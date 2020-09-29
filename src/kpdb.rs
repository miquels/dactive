//! Read / write a database in diablo's `dkp` format.
//!
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::fs;
use std::io::{self, ErrorKind, Seek, Write};

use memmap::MmapMut;

const MAX_FILE_SIZE: usize = 4_000_000_000;

type Range = std::ops::Range<usize>;

//////////////////////////////////////////////////////////////
// KpDb implementation
//////////////////////////////////////////////////////////////

/// An open database handle.
pub struct KpDb {
    // appends since db creation.
    append_seq: u32,
    // last modified (written on exit).
    modified: u32,
    // appends since last sort.
    append_sseq: u32,
    // for each group, location and current value of artno_xref.
    entries: BTreeMap<String, EntryLoc>,
    // The mmap'd file (impl's DerefMut &[u8]).
    data: MmapMut,
    // Size of the mmap'ed file.
    datasz: usize,
    // File descriptor of the file.
    file: fs::File,
    // Data to be appended.
    ndata: Vec<u8>,
    // Filename of db file
    path: String,
}

impl KpDb {
    /// Open the database file, then read and check it.
    ///
    /// If 'create' is true, the file is created if it did not exist,
    /// but if it _did_ exist the open will fail.
    pub fn open(path: impl AsRef<str>, create: bool) -> io::Result<KpDb> {
        let path = path.as_ref();
        let mut options = fs::OpenOptions::new();
        let options = options.read(true).write(true).create_new(create);
        let file = if create {
            // Create and initialize.
            let mut file = options
                .open(&path)
                .map_err(|e| io::Error::new(e.kind(), format!("kpdb: create {}: {}", path, e)))?;
            write!(file, "$V00.00 00000000 {:08x} 00000000\n", unixtime_now())
                .map_err(|e| io::Error::new(e.kind(), format!("kpdb: {}: {}", path, e)))?;
            file
        } else {
            options
                .open(&path)
                .map_err(|e| io::Error::new(e.kind(), format!("kpdb: open {}: {}", path, e)))?
        };

        // This is safe providing that other unrelated processes don't modify the file.
        // We do put an fcntl lock on the file so other instances of nntp-rs will
        // not ever modify the file concurrently.
        let data = unsafe { MmapMut::map_mut(&file) }?;

        if data.len() > MAX_FILE_SIZE {
            return Err(io::Error::new(
                ErrorKind::InvalidData,
                format!("kpdb: {}: file too big (>={})", path, MAX_FILE_SIZE)
            ));
        }

        // Decode the head.
        if data.len() < 35
            || data[7] != b' '
            || data[16] != b' '
            || data[25] != b' '
            || data[34] != b'\n'
        {
            return Err(io::Error::new(
                ErrorKind::InvalidData,
                format!("kpdb: {}: head: cannot parse", path)
            ));
        }
        if &data[0..7] != &b"$V00.00"[..] {
            return Err(io::Error::new(
                ErrorKind::InvalidData,
                format!("kpdb: {}: head: unsupported version", path)
            ));
        }
        let append_seq = u32_from_hex(&data[8..16]).ok_or_else(|| {
            io::Error::new(ErrorKind::InvalidData, format!("kpdb: {}: head: field 2 damaged", path))
        })?;
        let modified = u32_from_hex(&data[17..25]).ok_or_else(|| {
            io::Error::new(ErrorKind::InvalidData, format!("kpdb: {}: head: field 3 damaged", path))
        })?;
        let append_sseq = u32_from_hex(&data[26..34]).ok_or_else(|| {
            io::Error::new(ErrorKind::InvalidData, format!("kpdb: {}: head: field 4 damaged", path))
        })?;

        // Now walk over the individual entries.
        let mut pos = 35;
        let mut lineno = 1;
        let datasz = data.len();

        let mut entries = BTreeMap::new();

        loop {
            // Find the newline at the end of the line.
            let mut idx = pos;
            loop {
                if idx == datasz || data[idx] == b'\n' {
                    break;
                }
                idx += 1;
            }
            if idx == datasz {
                break;
            }
            lineno += 1;

            // We have a line.
            let line = &data[pos..idx];
            if line.len() >= 8192 {
                return Err(io::Error::new(
                    ErrorKind::InvalidData,
                    format!("dactive.kp: line {}: too long", lineno),
                ));
            }

            // Now parse it, and turn it into a EntryLoc struct.
            // That struct has the offset and length of the line.
            let (name, entry) = EntryLoc::new(line, pos as u32, lineno)?;
            entries.insert(name, entry);

            pos = idx + 1;
        }

        Ok(KpDb {
            append_seq,
            modified,
            append_sseq,
            entries,
            data,
            datasz,
            file,
            ndata: Vec::new(),
            path: path.to_string(),
        })
    }

    /// Check if we need to remap the database. This should be called
    /// after every modification.
    #[inline]
    pub fn check_remap(&mut self) -> io::Result<()> {
        if self.ndata.len() == 0 {
            return Ok(());
        }
        self.do_check_remap()
    }

    pub fn do_check_remap(&mut self) -> io::Result<()> {
        // Will never happen but check anyway.
        if self.datasz + self.ndata.len() > MAX_FILE_SIZE {
            panic!(format!(
                "kpdb: FATAL: {}: grown too big (>{})",
                self.path, MAX_FILE_SIZE
            ));
        }

        // First append 'ndata' to the database file. If that fails, try to
        // recover and get to a stable state, and return an IO error.
        let oldlen = self.file.seek(io::SeekFrom::End(0))?;
        let ndata = std::mem::replace(&mut self.ndata, Vec::new());
        if let Err(e) = self.file.write_all(&ndata) {
            match self.file.metadata() {
                Err(_) => {
                    // If we can't even fstat() anymore, the world is broken.
                    panic!(format!(
                        "kpdb: FATAL: {}: partial written database file, can't recover: {}",
                        self.path, e
                    ));
                }
                Ok(meta) => {
                    // See if we can recover.
                    if meta.len() != oldlen {
                        if let Err(_) = self.file.set_len(oldlen) {
                            // If ftruncate fails, there's no way to recover.
                            panic!(format!(
                                "kpdb: FATAL: {}: partial written database file, can't recover: {}",
                                self.path, e
                            ));
                        }
                    }
                    self.ndata = ndata;
                    return Err(io::Error::new(
                        e.kind(),
                        format!("kpdb: {}: {}", self.path, e),
                    ));
                }
            }
        }

        // Now do a new mmap. Too bad we cannot use mremap, this is expensive.
        // If this fails, we are in an unrecoverable state.
        let data = match unsafe { MmapMut::map_mut(&self.file) } {
            Ok(data) => data,
            Err(e) => panic!(format!("kpdb: FATAL: mmap {}: {}", self.path, e)),
        };

        self.datasz = data.len();
        self.data = data;

        Ok(())
    }

    /// Get an `Entry` from the database. The `Entry` holds a multiple
    /// key/value pairs.
    pub fn get(&self, key: &str) -> Option<Entry<'_>> {
        self.entries.get(key).map(move |e| Entry::from_loc(e, self))
    }

    /// Get an `EntryMut` from the database. Like `Entry`, but mutable.
    pub fn get_mut(&mut self, key: &str) -> Option<EntryMut<'_>> {
        if let Some(loc) = self.entries.get(key) {
            Some(EntryMut::from_loc(loc.clone(), self))
        } else {
            None
        }
    }

    /// Insert a new Entry in the database.
    pub fn insert<'a>(&'a mut self, key: &str, kvpairs: &HashMap<&'static str, String>) {
        let start = self.datasz + self.ndata.len();
        let mut s = format!("+{:08x}.0000:{}", start, key);
        for (k, v) in kvpairs {
            s.push_str(&format!(" {}={}", k, v));
        }
        s.push('\n');
        self.ndata.extend_from_slice(s.as_bytes());
        let end = self.datasz + self.ndata.len();
        let entry_loc = EntryLoc {
            lineno: 0,
            offset: start as u32,
            len: (end - start) as u16,
        };
        self.entries.insert(key.to_string(), entry_loc.clone());
    }

    /// Iterate over all `Entry`s in the database.
    pub fn iter<'a>(&'a self) -> impl Iterator<Item = (&'a str, Entry<'a>)> {
        self.entries
            .iter()
            .map(move |(k, v)| (k.as_str(), Entry::from_loc(v, self)))
    }
}

// An EntryLoc is a reference to an Entry in the database,
// it's what we store in the in-memory btree to refer to
// the actual data by offset + len. `line` is for context
// information in errors etc.
#[derive(Clone)]
struct EntryLoc {
    lineno: u32,
    offset: u32,
    len: u16,
}

impl EntryLoc {
    // Parse a line, check its validity, then return an `EntryLoc` for it.
    fn new(line: &[u8], offset: u32, lineno: u32) -> io::Result<(String, EntryLoc)> {
        // Some sanity checks.
        if line.len() < 18 || line[14] != b':' {
            return Err(io::Error::new(
                ErrorKind::InvalidData,
                format!("dactive.kp: line {}: damaged", lineno),
            ));
        }

        // Must be UTF-8 (and is, because it should be ASCII).
        std::str::from_utf8(line).map_err(|_| {
            io::Error::new(
                ErrorKind::InvalidData,
                format!("dactive.kp: line {}: not ASCII/UTF-8", lineno),
            )
        })?;

        let entry = Entry { line, lineno };

        let name = entry
            .get_name()
            .ok_or_else(|| {
                io::Error::new(
                    ErrorKind::InvalidData,
                    format!("dactive.kp: line {}: no newsgroup name", lineno),
                )
            })?
            .to_string();

        // Now check that all fields that we need are present.
        //
        // NOTE: this does not belong in a generic kpdb implementation,
        // but as long as we _only_ use this for dactive.kp it's
        // a good consistency check.
        for key in vec!["NB", "NE", "NX", "S", "CTS", "LMTS"].into_iter() {
            entry.get_str(key).ok_or_else(|| {
                io::Error::new(
                    ErrorKind::InvalidData,
                    format!("dactive.kp: line {}: {} missing", lineno, key),
                )
            })?;
        }

        Ok((
            name,
            EntryLoc {
                lineno,
                offset,
                len: line.len() as u16,
            },
        ))
    }
}

/// A handle for an entry in the database.
#[derive(Clone)]
pub struct Entry<'a> {
    lineno: u32,
    line: &'a [u8],
}

impl<'a> Entry<'a> {
    // internal build an entry from an EntryLoc.
    fn from_loc<'b>(e: &EntryLoc, kpdb: &'b KpDb) -> Entry<'b> {
        let mut data: &[u8] = &kpdb.data;
        let mut start = e.offset as usize;
        if start >= kpdb.datasz {
            // If it starts beyond the data in the file, it's a buffered
            // entry that does not exist in the database file yet.
            //
            // That's an optimization, for when we add a lot of new entries
            // in succession, so that we do not have to mremap() all the time.
            //
            // Adjust the offset and refer to that internal buffered data.
            start -= kpdb.datasz;
            data = &kpdb.ndata;
        }
        let end = start + e.len as usize;
        Entry {
            lineno: e.lineno,
            line: &data[start..end],
        }
    }

    /// Get a direct reference to the raw data of this entry (name key1=val1 ...)
    pub fn get_raw(&'a self) -> &'a [u8] {
        if self.line.len() < 15 {
            &b""[..]
        } else {
            &self.line[15..]
        }
    }

    /// Get the name of this entry. Can only fail if the database is corrupt.
    /// (Perhaps we should use a Result instead of an Option).
    pub fn get_name(&'a self) -> Option<&'a str> {
        get_name(self.line)
    }

    /// Lookup a value, return it as a string.
    pub fn get_str(&'a self, key: &str) -> Option<&'a str> {
        let range = get_range(key, self.line)?;
        std::str::from_utf8(&self.line[range]).ok()
    }

    /// Lookup a value, then if it is found percent-decode it.
    pub fn get_decoded(&'a self, key: &str) -> Option<Vec<u8>> {
        let range = get_range(key, self.line)?;
        Some(pct_decode(&self.line[range]))
    }

    /// Lookup a value, then if it is found interpret it as a number.
    pub fn get_u64(&'a self, key: &str) -> Option<u64> {
        let s = self.get_str(key)?;
        u64::from_str_radix(s, 10).ok()
    }
}

/// A handle for a mutable entry in the database.
pub struct EntryMut<'a> {
    kpdb: &'a mut KpDb,
    entry_loc: EntryLoc,
    modified: Option<HashMap<&'static [u8], String>>,
}

impl<'a> EntryMut<'a> {
    // See Entry::from_loc().
    fn from_loc<'b>(entry_loc: EntryLoc, kpdb: &'b mut KpDb) -> EntryMut<'b> {
        EntryMut {
            kpdb,
            entry_loc,
            modified: None,
        }
    }

    // Since we keep an &mut KpDb in self, we cannot also keep a &line[u8]
    // there - no self-referencing structs in rust. So we get it via entry_loc.
    fn line(&self) -> &[u8] {
        let mut data = &self.kpdb.data[..];
        let mut start = self.entry_loc.offset as usize;
        if start >= self.kpdb.datasz {
            start -= self.kpdb.datasz;
            data = &self.kpdb.ndata[..];
        }
        let end = start + self.entry_loc.len as usize;
        &data[start..end]
    }

    // Since we keep an &mut KpDb in self, we cannot also keep a &mut line[u8]
    // there - no self-referencing structs in rust. So we get it via entry_loc.
    fn line_mut(&mut self) -> &mut [u8] {
        let mut data = &mut self.kpdb.data[..];
        let mut start = self.entry_loc.offset as usize;
        if start >= self.kpdb.datasz {
            start -= self.kpdb.datasz;
            data = &mut self.kpdb.ndata[..];
        }
        let end = start + self.entry_loc.len as usize;
        &mut data[start..end]
    }

    /// Set or replace a string value.
    pub fn set_str(&mut self, key: &'static str, val: &str) {
        // If we can modify the value in-place, do so.
        let line = self.line_mut();
        if let Some(range) = get_range(key, line) {
            if range.end - range.start == val.len() {
                line[range].copy_from_slice(val.as_bytes());
                return;
            }
        }
        // Otherwise stash the new value, we will deal with it later (on Drop).
        self.modified
            .get_or_insert_with(|| HashMap::new())
            .insert(key.as_bytes(), val.to_string());
    }

    pub fn get_str(&'a self, key: &str) -> Option<&'a str> {
        if let Some(ref hm) = self.modified {
            if let Some(val) = hm.get(key.as_bytes()) {
                return Some(val);
            }
        }
        let line = self.line();
        let range = get_range(key, line)?;
        std::str::from_utf8(&line[range]).ok()
    }

    pub fn get_u64(&'a self, key: &str) -> Option<u64> {
        let s = self.get_str(key)?;
        u64::from_str_radix(s, 10).ok()
    }
}

/// On drop, see if the self.modified hashmap is non-empty. If it is
/// not, we could not modify-in-place, so write a new entry for this line.
impl<'a> Drop for EntryMut<'a> {
    fn drop(&mut self) {
        if let Some(mut hm) = self.modified.take() {
            // invalidate old entry.
            self.line_mut()[0] = b'-';

            // Now remember location in ndata so we can update self.entries.
            let start = self.kpdb.ndata.len() + self.kpdb.datasz;
            let mut name = Vec::new();

            // Make a copy of the line, validate, start building new entry.
            let mut line = self.line().to_vec();
            line[0] = b'+';
            self.kpdb.ndata.extend_from_slice(&line[..15]);

            // Walk over all fields.
            let fields = line[15..].split(|b| b.is_ascii_whitespace());
            let mut first = true;
            for field in fields {
                if field.is_empty() {
                    continue;
                }

                // Split key/value on '='. Add key to new entry.
                let mut kv = field.splitn(2, |&b| b == b'=');
                let key = kv.next().unwrap();
                if !first {
                    self.kpdb.ndata.push(b' ');
                }
                self.kpdb.ndata.extend_from_slice(key);

                if first {
                    // This was the name of the entry, not a key/value pair.
                    first = false;
                    name = key.to_vec();
                    println!("XXX Drop {:?}: updating: {:?}", std::str::from_utf8(key), hm);
                    continue;
                }

                // If this key was also present in 'modified', use it.
                println!("XXX check key {:?}", std::str::from_utf8(key));
                if let Some(newval) = hm.remove(key) {
                    println!("XXX UPD: = {}", newval);
                    self.kpdb.ndata.push(b'=');
                    self.kpdb.ndata.extend_from_slice(newval.as_bytes());
                } else if let Some(val) = kv.next() {
                    // use the original value.
                    self.kpdb.ndata.push(b'=');
                    self.kpdb.ndata.extend_from_slice(val);
                }
            }

            // And add new key/value pairs.
            for (key, newval) in hm.into_iter() {
                self.kpdb.ndata.push(b' ');
                self.kpdb.ndata.extend_from_slice(key);
                self.kpdb.ndata.push(b'=');
                self.kpdb.ndata.extend_from_slice(newval.as_bytes());
            }

            // finalize.
            self.kpdb.ndata.push(b'\n');
            let end = self.kpdb.ndata.len() + self.kpdb.datasz;
            println!("XXX ndata is now: {:?}", std::str::from_utf8(&self.kpdb.ndata));
            let name = String::from_utf8(name).unwrap();
            self.kpdb.entries.insert(
                name,
                EntryLoc {
                    lineno: 0,
                    offset: start as u32,
                    len: (end - start) as u16,
                },
            );
        }
    }
}

// Helper.
// Scan the line to find 'key=value', then return the Range of value.
fn get_range(key: &str, line: &[u8]) -> Option<Range> {
    if line.len() < 15 {
        return None;
    }
    let mut idx = 15;

    let key = key.as_bytes();

    loop {
        // skip leading space.
        while idx < line.len() {
            if !line[idx].is_ascii_whitespace() {
                break;
            }
            idx += 1;
        }
        let start = idx;
        let mut eq = 0;

        // find end.
        while idx < line.len() {
            if line[idx] == b'=' {
                eq = idx;
            }
            if line[idx].is_ascii_whitespace() {
                break;
            }
            idx += 1;
        }

        if idx == start {
            return None;
        }
        if eq == 0 {
            continue;
        }

        if &line[start..eq] == key {
            if std::str::from_utf8(&line[eq + 1..idx]).is_ok() {
                return Some(Range {
                    start: eq + 1,
                    end: idx,
                });
            }
        }
    }
}

// Helper.
// Get the name of this entry.
fn get_name(line: &[u8]) -> Option<&str> {
    if line.len() < 15 {
        return None;
    }
    let mut idx = 15;

    // skip leading space.
    while idx < line.len() {
        if !line[idx].is_ascii_whitespace() {
            break;
        }
        idx += 1;
    }
    let start = idx;

    // find end.
    while idx < line.len() {
        if line[idx] == b'=' {
            return None;
        }
        if line[idx].is_ascii_whitespace() {
            break;
        }
        idx += 1;
    }

    if idx == start {
        return None;
    }

    std::str::from_utf8(&line[start..idx]).ok()
}

// Percent-decode a string. Returns a Vec<u8> since the
// result might not be valid utf-8.
fn pct_decode(d: &[u8]) -> Vec<u8> {
    let mut v = Vec::with_capacity(d.len());
    let mut i = 0;
    while i < d.len() {
        if d[i] == b'%' && d[i..].len() >= 3 {
            if let Ok(hex) = std::str::from_utf8(&d[i + 1..i + 3]) {
                if let Ok(c) = u8::from_str_radix(hex, 16) {
                    v.push(c);
                    i += 3;
                    continue;
                }
            }
        }
        v.push(d[i]);
        i += 1;
    }
    v
}

// helper.
fn u32_from_hex(data: &[u8]) -> Option<u32> {
    let hex = std::str::from_utf8(data).ok()?;
    u32::from_str_radix(hex, 16).ok()
}

// helper
fn unixtime_now() -> u32 {
    use std::time::SystemTime;
    SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .unwrap()
        .as_secs() as u32
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    use std::fs;

    #[test]
    fn test_kpdb() {
        let _ = fs::remove_file("test.kp");
        assert!(KpDb::open("test.kp", false).is_err());

        let mut db = KpDb::open("test.kp", true).expect("test.kp");

        let mut kv = HashMap::new();
        let now_hex = format!("{:08x}", unixtime_now());
        kv.insert("NB", "0000000001".into());
        kv.insert("NE", "0000000000".into());
        kv.insert("NX", "0000000000".into());
        kv.insert("S", "y".into());
        kv.insert("CTS", now_hex.clone());
        kv.insert("LMTS", now_hex);

        db.insert("test.1", &kv);

        kv.insert("GD", "testgroup2".into());
        db.insert("test.2", &kv);

        db.check_remap().expect("remap");

        {
            let mut t1 = db.get_mut("test.1").expect("test.1");
            assert!(t1.get_str("S").unwrap() == "y");

            t1.set_str("S", "n");
            assert!(t1.get_str("S").unwrap() == "n");

            t1.set_str("GD", "testgroup1");
            drop(t1);

            db.check_remap().expect("remap");
        }

        let t1 = db.get("test.1").expect("test.1");
        assert!(t1.get_str("GD").unwrap() == "testgroup1");

    }
}

