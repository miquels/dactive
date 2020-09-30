//! Read / write the active file in diablo's dactive.kp format.
//!
use std::fmt;
use std::io;
use std::sync::Mutex;

use crate::kpdb::{Record, KpDb};

// contains the exclusively locked active file.
pub struct ActiveFile(Mutex<ActiveInner>);

impl ActiveFile {
    pub fn open(path: impl AsRef<str>) -> io::Result<ActiveFile> {
        let kpdb = KpDb::open(path, false)?;
        let inner = ActiveInner { kpdb };
        Ok(ActiveFile(Mutex::new(inner)))
    }

    /// Return the low / high / xref counters for a group.
    pub fn group_counters(&self, name: &str) -> Option<GroupCounters> {
        let inner = self.0.lock().unwrap();
        let entry = inner.kpdb.get(name)?;
        Some(GroupCounters::read(&entry))
    }

    /// Output for the 'LIST active' command.
    pub fn list_active(&self, groups: Option<&str>) -> Option<Vec<u8>> {
        self.list_data(groups, true)
    }

    /// Output for the 'LIST newsgroups' command.
    pub fn list_newsgroups(&self, groups: Option<&str>) -> Option<Vec<u8>> {
        self.list_data(groups, false)
    }

    fn list_data(&self, groups: Option<&str>, active: bool) -> Option<Vec<u8>> {
        let inner = self.0.lock().unwrap();
        let mut buf = Vec::new();

        let groups = groups.unwrap_or("*");
        let is_wildpat = groups.chars().any(|c| "*?\\[".contains(c));

        if is_wildpat {
            for (group, entry) in inner.kpdb.iter() {
                if crate::wildmat::wildmat(&group, groups) {
                    inner.list_data(&entry, &mut buf, active);
                }
            }
        } else {
            let entry = inner.kpdb.get(groups)?;
            inner.list_data(&entry, &mut buf, active);
        }
        if !buf.is_empty() {
            Some(buf)
        } else {
            None
        }
    }
}

struct ActiveInner {
    kpdb: KpDb,
}

impl ActiveInner {
    fn list_data(&self, entry: &Record, buf: &mut Vec<u8>, active: bool) {
        if active {
            self.list_active(entry, buf)
        } else {
            self.list_newsgroups(entry, buf)
        }
    }

    fn list_active(&self, entry: &Record, buf: &mut Vec<u8>) {
        // It's twice as fast to iterate once over all fields,
        // than to call entry.get_str() three times.
        let mut fields = entry.get_raw().split(|b| b.is_ascii_whitespace());

        let name = match fields.next() {
            Some(name) => name,
            None => return,
        };

        let mut high = &b"0000000000"[..];
        let mut low = &b"0000000000"[..];
        let mut status = &b"x"[..];

        for field in fields {
            if field.starts_with(&b"NE="[..]) {
                high = &field[3..];
            }
            if field.starts_with(&b"NB="[..]) {
                low = &field[3..];
            }
            if field.starts_with(&b"S="[..]) {
                status = &field[2..];
            }
        }

        // because we have &[u8] fields instead of &str we cannot use write!(...).
        if name.starts_with(&b"."[..]) {
            buf.push(b'.');
        }
        buf.extend_from_slice(name);
        buf.push(b' ');
        buf.extend_from_slice(high);
        buf.push(b' ');
        buf.extend_from_slice(low);
        buf.push(b' ');
        buf.extend_from_slice(status);
        buf.extend_from_slice(&b"\r\n"[..]);
    }

    fn list_newsgroups(&self, entry: &Record, buf: &mut Vec<u8>) {
        let name = match entry.get_name() {
            Some(name) => name,
            None => return,
        };
        if let Some(desc) = entry.get_decoded("GD") {
            if !desc.is_empty() && desc != &b"?"[..] {
                if name.starts_with(".") {
                    buf.push(b'.');
                }
                buf.extend_from_slice(name.as_bytes());
                buf.push(b' ');
                buf.extend_from_slice(&desc);
                buf.extend_from_slice(&b"\r\n"[..]);
            }
        }
    }
}

// active-file flag for a group.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GroupStatus {
    PostingOk = b'y',
    NoPosting = b'n',
    Moderated = b'm',
    Junk = b'j',
    Closed = b'x',
}

impl fmt::Display for GroupStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", *self as u8 as char)
    }
}

impl std::default::Default for GroupStatus {
    fn default() -> Self {
        GroupStatus::Closed
    }
}

impl std::str::FromStr for GroupStatus {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "y" => Ok(GroupStatus::PostingOk),
            "n" => Ok(GroupStatus::NoPosting),
            "m" => Ok(GroupStatus::Moderated),
            "j" => Ok(GroupStatus::Junk),
            "x" => Ok(GroupStatus::Closed),
            _ => Err(()),
        }
    }
}

#[derive(Debug)]
pub struct GroupCounters {
    pub low: u64,
    pub high: u64,
    pub xref: u64,
}

impl GroupCounters {
    fn read(entry: &Record) -> GroupCounters {
        let low = entry.get_u64("NB").unwrap_or(1);
        let high = entry.get_u64("NE").unwrap_or(0);
        let xref = entry.get_u64("NX").unwrap_or(1);
        GroupCounters { low, high, xref }
    }
}
