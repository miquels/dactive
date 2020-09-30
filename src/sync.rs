//! Synchronize a dactive.kp file with LIST active and LIST newsgroups data.
//!
use std::collections::HashMap;
use std::io;

use crate::kpdb::KpDb;

pub fn sync_active(db: &mut KpDb, active: &[u8]) -> io::Result<()> {

    for line in active.split(|&b| b == b'\n') {

        // If it's not UTF-8 just ignore it - what can we do?
        if let Ok(line) = std::str::from_utf8(line) {

            // Check that it has at least four fields.
            let fields: Vec<_> = line.split_ascii_whitespace().collect();
            if fields.len() < 4 {
                continue;
            }

            // Look the group up in the current dactive.kp
            if let Some(mut rec) = db.get_mut(fields[0]) {
                // Exists. Check if the status flag changed.
                let status = rec.get_str("S").unwrap_or("");
                if status != fields[3] {
                    // Changed.
                    rec.set_str("S", fields[3]);
                }
                continue;
            }

            // We did not have this group yet, add it.
            let mut hm = HashMap::new();
            hm.insert("NB", "00000001".to_string());
            hm.insert("NE", "00000000".to_string());
            hm.insert("NX", "00000000".to_string());
            hm.insert("S", fields[3].to_string());
            db.insert(fields[0], &hm);
        }
    }
    db.flush()
}

