use std::env;
use std::io::{self, Write};

use dactive::dactive::ActiveFile;

fn main() -> io::Result<()> {
    let args = env::args().collect::<Vec<_>>();
    let act = ActiveFile::open(&args[1])?;

    println!("{:?}", act.group_counters(&args[2]));

    let stdout = io::stdout();
    let mut handle = stdout.lock();

    for _ in 0..20 {
        if let Some(line) = act.list_active(Some(&args[2])) {
            handle.write_all(&line).expect("write");
        }
    }
    //if let Some(line) = act.list_newsgroups(Some(&args[2])) {
    //    handle.write_all(&line).expect("write");
    //}

    Ok(())
}
