use std::process::ExitCode;

fn main() -> ExitCode {
    let mut args = std::env::args().skip(1);
    match args.next() {
        Some(path) => match std::fs::read_to_string(&path) {
            Ok(_source) => {
                eprintln!("kin: checking is not implemented yet ({path})");
                ExitCode::FAILURE
            }
            Err(err) => {
                eprintln!("kin: cannot read {path}: {err}");
                ExitCode::FAILURE
            }
        },
        None => {
            eprintln!("usage: kin <file.kin>");
            ExitCode::from(2)
        }
    }
}
