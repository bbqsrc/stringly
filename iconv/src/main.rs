//! iconv-compatible character encoding converter.
//!
//! Usage:
//!   iconv -f <from-encoding> -t <to-encoding> [file...]
//!   iconv -l

use std::env;
use std::fs::File;
use std::io::{self, Read, Write};
use std::process::ExitCode;

use stringly::registry;

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        print_usage(&args[0]);
        return ExitCode::from(1);
    }

    let mut from_encoding: Option<String> = None;
    let mut to_encoding: Option<String> = None;
    let mut output_file: Option<String> = None;
    let mut input_files: Vec<String> = Vec::new();
    let mut list_encodings = false;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "-f" | "--from-code" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("Error: -f requires an encoding name");
                    return ExitCode::from(1);
                }
                from_encoding = Some(args[i].clone());
            }
            "-t" | "--to-code" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("Error: -t requires an encoding name");
                    return ExitCode::from(1);
                }
                to_encoding = Some(args[i].clone());
            }
            "-o" | "--output" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("Error: -o requires a filename");
                    return ExitCode::from(1);
                }
                output_file = Some(args[i].clone());
            }
            "-l" | "--list" => {
                list_encodings = true;
            }
            "-h" | "--help" => {
                print_usage(&args[0]);
                return ExitCode::SUCCESS;
            }
            arg if arg.starts_with('-') => {
                eprintln!("Error: Unknown option: {}", arg);
                return ExitCode::from(1);
            }
            _ => {
                input_files.push(args[i].clone());
            }
        }
        i += 1;
    }

    if list_encodings {
        let mut unicode = Vec::new();
        let mut legacy = Vec::new();

        for enc in registry::encodings() {
            if enc.is_unicode() {
                unicode.push(enc.name());
            } else {
                legacy.push(enc.name());
            }
        }

        unicode.sort_unstable();
        legacy.sort_unstable();

        println!("Unicode encodings:");
        for name in &unicode {
            println!("  {}", name);
        }
        println!();
        println!("Legacy encodings:");
        for name in &legacy {
            println!("  {}", name);
        }
        return ExitCode::SUCCESS;
    }

    let from = match from_encoding {
        Some(f) => f,
        None => {
            eprintln!("Error: Source encoding (-f) is required");
            return ExitCode::from(1);
        }
    };

    let to = match to_encoding {
        Some(t) => t,
        None => {
            eprintln!("Error: Target encoding (-t) is required");
            return ExitCode::from(1);
        }
    };

    // Read input
    let input = if input_files.is_empty() {
        // Read from stdin
        let mut buf = Vec::new();
        if let Err(e) = io::stdin().read_to_end(&mut buf) {
            eprintln!("Error reading stdin: {}", e);
            return ExitCode::from(1);
        }
        buf
    } else {
        // Read from files
        let mut buf = Vec::new();
        for path in &input_files {
            let mut file = match File::open(path) {
                Ok(f) => f,
                Err(e) => {
                    eprintln!("Error opening {}: {}", path, e);
                    return ExitCode::from(1);
                }
            };
            if let Err(e) = file.read_to_end(&mut buf) {
                eprintln!("Error reading {}: {}", path, e);
                return ExitCode::from(1);
            }
        }
        buf
    };

    // Transcode
    let output = match registry::transcode(&input, &from, &to) {
        Ok(out) => out,
        Err(e) => {
            eprintln!("Error: {}", e);
            return ExitCode::from(1);
        }
    };

    // Write output
    let write_result = match output_file {
        Some(path) => {
            let mut file = match File::create(&path) {
                Ok(f) => f,
                Err(e) => {
                    eprintln!("Error creating {}: {}", path, e);
                    return ExitCode::from(1);
                }
            };
            file.write_all(&output)
        }
        None => io::stdout().write_all(&output),
    };

    if let Err(e) = write_result {
        eprintln!("Error writing output: {}", e);
        return ExitCode::from(1);
    }

    ExitCode::SUCCESS
}

fn print_usage(program: &str) {
    eprintln!(
        "Usage: {} -f <from-encoding> -t <to-encoding> [file...]",
        program
    );
    eprintln!("       {} -l", program);
    eprintln!();
    eprintln!("Options:");
    eprintln!("  -f, --from-code <encoding>  Source encoding");
    eprintln!("  -t, --to-code <encoding>    Target encoding");
    eprintln!("  -o, --output <file>         Output file (default: stdout)");
    eprintln!("  -l, --list                  List available encodings");
    eprintln!("  -h, --help                  Show this help");
}
