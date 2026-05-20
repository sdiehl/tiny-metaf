use std::fs;
use std::path::Path;

use tiny_fself::driver::Session;
use tiny_fself::parse;

fn run_file(path: &Path) -> String {
    let src = fs::read_to_string(path).unwrap();
    let prog = match parse::parse_program(&src) {
        Ok(p) => p,
        Err(e) => return format!("parse error: {e}"),
    };
    let mut s = Session::new();
    match s.process_program(&prog) {
        Ok(lines) => lines.join("\n"),
        Err(e) => format!("error: {e}"),
    }
}

#[test]
fn examples() {
    let base = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
    insta::glob!(&base, "*.f", |path| {
        let name = path.file_stem().unwrap().to_string_lossy().to_string();
        let out = run_file(path);
        insta::with_settings!({ snapshot_suffix => name }, {
            insta::assert_snapshot!(out);
        });
    });
}

#[test]
fn cases() {
    insta::glob!("cases/*.f", |path| {
        let name = path.file_stem().unwrap().to_string_lossy().to_string();
        let out = run_file(path);
        insta::with_settings!({ snapshot_suffix => name }, {
            insta::assert_snapshot!(out);
        });
    });
}
