//! issue_2997_foreign_result_kinds.rs — a curated foreign package call whose
//! result shape is already recorded (`strings.join` = string,
//! `strings.split`/`fields` = []string) must reach `OpKind`, so a string/slice
//! result stored into an `int` is rejected (Row 13 BUILDABLE). This covers the
//! unambiguous-shape subset; results whose shape is `Primitive` stay fail-open.

use hy_check::{check_file, Verdict};
use hy_syntax::parse_file;

fn check(src: &str) -> hy_check::CheckResult {
    let ast = parse_file("repro.hy", src).expect("snippet parses");
    check_file(&ast)
}

fn assert_rejected(src: &str) {
    let r = check(src);
    assert_eq!(r.verdict, Verdict::Reject, "expected Reject, diags: {:?}\nsrc:\n{src}", r.diagnostics);
}

fn assert_accepted(src: &str) {
    let r = check(src);
    assert_eq!(r.verdict, Verdict::Accept, "expected Accept, diags: {:?}\nsrc:\n{src}", r.diagnostics);
}

#[test]
fn strings_join_result_into_int_is_rejected() {
    assert_rejected(
        "import \"strings\"\nimport \"fmt\"\nfn main() {\n    var n int = strings.join([]string{\"a\"}, \",\")\n    fmt.println(n)\n}\n",
    );
}

#[test]
fn strings_split_slice_into_int_is_rejected() {
    assert_rejected(
        "import \"strings\"\nimport \"fmt\"\nfn main() {\n    var n int = strings.split(\"a,b\", \",\")\n    fmt.println(n)\n}\n",
    );
}

#[test]
fn strings_split_element_into_int_is_rejected() {
    assert_rejected(
        "import \"strings\"\nimport \"fmt\"\nfn main() {\n    parts := strings.split(\"a,b\", \",\")\n    var n int = parts[0]\n    fmt.println(n)\n}\n",
    );
}

#[test]
fn valid_foreign_result_uses_stay_accepted() {
    assert_accepted(
        "import \"strings\"\nimport \"fmt\"\nfn main() {\n    var s string = strings.join([]string{\"a\"}, \",\")\n    fmt.println(s)\n}\n",
    );
    assert_accepted(
        "import \"strings\"\nimport \"fmt\"\nfn main() {\n    parts := strings.split(\"a,b\", \",\")\n    var s string = parts[0]\n    fmt.println(s)\n}\n",
    );
}
