//! range_iter_bounds.rs — regression for issue #827: `for i in lo..hi`
//! integer-range bounds used to bypass HYB-E2009 in four ways (nil/bool/
//! pointer/comparison bounds, untyped `const` float/bool/string identifiers,
//! mismatched integer bound types, and constant bounds overflowing the loop
//! counter's type), each passing `hyb check` with 0 diagnostics and then
//! failing `go build` on the emitted Go.

use hy_check::{check_file, CheckResult, Verdict};
use hy_diag::Severity;
use hy_syntax::parse_file;

fn check(src: &str) -> CheckResult {
    let path = "inline.hy";
    let ast = parse_file(path, src)
        .unwrap_or_else(|diags| panic!("must parse (parser contract): {:?}", diags));
    check_file(&ast)
}

fn error_codes(r: &CheckResult) -> Vec<String> {
    r.diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .map(|d| d.code.clone())
        .collect()
}

fn rejects_with_e2009(src: &str) {
    let r = check(src);
    let cs = error_codes(&r);
    assert!(
        cs.iter().any(|c| c == "HYB-E2009"),
        "expected HYB-E2009 for {:?}, got {:?}",
        src,
        cs
    );
    assert_eq!(r.verdict, Verdict::Reject, "verdict for {:?}", src);
}

fn accepts_without_e2009(src: &str) {
    let r = check(src);
    let cs = error_codes(&r);
    assert!(
        !cs.iter().any(|c| c == "HYB-E2009"),
        "must NOT fire HYB-E2009 for {:?}, got {:?}",
        src,
        cs
    );
}

// ---------------------------------------------------------------- reject:

#[test]
fn non_integer_bound_literals_reject() {
    // Bypass 1: nil, boolean comparison, `!`, `&`, and float literals.
    rejects_with_e2009("fn main() { for i in 0..nil { _ = i } }");
    rejects_with_e2009("fn main() { for i in 0..(1 < 2) { _ = i } }");
    rejects_with_e2009("fn main() { b := true\n    for i in (!b)..5 { _ = i } }");
    rejects_with_e2009("fn main() { x := 5\n    for i in 0..(&x) { _ = i } }");
    rejects_with_e2009("fn main() { for i in 0..2.5 { _ = i } }");
    rejects_with_e2009("fn main() { for i in (1 < 2)..5 { _ = i } }");
}

#[test]
fn untyped_const_identifiers_reject() {
    // Bypass 2: untyped `const` float/bool/string identifiers, file-level
    // and block-scoped.
    rejects_with_e2009("const f = 2.5\n\nfn main() { for i in 0..f { _ = i } }");
    rejects_with_e2009("const b = true\n\nfn main() { for i in 0..b { _ = i } }");
    rejects_with_e2009("const s = \"abc\"\n\nfn main() { for i in 0..s { _ = i } }");
    rejects_with_e2009("fn main() { const f = 2.5\n    for i in 0..f { _ = i } }");
    rejects_with_e2009("fn main() { const b = false\n    for i in 0..b { _ = i } }");
}

#[test]
fn mismatched_bound_types_reject() {
    // Bypass 3: mismatched concrete integer types between lo and hi.
    rejects_with_e2009("fn main() { var n u32 = 5\n    for i in 0..n { _ = i } }");
    rejects_with_e2009("fn main() { var lo i32 = 0\n    var hi i64 = 5\n    for i in lo..hi { _ = i } }");
    // Inclusive lowering binds hyLo/hyHi independently: an untyped constant
    // hi gets Go's default type `int`, so `lo: i64` mismatches.
    rejects_with_e2009("fn main() { var lo i64 = 0\n    for i in lo..=10 { _ = i } }");
    // Exclusive lowering: `i := 0` defaults to `int`, `n: u8` mismatches.
    rejects_with_e2009("fn main() { var n u8 = 5\n    for i in 0..n { _ = i } }");
    // Inclusive lowering binds hyLo/hyHi independently: an untyped constant
    // hi gets Go's default type `int`, so `lo: i8` mismatches too.
    rejects_with_e2009("fn main() { var lo i8 = 0\n    for i in lo..=100 { _ = i } }");
}

#[test]
fn overflowing_constant_bounds_reject() {
    // Bypass 4: constant bounds that overflow the loop counter's type.
    rejects_with_e2009("fn main() { for i in 0..(1 << 63) { _ = i } }");
    rejects_with_e2009("fn main() { for i in 0..99999999999999999999 { _ = i } }");
    rejects_with_e2009("fn main() { var lo i8 = 0\n    for i in lo..300 { _ = i } }");
    rejects_with_e2009("fn main() { var hi u8 = 10\n    for i in -1..hi { _ = i } }");
}

// ---------------------------------------------------------------- accept:

#[test]
fn valid_integer_ranges_stay_accepted() {
    accepts_without_e2009("fn main() { for i in 0..10 { _ = i } }");
    accepts_without_e2009("fn main() { for i in 0..=10 { _ = i } }");
    accepts_without_e2009("fn main() { n := 5\n    for i in 0..n { _ = i } }");
    // Exclusive form: the untyped constant hi adopts lo's type — no mismatch.
    accepts_without_e2009("fn main() { var lo i64 = 0\n    for i in lo..10 { _ = i } }");
    // Conversion-call bound: the counter takes the conversion's type.
    accepts_without_e2009("fn main() { var n u32 = 5\n    for i in u32(0)..n { _ = i } }");
    accepts_without_e2009("fn main() { var lo i64 = 0\n    var hi i64 = 10\n    for i in lo..hi { _ = i } }");
    accepts_without_e2009("fn main() { const n = 300\n    for i in 0..n { _ = i } }");
}

#[test]
fn iterate_form_untouched() {
    // The `for x in e` iterable checks (#411) must not regress.
    accepts_without_e2009("fn main() { xs := []int{1, 2}\n    for x in xs { _ = x } }");
    accepts_without_e2009("fn main() { m := map[string]int{\"a\": 1}\n    for k, v in m { _ = k + v } }");
}
