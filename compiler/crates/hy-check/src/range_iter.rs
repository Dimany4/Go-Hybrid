//! range_iter.rs — `for x in e` iterable-kind checks (HYB-E2009 / E3005).
//!
//! Issue #411: SPEC-LANGUAGE LX13 pins the iterable set ("`for x in e`
//! iterates slices, arrays, strings (runes), maps (keys), channels (until
//! close), and integer ranges `for i in 0..n`"), but nothing checked that
//! the `e` of a `ForKind::Iterate` belongs to it. `for v in 5` / `for v in
//! true` / `for v in box{...}` / `for v in count()` (an int-returning call)
//! passed `hyb check` with 0 diagnostics and emitted `for _, v := range x`
//! — Go: `cannot range over x`. This mirrors the send-target (#77) and
//! receive-operand classification:
//!   * iterable kinds (Slice/Array/Str/Map/Chan/BorrowHandle, plus the
//!     element-source foreign handles) pass;
//!   * a concrete non-iterable is HYB-E2009;
//!   * an unresolvable operand stays fail-closed (HYB-E3005, O4.9) — the
//!     same treatment the send and receive sides give an unknown operand.
//!
//! Go's range rule also allows a pointer TO AN ARRAY (`*[N]T`), so exactly
//! one Pointer level is normalized for arrays — `*struct` / `*slice` /
//! `*string` stay non-iterable, as in Go.
//!
//! `ForKind::Range` (`for i in 0..n`) has no iterable operand and is not
//! affected. Wiring: the Tier-0 flat walk (lib.rs, per flattened statement)
//! and the closure walk (closures.rs — FnLit bodies sit outside the flat
//! walk, the A5 perimeter).

use crate::const_overflow::{const_int_fold_with, fixed_width_int_range, ConstFold};
use crate::model::{unwrap_parens, Checker, FnState, TypeShape};
use hy_diag::{Diagnostic, Span};
use hy_syntax::{Expr, ForKind, LitKind, Stmt, TypeExpr};
use std::collections::HashMap;

impl<'a> Checker<'a> {
    /// Statement entry: classify the iterable of every `for x in e` and the
    /// integer bounds of every `for i in lo..hi` in this statement's own
    /// position. Nested block bodies are NOT recursed — the Tier-0 flat walk
    /// already lists those statements; the closure walk recurses explicitly.
    pub(crate) fn check_stmt_range_iterable(&mut self, st: &FnState, stmt: &Stmt) {
        match stmt {
            Stmt::For {
                kind: ForKind::Iterate { vars, expr },
                ..
            } => {
                let span = expr.span();
                let before = self.diags.len();
                self.check_range_iterable(st, expr, span);
                if self.diags.len() == before {
                    let shape = self.shape_of_expr(st, expr);
                    let is_chan = matches!(shape, TypeShape::Chan(_));
                    let is_set = matches!(
                        shape,
                        TypeShape::Struct(Some(ref n)) if n.starts_with("set[") || n == "set"
                    );
                    if vars.len() > 1 && (is_chan || is_set) {
                        let kind_str = if is_chan { "channel" } else { "set" };
                        let why_note = if is_chan {
                            "why: Go permits only a single iteration variable when ranging over a channel (`range over … permits only one iteration variable`), so an accepted Hybrid program would emit unbuildable Go (LX13)".to_string()
                        } else {
                            "why: ranging over a set yields elements as single values; sets permit only one iteration variable (T9)".to_string()
                        };
                        let msg = format!(
                            "`for {}, {} in {}` binds {} variables, but ranging over a {} yields only 1 value (HYB-E2009)",
                            vars[0],
                            vars[1],
                            expr.render(),
                            vars.len(),
                            kind_str
                        );
                        let notes = vec![
                            why_note,
                            format!("fix: bind a single variable (`for {} in {} {{ … }}`)", vars[0], expr.render()),
                        ];
                        self.diags.push(
                            Diagnostic::error("HYB-E2009", self.path.clone(), span, msg)
                                .with_notes(notes),
                        );
                    } else if vars.len() > 2 {
                        let msg = format!(
                            "`for {} in {}` binds {} variables, but `for … in` permits at most 2 iteration variables (HYB-E2009)",
                            vars.join(", "),
                            expr.render(),
                            vars.len()
                        );
                        let notes = vec![
                            "why: Go's `range` clause permits at most two iteration variables (index/key and element), and the emitter cannot lower 3+ loop variables (LX13)".to_string(),
                            format!(
                                "fix: bind at most two variables (`for {}, {} in {} {{ … }}`)",
                                vars[0],
                                vars[1],
                                expr.render()
                            ),
                        ];
                        self.diags.push(
                            Diagnostic::error("HYB-E2009", self.path.clone(), span, msg)
                                .with_notes(notes),
                        );
                    }
                }
            }
            Stmt::For {
                kind:
                    ForKind::Range {
                        var,
                        lo,
                        hi,
                        inclusive,
                        ..
                    },
                ..
            } => {
                self.check_integer_range_bound(st, var, lo);
                self.check_integer_range_bound(st, var, hi);
                self.check_range_bound_types(st, lo, hi, *inclusive);
            }
            _ => {}
        }
    }
    /// Bypasses 3 and 4 from issue #827:
    /// 3. Mismatched integer types between `lo` and `hi`
    ///    (`for i in 0..n` where `n: u32`, `for i in lo..hi` where `lo: i32`
    ///    and `hi: i64`, etc.).
    /// 4. Constant integer bounds that overflow the loop counter's integer
    ///    type (`for i in 0..(1 << 63)`, `var lo i8 = 0; for i in lo..300`).
    fn check_range_bound_types(&mut self, st: &FnState, lo: &Expr, hi: &Expr, inclusive: bool) {
        let lo_ty = self.range_bound_int_type(st, lo);
        let hi_ty = self.range_bound_int_type(st, hi);

        // Both bounds carry concrete integer types: the emitted Go compares
        // two typed values, and Go rejects `int` vs `uint32` / `i32` vs
        // `i64` comparisons outright.
        if let (Some(lt), Some(ht)) = (&lo_ty, &hi_ty) {
            if lt != ht {
                self.emit_range_bound_mismatch(lo, hi, lt, ht);
                return;
            }
        }

        // Mixed typed/untyped bounds. An untyped bound is a constant, so:
        //   * exclusive (`for i := lo; i < hi; i++`): the counter `i` takes
        //     lo's type — or Go's default `int` when lo is untyped — and a
        //     typed `hi` of any other type makes `i < hi` a Go mismatch
        //     (`for i in 0..n` with `n: u32`);
        //   * inclusive (`hyLo := lo; hyHi := hi; … hyLo <= hyHi`): both
        //     bounds become independent variables, and an untyped constant
        //     gets the default type `int`, so a non-`int` typed bound next
        //     to an untyped one rejects (`for i in lo..=10`, `lo: i64`).
        match (&lo_ty, &hi_ty) {
            (Some(lt), None) => {
                if inclusive && lt != "int" {
                    self.emit_range_bound_mismatch(lo, hi, lt, "int");
                    return;
                }
            }
            (None, Some(ht)) => {
                if ht != "int" {
                    self.emit_range_bound_mismatch(lo, hi, "int", ht);
                    return;
                }
            }
            _ => {}
        }

        // Bypass 4: constant bounds that overflow the counter's integer
        // type. The effective counter type is the typed side when there is
        // one, and Go's default `int` for all-untyped bounds
        // (`for i in 0..(1 << 63)`).
        let counter_ty = lo_ty
            .clone()
            .or_else(|| hi_ty.clone())
            .unwrap_or_else(|| "int".to_string());
        for (bound_expr, bound_ty) in [(lo, lo_ty.as_deref()), (hi, hi_ty.as_deref())] {
            // A typed bound is compared at its own type; an untyped constant
            // bound adopts the counter's type.
            let Some(target_ty) = bound_ty.or(Some(counter_ty.as_str())) else {
                continue;
            };
            let Some((bmin, bmax)) = fixed_width_int_range(target_ty) else {
                continue;
            };
            // The const map borrows `self`, so every fold happens inside this
            // scope and only the owned verdict outlives it — the push below
            // needs `&mut self.diags`.
            let verdict = {
                let consts = self.collect_const_map(st);
                let mut folded = const_int_fold_with(bound_expr, &consts, 0, Some(st));
                if let ConstFold::NotConst = folded {
                    // Block-scoped `const` identifiers are not in the
                    // file-level map; resolve them at the use site.
                    folded = match unwrap_parens(bound_expr) {
                        Expr::Ident { name, span, .. } => {
                            match self.resolve_local_const_decl_at(name, span.start) {
                                Some((_ty, val, _pos)) => {
                                    const_int_fold_with(val, &consts, 0, None)
                                }
                                None => ConstFold::NotConst,
                            }
                        }
                        _ => ConstFold::NotConst,
                    };
                }
                match folded {
                    ConstFold::Val(v) if v < bmin || v > bmax => Some((
                        format!(
                            "constant `{}` overflows the `{}` loop counter bound (HYB-E2009)",
                            bound_expr.render(),
                            target_ty
                        ),
                        "why: the emitted Go rejects a constant outside the loop counter's fixed-width type (`constant … overflows …`), so an accepted Hybrid program would emit unbuildable Go".to_string(),
                        format!(
                            "fix: use a constant representable in `{}` (range {}..={})",
                            target_ty, bmin, bmax
                        ),
                    )),
                    ConstFold::TooBig => Some((
                        format!(
                            "constant `{}` is too large for the `{}` loop counter bound (HYB-E2009)",
                            bound_expr.render(),
                            target_ty
                        ),
                        "why: the constant's magnitude exceeds every fixed-width Hybrid integer range, so the emitted Go rejects it".to_string(),
                        "fix: reduce the constant expression or bind the bound to a local variable first".to_string(),
                    )),
                    _ => None,
                }
            };
            if let Some((msg, why, fix)) = verdict {
                let span = bound_expr.span();
                let notes = vec![why, fix];
                self.diags.push(
                    Diagnostic::error("HYB-E2009", self.path.clone(), span, msg)
                        .with_notes(notes),
                );
            }
        }
    }

    /// Emits the shared mismatch diagnostic for `check_range_bound_types`.
    fn emit_range_bound_mismatch(&mut self, lo: &Expr, hi: &Expr, lt: &str, ht: &str) {
        let span = hy_diag::Span {
            start: lo.span().start,
            end: hi.span().end,
        };
        let msg = format!(
            "`for i in {}..{}` — bounds have mismatched integer types (`{}` vs `{}`); `go build` rejects the comparison (HYB-E2009)",
            lo.render(),
            hi.render(),
            lt,
            ht
        );
        let notes = vec![
            "why: the emitted Go comparison requires identical integer types on both sides; an untyped constant bound adopts Go's default type `int`".to_string(),
            "fix: align the bound types (e.g. `for i in u32(0)..n`, or declare the bounds with matching `var` types)".to_string(),
        ];
        self.diags.push(
            Diagnostic::error("HYB-E2009", self.path.clone(), span, msg).with_notes(notes),
        );
    }
    /// Resolves the CONCRETE integer type of a range bound (`u32`, `i64`,
    /// `byte`, ...). Untyped operands — integer literals, unary negation of
    /// them, untyped `const` identifiers — have no concrete type here
    /// (Go adopts the other side's type, or the default `int` for the
    /// counter), so they return None; the default-type rules live in
    /// `check_range_bound_types`. Returns None if the bound is not a
    /// resolved integer.
    fn range_bound_int_type(&self, st: &FnState, expr: &Expr) -> Option<String> {
        match unwrap_parens(expr) {
            Expr::Ident { name, .. } => {
                if let Some(b) = st.env_lookup(name) {
                    if let Some(ty) = &b.ty {
                        let resolved = self.resolve_type_alias(ty);
                        if let TypeExpr::Named { name: tn, .. } = &resolved {
                            // Every fixed-width spelling (u8/uint8/byte,
                            // rune, int, uint, ...) — the emitted Go
                            // comparison must match Go's types exactly.
                            if fixed_width_int_range(tn).is_some() {
                                return Some(tn.clone());
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        if let Some(ty) = self.ty_of_expr(st, expr) {
            let resolved = self.resolve_type_alias(&ty);
            if let TypeExpr::Named { name, .. } = &resolved {
                if fixed_width_int_range(name).is_some() {
                    return Some(name.clone());
                }
            }
        }
        None
    }

    /// Collects a map of file-level and block-scoped constants (name -> value)
    /// for use in constant folding (`const_int_fold_with`).
    fn collect_const_map(&self, st: &FnState) -> HashMap<String, &Expr> {
        let mut map = HashMap::new();
        for d in &self.file.decls {
            if let hy_syntax::Decl::Const(c) = d {
                map.insert(c.name.clone(), &c.value);
            }
        }
        let _ = st;
        map
    }

    fn check_integer_range_bound(&mut self, st: &FnState, var: &str, bound: &Expr) {
        let non_int_desc = self.non_integer_bound_kind(st, bound);
        let Some(kind_desc) = non_int_desc else {
            return;
        };
        let span = bound.span();
        let msg = format!(
            "`{}` ({kind_desc}) is not an integer — `for {var} in lo..hi` requires integer range bounds (LX13) (HYB-E2009)",
            bound.render()
        );
        let notes = vec![
            "why: SPEC-LANGUAGE LX13 defines `for i in lo..hi` as an integer range lowered to `for i := lo; i < hi; i++`, which Go rejects on non-integer bounds".to_string(),
            "fix: use integer expressions for both `lo` and `hi` (e.g. `for i in 0..len(xs)`), or iterate a collection directly with `for x in xs`".to_string(),
        ];
        self.diags.push(
            Diagnostic::error("HYB-E2009", self.path.clone(), span, msg).with_notes(notes),
        );
    }

    fn non_integer_bound_kind(&self, st: &FnState, expr: &Expr) -> Option<String> {
        match unwrap_parens(expr) {
            Expr::Lit {
                kind: LitKind::Float(_),
                ..
            } => return Some("float".to_string()),
            Expr::Lit {
                kind: LitKind::Bool(_),
                ..
            } => return Some("bool".to_string()),
            Expr::Lit {
                kind: LitKind::Str(_) | LitKind::RawStr(_),
                ..
            }
            | Expr::Interp { .. } => return Some("string".to_string()),
            Expr::Lit {
                kind: LitKind::Nil,
                ..
            } => return Some("nil".to_string()),
            Expr::Unary { op, .. } if matches!(op, hy_syntax::UnOp::Not) => {
                return Some("bool".to_string());
            }
            Expr::Unary { op, .. } if matches!(op, hy_syntax::UnOp::Addr) => {
                return Some("pointer".to_string());
            }
            Expr::AddrOf { .. } => return Some("pointer".to_string()),
            Expr::Binary { op, .. } => {
                if matches!(
                    op,
                    hy_syntax::BinOp::Eq
                        | hy_syntax::BinOp::Ne
                        | hy_syntax::BinOp::Lt
                        | hy_syntax::BinOp::Gt
                        | hy_syntax::BinOp::Le
                        | hy_syntax::BinOp::Ge
                        | hy_syntax::BinOp::And
                        | hy_syntax::BinOp::Or
                ) {
                    return Some("bool".to_string());
                }
            }
            Expr::Ident { name, span } => {
                if name == "nil" {
                    return Some("nil".to_string());
                }
                if name == "true" || name == "false" {
                    return Some("bool".to_string());
                }
                if let Some(c) = self.file_const_decl(name) {
                    if let Some(k) = self.non_integer_bound_kind(st, &c.value) {
                        return Some(k);
                    }
                }
                if let Some((_ty, val, _pos)) =
                    self.resolve_local_const_decl_at(name, span.start)
                {
                    if let Some(k) = self.non_integer_bound_kind(st, val) {
                        return Some(k);
                    }
                }
            }
            Expr::Unary { operand, .. } => {
                if let Some(k) = self.non_integer_bound_kind(st, operand) {
                    return Some(k);
                }
            }
            _ => {}
        }
        if let Some(ty) = self.ty_of_expr(st, expr) {
            let resolved = self.resolve_type_alias(&ty);
            if let TypeExpr::Named { name, .. } = &resolved {
                if matches!(
                    name.as_str(),
                    "bool"
                        | "float32"
                        | "float64"
                        | "f32"
                        | "f64"
                        | "complex64"
                        | "complex128"
                        | "string"
                        | "error"
                ) {
                    return Some(resolved.render());
                }
            }
        }
        let shape = self.shape_of_expr(st, expr);
        match shape {
            TypeShape::Primitive | TypeShape::Unknown => None,
            other => Some(other.render()),
        }
    }

    /// Classify a range's ITERABLE — the mirror of `check_send_target`
    /// (issue #411): SPEC-LANGUAGE LX13 allows slices, arrays, strings,
    /// maps, and channels (plus L3 borrow views, which the shape layer
    /// already iterates — corpus 05/07/11/12, and the foreign element-source
    /// handles the emitter ranges via its ForeignTy branch). A concrete
    /// non-iterable is HYB-E2009; an unresolvable shape is fail-closed
    /// HYB-E3005 (O4.9), exactly as the send (#77) and receive (#409)
    /// sides treat an unknown operand. A TYPE contract, not a sendability
    /// doubt — `managed` does not suppress it.
    pub(crate) fn check_range_iterable(&mut self, st: &FnState, expr: &Expr, span: Span) {
        // Go: "array, pointer to array, slice, string, map, or channel" —
        // only pointer-to-ARRAY is rangeable (`*struct` / `*slice` /
        // `*string` are not), so normalize exactly one Pointer level for
        // arrays and leave every other shape as classified.
        let shape = match self.shape_of_expr(st, expr) {
            TypeShape::Pointer(inner) if matches!(*inner, TypeShape::Array(_)) => *inner,
            other => other,
        };
        match shape {
            TypeShape::Slice(_)
            | TypeShape::Array(_)
            | TypeShape::Str
            | TypeShape::Map(_, _)
            // The L3 borrow views (e.g. `doc.array("users")?` — the element
            // view the emitter iterates; corpus 05/07/11/12). Corpus-driven,
            // NOT a Go range shape — Go cannot range the view struct itself.
            | TypeShape::BorrowHandle(_) => {}
            TypeShape::Struct(Some(ref n)) if n.starts_with("set[") || n == "set" => {}
            TypeShape::Chan(_) => {
                let chan_ty = self.ty_of_expr(st, expr).or_else(|| {
                    if let Expr::Ident { name, .. } = unwrap_parens(expr) {
                        let root = crate::freeze::resolve_alias(st, name);
                        self.lookup_binding(st, &root).and_then(|b| b.ty.clone())
                    } else {
                        None
                    }
                });
                if let Some(ty) = chan_ty {
                    let resolved = self.resolve_type_alias(&ty);
                    if matches!(
                        resolved,
                        hy_syntax::TypeExpr::Chan {
                            dir: hy_syntax::ChanDir::Send,
                            ..
                        }
                    ) {
                        let msg = format!(
                            "cannot range over `{}` (`{}`) — channel is send-only (HYB-E2009)",
                            expr.render(),
                            resolved.render()
                        );
                        let notes = vec![
                            "why: Go rejects `range` over a `chan<- T` send-only channel (`invalid operation: cannot range over … (receive from send-only type)`), so an accepted Hybrid program would emit unbuildable Go".to_string(),
                            "fix: declare the parameter or binding as a bidirectional (`chan T`) or receive-only (`<-chan T`) channel".to_string(),
                        ];
                        self.diags.push(
                            Diagnostic::error("HYB-E2009", self.path.clone(), span, msg)
                                .with_notes(notes),
                        );
                    }
                }
            }
            // The foreign handles the emitter ranges as element sources
            // (the ForeignTy range branch); `serde_json.value` only —
            // other handles (`flate2.writer`) are not iterable and fall
            // through to the concrete-non-iterable arm.
            TypeShape::OwnHandle(ref t) if crate::foreign::is_iterable_handle(t) => {}
            TypeShape::Unknown => {
                let msg = format!(
                    "cannot prove `{}` is iterable — `for x in e` needs a slice, array, string, map, or channel (LX13; O4.9)",
                    expr.render()
                );
                let notes = vec![
                    "why: the checker cannot classify the iterable's type, and Go cannot range over it (issue #411)".to_string(),
                    "fix: bind the iterable to a local with a visible type first, so the checker can resolve it".to_string(),
                ];
                self.diags.push(
                    Diagnostic::error("HYB-E3005", self.path.clone(), span, msg).with_notes(notes),
                );
            }
            other => {
                let msg = format!(
                    "`{}` ({}) is not iterable — `for x in e` iterates slices, arrays, strings, maps, and channels (LX13)",
                    expr.render(),
                    other.render()
                );
                let notes = vec![
                    "why: ranging over a non-iterable is not valid Go (`cannot range over`); the accepted subset only emits buildable Go (issue #411)".to_string(),
                    "fix: iterate a slice/array/string/map/chan binding, or use the integer-range form `for i in 0..n`".to_string(),
                ];
                self.diags.push(
                    Diagnostic::error("HYB-E2009", self.path.clone(), span, msg).with_notes(notes),
                );
            }
        }
    }
}
