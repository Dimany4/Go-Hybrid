//! const_overflow.rs — constant initializers that would make the emitted
//! Go unbuildable (issue #148, extended by issue #201-B).
//!
//! `var n int8 = 300` (and the file-level `const` twin) pass `hyb check`
//! with 0 diagnostics today, then fail `go vet` / `go build` with
//! `cannot use 300 as int8 value (overflows)`. The accepted-should-
//! emit-buildable-Go contract requires a checker diagnostic (HYB-E6002)
//! for that narrow constant case. Issue #201-B extends the fold to
//! constant *expressions* (`100 + 100`, `1 << 10` — Go folds them before
//! the range check, so they overflow the same way) and to float constants
//! assigned to an integer type (`2.5` → Go `(truncated)`). Non-constant
//! operands stay out of scope — Go truncates at run time via an explicit
//! conversion (SPEC-LANGUAGE X4), and the conversion form `int8(x)` is
//! unaffected.
//!
//! Issue #725 extends the pass to TYPED constant ARITHMETIC: a constant
//! expression with a fixed-width TYPED operand (`const top u8 = 255; top + 1`,
//! `i64(1) << 63`, `u8(0) - 1`) folds in the OPERAND's type in Go and is
//! rejected there when the result (or an untyped operand converted to the
//! typed operand's type) is unrepresentable. The shared fold computed values
//! in arbitrary precision without the type (and conversions were NotConst),
//! so these passed with 0 diagnostics and failed `go build`.
//! `check_typed_const_arith` closes that gap at the init/default-int sites;

use crate::model::{unwrap_parens, Checker, FnState};
use hy_diag::{Diagnostic, Span};
use hy_syntax::{BinOp, CallArg, Expr, ForKind, InterpPart, LitKind, Place, PlaceKind, SelectArmKind, Stmt, TypeExpr, UnOp};
use std::collections::HashMap;

impl<'a> Checker<'a> {
    /// When `ty` is a fixed-width integer and `value` is an integer
    /// constant (literal or folded constant expression) outside that
    /// type's range, or a float constant, emit HYB-E6002.
    pub(crate) fn check_const_overflow_init(
        &mut self,
        name: &str,
        ty: &TypeExpr,
        value: &Expr,
        st: Option<&FnState>,
    ) {
        // Issue #725: typed-constant arithmetic inside the initializer
        // overflows in the OPERAND's type, independent of the init target.
        self.check_typed_const_arith(value, st);
        let resolved = self.resolve_type_alias(ty);
        let TypeExpr::Named {
            name: ty_name,
            span: ty_span,
        } = &resolved
        else {
            return;
        };
        if let Some(is_f32) = is_float_type(ty_name) {
            if let Some(f) = self.const_float_fold(value, st) {
                let overflows = if is_f32 {
                    (f as f32).is_infinite()
                } else {
                    f.is_infinite()
                };
                if overflows {
                    let span = value.span();
                    let msg = format!(
                        "constant `{}` overflows declared type `{}` of `{}` (HYB-E6002)",
                        value.render(),
                        ty_name,
                        name
                    );
                    let notes = vec![
                        format!(
                            "why: Go rejects a constant initializer that overflows `{}` (`cannot use {} as {} value (overflows)`), so an accepted Hybrid program would emit unbuildable Go (issue #683)",
                            ty_name, value.render(), ty_name
                        ),
                        format!(
                            "fix: use a finite `{}` value in range",
                            ty_name
                        ),
                        format!(
                            "note: the declared type was written here ({})",
                            span_hint(*ty_span)
                        ),
                    ];
                    self.diags.push(
                        Diagnostic::error("HYB-E6002", self.path.clone(), span, msg).with_notes(notes),
                    );
                }
            }
            return;
        }
        let Some((lo, hi)) = fixed_width_int_range(ty_name) else {
            return;
        };
        match const_int_fold_with(value, &self.const_values, 0, st) {
            ConstFold::NotConst => {}
            ConstFold::TooBig => {
                let span = value.span();
                let msg = format!(
                    "constant expression `{}` overflows declared type `{}` of `{}` (HYB-E6002)",
                    value.render(),
                    ty_name,
                    name
                );
                let notes = vec![
                    format!(
                        "why: Go folds the constant expression before the range check and rejects a value outside `{}` (`cannot use … as {} value (overflows)`), so an accepted Hybrid program would emit unbuildable Go (issue #201)",
                        ty_name, ty_name
                    ),
                    format!(
                        "fix: use a constant in [{}, {}] or widen the declared type",
                        lo, hi
                    ),
                    format!(
                        "note: the declared type was written here ({})",
                        span_hint(*ty_span)
                    ),
                ];
                self.diags.push(
                    Diagnostic::error("HYB-E6002", self.path.clone(), span, msg).with_notes(notes),
                );
                return;
            }
            ConstFold::Val(v) => {
                if v >= lo && v <= hi {
                    return;
                }
                let span = value.span();
                let msg = format!(
                    "constant `{}` overflows declared type `{}` of `{}` (HYB-E6002)",
                    value.render(),
                    ty_name,
                    name
                );
                let notes = vec![
                    format!(
                        "why: Go rejects a constant initializer outside `{}`'s range (`cannot use … as {} value (overflows)`), so an accepted Hybrid program would emit unbuildable Go (issue #148)",
                        ty_name, ty_name
                    ),
                    format!(
                        "fix: use a constant in [{}, {}], widen the declared type, or convert from a variable if truncation is intentional (`x := {}; y := {}(x)`)",
                        lo, hi, value.render(), ty_name
                    ),
                    format!(
                        "note: the declared type was written here ({})",
                        span_hint(*ty_span)
                    ),
                ];
                self.diags.push(
                    Diagnostic::error("HYB-E6002", self.path.clone(), span, msg).with_notes(notes),
                );
                return;
            }
        }
        // Issue #201-B: a float constant is never assignable to an integer
        // type in Go — `var x int = 2.5` fails with `(truncated)` (and a
        // magnitude that cannot fit fails with `(overflows)`).
        if let Some(f) = const_float_value(value) {
            let span = value.span();
            let msg = format!(
                "float constant `{}` assigned to integer type `{}` of `{}` (HYB-E6002)",
                value.render(),
                ty_name,
                name
            );
            let notes = vec![
                format!(
                    "why: Go rejects a float constant as an `{}` value (`cannot use … as {} value (truncated)`), so an accepted Hybrid program would emit unbuildable Go (issue #201)",
                    ty_name, ty_name
                ),
                format!(
                    "fix: drop the fractional part (`{}` → `{}`), use a float declared type, or convert from a variable if rounding is intentional",
                    value.render(),
                    integer_of_float(f)
                ),
                format!(
                    "note: the declared type was written here ({})",
                    span_hint(*ty_span)
                ),
            ];
            self.diags.push(
                Diagnostic::error("HYB-E6002", self.path.clone(), span, msg).with_notes(notes),
            );
        }
    }

    /// When `ty` is a fixed-width integer and `value` assigned to `target`
    /// is an integer constant outside that type's range, or a float constant, emit HYB-E6002.
    pub(crate) fn check_const_overflow_assign(
        &mut self,
        target: &str,
        ty: &TypeExpr,
        value: &Expr,
    ) {
        let resolved = self.resolve_type_alias(ty);
        let TypeExpr::Named {
            name: ty_name,
            span: ty_span,
        } = &resolved
        else {
            return;
        };
        if let Some(is_f32) = is_float_type(ty_name) {
            if let Some(f) = self.const_float_fold(value, None) {
                let overflows = if is_f32 {
                    (f as f32).is_infinite()
                } else {
                    f.is_infinite()
                };
                if overflows {
                    let span = value.span();
                    let msg = format!(
                        "constant `{}` overflows declared type `{}` of `{}` (HYB-E6002)",
                        value.render(),
                        ty_name,
                        target
                    );
                    let notes = vec![
                        format!(
                            "why: Go rejects a constant assignment that overflows `{}` (`cannot use {} as {} value in assignment (overflows)`), so an accepted Hybrid program would emit unbuildable Go (issue #683)",
                            ty_name, value.render(), ty_name
                        ),
                        format!(
                            "fix: use a finite `{}` value in range",
                            ty_name
                        ),
                        format!(
                            "note: the declared type was written here ({})",
                            span_hint(*ty_span)
                        ),
                    ];
                    self.diags.push(
                        Diagnostic::error("HYB-E6002", self.path.clone(), span, msg).with_notes(notes),
                    );
                }
            }
            return;
        }
        let Some((lo, hi)) = fixed_width_int_range(ty_name) else {
            return;
        };
        match const_int_fold(value) {
            ConstFold::NotConst => {}
            ConstFold::TooBig => {
                let span = value.span();
                let msg = format!(
                    "constant expression `{}` overflows declared type `{}` of `{}` (HYB-E6002)",
                    value.render(),
                    ty_name,
                    target
                );
                let notes = vec![
                    format!(
                        "why: Go folds the constant expression before the range check and rejects a value outside `{}` (`cannot use … as {} value (overflows)`), so an accepted Hybrid program would emit unbuildable Go (issue #300)",
                        ty_name, ty_name
                    ),
                    format!(
                        "fix: use a constant in [{}, {}] or widen the declared type",
                        lo, hi
                    ),
                    format!(
                        "note: the declared type was written here ({})",
                        span_hint(*ty_span)
                    ),
                ];
                self.diags.push(
                    Diagnostic::error("HYB-E6002", self.path.clone(), span, msg).with_notes(notes),
                );
                return;
            }
            ConstFold::Val(v) => {
                if v >= lo && v <= hi {
                    return;
                }
                let span = value.span();
                let msg = format!(
                    "constant `{}` overflows declared type `{}` of `{}` (HYB-E6002)",
                    value.render(),
                    ty_name,
                    target
                );
                let notes = vec![
                    format!(
                        "why: Go rejects a constant assignment outside `{}`'s range (`cannot use … as {} value (overflows)`), so an accepted Hybrid program would emit unbuildable Go (issue #300)",
                        ty_name, ty_name
                    ),
                    format!(
                        "fix: use a constant in [{}, {}], widen the declared type, or convert from a variable if truncation is intentional (`x := {}; {} = {}(x)`)",
                        lo, hi, value.render(), target, ty_name
                    ),
                    format!(
                        "note: the declared type was written here ({})",
                        span_hint(*ty_span)
                    ),
                ];
                self.diags.push(
                    Diagnostic::error("HYB-E6002", self.path.clone(), span, msg).with_notes(notes),
                );
                return;
            }
        }
        if const_float_value(value).is_some() {
            let span = value.span();
            let msg = format!(
                "float constant `{}` assigned to integer type `{}` of `{}` (HYB-E6002)",
                value.render(),
                ty_name,
                target
            );
            let notes = vec![
                format!(
                    "why: Go rejects a float constant as an `{}` value (`cannot use … as {} value (truncated)`), so an accepted Hybrid program would emit unbuildable Go (issue #300)",
                    ty_name, ty_name
                ),
                format!(
                    "fix: convert explicitly at runtime if truncation is intentional (`x := {}; {} = {}(x)`)",
                    value.render(), target, ty_name
                ),
                format!(
                    "note: the declared type was written here ({})",
                    span_hint(*ty_span)
                ),
            ];
            self.diags.push(
                Diagnostic::error("HYB-E6002", self.path.clone(), span, msg).with_notes(notes),
            );
        }
    }

    /// Check integer constants in variable declarations without an explicit
    /// type. Go gives these declarations the target's default `int` type.
    pub(crate) fn check_default_int_overflow(
        &mut self,
        name: &str,
        value: &Expr,
        st: Option<&FnState>,
    ) {
        // Issue #725: a typed constant operand must overflow in ITS type
        // before the untyped default-type check applies.
        self.check_typed_const_arith(value, st);
        let (lo, hi) = target_int_range();
        match const_int_fold_with(value, &self.const_values, 0, st) {
            ConstFold::NotConst => return,
            ConstFold::Val(v) if v >= lo && v <= hi => return,
            ConstFold::Val(_) | ConstFold::TooBig => {}
        }

        let span = value.span();
        let msg = format!(
            "constant expression `{}` overflows default type `int` of `{}` (HYB-E6002)",
            value.render(),
            name
        );
        let notes = vec![
            "why: Go assigns default type `int` to an untyped integer constant in a variable declaration and rejects values outside the target int range, so an accepted Hybrid program would emit unbuildable Go (issue #228)"
                .to_string(),
            format!(
                "fix: use a value in [{}, {}], declare an explicit wider type, or keep the value as an untyped constant",
                lo, hi
            ),
        ];
        self.diags.push(
            Diagnostic::error("HYB-E6002", self.path.clone(), span, msg).with_notes(notes),
        );
    }

    /// Check untyped float constants in variable declarations without an explicit
    /// type. Go gives these declarations the default `float64` type.
    pub(crate) fn check_default_float_overflow(
        &mut self,
        name: &str,
        value: &Expr,
        st: Option<&FnState>,
    ) {
        if !is_float_const_expr(value, &self.const_values, 0, st) {
            return;
        }
        if let Some(f) = self.const_float_fold(value, st) {
            if f.is_infinite() {
                let span = value.span();
                let msg = format!(
                    "constant expression `{}` overflows default type `float64` of `{}` (HYB-E6002)",
                    value.render(),
                    name
                );
                let notes = vec![
                    format!(
                        "why: Go assigns default type `float64` to an untyped float constant in a variable declaration and rejects values outside float64's range (`cannot use {} as float64 value in assignment (overflows)`), so an accepted Hybrid program would emit unbuildable Go (issue #683)",
                        value.render()
                    ),
                    "fix: use a finite `float64` value in range, or declare an explicit type".to_string(),
                ];
                self.diags.push(
                    Diagnostic::error("HYB-E6002", self.path.clone(), span, msg).with_notes(notes),
                );
            }
        }
    }

    /// Fold a constant float expression (literals, identifiers, unary, binary).
    pub(crate) fn const_float_fold(&self, e: &Expr, st: Option<&FnState>) -> Option<f64> {
        const_float_fold_with(e, &self.const_values, 0, st)
    }

    // -----------------------------------------------------------------------
    // Issue #228 family C: constant misuse in TYPE CONVERSION CALLS
    // -----------------------------------------------------------------------
    //
    // `int8(300)` (Go spelling), `int8(2.5)`, `int("abc")`, `string(2.5)`,
    // `int(10^30)`, `[]int(3)` all pass `hyb check` with 0 diagnostics and
    // then fail `go build` on the emitted program. SUB-64 integer overflow
    // in a conversion is deliberately NOT rejected here: SPEC-LANGUAGE
    // line 1991's executable claim `u8(300) == 44` makes the emitter fold
    // the two's-complement truncation (constconv.rs), and the same fold now
    // applies to the Go spellings (`int8(300)` -> `int8(44)`). This pass
    // covers the rest of the literal-constant matrix the fold cannot (the
    // same literal-only scope as E6001/E6002 — issue #149/#148).

    /// Pass-B entry: same statement surface (and same deep-closure rule) as
    /// `check_stmt_const_zero_divisor`.
    pub(crate) fn check_stmt_type_conversions(&mut self, stmt: &Stmt) {
        self.check_stmt_type_conversions_inner(stmt, /*deep=*/ false);
    }

    fn check_stmt_type_conversions_inner(&mut self, stmt: &Stmt, deep: bool) {
        match stmt {
            Stmt::Local(l) => {
                for v in &l.values {
                    self.check_expr_type_conversions(v);
                }
            }
            Stmt::Assign { targets, values, .. } => {
                for t in targets {
                    self.check_place_type_conversions(t);
                }
                for v in values {
                    self.check_expr_type_conversions(v);
                }
            }
            Stmt::Expr { expr, .. } => self.check_expr_type_conversions(expr),
            Stmt::Send { chan, value, .. } => {
                self.check_expr_type_conversions(chan);
                self.check_expr_type_conversions(value);
            }
            Stmt::If {
                init,
                cond,
                then,
                otherwise,
                ..
            } => {
                if deep {
                    if let Some(init) = init {
                        self.check_stmt_type_conversions_inner(init, true);
                    }
                }
                self.check_expr_type_conversions(cond);
                if deep {
                    for s in &then.stmts {
                        self.check_stmt_type_conversions_inner(s, true);
                    }
                    if let Some(other) = otherwise {
                        self.check_stmt_type_conversions_inner(other, true);
                    }
                }
            }
            Stmt::For { kind, body, .. } => {
                match kind {
                    ForKind::While { cond } => self.check_expr_type_conversions(cond),
                    ForKind::Range { lo, hi, .. } => {
                        self.check_expr_type_conversions(lo);
                        self.check_expr_type_conversions(hi);
                    }
                    ForKind::Iterate { expr, .. } => self.check_expr_type_conversions(expr),
                    ForKind::Infinite => {}
                }
                if deep {
                    for s in &body.stmts {
                        self.check_stmt_type_conversions_inner(s, true);
                    }
                }
            }
            Stmt::Return { values, .. } => {
                for v in values {
                    self.check_expr_type_conversions(v);
                }
            }
            Stmt::Task { callee, args, .. } => {
                self.check_expr_type_conversions(callee);
                for a in args {
                    self.check_expr_type_conversions(&a.value);
                }
            }
            Stmt::Managed { body, .. } => {
                if deep {
                    for s in &body.stmts {
                        self.check_stmt_type_conversions_inner(s, true);
                    }
                }
            }
            Stmt::Match { subject, arms, .. } => {
                self.check_expr_type_conversions(subject);
                for arm in arms {
                    if let Some(g) = &arm.guard {
                        self.check_expr_type_conversions(g);
                    }
                    if deep {
                        for s in &arm.body.stmts {
                            self.check_stmt_type_conversions_inner(s, true);
                        }
                    }
                }
            }
            Stmt::Defer { call, .. } => self.check_expr_type_conversions(call),
            Stmt::Break { .. } | Stmt::Continue { .. } => {}
            Stmt::Block { block, .. } => {
                if deep {
                    for s in &block.stmts {
                        self.check_stmt_type_conversions_inner(s, true);
                    }
                }
            }
            Stmt::Select { arms, .. } => {
                for arm in arms {
                    match &arm.kind {
                        SelectArmKind::Send { chan, value, is_move: _ } => {
                            self.check_expr_type_conversions(chan);
                            self.check_expr_type_conversions(value);
                        }
                        SelectArmKind::Recv { chan, .. } => self.check_expr_type_conversions(chan),
                        SelectArmKind::Default => {}
                    }
                    if deep {
                        for s in &arm.body.stmts {
                            self.check_stmt_type_conversions_inner(s, true);
                        }
                    }
                }
            }
        }
    }

    fn check_place_type_conversions(&mut self, place: &Place) {
        match &place.kind {
            PlaceKind::Ident(_) => {}
            PlaceKind::Index { base, index } => {
                self.check_place_type_conversions(base);
                self.check_expr_type_conversions(index);
            }
            PlaceKind::Field { base, .. } | PlaceKind::AddrOf { base } => {
                self.check_place_type_conversions(base)
            }
        }
    }

    pub(crate) fn check_expr_type_conversions(&mut self, expr: &Expr) {
        match expr {
            Expr::Binary { lhs, rhs, .. } => {
                self.check_expr_type_conversions(lhs);
                self.check_expr_type_conversions(rhs);
            }
            Expr::Unary { operand, .. }
            | Expr::AddrOf { operand, .. }
            | Expr::Move { operand, .. }
            | Expr::Try { operand, .. }
            | Expr::Paren { inner: operand, .. }
            | Expr::Field { base: operand, .. }
            | Expr::Receive { chan: operand, .. } => {
                self.check_expr_type_conversions(operand)
            }
            Expr::Index { base, index, .. } => {
                self.check_expr_type_conversions(base);
                self.check_expr_type_conversions(index);
            }
            Expr::Slice { base, lo, hi, .. } => {
                self.check_expr_type_conversions(base);
                if let Some(lo) = lo {
                    self.check_expr_type_conversions(lo);
                }
                if let Some(hi) = hi {
                    self.check_expr_type_conversions(hi);
                }
            }
            Expr::Call {
                callee,
                args,
                span,
            } => {
                self.check_expr_type_conversions(callee);
                for a in args {
                    self.check_expr_type_conversions(&a.value);
                }
                self.check_conversion_call(callee, args, *span);
            }
            Expr::StructLit { fields, .. } => {
                for f in fields {
                    self.check_expr_type_conversions(&f.value);
                }
            }
            Expr::SliceLit { items, .. } => {
                for i in items {
                    self.check_expr_type_conversions(i);
                }
            }
            Expr::MapLit { entries, .. } => {
                for (k, v) in entries {
                    self.check_expr_type_conversions(k);
                    self.check_expr_type_conversions(v);
                }
            }
            Expr::Interp { parts, .. } => {
                for p in parts {
                    if let InterpPart::Expr(e) = p {
                        self.check_expr_type_conversions(e);
                    }
                }
            }
            Expr::FnLit { body, .. } => {
                // Closure bodies are not flattened into Pass B — deep-walk.
                for stmt in &body.stmts {
                    self.check_stmt_type_conversions_inner(stmt, /*deep=*/ true);
                }
            }
            Expr::Ident { .. } | Expr::Lit { .. } => {}
        }
    }

    /// One conversion-call site: a one-argument `Type(const)` where Go
    /// would refuse the compile.
    fn check_conversion_call(&mut self, callee: &Expr, args: &[CallArg], span: Span) {
        if args.len() != 1 || args[0].spread {
            // arity of a conversion is the emitter's own guard; spread is
            // not a conversion shape.
            return;
        }
        let arg = unwrap_parens(&args[0].value);
        let callee = unwrap_parens(callee); // #823: parens are transparent
        // `[]byte("abc")` — a slice type-as-value called with one argument
        // (the standing type-as-value encoding; see hy-emit's conversion
        // branch for the emission half of issue #228).
        if let Expr::SliceLit {
            elem: Some(t),
            items,
            ..
        } = callee
        {
            if items.is_empty() && callee.as_array_lit().is_none() {
                self.check_slice_conversion(t, arg, span);
                return;
            }
        }
        let Expr::Ident { name, span: id_span, .. } = callee else {
            return;
        };
        // #823: resolve type aliases — `type my_int = int; my_int("abc")`
        // and `type my_slice = []int; my_slice("abc")` are conversion calls
        // of the aliased type, not free function calls. `resolve_type_alias`
        // handles nesting (`type b = a; type a = int`).
        let dummy = TypeExpr::Named {
            name: name.clone(),
            span: *id_span,
        };
        match self.resolve_type_alias(&dummy) {
            TypeExpr::Named { name: target, .. } => {
                if is_conversion_target(&target) {
                    let is_lit = matches!(arg, Expr::Lit { .. });
                    let Some(c) = self.conv_const(arg, 0) else {
                        return; // non-constant operand: run-time conversion (SPEC X4)
                    };
                    self.check_conv_against_target(&target, &c, arg, span, is_lit);
                    return;
                }
            }
            TypeExpr::Slice { elem, .. } => {
                self.check_slice_conversion(&elem, arg, span);
                return;
            }
            _ => {}
        }
        if !is_conversion_target(name) {
            return;
        }
        let is_lit = matches!(arg, Expr::Lit { .. });
        let Some(c) = self.conv_const(arg, 0) else {
            return; // non-constant operand: run-time conversion (SPEC X4)
        };
        self.check_conv_against_target(name, &c, arg, span, is_lit);
    }

    fn check_slice_conversion(&mut self, elem: &TypeExpr, arg: &Expr, span: Span) {
        let TypeExpr::Named { name: slice_elem, .. } = elem else {
            return; // []T with a non-named element + a run-time operand
        };
        // #823: resolve element type aliases — `type my_elem = u8;
        // []my_elem("abc")` is a string -> []byte conversion, and
        // `type my_elem = int; []my_elem("abc")` is an error.
        let resolved_elem = self
            .type_aliases
            .get(slice_elem)
            .and_then(|ty| {
                if let TypeExpr::Named { name: target, .. } = ty {
                    Some(target.clone())
                } else {
                    None
                }
            })
            .unwrap_or_else(|| slice_elem.clone());
        match self.conv_const(arg, 0) {
            Some(ConvConst::Str) => {
                // Go allows string -> []byte / []rune (and their aliases)
                // only; every other element type is a compile error.
                if !matches!(
                    resolved_elem.as_str(),
                    "u8" | "byte" | "uint8" | "i32" | "int32" | "rune"
                ) {
                    self.emit_const_conversion_error(
                        span,
                        format!(
                            "a string constant cannot be converted to a `{}` slice (HYB-E6006)",
                            resolved_elem
                        ),
                        vec![
                            format!(
                                "why: Go only allows string -> []byte / []rune conversions; `[]{}(\"…\")` fails to build (`cannot convert ... to type []{}`), so an accepted Hybrid program would emit unbuildable Go (issue #228)",
                                resolved_elem, resolved_elem
                            ),
                            "fix: convert to `[]byte` (or `[]rune` for text) first, or use a run-time operand whose type matches the target slice".to_string(),
                        ],
                    );
                }
            }
            Some(c) => {
                self.emit_const_conversion_error(
                    span,
                    format!(
                        "a {} constant cannot be converted to a `{}` slice (HYB-E6006)",
                        c.kind_name(),
                        resolved_elem
                    ),
                    vec![
                        format!(
                            "why: Go has no constant-to-slice conversion; `[]{}({})` fails to build (`invalid operation: cannot convert ...`), so an accepted Hybrid program would emit unbuildable Go (issue #228)",
                            resolved_elem,
                            arg.render()
                        ),
                        "fix: build the slice explicitly (e.g. `[]{}{{{}}}` or `make([]{}, n)` with a variable length)".to_string(),
                    ],
                );
            }
            None => {} // run-time operand: element-type errors are Go's
        }
    }

    fn check_conv_against_target(
        &mut self,
        target: &str,
        c: &ConvConst,
        arg: &Expr,
        span: Span,
        is_lit: bool,
    ) {
        if let Some((lo, hi)) = fixed_width_int_range(target) {
            match c {
                ConvConst::Int(v) => {
                    if *v < lo || *v > hi {
                        // Only reject when the emitter cannot fold this constant
                        // into a legal literal. 64-bit targets never fold, so they
                        // reject everything. Sub-64 targets fold bare literals and
                        // simple unary negations (`uint8(-1)` — upstream
                        // tests/const_conversion.rs sub64 accept set), so only flag
                        // constants that are *not* one of these simple foldable
                        // forms; const identifiers and constant arithmetic (#823)
                        // are not rewritten by the fold, so they still reject.
                        if is_64bit_int_target(target)
                            || !(is_lit || is_simple_unary_negation(arg))
                        {
                            // 64-bit targets skip the emitter's X4 fold, and
                            // non-literal operands (#823: const identifiers,
                            // constant arithmetic) are not rewritten by it
                            // either — Go rejects them outright.
                            self.emit_const_conversion_error(
                                span,
                                format!(
                                    "constant `{}` overflows `{}` in a conversion (HYB-E6006)",
                                    arg.render(),
                                    target
                                ),
                                vec![
                                    format!(
                                        "why: Go rejects `{}({})` at compile time (`constant ... overflows {}`), so an accepted Hybrid program would emit unbuildable Go (issue #228)",
                                        target,
                                        arg.render(),
                                        target
                                    ),
                                    format!(
                                        "fix: use a constant in [{}, {}], or widen the target type",
                                        lo, hi
                                    ),
                                ],
                            );
                        }
                        // sub-64 LITERAL targets: the emitter's SPEC X4 fold
                        // rewrites the constant (u8(300) == 44) — accepted
                        // on purpose.
                    }
                }
                ConvConst::Char(v) => {
                    if (*v as i128) < lo || (*v as i128) > hi {
                        // The fold only rewrites integer LITERALS, so an
                        // out-of-range rune must reject (Go: `constant 256
                        // overflows byte` for `byte('Ā')`).
                        self.emit_const_conversion_error(
                            span,
                            format!(
                                "rune constant `{}` is out of range for `{}` in a conversion (HYB-E6006)",
                                arg.render(),
                                target
                            ),
                            vec![
                                format!(
                                    "why: Go rejects `{}({})` at compile time (the code point does not fit `{}`), so an accepted Hybrid program would emit unbuildable Go (issue #228)",
                                    target,
                                    arg.render(),
                                    target
                                ),
                                format!(
                                    "fix: use a rune in [{}, {}], or convert from a variable if truncation is intended",
                                    lo, hi
                                ),
                            ],
                        );
                    }
                }
                ConvConst::Float(f) => {
                    if !(f.fract() == 0.0 && *f >= lo as f64 && *f <= hi as f64) {
                        self.emit_const_conversion_error(
                            span,
                            format!(
                                "constant `{}` is not representable in `{}` in a conversion (HYB-E6006)",
                                arg.render(),
                                target
                            ),
                            vec![
                                format!(
                                    "why: Go only converts an untyped float constant to `{}` when it has no fractional part and fits the range (`cannot convert ...` / `overflows`), so an accepted Hybrid program would emit unbuildable Go (issue #228)",
                                    target
                                ),
                                format!(
                                    "fix: use an integer constant in [{}, {}], or bind the value to a variable first",
                                    lo, hi
                                ),
                            ],
                        );
                    }
                }
                ConvConst::Huge { .. } => {
                    // Out of i128 — past every fixed-width target; the
                    // emitter's fold cannot parse it either.
                    self.emit_const_conversion_error(
                        span,
                        format!(
                            "integer constant `{}` does not fit `{}` in a conversion (HYB-E6006)",
                            arg.render(),
                            target
                        ),
                        vec![
                            format!(
                                "why: Go rejects `{}({})` at compile time (`constant ... overflows {}`), so an accepted Hybrid program would emit unbuildable Go (issue #228)",
                                target,
                                arg.render(),
                                target
                            ),
                            format!(
                                "fix: use a constant in [{}, {}], or widen the target type",
                                lo, hi
                            ),
                        ],
                    );
                }
                ConvConst::Str | ConvConst::Bool | ConvConst::Nil => {
                    self.emit_conv_kind_error(target, c, arg, span);
                }
            }
            return;
        }
        match target {
            // float targets: every i128 fits f64; f32's max (3.4e38)
            // exceeds i128's max (1.7e38), so integer/runes always fit.
            // Past-i128 literals carry their f64 reading and still have to
            // respect f32's max (`float32(1e40)` overflows f32 in Go).
            "f32" | "f64" | "float32" | "float64" => match c {
                ConvConst::Float(f) | ConvConst::Huge { f, .. } => {
                    let overflows = !f.is_finite()
                        || (is_f32_target(target) && f.abs() > f32::MAX as f64);
                    if overflows {
                        self.emit_const_conversion_error(
                            span,
                            format!(
                                "constant `{}` overflows `{}` in a conversion (HYB-E6006)",
                                arg.render(),
                                target
                            ),
                            vec![
                                format!(
                                    "why: Go rejects `{}({})` at compile time (`constant ... overflows {}`), so an accepted Hybrid program would emit unbuildable Go (issue #228)",
                                    target,
                                    arg.render(),
                                    target
                                ),
                                format!(
                                    "fix: use a constant within `{}` range, or widen the target type to `f64`",
                                    target
                                ),
                            ],
                        );
                    }
                }
                ConvConst::Str | ConvConst::Bool | ConvConst::Nil => {
                    self.emit_conv_kind_error(target, c, arg, span)
                }
                ConvConst::Int(_) | ConvConst::Char(_) => {}
            },
            "string" => match c {
                ConvConst::Str
                | ConvConst::Int(_)
                | ConvConst::Char(_)
                | ConvConst::Huge {
                    lt_512: true, ..
                } => {
                    // Go-legal: `string(65)`, `string("…")`, and huge
                    // rune-valued integers build — verified up to the
                    // 2^512 boundary (go1.25: `string(2^512 - 1)` builds,
                    // `string(2^512)` is `constant overflow`).
                }
                ConvConst::Huge {
                    lt_512: false, ..
                } => {
                    self.emit_const_conversion_error(
                        span,
                        format!(
                            "integer constant `{}` does not fit the conversion to `string` (HYB-E6006)",
                            arg.render()
                        ),
                        vec![
                            format!(
                                "why: Go rejects `string({})` at compile time (`constant overflow` — string conversions accept integer constants below 2^512), so an accepted Hybrid program would emit unbuildable Go (issue #228)",
                                arg.render()
                            ),
                            "fix: use a smaller constant (below 2^512), or convert from a variable".to_string(),
                        ],
                    );
                }
                ConvConst::Float(_) | ConvConst::Bool | ConvConst::Nil => {
                    self.emit_conv_kind_error(target, c, arg, span)
                }
            },
            "bool" => match c {
                ConvConst::Bool => {}
                _ => self.emit_conv_kind_error(target, c, arg, span),
            },
            _ => {}
        }
    }

    fn emit_conv_kind_error(&mut self, target: &str, c: &ConvConst, arg: &Expr, span: Span) {
        self.emit_const_conversion_error(
            span,
            format!(
                "a {} constant cannot be converted to `{}` (HYB-E6006)",
                c.kind_name(),
                target
            ),
            vec![
                format!(
                    "why: Go rejects `{}({})` at compile time (`cannot convert {} to type {}`), so an accepted Hybrid program would emit unbuildable Go (issue #228)",
                    target,
                    arg.render(),
                    arg.render(),
                    target
                ),
                "fix: use a constant of a convertible kind (numbers and strings convert between numeric/string types), or bind the operand to a variable first".to_string(),
            ],
        );
    }

    fn emit_const_conversion_error(&mut self, span: Span, msg: String, notes: Vec<String>) {
        self.diags
            .push(Diagnostic::error("HYB-E6006", self.path.clone(), span, msg).with_notes(notes));
    }
    // ---- Issue #725: typed constant ARITHMETIC overflow (HYB-E6002) ----
    //
    // `const top u8 = 255; a := top + 1` and `b := i64(1) << 63` pass
    // `hyb check` today: the #201-B fold (`const_int_fold_with`) computes
    // values in arbitrary precision but drops the operands' fixed-width
    // type, and conversion calls it cannot fold (`i64(1)`) make the whole
    // expression `NotConst`. Go folds the same expressions in the OPERAND's
    // type and rejects (`top + 1 (constant 256 of type uint8) overflows
    // uint8`), so the accepted program emits unbuildable Go (GUARANTEES
    // Row 13 / BUILDABLE).
    //
    // This walker re-checks exactly that shape: a Binary/Unary constant
    // expression with at least one fixed-width TYPED constant operand (a
    // file-level `const` with a type ascription, or a spec conversion of a
    // constant) must fold to a value representable in that type.
    // Conversions keep the SPEC X4 wrap semantics `hy-emit`'s constconv
    // fold already applies (`u8(300)` → `uint8(44)`), so checker and
    // emitter agree; operands are walked first, so a nested overflow is
    // reported at the inner expression.
    //
    // Out of scope, documented: float-typed constants (no integer overflow
    // domain), local typed `const` (the shared fold treats local `const`
    // bindings as runtime values), comparison operands (bool result, no
    // overflow domain), Go-spelled conversion names (`uint8`, `int64`, … —
    // ordinary identifiers per LX3/#728), closure bodies (closures.rs
    // scope), and assignment sites (`check_const_overflow_assign` carries
    // no FnState, so the local-shadowing rule cannot be applied there
    // safely — the init sites below cover the reported shape).
    pub(crate) fn check_typed_const_arith(&mut self, e: &Expr, st: Option<&FnState>) {
        match unwrap_parens(e) {
            Expr::Binary { op, lhs, rhs, .. } => {
                self.check_typed_const_arith(lhs, st);
                self.check_typed_const_arith(rhs, st);
                use hy_syntax::BinOp::*;
                let is_shift = matches!(op, Shl | Shr);
                let arith = matches!(op, Add | Sub | Mul | Div | Mod | Shl | Shr);
                if !arith {
                    return;
                }
                let lt = self.typed_const_of(lhs, 0, st);
                let rt = self.typed_const_of(rhs, 0, st);
                // Shifts take their type from the LEFT operand only (the
                // count is an arbitrary-width non-negative int in Go).
                let typed = if is_shift {
                    lt.clone()
                } else {
                    lt.clone().or(rt.clone())
                };
                let Some(t) = typed else {
                    return;
                };
                let (lo, hi) = fixed_width_int_range(&t.ty).unwrap_or((i128::MIN, i128::MAX));
                // A non-shift untyped constant operand must itself be
                // representable in the typed operand's type (Go converts it
                // there before the operation).
                if !is_shift {
                    if lt.is_none() {
                        self.check_typed_operand_fits(rhs, st, &t.ty, lo, hi);
                    }
                    if rt.is_none() {
                        self.check_typed_operand_fits(lhs, st, &t.ty, lo, hi);
                    }
                }
                let l = self.typed_const_value_of(lhs, st);
                let r = self.typed_const_value_of(rhs, st);
                match fold_bin(*op, l, r) {                    ConstFold::Val(v) => {
                        if v < lo || v > hi {
                            let span = e.span();
                            let msg = format!(
                                "typed constant expression `{}` = {} overflows `{}` (range [{}, {}]) (HYB-E6002)",
                                e.render(),
                                v,
                                t.ty,
                                lo,
                                hi
                            );
                            let notes = vec![
                                format!(
                                    "why: Go folds the constant expression in the operand's type and rejects it (`constant {} of type {} overflows {}`), so an accepted Hybrid program would emit unbuildable Go (issue #725)",
                                    v, t.ty, t.ty
                                ),
                                format!(
                                    "fix: keep the constant in [{}, {}], widen the operand type, or convert from a runtime variable if wrapping is intentional",
                                    lo, hi
                                ),
                            ];
                            self.diags.push(
                                Diagnostic::error("HYB-E6002", self.path.clone(), span, msg)
                                    .with_notes(notes),
                            );
                        }
                    }
                    ConstFold::TooBig => {
                        let span = e.span();
                        let msg = format!(
                            "typed constant expression `{}` overflows `{}` (HYB-E6002)",
                            e.render(),
                            t.ty
                        );
                        let notes = vec![
                            format!(
                                "why: Go folds the constant expression in the operand's type and rejects a value outside `{}` (`constant … of type {} overflows {}`), so an accepted Hybrid program would emit unbuildable Go (issue #725)",
                                t.ty, t.ty, t.ty
                            ),
                            format!(
                                "fix: keep the constant in [{}, {}], widen the operand type, or convert from a runtime variable if wrapping is intentional",
                                lo, hi
                            ),
                        ];
                        self.diags.push(
                            Diagnostic::error("HYB-E6002", self.path.clone(), span, msg)
                                .with_notes(notes),
                        );
                    }
                    ConstFold::NotConst => {}
                }
            }            Expr::Unary { op: UnOp::Neg, operand, .. } => {
                self.check_typed_const_arith(operand, st);
                if let Some(t) = self.typed_const_of(operand, 0, st) {
                    let (lo, hi) = fixed_width_int_range(&t.ty).unwrap_or((i128::MIN, i128::MAX));
                    let overflow = match t.val.checked_neg() {
                        Some(v) => v < lo || v > hi,
                        None => true,
                    };
                    if overflow {
                        let span = e.span();
                        let msg = format!(
                            "typed constant expression `{}` overflows `{}` (range [{}, {}]) (HYB-E6002)",
                            e.render(),
                            t.ty,
                            lo,
                            hi
                        );
                        let notes = vec![
                            format!(
                                "why: Go folds `-({})` in the operand's type `{}` and rejects the result (`constant … of type {} overflows {}`), so an accepted Hybrid program would emit unbuildable Go (issue #725)",
                                operand.render(),
                                t.ty,
                                t.ty,
                                t.ty
                            ),
                            format!(
                                "fix: use a value whose negation fits in [{}, {}], or widen the operand type",
                                lo, hi
                            ),
                        ];
                        self.diags.push(
                            Diagnostic::error("HYB-E6002", self.path.clone(), span, msg)
                                .with_notes(notes),
                        );
                    }
                }
            }
            Expr::Unary { operand, .. } => self.check_typed_const_arith(operand, st),
            Expr::Call { args, .. } => {
                for a in args {
                    self.check_typed_const_arith(&a.value, st);
                }
            }
            Expr::Index { base, index, .. } => {
                self.check_typed_const_arith(base, st);
                self.check_typed_const_arith(index, st);
            }
            Expr::Field { base, .. } => self.check_typed_const_arith(base, st),
            Expr::Slice { base, lo, hi, .. } => {
                self.check_typed_const_arith(base, st);
                if let Some(x) = lo {
                    self.check_typed_const_arith(x, st);
                }
                if let Some(x) = hi {
                    self.check_typed_const_arith(x, st);
                }
            }
            Expr::SliceLit { items, .. } => {
                for i in items {
                    self.check_typed_const_arith(i, st);
                }
            }
            Expr::MapLit { entries, .. } => {
                for (k, v) in entries {
                    self.check_typed_const_arith(k, st);
                    self.check_typed_const_arith(v, st);
                }
            }
            Expr::StructLit { fields, .. } => {
                for f in fields {
                    self.check_typed_const_arith(&f.value, st);
                }
            }
            Expr::Interp { parts, .. } => {
                for p in parts {
                    if let InterpPart::Expr(x) = p {
                        self.check_typed_const_arith(x, st);
                    }
                }
            }
            // FnLit bodies are the closures.rs pass's scope; literals are done.
            _ => {}
        }
    }    /// A non-typed constant operand of a typed constant expression must be
    /// representable in the typed operand's type (Go converts it there
    /// before the operation: `top - 300` fails even though only `300` is
    /// out of `u8` range). Runtime operands fold to NotConst and skip.
    fn check_typed_operand_fits(&mut self, e: &Expr, st: Option<&FnState>, ty: &str, lo: i128, hi: i128) {
        if self.typed_const_of(e, 0, st).is_some() {
            return;
        }
        match const_int_fold_with(e, &self.const_values, 0, st) {
            ConstFold::Val(v) if v < lo || v > hi => {
                let span = e.span();
                let msg = format!(
                    "constant `{}` overflows `{}` in a typed constant expression (HYB-E6002)",
                    e.render(),
                    ty
                );
                let notes = vec![
                    format!(
                        "why: Go converts the untyped constant operand to the typed operand's type `{}` before the operation (`constant {} overflows {}`), so an accepted Hybrid program would emit unbuildable Go (issue #725)",
                        ty, v, ty
                    ),
                    format!(
                        "fix: use an operand in [{}, {}], or convert from a runtime variable",
                        lo, hi
                    ),
                ];
                self.diags.push(
                    Diagnostic::error("HYB-E6002", self.path.clone(), span, msg).with_notes(notes),
                );
            }
            _ => {}
        }
    }

    /// The constant integer value of `e`, preferring the typed reading (a
    /// spec conversion of a constant is `NotConst` for the shared fold).
    fn typed_const_value_of(&self, e: &Expr, st: Option<&FnState>) -> ConstFold {
        match self.typed_const_of(e, 0, st) {
            Some(t) => ConstFold::Val(t.val),
            None => const_int_fold_with(e, &self.const_values, 0, st),
        }
    }    /// The constant value of `e` WITH its fixed-width integer type, when it
    /// is a typed constant: a file-level `const` with a fixed-width type
    /// ascription, a Hybrid-spec conversion of a constant (X4 wrap — the
    /// same two's-complement truncation `hy-emit`'s constconv fold applies),
    /// a negation of one, or an arithmetic combination whose result fits
    /// (an overflowing sub-expression is rejected at its own node first, so
    /// `None` here means the walker already diagnosed it, the operand is
    /// runtime, or the type is not fixed-width).
    fn typed_const_of(&self, e: &Expr, depth: u32, st: Option<&FnState>) -> Option<TypedConst> {
        if depth > 32 {
            return None;
        }
        match unwrap_parens(e) {
            Expr::Ident { name, .. } => {
                if let Some(st) = st {
                    if st.env_lookup(name).is_some() {
                        // A local binding shadows the file-level const (same
                        // rule as `const_int_fold_with`); local typed consts
                        // are outside this pass's scope.
                        return None;
                    }
                }
                let cdecl = self.file_const_decl(name)?;
                let ty = cdecl.ty.as_ref()?;
                let resolved = self.resolve_type_alias(ty);
                let TypeExpr::Named { name: ty_name, .. } = &resolved else {
                    return None;
                };
                if fixed_width_int_range(ty_name).is_none() {
                    return None;
                }
                match const_int_fold_with(&cdecl.value, &self.const_values, depth + 1, None) {
                    ConstFold::Val(v) => Some(TypedConst {
                        val: v,
                        ty: ty_name.clone(),
                    }),
                    _ => None,
                }
            }
            Expr::Call { callee, args, .. } => {
                if args.len() != 1 || args[0].spread {
                    return None;
                }
                let Expr::Ident { name, .. } = unwrap_parens(callee) else {
                    return None;
                };
                // Hybrid-spec conversion spellings only (LX3): Go's spelled
                // variants (`uint8`, `int64`, …) are ordinary identifiers
                // (#728) and stay out of this pass.
                if !is_spec_int_conv(name) {
                    return None;
                }
                if let Some(st) = st {
                    if st.env_lookup(name).is_some() {
                        return None;
                    }
                }
                if self.const_values.contains_key(name.as_str()) {
                    return None;
                }
                match const_int_fold_with(&args[0].value, &self.const_values, depth + 1, st) {
                    ConstFold::Val(v) => {
                        let (lo, hi) = fixed_width_int_range(name)?;
                        // SPEC X4 wrap, verbatim from hy-emit/constconv.rs:
                        // two's-complement truncation into the target width.
                        let len = hi - lo + 1;
                        let masked = v & (len - 1);
                        let folded = if lo < 0 && masked > hi {
                            masked - len
                        } else {
                            masked
                        };
                        Some(TypedConst {
                            val: folded,
                            ty: name.clone(),
                        })
                    }
                    _ => None,
                }
            }            Expr::Unary { op: UnOp::Neg, operand, .. } => {
                let t = self.typed_const_of(operand, depth + 1, st)?;
                let (lo, hi) = fixed_width_int_range(&t.ty)?;
                match t.val.checked_neg() {
                    Some(v) if v >= lo && v <= hi => Some(TypedConst {
                        val: v,
                        ty: t.ty,
                    }),
                    _ => None,
                }
            }
            Expr::Binary { op, lhs, rhs, .. } => {
                let lt = self.typed_const_of(lhs, depth + 1, st);
                let rt = self.typed_const_of(rhs, depth + 1, st);
                let is_shift = matches!(op, BinOp::Shl | BinOp::Shr);
                let t = if is_shift { lt? } else { lt.or(rt)? };
                let (lo, hi) = fixed_width_int_range(&t.ty)?;
                let l = self.typed_const_value_of(lhs, st);
                let r = self.typed_const_value_of(rhs, st);
                match fold_bin(*op, l, r) {
                    ConstFold::Val(v) if v >= lo && v <= hi => Some(TypedConst {
                        val: v,
                        ty: t.ty,
                    }),
                    _ => None,
                }
            }
            _ => None,
        }
    }


    /// #823: fold a constant conversion operand. Resolves file-level `const`
    /// identifiers recursively and folds constant arithmetic (`1.5 + 1.0`,
    /// `1 << 63`) and comparisons (`1 < 2`) so `u8(N)`, `int(f)`, `[]int(s)`,
    /// and `int(1 < 2)` are checked exactly as Go folds them. Local shadowing
    /// is not visible here (Pass B), so an ident resolves through the
    /// file-level `const` table — the fail-open rule `typed_const_of`
    /// applies when the scope is unknown.
    fn conv_const(&self, e: &Expr, depth: usize) -> Option<ConvConst> {
        if depth > 32 {
            return None;
        }
        match unwrap_parens(e) {
            Expr::Lit { kind, .. } => Some(match kind {
                LitKind::Int(s) => match parse_int_lit(s) {
                    Some(ConstInt::Value(v)) => ConvConst::Int(v),
                    Some(ConstInt::PosOverflow) | Some(ConstInt::NegOverflow) | None => {
                        ConvConst::Huge {
                            f: huge_int_as_f64(s),
                            lt_512: lit_below_2_512(s),
                        }
                    }
                },
                LitKind::Float(s) => ConvConst::Float(s.parse::<f64>().unwrap_or(f64::INFINITY)),
                LitKind::Char(c) => ConvConst::Char(*c as i32),
                LitKind::Str(_) | LitKind::RawStr(_) => ConvConst::Str,
                LitKind::Bool(_) => ConvConst::Bool,
                LitKind::Nil => ConvConst::Nil,
            }),
            Expr::Ident { name, .. } => {
                let cdecl = self.file_const_decl(name)?;
                self.conv_const(&cdecl.value, depth + 1)
            }
            Expr::Unary { op, operand, .. } => {
                let c = self.conv_const(operand, depth + 1)?;
                match op {
                    UnOp::Neg => match c {
                        ConvConst::Int(v) => Some(match v.checked_neg() {
                            Some(n) => ConvConst::Int(n),
                            None => ConvConst::Huge {
                                f: -(v as f64),
                                lt_512: true,
                            },
                        }),
                        ConvConst::Float(f) => Some(ConvConst::Float(-f)),
                        ConvConst::Huge { f, lt_512 } => Some(ConvConst::Huge { f: -f, lt_512 }),
                        other => Some(other),
                    },
                    _ => None,
                }
            }
            Expr::Binary { op, lhs, rhs, .. } => {
                let l = self.conv_const(lhs, depth + 1)?;
                let r = self.conv_const(rhs, depth + 1)?;
                self.fold_conv_bin(op, l, r)
            }
            _ => None,
        }
    }

    /// Constant folding of one binary operator on two already-folded
    /// operands. Kinds stay honest: string addition is `Str`, comparisons
    /// and logic are `Bool`, and numeric arithmetic folds Int/Float/Huge
    /// exactly (arbitrary-precision ints, Go-style untyped promotion).
    fn fold_conv_bin(&self, op: &BinOp, l: ConvConst, r: ConvConst) -> Option<ConvConst> {
        match op {
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                return Some(ConvConst::Bool);
            }
            BinOp::And | BinOp::Or => {
                return match (l, r) {
                    (ConvConst::Bool, ConvConst::Bool) => Some(ConvConst::Bool),
                    _ => None,
                };
            }
            _ => {}
        }
        let (li, ri) = match (&l, &r) {
            (ConvConst::Int(a), ConvConst::Int(b)) => (*a, *b),
            (ConvConst::Char(a), ConvConst::Int(b)) => (*a as i128, *b),
            (ConvConst::Int(a), ConvConst::Char(b)) => (*a, *b as i128),
            (ConvConst::Char(a), ConvConst::Char(b)) => (*a as i128, *b as i128),
            _ => {
                return match (op, l, r) {
                    (BinOp::Add, ConvConst::Str, ConvConst::Str) => Some(ConvConst::Str),
                    (BinOp::Add, ConvConst::Float(a), ConvConst::Float(b)) => {
                        Some(ConvConst::Float(a + b))
                    }
                    (BinOp::Sub, ConvConst::Float(a), ConvConst::Float(b)) => {
                        Some(ConvConst::Float(a - b))
                    }
                    (BinOp::Mul, ConvConst::Float(a), ConvConst::Float(b)) => {
                        Some(ConvConst::Float(a * b))
                    }
                    _ => None,
                };
            }
        };
        Some(match op {
            BinOp::Add => ConvConst::Int(li.checked_add(ri)?),
            BinOp::Sub => ConvConst::Int(li.checked_sub(ri)?),
            BinOp::Mul => ConvConst::Int(li.checked_mul(ri)?),
            BinOp::Div => {
                if ri == 0 {
                    return None;
                }
                ConvConst::Int(li.checked_div(ri)?)
            }
            BinOp::Mod => {
                if ri == 0 {
                    return None;
                }
                ConvConst::Int(li.checked_rem(ri)?)
            }
            BinOp::BitAnd => ConvConst::Int(li & ri),
            BinOp::BitOr => ConvConst::Int(li | ri),
            BinOp::BitXor => ConvConst::Int(li ^ ri),
            BinOp::Shl => {
                let r = u32::try_from(ri).ok()?;
                if r >= 128 {
                    return None;
                }
                ConvConst::Int(li.checked_shl(r)?)
            }
            BinOp::Shr => {
                let r = u32::try_from(ri).ok()?;
                if r >= 128 {
                    return None;
                }
                ConvConst::Int(li.checked_shr(r)?)
            }
            _ => return None, // unknown operator: not a constant fold here
        })
    }
}


/// A constant integer expression with a KNOWN fixed-width integer type
/// (issue #725): the folded value plus the type name that must represent
/// it. Produced for typed `const` idents, spec conversions of constants,
/// negations, and fitting arithmetic combinations of those.
#[derive(Debug, Clone)]
struct TypedConst {
    val: i128,
    ty: String,
}

/// The Hybrid-spec conversion spellings (LX3 predeclared) whose constant
/// arithmetic this pass models: fixed-width integer types only. Go's
/// spelled variants (`uint8`, `int64`, `float32`, …) are ordinary Hybrid
/// identifiers (LX3 / issue #728) and stay out of scope.
fn is_spec_int_conv(name: &str) -> bool {
    matches!(
        name,
        "u8" | "u16" | "u32" | "u64" | "i8" | "i16" | "i32" | "i64" | "int" | "uint" | "byte" | "rune"
    )
}

/// A literal-constant conversion operand (the literal-only scope shared with
/// E6001/E6002). Anything else — idents, binary ops, calls — is out of
/// scope: it is either run-time (SPEC X4) or another pass's business. Anything else — idents, binary ops, calls — is out of
/// scope: it is either run-time (SPEC X4) or another pass's business.
enum ConvConst {
    Int(i128),
    /// Integer literal past i128 (or past u128) — carries its `f64` reading
    /// so float targets can still decide (`f64(10^40)` is fine, `f32(10^40)`
    /// overflows f32), plus whether the value is strictly below 2^512
    /// (Go's verified boundary: `string(2^512 - 1)` builds,
    /// `string(2^512)` is `constant overflow`).
    Huge { f: f64, lt_512: bool },
    Float(f64),
    Char(i32),
    Str,
    Bool,
    Nil,
}

impl ConvConst {
    fn kind_name(&self) -> &'static str {
        match self {
            ConvConst::Int(_) | ConvConst::Huge { .. } => "integer",
            ConvConst::Float(_) => "float",
            ConvConst::Char(_) => "rune",
            ConvConst::Str => "string",
            ConvConst::Bool => "boolean",
            ConvConst::Nil => "nil",
        }
    }
}

/// Strictly-below-2^512, decided EXACTLY on the literal's digit string (an
/// `f64` reading would round `2^512 - 1` up to `2^512` and wrongly reject
/// what Go builds). Verified against go1.25: `string(2^512 - 1)` builds,
/// `string(2^512)` is `constant overflow`; the boundary does not appear on
/// any other target (i128 tops out at ~1.7e38, f64 at ~1.8e308).
const TWO_POW_512: &str = "13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096";

fn lit_below_2_512(s: &str) -> bool {
    let t = s.replace('_', "");
    let t = t.trim_start_matches('0');
    let t = if t.is_empty() { "0" } else { t };
    let t = t.strip_prefix('-').unwrap_or(t);
    match t.len().cmp(&TWO_POW_512.len()) {
        std::cmp::Ordering::Less => true,
        std::cmp::Ordering::Greater => false,
        std::cmp::Ordering::Equal => t < TWO_POW_512,
    }
}

/// Best `f64` reading of an integer literal that overflowed `i128` — used so
/// float targets can still decide (`f64(10^40)` is fine, `f32(10^40)`
/// overflows f32). Radix forms are read as `u128` first (they top out at
/// 3.4e38, inside f64); decimals read directly (anything past 1e308
/// legitimately becomes `inf`, which is exactly the Go-side rejection).
fn huge_int_as_f64(s: &str) -> f64 {
    let t = s.replace('_', "");
    if let Ok(v) = t.parse::<f64>() {
        return v;
    }
    for (pref, radix) in [("0x", 16u32), ("0X", 16), ("0b", 2), ("0B", 2), ("0o", 8), ("0O", 8)] {
        if let Some(rest) = t.strip_prefix(pref) {
            if let Ok(v) = u128::from_str_radix(rest, radix) {
                return v as f64;
            }
        }
    }
    f64::INFINITY
}

/// True when `name` is a built-in conversion target of `Type(const)` calls.
fn is_conversion_target(name: &str) -> bool {
    fixed_width_int_range(name).is_some()
        || matches!(
            name,
            "f32" | "f64" | "float32" | "float64" | "string" | "bool"
        )
}

/// Targets the emitter's SPEC X4 fold skips (`bits >= 64`) — constants here
/// must reject instead of pass through.
fn is_64bit_int_target(name: &str) -> bool {
    matches!(
        name,
        "i64" | "int64" | "int" | "isize" | "u64" | "uint64" | "uint" | "usize" | "uintptr"
    )
}

/// `uint8(-1)` / `i8(-300)` — a unary minus over an integer literal is
/// folded exactly like the bare literal (the emitter's SPEC X4 rewrite
/// truncates both), so it stays accepted (upstream
/// tests/const_conversion.rs sub64 accept set). Anything else — const
/// identifiers, constant arithmetic, floats — is NOT rewritten by the
/// fold and must still reject (#823).
fn is_simple_unary_negation(arg: &Expr) -> bool {
    matches!(
        unwrap_parens(arg),
        Expr::Unary {
            op: hy_syntax::UnOp::Neg,
            operand,
            ..
        } if matches!(
            unwrap_parens(operand),
            Expr::Lit {
                kind: hy_syntax::LitKind::Int(_),
                ..
            }
        )
    )
}

fn is_f32_target(name: &str) -> bool {
    matches!(name, "f32" | "float32")
}

/// The built-in float TYPES as spelled in an ascription: `Some(true)` =
/// float32, `Some(false)` = float64. `f32`/`f64` are accepted alias
/// spellings (the emitter maps both to float32/float64 — issue #683's
/// float legs must reject past-range constants under either spelling).
/// Carried from rickymulya's parallel take #689 (credit).
fn is_float_type(ty_name: &str) -> Option<bool> {
    match ty_name {
        "float32" | "f32" => Some(true),
        "float64" | "f64" => Some(false),
        _ => None,
    }
}

fn span_hint(span: Span) -> String {
    format!("{}:{}", span.start.line, span.start.col)
}

/// Target word size for platform-dependent integer types. Hybrid's current
/// emitter/runtime targets are 64-bit; keep the policy centralized so a
/// future target configuration can replace this constant.
pub(crate) const TARGET_INT_WIDTH_BITS: u32 = 64;

#[inline]
pub(crate) fn target_int_range() -> (i128, i128) {
    match TARGET_INT_WIDTH_BITS {
        32 => (i32::MIN as i128, i32::MAX as i128),
        64 => (i64::MIN as i128, i64::MAX as i128),
        _ => (i64::MIN as i128, i64::MAX as i128),
    }
}

#[inline]
pub(crate) fn target_uint_range() -> (i128, i128) {
    match TARGET_INT_WIDTH_BITS {
        32 => (0, u32::MAX as i128),
        64 => (0, u64::MAX as i128),
        _ => (0, u64::MAX as i128),
    }
}

/// Inclusive representable range for a Hybrid fixed-width integer type
/// name (SPEC-LANGUAGE §11 / Go's typed-constant assignment rule).
/// Platform-word `int`/`uint`/`isize`/`usize` use the 64-bit LP64 ranges
/// the emitter targets (SPEC B9 / X7).
pub(crate) fn fixed_width_int_range(name: &str) -> Option<(i128, i128)> {
    Some(match name {
        "i8" | "int8" => (i8::MIN as i128, i8::MAX as i128),
        "u8" | "uint8" | "byte" => (0, u8::MAX as i128),
        "i16" | "int16" => (i16::MIN as i128, i16::MAX as i128),
        "u16" | "uint16" => (0, u16::MAX as i128),
        "i32" | "int32" | "rune" => (i32::MIN as i128, i32::MAX as i128),
        "u32" | "uint32" => (0, u32::MAX as i128),
        "i64" | "int64" => (i64::MIN as i128, i64::MAX as i128),
        "int" | "isize" => target_int_range(),
        "u64" | "uint64" => (0, u64::MAX as i128),
        "uint" | "usize" | "uintptr" => target_uint_range(),
        _ => return None,
    })
}

/// Parsed integer literal, retaining the fact that a syntactically valid
/// value exceeded i128 instead of treating it as non-constant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ConstInt {
    Value(i128),
    PosOverflow,
    NegOverflow,
}

/// Outcome of folding a constant integer expression (issue #201-B).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ConstFold {
    /// Folded to an exact i128 value.
    Val(i128),
    /// Not a constant the checker can prove (idents, calls, …) — callers
    /// stay silent (fail-open; other diagnostics own those shapes).
    NotConst,
    /// Provably a constant whose magnitude exceeds every fixed-width
    /// Hybrid integer range (e.g. `1 << 200`, `i128` arithmetic overflow).
    TooBig,
}

/// Fold a pure integer constant expression: int literals (any base the
/// lexer keeps), unary `-`, parentheses, and the arithmetic/shift/bitwise
/// operators over constant operands (issue #201-B: Go folds `100 + 100`
/// and `1 << 10` before the range check, so they overflow identically).
/// Anything else (idents, calls) is `NotConst`.
pub(crate) fn const_int_fold(e: &Expr) -> ConstFold {
    const_int_fold_with(e, &HashMap::new(), 0, None)
}

/// Like [`const_int_fold`], but resolves file-level `const` identifiers to
/// their (constant) initializers: `const big = 300; var n int8 = big` must
/// be rejected like the literal. A local binding with the same name shadows
/// the file-level const, so `st` is consulted before resolving.
pub(crate) fn const_int_fold_with(
    e: &Expr,
    consts: &HashMap<String, &Expr>,
    depth: u32,
    st: Option<&FnState>,
) -> ConstFold {
    match unwrap_parens(e) {
        Expr::Lit {
            kind: LitKind::Int(s),
            ..
        } => match parse_int_lit(s) {
            Some(ConstInt::Value(v)) => ConstFold::Val(v),
            Some(ConstInt::PosOverflow | ConstInt::NegOverflow) => ConstFold::TooBig,
            None => ConstFold::NotConst,
        },
        Expr::Lit {
            kind: LitKind::Char(c),
            ..
        } => ConstFold::Val(*c as i128),
        Expr::Ident { name, .. } => {
            if let Some(st) = st {
                if st.env_lookup(name).is_some() {
                    return ConstFold::NotConst;
                }
            }
            if depth < 16 {
                if let Some(v) = consts.get(name) {
                    // The function state guards the identifier at the *use
                    // site* only: a const's own initializer refers to the
                    // file-level scope, so expand it without `st`.
                    return const_int_fold_with(v, consts, depth + 1, None);
                }
            }
            ConstFold::NotConst
        }
        Expr::Unary {
            op: UnOp::Neg,
            operand,
            ..
        } => match const_int_fold_with(operand, consts, depth + 1, st) {
            ConstFold::Val(v) => v.checked_neg().map(ConstFold::Val).unwrap_or(ConstFold::TooBig),
            ConstFold::NotConst => ConstFold::NotConst,
            ConstFold::TooBig => ConstFold::TooBig,
        },
        Expr::Binary { op, lhs, rhs, .. } => {
            let l = const_int_fold_with(lhs, consts, depth + 1, st);
            let r = const_int_fold_with(rhs, consts, depth + 1, st);
            fold_bin(*op, l, r)
        }
        _ => ConstFold::NotConst,
    }
}

fn fold_bin(op: BinOp, l: ConstFold, r: ConstFold) -> ConstFold {
    use BinOp::*;
    // Division/shift-by-huge and `TooBig` interactions are handled per-op.
    match op {
        Add | Sub | Mul => {
            if matches!(l, ConstFold::NotConst) || matches!(r, ConstFold::NotConst) {
                return ConstFold::NotConst;
            }
            if matches!(l, ConstFold::TooBig) || matches!(r, ConstFold::TooBig) {
                return ConstFold::TooBig;
            }
            let (ConstFold::Val(a), ConstFold::Val(b)) = (l, r) else {
                return ConstFold::NotConst;
            };
            let v = match op {
                Add => a.checked_add(b),
                Sub => a.checked_sub(b),
                _ => a.checked_mul(b),
            };
            v.map(ConstFold::Val).unwrap_or(ConstFold::TooBig)
        }
        // Bitwise masking can shrink a `TooBig` value back into range —
        // give up (fail-open) rather than guess.
        BitAnd | BitOr | BitXor => {
            if matches!(l, ConstFold::TooBig) || matches!(r, ConstFold::TooBig) {
                return ConstFold::NotConst;
            }
            let (ConstFold::Val(a), ConstFold::Val(b)) = (l, r) else {
                return ConstFold::NotConst;
            };
            let v = match op {
                BitAnd => a & b,
                BitOr => a | b,
                _ => a ^ b,
            };
            ConstFold::Val(v)
        }
        Shl => {
            let (ConstFold::Val(a), ConstFold::Val(n)) = (l, r) else {
                // A provably-huge left operand stays huge when shifted by
                // a non-negative constant; anything else fails open.
                if matches!(l, ConstFold::TooBig)
                    && matches!(r, ConstFold::Val(n) if n >= 0)
                {
                    return ConstFold::TooBig;
                }
                return ConstFold::NotConst;
            };
            if n < 0 {
                // Negative counts are HYB-E6005's job at the shift site.
                return ConstFold::NotConst;
            }
            if a == 0 {
                return ConstFold::Val(0);
            }
            if n >= 128 {
                return ConstFold::TooBig;
            }
            let n = n as u32;
            let base = 1u128 << n;
            let Some(mag) = (a.unsigned_abs() as u128).checked_mul(base) else {
                return ConstFold::TooBig;
            };
            if mag > i128::MAX as u128 {
                return ConstFold::TooBig;
            }
            let mag = mag as i128;
            ConstFold::Val(if a < 0 { -mag } else { mag })
        }
        Shr => {
            let (ConstFold::Val(a), ConstFold::Val(n)) = (l, r) else {
                return ConstFold::NotConst;
            };
            if n < 0 {
                return ConstFold::NotConst;
            }
            if n >= 128 {
                // Arithmetic shift: non-negative → 0, negative → -1.
                return ConstFold::Val(if a < 0 { -1 } else { 0 });
            }
            ConstFold::Val(a >> (n as u32))
        }
        Div | Mod => {
            // `TooBig` operands give up: division shrinks and could land
            // back in range — never guess (fail-open, no false reject).
            if !matches!(l, ConstFold::Val(_)) || !matches!(r, ConstFold::Val(_)) {
                return ConstFold::NotConst;
            }
            let (ConstFold::Val(a), ConstFold::Val(b)) = (l, r) else {
                return ConstFold::NotConst;
            };
            if b == 0 {
                return ConstFold::NotConst; // HYB-E6001 owns `/ 0`
            }
            match op {
                Div => a.checked_div(b).map(ConstFold::Val).unwrap_or(ConstFold::TooBig),
                _ => a.checked_rem(b).map(ConstFold::Val).unwrap_or(ConstFold::NotConst),
            }
        }
        _ => ConstFold::NotConst,
    }
}

/// Convenience: fold to a value when the expression IS a constant in
/// range (used by the negative-shift check in emit_guard.rs).
pub(crate) fn const_int_value(e: &Expr) -> Option<i128> {
    match const_int_fold(e) {
        ConstFold::Val(v) => Some(v),
        _ => None,
    }
}

/// Fold a float constant expression (literals, unary `-`, parens) — the
/// `var x int = 2.5` truncation site (issue #201-B).
pub(crate) fn const_float_value(e: &Expr) -> Option<f64> {
    match unwrap_parens(e) {
        Expr::Lit {
            kind: LitKind::Float(s),
            ..
        } => s.replace('_', "").parse::<f64>().ok(),
        Expr::Unary {
            op: UnOp::Neg,
            operand,
            ..
        } => const_float_value(operand).map(|v| -v),
        _ => None,
    }
}

/// Fold a float constant expression, resolving identifiers via `consts`.
pub(crate) fn const_float_fold_with(
    e: &Expr,
    consts: &HashMap<String, &Expr>,
    depth: u32,
    st: Option<&FnState>,
) -> Option<f64> {
    match unwrap_parens(e) {
        Expr::Lit {
            kind: LitKind::Float(s),
            ..
        } => {
            let clean: String = s.chars().filter(|c| *c != '_').collect();
            clean.parse::<f64>().ok()
        }
        Expr::Lit {
            kind: LitKind::Int(s),
            ..
        } => {
            let clean: String = s.chars().filter(|c| *c != '_').collect();
            if let Some(ConstInt::Value(v)) = parse_int_lit(s) {
                Some(v as f64)
            } else if let Ok(f) = clean.parse::<f64>() {
                Some(f)
            } else {
                None
            }
        }
        Expr::Lit {
            kind: LitKind::Char(c),
            ..
        } => Some(*c as u32 as f64),
        Expr::Ident { name, .. } => {
            if let Some(st) = st {
                if st.env_lookup(name).is_some() {
                    return None;
                }
            }
            if depth < 16 {
                if let Some(v) = consts.get(name) {
                    return const_float_fold_with(v, consts, depth + 1, None);
                }
            }
            None
        }
        Expr::Unary {
            op: UnOp::Neg,
            operand,
            ..
        } => const_float_fold_with(operand, consts, depth + 1, st).map(|v| -v),
        Expr::Binary { op, lhs, rhs, .. } => {
            let l = const_float_fold_with(lhs, consts, depth + 1, st)?;
            let r = const_float_fold_with(rhs, consts, depth + 1, st)?;
            match op {
                BinOp::Add => Some(l + r),
                BinOp::Sub => Some(l - r),
                BinOp::Mul => Some(l * r),
                BinOp::Div => {
                    if r == 0.0 {
                        None
                    } else {
                        Some(l / r)
                    }
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Returns true if `e` is an untyped float constant expression (contains at least one float literal or float const).
fn is_float_const_expr(
    e: &Expr,
    consts: &HashMap<String, &Expr>,
    depth: u32,
    st: Option<&FnState>,
) -> bool {
    match unwrap_parens(e) {
        Expr::Lit {
            kind: LitKind::Float(_),
            ..
        } => true,
        Expr::Lit { .. } => false,
        Expr::Ident { name, .. } => {
            if let Some(st) = st {
                if st.env_lookup(name).is_some() {
                    return false;
                }
            }
            if depth < 16 {
                if let Some(v) = consts.get(name) {
                    return is_float_const_expr(v, consts, depth + 1, None);
                }
            }
            false
        }
        Expr::Unary { operand, .. } => is_float_const_expr(operand, consts, depth + 1, st),
        Expr::Binary { lhs, rhs, .. } => {
            is_float_const_expr(lhs, consts, depth + 1, st)
                || is_float_const_expr(rhs, consts, depth + 1, st)
        }
        _ => false,
    }
}

/// Render a folded float as the nearest integer literal for the fix-it.
fn integer_of_float(f: f64) -> String {
    format!("{}", f.trunc() as i128)
}

pub(crate) fn parse_int_lit(s: &str) -> Option<ConstInt> {
    let clean: String = s.chars().filter(|c| *c != '_').collect();
    if clean.is_empty() {
        return None;
    }
    let s = clean.as_str();
    let (radix, digits) = if let Some(rest) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        (16, rest)
    } else if let Some(rest) = s.strip_prefix("0b").or_else(|| s.strip_prefix("0B")) {
        (2, rest)
    } else if let Some(rest) = s.strip_prefix("0o").or_else(|| s.strip_prefix("0O")) {
        (8, rest)
    } else if s.len() > 1 && s.starts_with('0') {
        if s.chars().any(|c| c == '8' || c == '9') {
            return None;
        }
        (8, s)
    } else {
        (10, s)
    };
    if digits.is_empty() {
        return None;
    }
    match i128::from_str_radix(digits, radix) {
        Ok(v) => Some(ConstInt::Value(v)),
        Err(err) => match err.kind() {
            std::num::IntErrorKind::PosOverflow => Some(ConstInt::PosOverflow),
            std::num::IntErrorKind::NegOverflow => Some(ConstInt::NegOverflow),
            _ => None,
        },
    }
}

#[cfg(test)]
mod unit {
    use super::*;

    #[test]
    fn ranges_match_go_fixed_width() {
        assert_eq!(fixed_width_int_range("int8"), Some((-128, 127)));
        assert_eq!(fixed_width_int_range("byte"), Some((0, 255)));
        assert_eq!(fixed_width_int_range("u16"), Some((0, 65535)));
        assert!(fixed_width_int_range("string").is_none());
        assert!(fixed_width_int_range("float64").is_none());
    }

    #[test]
    fn parse_bases() {
        assert_eq!(parse_int_lit("300"), Some(ConstInt::Value(300)));
        assert_eq!(parse_int_lit("0x12C"), Some(ConstInt::Value(300)));
        assert_eq!(parse_int_lit("0b101"), Some(ConstInt::Value(5)));
        assert_eq!(parse_int_lit("0o10"), Some(ConstInt::Value(8)));
        assert_eq!(parse_int_lit("1_000"), Some(ConstInt::Value(1000)));
    }

    #[test]
    fn parse_overflow_and_target_ranges() {
        assert_eq!(
            parse_int_lit("340282366920938463463374607431768211457"),
            Some(ConstInt::PosOverflow)
        );
        assert_eq!(target_int_range(), (i64::MIN as i128, i64::MAX as i128));
        assert_eq!(target_uint_range(), (0, u64::MAX as i128));
    }
}

#[cfg(test)]
mod typed_arith_tests {
    use crate::{check_file, Verdict};

    fn check(src: &str) -> crate::CheckResult {
        let ast = hy_syntax::parse_file("test.hy", src).expect("test source must parse");
        check_file(&ast)
    }

    /// Issue #725 lead: `top + 1` folds to 256 in the OPERAND's type `u8` —
    /// Go rejects `constant 256 of type uint8 overflows uint8`.
    #[test]
    fn typed_const_ident_arith_overflow_rejected() {
        let r = check(
            "import \"fmt\"\n\
             const top u8 = 255\n\
             fn main() {\n\
               a := top + 1\n\
               fmt.println(\"{a}\")\n\
             }",
        );
        assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
        assert!(
            r.diagnostics.iter().any(|d| d.code == "HYB-E6002"),
            "expected HYB-E6002, got {:?}",
            r.diagnostics
        );
    }

    /// `i64(1) << 63` — the conversion operand was invisible to the shared
    /// fold (NotConst); the typed reading folds 1<<63 and rejects in i64.
    #[test]
    fn typed_conv_shift_overflow_rejected() {
        let r = check(
            "import \"fmt\"\n\
             fn main() {\n\
               b := i64(1) << 63\n\
               fmt.println(\"{b}\")\n\
             }",
        );
        assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
        assert!(
            r.diagnostics.iter().any(|d| d.code == "HYB-E6002"),
            "expected HYB-E6002, got {:?}",
            r.diagnostics
        );
    }

    /// Both operands typed (`u8(250) + u8(10)`): the folded result 260
    /// overflows u8 in Go.
    #[test]
    fn typed_conv_arith_overflow_rejected() {
        let r = check(
            "import \"fmt\"\n\
             fn main() {\n\
               c := u8(250) + u8(10)\n\
               fmt.println(\"{c}\")\n\
             }",
        );
        assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
        assert!(
            r.diagnostics.iter().any(|d| d.code == "HYB-E6002"),
            "expected HYB-E6002, got {:?}",
            r.diagnostics
        );
    }

    /// `u8(0) - 1` → -1 is unrepresentable in u8.
    #[test]
    fn typed_conv_sub_underflow_rejected() {
        let r = check(
            "import \"fmt\"\n\
             fn main() {\n\
               d := u8(0) - 1\n\
               fmt.println(\"{d}\")\n\
             }",
        );
        assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
        assert!(
            r.diagnostics.iter().any(|d| d.code == "HYB-E6002"),
            "expected HYB-E6002, got {:?}",
            r.diagnostics
        );
    }

    /// `-u8(1)` — unary negation of a typed constant overflows u8.
    #[test]
    fn unary_neg_typed_const_rejected() {
        let r = check(
            "import \"fmt\"\n\
             fn main() {\n\
               e := -u8(1)\n\
               fmt.println(\"{e}\")\n\
             }",
        );
        assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
        assert!(
            r.diagnostics.iter().any(|d| d.code == "HYB-E6002"),
            "expected HYB-E6002, got {:?}",
            r.diagnostics
        );
    }
    /// `i8(-128) / -1` → 128 overflows i8 (Go: `constant 128 of type int8 overflows int8`).
    #[test]
    fn typed_conv_div_overflow_rejected() {
        let r = check(
            "import \"fmt\"\n\
             fn main() {\n\
               f := i8(-128) / -1\n\
               fmt.println(\"{f}\")\n\
             }",
        );
        assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
        assert!(
            r.diagnostics.iter().any(|d| d.code == "HYB-E6002"),
            "expected HYB-E6002, got {:?}",
            r.diagnostics
        );
    }

    /// `int(u8(255) + 1)` — the nested inner expression overflows first and
    /// is reported at its own span.
    #[test]
    fn nested_conversion_arg_rejected() {
        let r = check(
            "import \"fmt\"\n\
             fn main() {\n\
               g := int(u8(255) + 1)\n\
               fmt.println(\"{g}\")\n\
             }",
        );
        assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
        assert!(
            r.diagnostics.iter().any(|d| d.code == "HYB-E6002"),
            "expected HYB-E6002, got {:?}",
            r.diagnostics
        );
    }

    /// File-level `const` with a typed constant initializer that overflows
    /// (the file-level init site carries no FnState — must still reject).
    #[test]
    fn file_const_typed_init_overflow_rejected() {
        let r = check("const bad i8 = i8(127) + 1\n");
        assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
        assert!(
            r.diagnostics.iter().any(|d| d.code == "HYB-E6002"),
            "expected HYB-E6002, got {:?}",
            r.diagnostics
        );
    }

    /// Typed `var` initializer: `var b u8 = u8(255) + 1` (the init site
    /// with an explicit type).
    #[test]
    fn typed_var_init_overflow_rejected() {
        let r = check(
            "import \"fmt\"\n\
             fn main() {\n\
               var b u8 = u8(255) + 1\n\
               fmt.println(\"{b}\")\n\
             }",
        );
        assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
        assert!(
            r.diagnostics.iter().any(|d| d.code == "HYB-E6002"),
            "expected HYB-E6002, got {:?}",
            r.diagnostics
        );
    }

    /// Control: in-range typed arithmetic stays accepted.
    #[test]
    fn in_range_typed_arith_accepted() {
        let r = check(
            "import \"fmt\"\n\
             const top u8 = 255\n\
             fn main() {\n\
               ok := u8(250) + u8(5)\n\
               fine := top - 255\n\
               fmt.println(\"{ok} {fine}\")\n\
             }",
        );
        assert_eq!(r.verdict, Verdict::Accept, "{:?}", r.diagnostics);
    }

    /// Control: the SPEC X4 conversion wrap (`u8(300)` → 44) is the
    /// emitter's defined behavior and must stay accepted.
    #[test]
    fn conversion_wrap_still_accepted() {
        let r = check(
            "import \"fmt\"\n\
             fn main() {\n\
               w := u8(300)\n\
               fmt.println(\"{w}\")\n\
             }",
        );
        assert_eq!(r.verdict, Verdict::Accept, "{:?}", r.diagnostics);
    }

    /// Control: runtime operands are out of scope (X4 run-time conversion).
    #[test]
    fn runtime_operand_still_accepted() {
        let r = check(
            "import \"fmt\"\n\
             fn main() {\n\
               w := 300\n\
               v := u8(w)\n\
               fmt.println(\"{v}\")\n\
             }",
        );
        assert_eq!(r.verdict, Verdict::Accept, "{:?}", r.diagnostics);
    }

    /// Control: a local binding shadowing a typed const disables the typed
    /// reading (same rule as the shared fold) — no false reject.
    #[test]
    fn local_shadow_not_misread_as_typed_const() {
        let r = check(
            "import \"fmt\"\n\
             const top u8 = 255\n\
             fn main() {\n\
               top := 5\n\
               x := top + 1\n\
               fmt.println(\"{x}\")\n\
             }",
        );
        assert_eq!(r.verdict, Verdict::Accept, "{:?}", r.diagnostics);
    }

    /// Regression guard: the untyped-constant overflow path (issue #228)
    /// must keep rejecting — `x := 1 << 63` overflows the default `int`.
    #[test]
    fn untyped_default_int_overflow_still_rejected() {
        let r = check(
            "import \"fmt\"\n\
             fn main() {\n\
               x := 1 << 63\n\
               fmt.println(\"{x}\")\n\
             }",
        );
        assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
        assert!(
            r.diagnostics.iter().any(|d| d.code == "HYB-E6002"),
            "expected HYB-E6002, got {:?}",
            r.diagnostics
        );
    }
}