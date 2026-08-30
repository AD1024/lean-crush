import Lean
import Crush.Metatheory.HO.Core

/-!
# Surface syntax for the metatheory core

`(ho| ...)` elaborates a small higher-order formula directly to an intrinsically typed
`Crush.Metatheory.Term`. Bound identifiers are resolved to typed de Bruijn references.
Two antiquotation forms connect object syntax to Lean declarations:

* `#c` embeds a `Const signature ty` reference as an uninterpreted constant;
* `~t` embeds an already constructed `Term signature context ty`.

Opaque type names are written as identifiers and are identified by their spelling.
`~ty` embeds an existing `Ty` expression when a separately declared type value is
preferred.
-/

open Lean Elab

namespace Crush.Metatheory

declare_syntax_cat metatheoryTy
declare_syntax_cat metatheoryTerm

syntax:max ident : metatheoryTy
syntax:max "~" term:max : metatheoryTy
syntax:arg "(" metatheoryTy ")" : metatheoryTy
syntax:25 metatheoryTy:26 " → " metatheoryTy:25 : metatheoryTy

syntax:arg "(" metatheoryTerm ")" : metatheoryTerm
syntax:max "~" term:max : metatheoryTerm
syntax:max "#" term:max : metatheoryTerm
syntax:max ident : metatheoryTerm
syntax:max "⊤" : metatheoryTerm
syntax:max "⊥" : metatheoryTerm
syntax:70 metatheoryTerm:70 metatheoryTerm:71 : metatheoryTerm
syntax:65 "¬" metatheoryTerm:65 : metatheoryTerm
syntax:50 metatheoryTerm:51 " = " metatheoryTerm:51 : metatheoryTerm
syntax:50 metatheoryTerm:51 " ≠ " metatheoryTerm:51 : metatheoryTerm
syntax:40 metatheoryTerm:41 " ∧ " metatheoryTerm:40 : metatheoryTerm
syntax:35 metatheoryTerm:36 " ∨ " metatheoryTerm:35 : metatheoryTerm
syntax:30 metatheoryTerm:31 " → " metatheoryTerm:10 : metatheoryTerm
syntax:25 metatheoryTerm:26 " ↔ " metatheoryTerm:10 : metatheoryTerm
syntax:10 "λ" ident ":" metatheoryTy "." metatheoryTerm:10 : metatheoryTerm
syntax:10 "∀" ident ":" metatheoryTy "," metatheoryTerm:10 : metatheoryTerm
syntax:10 "∃" ident ":" metatheoryTy "," metatheoryTerm:10 : metatheoryTerm

/-- Convert object-language type syntax to a Lean term denoting `Ty`. -/
private partial def expandTy : Syntax → MacroM (TSyntax `term)
  | `(metatheoryTy| ($ty:metatheoryTy)) => expandTy ty
  | `(metatheoryTy| ~$ty:term) => pure ty
  | `(metatheoryTy| $name:ident) => do
      if name.getId == `Bool then
        `(term| Ty.bool)
      else
        let value := Syntax.mkStrLit name.getId.toString
        `(term| Ty.base { name := $value })
  | `(metatheoryTy| $domain:metatheoryTy → $codomain:metatheoryTy) => do
      let domain ← expandTy domain
      let codomain ← expandTy codomain
      `(term| Ty.arrow $domain $codomain)
  | stx => Macro.throwErrorAt stx "unsupported metatheory type syntax"

/-- The typed de Bruijn reference for `name` in a nearest-binder-first environment. -/
private partial def boundRef (name : Name) : List Name → MacroM (TSyntax `term)
  | [] => Macro.throwError s!"unbound metatheory variable `{name}`"
  | binder :: binders =>
      if name == binder then
        `(term| Ref.here)
      else do
        let rest ← boundRef name binders
        `(term| Ref.there $rest)

/-- Expand metatheory object syntax to ordinary Lean constructor syntax. Lean's term
elaborator subsequently infers and checks all intrinsic type indices. -/
private partial def expandTerm (binders : List Name) : Syntax → MacroM (TSyntax `term)
  | `(metatheoryTerm| ($body:metatheoryTerm)) => expandTerm binders body
  | `(metatheoryTerm| ~$term:term) => pure term
  | `(metatheoryTerm| #$constant:term) => `(term| Term.const $constant)
  | `(metatheoryTerm| $name:ident) => do
      let ref ← boundRef name.getId binders
      `(term| Term.var $ref)
  | `(metatheoryTerm| ⊤) => `(term| Term.trueE)
  | `(metatheoryTerm| ⊥) => `(term| Term.falseE)
  | `(metatheoryTerm| ¬ $body:metatheoryTerm) => do
      `(term| Term.not $(← expandTerm binders body))
  | `(metatheoryTerm| $left:metatheoryTerm ∧ $right:metatheoryTerm) => do
      `(term| Term.and $(← expandTerm binders left) $(← expandTerm binders right))
  | `(metatheoryTerm| $left:metatheoryTerm ∨ $right:metatheoryTerm) => do
      `(term| Term.or $(← expandTerm binders left) $(← expandTerm binders right))
  | `(metatheoryTerm| $left:metatheoryTerm → $right:metatheoryTerm) => do
      `(term| Term.imp $(← expandTerm binders left) $(← expandTerm binders right))
  | `(metatheoryTerm| $left:metatheoryTerm ↔ $right:metatheoryTerm) => do
      `(term| Term.iff $(← expandTerm binders left) $(← expandTerm binders right))
  | `(metatheoryTerm| $left:metatheoryTerm = $right:metatheoryTerm) => do
      `(term| Term.eq $(← expandTerm binders left) $(← expandTerm binders right))
  | `(metatheoryTerm| $left:metatheoryTerm ≠ $right:metatheoryTerm) => do
      `(term| Term.ne $(← expandTerm binders left) $(← expandTerm binders right))
  | `(metatheoryTerm| $fn:metatheoryTerm $arg:metatheoryTerm) => do
      `(term| Term.app $(← expandTerm binders fn) $(← expandTerm binders arg))
  | `(metatheoryTerm| λ $name:ident : $domain:metatheoryTy . $body:metatheoryTerm) => do
      let domain ← expandTy domain
      let body ← expandTerm (name.getId :: binders) body
      `(term| Term.lam (domain := $domain) $body)
  | `(metatheoryTerm| ∀ $name:ident : $domain:metatheoryTy, $body:metatheoryTerm) => do
      let domain ← expandTy domain
      let body ← expandTerm (name.getId :: binders) body
      `(term| Term.forallE (domain := $domain) $body)
  | `(metatheoryTerm| ∃ $name:ident : $domain:metatheoryTy, $body:metatheoryTerm) => do
      let domain ← expandTy domain
      let body ← expandTerm (name.getId :: binders) body
      `(term| Term.existsE (domain := $domain) $body)
  | stx => Macro.throwErrorAt stx "unsupported metatheory term syntax"

/-- Quotation for intrinsically typed higher-order terms and formulas. -/
elab "(ho|" body:metatheoryTerm ")" : term => do
  let expanded ← liftMacroM <| expandTerm [] body
  Lean.Elab.Term.elabTerm expanded none

end Crush.Metatheory
