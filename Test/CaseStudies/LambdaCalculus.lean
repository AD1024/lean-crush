import Crush

open Crush
-- open Lean
open Lean.Parser


public section Lam

  set_option crush.trust "reconstruct"

  inductive Ty: Type
  | Boolean
  | Nat
  | Arrow: Ty → Ty → Ty
  deriving Lean.ToExpr

  inductive Term: Type
  | Var (x: String)
  | NatConst (c: Nat)
  | BoolConst (b: Bool)
  | Lam (v: String) (ty: Ty) (body: Term)
  | App: Term → Term → Term
  | Ite: Term → Term → Term → Term
  deriving Lean.ToExpr

  declare_syntax_cat lambda_calculus
  declare_syntax_cat lambda_types

  syntax (name := lamAtomType) ident : lambda_types
  syntax (name := lamArr) (lambda_types "→" lambda_types) : lambda_types

  syntax "(" lambda_calculus ")" : lambda_calculus
  -- Antiquotation: `~e` splices a Lean `Term`-valued expression into the object syntax,
  -- so rules and lemmas can be stated over metavariables (`~t1 ~t2`, `if ~c then ...`).
  syntax:max (name := lamSplice) "~" term:max : lambda_calculus
  syntax (name := lamVar) ident : lambda_calculus
  syntax (name := lamNat) num : lambda_calculus
  syntax (name := lamTrue) "⊤" : lambda_calculus
  syntax (name := lamFalse) "⊥" : lambda_calculus
  syntax (name := lamAbs) ("λ" ident ":" lambda_types "." lambda_calculus) : lambda_calculus
  syntax (name := lamApp) (lambda_calculus lambda_calculus) : lambda_calculus
  syntax (name := lamIte) ("if" lambda_calculus "then" lambda_calculus "else" lambda_calculus) : lambda_calculus

  partial def elabLamTypes : Lean.Syntax → Lean.Meta.MetaM Ty
    | `(lambda_types| $i:ident) =>
        let name := i.getId.toString
        match name with
        | "Boolean" => return Ty.Boolean
        | "Nat" => return Ty.Nat
        | _ => Lean.Elab.throwUnsupportedSyntax
    | `(lambda_types| $l:lambda_types → $r:lambda_types) => do
        let l ← elabLamTypes l
        let r ← elabLamTypes r
        return Ty.Arrow l r
    | _ => Lean.Elab.throwUnsupportedSyntax

  -- Builds the `Expr` denoting the parsed term. Producing an `Expr` (rather than
  -- reifying to a `Term` value and `toExpr`-ing it) is what lets `~e` splice an open
  -- Lean term: a bound metavariable has no value to reify, only an expression to embed.
  partial def elabLamCalc : Lean.Syntax → Lean.Elab.Term.TermElabM Lean.Expr
    | `(lambda_calculus| ($body:lambda_calculus)) => elabLamCalc body
    | `(lambda_calculus| ~$e:term) => Lean.Elab.Term.elabTerm e (some (Lean.mkConst ``Term))
    | `(lambda_calculus| ⊤) => return Lean.mkApp (Lean.mkConst ``Term.BoolConst) (Lean.toExpr true)
    | `(lambda_calculus| ⊥) => return Lean.mkApp (Lean.mkConst ``Term.BoolConst) (Lean.toExpr false)
    | `(lambda_calculus| $i:ident) =>
      return Lean.mkApp (Lean.mkConst ``Term.Var) (Lean.toExpr i.getId.toString)
    | `(lambda_calculus| $n:num) =>
      return Lean.mkApp (Lean.mkConst ``Term.NatConst) (Lean.toExpr n.getNat)
    | `(lambda_calculus| λ $v:ident : $t:lambda_types . $body:lambda_calculus) => do
      return Lean.mkApp3 (Lean.mkConst ``Term.Lam) (Lean.toExpr v.getId.toString)
        (Lean.toExpr (← elabLamTypes t)) (← elabLamCalc body)
    | `(lambda_calculus| $e1:lambda_calculus $e2:lambda_calculus) => do
      return Lean.mkApp2 (Lean.mkConst ``Term.App) (← elabLamCalc e1) (← elabLamCalc e2)
    | `(lambda_calculus| if $cond:lambda_calculus then $ib:lambda_calculus else $eb:lambda_calculus) => do
      return Lean.mkApp3 (Lean.mkConst ``Term.Ite)
        (← elabLamCalc cond) (← elabLamCalc ib) (← elabLamCalc eb)
    | _ => Lean.Elab.throwUnsupportedSyntax

  elab "(lam|" p:lambda_calculus ")" : term => elabLamCalc p

  #eval (lam| λ x : Nat. x)

  abbrev relation (α : Type) := α → α → Prop

  inductive Tr {α : Type} (R : relation α) : relation α where
  | refl : ∀ x, Tr R x x
  | trans: ∀ {x y z}, R x y → Tr R y z → Tr R x z

  -- Values: numeric and boolean literals, and abstractions. A lambda must be a value for
  -- β-reduction to apply once the argument is reduced.
  inductive Value : Term → Prop
  | v_nat : ∀ {n}, Value (Term.NatConst n)
  | v_bool: ∀ {b}, Value (Term.BoolConst b)
  | v_abs : ∀ {x ty body}, Value (Term.Lam x ty body)

  -- Naive (non-capture-avoiding) substitution of `t` for the free `x` in `e`.
  --
  -- Written as direct structural recursion rather than with a `where go` helper: the
  -- per-constructor equation lemmas then peel exactly one layer, leaving a recursive call
  -- on an opaque subterm atomic. `simp only [subst]` therefore exposes a first-order goal
  -- `crush` can close, whereas a `where`-helper's equations unfold into a stuck matcher
  -- the solver chokes on (see the `subst` lemmas below).
  def subst : Term → String → Term → Term
    | Term.Var x',        x, t => if x == x' then t else Term.Var x'
    | Term.NatConst n,    _, _ => Term.NatConst n
    | Term.BoolConst b,   _, _ => Term.BoolConst b
    | Term.Lam b ty body, x, t => if b != x then Term.Lam b ty (subst body x t) else Term.Lam b ty body
    | Term.App e1 e2,     x, t => Term.App (subst e1 x t) (subst e2 x t)
    | Term.Ite c b1 b2,   x, t => Term.Ite (subst c x t) (subst b1 x t) (subst b2 x t)

  -- Call-by-value small-step reduction, left-to-right. The congruence rules use the
  -- object syntax with `~`-splices; β-reduction and its binder are stated with the
  -- constructors directly, since the object syntax's binder is a literal identifier.
  inductive Step : Term → Term → Prop
  | app_left : ∀ {t1 t1' t2 : Term},
      Step t1 t1' → Step (lam| ~t1 ~t2) (lam| ~t1' ~t2)
  | app_right: ∀ {v1 t2 t2' : Term},
      Value v1 → Step t2 t2' → Step (lam| ~v1 ~t2) (lam| ~v1 ~t2')
  | app_beta : ∀ {x : String} {ty : Ty} {body v : Term},
      Value v → Step (Term.App (Term.Lam x ty body) v) (subst body x v)
  | ite_cond : ∀ {c c' e1 e2 : Term},
      Step c c' → Step (lam| if ~c then ~e1 else ~e2) (lam| if ~c' then ~e1 else ~e2)
  | ite_true : ∀ {e1 e2 : Term}, Step (lam| if ⊤ then ~e1 else ~e2) e1
  | ite_false: ∀ {e1 e2 : Term}, Step (lam| if ⊥ then ~e1 else ~e2) e2

  notation L:10 "~>" R:10 => Step L R
  notation L:10 "~>⋆" R:10 => Tr Step L R

  example :
      (lam| (λ f: Nat → Nat. f 0) (if ⊥ then λ x: Nat. x else λ y: Nat. y)) ~>⋆ .NatConst 0 := by
    apply Tr.trans (Step.app_right .v_abs Step.ite_false)
    apply Tr.trans (Step.app_beta .v_abs)
    simp only [subst]
    apply Tr.trans (Step.app_beta .v_nat)
    simp only [subst]
    apply Tr.refl

  /-! ## Example `crush` usage

  `crush` is a first-order SMT hammer. It cannot invert the inductive relations above
  (a `~>⋆` chain, determinism) or fold the recursive `subst` into a terminating query —
  those stay manual, as the reduction proof above shows. What it *does* discharge are
  ground/structural goals and, via defunctionalization, higher-order ones. -/

  -- Datatype no-confusion and injectivity, closed directly.
  example (a b c d : Ty) : Ty.Arrow a b = Ty.Arrow c d → a = c ∧ b = d := by crush
  example (v : String) (ty : Ty) (b : Term) (n : Nat) :
      Term.Lam v ty b ≠ Term.NatConst n := by crush
  example (v1 v2 : String) (t1 t2 : Ty) (b1 b2 : Term) :
      Term.Lam v1 t1 b1 = Term.Lam v2 t2 b2 → v1 = v2 ∧ t1 = t2 ∧ b1 = b2 := by crush

  /-! ### Higher-order obligations, made first-order by defunctionalization

  A valuation of variables is a Lean function `String → Nat`. Extending one *returns a
  function*, and comparing two valuations is an equation *between functions* — higher
  order on its face. `crush`'s defunctionalization encodes each function value as a
  first-order `Fn` sort applied through an `app` symbol and emits that sort's
  extensionality axiom, so the goals below become ordinary first-order SMT queries.
  `@[crush_unfold]` folds `Valuation.set`'s defining equation into each query, so no
  `u[Valuation.set]` hint is needed. -/

  abbrev Valuation := String → Nat

  /-- Extend a valuation, shadowing any previous binding of `x`. -/
  @[crush_unfold]
  def Valuation.set (ρ : Valuation) (x : String) (v : Nat) : Valuation :=
    fun y => if x == y then v else ρ y

  -- Reading back the variable just written.
  example (ρ : Valuation) (x : String) (v : Nat) : (ρ.set x v) x = v := by crush
  -- An unrelated variable is untouched (the inequality comes from a hypothesis).
  example (ρ : Valuation) (x y : String) (v : Nat) (h : x ≠ y) :
      (ρ.set x v) y = ρ y := by crush
  -- Shadowing is a function equality, discharged via the arrow extensionality axiom.
  example (ρ : Valuation) (x : String) (u v : Nat) :
      (ρ.set x u).set x v = ρ.set x v := by crush
  -- Pointwise-equal valuations are equal — funext, as a defunctionalized query.
  example (ρ σ : Valuation) (h : ∀ y, ρ y = σ y) : ρ = σ := by crush

  /-! ### `crush` closing the leaves of a structural induction

  `crush` cannot do induction, but it *can* discharge each first-order leaf a `Term`
  induction produces. The pattern is
  `induction e … <;> simp only [subst, mentions] <;> crush`:

  * the `induction` supplies the recursive structure and the induction hypotheses;
  * `simp only [subst, mentions]` peels **one** layer of the recursion (this is why
    `subst` above is direct structural recursion — its equations expose the recursive
    calls as atomic terms);
  * `crush` closes the residual first-order goal, using the IHs *from context*.

  These particular leaves are equational, so `grind` or `simp` close them too — the value
  here is the *pattern*, not a capability unique to `crush`. Where `crush` genuinely
  outperforms `grind` is offloading to the SMT solver's decision procedures; the
  string-theory section below is an example `grind` cannot do.

  One caveat worth stating: the IHs must stay in context — passing them as explicit
  `crush [ih]` hints triggers eager instantiation against the recursive `subst`/`mentions`
  and diverges. Bare `crush` uses them lazily and succeeds. -/

  -- A boolean "occurs free" test, so we can state the substitution lemmas.
  def mentions (x : String) : Term → Bool
    | Term.Var y => x == y
    | Term.App a b => mentions x a || mentions x b
    | Term.Ite c a b => mentions x c || mentions x a || mentions x b
    | Term.Lam y _ body => if x == y then false else mentions x body
    | _ => false

  /-- Substituting a variable that does not occur free is a no-op — `crush` closes each
  inductive leaf from the IH. -/
  theorem subst_not_free (x : String) (t : Term) :
      ∀ e, mentions x e = false → subst e x t = e := by
    intro e
    induction e with
    | Var y => intro h; simp only [mentions] at h; simp only [subst]; crush
    | NatConst n => intro _; simp only [subst]
    | BoolConst b => intro _; simp only [subst]
    | Lam y ty body ih => intro h; simp only [mentions] at h; simp only [subst]; crush
    | App a b iha ihb => intro h; simp only [mentions] at h; simp only [subst]; crush
    | Ite c a b ihc iha ihb => intro h; simp only [mentions] at h; simp only [subst]; crush

  /-- Idempotency of substitution: substituting twice equals once, provided `x` does not
  occur free in `t` (otherwise the second pass would replace the `x`s inside the inserted
  copies of `t`). Proved by induction on `e`; `crush` closes the congruence leaves. -/
  theorem subst_idem (x : String) (t : Term) (h : mentions x t = false) :
      ∀ e, subst (subst e x t) x t = subst e x t := by
    intro e
    induction e with
    | Var y =>
        by_cases hxy : x = y
        · subst hxy; simp only [subst, beq_self_eq_true, if_true]; exact subst_not_free x t t h
        · simp [subst, hxy]
    | NatConst n => simp only [subst]
    | BoolConst b => simp only [subst]
    | Lam y ty body ih =>
        by_cases hxy : y = x
        · subst hxy; simp [subst]
        · simp only [subst, show (y != x) = true by simp [hxy], if_true]; crush
    | App a b iha ihb => simp only [subst]; crush
    | Ite c a b ihc iha ihb => simp only [subst]; crush

  /-! ### Where `crush` outperforms `grind`: SMT theories

  Variable names are `String`s, so generating a fresh name is genuine string reasoning.
  The SMT solver has a string theory (concatenation, length, injectivity); `crush` uses
  it, while `grind` — which has no string decision procedure — fails on each lemma below.
  This is the case-study's honest answer to "why `crush` and not `grind`": the payoff is
  the solver's dedicated theories, not the small equational goals above. -/

  /-- A fresh variant of a name, distinct from the original. -/
  @[crush_unfold]
  def fresh (x : String) : String := x ++ "'"

  -- `x ++ "'" ≠ x` holds by length; `grind` has no string theory and fails here.
  theorem fresh_ne (x : String) : fresh x ≠ x := by crush
  -- Priming is injective — string concatenation is left-cancellative.
  theorem fresh_injective (x y : String) (h : fresh x = fresh y) : x = y := by crush
  -- Iterated freshening stays distinct from the base name.
  theorem fresh_fresh_ne (x : String) : fresh (fresh x) ≠ x := by
    crush using
      intro heq
      have h := congrArg String.length heq
      simp [fresh] at h
      change x.length + 1 + 1 = x.length at h
      omega

end Lam
