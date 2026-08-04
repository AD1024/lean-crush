import Crush.SMT.Syntax

/-!
# A concrete denotational semantics for the emitted SMT terms

This module exists because of a specific methodological failure worth recording.

An earlier version of the soundness ledger stated its obligations over an **opaque**
`Interp` and `Sat`:

```lean
opaque Interp : Type
opaque Sat : Interp → List CTerm → Prop
def Equivalence (T) : Prop := ∀ I Γ, Sat I Γ ↔ Sat I (T Γ)
```

Nothing can be proven or refuted about an opaque predicate, so `Equivalence T`
constrained nothing at all. Worse, the higher-order obligations were "proved" by
defining *both* sides:

```lean
def appOf F x := F x
def closureOf φ := φ
theorem p4a : appOf (closureOf φ) x = φ x := rfl   -- i.e. `φ x = φ x`
```

That is a tautology wearing the costume of a soundness theorem. It type-checks, it
depends on no axioms, and it says **nothing** about `Crush/Translation/Translate.lean`.
Meanwhile real unsoundness bugs kept surfacing in the translator — which is the
evidence that the ledger had no contact with the code.

The fix is this file: an actual `Value` domain and an actual evaluator for
`SMT.Term`. Because `eval` is a real function, a claim about it can be *false*, and
`decide`/`native_decide`/`simp` can refute it. That is the property the opaque
version lacked.

Scope: the fragment the translator actually emits — booleans, integers, and the
operators appearing in `Translate.lean`. Bit-vectors and strings are represented but
their operators are left to future work; `eval` returns `none` on anything
unmodelled rather than inventing a value, so a theorem quantified over "terms that
evaluate" can never be vacuously satisfied by a gap in the semantics.
-/

namespace Crush.Proofs

open Crush.SMT

/-- The value domain. An SMT model assigns one of these to every term. -/
inductive Value where
  | bool : Bool → Value
  | int  : Int → Value
  | str  : String → Value
  /-- A bit-vector of the given width, value taken modulo `2 ^ width`. -/
  | bv   : (width : Nat) → (value : Nat) → Value
  deriving DecidableEq, BEq, Inhabited, Repr

namespace Value

def asBool? : Value → Option Bool
  | .bool b => some b
  | _ => none

def asInt? : Value → Option Int
  | .int i => some i
  | _ => none

end Value

/-- An interpretation: a total assignment of values to symbol applications.

Taking the environment as `String → List Value → Option Value` models an SMT model
directly — uninterpreted symbols are exactly the ones whose meaning the model picks
— and covers nullary symbols (constants) as the empty-argument case. -/
structure Interp where
  /-- The meaning of an uninterpreted symbol applied to argument values. -/
  symbols : String → List Value → Option Value
  /-- Values bound by enclosing `forall`/`exists`/`let`/`lambda`, innermost first. -/
  binders : List Value := []

namespace Interp

/-- Push a binder value, as entering a quantifier does. -/
def push (I : Interp) (v : Value) : Interp := { I with binders := v :: I.binders }

/-- Push several binder values; the first element of `vs` becomes innermost, so a
`forall` binding `x̄` pushes them in reverse. -/
def pushAll (I : Interp) (vs : List Value) : Interp :=
  { I with binders := vs ++ I.binders }

end Interp

/-- Interpret a literal. -/
def evalLit : Literal → Value
  | .bool b => .bool b
  | .num n => .int (Int.ofNat n)
  | .str s => .str s
  | .bitvec w v => .bv w (v % 2 ^ w)

/-- Whether two values inhabit the same sort. Used to reject heterogeneous `ite`
and `=`, which SMT-LIB forbids but z3 silently accepts. -/
def sameSortV : Value → Value → Bool
  | .bool _, .bool _ => true
  | .int _, .int _ => true
  | .str _, .str _ => true
  | .bv w _, .bv w' _ => w == w'
  | _, _ => false

/-- All ways of picking one value from each list, preserving order. -/
def cartesian : List (List Value) → List (List Value)
  | [] => [[]]
  | vs :: rest => (cartesian rest).flatMap fun tl => vs.map fun v => v :: tl

/-- Evaluate an *interpreted* operator applied to already-evaluated arguments.

Returns `none` when the symbol is not a theory operator (so the caller falls back to
the interpretation) or when the arguments have the wrong shape. Deliberately total
and deliberately partial: a wrong-sorted application yields `none` rather than a
coerced value, which is what makes ill-sorted emission detectable here even though
z3 silently accepts it. -/
def evalOp (f : String) (args : List Value) : Option Value :=
  match f, args with
  -- Propositional
  | "true", [] => some (.bool true)
  | "false", [] => some (.bool false)
  | "not", [.bool a] => some (.bool (!a))
  | "and", vs => boolFold (· && ·) true vs
  | "or", vs => boolFold (· || ·) false vs
  | "=>", [.bool a, .bool b] => some (.bool (!a || b))
  | "xor", [.bool a, .bool b] => some (.bool (a != b))
  -- Equality and ite are sort-polymorphic but must be *homogeneous*.
  | "=", [a, b] => if sameSort a b then some (.bool (a == b)) else none
  | "distinct", [a, b] => if sameSort a b then some (.bool (a != b)) else none
  -- Integer arithmetic
  | "-", [.int a] => some (.int (-a))
  | "+", vs => intFold (· + ·) 0 vs
  | "*", vs => intFold (· * ·) 1 vs
  | "-", [.int a, .int b] => some (.int (a - b))
  | "<=", [.int a, .int b] => some (.bool (a ≤ b))
  | "<", [.int a, .int b] => some (.bool (a < b))
  | ">=", [.int a, .int b] => some (.bool (a ≥ b))
  | ">", [.int a, .int b] => some (.bool (a > b))
  -- SMT-LIB `div`/`mod` are Euclidean, and are *underspecified* at a zero divisor.
  -- We model the divisor-zero case as `none` (no committed value) rather than
  -- picking one, so a theorem about them cannot silently rely on our choice.
  | "div", [.int a, .int b] => if b == 0 then none else some (.int (a / b))
  | "mod", [.int a, .int b] => if b == 0 then none else some (.int (a % b))
  | _, _ => none
where
  sameSort : Value → Value → Bool
    | .bool _, .bool _ => true
    | .int _, .int _ => true
    | .str _, .str _ => true
    | .bv w _, .bv w' _ => w == w'
    | _, _ => false
  boolFold (op : Bool → Bool → Bool) (init : Bool) (vs : List Value) : Option Value := do
    let bs ← vs.mapM Value.asBool?
    return .bool (bs.foldl op init)
  intFold (op : Int → Int → Int) (init : Int) (vs : List Value) : Option Value := do
    let is ← vs.mapM Value.asInt?
    return .int (is.foldl op init)

/-- The finite domain a quantifier ranges over, for the purposes of this semantics.

Quantifying over `Int` is not decidable, so `eval` handles quantifiers only when an
explicit finite domain is supplied — which is enough to state and *test* the
properties that matter (the guard shapes in P10, the operator agreements in P11).
`none` means "no domain available", and `eval` then declines rather than guessing. -/
abbrev Domain := SSort → Option (List Value)

/-- Evaluate an SMT term under an interpretation.

`none` means *not modelled*: an unmodelled operator, an ill-sorted application, a
quantifier without a finite domain, an unbound de Bruijn index, or exhausted fuel.
It never means "false" — conflating the two is how a semantics stops being able to
refute anything.

`Term` is a nested inductive over `Array`, so this recurses on an explicit `fuel`
argument rather than on the term. That keeps `eval` a *total, reducible* definition,
which is what makes claims about it decidable — and therefore refutable. A `partial
def` would type-check but block `decide`, leaving us unable to demonstrate that a
false claim is false, which is the whole failure this module exists to correct. -/
def eval (fuel : Nat) (dom : Domain) (I : Interp) : Term → Option Value :=
  match fuel with
  | 0 => fun _ => none
  | fuel + 1 => fun t =>
    match t with
    | .lit l => some (evalLit l)
    | .bvar i => I.binders[i]?
    | .annot t _ => eval fuel dom I t
    -- `ite` must be *lazy in the untaken branch*, matching SMT-LIB: a guard such as
    -- `(ite (= b 0) 0 (div a b))` is precisely a device for keeping the solver away
    -- from the underspecified branch, so evaluating both would defeat its purpose and
    -- report the guarded term as unmodelled. (Getting this wrong is what a real
    -- semantics catches: the strict version refuted the `intDivGuard` theorems.)
    | .app (.symb "ite") #[c, t, e] => do
      let cv ← eval fuel dom I c
      let b ← cv.asBool?
      let taken ← eval fuel dom I (if b then t else e)
      -- Laziness must not cost sort-checking. If the *untaken* branch also has a
      -- value, the two must agree in sort; if it has none (the guarded-division
      -- case, where that is the whole point) the taken branch stands alone.
      match eval fuel dom I (if b then e else t) with
      | some other => if sameSortV taken other then some taken else none
      | none => some taken
    | .app (.symb f) args => do
      let vs ← args.toList.mapM (eval fuel dom I)
      match evalOp f vs with
      | some v => some v
      | none => I.symbols f vs
    | .app (.indexed _ _) _ => none
    | .letE binds body => do
      let vs ← binds.toList.mapM (fun b => eval fuel dom I b.2)
      eval fuel dom (I.pushAll vs.reverse) body
    | .forallE bs body => do
      let vss ← bs.toList.mapM (fun b => dom b.2)
      let results ← (cartesian vss).mapM fun vs =>
        (eval fuel dom (I.pushAll vs.reverse) body).bind Value.asBool?
      return .bool (results.all id)
    | .existsE bs body => do
      let vss ← bs.toList.mapM (fun b => dom b.2)
      let results ← (cartesian vss).mapM fun vs =>
        (eval fuel dom (I.pushAll vs.reverse) body).bind Value.asBool?
      return .bool (results.any id)
    -- A `lambda` term is a value only in the higher-order fragment, which this
    -- first-order value domain does not represent.
    | .lam _ _ => none

/-- `I` satisfies `t` when `t` evaluates to `true`.

Note the asymmetry with `¬ Sat`: a term that does not evaluate (`none`) is *not*
satisfied, but neither is it refuted. Obligations must therefore be stated over
terms that evaluate, and `evaluates` below makes that hypothesis explicit rather
than hiding it. -/
def Sat (fuel : Nat) (dom : Domain) (I : Interp) (t : Term) : Prop :=
  eval fuel dom I t = some (Value.bool true)

/-- `t` has a value under `I` — the hypothesis that keeps an obligation from being
vacuously true by falling into the unmodelled case. -/
def evaluates (fuel : Nat) (dom : Domain) (I : Interp) (t : Term) : Prop :=
  (eval fuel dom I t).isSome

end Crush.Proofs
