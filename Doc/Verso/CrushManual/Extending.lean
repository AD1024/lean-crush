import VersoManual
import Crush

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Extending Translation" =>
%%%
tag := "extending"
%%%

An unsupported Lean function is translated as an uninterpreted symbol.
This preserves congruence but not the function's implementation or algebraic
properties.
There are three ways to add the missing semantics:

1. expose Lean equation lemmas;
2. map a constant directly to an existing SMT theory symbol;
3. register a metaprogrammed lowering for full control.

# Extending Checked Reconstruction

Translation and proof reconstruction are separate extension points.
When SMT already understands enough semantics to report `unsat`, but
`crush.trust "reconstruct"` needs a domain theorem to rebuild the argument,
register it with `@[crush_reconstruct]`:

```lean
inductive Phase where
  | initial
  | next (previous : Phase)

def Advances (source target : Phase) : Prop :=
  target = .next source

@[crush_reconstruct]
theorem advancesNext (phase : Phase) :
    Advances phase (.next phase) :=
  rfl
```

Registered theorems participate in bounded backward proof search.
The search uses a structural index to match their conclusion against the current
reconstruction goal,
solves their premises with the core-restricted Lean finishers, and checks the
resulting term with Lean's kernel.
It is datatype-independent, so downstream libraries can register bridge lemmas
for their own inductive types and relations without adding those rules wholesale
to `grind`.

This attribute does not send a theorem to SMT.
If the solver also needs the fact, pass it to `crush [...]`, expose equations
with `@[crush_unfold]`, or define a lowering as described below.

# Equation-Based Support

Use `u[f]` or `d[f]` at one call site.
Use attributes when the definition should be available wherever it is relevant:

```lean
@[crush_unfold]
def distanceFromZero (x : Int) : Int :=
  if x < 0 then -x else x

example (x : Int) : 0 ≤ distanceFromZero x := by
  crush
```

`@[crush_unfold]` registers all equation lemmas.
`@[crush_defeq]` registers only the single definitional equation.
Here the single equation is enough to expose a proposition wrapper:

```lean
@[crush_defeq]
def isNonnegative (x : Int) : Prop :=
  0 ≤ x

example (x : Int) (h : isNonnegative x) :
    0 < x + 1 := by
  crush
```

Both can be local attributes when importing code that cannot be modified:

```lean
attribute [local crush_unfold] List.length

example (xs : List Int) : xs.length = 0 ↔ xs = [] := by
  crush
```

Equation-based support is the simplest choice when unfolding is finite and does
not create solver quantifier loops.

# Direct Symbol Mappings

`crush_map` recursively translates the arguments and applies an existing SMT
symbol:

```lean
def addInt (x y : Int) : Int := x + y

crush_map addInt => "+"

example (x y : Int) : addInt x y = y + x := by
  crush
```

`crush_map_sort` maps a Lean type constructor to an existing nullary SMT sort.
The Lean type and SMT sort must represent the same values.
For example, a one-field structure over `Int` is representation-isomorphic to
SMT `Int`; its projection and operation can then use identity and arithmetic
lowerings:

```lean
open Crush

structure MappedInt where
  value : Int

namespace MappedInt

def next (x : MappedInt) : MappedInt :=
  ⟨x.value + 1⟩

end MappedInt

crush_map_sort MappedInt => "Int"

@[crush_lower MappedInt.value]
def lowerMappedIntValue : LoweringHandler := fun ctx => do
  let #[x] := ctx.args | return none
  return some (← ctx.emitTerm x)

@[crush_lower MappedInt.next]
def lowerMappedIntNext : LoweringHandler := fun ctx => do
  let #[x] := ctx.args | return none
  let sx ← ctx.emitTerm x
  return some (smt| (+ $sx 1))

example (x : MappedInt) :
    (MappedInt.next x).value = x.value + 1 := by
  crush
```

The target is emitted verbatim and is not declared.
These commands are therefore appropriate only for solver theory symbols or
sorts already declared elsewhere.
Use a full handler when a fresh declaration is required.

# Targeted Lowerings

`@[crush_lower target]` registers a handler only for applications whose head is
`target`.
The handler receives the original Lean arguments and recursive `emitTerm` and
`emitSort` callbacks.
The head and arguments are syntactic and are not weak-head-normalized before
dispatch; use the available `MetaM` operations when a handler needs reduction.
It returns `some term` when it recognizes an application and `none` to defer:

```lean
open Crush

def clampNonnegative (x : Int) : Int :=
  if x < 0 then 0 else x

@[crush_lower clampNonnegative high]
def lowerClampNonnegative : LoweringHandler := fun ctx => do
  let #[x] := ctx.args | return none
  let sx ← ctx.emitTerm x
  return some (smt| (ite (< $sx 0) 0 $sx))

example (x : Int) (hx : 0 ≤ x) :
    clampNonnegative x = x := by
  crush
```

The `(smt| ...)` quotation is a shallow embedding of SMT-LIB terms.
Symbols, numerals, strings, and applications use SMT-LIB syntax.
`$term` splices an existing `Crush.SMT.Term`.
The quotation constructs lean-crush's typed SMT syntax tree; it does not insert
an unchecked command string.

Multiple handlers may target the same declaration.
As shown by `lowerClampNonnegative`, a numeric priority or `high`/`low` controls
their order in the same style as `simp`.

A handler must decline any shape it cannot encode exactly.
In particular, lowerings for overloaded operations should verify argument types
and call `ctx.hasExpectedInstance` with the exact dictionary whose semantics they
implement before assigning a standard typeclass operation its SMT meaning.
`ctx.hasCanonicalInstance` only compares against ambient global typeclass
synthesis; a higher-priority global instance can change that baseline.
`ctx.hasInstanceHead` is available for dependent dictionaries whose proof
parameters make full definitional equality impractical.

# Dependent Result Lowerings

`@[crush_lower_result T]` dispatches on a term's result-family head instead of
its application head.
It first checks the immediate head of the inferred type.
If that type is syntactically a dependent function, it opens the binders and
checks the codomain head.
Named aliases remain separate dispatch keys, so register the alias too when
callers may retain it in the inferred type.
This is useful for generated declarations and lambdas whose head is unstable,
but whose result family is known.
The handler still receives the original term's `ctx.fn` and `ctx.args`; peeled
binders are used only to select the handler.

The term representation must agree with a sort handler.
Here every `IndexedInt index` is representation-isomorphic to SMT `Int`,
even though the result type depends on the input:

```lean
open Crush

structure IndexedInt (index : Int) where
  value : Int

def indexedInt (index : Int) : IndexedInt index :=
  ⟨index⟩

@[crush_translate_sort]
def translateIndexedIntSort : SortHandler := fun ctx => do
  let .const ``IndexedInt _ := ctx.fn
    | return none
  let #[_] := ctx.args | return none
  return some (.app (.symb "Int") #[])

@[crush_lower_result IndexedInt]
def lowerIndexedInt : LoweringHandler := fun ctx => do
  let .const ``indexedInt _ := ctx.fn
    | return none
  let #[index] := ctx.args | return none
  return some (← ctx.emitTerm index)

@[crush_lower IndexedInt.value]
def lowerIndexedIntValue : LoweringHandler := fun ctx => do
  let #[_, value] := ctx.args | return none
  return some (← ctx.emitTerm value)

example (index : Int) :
    (indexedInt index).value = index := by
  crush
```

The built-in `Decidable` encoding uses this path.
`Decidable p` and dependent functions ending in it are represented by an
axiomatized singleton SMT sort, matching Lean's proof-irrelevant subsingleton.
Concretely, the lowering emits the equivalent of:

```
(declare-sort Decision 0)
(declare-fun decision () Decision)
(assert (forall ((d Decision)) (= d decision)))
```

Observing the value with `decide p` lowers to `p`; consequently,
`DecidableEq` is observed as SMT equality without encoding the implementation
of a particular decision procedure.
The built-in handler is registered for both `Decidable` and the named
`DecidableEq` alias.

# General Handlers

`@[crush_translate]` registers a `TranslationHandler` that can inspect every
term head.
General handlers run before targeted lowerings, so they can override built-in
behavior.
Use this when dispatch cannot be expressed by one head constant, or when one
handler intentionally recognizes a family of constants:

```lean
open Crush

def translatedSuccessor (x : Int) : Int :=
  x + 1

@[crush_translate]
def translateSuccessor : TranslationHandler := fun ctx => do
  let .const ``translatedSuccessor _ := ctx.fn
    | return none
  let #[x] := ctx.args | return none
  let sx ← ctx.emitTerm x
  return some (smt| (+ $sx 1))

example (x : Int) :
    translatedSuccessor x = x + 1 := by
  crush
```

The `ctx.declare` callback can emit declarations once and return the allocated
symbol.
This example gives an opaque Lean function an equally opaque SMT function.
The declaration is emitted once even though the translated symbol occurs twice:

```lean
open Crush

opaque externalToken : Int → Int

@[crush_translate]
def translateExternalToken :
    TranslationHandler := fun ctx => do
  let .const ``externalToken _ := ctx.fn
    | return none
  let #[x] := ctx.args | return none
  let intSort : SMT.SSort :=
    .app (.symb "Int") #[]
  let fn ← ctx.declare "docs.externalToken"
    "external_token" fun name => do
      return #[.declFun name #[intSort] intSort]
  let sx ← ctx.emitTerm x
  return some (.app (.symb fn) #[sx])

example (x y : Int) (h : x = y) :
    externalToken x = externalToken y := by
  crush
```

# Extending Alethe Replay

Alethe replay has two extension layers:

1. certificate terms are decoded back into Lean expressions;
2. certificate inference rules are proved from their replayed premises.

The `register_crush_replay term` and `register_crush_replay rule` commands
extend these layers without requiring Lean metaprogramming.
Trust mode does not replay a certificate, but checked reconstruction must
decode every relevant term and construct a proof for every inference.

## Define an Inverse Term

The following lowering emits `((_ divisible 3) value)`.
The inverse registration also accepts `(divisible 3 value)`, the normalized
form that cvc5 may use in a certificate:

```lean
open Lean Meta
open Crush Crush.Alethe Crush.SMT

def MultipleOfThree (value : Int) : Prop :=
  value % 3 = 0

@[crush_lower MultipleOfThree]
def lowerMultipleOfThree : LoweringHandler := fun ctx => do
  let #[value] := ctx.args | return none
  return some
    (.app (.indexed "divisible" #[.inr 3])
      #[← ctx.emitTerm value])

register_crush_replay term <<
  ((_ divisible (int divisor)) (term value : Int)) |
  (divisible (term divisor : Int) (term value : Int)) =>
    value % divisor = 0
>>
```

An ordinary pattern has the form `(operator arguments...)`.
An indexed pattern has the form
`((_ operator indices...) arguments...)`.
Indices are raw S-expressions; ordinary arguments have already been decoded to
Lean expressions.

The pattern language provides:

* `_` for one ignored item and a final `..` for the remaining items;
* bare symbols, numerals, and strings for exact matches;
* `(sexp x)` for a raw `Sexp`;
* `(term x)` for a decoded Lean expression;
* `(term x : T)` for a decoded expression whose Lean type is definitionally
  equal to `T`;
* `(nat x)`, `(int x)`, `(string x)`, and `(atom x)` for parsed raw values;
* `(sort x)` for a decoded SMT sort and `(prop x)` for a decoded proposition.

`nat` and `int` parse certificate metadata directly.
They are not abbreviations for typed `term` captures.
For example, `(nat width)` parses a raw decimal width as a Lean `Nat`, whereas
`(term width : Nat)` asks the certificate term decoder to reconstruct a
Nat-valued SMT term.

Alternatives separated by `|` must bind the same names, though their concrete
certificate shapes may differ.
Built-in term decoding runs before custom registrations.
Use `register_crush_replay term high`, `low`, or a numeric priority when
multiple custom registrations can match the same operator.
The right-hand side is type-checked, but Crush cannot infer whether it is the
intended inverse of a custom lowering.
An inaccurate inverse causes source-assumption bridging or later replay steps
to fail; it is never accepted in place of a kernel-checked proof.

## Register an Inference Rule

A rule pattern matches the Alethe rule name followed by its raw `:args`:

```lean
register_crush_replay rule low <<
  (docs_arith_commute
    (term left : Int) (term right : Int)) |
  (docs_arith_swap (term left : Int) (term right : Int)) =>
    by omega
>>
```

The right-hand side is an ordinary Lean tactic script.
Its goal is the decoded conclusion of that certificate step.
The local context contains only the step's replayed premises and the values
captured by the pattern; unrelated hypotheses from the user's theorem are not
available.
If the tactic does not close the goal, replay tries the next registration.

Alternatives and captures follow the same rules as term registrations.
Use `register_crush_replay rule high`, `low`, or a numeric priority to control
dispatch.
Exact-rule handlers run before wildcard low-level handlers.

Every proof returned by a rule registration is checked against the step target
with `Lean.Kernel.check`.
Declarations generated while the tactic runs are checked recursively as well.
A failed check is an error, not a replay miss.

## Low-Level Handlers

Use attributes when matching requires arbitrary metaprogramming:

```lean
@[crush_replay "docs.zero"]
def replayDocsZero : ReplayTermHandler := fun ctx => do
  let #[] := ctx.indices | return none
  let #[] := ctx.args | return none
  return some (Lean.toExpr (0 : Int))

@[crush_replay_rule "docs_rule" low]
def replayDocsRule : ReplayRuleHandler := fun ctx => do
  unless ctx.args.isEmpty do return none
  ctx.runTacticWithScopeFallback (← `(tactic| grind))
```

A `ReplayTermContext` exposes `head`, raw `indices`, and recursively decoded
`args`.
A `ReplayRuleContext` additionally exposes the step target, clause literals,
replayed premises, raw rule arguments, term/sort decoders, and enclosing
subproof facts.
Returning `none` delegates to the next handler.
`runTactic` uses only ordinary premises; `runTacticWithScopeFallback` retries
with enclosing subproof facts when the certificate rule requires them.

## Test Term Decoding

A solver may simplify away an operator or change the shape used in a live
certificate.
Add a deterministic fixture for every accepted spelling:

```lean
private def parseAletheTerm
    (source : String) : MetaM Sexp := do
  let some (term, rest) := parseSexp source
    | throwError "failed to parse Alethe term `{source}`"
  unless rest.trimAscii.isEmpty do
    throwError "trailing input after Alethe term `{source}`"
  return term

private def assertDecoded
    (symbols : Std.HashMap String Expr)
    (source : String) (expected : Expr) : MetaM Unit := do
  let decoders ← getReplayTermHandlers
  let context : TermCtx := {
    symbols
    named := {}
    decoders
  }
  let term ← parseAletheTerm source
  let some actual ← toExpr? context 64 term
    | throwError "failed to decode Alethe term `{source}`"
  unless ← isDefEq actual expected do
    throwError "decoder mismatch for `{source}`"

run_meta do
  unless ← hasReplayTermHandlersFor "divisible" do
    throwError
      "the `divisible` replay handler was not registered"
  withLocalDeclD `x (mkConst ``Int) fun x => do
    let remainder ←
      mkAppM ``HMod.hMod #[x, Lean.toExpr (3 : Int)]
    let expected ←
      mkEq remainder (Lean.toExpr (0 : Int))
    let symbols :=
      ({} : Std.HashMap String Expr).insert "x" x
    assertDecoded symbols "((_ divisible 3) x)" expected
    assertDecoded symbols "(divisible 3 x)" expected
```

`TermCtx.symbols` maps symbolic SMT atoms back to Lean expressions.
`toExpr?` then exercises the same recursive decoder used by certificate replay.

## Require Alethe in an Integration Test

Run a symbolic theorem with cvc5 and Alethe-only reconstruction.
Using `"auto"` here is insufficient because core-directed reconstruction could
hide a broken replay registration:

```lean
section

set_option crush.backend "cvc5"
set_option crush.trust "reconstruct"
set_option crush.reconstruct "alethe"
set_option crush.timeout 10

theorem customDivisibilityReplay (x : Int)
    (hx : MultipleOfThree x) :
    ¬x % 3 ≠ 0 := by
  crush

#print axioms customDivisibilityReplay

end
```

The theorem must elaborate without `Crush.crushSorry` in the `#print axioms`
output.
Use symbolic operands and a property that depends on the custom operator;
closed computations may be discharged before replay exercises the extension.

The complete executable tests, including alternatives, priorities, context
isolation, compatibility, and kernel rejection, are in
[Test/AletheExtension.lean](https://github.com/AD1024/lean-crush/blob/main/Test/AletheExtension.lean).

## Diagnose Replay Failures

The first failure classification identifies the layer to address:

* `term-gap` means a certificate term could not be converted to Lean. Add or
  correct a `register_crush_replay term` registration or
  `@[crush_replay]` handler.
* `rule-gap` means the terms decoded, but Lean could not prove one concrete
  inference from its replayed premises. Add a
  `register_crush_replay rule` registration or `@[crush_replay_rule]` handler.
* “did not emit an Alethe certificate” means cvc5 proved the query but could not
  serialize the proof. No downstream extension can recover a certificate that
  the solver did not produce.
* `kernel-reject` or `replay-exception` indicates an invalid generated proof or
  an implementation defect. Reduce the failing theorem and report the
  certificate step.

`@[crush_reconstruct]` extends core-directed reconstruction, not individual
Alethe inference replay.
In strict `crush.reconstruct "alethe"` mode, every required inference must be
supported by Alethe replay itself.

# Parameterized Sort Handlers

`@[crush_translate_sort]` is the sort-level counterpart to
`@[crush_translate]`.
It can inspect type arguments and recursively translate them with
`ctx.emitSort`.

A total Lean map is exactly the model provided by SMT Array theory.
The sort handler maps `TotalMap key value` to `(Array key value)`, while term
handlers map lookup and update to `select` and `store`:

```lean
open Crush

structure TotalMap (κ ν : Type) where
  fn : κ → ν

namespace TotalMap

def get {κ ν : Type}
    (m : TotalMap κ ν) (k : κ) : ν :=
  m.fn k

def set {κ ν : Type} [DecidableEq κ]
    (m : TotalMap κ ν)
    (k : κ) (v : ν) : TotalMap κ ν :=
  ⟨fun k' => if k' = k then v else m.fn k'⟩

end TotalMap

@[crush_translate_sort]
def translateTotalMapSort : SortHandler := fun ctx => do
  let .const ``TotalMap _ := ctx.fn
    | return none
  let #[key, value] := ctx.args | return none
  let keySort ← ctx.emitSort key
  let valueSort ← ctx.emitSort value
  return some (.app (.symb "Array")
    #[keySort, valueSort])

@[crush_translate]
def translateTotalMapGet :
    TranslationHandler := fun ctx => do
  let .const ``TotalMap.get _ := ctx.fn
    | return none
  let #[_, _, map, key] := ctx.args | return none
  let smap ← ctx.emitTerm map
  let skey ← ctx.emitTerm key
  return some (smt| (select $smap $skey))

@[crush_translate]
def translateTotalMapSet :
    TranslationHandler := fun ctx => do
  let .const ``TotalMap.set _ := ctx.fn
    | return none
  let #[_, _, _, map, key, value] := ctx.args
    | return none
  let smap ← ctx.emitTerm map
  let skey ← ctx.emitTerm key
  let svalue ← ctx.emitTerm value
  return some (smt| (store $smap $skey $svalue))

example (m : TotalMap Int Int) (k value : Int) :
    TotalMap.get (TotalMap.set m k value) k = value := by
  crush
```

Operation lowerings must agree with the selected representation.
They should return `none` when the operand's type or another sort handler's
representation does not match their encoding.

# Extending Finite Arrays

Downstream Array operations can reuse lean-crush's canonical finite-array
representation through `withFiniteArray`.
The callback receives a let-bound Array value, its logical length, its SMT array
data, and a constructor helper:

```lean
open Crush

def overwriteFirst {α : Type}
    (xs : Array α) (value : α) : Array α :=
  xs.setIfInBounds 0 value

@[crush_lower overwriteFirst]
def lowerOverwriteFirst : LoweringHandler := fun ctx => do
  let #[elem, xs, value] := ctx.args | return none
  let svalue ← ctx.emitTerm value
  withFiniteArray ctx elem xs fun view => do
    let data := (smt| (store $(view.data) 0 $svalue))
    let updated := view.mkValue view.length data
    return (smt| (ite (> $(view.length) 0)
      $updated $(view.value)))

example (xs : Array Int) (value : Int) (_h : 0 < xs.size) :
    (overwriteFirst xs value)[0]! = value := by
  crush
```

`withFiniteArray` returns `none` if a custom sort handler selected another
representation.
It also inserts an SMT `let`, preventing repeated selectors from duplicating a
nested update term.

# Soundness Checklist

Before registering a lowering:

* Match the complete elaborated argument spine, including type and instance
  arguments.
* Check overloaded instances rather than assuming they are canonical.
* Recurse through `ctx.emitTerm` and `ctx.emitSort`.
* Return `none` for unsupported types or representations.
* Use `ctx.declare` for fresh SMT symbols.
* Preserve Lean's behavior at boundary cases such as division by zero and
  out-of-bounds indexing.
* Add a negative regression demonstrating that the encoding cannot prove an
  arbitrary result.

Under `crush.trust "reconstruct"`, Lean checks the final proof, but an incorrect
lowering still causes confusing failures.
Under the default trust policy, translation correctness is part of the trusted
computing base.
