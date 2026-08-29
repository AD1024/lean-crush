import VersoManual
import Crush

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Extending lean-crush" =>
%%%
tag := "extending"
%%%

lean-crush can be extended at both sides of the solver boundary:

* translation extensions teach SMT the semantics of Lean types and operations;
* reconstruction extensions teach Lean how to recover a checked proof from an
  `unsat` result.

Adding a translation does not automatically add a reconstruction rule, and
adding a reconstruction rule does not change the SMT query.
Identify which side failed before choosing an API.

# Choosing an Extension Point
%%%
tag := "extending-choose"
%%%

## When SMT Lacks Semantics

An unsupported Lean application is normally translated as an uninterpreted
symbol.
SMT can still use equality congruence, but it cannot reason from the
implementation or algebraic properties of that symbol.

Choose the least powerful mechanism that represents the missing semantics:

1. Use `u[f]`, `d[f]`, `@[crush_unfold]`, or `@[crush_defeq]` when Lean's own
   equations are finite and solver-friendly.
2. Use `crush_map` when a Lean constant is exactly an existing SMT operator, or
   `crush_map_sort` when a monomorphic Lean type is exactly an existing nullary
   SMT sort.
3. Use `@[crush_certified_lower f]` when a Lean primitive maps directly to an
   existing SMT symbol and carries the required semantic contract.
4. Use `@[crush_translate_head f]` when one stable application head needs a
   shape-sensitive encoding.
5. Use `@[crush_translate_family T]` when applications have unstable heads but a
   stable result-family head, including dependent function results.
6. Use `@[crush_translate]` only when dispatch spans several heads or
   intentionally overrides head-indexed and built-in translation.
7. Use `@[crush_translate_sort]` for a parameterized or
   representation-sensitive sort.

Equation support is the safest starting point because Lean already proves the
equations and reconstruction can reuse them.
A lowering produces a smaller, theory-aware SMT term, but the author is
responsible for showing that the encoding has exactly the Lean operation's
semantics.

## When Reconstruction Lacks a Proof

First confirm that SMT returns `unsat`.
Then choose according to the reconstruction algorithm:

* Use `with [...]` for proof terms needed by one call.
* Use `using` for a goal-specific Lean tactic needed by one call.
* Use `@[crush_reconstruct]` for reusable lemmas used by core-directed
  reconstruction.
* Use `register_crush_replay term` to decode a custom SMT term appearing in a
  cvc5 Alethe certificate.
* Use `register_crush_replay rule` to prove a custom or unsupported Alethe
  inference from its replayed premises.

The first three mechanisms operate on the original Lean goal and unsat core.
The last two operate on individual certificate terms and steps.
An Alethe-only run does not consult `@[crush_reconstruct]`, while core-only
reconstruction does not consult replay registrations.

# Equation-Based Support
%%%
tag := "extending-equations"
%%%

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
%%%
tag := "extending-mappings"
%%%

`crush_map` recursively translates the arguments and applies an existing SMT
symbol:

```lean
def addInt (x y : Int) : Int := x + y

crush_map addInt => "+"

example (x y : Int) : addInt x y = y + x := by
  crush
```

This command is appropriate only when every elaborated application of the Lean
constant has the same SMT meaning.
It provides no argument-shape or typeclass-instance guard.
Use `@[crush_translate_head]` instead for overloaded operations, partial support, or
encodings that need to inspect types.

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

@[crush_translate_head MappedInt.value]
def lowerMappedIntValue : LoweringHandler := fun ctx => do
  let #[x] := ctx.args | return none
  return some (← ctx.emitTerm x)

@[crush_translate_head MappedInt.next]
def lowerMappedIntNext : LoweringHandler := fun ctx => do
  let #[x] := ctx.args | return none
  let sx ← ctx.emitTerm x
  return some (smt| (+ $sx 1))

example (x : MappedInt) :
    (MappedInt.next x).value = x.value + 1 := by
  crush
```

`crush_map_sort` and `crush_map` solve different problems.
The former chooses the representation of values of a Lean type; the latter
chooses the operation applied to already translated values.
After mapping a custom type to `Int`, its constructors, projections, and
operations still need compatible term lowerings as the example demonstrates.

The target is emitted verbatim and is not declared.
These commands are therefore appropriate only for solver theory symbols or
sorts already declared elsewhere.
Use a full handler when a fresh declaration is required.

# Targeted Lowerings
%%%
tag := "extending-targeted"
%%%

`@[crush_translate_head target]` registers a handler only for applications whose head is
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

@[crush_translate_head clampNonnegative high]
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
The quotation constructs a structured `Crush.SMT.Term`; it does not insert an
unchecked command string. lean-crush validates the sorts of the final script
before invoking a solver.

Multiple handlers may target the same declaration.
As shown by `lowerClampNonnegative`, a numeric priority or `high`/`low` controls
their order in the same style as `simp`.

Targeted dispatch is preferable to `@[crush_translate]` when the head constant
is known: unrelated applications never invoke the handler, and the declaration
itself records what is being extended.
Like a general handler, a targeted handler may call `ctx.declare` when its
encoding needs fresh SMT declarations.

A handler must decline any shape it cannot encode exactly.
In particular, lowerings for overloaded operations should verify argument types
and call `ctx.hasExpectedInstance` with the exact dictionary whose semantics they
implement before assigning a standard typeclass operation its SMT meaning.
`ctx.hasCanonicalInstance` only compares against ambient global typeclass
synthesis; a higher-priority global instance can change that baseline.
`ctx.hasInstanceHead` is available for dependent dictionaries whose proof
parameters make full definitional equality impractical.

# Certified Lowerings
%%%
tag := "extending-certified"
%%%

An unrestricted lowering is arbitrary metaprogram code and therefore crosses a
trusted translation boundary.
The certified registries are deliberately narrow: their constructors have
fixed behavior and cannot contain an arbitrary SMT callback.

The built-in `Not` mapping is closed rather than user-parameterized. The
constructor fixes Lean `Not` and SMT logical `not`; the metatheory proves that
negation preserves the canonical relation. There is no proposition claiming
that an arbitrary declaration name "denotes" negation, and no axiom claiming
that an arbitrary solver symbol "denotes" SMT `not`.

For user-defined interpreted functions, use the definition constructor. It
delta-reduces the actual Lean definition and recursively translates the
kernel-equivalent body. The user cannot provide a separate SMT body, so the two
sides cannot drift:

```lean
open Crush

@[crush_certified_def]
def releaseReady
    (testsPassed reviewApproved : Prop)
    (freezeActive : Prop) : Prop :=
  testsPassed ∧ reviewApproved ∧ ¬freezeActive

example (testsPassed reviewApproved freezeActive : Prop)
    (ready : releaseReady testsPassed reviewApproved
      freezeActive) :
    testsPassed ∧ reviewApproved ∧ ¬freezeActive := by
  crush
```

Delta reduction turns the application into
`testsPassed ∧ reviewApproved ∧ ¬freezeActive`, after
which ordinary structural translation emits the corresponding `and` and `not`
terms. It emits neither a fresh uninterpreted function nor a solver axiom.

`@[crush_certified_def]` accepts only declarations with a body. An `opaque`
declaration cannot use this path: without a Lean definition or theorem, its
proposed meaning really would be an assumption. If a recursive definition does
not reduce at the current arguments, use its kernel-checked equation lemmas through
`@[crush_unfold]`, `@[crush_defeq]`, `u[f]`, or `d[f]`.

Certified translation and proof discharge are separate concerns.
This restricted step introduces no additional semantic assumption, while
`crush.trust` still determines whether the final solver result is trusted or
reconstructed. Mapping a genuinely external primitive with `crush_map` remains
an explicitly trusted extension until its interpreted operator is added to the
closed verified fragment.

The same mechanism works with interpreted integer operations. Here
`greatest` names the nested result, which is proved to bound all three inputs
and to select one of them:

```lean
@[crush_certified_def]
def intMax (a b : Int) : Int :=
  if a ≥ b then a else b

set_option crush.trust "reconstruct" in
example (a b c : Int) :
    let greatest := intMax a (intMax b c)
    a ≤ greatest ∧ b ≤ greatest ∧
      c ≤ greatest ∧
      (greatest = a ∨ greatest = b ∨
        greatest = c) := by
  dsimp only
  crush using (simp_all [intMax]; grind)
```

`dsimp only` zeta-reduces the local name while leaving `intMax` applications
intact for certified lowering. The solver sees nested integer `ite` and order
terms. The explicit finisher independently checks the result in Lean by
unfolding `intMax` and using `grind`.

# Dependent Result Lowerings
%%%
tag := "extending-result"
%%%

`@[crush_translate_family T]` dispatches on a term's result-family head instead of
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

Use result dispatch only when head dispatch is insufficient.
For an ordinary named operation such as `MappedInt.next`,
`@[crush_translate_head MappedInt.next]` is both cheaper and more precise.
Result dispatch is intended for generated functions, lambdas, and dependent
functions that all produce one representation family.

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

@[crush_translate_family IndexedInt]
def lowerIndexedInt : LoweringHandler := fun ctx => do
  let .const ``indexedInt _ := ctx.fn
    | return none
  let #[index] := ctx.args | return none
  return some (← ctx.emitTerm index)

@[crush_translate_head IndexedInt.value]
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
%%%
tag := "extending-general"
%%%

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

Because a general handler is consulted for every application, it should reject
non-matching heads before doing reduction or type inference.
Prefer targeted or result-indexed handlers when either dispatch key is
available.

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

# Parameterized Sort Handlers
%%%
tag := "extending-sorts"
%%%

`@[crush_translate_sort]` is the sort-level counterpart to
`@[crush_translate]`.
It can inspect type arguments and recursively translate them with
`ctx.emitSort`.

Use `crush_map_sort` when a monomorphic Lean type always maps to one existing
nullary SMT sort.
Use a sort handler when the target sort depends on Lean type arguments, needs
guards, or requires declarations.

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

@[crush_translate_head TotalMap.get]
def translateTotalMapGet :
    TranslationHandler := fun ctx => do
  let #[keyTy, valueTy, map, key] := ctx.args
    | return none
  let mapSort ← ctx.emitSort (← Lean.Meta.inferType map)
  let keySort ← ctx.emitSort keyTy
  let valueSort ← ctx.emitSort valueTy
  unless mapSort ==
      .app (.symb "Array") #[keySort, valueSort] do
    return none
  let smap ← ctx.emitTerm map
  let skey ← ctx.emitTerm key
  return some (smt| (select $smap $skey))

@[crush_translate_head TotalMap.set]
def translateTotalMapSet :
    TranslationHandler := fun ctx => do
  let #[keyTy, valueTy, _, map, key, value] := ctx.args
    | return none
  let mapSort ← ctx.emitSort (← Lean.Meta.inferType map)
  let keySort ← ctx.emitSort keyTy
  let valueSort ← ctx.emitSort valueTy
  unless mapSort ==
      .app (.symb "Array") #[keySort, valueSort] do
    return none
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
%%%
tag := "extending-arrays"
%%%

Downstream Array operations can reuse lean-crush's canonical finite-array
representation through `withFiniteArray`.
The callback receives a let-bound Array value, its logical length, its SMT array
data, and a constructor helper:

```lean
open Crush

def overwriteFirst {α : Type}
    (xs : Array α) (value : α) : Array α :=
  xs.setIfInBounds 0 value

@[crush_translate_head overwriteFirst]
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
%%%
tag := "extending-soundness"
%%%

Before registering a lowering:

* Match the complete elaborated argument spine, including type and instance
  arguments.
* Check overloaded instances rather than assuming they are canonical.
* Recurse through `ctx.emitTerm` and `ctx.emitSort`.
* Verify operand sorts and return `none` for unsupported types or
  representations.
* Use `ctx.declare` for fresh SMT symbols.
* Preserve Lean's behavior at boundary cases such as division by zero and
  out-of-bounds indexing.
* Add a negative regression demonstrating that the encoding cannot prove an
  arbitrary result.

Under `crush.trust "reconstruct"`, Lean checks the final proof, but an incorrect
lowering still causes confusing failures.
Under the default trust policy, translation correctness is part of the trusted
computing base.

# Extending Checked Reconstruction
%%%
tag := "extending-reconstruction"
%%%

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

set_option crush.trust "reconstruct" in
example (phase : Phase) :
    Advances phase (.next phase) := by
  crush d[Advances]
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
with `@[crush_unfold]`, or define a lowering as described above.

Use a local attribute when the theorem should affect only one section:

```lean
theorem initialAdvances :
    Advances .initial (.next .initial) :=
  rfl

attribute [local crush_reconstruct] initialAdvances
```

Unlike `with [advancesNext phase]`, the registered theorem is matched lazily
against reconstruction goals and can be applied at different arguments.
Unlike `using`, it supplies a declarative rule rather than a complete tactic
script.

# Extending Alethe Replay
%%%
tag := "extending-alethe"
%%%

Alethe replay has two extension layers:

1. certificate terms are decoded back into Lean expressions;
2. certificate inference rules are proved from their replayed premises.

The `register_crush_replay term` and `register_crush_replay rule` commands
extend these layers without requiring Lean metaprogramming.
Trust mode does not replay a certificate, but checked reconstruction must
decode every relevant term and construct a proof for every inference.

A term registration is an inverse translation: use it when a custom lowering
introduces an SMT operator that may appear in the certificate.
A rule registration is a proof procedure: use it when terms already decode but
one named Alethe inference is unsupported.
Adding one does not substitute for the other.

## Replay DSL Syntax

The registration commands have the following EBNF.
`lean-term`, `lean-type`, and `tactic-sequence` are ordinary Lean syntax;
`priority` is `low`, `high`, or a natural number.

```
term-registration ::=
  "register_crush_replay" "term" [priority] "<<"
    term-pattern {"|" term-pattern}
    "=>" lean-term ">>"

rule-registration ::=
  "register_crush_replay" "rule" [priority] "<<"
    rule-pattern {"|" rule-pattern}
    ["if" lean-term]
    "=>" "by" tactic-sequence ">>"

term-pattern ::=
    "(" symbol {expr-pattern} ")"
  | "(" "(" "_" symbol {sexp-pattern} ")" {expr-pattern} ")"

rule-pattern ::= "(" symbol {sexp-pattern} ")"
symbol       ::= identifier | string-literal

expr-pattern ::=
    "_"
  | ".."
  | "(term" identifier [":" lean-type] ")"

sexp-pattern ::=
    "_"
  | ".."
  | identifier
  | natural
  | string-literal
  | "(atom" string-literal ")"
  | "(sexp" identifier ")"
  | "(term" identifier [":" lean-type] ")"
  | "(nat" identifier ")"
  | "(int" identifier ")"
  | "(string" identifier ")"
  | "(atom" identifier ")"
  | "(sort" identifier ")"
  | "(prop" identifier ")"
  | "(" {sexp-pattern} ")"
```

An ordinary term pattern matches an SMT operator whose arguments have already
been decoded to Lean expressions.
The `(_ operator indices...)` form additionally matches an indexed SMT
identifier, while a rule pattern matches an Alethe rule name and its raw
`:args`.
`..` is permitted only as the final pattern in an argument list.
Every capture name must occur once per alternative, and all `|` alternatives
must bind the same names.
Only rule registrations accept an `if` condition, and only their right-hand
side is a tactic script.
The outer `<< ... >>` fence reserves `>>` as its closing delimiter, and `=>`
separates a rule condition from its tactic. Define a named Lean value when a
condition itself would otherwise need either token.

## Define an Inverse Term

The following lowering emits `((_ divisible 3) value)`.
The inverse registration also accepts `(divisible 3 value)`, the normalized
form that cvc5 may use in a certificate:

```lean
open Lean Meta
open Crush Crush.Alethe Crush.SMT

def MultipleOfThree (value : Int) : Prop :=
  value % 3 = 0

@[crush_translate_head MultipleOfThree]
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

Append `if condition` when matching the certificate syntax alone is not enough.
The condition is a metaprogrammed dispatch guard, not a Lean proposition:

```lean
structure ReplayStringBindingIs where
  name : Name
  expected : String

instance : ReplayCondition ReplayStringBindingIs where
  check condition ctx := do
    let captured := ctx.binding? condition.name
    let some (.lit (.strVal value)) := captured
      | return false
    return value == condition.expected

def docsEnabledReplay : ReplayStringBindingIs where
  name := `mode
  expected := "enabled"

register_crush_replay rule low <<
  (docs_conditional_rule (atom mode) ..)
    if docsEnabledReplay =>
    by exact True.intro
>>
```

`ReplayCondition α` defines `check : α → ReplayRuleContext → MetaM Bool`.
The guard runs after the pattern has matched, so it can inspect the target,
premises, raw arguments, and named captures through `ctx.binding?`.
It runs without retaining metavariable-state changes.
Returning `false` delegates to the next registration; an exception reports a
broken condition.
When a registration has several `|` alternatives, the condition applies to all
of them.
A callback of type `ReplayConditionHandler` can be used directly through the
built-in instance.

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

Prefer the `register_crush_replay` pattern DSL for a fixed certificate shape.
Use `@[crush_replay]` or `@[crush_replay_rule]` only when matching requires
recursive inspection, dynamic operator selection, or custom metavariable
control.

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
