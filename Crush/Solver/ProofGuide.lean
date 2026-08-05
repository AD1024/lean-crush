import Crush.Solver.Alethe

/-!
# Reading an Alethe proof as a reconstruction *guide*

`Crush.Alethe` parses cvc5's proof; this module turns it into the small amount of
information the reconstruction layer can actually act on. It deliberately stops short
of replaying rules onto Lean goals.

## Why a guide rather than a checker

Replaying Alethe step-by-step needs each SMT term mapped back to a Lean `Expr`, and
crush's translation is one-directional (`Crush.Translation.Translate` emits SMT and
keeps only a symbol→origin name map). Building the inverse for every theory is the
bulk of the work in a full checker, and the payoff is small: measurement (2026-08-05)
showed that on every goal where cvc5 returns `unsat`, the existing core-directed
finishers already reconstruct — **except** goals whose proof turns on evaluating a
ground term. cvc5 discharges those with the `evaluate` rule (`str.len "ab" = 2`);
`grind`/`omega`/`simp_all` do not compute them, while `decide`/`rfl` do.

So the guide answers two questions:

1. **Is the proof usable at all?** A `hole` step is cvc5 admitting an untranslated
   rewrite — an unjustified gap. A proof containing one tells us nothing, and treating
   it as a licence to trust would be exactly the silent gap the design forbids.
2. **Does the proof turn on ground evaluation?** If so, offer the evaluating finishers
   (`decide`/`rfl` after substitution), which the default ladder omits because they are
   useless on the common case and can be expensive.

Every answer here only ever *adds* finisher attempts. Reconstruction still succeeds
only when a Lean tactic closes the goal and the kernel accepts the term, so a
misread proof can cost time but cannot make an unproved goal look proved.
-/

namespace Crush.Alethe

/-- Alethe rules that discharge a step by *computing* on ground terms rather than by
logical inference: cvc5 emits these for `str.len "ab" = 2`, `2 = 2`, `(not true) =
false`, and arithmetic on literals. Their Lean counterpart is `decide`/`rfl`/`simp`,
not `grind`/`omega`. -/
def evaluationRules : Array String :=
  #["evaluate", "rare_rewrite", "all_simplify", "string_simplify", "arith_simplify",
    "bool_simplify", "equiv_simplify", "eval", "concat_eq"]

/-- What a proof tells the reconstruction layer. -/
structure Guide where
  /-- Distinct rule names in the proof, for diagnostics. -/
  rules      : Array String
  /-- `true` if any step is `hole` — cvc5 could not justify that step in Alethe, so
  the proof has an unjustified gap and must not be read as a licence for anything. -/
  hasHole    : Bool
  /-- `true` if the proof discharges a step by ground evaluation, so the evaluating
  finishers are worth trying. -/
  needsEval  : Bool
  /-- Step / assume / anchor counts, for diagnostics. -/
  steps      : Nat
  deriving Inhabited, Repr

/-- Read a parsed proof into a `Guide`. -/
def AletheProof.guide (p : AletheProof) : Guide :=
  let rules := p.rules
  { rules
    hasHole   := rules.contains "hole"
    needsEval := rules.any evaluationRules.contains
    steps     := p.stats.2.1 }

/-- The guide for cvc5's raw `(get-proof)` text, or `none` when there is no usable
proof: the text is absent (z3, or proofs switched off), unparseable, cvc5 replied
`(error …)` (it does that for datatype-exhaustiveness goals), or the proof contains a
`hole`. Collapsing all of those to `none` keeps the caller's contract simple — a
`Guide` means "this proof said something checkable". -/
def guideOf? (proofText : String) : Option Guide := do
  if proofText.trimAscii.isEmpty then none
  else
    let p ← parseProof proofText
    let g := p.guide
    -- A holed proof is not a usable justification for anything.
    if g.hasHole then none else some g

end Crush.Alethe
