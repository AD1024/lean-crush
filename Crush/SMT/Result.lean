import Crush.SMT.Sexp

/-!
# Interpreting solver output

Turns the raw text captured from a solver's `get-unsat-core` / `get-model` into
structured data the tactic can act on:

* `parseUnsatCore` — the list of fact ids named `crush_fact_<n>` in the core, so
  the discharge layer can select exactly the hypotheses the solver used
  so a failure can name the hypotheses actually responsible.
* `parseModel` — the `(define-fun …)` assignments from a `sat` answer, so a
  failed goal can be reported as a concrete counterexample rather than a generic
  "failed".
-/

namespace Crush.SMT

/-- The prefix we attach to every asserted fact's `:named` attribute. The numeric
suffix indexes back into `TranslateState.facts`. -/
def factNamePrefix : String := "crush_fact_"

-- Nested inductive over `Array`; the recursion goes through a list helper so the
-- descent is structural and this is total rather than `partial`.
mutual
  /-- All fact ids named `crush_fact_<n>` anywhere within an S-expression. -/
  private def collectFactIds : Sexp → Array Nat
    | .atom name =>
      if name.startsWith factNamePrefix then
        match (name.drop factNamePrefix.length).toNat? with
        | some n => #[n]
        | none => #[]
      else #[]
    | .list xs => collectFactIdsList xs.toList
    | .str _ => #[]
  termination_by x => sizeOf x
  decreasing_by obtain ⟨l⟩ := xs; simp [Array.mk.sizeOf_spec]; omega

  private def collectFactIdsList : List Sexp → Array Nat
    | [] => #[]
    | x :: xs => collectFactIds x ++ collectFactIdsList xs
  termination_by xs => sizeOf xs
  decreasing_by all_goals (simp_wf; omega)
end

/-- Extract the fact ids referenced in an unsat core. The core text is an
S-expression list of names, e.g. `(crush_fact_3 crush_fact_7)`. Robust to a
leading `unsat` token and to surrounding whitespace/comments. -/
def parseUnsatCore (coreText : String) : Array Nat :=
  (parseSexps coreText).foldl (fun acc s => acc ++ collectFactIds s) #[]

/-- A single model assignment from `get-model`: a symbol and its value rendered
back to SMT-LIB text (kept as text since interpreting it needs the sort context). -/
structure ModelEntry where
  name  : String
  value : String
  deriving Inhabited, Repr

/-- Parse a `get-model` response into its `(define-fun name () sort value)`
entries. Tolerates the `(model …)` wrapper some solvers emit and the bare list
form (SMT-LIB 2.6) others use. -/
def parseModel (modelText : String) : Array ModelEntry := Id.run do
  let mut entries := #[]
  for top in parseSexps modelText do
    let items : Array Sexp := match top with
      | .list xs =>
        -- Either `(model (define-fun …) …)` or a bare `((define-fun …) …)`.
        match xs[0]? with
        | some (Sexp.atom "model") => xs.extract 1 xs.size
        | _ => xs
      | _ => #[]
    for item in items do
      if let Sexp.list defn := item then
        match defn[0]?, defn[1]?, defn.back? with
        | some (Sexp.atom "define-fun"), some (Sexp.atom name), some val =>
          entries := entries.push { name, value := toString val }
        | _, _, _ => pure ()
  return entries

end Crush.SMT
