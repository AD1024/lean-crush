import Crush.Solver.CPC.Parser

open Crush Crush.SMT

private def parsed (source : String) : IO Replay.Proof := do
  match CPC.parseProof source with
  | .ok proof => pure proof
  | .error message => throw <| IO.userError message

private def rejects (source : String) : IO Unit := do
  if (CPC.parseProof source).toOption.isSome then
    throw <| IO.userError s!"accepted malformed CPC certificate: {source}"

#eval show IO Unit from do
  let proof ← parsed "(
    (define @t1 () (= x x))
    (define @t2 () @t1)
    (assume @p1 (not @t2))
    (step @p2 @t2 :rule refl :args (x))
    (step @p3 false :rule contra :premises (@p2 @p1)))"
  unless proof.commands.size == 3 && proof.emptyClauseStep?.isSome &&
      proof.rules == #["refl", "contra"] do
    throw <| IO.userError "CPC shared terms or formula conclusions were not parsed"
  let .step _ clause _ _ _ _ := proof.commands[1]!
    | throw <| IO.userError "expected shared-term step"
  unless clause == #[.list #[.atom "=", .atom "x", .atom "x"]] do
    throw <| IO.userError "CPC definitions were not expanded"

#eval show IO Unit from do
  let proof ← parsed "(
    (assume-push h p)
    (assume-push k q)
    (step s p :rule copy :premises (h))
    (step unused q :rule copy :premises (k))
    (step-pop inner :rule scope :premises (s))
    (step-pop outer :rule scope :premises (inner))
    (step done true :rule arbitrary))"
  unless proof.stats == (2, 7, 2) do
    throw <| IO.userError s!"unexpected scoped command inventory: {proof.stats}"
  let closings := proof.commands.filterMap fun
    | .step id clause "scope" _ _ discharge => some (id, clause, discharge)
    | _ => none
  unless closings.size == 2 && closings[0]!.2.2 == #["k"] &&
      closings[1]!.2.2 == #["h"] do
    throw <| IO.userError "CPC local assumptions were not discharged separately"
  -- A proof identifier can be printed again after its previous scope has closed.
  discard <| parsed "((assume-push h p) (step s p :rule copy :premises (h))
    (step-pop a :rule scope :premises (s))
    (assume-push k q) (step s q :rule copy :premises (k))
    (step-pop b :rule scope :premises (s)))"

#eval show IO Unit from do
  let proof ← parsed "(
    (step r (= (+ (@var \"x\" Int) 0) (@var \"x\" Int)) :rule arith-add-zero)
    (step q (= (forall (@list (@var \"x\" Int)) (= (@var \"x\" Int) (@var \"x\" Int))) true)
      :rule forall-refl))"
  let .step _ #[.list free] _ _ _ _ := proof.commands[0]!
    | throw <| IO.userError "free CPC variable was not universally closed"
  unless free[0]? == some (.atom "forall") do
    throw <| IO.userError "free CPC variable escaped its inference"
  let .step _ #[.list bound] _ _ _ _ := proof.commands[1]!
    | throw <| IO.userError "bound CPC variable was not parsed"
  unless bound[0]? == some (.atom "=") do
    throw <| IO.userError "bound CPC variable was incorrectly generalized twice"
  let shared ← parsed "(
    (define q () (forall (@list (@var \"x\" Int)) (= (@var \"x\" Int) (@var \"x\" Int))))
    (define qq () q)
    (step r (= q qq) :rule refl))"
  let .step _ #[.list #[.atom "=", left, right]] _ _ _ _ := shared.commands[0]!
    | throw <| IO.userError "shared quantified definition changed its binder structure"
  unless left == right && left.list?.any (fun parts => parts[0]? == some (.atom "forall")) do
    throw <| IO.userError "shared quantified definitions were not expanded consistently"

#eval show IO Unit from do
  rejects "((step s :rule refl :args (true)))"
  rejects "((step s true :rule refl :premises (missing)))"
  rejects "((step s true :rule refl) (step s false :rule refl))"
  rejects "((assume-push h false) (step s false :rule copy :premises (h)))"
  rejects "((step-pop s :rule scope :premises (h)))"
  rejects "((assume-push h false) (step s false :rule copy :premises (h))
    (step-pop c :rule scope :premises (s)) (step bad false :rule copy :premises (s)))"
  rejects "((define macro (x) x) (step s true :rule refl))"
  rejects "((define x () x) (step s x :rule refl))"
  rejects "((step s true :rule refl :premises ((macro p))))"
  rejects "((step s true :rule refl :rule trust))"
  rejects "(error \"unsupported certificate\")"
  rejects "((step s true :rule refl)"
