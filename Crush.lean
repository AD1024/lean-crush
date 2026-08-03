import Crush.SMT.Syntax
import Crush.SMT.Print
import Crush.SMT.Sexp
import Crush.SMT.Result
import Crush.Frontend.Config
import Crush.Reify.Term
import Crush.Reify.Collect
import Crush.Translation.Monad
import Crush.Translation.Attr
import Crush.Translation.Builtins
import Crush.Translation.Translate
import Crush.Solver.Process
import Crush.Frontend.Tactic
-- Note: `Crush.Proofs.Obligations` (the sorry-backed soundness ledger, §10b) is
-- deliberately NOT imported here — the tactic must not depend on unproven
-- obligations, or every downstream proof would pick up `sorryAx`. It is a
-- separate `Proofs` lake target, built and audited on its own.

/-!
# lean-crush

A bridge between Lean 4 and SMT solvers with first-class higher-order support and
a user-extensible, metaprogrammed translation layer.

This root module re-exports the public API. `import Crush` gives you:

* the `crush` tactic (`Crush.Frontend.Tactic`),
* the `@[crush_translate]` attribute and `crush_map`/`crush_map_sort` sugar
  (`Crush.Translation.Attr`, `Crush.Translation.Builtins`),
* all `crush.*` `set_option`s (`Crush.Frontend.Config`).

See `Doc/PLAN.md` for the architecture and implementation roadmap.
-/
