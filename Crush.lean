import Crush.SMT.Syntax
import Crush.SMT.Quote
import Crush.SMT.Print
import Crush.SMT.Check
import Crush.SMT.Sexp
import Crush.SMT.Result
import Crush.Frontend.Config
import Crush.Reify.Term
import Crush.Reify.Collect
import Crush.Translation.Monad
import Crush.Translation.Attr
import Crush.Translation.Unfold
import Crush.Translation.Preprocess
import Crush.Translation.Builtins
import Crush.Translation.Monomorphize
import Crush.Translation.Translate
import Crush.Translation.DefaultLowerings
import Crush.Solver.Process
import Crush.Solver.Alethe
import Crush.Solver.AletheTerm
import Crush.Solver.AletheReplay
import Crush.Solver.Reconstruct
import Crush.Frontend.Tactic

/-!
# lean-crush

A bridge between Lean 4 and SMT solvers with first-class higher-order support and
a user-extensible, metaprogrammed translation layer.

This root module re-exports the public API. `import Crush` gives you:

* the `crush` tactic (`Crush.Frontend.Tactic`),
* the `@[crush_translate]` and `@[crush_lower]` attributes, `(smt| ...)` quotations,
  and `crush_map`/`crush_map_sort` sugar
  (`Crush.Translation.Attr`, `Crush.SMT.Quote`, `Crush.Translation.Builtins`),
* all `crush.*` `set_option`s (`Crush.Frontend.Config`).

See `README.md` and `Doc/PLAN.md` for the architecture and roadmap.
-/
