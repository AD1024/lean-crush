import Crush.SMT.Syntax
import Crush.SMT.Print
import Crush.Frontend.Config
import Crush.Reify.Term
import Crush.Translation.Monad
import Crush.Translation.Attr
import Crush.Translation.Builtins
import Crush.Solver.Process

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
