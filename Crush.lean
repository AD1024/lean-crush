import Crush.SMT.Syntax
import Crush.SMT.Quote
import Crush.SMT.Print
import Crush.SMT.Check
import Crush.SMT.Sexp
import Crush.SMT.Result
import Crush.Metatheory.Datatype.Core
import Crush.Metatheory.Datatype.Semantics
import Crush.Metatheory.Datatype.Syntax
import Crush.Metatheory.Datatype.Model
import Crush.Metatheory.Datatype.Guarded
import Crush.Metatheory.Datatype.Carrier
import Crush.Metatheory.Datatype.FamilyModel
import Crush.Metatheory.Datatype.Flattened
import Crush.Metatheory.HO
import Crush.Metatheory.FO.Core
import Crush.Metatheory.FO.Semantics
import Crush.Metatheory.FO.Symbols
import Crush.Metatheory.FO.Family
import Crush.Metatheory.FO.FamilySemantics
import Crush.Metatheory.FO.Guarded
import Crush.Metatheory.Defunctionalization.Collect
import Crush.Metatheory.Defunctionalization.Annotate
import Crush.Metatheory.Defunctionalization.Eta
import Crush.Metatheory.Defunctionalization.EtaCorrectness
import Crush.Metatheory.Defunctionalization.Translate
import Crush.Metatheory.Defunctionalization.Core
import Crush.Metatheory.Defunctionalization.LogicalRelation
import Crush.Metatheory.Notation
import Crush.Metatheory.Defunctionalization.Fundamental
import Crush.Metatheory.Defunctionalization.ModelExtension
import Crush.Metatheory.Defunctionalization.FlattenedApplication
import Crush.Metatheory.Defunctionalization.ProductionClosure
import Crush.Metatheory.Defunctionalization.Flattened.Denotation
import Crush.Metatheory.Defunctionalization.Flattened.Theory
import Crush.Metatheory.Guarded.Encoding
import Crush.Metatheory.Hooks
import Crush.Metatheory.SMT.Datatype
import Crush.Metatheory.SMT.DatatypeGuard
import Crush.Metatheory.SMT.DatatypeGuarded
import Crush.Metatheory.SMT.DatatypeLifted
import Crush.Metatheory.SMT.DatatypeCarry
import Crush.Metatheory.SMT.Semantics
import Crush.Metatheory.SMT.Representation
import Crush.Metatheory.SMT.Guarded
import Crush.Metatheory.SMT.Model
import Crush.Metatheory.SMT.ModelExtension
import Crush.Metatheory.SMT.DatatypeRepresentation
import Crush.Metatheory.SMT.DatatypeCanonical
import Crush.Metatheory.SMT.Soundness
import Crush.Metatheory.SMT.GuardedSoundness
import Crush.Metatheory.SMT.Int
import Crush.Metatheory.Reification.Type
import Crush.Metatheory.Reification.Datatype
import Crush.Metatheory.VCG.Command
import Crush.Metatheory.VCG.Datatype
import Crush.Metatheory.Reification.Capture
import Crush.Metatheory.Reification.Term
import Crush.Metatheory.Reification.Reify
import Crush.Metatheory.Reification.Witness
import Crush.Metatheory.VCG.Trust
import Crush.Metatheory.VCG.Generate
import Crush.Frontend.Config
import Crush.Frontend.Collect
import Crush.Translation.Monad
import Crush.Metatheory.VCG.Stateful
import Crush.Metatheory.VCG.Soundness
import Crush.Metatheory.VCG.Production
import Crush.Translation.Attr
import Crush.Translation.Unfold
import Crush.Translation.Preprocess
import Crush.Translation.Builtins
import Crush.Translation.Monomorphize
import Crush.Translation.Instantiate
import Crush.Translation.Translate
import Crush.Translation.DefaultLowerings
import Crush.Solver.Process
import Crush.Solver.AletheReplay
import Crush.Solver.Reconstruct
import Crush.Frontend.Tactic

/-!
# lean-crush

A bridge between Lean 4 and SMT solvers with first-class higher-order support and
a user-extensible, metaprogrammed translation layer.

This root module re-exports the public API. `import Crush` gives you:

* the `crush` tactic (`Crush.Frontend.Tactic`),
* the `@[crush_translate]` and `@[crush_translate_head]` attributes, `(smt| ...)` quotations,
  and `crush_map`/`crush_map_sort` sugar
  (`Crush.Translation.Attr`, `Crush.SMT.Quote`, `Crush.Translation.Builtins`),
* the `@[crush_reconstruct]` attribute for extending checked proof replay
  (`Crush.Solver.ReconstructAttr`),
* `register_crush_replay`, `@[crush_replay]`, and
  `@[crush_replay_rule]` for extending checked Alethe replay
  (`Crush.Solver.AletheReplay`),
* all `crush.*` `set_option`s (`Crush.Frontend.Config`).

See `README.md` and `Doc/PLAN.md` for the architecture and roadmap.
-/
