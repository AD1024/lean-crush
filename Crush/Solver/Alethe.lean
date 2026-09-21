import Crush.Solver.Alethe.Replay

/-!
# Alethe certificate replay

Public entry point for parsing and replaying cvc5 Alethe certificates.

* `Parser` reads certificates and inventories their features.
* `Term` decodes certificate terms as Lean expressions.
* `ReplayAttr` provides the replay registries and `register_crush_replay` syntax.
* `ArithmeticRules` and `ReplayRules` provide built-in handlers and their lemmas.
* `Replay` executes certificates and validates the resulting proof.
-/
