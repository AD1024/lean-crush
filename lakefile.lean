import Lake
open Lake DSL

package «crush» where
  precompileModules := true
  preferReleaseBuild := false
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    -- Test goals routinely bind hypotheses (`h`, `h0`, …) that the *goal* refers to
    -- but the proof body (`by crush`) never names, since `crush` reads the whole
    -- context. That is intentional, not dead code, so the unused-variable linter is
    -- pure noise here — and its warnings clutter CI output enough to bury a real
    -- error. Turn it off package-wide; the library carries no such bindings.
    ⟨`linter.unusedVariables, false⟩
  ]

@[default_target]
lean_lib «Crush» where
  -- Root module re-exports the public API (tactic + attribute + config).

lean_lib «Test» where
  globs := #[.submodules `Test]
