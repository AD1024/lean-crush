import Lake
open Lake DSL

-- Mathlib pinned at the tag whose toolchain is exactly ours (`v4.32.2`), so it can be
-- `require`d without the toolchain conflict that blocks the loom/lean-auto case studies.
-- Fetched via `lake exe cache get` (prebuilt oleans), never compiled here. Only
-- `Test/CaseStudies/Mathlib.lean` imports it; the library and other tests use `Crush`.
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.32.2"

package «crush» where
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
  -- `precompileModules` lives here, not on the package: the tactic's native code is
  -- loaded when `Crush` is imported (fast metaprogram evaluation), but the setting does
  -- NOT propagate to the `Test` lib. That matters once Mathlib is a dependency — a
  -- package-level `true` forces every Test module to precompile its *whole* transitive
  -- import closure, which compiles Mathlib into a 118 MB dylib and then `dlopen`s it,
  -- segfaulting the elaborator. Mathlib itself ships `precompileModules := false` (its
  -- cache is olean-only) for exactly this reason, so we keep Test olean-only too.
  precompileModules := true

lean_lib «Test» where
  globs := #[.submodules `Test]
