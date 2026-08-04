import Lake
open Lake DSL

package «crush» where
  precompileModules := true
  preferReleaseBuild := false
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

@[default_target]
lean_lib «Crush» where
  -- Root module re-exports the public API (tactic + attribute + config).

lean_lib «Test» where
  globs := #[.submodules `Test]
