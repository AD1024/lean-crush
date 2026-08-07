import Lake
open Lake DSL

-- Mathlib integration tests are a separate package so installing `crush` does not
-- fetch Mathlib or its transitive dependency graph.
require crush from ".."
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.32.2"

package crushMathlibTest where
  reservoir := false
  packagesDir := "../.lake/packages"
  preferReleaseBuild := false
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, false⟩
  ]

@[default_target]
lean_lib MathlibTest where
  globs := #[.submodules `MathlibTest]
