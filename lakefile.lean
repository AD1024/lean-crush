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

-- The soundness-obligation ledger. Kept out of the `Crush`
-- import chain so its `sorry`s never leak into the tactic; built separately so
-- the statements stay type-checked and `#print axioms` stays honest.
lean_lib «Crush.Proofs» where
  globs := #[.submodules `Crush.Proofs]

lean_lib «Test» where
  globs := #[.submodules `Test]
