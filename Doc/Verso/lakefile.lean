import Lake

open Lake DSL

package «crush-docs» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, false⟩
  ]

require verso from git
  "https://github.com/leanprover/verso.git" @ "v4.32.0"

require crush from "../.."

lean_lib CrushManual

@[default_target]
lean_exe «crush-docs» where
  root := `CrushManualMain
  supportInterpreter := true
