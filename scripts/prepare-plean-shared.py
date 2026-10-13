#!/usr/bin/env python3
"""Generate one PLean scaffold for all backends, retaining Auto's Lean 4.24.

The source of the scaffold and VC generator is P@9c098b4. Only BenchBackend
selects a backend. Auto's counterexample pretty-printer uses the older parser;
that compatibility change is outside VC generation and proof search.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

REV = '9c098b4c5ad32faf2a022929b6726d2a182a9e1d'
AUTO_REV = 'be39726723e71f9aa1e02c6cfeeae9b0c31b8947'
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('ablation', HERE / 'prepare-plean-backend-only.py')
ablation = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ablation)

COMMON_CLOSE = '''/-! The benchmark always disables the obligation cache. -/
register_option pverify.cache : Bool := { defValue := false }
register_option pverify.profile : Bool := { defValue := true }

def pverifySmtCloseDefault : TacticM Unit := do
  if pverify.cache.get (← getOptions) then
    throwError "the shared benchmark forbids cached proofs"
  evalTactic (← `(tactic| pverify_smt_prep))
  unless (← getGoals).isEmpty do
    evalTactic (← `(tactic| all_goals pverify_backend (pverify_selected_backend)))

def pverifySmtCloseProfiled : TacticM Unit := pverifySmtCloseDefault

'''

OPTION = '''
open Lean Elab Tactic
register_option pverify.benchmark.backend : String := { defValue := "unset" }
syntax "pverify_selected_backend" : tactic
elab_rules : tactic
  | `(tactic| pverify_selected_backend) => do
    match pverify.benchmark.backend.get (← getOptions) with
'''
BACKENDS = {
    'modern': 'import Crush\nimport Duper\nimport Smt\n' + OPTION + '''
    | "crush" => evalTactic (← `(tactic| crush [*]))
    | "grind" => evalTactic (← `(tactic| grind (splits := 20)))
    | "duper" => evalTactic (← `(tactic| duper [*]))
    | "smt" => evalTactic (← `(tactic| smt +mono (timeout := 5) [*]))
    | other => throwError "unsupported benchmark backend: {other}"
''',
    'auto': 'import Loom.SMT\n' + OPTION + '''
    | "auto" => evalTactic (← `(tactic| loom_smt [*]))
    | other => throwError "unsupported benchmark backend: {other}"
''',
}


def read_git(repo, rev, relative):
    return subprocess.check_output(['git', '-C', str(repo), 'show', f'{rev}:Src/PLean/{relative}'], text=True)


def common_tactic(original):
    text = ablation.patch_tactic(original, 'crush')
    text = text.replace('import Loom.SMT', 'import PLean.Verify.BenchBackend')
    start = text.index('/-! ## Obligation cache')
    end = text.index('syntax "pverify_smt" : tactic', start)
    text = text[:start] + COMMON_CLOSE + text[end:]
    text = text.replace('pverify_backend (crush [*])', 'pverify_backend (pverify_selected_backend)')
    # Record the original VC type before any backend-dependent attempt.
    anchor = '        let savedGoals ← getGoals\n'
    text = text.replace(anchor, anchor + '''        for g in savedGoals do
          let ty ← instantiateMVars (← g.getType)
          IO.println s!"PLEAN_VC_TYPE\\t{← currentObligationKey}\\t{Json.compress (toJson (reprStr ty))}"
''')
    text = text.replace('        let benchStart ← IO.monoNanosNow\n', '')
    text = text.replace('        let mut diagnostic : Option String := none',
                        '        let benchStart ← IO.monoNanosNow\n        let mut diagnostic : Option String := none')
    # Do not pay for a duplicate leaf call left by removing alternative provers.
    text = text.replace('first | pverify_smt | (refine ⟨?_, ?_⟩ <;> pverify_smt) | pverify_smt',
                        'first | pverify_smt | (refine ⟨?_, ?_⟩ <;> pverify_smt)')
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', required=True, type=Path)
    parser.add_argument('--out', required=True, type=Path)
    parser.add_argument('--variant', required=True, choices=BACKENDS)
    parser.add_argument('--auto-loom', type=Path)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=False)
    files = subprocess.check_output(['git', '-C', str(args.repo), 'ls-tree', '-r', '--name-only', REV, 'Src/PLean'], text=True).splitlines()
    for file in files:
        relative = str(Path(file).relative_to('Src/PLean'))
        target = args.out / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(subprocess.check_output(['git', '-C', str(args.repo), 'show', f'{REV}:{file}']))
    tactic = args.out / 'PLean/Verify/Tactic.lean'
    tactic.write_text(common_tactic(tactic.read_text()))
    obligation = args.out / 'PLean/Verify/Obligation.lean'
    obligation.write_text(ablation.patch_obligation(obligation.read_text())
                          .replace('(joined.take maxChars).toString', 'toString (joined.take maxChars)')
                          .replace('Verify.renderValue (.list d.args)', 'Verify.renderModelArgs d'))
    (args.out / 'PLean/Verify/BenchBackend.lean').write_text(BACKENDS[args.variant])
    if args.variant == 'auto':
        # Parser/diagnostic representation only, no proof-producing code.
        for relative in ['PLean/Verify/CexParse.lean', 'PLean/Verify/CexModel.lean']:
            (args.out / relative).write_text(read_git(args.repo, AUTO_REV, relative))
        if args.auto_loom is None:
            parser.error('--auto-loom is required for the Auto compatibility adapter')
        smt = args.auto_loom / 'Loom/SMT.lean'
        target = args.out / 'Loom/SMT.lean'
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(smt.read_text())
        (args.out / 'lean-toolchain').write_text('leanprover/lean4:v4.24.0\n')
    model = args.out / 'PLean/Verify/CexModel.lean'
    constructor = 'app' if args.variant == 'auto' else 'list'
    model.write_text(model.read_text() + f'\nnamespace PLean.Verify\ndef renderModelArgs (d : ModelDef) : String := renderValue (.{constructor} d.args)\nend PLean.Verify\n')
    manifest = {str(p.relative_to(args.out)): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in args.out.rglob('*.lean')}
    (args.out / 'shared-source-hashes.json').write_text(json.dumps(manifest, indent=2) + '\n')


if __name__ == '__main__':
    main()
