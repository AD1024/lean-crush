#!/usr/bin/env python3
"""Remove auxiliary proof search from a pinned PLean benchmark checkout.

Keep WP generation, normalization, case/conjunction splits, and frame walking.
Their leaves use pverify_smt (the selected backend), including the case analysis
inside default_inv. Do not edit solver internals. Run after the backend patch.

The proof marker survives only in the final proof, unlike traces emitted by
backtracked tactic attempts. PLEAN_BENCH records total obligation tactic time
(including failed attempts) and whether that final proof uses the backend.
"""

import argparse
import re
from pathlib import Path

MARKER = "-- PLEAN_BACKEND_ONLY_V1"
AUXILIARY = {"grind", "omega", "tauto", "assumption", "trivial", "solve_by_elim"}

# Mask comments and strings without moving offsets. Lean block comments nest.
def code_mask(text: str) -> str:
    chars = list(text)
    i = 0
    while i < len(text):
        start = i
        if text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("unterminated Lean block comment")
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            i += 1
            continue
        for j in range(start, i):
            if chars[j] != "\n":
                chars[j] = " "
    return "".join(chars)


def replace_auxiliary(text: str) -> str:
    mask = code_mask(text)
    edits = []
    for match in re.finditer(r"(?<![\w.'])[A-Za-z_][\w']*(?![\w.'])", mask):
        if match.group() not in AUXILIARY:
            continue
        end = match.end()
        if match.group() == "solve_by_elim":
            hints = re.match(r"\s*\[[^\]]*\]", mask[end:])
            if hints:
                end += hints.end()
        edits.append((match.start(), end))
    for start, end in reversed(edits):
        text = text[:start] + "pverify_smt" + text[end:]
    # Removing alternative solvers should not repeatedly run the same closer.
    while re.search(r"pverify_smt\s*\|\s*pverify_smt", text):
        text = re.sub(r"pverify_smt\s*\|\s*pverify_smt", "pverify_smt", text)
    return text


INSTRUMENTATION = r'''
-- PLEAN_BACKEND_ONLY_V1
-- An identity marker records which backend proofs occur in the final term.
def pverifyBackendProof {α : Sort u} (h : α) : α := h

initialize pverifyBenchTimes : IO.Ref (Std.HashMap String Nat) ← IO.mkRef ∅

elab "pverify_backend" "(" ts:tacticSeq ")" : tactic => do
  let mut next := []
  for g in ← getGoals do
    let fresh ← g.withContext do
      let fresh ← mkFreshExprSyntheticOpaqueMVar (← g.getType) (tag := ← g.getTag)
      g.assign (← mkAppM ``pverifyBackendProof #[fresh])
      pure fresh.mvarId!
    next := next ++ [fresh]
  setGoals next
  evalTactic ts

'''


def patch_tactic(text: str, backend: str) -> str:
    if MARKER in text:
        raise ValueError("tree is already patched; use --check")
    original_code = code_mask(text)
    # Protect and mark the selected backend before replacing auxiliary tactics.
    if backend == "auto":
        primary = r"loom_smt \[\*\]"
        expected = 1
    else:
        primary = {
            "crush": r"all_goals crush \[\*\]",
            "duper": r"all_goals duper \[\*\]",
            "grind": r"all_goals grind \(splits := \d+\)",
            "smt": r"all_goals smt [^\n]*?\[\*\]",
        }[backend]
        expected = 3
    protected = []
    def protect(match):
        command = match.group()
        if command.startswith("all_goals "):
            command = "all_goals pverify_backend (" + command[10:] + ")"
        else:
            command = "pverify_backend (" + command + ")"
        protected.append(command)
        return f"PLEAN_SELECTED_BACKEND_{len(protected) - 1}"
    matches = list(re.finditer(primary, code_mask(text)))
    count = len(matches)
    for match in reversed(matches):
        text = text[:match.start()] + protect(match) + text[match.end():]
    if count != expected:
        raise ValueError(f"expected {expected} {backend} backend sites, found {count}")
    text = replace_auxiliary(text)
    for i, command in enumerate(protected):
        text = text.replace(f"PLEAN_SELECTED_BACKEND_{i}", command)
    # Auto's profiled path inlines the solver invocation instead of calling
    # loom_smt. Mark its successful assignment too, without changing that path.
    if backend == "auto":
        old = '(mvPost.assign (mkApp (mkConst ``Loom.SMT.trust_smt) goalTypePost))'
        new = '(mvPost.assign (← mkAppM ``pverifyBackendProof #[mkApp (mkConst ``Loom.SMT.trust_smt) goalTypePost]))'
        if text.count(old) != 1:
            raise ValueError("Auto's profiled proof assignment changed")
        text = text.replace(old, new)
    anchor = 'syntax "pverify_log_failure_else_sorry " tacticSeq : tactic'
    if text.count(anchor) != 1:
        raise ValueError("obligation wrapper changed")
    text = text.replace(anchor, INSTRUMENTATION + anchor)
    old = "        let savedGoals ← getGoals\n"
    if text.count(old) != 1:
        raise ValueError("saved-goal wrapper changed")
    text = text.replace(old, "        let benchStart ← IO.monoNanosNow\n" + old)
    old = "        | none => pure ()\n"
    end = text.index(old, text.index(anchor)) + len(old)
    text = text[:end] + r'''
        let benchElapsed := (← IO.monoNanosNow) - benchStart
        let benchKey ← currentObligationKey
        liftM (m := IO) (pverifyBenchTimes.modify (·.insert benchKey benchElapsed))
        let mut usesBackend := false
        let mut incomplete := false
        for g in savedGoals do
          let value ← instantiateMVars (mkMVar g)
          incomplete := incomplete || value.hasSorry || value.hasExprMVar
          usesBackend := usesBackend || (value.find? fun e =>
            e.isConstOf ``pverifyBackendProof).isSome
        let provenance := if incomplete then "failed"
          else if usesBackend then "backend" else "scaffold"
        IO.println s!"PLEAN_BENCH\t{benchKey}\t{benchElapsed}\t{provenance}"
''' + text[end:]
    # A patch must never silently delete the scaffold while changing leaves.
    patched_code = code_mask(text)
    for scaffold in ("rcases", "by_cases", "cases", "refine", "pverify_split_smt",
                     "pverify_split_ite_smt", "pverify_frame_walk"):
        pattern = r"\b" + scaffold + r"\b"
        if len(re.findall(pattern, original_code)) != len(re.findall(pattern, patched_code)):
            raise ValueError(f"patch unexpectedly changed the {scaffold} scaffold")
    return text


def patch_obligation(text: str) -> str:
    old = "first | (intros; trivial) | pverify_smt"
    if text.count(old) != 1:
        raise ValueError("base-case automation changed")
    text = text.replace(old, "pverify_smt")
    # A diagnostic pilot may select exact VC names without invoking the other
    # obligations. The full benchmark leaves this environment variable unset.
    anchor = "  let (manualProof, emitError?) ← try\n      let m ← emitter\n"
    if text.count(anchor) != 1:
        raise ValueError("obligation emission entry point changed")
    return text.replace(anchor, '''  let (manualProof, emitError?) ← try
      if let some selected ← IO.getEnv "PLEAN_BENCH_VCS" then
        unless (selected.splitOn "\\n").contains key do
          throwError "not selected for diagnostic pilot"
      let m ← emitter
''')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tree", type=Path)
    parser.add_argument("--backend", required=True, choices=["auto", "crush", "duper", "grind", "smt"])
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    tactic = args.tree / "PLean/Verify/Tactic.lean"
    obligation = args.tree / "PLean/Verify/Obligation.lean"
    if args.check:
        if MARKER not in tactic.read_text() or "intros; trivial" in code_mask(obligation.read_text()):
            parser.error("PLean tree does not have the backend-only patch")
        return
    # Validate both transformations before writing either source.
    new_tactic = patch_tactic(tactic.read_text(), args.backend)
    new_obligation = patch_obligation(obligation.read_text())
    tactic.write_text(new_tactic)
    obligation.write_text(new_obligation)


if __name__ == "__main__":
    main()
