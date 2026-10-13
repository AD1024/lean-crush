# Table 4: replay implementation size

From the repository root, using Python 3.10 or later (no dependencies):

```sh
python3 scripts/count_replay_effort.py
python3 scripts/count_replay_effort.py --format latex
python3 scripts/count_replay_effort.py --format json
```

The default output is the paper's six-category table. LaTeX output is an
includable table, not a standalone document. JSON gives the current Git revision
and an audit of every fenced region: file, line range, category, LoC, and handler
count. The script reads the working tree; uncommitted changes affect the result.
Use `--source /path/to/lean-crush` to inspect another annotated checkout.

## Scope and units

The `tacas-eval` branch starts at `tacas-evals` (`fc4191c`). At that revision,
the extension code is in `Crush/Solver/AletheBridge.lean`,
`Crush/Solver/AletheArithmetic.lean`, and `Crush/Solver/AletheReplay.lean`.

- **Handlers:** one `register_crush_replay rule` command or one declaration
  annotated with `@[crush_replay_rule ...]`. A command matching several solver
  rule names counts once. The count is detected from code, not specified in
  a fence. The option-gated trusted bitvector handler is included, as in the
  existing paper table; this is a source inventory, not a count of handlers
  exercised by the experiments.
- **Handler LoC:** nonblank, noncomment physical lines in handler regions,
  including attributes, signatures, registration syntax, and proof bodies.
- **Lemma LoC:** the existing table's name for supporting-code LoC. It includes
  helper definitions, metaprograms, structures, instances, and supporting lemmas
  and their proofs, not just theorem declarations. Each source line is counted
  once even if several handlers use it.
- **Total:** Handler LoC plus Lemma LoC.

Imports, namespace/open commands, the shared replay engine and protocol
dispatch, term-decoder registrations, tests, and standard-library lemmas are
outside this inventory. Shared-engine-only logic helpers remain outside the
fences. Supporting declarations included in the previous inventory remain
included even when also used by protocol dispatch. This reproduces the scope
of the paper's original counting script, rather than measuring the entire
reconstruction implementation or a minimal dependency closure.

## Fences

```lean
-- table4:begin arithmetic lemma arithmetic-support
private theorem exampleLemma : True := by
  trivial
-- table4:end arithmetic-support

-- table4:begin logic handler logical-rules
register_crush_replay rule low <<
  (refl ..) => by rfl
>>
-- table4:end logical-rules
```

Categories are `assumptions`, `logic`, `quantifiers`, `arithmetic`, `bitvectors`,
and `strings`. The kind is `handler` or `lemma`. Names must be unique within a
file. Regions may group adjacent declarations, but cannot nest or overlap.
Put markers on their own lines. Nested Lean comments and quoted literals are
handled when counting; the fences themselves do not count as LoC.

The script scans all Lean files under `Crush` and rejects rule registrations
outside handler fences, registrations inside lemma fences, malformed or
unclosed fences, unknown categories, duplicate names, and empty regions.
Helper dependencies are not inferred: when adding supporting code, include it
in an appropriate fence explicitly.

## Comparison with the existing paper table

At `tacas-evals`, the output is **55 handlers, 256 Handler LoC, 797 Lemma LoC,
1,053 total LoC**. The paper's table cites `16d19d7` and reports **56, 263, 797,
1,060**. That revision has an additional seven-line `bv_bitwise_slicing`
registration. Only the Bitvectors row changes: **13 / 72 / 337 / 409** at the
evaluation tag, versus **14 / 79 / 337 / 416** in the paper. The paper is not
modified by this script.
