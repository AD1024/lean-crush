#!/usr/bin/env python3
"""Audit and measure the same PLean scaffold across all benchmark backends.

Use --prepare-only to inspect evidence before running. Each completed file is
checkpointed; --resume never repeats a completed measurement. No Lake calls,
source edits, dependency resolution, or parallel measurements occur in a run.
"""
import argparse
from collections import Counter
import csv
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
import zipfile

ROOT = Path(__file__).resolve().parent.parent
LANES = ['crush-portfolio', 'crush-verify', 'crush-alethe', 'auto', 'grind', 'duper', 'smt-only']
FILES = ['ClockBound', 'Consensus', 'DistributedLock', 'LockServer', 'PingPongAuto',
         'PingPongTrivial', 'RingLeader', 'ShardedKV', 'TwoPhaseCommit']
COMMON = ['-DElab.async=false', '-DmaxHeartbeats=1000000', '-DmaxRecDepth=1000000',
          '-Dpverify.cache=false', '-Dpverify.profile=true', '-j1']
MEASURE_COLS = ['suite', 'lane', 'repeat', 'vc_key', 'status', 'category', 'milliseconds', 'message']
PROFILE_COLS = ['suite', 'lane', 'repeat', 'vc_key', 'declaration', 'goal_hash', 'outcome',
                'replay', 'detail', 'total_nanos', 'phases', 'metrics']


def digest(file):
    return hashlib.sha256(file.read_bytes()).hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def options(lane):
    if lane.startswith('crush-'):
        trust = 'trust' if lane == 'crush-verify' else 'reconstruct'
        replay = 'alethe' if lane == 'crush-alethe' else 'auto'
        return ['-Dpverify.benchmark.backend=crush', '-Dcrush.backend=cvc5', '-Dcrush.timeout=5',
                '-Dcrush.trust=' + trust, '-Dcrush.reconstruct=' + replay,
                '-Dcrush.inst.fuel=0', '-Dcrush.profile=true', '-Dcrush.profile.machine=true']
    if lane == 'auto':
        return ['-Dpverify.benchmark.backend=auto', '-Dloom.solver=cvc5',
                '-Dloom.solver.smt.timeout=5', '-Dloom.solver.smt.retryOnUnknown=false',
                '-Dauto.mono.ignoreNonQuasiHigherOrder=true']
    if lane == 'duper':
        return ['-Dpverify.benchmark.backend=duper', '-Dduper.maxSaturationTime=5']
    return ['-Dpverify.benchmark.backend=' + ('smt' if lane == 'smt-only' else lane)]


def read_tsv(path):
    with path.open() as stream:
        return list(csv.DictReader(stream, delimiter='\t'))


def expected_vc_keys(archive=None):
    """Read the shipped cohort without requiring an extracted local dataset."""
    archive = archive or ROOT / 'scripts/benchmark-data/eval-data.zip'
    with zipfile.ZipFile(archive) as source:
        with source.open('plean/measurements.tsv') as stream:
            rows = csv.DictReader(io.TextIOWrapper(stream, encoding='utf-8'), delimiter='\t')
            keys = {r['vc_key'] for r in rows}
    if len(keys) != 192:
        raise ValueError(f'expected 192 archived VC identities, found {len(keys)}')
    if {k.split('|', 1)[0] for k in keys} != {f'Examples/{stem}.lean' for stem in FILES}:
        raise ValueError('archived VC files differ from the pinned PLean corpus')
    return keys


def write_tsv(path, columns, rows):
    with path.open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=columns, delimiter='\t', lineterminator='\n')
        writer.writeheader()
        writer.writerows(rows)


def audit(config):
    modern, auto = (Path(config[k]['tree']) for k in ['modern', 'auto'])
    exceptions = {'PLean/Verify/BenchBackend.lean', 'PLean/Verify/CexParse.lean', 'PLean/Verify/CexModel.lean'}
    equal, different = {}, {}
    for source in sorted((modern / 'PLean').rglob('*.lean')):
        relative = str(source.relative_to(modern))
        a, b = digest(source), digest(auto / relative)
        if a == b:
            equal[relative] = a
        else:
            different[relative] = {'modern': a, 'auto': b}
    if set(different) != exceptions:
        raise ValueError(f'unexpected source differences: {set(different) ^ exceptions}')
    spec = importlib.util.spec_from_file_location('ablation', ROOT / 'scripts/prepare-plean-backend-only.py')
    ablation = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ablation)
    code = ablation.code_mask((modern / 'PLean/Verify/Tactic.lean').read_text())
    if set(re.findall(r'\b\w+\b', code)) & ablation.AUXILIARY:
        raise ValueError('auxiliary closing tactic remains in the shared scaffold')
    for scaffold in ['pverify_split_smt', 'pverify_split_ite_smt', 'pverify_structural_smt', 'pverify_frame_walk']:
        if scaffold not in code:
            raise ValueError(f'missing scaffold: {scaffold}')
    if digest(auto / 'Loom/SMT.lean') != digest(Path(config['original_auto_loom']) / 'Loom/SMT.lean'):
        raise ValueError('Loom source has been changed')
    for file in FILES:
        if digest(modern / f'Examples/{file}.lean') != digest(auto / f'Examples/{file}.lean'):
            raise ValueError(f'benchmark source differs: {file}')
    return {'policy': 'shared-backend-only-scaffolds-v2', 'identical_source_files': equal,
            'permitted_backend_and_diagnostic_adapters': different,
            'loom_smt_source_unchanged': True, 'common_lean_options': COMMON,
            'lanes': {lane: options(lane) for lane in LANES},
            'success_criterion': 'final PLean obligation proof contains no sorry; provenance reported separately',
            'timing': 'whole obligation tactic, including failed attempts; excludes VC-type logging',
            'version_exception': 'Auto uses Lean 4.24.0; the other backends use Lean 4.32.2'}


def prepare(config, out):
    out.mkdir(parents=True, exist_ok=False)
    evidence = audit(config)
    dump(out / 'scaffold-audit.json', evidence)
    dump(out / 'config.json', config)
    snapshots = out / 'sources'
    snapshots.mkdir()
    for variant in ['modern', 'auto']:
        tree = Path(config[variant]['tree'])
        for relative in [*evidence['identical_source_files'], *evidence['permitted_backend_and_diagnostic_adapters']]:
            target = snapshots / variant / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(tree / relative, target)
    generated = out / 'generated'
    generated.mkdir()
    for file in FILES:
        target = generated / f'{file}.lean'
        source = Path(config['modern']['tree']) / f'Examples/{file}.lean'
        env = dict(os.environ, PLEAN_LIBRARY_ONLY='true', MAX_HEARTBEATS='1000000')
        subprocess.run(['bash', '-c', 'source "$1"; write_benchmark_file "$2" "$3" grind',
                        'generate', str(ROOT / 'scripts/benchmark-plean.sh'), str(source), str(target)], env=env, check=True)
        # All lanes consume this same file. Backend options are supplied only
        # on the compiler command line; remove corpus-specific solver settings.
        text = re.sub(r'^set_option (?:crush|loom|auto|duper)\.[^\n]*\n', '', target.read_text(), flags=re.M)
        target.write_text(text)
    evidence['generated_source_sha256'] = {p.name: digest(p) for p in generated.glob('*.lean')}
    dump(out / 'scaffold-audit.json', evidence)
    print(json.dumps({'audit': str(out / 'scaffold-audit.json'),
                      'identical_lean_sources': len(evidence['identical_source_files']),
                      'tactic_sha256': evidence['identical_source_files']['PLean/Verify/Tactic.lean'],
                      'obligation_sha256': evidence['identical_source_files']['PLean/Verify/Obligation.lean']}, indent=2), flush=True)


def parse_log(text, lane, file, expected):
    times, provenance, categories, passed, types, profiles = {}, {}, {}, set(), {}, []
    for line in text.splitlines():
        if '[SMT]' in line:
            for name in expected:
                if re.search(r'(?<![\w.])' + re.escape(name) + r'(?![\w.])', line):
                    passed.add(name)
        if 'PLEAN_TIME\t' in line:
            _, name, nanos = line[line.index('PLEAN_TIME\t'):].split('\t')
            times[name] = int(nanos)
        if 'PLEAN_BENCH\t' in line:
            _, name, nanos, origin = line[line.index('PLEAN_BENCH\t'):].split('\t')
            provenance[name] = origin
        if 'PLEAN_DIAG\t' in line:
            _, name, category = line[line.index('PLEAN_DIAG\t'):].split('\t')
            categories[name] = category
        if 'PLEAN_VC_TYPE\t' in line:
            _, name, ty = line[line.index('PLEAN_VC_TYPE\t'):].split('\t', 2)
            types[name] = ty
        if 'CRUSH_PROFILE\t' in line:
            parts = line[line.index('CRUSH_PROFILE\t'):].split('\t')
            if len(parts) != 10:
                raise ValueError(f'bad profile record: {parts[:4]}')
            profiles.append(dict(zip(PROFILE_COLS, ['plean', lane, '1', file + '|' + parts[2], *parts[2:]])))
    if set(times) != set(expected):
        raise ValueError(f'{lane}/{file}: VC set differs: {set(times) ^ set(expected)}')
    rows = []
    for name in sorted(expected):
        origin = provenance.get(name, 'not-entered')
        success = name in passed
        if success != (origin in ['backend', 'scaffold']):
            raise ValueError(f'final outcome/provenance mismatch: {lane}/{name}/{origin}')
        rows.append(dict(zip(MEASURE_COLS, ['plean', lane, '1', file + '|' + name,
                    'pass' if success else 'fail', '-' if success else categories.get(name, 'tactic'),
                    f'{times[name]/1e6:.3f}', origin])))
    return {'rows': rows, 'profiles': profiles, 'vc_types': types}


def consolidate(out):
    results = [json.loads(p.read_text()) for p in sorted((out / 'checkpoints').glob('*.json'))]
    rows = [row for result in results for row in result['rows']]
    profiles = [row for result in results for row in result['profiles']]
    write_tsv(out / 'measurements.tsv', MEASURE_COLS, rows)
    write_tsv(out / 'profile-events.tsv', PROFILE_COLS, profiles)
    summary = []
    for lane in LANES:
        selected = [r for r in rows if r['lane'] == lane]
        counts = Counter(r['message'] for r in selected)
        summary.append({'lane': lane, 'attempted': len(selected),
                        'passed': sum(r['status'] == 'pass' for r in selected),
                        'backend_proofs': counts['backend'], 'scaffold_proofs': counts['scaffold']})
    write_tsv(out / 'summary.tsv', list(summary[0]), summary)
    return summary


def run(config, out):
    recorded = json.loads((out / 'scaffold-audit.json').read_text())
    current = audit(config)
    if any(current[k] != recorded[k] for k in current):
        raise ValueError('source/options changed after preflight audit')
    for name, expected_hash in recorded['generated_source_sha256'].items():
        if digest(out / 'generated' / name) != expected_hash:
            raise ValueError(f'generated source changed: {name}')
    keys = expected_vc_keys()
    for folder in ['checkpoints', 'logs']:
        (out / folder).mkdir(exist_ok=True)
    env = dict(os.environ)
    env.pop('PLEAN_BENCH_VCS', None)
    env['PATH'] = config['solver_bin_dir'] + os.pathsep + env['PATH']
    for lane in LANES:
        settings = config['auto' if lane == 'auto' else 'modern']
        env['LEAN_PATH'] = settings['lean_path']
        for stem in FILES:
            checkpoint = out / 'checkpoints' / f'{lane}-{stem}.json'
            if checkpoint.exists():
                print(f'Reusing completed {lane}/{stem}', flush=True)
                continue
            file = f'Examples/{stem}.lean'
            expected = {key.split('|', 1)[1] for key in keys if key.split('|', 1)[0] == file}
            command = [settings['lean'], *['--load-dynlib=' + p for p in settings.get('dynlibs', [])],
                       *COMMON, *options(lane), str(out / 'generated' / f'{stem}.lean')]
            log = out / 'logs' / f'{lane}-{stem}.log'
            print(f'Starting {lane}/{stem} ({len(expected)} VCs)', flush=True)
            start = time.monotonic()
            with log.open('w') as stream:
                process = subprocess.run(command, cwd=settings['tree'], env=env, stdout=stream, stderr=subprocess.STDOUT)
            elapsed = time.monotonic() - start
            if process.returncode:
                raise RuntimeError(f'Lean invocation failed ({process.returncode}); inspect {log}')
            result = parse_log(log.read_text(), lane, file, expected)
            result.update(command=command, wall_seconds=elapsed, log_sha256=digest(log))
            dump(checkpoint, result)
            consolidate(out)
            print(f'Finished {lane}/{stem}: {sum(r["status"] == "pass" for r in result["rows"])}/{len(expected)}; {elapsed:.1f}s', flush=True)
    summary = consolidate(out)
    if any(row['attempted'] != 192 for row in summary):
        raise RuntimeError('incomplete benchmark')
    dump(out / 'completion.json', {'status': 'complete', 'summary': summary})
    print(json.dumps(summary, indent=2), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--prepare-only', action='store_true')
    parser.add_argument('--resume', action='store_true')
    args = parser.parse_args()
    config = json.loads(args.config.read_text())
    out = args.out.resolve()
    if not args.resume:
        prepare(config, out)
    if not args.prepare_only:
        run(config, out)


if __name__ == '__main__':
    main()
