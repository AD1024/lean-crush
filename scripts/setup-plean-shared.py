#!/usr/bin/env python3
"""Provision the pinned PLean environment without measuring any VCs.

All Git checkouts and build outputs belong to --out. No developer checkout,
package symlink, moving branch, or pre-existing build cache is required.
Mathlib's transitive revisions come from its pinned committed manifest.
The existing source generator supplies the unchanged shared proof scaffold.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import urllib.request
import zipfile

HERE = Path(__file__).resolve().parent
LOCK = HERE / 'benchmark-data/plean-shared-lock.json'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def source_hash(root):
    hashes = {str(p.relative_to(root)): digest(p) for p in sorted(root.rglob('*.lean'))
              if '.lake' not in p.relative_to(root).parts}
    return hashlib.sha256(json.dumps(hashes, sort_keys=True).encode()).hexdigest()


def clean_env():
    env = dict(os.environ)
    for name in ['LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'ELAN_TOOLCHAIN',
                 'LAKE_HOME', 'PLEAN_BENCH_VCS']:
        env.pop(name, None)
    env['GIT_TERMINAL_PROMPT'] = '0'
    # macOS tar warns about unsupported inherited locales; older Mathlib cache
    # tools treat any stderr from tar as a fatal extraction error.
    env['LANG'] = 'C'
    env['LC_ALL'] = 'C'
    return env


class Setup:
    def __init__(self, root, lock, require_cache=False):
        self.root, self.lock, self.require_cache = root.resolve(), lock, require_cache
        self.env = clean_env()
        # Keep package caches inside this environment, including on a cold build.
        self.env['MATHLIB_CACHE_DIR'] = str(self.root / 'cache/mathlib')
        self.env['XDG_CACHE_HOME'] = str(self.root / 'cache')
        self.env['LAKE_CACHE_DIR'] = str(self.root / 'cache/lake')
        self.log = root / 'setup.log'
        self.pins = {}

    def run(self, command, cwd=None, env=None, check=True, input=None):
        command = list(map(str, command))
        print('+', ' '.join(command), flush=True)
        with self.log.open('a') as stream:
            stream.write('\n+ ' + ' '.join(command) + '\n')
            stream.flush()
            p = subprocess.run(command, cwd=cwd or self.root, env=env or self.env,
                               input=input, text=True, stdout=stream, stderr=subprocess.STDOUT)
        if check and p.returncode:
            raise RuntimeError(f'Command failed ({p.returncode}); see {self.log}: {command}')
        return p.returncode

    def output(self, command, cwd=None, env=None):
        return subprocess.check_output(list(map(str, command)), cwd=cwd or self.root,
                                       env=env or self.env, text=True).strip()

    def checkout(self, name, spec, path):
        require(re.fullmatch(r'[0-9a-f]{40}', spec['rev']), f'Unpinned revision: {name}')
        require(not path.is_symlink(), f'Refusing a package symlink: {path}')
        require(path.resolve().is_relative_to(self.root), f'Checkout outside setup directory: {path}')
        if not path.exists():
            path.mkdir(parents=True)
            self.run(['git', 'init', '--quiet', path])
            self.run(['git', '-C', path, 'remote', 'add', 'origin', spec['url']])
        require((path / '.git').is_dir(), f'Not an owned Git checkout: {path}')
        require(not (path / '.git/objects/info/alternates').exists(), f'Refusing borrowed Git objects: {path}')
        origin = self.output(['git', '-C', path, 'remote', 'get-url', 'origin'])
        require(origin == spec['url'], f'Origin differs for {name}: {origin}')
        if self.run(['git', '-C', path, 'cat-file', '-e', spec['rev'] + '^{commit}'], check=False):
            self.run(['git', '-C', path, 'fetch', '--depth=1', 'origin', spec['rev']])
        head = subprocess.run(['git', '-C', str(path), 'rev-parse', '--verify', 'HEAD'],
                              stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
        if head.returncode:
            self.run(['git', '-C', path, 'checkout', '--detach', spec['rev']])
        else:
            require(head.stdout.strip() == spec['rev'], f'Refusing to replace a different checkout: {path}')
        self.pins[str(path)] = spec
        self.verify_checkout(path, spec)
        return path

    def verify_checkout(self, path, spec):
        require(not path.is_symlink(), f'Package became a symlink: {path}')
        require(self.output(['git', '-C', path, 'rev-parse', 'HEAD']) == spec['rev'], f'Revision changed: {path}')
        require(not self.output(['git', '-C', path, 'status', '--porcelain', '--untracked-files=no']),
                f'Tracked source changes in dependency: {path}')
        extras = self.output(['git', '-C', path, 'ls-files', '--others', '--exclude-standard']).splitlines()
        require(not any(p.endswith('.lean') for p in extras), f'Untracked Lean sources in dependency: {path}')

    def toolchain(self, variant):
        name = self.lock['toolchains'][variant]
        env = dict(self.env, ELAN_TOOLCHAIN=name)
        # Some elan versions report an error when installing an existing toolchain.
        # Resolve the explicitly pinned compiler first, installing only if absent.
        try:
            self.output(['elan', 'which', 'lean'], env=env)
        except subprocess.CalledProcessError:
            self.run(['elan', 'toolchain', 'install', name])
        lean = Path(self.output(['elan', 'which', 'lean'], env=env)).resolve()
        version = self.output([lean, '--version'])
        require(f'version {name.rsplit(":v", 1)[1]},' in version, f'Unexpected Lean compiler: {version}')
        require(self.lock['compiler_commits'][variant] in version, f'Unexpected Lean compiler commit: {version}')
        env['PATH'] = str(lean.parent) + os.pathsep + env.get('PATH', '')
        if platform.system() == 'Darwin':
            # Lean's bundled clang needs the SDK's libc++ headers for native FFI.
            sdk = Path(self.output(['xcrun', '--show-sdk-path']))
            headers = sdk / 'usr/include/c++/v1'
            require((headers / 'cstdint').exists(), f'C++ SDK headers missing: {headers}')
            env['SDKROOT'] = str(sdk)
            builtin_headers = lean.parent.parent / 'include/clang'
            env['CPLUS_INCLUDE_PATH'] = os.pathsep.join(map(str, [headers, builtin_headers]))
        return lean, env

    def mathlib(self, variant, root, env):
        # The committed manifest is the lock for the entire Mathlib closure.
        manifest = json.loads((root / 'lake-manifest.json').read_text())
        deps = []
        for spec in manifest['packages']:
            require(spec['type'] == 'git' and not spec.get('subDir'), 'Unsupported Mathlib dependency')
            name = spec['name']
            require(re.fullmatch(r'[A-Za-z0-9_-]+', name), f'Invalid package name: {name}')
            dependency = self.checkout(f'{variant}/{name}', spec, root / '.lake/packages' / name)
            deps.append(dependency)
            if name == 'proofwidgets' and spec.get('inputRev', '').startswith('v'):
                # Older Mathlib cache clients ask Lake for the cloud release.
                # A shallow commit checkout omits the tag Lake needs to find it.
                self.release_tag(dependency, spec)
        lake = str(Path(env['PATH'].split(os.pathsep)[0]) / 'lake')
        missed = self.run([lake, 'exe', 'cache', 'get'], cwd=root, env=env, check=False)
        if missed:
            require(not self.require_cache, f'Mathlib cache unavailable for {variant}; see {self.log}')
            self.run([lake, 'build', 'Mathlib'], cwd=root, env=env)
        for dependency in [root, *deps]:
            self.verify_checkout(dependency, self.pins[str(dependency)])
        return deps

    def release_tag(self, path, spec):
        tag = spec['inputRev']
        require(re.fullmatch(r'v[0-9][A-Za-z0-9.+_-]*', tag), f'Invalid release tag: {tag}')
        ref = 'refs/tags/' + tag
        self.run(['git', '-C', path, 'fetch', '--depth=1', 'origin', ref + ':' + ref])
        require(self.output(['git', '-C', path, 'rev-parse', ref + '^{commit}']) == spec['rev'],
                f'Release tag does not match pinned commit: {tag}')

    def solver(self):
        spec = self.lock['external_cvc5']
        systems = {'Darwin': 'macOS', 'Linux': 'Linux'}
        machines = {'arm64': 'arm64', 'aarch64': 'arm64', 'x86_64': 'x86_64'}
        require(platform.system() in systems and platform.machine() in machines,
                'Automatic solver setup supports macOS/Linux on arm64/x86_64')
        target = f'{systems[platform.system()]}-{machines[platform.machine()]}-static'
        stem = 'cvc5-' + target
        binary = self.root / 'solvers/bin/cvc5'
        if not binary.exists():
            binary.parent.mkdir(parents=True, exist_ok=True)
            if candidate := os.environ.get('CVC5_BIN'):
                path = shutil.which(candidate) or candidate
                shutil.copy2(path, binary)
            else:
                archive = self.root / (stem + '.zip')
                url = f'{spec["release_url"]}/{stem}.zip'
                print('Downloading', url, flush=True)
                urllib.request.urlretrieve(url, archive)
                with zipfile.ZipFile(archive) as source:
                    binary.write_bytes(source.read(f'{stem}/bin/cvc5'))
            binary.chmod(0o755)
        if expected := spec['binary_sha256'].get(target):
            require(digest(binary) == expected, f'Solver checksum mismatch: {binary}')
        version = self.output([binary, '--version']).splitlines()[0]
        require(version.startswith('cvc5 ' + spec['version'] + ' '), f'Wrong solver: {version}')
        return binary

    def provision(self):
        p = self.checkout('PLean', self.lock['PLean'], self.root / 'sources/P')
        self.run(['git', '-C', p, 'fetch', '--depth=1', 'origin', self.lock['auto_adapter_rev']])
        packages, settings, compilers = {}, {}, {}
        for variant in ['modern', 'auto']:
            packages[variant] = {name: self.checkout(f'{variant}/{name}', spec,
                                    self.root / 'dependencies' / variant / name)
                                 for name, spec in self.lock[variant].items()}
            tree = self.root / ('modern' if variant == 'modern' else 'auto-compat')
            if not tree.exists():
                command = [sys.executable, HERE / 'prepare-plean-shared.py', '--repo', p,
                           '--out', tree, '--variant', variant]
                if variant == 'auto':
                    command += ['--auto-loom', packages[variant]['Loom']]
                self.run(command)
            require(source_hash(tree) == self.lock['source_bundle_sha256'][variant],
                    f'Generated {variant} sources differ from the measured scaffold')
            lean, env = self.toolchain(variant)
            compilers[variant] = (lean, env)
            settings[variant] = {'tree': str(tree), 'lean': str(lean)}
        solver = self.solver()
        # Loom's unmodified Auto adapter resolves this path at elaboration.
        auto_binary = Path(settings['auto']['tree']) / '.lake/build/cvc5'
        auto_binary.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(solver, auto_binary)
        for variant in ['modern', 'auto']:
            lean, env = compilers[variant]
            pkgs = packages[variant]
            mathlib_deps = self.mathlib(variant, pkgs['mathlib'], env)
            # Auto's metaprogramming derives instances through native plugins.
            # Its own Lake setup must build/load those plugins consistently.
            self.run([lean.parent / 'lake', 'build', 'Auto'], cwd=pkgs['auto'], env=env)
            dynlibs = []
            if variant == 'modern':
                self.run([lean.parent / 'lake', 'build', 'cvc5:shared'], cwd=pkgs['cvc5'], env=env)
                suffix = '.dylib' if platform.system() == 'Darwin' else '.so'
                library = pkgs['cvc5'] / ('.lake/build/lib/libcvc5_cvc5' + suffix)
                require(library.exists(), f'Native cvc5 binding missing: {library}')
                dynlibs = [str(library)]
                ordered = [pkgs[k] for k in ['Duper', 'Smt', 'auto', 'cvc5', 'Loom', 'Crush']]
            else:
                ordered = [pkgs['Loom'], pkgs['auto']]
            tree = Path(settings[variant]['tree'])
            roots = [tree, *ordered, pkgs['mathlib'], *mathlib_deps]
            command = [sys.executable, HERE / 'build-lean-direct.py', '--lean', lean]
            if variant == 'auto':
                # The unchanged compatibility adapter overrides Loom.SMT.
                # Lean 4.24 resolves a namespace from the first matching root,
                # so its Loom modules must share one compiled module tree.
                command += ['--output-dir', tree / '.lake/build/lib/lean']
            native_packages = [pkgs['auto'], *([pkgs['cvc5']] if variant == 'modern' else [])]
            for root in [tree, *(r for r in ordered if r not in native_packages)]:
                command += ['--root', root]
            for root in [pkgs['mathlib'], *mathlib_deps, *native_packages]:
                command += ['--dependency', root]
            for library in dynlibs:
                command += ['--load-dynlib', library]
            self.run([*command, 'PLean'], env=env)
            settings[variant]['lean_path'] = os.pathsep.join(str(r / '.lake/build/lib/lean') for r in roots)
            if dynlibs:
                settings[variant]['dynlibs'] = dynlibs
            probe = 'import PLean\n'
            if variant == 'modern':
                probe += f'''#eval do
  let version ← cvc5.Env.runIO do
    let tm ← cvc5.TermManager.new
    let solver ← cvc5.Solver.new tm
    solver.getVersion
  unless version.startsWith "{self.lock['embedded_cvc5_version']}" do
    throw (IO.userError s!"Wrong embedded cvc5: {{version}}")
  IO.println s!"Embedded cvc5: {{version}}"
'''
            self.run([lean, *['--load-dynlib=' + d for d in dynlibs], '--stdin'],
                     cwd=tree, env=dict(env, LEAN_PATH=settings[variant]['lean_path']), input=probe)
            require(source_hash(tree) == self.lock['source_bundle_sha256'][variant], 'Build altered scaffold sources')
        for path, spec in self.pins.items():
            self.verify_checkout(Path(path), spec)
        config = {'original_auto_loom': str(packages['auto']['Loom']),
                  'solver_bin_dir': str(solver.parent), **settings,
                  'versions': {'PLean': self.lock['PLean']['rev'],
                               'modern': {k: v['rev'] for k, v in self.lock['modern'].items()},
                               'auto': {k: v['rev'] for k, v in self.lock['auto'].items()},
                               'external_cvc5': self.lock['external_cvc5']['version'],
                               'embedded_cvc5': self.lock['embedded_cvc5_version']}}
        save(self.root / 'provisioning-manifest.json', {
            'lock': self.lock, 'config': config, 'source_pins': self.pins,
            'source_bundle_sha256': {v: source_hash(Path(settings[v]['tree'])) for v in settings},
            'binary_sha256': {str(p): digest(p) for p in [solver, auto_binary,
                *(Path(s['lean']) for s in settings.values()),
                *(Path(d) for s in settings.values() for d in s.get('dynlibs', []))]},
            'system': platform.platform(), 'validation': 'imports and native solver version checked; no VCs measured'})
        save(self.root / 'run-config.json', config)
        return config

    def verify_ready(self):
        manifest = json.loads((self.root / 'provisioning-manifest.json').read_text())
        config = json.loads((self.root / 'run-config.json').read_text())
        require(manifest['lock'] == self.lock and manifest['config'] == config, 'Provisioned configuration changed')
        for variant in ['modern', 'auto']:
            require(source_hash(Path(config[variant]['tree'])) == self.lock['source_bundle_sha256'][variant],
                    f'{variant} scaffold sources changed')
        for path, spec in manifest['source_pins'].items():
            self.verify_checkout(Path(path), spec)
        for path, expected in manifest['binary_sha256'].items():
            require(digest(Path(path)) == expected, f'Compiler or solver binary changed: {path}')
        return config


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--require-cache', action='store_true')
    args = parser.parse_args()
    require(not args.out.is_symlink(), 'Refusing a symlink setup directory')
    root = args.out.resolve()
    identity = {'lock_sha256': digest(LOCK), 'scripts_sha256': {name: digest(HERE / name) for name in
                ['setup-plean-shared.py', 'prepare-plean-shared.py', 'prepare-plean-backend-only.py', 'build-lean-direct.py']}}
    if root.exists():
        marker = root / 'setup-identity.json'
        require(marker.exists(), f'Refusing to modify an environment not created by this setup: {root}')
        require(json.loads(marker.read_text()) == identity, 'Setup inputs changed; choose a fresh output directory')
    else:
        root.mkdir(parents=True)
        save(root / 'setup-identity.json', identity)
    with (root / 'setup.lock').open('a') as guard:
        fcntl.flock(guard, fcntl.LOCK_EX | fcntl.LOCK_NB)
        setup = Setup(root, json.loads(LOCK.read_text()), args.require_cache)
        if (root / 'run-config.json').exists():
            setup.verify_ready()
        else:
            setup.provision()
    print(f'Prepared {root / "run-config.json"}')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, RuntimeError, BlockingIOError) as error:
        sys.exit(str(error))
