#!/usr/bin/env python3
"""Build imports directly with Lean, without modifying Lake dependency trees."""
import argparse
import os
from pathlib import Path
import re
import subprocess


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean', required=True)
    p.add_argument('--root', action='append', type=Path, required=True)
    p.add_argument('--dependency', action='append', type=Path, default=[])
    p.add_argument('--output-dir', type=Path,
                   help='Use one module tree for roots sharing a Lean namespace')
    p.add_argument('--load-dynlib', action='append', default=[])
    p.add_argument('modules', nargs='+')
    args = p.parse_args()
    roots = [x.resolve() for x in args.root]
    builds = [x / '.lake/build/lib/lean' for x in roots + args.dependency]
    shared_output = args.output_dir.resolve() if args.output_dir else None
    if shared_output:
        builds.insert(0, shared_output)
    env = dict(os.environ, LEAN_PATH=':'.join(map(str, dict.fromkeys(builds))))
    seen, changed = set(), set()

    def build(module):
        if module in seen:
            return
        seen.add(module)
        relative = Path(*module.split('.')).with_suffix('.lean')
        owner = next((r for r in roots if (r / relative).exists()), None)
        if owner is None:
            return
        source = owner / relative
        imports = re.findall(r'^(?:(?:public|meta)\s+)*import\s+([\w.\x27]+)', source.read_text(), re.M)
        for dependency in imports:
            build(dependency)
        output_root = shared_output or (owner / '.lake/build/lib/lean')
        output = output_root / relative.with_suffix('.olean')
        if output.exists() and output.stat().st_mtime > source.stat().st_mtime and not any(d in changed for d in imports):
            return
        output.parent.mkdir(parents=True, exist_ok=True)
        print('BUILD', module, flush=True)
        subprocess.run([args.lean, *['--load-dynlib=' + x for x in args.load_dynlib],
                        '-o', str(output), str(source)], cwd=owner, env=env, check=True)
        changed.add(module)

    for module in args.modules:
        build(module)


if __name__ == '__main__':
    main()
