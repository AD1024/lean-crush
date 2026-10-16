# syntax=docker/dockerfile:1
# Evaluation environment only. Mount a clean tacas-evals checkout at runtime;
# neither benchmark results nor host build artifacts are copied into the image.
FROM ubuntu:24.04

SHELL ["/bin/bash", "-o", "pipefail", "-c"]

RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
      bash bsdextrautils build-essential ca-certificates clang cmake curl file \
      fonts-dejavu-core gawk git libatomic1 libc++-dev libc++abi-dev libgmp-dev \
      libgomp1 libssl-dev libuv1-dev librsvg2-bin ninja-build patch perl pkg-config \
      python3 python3-dev python3-venv rsync unzip util-linux xz-utils zip zstd \
    && rm -rf /var/lib/apt/lists/*

# Match the host's ownership for the writable checkout mounted below. Ubuntu
# images can already have UID/GID 1000, so reuse existing IDs when present.
ARG EVAL_UID=1000
ARG EVAL_GID=1000
RUN set -eux; \
    getent group "${EVAL_GID}" >/dev/null || groupadd --gid "${EVAL_GID}" evaluator; \
    getent passwd "${EVAL_UID}" >/dev/null || \
      useradd --create-home --uid "${EVAL_UID}" --gid "${EVAL_GID}" --shell /bin/bash evaluator; \
    mkdir -p /opt/elan /workspace/lean-crush; \
    chown "${EVAL_UID}:${EVAL_GID}" /opt/elan /workspace/lean-crush

ENV ELAN_HOME=/opt/elan \
    PATH=/opt/elan/bin:/opt/eval-python/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin \
    LANG=C.UTF-8 \
    LC_ALL=C.UTF-8 \
    MPLBACKEND=Agg \
    PYTHONUNBUFFERED=1 \
    GIT_TERMINAL_PROMPT=0 \
    CURATED_REPO_URL=https://github.com/AD1024/Lean-SMT-Benchmarks.git \
    CVC5_BIN=/usr/local/bin/cvc5 \
    Z3_BIN=/usr/local/bin/z3

# Public repositories must not require the evaluator's SSH keys. Restrict the
# safe-directory exception to the documented mount, not every Git repository.
RUN git config --system url."https://github.com/".insteadOf 'git@github.com:' \
    && git config --system --add url."https://github.com/".insteadOf 'ssh://git@github.com/' \
    && git config --system --add safe.directory /workspace/lean-crush

# Keep the toolchain selection tied to the repository's own pins.
COPY lean-toolchain /opt/lean-crush-env/lean-toolchain
COPY scripts/benchmark-data/plean-shared-lock.json /opt/lean-crush-env/plean-shared-lock.json

# SHA-256 values are the official GitHub release asset digests for elan 4.2.4,
# cvc5 1.3.4 and Z3 5.1.0. Update versions and checksums together.
# The external cvc5 executable is separate from lean-smt's pinned 1.3.2 FFI
# library, which the existing benchmark setup builds without modification.
ARG TARGETARCH
RUN set -eux; \
    case "${TARGETARCH:-$(dpkg --print-architecture)}" in \
      amd64) \
        elan_arch=x86_64; cvc5_arch=x86_64; z3_target=x64-glibc-2.39; \
        elan_sha=42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63; \
        cvc5_sha=dcdbfada0ce493ee98259c0816e0daafc561c223aadb3af298c2968e73ea39c6; \
        z3_sha=f47be8d27d3230e823bf1eeede2fe0abaca55bb78d0b59974370e6689a92284a ;; \
      arm64) \
        elan_arch=aarch64; cvc5_arch=arm64; z3_target=arm64-glibc-2.38; \
        elan_sha=05febd124d84ebf994b2e7479922a5650b1e950c17ae3bd1ddd776b65bb72bf9; \
        cvc5_sha=2a4c108367f20b0c8990abd6b9535a5d62e08908d471d4671c00734e408f85bc; \
        z3_sha=2832cfd43c6862fbaf78834b5f1e35d031b4a87e85456b696c1c6f609cd5609e ;; \
      *) printf 'Unsupported architecture: %s\n' "${TARGETARCH}" >&2; exit 1 ;; \
    esac; \
    python3 -c 'import json; p=json.load(open("/opt/lean-crush-env/plean-shared-lock.json")); assert p["external_cvc5"]["version"] == "1.3.4"'; \
    download_dir="$(mktemp -d)"; \
    trap 'rm -rf "$download_dir"' EXIT; \
    cd "$download_dir"; \
    curl -fL --retry 3 --connect-timeout 30 \
      "https://github.com/leanprover/elan/releases/download/v4.2.4/elan-${elan_arch}-unknown-linux-gnu.tar.gz" -o elan.tar.gz; \
    printf '%s  %s\n' "$elan_sha" elan.tar.gz | sha256sum -c -; \
    mkdir elan; tar -xzf elan.tar.gz -C elan; \
    install -m755 elan/elan-init /usr/local/bin/elan-init; \
    curl -fL --retry 3 --connect-timeout 30 \
      "https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.4/cvc5-Linux-${cvc5_arch}-static.zip" -o cvc5.zip; \
    printf '%s  %s\n' "$cvc5_sha" cvc5.zip | sha256sum -c -; \
    unzip -q cvc5.zip; \
    install -m755 "cvc5-Linux-${cvc5_arch}-static/bin/cvc5" /usr/local/bin/cvc5; \
    curl -fL --retry 3 --connect-timeout 30 \
      "https://github.com/Z3Prover/z3/releases/download/z3-5.1.0/z3-5.1.0-${z3_target}.zip" -o z3.zip; \
    printf '%s  %s\n' "$z3_sha" z3.zip | sha256sum -c -; \
    unzip -q z3.zip; \
    mkdir -p /opt/lean-crush-env/z3; \
    cp -a "z3-5.1.0-${z3_target}/bin" /opt/lean-crush-env/z3/; \
    ln -s /opt/lean-crush-env/z3/bin/z3 /usr/local/bin/z3; \
    cvc5 --version; z3 --version

# A virtual environment avoids Ubuntu's externally-managed Python restriction.
# librsvg2-bin above supplies rsvg-convert, used for the SVG figure PDFs.
RUN python3 -m venv /opt/eval-python \
    && /opt/eval-python/bin/python -m pip install --no-cache-dir 'matplotlib==3.11.2' \
    && /opt/eval-python/bin/python -m pip freeze > /opt/lean-crush-env/python-packages.txt

USER ${EVAL_UID}:${EVAL_GID}
RUN elan-init -y --no-modify-path --default-toolchain none

# Lean ships Clang's builtin headers under include/clang, but its Linux Clang
# looks in lib/clang/<version>/include. Lake prepends the toolchain's bin to
# PATH, so installing Ubuntu's clang alone does not fix lean-cvc5's size_t
# errors. Make each bundled compiler find its own headers, without mixing
# toolchain versions or relying on shell-local CPLUS_INCLUDE_PATH exports.
RUN python3 - <<'PY'
import json
import os
from pathlib import Path
import subprocess

root = Path('/opt/lean-crush-env')
pins = json.loads((root / 'plean-shared-lock.json').read_text())
versions = {(root / 'lean-toolchain').read_text().strip(), *pins['toolchains'].values()}
for version in sorted(versions):
    subprocess.run(['elan', 'toolchain', 'install', version], check=True)
    env = dict(os.environ, ELAN_TOOLCHAIN=version)
    lean = Path(subprocess.check_output(['elan', 'which', 'lean'], env=env, text=True).strip())
    clang = lean.parent / 'clang'
    builtin_headers = lean.parent.parent / 'include/clang'
    resource = Path(subprocess.check_output([clang, '-print-resource-dir'], text=True).strip())
    if not (resource / 'include').exists():
        if not (builtin_headers / 'stddef.h').is_file():
            raise RuntimeError(f'Missing bundled Clang headers: {builtin_headers}')
        resource.mkdir(parents=True, exist_ok=True)
        (resource / 'include').symlink_to(builtin_headers, target_is_directory=True)
    # Exercise libc++ and Lean's C API with the same compiler used by Lake.
    subprocess.run([clang, '-std=c++17', '-stdlib=libc++', '-fsyntax-only',
                    '-I', lean.parent.parent / 'include', '-x', 'c++', '-'],
                   input='#include <cstddef>\n#include <cstdint>\n#include <ostream>\n'
                         '#include <lean/lean.h>\nstatic_assert(sizeof(std::size_t) > 0);\n',
                   text=True, check=True)
PY

# Compile the pinned C++ binding during image construction, exercising the
# exact FFI target that failed during PLean setup. The benchmark setup builds
# the remaining Lean modules; this check runs no benchmarks and keeps no outputs.
RUN python3 - <<'PY'
import json
import os
from pathlib import Path
import subprocess
import tempfile

pins = json.loads(Path('/opt/lean-crush-env/plean-shared-lock.json').read_text())
env = dict(os.environ, ELAN_TOOLCHAIN=pins['toolchains']['modern'])
lean = Path(subprocess.check_output(['elan', 'which', 'lean'], env=env, text=True).strip())
env['PATH'] = str(lean.parent) + os.pathsep + env['PATH']
spec = pins['modern']['cvc5']
with tempfile.TemporaryDirectory(prefix='lean-cvc5-check-') as folder:
    def run(args, **kwargs):
        return subprocess.run(args, cwd=folder, env=env, check=True, **kwargs)
    run(['git', 'init', '--quiet'])
    run(['git', 'fetch', '--depth=1', spec['url'], spec['rev']])
    run(['git', 'checkout', '--detach', 'FETCH_HEAD'])
    run([lean.parent / 'lake', 'build', 'cvc5Enums', 'ffi.o'])
PY

# No default toolchain override: Lake/Lean use the mounted lean-toolchain file,
# and PLean explicitly selects its two locked compilers.
WORKDIR /workspace/lean-crush
CMD ["bash"]
