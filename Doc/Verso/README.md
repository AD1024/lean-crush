# lean-crush Verso manual

This is an optional documentation package. Its Verso dependencies are isolated
from the root `lean-crush` package.

The `Documentation` GitHub Actions workflow publishes the manual at
<https://ad1024.github.io/lean-crush/>.

From this directory:

```sh
lake update
lake build
lake exe crush-docs
python3 -m http.server 8000 --directory _out/html-multi
```

Then open <http://localhost:8000>. The Lean examples in the manual are
elaborated while the documentation is built, and examples that invoke `crush`
require Z3 on `PATH`.
