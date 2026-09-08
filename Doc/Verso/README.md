# lean-crush Verso manual

This is an optional documentation package. Its Verso dependencies are isolated
from the root `lean-crush` package.

The `Documentation` GitHub Actions workflow publishes the manual at
<https://ad1024.github.io/lean-crush/>.

From this directory:

```sh
lake build
lake exe crush-docs
python3 -m http.server 8000 --directory _out/html-multi
```

Then open <http://localhost:8000>. The build uses the pinned Lean and Verso
dependencies. Run `lake update` only when intentionally updating those dependencies.

The Lean examples are checked during the build and require both Z3 and cvc5 on
`PATH`; CI uses Z3 5.1.0 and cvc5 1.3.4. Edit the sources under `CrushManual/`,
then run both build and render before publishing. The HTML under `_out/` is
generated output.
