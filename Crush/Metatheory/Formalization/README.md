# LaTeX metatheory

`metatheory.tex` is a prose-and-mathematics presentation of the proof-facing
defunctionalization development. It uses the notation centralized in
`../Notation.lean` and footnotes definitions and results with their Lean source
files.

Build it from this directory with:

```sh
pdflatex metatheory.tex
pdflatex metatheory.tex
```

The second run resolves the table of contents and cross-references.
