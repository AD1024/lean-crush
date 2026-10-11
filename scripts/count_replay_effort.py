#!/usr/bin/env python3
"""Reproduce Table 4 from explicit Lean source fences (standard library only).

Count nonblank, noncomment physical lines, including signatures and attributes.
One registration command or attributed declaration is one handler, even when it
matches several rules. The historical 'Lemma LoC' column includes helper code.
See scripts/replay-effort.md for the scope and fence format.
"""

import argparse
from dataclasses import asdict, dataclass
import json
from pathlib import Path
import re
import subprocess


CATEGORIES = {
    "assumptions": "Assumption normalization",
    "logic": "Logic and equality",
    "quantifiers": "Quantifiers",
    "arithmetic": "Arithmetic",
    "bitvectors": "Bitvectors",
    "strings": "Strings",
}
REGISTRATION = re.compile(r"^\s*(?:register_crush_replay\s+rule\b|@\[crush_replay_rule\b)")
BEGIN = re.compile(r"-- table4:begin (\S+) (handler|lemma) (\S+)\s*$")
END = re.compile(r"-- table4:end (\S+)\s*$")
CHAR = re.compile(r"'(?:[^'\\\n]|\\(?:u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2}|.))'")


def lex(source):
    """Return comment-free code, string-masked code, and real line comments.

    Preserve physical lines. Lean block comments nest; comment delimiters in
    strings/character literals are not comments. Mask literals separately so
    strings that look like registrations cannot inflate handler counts.
    """
    code, tokens, comments = [], [], {}
    i, depth, line = 0, 0, 1
    while i < len(source):
        pair, char = source[i:i + 2], source[i]
        if depth:
            if pair in ("/-", "-/"):
                depth += 1 if pair == "/-" else -1
                code.append("  ")
                tokens.append("  ")
                i += 2
            else:
                code.append("\n" if char == "\n" else " ")
                tokens.append("\n" if char == "\n" else " ")
                line += char == "\n"
                i += 1
        elif pair == "/-":
            depth = 1
            code.append("  ")
            tokens.append("  ")
            i += 2
        elif pair == "--":
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            comments[line] = source[i:end]
            code.append(" " * (end - i))
            tokens.append(" " * (end - i))
            i = end
        elif char == '"':
            start = i
            i += 1
            while i < len(source):
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise ValueError("Unterminated string")
            literal = source[start:i]
            code.append(literal)
            tokens.append(re.sub(r"[^\n]", " ", literal))
            line += literal.count("\n")
        elif char == "'" and (match := CHAR.match(source, i)):
            literal = match[0]
            code.append(literal)
            tokens.append(" " * len(literal))
            i = match.end()
        else:
            code.append(char)
            tokens.append(char)
            line += char == "\n"
            i += 1
    if depth:
        raise ValueError("Unterminated block comment")
    return "".join(code), "".join(tokens), comments


@dataclass
class Region:
    file: str
    name: str
    category: str
    kind: str
    start: int
    end: int
    loc: int
    handlers: int


def inventory(source, filename):
    code, tokens, comments = lex(source)
    lines, token_lines = code.splitlines(), tokens.splitlines()
    regions, names, current = [], set(), None
    for number, (line, token_line) in enumerate(zip(lines, token_lines), 1):
        comment = comments.get(number, "")
        if comment.startswith("-- table4:"):
            if line.strip():
                raise ValueError(f"{filename}:{number}: fence must occupy its own line")
            begin, end = BEGIN.fullmatch(comment), END.fullmatch(comment)
            if begin:
                category, kind, name = begin.groups()
                if current or name in names or category not in CATEGORIES:
                    raise ValueError(f"{filename}:{number}: nested, duplicate, or unknown fence")
                names.add(name)
                current = Region(filename, name, category, kind, number + 1, 0, 0, 0)
            elif end:
                if not current or current.name != end[1]:
                    raise ValueError(f"{filename}:{number}: mismatched end fence")
                current.end = number - 1
                if not current.loc or (current.kind == "handler" and not current.handlers):
                    raise ValueError(f"{filename}:{number}: empty code/handler region")
                regions.append(current)
                current = None
            else:
                raise ValueError(f"{filename}:{number}: malformed fence")
            continue
        registered = bool(REGISTRATION.match(token_line))
        if registered and (current is None or current.kind != "handler"):
            raise ValueError(f"{filename}:{number}: replay registration outside handler fence")
        if current:
            current.loc += bool(line.strip())
            current.handlers += registered
    if current:
        raise ValueError(f"{filename}: unclosed fence {current.name}")
    return regions


def collect(root):
    regions = []
    # Scan every Lean module so newly added rule registrations cannot silently
    # escape the inventory. Term-decoder registrations are outside Table 4.
    for path in sorted((root / "Crush").rglob("*.lean")):
        regions.extend(inventory(path.read_text(), str(path.relative_to(root))))
    if not regions:
        raise ValueError("No Table 4 fences found")
    return regions


def totals(regions):
    rows = {category: [0, 0, 0] for category in CATEGORIES}
    for region in regions:
        row = rows[region.category]
        row[0] += region.handlers
        row[1 if region.kind == "handler" else 2] += region.loc
    return rows


def render(rows, fmt):
    records = [(CATEGORIES[key], *values, values[1] + values[2]) for key, values in rows.items()]
    records.append(("Total", *(sum(row[i] for row in records) for i in range(1, 5))))
    headings = ("Category", "Handlers", "Handler LoC", "Lemma LoC", "Total")
    if fmt == "latex":
        lines = [r"\begin{table}[t!]", r"\centering",
                 r"\caption{Implementation size of built-in Alethe replay extensions.}",
                 r"\label{tab:eval-replay-effort}", r"\small",
                 r"\setlength{\tabcolsep}{5pt}", r"\renewcommand{\arraystretch}{1.1}",
                 r"\begin{tabular}{@{}lrrrr@{}}", r"\hline",
                 " & ".join(r"\textbf{" + h + "}" for h in headings) + r" \\", r"\hline"]
        for row in records:
            cells = [str(row[0]), *(f"{v:,}" for v in row[1:])]
            if row[0] == "Total":
                lines.append(r"\hline")
                cells = [r"\textbf{" + cell + "}" for cell in cells]
            lines.append(" & ".join(cells) + r" \\")
        return "\n".join(lines + [r"\hline", r"\end{tabular}", r"\end{table}"])
    lines = ["| " + " | ".join(headings) + " |", "|---|---:|---:|---:|---:|"]
    lines.extend("| " + " | ".join(map(str, row)) + " |" for row in records)
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--format", choices=("markdown", "latex", "json"), default="markdown")
    args = parser.parse_args()
    try:
        regions = collect(args.source)
    except ValueError as error:
        parser.error(str(error))
    rows = totals(regions)
    if args.format == "json":
        revision = subprocess.run(["git", "-C", str(args.source), "rev-parse", "HEAD"],
                                  capture_output=True, text=True, check=True).stdout.strip()
        print(json.dumps({"revision": revision, "totals": rows,
                          "regions": [asdict(region) for region in regions]}, indent=2))
    else:
        print(render(rows, args.format))


if __name__ == "__main__":
    main()
