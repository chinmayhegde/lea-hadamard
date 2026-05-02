"""Blueprint parser: extracts theorem DAG from leanblueprint-style LaTeX.

Reads .tex files containing leanblueprint annotations:
- `\\begin{theorem|lemma|definition|proposition|corollary}[title]`
- `\\label{kind:name}` — node id
- `\\lean{Name}` — canonical Lean declaration name
- `\\uses{a, b, ...}` — dependency labels
- `\\leanok` — node already formalized

Emits a JSON DAG: { "nodes": [ {label, kind, title, lean, uses, leanok, body} ], ... }

Regex-based; sufficient for well-formed blueprint TeX. Does not handle nested
environments or unusual TeX. For pathological input, swap in plasTeX (the
toolchain leanblueprint uses).

Usage:
    python3 blueprint_parser.py blueprint/src/sample.tex
    python3 blueprint_parser.py blueprint/src/  # parse a whole tree
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field, asdict
from pathlib import Path

# A blueprint "node": one theorem-like environment block.
ENVIRONMENTS = ("theorem", "lemma", "definition", "proposition", "corollary",
                "fact", "remark")

# Match `\begin{kind}[optional title]\n ... \end{kind}` non-greedy.
# Title is optional; we capture from `\begin{...}` to the matching `\end{...}`.
ENV_RE = re.compile(
    r"\\begin\{(?P<kind>" + "|".join(ENVIRONMENTS) + r")\}"
    r"(?:\[(?P<title>[^\]]*)\])?"
    r"(?P<body>.*?)"
    r"\\end\{(?P=kind)\}",
    re.DOTALL,
)
LABEL_RE = re.compile(r"\\label\{(?P<label>[^}]+)\}")
LEAN_RE = re.compile(r"\\lean\{(?P<lean>[^}]+)\}")
USES_RE = re.compile(r"\\uses\{(?P<uses>[^}]+)\}")
LEANOK_RE = re.compile(r"\\leanok\b")


@dataclass
class Node:
    label: str
    kind: str
    title: str
    lean: str | None
    uses: list[str] = field(default_factory=list)
    leanok: bool = False
    body: str = ""
    source_file: str = ""


def parse_block(kind: str, title: str | None, body: str, source_file: str) -> Node | None:
    label_m = LABEL_RE.search(body)
    if not label_m:
        return None  # blocks without labels aren't addressable
    lean_m = LEAN_RE.search(body)
    uses_m = USES_RE.search(body)
    uses = []
    if uses_m:
        # Split on commas, strip whitespace, drop empties.
        uses = [u.strip() for u in uses_m.group("uses").split(",") if u.strip()]
    return Node(
        label=label_m.group("label"),
        kind=kind,
        title=title or "",
        lean=lean_m.group("lean") if lean_m else None,
        uses=uses,
        leanok=bool(LEANOK_RE.search(body)),
        # Strip the meta-commands from the visible body.
        body=re.sub(r"\\(label|lean|uses|leanok)\b\s*\{?[^}]*\}?", "", body).strip(),
        source_file=source_file,
    )


def parse_file(path: Path) -> list[Node]:
    text = path.read_text()
    nodes = []
    for m in ENV_RE.finditer(text):
        node = parse_block(m.group("kind"), m.group("title"), m.group("body"), str(path))
        if node is not None:
            nodes.append(node)
    return nodes


def parse_tree(root: Path) -> list[Node]:
    if root.is_file():
        return parse_file(root)
    nodes = []
    for tex in sorted(root.rglob("*.tex")):
        nodes.extend(parse_file(tex))
    return nodes


def validate(nodes: list[Node]) -> list[str]:
    """Return list of validation problems (empty list = clean)."""
    problems = []
    labels = {n.label for n in nodes}
    for n in nodes:
        for dep in n.uses:
            if dep not in labels:
                problems.append(f"{n.label}: depends on unknown {dep!r}")
        if n.leanok and not n.lean:
            problems.append(f"{n.label}: \\leanok without \\lean{{...}}")
    return problems


def topological_layers(nodes: list[Node]) -> list[list[str]]:
    """Group nodes into dependency-respecting layers. Layer 0 has no deps;
    each subsequent layer depends only on prior layers."""
    by_label = {n.label: n for n in nodes}
    in_layer: dict[str, int] = {}
    remaining = set(by_label)
    layer = 0
    layers: list[list[str]] = []
    while remaining:
        ready = [
            lbl for lbl in remaining
            if all(dep not in remaining for dep in by_label[lbl].uses)
        ]
        if not ready:
            # Cycle detected; surface remaining as final "broken" layer.
            layers.append(sorted(remaining))
            break
        layers.append(sorted(ready))
        for lbl in ready:
            in_layer[lbl] = layer
            remaining.remove(lbl)
        layer += 1
    return layers


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("path", type=Path, help="blueprint .tex file or directory")
    ap.add_argument("--out", type=Path, default=None,
                    help="write JSON DAG to this path (default: stdout)")
    ap.add_argument("--summary", action="store_true",
                    help="print human summary instead of full JSON")
    args = ap.parse_args()

    nodes = parse_tree(args.path)
    problems = validate(nodes)
    layers = topological_layers(nodes)

    if args.summary:
        print(f"Found {len(nodes)} nodes across "
              f"{len({n.source_file for n in nodes})} files")
        kind_counts: dict[str, int] = {}
        for n in nodes:
            kind_counts[n.kind] = kind_counts.get(n.kind, 0) + 1
        for kind, count in sorted(kind_counts.items()):
            print(f"  {kind}: {count}")
        leanok = sum(1 for n in nodes if n.leanok)
        print(f"  \\leanok: {leanok}/{len(nodes)} ({100*leanok/max(len(nodes),1):.0f}%)")
        print(f"\nTopological layers: {len(layers)}")
        for i, layer in enumerate(layers):
            print(f"  layer {i} ({len(layer)} nodes): {', '.join(layer[:5])}"
                  + (" ..." if len(layer) > 5 else ""))
        if problems:
            print(f"\nValidation problems ({len(problems)}):")
            for p in problems[:10]:
                print(f"  {p}")
            if len(problems) > 10:
                print(f"  ... ({len(problems) - 10} more)")
        else:
            print("\nValidation: clean")
        return 0

    out = {
        "nodes": [asdict(n) for n in nodes],
        "layers": layers,
        "problems": problems,
    }
    if args.out:
        args.out.write_text(json.dumps(out, indent=2))
    else:
        json.dump(out, sys.stdout, indent=2)
        print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
