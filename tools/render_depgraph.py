"""Render the blueprint dependency DAG to a self-contained SVG, with nodes
colored by formalization status (done / in-progress / pending / stuck).

No external graphviz / matplotlib dependency — pure Python emit. Layered
layout: layer index -> y, position-within-layer -> x. Edges drawn as
quadratic bezier from parent to child.

Usage:
    python3 tools/render_depgraph.py \\
        --blueprint /tmp/counting_hadamard/blueprint/src/ \\
        --tracker-glob 'runs/*tracker*.json' \\
        --out progress_reports/dep-graph-snapshots/$(date +%Y-%m-%d_%H%M).svg
"""

from __future__ import annotations

import argparse
import glob
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from blueprint_parser import parse_tree, topological_layers

STATUS_FILL = {
    "done": "#86efac",          # green-300
    "in_progress": "#fde047",   # yellow-300
    "stuck": "#fca5a5",          # red-300
    "pending": "#e5e7eb",        # gray-200
}
STATUS_STROKE = {
    "done": "#16a34a",
    "in_progress": "#ca8a04",
    "stuck": "#dc2626",
    "pending": "#9ca3af",
}


def collect_status(tracker_paths: list[Path]) -> dict[str, str]:
    """Merge all tracker files into a label -> status dict."""
    out: dict[str, str] = {}
    for p in tracker_paths:
        try:
            data = json.loads(p.read_text())
        except Exception:
            continue
        for label, entry in data.items():
            if entry.get("status") == "done":
                out[label] = "done"  # done wins over anything
            elif label not in out:
                out[label] = entry.get("status", "pending")
    return out


def layout(layers: list[list[str]], node_w: int = 200, node_h: int = 50,
           x_gap: int = 40, y_gap: int = 80) -> tuple[dict[str, tuple[int, int]], int, int]:
    """Compute (x, y) center for each node. Layer 0 at bottom (deepest deps),
    last layer at top (final theorem)."""
    max_in_layer = max(len(L) for L in layers)
    width = max_in_layer * (node_w + x_gap) + x_gap
    height = len(layers) * (node_h + y_gap) + y_gap
    pos: dict[str, tuple[int, int]] = {}
    for i, layer in enumerate(layers):
        y = height - (i + 1) * (node_h + y_gap)
        # center this layer's nodes horizontally
        layer_w = len(layer) * (node_w + x_gap) - x_gap
        x_start = (width - layer_w) // 2
        for j, lbl in enumerate(layer):
            x = x_start + j * (node_w + x_gap) + node_w // 2
            pos[lbl] = (x, y + node_h // 2)
    return pos, width, height


def render(nodes, layers, status_map, title: str, node_w=200, node_h=50) -> str:
    pos, width, height = layout(layers, node_w=node_w, node_h=node_h)
    by_label = {n.label: n for n in nodes}

    parts = [
        f'<?xml version="1.0" encoding="UTF-8"?>',
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height + 60}" '
        f'font-family="ui-sans-serif, system-ui, sans-serif">',
        # Definitions for arrowhead
        '<defs><marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" '
        'markerWidth="6" markerHeight="6" orient="auto">'
        '<path d="M0,0 L10,5 L0,10 Z" fill="#6b7280"/></marker></defs>',
        # Title
        f'<text x="{width // 2}" y="30" text-anchor="middle" font-size="20" '
        f'font-weight="bold">{title}</text>',
    ]

    # Edges (drawn first so nodes overlay)
    for n in nodes:
        if n.label not in pos:
            continue
        for dep in n.uses:
            if dep not in pos:
                continue
            x1, y1 = pos[dep]   # parent (lower layer)
            x2, y2 = pos[n.label]
            # quadratic bezier through the midpoint, slightly bowed
            mx = (x1 + x2) // 2
            my = (y1 + y2) // 2 - 20
            parts.append(
                f'<path d="M{x1},{y1 - node_h // 2} Q{mx},{my} {x2},{y2 + node_h // 2}" '
                f'stroke="#6b7280" stroke-width="1.2" fill="none" marker-end="url(#arrow)"/>'
            )

    # Nodes
    for label, (cx, cy) in pos.items():
        st = status_map.get(label, "pending")
        fill = STATUS_FILL[st]
        stroke = STATUS_STROKE[st]
        n = by_label.get(label)
        kind = n.kind[:3] if n else "?"
        title_attr = (n.title or label) if n else label
        # Trim label for display
        disp = label.replace("lem:", "").replace("thm:", "").replace("prop:", "") \
                    .replace("fact:", "").replace("cor:", "")
        parts.append(
            f'<g><title>{title_attr} ({st})</title>'
            f'<rect x="{cx - node_w // 2}" y="{cy - node_h // 2}" '
            f'width="{node_w}" height="{node_h}" rx="6" '
            f'fill="{fill}" stroke="{stroke}" stroke-width="1.5"/>'
            f'<text x="{cx}" y="{cy - 4}" text-anchor="middle" font-size="11">{disp}</text>'
            f'<text x="{cx}" y="{cy + 14}" text-anchor="middle" font-size="9" '
            f'fill="#6b7280">{kind} · {st}</text>'
            f'</g>'
        )

    # Legend
    legend_y = height + 25
    legend_x = 20
    for st, lab in [("done", "done"), ("in_progress", "in progress"),
                    ("stuck", "stuck"), ("pending", "pending")]:
        parts.append(
            f'<rect x="{legend_x}" y="{legend_y - 10}" width="14" height="14" rx="3" '
            f'fill="{STATUS_FILL[st]}" stroke="{STATUS_STROKE[st]}"/>'
            f'<text x="{legend_x + 22}" y="{legend_y + 2}" font-size="11">{lab}</text>'
        )
        legend_x += 110
    parts.append('</svg>')
    return "\n".join(parts)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--blueprint", type=Path, required=True)
    ap.add_argument("--tracker-glob", type=str, default="",
                    help="glob pattern for tracker JSON files")
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--title", default=None)
    args = ap.parse_args()

    nodes = parse_tree(args.blueprint)
    if not nodes:
        print("No blueprint nodes found.", file=sys.stderr)
        return 1

    layers = topological_layers(nodes)
    tracker_paths = [Path(p) for p in glob.glob(args.tracker_glob)] if args.tracker_glob else []
    status = collect_status(tracker_paths)

    title = args.title or (
        f"Davis blueprint dependency graph — "
        f"{datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M UTC')}"
    )
    svg = render(nodes, layers, status, title)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(svg)

    done = sum(1 for v in status.values() if v == "done")
    print(f"Wrote {args.out} ({len(nodes)} nodes, {done} done)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
