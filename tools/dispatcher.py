"""Blueprint-driven Lea dispatcher.

Reads a blueprint, finds nodes whose dependencies are all proven, and
dispatches Lea on each unproven node. Tracks per-node status in a JSON
file. Validates each completion with `lake build`.

Usage:
    python3 tools/dispatcher.py \\
        --blueprint blueprint/src/test_dispatch.tex \\
        --lake-root /home/chinmay-gcp/lea-hadamard \\
        --lea-root /home/chinmay-gcp/lea-prover \\
        --tracker runs/test_tracker.json \\
        --target-module LeaHadamard.Test \\
        --limit 1

The dispatcher itself never modifies Lean source. Lea's tools
(`write_file`, `edit_file`, `lean_check`) are the only writers.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from dataclasses import dataclass, field, asdict
from datetime import datetime, timezone
from pathlib import Path

# Local sibling import
sys.path.insert(0, str(Path(__file__).parent))
from blueprint_parser import Node, parse_tree


@dataclass
class TrackerEntry:
    label: str
    lean: str | None
    status: str = "pending"  # pending | in_progress | done | stuck
    attempts: int = 0
    cost_usd: float = 0.0
    last_error: str = ""
    started_at: str = ""
    completed_at: str = ""
    lean_proof_lines: int = 0
    target_file: str = ""


def load_tracker(path: Path, nodes: list[Node]) -> dict[str, TrackerEntry]:
    if path.exists():
        data = json.loads(path.read_text())
        return {k: TrackerEntry(**v) for k, v in data.items()}
    return {n.label: TrackerEntry(label=n.label, lean=n.lean) for n in nodes}


def save_tracker(tracker: dict[str, TrackerEntry], path: Path):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({k: asdict(v) for k, v in tracker.items()}, indent=2))


def find_ready(nodes: list[Node], tracker: dict[str, TrackerEntry]) -> list[Node]:
    """Nodes whose deps are all 'done' and which themselves are not 'done'."""
    ready = []
    for n in nodes:
        if tracker[n.label].status == "done":
            continue
        if all(tracker.get(d, TrackerEntry(d, None)).status == "done" for d in n.uses):
            ready.append(n)
    return ready


def dep_summaries(node: Node, by_label: dict[str, Node],
                  tracker: dict[str, TrackerEntry]) -> str:
    if not node.uses:
        return "(none — this is a leaf node; rely on Mathlib only)"
    lines = []
    for d in node.uses:
        dep = by_label.get(d)
        if dep and tracker.get(d, TrackerEntry(d, None)).status == "done" and dep.lean:
            body = re.sub(r"\s+", " ", dep.body or "").strip()
            lines.append(f"- `{dep.lean}`: {body[:300]}")
    return "\n".join(lines) if lines else "(deps listed but not yet resolved — should not happen)"


def lookup_mathlib_hint(name: str, mathlib_root: Path) -> str:
    """Look up a Mathlib lemma's signature by name. Returns '<name>: <signature>'
    or empty string if not found. Searches `theorem|lemma <name>` definitions."""
    proc = subprocess.run(
        ["grep", "-rEn", "--include=*.lean",
         rf"^(theorem|lemma)\s+{re.escape(name)}\b",
         str(mathlib_root)],
        capture_output=True, text=True, timeout=180,
    )
    if proc.returncode != 0 or not proc.stdout.strip():
        return ""
    line = proc.stdout.splitlines()[0]
    parts = line.split(":", 2)
    if len(parts) < 3:
        return f"- `{name}` (found, but couldn't parse signature)"
    file, _, sig = parts
    sig = sig.strip()
    return f"- `{name}` (in {Path(file).name}): `{sig[:280]}`"


def collect_hints(hint_names: list[str], mathlib_root: Path) -> str:
    if not hint_names:
        return "(none provided; use search_mathlib to find candidates)"
    lines = []
    for name in hint_names:
        h = lookup_mathlib_hint(name, mathlib_root)
        lines.append(h or f"- `{name}` (not found by grep — check spelling or import path)")
    return "\n".join(lines)


def build_prompt(node: Node, by_label: dict[str, Node],
                 tracker: dict[str, TrackerEntry],
                 lake_root: Path, target_path: Path,
                 hints_text: str = "(none provided)") -> str:
    deps_text = dep_summaries(node, by_label, tracker)
    body = re.sub(r"\s+", " ", node.body or "").strip()
    return f"""You are formalizing a research math result in Lean 4 (Lean v4.28.0 + Mathlib v4.28.0).

THEOREM TO PROVE:
{node.title or '(untitled)'}

STATEMENT (LaTeX, transliterate to Lean):
{body}

REQUIRED LEAN NAME (use this exact name):
{node.lean}

ALREADY-PROVEN PREREQUISITES YOU MAY USE:
{deps_text}

RELEVANT MATHLIB LEMMAS (curated hints — these are likely useful):
{hints_text}

OUTPUT FILE (absolute path):
{target_path}

INSTRUCTIONS:
1. Create the file at the absolute path above. Add appropriate Mathlib imports
   (e.g. `import Mathlib`).
2. Inside, declare the theorem with name `{node.lean}` and prove it.
3. The Lake project lives at `{lake_root}`. Use `lean_check` with that path
   (or its files) to verify your work, and `search_mathlib` for relevant lemmas.
4. The final proof must NOT contain `sorry` UNLESS the proof is genuinely
   beyond reach (see point 9). Stop as soon as `lean_check` returns clean.
5. Do not modify any file other than the OUTPUT FILE above.
6. Do not redefine any lemma that already exists in Mathlib under the same name.
7. Strongly prefer the curated Mathlib hints above over re-deriving from scratch.
   When in doubt, search via signature (`search_mathlib` with type-shaped query)
   rather than by name guessing.

8. ⚠ THEOREM SIGNATURE MUST MATCH THE BLUEPRINT STATEMENT.
   Hypotheses, conclusion, and types of bound variables must reflect what the
   LaTeX statement says. The following are CHEATS that we explicitly detect:

   (a) Adding a hypothesis whose body is the conclusion (or implies it). This
       turns the theorem into `∀ x, P x → P x` — provable by `:= h`. If you
       find yourself writing `:= hHC` or `exact hConclusion` as the entire
       proof, you are cheating; stop and add a `sorry` instead.

   (b) Lifting a real-valued bound to `ℝ≥0∞` or `ℝ≥0` and using `⊤` / `∞`
       as the bounding constant. The bound becomes vacuous. If the blueprint
       statement is in `ℝ`, the theorem must be in `ℝ`.

   (c) Generalising specific objects to universal hypotheses. If the statement
       talks about a specific `N` (e.g. count of partial Hadamard matrices),
       do NOT take `(N : ℕ → ℕ → ℝ)` as a generic hypothesis; either define
       `N` (or use a placeholder) or leave a `sorry`.

   (d) Choosing a structurally trivial codomain (e.g. `Bool` instead of `ℝ`,
       or `Unit` instead of a real type) to make the theorem hold by
       computation.

9. If the proof is genuinely beyond reach — missing Mathlib infrastructure,
   needs deep external machinery, or requires definitions you cannot
   reasonably build — leave a `sorry` plus a one-paragraph comment explaining
   exactly what's missing. This is the CORRECT failure mode. We will not
   penalise honest `sorry`-with-explanation; we WILL reject signature
   mutations that hide the failure.
"""


def run_lea(prompt: str, lea_root: Path, model: str | None,
            max_turns: int, lea_log_path: Path,
            wall_timeout: int = 14400) -> tuple[bool, str, float]:
    """Invoke `uv run lea` with the prompt, streaming output to the log file
    in real time so progress is visible during long runs. Kills the child
    process if `wall_timeout` seconds elapse."""
    cmd = ["uv", "run", "lea", "--max-turns", str(max_turns)]
    if model:
        cmd.extend(["-m", model])
    cmd.append(prompt)
    lea_log_path.parent.mkdir(parents=True, exist_ok=True)

    captured: list[str] = []
    t0 = time.time()
    with open(lea_log_path, "w") as logf:
        proc = subprocess.Popen(
            cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, cwd=str(lea_root), bufsize=1,
        )
        try:
            assert proc.stdout is not None
            while True:
                line = proc.stdout.readline()
                if line:
                    logf.write(line)
                    logf.flush()
                    captured.append(line)
                elif proc.poll() is not None:
                    break
                if time.time() - t0 > wall_timeout:
                    proc.kill()
                    msg = f"\n[dispatcher: killed after {wall_timeout}s wall timeout]\n"
                    logf.write(msg)
                    logf.flush()
                    captured.append(msg)
                    break
        finally:
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
    output = "".join(captured)
    cost = parse_lea_cost(output)
    success = parse_lea_success(output)
    return success, output, cost


def parse_lea_cost(output: str) -> float:
    """Extract Lea's reported cost from her summary line, e.g. '~$0.0898'."""
    m = re.search(r"~\$([0-9]*\.?[0-9]+)", output)
    return float(m.group(1)) if m else 0.0


def parse_lea_success(output: str) -> bool:
    """Heuristic: Lea exits with a 'done' message vs 'max turns reached'."""
    last = output.strip().split("\n")[-30:]
    last_text = "\n".join(last)
    if "max turns reached" in last_text.lower():
        return False
    if "Error:" in last_text and "max turns" in last_text:
        return False
    return True


def lake_build(lake_root: Path, lake_log_path: Path,
               target: str | None = None) -> tuple[bool, str]:
    """Run `lake build [target]` in the project root; return (success, log).

    Pass `target` (e.g. "LeaHadamard.Hadamard.Lem_xxx") to build only that
    module + its dependencies, avoiding cross-contamination from other
    in-flight files when multiple dispatchers run concurrently.
    """
    cmd = ["lake", "build"]
    if target:
        cmd.append(target)
    proc = subprocess.run(
        cmd, capture_output=True, text=True, cwd=str(lake_root), timeout=900,
    )
    output = (proc.stdout or "") + "\n" + (proc.stderr or "")
    lake_log_path.parent.mkdir(parents=True, exist_ok=True)
    lake_log_path.write_text(output)
    if proc.returncode != 0:
        return False, output
    if re.search(r"uses\s+[`']sorry[`']", output):
        return False, output + "\n[REJECTED: sorry detected]"
    if re.search(r"\berror:", output):
        return False, output
    return True, output


def label_to_path(label: str, target_module: str) -> Path:
    """LeaHadamard.Test + 'lem:add-zero-left' -> LeaHadamard/Test/Lem_add_zero_left.lean"""
    safe = re.sub(r"[^A-Za-z0-9]", "_", label)
    safe = safe[0].upper() + safe[1:] if safe else "X"
    return Path(target_module.replace(".", "/")) / f"{safe}.lean"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--blueprint", type=Path, required=True)
    ap.add_argument("--lake-root", type=Path, required=True)
    ap.add_argument("--lea-root", type=Path, required=True,
                    help="Path to lea-prover repo (cwd for `uv run lea`)")
    ap.add_argument("--tracker", type=Path, required=True)
    ap.add_argument("--target-module", default="LeaHadamard.Auto",
                    help="Lean namespace under which Lea writes proofs")
    ap.add_argument("--model", default=None,
                    help="Lea model override (default: Lea's default)")
    ap.add_argument("--max-turns", type=int, default=30)
    ap.add_argument("--limit", type=int, default=1,
                    help="Maximum nodes to dispatch this run")
    ap.add_argument("--logs-dir", type=Path, default=None,
                    help="Per-dispatch logs go here (default: alongside tracker)")
    ap.add_argument("--hints", type=str, default="",
                    help="Comma-separated Mathlib lemma names to surface as hints")
    ap.add_argument("--mathlib-root", type=Path,
                    default=Path("/home/chinmay-gcp/lea-hadamard/.lake/packages/mathlib"),
                    help="Path to local Mathlib for hint signature lookup")
    args = ap.parse_args()

    logs_dir = args.logs_dir or args.tracker.parent / "logs"

    nodes = parse_tree(args.blueprint)
    by_label = {n.label: n for n in nodes}
    tracker = load_tracker(args.tracker, nodes)

    print(f"Loaded {len(nodes)} blueprint nodes; "
          f"done={sum(1 for v in tracker.values() if v.status == 'done')}/"
          f"{len(tracker)}")

    ready = find_ready(nodes, tracker)
    if not ready:
        done = sum(1 for v in tracker.values() if v.status == "done")
        if done == len(tracker):
            print("All nodes done.")
        else:
            stuck = [k for k, v in tracker.items() if v.status == "stuck"]
            blocked = [k for k, v in tracker.items() if v.status == "pending"]
            print(f"Nothing ready. stuck={stuck} blocked={blocked}")
        return 0

    print(f"Ready to dispatch ({len(ready)}): {', '.join(n.label for n in ready)}")
    print(f"Will dispatch up to {args.limit} this run.")

    dispatched = 0
    for node in ready:
        if dispatched >= args.limit:
            break

        target_rel = label_to_path(node.label, args.target_module)
        target_abs = args.lake_root / target_rel
        hint_names = [h.strip() for h in args.hints.split(",") if h.strip()]
        hints_text = collect_hints(hint_names, args.mathlib_root)
        prompt = build_prompt(node, by_label, tracker, args.lake_root, target_abs,
                              hints_text=hints_text)

        print(f"\n=== {node.label} -> {node.lean} ===")
        print(f"  target: {target_rel}")
        tracker[node.label].status = "in_progress"
        tracker[node.label].started_at = datetime.now(timezone.utc).isoformat()
        tracker[node.label].attempts += 1
        tracker[node.label].target_file = str(target_rel)
        save_tracker(tracker, args.tracker)

        lea_log = logs_dir / f"{node.label.replace(':', '_')}.lea.log"
        ok_lea, _, cost = run_lea(prompt, args.lea_root, args.model,
                                  args.max_turns, lea_log)
        tracker[node.label].cost_usd += cost
        print(f"  Lea: success={ok_lea} cost=~${cost:.4f} log={lea_log}")

        # Validate with single-target lake build to avoid cross-contamination
        # from other concurrent dispatchers' in-flight files.
        lake_log = logs_dir / f"{node.label.replace(':', '_')}.lake.log"
        target_module = str(target_rel.with_suffix("")).replace("/", ".")
        ok_lake, lake_out = lake_build(args.lake_root, lake_log, target=target_module)
        if ok_lake and target_abs.exists():
            tracker[node.label].status = "done"
            tracker[node.label].completed_at = datetime.now(timezone.utc).isoformat()
            tracker[node.label].lean_proof_lines = len(target_abs.read_text().splitlines())
            print(f"  ✓ done ({tracker[node.label].lean_proof_lines} lines)")
        else:
            tracker[node.label].status = "stuck"
            tracker[node.label].last_error = lake_out[-800:]
            print(f"  ✗ stuck (build failed or file missing)")

        save_tracker(tracker, args.tracker)
        dispatched += 1

    print(f"\nDispatched {dispatched} nodes. Tracker: {args.tracker}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
