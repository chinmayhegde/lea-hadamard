"""Auto-discovery of Mathlib hint candidates for a given lemma statement.

Given a statement (string of LaTeX or English math), extract distinguishing
keywords and grep Mathlib for theorem/lemma names that contain those keywords.
Score by overlap and return the top-N candidates.

Not a substitute for genuine signature-based search (loogle / `apply?`), but
significantly better than no hints at all when the statement uses recognizable
math vocabulary.

Usage:
    python3 tools/mathlib_hints.py "the integral of x^n exp(-x^2)" --top 10
"""

from __future__ import annotations

import argparse
import re
import subprocess
from collections import Counter
from pathlib import Path

# Common math vocabulary -> Mathlib naming conventions.
# Extending this dictionary improves hit rate.
KEYWORD_MAP = {
    "integral": ["integral"],
    "integrate": ["integral"],
    "expectation": ["integral", "expect"],
    "gaussian": ["gaussian", "exp_neg.*sq"],
    "exponential": ["exp"],
    "exp": ["exp"],
    "norm": ["norm", "abs"],
    "moment": ["moment", "rpow_mul_exp"],
    "rpow": ["rpow"],
    "power": ["pow", "rpow"],
    "polynomial": ["polynomial"],
    "fourier": ["fourier"],
    "characteristic function": ["charFun", "characteristic"],
    "matrix": ["matrix"],
    "determinant": ["det"],
    "trace": ["trace"],
    "eigenvalue": ["eigenvalue", "spectrum"],
    "positive definite": ["posDef", "PosSemidef"],
    "symmetric": ["symm", "isSymm"],
    "complex": ["complex", "Complex"],
    "real": ["Real"],
    "torus": ["torus", "UnitAddCircle"],
    "lattice": ["lattice"],
    "hadamard": ["hadamard"],
    "rademacher": ["rademacher", "uniformOn"],
    "hypercontractive": ["hypercontract", "Bonami"],
    "cosine": ["cos"],
    "sine": ["sin"],
    "constant": ["const"],
    "change of variable": ["integral_comp"],
    "scaling": ["integral_comp_mul"],
    "absolute value": ["abs"],
    "inequality": ["le", "lt"],
    "bound": ["le", "bound"],
    "convergence": ["tendsto", "Filter"],
    "asymptotic": ["asymptotic", "isLittleO", "isBigO"],
    "limit": ["tendsto"],
    "sum": ["sum", "tsum"],
    "product": ["prod", "mul"],
    "expectation": ["expect", "integral"],
    "variance": ["variance", "Var"],
    "covariance": ["cov", "Cov"],
    "probability": ["probability", "Prob"],
    "measure": ["measure", "Measure"],
}


def extract_keywords(statement: str) -> list[str]:
    """Lowercase the statement, find dictionary keys whose phrase appears in it."""
    text = statement.lower()
    matched = []
    for key, _ in KEYWORD_MAP.items():
        if key in text:
            matched.append(key)
    # Always include some default math vocabulary if none matched
    if not matched:
        for k in ["integral", "norm", "real"]:
            if k in text:
                matched.append(k)
    return matched


def grep_lemmas(pattern: str, mathlib_root: Path, max_matches: int = 200) -> list[tuple[str, str, str]]:
    """Return list of (file, lineno, signature) for theorem|lemma whose name matches pattern."""
    proc = subprocess.run(
        ["grep", "-rEn", "--include=*.lean",
         rf"^(theorem|lemma)\s+\w*{pattern}\w*\b",
         str(mathlib_root)],
        capture_output=True, text=True, timeout=120,
    )
    if proc.returncode != 0:
        return []
    out = []
    for line in proc.stdout.splitlines()[:max_matches]:
        parts = line.split(":", 2)
        if len(parts) >= 3:
            out.append((parts[0], parts[1], parts[2].strip()))
    return out


def find_hints(statement: str, mathlib_root: Path, top_n: int = 10) -> list[tuple[str, int, str]]:
    """Return top-N (lemma_name, score, signature) candidates."""
    keywords = extract_keywords(statement)
    if not keywords:
        return []
    # Aggregate Mathlib name patterns from matched keywords
    patterns = set()
    for kw in keywords:
        patterns.update(KEYWORD_MAP[kw])

    # Score lemmas by how many distinct patterns appear in their name
    candidates: dict[str, tuple[int, str, str]] = {}
    for pat in patterns:
        for file, lineno, sig in grep_lemmas(pat, mathlib_root):
            m = re.match(r"(?:theorem|lemma)\s+(\S+)", sig)
            if not m:
                continue
            name = m.group(1).rstrip("(:")
            if name in candidates:
                score, _, _ = candidates[name]
                candidates[name] = (score + 1, file, sig)
            else:
                candidates[name] = (1, file, sig)

    ranked = sorted(candidates.items(), key=lambda kv: -kv[1][0])
    return [(name, score, sig) for name, (score, _, sig) in ranked[:top_n]]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("statement", help="Lemma statement (English/LaTeX)")
    ap.add_argument("--mathlib-root", type=Path,
                    default=Path("/home/chinmay-gcp/lea-hadamard/.lake/packages/mathlib"))
    ap.add_argument("--top", type=int, default=10)
    args = ap.parse_args()

    hints = find_hints(args.statement, args.mathlib_root, top_n=args.top)
    if not hints:
        print("No hint candidates found.")
        return 1
    print(f"Top {len(hints)} candidates:")
    for name, score, sig in hints:
        print(f"  [{score}] {name}")
        print(f"        {sig[:200]}")
    return 0


if __name__ == "__main__":
    import sys
    sys.exit(main() or 0)
