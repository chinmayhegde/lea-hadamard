"""Extract a single named theorem environment from a blueprint TeX file.

Usage: python3 extract_node.py <input.tex> <label> > <output.tex>
"""
import re
import sys

ENVS = ("lemma", "theorem", "definition", "proposition", "corollary", "fact", "remark")
ENV_RE = re.compile(
    r"(\\begin\{(" + "|".join(ENVS) + r")\}(?:\[[^\]]*\])?"
    r"(?:.*?)\\end\{\2\})",
    re.DOTALL,
)
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")


def main():
    src = open(sys.argv[1]).read()
    target = sys.argv[2]
    for m in ENV_RE.finditer(src):
        body = m.group(1)
        labels = LABEL_RE.findall(body)
        if target in labels:
            print(body)
            return 0
    print(f"label {target!r} not found in {sys.argv[1]}", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
