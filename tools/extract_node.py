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


def strip_tex_comments(src: str) -> str:
    """Remove TeX line comments. Treats `%` as comment-start when it isn't escaped."""
    out_lines = []
    for line in src.splitlines():
        # find first % that's not preceded by an odd number of backslashes
        i = 0
        while i < len(line):
            if line[i] == "%":
                # count preceding backslashes
                j = i - 1
                bs = 0
                while j >= 0 and line[j] == "\\":
                    bs += 1
                    j -= 1
                if bs % 2 == 0:
                    line = line[:i]
                    break
            i += 1
        out_lines.append(line)
    return "\n".join(out_lines)


def main():
    import os
    path = sys.argv[1]
    target = sys.argv[2]
    if os.path.isdir(path):
        sources = []
        for root, _, files in os.walk(path):
            for f in files:
                if f.endswith(".tex"):
                    sources.append(os.path.join(root, f))
    else:
        sources = [path]
    for src_path in sorted(sources):
        src = strip_tex_comments(open(src_path).read())
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
