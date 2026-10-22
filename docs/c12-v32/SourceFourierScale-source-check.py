"""Read-only source/contract binding check; never invokes Lean."""
from pathlib import Path
import hashlib
import json
import re

BASE = Path(__file__).parent
SOURCE = BASE / "SourceFourierScale.lean"
SCOPE = BASE / "SourceFourierScale-next-scope.md"
REVIEW = BASE / "SourceFourierScale-declaration-review.md"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def strip_noncode(text):
    out, pos, depth = [], 0, 0
    while pos < len(text):
        if depth:
            if text.startswith("/-", pos):
                depth += 1
                pos += 2
            elif text.startswith("-/", pos):
                depth -= 1
                pos += 2
            else:
                out.append("\n" if text[pos] == "\n" else " ")
                pos += 1
        elif text.startswith("/-", pos):
            depth = 1
            pos += 2
        elif text.startswith("--", pos):
            end = text.find("\n", pos)
            pos = len(text) if end < 0 else end
        elif text[pos] == '"':
            pos += 1
            while pos < len(text):
                if text[pos] == "\\":
                    pos += 2
                elif text[pos] == '"':
                    pos += 1
                    break
                else:
                    pos += 1
            out.append(" ")
        else:
            out.append(text[pos])
            pos += 1
    assert depth == 0, "Unclosed block comment"
    return "".join(out)


def inspect():
    raw, frozen, review = SOURCE.read_bytes(), SCOPE.read_bytes(), REVIEW.read_bytes()
    assert sha(frozen) == "5d0afce4726be7a211e934a6bc3ff72e68fc2e622bc091b1e67ad4abff1773ef"
    assert sha(review) == "cf3a3a7b298d19ab7549d93f0d9f823c3e4c577987c74859da2a3ee3cb9e41c9"
    assert b"\r" not in raw and not raw.startswith(b"\xef\xbb\xbf")
    source = raw.decode("utf8")
    code = strip_noncode(source)
    forbidden = re.findall(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code)
    assert not forbidden
    declarations = [
        {"private": bool(p), "kind": k, "name": n}
        for p, k, n in re.findall(r"(?m)^(private )?(theorem|lemma|def|abbrev|axiom)\s+(\w+)", code)
    ]
    public = [d for d in declarations if not d["private"]]
    expected = ["sourceTruncation_gamma_bounds", "sourceTruncation_oddPower_scale_inputs"]
    assert [d["name"] for d in public] == expected
    assert all(d["kind"] in ("theorem", "lemma") for d in declarations)
    blocks = re.findall(r"```lean\n(.*?)```", frozen.decode("utf8"), re.S)
    assert len(blocks) == 2
    comparisons = []
    for name, block in zip(expected, blocks):
        start = source.index("theorem " + name)
        end = source.index(" := by", start)
        equal = re.sub(r"\s+", "", source[start:end]) == re.sub(r"\s+", "", block.strip())
        assert equal, name
        comparisons.append({"name": name, "exact_frozen_header_mod_whitespace": equal})
    return {
        "status": "PASS", "source_sha256": sha(raw), "source_bytes": len(raw),
        "source_lf_lines": raw.count(b"\n"), "utf8_lf_no_bom": True,
        "scope_sha256": sha(frozen), "declaration_review_sha256": sha(review),
        "comparisons": comparisons, "declarations": declarations,
        "public_definitions": 0, "public_theorems": 2, "forbidden_code": forbidden,
        "imports": re.findall(r"(?m)^import (\S+)", code),
    }


if __name__ == "__main__":
    print(json.dumps(inspect(), indent=2))
