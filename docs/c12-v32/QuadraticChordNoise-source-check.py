"""Frozen source/signature check only; this never invokes local Lean."""
import hashlib
import json
from pathlib import Path
import re

base = Path(__file__).resolve().parent
scope_bytes = (base / "FourierComparison-next-scope.md").read_bytes()
scope = scope_bytes.decode("utf-8")
source_bytes = (base / "QuadraticChordNoise.lean").read_bytes()
source = source_bytes.decode("utf-8")
frozen_hash = hashlib.sha256(scope_bytes).hexdigest()
assert frozen_hash == "912c3e001bcea85a64332c9efaf530ef55f3ddc0bf055841a762468a65a5ab44"
normalize = lambda s: re.sub(r"\s+", "", s)
frozen = re.findall(r"```lean\s*\n(theorem\s+quadratic[\s\S]*?)\n```", scope)
actual = re.findall(r"(?m)^(theorem\s+quadratic[\s\S]*?) := by\n", source)
assert len(frozen) == len(actual) == 4, (len(frozen), len(actual))
assert [normalize(x) for x in frozen] == [normalize(x) for x in actual]
defs_frozen = re.findall(r"```lean\s*\n(noncomputable def[\s\S]*?)\n```", scope)
defs_actual = source[source.index("noncomputable def"):source.index("private lemma")].strip()
assert len(defs_frozen) == 1
assert normalize(defs_frozen[0]) == normalize(defs_actual)
defs = re.findall(r"(?m)^(?:private\s+)?(?:noncomputable\s+)?def\s+(\S+)", source)
assert len(defs) == 4
assert not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", source)
report = {
    "status": "PASS",
    "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
    "scope_sha256": frozen_hash,
    "public_theorems": re.findall(r"(?m)^theorem\s+(\S+)", source),
    "private_lemmas": re.findall(r"(?m)^private lemma\s+(\S+)", source),
    "definitions": defs,
    "forbidden_source_tokens": [],
    "frozen_signatures_equal_after_whitespace_normalization": True,
    "frozen_definitions_equal_after_whitespace_normalization": True,
}
print(json.dumps(report, ensure_ascii=False, indent=2))
