import collections
import hashlib
import json
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.setrecursionlimit(100000)
ROOT = Path("C:/game/shao lean/drafts/oq56/unit261")
OUT = ROOT / "source-review-01"
META = ROOT / "owner-evidence-01/actual-owned-metadata.json"
TYPES = ROOT / "owner-evidence-01/actual-owned-types.txt"
VALUES = ROOT / "owner-evidence-01/actual-owned-values.txt"

def digest(b):
    return hashlib.sha256(b).hexdigest()

def write(name, obj):
    (OUT / name).write_bytes((json.dumps(obj, ensure_ascii=False, indent=2) + "\n").encode())

mb = META.read_bytes()
tb = TYPES.read_bytes()
meta = json.loads(mb)
entries = meta["entries"]
assert len(entries) == meta["actualOwnerCount"] == 2
assert b"".join((e["name"] + " : " + e["type"]).encode() for e in entries) == tb
assert VALUES.read_bytes() == b""
raw = "".join(
    "OQ56_OWNED_JSON " + e["rawOwnedJSON"] + "\n"
    + "OQ56_OWNED_TYPE " + e["name"] + " : " + e["type"]
    + ("OQ56_OWNED_VALUE " + e["name"] + " := " + e["value"] if "value" in e else "")
    for e in entries
) + meta["rawOwnedCountLine"]
assert digest(raw.encode()) == meta["rawStdoutSHA256"] == "ca4b2de9365a8a64d779a9761d3803dfc5ee664d9b267cd18c99a769e6591579"
assert len(raw.encode()) == meta["rawStdoutBytes"] == 12748995
assert digest(tb) == "0ab708982bdbbae74b998e706d84557f274c4a99fdb6c6d8c9469d5bd9d26e31"
assert digest(mb) == "2d62a39bc0c4512d6cff909ae0933e336b9e5d55c620bc07877f3a8bc6921c0e"

for e in entries:
    assert e["constantKind"] == "thmInfo" and e["isTheorem"] and e["bodyExpressionPresent"]
    assert set(e["axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
    assert "value" not in e
    assert e["typeLines"] == len(e["type"].splitlines())
    assert ".".join(x["value"] for x in e["components"]) == e["name"]
    assert all(x not in e["type"] for x in ["⋯", "...", "<elided>", "failed to pretty print"])

canonical = [re.sub(r"\s+", " ", e["type"]).strip() for e in entries]
const_re = re.compile(r"@?[\w']+(?:\.[\w']+)+(?:\.\{[^}]*\})?")
counts = collections.Counter(m.group() for s in canonical for m in const_re.finditer(s))
ks = sorted(k for k, v in counts.items() if len(k) >= 16 and v >= 2)
kmap = {v: "⟪K%d⟫" % (i + 1) for i, v in enumerate(ks)}
aliased = [const_re.sub(lambda m: kmap.get(m.group(), m.group()), s) for s in canonical]

nodes = []
node_ids = {}
occ = collections.Counter()
sizes = []

def intern(parts):
    key = tuple(parts)
    idx = node_ids.get(key)
    if idx is None:
        idx = len(nodes)
        node_ids[key] = idx
        nodes.append(key)
        sizes.append(2 + sum(sizes[x] if isinstance(x, int) else len(x) for x in key))
    occ[idx] += 1
    return idx

roots = []
for s in aliased:
    stack = [[]]
    for token in re.split(r"([()])", s):
        if token == "(":
            stack.append([])
        elif token == ")":
            assert len(stack) > 1
            idx = intern(stack.pop())
            stack[-1].append(idx)
        elif token:
            stack[-1].append(token)
    assert len(stack) == 1
    roots.append(tuple(stack[0]))

selected = sorted((i for i in range(len(nodes)) if occ[i] >= 2 and sizes[i] >= 50), key=lambda i: (sizes[i], i))
dmap = {idx: "⟦D%d⟧" % (j + 1) for j, idx in enumerate(selected)}
encode_cache = {}

def encode_parts(parts):
    return "".join(encode(x) if isinstance(x, int) else x for x in parts)

def encode(idx):
    if idx in dmap:
        return dmap[idx]
    if idx not in encode_cache:
        encode_cache[idx] = "(" + encode_parts(nodes[idx]) + ")"
    return encode_cache[idx]

defs = [{"id": dmap[i], "value": "(" + encode_parts(nodes[i]) + ")", "occurrences": occ[i]} for i in selected]
owners = [{"name": e["name"], "typeLines": e["typeLines"], "factoredType": encode_parts(root),
           "originalTypeSHA256": digest(e["type"].encode()), "canonicalTypeSHA256": digest(c.encode())}
          for e, c, root in zip(entries, canonical, roots)]
dictionary = {x["id"]: x["value"] for x in defs}
aliases = [{"id": kmap[k], "value": k, "occurrences": counts[k]} for k in ks]
kdict = {x["id"]: x["value"] for x in aliases}
expanded = {}

def expand_d(key):
    if key not in expanded:
        expanded[key] = re.sub(r"⟦D\d+⟧", lambda m: expand_d(m.group()), dictionary[key])
    return expanded[key]

for e, c, owner in zip(entries, canonical, owners):
    result = re.sub(r"⟦D\d+⟧", lambda m: expand_d(m.group()), owner["factoredType"])
    result = re.sub(r"⟪K\d+⟫", lambda m: kdict[m.group()], result)
    assert result == c
    # Whitespace is an independent exact layout channel, never semantic omission.
    old_tokens = list(re.finditer(r"\S+", e["type"]))
    rebuilt_tokens = list(re.finditer(r"\S+", result))
    assert [m.group() for m in old_tokens] == [m.group() for m in rebuilt_tokens]
    layout = []
    pos = 0
    for old, new in zip(old_tokens, rebuilt_tokens):
        layout.extend([e["type"][pos:old.start()], new.group()])
        pos = old.end()
    layout.append(e["type"][pos:])
    restored = "".join(layout)
    assert restored.encode() == e["type"].encode()
    owner["reversibleCanonicalAndRawBytesVerified"] = True
    owner["factoredCharacters"] = len(owner["factoredType"])

readmap = {
    "schema": "oq56-unit261-lossless-all-actual-type-read-map-v1",
    "method": "Exact constant/universe aliases and repeated balanced-parentheses expression DAG; full remaining spines. Canonical expansion exact; original inter-token whitespace layout restores each original TYPE byte exactly.",
    "inputTypesSHA256": digest(tb), "inputTypesBytes": len(tb),
    "inputTypesLF": tb.count(b"\n"), "metadataSHA256": digest(mb),
    "aliases": aliases, "definitions": defs, "owners": owners,
    "rawStdoutSHA256": digest(raw.encode()), "rawStdoutBytes": len(raw.encode()),
    "completeRawTYPEMetadataAndStdoutByteEqualityVerified": True,
    "noElisionOrNamespaceFilter": True, "allActualTheorems": 2, "nonTheorems": 0,
    "requiredVALUE": 0, "allRecursiveAxioms": sorted({"propext", "Classical.choice", "Quot.sound"}),
    "semanticReadComplete": False
}
write("MACHINE-TYPE-READ-MAP.json", readmap)
write("MACHINE-TYPE-RAW-IDENTITY.json", {
    "schema": "oq56-unit261-machine-lossless-raw-identity-v1",
    "metadataSHA256": digest(mb), "typesSHA256": digest(tb),
    "typesBytes": len(tb), "typesLF": tb.count(b"\n"),
    "reconstructedRawStdoutSHA256": digest(raw.encode()),
    "reconstructedRawStdoutBytes": len(raw.encode()),
    "actualOwnerCount": len(entries), "allTheoremCount": sum(e["isTheorem"] for e in entries),
    "TYPElines": sum(e["typeLines"] for e in entries), "VALUElines": 0,
    "allRawTYPEBytesRecoveredFromDAGAndOriginalExactWhitespaceLayout": True,
    "noSemanticElision": True, "semanticReadingStillRequired": True,
})
print(json.dumps({"aliases": len(aliases), "definitions": len(defs), "owners": [
    {"name": o["name"], "lines": o["typeLines"], "factoredCharacters": o["factoredCharacters"]} for o in owners],
    "mapBytes": (OUT / "MACHINE-TYPE-READ-MAP.json").stat().st_size}, ensure_ascii=False))
