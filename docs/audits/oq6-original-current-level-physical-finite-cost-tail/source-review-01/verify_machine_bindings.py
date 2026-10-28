import hashlib
import json
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path("C:/game/shao lean/drafts/oq56/unit261")
OUT = ROOT / "source-review-01"

def sha(b):
    return hashlib.sha256(b).hexdigest()

def read(rel, expected=None):
    p = ROOT / rel
    b = p.read_bytes()
    if expected:
        assert sha(b) == expected, str(p)
    return json.loads(b)

def same_bytes(local_path, remote_fp):
    b = Path(local_path).read_bytes()
    assert len(b) == remote_fp["bytes"] and sha(b) == remote_fp["sha256"]

meta = read("owner-evidence-01/actual-owned-metadata.json", "2d62a39bc0c4512d6cff909ae0933e336b9e5d55c620bc07877f3a8bc6921c0e")
summary = read("owner-evidence-01/native-kernel-and-all-owner-audit-summary.json", "c1f8818b1611ca480497cae8ba5c300f5184327050c9705c091ed821b155ae3e")
binding = read("owner-evidence-01/server-metadata-binding.json", "6c9bd09f3b59f7a642e1e549e5d0995736cfc3e80147e56fd579ca8f2fd03f7e")
proj = read("lead-execution-01/machine-command-pins-CPU-and-stop-existing-receipts-projection.json", "7ffb46023ce7228fe3069b171525ea18af9e9f6e598b82d0810bdb53c0b6e107")
assert meta["source"] == summary["source"] == binding["source"] == proj["source"]
assert meta["object"] == summary["object"] == binding["object"] == proj["firstOriginalObject"]
obj = meta["object"]
assert obj == proj["auditObjectBefore"] == proj["auditObjectAfter"]
assert obj["sha256"] == "1e23231ca1de2adca9a97bf48f3e85f9fdc9e5d2dcf11eb2db98914a19f2faa9"
assert obj["bytes"] == 16938928 and obj["mtime_ns"] == "1793223100095739394"
same_bytes(ROOT / "author-repair-02/OriginalCurrentLevelPhysicalFiniteCostTail.lean", meta["source"])
same_bytes(ROOT / "owner-evidence-01/actual-owned-metadata.json", binding["metadata"])
same_bytes(ROOT / "owner-evidence-01/native-kernel-and-all-owner-audit-summary.json", binding["summary"])
assert summary["actualNativeAttempt"] == proj["actualSourceNativeAttempt"] == 3
assert summary["actualNativeLabel"] == "author-kernel-03"
assert summary["legacyNative01KeyMeansActualNative03"]
assert summary["actualOwned"] == meta["actualOwnerCount"] == 2
assert summary["actualTheorems"] == meta["allTheoremCount"] == 2
assert summary["actualNonTheorems"] == meta["nonTheoremCount"] == 0
assert summary["TYPElines"] == sum(e["typeLines"] for e in meta["entries"]) == 78635
assert summary["VALUElines"] == 0
for e in meta["entries"]:
    raw = json.loads(e["rawOwnedJSON"])
    assert all(e[k] == v for k, v in raw.items())
    assert e["constantKind"] == "thmInfo" and e["isTheorem"]
    assert e["bodyExpressionPresent"] and "value" not in e
    assert set(e["axioms"]) == {"propext", "Classical.choice", "Quot.sound"}

for key, s_key in [("native", "native01"), ("audit", "ownedAudit01")]:
    r = proj[key]
    s = summary[s_key]
    assert r["actualExitCode"] == s["actualExitCode"] == 0
    assert r["allOwnedEnded"] and not r["timedOut"]
    assert r["cleanupEvents"] == [] and r["ownershipIssue"] is None and r["postError"] is None
    assert r["preservationEqual"] and r["beforeAfterExact"] and s["beforeAfterExact"]
    assert r["receipt"] == s["receipt"]
    assert r["strictWrapperSuccess"] is False and s["strictWrapperSuccess"] is False
    assert r["CPUbefore"] == r["CPUafter"] == r["resourceCPU"] == [52, 53, 54, 55]
    assert r["command"][:10] == ["taskset", "-c", "52-55", "lake", "env", "lean", "-M", "8192", "-j", "4"]
assert proj["native"]["command"][-3:] == ["-o", obj["physical_path"], "Shao/OQ6/OriginalCurrentLevelPhysicalFiniteCostTail.lean"]
assert "-o" not in proj["audit"]["command"] and proj["audit"]["no_o"] and proj["audit"]["own_object_import"]
assert binding["nativeReceipt"] == proj["native"]["receipt"]
assert binding["auditReceipt"] == meta["auditReceipt"] == proj["audit"]["receipt"]
assert summary["native01"]["sourceErrors"] == 0 and summary["native01"]["sourceWarnings"] == 24
assert summary["native01"]["protectedDerived"] == 28963
assert summary["ownedAudit01"]["protectedDerived"] == 28972
stop = proj["manualAuthorStop"]
assert stop["fp"]["sha256"] == "fca9b7ca890077454be220d03c90477f64647136a0c958ca0fc4c05dc52cbf3c"
assert stop["fp"]["bytes"] == 1401
assert stop["content"]["FIRSTOriginalObject"] == obj
assert stop["content"]["source"] == meta["source"]
assert stop["content"]["actualNativeExitCode"] == 0 and stop["content"]["naturalEnded"]
assert stop["content"]["allAuthorNativeStopped"] and stop["content"]["onlySameOriginalObjectImportAuditNext"]
stop_bytes = (json.dumps(stop["content"], ensure_ascii=False, indent=2) + "\n").encode()
assert len(stop_bytes) == stop["fp"]["bytes"] and sha(stop_bytes) == stop["fp"]["sha256"]
pin = proj["pinnedToolchain"]
literal = pin["literalUTF8Content"].encode()
assert literal == b"leanprover/lean4:v4.36.0-rc1\n"
assert sha(literal) == "d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4"
for k in ["nativeBefore", "nativeAfter", "auditBefore", "auditAfter"]:
    assert pin[k] == pin["current"]
assert pin["current"]["sha256"] == sha(literal) and pin["current"]["bytes"] == len(literal)
assert proj["gitPins"]["Mathlib_HEAD"] == "807d3836b165983210ee2ecf3cd28f239436949c"
assert summary["oldProducerRechecks"] == 0 and summary["ownLean"] == binding["ownLean"] == []
same_bytes(ROOT / "lead-execution-01/owned-object-audit-input.lean", proj["audit"]["input"])
origin = proj["native"]["processControlOrigin"]
for key, file in [("sourceReview", "SOURCE-REPORT.md"), ("affectedRepair01Review", "REPAIR01-REPORT.md"), ("affectedRepair02Review", "REPAIR02-REPORT.md")]:
    same_bytes(OUT / file, origin[key])

result = {
    "schema": "oq56-unit261-independent-machine-binding-check-v1",
    "allChecksPass": True, "source": meta["source"], "firstOriginalObject": obj,
    "nativeActualAttempt": 3, "nativeActualRC": 0, "auditActualRC": 0,
    "sameOriginalObjectFullFingerprintPreserved": True,
    "sourceReviewExactUnionBindingsMatch": True,
    "nativeAndAuditCPU": [52, 53, 54, 55], "memoryMiB": 8192, "jobs": 4,
    "nativeNaturalEnded": True, "auditNaturalEnded": True,
    "cleanupEvents": [], "ownershipIssue": None, "postError": None,
    "manualSTOPContentExactBytesReconstructed": True,
    "literalPinExactAllFourSnapshots": True, "literalPinSHA256": sha(literal),
    "MathlibHEAD": proj["gitPins"]["Mathlib_HEAD"],
    "allActualOwners": 2, "TYPElines": 78635, "requiredVALUE": 0,
    "allRecursiveAxiomsWhitelisted": True,
    "warnings": {"style": 6, "unused": 18, "total": 24, "errors": 0},
    "strictWrapperSuccessNative": False, "strictWrapperSuccessAudit": False,
    "newLeanCallsByReviewer": 0, "newAXCallsByReviewer": 0,
}
(OUT / "MACHINE-BINDING-CHECK.json").write_bytes((json.dumps(result, ensure_ascii=False, indent=2) + "\n").encode())
print(json.dumps({"allChecksPass": True, "manualStopByteExact": True, "actualOwnerCount": 2, "TYPElines": 78635, "nativeAttempt": 3}))
