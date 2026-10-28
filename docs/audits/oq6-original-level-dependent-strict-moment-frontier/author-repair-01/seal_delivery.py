from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json

ROOT = Path('C:/game/shao lean')
UNIT = ROOT / 'drafts/oq56/unit257'
OUT = UNIT / 'author-repair-01'
SRC = OUT / 'OriginalLevelDependentStrictMomentFrontier.lean'


def read(p):
    return json.loads(p.read_text(encoding='utf-8'))


def bind(p):
    b = p.read_bytes()
    return {'path': p.as_posix(), 'sha256': hashlib.sha256(b).hexdigest(),
            'bytes': len(b), 'LF': b.count(b'\n')}


def save(name, value):
    p = OUT / name
    assert not p.exists(), p
    p.write_bytes((json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode('utf-8'))


assert not (OUT / 'MANIFEST.json').exists()
assert not (OUT / 'FINALWRITE.json').exists()
check = read(OUT / 'REPAIR-CHECK.json')
assert check['STATUS'] == 'PASS_SOURCE_STATIC_ONLY'
assert check['source'] == bind(SRC)
assert check['sourceInsertions'] == 2 and check['sourceDeletions'] == 0
assert check['removeOnlyTwoInsertedLinesRestoresOldSourceExactly']
inputs = read(OUT / 'INPUT-BINDINGS.json')['inputs']
for x in inputs:
    assert bind(Path(x['path'])) == {k: x[k] for k in ['path', 'sha256', 'bytes', 'LF']}
payload = []
for p in sorted(OUT.iterdir()):
    assert p.is_file(), p
    if p.name in ['MANIFEST.json', 'FINALWRITE.json']:
        continue
    b = p.read_bytes()
    assert b.decode('utf-8').encode('utf-8') == b
    assert not b.startswith(b'\xef\xbb\xbf') and b'\r' not in b
    assert b.endswith(b'\n') and not b.endswith(b'\n\n'), p
    payload.append(bind(p))
assert check['formattedPayloadsChecked'] == len(payload) - 1
activation = read(UNIT / 'repair-01-ACTIVATION.json')
common = {
    'role': '/root/oq56_unit257_author_repair01',
    'ownerChat': activation['ownerChat'],
    'currentRoot': activation['root'],
    'source': bind(SRC),
    'proof': bind(OUT / 'PROOF-BODY.txt'),
    'frozenHead': bind(UNIT / 'freeze-01/FROZEN-HEAD.txt'),
    'originalSource': bind(UNIT / 'author-01/OriginalLevelDependentStrictMomentFrontier.lean'),
    'exactPatch': bind(OUT / 'exact.patch'),
    'mathematicalDeclarationChanged': False,
    'sourceAccepted': False,
    'independentAffectedReviewPending': True,
    'machinePending': True,
    'qualified': False,
    'actualOwnerCount': None,
    'actualTYPE': None,
    'actualVALUE': None,
    'actualAX': None,
}
manifest = {
    'schema': 'unit257-repair01-derived-final-payload-manifest-v1',
    'atUTC': datetime.now(timezone.utc).isoformat(),
    **common,
    'payloadCountExcludingManifestAndRelease': len(payload),
    'payload': payload,
    'immutableInputBindingsVerified': len(inputs),
    'allOriginalInputBytesUnchanged': True,
    'wholeLeanSourceDiff': {'insertedLines': 2, 'deletedLines': 0,
        'newInsertedLineNumbers': check['exactSourceInsertedLines']},
    'fullProofArtifactSingleFinalLF': True,
    'inheritedProofClosingBoundarySeparatorLF': 1,
    'allPayloadUTF8NoBOMNoCRSingleFinalLF': True,
    'pureSourceStaticCheck': bind(OUT / 'REPAIR-CHECK.json'),
    'noNewServerOrKernelClaims': True,
}
save('MANIFEST.json', manifest)
for x in payload:
    assert bind(Path(x['path'])) == x
for x in inputs:
    assert bind(Path(x['path'])) == {k: x[k] for k in ['path', 'sha256', 'bytes', 'LF']}
release = {
    'schema': 'unit257-repair01-finalwrite-sixzero-release-v1',
    'atUTC': datetime.now(timezone.utc).isoformat(),
    **common,
    'STATUS': 'DIRECTED_PROOF_EXPRESSION_REPAIR_DELIVERED_WRITER_RELEASED',
    'finalManifest': bind(OUT / 'MANIFEST.json'),
    'payloadCountExcludingManifestAndRelease': len(payload),
    'allPayloadAndInputBindingsVerifiedBeforeRelease': True,
    'sourceRepairComplete': True,
    'onlyTwoLocalDefinitionalTypeAlignmentCommandsAdded': True,
    'oldCompleteSourceReviewReusedWithAffectedSupplementPending': True,
    'requestedModel': 'gpt-6.1-sol',
    'requestedEffort': 'xhigh',
    'freshContextRequested': True,
    'actualModel': None,
    'actualBackend': None,
    'actualEffort': None,
    'usage': {'input': None, 'cachedInput': None, 'output': None, 'reasoningSubset': None},
    'operations': dict.fromkeys(['Lean', 'lake', 'PP', 'AX', 'server', 'network',
        'upload', 'Git', 'API', 'children', 'sidebar', 'Goal', 'schedule'], 0),
    'writers': 0,
    'heavy': 0,
    'inflight': 0,
    'pendingExternal': 0,
    'children': 0,
    'uncertain': 0,
    'stopWritingAfterThisFile': True,
    'ownershipReleased': 'All exclusive author-repair-01 directory writer authority is released after this last write; no shared/server/execution/publication/child authority was held.',
    'sameM0BeforeAllNCurrentZEpsilonPBudget': True,
    'sameXiYEpsilonEtaAndCosts': True,
    'originalMuMomentOnly': True,
    'everyDelta0EqualsOriginalDelta': True,
    'allPartialDenominatorsRemainCompleteI': True,
    'jointSingleK0ForEveryPositiveTauDeltaWithOriginalPositiveSlack': True,
    'actualUpperCurrentPhysicalExternalEngineCDFRelativeDC': 'OPEN',
    'fullOQ56': 'OPEN',
    'root': 'OPEN',
    'nextDependency': 'Existing independent SOURCE reviewer checks only affected two proof expressions and new exact source bindings, then parent new-source native and if successful same-first-original-object allactual TYPE/requiredVALUE/transitiveAX; independent final qualification remains mandatory.',
}
# FINALWRITE is deliberately the final filesystem mutation in this script.
save('FINALWRITE.json', release)
print(json.dumps({'STATUS': release['STATUS'], 'source': bind(SRC),
    'proof': bind(OUT / 'PROOF-BODY.txt'), 'patch': bind(OUT / 'exact.patch'),
    'manifest': bind(OUT / 'MANIFEST.json'), 'release': bind(OUT / 'FINALWRITE.json'),
    'payloadCount': len(payload), 'immutableInputCount': len(inputs),
    'sixZero': {k: release[k] for k in ['writers', 'heavy', 'inflight',
        'pendingExternal', 'children', 'uncertain']},
    'qualified': False, 'machinePending': True}, ensure_ascii=False))
