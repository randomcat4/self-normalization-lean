from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json

OUT = Path('C:/game/shao lean/drafts/oq56/unit256/author-repair-01')
OLD = OUT.parent / 'author-01'
FREEZE = OUT.parent / 'freeze-02'
ROLE = '/root/oq56_unit256_author_repair01'

def binding(path):
    path = Path(path)
    raw = path.read_bytes()
    return {'path': path.as_posix(), 'sha256': hashlib.sha256(raw).hexdigest(),
            'bytes': len(raw), 'LF': raw.count(b'\n')}

def load(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))

def save(name, value):
    (OUT / name).write_bytes((json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode('utf-8'))

assert not (OUT / 'FINALWRITE.json').exists()
source = OUT / 'OriginalLevelDependentLiteralWeightedConsumer.lean'
sb = binding(source)
assert (sb['sha256'], sb['bytes'], sb['LF']) == (
    'bbab19f1d8c091b81e3c06e7cfbc0dcc3c6acb16ce39261d0f08b2dc3ac1efcf', 66823, 1053)
proof = binding(OUT / 'PROOF-BODY.txt')
assert (proof['sha256'], proof['bytes'], proof['LF']) == (
    '03325066041df6ad3fc4b5d5a266f44caa3597e74fb573efdc931a4028f84b07', 33117, 561)
assert source.read_bytes() == (FREEZE / 'FROZEN-PREAMBLE.txt').read_bytes() + \
    (FREEZE / 'FROZEN-HEAD.txt').read_bytes() + b':= by\n' + \
    (OUT / 'PROOF-BODY.txt').read_bytes() + (FREEZE / 'FROZEN-CLOSING.txt').read_bytes()
static = load(OUT / 'STATIC-CHECK.json')
verification = load(OUT / 'REPAIR-STATIC-CHECK.json')
assert static['source'] == sb == verification['source']
assert verification['STATUS'] == 'STATIC_PASS_ONLY' and verification['changedLines'] == [757, 797, 1030]
assert static['qualified'] is False and verification['qualified'] is False
assert static['actualMachineOwnerCount'] is None and verification['actualTYPE'] is None
assert verification['actualVALUE'] is None and verification['recursiveAX'] is None
old_manifest = load(OLD / 'MANIFEST.json')
for item in old_manifest['payload']:
    assert binding(item['path']) == item, item['path']
assert binding(OLD / 'MANIFEST.json')['sha256'] == 'b26c98712d21495cc115b0eb88329a71610fb93bf2bc114b725a96d3ca90a6b8'
assert binding(OLD / 'FINALWRITE.json')['sha256'] == '8c17b37feaf3ad246e049c6c7300146284587d8bfca66137b86c8cf3a7a5374a'
paths = [p for p in sorted(OUT.iterdir()) if p.is_file() and p.name not in ('MANIFEST.json', 'FINALWRITE.json')]
for path in paths:
    raw = path.read_bytes()
    assert raw.decode('utf-8').encode('utf-8') == raw, path.name
    assert not raw.startswith(b'\xef\xbb\xbf') and b'\r' not in raw, path.name
    assert raw.endswith(b'\n') and not raw.endswith(b'\n\n'), path.name
payload = [binding(p) for p in paths]
manifest = {
    'schema': 'unit256-repair01-complete-source-final-payload-manifest-v1',
    'atUTC': datetime.now(timezone.utc).isoformat(), 'role': ROLE,
    'leadOwner': '01a1822b-1815-7f21-a1af-2e0b15ee67a5',
    'source': sb, 'proof': proof, 'freeze': binding(FREEZE / 'frozen-declaration.json'),
    'payloadCountExcludingManifestAndRelease': len(payload), 'payload': payload,
    'old35PayloadsVerifiedReadOnlyCountDerived': len(old_manifest['payload']),
    'oldOriginalSource': binding(OLD / source.name), 'oldOriginalManifest': binding(OLD / 'MANIFEST.json'),
    'oldOriginalRelease': binding(OLD / 'FINALWRITE.json'),
    'changedSourceLines': [757, 797, 1030], 'allNonProofAndFrozenBytesExact': True,
    'allCurrentPayloadsUtf8LFSingleFinalLF': True,
    'actualOwnerCount': None, 'actualTYPE': None, 'actualVALUE': None, 'recursiveAX': None,
    'evidenceClass': 'PURE_SOURCE_DERIVED_STATIC_NOT_MACHINE_OWNER',
    'qualified': False, 'machinePending': True,
}
save('MANIFEST.json', manifest)
for item in payload:
    assert binding(item['path']) == item, item['path']
mb = binding(OUT / 'MANIFEST.json')
release = {
    'schema': 'unit256-repair01-finalwrite-sixzero-release-v1',
    'atUTC': datetime.now(timezone.utc).isoformat(), 'role': ROLE,
    'leadOwner': '01a1822b-1815-7f21-a1af-2e0b15ee67a5',
    'currentRoot': '01a17d3c-6dfd-7cc0-94ed-35d758a423a5',
    'STATUS': 'THREE_PROOF_EXPRESSION_REPAIRS_COMPLETE_SOURCE_DELIVERED',
    'source': sb, 'proof': proof, 'freeze': binding(FREEZE / 'frozen-declaration.json'),
    'finalManifest': mb, 'payloadCountExcludingManifestAndRelease': len(payload),
    'payloadCountIncludingManifestExcludingRelease': len(payload) + 1,
    'allPayloadsVerifiedBeforeRelease': True, 'changedSourceLines': [757, 797, 1030],
    'mathematicalAssumptionsOrStatementChanged': False,
    'old35PayloadsAndAllPriorFailuresRetainedReadOnly': True,
    'authorProofCompleteAsCandidate': True, 'sourceAccepted': False,
    'independentAffectedProofReviewPending': True, 'qualified': False, 'machinePending': True,
    'actualMachineOwnerCount': None, 'actualMachineTheorems': None, 'actualMachineNonTheorems': None,
    'actualTYPELF': None, 'requiredVALUECount': None, 'allOwnedAxiomOccurrences': None,
    'actualTYPE': None, 'actualVALUE': None, 'recursiveAX': None,
    'requestedModel': 'gpt-6.1-sol', 'requestedEffort': 'xhigh', 'freshContextRequested': True,
    'actualModel': None, 'actualBackend': None, 'actualEffort': None,
    'usage': {'input': None, 'cachedInput': None, 'output': None, 'reasoningSubset': None},
    'writers': 0, 'heavy': 0, 'inflight': 0, 'pendingExternal': 0, 'children': 0, 'uncertain': 0,
    'stopWritingAfterThisFile': True,
    'ownershipReleased': 'All author-repair-01 writer authority released after this final write. No other owner, server, execution, or publication authority was held.',
    'LeanLakePPAXServerNetworkUploadGitAPIChildrenSidebarGoalScheduleOperations': 0,
    'oldNative02': {'exit_code': 1, 'objectAfter': None, 'retainedWithoutReplay': True},
    'nextDependency': 'Same independent reviewer affected-proof review; parent new complete-source native and, only upon success, same-first-original-object all-owned TYPE/required VALUE/transitive AX. Original-p strictbudget/actualupper/physicalpayments/sourceengine remain subsequent OPEN interfaces.',
    'fullOQ56': 'OPEN', 'root': 'OPEN',
}
# Deliberately the final filesystem write by this repair author.
save('FINALWRITE.json', release)
print(json.dumps({'source': sb, 'proof': proof, 'manifest': mb,
    'FINALWRITE': binding(OUT / 'FINALWRITE.json'), 'payloadCount': len(payload),
    'allSixRuntimeCounts': 0, 'qualified': False, 'machinePending': True}, ensure_ascii=False))
