from pathlib import Path
from datetime import datetime, timezone
import difflib
import hashlib
import json

ROOT = Path('C:/game/shao lean')
UNIT = ROOT / 'drafts/oq56/unit256'
OUT = UNIT / 'author-repair-01'
OLD = UNIT / 'author-01'
FREEZE = UNIT / 'freeze-02'
ROLE = '/root/oq56_unit256_author_repair01'

def binding(p):
    p = Path(p)
    raw = p.read_bytes()
    return {'path': p.as_posix(), 'sha256': hashlib.sha256(raw).hexdigest(),
            'bytes': len(raw), 'LF': raw.count(b'\n')}

def save(name, value):
    (OUT / name).write_bytes((json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode('utf-8'))

assert not (OUT / 'FINALWRITE.json').exists()
source_name = 'OriginalLevelDependentLiteralWeightedConsumer.lean'
old_source = OLD / source_name
expected = {
    old_source: ('8165e387c4f04ae5a751b76468d98fe8a5909d980f3d5f70384475b1c02d3466', 66807),
    OLD / 'FINALWRITE.json': ('8c17b37feaf3ad246e049c6c7300146284587d8bfca66137b86c8cf3a7a5374a', 2925),
    OLD / 'MANIFEST.json': ('b26c98712d21495cc115b0eb88329a71610fb93bf2bc114b725a96d3ca90a6b8', 9112),
    FREEZE / 'frozen-declaration.json': ('c2f06d7e94c9cb9dfaf3ea6851c8cb9c287cf7ef3e1b9b8472b44b292ee0894a', 2368),
    FREEZE / 'FROZEN-HEAD.txt': ('7951013304c2f42406971387ea8749955c0c44fa5e56c604d9ef587cd0d0a6ac', 33236),
    FREEZE / 'FROZEN-PREAMBLE.txt': ('a52e8a0b63b5dcc2e85e5d83512c5d25d821a6c47d82564a200a78ac0f2d3bf8', 399),
    FREEZE / 'FROZEN-CLOSING.txt': ('ea4bd4efb58a5f2637dc75658a6551393c16ad47f335454dd9551d86b8c6038b', 65),
    UNIT / 'source-review-01/SOURCE-REPORT.md': ('b1668b3e559d971b2039f2ed35da0564f37eaa5ff8706ef6dd15eb674d26dbad', 10987),
    UNIT / 'source-review-01/SOURCE-VERDICT.json': ('0c533f9b445ca343c26a8aa26d7cefed06c89d0165424c99cf795c685374aeb4', 2966),
    UNIT / 'lead-execution-01/native02-actual-projection.json': ('f1b305a099d20875ba87f1da11be8769a64507b4aeba07fafb859b18852bdc8e', 6736),
    ROOT / 'drafts/oq56/unit255/author-01/OriginalLevelDependentCanonicalCostPacket.lean': ('a2db2c096e444b9ddd63fe4ff0baa451a0d2b834cb5c9049998cee2eeeb18989', 38774),
    ROOT / 'drafts/oq56/unit255/qualified-evidence.json': ('3f0421247fcccb0515153b89a2381206243b7ca96c4a049d2caf124284f52713', 8204),
}
for path, (sha, size) in expected.items():
    actual = binding(path)
    assert actual['sha256'] == sha and actual['bytes'] == size, actual
old_manifest = json.loads((OLD / 'MANIFEST.json').read_text(encoding='utf-8'))
for item in old_manifest['payload']:
    actual = binding(item['path'])
    assert actual == item, item['path']
old_release = json.loads((OLD / 'FINALWRITE.json').read_text(encoding='utf-8'))
assert all(old_release[key] == 0 for key in ('writers', 'heavy', 'inflight', 'pendingExternal', 'children', 'uncertain'))

pre = (FREEZE / 'FROZEN-PREAMBLE.txt').read_bytes()
head = (FREEZE / 'FROZEN-HEAD.txt').read_bytes()
close = (FREEZE / 'FROZEN-CLOSING.txt').read_bytes()
original = old_source.read_bytes()
assert original == pre + head + b':= by\n' + (OLD / 'PROOF-BODY.txt').read_bytes() + close
read_paths = [
    Path('C:/Users/UIO/.agents/skills/math-theorem/SKILL.md'),
    Path('C:/Users/UIO/.agents/skills/math-theorem/references/prompt-library.md'),
    Path('C:/Users/UIO/.agents/skills/math-theorem/references/openai-workflow.md'),
    Path('C:/Users/UIO/.agents/skills/math-theorem/references/lean-verification.md'),
    old_source, OLD / 'REPORT.md', OLD / 'ROUTE.md', OLD / 'INPUT-BINDINGS.json',
    OLD / 'build_evidence.py', OLD / 'finalize_delivery.py',
    FREEZE / 'frozen-declaration.json', FREEZE / 'SOURCE-ROUTE.md',
    UNIT / 'source-review-01/SOURCE-REPORT.md', UNIT / 'source-review-01/SOURCE-VERDICT.json',
    UNIT / 'lead-execution-01/native02-actual-projection.json',
]
save('READ_ACK.json', {
    'schema': 'unit256-repair01-actual-read-ack-v1',
    'atUTC': datetime.now(timezone.utc).isoformat(), 'role': ROLE,
    'leadOwner': '01a1822b-1815-7f21-a1af-2e0b15ee67a5',
    'currentRoot': '01a17d3c-6dfd-7cc0-94ed-35d758a423a5',
    'fullModelRead': [binding(p) for p in read_paths],
    'sourceReadCoverage': [[1, 360], [361, 720], [721, 1053]],
    'displayTruncationRepairedByExactReread': [[650, 684]],
    'frozenHeadReadAsExactCurrentSourcePrefix': True,
    'frozenAssemblyByteEquality': True,
    'native02DiagnosticStdoutAndStderrReadCompletely': True,
    'oldAuthorPayloadCountVerifiedWithoutCopy': len(old_manifest['payload']),
    'oldSixZeroReleaseVerified': True,
    'upstreamQualifiedProofsAndOldActualTYPESNotRereviewed': True,
    'requestedModel': 'gpt-6.1-sol', 'requestedEffort': 'xhigh', 'freshContextRequested': True,
    'actualModel': None, 'actualBackend': None, 'actualEffort': None,
    'usage': {'input': None, 'cachedInput': None, 'output': None, 'reasoningSubset': None},
    'LeanLakePPAXServerNetworkUploadGitAPIChildrenSidebarGoalScheduleOperations': 0,
})

edits = [
    (757,
     '          · simpa only [Real.norm_eq_abs] using hFdelMeas.fst.norm.add\n',
     '          · exact (continuous_abs.measurable.comp hFdelMeas.fst).add\n',
     'Direct measurable composition with the continuous absolute-value function; retains the exact second component of Fdelete and all its inputs.'),
    (797,
     '      simpa only [hDeltaEq k i] using (hMI.sub hMdI).abs\n',
     '      simpa only [hDeltaEq k i, Pi.sub_apply] using (hMI.sub hMdI).abs\n',
     'Expands pointwise function subtraction at x; no change to the true signed deletion difference or integrability hypotheses.'),
    (1030,
     '    exact ⟨k₀, fun k hk => (hk₀ k hk).le.trans (add_le_add_right hSourceBound δ)⟩\n',
     '    exact ⟨k₀, fun k hk => (hk₀ k hk).le.trans (add_le_add hSourceBound (le_refl δ))⟩\n',
     'Adds the same δ on the right sides of both quantities via the two-argument addition monotonicity theorem; retains the existing positive-slack eventual bound.'),
]
old_text = original.decode('utf-8')
new_text = old_text
for line, old, new, reason in edits:
    assert old_text.splitlines(keepends=True)[line - 1] == old, line
    assert new_text.count(old) == 1, line
    new_text = new_text.replace(old, new)
new_raw = new_text.encode('utf-8')
assert new_raw.startswith(pre + head + b':= by\n') and new_raw.endswith(close)
proof = new_raw[len(pre + head + b':= by\n'):-len(close)]
assert new_raw == pre + head + b':= by\n' + proof + close
assert new_raw.count(b'\n') == original.count(b'\n') == 1053
assert new_raw.endswith(b'\n') and not new_raw.endswith(b'\n\n')
assert b'\r' not in new_raw and not new_raw.startswith(b'\xef\xbb\xbf')
(OUT / source_name).write_bytes(new_raw)
(OUT / 'PROOF-BODY.txt').write_bytes(proof)
diff = ''.join(difflib.unified_diff(old_text.splitlines(keepends=True), new_text.splitlines(keepends=True),
    fromfile='author-01/' + source_name, tofile='author-repair-01/' + source_name, n=5))
(OUT / 'EXACT-DIFF.patch').write_bytes(diff.encode('utf-8'))
save('EXACT-DIFF.json', {
    'schema': 'unit256-repair01-exact-three-proof-line-diff-v1',
    'before': binding(old_source), 'after': binding(OUT / source_name),
    'changes': [{'oldLine': line, 'newLine': line, 'oldUTF8': old, 'newUTF8': new, 'reason': reason}
                for line, old, new, reason in edits],
    'changedSourceLines': [line for line, _, _, _ in edits],
    'lineCountUnchanged': True, 'publicStatementAndPreambleAndClosingExactlyUnchanged': True,
    'mathematicalAssumptionsChanged': False, 'routeChanged': False,
    'actualTYPE': None, 'actualVALUE': None, 'recursiveAX': None, 'qualified': False,
})
input_paths = list(expected) + [OLD / 'INPUT-BINDINGS.json', OLD / 'PROOF-BODY.txt', OLD / 'REPORT.md', OLD / 'ROUTE.md',
    OLD / 'build_evidence.py', ROOT / 'library/Shao/OQ6/LiteralDeletedWeightedCosts.lean',
    ROOT / 'library/Shao/OQ6/NormalizedRemainderEnvelope.lean', ROOT / 'library/Shao/OQ6/ScalarObservationCoding.lean',
    ROOT / 'library/Shao/OQ6/QuantizedObservationCoding.lean']
save('INPUT-BINDINGS.json', {
    'schema': 'unit256-repair01-input-bindings-v1',
    'inputs': [binding(p) for p in input_paths],
    'allRequestedExactBindingsVerified': True,
    'oldManifestPayloads': old_manifest['payload'],
    'oldManifestPayloadsVerifiedWithoutModificationOrCopy': True,
    'inheritedBindingsAreHistoricalReadOnlyEvidence': binding(OLD / 'INPUT-BINDINGS.json'),
    'onlyRequiredCompleteUpstreamContractsParsedForInventory': True,
})

# Reuse the established complete source-derived inventory generator. The replacement
# prefix binds the repair directory and deliberately omits the old author's read ACK.
original_builder = (OLD / 'build_evidence.py').read_text(encoding='utf-8')
tail = original_builder[original_builder.index('source=SRC.read_bytes();'):]
prefix = '''from pathlib import Path
import hashlib, json, re
ROOT = Path('C:/game/shao lean')
OUT = ROOT / 'drafts/oq56/unit256/author-repair-01'
FREEZE = ROOT / 'drafts/oq56/unit256/freeze-02'
SRC = OUT / 'OriginalLevelDependentLiteralWeightedConsumer.lean'
assert not (OUT/'FINALWRITE.json').exists()
def binding(path):
    p = Path(path); b = p.read_bytes()
    return {'path': p.as_posix(), 'sha256': hashlib.sha256(b).hexdigest(), 'bytes':len(b), 'LF':b.count(b'\\n')}
def text(path): return Path(path).read_text(encoding='utf-8')
def save(name, value):
    value.update({'generationRole':'/root/oq56_unit256_author_repair01',
      'evidenceClass':'PURE_SOURCE_DERIVED_STATIC_NOT_MACHINE_OWNER',
      'actualTYPE':None,'actualVALUE':None,'recursiveAX':None,'qualified':False})
    (OUT / name).write_bytes((json.dumps(value, ensure_ascii=False, indent=2)+'\\n').encode('utf-8'))

'''
(OUT / 'build_evidence.py').write_bytes((prefix + tail).encode('utf-8'))
print(json.dumps({'readACK': binding(OUT/'READ_ACK.json'), 'source': binding(OUT/source_name),
                  'proof': binding(OUT/'PROOF-BODY.txt'), 'changedLines': [757, 797, 1030],
                  'oldPayloadsVerified': len(old_manifest['payload'])}, ensure_ascii=False))
