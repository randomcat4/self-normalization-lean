from pathlib import Path
import datetime
import hashlib
import json
import re

BASE = Path('C:/game/shao lean/drafts/oq56/unit248')
OUT = BASE / 'source-review-repair-02'
NOW = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat()
SHA = lambda b: hashlib.sha256(b).hexdigest()

def bind(path):
    p = Path(path)
    b = p.read_bytes()
    return {'path': p.as_posix(), 'sha256': SHA(b), 'bytes': len(b)}

def save(name, value):
    (OUT / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n',
                            encoding='utf-8', newline='\n')

def verify(v):
    assert bind(v['path']) == {k: v[k] for k in ['path', 'sha256', 'bytes']}, v['path']

activation = json.loads((BASE / 'affected-review-activation-02/ACTIVATION.json').read_bytes())
assert len(activation['inputs']) == 55
for v in activation['inputs']:
    verify(v)
author_m = json.loads((BASE / 'author-repair-02/MANIFEST.json').read_bytes())
for group in ['inputs', 'payloads', 'readOnlyQualifiedInterfaceBindings']:
    for v in author_m[group]:
        verify(v)
author_r = json.loads((BASE / 'author-repair-02/lastzeroRELEASE.json').read_bytes())
assert author_r['FINALWRITE'] and author_r['noFurtherWritesAfterThisRelease']
assert len(author_r['sixZero']) == 6 and all(v == 0 for v in author_r['sixZero'].values())
verify(author_r['manifest'])

oldp = BASE / 'author-repair-01/OriginalSameWitnessPhysicalPaidTailApplication.lean'
newp = BASE / 'author-repair-02/OriginalSameWitnessPhysicalPaidTailApplication.lean'
old, new = oldp.read_bytes(), newp.read_bytes()
assert SHA(old) == '50fea02c741964634c5bf3db5e198bc647577f04814df5310682a9485ef30255'
assert SHA(new) == '50cc9872e1d6148e4a81f0d49da391a1b4b749b682c91b4ba347ae22bad00433'
assert len(old) == 256777 and len(new) == 256822
assert old.count(b'\n') == 3964 and new.count(b'\n') == 3965
assert b'\r' not in new and not new.startswith(b'\xef\xbb\xbf')
marker = b'        have hMeas220 :\n'
line = '            letI : MeasurableSpace Ω := mΩ\n'.encode()
assert len(line) == 45 and old.count(marker) == new.count(marker) == 1
at = old.index(marker) + len(marker)
assert at == 241315
assert old[:at] + line + old[at:] == new
assert new[:at] + new[at + len(line):] == old
assert new[at:at + len(line)] == line
assert old[:at] == new[:at] and old[at:] == new[at + 45:]
oldtext, newtext = old.decode(), new.decode()

oldctx = json.loads((BASE / 'author-repair-01/ACTUAL-PROP-CONTEXTS.json').read_bytes())
newctx = json.loads((BASE / 'author-repair-02/ACTUAL-PROP-CONTEXTS.json').read_bytes())
f2 = json.loads((BASE / 'freeze-02/INTERFACE-INVENTORY.json').read_bytes())
f3 = json.loads((BASE / 'freeze-03/INTERFACE-INVENTORY.json').read_bytes())
freeze = json.loads((BASE / 'freeze-03/frozen-declaration.json').read_bytes())
patch = json.loads((BASE / 'author-repair-02/PATCH.json').read_bytes())
assert patch['oldByteOffset'] == at and patch['insertedLine'].encode() == line
assert patch['insertedBytes'] == 45 and patch['changeCountDerived'] == 1
assert freeze['expectedExactOneDeltaSource'] == {'sha256': SHA(new), 'bytes': len(new), 'LF': new.count(b'\n')}

coordinate_checks = []
def checkcoords(a, b, path=''):
    if isinstance(a, dict):
        if {'byteOffset', 'line', 'column'}.issubset(a):
            off = a['byteOffset']
            expected = off + (45 if off >= at else 0)
            assert b['byteOffset'] == expected, (path, off, expected, b)
            pre = new[:expected].decode()
            assert b['line'] == pre.count('\n') + 1, (path, 'line')
            assert b['column'] == len(pre.rsplit('\n', 1)[-1]) + 1, (path, 'column')
            coordinate_checks.append({'path': path, 'oldByteOffset': off, 'current': b})
        else:
            for k, v in a.items():
                if k in b:
                    checkcoords(v, b[k], path + '/' + k)
    elif isinstance(a, list):
        for i, (x, y) in enumerate(zip(a, b)):
            checkcoords(x, y, path + '/' + str(i))

checkcoords(oldctx, newctx)
assert len(coordinate_checks) == 353

def stripcoords(x):
    if isinstance(x, dict):
        if {'byteOffset', 'line', 'column'}.issubset(x):
            return '<independently-verified-coordinate>'
        return {k: stripcoords(v) for k, v in x.items()}
    if isinstance(x, list):
        return [stripcoords(v) for v in x]
    return x

for k in ['publicOrdinary', 'approvedOptionalOrdinary', 'actualSameModelChoices',
          'APIImplicitInstances', 'additionalPureLogicalPackages', 'proofIntroductoryCoordinates']:
    assert stripcoords(oldctx[k]) == stripcoords(newctx[k]), k
assert oldctx['completeUniqueContexts'] == newctx['completeUniqueContexts'][:-1]
inner = newctx['completeUniqueContexts'][-1]
assert inner['id'] == 'C07T' and inner['parent'] == 'C07'
assert inner['text'] == 'letI : MeasurableSpace Ω := mΩ\n' and inner['typeLocalOnly']
assert oldctx['approvedInstances'] == newctx['approvedInstances'][:8]
newinst = newctx['approvedInstances'][-1]
assert newinst['name'] == 'typeLocalOriginalOmegaForMeas220'
assert newinst['type'] == 'MeasurableSpace Ω' and newinst['rhs'] == 'mΩ'
assert newinst['typeLocalOnly'] and not newinst['newHypothesis'] and newinst['used']
assert newinst['sourceCoordinate'] == {'byteOffset': at, 'line': 3723, 'column': 1}
assert new[at:at + 45].decode().strip() == 'letI : MeasurableSpace Ω := mΩ'

facts = []
for a, b in zip(oldctx['fullFrozenPropositions'], newctx['fullFrozenPropositions']):
    name = a['name']
    assert b['name'] == name
    if name == 'hMeas220':
        assert b['fullType'] == '    letI : MeasurableSpace Ω := mΩ\n' + a['fullType']
        assert b['previousFullTypeSHA256'] == SHA(a['fullType'].encode())
        assert b['typeLocalInnerContextId'] == 'C07T'
    else:
        assert a['fullType'] == b['fullType'], name
    for k, v in a.items():
        if k not in ['fullType', 'actualBinding', 'previousFullTypeSHA256']:
            assert b[k] == v, (name, k)
        if k == 'previousFullTypeSHA256' and name != 'hMeas220':
            assert b[k] == v, (name, k)
    facts.append({'name': name, 'fullType': b['fullType'], 'contextId': b['contextId'],
                  'typeLocalInnerContextId': b.get('typeLocalInnerContextId'),
                  'scope': b.get('scope'), 'actualBinding': b['actualBinding'],
                  'oldFullTypeSHA256': SHA(a['fullType'].encode()),
                  'currentFullTypeSHA256': SHA(b['fullType'].encode()),
                  'changedThisRepair': name == 'hMeas220',
                  'coverage': 'complete-current-affected-read' if name == 'hMeas220' else 'exact-complete-prior-review-reused'})
assert len(facts) == 32 and sum(x['changedThisRepair'] for x in facts) == 1
for k in ['publicOrdinary', 'optionalOrdinary', 'APIImplicitInstances']:
    assert f2[k] == f3[k], k
assert f2['approvedInstances'] == f3['approvedInstances'][:8]
assert f3['approvedInstances'][-1] == freeze['newScopedInstanceOption']
for a, b in zip(f2['frozenProofFacts'], f3['frozenProofFacts']):
    assert a['name'] == b['name']
    if a['name'] == 'hMeas220':
        assert b['fullType'] == '    letI : MeasurableSpace Ω := mΩ\n' + a['fullType']
    else:
        assert a == b
    c = next(x for x in newctx['fullFrozenPropositions'] if x['name'] == b['name'])
    assert c['fullType'] == b['fullType']

# Full changed type is independently matched to literal source, including its := boundary.
rx = re.compile(r'\s+|[()\[\]{};,]|[^\s()\[\]{};,]+')
tok = lambda t: [m.group() for m in rx.finditer(t) if not m.group().isspace()]
m = re.search(r'^        have hMeas220\s*:', newtext, re.M)
meas = next(x for x in newctx['fullFrozenPropositions'] if x['name'] == 'hMeas220')
ts, want = tok(newtext[m.end():]), tok(meas['fullType'])
assert ts[:len(want)] == want and ts[len(want)] == ':='
assert patch['fullAffectedTypeAfter'] == meas['fullType'] == freeze['onlyChangedFullProp']['after']
assert patch['fullAffectedTypeBefore'] == freeze['onlyChangedFullProp']['before']
start, end = newtext.index('        have hMeas220 :'), newtext.index('        have hPhysicalMeasurable :')
block = newtext[start:end]
assert block.count('letI : MeasurableSpace Ω := mΩ') == 1
assert block.index('letI : MeasurableSpace Ω := mΩ') < block.index('let g : Ω → ℝ')
type_end = block.index(') :=\n') + 2
rhs = block[type_end:]
oldstart, oldend = oldtext.index('        have hMeas220 :'), oldtext.index('        have hPhysicalMeasurable :')
oldblock = oldtext[oldstart:oldend]
oldrhs = oldblock[oldblock.index(') :=\n') + 2:]
assert rhs == oldrhs
assert 'letI' not in rhs and 'Ω mΩ μ hμProbability h hh hh2 hhsymm hcenter hprojectionsecond' in rhs
assert 'n hn 0 (by norm_num) (by norm_num) 512 (by norm_num)' in rhs

for file in ['FROZEN-PREAMBLE.txt', 'FROZEN-HEAD.txt', 'FROZEN-INITIAL-INTRO.txt', 'FROZEN-H247-CALL.txt']:
    b = (BASE / 'freeze-01' / file).read_bytes()
    assert b in new and new.index(b) == old.index(b), file
closing = (BASE / 'freeze-02/FROZEN-CLOSING.txt').read_bytes()
assert old.endswith(closing) and new.endswith(closing)
assert len(newctx['publicOrdinary']) == 145 and len(newctx['approvedOptionalOrdinary']) == 147
assert len(newctx['additionalPureLogicalPackages']) == 8
assert len(newctx['approvedInstances']) == 9 and len(newctx['APIImplicitInstances']) == 5
assert len(newctx['actualSameModelChoices']) == 2
assert sum(x['used'] for x in newctx['approvedInstances']) == 8
assert len(oldctx['actualHaveDeclarations']) == len(newctx['actualHaveDeclarations']) == 38
for a, b in zip(oldctx['actualHaveDeclarations'], newctx['actualHaveDeclarations']):
    assert a['name'] == b['name'] and a['indent'] == b['indent']
    assert b['line'] == a['line'] + (1 if a['line'] >= 3723 else 0)

qualified_path = Path('C:/game/shao lean/drafts/oq56/unit220/qualified-evidence.json')
qualified = json.loads(qualified_path.read_bytes())
verify(qualified['metadata'])
metadata = json.loads(Path(qualified['metadata']['path']).read_bytes())
entry = metadata['entries'][0]
t = entry['type']
assert len(t.encode()) == 22108 and len(t.splitlines()) == 296
assert SHA(t.encode()) == 'b1a645022d16f2ae31b71ea7b2ff506d05952e0d8e5b281e5be59aaa550c9cdf'
assert entry['name'] == 'Shao.OQ6.OriginalClippedStatisticMeasurable.actual_normalized_compact_clipped_observables'
assert qualified['qualified'] and qualified['kernelChecked']
assert qualified['originalObject'] == qualified['firstOriginalObject']
assert metadata['source']['sha256'] == qualified['source']['sha256']
assert metadata['object']['sha256'] == qualified['originalObject']['sha256']
assert '@MeasurableSpace.pi.{0, u}' in '\n'.join(t.splitlines()[253:])
assert 'mΩ)' in '\n'.join(t.splitlines()[266:279])

diag = json.loads((BASE / 'lead-execution-02/native-complete-diagnostic-projection.json').read_bytes())
error = diag['completeErrorBlocks'][0]
assert len(diag['completeErrorBlocks']) == diag['sourceErrorsDerived'] == 1
assert len(error.encode()) == 5264 and SHA(error.encode()) == '927a55441b499ae29bb998f5a0d7cc6533c41a89144635f1825c87237be935a5'
assert diag['actualRC'] == 1 and diag['sourceWarningsDerived'] == 8 and diag['object'] is None
assert diag['allOwnedEnded'] and diag['beforeAfterExact'] and diag['preservationEqual']
assert diag['protectedRecordsDerived'] == 25348 and not diag['timedOut']
assert not diag['cleanupEvents'] and diag['ownershipIssue'] is None

result = {'schema': 'oq56-unit248-independent-one-type-local-line-affected02-verification-v1',
 'atUTC': NOW(), 'oldSource': bind(oldp), 'source': bind(newp), 'sourceLF': 3965,
 'wholeByteForwardSingleInsertionExact': True, 'wholeByteReverseTo50feaExact': True,
 'insertedLine': line.decode(), 'insertedBytes': 45, 'oldAndNewInsertionByteOffset': at,
 'insertionLine': 3723, 'unchangedWholeIntervals': [{'oldStart': 0, 'oldEndExclusive': at, 'newStart': 0, 'newEndExclusive': at, 'sha256': SHA(old[:at])}, {'oldStart': at, 'oldEndExclusive': len(old), 'newStart': at + 45, 'newEndExclusive': len(new), 'sha256': SHA(old[at:])}],
 'allOtherProofBytesExact': True, 'publicHeadOriginal16H247CallAndClosingExact': True,
 'old8InstanceRowsExact': True, 'new9thInstance': newinst,
 'all145Public147Optional5APIAnd2ChoicesTypeRHSScopeExact': True,
 'old11ContextsExact': True, 'newTypeLocalContext': inner,
 'full32Propositions': facts, 'allOther31FullPropsExact': True,
 'all8PureLogicalPackagesExact': True,
 'inheritedCoordinateChecksDerived': len(coordinate_checks),
 'newInstanceCoordinateChecked': True, 'totalCurrentCoordinateRecordsDerived': len(coordinate_checks) + 1,
 'coordinateChecks': coordinate_checks,
 'qualified220CompleteTYPERead': {'metadata': bind(qualified['metadata']['path']), 'name': entry['name'], 'typeSHA256': SHA(t.encode()), 'typeBytes': len(t.encode()), 'typeLines': len(t.splitlines()), 'readAllLines': [[1, 150], [151, 296]], 'deletedSubtypePiOriginalmOmega': True, 'source': qualified['source'], 'FIRSTO': qualified['originalObject'], 'proofOrChecksReplayed': False},
 'native02Failure': {k: diag[k] for k in ['receipt', 'config', 'actualRC', 'seconds', 'sourceErrorsDerived', 'sourceWarningsDerived', 'object', 'allOwnedEnded', 'protectedRecordsDerived', 'beforeAfterExact', 'preservationEqual', 'timedOut', 'cleanupEvents', 'ownershipIssue']},
 'native03Status': 'NOT_RUN_BY_REVIEWER_PENDING_LEAD', 'current248ActualTYPECounts': None,
 'authorManifestCountsDerived': {k: len(author_m[k]) for k in ['inputs', 'payloads', 'readOnlyQualifiedInterfaceBindings']},
 'noOldProofOr247TYPEReviewReplay': True, 'noMathematicalExecution': True, 'P168Readopted': False}
save('INDEPENDENT-DELTA-VERIFICATION.json', result)
save('AFFECTED-BLOCKS.json', {'schema': 'oq56-unit248-full-affected02-blocks-read-v1', 'source': bind(newp),
 'fullCurrentHMeas220TypeAndCall': block, 'fullCurrentHMeas220Type': meas['fullType'], 'fullCurrentHMeas220RHS': rhs,
 'qualified220FullActualTYPE': t, 'qualified220FullActualTYPEBinding': result['qualified220CompleteTYPERead'],
 'fullNative02ErrorBlock': error, 'native02ErrorSHA256': SHA(error.encode()),
 'newTypeLocalInstance': newinst, 'newTypeLocalContext': inner,
 'allReadSourceLineBlocks': [[2053,2063],[3519,3529],[3720,3782],[3798,3804],[3959,3965]],
 'whole50feaPriorSourceAndCompletePriorReviewReused': True})
print(json.dumps({'PASS': True, 'sourceSHA256': SHA(new), 'insertionBytes': 45,
 'inheritedCoordinates': len(coordinate_checks), 'newCoordinate': 1,
 'full32Props': 32, 'onlyChangedProp': 'hMeas220', 'instances': 9,
 'public': 145, 'optional': 147, 'API': 5,
 'qualified220TYPEReadAll296Lines22108Bytes': True,
 'native02': 'RC1/oneerror/eightwarnings/noO/allended', 'kernelPending': True,
 'authorManifestCounts': result['authorManifestCountsDerived']}, ensure_ascii=False))
