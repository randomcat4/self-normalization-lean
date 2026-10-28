from pathlib import Path
from datetime import datetime, timezone
import difflib
import hashlib
import json
import re

ROOT = Path('C:/game/shao lean')
UNIT = ROOT / 'drafts/oq56/unit257'
OUT = UNIT / 'author-repair-01'
OLD = UNIT / 'author-01'
SRC = OUT / 'OriginalLevelDependentStrictMomentFrontier.lean'


def read(p):
    return json.loads(p.read_text(encoding='utf-8'))


def bind(p):
    b = p.read_bytes()
    return {'path': p.as_posix(), 'sha256': hashlib.sha256(b).hexdigest(),
            'bytes': len(b), 'LF': b.count(b'\n')}


def save(name, value):
    (OUT / name).write_bytes((json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode('utf-8'))


inputs = read(OUT / 'INPUT-BINDINGS.json')['inputs']
for x in inputs:
    actual = bind(Path(x['path']))
    assert all(actual[k] == x[k] for k in ['path', 'sha256', 'bytes', 'LF']), x['path']
source = SRC.read_bytes()
oldsource = (OLD / SRC.name).read_bytes()
insertions = [
    '    change Filter.Tendsto sourceCostη Filter.atTop (nhds sourceCost0) at hSourceLim\n',
    '    change Filter.Tendsto compactCostη Filter.atTop (nhds compactCost0) at hCostLim\n',
]
restored = source
for s in insertions:
    assert restored.count(s.encode('utf-8')) == 1
    restored = restored.replace(s.encode('utf-8'), b'', 1)
assert restored == oldsource
diff = list(difflib.unified_diff(oldsource.decode('utf-8').splitlines(keepends=True),
    source.decode('utf-8').splitlines(keepends=True),
    fromfile=(OLD / SRC.name).as_posix(), tofile=SRC.as_posix()))
assert ''.join(diff).encode('utf-8') == (OUT / 'exact.patch').read_bytes()
plus = [s for s in diff if s.startswith('+') and not s.startswith('+++')]
minus = [s for s in diff if s.startswith('-') and not s.startswith('---')]
assert len(plus) == 2 and len(minus) == 0
assert [s[1:] for s in plus] == insertions

f = UNIT / 'freeze-01'
pre, head, close = [(f / n).read_bytes() for n in
    ['FROZEN-PREAMBLE.txt', 'FROZEN-HEAD.txt', 'FROZEN-CLOSING.txt']]
proof = (OUT / 'PROOF-BODY.txt').read_bytes()
assert source == pre + head + b':= by\n' + proof + b'\n' + close
oldproof = (OLD / 'PROOF-BODY.txt').read_bytes()
for s in insertions:
    proof = proof.replace(s.encode('utf-8'), b'', 1)
assert proof + b'\n' == oldproof

prod, oldprod = [read(p / 'PRODUCER-TYPES.json') for p in [OUT, OLD]]
loc, oldloc = [read(p / 'LOCAL-CONTEXTS.json') for p in [OUT, OLD]]
pat, oldpat = [read(p / 'BINDING-TYPES.json') for p in [OUT, OLD]]
assert prod['contracts'] == oldprod['contracts']
assert prod['applications'] == oldprod['applications']
assert len(loc['declarations']) == len(oldloc['declarations'])
rhs_changes = []
for a, b in zip(oldloc['declarations'], loc['declarations']):
    for key in ['kind', 'name', 'fullHeaderAndExplicitSourceType', 'fullInferredSourceType']:
        assert a[key] == b[key], (key, a['name'])
    if a['fullRHS'] != b['fullRHS']:
        rhs_changes.append(b['name'])
assert rhs_changes == ['hSourceEvent', 'hCostEvent'], rhs_changes
assert len(pat['allPatternBindings']) == len(oldpat['allPatternBindings'])
for a, b in zip(oldpat['allPatternBindings'], pat['allPatternBindings']):
    for key in ['name', 'fullType', 'fullSourceLetContext', 'origin']:
        assert a[key] == b[key], (key, a['name'])
    assert b['lexicalScopeEndLine'] >= b['commandStartLine']
lines = source.splitlines(keepends=True)
offsets = [0]
for line in lines:
    offsets.append(offsets[-1] + len(line))
slices = loc['declarations'] + loc['bindingCommands']
for item in slices:
    s = item['slice']
    raw = source[s['startByte']:s['endByteExclusive']]
    assert raw.decode('utf-8') == s['utf8']
    assert hashlib.sha256(raw).hexdigest() == s['sha256']
    assert s['startByte'] == offsets[s['startLine'] - 1]
    assert s['endByteExclusive'] == offsets[s['endLine']]
    assert item['lexicalScopeEndLine'] >= s['startLine']


def single_line_slice(command):
    start = source.index(command.encode('utf-8'))
    end = start + len(command.encode('utf-8'))
    n = source[:start].count(b'\n') + 1
    return {'startLine': n, 'endLine': n, 'startByte': start,
            'endByteExclusive': end, 'sha256': hashlib.sha256(source[start:end]).hexdigest(),
            'utf8': command}


bindings = {x['name']: x for x in pat['allPatternBindings']}
decls = {x['name']: x for x in loc['declarations']}
alignments = []
for hyp, event, func, limit, command in [
    ('hSourceLim', 'hSourceEvent', 'sourceCostη', 'sourceCost0', insertions[0]),
    ('hCostLim', 'hCostEvent', 'compactCostη', 'compactCost0', insertions[1]),
]:
    b, d = bindings[hyp], decls[event]
    expected = f'Filter.Tendsto {func} Filter.atTop (nhds {limit})'
    assert b['fullType'] == expected
    assert command.strip() == f'change {expected} at {hyp}'
    aligned = {
        'hypothesis': hyp,
        'enclosingEvent': event,
        'fullLogicalSourceTypeBeforeUnderProducerLetContext': b['fullType'],
        'fullProducerSourceLetContext': b['fullSourceLetContext'],
        'beforeActualElaborationRepresentation': 'The failed native diagnostic expands the same producer function and limit while the sub_const argument remains the current local named cost. This source inventory is not machine PP.',
        'afterChangeFullType': expected,
        'changeIsOnlyDefinitionalTypeAlignment': True,
        'subConstFullType': f'Filter.Tendsto (fun k : ℕ => {func} k - {limit}) Filter.atTop (nhds ({limit} - {limit}))',
        'absFullType': f'Filter.Tendsto (fun k : ℕ => |{func} k - {limit}|) Filter.atTop (nhds |{limit} - {limit}|)',
        'eventuallyNeighbourhoodGoalBeforeSimp': f'∀ᶠ (y : ℝ) in nhds |{limit} - {limit}|, y < τ',
        'eventuallyNeighbourhoodGoalAfterOnlySubSelfAbsZero': '∀ᶠ (y : ℝ) in nhds (0 : ℝ), y < τ',
        'sourceOfNeighbourhoodEvent': 'eventually_lt_nhds (hτ : (0 : ℝ) < τ)',
        'eventFullType': d['fullHeaderAndExplicitSourceType'].split(':', 1)[1].strip(),
        'eventFullRHS': d['fullRHS'],
        'changeSlice': single_line_slice(command),
        'enclosingEventSlice': d['slice'],
        'changeLocalScope': {'startLine': single_line_slice(command)['startLine'],
                            'endLine': d['slice']['endLine'],
                            'description': 'Only within this have proof; the surrounding theorem statement and consumer packet are unchanged.'},
        'newMathematicalPremises': [],
        'newTopLevelDeclaration': False,
        'machineElaborated': False,
        'evidenceClass': 'PURE_SOURCE_DERIVED_STATIC_NOT_MACHINE_PP',
    }
    alignments.append(aligned)
save('CHANGE-TYPE-ALIGNMENTS.json', {
    'schema': 'unit257-repair01-two-definitional-hypothesis-type-alignments-v1',
    'source': bind(SRC),
    'originalSource': bind(OLD / SRC.name),
    'native01ActualProjection': bind(UNIT / 'lead-execution-01/native01-actual-projection.json'),
    'completeAlignments': alignments,
    'newDeclarationsOrPremises': False,
    'APIChange': False,
    'machinePP': False,
    'qualified': False,
})

formats = []
for p in sorted(OUT.iterdir()):
    if p.is_file() and p.name not in ['REPAIR-CHECK.json', 'MANIFEST.json', 'FINALWRITE.json']:
        b = p.read_bytes()
        assert b.decode('utf-8').encode('utf-8') == b, p
        assert not b.startswith(b'\xef\xbb\xbf') and b'\r' not in b, p
        assert b.endswith(b'\n') and not b.endswith(b'\n\n'), p
        formats.append(bind(p))
for x in inputs:
    actual = bind(Path(x['path']))
    assert actual == {k: x[k] for k in ['path', 'sha256', 'bytes', 'LF']}, x['path']
check = {
    'schema': 'unit257-repair01-local-exact-source-static-check-v1',
    'atUTC': datetime.now(timezone.utc).isoformat(),
    'STATUS': 'PASS_SOURCE_STATIC_ONLY',
    'source': bind(SRC),
    'proof': bind(OUT / 'PROOF-BODY.txt'),
    'patch': bind(OUT / 'exact.patch'),
    'frozenHead': bind(f / 'FROZEN-HEAD.txt'),
    'immutableInputBindingsChecked': len(inputs),
    'allOldInputBytesUnchanged': True,
    'exactSourceInsertedLines': [x['changeSlice']['startLine'] for x in alignments],
    'sourceInsertions': len(plus),
    'sourceDeletions': len(minus),
    'removeOnlyTwoInsertedLinesRestoresOldSourceExactly': True,
    'sameFrozenPreambleFull517LFHeadAndClosing': True,
    'completeSourceAssemblyWithExplicitInherited1LFBoundarySeparator': True,
    'allOriginalProofTokensUnchangedApartFromTwoTypeAlignmentCommands': True,
    'allProducerFullDeclarationsArgumentsAndReturnTypesIdenticalToOld': True,
    'producerContracts': len(prod['contracts']),
    'producerApplications': len(prod['applications']),
    'localFullTypesHeadersInferredTypesRHSAndScopes': len(loc['declarations']),
    'onlyChangedLocalRHSNames': rhs_changes,
    'patternCommands': len(loc['bindingCommands']),
    'patternBoundFullTypes': len(pat['allPatternBindings']),
    'allPatternFullTypesSourceContextsOriginsIdenticalToOld': True,
    'allSourceSlicesLineByteHashTextRoundtrip': len(slices),
    'typeAlignmentFullStaticDerivations': bind(OUT / 'CHANGE-TYPE-ALIGNMENTS.json'),
    'formattedPayloadsChecked': len(formats),
    'allTextUTF8NoBOMNoCRSingleFinalLF': True,
    'uniquePublicTheoremCount': len(re.findall(r'(?m)^theorem\s+', source.decode('utf-8'))),
    'forbiddenTokens': re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', source.decode('utf-8')),
    'mathematicalDeclarationPremiseQuantifierConstantCostEtaChanges': False,
    'staticInventoryIsNotMachinePP': True,
    'actualOwnerCount': None,
    'actualTYPE': None,
    'actualVALUE': None,
    'actualAX': None,
    'kernelExecuted': False,
    'axiomAuditExecuted': False,
    'sourceAccepted': False,
    'independentAffectedReviewPending': True,
    'machinePending': True,
    'qualified': False,
    'operations': dict.fromkeys(['Lean', 'lake', 'PP', 'AX', 'server', 'network',
        'upload', 'Git', 'API', 'children', 'sidebar', 'Goal', 'schedule'], 0),
}
assert check['uniquePublicTheoremCount'] == 1 and check['forbiddenTokens'] == []
save('REPAIR-CHECK.json', check)
print(json.dumps({k: check[k] for k in ['STATUS', 'source', 'proof',
    'immutableInputBindingsChecked', 'exactSourceInsertedLines', 'sourceInsertions',
    'sourceDeletions', 'producerContracts', 'producerApplications',
    'localFullTypesHeadersInferredTypesRHSAndScopes', 'patternCommands',
    'patternBoundFullTypes', 'allSourceSlicesLineByteHashTextRoundtrip',
    'qualified', 'machinePending']}, ensure_ascii=False))
