from pathlib import Path
import hashlib
import json

OUT = Path('C:/game/shao lean/drafts/oq56/unit256/author-repair-01')
OLD = OUT.parent / 'author-01'
FREEZE = OUT.parent / 'freeze-02'
NAME = 'OriginalLevelDependentLiteralWeightedConsumer.lean'

def binding(path):
    raw = Path(path).read_bytes()
    return {'path': Path(path).as_posix(), 'sha256': hashlib.sha256(raw).hexdigest(),
            'bytes': len(raw), 'LF': raw.count(b'\n')}

def load(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))

def save(name, value):
    (OUT / name).write_bytes((json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode('utf-8'))

assert not (OUT / 'FINALWRITE.json').exists()
old_raw = (OLD / NAME).read_bytes()
new_raw = (OUT / NAME).read_bytes()
old_lines = old_raw.decode('utf-8').splitlines(keepends=True)
new_lines = new_raw.decode('utf-8').splitlines(keepends=True)
changed_lines = [i for i, (a, b) in enumerate(zip(old_lines, new_lines), 1) if a != b]
assert changed_lines == [757, 797, 1030]
assert len(old_lines) == len(new_lines) == 1053
pre = (FREEZE / 'FROZEN-PREAMBLE.txt').read_bytes()
head = (FREEZE / 'FROZEN-HEAD.txt').read_bytes()
close = (FREEZE / 'FROZEN-CLOSING.txt').read_bytes()
proof = (OUT / 'PROOF-BODY.txt').read_bytes()
assert new_raw == pre + head + b':= by\n' + proof + close
assert new_raw.decode('utf-8').encode('utf-8') == new_raw
assert b'\r' not in new_raw and not new_raw.startswith(b'\xef\xbb\xbf')
assert new_raw.endswith(b'\n') and not new_raw.endswith(b'\n\n')
old_builder = (OLD / 'build_evidence.py').read_text(encoding='utf-8')
new_builder = (OUT / 'build_evidence.py').read_text(encoding='utf-8')
marker = 'source=SRC.read_bytes();'
assert new_builder[new_builder.index(marker):] == old_builder[old_builder.index(marker):]
old_contexts = load(OLD / 'LOCAL-CONTEXTS.json')
new_contexts = load(OUT / 'LOCAL-CONTEXTS.json')
assert len(old_contexts['declarations']) == len(new_contexts['declarations'])
old_bindings = load(OLD / 'BINDING-TYPES.json')
new_bindings = load(OUT / 'BINDING-TYPES.json')
assert old_bindings['allRcasedIntroducedObtainedFunextNames'] == new_bindings['allRcasedIntroducedObtainedFunextNames']
assert old_contexts['binderCommands'] != []
assert [(d['kind'], d['slice']['utf8'], d['lexicalScopeEndLine']) for d in old_contexts['binderCommands']] == [
       (d['kind'], d['slice']['utf8'], d['lexicalScopeEndLine']) for d in new_contexts['binderCommands']]
changed_contexts = []
for old, new in zip(old_contexts['declarations'], new_contexts['declarations']):
    assert (old['kind'], old['name'], old['slice']['sourceStartLine'], old['slice']['sourceEndLine']) == (
        new['kind'], new['name'], new['slice']['sourceStartLine'], new['slice']['sourceEndLine'])
    for field in ('headerAndFullSourceType', 'completeInferredType', 'lexicalScopeEndLine'):
        assert old.get(field) == new.get(field), (new['name'], field)
    if old['completeRHS'] != new['completeRHS']:
        changed_contexts.append({'name': new['name'], 'oldCompleteLocal': old, 'newCompleteLocal': new})
assert [d['name'] for d in changed_contexts] == ['hCurrent', 'hFdeleteMeas', 'hDeltaI', 'hDI', 'hSourceEventually']
all_slices = [d['slice'] for d in new_contexts['declarations']] + [d['slice'] for d in new_contexts['binderCommands']]
for item in all_slices:
    raw = new_raw[item['startByte']:item['endByteExclusive']]
    assert raw.decode('utf-8') == item['utf8']
    assert hashlib.sha256(raw).hexdigest() == item['sha256']
    start = item['sourceStartLine']
    end = item['sourceEndLine']
    assert raw.decode('utf-8') == ''.join(new_lines[start - 1:end])
necessary_names = {'Fdelete', 'hMI', 'hMdI', 'hDeltaEq', 'hDeltaBound', 'hSourceBound', 'htail'}
support_declarations = [d for d in new_contexts['declarations'] if d['name'] in necessary_names]
direct_bindings = [d for d in new_bindings['allRcasedIntroducedObtainedFunextNames']
                   if d['sourceLine'] in (737, 738, 1029)]
assert [d['name'] for d in direct_bindings] == ['Fdel', 'hFdelMeas', 'hFdelPoint', 'FU', 'hFUMeas',
    'hFULocalPoint', 'hFUFullRestrictionMeas', 'hFUPoint', 'k₀', 'hk₀']
save('CHANGED-CONTEXTS.json', {
    'schema': 'unit256-repair01-complete-affected-locals-and-bindings-v1',
    'source': binding(OUT / NAME), 'before': binding(OLD / NAME),
    'changedLines': changed_lines, 'changedLocals': changed_contexts,
    'unchangedSupportingLocalsWithFullTypesRHSAndSource': support_declarations,
    'directBindingsWithFullSourceTypesAndOrigins': direct_bindings,
    'allBindingTypesAndNamesIdentical': True,
    'allDeclarationTypesAndLexicalScopesIdentical': True,
    'fullCurrentInventory': [binding(OUT / n) for n in ('LOCAL-CONTEXTS.json', 'BINDING-TYPES.json', 'PRODUCER-TYPES.json')],
    'fullHistoricalInventoryRetainedReadOnly': [binding(OLD / n) for n in ('LOCAL-CONTEXTS.json', 'BINDING-TYPES.json', 'PRODUCER-TYPES.json')],
    'evidenceClass': 'PURE_SOURCE_DERIVED_STATIC_NOT_MACHINE_OWNER',
    'actualTYPE': None, 'actualVALUE': None, 'recursiveAX': None, 'qualified': False,
})
old_manifest = load(OLD / 'MANIFEST.json')
for item in old_manifest['payload']:
    assert binding(item['path']) == item, item['path']
expected_old = {
    'MANIFEST.json': ('b26c98712d21495cc115b0eb88329a71610fb93bf2bc114b725a96d3ca90a6b8', 9112),
    'FINALWRITE.json': ('8c17b37feaf3ad246e049c6c7300146284587d8bfca66137b86c8cf3a7a5374a', 2925),
}
for name, (sha, size) in expected_old.items():
    actual = binding(OLD / name)
    assert (actual['sha256'], actual['bytes']) == (sha, size)
static = load(OUT / 'STATIC-CHECK.json')
assert static['forbiddenHits'] == [] and static['publicTheoremCount'] == 1
assert static['topLevelHelpersDefsInstances'] == 0
assert static['frozenHeadExact'] and static['whole255FirstPacketLiteralModuloOuterParenthesesAndIndentation']
assert static['source'] == binding(OUT / NAME)
assert static['actualMachineOwnerCount'] is None and static['actualTYPELF'] is None
assert static['actualVALUECount'] is None and static['recursiveAX'] is None
assert static['qualified'] is False and static['kernelExecuted'] is False and static['axiomAuditExecuted'] is False
diagnostic = load(OUT.parent / 'lead-execution-01/native02-actual-projection.json')
assert diagnostic['exit_code'] == 1 and diagnostic['object_after'] is None
assert diagnostic['all_owned_group_ended'] and diagnostic['final_live_owned_members'] == []
result = {
    'schema': 'unit256-repair01-independent-static-integrity-check-v1',
    'STATUS': 'STATIC_PASS_ONLY', 'source': binding(OUT / NAME), 'proof': binding(OUT / 'PROOF-BODY.txt'),
    'changedLines': changed_lines, 'changedLocalDeclarationNames': [d['name'] for d in changed_contexts],
    'allLocalDeclarationCountDerived': len(new_contexts['declarations']),
    'binderCommandCountDerived': len(new_contexts['binderCommands']),
    'allPatternNameCountDerived': len(new_bindings['allRcasedIntroducedObtainedFunextNames']),
    'slicesRoundtrippedDerived': len(all_slices),
    'allDeclarationTypesScopesAndAllPatternBindingsUnchanged': True,
    'frozenPreambleHeadClosingAndFirstConjunctionExact': True,
    'sourceInventoryGeneratorTailReusedExactly': True,
    'utf8NoBOM': True, 'CRCount': 0, 'singleFinalLF': True,
    'oldPayloadsReverifiedReadOnly': len(old_manifest['payload']),
    'oldNative02FailureRetainedAt': binding(OUT.parent / 'lead-execution-01/native02-actual-projection.json'),
    'oldNative02RemoteReceiptBindingReusedAsFailureOnly': diagnostic['receipt'],
    'oldNative02Status': {'exit_code': diagnostic['exit_code'], 'seconds': diagnostic['seconds'], 'object_after': None},
    'noNativeRetryByThisAuthor': True,
    'fullRepairedProofReread': [489, 1049],
    'unchangedFrozenPrefixAlreadyFullyReadAsExactSourceBytes': [1, 488],
    'actualOwnerCount': None, 'actualTYPE': None, 'actualVALUE': None, 'recursiveAX': None,
    'qualified': False, 'machinePending': True,
    'independentAffectedProofReviewPending': True,
    'evidenceClass': 'PURE_SOURCE_DERIVED_STATIC_NOT_MACHINE_OWNER',
}
save('REPAIR-STATIC-CHECK.json', result)
print(json.dumps({k: result[k] for k in ('STATUS', 'source', 'changedLines', 'changedLocalDeclarationNames',
    'allLocalDeclarationCountDerived', 'binderCommandCountDerived', 'allPatternNameCountDerived', 'slicesRoundtrippedDerived',
    'oldPayloadsReverifiedReadOnly', 'qualified', 'machinePending')}, ensure_ascii=False))
