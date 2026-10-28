from pathlib import Path
import hashlib
import json
import re
from datetime import datetime, timezone

ROOT = Path('C:/game/shao lean')
OUT = ROOT / 'drafts/oq56/unit257/source-review-01'
AUTHOR = OUT.parent / 'author-01'
FREEZE = OUT.parent / 'freeze-01'

def raw(path):
    return Path(path).read_bytes()

def read(path):
    return raw(path).decode('utf-8')

def obj(path):
    return json.loads(read(path))

def sha(data):
    return hashlib.sha256(data).hexdigest()

def bind(path):
    data = raw(path)
    return {'path': Path(path).as_posix(), 'sha256': sha(data),
            'bytes': len(data), 'LF': data.count(b'\n')}

def save(name, value):
    (OUT / name).write_bytes((json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode('utf-8'))

def norm(value):
    return re.sub(r'\s+', '', value)

def conjunctions(value):
    opening = {'(': ')', '[': ']', '{': '}', '⟨': '⟩'}
    closing = set(opening.values())
    stack, output, begin = [], [], 0
    for pos, char in enumerate(value):
        if char in opening:
            stack.append(opening[char])
        elif char in closing:
            assert stack.pop() == char
        elif char == '∧' and not stack:
            output.append(value[begin:pos].strip())
            begin = pos + 1
    assert not stack
    return output + [value[begin:].strip()]

def split_at(value, marker):
    pos = value.index(marker)
    return value[:pos], conjunctions(value[pos:])

def tokens(value, mapping):
    pattern = r'(?<![\w₀-₉])(?:' + '|'.join(re.escape(k) for k in sorted(mapping, key=len, reverse=True)) + r')(?![\w₀-₉])'
    return re.sub(pattern, lambda match: mapping[match.group()], value)

def theorem_head(path, name):
    value = read(path)
    begin = value.index('theorem ' + name)
    end = value.index(':= by', begin)
    return value[begin:end].rstrip()

source_path = AUTHOR / 'OriginalLevelDependentStrictMomentFrontier.lean'
data = raw(source_path)
source = data.decode('utf-8')
assert bind(source_path)['sha256'] == 'ee2f5ff993bc92f6d5154be82ebb4da683f909717f0b20a98a4b8c76255f305b'
assert len(data) == 46525 and data.count(b'\n') == 731
assert data == raw(FREEZE/'FROZEN-PREAMBLE.txt') + raw(FREEZE/'FROZEN-HEAD.txt') + b':= by\n' + raw(AUTHOR/'PROOF-BODY.txt') + raw(FREEZE/'FROZEN-CLOSING.txt')
assert not data.startswith(b'\xef\xbb\xbf') and b'\r' not in data
assert data.endswith(b'\n') and not data.endswith(b'\n\n')
assert not re.findall(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', source)
assert re.findall(r'(?m)^(?:private\s+)?(?:theorem|lemma|def|abbrev|instance|opaque|axiom)\s+[^\s:(]+',source) == ['theorem actual_original_level_dependent_strict_moment_frontier']

input_rows = obj(AUTHOR/'INPUT-BINDINGS.json')['inputs']
payload_rows = obj(AUTHOR/'MANIFEST.json')['payload']
verified = {}
for row in input_rows + payload_rows + obj(OUT.parent/'parent-source-intake-01.json')['bindings']:
    actual = bind(row['path'])
    assert all(actual[k] == row[k] for k in ('path','sha256','bytes')), row['path']
    if 'LF' in row:
        assert actual['LF'] == row['LF']
    verified[row['path']] = actual
assert len(input_rows) == 19 and len(payload_rows) == 17
release = obj(AUTHOR/'FINALWRITE.json')
assert all(release[k] == 0 for k in ('writers','heavy','inflight','pendingExternal','children','uncertain'))
assert release['stopWritingAfterThisFile'] and release['authorProofComplete']

producer = obj(AUTHOR/'PRODUCER-TYPES.json')
heads = {}
for key, value in producer['contracts'].items():
    name = re.match(r'theorem\s+(\S+)', value['fullDeclaration'])[1]
    heads[key] = theorem_head(value['input']['path'], name)
    assert heads[key] == value['fullDeclaration']

h256 = heads['qualified256']
h257 = read(FREEZE/'FROZEN-HEAD.txt')
packet_marker = '      (∀ (n : ℕ)'
divider = ') ∧\n      ∀ (n : ℕ)'
packet256 = h256[h256.index(packet_marker)+7:h256.index(divider)]
packet257 = h257[h257.index(packet_marker)+7:h257.index(divider)]
consumer256 = h256[h256.index('      ∀ (n : ℕ)'):]
consumer257 = h257[h257.index('      ∀ (n : ℕ)'):h257.index('        ) ∧\n        ∀ (p : ℝ)')]
consumer257 = consumer257.replace('        (\n        @IsProbabilityMeasure','        @IsProbabilityMeasure',1)
assert norm(packet256) == norm(packet257)
assert norm(consumer256) == norm(consumer257)
consumer_lets, consumer_fields = split_at(consumer256[consumer256.index('        let mN :'):], '        @IsProbabilityMeasure')
packet_lets, packet_fields = split_at(packet256[packet256.index('        let mN :'):], '        @IsProbabilityMeasure')
iid_result = heads['originalIID'][heads['originalIID'].index('    let β :'):]
iid_outer_lets, iid_outer_fields = split_at(iid_result, '    0 ≤ β ∧')
iid_for_n = iid_outer_fields[-1]
iid_for_n = iid_for_n[iid_for_n.index('        let P :'):-1]
iid_n_lets, iid_n_fields = split_at(iid_for_n, '        IsProbabilityMeasure P ∧')
norm_result = heads['normalizedStrict'][heads['normalizedStrict'].index('    let η :'):]
norm_lets = norm_result[:norm_result.index('    (∀ i : Fin n, δ0 i <')]
norm_fields = conjunctions(norm_result[norm_result.index('    (∀ i : Fin n, Integrable'):])

expected_results = {
    'hOriginal': h256[h256.index('    let g :'):],
    'hAnalytic': consumer_lets + ' ∧\n'.join(consumer_fields),
    'hPacket0': tokens(packet_lets + ' ∧\n'.join(packet_fields), {'y':'z','ε':'(ε 0)'}),
    'hOriginalBudget': iid_result,
    'hNormalized': tokens(norm_result, {'Ω':'(Fin n → Ω × ℝ)'})
}
for key, value in expected_results.items():
    assert producer['applications'][key]['fullResultType'] == value, key

local = obj(AUTHOR/'LOCAL-CONTEXTS.json')
bindings = obj(AUTHOR/'BINDING-TYPES.json')
lines = source.splitlines(keepends=True)
offsets = [0]
for line in lines:
    offsets.append(offsets[-1] + len(line.encode('utf-8')))
declaration_starts = [i for i,line in enumerate(lines,1) if re.match(r'^\s*(?:·\s*)?(letI|let|have)\s+',line)]
command_starts = [i for i,line in enumerate(lines,1) if i >= 532 and re.match(r'^\s*(?:·\s*)?(intro|rcases|by_contra|filter_upwards)\b',line)]
assert declaration_starts == [d['slice']['startLine'] for d in local['declarations']]
assert command_starts == [d['slice']['startLine'] for d in local['bindingCommands']]
slice_count = 0
for item in local['declarations'] + local['bindingCommands']:
    s = item['slice']
    actual = data[s['startByte']:s['endByteExclusive']]
    assert actual.decode('utf-8') == s['utf8']
    assert sha(actual) == s['sha256']
    assert s['startByte'] == offsets[s['startLine']-1] and s['endByteExclusive'] == offsets[s['endLine']]
    assert item['lexicalScopeEndLine'] >= s['endLine'] and item['lexicalScopeEndLine'] <= 727
    if 'fullHeaderAndExplicitSourceType' in item:
        cut = s['utf8'].find(':=')
        assert item['fullHeaderAndExplicitSourceType'] == s['utf8'][:cut].strip()
        assert item['fullRHS'] == s['utf8'][cut+2:].strip()
        if item['name'] in expected_results:
            assert item['fullInferredSourceType'] == expected_results[item['name']]
    slice_count += 1

rows_by_line = {}
for row in bindings['allPatternBindings']:
    rows_by_line.setdefault(row['commandStartLine'], []).append(row)
    assert row['evidenceClass'] == 'PURE_SOURCE_DERIVED_STATIC_NOT_MACHINE_PP'
assert sorted(rows_by_line) == command_starts
frozen_lets = {}
for d in local['declarations']:
    if d['slice']['startLine'] < 532:
        frozen_lets[d['name']] = d
expected_group_types = {
 549: (['MeasurableSpace Ω', 'm₀ ≤ mΩ', '@MeasurableSpace.CountablyGenerated Ω m₀', h256[h256.index('      let μ₀ :'):]], ''),
 554: (['IsProbabilityMeasure μ₀', packet256, consumer256], ''),
 567: (consumer_fields, consumer_lets),
 581: ([tokens(x, {'y':'z','ε':'(ε 0)'}) for x in packet_fields[:5]+[' ∧\n'.join(packet_fields[5:])]], tokens(packet_lets, {'y':'z','ε':'(ε 0)'})),
 603: (iid_outer_fields, iid_outer_lets),
 604: (iid_n_fields, iid_outer_lets+iid_n_lets),
 666: (['Loriginal ≤ Real.rpow cWindow p', '∀ i : Fin n, δoriginal i < (1 / 2 : ℝ)', 'Loriginal < cBudget * z ^ 2'], ''),
 685: ([tokens(x, {'Ω':'(Fin n → Ω × ℝ)'}) for x in norm_fields[:4]] + ['ℕ','∀ k : ℕ, kStrict ≤ k → (∀ i : Fin n, δη k i < (1 / 2 : ℝ)) ∧ Lη k < cBudget * z ^ 2'], None)
}
type_count = 0
for start, rows in rows_by_line.items():
    command = next(c for c in local['bindingCommands'] if c['slice']['startLine'] == start)
    value = command['slice']['utf8']
    if command['kind'] == 'intro':
        names = value.split('intro ',1)[1].strip().split()
    elif command['kind'] == 'rcases':
        names = [x.strip() for x in value[value.index('⟨')+1:value.rindex('⟩')].split(',')]
    elif command['kind'] == 'by_contra':
        names = ['hnot']
    else:
        names = value.split('with ',1)[1].strip().split()
    assert names == [r['name'] for r in rows]
    if start in expected_group_types:
        types, context = expected_group_types[start]
        assert len(types) == len(rows)
        for j,(row,tp) in enumerate(zip(rows, types)):
            assert row['fullType'] == tp.strip(), (start,row['name'])
            expected_context = context if context is not None else (tokens(norm_lets, {'Ω':'(Fin n → Ω × ℝ)'}) if j < 4 else '')
            assert row['fullSourceLetContext'] == expected_context
    for row in rows:
        assert row['lexicalScopeEndLine'] == command['lexicalScopeEndLine']
        if command['kind'] == 'intro' and row['name'] in frozen_lets:
            d = frozen_lets[row['name']]
            assert row['fullType'] == d['fullHeaderAndExplicitSourceType'].split(':',1)[1].strip()
            assert row['origin'] == 'intro of frozen local let; full RHS: ' + d['fullRHS']
        type_count += 1

assert len(local['declarations']) == 198 and len(local['bindingCommands']) == 22
assert type_count == 199 and len(consumer_fields) == 49 and len(packet_fields) == 89
save('SOURCE-STATIC-VERIFICATION.json', {
 'schema':'unit257-independent-source-only-static-verification-v1',
 'atUTC':datetime.now(timezone.utc).isoformat(), 'source':bind(source_path),
 'freezeAssemblyExact':True,'frozen517LFReadByExactSourceSegment':True,
 'qualified256FullContractExactToProducerInventory':True,
 'whole255PacketViaQualified256Retained':True, 'whole256ConsumerRetainedModuloOuterParenthesesWhitespace':True,
 'inputBindings':len(input_rows),'authorPayloadBindings':len(payload_rows),
 'uniqueInputAndPayloadAndParentBindings':len(verified), 'allBindings':list(verified.values()),
 'sourceDeclarations':len(local['declarations']), 'bindingCommands':len(local['bindingCommands']),
 'patternNames':type_count,'sourceSlicesRoundtrip':slice_count,
 'consumerFields':len(consumer_fields),'packetFields':len(packet_fields),
 'producerContractsExact':len(heads),'producerApplicationsFullResultTypesExact':len(expected_results),
 'allGroupedRcasingTypesAndContextsExact':True,'allFrozenLetIntroTypesAndRHSExact':True,
 'fullTypeRHSAndScopeSemanticReview':'Complete model review against full source; repeated contexts compared exactly rather than reprinting duplicate contracts',
 'staticNotMachinePP':True,'machinePending':True,'qualified':False,
 'actualOwnerCount':None,'actualTYPE':None,'actualVALUE':None,'actualAX':None,
 'LeanLakePPAXServerNetworkUploadGitAPIChildrenSidebarGoalScheduleOperations':0})
print(json.dumps({'STATUS':'PASS_SOURCE_ONLY','source':bind(source_path), 'bindings':len(verified),
 'localDeclarations':198,'bindingCommands':22,'patternNames':199,'slices':slice_count,
 'producerContracts':len(heads),'producerApplications':len(expected_results)},ensure_ascii=False))
