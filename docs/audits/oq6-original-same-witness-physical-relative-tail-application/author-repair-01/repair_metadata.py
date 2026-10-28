"""Bounded local byte repair and coordinate validation; no Lean/server actions."""
from __future__ import annotations

from copy import deepcopy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

ROOT = Path('C:/game/shao lean')
UNIT = ROOT / 'drafts/oq56/unit249'
OLD = UNIT / 'author-01'
OUT = UNIT / 'author-repair-01'
FREEZE = UNIT / 'freeze-01'
NAME = 'OriginalSameWitnessPhysicalRelativeTailApplication.lean'
NOW = datetime.now(timezone.utc).isoformat()
ROLE = '/root/oq56_unit249_author_repair01'
OPS = {k: 0 for k in ['Lean', 'lake', 'kernel', 'PP', 'AX', 'server', 'network',
                      'upload', 'Git', 'publicationAPI', 'children', 'Goal', 'schedule', 'sidebar']}
USAGE = {k: None for k in ['input', 'cachedInput', 'output', 'reasoningSubset']}


def sha(b):
    return hashlib.sha256(b).hexdigest()


def binding(p):
    p = Path(p)
    b = p.read_bytes()
    return {'path': p.as_posix(), 'sha256': sha(b), 'bytes': len(b)}


def load(p):
    return json.loads(Path(p).read_bytes())


def verify(b):
    actual = binding(b['path'])
    assert actual == b, (b['path'], actual, b)
    return actual


def write_json(name, data):
    (OUT / name).write_bytes((json.dumps(data, ensure_ascii=False, indent=2) + '\n').encode('utf-8'))


def flat(s):
    return ''.join(s.split())


assert {p.name for p in OUT.iterdir()} == {'repair_metadata.py'}, 'Output directory is not fresh'
f2 = load(UNIT / 'freeze-02/frozen-declaration.json')
assert binding(UNIT / 'freeze-02/frozen-declaration.json') == {
    'path': (UNIT / 'freeze-02/frozen-declaration.json').as_posix(),
    'sha256': 'cbc16090a06cbe6dcb9f43aece8d224b03fe6fc1969eba9ac07026d35d257787', 'bytes': 2342}
verify(f2['inheritedFullInterfaceFreeze'])
verify(f2['oldSource'])
verify(f2['oldAuthorFinalRelease'])
verify(f2['firstNativeKnownEndedFailure'])
old_release = load(f2['oldAuthorFinalRelease']['path'])
assert old_release['FINALWRITE'] and old_release['writerReleased']
assert all(v == 0 for v in old_release['sixZero'].values())
review_release_path = UNIT / 'source-review-01/SOURCE-STAGE-RELEASE.json'
assert binding(review_release_path)['sha256'] == 'd7ef1b81bae99652f38bcee44521f8139f7fd459883fe36ee0fb7a1e80cb0841'
review_release = load(review_release_path)
assert review_release['stageWriterReleased'] and all(v == 0 for v in review_release['sixZero'].values())
assert review_release['STATUS'] == 'CRITICAL_GAPS' and not review_release['qualified']
intake_path = UNIT / 'parent-independent-source-intake-01.json'
assert binding(intake_path)['sha256'] == '3da481e11cf97d449c95588407491397c6cda1382514b90d885fa336293ed8d1'
intake = load(intake_path)
for k in ['source', 'report', 'manifest', 'coverage', 'reviewStageRelease']:
    verify(intake[k])
assert intake['sourceVerdict'] == 'CRITICAL_GAPS' and intake['oldCompleteCoverageReusableOutsideOneLine']
old_manifest = load(OLD / 'MANIFEST.json')
for b in old_manifest['inputs'] + old_release['payloads']:
    verify(b)
f1 = load(FREEZE / 'frozen-declaration.json')
for b in f1['files']:
    verify(b)
inventory = load(FREEZE / 'INTERFACE-INVENTORY.json')
facts_old = load(OLD / 'FACT-COORDINATES.json')
decs_old = load(OLD / 'DECLARATION-COORDINATES.json')
old = (OLD / NAME).read_bytes()
old_text = old.decode('utf-8')
lines = old.splitlines(keepends=True)
line_index = f2['allowedOnlyProofDelta']['sourceLine'] - 1
before = f2['allowedOnlyProofDelta']['before'].encode('utf-8')
after = f2['allowedOnlyProofDelta']['after'].encode('utf-8')
assert line_index == 3767 and lines[line_index] == before
line_start = sum(map(len, lines[:line_index]))
line_end = line_start + len(before)
new = old[:line_start] + after + old[line_end:]
text = new.decode('utf-8')
assert len(after) - len(before) == 2
assert sha(new) == f2['expectedNewSource']['sha256'] and len(new) == 240930
assert new.count(b'\n') == 3824 and b'\r' not in new and not new.startswith(b'\xef\xbb\xbf')
assert old[:line_start] == new[:line_start]
assert old[line_end:] == new[line_start + len(after):]
assert [j + 1 for j, (a, b) in enumerate(zip(lines, new.splitlines(keepends=True))) if a != b] == [3768]
new_source_path = OUT / NAME
new_source_path.write_bytes(new)


def coord(s, pos, with_byte_column=False):
    prefix = s[:pos]
    last = prefix.rsplit('\n', 1)[-1]
    c = {'byte': len(prefix.encode('utf-8')), 'line': prefix.count('\n') + 1, 'column': len(last) + 1}
    if with_byte_column:
        c['byteColumnUTF8'] = len(last.encode('utf-8')) + 1
    return c


old_char_end = len(old[:line_end].decode('utf-8'))
old_char_start = len(old[:line_start].decode('utf-8'))
coordinate_checks = []


def move_char(pos):
    assert isinstance(pos, int) and 0 <= pos <= len(old_text)
    assert not old_char_start < pos < old_char_end, ('Unexpected boundary inside repaired line', pos)
    return pos + 2 if pos >= old_char_end else pos


def transform(value, path=''):
    if isinstance(value, list):
        return [transform(v, f'{path}/{j}') for j, v in enumerate(value)]
    if not isinstance(value, dict):
        return value
    if {'byte', 'line', 'column'} <= value.keys():
        assert set(value) in ({'byte', 'line', 'column'}, {'byte', 'line', 'column', 'byteColumnUTF8'})
        pos = len(old[:value['byte']].decode('utf-8'))
        assert coord(old_text, pos, 'byteColumnUTF8' in value) == value, (path, value)
        result = coord(text, move_char(pos), 'byteColumnUTF8' in value)
        assert result['line'] == value['line'] and result['column'] == value['column']
        coordinate_checks.append((path, value['byte'], result['byte']))
        return result
    result = {}
    for k, v in value.items():
        result[k] = move_char(v) if k.endswith('Character') or k.endswith('CharacterExclusive') else transform(v, f'{path}/{k}')
    return result


facts = transform(facts_old, 'facts')
changed_fact_slices = []
for old_row, row in zip(facts_old, facts):
    a, b = row['startCharacter'], row['endCharacterExclusive']
    assert row['start'] == coord(text, a) and row['endExclusive'] == coord(text, b)
    old_slice = old_text[old_row['startCharacter']:old_row['endCharacterExclusive']].encode('utf-8')
    assert sha(old_slice) == old_row['sourceSliceSHA256']
    new_slice = text[a:b].encode('utf-8')
    row['sourceSliceSHA256'] = sha(new_slice)
    if old_slice != new_slice:
        changed_fact_slices.append(row['name'])
    frozen_fact = next(x for x in inventory['proposedProofFacts'] if x['name'] == row['name'])
    assert row['fullType'] == frozen_fact['fullType'] == old_row['fullType']
    if row['explicitType']:
        ts, te = row['typeStartCharacter'], row['typeEndCharacterExclusive']
        assert flat(text[ts:te]) == flat(row['fullType'])
        assert row['typeStart'] == coord(text, ts) and row['typeEndExclusive'] == coord(text, te)
        assert row['proofStart'] == coord(text, row['proofStartCharacter'])
        assert old_text[old_row['typeStartCharacter']:old_row['typeEndCharacterExclusive']] == text[ts:te]
assert changed_fact_slices == ['hPaymentLeOne']
assert len(facts) == 28 and sum(x['explicitType'] for x in facts) == 27
assert [x['name'] for x in facts if not x['explicitType']] == ['h248']
payment_fact = next(x for x in facts if x['name'] == 'hPaymentLeOne')
assert payment_fact['fullType'] == 'payment ≤ payment1'
write_json('FACT-COORDINATES.json', facts)
decs = transform(decs_old, 'declarations')
decs['source'] = binding(new_source_path)
decs['facts'] = [{k: v for k, v in row.items() if k != 'fullType'} for row in facts]


def slice_at(row, end_key='rhsEndExclusive'):
    return new[row['start']['byte']:row[end_key]['byte']].decode('utf-8')


ordinary = decs['ordinaryLets']
public_rows = [x for x in ordinary if x['role'] == 'PUBLIC_HEAD']
assert len(ordinary) == 730 and len(public_rows) == 155
assert [x['publicOccurrence'] for x in public_rows] == list(range(1, 156))
for row in ordinary:
    category, ref = row['freezeRef'].split('/', 1)
    if category in {'publicOrdinary', 'optionalOrdinary'}:
        frow = inventory[category][int(ref)]
        expected = 'let ' + frow['name'] + ' : ' + frow['type'] + ' := ' + frow['rhs']
    else:
        assert row['insideFact'] == 'hAbsorption236'
        expected = 'let cWindow : ℝ := min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ))'
    assert flat(slice_at(row)) == flat(expected), row
lexical_let_starts = [len(text[:m.start('keyword')].encode('utf-8')) for m in
                      re.finditer(r'(?m)^[ \t]*(?P<keyword>let)[ \t]+(?:(?P<name>[^\s:]+)[ \t]+)?(?=:)', text)]
assert lexical_let_starts == [x['start']['byte'] for x in ordinary]
instances = decs['instanceLets']
assert len(instances) == 8 and len(inventory['approvedInstances']) == 8
for row in instances:
    approved = inventory['approvedInstances'][int(row['freezeRef'].split('/')[1])]
    assert row['type'] == approved['type'] and row['rhs'] == approved['rhs']
    expected = ['letI : ' + row['type'] + ' := ' + row['rhs']]
    if row['name'] == 'selectedCountableGeneration':
        expected.append('letI : MeasurableSpace.CountablyGenerated Ω := hcg')
    assert flat(slice_at(row)) in [flat(x) for x in expected]
lexical_instance_starts = [len(text[:m.start('keyword')].encode('utf-8')) for m in
                           re.finditer(r'(?m)^[ \t]*(?P<keyword>letI)[ \t]+(?=[:])', text)]
assert lexical_instance_starts == [x['start']['byte'] for x in instances]
have_matches = list(re.finditer(r'(?m)^  have ([^\s:]+)', text))
assert [x[1] for x in have_matches] == [x['name'] for x in facts]
assert [len(text[:m.start()].encode('utf-8')) for m in have_matches] == [x['start']['byte'] for x in facts]
choices = decs['allClassicalChooseOccurrences']
assert len(choices) == 4 and sum(x['kind'] == 'DATA_CHOICE_SAME248' for x in choices) == 2
assert [x['start']['byte'] for x in choices] == [len(text[:m.start()].encode('utf-8')) for m in re.finditer(r'Classical\.choose\b', text)]
assert [x['byte'] for x in decs['chooseSpecOccurrences']] == [len(text[:m.start()].encode('utf-8')) for m in re.finditer(r'Classical\.choose_spec\b', text)]
for row in decs['proofOrdinaryIntroductionsOfFrozenLets']:
    assert new[row['start']['byte']:row['endExclusive']['byte']].decode('utf-8') == row['name']
for row in decs['internalPatternBindings']:
    assert new[row['start']['byte']:].decode('utf-8').startswith(row['name'])
for row in decs['otherOriginalBinderIntroductions']:
    assert new[row['start']['byte']:].decode('utf-8').startswith(row['sourceLine'])
write_json('DECLARATION-COORDINATES.json', decs)
optional_map = []
assert len(inventory['optionalOrdinary']) == 159
for j, row in enumerate(inventory['optionalOrdinary']):
    public_ordinal = row.get('publicOccurrence')
    if public_ordinal is not None:
        target = public_rows[public_ordinal - 1]
        prow = inventory['publicOrdinary'][public_ordinal - 1]
        assert row['name'] == prow['name'] and flat(row['type']) == flat(prow['type']) and flat(row['rhs']) == flat(prow['rhs'])
    else:
        matches = [x for x in ordinary if x['role'] == 'OPERATIVE_PROOF' and x['freezeRef'] == f'optionalOrdinary/{j}']
        assert len(matches) == 1
        target = matches[0]
    expected = 'let ' + row['name'] + ' : ' + row['type'] + ' := ' + row['rhs']
    assert flat(slice_at(target)) == flat(expected)
    optional_map.append({'freezeRef': f'optionalOrdinary/{j}', 'name': row['name'],
                         'publicOccurrence': public_ordinal, 'sourceRole': target['role'],
                         'start': target['start'], 'rhsEndExclusive': target['rhsEndExclusive'],
                         'exactFrozenTypeSHA256': sha(row['type'].encode('utf-8')),
                         'exactFrozenRHSSHA256': sha(row['rhs'].encode('utf-8'))})
write_json('OPTIONAL-MAPPING.json', {'schema': 'oq56-unit249-all159-optional-freeze-source-mapping-v1',
                                  'source': binding(new_source_path), 'inventory': binding(FREEZE / 'INTERFACE-INVENTORY.json'),
                                  'rows': optional_map, 'countDerived': len(optional_map),
                                  'completeTypesAndRHSRetainedInExactBoundInventory': True})
preamble = (FREEZE / 'FROZEN-PREAMBLE.txt').read_bytes()
head = (FREEZE / 'FROZEN-HEAD.txt').read_bytes()
closing = (FREEZE / 'FROZEN-CLOSING.txt').read_bytes()
assert new.startswith(preamble + head) and new.endswith(closing)
assert not re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', text)
assert len(re.findall(r'(?m)^theorem\s', text)) == 1
diag = load(f2['firstNativeKnownEndedFailure']['path'])
assert diag['actualRC'] == 1 and diag['errorCountDerived'] == 1 and not diag['timedOut']
assert diag['allOwnedEnded'] and diag['beforeAfterEqual'] and diag['preservationEqual']
counts = {'publicOrdinary': len(public_rows), 'optionalOrdinaryCatalog': len(optional_map),
          'allLexicalOrdinaryLetOccurrencesIncludingTypeCopies': len(ordinary),
          'allLexicalInstanceLetOccurrencesIncludingTypeCopies': len(instances),
          'haveRowsWithFullFrozenTypes': len(facts), 'explicitFullTypeHaveRows': sum(x['explicitType'] for x in facts),
          'permittedInferredPropHaveRows': 1, 'sameDataChoices': sum(x['kind'] == 'DATA_CHOICE_SAME248' for x in choices),
          'proofWitnessChoicesFromSameExistential': sum(x['kind'] == 'PROOF_WITNESS_SAME_HMODEL' for x in choices),
          'newTopLevelHelpers': 0, 'newInstances': 0, 'newSelectors': 0, 'newNatCutoffs': 0}
checks = {'schema': 'oq56-unit249-single-line-repair-local-textual-checks-v1', 'atUTC': NOW,
          'source': binding(new_source_path), 'oldSource': binding(OLD / NAME),
          'onlyChangedLine': 3768, 'before': before.decode('utf-8'), 'after': after.decode('utf-8'),
          'oldChangedLineUTF8ByteRangeExclusive': [line_start, line_end],
          'newChangedLineUTF8ByteRangeExclusive': [line_start, line_start + len(after)],
          'allOtherSourceAndProofBytesExact': True, 'prefixByteExact': True, 'suffixByteExact': True,
          'lineNumberDelta': 0, 'postLineUTF8ByteDelta': 2, 'UTF8NoBOM': True, 'LFOnly': True,
          'preamblePublicHeadClosingByteExact': True, 'all28FullFrozenFactTypesUnchanged': True,
          'changedFactSlices': changed_fact_slices, 'hPaymentLeOneFullType': payment_fact['fullType'],
          'allOldCoordinatesRecomputedAndVerified': len(coordinate_checks),
          'shiftedCoordinateDictionariesDerived': sum(a != b for _, a, b in coordinate_checks),
          'all730OrdinaryLetsReMatchedToFreeze': True, 'all8InstancesReMatchedToFreeze': True,
          'all159OptionalRowsReMatchedToPublicOrOperativeSource': True,
          'allFactsTypesAndSourceSliceHashesRecomputed': True, 'countsDerived': counts,
          'LeanParsingOrElaborationPerformed': False, 'notIndependentReviewOrKernelEvidence': True,
          'oldFailureRemainsRC1NoObject': True, 'newKernelPending': True, 'sourceAccepted': False,
          'operations': OPS}
write_json('TEXTUAL-CHECKS.json', checks)
report = f'''# Unit249 单行形式接口修复

本次只在新目录保存完整新源码，将第 3768 行 `apply add_le_add_left` 改为 `apply add_le_add le_rfl`。新源 SHA256 为 `{sha(new)}`，240930 字节、3824 LF，UTF-8 无 BOM、仅 LF。

局部事实 `hPaymentLeOne` 的完整冻结类型保持 `payment ≤ payment1`。展开两个 payment 后，共同左前缀 A 满足 `A ≤ A`；`add_le_add le_rfl` 将目标 `A+B ≤ A+C` 归约为原有的 `B ≤ C`。其后的乘法单调性、指数单调性及由 z≥1 和 sqrt(n)≥0 得到的比较证明逐字节不变。未修改任何前提、公开类型、let、实例、选择或其他证明。

确定性脚本直接比较补丁前后的前缀/后缀和逐行差异：仅第 3768 行不同，净增 2 个 ASCII/UTF-8 字节。所有行号保持，后续字节坐标重算。28 项完整冻结事实类型均保持，其中 27 项实际显式、h248 为唯一允许推断项；155 public、159 optional、730 lexical let、8 既有 letI、同一 witness 的 2 data choices 的完整映射均复算核对。FACT 的 sourceSliceSHA256 只有 hPaymentLeOne 改变，其余 27 片段逐字节相同。

旧作者和旧独审阶段释放、freeze01/02、原失败及旧完整 coverage 均按实际哈希绑定。旧审稿结论仍为 CRITICAL_GAPS；本次不将其转记通过。未受影响完整审查按父级冻结指令复用。新源仍 sourceAccepted=false、qualified=false、kernelPending=true；等待独立差异审查和 lead 的新源服务器 native/同首个成功对象实际 TYPE/必需 VALUE/transitive AX。旧 248/236 的证明、TYPE、AX 不重放。

本上下文实际 Lean/lake/PP/AX/server/network/upload/Git/外部 publication API/children/Goal/schedule/sidebar 操作均为零；仅使用本地文本与元数据工具。requestedModel=gpt-6.1-sol，requestedEffort=xhigh；实际 model/effort/usage 不可见，全部记录为 null。
'''
(OUT / 'REPAIR.md').write_bytes(report.encode('utf-8'))
inputs_by_path = {}
for b in old_manifest['inputs'] + old_release['payloads']:
    inputs_by_path[b['path']] = verify(b)
for p in [UNIT / 'freeze-02/frozen-declaration.json', OLD / 'lastzeroRELEASE.json', review_release_path,
          intake_path, UNIT / 'source-review-01/SOURCE-REVIEW.md', UNIT / 'source-review-01/COVERAGE.json',
          UNIT / 'source-review-01/VERDICT.json', UNIT / 'source-review-01/MANIFEST.json',
          UNIT / 'lead-execution-01/native-complete-diagnostic-projection.json']:
    inputs_by_path[p.as_posix()] = binding(p)
inputs = list(inputs_by_path.values())
payload_names = [NAME, 'FACT-COORDINATES.json', 'DECLARATION-COORDINATES.json', 'OPTIONAL-MAPPING.json',
                 'TEXTUAL-CHECKS.json', 'REPAIR.md', 'repair_metadata.py']
payloads = [binding(OUT / name) for name in payload_names]
manifest = {'schema': 'oq56-unit249-exact-single-line-author-repair-manifest-v1', 'atUTC': NOW,
            'role': ROLE, 'ownerChat': '01a1822b-1815-7f21-a1af-2e0b15ee67a5',
            'rootCoordinator': '01a17d3c-6dfd-7cc0-94ed-35d758a423a5', 'ownedRoot': OUT.as_posix(),
            'unit': 249, 'module': old_manifest['module'], 'publicTheorem': old_manifest['publicTheorem'],
            'STATUS': 'EXACT_FROZEN_SINGLE_LINE_REPAIR_SEALED_UNCHECKED',
            'proofStatus': 'INCOMPLETE', 'proofStatusQualifier': 'Authorized formal API repair implemented; independent delta review and new-source kernel/all-owned audit remain pending.',
            'sourceComplete': True, 'sourceAccepted': False, 'independent': False, 'qualified': False,
            'kernelChecked': False, 'kernelPending': True, 'axiomAudited': False,
            'source': binding(new_source_path), 'sourceLF': 3824, 'sourceUTF8NoBOM': True, 'sourceLFOnly': True,
            'oldSource': binding(OLD / NAME), 'frozenDeclaration': binding(UNIT / 'freeze-02/frozen-declaration.json'),
            'inheritedFullInterfaceFreeze': binding(FREEZE / 'frozen-declaration.json'),
            'allOtherSourceAndProofBytesExact': True, 'preamblePublicHeadClosingByteExact': True,
            'onlyProofDelta': f2['allowedOnlyProofDelta'], 'fullFrozenFactTypes': 28,
            'hPaymentLeOneFullType': 'payment ≤ payment1', 'actualDerivedCounts': counts,
            'inputCountDerived': len(inputs), 'inputs': inputs,
            'payloadCountDerivedExcludingManifestAndLastRelease': len(payloads), 'payloads': payloads,
            'allInputsAndPayloadsHashBound': True, 'sourceCoordinateMaps': {
                'facts': binding(OUT / 'FACT-COORDINATES.json'), 'declarations': binding(OUT / 'DECLARATION-COORDINATES.json'),
                'all159OptionalRows': binding(OUT / 'OPTIONAL-MAPPING.json')},
            'independentCoverageReuse': {'completeOldReport': binding(UNIT / 'source-review-01/SOURCE-REVIEW.md'),
                                       'completeOldCoverage': binding(UNIT / 'source-review-01/COVERAGE.json'),
                                       'priorVerdict': 'CRITICAL_GAPS', 'priorFailureNotConvertedToPass': True,
                                       'actualDeltaIndependentReviewPending': True},
            'oldFailure': {'diagnostic': binding(UNIT / 'lead-execution-01/native-complete-diagnostic-projection.json'),
                           'actualRC': 1, 'errorCount': 1, 'objectProduced': False, 'preservedUnchanged': True},
            'newAssumptions': False, 'newPublicDeclarations': False, 'fullOQ56': 'OPEN',
            'readingFrontier': 'Bounded author repair only: full freeze/release/review report and exact local gap read; all source bytes bound and all metadata coordinates/types mechanically verified. No claim of fresh complete proof/source review.',
            'nextExactDependency': 'Qualified independent affected one-line review, then lead-scheduled new-source server native and same-first-successful-original-object all-actual TYPE/required VALUE/transitive AX. Reuse unaffected old complete review and qualified248/236 evidence.',
            'operations': OPS, 'operationsClarification': 'Local file tools and collaboration ACK used; API zero means external publication/API operations.',
            'requestedModel': 'gpt-6.1-sol', 'requestedEffort': 'xhigh', 'actualBackend': None,
            'actualModel': None, 'actualEffort': None, 'usage': USAGE}
write_json('MANIFEST.json', manifest)
for b in inputs + payloads:
    verify(b)
print(json.dumps({'status': manifest['STATUS'], 'source': manifest['source'], 'LF': 3824,
                  'manifest': binding(OUT / 'MANIFEST.json'), 'inputs': len(inputs), 'payloads': len(payloads),
                  'counts': counts, 'coordinateDictionariesVerified': len(coordinate_checks),
                  'shiftedCoordinateDictionaries': sum(a != b for _, a, b in coordinate_checks),
                  'changedFactSlices': changed_fact_slices, 'releaseWritten': False, 'operations': OPS}, ensure_ascii=True))
