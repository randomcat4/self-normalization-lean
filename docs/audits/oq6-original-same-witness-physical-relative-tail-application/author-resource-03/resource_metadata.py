"""Reuse bound local metadata routines for the sole frozen theorem option insertion."""
from __future__ import annotations

import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

ROOT = Path('C:/game/shao lean')
UNIT = ROOT / 'drafts/oq56/unit249'
OLD = UNIT / 'author-repair-01'
OUT = UNIT / 'author-resource-03'
FREEZE = UNIT / 'freeze-01'
NAME = 'OriginalSameWitnessPhysicalRelativeTailApplication.lean'
NOW = datetime.now(timezone.utc).isoformat()
existing = {p.name for p in OUT.iterdir()}
assert 'resource_metadata.py' in existing and existing <= {'resource_metadata.py', NAME, 'FACT-COORDINATES.json', 'DECLARATION-COORDINATES.json', 'OPTIONAL-MAPPING.json'}, 'Unexpected output or sealed state'

# Execute only the named, previously hash-bound local metadata functions.
# The old script's module body is never executed and OLD is never a write target.
tool_path = OLD / 'repair_metadata.py'
tool_bytes = tool_path.read_bytes()
assert hashlib.sha256(tool_bytes).hexdigest() == '96199d8fe49f0706d43a0f6fcad5542e389d3dd9d42339245d344633394c460f'
tool_text = tool_bytes.decode('utf-8')
names = ['sha', 'binding', 'load', 'verify', 'write_json', 'flat', 'coord', 'slice_at']
selected = [node for node in ast.parse(tool_text).body if isinstance(node, ast.FunctionDef) and node.name in names]
assert [node.name for node in selected] == names
exec(compile(ast.Module(body=selected, type_ignores=[]), str(tool_path) + ':metadata-functions-only', 'exec'))

f3_path = UNIT / 'freeze-03/frozen-declaration.json'
assert binding(f3_path) == {'path': f3_path.as_posix(),
                          'sha256': '392ce9b9e9fba5ac31c77999f823fa32b624faac7002e48165798d574c702a99', 'bytes': 3292}
f3 = load(f3_path)
for key in ['priorCompleteFreeze', 'priorOneLineRepairFreeze', 'oldSource']:
    verify(f3[key])
verify(f3['knownEndedNative02']['projection'])
old_release_path = OLD / 'lastzeroRELEASE.json'
assert binding(old_release_path)['sha256'] == 'd251884b47080b60587f234c045e8aecff468bb345cd178e27fc2ce67118aa65'
old_release = load(old_release_path)
assert old_release['FINALWRITE'] and old_release['writerReleased'] and all(v == 0 for v in old_release['sixZero'].values())
for b in old_release['payloads']:
    verify(b)
review_release_path = UNIT / 'source-review-repair-01/PHASE-RELEASE.json'
assert binding(review_release_path)['sha256'] == 'e249e508a6117e5a478664fdc11d5f46be1d2067efd2fb0f76766c0136c6a22c'
review_release = load(review_release_path)
assert review_release['FINALWRITE'] and review_release['writerReleased'] and all(v == 0 for v in review_release['sixZero'].values())
assert review_release['sourceVerdict'] == 'CORRECT' and not review_release['qualified']
for k in ['source', 'manifest', 'sourceManifest', 'supplement']:
    verify(review_release[k])
supplement = load(review_release['supplement']['path'])
verify(supplement['sourceReportUnchanged'])
verify(supplement['diagnosticProjection'])
diagnostic = load(f3['knownEndedNative02']['projection']['path'])
assert diagnostic['exit_code'] == 1 and diagnostic['object_after'] is None and not diagnostic['timed_out']
assert diagnostic['all_owned_group_ended'] and diagnostic['beforeAfterEqual'] and diagnostic['preservation_equal']
assert diagnostic['ownership_issue'] is None and not diagnostic['cleanup_events'] and not diagnostic['final_live_owned_members']
assert diagnostic['post_error'] is None
errors = [r for r in diagnostic['diagnostics'] if ': error:' in r['text']]
assert len(errors) == 2 and all('heartbeats (200000)' in r['text'] for r in errors)
assert 'add_le_add_left' not in diagnostic['rawStdout']
old_manifest = load(OLD / 'MANIFEST.json')
inventory = load(FREEZE / 'INTERFACE-INVENTORY.json')
freeze1 = load(FREEZE / 'frozen-declaration.json')
for b in freeze1['files']:
    verify(b)
facts_old = load(OLD / 'FACT-COORDINATES.json')
decs_old = load(OLD / 'DECLARATION-COORDINATES.json')
old = (OLD / NAME).read_bytes()
old_text = old.decode('utf-8')
lines = old.splitlines(keepends=True)
delta = f3['authorizedDelta']
assert delta['insertionOldLine'] == 15 and delta['boundedMaxHeartbeats'] == 800000
before = delta['before'].encode('utf-8')
after = delta['after'].encode('utf-8')
assert lines[14] == before and after == b'set_option maxHeartbeats 800000 in\n' + before
insertion = after[:-len(before)]
insertion_byte = sum(map(len, lines[:14]))
insertion_character = len(old[:insertion_byte].decode('utf-8'))
assert len(insertion) == 35 and insertion.count(b'\n') == 1
new = old[:insertion_byte] + insertion + old[insertion_byte:]
text = new.decode('utf-8')
assert sha(new) == delta['newSourceExpectedSHA256'] == '19c3e659b538c19d7e73a55bcaec1dc6727b435665e215890cc6c219c88704a0'
assert len(new) == delta['newSourceExpectedBytes'] == 240965
assert new.count(b'\n') == delta['newSourceExpectedLF'] == 3825
assert new[:insertion_byte] + new[insertion_byte + len(insertion):] == old
assert not new.startswith(b'\xef\xbb\xbf') and b'\r' not in new
new_source_path = OUT / NAME
if new_source_path.exists():
    assert new_source_path.read_bytes() == new
new_source_path.write_bytes(new)
coordinate_checks = []


def move_char(pos):
    assert isinstance(pos, int) and 0 <= pos <= len(old_text)
    return pos + len(insertion) if pos >= insertion_character else pos


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
        shift = int(pos >= insertion_character)
        assert result['line'] == value['line'] + shift and result['column'] == value['column']
        assert result['byte'] == value['byte'] + len(insertion) * shift
        coordinate_checks.append((path, value, result))
        return result
    return {k: move_char(v) if k.endswith('Character') or k.endswith('CharacterExclusive')
            else transform(v, f'{path}/{k}') for k, v in value.items()}


facts = transform(facts_old, 'facts')
for old_row, row in zip(facts_old, facts):
    raw = text[row['startCharacter']:row['endCharacterExclusive']].encode('utf-8')
    old_raw = old_text[old_row['startCharacter']:old_row['endCharacterExclusive']].encode('utf-8')
    assert raw == old_raw and sha(raw) == row['sourceSliceSHA256'] == old_row['sourceSliceSHA256']
    assert row['start'] == coord(text, row['startCharacter']) and row['endExclusive'] == coord(text, row['endCharacterExclusive'])
    frozen_row = next(x for x in inventory['proposedProofFacts'] if x['name'] == row['name'])
    assert row['fullType'] == old_row['fullType'] == frozen_row['fullType']
    if row['explicitType']:
        assert text[row['typeStartCharacter']:row['typeEndCharacterExclusive']] == old_text[old_row['typeStartCharacter']:old_row['typeEndCharacterExclusive']]
        assert flat(text[row['typeStartCharacter']:row['typeEndCharacterExclusive']]) == flat(row['fullType'])
        assert row['typeStart'] == coord(text, row['typeStartCharacter'])
        assert row['typeEndExclusive'] == coord(text, row['typeEndCharacterExclusive'])
        assert row['proofStart'] == coord(text, row['proofStartCharacter'])
assert len(facts) == 28 and sum(x['explicitType'] for x in facts) == 27
write_json('FACT-COORDINATES.json', facts)
decs = transform(decs_old, 'declarations')
decs['source'] = binding(new_source_path)
decs['facts'] = [{k: v for k, v in row.items() if k != 'fullType'} for row in facts]

# Reuse the exact hash-bound exhaustive validator/mapper, including all ordinary,
# optional, instance, fact, choice and binder checks. OUT points only to this unit.
block_start = tool_text.index("ordinary = decs['ordinaryLets']\n")
block_end = tool_text.index("preamble = (FREEZE / 'FROZEN-PREAMBLE.txt').read_bytes()\n", block_start)
validator = tool_text[block_start:block_end]
assert 'OLD /' not in validator and 'OUT /' not in validator
exec(compile(validator, str(tool_path) + ':reused-exhaustive-metadata-validator', 'exec'))

preamble = (FREEZE / 'FROZEN-PREAMBLE.txt').read_bytes()
head = (FREEZE / 'FROZEN-HEAD.txt').read_bytes()
closing = (FREEZE / 'FROZEN-CLOSING.txt').read_bytes()
assert old.startswith(preamble + head) and new.startswith(preamble + insertion + head)
assert new.endswith(closing)
assert text.count('set_option maxHeartbeats 800000 in\n') == 1
assert re.findall(r'(?m)^set_option[^\n]*', text) == re.findall(r'(?m)^set_option[^\n]*', old_text) + ['set_option maxHeartbeats 800000 in']
assert len(re.findall(r'(?m)^theorem\s', text)) == 1
assert not re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', text)
counts = {'publicOrdinary': len(public_rows), 'optionalOrdinaryCatalog': len(optional_map),
          'allLexicalOrdinaryLetOccurrencesIncludingTypeCopies': len(ordinary),
          'allLexicalInstanceLetOccurrencesIncludingTypeCopies': len(instances),
          'haveRowsWithFullFrozenTypes': len(facts), 'explicitFullTypeHaveRows': sum(x['explicitType'] for x in facts),
          'permittedInferredPropHaveRows': sum(not x['explicitType'] for x in facts),
          'sameDataChoices': sum(x['kind'] == 'DATA_CHOICE_SAME248' for x in choices),
          'proofWitnessChoicesFromSameExistential': sum(x['kind'] == 'PROOF_WITNESS_SAME_HMODEL' for x in choices),
          'newTopLevelHelpers': 0, 'newInstances': 0, 'newSelectors': 0, 'newNatCutoffs': 0}
assert counts == old_manifest['actualDerivedCounts']
ops = {k: 0 for k in ['Lean', 'lake', 'kernel', 'PP', 'AX', 'server', 'network', 'upload', 'Git',
                     'publicationAPI', 'children', 'Goal', 'schedule', 'sidebar']}
checks = {'schema': 'oq56-unit249-theorem-scoped-finite-option-static-checks-v1', 'atUTC': NOW,
          'source': binding(new_source_path), 'oldSource': binding(OLD / NAME),
          'authorizedOption': 'set_option maxHeartbeats 800000 in', 'optionScope': 'only the following single theorem command',
          'insertionNewLine': 15, 'oldTheoremLine': 15, 'newTheoremLine': 16,
          'insertionUTF8ByteRangeExclusive': [insertion_byte, insertion_byte + len(insertion)],
          'removedOptionRecoversEveryOldSourceByte': True, 'allMathematicalDeclarationAndProofBytesExact': True,
          'all28FactSourceSliceHashesUnchanged': True, 'all28FullFrozenFactTypesUnchanged': True,
          'all155Public159Optional730Let8InstanceTypesAndRHSMatched': True,
          'all2DataChoicesAnd2ProofWitnessChoicesUnchanged': True, 'noNewOptionOrProofLogic': True,
          'countsDerived': counts, 'coordinateDictionariesRecomputed': len(coordinate_checks),
          'coordinateDictionariesShifted35BytesAnd1Line': sum(a != b for _, a, b in coordinate_checks),
          'reusedMetadataTooling': binding(tool_path), 'reusedFunctions': names,
          'reusedExhaustiveValidatorSHA256': sha(validator.encode('utf-8')),
          'metadataExecutionHistory': [
              {'attempt': 1, 'result': 'NameError: slice_at was not selected from the prior metadata tool',
               'effects': 'Only this new directory source and fact map existed; no old source, Lean or server action.'},
              {'attempt': 2, 'correction': 'Select the same bound slice_at function before reusing the validator',
               'unchangedNewSourceVerifiedBeforeReuse': True,
               'result': 'Overstrict new-options guard rejected unchanged inherited set_option autoImplicit false'},
              {'attempt': 3, 'correction': 'Compare inherited options exactly and permit only the single frozen added option',
               'noSourceChangeFromPriorAttempt': True}],
          'UTF8NoBOM': True, 'LFOnly': True, 'sourceLF': 3825,
          'native02KnownEndedRC': 1, 'native02NoObject': True, 'native02Finite200000CapErrors': errors,
          'native02AllWarningsPreservedInOriginalDiagnostic': True, 'native02PriorAdditiveErrorAbsent': True,
          'LeanParsingOrElaborationPerformed': False, 'notIndependentReviewOrKernelEvidence': True, 'operations': ops}
write_json('STATIC-CHECKS.json', checks)
report = f'''# Unit249 有限定理选项修订

仅在旧第 15 行 theorem 前插入 `set_option maxHeartbeats 800000 in`，作用域仅为随后这一个定理声明。新源 SHA256 `{sha(new)}`，240965 字节、3825 LF，UTF-8 无 BOM、仅 LF，精确命中 freeze03。

移除新插入的 35 字节行即可逐字节还原旧源 8202e107…f1f899b；全部数学声明、假设、证明逻辑、let、RHS、实例、选择以及 28 个事实片段哈希保持原样。第 15 行及之后的原坐标按实际 UTF-8 重算为 +35 字节、+1 行，列号不变。复用已封存确定性元数据函数与完整库存校验逻辑，重新核对 730 let、8 letI、28 have/完整冻结类型、155 public、159 optional、2 same-data choices；并未重新生成或重读不变数学证明。

native02 的实际 RC1/noO、26.810858 秒、默认 200000 心跳上限、3819:74 tactic/15:0 whnf 两条诊断和所有 warnings 原样保留；原加法接口错误已不存在。该失败不是内核通过，新资源选项也不构成证明检查结果。独审旧源 CORRECT 与完整旧覆盖按精确哈希复用，新选项差异仍待独立审查，随后由 lead 安排新源 native/同首个成功原对象实际 TYPE/必需 VALUE/transitive AX。

本单元没有 Lean、PP、AX、服务器、网络、上传、Git、外部 API、publication 或 children 操作。sourceAccepted=false，qualified=false，kernelPending=true；fullOQ56=OPEN。请求模型/effort 保持 gpt-6.1-sol/xhigh，实际模型/effort/usage 不可见，均记 null。
'''
(OUT / 'DELTA.md').write_bytes(report.encode('utf-8'))
input_paths = [f3_path, FREEZE / 'frozen-declaration.json', UNIT / 'freeze-02/frozen-declaration.json',
               OLD / NAME, OLD / 'MANIFEST.json', old_release_path, tool_path,
               OLD / 'FACT-COORDINATES.json', OLD / 'DECLARATION-COORDINATES.json', OLD / 'OPTIONAL-MAPPING.json',
               review_release_path, Path(review_release['manifest']['path']), Path(review_release['sourceManifest']['path']),
               Path(review_release['supplement']['path']), Path(supplement['sourceReportUnchanged']['path']),
               Path(f3['knownEndedNative02']['projection']['path'])]
input_paths += [Path(b['path']) for b in freeze1['files']]
inputs = [binding(p) for p in dict.fromkeys(input_paths)]
payload_names = [NAME, 'FACT-COORDINATES.json', 'DECLARATION-COORDINATES.json', 'OPTIONAL-MAPPING.json',
                 'STATIC-CHECKS.json', 'DELTA.md', 'resource_metadata.py']
payloads = [binding(OUT / p) for p in payload_names]
manifest = {'schema': 'oq56-unit249-theorem-scoped-finite-option-author-manifest-v1', 'atUTC': NOW,
            'role': '/root/oq56_unit249_author_repair01', 'ownerChat': '01a1822b-1815-7f21-a1af-2e0b15ee67a5',
            'rootCoordinator': '01a17d3c-6dfd-7cc0-94ed-35d758a423a5', 'ownedRoot': OUT.as_posix(),
            'unit': 249, 'module': old_manifest['module'], 'publicTheorem': old_manifest['publicTheorem'],
            'STATUS': 'EXACT_FROZEN_THEOREM_SCOPED_FINITE_OPTION_SEALED_UNCHECKED',
            'source': binding(new_source_path), 'sourceLF': 3825, 'sourceUTF8NoBOM': True, 'sourceLFOnly': True,
            'oldSource': binding(OLD / NAME), 'frozenDeclaration': binding(f3_path),
            'onlyDelta': delta, 'removedOptionRecoversEveryOldSourceByte': True,
            'allMathematicalDeclarationAndProofBytesExact': True, 'all28FactSourceSliceHashesUnchanged': True,
            'actualDerivedCounts': counts, 'inputCountDerived': len(inputs), 'inputs': inputs,
            'payloadCountDerivedExcludingManifestAndLastRelease': len(payloads), 'payloads': payloads,
            'allInputsAndPayloadsHashBound': True, 'sourceCoordinateMaps': {
                'facts': binding(OUT / 'FACT-COORDINATES.json'), 'declarations': binding(OUT / 'DECLARATION-COORDINATES.json'),
                'all159OptionalRows': binding(OUT / 'OPTIONAL-MAPPING.json')},
            'reusedMetadataTooling': binding(tool_path), 'reusedExhaustiveValidatorSHA256': sha(validator.encode('utf-8')),
            'priorIndependentSourceVerdict': 'CORRECT', 'priorIndependentRelease': binding(review_release_path),
            'priorNativeFailure': {'projection': binding(f3['knownEndedNative02']['projection']['path']),
                                   'receiptSHA256': diagnostic['receipt']['sha256'], 'actualRC': 1, 'object': None,
                                   'preservedUnchanged': True, 'notConvertedToPass': True},
            'sourceComplete': True, 'sourceAccepted': False, 'independent': False, 'qualified': False,
            'kernelChecked': False, 'kernelPending': True, 'axiomAudited': False,
            'noNewAssumptionChoiceLocalFactInstanceOrProofLogic': True,
            'nativeResourcesUnchanged': f3['nativeResourcesUnchanged'], 'fullOQ56': 'OPEN',
            'nextExactDependency': 'Same independent reviewer checks only the frozen option/coordinate delta using prior complete SOURCE coverage; lead schedules new-source native and same-first-successful-original-object allactual TYPE/required VALUE/transitive AX.',
            'operations': ops, 'operationsClarification': 'Local file tools and collaboration ACK used; API zero refers external publication/API operations.',
            'requestedModel': 'gpt-6.1-sol', 'requestedEffort': 'xhigh', 'actualBackend': None,
            'actualModel': None, 'actualEffort': None,
            'usage': {k: None for k in ['input', 'cachedInput', 'output', 'reasoningSubset']}}
write_json('MANIFEST.json', manifest)
for b in inputs + payloads:
    verify(b)
print(json.dumps({'status': manifest['STATUS'], 'source': manifest['source'], 'manifest': binding(OUT / 'MANIFEST.json'),
                  'inputs': len(inputs), 'payloads': len(payloads), 'countsDerived': counts,
                  'coordinatesRecomputed': len(coordinate_checks),
                  'coordinatesShifted': sum(a != b for _, a, b in coordinate_checks), 'releaseWritten': False}, ensure_ascii=True))
