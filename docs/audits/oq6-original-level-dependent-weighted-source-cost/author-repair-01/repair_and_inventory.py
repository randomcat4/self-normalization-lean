from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re

# Pure local byte repair and source inventory; this file never invokes Lean,
# subprocesses, a server, a network client, Git, or an API.
BASE = Path('C:/game/shao lean/drafts/oq56/unit250')
OUT = BASE / 'author-repair-01'
ROLE = '/root/oq56_unit250_author_repair01'
LEAD = '01a1822b-1815-7f21-a1af-2e0b15ee67a5'
ROOT = '01a17d3c-6dfd-7cc0-94ed-35d758a423a5'
SOURCE_NAME = 'OriginalLevelDependentWeightedSourceCost.lean'


def digest(b):
    return hashlib.sha256(b).hexdigest()


def binding(p):
    p = Path(p)
    b = p.read_bytes()
    return {'path': p.as_posix(), 'bytes': len(b), 'sha256': digest(b)}


def save_new(name, value):
    b = (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode('utf-8')
    with (OUT / name).open('xb') as f:
        f.write(b)


def now():
    return datetime.now(timezone.utc).isoformat()


assert not (OUT / 'lastzeroRELEASE.json').exists(), 'Released author must not write'
assert set(p.name for p in OUT.iterdir()) == {'repair_and_inventory.py'}, 'Fresh bounded output only'
inputs = {}


def read_bound(path, expected_sha=None, expected_bytes=None):
    p = Path(path)
    b = p.read_bytes()
    if expected_sha is not None:
        assert digest(b) == expected_sha, p
    if expected_bytes is not None:
        assert len(b) == expected_bytes, p
    inputs[p.as_posix()] = binding(p)
    return b


freeze2_b = read_bound(BASE / 'freeze-02/frozen-declaration.json',
    'dd409f67c9713400edad5ffec1c71a9b6afc5d3ac3b65163bb4597e4ece260bf', 2935)
clarification_b = read_bound(BASE / 'freeze-02/ANNOTATION-COORDINATE-CLARIFICATION.json',
    '217b674eb7e22afa4420f59e58e1f38642609d20f52aab7d6439b72a237d341e', 858)
freeze1_b = read_bound(BASE / 'freeze-01/frozen-declaration.json',
    'a26f0a109e8f06fd03c4326ecd868ed882ae40f84a927c172b67e567ac8166de', 4352)
freeze2 = json.loads(freeze2_b)
freeze1 = json.loads(freeze1_b)
clarification = json.loads(clarification_b)
assert clarification['exactAuthorizedSourceSHA256'] == freeze2['expectedNewSource']['sha256']
for item in freeze1['files'] + freeze1['originalSources'] + freeze1['exactAcceptedBearingInterfaces']:
    read_bound(item['path'], item['sha256'], item['bytes'])
old = read_bound(BASE / 'author-01' / SOURCE_NAME,
    '17ab15bf0299531a33ba9710cbb8e43c61d59de6d306aeb5e900378b2a799c2a', 19166)
read_bound(BASE / 'author-01/lastzeroRELEASE.json',
    'baef7a04ddea4a296e592c1dedfbf3e3368b61ff223c48dff85d29283a9a38b8', 2246)
read_bound(BASE / 'author-01/assemble_and_inventory.py')
old_inventory_b = read_bound(BASE / 'author-01/SOURCE-INTERFACE-INVENTORY.json')
read_bound(BASE / 'author-01/MANIFEST.json',
    '4954ce520a25cf3eaa6bc8a23a26a3c59925a3a52cf86343edcbeab2aabca064', 6452)
native_b = read_bound(BASE / 'lead-execution-01/native-complete-diagnostic-projection.json',
    'b21c373763000c92aa3a949e27dbeeef3bfd88213d24505e24482fb65ab3a8f0', 3014)
parent_b = read_bound(BASE / 'parent-independent-source-intake-01.json',
    '60461811f280c359c178f4b358a50d1528e5d092d6625c7c6d4743666e28da9e', 1781)
parent = json.loads(parent_b)
for key in ['initialSemanticReport', 'initialSemanticVerdict', 'nativeGapAddendum',
            'currentVerdict', 'stageRelease']:
    item = parent[key]
    read_bound(item['path'], item['sha256'], item['bytes'])
coverage_b = read_bound(BASE / 'source-review-01/COVERAGE.json')
assert digest(coverage_b).startswith('05e0da2b')
read_bound(BASE / 'source-review-01/MANIFEST.json',
    '9e2b6996cd3dfc28d75b3a11431c48f8ec7f818d012f933fba6c1932cf5710fd', 8876)
read_bound(BASE / 'source-review-01/NATIVE01-STAGE-MANIFEST.json',
    'd21a0206e27593ef52455cd67d5c7bded4881cf4f2491d0ef11cad84e0a00e50', 2618)
native = json.loads(native_b)
assert native['actualRC'] == 1 and native['objectAfter'] is None
assert native['allOwnedEnded'] and native['beforeAfterEqual'] and native['preservationEqual']
assert not native['timedOut'] and not native['cleanupEvents']
assert native['ownershipIssue'] is None and native['postError'] is None
assert len(native['errors']) == 3
for rel in ['author-01/lastzeroRELEASE.json', 'source-review-01/NATIVE01-RELEASE.json']:
    release = json.loads((BASE / rel).read_bytes())
    assert release['FINALWRITE'] and all(v == 0 for v in release['sixZero'].values())

save_new('READING-RUNTIME-ACK.json', {
    'schema': 'unit250-repair-author-actual-read-ack-v1', 'atUTC': now(),
    'role': ROLE, 'ownerChat': LEAD, 'currentRoot': ROOT,
    'actualRuntime': 'RUNNING_BOUNDED_PURELOCAL_REPAIR', 'writerScope': OUT.as_posix(),
    'completeRead': ['freeze-01 complete declaration', 'freeze-02 complete repair freeze',
        'coordinate clarification', 'old 363LF full source', 'independent REPORT.md',
        'GAP-ADDENDUM-NATIVE01.md', 'all three complete native errors',
        'old author and independent reviewer FINALWRITE releases', 'old inventory script read only'],
    'unaffectedCompleteOriginalAndProofReview': 'Reused only by exact old review bindings; this role does not claim a new independent full review.',
    'requestedModel': 'gpt-6.1-sol', 'requestedEffort': 'xhigh',
    'actualModel': None, 'actualEffort': None,
    'usage': {'input': None, 'cachedInput': None, 'output': None, 'reasoningSubset': None},
    'writers': 1, 'heavyCommands': 0, 'inflightExecution': 0,
    'pendingExternal': 0, 'children': 0, 'uncertainOperations': 0,
    'hashDiagnosticNote': 'One preliminary read-only diagnostic mistakenly extended a supplied release SHA prefix to an unrelated full digest; actual reviewer release b605af1240c214c3cdc00fd65db5ddc7b1607f1053df5d6352a4ae551fee824f is exact against parent-independent-source-intake-01.json. No input file changed.',
})

new = old
deltas = []
for index, delta in enumerate(freeze2['allowedOnlyProofDeltas'], 1):
    before = delta['before'].encode('utf-8')
    after = delta['after'].encode('utf-8')
    assert old.count(before) == 1 and new.count(before) == 1
    old_start = old.index(before)
    new_start = new.index(before)
    new = new[:new_start] + after + new[new_start + len(before):]
    deltas.append({'index': index, 'before': delta['before'], 'after': delta['after'],
        'oldByteStart0': old_start, 'oldByteEndExclusive0': old_start + len(before),
        'newByteStart0': new_start, 'newByteEndExclusive0': new_start + len(after),
        'oldLinesInclusive': [old[:old_start].count(b'\n') + 1,
            old[:old_start + len(before)].count(b'\n')],
        'newLinesInclusive': [new[:new_start].count(b'\n') + 1,
            new[:new_start + len(after)].count(b'\n')],
        'beforeSha256': digest(before), 'afterSha256': digest(after)})
expected = freeze2['expectedNewSource']
assert digest(new) == expected['sha256'] and len(new) == expected['bytes']
assert new.count(b'\n') == expected['LF']
assert new.decode('utf-8').encode('utf-8') == new and b'\r' not in new
assert not new.startswith(b'\xef\xbb\xbf')
reverse = new
for delta in reversed(freeze2['allowedOnlyProofDeltas']):
    after, before = delta['after'].encode('utf-8'), delta['before'].encode('utf-8')
    assert reverse.count(after) == 1
    reverse = reverse.replace(after, before, 1)
assert reverse == old
segments = []
old_cursor = new_cursor = 0
for delta in deltas + [{'oldByteStart0': len(old), 'newByteStart0': len(new),
                        'oldByteEndExclusive0': len(old), 'newByteEndExclusive0': len(new)}]:
    a = old[old_cursor:delta['oldByteStart0']]
    b = new[new_cursor:delta['newByteStart0']]
    assert a == b
    segments.append({'oldByteRange0HalfOpen': [old_cursor, delta['oldByteStart0']],
        'newByteRange0HalfOpen': [new_cursor, delta['newByteStart0']],
        'bytes': len(a), 'sha256': digest(a), 'exactlyEqual': True})
    old_cursor, new_cursor = delta['oldByteEndExclusive0'], delta['newByteEndExclusive0']
pre = (BASE / 'freeze-01/FROZEN-PREAMBLE.txt').read_bytes()
head = (BASE / 'freeze-01/FROZEN-HEAD.txt').read_bytes()
closing = (BASE / 'freeze-01/FROZEN-CLOSING.txt').read_bytes()
assert old.startswith(pre + head) and new.startswith(pre + head)
assert old.endswith(closing) and new.endswith(closing)
with (OUT / SOURCE_NAME).open('xb') as f:
    f.write(new)


def parameter_sites(signature, start_line, name):
    pos = signature.index(name) + len(name)
    answer = []
    while pos < len(signature):
        while pos < len(signature) and signature[pos].isspace():
            pos += 1
        if pos >= len(signature) or signature[pos] not in '([{':
            break
        begin = pos
        stack = [signature[pos]]
        pos += 1
        while stack:
            ch = signature[pos]
            if ch in '([{':
                stack.append(ch)
            elif ch in ')]}':
                stack.pop()
            pos += 1
        content = signature[begin + 1:pos - 1]
        if ':' in content:
            names, tp = content.split(':', 1)
            names = names.strip().split()
        else:
            names, tp = [None], content
        prefix = signature[:begin]
        answer.append({'line': start_line + prefix.count('\n'),
            'columnCodepoint1': len(prefix.rsplit('\n', 1)[-1]) + 1,
            'completeSourceBinder': signature[begin:pos], 'names': names,
            'fullTypeExact': tp.strip()})
    return answer


def source_records(data):
    lines = data.decode('utf-8').splitlines()
    records = []
    for i, line in enumerate(lines):
        m = re.match(r'^(\s*)(let|have|letI|haveI)\s+([^\s(:]+)', line)
        if not m:
            continue
        indent, kind, name = len(m.group(1)), m.group(2), m.group(3)
        end = i + 1
        while end < len(lines):
            line_next = lines[end]
            if line_next.strip() and len(line_next) - len(line_next.lstrip()) <= indent:
                break
            end += 1
        block = '\n'.join(lines[i:end])
        marker = block.find(':=')
        signature = block[:marker].rstrip() if marker >= 0 else block
        rhs = block[marker + 2:].lstrip() if marker >= 0 else None
        scope = 'FROZEN_RESULT_TELESCOPE' if i < (pre + head).count(b'\n') else 'THEOREM_PROOF'
        records.append({'id': f'{kind}:{name}:{i + 1}', 'kind': kind, 'name': name,
            'lineStart': i + 1, 'lineEndInclusive': end, 'scope': scope,
            'indentation': indent, 'fullSourceSignature': signature, 'completeRHS': rhs,
            'completeSourceBlock': block,
            'sourceBlockSha256': digest((block + '\n').encode('utf-8')),
            'declarationParameterBinders': parameter_sites(signature, i + 1, name)})
    for record in records:
        parents = [p for p in records if p['lineStart'] < record['lineStart'] <= p['lineEndInclusive']
            and p['indentation'] < record['indentation']]
        record['lexicallyEnclosingBindingIds'] = [p['id'] for p in parents]
        record['visiblePriorProofBindingIds'] = [p['id'] for p in records
            if p['scope'] == 'THEOREM_PROOF' and p['lineEndInclusive'] < record['lineStart']
            and (p['indentation'] == 2 or any(q['lineStart'] < p['lineStart'] < record['lineStart'] <= q['lineEndInclusive']
                and q['indentation'] < p['indentation'] for q in parents))]
        record['completeAmbientTheoremParametersReference'] = 'publicFrozenCompleteHead'
        record['ownParameterizedBindersReference'] = 'fullSourceSignature'
    return records


SITE_PATTERN = r'\b(?:fun|intro|by_cases)\b|∀|∫|∑|\{Ω\s*:|\(Ω\s*:|\[mΩ\s*:|\[IsProbabilityMeasure'


def binder_sites(data, records):
    result = []
    known = {'o': 'Ω', 'y': 'Ω', 't': 'Ω × Ω', 'ζ': 'Fin n → Ω',
        'i': 'Fin n', 'j': 'Fin n', 'k': 'Fin n', "k'": 'Fin n',
        'hj': 'j ∈ (Finset.univ : Finset (Fin n))',
        "hk'": "k' ∈ (Finset.univ : Finset (Fin n))",
        'hij': "j = i ∨ k' = i", 'hjk': "j < k'"}
    for i, line in enumerate(data.decode('utf-8').splitlines()):
        for m in re.finditer(SITE_PATTERN, line):
            enclosing = [r for r in records if r['lineStart'] <= i + 1 <= r['lineEndInclusive']]
            owner = enclosing[-1] if enclosing else None
            kind, tail = m.group(0), line[m.end():]
            if kind == 'fun':
                binder_text = tail.split('=>', 1)[0].strip()
            elif kind == 'intro':
                binder_text = tail.strip()
            elif kind == 'by_cases':
                binder_text = tail.split(':', 1)[0].strip()
            elif kind in ['∀', '∫', '∑']:
                binder_text = tail.split(',', 1)[0].strip()
            else:
                binder_text = tail
            names_text = binder_text.split(':', 1)[0].replace('(', '').replace(')', '').strip()
            if kind == '∑' and '∈' in names_text:
                names_text = names_text.split('∈', 1)[0].strip()
            types = []
            for name in names_text.split():
                tp = known.get(name)
                if name == '_':
                    if ':' in binder_text:
                        tp = binder_text.split(':', 1)[1].strip()
                    elif "k' _" in binder_text:
                        tp = "k' ∈ (Finset.univ : Finset (Fin n)).erase j"
                    elif 'j _' in binder_text:
                        tp = 'j ∈ (Finset.univ : Finset (Fin n)).erase i' if owner and owner['name'] == 'hSdeleteM' else 'j ∈ (Finset.univ : Finset (Fin n))'
                    elif 'i _' in binder_text:
                        tp = 'i ∈ (Finset.univ : Finset (Fin n))'
                if tp is not None:
                    types.append({'name': name, 'fullType': tp})
            if kind.startswith('{Ω') or kind.startswith('(Ω'):
                types = [{'name': 'Ω', 'fullType': 'Type u'}]
            elif kind.startswith('[mΩ'):
                types = [{'name': 'mΩ', 'fullType': 'MeasurableSpace Ω'}]
            elif kind == '[IsProbabilityMeasure':
                types = [{'name': None, 'fullType': 'IsProbabilityMeasure μ'}]
            result.append({'siteOrdinal1': len(result) + 1, 'line': i + 1,
                'column': m.start() + 1, 'columnUnit': 'Unicode codepoints, 1-based',
                'kind': kind, 'enclosingSourceBlock': owner['id'] if owner else 'PUBLIC_FROZEN_THEOREM',
                'enclosingBindingIds': [r['id'] for r in enclosing],
                'binderSourceText': binder_text, 'inferredSourceBinderTypes': types,
                'completeLine': line})
    return result


records_old, records = source_records(old), source_records(new)
sites_old, sites = binder_sites(old, records_old), binder_sites(new, records)
assert [(r['kind'], r['name'], r['fullSourceSignature']) for r in records_old] == [
    (r['kind'], r['name'], r['fullSourceSignature']) for r in records]
old_inventory = json.loads(old_inventory_b)
assert [(r['kind'], r['name'], r['completeSourceBlock']) for r in records_old] == [
    (r['kind'], r['name'], r['completeSourceBlock']) for r in old_inventory['bindings']]
assert [(s['line'], s['column'], s['kind']) for s in sites_old] == [
    (s['line'], s['column'], s['kind']) for s in old_inventory['allVariableBinderSites']]
changed = [(a, b) for a, b in zip(records_old, records)
    if a['completeSourceBlock'] != b['completeSourceBlock']]
assert [b['name'] for a, b in changed] == ['hEdgeM', 'hFullDom', 'hDeleteDom']
assert len(sites) == len(sites_old) + 1
public_signature = head.decode('utf-8').split(' :\n    let g', 1)[0]
public_parameters = parameter_sites(public_signature, pre.count(b'\n') + 1,
    'actual_original_level_dependent_weighted_source_cost')
counts = {'namedBindings': len(records), 'let': sum(r['kind'] == 'let' for r in records),
    'resultTelescopeLet': sum(r['kind'] == 'let' and r['scope'] == 'FROZEN_RESULT_TELESCOPE' for r in records),
    'proofLet': sum(r['kind'] == 'let' and r['scope'] == 'THEOREM_PROOF' for r in records),
    'have': sum(r['kind'] == 'have' for r in records), 'binderMarkerSites': len(sites),
    'oldBinderMarkerSitesRederived': len(sites_old), 'publicParameterGroups': len(public_parameters),
    'explicitDeclarationParameterGroups': len(public_parameters) + sum(len(r['declarationParameterBinders']) for r in records)}
save_new('SOURCE-INTERFACE-INVENTORY.json', {
    'schema': 'unit250-repair-lossless-source-interface-inventory-v2',
    'status': 'SOURCE_ONLY_INVENTORY_GENERATED_ACTUAL_MACHINE_INTERFACES_PENDING',
    'source': binding(OUT / SOURCE_NAME), 'sourceLF': new.count(b'\n'),
    'publicDeclaration': 'Shao.OQ6.OriginalLevelDependentWeightedSourceCost.actual_original_level_dependent_weighted_source_cost',
    'publicFrozenPreamble': pre.decode('utf-8'), 'publicFrozenCompleteHead': head.decode('utf-8'),
    'publicClosing': closing.decode('utf-8'), 'publicDeclarationParameterBinders': public_parameters,
    'bindings': records, 'allVariableBinderSites': sites, 'actualDerivedCounts': counts,
    'binderSiteDefinition': 'Literal occurrences of SITE_PATTERN in this exact source, with declaration-parameter groups separately inventoried. A marker site may bind several names; this is not an elaborated owner count or a claim to count every variable occurrence.',
    'binderSitePattern': SITE_PATTERN, 'coordinateConvention': '1-based source line and Unicode-codepoint column',
    'sourceBlockHashConvention': 'SHA256(UTF8(completeSourceBlock + one LF))',
    'fullTypeDictionary': old_inventory['fullTypeDictionary'],
    'allLocalFullSignaturesByteExactAgainstOldSource': True,
    'allExplicitLocalSubstantiveFactsHaveType': all(':' in r['fullSourceSignature'] for r in records if r['kind'] == 'have'),
    'nestedFactParentage': [{'name': r['name'], 'lines': [r['lineStart'], r['lineEndInclusive']],
        'enclosingBindingIds': r['lexicallyEnclosingBindingIds'], 'visiblePriorProofBindingIds': r['visiblePriorProofBindingIds']}
        for r in records if r['indentation'] > 2 and r['scope'] == 'THEOREM_PROOF'],
    'generatedActualOwnerTypesAndNonTheoremValues': None,
    'generatedInterfaceReason': 'No Lean/PP/AX execution authorized for this author. This lossless source inventory is not machine TYPE/VALUE/owner evidence.',
})

forbidden = re.findall(rb'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', new)
assert not forbidden
assert len(re.findall(rb'^theorem ', new, re.M)) == 1
assert not re.search(rb'^(?:def|lemma|instance|structure|class|opaque|abbrev)\b', new, re.M)
static = {
    'schema': 'unit250-three-frozen-deltas-static-byte-check-v1', 'atUTC': now(),
    'oldSource': binding(BASE / 'author-01' / SOURCE_NAME), 'newSource': binding(OUT / SOURCE_NAME),
    'utf8Strict': True, 'BOM': False, 'CRBytes': new.count(b'\r'), 'LFCount': new.count(b'\n'),
    'authorizedThreeExactReplacementsOnly': True, 'reverseThreeReplacementsReconstructOldExact': reverse == old,
    'deltas': deltas, 'allUnchangedByteSegments': segments,
    'frozenPreambleExact': new.startswith(pre), 'frozenPreambleAndHeadExact': new.startswith(pre + head),
    'frozenClosingExact': new.endswith(closing), 'allLocalFullTypesExact': True,
    'changedBindingProofsOnly': [{'name': b['name'],
        'oldLines': [a['lineStart'], a['lineEndInclusive']], 'newLines': [b['lineStart'], b['lineEndInclusive']],
        'oldSourceBlockSha256': a['sourceBlockSha256'], 'newSourceBlockSha256': b['sourceBlockSha256'],
        'fullSignatureExact': a['fullSourceSignature'] == b['fullSourceSignature']}
        for a, b in changed],
    'actualDerivedCounts': counts, 'publicTheorems': 1, 'newTopLevelHelpers': 0,
    'explicitNewInstances': 0, 'newFactBindings': len(records) - len(records_old),
    'newLambdaBinderMarkerOccurrences': len(sites) - len(sites_old),
    'forbiddenConstructMatches': [],
    'sourceAnalyticProducerCalls': new.count(b'Shao.OQ6.SourceAnalyticCost.actual_quadratic_source_analytic_cost'),
    'noNewPremiseInstanceModelChoiceOrQuantifier': True,
    'kernel': 'NOT_RUN_NEW_SOURCE', 'transitiveAxioms': 'NOT_RUN_NEW_SOURCE',
    'independentAffectedFinalReview': 'PENDING_SAME_SEPARATE_REVIEWER',
    'sourceAccepted': False, 'qualified': False,
}
save_new('STATIC-CHECK.json', static)

delta_text = f'''# Unit250 冻结的三个形式证明修复

状态：完整修复候选已按精确冻结字节封存；新源未运行 Lean、PP 或 AX，未获得独立 affected-delta/final-machine 接受，sourceAccepted=false、qualified=false。

旧源 SHA256 `{digest(old)}`，{len(old)}B、{old.count(bytes([10]))}LF。
新源 SHA256 `{digest(new)}`，{len(new)}B、{new.count(bytes([10]))}LF，UTF-8、无 BOM、0CR。

1. 新238–240行：只为原 `hr.comp` 的坐标对映射加显式 `Measurable (fun ζ : Fin n → Ω => (ζ j, ζ k'))` 类型标注，固定映射定义域。没有引入新 fact、实例或可测性前提。hEdgeM 的完整类型保持。
2. 新327行：在 hFullDom 中用 `add_le_add le_rfl` 配对共同左前缀 `z * |D1 ζ|` 与 `z^2 * B ζ ≤ z^2 * BA ζ`；原非负乘子证明不变。hFullDom 的完整类型保持。
3. 新333行：在 hDeleteDom 中以同样 API 保持共同左前缀 `||D1 ζ|-|Ddeleted ζ i||`，右分量继续用 z 非负乘真实预算删除差支配；原 cap 与指数的非负乘法步骤不变。hDeleteDom 的完整类型保持。

STATIC-CHECK.json 给出三个 before/after 全块、旧新字节/行坐标、四段不变字节区间及 SHA256；逆替换精确重建旧源。除此之外所有字节精确相同，冻结 preamble/head/closing 与全部 let/have 完整类型不变。原模型及全部量词、full/deleted 权重、原 n 与 (n-2)^2 删除归一化、真实绝对删除差、预算当前层级 z、原 cap `min |z*ξ0_i| 1`、同一正积分 I=m^n 与最终常数全部保留。没有涉及 unit249 的 fixed clipping1。

从新365LF实际重新导出：{counts['namedBindings']} 个命名绑定，{counts['let']} let（结果 telescope {counts['resultTelescopeLet']}，proof {counts['proofLet']}）和 {counts['have']} have；{counts['binderMarkerSites']} 个定义明确的源 binder-marker 站点（旧源重导 {counts['oldBinderMarkerSitesRederived']}），{counts['publicParameterGroups']} 组公共参数。新增站点仅为类型标注中的 lambda；不是新假设或 machine owner。SOURCE-INTERFACE-INVENTORY.json 包含逐个完整 signature/RHS/source block、实际新行列、局部 binder 类型和 hDeleteM 内嵌 hAbsD/hAbsB 的作用域。

既有独立审稿的363LF全文及 p51/p54覆盖仅在三个delta之外按精确旧hash复用；原REPORT、COVERAGE、MANIFEST、GAP及native01失败资料均未改写。原native01自然RC1/3errors/noO保持，不是新源的pass；这里不重复旧production、proof、TYPE或AX检查。同一独立审稿角色仍需核对真实三个delta与首次成功原始O的全部actual TYPE、required VALUE及逐owner递归AX。source-level inventory不替代这些机器材料。

此角色只在 author-repair-01 写文件，无 Lean/lake/PP/AX、服务器、网络、上传、Git/API、发布、子智能体、Goal、schedule 或sidebar操作。请求 gpt-6.1-sol/xhigh；实际模型、强度及input/cachedInput/output/reasoningSubset用量均不可见，记null。
'''
with (OUT / 'DELTA.md').open('xb') as f:
    f.write(delta_text.encode('utf-8'))

# Verify all pinned read-only inputs again after the sole source repair.
for item in inputs.values():
    assert binding(item['path']) == item
save_new('READ-ONLY-INPUT-BINDINGS.json', {
    'schema': 'unit250-repair-readonly-input-bindings-v1', 'atUTC': now(),
    'inputCountDerived': len(inputs), 'allExactBeforeAndAfter': True,
    'inputs': list(inputs.values()),
    'readingScope': 'Hash binding of all listed inputs is distinct from complete semantic reading. Prior p51/p54 and unaffected proof reading are attributed to the preserved independent review.',
})
payloads = [binding(p) for p in sorted(OUT.iterdir()) if p.is_file()]
save_new('MANIFEST.json', {
    'schema': 'unit250-three-frozen-deltas-author-repair-manifest-v1', 'atUTC': now(),
    'role': ROLE, 'ownerChat': LEAD, 'currentRoot': ROOT, 'writerScope': OUT.as_posix(),
    'status': 'EXACT_FROZEN_REPAIR_CANDIDATE_SEALED_MACHINE_AND_AFFECTED_REVIEW_PENDING',
    'source': binding(OUT / SOURCE_NAME), 'sourceLF': new.count(b'\n'),
    'payloadCountDerived': len(payloads), 'payloads': payloads,
    'inputCountDerived': len(inputs), 'inputBindings': binding(OUT / 'READ-ONLY-INPUT-BINDINGS.json'),
    'repairFreeze': binding(BASE / 'freeze-02/frozen-declaration.json'),
    'completeDeclarationFreeze': binding(BASE / 'freeze-01/frozen-declaration.json'),
    'annotationClarification': binding(BASE / 'freeze-02/ANNOTATION-COORDINATE-CLARIFICATION.json'),
    'allOtherBytesExact': True, 'allLocalFullTypesExact': True, 'actualDerivedSourceCounts': counts,
    'newSourceKernel': 'PENDING_SERVER', 'newSourceActualTYPERequiredVALUERecursiveAX': 'PENDING_SERVER',
    'independentAffectedAndMachineReview': 'PENDING_SAME_SEPARATE_REVIEWER',
    'sourceAccepted': False, 'qualified': False, 'fullOQ56': 'OPEN',
    'priorKnownFailureRetained': 'native01 exact old source natural RC1/3errors/noO',
    'nonClaims': freeze1['nonClaims'],
    'requestedModel': 'gpt-6.1-sol', 'requestedEffort': 'xhigh',
    'actualModel': None, 'actualEffort': None,
    'usage': {'input': None, 'cachedInput': None, 'output': None, 'reasoningSubset': None},
})
print(json.dumps({'source': binding(OUT / SOURCE_NAME), 'LF': new.count(b'\n'),
    'counts': counts, 'payloadCountDerived': len(payloads), 'inputCountDerived': len(inputs),
    'manifest': binding(OUT / 'MANIFEST.json'), 'kernel': 'NOT_RUN'}, ensure_ascii=False))
