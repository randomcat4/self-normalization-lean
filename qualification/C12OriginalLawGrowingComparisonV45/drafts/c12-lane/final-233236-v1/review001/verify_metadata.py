"""Local, read-only evidence verification; writes this review's metadata only."""
from pathlib import Path
import datetime
import hashlib
import json
import re

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[3]
NOW = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat()
SHA = lambda b: hashlib.sha256(b).hexdigest()
def read(p):
    return (ROOT / p).read_bytes()
def load(p):
    return json.loads(read(p).decode('utf-8-sig'))
def binding(p):
    b = read(p)
    return {'path': str(p).replace('\\', '/'), 'bytes': len(b), 'sha256': SHA(b)}
def check_binding(x):
    got = binding(x['path'])
    assert got['bytes'] == x['bytes'] and got['sha256'] == x['sha256'], x['path']
    return {**got, 'match': True}
def response(p):
    r = load(p)
    assert r.get('exit_code') == 0, p
    return json.loads(r['stdout'])
def write_new(name, value):
    p = OUT / name
    assert not p.exists(), f'refuse overwrite: {p}'
    with p.open('x', encoding='utf-8', newline='\n') as f:
        json.dump(value, f, ensure_ascii=False, indent=2)
        f.write('\n')
def direct_bindings(value):
    found = []
    if isinstance(value, dict):
        if all(k in value for k in ('path', 'bytes', 'sha256')):
            found.append(check_binding(value))
        else:
            for v in value.values():
                found.extend(direct_bindings(v))
    elif isinstance(value, list):
        for v in value:
            found.extend(direct_bindings(v))
    return found

activation_path = 'drafts/c12-lane/final-233236-v1/review001/parent-activation001.json'
activation = load(activation_path)
assert binding(activation_path) == {'path': activation_path, 'bytes': 25813, 'sha256': 'c8c91e0916ef1c4a908b85fbda99775eab490ae9e2e4771103a4d94cb3515b03'}
mandatory = [check_binding(x) for x in activation['mandatoryInputs']]
assert len(mandatory) == 93
ack = load('drafts/c12-lane/final-233236-v1/review001/ACTUAL-ACK.json')
assert ack['mandatoryAllPass'] and not ack['analysisStarted']
phase_path = mandatory[0]['path']
phase = load(phase_path)
phase_sha = binding(phase_path)['sha256']

old_review_roots = [
    'drafts/c12-lane/machine-source-batch-229233-v1/review001',
    'drafts/c12-lane/machine-source-batch-231236237-v1/review001',
    'drafts/c12-lane/machine-232-v1/review001',
]
reuse_seals = []
for d in old_review_roots:
    seal = load(d + '/PAYLOAD-SEAL.json')
    checked = [check_binding(v) for v in seal['payloads']]
    assert len(checked) == seal['count']
    release = load(d + '/RELEASE.json')
    assert len(release['runtime']) == 16 and set(release['runtime'].values()) == {0}
    reuse_seals.append({'seal': binding(d + '/PAYLOAD-SEAL.json'),
                       'payloadCount': len(checked), 'payloads': checked,
                       'release': binding(d + '/RELEASE.json'), 'all16RuntimeZero': True})

extra = []
for u in activation['units']:
    freeze = load(u['freeze']['path'])
    for item in freeze['frozen']:
        extra.append(check_binding(item))
    extra.extend(direct_bindings(freeze['completeMathematicalCandidate']))
extra.append(check_binding(load(activation['units'][0]['freeze']['path'])['inputs'][-1]))
qualification_path = 'drafts/c12-lane/actual-original-small-budget-double-v1/parent-final-qualification001.json'
qualification = load(qualification_path)
assert qualification['formalQualified']
qualification_direct = direct_bindings(qualification)

interface_file = old_review_roots[0] + '/INTERFACE-CHECK.json'
interfaces_old = load(interface_file)
interface_bindings = []
for item in interfaces_old['interfaces']:
    interface_bindings.append(check_binding(item['parentFileBinding']))
for item in interfaces_old['snapshotSourceBindings'] if 'snapshotSourceBindings' in interfaces_old else []:
    pass
# The prior complete interface review is payload-sealed above. Exact source inputs
# from the freeze are checked without replaying any of their accepted proofs.
freeze233 = load(activation['units'][0]['freeze']['path'])
for item in freeze233['inputs']:
    extra.append(check_binding(item))

unit_data = []
all_intervals = []
for u in activation['units']:
    number = u['unit']
    source_path = u['source']['path']
    src = read(source_path)
    text = src.decode('utf-8', errors='strict')
    assert not src.startswith(b'\xef\xbb\xbf') and b'\r' not in src and src.endswith(b'\n')
    assert src.count(b'\n') == u['sourceFullLF']
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', text)
    theorem_start = src.index(b'theorem ')
    by_marker = src.index(b':= by\n', theorem_start)
    proof_start = by_marker + 3
    proof_end = src.rfind(b'\nend ')
    proof = src[proof_start:proof_end]
    head = src[theorem_start:by_marker].rstrip() + b'\n'
    preamble = src[:theorem_start]
    freeze = load(u['freeze']['path'])
    assert preamble == read(freeze['frozen'][0]['path'])
    assert head == read(freeze['frozen'][1]['path'])
    assert len(proof) == u['wholeProofBytes'] and SHA(proof) == u['wholeProofSHA256']
    source_record = {**binding(source_path), 'fullLF': src.count(b'\n'),
                     'strictUTF8': True, 'BOM': False, 'CRCount': 0,
                     'completeSourceRead': True,
                     'preamble': {**binding(freeze['frozen'][0]['path']), 'exactByteMatch': True},
                     'frozenPublicHead': {**binding(freeze['frozen'][1]['path']), 'exactByteMatch': True},
                     'wholeProof': {'byteRangeHalfOpen': [proof_start, proof_end],
                                    'startLine': src[:proof_start].count(b'\n') + 1,
                                    'endLine': src[:proof_end].count(b'\n'),
                                    'bytes': len(proof), 'sha256': SHA(proof),
                                    'completeRead': True}}
    type_path = u['actualTYPE']['path']
    native = str(Path(type_path).parent.parent).replace('\\', '/')
    receipt_dir = native + '/server-receipts'
    owner = load(receipt_dir + '/owned-audit.json')
    idx = load(receipt_dir + '/actual-types-values-index.json')
    raw = read(type_path)
    assert raw.count(b'\n') == u['actualTYPEFullLF']
    type_text = raw.decode('utf-8', errors='strict')
    assert all(x not in type_text for x in ['⋯', '…', '[truncated]', '<truncated>'])
    matches = list(re.finditer(rb'(?m)^TARGET_DECL (\S+) KIND (\S+) AXIOMS \[', raw))
    names = []
    coverage = []
    for j, m in enumerate(matches):
        end = matches[j + 1].start() if j + 1 < len(matches) else len(raw)
        block = raw[m.start():end]
        type_start = m.start() + block.index(b'ACTUAL_TYPE ') + len(b'ACTUAL_TYPE ')
        name, kind = m.group(1).decode(), m.group(2).decode()
        assert kind == 'theorem' and b'DEFINITION_VALUE ' not in block
        axes = re.search(rb'AXIOMS \[([\s\S]*?)\]\nACTUAL_TYPE ', block).group(1).decode()
        axioms = [x.strip() for x in axes.split(',') if x.strip()]
        expected = next(x for x in owner['module_owned_constants'] if x['name'] == name)
        assert expected['kind'] == kind and expected['axioms'] == axioms
        assert set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}
        start_line = raw[:m.start()].count(b'\n') + 1
        end_line = raw[:end].count(b'\n')
        entry = idx['entries'][j]
        assert (entry['name'], entry['kind'], entry['startLine'], entry['endLine']) == (name, kind, start_line, end_line)
        assert entry['hasActualType'] and not entry['hasFullValue']
        coverage.append({'name': name, 'kind': kind, 'owner': expected['owner'],
                         'axioms': axioms, 'recursiveAxiomsWhitelistPass': True,
                         'fullBlockLineRange': [start_line, end_line],
                         'fullBlockByteRangeHalfOpen': [m.start(), end],
                         'fullBlockBytes': len(block), 'fullBlockSHA256': SHA(block),
                         'fullTypeByteRangeHalfOpen': [type_start, end],
                         'fullTypeBytes': end - type_start, 'fullTypeSHA256': SHA(raw[type_start:end]),
                         'allBinderLetInstanceConclusionRead': True,
                         'completeActualTypeRead': True, 'requiredNonTheoremValue': False})
        names.append(name)
    owner_names = [x['name'] for x in owner['module_owned_constants']]
    assert len(names) == len(set(names)) == len(owner_names) and set(names) == set(owner_names)
    counts = {'actualOwnedCount': len(owner_names),
              'actualTheoremCount': sum(x['kind'] == 'theorem' for x in owner['module_owned_constants']),
              'actualNonTheoremValueCount': sum(x['kind'] != 'theorem' for x in owner['module_owned_constants']),
              'actualPublicCount': sum(x['name'].split('.')[-1] in re.findall(r'^theorem (\w+)', text, re.M) for x in owner['module_owned_constants'])}
    assert counts['actualNonTheoremValueCount'] == 0
    assert counts['actualOwnedCount'] == owner['target_constant_count'] == idx['typeCount']
    assert counts['actualTheoremCount'] == owner['target_theorem_count']
    assert counts['actualPublicCount'] == owner['public_theorem_count'] == 1
    assert idx['fullValueCount'] == owner['target_definition_count_including_private_generated'] == 0
    extraction = response(native + '/audit001-type-value-extraction-response.json')
    curated = []
    for row in extraction['rows']:
        curated.append(check_binding({'path': receipt_dir + '/' + row['file'], 'bytes': row['bytes'], 'sha256': row['sha256']}))
    get_intent = load(native + '/audit001-curated-receipts-get-intent.json')
    assert len(curated) == load(native + '/audit001-curated-receipts-get-response.json')['transferred'] == 9
    assert {Path(x['path']).name for x in curated} == {Path(x['local']).name for x in get_intent['files']}
    assert extraction['typeCount'] == len(names) and extraction['fullValueCount'] == 0
    kernel_name = 'kernel%03d' % u['nativeAttempt']
    kernel = load(receipt_dir + '/' + kernel_name + '-result.json')
    audit = load(receipt_dir + '/audit001-result.json')
    alias = response(native + '/audit001-input-object-binding-response.json')
    assert kernel['naturalRC'] == audit['naturalRC'] == 0
    for r in (kernel, audit):
        assert r['sourceSHA256Before'] == r['sourceSHA256After'] == u['source']['sha256']
        assert r['errorHeaderCount'] == 0 and not r['errorHeaders']
        assert r['userComputeRangeOK'] and r['peakAggregateMemoryGiB'] < 180
    obj_sha = kernel['objectSHA256']
    assert kernel['objectBytes'] == audit['objectBytes'] == alias['originalObjectBytes']
    assert obj_sha == audit['objectSHA256'] == alias['aliasSHA256'] == alias['originalSuccessfulObjectSHA256'] == idx['objectSHA256']
    assert alias['sourceSHA256'] == idx['sourceSHA256'] == u['source']['sha256']
    audit_source = source_path.split('/source004/')[0] + '/native-preparation001/OwnedAudit.lean'
    assert alias['auditSHA256'] == binding(audit_source)['sha256']
    assert alias['aliasPreviouslyAbsent'] and alias['noUncertainAuditPriorEffects'] and alias['sharedPackageCacheWrites'] == 0
    assert audit['AX'] == 'PASS_ALL_ACTUAL_OWNERS_TRANSITIVE'
    assert audit['ownedReportSHA256'] == binding(receipt_dir + '/owned-audit.json')['sha256']
    assert extraction['rawLogSHA256'] == audit['logSHA256']
    guard = response(native + '/prior-failed-source-guard-response.json')
    assert guard['oldSourceExact'] and guard['previousRC'] == 1 and guard['noObjectNoAX'] and guard['phase'] == 35
    resources = []
    for name in (kernel_name, 'audit001'):
        result = load(receipt_dir + '/' + name + '-result.json')
        start = load(receipt_dir + '/' + name + '-start.json')
        dispatch = load(native + '/' + name + '-dispatch-intent.json')
        assert response(native + '/' + name + '-dispatch-response.json') == result
        assert start['phaseSHA256'] == phase_sha and start['CPU'] == [44, 45, 46, 47]
        assert start['sourceSHA256'] == u['source']['sha256'] and start['sourceBytes'] == len(src)
        assert start['command'][:5] == ['lake', 'env', 'lean', '-M8192', '-j4']
        assert 'taskset -c 44-47 flock -x /root/rivermind-data/shao-lean-20261021/locks/c12-heavy.lock' in dispatch['command']
        assert 'leanprover/lean4:v4.36.0-rc1' in dispatch['stdin'] and phase_sha in dispatch['stdin']
        ts = load(receipt_dir + '/' + name + '-threads.json')
        users = [x for x in ts if x['kind'] == 'userCompute']
        helpers = [x for x in ts if x['kind'] == 'kernelSQhelper']
        assert len(users) == result['userThreadsObserved'] and users
        assert all(set(x['affinity']) <= {44, 45, 46, 47} and x['userRangeOK'] for x in users)
        assert all(x['comm'].startswith('iou-sqp-') and x['firstTicks'] == x['lastTicks'] == 0 for x in helpers)
        assert helpers == result['kernelSQhelpers']
        assert result['startUTC'] == start['atUTC']
        all_intervals.append([start['atUTC'], result['atUTC']])
        resources.append({'receipt': name, 'startUTC': start['atUTC'], 'endUTC': result['atUTC'],
                          'phaseSHA256': phase_sha, 'CPU': start['CPU'], 'lock': start['flock'],
                          'actualCommand': start['command'], 'userThreadCount': len(users),
                          'allUserAffinitiesWithin44to47': True, 'kernelSQHelperCount': len(helpers),
                          'allKernelSQZeroTicks': True, 'peakObservedAggregateMemoryGiB': result['peakAggregateMemoryGiB'],
                          'peakObservedTargetRSSKiB': result['peakObservedRSSKiB'],
                          'originalLogSHA256': result['logSHA256'], 'originalLogBytes': result['logBytes'],
                          'rawLogDownloadedOrClaimedReadByReviewer': False})
    unit_data.append({'unit': number, 'version': 'source004', 'source': source_record,
                      'actualTypeText': {**binding(type_path), 'fullLF': raw.count(b'\n'), 'completeRead': True,
                                         'truncationMarkerCount': 0},
                      'allActualOwnerTypeCoverage': coverage, 'countsDerivedFromActualOwnerMap': counts,
                      'ownerMap': binding(receipt_dir + '/owned-audit.json'),
                      'index': binding(receipt_dir + '/actual-types-values-index.json'),
                      'nativeReceipt': binding(receipt_dir + '/' + kernel_name + '-result.json'),
                      'sameOriginalObjectAuditReceipt': binding(receipt_dir + '/audit001-result.json'),
                      'auditSource': binding(audit_source),
                      'sameFirstOriginalObjectSHA256': obj_sha, 'sameFirstOriginalObjectBytes': kernel['objectBytes'],
                      'kernelAndAuditRC': [0, 0], 'allOwnerRecursiveAxiomWhitelist': True,
                      'fullNonTheoremValues': [], 'emptyValuesDerivedFromActualMap': True,
                      'curatedReceiptBindings': curated, 'resources': resources,
                      'noUncertainReplay': True, 'failureGuard': guard})

s233root = 'drafts/c12-lane/original-growing-double-comparison-v1/'
s236root = 'drafts/c12-lane/original-moment-envelope-v1/'
old233 = read(s233root + 'source003/OriginalGrowingDoubleComparison.lean')
new233 = read(s233root + 'source004/OriginalGrowingDoubleComparison.lean')
old_line = b'add_le_add_right (mul_le_mul_of_nonneg_right hFour hPsi) _'
new_line = b'add_le_add (mul_le_mul_of_nonneg_right hFour hPsi) (le_refl _)'
assert old233.count(old_line) == 1 and old233.replace(old_line, new_line) == new233
old236 = read(s236root + 'source001/OriginalMomentEnvelope.lean')
s236002 = read(s236root + 'source002/OriginalMomentEnvelope.lean')
s236003 = read(s236root + 'source003/OriginalMomentEnvelope.lean')
s236004 = read(s236root + 'source004/OriginalMomentEnvelope.lean')
assert old236.replace(b'import Mathlib.Tactic\n', b'import Mathlib.Tactic.Linarith\nimport Mathlib.Tactic.NormNum\nimport Mathlib.Tactic.FieldSimp\nimport Mathlib.Tactic.Ring\n') == s236002
assert s236002.replace(b'Real.tendsto_rpow_neg_atTop', b'tendsto_rpow_neg_atTop') == s236003
changed236 = s236003
for before, after in [
    (b'simp only [Function.comp_apply, Real.rpow_neg', b'simp only [Real.rpow_eq_pow, Function.comp_apply, Real.rpow_neg'),
    (b'simpa only [mul_zero] using hPower', b'simpa only [Real.rpow_eq_pow, mul_zero] using hPower'),
    (b'((p - 2) / 2) := by\n    rw [\u2190 Real.rpow_mul'.decode('unicode_escape').encode('utf-8'), b'((p - 2) / 2) := by\n    simp only [Real.rpow_eq_pow]\n    rw [\u2190 Real.rpow_mul'.decode('unicode_escape').encode('utf-8')),
    (b'  rw [Real.div_rpow', '  simp only [Real.rpow_eq_pow] at hDenominator \u22a2\n  rw [Real.div_rpow'.encode('utf-8')),
]:
    assert changed236.count(before) == 1, before
    changed236 = changed236.replace(before, after)
assert changed236 == s236004

failures = []
for p in [s233root + 'native001/server-receipts/kernel001-result.json',
          s236root + 'native001/server-receipts/kernel001-result.json',
          s236root + 'native002/server-receipts/kernel002-result.json']:
    f = load(p)
    assert f['naturalRC'] == 1 and f['objectSHA256'] is None and f['AX'] == 'notrun'
    failures.append({'receipt': binding(p), 'naturalRC': 1, 'sourceSHA256': f['sourceSHA256Before'],
                     'errorHeaders': f['errorHeaders'], 'objectSHA256': None, 'AX': 'notrun'})
first233 = load(s233root + 'native001/server-receipts/kernel001-result.json')['startUTC']
assert datetime.datetime.fromisoformat(qualification['atUTC']) < datetime.datetime.fromisoformat(first233)
producer_binding = load(s233root + 'qualified-producer232002-binding002.json')
assert producer_binding['consumerSource'] == activation['units'][0]['source']
assert producer_binding['qualifiedProducerSource'] == {k: qualification['source'][k] for k in ('path','bytes','sha256')}
source232001 = read('drafts/c12-lane/actual-original-small-budget-double-v1/source001/ActualOriginalSmallBudgetDouble.lean')
source232002 = read(qualification['source']['path'])
assert source232001.split(b':= by\n', 1)[0] == source232002.split(b':= by\n', 1)[0]
intervals = sorted((datetime.datetime.fromisoformat(a), datetime.datetime.fromisoformat(b)) for a, b in all_intervals)
assert all(intervals[i][1] < intervals[i+1][0] for i in range(len(intervals)-1))
result = {'atUTC': NOW(), 'status': 'PASS_EXACT_SOURCE_ALL_NEW_TYPES_ALL_OWNERS_SAME_ORIGINAL_OBJECTS',
          'activation': binding(activation_path), 'mandatoryInputCount': len(mandatory), 'mandatoryAllPass': True,
          'ACKExistedBeforeAnalysis': True, 'units': unit_data, 'reusedReviewSeals': reuse_seals,
          'additionalDirectBindings': extra, 'priorQualified232DirectBindings': qualification_direct,
          'priorInterfaceFile': binding(interface_file), 'priorInterfaceParentBindings': interface_bindings,
          'exactChanges': {'233003to004OnlyCalcAddCongruence': True,
                           '236001to002OnlyTacticImports': True,
                           '236002to003OnlyNamespace': True,
                           '236003to004OnlyFourRpowEqPowNormalizations': True,
                           'bothFrozenHeadsAndFinalPreamblesUnchanged': True},
          'preservedFailures': failures,
          'producer232QualifiedBefore233FirstNative': {'qualificationUTC': qualification['atUTC'], 'first233NativeUTC': first233, 'pass': True},
          'source232001to002FrozenPreambleHeadSameBytes': True,
          'phase': {'binding': binding(phase_path), 'heavyAllowances': phase['heavyAllowances'], 'resourcePolicy': phase['resourcePolicy']},
          'allFourC12HeavyIntervalsSerial': True,
          'reviewerNewLeanAXServerNetworkUploadGitSourceWritesChildren': 0,
          'oldProducerProofRereviews': 0, 'oldProducerLeanAXReplays': 0,
          'configuredModel': 'gpt-6.1-sol', 'configuredEffort': 'xhigh',
          'actualModel': None, 'actualEffort': None,
          'usage': {'input': None, 'cachedInput': None, 'output': None, 'reasoningSubset': None},
          'C2C12': 'OPEN', 'fullRootOD': 'OPEN', 'OQ3': 'PAUSED_BY_USER'}
write_new('DETERMINISTIC-CHECK.json', result)
print(json.dumps({'status': result['status'], 'mandatory': len(mandatory),
                  'unitCounts': [{**x['countsDerivedFromActualOwnerMap'], 'unit': x['unit']} for x in unit_data],
                  'oldSealPayloadCounts': [x['payloadCount'] for x in reuse_seals],
                  'preservedNativeFailures': len(failures), 'allFourHeavyIntervalsSerial': True}, ensure_ascii=False))
