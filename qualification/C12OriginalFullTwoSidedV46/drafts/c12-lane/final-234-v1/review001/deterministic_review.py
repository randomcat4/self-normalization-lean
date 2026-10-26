"""Local read-only evidence verification for the independent 234 final review."""
from pathlib import Path
import datetime as dt
import difflib
import hashlib
import json
import re

ROOT = Path('C:/game/shao lean')
OUT = ROOT / 'drafts/c12-lane/final-234-v1/review001'
BASE = ROOT / 'drafts/c12-lane/original-growing-absolute-comparison-v1'
NOW = lambda: dt.datetime.now(dt.timezone.utc).isoformat()
SHA = lambda b: hashlib.sha256(b).hexdigest()
J = lambda p: json.loads(Path(p).read_text(encoding='utf-8'))

def resolve(p):
    p = Path(p)
    return p if p.is_absolute() else ROOT / p

def meta(p):
    p = resolve(p)
    b = p.read_bytes()
    try:
        name = p.relative_to(ROOT).as_posix()
    except ValueError:
        name = p.as_posix()
    return dict(path=name, bytes=len(b), sha256=SHA(b))

def verify(ref):
    got = meta(ref['path'])
    assert (got['bytes'], got['sha256']) == (ref['bytes'], ref['sha256']), ref['path']
    return got

def refs_in(x):
    found = []
    if isinstance(x, dict):
        if all(k in x for k in ('path', 'bytes', 'sha256')):
            found.append(verify(x))
        for v in x.values():
            found.extend(refs_in(v))
    elif isinstance(x, list):
        for v in x:
            found.extend(refs_in(v))
    return found

def timestamp(x):
    return dt.datetime.fromisoformat(x)

activation = J(OUT / 'parent-activation001.json')
assert meta(OUT / 'parent-activation001.json')['sha256'] == 'af60bfb1a3143ee00f7e8102af95032dddd4b9aa42a2243405c8380b627599c0'
mandatory = [verify(x) for x in activation['mandatoryInputs']]
assert len(mandatory) == 51
ack = J(OUT / 'ACTUAL-ACK.json')
assert ack['allMandatoryVerified'] and ack['mandatoryCount'] == 51

source_path = BASE / 'source002/OriginalGrowingAbsoluteComparison.lean'
old_path = BASE / 'source001/OriginalGrowingAbsoluteComparison.lean'
source = source_path.read_bytes()
old = old_path.read_bytes()
source.decode('utf-8', errors='strict')
assert len(source) == 10479 and source.count(b'\n') == 194
assert not source.startswith(b'\xef\xbb\xbf') and b'\r' not in source
assert SHA(source) == activation['currentSource']['sha256']
head_start = source.index(b'theorem ')
marker = source.index(b' := by\n', head_start)
head = source[head_start:marker] + b'\n'
preamble = source[:head_start]
assert preamble == (BASE / 'frozen-preamble001.lean.txt').read_bytes()
assert head == (BASE / 'public1-frozen-head.lean.txt').read_bytes()
by_start = marker + len(b' := ')
body_end = source.rindex(b'\nend Shao.C2.OriginalGrowingAbsoluteComparison')
proof = source[by_start:body_end].rstrip(b'\n') + b'\n'
proof_end = by_start + len(proof)
assert len(proof) == 6920
assert SHA(proof) == 'ad089af1e910a3ea9c75dc63974c06e60b91becb9a9d8d013c01d5fdd210d5b3'
old_site = b'simpa only [neg_one_smul, Shao.lowerMax] using hMinus.'
new_site = b'simpa only [L, population, rawEnergy, neg_one_smul, Shao.lowerMax] using hMinus.'
assert old.count(old_site) == 2 and source == old.replace(old_site, new_site)
diff = ''.join(difflib.unified_diff(old.decode().splitlines(True), source.decode().splitlines(True), fromfile='source001', tofile='source002'))
assert diff.encode() == (BASE / 'source002/exact-let-unfold-diff001.txt').read_bytes()
forbidden = re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', source.decode())
assert not forbidden
proof_meta = dict(byteRangeHalfOpen=[by_start, proof_end], bytes=len(proof), sha256=SHA(proof),
                  literalByLine=source[:by_start].count(b'\n') + 1,
                  bodyStartLine=source[:by_start].count(b'\n') + 2,
                  bodyEndLine=source[:proof_end].count(b'\n'), completeRead=True)

receipts = BASE / 'native002/server-receipts'
audit = J(receipts / 'owned-audit.json')
index = J(receipts / 'actual-types-values-index.json')
types = (receipts / 'actual-types-values.txt').read_bytes()
types.decode('utf-8', errors='strict')
assert len(types) == 43414 and types.count(b'\n') == 520
assert b'\r' not in types and not types.startswith(b'\xef\xbb\xbf')
markers = {x: types.decode().count(x) for x in ['⋯', '…', '[truncated]', '<truncated>']}
assert not any(markers.values())
matches = list(re.finditer(rb'(?m)^TARGET_DECL (\S+) KIND (theorem|definition) AXIOMS \[([^]]*)\]', types))
assert len(matches) == len(audit['module_owned_constants']) == len(index['entries']) == 8
owner_rows = {x['name']: x for x in audit['module_owned_constants']}
index_rows = {x['name']: x for x in index['entries']}
assert len(owner_rows) == len(index_rows) == 8
assert set(owner_rows) == set(index_rows) == {m[1].decode() for m in matches}
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
actual = []
public = 'Shao.C2.OriginalGrowingAbsoluteComparison.original_iid_growing_double_and_absolute_comparison'
for i, m in enumerate(matches):
    end = matches[i+1].start() if i+1 < len(matches) else len(types)
    block = types[m.start():end]
    name = m[1].decode()
    kind = m[2].decode()
    axes = re.findall(r'[A-Za-z][A-Za-z.]*', m[3].decode())
    row = owner_rows[name]
    ix = index_rows[name]
    assert row['owner'] == audit['target_module'] == 'Shao.C2.OriginalGrowingAbsoluteComparison'
    assert row['kind'] == ix['kind'] == kind == 'theorem'
    assert set(axes) == set(row['axioms']) <= allowed
    start_line = types[:m.start()].count(b'\n') + 1
    end_line = types[:end].count(b'\n')
    assert (ix['startLine'], ix['endLine']) == (start_line, end_line)
    assert block.count(b'ACTUAL_TYPE ') == 1 and b'DEFINITION_VALUE ' not in block
    assert ix['hasActualType'] and not ix['hasFullValue']
    type_start = m.start() + block.index(b'ACTUAL_TYPE ') + len(b'ACTUAL_TYPE ')
    type_bytes = types[type_start:end]
    actual.append(dict(name=name, kind=kind, public=name == public, generated=name != public,
                       declarationLines=[start_line, end_line], declarationBytes=len(block), declarationSHA256=SHA(block),
                       typeByteRangeHalfOpen=[type_start, end], typeBytes=len(type_bytes), typeSHA256=SHA(type_bytes),
                       completeTypeRead=True, everyBinderLetInstanceConclusionRead=True,
                       nonTheoremFullValueRequired=False, axioms=axes))
assert len(actual) == index['typeCount'] == audit['target_constant_count'] == audit['target_theorem_count'] == 8
assert sum(x['public'] for x in actual) == audit['public_theorem_count'] == 1
assert index['fullValueCount'] == audit['target_definition_count_including_private_generated'] == 0
owned_source = (BASE / 'native-preparation001/OwnedAudit.lean').read_text(encoding='utf-8')
for needle in ['env.constants.toList', 'env.getModuleIdxFor? name', 'owner == target', 'Lean.collectAxioms name', 'DEFINITION_VALUE', 'Owned non-theorem kind requires explicit complete value audit']:
    assert needle in owned_source
assert not re.search(r'hasPrefix|isPrefixOf|startsWith', owned_source)

native = J(receipts / 'kernel002-result.json')
audited = J(receipts / 'audit001-result.json')
first_object = 'fb3563a8c7a81220e4cdf6e259e5a40054c5c43a03ed0703ed9f9f178073563a'
resource = []
for stage, result in [('kernel002', native), ('audit001', audited)]:
    start = J(receipts / f'{stage}-start.json')
    threads = J(receipts / f'{stage}-threads.json')
    intent = J(BASE / 'native002' / f'{stage}-dispatch-intent.json')
    response = J(BASE / 'native002' / f'{stage}-dispatch-response.json')
    assert response['exit_code'] == 0 and json.loads(response['stdout']) == result
    assert result['naturalRC'] == 0 and result['errorHeaderCount'] == 0
    assert result['sourceSHA256Before'] == result['sourceSHA256After'] == SHA(source)
    assert result['objectSHA256'] == first_object and result['objectBytes'] == 576688
    assert start['sourceSHA256'] == SHA(source) and start['sourceBytes'] == len(source)
    assert start['CPU'] == [44,45,46,47] and start['phaseSHA256'] == '9ef3396f9862e945f006aec1185c6235757383ccec0b8e8906163f7b41561994'
    assert '-M8192' in start['command'] and '-j4' in start['command']
    assert 'c12-heavy.lock' in start['flock'] and 'taskset -c 44-47 flock -x' in intent['command']
    assert "leanprover/lean4:v4.36.0-rc1" in intent['stdin']
    assert result['userComputeRangeOK'] and result['peakAggregateMemoryGiB'] < 180
    users = [x for x in threads if x['kind'] == 'userCompute']
    helpers = [x for x in threads if x['kind'] == 'kernelSQhelper']
    assert len(users) == result['userThreadsObserved'] == 3
    assert all(set(x['affinity']) <= {44,45,46,47} and x['userRangeOK'] for x in users)
    assert len(helpers) == 1 and all(x['comm'].startswith('iou-sqp-') and x['firstTicks'] == x['lastTicks'] == 0 for x in helpers)
    assert helpers == result['kernelSQhelpers']
    resource.append(dict(stage=stage, startUTC=start['atUTC'], endUTC=result['atUTC'], naturalRC=result['naturalRC'],
                         sourceBeforeAfterExact=True, originalObjectSHA256=first_object, originalObjectBytes=576688,
                         CPU=start['CPU'], command=start['command'], flock=start['flock'], phaseSHA256=start['phaseSHA256'],
                         userThreads=len(users), userComputeRangeOK=True,
                         kernelSQHelpers=[dict(tid=x['tid'], comm=x['comm'], firstTicks=x['firstTicks'], lastTicks=x['lastTicks'],
                                               affinityMin=min(x['affinity']), affinityMax=max(x['affinity']), classification='ZERO_TICK_KERNEL_IO_HELPER') for x in helpers],
                         peakObservedAggregateMemoryGiB=result['peakAggregateMemoryGiB'], peakObservedRSSKiB=result['peakObservedRSSKiB']))
assert timestamp(native['atUTC']) < timestamp(audited['startUTC'])
assert audited['ownedReportSHA256'] == meta(receipts / 'owned-audit.json')['sha256']
assert audited['AX'] == 'PASS_ALL_ACTUAL_OWNERS_TRANSITIVE'
assert index['sourceSHA256'] == SHA(source) and index['objectSHA256'] == first_object
alias_response = J(BASE / 'native002/audit001-input-object-binding-response.json')
alias = json.loads(alias_response['stdout'])
assert alias_response['exit_code'] == 0 and alias['aliasPreviouslyAbsent'] and alias['noUncertainAuditPriorEffects']
assert alias['sourceSHA256'] == SHA(source)
assert alias['originalSuccessfulObjectSHA256'] == alias['aliasSHA256'] == first_object
assert alias['auditSHA256'] == meta(BASE / 'native-preparation001/OwnedAudit.lean')['sha256']
assert alias['originalObjectBytes'] == 576688 and alias['sharedPackageCacheWrites'] == alias['LeanAX'] == 0

extract_response = J(BASE / 'native002/audit001-type-value-extraction-response.json')
extract = json.loads(extract_response['stdout'])
assert extract_response['exit_code'] == 0 and extract['AX'] == 'PASS'
assert extract['rawLogSHA256'] == audited['logSHA256']
assert extract['typeCount'] == 8 and extract['fullValueCount'] == 0
curated = []
for row in extract['rows']:
    ref = dict(path=str(receipts / row['file']), bytes=row['bytes'], sha256=row['sha256'])
    curated.append(verify(ref))
get_intent = J(BASE / 'native002/audit001-curated-receipts-get-intent.json')
get_response = J(BASE / 'native002/audit001-curated-receipts-get-response.json')
assert get_response['transferred'] == len(curated) == 9
assert {Path(x['local']).name for x in get_intent['files']} == {Path(x['path']).name for x in curated}

failure = J(BASE / 'native001/server-receipts/kernel001-result.json')
assert failure['naturalRC'] == 1 and failure['objectSHA256'] is None and failure['objectBytes'] is None
assert failure['sourceSHA256Before'] == failure['sourceSHA256After'] == SHA(old) and failure['AX'] == 'notrun'
assert failure['errorHeaderCount'] == 2 and all(any(f':{n}:4:' in x for x in failure['errorHeaders']) for n in [95,101])
guard_response = J(BASE / 'native002/prior-failure-guard-response.json')
guard = json.loads(guard_response['stdout'])
assert guard_response['exit_code'] == 0 and guard == dict(priorFailureSourceExact=True, noObjectNoAX=True, phase=35)

qualification_path = ROOT / 'drafts/c12-lane/original-growing-double-comparison-v1/parent-final-qualification001.json'
qualification = J(qualification_path)
assert qualification['formalQualified'] and qualification['unit'] == 233
qualification_refs = refs_in(qualification)
assert timestamp(qualification['atUTC']) < timestamp(failure['startUTC'])
binding = J(BASE / 'qualified-producer233004-binding002.json')
binding_refs = refs_in(binding)
assert binding['consumerSource']['sha256'] == SHA(source)
assert binding['formalQualification']['sha256'] == meta(qualification_path)['sha256']
assert timestamp(binding['atUTC']) < timestamp(native['startUTC'])
producer = resolve(binding['qualifiedProducerSource']['path']).read_bytes()
producer_start = producer.index(b'theorem ')
producer_end = producer.index(b' := by\n', producer_start)
producer_frozen_path = ROOT / 'drafts/c12-lane/original-growing-double-comparison-v1/public1-frozen-head.lean.txt'
assert producer[producer_start:producer_end] + b'\n' == producer_frozen_path.read_bytes()

old_seals = []
old_refs = []
for dirname in ['source-batch-230repair234-v1', 'final-233236-v1']:
    directory = ROOT / 'drafts/c12-lane' / dirname / 'review001'
    seal = J(directory / 'PAYLOAD-SEAL.json')
    entries = [verify(x) for x in seal['payloads']]
    assert len(entries) == seal.get('payloadCount', seal.get('count'))
    release = J(directory / 'RELEASE.json')
    assert len(release['runtime']) == 16 and all(x == 0 for x in release['runtime'].values())
    old_seals.append(dict(seal=meta(directory / 'PAYLOAD-SEAL.json'), payloadCount=len(entries), allPayloadsMatch=True,
                          release=meta(directory / 'RELEASE.json'), releaseRuntimeCount=16, releaseAllZero=True))
    old_refs.extend(entries)

old_coverage = J(ROOT / 'drafts/c12-lane/source-batch-230repair234-v1/review001/COVERAGE.json')
interfaces = []
for entry in old_coverage['usedProducerInterfaces']:
    if entry.get('unit') in [221,222,227,228,229,233]:
        continue
    if 'file' not in entry:
        continue
    file_meta = verify(entry['file'])
    block_key = 'sourceBlock' if 'sourceBlock' in entry else 'typeBlock' if 'typeBlock' in entry else None
    block_meta = None
    if block_key:
        b = resolve(entry['file']['path']).read_bytes()
        lines = b.splitlines(keepends=True)
        span = entry[block_key]
        block = b''.join(lines[span['startLine']-1:span['endLine']])
        assert (len(block), SHA(block)) == (span['bytes'], span['sha256'])
        block_meta = dict(startLine=span['startLine'], endLine=span['endLine'], bytes=len(block), sha256=SHA(block))
    if entry.get('jsonSelector'):
        data = J(resolve(entry['file']['path']))
        declarations = data['declarations']
        if isinstance(declarations, list):
            declaration = next(x for x in declarations if x['name'] == entry['declaration'])
        else:
            declaration = declarations[entry['declaration']]
        b = declaration['type'].encode()
        expected = entry['extractedType']
        assert (len(b), SHA(b)) == (expected['bytes'], expected['sha256'])
        block_meta = dict(bytes=len(b), sha256=SHA(b), lines=expected['lines'])
    interfaces.append(dict(interface=entry.get('interface', entry.get('declaration')), file=file_meta,
                           completeQualifiedCoverageReused=True, block=block_meta,
                           newOldProofRereview=False, newOldLargeTypeRereview=False))
    if 'reusedProofQualification' in entry:
        old_refs.append(verify(entry['reusedProofQualification']))

extra_paths = [
    'drafts/c12-lane/original-growing-double-comparison-v1/qualified-original-producer-complete-public-heads.txt',
    'library/Shao/Probability/TruncationIntegrals.lean',
    'library/Shao/Probability/GaussianTail.lean',
    'library/Shao/Probability/MeasurablePath.lean',
    'library/Shao/Probability/FiniteIID.lean',
    'library/Shao/Basic/Events.lean',
    'C:/game/shao/current/c12/main.tex',
]
extra = [meta(x) for x in extra_paths]
assert extra[0]['bytes'] == 4206 and extra[0]['sha256'] == '87e83e29f55a93cdc5e0d3367b2e06920733ba2ee2dc7dda10955c604746ff9a'
assert extra[-1]['sha256'] == 'beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06'

result = dict(atUTC=NOW(), role='c12_final_234_review001', status='PASS_LOCAL_DETERMINISTIC_EVIDENCE_CHECK',
              mandatoryInputsVerified=51, activation=meta(OUT / 'parent-activation001.json'),
              exactSource=meta(source_path), sourceFormat=dict(strictUTF8=True, LF=194, BOM=False, CRCount=0),
              exactPreamble=dict(bytes=len(preamble), sha256=SHA(preamble), frozenExact=True),
              exactPublicHead=dict(bytes=len(head), sha256=SHA(head), frozenExact=True), wholeProof=proof_meta,
              sourceDelta=dict(exactOnlyTwoLetUnfoldSites=True, mathUnchanged=True, diffExact=True,
                               diff=meta(BASE / 'source002/exact-let-unfold-diff001.txt')), forbiddenConstructs=forbidden,
              actualTypesFile=meta(receipts / 'actual-types-values.txt'), actualTypeLF=520,
              actualOwnedCount=8, actualTheoremCount=8, actualPublicCount=1, actualGeneratedCount=7,
              actualNonTheoremFullValueCount=0, actualTypes=actual, truncationMarkers=markers,
              actualOwnerSelection=dict(getModuleIdxForRealOwner=True, enumeratesAllConstants=True,
                                        prefixFilter=False, collectAxiomsTransitive=True, allNonTheoremFullValuesRequired=True),
              allowedAxioms=sorted(allowed), resourceReceipts=resource, nativeAuditSerial=True,
              sameFirstSuccessfulObjectAlias=alias, curatedReceipts=curated, curatedCount=9,
              dispatchResultsEqualSavedResults=True, extractionRawLogHashMatches=True,
              failedNativePreserved=dict(source=meta(old_path), receipt=meta(BASE / 'native001/server-receipts/kernel001-result.json'),
                                        naturalRC=1, errorLines=[95,101], noObject=True, noAX=True, exactFailureGuard=guard),
              qualified233=meta(qualification_path), qualified233DirectRefsVerified=qualification_refs,
              qualified233Before234FirstNative=dict(qualificationUTC=qualification['atUTC'], firstNativeUTC=failure['startUTC'], passOrder=True),
              consumerBinding=meta(BASE / 'qualified-producer233004-binding002.json'), bindingRefsVerified=binding_refs,
              producerHeadExact=True, reusedOldPayloadSeals=old_seals, oldReferencedPayloadsVerified=old_refs,
              reusedCompleteInterfaces=interfaces, supplementalInputs=extra,
              localReadCorrection='Optional original-source read first used nonexistent workspace/current path, then read correct C:/game/shao/current path; no input mutation and no Lean/server execution.',
              noOldProducerProofOrLargeTypeRereview=True, noOldProducerLeanAXReplay=True,
              reviewerLeanAXServerNetworkGitUploadSourceWritesChildren=0,
              configuredModel='gpt-6.1-sol', configuredEffort='xhigh', actualModel=None, actualEffort=None,
              usage=dict(input=None, cachedInput=None, output=None, reasoningSubset=None),
              C2C12='OPEN', fullRootOD='OPEN', OQ3='PAUSED_BY_USER')
target = OUT / 'DETERMINISTIC-CHECK.json'
assert not target.exists(), 'Do not overwrite review check output'
target.write_bytes((json.dumps(result, ensure_ascii=False, indent=2) + '\n').encode('utf-8'))
print(json.dumps(dict(status=result['status'], mandatory=51, sourceLF=194, proof=proof_meta,
                      actualOwner=8, actualTypeLF=520, curated=9,
                      oldPayloadCounts=[x['payloadCount'] for x in old_seals],
                      qualified233BeforeFirstNative=True, sameFirstObject=True,
                      resources=[dict(stage=x['stage'], userThreads=x['userThreads'], memoryGiB=x['peakObservedAggregateMemoryGiB']) for x in resource])), flush=True)
