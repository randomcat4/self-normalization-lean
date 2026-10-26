"""Offline, read-only input validation for the independent machine supplement.

Writes only this review directory. Never invokes Lean, a server, or network.
"""
import hashlib
import json
import re
from pathlib import Path
from datetime import datetime, timezone

ROOT = Path('C:/game/shao lean')
OUT = ROOT / 'drafts/c12-lane/final-machine-batch-223228-v1/review001'
OLD = ROOT / 'drafts/c12-lane/source-machine-batch-223227228-v1/review001'
ROWS = []
READS = {}


def digest(b):
    return hashlib.sha256(b).hexdigest()


def pathof(p):
    p = Path(p)
    return p if p.is_absolute() else ROOT / p


def read(p):
    p = pathof(p)
    b = p.read_bytes()
    READS[p.as_posix()] = dict(path=p.as_posix(), bytes=len(b), sha256=digest(b))
    return b


def load(p):
    return json.loads(read(p).decode('utf-8-sig'))


def binding(row, origin):
    p = pathof(row['path'])
    if not p.is_file():
        result = dict(path=p.as_posix(), origin=origin, exists=False, verified=False,
                      expectedBytes=row.get('bytes'), expectedSHA256=row['sha256'])
    else:
        b = read(p)
        result = dict(path=p.as_posix(), origin=origin, bytes=len(b), sha256=digest(b),
                      expectedBytes=row.get('bytes'), expectedSHA256=row['sha256'],
                      verified=digest(b) == row['sha256'] and
                      (row.get('bytes') is None or len(b) == row['bytes']))
    ROWS.append(result)
    return result


def walk_bindings(obj, origin):
    if isinstance(obj, dict):
        if isinstance(obj.get('path'), str) and isinstance(obj.get('sha256'), str):
            p = obj['path']
            if p.startswith('C:/') or p.startswith('C:\\') or not p.startswith('/'):
                binding(obj, origin)
        for key, val in obj.items():
            walk_bindings(val, origin + '/' + key)
    elif isinstance(obj, list):
        for i, val in enumerate(obj):
            walk_bindings(val, origin + '/' + str(i))


def write(name, obj):
    (OUT / name).write_text(json.dumps(obj, ensure_ascii=False, indent=2) + '\n',
                            encoding='utf-8', newline='\n')


def response(p):
    data = load(p)
    assert data['exit_code'] == 0 and data['stderr'] == ''
    return json.loads(data['stdout'])


def machine_unit(unit, base, native, kernel, expected_source, expected_object, object_bytes):
    base = ROOT / 'drafts/c12-lane' / base
    receipts = base / native / 'server-receipts'
    cov = next(x for x in load(OLD / 'COVERAGE.json')['units'] if x['unit'] == unit)
    b = read(cov['source']['path'])
    assert digest(b) == expected_source and len(b) == cov['source']['bytes']
    text = b.decode('utf-8')
    assert not b.startswith(b'\xef\xbb\xbf') and b'\r' not in b
    assert b.count(b'\n') == cov['sourceLines']
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', text)
    lines = text.splitlines(keepends=True)
    freeze = load(base / 'parent-exact-declaration-freeze001.json')
    heads = []
    for i, frozen in enumerate(freeze['frozen']):
        fb = read(frozen['path'])
        assert len(fb) == frozen['bytes'] and digest(fb) == frozen['sha256']
        if i == 0:
            assert b.startswith(fb)
        else:
            proof = cov['proofs'][i - 1]
            head = ''.join(lines[proof['headStartLine']-1:proof['bodyStartLine']-1])
            assert head.endswith(' := by\n')
            assert (head[:-len(' := by\n')] + '\n').encode() == fb
        heads.append(dict(**frozen, byteExact=True))
    proofs = []
    for p in cov['proofs']:
        pb = ('by\n' + ''.join(lines[p['bodyStartLine']-1:p['bodyEndLine']])).encode()
        assert len(pb) == p['bytes'] and digest(pb) == p['sha256']
        proofs.append(dict(**p, exactQualifiedCompleteProofReuse=True,
                           newCompleteProofReview=False))
    covered = [n for seg in cov['segments'] for n in range(seg['lines'][0], seg['lines'][1]+1)]
    assert covered == list(range(1, len(lines)+1))
    assert cov['criticalGaps'] == [] and cov['completeSourceRead']
    assert cov['status'] == 'CORRECT_SOURCE_ONLY'
    assert not cov['formalQualified']
    prep = load(base / 'native-preparation001/PREPARATION.json')
    audit_source = read(base / 'native-preparation001/OwnedAudit.lean')
    assert prep['auditSHA256'] == digest(audit_source) and prep['auditBytes'] == len(audit_source)
    assert prep['sourceSHA256'] == expected_source
    assert prep['successfulOriginalObjectSHA256'] == expected_object
    assert prep['nativePhase'] == 29 and not prep['sourceChanged']
    audit_text = audit_source.decode()
    assert 'env.getModuleIdxFor? name' in audit_text
    assert 'if owner == target then' in audit_text
    assert 'Lean.collectAxioms name' in audit_text
    assert 'ACTUAL_TYPE {info.type}' in audit_text
    assert 'VALUE {value.value}' in audit_text
    assert 'set_option pp.all true' in audit_text
    assert 'requires explicit complete value audit' in audit_text
    assert not any(x in audit_text for x in ['startsWith', 'isPrefixOf', 'filterPrefix'])
    owner = load(receipts / 'owned-audit.json')
    assert owner['status'] == 'PASS' and owner['target_module'] == prep['target']
    owned = owner['module_owned_constants']
    names = [x['name'] for x in owned]
    assert len(names) == len(set(names)) == owner['target_constant_count']
    assert set(prep['allPublicNames']) <= set(names)
    assert sum(x['kind'] == 'theorem' for x in owned) == owner['target_theorem_count']
    assert sum(x['kind'] == 'definition' for x in owned) == owner['target_definition_count_including_private_generated']
    assert len(prep['allPublicNames']) == owner['public_theorem_count']
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    assert set(owner['allowed_axioms']) == allowed
    for x in owned:
        assert x['owner'] == prep['target']
        assert x['kind'] in ['theorem', 'definition']
        assert set(x['axioms']) <= allowed
    idx = load(receipts / 'actual-types-values-index.json')
    tb = read(receipts / 'actual-types-values.txt')
    tt = tb.decode('utf-8')
    tl = tt.splitlines(keepends=True)
    assert idx['sourceSHA256'] == expected_source and idx['objectSHA256'] == expected_object
    assert len(idx['entries']) == idx['typeCount'] == len(owned)
    assert set(x['name'] for x in idx['entries']) == set(names)
    assert not any(tt.count(m) for m in ['⋯', '…', '[truncated]', '<truncated>'])
    assert not any(idx['truncationMarkers'].values())
    all_ranges = []
    types = []
    for ent in idx['entries']:
        a, z = ent['startLine'], ent['endLine']
        all_ranges += list(range(a,z+1))
        block = ''.join(tl[a-1:z])
        row = next(x for x in owned if x['name'] == ent['name'])
        assert block.startswith('TARGET_DECL ' + ent['name'] + ' KIND ' + ent['kind'] + ' AXIOMS ')
        assert block.count('TARGET_DECL ') == 1 and block.count('ACTUAL_TYPE ') == 1
        assert ent['kind'] == row['kind'] and ent['hasActualType']
        parsed_axioms = re.search(r'AXIOMS \[([^\]]*)\]', block, re.S).group(1)
        assert [x.strip() for x in parsed_axioms.split(',') if x.strip()] == row['axioms']
        value = ent['kind'] == 'definition'
        assert ent['hasFullValue'] == value
        assert ('DEFINITION_VALUE ' in block) == value
        type_text = block.split('ACTUAL_TYPE ',1)[1]
        if value:
            type_text = type_text.split('DEFINITION_VALUE ',1)[0]
        types.append(dict(**ent, owner=row['owner'], recursiveAxioms=row['axioms'],
                          completeBlockBytes=len(block.encode()), completeBlockSHA256=digest(block.encode()),
                          actualTypeTextBytes=len(type_text.encode()), actualTypeTextSHA256=digest(type_text.encode()),
                          completeActualTypeIndependentlyRead=True, noTruncation=True))
    assert all_ranges == list(range(1,len(tl)+1))
    assert idx['fullValueCount'] == sum(x['kind'] != 'theorem' for x in owned) == 0
    extraction = response(base / native / 'audit001-type-value-extraction-response.json')
    assert extraction['typeCount'] == len(owned) and extraction['fullValueCount'] == 0
    assert extraction['AX'] == 'PASS' and extraction['c12LockFree']
    for row in extraction['rows']:
        binding(dict(path=(receipts / row['file']).as_posix(), bytes=row['bytes'],sha256=row['sha256']),
                f'{unit}-exact-server-extraction-row')
    obj_bind = response(base / native / 'audit001-input-object-binding-response.json')
    assert obj_bind['sourceSHA256'] == expected_source
    assert obj_bind['originalSuccessfulObjectSHA256'] == obj_bind['aliasSHA256'] == expected_object
    assert obj_bind['originalObjectBytes'] == object_bytes
    assert obj_bind['aliasPreviouslyAbsent'] and obj_bind['c12LockFree']
    assert obj_bind['noUncertainAuditPriorEffects'] and obj_bind['sharedPackageCacheWrites'] == 0
    assert obj_bind['auditSHA256'] == digest(audit_source) and obj_bind['LeanAX'] == 0
    resource = []
    for label in [kernel, 'audit001']:
        start = load(receipts / (label + '-start.json'))
        result = load(receipts / (label + '-result.json'))
        intent = load(base / native / (label + '-dispatch-intent.json'))['request']
        reply = response(base / native / (label + '-dispatch-response.json'))
        assert reply == result
        assert result['startUTC'] == start['atUTC']
        assert result['naturalRC'] == 0 and result['errorHeaderCount'] == 0 and result['errorHeaders'] == []
        assert start['sourceSHA256'] == result['sourceSHA256Before'] == result['sourceSHA256After'] == expected_source
        assert start['sourceBytes'] == len(b)
        assert result['objectSHA256'] == expected_object and result['objectBytes'] == object_bytes
        assert start['CPU'] == [44,45,46,47] and 'c12-heavy.lock' in start['flock']
        assert start['phaseSHA256'] == '15a60bf452294d96b79a9a9a1e7c9b77ddede4f1059c5cce4dcf3692ea47c813'
        assert start['command'][:5] == ['lake','env','lean','-M8192','-j4']
        assert 'taskset -c 44-47 flock -x /root/rivermind-data/shao-lean-20261021/locks/c12-heavy.lock' in intent['command']
        assert "leanprover/lean4:v4.36.0-rc1" in intent['stdin']
        assert expected_source in intent['stdin'] and start['phaseSHA256'] in intent['stdin']
        assert 'never replay uncertain' in intent['stdin']
        if label == kernel:
            assert start['command'][5] == '-o' and 'never overwrite uncertain existing object' in intent['stdin']
        else:
            assert '-o' not in start['command'] and expected_object in intent['stdin']
            assert result['AX'] == 'PASS_ALL_ACTUAL_OWNERS_TRANSITIVE'
            assert result['ownedReportSHA256'] == digest(read(receipts / 'owned-audit.json'))
            assert result['actualOwnedCount'] == len(owned)
            assert result['actualDefinitionCount'] == 0 and result['actualPublicCount'] == len(prep['allPublicNames'])
            assert extraction['rawLogSHA256'] == result['logSHA256']
        ts = load(receipts / result['threadRecordFile'])
        users = [x for x in ts if x['kind'] == 'userCompute']
        helpers = [x for x in ts if x['kind'] == 'kernelSQhelper']
        assert users and len(users) == result['userThreadsObserved']
        assert all(x['affinity'] == [44,45,46,47] and x['userRangeOK'] and
                   x['lastTicks'] >= x['firstTicks'] for x in users)
        assert result['userComputeRangeOK'] and helpers == result['kernelSQhelpers']
        assert len(helpers) == 1
        assert all(x['comm'].startswith('iou-sqp-') and x['firstTicks'] == x['lastTicks'] == 0
                   and x['affinity'] == list(range(256)) and any(u['Tgid'] == x['Tgid'] for u in users)
                   for x in helpers)
        assert start['memoryGiB'] < 180 and result['peakAggregateMemoryGiB'] < 180
        assert datetime.fromisoformat(result['atUTC']) > datetime.fromisoformat(start['atUTC'])
        resource.append(dict(receipt=label, startUTC=start['atUTC'], endUTC=result['atUTC'],naturalRC=0,
                             sourceBeforeAfterExact=True, sameOriginalObject=True,
                             objectSHA256=expected_object,objectBytes=object_bytes,
                             command=start['command'],phaseSHA256=start['phaseSHA256'],CPU=start['CPU'],
                             lock=start['flock'],actualUserThreads=users,
                             kernelHelpers=[dict(tid=x['tid'],comm=x['comm'],Tgid=x['Tgid'],firstTicks=0,lastTicks=0,
                                                 affinityCount=256,affinityExact0to255=True) for x in helpers],
                             peakAggregateMemoryGiB=result['peakAggregateMemoryGiB'],
                             peakObservedRSSKiB=result['peakObservedRSSKiB'],
                             logSHA256=result['logSHA256'],logBytes=result['logBytes'],
                             fullProject80GiBBudgetNotIndependentlyMeasuredBySingleTarget=True))
    assert datetime.fromisoformat(resource[0]['endUTC']) < datetime.fromisoformat(obj_bind['atUTC'])
    assert datetime.fromisoformat(obj_bind['atUTC']) < datetime.fromisoformat(resource[1]['startUTC'])
    own_source = {k:cov['source'][k] for k in ['path','bytes','sha256']}
    own_source['readScope'] = 'Exact source bytes/frozen heads/whole-proof hashes verified for qualified independent SOURCE-review reuse; no new proof review'
    return dict(unit=unit,source=own_source,sourceLines=len(lines),LF=b.count(b'\n'),CR=0,BOM=False,
                qualifiedCompleteSourceProofReuse=dict(report=(OLD/'REPORT.md').as_posix(),
                                                      reportSHA256=digest(read(OLD/'REPORT.md')),
                                                      coverage=(OLD/'COVERAGE.json').as_posix(),
                                                      coverageSHA256=digest(read(OLD/'COVERAGE.json')),
                                                      exactSource=True,priorReviewer='c12_source_machine_batch_223227228_review001',
                                                      thisReviewMode='EXACT_QUALIFIED_COMPLETE_SOURCE_TO_STATEMENT_AND_WHOLE_PROOF_REUSE',
                                                      priorQualifiedSegments=cov['segments'],proofs=proofs),
                frozen=heads,actualOwnerCounts=dict(all=len(owned),theorems=owner['target_theorem_count'],
                                                  public=owner['public_theorem_count'],nonTheorems=0,
                                                  actualTYPE=len(types),nonTheoremVALUE=0),
                actualTypeFile=dict(path=(receipts/'actual-types-values.txt').as_posix(),bytes=len(tb),sha256=digest(tb),lines=len(tl)),
                actualTypeCoverage=types,actualTYPELinesCoveredExactlyOnce=[1,len(tl)],
                allActualNonTheoremValuesReviewedEmptySet=True,recursiveAXAllActualOwners='PASS',
                originalObjectSHA256=expected_object,originalObjectBytes=object_bytes,
                originalObjectBinding=obj_bind,receiptResources=resource,
                status='CORRECT_FORMALLY_QUALIFIED_EXACT_SOURCE',formalQualified=True,criticalGaps=[])


if __name__ == '__main__':
    activation = load(OUT / 'parent-activation001.json')
    binding(dict(path=(OUT / 'parent-activation001.json').as_posix(), bytes=14336,
                 sha256='1dd0d35172c046c73c47f051099ce2715284ab08e2169a6c65136c13ae135bea'),
            'exact-parent-activation')
    assert len(activation['mandatoryInputs']) == 51
    for row in activation['mandatoryInputs']:
        binding(row, 'mandatory51')
    old_input = load(OLD / 'INPUT-SEAL.json')
    # Parse and validate every occurrence, not only a hand-picked proof namespace.
    walk_bindings(old_input, 'prior-complete-input-seal')
    old_payload = load(OLD / 'PAYLOAD-SEAL.json')
    walk_bindings(old_payload, 'prior-complete-payload-seal')
    old_coverage = load(OLD / 'COVERAGE.json')
    walk_bindings(old_coverage, 'prior-complete-coverage')
    extra = [
        'drafts/c12-lane/actual-retained-centered-normalized-law-v1/parent-exact-declaration-freeze001.json',
        'drafts/c12-lane/actual-brownian-threshold-payment-v1/parent-exact-declaration-freeze001.json',
        'drafts/c12-lane/actual-retained-centered-normalized-law-v1/parent-source-stage-acceptance005.json',
        'drafts/c12-lane/actual-brownian-threshold-payment-v1/parent-source-stage-acceptance001.json',
    ]
    for p in extra:
        walk_bindings(load(p), p)
    units = [
        machine_unit(223,'actual-retained-centered-normalized-law-v1','native005','kernel005',
                     '18f4db53d7e1c8a3bd07ae4fb9b1b0c8a71a694f8258830f2b412d19b0d825bc',
                     '3ef8fda559a5b06b1b6a3c98681916ce690bee9f634a4c0cd856048d3675e698',532200),
        machine_unit(228,'actual-brownian-threshold-payment-v1','native001','kernel001',
                     'aa7f0e1f46a0fa7aea7c351881851efb80aae09912d1ff7d8da8b1c04e2fd97d',
                     '8267b53f421038e1e9c68d5eea17a49448b6bde65a343c90eb8382b24f982868',371944),
    ]
    intervals = sorted([x for unit in units for x in unit['receiptResources']],key=lambda x:x['startUTC'])
    assert all(datetime.fromisoformat(a['endUTC']) < datetime.fromisoformat(b['startUTC'])
               for a,b in zip(intervals,intervals[1:]))
    boundary = load('drafts/c12-lane/phase29-native-batch/natural-zero-boundary001.json')
    assert boundary['heavy'] == boundary['inflightAfterThisRead'] == boundary['pendingExternalAfterThisRead'] == 0
    assert boundary['actualC12LeanLakeProcesses'] == [] and boundary['c12LockFree']
    assert all(dict((x['unit'],x) for x in units)[223 if 'Retained' in row['mod'] else 228]['source']['sha256'] == row['sourceSHA256']
               and dict((x['unit'],x) for x in units)[223 if 'Retained' in row['mod'] else 228]['originalObjectSHA256'] == row['objectSHA256']
               for row in boundary['sourceRows'])
    phase30 = load('coordination/restart-20261025/HEAVY-PHASE-ROOT-OQ56-30.json')
    assert phase30['phase'] == 'ROOT_OQ56_30' and phase30['heavyAllowances']['c12'] == 0
    walk_bindings(phase30['oldPhase'],'current-phase30/prior-phase')
    walk_bindings(phase30['c12NaturalSourceZeroObservation'],'current-phase30/archived-zero')
    assert datetime.fromisoformat(intervals[-1]['endUTC']) < datetime.fromisoformat(boundary['atUTC']) < datetime.fromisoformat(phase30['atUTC'])
    read('library/Shao/Probability/RetainedComparison.lean')
    for p in [
        'SERVER.md','coordination/TEAM.md','coordination/streamlined-acceptance-current.md','library/lake-manifest.json',
        'C:/Users/UIO/.agents/skills/math-theorem/SKILL.md',
        'C:/Users/UIO/.agents/skills/math-theorem/references/prompt-library.md',
        'C:/Users/UIO/.agents/skills/math-theorem/references/openai-workflow.md',
        'C:/Users/UIO/.agents/skills/math-theorem/references/lean-verification.md',
        'C:/Users/UIO/.codex/skills/chinese-output-style/SKILL.md',
    ]:
        read(p)
    summary = dict(atUTC=datetime.now(timezone.utc).isoformat(),
                   status='PASS_COMPLETE_OFFLINE_EXACT_BINDING_AND_MACHINE_RECEIPT_CHECK',
                   bindingOccurrences=len(ROWS), uniqueReadPaths=len(READS),
                   failures=[r for r in ROWS if not r['verified']],
                   allPass=all(r['verified'] for r in ROWS),
                   bindings=ROWS, readInputs=list(READS.values()))
    assert summary['allPass'], summary['failures']
    write('INPUT-SEAL.json', summary)
    write('DETERMINISTIC-CHECK.json',dict(atUTC=summary['atUTC'],status=summary['status'],
                                        mandatoryInputs=51,allMandatoryVerified=True,
                                        bindingOccurrences=len(ROWS),uniqueReadPaths=len(READS),
                                        allBindingsVerified=True,oldInputSealOccurrences=348,
                                        oldInputSealReadPaths=160,oldPayloads=10,
                                        frozenPreamblesAndHeadsExact=True,wholeProofHashReuses=4,
                                        oldProducerProofReaudits=0,newProofReviews=0,
                                        actualTypes=5,actualNonTheoremValues=0,
                                        allReceiptIntervalsSerial=True,archivedNaturalZeroVerified=True,
                                        currentPhase='ROOT_OQ56_30',currentC12Heavy=0,
                                        historicalSnapshotAliasRequired=False,units=units))
    # The human review is recorded here; the checks above only validate bytes and receipt interfaces.
    semantics = {
        223: {
            'publicActualType': '概率nu、n>0、二阶可积、nE z²=1、原均值0、x≥0、0<epsilon≤1/2和R≤epsilon³/8完整保留；rho/mu/V/chi是同一条件律的实际对象，十二输出与冻结陈述完全一致。',
            'generatedActualType': 'Shao.retainedStandardize.eq_1位于公开命名空间外而真实owner属于本模块；完整类型为任意nu/x/z的真实标准化展开等式，已核对RetainedComparison定义21—24，未加入概率或V>0假设。',
            'boundaries': '源码与四段合格旧证明之一精确复用；未声称已证明无界律比较或C2根。',
        },
        228: {
            'orderedBrownianActualType': '任意可测空间、真实B与概率PB、IsBrownianReal、0<s≤t；真实D的上下存在时刻分立，弱墙保留；差界非负且上界为4(Psi(s)−Psi(t))。',
            'localBrownianActualType': '真实同一Brownian双事件，x/t严格正及同一邻域；尾比较与常数8exp(2)的实际实概率绝对差付款完整。',
            'GaussianActualType': 'x/t非负且同一邻域，包括零点和单点；真实standardNormalTail差常数2exp(2)，无新增结论oracle。',
            'boundaries': '完整三整证明与源码到原稿范围精确复用；不替调用方证明原稿常数选择或剩余根依赖。',
        },
    }
    telemetry = dict(configuredModel='gpt-6.1-sol',configuredEffort='xhigh',freshContext=True,
                     actualModel=None,actualEffort=None,
                     usage=dict(inputTokens=None,cachedInputTokens=None,outputTokens=None,reasoningSubsetTokens=None))
    scope = dict(C2='OPEN',C12='OPEN',fullRootOD='OPEN',OQ3='PAUSED_BY_USER')
    for unit in units:
        unit['actualTypeSemanticReview'] = semantics[unit['unit']]
    coverage = dict(atUTC=summary['atUTC'],role=activation['role'],status='CORRECT',
                    scope='223source005/228source001独立完整机器补充；精确复用已合格完整SOURCE/整证明审查',
                    units=units,mandatoryInputs=51,allMandatoryInputsVerified=True,
                    bindingOccurrences=len(ROWS),uniqueReadPaths=len(READS),
                    newCompleteIndependentWholeProofReviews=0,exactQualifiedWholeProofReuses=4,
                    oldProducerWholeProofReaudits=0,allFiveActualTypesCompletelyRead=True,
                    actualNonTheoremValueCount=0,allActualNonTheoremValuesReviewedEmptySet=True,
                    allFrozenPreamblesAndHeadsExact=True,allSourceChangesCoveredByQualifiedPriorReview=True,
                    recursiveAXWhitelist=['propext','Classical.choice','Quot.sound'],criticalGaps=[],
                    currentPhase='ROOT_OQ56_30',currentC12Heavy=0,noNewExecution=True,
                    historicalSnapshotAliasRequired=False,**telemetry,**scope)
    write('COVERAGE.json',coverage)
    verdict = dict(atUTC=summary['atUTC'],status='CORRECT',
                   units=[dict(unit=u['unit'],source=u['source'],status=u['status'],formalQualified=True,
                               qualifiedWholeProofReuse=True,allActualTypesReviewed=True,
                               allActualNonTheoremValuesReviewedEmptySet=True,recursiveAX='PASS',
                               originalObjectSHA256=u['originalObjectSHA256'],originalObjectBytes=u['originalObjectBytes'],
                               criticalGaps=[]) for u in units],
                   authorReviewerSeparated=True,sourceWrites=0,newProofReviews=0,oldProducerProofReaudits=0,
                   nextDependencies='既有C12 owner按精确两源/原O登记资格与实质里程碑发布，继续229和实际条件保留律比较的源绑定依赖；无新增执行或根闭合授权。',
                   noRootClosure=True,**telemetry,**scope)
    write('VERDICT.json',verdict)
    checkpoint = dict(atUTC=summary['atUTC'],role=activation['role'],status='REVIEW_COMPLETE_FINAL_SEAL_AND_RELEASE_ONLY',
                      completedUnits=[223,228],qualifiedSources={str(u['unit']):u['source']['sha256'] for u in units},
                      exactNextDependency='仅封存本目录PAYLOAD并写实际全零RELEASE；之后交回既有C12 owner办理精确范围资格/发布并继续229/条件保留律比较。',
                      actualRunState=dict(reviewer=1,artifactWriter=1,sourceWriters=0,heavy=0,inflight=0,
                                          pendingExternal=0,children=0,Lean=0,AX=0,server=0,network=0,
                                          upload=0,GitAPI=0,persistentOwnedProcesses=0,queuedCommands=0,
                                          pendingWrites=2),
                      actualFinalRunState='由随后RELEASE.json记录；本CHECKPOINT不把尚待封印写入说成已释放。',
                      noFurtherProofOrMachineWork=True,**telemetry,**scope)
    write('CHECKPOINT.json',checkpoint)
    report = (OUT/'REPORT.md').read_bytes()
    assert f'{len(ROWS)} 个绑定出现、{len(READS)} 个不同读取路径' in report.decode('utf-8')
    payloads = []
    for p in sorted(OUT.iterdir()):
        if not p.is_file() or p.name in ['parent-activation001.json','PAYLOAD-SEAL.json','RELEASE.json']:
            continue
        pb = p.read_bytes()
        pb.decode('utf-8')
        assert not pb.startswith(b'\xef\xbb\xbf') and b'\r' not in pb
        payloads.append(dict(path=p.as_posix(),bytes=len(pb),sha256=digest(pb)))
    assert {Path(p['path']).name for p in payloads} == {
        'ACK.json','BINDING-CHECK-PRELIMINARY.json','CHECKER-REPAIRS.json',
        'CHECKPOINT.json','COVERAGE.json','DETERMINISTIC-CHECK.json','INPUT-SEAL.json',
        'REPORT.md','VERDICT.json','verify_inputs.py','verify_inputs.failed001.py.txt'}
    write('PAYLOAD-SEAL.json',dict(atUTC=datetime.now(timezone.utc).isoformat(),status='EXACT_REVIEW_PAYLOAD_SEALED',
                                   payloadCount=len(payloads),payloads=payloads,allPayloadsUTF8NoBOMLF=True,
                                   activationSourceOldReviewLibraryCoordinationReadOnly=True,
                                   selfAndReleaseExcludedForAcyclicSeal=True,
                                   units={str(u['unit']):u['status'] for u in units},**telemetry,**scope))
    seal = (OUT/'PAYLOAD-SEAL.json').read_bytes()
    # This is the final mutation performed by this role. There is no retained execution or write queue.
    zero = dict(reviewer=0,artifactWriter=0,sourceWriters=0,heavy=0,inflight=0,pendingExternal=0,
                children=0,Lean=0,AX=0,server=0,network=0,upload=0,GitAPI=0,persistentOwnedProcesses=0,
                queuedCommands=0,pendingWrites=0)
    write('RELEASE.json',dict(atUTC=datetime.now(timezone.utc).isoformat(),
                              status='NATURAL_COMPLETE_REVIEW_ALL_ZERO_RELEASE',directory=OUT.as_posix(),
                              sourceOwnership='NONE_EVER',scope='仅本独立reviewer实际状态，不声称当前全局服务器状态',
                              allReviewWriterExecutionChildAuthorityReleased=True,
                              payloadSeal=dict(path=(OUT/'PAYLOAD-SEAL.json').as_posix(),bytes=len(seal),sha256=digest(seal)),
                              units={str(u['unit']):dict(status=u['status'],formalQualified=True) for u in units},
                              **zero,**telemetry,**scope))
    print(json.dumps({k:summary[k] for k in ['status','bindingOccurrences','uniqueReadPaths','allPass','failures']},
                     ensure_ascii=False, indent=2))
    for name in ['REPORT.md','COVERAGE.json','VERDICT.json','INPUT-SEAL.json','PAYLOAD-SEAL.json','CHECKPOINT.json','RELEASE.json']:
        rb = (OUT/name).read_bytes()
        print(json.dumps(dict(file=name,bytes=len(rb),sha256=digest(rb))))
