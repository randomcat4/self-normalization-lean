from pathlib import Path
import datetime
import hashlib
import json

BASE = Path('C:/game/shao lean/drafts/oq56/unit248')
OUT = BASE / 'source-review-repair-02'
ROLE = '/root/oq56_original_same_witness_physical_paid_tail248_source_review'
OWNER = '01a17665-2e41-7ed1-9911-57f16fe889fa'
NOW = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat()
SHA = lambda b: hashlib.sha256(b).hexdigest()
ZERO_OPS = {k: 0 for k in ['Lean', 'lake', 'kernel', 'PP', 'AX', 'server', 'network', 'upload', 'Git', 'API', 'children']}
MODEL = {'requestedModel': 'gpt-6.1-sol', 'requestedEffort': 'xhigh', 'actualBackend': None,
         'actualModel': None, 'actualEffort': None,
         'usage': {'input': None, 'cachedInput': None, 'output': None, 'reasoningSubset': None}}

def bind(path):
    p = Path(path)
    b = p.read_bytes()
    return {'path': p.as_posix(), 'sha256': SHA(b), 'bytes': len(b)}

def verify(v):
    assert bind(v['path']) == {k: v[k] for k in ['path', 'sha256', 'bytes']}, v['path']

def save(name, value):
    (OUT / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n',
                            encoding='utf-8', newline='\n')

assert not (OUT / 'lastzeroRELEASE.json').exists(), 'FINALWRITE already exists; never replay'
ap = BASE / 'affected-review-activation-02/ACTIVATION.json'
assert bind(ap)['sha256'] == '74d18402031bc8700b9a4891109b6f380fb664d5ab8a234e6fde95c104794e10'
a = json.loads(ap.read_bytes())
for v in a['inputs']:
    verify(v)
assert len(a['inputs']) == 55
verify(a['authorRepairFINALWRITE'])
ar = json.loads(Path(a['authorRepairFINALWRITE']['path']).read_bytes())
assert ar['FINALWRITE'] and len(ar['sixZero']) == 6 and all(v == 0 for v in ar['sixZero'].values())
prior_complete = a['priorCompleteSourceReview']
prior_affected = a['priorAffectedUnionReview']
assert prior_complete['sha256'] == 'dd4de77c69e558b60f9bb468f7c601016446796b09563a2c3514d103e6ec4d5a'
assert prior_affected['sha256'] == 'ca2b1935d87dcd4e5583d7f769fdc056740cbe16bd5de84f220c0eed99f28a93'
v = json.loads((OUT / 'INDEPENDENT-DELTA-VERIFICATION.json').read_bytes())
ctx = json.loads((BASE / 'author-repair-02/ACTUAL-PROP-CONTEXTS.json').read_bytes())
assert v['wholeByteForwardSingleInsertionExact'] and v['wholeByteReverseTo50feaExact']
assert v['allOther31FullPropsExact'] and v['inheritedCoordinateChecksDerived'] == 353
assert v['totalCurrentCoordinateRecordsDerived'] == 354
assert v['qualified220CompleteTYPERead']['typeLines'] == 296
source = v['source']
verify(source)
assert source['sha256'] == '50cc9872e1d6148e4a81f0d49da391a1b4b749b682c91b4ba347ae22bad00433'
next_dep = ('Lead-only native03 on exact50cc from known-ended native02 receipt cc260aa6340166147381e8290de9572a6fae16dd794ee577f0f14be27e5e5ff0; '
            'if successful preserve SAMEFIRSTO then all-owned actualTYPE/requiredVALUE/transitiveAX; SAMEreviewer finaljoin under new activation. '
            'If same interface error remains reassess actual interface before further patches. P168 already adopted native01cfg1c8, never readopt.')
union = {'completeOriginalSOURCEReview': prior_complete,
         'completeAffected01UnionReview': prior_affected,
         'currentAffected02Review': 'Complete one45BTYPE-local instance/type/RHS/ambient-domain/qualified220currentTYPE review',
         'allUnchangedEvidenceReusedExactly': True, 'uncoveredChangedBytes': 0,
         'oldSourceProofOrQualified247TYPEReviewReplayed': False,
         'wholeSourceToStatementProofCoverageCompleteViaExactUnion': True}
reading = {'fullAuthorREPORTAndPATCHAndInterfaceReadDescriptor': True, 'fullFreeze03Metadata': True,
           'fullCurrentHMeas220TypeAndRHS': True,
           'completeSourceBlocksReadThisTurn': [[2053,2063],[3519,3529],[3720,3782],[3798,3804],[3959,3965]],
           'qualified220CompleteActualPublicTYPE': v['qualified220CompleteTYPERead'],
           'native02FullError': {'bytes': 5264, 'sha256': '927a55441b499ae29bb998f5a0d7cc6533c41a89144635f1825c87237be935a5', 'completeRead': True},
           'newInstanceAndContextFullyRead': True, 'wholeCurrentSourceUnchangedPartReusedFromCompletePriorReview': True}
coverage = {'schema': 'oq56-unit248-independent-complete-exact-SOURCE-affected02-union-coverage-v1',
 'atUTC': NOW(), 'role': ROLE, 'ownerChat': OWNER, 'ownedRoot': OUT.as_posix(),
 'source': source, 'sourceLF': 3965, 'activation': bind(ap), 'verifiedActivationInputCount': 55,
 'sameReviewer': True, 'neverAuthor': True, 'independent': True,
 'coverageUnion': union, 'actualReading': reading,
 'completeUniqueCurrentContexts': ctx['completeUniqueContexts'],
 'full32CurrentFrozenPropositions': v['full32Propositions'],
 'additional8LogicalPackages': ctx['additionalPureLogicalPackages'],
 'public145FullTypeRHSScopeAndCoordinates': ctx['publicOrdinary'],
 'optional147FullTypeRHSScope': ctx['approvedOptionalOrdinary'],
 'same2DataChoicesFullTypeRHSChoicePropScopeCoordinates': ctx['actualSameModelChoices'],
 'approved9InstanceFullTypeRHSScope': ctx['approvedInstances'],
 'API5ImplicitFullTypeRHSScope': ctx['APIImplicitInstances'],
 'countsDerived': {'publicOrdinary': len(ctx['publicOrdinary']), 'optionalOrdinary': len(ctx['approvedOptionalOrdinary']),
   'frozenProps': len(v['full32Propositions']), 'additionalLogicalPackages': len(ctx['additionalPureLogicalPackages']),
   'approvedInstances': len(ctx['approvedInstances']), 'usedApprovedInstances': sum(x['used'] for x in ctx['approvedInstances']),
   'APIImplicitInstances': len(ctx['APIImplicitInstances']), 'sameDataChoices': len(ctx['actualSameModelChoices']),
   'inheritedCoordinateChecks': 353, 'newInstanceCoordinateChecks': 1, 'totalCurrentCoordinateRecords': 354,
   'current248MachineOwnerCount': None, 'current248MachineTYPECount': None, 'current248MachineVALUECount': None},
 'onlyCurrentChangedType': 'hMeas220', 'other31FullTypesExact': True, 'all8LogicalPackageTypesExact': True,
 'newTypeLocalInstanceIntroducesHypothesis': False, 'newOuterExecutableOmegaReinstalls': 0,
 'newModelLawSelectorCutoffWindowCostZeroAtomPremise': False,
 'selectedOuterM0AndOriginalSampleMNAndOriginalPUnchanged': True,
 'fullHMeas220LastDeletedSubtypePiNowOriginalmOmega': True,
 'newSourceByteDelta': {'bytes':45,'LF':1,'byteOffset':241315,'line':3723,'insertedLine':v['insertedLine'],
                       'forwardWholeByteExact':True,'reverseWholeByteExact':True},
 'originalScopeRetention': {'original16PiAnd222BH247CallBeforeGlobalLets': True,
   'same247CgAndM0Only': True, 'universalClauses':71,'paymentClauses':39,'physicalClauses':8,
   'actualSameNWH1AndPaymentAtOne': True,'original197Geometry':True,
   'original210PhysicalZeroBranchExplicitOnePlusRhoGuard':True,
   'original220AtSameNZeroZ512OriginalSampleGlobalMeasurability':True,
   'allRealClosedUpperLowerSymmetricDifferenceFiniteProbability':True,
   'currentZOriginalPhysicalPaidTailAndBothPaymentTerms':True,
   'fullWeightedSourceCostBothWindowsExternalSZCBudgetScopes':True},
 'native02Failure': v['native02Failure'], 'native03': 'PENDING_LEAD_NOT_EXECUTED_BY_REVIEWER',
 'proofOrElaborationPassClaimedForCurrentSource': False,
 'sourceAccepted': True,'qualified':False,'kernelPending':True,'kernelChecked':False,'axiomAudited':False,
 'criticalGaps': [], 'noGapsWithinExactSourceReviewUnion':True,
 'evidence': {'independentDeltaVerification':bind(OUT/'INDEPENDENT-DELTA-VERIFICATION.json'),
              'fullAffectedBlocks':bind(OUT/'AFFECTED-BLOCKS.json'),
              'authorFullCurrentContextMap':bind(BASE/'author-repair-02/ACTUAL-PROP-CONTEXTS.json')},
 'operations':ZERO_OPS,'P168Readopted':False,'nextExactDependency':next_dep,**MODEL}
save('COVERAGE.json', coverage)
verdict = {'schema':'oq56-unit248-SAMEindependent-affected02-source-verdict-v1','atUTC':NOW(),
 'role':ROLE,'ownerChat':OWNER,'ownedRoot':OUT.as_posix(),'source':source,'sourceLF':3965,
 'independent':True,'sameReviewer':True,'neverAuthor':True,'sourceAccepted':True,'qualified':False,
 'kernelPending':True,'kernelChecked':False,'axiomAudited':False,
 'status':'COMPLETE_EXACT_PRIOR_SOURCE_PLUS_AFFECTED01_PLUS_AFFECTED02_UNION_SOURCE_ACCEPTED_KERNEL_PENDING',
 'completeSourceToStatementProofReviewViaExactUnion':True,'coverageUnion':union,
 'criticalGaps':[],'uncoveredChangedBytes':0,'all32FullPropsAnd9InstancesAnd5APICovered':True,
 'only45BTypeLocalOriginalOmegaInstanceAdded':True,'fullQualified220296Line22108ByteCurrentTYPERead':True,
 'inherited353CoordinatesAndNew1CoordinateVerified':True,
 'native02ActualRC':1,'native02Errors':1,'native02Warnings':8,'native02Object':None,
 'native02AllOwnedEnded':True,'native02ProtectedRecords':25348,'native03Required':True,
 'currentUnit248ActualTYPEOwnerCounts':None,'allNative02ErrorsClaimedResolvedByMachine':False,
 'reviewerMachineExecutions':0,'P168Readopted':False,'operations':ZERO_OPS,
 'coverage':bind(OUT/'COVERAGE.json'),'fullreport':bind(OUT/'fullreport.md'),
 'nextExactDependency':next_dep,**MODEL}
save('verdict.json',verdict)
checkpoint={'schema':'oq56-unit248-SAMEindependent-affected02-complete-checkpoint-v1','atUTC':NOW(),
 'role':ROLE,'ownerChat':OWNER,'ownedRoot':OUT.as_posix(),'source':source,'sourceLF':3965,
 'readingFrontier':'Complete affected02 SOURCE/type/RHS/context/interface reading and independent exact entirebyte/inventory/coordinate verification; prior complete source and affected01 reused unchanged.',
 'actualReading':reading,'sourceAccepted':True,'qualified':False,'kernelPending':True,
 'currentReviewComplete':True,'uncertainOperations':0,'heavy':0,'inflight':0,'pendingExternal':0,
 'nextExactDependency':next_dep,'operations':ZERO_OPS,'P168Readopted':False,**MODEL}
save('CHECKPOINT.json',checkpoint)

# Every payload is completed before manifest construction.  The release below is the final write.
payloads = [bind(p) for p in sorted(OUT.iterdir(),key=lambda p:p.name)
            if p.is_file() and p.name not in ['MANIFEST.json','lastzeroRELEASE.json']]
assert len(payloads)==9
for p in payloads:
    verify(p)
manifest={'schema':'oq56-unit248-SAMEindependent-affected02-complete-SOURCE-union-manifest-v1','atUTC':NOW(),
 'role':ROLE,'ownerChat':OWNER,'ownedRoot':OUT.as_posix(),'activation':bind(ap),
 'inputs':a['inputs'],'inputCountDerived':len(a['inputs']),
 'source':source,'sourceLF':3965,'payloads':payloads,'payloadCountDerivedExcludingManifestAndFinalRelease':len(payloads),
 'coverageUnion':union,'allInputsAndPayloadsHashBound':True,
 'allInherited353AndNew1CoordinatesVerified':True,'only45BTypeLocalLine':True,
 'all32FullProps9Instances5APIAnd145Public147OptionalCovered':True,
 'qualified220CompleteActualTYPE296Lines22108BytesRead':True,
 'sourceAccepted':True,'qualified':False,'kernelPending':True,'kernelChecked':False,'axiomAudited':False,
 'criticalGaps':[],'neverAuthor':True,'sameReviewer':True,'independent':True,
 'operations':ZERO_OPS,'P168Readopted':False,
 'selfBinding':'Bound by final lastzeroRELEASE; manifest does not self-hash.',
 'nextExactDependency':next_dep,**MODEL}
save('MANIFEST.json',manifest)
for p in manifest['payloads']+manifest['inputs']+[manifest['activation']]:
    verify(p)
release={'schema':'oq56-unit248-SAMEindependent-affected02-FINALWRITE-sixzero-release-v1','atUTC':NOW(),
 'role':ROLE,'ownerChat':OWNER,'ownedRoot':OUT.as_posix(),'FINALWRITE':True,
 'status':'COMPLETE_EXACT_PRIOR_PLUS_AFFECTED01_PLUS_AFFECTED02_SOURCE_ACCEPTED_KERNEL_PENDING_SEALED_RELEASED',
 'manifest':bind(OUT/'MANIFEST.json'),'source':source,'sourceLF':3965,
 'inputCountDerived':55,'payloadCountDerivedExcludingManifestAndFinalRelease':len(payloads),
 'allInputsAndPayloadsHashBound':True,'writerReleased':True,'executionReleased':True,
 'publicationReleased':True,'childAuthorityReleased':True,
 'sixZero':{'writers':0,'heavyCommands':0,'inflightExecution':0,'pendingExternal':0,'children':0,'uncertainOperations':0},
 'sixZeroScope':'This SAME independent affected02 review role only; no lead/Root/server process claim.',
 'noFurtherWritesAfterThisRelease':True,'sameReviewer':True,'neverAuthor':True,'independent':True,
 'sourceAccepted':True,'qualified':False,'kernelPending':True,'kernelChecked':False,'axiomAudited':False,
 'criticalGaps':[],'completeExactSourceReviewUnion':True,
 'only45BTypeLocalOriginalOmegaLineReviewed':True,'qualified220CompleteActualTYPERead':True,
 'native02StillFailedNoObject':True,'native03StillRequired':True,'current248ActualTYPECounts':None,
 'operations':ZERO_OPS,'P168Readopted':False,'nextExactDependency':next_dep,**MODEL}
save('lastzeroRELEASE.json',release)
# No filesystem writes below this line.
print(json.dumps({'SEALED':True,'sourceAccepted':True,'qualified':False,'kernelPending':True,
 'MANIFEST':bind(OUT/'MANIFEST.json'),'FINALWRITE':bind(OUT/'lastzeroRELEASE.json'),
 'COVERAGE':bind(OUT/'COVERAGE.json'),'REPORT':bind(OUT/'fullreport.md'),
 'VERDICT':bind(OUT/'verdict.json'),'payloads':len(payloads),'inputs':55},ensure_ascii=False))
