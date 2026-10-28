from pathlib import Path
from collections import Counter
import datetime,hashlib,json

BASE=Path('C:/game/shao lean/drafts/oq56/unit248');OUT=BASE/'final-review-01'
assert not (OUT/'lastzeroRELEASE.json').exists(),'FINALWRITE already exists; never replay'
ROLE='/root/oq56_original_same_witness_physical_paid_tail248_source_review'
OWNER='01a17665-2e41-7ed1-9911-57f16fe889fa'
NOW=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
SHA=lambda b:hashlib.sha256(b).hexdigest()
MODEL={'requestedModel':'gpt-6.1-sol','requestedEffort':'xhigh','actualBackend':None,'actualModel':None,'actualEffort':None,
       'usage':{'input':None,'cachedInput':None,'output':None,'reasoningSubset':None}}
OPS={k:0 for k in ['Lean','lake','kernel','PP','AX','server','network','upload','Git','API','children']}
def bind(p):
    p=Path(p);b=p.read_bytes();return {'path':p.as_posix(),'sha256':SHA(b),'bytes':len(b)}
def verify(v):assert bind(v['path'])=={k:v[k] for k in ['path','sha256','bytes']},v['path']
def load(p):return json.loads(Path(p).read_bytes())
def save(name,j):(OUT/name).write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
ap=BASE/'final-review-activation-01/ACTIVATION.json';a=load(ap)
assert bind(ap)['sha256']=='47cd6f7ea850ba66a6849fb1f9366614834e29ecd17877a54c412fd0337325f1'
assert len(a['inputs'])==101
for v in a['inputs']:verify(v)
sr=load(BASE/'source-review-repair-02/lastzeroRELEASE.json')
assert sr['FINALWRITE'] and all(v==0 for v in sr['sixZero'].values()) and sr['sourceAccepted']
meta=load(BASE/'normalized-owner-evidence-01/actual-owned-metadata.json')
summary=load(BASE/'normalized-owner-evidence-01/native-kernel-and-all-owner-audit-summary.json')
machine=load(OUT/'MACHINE-JOIN-VERIFICATION.json')
rest=load(OUT/'TYPE-INDEPENDENT-RESTORATION.json')
corr=load(OUT/'PUBLIC-TYPE-CORRESPONDENCE.json')
scope=load(OUT/'BINDER-SCOPE-JOIN.json')
prior=load(BASE/'source-review-repair-02/COVERAGE.json')
entry=meta['entries'][0]
assert rest['wholeByteRoundTrip'] and rest['wholeTokenRoundTrip'] and rest['wholeTriviaRoundTrip']
assert rest['all318DictionaryEntriesAndAll492MainLinesCompletelyRead']
assert rest['fullAuditStdoutReconstruction']['exact'] and rest['noPrinterFailuresOrElision']
assert corr['orderedNamesExactlyMatchAll145PublicSourceRows'] and len(corr['rows'])==145
assert scope['actualTopBinderGroupsDerived']==16 and scope['allScopesReadCompletely']
assert machine['allRecursiveAxiomsWhitelisted'] and machine['native']['actualExitCode']==machine['sameFIRSTOAudit']['actualExitCode']==0
assert machine['source']==summary['source']==meta['source'] and machine['FIRSTO']==summary['object']==meta['object']
assert machine['sourceCoordinateCountDerived']==354
assert a['source']==prior['source']==sr['source']
sources=[]
for folder in ['source-review-01','source-review-repair-01','source-review-repair-02']:
    sources.append({'manifest':bind(BASE/folder/'MANIFEST.json'),'release':bind(BASE/folder/'lastzeroRELEASE.json'),
                    'fullreport':bind(BASE/folder/'fullreport.md'),'coverage':bind(BASE/folder/'COVERAGE.json'),
                    'verdict':bind(BASE/folder/'verdict.json')})
source_union={'manifest':sources[-1]['manifest'],'release':sources[-1]['release'],'fullreport':sources[-1]['fullreport'],
 'coverage':sources[-1]['coverage'],'verdict':sources[-1]['verdict'],'fullUnion':sources,
 'completeSourceToStatementProofReview':True,'unchangedSourceReusedExactly':True,
 'completeOriginalThenAffected01ThenAffected02':True,'newFullProofReviewReplay':False,
 'currentSource':a['source'],'sourceLF':3965,'currentSourceCoordinatesDerived':354}
type_binding=bind(BASE/'normalized-owner-evidence-01/actual-owned-types.txt')
value_binding=bind(BASE/'normalized-owner-evidence-01/actual-owned-values.txt')
metadata_binding=bind(BASE/'normalized-owner-evidence-01/actual-owned-metadata.json')
ax=dict(Counter(x for row in meta['entries'] for x in row['axioms']))
counts={'actualOwned':len(meta['entries']),'theorems':sum(row['isTheorem'] for row in meta['entries']),
        'nonTheorems':sum(not row['isTheorem'] for row in meta['entries']),
        'TYPElines':sum(row['typeLines'] for row in meta['entries']),
        'VALUElines':sum(row.get('valueLines',0) for row in meta['entries'])}
assert counts=={'actualOwned':1,'theorems':1,'nonTheorems':0,'TYPElines':14646,'VALUElines':0}
semantic_scope={'description':'Originalsamewitnessfiniteconditionalphysicalscalarpaidtail, samecg/m0,n/w, originalnormalizedkernel and originalsample.',
 'physicalGuard':'1 + rho ≤ Real.sqrt (n : ℝ)',
 'sameAtOneAndCurrentZWitness':True,'universalClausesRetained':71,'paymentClausesRetained':39,'physicalClauses':8,
 'weightedSourceCostRetained':True,'remainderAndMomentWindowsRetained':True,'externalSZAndCBudgetScopesRetained':True,
 'allRealClosedUpperAndLowerEvents':True,'atomPremiseAdded':False,
 'lowerPayments':'- payment_z - payment1','upperPayments':'+ 3 * payment_z + payment1',
 'rootAndFullOQ56':'OPEN','unit249Implemented':False}
outside=['cost smallness','payment absorption','existence of the external scalar SZ premise','uniform late-rho removal of the explicit physical guard',
         'unguarded physical equality','CDF upgrade','full OQ56 closure','root completion']
coverage={'schema':'oq56-unit248-SAMEindependent-complete-final-source-currentTYPE-FIRSTO-coverage-v1','atUTC':NOW(),
 'reviewer':ROLE,'ownerChat':OWNER,'ownedRoot':OUT.as_posix(),'activation':bind(ap),'verifiedImmutableInputCount':101,
 'independent':True,'neverAuthor':True,'sameReviewer':True,'source':summary['source'],'localReviewedSource':a['source'],'sourceLF':3965,
 'sourceReviewReusedExactly':source_union,
 'all32FullFrozenProps':prior['full32CurrentFrozenPropositions'],
 'all8LogicalPackages':prior['additional8LogicalPackages'],
 'all145PublicSourceFullTypeRHSScopeAndCoordinates':prior['public145FullTypeRHSScopeAndCoordinates'],
 'all147OptionalSourceFullTypeRHSScope':prior['optional147FullTypeRHSScope'],
 'same2ChoicesFullTypeRHSPropScope':prior['same2DataChoicesFullTypeRHSChoicePropScopeCoordinates'],
 'all9InstancesFullTypeRHSScope':prior['approved9InstanceFullTypeRHSScope'],
 'all5ImplicitAPIFullTypeRHSScope':prior['API5ImplicitFullTypeRHSScope'],
 'sourceCoordinateRecordsDerived':354,'sourceInheritedRebasedCoordinateRecords':353,'sourceNewTypeLocalCoordinateRecords':1,
 'completeCurrentActualTYPE':{'typeFile':type_binding,'metadata':metadata_binding,'TYPElines':14646,'TYPEbytes':2347133,'TYPEtokens':59334,
     'bodyTYPEBytes':2347008,'bodyTYPESHA256':rest['TYPEBodySHA256'],
     'completeDictionaryRead':True,'dictionaryEntries':318,'readDictionaryRanges':rest['readDictionaryRanges'],
     'completeCurrentMainRead':True,'mainEntries':15705,'mainReadLines':492,'readMainRanges':rest['readMainRanges'],
     'dictionary':bind(OUT/'TYPE-LOSSLESS-DICTIONARY.json'),'dictionaryRead':bind(OUT/'TYPE-DICTIONARY-READ.txt'),'mainRead':bind(OUT/'TYPE-MAIN-READ.txt'),
     'allBytesTokensTriviaIndependentlyRestored':True,'noPrinterFailuresOrElision':True,
     'restoration':bind(OUT/'TYPE-INDEPENDENT-RESTORATION.json'),
     'public145ActualFullTypeRHSAndSourceCorrespondence':bind(OUT/'PUBLIC-TYPE-CORRESPONDENCE.json'),
     'actual16BindersAndAllScopeCoverage':bind(OUT/'BINDER-SCOPE-JOIN.json')},
 'requiredVALUE':{'file':value_binding,'bytes':0,'lines':0,'requiredNonTheorems':0,'complete':True},
 'fullAuditStdoutIndependentReconstruction':rest['fullAuditStdoutReconstruction'],
 'actualAllOwnerCountsDerived':counts,'actualName':entry['name'],'levelParams':entry['levelParams'],'constantKind':entry['constantKind'],
 'bodyExpressionPresent':entry['bodyExpressionPresent'],'actualGeneratedHelperCount':0,'allTransitiveAxioms':ax,
 'allRecursiveAxiomsWhitelisted':True,'completeSourceToStatementProofReview':True,'allCurrentTYPERequiredVALUEReadComplete':True,
 'machineJoin':bind(OUT/'MACHINE-JOIN-VERIFICATION.json'),'firstOriginalObject':summary['object'],
 'nativeActualRC':0,'auditActualRC':0,'nativeOuterRC':1,'auditOuterRC':1,'wrapperNativeSuccess':False,'wrapperAuditSuccess':False,
 'FIRSTEMPTY':None,'FIRSTEMPTYIsReturnedRunnerField':False,
 'scope':semantic_scope,'remainingOutsideScope':outside,
 'sourceAccepted':True,'qualified':True,'kernelPending':False,'kernelChecked':True,'axiomAudited':True,
 'criticalGaps':[],'reviewerOperations':OPS,'P168Readopted':False,**MODEL}
save('COVERAGE.json',coverage)
active_type={'typeFile':type_binding,'VALUEfile':value_binding,'metadata':metadata_binding,'coverage':bind(OUT/'COVERAGE.json'),
 'TYPElines':14646,'TYPEbytes':2347133,'TYPEtokens':59334,'VALUElines':0,'VALUEbytes':0,
 'dictionary':bind(OUT/'TYPE-LOSSLESS-DICTIONARY.json'),'completeDictionaryRead':True,'completeCurrentMainRead':True,
 'allBytesTokensTriviaIndependentlyRestored':True,'noPrinterFailuresOrElision':True,
 'TYPEBodyBytes':2347008,'TYPEBodySHA256':rest['TYPEBodySHA256'],
 'completeReadingRanges':{'dictionary':rest['readDictionaryRanges'],'currentMain':rest['readMainRanges']}}
warnings=load(BASE/'lead-execution-03/native-warning-classification.json')
qualified={'schema':'oq56-unit248-SAMEindependent-qualified-exact-source-first-originalO-evidence-v1','atUTC':NOW(),
 'unit':248,'reviewer':ROLE,'ownerChat':OWNER,'ownedRoot':OUT.as_posix(),'independent':True,'neverAuthor':True,'sameReviewer':True,
 'STATUS':'QUALIFIED_EXACT_SOURCE_FIRST_ORIGINAL_OBJECT_COMPLETE_INDEPENDENT_REVIEW','verdict':'ACCEPT_QUALIFIED_EXACT_UNIT248_SCOPE',
 'qualified':True,'kernelPending':False,'sourceAccepted':True,'completeSourceToStatementProofReview':True,
 'completeIndependentReview':True,'kernelChecked':True,'axiomAudited':True,'allCurrentTYPERequiredVALUEReadComplete':True,
 'module':meta['module'],'publicTheorem':entry['name'],'source':summary['source'],'localReviewedSource':a['source'],'sourceLF':3965,
 'sourceReviewReusedExactly':source_union,'firstOriginalObject':summary['object'],'FIRSToriginalObject':summary['object'],
 'firstOriginalObjectIsFirstSuccess':True,'sameOriginalObjectAuditedWithout_o':True,
 'native':summary['native03'],'sameOriginalObjectAudit':summary['ownedAudit01'],
 'nativeActualRC':0,'auditActualRC':0,'nativeOuterRC':1,'auditOuterRC':1,'wrapperNativeSuccess':False,'wrapperAuditSuccess':False,
 'FIRSTEMPTY':None,'FIRSTEMPTYIsReturnedRunnerField':False,
 'actualOwnedCount':counts['actualOwned'],'actualTheoremCount':counts['theorems'],'actualNonTheoremCount':counts['nonTheorems'],
 'actualGeneratedHelperCount':0,'actualOwnerDiscovery':meta['ownerDiscovery'],'allActualBodiesPresent':True,
 'levelParams':entry['levelParams'],'constantKind':entry['constantKind'],'allTransitiveAxioms':ax,'allRecursiveAxiomsWhitelisted':True,
 'activeCompleteTYPE':active_type,'fullAuditStdoutIndependentReconstruction':rest['fullAuditStdoutReconstruction'],
 'preservation':{'sourceObjectShaBytesNsPreserved':True,'nativeProtectedRecords':25388,'auditProtectedRecords':25398,
   'allOwnedProcessesEnded':True,'noTimeoutCleanupOwnershipIssueVerifiedByBoundNormalizer':True,'uncertainOperations':0,
   'serverBinding':bind(BASE/'normalized-owner-evidence-01/server-metadata-binding.json')},
 'warnings':{'nativeSourceErrors':0,'nativeSourceWarnings':52,'categoriesDerived':dict(Counter(x['category'] for x in warnings['warnings'])),
   'classification':bind(BASE/'lead-execution-03/native-warning-classification.json'),'standingStderrBytes':134,
   'standingStderrSHA256':'11ec49f9906e54894a8ffa4551c841fd9873cf63f295722c88755032b40c3cbf',
   'allOriginalMessagesRemainServer':True,'fullWarningMessageReadingClaimed':False,'noSourceChangesToSilenceWarnings':True},
 'runtimeClaim':{'singleNativeFrame':machine['nativeSingleLiveFrame'],'postAuditActualZeroObserved':True,'postAuditOwnLockFreeObserved':True,
   'continuousAllTIDObservationClaim':False,'allOwnedEnded':True,'currentExecutionPhase':'ROOT_OQ56_OQ3_40','historicalPhase39RunnerLabelsRetained':True},
 'P168AdoptedExactlyOnceNativeConfig':machine['P168AdoptedOnceOriginalCfg1c8'],'P168Readopted':False,
 'reviewPayloads':{'fullreport':bind(OUT/'fullreport.md'),'coverage':bind(OUT/'COVERAGE.json'),
   'restoration':bind(OUT/'TYPE-INDEPENDENT-RESTORATION.json'),'machineJoin':bind(OUT/'MACHINE-JOIN-VERIFICATION.json'),
   'publicCorrespondence':bind(OUT/'PUBLIC-TYPE-CORRESPONDENCE.json'),'binderScopes':bind(OUT/'BINDER-SCOPE-JOIN.json'),
   'localDiagnosticHistory':bind(OUT/'LOCAL-DIAGNOSTIC-HISTORY.json')},
 'rootAccepted':False,'rootIntegrationAccepted':False,'rootAndFullOQ56':'OPEN','scope':semantic_scope,'remainingOutsideScope':outside,
 'nextExactDependency':'Lead exact-evidence publication/intake and planned natural successor handoff; reviewer stops writes after FINALWRITE. No unit249 implementation.',
 'reviewerOperations':OPS,'actualMetadata':metadata_binding,'actualTypes':type_binding,'actualValues':value_binding,
 'summary':bind(BASE/'normalized-owner-evidence-01/native-kernel-and-all-owner-audit-summary.json'),
 'serverMetadataBinding':bind(BASE/'normalized-owner-evidence-01/server-metadata-binding.json'),
 'allOwnerCountsDerived':counts,'allTYPElines':14646,'allVALUElines':0,'allOwnedProcessesEnded':True,
 'heavy':0,'inflight':0,'pendingExternal':0,**MODEL}
save('qualified-evidence.json',qualified)
ck=load(OUT/'CHECKPOINT.json');ck.update({'atUTC':NOW(),'qualificationAccepted':True,'qualified':True,'kernelPending':False,
 'finalReviewComplete':True,'remaining':[],'nextExactDependency':qualified['nextExactDependency'],
 'nativeActualRC':0,'auditActualRC':0,'actualOwnedCount':1,'sourceCoordinateRecordsDerived':354,
 'uncertainOperations':0,'heavy':0,'inflight':0,'pendingExternal':0})
save('CHECKPOINT.json',ck)
payloads=[bind(p) for p in sorted(OUT.iterdir(),key=lambda p:p.name) if p.is_file() and p.name not in ['MANIFEST.json','lastzeroRELEASE.json']]
assert len(payloads)==16,len(payloads)
for v in payloads:verify(v)
manifest={'schema':'oq56-unit248-SAMEindependent-complete-qualified-final-review-manifest-v1','atUTC':NOW(),
 'role':ROLE,'ownerChat':OWNER,'ownedRoot':OUT.as_posix(),'activation':bind(ap),'inputs':a['inputs'],'inputCountDerived':101,
 'payloads':payloads,'payloadCountDerivedExcludingManifestAndFinalRelease':len(payloads),
 'source':a['source'],'remoteSource':summary['source'],'sourceLF':3965,'firstOriginalObject':summary['object'],
 'completeSourceReviewUnion':source_union,'completeCurrentTYPERequiredVALUEReading':True,'allTYPEBytesTokensTriviaRestored':True,
 'fullAuditStdoutIndependentReconstruction':rest['fullAuditStdoutReconstruction'],
 'allInputsAndPayloadsHashBound':True,'independent':True,'neverAuthor':True,'sameReviewer':True,
 'sourceAccepted':True,'qualified':True,'kernelPending':False,'kernelChecked':True,'axiomAudited':True,'criticalGaps':[],
 'actualOwnerCountsDerived':counts,'actualTransitiveAxioms':ax,'reviewerOperations':OPS,'P168Readopted':False,
 'rootAndFullOQ56':'OPEN','unit249Implemented':False,
 'selfBinding':'This manifest is bound by lastzeroRELEASE; no self hash.',
 'nextExactDependency':qualified['nextExactDependency'],**MODEL}
save('MANIFEST.json',manifest)
for v in manifest['inputs']+manifest['payloads']+[manifest['activation']]:verify(v)
release={'schema':'oq56-unit248-SAMEindependent-qualified-final-review-FINALWRITE-sixzero-release-v1','atUTC':NOW(),
 'role':ROLE,'ownerChat':OWNER,'ownedRoot':OUT.as_posix(),'FINALWRITE':True,
 'status':'QUALIFIED_EXACT_SOURCE_FIRST_ORIGINAL_OBJECT_COMPLETE_INDEPENDENT_REVIEW_SEALED_RELEASED',
 'manifest':bind(OUT/'MANIFEST.json'),'qualifiedEvidence':bind(OUT/'qualified-evidence.json'),
 'source':a['source'],'sourceLF':3965,'firstOriginalObject':summary['object'],
 'inputCountDerived':101,'payloadCountDerivedExcludingManifestAndFinalRelease':len(payloads),'allInputsAndPayloadsHashBound':True,
 'writerReleased':True,'executionReleased':True,'publicationReleased':True,'childAuthorityReleased':True,
 'sixZero':{'writers':0,'heavyCommands':0,'inflightExecution':0,'pendingExternal':0,'children':0,'uncertainOperations':0},
 'sixZeroScope':'This SAME independent final-review role only; no additional lead/Root/server process observation claim.',
 'noFurtherWritesAfterThisRelease':True,'independent':True,'neverAuthor':True,'sameReviewer':True,
 'sourceAccepted':True,'qualified':True,'kernelPending':False,'kernelChecked':True,'axiomAudited':True,
 'completeCurrentTYPERequiredVALUEReading':True,'allTYPEBytesTokensTriviaRestored':True,'fullAuditStdoutRestoredExactly':True,
 'criticalGaps':[],'actualOwnerCountsDerived':counts,'allTransitiveAxioms':ax,
 'nativeActualRC':0,'auditActualRC':0,'nativeOuterRC':1,'auditOuterRC':1,'strictWrappersRemainFalse':True,
 'FIRSTEMPTYReturned':False,'P168Readopted':False,'reviewerOperations':OPS,'rootAndFullOQ56':'OPEN','unit249Implemented':False,
 'nextExactDependency':qualified['nextExactDependency'],**MODEL}
save('lastzeroRELEASE.json',release)
# FINALWRITE above. No filesystem writes below.
print(json.dumps({'SEALED':True,'qualified':True,'kernelPending':False,
 'MANIFEST':bind(OUT/'MANIFEST.json'),'FINALWRITE':bind(OUT/'lastzeroRELEASE.json'),
 'QUALIFIED_EVIDENCE':bind(OUT/'qualified-evidence.json'),'COVERAGE':bind(OUT/'COVERAGE.json'),'REPORT':bind(OUT/'fullreport.md'),
 'inputs':101,'payloads':len(payloads),'actualOwners':1,'TYPElines':14646,'TYPEbytes':2347133,
 'firstOriginalObject':summary['object'],'sixZero':release['sixZero']},ensure_ascii=False))
