from pathlib import Path
import json,hashlib,datetime

BASE=Path(r'C:/game/shao lean')
OUT=BASE/'drafts/oq56/unit248/source-review-repair-01'
AP=BASE/'drafts/oq56/unit248/affected-review-activation-01/ACTIVATION.json'
def sha(raw):return hashlib.sha256(raw).hexdigest()
def bind(p):
    p=Path(p);raw=p.read_bytes();return {'path':str(p).replace('\\','/'),'sha256':sha(raw),'bytes':len(raw)}
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def write(name,obj):(OUT/name).write_text(json.dumps(obj,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
assert not (OUT/'lastzeroRELEASE.json').exists(),'Already FINALWRITE sealed; no further writes.'
a=json.loads(AP.read_bytes());assert bind(AP)['sha256']=='6cac02270d58b4ef0fc93652822a091107cd8445ade77f7148938f1b3e3c5655'
for x in a['inputs']:assert bind(x['path'])==x,x['path']
v=json.loads((OUT/'INDEPENDENT-DELTA-VERIFICATION.json').read_bytes())
blocks=json.loads((OUT/'AFFECTED-BLOCKS.json').read_bytes())
ctx=json.loads((BASE/'drafts/oq56/unit248/author-repair-01/ACTUAL-PROP-CONTEXTS.json').read_bytes())
ar=json.loads(Path(a['authorRepairFinalRelease']['path']).read_bytes())
pr=json.loads(Path(a['priorSourceReviewFinalRelease']['path']).read_bytes())
assert ar['FINALWRITE'] and pr['FINALWRITE'] and pr['sourceAccepted']
assert all(x==0 for x in ar['sixZero'].values()) and all(x==0 for x in pr['sixZero'].values())
assert v['forward3PatchesWholeByteExact'] and v['reverse3PatchesWholeByteExact'] and v['noFourthSourceChange']
assert bind(a['source']['path'])==a['source'] and v['newSource']==a['source']
assert v['independentCoordinateChecksDerived']==353
am_path=BASE/'drafts/oq56/unit248/author-repair-01/MANIFEST.json';am=json.loads(am_path.read_bytes())
for x in am['inputs']+am['payloads']:assert bind(x['path'])==x
prior_refs={name:bind(BASE/'drafts/oq56/unit248/source-review-01'/name) for name in ['MANIFEST.json','lastzeroRELEASE.json','fullreport.md','COVERAGE.json','verdict.json']}
operations={k:0 for k in ['Lean','lake','kernel','PP','AX','server','network','upload','Git','API','children']}
usage={'input':None,'cachedInput':None,'output':None,'reasoningSubset':None}
full_affected=[]
for name in v['onlyTwoFrozenFullPropClarifications']:
    row=next(x for x in ctx['fullFrozenPropositions'] if x['name']==name)
    full_affected.append({k:row[k] for k in ['name','fullType','scope','contextId','actualBinding','obtainedFrom']})
coverage={
 'schema':'oq56-unit248-SAMEreviewer-complete-prior-plus-three-delta-affected-SOURCE-coverage-v1',
 'atUTC':now(),'role':a['role'],'ownerChat':a['ownerChat'],'independent':True,'neverAuthor':True,'sameReviewer':True,
 'source':dict(a['source'],LF=3964),'priorSource':v['oldSource'],
 'completeSourceToStatementProofReview':True,'coverageMethod':'EXACT_COMPLETE_PRIOR_SOURCE_PLUS_COMPLETE_AFFECTED_UNION',
 'completePriorSourceReviewReused':prior_refs,'oldReviewDirectoryFINALWRITEImmutable':True,
 'unaffectedSourceProofOr247TYPEOrHelperReReview':False,'oldChecksReplayed':False,
 'sourceAccepted':True,'qualified':False,'kernelPending':True,'kernelChecked':False,'axiomAudited':False,
 'wholeByteDeltaProof':v,'fullAffectedSourceBlocksAndCalls':blocks,'completeAffectedFullPropTypes':full_affected,
 'allUnchangedCoverage':{
  'publicOrdinary145FullTypeRHSScope':'Exact equality of full old/new145 records and entire public head. Complete prior semantic reading reused, not repeated.',
  'optionalOrdinary147':'Exact equality of all147 complete records including only samecg/m0 additional choices.',
  'approvedInstances8':{'exactFullRows':ctx['approvedInstances'],'semanticReviewReused':True},
  'APIImplicitContexts5':{'exactFullRows':ctx['APIImplicitInstances'],'semanticReviewReused':True},
  'sameModelChoices':'Full existing choice/context rows exact; no new data selector/model/law/cutoff.',
  'completeUniqueContexts11':'Every old/new full context row exact; complete prior scopes retained.',
  'frozenProps32':'All32 full types individually compared. Only hMeas220 original product and hPhysicalFinite explicit ENNReal.top differ; other30 and all scope fields exact.',
  'additionalLogicalPackages8':'All8 complete logical types and semantic fields exact; source coordinates independently rebased.',
  'retainedClauses':'Prior71universal/39payment/8physical complete source coverage unchanged through exact entire public-head equality.',
  'mathematicalScope':'Same247 cg/m0/mu0/nu/eta, originaln/rho/coefficients, bothwindows, fullweightedcost, externalSZ, explicitstudentizerguard, originalphysicalzerobranch, allrealclosedupper/lower, atom-safe eventpayment transfer unchanged.'},
 'affectedReadCoverage':[
  {'sourceLines':[2053,2062],'scope':'Same selected m0/hm0/hcg/mu0 and selected Ω/countable-generation instance installs; original Ω measurable-space remains separately named mΩ.'},
  {'sourceLines':[3267,3269],'scope':'Same fixedn/w/z, original47 let introduction; originalmN/P definitions inherited byteexact.'},
  {'sourceLines':[3521,3526],'scope':'Isolated original-sample mN and original-P probability instance; distinct from ambient selectedΩ m0.'},
  {'sourceLines':[3722,3769],'scope':'COMPLETE new hMeas220 full typedblock and complete explicit originalOmega/mOmega/mu/n/z0/C0512 call read. Sole product annotation changed.'},
  {'sourceLines':[3770,3778],'scope':'Immediate physical/clipped measurability projections and exact disagreement complement consumers; unchanged and reviewed in affected interaction context.'},
  {'sourceLines':[3799,3801],'scope':'COMPLETE new hPhysicalFinite type and unchanged originalP measure_ne_top proof; explicittop ENNReal.'},
  {'sourceLines':[3958,3964],'scope':'Proof ending plus newlyclosed anonymous section and unchanged named namespace end.'}],
 'native01DiagnosticBoundary':dict(v['native01Failure'],
  shortBlocksReadCompletely=[0,1,2,5],
  longBlockContextReadingRangesOneBasedInclusive={'3':[[1,28],[326,340],[634,650],[764,925]],'4':[[1,28],[326,340],[634,650],[805,901]]},
  allSixBlockIdentitiesVerified=True,unrelatedDuplicateGoalContextPreservedNotNewProofEvidence=True,
  allRemainingGoalsClaimedResolved=False,compilerRecoveryPlaceholdersNotAuthorSource=True,
  current248ActualTYPEorVALUEorAXEvidence=False),
 'authorRepairManifestInputAndPayloadVerification':{'manifest':bind(am_path),'inputsDerived':len(am['inputs']),'payloadsDerived':len(am['payloads']),'allExact':True},
 'criticalGaps':[],'noNewMathematicalPremiseModelLawSelectorInstanceWindowCostZeroAtomChange':True,
 'P168AlreadyAdoptedNative01NeverReadopt':True,'P168Readopted':False,
 'machineLayer':{'native02':None,'FIRSTOriginalObject':None,'actualOwnedCount':None,'completeActualTYPE':None,'requiredVALUE':None,'transitiveAX':None,'pending':True},
 'nextExactDependency':'Lead-only newnative02 on exact50fea source fromknownended/noO native01; ifsuccess SAMEFIRSTO allactualTYPE/requiredVALUE/transitiveAX then SAMEreviewer finaljoin undernewactivation.',
 'operations':operations,'requestedModel':a['requestedModel'],'requestedEffort':a['requestedEffort'],
 'actualBackend':None,'actualModel':None,'actualEffort':None,'usage':usage}
write('COVERAGE.json',coverage)
verdict={'schema':'oq56-unit248-SAMEreviewer-affected-source-union-verdict-v1','atUTC':now(),
 'STATUS':'CORRECT','verdict':'SOURCE_ACCEPTED_BY_EXACT_PRIOR_PLUS_AFFECTED_UNION_KERNEL_PENDING',
 'role':a['role'],'ownerChat':a['ownerChat'],'independent':True,'neverAuthor':True,'sameReviewer':True,
 'source':a['source'],'sourceLF':3964,'sourceAccepted':True,'qualified':False,'kernelPending':True,'kernelChecked':False,'axiomAudited':False,
 'completeSourceToStatementProofReview':True,'coverageMethod':coverage['coverageMethod'],
 'exactPriorCompleteSOURCEEvidenceReused':prior_refs,'oldSourceAndReviewImmutable':True,
 'forwardAndReverseThreePatchesWholeByteExact':True,'onlyThreeFrozenDeltas':True,'fullAffectedTypesContextsCallsProofsSectionClosureRead':True,
 'all145Public147Optional32Props8Logical8Instances5APIUnionCovered':True,
 'onlyTwoFrozenProofTypeClarifications':v['onlyTwoFrozenFullPropClarifications'],
 'criticalGaps':[],'native01ActualRC':1,'native01Object':None,'allRemainingGoalsProvedCascades':False,'newNativeRequired':True,
 'actualOwnedCount':None,'nextExactDependency':coverage['nextExactDependency'],'operations':operations,'P168Readopted':False,
 'requestedModel':a['requestedModel'],'requestedEffort':a['requestedEffort'],'actualBackend':None,'actualModel':None,'actualEffort':None,'usage':usage}
write('verdict.json',verdict)
cp=json.loads((OUT/'CHECKPOINT.json').read_bytes())
cp.update({'atUTC':now(),'actualState':'COMPLETE_AFFECTED_SOURCE_UNION_ACCEPTED_PENDING_FINALWRITE_SEAL',
 'sourceAccepted':True,'qualified':False,'kernelPending':True,
 'remaining':['Write M andFINALWRITE6zero R last; then no further writes underthisactivation.','Leadnative02/sameFIRSTO allactualmachineevidence then SAMEreviewer finaljoin.']})
write('CHECKPOINT.json',cp)
for x in a['inputs']:assert bind(x['path'])==x,x['path']
payloads=[bind(p) for p in sorted(OUT.iterdir()) if p.is_file() and p.name not in ['MANIFEST.json','lastzeroRELEASE.json']]
manifest={'schema':'oq56-unit248-SAMEreviewer-affected-review-manifest-v1','atUTC':now(),'role':a['role'],
 'ownerChat':a['ownerChat'],'ownedRoot':a['ownedRoot'],'activation':bind(AP),'source':a['source'],'sourceLF':3964,
 'inputs':a['inputs'],'inputCountDerived':len(a['inputs']),'payloads':payloads,'payloadCountDerivedExcludingManifestAndFinalRelease':len(payloads),
 'completePriorSOURCEPlusAffectedUnion':True,'priorCompleteSOURCEReview':prior_refs,
 'allInputsAndPayloadsHashBound':True,'sourceAccepted':True,'qualified':False,'kernelPending':True,'kernelChecked':False,'axiomAudited':False,
 'oldSourceReviewDirectoryImmutable':True,'onlyThreeFrozenSourceDeltas':True,'selfHashBoundInFinalRelease':True,
 'finalReleaseLastNotCircularlyIncluded':True,'requestedModel':a['requestedModel'],'requestedEffort':a['requestedEffort'],
 'actualBackend':None,'actualModel':None,'actualEffort':None,'usage':usage}
write('MANIFEST.json',manifest)
release={'schema':'oq56-unit248-SAMEindependent-affected-review-FINALWRITE-sixzero-release-v1','atUTC':now(),
 'role':a['role'],'ownerChat':a['ownerChat'],'ownedRoot':a['ownedRoot'],'FINALWRITE':True,
 'status':'COMPLETE_EXACT_PRIOR_PLUS_AFFECTED_SOURCE_ACCEPTED_KERNEL_PENDING_SEALED_RELEASED',
 'manifest':bind(OUT/'MANIFEST.json'),'source':a['source'],'sourceLF':3964,
 'inputCountDerived':len(a['inputs']),'payloadCountDerivedExcludingManifestAndFinalRelease':len(payloads),
 'allInputsAndPayloadsHashBound':True,'writerReleased':True,'executionReleased':True,'publicationReleased':True,'childAuthorityReleased':True,
 'sixZero':{'writers':0,'heavyCommands':0,'inflightExecution':0,'pendingExternal':0,'children':0,'uncertainOperations':0},
 'sixZeroScope':'This SAME independent affected-review role only, no lead/Root/server process claim.',
 'noFurtherWritesAfterThisRelease':True,'independent':True,'neverAuthor':True,'sameReviewer':True,
 'sourceAccepted':True,'qualified':False,'kernelPending':True,'kernelChecked':False,'axiomAudited':False,'criticalGaps':[],
 'completePriorSOURCEPlusAffectedUnion':True,'native01StillFailedNoObject':True,'allRemainingGoalsProvedCascades':False,
 'operations':operations,'P168Readopted':False,'nextExactDependency':coverage['nextExactDependency'],
 'requestedModel':a['requestedModel'],'requestedEffort':a['requestedEffort'],'actualBackend':None,'actualModel':None,'actualEffort':None,'usage':usage}
# FINAL DIRECTORY WRITE UNDER THIS ACTIVATION.
write('lastzeroRELEASE.json',release)
print(json.dumps({'verdict':verdict['verdict'],'source':a['source'],'sourceLF':3964,
 'manifest':bind(OUT/'MANIFEST.json'),'release':bind(OUT/'lastzeroRELEASE.json'),
 'report':bind(OUT/'fullreport.md'),'coverage':bind(OUT/'COVERAGE.json'),'verdictFile':bind(OUT/'verdict.json'),
 'payloadCount':len(payloads),'sixZero':release['sixZero']},ensure_ascii=False))
