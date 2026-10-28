from pathlib import Path
import json,hashlib,datetime,re

BASE=Path(r'C:/game/shao lean')
OUT=BASE/'drafts/oq56/unit248/source-review-01'
ACT=BASE/'drafts/oq56/unit248/source-review-activation-01/ACTIVATION.json'
def digest(raw):return hashlib.sha256(raw).hexdigest()
def bind(p):
    p=Path(p); raw=p.read_bytes()
    return {'path':str(p).replace('\\','/'),'sha256':digest(raw),'bytes':len(raw)}
def write(name,value):
    (OUT/name).write_text(json.dumps(value,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
assert not (OUT/'lastzeroRELEASE.json').exists(),'FINALWRITE already present; no further writes permitted'
a=json.loads(ACT.read_bytes())
assert bind(ACT)['sha256']=='8e24ea37cbb56297cac5eda2b578cbf49317b2f638ab140a3ef1cc004fe99f41'
for x in a['inputs']:assert bind(x['path'])==x,x['path']
author=json.loads((BASE/'drafts/oq56/unit248/author-01/ACTUAL-PROP-CONTEXTS.json').read_bytes())
inv=json.loads((OUT/'INDEPENDENT-INVENTORY.json').read_bytes())
ret=json.loads((OUT/'INDEPENDENT-RETENTION.json').read_bytes())
restore=json.loads((OUT/'TYPE247-INDEPENDENT-RESTORATION.json').read_bytes())
packet=json.loads((OUT/'SOURCE-LOSSLESS-DICTIONARY.json').read_bytes())
raw=Path(a['source']['path']).read_bytes(); s=raw.decode('utf-8')
assert bind(a['source']['path'])==a['source'] and raw.count(b'\n')==3962
assert raw[:3]!=b'\xef\xbb\xbf' and b'\r' not in raw and b'\t' not in raw
assert ''.join(x['leading']+packet['dictionary'][x['ref']]['text']+x['trailing']+x['ending'] for x in packet['main']).encode()==raw
assert len(packet['dictionary'])==853 and len(packet['main'])==3962
assert len((OUT/'SOURCE-MAIN-READ.txt').read_text(encoding='utf-8').splitlines())==124
assert inv['countsDerived']['publicOrdinary']==145 and len(inv['fullFacts'])==40
assert ret['universalClausesDerived']==71 and ret['paymentClausesDerived']==39 and ret['newPhysicalPackageClausesDerived']==8
release_author=json.loads(Path(a['authorFinalRelease']['path']).read_bytes())
assert release_author['FINALWRITE'] and all(v==0 for v in release_author['sixZero'].values())
for x in author['approvedInstances']:
    assert isinstance(x['type'],str) and isinstance(x['rhs'],str) and isinstance(x['scope'],str)
facts_by_name={x['name']:x for x in author['fullFrozenPropositions']+author['additionalPureLogicalPackages']}
fullfacts=[]
for row in inv['fullFacts']:
    f=facts_by_name[row['name']]
    fullfacts.append(dict(row,fullType=f['fullType'],scope=f.get('scope',f.get('kind')),contextId=f['contextId']))

coverage={
 'schema':'oq56-unit248-independent-complete-SOURCE-semantic-coverage-v1',
 'atUTC':now(),'reviewer':a['role'],'ownerChat':a['ownerChat'],'independent':True,'neverAuthor':True,
 'source':dict(a['source'],LF=3962,UTF8NoBOM=True,LFOnly=True),
 'completeSourceToStatementProofReview':True,'completeIndependentReview':True,
 'sourceAccepted':True,'qualified':False,'kernelPending':True,'kernelChecked':False,'axiomAudited':False,
 'sourceReading':{'coverage':'ALL source lines1-3962, no unread region',
  'method':'Every complete literal normalized-line dictionary entry and every ordered currentmain reference/indent read; complete exact byte/token/trivia restoration; duplicate literal source lines read once and reused without abstraction.',
  'dictionaryEntriesRead':853,'mainReadLinesRead':124,'originalLinesCovered':3962,
  'wholeByteRoundTrip':True,'wholeTokenAndTriviaRoundTrip':True,
  'packet':bind(OUT/'SOURCE-LOSSLESS-DICTIONARY.json'),
  'dictionaryRead':bind(OUT/'SOURCE-DICTIONARY-READ.txt'),'mainRead':bind(OUT/'SOURCE-MAIN-READ.txt')},
 'qualified247CompletePublicTYPE':dict(restore,dictionaryReadComplete318=True,currentMainReadComplete431=True,
   sourceProofsReReviewed=False),
 'originalSourcesReadComplete':['p51.md','p54.md'],
 'countsDerived':inv['countsDerived'],
 'publicOrdinaryCompleteTypeRHSScope':inv['publicOrdinary'],
 'optionalOrdinaryCompleteTypeRHSScope':author['approvedOptionalOrdinary'],
 'fullFrozenPropsAndAdditionalLogicalTypes':fullfacts,
 'completeContextLayers':author['completeUniqueContexts'],
 'approvedInstancesCompleteTypeRHSScope':author['approvedInstances'],
 'APIImplicitInstancesCompleteTypeRHSScope':author['APIImplicitInstances'],
 'executableInstanceCoordinates':{
  'selectedSpace':2061,'selectedCountableGeneration':2062,
  'originalSampleSpace':3524,'originalSampleProbability':{'declaration':3525,'rhs':3526},
  'typeLocalRestatementsNotExecuted':[765,766,1413,1414],
  'usedApprovedRowsDerived':7,'unusedApprovedRows':['augmentedProductSpace']},
 'retention':ret,
 'proofCoverage':[
  {'sourceLines':[745,749],'review':'Original16 introduction, sole222B qualified247 call before six globals; full public actual247 type read.'},
  {'sourceLines':[750,759],'review':'Literal r symmetry from hhsymm; rho nonnegative as sqrt.'},
  {'sourceLines':[760,2704],'review':'Entire typed hCg/hModel/hRetained247 packages; sole cg/m0 and dependent hm0/hcg; exact original μ0 trim and selected instances.'},
  {'sourceLines':[2705,3269],'review':'Whole same eventual payment package, Eventually.mono, same n/w/z and47 original lets; no new cutoff.'},
  {'sourceLines':[3270,3455],'review':'Whole current-z producer type and exact conditional externalSZ weighted-source-cost tail projection.'},
  {'sourceLines':[3456,3520],'review':'Complete exact eight-clause new physical package type, four literal public lets and explicit guard.'},
  {'sourceLines':[3521,3714],'review':'Isolated original sample instances; window1; Ktail nonnegative; COMPLETE same-fixed-n/w level1 producer type and call.'},
  {'sourceLines':[3715,3778],'review':'Samecg H1 measurable/payment1; full qualified220 specialized original-space type/call atn,z0,C0512; global physical/clip measurability and disagreement event.'},
  {'sourceLines':[3779,3801],'review':'Original197 deterministic geometry with all actualUpper/Rows premises; absdelta≤1/32 and lower≥−1/2; original-P finiteness.'},
  {'sourceLines':[3802,3868],'review':'Full guarded package; explicit1+rho≤sqrt n; original210 literal delta/denominator/zero branch; disagreement subset and probability payment.'},
  {'sourceLines':[3869,3909],'review':'Both closed symmetric differences for all real t; all four event measurabilities; original finite probability absolute comparisons and payment1.'},
  {'sourceLines':[3910,3920],'review':'Both real-order transfer inequalities at currentz; exact −payment_z−payment1 / +3payment_z+payment1; full eight-clause assembly.'},
  {'sourceLines':[3921,3962],'review':'All39 retained payment projections in order, new package and exact closing.'}],
 'bearingAPICompleteRead':[
  {'name':'bounded_remainder_small_window','qualifiedUnit':197,'sourceSHA256':'c0102fa13835fb22b01148e42d66cf8ff5704d682b9a6142eb508d7172d95cc9','fullTypeAndAmbientRead':True,'use':'same n,g,r,originalUpper,originalRows,Ktail,t0,y1; exact window and membership'},
  {'name':'literal_clippedCentered_comparison_on_projectionGood','qualifiedUnit':210,'sourceSHA256':'8d601a1496ca1a330fb7f96a2ff5cdab6f0d3b37c125a710735d9123c5be1f14','fullTypeAndAmbientRead':True,'use':'fixed512/rho/y1, explicit1+rho guard, original delta lower bound; literal zero branch'},
  {'name':'actual_normalized_compact_clipped_observables','qualifiedUnit':220,'sourceSHA256':'052fb7eb6bb1d17218bf47c6c4f5b6715561da68b022bdacf6835fee5d667103','fullTypeAndAmbientRead':True,'use':'originalOmega/mOmega/mu, same n, z0,C0512; complete output context and projections11/12'},
  {'name':'abs_measureReal_sub_le_measureReal_symmDiff','fullTypeAndAmbientRead':True,'use':'same original finite P, both null-measurable closed events; all real t'},
  {'name':'measureReal_mono','fullTypeAndAmbientRead':True,'use':'actual source side condition P(super-set)≠∞ explicitly supplied'},
  {'name':'measurableSet_eq_fun / MeasurableSet.compl / Measurable preimage / measurableSet_Ici / measurableSet_Iic / Measure.pi probability','fullTypeAndAmbientRead':True,'use':'original measurable/probability model and standard real instances'}],
 'qualifiedPriorEvidenceReused':{'unit247SourceSHA256':'6f64eb0d74346cf03f5eac8832cc39f377b0fb3ac50007200bdf11eefdc4ecaf','unit247FIRSTOSHA256':'e926c6395aab6d532d9024dbabeb630e1ede634c277ab0167df0dbaf934701ca','nativeActualRC':0,'sameFIRSTOAuditActualRC':0,'proofReReview':False,'checksReplayed':False},
 'scopeLimits':a['scopeLimits'],'criticalGaps':[],
 'machineLayer':{'current248Native':None,'current248FIRSTO':None,'current248ActualOwnedCount':None,
  'current248CompleteTYPES':None,'current248RequiredVALUES':None,'current248TransitiveAX':None,
  'sameReviewerLaterFinalJoinRequired':True,'allPending':True},
 'operations':{k:0 for k in ['Lean','lake','kernel','PP','AX','server','network','upload','Git','API','children']},
 'requestedModel':a['requestedModel'],'requestedEffort':a['requestedEffort'],
 'actualBackend':None,'actualModel':None,'actualEffort':None,
 'usage':{'input':None,'cachedInput':None,'output':None,'reasoningSubset':None}}
write('COVERAGE.json',coverage)
verdict={'schema':'oq56-unit248-independent-complete-SOURCE-verdict-v1','atUTC':now(),
 'STATUS':'CORRECT','verdict':'SOURCE_ACCEPTED_KERNEL_PENDING','source':a['source'],'sourceLF':3962,
 'reviewer':a['role'],'ownerChat':a['ownerChat'],'independent':True,'neverAuthor':True,
 'completeSourceToStatementProofReview':True,'completeIndependentReview':True,
 'sourceAccepted':True,'qualified':False,'kernelPending':True,'kernelChecked':False,'axiomAudited':False,
 'criticalGaps':[],'frozenDeclarationExact':True,'all145Public147OptionalTypeRHSScopeComplete':True,
 'all32FrozenAnd8LogicalTypesScopesProofsComplete':True,'all8Instances5APIContextsComplete':True,
 'retainedUniversal71Payment39AndNewPhysical8Verified':True,
 'qualified247CompletePublicTYPEReadAndRestored':True,
 'qualified247ProofAndChecksReusedWithoutReplay':True,'noNewHypothesesModelLawSelectorCutoff':True,
 'explicitStudentizerGuardRetained':True,'originalWeightedSourceCostBothWindowsExternalSZRetained':True,
 'scope':a['scope'],'scopeLimits':a['scopeLimits'],
 'nextExactDependency':'Lead first new native on exact dbe4 source; if successful SAME FIRSTO allactual TYPE/required VALUE/transitive AX, then SAME reviewer finaljoin under new activation.',
 'actualOwnedConstantCount':None,'operations':coverage['operations'],
 'requestedModel':a['requestedModel'],'requestedEffort':a['requestedEffort'],
 'actualBackend':None,'actualModel':None,'actualEffort':None,'usage':coverage['usage']}
write('verdict.json',verdict)
history=json.loads((OUT/'LOCAL-DIAGNOSTIC-HISTORY.json').read_bytes())
history['events'].append({'script':'verify_inventory.py','scriptSHA256':bind(OUT/'verify_inventory.py')['sha256'],
 'exitCode':0,'atUTC':now(),'result':'All145 public fulltype/RHS/scope/currentcoords and40 logical fulltype/source assertions pass after only local verifier expectation corrections. No source/math/Lean result changed.'})
write('LOCAL-DIAGNOSTIC-HISTORY.json',history)
checkpoint=json.loads((OUT/'CHECKPOINT.json').read_bytes())
checkpoint.update({'atUTC':now(),'actualState':'COMPLETE_SOURCE_REVIEW_PENDING_FINALWRITE_SEAL',
 'currentValidation':'All independent inventory/currentcoordinate/fulltype checks pass. Whole old247 type prefix and71/39 retained clauses plus8new clauses independently verified. Complete report/coverage/verdict written; no critical gap found.',
 'remaining':['Write MANIFEST and FINALWRITE sixzero release; then no later writes in this source directory.','Lead newnative/sameFIRSTO allactual evidence; SAME reviewer finaljoin under new activation.'],
 'sourceAccepted':True,'qualified':False,'kernelPending':True})
write('CHECKPOINT.json',checkpoint)

# All source-bound immutable inputs are checked again immediately before sealing.
for x in a['inputs']:assert bind(x['path'])==x,x['path']
support_paths=[BASE/'AGENTS.md',BASE/'SERVER.md',BASE/'coordination/TEAM.md',
 Path(r'C:/Users/UIO/.agents/skills/math-theorem/SKILL.md'),
 Path(r'C:/Users/UIO/.agents/skills/math-theorem/references/prompt-library.md'),
 Path(r'C:/Users/UIO/.agents/skills/math-theorem/references/openai-workflow.md'),
 Path(r'C:/Users/UIO/.agents/skills/math-theorem/references/lean-verification.md'),
 BASE/'drafts/oq56/unit247/final-review-01/type-packet.cjs',
 BASE/'drafts/oq56/unit248/source-review-capacity-interruption-01/OBSERVATION.json']
payloads=[bind(p) for p in sorted(OUT.iterdir()) if p.is_file() and p.name not in ['MANIFEST.json','lastzeroRELEASE.json']]
manifest={'schema':'oq56-unit248-independent-SOURCE-review-manifest-v1','atUTC':now(),'role':a['role'],
 'ownerChat':a['ownerChat'],'ownedRoot':a['ownedRoot'],'activation':bind(ACT),
 'source':a['source'],'sourceLF':3962,'inputs':a['inputs'],'inputCountDerived':len(a['inputs']),
 'additionalReadOnlySupportingInputs':[bind(p) for p in support_paths],
 'payloads':payloads,'payloadCountDerivedExcludingManifestAndFinalRelease':len(payloads),
 'allInputsAndPayloadsHashBound':True,'completeIndependentSourceReview':True,'sourceAccepted':True,
 'qualified':False,'kernelPending':True,'kernelChecked':False,'axiomAudited':False,
 'manifestSelfHashInFinalRelease':True,'finalReleaseWrittenLastAndNotCircularlyIncluded':True,
 'requestedModel':a['requestedModel'],'requestedEffort':a['requestedEffort'],
 'actualBackend':None,'actualModel':None,'actualEffort':None,'usage':coverage['usage']}
write('MANIFEST.json',manifest)
release={'schema':'oq56-unit248-independent-SOURCE-review-FINALWRITE-sixzero-release-v1','atUTC':now(),
 'role':a['role'],'ownerChat':a['ownerChat'],'ownedRoot':a['ownedRoot'],'FINALWRITE':True,
 'status':'COMPLETE_INDEPENDENT_SOURCE_ACCEPTED_KERNEL_PENDING_SEALED_RELEASED',
 'manifest':bind(OUT/'MANIFEST.json'),'source':a['source'],'sourceLF':3962,
 'inputCountDerived':len(a['inputs']),'payloadCountDerivedExcludingManifestAndFinalRelease':len(payloads),
 'allInputsAndPayloadsHashBound':True,'writerReleased':True,'executionReleased':True,
 'publicationReleased':True,'childAuthorityReleased':True,
 'sixZero':{'writers':0,'heavyCommands':0,'inflightExecution':0,'pendingExternal':0,'children':0,'uncertainOperations':0},
 'sixZeroScope':'This independent reviewer role only; no lead/Root/server process claim.',
 'noFurtherWritesAfterThisRelease':True,'independent':True,'neverAuthor':True,
 'completeSourceToStatementProofReview':True,'sourceAccepted':True,'qualified':False,
 'kernelPending':True,'kernelChecked':False,'axiomAudited':False,'criticalGaps':[],
 'operations':coverage['operations'],'nextExactDependency':verdict['nextExactDependency'],
 'requestedModel':a['requestedModel'],'requestedEffort':a['requestedEffort'],
 'actualBackend':None,'actualModel':None,'actualEffort':None,'usage':coverage['usage']}
# FINAL FILESYSTEM WRITE UNDER THIS SOURCE-REVIEW ACTIVATION.
write('lastzeroRELEASE.json',release)
print(json.dumps({'status':'SOURCE_ACCEPTED_KERNEL_PENDING','source':a['source'],
 'manifest':bind(OUT/'MANIFEST.json'),'finalRelease':bind(OUT/'lastzeroRELEASE.json'),
 'coverage':bind(OUT/'COVERAGE.json'),'verdict':bind(OUT/'verdict.json'),
 'fullreport':bind(OUT/'fullreport.md'),'payloadCount':len(payloads),'sixZero':release['sixZero']},ensure_ascii=False))
