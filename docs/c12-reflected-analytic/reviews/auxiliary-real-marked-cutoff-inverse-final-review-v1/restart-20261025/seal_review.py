import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,datetime,re
ROOT=Path('C:/game/shao lean')
R=ROOT/'drafts/c12-lane/auxiliary-real-marked-cutoff-inverse-final-review-v1'
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def digest(p):
    b=p.read_bytes();return {'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}
def put(name,obj):
    p=R/name
    with p.open('x',encoding='utf-8',newline='\n') as f:f.write(json.dumps(obj,ensure_ascii=False,indent=2)+'\n')
local=load(R/'local-binding-observation.json');remote=load(R/'remote-binding-observation.json')
qual=load(R/'qualification-binding-observation.json');native=load(R/'native-contract-observation.json')
units=[]
for number,tag,module in [(185,'cutoff-inverse','AuxiliaryRealMarkedCutoffInverse'),(186,'finite-cutoff-budget','AuxiliaryRealMarkedFiniteCutoffBudget')]:
    packet=ROOT/('drafts/c12-lane/auxiliary-real-marked-'+tag+'-v1')
    receipt=load(packet/'receipt.json');freeze=load(packet/'freeze-record.json');owner=load(packet/'owned-audit.json')
    source=packet/(module+'.lean');b=source.read_bytes();text=b.decode();types=(packet/'actual-owned-types.txt').read_bytes()
    starts=[m.start() for m in re.finditer(rb'^TARGET_DECL ',types,re.M)]+[len(types)]
    declarations=[]
    sourceNames=re.findall(r'^(private )?theorem (\S+)',text,re.M)
    for i,row in enumerate(owner['module_owned_constants']):
        block=types[starts[i]:starts[i+1]]
        n=row['name'];short=n.rsplit('.',1)[-1]
        declarations.append(dict(row,typeExportByteOffset=starts[i],typeExportBytes=len(block),
           typeExportSHA256=hashlib.sha256(block).hexdigest(),completeTypeRead=True,completeProofReviewed=True,
           sourceDeclarationMatched=short in [name for _,name in sourceNames],private=n.startswith('_private.')))
    counts={'actualOwnedConstants':len(declarations),'theorems':sum(x['kind']=='theorem' for x in declarations),
        'publicTheorems':sum(not x['private'] and x['kind']=='theorem' for x in declarations),
        'privateTheorems':sum(x['private'] and x['kind']=='theorem' for x in declarations),
        'generatedDeclarations':sum(not x['sourceDeclarationMatched'] for x in declarations),
        'nonTheorems':sum(x['kind']!='theorem' for x in declarations),'actualTypeBytes':len(types),
        'definitionValueBytes':(packet/'actual-definition-values.txt').stat().st_size}
    units.append({'unit':number,'module':receipt['module'],'status':'CORRECT',
       'source':dict(path=str(source),**digest(source),lines=len(text.splitlines())),
       'objectSHA256':receipt['objectSHA256'],'receipt':dict(path=str(packet/'receipt.json'),**digest(packet/'receipt.json')),
       'freeze':dict(path=str(packet/'frozen.lean.txt'),**digest(packet/'frozen.lean.txt'),record=freeze),
       'originalKernelAttempt':receipt['kernelAttempt'],'originalKernelExit':receipt['kernelExit'],
       'originalAuditExit':receipt['auditExit'],'ownedAuditBinding':digest(packet/'owned-audit.json'),
       'auditProgramBinding':digest(packet/'OwnedAudit.lean'),'actualTypeExport':digest(packet/'actual-owned-types.txt'),
       'actualDefinitionValues':digest(packet/'actual-definition-values.txt'),'derivedCounts':counts,'declarations':declarations,
       'allSourceContextProofsTypesValuesReviewed':True,'frozenAssumptionsPreserved':True,
       'consumedInterfaces':load(packet/'consumed-interface-bindings.json')['interfaces']})
combined={key:sum(u['derivedCounts'][key] for u in units) for key in units[0]['derivedCounts']}
combined['modules']=len(units)
report={'schema':'c12-combined-independent-complete-final-review-v1','atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'status':'CORRECT','units':units,'combinedDerivedCounts':combined,
 'reviewer':{'task':'/root/auxiliary_real_marked_cutoff_inverse_final_review','authorOfNeitherNewUnit':True,
    'sameCanonicalIndependentRoleResumed':True,'requestedModel':'gpt-6.1-sol','requestedEffort':'xhigh',
    'actualModel':None,'actualEffort':None,'usage':{'input':None,'cachedInput':None,'output':None,'reasoningSubset':None}},
 'governingBrief':digest(R/'brief.txt'),'resumptionAmendment':digest(R/'restart-20261025/resumption-amendment.md'),
 'originalPauseEvidencePreserved':True,'old185QualificationReused':False,'newBatchInteraction':{
    'from':185,'to':186,'completeIndependentReviewCovered':True,'consumedPublicTypeByteIdentical':True,
    'unit185DependsOn184':False,'unit185DependsOn186':False,'cycle':False,
    'unit186Consumes185For':'genuine unshifted q>=1 kernel integrability only',
    'unit186NumericCoefficientFrom':'qualified old184, chosen before law,m,b,H',
    'unit186StrongKernelCoarsening':'both actual a3 integrabilities supplied by qualified raw coordinate-factor contract; monotonicity with both kernel integrabilities'},
 'coverage':{'sourceLines':{str(u['unit']):[1,u['source']['lines']] for u in units},
    'actualOwnedTypeBytesFullyRead':combined['actualTypeBytes'],'allFourProofsReviewed':True,
    'allActualOwnedNamesReviewed':True,'allPrivateGeneratedAndNonTheoremCoverageOwnerDerived':True,
    'consumedDistinctOldTypeBytesFullyRead':108446,'new185PublicTypeBytesReusedAfterExactSliceValidation':28859,
    'allSixConsumedSlicesBound':True,'sourceSupplementSHA256':'b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd',
    'sourceSupplementLinesFullyRead':[[4360,4485]],'completeSourceSemanticsReviewed':True,
    'nativeContractsFullyCheckedAtBearingUseSites':True,'allFourCriticalNativeFilesByteIdenticalToPin':True,
    'successfulOriginalKernelLogsFullyRead':True,'failed185Attempt001LogAndExactDiffRead':True,
    'fullOriginalAuditLogsLosslesslyReadViaExactPayloadFraming':True,'rawLogsCopiedIntoWorkspace':False},
 'mathematicalScope':{'growth':'all real a>=0','inverseOrder':'all real q>=1 explicitly','moments':'finite second moment only; mean0 and second moment1',
    'law':'actual pi measure on Fin(m+1)','mark':'abs(v0)^3','energy':'actual sum of all coordinate squares','sum':'actual full coordinate sum',
    'targetIntegrability':True,'actualKernelIntegrability':True,'universalNumericCoefficient':True,
    'unit185UpperCutoff':'infinity','unit186UpperCutoff':'finite H>=b>0; selected T<H; exact a3(s/2) coarse kernel',
    'qBelow1Claimed':False,'rootClosureClaimed':False,'noveltyClaimed':False},
 'qualifiedOldEvidence':local['oldQualifications'],'qualifiedRootContracts':qual['qualifiedContracts'],
 'evidenceFiles':{name:digest(R/name) for name in ['full-review.md','local-binding-observation.json','remote-binding-observation.json',
     'qualification-binding-observation.json','native-contract-observation.json','contract-completion-observation.json','native-tail-observation.json']},
 'originalServerEvidence':{'toolchain':remote['toolchain'],'mathlib':remote['mathlib'],'packages':remote['packages'],
    'worktreeGit':remote['git'],'bindingCount':len(remote['bindings']),'wholeOwnerAxiomWhitelist':['propext','Classical.choice','Quot.sound'],
    'allOwnedRecursiveAxiomChecksPASS':True,'newLeanRuns':0,'newAuditRuns':0,'allOldProofReReviews':0,
    'originalSuccessfulReceiptsReused':True,'archiveCurrentImportObjectsIdentical':True},
 'boundaryAttacksPassed':['q=1/e=0','a=0/zero full sum','m=0 one coordinate','atomic laws/zero atoms','zero energy false selector',
    's=0 excluded before rpow identities','b=T included','T=H excluded','H=b empty selector','retained=1/2 negative branch','both gamma signs','universal C quantifier order'],
 'criticalGaps':[],'newHeavyEvidenceNeeded':False,'noParentAcceptanceWritten':True,
 'originalScopeStatus':{'C1':'COMPLETE_IMMUTABLE_V85','C2':'OPEN','C12':'OPEN','OQ56':'OPEN','OQ3':'PAUSED_BY_USER'},
 'readOnlyObservationFailures':{'attempt001':'rg absent; failed script and failure JSON preserved; no remote writes',
    'responseShapeCorrection':'successful second observation initially printed transport envelope; local handler corrected and fresh readonly snapshot saved; no proof gate replay'}}
put('full-review.json',report)

# Deterministic evidence validation; this does not invoke Lean or another mathematical checker.
checks={}
for p,expected in local['bindings'].items():checks['local '+p]=digest(Path(p))==expected
for p,expected in qual['bindings'].items():checks['qualification '+p]=digest(Path(p))==expected
checks['qualification observation all PASS']=qual['allPass']
checks['all old complete-review seals retained']=all(all(o['seals'].values()) for o in local['oldQualifications'])
checks['all consumed export and slices exact']=all(x['exportMatch'] and x['sliceMatch'] and x['exactSlice'] for x in local['consumedSlices'])
checks['all source freezes/format/forbidden tokens']=all(x['sourceMatchesReceipt'] and x['freezeMatchesReconstructed'] and x['noBOM'] and x['CRCount']==0 and not x['forbiddenTokens'] and x['receiptBindings'] for x in local['sourceChecks'])
checks['all current and archived sources consistent']=all(x['sourceEqualsArchive'] and x['sourceFreezeMatches'] and x['preflightBindingsMatch'] and all(x['receiptArtifactMatches'].values()) and all(y['reconstructedFreezeMatches'] and y['noBOM'] and y['CRCount']==0 for y in x['archiveFormatsAndFreezes']) for x in remote['units'])
for i,u in enumerate(remote['units']):
    frame=u['auditFraming'];packet=Path(units[i]['actualTypeExport'].get('path',units[i]['source']['path'])).parent
    payload=(packet/'actual-owned-types.txt').read_bytes()
    raw=frame['prefix'].encode()+payload+frame['suffix'].encode()
    checks['lossless full raw audit framing '+u['module']]=(len(raw)==frame['rawBinding']['bytes'] and hashlib.sha256(raw).hexdigest()==frame['rawBinding']['sha256'] and frame['exactPayloadContiguousAfterInfoPrefixRemoval'] and frame['removedInfoPrefixes']==[])
checks['whole owner names exact; no elision']=all(c['typeNamesEqual'] and c['noEllipsis'] for c in local['derivedCounts'])
checks['actual owned/source declarations complete']=all(d['sourceDeclarationMatched'] for u in units for d in u['declarations'])
checks['all actual axioms whitelisted']=all(set(d['axioms'])<=set(['propext','Classical.choice','Quot.sound']) for u in units for d in u['declarations'])
checks['combined counts exact']=combined=={'actualOwnedConstants':4,'theorems':4,'publicTheorems':2,'privateTheorems':2,'generatedDeclarations':0,'nonTheorems':0,'actualTypeBytes':98094,'definitionValueBytes':0,'modules':2}
checks['native critical files match pin']=all(x['byteIdenticalToPin'] for x in native['nativePinChecks'])
checks['no C12 Lean/lake observed']=load(R/'contract-completion-observation.json')['c12LeanLakeProcesses']==[]
pause=load(R/'USER-PAUSE-RELEASE.json')
checks['original pause sealed bytes preserved']=all(digest(R/n)==v for n,v in pause['payloads'].items())
checks['185 and186 author releases zero inFlight']=all(load(ROOT/('drafts/c12-lane/auxiliary-real-marked-'+tag+'-v1/RELEASE.json'))['inFlight']==[] for tag in ['cutoff-inverse','finite-cutoff-budget'])
checks['full review JSON and MD exist']=bool((R/'full-review.md').stat().st_size and (R/'full-review.json').stat().st_size)
validation={'schema':'c12-combined-review-validation-v1','atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'status':'PASS' if all(checks.values()) else 'FAIL','checkCount':len(checks),'checks':checks,
    'localBoundFileCount':len(local['bindings']),'remoteBoundFileCount':len(remote['bindings']),
    'qualificationCheckCount':len(qual['checks']),'reviewMD':digest(R/'full-review.md'),'reviewJSON':digest(R/'full-review.json'),
    'inFlight':[],'heavy':False,'noLeanOrAxiomReplay':True}
put('validation.json',validation)
assert validation['status']=='PASS',[k for k,v in checks.items() if not v]
payloads={str(p.relative_to(R)).replace('\\','/'):digest(p) for p in sorted(R.rglob('*')) if p.is_file() and p.name not in ['RELEASE.json','seals.json']}
put('seals.json',{'schema':'c12-combined-review-payload-seals-v1','payloads':payloads,'payloadCount':len(payloads)})
put('RELEASE.json',{'schema':'c12-combined-final-independent-review-release-v1','atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'status':'COMPLETE_FINAL_REVIEW_CORRECT_RELEASED','units':[185,186],'verdict':'CORRECT','writerReleased':True,
 'executionReleased':True,'heavy':False,'heavyInFlight':False,'inFlight':[],'noSourceWrites':True,
 'newLeanRuns':0,'newAuditRuns':0,'subagents':0,'actualModel':None,'actualEffort':None,'requestedModel':'gpt-6.1-sol',
 'requestedEffort':'xhigh','usage':{'input':None,'cachedInput':None,'output':None,'reasoningSubset':None},
 'counts':combined,'seals':digest(R/'seals.json'),'fullReviewMD':digest(R/'full-review.md'),'fullReviewJSON':digest(R/'full-review.json'),
 'validation':digest(R/'validation.json'),'allReviewPayloadsHashBound':True,'parentQualificationAndPublicationPending':True})
print(json.dumps({'status':validation['status'],'checks':len(checks),'payloadCount':len(payloads),'release':digest(R/'RELEASE.json'),
   'fullReviewMD':digest(R/'full-review.md'),'fullReviewJSON':digest(R/'full-review.json'),'counts':combined},indent=2))
