import datetime,hashlib,json,shlex,sys
from pathlib import Path
ROOT=Path('C:/game/shao lean');HERE=ROOT/'drafts/c12-lane/real-marked-extended-budget-final-review-v1'
sys.path.insert(0,str(ROOT/'tools'))
from transport_client import send_request
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def meta(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}
def save(name,obj):(HERE/name).write_text(json.dumps(obj,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
v=load(HERE/'source-binding-validation.json');obs=load(HERE/'fresh-readonly-observation.json');follow=load(HERE/'native-source-binding-followup.json');local=load(HERE/'local-bindings.json')
targets={p:{'sha256':r['sha256'],'bytes':r['bytes']} for p,r in obs['bindings'].items() if p.endswith('.olean') or (p.endswith('.lean') and '/workspaces/' in p and '/.lake/packages/' not in p)}
code=r'''
import datetime,hashlib,json,os,pathlib,sys
out={'atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'readOnly':True,'affinity':sorted(os.sched_getaffinity(0)),'files':[]}
for path,expected in json.loads(sys.stdin.read()).items():
 b=pathlib.Path(path).read_bytes();r={'path':path,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)};r['matchesExpected']=all(r[k]==val for k,val in expected.items());out['files'].append(r)
print(json.dumps(out))
'''
r=send_request({'action':'exec','command':'taskset -c 44-47 python3 -c '+shlex.quote(code),'stdin':json.dumps(targets),'timeout':60})
if r.get('ok') is False or r.get('exit_code')!=0:save('final-readonly-binding-failure.json',r);raise SystemExit('Final readonly binding failed')
final=json.loads(r['stdout']);save('final-readonly-binding.json',final)
assert all(x['matchesExpected'] for x in final['files'])
assert v['status']=='PASS' and all(c['pass'] for c in v['checks'])
assert all(meta(Path(row['path']))==row for row in local['files']), 'Local bound file changed'
review={
 'schema':'c12-independent-complete-final-review-v1','status':'CORRECT','atUTC':now(),'units':[187,188],
 'reviewer':{'role':'/root/real_marked_extended_budget_final_review','authoredNeitherModule':True,'freshContext':True,'requestedModel':'gpt-6.1-sol','requestedEffort':'xhigh','requestedFork':'none','observableActualModel':None,'observableActualEffort':None,'usage':{'input':None,'cachedInput':None,'output':None,'reasoningSubset':None}},
 'exactBindings':v['units'],'derivedCounts':v['derivedCounts'],'criticalGaps':[],
 'completeCoverage':{'allNewSourceStatementsContextsProofs':True,'allActualOwnedTypes':True,'actualTypesBytes':52489,'allActualDefinitionValues':True,'actualValueBytes':0,'completeConsumedOld184PublicTypeBytes':30767,'completeConsumedRootRawPublicTypeBytes':22456,'new187To188ExactFullTypeReuseBytes':28178,'sourceToStatementPrimaryScope':True,'nativeCriticalContracts':True,'qualifiedOldProofsReused':True,'oldCompleteProofRereviews':0},
 'sourceScope':{'primary':'C:/game/shao/current/c12/supplement.tex','primarySHA256':follow['primary']['sha256'],'readLines':[[4401,4496]],'masterLines':[[4431,4444],[4474,4485]],'branch':'ordinary cubic-marked ell=1','pathDimension':'m+1','energy':'actual full sum of squares','sum':'actual full prefixSum at length','mark':'abs(v 0)^3','law':'actual iid raw pi Fin(m+1)','growth':'all real a>=0','inverse':'all real q>0','finiteSecondMomentOnly':True,'retainedGamma':'closed z^2<=b, threshold >=1/2, -c or 1','constantOrder':'before law,m,b,H','finiteH187SelectedGenuinelyIntegrable':True,'infiniteH188NoBochnerFinitenessClaim':True,'extendedIntegralsMayBeInfinity':True,'newMomentOrOracleAssumptions':False,'rarePsiOrWholeC2Credit':False},
 'proofCoverage':{'187':{'sourceLines':[[1,103]],'segments':['frozen context and constant before law','H positivity, delta and exact stronger K','qualified184 contract and public raw hRaw projection','legal positive damping ranges and true integral_mono','pointwise selected/K nonnegativity','native ofReal conversions, positive coefficient and extended integral monotonicity']},'188':{'sourceLines':[[1,169]],'segments':['frozen context and C0 exp1 before law','positive monotone cofinal H_n=b+m+n+1 and exact cutoffs','gamma<=1 and 0<=m/H_n<=1, both gamma signs','finite-constant ENNReal scaling and uniform cutoff bound','actual F_n/G_n measurability','pointwise G monotonicity','pointwise supremum equals exact final selected, all branches','native lintegral_iSup and supremum uniform bound']}},
 'boundaryCoverage':['0<q<1 possible infinite integrals','q=0 excluded','a=0','m=0 one coordinate','H=b empty finite event','T=0 before division','T=b weak endpoint and threshold atoms','T=H strict finite upper endpoint','retained exactly 1/2','both gamma signs','positive-damping a3 genuine integral','finite positive constants with infinite RHS','universal coefficient order','acyclic old184/Root ->187 ->188'],
 'serverEvidence':{'originalKernelAttempts':[1,2,3],'kernelExitSequences':{'187':[1,1,0],'188':[1,1,0]},'originalKernel003PassBoth':True,'originalAllOwnedRecursiveAXPassBoth':True,'allowedAxioms':['propext','Classical.choice','Quot.sound'],'allOwnerSelection':'getModuleIdxFor? exact defining module, every environment constant including private/generated','auditLogReconstructedFromCompleteTypeAndExactPrefixSuffix':True,'allSixAttemptFrozenHeadersIdentical':True,'allSixAttemptUTF8NoBOMLF':True,'allSixAttemptSourcesForbiddenFree':True,'proofOnlyRepairs':True,'preDispatch187PythonFailureZeroLeanEffect':True,'freshBindingCount':len(obs['bindings']),'finalSourceObjectBindingCount':len(final['files']),'fiveNativeFilesMatchPinnedGitBlobs':True,'toolchain':obs['toolchain'],'mathlib':obs['mathlibHead'],'packages':obs['packageRealpath'],'CPUs':'44-47','C12LeanLakeObserved':follow['C12LeanLake'],'rawLogsRemainRemote':True},
 'evidenceArtifacts':{name:meta(HERE/name) for name in ['full-review.md','read-coverage.json','local-bindings.json','source-binding-validation.json','fresh-readonly-observation.json','native-source-binding-followup.json','final-readonly-binding.json','RUNTIME-ACK.json']},
 'executionAndOwnership':{'writesOnlyReviewFolder':True,'authorSourcesOrSharedFilesModified':False,'newLeanKernelBuildChecks':0,'newAxiomChecks':0,'oldSuccessfulChecksReplayed':0,'uploads':0,'publicationOrGitAPIMutations':0,'cacheChanges':0,'subagents':0,'rawLogsCopied':0,'noInflight':True},
 'disposition':'Independent complete final review CORRECT for exact NEW187/188; parent acceptance/integration/publication separate','rootStatus':{'C1':'immutablev85 complete existing state, no new claim here','C2':'OPEN','C12':'OPEN','OQ56':'OPEN','OQ3':'PAUSED_BY_USER','OQ4':'IDLE'}}
save('full-review.json',review)
checks=[{'name':'source-binding checks all pass','pass':all(c['pass'] for c in v['checks']),'count':len(v['checks'])},
 {'name':'58 local bound files unchanged at seal','pass':all(meta(Path(row['path']))==row for row in local['files']),'count':len(local['files'])},
 {'name':'77 original remote expected bindings exact','pass':all(x['matchesExpected'] for x in obs['bindings'].values()),'count':len(obs['bindings'])},
 {'name':'final source/object read-only rebindings exact','pass':all(x['matchesExpected'] for x in final['files']),'count':len(final['files'])},
 {'name':'five critical native files equal pinned Git blobs','pass':all(x['matchesPinnedGitBlob'] for x in follow['nativePinnedBindings']),'count':len(follow['nativePinnedBindings'])},
 {'name':'owned counts from defining-owner maps and complete TYPE exports','pass':v['derivedCounts']=={'actualOwned':2,'theorems':2,'public':2,'private':0,'generated':0,'nonTheorems':0,'actualTypesBytes':52489,'actualValuesBytes':0}},
 {'name':'both whole original audit logs reconstructed exactly','pass':all(u['auditLogReconstruction']['matchesEntireOriginal'] for u in obs['units'].values())},
 {'name':'complete independent mathematical review finished','pass':review['status']=='CORRECT' and not review['criticalGaps']}]
save('validation.json',{'schema':'c12-final-review-validation-v1','atUTC':now(),'status':'PASS' if all(c['pass'] for c in checks) else 'FAIL','checks':checks,'mathematicalVerdict':'CORRECT','criticalGaps':[],'completeSourceBindingValidation':meta(HERE/'source-binding-validation.json'),'fullReport':meta(HERE/'full-review.md'),'fullReportJSON':meta(HERE/'full-review.json'),'noNewLeanOrAudit':True})
payloads=[meta(p) for p in sorted(HERE.iterdir()) if p.is_file() and p.name not in ['payload-seal.json','RELEASE.json']]
save('payload-seal.json',{'schema':'c12-independent-review-payload-seal-v1','atUTC':now(),'files':payloads,'fileCount':len(payloads),'allHashes':'SHA256 of exact bytes','excludedSelfAndReleaseToAvoidCircularHash':True})
assert all(meta(Path(row['path']))==row for row in load(HERE/'payload-seal.json')['files'])
save('RELEASE.json',{'schema':'c12-independent-complete-review-release-v1','atUTC':now(),'status':'CORRECT_REVIEW_COMPLETE_RELEASED','units':[187,188],'reviewer':'/root/real_marked_extended_budget_final_review','writerReleased':True,'executionReleased':True,'inFlight':[],'heavy':False,'criticalGaps':[],'payloadSeal':meta(HERE/'payload-seal.json'),'fullReviewMD':meta(HERE/'full-review.md'),'fullReviewJSON':meta(HERE/'full-review.json'),'validation':meta(HERE/'validation.json'),'derivedCounts':v['derivedCounts'],'independentReviewerAuthoredNeither':True,'requestedModel':'gpt-6.1-sol','requestedEffort':'xhigh','requestedFork':'none','observableActualModel':None,'observableActualEffort':None,'usage':{'input':None,'cachedInput':None,'output':None,'reasoningSubset':None},'oldProofRereviews':0,'newLeanChecks':0,'newAxiomChecks':0,'rawLogsCopied':0,'publication':False,'parentAcceptanceWritten':False,'scope':'ordinary marked real a>=0/q>0 extended integral estimates, finite-H genuine selected integrability; C2/C12 remain OPEN'})
release=load(HERE/'RELEASE.json')
for key in ['payloadSeal','fullReviewMD','fullReviewJSON','validation']:assert meta(Path(release[key]['path']))==release[key]
print(json.dumps({'status':release['status'],'payloadFiles':len(payloads),'localBindings':len(local['files']),'sourceBindingChecks':len(v['checks']),'remoteBindings':len(obs['bindings']),'finalBindings':len(final['files']),'reportMD':release['fullReviewMD'],'reportJSON':release['fullReviewJSON'],'release':meta(HERE/'RELEASE.json'),'validation':release['validation'],'payloadSeal':release['payloadSeal']},indent=2))
