"""Derive review coverage and source/evidence bindings without running Lean."""
import datetime,hashlib,json,re
from pathlib import Path
ROOT=Path('C:/game/shao lean');HERE=ROOT/'drafts/c12-lane/real-marked-extended-budget-final-review-v1'
packets={'187':ROOT/'drafts/c12-lane/auxiliary-real-marked-finite-cutoff-extended-budget-v1','188':ROOT/'drafts/c12-lane/auxiliary-real-marked-cutoff-extended-budget-v1'}
old=ROOT/'drafts/c12-lane/auxiliary-real-marked-finite-cutoff-inverse-final-review-v1'
oldpacket=ROOT/'drafts/c12-lane/auxiliary-real-marked-finite-cutoff-inverse-v1'
def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def met(p):
 b=p.read_bytes();return {'path':str(p),'sha256':sha(b),'bytes':len(b)}
files=set(p for folder in packets.values() for p in folder.iterdir() if p.is_file())
for name in ['parent-acceptance.json','full-review.md','full-review.json','RELEASE.json','validation.json','local-bindings.json','qualified-evidence-bindings.json']:
 files.add(old/name)
for name in ['receipt.json','AuxiliaryRealMarkedFiniteCutoffInverse.lean','actual-owned-types.txt']:
 files.add(oldpacket/name)
for name in ['common-suffix-moment-budgets-root-qualification.json','common-suffix-moment-budgets-qualified-owner-map.json','common-suffix-moment-budgets-full-review.md','common-suffix-moment-budgets-full-review.json']:
 files.add(ROOT/'coordination'/name)
for name in ['187-pre-dispatch-python-syntax-error-dispatch.json','187-pre-dispatch-python-syntax-error-response.json','187-pre-dispatch-no-lean-effect-check.json','187188-zero-heavy-boundary.json']:
 files.add(ROOT/'drafts/c12-lane/restart-20261025'/name)
files.update([ROOT/'drafts/c12-suffix-moment-budgets-production/all-owned-types.txt',ROOT/'drafts/c12-suffix-moment-budgets-production/SourceSuffixMomentBudgets.lean',ROOT/'library/Shao/Basic/FinitePath.lean',Path('C:/game/shao/current/c12/supplement.tex'),ROOT/'AGENTS.md',ROOT/'SERVER.md',ROOT/'coordination/streamlined-acceptance-current.md'])
rows=[met(p) for p in sorted(files)]
(HERE/'local-bindings.json').write_text(json.dumps({'atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':rows,'count':len(rows)},indent=2)+'\n',encoding='utf-8',newline='\n')
checks=[]
def check(name,ok,detail=None):checks.append({'name':name,'pass':bool(ok),'detail':detail})
coverage=[];units={}
for unit,folder in packets.items():
 r=load(folder/'receipt.json');audit=load(folder/'owned-audit.json');source=folder/(r['module'].split('.')[-1]+'.lean');b=source.read_bytes();text=b.decode('utf-8');frozen=(folder/'frozen.lean.txt').read_bytes()
 check(unit+' source',sha(b)==r['sourceSHA256']);check(unit+' receipt',sha((folder/'receipt.json').read_bytes())=={'187':'5cae7877257a20dbfe18356ae610049aa485fc0bc732385785ff399f69c2861b','188':'0c18a07c9e006245b6d32ad61452f838661264b9bf683b621df062e0e51c73c8'}[unit]);check(unit+' frozen',sha(frozen)==r['frozenSHA256'])
 check(unit+' exact head', (text.split(':= by',1)[0]+':= by\n\nend '+r['module']+'\n').encode()==frozen)
 before=folder/('source-before-kernel001.lean.txt' if unit=='187' else 'source-before-first-gate.lean.txt');beforetext=before.read_text(encoding='utf-8')
 check(unit+' preserved pre-gate draft exact frozen head',(beforetext.split(':= by',1)[0]+':= by\n\nend '+r['module']+'\n').encode()==frozen)
 check(unit+' UTF8NoBOMLF',not b.startswith(b'\xef\xbb\xbf') and b'\r' not in b)
 check(unit+' source forbidden free',not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',text))
 for name,a in r['artifacts'].items():
  p=folder/name
  if p.is_file():check(unit+' local artifact '+name,met(p)['sha256']==a['sha256'] and p.stat().st_size==a['bytes'])
 types=(folder/'actual-owned-types.txt').read_bytes();values=(folder/'actual-definition-values.txt').read_bytes()
 names=re.findall(r'^TARGET_DECL (\S+) KIND (\S+) AXIOMS',types.decode('utf-8'),flags=re.M)
 owned=audit['module_owned_constants'];check(unit+' types enumerate actual owner map',[(x['name'],x['kind']) for x in owned]==names)
 check(unit+' all owner rows target',all(x['owner']==r['module'] for x in owned));check(unit+' recursive AX whitelist',all(set(x['axioms'])<=set(r['whitelist']) for x in owned))
 check(unit+' values empty and no definitions',not values and not any(x['kind']!='theorem' for x in owned))
 public=[x['name'] for x in owned if x['kind']=='theorem' and '._private.' not in x['name'] and not x['name'].startswith('_private.')]
 units[unit]={'module':r['module'],'source':met(source),'receipt':met(folder/'receipt.json'),'frozen':met(folder/'frozen.lean.txt'),'objectSHA256':r['objectSHA256'],'ownedNames':[x['name'] for x in owned],'actualOwned':len(owned),'theorems':sum(x['kind']=='theorem' for x in owned),'public':len(public),'private':len(owned)-len(public),'generated':0,'nonTheorems':sum(x['kind']!='theorem' for x in owned),'actualTypes':met(folder/'actual-owned-types.txt'),'actualValues':met(folder/'actual-definition-values.txt')}
 for p in [source,folder/'actual-owned-types.txt',folder/'actual-definition-values.txt',folder/'frozen.lean.txt',folder/'OwnedAudit.lean']:
  coverage.append({**met(p),'read':'COMPLETE','lineCoverage':[[1,len(p.read_text(encoding='utf-8').splitlines())]] if p.stat().st_size else [],'byteCoverage':[[0,p.stat().st_size]],'purpose':'New complete proof/context or exact actual export/audit/freeze'})
op=load(old/'parent-acceptance.json');rootq=load(ROOT/'coordination/common-suffix-moment-budgets-root-qualification.json')
check('184 parent qualifier hash',sha((old/'parent-acceptance.json').read_bytes())=='0ce125c8f5e7127b6b5ef6c8f3b4d58abf6363f9bdd4f09f5670bcc4d8c0d457')
for name,key in [('full-review.md','fullReviewMDSHA256'),('full-review.json','fullReviewJSONSHA256'),('RELEASE.json','reviewReleaseSHA256'),('validation.json','validationSHA256')]:check('184 qualified '+name,sha((old/name).read_bytes())==op[key])
check('184 original source',met(oldpacket/'AuxiliaryRealMarkedFiniteCutoffInverse.lean')['sha256']==op['exactBindings']['184']['sourceSHA256']);check('184 original receipt',met(oldpacket/'receipt.json')['sha256']==op['exactBindings']['184']['receiptSHA256'])
check('Root qualification hash',sha((ROOT/'coordination/common-suffix-moment-budgets-root-qualification.json').read_bytes())=='3999793eb1e77bb679c4b8a5d7e1220392ed9ae01d09cc7f0064da14f6bce4f3')
for path,key in [(rootq['fresh_complete_independent_report']['path'],'sha256'),(rootq['fresh_complete_independent_report']['JSON'],'JSON_sha256')]:check('Root qualified report '+path,met(ROOT/path)['sha256']==rootq['fresh_complete_independent_report'][key])
check('Root owner-map qualified hash',met(ROOT/rootq['qualifiedOwnerMap'])['sha256']==rootq['qualifiedOwnerMapSHA256'])
check('Root original source',met(ROOT/rootq['local_source'])['sha256']==rootq['source_sha256'])
for name,src in [('consumed-qualified-strong-finite-cutoff-complete-type.txt',oldpacket/'actual-owned-types.txt'),('consumed-raw-coordinate-factors-complete-type.txt',ROOT/'drafts/c12-suffix-moment-budgets-production/all-owned-types.txt')]:
 p=packets['187']/name; b=p.read_bytes();check(name+' lossless complete slice',src.read_bytes().count(b)==1);coverage.append({**met(p),'read':'COMPLETE','lineCoverage':[[1,len(b.decode('utf-8').splitlines())]],'byteCoverage':[[0,len(b)]],'purpose':'Complete consumed already-qualified public contract; old proof evidence reused, no old proof rereview'})
p=packets['188']/'consumed-new-batch-finite-extended-complete-type.txt';check('188 consumes byte-identical 187 complete actual type',p.read_bytes()==(packets['187']/'actual-owned-types.txt').read_bytes());coverage.append({**met(p),'read':'REUSED_IDENTICAL_ALREADY_COMPLETELY_READ_NEW187_BYTES','byteCoverage':[[0,p.stat().st_size]]})
rootmap=load(ROOT/rootq['qualifiedOwnerMap']);rawrows=[r for r in rootmap['records'] if r.get('name')=='Shao.Probability.raw_gaussian_damped_coordinate_factors'];check('Root raw contract owner qualified',len(rawrows)==1,rawrows)
native=load(HERE/'native-source-binding-followup.json');check('primary local/remote exact binding',met(Path('C:/game/shao/current/c12/supplement.tex'))['sha256']==native['primary']['sha256']);check('Basic actual source agrees library',met(ROOT/'library/Shao/Basic/FinitePath.lean')['sha256']==native['projectContracts']['Shao/Basic/FinitePath.lean']['sha256'])
obs=load(HERE/'fresh-readonly-observation.json');check('77 fresh server bindings',len(obs['bindings'])==77 and all(r['matchesExpected'] for r in obs['bindings'].values()));check('native exact pinned git blobs',all(r['matchesPinnedGitBlob'] for r in native['nativePinnedBindings']));check('No current C12 Lean/lake',native['C12LeanLake']==[])
for unit,u in obs['units'].items():
 check(unit+' all three attempt headers/encoding/forbidden',all(a['frozenExact'] and a['UTF8NoBOMLF'] and not a['forbiddenTokens'] for a in u['attempts']));check(unit+' exact whole audit log reconstructed',u['auditLogReconstruction']['matchesEntireOriginal'] and u['typePayloadSingleOccurrence']);check(unit+' old failure/pass denominator',[a['exit']['kernelExit'] for a in u['attempts']]==[1,1,0]);check(unit+' original audit pass',u['auditExit']['auditExit']==0)
old184at=datetime.datetime.fromisoformat(op['atUTC']);freeze187=datetime.datetime.fromisoformat(load(packets['187']/'freeze-record.json')['atUTC']);check('184 qualified before new187 freeze',old184at<freeze187)
p187='/root/rivermind-data/shao-lean-20261021/outputs/c12-auxiliary-real-marked-finite-cutoff-extended-budget-v71/';p188='/root/rivermind-data/shao-lean-20261021/outputs/c12-auxiliary-real-marked-cutoff-extended-budget-v71/'
check('187 kernel and recursiveAX artifacts predate first188 source snapshot',obs['bindings'][p187+'kernel003-result.json']['mtimeNs']<obs['bindings'][p188+'attempt001/source.lean']['mtimeNs'] and obs['bindings'][p187+'audit-result.json']['mtimeNs']<obs['bindings'][p188+'attempt001/source.lean']['mtimeNs'])
check('All sources released',all(load(p/'RELEASE.json')['writerReleased'] and load(p/'RELEASE.json')['executionReleased'] and not load(p/'RELEASE.json')['inFlight'] for p in packets.values()))
totals={k:sum(u[k] for u in units.values()) for k in ['actualOwned','theorems','public','private','generated','nonTheorems']};totals['actualTypesBytes']=sum(u['actualTypes']['bytes'] for u in units.values());totals['actualValuesBytes']=sum(u['actualValues']['bytes'] for u in units.values())
validation={'atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS' if all(c['pass'] for c in checks) else 'FAIL','checks':checks,'units':units,'derivedCounts':totals,'independentReviewProofCoverage':'Complete new187 and188; qualified184 and Root proof evidence reused','oldCompleteProofRereviews':0,'newLeanChecks':0,'newAxiomChecks':0,'rawLogsCopied':0}
(HERE/'source-binding-validation.json').write_text(json.dumps(validation,indent=2)+'\n',encoding='utf-8',newline='\n')
(HERE/'read-coverage.json').write_text(json.dumps({'units':units,'coverage':coverage,'primaryReadLines':[[4401,4496]],'derivedCounts':totals,'actualDefinitionsZeroVerified':True},indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({'status':validation['status'],'localBoundFiles':len(rows),'checks':len(checks),'failed':[x for x in checks if not x['pass']],'counts':totals,'qualifiedRawRow':rawrows},indent=2))
