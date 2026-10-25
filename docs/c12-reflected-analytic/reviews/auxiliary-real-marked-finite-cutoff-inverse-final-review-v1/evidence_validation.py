from pathlib import Path
import hashlib,json,sys,re
sys.dont_write_bytecode=True
r=Path(__file__).parent;w=Path('C:/game/shao lean');a=r.parent/'auxiliary-real-marked-finite-cutoff-inverse-v1'
def bind(p):
 p=Path(p);b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
rows=[];checks=[]
for folder in ['auxiliary-real-marked-moments-final-review-v1','auxiliary-unmarked-real-finite-cutoff-inverse-final-review-v1']:
 p=r.parent/folder/'parent-acceptance.json';q=json.loads(p.read_text());rows.append(bind(p))
 for fname,key in [('full-review.json','fullReviewJSONSHA256'),('full-review.md','fullReviewMDSHA256'),('RELEASE.json','reviewReleaseSHA256'),('validation.json','validationSHA256')]:
  row=bind(p.parent/fname);row['matchesQualifiedSHA256']=row['sha256']==q[key];rows.append(row);checks.append(row['matchesQualifiedSHA256'])
for file in ['common-suffix-moment-budgets-root-qualification.json','common-suffix-scalar-interfaces-root-qualification.json']:
 p=w/'coordination'/file;q=json.loads(p.read_text());rows.append(bind(p));review=q['fresh_complete_independent_report'];pairs=[(review['path'],review['sha256']),(q['qualifiedOwnerMap'],q['qualifiedOwnerMapSHA256'])]
 if 'JSON' in review:pairs.append((review['JSON'],review['JSON_sha256']))
 if 'structuredPath' in review:pairs.append((review['structuredPath'],review['structuredSHA256']))
 for rel,sha in pairs:
  row=bind(w/rel);row['matchesQualifiedSHA256']=row['sha256']==sha;rows.append(row);checks.append(row['matchesQualifiedSHA256'])
for p in [w/'coordination/handoffs/20261024/c12-ACTIVATION.json',w/'coordination/streamlined-acceptance-current.md',w/'SERVER.md']:
 rows.append(bind(p))
result={'status':'PASS' if all(checks) else 'FAIL','readOnlyEvidenceHashChecks':len(checks),'allPass':all(checks),'bindings':rows,'oldProofReReviews':0,'LeanReplays':0,'auditReplays':0}
(r/'qualified-evidence-bindings.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in result.items() if k!='bindings'}))
sys.path.insert(0,str(w/'tools'))
from transport_client import send_request
code=r'''from pathlib import Path
import hashlib,json,datetime,sys
sys.dont_write_bytecode=True
base=Path('/root/rivermind-data/shao-lean-20261021');wt=base/'workspaces/c12-bridge-domination-v71';out=base/'outputs/c12-auxiliary-real-marked-finite-cutoff-inverse-v71'
paths=[wt/'Shao/C2/AuxiliaryRealMarkedFiniteCutoffInverse.lean',wt/'.lake/build/lib/lean/Shao/C2/AuxiliaryRealMarkedFiniteCutoffInverse.olean',out/'AuxiliaryRealMarkedFiniteCutoffInverse.olean',out/'receipt.json',out/'frozen.lean.txt',out/'actual-owned-types.txt',out/'owned-audit.json',out/'attempt002/exit.json',out/'audit-exit.json',base/'outputs/common-suffix-moment-budgets-v73/producer39.olean',base/'workspaces/common-suffix-scalar-interfaces-v88/.lake/build/lib/lean/Shao/Probability/SourceSuffixScalarInterfaces.olean']
rows=[]
for p in paths:
 b=p.read_bytes();rows.append({'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
print(json.dumps({'observedUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'bindings':rows,'readOnly':True,'LeanCommands':0,'auditCommands':0}))
'''
v=send_request({'action':'exec','command':'taskset -c 14-17 python -','stdin':code,'timeout':60})
if v.get('exit_code')!=0:
 (r/'final-binding-observation-failure.json').write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf-8');print(json.dumps(v));raise SystemExit(1)
fresh=json.loads(v['stdout']);(r/'final-remote-observations.json').write_text(json.dumps(fresh,ensure_ascii=False,indent=2)+'\n',encoding='utf-8');print(json.dumps({'finalRemoteBindings':len(fresh['bindings']),'observedUTC':fresh['observedUTC']}))
