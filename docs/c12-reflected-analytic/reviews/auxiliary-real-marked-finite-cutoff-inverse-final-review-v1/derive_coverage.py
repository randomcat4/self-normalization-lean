from pathlib import Path
import re,json,hashlib
r=Path(__file__).parent;a=r.parent/'auxiliary-real-marked-finite-cutoff-inverse-v1';t=(a/'actual-owned-types.txt').read_bytes();heads=list(re.finditer(rb'(?m)^TARGET_DECL ([^\n]+)',t));rows=[];owned=json.loads((a/'owned-audit.json').read_text())['module_owned_constants']
for i,h in enumerate(heads):
 z=heads[i+1].start() if i+1<len(heads) else len(t);chunk=t[h.start():z];name=h.group(1).decode().split(' KIND ')[0];rows.append({'name':name,'byteStart':h.start(),'byteEnd':z,'bytes':len(chunk),'sha256':hashlib.sha256(chunk).hexdigest(),'auditOwnerMapMatch':any(o['name']==name for o in owned)})
coverage={'ownedTypes':{'bytes':len(t),'chars':len(t.decode()),'rangesReadChars':[[0,22000],[22000,44000],[44000,66000],[66000,len(t.decode())]],'rows':rows,'exactOwnerNamesMatch':sorted(x['name'] for x in rows)==sorted(x['name'] for x in owned)},'consumedTypes':[]}
for file in ['consumed-real-marked-moment-complete-type.txt','consumed-unmarked-finite-cutoff-complete-type.txt','consumed-raw-coordinate-factors-complete-type.txt','consumed-inverse-laplace-complete-type.txt']:
 data=(a/file).read_bytes();coverage['consumedTypes'].append({'file':file,'bytes':len(data),'chars':len(data.decode()),'sha256':hashlib.sha256(data).hexdigest(),'fullRead':True})
coverage['counts']={'owned':len(owned),'theorems':sum(o['kind']=='theorem' for o in owned),'private':sum(o['name'].startswith('_private.') for o in owned),'public':sum(not o['name'].startswith('_private.') for o in owned),'nonTheorems':sum(o['kind']!='theorem' for o in owned),'generated':sum(o['kind']=='theorem' and not(o['name'].startswith('_private.') or o['name']=='Shao.C2.AuxiliaryRealMarkedFiniteCutoffInverse.auxiliary_actual_real_marked_finite_cutoff_inverse_moments') for o in owned),'valuesBytes':(a/'actual-definition-values.txt').stat().st_size}
(r/'read-coverage.json').write_text(json.dumps(coverage,indent=2)+'\n',encoding='utf-8');print(json.dumps(coverage,indent=2))
