import json,hashlib,re
from pathlib import Path
r=Path(__file__).parent;w=Path('C:/game/shao lean');a=w/'drafts/c12-lane/auxiliary-real-marked-finite-cutoff-inverse-v1'
def binding(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}
rows=[binding(p) for p in sorted(a.iterdir()) if p.is_file()]
receipt=json.loads((a/'receipt.json').read_text());matches=[]
for row in rows:
 p=Path(row['path']);exp=receipt['artifacts'].get(p.name)
 if exp:matches.append({'file':p.name,'match':row['sha256']==exp['sha256'] and row['bytes']==exp['bytes']})
slices=[]
for q in json.loads((a/'consumed-interface-bindings.json').read_text())['interfaces']:
 p=Path(q['path']);data=p.read_bytes();export=binding(p);sl=data[q['offset']:q['offset']+q['bytes']];out=(a/q['file']).read_bytes();slices.append({'name':q['name'],'sourceExport':export,'offset':q['offset'],'bytes':len(sl),'sliceSHA256':hashlib.sha256(sl).hexdigest(),'exportHashMatch':export['sha256']==q['sourceExportSHA256'],'sliceHashMatch':hashlib.sha256(sl).hexdigest()==q['sliceSHA256'],'localCopyExact':sl==out})
quals=[w/'drafts/c12-lane/auxiliary-real-marked-moments-final-review-v1/parent-acceptance.json',w/'drafts/c12-lane/auxiliary-unmarked-real-finite-cutoff-inverse-final-review-v1/parent-acceptance.json',w/'coordination/common-suffix-moment-budgets-root-qualification.json',w/'coordination/common-suffix-scalar-interfaces-root-qualification.json']
qualrows=[]
for p in quals:
 if not p.exists():
  hits=list((w/'coordination').rglob(p.name));p=hits[0] if len(hits)==1 else p
 q=json.loads(p.read_text());row=binding(p);row['qualification']=q;qualrows.append(row)
root=w/'drafts/c2-residual-rare-suffix-production/private-helper-heads-request01.lean.txt';rows.append(binding(root))
s=(a/'AuxiliaryRealMarkedFiniteCutoffInverse.lean').read_text();heads=re.sub(r'(?ms)(:= by\n).*?(?=\n(?:private theorem|theorem|end Shao))',r'\1',s)
freeze=(a/'frozen.lean.txt').read_text();result={'authorFiles':rows,'receiptArtifactComparisons':matches,'allReceiptArtifactComparisonsPass':all(x['match'] for x in matches),'consumedSlices':slices,'qualificationBindings':qualrows,'currentHeadsExactlyFrozen':heads==freeze,'sourceLines':len(s.splitlines())}
(r/'local-bindings.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('LOCAL_BINDINGS',json.dumps({'files':len(rows),'receiptMatches':len(matches),'allPass':result['allReceiptArtifactComparisonsPass'],'sliceBindings':slices,'currentHeadsExactlyFrozen':heads==freeze,'qualifications':[{'path':q['path'],'sha256':q['sha256'],'keys':list(q['qualification'])} for q in qualrows],'rootHeads':rows[-1]},ensure_ascii=False))
reg=json.loads((w/'coordination/REGISTRY.json').read_text());print('REGISTRY_TOP',list(reg))
for k,v in reg.items():
 if k.lower() in ['lanes','owners','resourceleases','leases','coordinator','currentcoordinator']:
  if isinstance(v,dict):print(k,json.dumps({x:y for x,y in v.items() if 'c12' in x.lower() or 'root' in x.lower()},ensure_ascii=False))
  else:print(k,json.dumps(v,ensure_ascii=False)[:1800])
for row in qualrows:
 print('QUALIFIED_EVIDENCE',row['path']);print(json.dumps(row['qualification'],ensure_ascii=False,indent=2))
