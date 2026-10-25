import sys, json, pathlib
sys.dont_write_bytecode = True
sys.path.insert(0, 'C:/game/shao lean/tools')
from transport_client import send_request

mode = sys.argv[1]
remote = r'''
import pathlib, hashlib, json, re, subprocess, difflib
from datetime import datetime, timezone
base=pathlib.Path('/root/rivermind-data/shao-lean-20261021')
wt=base/'workspaces/c12-bridge-domination-v71'
out=base/'outputs/c12-auxiliary-unmarked-real-finite-cutoff-inverse-v71'
def bind(p):
 p=pathlib.Path(p); b=p.read_bytes(); return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def emit(label,p):
 p=pathlib.Path(p); print('\nFILE '+label+' '+str(p)); print(p.read_text(encoding='utf-8'))
'''
if mode == 'bindings':
    remote += r'''
receipt=json.loads((out/'receipt.json').read_text())
paths=[wt/'Shao/C2/AuxiliaryUnmarkedRealFiniteCutoffInverse.lean',wt/'.lake/build/lib/lean/Shao/C2/AuxiliaryUnmarkedRealFiniteCutoffInverse.olean',out/'AuxiliaryUnmarkedRealFiniteCutoffInverse.olean',out/'receipt.json']
paths += [pathlib.Path(v['remotePath']) for v in receipt['artifacts'].values()]
pre=json.loads((out/'preflight-observation.json').read_text())
paths += [pathlib.Path(p) for p in pre['bindings']]
paths += [base/'sources/current/c12/supplement.tex',wt/'lean-toolchain',wt/'lake-manifest.json']
mathlib=(wt/'.lake/packages/mathlib').resolve()
git=lambda *args: subprocess.check_output(['git','-C',str(wt),*args],text=True).strip()
obj={ 'atUTC':datetime.now(timezone.utc).isoformat(), 'branch':git('branch','--show-current'), 'head':git('rev-parse','HEAD'), 'tree':git('rev-parse','HEAD^{tree}'), 'mathlibPath':str(mathlib), 'mathlibHEAD':subprocess.check_output(['git','-C',str(mathlib),'rev-parse','HEAD'],text=True).strip(), 'bindings':[bind(p) for p in dict.fromkeys(paths)] }
for section in ['artifacts']:
 for name,v in receipt[section].items():
  got=bind(v['remotePath']); assert got['sha256']==v['sha256'] and got['bytes']==v['bytes'],name
for p,v in pre['bindings'].items():
 got=bind(p); assert got['sha256']==v['sha256'] and got['bytes']==v['bytes'],p
audit=json.loads((out/'owned-audit.json').read_text())
types=(out/'actual-owned-types.txt').read_bytes(); log=(out/'owned-audit.log').read_bytes()
at=log.find(b'TARGET_DECL '); end=at+len(types)
assert log[at:end]==types
obj['auditReconstruction']={'prefix':log[:at].decode(),'payloadSHA256':hashlib.sha256(types).hexdigest(),'payloadBytes':len(types),'suffix':log[end:].decode(),'roundTrip':log[:at]+types+log[end:]==log}
decls=[x for x in audit['module_owned_constants']]
obj['derivedCounts']={'owned':len(decls),'theorems':sum(x['kind']=='theorem' for x in decls),'nonTheorems':sum(x['kind']!='theorem' for x in decls),'private':sum(x['name'].startswith('_private.') for x in decls),'public':sum(not x['name'].startswith('_private.') for x in decls),'valuesBytes':(out/'actual-definition-values.txt').stat().st_size,'actualTypesBytes':len(types)}
obj['ownerRecords']=decls
frozen=(out/'frozen.lean.txt').read_bytes()
pattern=rb'(?ms)^(?:private )?theorem\s+.*? := by\n'
heads=[]
for p in [wt/'Shao/C2/AuxiliaryUnmarkedRealFiniteCutoffInverse.lean',out/'attempt001/source.lean',out/'attempt002/source.lean']:
 b=p.read_bytes(); matches=list(re.finditer(pattern,b)); reconstructed=b[:matches[0].start()]+b'\n'.join(m.group(0) for m in matches)+b'\nend Shao.C2.AuxiliaryUnmarkedRealFiniteCutoffInverse\n'
 heads.append({'path':str(p),'count':len(matches),'headers':[hashlib.sha256(m.group(0)).hexdigest() for m in matches],'reconstructedSHA256':hashlib.sha256(reconstructed).hexdigest(),'freezeExact':reconstructed==frozen,'utf8NoBOM':not b.startswith(b'\xef\xbb\xbf'),'CRcount':b.count(b'\r'),'forbidden':re.findall(rb'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',b)})
obj['headIdentity']=heads
obj['scalarSourceAbsentC12']=not (wt/'Shao/Probability/SourceSuffixScalarInterfaces.lean').exists()
print(json.dumps(obj,ensure_ascii=False,indent=2))
'''
elif mode == 'evidence':
    remote += r'''
for name in ['attempt001/command.txt','attempt001/exit.json','attempt001/kernel.log','attempt002/command.txt','attempt002/exit.json','attempt002/kernel.log','audit-command.txt','audit-exit.json']:
 emit(name,out/name)
a=(out/'attempt001/source.lean').read_text(); b=(out/'attempt002/source.lean').read_text()
print('\nCOMPLETE_PROOF_DELTA'); print(''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True),fromfile='attempt001',tofile='attempt002')))
source=(base/'sources/current/c12/supplement.tex').read_text().splitlines()
print('\nSOURCE_EXCERPTS')
for lo,hi in [(4410,4455),(4470,4489)]:
 print('\n'+ '\n'.join(f'{i+1}: {source[i]}' for i in range(lo-1,hi)))
'''
elif mode == 'native-index':
    remote += r'''
mathlib=(wt/'.lake/packages/mathlib').resolve()
patterns=r'(theorem|lemma|def) (integrable_prod_iff|integral_integral_swap|integral_prod_(left|right)|integral_const_mul|rpow_(add|div_two_eq_sqrt|le_rpow_of_nonpos|neg|nonneg|pos_of_pos|le_rpow)|div_rpow|mul_rpow|one_div_le_one_div_of_le|div_le_one|exp_le_exp|exp_add)|integral_prod_right\x27'
for folder in ['Mathlib/MeasureTheory/Integral','Mathlib/Analysis/SpecialFunctions/Pow','Mathlib/Algebra/Order/Field','Mathlib/Analysis/SpecialFunctions/Exp.lean']:
 p=mathlib/folder
 for f in ([p] if p.is_file() else p.rglob('*.lean')):
  for i,line in enumerate(f.read_text().splitlines()):
   if re.search(patterns,line): print(f'{f.relative_to(mathlib)}:{i+1}:{line}')
for path,patterns2 in [('Shao/Basic/FinitePath.lean',r'^(abbrev Path|def prefixSum|def energy)'),('Shao/Probability/MeasurablePath.lean',r'^(theorem measurable_(energy|prefixSum))')]:
 lines=(wt/path).read_text().splitlines()
 print('\nPROJECT_CONTRACTS '+path)
 for i,line in enumerate(lines):
  if re.search(patterns2,line): print('\n'.join(f'{j+1}: {lines[j]}' for j in range(max(0,i-2),min(len(lines),i+10))))
'''
elif mode.startswith('native-details'):
    group = mode[-1]
    remote += r'''
mathlib=(wt/'.lake/packages/mathlib').resolve()
pin='807d3836b165983210ee2ecf3cd28f239436949c'
groups={
'1':{'Mathlib/MeasureTheory/Integral/Prod.lean':[(35,95),(130,158),(195,246),(275,344),(467,490)],'Mathlib/MeasureTheory/Integral/Bochner/Basic.lean':[(266,301)]},
'2':{'Mathlib/Analysis/SpecialFunctions/Pow/Real.lean':[(25,40),(109,120),(155,170),(198,226),(250,265),(468,496),(541,573),(990,1005)],'Mathlib/Algebra/Order/Field/Basic.lean':[(20,76)]},
'3':{'Mathlib/MeasureTheory/Integral/Prod.lean':[(95,130),(158,195),(425,467)],'Mathlib/Analysis/Complex/Exponential.lean':[(196,215),(292,321)],'Mathlib/MeasureTheory/Integral/Bochner/Basic.lean':[(625,677)],'Mathlib/MeasureTheory/Function/SpecialFunctions/Basic.lean':[(125,154)],'Mathlib/MeasureTheory/Group/Arithmetic.lean':[(170,200)]},
'4':{'Mathlib/MeasureTheory/Function/L1Space/Integrable.lean':[(32,113)],'Mathlib/MeasureTheory/Integral/Bochner/Basic.lean':[(35,65),(240,260),(580,595)]},
'5':{'Mathlib/MeasureTheory/Integral/Bochner/Basic.lean':[(90,120),(235,243)]}}
bindings=[]
for path,ranges in groups[GROUP].items():
 p=mathlib/path; b=p.read_bytes(); canonical=subprocess.check_output(['git','-C',str(mathlib),'show',pin+':'+path]); assert b==canonical,path
 row=bind(p); row['pathAtPin']=path; row['identicalToPinnedBlob']=True; row['readRanges']=ranges; bindings.append(row)
 lines=b.decode().splitlines()
 for lo,hi in ranges:
  print('\nNATIVE '+path+f' {lo}-{hi}'); print('\n'.join(f'{i+1}: {lines[i]}' for i in range(lo-1,hi)))
print('\nBINDINGS_JSON '+json.dumps(bindings))
'''.replace('GROUP', repr(group))
elif mode == 'native-final-index':
    remote += r'''
mathlib=(wt/'.lake/packages/mathlib').resolve()
for pattern in [r'(theorem|lemma) (exp_le_exp|exp_add|integral_mono|integral_mono_ae|Integrable.mono\x27|Integrable.integral_prod_left|Integrable.integral_prod_right)',r'(theorem|lemma) (Measurable.pow_const|Measurable.sqrt|Measurable.rpow_const)']:
 result=subprocess.run(['git','-C',str(mathlib),'grep','-n','-E',pattern,'807d3836b165983210ee2ecf3cd28f239436949c','--','Mathlib'],text=True,encoding='utf-8',stdout=subprocess.PIPE)
 print(result.stdout)
'''
elif mode == 'last-index':
    remote += r'''
mathlib=(wt/'.lake/packages/mathlib').resolve()
for pattern in ["theorem Integrable.mono'", "lemma Integrable.mono'", "theorem mono'", "lemma mono'", 'def Integrable']:
 result=subprocess.run(['git','-C',str(mathlib),'grep','-n','-F',pattern,'807d3836b165983210ee2ecf3cd28f239436949c','--','Mathlib/MeasureTheory/Function'],text=True,encoding='utf-8',stdout=subprocess.PIPE)
 print(result.stdout)
print('\nTIMINGS '+json.dumps({p:str((out/p).stat().st_mtime_ns) for p in ['freeze-record.json','preflight-observation.json','attempt001/kernel.log','attempt002/kernel.log','receipt.json']}))
print('\nPINS '+(wt/'lean-toolchain').read_text()); manifest=json.loads((wt/'lake-manifest.json').read_text()); print(json.dumps([x for x in manifest['packages'] if x['name']=='mathlib']))
'''
else:
    raise SystemExit('Unknown mode')
result=send_request({'action':'exec','command':'taskset -c 14-17 python -','stdin':remote,'timeout':60})
if mode == 'bindings' and result.get('exit_code') == 0:
    payload=json.loads(result['stdout'])
    pathlib.Path(__file__).with_name('fresh-remote-bindings.json').write_text(json.dumps(payload,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'transportOK':True,'bindings':len(payload['bindings']),'head':payload['head'],'tree':payload['tree'],'mathlib':payload['mathlibHEAD'],'counts':payload['derivedCounts'],'auditReconstruction':payload['auditReconstruction'],'headIdentity':payload['headIdentity'],'scalarSourceAbsentC12':payload['scalarSourceAbsentC12']},ensure_ascii=False,indent=2))
else:
    if result.get('exit_code') == 0:
        if mode.startswith('native-details'):
            metadata=json.loads(result['stdout'].split('BINDINGS_JSON ',1)[1])
            pathlib.Path(__file__).with_name('native-contract-bindings-'+mode[-1]+'.json').write_text(json.dumps(metadata,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
        print(result['stdout'])
    else:
        print(json.dumps(result,ensure_ascii=False))
