import sys, json, hashlib
from pathlib import Path
sys.dont_write_bytecode=True
sys.path.insert(0,'C:/game/shao lean/tools')
from transport_client import send_request
review=Path(__file__).parent
remote=r'''import sys,json,hashlib,subprocess,difflib,re
from pathlib import Path
sys.dont_write_bytecode=True
base=Path('/root/rivermind-data/shao-lean-20261021')
wt=base/'workspaces/c12-bridge-domination-v71'
out=base/'outputs/c12-auxiliary-real-marked-finite-cutoff-inverse-v71'
receipt=json.loads((out/'receipt.json').read_text())
def binding(p):
 p=Path(p); b=p.read_bytes(); return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
rows=[]
for name,expected in receipt['artifacts'].items():
 row=binding(expected['remotePath']);row['expectedMatch']=(row['sha256']==expected['sha256'] and row['bytes']==expected['bytes']);rows.append(row)
pre=json.loads((out/'preflight-observation.json').read_text())
for p,expected in pre['bindings'].items():
 row=binding(p);row['expectedMatch']=row['sha256']==expected['sha256'] and row['bytes']==expected['bytes'];rows.append(row)
for p in [out/'receipt.json',out/'AuxiliaryRealMarkedFiniteCutoffInverse.olean',wt/'Shao/C2/AuxiliaryRealMarkedFiniteCutoffInverse.lean',wt/'.lake/build/lib/lean/Shao/C2/AuxiliaryRealMarkedFiniteCutoffInverse.olean',base/'sources/current/c12/supplement.tex',wt/'lean-toolchain']:
 rows.append(binding(p))
git=lambda *args:subprocess.check_output(['git','-C',str(wt),*args],text=True).strip()
b=(out/'owned-audit.log').read_bytes();types=(out/'actual-owned-types.txt').read_bytes();pos=b.find(types);prefix=b[:pos];suffix=b[pos+len(types):]
source=(wt/'Shao/C2/AuxiliaryRealMarkedFiniteCutoffInverse.lean').read_bytes()
heads=lambda t: re.sub(r'(?ms)(:= by\n).*?(?=\n(?:private theorem|theorem|end Shao))',r'\1',t)
attempts=[(out/f'attempt00{i}/source.lean').read_text() for i in [1,2]]
result={'observedUTC':__import__('datetime').datetime.now(__import__('datetime').timezone.utc).isoformat(),'bindings':rows,'allExpectedMatch':all(r.get('expectedMatch',True) for r in rows),'branch':git('branch','--show-current'),'HEAD':git('rev-parse','HEAD'),'tree':git('rev-parse','HEAD^{tree}'),'status':git('status','--short'),'toolchain':(wt/'lean-toolchain').read_text().strip(),'packagesResolved':str((wt/'.lake/packages').resolve()),'auditFraming':{'prefixBytes':len(prefix),'prefix':prefix.decode(),'typesOffset':pos,'typesBytes':len(types),'typesSHA256':hashlib.sha256(types).hexdigest(),'suffixBytes':len(suffix),'suffix':suffix.decode(),'lossless':prefix+types+suffix==b,'wholeLogSHA256':hashlib.sha256(b).hexdigest()},'sourceFormat':{'UTF8':source.decode('utf-8') is not None,'BOM':source.startswith(b'\xef\xbb\xbf'),'CR':source.count(b'\r'),'LF':source.count(b'\n'),'forbiddenHits':re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',source.decode())},'allHeadsEqual':heads(attempts[0])==heads(attempts[1])==heads(source.decode())}
math=wt/'.lake/packages/mathlib';pin='807d3836b165983210ee2ecf3cd28f239436949c'
result['mathlibHead']=subprocess.check_output(['git','-C',str(math),'rev-parse','HEAD'],text=True).strip()
contracts={
'Mathlib/MeasureTheory/Integral/Prod.lean':['integrable_prod_iff','integral_prod_right','integral_integral_swap'],
'Mathlib/MeasureTheory/Function/L1Space/Integrable.lean':['theorem Integrable.mono\''],
'Mathlib/Analysis/SpecialFunctions/Pow/Real.lean':['theorem rpow_le_rpow_of_nonpos','theorem rpow_div_two_eq_sqrt','theorem rpow_add','theorem div_rpow','theorem rpow_neg']}
contractsout=[]; nativebindings=[]
for rel,terms in contracts.items():
 p=math/rel
 if not p.exists():
  contractsout.append({'path':rel,'missing':True});continue
 raw=p.read_bytes(); pinned=subprocess.check_output(['git','-C',str(math),'show',f'{pin}:{rel}']);nativebindings.append({'path':str(p),'sha256':hashlib.sha256(raw).hexdigest(),'pinSHA256':hashlib.sha256(pinned).hexdigest(),'matchesPin':raw==pinned})
 lines=raw.decode().splitlines()
 for term in terms:
  for i,line in enumerate(lines):
   if term in line:
    contractsout.append({'path':rel,'term':term,'startLine':max(1,i-4),'lines':'\n'.join(f'{j+1}: {lines[j]}' for j in range(max(0,i-5),min(len(lines),i+23)))})
result['nativeBindings']=nativebindings
print('OBSERVATION_JSON '+json.dumps(result,ensure_ascii=False))
print('KERNEL002_FULL\n'+(out/'attempt002/kernel.log').read_text())
print('FAILED001_COMMAND_EXIT\n'+(out/'attempt001/command.txt').read_text()+(out/'attempt001/exit.json').read_text())
print('FAILED001_FULL\n'+(out/'attempt001/kernel.log').read_text())
print('PROOF_DELTA_FULL\n'+''.join(difflib.unified_diff(attempts[0].splitlines(True),attempts[1].splitlines(True),fromfile='attempt001',tofile='attempt002')))
print('AUDIT_COMMAND_EXIT\n'+(out/'audit-command.txt').read_text()+(out/'audit-exit.json').read_text())
print('NATIVE_CONTRACTS\n'+json.dumps(contractsout,ensure_ascii=False,indent=2))
lines=(base/'sources/current/c12/supplement.tex').read_text().splitlines()
print('ORIGINAL_SOURCE\n'+'\n'.join(f'{i+1}: {lines[i]}' for a,z in [(4431,4444),(4474,4485)] for i in range(a-1,z)))
'''
request={'action':'exec','command':'taskset -c 14-17 python -','stdin':remote,'timeout':60}
res=send_request(request)
if not res.get('ok'):
 (review/'remote-observation-failure.json').write_text(json.dumps(res,indent=2)+'\n',encoding='utf-8'); print(json.dumps(res));raise SystemExit(1)
print(json.dumps(res,ensure_ascii=False))
stdout=res.get('stdout','')
if not stdout and isinstance(res.get('result'),dict):stdout=res['result'].get('stdout','')
for line in stdout.splitlines():
 if line.startswith('OBSERVATION_JSON '):
  (review/'remote-observations.json').write_text(json.dumps(json.loads(line[len('OBSERVATION_JSON '):]),ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
