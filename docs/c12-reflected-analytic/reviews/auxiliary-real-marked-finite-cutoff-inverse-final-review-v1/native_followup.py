import sys,json,hashlib
from pathlib import Path
sys.dont_write_bytecode=True
sys.path.insert(0,'C:/game/shao lean/tools')
from transport_client import send_request
r=Path(__file__).parent
code=r'''import sys,json,hashlib,subprocess,re
from pathlib import Path
sys.dont_write_bytecode=True
base=Path('/root/rivermind-data/shao-lean-20261021');wt=base/'workspaces/c12-bridge-domination-v71';math=wt/'.lake/packages/mathlib';pin='807d3836b165983210ee2ecf3cd28f239436949c'
spec=[('Mathlib/MeasureTheory/Integral/Prod.lean',[(48,61),(100,101),(139,145),(225,242),(330,343),(465,490)]),('Mathlib/MeasureTheory/Function/L1Space/Integrable.lean',[(34,48),(104,106)]),('Mathlib/Analysis/SpecialFunctions/Pow/Real.lean',[(207,208),(258,263),(476,489),(998,1001)]),('Mathlib/Analysis/SpecialFunctions/Pow/Monotone.lean',[])]
rows=[];excerpts=[]
for rel,ranges in spec:
 p=math/rel
 if not p.exists():
  excerpts.append({'path':str(p),'missing':True});continue
 raw=p.read_bytes();old=subprocess.check_output(['git','-C',str(math),'show',pin+':'+rel]);rows.append({'path':str(p),'sha256':hashlib.sha256(raw).hexdigest(),'pinSHA256':hashlib.sha256(old).hexdigest(),'matchesPin':raw==old});lines=raw.decode().splitlines()
 if rel.endswith('Monotone.lean'):
  for i,line in enumerate(lines):
   if re.match(r'(?:theorem|lemma) rpow_le_rpow_of_nonpos\b',line):ranges.append((i+1,min(len(lines),i+12)))
 excerpts.extend({'path':str(p),'firstLine':a,'lastLine':b,'text':'\n'.join(f'{i+1}: {lines[i]}' for i in range(a-1,b))} for a,b in ranges)
core=Path('/root/.elan/toolchains/leanprover--lean4---v4.36.0-rc1/src/lean/Lean/Util/CollectAxioms.lean')
if core.exists():
 raw=core.read_bytes();rows.append({'path':str(core),'sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw)});excerpts.append({'path':str(core),'text':raw.decode()})
for rel,pattern in [('Shao/Basic/FinitePath.lean',r'^(?:abbrev Path|def prefixSum|def energy)\b'),('Shao/Probability/MeasurablePath.lean',r'^(?:theorem|lemma) measurable_(?:prefixSum|energy)\b')]:
 p=wt/rel;lines=p.read_text().splitlines()
 for i,line in enumerate(lines):
  if re.match(pattern,line):excerpts.append({'path':str(p),'firstLine':i+1,'text':'\n'.join(f'{j+1}: {lines[j]}' for j in range(max(0,i-2),min(len(lines),i+10)))})
# Original successful attempt chronology and exact exit records; all read-only.
out=base/'outputs/c12-auxiliary-real-marked-finite-cutoff-inverse-v71'
meta={n:{'mtimeNs':(out/n).stat().st_mtime_ns,'content':(out/n).read_text() if n.endswith('exit.json') else None} for n in ['freeze-record.json','attempt001/command.txt','attempt001/exit.json','attempt002/exit.json','audit-exit.json']}
print(json.dumps({'bindings':rows,'excerpts':excerpts,'originalGateMetadata':meta},ensure_ascii=False,indent=2))
'''
v=send_request({'action':'exec','command':'taskset -c 14-17 python -','stdin':code,'timeout':60})
if v.get('exit_code')!=0:
 (r/'native-followup-failure.json').write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf-8');print(json.dumps(v));raise SystemExit(1)
data=json.loads(v['stdout']);(r/'native-contract-targeted-observations.json').write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n',encoding='utf-8');print(v['stdout'])
