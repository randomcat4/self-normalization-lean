import sys,json
from pathlib import Path
sys.dont_write_bytecode=True
sys.path.insert(0,'C:/game/shao lean/tools')
from transport_client import send_request
code=r'''import sys,json,re,hashlib,subprocess
from pathlib import Path
sys.dont_write_bytecode=True
base=Path('/root/rivermind-data/shao-lean-20261021');wt=base/'workspaces/c12-bridge-domination-v71';math=wt/'.lake/packages/mathlib';pin='807d3836b165983210ee2ecf3cd28f239436949c'
terms=['rpow_le_rpow_of_nonpos','integral_mono','integral_const_mul'];rows=[];ex=[];seen=set()
for directory in ['Mathlib/Analysis/SpecialFunctions/Pow','Mathlib/MeasureTheory/Integral/Bochner']:
 for p in sorted((math/directory).rglob('*.lean')):
  raw=p.read_bytes();lines=raw.decode().splitlines()
  for i,line in enumerate(lines):
   if any(re.match(r'(?:protected )?(?:theorem|lemma) '+re.escape(t)+r'(?:\s|\{)',line) for t in terms):
    if p not in seen:
     rel=str(p.relative_to(math));old=subprocess.check_output(['git','-C',str(math),'show',pin+':'+rel]);rows.append({'path':str(p),'sha256':hashlib.sha256(raw).hexdigest(),'pinSHA256':hashlib.sha256(old).hexdigest(),'matchesPin':raw==old});seen.add(p)
    ex.append({'path':str(p),'firstLine':i+1,'text':'\n'.join(f'{j+1}: {lines[j]}' for j in range(max(0,i-2),min(len(lines),i+12)))})
print(json.dumps({'bindings':rows,'excerpts':ex},ensure_ascii=False,indent=2))
'''
v=send_request({'action':'exec','command':'taskset -c 14-17 python -','stdin':code,'timeout':60})
if v.get('exit_code')!=0:print(json.dumps(v));raise SystemExit(1)
data=json.loads(v['stdout']);(Path(__file__).parent/'native-additional-contracts.json').write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n',encoding='utf-8');print(v['stdout'])
reg=json.loads(Path('C:/game/shao lean/coordination/REGISTRY.json').read_text());print('CURRENT_OWNER',json.dumps({'rootThread':reg.get('rootThread'),'model':reg.get('model'),'reasoning':reg.get('reasoning'),'c12':[x for x in reg.get('leads',[]) if 'c12' in str(x).lower()] if isinstance(reg.get('leads'),list) else {k:v for k,v in reg.get('leads',{}).items() if 'c12' in k.lower()}},ensure_ascii=False))
print('C12_ACTIVATION',Path('C:/game/shao lean/coordination/handoffs/20261024/c12-ACTIVATION.json').read_text())
