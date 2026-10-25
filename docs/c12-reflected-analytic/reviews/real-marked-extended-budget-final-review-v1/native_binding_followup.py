import hashlib,json,shlex,sys
from pathlib import Path
ROOT=Path('C:/game/shao lean'); HERE=ROOT/'drafts/c12-lane/real-marked-extended-budget-final-review-v1'
sys.path.insert(0,str(ROOT/'tools'))
from transport_client import send_request
o=json.loads((HERE/'fresh-readonly-observation.json').read_text(encoding='utf-8'))
nativePaths=sorted({r['path'] for rs in o['native'].values() for r in rs})
code=r'''
import datetime,hashlib,json,os,pathlib,subprocess,sys
cfg=json.loads(sys.stdin.read()); wt=pathlib.Path('/root/rivermind-data/shao-lean-20261021/workspaces/c12-bridge-domination-v71'); ml=wt/'.lake/packages/mathlib'
def meta(p):
 b=pathlib.Path(p).read_bytes();return {'remotePath':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
out={'atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'readOnly':True,'affinity':sorted(os.sched_getaffinity(0)),'nativePinnedBindings':[],'primary':{},'projectContracts':{},'C12LeanLake':[]}
for p in cfg['nativePaths']:
 p=pathlib.Path(p); rel=p.relative_to(ml); b=p.read_bytes(); pinned=subprocess.check_output(['git','-C',str(ml),'show','807d3836b165983210ee2ecf3cd28f239436949c:'+str(rel)])
 out['nativePinnedBindings'].append({**meta(p),'pinnedGitBlobSHA256':hashlib.sha256(pinned).hexdigest(),'matchesPinnedGitBlob':b==pinned})
src=pathlib.Path('/root/rivermind-data/shao-lean-20261021/sources/c12/supplement.tex')
if not src.exists():
 matches=list(pathlib.Path('/root/rivermind-data/shao-lean-20261021/sources').glob('**/c12/supplement.tex'));src=matches[0] if matches else src
if src.exists():
 ls=src.read_text().splitlines();out['primary']={**meta(src),'scopeLines':[{ 'line':i+1,'text':ls[i]} for i in range(4430,4485)]}
for rel,starts in [('Shao/Basic/FinitePath.lean',['abbrev Path','def prefixSum','def energy','@[simp] theorem prefixSum_length']),('Shao/Probability/SourceSuffixMomentBudgets.lean',['theorem raw_gaussian_damped_coordinate_factors'])]:
 p=wt/rel
 if not p.exists() and 'SourceSuffix' in rel:p=pathlib.Path('/root/rivermind-data/shao-lean-20261021/workspaces/common-suffix-moment-budgets-v73')/rel
 ls=p.read_text().splitlines();rows=[]
 for i,line in enumerate(ls):
  if any(line.startswith(x) for x in starts):
   end=i+1
   if 'raw_gaussian' in line:
    while end<len(ls) and ':= by' not in ls[end-1]:end+=1
   else:end=min(len(ls),i+5)
   rows.append({'start':i+1,'end':end,'text':'\n'.join(ls[i:end])})
 out['projectContracts'][rel]={**meta(p),'excerpts':rows}
for p in pathlib.Path('/proc').glob('[0-9]*/cmdline'):
 try:
  c=p.read_bytes().split(b'\0');exe=pathlib.Path(c[0].decode()).name if c else ''
  if exe in ['lean','lake']:
   text=b' '.join(c).decode(errors='replace')
   if 'c12-' in text or 'AuxiliaryRealMarked' in text:out['C12LeanLake'].append({'pid':int(p.parent.name),'command':text,'affinity':sorted(os.sched_getaffinity(int(p.parent.name)))})
 except (OSError,ProcessLookupError):pass
print(json.dumps(out,ensure_ascii=False))
'''
r=send_request({'action':'exec','command':'taskset -c 44-47 python3 -c '+shlex.quote(code),'stdin':json.dumps({'nativePaths':nativePaths}),'timeout':60})
if r.get('ok') is False or r.get('exit_code')!=0:print(json.dumps(r));raise SystemExit(1)
d=json.loads(r['stdout']);(HERE/'native-source-binding-followup.json').write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(d,ensure_ascii=False,indent=2))
