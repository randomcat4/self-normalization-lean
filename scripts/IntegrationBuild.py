import pathlib,subprocess,json,hashlib,time,os
w=pathlib.Path.cwd();r=pathlib.Path('/root/rivermind-data/shao-lean-20261021');logdir=r/'logs/integration-v42/sequential';logdir.mkdir(parents=True,exist_ok=True)
base='ece32b1691a5d24a1f8114f6e6a32cbcb0613529'
changed=subprocess.check_output(['git','diff','--name-only',base,'HEAD','--','Shao'],text=True).splitlines()
mods={p[:-5].replace('/','.') : p for p in changed if p.endswith('.lean')}
order=[];active=set();done=set()
def visit(m):
 if m in done:return
 assert m not in active,'import cycle '+m
 active.add(m)
 for line in (w/mods[m]).read_text().splitlines():
  if line.startswith('import '):
   for d in line[7:].split():
    if d in mods:visit(d)
 active.remove(m);done.add(m);order.append(m)
for m in sorted(mods):visit(m)
results=[]
for m in order+['Shao']:
 p=mods.get(m,'Shao.lean');dest=w/'.lake/build/lib/lean'/pathlib.Path(m.replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
 log=logdir/(m+'.log');start=time.monotonic()
 with log.open('w') as f:res=subprocess.run(['lake','env','lean','-M','8192','-j','4','-DautoImplicit=false','-o',str(dest),p],stdout=f,stderr=subprocess.STDOUT)
 entry={'module':m,'source':p,'source_sha256':hashlib.sha256((w/p).read_bytes()).hexdigest(),'exit_code':res.returncode,'seconds':round(time.monotonic()-start,3),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()}
 results.append(entry);(logdir/'progress.json').write_text(json.dumps(results,indent=2)+'\n')
 print(m,res.returncode,flush=True)
 if res.returncode:raise SystemExit(res.returncode)
print('SEQUENTIAL_INTEGRATED_BUILD_PASS',len(results),flush=True)
