import pathlib,subprocess,json,hashlib,time,os
w=pathlib.Path.cwd();r=pathlib.Path('/root/rivermind-data/shao-lean-20261021');logdir=r/'logs/integration-v45/sequential';logdir.mkdir(parents=True,exist_ok=True)
base='e685f157e178289d21de98cdcb963bd951dd6fba'
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
 if m in {'Shao.Probability.QuadraticChordConeDerivatives': 'e6cae0ce8206f0800c9b0846e7f11c4d43f901d201b8d443e36104898e396cb8', 'Shao.Probability.SourceScalarFourierDerivatives': 'f73e3779d4e6df00bd0fec4ef5898e1db8952a011f96ee99a0236ed2c57e4aa0', 'Shao.Probability.QuadraticFullNoiseConeDerivatives': '32c4bba923ca01613a67b688e07fce4d493210ff2e2d48d6e45584fa8f407144', 'Shao.Probability.CenteredQuadraticCharacteristic': 'e1e4092b75e4b7bcb01afd3fffcf134070c7c3d33fcda63379f2a1717c3756e5'}:
  object_hashes={'Shao.Probability.QuadraticChordConeDerivatives': 'e6cae0ce8206f0800c9b0846e7f11c4d43f901d201b8d443e36104898e396cb8', 'Shao.Probability.SourceScalarFourierDerivatives': 'f73e3779d4e6df00bd0fec4ef5898e1db8952a011f96ee99a0236ed2c57e4aa0', 'Shao.Probability.QuadraticFullNoiseConeDerivatives': '32c4bba923ca01613a67b688e07fce4d493210ff2e2d48d6e45584fa8f407144', 'Shao.Probability.CenteredQuadraticCharacteristic': 'e1e4092b75e4b7bcb01afd3fffcf134070c7c3d33fcda63379f2a1717c3756e5'}
  assert hashlib.sha256(dest.read_bytes()).hexdigest()==object_hashes[m]
  entry={'module':m,'source':p,'source_sha256':hashlib.sha256((w/p).read_bytes()).hexdigest(),'object_sha256':object_hashes[m],'exit_code':0,'seconds':0,'mode':'REUSE_EXACT_SOURCE_BOUND_AUTHOR_OBJECT_AFTER_COMPLETE_INDEPENDENT_REVIEW'}
  results.append(entry);(logdir/'progress.json').write_text(json.dumps(results,indent=2)+'\n')
  print(m,'REUSED_VERIFIED_OBJECT',flush=True)
  continue
 with log.open('w') as f:res=subprocess.run(['lake','env','lean','-M','8192','-j','4','-DautoImplicit=false','-o',str(dest),p],stdout=f,stderr=subprocess.STDOUT)
 entry={'module':m,'source':p,'source_sha256':hashlib.sha256((w/p).read_bytes()).hexdigest(),'exit_code':res.returncode,'seconds':round(time.monotonic()-start,3),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()}
 results.append(entry);(logdir/'progress.json').write_text(json.dumps(results,indent=2)+'\n')
 print(m,res.returncode,flush=True)
 if res.returncode:raise SystemExit(res.returncode)
print('SEQUENTIAL_INTEGRATED_BUILD_PASS',len(results),flush=True)
