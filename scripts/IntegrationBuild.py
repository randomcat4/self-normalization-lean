import pathlib,subprocess,json,hashlib,time,os
w=pathlib.Path.cwd();r=pathlib.Path('/root/rivermind-data/shao-lean-20261021');logdir=r/'logs/integration-v46/sequential';logdir.mkdir(parents=True,exist_ok=True)
base='312caf24d4e6cfb631a5dedc66e292712b25dd5f'
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
 if m in {'Shao.OQ3.QuadraticTiltCumulants': '820239a2a46ae6f3fa5658c5a5f8aca431638d25fbd3a6075ab480d7616b087e', 'Shao.OQ3.OpenDomainWeightedMoments': '7069680b42bf0b5f9060bc9b311fba9bd280c50238958f83090cac2fe39d2f67', 'Shao.OQ3.OpenDomainFrechetCumulants': '6059967b10abffa9967d6fd1fa9cfc5542dda3d7afb5e03439cc6d932a67c6b9', 'Shao.OQ3.OpenDomainSmoothMean': 'c2335375b874e28df095edea6c9d53d5705159acdfe7133d457bfa3d78481dcf', 'Shao.OQ3.OpenDomainMeanInverse': 'faacb1e47ce77dd81588bf908418308c18ded0e65f672455f55bec48a99ecda0', 'Shao.OQ3.OpenDomainCompactMoments': 'a91518aceb2c3e577f8342b4c2c159ba02654953f70d3d16c7967e963814d367', 'Shao.Probability.CenteredQuadraticCharacteristicPower': '356c79ce4975dd6c42b7ea45ac5471f9f8df2845b532734fcf460b3336ef9e56', 'Shao.Probability.QuadraticFullNoiseHighFrequency': 'c5aa9254f1ac89eb6bf3c72877dc6c9b879566d6983725a15ef4803e75021929', 'Shao.Probability.SourceFourierTestKernel': 'f3d751f7a84fa991841a6a005e009b1d6ee28cb2347f55a0280417637adaaeba'}:
  object_hashes={'Shao.OQ3.QuadraticTiltCumulants': '820239a2a46ae6f3fa5658c5a5f8aca431638d25fbd3a6075ab480d7616b087e', 'Shao.OQ3.OpenDomainWeightedMoments': '7069680b42bf0b5f9060bc9b311fba9bd280c50238958f83090cac2fe39d2f67', 'Shao.OQ3.OpenDomainFrechetCumulants': '6059967b10abffa9967d6fd1fa9cfc5542dda3d7afb5e03439cc6d932a67c6b9', 'Shao.OQ3.OpenDomainSmoothMean': 'c2335375b874e28df095edea6c9d53d5705159acdfe7133d457bfa3d78481dcf', 'Shao.OQ3.OpenDomainMeanInverse': 'faacb1e47ce77dd81588bf908418308c18ded0e65f672455f55bec48a99ecda0', 'Shao.OQ3.OpenDomainCompactMoments': 'a91518aceb2c3e577f8342b4c2c159ba02654953f70d3d16c7967e963814d367', 'Shao.Probability.CenteredQuadraticCharacteristicPower': '356c79ce4975dd6c42b7ea45ac5471f9f8df2845b532734fcf460b3336ef9e56', 'Shao.Probability.QuadraticFullNoiseHighFrequency': 'c5aa9254f1ac89eb6bf3c72877dc6c9b879566d6983725a15ef4803e75021929', 'Shao.Probability.SourceFourierTestKernel': 'f3d751f7a84fa991841a6a005e009b1d6ee28cb2347f55a0280417637adaaeba'}
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
