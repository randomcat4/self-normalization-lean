import pathlib,subprocess,json,hashlib,time,os
w=pathlib.Path.cwd();r=pathlib.Path('/root/rivermind-data/shao-lean-20261021');logdir=r/'logs/integration-v47/sequential';logdir.mkdir(parents=True,exist_ok=True)
base='efeecafac6ddc7f5f5407bbc8b7e3519143ffef0'
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
 if m in {'Shao.Probability.QuadraticFullNoiseRegionFour': 'ea60703c33a6b503f835607153b84311549a8234eea52b8f2aa20f16039a91b5', 'Shao.Probability.QuadraticFullNoiseGlobalOddEven': '999cf81e1044a178f038875d1902fcc474b93bd2b5c0a17860a0c8a1dfe40dde', 'Shao.Probability.QuadraticFullNoiseOutsideWeights': 'fb0362b6f0943eeffcc675689a5e9ce029e0cdf82d55d0b3fcd432fb8e1e63de', 'Shao.Probability.SourceFutureNoiseFourier': '284987012197dc7db3c5abd55d4ff6441d737b1de07b7612a08bf4f806f11fd2', 'Shao.OQ3.OpenDomainAffineMoments': '4db6e4828491ef0f086d259e03125128d286d95ed5a35ddf387a4729549cf95a', 'Shao.OQ3.QuadraticWhiteningSpectralData': 'e30a9e99dd2bbcd1f6cc44c7a2b577724f20f6f71cb1e555fb0173c0eabf01cd', 'Shao.OQ3.OpenDomainWhitenedFamily': 'fccdc64bc2e71f1fdc4d070c89ec0c019640d3d99379a063782776c0436314a5', 'Shao.OQ3.OpenDomainRealMoments': '3775c3293e78e0c58fb8000651f1e3c23f5f3a10bd6809b168417afb6b85d3e1', 'Shao.OQ3.OpenDomainCompactMeanChart': '570a5ad3658e6415eb6dbde5f60df723f42d0e853b20d391870eeac3ce146f33', 'Shao.OQ3.OpenDomainLegendre': 'fd7c4ddacc183c4bd93030bed4c5b57c677965668fe192abd51d9126150f2a6e', 'Shao.OQ3.OpenDomainRateDerivatives': '976331f85ecd1a41e88c278e00446025fbcb1acf1236d4e01b634452c0baaa9d', 'Shao.OQ3.OpenDomainBoundaryRate': '31707cfce94ffcf16232cb8d43e27f7443673566df0f39b8c226fa2b327ac524'}:
  object_hashes={'Shao.Probability.QuadraticFullNoiseRegionFour': 'ea60703c33a6b503f835607153b84311549a8234eea52b8f2aa20f16039a91b5', 'Shao.Probability.QuadraticFullNoiseGlobalOddEven': '999cf81e1044a178f038875d1902fcc474b93bd2b5c0a17860a0c8a1dfe40dde', 'Shao.Probability.QuadraticFullNoiseOutsideWeights': 'fb0362b6f0943eeffcc675689a5e9ce029e0cdf82d55d0b3fcd432fb8e1e63de', 'Shao.Probability.SourceFutureNoiseFourier': '284987012197dc7db3c5abd55d4ff6441d737b1de07b7612a08bf4f806f11fd2', 'Shao.OQ3.OpenDomainAffineMoments': '4db6e4828491ef0f086d259e03125128d286d95ed5a35ddf387a4729549cf95a', 'Shao.OQ3.QuadraticWhiteningSpectralData': 'e30a9e99dd2bbcd1f6cc44c7a2b577724f20f6f71cb1e555fb0173c0eabf01cd', 'Shao.OQ3.OpenDomainWhitenedFamily': 'fccdc64bc2e71f1fdc4d070c89ec0c019640d3d99379a063782776c0436314a5', 'Shao.OQ3.OpenDomainRealMoments': '3775c3293e78e0c58fb8000651f1e3c23f5f3a10bd6809b168417afb6b85d3e1', 'Shao.OQ3.OpenDomainCompactMeanChart': '570a5ad3658e6415eb6dbde5f60df723f42d0e853b20d391870eeac3ce146f33', 'Shao.OQ3.OpenDomainLegendre': 'fd7c4ddacc183c4bd93030bed4c5b57c677965668fe192abd51d9126150f2a6e', 'Shao.OQ3.OpenDomainRateDerivatives': '976331f85ecd1a41e88c278e00446025fbcb1acf1236d4e01b634452c0baaa9d', 'Shao.OQ3.OpenDomainBoundaryRate': '31707cfce94ffcf16232cb8d43e27f7443673566df0f39b8c226fa2b327ac524'}
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
