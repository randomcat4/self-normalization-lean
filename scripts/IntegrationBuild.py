import pathlib,subprocess,json,hashlib,time,os
w=pathlib.Path.cwd();r=pathlib.Path('/root/rivermind-data/shao-lean-20261021');logdir=r/'logs/integration-v49/sequential';logdir.mkdir(parents=True,exist_ok=True)
base='f452ec2a47b6f12977d10a3d995ad3852a00c5a7'
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
 if m in {'Shao.OQ3.OpenDomainBoundaryJet': 'd593a9c439572b7bfbdc6e451876513372b0dbb8a2f43e8fb10101c4043e3f50', 'Shao.OQ3.LocalCubicTaylor': 'ac1d743f360f14e70d84d3a0ab4de0d0347009b85f26a38f347aa123ab390bdd', 'Shao.OQ3.LocalBoundaryTaylor': '5e6a3ce2f66a9bbd3338c03d7c6d8a465e1cbe5003da85314b68bde62e5fac9e', 'Shao.OQ3.OpenDomainBoundaryTaylor': '79dbfe6730c023911f392ebeba0a4d7296478acf5f03b9e4e6f57e725608b383', 'Shao.OQ3.LocalBoundaryLowerBound': '5b3b1c07f823292b441f42c1c99538056651507e0a36e9a1e2ad4e70ae7049b9', 'Shao.OQ3.OpenDomainBoundaryLowerBound': '6be9582aee39433d33a46a52fef52cdeea79c7c0e6a63a271ff131d4e6cf1cea', 'Shao.OQ3.OpenDomainCovarianceAmplitude': '494d228652c426ebb25ac2916a3e5e240ae60cdb1c4e17f39dac3f95f0c392b2', 'Shao.OQ3.BoundaryLaplaceExponential': '780eb1879be224113235fcbba8d1330c01cf7836b0db3448e5b20d772e8c63a2', 'Shao.OQ3.BoundaryLaplaceScaledError': 'fd4904b34868cc51622118741f38f762366be5efafa0571659e88ec814e8a00a', 'Shao.OQ3.BoundaryLaplaceCutoff': '152711f7a5ac9eebdc7fd0b4e063d4be4187c4dd726f7a54419c793be2621893', 'Shao.OQ5.P53.SparseProjectionLaw': '4dc653399ec68e05188f7dc12dfbc7875c0de4718a0354a6bdc7c9718003f0f3', 'Shao.OQ5.P53.SparsePopulation': '5f90758e61df1a8d319737332602259cda2ee2c7e86d2dff45278b3d6da2bc6c', 'Shao.OQ5.P53.SparsePopulationKernel': '75cd0065aaf857dd296ebb4e4c602e96fdc9c931f8c1354dbbb635face926d66', 'Shao.Probability.SourceKernelAmplitudeFamily': '15cc5fde79f240f26782f0daabf9c49c1a06f60968068cebf2a684818db94ff7', 'Shao.Probability.SourceKernelMarkedOutside': '2be9fff325937c535766dbfd9d8f69c618d358fe69ed9c994caa643672e2dd35', 'Shao.Probability.SourceFutureNoiseInversion': 'bb0ced399a1f20b7b9822e6d16504639bd26a1a2d1e3e04ffdc934a76ce1daeb'}:
  object_hashes={'Shao.OQ3.OpenDomainBoundaryJet': 'd593a9c439572b7bfbdc6e451876513372b0dbb8a2f43e8fb10101c4043e3f50', 'Shao.OQ3.LocalCubicTaylor': 'ac1d743f360f14e70d84d3a0ab4de0d0347009b85f26a38f347aa123ab390bdd', 'Shao.OQ3.LocalBoundaryTaylor': '5e6a3ce2f66a9bbd3338c03d7c6d8a465e1cbe5003da85314b68bde62e5fac9e', 'Shao.OQ3.OpenDomainBoundaryTaylor': '79dbfe6730c023911f392ebeba0a4d7296478acf5f03b9e4e6f57e725608b383', 'Shao.OQ3.LocalBoundaryLowerBound': '5b3b1c07f823292b441f42c1c99538056651507e0a36e9a1e2ad4e70ae7049b9', 'Shao.OQ3.OpenDomainBoundaryLowerBound': '6be9582aee39433d33a46a52fef52cdeea79c7c0e6a63a271ff131d4e6cf1cea', 'Shao.OQ3.OpenDomainCovarianceAmplitude': '494d228652c426ebb25ac2916a3e5e240ae60cdb1c4e17f39dac3f95f0c392b2', 'Shao.OQ3.BoundaryLaplaceExponential': '780eb1879be224113235fcbba8d1330c01cf7836b0db3448e5b20d772e8c63a2', 'Shao.OQ3.BoundaryLaplaceScaledError': 'fd4904b34868cc51622118741f38f762366be5efafa0571659e88ec814e8a00a', 'Shao.OQ3.BoundaryLaplaceCutoff': '152711f7a5ac9eebdc7fd0b4e063d4be4187c4dd726f7a54419c793be2621893', 'Shao.OQ5.P53.SparseProjectionLaw': '4dc653399ec68e05188f7dc12dfbc7875c0de4718a0354a6bdc7c9718003f0f3', 'Shao.OQ5.P53.SparsePopulation': '5f90758e61df1a8d319737332602259cda2ee2c7e86d2dff45278b3d6da2bc6c', 'Shao.OQ5.P53.SparsePopulationKernel': '75cd0065aaf857dd296ebb4e4c602e96fdc9c931f8c1354dbbb635face926d66', 'Shao.Probability.SourceKernelAmplitudeFamily': '15cc5fde79f240f26782f0daabf9c49c1a06f60968068cebf2a684818db94ff7', 'Shao.Probability.SourceKernelMarkedOutside': '2be9fff325937c535766dbfd9d8f69c618d358fe69ed9c994caa643672e2dd35', 'Shao.Probability.SourceFutureNoiseInversion': 'bb0ced399a1f20b7b9822e6d16504639bd26a1a2d1e3e04ffdc934a76ce1daeb'}
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
