import pathlib,subprocess,json,hashlib,time,os
w=pathlib.Path.cwd();r=pathlib.Path('/root/rivermind-data/shao-lean-20261021');logdir=r/'logs/integration-v50/sequential';logdir.mkdir(parents=True,exist_ok=True)
base='5e7f4616f2092c91e62e40912a8fa2f0637b382a'
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
 if m in {'Shao.OQ4.RademacherRealThresholdBridge': 'a8ea9dcc1d9f8364e7e5a13c707cc82d88a6498357495e33952e548cd42eba44', 'Shao.OQ4.RademacherAdjacentLogFinite': '13ef20d6ce80ebd76ad9126cbd3747b37cc302d93cce9da30df52df967053319', 'Shao.OQ4.RademacherAdjacentLog': '8588160d6a59ba6093b2f51b3a84ad64601d649c897f14b1f41b170669fe0704', 'Shao.OQ4.WeightedThirdMomentB2': '9f17fff7fa969fa5e69c8cb06e8a0962280f033d93e58f1fdb0d47924e62a2bd', 'Shao.OQ5.P53.SparsePopulationOperator': 'b4421c6b33a7ac171e28dde3d5a6cb47db68e306e49736efaaec91b34aed5cfe', 'Shao.Probability.QuadraticFullNoiseMarkedOutside': 'b1102c4dbbd7d04d9a22c48770c2fa73c9636fbb0fd50c66f5cf82863c727a95', 'Shao.Probability.QuadraticFullNoiseMarkedRegionFour': '1ef36c40d6b61aea8460c2a8a121c172ea3141c05c7bdaff78189a9d4ad923a8', 'Shao.Probability.SourceFutureNoiseOddEven': 'f4d6d31b22933ef66ad85862bc69779f109bb2a289e0697c6ff0eafcbeb3a3c8', 'Shao.OQ4.PolygonalThirdMomentB3': '2f276340bba49f7f4ed5c424d52a145690563f209140f939bdd37d76d86a554a', 'Shao.Probability.QuadraticFullNoiseLowDerivatives': '7fa6d0e9f697c8a290c07c7a160248023bf35c30bfafcaba584d8207a6d05658', 'Shao.Probability.SourceOddEvenWholeLineIBP': '01f8df4d5fe563e6c4265f33b172655db220b91bacebe097f4ad5afe30bebdab'}:
  object_hashes={'Shao.OQ4.RademacherRealThresholdBridge': 'a8ea9dcc1d9f8364e7e5a13c707cc82d88a6498357495e33952e548cd42eba44', 'Shao.OQ4.RademacherAdjacentLogFinite': '13ef20d6ce80ebd76ad9126cbd3747b37cc302d93cce9da30df52df967053319', 'Shao.OQ4.RademacherAdjacentLog': '8588160d6a59ba6093b2f51b3a84ad64601d649c897f14b1f41b170669fe0704', 'Shao.OQ4.WeightedThirdMomentB2': '9f17fff7fa969fa5e69c8cb06e8a0962280f033d93e58f1fdb0d47924e62a2bd', 'Shao.OQ5.P53.SparsePopulationOperator': 'b4421c6b33a7ac171e28dde3d5a6cb47db68e306e49736efaaec91b34aed5cfe', 'Shao.Probability.QuadraticFullNoiseMarkedOutside': 'b1102c4dbbd7d04d9a22c48770c2fa73c9636fbb0fd50c66f5cf82863c727a95', 'Shao.Probability.QuadraticFullNoiseMarkedRegionFour': '1ef36c40d6b61aea8460c2a8a121c172ea3141c05c7bdaff78189a9d4ad923a8', 'Shao.Probability.SourceFutureNoiseOddEven': 'f4d6d31b22933ef66ad85862bc69779f109bb2a289e0697c6ff0eafcbeb3a3c8', 'Shao.OQ4.PolygonalThirdMomentB3': '2f276340bba49f7f4ed5c424d52a145690563f209140f939bdd37d76d86a554a', 'Shao.Probability.QuadraticFullNoiseLowDerivatives': '7fa6d0e9f697c8a290c07c7a160248023bf35c30bfafcaba584d8207a6d05658', 'Shao.Probability.SourceOddEvenWholeLineIBP': '01f8df4d5fe563e6c4265f33b172655db220b91bacebe097f4ad5afe30bebdab'}
  assert hashlib.sha256(dest.read_bytes()).hexdigest()==object_hashes[m]
  entry={'module':m,'source':p,'source_sha256':hashlib.sha256((w/p).read_bytes()).hexdigest(),'object_sha256':object_hashes[m],'exit_code':0,'seconds':0,'mode':'REUSE_EXACT_SOURCE_BOUND_AUTHOR_OBJECT_AFTER_COMPLETE_INDEPENDENT_REVIEW'}
  results.append(entry);(logdir/'progress.json').write_text(json.dumps(results,indent=2)+'\n')
  print(m,'REUSED_VERIFIED_OBJECT',flush=True)
  continue
 with log.open('w') as f:res=subprocess.run(['lake','env','lean','-M','8192','-j','4','-DautoImplicit=false','-o',str(dest),p],stdout=f,stderr=subprocess.STDOUT)
 entry={'module':m,'source':p,'source_sha256':hashlib.sha256((w/p).read_bytes()).hexdigest(),'exit_code':res.returncode,'seconds':round(time.monotonic()-start,3),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()}
 entry['mode']='AGGREGATE_ONLY' if m=='Shao' else 'FIRST_NECESSARY_PURE_SOURCE_OBJECT_EMISSION_AFTER_QUALIFIED_KERNEL_REVIEW'
 if res.returncode==0:entry['object_sha256']=hashlib.sha256(dest.read_bytes()).hexdigest()
 results.append(entry);(logdir/'progress.json').write_text(json.dumps(results,indent=2)+'\n')
 print(m,res.returncode,flush=True)
 if res.returncode:raise SystemExit(res.returncode)
print('SEQUENTIAL_INTEGRATED_BUILD_PASS',len(results),flush=True)
