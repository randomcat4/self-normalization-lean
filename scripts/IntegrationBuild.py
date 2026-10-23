import pathlib,subprocess,json,hashlib,time,os
w=pathlib.Path.cwd();r=pathlib.Path('/root/rivermind-data/shao-lean-20261021');logdir=r/'logs/integration-v48/sequential';logdir.mkdir(parents=True,exist_ok=True)
base='388b6e253cff7f898c1f4c2fec46c63439f4a24f'
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
 if m in {'Shao.OQ5.P53.SparseCoefficientMoments': 'f7780fa2c42c9cc4dfd4c94f8c900628bc5252690f284bbf34133bc0aa203381', 'Shao.OQ5.P53.SparseSignedLabelLaw': '8c20f2f4af2837802af8780b40229de37bc09fc9fdf4ddcf954b5aad9591b848', 'Shao.OQ5.P53.SparseSignedAmplitude': '01d1f0629004fff1091bb0b8ade0f82707a20e3c7debd2998494585868f977f4', 'Shao.OQ5.P53.SparseSignedShift': 'd82be1592f14bdd89baf1cf6147ce3f0910756a6df2896509857689f510c583c', 'Shao.Probability.SourceMarkFourierNorms': 'fa56f513ff44ca0d09436ddbb241a7b6840e3161b5aecc6048c7074f75f0fe87'}:
  object_hashes={'Shao.OQ5.P53.SparseCoefficientMoments': 'f7780fa2c42c9cc4dfd4c94f8c900628bc5252690f284bbf34133bc0aa203381', 'Shao.OQ5.P53.SparseSignedLabelLaw': '8c20f2f4af2837802af8780b40229de37bc09fc9fdf4ddcf954b5aad9591b848', 'Shao.OQ5.P53.SparseSignedAmplitude': '01d1f0629004fff1091bb0b8ade0f82707a20e3c7debd2998494585868f977f4', 'Shao.OQ5.P53.SparseSignedShift': 'd82be1592f14bdd89baf1cf6147ce3f0910756a6df2896509857689f510c583c', 'Shao.Probability.SourceMarkFourierNorms': 'fa56f513ff44ca0d09436ddbb241a7b6840e3161b5aecc6048c7074f75f0fe87'}
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
