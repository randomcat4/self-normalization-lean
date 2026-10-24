from pathlib import Path
import subprocess, json, hashlib, time

w=Path.cwd()
r=Path('/root/rivermind-data/shao-lean-20261021')
logs=r/'logs/integration-v71'
config=json.loads((logs/'scope-config.json').read_text())
logdir=logs/'sequential'
logdir.mkdir(exist_ok=True)
changed=subprocess.check_output(['git','diff','--name-only',config['base'],'HEAD','--','Shao'],text=True).splitlines()
assert set(changed)==set(config['expected'])
mods={p[:-5].replace('/','.') : p for p in changed}
assert set(mods)==set(config['reuse'])
order=[]
active=set()
done=set()
def visit(m):
    if m in done:return
    assert m not in active,'import cycle '+m
    active.add(m)
    for line in (w/mods[m]).read_text().splitlines():
        if line.startswith('import '):
            for d in line[7:].split():
                if d in mods:visit(d)
    active.remove(m)
    done.add(m)
    order.append(m)
for m in sorted(mods):visit(m)
results=[]
for m in order:
    d=config['reuse'][m]
    assert 'PENDING' not in d['qualified_review']
    p=mods[m]
    sh=hashlib.sha256((w/p).read_bytes()).hexdigest()
    assert sh==d['source_sha256']
    dest=w/'.lake/build/lib/lean'/Path(m.replace('.','/')+'.olean')
    assert hashlib.sha256(dest.read_bytes()).hexdigest()==d['sha256']
    results.append({'module':m,'source':p,'source_sha256':sh,'object_sha256':d['sha256'],
                    'exit_code':0,'seconds':0,'mode':'REUSE_EXACT_QUALIFIED_ORIGINAL_PRODUCER_OBJECT',
                    'qualified_review_sha256':d['qualified_review_sha256']})
dest=w/'.lake/build/lib/lean/Shao.olean'
assert not dest.is_symlink(),'Never overwrite an accepted aggregate through a symlink'
log=logdir/'Shao.log'
start=time.monotonic()
with log.open('w') as f:
    proc=subprocess.run(['lake','env','lean','-M','8192','-j','4','-DautoImplicit=false',
                         '-o',str(dest),'Shao.lean'],stdout=f,stderr=subprocess.STDOUT)
entry={'module':'Shao','source':'Shao.lean','source_sha256':hashlib.sha256((w/'Shao.lean').read_bytes()).hexdigest(),
       'exit_code':proc.returncode,'seconds':round(time.monotonic()-start,3),
       'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'mode':'AGGREGATE_ONLY'}
if proc.returncode==0:entry['object_sha256']=hashlib.sha256(dest.read_bytes()).hexdigest()
results.append(entry)
(logdir/'progress.json').write_bytes((json.dumps(results,indent=2)+'\n').encode())
assert proc.returncode==0,'Aggregate failed; preserve original log'
print('INTEGRATED_BUILD_PASS',len(order),'qualified producer objects reused; aggregate only')
