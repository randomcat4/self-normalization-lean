import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,datetime,hashlib,os,re
base=Path('/root/rivermind-data/shao-lean-20261021');mathlib=base/'cache-overlays/shared-v34/packages/mathlib'
obs={'atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'affinity':sorted(os.sched_getaffinity(0)), 'display':{},'ranges':[]}
for p,ranges in [
 (mathlib/'Mathlib/MeasureTheory/Integral/Prod.lean',[(78,140),(245,305)]),
 (base/'sources/current/c12/supplement.tex',[(4360,4430),(4445,4473)])]:
    b=p.read_bytes();lines=b.decode().splitlines()
    for a,z in ranges:
        obs['ranges'].append({'path':str(p),'from':a,'to':z,'sha256':hashlib.sha256(b).hexdigest()})
        obs['display'][str(p)+f':{a}-{z}']='\n'.join(f'{i+1}: {lines[i]}' for i in range(a-1,z))
# Bounded read-only runtime view: identify only C12 Lean/lake execution by cwd/cmdline.
own=[]
for proc in Path('/proc').iterdir():
    if not proc.name.isdigit():continue
    try:
        args=(proc/'cmdline').read_bytes().replace(b'\x00',b' ').decode(errors='replace')
        if not args:continue
        cwd=str((proc/'cwd').resolve())
        if cwd==str(base/'workspaces/c12-bridge-domination-v71') and re.search(r'(^|/| )(lean|lake)( |$)',args):
            own.append({'pid':int(proc.name),'cwd':cwd,'command':args[:700]})
    except (FileNotFoundError,PermissionError,ProcessLookupError):pass
obs['c12LeanLakeProcesses']=own
print(json.dumps(obs,ensure_ascii=False))
