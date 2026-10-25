import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,datetime,os,re,hashlib
p=Path('/root/rivermind-data/shao-lean-20261021/cache-overlays/shared-v34/packages/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean')
ls=p.read_text().splitlines(); ranges=[(139,172),(190,215),(306,350)]
obs={'atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'affinity':sorted(os.sched_getaffinity(0)),
 'sourceSHA256':hashlib.sha256(p.read_bytes()).hexdigest(),'ranges':ranges,'display':{}}
for a,b in ranges:obs['display'][str(p)+f':{a}-{b}']='\n'.join(f'{i+1}: {ls[i]}' for i in range(a-1,b))
print(json.dumps(obs,ensure_ascii=False))
