import sys
sys.dont_write_bytecode=True
from pathlib import Path
import subprocess,hashlib,json,datetime,re,os
base=Path('/root/rivermind-data/shao-lean-20261021')
mathlib=base/'cache-overlays/shared-v34/packages/mathlib'
wt=base/'workspaces/c12-bridge-domination-v71'
obs={'atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'affinity':sorted(os.sched_getaffinity(0)),
     'nativePinChecks':[],'definitionBindings':[],'display':{}}
def emit(p, ranges, native=False):
    b=p.read_bytes(); bind={'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}
    if native:
        pin=subprocess.check_output(['git','-C',str(mathlib),'show','807d3836b165983210ee2ecf3cd28f239436949c:'+str(p.relative_to(mathlib))])
        bind.update(pinSHA256=hashlib.sha256(pin).hexdigest(),byteIdenticalToPin=b==pin)
        obs['nativePinChecks'].append(bind)
    else:obs['definitionBindings'].append(bind)
    lines=b.decode().splitlines()
    for a,z in ranges:obs['display'][str(p)+f':{a}-{z}']='\n'.join(f'{i+1}: {lines[i]}' for i in range(a-1,min(z,len(lines))))
for file,ranges in [
 ('MeasureTheory/Integral/Prod.lean',[(35,77),(215,244),(360,390),(470,490)]),
 ('MeasureTheory/Function/L1Space/Integrable.lean',[(40,106)]),
 ('MeasureTheory/Integral/Bochner/Basic.lean',[(637,676)]),
 ('Analysis/SpecialFunctions/Pow/Real.lean',[(197,214),(249,263),(471,494),(545,560),(989,1006)])]:
    emit(mathlib/'Mathlib'/file,ranges,True)
for file,pattern in [('Shao/Basic/FinitePath.lean',r'^(abbrev Path|def (prefixSum|energy))'),('Shao/Probability/MeasurablePath.lean',r'^(theorem|lemma) measurable_(energy|prefixSum)')]:
    p=wt/file;ls=p.read_text().splitlines();ranges=[]
    for i,l in enumerate(ls):
        if re.search(pattern,l):ranges.append((max(1,i-1),min(len(ls),i+12)))
    emit(p,ranges)
print(json.dumps(obs,ensure_ascii=False))
