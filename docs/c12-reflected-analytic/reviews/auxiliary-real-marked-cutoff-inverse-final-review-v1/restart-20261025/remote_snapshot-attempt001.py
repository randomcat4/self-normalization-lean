import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,subprocess,datetime,re,difflib,os
base=Path('/root/rivermind-data/shao-lean-20261021')
wt=base/'workspaces/c12-bridge-domination-v71'
def bind(p):
    b=p.read_bytes();return {'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'mtimeNS':p.stat().st_mtime_ns}
def freeze(b):
    lines=b.decode().splitlines(keepends=True); starts=[i for i,l in enumerate(lines) if re.match(r'(private )?theorem ',l)]
    out=''.join(lines[:starts[0]])
    for start in starts:
        stop=next(i+1 for i in range(start,len(lines)) if ':= by' in lines[i])
        out+=''.join(lines[start:stop])+'\n'
    out+=next(l for l in reversed(lines) if l.startswith('end '))
    return out.encode()
obs={'atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'affinity':sorted(os.sched_getaffinity(0)),
     'readOnly':True,'newLeanAuditChecks':0,'bindings':{},'units':[],'display':{}}
for tag,name,attempt in [('cutoff-inverse','AuxiliaryRealMarkedCutoffInverse',2),('finite-cutoff-budget','AuxiliaryRealMarkedFiniteCutoffBudget',1)]:
    out=base/('outputs/c12-auxiliary-real-marked-'+tag+'-v71')
    r=json.loads((out/'receipt.json').read_text())
    files={out/'receipt.json',wt/('Shao/C2/'+name+'.lean'),out/(name+'.olean'),wt/('.lake/build/lib/lean/Shao/C2/'+name+'.olean')}
    files.update(Path(v['remotePath']) for v in r['artifacts'].values())
    pre=json.loads((out/'preflight-observation.json').read_text())
    files.update(Path(p) for p in pre['bindings'])
    for p in files:obs['bindings'][str(p)]=bind(p)
    source=(wt/('Shao/C2/'+name+'.lean')).read_bytes();f=(out/'frozen.lean.txt').read_bytes()
    checks=[]
    for a in range(1,attempt+1):
        p=out/('attempt%03d'%a)/'source.lean';b=p.read_bytes()
        checks.append({'path':str(p),'reconstructedFreezeMatches':freeze(b)==f,'CRCount':b.count(b'\r'),'noBOM':not b.startswith(b'\xef\xbb\xbf')})
        for file in ['command.txt','exit.json','kernel.log']:
            p=out/('attempt%03d'%a)/file
            obs['display'][str(p)]=p.read_text()
    for file in ['audit-command.txt','audit-exit.json']:
        obs['display'][str(out/file)]=(out/file).read_text()
    raw=(out/'owned-audit.log').read_bytes();types=(out/'actual-owned-types.txt').read_bytes()
    clean=re.sub(rb'(?m)^.*?\.lean:\d+:\d+: info: ',b'',raw)
    idx=clean.find(types)
    unit={'module':r['module'],'sourceEqualsArchive':source==(out/('attempt%03d'%attempt)/'source.lean').read_bytes(),
          'sourceFreezeMatches':freeze(source)==f,'archiveFormatsAndFreezes':checks,
          'receiptArtifactMatches':{n:obs['bindings'][v['remotePath']]['sha256']==v['sha256'] for n,v in r['artifacts'].items()},
          'preflightBindingsMatch':all(obs['bindings'][p]['sha256']==v['sha256'] for p,v in pre['bindings'].items()),
          'auditFraming':{'rawBinding':bind(out/'owned-audit.log'),'payloadBinding':bind(out/'actual-owned-types.txt'),
             'exactPayloadContiguousAfterInfoPrefixRemoval':idx>=0,
             'rawFirst500':raw[:500].decode(),'rawLast250':raw[-250:].decode()}}
    if idx>=0:
        unit['auditFraming'].update({'prefix':clean[:idx].decode(),'suffix':clean[idx+len(types):].decode(),
          'removedInfoPrefixes':[m.group().decode() for m in re.finditer(rb'(?m)^.*?\.lean:\d+:\d+: info: ',raw)]})
    obs['units'].append(unit)
    if attempt==2:
        old=(out/'attempt001/source.lean').read_text();new=source.decode()
        obs['display']['unit185 exact failed001 to successful002 source diff']=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True)))
supp=base/'sources/current/c12/supplement.tex';obs['bindings'][str(supp)]=bind(supp)
ls=supp.read_text().splitlines()
for a,b in [(4431,4444),(4474,4485)]:obs['display'][f'supplement.tex:{a}-{b}']='\n'.join(f'{i+1}: {ls[i]}' for i in range(a-1,b))
obs['git']={k:subprocess.check_output(['git','-C',str(wt)]+cmd,text=True).strip() for k,cmd in [('head',['rev-parse','HEAD']),('branch',['branch','--show-current']),('tree',['rev-parse','HEAD^{tree}'])]}
obs['toolchain']=(wt/'lean-toolchain').read_text().strip();obs['packages']=str((wt/'.lake/packages').resolve())
mathlib=(wt/'.lake/packages/mathlib').resolve()
obs['mathlib']=subprocess.check_output(['git','-C',str(mathlib),'rev-parse','HEAD'],text=True).strip()
obs['nativeLocations']=subprocess.run(['rg','-n','--glob','*.lean',r'^(theorem|lemma) (integrable_prod_iff|integral_integral_swap|integral_mono_ae|integral_mono|Integrable.mono\x27|rpow_add|rpow_le_rpow|div_rpow|rpow_div_two_eq_sqrt|rpow_neg)\b',str(mathlib/'Mathlib')],capture_output=True,text=True).stdout
print(json.dumps(obs,ensure_ascii=False))
