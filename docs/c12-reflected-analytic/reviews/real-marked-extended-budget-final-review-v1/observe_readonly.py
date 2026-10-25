"""One-shot independent read-only evidence observation; never invokes Lean."""
import datetime
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path('C:/game/shao lean')
HERE = ROOT / 'drafts/c12-lane/real-marked-extended-budget-final-review-v1'
sys.path.insert(0, str(ROOT / 'tools'))
from transport_client import send_request

PACKETS = {
    '187': ROOT / 'drafts/c12-lane/auxiliary-real-marked-finite-cutoff-extended-budget-v1',
    '188': ROOT / 'drafts/c12-lane/auxiliary-real-marked-cutoff-extended-budget-v1',
}
receipts = {u: json.loads((p/'receipt.json').read_text(encoding='utf-8')) for u,p in PACKETS.items()}
expected = {}
for r in receipts.values():
    for a in r['artifacts'].values():
        expected[a['remotePath']] = {'sha256':a['sha256'], 'bytes':a['bytes']}
    pre = json.loads((PACKETS['187' if 'Finite' in r['module'] else '188']/'preflight-observation.json').read_text(encoding='utf-8'))
    for a in [pre['source'],pre['object'],pre['importObject'],*pre['consumedBindings'].values(),*pre['nativeFiles'].values()]:
        expected[a['remotePath']] = {'sha256':a['sha256'], 'bytes':a['bytes']}

remote = r'''
import datetime, difflib, hashlib, json, os, pathlib, re, subprocess, sys
cfg = json.loads(sys.stdin.read())
base = pathlib.Path('/root/rivermind-data/shao-lean-20261021')
wt = base/'workspaces/c12-bridge-domination-v71'
def meta(p):
    p=pathlib.Path(p); b=p.read_bytes()
    return {'remotePath':str(p),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'mtimeNs':p.stat().st_mtime_ns}
def git(*args):
    return subprocess.check_output(['git','-C',str(wt),*args],text=True).strip()
out={'atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'readOnly':True,'affinity':sorted(os.sched_getaffinity(0)),
     'worktree':str(wt),'branch':git('branch','--show-current'),'head':git('rev-parse','HEAD'),'tree':git('rev-parse','HEAD^{tree}'),
     'toolchain':(wt/'lean-toolchain').read_text().strip(),'packageRealpath':str((wt/'.lake/packages').resolve()),
     'mathlibHead':subprocess.check_output(['git','-C',str(wt/'.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip(),
     'bindings':{},'units':{},'rawLogs':{},'native':{},'processObservation':[]}
for p,e in cfg['expected'].items():
    m=meta(p); m['matchesExpected']=all(m[k]==v for k,v in e.items()); out['bindings'][p]=m
for unit,r in cfg['receipts'].items():
    folder=pathlib.Path(r['allTypesComplete']['path']).parent
    module=r['module']; short=module.split('.')[-1]
    frozen=(folder/'frozen.lean.txt').read_bytes()
    attempts=[]; snaps=[]
    for n in [1,2,3]:
        path=folder/f'attempt{n:03d}/source.lean'; b=path.read_bytes(); s=b.decode('utf-8')
        hdr=s.split(':= by',1)[0]+':= by\n\nend '+module+'\n'
        attempts.append({'attempt':n,**meta(path),'frozenExact':hdr.encode()==frozen,'UTF8NoBOMLF':not b.startswith(b'\xef\xbb\xbf') and b'\r' not in b,
            'forbiddenTokens':re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',s),'exit':json.loads((folder/f'attempt{n:03d}/exit.json').read_text())})
        snaps.append(s)
        out['rawLogs'][unit+f'-kernel{n:03d}']=(folder/f'attempt{n:03d}/kernel.log').read_text()
    types=(folder/'actual-owned-types.txt').read_bytes(); values=(folder/'actual-definition-values.txt').read_bytes(); log=(folder/'owned-audit.log').read_bytes()
    i=log.find(types); prefix=log[:i] if i>=0 else b''; suffix=log[i+len(types):] if i>=0 else b''
    audit=json.loads((folder/'owned-audit.json').read_text())
    out['units'][unit]={'attempts':attempts,'attemptProofDiffs':{'001to002':''.join(difflib.unified_diff(snaps[0].splitlines(True),snaps[1].splitlines(True))),
       '002to003':''.join(difflib.unified_diff(snaps[1].splitlines(True),snaps[2].splitlines(True)))},
       'audit':audit,'auditExit':json.loads((folder/'audit-exit.json').read_text()),'auditResult':json.loads((folder/'audit-result.json').read_text()),
       'typeBytes':len(types),'valueBytes':len(values),'typePayloadSingleOccurrence':log.count(types)==1,
       'auditLogReconstruction':{'payloadFound':i>=0,'prefix':prefix.decode(),'suffix':suffix.decode(),
          'prefixBytes':len(prefix),'suffixBytes':len(suffix),'reconstructedSHA256':hashlib.sha256(prefix+types+suffix).hexdigest(),
          'matchesEntireOriginal':i>=0 and prefix+types+suffix==log},'currentSourceEqualsAttempt003':(wt/'Shao/C2'/f'{short}.lean').read_bytes()==snaps[2].encode()}
patterns=['ofReal_integral_eq_lintegral_ofReal','lintegral_const_mul\x27','lintegral_mono_ae','lintegral_iSup','ofReal_mul','ennreal_ofReal']
searchpaths=[wt/'.lake/packages/mathlib/Mathlib/MeasureTheory/Integral',wt/'.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean',wt/'.lake/packages/mathlib/Mathlib/Basic/ENNReal']
for pat in patterns:
    rows=[]
    for root in searchpaths:
        for p in ([root] if root.is_file() else root.rglob('*.lean')):
            ls=p.read_text().splitlines()
            for idx,line in enumerate(ls):
                if re.search(r'\b(?:theorem|lemma).*\b'+re.escape(pat)+r'(?=\s|\()',line):
                    rows.append({'path':str(p),'line':idx+1,'file':meta(p),'lines':[{'line':j+1,'text':ls[j]} for j in range(max(0,idx-2),min(len(ls),idx+13))]})
    out['native'][pat]=rows
for p in pathlib.Path('/proc').glob('[0-9]*/cmdline'):
    try:
        c=p.read_bytes().replace(b'\0',b' ').decode(errors='replace')
        if ('AuxiliaryRealMarkedFiniteCutoffExtendedBudget.lean' in c or 'AuxiliaryRealMarkedCutoffExtendedBudget.lean' in c or 'OwnedAudit.lean' in c) and (' lean ' in c or '/lean ' in c):
            out['processObservation'].append({'pid':int(p.parent.name),'command':c[:800],'affinity':sorted(os.sched_getaffinity(int(p.parent.name)))})
    except (OSError,ProcessLookupError):pass
print(json.dumps(out,ensure_ascii=False))
'''
request={'action':'exec','command':"taskset -c 44-47 python3 -c "+__import__('shlex').quote(remote),'stdin':json.dumps({'expected':expected,'receipts':receipts}),'timeout':60}
result=send_request(request)
if result.get('ok') is False or result.get('exit_code') != 0:
    (HERE/'fresh-readonly-observation-failure.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result)); raise SystemExit(1)
data=json.loads(result['stdout'])
logs=data.pop('rawLogs')
(HERE/'fresh-readonly-observation.json').write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({'atUTC':data['atUTC'],'affinity':data['affinity'],'branch':data['branch'],'head':data['head'],'tree':data['tree'],
 'bindingCount':len(data['bindings']),'mismatches':[v for v in data['bindings'].values() if not v['matchesExpected']],
 'units':data['units'],'native':data['native'],'processObservation':data['processObservation'],'RAW_LOGS_DISPLAY_ONLY_NOT_STORED_LOCALLY':logs},ensure_ascii=False,indent=2))
