import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,datetime
root=Path('C:/game/shao lean');review=root/'drafts/c12-lane/auxiliary-real-marked-cutoff-inverse-final-review-v1'
local=json.loads((review/'local-binding-observation.json').read_text());remote=json.loads((review/'remote-binding-observation.json').read_text())
checks={};bindings={};contracts=[]
def sha(p):
    b=p.read_bytes();bindings[str(p)]={'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)};return bindings[str(p)]['sha256']
expected={'coordination/common-suffix-moment-budgets-root-qualification.json':'3999793eb1e77bb679c4b8a5d7e1220392ed9ae01d09cc7f0064da14f6bce4f3',
          'coordination/common-suffix-scalar-interfaces-root-qualification.json':'2a2ca77941fa9500843582dc57681d01260abfd2abae7f0d1cab331e6ceb6c26',
          'coordination/restart-20261025/RESUMPTION-ACTIVATION.json':'e56beb0e19419eaad915eda38aab0a40ed4175d5101d5ba2b1b153285d1fd021',
          'drafts/c2-residual-rare-suffix-production/private-helper-heads-request01.lean.txt':'7a8c467528607017a7a55bb8b67f9c15b45e7642f5ceb7ecc55280ea04049939'}
for path,h in expected.items():checks[path]=sha(root/path)==h
for filename,names in [
 ('common-suffix-moment-budgets',['Shao.Probability.iid_marked_cutoff_inverse_moments','Shao.Probability.raw_gaussian_damped_coordinate_factors']),
 ('common-suffix-scalar-interfaces',['Shao.Probability.SourceSuffixScalarInterfaces.inverse_laplace'])]:
    q=json.loads((root/('coordination/'+filename+'-root-qualification.json')).read_text());report=q['fresh_complete_independent_report']
    checks[report['path']]=sha(root/report['path'])==report['sha256']
    jp=report.get('JSON',report.get('structuredPath'));jh=report.get('JSON_sha256',report.get('structuredSHA256'))
    checks[jp]=sha(root/jp)==jh
    mp=root/q['qualifiedOwnerMap'];checks[str(mp)]=sha(mp)==q['qualifiedOwnerMapSHA256']
    owner=json.loads(mp.read_text());rows=[r for r in owner['records'] if r.get('name') in names]
    checks[filename+' consumed names qualified']=set(r.get('name') for r in rows)==set(names)
    checks[filename+' canonical remote source']=remote['bindings'][q['source_path']]['sha256']==q['source_sha256']
    localSource=root/q['local_source'];checks[str(localSource)]=sha(localSource)==q['source_sha256']
    importPath='/root/rivermind-data/shao-lean-20261021/workspaces/c12-bridge-domination-v71/.lake/build/lib/lean/'+q['module'].replace('.','/')+'.olean'
    checks[filename+' import object']=remote['bindings'][importPath]['sha256']==q['object_sha256']
    contracts.append({'qualification':filename,'qualified':q['qualifiedForSourceBoundConsumption'],'consumedNames':rows})
for p,b in local['bindings'].items():
    if p.endswith('receipt.json') and '/auxiliary-real-marked-' in p.replace('\\','/') and 'final-review' not in p:
        packet=Path(p).parent;r=json.loads(Path(p).read_text())
        for name,artifact in r['artifacts'].items():
            if (packet/name).exists():checks['local-remote '+str(packet/name)]=sha(packet/name)==remote['bindings'][artifact['remotePath']]['sha256']
        checks['receiptRemote '+r['module']]=b['sha256']==remote['bindings']['/root/rivermind-data/shao-lean-20261021/outputs/c12-'+ ('auxiliary-real-marked-cutoff-inverse-v71' if 'Finite' not in r['module'] else 'auxiliary-real-marked-finite-cutoff-budget-v71')+'/receipt.json']['sha256']
result={'atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'checks':checks,'allPass':all(checks.values()),'bindings':bindings,'qualifiedContracts':contracts}
p=review/'qualification-binding-observation.json';assert not p.exists();p.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({'allPass':result['allPass'],'checkCount':len(checks),'failures':[k for k,v in checks.items() if not v],'qualifiedContracts':contracts},ensure_ascii=False,indent=2))
