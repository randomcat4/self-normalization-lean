import sys
sys.dont_write_bytecode = True
from pathlib import Path
import hashlib, json, re, datetime

ROOT = Path('C:/game/shao lean')
REVIEW = ROOT / 'drafts/c12-lane/auxiliary-real-marked-cutoff-inverse-final-review-v1'
PACKETS = [ROOT / ('drafts/c12-lane/' + x) for x in [
    'auxiliary-real-marked-cutoff-inverse-v1', 'auxiliary-real-marked-finite-cutoff-budget-v1']]

def digest(data):
    return {'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}

def put(name, obj):
    p = REVIEW / name
    assert not p.exists(), p
    p.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + '\n', encoding='utf-8', newline='\n')

def frozen(source):
    lines = source.splitlines(keepends=True)
    starts = [i for i,l in enumerate(lines) if re.match(r'(private )?theorem ',l)]
    out = ''.join(lines[:starts[0]])
    for start in starts:
        stop = next(i+1 for i in range(start,len(lines)) if ':= by' in lines[i])
        out += ''.join(lines[start:stop]) + '\n'
    out += next(l for l in reversed(lines) if l.startswith('end '))
    return out.encode()

def local():
    bindings, slices, checks, counts = {}, [], [], []
    for packet in PACKETS:
        for p in packet.iterdir():
            if p.is_file(): bindings[str(p)] = digest(p.read_bytes())
        receipt = json.loads((packet/'receipt.json').read_text())
        source = (packet/(receipt['module'].split('.')[-1]+'.lean')).read_bytes()
        f = frozen(source.decode('utf-8'))
        checks.append({'module': receipt['module'], 'sourceMatchesReceipt': digest(source)['sha256']==receipt['sourceSHA256'],
           'freezeMatchesReconstructed': f==(packet/'frozen.lean.txt').read_bytes(),
           'freezeSHA256':digest(f)['sha256'], 'noBOM':not source.startswith(b'\xef\xbb\xbf'), 'CRCount':source.count(b'\r'),
           'forbiddenTokens':re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',source.decode()),
           'receiptBindings': all(bindings.get(str(packet/n),{}).get('sha256')==v['sha256'] for n,v in receipt['artifacts'].items() if (packet/n).exists())})
        contract = json.loads((packet/'consumed-interface-bindings.json').read_text())
        for row in contract['interfaces']:
            export=Path(row['path']).read_bytes()
            subset=export[row['offset']:row['offset']+row['bytes']]
            data=(packet/row['file']).read_bytes()
            bindings[str(Path(row['path']))]=digest(export)
            slices.append(dict(row, exportMatch=digest(export)['sha256']==row['sourceExportSHA256'],
                 exactSlice=subset==data, sliceMatch=digest(subset)['sha256']==row['sliceSHA256']))
        owner=json.loads((packet/'owned-audit.json').read_text())
        names=[x['name'] for x in owner['module_owned_constants']]
        payload=(packet/'actual-owned-types.txt').read_bytes()
        actualNames=re.findall(rb'^TARGET_DECL (\S+) KIND',payload,re.M)
        counts.append({'module':receipt['module'],'names':names,'owned':len(names),
          'theorems':sum(x['kind']=='theorem' for x in owner['module_owned_constants']),
          'private':sum(x.startswith('_private.') for x in names),'public':sum(not x.startswith('_private.') for x in names),
          'nonTheorems':sum(x['kind']!='theorem' for x in owner['module_owned_constants']),
          'typeBytes':len(payload),'typeNamesEqual':names==[n.decode() for n in actualNames],
          'noEllipsis':'…' not in payload.decode() and '...' not in payload.decode(),
          'valueBytes':(packet/'actual-definition-values.txt').stat().st_size,
          'axioms':{x['name']:x['axioms'] for x in owner['module_owned_constants']}})
    old=[]
    for folder in ['auxiliary-real-marked-moments-final-review-v1','auxiliary-real-marked-finite-cutoff-inverse-final-review-v1']:
        d=ROOT/'drafts/c12-lane'/folder
        p=d/'parent-acceptance.json'; obj=json.loads(p.read_text()); bindings[str(p)]=digest(p.read_bytes())
        seals={}
        for key,name in [('fullReviewJSONSHA256','full-review.json'),('fullReviewMDSHA256','full-review.md'),('reviewReleaseSHA256','RELEASE.json'),('validationSHA256','validation.json')]:
            b=(d/name).read_bytes(); bindings[str(d/name)]=digest(b); seals[name]=digest(b)['sha256']==obj[key]
        old.append({'path':str(p),'binding':digest(p.read_bytes()),'status':obj['status'],'exactBindings':obj['exactBindings'],'seals':seals})
    for path in ['coordination/common-suffix-moment-budgets-root-qualification.json','coordination/common-suffix-scalar-interfaces-root-qualification.json',
                 'coordination/restart-20261025/RESUMPTION-ACTIVATION.json',
                 'drafts/c2-residual-rare-suffix-production/private-helper-heads-request01.lean.txt']:
        p=ROOT/path; bindings[str(p)]=digest(p.read_bytes())
    for p in [REVIEW/'brief.txt', REVIEW/'RUNTIME-ACK.json', REVIEW/'USER-PAUSE-CHECKPOINT.md',REVIEW/'USER-PAUSE-RELEASE.json']:
        bindings[str(p)]=digest(p.read_bytes())
    result={'atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'bindings':bindings,'sourceChecks':checks,
       'consumedSlices':slices,'derivedCounts':counts,'oldQualifications':old}
    put('local-binding-observation.json',result)
    print(json.dumps({k:v for k,v in result.items() if k!='bindings'},ensure_ascii=False,indent=2))

def remote(code, destination=None):
    sys.path.insert(0,str(ROOT/'tools'))
    from transport_client import send_request
    request={'action':'exec','command':'taskset -c 44-47 python3 -B -','timeout':90,'stdin':code}
    response=send_request(request)
    if response.get('ok') is False or response.get('exit_code',0)!=0:
        print(json.dumps(response)); return
    out=response.get('stdout',response.get('output',''))
    if not out:
        print(json.dumps(response)); return
    data=json.loads(out)
    display=data.pop('display',{})
    if destination: put(destination,data)
    summary={k:v for k,v in data.items() if k!='bindings'}
    summary['bindingCount']=len(data.get('bindings',{}))
    print(json.dumps(summary,ensure_ascii=False,indent=2))
    for key,value in display.items():
        print('\n'+key+'\n'+value)

if __name__=='__main__':
    if sys.argv[1]=='local': local()
    elif sys.argv[1]=='remote': remote(Path(sys.argv[2]).read_text(encoding='utf-8'),sys.argv[3] if len(sys.argv)>3 else None)
