import json, hashlib, pathlib, sys, re

ROOT = pathlib.Path('C:/game/shao lean')
OWN = ROOT/'drafts/oq56/unit256/source-review-01'
AUTHOR = ROOT/'drafts/oq56/unit256/author-01'
def read(p): return pathlib.Path(p).read_text(encoding='utf-8')
def load(p): return json.loads(read(p))
def sha(b): return hashlib.sha256(b).hexdigest()
def bind(p):
    p=pathlib.Path(p); b=p.read_bytes()
    return {'path':p.as_posix(),'sha256':sha(b),'bytes':len(b),'LF':b.count(b'\n')}
mode=sys.argv[1]
if mode=='shape':
    b=load(AUTHOR/'BINDING-TYPES.json')
    print(json.dumps(b['allRcasedIntroducedObtainedFunextNames'][100],ensure_ascii=False,indent=2))
elif mode=='contracts':
    p=load(AUTHOR/'PRODUCER-TYPES.json')
    for key in sys.argv[2:]:
        c=p['contracts'][key]
        print('CONTRACT',key, json.dumps({k:v for k,v in c.items() if k!='declaration'},ensure_ascii=False))
        print(c['declaration'])
elif mode=='bindings':
    b=load(AUTHOR/'BINDING-TYPES.json')
    start,end=map(int,sys.argv[2:4])
    for x in b['allRcasedIntroducedObtainedFunextNames'][start:end]:
        print(f"{x['sourceLine']}:{x['name']} [scope≤{x['lexicalScopeEndLine']}]\n{x['fullType']}\nORIGIN {x['completeRHSOrProjection']}")
elif mode=='inferred':
    p=load(AUTHOR/'PRODUCER-TYPES.json')
    for key in sys.argv[2:]:
        print('APPLICATION',key)
        print(json.dumps(p['applications'][key],ensure_ascii=False,indent=2))
elif mode=='verify':
    s=(AUTHOR/'OriginalLevelDependentLiteralWeightedConsumer.lean').read_bytes()
    freeze=ROOT/'drafts/oq56/unit256/freeze-02'
    pre=(freeze/'FROZEN-PREAMBLE.txt').read_bytes(); head=(freeze/'FROZEN-HEAD.txt').read_bytes()
    proof=(AUTHOR/'PROOF-BODY.txt').read_bytes(); closing=(freeze/'FROZEN-CLOSING.txt').read_bytes()
    assert s==pre+head+b':= by\n'+proof+closing
    oldpre=(ROOT/'drafts/oq56/unit256/freeze-01/FROZEN-PREAMBLE.txt').read_bytes()
    old=(ROOT/'drafts/oq56/unit256/preamble-amendment-01/pre-amendment-candidate.lean').read_bytes()
    assert old==oldpre+s[len(pre):]
    assert old==(AUTHOR/'preserved-freeze01/OriginalLevelDependentLiteralWeightedConsumer.lean').read_bytes()
    assert head==(ROOT/'drafts/oq56/unit256/freeze-01/FROZEN-HEAD.txt').read_bytes()
    assert proof==(AUTHOR/'preserved-freeze01/PROOF-BODY.txt').read_bytes()
    assert not s.startswith(b'\xef\xbb\xbf') and b'\r' not in s and s.endswith(b'\n') and not s.endswith(b'\n\n')
    intake=load(ROOT/'drafts/oq56/unit256/parent-intake-01.json')
    verified=[]
    for path,v in intake['bindings'].items():
        a=bind(path); assert a['sha256']==v['sha256'] and a['bytes']==v['bytes'],path
        verified.append(a)
    l=load(AUTHOR/'LOCAL-CONTEXTS.json')
    for x in l['declarations']+l['binderCommands']:
        z=x['slice']; bs=s[z['startByte']:z['endByteExclusive']]
        assert bs.decode('utf-8')==z['utf8'] and sha(bs)==z['sha256']
    assert len(l['declarations'])==278 and len(l['binderCommands'])==27
    p=load(AUTHOR/'PRODUCER-TYPES.json')
    for key,c in p['contracts'].items():
        path=c['input']['path']; lines=read(path).splitlines(keepends=True)
        actual=''.join(lines[c['sourceStartLine']-1:c['sourceEndLine']])
        # Inventory declaration intentionally omits the final := by delimiter.
        actual_head=actual.rsplit(':= by',1)[0].strip()
        assert actual_head==c['declaration'].strip(),key
    old_contract=p['contracts']['qualified255']['declaration']
    old_packet=old_contract.split('IsProbabilityMeasure μ₀ ∧',1)[1].strip()
    new_packet=''.join(s.decode('utf-8').splitlines(keepends=True)[34:289]).strip()
    assert new_packet.startswith('(') and new_packet.endswith(') ∧')
    new_packet=new_packet[1:-3].strip()
    assert re.sub(r'\s+','',old_packet)==re.sub(r'\s+','',new_packet)
    release=load(AUTHOR/'FINALWRITE.json')
    assert all(release[k]==0 for k in ['writers','heavy','inflight','pendingExternal','children','uncertain'])
    assert bind(AUTHOR/'FINALWRITE.json')['sha256']=='8c17b37feaf3ad246e049c6c7300146284587d8bfca66137b86c8cf3a7a5374a'
    report={'schema':'unit256-independent-source-byte-verification-v1','source':bind(AUTHOR/'OriginalLevelDependentLiteralWeightedConsumer.lean'),'freezeAssemblyExact':True,'notationAmendmentOnlyExact':True,'priorProofAndHeadBytesExact':True,'firstPacketLiteralModuloOuterParenthesesAndWhitespace':True,'authorSixZeroVerified':True,'allIntakeBindingsVerified':len(verified),'sourceSlicesVerified':len(l['declarations'])+len(l['binderCommands']),'localDeclarations':len(l['declarations']),'binderCommands':len(l['binderCommands']),'completePatternBindings':len(load(AUTHOR/'BINDING-TYPES.json')['allRcasedIntroducedObtainedFunextNames']),'allFiveContractSourceSlicesExact':True,'bindings':verified,'Lean':0,'server':0,'network':0}
    (OWN/'SOURCE-BYTE-CHECK.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k!='bindings'},ensure_ascii=False,indent=2))
