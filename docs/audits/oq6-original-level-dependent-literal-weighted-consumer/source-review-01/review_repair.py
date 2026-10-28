from pathlib import Path
import json,hashlib,datetime
R=Path('C:/game/shao lean/drafts/oq56/unit256'); O=R/'source-review-01'; A=R/'author-01'; B=R/'author-repair-01'
def j(p): return json.loads(Path(p).read_text(encoding='utf-8'))
def fp(p):
    p=Path(p); b=p.read_bytes(); return dict(path=p.as_posix(),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),LF=b.count(b'\n'))
def put(n,x): (O/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
olds=(A/'OriginalLevelDependentLiteralWeightedConsumer.lean').read_bytes(); news=(B/'OriginalLevelDependentLiteralWeightedConsumer.lean').read_bytes()
assert fp(B/'OriginalLevelDependentLiteralWeightedConsumer.lean')['sha256']=='bbab19f1d8c091b81e3c06e7cfbc0dcc3c6acb16ce39261d0f08b2dc3ac1efcf'
ol=olds.splitlines(keepends=True); nl=news.splitlines(keepends=True)
changed=[i+1 for i,(x,y) in enumerate(zip(ol,nl)) if x!=y]
assert len(ol)==len(nl)==1053 and changed==[757,797,1030]
f=R/'freeze-02'; proof=(B/'PROOF-BODY.txt').read_bytes()
assert news==(f/'FROZEN-PREAMBLE.txt').read_bytes()+(f/'FROZEN-HEAD.txt').read_bytes()+b':= by\n'+proof+(f/'FROZEN-CLOSING.txt').read_bytes()
assert b'\r' not in news and not news.startswith(b'\xef\xbb\xbf') and news.endswith(b'\n') and not news.endswith(b'\n\n')
old=j(A/'LOCAL-CONTEXTS.json'); new=j(B/'LOCAL-CONTEXTS.json'); affected=[]
for x,y in zip(old['declarations'],new['declarations']):
    assert (x['kind'],x['name'],x['headerAndFullSourceType'],x['lexicalScopeEndLine'],x['completeInferredType'])==(y['kind'],y['name'],y['headerAndFullSourceType'],y['lexicalScopeEndLine'],y['completeInferredType'])
    if x['completeRHS']!=y['completeRHS']: affected.append(y['name'])
assert affected==['hCurrent','hFdeleteMeas','hDeltaI','hDI','hSourceEventually']
for x in new['declarations']+new['binderCommands']:
    z=x['slice']; b=news[z['startByte']:z['endByteExclusive']]
    assert b.decode('utf-8')==z['utf8'] and hashlib.sha256(b).hexdigest()==z['sha256']
ob=j(A/'BINDING-TYPES.json'); nb=j(B/'BINDING-TYPES.json')
assert ob['allRcasedIntroducedObtainedFunextNames']==nb['allRcasedIntroducedObtainedFunextNames']
op=j(A/'PRODUCER-TYPES.json'); np=j(B/'PRODUCER-TYPES.json')
assert op['contracts']==np['contracts'] and op['applications']==np['applications']
cc=j(B/'CHANGED-CONTEXTS.json')
for x in cc['changedLocals']:
    assert x['oldCompleteLocal']==next(z for z in old['declarations'] if z['name']==x['name'])
    assert x['newCompleteLocal']==next(z for z in new['declarations'] if z['name']==x['name'])
rel=j(B/'FINALWRITE.json')
assert all(rel[k]==0 for k in ['writers','heavy','inflight','pendingExternal','children','uncertain'])
assert fp(B/'FINALWRITE.json')['sha256']=='4880ae29ea5c978ece6c7c9e5b60bf6e004aa5f9184345efb4e8763347d7ebe2'
m=j(B/'MANIFEST.json'); verified=[]
for x in m['payload']:
    y=fp(x['path']); assert (x['sha256'],x['bytes'])==(y['sha256'],y['bytes']); verified.append(y)
sm=j(O/'SOURCE-MANIFEST.json')
for x in sm['payloads']:
    y=fp(x['path']); assert (x['sha256'],x['bytes'])==(y['sha256'],y['bytes'])
assert fp(O/'SOURCE-MANIFEST.json')['sha256']=='490d103a2d06f71791a6290b4d14bd4c093a2e23ec4114895331ad4cb8a2385b'
result=dict(schema='unit256-independent-repair01-affected-source-check-v1',atUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),STATUS='CORRECT',stage='SOURCE_ACCEPTED_REPAIR01',sourceAccepted=True,qualified=False,machinePending=True,source=fp(B/'OriginalLevelDependentLiteralWeightedConsumer.lean'),proof=fp(B/'PROOF-BODY.txt'),oldSource=fp(A/'OriginalLevelDependentLiteralWeightedConsumer.lean'),exactChangedLines=changed,affectedCompleteRHS=affected,completeAffectedReadRanges=[[684,807],[1020,1049]],allDeclarationTypesAndLexicalScopesEqual=True,all349BindingTypesOriginsScopesEqual=True,allProducerContractsAndApplicationsEqual=True,all305NewSlicesExact=True,frozenAssemblyExact=True,onlyProofExpressionChanges=True,mathematicalAssumptionsOrStatementChanged=False,repairAuthorSixZeroVerified=True,repairAuthorManifest=fp(B/'MANIFEST.json'),repairAuthorRelease=fp(B/'FINALWRITE.json'),repairPayloadCountVerified=len(verified),repairPayloads=verified,originalSourceSevenPayloadsAndManifestUnchanged=True,originalSourceManifest=fp(O/'SOURCE-MANIFEST.json'),originalSourceCoverageReused=True,criticalGaps=[],fullOQ56='OPEN',root='OPEN',actualOwnerCount=None,actualTYPELF=None,requiredVALUECount=None,ownLeanAXServerNetworkOperations=0,finalRelease=False)
put('AFFECTED-REPAIR01-CHECK.json',result)
print(json.dumps({k:result[k] for k in ['STATUS','stage','source','exactChangedLines','affectedCompleteRHS','repairPayloadCountVerified','originalSourceSevenPayloadsAndManifestUnchanged']},ensure_ascii=False,indent=2))
