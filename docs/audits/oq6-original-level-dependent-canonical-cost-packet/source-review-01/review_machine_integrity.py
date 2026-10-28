from pathlib import Path
import json, hashlib, re
from collections import Counter
from datetime import datetime, timezone

B=Path('C:/game/shao lean/drafts/oq56/unit255')
D=B/'owner-evidence-01'; L=B/'lead-execution-01'; OUT=B/'source-review-01'
def j(p): return json.loads(Path(p).read_text(encoding='utf-8'))
def h(b): return hashlib.sha256(b).hexdigest()
def fp(p):
    p=Path(p); b=p.read_bytes()
    return dict(path=p.as_posix(),sha256=h(b),bytes=len(b))
def dump(n,v): (OUT/n).write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
def same(a,b):
    for k in ('sha256','bytes'):
        assert a[k]==b[k],(k,a,b)
    if 'mtime_ns' in a and 'mtime_ns' in b: assert a['mtime_ns']==b['mtime_ns']
    if 'physical_path' in a and 'physical_path' in b: assert a['physical_path']==b['physical_path']
    return True
def nested(p):
    x=j(L/p)
    return x,json.loads(x['stdout'])

m=j(D/'actual-owned-metadata.json'); s=j(D/'native-kernel-and-all-owner-audit-summary.json'); bind=j(D/'server-metadata-binding.json')
np,npv=nested('native-prepare-result.json'); nt,ntv=nested('native01-transport-result.json')
ap,apv=nested('audit-prepare-result.json'); at,atv=nested('audit01-transport-result.json')
nd=j(L/'native01-DISPATCHED.json'); ad=j(L/'audit01-DISPATCHED.json')
proj=j(L/'native01-actual-projection.json'); wc=j(L/'native01-warning-classification.json')
norm=j(L/'normalize-result.json'); norm_lines=norm['stdout'].splitlines(); nr=json.loads(norm_lines[0]); nw=json.loads(norm_lines[1])
tr=j(L/'normalized-evidence-transfer-binding.json')
localfiles=[]
for v in tr['files']:
    actual=fp(v['local']); same(v,actual); same(nr[v['key']],v); localfiles.append(actual)
same(bind['metadata'],fp(D/'actual-owned-metadata.json'))
same(bind['summary'],fp(D/'native-kernel-and-all-owner-audit-summary.json'))
same(m['source'],s['source']);same(m['source'],bind['source']);same(m['source'],npv['source'])
same(m['source'],fp(B/'author-01/OriginalLevelDependentCanonicalCostPacket.lean'))
assert (m['source']['sha256'],m['source']['bytes'])==(proj['input']['sha256'],proj['input']['bytes'])
same(m['source'],wc['source'])
assert npv['objectBefore'] is None
for o in (s['object'],bind['object'],proj['object_after'],apv['firstOriginalO'],ad['sameFirstO']): same(m['object'],o)
assert m['object']['sha256']=='5aa95b132fed55b6fbe546b21b65a244c035ff4d9915572ba1aaa7404da463eb'
assert m['object']['bytes']==6126920 and m['object']['mtime_ns']=='1793201957910253979'
for v in (npv['config'],nd['config'],proj['config']): same(v,s['native01']['config'])
for v in (apv['config'],ad['config']): same(v,s['ownedAudit01']['config'])
for v in (ntv['receipt'],bind['nativeReceipt'],wc['nativeReceipt']): same(v,s['native01']['receipt'])
for v in (atv['receipt'],bind['auditReceipt'],m['auditReceipt']): same(v,s['ownedAudit01']['receipt'])
for k in ('stdout','stderr'):
    same(ntv[k],s['native01'][k]); same(proj[k],s['native01'][k]);same(atv[k],s['ownedAudit01'][k])
same(bind['sourceRunEndedReceipt'],ntv['run_ended'])
assert np['exit_code']==ap['exit_code']==norm['exit_code']==0
assert nt['exit_code']==at['exit_code']==1
assert proj['exit_code']==s['native01']['actualExitCode']==s['ownedAudit01']['actualExitCode']==0
assert ntv['all_owned_group_ended'] and atv['all_owned_group_ended'] and s['allOwnedProcessesEnded']
assert proj['all_owned_group_ended'] and proj['beforeAfterEqual'] and proj['preservation_equal']
assert not proj['timed_out'] and not proj['cleanup_events'] and not proj['final_live_owned_members']
assert proj['ownership_issue'] is None and proj['post_error'] is None
assert s['native01']['protectedDerived']==proj['recordsDerived']==27035
assert s['ownedAudit01']['protectedDerived']==27043
assert s['native01']['beforeAfterExact'] and s['ownedAudit01']['beforeAfterExact']
assert s['ownedAudit01']['no_o'] and s['ownedAudit01']['own_object_import']
assert all(x is False for x in [proj['success'],ntv['success'],atv['success'],s['native01']['strictWrapperSuccess'],s['ownedAudit01']['strictWrapperSuccess']])
assert s['native01']['FIRSTEMPTY'] is None and s['native01']['FIRSTEMPTYIsReturnedRunnerField'] is False
assert s['native01']['requireEmptyStdout'] is True
assert not s['ownLean'] and not bind['ownLean']

entries=m['entries']; assert len(entries)==m['actualOwnerCount']==8
assert len({v['name'] for v in entries})==8
alltypes='';allvalues='';raw='';ax=Counter();owners=[];line=1
for e in entries:
    meta=json.loads(e['rawOwnedJSON'])
    assert set(meta)=={'axioms','bodyExpressionPresent','components','constantKind','isTheorem','levelParams','name'}
    assert all(meta[k]==e[k] for k in meta)
    assert '.'.join(c['value'] for c in e['components'])==e['name']
    assert e['constantKind']=='thmInfo' and e['isTheorem'] and e['bodyExpressionPresent']
    assert 'value' not in e
    assert set(e['axioms'])<={'propext','Classical.choice','Quot.sound'}
    assert len(e['axioms'])==len(set(e['axioms']))
    assert e['typeLines']==len(e['type'].splitlines()) and e['type'].endswith('\n')
    assert not any(z in e['type'] for z in ['⋯','...','<elided>'])
    ax.update(e['axioms'])
    alltypes+=e['name']+' : '+e['type']
    raw+='OQ56_OWNED_JSON '+e['rawOwnedJSON']+'\n'
    raw+='OQ56_OWNED_TYPE '+e['name']+' : '+e['type']
    owners.append(dict(name=e['name'],kind=e['constantKind'],levelParams=e['levelParams'],firstLine=line,lastLine=line+e['typeLines']-1,typeLines=e['typeLines'],typeSHA256=h(e['type'].encode()),axioms=e['axioms'],fullTypeRead=True,requiredVALUE=False))
    line+=e['typeLines']
raw+=m['rawOwnedCountLine'];rb=raw.encode('utf-8')
assert alltypes.encode()==(D/'actual-owned-types.txt').read_bytes()
assert allvalues.encode()==(D/'actual-owned-values.txt').read_bytes()==b''
assert line-1==s['TYPElines']==nr['TYPElines']==5101
assert m['allTheoremCount']==s['actualTheorems']==8 and m['nonTheoremCount']==m['nonTheoremFullValueCount']==s['actualNonTheorems']==0
assert dict(ax)==s['axiomOccurrences']==nr['axiomOccurrences']==tr['axiomOccurrences']=={'propext':8,'Classical.choice':2,'Quot.sound':2}
assert len(rb)==m['rawStdoutBytes']==bind['rawStdoutBytes']==s['ownedAudit01']['stdout']['bytes']==756181
assert h(rb)==m['rawStdoutSHA256']==bind['rawStdoutSHA256']==s['ownedAudit01']['stdout']['sha256']=='391a82d11937d6092a3c5bcdace90799c5b8bad5ddf3a68ce0f6c90c91de8024'
assert m['rawOwnedCountLine']=='OQ56_OWNED_COUNT 8\n'
assert m['ownerDiscovery']=='actual env.getModuleIdxFor? anchor then ALL env.constants without namespace filter'

diag=proj['diagnosticStdout']; err=proj['diagnosticStderr']
assert h(diag.encode())==s['native01']['stdout']['sha256'] and len(diag.encode())==3795
assert h(err.encode())==s['native01']['stderr']['sha256']==s['ownedAudit01']['stderr']['sha256'] and len(err.encode())==134
blocks=[x for x in re.split(r'(?m)(?=^Shao/OQ6/OriginalLevelDependentCanonicalCostPacket[.]lean:\d+:\d+:)',diag) if ': warning' in x]
assert len(blocks)==wc['sourceWarnings']==nw['sourceWarnings']==11
assert wc==nw and wc['sourceErrors']==0
for x,e in zip(blocks,wc['warnings']):
    assert h(x.encode())==e['completeMessageUTF8SHA256'] and len(x.encode())==e['completeMessageBytes']
assert len(re.findall(r': error(?:\([^)]*\))?:',diag))==0
audit=(L/'owned-object-audit-input.lean').read_bytes(); same(fp(L/'owned-object-audit-input.lean'),apv['auditSource'])
old=(B.parent/'unit254/lead-execution-01/owned-object-audit-input.lean').read_bytes()
assert old.replace(b'OriginalLevelDependentCanonicalCoding',b'OriginalLevelDependentCanonicalCostPacket').replace(b'actual_original_level_dependent_canonical_normalized_coding',b'actual_original_level_dependent_canonical_cost_packet')==audit
assert audit.count(b'\n')==62 and len(audit)==2800
sm=j(OUT/'SOURCE-MANIFEST.json')
for e in sm['payloads']:
    same(e,fp(e['path']))
assert sm['sourceAccepted'] and not sm['qualified'] and sm['machinePending']
check=dict(schema='unit255-independent-complete-machine-binding-check-v1',atUTC=datetime.now(timezone.utc).isoformat(),status='PASS_EXACT_BINDINGS',source=m['source'],firstOriginalO=m['object'],nativeReceipt=s['native01']['receipt'],auditReceipt=s['ownedAudit01']['receipt'],nativeConfig=s['native01']['config'],auditConfig=s['ownedAudit01']['config'],nativeActualRC=0,auditActualRC=0,transportRC=[1,1],strictWrapperSuccess=[False,False],sourceErrors=0,sourceWarnings=11,protectedRecords=[27035,27043],allOwnedNaturallyEnded=True,allActualOwners=owners,actualOwned=8,actualTheorems=8,actualNonTheorems=0,TYPELF=5101,requiredVALUECount=0,axiomOccurrences=dict(ax),allAXWhitelisted=True,rawStdoutReconstruction=dict(inMemoryOnly=True,bytes=len(rb),sha256=h(rb),lossless=True),metadataTYPEConcatenationExact=True,allFiveTransferredHashesExact=True,nativeDiagnosticBytesHashesAndMessagesExact=True,auditInputExactTemplateModuleAnchorReplacement=True,sourceSevenPayloadsAndManifestRemainUnchanged=True,noSourceProofRecompile=True,newReviewLeanAXServerOperations=0)
dump('FINAL-MACHINE-CHECK.json',check)
paths=[*D.glob('*'),*L.glob('*.json'),L/'owned-object-audit-input.lean',L/'reused-normalizer-adaptation.py',OUT/'SOURCE-MANIFEST.json']
dump('FINAL-HASH-BINDINGS.json',[fp(p) for p in paths if p.is_file()])
print(json.dumps({k:check[k] for k in ('status','actualOwned','TYPELF','requiredVALUECount','axiomOccurrences','rawStdoutReconstruction','sourceSevenPayloadsAndManifestRemainUnchanged')},ensure_ascii=False))
