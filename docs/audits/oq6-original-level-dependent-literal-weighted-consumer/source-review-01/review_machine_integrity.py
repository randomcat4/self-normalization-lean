"""Local-only adaptation of accepted unit255 independent machine-binding checker."""
from pathlib import Path
import json,hashlib,re
from collections import Counter
from datetime import datetime,timezone
B=Path('C:/game/shao lean/drafts/oq56/unit256'); D=B/'owner-evidence-01'; L=B/'lead-execution-01'; O=B/'source-review-01'
def j(p): return json.loads(Path(p).read_text(encoding='utf-8'))
def h(b): return hashlib.sha256(b).hexdigest()
def fp(p):
    p=Path(p); b=p.read_bytes(); return dict(path=p.as_posix(),sha256=h(b),bytes=len(b))
def same(a,b):
    for k in ['sha256','bytes']: assert a[k]==b[k],(k,a,b)
    if 'physical_path' in a and 'physical_path' in b:
        assert a['physical_path']==b['physical_path']
        if 'mtime_ns' in a and 'mtime_ns' in b: assert a['mtime_ns']==b['mtime_ns']
def nested(name):
    a=j(L/name); return a,json.loads(a['stdout'])
def put(name,x): (O/name).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
m=j(D/'actual-owned-metadata.json'); s=j(D/'native-kernel-and-all-owner-audit-summary.json'); b=j(D/'server-metadata-binding.json')
np,npv=nested('native03-prepare-result.json'); nt,ntv=nested('native03-transport-result.json')
ap,apv=nested('audit-prepare-result.json'); at,atv=nested('audit01-transport-result.json')
nd=j(L/'native03-DISPATCHED.json'); ad=j(L/'audit01-DISPATCHED.json')
proj=j(L/'native03-actual-projection.json'); wc=j(L/'native03-warning-classification.json')
norm=j(L/'normalizer-result.json'); nr,nw=[json.loads(x) for x in norm['stdout'].splitlines()]
server=j(L/'normalized-evidence-server-projection.json'); transfer=j(L/'normalized-evidence-transfer-binding.json')
keymap={'actual-owned-types.txt':'types','actual-owned-values.txt':'values','actual-owned-metadata.json':'metadata','native-kernel-and-all-owner-audit-summary.json':'summary','server-metadata-binding.json':'binding'}
for x in transfer['files']:
    actual=fp(x['local']); same(x,actual); k=keymap[Path(x['local']).name]
    for z in [nr[k],server[k],x['serverPhysical']]: same(z,actual)
    same(nr[k],x['serverPhysical']); same(server[k],x['serverPhysical'])
same(b['metadata'],fp(D/'actual-owned-metadata.json'));same(b['summary'],fp(D/'native-kernel-and-all-owner-audit-summary.json'))
for x in [s['source'],b['source'],npv['source'],wc['source']]: same(m['source'],x)
same(m['source'],fp(B/'author-repair-01/OriginalLevelDependentLiteralWeightedConsumer.lean'))
assert m['source']['sha256']=='bbab19f1d8c091b81e3c06e7cfbc0dcc3c6acb16ce39261d0f08b2dc3ac1efcf'
assert nd['sourceSHA256']==m['source']['sha256'] and npv['noObjectBefore'] and not npv['ownLive']
provenance=j(L/'SOURCE-REPAIR01-APPLIED.json'); same(npv['sourceByteProvenance'],fp(L/'SOURCE-REPAIR01-APPLIED.json'))
same(provenance['afterUnqualifiedCanonical'],m['source']); assert provenance['onlyChangedSourceLines']==[757,797,1030]
assert npv['oldOriginalSourceCopies']==provenance['preservedExactOldSourceCopies']
for x in [s['object'],b['object'],proj['object_after'],apv['firstOriginalO'],ad['sameFirstO']]:same(m['object'],x)
assert (m['object']['sha256'],m['object']['bytes'],m['object']['mtime_ns'])==('eaa1ed560433249906bdcf5018f26d867297406da8d1dda0bc730d50c8ff8887',16609080,'1793205737583793091')
for x in [npv['config'],nd['config'],proj['config']]:same(x,s['native03']['config'])
for x in [apv['config'],ad['config']]:same(x,s['ownedAudit01']['config'])
for x in [ntv['receipt'],b['nativeReceipt'],wc['nativeReceipt'],proj['receipt']]:same(x,s['native03']['receipt'])
for x in [atv['receipt'],b['auditReceipt'],m['auditReceipt']]:same(x,s['ownedAudit01']['receipt'])
for k in ['stdout','stderr']:same(ntv[k],s['native03'][k]);same(atv[k],s['ownedAudit01'][k])
same(b['sourceRunEndedReceipt'],ntv['run_ended'])
assert np['exit_code']==ap['exit_code']==norm['exit_code']==0 and nt['exit_code']==at['exit_code']==1
assert proj['exit_code']==s['native03']['actualExitCode']==s['ownedAudit01']['actualExitCode']==0
assert ntv['all_owned_group_ended'] and atv['all_owned_group_ended'] and s['allOwnedProcessesEnded'] and proj['all_owned_group_ended']
assert proj['beforeAfterEqual'] and proj['preservation_equal'] and not proj['timed_out'] and not proj['cleanup_events'] and not proj['final_live_owned_members'] and not proj['ownLive']
assert proj['ownership_issue'] is None and proj['post_error'] is None
assert s['native03']['protectedDerived']==proj['recordsDerived']==27462 and s['ownedAudit01']['protectedDerived']==27472
assert s['native03']['beforeAfterExact'] and s['ownedAudit01']['beforeAfterExact']
assert s['ownedAudit01']['no_o'] and s['ownedAudit01']['own_object_import']
assert all(x is False for x in [proj['success'],ntv['success'],atv['success'],s['native03']['strictWrapperSuccess'],s['ownedAudit01']['strictWrapperSuccess']])
assert s['native03']['FIRSTEMPTY'] is None and not s['native03']['FIRSTEMPTYIsReturnedRunnerField'] and s['native03']['requireEmptyStdout']
assert not s['ownLean'] and not b['ownLean']
entries=m['entries']; assert len(entries)==m['actualOwnerCount']==2 and len({x['name'] for x in entries})==2
types=''; values=''; raw=''; ax=Counter(); owners=[]; line=1
for e in entries:
    r=json.loads(e['rawOwnedJSON']);assert set(r)=={'axioms','bodyExpressionPresent','components','constantKind','isTheorem','levelParams','name'}
    assert all(r[k]==e[k] for k in r) and '.'.join(x['value'] for x in e['components'])==e['name']
    assert e['constantKind']=='thmInfo' and e['isTheorem'] and e['bodyExpressionPresent'] and 'value' not in e
    assert set(e['axioms'])<={'propext','Classical.choice','Quot.sound'} and len(e['axioms'])==len(set(e['axioms']))
    assert e['typeLines']==len(e['type'].splitlines()) and e['type'].endswith('\n')
    assert not any(x in e['type'] for x in ['⋯','...','<elided>','failed to pretty print','sorryAx'])
    ax.update(e['axioms']); types+=e['name']+' : '+e['type']
    raw+='OQ56_OWNED_JSON '+e['rawOwnedJSON']+'\n'+'OQ56_OWNED_TYPE '+e['name']+' : '+e['type']
    owners.append(dict(name=e['name'],kind=e['constantKind'],levelParams=e['levelParams'],bodyExpressionPresent=True,firstLine=line,lastLine=line+e['typeLines']-1,typeLines=e['typeLines'],typeSHA256=h(e['type'].encode()),axioms=e['axioms'],fullTypeRead=True,requiredVALUE=False));line+=e['typeLines']
raw+=m['rawOwnedCountLine'];rb=raw.encode('utf-8')
assert types.encode()==(D/'actual-owned-types.txt').read_bytes() and values.encode()==(D/'actual-owned-values.txt').read_bytes()==b''
assert line-1==s['TYPElines']==nr['TYPElines']==7912
assert m['allTheoremCount']==s['actualTheorems']==2 and m['nonTheoremCount']==m['nonTheoremFullValueCount']==s['actualNonTheorems']==0
assert dict(ax)==s['axiomOccurrences']==nr['axiomOccurrences']==server['axiomOccurrences']=={'propext':2,'Quot.sound':2,'Classical.choice':1}
assert len(rb)==m['rawStdoutBytes']==b['rawStdoutBytes']==s['ownedAudit01']['stdout']['bytes']==1073794
assert h(rb)==m['rawStdoutSHA256']==b['rawStdoutSHA256']==s['ownedAudit01']['stdout']['sha256']=='d2c1d97fd22c132978e9d5976875158f52e5cdda295bb8911caf4a092478304a'
assert m['rawOwnedCountLine']=='OQ56_OWNED_COUNT 2\n' and m['ownerDiscovery']=='actual env.getModuleIdxFor? anchor then ALL env.constants without namespace filter'
diag=proj['diagnosticStdout'];err=proj['diagnosticStderr']
assert h(diag.encode())==s['native03']['stdout']['sha256'] and len(diag.encode())==6873
assert h(err.encode())==s['native03']['stderr']['sha256']==s['ownedAudit01']['stderr']['sha256'] and len(err.encode())==134
blocks=[x for x in re.split(r'(?m)(?=^Shao/OQ6/OriginalLevelDependentLiteralWeightedConsumer[.]lean:\d+:\d+:)',diag) if ': warning' in x]
assert len(blocks)==wc['sourceWarnings']==nw['sourceWarnings']==18 and wc==nw and wc['sourceErrors']==0
for x,e in zip(blocks,wc['warnings']):assert h(x.encode())==e['completeMessageUTF8SHA256'] and len(x.encode())==e['completeMessageBytes']
assert not re.findall(r': error(?:\([^)]*\))?:',diag)
audit=(L/'owned-object-audit-input.lean').read_bytes();same(fp(L/'owned-object-audit-input.lean'),apv['auditSource'])
prior=(B.parent/'unit255/lead-execution-01/owned-object-audit-input.lean').read_bytes()
assert prior.replace(b'OriginalLevelDependentCanonicalCostPacket',b'OriginalLevelDependentLiteralWeightedConsumer').replace(b'actual_original_level_dependent_canonical_cost_packet',b'actual_original_level_dependent_literal_weighted_consumer')==audit
for manifest in ['SOURCE-MANIFEST.json','AFFECTED-REPAIR01-MANIFEST.json']:
    sm=j(O/manifest)
    for e in sm['payloads']:same(e,fp(e['path']))
check=dict(schema='unit256-independent-complete-machine-binding-check-v1',atUTC=datetime.now(timezone.utc).isoformat(),status='PASS_EXACT_BINDINGS',source=m['source'],firstOriginalO=m['object'],nativeReceipt=s['native03']['receipt'],auditReceipt=s['ownedAudit01']['receipt'],nativeConfig=s['native03']['config'],auditConfig=s['ownedAudit01']['config'],nativeActualRC=0,auditActualRC=0,transportRC=[1,1],strictWrapperSuccess=[False,False],sourceErrors=0,sourceWarnings=18,protectedRecords=[27462,27472],allOwnedNaturallyEnded=True,allActualOwners=owners,actualOwned=2,actualTheorems=2,actualNonTheorems=0,TYPELF=7912,requiredVALUECount=0,axiomOccurrences=dict(ax),allAXWhitelisted=True,rawStdoutReconstruction=dict(inMemoryOnly=True,bytes=len(rb),sha256=h(rb),lossless=True),metadataTYPEConcatenationExact=True,allFiveTransferredHashesExact=True,nativeDiagnosticBytesHashesAndMessagesExact=True,auditInputExactTemplateModuleAnchorReplacement=True,sourceSevenPayloadsManifestAndAffectedPayloadsRemainUnchanged=True,sourceProofRecompileByReviewer=False,newReviewLeanAXServerOperations=0)
put('FINAL-MACHINE-CHECK.json',check)
paths=[*D.glob('*'),*L.glob('*.json'),L/'owned-object-audit-input.lean',L/'reused-normalizer-adaptation.py',O/'SOURCE-MANIFEST.json',O/'AFFECTED-REPAIR01-MANIFEST.json']
put('FINAL-HASH-BINDINGS.json',[fp(p) for p in paths if p.is_file()])
print(json.dumps({k:check[k] for k in ['status','actualOwned','TYPELF','requiredVALUECount','axiomOccurrences','rawStdoutReconstruction','sourceSevenPayloadsManifestAndAffectedPayloadsRemainUnchanged']},ensure_ascii=False,indent=2))
