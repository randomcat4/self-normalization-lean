"""Read-only local receipt reconciliation. No Lean, remote I/O, or dependency walk."""
from pathlib import Path
import json, hashlib, collections, datetime

W = Path('C:/game/shao lean')
OUT = W/'drafts/oq4/positive-boundary-studentized-final-review-v1'
B = W/'drafts/oq4/positive-boundary-studentized-execution-author-v1'
R = B/'round004'
def read(p): return json.loads(Path(p).read_text(encoding='utf-8'))
def metrics(p):
    b=Path(p).read_bytes()
    return dict(path=str(p).replace('\\','/'),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),LF=b.count(b'\n'),CR=b.count(b'\r'),UTF8BOM=b.startswith(b'\xef\xbb\xbf'))
def save(name,v): (OUT/name).write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
checked=[]
def bound(p,sha=None,size=None):
    m=metrics(p)
    if sha is not None: assert m['sha256']==sha,(str(p),m['sha256'],sha)
    if size is not None: assert m['bytes']==size,(str(p),m['bytes'],size)
    checked.append(m); return m

source=bound(B/'PositiveBoundaryStudentized.lean','1f927813d1b491180ff0f3a368d0a2202b9c67c6bf2c09148344c6b7ecf19db4',23311)
assert (source['LF'],source['CR'],source['UTF8BOM'])==(463,0,False)
assert (B/'PositiveBoundaryStudentized.lean').read_bytes()==(R/'Source.lean').read_bytes()
assert (R/'Source.lean').read_bytes()+b'\n'+(R/'audit-suffix.lean').read_bytes()==(R/'private/Shao/OQ4/PositiveBoundaryStudentized.lean').read_bytes()
combined=bound(R/'private/Shao/OQ4/PositiveBoundaryStudentized.lean','cd51b9d4a6869d6fbf5acede801348f3afec05dede06e905dac8ab2621ac9349')
for rel,sha in [('drafts/oq4/frozen-positive-boundary-studentized-formal-v2.lean.txt','dc3d23f2b2a36070bddb9c30885a403cf8dc950c6f490193c62cda6915f96445'),('drafts/oq4/frozen-positive-boundary-studentized-v2.md','d82f2443e867db02b370421ce39993995903c2e0b9ecf5f754c167832c0cd983'),('drafts/oq4/takeover-20261023/positive-boundary-studentized-freeze-180-v2.json','d7e0bc48a003edbb3ec3e221776bdbccdbedbb2abc24050795c05adb1def36a8'),('drafts/oq4/takeover-20261023/positive-boundary-studentized-seal-parent-verification-v1.json','52bc3eb6c6b63cc12b96ae2cca7a8767b0d6afd50470ca1b714da9980b8c2dc9')]: bound(W/rel,sha)
bound(B/'checkpoint-author184-active.json','1f91df66f8dabe1db753028d8b5dcdb5dfad7f9324eae961bfe17e46a7848925')
bound(R/'stable-manifest.json','d4feaed3f4b31830d49d3e54b7141875b702acccb4808d8cba4aea285608e99b')
bound(R/'source-bound-final-receipt.json','93480849e02092db1258911f3882afa2ddbabcb605e3c591d67194118790dbc3')
# Reuse the parent's already completed 117-file seal; verify the actual compact
# inputs used here, rather than repeat unchanged archival rounds.
for manifest in ['compact-export-manifest.json','runtime-recovery-export-manifest.json']:
    bound(R/manifest)
    for f in read(R/manifest)['files']: bound(R/f['file'],f['sha256'],f['bytes'])
owned=read(R/'owned-native.json'); old=read(R/'old-direct-consumption-index.json'); chains=read(R/'consumed-source-object-chains.json')
axes=read(R/'per-root-axioms.json')
assert len(owned)==61 and len({x['name'] for x in owned})==61
assert collections.Counter(x['kind'] for x in owned)==dict(theorem=57,definition=4)
assert sum(x['public'] for x in owned)==7 and sum(x['explicitPrivate'] for x in owned)==17
assert all(not x['unsafe'] and not x['partial'] and x['valueAvailable'] for x in owned)
allow={'propext','Classical.choice','Quot.sound'}
assert all(set(x['axioms'])<=allow for x in owned)
assert all(x['elaboratedTypeExplicit']==x['type'] and x['type'] for x in owned)
assert sum(bool(x['elaboratedValueExplicit']) for x in owned)==4
assert all(not x['opaqueValueExplicit'] for x in owned)
if isinstance(axes,dict):
    axrows=axes.get('allOwned',axes.get('rows',axes.get('roots',axes.get('perRoot',[]))))
else: axrows=axes
assert len(axrows)==61
assert {x['name'] for x in axrows}=={x['name'] for x in owned}
axby={x['name']:x for x in axrows}
assert all(set(x['axioms'])==set(axby[x['name']]['axioms']) for x in owned)
text='Actual positive boundary studentized owned interface: unfiltered environment difference\n'
for x in owned:
    text+='\n===== '+x['name']+' ['+x['kind']+'] =====\nTYPE\n'+x['type']
    if x['kind']=='definition': text+='\nFULL DEFINITION VALUE\n'+x['elaboratedValueExplicit']
    text+='\n'
assert text==(R/'owned-interface.txt').read_text(encoding='utf-8')
before=read(R/'explicit-bindings-before.json'); after=read(R/'explicit-bindings-after.json')
assert before==after and len(before)==121
bindings={x['module']:x for x in before}
olds=old['allQualifiedTransitiveOldHeads']
assert len(olds)==899 and len(old['directOldHeads'])==18
assert collections.Counter(x['kind'] for x in olds)==dict(definition=164,theorem=735)
assert all(not x['unsafe'] and not x['partial'] and set(x['axioms'])<=allow for x in olds)
byowner=collections.defaultdict(list)
for x in olds: byowner[x['module']].append(x)
root=read(W/'library/verification/receipt-v64.json')
bound(W/'library/verification/receipt-v64.json')
chainrows=[]
for c in chains['modules']:
    mod=c['module']; items=byowner[mod]
    assert {x['name'] for x in items}==set(c['actualConsumedNames'])
    assert len(items)==c['actualConsumedHeadCount']
    assert collections.Counter(x['kind'] for x in items)==c['kindCounts']
    p=W/'library'/Path(mod.replace('.','/')+'.lean')
    if not p.exists() and mod=='Shao.OQ4.BrownianPositiveCDF': p=W/'drafts/oq4/positive-boundary-studentized-author-v1/BrownianPositiveCDF.lean'
    if not p.exists() and mod=='Shao.OQ4.RandomDenominatorFarTail': p=W/'drafts/oq4/random-denominator-far-tail-author-v1/RandomDenominatorFarTail.lean'
    sm=bound(p,c['sourceSHA256'])
    runtime=bindings[mod]; original=c['originalObject']
    assert runtime['resolved']==original['resolved'] and runtime['sha256']==original['sha256']
    assert all(runtime['target_identity'][k]==v for k,v in original['target_identity'].items())
    key=mod.replace('.','/')+'.lean'
    if key in root['source_files_sha256']:
        assert root['source_files_sha256'][key]==c['sourceSHA256']
    else:
        assert mod in {'Shao.OQ4.BrownianPositiveCDF','Shao.OQ4.RandomDenominatorFarTail'}
        receipt='brownian-positive-cdf-acceptance-v1.json' if mod.endswith('BrownianPositiveCDF') else 'random-denominator-far-tail-acceptance-v1.json'
        paid=read(W/'drafts/oq4/takeover-20261023'/receipt)
        assert paid['sourceSHA256']==c['sourceSHA256']
        bound(W/'drafts/oq4/takeover-20261023'/receipt)
    chainrows.append(dict(module=mod,source=sm,consumed=len(items),kinds=dict(collections.Counter(x['kind'] for x in items)),originalObject=original,actualBeforeAfterBinding=runtime,allNativeNamesKindsAXReconciled=True,qualifiedOldCompleteProofAndAXReused=True))
assert len(chainrows)==31 and sum(x['consumed'] for x in chainrows)==899
e=read(R/'execution-receipt.json'); literal=read(R/'lean-process-receipt.json'); final=read(R/'source-bound-final-receipt.json'); rec=read(R/'runtime-recovery-receipt.json')
assert e['actualLeanProcess']==literal and literal['leanPID']==765554
assert literal['actualLeanProcessExitCode']==0 and e['wrapperProcessExitCode']==0 and literal['reaped'] and not literal['timedOut'] and e['flockReleased']
assert e['object']==final['successfulExecution']['object']==rec['originalSourceObject']
assert e['object']['mtime_ns']==1792797588181414758
rows=[json.loads(x) for x in (R/'runtime-recovery-new-inputs.jsonl').read_text(encoding='utf-8').splitlines()]
assert rows==rec['allRecoveryNewRows'] and len(rows)==6
assert read(R/'runtime-import-delta.json')==rows
assert all(x['binding_basis']=='LOST_IN_MEMORY_RECOVERY_SECOND_READ' and x['recoveryReadOrdinal']==2 and not x['originalHashPersisted'] for x in rows)
assert rec['knownPersistedFingerprintsReused']==5124 and rec['originalRuntimeRowCount']==5130
alias=rec['strongLawAlias']
assert alias['sameRealpath'] and alias['sameDeviceInode'] and alias['actualResolved']==alias['rootResolved'] and alias['actualStat']==alias['rootStat']
assert alias['actualStat']['mtime_ns']==1792797177202552212
cache=read(R/'root-strong-law-cache-receipt.json');bound(R/'root-strong-law-cache-receipt.json','be3ab775fce3a1d39bcd484dfacd053b2337d8bf6b93549948b42deab644341c')
assert alias['actualInputSHA256']==alias['rootExpectedObjectSHA256']==cache['object_sha256']
assert alias['sourcePin']==cache['source_sha256'] and cache['Lean_compilation_commands']==0 and cache['preexisting_artifacts_checked']==41164
assert rec['newLeanCommands']==rec['secondAxiomDependencyWalks']==rec['sourceOrProofEdits']==rec['originalSourceObjectContentRehashes']==0
for f in ['actual-command.txt','audit-suffix.lean','runtime-recovery-request.json','runtime-recovery-plan.json','post-success-failure-context.json','original-written-evidence-manifest.json','execution-host-response.json'] : bound(R/f)
bound(B/'final-proof-local-repairs.diff','8aeab8dd597c66e0f67bec941126b870bb53016e318057799f5f388ad24282a9')
for p in ['drafts/oq4/takeover-20261023/brownian-positive-cdf-acceptance-v1.json','drafts/oq4/brownian-positive-cdf-final-review-v1/review.md','drafts/oq4/brownian-positive-cdf-final-review-v1/receipt.json','drafts/oq4/polygonal-killed-functional-limit-final-review-v1/review.md','drafts/oq4/polygonal-killed-functional-limit-final-review-v1/receipt.json'] : bound(W/p)
validation=dict(status='PASS_LOCAL_EXACT_EVIDENCE_RECONCILIATION_NOT_NEW_KERNEL_CHECK',atUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),source=source,combined=combined,checkedArtifacts=checked,all61NativeTypesAnd4ValuesMatchInterface=True,all61PerRootAXRowsAgree=True,all31ConsumedOwnerSourceObjectRuntimeChains=chainrows,oldConsumed899NamesKindsAXReconciled=True,parent117FileSealReusedWithoutBlanketReplay=True,originalLean=literal,originalObject=e['object'],originalRuntimeGapSecondReads=rows,strongLawAlias=alias,counts=dict(owned=61,theorems=57,definitions=4,public=7,explicitPrivate=17,generated=37,oldConsumed=899,oldDefinitions=164,oldTheorems=735,oldOwnerModules=31,directOldHeads=18,actualProjectImports=39,actualRuntimeImports=5130),reviewerOperations=dict(Lean=0,parser=0,server=0,secondWalk=0,oldObjectContentRehash=0,sourceEdits=0),integerMetadata='Python arbitrary-precision JSON integers; no JS numeric roundtrip')
save('evidence-validation.json',validation)
print(json.dumps(dict(status=validation['status'],checkedArtifacts=len(checked),chains=len(chainrows),oldHeads=len(olds),owned=len(owned),recoveryRows=len(rows))))
