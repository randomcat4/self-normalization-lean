from pathlib import Path
import hashlib,json
from datetime import datetime,timezone

out=Path('C:/game/shao lean/drafts/oq56/unit256/author-01')
freeze=out.parent/'freeze-02'
def binding(p):
    b=p.read_bytes()
    return {'path':p.as_posix(),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'LF':b.count(b'\n')}
def load(name):return json.loads((out/name).read_text(encoding='utf-8'))
def save(name,v):(out/name).write_bytes((json.dumps(v,ensure_ascii=False,indent=2)+'\n').encode())
assert not (out/'FINALWRITE.json').exists()
source=out/'OriginalLevelDependentLiteralWeightedConsumer.lean'
sb=binding(source)
assert sb['sha256']=='8165e387c4f04ae5a751b76468d98fe8a5909d980f3d5f70384475b1c02d3466'
assert sb['bytes']==66807 and sb['LF']==1053
assert source.read_bytes()==(freeze/'FROZEN-PREAMBLE.txt').read_bytes()+\
 (freeze/'FROZEN-HEAD.txt').read_bytes()+b':= by\n'+(out/'PROOF-BODY.txt').read_bytes()+\
 (freeze/'FROZEN-CLOSING.txt').read_bytes()
assert (out/'PROOF-BODY.txt').read_bytes()==(out/'preserved-freeze01/PROOF-BODY.txt').read_bytes()
static=load('STATIC-CHECK.json')
assert static['source']==sb and static['freezeAssemblyExact'] and static['sliceRoundtripExact']
assert static['actualMachineOwnerCount'] is None and static['qualified'] is False
assert load('PREAMBLE-AMENDMENT-APPLIED.json')['suffixExactlyUnchanged']
preservation=load('preserved-freeze01/PRESERVATION.json')
for item in preservation['payload']:
    actual=binding(Path(item['path']))
    assert actual['sha256']==item['sha256'] and actual['bytes']==item['bytes'],item['path']
payload=[binding(p) for p in sorted(out.rglob('*')) if p.is_file() and p.name not in ('MANIFEST.json','FINALWRITE.json')]
manifest={'schema':'unit256-complete-author-final-payload-manifest-v1','atUTC':datetime.now(timezone.utc).isoformat(),
 'role':'/root/oq56_unit256_author','leadOwner':'01a1822b-1815-7f21-a1af-2e0b15ee67a5',
 'source':sb,'proof':binding(out/'PROOF-BODY.txt'),'freeze':binding(freeze/'frozen-declaration.json'),
 'payloadCountExcludingManifestAndRelease':len(payload),'payload':payload,
 'preservedFreeze01PayloadsVerified':True,'allLocalFailuresRetained':True,
 'qualified':False,'machinePending':True,'allActualMachineOwnerCounts':None}
save('MANIFEST.json',manifest)
for item in payload:
    actual=binding(Path(item['path']))
    assert actual==item,item['path']
manifestBinding=binding(out/'MANIFEST.json')
release={'schema':'unit256-complete-author-finalwrite-sixzero-release-v1','atUTC':datetime.now(timezone.utc).isoformat(),
 'role':'/root/oq56_unit256_author','leadOwner':'01a1822b-1815-7f21-a1af-2e0b15ee67a5',
 'currentRoot':'01a17d3c-6dfd-7cc0-94ed-35d758a423a5',
 'STATUS':'COMPLETE_PROOF_SOURCE_CANDIDATE_DELIVERED',
 'source':sb,'proof':binding(out/'PROOF-BODY.txt'),
 'freeze':binding(freeze/'frozen-declaration.json'),'finalManifest':manifestBinding,
 'payloadCountExcludingManifestAndRelease':len(payload),'payloadCountIncludingManifestExcludingRelease':len(payload)+1,
 'allPayloadsVerifiedBeforeRelease':True,'authorProofComplete':True,
 'sourceAccepted':False,'independentReviewPending':True,'qualified':False,'machinePending':True,
 'actualMachineOwnerCount':None,'actualMachineTheorems':None,'actualMachineNonTheorems':None,
 'actualTYPELF':None,'requiredVALUECount':None,'allOwnedAxiomOccurrences':None,
 'requestedModel':'gpt-6.1-sol','requestedEffort':'xhigh','freshContextRequested':True,
 'actualModel':None,'actualBackend':None,'actualEffort':None,
 'usage':{'input':None,'cachedInput':None,'output':None,'reasoningSubset':None},
 'writers':0,'heavy':0,'inflight':0,'pendingExternal':0,'children':0,'uncertain':0,
 'stopWritingAfterThisFile':True,
 'ownershipReleased':'All unit256 author-01 writer authority released after this last write. No shared/server/execution/publication authority was held.',
 'LeanLakePPAXServerNetworkUploadGitAPIChildrenSidebarGoalScheduleOperations':0,
 'failureFiles':['LOCAL-FAILURE-01.json','LOCAL-FAILURE-02.json','LOCAL-READ-FAILURE-01.json'],
 'parentExplicitSyntaxAmendmentApplied':'PREAMBLE-AMENDMENT-APPLIED.json; old freeze01 and all original candidate bytes retained',
 'nextDependency':'Parent qualified independent complete new source review, first native and same-first-original-object allactual TYPE/required VALUE/transitive AX. Then same-witness original-p strictbudget/actualupper/physicalpayment/sourceengine interfaces.',
 'fullOQ56':'OPEN','root':'OPEN'}
# This is intentionally the final filesystem write by the author.
save('FINALWRITE.json',release)
print(json.dumps({'source':sb,'proof':binding(out/'PROOF-BODY.txt'),'manifest':manifestBinding,
 'FINALWRITE':binding(out/'FINALWRITE.json'),'payloads':len(payload),'allSixRuntimeCounts':0,
 'qualified':False,'machinePending':True},ensure_ascii=False))
