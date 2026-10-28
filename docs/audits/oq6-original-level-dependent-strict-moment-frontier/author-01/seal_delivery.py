from pathlib import Path
import hashlib,json,re
from datetime import datetime,timezone

OUT=Path('C:/game/shao lean/drafts/oq56/unit257/author-01')
FREEZE=OUT.parent/'freeze-01'
def bind(p):
    b=p.read_bytes()
    return {'path':p.as_posix(),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'LF':b.count(b'\n')}
def read(name):return json.loads((OUT/name).read_text(encoding='utf-8'))
def save(name,x):(OUT/name).write_bytes((json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))

assert not (OUT/'FINALWRITE.json').exists()
src=OUT/'OriginalLevelDependentStrictMomentFrontier.lean'
sb=bind(src);pb=bind(OUT/'PROOF-BODY.txt')
assert sb['sha256']=='ee2f5ff993bc92f6d5154be82ebb4da683f909717f0b20a98a4b8c76255f305b'
assert sb['bytes']==46525 and sb['LF']==731
assert src.read_bytes()==(FREEZE/'FROZEN-PREAMBLE.txt').read_bytes()+\
    (FREEZE/'FROZEN-HEAD.txt').read_bytes()+b':= by\n'+(OUT/'PROOF-BODY.txt').read_bytes()+\
    (FREEZE/'FROZEN-CLOSING.txt').read_bytes()
inputs=read('INPUT-BINDINGS.json')['inputs']
for item in inputs:
    actual=bind(Path(item['path']))
    for key in ('sha256','bytes','LF'):assert actual[key]==item[key],(item['path'],key)
static=read('STATIC-CHECK.json')
assert static['source']==sb and static['proof']==pb and static['freezeAssemblyExact']
assert static['qualified'] is False and static['actualTYPE'] is None
assert static['whole256ConsumerLiteralModuloOuterParenthesesAndWhitespace']
assert static['sourceLocalDeclarations']==198 and static['patternCommands']==22
assert static['patternBoundNamesWithCompleteTypes']==199
local=read('LOCAL-CONTEXTS.json');source=src.read_bytes()
assert local['source']==sb
for item in local['declarations']+local['bindingCommands']:
    sl=item['slice'];b=source[sl['startByte']:sl['endByteExclusive']]
    assert b.decode('utf-8')==sl['utf8'] and hashlib.sha256(b).hexdigest()==sl['sha256']
    assert item['lexicalScopeEndLine']>=sl['startLine']
bindings=read('BINDING-TYPES.json')
assert bindings['source']==sb and len(bindings['allPatternBindings'])==199
assert all(x['fullType'] and x['origin'] for x in bindings['allPatternBindings'])
assert not read('READ_ACK.json')['oldActualTYPEReread']
assert bind(FREEZE/'frozen-declaration.json')['sha256']=='1638ec2044887cd2c81851a8910d5e0062ef1909d589081e203356d00ea1bae0'
initial=OUT/'INITIAL-MANIFEST.json'
if not initial.exists():initial.write_bytes((OUT/'MANIFEST.json').read_bytes())
summary={
 'schema':'unit257-author-preseal-binding-verification-v1','atUTC':datetime.now(timezone.utc).isoformat(),
 'source':sb,'proof':pb,'allNineteenInputBindingsUnchanged':True,
 'allDeclaredSourceSlicesAndLexicalRangesVerified':True,'all199PatternTypesPresent':True,
 'freezeAndSourceAssemblyByteExact':True,'pureLocalOnly':True,
 'actualOwnerCount':None,'actualTYPE':None,'actualVALUE':None,'actualAX':None,
 'qualified':False,'machinePending':True,
 'LeanLakePPAXServerNetworkUploadGitAPIChildrenSidebarGoalScheduleOperations':0
}
save('DELIVERY-CHECK.json',summary)
payload=[bind(p) for p in sorted(OUT.rglob('*')) if p.is_file() and p.name not in ('MANIFEST.json','FINALWRITE.json')]
manifest={
 'schema':'unit257-complete-proof-author-final-manifest-v1','atUTC':datetime.now(timezone.utc).isoformat(),
 'role':'/root/oq56_unit257_author','ownerChat':'01a1822b-1815-7f21-a1af-2e0b15ee67a5',
 'source':sb,'proof':pb,'freeze':bind(FREEZE/'frozen-declaration.json'),
 'payloadCountExcludingManifestAndRelease':len(payload),'payload':payload,
 'allInputsExactAndUnchanged':True,'allLocalFailuresAndReadingNotesRetained':True,
 'qualified':False,'machinePending':True,'actualOwnerCount':None,'actualTYPE':None,'actualVALUE':None,'actualAX':None
}
save('MANIFEST.json',manifest)
for item in payload:assert bind(Path(item['path']))==item,item['path']
mb=bind(OUT/'MANIFEST.json')
release={
 'schema':'unit257-complete-proof-author-finalwrite-sixzero-release-v1','atUTC':datetime.now(timezone.utc).isoformat(),
 'role':'/root/oq56_unit257_author','ownerChat':'01a1822b-1815-7f21-a1af-2e0b15ee67a5',
 'currentRoot':'01a17d3c-6dfd-7cc0-94ed-35d758a423a5',
 'STATUS':'COMPLETE_PROOF_SOURCE_CANDIDATE_DELIVERED','source':sb,'proof':pb,
 'freeze':bind(FREEZE/'frozen-declaration.json'),'finalManifest':mb,
 'payloadCountExcludingManifestAndRelease':len(payload),'allPayloadsVerifiedBeforeRelease':True,
 'authorProofComplete':True,'sourceAccepted':False,'independentReviewPending':True,
 'qualified':False,'machinePending':True,
 'actualOwnerCount':None,'actualMachineTheorems':None,'actualMachineNonTheorems':None,
 'actualTYPE':None,'actualVALUE':None,'actualAX':None,'requiredVALUECount':None,'allOwnedAxiomOccurrences':None,
 'requestedModel':'gpt-6.1-sol','requestedEffort':'xhigh','freshContextRequested':True,
 'actualModel':None,'actualBackend':None,'actualEffort':None,
 'usage':{'input':None,'cachedInput':None,'output':None,'reasoningSubset':None},
 'writers':0,'heavy':0,'inflight':0,'pendingExternal':0,'children':0,'uncertain':0,
 'stopWritingAfterThisFile':True,
 'ownershipReleased':'All unit257 author-01 writer authority released after this last write; no server/shared/execution/publication authority was held.',
 'LeanLakePPAXServerNetworkUploadGitAPIChildrenSidebarGoalScheduleOperations':0,
 'sameM0BeforeAllNCurrentZEpsilonPBudget':True,
 'completeQualified256Retained':True,'originalMuMomentOnly':True,
 'allPartialDenominatorsRemainCompleteI':True,'jointSingleK0ForEveryPositiveTauDelta':True,
 'nextDependency':'Parent independent complete exactSOURCE review and first server native; ifsuccessful same-first-originalO allactual TYPE/requiredVALUE/transitiveAX qualification. Then actualupper/currentphysicalpayment/external sourceengine dependencies.',
 'fullOQ56':'OPEN','root':'OPEN'
}
# Final write. Nothing in this author context may mutate files afterward.
save('FINALWRITE.json',release)
print(json.dumps({'source':sb,'proof':pb,'manifest':mb,'FINALWRITE':bind(OUT/'FINALWRITE.json'),
 'payloads':len(payload),'sixRuntimeCounts':0,'qualified':False,'machinePending':True},ensure_ascii=False))
