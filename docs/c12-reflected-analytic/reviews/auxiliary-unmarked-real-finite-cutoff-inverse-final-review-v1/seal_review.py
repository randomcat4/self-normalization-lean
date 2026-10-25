import sys, pathlib, hashlib, json, re
from datetime import datetime, timezone
sys.dont_write_bytecode = True
here=pathlib.Path(__file__).resolve().parent
workspace=pathlib.Path('C:/game/shao lean')
packet=workspace/'drafts/c12-lane/auxiliary-unmarked-real-finite-cutoff-inverse-v1'
sha=lambda b:hashlib.sha256(b).hexdigest()
def readj(p): return json.loads(pathlib.Path(p).read_text(encoding='utf-8'))
def writej(name,v): (here/name).write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
def binding(p):
 p=pathlib.Path(p).resolve(); b=p.read_bytes(); return {'path':p.as_posix(),'bytes':len(b),'sha256':sha(b)}
local=[]
def bind(p,expected=None,size=None):
 row=binding(p)
 if expected is not None: assert row['sha256']==expected, row['path']
 if size is not None: assert row['bytes']==size, row['path']
 local.append(row); return row
receipt=readj(packet/'receipt.json')
bind(packet/'receipt.json','408db49a9b13f0f7206b860194a9a17341b75ad5748f1508eedbef0bf483e34c')
for name,row in receipt['artifacts'].items():
 p=packet/name
 if p.is_file(): bind(p,row['sha256'],row['bytes'])
bind(packet/'AuxiliaryUnmarkedRealFiniteCutoffInverse.lean',receipt['sourceSHA256'],15908)
bind(packet/'RELEASE.json')
source=(packet/'AuxiliaryUnmarkedRealFiniteCutoffInverse.lean').read_bytes()
source.decode('utf-8'); assert not source.startswith(b'\xef\xbb\xbf') and b'\r' not in source
assert not re.search(rb'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',source)
assert len(source.splitlines())==298
pattern=rb'(?ms)^(?:private )?theorem\s+.*? := by\n'
heads=list(re.finditer(pattern,source)); frozen=(packet/'frozen.lean.txt').read_bytes()
assert source[:heads[0].start()]+b'\n'.join(m.group(0) for m in heads)+b'\nend Shao.C2.AuxiliaryUnmarkedRealFiniteCutoffInverse\n'==frozen
audit=readj(packet/'owned-audit.json'); records=audit['module_owned_constants']
types=(packet/'actual-owned-types.txt').read_bytes()
actualNames=re.findall(rb'(?m)^TARGET_DECL (.*?) KIND theorem AXIOMS ',types)
assert set(x.decode() for x in actualNames)==set(x['name'] for x in records)
assert len(actualNames)==len(records)==2
assert all(x['kind']=='theorem' and x['owner']==receipt['module'] for x in records)
assert all(set(x['axioms'])=={'propext','Classical.choice','Quot.sound'} for x in records)
assert len(types)==37507 and b'\xe2\x8b\xaf' not in types and b'...' not in types
assert (packet/'actual-definition-values.txt').read_bytes()==b''
interfaces=readj(packet/'consumed-interface-bindings.json')
sliceResults=[]
for item in interfaces['interfaces']:
 sourcePath=pathlib.Path(item['path']); b=sourcePath.read_bytes(); bind(sourcePath,item['sourceExportSHA256'])
 part=b[item['offset']:item['offset']+item['bytes']]
 assert sha(part)==item['sliceSHA256']
 assert part==(packet/item['file']).read_bytes()
 sliceResults.append({'name':item['name'],'sourcePath':sourcePath.as_posix(),'offset':item['offset'],'bytes':len(part),'sha256':sha(part),'losslessSlice':True})
for dirname,expected in [('auxiliary-unmarked-real-cutoff-inverse-final-review-v1','24f9a78220d73fd61ab9a6faab20980b0086d5d3e4391bb40f773f26c3b5e051'),('auxiliary-real-damped-moments-final-review-v1','c9ae599ed490c31d4c348999ead6647b5705b22fef0f665bb12a1895bcf09884')]:
 folder=workspace/'drafts/c12-lane'/dirname
 bind(folder/'parent-acceptance.json',expected); parent=readj(folder/'parent-acceptance.json')
 assert parent['status']=='QUALIFIED_EXACT_SOURCE_COMPLETE_INDEPENDENT_REVIEW_ORIGINAL_SERVER_KERNEL_ALL_OWNED_AXIOMS'
 assert parent['allFullNewProofsPrivateGeneratedTypesValuesCovered'] and parent['criticalGaps']==[]
 for key,file in [('fullReviewJSONSHA256','full-review.json'),('fullReviewMDSHA256','full-review.md'),('reviewReleaseSHA256','RELEASE.json'),('validationSHA256','validation.json')]: bind(folder/file,parent[key])
 oldreview=readj(folder/'full-review.json')
 assert ('CORRECT' in json.dumps(oldreview))
old179=workspace/'drafts/c12-lane/auxiliary-real-damped-moments-v1'
old182=workspace/'drafts/c12-lane/auxiliary-unmarked-real-cutoff-inverse-v1'
for p,h in [(old179/'AuxiliaryRealDampedMoments.lean','f93568a407994566c92a9c6a3ec19c8dfeb7fc4dbea2baae70924166a256f22c'),(old179/'receipt.json','09f440e2eda6d29923828a68154a1428b153d4531fa87067e9c9814a531f4cf8'),(old182/'AuxiliaryUnmarkedRealCutoffInverse.lean','6ad57419f8d59f43b6fb72a56ccffdd81955590a1c056b18523a86897989246a'),(old182/'receipt.json','02dcf8421d8541079ac6dbf59c031a839bac76cbb842a618c06cca5d03555013')]: bind(p,h)
qualpath=workspace/'coordination/common-suffix-scalar-interfaces-root-qualification.json'
bind(qualpath,'2a2ca77941fa9500843582dc57681d01260abfd2abae7f0d1cab331e6ceb6c26'); qual=readj(qualpath)
assert qual['qualifiedForSourceBoundConsumption'] and qual['fresh_complete_independent_report']['fullSourceAllProofAll4ActualTypesKindDerived0ValuesRecursiveAXCoverage']
for p,h in [(qual['local_source'],qual['source_sha256']),(qual['qualifiedOwnerMap'],qual['qualifiedOwnerMapSHA256']),(qual['fresh_complete_independent_report']['path'],qual['fresh_complete_independent_report']['sha256']),(qual['fresh_complete_independent_report']['structuredPath'],qual['fresh_complete_independent_report']['structuredSHA256'])]: bind(workspace/p,h)
bind(workspace/'drafts/c2-residual-rare-suffix-production/private-helper-heads-request01.lean.txt','7a8c467528607017a7a55bb8b67f9c15b45e7642f5ceb7ecc55280ea04049939')
bind(here/'brief.txt')
local=list({r['path']:r for r in local}.values())
writej('local-binding-map.json',local)
fresh=readj(here/'fresh-remote-bindings.json')
remote={x['path']:x for x in fresh['bindings']}
assert len(remote)==50 and fresh['derivedCounts']['owned']==2
assert all(x['freezeExact'] and x['utf8NoBOM'] and x['CRcount']==0 and x['forbidden']==[] for x in fresh['headIdentity'])
assert fresh['auditReconstruction']['roundTrip']
prefixBytes=len(fresh['auditReconstruction']['prefix'].encode())
suffixBytes=len(fresh['auditReconstruction']['suffix'].encode())
assert prefixBytes+len(types)+suffixBytes==37718
for row in local:
 p=pathlib.Path(row['path'])
 if p.parent==packet and p.name in receipt['artifacts']:
  r=remote[receipt['artifacts'][p.name]['remotePath']]; assert r['bytes']==row['bytes'] and r['sha256']==row['sha256']
native={}
for p in sorted(here.glob('native-contract-bindings-*.json')):
 for row in readj(p):
  assert row['identicalToPinnedBlob']
  if row['path'] not in native: native[row['path']]=row
  else:
   assert native[row['path']]['sha256']==row['sha256']
   native[row['path']]['readRanges']+=row['readRanges']
writej('native-contract-bindings.json',{'mathlibPin':receipt['mathlib'],'files':list(native.values()),'allReadFilesExactlyPinned':True})
writej('evidence-observation.json',{'readOnly':True,'rawRemoteLogsDownloaded':False,'originalKernel001':{'exit':1,'fullLogRead':True,'fullDeltaRead':True,'preserved':True},'originalKernel002':{'exit':0,'fullLogRead':True,'commandRead':True},'originalAllOwnerAudit':{'exit':0,'implementationReadCompletely':True,'selection':'env.getModuleIdxFor? exact owner, every constant; public list only checks presence','allTypeBytesRead':37507,'completeLogLosslesslyReconstructed':True,'prefixBytes':prefixBytes,'suffixBytes':suffixBytes,'axioms':['propext','Classical.choice','Quot.sound']},'serverObservedMtimesNs':{'freeze-record.json':1792890044745525839,'preflight-observation.json':1792890042893530965,'attempt001/kernel.log':1792890051781506366,'attempt002/kernel.log':1792890073053447493,'receipt.json':1792890110041345122},'unit182QualificationUTC':'2026-10-25T01:00:18.718547+00:00','unit182QualifiedBefore183FirstGate':True,'diagnostics':[{'operation':'initial acknowledgement write','issue':'PowerShell false literal was corrected to $false immediately before the source/evidence review','sourceOrEvidenceChanged':False},{'operation':'remote metadata result parsing','issue':'transport returns exit_code rather than ok; corrected parser and repeated read-only metadata observation','sourceOrEvidenceChanged':False},{'operation':'remote native declaration search','issue':'rg absent on server; used read-only Python search and pinned git grep','sourceOrEvidenceChanged':False}]})
counts={'owned':2,'theorems':2,'public':1,'private':1,'generated':0,'nonTheorems':0,'values':0,'actualTypesBytes':37507,'actualValuesBytes':0}
report={'status':'CORRECT','unit':183,'role':'fresh independent final complete reviewer','requestedModel':'gpt-6.1-sol','requestedEffort':'xhigh','actualModel':None,'actualEffort':None,'tokenUsage':{'input':None,'cachedInput':None,'output':None,'reasoningSubset':None},'module':receipt['module'],'sourceSHA256':receipt['sourceSHA256'],'objectSHA256':receipt['objectSHA256'],'receiptSHA256':binding(packet/'receipt.json')['sha256'],'frozenSHA256':receipt['frozenSHA256'],'derivedCounts':counts,'fullSourceAndAllProofsRead':True,'actualOwnedTypesReadCompletely':True,'typeReadMethod':'literal sequential lines 1-170, 171-335, 336-end; every block/context/instance/let/target included','typePayloadSHA256':sha(types),'definitionValueCoverage':'kind-derived none; empty export verified','sourceFidelityReviewed':True,'allConsumedCompleteActualTypesRead':True,'consumedQualifiedInterfaces':sliceResults,'nativeContracts':{'allInspectedFilesExactAtPin':True,'fileCount':len(native),'bindingFile':'native-contract-bindings.json'},'originalServerEvidence':{'kernelAttempt':2,'kernelExit':0,'fullSuccessfulKernelLogRead':True,'fullFailedKernelLogAndProofDeltaRead':True,'auditExit':0,'exactOwnerSelectionImplementationRead':True,'allOwnerTransitiveAxiomCoverage':True,'auditLogCompleteByLosslessReconstruction':True,'rawLogsDownloaded':False,'LeanReplays':0,'auditReplays':0,'oldProofReReviews':0},'proofCoverage':[{'name':records[0]['name'],'sourceLines':[12,189],'complete':True,'points':['law-independent Ca,alpha,A','finite H shifted range','public182 kernel integrability only','actual qualified179 shifted sections and bound','nonpositive-power monotonicity and exact exponent cancellation','norm-integral/product integrability','inverse-Laplace and unconditional exponential identity','pointwise domination, actual selected integrability and Fubini']},{'name':records[1]['name'],'sourceLines':[191,296],'complete':True,'points':['two new power producers','real (1+u)^a bound','positive-energy sqrt/division/rpow identities','unchanged finite event','measurable nonnegative selected function','actual integrability and numerical integral combination']}],'edgeCases':['a=0','q arbitrary positive real including small q','n=0','zero energy off event','zero sum and 0^0 convention','atomic probability laws','H=b','energy=b included','energy=H excluded','retained=1/2 negative branch','both actual gamma branches','all constants chosen before law/n/b/H'],'criticalGaps':[],'scope':'ordinary unmarked ell0 finite-real-H master, finite second moment only, actual b<=energy<H and actual shifted retained-gamma kernel','rootStatus':{'C2':'OPEN','C12':'OPEN'},'parentAcceptanceWritten':False,'sharedChanges':False,'subagents':0,'heavyCommands':0,'localBindingsFile':'local-binding-map.json','localBindingsCount':len(local),'freshRemoteBindingsFile':'fresh-remote-bindings.json','freshRemoteBindingsCount':len(remote),'atUTC':datetime.now(timezone.utc).isoformat()}
writej('full-review.json',report)
checks={'sourceAndReceiptBound':True,'allPresentPacketArtifactsMatchReceipt':True,'localAndRemotePacketBindingsAgree':True,'bothFrozenHeadersAndContextExact':True,'threeRemoteVersionsFreezeExact':True,'encodingAndForbiddenProofScan':True,'actualOwnerNamesKindsCountsAndAxiomsMatch':True,'actualTypePayloadComplete':True,'nonTheoremValuesAbsentByOwnerMap':True,'allConsumedTypeSlicesLossless':True,'oldQualificationSealsMatch':True,'rootRareHeadsUntouched':True,'nativeFilesIdenticalToPinnedMathlib':True,'fullOriginalEvidenceReadAndReused':True,'LeanReplaysZero':True,'auditReplaysZero':True,'noSharedWrites':True}
validation={'status':'PASS','unit':183,'checks':checks,'localBoundFiles':len(local),'freshRemoteBindings':len(remote),'nativeFiles':len(native),'derivedCounts':counts,'reviewVerdict':'CORRECT','mathematicalVerdictIsIndependentReviewNotScriptInference':True,'atUTC':datetime.now(timezone.utc).isoformat()}
writej('validation.json',validation)
payloads=[binding(p) for p in sorted(here.iterdir()) if p.is_file() and p.name!='RELEASE.json']
writej('RELEASE.json',{'status':'FINAL_REVIEW_COMPLETE_CORRECT_RELEASED','unit':183,'writerReleased':True,'executionReleased':True,'inFlight':[],'heavyInFlight':False,'heavy':False,'sourceSHA256':receipt['sourceSHA256'],'objectSHA256':receipt['objectSHA256'],'receiptSHA256':binding(packet/'receipt.json')['sha256'],'frozenSHA256':receipt['frozenSHA256'],'fullReviewMDSHA256':binding(here/'full-review.md')['sha256'],'fullReviewJSONSHA256':binding(here/'full-review.json')['sha256'],'validationSHA256':binding(here/'validation.json')['sha256'],'localBindingMapSHA256':binding(here/'local-binding-map.json')['sha256'],'freshRemoteBindingsSHA256':binding(here/'fresh-remote-bindings.json')['sha256'],'derivedCounts':counts,'payloads':payloads,'parentAloneAcceptsPublishesAndUpdatesStatus':True,'atUTC':datetime.now(timezone.utc).isoformat()})
release=readj(here/'RELEASE.json')
for row in release['payloads']:
 assert binding(row['path'])==row
print(json.dumps({'status':'PASS','verdict':'CORRECT','sealedPayloads':len(payloads),'localBoundFiles':len(local),'freshRemoteBindings':len(remote),'nativeFiles':len(native),'receiptArtifacts':len(receipt['artifacts']),'counts':counts,'reviewMD':binding(here/'full-review.md'),'reviewJSON':binding(here/'full-review.json'),'release':binding(here/'RELEASE.json')},indent=2))
