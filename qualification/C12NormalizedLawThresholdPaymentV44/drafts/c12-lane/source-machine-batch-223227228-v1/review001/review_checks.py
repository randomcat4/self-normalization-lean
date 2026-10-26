from pathlib import Path
import hashlib, json, re, difflib, datetime

ROOT = Path('C:/game/shao lean')
HERE = ROOT/'drafts/c12-lane/source-machine-batch-223227228-v1/review001'
READS = {}
BINDINGS = []
def sha(b): return hashlib.sha256(b).hexdigest()
def resolve(p):
    p = Path(str(p).replace('\\', '/'))
    return p if p.is_absolute() else ROOT/p
def read(p, scope='byte binding; no automatic old-proof re-review'):
    p=resolve(p); b=p.read_bytes()
    READS[p.as_posix()]={'path':p.as_posix(),'bytes':len(b),'sha256':sha(b),'readScope':scope}
    return b
def js(p, scope='complete structured evidence parsed'):
    return json.loads(read(p,scope).decode('utf-8-sig'))
def bind(row, origin):
    p=resolve(row['path']); b=read(p)
    expectedHash=row.get('sha256', row.get('expectedSHA256'))
    expectedBytes=row.get('bytes',row.get('expectedBytes'))
    ok=(expectedHash is None or sha(b)==expectedHash) and (expectedBytes is None or len(b)==expectedBytes)
    rec={'path':p.as_posix(),'bytes':len(b),'sha256':sha(b),'expectedBytes':expectedBytes,'expectedSHA256':expectedHash,'origin':origin,'passCheck':ok}
    BINDINGS.append(rec)
    assert ok, rec
    return b
def dump(name,x):
    (HERE/name).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')

activationPath=HERE/'parent-activation001.json'
bind({'path':activationPath.as_posix(),'bytes':11417,'sha256':'cd4116c8481990a1422bfe7f9b1e9fa27711c01bd3f7ae8502b6ab8ce2e43447'},'parent exact activation')
a=js(activationPath)
assert len(a['mandatoryInputs'])==39
for r in a['mandatoryInputs']: bind(r,'39 mandatory activation inputs')
old=ROOT/'drafts/c12-lane/native-repairs-223227-v1/review001'
oldInput=js(old/'INPUT-SEAL.json')
for r in oldInput['bindings']: bind(r,'prior complete-source INPUT-SEAL binding')
for r in oldInput['readInputs']: bind(r,'prior complete-source INPUT-SEAL actual input')
for r in js(old/'PAYLOAD-SEAL.json')['payloads']: bind(r,'prior complete-source PAYLOAD-SEAL')
earlier=ROOT/'drafts/c12-lane/qualified-machine-and-source-batch-223226227-v1/review001'
for r in js(earlier/'PAYLOAD-SEAL.json')['files']: bind(r,'earlier whole-proof review payload')

units={}
specs={
223:('actual-retained-centered-normalized-law-v1/source005/ActualRetainedCenteredNormalizedLaw.lean',[(12,37,161)]),
227:('actual-centered-product-transport-v1/source002/ActualCenteredProductTransport.lean',[(13,16,26),(28,42,97)]),
228:('actual-brownian-threshold-payment-v1/source001/ActualBrownianThresholdPayment.lean',[(13,18,73),(75,85,108),(110,121,147)])}
for unit,(rel,proofspec) in specs.items():
    p=ROOT/'drafts/c12-lane'/rel; b=read(p,'full source/all declarations/all whole proofs read; 227 exact old complete proof coverage reused')
    s=b.decode('utf-8'); lines=s.splitlines(keepends=True)
    assert b.count(b'\r')==0 and not b.startswith(b'\xef\xbb\xbf') and s.endswith('\n')
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',s)
    base=p.parent.parent
    freeze=js(base/'parent-exact-declaration-freeze001.json')
    for r in freeze['frozen']+freeze['inputs']: bind(r,f'unit{unit} frozen direct payload')
    frozen=[]
    preamble=read(freeze['frozen'][0]['path']).decode('utf-8')
    assert s.startswith(preamble)
    frozen.append({**freeze['frozen'][0],'exact':True})
    proofs=[]
    for i,(h,body,end) in enumerate(proofspec):
        name=re.match(r'theorem (\w+)',lines[h-1]).group(1)
        head=''.join(lines[h-1:body-1]); assert head.endswith(' := by\n')
        head=head[:-len(' := by\n')]+'\n'
        frozenHead=read(freeze['frozen'][i+1]['path']).decode('utf-8')
        assert head==frozenHead,(unit,name,'head mismatch')
        frozen.append({**freeze['frozen'][i+1],'exact':True})
        proof=('by\n'+''.join(lines[body-1:end])).encode('utf-8')
        proofs.append({'name':name,'headStartLine':h,'bodyStartLine':body,'bodyEndLine':end,'bytes':len(proof),'sha256':sha(proof)})
    units[unit]={'unit':unit,'source':READS[p.as_posix()],'sourceLines':len(lines),'LF':b.count(b'\n'),'CR':0,'BOM':False,'frozen':frozen,'proofs':proofs}

u223base=ROOT/'drafts/c12-lane/actual-retained-centered-normalized-law-v1'
old223=read(u223base/'source004/ActualRetainedCenteredNormalizedLaw.lean').decode('utf-8').splitlines(keepends=True)
new223=read(units[223]['source']['path']).decode('utf-8').splitlines(keepends=True)
diff=[]
for op,i,j,k,l in difflib.SequenceMatcher(a=old223,b=new223,autojunk=False).get_opcodes():
    if op!='equal':diff.append({'op':op,'oldLines':[i+1,j],'newLines':[k+1,l],'old':''.join(old223[i:j]),'new':''.join(new223[k:l])})
assert len(diff)==1 and diff[0]['oldLines']==[55,56] and diff[0]['newLines']==[55,57],diff
assert units[223]['proofs'][0]['sha256']=='3a0ae68ff7341c838bb1664fe822aa635d0c75b1273b568783cd2b81c3f8834c'
units[223]['diffVersus004']=diff
prevCov=js(old/'COVERAGE.json'); prev227=next(u for u in prevCov['units'] if u['unit']==227)
assert units[227]['proofs']==prev227['proofs']
units[227]['completeIndependentProofReuse']=prev227['proofs']
earlierCov=js(earlier/'COVERAGE.json')
assert '22ca383b5f698bafef2df0f8c94f75ec0b45aabe02c53164c0c4c5ef3e08214d' in json.dumps(earlierCov['units']['u227'])

u228base=ROOT/'drafts/c12-lane/actual-brownian-threshold-payment-v1'
producer=read(ROOT/'library/Shao/Probability/SourceNonresidualBrownian.lean','only exact public interface484-500; old producer proof not re-reviewed').decode('utf-8').splitlines(keepends=True)
complete=read(u228base/'qualified-brownian-producer-complete-public-head002.txt').decode('utf-8')
partial=read(u228base/'qualified-brownian-producer-public-head.txt').decode('utf-8')
assert complete==''.join(producer[483:500]).replace(' := by\n','\n')
assert partial==''.join(producer[483:499])
qpath=ROOT/'coordination/common-nonresidual-brownian-root-qualification.json'
qual=js(qpath,'read qualified exact producer interface/accepted evidence chain; no duplicate proof review')
accept=js(ROOT/'coordination/integration-v85/common-source-acceptance.json','selected already-accepted producer binding')
qentry=next(x for x in accept['newCommon'] if x['pr']==333)
bind({'path':qpath.as_posix(),'sha256':qentry['qualificationSHA256']},'already accepted producer root qualification')
assert qual['qualifiedForSourceBoundConsumption'] and qual['source_sha256']==units[228]['frozen'][0].get('unused', 'e6de66f3b78a8607842ad71608e0bbce53751f2b69b3e6b973c7f125d8361b23')
for key in ('review','authorReceipt','authorRelease','reviewerRelease','independentPhysicalBindings'):
    r=qual[key];bind(r,'accepted producer qualified evidence byte reuse')
bind({'path':qual['review']['structuredPath'],'sha256':qual['review']['structuredSHA256']},'accepted producer structured complete review binding')
bind({'path':qual['qualifiedOwnerMap'],'sha256':qual['qualifiedOwnerMapSHA256']},'accepted producer owner-map binding')
main=read('C:/game/shao/current/c12/main.tex','original source1427-1490; 228 exact original1480-1485').decode('utf-8').splitlines()
excerpt=read(u228base/'original-g-main-threshold-payment-excerpt.txt').decode('utf-8')
assert excerpt.splitlines()==main[1479:1485]
units[228]['originalExcerptLineExactAfterLineEndingNormalization']=True
units[228]['originalExcerptCRCount']=excerpt.count('\r')
for p in ('library/lean-toolchain','library/lake-manifest.json','library/Shao/C2/BridgeDomination.lean','SERVER.md','coordination/TEAM.md','coordination/streamlined-acceptance-current.md'):
    read(ROOT/p,'selected current requirements/pins or relevant public definition only')
assert read(ROOT/'library/lean-toolchain').decode().strip()=='leanprover/lean4:v4.36.0-rc1'
manifest=js(ROOT/'library/lake-manifest.json');assert next(x for x in manifest['packages'] if x['name']=='mathlib')['rev']=='807d3836b165983210ee2ecf3cd28f239436949c'

base=ROOT/'drafts/c12-lane/actual-centered-product-transport-v1'
receipts=base/'native002/server-receipts'
idx=js(receipts/'actual-types-values-index.json');owned=js(receipts/'owned-audit.json')
types=read(receipts/'actual-types-values.txt','every complete actualTYPE1-178 literally read').decode('utf-8');typelines=types.splitlines(keepends=True)
target='Shao.C2.ActualCenteredProductTransport'
assert idx['sourceSHA256']==units[227]['source']['sha256']
assert owned['status']=='PASS' and owned['target_module']==target
names={r['name'] for r in owned['module_owned_constants']}
assert names=={r['name'] for r in idx['entries']}==set(re.findall(r'^TARGET_DECL (\S+) KIND',types,re.M))
assert len(names)==9 and len(owned['module_owned_constants'])==9
assert all(r['owner']==target and r['kind']=='theorem' and set(r['axioms'])<=set(owned['allowed_axioms']) for r in owned['module_owned_constants'])
assert set(owned['allowed_axioms'])=={'propext','Classical.choice','Quot.sound'}
assert owned['target_constant_count']==owned['target_theorem_count']==idx['typeCount']==9
assert owned['target_definition_count_including_private_generated']==idx['fullValueCount']==0 and owned['public_theorem_count']==2
assert types.count('ACTUAL_TYPE ')==9 and types.count('DEFINITION_VALUE ')==0
assert not any(v for v in idx['truncationMarkers'].values())
assert all(mark not in types for mark in ('⋯','…','[truncated]','<truncated>'))
nextline=1
for row in idx['entries']:
    assert row['startLine']==nextline and row['endLine']>=nextline and row['hasActualType'] and not row['hasFullValue']
    block=''.join(typelines[row['startLine']-1:row['endLine']]).encode('utf-8')
    assert block.decode().startswith('TARGET_DECL '+row['name']+' KIND theorem')
    row['completeBlockBytes']=len(block);row['completeBlockSHA256']=sha(block);row['reviewed']=True
    row['recursiveAxioms']=next(r['axioms'] for r in owned['module_owned_constants'] if r['name']==row['name'])
    nextline=row['endLine']+1
assert nextline==len(typelines)+1==179
sourceSHA=units[227]['source']['sha256'];objectSHA=idx['objectSHA256']
resource=[]
for prefix in ('kernel002','audit001'):
    start=js(receipts/(prefix+'-start.json')); result=js(receipts/(prefix+'-result.json')); threads=js(receipts/(prefix+'-threads.json'))
    assert start['sourceSHA256']==result['sourceSHA256Before']==result['sourceSHA256After']==sourceSHA
    assert result['naturalRC']==0 and result['errorHeaderCount']==0 and not result['errorHeaders']
    assert result['objectSHA256']==objectSHA and result['objectBytes']==161896
    assert start['CPU']==[44,45,46,47] and start['phaseSHA256']=='15a60bf452294d96b79a9a9a1e7c9b77ddede4f1059c5cce4dcf3692ea47c813'
    assert start['command'][:5]==['lake','env','lean','-M8192','-j4'] and 'c12-heavy.lock' in start['flock']
    users=[r for r in threads if r['kind']=='userCompute'];helpers=[r for r in threads if r['kind']=='kernelSQhelper']
    assert len(users)==result['userThreadsObserved'] and result['userComputeRangeOK']
    assert all(r['userRangeOK'] and set(r['affinity'])<=set([44,45,46,47]) for r in users)
    assert len(helpers)==1 and helpers[0]['comm'].startswith('iou-sqp-') and helpers[0]['firstTicks']==helpers[0]['lastTicks']==0
    assert result['peakAggregateMemoryGiB']<180
    resource.append({'receipt':prefix,'sourceSHA256':sourceSHA,'originalObjectSHA256':objectSHA,'originalObjectBytes':161896,'naturalRC':0,'actualUserThreads':len(users),'userAffinityExact44to47':True,'kernelHelperZeroTicks':True,'peakAggregateMemoryGiB':result['peakAggregateMemoryGiB'],'peakObservedRSSKiB':result['peakObservedRSSKiB'],'fullProject80GiBBudgetNotIndependentlyMeasuredBySingleTarget':True})
kr=js(receipts/'kernel002-result.json');ar=js(receipts/'audit001-result.json')
assert ar['AX']=='PASS_ALL_ACTUAL_OWNERS_TRANSITIVE' and ar['ownedReportSHA256']==sha(read(receipts/'owned-audit.json'))
assert ar['actualOwnedCount']==ar['actualTheoremCount']==9 and ar['actualDefinitionCount']==0 and ar['actualPublicCount']==2
ob=json.loads(js(base/'native002/audit001-input-object-binding-response.json')['stdout'])
assert ob['sourceSHA256']==sourceSHA and ob['originalSuccessfulObjectSHA256']==ob['aliasSHA256']==objectSHA and ob['originalObjectBytes']==161896
assert ob['aliasPreviouslyAbsent'] and ob['sharedPackageCacheWrites']==0 and ob['auditSHA256']==sha(read(base/'native-preparation001/OwnedAudit.lean'))
ex=json.loads(js(base/'native002/audit001-type-value-extraction-response.json')['stdout'])
for r in ex['rows']: bind({'path':(receipts/r['file']).as_posix(),'bytes':r['bytes'],'sha256':r['sha256']},'server extraction exact receipt binding')
assert ex['rawLogSHA256']==ar['logSHA256'] and ex['typeCount']==9 and ex['fullValueCount']==0 and ex['AX']=='PASS'
assert kr['atUTC']<ob['atUTC']<js(receipts/'audit001-start.json')['atUTC']<ar['atUTC']<ex['atUTC']
phase=js(ROOT/'coordination/restart-20261025/HEAVY-PHASE-C12-OQ56-29.json')
assert phase['heavyAllowances']['c12']==1 and phase['maximumConcurrentProjectHeavy']==2
units[227]['actualTypeCoverage']=idx['entries'];units[227]['actualOwnerCounts']={'all':len(names),'theorems':9,'public':2,'nonTheorems':0,'actualTYPE':9,'nonTheoremVALUE':0}
units[227]['originalObjectSHA256']=objectSHA;units[227]['originalObjectBytes']=161896;units[227]['receiptResources']=resource
units[228]['producerCompletePublicHeadLines']=[484,500];units[228]['oldPartialExcerptPreserved']=True
units[228]['originalSourceLines']=[1480,1485]

dump('DETERMINISTIC-CHECK.json',{'status':'PASS','mandatoryBindings':39,'bindingOccurrences':len(BINDINGS),'uniqueReadPaths':len(READS),'allBindingOccurrencesPass':True,'units':units,'actualReviewerActivity':{'Lean':0,'AX':0,'server':0,'network':0,'upload':0,'GitAPI':0,'heavy':0,'inflight':0,'pendingExternal':0,'children':0}})
dump('INPUT-SEAL.json',{'atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'activation':READS[activationPath.as_posix()],'bindings':BINDINGS,'readInputs':list(READS.values()),'allPass':True,'scope':'Complete changed-source proofs223/228;227 exact old complete independent proof reuse and every new actualTYPE/recursiveAX/receipt supplement; old producer proof reaudits0'})
print(json.dumps({'status':'PASS','mandatory':39,'bindingOccurrences':len(BINDINGS),'uniqueReadPaths':len(READS),'proofs':{str(k):v['proofs'] for k,v in units.items()},'actual227Owners':len(names),'actual227TYPELines':len(typelines)},ensure_ascii=False))
