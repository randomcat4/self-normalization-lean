from pathlib import Path
from collections import Counter
import datetime,hashlib,json,re

BASE=Path('C:/game/shao lean/drafts/oq56/unit248')
OUT=BASE/'final-review-01'
assert not (OUT/'lastzeroRELEASE.json').exists(), 'FINALWRITE immutable'
SHA=lambda b:hashlib.sha256(b).hexdigest()
def bind(p):
    p=Path(p);b=p.read_bytes();return {'path':p.as_posix(),'sha256':SHA(b),'bytes':len(b)}
def save(name,j):
    (OUT/name).write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
def load(p):return json.loads(Path(p).read_bytes())
def verify(v):assert bind(v['path'])=={k:v[k] for k in ['path','sha256','bytes']},v['path']
a=load(BASE/'final-review-activation-01/ACTIVATION.json')
assert len(a['inputs'])==101
for v in a['inputs']:verify(v)
assert bind(BASE/'final-review-activation-01/ACTIVATION.json')['sha256']=='47cd6f7ea850ba66a6849fb1f9366614834e29ecd17877a54c412fd0337325f1'
prior=load(BASE/'source-review-repair-02/COVERAGE.json')
assert prior['sourceAccepted'] and not prior['qualified'] and prior['kernelPending']
assert prior['source']==a['source']

# Independent whole grammar expansion and independently re-lexed token/trivia restoration.
d=load(OUT/'TYPE-LOSSLESS-DICTIONARY.json')
cache={};active=set()
def expand(xs):
    ts=[]
    for x in xs:
        if isinstance(x,str):ts.append(x)
        else:
            assert set(x) in [{'ref'},{'ref','startToken','endToken'}]
            if 'startToken' in x:assert isinstance(x['startToken'],int) and isinstance(x['endToken'],int) and 0<=x['startToken']<x['endToken']
            k=x['ref'];assert k in d['dictionary']
            if k not in cache:
                assert k not in active;active.add(k);cache[k]=expand(d['dictionary'][k]);active.remove(k)
            ts.extend(cache[k])
    return ts
expanded=expand(d['main'])
for k in d['dictionary']:
    expand([{'ref':k}])
assert len(expanded)==len(d['triviaBeforeEachExpandedToken'])==d['tokenCount']==59334
rebuilt=''.join(t+s for t,s in zip(d['triviaBeforeEachExpandedToken'],expanded))+d['trailingTrivia']
raw=Path(d['rawPath']).read_bytes();assert rebuilt.encode()==raw
rx=re.compile(r'\s+|[()\[\]{};,]|[^\s()\[\]{};,]+')
text=raw.decode();matches=list(rx.finditer(text));tokens=[m.group() for m in matches if not m.group().isspace()]
assert tokens==expanded
trivia=[];pos=0
for m in matches:
    if not m.group().isspace():trivia.append(text[pos:m.start()]);pos=m.end()
assert trivia==d['triviaBeforeEachExpandedToken'] and text[pos:]==d['trailingTrivia']
display=lambda xs:' '.join(x if isinstance(x,str) else '⟪'+x['ref']+'⟫' for x in xs)
dictionary_read='\n'.join(k+' := '+display(v) for k,v in d['dictionary'].items())+'\n'
assert dictionary_read==(OUT/'TYPE-DICTIONARY-READ.txt').read_text(encoding='utf-8')
lines=[];line=''
for x in d['main']:
    token=x if isinstance(x,str) else '⟪'+x['ref']+'⟫'
    if len(line)+len(token)+1>168:lines.append(line);line=token
    else:line+=(' ' if line else '')+token
if line:lines.append(line)
assert '\n'.join(lines)+'\n'==(OUT/'TYPE-MAIN-READ.txt').read_text(encoding='utf-8')
assert len(d['dictionary'])==318 and len(lines)==492 and len(d['main'])==15705
assert len(raw)==2347133 and raw.count(b'\n')==14646 and SHA(raw)=='75eddcda040855dcfff59b515c05b0cde9b57cbfef013ad6262c38ef9f69f747'
assert all(x not in text for x in ['⋯','...','<elided>'])
assert all(x not in text.lower() for x in ['failed to pretty print','exceeded maximum recursion depth','maximum number of heartbeats'])

meta=load(BASE/'normalized-owner-evidence-01/actual-owned-metadata.json')
summary=load(BASE/'normalized-owner-evidence-01/native-kernel-and-all-owner-audit-summary.json')
binding=load(BASE/'normalized-owner-evidence-01/server-metadata-binding.json')
projection=load(BASE/'lead-execution-03/normalization-server-projection.json')
entries=meta['entries'];assert len(entries)==1
e=entries[0]
assert text==e['name']+' : '+e['type'] and e['type'].endswith('\n')
assert e['typeLines']==len(e['type'].splitlines())==14646
assert len(e['type'].encode())==2347008 and SHA(e['type'].encode())=='f4135955c948b2f951616a7752862e397eb0c8e3ba4dcdb92c0e18844886aa79'
assert '.'.join(c['value'] for c in e['components'])==e['name']==meta['anchor']
assert e['levelParams']==['u'] and e['constantKind']=='thmInfo' and e['isTheorem'] and e['bodyExpressionPresent']
assert 'value' not in e and (BASE/'normalized-owner-evidence-01/actual-owned-values.txt').read_bytes()==b''
expected_json={k:e[k] for k in ['axioms','bodyExpressionPresent','components','constantKind','isTheorem','levelParams','name']}
assert json.loads(e['rawOwnedJSON'])==expected_json
full_stdout=''
for row in entries:
    full_stdout+='OQ56_OWNED_JSON '+row['rawOwnedJSON']+'\n'
    full_stdout+='OQ56_OWNED_TYPE '+row['name']+' : '+row['type']
    if not row['isTheorem']:full_stdout+='OQ56_OWNED_VALUE '+row['name']+' := '+row['value']
full_stdout+=meta['rawOwnedCountLine']
rb=full_stdout.encode();assert len(rb)==2347700 and SHA(rb)=='346ffe8983a97480b37640af293e3b4ea33fdbe07468a9f27ada3f709d8841a0'
assert meta['rawStdoutBytes']==len(rb) and meta['rawStdoutSHA256']==SHA(rb)==binding['rawStdoutSHA256']
assert meta['rawOwnedCountLine']=='OQ56_OWNED_COUNT 1\n'
assert meta['actualOwnerCount']==meta['allTheoremCount']==summary['actualOwned']==summary['actualTheorems']==1
assert meta['nonTheoremCount']==meta['nonTheoremFullValueCount']==summary['actualNonTheorems']==0
assert summary['TYPElines']==14646 and summary['VALUElines']==0
axes=Counter(ax for row in entries for ax in row['axioms'])
assert dict(axes)=={'propext':1,'Classical.choice':1,'Quot.sound':1}==summary['axiomOccurrences']
assert set(e['axioms'])=={'propext','Classical.choice','Quot.sound'}
assert 'ALL env.constants without namespace filter' in meta['ownerDiscovery']

# Exact local normalized bytes join the hash/ns-bound server projection and original object.
for stem,key in [('actual-owned-metadata.json','metadata'),('actual-owned-types.txt','types'),('actual-owned-values.txt','values'),('native-kernel-and-all-owner-audit-summary.json','summary'),('server-metadata-binding.json','binding')]:
    local=bind(BASE/'normalized-owner-evidence-01'/stem)
    assert local['sha256']==projection[key]['sha256'] and local['bytes']==projection[key]['bytes']
assert meta['source']==summary['source']==binding['source']
assert meta['object']==summary['object']==binding['object']==a['actualFirstOriginalObject']
assert meta['source']['sha256']==a['source']['sha256'] and meta['source']['bytes']==a['source']['bytes']
assert meta['object']['sha256']=='78972bd1f02cc3f8173bad9f660f6a690587182edf3fad8d9a0d38041436f92e'
assert meta['object']['bytes']==5560336
assert meta['auditReceipt']==summary['ownedAudit01']['receipt']==binding['auditReceipt']
nprep=load(BASE/'lead-execution-03/native-preparation-projection.json')
aprep=load(BASE/'lead-execution-03/owned-audit-preparation-projection.json')
diag=load(BASE/'lead-execution-03/native-complete-diagnostic-projection.json')
assert nprep['objectBefore'] is None
assert nprep['source']==aprep['source']==meta['source']==diag['source']
assert aprep['object']==diag['object']==meta['object']
assert diag['inputSnapshot']['sha256']==meta['source']['sha256'] and diag['inputSnapshot']['bytes']==256822
for label,sm in [('native',summary['native03']),('audit',summary['ownedAudit01'])]:
    transport=load(BASE/'lead-execution-03'/(label+'-transport-result.json'))
    row=json.loads(transport['stdout']);assert transport['exit_code']==1 and not row['success']
    assert row['all_owned_group_ended'] and row['author_stop'] is None and row['Lean_calls']==1 and row['no_automatic_next_invocation']
    assert row['receipt']==sm['receipt'] and row['stdout']==sm['stdout'] and row['stderr']==sm['stderr']
    assert sm['actualExitCode']==0 and not sm['strictWrapperSuccess'] and sm['beforeAfterExact']
assert summary['native03']['protectedDerived']==25388 and summary['ownedAudit01']['protectedDerived']==25398
assert summary['ownedAudit01']['no_o'] and summary['ownedAudit01']['own_object_import']
assert summary['native03']['sourceErrors']==0 and summary['native03']['sourceWarnings']==52
assert not summary['native03']['FIRSTEMPTYIsReturnedRunnerField'] and summary['native03']['FIRSTEMPTY'] is None
assert summary['allOwnedProcessesEnded'] and not summary['ownLean']
assert diag['actualRC']==0 and diag['allOwnedEnded'] and diag['beforeAfterExact'] and diag['preservationEqual']
assert not diag['timedOut'] and not diag['cleanupEvents'] and diag['ownershipIssue'] is None
assert summary['native03']['stderr']['sha256']==summary['ownedAudit01']['stderr']['sha256']=='11ec49f9906e54894a8ffa4551c841fd9873cf63f295722c88755032b40c3cbf'
assert summary['native03']['stderr']['bytes']==summary['ownedAudit01']['stderr']['bytes']==134
warnings=load(BASE/'lead-execution-03/native-warning-classification.json')
assert Counter(x['category'] for x in warnings['warnings'])=={'unused':43,'style':5,'deprecation':4}
assert len(warnings['warnings'])==52
runtime=load(BASE/'lead-execution-03/native03-actual-runtime-observation.json')
tids=[tid for row in runtime['rows'] for tid in row['tids']]
assert len(tids)==11 and Counter(x['name'] for x in tids)=={'python3':1,'lake':3,'lean':7}
assert all(x['cpus']=='52-55' for x in tids)
zero=load(BASE/'lead-execution-03/post-audit-actual-zero-runtime-observation.json')
assert zero['rows']==[] and zero['ownHeavyLockFree'] and zero['newObjectExists'] and zero['noSignalsOrMutation']
params=load(BASE/'lead-execution-03/parameters.json')
assert params['noPublicationDeltaReadoption'] and params['publication168AlreadyAdoptedByNative01Config']['sha256']=='1c8df02880b096733b090d75862931d9551da0bc263b095a8e3442889eb3d804'
assert params['baselineReceipt']['sha256']=='cc260aa6340166147381e8290de9572a6fae16dd794ee577f0f14be27e5e5ff0'

# Every literal public let, in current actual TYPE order, joins the complete source inventory.
ctx=load(BASE/'author-repair-02/ACTUAL-PROP-CONTEXTS.json')
decls=list(re.finditer(r'\b(?:have|let)\s+([^\s:]+)\s*:',e['type']))
assert [m.group(1) for m in decls]==[r['name'] for r in ctx['publicOrdinary']]
assert len(decls)==145
public=[]
typetokens=[m for m in rx.finditer(e['type']) if not m.group().isspace()]
for no,(match,row) in enumerate(zip(decls,ctx['publicOrdinary']),1):
    stack=[];assignment=None;end=None
    for token in typetokens:
        if token.start()<match.end():continue
        atom=token.group()
        if not stack and assignment is None and atom==':=':assignment=token;continue
        if assignment is not None and not stack and atom==';':end=token;break
        if atom in ['(','[','{']:stack.append(atom)
        elif atom in [')',']','}']:
            assert stack and {'(':')','[':']','{':'}'}[stack.pop()]==atom
    assert assignment is not None and end is not None,row['name']
    actual_type=e['type'][match.end():assignment.start()]
    actual_rhs=e['type'][assignment.end():end.start()]
    public.append({'occurrence':no,'name':row['name'],'sourceType':row['type'],'sourceRHS':row['rhs'],'sourceScope':row['scope'],
       'sourceCoordinate':row['publicStatementCoordinate'],
       'actualTYPEBodyCharSpan':[match.start(),end.end()],
       'actualTYPEBodyStartLine':e['type'][:match.start()].count('\n')+1,
       'actualFullTypeTokens':' '.join(m.group() for m in rx.finditer(actual_type) if not m.group().isspace()),
       'actualFullRHSTokens':' '.join(m.group() for m in rx.finditer(actual_rhs) if not m.group().isspace()),
       'actualFullDeclarationSHA256':SHA(e['type'][match.start():end.end()].encode()),
       'completeSemanticReading':'Included in full current dictionary/main reading and joined to exact complete source coverage; no hash-only substitute.'})
def coordcount(x):
    if isinstance(x,dict):return 1 if {'byteOffset','line','column'}.issubset(x) else sum(coordcount(v) for v in x.values())
    if isinstance(x,list):return sum(coordcount(v) for v in x)
    return 0
assert coordcount(ctx)==354
assert len(ctx['fullFrozenPropositions'])==32 and len(ctx['approvedInstances'])==9 and len(ctx['APIImplicitInstances'])==5
assert len(ctx['approvedOptionalOrdinary'])==147 and len(ctx['actualSameModelChoices'])==2
assert prior['public145FullTypeRHSScopeAndCoordinates']==ctx['publicOrdinary']
assert prior['approved9InstanceFullTypeRHSScope']==ctx['approvedInstances']
assert prior['API5ImplicitFullTypeRHSScope']==ctx['APIImplicitInstances']

restoration={'schema':'oq56-unit248-currentTYPE-independent-wholebyte-token-trivia-restoration-v1',
 'atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'typeFile':bind(d['rawPath']),
 'TYPElines':14646,'TYPEbytes':2347133,'TYPEtokens':59334,'TYPEBodyBytes':2347008,'TYPEBodySHA256':SHA(e['type'].encode()),
 'dictionaryEntriesDerived':318,'mainEntriesDerived':15705,'mainReadLinesDerived':492,
 'wholeByteRoundTrip':True,'wholeTokenRoundTrip':True,'wholeTriviaRoundTrip':True,
 'independentLexerReconstruction':True,'dictionaryAndMainReadFilesMatchPacket':True,
 'noPrinterFailuresOrElision':True,'all318DictionaryEntriesAndAll492MainLinesCompletelyRead':True,
 'readDictionaryRanges':[[1,160],[161,318]],'readMainRanges':[[1,82],[83,164],[165,246],[247,328],[329,410],[411,492]],
 'fullAuditStdoutReconstruction':{'sha256':SHA(rb),'bytes':len(rb),'JSON_TYPE_VALUE_COUNTOnly':True,'exact':True},
 'requiredVALUE':{'bytes':0,'lines':0,'nonTheorems':0,'complete':True},'oldProofOrOldTYPEReplay':False}
save('TYPE-INDEPENDENT-RESTORATION.json',restoration)
save('PUBLIC-TYPE-CORRESPONDENCE.json',{'schema':'oq56-unit248-full-current-public145-TYPE-to-exact-SOURCE-correspondence-v1',
 'source':a['source'],'currentTYPE':bind(d['rawPath']),'actualTYPEOrdinaryLetCountDerived':len(public),
 'orderedNamesExactlyMatchAll145PublicSourceRows':True,'rows':public,
 'source354CoordinatesReusedExactly':True,'source32FullProps9Instances5APIReusedExactly':True,
 'newNinthTypeLocalInstanceDoesNotLeakNewPublicPremise':True,'allCurrentPublicSemanticsReviewed':True})
save('MACHINE-JOIN-VERIFICATION.json',{'schema':'oq56-unit248-independent-firstO-native-allowner-final-machine-join-v1',
 'atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':summary['source'],'FIRSTO':summary['object'],
 'native':summary['native03'],'sameFIRSTOAudit':summary['ownedAudit01'],
 'nativeOuterRC':1,'auditOuterRC':1,'strictNativeSuccess':False,'strictAuditSuccess':False,
 'FIRSTEMPTY':None,'FIRSTEMPTYIsReturnedRunnerField':False,'standing134BStderrRetained':True,
 'actualOwnedCount':1,'actualTheoremCount':1,'actualNonTheoremCount':0,'actualGeneratedHelperCount':0,
 'allActualBodiesPresent':True,'allRecursiveAxioms':dict(axes),'allRecursiveAxiomsWhitelisted':True,
 'allTYPEComplete':True,'allRequiredVALUEComplete':True,
 'rawStdoutIndependentReconstruction':restoration['fullAuditStdoutReconstruction'],
 'nativeSingleLiveFrame':{'TIDs':11,'roles':dict(Counter(x['name'] for x in tids)),'allCPU52Through55':True,'continuousObservationClaim':False},
 'postAuditActualZeroObserved':True,'postAuditOwnLockFreeObserved':True,
 'allOwnedEnded':True,'noTimeoutCleanupOwnershipIssueVerifiedByBoundServerNormalizer':True,
 'sourceObjectShaBytesNsPreserved':True,'nativeProtectedRecords':25388,'auditProtectedRecords':25398,
 'P168AdoptedOnceOriginalCfg1c8':params['publication168AlreadyAdoptedByNative01Config'],'P168Readopted':False,
 'currentExecutionPhase':'ROOT_OQ56_OQ3_40','historicalRunnerPhase39LabelsUnchanged':True,
 'sourceReviewUnionReusedExactly':True,'sourceCoordinateCountDerived':354,'ordinary145OrderExact':True,
 'reviewerMathematicalExecutions':0,'oldProducerRechecks':0})
ck=load(OUT/'CHECKPOINT.json');ck.update({'atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'currentTYPEReading':{'dictionaryEntriesRead':[[1,160],[161,318]],'dictionaryComplete':True,'currentMainLinesRead':restoration['readMainRanges'],'currentMainTotalLines':492,'currentMainComplete':True},
 'independentRestorationPending':False,'wholeCurrentTYPEByteTokenTriviaAndRawAuditReconstructionVerified':True,
 'public145ActualTypeRHSOrderScopeJoinComplete':True,'remaining':['Write complete final report/coverage/qualified evidence/manifest/FINALWRITE last release'],
 'qualified':False,'kernelPending':True})
save('CHECKPOINT.json',ck)
print(json.dumps({'PASS':True,'TYPEbytes':2347133,'TYPElines':14646,'TYPEtokens':59334,'dictionary':318,'mainLines':492,
 'wholeByteTokenTriviaRestoration':True,'rawAuditStdoutBytes':len(rb),'rawAuditStdoutExact':True,
 'public145OrderedNamesExact':True,'sourceCoordinates':354,'actualOwners':1,'theorems':1,'nonTheorems':0,
 'standard3RecursiveAX':dict(axes),'nativeActualRC':0,'auditActualRC':0,'outerRCs':[1,1],
 'strictWrapperSuccesses':[False,False],'currentQualificationFinalSealPending':True},ensure_ascii=False))
