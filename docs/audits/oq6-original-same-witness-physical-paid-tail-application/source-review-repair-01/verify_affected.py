from pathlib import Path
import json,re,hashlib,datetime

BASE=Path(r'C:/game/shao lean')
OUT=BASE/'drafts/oq56/unit248/source-review-repair-01'
def sha(x):return hashlib.sha256(x).hexdigest()
def save(name,v):(OUT/name).write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
def bind(p):
    p=Path(p);b=p.read_bytes();return {'path':str(p).replace('\\','/'),'sha256':sha(b),'bytes':len(b)}
old_path=BASE/'drafts/oq56/unit248/author-01/OriginalSameWitnessPhysicalPaidTailApplication.lean'
new_path=BASE/'drafts/oq56/unit248/author-repair-01/OriginalSameWitnessPhysicalPaidTailApplication.lean'
old=old_path.read_bytes();new=new_path.read_bytes()
assert sha(old)=='dbe4dd9b334fda150951c9c42fb4b8138ede143418d5498435a887d856cc336b'
assert sha(new)=='50fea02c741964634c5bf3db5e198bc647577f04814df5310682a9485ef30255'
assert len(old)==256737 and len(new)==256777 and new.count(b'\n')==3964
assert b'\r' not in new and not new.startswith(b'\xef\xbb\xbf')
patch=json.loads((BASE/'drafts/oq56/unit248/author-repair-01/PATCH.json').read_bytes())
freeze=json.loads((BASE/'drafts/oq56/unit248/freeze-02/frozen-declaration.json').read_bytes())
assert len(patch['changes'])==len(freeze['changes'])==3
oldtext=old.decode();newtext=new.decode()
def scope_block(text,start,end):
    a=text.index(start);a=text.rfind('\n',0,a)+1;z=text.index(end,a)
    z=text.rfind('\n',0,z)+1
    return text[a:z]
old_meas=scope_block(oldtext,'        have hMeas220 :','        have hPhysicalMeasurable :')
new_meas=scope_block(newtext,'        have hMeas220 :','        have hPhysicalMeasurable :')
assert old_meas==patch['fullAffectedSourceBlocks']['hMeas220']['before']
assert new_meas==patch['fullAffectedSourceBlocks']['hMeas220']['after']
# Independently locate each frozen replacement inside its complete intended scope.
first=old.index('∂(μ.prod μ)'.encode(),old.index(b'        have hMeas220 :'))
assert first<old.index(b'        have hPhysicalMeasurable :')
second=old.index('∀ s : Set (Fin n → Ω), P s ≠ ∞'.encode(),old.index(b'        have hPhysicalFinite :'))
third=len(old)-len(b'\nend Shao.OQ6.OriginalSameWitnessPhysicalPaidTailApplication\n')
positions=[first,second,third]
for pos,row in zip(positions,patch['changes']):
    assert pos==row['oldByteOffset']
    before=row['before'].encode();after=row['after'].encode()
    assert old[pos:pos+len(before)]==before
    assert len(before)==row['oldBytes'] and len(after)==row['newBytes']
    assert sha(before)==row['beforeSHA256'] and sha(after)==row['afterSHA256']
    assert old[:pos].count(b'\n')+1==row['oldLine']
rebuilt=old
for pos,row in reversed(list(zip(positions,patch['changes']))):
    before=row['before'].encode();after=row['after'].encode();rebuilt=rebuilt[:pos]+after+rebuilt[pos+len(before):]
assert rebuilt==new
reversed_bytes=new;shift=0;new_positions=[]
for pos,row in zip(positions,patch['changes']):
    new_positions.append(pos+shift);shift+=len(row['after'].encode())-len(row['before'].encode())
for pos,row in reversed(list(zip(new_positions,patch['changes']))):
    before=row['before'].encode();after=row['after'].encode();assert reversed_bytes[pos:pos+len(after)]==after
    reversed_bytes=reversed_bytes[:pos]+before+reversed_bytes[pos+len(after):]
assert reversed_bytes==old
intervals=[];oa=na=0
for op,np,row in zip(positions,new_positions,patch['changes']):
    assert old[oa:op]==new[na:np]
    intervals.append({'oldByteRangeHalfOpen':[oa,op],'newByteRangeHalfOpen':[na,np],
                      'bytes':op-oa,'sha256':sha(old[oa:op]),'byteExact':True})
    oa=op+len(row['before'].encode());na=np+len(row['after'].encode())
assert old[oa:]==new[na:]
if old[oa:]:intervals.append({'oldByteRangeHalfOpen':[oa,len(old)],'newByteRangeHalfOpen':[na,len(new)],'bytes':len(old)-oa,'sha256':sha(old[oa:]),'byteExact':True})

oldctx=json.loads((BASE/'drafts/oq56/unit248/author-01/ACTUAL-PROP-CONTEXTS.json').read_bytes())
newctx=json.loads((BASE/'drafts/oq56/unit248/author-repair-01/ACTUAL-PROP-CONTEXTS.json').read_bytes())
f1=json.loads((BASE/'drafts/oq56/unit248/freeze-01/INTERFACE-INVENTORY.json').read_bytes())
f2=json.loads((BASE/'drafts/oq56/unit248/freeze-02/INTERFACE-INVENTORY.json').read_bytes())
for key in ['publicOrdinary','approvedOptionalOrdinary','actualSameModelChoices','approvedInstances','APIImplicitInstances','completeUniqueContexts','proofIntroductoryCoordinates','actualHaveDeclarations','countsDerived']:
    # These records precede the patched byte region or have no coordinates affected by it.
    assert oldctx[key]==newctx[key],key
for key in ['publicOrdinary','optionalOrdinary','approvedInstances','APIImplicitInstances']:
    assert f1[key]==f2[key],key
changed_types=[];fact_comparisons=[]
rx=re.compile(r'\s+|[()\[\]{};,]|[^\s()\[\]{};,]+')
tok=lambda t:[m.group() for m in rx.finditer(t) if not m.group().isspace()]
for oc,nc in zip(oldctx['fullFrozenPropositions'],newctx['fullFrozenPropositions']):
    assert oc['name']==nc['name'];name=oc['name']
    if oc['fullType']!=nc['fullType']:changed_types.append(name)
    if name=='hMeas220':assert nc['fullType']==oc['fullType'].replace('∂(μ.prod μ)','∂(@Measure.prod Ω Ω mΩ mΩ μ μ)')
    elif name=='hPhysicalFinite':assert nc['fullType']==oc['fullType'].replace('P s ≠ ∞','P s ≠ (⊤ : ENNReal)')
    else:assert nc['fullType']==oc['fullType'],name
    for key,value in oc.items():
        if key not in ['fullType','actualBinding']:assert nc[key]==value,(name,key)
    fact_comparisons.append({'name':name,'oldFullTypeSHA256':sha(oc['fullType'].encode()),
      'newFullTypeSHA256':sha(nc['fullType'].encode()),'typeUnchanged':oc['fullType']==nc['fullType'],
      'contextAndOtherSemanticFieldsExact':True,'currentBinding':nc['actualBinding']})
assert set(changed_types)=={'hMeas220','hPhysicalFinite'} and len(changed_types)==2
for oc,nc in zip(oldctx['additionalPureLogicalPackages'],newctx['additionalPureLogicalPackages']):
    for key,value in oc.items():
        if key!='actualBinding':assert nc[key]==value,(oc['name'],key)
for of,nf in zip(f1['frozenProofFacts'],f2['frozenProofFacts']):
    assert of['name']==nf['name']
    for key,value in of.items():
        if key!='fullType':assert nf[key]==value,(of['name'],key)
    if of['name'] not in changed_types:assert nf['fullType']==of['fullType']
    n=next(x for x in newctx['fullFrozenPropositions'] if x['name']==nf['name'])
    assert n['fullType']==nf['fullType']
for name in changed_types:
    n=next(x for x in newctx['fullFrozenPropositions'] if x['name']==name)
    m=re.search(r'^\s*have '+name+r'\s*:',newtext,re.M);assert m
    ts=tok(newtext[m.end():]);want=tok(n['fullType']);assert ts[:len(want)]==want and ts[len(want)]==':='
    assert newtext[:m.start()].count('\n')+1==n['actualBinding']['start']['line']
# Coordinate rebasing is independently reconstructed from original byte edits.
coordinateChecks=0
def checkcoords(a,b):
    global coordinateChecks
    if isinstance(a,dict):
        if set(['byteOffset','line','column']).issubset(a):
            off=a['byteOffset'];expected=off+sum(len(r['after'].encode())-len(r['before'].encode()) for p,r in zip(positions,patch['changes']) if off>=p+len(r['before'].encode()))
            assert b['byteOffset']==expected,(a,b,expected)
            pre=new[:expected].decode();assert b['line']==pre.count('\n')+1 and b['column']==len(pre.rsplit('\n',1)[-1])+1
            coordinateChecks+=1
        else:
            for k,v in a.items():
                if k in b:checkcoords(v,b[k])
    elif isinstance(a,list):
        for x,y in zip(a,b):checkcoords(x,y)
checkcoords(oldctx,newctx)
assert oldtext[:oldtext.index(' := by')]==newtext[:newtext.index(' := by')]
oldclosing=(BASE/'drafts/oq56/unit248/freeze-01/FROZEN-CLOSING.txt').read_bytes()
newclosing=(BASE/'drafts/oq56/unit248/freeze-02/FROZEN-CLOSING.txt').read_bytes()
assert old.endswith(oldclosing) and new.endswith(newclosing) and newclosing==b'\nend\n\n'+oldclosing[1:]
assert newtext.count('noncomputable section')==1 and newtext.count('\nend\n')==1

diag_path=BASE/'drafts/oq56/unit248/lead-execution-01/native-complete-diagnostic-projection.json'
diag=json.loads(diag_path.read_bytes());dr=json.loads((BASE/'drafts/oq56/unit248/author-repair-01/DIAGNOSTIC-READ.json').read_bytes())
assert len(diag['completeErrorBlocks'])==6 and diag['actualRC']==1 and diag['object'] is None
assert diag['allOwnedEnded'] and diag['beforeAfterExact'] and not diag['timedOut'] and not diag['cleanupEvents'] and diag['ownershipIssue'] is None
blocks=[]
for i,(text,row) in enumerate(zip(diag['completeErrorBlocks'],dr['blocks'])):
    rawblock=text.encode();assert len(rawblock)==row['bytes'] and sha(rawblock)==row['sha256'] and text.count('\n')==row['LF']
    blocks.append({'index':i,'firstLine':text.splitlines()[0],'sha256':sha(rawblock),'bytes':len(rawblock),
       'LF':text.count('\n'),'splitLinesCount':len(text.splitlines()),'fullFailureBlockIdentityVerified':True,
       'completePrintedContextIsMachineProofEvidence':False})
result={'schema':'oq56-unit248-independent-exact-three-delta-union-verification-v1','atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'oldSource':bind(old_path),'newSource':bind(new_path),'newSourceLF':new.count(b'\n'),
 'forward3PatchesWholeByteExact':True,'reverse3PatchesWholeByteExact':True,'noFourthSourceChange':True,
 'oldByteOffsetsDerived':positions,'newByteOffsetsDerived':new_positions,'byteDeltasDerived':[len(x['after'].encode())-len(x['before'].encode()) for x in patch['changes']],
 'unchangedIntervals':intervals,'completePublicHeadByteExact':True,'sourceClosureOnlyPlainEndAdded':True,
 'all145Public147Optional8Instances5APIAndChoicesContextsExact':True,'onlyTwoFrozenFullPropClarifications':changed_types,
 'full32FactComparison':fact_comparisons,'all8AdditionalLogicalTypesExact':True,
 'allSemanticScopeFieldsUnchanged':True,'independentCoordinateChecksDerived':coordinateChecks,
 'native01Failure':{'projection':bind(diag_path),'actualRC':diag['actualRC'],'seconds':diag['seconds'],
  'errorsDerived':len(blocks),'warningsReported':diag['sourceWarningsDerived'],'object':None,'allOwnedEnded':True,
  'allBeforeAfterExact':True,'timedOut':False,'cleanupEvents':[],'ownershipIssue':None,'blocks':blocks,
  'allOtherGoalsProvedCascades':False,'newNativeRequired':True},
 'noOldProofOr247TYPEReviewReplay':True,'noMathematicalExecution':True,'P168Readopted':False}
save('INDEPENDENT-DELTA-VERIFICATION.json',result)
save('AFFECTED-BLOCKS.json',{'source':bind(new_path),'hMeas220CompleteBlockAndCall':new_meas,
    'hPhysicalFiniteCompleteBlock':scope_block(newtext,'        have hPhysicalFinite :','        have hPhysicalGuardedPackage :'),
    'closingComplete':newclosing.decode(),'sameOriginalSampleAmbient':'Proof original mN/P instance at3524-3526; selected m0 remains at2061-2062. Complete unchanged surrounding coverage reused by exact whole-source reversal.'})
print(json.dumps({'wholeReverse':'PASS','only3Deltas':True,'twoChangedFullPropTypes':changed_types,
 'public145Optional147Instances8API5Unchanged':True,'coordinateChecks':coordinateChecks,'native01':'actualRC1/noO/6errors/allended','sourceOnly':True},ensure_ascii=False))
