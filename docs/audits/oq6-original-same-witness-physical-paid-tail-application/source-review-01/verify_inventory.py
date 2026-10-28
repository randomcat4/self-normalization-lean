from pathlib import Path
import json,re,hashlib,datetime,collections
BASE=Path(r'C:/game/shao lean')
OUT=BASE/'drafts/oq56/unit248/source-review-01'
SRC=BASE/'drafts/oq56/unit248/author-01/OriginalSameWitnessPhysicalPaidTailApplication.lean'
raw=SRC.read_bytes(); s=raw.decode('utf-8'); lines=s.splitlines(keepends=True)
author=json.loads((BASE/'drafts/oq56/unit248/author-01/ACTUAL-PROP-CONTEXTS.json').read_bytes())
freeze_dir=BASE/'drafts/oq56/unit248/freeze-01'
freeze=json.loads((freeze_dir/'INTERFACE-INVENTORY.json').read_bytes())
rx=re.compile(r'\s+|[()\[\]{};,]|[^\s()\[\]{};,]+')
def tok(t):return [m.group() for m in rx.finditer(t) if not m.group().isspace()]
def sha(t):return hashlib.sha256(t if isinstance(t,bytes) else t.encode()).hexdigest()
def coord(offset):
    pre=s[:offset];return {'line':pre.count('\n')+1,'column':len(pre.rsplit('\n',1)[-1])+1,'byteOffset':len(pre.encode())}
def save(name,v):(OUT/name).write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
head_end=s.index(' := by')
head=s[:head_end]
decs=list(re.finditer(r'^\s*let ([^ :\n]+)\s*:',head,re.M))
assert len(decs)==145
ordinary=[]
for n,(m,f,a) in enumerate(zip(decs,freeze['publicOrdinary'],author['publicOrdinary']),1):
    name=m.group(1); p=m.start()+len(m.group())-len(m.group().lstrip())
    assert name==f['name']==a['name'] and f['publicOccurrence']==n==a['publicOccurrence']
    for k in ['name','type','rhs','scope','publicOccurrence']:assert a[k]==f[k],(n,k)
    expected='let '+name+' : '+f['type']+' := '+f['rhs']
    assert tok(s[p:])[:len(tok(expected))]==tok(expected),n
    c=coord(p); assert c==a['publicStatementCoordinate'],(n,c,a['publicStatementCoordinate'])
    ordinary.append({'publicOccurrence':n,'name':name,'type':f['type'],'rhs':f['rhs'],
                     'frozenScope':f['scope'],'coordinate':c,'typeRHSTokensExact':True,'fullSemanticsRead':True})
assert author['approvedOptionalOrdinary']==freeze['optionalOrdinary']
assert author['approvedOptionalOrdinary'][:145]==freeze['publicOrdinary']
assert [x['name'] for x in freeze['optionalOrdinary'][145:]]==['cg','m₀']
choice_rows=[]
for name in ['cg','m₀']:
    row=next(x for x in freeze['optionalOrdinary'][145:] if x['name']==name)
    m=re.search(r'^  let '+re.escape(name)+r'\s*:',s,re.M);assert m
    text='let '+name+' : '+row['type']+' := '+row['rhs'];assert tok(s[m.start():])[:len(tok(text))]==tok(text)
    choice_rows.append({'name':name,'coordinate':coord(m.start()+2),'type':row['type'],'rhs':row['rhs'],'scope':row['scope']})
have_names=[m.group(1) for m in re.finditer(r'^\s*have ([^ :\n]+)',s,re.M)]
facts=author['fullFrozenPropositions']+author['additionalPureLogicalPackages']
assert len(facts)==40 and len(set(x['name'] for x in facts))==40
assert set(have_names)|{'hAllAtN247','hStudentizerWindow'}==set(x['name'] for x in facts)
assert len(have_names)==38
prop_rows=[]
for f in facts:
    name=f['name']; typ=f['fullType']
    if name=='h247':
        assert tok(typ)==tok((freeze_dir/'EXPECTED-H247-PROP.txt').read_text(encoding='utf-8'))
        m=re.search(r'^  have h247 :=',s,re.M);assert m
        method='sole inferred producer; full expected Prop exact-frozen and complete qualified247 actual TYPE read'
    elif name=='hAllAtN247':
        m=re.search(r'\(hAllAtN247\s*:',s);assert m
        part=s[m.end():];assert tok(part)[:len(tok(typ))]==tok(typ)
        method='complete explicit lambda-input type token match'
    elif name=='hStudentizerWindow':
        m=re.search(r'^ +intro hStudentizerWindow\b',s,re.M);assert m
        assert tok(typ)==tok('1 + rho ≤ Real.sqrt (n : ℝ)')
        package=next(x for x in facts if x['name']=='hPhysicalGuardedPackage')['fullType']
        assert tok(package)[:len(tok(typ))+2]==['(']+tok(typ)+['→']
        method='explicit antecedent of complete typed guarded package; no new hypothesis'
    else:
        m=re.search(r'^\s*have '+re.escape(name)+r'\s*:',s,re.M);assert m,name
        part=s[m.end():];want=tok(typ);got=tok(part)
        assert got[:len(want)]==want,(name,'full type mismatch')
        assert got[len(want)]==':=',(name,'incomplete type')
        method='complete explicit source type followed immediately by proof assignment'
    # Source starts are derived independently; author binding coordinates are comparison only.
    off=m.start(); off+=len(s[off:])-len(s[off:].lstrip())
    # lambda binder's reported start is the binder name rather than its opening parenthesis.
    if name=='hAllAtN247':off=m.start()+1
    c=coord(off)
    assert c['line']==f['actualBinding']['start']['line'],(name,c,f['actualBinding'])
    prop_rows.append({'name':name,'contextId':f['contextId'],'fullTypeSHA256':sha(typ),'fullTypeBytes':len(typ.encode()),
                     'independentlyDerivedCoordinate':c,'authorReportedCoordinate':f['actualBinding']['start'],
                     'verification':method,'fullTypeAndScopeSemanticsRead':True})
preamble=(freeze_dir/'FROZEN-PREAMBLE.txt').read_bytes();fhead=(freeze_dir/'FROZEN-HEAD.txt').read_bytes()
assert raw.startswith(preamble+fhead)
call=(freeze_dir/'FROZEN-H247-CALL.txt').read_bytes();assert len(call)==222 and raw.count(call)==1
intro=(freeze_dir/'FROZEN-INITIAL-INTRO.txt').read_bytes();assert raw.count(intro)==1
assert raw.index(call)<raw.index('  intro g r v rho β cWindow'.encode())
assert raw.endswith((freeze_dir/'FROZEN-CLOSING.txt').read_bytes())
original_intro=next(x for x in s.splitlines() if x.startswith('  intro Ω '));assert len(original_intro.split()[1:])==16
payment_intro=next(x for x in s.splitlines() if x.startswith('  intro mN '));assert len(payment_intro.split()[1:])==47
physical_intro=next(x for x in s.splitlines() if x.strip().startswith('intro Tphysical '));assert len(physical_intro.split()[1:])==4
assert not any(re.search(r'\b'+w+r'\b',s) for w in ['sorry','admit','axiom','unsafe','native_decide'])
assert not re.search(r'\b(kClipped|kPayment)\b',s)
assert len(re.findall(r'^theorem ',s,re.M))==1
save('INDEPENDENT-INVENTORY.json',{'atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),
  'source':{'path':str(SRC).replace('\\','/'),'sha256':sha(raw),'bytes':len(raw),'LF':raw.count(b'\n')},
  'exactFrozenPreambleHeadClosing':True,'fullFrozenHeadBytes':len(fhead),'soleH247CallBytes':len(call),
  'soleH247CallBeforeGlobalIntro':True,'originalPiIntroCount':16,'paymentIntroCount':47,'physicalIntroCount':4,
  'publicOrdinary':ordinary,'optional147ExactAndOnlyCgM0Additional':True,'sameDataChoices':choice_rows,
  'fullFacts':prop_rows,'countsDerived':{'publicOrdinary':len(ordinary),'optionalOrdinary':len(freeze['optionalOrdinary']),
  'frozenProps':len(author['fullFrozenPropositions']),'additionalLogicalPackages':len(author['additionalPureLogicalPackages']),
  'haveDeclarations':len(have_names),'ordinaryChoices':len(choice_rows),'newNatCutoffs':0,
  'approvedInstances':len(author['approvedInstances']),'APIImplicitContexts':len(author['APIImplicitInstances'])},
  'forbiddenEscapesAbsent':True,'oldProofReReviewOrMathExecution':False})
print(json.dumps({'allInventoryAssertionsPassed':True,'ordinary145':True,'facts40':True,
  'firstChoiceSourceLine':choice_rows[0]['coordinate']['line'],'secondChoiceSourceLine':choice_rows[1]['coordinate']['line']},ensure_ascii=False))
