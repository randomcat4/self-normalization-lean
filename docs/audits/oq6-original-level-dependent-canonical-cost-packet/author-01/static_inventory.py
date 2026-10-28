from pathlib import Path
import datetime
import hashlib
import json
import re
import traceback

B = Path('C:/game/shao lean')
O = B / 'drafts/oq56/unit255/author-01'
F = B / 'drafts/oq56/unit255/freeze-01'
P = O / 'OriginalLevelDependentCanonicalCostPacket.lean'

def sha(b):
    return hashlib.sha256(b).hexdigest()

def dump(name, obj):
    (O/name).write_bytes((json.dumps(obj, ensure_ascii=False, indent=2)+'\n').encode('utf-8'))

def swap(text, env):
    if not env:
        return text
    pat = r"(?<![\w'])(?:"+'|'.join(re.escape(x) for x in sorted(env, key=len, reverse=True))+r")(?![\w'])"
    return re.sub(pat, lambda m: '('+env[m.group(0)]+')', text)

def split_and(text):
    out, begin, stack = [], 0, []
    pairs = {')':'(', ']':'[', '}':'{', '⟩':'⟨'}
    for i,c in enumerate(text):
        if c in '([{⟨':
            stack.append(c)
        elif c in ')]}⟩':
            assert stack and stack.pop()==pairs[c], (i,c,text[max(0,i-50):i+50])
        elif c=='∧' and not stack:
            out.append(text[begin:i].strip())
            begin=i+1
    assert not stack
    out.append(text[begin:].strip())
    return out

def leading_lets(text, overrides=None):
    ls=text.splitlines(keepends=True)
    decls,j,env=[],0,{}
    while j<len(ls) and not ls[j].strip():
        j+=1
    while j<len(ls) and re.match(r'^\s*let(?:I)?\b',ls[j]):
        indent=len(ls[j])-len(ls[j].lstrip())
        end=j+1
        while end<len(ls):
            if ls[end].strip() and len(ls[end])-len(ls[end].lstrip())<=indent:
                break
            end+=1
        block=''.join(ls[j:end]).strip()
        k,rest=block.split(None,1)
        left,rhs=rest.split(':=',1)
        if k=='letI':
            name,ty=None,left.strip().removeprefix(':').strip()
        else:
            name,ty=left.split(':',1)
            name,ty=name.strip(),ty.strip()
        rhs=rhs.strip()
        decls.append({'name':name,'fullType':ty,'fullRHS':rhs,'exactBlock':block})
        if name:
            env[name]=(overrides or {}).get(name,swap(rhs,env))
        j=end
    return decls,''.join(ls[j:]).strip(),env

def target(text):
    head=text.split(':= by\n',1)[0]
    return head[head.index('    let g :'):].rstrip()

def main():
    raw=P.read_bytes()
    src=raw.decode('utf-8')
    lines=src.splitlines(keepends=True)
    offsets=[0]
    for line in lines:
        offsets.append(offsets[-1]+len(line.encode('utf-8')))
    proof_start=src[:src.index(':= by\n')+len(':= by\n')].count('\n')+1
    proof_end=len(lines)-4
    theorem_line=next(i+1 for i,l in enumerate(lines) if l.startswith('theorem '))
    def coord(a,b):
        text=''.join(lines[a:b])
        assert raw[offsets[a]:offsets[b]]==text.encode('utf-8')
        return {'startLine':a+1,'endLineInclusive':b,'startByte0':offsets[a],
                'endByteExclusive':offsets[b],'sha256':sha(text.encode('utf-8')),'text':text}
    s254=(B/'drafts/oq56/unit254/author-01/OriginalLevelDependentCanonicalCoding.lean').read_text(encoding='utf-8')
    s252=(B/'drafts/oq56/unit252/author-01/OriginalLevelDependentCorrectionEnvelope.lean').read_text(encoding='utf-8')
    s250=(B/'drafts/oq56/unit250/author-repair-01/OriginalLevelDependentWeightedSourceCost.lean').read_text(encoding='utf-8')
    t254=target(s254)
    canconj=t254[t254.index('        @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ ∧'):]
    canparts=split_and(canconj)
    t252=swap(target(s252),{'z':'y'})
    elets,econj,eenv=leading_lets(t252,{
        'g':'g','r':'r','v':'v','rho':'rho','P':'P','N':'N','ξ0':'ξ0',
        'D':'D1','J':'J','Ddelete':'Ddel','Jdelete':'Jdel','A':'A',
        'Adelete':'fun i ζ => Adel ζ i','B':'B','Bdelete':'fun i ζ => Bdelete ζ i','e':'D2','V':'V0'})
    eparts=[swap(x,eenv) for x in split_and(econj)]
    t250=swap(target(s250),{'z':'y','C0':'(512 : ℝ)'})
    wlets,wconj,wenv=leading_lets(t250,{
        'g':'g','r':'r','v':'v','rho':'rho','P':'P','N':'N','ξ0':'ξ0','D1':'D1','B':'B',
        'Bdelete':'Bdelete','S':'S0','Sdelete':'S0delete','fullTest':'fullTest0',
        'deletedTest':'deleteTest0','I':'Ioriginal','sourceCost':'costOriginal'})
    wparts=[swap(x,wenv) for x in split_and(wconj)]
    assert len(wparts)==5
    supplements={
        'hcanonical':t254,
        'hcan':canconj,
        'hcost':t252,
        'hweighted':t250,
        'hIncident':'''Shao.OQ5.P35.unorderedPairSum (fun (j k : Fin n) => r (ζ j) (ζ k)) -
Shao.OQ5.P35.unorderedPairSum (Shao.OQ6.ResidualDeletion.eraseIncident
  (fun (j k : Fin n) => r (ζ j) (ζ k)) i) =
Shao.OQ6.ResidualDeletion.rowSum (fun (j k : Fin n) => r (ζ j) (ζ k)) i'''
    }
    starts=[]
    for i,line in enumerate(lines):
        m=re.match(r'^(\s*)(letI|let|have)\b(.*)',line)
        if m:
            starts.append((i,len(m.group(1)),m.group(2)))
    records=[]
    for a,indent,kind in starts:
        b=a+1
        while b<len(lines):
            if lines[b].strip() and len(lines[b])-len(lines[b].lstrip())<=indent:
                break
            b+=1
        block=''.join(lines[a:b]).rstrip()
        first=block.strip().split(None,1)[1]
        left,rhs=first.split(':=',1)
        if kind=='letI':
            name,params,ty='anonymous-instance@'+str(a+1),'',left.strip().removeprefix(':').strip()
            origin='explicit source annotation'
        else:
            mm=re.match(r'([^\s:(]+)(.*)',left.strip(),re.S)
            name,tail=mm.group(1),mm.group(2)
            depth,colon=0,None
            for ii,c in enumerate(tail):
                if c in '([{': depth+=1
                elif c in ')]}': depth-=1
                elif c==':' and depth==0:
                    colon=ii
                    break
            if colon is None:
                params,ty='',supplements[name]
                origin='full exact source-bound producer instantiated in current lexical context'
            else:
                params,ty=tail[:colon].strip(),tail[colon+1:].strip()
                origin='explicit source annotation'
        records.append({'kind':kind,'name':name,'sourceParameters':params,
                        'fullType':('∀ '+params+',\n'+ty) if params else ty,'resultType':ty,
                        'fullRHS':rhs.strip(),'typeOrigin':origin,'indent':indent,
                        'sourceSlice':coord(a,b)})
    scope_ranges=[]
    for rr in records:
        if rr['kind']=='have' and rr['fullRHS'].startswith('by'):
            scope_ranges.append((rr['sourceSlice']['startLine'],rr['sourceSlice']['endLineInclusive'],
                                 rr['indent'],'proof of '+rr['name']))
    def scope(line_no,indent):
        cs=[r for r in scope_ranges if r[0]<line_no<=r[1] and r[2]<indent]
        if cs:
            a,b,d,owner=max(cs,key=lambda r:(r[2],r[0]))
            return {'enclosing':owner,'contextFromLine':a,'visibleThroughLine':b,
                    'declarationIndent':indent,'coordinateConvention':'1-based inclusive'}
        return {'enclosing':'frozen result telescope' if line_no<proof_start else 'whole theorem proof',
                'contextFromLine':theorem_line if line_no<proof_start else proof_start,
                'visibleThroughLine':proof_start-2 if line_no<proof_start else proof_end,
                'declarationIndent':indent,'coordinateConvention':'1-based inclusive'}
    for rr in records:
        rr['scope']=scope(rr['sourceSlice']['startLine'],rr.pop('indent'))
    resultdefs={x['name']:x for x in records if x['kind']=='let' and x['sourceSlice']['startLine']<proof_start}
    introtypes={n:d['resultType']+'\n:= '+d['fullRHS'] for n,d in resultdefs.items()}
    introtypes.update({'n':'ℕ','hn':'4 ≤ n','y':'ℝ','hy':'1 ≤ y',
                      'hywindow':'y ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ))',
                      'ε':'ℝ','hε':'0 < ε','hεsmall':'ε < 1 / (4 * Real.sqrt (n : ℝ))'})
    can_names=['hP₀prob','hP₀map','hO','hOindep','hgcoord','hgenergy','hQid','hW0eq','hV0eq','hT0eq',
               'hD1m','hD2m','hhalf','hTclipm','hTclipOriginal','hTcliplaw','hνprob','hqpres','hs','hηeval',
               'hηindep','hηL2','hηInts','hηmean','hηenergy','hηnull','hVηnull','hpositiveDenominator','hCmeas',
               'hCcomap','hfactor','hretained','hscalar','hdeletedFactor','hTηmeas','hZ0m','hZ0Original','hZmeas',
               'hZcodedlaw','hZ0law','hZcodedreal','hsigned','hcomparison']
    assert len(can_names)==len(canparts),(len(can_names),len(canparts))
    binding_records=[]
    def add(a,b,kind,pairs):
        binding_records.append({'origin':kind,'line':a+1,
                                'scope':scope(a+1,len(lines[a])-len(lines[a].lstrip())),
                                'producerSlice':coord(a,b),
                                'bindings':[{'name':n,'fullDependentType':t,
                                             'fullSourceBindingCommand':''.join(lines[a:b]),
                                             'RHSKind':'exact source binder/destructuring command; introduced let values are included with their full type'}
                                            for n,t in pairs]})
    for a,line in enumerate(lines):
        if a+1<proof_start:
            continue
        trimmed=line.strip()
        if trimmed.startswith('intro '):
            b=a+1
            names=trimmed[6:].split()
            if names[0]=='mN':
                while b<len(lines) and len(lines[b])-len(lines[b].lstrip())>2:
                    names.extend(lines[b].strip().split())
                    b+=1
            if names[0] in ('g','μ₀','n','mN'):
                pairs=[(n,introtypes[n]) for n in names]
            else:
                pairs=[(n,'Fin n' if n=='i' else '{j : Fin n // j ≠ i}') for n in names]
            add(a,b,'intro',pairs)
        elif trimmed.startswith('funext '):
            add(a,a+1,'funext',[(n,'Fin n' if n=='i' else 'Fin n → Ω') for n in trimmed[7:].split()])
        elif trimmed.startswith('rcases '):
            b=a+1
            while b<len(lines) and lines[b].strip() and len(lines[b])-len(lines[b].lstrip())>len(line)-len(line.lstrip()):
                b+=1
            cmd=''.join(lines[a:b]).strip()
            if cmd.startswith('rcases hcanonical '):
                pairs=[('m₀','MeasurableSpace Ω'),('hm₀','m₀ ≤ mΩ'),
                       ('hcg','@MeasurableSpace.CountablyGenerated Ω m₀'),
                       ('hbase',t254[t254.index('      let μ₀ :'):])]
            elif cmd.startswith('rcases hbase '):
                pairs=[('hμ₀prob','IsProbabilityMeasure μ₀'),
                       ('hfor',t254.split('      IsProbabilityMeasure μ₀ ∧\n',1)[1].strip())]
            elif cmd.startswith('rcases hcan '):
                pairs=list(zip(can_names,canparts))
            elif cmd.startswith('rcases hcost '):
                names=['_discard1','_discard2','_discard3','_discard4','hAIP','hAdelIP','hBIP','hBdeleteIP',
                       'heIP','hFullBounds','hDeletedBounds']
                pairs=list(zip(names,eparts[:11]))+[('_discard_remaining',' ∧\n'.join(eparts[11:]))]
            elif cmd.startswith('rcases hweighted '):
                pairs=list(zip(['hIoriginalPos','hFullOriginalI','hDeleteOriginalI','hCostOriginalNonneg','hCostOriginalBound'],wparts))
            elif cmd.startswith('rcases hdeletedFactor i '):
                pairs=[('Fdel','({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ'),
                       ('hFdel','Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdel'),
                       ('hFdelpoint','∀ x : Fin n → Ω × ℝ, (Ddel (q x) i, Jdel (q x) i, Bdelete (q x) i) = Fdel (fun j : {j : Fin n // j ≠ i} => η j.val x)')]
            elif cmd.startswith('rcases hDiff i '):
                diffr=next(x for x in records if x['name']=='hDiff')
                pairs=list(zip(['hADm','hBDm','hMassm','hADi','hBDi','hMassi'],split_and(diffr['resultType'])))
            else:
                raise AssertionError(('uncovered destruct',a+1,cmd))
            add(a,b,'rcases',pairs)
    assert all(r['fullType'] and r['fullRHS'] for r in records)
    dump('SOURCE-INVENTORY.json',{'schema':'unit255-complete-source-local-inventory-v1','sourceSHA256':sha(raw),
         'coordinateConvention':'UTF8 byte offsets 0-based half-open; lines 1-based inclusive','actualModuleOwners':None,
         'machinePending':True,'records':records,'count':len(records)})
    dump('PRODUCER-BINDINGS.json',{'schema':'unit255-complete-source-bindings-v1','sourceSHA256':sha(raw),
         'actualModuleOwners':None,'notMachinePP':True,'bindingCount':sum(len(x['bindings']) for x in binding_records),
         'records':binding_records})
    dump('PRODUCER-TYPES.json',{'schema':'unit255-complete-source-producer-types-v1',
         'note':'Full SOURCE expressions in the original mΩ/μ context and current n/y; not machine TYPE evidence.',
         'qualified254Result':t254,'qualified254CurrentContract':canparts,
         'qualified252AtCurrentYFullResult':t252,'qualified252Lets':elets,'qualified252ExpandedConjuncts':eparts,
         'qualified250AtCurrentY512FullResult':t250,'qualified250Lets':wlets,'qualified250ExpandedConjuncts':wparts})
    md=['# 第255单元完整源码局部库存\n','源码库存不是实际 machine owner / PP 结果。全部完整类型、右端和词法范围按精确当前源列出。\n']
    for x in records:
        q=x['sourceSlice']
        md += [f"## {x['kind']} {x['name']} — 第{q['startLine']}–{q['endLineInclusive']}行\n",
               f"UTF8字节[{q['startByte0']},{q['endByteExclusive']})；片段SHA256 `{q['sha256']}`。\n",
               '完整类型：\n```lean\n'+x['fullType']+'\n```\n',
               '完整右端：\n```lean\n'+x['fullRHS']+'\n```\n',
               '词法范围：'+json.dumps(x['scope'],ensure_ascii=False)+'\n']
    (O/'SOURCE-INVENTORY.md').write_bytes(('\n'.join(md).rstrip()+'\n').encode('utf-8'))
    md=['# 第255单元全部引入与拆解绑定\n','所列类型为完整源码依赖表达式；实际 elaborated TYPE 尚待服务器。\n']
    for x in binding_records:
        md += [f"## {x['origin']} — 第{x['line']}行\n",'```lean\n'+x['producerSlice']['text'].rstrip()+'\n```\n']
        for v in x['bindings']:
            md += ['`'+v['name']+'`\n```lean\n'+v['fullDependentType']+'\n```\n']
        md += ['词法范围：'+json.dumps(x['scope'],ensure_ascii=False)+'\n']
    (O/'INTRO-AND-DESTRUCTURING-INVENTORY.md').write_bytes(('\n'.join(md).rstrip()+'\n').encode('utf-8'))
    inputs=[
      F/'ACTIVATION.json',F/'frozen-declaration.json',F/'FROZEN-PREAMBLE.txt',F/'FROZEN-HEAD.txt',F/'FROZEN-CLOSING.txt',F/'SOURCE-ROUTE.md',
      F/'FREEZE-STATIC-FAILURE-01.json',F/'FREEZE-STATIC-FAILURE-CLARIFICATION.json',
      B/'drafts/oq56/unit254/author-01/OriginalLevelDependentCanonicalCoding.lean',B/'drafts/oq56/unit254/qualified-evidence.json',
      B/'drafts/oq56/unit254/source-review-01/FINAL-REPORT.md',B/'drafts/oq56/unit254/source-review-01/FINAL-VERDICT.json',
      B/'drafts/oq56/unit254/source-review-01/FINALWRITE.json',
      B/'drafts/oq56/unit250/author-01/OriginalLevelDependentWeightedSourceCost.lean',
      B/'drafts/oq56/unit250/author-repair-01/OriginalLevelDependentWeightedSourceCost.lean',B/'drafts/oq56/unit250/qualified-evidence.json',
      B/'drafts/oq56/unit252/author-01/OriginalLevelDependentCorrectionEnvelope.lean',B/'drafts/oq56/unit252/qualified-evidence.json',
      B/'library/Shao/OQ6/OriginalClippedCanonicalCostPacket.lean',
      Path('C:/game/shao/current/oq56/inputs02/p51.md'),Path('C:/game/shao/current/oq56/inputs02/p54.md'),
      B/'coordination/integration-v149/original-t-relative-tail-cost-source-implication-review.md',
      Path('C:/Users/UIO/.agents/skills/math-theorem/SKILL.md'),
      Path('C:/Users/UIO/.agents/skills/math-theorem/references/prompt-library.md'),
      Path('C:/Users/UIO/.agents/skills/math-theorem/references/openai-workflow.md'),
      Path('C:/Users/UIO/.agents/skills/math-theorem/references/lean-verification.md'),
      B/'SERVER.md',B/'coordination/TEAM.md',
      B/'drafts/oq56/unit254/author-01/static_inventory.py',
      Path('C:/Users/UIO/.codex/skills/windows-gbk-utf8/SKILL.md')]
    bindings=[]
    for p in inputs:
        data=p.read_bytes()
        bindings.append({'path':p.as_posix(),'sha256':sha(data),'bytes':len(data),
                         'readCoverage':'full text' if p.name!='TEAM.md' else 'selected current and ownership/resource clauses'})
    expected={
        '78d92960a8ea7142bea38f17133ce757af2f64ee1a304c390cc19f8bfa4863ae':F/'FROZEN-HEAD.txt',
        '4f216cc6d31130f00d98acbb817d4e04762461715781d30135613af55757b387':F/'frozen-declaration.json',
        'd12c222bd79655ff1ba2d7442cc580b962f971b929fa41adaddcd0db829d564f':B/'drafts/oq56/unit254/qualified-evidence.json',
        '2d90010762b6d92cbf249512825c8eb429b387288325a21edcc8f90553d95896':B/'drafts/oq56/unit254/author-01/OriginalLevelDependentCanonicalCoding.lean',
        '9eab174ed67833ed40df18ea889fb60a98e0c49401d4955872560e15bc4ebe6f':B/'drafts/oq56/unit250/author-repair-01/OriginalLevelDependentWeightedSourceCost.lean',
        'fc91fdfe3a92b472deba8ecea7183c62381643524d9cf875a3e594c649782020':B/'drafts/oq56/unit252/author-01/OriginalLevelDependentCorrectionEnvelope.lean'}
    assert all(sha(p.read_bytes())==h for h,p in expected.items())
    frozen=json.loads((F/'frozen-declaration.json').read_text(encoding='utf-8'))
    for key in ('preamble','head','closing','route','oldAcceptedSource','bearing254Candidate','bearing250Qualified','bearing252Qualified'):
        entry=frozen[key]
        data=Path(entry['path']).read_bytes()
        assert sha(data)==entry['sha256'] and len(data)==entry['bytes'],key
    for unit in (250,252,254):
        qualified=json.loads((B/f'drafts/oq56/unit{unit}/qualified-evidence.json').read_text(encoding='utf-8'))
        entry=qualified['source']
        data=Path(entry['path']).read_bytes()
        assert qualified['qualified'] is True
        assert sha(data)==entry['sha256'] and len(data)==entry['bytes'],unit
    composition=(F/'FROZEN-PREAMBLE.txt').read_bytes()+(F/'FROZEN-HEAD.txt').read_bytes()+b':= by\n'+(O/'PROOF-BODY.txt').read_bytes()+(F/'FROZEN-CLOSING.txt').read_bytes()
    assert composition==raw
    forbidden=re.findall(r'(?<![\w])(?:sorry|admit|axiom|unsafe|native_decide)(?![\w])',src)
    top=re.findall(r'(?m)^(theorem|lemma|def|abbrev|instance|opaque|axiom)\b([^\n]*)',src)
    assert not forbidden and len(top)==1 and top[0][0]=='theorem'
    assert not raw.startswith(b'\xef\xbb\xbf') and b'\r' not in raw
    assert raw.endswith(b'\n') and not raw.endswith(b'\n\n')
    assert (F/'FROZEN-HEAD.txt').read_bytes().count(b'\n')==276
    assert src.count('OriginalLevelDependentCanonicalCoding.actual_original_level_dependent_canonical_normalized_coding')==1
    assert src.count('OriginalLevelDependentCorrectionEnvelope.actual_original_level_dependent_correction_envelope')==1
    assert src.count('OriginalLevelDependentWeightedSourceCost.actual_original_level_dependent_weighted_source_cost')==1
    oldcore=s254.split('        @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ ∧',1)[1].split('\n:= by\n',1)[0]
    newcore=src.split('        @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ ∧',1)[1].split(' ∧\n        (∀ ξ : Fin n → Ω, 0 ≤ A ξ',1)[0]
    assert oldcore==newcore
    slices=[x['sourceSlice'] for x in records]+[x['producerSlice'] for x in binding_records]
    assert all(raw[q['startByte0']:q['endByteExclusive']].decode('utf-8')==q['text'] for q in slices)
    counts={'sourceBytes':len(raw),'sourceLF':raw.count(b'\n'),'frozenHeadLF':276,
            'proofLF':(O/'PROOF-BODY.txt').read_bytes().count(b'\n'),'proofStartLine':proof_start,'proofEndLine':proof_end,
            'sourcePublicTheorems':1,'topLevelHelpersDefsInstances':0,'localLet':sum(x['kind']=='let' for x in records),
            'localLetI':sum(x['kind']=='letI' for x in records),'localHave':sum(x['kind']=='have' for x in records),
            'introDestructCommands':len(binding_records),'introDestructBindings':sum(len(x['bindings']) for x in binding_records),
            'sourceSliceRoundtrips':len(slices),'inputBindings':len(bindings),'actualModuleOwners':None}
    dump('INPUT-HASH-BINDINGS.json',bindings)
    dump('STATIC-CHECK.json',{'schema':'unit255-author-static-only-v1','atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'sourceSHA256':sha(raw),'status':'PASS','exactFrozenComposition':True,'frozenCanonical254FullContractLiteralPreserved':True,
         'fullSourceSliceRoundtrip':True,'UTF8NoBOM':True,'LFOnly':True,'singleFinalNewline':True,
         'forbiddenTokens':forbidden,'onePublicTheoremNoTopLevelHelpers':True,'expectedInputHashesVerified':True,
         'fullFreezeRecordBindingsVerified':True,'allThreeQualifiedSourceBindingsVerified':True,
         'counts':counts,'LeanExecuted':False,'kernelChecked':False,'qualified':False,'machinePending':True})
    print(json.dumps({'status':'STATIC_PASS_ONLY','sourceSHA256':sha(raw),'counts':counts},ensure_ascii=False))

try:
    main()
except Exception as e:
    stamp=datetime.datetime.now(datetime.timezone.utc).isoformat()
    prior=list(O.glob('STATIC-FAILURE-*.json'))
    dump('STATIC-FAILURE-'+str(len(prior)+1).zfill(2)+'.json',{'atUTC':stamp,'failure':repr(e),'traceback':traceback.format_exc(),
         'sourceEffects':'static output only; no frozen input mutation','LeanServerNetworkAPI':0})
    raise
