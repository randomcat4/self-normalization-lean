from pathlib import Path
import hashlib,json,re,traceback
from datetime import datetime,timezone

ROOT=Path('C:/game/shao lean')
OUT=ROOT/'drafts/oq56/unit257/author-repair-01'
FREEZE=OUT.parent/'freeze-01'
SRC=OUT/'OriginalLevelDependentStrictMomentFrontier.lean'
def text(p):return p.read_text(encoding='utf-8')
def bind(p):
    b=p.read_bytes()
    return {'path':p.as_posix(),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'LF':b.count(b'\n')}
def save(name,x):(OUT/name).write_bytes((json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
def contract(p,name):
    s=text(p); a=s.index('theorem '+name); z=s.index(':= by',a)
    return {'input':bind(p),'fullDeclaration':s[a:z].rstrip(),
            'startLine':s[:a].count('\n')+1,'endLine':s[:z].count('\n')+1}
def split_ands(s):
    pairs={'(':')','[':']','{':'}','⟨':'⟩'}; stack=[]; fields=[]; a=0
    for i,c in enumerate(s):
        if c in pairs:stack.append(pairs[c])
        elif c in pairs.values():
            assert stack and stack.pop()==c,(i,c)
        elif c=='∧' and not stack:fields.append(s[a:i].strip());a=i+1
    assert not stack
    return fields+[s[a:].strip()]
def replace_tokens(s,mapping):
    # Lean identifiers include Greek and subscript characters. Token boundaries
    # are based on the full identifier, not Python's narrower word boundary.
    pat=r'(?<![\w₀-₉])(?:'+'|'.join(re.escape(k) for k in sorted(mapping,key=len,reverse=True))+r')(?![\w₀-₉])'
    return re.sub(pat,lambda m:mapping[m.group()],s)
def result_at(c,marker):return c['fullDeclaration'][c['fullDeclaration'].index(marker):]
def fields_at(s,marker):
    a=s.index(marker)
    return s[:a],split_ands(s[a:])

try:
    source=SRC.read_bytes();src=source.decode('utf-8');proof=(OUT/'PROOF-BODY.txt').read_bytes()
    pre=(FREEZE/'FROZEN-PREAMBLE.txt').read_bytes();head=(FREEZE/'FROZEN-HEAD.txt').read_bytes();close=(FREEZE/'FROZEN-CLOSING.txt').read_bytes()
    assert source==pre+head+b':= by\n'+proof+b'\n'+close
    assert source.decode('utf-8').encode('utf-8')==source
    assert not source.startswith(b'\xef\xbb\xbf') and b'\r' not in source
    assert source.endswith(b'\n') and not source.endswith(b'\n\n')
    bad=re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',src)
    assert not bad,bad
    top=re.findall(r'(?m)^(?:private\s+)?(?:theorem|lemma|def|abbrev|instance|opaque|axiom)\s+[^\s:(]+',src)
    assert top==['theorem actual_original_level_dependent_strict_moment_frontier'],top
    qualified256=ROOT/'drafts/oq56/unit256/author-repair-01/OriginalLevelDependentLiteralWeightedConsumer.lean'
    c256=contract(qualified256,'actual_original_level_dependent_literal_weighted_consumer')
    cIID=contract(ROOT/'library/Shao/OQ6/IIDSourceStrictMomentBudgets.lean','actual_iid_source_z_strict_moment_budgets')
    cNorm=contract(ROOT/'library/Shao/OQ6/NormalizedStrictMomentBudgets.lean','actual_source_z_strict_truncated_moment_budgets')
    h256=c256['fullDeclaration']; h257=head.decode()
    packet256=h256[h256.index('      (∀ (n : ℕ)')+7:h256.index(') ∧\n      ∀ (n : ℕ)')]
    packet257=h257[h257.index('      (∀ (n : ℕ)')+7:h257.index(') ∧\n      ∀ (n : ℕ)')]
    consumer256=h256[h256.index('      ∀ (n : ℕ)'):]
    consumer257=h257[h257.index('      ∀ (n : ℕ)'):h257.index('        ) ∧\n        ∀ (p : ℝ)')]
    consumer257=consumer257.replace('        (\n        @IsProbabilityMeasure','        @IsProbabilityMeasure',1)
    compact=lambda s:re.sub(r'\s+','',s)
    assert compact(packet256)==compact(packet257)
    assert compact(consumer256)==compact(consumer257)
    consumerLets,consumerFields=fields_at(consumer256[consumer256.index('        let mN :'):],'        @IsProbabilityMeasure')
    packetLets,packetFields=fields_at(packet256[packet256.index('        let mN :'):],'        @IsProbabilityMeasure')
    iidResult=result_at(cIID,'    let β :')
    iidOuterLets,iidOuterFields=fields_at(iidResult,'    0 ≤ β ∧')
    iidNResult=iidOuterFields[-1]
    assert iidNResult.startswith('(∀ (n : ℕ)')
    iidNResult=iidNResult[iidNResult.index('        let P :'):-1]
    iidNLets,iidNFields=fields_at(iidNResult,'        IsProbabilityMeasure P ∧')
    normResult=result_at(cNorm,'    let η :')
    normLets=normResult[:normResult.index('    (∀ i : Fin n, δ0 i <')]
    normOutput=normResult[normResult.index('    (∀ i : Fin n, Integrable'):]
    normFields=split_ands(normOutput)
    assert len(normFields)==5,len(normFields)
    lines=src.splitlines(keepends=True);offsets=[0]
    for line in lines:offsets.append(offsets[-1]+len(line.encode('utf-8')))
    proofStart=(pre+head+b':= by\n').count(b'\n')+1
    proofEnd=proofStart+proof.count(b'\n')-1
    def snippet(start,end):
        b=source[offsets[start-1]:offsets[end]]
        assert b.decode('utf-8')==''.join(lines[start-1:end])
        return {'startLine':start,'endLine':end,'startByte':offsets[start-1],
          'endByteExclusive':offsets[end],'sha256':hashlib.sha256(b).hexdigest(),'utf8':b.decode('utf-8')}
    def indent(s):return len(re.match(r'^(\s*)(?:·\s*)?',s).group())
    def block_end(start):
        d=indent(lines[start-1])
        for j in range(start,len(lines)):
            if lines[j].strip() and indent(lines[j])<=d:return j
        return len(lines)
    def scope_end(start):
        if start<proofStart:
            d=indent(lines[start-1])
            for j in range(start,len(lines)):
                if lines[j].strip() and indent(lines[j])<d:return j
            return (pre+head).count(b'\n')
        d=indent(lines[start-1])
        for j in range(start,len(lines)):
            if lines[j].strip() and (indent(lines[j])<d or (lines[j].lstrip().startswith('·') and indent(lines[j])<=d)):
                return min(j,proofEnd)
        return proofEnd
    apps={
      'hOriginal':{'producer':'qualified256','arguments':'μ h hh hh2 hhsymm hcenter hprojectionsecond in original Ω/mΩ',
        'fullResultType':result_at(c256,'    let g :')},
      'hAnalytic':{'producer':'hconsumer from qualified256','arguments':'n hn z hz hwindow',
        'fullResultType':consumerLets+' ∧\n'.join(consumerFields)},
      'hPacket0':{'producer':'hfor from the SAME qualified256 witness','arguments':'n hn z hz hwindow (ε 0) (hε 0).1 (hε 0).2',
        'fullResultType':replace_tokens(packetLets+' ∧\n'.join(packetFields),{'y':'z','ε':'(ε 0)'})},
      'hOriginalBudget':{'producer':'originalIID','arguments':'Ω mΩ μ originalIsProbabilityMeasure g hgOriginal hg2Original p hp2 hp3 hgp cBudget hcBudget',
        'fullResultType':iidResult},
      'hNormalized':{'producer':'normalizedStrict','arguments':'(Fin n → Ω × ℝ) mAug ν hνprob n hn1 ξ (fun i => (hξPacket i).1) (fun i => (hξPacket i).2.1) (fun i => (hξPacket i).2.2) hξenergy Y (fun k i => (hYpacket k i).2.1) ε (fun k => (hε k).1) (fun k => (hε k).2) hεlim (fun k i => (hYpacket k i).2.2) z hz cBudget hcBudget',
        'fullResultType':replace_tokens(normResult,{'Ω':'(Fin n → Ω × ℝ)'})},
    }
    decls=[];commands=[]
    for i,line in enumerate(lines,1):
        m=re.match(r'^\s*(?:·\s*)?(letI|let|have)\s+(.+)',line)
        if m:
            end=block_end(i);raw=''.join(lines[i-1:end]);cut=raw.find(':=')
            header=raw[:cut].strip() if cut>=0 else raw.strip()
            rhs=raw[cut+2:].strip() if cut>=0 else None
            n=re.match(r'([^\s:(]+)',m.group(2));name=n.group(1) if n else None
            inferred=None
            if name in apps:inferred=apps[name]['fullResultType']
            if name=='hm':
                if 'integral_map_of_stronglyMeasurable' in raw:
                    inferred='(∫ ζ, Fz (ξ0 i ζ) ∂(@Measure.map (Fin n → Ω) (Fin n → Ω) mN mN₀ id P)) = (∫ ζ, Fz (ξ0 i (id ζ)) ∂P)'
                else:
                    inferred='(∫ ζ, Fz (ξ0 i ζ) ∂(@Measure.map (Fin n → Ω × ℝ) (Fin n → Ω) mAug mN₀ q ν)) = (∫ x, Fz (ξ0 i (q x)) ∂ν)'
            if name=='hi':inferred='Integrable[mAug] (fun x => Fz (ξ0 i (q x))) ν'
            # A source-only inventory records every explicit header verbatim;
            # inferred have headers are backed by complete producer types above.
            if m.group(1)=='have' and re.match(r'^have\s+[^\s:(]+\s*$',header):
                assert inferred is not None,('uncovered inferred have',name,i)
            decls.append({'kind':m.group(1),'name':name,'fullHeaderAndExplicitSourceType':header,
              'fullRHS':rhs,'fullInferredSourceType':inferred,'lexicalScopeEndLine':scope_end(i),
              'slice':snippet(i,end),'machineElaborated':False})
        b=re.match(r'^\s*(?:·\s*)?(intro|rcases|by_contra|filter_upwards)\b',line)
        if b and i>=proofStart:
            end=i
            if b.group(1)=='rcases':
                while '⟨' not in ''.join(lines[i-1:end]):end+=1
                depth=''.join(lines[i-1:end]).count('⟨')-''.join(lines[i-1:end]).count('⟩')
                while depth>0:
                    end+=1;depth+=lines[end-1].count('⟨')-lines[end-1].count('⟩')
            elif b.group(1)=='intro':
                while end<len(lines) and lines[end].strip() and indent(lines[end])>indent(line):end+=1
            elif b.group(1)=='filter_upwards':
                while 'with ' not in ''.join(lines[i-1:end]):end+=1
            commands.append({'kind':b.group(1),'slice':snippet(i,end),'lexicalScopeEndLine':scope_end(i)})
    resolved=[]
    def typed(name,tp,rhs,cmd,context=''):
        resolved.append({'name':name,'fullType':tp.strip(),'fullSourceLetContext':context,
          'origin':rhs,'commandStartLine':cmd['slice']['startLine'],'lexicalScopeEndLine':cmd['lexicalScopeEndLine'],
          'evidenceClass':'PURE_SOURCE_DERIVED_STATIC_NOT_MACHINE_PP'})
    frozenDecls={}
    for d in decls:
        if d['slice']['startLine']<proofStart and d['name']:
            frozenDecls.setdefault(d['name'],[]).append(d)
    simple={'n':'ℕ','hn':'4 ≤ n','z':'ℝ','hz':'1 ≤ z',
      'hwindow':'z ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ))',
      'p':'ℝ','hp2':'2 < p','hp3':'p ≤ 3','hgp':'Integrable[mΩ] (fun o : Ω => Real.rpow |g o| p) μ',
      'cBudget':'ℝ','hcBudget':'0 < cBudget','i':'Fin n','hβzero':'β = 0',
      'hMomentWindow':'β = 0 ∨ (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) * Real.rpow (n : ℝ) ((p - 2) / (2 * p)))',
      'τ':'ℝ','δ':'ℝ','hτ':'0 < τ','hδ':'0 < δ'}
    for cmd in commands:
        raw=cmd['slice']['utf8'];kind=cmd['kind']
        if kind=='intro':
            names=raw.split('intro ',1)[1].strip().split()
            for name in names:
                if name in frozenDecls:
                    d=frozenDecls[name][-1]
                    variableType=d['fullHeaderAndExplicitSourceType'].split(':',1)[1].strip()
                    typed(name,variableType,
                      'intro of frozen local let; full RHS: '+d['fullRHS'],cmd)
                else:
                    assert name in simple,('unmapped intro',name,raw)
                    typed(name,simple[name],'intro of the exact frozen/enclosing target',cmd)
        elif kind=='by_contra':
            typed('hnot','¬ Integrable[mΩ] (fun o => g o ^ 2) μ','by_contra in hgSquareIntegrable',cmd)
        elif kind=='filter_upwards':
            names=raw.split('with ',1)[1].strip().split()
            types=['ℕ','(∀ i : Fin n, δη k i < (1 / 2 : ℝ)) ∧ Lη k < cBudget * z ^ 2',
              '(∫ x, |Qε k x| ∂ν) < τ','|sourceCostη k - sourceCost0| < τ',
              '|compactCostη k - compactCost0| < τ',
              'sourceCostη k ≤ 64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ) + δ']
            assert len(names)==len(types)
            for name,tp in zip(names,types):typed(name,tp,'pointwise binding from the five complete eventual sources in filter_upwards',cmd)
        elif kind=='rcases':
            target=raw.split('rcases ',1)[1].split(' with',1)[0].strip()
            names=[x.strip() for x in raw[raw.index('⟨')+1:raw.rindex('⟩')].split(',')]
            if target=='hOriginal':
                tps=['MeasurableSpace Ω','m₀ ≤ mΩ','@MeasurableSpace.CountablyGenerated Ω m₀',
                     h256[h256.index('      let μ₀ :'):]]
                for name,tp in zip(names,tps):typed(name,tp,'existential field of the complete qualified256 result',cmd)
            elif target=='hbase':
                tps=['IsProbabilityMeasure μ₀',packet256,consumer256]
                for name,tp in zip(names,tps):typed(name,tp,'conjunction field of hbase under μ₀/m₀/hcg',cmd)
            elif target=='hAnalytic':
                assert len(names)==len(consumerFields),(len(names),len(consumerFields))
                for j,(name,tp) in enumerate(zip(names,consumerFields)):
                    typed(name,tp,'hAnalytic'+'.2'*j+('.1' if j<len(names)-1 else ''),cmd,consumerLets)
            elif target=='hPacket0':
                assert len(names)==6
                epsMap={'y':'z','ε':'(ε 0)'}
                tps=packetFields[:5]+[' ∧\n'.join(packetFields[5:])]
                for j,(name,tp) in enumerate(zip(names,tps)):
                    typed(name,replace_tokens(tp,epsMap),'hPacket0'+'.2'*j+('.1' if j<5 else ''),cmd,replace_tokens(packetLets,epsMap))
            elif target=='hOriginalBudget':
                assert len(names)==len(iidOuterFields)==5
                for j,(name,tp) in enumerate(zip(names,iidOuterFields)):
                    typed(name,tp,'hOriginalBudget'+'.2'*j+('.1' if j<4 else ''),cmd,iidOuterLets)
            elif target=='hSource n hn1 z hz':
                assert len(names)==len(iidNFields)==11
                for j,(name,tp) in enumerate(zip(names,iidNFields)):
                    typed(name,tp,'hSource n hn1 z hz field'+str(j+1),cmd,iidOuterLets+iidNLets)
            elif target=='hSourceStrict hMomentWindow':
                tps=['Loriginal ≤ Real.rpow cWindow p',
                  '∀ i : Fin n, δoriginal i < (1 / 2 : ℝ)','Loriginal < cBudget * z ^ 2']
                for name,tp in zip(names,tps):typed(name,tp,'conjunction field of hSourceStrict hMomentWindow; original law',cmd)
            elif target=='hNormalized hδ0Half hL0Strict':
                tps=normFields[:4]+['ℕ','∀ k : ℕ, kStrict ≤ k → (∀ i : Fin n, δη k i < (1 / 2 : ℝ)) ∧ Lη k < cBudget * z ^ 2']
                assert len(names)==len(tps)==6
                for j,(name,tp) in enumerate(zip(names,tps)):
                    typed(name,replace_tokens(tp,{'Ω':'(Fin n → Ω × ℝ)'}),
                      'hNormalized hδ0Half hL0Strict conjunct/existential field'+str(j+1),cmd,
                      replace_tokens(normLets,{'Ω':'(Fin n → Ω × ℝ)'}) if j<4 else '')
            else:raise AssertionError(('uncovered pattern',target))
    save('PRODUCER-TYPES.json',{'schema':'unit257-complete-source-contracts-and-applications-v1',
      'contracts':{'qualified256':c256,'originalIID':cIID,'normalizedStrict':cNorm},'applications':apps,
      'source':bind(SRC),'machinePP':False,'actualOwnerCount':None,
      'qualified256ExactSourceReuseOnly':True,'oldActualTYPENotReread':True})
    save('LOCAL-CONTEXTS.json',{'schema':'unit257-complete-local-source-types-rhs-lexical-slices-v1',
      'source':bind(SRC),'proofStartLine':proofStart,'proofEndLine':proofEnd,
      'declarations':decls,'bindingCommands':commands,'machineElaborated':False,
      'allInferredHaveTypesCompleteByProducerOrIntegralAPISpecialization':True})
    save('BINDING-TYPES.json',{'schema':'unit257-all-tactic-pattern-source-type-inventory-v1',
      'source':bind(SRC),'allPatternBindings':resolved,'patternCommandCount':len(commands),
      'allPatternBoundNames':len(resolved),'consumerFields':len(consumerFields),'packetFields':len(packetFields),
      'IIDOuterFields':len(iidOuterFields),'IIDSourceFields':len(iidNFields),'normalizedOutputFields':len(normFields),
      'completeContractsAndEveryApplication':'PRODUCER-TYPES.json','machinePP':False,'actualOwnerCount':None})
    save('STATIC-CHECK.json',{'schema':'unit257-pure-local-static-check-v1','source':bind(SRC),
      'proof':bind(OUT/'PROOF-BODY.txt'),'freezeAssemblyExact':True,'frozenHeadExact':True,
      'whole255FirstPacketPreservedViaExactQualified256FirstPacketEquality':True,
      'whole256ConsumerLiteralModuloOuterParenthesesAndWhitespace':True,
      'sameM0BeforeAllNCurrentZEpsilonPBudget':True,'UTF8NoBOM':True,'CRCount':0,'singleFinalLF':True,
      'forbiddenHits':bad,'publicTheoremCount':1,'topLevelHelperDefInstanceCount':0,
      'allSourceSlicesRoundtripExact':True,'sourceLocalDeclarations':len(decls),
      'patternCommands':len(commands),'patternBoundNamesWithCompleteTypes':len(resolved),
      'actualOwnerCount':None,'actualTYPE':None,'actualVALUE':None,'actualAX':None,
      'kernelExecuted':False,'axiomAuditExecuted':False,'qualified':False,'machinePending':True})
    print(json.dumps({'STATIC':'PASS','source':bind(SRC),'proofRange':[proofStart,proofEnd],
      'localDeclarations':len(decls),'patternCommands':len(commands),'patternNames':len(resolved),
      'consumerFields':len(consumerFields),'packetFields':len(packetFields)},ensure_ascii=False))
except Exception:
    failure={'atUTC':datetime.now(timezone.utc).isoformat(),'stage':'local static inventory generation',
      'exception':traceback.format_exc(),'LeanServerNetworkOperations':0}
    n=1
    while (OUT/f'LOCAL-FAILURE-{n:02d}.json').exists():n+=1
    save(f'LOCAL-FAILURE-{n:02d}.json',failure)
    raise
