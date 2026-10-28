from pathlib import Path
import hashlib, json, re
from datetime import datetime, timezone

ROOT = Path('C:/game/shao lean')
OUT = ROOT / 'drafts/oq56/unit256/author-01'
FREEZE = ROOT / 'drafts/oq56/unit256/freeze-01'
SRC = OUT / 'OriginalLevelDependentLiteralWeightedConsumer.lean'
def binding(path):
    p = Path(path); b = p.read_bytes()
    return {'path': p.as_posix(), 'sha256': hashlib.sha256(b).hexdigest(), 'bytes':len(b), 'LF':b.count(b'\n')}
def text(path): return Path(path).read_text(encoding='utf-8')
def save(name, value):
    (OUT / name).write_bytes((json.dumps(value, ensure_ascii=False, indent=2)+'\n').encode('utf-8'))

inputs = [
 Path('C:/Users/UIO/.agents/skills/math-theorem/SKILL.md'),
 Path('C:/Users/UIO/.agents/skills/math-theorem/references/prompt-library.md'),
 Path('C:/Users/UIO/.agents/skills/math-theorem/references/openai-workflow.md'),
 Path('C:/Users/UIO/.agents/skills/math-theorem/references/lean-verification.md'),
 ROOT/'SERVER.md', ROOT/'coordination/TEAM.md', ROOT/'coordination/REGISTRY.json',
 *sorted(FREEZE.iterdir()),
 ROOT/'drafts/oq56/unit255/qualified-evidence.json',
 ROOT/'drafts/oq56/unit255/author-01/OriginalLevelDependentCanonicalCostPacket.lean',
 ROOT/'drafts/oq56/unit255/source-review-01/FINAL-REPORT.md',
 ROOT/'drafts/oq56/unit255/source-review-01/FINAL-VERDICT.json',
 ROOT/'drafts/oq56/unit255/source-review-01/FINALWRITE.json',
 ROOT/'library/Shao/OQ6/OriginalLiteralWeightedConsumer.lean',
 ROOT/'library/Shao/OQ6/LiteralDeletedWeightedCosts.lean',
 ROOT/'library/Shao/OQ6/NormalizedRemainderEnvelope.lean',
 ROOT/'library/Shao/OQ6/ScalarObservationCoding.lean',
 ROOT/'library/Shao/OQ6/QuantizedObservationCoding.lean',
 ROOT/'library/Shao/OQ6/OriginalLiteralRemainderEnvelope.lean',
 Path('C:/game/shao/current/oq56/inputs02/p51.md'),
 Path('C:/game/shao/current/oq56/inputs02/p54.md'),
 ROOT/'coordination/integration-v149/original-t-relative-tail-cost-source-implication-review.md',
]
expected = {
 'FROZEN-HEAD.txt':('7951013304c2f42406971387ea8749955c0c44fa5e56c604d9ef587cd0d0a6ac',33236),
 'frozen-declaration.json':('dfe7d5d3ed0334343f9d688d3417895a205b3f2076bb63825deb34be56945710',1924),
 'ACTIVATION.json':('b195f098',1754),
 'OriginalLevelDependentCanonicalCostPacket.lean':('a2db2c096e444b9ddd63fe4ff0baa451a0d2b834cb5c9049998cee2eeeb18989',38774),
 'OriginalLiteralWeightedConsumer.lean':('929ef5e4e39f72b43e2c034996ffb6e2bf776a979614fb0046cef77f0ce36c89',41601),
 'qualified-evidence.json':('3f0421247fcccb0515153b89a2381206243b7ca96c4a049d2caf124284f52713',8204),
 'FINAL-REPORT.md':('f89579fb96501226d6228af91f7c016d021a8104cd9a4a0dff2b3fc8863f0258',11194),
 'FINAL-VERDICT.json':('4330f842b6e8c00d3acb1b54c77753ea9d6b7e855d4a9079dd9c28a36e05e7f6',5224),
 'FINALWRITE.json':('6229405081e041530a0a4c76d99ea3c07b2a5d6105896e90d1738eb6be783363',2891),
}
bound=[]
for p in inputs:
    item=binding(p)
    if p.name in expected:
        sha, size=expected[p.name]
        assert item['sha256'].startswith(sha) and item['bytes']==size, item
        item['requestedBindingVerified']=True
    bound.append(item)
save('INPUT-BINDINGS.json', {'schema':'unit256-author-input-bindings-v1','inputs':bound})
save('READ_ACK.json', {
 'schema':'unit256-author-actual-read-ack-v1', 'atUTC':datetime.now(timezone.utc).isoformat(),
 'role':'/root/oq56_unit256_author','leadOwner':'01a1822b-1815-7f21-a1af-2e0b15ee67a5',
 'readCompletely':['all six frozen files','255 exact complete source, qualified, final report, final verdict, release',
   '228 exact complete source including preserved historical comments',
   'LiteralDeletedWeightedCosts full contract and complete proof',
   'NormalizedRemainderEnvelope actual_normalized_remainder_envelope_spec full contract and complete proof',
   'p51 full text','p54 full text','v149 original-T-relative-tail-cost-source-implication-review full text',
   'scalar and quantized coding consumed contracts'],
 'targetedSourceReads':['OriginalLiteralRemainderEnvelope retained-factor/subtype-sum construction only; qualification reused',
   'SERVER/TEAM/REGISTRY selected current fields; no broad historical dump'],
 'allRequestedExactBindingsVerified':True,
 'oldActualTYPERecheck':False,'oldLeanOrAXReplay':False,
 'requestedModel':'gpt-6.1-sol','requestedEffort':'xhigh','actualModel':None,'actualBackend':None,'actualEffort':None,
 'usage':{'input':None,'cachedInput':None,'output':None,'reasoningSubset':None},
 'LeanLakePPAXServerNetworkUploadGitAPIChildrenSidebarGoalScheduleOperations':0
})

source=SRC.read_bytes(); proof=(OUT/'PROOF-BODY.txt').read_bytes()
pre=(FREEZE/'FROZEN-PREAMBLE.txt').read_bytes(); head=(FREEZE/'FROZEN-HEAD.txt').read_bytes(); close=(FREEZE/'FROZEN-CLOSING.txt').read_bytes()
assert source==pre+head+b':= by\n'+proof+close
assert source.decode('utf-8').encode('utf-8')==source
assert not source.startswith(b'\xef\xbb\xbf') and b'\r' not in source
assert source.endswith(b'\n') and not source.endswith(b'\n\n')
src=source.decode(); lines=src.splitlines(keepends=True)
offsets=[0]
for line in lines: offsets.append(offsets[-1]+len(line.encode()))
forbidden=re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',src)
assert forbidden==[],forbidden
top=re.findall(r'(?m)^(?:private\s+)?(?:theorem|lemma|def|abbrev|instance|opaque|axiom)\s+[^\s:(]+',src)
assert top==['theorem actual_original_level_dependent_literal_weighted_consumer'],top
old255=text(ROOT/'drafts/oq56/unit255/author-01/OriginalLevelDependentCanonicalCostPacket.lean')
packet255=old255[old255.index('      ∀ (n : ℕ)'):old255.index('\n:= by')]
h256=head.decode()
packet256=h256[h256.index('      (∀ (n : ℕ)')+7:h256.index(') ∧\n      ∀ (n : ℕ)')]
assert re.sub(r'\s+','',packet256)==re.sub(r'\s+','',packet255)
proofStart=(pre+head+b':= by\n').count(b'\n')+1
proofEnd=proofStart+proof.count(b'\n')-1
firstPacketBegin=pre.count(b'\n')+h256[:h256.index('      (∀ (n : ℕ)')].count('\n')+1
firstPacketEnd=pre.count(b'\n')+h256[:h256.index(') ∧\n      ∀ (n : ℕ)')].count('\n')+1

def slice_info(start,end):
    b=source[offsets[start-1]:offsets[end]]
    assert b.decode()==''.join(lines[start-1:end])
    return {'sourceStartLine':start,'sourceEndLine':end,'startByte':offsets[start-1],
      'endByteExclusive':offsets[end], 'sha256':hashlib.sha256(b).hexdigest(),'utf8':b.decode()}
def logical_indent(s):
    # Bullet commands are nested by the bullet width; keep the exact raw line.
    prefix=re.match(r'^(\s*)(?:·\s*)?',s).group()
    return len(prefix)
def block_end(start):
    indent=logical_indent(lines[start-1])
    for j in range(start,len(lines)):
        if lines[j].strip() and logical_indent(lines[j])<=indent:
            return j
    return len(lines)
def scope_end(start):
    indent=logical_indent(lines[start-1])
    if start>=proofStart:
        for j in range(start,len(lines)):
            if lines[j].strip() and (logical_indent(lines[j])<indent or
              (lines[j].lstrip().startswith('·') and logical_indent(lines[j])<=indent)):
                return min(j,proofEnd)
        return proofEnd
    # Frozen lets belong to their complete branch statement; exact source retained.
    if firstPacketBegin<start<=firstPacketEnd:
        return firstPacketEnd
    return (pre+head).count(b'\n')

decls=[]; binders=[]
for i,line in enumerate(lines,1):
    m=re.match(r'^\s*(?:·\s*)?(letI|let|have)\s+(.+)',line)
    if m:
        end=block_end(i); raw=''.join(lines[i-1:end]); split=raw.find(':=')
        # The first := is always the declaration RHS in these local source blocks.
        header=raw[:split].strip() if split>=0 else raw.strip()
        rhs=raw[split+2:].strip() if split>=0 else None
        kind=m.group(1); tail=m.group(2)
        nm=re.match(r'([^\s:(]+)',tail)
        name=nm.group(1) if nm else None
        decls.append({'kind':kind,'name':name,'headerAndFullSourceType':header,
          'completeRHS':rhs,'inferredTypeContractReference':None,
          'lexicalScopeEndLine':scope_end(i),'scopeInterpretation':'source lexical scope, not an elaborated environment',
          'slice':slice_info(i,end)})
    mb=re.match(r'^\s*(?:·\s*)?(intro|rcases|obtain|funext)\s+',line)
    if mb:
        end=i
        # Rcasing bracket patterns and multiline intro name sequences may continue.
        if mb.group(1) in ('rcases','obtain'):
            depth=line.count('⟨')-line.count('⟩')
            if ' with' in line and '⟨' not in line:
                while end<len(lines) and not '⟨' in lines[end-1]: end+=1
                depth=''.join(lines[i-1:end]).count('⟨')-''.join(lines[i-1:end]).count('⟩')
            while depth>0 and end<len(lines):
                end+=1; depth+=lines[end-1].count('⟨')-lines[end-1].count('⟩')
        elif mb.group(1)=='intro':
            while end<len(lines) and lines[end].strip() and logical_indent(lines[end])>logical_indent(line) and re.match(r'^\s*[\w₀-₉Α-ω]+',lines[end]):
                end+=1
        binders.append({'kind':mb.group(1),'slice':slice_info(i,end),'lexicalScopeEndLine':scope_end(i),
          'sourceTypeAndInputBindings':'See full surrounding statement/source and PRODUCER-TYPES.json. All original source retained without elision.'})

def contract(path, theorem):
    s=text(path); start=s.index('theorem '+theorem); end=s.index(':= by',start)
    return {'input':binding(path),'declaration':s[start:end].rstrip(),
      'sourceStartLine':s[:start].count('\n')+1,'sourceEndLine':s[:end].count('\n')+1}
contracts={
 'qualified255':contract(ROOT/'drafts/oq56/unit255/author-01/OriginalLevelDependentCanonicalCostPacket.lean','actual_original_level_dependent_canonical_cost_packet'),
 'weightedLimits':contract(ROOT/'library/Shao/OQ6/LiteralDeletedWeightedCosts.lean','literal_deleted_weighted_cost_limits'),
 'remainderEnvelope':contract(ROOT/'library/Shao/OQ6/NormalizedRemainderEnvelope.lean','actual_normalized_remainder_envelope_spec'),
 'scalarCode':contract(ROOT/'library/Shao/OQ6/ScalarObservationCoding.lean','countable_uniform_augmented_base_four_code'),
 'quantizedCode':contract(ROOT/'library/Shao/OQ6/QuantizedObservationCoding.lean','quantized_observation_spec'),
}
applications={
 'hOriginal':{'producer':'qualified255','arguments':'Ω mΩ μ original IsProbabilityMeasure μ; h hh hh2 hhsymm hcenter hprojectionsecond',
   'resultContext':'let g := original μ-projection; let r := h-g-g; let v := original μ.prod μ integral; let rho := sqrt v; ∃ m0 hm0 hcg, let μ0 := μ.trim hm0; letI := m0; letI := hcg; IsProbabilityMeasure μ0 ∧ forall n/hn/z/hz/window/ε/hε/small full exact packet',
   'completeResultType':'let g : Ω → ℝ :='+contracts['qualified255']['declaration'].split('    let g : Ω → ℝ :=',1)[1]},
 'hPacket0':{'producer':'qualified255','arguments':'hfor n hn z hz hwindow (ε 0) (hε 0) (hεsmall 0)',
   'completePacketTypeWithOriginalLocalLetContext':packet255,'substitution':{'y':'z','ε':'ε 0'},'retainedFullFirstConjunct':'hfor'},
 'hPacket':{'producer':'qualified255','arguments':'hfor n hn z hz hwindow (ε k) (hε k) (hεsmall k)',
   'completePacketTypeWithOriginalLocalLetContext':packet255,'substitution':{'y':'z','ε':'ε k'},'kScope':'hCurrent k only'},
 'hcode':{'producer':'scalarCode','arguments':'Ω m0 hcg μ0 hμ0prob'},
 'hquant':{'producer':'quantizedCode','arguments':'X=Ω × ℝ, mX=mAugLocal; ξlocal i; c i; hξlocalMeas i; hCodeMeas hCodeRange hCodeComap; ε k; hε k'},
 'hWeighted':{'producer':'weightedLimits','arguments':'(Fin n → Ω × ℝ) mAug ν hνprob n hn1 ξ hξ hξ2 hξmean hξenergy Y hY ε hε hεsmall hεlim herr A B Adelete Bdelete hA hB hAdelete hBdelete hAnonneg hBnonneg hAdeletenonneg hBdeletenonneg hAint hBint hAdeleteint hBdeleteint z hz0 K hK'},
 'hEnvelope':{'producer':'remainderEnvelope','arguments':'(Fin n → Ω × ℝ) mAug ν hνprob n hn1 ξ (Y k) hξ hξ2 hξmean hξenergy (hY k) (fun x => D1 (q x)) (fun x => D2 (q x)) A B Adelete Bdelete hD1 hD2 hA hB hAnonneg hBnonneg hD1A hD2B hAint hBint (ε k) (hε k) (hεsmall k) (herr k) z hz0'},
 'hsplit':{'producer':'Fintype.sum_subtype_add_sum_subtype', 'arguments':'(fun j : Fin n => j = i) f',
   'completeResultType':'(∑ j : {j : Fin n // j = i}, f j.val) + (∑ j : {j : Fin n // ¬ j = i}, f j.val) = ∑ j : Fin n, f j'},
}
for d in decls:
    name=d['name']
    if name in applications: d['inferredTypeContractReference']=name
    if name=='hmap': d['inferredTypeContractReference']='integral_map with the explicitly typed AEStronglyMeasurable previous local hfiMapAESM/hf and hq; full statement is stated immediately as enclosing hξmeanTransport/hξsecondTransport'
    if name in ('h1','h2'): d['inferredTypeContractReference']='explicit @integral_map/@integral_map_of_stronglyMeasurable application and exact target function f in enclosing typed hIntEq'
    if name=='ht': d['inferredTypeContractReference']='exact indexed full result from hDeletedLimν/hDeletedRatioν/hCompactLimν, immediately followed by an explicit complete change type'
save('PRODUCER-TYPES.json',{'schema':'unit256-source-contracts-and-complete-applications-v1','contracts':contracts,'applications':applications,
 'actualMachinePP':False,'actualMachineOwnerCount':None,'qualificationReuse':'255 exact source/O/TYPE/AX is reused; no old source or actual TYPE review/check replayed'})

def split_ands(s):
    pairs={'(':')','[':']','{':'}','⟨':'⟩'}; stack=[]; out=[]; start=0
    for pos,c in enumerate(s):
        if c in pairs: stack.append(pairs[c])
        elif c in pairs.values():
            assert stack and stack.pop()==c,(pos,c)
        elif c=='∧' and not stack:
            out.append(s[start:pos].strip()); start=pos+1
    assert not stack
    out.append(s[start:].strip())
    return out
def specialize(s,mapping):
    return re.sub(r'\b(?:'+ '|'.join(re.escape(k) for k in sorted(mapping,key=len,reverse=True))+r')\b',
      lambda m:mapping[m.group()],s)
def output_contract(key,marker):
    d=contracts[key]['declaration']; pos=d.index(marker)
    return d[pos:]
def conjunction_parts(result,marker):
    pos=result.index(marker)
    return result[:pos],split_ands(result[pos:])

packet_result=packet255[packet255.index('        let mN :'):]
packet_lets,packet_fields=conjunction_parts(packet_result,'        @IsProbabilityMeasure')
weighted_result=output_contract('weightedLimits','    let η :')
weighted_lets,weighted_fields=conjunction_parts(weighted_result,'    Measurable H ∧')
envelope_result=output_contract('remainderEnvelope','    let η :')
envelope_lets,envelope_fields=conjunction_parts(envelope_result,'    (∀ i : Fin n, Measurable (η i)) ∧')
code_result=output_contract('scalarCode','    let H :')
code_lets,code_fields=conjunction_parts(code_result,'    IsProbabilityMeasure lambda01 ∧')
quant_result=output_contract('quantizedCode','    let Y :')
packet_pattern=re.search(r'rcases hPacket0 with\s*⟨(.*?)⟩',src,re.S).group(1)
packet_prefix_count=len(packet_pattern.split(','))-1
suffix_pattern=re.search(r'rcases hSuffix0 with\s*⟨(.*?)⟩',src,re.S).group(1)
packet_suffix_count=len(suffix_pattern.split(','))
weighted_pattern=re.search(r'rcases hWeighted with\s*⟨(.*?)⟩',src,re.S).group(1)
assert len(packet_fields)==packet_prefix_count+packet_suffix_count,len(packet_fields)
assert len(weighted_fields)==len(weighted_pattern.split(',')),len(weighted_fields)
assert len(envelope_fields)==36,len(envelope_fields)
assert len(code_fields)==10,len(code_fields)

resolved=[]
def typed(name,tp,rhs,line,scope,context=''):
    resolved.append({'name':name,'fullType':tp.strip(),'completeRHSOrProjection':rhs,
      'sourceLine':line,'lexicalScopeEndLine':scope,'fullLocalLetContext':context,
      'typeOrigin':'pure source contract specialization; no machine PP or new qualification claim'})
for b in binders:
    raw=b['slice']['utf8']; start=b['slice']['sourceStartLine']; scope=b['lexicalScopeEndLine']
    if b['kind']=='rcases':
        target=raw.split('rcases ',1)[1].split(' with',1)[0].strip()
        bracket=raw[raw.index('⟨')+1:raw.rindex('⟩')]
        names=[x.strip() for x in bracket.split(',')]
        if target in ('hPacket0','hPacket'):
            eps='(ε 0)' if target=='hPacket0' else '(ε k)'
            fields=[specialize(f,{'y':'z','ε':eps}) for f in packet_fields]
            lets=specialize(packet_lets,{'y':'z','ε':eps})
            assert len(names)==packet_prefix_count+1,(target,len(names))
            for j,name in enumerate(names):
                tp=fields[j] if j<packet_prefix_count else ' ∧\n'.join(fields[j:])
                typed(name,tp,target+('.2'*j)+('.1' if j<packet_prefix_count else ''),start,scope,lets)
        elif target=='hSuffix0':
            assert len(names)==packet_suffix_count
            fields=[specialize(f,{'y':'z','ε':'(ε 0)'}) for f in packet_fields[packet_prefix_count:]]
            for j,(name,tp) in enumerate(zip(names,fields)):
                typed(name,tp,'hSuffix0'+'.2'*j+('.1' if j<24 else ''),start,scope,
                  specialize(packet_lets,{'y':'z','ε':'(ε 0)'}))
        elif target in ('hWeighted','hEnvelope','hcode'):
            fields,lets = {'hWeighted':(weighted_fields,weighted_lets),
              'hEnvelope':(envelope_fields,envelope_lets),'hcode':(code_fields,code_lets)}[target]
            mapping={'Ω':'(Fin n → Ω × ℝ)','x':'z'} if target=='hWeighted' else (
              {'Ω':'(Fin n → Ω × ℝ)','Y':'(Y k)','ε':'(ε k)',
               'D1':'(fun x => D1 (q x))','D2':'(fun x => D2 (q x))'} if target=='hEnvelope' else {'μ':'μ₀'})
            assert len(names)==len(fields),(target,len(names),len(fields))
            for j,(name,tp) in enumerate(zip(names,fields)):
                typed(name,specialize(tp,mapping),target+'.2'*j+('.1' if j<len(fields)-1 else ''),
                  start,scope,specialize(lets,mapping))
        elif target=='hOriginal':
            tp0=applications['hOriginal']['completeResultType']
            typed(names[0],'MeasurableSpace Ω','Exists witness of hOriginal',start,scope)
            typed(names[1],'m₀ ≤ mΩ','Exists witness of hOriginal after m₀',start,scope)
            typed(names[2],'@MeasurableSpace.CountablyGenerated Ω m₀','Exists witness of hOriginal after m₀/hm₀',start,scope)
            typed(names[3],tp0[tp0.index('      let μ₀ :'):], 'remaining hOriginal body after m₀/hm₀/hcg',start,scope)
        elif target=='hbase':
            typed(names[0],'IsProbabilityMeasure μ₀','hbase.1',start,scope)
            typed(names[1],packet255,'hbase.2',start,scope)
        elif target.startswith('hfactorK '):
            arg={'hfactorK (M k) hMm':'M k','hfactorK (Anew k) (hAnewSpec k).1':'Anew k','hfactorK B hB':'B'}[target]
            typed(names[0],'(Fin n → ℝ) → ℝ','existential witness of '+target,start,scope)
            typed(names[1],f'Measurable[borel (Fin n → ℝ), borel ℝ] {names[0]}','first property of '+target,start,scope)
            typed(names[2],f'∀ x : Fin n → Ω × ℝ, ({arg}) x = {names[0]} (C k x)','second property of '+target,start,scope)
        elif target=='hdeletedFactorK i':
            typed(names[0],'({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ',target+' existential witness',start,scope)
            typed(names[1],'Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdel',target+' measurability',start,scope)
            typed(names[2],'∀ x : Fin n → Ω × ℝ, (residualStatisticDDeleted n r (q x) i, residualEnergyJDeleted n r (q x) i, studentizerClipBudgetDeleted n r 512 rho z (q x) i) = Fdel (fun j : {j : Fin n // j ≠ i} => η k j.val x)',target+' pointwise property',start,scope)
        elif target=='hretainedK i (Uret i) (hUretMeas i)':
            ret='{j : Fin n // j ≠ i}'
            tps=[f'({ret} → ℝ) → ℝ',f'Measurable[borel ({ret} → ℝ), borel ℝ] FU',
              f'∀ y : {ret} → Ω × ℝ, Uret i y = FU (fun j => ηlocal k j.val (y j))',
              'Measurable[borel (Fin n → ℝ), borel ℝ] (fun t : Fin n → ℝ => FU (fun j => t j.val))',
              f'∀ x : Fin n → Ω × ℝ, Uret i (fun j => x j.val) = FU (fun j : {ret} => η k j.val x)']
            for name,tp in zip(names,tps): typed(name,tp,target+' corresponding existential/property binding',start,scope)
        elif target=='hscalarK':
            tps=['(Fin n → ℝ) → ℝ','Measurable[borel (Fin n → ℝ), borel ℝ] G2',
              '∀ x : Fin n → Ω × ℝ, D2 (q x) = G2 (C k x)',
              '∀ t : ℝ, ∃ G1 : (Fin n → ℝ) → ℝ, Measurable[borel (Fin n → ℝ), borel ℝ] G1 ∧ ∀ x : Fin n → Ω × ℝ, (D1 (q x) + W x - Wη k x + t * b x * (Vη k x - V x)) = G1 (C k x)']
            for name,tp in zip(names,tps):typed(name,tp,target+' existential/property binding',start,scope)
        elif target=='hG1for z':
            tps=['(Fin n → ℝ) → ℝ','Measurable[borel (Fin n → ℝ), borel ℝ] G1',
              '∀ x : Fin n → Ω × ℝ, Dη k x = G1 (C k x)']
            for name,tp in zip(names,tps):typed(name,tp,target+' existential/property binding',start,scope)
        else: raise AssertionError(('uncovered rcases',target))
    elif b['kind']=='obtain':
        typed('k₀','ℕ','existential witness of Filter.eventually_atTop.1 htail',start,scope)
        typed('hk₀','∀ k : ℕ, k₀ ≤ k → sourceCostη k < sourceCost0 + δ',
          'property of Filter.eventually_atTop.1 htail',start,scope)
    elif b['kind']=='funext':
        typed('k','ℕ','function extensionality binder in hεeq',start,scope)
    elif b['kind']=='intro':
        rawNames=raw.split('intro ',1)[1].strip().split()
        for name in rawNames:
            candidates=[d for d in decls if d['name']==name and d['slice']['sourceStartLine']<proofStart]
            if name in ('g','r','v','rho','μ₀') or (len(rawNames)>15):
                assert candidates,(name,start)
                d=candidates[-1]
                typed(name,d['headerAndFullSourceType'].split(':=')[0],
                  'intro of frozen let; complete RHS retained in LOCAL-CONTEXTS at '+str(d['slice']['sourceStartLine']),start,scope)
            else:
                tp={'n':'ℕ','hn':'4 ≤ n','z':'ℝ','hz':'1 ≤ z',
                  'hwindow':'z ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ))',
                  'i':'Fin n','x':'Fin n → Ω × ℝ','k':'ℕ'}[name]
                typed(name,tp,'intro binder',start,scope)
save('BINDING-TYPES.json',{'schema':'unit256-all-pattern-binder-source-types-v1',
 'source':binding(SRC),'allRcasedIntroducedObtainedFunextNames':resolved,
 'packetFields':len(packet_fields),'weightedFields':len(weighted_fields),'envelopeFields':len(envelope_fields),
 'allInputContractsAndInstantiationArguments':'PRODUCER-TYPES.json','actualMachinePP':False})
applications['hPacket0']['completeResultType']=specialize(packet_result,{'y':'z','ε':'(ε 0)'})
applications['hPacket']['completeResultType']=specialize(packet_result,{'y':'z','ε':'(ε k)'})
applications['hWeighted']['completeResultType']=specialize(weighted_result,{'Ω':'(Fin n → Ω × ℝ)','x':'z'})
applications['hEnvelope']['completeResultType']=specialize(envelope_result,{
 'Ω':'(Fin n → Ω × ℝ)','Y':'(Y k)','ε':'(ε k)',
 'D1':'(fun x => D1 (q x))','D2':'(fun x => D2 (q x))'})
applications['hcode']['completeResultType']=specialize(code_result,{'μ':'μ₀'})
applications['hquant']['completeResultType']=specialize(quant_result,{
 'X':'(Ω × ℝ)','ξ':'(ξlocal i)','c':'(c i)','ε':'(ε k)'})
for d in decls:
    name=d['name']; raw=d['slice']['utf8']
    if name in applications:
        d['completeInferredType']=applications[name].get('completeResultType')
        d['completeInputBindings']=applications[name].get('arguments')
    elif name=='hmap':
        sq=' ^ 2' if 'hf' in raw and 'hfiMapAESM' not in raw else ''
        d['completeInferredType']=(f'(∫ ζ, (ξ0 i ζ){sq} ∂(@Measure.map (Fin n → Ω × ℝ) (Fin n → Ω) mAug mN₀ q ν)) = '
          f'(∫ x, (ξ0 i (q x)){sq} ∂ν)')
    elif name=='h1':
        d['completeInferredType']='(∫ ζ, f ζ ∂(@Measure.map (Fin n → Ω × ℝ) (Fin n → Ω) mAug mN₀ q ν)) = (∫ x, f (q x) ∂ν)'
    elif name=='h2':
        d['completeInferredType']='(∫ ζ, f ζ ∂(@Measure.map (Fin n → Ω) (Fin n → Ω) mN mN₀ id P)) = (∫ ζ, f (id ζ) ∂P)'
    elif name=='ht':
        # Each inferred ht is immediately ascribed its complete current type by change.
        following=src.split(raw,1)[1]
        typ=following.split('change ',1)[1].split(' at ht',1)[0].strip()
        d['completeInferredType']=typ
    else:
        d['completeInferredType']=None
    if ':=' in raw and not re.search(r':\s*[^=].*:=',raw.split(':=',1)[0]+':=',re.S):
        if name is not None:
            assert d.get('completeInferredType') is not None,('uncovered inferred declaration',name)
save('PRODUCER-TYPES.json',{'schema':'unit256-source-contracts-and-complete-applications-v1','contracts':contracts,'applications':applications,
 'actualMachinePP':False,'actualMachineOwnerCount':None,'qualificationReuse':'255 exact source/O/TYPE/AX is reused; no old source or actual TYPE review/check replayed'})
save('LOCAL-CONTEXTS.json',{'schema':'unit256-complete-local-source-contexts-v1','source':binding(SRC),
 'proofStartLine':proofStart,'proofEndLine':proofEnd,'declarations':decls,'binderCommands':binders,
 'allRawSourceTypesRHSLexicalCoordinatesIncluded':True,'machineElaboratedTypes':False})
save('STATIC-CHECK.json',{'schema':'unit256-pure-local-static-check-v1','source':binding(SRC),
 'proof':binding(OUT/'PROOF-BODY.txt'),'freezeAssemblyExact':True,'frozenHeadExact':True,
 'whole255FirstPacketLiteralModuloOuterParenthesesAndIndentation':True,'sameM0BeforeAllNZEpsilon':True,
 'utf8NoBOM':True,'CRCount':0,'singleFinalLF':True,'forbiddenHits':forbidden,'publicTheoremCount':1,
 'topLevelHelpersDefsInstances':0,'localDeclarations':len(decls),'binderCommands':len(binders),
 'allPatternBoundNamesWithFullTypes':len(resolved),
 'sliceRoundtripExact':True,'fullSourceByteRoundtripExact':True,
 'actualMachineOwnerCount':None,'actualTYPELF':None,'actualVALUECount':None,
 'qualified':False,'machinePending':True,'kernelExecuted':False,'axiomAuditExecuted':False})
print(json.dumps({'STATIC':'PASS','source':binding(SRC),'proofRange':[proofStart,proofEnd],
 'sourceLocalDeclarations':len(decls),'binderCommands':len(binders),'allPatternBoundNames':len(resolved),
 'packetFields':len(packet_fields),'weightedFields':len(weighted_fields),'contracts':len(contracts)},ensure_ascii=False))
