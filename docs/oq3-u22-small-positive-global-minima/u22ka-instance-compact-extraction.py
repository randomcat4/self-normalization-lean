from pathlib import Path
import hashlib,json,re,datetime
r=Path('/root/rivermind-data/shao-lean-20261021/runs/oq3/u22ka-20261028')
w=Path('/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3')
sha=lambda b:hashlib.sha256(b).hexdigest()
raw=(r/'statement-instance.log').read_bytes()
assert sha(raw)=='81ab9c8c64b870f9eb9a815524db5d2e1f9ebd6cc5acbd3e4303eaae0fc97fe8'
assert sha((w/'Shao/OQ3/SymmetricEightAtomSmallPositiveMinimum.lean').read_bytes())=='8222b7afcc4418e4cb1c8269858fefec17a647a1c7784b0076cf6a2509e58b47'
assert sha((w/'.lake/build/lib/lean/Shao/OQ3/SymmetricEightAtomSmallPositiveMinimum.olean').read_bytes())=='22f737f0f7ca3500f3cdf932671546c3dac5d0a043c4f0cff8bd8fb85e6ee40d'
text=raw.decode('utf-8');parts=text.split('ACTUAL_RATE_NEZERO_RAW ')[1:];assert len(parts)==2
records=[]
def parse(text):
    tokens=re.findall(r'"(?:\\.|[^"\\])*"|[()\[\],]|[^\s()\[\],]+',text)
    pos=0
    def seq(end=None):
        nonlocal pos
        out=[]
        while pos<len(tokens):
            t=tokens[pos];pos+=1
            if t==end:return out
            if t=='(':out.append(seq(')'))
            elif t=='[':out.append(['LIST',*seq(']')])
            elif t in (')',']'):raise ValueError('unbalanced '+t)
            elif t!=',':out.append(t)
        assert end is None
        return out
    tree=seq();assert pos==len(tokens);return tree

def app(e):
    if e[0]=='Lean.Expr.app':
        assert len(e)==3
        h,a=app(e[1]);return h,a+[e[2]]
    return e,[]
def const(e,name):return isinstance(e,list) and len(e)==3 and e[:2]==['Lean.Expr.const','`'+name]
def bvar(e):
    assert len(e)==2 and e[0]=='Lean.Expr.bvar';return int(e[1])
def walk(e):
    if isinstance(e,list):
        yield e
        for x in e:yield from walk(x)
def digest(e):return sha(json.dumps(e,separators=(',',':')).encode())
for i,p in enumerate(parts):
    expr=p.split('\nKA_STATEMENT_INSTANCE_BINDING PASS')[0].rstrip()
    tree=parse(expr)
    h,args=app(tree)
    assert const(h,'MeasureTheory.IsProbabilityMeasure.neZero') and len(args)==4
    assert const(args[0],'Real') and const(args[1],'Real.measurableSpace')
    mu=bvar(args[2]);ph,pa=app(args[3]);assert const(ph,'And.left') and len(pa)==3
    dh,da=app(pa[2]);assert const(dh,'Shao.OQ3.symmetric_eight_atom_law_and_phase_gap') and len(da)==1
    a=bvar(da[0]);assert a==mu+2
    ih,ia=app(pa[0]);assert const(ih,'MeasureTheory.IsProbabilityMeasure') and len(ia)==3
    assert const(ia[0],'Real') and const(ia[1],'Real.measurableSpace')
    # Validate every nested group parses, and collect ALL raw constants deterministically.
    constants=sorted({n[1][1:] for n in walk(tree) if n and n[0]=='Lean.Expr.const'})
    records.append({'ordinal':i+1,'completeRawExprBytes':len(expr.encode()),'completeRawExprSHA256':sha(expr.encode()),'allParsedTokensConsumed':True,'actualMuDeBruijn':mu,'actualAmplitudeDeBruijn':a,'exactApplicationShape':'MeasureTheory.IsProbabilityMeasure.neZero Real Real.measurableSpace mu (And.left probabilityProposition remainingConjunction (Shao.OQ3.symmetric_eight_atom_law_and_phase_gap a))','inferredProbabilityPropositionASTSHA256':digest(pa[0]),'inferredRemainingConjunctionASTSHA256':digest(pa[1]),'exactJDCallASTSHA256':digest(pa[2]),'allRawConstants':constants,'rawExprNodeCount':sum(1 for n in walk(tree) if n and isinstance(n[0],str) and n[0].startswith('Lean.Expr.'))})
assert 'KERNEL_LET_NODES 2' in text and 'SOURCE_STATEMENT_LETS 3' in text and 'SOURCE_PROOF_LETS 1' in text
out={'atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'COMPLETE_RAW_EXPR_PARSE_AND_EXACT_HIDDEN_INSTANCE_SHAPE_PASS','rawLogSHA256':sha(raw),'rawLogBytes':len(raw),'fullRawLogRemainsServerOnly':True,'completeRawLogModelRead':False,'sourceStatementLets':3,'sourceProofLets':1,'kernelDataLetNodes':2,'distinctRawInstanceValues':len(records),'instances':records,'omissionsFromSkeleton':'Only inferable type/proposition parameters are replaced by labels; complete raw Expr blocks and proposition AST hashes retained. No proof term omitted: neZero, And.left, and exact qualified JD application explicitly validated.','producerBuilds':0,'oldAxiomCollections':0,'sameFirstOUnchanged':'22f737f0f7ca3500f3cdf932671546c3dac5d0a043c4f0cff8bd8fb85e6ee40d'}
p=r/'statement-instance-compact-binding.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,ensure_ascii=False))
