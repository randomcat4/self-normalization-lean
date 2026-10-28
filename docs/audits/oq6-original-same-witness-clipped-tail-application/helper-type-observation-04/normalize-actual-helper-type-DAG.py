from pathlib import Path
import json,re,hashlib,importlib.util,os,collections
P={'receipt': {'physical_path': '/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/work/oq56/successor-unit246-01/OriginalSameWitnessClippedTailApplication/helper-type-observation-04/receipt.json', 'sha256': '3cb0116be11fe66657a707d79aeb68770d5f44b87c091daf701b2c2dc1cbd4b0', 'bytes': 24953642, 'mtime_ns': '1793168340255296397'}, 'spec': {'schema': 'oq56-exact-two-helper-structural-DAG-observation-spec-v4-syntax-only', 'atUTC': '2026-10-28T06:18:13.761788+00:00', 'unit': 246, 'ownerChat': '01a17665-2e41-7ed1-9911-57f16fe889fa', 'observerInput': {'path': 'C:/game/shao lean/drafts/oq56/unit246/helper-type-observation-04/ObserveOriginalHelperTypes246DAGFix01.lean', 'sha256': '63daf8ab3ebbbce5294a03cba0675f601dd30cefc8670bf3b74ec2577e1a0529', 'bytes': 4953}, 'directCurrentBaseline': {'physical_path': '/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/work/oq56/successor-unit246-01/OriginalSameWitnessClippedTailApplication/helper-type-observation-03/receipt.json', 'sha256': '133d95135305c2886c9a507d2df7fa7309a66626f4280cb48b9842481604aa07', 'bytes': 24944124, 'mtime_ns': '1793168222655621875'}, 'exactFrozenSource': {'physical_path': '/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/Shao/OQ6/OriginalSameWitnessClippedTailApplication.lean', 'sha256': '2476b169e56b9c3454c21b2aefcfba350d77c25ed3cf5aef908f88cd63cfc263', 'bytes': 212717, 'mtime_ns': '1793166281300994903'}, 'sameFirstOriginalObject': {'physical_path': '/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/.lake/build/lib/lean/Shao/OQ6/OriginalSameWitnessClippedTailApplication.olean', 'sha256': '1575b7a7e40c93ea02504d7467ca653083fc3a6f978615918f44f257bc837a88', 'bytes': 13423272, 'mtime_ns': '1793166355920788380'}, 'targets': ['Shao.OQ6.OriginalSameWitnessClippedTailApplication.actual_original_same_witness_clipped_scalar_tail_application._proof_1_1', 'Shao.OQ6.OriginalSameWitnessClippedTailApplication.actual_original_same_witness_clipped_scalar_tail_application._proof_1_2'], 'scope': 'Import-only observation of exactly two original info.type roots. Exhaustive twelve-Expr-constructor encoder; exact ExprStructMap (Expr.equal includes binder names/annotations), bottom-up ids preserve sharing. Each child id must precede node. No alpha rewriting, delab, reduction or subexpression elision. Full hierarchical names/components/binderInfo/levels/literals/metadata recorded. Depth fuel exhaustion is fatal, no incomplete placeholder accepted. Nonrecursive scalar payload uses derived Repr. Full actual DAG review required; source/O/native/allownerAX/publicTYPE preserved.', 'noSourceProofRecompile': True, 'noPublicTypeReplay': True, 'noAXReplay': True, 'noProducerReplay': True, 'noPublicationDeltaAdoption': True, 'CPU': '52-55', 'nativeLimits': '-M8192 -j4', 'singleHeavyLock': 'work/oq56/HEAVY.lock', 'existingRootV3RunnerUnchanged': True, 'qualified': False, 'finalIndependentReviewer': '/root/oq56_original_clipped_tail246_source_review', 'retainedFailedObserver01': {'path': 'C:/game/shao lean/drafts/oq56/unit246/helper-type-observation-01/complete-observer-failure-projection.json', 'sha256': 'afb1d19914a03aff357c05143e4a741616bf4d84fff6b22f353f3eb63a70c552', 'bytes': 3280}, 'retainedFailedObserver02': {'path': 'C:/game/shao lean/drafts/oq56/unit246/helper-type-observation-02/complete-observer-failure-projection.json', 'sha256': '64582aeed5505df3b0dda8a941a72ca1c0aafa2dc341c0bf46b3b7a0a530f5d2', 'bytes': 3192}, 'priorAllOwnerAXReceipt': {'physical_path': '/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/work/oq56/successor-unit246-01/OriginalSameWitnessClippedTailApplication/owned-object-audit-01/receipt.json', 'sha256': '0b6c1ab7865647df609ad9848cd138061f0fe81a1762196426e200cda21a604b', 'bytes': 24907324, 'mtime_ns': '1793166531740301770'}, 'prospectiveOnlyPendingObserver02NaturalEndAndActualZero': False, 'actualZeroVerified': {'path': 'C:/game/shao lean/drafts/oq56/unit246/helper-type-observation-02/complete-observer-failure-projection.json', 'sha256': '64582aeed5505df3b0dda8a941a72ca1c0aafa2dc341c0bf46b3b7a0a530f5d2', 'bytes': 3192}, 'retainedFailedObserver03': {'path': 'C:/game/shao lean/drafts/oq56/unit246/helper-type-observation-03/complete-observer-failure-projection.json', 'sha256': '841fc03e8d7d08f5bbd3bcb7ed69b4ae4cfec486aeaf8b407d09de64b9c492d3', 'bytes': 3378}, 'syntaxDelta': {'path': 'C:/game/shao lean/drafts/oq56/unit246/helper-type-observation-04/EXACT-PARSER-SYNTAX-DELTA.diff', 'sha256': '468ce6999d37d66e66d2f40bdce95835a3075271696be891d1560ce1bfd81c3d', 'bytes': 495}, 'onlyChange': 'One typed single-line StateT setter replaces offside multi-line record. All twelve constructor/name/binder/level/metadata/traversal logic bytes exact. Original accepted source/O/native/AX/publicTYPE unchanged.'}}
W=Path('/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56');os.chdir(W)
runner=Path('/root/rivermind-data/shao-lean-20261021/tools/current-execution/oq56_lane_bounded_phase39_v3.py')
sp=importlib.util.spec_from_file_location('R',runner);R=importlib.util.module_from_spec(sp);sp.loader.exec_module(R)
rp=Path(P['receipt']['physical_path']);assert R.fp(rp)==P['receipt'];r=json.loads(rp.read_bytes())
assert r['exit_code']==0 and r['all_owned_group_ended'] and r['preservation_equal'] and r['before']==r['after'] and not r['timed_out'] and r['cleanup_events']==[] and r['ownership_issue'] is None and not R.lane_live()
for k in ['exactFrozenSource','sameFirstOriginalObject']:
 p=Path(P['spec'][k]['physical_path']);assert R.fp(p)==P['spec'][k] and r['after']['records'][str(p)]==P['spec'][k]
rawp=Path(r['stdout']['physical_path']);assert R.fp(rawp)==r['stdout'];raw=rawp.read_bytes();text=raw.decode('utf-8');assert not re.search(r': error(?:\([^)]*\))?:',text)
matches=list(re.finditer(r'(?m)^.*?\bOQ56_HELPER_TYPE_DAG_JSON (.+)$',text));assert len(matches)==1
m=matches[0];packetText=m.group(1);j=json.loads(packetText)
assert j['schema']=='exact-ExprStructEq-DAG-v1' and j['helperCount']==2 and [x['name']for x in j['roots']]==P['spec']['targets']
assert len(re.findall(r'(?m)^.*?\bOQ56_HELPER_TYPE_COUNT 2$',text))==1
nodes=j['nodes'];assert len(nodes)==j['nodeCount']
tags=collections.Counter();loose=[];sizes=[];edges=[];safeNats=[]
def namecheck(a):
 assert isinstance(a,list)
 for c in a:
  assert c['kind']in ['str','num'] and set(c)=={'kind','value'}
  if c['kind']=='str':assert isinstance(c['value'],str)
  else:assert type(c['value'])is int and 0<=c['value']<2**53;safeNats.append(c['value'])
def nref(n,k,i):
 v=n[k];assert type(v)is int and 0<=v<i,(i,k,v);return v
for i,n in enumerate(nodes):
 assert n['id']==i;tag=n['tag'];tags[tag]+=1;refs=[];rng=0
 if 'name'in n:namecheck(n['name'])
 for k,v in n.items():
  if k.endswith('Repr')or k.endswith('Reprs'):
   for s in ([v]if isinstance(v,str)else v):assert isinstance(s,str) and all(t not in s for t in ['⋯','<elided>','failed to pretty print','...'])
 if tag=='bvar':rng=n['index']+1
 elif tag in ['fvar','mvar']:raise AssertionError(('openExpr',i,tag))
 elif tag in ['sort','const','lit']:pass
 elif tag=='app':
  refs=[nref(n,'function',i),nref(n,'argument',i)];rng=max(loose[k]for k in refs)
 elif tag in ['lam','forallE']:
  refs=[nref(n,'domain',i),nref(n,'body',i)];rng=max(loose[refs[0]],max(0,loose[refs[1]]-1))
 elif tag=='letE':
  refs=[nref(n,'type',i),nref(n,'value',i),nref(n,'body',i)];assert type(n['nondep'])is bool
  rng=max(loose[refs[0]],loose[refs[1]],max(0,loose[refs[2]]-1))
 elif tag in ['mdata','proj']:refs=[nref(n,'body',i)];rng=loose[refs[0]]
 else:raise AssertionError(('unknownConstructor',i,tag))
 edges.append(refs);loose.append(rng);sizes.append(1+sum(sizes[k]for k in refs))
reachable=set();stack=[x['root']for x in j['roots']]
while stack:
 i=stack.pop()
 if i in reachable:continue
 assert type(i)is int and 0<=i<len(nodes);reachable.add(i);stack.extend(edges[i])
assert len(reachable)==len(nodes)
rootSummaries=[]
for x in j['roots']:
 assert loose[x['root']]==0;namecheck(x['nameComponents'])
 for a in x['levelParams']:namecheck(a)
 trail=[];i=x['root']
 while nodes[i]['tag']=='forallE':
  n=nodes[i];trail.append({'node':i,'name':n['name'],'domain':n['domain'],'binderInfoRepr':n['binderInfoRepr']});i=n['body']
 count=sizes[x['root']]
 rootSummaries.append({'name':x['name'],'root':x['root'],'leadingForallBinders':trail,'bodyAfterLeadingForalls':i,'rootLooseBVarRange':0,'expandedExprNodeCountDecimal':str(count)if count.bit_length()<1024 else None,'expandedExprNodeCountBitLength':count.bit_length()})
U=rp.parent.parent;N=U/'helper-type-evidence-04';assert not N.exists();N.mkdir()
p=N/'full-helper-types.dag.json';p.write_bytes((packetText+'\n').encode());files={p.name:R.fp(p)}
summary={k:r.get(k)for k in ['exit_code','success','seconds','all_owned_group_ended','preservation_equal','timed_out','cleanup_events','ownership_issue','object_before','object_after','input','config','stdout','stderr']}
summary.update(schema='oq56-complete-two-helper-same-FIRSTO-DAG-observation-v1',receipt=R.fp(rp),beforeAfterExact=True,protectedRecordsDerived=len(r['after']['records']),source=P['spec']['exactFrozenSource'],firstOriginalObject=P['spec']['sameFirstOriginalObject'],ownLiveAfter=[],actualHelperCountDerived=2,uniqueExpressionNodeCountDerived=len(nodes),constructorCountsDerived=dict(tags),roots=rootSummaries,allEdgesBackwardAndEveryNodeReachable=True,allRootBVarsClosed=True,nameComponentNumericMax=max(safeNats,default=0),rawPacketByteStart=len(text[:m.start(1)].encode()),rawPacketByteLength=len(packetText.encode()),rawPacketSHA256=hashlib.sha256(packetText.encode()).hexdigest(),allScalarReprNoElisionMarker=True,noSourceProofRecompile=True,noAXReplay=True,noPublicTYPEReplay=True,priorAllOwnerAXReceipt=P['spec']['priorAllOwnerAXReceipt'],originalFailedTYPEPlaceholdersRetained=True,qualified=False)
p=N/'observation-summary.json';p.write_bytes((json.dumps(summary,ensure_ascii=False,indent=2)+'\n').encode());files[p.name]=R.fp(p)
print(json.dumps({'summary':summary,'normalizedSemanticFiles':files},ensure_ascii=False))
