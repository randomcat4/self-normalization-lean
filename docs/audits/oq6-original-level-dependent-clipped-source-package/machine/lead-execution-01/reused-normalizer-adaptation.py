from pathlib import Path
import json,hashlib,re,os,importlib.util
from collections import Counter
W=Path('/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56');os.chdir(W);T=W/'work/oq56/successor-unit251-01/OriginalLevelDependentClippedSourcePackage'
spec=importlib.util.spec_from_file_location('R',Path('/root/rivermind-data/shao-lean-20261021/tools/current-execution/oq56_lane_bounded_phase39_v3.py'));R=importlib.util.module_from_spec(spec);spec.loader.exec_module(R)
nr=T/'author-kernel-01/receipt.json';ar=T/'owned-object-audit-01/receipt.json'
assert R.fp(nr)['sha256']=='c3d719b75c64fd4deaf98fe9a970f06533c0153d7507ece4cac5c90b664be5fc'
assert R.fp(ar)['sha256']=='15ff8e5a5c4d5f8a5a967200dff44f75da40676b616bfe3d6e999f6849aba37e'
n=json.loads(nr.read_bytes());a=json.loads(ar.read_bytes())
for r in [n,a]:
 assert r['exit_code']==0 and r['all_owned_group_ended'] and r['before']==r['after'] and r['preservation_equal']
assert not R.lane_live() and all(not r['timed_out'] and r['cleanup_events']==[] and r['ownership_issue'] is None for r in [n,a])
for path,e in a['after']['records'].items():
 st=Path(path).stat();assert st.st_size==e['bytes']and str(st.st_mtime_ns)==e['mtime_ns'],path
S=W/'Shao/OQ6/OriginalLevelDependentClippedSourcePackage.lean';O=W/'.lake/build/lib/lean/Shao/OQ6/OriginalLevelDependentClippedSourcePackage.olean';sf=R.fp(S);of=R.fp(O)
assert sf['sha256']=='ab6f36156e138a4616fa769bd7ad123b3cd0adf92be79414e6ab226598291e53' and of==n['object_after'] and of==a['before']['records'][str(O)]==a['after']['records'][str(O)]
rawp=T/'owned-object-audit-01/owned-object-audit-01.stdout';raw=rawp.read_bytes();text=raw.decode('utf-8')
pat=re.compile(r'(?m)^OQ56_OWNED_(JSON|TYPE|VALUE|COUNT) ');ms=list(pat.finditer(text));assert ms and ms[0].start()==0
entries=[];countline=None;rebuilt=[]
for i,m in enumerate(ms):
 payload=text[m.end():ms[i+1].start() if i+1<len(ms) else len(text)]
 tag=m.group(1);rebuilt.append('OQ56_OWNED_'+tag+' '+payload)
 if tag=='JSON':
  assert payload.endswith('\n') and len(payload.splitlines())==1
  e=json.loads(payload);e['rawOwnedJSON']=payload[:-1];entries.append(e)
 elif tag=='TYPE':
  e=entries[-1];prefix=e['name']+' : ';assert payload.startswith(prefix) and 'type' not in e;e['type']=payload[len(prefix):];e['typeLines']=len(e['type'].splitlines())
 elif tag=='VALUE':
  e=entries[-1];prefix=e['name']+' := ';assert payload.startswith(prefix) and 'value' not in e;e['value']=payload[len(prefix):];e['valueLines']=len(e['value'].splitlines())
 else:
  assert i==len(ms)-1 and countline is None;count=int(payload.strip());countline='OQ56_OWNED_COUNT '+payload
assert ''.join(rebuilt).encode()==raw and count==len(entries)==len({e['name'] for e in entries})
allowed={'propext','Classical.choice','Quot.sound'}
for e in entries:
 assert '.'.join(c['value'] for c in e['components'])==e['name'] and all(c['kind'] in ['str','num'] for c in e['components'])
 assert e['bodyExpressionPresent'] and e['constantKind'] in ['thmInfo','defnInfo','opaqueInfo'] and e['isTheorem']==(e['constantKind']=='thmInfo') and set(e['axioms'])<=allowed
 assert e['type'].endswith('\n') and all(x not in e['type'] for x in ['⋯','...','<elided>'])
 assert all(x not in e['type'].lower() for x in ['failed to pretty print','exceeded maximum recursion depth','maximum number of heartbeats']),e['name']
 if not e['isTheorem']:assert 'value' in e and e['value'].endswith('\n') and all(x not in e['value'] for x in ['⋯','...','<elided>']) and all(x not in e['value'].lower() for x in ['failed to pretty print','exceeded maximum recursion depth','maximum number of heartbeats'])
 else:assert 'value' not in e
ax=dict(Counter(x for e in entries for x in e['axioms']));nt=sum(not e['isTheorem'] for e in entries);tl=sum(e['typeLines'] for e in entries);vl=sum(e.get('valueLines',0) for e in entries)
public=len(re.findall(r'(?m)^theorem\s+',S.read_text()));assert public==1
assert not re.findall(r'(?m)^(?:noncomputable\s+)?(?:def|abbrev|opaque|instance|axiom)\s+',S.read_text())
D=T/'owner-evidence-01';D.mkdir(exist_ok=False)
def save(p,j):
 with p.open('xb') as h:h.write((json.dumps(j,ensure_ascii=False,indent=2)+'\n').encode())
metadata={'schema':'oq56-complete-actual-owned-metadata-v2','module':'Shao.OQ6.OriginalLevelDependentClippedSourcePackage','anchor':'Shao.OQ6.OriginalLevelDependentClippedSourcePackage.actual_original_level_dependent_clipped_source_package','source':sf,'object':of,'auditReceipt':R.fp(ar),'ownerDiscovery':'actual env.getModuleIdxFor? anchor then ALL env.constants without namespace filter','actualOwnerCount':count,'allTheoremCount':count-nt,'nonTheoremCount':nt,'nonTheoremFullValueCount':nt,'sourceDeclaredCount':public,'publicSourceTheoremCount':public,'entries':entries,'rawOwnedCountLine':countline,'rawStdoutBytes':len(raw),'rawStdoutSHA256':hashlib.sha256(raw).hexdigest(),'exactRawStdoutReconstructedFromOnlyJSONTypeValueCountBlocks':True,'allRecursiveAxiomsWhitelisted':True,'allTYPEAndNonTheoremFULLVALUEEmitted':True,'noElisionMarkers':True,'qualified':False}
mp=D/'actual-owned-metadata.json';save(mp,metadata)
dg={'completeDiagnosticText':Path(n['stdout']['physical_path']).read_text(encoding='utf8')}
def compact(label,r,rp):
 q=T/label
 return {'actualExitCode':r['exit_code'],'seconds':r['seconds'],'receipt':R.fp(rp),'config':R.fp(T/(label+'-config.json')),'stdout':R.fp(q/(label+'.stdout')),'stderr':R.fp(q/(label+'.stderr')),'strictWrapperSuccess':r['success'],'beforeAfterExact':r['before']==r['after'],'protectedDerived':len(r['before']['records'])}
nc=compact('author-kernel-01',n,nr);nc['config']=R.fp(T/'author-kernel-01-config.json');nc.update({'FIRSTEMPTY':None,'FIRSTEMPTYIsReturnedRunnerField':False,'requireEmptyStdout':n['require_empty_stdout'],'sourceErrors':len(re.findall(r': error(?:\([^)]*\))?:',dg['completeDiagnosticText'])),'sourceWarnings':len(re.findall(r': warning(?:\([^)]*\))?:',dg['completeDiagnosticText']))})
ac=compact('owned-object-audit-01',a,ar);ac.update({'no_o':True,'own_object_import':True})
summary={'schema':'oq56-unit251-native-originalO-all-owned-summary-v1','source':sf,'object':of,'native01':nc,'ownedAudit01':ac,'actualOwned':count,'actualTheorems':count-nt,'actualNonTheorems':nt,'TYPElines':tl,'VALUElines':vl,'axiomOccurrences':ax,'allOwnedProcessesEnded':True,'ownLean':[],'oldProducerRechecks':0,'rawLogsRemainServer':True,'correctNativeUnit':251,'actualNativeAttempt':1,'sourceVersion':'first-success-native01-280LF','executionPhase':'ROOT_OQ56_OQ3_40','qualified':False}
sp=D/'native-kernel-and-all-owner-audit-summary.json';save(sp,summary)
binding={'schema':'oq56-unit251-normalized-originalO-metadata-server-binding-v1','utc':R.now(),'source':sf,'object':of,'nativeReceipt':R.fp(nr),'auditReceipt':R.fp(ar),'metadata':R.fp(mp),'summary':R.fp(sp),'sourceRunEndedReceipt':R.fp(T/'author-kernel-01/RUN-ENDED.json'),'rawStdoutSHA256':hashlib.sha256(raw).hexdigest(),'rawStdoutBytes':len(raw),'allCountsDerivedFromActualModuleIndex':True,'rawLogsObjectsCachesNotTransferred':True,'allOwnedEnded':True,'ownLean':[],'qualified':False}
bp=D/'server-metadata-binding.json';save(bp,binding)
tp=D/'actual-owned-types.txt';tp.open('xb').write(''.join(e['name']+' : '+e['type'] for e in entries).encode())
vp=D/'actual-owned-values.txt';vp.open('xb').write(''.join(e['name']+' := '+e['value'] for e in entries if 'value'in e).encode())
print(json.dumps({'types':R.fp(tp),'values':R.fp(vp),'metadata':R.fp(mp),'summary':R.fp(sp),'binding':R.fp(bp),'actualOwned':count,'theorems':count-nt,'nonTheorems':nt,'TYPElines':tl,'VALUElines':vl,'axiomOccurrences':ax,'nativeActual0':True,'auditActual0':True,'nativeWarnings':len(re.findall(r': warning(?:\([^)]*\))?:',dg['completeDiagnosticText'])),'protected':[len(n['before']['records']),len(a['before']['records'])],'ownLean':[]}))

blocks=[x for x in re.split(r'(?m)(?=^Shao/OQ6/OriginalLevelDependentClippedSourcePackage[.]lean:\d+:\d+:)',dg['completeDiagnosticText']) if ': warning' in x]
warnings=[]
for x in blocks:
 first=x.splitlines()[0]
 category='unused' if 'is not explicitly referenced.' in first else ('style' if 'Try this:' in x else ('deprecation' if 'deprecated' in x else 'context-or-other'))
 warnings.append({'location':first.split(': warning',1)[0],'category':category,'headline':first.split(': warning',1)[1].strip(),'completeMessageUTF8SHA256':hashlib.sha256(x.encode()).hexdigest(),'completeMessageBytes':len(x.encode())})
assert len(warnings)==nc['sourceWarnings']
print(json.dumps({'schema':'oq56-unit251-native01-warning-classification-v1','source':sf,'nativeReceipt':R.fp(nr),'sourceErrors':nc['sourceErrors'],'sourceWarnings':len(warnings),'categories':dict(Counter(x['category'] for x in warnings)),'warnings':warnings,'allOriginalMessagesRemainServer':True,'strictWrapperSuccess':n['success'],'actualNativeRC':n['exit_code'],'actualAuditRC':a['exit_code'],'auditStrictWrapperSuccess':a['success']}))

