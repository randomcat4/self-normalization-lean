from pathlib import Path
import json,hashlib,datetime

HERE=Path('C:/game/shao lean/drafts/c12-lane/source-machine-batch-223227228-v1/review001')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
def dump(name,obj):
    (HERE/name).write_text(json.dumps(obj,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
def binding(p):
    p=Path(p);b=p.read_bytes()
    return {'path':p.as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def get(name): return json.loads((HERE/name).read_text(encoding='utf-8'))

checked=get('DETERMINISTIC-CHECK.json')
inputs=get('INPUT-SEAL.json')
assert checked['status']=='PASS' and checked['bindingOccurrences']==len(inputs['bindings'])==348
for row in inputs['bindings']:
    actual=binding(row['path'])
    assert actual['bytes']==row['bytes'] and actual['sha256']==row['sha256']
for row in inputs['readInputs']:
    actual=binding(row['path'])
    assert actual['bytes']==row['bytes'] and actual['sha256']==row['sha256']
config={'configuredModel':'gpt-6.1-sol','configuredEffort':'xhigh','freshContext':True,'actualModel':None,'actualEffort':None,'usage':{'inputTokens':None,'cachedInputTokens':None,'outputTokens':None,'reasoningSubsetTokens':None}}
zero={k:0 for k in ['reviewer','artifactWriter','sourceWriters','heavy','inflight','pendingExternal','children','Lean','AX','server','network','upload','GitAPI','persistentOwnedProcesses','queuedCommands','pendingWrites']}
common={'C2':'OPEN','C12':'OPEN','fullRootOD':'OPEN','OQ3':'PAUSED_BY_USER'}

seg={
223:[(1,11,'冻结前导'),(12,36,'完整冻结head与十二输出'),(37,46,'同一nu/rho的b与规模重参数'),(47,52,'真实标准化map函数外延'),(53,60,'受影响Nat.cast_zero侧条件及真实矩接口'),(61,73,'rho支持/可积与真实方差正性/界'),(74,81,'自己的R三阶账与n正性'),(82,91,'非零保留均值界'),(92,103,'实际map的ae支持'),(104,110,'实际积分map与三次尺度'),(111,121,'nC付款及非负性'),(122,134,'s/sigma正性与立方下界'),(135,149,'分母恒等式及合法ratio'),(150,161,'十二字段与64R/a³最终账'),(162,163,'分隔/命名空间结束')],
227:[(1,12,'精确冻结前导'),(13,15,'第一完整冻结head及旧语义覆盖'),(16,26,'第一完整受影响证明精确复用旧独审'),(27,27,'分隔'),(28,41,'第二完整冻结head及旧语义覆盖'),(42,97,'第二完整证明精确复用更早独审'),(98,99,'分隔/命名空间结束')],
228:[(1,12,'冻结前导/导入'),(13,17,'第一完整冻结head'),(18,23,'delta与邻域预算'),(24,35,'闭区间每点非负与距离预算'),(36,43,'区间内线性界'),(44,61,'真实localcomparison/Mills/导数范数统一界'),(62,73,'凸区间MVT及常数2exp2'),(74,74,'分隔'),(75,84,'第二完整冻结head/真实双事件'),(85,96,'两正阈值完整producer第五字段'),(97,101,'上下独立见证的D嵌套'),(102,108,'H嵌套/有限实测度/两差界'),(109,109,'分隔'),(110,120,'第三完整冻结head/正性与邻域'),(121,123,'局部tail比较与高斯差'),(124,133,'x≤t绝对差付款'),(134,140,'t≤x绝对差付款'),(141,147,'最终4×2exp2及尾比较'),(148,149,'分隔/命名空间结束')]
}
unitRecords=[]
for unit in (223,227,228):
    u=checked['units'][str(unit)]
    mode='EXACT_QUALIFIED_COMPLETE_SOURCE_PROOF_REUSE_PLUS_NEW_COMPLETE_MACHINE_SUPPLEMENT' if unit==227 else 'NEW_COMPLETE_INDEPENDENT_SOURCE_TO_STATEMENT_WHOLE_PROOF_REVIEW'
    u['segments']=[{'lines':[lo,hi],'subject':subject,'mode':mode,'reviewed':True} for lo,hi,subject in seg[unit]]
    observed=[i for lo,hi,_ in seg[unit] for i in range(lo,hi+1)]
    assert observed==list(range(1,u['sourceLines']+1))
    u['allSourceLinesCoveredExactlyOnce']=True
    u['completeSourceRead']=True
    u['sourceOnly']=unit!=227
    u['formalQualified']=unit==227
    u['status']='CORRECT_FORMALLY_QUALIFIED_EXACT_SOURCE' if unit==227 else 'CORRECT_SOURCE_ONLY'
    u['criticalGaps']=[]
    u['newWholeProofReviewCount']=0 if unit==227 else (1 if unit==223 else 3)
    if unit==227:
        u['qualifiedCompleteSourceProofReview']=binding('C:/game/shao lean/drafts/c12-lane/native-repairs-223227-v1/review001/REPORT.md')
        u['qualifiedCompleteSourceProofCoverage']=binding('C:/game/shao lean/drafts/c12-lane/native-repairs-223227-v1/review001/COVERAGE.json')
        u['earlierSecondWholeProofReview']=binding('C:/game/shao lean/drafts/c12-lane/qualified-machine-and-source-batch-223226227-v1/review001/REPORT.md')
        u['allActualOwnedTypesReviewed']=True
        u['allActualNonTheoremValuesReviewedEmptySet']=True
        u['recursiveAXAllActualOwners']='PASS'
        u['actualTYPELinesCoveredExactlyOnce']=[1,178]
    unitRecords.append(u)
coverage={'atUTC':now,'role':'c12_source_machine_batch_223227228_review001','status':'CORRECT','scope':'223source005/227source002finalmachine/228source001SOURCE','proofHashConvention':'by LF + complete indented body through final proof line LF; no separator','units':unitRecords,'newCompleteIndependentWholeProofReviews':4,'exactUnchangedWholeProofReuses227':2,'oldProducerWholeProofReaudits':0,'allFrozenHeadsAndPreamblesByteExact':True,'allSourceChangesCovered':True,'mandatoryBindings':39,'extendedBindingOccurrences':348,'uniqueReadPaths':160,'criticalGaps':[],**config,**common}
dump('COVERAGE.json',coverage)
verdict={'atUTC':now,'status':'CORRECT','units':[{'unit':u['unit'],'source':u['source'],'status':u['status'],'sourceOnly':u['sourceOnly'],'formalQualified':u['formalQualified'],'criticalGaps':[]} for u in unitRecords],'noRootClosure':True,'authorReviewerSeparated':True,'sourceWrites':0,'newLeanAXServerNetworkUploadsGitAPI':0,'actualReviewerActivity':zero,'nextDependencies':{'223':'Exactsource005 firstnative and sameoriginalO allactualTYPE/nonthmVALUE/recursiveAX aftersuccess','227':'Exactqualified module may enter authorized publication/intake','228':'Exactsource001 firstnative and sameoriginalO allactualTYPE/nonthmVALUE/recursiveAX aftersuccess'},**config,**common}
dump('VERDICT.json',verdict)
dump('CHECKER-REPAIRS.json',{'atUTC':now,'scope':'Only local metadata checking code/diagnostic reads; no source/oldreceipt/Lean/AX/server effects','attempts':[{'attempt':1,'result':'KeyError payloads','cause':'Earlier immutable PAYLOAD-SEAL uses files, while recent schema uses payloads','repair':'Read exact existing files field; no input modification'},{'attempt':2,'result':'Original-excerpt raw-string equality assertion','cause':'Immutable original excerpt has CRLF6, main line comparison removes line endings','repair':'Preserve bytes; compare all six exact text lines with splitlines and record CR6'},{'attempt':'diagnostic-read','result':'PowerShell ParserError empty pipe element','cause':'Diagnostic loop statement piped without array expression','repair':'Read via array expression; no files written'},{'attempt':3,'result':'PASS','mandatoryBindings':39,'bindingOccurrences':348,'uniqueReadPaths':160}],'mathematicalVerdictUnaffected':True,'allInputBytesPreserved':True})
dump('CHECKPOINT.json',{'atUTC':now,'state':'COMPLETE_REVIEW_FINAL_SEAL_READY','scope':'Only this review001, activation/source/oldreview/library/coordination read-only','units':{str(u['unit']):{'sourceSHA256':u['source']['sha256'],'status':u['status'],'formalQualified':u['formalQualified']} for u in unitRecords},'allMandatoryAndExtendedBindingsReverifiedAtCompletion':True,'heavy':0,'inflight':0,'pendingExternal':0,'children':0,'queuedCommands':0,'nextDependency':'Parent consumes exact per-unit verdict; no reviewer execution dispatched','writerAuthorityAfterSeal':'RELEASED',**config,**common})
payload=[]
for p in sorted(HERE.iterdir()):
    if p.is_file() and p.name not in {'parent-activation001.json','PAYLOAD-SEAL.json','RELEASE.json'}:
        b=p.read_bytes();b.decode('utf-8');assert not b.startswith(b'\xef\xbb\xbf') and b'\r' not in b
        payload.append(binding(p))
dump('PAYLOAD-SEAL.json',{'atUTC':now,'status':'EXACT_REVIEW_PAYLOAD_SEALED','payloadCount':len(payload),'payloads':payload,'allPayloadsUTF8NoBOMLF':True,'activationSourceOldReviewLibraryCoordinationReadOnly':True,'selfAndReleaseExcludedForAcyclicSeal':True,'units':{str(u['unit']):u['status'] for u in unitRecords},**config,**common})
release={'atUTC':now,'status':'NATURAL_COMPLETE_REVIEW_ALL_ZERO_RELEASE','directory':HERE.as_posix(),'scope':'This independent reviewer only; no claim of global current server state','sourceOwnership':'NONE_EVER','allReviewWriterExecutionChildAuthorityReleased':True,**zero,'payloadSeal':binding(HERE/'PAYLOAD-SEAL.json'),'units':{str(u['unit']):{'status':u['status'],'formalQualified':u['formalQualified']} for u in unitRecords},**config,**common}
dump('RELEASE.json',release)
for row in get('PAYLOAD-SEAL.json')['payloads']:
    assert binding(row['path'])==row
assert binding(HERE/'PAYLOAD-SEAL.json')==get('RELEASE.json')['payloadSeal']
print(json.dumps({'status':'SEALED_RELEASED','payloads':len(payload),'verdict':{str(u['unit']):u['status'] for u in unitRecords},'REPORT':binding(HERE/'REPORT.md'),'COVERAGE':binding(HERE/'COVERAGE.json'),'PAYLOAD':binding(HERE/'PAYLOAD-SEAL.json'),'RELEASE':binding(HERE/'RELEASE.json')},ensure_ascii=False))
