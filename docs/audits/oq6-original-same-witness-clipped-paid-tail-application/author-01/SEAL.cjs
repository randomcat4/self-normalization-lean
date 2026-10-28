/* Final local artifact seal. The lastzeroRELEASE write below is FINALWRITE. */
'use strict';
const fs=require('fs');
const path=require('path');
const crypto=require('crypto');
const own='C:/game/shao lean/drafts/oq56/unit247/author-01';
const base='C:/game/shao lean/drafts/oq56/unit247';
const read=p=>fs.readFileSync(p,'utf8');
const sha=b=>crypto.createHash('sha256').update(b).digest('hex');
const bind=p=>({path:p,sha256:sha(fs.readFileSync(p)),bytes:fs.statSync(p).size});
const assert=(x,m)=>{if(!x)throw Error(m);};
const write=(name,o)=>{
  const p=path.resolve(own,name);
  assert(p.startsWith(path.resolve(own)+path.sep),'seal ownership');
  const s=JSON.stringify(o,null,2)+'\n';
  assert(!s.includes('\r'),'seal LF');fs.writeFileSync(p,s,'utf8');
};
assert(!fs.existsSync(own+'/lastzeroRELEASE.json'),'already FINALWRITE sealed');
const activationPath=base+'/implementation-activation-01/ACTIVATION.json';
const activation=JSON.parse(read(activationPath));
assert(bind(activationPath).sha256==='ed955f81f097872adc2c7a5d58f88b9c020fe1ce2221fe2b8731028cf12bb63f','activation hash');
const supplementPath=base+'/lead-nat-order-api-freeze-01/FROZEN-API-SUPPLEMENT.json';
const supplement=JSON.parse(read(supplementPath));
const supplementaryInputs=[bind(supplementPath),supplement.primaryRead,supplement.ambientRead,supplement.completeDeclarations];
assert(supplementaryInputs[0].sha256==='660a22aa20fed39767bab4a1382a86a62d5f866383f252cda2a3a55f0c4d55c6','supplement root');
const inputs=[...activation.inputs,...supplementaryInputs];
assert(activation.inputs.length===55 && supplementaryInputs.length===4 && new Set(inputs.map(x=>x.path)).size===59,'derived input counts');
for(const i of inputs){const b=bind(i.path);assert(b.sha256===i.sha256&&b.bytes===i.bytes,'immutable input '+i.path);}
const release=JSON.parse(read(activation.priorStage1ExclusiveWriterRelease.path));
assert(release.FINALWRITE&&Object.values(release.sixZero).every(x=>x===0),'stage1 release');
const source=bind(own+'/OriginalSameWitnessClippedPaidTailApplication.lean');
assert(source.sha256==='6f64eb0d74346cf03f5eac8832cc39f377b0fb3ac50007200bdf11eefdc4ecaf'&&source.bytes===212204,'final source');
const text=read(source.path);
assert(!text.includes('\r')&&!text.startsWith('\uFEFF')&&text.split('\n').length-1===3093,'source UTF8 LF');
assert(text.startsWith(read(base+'/freeze-02/FROZEN-PREAMBLE.txt')+read(base+'/freeze-02/FROZEN-HEAD.txt')+' := by\n'+
  read(base+'/freeze-02/FROZEN-INITIAL-INTRO.txt')+read(base+'/freeze-03/FROZEN-H246-CALL.txt')),'full frozen prefix');
assert(text.endsWith(read(base+'/freeze-02/FROZEN-CLOSING.txt')),'closing');
const delta=JSON.parse(read(own+'/PROOF-DELTA.json'));
assert(delta.final.sha256===source.sha256&&delta.changedLines.length===2&&delta.reverseOnlyTwoLinesRecoversPriorByteExact,'two-line delta');
const contexts=JSON.parse(read(own+'/ACTUAL-PROP-CONTEXTS.json'));
assert(contexts.source.sha256===source.sha256&&contexts.publicOrdinary.length===141&&
  contexts.optionalOrdinary.length===145&&contexts.optionalOrdinary.filter(x=>x.mirrorUsed).length===58&&
  Object.keys(contexts.proofFactTypeDictionary).length===33&&contexts.instanceInventory.length===6,'actual contexts');
for(const r of contexts.publicOrdinary){assert(r.type&&r.rhs&&r.scope&&r.completeEnclosingParameterContext&&r.sourceDeclaration.startLine>0,'complete public row');
  if(r.mirrorUsed)assert(r.mirrorSourceLine>=678,'mirror coordinates');}
for(const r of Object.values(contexts.proofFactTypeDictionary))assert(r.type&&r.enclosingParameterContext&&r.sourceStartLine>=678,'full actual fact');
const checkpoint=JSON.parse(read(own+'/CHECKPOINT.json'));
checkpoint.status='AUTHOR_COMPLETE_SOURCE_WRITER_RELEASED_FINAL_METADATA_SEAL';
checkpoint.activeWriter=0;checkpoint.sourceWriterReleased=true;checkpoint.administrativeSealInProgress=true;
checkpoint.finalReleaseFile=own+'/lastzeroRELEASE.json';
checkpoint.finalReleasePending=true;checkpoint.source=source;
write('CHECKPOINT.json',checkpoint);
const excluded=new Set(['MANIFEST.json','lastzeroRELEASE.json']);
const payloads=fs.readdirSync(own).filter(n=>!excluded.has(n)).sort().map(n=>bind(own+'/'+n));
for(const b of payloads){const raw=fs.readFileSync(b.path);assert(!(raw[0]===239&&raw[1]===187&&raw[2]===191),'payload BOM');
  assert(!raw.includes(13),'payload CR');}
const usage={input:null,cachedInput:null,output:null,reasoningSubset:null};
const manifest={schema:'oq56-unit247-complete-author-manifest-v1',atUTC:new Date().toISOString(),
  role:activation.role,ownerChat:activation.ownerChat,ownedRoot:own,
  status:'COMPLETE AUTHOR SOURCE; INDEPENDENT SOURCE AND LEAD MACHINE GATES PENDING',
  activation:bind(activationPath),activationInputs:55,supplementInputs:4,
  inputCountDerived:inputs.length,inputs,allInputsVerified:true,
  payloadCountDerived:payloads.length,payloads,allPayloadsVerified:true,
  source,provisional:bind(own+'/PROVISIONAL-SOURCE-831b25e1.txt'),proofDelta:bind(own+'/PROOF-DELTA.json'),
  countsDerived:{publicOrdinary:contexts.publicOrdinary.length,optionalApproved:contexts.optionalOrdinary.length,
    optionalUsed:contexts.optionalOrdinary.filter(x=>x.mirrorUsed).length,optionalUnused:87,
    frozenNamedProps:Object.keys(contexts.proofFactTypeDictionary).length,instances:contexts.instanceInventory.length,
    pureLogicalWholeProducerPackages:contexts.pureLogicalWholeProducerPackages.length,
    retainedUniversalConjuncts:71,retainedPaymentConjuncts:38,newPaidClause:1,newNaturalCutoffs:2},
  fullAllOrdinaryPropInstanceContexts:true,sourceCoordinates:true,publicFreezeExact:true,
  qualifiedImmediateProducer:activation.qualifiedImmediateProducer,qualifiedProducerEvidenceReused:true,
  proofOptionsUnchanged:true,forbiddenSourceTokens:[],
  authorReviewerIndependent:true,independentCompleteSOURCEReviewPending:true,
  qualified:false,kernelChecked:false,axiomAudited:false,
  allActualMathChecksLeadServerOnly:true,LeanCalls:0,serverCalls:0,networkCalls:0,children:0,
  actualBackend:null,actualModel:null,actualEffort:null,requestedModel:'gpt-6.1-sol',requestedEffort:'xhigh',usage,
  modelMetadataBoundary:'Runtime/backend/token counts are not independently exposed to this context; unavailable fields remain null.',
  sourceScope:'Whole qualified246 plus conditional literal512/clipping1 original clipped paid-tail lower minus payment and upper plus3payment. Same witnesses/original envelope/two windows/external input. No external existence/error vanishing/unclipped physical/CDF/atoms/root claim.',
  nextExactDependency:'Fresh independent full SOURCE review; lead first newnative; sameFIRSTO allactualAX/current completeTYPE; qualified final join.',
  terminalRelease:'lastzeroRELEASE.json is the FINALWRITE, binds this manifest and releases this author only.'};
write('MANIFEST.json',manifest);
for(const b of [...inputs,...payloads]){const now=bind(b.path);assert(now.sha256===b.sha256&&now.bytes===b.bytes,'final binding changed');}
const manifestBinding=bind(own+'/MANIFEST.json');
const terminal={schema:'oq56-unit247-author-finalwrite-sixzero-release-v1',atUTC:new Date().toISOString(),
  role:activation.role,ownerChat:activation.ownerChat,ownedRoot:own,
  FINALWRITE:true,status:'AUTHOR_COMPLETE_SEALED_RELEASED_PENDING_INDEPENDENT_AND_SERVER_GATES',
  manifest:manifestBinding,source,payloadCountDerived:payloads.length,inputCountDerived:inputs.length,
  allImmutableInputsAndPayloadsVerified:true,
  sixZeroScope:'This unit247 author role only; no claim about lead/other owners or global server state.',
  sixZero:{writers:0,heavyCommands:0,inflightExecution:0,pendingExternal:0,children:0,uncertainOperations:0},
  writerReleased:true,executionReleased:true,publicationReleased:true,childAuthorityReleased:true,
  noFurtherWritesAfterThisRelease:true,qualified:false,kernelChecked:false,axiomAudited:false,
  independentCompleteSOURCEReviewPending:true,
  twoLineDirectNatOrderProofDelta:bind(own+'/PROOF-DELTA.json'),
  publicFreeze01_02_03Exact:true,newUnfrozenDataAssumptionsInstancesOptions:0,
  actualBackend:null,actualModel:null,actualEffort:null,requestedModel:'gpt-6.1-sol',requestedEffort:'xhigh',usage,
  nextExactDependency:manifest.nextExactDependency};
write('lastzeroRELEASE.json',terminal); // FINALWRITE: no file mutation follows.
console.log(JSON.stringify({source,manifest:manifestBinding,release:bind(own+'/lastzeroRELEASE.json'),
  payloadCountDerived:payloads.length,inputCountDerived:inputs.length,sixZero:terminal.sixZero},null,2));
