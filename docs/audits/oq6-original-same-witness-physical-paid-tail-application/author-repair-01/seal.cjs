const fs=require('fs');
const path=require('path');
const crypto=require('crypto');
const root=__dirname;
const work='C:/game/shao lean';
const hash=b=>crypto.createHash('sha256').update(b).digest('hex');
const bind=p=>{const b=fs.readFileSync(p);return{path:p.replaceAll('\\','/'),sha256:hash(b),bytes:b.length};};
const get=p=>JSON.parse(fs.readFileSync(p,'utf8'));
const write=(p,j)=>fs.writeFileSync(p,JSON.stringify(j,null,2)+'\n','utf8');
if(fs.existsSync(path.join(root,'lastzeroRELEASE.json')))throw Error('Already released; no further writes');
const ap=path.join(work,'drafts/oq56/unit248/repair-activation-01/ACTIVATION.json');
const a=get(ap);
for(const x of a.inputs){const b=bind(x.path);if(b.sha256!==x.sha256||b.bytes!==x.bytes)throw Error('Input changed '+x.path);}
const source=bind(path.join(root,'OriginalSameWitnessPhysicalPaidTailApplication.lean'));
if(source.sha256!==a.expectedExactThreeDeltaSource.sha256||source.bytes!==a.expectedExactThreeDeltaSource.bytes)throw Error('Source expectation differs');
const expected=['FIRSTWRITE-RUNTIME-ACK.json','OriginalSameWitnessPhysicalPaidTailApplication.lean','PATCH.json',
  'ACTUAL-PROP-CONTEXTS.json','REPORT.md','LOCAL-VALIDATION.json','DIAGNOSTIC-READ.json','CHECKPOINT.json',
  'LOCAL-TOOLING-HISTORY.json','repair.cjs','seal.cjs'];
const actual=fs.readdirSync(root).filter(n=>fs.statSync(path.join(root,n)).isFile());
if(actual.length!==expected.length||actual.some(n=>!expected.includes(n)))throw Error('Owned payload inventory differs');
const payloads=expected.map(n=>bind(path.join(root,n)));
const model={requestedModel:'gpt-6.1-sol',requestedEffort:'xhigh',actualBackend:null,actualModel:null,actualEffort:null,
  usage:{input:null,cachedInput:null,output:null,reasoningSubset:null}};
const operations={Lean:0,lake:0,kernel:0,PP:0,AX:0,server:0,network:0,upload:0,Git:0,API:0,children:0};
const next='SAME independent reviewer affected review of both full typed fragments and section closure, joined to unchanged complete prior SOURCE coverage; then lead-only native02. P168 never readopted.';
const manifest={schema:'oq56-unit248-SAMEauthor-exact3delta-repair-manifest-v1',atUTC:new Date().toISOString(),
  role:a.role,ownerChat:a.ownerChat,ownedRoot:root.replaceAll('\\','/'),activation:bind(ap),freeze:a.newFreeze02,
  priorAuthorFINALWRITE:a.priorAuthorFINALWRITE,inputs:a.inputs,inputCountDerived:a.inputs.length,
  source,sourceLF:a.expectedExactThreeDeltaSource.LF,payloads,payloadCountDerived:payloads.length,
  onlyThreeFrozenDeltas:true,oldAuthorAndReviewImmutable:true,allOtherProofBytesExact:true,all6DiagnosticsReadComplete:true,
  noAllCascadesOrKernelSuccessClaim:true,sourceComplete:true,sourceAccepted:false,independent:false,qualified:false,kernelPending:true,
  selfBinding:'Final release binds this manifest; neither manifest nor release is self-hashed.',
  nextExactDependency:next,operations,...model};
const mp=path.join(root,'MANIFEST.json');
write(mp,manifest);
const release={schema:'oq56-unit248-SAMEauthor-exact3delta-FINALWRITE-sixzero-release-v1',atUTC:new Date().toISOString(),
  role:a.role,ownerChat:a.ownerChat,ownedRoot:root.replaceAll('\\','/'),FINALWRITE:true,
  status:'EXACT_THREE_DELTA_SOURCE_AND_AFFECTED_CONTEXTS_SEALED_RELEASED_KERNEL_PENDING',
  manifest:bind(mp),source,sourceLF:a.expectedExactThreeDeltaSource.LF,inputCountDerived:a.inputs.length,payloadCountDerived:payloads.length,
  allInputsAndPayloadsHashBound:true,onlyThreeFrozenDeltas:true,oldAuthorAndReviewImmutable:true,
  writerReleased:true,executionReleased:true,publicationReleased:true,childAuthorityReleased:true,
  sixZero:{writers:0,heavyCommands:0,inflightExecution:0,pendingExternal:0,children:0,uncertainOperations:0},
  sixZeroScope:'This SAME original author repair role only; no server or lead/reviewer global process claim.',
  noFurtherWritesAfterThisRelease:true,sourceComplete:true,sourceAccepted:false,independent:false,qualified:false,kernelPending:true,
  kernelChecked:false,axiomAudited:false,P168AlreadyAdoptedNeverReadopt:true,nextExactDependency:next,operations,...model};
const rp=path.join(root,'lastzeroRELEASE.json');
write(rp,release);
// All work below is read-only after the final release write.
console.log(JSON.stringify({source,sourceLF:release.sourceLF,manifest:bind(mp),release:bind(rp),payloadCount:payloads.length,sixZero:release.sixZero}));
