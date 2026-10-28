// Run only once after the local author work is complete. The release is the
// last filesystem write made by this role; subsequent verification is read-only.
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const root = __dirname;
const work = 'C:/game/shao lean';
const hash = b => crypto.createHash('sha256').update(b).digest('hex');
const bind = p => {const b=fs.readFileSync(p);return {path:p.replaceAll('\\','/'),sha256:hash(b),bytes:b.length};};
const get = p => JSON.parse(fs.readFileSync(p,'utf8'));
const write = (p,j) => fs.writeFileSync(p,JSON.stringify(j,null,2)+'\n','utf8');
if(fs.existsSync(path.join(root,'lastzeroRELEASE.json')))throw Error('Already released: no later write allowed');
const ap=path.join(work,'drafts/oq56/unit248/implementation-activation-01/ACTIVATION.json');
const a=get(ap);
for(const x of a.inputs){const b=bind(x.path);if(b.sha256!==x.sha256||b.bytes!==x.bytes)throw Error('Input changed: '+x.path);}
const source=bind(path.join(root,'OriginalSameWitnessPhysicalPaidTailApplication.lean'));
for(const name of ['ACTUAL-PROP-CONTEXTS.json','COMPATIBILITY.json','CHECKPOINT.json','LOCAL-VALIDATION.json']){
  const j=get(path.join(root,name));if(j.source.sha256!==source.sha256||j.source.bytes!==source.bytes)throw Error('Stale source binding '+name);
}
const expected=['FIRSTWRITE-RUNTIME-ACK.json','RESUMPTION-RUNTIME-ACK-01.json','OriginalSameWitnessPhysicalPaidTailApplication.lean',
  'ACTUAL-PROP-CONTEXTS.json','COMPATIBILITY.json','REPORT.md','CHECKPOINT.json','TYPE247-RESTORATION.json',
  'LOCAL-VALIDATION.json','LOCAL-TOOLING-HISTORY.json','build-source.cjs','write-evidence.cjs','seal.cjs'];
const actual=fs.readdirSync(root).filter(n=>fs.statSync(path.join(root,n)).isFile());
if(actual.length!==expected.length||actual.some(n=>!expected.includes(n)))throw Error('Unexpected owned payload before sealing');
const payloads=expected.map(n=>bind(path.join(root,n)));
const model={requestedModel:'gpt-6.1-sol',requestedEffort:'xhigh',actualBackend:null,actualModel:null,actualEffort:null,
  usage:{input:null,cachedInput:null,output:null,reasoningSubset:null}};
const manifest={
  schema:'oq56-unit248-complete-author-source-and-evidence-manifest-v1',atUTC:new Date().toISOString(),
  role:a.role,ownerChat:a.ownerChat,ownedRoot:root.replaceAll('\\','/'),activation:bind(ap),
  exactFreeze:a.exactFreeze,qualified247:a.qualifiedImmediateProducer,inputs:a.inputs,inputCountDerived:a.inputs.length,
  source,payloads,payloadCountDerived:payloads.length,
  selfBinding:'The final release binds this manifest; neither manifest nor release is self-hashed.',
  sourceComplete:true,independent:false,sourceAccepted:false,qualified:false,kernelPending:true,
  noActualMathematicalExecution:true,noFurtherProofWrites:true,
  nextExactDependency:'Lead exact-source intake and fresh independent complete review; designated-server native and sameFIRSTO allactualTYPE/requiredVALUE/transitiveAX later.',
  ...model
};
const mp=path.join(root,'MANIFEST.json');
write(mp,manifest);
const release={
  schema:'oq56-unit248-complete-author-FINALWRITE-sixzero-release-v1',atUTC:new Date().toISOString(),
  role:a.role,ownerChat:a.ownerChat,ownedRoot:root.replaceAll('\\','/'),FINALWRITE:true,
  status:'COMPLETE_SOURCE_AND_EVIDENCE_SEALED_RELEASED_KERNEL_PENDING',manifest:bind(mp),source,
  payloadCountDerived:payloads.length,inputCountDerived:a.inputs.length,allInputsAndPayloadsHashBound:true,
  writerReleased:true,executionReleased:true,publicationReleased:true,childAuthorityReleased:true,
  sixZero:{writers:0,heavyCommands:0,inflightExecution:0,pendingExternal:0,children:0,uncertainOperations:0},
  sixZeroScope:'This author role only; no global lead, reviewer or server process claim.',
  noFurtherWritesAfterThisRelease:true,sourceComplete:true,independent:false,sourceAccepted:false,
  qualified:false,kernelPending:true,kernelChecked:false,axiomAudited:false,
  operations:{Lean:0,lake:0,kernel:0,PP:0,AX:0,server:0,network:0,upload:0,Git:0,API:0,children:0},
  nextExactDependency:manifest.nextExactDependency,...model
};
const rp=path.join(root,'lastzeroRELEASE.json');
write(rp,release);
// Read-only result after the last write.
console.log(JSON.stringify({status:release.status,source,manifest:bind(mp),release:bind(rp),payloads:payloads.length,sixZero:release.sixZero}));
