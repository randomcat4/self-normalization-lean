const fs=require('fs');
const path=require('path');
const crypto=require('crypto');
const root=__dirname;
const work='C:/game/shao lean';
const oldRoot=path.join(work,'drafts/oq56/unit248/author-01');
const freezeRoot=path.join(work,'drafts/oq56/unit248/freeze-02');
const read=p=>fs.readFileSync(p,'utf8');
const json=p=>JSON.parse(read(p));
const sha=b=>crypto.createHash('sha256').update(b).digest('hex');
const bind=p=>{const b=fs.readFileSync(p);return{path:p.replaceAll('\\','/'),sha256:sha(b),bytes:b.length};};
const put=(n,j)=>fs.writeFileSync(path.join(root,n),JSON.stringify(j,null,2)+'\n','utf8');
if(fs.existsSync(path.join(root,'lastzeroRELEASE.json')))throw Error('Released directory is immutable');
const ap=path.join(work,'drafts/oq56/unit248/repair-activation-01/ACTIVATION.json');
const activation=json(ap);
const freeze=json(path.join(freezeRoot,'frozen-declaration.json'));
const inv=json(path.join(freezeRoot,'INTERFACE-INVENTORY.json'));
for(const x of activation.inputs){const b=bind(x.path);if(b.sha256!==x.sha256||b.bytes!==x.bytes)throw Error('Input changed '+x.path);}
const oldRelease=json(path.join(oldRoot,'lastzeroRELEASE.json'));
if(!oldRelease.FINALWRITE||Object.values(oldRelease.sixZero).some(x=>x!==0))throw Error('Old writer release invalid');
const oldPath=path.join(oldRoot,'OriginalSameWitnessPhysicalPaidTailApplication.lean');
const old=read(oldPath);
const oldBinding=bind(oldPath);
let current=old;
const changes=[];
const apply=(name,before,after,min,max)=>{
  const pos=current.indexOf(before,min);
  if(pos<0||pos>=max||current.indexOf(before,pos+before.length)>=0&&current.indexOf(before,pos+before.length)<max)throw Error('Ambiguous scoped delta '+name);
  const originalPos=pos-changes.reduce((sum,d)=>sum+d.after.length-d.before.length,0);
  if(old.slice(originalPos,originalPos+before.length)!==before)throw Error('Original scoped block missing');
  changes.push({name,before,after,oldCharOffset:originalPos,
    oldByteOffset:Buffer.byteLength(old.slice(0,originalPos)),oldBytes:Buffer.byteLength(before),newBytes:Buffer.byteLength(after),
    oldLine:old.slice(0,originalPos).split('\n').length,beforeSHA256:sha(before),afterSHA256:sha(after)});
  current=current.slice(0,pos)+after+current.slice(pos+before.length);
};
const hStart=current.indexOf('        have hMeas220 :');
const hEnd=current.indexOf('        have hPhysicalMeasurable :',hStart);
if(hStart<0||hEnd<0)throw Error('Affected complete hMeas220 block absent');
const beforeHMeasBlock=current.slice(hStart,hEnd);
apply('hMeas220 explicit original product measure','∂(μ.prod μ)','∂(@Measure.prod Ω Ω mΩ mΩ μ μ)',hStart,hEnd);
apply('hPhysicalFinite explicit ENNReal top','∀ s : Set (Fin n → Ω), P s ≠ ∞','∀ s : Set (Fin n → Ω), P s ≠ (⊤ : ENNReal)',current.indexOf('        have hPhysicalFinite :'),current.length);
const oldClosing=read(path.join(work,'drafts/oq56/unit248/freeze-01/FROZEN-CLOSING.txt'));
const newClosing=read(path.join(freezeRoot,'FROZEN-CLOSING.txt'));
if(!current.endsWith(oldClosing))throw Error('Old closing absent');
apply('anonymous noncomputable section closing',oldClosing,newClosing,current.length-oldClosing.length,current.length);
const expected=activation.expectedExactThreeDeltaSource;
const actual={sha256:sha(current),bytes:Buffer.byteLength(current),LF:current.split('\n').length-1};
if(actual.sha256!==expected.sha256||actual.bytes!==expected.bytes||actual.LF!==expected.LF)throw Error('Three-delta source differs from exact freeze expectation '+JSON.stringify(actual));
let reversed=current;
for(const d of [...changes].reverse()){
  const p=reversed.indexOf(d.after,d.oldCharOffset);
  if(p<0)throw Error('Reverse block absent '+d.name);
  reversed=reversed.slice(0,p)+d.before+reversed.slice(p+d.after.length);
}
if(reversed!==old)throw Error('Reverse patch failed');
const sourcePath=path.join(root,'OriginalSameWitnessPhysicalPaidTailApplication.lean');
fs.writeFileSync(sourcePath,current,'utf8');
const source=bind(sourcePath);
const now=new Date().toISOString();
const operations={Lean:0,lake:0,kernel:0,PP:0,AX:0,server:0,network:0,upload:0,Git:0,API:0,children:0};
const model={requestedModel:'gpt-6.1-sol',requestedEffort:'xhigh',actualBackend:null,actualModel:null,actualEffort:null,
  usage:{input:null,cachedInput:null,output:null,reasoningSubset:null}};
const originalPosForByte=b=>Buffer.from(old,'utf8').subarray(0,b).toString('utf8').length;
const mapByte=b=>{
  let value=b;
  for(const d of changes){
    const end=d.oldByteOffset+d.oldBytes;
    if(b>=end)value+=d.newBytes-d.oldBytes;
    else if(b>d.oldByteOffset)throw Error('A stored coordinate is inside a replaced token');
  }
  return value;
};
const newPosition=b=>{
  const prefix=Buffer.from(current,'utf8').subarray(0,b).toString('utf8');
  return{byteOffset:b,line:prefix.split('\n').length,column:prefix.length-prefix.lastIndexOf('\n')};
};
const updateCoordinates=value=>{
  if(!value||typeof value!=='object')return;
  if(!Array.isArray(value)&&typeof value.byteOffset==='number'&&typeof value.line==='number'&&typeof value.column==='number'){
    Object.assign(value,newPosition(mapByte(value.byteOffset)));return;
  }
  for(const child of Object.values(value))updateCoordinates(child);
};
const oldContextsPath=path.join(oldRoot,'ACTUAL-PROP-CONTEXTS.json');
const contexts=json(oldContextsPath);
updateCoordinates(contexts);
contexts.atUTC=now;
contexts.source=source;
contexts.schema='oq56-unit248-full-actual-source-contexts-exact3delta-repair-v2';
contexts.priorFullContextInventory=bind(oldContextsPath);
contexts.exactRepairFreeze=activation.newFreeze02;
const changesByName=Object.fromEntries(inv.frozenProofFacts.map(x=>[x.name,x]));
for(const name of ['hMeas220','hPhysicalFinite']){
  const row=contexts.fullFrozenPropositions.find(x=>x.name===name);
  row.previousFullTypeSHA256=sha(row.fullType);
  row.fullType=changesByName[name].fullType;
  row.elaborationOnlyAmendment=true;
  const loc=current.indexOf('have '+name+' :');
  const indent=current.slice(current.lastIndexOf('\n',loc)+1,loc).length;
  const ls=row.fullType.replace(/^\n+|\n+$/g,'').split('\n');
  const base=Math.min(...ls.filter(x=>x.trim()).map(x=>x.match(/^ */)[0].length));
  const type=ls.map(x=>' '.repeat(indent+4)+x.slice(base)).join('\n');
  const header=' '.repeat(indent)+'have '+name+' :\n'+type+' :=';
  const headerPos=current.lastIndexOf('\n',loc)+1;
  if(!current.startsWith(header,headerPos))throw Error('Repaired full frozen type differs '+name);
  row.actualBinding={start:newPosition(Buffer.byteLength(current.slice(0,headerPos))),end:newPosition(Buffer.byteLength(current.slice(0,headerPos+header.length)))};
}
contexts.affectedContextAmendment={changedOnlyFullTypes:['hMeas220','hPhysicalFinite'],scopeClosingOnly:true,
  publicOrdinary145Unchanged:true,optionalOrdinary147Unchanged:true,instances8AndAPI5Unchanged:true,
  other30FrozenFullPropsUnchanged:true,sourceCoordinatesRebasedFromExactThreeDeltas:true,
  oldCompleteSOURCEReviewReused:true,sameIndependentAffectedReviewPending:true};
put('ACTUAL-PROP-CONTEXTS.json',contexts);
const afterHMeasStart=current.indexOf('        have hMeas220 :');
const afterHMeasEnd=current.indexOf('        have hPhysicalMeasurable :',afterHMeasStart);
const diagPath=path.join(work,'drafts/oq56/unit248/lead-execution-01/native-complete-diagnostic-projection.json');
const diag=json(diagPath);
put('DIAGNOSTIC-READ.json',{
  schema:'oq56-unit248-native01-all6-complete-diagnostic-block-read-v1',atUTC:now,projection:bind(diagPath),
  actualRC:diag.actualRC,seconds:diag.seconds,errorsDerived:diag.sourceErrorsDerived,warningsDerived:diag.sourceWarningsDerived,
  object:diag.object,allOwnedEnded:diag.allOwnedEnded,beforeAfterExact:diag.beforeAfterExact,timedOut:diag.timedOut,
  cleanupEvents:diag.cleanupEvents,ownershipIssue:diag.ownershipIssue,
  blocks:diag.completeErrorBlocks.map((text,index)=>({index,firstLine:text.split('\n')[0],sha256:sha(text),bytes:Buffer.byteLength(text),
    LF:text.split('\n').length-1,entireBlockRead:true,readingRanges:index===3?[[0,149],[150,459],[460,925]]:index===4?[[0,329],[330,650],[651,901]]:[[0,text.split('\n').length-1]]})),
  largeUnsolvedGoalContextsRetainedByReference:true,allRemainingErrorsProvenCascades:false,newNativeRequired:true,
  compilerRecoveryPlaceholdersAreNotAuthorSource:true,P168AlreadyAdoptedNeverReadopt:true,operations
});
const prefix=read(path.join(work,'drafts/oq56/unit248/freeze-01/FROZEN-PREAMBLE.txt'))+
  read(path.join(work,'drafts/oq56/unit248/freeze-01/FROZEN-HEAD.txt'));
const intro=read(path.join(work,'drafts/oq56/unit248/freeze-01/FROZEN-INITIAL-INTRO.txt'));
const call=read(path.join(work,'drafts/oq56/unit248/freeze-01/FROZEN-H247-CALL.txt'));
const sourceErrorTokens=/\b(sorry|admit|axiom|unsafe|native_decide)\b/.test(current);
if(!current.startsWith(prefix)||!current.includes(intro)||!current.includes(call)||sourceErrorTokens||current.includes('\r')||current.charCodeAt(0)===0xfeff)throw Error('Frozen/encoding/proof-token guard failed');
const sameTypes=contexts.fullFrozenPropositions.filter(x=>!['hMeas220','hPhysicalFinite'].includes(x.name)).every(x=>
  x.fullType===json(oldContextsPath).fullFrozenPropositions.find(y=>y.name===x.name).fullType);
if(!sameTypes)throw Error('An unaffected full type changed');
put('PATCH.json',{
  schema:'oq56-unit248-exact3frozen-elaboration-only-delta-patch-v1',atUTC:now,oldSource:oldBinding,newSource:source,
  freeze:activation.newFreeze02,changes,changeCountDerived:changes.length,expectedSource:expected,
  fullAffectedSourceBlocks:{hMeas220:{before:beforeHMeasBlock,after:current.slice(afterHMeasStart,afterHMeasEnd)},
    hPhysicalFinite:{before:freeze.changes.find(x=>x.name==='hPhysicalFinite').before,after:freeze.changes.find(x=>x.name==='hPhysicalFinite').after},
    closing:{before:oldClosing,after:newClosing}},
  completePublicPreambleHeadByteExact:true,initial16PiIntroByteExact:true,h247CallByteExact:true,
  reverseThreeDeltasRestoresEntireOldSourceByteExact:true,allOtherProofBytesUnchanged:true,
  allOther30FrozenFullPropsUnchanged:sameTypes,noMathematicalAssumptionOrOutputChange:true,additionalSourceEdits:0,
  originalReviewCoverage:activation.inputs.filter(x=>x.path.includes('/source-review-01/')),
  affectedIndependentReviewPending:true,qualified:false,kernelPending:true,operations
});
put('LOCAL-VALIDATION.json',{
  schema:'oq56-unit248-exact3delta-local-source-byte-validation-only-v1',atUTC:now,status:'PASS_LOCAL_BYTES_ONLY',
  source,sourceLF:actual.LF,sourceExpectedExact:true,all30InputsExact:true,activation:bind(ap),
  oldAuthorReleasedAndImmutable:true,all3FrozenDeltasOnly:true,reverseEntireOldSourceExact:true,
  publicPreambleAndHeadExact:true,original16PiIntroExact:true,h247CallExact:true,other30FrozenFullPropsExact:sameTypes,
  fullAffectedTypeHeadersExact:true,UTF8NoBOM:true,LFOnly:true,noForbiddenSourceTokens:true,
  qualified:false,kernelChecked:false,axiomAudited:false,kernelPending:true,
  notProofOfNativeSuccess:true,noClaimAllPriorUnsolvedGoalsCascades:true,operations
});
put('CHECKPOINT.json',{
  schema:'oq56-unit248-SAMEauthor-exact3delta-repair-checkpoint-v1',atUTC:now,role:activation.role,ownerChat:activation.ownerChat,
  source,sourceLF:actual.LF,freeze:activation.newFreeze02,status:'EXACT_THREE_DELTA_REPAIR_COMPLETE_SOURCE_ONLY',
  actualRuntime:'LOCAL_REPAIR_COMPLETE_PENDING_FINAL_SEAL',heavy:0,inflight:0,pendingExternal:0,children:0,uncertainOperations:0,
  sourceComplete:true,qualified:false,kernelPending:true,sourceAccepted:false,
  nextExactDependency:'SAME independent reviewer reviews two affected complete types and scope closing, joins unchanged prior complete SOURCE review; lead native02 only afterward, P168 never readopted.',
  operations,...model
});
const report=`# Unit248 same-author exact three-delta repair

Status: EXACT_THREE_DELTA_REPAIR_COMPLETE_SOURCE_ONLY. The new source is SHA256 ${actual.sha256}, ${actual.bytes} bytes, ${actual.LF} LF. It exactly equals the lead-frozen expected source. The old author-01 source, manifest, FINALWRITE release, independent review, old/new freezes and native01 failure evidence were read-only throughout.

The repair activation015f8d8317db4597b1664f7e5db5094a631701441913963abc6400795068de30 and all30 inputs were verified before the actual FIRSTWRITE ACK. The old author FINALWRITE release has all six counters zero. This is the same canonical original author with requested gpt-6.1-sol/xhigh, working exclusively in author-repair-01.

All six native01 error blocks were read completely, including the926-line and902-line unsolved-goal context blocks. They remain bound by the original125148-byte diagnostic projection302c4c58. Native01 actually endedRC1 after26.693328987807035 seconds with6errors/2warnings/no object; before-after source/protection preservation is exact, all owned processes ended, no timeout, cleanup or ownership issue. A prior complete independent SOURCE review passed. The original failure and both large contexts remain preserved. This repair does not certify that every other reported goal was a cascade; only a new native run can establish that.

The three changes are exactly:

1. In the complete hMeas220 typed proposition only, change the v integral measure from ∂(μ.prod μ) to ∂(@Measure.prod Ω Ω mΩ mΩ μ μ). The diagnostic at3725:54 explicitly distinguished synthesized selected-space instance this✝² from originalmΩ. The literal original product measure is now explicit, consistent with the original μ and theorem220 application. The entire rest of that full proposition, its call and proof bytes remain unchanged. No law or mathematical premise is changed.
2. In hPhysicalFinite, replace the unscoped infinity token by (⊤ : ENNReal). The expected-token error at3800:41 and Missing cases at3799:13 are retained. The proposition remains that the same original finite product P assigns no set infinite measure. No new scope import, instance, measure or proof step is added.
3. Insert plain end and a blank line before the existing named namespace end, closing the anonymous noncomputable section opened in the exact preamble. The diagnostic at3962:0 explicitly reported that the current scope was unnamed. This changes no theorem, statement or proof.

The two unsolved-goal blocks at3521:6 and744:4 were reviewed in full as diagnostic contexts. They include compiler recovery placeholders for the failed typed measure/top expression; those placeholders are not author-written source. The entire remaining proof, including final reconstruction of all retained conclusions, remains byte exact. No fourth change was made or authorized. PATCH.json includes all exact old/new replacements, full affected blocks and reverse-patch verification restoring the entire old256737-byte source exactly.

The full public head, original16Pi introduction, exact222-byte h247 call, all145 public ordinary rows,147 optional ordinary cap,8 instance rows,5 implicit API rows, both original windows, same cg/m₀/μ₀/ν/η, original weighted full/deleted sourceCost0, clipping1 and true zero-denominator branch remain unchanged. The other30 complete frozen proposition types are exact. ACTUAL-PROP-CONTEXTS.json retains the complete prior context inventory, updates only hMeas220 and hPhysicalFinite full types, and rebases source coordinates using the exact three byte deltas.

No Lean/lake/kernel/PP/AX/server/network/upload/Git/API/child work was performed here. No new execution wrapper, model, assumption, cutoff, source option or instance was introduced. P168 was already adopted in native01 configuration1c8 and was not readopted. No proof/kernel/AX result is claimed: sourceAccepted=false, qualified=false, kernelPending=true. Original externalSZ/cost-smallness/error-absorption/CDF/fullOQ56/root scope exclusions remain.

Next exact dependency: the same qualified independent reviewer covers the two complete affected typed fragments and section closing, joins that evidence to the unchanged complete prior SOURCE review, then the lead may run native02 on the exact new source. The author's final release will be the last write, with all six author-scoped counters zero. Requested model/effort remain gpt-6.1-sol/xhigh; actual backend/model/effort and input/cached-input/output/reasoning-subset usage are unknown/null.
`;
fs.writeFileSync(path.join(root,'REPORT.md'),report,'utf8');
console.log(JSON.stringify({source,LF:actual.LF,changes:changes.length,reverseExact:true,publicHeadExact:true,other30TypesExact:sameTypes,all30BindingsExact:true,qualified:false,kernelPending:true}));
