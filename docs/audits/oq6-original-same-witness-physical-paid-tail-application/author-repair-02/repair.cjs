const fs=require('fs');
const path=require('path');
const crypto=require('crypto');
const root=__dirname;
const work='C:/game/shao lean';
const oldRoot=path.join(work,'drafts/oq56/unit248/author-repair-01');
const read=p=>fs.readFileSync(p,'utf8');
const json=p=>JSON.parse(read(p));
const hash=b=>crypto.createHash('sha256').update(b).digest('hex');
const bind=p=>{const b=fs.readFileSync(p);return{path:p.replaceAll('\\','/'),sha256:hash(b),bytes:b.length};};
const put=(n,j)=>fs.writeFileSync(path.join(root,n),JSON.stringify(j,null,2)+'\n','utf8');
if(fs.existsSync(path.join(root,'lastzeroRELEASE.json')))throw Error('Released directory immutable');
const ap=path.join(work,'drafts/oq56/unit248/repair-activation-02/ACTIVATION.json');
const a=json(ap);
for(const x of a.inputs){const b=bind(x.path);if(b.sha256!==x.sha256||b.bytes!==x.bytes)throw Error('Input changed '+x.path);}
const r=json(a.priorAuthorFINALWRITE.path);
if(!r.FINALWRITE||Object.values(r.sixZero).some(x=>x!==0))throw Error('Prior release invalid');
const f=json(a.newFreeze03.path);
const inv=json(path.join(work,'drafts/oq56/unit248/freeze-03/INTERFACE-INVENTORY.json'));
const oldPath=path.join(oldRoot,'OriginalSameWitnessPhysicalPaidTailApplication.lean');
const old=read(oldPath);
const before=f.sourceEditOnly.before;
const after=f.sourceEditOnly.after;
const at=old.indexOf(before);
if(at<0||old.indexOf(before,at+1)>=0||!after.startsWith(before))throw Error('Nonunique frozen insertion anchor');
const insertion=after.slice(before.length);
if(insertion!=='            letI : MeasurableSpace Ω := mΩ\n')throw Error('Frozen line differs');
const insertAt=at+before.length;
const insertByte=Buffer.byteLength(old.slice(0,insertAt));
const current=old.slice(0,insertAt)+insertion+old.slice(insertAt);
const expected=a.expectedExactOneDeltaSource;
if(hash(current)!==expected.sha256||Buffer.byteLength(current)!==expected.bytes||current.split('\n').length-1!==expected.LF)throw Error('Expected source differs');
const reversed=current.slice(0,insertAt)+current.slice(insertAt+insertion.length);
if(reversed!==old)throw Error('Reverse full source differs');
const sp=path.join(root,'OriginalSameWitnessPhysicalPaidTailApplication.lean');
fs.writeFileSync(sp,current,'utf8');
const source=bind(sp);
const now=new Date().toISOString();
const operations={Lean:0,lake:0,kernel:0,PP:0,AX:0,server:0,network:0,upload:0,Git:0,API:0,children:0};
const model={requestedModel:'gpt-6.1-sol',requestedEffort:'xhigh',actualBackend:null,actualModel:null,actualEffort:null,
  usage:{input:null,cachedInput:null,output:null,reasoningSubset:null}};
const pos=b=>{
  const t=Buffer.from(current,'utf8').subarray(0,b).toString('utf8');
  return{byteOffset:b,line:t.split('\n').length,column:t.length-t.lastIndexOf('\n')};
};
const cp=path.join(oldRoot,'ACTUAL-PROP-CONTEXTS.json');
const oldContexts=json(cp);
const contexts=json(cp);
function rebase(v){
  if(!v||typeof v!=='object')return;
  if(!Array.isArray(v)&&typeof v.byteOffset==='number'&&typeof v.line==='number'&&typeof v.column==='number'){
    Object.assign(v,pos(v.byteOffset+(v.byteOffset>=insertByte?Buffer.byteLength(insertion):0)));return;
  }
  for(const x of Object.values(v))rebase(x);
}
rebase(contexts);
contexts.atUTC=now;
contexts.source=source;
contexts.schema='oq56-unit248-full-source-contexts-typeLocalOriginalOmega-repair-v3';
contexts.priorFullContextInventory=bind(cp);
contexts.exactRepairFreeze=a.newFreeze03;
const row=contexts.fullFrozenPropositions.find(x=>x.name==='hMeas220');
row.previousFullTypeSHA256=hash(row.fullType);
row.fullType=inv.frozenProofFacts.find(x=>x.name==='hMeas220').fullType;
row.typeLocalInnerContextId='C07T';
row.elaborationOnlyAmendment=true;
const fullLines=row.fullType.replace(/^\n+|\n+$/g,'').split('\n');
const base=Math.min(...fullLines.filter(x=>x.trim()).map(x=>x.match(/^ */)[0].length));
const header='        have hMeas220 :\n'+fullLines.map(x=>'            '+x.slice(base)).join('\n')+' :=';
if(!current.startsWith(header,at))throw Error('Complete repaired type header differs');
row.actualBinding={start:pos(Buffer.byteLength(current.slice(0,at))),end:pos(Buffer.byteLength(current.slice(0,at+header.length)))};
contexts.completeUniqueContexts.push({id:'C07T',parent:'C07',text:'letI : MeasurableSpace Ω := mΩ\n',
  scope:'ONLY inside the hMeas220 full typed Prop, from its first type-local letI through its last deleted-subtype measurable E clause.',
  role:'Original Ω type-local instance; no executable or enclosing-context reinstall.',typeLocalOnly:true,originalInstanceArgumentReused:true});
contexts.approvedInstances.push({...f.newScopedInstanceOption,used:true,actualDisposition:'Type-local only inside hMeas220 complete Prop',
  sourceCoordinate:pos(insertByte)});
contexts.countsDerived.approvedInstanceRows=contexts.approvedInstances.length;
contexts.countsDerived.usedApprovedInstanceRows=contexts.approvedInstances.filter(x=>x.used).length;
for(const x of contexts.actualHaveDeclarations)if(x.line>old.slice(0,insertAt).split('\n').length-1)x.line++;
contexts.affectedContextAmendment={changedOnlyFullType:'hMeas220',allOther31FullPropsUnchanged:true,
  newApprovedInstanceOption:f.newScopedInstanceOption,approvedInstanceRowsDerived:contexts.approvedInstances.length,
  noExecutableOriginalOmegaReinstall:true,allOriginalPublicOrdinaryAndChoicesUnchanged:true,
  priorThreeSourceFixesUnchanged:true,oneLineCoordinateRebase:true,oldCompleteSOURCEAndPriorAffectedReviewReused:true,
  sameIndependentAffectedReview02Pending:true};
const other31=contexts.fullFrozenPropositions.filter(x=>x.name!=='hMeas220').every(x=>x.fullType===oldContexts.fullFrozenPropositions.find(y=>y.name===x.name).fullType);
if(!other31||contexts.approvedInstances.length!==9)throw Error('Context invariants differ');
put('ACTUAL-PROP-CONTEXTS.json',contexts);
const dp=path.join(work,'drafts/oq56/unit248/lead-execution-02/native-complete-diagnostic-projection.json');
const diag=json(dp);
const q220p=path.join(work,'drafts/oq56/unit220/qualified-evidence.json');
const q220=json(q220p);
const mp=q220.metadata.path;
const metadata=json(mp);
if(bind(mp).sha256!==q220.metadata.sha256||bind(mp).bytes!==q220.metadata.bytes)throw Error('Qualified220 metadata binding differs');
const entry=metadata.entries.find(x=>x.name==='Shao.OQ6.OriginalClippedStatisticMeasurable.actual_normalized_compact_clipped_observables');
if(!entry||entry.typeLines!==296||!entry.type.includes('mΩ'))throw Error('Qualified220 current TYPE interface absent');
const subtypeAt=entry.type.indexOf('(@Exists.{u + 1}');
put('INTERFACE-AND-DIAGNOSTIC-READ.json',{
  schema:'oq56-unit248-one-current-diagnostic-and-qualified220-TYPE-interface-read-v1',atUTC:now,
  diagnostic:bind(dp),entireErrorBlockRead:true,errorBlockBytes:Buffer.byteLength(diag.completeErrorBlocks[0]),
  errorBlockSHA256:hash(diag.completeErrorBlocks[0]),actualRC:diag.actualRC,seconds:diag.seconds,
  errors:diag.sourceErrorsDerived,warnings:diag.sourceWarningsDerived,object:diag.object,
  allOwnedEnded:diag.allOwnedEnded,beforeAfterExact:diag.beforeAfterExact,protectedRecordsDerived:diag.protectedRecordsDerived,
  timedOut:diag.timedOut,cleanupEvents:diag.cleanupEvents,
  qualified220:bind(q220p),actualCurrentTYPEMetadata:bind(mp),completeCurrentPublicTYPE296Read:true,
  publicTYPEName:entry.name,publicTYPEsha256:hash(entry.type),publicTYPEbytes:Buffer.byteLength(entry.type),
  relevantCompleteDeletedSubtypeTYPEFragment:entry.type.slice(subtypeAt),
  originalArgumentMeasurableSpace:'mΩ',deletedSubtypePiUsesOriginalmOmega:true,
  producerProofReviewOrMachineReplay:false,newNativeStillRequired:true,operations
});
const prefix=read(path.join(work,'drafts/oq56/unit248/freeze-01/FROZEN-PREAMBLE.txt'))+read(path.join(work,'drafts/oq56/unit248/freeze-01/FROZEN-HEAD.txt'));
const closing=read(path.join(work,'drafts/oq56/unit248/freeze-02/FROZEN-CLOSING.txt'));
const intro=read(path.join(work,'drafts/oq56/unit248/freeze-01/FROZEN-INITIAL-INTRO.txt'));
const call=read(path.join(work,'drafts/oq56/unit248/freeze-01/FROZEN-H247-CALL.txt'));
if(!current.startsWith(prefix)||!current.endsWith(closing)||!current.includes(intro)||!current.includes(call))throw Error('Public source invariant differs');
if(current.includes('\r')||current.charCodeAt(0)===0xfeff||/\b(sorry|admit|axiom|unsafe|native_decide)\b/.test(current))throw Error('Source byte/proof token guard failed');
put('PATCH.json',{
  schema:'oq56-unit248-one-frozen-typeLocalOriginalOmega-line-patch-v1',atUTC:now,oldSource:bind(oldPath),newSource:source,
  freeze:a.newFreeze03,changeCountDerived:1,oldCharOffset:insertAt,oldByteOffset:insertByte,
  oldLine:old.slice(0,insertAt).split('\n').length,before,after,insertedLine:insertion,insertedBytes:Buffer.byteLength(insertion),
  fullAffectedTypeBefore:f.onlyChangedFullProp.before,fullAffectedTypeAfter:f.onlyChangedFullProp.after,
  reverseEntire50feaSourceByteExact:true,allOtherSourceBytesUnchanged:true,other31FullPropTypesExact:other31,
  publicHead16PiH247ClosingExact:true,priorThreeSourceFixesExact:true,typeLocalOnly:true,executableOmegaReinstallsAdded:0,
  approvedInstanceRowsDerived:9,ordinary145AndOptional147Unchanged:true,APIImplicit5Unchanged:true,
  newModelLawCutoffPremiseSelector:false,additionalSourceEdits:0,independentAffectedReviewPending:true,
  qualified:false,kernelPending:true,operations
});
put('LOCAL-VALIDATION.json',{
  schema:'oq56-unit248-one-frozen-line-local-validation-only-v1',atUTC:now,status:'PASS_LOCAL_BYTES_ONLY',source,
  sourceLF:expected.LF,expectedSHAAndBytesLFExact:true,all33InputsExact:true,priorAuthorFINALWRITEAndSixZeroVerified:true,
  onlyOneFrozenLine:true,reverseEntireOldSourceExact:true,other31FullPropsExact:other31,
  fullAffectedTypeExact:true,publicPreambleHead16PiCallClosingExact:true,priorThreeFixesRetained:true,
  typeLocalOriginalOmegaInstanceOption9:true,noExecutableOmegaReinstall:true,UTF8NoBOM:true,LFOnly:true,
  qualified:false,sourceAccepted:false,kernelChecked:false,axiomAudited:false,kernelPending:true,
  noPreclaimNative03Success:true,operations
});
put('CHECKPOINT.json',{
  schema:'oq56-unit248-SAMEauthor-repair02-compact-checkpoint-v1',atUTC:now,role:a.role,ownerChat:a.ownerChat,
  source,sourceLF:expected.LF,freeze:a.newFreeze03,status:'EXACT_ONE_TYPE_LOCAL_LINE_REPAIR_COMPLETE_SOURCE_ONLY',
  actualRuntime:'LOCAL_REPAIR_COMPLETE_PENDING_FINAL_SEAL',heavy:0,inflight:0,pendingExternal:0,children:0,uncertainOperations:0,
  qualified:false,kernelPending:true,sourceAccepted:false,
  nextExactDependency:'SAME independent affected review02 joins unchanged complete SOURCE/prior affected coverage, then lead-only native03 from known-ended native02 baseline; no P168 readoption.',
  operations,...model
});
const paragraphs=[
'# Unit248 same-author one-line type-local original-space repair',
'Status: EXACT_ONE_TYPE_LOCAL_LINE_REPAIR_COMPLETE_SOURCE_ONLY. New source SHA256 '+expected.sha256+', '+expected.bytes+' bytes, '+expected.LF+' LF; exactly equal to the lead freeze. All33 input bindings and the prior FINALWRITE six-zero release were verified before the actual FIRSTWRITE ACK. Only author-repair-02 was writable; all earlier source, reviews, freezes and native failure evidence remain immutable.',
'The only source change is the45-byte line with twelve spaces followed by letI : MeasurableSpace Ω := mΩ and LF, immediately inside the complete hMeas220 TYPE before its g let. Reversing that insertion restores the entire256777-byte50fea source exactly. The complete public head, original16Pi introduction,222-byte h247 call, prior repaired closing and all remaining proof bytes are unchanged. All other31 frozen full proposition types,145 public ordinary rows,147 optional ordinary rows and5 implicit API rows remain exact. No new executable code or outer Ω instance reinstall is added.',
'Native02 actually endedRC1 in26.166772451251745 seconds with one error/eight warnings/no object; all owned processes ended,25348 protected records were preserved exactly, no timeout or cleanup. The entire5264-byte type-mismatch diagnostic at3767:12 was read. It prints the result and expected types similarly, including the final existential deleted-subtype E measurable clause. The diagnostic is retained by its original binding; no new Lean or diagnostic printer was run.',
'The qualified220 current complete296-line public TYPE was read from exact owner metadata23438359180e7faa294551212f1171869a83589f09144751fc40d3713907d810. In its final existential E clause, the source domain is the product of original Ω over {j : Fin n // j ≠ i}; the explicit MeasurableSpace.pi factors are all originalmΩ. Existing originalsamplemN overrides Fin n → Ω only. Before this repair, the type-local deleted-subtype Pi could still infer selectedm₀, causing the hidden mismatch while the printer displayed the same surface text. The new first type-local Ω instance makes every domain in the complete hMeas220 Prop use the original given mΩ, consistent with the unchanged explicit Ω/mΩ/μ application of qualified220.',
'This is a source-level diagnosis and exact frozen elaboration repair. Native03 must confirm it; no proof pass or fully resolved elaboration is claimed. The new ninth approved instance option is scoped exclusively inside hMeas220 TYPE and reuses an existing input argument. It introduces no assumption, model, law, measure, cutoff or selector. The earlier explicit original product measure, typed ENNReal top and anonymous-section closing are byte exact.',
'ACTUAL-PROP-CONTEXTS.json preserves the full context/type inventory, changes only hMeas220 full type, adds the explicit type-local context and ninth instance option, and rebases every recorded source coordinate. PATCH.json records the exact line and full affected before/after types. INTERFACE-AND-DIAGNOSTIC-READ.json binds the complete native02 diagnostic and qualified220 current TYPE read, with the complete relevant deleted-subtype fragment. No accepted producer proof was rereviewed or rechecked.',
'No Lean/lake/kernel/PP/AX/server/network/upload/Git/API/children operation was performed. P168 was already adopted in native01cfg1c8 and is not readopted. qualified=false, sourceAccepted=false, kernelPending=true. Original externalSZ/cost-smallness/error-absorption/CDF/fullOQ56/root exclusions remain unchanged.',
'Next exact dependency: the same qualified independent reviewer performs affected review02 and joins unchanged complete prior SOURCE and first affected coverage, then the lead runs native03 on exact50cc source from the known-ended native02 baseline. The final release will be the last filesystem write, with all six author-scoped counters zero. Requested gpt-6.1-sol/xhigh; actual backend/model/effort and separate input/cached-input/output/reasoning-subset usage remain unknown/null.'
];
fs.writeFileSync(path.join(root,'REPORT.md'),paragraphs.join('\n\n')+'\n','utf8');
console.log(JSON.stringify({source,LF:expected.LF,insertedBytes:Buffer.byteLength(insertion),reverseExact:true,other31FullTypesExact:other31,approvedInstanceRows:contexts.approvedInstances.length,all33BindingsExact:true,qualified:false,kernelPending:true}));
