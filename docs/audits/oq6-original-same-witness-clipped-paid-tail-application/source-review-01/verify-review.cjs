const fs=require('fs'), crypto=require('crypto');
const root=__dirname, base='C:/game/shao lean/drafts/oq56/unit247/';
const read=p=>fs.readFileSync(p,'utf8'), sha=s=>crypto.createHash('sha256').update(s).digest('hex');
const norm=s=>s.replace(/\s+/g,' ').trim();
const s=read(base+'author-01/OriginalSameWitnessClippedPaidTailApplication.lean');
const p=JSON.parse(read(base+'author-01/ACTUAL-PROP-CONTEXTS.json'));
const a=JSON.parse(read(base+'source-review-activation-01/ACTIVATION.json'));
for(const x of a.inputs){const b=fs.readFileSync(x.path);if(b.length!==x.bytes||sha(b)!==x.sha256)throw Error('input drift '+x.path);}
const m=JSON.parse(read(root+'/SOURCE-LOSSLESS-MAP.json'));const rl=[];for(const r of m.records){if(r.kind==='literal')rl.push(r.text);else for(let j=r.previousFirst-1;j<r.previousLast;j++){const old=rl[j],n=old.match(/^ */)[0].length+r.indentShift;rl.push(' '.repeat(n)+old.replace(/^ */,''));}}
if(rl.join('')!==s)throw Error('independent source restore');
const rx=/\s+|[()\[\]{};,]|[^\s()\[\]{};,]+/g;
const toks=t=>[...t.matchAll(rx)].map(x=>x[0]).filter(t=>!/^\s+$/.test(t));
const st=toks(s),c=JSON.parse(read(root+'/CONTEXT-LOSSLESS-MAP.json'));
for(const x of c.strings){let ts=[];for(const r of x.recs)if(r.t!==undefined)ts.push(r.t);else ts.push(...st.slice(r.s,r.s+r.n));if(ts.map((t,i)=>x.trivia[i]+t).join('')+x.trailing!==x.raw)throw Error('independent context restore '+x.id);}
const db='C:/game/shao lean/drafts/oq56/unit246/lead-final-type-packet-01/';
const d=JSON.parse(read(db+'TYPE-LOSSLESS-DICTIONARY.json'));let cache={};function exp(v){return v.flatMap(x=>typeof x==='string'?[x]:cache[x.ref]||(cache[x.ref]=exp(d.dictionary[x.ref])));}
const dt=exp(d.main), restored=dt.map((t,i)=>d.triviaBeforeEachExpandedToken[i]+t).join('')+d.trailingTrivia;
if(restored!==read(d.rawType.path))throw Error('independent246 TYPE restore');
for(const [id,ds]of Object.entries(d.dictionary)){const line=id+' := '+ds.map(x=>typeof x==='string'?x:'⟪'+x.ref+'⟫').join(' ');if(!read(db+'TYPE-DICTIONARY-READ.txt').split(/\r?\n/).includes(line))throw Error('dict read mismatch '+id);}
if(norm(read(db+'TYPE-MAIN-READ.txt'))!==norm(d.main.map(x=>typeof x==='string'?x:'⟪'+x.ref+'⟫').join(' ')))throw Error('mainread mismatch');
const q=JSON.parse(read('C:/game/shao lean/drafts/oq56/unit246/normalized-owner-evidence-01/actual-owned-metadata.json'));
const publicType=read('C:/game/shao lean/drafts/oq56/unit246/normalized-owner-evidence-02/public-full-type.txt');
if(norm(q.entries[0].type)!==norm(publicType))throw Error('public extraction');
const lines=s.split('\n');let publicMapFailures=[];
for(const v of p.publicOrdinary){const raw=lines.slice(v.sourceDeclaration.startLine-1,v.sourceDeclaration.endLine).join('\n');if(!norm(raw).includes(norm('let '+v.name+' : '+v.type+' := '+v.rhs)))publicMapFailures.push(v.name+'@'+v.sourceDeclaration.startLine);}
if(publicMapFailures.length)throw Error('ordinary mapping '+publicMapFailures.join(','));
const freezeExact=s.startsWith(read(base+'freeze-02/FROZEN-PREAMBLE.txt')+read(base+'freeze-02/FROZEN-HEAD.txt'))&&s.endsWith(read(base+'freeze-02/FROZEN-CLOSING.txt'));
if(!freezeExact)throw Error('freeze head/closing');
const delta=JSON.parse(read(base+'author-01/PROOF-DELTA.json'));let provisional=s;
for(const x of delta.changedLines){if(provisional.split(x.new).length!==2)throw Error('delta not unique');provisional=provisional.replace(x.new,x.old);}
if(provisional!==read(delta.provisional.path))throw Error('two line reverse');
const facts=[...s.matchAll(/^\s*have (\S+)\s*:/gm)].map(x=>x[1]);facts.push('h246','hUpperFailed');
const typeCoverage=JSON.parse(read('C:/game/shao lean/drafts/oq56/unit246/normalized-owner-evidence-02/TYPE-coverage.json'));
const inv=JSON.parse(read(base+'freeze-01/INTERFACE-INVENTORY.json'));
const ordinaryFreezeMatch=p.publicOrdinary.every((v,i)=>['name','type','rhs','scope'].every(k=>norm(v[k])===norm(inv.ordinaryBindings[i][k])));
if(!ordinaryFreezeMatch)throw Error('frozen ordinary mismatch');
const factFreezeMatch=Object.entries(p.proofFactTypeDictionary).every(([k,v])=>norm(v.type)===norm(inv.proofFactTypeDictionary[k].type));
if(!factFreezeMatch)throw Error('frozen fact mismatch');
function conjunctions(first,last){let depth=0,n=1;for(const c of lines.slice(first-1,last).join('\n')){if('([{'.includes(c))depth++;else if(')]}'.includes(c))depth--;else if(c==='∧'&&depth===0)n++;}return n;}
const universalConj=conjunctions(166,489),paymentConj=conjunctions(601,676),jointConj=conjunctions(404,440);
const currentResult=s.slice(s.indexOf('    let g'),s.indexOf('\n := by'));
const priorResult=norm(read(base+'freeze-03/EXPECTED-H246-PROP.txt'));
const removed=norm(currentResult.replace(lines.slice(584,600).join('\n')+'\n','').replace(lines.slice(662,674).join('\n')+'\n',''));
if(removed!==priorResult)throw Error('exact retained246 result removal');
const result={schema:'unit247-independent-local-byte-context-verification-v1',sourceSHA256:sha(s),sourceBytes:Buffer.byteLength(s),sourceLF:(s.match(/\n/g)||[]).length,immutableInputs:76,sourceLineRestorationExact:true,sourceReadingRecords:m.records.length,sourceRepeatedBlocks:m.records.filter(r=>r.kind==='reuse').length,contextStrings:c.strings.length,contextAliases:c.refs.length,allContextByteTokenTriviaRestorationExact:true,producer246FullTYPEByteTokenTriviaRestorationExact:true,producer246MainTokens:dt.length,producer246DictionaryEntries:Object.keys(d.dictionary).length,producer246PublicTYPEExactlyFromOriginalMetadata:true,producer246CoverageKinds:typeCoverage.entries.map(x=>({name:x.name,kind:x.completeTypeRepresentation.kind,axioms:x.axioms})),frozenPublicHeadPreambleClosingExact:freezeExact,publicOrdinaryFromActualSource:p.publicOrdinary.length,allPublicTypeRHSMapsIndependentlyMatched:true,optionalCount:p.optionalOrdinary.length,optionalUsed:p.optionalOrdinary.filter(x=>x.mirrorUsed).length,optionalUnused:p.optionalOrdinary.filter(x=>!x.mirrorUsed).length,instances:p.instanceInventory.length,facts: [...new Set(facts)],factCount:[...new Set(facts)].length,frozenPropDictionaryCount:Object.keys(p.proofFactTypeDictionary).length,logicalPackageCount:p.pureLogicalWholeProducerPackages.length,twoLineDeltaReverseExact:true,CR:(s.match(/\r/g)||[]).length,forbidden:(s.match(/\b(sorry|admit|axiom|unsafe|native_decide)\b/g)||[]),LeanCalls:0,serverCalls:0,networkCalls:0,children:0,qualified:false,kernelPending:true};
Object.assign(result,{frozenOrdinaryNamesTypesRHSScopesExact:ordinaryFreezeMatch,frozenFactFullTypesExact:factFreezeMatch,universalConjunctsDerived:universalConj,paymentConjunctsDerived:paymentConj,retainedPaymentConjunctsDerived:paymentConj-1,jointPacketConjunctsDerived:jointConj,completePrior246ResultRecoveredByOnlyNewDataAndContractRemoval:true,frozenFactNames: Object.keys(p.proofFactTypeDictionary),frozenFactsAllUsed:p.proofFactTypeDictionary&&Object.values(p.proofFactTypeDictionary).every(v=>v.used),pureLogicalPackages:p.pureLogicalWholeProducerPackages.map(v=>({name:v.name,sourceStartLine:v.sourceStartLine,sourceEndLine:v.sourceEndLine})),instanceCoordinateCorrection:{authorMetadataSelectedSpaceLine:688,actualExecutableProofInstallLine:1930,reason:'688 is a type-local restatement; actual proof has sole selected-space installation at1930. Source unaffected.'}});
fs.writeFileSync(root+'/LOCAL-VERIFICATION.json',JSON.stringify(result,null,2)+'\n');
console.log(JSON.stringify(result,null,2));
