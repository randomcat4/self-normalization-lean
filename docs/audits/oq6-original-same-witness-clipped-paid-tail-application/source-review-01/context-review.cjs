const fs=require('fs'), crypto=require('crypto');
const root=__dirname, base='C:/game/shao lean/drafts/oq56/unit247/';
const source=fs.readFileSync(base+'author-01/OriginalSameWitnessClippedPaidTailApplication.lean','utf8');
const p=JSON.parse(fs.readFileSync(base+'author-01/ACTUAL-PROP-CONTEXTS.json','utf8'));
const tokenRx=/\s+|[()\[\]{};,]|[^\s()\[\]{};,]+/g;
function lex(s){let toks=[],trivia=[],space='';for(const m of s.matchAll(tokenRx)){if(/^\s+$/.test(m[0]))space+=m[0];else{toks.push(m[0]);trivia.push(space);space='';}}return{toks,trivia,trailing:space};}
const st=lex(source).toks, idx=new Map();for(let i=0;i<st.length-4;i++){let k=JSON.stringify(st.slice(i,i+4));if(!idx.has(k))idx.set(k,[]);idx.get(k).push(i);}
const strings=[],unique=new Map(),refs=[];
function add(label,s){if(typeof s!=='string')return;if(unique.has(s)){refs.push({label,reuse:unique.get(s)});return;}let id='C'+String(strings.length+1).padStart(4,'0');unique.set(s,id);let l=lex(s),recs=[];for(let i=0;i<l.toks.length;){let bn=0,bj=0;for(const j of (idx.get(JSON.stringify(l.toks.slice(i,i+4)))||[])){let n=4;while(i+n<l.toks.length&&st[j+n]===l.toks[i+n])n++;if(n>bn){bn=n;bj=j;}}if(bn>=8){recs.push({s:bj,n:bn});i+=bn;}else{recs.push({t:l.toks[i]});i++;}}let restored=[];for(const r of recs)if(r.t!==undefined)restored.push(r.t);else restored.push(...st.slice(r.s,r.s+r.n));let text=restored.map((t,i)=>l.trivia[i]+t).join('')+l.trailing;if(text!==s)throw Error('roundtrip '+label);strings.push({id,label,raw:s,recs,trivia:l.trivia,trailing:l.trailing,tokenCount:l.toks.length});refs.push({label,reuse:id});}
for(const [k,v]of Object.entries(p.declarationContexts))add('declarationContexts.'+k,v);
for(const group of ['publicOrdinary','optionalOrdinary','instanceInventory','pureLogicalWholeProducerPackages','logicalOnlyBoundVariables'])for(const [i,v]of (p[group]||[]).entries()){for(const k of ['type','rhs','enclosingParameterContext','completeEnclosingParameterContext','proofMirrorActualContext'])add(group+'.'+i+'.'+v.name+'.'+k,v[k]);}
for(const [k,v]of Object.entries(p.proofFactTypeDictionary))for(const f of ['type','enclosingParameterContext'])add('proofFact.'+k+'.'+f,v[f]);
add('completeResultType',p.completeResultType);add('fullExistingAssumptionBindersIn',p.fullExistingAssumptionBindersIn);
const out=[];for(const x of strings){out.push(x.id+' '+x.label+' ['+x.tokenCount+' tokens]');out.push(x.recs.map(r=>r.t!==undefined?r.t:`⟪SOURCE-TOKENS ${r.s+1}..${r.s+r.n}⟫`).join(' '));}
out.push('ALL EXACT CONTEXT ALIASES');for(const r of refs)out.push(r.label+' = '+r.reuse);
fs.writeFileSync(root+'/CONTEXT-LOSSLESS-READ.txt',out.join('\n')+'\n');
fs.writeFileSync(root+'/CONTEXT-LOSSLESS-MAP.json',JSON.stringify({schema:'independent-context-token-references-v1',sourceTokenCount:st.length,strings,refs,allByteRestorationsExact:true},null,2)+'\n');
const rows=p.optionalOrdinary.map((v,i)=>({i:i+1,name:v.name,type:v.type,rhs:v.rhs,scope:v.scope,line:v.sourceDeclaration?.startLine,end:v.sourceDeclaration?.endLine,used:v.mirrorUsed,mirrorLine:v.mirrorSourceLine,kind:v.kind}));
fs.writeFileSync(root+'/ORDINARY-SCOPE-READ.txt',rows.map(v=>JSON.stringify(v)).join('\n')+'\n');
fs.writeFileSync(root+'/INSTANCE-READ.txt',p.instanceInventory.map(v=>JSON.stringify(Object.fromEntries(Object.entries(v).filter(([k])=>k!=='enclosingParameterContext')))).join('\n')+'\n');
console.log(JSON.stringify({uniqueContextStrings:strings.length,contextAliases:refs.length,contextReadBytes:Buffer.byteLength(out.join('\n')),ordinaryCount:rows.length,ordinaryUsed:rows.filter(v=>v.used).length,instanceCount:p.instanceInventory.length}));
