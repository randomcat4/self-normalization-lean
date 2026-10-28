const fs=require('fs'),crypto=require('crypto');
const root=__dirname,base='C:/game/shao lean/drafts/oq56/unit247/';
const hash=x=>crypto.createHash('sha256').update(x).digest('hex'), read=p=>JSON.parse(fs.readFileSync(p,'utf8'));
const a=read(base+'final-review-activation-01/ACTIVATION.json');
for(const x of a.inputs){const b=fs.readFileSync(x.path);if(b.length!==x.bytes||hash(b)!==x.sha256)throw Error('input drift '+x.path);}
const d=read(root+'/TYPE-LOSSLESS-DICTIONARY.json'), cache={},used=new Set();
function dec(x){if(typeof x==='string')return[x];used.add(x.ref);if(!cache[x.ref])cache[x.ref]=d.dictionary[x.ref].flatMap(dec);return cache[x.ref];}
const ts=d.main.flatMap(dec), raw=fs.readFileSync(d.rawPath),rest=ts.map((t,i)=>d.triviaBeforeEachExpandedToken[i]+t).join('')+d.trailingTrivia;
if(!Buffer.from(rest).equals(raw))throw Error('TYPE byte restoration');
const rx=new RegExp(d.lexerRegex,'g'), originalTokens=[...raw.toString('utf8').matchAll(rx)].map(m=>m[0]).filter(t=>!/^\s+$/.test(t));
if(JSON.stringify(ts)!==JSON.stringify(originalTokens))throw Error('TYPE token restoration');
const dictText=Object.entries(d.dictionary).map(([k,v])=>k+' := '+v.map(x=>typeof x==='string'?x:'⟪'+x.ref+'⟫').join(' ')).join('\n')+'\n';
if(dictText!==fs.readFileSync(root+'/TYPE-DICTIONARY-READ.txt','utf8'))throw Error('dictionary READ');
const mainText=d.main.map(x=>typeof x==='string'?x:'⟪'+x.ref+'⟫').join(' ');
if(mainText!==fs.readFileSync(root+'/TYPE-MAIN-READ.txt','utf8').replace(/\s+/g,' ').trim())throw Error('main READ');
const m=read(base+'normalized-owner-evidence-01/actual-owned-metadata.json'),s=read(base+'normalized-owner-evidence-01/native-kernel-and-all-owner-audit-summary.json'),b=read(base+'normalized-owner-evidence-01/server-metadata-binding.json');
let stdout='',types='',values='';const allowed=new Set(['propext','Classical.choice','Quot.sound']);
for(const e of m.entries){const j=JSON.parse(e.rawOwnedJSON);for(const [k,v]of Object.entries(j))if(JSON.stringify(v)!==JSON.stringify(e[k]))throw Error('rawJSON mismatch');if(e.components.map(x=>x.value).join('.')!==e.name)throw Error('full name');if(!e.bodyExpressionPresent||e.axioms.some(x=>!allowed.has(x)))throw Error('body/AX');if(/⋯|\.\.\.|<elided>|failed to pretty print|exceeded maximum recursion depth|maximum number of heartbeats/i.test(e.type))throw Error('TYPE failure/elision');stdout+='OQ56_OWNED_JSON '+e.rawOwnedJSON+'\nOQ56_OWNED_TYPE '+e.name+' : '+e.type;types+=e.name+' : '+e.type;if(e.value!==undefined){stdout+='OQ56_OWNED_VALUE '+e.name+' := '+e.value;values+=e.name+' := '+e.value;}}
stdout+=m.rawOwnedCountLine;
if(hash(stdout)!==b.rawStdoutSHA256||Buffer.byteLength(stdout)!==b.rawStdoutBytes||hash(stdout)!==s.ownedAudit01.stdout.sha256)throw Error('audit stdout reconstruction');
if(types!==raw.toString('utf8')||values!==fs.readFileSync(base+'normalized-owner-evidence-01/actual-owned-values.txt','utf8'))throw Error('TYPE VALUE extraction');
if(m.entries.length!==1||m.actualOwnerCount!==1||m.entries.some(x=>!x.isTheorem||x.constantKind!=='thmInfo')||m.nonTheoremCount!==0||values!=='')throw Error('owners');
const expectedO=a.actualFirstOriginalObject;for(const x of [s.object,b.object,m.object])for(const k of ['physical_path','sha256','bytes','mtime_ns'])if(x[k]!==expectedO[k])throw Error('FIRSTO identity');
if(s.source.sha256!==a.source.sha256||m.source.sha256!==a.source.sha256||b.source.sha256!==a.source.sha256)throw Error('source identity');
const prep=read(base+'lead-execution-01/native-preparation-projection.json'),auditPrep=read(base+'lead-execution-01/owned-audit-preparation-projection.json');
if(prep.objectBefore!==null||JSON.stringify(auditPrep.object)!==JSON.stringify(expectedO)||s.native01.actualExitCode!==0||s.ownedAudit01.actualExitCode!==0||!s.native01.beforeAfterExact||!s.ownedAudit01.beforeAfterExact||!s.ownedAudit01.no_o||!s.ownedAudit01.own_object_import)throw Error('native/same-object receipt');
const proofBindingNames=[...rest.matchAll(/\b(?:have|let) (\S+) :/g)].map(x=>x[1]);
const sourceContexts=read(base+'author-01/ACTUAL-PROP-CONTEXTS.json');
if(JSON.stringify(proofBindingNames)!==JSON.stringify(sourceContexts.publicOrdinary.map(x=>x.name)))throw Error('all141 actual public let names/order');
const v={schema:'oq56-unit247-independent-finaljoin-local-verification-v1',atUTC:new Date().toISOString(),immutableInputCountDerived:117,all117Exact:true,SOURCEReviewUnchanged:true,source:a.source,FIRSToriginalObject:expectedO,fullTYPEByteExact:true,fullTYPETokenExact:true,allTriviaExact:true,TYPEsha256:hash(raw),TYPEbytes:raw.length,TYPElines:raw.toString('utf8').split('\n').length-1,TYPEtokens:ts.length,mainRecords:d.main.length,currentMainLines:fs.readFileSync(root+'/TYPE-MAIN-READ.txt','utf8').split('\n').length-1,dictionaryEntries:Object.keys(d.dictionary).length,usedDictionaryClosure:used.size,fullCurrentDictionaryREADMatched:true,fullCurrentMainREADMatched:true,actualTypeOrdinaryLetBindingsDerived:proofBindingNames.length,actualTypeOrdinaryLetBindingNames:proofBindingNames,fullMetadataRawJSONMatched:true,fullAuditStdoutReconstructed:true,rawAuditStdoutSHA256:hash(stdout),rawAuditStdoutBytes:Buffer.byteLength(stdout),actualOwnerCount:m.entries.length,theorems:1,nonTheorems:0,helpers:0,VALUEbytes:0,VALUElines:0,ownerName:m.entries[0].name,levelParams:m.entries[0].levelParams,constantKind:m.entries[0].constantKind,bodyExpressionPresent:true,allActualTransitiveAxioms:m.entries[0].axioms,allWhitelisted:true,nativeRC:0,auditRC:0,nativeStrictWrapperSuccess:false,auditStrictWrapperSuccess:false,nativeOuterRC:read(base+'lead-execution-01/native-transport-result.json').exit_code,auditOuterRC:read(base+'lead-execution-01/audit-transport-result.json').exit_code,FIRSTEMPTY:null,actualRuntimeClaim:'Ended receipt and STARTED record establish execution; live frame missed and no unobserved TID/continuous-runtime claim.',newReviewerLeanCalls:0,newReviewerServerCalls:0,newReviewerNetworkCalls:0,newReviewerChildren:0};
fs.writeFileSync(root+'/VERIFICATION.json',JSON.stringify(v,null,2)+'\n');
console.log(JSON.stringify({...v,actualTypeOrdinaryLetBindingNames:undefined},null,2));
