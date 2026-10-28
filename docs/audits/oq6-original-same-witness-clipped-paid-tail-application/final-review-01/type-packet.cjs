const fs=require('fs'),crypto=require('crypto');
const root=__dirname,prior='C:/game/shao lean/drafts/oq56/unit246/lead-final-type-packet-01/';
const rawPath='C:/game/shao lean/drafts/oq56/unit247/normalized-owner-evidence-01/actual-owned-types.txt';
const d=JSON.parse(fs.readFileSync(prior+'TYPE-LOSSLESS-DICTIONARY.json','utf8'));
const cache={};function expand(xs){return xs.flatMap(x=>typeof x==='string'?[x]:cache[x.ref]||(cache[x.ref]=expand(d.dictionary[x.ref])));}
const raw=fs.readFileSync(rawPath,'utf8'),rx=/\s+|[()\[\]{};,]|[^\s()\[\]{};,]+/g;
const tokens=[],trivia=[];let trailing='';for(const m of raw.matchAll(rx)){if(/^\s+$/.test(m[0]))trailing+=m[0];else{tokens.push(m[0]);trivia.push(trailing);trailing='';}}
const byFirst=new Map();for(const id of Object.keys(d.dictionary)){let ts=expand(d.dictionary[id]);if(!byFirst.has(ts[0]))byFirst.set(ts[0],[]);byFirst.get(ts[0]).push({id,ts});}
const main=[];let n=0;while(n<tokens.length){let best=null;for(const x of byFirst.get(tokens[n])||[]){if((!best||x.ts.length>best.ts.length)&&x.ts.every((t,j)=>tokens[n+j]===t))best=x;}if(best){main.push({ref:best.id,startToken:n,endToken:n+best.ts.length});n+=best.ts.length;}else{main.push(tokens[n]);n++;}}
const display=main.map(x=>typeof x==='string'?x:'⟪'+x.ref+'⟫');let out=[],line='';for(const t of display){if(line.length+t.length+1>168){out.push(line);line=t;}else line+=(line?' ':'')+t;}if(line)out.push(line);
const packet={schema:'oq56-unit247-current-actual-type-established-lossless-dictionary-v1',rawPath,rawSHA256:crypto.createHash('sha256').update(raw).digest('hex'),rawBytes:Buffer.byteLength(raw),lexerRegex:rx.source,tokenCount:tokens.length,dictionary:d.dictionary,dictionaryOrigin:{path:prior+'TYPE-LOSSLESS-DICTIONARY.json',sha256:crypto.createHash('sha256').update(fs.readFileSync(prior+'TYPE-LOSSLESS-DICTIONARY.json')).digest('hex')},dictionaryReferenceCoordinateScope:'Dictionary-internal start/end coordinates are inherited origin metadata only; expansions use ref and literal tokens. Current main has its own current expanded token coordinates.',main,triviaBeforeEachExpandedToken:trivia,trailingTrivia:trailing};
fs.writeFileSync(root+'/TYPE-LOSSLESS-DICTIONARY.json',JSON.stringify(packet,null,2)+'\n');
fs.writeFileSync(root+'/TYPE-DICTIONARY-READ.txt',fs.readFileSync(prior+'TYPE-DICTIONARY-READ.txt'));
fs.writeFileSync(root+'/TYPE-MAIN-READ.txt',out.join('\n')+'\n');
console.log(JSON.stringify({tokens:tokens.length,mainRecords:main.length,mainLines:out.length,mainBytes:Buffer.byteLength(out.join('\n')+'\n'),dictionaryEntries:Object.keys(d.dictionary).length,dictionaryTextUnchanged:true}));
