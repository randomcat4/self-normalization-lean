const fs = require('fs');
const crypto = require('crypto');
const root = __dirname;
const sourcePath = 'C:/game/shao lean/drafts/oq56/unit247/author-01/OriginalSameWitnessClippedPaidTailApplication.lean';
const source = fs.readFileSync(sourcePath, 'utf8');
const lines = source.match(/[^\n]*\n|[^\n]+$/g) || [];
const key = x => x.replace(/^ */, '');
const indent = x => x.length-key(x).length;
const records = [];
const seen = new Map();
let i = 0;
while (i < lines.length) {
  let bestN = 0, bestJ = -1, bestShift=0;
  for (const j of (seen.get(key(lines[i])) || [])) {
    const shift=indent(lines[i])-indent(lines[j]);
    let n = 0;
    while (i+n < lines.length && j+n < i && key(lines[j+n]) === key(lines[i+n]) && indent(lines[i+n])-indent(lines[j+n])===shift) n++;
    if (n > bestN) { bestN=n; bestJ=j; bestShift=shift; }
  }
  if (bestN >= 3 && lines.slice(i,i+bestN).join('').length >= 120) {
    records.push({kind:'reuse', sourceFirst:i+1, sourceLast:i+bestN, previousFirst:bestJ+1, previousLast:bestJ+bestN,indentShift:bestShift});
    for(let p=i;p<i+bestN;p++) { if(!seen.has(key(lines[p]))) seen.set(key(lines[p]),[]); seen.get(key(lines[p])).push(p); }
    i += bestN;
  } else {
    records.push({kind:'literal', sourceFirst:i+1, text:lines[i]});
    if(!seen.has(key(lines[i]))) seen.set(key(lines[i]),[]); seen.get(key(lines[i])).push(i); i++;
  }
}
const restored=[];
for(const r of records) {
  if(r.kind==='literal') restored.push(r.text);
  else for(let p=r.previousFirst-1;p<r.previousLast;p++) restored.push(' '.repeat(indent(restored[p])+r.indentShift)+key(restored[p]));
}
if(Buffer.compare(Buffer.from(restored.join('')),Buffer.from(source))) throw Error('SOURCE ROUNDTRIP FAILURE');
const main = records.map(r => r.kind==='literal' ? `${String(r.sourceFirst).padStart(4)} | ${r.text}` : `${r.sourceFirst}-${r.sourceLast} | <<EXACT REUSE OF EARLIER COMPLETE LINES ${r.previousFirst}-${r.previousLast}; LEADING INDENT SHIFT ${r.indentShift}>>\n`).join('');
fs.writeFileSync(root+'/SOURCE-LOSSLESS-READ.txt',main);
fs.writeFileSync(root+'/SOURCE-LOSSLESS-MAP.json',JSON.stringify({schema:'independent-source-lossless-line-reference-v1', sourcePath, sourceSHA256:crypto.createHash('sha256').update(source).digest('hex'), sourceBytes:Buffer.byteLength(source),sourceLF:(source.match(/\n/g)||[]).length,records,restoredByteExact:true},null,2)+'\n');
const props=JSON.parse(fs.readFileSync('C:/game/shao lean/drafts/oq56/unit247/author-01/ACTUAL-PROP-CONTEXTS.json','utf8'));
const compact={};
for(const k of ['declarationContexts','publicOrdinary','optionalOrdinary','proofFactTypeDictionary','proofFactRecords','pureLogicalWholeProducerPackages','instanceInventory']) {
 const v=props[k]; const first=Array.isArray(v)?v[0]:Object.values(v||{})[0]; compact[k]={type:Array.isArray(v)?'array':typeof v,count:Array.isArray(v)?v.length:Object.keys(v||{}).length,firstKeys:typeof first==='object'?Object.keys(first||{}):[]};
}
console.log(JSON.stringify({rawLines:lines.length,readingLines:main.split('\n').length,readingBytes:Buffer.byteLength(main),reuseBlocks:records.filter(x=>x.kind==='reuse').length,props:compact},null,2));
