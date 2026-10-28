from pathlib import Path
import datetime, hashlib, json, re

BASE=Path('C:/game/shao lean/drafts/oq56/unit248')
OUT=BASE/'final-review-01'
assert not (OUT/'lastzeroRELEASE.json').exists(), 'FINALWRITE immutable'
SHA=lambda b:hashlib.sha256(b).hexdigest()
def save(name,j):
    (OUT/name).write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')

# Reuse the established lossless dictionary grammar, with a completely NEW current main.
prior=Path('C:/game/shao lean/drafts/oq56/unit247/final-review-01/TYPE-LOSSLESS-DICTIONARY.json')
seed=json.loads(prior.read_bytes())
rawpath=BASE/'normalized-owner-evidence-01/actual-owned-types.txt'
raw=rawpath.read_bytes(); text=raw.decode('utf-8')
metadata=json.loads((BASE/'normalized-owner-evidence-01/actual-owned-metadata.json').read_bytes())
e=metadata['entries'][0]
assert text==e['name']+' : '+e['type']
rx=re.compile(seed['lexerRegex'])
matches=[m for m in rx.finditer(text) if not m.group().isspace()]
tokens=[m.group() for m in matches]
trivia=[]; pos=0
for m in matches:
    trivia.append(text[pos:m.start()]);pos=m.end()
trailing=text[pos:]
cache={}
def expand(xs):
    out=[]
    for x in xs:
        if isinstance(x,str):out.append(x)
        else:
            k=x['ref']
            if k not in cache:cache[k]=expand(seed['dictionary'][k])
            out.extend(cache[k])
    return out
index={}
for k,v in seed['dictionary'].items():
    value=expand(v)
    assert value
    index.setdefault(value[0],[]).append((k,value))
for xs in index.values():xs.sort(key=lambda row:(-len(row[1]),row[0]))
main=[];i=0
while i<len(tokens):
    found=False
    for k,v in index.get(tokens[i],[]):
        if tokens[i:i+len(v)]==v:
            main.append({'ref':k});i+=len(v);found=True;break
    if not found:main.append(tokens[i]);i+=1

needed=set()
def need(k):
    if k in needed:return
    needed.add(k)
    for x in seed['dictionary'][k]:
        if isinstance(x,dict):need(x['ref'])
for x in main:
    if isinstance(x,dict):need(x['ref'])
dictionary={k:v for k,v in seed['dictionary'].items() if k in needed}
packet={'schema':'oq56-current248-actualTYPE-lossless-token-dictionary-v1','rawPath':rawpath.as_posix(),
 'rawSHA256':SHA(raw),'rawBytes':len(raw),'rawLF':raw.count(b'\n'),
 'actualTYPEBodySHA256':SHA(e['type'].encode()),'actualTYPEBodyBytes':len(e['type'].encode()),
 'lexerRegex':seed['lexerRegex'],'tokenCount':len(tokens),'dictionary':dictionary,
 'dictionaryOrigin':{'path':prior.as_posix(),'sha256':SHA(prior.read_bytes()),'bytes':len(prior.read_bytes()),
                     'meaning':'Established literal token grammar only. Oldmain/proof/TYPE not reread; all current dictionary and NEW currentmain must be fully read.'},
 'dictionaryReferenceCoordinateScope':'Nested dictionary startToken/endToken annotations are inherited ORIGINAL grammar-origin coordinates, never current248 coordinates. Only ref determines expansion; currentmain and current token/trivia restoration are independent.',
 'main':main,'triviaBeforeEachExpandedToken':trivia,'trailingTrivia':trailing}
def display(xs):return ' '.join(x if isinstance(x,str) else '⟪'+x['ref']+'⟫' for x in xs)
dread='\n'.join(k+' := '+display(v) for k,v in dictionary.items())+'\n'
lines=[];line=''
for x in main:
    token=x if isinstance(x,str) else '⟪'+x['ref']+'⟫'
    if len(line)+len(token)+1>168:
        lines.append(line);line=token
    else:line+=(' ' if line else '')+token
if line:lines.append(line)
mread='\n'.join(lines)+'\n'
save('TYPE-LOSSLESS-DICTIONARY.json',packet)
(OUT/'TYPE-DICTIONARY-READ.txt').write_text(dread,encoding='utf-8',newline='\n')
(OUT/'TYPE-MAIN-READ.txt').write_text(mread,encoding='utf-8',newline='\n')
save('LOCAL-DIAGNOSTIC-HISTORY.json',{'schema':'oq56-unit248-finaljoin-local-read-diagnostics-v1',
 'atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'events':[{'operation':'Read-only metadata shape inspection','exception':'TypeError: object of type int has no len()',
            'cause':'typeLines is a line-count integer, not a list.','effect':'No mutation or mathematical execution; later inspection uses the integer directly.'},
           {'operation':'Metadata warning-row display','effect':'Tool output truncated warning metadata; no complete warning-message reading claimed. Full mathematics was not in that truncation.'},
           {'operation':'Lossless TYPE packet preparation, first attempt','exception':'AssertionError at type-file/body composition boundary',
            'cause':'The metadata TYPE body already includes its final LF; the inspection incorrectly expected one additional LF.',
            'correction':'Exact file equals name + literal space-colon-space + the complete body, with no extra LF.',
            'effect':'Preparation stopped before packet writes; no source or mathematical execution.'}],
 'uncertainOperations':0,'sourceEffects':0,'proofResult':None})
print(json.dumps({'currentRawTypeSHA256':SHA(raw),'rawBytes':len(raw),'rawLF':raw.count(b'\n'),
 'bodySHA256':SHA(e['type'].encode()),'bodyBytes':len(e['type'].encode()),
 'tokens':len(tokens),'dictionaryEntries':len(dictionary),'dictionaryReadBytes':len(dread.encode()),
 'mainEntries':len(main),'mainReadLines':len(lines),'mainReadBytes':len(mread.encode()),
 'actualReadingStillPending':True},ensure_ascii=False))
