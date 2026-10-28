from pathlib import Path
import re, json, hashlib, datetime

ROOT = Path(r'C:/game/shao lean')
OUT = ROOT / 'drafts/oq56/unit248/source-review-01'
def sha(b): return hashlib.sha256(b).hexdigest()
def save(name, obj):
    (OUT/name).write_text(json.dumps(obj, ensure_ascii=False, indent=2)+'\n', encoding='utf-8', newline='\n')

a_path = ROOT/'drafts/oq56/unit248/source-review-activation-01/ACTIVATION.json'
a = json.loads(a_path.read_bytes())
checks = []
for row in a['inputs']:
    raw = Path(row['path']).read_bytes()
    assert sha(raw) == row['sha256'] and len(raw) == row['bytes'], row['path']
    checks.append(dict(row, verified=True))
save('INPUT-VERIFICATION.json', {'atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'activationSHA256':sha(a_path.read_bytes()), 'countDerived':len(checks), 'inputs':checks})

# Independently restore the established qualified247 token/dictionary/trivia packet.
prior = ROOT/'drafts/oq56/unit247/final-review-01'
d = json.loads((prior/'TYPE-LOSSLESS-DICTIONARY.json').read_bytes())
cache = {}
def expand(xs):
    ts = []
    for x in xs:
        if isinstance(x,str): ts.append(x)
        else:
            ref=x['ref']
            if ref not in cache: cache[ref] = expand(d['dictionary'][ref])
            ts.extend(cache[ref])
    return ts
tokens = expand(d['main'])
rebuilt = ''.join(t+s for t,s in zip(d['triviaBeforeEachExpandedToken'], tokens)) + d['trailingTrivia']
raw = Path(d['rawPath']).read_bytes()
assert len(tokens)==d['tokenCount'] and rebuilt.encode('utf-8')==raw
rx = re.compile(d['lexerRegex'])
independent_tokens=[m.group() for m in rx.finditer(raw.decode('utf-8')) if not m.group().isspace()]
assert independent_tokens==tokens
def refs_text(xs):
    return ' '.join(x if isinstance(x,str) else '⟪'+x['ref']+'⟫' for x in xs)
dictionary_read='\n'.join(k+' := '+refs_text(v) for k,v in d['dictionary'].items())+'\n'
assert dictionary_read==(prior/'TYPE-DICTIONARY-READ.txt').read_text(encoding='utf-8')
display=[x if isinstance(x,str) else '⟪'+x['ref']+'⟫' for x in d['main']]
lines=[]; line=''
for t in display:
    if len(line)+len(t)+1>168: lines.append(line); line=t
    else: line+=(' ' if line else '')+t
if line: lines.append(line)
assert '\n'.join(lines)+'\n'==(prior/'TYPE-MAIN-READ.txt').read_text(encoding='utf-8')
save('TYPE247-INDEPENDENT-RESTORATION.json', {'rawPath':d['rawPath'],'rawSHA256':sha(raw),'rawBytes':len(raw),
    'tokenCountDerived':len(tokens),'dictionaryEntriesDerived':len(d['dictionary']),
    'mainEntriesDerived':len(d['main']),'mainReadLinesDerived':len(lines),
    'wholeByteRoundTrip':True,'wholeTokenRoundTrip':True,'wholeTriviaRoundTrip':True,
    'dictionaryAndMainReadFilesMatchPacket':True,'oldProofsReviewed':False})

# A lossless line dictionary of the CURRENT source.  Every unique complete line is
# displayed literally. Main records contain each line id and its exact leading
# whitespace; internal/trailing whitespace and line endings are retained separately.
# This is text packaging only, not a Lean parser or a mathematical check.
source=Path(a['source']['path']); raw=source.read_bytes(); text=raw.decode('utf-8')
full_lines=text.splitlines(keepends=True)
dictionary={}; ids={}; main=[]; dictionary_read=[]
for lineno, line in enumerate(full_lines,1):
    body=line.rstrip('\r\n'); ending=line[len(body):]
    leading=body[:len(body)-len(body.lstrip())]; core=body.strip(); trailing=body[len(body.rstrip()):]
    # Empty lines have no duplicated leading/trailing whitespace in reconstruction.
    if not core: leading=body; trailing=''
    if core not in ids:
        ident=f'S{len(ids)+1:04d}'; ids[core]=ident
        dictionary[ident]={'firstSourceLine':lineno,'text':core}
        dictionary_read.append(f'{ident} [first L{lineno}] := {core}')
    main.append({'ref':ids[core],'sourceLine':lineno,'leading':leading,'trailing':trailing,'ending':ending})
restored=''.join(x['leading']+dictionary[x['ref']]['text']+x['trailing']+x['ending'] for x in main)
assert restored.encode('utf-8')==raw
tokrx=re.compile(r'\s+|[()\[\]{};,]|[^\s()\[\]{};,]+')
assert [m.group() for m in tokrx.finditer(restored)]==[m.group() for m in tokrx.finditer(text)]
save('SOURCE-LOSSLESS-DICTIONARY.json',{'schema':'independent-current-source-whole-line-dictionary-v1',
    'source':a['source'],'sourceLF':raw.count(b'\n'),'dictionary':dictionary,'main':main,
    'wholeByteRoundTrip':True,'wholeTokenAndTriviaRoundTrip':True})
(OUT/'SOURCE-DICTIONARY-READ.txt').write_text('\n'.join(dictionary_read)+'\n',encoding='utf-8',newline='\n')
main_display=[]
for i in range(0,len(main),32):
    chunk=main[i:i+32]
    main_display.append(f"L{chunk[0]['sourceLine']}-{chunk[-1]['sourceLine']}: "+' '.join(x['ref']+'^'+str(len(x['leading'])) for x in chunk))
(OUT/'SOURCE-MAIN-READ.txt').write_text('\n'.join(main_display)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({'inputsVerified':len(checks),'sourceBytes':len(raw),'sourceLF':raw.count(b'\n'),
      'sourceDictionaryEntries':len(dictionary),'sourceDictionaryBytes':(OUT/'SOURCE-DICTIONARY-READ.txt').stat().st_size,
      'sourceMainReadLines':len(main_display),'sourceMainReadBytes':(OUT/'SOURCE-MAIN-READ.txt').stat().st_size,
      'byteTokenTriviaRoundTrips':True},ensure_ascii=False))
