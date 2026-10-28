import datetime
import hashlib
import json
import pathlib
import re

ROOT = pathlib.Path('C:/game/shao lean')
UNIT = ROOT / 'drafts/oq56/unit253'
OUT = UNIT / 'source-review-01'
AUTHOR = UNIT / 'author-01'

def read(p):
    return pathlib.Path(p).read_bytes()

def sha(b):
    return hashlib.sha256(b).hexdigest()

def fp(p):
    p = pathlib.Path(p)
    b = read(p)
    return dict(path=p.as_posix(), sha256=sha(b), bytes=len(b), LF=b.count(b'\n'))

def jread(p):
    return json.loads(read(p).decode('utf-8'))

seen = {}
def bindings(obj):
    if isinstance(obj, dict):
        path = obj.get('path')
        if isinstance(path, str) and obj.get('sha256') and obj.get('bytes') is not None:
            p = pathlib.Path(path)
            if p.is_file():
                q = fp(p)
                assert q['sha256'] == obj['sha256'], (path, 'hash')
                assert q['bytes'] == obj['bytes'], (path, 'bytes')
                if 'LF' in obj:
                    assert q['LF'] == obj['LF'], (path, 'LF')
                seen[p.as_posix()] = q
        for v in obj.values():
            bindings(v)
    elif isinstance(obj, list):
        for v in obj:
            bindings(v)

roots = list((UNIT / 'freeze-01').glob('*')) + [
    AUTHOR / 'MANIFEST.json', AUTHOR / 'FINALWRITE.json',
    UNIT / 'parent-author-source-intake-01.json',
    ROOT / 'drafts/oq56/unit251/qualified-evidence.json',
    ROOT / 'drafts/oq56/unit252/qualified-evidence.json',
]
for p in roots:
    seen[p.as_posix()] = fp(p)
    if p.suffix == '.json':
        bindings(jread(p))

source_path = AUTHOR / 'OriginalLevelDependentCountablyGeneratedModel.lean'
b = read(source_path)
s = b.decode('utf-8')
assert sha(b) == '00c05d340014e5d8193390ab01beaf19f2ee86423767953c8eb86585e38386be'
assert len(b) == 15673 and b.count(b'\n') == 265
assert b'\r' not in b and not b.startswith(b'\xef\xbb\xbf') and b.endswith(b'\n') and not b.endswith(b'\n\n')
freeze = UNIT / 'freeze-01'
assert b == read(freeze/'FROZEN-PREAMBLE.txt') + read(freeze/'FROZEN-HEAD.txt') + b':= by\n' + read(AUTHOR/'PROOF-BODY.txt') + read(freeze/'FROZEN-CLOSING.txt')
assert len(re.findall(r'^theorem\s+', s, re.M)) == 1
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', s)
assert not re.search(r'^(?:private\s+)?(?:def|lemma|instance|opaque)\s+', s, re.M)

coordinate_count = 0
def coordinates(obj):
    global coordinate_count
    if isinstance(obj, dict):
        if all(k in obj for k in ['raw','charStart0','charEnd0Exclusive','byteStart0','byteEnd0Exclusive']):
            i,j = obj['charStart0'],obj['charEnd0Exclusive']
            bi,bj = obj['byteStart0'],obj['byteEnd0Exclusive']
            raw = obj['raw']
            assert s[i:j] == raw and b[bi:bj] == raw.encode('utf-8')
            assert len(s[:i].encode('utf-8')) == bi and len(s[:j].encode('utf-8')) == bj
            if 'sliceSHA256' in obj:
                assert sha(b[bi:bj]) == obj['sliceSHA256']
            if 'sliceBytes' in obj:
                assert len(b[bi:bj]) == obj['sliceBytes']
            for pos, label in [(i,'start'),(j,'end')]:
                line = s.count('\n',0,pos)+1
                start = s.rfind('\n',0,pos)+1
                col = pos-start+1
                byte_col = len(s[start:pos].encode('utf-8'))+1
                for key,value in [(label+'Line1',line),(label+'ColumnCodepoint1',col),(label+'ColumnUTF8Byte1',byte_col)]:
                    if key in obj: assert obj[key] == value, (key, obj.get('name'), obj[key], value)
            coordinate_count += 1
        if obj.get('sourceSHA256'):
            assert obj['sourceSHA256'] == sha(b)
        for v in obj.values(): coordinates(v)
    elif isinstance(obj,list):
        for v in obj: coordinates(v)

local = jread(AUTHOR/'LOCAL-SOURCE-INVENTORY.json')
proof = jread(AUTHOR/'PROOF-BINDING-INVENTORY.json')
params = jread(AUTHOR/'DECLARATION-PARAMETER-INVENTORY.json')
static = jread(AUTHOR/'STATIC-CHECK.json')
for obj in [local,proof,params,static]: coordinates(obj)
assert len(local['locals']) == 79 and len(proof['binders']) == 42 and len(proof['allProofCommands']) == 15 and len(params['parameters']) == 10
for x in local['locals']:
    assert x['scopeBodyStart0'] == x['source']['charEnd0Exclusive']
    assert x['scopeBodyByteStart0'] == len(s[:x['scopeBodyStart0']].encode('utf-8'))
    assert x['scopeByteEnd0Exclusive'] == len(s[:x['scopeEnd0Exclusive']].encode('utf-8'))
    assert x['scopeBodyStart0'] < x['scopeEnd0Exclusive']
    assert x['fullType'] in x['source']['raw'] and x['fullRHS'] in x['source']['raw']
for x in proof['binders']:
    assert x['scopeEnd0Exclusive'] == s.index('\nend\n')
    assert not x['introducesNewPremise']
for x in params['parameters']:
    assert not x['introducedByAuthor']

old = read(ROOT/'library/Shao/OQ6/OriginalCountablyGeneratedModel.lean').decode('utf-8')
old_head = old[old.index('theorem '):old.index('\n:= by')]
head = read(freeze/'FROZEN-HEAD.txt').decode('utf-8')
old_prefix = old_head[:old_head.index('      (∀ (n : ℕ)')]
new_prefix = head[:head.index('      (∀ (n : ℕ)')]
assert old_prefix.replace('actual_normalized_original_countably_generated_model','actual_original_level_dependent_countably_generated_model') == new_prefix

packet_checks = []
for n, start, end in [(251,'            let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀', '\n        ) ∧'), (252,'            let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀', '\n        ))')]:
    h = read(ROOT/f'drafts/oq56/unit{n}/freeze-01/FROZEN-HEAD.txt').decode('utf-8')
    body = h[h.index('    let g :'):].strip().replace('μ','μ₀')
    offset = 0 if n == 251 else s.index('\n        ) ∧')+1
    a=s.index(start,offset);z=s.index(end,a)
    normal=lambda t: re.sub(r'\s+',' ',t).strip()
    assert normal(body) == normal(s[a:z])
    packet_checks.append(dict(unit=n, wholeResultPreserved=True, onlySubstitution='μ→μ₀ plus whitespace', charStart0=a, charEnd0Exclusive=z))

release = jread(AUTHOR/'FINALWRITE.json')
assert release['FINALWRITE'] and release['noFurtherWrites'] and all(v==0 for v in release['sixZero'].values())
assert fp(AUTHOR/'STATIC-FAILURE-001-PREIMAGE.py.txt')['sha256'] == 'b85e70cdc0d17467ecc85dee0604db2a6b49d177edc7e071a2d15bce2e570b35'

result=dict(schema='unit253-independent-source-byte-binding-check-v1',atUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',source=fp(source_path),sourceCompositionExact=True,oldCorePrefixExact=True,packetComparisons=packet_checks,sourceCoordinateRoundTrips=coordinate_count,localCount=79,proofBinderCount=42,proofCommandCount=15,originalParameterCount=10,actualOwnerCount=None,actualOwnerCountPendingMachine=True,allReferencedExistingLocalBindingsVerified=len(seen),bindings=list(seen.values()),authorReleaseSixZeroVerified=True,staticFailurePreserved=True,LeanExecuted=False,qualified=False,machinePending=True,fullOQ56='OPEN')
(OUT/'SOURCE-BINDING-CHECK.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({k:v for k,v in result.items() if k!='bindings'},ensure_ascii=False))
