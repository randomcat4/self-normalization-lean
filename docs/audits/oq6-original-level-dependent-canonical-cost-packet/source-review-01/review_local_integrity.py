from pathlib import Path
import json, hashlib, re
from datetime import datetime, timezone

BASE = Path('C:/game/shao lean/drafts/oq56/unit255')
OUT = BASE / 'source-review-01'
AUTHOR = BASE / 'author-01'
FREEZE = BASE / 'freeze-01'
SOURCE = AUTHOR / 'OriginalLevelDependentCanonicalCostPacket.lean'
def sha(b):
    return hashlib.sha256(b).hexdigest()
def readj(p):
    return json.loads(Path(p).read_text(encoding='utf-8'))
def binding(p):
    p=Path(p); b=p.read_bytes()
    return dict(path=p.as_posix(), sha256=sha(b), bytes=len(b))
def check_binding(o):
    b=Path(o['path']).read_bytes()
    assert len(b)==o['bytes'] and sha(b)==o['sha256'], o['path']
    return binding(o['path'])
def dump(name, o):
    (OUT/name).write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')

b=SOURCE.read_bytes(); s=b.decode('utf-8',errors='strict')
assert sha(b)=='a2db2c096e444b9ddd63fe4ff0baa451a0d2b834cb5c9049998cee2eeeb18989'
assert len(b)==38774 and b.count(b'\n')==671 and b'\r' not in b
assert not b.startswith(b'\xef\xbb\xbf') and b.endswith(b'\n') and not b.endswith(b'\n\n')
freeze=readj(FREEZE/'frozen-declaration.json')
for k in ('preamble','head','closing','route','oldAcceptedSource','bearing254Candidate','bearing250Qualified','bearing252Qualified'):
    check_binding(freeze[k])
proof=(AUTHOR/'PROOF-BODY.txt').read_bytes()
assert b==(FREEZE/'FROZEN-PREAMBLE.txt').read_bytes()+(FREEZE/'FROZEN-HEAD.txt').read_bytes()+b':= by\n'+proof+(FREEZE/'FROZEN-CLOSING.txt').read_bytes()
assert proof.count(b'\n')==373
head=(FREEZE/'FROZEN-HEAD.txt').read_text(encoding='utf-8')
source254=Path(freeze['bearing254Candidate']['path']).read_text(encoding='utf-8')
core_start='        @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ ∧'
core_end='          |P.real (A0 R z) - ν.real (Eη R z)| ≤ p0)'
def core(t):
    i=t.index(core_start); j=t.index(core_end,i)+len(core_end)
    return t[i:j]
assert core(head)==core(source254)
for p in (BASE/'parent-author-source-intake-01.json',BASE/'parent-qualified250-version-alignment.json'):
    readj(p)
inv=readj(AUTHOR/'SOURCE-INVENTORY.json')
prod=readj(AUTHOR/'PRODUCER-BINDINGS.json')
types=readj(AUTHOR/'PRODUCER-TYPES.json')
assert inv['sourceSHA256']==sha(b) and prod['sourceSHA256']==sha(b)
counts={k:sum(r['kind']==k for r in inv['records']) for k in ('let','letI','have')}
assert counts==dict(let=78,letI=4,have=68)
checks=[]
for entry in [r['sourceSlice'] for r in inv['records']]+[r['producerSlice'] for r in prod['records']]:
    piece=b[entry['startByte0']:entry['endByteExclusive']]
    assert piece==entry['text'].encode('utf-8') and sha(piece)==entry['sha256']
    assert b[:entry['startByte0']].count(b'\n')+1==entry['startLine']
    assert entry['endLineInclusive']==entry['startLine']+piece.count(b'\n')-1
    checks.append(dict(startLine=entry['startLine'],endLine=entry['endLineInclusive'],sha256=entry['sha256']))
assert len(checks)==168 and len(prod['records'])==18
assert sum(len(r['bindings']) for r in prod['records'])==164
assert len(types['qualified254CurrentContract'])==43
assert len(types['qualified252Lets'])==24 and len(types['qualified250Lets'])==16
assert len(types['qualified252ExpandedConjuncts'])==29 and len(types['qualified250ExpandedConjuncts'])==5
for r in inv['records']:
    assert r['fullType'] and r['fullRHS'] and r['scope']
for r in prod['records']:
    for v in r['bindings']:
        assert v['fullDependentType'] and v['fullSourceBindingCommand']==r['producerSlice']['text']
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',s)
assert len(re.findall(r'^theorem ',s,re.M))==1
assert not re.search(r'^(?:private\s+)?(?:def|instance|lemma|abbrev|opaque|axiom)\b',s,re.M)
manifest=readj(AUTHOR/'MANIFEST.json')
assert len(manifest['payloads'])==manifest['payloadCount']==17
verified=[check_binding(x) for x in manifest['payloads']]
release=readj(AUTHOR/'FINALWRITE.json')
assert all(release[k]==0 for k in ('writers','heavy','inflight','pendingExternal','children','uncertain'))
for k in ('source','manifest','authorReport','staticCheck','integrityCheck'):
    check_binding(release[k])
activation=readj(FREEZE/'ACTIVATION.json')
for k in ('freeze','qualified254','independent254FinalRelease','exactPredecessorSource'):
    check_binding(activation[k])
upstream=[]
for unit in (250,252,254):
    qpath=BASE.parent/f'unit{unit}'/'qualified-evidence.json'
    q=readj(qpath)
    assert q['qualified'] is True
    for k in ('source','independentFinalReport','independentFinalVerdict','independentFinalRelease'):
        upstream.append(check_binding(q[k]))
    upstream.append(binding(qpath))
author_input_checks=[]
for v in readj(AUTHOR/'INPUT-HASH-BINDINGS.json'):
    current=binding(v['path'])
    author_input_checks.append(dict(**current, archivedExpectedSHA256=v['sha256'],matchesArchived=(current['sha256']==v['sha256'] and current['bytes']==v['bytes'])))
assert all(v['matchesArchived'] for v in author_input_checks)
audit=dict(schema='unit255-independent-source-byte-review-v1',atUTC=datetime.now(timezone.utc).isoformat(),source=binding(SOURCE),status='PASS_STATIC_ONLY_NOT_A_MATHEMATICAL_VERDICT',frozenComposition=True,canonical254LiteralCorePreserved=True,UTF8NoBOM=True,LF=671,headLF=276,proofLF=373,sourceLocalCounts=counts,sourceSlicesRoundtrip=len(checks),producerCommands=18,producerBindings=164,canonicalCoreConjuncts=43,producer252ExpandedConjuncts=29,producer250ExpandedConjuncts=5,author17ManifestPayloadsVerified=True,authorReleaseSixZero=True,authorInputBindingsVerified=len(author_input_checks),acceptedOldEvidenceReusedWithoutNewTYPEProofAXRuns=True,qualified=False,machinePending=True)
dump('SOURCE-INTEGRITY-CHECK.json',audit)
inputs=[binding(p) for p in [SOURCE,*FREEZE.glob('*'),AUTHOR/'MANIFEST.json',AUTHOR/'FINALWRITE.json',AUTHOR/'AUTHOR-REPORT.md',AUTHOR/'SOURCE-ROUTE.md',AUTHOR/'SOURCE-INVENTORY.json',AUTHOR/'PRODUCER-BINDINGS.json',AUTHOR/'PRODUCER-TYPES.json',AUTHOR/'LOCAL-READ-FAILURE-01.json',BASE/'parent-author-source-intake-01.json',BASE/'parent-qualified250-version-alignment.json'] if p.is_file()]
dump('SOURCE-HASH-BINDINGS.json',dict(readBindings=inputs+upstream,authorManifestPayloadBindings=verified,authorArchivedInputBindings=author_input_checks))
print(json.dumps(audit,ensure_ascii=False))
