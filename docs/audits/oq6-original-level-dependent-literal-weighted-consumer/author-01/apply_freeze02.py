from pathlib import Path
import hashlib,json
from datetime import datetime,timezone

root=Path('C:/game/shao lean'); out=root/'drafts/oq56/unit256/author-01'
oldfreeze=root/'drafts/oq56/unit256/freeze-01'; newfreeze=root/'drafts/oq56/unit256/freeze-02'
def binding(p):
    b=p.read_bytes(); return {'path':p.as_posix(),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'LF':b.count(b'\n')}
oldpre=(oldfreeze/'FROZEN-PREAMBLE.txt').read_bytes()
newpre=(newfreeze/'FROZEN-PREAMBLE.txt').read_bytes()
assert len(oldpre)==390 and len(newpre)==399
assert newpre==oldpre.replace(b'open scoped BigOperators Classical Topology MeasureTheory\n',
 b'open scoped BigOperators Classical Topology MeasureTheory symmDiff\n')
for name in ['FROZEN-HEAD.txt','FROZEN-CLOSING.txt','SOURCE-ROUTE.md']:
    assert (oldfreeze/name).read_bytes()==(newfreeze/name).read_bytes(),name
src=out/'OriginalLevelDependentLiteralWeightedConsumer.lean'; before=src.read_bytes()
assert hashlib.sha256(before).hexdigest()=='556ba5b0dc475e4881e3e91a774b2f22961bd3526683b6356ae1c3061f9598a1'
assert before==(out/'preserved-freeze01'/src.name).read_bytes()
proof=(out/'PROOF-BODY.txt').read_bytes()
assert proof==(out/'preserved-freeze01/PROOF-BODY.txt').read_bytes()
assert before.startswith(oldpre)
after=newpre+before[len(oldpre):]
assert after[len(newpre):]==before[len(oldpre):]
src.write_bytes(after)
afterbind=binding(src)
for name in ['REPORT.md','ROUTE.md']:
    p=out/name; s=p.read_text(encoding='utf-8')
    s=s.replace('556ba5b0dc475e4881e3e91a774b2f22961bd3526683b6356ae1c3061f9598a1',afterbind['sha256'])
    s=s.replace('66798B','66807B')
    s=s.replace('freeze dfe7d5d3…/1924B及ACTIVATION b195f098…/1754B精确绑定已核。',
      '当前freeze-02 c2f06d7e…/2368B及ACTIVATION55931ff3…/2622B精确绑定已核；仅父显式修正前言symmDiff作用域，474LF数学head及完整证明未变，freeze-01与原候选另存。')
    if name=='REPORT.md':
        s += '\n## 父显式冻结前言语法修正\n\n完整首包中使用∆，作者发现freeze-01前言没有显式open scoped symmDiff；父在任何首次Lean检查前制作freeze-02，只将前言390B改为399B。AMENDMENT df7154dcad4a40958209d134e5e51dac350e84fd59a5c1a32bd9f0eeb15bbb32/2145B明确授权同一作者更换此前缀。474LF head、closing和route逐字相同，原source完整后缀和561LF proof均逐字不变。原候选556ba5b0dc475e4881e3e91a774b2f22961bd3526683b6356ae1c3061f9598a1/66798B及当时15个payload保存在preserved-freeze01，父的preamble-amendment-01也保留独立原件；所有原失败保持。无数学前提修改、无新模型/上下文、无机器检查。FROZEN-PREAMBLE当前a52e8a0b63b5dcc2e85e5d83512c5d25d821a6c47d82564a200a78ac0f2d3bf8/399B。此修正及精确suffix比较记录于PREAMBLE-AMENDMENT-APPLIED.json。\n'
    p.write_bytes(s.encode('utf-8'))
record={'schema':'unit256-author-applied-parent-preamble-only-amendment-v1','atUTC':datetime.now(timezone.utc).isoformat(),
 'parentAmendment':binding(root/'drafts/oq56/unit256/preamble-amendment-01/AMENDMENT.json'),
 'oldCandidate':binding(out/'preserved-freeze01'/src.name),'newCandidate':afterbind,
 'proof':binding(out/'PROOF-BODY.txt'),'oldPreamble':binding(oldfreeze/'FROZEN-PREAMBLE.txt'),
 'newPreamble':binding(newfreeze/'FROZEN-PREAMBLE.txt'),'suffixExactlyUnchanged':True,
 'proofExactlyUnchanged':True,'all474HeadLFExactlyUnchanged':True,'oldFreezeEdits':0,'proofChanges':0,
 'mathAssumptionChanges':0,'LeanServerNetworkOperations':0}
(out/'PREAMBLE-AMENDMENT-APPLIED.json').write_bytes((json.dumps(record,ensure_ascii=False,indent=2)+'\n').encode())
print(json.dumps(afterbind))
