from pathlib import Path
import hashlib,json
out=Path('C:/game/shao lean/drafts/oq56/unit257/author-01')
freeze=out.parent/'freeze-01'
proof=(out/'PROOF-BODY.txt').read_bytes()
assert b'\r' not in proof
source=(freeze/'FROZEN-PREAMBLE.txt').read_bytes()+(freeze/'FROZEN-HEAD.txt').read_bytes()+b':= by\n'+proof+(freeze/'FROZEN-CLOSING.txt').read_bytes()
assert b'\r' not in source and source.endswith(b'\n') and not source.endswith(b'\n\n')
assert not source.startswith(b'\xef\xbb\xbf')
p=out/'OriginalLevelDependentStrictMomentFrontier.lean'
p.write_bytes(source)
print(json.dumps({'path':p.as_posix(),'sha256':hashlib.sha256(source).hexdigest(),'bytes':len(source),'LF':source.count(b'\n'),'proofLF':proof.count(b'\n')},ensure_ascii=False))
