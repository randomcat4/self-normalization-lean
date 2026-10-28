from pathlib import Path
import hashlib, json
from datetime import datetime, timezone

out=Path('C:/game/shao lean/drafts/oq56/unit256/author-01')
dst=out/'preserved-freeze01'
assert not dst.exists()
dst.mkdir()
payload=[]
for path in sorted(out.iterdir()):
    if not path.is_file() or path.name=='preserve_freeze01.py': continue
    b=path.read_bytes(); target=dst/path.name
    target.write_bytes(b)
    payload.append({'path':target.as_posix(),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)})
record={'schema':'unit256-freeze01-candidate-preservation-before-parent-syntax-fix-v1',
 'atUTC':datetime.now(timezone.utc).isoformat(),
 'parentInstruction':'Preserve freeze01 candidate and all current payload bytes before frozen preamble-only symmDiff repair.',
 'sourceSHA256':'556ba5b0dc475e4881e3e91a774b2f22961bd3526683b6356ae1c3061f9598a1',
 'proofUnchanged':True,'oldFreezeDirectoryUntouched':True,'payload':payload,
 'machineChecks':0,'qualified':False,'machinePending':True}
(dst/'PRESERVATION.json').write_bytes((json.dumps(record,ensure_ascii=False,indent=2)+'\n').encode())
print(json.dumps({'preservedPayloads':len(payload),'sourceSHA256':record['sourceSHA256']}))
