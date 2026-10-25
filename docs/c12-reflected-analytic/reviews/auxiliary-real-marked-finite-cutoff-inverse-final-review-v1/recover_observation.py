import json,hashlib
from pathlib import Path
r=Path(__file__).parent;p=r/'remote-observation-failure.json';v=json.loads(p.read_text(encoding='utf-8'));s=v['stdout'];a=s.index('OBSERVATION_JSON ')+len('OBSERVATION_JSON ');z=s.index('\nKERNEL002_FULL',a);obs=json.loads(s[a:z]);(r/'remote-observations.json').write_text(json.dumps(obs,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
logStart=s.index('KERNEL002_FULL');logEnd=s.index('NATIVE_CONTRACTS');logs=s[logStart:logEnd];print(logs)
nativeStart=logEnd+len('NATIVE_CONTRACTS\n');nativeEnd=s.index('\nORIGINAL_SOURCE',nativeStart);native=json.loads(s[nativeStart:nativeEnd]);original=s[nativeEnd+1:]
(r/'native-contract-excerpts.json').write_text(json.dumps(native,ensure_ascii=False,indent=2)+'\n',encoding='utf-8');(r/'original-source-excerpt.txt').write_text(original+'\n',encoding='utf-8')
p.write_text(json.dumps({'status':'TRANSPORT_RESPONSE_ADAPTER_CORRECTED_NO_REMOTE_CHECK_FAILURE','exit_code':v['exit_code'],'reason':'Success schema uses exit_code/stdout, not ok=true. Original read-only command succeeded; reused saved response without replay. Raw logs removed from local adapter diagnostic; remain at original remote paths.','remoteStdoutSHA256':hashlib.sha256(s.encode()).hexdigest()},indent=2)+'\n',encoding='utf-8')
print('COMPACT_OBSERVATION',json.dumps({k:v for k,v in obs.items() if k!='bindings'},ensure_ascii=False))
print(original)
