"""Generate the public-theorem coverage list from this project's Lean source layout."""
from pathlib import Path
import re,sys
root=Path(__file__).resolve().parents[1]
names=[]
for path in sorted((root/'Shao').rglob('*.lean')):
    text=path.read_text()
    # Project declaration headers are at column zero. Remove block comments first.
    text=re.sub(r'/\-.*?\-/', '', text, flags=re.S)
    scopes=[]
    for line in text.splitlines():
        line=line.split('--',1)[0].rstrip()
        match=re.fullmatch(r'namespace (\S+)',line)
        if match:
            scopes.append(('namespace',match[1]));continue
        match=re.fullmatch(r'(?:noncomputable )?section(?: (\S+))?',line)
        if match:
            scopes.append(('section',match[1] or ''));continue
        match=re.fullmatch(r'end(?: (\S+))?',line)
        if match:
            if not scopes:raise RuntimeError(f'Unmatched scope end: {path}: {line}')
            kind,label=scopes.pop()
            if match[1] and match[1]!=label:raise RuntimeError(f'Scope mismatch: {path}: {line}')
            continue
        match=re.match(r'^(?:@\[[^\n]*\]\s*)?(?:public )?theorem\s+(\S+)',line)
        if match:
            namespace='.'.join(s[1] for s in scopes if s[0]=='namespace')
            if not namespace.startswith('Shao'):raise RuntimeError(f'Unexpected namespace in {path}')
            names.append(namespace+'.'+match[1])
    # A file-level anonymous section may intentionally stay open to EOF.
    if any(k=='namespace' or v for k,v in scopes):raise RuntimeError(f'Unclosed named scopes: {path}')
if len(set(names))!=len(names) or not names:raise RuntimeError('Duplicate or empty declaration list')
out=root/'verification/expected-public-theorems.txt'
content='\n'.join(sorted(names))+'\n'
if '--check' in sys.argv:
    if not out.exists() or out.read_text()!=content:raise SystemExit('Public theorem manifest is stale')
else:
    out.write_text(content)
print(f'PUBLIC_THEOREMS {len(names)}')
