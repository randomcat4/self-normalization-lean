import sys
sys.dont_write_bytecode = True
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('C:/game/shao lean')
REVIEW = ROOT / 'drafts/c12-lane/auxiliary-unmarked-paid-cauchy-final-review-v1'
AUTHOR = ROOT / 'drafts/c12-lane/auxiliary-unmarked-paid-cauchy-v1'
REMOTE = '/root/rivermind-data/shao-lean-20261021'
WT = REMOTE + '/workspaces/c12-bridge-domination-v71'
OUT = REMOTE + '/outputs/c12-auxiliary-unmarked-paid-cauchy-v71'
sys.path.insert(0, str(ROOT / 'tools'))
from transport_client import send_request

def sha(data):
    return hashlib.sha256(data).hexdigest()

def write(name, data):
    (REVIEW / name).write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n', encoding='utf-8', newline='\n')

DEPENDENCIES = {
    '175': ('auxiliary-unmarked-damped-moments-v1', 'AuxiliaryUnmarkedDampedMoments.lean', 'auxiliary-higher-mark-damped-final-review-v1'),
    '176': ('auxiliary-third-moment-truncation-v1', 'AuxiliaryThirdMomentTruncation.lean', 'auxiliary-third-moment-truncation-final-review-v1'),
    '173': ('auxiliary-unmarked-block-real-cauchy-v1', 'AuxiliaryUnmarkedBlockRealCauchy.lean', 'auxiliary-real-rare-split-cauchy-final-review-v1'),
}

def dependency_bindings():
    rows = {}
    remote = {}
    for unit, (folder, filename, review_folder) in DEPENDENCIES.items():
        directory = ROOT / 'drafts/c12-lane' / folder
        receipt_path = directory / 'receipt.json'
        receipt = json.loads(receipt_path.read_text(encoding='utf-8'))
        review_data = (ROOT / 'drafts/c12-lane' / review_folder / 'full-review.json').read_text(encoding='utf-8')
        assert receipt['sourceSHA256'] in review_data and receipt['objectSHA256'] in review_data, unit
        local = {}
        for fname in [filename, 'frozen.lean.txt', 'actual-owned-types.txt', 'receipt.json']:
            p = directory / fname
            b = p.read_bytes()
            local[str(p)] = {'sha256': sha(b), 'bytes': len(b)}
        assert local[str(directory / filename)]['sha256'] == receipt['sourceSHA256']
        assert local[str(directory / 'frozen.lean.txt')]['sha256'] == receipt['frozenSHA256']
        assert local[str(directory / 'actual-owned-types.txt')]['sha256'] == receipt['allTypesComplete']['sha256']
        for fname, info in receipt.get('artifacts', {}).items():
            if fname in ['frozen.lean.txt', 'actual-owned-types.txt', 'owned-audit.json', 'OwnedAudit.lean']:
                remote[info['remotePath']] = {'sha256': info['sha256'], 'bytes': info['bytes']}
        typeinfo = receipt['allTypesComplete']
        remote[typeinfo['path']] = {'sha256': typeinfo['sha256'], 'bytes': typeinfo['bytes']}
        rows[unit] = {'module': receipt['module'], 'sourceSHA256': receipt['sourceSHA256'], 'objectSHA256': receipt['objectSHA256'], 'receiptSHA256': sha(receipt_path.read_bytes()), 'frozenSHA256': receipt['frozenSHA256'], 'localFiles': local, 'completeQualifiedReviewJSONBindsExactSourceAndObject': True, 'qualifiedProofReviewReused': True}
    return rows, remote

def local():
    receipt = json.loads((AUTHOR / 'receipt.json').read_text(encoding='utf-8'))
    frozen = (AUTHOR / 'frozen.lean.txt').read_text(encoding='utf-8')
    source = (AUTHOR / 'AuxiliaryUnmarkedPaidCauchy.lean').read_text(encoding='utf-8')
    lines = source.splitlines(keepends=True)
    reconstructed = []
    inside = False
    for line in lines:
        if line.startswith('theorem '):
            inside = True
        if not inside or line.startswith('theorem '):
            reconstructed.append(line)
        elif inside:
            reconstructed.append(line)
        if inside and line.rstrip().endswith(':= by'):
            inside = False
            # Consume proof separately until the next theorem or final namespace end.
            break
    # Reconstruct context and each complete theorem declaration, excluding proof bodies.
    heads = list(re.finditer(r'^theorem .*?:= by\n', source, re.M | re.S))
    header = source[:source.index('theorem ')]
    declarations = []
    for part in re.split(r'(?m)^theorem ', source)[1:]:
        declarations.append('theorem ' + part[:part.index(':= by') + len(':= by')] + '\n')
    reconstruction = header + '\n'.join(declarations) + '\nend Shao.C2.AuxiliaryUnmarkedPaidCauchy\n'
    assert reconstruction == frozen, 'Complete context/head freeze differs'
    local_rows = {}
    for p in sorted(AUTHOR.iterdir()):
        if p.is_file():
            b = p.read_bytes()
            local_rows[str(p)] = {'sha256': sha(b), 'bytes': len(b)}
    assert local_rows[str(AUTHOR / 'AuxiliaryUnmarkedPaidCauchy.lean')]['sha256'] == receipt['sourceSHA256']
    assert local_rows[str(AUTHOR / 'frozen.lean.txt')]['sha256'] == receipt['frozenSHA256']
    assert receipt['wholeOwnedCount'] == 2 and receipt['wholeTheoremCount'] == 2 and receipt['wholeNonTheoremCount'] == 0
    raw = (AUTHOR / 'AuxiliaryUnmarkedPaidCauchy.lean').read_bytes()
    assert not raw.startswith(b'\xef\xbb\xbf') and b'\r' not in raw
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', source)
    qual = {}
    known = {
        '175': ('auxiliary-higher-mark-damped-final-review-v1', '825d93799a5b2b6dd53cf10c946bcef621d1997ad2cf1dbe54a633487417adac'),
        '176': ('auxiliary-third-moment-truncation-final-review-v1', 'd87ac18fc5b4627c893f363f7f489c2846da66c950da2d8db4c18ee0cfa9a227'),
        '173': ('auxiliary-real-rare-split-cauchy-final-review-v1', '8b6028e607ec8de899b76e5d527b4279b2a5c33c84591cd509a00dabc28b1c94'),
    }
    for unit, (folder, expected) in known.items():
        directory = ROOT / 'drafts/c12-lane' / folder
        parent = directory / 'parent-acceptance.json'
        assert sha(parent.read_bytes()) == expected
        data = json.loads(parent.read_text(encoding='utf-8'))
        fields = {'fullReviewJSONSHA256': 'full-review.json', 'fullReviewMDSHA256': 'full-review.md', 'validationSHA256': 'validation.json'}
        fields['reviewReleaseSHA256' if unit == '175' else 'writerReleaseSHA256'] = 'RELEASE.json' if unit == '175' else 'writer-release.json'
        rows = {}
        for field, filename in fields.items():
            p = directory / filename
            b = p.read_bytes()
            assert sha(b) == data[field], str(p)
            rows[str(p)] = {'sha256': sha(b), 'bytes': len(b)}
        qual[unit] = {'parentPath': str(parent), 'parentSHA256': expected, 'status': data['status'], 'sealedReviewBindings': rows}
    paper = {}
    for filename, expected in [('main.tex', 'beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06'), ('supplement.tex', 'b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd')]:
        p = Path('C:/game/shao/current/c12') / filename
        b = p.read_bytes()
        assert sha(b) == expected
        paper[str(p)] = {'sha256': sha(b), 'bytes': len(b)}
    result = {'status': 'PASS', 'atUTC': datetime.now(timezone.utc).isoformat(), 'authorFiles': local_rows, 'qualifiedEvidence': qual, 'sourcePaper': paper, 'completeContextHeadsFreezeReconstruction': True, 'UTF8NoBOMLF': True, 'forbiddenTermsAbsent': True}
    dependencies, remote = dependency_bindings()
    result['consumedDependencies'] = dependencies
    result['remoteDependencyEvidenceExpected'] = remote
    write('local-evidence-bindings.json', result)
    print(json.dumps({'status': 'PASS', 'authorFiles': len(local_rows), 'qualifiedParents': list(qual), 'qualifiedSeals': sum(len(q['sealedReviewBindings']) for q in qual.values()), 'paperSources': len(paper), 'freezeContextHeadsExact': True}, indent=2))

def remote(mode):
    receipt = json.loads((AUTHOR / 'receipt.json').read_text(encoding='utf-8'))
    preflight = json.loads((AUTHOR / 'preflight-observation.json').read_text(encoding='utf-8'))
    expected = {p: dict(info) for p, info in preflight['bindings'].items()}
    for filename, info in receipt['artifacts'].items():
        expected[info['remotePath']] = {'sha256': info['sha256'], 'bytes': info['bytes']}
    dependencies, dependency_remote = dependency_bindings()
    expected.update(dependency_remote)
    for path in [WT + '/Shao/C2/AuxiliaryUnmarkedPaidCauchy.lean']:
        expected[path] = {'sha256': receipt['sourceSHA256']}
    for path in [WT + '/.lake/build/lib/lean/Shao/C2/AuxiliaryUnmarkedPaidCauchy.olean', OUT + '/AuxiliaryUnmarkedPaidCauchy.olean']:
        expected[path] = {'sha256': receipt['objectSHA256']}
    code = """import json,hashlib,subprocess,datetime
from pathlib import Path
expected=json.loads(EXPECTED)
rows={}
fail=[]
for name,e in expected.items():
 p=Path(name)
 if not p.is_file():
  rows[name]={'exists':False};fail.append(name);continue
 b=p.read_bytes();a={'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)};rows[name]=a
 if any(a.get(k)!=v for k,v in e.items()):fail.append(name)
wt=WT
git=lambda *args:subprocess.check_output(['git','-C',wt,*args],text=True).strip()
out=Path(OUT)
log=(out/'owned-audit.log').read_text()
typ=(out/'actual-owned-types.txt').read_text()
start=log.index('TARGET_DECL ')
end=log.index('info: AUDITED_TARGET_CONSTANTS') if 'info: AUDITED_TARGET_CONSTANTS' in log else log.index('AUDITED_TARGET_CONSTANTS')
portion=log[start:end]
# Actual export is the complete TARGET_DECL/ACTUAL_TYPE blocks without log metadata.
print(json.dumps({'status':'PASS' if not fail else 'FAIL','atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'bindings':rows,'failures':fail,'branch':git('branch','--show-current'),'HEAD':git('rev-parse','HEAD'),'tree':git('rev-parse','HEAD^{tree}'),'auditLogPrefix':log[:start],'auditLogSuffix':log[end:],'auditTypesBytes':len(typ.encode()),'logBytes':len(log.encode()),'rawTypeBlocksMatch':typ.strip()==portion.strip(),'typeBlockBoundary':{'portionBytes':len(portion.encode()),'typeBytes':len(typ.encode()),'exactEqual':portion==typ,'portionAfterType':portion[len(typ):] if portion.startswith(typ) else None},'attemptDirectories':sorted(p.name for p in out.glob('attempt*') if p.is_dir()),'leanToolchain':Path(wt+'/lean-toolchain').read_text().strip(),'mathlibHEAD':subprocess.check_output(['git','-C',wt+'/.lake/packages/mathlib','rev-parse','HEAD'],text=True).strip(),'expectedAbsentCommonSources':{n: not Path(wt+'/'+n).exists() for n in ['Shao/Probability/SourceSuffixScalarInterfaces.lean','Shao/Probability/SourceSuffixMomentBudgets.lean']},'kernelLog':(out/'attempt001/kernel.log').read_text(),'kernelCommand':(out/'attempt001/command.txt').read_text(),'kernelExit':(out/'attempt001/exit.json').read_text(),'auditCommand':(out/'audit-command.txt').read_text(),'auditExit':(out/'audit-exit.json').read_text()},ensure_ascii=False))
"""
    code = 'EXPECTED=' + repr(json.dumps(expected)) + '\nWT=' + repr(WT) + '\nOUT=' + repr(OUT) + '\n' + code
    result = send_request({'action': 'exec', 'command': 'python3 -', 'stdin': code, 'timeout': 60})
    if not result.get('ok', True):
        print(json.dumps(result)); return
    if result.get('exit_code', result.get('exitCode', 0)) != 0:
        print(json.dumps(result)); return
    observation = json.loads(result['stdout'])
    write('readonly-' + mode + '-observation.json', observation)
    print(json.dumps({k: v for k, v in observation.items() if k != 'bindings'}, ensure_ascii=False, indent=2))
    print('Binding count:', len(observation['bindings']))

if __name__ == '__main__':
    if sys.argv[1] == 'local': local()
    elif sys.argv[1] in ['server', 'final']: remote(sys.argv[1])
    elif sys.argv[1] in ['native', 'native-extra']:
        code = r'''import json,hashlib,subprocess
from pathlib import Path
wt=Path('/root/rivermind-data/shao-lean-20261021/workspaces/c12-bridge-domination-v71')
ml=wt/'.lake/packages/mathlib'
patterns='(?:theorem|lemma) (?:sqrt_sq_eq_abs|sq_sqrt|sqrt_le_sqrt|sqrt_pos|sqrt_nonneg|exp_nat_mul|rpow_mul|rpow_natCast|rpow_nonneg)\\b'
import re
found=[]
for rel in ['Mathlib/Analysis/SpecialFunctions/Pow/Real.lean','Mathlib/Analysis/SpecialFunctions/Exp.lean','Mathlib/Data/Real/Sqrt.lean','Mathlib/Data/Complex/Exponential.lean']:
 p=ml/rel
 if p.is_file() and re.search(patterns,p.read_text()):found.append(str(p))
if EXTRA:
 found=[]
 for glob in ['*Sqrt*.lean','*Exponential*.lean','Exp.lean']:
  for p in (ml/'Mathlib').rglob(glob):
   if re.search(patterns,p.read_text()) and str(p) not in found:found.append(str(p))
records=[]
for filename in found:
 p=Path(filename);rel=str(p.relative_to(ml));b=p.read_bytes()
 pinned=subprocess.check_output(['git','-C',str(ml),'show','807d3836b165983210ee2ecf3cd28f239436949c:'+rel])
 lines=b.decode().splitlines();ranges=[]
 import re
 for i,line in enumerate(lines):
  if re.search(patterns,line):
   lo=max(0,i-2);hi=min(len(lines),i+9)
   ranges.append({'lines':[lo+1,hi],'text':'\n'.join(str(j+1)+': '+lines[j] for j in range(lo,hi))})
 records.append({'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'pinnedBlobSHA256':hashlib.sha256(pinned).hexdigest(),'workingEqualsPinned':b==pinned,'ranges':ranges})
extra=[]
for filename in ([] if EXTRA else [str(wt/'Shao/Basic/FinitePath.lean'),'/root/rivermind-data/shao-lean-20261021/toolchains/elan/toolchains/leanprover--lean4---v4.36.0-rc1/src/lean/Lean/Util/CollectAxioms.lean']):
 p=Path(filename);b=p.read_bytes();lines=b.decode().splitlines()
 if p.name=='FinitePath.lean':
  chosen=[(1,60)]
 else:chosen=[(1,len(lines))]
 extra.append({'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'ranges':[{'lines':[lo,hi],'text':'\n'.join(str(j)+': '+lines[j-1] for j in range(lo,hi+1))} for lo,hi in chosen]})
print(json.dumps({'native':records,'extra':extra},ensure_ascii=False))
'''
        code = 'EXTRA=' + repr(sys.argv[1] == 'native-extra') + '\n' + code
        result = send_request({'action':'exec','command':'python3 -','stdin':code,'timeout':60})
        if result.get('ok', True) and result.get('exit_code', result.get('exitCode', 0)) == 0:
            data=json.loads(result['stdout']);write('native-extra-interface-observation.json' if sys.argv[1] == 'native-extra' else 'native-interface-observation.json',data)
            print(json.dumps(data,ensure_ascii=False,indent=2))
        else:
            write('native-read-failure.json',result)
            print(json.dumps(result))
