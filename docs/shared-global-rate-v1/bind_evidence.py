"""Bind final source, exact frozen declarations, target and module-owner audit."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

doc = Path(__file__).resolve().parent
worktree = doc.parents[1]
source_path = worktree / 'Shao/Probability/BivariateLegendre.lean'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
source = source_path.read_text(encoding='utf-8')
parts = source.split('\n\ntheorem ')
assert len(parts) == 5
prefix = re.sub(r'/\-!\n.*?\-/\n\n', '', parts[0], flags=re.S).rstrip()
blocks = [prefix + '\n\nend Shao.Probability']
blocks.extend('theorem ' + p.split(' := by', 1)[0] for p in parts[1:])
actual_snapshot = ('\n\n'.join(blocks) + '\n').encode('utf-8')
frozen = doc / 'frozen-declarations-v1.txt'
assert actual_snapshot == frozen.read_bytes(), 'Frozen source declaration text changed'
assert sha(frozen) == '0b2bafc5965881e4ada01f8ebbeafc8d705ffc78980db711a29fd93dc10d8b81'
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', source)
assert not re.search(r'^import Shao\.OQ3', source, flags=re.M)
assert sha(source_path) == sha(doc / 'attempts/target-03.lean')
assert sha(doc / 'Audit.lean') == sha(doc / 'attempts/audit-02.lean')
assert (doc / 'attempts/target-03.exit.txt').read_text().strip() == '0'
assert (doc / 'attempts/audit-02.exit.txt').read_text().strip() == '0'
audit = (doc / 'attempts/audit-02.stdout.log').read_text(encoding='utf-8')
assert 'error:' not in audit and 'warning:' not in audit
assert '...' not in audit and '⋯' not in audit
declarations = re.findall(r'^OWNED_DECL (.+)$', audit, flags=re.M)
assert len(declarations) == 7 and len(set(declarations)) == 7
assert len(re.findall(r'^TYPE ', audit, flags=re.M)) == 7
assert len(re.findall(r'^LEVEL_PARAMS ', audit, flags=re.M)) == 7
assert len(re.findall(r'^AXIOMS ', audit, flags=re.M)) == 7
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for atoms in re.findall(r'^AXIOMS \[(.*?)\]$', audit, flags=re.M):
    assert set(atoms.split(', ')) <= allowed
expected_counts = {
    'BIVARIATE_FROZEN_DEFINITIONS': 3,
    'BIVARIATE_PUBLIC_THEOREMS': 4,
    'BIVARIATE_ALL_THEOREMS': 4,
    'BIVARIATE_ALL_MODULE_OWNED_CONSTANTS': 7,
}
for key, count in expected_counts.items():
    assert f'{key} {count}\n' in audit
assert 'BIVARIATE_MODULE_OWNER_AXIOM_GATE PASS\n' in audit
(doc / 'actual-declarations.txt').write_text(audit, encoding='utf-8', newline='\n')
(doc / 'source-declarations-v1.txt').write_bytes(actual_snapshot)
git = lambda *args: subprocess.check_output(['git', '-C', str(worktree), *args], text=True).strip()
base = 'ded5b45059cf80861712f61c86170243d5e87fc2'
assert git('merge-base', base, 'HEAD') == base
assert git('branch', '--show-current') == 'feat/shared-bivariate-legendre-v1'
for path in ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'Shao.lean']:
    assert subprocess.check_output(['git', '-C', str(worktree), 'show', f'{base}:{path}']) == (worktree / path).read_bytes()
receipt = {
    'status': 'AUTHOR_TARGET_AND_FULL_MODULE_OWNER_AUDIT_PASS_PENDING_INDEPENDENT_PROOF_REVIEW',
    'author_context': '/root/global_rate_author',
    'author_model': 'gpt-6.1-sol',
    'reasoning_effort': 'xhigh',
    'base': base,
    'branch': git('branch', '--show-current'),
    'worktree': str(worktree),
    'production_path': str(source_path.relative_to(worktree)),
    'source_sha256': sha(source_path),
    'frozen_declarations_sha256': sha(frozen),
    'source_declarations_match_frozen_bytes': True,
    'source_declarations_sha256': hashlib.sha256(actual_snapshot).hexdigest(),
    'actual_declarations_sha256': sha(doc / 'actual-declarations.txt'),
    'audit_source_sha256': sha(doc / 'Audit.lean'),
    'lean_version': '4.36.0-rc1',
    'lean_commit': 'c9afcddf514a6772bd4d649f7cfc04eff0b9f15e',
    'mathlib_pin': '807d3836b165983210ee2ecf3cd28f239436949c',
    'packages_realpath': str((worktree / '.lake/packages').resolve()),
    'olean_sha256': sha(worktree / '.lake/build/lib/lean/Shao/Probability/BivariateLegendre.olean'),
    'counts': {'definitions': 3, 'public_theorems': 4, 'all_theorems': 4, 'module_owned_constants': 7, 'additional_private_or_generated': 0},
    'owned_declarations': declarations,
    'axiom_whitelist': sorted(allowed),
    'ownership_method': 'getModuleIdxFor? == Shao.Probability.BivariateLegendre; enumerate all constants and collectAxioms transitively',
    'target_success': 'attempts/target-03',
    'audit_success': 'attempts/audit-02',
    'attempts': [
        {'id': 'target-01', 'exit': 127, 'cause': '/usr/bin/time absent; Lean did not start'},
        {'id': 'target-02', 'exit': 1, 'cause': 'anonymous noncomputable section missing end; all four proof bodies unchanged'},
        {'id': 'target-03', 'exit': 0, 'cause': None},
        {'id': 'audit-01', 'exit': 1, 'cause': 'unsupported pp.maxDepth output option; module enumeration itself completed'},
        {'id': 'audit-02', 'exit': 0, 'cause': None},
    ],
    'resource_policy': {'cpu_affinity': '10-13', 'lean_memory_mib': 8192, 'lean_jobs': 4, 'autoImplicit': False, 'max_concurrent_heavy_commands': 1},
    'successful_unchanged_checks_repeated': False,
    'local_lean_run': False,
    'cache_writes_or_pin_changes': False,
    'external_process_changes': False,
    'nonclaims': ['Independent complete-proof review not performed by author', 'No original root closure', 'No KL, derivative, Hessian or probability estimate extension', 'No merge, push, publication or PR'],
}
server_only = lambda p: p.suffix == '.log' or p.name in {
    'declaration-proposal-v1.md', 'source-map.md', 'statement-review-v1.md'}
receipt['server_only_evidence'] = {
    str(p): sha(p) for p in sorted(doc.rglob('*')) if p.is_file() and server_only(p)
}
receipt['evidence_sha256'] = {
    str(p.relative_to(doc)): sha(p)
    for p in sorted(doc.rglob('*'))
    if p.is_file() and p.name not in {'author-receipt.json', 'MANIFEST.sha256'}
}
(doc / 'author-receipt.json').write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
manifest = [f'{sha(p)}  {p.relative_to(worktree)}' for p in sorted(doc.rglob('*')) if p.is_file() and p.name != 'MANIFEST.sha256' and not server_only(p)]
manifest.insert(0, f'{sha(source_path)}  {source_path.relative_to(worktree)}')
(doc / 'MANIFEST.sha256').write_text('\n'.join(manifest) + '\n', encoding='utf-8')
print(json.dumps({'status': receipt['status'], 'source_sha256': receipt['source_sha256'], 'counts': receipt['counts'], 'receipt_sha256': sha(doc / 'author-receipt.json'), 'manifest_sha256': sha(doc / 'MANIFEST.sha256'), 'actual_declarations_sha256': receipt['actual_declarations_sha256']}))
