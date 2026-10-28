from pathlib import Path
import difflib
import hashlib
import json

ROOT = Path('C:/game/shao lean')
UNIT = ROOT / 'drafts/oq56/unit257'
OUT = UNIT / 'author-repair-01'
OLD = UNIT / 'author-01'
FREEZE = UNIT / 'freeze-01'
assert (OUT / 'ACTUAL_READ_ACK.json').is_file()


def bind(p):
    b = p.read_bytes()
    return {'path': p.as_posix(), 'sha256': hashlib.sha256(b).hexdigest(),
            'bytes': len(b), 'LF': b.count(b'\n')}


def save(name, value):
    (OUT / name).write_bytes((json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode('utf-8'))


original = (OLD / 'OriginalLevelDependentStrictMomentFrontier.lean').read_bytes()
assert hashlib.sha256(original).hexdigest() == 'ee2f5ff993bc92f6d5154be82ebb4da683f909717f0b20a98a4b8c76255f305b'
original_proof = (OLD / 'PROOF-BODY.txt').read_bytes()
repairs = [
    ('    exact (hSourceLim.sub_const sourceCost0).abs.eventually\n',
     '    change Filter.Tendsto sourceCostη Filter.atTop (nhds sourceCost0) at hSourceLim\n'),
    ('    exact (hCostLim.sub_const compactCost0).abs.eventually\n',
     '    change Filter.Tendsto compactCostη Filter.atTop (nhds compactCost0) at hCostLim\n'),
]
source = original
proof = original_proof
for anchor, insertion in repairs:
    a, i = anchor.encode('utf-8'), insertion.encode('utf-8')
    assert source.count(a) == proof.count(a) == 1
    source = source.replace(a, i + a, 1)
    proof = proof.replace(a, i + a, 1)
# The old proof-body artifact included one boundary blank line. Keep the whole
# source byte-exact except for the two insertions, and represent that inherited
# boundary separator explicitly when assembling the single-final-LF proof file.
assert proof.endswith(b'\n\n') and not proof.endswith(b'\n\n\n')
proof = proof[:-1]
pre = (FREEZE / 'FROZEN-PREAMBLE.txt').read_bytes()
head = (FREEZE / 'FROZEN-HEAD.txt').read_bytes()
close = (FREEZE / 'FROZEN-CLOSING.txt').read_bytes()
assert source == pre + head + b':= by\n' + proof + b'\n' + close
for b in [source, proof]:
    assert b.decode('utf-8').encode('utf-8') == b
    assert not b.startswith(b'\xef\xbb\xbf') and b'\r' not in b
    assert b.endswith(b'\n') and not b.endswith(b'\n\n')
(OUT / 'OriginalLevelDependentStrictMomentFrontier.lean').write_bytes(source)
(OUT / 'PROOF-BODY.txt').write_bytes(proof)
patch = ''.join(difflib.unified_diff(original.decode('utf-8').splitlines(keepends=True),
    source.decode('utf-8').splitlines(keepends=True),
    fromfile=(OLD / 'OriginalLevelDependentStrictMomentFrontier.lean').as_posix(),
    tofile=(OUT / 'OriginalLevelDependentStrictMomentFrontier.lean').as_posix()))
(OUT / 'exact.patch').write_bytes(patch.encode('utf-8'))
assert sum(l.startswith('+') and not l.startswith('+++') for l in patch.splitlines()) == 2
assert sum(l.startswith('-') and not l.startswith('---') for l in patch.splitlines()) == 0

# Reuse the already-read pure-static inventory tool, adapting only the owned
# output directory and the explicit inherited proof/closing separator.
tool = (OLD / 'build_evidence.py').read_text(encoding='utf-8')
assert tool.count("OUT=ROOT/'drafts/oq56/unit257/author-01'") == 1
tool = tool.replace("OUT=ROOT/'drafts/oq56/unit257/author-01'",
                    "OUT=ROOT/'drafts/oq56/unit257/author-repair-01'", 1)
assert tool.count("assert source==pre+head+b':= by\\n'+proof+close") == 1
tool = tool.replace("assert source==pre+head+b':= by\\n'+proof+close",
                    "assert source==pre+head+b':= by\\n'+proof+b'\\n'+close", 1)
(OUT / 'build_evidence.py').write_bytes(tool.encode('utf-8'))
save('LOCAL-READ-NOTES.json', {
    'schema': 'unit257-repair01-local-read-and-format-notes-v1',
    'displayTruncation': 'Combined long outputs were truncated; affected full generic/source/proof/report materials were subsequently displayed in bounded calls.',
    'administrativeFailure': {
        'exception': "AttributeError: 'list' object has no attribute 'get'",
        'stage': 'optional compact REGISTRY owner print after ACK and INPUT-BINDINGS had already been saved',
        'sourceWritesBeforeFailure': 0,
        'effect': 'ACK and INPUT-BINDINGS existed and were read back; no authority inferred from failed optional print; no Lean/server operation occurred',
    },
    'proofBodyArtifactBoundaryNormalization': {
        'oldTrailingLFCount': 2,
        'newTrailingLFCount': 1,
        'inheritedSeparatorLFRepresentedInAssembly': 1,
        'wholeLeanSourceChanges': 'exactly two inserted change-at-hypothesis lines; all other original bytes retained',
    },
    'noNewLeanCheckOrMathematicalFailure': True,
    'allOldFailuresAndReceiptsPreserved': True,
})
print(json.dumps({'source': bind(OUT / 'OriginalLevelDependentStrictMomentFrontier.lean'),
    'proof': bind(OUT / 'PROOF-BODY.txt'), 'patch': bind(OUT / 'exact.patch'),
    'sourceInsertions': 2, 'sourceDeletions': 0, 'LeanServerNetworkOperations': 0}, ensure_ascii=False))
