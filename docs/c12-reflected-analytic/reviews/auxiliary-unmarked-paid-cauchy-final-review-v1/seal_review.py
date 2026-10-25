import sys
sys.dont_write_bytecode = True
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
AUTHOR = HERE.parent / 'auxiliary-unmarked-paid-cauchy-v1'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def write(name, obj):
    (HERE / name).write_text(json.dumps(obj, ensure_ascii=False, indent=2) + '\n', encoding='utf-8', newline='\n')

def binding(p):
    return {'path': str(p), 'sha256': sha(p), 'bytes': p.stat().st_size}

local = json.loads((HERE / 'local-evidence-bindings.json').read_text(encoding='utf-8'))
final = json.loads((HERE / 'readonly-final-observation.json').read_text(encoding='utf-8'))
receipt = json.loads((AUTHOR / 'receipt.json').read_text(encoding='utf-8'))
audit = json.loads((AUTHOR / 'owned-audit.json').read_text(encoding='utf-8'))
types = (AUTHOR / 'actual-owned-types.txt').read_text(encoding='utf-8')
production = (AUTHOR / 'AuxiliaryUnmarkedPaidCauchy.lean').read_text(encoding='utf-8')
actual_names = re.findall(r'^TARGET_DECL (\S+) KIND theorem', types, re.M)
public_names = re.findall(r'^theorem (\w+)', production, re.M)
assert len(actual_names) == 2 and len(set(actual_names)) == 2 and len(public_names) == 2
assert set(actual_names) == {r['name'] for r in audit['module_owned_constants']}
assert set(actual_names) == {'Shao.C2.AuxiliaryUnmarkedPaidCauchy.' + n for n in public_names}
assert all(r['kind'] == 'theorem' and set(r['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for r in audit['module_owned_constants'])
assert (AUTHOR / 'actual-definition-values.txt').stat().st_size == 0
assert '...' not in types and '⋯' not in types
assert final['status'] == 'PASS' and final['failures'] == []
assert final['typeBlockBoundary']['exactEqual'] and final['attemptDirectories'] == ['attempt001']
assert len(final['bindings']) == 46
assert final['leanToolchain'] == receipt['toolchain'] and final['mathlibHEAD'] == receipt['mathlib']
assert json.loads(final['kernelExit'])['kernelExit'] == 0 and json.loads(final['auditExit'])['auditExit'] == 0
assert sha(AUTHOR / 'receipt.json') == '2c0fbd2927faf5c429de5c0014e33d556bc118304433953cb78679397ba9746c'
assert all(final['expectedAbsentCommonSources'].values())

checked = {}
def check_rows(rows):
    for path, expected in rows.items():
        p = Path(path)
        assert sha(p) == expected['sha256'], path
        if 'bytes' in expected:
            assert p.stat().st_size == expected['bytes'], path
        checked[str(p)] = binding(p)

check_rows(local['authorFiles'])
check_rows(local['sourcePaper'])
for qualification in local['qualifiedEvidence'].values():
    p = Path(qualification['parentPath'])
    assert sha(p) == qualification['parentSHA256']
    checked[str(p)] = binding(p)
    check_rows(qualification['sealedReviewBindings'])
for dependency in local['consumedDependencies'].values():
    check_rows(dependency['localFiles'])

native = []
for name in ['native-interface-observation.json', 'native-extra-interface-observation.json']:
    data = json.loads((HERE / name).read_text(encoding='utf-8'))
    for row in data['native']:
        assert row['workingEqualsPinned'] and row['sha256'] == row['pinnedBlobSHA256']
        native.append({'path': row['path'], 'sha256': row['sha256']})

coverage = {
    'completeOriginalSourceToFrozenStatements': True,
    'completeImportsContextAndBothHeadsFrozenBeforeImplementation': True,
    'completeFinalProductionProofs': True,
    'allActualOwnedTypesLiterallyReadUnelided': True,
    'allActualNonTheoremValues': True,
    'allPrivateGeneratedOwners': True,
    'completeConsumedQualifiedHeadsAndTypes': True,
    'newInterfaceInteractions': True,
    'exactSourceObjectReceiptBindings': True,
    'completeOriginalSavedLogsByLosslessPayloadDecomposition': True,
    'allOwnedRecursiveAxiomImplementationAndEvidence': True,
    'sourceScopeQuantifiersAndBoundaryCases': True,
    'qualifiedOldProofReviewsReusedWithoutReReview': True,
    'fullParentAcceptanceWritten': False,
}
counts = {
    'publicSourceTheorems': len(public_names),
    'actualOwnedConstants': len(audit['module_owned_constants']),
    'actualTheorems': sum(r['kind'] == 'theorem' for r in audit['module_owned_constants']),
    'privateSourceTheorems': 0,
    'generatedTheorems': len(actual_names) - len(public_names),
    'nonTheoremValues': sum(r['kind'] != 'theorem' for r in audit['module_owned_constants']),
    'completeActualTypeBytes': (AUTHOR / 'actual-owned-types.txt').stat().st_size,
    'completeNonTheoremValueBytes': (AUTHOR / 'actual-definition-values.txt').stat().st_size,
}
review = {
    'status': 'CORRECT',
    'unit': 178,
    'module': receipt['module'],
    'atUTC': datetime.now(timezone.utc).isoformat(),
    'reviewerTask': '/root/auxiliary_unmarked_paid_cauchy_final_review',
    'author': '01a16c4c-25a6-7740-a10e-12635a13edae',
    'reviewerConfiguredModel': 'gpt-6.1-sol',
    'reviewerConfiguredEffort': 'xhigh',
    'backendModelTelemetry': None,
    'usage': {'input': None, 'cachedInput': None, 'output': None, 'reasoningSubset': None},
    'authorReviewerSeparation': True,
    'sourceSHA256': receipt['sourceSHA256'],
    'objectSHA256': receipt['objectSHA256'],
    'receiptSHA256': sha(AUTHOR / 'receipt.json'),
    'frozenSHA256': receipt['frozenSHA256'],
    'completeActualTypesSHA256': sha(AUTHOR / 'actual-owned-types.txt'),
    'actualDefinitionValuesSHA256': sha(AUTHOR / 'actual-definition-values.txt'),
    'fullReviewMD': binding(HERE / 'full-review.md'),
    'coverage': coverage,
    'derivedCounts': counts,
    'ownedNames': actual_names,
    'allOwnedAxiomRows': audit['module_owned_constants'],
    'whitelist': ['propext', 'Classical.choice', 'Quot.sound'],
    'qualifiedDependencies': local['consumedDependencies'],
    'qualificationEvidence': local['qualifiedEvidence'],
    'originalSourceEvidence': local['sourcePaper'],
    'kernel': {'sourceBoundOriginalAttempt': 'attempt001', 'kernelExit': 0, 'auditExit': 0, 'newReviewerLeanRuns': 0, 'newReviewerAuditRuns': 0, 'replays': 0},
    'finalRemoteEvidence': binding(HERE / 'readonly-final-observation.json'),
    'finalRemoteBindingCount': len(final['bindings']),
    'nativePinnedSourceBindings': native,
    'scope': 'Natural-order unmarked decaying moment producer and arbitrary-measurable-set Cauchy with higher damped integrability paid from first theorem at2p. Auxiliary finite3 only. Positive s, s*beta^2<=half. Genuine raw pi, full sum, energy and restricted Laplace integral. Original finite2 scope unchanged.',
    'excludedClaims': ['arbitrary-real-order numeric moment producer', 's=0', 'marked Cauchy', 'rare-event probability estimate', 'inverse-moment or grid assembly', 'C2 or C12 root completion', 'novelty or new external-result attribution'],
    'proofReview': {
        public_names[0]: {'status': 'CORRECT', 'complete': True, 'bearingArgument': 'Exact qualified176 b=4beta^2 retained half and positive cutoff; legal-scale algebra; exact qualified175 negative gamma branch with universal Cp before law/cutoff/n/s.'},
        public_names[1]: {'status': 'CORRECT', 'complete': True, 'bearingArgument': 'First theorem at2p; exact Nat/Real cast function equality pays qualified173 hDamped; actual unmarked Cauchy; native sqrt monotonicity and complete positive square identity give sqrtC2p*s^(-p/2)*exp(-(c/2)sn).'},
    },
    'criticalGaps': [],
    'inspectionIssues': binding(HERE / 'inspection-notes.json'),
    'rootStatus': {'C2': 'OPEN', 'C12': 'OPEN'},
    'nextMissingMathematicalInterface': 'A separately proved bound on the actual restricted Laplace/tilted rare-event factor; then marked assembly/inverse moments/grids as independently source-bound dependencies.',
    'publicationOrIntegration': 'NONE_BY_REVIEWER',
}
write('full-review.json', review)

validation = {
    'status': 'PASS',
    'unit': 178,
    'atUTC': datetime.now(timezone.utc).isoformat(),
    'checks': {'sealedQualifiedParentHashes': True, 'sealedQualifiedReviewJSONMarkdownValidationRelease': True, 'allLocalExpectedFields': True, 'originalSourceHashes': True, 'freezeContextHeadsExact': True, 'actualOwnerMapMatchesAllFullTypeBlocksAndProductionHeads': True, 'allOwnerWhitelist': True, 'allNonTheoremValuesCovered': True, 'finalRemoteExpectedHashes': True, 'pinnedNativeSourceBlobs': True, 'completeAuditLogPayloadEquality': True, 'originalKernelAuditExitZero': True, 'UTF8NoBOMLF': True, 'noForbiddenProofTerms': True},
    'localBindingsVerified': len(checked),
    'localBoundFiles': checked,
    'remoteBindingsVerified': len(final['bindings']),
    'qualifiedParentCount': len(local['qualifiedEvidence']),
    'qualifiedReviewSealCount': sum(len(q['sealedReviewBindings']) for q in local['qualifiedEvidence'].values()),
    'derivedCounts': counts,
    'fullReviewJSON': binding(HERE / 'full-review.json'),
    'fullReviewMD': binding(HERE / 'full-review.md'),
    'newLeanRuns': 0,
    'newAuditRuns': 0,
    'oldProofReReviews': 0,
    'initialReadOnlyObservation': 'FAIL_UNSUPPORTED_EXTRA_PATH_PRESERVED',
    'inspectionIssuesResolved': True,
    'finalReadOnlyObservation': 'PASS_ALL46_EXPECTED_BINDINGS',
    'validationScope': 'Deterministic evidence consistency; mathematical verdict is the independent complete review, not inferred from these assertions alone.',
}
write('validation.json', validation)

payload = {}
for p in sorted(HERE.iterdir()):
    if p.is_file() and p.name not in ['sealed-payload.json', 'RELEASE.json']:
        payload[p.name] = binding(p)
write('sealed-payload.json', {'status': 'SEALED', 'unit': 178, 'files': payload})
for row in payload.values():
    assert sha(Path(row['path'])) == row['sha256']
release = {
    'status': 'COMPLETE_INDEPENDENT_FINAL_REVIEW_CORRECT_WRITER_EXECUTION_RELEASED',
    'unit': 178,
    'module': receipt['module'],
    'atUTC': datetime.now(timezone.utc).isoformat(),
    'reviewerTask': '/root/auxiliary_unmarked_paid_cauchy_final_review',
    'writerReleased': True,
    'executionReleased': True,
    'heavyInFlight': False,
    'inFlight': [],
    'actualRunState': 'COMPLETE_RELEASED_ZERO_INFLIGHT',
    'reviewerConfiguredModel': 'gpt-6.1-sol',
    'reviewerConfiguredEffort': 'xhigh',
    'backendAndUsageTelemetry': None,
    'usage': {'input': None, 'cachedInput': None, 'output': None, 'reasoningSubset': None},
    'sourceSHA256': receipt['sourceSHA256'],
    'objectSHA256': receipt['objectSHA256'],
    'receiptSHA256': sha(AUTHOR / 'receipt.json'),
    'frozenSHA256': receipt['frozenSHA256'],
    'fullReviewJSONSHA256': sha(HERE / 'full-review.json'),
    'fullReviewMDSHA256': sha(HERE / 'full-review.md'),
    'validationSHA256': sha(HERE / 'validation.json'),
    'finalReadOnlyObservationSHA256': sha(HERE / 'readonly-final-observation.json'),
    'sealedPayloadSHA256': sha(HERE / 'sealed-payload.json'),
    'sealedFiles': len(payload),
    'criticalGaps': [],
    'parentAcceptanceWritten': False,
    'productionChanges': False,
    'LeanRuns': 0,
    'auditRuns': 0,
    'gateReplays': 0,
    'next': 'Parent may verify seals and independently accept this exact unit; C2/C12 OPEN. No reviewer execution remains.',
}
write('RELEASE.json', release)
print(json.dumps({'status': 'CORRECT', 'derivedCounts': counts, 'localBindingsVerified': len(checked), 'remoteBindingsVerified': len(final['bindings']), 'sealedFiles': len(payload), 'fullReviewJSONSHA256': release['fullReviewJSONSHA256'], 'fullReviewMDSHA256': release['fullReviewMDSHA256'], 'validationSHA256': release['validationSHA256'], 'releaseSHA256': sha(HERE / 'RELEASE.json'), 'actualRunState': release['actualRunState']}, indent=2))
