from pathlib import Path
import hashlib
import json
import re
from datetime import datetime, timezone

ROOT = Path('C:/game/shao lean')
OUT = ROOT / 'drafts/oq56/unit250/author-01'
FREEZE = OUT.parent / 'freeze-01'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def save(name, value):
    text = json.dumps(value, ensure_ascii=False, indent=2) + '\n'
    (OUT / name).write_bytes(text.encode('utf-8'))

frozen = json.loads((FREEZE / 'frozen-declaration.json').read_text(encoding='utf-8'))
assert sha((FREEZE / 'frozen-declaration.json').read_bytes()) == 'a26f0a109e8f06fd03c4326ecd868ed882ae40f84a927c172b67e567ac8166de'
for item in frozen['files'] + frozen['originalSources'] + frozen['exactAcceptedBearingInterfaces']:
    data = Path(item['path']).read_bytes()
    assert len(data) == item['bytes'] and sha(data) == item['sha256'], item['path']

pre = (FREEZE / 'FROZEN-PREAMBLE.txt').read_bytes()
head = (FREEZE / 'FROZEN-HEAD.txt').read_bytes()
closing = (FREEZE / 'FROZEN-CLOSING.txt').read_bytes()
body = (OUT / 'PROOF-BODY.txt').read_bytes().replace(b'\r\n', b'\n')
source = pre + head + b' := by\n' + body.rstrip(b'\n') + b'\n\n' + closing
assert not source.startswith(b'\xef\xbb\xbf') and b'\r' not in source
assert source.startswith(pre + head) and source.endswith(closing)
assert len(re.findall(rb'^theorem ', source, re.M)) == 1
assert not re.search(rb'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', source)
path = OUT / 'OriginalLevelDependentWeightedSourceCost.lean'
path.write_bytes(source)
lines = source.decode('utf-8').splitlines()

# A lossless source-level inventory. Every declaration record contains its complete
# source type and RHS, rather than a shortened mathematical description.
starts = []
for i, line in enumerate(lines):
    m = re.match(r'^(\s*)(let|have|letI|haveI)\s+([^\s(:]+)', line)
    if m:
        starts.append((i, len(m.group(1)), m.group(2), m.group(3)))
records = []
for i, indent, kind, name in starts:
    end = i + 1
    while end < len(lines):
        line = lines[end]
        if line.strip() and len(line) - len(line.lstrip()) <= indent:
            break
        end += 1
    # Frozen let declarations are a nested theorem-result telescope; their lexical
    # RHS ends at the next let or conclusion at the same indentation.
    chunk = '\n'.join(lines[i:end])
    marker = chunk.find(':=')
    signature = chunk[:marker].rstrip() if marker >= 0 else chunk
    rhs = chunk[marker + 2:].lstrip() if marker >= 0 else None
    section = 'FROZEN_RESULT_TELESCOPE' if i < len((pre + head).decode('utf-8').splitlines()) else 'THEOREM_PROOF'
    records.append({
        'id': f'{kind}:{name}:{i+1}', 'kind': kind, 'name': name,
        'lineStart': i+1, 'lineEndInclusive': end,
        'scope': section, 'indentation': indent,
        'fullSourceSignature': signature, 'completeRHS': rhs,
        'completeSourceBlock': chunk,
        'sourceBlockSha256': sha((chunk + '\n').encode('utf-8')),
    })

for record in records:
    record['visiblePriorProofBindingIds'] = [p['id'] for p in records
        if p['scope'] == 'THEOREM_PROOF' and p['indentation'] == 2
        and p['lineEndInclusive'] < record['lineStart']]
    record['completeAmbientTheoremParametersReference'] = 'publicFrozenCompleteHead'
    record['ownParameterizedBindersReference'] = 'fullSourceSignature'

def parameter_sites(signature, start_line, name):
    # Parse only the parameter telescope immediately after a declaration name.
    # Nested parentheses in a full hypothesis type are preserved verbatim.
    pos = signature.index(name) + len(name)
    answer = []
    while pos < len(signature):
        while pos < len(signature) and signature[pos].isspace():
            pos += 1
        if pos >= len(signature) or signature[pos] not in '([{':
            break
        begin = pos
        stack = [signature[pos]]
        pos += 1
        while stack:
            ch = signature[pos]
            if ch in '([{':
                stack.append(ch)
            elif ch in ')]}':
                stack.pop()
            pos += 1
        content = signature[begin+1:pos-1]
        if ':' in content:
            names, tp = content.split(':', 1)
            names = names.strip().split()
        else:
            names, tp = [None], content
        answer.append({'line': start_line + signature[:begin].count('\n'),
            'completeSourceBinder': signature[begin:pos],
            'names':names, 'fullTypeExact':tp.strip()})
    return answer

public_sig = head.decode('utf-8').split(' :\n    let g', 1)[0]
declaration_binders = parameter_sites(public_sig, pre.decode('utf-8').count('\n')+1,
    'actual_original_level_dependent_weighted_source_cost')
for record in records:
    record['declarationParameterBinders'] = parameter_sites(record['fullSourceSignature'],
        record['lineStart'], record['name'])

# Every variable-binding site is retained with the literal surrounding source.
# The accompanying type dictionary supplies full inferred types for all source
# binder names, including finite-sum membership and unnamed binders.
binder_sites = []
for i, line in enumerate(lines):
    for match in re.finditer(r'\b(?:fun|intro|by_cases)\b|∀|∫|∑|\{Ω\s*:|\(Ω\s*:|\[mΩ\s*:|\[IsProbabilityMeasure', line):
        enclosing = [x for x in records if x['lineStart'] <= i+1 <= x['lineEndInclusive']]
        owner = enclosing[-1]['id'] if enclosing else 'PUBLIC_FROZEN_THEOREM'
        token = match.group(0)
        inferred = []
        tail = line[match.end():]
        owner_name = enclosing[-1]['name'] if enclosing else ''
        if token == 'fun':
            binder_text = tail.split('=>', 1)[0].strip()
        elif token == 'intro':
            binder_text = tail.strip()
        elif token == 'by_cases':
            binder_text = tail.split(':', 1)[0].strip()
        elif token in ['∀', '∫', '∑']:
            binder_text = tail.split(',', 1)[0].strip()
        else:
            binder_text = tail
        names_text = binder_text.split(':', 1)[0].replace('(', '').replace(')', '').strip()
        if token == '∑' and '∈' in names_text:
            names_text = names_text.split('∈', 1)[0].strip()
        for name in names_text.split():
            tp = {'o':'Ω', 'y':'Ω', 't':'Ω × Ω', 'ζ':'Fin n → Ω',
                  'i':'Fin n', 'j':'Fin n', 'k':'Fin n', "k'":'Fin n',
                  'hj':'j ∈ (Finset.univ : Finset (Fin n))',
                  "hk'":"k' ∈ (Finset.univ : Finset (Fin n))",
                  'hij':"j = i ∨ k' = i", 'hjk':"j < k'"}.get(name)
            if name == '_':
                if ':' in binder_text:
                    tp = binder_text.split(':', 1)[1].strip()
                elif 'k\u0027 _' in binder_text:
                    tp = "k' ∈ (Finset.univ : Finset (Fin n)).erase j"
                elif 'j _' in binder_text:
                    tp = 'j ∈ (Finset.univ : Finset (Fin n)).erase i' if owner_name == 'hSdeleteM' else 'j ∈ (Finset.univ : Finset (Fin n))'
                elif 'i _' in binder_text:
                    tp = 'i ∈ (Finset.univ : Finset (Fin n))'
            if tp is not None:
                inferred.append({'name':name, 'fullType':tp})
        binder_sites.append({'line': i+1, 'column': match.start()+1,
            'kind': token, 'enclosingSourceBlock': owner,
            'binderSourceText': binder_text, 'inferredSourceBinderTypes': inferred,
            'completeLine': line})

save('SOURCE-INTERFACE-INVENTORY.json', {
    'schema': 'unit250-lossless-source-interface-inventory-v1',
    'status': 'SOURCE_COMPLETE_GENERATED_KERNEL_INTERFACES_PENDING',
    'source': {'path': str(path), 'bytes': len(source), 'sha256': sha(source)},
    'publicDeclaration': 'Shao.OQ6.OriginalLevelDependentWeightedSourceCost.actual_original_level_dependent_weighted_source_cost',
    'publicFrozenPreamble': pre.decode('utf-8'),
    'publicFrozenCompleteHead': head.decode('utf-8'),
    'publicClosing': closing.decode('utf-8'),
    'publicDeclarationParameterBinders': declaration_binders,
    'bindings': records,
    'allVariableBinderSites': binder_sites,
    'fullTypeDictionary': {
        'Ω': 'Type u', 'mΩ': 'MeasurableSpace Ω',
        'μ': 'Measure Ω', 'probabilityInstance': 'IsProbabilityMeasure μ',
        'h': 'Ω → Ω → ℝ', 'g': 'Ω → ℝ', 'r': 'Ω → Ω → ℝ',
        'n': 'ℕ', 'z,C0,v,rho,N,I,m,K,Q,A,denA,k,kA': 'ℝ',
        'o,y': 'Ω', 't in product integrals or product measurability': 'Ω × Ω',
        'ζ': 'Fin n → Ω', 'i,j,k,k\u0027 in sample indices': 'Fin n',
        'anonymous finite-product coordinate binder': 'Fin n',
        'anonymous measurable_const sample binder': 'Fin n → Ω',
        'j/hj in hPairM and hPairDeleteM': 'j : Fin n; hj : j ∈ (Finset.univ : Finset (Fin n))',
        "k\u0027/hk\u0027 in hPairM and hPairDeleteM": "k' : Fin n; hk' : k' ∈ (Finset.univ : Finset (Fin n))",
        'hij in hEraseM': "j = i ∨ k' = i",
        'hjk in hPairM and hPairDeleteM': "j < k'",
        'fun j _ in hL0/hLM/hLdeleteM/hSM': 'j : Fin n; _ : j ∈ (Finset.univ : Finset (Fin n))',
        'fun j _ in hSdeleteM': 'j : Fin n; _ : j ∈ (Finset.univ : Finset (Fin n)).erase i',
        "fun k\u0027 _ in hRowM and hRowDeleteM": "k' : Fin n; _ : k' ∈ (Finset.univ : Finset (Fin n)).erase j",
        'fun i _ in finite integral sums': 'i : Fin n; _ : i ∈ (Finset.univ : Finset (Fin n))',
        'classical tactic': 'Local classical decidability instances only; no explicit source letI/haveI/instance declaration',
    },
    'allExplicitLocalSubstantiveFactsHaveType': True,
    'explicitTopLevelHelperCount': 0, 'explicitInstanceDeclarationCount': 0,
    'generatedActualOwnerTypesAndNonTheoremValues': None,
    'generatedInterfaceReason': 'No Lean executed by the pure-local author; lead must bind server-generated actual names/types/values to this exact hash.',
})

save('READING-RUNTIME-ACK.json', {
    'schema': 'unit250-author-actual-reading-runtime-ack-v1',
    'atUTC': datetime.now(timezone.utc).isoformat(),
    'role': '/root/oq56_unit250_author',
    'ownerChat': '01a1822b-1815-7f21-a1af-2e0b15ee67a5',
    'ownedRoot': str(OUT),
    'actualRuntime': 'RUNNING_PURELOCAL_SOURCE_AUTHOR',
    'freezeAndAllListedOriginalAndBearingHashesVerified': True,
    'completeOriginalReading': ['p51.md', 'p54.md'],
    'completeFrozenPreambleHeadClosingRouteRead': True,
    'completeBearingPublicHeadersDefinitionsRead': True,
    'writer': 1, 'heavyCommands': 0, 'inflightExecution': 0,
    'pendingExternal': 0, 'children': 0, 'uncertainOperations': 0,
    'requestedModel': 'gpt-6.1-sol', 'requestedEffort': 'xhigh',
    'actualModel': None, 'actualEffort': None,
    'usage': {'input':None, 'cachedInput':None, 'output':None, 'reasoningSubset':None},
})

save('STATIC-CHECK.json', {
    'schema': 'unit250-author-static-check-v1', 'atUTC': datetime.now(timezone.utc).isoformat(),
    'sourceSha256': sha(source), 'bytes': len(source),
    'utf8Strict': source.decode('utf-8').encode('utf-8') == source,
    'BOM': False, 'CRBytes': source.count(b'\r'), 'LFCount': source.count(b'\n'),
    'frozenPreambleHeadExact': source.startswith(pre + head),
    'frozenClosingExact': source.endswith(closing),
    'publicTheoremCount': 1,
    'newTopLevelHelpers': 0,
    'forbiddenConstructMatches': [],
    'sourceAnalyticProducerCalls': source.count(b'Shao.OQ6.SourceAnalyticCost.actual_quadratic_source_analytic_cost'),
    'sourceBindingRecords': len(records), 'sourceBinderSites': len(binder_sites),
    'explicitDeclarationParameterGroups': len(declaration_binders) + sum(len(r['declarationParameterBinders']) for r in records),
    'kernel': 'NOT_RUN', 'transitiveAxioms': 'NOT_RUN', 'independentFinalReview': 'PENDING',
})

payloads = []
for name in ['OriginalLevelDependentWeightedSourceCost.lean', 'PROOF-BODY.txt', 'SOURCE-ROUTE.md',
             'SOURCE-INTERFACE-INVENTORY.json', 'STATIC-CHECK.json', 'assemble_and_inventory.py',
             'READING-RUNTIME-ACK.json', 'SEAL-ATTEMPT-01.json']:
    p = OUT / name
    data = p.read_bytes()
    payloads.append({'path': str(p), 'bytes': len(data), 'sha256': sha(data)})
additional = []
for rel in ['Shao/OQ6/QuadraticTilt.lean', 'Shao/OQ6/ResidualDeletion.lean',
            'Shao/OQ6/CanonicalDoubleGhostScalarMoments.lean',
            'Shao/OQ5/P51/BoundedStudentizerGeometry.lean', 'Shao/OQ5/P35/RowIdentity.lean']:
    p = ROOT / 'library' / rel
    data = p.read_bytes()
    additional.append({'path':str(p), 'bytes':len(data), 'sha256':sha(data)})
save('MANIFEST.json', {
    'schema': 'unit250-author-final-payload-manifest-v1',
    'status': 'PROVED_CANDIDATE_NOT_KERNEL_CHECKED_NOT_ACCEPTED',
    'owner': '/root/oq56_unit250_author',
    'laneLead': '01a1822b-1815-7f21-a1af-2e0b15ee67a5',
    'currentRoot': '01a17d3c-6dfd-7cc0-94ed-35d758a423a5',
    'requestedModel': 'gpt-6.1-sol', 'requestedEffort': 'xhigh',
    'actualModel': None, 'actualEffort': None,
    'usage': {'input': None, 'cachedInput': None, 'output': None, 'reasoningSubset': None},
    'frozenDeclaration': {'path': str(FREEZE/'frozen-declaration.json'), 'bytes': 4352,
        'sha256': 'a26f0a109e8f06fd03c4326ecd868ed882ae40f84a927c172b67e567ac8166de'},
    'freezePayloads': frozen['files'],
    'readOnlyBearingInputs': frozen['exactAcceptedBearingInterfaces'],
    'additionalAlreadyAcceptedPublicDefinitionsOrWeightBound': additional,
    'readOnlyOriginalSources': frozen['originalSources'],
    'payloads': payloads,
    'kernel': 'PENDING_SERVER', 'independentFinalReview': 'PENDING_FRESH_SEPARATE',
    'actualGeneratedTypesValuesAllOwnerAxioms': 'PENDING_SERVER',
    'noNewPremises': True, 'newPublicTheorems': 1,
    'nonClaims': frozen['nonClaims'],
    'writerScope': str(OUT),
})
print(json.dumps({'sourceSha256': sha(source), 'sourceBytes': len(source),
    'bindingRecords': len(records), 'binderSites': len(binder_sites),
    'kernel': 'NOT_RUN'}, ensure_ascii=False))
