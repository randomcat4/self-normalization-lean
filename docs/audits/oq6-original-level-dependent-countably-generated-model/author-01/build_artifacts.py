from pathlib import Path
import hashlib
import json
import re
import textwrap
from datetime import datetime, timezone

ROOT = Path('C:/game/shao lean')
OUT = ROOT / 'drafts/oq56/unit253/author-01'
FREEZE = ROOT / 'drafts/oq56/unit253/freeze-01'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write(name, value):
    data = value if isinstance(value, str) else json.dumps(value, ensure_ascii=False, indent=2) + '\n'
    data = data.replace('\r\n', '\n').replace('\r', '\n').rstrip('\n') + '\n'
    (OUT / name).write_bytes(data.encode('utf-8'))


def fp(path):
    data = path.read_bytes()
    return {'path': path.as_posix(), 'sha256': sha(data), 'bytes': len(data), 'LF': data.count(b'\n')}


PRE = (FREEZE / 'FROZEN-PREAMBLE.txt').read_bytes()
HEAD = (FREEZE / 'FROZEN-HEAD.txt').read_bytes()
CLOSE = (FREEZE / 'FROZEN-CLOSING.txt').read_bytes()
BODY = (OUT / 'PROOF-BODY.txt').read_bytes()
SOURCE = PRE + HEAD + b':= by\n' + BODY + CLOSE
SOURCE_PATH = OUT / 'OriginalLevelDependentCountablyGeneratedModel.lean'
SOURCE_PATH.write_bytes(SOURCE)
S = SOURCE.decode('utf-8')
H = HEAD.decode('utf-8')
P = PRE.decode('utf-8')
proof_start = len(P) + len(H) + len(':= by\n')
proof_end = proof_start + len(BODY.decode('utf-8'))
head_end = len(P) + len(H)


def span(start, end, text=S, path=SOURCE_PATH):
    raw = text[start:end]
    line_start = text.rfind('\n', 0, start) + 1
    line_end = text.rfind('\n', 0, end) + 1
    return {
        'path': path.as_posix(), 'sourceSHA256': sha(path.read_bytes()),
        'charStart0': start, 'charEnd0Exclusive': end,
        'byteStart0': len(text[:start].encode('utf-8')),
        'byteEnd0Exclusive': len(text[:end].encode('utf-8')),
        'startLine1': text.count('\n', 0, start) + 1,
        'startColumnCodepoint1': start - line_start + 1,
        'startColumnUTF8Byte1': len(text[line_start:start].encode('utf-8')) + 1,
        'endLine1': text.count('\n', 0, end) + 1,
        'endColumnCodepoint1': end - line_end + 1,
        'endColumnUTF8Byte1': len(text[line_end:end].encode('utf-8')) + 1,
        'sliceSHA256': sha(raw.encode('utf-8')), 'sliceBytes': len(raw.encode('utf-8')),
        'raw': raw,
    }


scope_specs = [
    ('original-model-outer', len(P), S.index('    ∃ (m₀'), head_end),
    ('trimmed-model-core', S.index('      let μ₀'), S.index('      IsProbabilityMeasure μ₀'), head_end),
    ('arbitrary-finite-observation', S.index('      (∀ (J : Type v)'), S.index('      (∀ (n : ℕ)'), S.index('      (∀ (n : ℕ)')),
]
packet1_open = S.index('        (\n            let g', scope_specs[-1][2])
packet1_start = packet1_open + len('        (\n')
packet1_end = S.index('        ) ∧\n', packet1_start)
packet2_open = S.index('        (\n            let g', packet1_end)
packet2_start = packet2_open + len('        (\n')
finite_closing = S.rfind(') ∧\n', scope_specs[-1][1], scope_specs[-1][2])
assert finite_closing >= 0
scope_specs[-1] = (*scope_specs[-1][:3], finite_closing)
packet2_closing = head_end - len('        ))\n') + len('        ')
# Scope boundaries point to the closing delimiter of the surrounding forall/packet.
# The declaration-search intervals may include whitespace and that delimiter, but
# no local is considered in scope in the next packet.
scope_specs += [
    ('current-251-packet', packet1_start, packet1_end, packet1_end + len('        ')),
    ('current-252-packet', packet2_start, head_end, packet2_closing),
    ('proof-local', proof_start, proof_end, proof_end),
]

lines = S.splitlines(keepends=True)
line_offsets = []
cursor = 0
for line in lines:
    line_offsets.append(cursor)
    cursor += len(line)

locals_inventory = []
for index, line in enumerate(lines):
    match = re.match(r'^( *)(letI|let)\s+', line)
    if not match:
        continue
    indent = len(match.group(1))
    end_index = index + 1
    while end_index < len(lines):
        candidate = lines[end_index]
        if candidate.strip() and len(candidate) - len(candidate.lstrip(' ')) <= indent:
            break
        end_index += 1
    start = line_offsets[index]
    end = line_offsets[end_index] if end_index < len(lines) else len(S)
    raw = S[start:end]
    parsed = re.match(r'^ *(letI|let)\s+(.*?)\s*:=\s*(.*)', raw, re.S)
    assert parsed, raw
    kw, left, rhs = parsed.groups()
    if kw == 'letI':
        name = '@anonymous-letI-line-' + str(index + 1)
        full_type = left.removeprefix(':').strip()
    else:
        name, full_type = left.split(':', 1)
        name, full_type = name.strip(), full_type.strip()
    scope = [x for x in scope_specs if x[1] <= start < x[2]]
    assert len(scope) == 1, (name, scope)
    lexical = scope[0]
    locals_inventory.append({
        'id': f'local-{len(locals_inventory)+1:03}', 'kind': kw,
        'name': name, 'fullType': full_type, 'fullRHS': rhs.rstrip('\n'),
        'source': span(start, end), 'lexicalScope': lexical[0],
        'scopeBodyStart0': end, 'scopeEnd0Exclusive': lexical[3],
        'scopeBodyByteStart0': len(S[:end].encode('utf-8')),
        'scopeByteEnd0Exclusive': len(S[:lexical[3]].encode('utf-8')),
        'environment': 'original mΩ/μ; original outer lets' if lexical[0] == 'original-model-outer'
            else 'finite J : Type v, instJ : Fintype J, m₀/μ₀ plus original mΩ/μ' if lexical[0] == 'arbitrary-finite-observation'
            else 'same fixed m₀/μ₀; n≥4, current z≥1 and tilt window' if lexical[0].startswith('current-')
            else 'same existential witness m₀/hm₀; μ₀=μ.trim hm₀; local m₀ measurable instance',
    })

statement_lets = [x for x in locals_inventory if x['lexicalScope'] != 'proof-local']
proof_lets = [x for x in locals_inventory if x['lexicalScope'] == 'proof-local']
assert len(statement_lets) == 72, len(statement_lets)
assert len(proof_lets) == 7, len(proof_lets)
assert len([x for x in statement_lets if x['kind'] == 'letI']) == 1
assert len([x for x in proof_lets if x['kind'] == 'letI']) == 2

commands = []
for index, line in enumerate(lines):
    start = line_offsets[index]
    if not proof_start <= start < proof_end or not re.match(r'^  \S', line):
        continue
    end_index = index + 1
    while end_index < len(lines):
        candidate_start = line_offsets[end_index]
        if candidate_start >= proof_end or re.match(r'^  \S', lines[end_index]):
            break
        end_index += 1
    end = min(line_offsets[end_index] if end_index < len(lines) else len(S), proof_end)
    commands.append({'id': f'command-{len(commands)+1:02}', 'kind': line.strip().split()[0], 'source': span(start, end)})
assert len(commands) == 15
obtain_cmd = next(x for x in commands if x['kind'] == 'obtain')
rcases_cmd = next(x for x in commands if x['kind'] == 'rcases')
intro_cmds = [x for x in commands if x['kind'] == 'intro']

OLD_PATH = ROOT / 'library/Shao/OQ6/OriginalCountablyGeneratedModel.lean'
OLD_RAW = OLD_PATH.read_bytes()
OLD = OLD_RAW.decode('utf-8').replace('\r\n', '\n')
old_head = OLD.split(':= by\n', 1)[0]
old_theorem_head = old_head[old_head.index('theorem actual_normalized_original_countably_generated_model'):]
old_tail_index = old_theorem_head.index('      (∀ (n : ℕ) (hn : 4 ≤ n)')
new_tail_index = H.index('      (∀ (n : ℕ) (hn : 4 ≤ n)')
old_core_prefix = old_theorem_head[:old_tail_index].replace(
    'actual_normalized_original_countably_generated_model',
    'actual_original_level_dependent_countably_generated_model', 1)
assert old_core_prefix == H[:new_tail_index]
full_hcore_type = old_head[old_head.index('      let μ₀'):].strip()
result_core = old_head[old_head.index('      IsProbabilityMeasure μ₀'):].strip()


def split_top_and(text):
    parts = []
    stack = []
    start = 0
    pairs = {')': '(', ']': '[', '}': '{'}
    for i, char in enumerate(text):
        if char in '([{':
            stack.append(char)
        elif char in ')]}':
            assert stack and stack.pop() == pairs[char], (i, char)
        elif char == '∧' and not stack:
            parts.append(text[start:i].strip())
            start = i + 1
    assert not stack
    parts.append(text[start:].strip())
    return parts


core_types = split_top_and(result_core)
assert len(core_types) == 22, len(core_types)
core_names = ['hprob₀', 'hμmap', 'hgeq', 'hreq', 'hv', 'hrho', 'hrow', 'hh₂₀',
              'hcenter₀', 'hgmeas', 'hg₂₀', 'hgmean', 'hgsecond', 'hrmeas', 'hr₂₀',
              'hrsymm', 'hrcanonical', 'hglaw', 'hglp', 'hpair', 'hfinite', '_hfixed']


def binder_span(command, name, occurrence=0):
    raw = command['source']['raw']
    hits = list(re.finditer(r'(?<![\w₀-₉])' + re.escape(name) + r'(?![\w₀-₉])', raw))
    assert len(hits) > occurrence, name
    hit = hits[occurrence]
    start = command['source']['charStart0'] + hit.start()
    return span(start, start + len(name))


binders = []
for name in ['f', 'g', 'r', 'v', 'rho', 'rowIntegrable', 'gLp', 'projectionLaw', 'pairLaw']:
    origin = next(x for x in statement_lets if x['name'] == name and x['lexicalScope'] == 'original-model-outer')
    binders.append({'kind': 'intro-existing-statement-let', 'name': name,
                    'fullType': origin['fullType'], 'fullRHS': origin['fullRHS'],
                    'source': binder_span(intro_cmds[0], name), 'producer': intro_cmds[0]['source'],
                    'lexicalScope': 'proof body after first intro through proof_end', 'scopeEnd0Exclusive': proof_end,
                    'introducesNewPremise': False, 'originLocalID': origin['id']})

obtain_names = ['m₀', 'hm₀', 'hcount₀', 'hh₀', 'hf₀', 'hcore']
obtain_types = ['MeasurableSpace Ω', 'm₀ ≤ mΩ', '@MeasurableSpace.CountablyGenerated Ω m₀',
                'Measurable[m₀.prod m₀, borel ℝ] (fun t : Ω × Ω => h t.1 t.2)',
                '∀ k : ℕ, Measurable[m₀, borel ℝ] (f k)', full_hcore_type]
for name, typ in zip(obtain_names, obtain_types):
    binders.append({'kind': 'obtain-witness-or-And-component', 'name': name, 'fullType': typ,
                    'fullProducerRHS': obtain_cmd['source']['raw'].split(':=', 1)[1].strip(),
                    'source': binder_span(obtain_cmd, name), 'producer': obtain_cmd['source'],
                    'eliminationPattern': obtain_names,
                    'lexicalScope': 'proof after obtain, throughout fixed m₀ branch', 'scopeEnd0Exclusive': proof_end,
                    'introducesNewPremise': False})
for i, (name, typ) in enumerate(zip(core_names, core_types)):
    rhs = 'hcore' + '.2' * i + ('.1' if i < len(core_names)-1 else '')
    binders.append({'kind': 'rcases-existing-model-core', 'name': name, 'fullType': typ,
                    'fullProducerRHS': 'hcore', 'definitionalProjectionRHS': rhs,
                    'source': binder_span(rcases_cmd, name), 'producer': rcases_cmd['source'],
                    'lexicalScope': 'proof after rcases, same m₀/μ₀, throughout final conjunction',
                    'scopeEnd0Exclusive': proof_end, 'introducesNewPremise': False,
                    'originDeclaration': 'Shao.OQ6.OriginalCountablyGeneratedModel.actual_normalized_original_countably_generated_model',
                    'originSource': fp(OLD_PATH), 'componentNumber1': i+1,
                    'discarded': name == '_hfixed'})
for name, typ in [('n', 'ℕ'), ('hn', '4 ≤ n'), ('z', 'ℝ'), ('hz', '1 ≤ z'),
                  ('hwindow', 'z ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ))')]:
    binders.append({'kind': 'intro-existing-frozen-forall', 'name': name, 'fullType': typ,
                    'fullRHS': None, 'RHSDisposition': 'universally quantified frozen binder; no assigned RHS',
                    'source': binder_span(intro_cmds[1], name), 'producer': intro_cmds[1]['source'],
                    'lexicalScope': 'last exact conjunction only, after m₀ is fixed',
                    'scopeEnd0Exclusive': proof_end, 'introducesNewPremise': False})

for i, item in enumerate(binders, 1):
    item['id'] = f'binding-{i:03}'
assert len(binders) == 42

inventory = {'schema': 'unit253-full-source-local-types-rhs-lexical-scopes-v1',
             'source': fp(SOURCE_PATH), 'coordinateConvention': '0-based half-open codepoint and UTF8 byte offsets; line and column 1-based',
             'notLeanElaboratedTypes': True, 'actualModuleOwnerCount': None,
             'sourceLocalCount': len(locals_inventory), 'statementLocalCount': len(statement_lets),
             'proofLocalCount': len(proof_lets), 'explicitLocalHaveCount': 0,
             'scopeSpecifications': [{'name': x[0], 'declarationIntervalStart0': x[1], 'declarationIntervalEnd0Exclusive': x[2], 'scopeEnd0Exclusive': x[3]} for x in scope_specs],
             'locals': locals_inventory}
write('LOCAL-SOURCE-INVENTORY.json', inventory)
write('PROOF-BINDING-INVENTORY.json', {'schema': 'unit253-full-intro-obtain-rcases-binding-types-v1',
                                     'source': fp(SOURCE_PATH), 'bindingCount': len(binders),
                                     'proofLetBindingsSeparately': len(proof_lets),
                                     'actualModuleOwnerCount': None, 'binders': binders, 'allProofCommands': commands})


def flat(text):
    return ' '.join(text.split())


packet_comparisons = []
for unit, start, end in [(251, packet1_start, packet1_end), (252, packet2_start, head_end)]:
    head_path = ROOT / f'drafts/oq56/unit{unit}/freeze-01/FROZEN-HEAD.txt'
    dep_head = head_path.read_text(encoding='utf-8')
    dep_body = dep_head[dep_head.index('    let g :'):].strip().replace('μ', 'μ₀')
    actual = S[start:end].strip()
    if unit == 252:
        assert actual.endswith('))')
        actual = actual[:-2].rstrip()
    assert flat(actual) == flat(dep_body), f'packet{unit} differs'
    packet_comparisons.append({'unit': unit, 'inputHead': fp(head_path),
                               'targetSource': span(start, end),
                               'comparison': 'full token text equal after whitespace normalization and only μ→μ₀; 252 remove two frozen outer parentheses',
                               'PASS': True})

read_ack = json.loads((OUT / 'READ_ACK.json').read_text(encoding='utf-8'))
preservation = []
for binding in read_ack['inputBindings']:
    now = fp(Path(binding['path']))
    match = now['sha256'] == binding['sha256'] and now['bytes'] == binding['bytes']
    assert match, binding['path']
    preservation.append({'before': binding, 'after': now, 'unchanged': match})

for item in locals_inventory:
    ref = item['source']
    part = SOURCE[ref['byteStart0']:ref['byteEnd0Exclusive']]
    assert part.decode('utf-8') == ref['raw']
    assert sha(part) == ref['sliceSHA256']
    assert S[ref['charStart0']:ref['charEnd0Exclusive']] == ref['raw']
for item in binders:
    ref = item['source']
    assert SOURCE[ref['byteStart0']:ref['byteEnd0Exclusive']].decode('utf-8') == item['name']
    assert sha(SOURCE[ref['byteStart0']:ref['byteEnd0Exclusive']]) == ref['sliceSHA256']
for item in commands:
    ref = item['source']
    assert SOURCE[ref['byteStart0']:ref['byteEnd0Exclusive']].decode('utf-8') == ref['raw']

forbidden = re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', S)
public = re.findall(r'^theorem\s+(\S+)', S, re.M)
assert not forbidden
assert public == ['actual_original_level_dependent_countably_generated_model']
assert not re.findall(r'^(?:def|instance|abbrev|lemma|opaque|axiom)\b', S, re.M)
assert SOURCE == PRE + HEAD + b':= by\n' + BODY + CLOSE
assert not SOURCE.startswith(b'\xef\xbb\xbf') and b'\r' not in SOURCE
assert SOURCE.endswith(b'\n') and not SOURCE.endswith(b'\n\n')
assert BODY.endswith(b'\n') and not BODY.endswith(b'\n\n')
assert sha(HEAD) == '6feaec58d9f065cf442ffaeab0192b41809f80d4c3c33bda4d559c2a227119cd'

write('STATIC-CHECK.json', {
    'schema': 'unit253-author-static-composition-inventory-input-preservation-v1',
    'atUTC': datetime.now(timezone.utc).isoformat(), 'source': fp(SOURCE_PATH),
    'proof': fp(OUT / 'PROOF-BODY.txt'), 'compositionExact': True,
    'inputBindingsUnchanged': preservation, 'genericModelCoreLiteralPrefixEqual': True,
    'packetResultWholeBodyComparisons': packet_comparisons,
    'inventoryRoundTrip': {'locals': len(locals_inventory), 'proofBindings': len(binders), 'proofCommands': len(commands), 'PASS': True},
    'statementLetsIncludingLetI': len(statement_lets), 'proofLetsIncludingLetI': len(proof_lets),
    'publicTheorems': public, 'handwrittenTopLevelHelpersDefsInstances': 0,
    'forbiddenTokens': forbidden, 'UTF8': True, 'LF': True, 'BOM': False, 'singleFinalLF': True,
    'LeanExecuted': False, 'axiomAuditExecuted': False, 'actualModuleOwnerCount': None,
    'qualified': False, 'machinePending': True, 'fullOQ56': 'OPEN',
})
print(json.dumps({'source': fp(SOURCE_PATH), 'sourceLocals': len(locals_inventory),
                  'proofBindings': len(binders), 'proofCommands': len(commands),
                  'inputsUnchanged': len(preservation), 'static': 'PASS',
                  'qualified': False, 'machinePending': True}, ensure_ascii=False))
