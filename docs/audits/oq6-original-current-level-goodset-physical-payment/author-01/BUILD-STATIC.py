"""Local static packet exporter only; never invokes Lean, shell, network or a server."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path('C:/game/shao lean')
BASE = ROOT / 'drafts/oq56/unit258/author-01'
FREEZE = BASE.parent / 'freeze-01'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write(name, value):
    if not isinstance(value, str):
        value = json.dumps(value, ensure_ascii=False, indent=2)
    (BASE / name).write_bytes((value.replace('\r\n', '\n').rstrip('\n') + '\n').encode('utf-8'))


source = (BASE / 'OriginalCurrentLevelGoodsetPhysicalPayment.lean').read_bytes()
lines = source.decode('utf-8').splitlines(keepends=True)
starts = [0]
for line in lines:
    starts.append(starts[-1] + len(line.encode('utf-8')))


def span(first, last):
    data = source[starts[first - 1]:starts[last]]
    return dict(startLine=first, endLine=last, startByteInclusive=starts[first - 1],
                endByteExclusive=starts[last], sha256=sha(data), utf8=data.decode('utf-8'))


def line_of(fragment, first=1, last=None):
    return next(i + 1 for i in range(first - 1, last or len(lines)) if fragment in lines[i])


p54 = (ROOT / 'library/Shao/OQ6/P54ActualGoodsetFrontier.lean').read_text('utf-8')
p54head = p54[p54.index('theorem fixed_original_'):p54.index(' := by')]
frontier_type = p54head[p54head.index('      ∀ (C a t0 M'):].strip()
hn_type = p54head[p54head.index('          4 ≤ n ∧'):].strip()
head = (FREEZE / 'FROZEN-HEAD.txt').read_text('utf-8')
old = 'clippedCenteredDelta n g r 512 rho 1 x'
raw = 'centeredDelta n g r x'
v = 'projectionV n g x'
d = 'residualStatisticD n r x'
s = 'Real.sqrt (centeredSq n g r x)'
old_names = ['hVpos', 'hEnergy', 'hNum', 'hNumStrict', 'hRawScaled', 'hRawAbs',
             'hRawLower', 'hOldContract', 'hOldScaled', 'hOldStrict', 'hOldAbs',
             'hOldClipPos', 'hSourcePos', 'hFactor']
old_types = [f'0 < {v}', '(1 / 2 : ℝ) ≤ projectionEnergy n g x',
             f'z * |{d}| ≤ {v} / 8', f'z * |{d}| < {v} / 4',
             f'z ^ (2 : ℕ) * |{raw}| ≤ (1 / 32 : ℝ)',
             f'|{raw}| ≤ (1 / 32 : ℝ)', f'-(1 / 8 : ℝ) < {raw}',
             f'|{old}| ≤ |{raw}|', f'z ^ (2 : ℕ) * |{old}| ≤ (1 / 32 : ℝ)',
             f'z ^ (2 : ℕ) * |{old}| < (1 / 8 : ℝ)',
             f'|{old}| ≤ (1 / 32 : ℝ)',
             f'0 < {v} * Real.sqrt (1 + {old})', f'0 < {s}',
             f'{s} = {v} * Real.sqrt (1 + {raw})']
old_on = '∀ (x : Fin n → Ω), x ∈ Hsource →\n  ' + ' ∧\n  '.join(old_types)
on_result = ' ∧\n  '.join(['0 < V0 x', 'z * |D1 x| ≤ V0 x / 8',
              'z ^ 2 * |D2z x| ≤ (1 / 32 : ℝ)', f'0 < {s}',
              f'{s} = V0 x * Real.sqrt (1 + {raw})', f'D2z x = {raw}',
              'clipped x = physical x'])
on_type = '∀ (x : Fin n → Ω) (hx : x ∈ Hsource),\n  ' + on_result
clip_type = ' ∧\n'.join([
    '(1 / 2 : ℝ) ≤ 1 + clippedCenteredDelta n g r 512 rho z x',
    '|clippedCenteredDelta n g r 512 rho z x| ≤ studentizerClipBudget n r 512 rho z x',
    f'|clippedCenteredDelta n g r 512 rho z x| ≤ |{raw}|',
    '(0 < projectionV n g x → 0 < projectionV n g x * Real.sqrt (1 + clippedCenteredDelta n g r 512 rho z x))'])
literal_type = ' ∧\n'.join([
    f'clippedCenteredDelta n g r 512 rho z x = {raw}',
    '0 < projectionV n g x * Real.sqrt (1 + clippedCenteredDelta n g r 512 rho z x)',
    f'0 < {s}',
    f'projectionV n g x * Real.sqrt (1 + clippedCenteredDelta n g r 512 rho z x) = {s}',
    'clippedCenteredStatistic n g r 512 rho z x =\n  (if Real.sqrt (centeredSq n g r x) = 0 then 0 else\n    (projectionW n g x + residualStatisticD n r x) / Real.sqrt (centeredSq n g r x))'])
types = {
    'instP': 'IsProbabilityMeasure P', 'h512': '(0 : ℝ) ≤ 512', 'hz0': '(0 : ℝ) ≤ z',
    'hmeas': 'Measurable physical ∧ Measurable clipped ∧ MeasurableSet Eclip',
    'hPhysicalMeas': 'Measurable physical', 'hClippedMeas': 'Measurable clipped',
    'hEclipMeas': 'MeasurableSet Eclip', 'hOn': on_type, 'hxOn': on_result,
    'hCurrentClip': clip_type, 'hContract': f'|D2z x| ≤ |{raw}|',
    'hScaled': 'z ^ 2 * |D2z x| ≤ (1 / 32 : ℝ)', 'hLower': f'-(1 / 2 : ℝ) ≤ {raw}',
    'hLiteral': literal_type, 'hSafeSubset': 'Hsource ⊆ Ssafe',
    'hUnionSubset': '(Ssafeᶜ ∪ Eclip ∪ Zphysical) ⊆ Hsourceᶜ',
    'hRemainderSubset': '(E2 ∪ Z0) ⊆ Ssafeᶜ',
    'hSafeComplSubset': 'Ssafeᶜ ⊆ Hsourceᶜ',
    'hAllSubset': '(E2 ∪ Z0 ∪ Eclip ∪ Zphysical) ⊆ Hsourceᶜ',
    'hEclipSubset': 'Eclip ⊆ Hsourceᶜ', 'hSafeFee': 'P.real Ssafeᶜ ≤ payment',
    'hAllFee': 'P.real (E2 ∪ Z0 ∪ Eclip ∪ Zphysical) ≤ payment',
    'hEclipFee': 'P.real Eclip ≤ payment'}
declarations = []
for i, line in enumerate(lines):
    match = re.match(r'^( *)(have|letI) (\w+)', line)
    if not match:
        continue
    indent, kind, name = len(match[1]), match[2], match[3]
    end = i + 1
    while end < len(lines):
        if lines[end].strip() and len(lines[end]) - len(lines[end].lstrip(' ')) <= indent:
            break
        end += 1
    record = dict(name=name, kind=kind, fullStaticType=types[name], sourceSlice=span(i + 1, end))
    record['RHS'] = record['sourceSlice']['utf8'].split(':=', 1)[1].lstrip()
    record['scope'] = ('hOn proof after declaration' if indent == 4 else 'main proof after declaration')
    if name == 'hxOn':
        record['scope'] = 'containing set inclusion proof only, after declaration'
    declarations.append(record)
assert len(declarations) == 24
proof_end = len(lines) - (FREEZE / 'FROZEN-CLOSING.txt').read_bytes().count(b'\n')
on_decl = next(e for e in declarations if e['name'] == 'hOn')
for record in declarations:
    container = next((e for e in declarations
        if e['name'] != record['name'] and e['sourceSlice']['startLine'] < record['sourceSlice']['startLine']
        and record['sourceSlice']['endLine'] <= e['sourceSlice']['endLine']), None)
    record['availableAfterSourceLine'] = record['sourceSlice']['endLine']
    record['scopeEndLineInclusive'] = container['sourceSlice']['endLine'] if container else proof_end
write('LOCAL-DECLARATIONS.json', dict(status='STATIC_AUTHOR_TYPES_RHS_AND_SLICES_NOT_MACHINE_PP',
      sourceSHA256=sha(source), count=len(declarations), declarations=declarations))
ordinary = []
headlines = head.splitlines(keepends=True)
for i, line in enumerate(headlines):
    match = re.match(r'^ +let (\w+) : (.*)', line)
    if not match:
        continue
    end = i + 1
    while end < len(headlines) and not re.match(r'^            (?:let |MeasurableSet )', headlines[end]):
        end += 1
    exact = ''.join(headlines[i:end])
    lhs, rhs = exact.strip().removeprefix('let ').split(':=', 1)
    name, typ = lhs.split(':', 1)
    ordinary.append(dict(name=name.strip(), fullType=typ.strip(), RHS=rhs.strip(),
        exactFrozenText=exact, frozenHeadLines=[i + 1, end],
        scope='ordered intro establishes the frozen local definition through all later lets and final exact'))
assert len(ordinary) == 17
write('ORDINARY-LET-CONTEXT.json', dict(status='EXACT_FROZEN_ORDINARY_LETS_NOT_MACHINE_PP',
      count=len(ordinary), definitions=ordinary,
      classicalTactic='classical adds classical decidability; actual generated instance names require later server TYPE/VALUE inventory, not claimed here.'))
binding_types = {
    'cg': 'ℝ', 'hcg': '0 < cg', 'hFrontier': frontier_type,
    'C': 'ℝ', 'a': 'ℝ', 't0': 'ℝ', 'M': 'ℝ', 'hC': '0 ≤ C', 'ha': '0 ≤ a',
    'ht0': '0 < t0', 'hM': '0 ≤ M', 'n': 'ℕ', 'hn': hn_type,
    'r': 'Ω → Ω → ℝ', 'w': 'Ω → ℝ', 'hr': 'Measurable (Function.uncurry r)',
    'hr1': 'Integrable (Function.uncurry r) (μ.prod μ)',
    'hcR': "∀ᵐ o : Ω ∂μ, (∫ o' : Ω, r o o' ∂μ) = 0",
    'hcL': "∀ᵐ o' : Ω ∂μ, (∫ o : Ω, r o o' ∂μ) = 0",
    'hW': '∀ᵐ o : Ω ∂μ, 0 ≤ w o',
    'hWR': '∀ᵐ o : Ω ∂μ, w o ≤ boundedPolylogHeight C a n',
    'hSq': 'Integrable (fun o : Ω => (w o) ^ (2 : ℕ)) μ',
    'hSqBound': '(∫ o : Ω, (w o) ^ (2 : ℕ) ∂μ) ≤ M',
    'hEnv': '∀ᵐ p : Ω × Ω ∂μ.prod μ, |r p.1 p.2| ≤ w p.1 * w p.2',
    'hsym': "∀ o o' : Ω, r o o' = r o' o", 'rho': 'ℝ', 'z': 'ℝ',
    'hrho': '0 ≤ rho', 'hz': '(1 : ℝ) ≤ z',
    'hzWindow': 'z ≤ remainderWindowScale (tailScale M) t0 * Real.rpow (n : ℝ) (1 / 6 : ℝ)',
    'hGeometry': '(1 + rho) * z ≤ Real.sqrt (n : ℝ)',
    'hHMeas': 'MeasurableSet Hsource', 'hOldOn': old_on,
    'hOldZero': '({x : Fin n → Ω | projectionV n g x = 0} ∪ {x : Fin n → Ω | Real.sqrt (centeredSq n g r x) = 0}) ⊆ Hsourceᶜ',
    'hHfee': 'P.real Hsourceᶜ ≤ payment'}
binding_types.update(dict(zip(old_names, old_types)))
binding_types.update({o['name']: o['fullType'] for o in ordinary})
bindings = []


def binding(names, first, last, scope, overrides=None):
    overrides = overrides or {}
    bindings.append(dict(sourceSlice=span(first, last), scope=scope, bindings=[
        dict(name=name, fullStaticType=overrides.get(name, binding_types.get(name)),
             RHS=next((o['RHS'] for o in ordinary if o['name'] == name), None)) for name in names]))


binding(['cg', 'hcg', 'hFrontier'], line_of('  rcases Shao.OQ6.P54'),
        line_of('μ g hg hg2 hgmean hgsecond with'), 'rest of main proof')
binding(['C', 'a', 't0', 'M', 'hC', 'ha', 'ht0', 'hM'], line_of('  intro C a t0'),
        line_of('  intro C a t0'), 'rest of main proof')
binding(['n', 'hn'], line_of('  filter_upwards'), line_of('  filter_upwards'),
        'the single eventually body through final exact')
binding(['r', 'w', 'hr', 'hr1', 'hcR', 'hcL', 'hW', 'hWR', 'hSq', 'hSqBound', 'hEnv',
         'hsym', 'rho', 'z', 'hrho', 'hz', 'hzWindow', 'hGeometry'], line_of('  intro r w'),
        line_of('rho z hrho hz hzWindow hGeometry'), 'rest of main proof')
binding([o['name'] for o in ordinary], line_of('  intro q K P'), line_of('    Zphysical payment'),
        'the frozen ordered local let context; each name through final exact')
binding(['hHMeas', 'hOldOn', 'hOldZero', 'hHfee'], line_of('  rcases hn.2'),
        line_of('⟨hHMeas, hOldOn'), 'rest of main proof')
binding(['x', 'hx'], line_of('  have hOn ('), line_of('      clipped x = physical x := by'),
        'hOn proof only', {'x': 'Fin n → Ω', 'hx': 'x ∈ Hsource'})
binding(old_names, line_of('    rcases hOldOn'), line_of('hSourcePos, hFactor⟩'), 'hOn proof after rcases')
intro_specs = [
    ('hSafeSubset', '    intro x hx', ['x', 'hx'], ['Fin n → Ω', 'x ∈ Hsource']),
    ('hUnionSubset', '    intro x hx hxH', ['x', 'hx', 'hxH'], ['Fin n → Ω', 'x ∈ Ssafeᶜ ∪ Eclip ∪ Zphysical', 'x ∈ Hsource']),
    ('hRemainderSubset', '    intro x hx hxSafe', ['x', 'hx', 'hxSafe'], ['Fin n → Ω', 'x ∈ E2 ∪ Z0', 'x ∈ Ssafe']),
    ('hSafeComplSubset', '    intro x hx hxH', ['x', 'hx', 'hxH'], ['Fin n → Ω', 'x ∈ Ssafeᶜ', 'x ∈ Hsource']),
    ('hAllSubset', '    intro x hx', ['x', 'hx'], ['Fin n → Ω', 'x ∈ E2 ∪ Z0 ∪ Eclip ∪ Zphysical']),
    ('hEclipSubset', '    intro x hx', ['x', 'hx'], ['Fin n → Ω', 'x ∈ Eclip'])]
for parent, fragment, names, ts in intro_specs:
    decl = next(e for e in declarations if e['name'] == parent)
    first = line_of(fragment, decl['sourceSlice']['startLine'], decl['sourceSlice']['endLine'])
    binding(names, first, first, parent + ' proof only', dict(zip(names, ts)))
for fragment, names, ts, scope in [
    ('    rcases hx with (hxSafe', ['hxSafe', 'hxClip', 'hxPhysical'], ['x ∈ Ssafeᶜ', 'x ∈ Eclip', 'x ∈ Zphysical'], 'respective hUnionSubset branches'),
    ('    rcases hx with hxE2', ['hxE2', 'hxZ0'], ['x ∈ E2', 'x ∈ Z0'], 'respective hRemainderSubset branches'),
    ('    rcases hx with ((hxE2', ['hxE2', 'hxZ0', 'hxClip', 'hxPhysical'], ['x ∈ E2', 'x ∈ Z0', 'x ∈ Eclip', 'x ∈ Zphysical'], 'respective hAllSubset branches')]:
    first = line_of(fragment)
    binding(names, first, first, scope, dict(zip(names, ts)))
assert all(item['fullStaticType'] is not None for group in bindings for item in group['bindings'])
for group in bindings:
    first = group['sourceSlice']['startLine']
    container = next((e for e in declarations if e['sourceSlice']['startLine'] <= first
        and first <= e['sourceSlice']['endLine']), None)
    group['scopeStartLineInclusive'] = first
    group['scopeEndLineInclusive'] = container['sourceSlice']['endLine'] if container else proof_end
    if group['scope'].startswith('respective'):
        for item in group['bindings']:
            name = item['name']
            if 'hUnionSubset' in group['scope']:
                fragment = {'hxSafe': '· exact hxSafe', 'hxClip': '· exact hxClip',
                            'hxPhysical': '· exact (ne_of_gt hxOn'}[name]
            elif 'hRemainderSubset' in group['scope']:
                fragment = {'hxE2': '· change (1 / 4', 'hxZ0': '· exact (ne_of_gt hxSafe'}[name]
            else:
                fragment = {'hxE2': '· exact hSafeComplSubset (hRemainderSubset (Or.inl',
                            'hxZ0': '· exact hSafeComplSubset (hRemainderSubset (Or.inr',
                            'hxClip': '· exact hUnionSubset (Or.inl',
                            'hxPhysical': '· exact hUnionSubset (Or.inr'}[name]
            branch_first = line_of(fragment, first, group['scopeEndLineInclusive'])
            branch_end = branch_first
            if 'hRemainderSubset' in group['scope'] and name == 'hxE2':
                branch_end += 1
            item['branchScopeSlice'] = span(branch_first, branch_end)
write('BINDING-SCOPES.json', dict(status='COMPLETE_EXPLICIT_SOURCE_BINDINGS_NOT_MACHINE_PP',
    initialFrozenTheoremContext=head, groups=bindings,
    definitionalChanges=[dict(name='hxE2', scope='first hRemainderSubset branch after change',
      before='x ∈ E2', after='(1 / 4 : ℝ) < z ^ 2 * |D2z x|', RHS='definitionally identical proposition')]))
write('STATIC-FULL-TYPES.txt', 'STATIC AUTHOR FULL TYPES / COMPLETE RHS; NOT MACHINE PP\n\n' + '\n\n'.join(
      '[' + e['name'] + ' @ line ' + str(e['sourceSlice']['startLine']) + ']\n' + e['fullStaticType'] + '\nRHS:\n' + e['RHS'] for e in declarations))
contracts = []
for rel, name in [
    ('library/Shao/OQ6/P54ActualGoodsetFrontier.lean', 'fixed_original_boundedPolylog_goodset_frontier'),
    ('library/Shao/OQ5/P51/ClippedStudentizer.lean', 'clippedCenteredDelta_bounds'),
    ('library/Shao/OQ5/P51/LiteralClippedComparison.lean', 'literal_clippedCentered_comparison_on_projectionGood'),
    ('library/Shao/OQ6/OriginalPhysicalClippedTailTransfer.lean', 'physical_clipped_globally_measurable')]:
    data = (ROOT / rel).read_bytes()
    text = data.decode('utf-8')
    first = text.index('theorem ' + name)
    end = text.index(' := by', first)
    contract = text[first:end].encode('utf-8')
    contracts.append(dict(name=name, source=str(ROOT / rel), sourceSHA256=sha(data),
        startByteInclusive=len(text[:first].encode('utf-8')), endByteExclusive=len(text[:end].encode('utf-8')),
        contractSHA256=sha(contract), completeSourceDeclarationType=contract.decode('utf-8')))
write('PRODUCER-CONTRACTS.json', dict(status='EXACT_ACCEPTED_SOURCE_CONTRACTS_NO_OLD_AUDIT_REPLAY', producers=contracts))
calls = [
    dict(producer=contracts[0]['name'], actualArguments=['μ', 'g', 'hg', 'hg2', 'hgmean', 'hgsecond'],
         returnType='∃ cg : ℝ, 0 < cg ∧\n' + frontier_type, outputs=['cg', 'hcg', 'hFrontier']),
    dict(producer='hFrontier', actualArguments=['C', 'a', 't0', 'M', 'hC', 'ha', 'ht0', 'hM'],
         returnType='∀ᶠ n : ℕ in atTop,\n' + hn_type, outputs=['n', 'hn']),
    dict(producer='hn.2', actualArguments=['r', 'w', 'hr', 'hr1', 'hcR', 'hcL', 'hW', 'hWR', 'hSq',
         'hSqBound', 'hEnv', 'hsym', '512', 'rho', 'z', 'h512', 'hrho', 'hz', 'hzWindow'],
         returnType='MeasurableSet Hsource ∧\n(' + old_on + ') ∧\n(' + binding_types['hOldZero'] + ') ∧\nP.real Hsourceᶜ ≤ payment',
         outputs=['hHMeas', 'hOldOn', 'hOldZero', 'hHfee']),
    dict(producer=contracts[1]['name'], actualArguments=['n', 'g', 'r', '512', 'rho', 'z', 'x', 'h512', 'hrho', 'hz0'],
         returnType=clip_type, outputs=['hCurrentClip']),
    dict(producer=contracts[2]['name'], actualArguments=['n', 'g', 'r', 'rho', 'z', 'x', 'hn.1', 'hz',
         'hsym', 'hrho', 'hGeometry', 'hx.1', 'hLower'], returnType=literal_type, outputs=['hLiteral']),
    dict(producer=contracts[3]['name'], actualArguments=['n', 'g', 'r', 'hg', 'hr', '512', 'rho', 'z'],
         returnType='Measurable physical ∧ Measurable clipped ∧ MeasurableSet Eclip',
         localLetRHS={o['name']: o['RHS'] for o in ordinary if o['name'] in ['physical', 'clipped', 'Eclip']}, outputs=['hmeas'])]
write('PRODUCER-CALLS.json', dict(status='STATIC_ACTUAL_ARGUMENT_RETURN_TYPES_NOT_MACHINE_PP', calls=calls,
    foundationalApplications=[
      dict(term='inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => μ)))', type='IsProbabilityMeasure P', reason='P is definitionally sampleLaw n μ = Measure.pi (fun _ : Fin n => μ).'),
      dict(term='mul_le_mul_of_nonneg_left hContract (sq_nonneg z)', type=f'z ^ 2 * |D2z x| ≤ z ^ 2 * |{raw}|'),
      dict(term='(mul_le_mul_of_nonneg_left hContract (sq_nonneg z)).trans hRawScaled', type='z ^ 2 * |D2z x| ≤ (1 / 32 : ℝ)'),
      dict(term='measure_ne_top P Hsourceᶜ', type='P Hsourceᶜ ≠ ∞'),
      *[dict(term='measureReal_mono (μ := P) ' + subset + ' (measure_ne_top P Hsourceᶜ)',
             type='P.real ' + event + ' ≤ P.real Hsourceᶜ') for subset, event in [
             ('hSafeComplSubset', 'Ssafeᶜ'), ('hAllSubset', '(E2 ∪ Z0 ∪ Eclip ∪ Zphysical)'), ('hEclipSubset', 'Eclip')]]]))
fr = json.loads((FREEZE / 'frozen-declaration.json').read_text('utf-8'))
inputs = [fr['preamble'], fr['head'], fr['closing'], fr['sourceRoute']] + fr['bearingSourceBindings']
for item in inputs:
    actual = Path(item['path']).read_bytes()
    assert sha(actual) == item['sha256'] and len(actual) == item['bytes']
write('INPUT-BINDINGS.json', dict(freezeSHA256=sha((FREEZE / 'frozen-declaration.json').read_bytes()),
    activationSHA256=sha((FREEZE / 'ACTIVATION.json').read_bytes()), inputs=inputs))
offset = 0
segments = []
for label, path in [('frozenPreamble', FREEZE / 'FROZEN-PREAMBLE.txt'), ('frozenHead', FREEZE / 'FROZEN-HEAD.txt'),
                    ('completeProofBody', BASE / 'PROOF-BODY.txt'), ('frozenClosing', FREEZE / 'FROZEN-CLOSING.txt')]:
    raw_bytes = path.read_bytes()
    assert source[offset:offset + len(raw_bytes)] == raw_bytes
    segments.append(dict(label=label, path=str(path), startByteInclusive=offset,
        endByteExclusive=offset + len(raw_bytes), sha256=sha(raw_bytes), utf8=raw_bytes.decode('utf-8')))
    offset += len(raw_bytes)
assert offset == len(source)
write('SOURCE-SLICES.json', dict(sourceSHA256=sha(source), sourceBytes=len(source),
    convention='zero-based UTF8 byte offsets, end-exclusive; source line ranges one-based inclusive', segments=segments,
    allLocalDeclarationsAndExactRHSSlices='LOCAL-DECLARATIONS.json',
    allExplicitBindingSlices='BINDING-SCOPES.json', allProducerContractSlices='PRODUCER-CONTRACTS.json'))
print(json.dumps(dict(sourceSHA256=sha(source), lines=len(lines), localHaveLetI=len(declarations),
      ordinaryLets=len(ordinary), bindingGroups=len(bindings), acceptedProducerContracts=len(contracts))))
