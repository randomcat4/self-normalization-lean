from pathlib import Path
import datetime
import hashlib
import json
import re

B = Path('C:/game/shao lean')
O = B / 'drafts/oq56/unit254/author-01'
F = B / 'drafts/oq56/unit254/freeze-01'
P = O / 'OriginalLevelDependentCanonicalCoding.lean'
raw = P.read_bytes()
src = raw.decode('utf-8')
lines = src.splitlines(keepends=True)
offsets = [0]
for line in lines:
    offsets.append(offsets[-1] + len(line.encode('utf-8')))


def sha(b):
    return hashlib.sha256(b).hexdigest()


def dump(name, obj):
    (O / name).write_bytes((json.dumps(obj, ensure_ascii=False, indent=2) + '\n').encode('utf-8'))


def coord(a, b):
    text = ''.join(lines[a:b])
    assert raw[offsets[a]:offsets[b]] == text.encode('utf-8')
    return {'startLine': a + 1, 'endLineInclusive': b, 'startByte0': offsets[a],
            'endByteExclusive': offsets[b], 'sha256': sha(text.encode('utf-8')),
            'text': text}


def swap(text, env):
    if not env:
        return text
    pat = r"(?<![\w']) (?:"  # replace below; the explicit token boundaries include Unicode
    pat = r"(?<![\w'])(?:" + '|'.join(re.escape(x) for x in sorted(env, key=len, reverse=True)) + r")(?![\w'])"
    return re.sub(pat, lambda m: '(' + env[m.group(0)] + ')', text)


def split_and(text):
    out, begin, stack = [], 0, []
    pairs = {')': '(', ']': '[', '}': '{', '⟩': '⟨'}
    for i, c in enumerate(text):
        if c in '([{⟨':
            stack.append(c)
        elif c in ')]}⟩':
            assert stack and stack.pop() == pairs[c], (i, c, text[max(0, i-50):i+50])
        elif c == '∧' and not stack:
            out.append(text[begin:i].strip())
            begin = i + 1
    assert not stack
    out.append(text[begin:].strip())
    return out


def leading_lets(text, overrides=None):
    # Read a consecutive leading let telescope by its exact source indentation.
    ls = text.splitlines(keepends=True)
    decls, j, env = [], 0, {}
    while j < len(ls) and not ls[j].strip():
        j += 1
    while j < len(ls) and re.match(r'^\s*let(?:I)?\b', ls[j]):
        indent = len(ls[j]) - len(ls[j].lstrip())
        end = j + 1
        while end < len(ls):
            if ls[end].strip() and len(ls[end]) - len(ls[end].lstrip()) <= indent:
                break
            end += 1
        block = ''.join(ls[j:end]).strip()
        k, rest = block.split(None, 1)
        left, rhs = rest.split(':=', 1)
        if k == 'letI':
            name, ty = None, left.strip().removeprefix(':').strip()
        else:
            name, ty = left.split(':', 1)
            name, ty = name.strip(), ty.strip()
        rhs = rhs.strip()
        decls.append({'name': name, 'fullType': ty, 'fullRHS': rhs, 'exactBlock': block})
        if name:
            env[name] = (overrides or {}).get(name, swap(rhs, env))
        j = end
    return decls, ''.join(ls[j:]).strip(), env


def target(text, anchor):
    head = text.split(':= by\n', 1)[0]
    return head[head.index(anchor):].rstrip()


s253 = (B / 'drafts/oq56/unit253/author-01/OriginalLevelDependentCountablyGeneratedModel.lean').read_text(encoding='utf-8')
s251 = (B / 'drafts/oq56/unit251/author-01/OriginalLevelDependentClippedSourcePackage.lean').read_text(encoding='utf-8')
sambient = (B / 'library/Shao/OQ6/AmbientCanonicalCodingTransport.lean').read_text(encoding='utf-8')
t253 = target(s253, '    let f :')
t253 = t253.replace('Type v', 'Type').replace('Type w', 'Type')
t251 = target(s251, '    let g :')
# Instantiation changes only the original probability law and current-level parameter.
t251 = re.sub(r'(?<!\w)μ(?!\w)', 'μ₀', t251)
t251 = re.sub(r'(?<!\w)z(?!\w)', 'y', t251)
pkglets, pkgconj, pkgenv = leading_lets(t251, {'g': 'g₀', 'r': 'r₀', 'v': 'v₀', 'rho': 'rho₀', 'P': 'P₀', 'N': 'N'})
pkgparts = split_and(pkgconj)
expanded_pkgparts = [swap(x, pkgenv) for x in pkgparts]
assert len(pkgparts) == 24, len(pkgparts)
corestart = t253.index('      IsProbabilityMeasure μ₀ ∧')
coreparts = split_and(t253[corestart:])
assert len(coreparts) == 22, len(coreparts)
core_let_context = '''letI : MeasurableSpace Ω := m₀
let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
let rho₀ : ℝ := Real.sqrt v₀
'''

sample = 'Fin n → Ω'
aug = 'Fin n → Ω × ℝ'
ret = '{j : Fin n // j ≠ i}'
finiteparts = [
    '@IsProbabilityMeasure (Fin n → Ω) mN₀ P₀',
    'Measurable[mN, mN₀] (id : (Fin n → Ω) → Fin n → Ω)',
    'P₀ = @Measure.map (Fin n → Ω) (Fin n → Ω) mN mN₀ id P',
    '∀ (B : Type) (mB : MeasurableSpace B) (T : (Fin n → Ω) → B), Measurable[mN₀, mB] T → @Measure.map (Fin n → Ω) B mN₀ mB T P₀ = @Measure.map (Fin n → Ω) B mN mB T P'
]
frozen_head = (F / 'FROZEN-HEAD.txt').read_text(encoding='utf-8')
finaltarget = frozen_head[frozen_head.index('        @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ ∧'):].strip()
finalparts = split_and(finaltarget)


def fp(prefix):
    hits = [x for x in finalparts if x.startswith(prefix)]
    assert len(hits) == 1, (prefix, len(hits))
    return hits[0]


amb_compare = '''∀ (z : ℝ) (R : ℝ → ℝ → Prop), R ∈ comparisons →
MeasurableSet[mN₀] {ξ : Fin n → Ω | R (T0 ξ) z} ∧
MeasurableSet[mN₀] {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ)) (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))} ∧
MeasurableSet (Eη R z) ∧
ν (Eη R z) = P₀ {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ)) (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))} ∧
(∀ᵐ ξ ∂P₀, ξ ∈ ({ξ : Fin n → Ω | R (T0 ξ) z} ∆ {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ)) (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))}) → V0 ξ = 0) ∧
P₀ ({ξ : Fin n → Ω | R (T0 ξ) z} ∆ {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ)) (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))}) ≤ P₀ {ξ : Fin n → Ω | V0 ξ = 0} ∧
|P₀.real {ξ : Fin n → Ω | R (T0 ξ) z} - ν.real (Eη R z)| ≤ P₀.real {ξ : Fin n → Ω | V0 ξ = 0}'''
ambtypes = {
    'hνprob': 'IsProbabilityMeasure ν',
    'hQpres': 'MeasurePreserving Q P₀ P₀',
    'hqpres': 'MeasurePreserving q ν P₀',
    'hs': '(1 / 2 : ℝ) < s',
    'hηeval': fp('(∀ (i : Fin n) (x : Fin n → Ω × ℝ), η i x ='),
    'hηindep': 'iIndepFun η ν',
    'hηL2': fp('(∀ i : Fin n, Measurable (η i) ∧'),
    'hηInts': fp('(∀ i : Fin n, Integrable (η i) ν ∧'),
    'hηmean': fp('(∀ i : Fin n, (∫ x, η i x ∂ν) = 0)'),
    'hηenergy': '(∑ i : Fin n, ∫ x, (η i x) ^ 2 ∂ν) = 1',
    'hηnull': fp('(∀ (i : Fin n) (t : ℝ), ν'),
    'hVηnull': 'ν {x : Fin n → Ω × ℝ | Vη x = 0} = 0',
    'hVηpos': '∀ᵐ x ∂ν, 0 < Vη x',
    'hCmeas': 'Measurable[mAug, borel (Fin n → ℝ)] C',
    'hCcomap': 'MeasurableSpace.comap C (borel (Fin n → ℝ)) = mAug',
    'hfactor': fp('(∀ (H :'),
    'hretained': fp('(∀ (i : Fin n) (d :'),
    'hscalar': fp('(∃ G2 :'),
    'hT0meas': 'Measurable T0',
    'hTηmeas': '∀ z : ℝ, Measurable (Tη z)',
    'hZambientmeas': 'MeasurableSet[mN₀] {ξ : Fin n → Ω | V0 ξ = 0}',
    'hZmeas': 'MeasurableSet Z',
    'hZlaw': 'ν Z = P₀ {ξ : Fin n → Ω | V0 ξ = 0}',
    'hZreal': 'ν.real Z = P₀.real {ξ : Fin n → Ω | V0 ξ = 0}',
    'hsigned': fp('(∀ (z : ℝ) (x : Fin n → Ω × ℝ),'),
    'hcompare': amb_compare,
}
assert len(ambtypes) == 26
comparison_parts = [
    'MeasurableSet[mN₀] (A0 R z)', 'MeasurableSet[mN₀] (F0 R z)',
    'MeasurableSet (Eη R z)', 'ν (Eη R z) = P₀ (F0 R z)',
    '(∀ᵐ ξ ∂P₀, ξ ∈ (A0 R z ∆ F0 R z) → ξ ∈ Z0)',
    'P₀ (A0 R z ∆ F0 R z) ≤ P₀ Z0',
    '|P₀.real (A0 R z) - ν.real (Eη R z)| ≤ P₀.real Z0'
]

supplements = {
    'hmodel': t253,
    'hfiniteN': ' ∧\n'.join(finiteparts),
    'hstatisticsCurrent': ' ∧\n'.join(expanded_pkgparts),
    'hcanonical': ' ∧\n'.join('(' + x + ')' for x in ambtypes.values()),
    'hx': '(1 / 2 : ℝ) ≤ 1 + clippedCenteredDelta n g₀ r₀ 512 rho₀ y ξ',
    'hpoint': '(residualStatisticDDeleted n r₀ ζ i, residualEnergyJDeleted n r₀ ζ i, studentizerClipBudgetDeleted n r₀ 512 rho₀ y ζ i) = E_i (fun j : {j : Fin n // j ≠ i} => ζ j.val)',
    'hc': amb_compare.split('R ∈ comparisons →\n', 1)[1]
}

# Every source let/letI/have is preserved with its complete type/RHS and byte slice.
records = []
starts = []
for i, line in enumerate(lines):
    m = re.match(r'^(\s*)(letI|let|have)\b(.*)', line)
    if m:
        starts.append((i, len(m.group(1)), m.group(2)))
for a, indent, kind in starts:
    b = a + 1
    while b < len(lines):
        if lines[b].strip() and len(lines[b]) - len(lines[b].lstrip()) <= indent:
            break
        b += 1
    block = ''.join(lines[a:b]).rstrip()
    first = block.strip().split(None, 1)[1]
    left, rhs = first.split(':=', 1)
    if kind == 'letI':
        name, params, ty = 'anonymous-instance@' + str(a + 1), '', left.strip().removeprefix(':').strip()
    else:
        mm = re.match(r"([^\s:(]+)(.*)", left.strip(), re.S)
        name, tail = mm.group(1), mm.group(2)
        # Find the result colon outside all explicit binders.
        depth, colon = 0, None
        for ii, c in enumerate(tail):
            if c in '([{': depth += 1
            elif c in ')]}': depth -= 1
            elif c == ':' and depth == 0:
                colon = ii
                break
        if colon is None:
            params, ty = '', supplements[name]
        else:
            params, ty = tail[:colon].strip(), tail[colon + 1:].strip()
    parent_candidates = [(x, d, k) for x, d, k in starts if x < a and d < indent and x >= 183]
    enclosing = 'theorem body' if a >= 183 else 'frozen theorem result telescope'
    # A complete byte context makes all lexical dependencies inspectable; no inferred machine ownership is claimed.
    records.append({'kind': kind, 'name': name, 'sourceParameters': params,
                    'fullType': ('∀ ' + params + ',\n' + ty) if params else ty,
                    'resultType': ty, 'fullRHS': rhs.strip(),
                    'typeOrigin': 'explicit source annotation' if ':' in left else 'full source-bound producer instantiation',
                    'scope': {'enclosing': enclosing, 'declarationIndent': indent,
                              'contextFromLine': 16, 'contextThroughLine': a + 1,
                              'sourceResultLocalsRemainLexical': a < 183},
                    'sourceSlice': coord(a, b)})
assert all(x['fullType'] and x['fullRHS'] for x in records)

# Exact source lexical scopes: enclosing proof-have or bullet branch, otherwise the whole theorem.
scope_ranges = []
for rr in records:
    if rr['kind'] == 'have' and rr['fullRHS'].startswith('by'):
        scope_ranges.append((rr['sourceSlice']['startLine'], rr['sourceSlice']['endLineInclusive'],
                             rr['scope']['declarationIndent'], 'proof of ' + rr['name']))
for aa, ll in enumerate(lines):
    bm = re.match(r'^(\s*)· ', ll)
    if bm:
        dd = len(bm.group(1))
        bb = aa + 1
        while bb < len(lines):
            if lines[bb].strip() and len(lines[bb]) - len(lines[bb].lstrip()) <= dd:
                break
            bb += 1
        scope_ranges.append((aa + 1, bb, dd, 'bullet branch at ' + str(aa + 1)))


def lexical_scope(line_no, indent):
    candidates = [r for r in scope_ranges if r[0] < line_no <= r[1] and r[2] < indent]
    if candidates:
        a, b, dd, owner = max(candidates, key=lambda r: (r[2], r[0]))
        return {'enclosing': owner, 'contextFromLine': a, 'visibleThroughLine': b,
                'declarationIndent': indent, 'coordinateConvention': '1-based inclusive'}
    return {'enclosing': 'frozen result telescope' if line_no < 183 else 'whole theorem proof',
            'contextFromLine': 16 if line_no < 183 else 184,
            'visibleThroughLine': 182 if line_no < 183 else 523,
            'declarationIndent': indent, 'coordinateConvention': '1-based inclusive'}


for rr in records:
    rr['scope'] = lexical_scope(rr['sourceSlice']['startLine'], rr['scope']['declarationIndent'])

# Source-level parameter/producer binding inventory, separate from compiled module owners.
producer = []


def add_bindings(a, b, origin, pairs, context='same frozen theorem and enclosing source lexical scope'):
    indent = len(lines[a])-len(lines[a].lstrip())
    producer.append({'line': a + 1, 'origin': origin, 'scope': lexical_scope(a + 1, indent),
                     'producerSlice': coord(a, b),
                     'bindings': [{'name': n, 'fullDependentType': t} for n, t in pairs]})


resultdefs = {x['name']: x for x in records if x['kind'] == 'let' and x['sourceSlice']['startLine'] < 183}
introtypes = {n: (d['resultType'] + '\n:= ' + d['fullRHS']) for n, d in resultdefs.items()}
introtypes.update({'n': 'ℕ', 'hn': '4 ≤ n', 'y': 'ℝ', 'hy': '1 ≤ y',
                  'hywindow': 'y ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ))',
                  'ε': 'ℝ', 'hε': '0 < ε', 'hεsmall': 'ε < 1 / (4 * Real.sqrt (n : ℝ))'})
for a, line in enumerate(lines):
    if a < 183:
        continue
    trimmed = line.strip().removeprefix('· ').strip()
    if trimmed.startswith('intro '):
        b = a + 1
        names = trimmed[len('intro '):].strip().split()
        if names and names[0] == 'mN':
            while b < len(lines) and len(lines[b]) - len(lines[b].lstrip()) > 2:
                names.extend(lines[b].strip().split())
                b += 1
        pairs = []
        for n in names:
            if a + 1 in (185, 192, 223, 224):
                t = introtypes[n]
            elif n == 'j': t = '{j : Fin n // j ≠ i}'
            elif n == 'x': t = aug
            elif n == 'z': t = 'ℝ'
            elif n == 'R': t = 'ℝ → ℝ → Prop'
            elif n == 'hR': t = 'R ∈ comparisons'
            elif n == 'ξ': t = sample
            elif n == 'hdiff': t = 'ξ ∈ (A0 R z ∆ F0 R z)'
            elif n == 'heq':
                t = ('(projectionW n g ξ + D1 ξ) / (projectionV n g ξ * Real.sqrt (1 + D2 ξ)) = z'
                     if a + 1 == 508 else '(projectionW n g ξ + D1 ξ) = z * (projectionV n g ξ * Real.sqrt (1 + D2 ξ))')
            else: raise AssertionError(('uncovered intro', a + 1, n))
            pairs.append((n, t))
        add_bindings(a, b, 'intro', pairs)
    elif trimmed.startswith('funext '):
        names = trimmed[7:].split()
        add_bindings(a, a+1, 'funext', [(n, 'Fin n' if n == 'i' else sample) for n in names])
    elif trimmed.startswith('filter_upwards '):
        add_bindings(a, a+1, 'filter_upwards', [('x', aug), ('hx', '0 < Vη x')])
    elif trimmed.startswith('by_contra '):
        add_bindings(a, a+1, 'by_contra', [('hnot', 'ξ ∉ Z0')])
    elif trimmed.startswith('rcases '):
        b = a + 1
        while b < len(lines) and lines[b].strip() and len(lines[b]) - len(lines[b].lstrip()) > len(line)-len(line.lstrip()):
            b += 1
        command = ''.join(lines[a:b]).strip()
        if command.startswith('rcases hmodel '):
            hbase = t253[t253.index('      let μ₀ :'):]
            pairs = [('m₀', 'MeasurableSpace Ω'), ('hm₀', 'm₀ ≤ mΩ'),
                     ('hcg', '@MeasurableSpace.CountablyGenerated Ω m₀'),
                     ('hh₀', 'Measurable[m₀.prod m₀, borel ℝ] (fun t : Ω × Ω => h t.1 t.2)'),
                     ('hf₀', '∀ k : ℕ, Measurable[m₀, borel ℝ] (fun _o : Ω => (0 : ℝ))'), ('hbase', hbase)]
        elif command.startswith('rcases hbase '):
            names = ['hμ₀prob','hμ₀map','hgpoint','hrpoint','hvpoint','hrhopoint','hrow','hh₂₀','hcenter₀','hgmeas₀','hg₂₀','hgmean₀','hgsecond₀','hrmeas₀','hr₂₀','hrsymm₀','hrcanonical₀','hglaw₀','hglp₀','hpair₀','hfinite','hstatistics']
            pairs = [(n, core_let_context + t) for n, t in zip(names, coreparts)]
        elif command.startswith('rcases hfiniteN '):
            pairs = list(zip(['hP₀prob','hidmeas','hP₀map','hfiniteLaw'], finiteparts))
        elif command.startswith('rcases hstatisticsCurrent '):
            names = ['hWm','hVm','hD1m','hJm','hAm','hBm','hdm','hD2m','hsm','hTclipm','hTactualm','hfullTestm','hZ0m','hZsm','hglobal','hzero','hphysicalzero','hdeleted','hcurrentTail']
            pairs = list(zip(names[:18], expanded_pkgparts[:18])) + [('hcurrentTail', ' ∧\n'.join(expanded_pkgparts[18:]))]
        elif command.startswith('rcases hcanonical '):
            pairs = list(ambtypes.items())
        elif command.startswith('rcases hdeleted i '):
            base = 'residualStatisticDDeleted n r₀'
            energy = 'residualEnergyJDeleted n r₀'
            budget = 'studentizerClipBudgetDeleted n r₀ 512 rho₀ y'
            A = '(fun ζ : Fin n → Ω => |residualStatisticD n r₀ ζ|)'
            Ad = '(fun ζ : Fin n → Ω => |residualStatisticDDeleted n r₀ ζ i|)'
            Bgt = '(studentizerClipBudget n r₀ 512 rho₀ y)'
            cap = '(fun ζ : Fin n → Ω => min |y * (g₀ (ζ i) / N)| 1)'
            deletedtest = f'fun ζ : Fin n → Ω => {cap} ζ * (|{A} ζ - {Ad} ζ| + y * |{Bgt} ζ - {budget} ζ i|)'
            pairs = [('hcapi', f'Measurable {cap}'),
                     ('hDdi', f'Measurable (fun ζ : Fin n → Ω => {base} ζ i)'),
                     ('hJdi', f'Measurable (fun ζ : Fin n → Ω => {energy} ζ i)'),
                     ('hAdi', f'Measurable {Ad}'),
                     ('hBdi', f'Measurable (fun ζ : Fin n → Ω => {budget} ζ i)'),
                     ('htesti', f'Measurable ({deletedtest})'),
                     ('E_i', '({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ'),
                     ('hEmeas', 'Measurable E_i'),
                     ('hEpoint', f'∀ ζ : Fin n → Ω, ({base} ζ i, {energy} ζ i, {budget} ζ i) = E_i (fun j : {{j : Fin n // j ≠ i}} => ζ j.val)')]
        elif command.startswith('rcases hretained '):
            m = re.match(r'rcases hretained i (d[DJB]) (hd[DJB]) with ⟨(F[DJB]),', command)
            d, hd, name = m.groups()
            pairs = [(name, '({j : Fin n // j ≠ i} → ℝ) → ℝ'),
                     ('h'+name+'m', f'Measurable[borel ({{j : Fin n // j ≠ i}} → ℝ), borel ℝ] {name}'),
                     ('h'+name+'point', f'∀ y : {{j : Fin n // j ≠ i}} → Ω × ℝ, {d} y = {name} (fun j => ηlocal j.val (y j))'),
                     ('h'+name+'lift', f'Measurable[borel (Fin n → ℝ), borel ℝ] (fun t : Fin n → ℝ => {name} (fun j => t j.val))'),
                     ('h'+name+'full', f'∀ x : Fin n → Ω × ℝ, {d} (fun j => x j.val) = {name} (fun j => η j.val x)')]
        elif command.startswith('rcases hcomparison0 '):
            pairs = list(zip(['hA0m','hF0m','hEηm','hEηlaw','hAFae','hAF₀','hreal₀'], comparison_parts))
        elif command.startswith('rcases hR '):
            pairs = [('rfl branch '+str(i+1), 'R = '+x) for i, x in enumerate(['(fun a b : ℝ => a ≤ b)','(fun a b : ℝ => a < b)','(fun a b : ℝ => b ≤ a)','(fun a b : ℝ => b < a)','(fun a b : ℝ => a = b)'])]
        elif command.startswith('rcases Set.mem_symmDiff.mp hdiff '):
            pairs = [('ha@left', 'ξ ∈ A0 R z'), ('hf@left', 'ξ ∉ F0 R z'),
                     ('hf@right', 'ξ ∈ F0 R z'), ('ha@right', 'ξ ∉ A0 R z')]
        else:
            raise AssertionError(('uncovered destruct', a+1, command))
        add_bindings(a, b, 'rcases', pairs)

dump('SOURCE-INVENTORY.json', {'schema':'unit254-complete-source-local-inventory-v1',
    'sourceSHA256':sha(raw), 'coordinateConvention':'UTF8 byte offsets 0-based half-open; line numbers 1-based inclusive',
    'actualModuleOwners':None, 'machinePending':True, 'sourceLocalRecordCount':len(records), 'records':records})
dump('PRODUCER-BINDINGS.json', {'schema':'unit254-source-level-intro-destruct-binding-inventory-v1',
    'sourceSHA256':sha(raw), 'bindingCount':sum(len(x['bindings']) for x in producer),
    'namedBindingEntries':sum(len(x['bindings']) for x in producer)-5, 'rflSubstitutionBranchEntries':5,
    'actualModuleOwners':None, 'notMachinePP':True,
    'dependentContext':'Complete exact source local types/RHS/byte scopes in SOURCE-INVENTORY; current inner g₀/r₀/rho₀ deliberately distinct until explicit rewrites.',
    'records':producer})
dump('PRODUCER-TYPES.json', {'schema':'unit254-bearing-producer-types-v1',
    'qualified253CompleteResult':t253, 'qualified251CurrentMu0YCompleteResult':t251,
    'currentPacketLetTelescope':pkglets, 'coreDependentLetContext':core_let_context, 'core22FullTypes':coreparts,
    'ambient26InstantiatedFullTypes':ambtypes,
    'canonicalAmbientProducerFullSource':sambient,
    'note':'Source-bound dependent types, not elaborated TYPE evidence; no old producer machine checks repeated.'})

md = ['# 第254单元完整源码局部库存\n', '库存仅描述当前源中的局部项；实际编译所属声明数为 null，待服务器。\n']
for x in records:
    q = x['sourceSlice']
    md += [f"## {x['kind']} {x['name']} — 第{q['startLine']}–{q['endLineInclusive']}行\n",
           f"UTF8字节[{q['startByte0']},{q['endByteExclusive']})；完整声明片段SHA256 `{q['sha256']}`。\n",
           '完整依赖类型：\n```lean\n'+x['fullType']+'\n```\n',
           '完整右端／证明体：\n```lean\n'+x['fullRHS']+'\n```\n',
           '词法范围：'+json.dumps(x['scope'],ensure_ascii=False)+'\n']
(O/'SOURCE-INVENTORY.md').write_bytes(('\n'.join(md).rstrip()+'\n').encode('utf-8'))
md = ['# 第254单元全部引入与产生绑定\n', '完整依赖上下文由冻结声明与 SOURCE-INVENTORY 的精确源码坐标共同给出；以下无省略类型。\n']
for x in producer:
    md += [f"## {x['origin']} — 第{x['line']}行\n", '```lean\n'+x['producerSlice']['text'].rstrip()+'\n```\n']
    for v in x['bindings']:
        md += ['`'+v['name']+'`\n```lean\n'+v['fullDependentType']+'\n```\n']
(O/'INTRO-AND-DESTRUCTURING-INVENTORY.md').write_bytes(('\n'.join(md).rstrip()+'\n').encode('utf-8'))

# Static checks only: no Lean, lake, elaboration, server or audit invocation.
ack = json.loads((O/'READ_ACK.json').read_text(encoding='utf-8'))
input_results = []
for d in ack['inputs']:
    data = Path(d['path']).read_bytes()
    ok = sha(data)==d['sha256'] and len(data)==d['bytes']
    input_results.append({'path':d['path'],'sha256':sha(data),'bytes':len(data),'unchanged':ok})
assert all(x['unchanged'] for x in input_results)
composition = (F/'FROZEN-PREAMBLE.txt').read_bytes()+(F/'FROZEN-HEAD.txt').read_bytes()+b':= by\n'+(O/'PROOF-BODY.txt').read_bytes()+(F/'FROZEN-CLOSING.txt').read_bytes()
forbidden = re.findall(r'(?<![\w])(?:sorry|admit|axiom|unsafe|native_decide)(?![\w])', src)
top = re.findall(r'(?m)^(theorem|lemma|def|abbrev|instance|opaque|axiom)\b([^\n]*)', src)
assert composition == raw
assert not forbidden
assert len(top)==1 and top[0][0]=='theorem'
assert not raw.startswith(b'\xef\xbb\xbf') and b'\r' not in raw
assert raw.endswith(b'\n') and not raw.endswith(b'\n\n')
assert (F/'FROZEN-HEAD.txt').read_bytes().count(b'\n')==167
assert 'zeroLevel' not in src and 'B1del' not in src
assert 'intro n hn y hy hywindow ε hε hεsmall' in src
allrounds = [x['sourceSlice'] for x in records]+[x['producerSlice'] for x in producer]
assert all(raw[q['startByte0']:q['endByteExclusive']].decode('utf-8')==q['text'] for q in allrounds)
counts = {'sourceBytes':len(raw),'sourceLF':raw.count(b'\n'),
          'frozenHeadLF':(F/'FROZEN-HEAD.txt').read_bytes().count(b'\n'),
          'proofLF':(O/'PROOF-BODY.txt').read_bytes().count(b'\n'),
          'sourcePublicTheorems':len(top),'sourceTopLevelHelpersDefsInstances':0,
          'localLet':sum(x['kind']=='let' for x in records),
          'localLetI':sum(x['kind']=='letI' for x in records),
          'localHave':sum(x['kind']=='have' for x in records),
          'introDestructCommands':len(producer),
          'introDestructBindings':sum(len(x['bindings']) for x in producer),
          'namedBindingEntries':sum(len(x['bindings']) for x in producer)-5, 'rflSubstitutionBranchEntries':5,
          'sourceSliceRoundtrips':len(allrounds),'inputBindings':len(input_results),
          'actualModuleOwners':None,'actualTheorems':None,'actualNonTheorems':None}
dump('INPUT-HASH-BINDINGS.json', input_results)
dump('STATIC-CHECK.json', {'schema':'unit254-author-static-only-v1','atUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),
     'sourceSHA256':sha(raw),'status':'PASS','exactFrozenComposition':True,'fullSourceSliceRoundtrip':True,
     'UTF8NoBOM':True,'LFOnly':True,'singleFinalNewline':True,'frozenHeadPreserved':True,
     'forbiddenTokens':forbidden,'onePublicTheoremNoTopLevelHelpers':True,'allInputsUnchanged':True,
     'counts':counts,'LeanExecuted':False,'kernelChecked':False,'qualified':False,'machinePending':True})
print(json.dumps({'status':'STATIC_PASS_ONLY','sourceSHA256':sha(raw),'counts':counts},ensure_ascii=False))
