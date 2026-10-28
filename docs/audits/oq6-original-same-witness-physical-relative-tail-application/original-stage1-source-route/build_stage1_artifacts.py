from pathlib import Path
import copy
import datetime
import hashlib
import json
import re

ROOT = Path('C:/game/shao lean')
PLAN = ROOT / 'drafts/oq56/next-source/oq6-original-same-witness-physical-relative-tail-planned'
OWN = PLAN / 'author-stage1-01'
ACT = PLAN / 'STAGE1-ACTIVATION.json'
OLD = ROOT / 'drafts/oq56/unit248'
NEW_NAME = 'actual_original_same_witness_physical_relative_tail_application'
OLD_NAME = 'actual_original_same_witness_physical_paid_scalar_tail_application'
MODULE = 'Shao.OQ6.OriginalSameWitnessPhysicalRelativeTailApplication'
NOW = datetime.datetime.now(datetime.timezone.utc).isoformat()
assert not (OWN / 'lastzeroRELEASE.json').exists(), 'This role is sealed; no later writes are permitted.'


def read(p):
    return Path(p).read_text(encoding='utf-8')


def binding(p):
    p = Path(p)
    b = p.read_bytes()
    return {'path': p.as_posix(), 'sha256': hashlib.sha256(b).hexdigest(), 'bytes': len(b)}


def put(name, value):
    text = value if isinstance(value, str) else json.dumps(value, ensure_ascii=False, indent=2) + '\n'
    assert '\r' not in text and not text.startswith('\ufeff')
    (OWN / name).write_text(text, encoding='utf-8', newline='\n')


activation = json.loads(read(ACT))
assert binding(ACT)['sha256'] == '33a03c2ea1f6427b14e1d45b13989d057112cfd9f9b91f554682e7fc9bf3c6e2'
for item in activation['inputs']:
    assert binding(item['path']) == item
release248 = json.loads(read(OLD / 'author-01/lastzeroRELEASE.json'))
assert release248['FINALWRITE'] and release248['noFurtherWritesAfterThisRelease']
assert all(v == 0 for v in release248['sixZero'].values())
assert binding(release248['source']['path']) == release248['source']
freeze = json.loads(read(OLD / 'freeze-01/frozen-declaration.json'))
for item in freeze['files']:
    assert binding(item['path']) == item
old_head = read(OLD / 'freeze-01/FROZEN-HEAD.txt')
old_inventory = json.loads(read(OLD / 'freeze-01/INTERFACE-INVENTORY.json'))
old_contexts = json.loads(read(OLD / 'author-01/ACTUAL-PROP-CONTEXTS.json'))
ref237 = json.loads(read(ROOT / 'drafts/oq56/unit237/author-stage1-01/INTERFACE-INVENTORY.json'))

# Parse complete literal let declarations already present in the bound public head.
def old_let(name, occurrence=1):
    matches = list(re.finditer(r'(?m)^([ ]*)let ' + re.escape(name) + r' : ', old_head))
    m = matches[occurrence - 1]
    start = m.start()
    tail = old_head[m.end():]
    following = re.search(r'(?m)^' + re.escape(m.group(1)) + r'(?:let |Measurable\[|\(1 : ℝ\))', tail)
    assert following is not None, name
    return old_head[start:m.end() + following.start()].rstrip('\n')


source_cost = old_let('sourceCost0', 2)
L0 = old_let('L0', 2)
physical = old_let('Tphysical')
# Only indentation changes in a repeated let at the new branch's scope.
physical = '\n'.join(line[2:] if line.startswith('  ') else line for line in physical.splitlines())

contract_start = '''      (∀ (Cenv aenv t0 Menv : ℝ)
          (hCenv : 0 ≤ Cenv) (haenv : 0 ≤ aenv)
          (ht0 : 0 < t0) (hMenv : 0 ≤ Menv),
        let cPaid : ℝ := min
          (remainderWindowScale (Shao.OQ6.BoundedProductEnvelopeTails.tailScale Menv) t0)
          (min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ)))
        0 < cPaid ∧
        ∀ᶠ n : ℕ in Filter.atTop,
          4 ≤ n ∧
          1 + rho ≤ Real.sqrt (n : ℝ) ∧
          (1 : ℝ) ≤ cPaid * Real.rpow (n : ℝ) (1 / 6 : ℝ) ∧
          ∀ (w : Ω → ℝ)
            (hW : ∀ᵐ o : Ω ∂μ, 0 ≤ w o)
            (hWR : ∀ᵐ o : Ω ∂μ,
              w o ≤ boundedPolylogHeight Cenv aenv n)
            (hSq : Integrable[mΩ] (fun o : Ω => (w o) ^ (2 : ℕ)) μ)
            (hSqBound : (∫ o : Ω, (w o) ^ (2 : ℕ) ∂μ) ≤ Menv)
            (hEnv : ∀ᵐ t : Ω × Ω ∂(@Measure.prod Ω Ω mΩ mΩ μ μ),
              |r t.1 t.2| ≤ w t.1 * w t.2)
            (z : ℝ) (hz : (1 : ℝ) ≤ z)
            (hzPaidWindow : z ≤ cPaid * Real.rpow (n : ℝ) (1 / 6 : ℝ)),
        let mN : MeasurableSpace (Fin n → Ω) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => mΩ)
        let P : @Measure (Fin n → Ω) mN :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => mΩ) (fun _ : Fin n => μ)
        let N : ℝ := Real.sqrt (n : ℝ)
        let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => g (ζ i) / N
        let D1 : (Fin n → Ω) → ℝ := residualStatisticD n r
'''
relative = '''        ∀ (C1 C2 C3 C4 : ℝ)
            (hSZcBudget : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
              cBudget C1 C2 C3 C4)
            (hzMomentWindow : β = 0 ∨
              (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                Real.rpow (n : ℝ) ((p - 2) / (2 * p)))),
          Shao.standardNormalTail z *
              (Real.exp (-C1 * L0) * (1 - C2 * sourceCost0) - R) ≤
            P.real {ζ : Fin n → Ω | z ≤ Tphysical ζ} ∧
          P.real {ζ : Fin n → Ω | z ≤ Tphysical ζ} ≤
            Shao.standardNormalTail z *
              (Real.exp (C3 * L0) * (1 + C4 * sourceCost0) + 2 * R)'''
contract = contract_start + L0 + '\n' + source_cost + '\n' + physical + '''
        let R : ℝ := Real.exp (-(t0 / (2 : ℝ)) * Real.rpow (n : ℝ) (1 / 3 : ℝ))
''' + relative + ')\n'
assert contract.count('let ') == 10
new_head = old_head.rstrip('\n').replace(OLD_NAME, NEW_NAME, 1) + ' ∧\n' + contract
preamble = '''import Shao.OQ6.OriginalSameWitnessPhysicalPaidTailApplication
import Shao.OQ6.OriginalExceptionalTailAbsorption
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Basic

set_option autoImplicit false
universe u
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology MeasureTheory symmDiff
open Shao.OQ5.P51
namespace Shao.OQ6.OriginalSameWitnessPhysicalRelativeTailApplication
noncomputable section

'''
closing = '\nend Shao.OQ6.OriginalSameWitnessPhysicalRelativeTailApplication\n'
put('CANDIDATE-PREAMBLE.txt', preamble)
put('CANDIDATE-HEAD.txt', new_head)
put('CANDIDATE-CLOSING.txt', closing)
put('CANDIDATE-DECLARATION.lean', preamble + new_head + closing)
put('NEW-RELATIVE-TAIL-CONTRACT.txt', contract)

def parse_lets(text, end_marker=None):
    matches = list(re.finditer(r'(?m)^([ ]*)let ([^\s:]+) : ', text))
    result = []
    for i, m in enumerate(matches):
        end = matches[i+1].start() if i+1 < len(matches) else text.index(end_marker)
        chunk = text[m.end():end].rstrip()
        if m.group(2) == 'cPaid':
            chunk = chunk[:chunk.index('\n        0 < cPaid')]
        typ, rhs = chunk.split(' :=', 1)
        result.append({'name': m.group(2), 'type': typ.strip(), 'rhs': rhs.strip(),
                       'scope': 'new common-paid branch: cPaid after fixed envelope scalars and before eventual n; all remaining lets after same n/w/z, original mΩ/μ',
                       'branch': 'new-relative-paid', 'contextId': 'N02' if m.group(2) == 'cPaid' else 'N05'})
    return result

new_ordinary = parse_lets(contract, '        ∀ (C1 C2 C3 C4')
ordinary = copy.deepcopy(old_inventory['publicOrdinary']) + new_ordinary
for i, row in enumerate(ordinary, 1):
    row['publicOccurrence'] = i
old_names = re.findall(r'^\s*let\s+([^\s:]+)\s*:', old_head, re.M)
new_names = re.findall(r'^\s*let\s+([^\s:]+)\s*:', new_head, re.M)
assert old_names == [r['name'] for r in old_inventory['publicOrdinary']]
assert new_names == [r['name'] for r in ordinary]
payment_rhs = '''(3 : ℝ) * Real.exp (-boundedPolylogMomentOrder t0 n) + Real.exp (-cg * (n : ℝ)) +
  (4 : ℝ) * Real.exp (-(z * Real.sqrt (n : ℝ)) / (2 : ℝ))'''
payment1_rhs = '''(3 : ℝ) * Real.exp (-boundedPolylogMomentOrder t0 n) + Real.exp (-cg * (n : ℝ)) +
  (4 : ℝ) * Real.exp (-Real.sqrt (n : ℝ) / (2 : ℝ))'''
new_optional = [dict(name=name, type='ℝ', rhs=rhs, scope='OPTIONAL only new paid-branch fixed n/w/z; identical scalar expansion to SAME248 local payment, not a new fee assumption', contextId='N06')
                for name, rhs in [('payment', payment_rhs), ('payment1', payment1_rhs)]]
optional = copy.deepcopy(old_inventory['optionalOrdinary']) + copy.deepcopy(new_ordinary) + new_optional

result248 = old_head[old_head.index('    let g :'):].rstrip()
cg_prop = old_head[old_head.index('    ∃ cg :'):].rstrip()
model_prop = old_head[old_head.index('    ∃ (m₀ :'):].rstrip()
retained248 = old_head[old_head.index('      IsProbabilityMeasure μ₀ ∧'):].rstrip()
original_telescope = old_head[old_head.index('  ∀'):old_head.index('    let g :')]
global_lets = old_head[old_head.index('    let g :'):old_head.index('    Measurable[mΩ')]
env_start = old_head.index('      (∀ (Cenv aenv t0 Menv : ℝ)')
old_env = old_head[env_start:].rstrip()
# Remove precisely the outer parentheses of the old second conjunct, retaining internal closes.
old_env_type = old_env.strip()[1:-1]
old_n_type = old_env_type[old_env_type.index('          4 ≤ n ∧'):].rstrip()
old_at_current = old_env_type[old_env_type.index('        let mN :'):].rstrip()
assert old_at_current.endswith(')))')
new_local_start = contract.index('        let mN :')
new_local_end = contract.index('        ∀ (C1 C2 C3 C4')
new_lets_text = contract[new_local_start:new_local_end]
env_binders = contract[contract.index('(∀')+2:contract.index('        let cPaid :')].rstrip(',\n ')
paid_let = contract[contract.index('        let cPaid :'):contract.index('        0 < cPaid')]
late_binders = contract[contract.index('          ∀ (w :'):new_local_start]

contexts = [
    {'id':'N00','parent':None,'text':original_telescope,'role':'exact original16 outer telescope; before producer248'},
    {'id':'N01','parent':'N00','text':global_lets,'role':'same original six global lets; rho fixed here BEFORE cg/model/envelope/eventual n'},
    {'id':'N01c','parent':'N01','text':'let cg : ℝ := Classical.choose hCg\n','role':'sole SAME248 cg, no235/237/239 selector'},
    {'id':'N01m','parent':'N01c','text':'let m₀ : MeasurableSpace Ω := Classical.choose hModel\n','role':'sole SAME248 m₀; hm₀/hcg proof witnesses are extracted here before μ₀'},
    {'id':'N01s','parent':'N01m','text':'(hm₀ : m₀ ≤ mΩ)\n(hcg : @MeasurableSpace.CountablyGenerated Ω m₀)\nlet μ₀ : @Measure Ω m₀ := μ.trim hm₀\nletI : MeasurableSpace Ω := m₀\nletI : MeasurableSpace.CountablyGenerated Ω := hcg\n','role':'same μ₀ and selected-space instances only after hm₀/hcg; original mΩ remains explicit on original-law observables'},
    {'id':'N02','parent':'N01s','text':env_binders+'\n'+paid_let,'role':'fixed Cenv/aenv/t0/Menv and exact deterministic cPaid before eventual n'},
    {'id':'N03','parent':'N02','text':'(n : ℕ)\n','role':'same eventual n, before every late w/z'},
    {'id':'N04','parent':'N03','text':late_binders,'role':'same complete late envelope and closed paid-window quantifiers'},
    {'id':'N05','parent':'N04','text':new_lets_text,'role':'exact new original sample law and original sourceCost/physical zero branch'},
    {'id':'N06','parent':'N05','text':'let payment : ℝ := '+payment_rhs+'\nlet payment1 : ℝ := '+payment1_rhs+'\n','role':'only two optional proof-local scalar aliases'},
    {'id':'N07','parent':'N06','text':relative[:relative.index('          Shao.standardNormalTail')],'role':'unchanged original externalSZ input and strict-moment-window alternative; not new assumptions'},
]

props = []
def prop(name, typ, context, purpose):
    props.append({'name':name,'fullType':typ,'contextId':context,'scope':next(c['role'] for c in contexts if c['id']==context),
                  'kind':'PROPOSED_PROOF_OBLIGATION_NOT_INPUT_PREMISE_NOT_IMPLEMENTED','purpose':purpose})

prop('h248', result248, 'N00', 'sole permitted inferred producer fact; prospective until exact248 qualification; call before global lets/choices')
prop('hCg', cg_prop, 'N01', 'exact producer248 existential proposition after stripping only global conjunction prefix')
prop('hcgpos', '0 < cg', 'N01c', 'first field of SAME248 cg witness')
prop('hModel', model_prop, 'N01c', 'exact SAME248 model existential, no independent model selection')
prop('hm₀', 'm₀ ≤ mΩ', 'N01m', 'proof witness from SAME248 model')
prop('hcg', '@MeasurableSpace.CountablyGenerated Ω m₀', 'N01m', 'proof witness from SAME248 model')
prop('hμ₀Probability', 'IsProbabilityMeasure μ₀', 'N01s', 'same selected measure probability field')
prop('hRetained248', retained248, 'N01s', 'retain whole producer248 selected-model conclusion, not just a finite identity')
prop('hOldPayments248', old_env_type, 'N01s', 'entire original-window/explicit-guard248 branch unchanged')
prop('hOldAtN248', old_n_type, 'N03', 'old eventual predicate at same n before late w/z; type-local old lets remain local')
prop('hOldAtCurrent248', old_at_current, 'N04', 'all original payment, physical and original-window clauses at the SAME n/w/z')
prop('hTailScalePos', '0 < Shao.OQ6.BoundedProductEnvelopeTails.tailScale Menv', 'N02', 'qualified bounded_scales_pos; no new positivity premise')
prop('hRemainderScalePos', '0 < remainderWindowScale (Shao.OQ6.BoundedProductEnvelopeTails.tailScale Menv) t0', 'N02', 'remainderWindowScale_bounds at positive/nonnegative K')
prop('hAbsScalePos', '0 < min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ))', 'N02', 'first field of qualified236 at actual t0,cg')
prop('hPaidPositive', '0 < cPaid', 'N02', 'minimum of two positive scales')
prop('hPaidLeBoth', 'cPaid ≤ remainderWindowScale (Shao.OQ6.BoundedProductEnvelopeTails.tailScale Menv) t0 ∧\n  cPaid ≤ min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ)) ∧ cPaid ≤ 1', 'N02', 'deterministic min geometry, no new window premise')
prop('hAuxWindowEq', 'min (1 : ℝ) (Real.sqrt ((2 * cPaid) ^ (2 : ℕ)) / (2 : ℝ)) = cPaid', 'N02', 'use Real.sqrt_sq with 0≤2*cPaid and cPaid≤1; inline positive236 auxiliary t0, no ordinary helper scalar')
prop('hPaidNonemptyEventually', '∀ᶠ n : ℕ in Filter.atTop,\n  4 ≤ n ∧ (1 : ℝ) ≤ cPaid * Real.rpow (n : ℝ) (1 / 6 : ℝ)', 'N02', 'reuse qualified236 nonempty-window field at inline positive parameter (2*cPaid)^2 and same cg; no new rpow-growth API')
prop('hSqrtNatAtTop', 'Filter.Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) Filter.atTop Filter.atTop', 'N02', 'Real.tendsto_sqrt_atTop composed with exact tendsto_natCast_atTop_atTop at R=ℝ')
prop('hStudentizerEventually', '∀ᶠ n : ℕ in Filter.atTop, 1 + rho ≤ Real.sqrt (n : ℝ)', 'N02', 'pull back exact Filter.eventually_atTop real threshold set along hSqrtNatAtTop; rho already fixed')
prop('hAbsorption236', '''let cWindow : ℝ := min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ))
0 < cWindow ∧ ∀ᶠ n : ℕ in Filter.atTop,
  4 ≤ n ∧ (1 : ℝ) ≤ cWindow * Real.rpow (n : ℝ) (1 / 6 : ℝ) ∧
  ∀ z : ℝ, (1 : ℝ) ≤ z → z ≤ cWindow * Real.rpow (n : ℝ) (1 / 6 : ℝ) →
  (6 : ℝ) * Real.exp (-boundedPolylogMomentOrder t0 n) +
    (2 : ℝ) * Real.exp (-cg * (n : ℝ)) +
    (8 : ℝ) * Real.exp (-Real.sqrt (n : ℝ) / (2 : ℝ)) ≤
      Real.exp (-(t0 / (2 : ℝ)) * Real.rpow (n : ℝ) (1 / 3 : ℝ)) * Shao.standardNormalTail z''', 'N02', 'exact qualified236 formula and fixed-positive t0,cg, no new existential selector')
prop('hFeeIsDoublePaymentOne', '''(6 : ℝ) * Real.exp (-boundedPolylogMomentOrder t0 n) +
  (2 : ℝ) * Real.exp (-cg * (n : ℝ)) +
  (8 : ℝ) * Real.exp (-Real.sqrt (n : ℝ) / (2 : ℝ)) = 2 * payment1''', 'N06', 'literal polynomial identity 6=2*3,2=2*1,8=2*4')
prop('hPaymentLeOne', 'payment ≤ payment1', 'N06', 'hz:1≤z and Real.sqrt_nonneg n; exp monotonicity')
prop('hDoublePaymentAbsorbed', '2 * payment1 ≤ R * Shao.standardNormalTail z', 'N06', '236 on same cg and narrowed window')
prop('hLowerLoss', 'payment + payment1 ≤ R * Shao.standardNormalTail z', 'N06', 'payment≤payment1 and exact double-payment absorption')
prop('hUpperLoss', '3 * payment + payment1 ≤ 2 * (R * Shao.standardNormalTail z)', 'N06', '3payment+payment1≤4payment1≤2RΨ, without cost sign premises')
prop('hPhysicalPaidBounds', '''Shao.standardNormalTail z * Real.exp (-C1 * L0) * (1 - C2 * sourceCost0) - payment - payment1 ≤
  P.real {ζ : Fin n → Ω | z ≤ Tphysical ζ} ∧
P.real {ζ : Fin n → Ω | z ≤ Tphysical ζ} ≤
  Shao.standardNormalTail z * Real.exp (C3 * L0) * (1 + C4 * sourceCost0) + 3 * payment + payment1''', 'N07', 'literal SAME248 guarded physical result after deriving guard in common eventual set')
prop('hRelativeBounds', relative[relative.index('          Shao.standardNormalTail'):].rstrip(), 'N07', 'algebraic factorization only; no Ψ division, positivity or weighted-cost smallness')

choices = [
    {'name':'cg','type':'ℝ','rhs':'Classical.choose hCg','choiceFullProp':cg_prop,'contextId':'N01','scope':'after original global g/r/v/rho/β/cWindow and before selected m₀; SAME producer248'},
    {'name':'m₀','type':'MeasurableSpace Ω','rhs':'Classical.choose hModel','choiceFullProp':model_prop,'contextId':'N01c','scope':'after sole cg/hcgpos and before μ₀ and its selected instances; SAME producer248'},
]
inventory = {
    'schema':'oq56-unit249-stage1-complete-prospective-interface-v1','atUTC':NOW,'status':'PROPOSED_NOT_FROZEN_NOT_IMPLEMENTED_NOT_ELABORATED',
    'ownerChat':activation['ownerChat'],'role':activation['role'],'moduleProposed':MODULE,'publicTheoremProposed':MODULE+'.'+NEW_NAME,
    'original16Telescope':original_telescope,'completeUniqueContexts':contexts,'contextExpansionRule':'Concatenate parent-chain text in order; named substantive proof facts have explicit fullType below. Old public type-local lets remain exactly scoped by the whole retained248 head.',
    'publicOrdinary':ordinary,'optionalOrdinary':optional,'proposedProofFacts':props,'actualSameModelChoicesProposed':choices,
    'approvedInstances':old_inventory['approvedInstances'],'APIImplicitInstances':old_inventory['APIImplicitInstances'],
    'newBranchInstanceScopeReuses':'Only same originalSampleSpace=mN, originalSampleProbability from original μ, finiteIndex and standard real/Filter algebra instances at exact matching scopes. No new instance, law or model.',
    'retained248FrozenProofFactsReferenceOnly':old_inventory['frozenProofFacts'],
    'retained248CompleteContextsReferenceOnly':old_contexts['completeUniqueContexts'],
    'retained248AdditionalLogicalPackagesReferenceOnly':old_contexts['additionalPureLogicalPackages'],
    'referenceOnlyPolicy':'The248 author helper facts are preserved as complete full-type/context reference, not requirements to replay its proof. Future249 author calls prospective qualified248 once, uses the complete public result, and does not reconstruct old247/248 proofs.',
    'importedActualDefinitionInventory':ref237['importedActualDefinitionInventory'],
    'publicTopLevelHelpers':[],'newStructures':[],'newInstances':[],'callbacks':[],'newIndependentSelectors':[],'newNatCutoffs':[],
    'newPublicOrdinary':new_ordinary,'newOptionalScalarAliases':new_optional,
    'countsDerived':{'retainedPublicOrdinary':len(old_names),'newPublicOrdinary':len(new_ordinary),'publicOrdinary':len(ordinary),'optionalOrdinary':len(optional),'proposedProofFacts':len(props),'completeUniqueContexts':len(contexts),'sameModelDataChoices':len(choices),'approvedInstanceRows':len(old_inventory['approvedInstances']),'APIImplicitRows':len(old_inventory['APIImplicitInstances']),'newTopLevelHelpers':0,'newNatCutoffs':0,'newIndependentSelectors':0},
    'producer248':{'source':release248['source'],'qualifiedAtActivation':False,'SOURCEReviewPendingAtActivation':True,'usage':'public prospective head/context ONLY; implementation requires exact qualification and lead freeze'},
    'source236QualifiedEvidence':binding(ROOT/'drafts/oq56/unit236/qualified-evidence.json'),
    'source247QualifiedEvidenceReusedIndirectly':binding(ROOT/'drafts/oq56/unit247/qualified-evidence.json'),
    'solePermittedInferredProp':'h248 before original global lets and choices; every other substantive have must have full explicit type',
    'newPremises':[],'nonClaims':activation['nonClaims'],
}
put('INTERFACE-INVENTORY.json', inventory)

supplemental = [x for x in freeze['files'] if x not in activation['inputs']]
supplemental += [binding(release248['source']['path']), binding(ROOT/'drafts/oq56/unit234/lead-api-reference-01/Mathlib__Order__Filter__AtTopBot__Basic.lean.md'), binding(ROOT/'library/Shao/OQ5/P51/BoundedPolylogWindow.lean')]
coord = [binding(ROOT/'AGENTS.md'),binding(ROOT/'SERVER.md'),binding(ROOT/'coordination/TEAM.md')]
put('INPUT-BINDINGS.json', {'schema':'oq56-unit249-stage1-input-bindings-v1','atUTC':NOW,'activation':binding(ACT),'directImmutableInputs':activation['inputs'],'directCountDerived':len(activation['inputs']),'supplementalExactInputs':supplemental,'coordinationObservedOnly':coord,
                          'readingFrontier':{'fullOriginalSources':['p51.md','p54.md'],'fullProspectivePublicHead':'unit248/freeze-01/FROZEN-HEAD.txt, entire original16 and all145 ordinary declarations read','fullRelevantAPI':'qualified236 complete public source head/ambient and actual99LF TYPE; sqrt pinned ranges1-39,98-118,118-264; nat-cast and Filter.eventually_atTop full heads/ambient; all relevant remainder/tail scale definitions/heads','complete248Contexts':'11 unique contexts, all32 full-type facts and8 additional packages structurally compared with entire read public head; nonidentical helper types/instances read separately; large identical producer tails read by exact-token correspondence and terminal delimiter difference, rather than reprinting duplicate651121B JSON','selectedMetadataOnly':['248 manifest/compatibility binding and scalar policy fields','236/247 qualification bindings and scope/status metadata','TEAM current relevant constraints'],'source248Proof':'hash-only sealed dbe4; proof not reviewed, implemented or replayed','incidentalRead':'One bounded local BoundedPolylogWindow excerpt also displayed an accepted proof before the print limit; no reassessment, proof reuse by copying, check or replay was performed. The final route does not depend on its rpow-growth implementation.'}})

# This is a textual/byte validation, never a Lean parser or kernel claim.
restored = new_head.removesuffix(' ∧\n'+contract).replace(NEW_NAME, OLD_NAME, 1)+'\n'
assert restored == old_head
assert new_head.count('∃ cg : ℝ') == old_head.count('∃ cg : ℝ') == 1
assert new_head.count('∃ (m₀ : MeasurableSpace Ω)') == old_head.count('∃ (m₀ : MeasurableSpace Ω)') == 1
assert '1 + rho ≤ Real.sqrt (n : ℝ)' in contract
assert contract.index('∀ᶠ n') < contract.index('∀ (w :') < contract.index('(z : ℝ)')
assert contract.index('1 + rho ≤') < contract.index('∀ (w :')
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',preamble+new_head+closing)
assert ':= by' not in new_head and ':= by' not in preamble+closing
assert '(1 - C2 * sourceCost0)' in contract and '(1 + C4 * sourceCost0)' in contract
assert '/ Shao.standardNormalTail' not in contract
assert contract.count('ScalarShaoZhouFiniteCostTailInput') == 1
normalize=lambda t:re.sub(r'\s+',' ',t).strip()
for name in ['L0','sourceCost0','Tphysical']:
    newrow=next(x for x in new_ordinary if x['name']==name)
    oldrows=[x for x in old_inventory['publicOrdinary'] if x['name']==name]
    assert any(normalize(x['type'])==normalize(newrow['type']) and normalize(x['rhs'])==normalize(newrow['rhs']) for x in oldrows),name
# Balanced delimiters catches accidental text-generation defects, not Lean typing.
stack=[]; pairs={')':'(',']':'[','}':'{'}
for c in new_head:
    if c in '([{': stack.append(c)
    elif c in ')]}': assert stack and stack.pop()==pairs[c], c
assert not stack
def coord(text, offset):
    return {'charOffsetZeroBased':offset,'utf8ByteOffsetZeroBased':len(text[:offset].encode('utf-8')),
            'lineOneBased':text.count('\n',0,offset)+1,'columnOneBased':offset-text.rfind('\n',0,offset)}

insert = len(old_head.rstrip('\n').replace(OLD_NAME, NEW_NAME, 1))
old_guard_start = new_head.index('          (1 + rho ≤ Real.sqrt (n : ℝ) →')
old_env_start = new_head.index('      (∀ (Cenv aenv t0 Menv : ℝ)')
old_env_end = insert-1
assert new_head[old_env_end] == ')'
closing_run = []
k = old_env_end
while new_head[k] == ')':
    closing_run.append(coord(new_head,k)); k-=1
closing_run.reverse()
assert len(closing_run) == 4
assert new_head[insert:insert+3] == ' ∧\n'
new_branch_start = insert+3+6
assert new_head[new_branch_start:new_branch_start+2] == '(∀'
old_stack=[]
for offset,c in enumerate(new_head[:insert]):
    if c in '([{': old_stack.append((c,offset))
    elif c in ')]}': assert old_stack.pop()[0] == pairs[c]
assert not old_stack
scope_coordinates={'schema':'oq56-unit249-added-conjunction-exact-scope-coordinates-v1','atUTC':NOW,
                   'candidateHead':binding(OWN/'CANDIDATE-HEAD.txt'),'offsetConvention':'zero-based UTF8 byte and Unicode-character offsets; one-based lines/Unicode columns; all coordinates refer to CANDIDATE-HEAD.txt, not declaration preamble',
                   'parentScope':'same existential cg/m₀/hm₀/hcg selected-model conclusion after μ₀ and selected letI instances; sibling of old universal branch and old envelope/eventual branch',
                   'contextExpansion':['original16','original g/r/v/rho/β/cWindow','sole SAME248 cg and m₀','μ₀ trim and same selected letI instances'],
                   'oldEnvelopeBranchOpening':coord(new_head,old_env_start+6),'oldExplicitGuardOpening':coord(new_head,old_guard_start+10),
                   'oldTerminalFourClosingParensLeftToRight':closing_run,'oldEnvelopeBranchClosing':coord(new_head,old_env_end),
                   'addedConjunction':coord(new_head,insert+1),'newBranchOpening':coord(new_head,new_branch_start),
                   'newBranchClosing':coord(new_head,len(new_head.rstrip('\n'))-1),
                   'newEventualQuantifier':coord(new_head,new_head.index('        ∀ᶠ n',insert)+8),
                   'newDerivedStudentizerGuardConclusion':coord(new_head,new_head.index('          1 + rho ≤',insert)+10),
                   'newLateWQuantifier':coord(new_head,new_head.index('          ∀ (w :',insert)+10),
                   'newLateZBinder':coord(new_head,new_head.index('            (z : ℝ)',insert)+12),
                   'openDelimiterStackBeforeAddedConjunction':[],
                   'textualScopeFacts':{'allOldBranchAndGuardParensClosedBeforeAddition':True,'newBranchOutsideOldExplicitGuardAntecedent':True,'newGuardIsConjunctOfNewEventualConclusionBeforeWZ':True,'rhoDefinedBeforeCgModelEnvelopeAndEventualN':True},
                   'notLeanParserOrKernelScopeCertification':True}
put('SCOPE-COORDINATES.json',scope_coordinates)
validation={'schema':'oq56-unit249-stage1-local-structural-validation-v1','atUTC':NOW,'status':'PASS_TEXT_BYTES_COUNTS_ONLY_NOT_LEAN_CHECKED','activationInput28AllExact':True,'unit248AuthorFINALWRITE6zeroVerified':True,'unit248SealedSourceExact':binding(release248['source']['path']),'unit248Qualified':False,'whole248HeadExactAfterOnlyNewContractRemovalAndTheoremNameRestoration':True,'oldHead':binding(OLD/'freeze-01/FROZEN-HEAD.txt'),'candidateHead':binding(OWN/'CANDIDATE-HEAD.txt'),'contract':binding(OWN/'NEW-RELATIVE-TAIL-CONTRACT.txt'),'oldOrdinaryNamesAndOrderExact':True,'allOrdinaryCountsDerivedFromActualHeads':True,'countsDerived':inventory['countsDerived'],'original16Unchanged':True,'soleCgM0No235237239Selectors':True,'originalWindowAndGuardedBranchUnchanged':True,'newCommonPaidWindowPositiveAndEventuallyNonemptyIsConclusion':True,'guardBeforeLateWZWithinCommonEventualSet':True,'noNewStochasticPremise':True,'noPsiDivisionOrHiddenCostSignPremise':True,'delimitersBalanced':True,'noProofBodiesAdded':True,'UTF8NoBOMLFOnly':True,'qualificationOrKernelClaim':False,'mathematicalExecution':False,'operations':activation['runtimeRestriction'],'knownGaps':['Exact248 qualification is not yet available at this immutable activation boundary.','Lead must freeze this whole proposed declaration/inventory before any249 implementation.','New candidate and all helper obligations have no Lean elaboration/kernel proof yet.'],'nextExactDependency':'Lead Stage1 intake, exact qualified248 evidence, substantive249 freeze; then a separately authorized author can implement.'}
validation['addedBranchExactScopeCoordinates']=binding(OWN/'SCOPE-COORDINATES.json')
validation['sameLiteralL0SourceCost0PhysicalRHSAtNewScope']=True
validation['operations']={k:0 for k in ['Lean','lake','kernel','PP','AX','server','network','upload','Git','API','children']}
put('LOCAL-VALIDATION.json', validation)

sqrt_primary = json.loads(read(PLAN/'PRIMARY-SQRT-API.json'))
sqrt_ambient = json.loads(read(PLAN/'PRIMARY-SQRT-AMBIENT-SUPPLEMENT.json'))
source236 = read(ROOT/'drafts/oq56/unit236/author-repair-01/OriginalExceptionalTailAbsorption.lean')
public236 = source236[:source236.index(':= by')].rstrip()
actual236 = read(ROOT/'drafts/oq56/unit236/owner-evidence-01/actual-owned-types.txt')
basic_path = ROOT/'drafts/oq56/unit234/lead-api-reference-01/Mathlib__Order__Filter__AtTopBot__Basic.lean.md'
natcast_path = ROOT/'drafts/oq56/unit236/lead-api-reference-01/Mathlib__Order__Filter__AtTopBot__Archimedean.lean.md'
api = '''# Unit249 exact API and ambient context

Status: local interface reading only, no elaboration, kernel check, proof
implementation or new mathematical qualification. All source references below
are immutable local captures/snapshots. Pinned Lean4.36.0-rc1 and mathlib
807d3836b165983210ee2ecf3cd28f239436949c are recorded; no local toolchain was
probed or invoked.

## Qualified236 public head and complete ambient

The currently qualified source is cb1ed434c1029e674ddff14a1be07ab55b2fb064060acbe92bea389a93f7df8f,
11444 bytes. The same first original object is
99a8ccfe353e26adef88d524e78418952f840906bb0a63ba886156a88a53d716.
Current qualification binds successful native/all-owner audits, complete
independent review and all actual99LF TYPE/0VALUE. Those accepted proofs and
checks are reused exactly, not reviewed or executed again.

```lean
''' + public236 + '\n```\n\nThe current entire actual TYPE follows, with its implicit real instances and literal RHS:\n\n```lean\n' + actual236 + '\n```\n'
api += '\n## Pinned square-root full heads and namespace/ambient\n\n'
api += 'Underlying source: '+json.dumps({k:sqrt_primary[k] for k in ['physicalPath','resolvedPath','sha256','bytes','pinnedMathlib']},ensure_ascii=False)+'\n\n'
for capture in [sqrt_primary['ranges'][0],*sqrt_ambient['ranges'],*sqrt_primary['ranges'][1:]]:
    api += f"Exact pinned lines{capture['start']}–{capture['end']}:\n\n```lean\n{capture['text']}\n```\n\n"
api += '''The supplement explicitly closes NNReal and opens namespace Real before
the captured `variable {x y : ℝ}`. Therefore the adopted head is
`Real.tendsto_sqrt_atTop : Filter.Tendsto (Real.sqrt : ℝ → ℝ) atTop atTop`,
not an NNReal theorem. The chosen guard route is this theorem composed with
the exact natural-cast theorem below. It does not need any positivity of rho.
`Real.sqrt_sq (h : 0 ≤ x) : √(x^2) = x` is used only for the auxiliary236
nonempty-window normalization. `Real.le_sqrt_of_sq_le` is captured but not
needed by the chosen route; it remains a genuine fallback, not a new premise.

## Pinned natural-cast and eventual-atTop heads/ambient

'''+read(natcast_path)+'\n\n'+read(basic_path)
api += '''
At `R=ℝ`, the Semiring/PartialOrder/IsOrderedRing/Archimedean instances in the
nat-cast head are standard imported real instances, not new hypotheses.
The Filter.eventually_atTop head includes Preorder, IsDirectedOrder and
Nonempty ambient conditions; ℝ satisfies them. Its reverse direction gives
the actual real threshold set `∀ᶠ x:ℝ in atTop, 1+rho≤x` from the witness
`1+rho`. Pulling this set back through the composed Tendsto supplies the
guard. Eventual intersection and specialization are logical Filter operations;
no new analytic API or per-unit execution wrapper is proposed.

## Exact curated scale definitions and positivity heads

'''
for file, names in [('library/Shao/OQ5/P51/BoundedRemainderPayments.lean',['remainderWindowScale','remainderWindowScale_bounds']),('library/Shao/OQ6/BoundedProductEnvelopeTails.lean',['commonMomentScale','envelopeTailScale','squareTailScale','scalarTailScale','rowTailScale','tailScale','bounded_scales_pos'])]:
    src = read(ROOT/file)
    ambient = src[:src.index('noncomputable section')+len('noncomputable section')]
    api += '\nSource '+json.dumps(binding(ROOT/file),ensure_ascii=False)+'\n\n```lean\n'+ambient+'\n```\n\n'
    for name in names:
        start = re.search(r'(?m)^(?:def|theorem) '+re.escape(name)+r'\b',src).start()
        tail=src[start:]
        later=re.search(r'(?m)^(?:private )?(?:noncomputable )?(?:def|theorem|lemma) ',tail[1:])
        chunk=tail[:1+later.start()] if later else tail
        if ':= by' in chunk: chunk=chunk[:chunk.index(':= by')]
        api += '```lean\n'+chunk.rstrip()+'\n```\n\n'
api += '''Historical “pending” source comments do not supersede current qualified
evidence. Unit237's interface is used only as a reference for common-window
geometry and literal definitions; no235/237/239 selector, law or theorem is
consumed. All32 imported actual definitions, including residual denominators,
jackknife square, clipping1 and the exact Gaussian-tail RHS, are reproduced
with full parameter/result types in INTERFACE-INVENTORY.json.

## Prospective248 full interface

The exact entire46589B public head is retained as the prefix of
CANDIDATE-HEAD.txt, up to its one theorem-name change. LOCAL-VALIDATION.json
records the byte restoration check. The original16 telescope, every145 old
ordinary type/RHS/scope, full producer/model choice propositions, the11 old
unique contexts and all32 old typed reference facts remain in the inventory.
The248 sealed dbe4 source is hash checked only; no248 proof is reviewed here.
Its qualification remains false at this immutable activation boundary.

## Ordinary scalar operations

The payment comparison uses only z≥1 and sqrt(n)≥0 followed by exponential
monotonicity. Fee identity and final factorization are real polynomial
identities. No guessed new named scalar API, density/CDF identity, positive
Psi denominator, source-cost sign or stochastic independence fact is needed.
These are proposed explicitly typed local obligations in the inventory, not
new theorem assumptions and not implemented Lean proofs.
'''
put('API-CONTEXT.md',api)

route='''# Unit249 Stage1 source-bound design

Status: COMPLETE PROSPECTIVE INTERFACE/SOURCE/API DESIGN. This package is not
a lead freeze, proof implementation, independent review, Lean elaboration or
qualification. The sole lane owner is01a17665-2e41-7ed1-9911-57f16fe889fa.
All writes are confined to the assigned author-stage1-01 directory.

## Exact source target and direct consumer

The target is p54 §2 after F6, read with complete p51 S1–S8 and p54 §§1–3.
Those originals were read completely, including the p54 repair of p51's
false arbitrary-polynomial conditional p-moment variation claim. This unit
does not revive that claim. It concerns only the existing original bounded
product/polylog envelope model and the actual centered-row statistic.

The direct consumer is the original physical closed upper-tail bound with
Gaussian-relative exceptional payments. The missing scalar obligation is
to convert248's explicit physical losses `payment_z+payment_1` and
`3payment_z+payment_1` into R*Psi and2R*Psi on one positive, eventually
nonempty common window. Full weighted sourceCost0 and the exact external
Shao–Zhou finite-cost input remain explicit. No weighted-cost rate, final
beta-term absorption, CDF/atom theorem or fullOQ56/root completion is claimed.

## Prospective248 dependency and unchanged entire interface

The bound input248 frozen head is46589B/SHA256
602ce2e2c78cee8ca6f5bd3d53ce8b90d9b5caaa1c3b71ff720c59d98f02baa5.
Its author sealed dbe4dd9b334fda150951c9c42fb4b8138ede143418d5498435a887d856cc336b,
256737B, with exact FINALWRITE/six-zero release. That source was checked by
hash only here. It is SOURCE-review-pending and NOT qualified at this
activation; no proof or machine pass is inferred from its public proposal.

Candidate249 is the WHOLE248 declaration plus one additional conjunction at
the SAME selected-model scope. Removing exactly NEW-RELATIVE-TAIL-CONTRACT.txt
and its conjunction and restoring the old theorem name reconstructs every
byte of the old frozen head. In particular the original large remainder
window, all universal finite-n analytic/coding/cost clauses, all old ordinary
definitions, actual physical zero branch, all-real closed-threshold payment
clauses and explicit studentizer-guard implication are retained unchanged.
The new result does not silently replace or strengthen that old branch.

The planned author calls prospective qualified248 once before all global
lets and choices. The sole two data choices remain its cg and m₀, with
their exact FULL existential propositions frozen in the inventory. The
same hm₀/hcg, μ₀, ν and η are retained. There is no call to an independent
235,237 or239 selector and no third data choice, model or law.

## Quantifier order and the fixed-rho distinction

The original sixteen binder groups fix Ω,mΩ,μ,h, all original measurability,
second-moment, symmetry, centering, projection variance and p-moment
assumptions, p∈(2,3], and cBudget>0. The exact six global definitions remain
g, r=h-g-g, v=the ORIGINAL residual second moment, rho=sqrt(v), β and the
original strict-moment cWindow. Thus rho is already a fixed scalar before
the cg/model choices, fixed envelope scalars and eventual n.

For every fixed nonnegative Cenv,aenv,Menv and positive t0, define

`cPaid = min (remainderWindowScale (tailScale Menv) t0)
  (min 1 (sqrt(t0)/2))`.

Its RHS depends only on Menv,t0 and is fixed before n. The proposal asserts
0<cPaid. One common eventual natural set asserts n≥4,1+rho≤sqrt(n) and
1≤cPaid*n^(1/6), before quantifying over the late envelope w and level z.
Therefore [1,cPaid*n^(1/6)] is eventually nonempty, including both endpoints.
This is not a uniform statement over an arbitrary rho supplied after n.
No such late-rho statement is used or offered.

The later w still has exactly the original AE nonnegativity, bounded-polylog
height, square integrability/integral bound and AE product envelope. No
Measurablew hypothesis is added. The later level is exactly1≤z≤cPaid*n^(1/6).
The same original externalSZ input and strict-moment alternative
`β=0 ∨ (0<β ∧ z≤cWindow*β^(-1/p)*n^((p-2)/(2p)))` follow at their old scope.
The new physical tail has no user-supplied studentizer guard.

## Chosen API route for the two eventual scalar facts

The exact pinned square-root capture and its Real-namespace supplement are
fully read and bound. `Real.tendsto_sqrt_atTop` composed with the exact
`tendsto_natCast_atTop_atTop` at R=ℝ gives sqrt(n)→atTop. The pinned
Filter.eventually_atTop head/ambient gives the real threshold set at
1+rho; pull it back through this Tendsto. Intersect with the SAME248
eventual predicate and236 absorption predicate before introducing w,z.
No new natural-number cutoff or data-dependent selector is needed.

For common-window nonemptiness choose the smallest already bound API route
without introducing another primary rpow-growth source: reuse the qualified
236 nonempty-window field at inline parameter `(2*cPaid)^2>0` and the SAME
cg. Since0<cPaid≤1, captured `Real.sqrt_sq` identifies its scale
`min 1 (sqrt((2*cPaid)^2)/2)` EXACTLY with cPaid. The auxiliary parameter is
an inline deterministic expression, not a new ordinary let, model or
assumption. This second236 application discards its fee result; the actual
fee application below still uses the ORIGINAL t0. No exponent is changed
in the target R. The optional alternate rpow growth proof is not needed.

Tail-scale positivity follows from the exact bounded_scales_pos interface;
remainderWindowScale_bounds then supplies its positive scale. The other
minimum branch is positive by qualified236 at actual t0,cg. Min geometry
gives cPaid>0,cPaid≤both parent scales,cPaid≤1. Nonnegative n^(1/6) transfers
the paid-window level into both parent windows. All are typed local
obligations, not new public assumptions. No old proof/check is replayed.

## Exact coefficients and final product inequalities

Qualified236 has no existential cg. It takes every fixed positive t0,cg and
eventually bounds its LITERAL6exp(-q)+2exp(-cg*n)+8exp(-sqrt(n)/2) by
R*Psi(z), where q=boundedPolylogMomentOrder t0 n and
R=exp(-(t0/2)*n^(1/3)). The complete current99LF actualTYPE and source
ambient were read; the old qualified proof/review/first-object audit is
reused without replay.

For the SAME cg, its left side is exactly2*payment_1. Since z≥1 and
sqrt(n)≥0, payment_z≤payment_1. Consequently the prospective local loss
obligations are `payment_z+payment_1≤R*Psi(z)` and
`3payment_z+payment_1≤2*(R*Psi(z))`. Applying248's now-derived guard and
substituting these scalar losses gives precisely

`Psi(z)*(exp(-C1*L0)*(1-C2*sourceCost0)-R) ≤ P(Tphysical≥z)`

and

`P(Tphysical≥z) ≤ Psi(z)*(exp(C3*L0)*(1+C4*sourceCost0)+2*R)`.

This is algebraic factorization. No division by Psi, no Ψ>0 premise, no
positivity of1-C2*sourceCost0, and no cost-smallness condition is needed.
The physical statistic retains the explicit s=0→0 branch and all original
residual, deleted-residual, jackknife and clipping512/rho/1 coefficients.
No probability density or continuous-tail interpretation is substituted.

## Complete proposed interface inventory and local validation

Every155 public ordinary occurrence is derived from the candidate head:
145 exact old occurrences and10 in the new branch. The159 optional ordinary
rows consist of147 inherited scoped rows, those10 new public rows and only
two new optional scalar payment aliases. The28 explicitly typed proposed
local facts,11 new context fragments,2 complete choice propositions,8
existing instance rows and5 API implicit rows are recorded in full. These
are proposed ceilings/contracts, not claims about a future implemented
proof. There are no top-level helper declarations, custom instances,
callbacks, new structures or new Nat cutoffs.

The exact new sourceCost0 RHS is copied from the second248 branch, with
its full/partial exponential weights and original deleted quantities.
The whole old248 author fact/context inventory is retained as reference
only; future249 implementation consumes the public producer result instead
of rebuilding old proof helpers. All model choice propositions and new
helper types are written before implementation.

LOCAL-VALIDATION.json checks28 activation bindings,248 author FINALWRITE6zero,
the sealed dbe4 hash, all eight frozen file bindings, whole-head restoration,
ordinary order/counts, quantifier/guard ordering, delimiter balance,
forbidden proof tokens and UTF8-noBOM/LF. These are deterministic textual
checks, not Lean parsing, elaboration or mathematical acceptance.
SCOPE-COORDINATES.json additionally records exact UTF8 byte/line/column
coordinates for the old envelope and explicit-guard openings, their four
terminal closing parentheses, the added conjunction, new branch opening and
closing, and new eventual/derived-guard/late-w/z positions. The delimiter
stack is empty immediately before the addition: no old explicit-guard or
old per-n/envelope branch is left open. The addition is a sibling conjunct
at the SAME selected-model conclusion level. This is the precise syntactic
reason the new branch is outside the old guard antecedent.

## Honest reading frontier, provenance and exact next dependency

The entire original p51/p54 and entire248 frozen public head were read.
The large651121B actual-context JSON contains substantial repeated public
tails: all unique contexts and fact scopes were mapped, full types compared
tokenwise with the already-read head, and nonidentical helper/instance
types were read separately. Literal duplicate tails were not repeatedly
printed. INPUT-BINDINGS.json records this frontier and the one incidental
accepted-window proof excerpt; it does not claim a new old-proof review.
Qualification manifests/compatibility were read for bindings, scope and
status, not falsely described as every-byte semantic reviews.

No mathematical/API obstruction was found in this scalar design. Exact248
qualification is still the hard dependency. Only after the lead verifies
that exact qualified248 evidence and freezes this entire249 declaration,
contexts/inventory and helper scope may a separately authorized author
implement249. Such implementation will need new independent complete
source-to-statement/proof review and designated-server native/sameFIRSTO
all-actualTYPE/requiredVALUE/transitiveAX evidence. None occurred here.

All actual Lean/lake/kernel/PP/AX/server/network/upload/Git/API/children
operations are zero. Requested model/effort are gpt-6.1-sol/xhigh; actual
backend/model/effort and input/cached-input/output/reasoning-subset counts
are not exposed and remain null. No new Goal, schedule, sidebar or outbound
Root message was created. FINALWRITE6zero release is written last.
'''
put('SOURCE-ROUTE.md',route)
print(json.dumps({'written':'candidate/inventory/bindings/validation','counts':inventory['countsDerived'],'head':binding(OWN/'CANDIDATE-HEAD.txt'),'contract':binding(OWN/'NEW-RELATIVE-TAIL-CONTRACT.txt')},ensure_ascii=False,indent=2))
