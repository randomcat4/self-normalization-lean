/* Local deterministic Stage1 artifact generation; no Lean, proof, process or network API. */
'use strict';
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const root = 'C:/game/shao lean';
const base = root + '/drafts/oq56/next-source/oq6-original-same-witness-clipped-paid-tail-planned';
const own = base + '/author-stage1-01';
const freeze = root + '/drafts/oq56/unit246/freeze-01';
const oldAuthor = root + '/drafts/oq56/next-source/oq6-original-same-witness-clipped-tail-application-planned/author-stage1-01';
const read = p => fs.readFileSync(p, 'utf8');
const sha = b => crypto.createHash('sha256').update(b).digest('hex');
const bind = p => ({path: p, sha256: sha(fs.readFileSync(p)), bytes: fs.statSync(p).size});
const assert = (v, m) => { if (!v) throw Error(m); };
const put = (name, s) => {
  const p = path.resolve(own, name);
  assert(p.startsWith(path.resolve(own) + path.sep), 'write outside ownership');
  assert(!s.includes('\r'), 'new artifact must be LF');
  fs.writeFileSync(p, s, 'utf8');
};
const json = (name, o) => put(name, JSON.stringify(o, null, 2) + '\n');
const activationPath = base + '/activation-stage1-01/ACTIVATION.json';
const activation = JSON.parse(read(activationPath));
assert(sha(fs.readFileSync(activationPath)) === 'c2bdec40f4d3832d7d0118442092244dc9fcd0096649562ca160e2c4bc3ac525', 'activation changed');
for (const row of activation.inputs) {
  const b = bind(row.path);
  assert(b.sha256 === row.sha256 && b.bytes === row.bytes, 'input changed: ' + row.path);
}
const oldHead = read(freeze + '/FROZEN-HEAD.txt');
const oldPreamble = read(freeze + '/FROZEN-PREAMBLE.txt');
const oldClosing = read(freeze + '/FROZEN-CLOSING.txt');
const old = JSON.parse(read(freeze + '/INTERFACE-INVENTORY.json'));
assert(old.ordinaryBindings.length === 138, 'old public ordinary count');
const inherited245Head = read(root + '/drafts/oq56/unit245/freeze-01/FROZEN-HEAD.txt');
const recovered245Head = oldHead.replace(old.completeNewContract, '').replace('actual_original_same_witness_clipped_scalar_tail_application', 'actual_original_same_witness_clipped_event_transport');
assert(recovered245Head === inherited245Head, 'lossless full245 recovery from fully read246');
assert(read(oldAuthor + '/API-CONTEXT.md').includes(inherited245Head.trim()), 'full245 API text mismatch');
assert(read(oldAuthor + '/API-CONTEXT.md').includes(old.declarationContexts.producer244CompleteHead.trim()), 'full244 API text mismatch');
const oldName = 'actual_original_same_witness_clipped_scalar_tail_application';
const newName = 'actual_original_same_witness_clipped_paid_scalar_tail_application';
const oldModule = 'Shao.OQ6.OriginalSameWitnessClippedTailApplication';
const newModule = 'Shao.OQ6.OriginalSameWitnessClippedPaidTailApplication';

const newData = `        let T0 : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho 1
        let L0 : ℝ := ∑ i : Fin n,
          ∫ ζ, (z * ξ0 i ζ) ^ 2 * min |z * ξ0 i ζ| 1 ∂P
        let sourceCost0 : ℝ :=
          ((∫ ζ,
              (z * |D1 ζ| + z ^ 2 * studentizerClipBudget n r 512 rho 1 ζ) *
                Real.exp (∑ j : Fin n, (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P) +
            ∑ i : Fin n, ∫ ζ,
              (min |z * ξ0 i ζ| 1 *
                (|(|D1 ζ|) - (|residualStatisticDDeleted n r ζ i|)| +
                  z * |studentizerClipBudget n r 512 rho 1 ζ -
                    studentizerClipBudgetDeleted n r 512 rho 1 ζ i|)) *
                Real.exp (∑ j ∈ Finset.univ.erase i,
                  (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P) /
            (∫ ζ, Real.exp (∑ j : Fin n,
              (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P)
`;
const newClause = `        (∀ (C1 C2 C3 C4 : ℝ)
            (hSZcBudget : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
              cBudget C1 C2 C3 C4)
            (hzMomentWindow : β = 0 ∨
              (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                Real.rpow (n : ℝ) ((p - 2) / (2 * p)))),
          Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                (1 - C2 * sourceCost0) - payment ≤
            P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
          P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ≤
            Shao.standardNormalTail z * Real.exp (C3 * L0) *
                (1 + C4 * sourceCost0) + 3 * payment) ∧
`;
const dataMarker = '        Measurable[mN₀, borel ℝ] V0 ∧\n';
const clauseMarker = '        Filter.limsup (fun k : ℕ => ν.real (E k))\n          Filter.atTop ≤ payment)';
assert(oldHead.split(dataMarker).length === 2, 'data insertion marker');
assert(oldHead.split(clauseMarker).length === 2, 'clause insertion marker');
const head = oldHead.replace(oldName, newName).replace(dataMarker, newData + dataMarker).replace(clauseMarker, newClause + clauseMarker);
const preamble = oldPreamble.replace('import Shao.OQ6.OriginalSameWitnessClippedEventTransport', 'import ' + oldModule).replace('namespace ' + oldModule, 'namespace ' + newModule);
const closing = oldClosing.replace(oldModule, newModule);
const recovered = head.replace(newData, '').replace(newClause, '').replace(newName, oldName);
assert(Buffer.from(recovered).equals(fs.readFileSync(freeze + '/FROZEN-HEAD.txt')), 'whole246 recovery failed');
put('CANDIDATE-PREAMBLE.txt', preamble);
put('CANDIDATE-HEAD.txt', head);
put('CANDIDATE-CLOSING.txt', closing);
put('CANDIDATE-DECLARATION.lean', preamble + head + closing);
put('NEW-CLIPPED-PAID-TAIL-CONTRACT.txt', newData + '\n' + newClause);

const parameters = old.declarationContexts.originalParameters;
const globalLets = old.declarationContexts.globalSixResultLets;
const selected = old.declarationContexts.selectedModelContext;
const universalStart = oldHead.indexOf('      (∀ (n : ℕ)');
const paymentStart = oldHead.indexOf('      (∀ (Cenv aenv t0 Menv : ℝ)');
assert(universalStart > 0 && paymentStart > universalStart, 'branch boundaries');
const universalAll = oldHead.slice(universalStart, paymentStart).trim().replace(/ ∧$/, '');
const paymentAll = oldHead.slice(paymentStart).trim();
const paymentLetsStart = head.indexOf('        let mN :', head.indexOf('      (∀ (Cenv'));
const paymentLetsEnd = head.indexOf(dataMarker, paymentLetsStart);
const paymentLets = head.slice(paymentLetsStart, paymentLetsEnd);
const paymentOuter = `(Cenv aenv t0 Menv : ℝ)
(hCenv : 0 ≤ Cenv) (haenv : 0 ≤ aenv)
(ht0 : 0 < t0) (hMenv : 0 ≤ Menv)
(n : ℕ) (hn : 4 ≤ n)
(w : Ω → ℝ)
(hW : ∀ᵐ o : Ω ∂μ, 0 ≤ w o)
(hWR : ∀ᵐ o : Ω ∂μ, w o ≤ boundedPolylogHeight Cenv aenv n)
(hSq : Integrable[mΩ] (fun o : Ω => (w o) ^ (2 : ℕ)) μ)
(hSqBound : (∫ o : Ω, (w o) ^ (2 : ℕ) ∂μ) ≤ Menv)
(hEnv : ∀ᵐ t : Ω × Ω ∂(@Measure.prod Ω Ω mΩ mΩ μ μ), |r t.1 t.2| ≤ w t.1 * w t.2)
(z : ℝ) (hz : (1 : ℝ) ≤ z)
(hzWindow : z ≤ remainderWindowScale
  (Shao.OQ6.BoundedProductEnvelopeTails.tailScale Menv) t0 *
    Real.rpow (n : ℝ) (1 / 6 : ℝ))
`;
const externalBinders = `(C1 C2 C3 C4 : ℝ)
(hSZcBudget : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
  cBudget C1 C2 C3 C4)
(hzMomentWindow : β = 0 ∨
  (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
    Real.rpow (n : ℝ) ((p - 2) / (2 * p))))
`;
const paymentContext = selected + '\n' + paymentOuter + paymentLets;
const externalContext = paymentContext + externalBinders;
const tauContext = externalContext + '(τ : ℝ) (hτ : 0 < τ)\n';
// These are generator strings only. They are not live Lean ordinary aliases.
const tail = 'P.real {ζ : Fin n → Ω | z ≤ T0 ζ}';
const zero = 'P.real {ζ : Fin n → Ω | projectionV n g ζ = 0}';
const lower = 'Shao.standardNormalTail z * Real.exp (-C1 * L0) * (1 - C2 * sourceCost0)';
const upper = 'Shao.standardNormalTail z * Real.exp (C3 * L0) * (1 + C4 * sourceCost0)';
const err1 = 'ν.real {x : Fin n → Ω × ℝ | z * |Dη k x| > Vη k x / 4}';
const err2 = 'ν.real {x : Fin n → Ω × ℝ | z ^ 2 * |D2 (q x)| > (1 / 4 : ℝ)}';
const upperPoint = `${tail} ≤\n  ${upper} +\n    ${err1} +\n    ${err2} +\n    ${zero} + τ`;
const clippedExistential = `∃ k0 : ℕ, ∀ (k : ℕ), k0 ≤ k →\n  ${upperPoint}`;
const payPoint = 'ν.real (E k) ≤ payment + τ';
const paymentExistential = `∃ k0 : ℕ, ∀ (k : ℕ), k0 ≤ k → ${payPoint}`;
const cutoffContext = tauContext + `(hClippedCutoff :\n${clippedExistential})\n(hPaymentCutoff :\n${paymentExistential})\n`;
const chosenContext = cutoffContext + 'let kClipped : ℕ := Classical.choose hClippedCutoff\nlet kPayment : ℕ := Classical.choose hPaymentCutoff\n';
const approxType = `∀ (τ : ℝ), 0 < τ →\n  ${tail} ≤ ${upper} + 3 * payment + 2 * τ`;
const upperTarget = `${tail} ≤ ${upper} + 3 * payment`;
const gap = `(${tail} - (${upper} + 3 * payment)) / 4`;
const failedContext = externalContext + `(hUpperWithTolerance :\n${approxType})\n(hUpperFailed : ¬ (${upperTarget}))\n`;
const resultType = oldHead.slice(oldHead.indexOf(' :\n') + 3).trim();
const cgProp = oldHead.slice(oldHead.indexOf('    ∃ cg : ℝ,')).trim();
const modelProp = oldHead.slice(oldHead.indexOf('    ∃ (m₀ :')).trim();
const h246Available = parameters + '\n' + globalLets + `\n(h246 :\n${resultType})\n`;
const cgCtx = h246Available + `(hCg :\n${cgProp})\n`;
const cgChosenCtx = cgCtx + 'let cg : ℝ := Classical.choose hCg\n';
const beforeModelCtx = cgChosenCtx + '(hcgpos : 0 < cg)\n';
const modelCtx = beforeModelCtx + `(hModel :\n${modelProp})\n`;
const contexts = {
  originalParameters: parameters, globalSixResultLets: globalLets,
  producer246CompleteHead: oldHead, candidateCompleteHead: head,
  h246AvailableContext: h246Available, cgSelectionContext: cgCtx,
  cgChosenContext: cgChosenCtx, beforeModelContext: beforeModelCtx, m0SelectionContext: modelCtx,
  selectedModelContext: selected, selectedUniversalContext: old.declarationContexts.selectedUniversalContext,
  selectedPaymentContext: paymentContext, paymentExternalContext: externalContext,
  paymentTauContext: tauContext, paidCutoffChoiceContext: cutoffContext,
  paidChosenCutoffsContext: chosenContext, failedPaidUpperContext: failedContext,
  originalUniversalScopeForOldInstances: old.declarationContexts.selectedUniversalContext,
};
const facts = {};
const addFact = (name, type, contextRef, availability) => {
  facts[name] = {type, completePropContextRef: contextRef, enclosingParameterContext: contexts[contextRef], availability};
};
addFact('h246', resultType, 'originalParameters', 'One immediate246 invocation with identical original parameters; prospective until qualified exact246 and later explicit activation.');
addFact('hCg', cgProp, 'h246AvailableContext', 'Projection of complete h246; sole cg existential.');
addFact('hcgpos', '0 < cg', 'cgChosenContext', 'Classical.choose_spec of sole complete hCg.');
addFact('hModel', modelProp, 'beforeModelContext', 'Same complete hCg after sole cg selection.');
addFact('hm₀', 'm₀ ≤ mΩ', 'selectedModelContext', 'Dependent proof witness from sole complete hModel; no second model selection.');
addFact('hCountableGeneration', '@MeasurableSpace.CountablyGenerated Ω m₀', 'selectedModelContext', 'Dependent proof witness from same full model existential.');
addFact('hμ₀Probability', '@IsProbabilityMeasure Ω m₀ μ₀', 'selectedModelContext', 'Same immediate246 output, retained proof; no new probability instance installed.');
addFact('hUniversal246', universalAll, 'selectedModelContext', 'Complete same-model universal branch of246, without omission of any original data or clauses.');
addFact('hPayment246', paymentAll, 'selectedModelContext', 'Complete same-model eventual-payment branch of246 before adding any new public data.');
addFact('hClippedLower', `${lower} - ${zero} ≤ ${tail}`, 'paymentExternalContext', 'Complete246 universal branch at n, hn, 512, nonnegative512, z, nonnegative z from hz; same external constants/input/window.');
addFact('hClippedEventual', `∀ (τ : ℝ), 0 < τ →\n  ${clippedExistential}`, 'paymentExternalContext', 'Upper-only logical projection of complete246 per-τ joint cutoff, specialized at literal512; original full joint clause remains in246.');
addFact('hNumeratorPayment', '∀ (δ : ℝ), 0 < δ →\n  ∀ᶠ k : ℕ in Filter.atTop, ν.real (E k) ≤ payment + δ', 'selectedPaymentContext', 'Retained complete246 payment output; δ arbitrary positive real, fixed n,w,z.');
addFact('hSecondPayment', 'ν.real E2 ≤ payment', 'selectedPaymentContext', 'Retained complete246 payment output.');
addFact('hZeroTransport', `ν.real {x : Fin n → Ω × ℝ | V x = 0} =\n  ${zero}`, 'selectedPaymentContext', 'Immediate246 universal branch retains245 exact same-model zero event transport.');
addFact('hZeroPayment', 'ν.real Z ≤ payment', 'selectedPaymentContext', 'Retained complete246 payment output.');
addFact('hOriginalZeroPayment', `${zero} ≤ payment`, 'selectedPaymentContext', 'Rewrite hZeroTransport with literal Z RHS and hZeroPayment; no new probability premise.');
addFact('hPaidLower', `${lower} - payment ≤ ${tail}`, 'paymentExternalContext', 'Real order from hClippedLower and hOriginalZeroPayment.');
addFact('hClippedCutoff', clippedExistential, 'paymentTauContext', 'hClippedEventual τ hτ; complete derived existential is explicit before any choose.');
addFact('hPaymentEventuallyAtTau', '∀ᶠ k : ℕ in Filter.atTop, ν.real (E k) ≤ payment + τ', 'paymentTauContext', 'hNumeratorPayment τ hτ.');
addFact('hPaymentCutoff', paymentExistential, 'paymentTauContext', 'Filter.eventually_atTop.mp specialized to ℕ and literal numerator payment predicate.');
addFact('hClippedAll', `∀ (k : ℕ), kClipped ≤ k →\n  ${upperPoint}`, 'paidChosenCutoffsContext', 'Classical.choose_spec hClippedCutoff.');
addFact('hPaymentAll', `∀ (k : ℕ), kPayment ≤ k → ${payPoint}`, 'paidChosenCutoffsContext', 'Classical.choose_spec hPaymentCutoff.');
addFact('hCommonClippedLe', 'kClipped ≤ kClipped + kPayment', 'paidChosenCutoffsContext', 'Natural linear arithmetic.');
addFact('hCommonPaymentLe', 'kPayment ≤ kClipped + kPayment', 'paidChosenCutoffsContext', 'Natural linear arithmetic.');
addFact('hClippedAtCommon', upperPoint.replaceAll(' k ', ' (kClipped + kPayment) '), 'paidChosenCutoffsContext', 'hClippedAll at the inline common sum; no new common-k data alias.');
addFact('hPaymentAtCommon', 'ν.real (E (kClipped + kPayment)) ≤ payment + τ', 'paidChosenCutoffsContext', 'hPaymentAll at that identical inline common sum.');
addFact('hPaidUpperApprox', `${tail} ≤ ${upper} + 3 * payment + 2 * τ`, 'paidChosenCutoffsContext', 'Complete literal E/E2 identification and real linear arithmetic with three separate payment bounds.');
addFact('hUpperWithTolerance', approxType, 'paymentExternalContext', 'Universally quantify τ>0 after the two inventoried cutoff selections; fixed-n scalar target independent of k and τ.');
addFact('hUpperFailed', `¬ (${upperTarget})`, 'paymentExternalContext', 'Only temporary contradiction branch, never a theorem premise.');
addFact('hUpperGapPositive', `0 < ${gap}`, 'failedPaidUpperContext', 'Real linear order from hUpperFailed, no named gap ordinary datum.');
addFact('hUpperAtGap', `${tail} ≤ ${upper} + 3 * payment + 2 * (${gap})`, 'failedPaidUpperContext', 'hUpperWithTolerance applied to the literal positive quarter-gap, no τ data choice.');
addFact('hPaidUpper', upperTarget, 'paymentExternalContext', 'Contradiction between strict failed-target gap and hUpperAtGap by real linear arithmetic only.');
addFact('hPaidContract', `${lower} - payment ≤ ${tail} ∧\n${upperTarget}`, 'paymentExternalContext', 'And of the proposed hPaidLower and hPaidUpper; not a completed proof.');

const dataLines = [...newData.matchAll(/^        let (\S+) : (.+?) :=([\s\S]*?)(?=^        let |$(?![\s\S]))/gm)];
assert(dataLines.length === 3, 'exact three new public bindings');
const newOrdinary = dataLines.map((m, i) => ({
  name: m[1], type: m[2], rhs: m[3].trim(),
  scope: 'Payment branch ONLY, same chosen cg/m₀/μ₀, after eventual n and original w/z hypotheses; fixed C0=512 and clipping1; before external scalar constants/window and new conclusion.',
  completePropContextRef: 'selectedPaymentContext',
  enclosingParameterContext: selected + '\n' + paymentOuter + paymentLets.slice(0, paymentLets.indexOf(m[0])),
  public: true, new: true,
}));
const choiceRows = [
  {name: 'cg', type: 'ℝ', rhs: 'Classical.choose hCg', scope: 'Sole immediate246 existential, before m₀/all n/w/z/external constants.', choiceInputPropName: 'hCg', completeChoiceInputPropType: cgProp, completePropContextRef: 'cgSelectionContext', enclosingParameterContext: cgCtx},
  {name: 'm₀', type: 'MeasurableSpace Ω', rhs: 'Classical.choose hModel', scope: 'Same immediate246 sole reduced-space witness after cg, before μ₀ and both branches.', choiceInputPropName: 'hModel', completeChoiceInputPropType: modelProp, completePropContextRef: 'm0SelectionContext', enclosingParameterContext: modelCtx},
];
const cutoffs = [
  {name: 'kClipped', type: 'ℕ', rhs: 'Classical.choose hClippedCutoff', choiceInputPropName: 'hClippedCutoff', completeChoiceInputPropType: clippedExistential},
  {name: 'kPayment', type: 'ℕ', rhs: 'Classical.choose hPaymentCutoff', choiceInputPropName: 'hPaymentCutoff', completeChoiceInputPropType: paymentExistential},
].map(r => ({...r, scope: 'For fixed payment n,w,z/C1..C4/hSZcBudget/hzMomentWindow and τ>0 only; no uniform k or n rate is claimed.', completePropContextRef: 'paidCutoffChoiceContext', enclosingParameterContext: cutoffContext}));
const instances = old.instanceInventory.map(r => ({...r,
  status: 'Inherited optional exact-scope instance; no new247 local instance.',
  completePropContextRef: r.name === 'augmentedProductSpace' || r.name === 'finiteIndex' ? 'originalUniversalScopeForOldInstances' : (r.name === 'selectedSpace' || r.name === 'selectedCountableGeneration' ? 'selectedModelContext' : 'originalParameters'),
}));
for (const r of instances) r.enclosingParameterContext = contexts[r.completePropContextRef];
const implicitInstances = [
  {type: 'Preorder ℕ', actualRHS: '(inferInstance : Preorder ℕ)'},
  {type: 'IsDirectedOrder ℕ', actualRHS: '(inferInstance : IsDirectedOrder ℕ)'},
  {type: 'Nonempty ℕ', actualRHS: '(inferInstance : Nonempty ℕ)'},
].map(r => ({...r, scope: 'Only the ℕ specialization of Filter.eventually_atTop; implicit existing core/Mathlib instance argument, not a new local letI or assumption.'}));
const apiPacketPath = root + '/drafts/oq56/unit178/lead-primary-api-01/integer-tail-filter-monotonicity-source-packet.json';
const apiPacket = JSON.parse(read(apiPacketPath));
assert(apiPacket.mathlibHEAD === '807d3836b165983210ee2ecf3cd28f239436949c', 'mathlib mismatch');
for (const f of apiPacket.files) for (const e of f.excerpts) assert(sha(e.raw) === e.rawSHA256, 'API raw excerpt mismatch');
const atTopPath = root + '/drafts/oq56/unit234/lead-api-reference-01/Mathlib__Order__Filter__AtTopBot__Basic.lean.md';
const atTop = read(atTopPath);
assert(atTop.includes('807d3836b165983210ee2ecf3cd28f239436949c') && atTop.includes('lemma eventually_atTop : (∀ᶠ x in atTop, p x) ↔ ∃ a, ∀ b, a ≤ b → p b := mem_atTop_sets'), 'atTop primary head missing');
const apiSelected = apiPacket.files[3];
const supplemental = [bind(apiPacketPath), bind(atTopPath), bind(root + '/library/lean-toolchain'), bind(root + '/library/lake-manifest.json')];
const inventory = {
  schema: 'oq56-unit247-complete-prospective-declaration-ordinary-instance-inventory-v1',
  status: 'STAGE1 DECLARATION/SOURCE-INTERFACE PROPOSAL ONLY; NO PROOF OR QUALIFICATION',
  module: newModule, publicTheorem: newModule + '.' + newName,
  producer246Freeze: bind(freeze + '/frozen-declaration.json'), producer246FullHead: bind(freeze + '/FROZEN-HEAD.txt'),
  producerQualificationBoundary: 'ENTIRE246 unqualified. Exact qualified246 and later explicit implementation activation are BOTH mandatory. This Stage1 completion does not grant either.',
  theoremParameterContext: parameters, completeResultType: head.slice(head.indexOf(' :\n') + 3).trim(),
  declarationContexts: contexts,
  ordinaryBindings: [...old.ordinaryBindings, ...newOrdinary],
  oldPublicOrdinaryOccurrences: 138, totalPublicOrdinaryOccurrences: 141, newPublicOrdinaryOccurrences: 3,
  old138RowsByteContentExactlyInherited246: true, newPublicOrdinaryData: newOrdinary,
  publicMirrorOrder: [...old.ordinaryBindings.map(r => r.name), ...newOrdinary.map(r => r.name)],
  optionalPublicOrdinaryMirrorRule: 'Only exact literal matching scopes/RHS/types; no extra aliases. All old138 rows are unchanged. Three new mirrors only in payment scope.',
  soleExistingWitnessSelections: choiceRows, newProofLocalOrdinaryData: cutoffs, newProofLocalOrdinaryCount: 2,
  optionalProofOrdinaryCount: 145, countDerivation: '138 inherited public mirrors + 3 new public mirrors + 2 sole immediate246 witnesses + 2 proposed new natural cutoffs =145; producer246 proof-local kTail/kJoint/kExact are NOT reselected.',
  inlineOrdinaryExpressionsNotNamedData: ['kClipped + kPayment', gap],
  newFactorSelections: [], newModelChoices: [], newExplicitSections: [], newProbabilityInstances: [],
  proofFactTypeDictionary: facts, completePropScopeRule: 'Every proposed named fact is explicitly typed by its complete Prop and complete enclosing parameter/let context here; no inferred-have alias or omitted ordinary datum is approved.',
  instanceInventory: instances, instanceEntryCount: instances.length, newInstanceEntryCount: 0,
  APIImplicitInstanceArguments: implicitInstances,
  noNeBotInstanceNeeded: 'Use pinned eventually_atTop to select kPayment, then the inline natural sum; no Eventually.exists invocation or new NeBot letI is required. Its complete primary type remains documented as an available alternative only.',
  completeNewData: newData, completeNewContract: newClause, completeExternalBinders: externalBinders,
  exactSourceCostInterpretation: 'Original P full weighted cost PLUS unperturbed original deleted weighted cost, divided by original I0; all three complete literal RHS appear in candidate payment scope. No perturbed η cost, new quantitative bound or hypothesis.',
  producerCallActualArguments: old.producerCallActualArguments,
  immediateProducerCall: oldModule + '.actual_original_same_witness_clipped_scalar_tail_application μ h hh hh2 hhsymm hcenter hprojectionsecond p hp2 hp3 hgp cBudget hcBudget',
  sourcePremiseAvailability: {
    originalAllParametersUnchanged: true, sameOnceCgM0Mu0MAugNuActualEta: true,
    allOld246OutputsRecoveredAfterOnlyNewDataClauseNameRemoval: true,
    whole246RecoveredSHA256: sha(recovered), C0: 'literal512', clipping: 'literal1',
    externalScalarInputExplicitAtCBudget: true, originalRemainderWindowAndStrictMomentWindowBothExplicit: true,
    newNDependency: 'No new eventual-n selection. Reuse complete246 hPayment246 at Cenv,aenv,t0,Menv before w,z and C1..C4/hSZcBudget/hzMomentWindow. The n cutoff may depend on fixed original data/cg and envelope parameters exactly as246; it does not depend on w,z,external constants or the strict-window proof.',
    kDependency: 'kClipped and kPayment may depend on fixed original data/model, Cenv,aenv,t0,Menv,n,w and its hypotheses,z,both windows,C1..C4,hSZcBudget,τ; no uniformity/rate is asserted.',
    lowerRoute: 'Exact246 lower minus original projection-zero, same246 transport νZ=Pzero, retained νZ≤payment, real order.',
    upperRoute: 'Complete246 per-τ upper and retained numerator payment at δ=τ; choose two explicit natural cutoffs, specialize at kClipped+kPayment; E2 and Pzero each≤payment; obtain normalUpper+3payment+2τ; eliminate τ using the literal positive quarter-gap by real linear arithmetic.',
    noProbabilityLimitCDFAtomsOrErrorZero: true, no239Selector: true,
  },
  allOriginalAssumptionsUnchanged: true, mathematicalGapsFoundAtStage1: [],
  primaryAPIBindings: supplemental, primaryAPIMissing: [],
  operationalPrerequisites: ['exact qualified246 complete independent source/proof review and exact server kernel/all-owner transitive-axiom receipt', 'lead freeze of247 complete header/ordinary/instance inventory', 'later explicit implementation activation'],
  implementationAuthorized: false, qualified: false, kernelChecked: false, axiomAudited: false,
  requestedModel: 'gpt-6.1-sol', requestedEffort: 'xhigh', actualBackend: null, actualModel: null, actualEffort: null,
  usage: {inputTokens: null, cachedInputTokens: null, outputTokens: null, reasoningSubsetTokens: null},
};
json('INTERFACE-INVENTORY.json', inventory);
// Byte-exact inherited API contexts are included in the review packet, not summarized away.
const apiDoc = `# Unit247 Stage1 complete primary APIs and actual specialization

STATUS: prospective declaration/source-interface proposal only. Entire246 remains unqualified. No implementation, elaboration or kernel/axiom acceptance is asserted.

## Immediate246 complete frozen preamble/head/closing

Binding: ${JSON.stringify(bind(freeze + '/FROZEN-HEAD.txt'))}

\`\`\`lean
${oldPreamble}${oldHead}${oldClosing}\`\`\`

## Complete inherited245/244 payment/transport/external APIs

The following previously bound source packet is copied losslessly in full. Its historical status text is not a new qualification claim. The complete246 head above has also been fully read; its unchanged inherited contexts and all actual new247 scopes are explicit in the inventory.

${read(oldAuthor + '/API-CONTEXT.md')}

## Pinned Filter primary head, structural context and raw excerpt

Packet binding: ${JSON.stringify(bind(apiPacketPath))}
Pinned mathlib: ${apiPacket.mathlibHEAD}

${apiSelected.excerpts.map(e => `Source ${apiSelected.sourcePath}; sourceSHA256 ${apiSelected.sourceSHA256}; lines ${e.firstLine1}–${e.lastLine1}; rawSHA256 ${e.rawSHA256}.

Complete chronological structural context:
\`\`\`lean
${e.chronologicalStructuralContext.map(c => c.raw).join('')}\`\`\`

Complete raw excerpt:
\`\`\`lean
${e.raw}\`\`\`
`).join('\n')}

## Pinned eventually_atTop complete source context

Binding: ${JSON.stringify(bind(atTopPath))}

${atTop}

## Exact used Filter specialization, instances and scope

\`\`\`lean
-- Complete generic atTop theorem effective context:
{α : Type*} [Preorder α] [IsDirectedOrder α] [Nonempty α] {p : α → Prop}
Filter.eventually_atTop :
  (∀ᶠ x in Filter.atTop, p x) ↔ ∃ a, ∀ b, a ≤ b → p b
-- Actual specialization after fixed payment n,w,z/external constants and τ>0:
(Filter.eventually_atTop :
  (∀ᶠ k : ℕ in Filter.atTop, ν.real (E k) ≤ payment + τ) ↔
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ν.real (E k) ≤ payment + τ)
-- Complete generic intersection theorem:
{α : Type u} {p q : α → Prop} {f : Filter α}
Filter.Eventually.and :
  f.Eventually p → f.Eventually q → ∀ᶠ x in f, p x ∧ q x
-- Available generic existence theorem; NOT needed by the chosen two-cutoff route:
{α : Type u} {p : α → Prop} {f : Filter α} [Filter.NeBot f]
Filter.Eventually.exists : (∀ᶠ x in f, p x) → ∃ x, p x
\`\`\`

The proposed implementation uses eventually_atTop.mp for hPaymentEventuallyAtTau and retains the complete resulting existential as hPaymentCutoff. The ℕ instance arguments are literally (inferInstance : Preorder ℕ), (inferInstance : IsDirectedOrder ℕ), (inferInstance : Nonempty ℕ), in that fixed payment/tolerance scope. They are existing implicit arguments; no new local letI. kClipped and kPayment use Classical.choose on exactly the complete inventoried Props, with Classical.choose_spec as their full all-k specifications. Their inline sum is at least each. No NeBot instance is required and no undisclosed Eventually.exists choice is licensed.

Eventual intersection is available from the complete primary and head, but no new n intersection is needed: the inherited eventual-n proposition itself is strengthened pointwise for all its w,z/external constants. The needed k intersection is represented by the inline sum after eventual_atTop extraction. All naturals/order steps are ordinary omega/linarith arithmetic; no new helper theorem is invented.

## Full actual immediate producer binding

${inventory.immediateProducerCall}

Ω/mΩ and every explicit argument are the identical original binder. Select cg and m₀ only from this complete246 result. For its universal clause use n, hn, literal(512 : ℝ), a proof of0≤512, z and 0≤z from original hz. Use SAME C1,C2,C3,C4,hSZcBudget,hz and hzMomentWindow. Universal and payment ν/η/E/E2/Z expressions match by the complete literal let RHS, not a fresh stochastic model. Every newly proposed scalar Prop, ordinary datum, RHS, choice input and enclosing scope is explicit in INTERFACE-INVENTORY.json.

## Literal512 data match

${newData}

T0 is the exact universal T0 at512. L0 is the universal sum of δ0 after expanding its Fz/δ0 lets. sourceCost0 is its exact original fullTest0 plus original unperturbed deletedTest0 weighted numerator divided by I0, expanding A0/B0/A0delete/B0delete/ℓ0/S0/S0minus/I0, all at512. Existing D1, ξ0 and P remain the literal public original quantities. No η-dependent cost or additional assumption occurs.
`;
put('API-CONTEXT.md', apiDoc);
const bindings = JSON.parse(read(own + '/INPUT-BINDINGS.json'));
bindings.supplementalReadOnlyPrimaryBindings = supplemental;
bindings.allSupplementalPinnedExcerptsHashVerified = true;
json('INPUT-BINDINGS.json', bindings);
const localChecks = {
  schema: 'oq56-unit247-stage1-local-static-validation-v1', atUTC: new Date().toISOString(),
  activationVerified: true, activationInputCountDerived: activation.inputs.length,
  activationInputsByteHashVerified: true, old246FullHeadByteExactRecovered: true,
  inherited245FullHeadLosslesslyReadThrough246AndRecoveredExact: true,
  inherited245FullHeadIncludedExactInPrimaryAPIContext: true,
  inherited244CompleteHeadIncludedExactInPrimaryAPIContext: true,
  old246ExpectedSHA256: bind(freeze + '/FROZEN-HEAD.txt').sha256, recovered246SHA256: sha(recovered),
  wholeOld138OrdinaryRowsExact: JSON.stringify(inventory.ordinaryBindings.slice(0,138)) === JSON.stringify(old.ordinaryBindings),
  publicOrdinaryCountDerived: inventory.ordinaryBindings.length, newPublicOrdinaryCountDerived: newOrdinary.length,
  newNatCutoffsDerived: cutoffs.length, optionalProofOrdinaryCountDerived: inventory.ordinaryBindings.length + choiceRows.length + cutoffs.length,
  everyNewOrdinaryHasFullTypeRHSContextAndChoicePropWhereRequired: [...newOrdinary,...choiceRows,...cutoffs].every(r => r.type && r.rhs && r.enclosingParameterContext && (!r.choiceInputPropName || r.completeChoiceInputPropType)),
  everyNewNamedFactHasFullPropAndCompleteContext: Object.values(facts).every(r => r.type && r.enclosingParameterContext),
  fullPropRecordCountDerived: Object.keys(facts).length,
  instanceCountDerived: instances.length, newLocalInstanceCount: 0, implicitExistingNatAPIInstanceArguments: implicitInstances.length,
  allInstancesHaveCompleteTypeRHSContext: instances.every(r => r.type && r.rhs && r.enclosingParameterContext),
  noProofBody: !/\b(?:by|sorry|admit|axiom|unsafe|native_decide)\b/.test(preamble+head+closing),
  noSelfImport: !preamble.includes('import ' + newModule), immediate246Import: preamble.startsWith('import ' + oldModule + '\n'),
  bothWindowsExplicit: head.includes('hzMomentWindow') && head.includes('remainderWindowScale'),
  onlyNewDataAreT0L0SourceCost0: JSON.stringify(newOrdinary.map(r=>r.name)) === JSON.stringify(['T0','L0','sourceCost0']),
  no239SelectorOrCostAssumption: !newData.includes('η') && !newClause.includes('239'),
  preservedPaymentLiteral: head.includes('(3 : ℝ) * Real.exp (-qOrder) + Real.exp (-cg * (n : ℝ)) +\n            (4 : ℝ) * Real.exp (-(z * Real.sqrt (n : ℝ)) / (2 : ℝ))'),
  candidateUtf8LfNoBom: [preamble,head,closing].every(s=>!s.includes('\r')&&!s.startsWith('\ufeff')),
  pinnedFilterRawExcerptsHashVerified: true, primaryMissing: [],
  leanCalls: 0, serverCalls: 0, networkCalls: 0, uploadCalls: 0, gitOrPublicationAPICalls: 0, children: 0,
  staticOnly: true, implementationAuthorized: false, qualified: false, whole246Qualified: false,
};
for(const k of ['wholeOld138OrdinaryRowsExact','everyNewOrdinaryHasFullTypeRHSContextAndChoicePropWhereRequired','everyNewNamedFactHasFullPropAndCompleteContext','allInstancesHaveCompleteTypeRHSContext','noProofBody','noSelfImport','immediate246Import','bothWindowsExplicit','onlyNewDataAreT0L0SourceCost0','no239SelectorOrCostAssumption','preservedPaymentLiteral','candidateUtf8LfNoBom']) assert(localChecks[k],k);
json('LOCAL-VALIDATION.json', localChecks);
console.log(JSON.stringify({generated:true,head:bind(own+'/CANDIDATE-HEAD.txt'),whole246Recovered:localChecks.old246FullHeadByteExactRecovered,ordinary:localChecks.publicOrdinaryCountDerived,newData:newOrdinary.length,newCutoffs:cutoffs.length,facts:Object.keys(facts).length,instances:instances.length,proof:false,qualified:false},null,2));
