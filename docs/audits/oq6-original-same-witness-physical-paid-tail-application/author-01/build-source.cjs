const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const root = __dirname;
const work = 'C:/game/shao lean';
const freeze = path.join(work, 'drafts/oq56/unit248/freeze-01');
const read = p => fs.readFileSync(p, 'utf8');
const json = p => JSON.parse(read(p));
const inv = json(path.join(freeze, 'INTERFACE-INVENTORY.json'));
const facts = Object.fromEntries(inv.frozenProofFacts.map(x => [x.name, x]));
const lines = [];
const emit = s => lines.push(s.replace(/\r\n/g, '\n').replace(/\n+$/, ''));
const indent = (s, n) => {
  const ls = s.replace(/\r\n/g, '\n').replace(/^\n+|\n+$/g, '').split('\n');
  const base = Math.min(...ls.filter(l => l.trim()).map(l => l.match(/^ */)[0].length));
  return ls.map(l => ' '.repeat(n) + l.slice(base)).join('\n');
};
const projection = (name, index, count) => name + '.2'.repeat(index - 1) + (index === count ? '' : '.1');
const have = (name, rhs, n = 2) => {
  if (!facts[name]) throw new Error('Unfrozen fact: ' + name);
  emit(' '.repeat(n) + 'have ' + name + ' :\n' + indent(facts[name].fullType, n + 4) + ' :=\n' + indent(rhs, n + 4));
};
const parseLets = s => [...s.matchAll(/^\s*let (?!I\b)([^ :\n]+)\s*:/gm)].map(x => x[1]);

// The qualified producer TYPE is restored from the lossless lexical dictionary.
// This is a local byte check, not Lean execution or renewed producer review.
const dp = path.join(work, 'drafts/oq56/unit247/final-review-01/TYPE-LOSSLESS-DICTIONARY.json');
const d = json(dp);
function expand(xs) {
  return xs.flatMap(x => typeof x === 'string' ? [x] : expand(d.dictionary[x.ref]));
}
const tokens = expand(d.main);
if (tokens.length !== d.tokenCount || tokens.length !== d.triviaBeforeEachExpandedToken.length) throw Error('TYPE token count mismatch');
const restored = tokens.map((t, i) => d.triviaBeforeEachExpandedToken[i] + t).join('') + d.trailingTrivia;
const raw = fs.readFileSync(path.join(work, 'drafts/oq56/unit247/normalized-owner-evidence-01/actual-owned-types.txt'));
const restoredBuffer = Buffer.from(restored, 'utf8');
if (!raw.equals(restoredBuffer)) throw Error('TYPE restoration differs');
const digest = crypto.createHash('sha256').update(raw).digest('hex');
if (digest !== d.rawSHA256 || raw.length !== d.rawBytes) throw Error('TYPE bound hash mismatch');
fs.writeFileSync(path.join(root, 'TYPE247-RESTORATION.json'), JSON.stringify({
  schema: 'oq56-unit248-qualified247-public-TYPE-lossless-restoration-v1',
  dictionaryPath: dp, dictionaryCount: Object.keys(d.dictionary).length,
  mainItems: d.main.length, expandedTokens: tokens.length,
  restoredSHA256: digest, restoredBytes: raw.length, exactBytes: true,
  dictionary318ReadComplete: true, currentMain431ReadComplete: true,
  onlyPublicTYPEConsumed: true, producerProofReReview: false,
  Lean: 0, PP: 0, AX: 0, server: 0
}, null, 2) + '\n');

emit(read(path.join(freeze, 'FROZEN-PREAMBLE.txt')));
emit(read(path.join(freeze, 'FROZEN-HEAD.txt')) + ' := by');
emit(read(path.join(freeze, 'FROZEN-INITIAL-INTRO.txt')));
emit(read(path.join(freeze, 'FROZEN-H247-CALL.txt')));
emit('  intro g r v rho β cWindow');
have('hrSymm', 'by\n  intro o y\n  dsimp only [r]\n  rw [hhsymm o y]\n  ring');
have('hRhoNonneg', 'Real.sqrt_nonneg v');
have('hCg', projection('h247', 7, 7));
emit('  let cg : ℝ := Classical.choose hCg');
have('hcgpos', '(Classical.choose_spec hCg).1');
have('hModel', '(Classical.choose_spec hCg).2');
emit('  let m₀ : MeasurableSpace Ω := Classical.choose hModel');
have('hm₀', 'Classical.choose (Classical.choose_spec hModel)');
have('hcg', 'Classical.choose (Classical.choose_spec (Classical.choose_spec hModel))');
emit('  let μ₀ : @Measure Ω m₀ := μ.trim hm₀');
emit('  letI : MeasurableSpace Ω := m₀');
emit('  letI : MeasurableSpace.CountablyGenerated Ω := hcg');
have('hRetained247', 'Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hModel))');
have('hμ₀Probability', 'hRetained247.1');
have('hPaymentAll247', 'hRetained247.2.2');
emit('  refine ⟨' + Array.from({ length: 6 }, (_, k) => projection('h247', k + 1, 7)).join(', ') + ',\n    cg, hcgpos, m₀, hm₀, hcg, hμ₀Probability, hRetained247.2.1, ?_⟩');
emit('  intro Cenv aenv t0 Menv hCenv haenv ht0 hMenv');
emit('  refine Filter.Eventually.mono\n    (hPaymentAll247 Cenv aenv t0 Menv hCenv haenv ht0 hMenv)\n    (fun (n : ℕ) (hAllAtN247 : 4 ≤ n ∧\n' + indent(facts.hPaymentAtN247.fullType, 8) + ') => ?_)');
emit('  have hn : 4 ≤ n := hAllAtN247.1');
have('hPaymentAtN247', 'hAllAtN247.2');
emit('  refine ⟨hn, ?_⟩');
emit('  intro w hW hWR hSq hSqBound hEnv z hz hzWindow');
const paymentNames = parseLets(inv.completeContexts.paymentOrdinaryContext);
emit('  intro ' + paymentNames.join(' '));
const currentType = facts.hPaymentAtN247.fullType.slice(facts.hPaymentAtN247.fullType.indexOf('        let mN'));
emit('  have hAtCurrent247 :\n' + indent(currentType, 6) + ' :=\n    hPaymentAtN247 w hW hWR hSq hSqBound hEnv z hz hzWindow');
have('hClippedCurrentBounds', projection('hAtCurrent247', 38, 39));
have('hNewPhysicalWhole', 'by\n  intro Tphysical H1source payment1 Ephysical\n' + '  -- The following block uses the original sample sigma algebra and original P.\n' +
  '  letI : MeasurableSpace (Fin n → Ω) := mN\n' +
  '  letI : @IsProbabilityMeasure (Fin n → Ω) mN P :=\n' +
  '    (inferInstance : @IsProbabilityMeasure (Fin n → Ω) mN P)\n' +
  '__PHYSICAL_BODY__');

const physical = [];
function ph(s) { physical.push(s); }
// have() above reindents the full proof uniformly; physical fragments below use
// indentation relative to that proof's first `by` line.
function fh(name, rhs, n = 2) {
  return ' '.repeat(n) + 'have ' + name + ' :\n' + indent(facts[name].fullType, n + 4) + ' :=\n' + indent(rhs, n + 4);
}
ph(fh('hWindowOne', 'hz.trans hzWindow'));
ph(fh('hWindowOnePublic', 'hWindowOne'));
ph(fh('hKtailNonneg', `by
  dsimp only [Ktail, Shao.OQ6.BoundedProductEnvelopeTails.tailScale,
    Shao.OQ6.BoundedProductEnvelopeTails.squareTailScale]
  exact le_trans
    (mul_nonneg (le_of_lt (Real.exp_pos 1))
      (show 0 ≤ Menv + 1 by linarith only [hMenv]))
    (le_max_left _ _)`));
ph(fh('hAtOne247', 'hPaymentAtN247 w hW hWR hSq hSqBound hEnv 1 (le_refl 1) hWindowOne'));
ph(fh('hH1Measurable', projection('hAtOne247', 7, 39)));
ph(fh('hH1Payment', 'by\n  simpa only [one_mul] using ' + projection('hAtOne247', 16, 39)));
ph(fh('hMeas220', `@Shao.OQ6.OriginalClippedStatisticMeasurable.actual_normalized_compact_clipped_observables
  Ω mΩ μ hμProbability h hh hh2 hhsymm hcenter hprojectionsecond
  n hn 0 (by norm_num) (by norm_num) 512 (by norm_num)`));
ph(fh('hPhysicalMeasurable', projection('hMeas220', 12, 17)));
ph(fh('hClippedMeasurable', projection('hMeas220', 11, 17)));
ph(fh('hDisagreementMeasurable', '(measurableSet_eq_fun hClippedMeasurable hPhysicalMeasurable).compl'));
ph(fh('hSmallOne', `by
  intro ζ hζ
  exact bounded_remainder_small_window n g r ζ Ktail t0 1
    hrSymm hn hKtailNonneg ht0 (le_refl 1) hWindowOne
    hζ.2.1 hζ.2.2 hζ.1`));
ph(fh('hSmallAndLowerOne', `by
  intro ζ hζ
  refine ⟨(hSmallOne ζ hζ).1, (hSmallOne ζ hζ).2.2.2, ?_⟩
  linarith only [(abs_le.mp (hSmallOne ζ hζ).2.2.2).1]`));
ph(fh('hPhysicalFinite', 'fun s => measure_ne_top P s'));
ph(fh('hPhysicalGuardedPackage', `by
  intro hStudentizerWindow
${fh('hLiteralComparison', `by
  intro ζ hζ
  exact literal_clippedCentered_comparison_on_projectionGood n g r rho 1 ζ
    hn (le_refl 1) hrSymm hRhoNonneg
    (by simpa only [mul_one] using hStudentizerWindow) hζ.1
    (hSmallAndLowerOne ζ hζ).2.2`, 2)}
  have hDisagreementSubset : Ephysical ⊆ H1sourceᶜ := by
    intro ζ hζ hGood
    exact hζ (hLiteralComparison ζ hGood).2.2.2.2
  have hDisagreementMono : P.real Ephysical ≤ P.real H1sourceᶜ :=
    measureReal_mono hDisagreementSubset (hPhysicalFinite H1sourceᶜ)
  have hDisagreementPayment : P.real Ephysical ≤ payment1 :=
    hDisagreementMono.trans hH1Payment
${fh('hClosedUpperDiff', `by
  intro t ζ hζ hEq
  rcases hζ with hζ | hζ
  · exact hζ.2 (by simpa only [Set.mem_setOf_eq, hEq] using hζ.1)
  · exact hζ.2 (by simpa only [Set.mem_setOf_eq, hEq] using hζ.1)`, 2)}
${fh('hClosedLowerDiff', `by
  intro t ζ hζ hEq
  rcases hζ with hζ | hζ
  · exact hζ.2 (by simpa only [Set.mem_setOf_eq, hEq] using hζ.1)
  · exact hζ.2 (by simpa only [Set.mem_setOf_eq, hEq] using hζ.1)`, 2)}
  have hUpperComparison : ∀ t : ℝ,
      |P.real {ζ : Fin n → Ω | t ≤ Tphysical ζ} -
        P.real {ζ : Fin n → Ω | t ≤ T0 ζ}| ≤ P.real Ephysical := by
    intro t
    exact (abs_measureReal_sub_le_measureReal_symmDiff (μ := P)
      (hPhysicalMeasurable measurableSet_Ici).nullMeasurableSet
      (hClippedMeasurable measurableSet_Ici).nullMeasurableSet).trans
      (measureReal_mono (hClosedUpperDiff t) (hPhysicalFinite Ephysical))
  have hLowerComparison : ∀ t : ℝ,
      |P.real {ζ : Fin n → Ω | Tphysical ζ ≤ t} -
        P.real {ζ : Fin n → Ω | T0 ζ ≤ t}| ≤ P.real Ephysical := by
    intro t
    exact (abs_measureReal_sub_le_measureReal_symmDiff (μ := P)
      (hPhysicalMeasurable measurableSet_Iic).nullMeasurableSet
      (hClippedMeasurable measurableSet_Iic).nullMeasurableSet).trans
      (measureReal_mono (hClosedLowerDiff t) (hPhysicalFinite Ephysical))
  refine ⟨hLiteralComparison, hDisagreementSubset, hDisagreementMono,
    hDisagreementPayment, ?_, ?_⟩
  · intro t
    exact ⟨hPhysicalMeasurable measurableSet_Ici,
      hClippedMeasurable measurableSet_Ici,
      hPhysicalMeasurable measurableSet_Iic,
      hClippedMeasurable measurableSet_Iic,
      hClosedUpperDiff t, hClosedLowerDiff t,
      hUpperComparison t, hLowerComparison t,
      (hUpperComparison t).trans hDisagreementPayment,
      (hLowerComparison t).trans hDisagreementPayment⟩
  · intro C1 C2 C3 C4 hSZcBudget hzMomentWindow
    constructor
    · linarith only [
        (hClippedCurrentBounds C1 C2 C3 C4 hSZcBudget hzMomentWindow).1,
        (abs_le.mp ((hUpperComparison z).trans hDisagreementPayment)).1]
    · linarith only [
        (hClippedCurrentBounds C1 C2 C3 C4 hSZcBudget hzMomentWindow).2,
        (abs_le.mp ((hUpperComparison z).trans hDisagreementPayment)).2]`));
ph('  exact ⟨hWindowOnePublic, hH1Measurable, hH1Payment,\n    hPhysicalMeasurable, hClippedMeasurable, hDisagreementMeasurable,\n    hSmallAndLowerOne, hPhysicalGuardedPackage⟩');

// Insert the substantive proof under the uniform indentation generated by have().
let source = lines.join('\n') + '\n';
source = source.replace(/^ *?__PHYSICAL_BODY__$/m, indent(physical.join('\n'), 8));
if (source.includes('__PHYSICAL_BODY__')) throw new Error('Unexpanded body');
// Preserve the literal frozen preamble and head byte-for-byte, including their
// intentional terminating newlines. Only the theorem's proof is inserted.
source = read(path.join(freeze, 'FROZEN-PREAMBLE.txt')) +
  read(path.join(freeze, 'FROZEN-HEAD.txt')) + ' := by\n' +
  source.slice(source.indexOf(read(path.join(freeze, 'FROZEN-INITIAL-INTRO.txt')).replace(/\n+$/, '')));
source += '  exact ⟨' + Array.from({ length: 39 }, (_, k) => projection('hAtCurrent247', k + 1, 39)).join(',\n    ') + ',\n    hNewPhysicalWhole⟩\n';
source += read(path.join(freeze, 'FROZEN-CLOSING.txt'));
if (/\r/.test(source)) throw Error('CR in source');
fs.writeFileSync(path.join(root, 'OriginalSameWitnessPhysicalPaidTailApplication.lean'), source, 'utf8');
console.log(JSON.stringify({ sourceBytes: Buffer.byteLength(source), sourceLF: source.split('\n').length - 1,
  sourceSHA256: crypto.createHash('sha256').update(source).digest('hex'), paymentNames,
  restorationSHA256: digest, forbidden: /\b(sorry|admit|axiom|unsafe|native_decide)\b/.test(source) }));
