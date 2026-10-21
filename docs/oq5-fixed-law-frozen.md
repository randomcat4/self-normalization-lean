# Frozen source interfaces for the p35 fixed-law foundations

These interfaces were frozen and independently checked against p35 before implementation. Unit03 uses its documented v2 narrower integrable-observable helper. The actual source signatures and final checks are recorded in oq5-fixed-law-review.md.

# OQ56 unit 01 — fixed category law (frozen v1)

Date: 2026-10-21. Owner: OQ56 lead. Root remains OPEN.
Sources: current/oq56/inputs02/p35.md §3, lines 66–101; contract C0/C1. Source SHA256 F5308D1BCDBE2C54E075626617572BF264E3148DD4393324A22AC9664E4E2DA5.

## Exact mathematical interface

Namespace Shao.OQ5.P35. For c : ℕ define once, without any current-sample-size parameter:
* categoryMass c : ℝ := if c = 0 then 16382 / 16383 else (1 / 16384 : ℝ)^c.
* categoryScale c : ℝ := (4 : ℝ)^c.
* categoryValue c : ℝ := if c = 0 then 0 else (32 : ℝ)^c.
* featureMean : ℝ := 1 / 511.
* categoryFeature c : ℝ := categoryValue c - featureMean.
* categoryOffset c : ℝ := if c = 0 then 0 else (categoryScale c - 1) * (categoryFeature c)^2 / ((categoryScale c)^4 - 2).

Required exact core conclusions (separate theorems, no extra hypotheses):
categoryMass_nonneg c : 0 ≤ categoryMass c
categoryMass_pos c : 0 < categoryMass c
hasSum_categoryMass : HasSum categoryMass 1
hasSum_mass_value : HasSum (fun c => categoryMass c * categoryValue c) (1/511)
hasSum_mass_value_sq : HasSum (fun c => categoryMass c * categoryValue c ^ 2) (1/15)
categoryOffset_nonneg c : 0 ≤ categoryOffset c
categoryOffset_le c : categoryOffset c ≤ 2 * categoryScale c ^ 2
summable_mass_offset_pow (r : ℕ) (hr : r ≤ 3) : Summable (fun c => categoryMass c * categoryOffset c ^ r)

Supporting algebra and geometric-series lemmas may be added without changing these conclusions. All values at c=0 must be handled; the positive-category identities use c=j+1. No fourth feature moment is assumed or asserted finite. Divergence of fourth moment is a subsequent independent unit, not an input to this one.

## Measure extension (next dependency, freeze separately)

Construct an actual probability measure on ℕ with these exact atom masses; prove the integrals of v and v² and integrability of d,d²,d³. Then use the product with an independent uniform law on [-1,1] and push forward (c,a)↦3c+a. Exact full-law and decoding declarations are not yet frozen and must not be implemented until separately frozen. An infinite iid sequence and real Borel kernel are still required for C0 completion.

## Exclusions and acceptance

No triangular array, no n parameter in law/kernel, no change of masses or d coefficients, no p52/p53 scope. No sorry/admit/new axiom/unsafe/native_decide. All Lean checking is server-only in assigned worktree; shared cache read-only. Author must not review own encoding/proof. First blind semantic check precedes implementation, then actual targeted compilation and fresh independent proof review with axiom audit. Partial unit acceptance is not OQ5 completion.


# OQ56 unit02 — real encoding, frozen v1

Source: p35 §3 (X=3C+A; disjoint intervals recover C,A by Borel maps), C0. Source hash as unit01.

Exact declarations in namespace Shao.OQ5.P35:
encodeObservation (c : ℕ) (a : ℝ) : ℝ := 3 * (c : ℝ) + a
decodeCategory (x : ℝ) : ℕ := Nat.floor ((x+1)/3)
decodeNoise (x : ℝ) : ℝ := x - 3 * (decodeCategory x : ℝ)

Required theorems:
measurable_encodeObservation : Measurable (fun ca : ℕ × ℝ => encodeObservation ca.1 ca.2)
measurable_decodeCategory : Measurable decodeCategory
measurable_decodeNoise : Measurable decodeNoise
decodeCategory_encode (c : ℕ) (a : ℝ) (ha : a ∈ Set.Icc (-1 : ℝ) 1) : decodeCategory (encodeObservation c a) = c
decodeNoise_encode (c : ℕ) (a : ℝ) (ha : a ∈ Set.Icc (-1 : ℝ) 1) : decodeNoise (encodeObservation c a) = a
encode_decode (x : ℝ) : encodeObservation (decodeCategory x) (decodeNoise x) = x

Borel structures on ℕ, ℝ and their product are standard. This is deterministic coding only; no law, probability, iid, moments or root theorem claim.
Off the support intervals these decoder formulas are an explicit Borel extension. The original says recovery maps exist, and the contract gives the zero extension as one possible choice; agreement off support is not claimed or needed. Both endpoints ±1 are included. The floor argument belongs to [c,c+2/3], so no interval-end overlap or c=0 failure occurs.

No new hypotheses, no premise changes. No sorry/admit/new axiom/unsafe/native_decide. Compile only on server. Blind source/statement review before implementation; independent proof review after compilation.


# OQ56 unit03 — actual fixed atomic law, frozen v2

Source p35 §3 (lines 66–99); C0 and numeric portion of C1. Category coefficient definitions are frozen in unit01/frozen-v1.md. They do not depend on current sample size.

Namespace Shao.OQ5.P35. Imports FixedLawCoefficients and pinned SumMeasure.
categoryMeasure : MeasureTheory.Measure ℕ := MeasureTheory.Measure.sum (fun c : ℕ => ENNReal.ofReal (categoryMass c) • MeasureTheory.Measure.dirac c)

Exact required conclusions, no extra hypotheses:
instance categoryMeasure_isProbabilityMeasure : MeasureTheory.IsProbabilityMeasure categoryMeasure
categoryMeasure_singleton (c : ℕ) : categoryMeasure {c} = ENNReal.ofReal (categoryMass c)
integrable_categoryMeasure_iff (f : ℕ → ℝ) : MeasureTheory.Integrable f categoryMeasure ↔ Summable (fun c => categoryMass c * ‖f c‖)
integral_categoryMeasure (f : ℕ → ℝ) (hf : MeasureTheory.Integrable f categoryMeasure) : (∫ c, f c ∂categoryMeasure) = ∑' c, categoryMass c * f c
integrable_categoryValue : MeasureTheory.Integrable categoryValue categoryMeasure
integral_categoryValue : (∫ c, categoryValue c ∂categoryMeasure) = 1/511
integrable_categoryValue_sq : MeasureTheory.Integrable (fun c => categoryValue c ^ 2) categoryMeasure
integral_categoryValue_sq : (∫ c, categoryValue c ^ 2 ∂categoryMeasure) = 1/15
integrable_categoryOffset_pow (r : ℕ) (hr : r ≤ 3) : MeasureTheory.Integrable (fun c => categoryOffset c ^ r) categoryMeasure

The integral_categoryMeasure identity requires actual integrability. Every numeric moment theorem must separately prove the integrability result. Version 2 records this premise explicitly after reading pinned integral_sum_dirac_eq_tsum, which has weighted-norm summability as an input. No claim about nonintegrable f is made. This changes only a convenience identity, not a root assumption.

Additional helper lemmas permitted. No moment of order four or feature/increment independence assumption. This does not yet construct the continuous product, real law, infinite iid sequence, kernel, rank-one operator, positive denominator or tails. Atomic law alone is only partial C0/C1. Every public theorem must be server compiled, independently reviewed and axiom-audited. No sorry/admit/new axiom/unsafe/native_decide. Shared cache remains read-only. Author must not review own encoding/proof.



# OQ56 unit04 — actual continuous product and real law, frozen v1

Source p35 §3 (X=3C+A, A independent Uniform[-1,1]), contract C0. FixedCategoryLaw unit03 fixes the actual category measure; RealEncoding unit02 fixes Borel encoding/decoding with exact support recovery.

Namespace Shao.OQ5.P35, standard Borel structures.
noiseLaw : MeasureTheory.Measure ℝ := ProbabilityTheory.cond MeasureTheory.volume (Set.Icc (-1 : ℝ) 1)
observationPairLaw : MeasureTheory.Measure (ℕ × ℝ) := categoryMeasure.prod noiseLaw
realLaw : MeasureTheory.Measure ℝ := MeasureTheory.Measure.map (fun ca : ℕ × ℝ => encodeObservation ca.1 ca.2) observationPairLaw

Required exact conclusions, no extra premises:
instance noiseLaw_isProbabilityMeasure : MeasureTheory.IsProbabilityMeasure noiseLaw
instance observationPairLaw_isProbabilityMeasure : MeasureTheory.IsProbabilityMeasure observationPairLaw
instance realLaw_isProbabilityMeasure : MeasureTheory.IsProbabilityMeasure realLaw
noiseLaw_ae_mem : ∀ᵐ a ∂noiseLaw, a ∈ Set.Icc (-1 : ℝ) 1
noiseLaw_absolutelyContinuous : noiseLaw ≪ MeasureTheory.volume
pairLaw_ae_noise_mem : ∀ᵐ ca ∂observationPairLaw, ca.2 ∈ Set.Icc (-1 : ℝ) 1
map_decode_realLaw : MeasureTheory.Measure.map (fun x => (decodeCategory x, decodeNoise x)) realLaw = observationPairLaw
map_category_realLaw : MeasureTheory.Measure.map decodeCategory realLaw = categoryMeasure
map_noise_realLaw : MeasureTheory.Measure.map decodeNoise realLaw = noiseLaw

The product measure provides the actual independence of category/noise; recovery of their entire joint law rules out marginal-only substitutions. This law is chosen once with no sample-size parameter. The interval normalization is relative to Lebesgue volume, not counting measure; both closed endpoints are included and null for noiseLaw. The arbitrary off-support Borel extension from unit02 does not affect the pushforward/recovered law. No claim of independence between categoryOffset and categoryFeature; both remain functions of category.

This is still partial C0. An infinite iid sample, fixed symmetric Borel kernel and actual moments/projections remain subsequent dependencies. No root theorem or tail certification. No sorry/admit/new axiom/unsafe/native_decide. Proofs and compilation only on assigned server worktree; independent statement review before implementation and fresh proof review after compilation.


# OQ56 unit05 — centered feature moments, frozen v1

Source: p35 §3, lines 73–99; contract C1. Use exactly unit01 categoryFeature c = categoryValue c - featureMean, featureMean = 1/511, and actual categoryMeasure from unit03. No new probability law and no extra root assumptions.

Namespace Shao.OQ5.P35:
featureVariance : ℝ := 1/15 - featureMean ^ 2
integrable_categoryFeature : MeasureTheory.Integrable categoryFeature categoryMeasure
integral_categoryFeature : (∫ c, categoryFeature c ∂categoryMeasure) = 0
integrable_categoryFeature_sq : MeasureTheory.Integrable (fun c => categoryFeature c ^ 2) categoryMeasure
integral_categoryFeature_sq : (∫ c, categoryFeature c ^ 2 ∂categoryMeasure) = featureVariance
featureVariance_pos : 0 < featureVariance

No fourth moment, no independence of d and feature, no current n parameter. Supporting helpers allowed. This certifies only the category feature scalar moments, not kernel integrability, projection, operator rank, iid, studentizer or tails. No sorry/admit/new axiom/unsafe/native_decide. Compile only on assigned server; no shared cache writes. Independent source translation before proof, independent proof/source-to-Lean and axioms review afterwards.
