# Frozen p35 construction and moment interfaces

Each interface below was source-reviewed before implementation. Final source hashes and independent gates are in oq5-construction-review.md.

# OQ56 unit06 — one actual infinite iid real sequence, frozen v1

Source p35 §1/3 and contract C0: one fixed real law with an iid sequence before all finite sample sizes. Use existing realLaw exactly. Standard measurable structure on ℕ→ℝ.

Namespace Shao.OQ5.P35:
sampleLaw : MeasureTheory.Measure (ℕ → ℝ) := MeasureTheory.Measure.infinitePi (fun _ : ℕ => realLaw)
sampleCoordinate (i : ℕ) (ω : ℕ → ℝ) : ℝ := ω i

Exact required conclusions:
instance sampleLaw_isProbabilityMeasure : MeasureTheory.IsProbabilityMeasure sampleLaw
measurable_sampleCoordinate (i : ℕ) : Measurable (sampleCoordinate i)
map_sampleCoordinate (i : ℕ) : MeasureTheory.Measure.map (sampleCoordinate i) sampleLaw = realLaw
iIndepFun_sampleCoordinate : ProbabilityTheory.iIndepFun sampleCoordinate sampleLaw
map_sampleCoordinate_pair (i j : ℕ) (hij : i ≠ j) : MeasureTheory.Measure.map (fun ω => (sampleCoordinate i ω, sampleCoordinate j ω)) sampleLaw = realLaw.prod realLaw

The sequence includes coordinate zero; any later finite statistic can use coordinates 0 through n-1 on this same probability space. No finite-n probability law, changing distribution, iid hypothesis or other mathematical premise may be added. Independence is full mutual iIndepFun, not just pairwise. The final pair-law theorem requires distinct indices and must retain that hypothesis; same-index fourth moments are not inferred.

Only actual sample construction is certified by this unit; kernel moments, projections, studentizer and probability tails still need proof. Pinned InfinitePi package closure must be supplied by root; authors may not fetch/write shared cache. Independent statement review before implementation; server-only actual compilation then fresh independent proof/semantic and axiom audit. No sorry/admit/new axiom/unsafe/native_decide. Authors may add helpers without changing these declarations.

# OQ56 unit07 — actual fixed Borel kernel and finite-row bridge, frozen v1

Sources: p35 §3, formula (8), lines 80–99; finite row matrix p35 §2, lines 28–31. C0 construction and D1 bridge only. Use exact existing RealEncoding, FixedLawCoefficients and RowIdentity definitions.

Namespace Shao.OQ5.P35:
observationOffset (x : ℝ) : ℝ := categoryOffset (decodeCategory x)
observationFeature (x : ℝ) : ℝ := categoryFeature (decodeCategory x)
populationKernel (x y : ℝ) : ℝ := decodeNoise x + decodeNoise y + observationOffset x + observationOffset y - observationFeature x * observationFeature y

Exact conclusions:
measurable_observationOffset : Measurable observationOffset
measurable_observationFeature : Measurable observationFeature
measurable_populationKernel : Measurable (fun xy : ℝ × ℝ => populationKernel xy.1 xy.2)
populationKernel_symmetric (x y : ℝ) : populationKernel x y = populationKernel y x
observationOffset_encode (c : ℕ) (a : ℝ) (ha : a ∈ Set.Icc (-1 : ℝ) 1) : observationOffset (encodeObservation c a) = categoryOffset c
observationFeature_encode (c : ℕ) (a : ℝ) (ha : a ∈ Set.Icc (-1 : ℝ) 1) : observationFeature (encodeObservation c a) = categoryFeature c
populationKernel_encode (c d : ℕ) (a b : ℝ) (ha : a ∈ Set.Icc (-1 : ℝ) 1) (hb : b ∈ Set.Icc (-1 : ℝ) 1) : populationKernel (encodeObservation c a) (encodeObservation d b) = a + b + categoryOffset c + categoryOffset d - categoryFeature c * categoryFeature d
populationKernel_sample {n : ℕ} (X : Fin n → ℝ) (i j : Fin n) : populationKernel (X i) (X j) = kernel (fun i => decodeNoise (X i)) (fun i => observationOffset (X i)) (fun i => observationFeature (X i)) i j

No current n parameter in populationKernel or law. The n in the last theorem only indexes a sample and does not change the population kernel. It is the raw uncentered p35 kernel; no normalization or variance scaling is done. Off-support formulas follow existing Borel extension. No probability/moment/integral/operator/tail claims. No fourth moment or d/Z independence. Additional helpers allowed without modifying these declarations. Preimplementation independent semantic review then server compilation, fresh independent proof review, whitelist axiom audit. No sorry/admit/new axiom/unsafe/native_decide.

# OQ56 unit08 — continuous noise moments, frozen v1

Source p35 §3: A independent Uniform[-1,1], EA=0, Var(A)=1/3 and bounded moments. Use existing noiseLaw exactly: normalized Lebesgue volume on the closed interval [-1,1], without any new law or premise.

Namespace Shao.OQ5.P35, exact required conclusions:
integrable_noiseLaw_abs_pow (r : ℕ) (hr : r ≤ 3) : MeasureTheory.Integrable (fun a : ℝ => |a| ^ r) noiseLaw
integrable_noiseLaw_id : MeasureTheory.Integrable (fun a : ℝ => a) noiseLaw
integral_noiseLaw_id : (∫ a : ℝ, a ∂noiseLaw) = 0
integrable_noiseLaw_sq : MeasureTheory.Integrable (fun a : ℝ => a ^ 2) noiseLaw
integral_noiseLaw_sq : (∫ a : ℝ, a ^ 2 ∂noiseLaw) = (1/3 : ℝ)

No current sample-size parameter, no change to normalized interval law, no moment of categoryFeature is asserted here. r=0 uses |a|^0=1 including at a=0. Supporting helpers allowed; authors must not modify these definitions/assumptions. Cached FTC/elementary polynomial antiderivatives are an available route, but proof strategy is not an assumption.

This is a bounded-noise moment dependency only, not kernel/projection/tail completion. Independent source/statement review precedes proof; server-only compilation, fresh independent proof/semantic review and transitive whitelist axiom audit follow. No sorry/admit/new axiom/unsafe/native_decide. Shared caches read-only and no commits by author.

# OQ56 unit09 — actual real-observation moments, frozen v1

Source p35 §3, C1. Existing actual realLaw, decodeNoise, observationFeature/Offset, featureVariance, and their exact laws/definitions are unchanged. Numeric category feature moments come from unit05 and continuous noise from unit08.

Namespace Shao.OQ5.P35, exact required conclusions:
integrable_decodeNoise_abs_pow (r : ℕ) (hr : r ≤ 3) : MeasureTheory.Integrable (fun x => |decodeNoise x| ^ r) realLaw
integrable_decodeNoise : MeasureTheory.Integrable decodeNoise realLaw
integral_decodeNoise : (∫ x, decodeNoise x ∂realLaw) = 0
integrable_decodeNoise_sq : MeasureTheory.Integrable (fun x => decodeNoise x ^ 2) realLaw
integral_decodeNoise_sq : (∫ x, decodeNoise x ^ 2 ∂realLaw) = (1/3 : ℝ)
integrable_observationFeature : MeasureTheory.Integrable observationFeature realLaw
integral_observationFeature : (∫ x, observationFeature x ∂realLaw) = 0
integrable_observationFeature_sq : MeasureTheory.Integrable (fun x => observationFeature x ^ 2) realLaw
integral_observationFeature_sq : (∫ x, observationFeature x ^ 2 ∂realLaw) = featureVariance
integrable_observationOffset_pow (r : ℕ) (hr : r ≤ 3) : MeasureTheory.Integrable (fun x => observationOffset x ^ r) realLaw
integral_observationOffset_pow (r : ℕ) (hr : r ≤ 3) : (∫ x, observationOffset x ^ r ∂realLaw) = ∫ c, categoryOffset c ^ r ∂categoryMeasure

These are actual integrals with separate actual integrability proofs, not formal equalities from nonintegrable zero conventions. Keep the r=0 boundary. No fourth feature moment, no category-feature/offset independence, no new probability assumptions, no sample-size dependence and no decoder embedding/injectivity hypothesis. Generic measurable map/integrability transport helpers may be added without modifying these declarations.

This is still a C1 moment dependency, without kernel-square/projection/operator/studentizer/tail certification. Independent statement review before proof; actual pinned server compilation and fresh independent proof/source-to-Lean and transitive axiom audit afterwards. No sorry/admit/new axiom/unsafe/native_decide. Shared cache read-only.

# OQ56 unit10 — actual kernel moments and Hoeffding identities, frozen v1

Source p35 §3, formulas (1),(8) and lines86–99; C1. Use the exact existing fixed raw populationKernel, realLaw, observationFeature/Offset and decodeNoise. Pair expectations use realLaw.prod realLaw, corresponding to two distinct iid samples by unit06.

Namespace Shao.OQ5.P35:
offsetMean : ℝ := ∫ x, observationOffset x ∂realLaw
populationMean : ℝ := 2 * offsetMean
populationProjection (x : ℝ) : ℝ := decodeNoise x + observationOffset x - offsetMean
populationResidual (x y : ℝ) : ℝ := -observationFeature x * observationFeature y

Required exact conclusions, no extra premises:
integrable_observationOffset : MeasureTheory.Integrable observationOffset realLaw
integrable_populationKernel : MeasureTheory.Integrable (fun xy : ℝ × ℝ => populationKernel xy.1 xy.2) (realLaw.prod realLaw)
integrable_populationKernel_sq : MeasureTheory.Integrable (fun xy : ℝ × ℝ => populationKernel xy.1 xy.2 ^ 2) (realLaw.prod realLaw)
integrable_populationKernel_right (x : ℝ) : MeasureTheory.Integrable (populationKernel x) realLaw
integral_populationKernel_right (x : ℝ) : (∫ y, populationKernel x y ∂realLaw) = populationProjection x + populationMean
integral_populationKernel : (∫ xy : ℝ × ℝ, populationKernel xy.1 xy.2 ∂realLaw.prod realLaw) = populationMean
populationResidual_decomposition (x y : ℝ) : populationKernel x y - populationMean - populationProjection x - populationProjection y = populationResidual x y
integrable_populationResidual_right (x : ℝ) : MeasureTheory.Integrable (populationResidual x) realLaw
integral_populationResidual_right (x : ℝ) : (∫ y, populationResidual x y ∂realLaw) = 0
integrable_populationResidual_sq : MeasureTheory.Integrable (fun xy : ℝ × ℝ => populationResidual xy.1 xy.2 ^ 2) (realLaw.prod realLaw)
integral_populationResidual_sq : (∫ xy : ℝ × ℝ, populationResidual xy.1 xy.2 ^ 2 ∂realLaw.prod realLaw) = featureVariance ^ 2

The squared residual requires two different coordinates' second moments, not a fourth feature moment. Offset and feature may be dependent; nothing factors a same-observation offset/feature product. Numeric integrals need the separately proved integrability. Kernel/mean/projection remain raw/unscaled. Supporting helper inequalities/transport permitted, no premise changes. This is still not the operator rank theorem, projection third moment/positive variance, true denominator, conditional rare events or tails. Preimplementation independent statement review then server-only actual Lean, independent proof/source review and whitelist axioms. No sorry/admit/new axiom/unsafe/native_decide.

# OQ56 unit11 — actual projection moment premises, frozen v1

Source p35 §3 lines88–99: g=A+d-dbar, Eg=0, 0<Eg²<∞, E|g|³<∞, Var(g)>=1/3. Use exact populationProjection, offsetMean and actual realLaw from preceding frozen units. No change of law/kernel/normalization.

Namespace Shao.OQ5.P35, exact required conclusions without additional premises:
integrable_populationProjection : MeasureTheory.Integrable populationProjection realLaw
integral_populationProjection : (∫ x, populationProjection x ∂realLaw) = 0
integrable_populationProjection_sq : MeasureTheory.Integrable (fun x => populationProjection x ^ 2) realLaw
integrable_populationProjection_abs_cube : MeasureTheory.Integrable (fun x => |populationProjection x| ^ 3) realLaw
integral_populationProjection_sq_ge : (1/3 : ℝ) ≤ ∫ x, populationProjection x ^ 2 ∂realLaw
integral_populationProjection_sq_pos : 0 < ∫ x, populationProjection x ^ 2 ∂realLaw

Actual category/noise independence is supplied by the existing full decoded joint product law, not by a new hypothesis. No feature/offset independence or fourth feature moment. The positive variance bound is for this unscaled raw g; do not silently assert unit variance. Cubic absolute integrability uses bounded noise and categoryOffset third moment, not categoryFeature third/fourth moment. Supporting mixed-moment/variance identities are allowed if proved from existing laws and integrability. This does not certify a rank-one operator, studentizer, rare-event chain or tails. Independent statement review before proof; server-only compilation then fresh proof/source review and whitelist axioms. No sorry/admit/new axiom/unsafe/native_decide.
