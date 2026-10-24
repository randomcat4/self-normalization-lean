# Positive-boundary proposal: consumed interfaces and primary evidence

Author180, gpt-6.1-sol/xhigh, mathematical proposal only. No source implementation, local/remote Lean, parser, Git, installation, cache mutation, raw download or heavy computation. Online primary sources were read through the browsing tool; none was saved as a raw downloaded file. These API readings are not mechanical verification of either new proposed module.

## Fixed source and accepted basis

Project pins read from SERVER.md and current compact resume: Lean `leanprover/lean4:v4.36.0-rc1`; Mathlib `807d3836b165983210ee2ecf3cd28f239436949c`. Root v61 receipt is `library/verification/receipt-v61.json`, SHA256 `915bdc06612c6d5a54c234e7f7ea75662e717d59fc3bd362ba55d0d41b801cc3`. It records accepted original source/kernel/all-owned-axiom evidence, which this proposal reuses. This is not a claim that a new consumer has been checked.

Complete parent mathematical intake was read. Original fixed-law assumptions read in `C:/game/shao/current/oq4/frozen01.md`; E6 and the preceding exact random-event convention read in `denom01.md`, including lines114–131. Optional downstream `small-boundary-window-transfer-next-math-notes-v1.md` was read for interface fit. Its entire-window, σ and arbitrary iid-space obligations remain outside this unit.

The original source README contains historical mathematical completion descriptions. Current AGENTS.md and the present root receipt/scope policy govern formal acceptance; no historical label is used to close any currently OPEN root group.

## Qualified project interfaces: direct actual heads and values read

Local hashes below were compared against v61 `source_files_sha256` and matched exactly. Only actually consumed interfaces were inspected; no accepted old proof was re-reviewed or rerun.

| Actual source | SHA256 | Consumed contract |
|---|---|---|
| Shao/Probability/BrownianSup.lean | f7f86bd8db582d9a4e53241f9cfc8384f86ee33765a40c5541a15b6f0c22a718 | Actual pathSup/fullStrip/traceSup/U/probability values; measurable_U; U_ae_eq_pathSup; probability_eq_fullStrip; probability_eq_probability |
| Shao/Probability/BrownianFirstTerm.lean | f4faa8c89016aea74dd16c8ea0dc359213390413d3ab0faff234dd98d0a87c6a | actual_brownian_eventually_positive at arbitrary given B/P, initially for sufficiently small positive radius only |
| Shao/Probability/FiniteIID.lean | d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b | samplePath complete value; iid_samplePath_map_eq_pi, with measurable finite coordinates, actual independence and actual IdentDistrib-to-ν; n=0 included |
| Shao/OQ4/BrownianSurvivalBoundary.lean | 5ad4214f363192f6a196d2f1f7cf19302171cd5b93785d5206e37c19ad934e12 | closedSurvival and pathSup complete values; measure_pathSup_eq_one_eq_zero at unit level, T>0 and start u∈[-1,1] |
| Shao/OQ4/PolygonalKilledFunctionalLimit.lean | 0102ad1ce0963c8955000b2e46d90c830258fec3bc40001af0403da20ec08942 | floorHorizon/discreteClosedSurvival complete values; actual discrete_survival_tendsto_brownian full head, not an arbitrary-radius limit |

The BrownianSup probability value is P.real{U≤x}; U is a measurable modification of its countable trace supremum. Its raw pathSup value is the real sSup of the absolute-value image of [0,1]. The fullStrip value monitors all times in that closed interval. `probability_eq_probability` compares two genuine actual Brownian realizations at the same radius and allows different probability spaces. It does not itself rescale radii or horizons.

The boundary theorem's atom is exactly pathSup(B,T,u)=1. No arbitrary positive-radius null statement is already in that consumed head. Proposal A pays this gap using scaling and a compact-maximum transport.

The paid row head requires: an actual B/P/hB, T>0; natural row lengths; all-index h_j>0; T*h_j²≤n_j; probability laws; integrable absolute cubes; mean0 and second1; one real common bound M for all third moments; h_j→∞; b_j:ℝ≥0 tending to1; and u_j→u∈[-1,1]. Its result uses the exact floorHorizon, the actual row product measures and actual unit closedSurvival of B at T. These are all paid explicitly in proof.md Section6. Only early lengths and NNReal boundary coercions are patched; neither is made an extra final premise.

Other already accepted project values used directly are `Shao.Path`, `prefixSum`, `energy`, `closedStrip`, `energy_nonneg`, `energy_eq_zero_iff`, `prefixSum_eq_zero_of_energy_eq_zero`, `measurable_prefixSum`, `measurable_energy` and measurable sqrt energy. Their full consumed values/heads were read from Basic/FinitePath, Basic/ClosedSurvival and Probability/MeasurablePath. Their hashes are recorded and compared to the v61 source map in checkpoint.json.

## Exact qualified FAR value, pending root merge

The parent-qualified source is `drafts/oq4/random-denominator-far-tail-author-v1/RandomDenominatorFarTail.lean`, SHA256 `2388a74ec1537453148f31736be689907f758d0961052e1c5df23bf4eb667cc5`. It was read directly and its exact hash matches the parent's qualification. The consumed public value is

    randomDenominatorEvent n h =
      {a | a ∈ Shao.closedStrip (h / Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy a))}.

This proposal accesses no private FAR declaration. Parent-recorded independent full review173 and acceptance SHA `1a99d019368aa24076ce197b30391dba87806b37e2447a22f323f1182098888b` are reused. Original server object SHA is `e3280a89ed2acfc132cd23723735c41d84568ae91f27be935b05adc5a8267030`; source-bound receipt SHA is `d6c3306c39f9de56518b56687640407396c4a0b039da55572da33bde031956ad`. Current parent publication is PR226; root merge remains pending according to the intake. Actual runtime binding of this original object at a future new consumer check is the parent's later gate; this author did not access the server or rehash the remote object.

## Pinned primary Mathlib evidence

All links below name the exact pinned commit, not moving master documentation. Quotes are limited to the short decisive heads; mathematical application and unpaid obligations are stated separately.

1. [StrongLaw.lean lines567–571](https://raw.githubusercontent.com/leanprover-community/mathlib4/807d3836b165983210ee2ecf3cd28f239436949c/Mathlib/Probability/StrongLaw.lean):

       theorem strong_law_ae_real
         (X : ℕ → Ω → ℝ) (hint : Integrable (X 0) μ)
         (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
         (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
         ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (∑ i ∈ range n, X i ω) / n)
           atTop (𝓝 μ[X 0])

   Application: X_i(ω)=ω_i² on the actual infinite product. Only integrability of X_0, not its variance, is required. The true expectation is paid by the evaluation law and the given second moment1.

2. [InfinitePi independence lines112–115](https://raw.githubusercontent.com/leanprover-community/mathlib4/807d3836b165983210ee2ecf3cd28f239436949c/Mathlib/Probability/Independence/InfinitePi.lean): `iIndepFun_infinitePi` accepts a measurable function on each component probability space and returns independence of `fun i ω => X i (ω i)` under `infinitePi P`. Reading included the entire head. Apply once with component square for strong-law pairwise independence, and with id plus injective Fin.val precomposition for the finite projection law.

3. [ProductMeasure.lean lines430–442](https://raw.githubusercontent.com/leanprover-community/mathlib4/807d3836b165983210ee2ecf3cd28f239436949c/Mathlib/Probability/ProductMeasure.lean): `measurePreserving_eval_infinitePi μ i` is MeasurePreserving(Function.eval i)(infinitePi μ)(μ i); `infinitePi_map_eval μ i` gives the exact mapped measure μ i. These pay both square integrability/expectation transport and the actual identical laws used by FiniteIID. The finite map to π_n is still a new proof obligation, not supplied by this scalar evaluation theorem.

4. [ConvergenceInMeasure.lean lines112–118 and194–197](https://raw.githubusercontent.com/leanprover-community/mathlib4/807d3836b165983210ee2ecf3cd28f239436949c/Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean):

       tendstoInMeasure_of_tendsto_ae [IsFiniteMeasure μ]
         (hf : ∀ n, AEStronglyMeasurable (f n) μ)
         (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))

   Its result is TendstoInMeasure μ f atTop g. `tendstoInMeasure_iff_measureReal_norm` states the equivalent real-measure convergence to0 of `{x | ε≤‖f i x−g x‖}` for every ε>0 when μ is finite. The average is measurable and μ∞ is a probability measure. The strict bad event is contained in this weak threshold event, after positive-n normalization and exact finite pushforward.

5. [BrownianMotion/Basic.lean lines284–290](https://raw.githubusercontent.com/leanprover-community/mathlib4/807d3836b165983210ee2ecf3cd28f239436949c/Mathlib/Probability/BrownianMotion/Basic.lean):

       lemma IsBrownianReal.smul (hB : IsBrownianReal B P) {c : ℝ≥0} (hc : c ≠ 0) :
         IsBrownianReal (fun t ω => (√c)⁻¹ * B (c * t) ω) P

   This is the exact actual scaling used by A. For the level-null proof c=ofReal(x²); for the horizon identity c=T. Both c≠0 conditions are proved from positivity, and sqrt(x²)=x uses x>0.

6. [DominatedConvergence.lean lines111–118](https://raw.githubusercontent.com/leanprover-community/mathlib4/807d3836b165983210ee2ecf3cd28f239436949c/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean): `tendsto_integral_filter_of_norm_le_const` works for a countably generated filter and finite measure, with eventual AEStronglyMeasurable functions, one eventual almost-sure constant norm bound, and almost-sure pointwise convergence. Apply with real filter nhds x, functions `1_{Z≤y}`, bound1 and the off-null-atom local constancy proof. This directly proves ContinuousAt, so no sequential continuity API or distribution-CDF continuity black box is needed.

Standard finite-sum, sqrt, ofReal-continuity and ordered-field identities remain formal elaboration work, not an unchecked substitute for a mathematical limit. No exact library lemma name beyond the primary/public heads read here is asserted as already tested. The entire mathematical proof for those elementary transports is supplied in proof.md; no target limit appears among the proposed hypotheses.

## Declaration and evidence status

`declarations.lean.txt` proposes exactly36 module declarations:31 theorem heads and5 full transparent def values. A has12 declarations (1 private def,5 private theorems,6 public theorems); B has24 (3 private defs,1 public def,14 private theorems,6 public theorems). All27 import lines and both `autoImplicit false` options are listed in their actual future module sections. The first module supplies a new actual Brownian CDF interface; the second proves actual finite law and studentized limits. No implementation exists and no independent acceptance is claimed.

Actual model/effort: prescribed gpt-6.1-sol/xhigh. Token counters (input, cached input, output, reasoning subset) are not exposed by these tools; no fabricated usage or subscription percentage is reported.
