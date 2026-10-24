import Shao.OQ6.AmbientCanonicalIntegrableCDF
import Shao.OQ6.WeightedCostClipping
import Mathlib.Topology.Order.OrderClosed

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Shao.OQ6.WeightedAECDFBounds

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology

universe u v

theorem ambient_weighted_ae_cdf_bounds
    (C : ℝ)
    (hSZ : Shao.OQ6.NormalizedIntegrableCDFAssembly.ScalarShaoZhouFiniteCostCDFInput.{v} C)
    {Ω0 : Type u} [MeasurableSpace Ω0]
    (P : Measure Ω0) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n) {X : Fin n → Type v}
    [mX : ∀ i : Fin n, MeasurableSpace (X i)]
    [∀ i : Fin n, MeasurableSpace.CountablyGenerated (X i)]
    (O : ∀ i : Fin n, Ω0 → X i)
    (hO : ∀ i : Fin n, Measurable (O i))
    (hOindep : iIndepFun O P)
    (g : ∀ i : Fin n, X i → ℝ)
    (hg : ∀ i : Fin n, Measurable (g i))
    (hg2 : ∀ i : Fin n, MemLp (fun ω : Ω0 => g i (O i ω)) 2 P)
    (hgmean : ∀ i : Fin n, (∫ ω, g i (O i ω) ∂P) = 0)
    (hgenergy : (∑ i : Fin n, ∫ ω, (g i (O i ω)) ^ 2 ∂P) = 1)
    (D1 D2 Aenv Benv : (∀ i : Fin n, X i) → ℝ)
    (Adeleted Bdeleted : ∀ i : Fin n, (∀ j : {j : Fin n // j ≠ i}, X j.1) → ℝ)
    (hD1 : Measurable D1) (hD2 : Measurable D2)
    (hAenv : Measurable Aenv) (hBenv : Measurable Benv)
    (hAdeleted : ∀ i : Fin n, Measurable (Adeleted i))
    (hBdeleted : ∀ i : Fin n, Measurable (Bdeleted i))
    (hAnonneg : ∀ᵐ ω ∂P, 0 ≤ Aenv (fun i => O i ω))
    (hBnonneg : ∀ᵐ ω ∂P, 0 ≤ Benv (fun i => O i ω))
    (hAdeletenonneg : ∀ i : Fin n, ∀ᵐ ω ∂P,
      0 ≤ Adeleted i (fun j => O j.1 ω))
    (hBdeletenonneg : ∀ i : Fin n, ∀ᵐ ω ∂P,
      0 ≤ Bdeleted i (fun j => O j.1 ω))
    (hD1A : ∀ᵐ ω ∂P, |D1 (fun i => O i ω)| ≤ Aenv (fun i => O i ω))
    (hD2B : ∀ᵐ ω ∂P, |D2 (fun i => O i ω)| ≤ Benv (fun i => O i ω))
    (hD2pos : ∀ᵐ ω ∂P, 0 < 1 + D2 (fun i => O i ω))
    (κ : Ω0 → ℝ) (hκ : Measurable κ)
    (z : ℝ) (hz : 0 ≤ z)
    (hFull : Integrable (fun ω : Ω0 =>
      Aenv (fun i => O i ω) + z * Benv (fun i => O i ω)) P)
    (hDeleted : ∀ i : Fin n, Integrable (fun ω : Ω0 =>
      min |g i (O i ω)| (1 + z)⁻¹ *
        (|Aenv (fun j => O j ω) - Adeleted i (fun j => O j.1 ω)| +
          z * |Benv (fun j => O j ω) - Bdeleted i (fun j => O j.1 ω)|)) P) :
    let Q : Ω0 → (∀ i : Fin n, X i) := fun ω i => O i ω
    let ξ0 : Fin n → Ω0 → ℝ := fun i ω => g i (O i ω)
    let W0 : Ω0 → ℝ := fun ω => ∑ i : Fin n, ξ0 i ω
    let V0 : Ω0 → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ0 i ω) ^ 2)
    let b0 : Ω0 → ℝ := fun ω => Real.sqrt (1 + D2 (Q ω))
    let T0 : Ω0 → ℝ := fun ω => if V0 ω = 0 then κ ω else (W0 ω + D1 (Q ω)) / (V0 ω * b0 ω)
    let F0 : Set Ω0 := {ω : Ω0 | W0 ω + D1 (Q ω) ≤ z * V0 ω * b0 ω}
    let Z0 : Set Ω0 := {ω : Ω0 | V0 ω = 0}
    let p0 : ℝ := P.real Z0
    let δ0 : Fin n → ℝ := fun i =>
      ∫ ω, ((1 + z) * ξ0 i ω) ^ 2 * min |(1 + z) * ξ0 i ω| 1 ∂P
    let L0 : ℝ := ∑ i : Fin n, δ0 i
    let compactDeleted0 : Fin n → Ω0 → ℝ := fun i ω =>
      min |ξ0 i ω| (1 + z)⁻¹ *
        (|Aenv (Q ω) - Adeleted i (fun j => O j.1 ω)| +
          z * |Benv (Q ω) - Bdeleted i (fun j => O j.1 ω)|)
    let compactCost0 : ℝ := L0 + (∫ ω, Aenv (Q ω) + z * Benv (Q ω) ∂P) +
      ∑ i : Fin n, ∫ ω, compactDeleted0 i ω ∂P
    |P.real F0 - Shao.OQ4.standardNormalCDF z| ≤ C * compactCost0 ∧
    |P.real {ω : Ω0 | T0 ω ≤ z} - Shao.OQ4.standardNormalCDF z| ≤ C * compactCost0 + p0 := by
  classical
  let Q : Ω0 → (∀ i : Fin n, X i) := fun ω i => O i ω
  let ξ0 : Fin n → Ω0 → ℝ := fun i ω => g i (O i ω)
  let W0 : Ω0 → ℝ := fun ω => ∑ i : Fin n, ξ0 i ω
  let V0 : Ω0 → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ0 i ω) ^ 2)
  let b0 : Ω0 → ℝ := fun ω => Real.sqrt (1 + D2 (Q ω))
  let T0 : Ω0 → ℝ := fun ω => if V0 ω = 0 then κ ω else (W0 ω + D1 (Q ω)) / (V0 ω * b0 ω)
  let F0 : Set Ω0 := {ω : Ω0 | W0 ω + D1 (Q ω) ≤ z * V0 ω * b0 ω}
  let Z0 : Set Ω0 := {ω : Ω0 | V0 ω = 0}
  let p0 : ℝ := P.real Z0
  let δ0 : Fin n → ℝ := fun i =>
    ∫ ω, ((1 + z) * ξ0 i ω) ^ 2 * min |(1 + z) * ξ0 i ω| 1 ∂P
  let L0 : ℝ := ∑ i : Fin n, δ0 i
  let compactDeleted0 : Fin n → Ω0 → ℝ := fun i ω =>
    min |ξ0 i ω| (1 + z)⁻¹ *
      (|Aenv (Q ω) - Adeleted i (fun j => O j.1 ω)| +
        z * |Benv (Q ω) - Bdeleted i (fun j => O j.1 ω)|)
  let compactCost0 : ℝ := L0 + (∫ ω, Aenv (Q ω) + z * Benv (Q ω) ∂P) +
    ∑ i : Fin n, ∫ ω, compactDeleted0 i ω ∂P
  change |P.real F0 - Shao.OQ4.standardNormalCDF z| ≤ C * compactCost0 ∧
    |P.real {ω : Ω0 | T0 ω ≤ z} - Shao.OQ4.standardNormalCDF z| ≤ C * compactCost0 + p0
  have hQ : Measurable Q := Measurable.of_eval hO
  have hξ (i : Fin n) : Measurable (ξ0 i) := (hg i).comp (hO i)
  let μ : Measure (∀ i : Fin n, X i) := P.map Q
  letI : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (P.map Q)
    infer_instance
  let Aplus : (∀ i : Fin n, X i) → ℝ := fun o => max 0 (Aenv o)
  let Bplus : (∀ i : Fin n, X i) → ℝ := fun o => max 0 (Benv o)
  let AplusDelete : ∀ i : Fin n, (∀ j : {j : Fin n // j ≠ i}, X j.1) → ℝ :=
    fun i t => max 0 (Adeleted i t)
  let BplusDelete : ∀ i : Fin n, (∀ j : {j : Fin n // j ≠ i}, X j.1) → ℝ :=
    fun i t => max 0 (Bdeleted i t)
  let Ad : Fin n → (∀ i : Fin n, X i) → ℝ :=
    fun i o => AplusDelete i (fun j => o j.1)
  let Bd : Fin n → (∀ i : Fin n, X i) → ℝ :=
    fun i o => BplusDelete i (fun j => o j.1)
  have hAplus : Measurable Aplus :=
    (measurable_const : Measurable (fun _ : (∀ i : Fin n, X i) => (0 : ℝ))).max hAenv
  have hBplus : Measurable Bplus :=
    (measurable_const : Measurable (fun _ : (∀ i : Fin n, X i) => (0 : ℝ))).max hBenv
  have hAplusDelete (i : Fin n) : Measurable (AplusDelete i) :=
    (measurable_const : Measurable
      (fun _ : (∀ j : {j : Fin n // j ≠ i}, X j.1) => (0 : ℝ))).max (hAdeleted i)
  have hBplusDelete (i : Fin n) : Measurable (BplusDelete i) :=
    (measurable_const : Measurable
      (fun _ : (∀ j : {j : Fin n // j ≠ i}, X j.1) => (0 : ℝ))).max (hBdeleted i)
  have hAd (i : Fin n) : Measurable (Ad i) :=
    (hAplusDelete i).comp (Measurable.of_eval (fun j => measurable_pi_apply j.1))
  have hBd (i : Fin n) : Measurable (Bd i) :=
    (hBplusDelete i).comp (Measurable.of_eval (fun j => measurable_pi_apply j.1))
  have hAeq : (fun ω : Ω0 => Aplus (Q ω)) =ᵐ[P] (fun ω => Aenv (Q ω)) := by
    filter_upwards [hAnonneg] with ω hω
    exact max_eq_right hω
  have hBeq : (fun ω : Ω0 => Bplus (Q ω)) =ᵐ[P] (fun ω => Benv (Q ω)) := by
    filter_upwards [hBnonneg] with ω hω
    exact max_eq_right hω
  have hAdeq (i : Fin n) :
      (fun ω : Ω0 => Ad i (Q ω)) =ᵐ[P]
        (fun ω => Adeleted i (fun j => O j.1 ω)) := by
    filter_upwards [hAdeletenonneg i] with ω hω
    exact max_eq_right hω
  have hBdeq (i : Fin n) :
      (fun ω : Ω0 => Bd i (Q ω)) =ᵐ[P]
        (fun ω => Bdeleted i (fun j => O j.1 ω)) := by
    filter_upwards [hBdeletenonneg i] with ω hω
    exact max_eq_right hω
  let Ap : Ω0 → ℝ := fun ω => Aplus (Q ω)
  let Bp : Ω0 → ℝ := fun ω => Bplus (Q ω)
  let Adp : Fin n → Ω0 → ℝ := fun i ω => Ad i (Q ω)
  let Bdp : Fin n → Ω0 → ℝ := fun i ω => Bd i (Q ω)
  have hAp : Measurable Ap := hAplus.comp hQ
  have hBp : Measurable Bp := hBplus.comp hQ
  have hAdp (i : Fin n) : Measurable (Adp i) := (hAd i).comp hQ
  have hBdp (i : Fin n) : Measurable (Bdp i) := (hBd i).comp hQ
  have hFullEq : (fun ω : Ω0 => Ap ω + z * Bp ω) =ᵐ[P]
      (fun ω => Aenv (Q ω) + z * Benv (Q ω)) := by
    filter_upwards [hAeq, hBeq] with ω hA hB
    change Aplus (Q ω) + z * Bplus (Q ω) = Aenv (Q ω) + z * Benv (Q ω)
    rw [hA, hB]
  have hDeletedEq (i : Fin n) :
      (fun ω : Ω0 => min |ξ0 i ω| (1 + z)⁻¹ *
        (|Ap ω - Adp i ω| + z * |Bp ω - Bdp i ω|)) =ᵐ[P] compactDeleted0 i := by
    filter_upwards [hAeq, hBeq, hAdeq i, hBdeq i] with ω hA hB hAi hBi
    change min |ξ0 i ω| (1 + z)⁻¹ *
        (|Aplus (Q ω) - Ad i (Q ω)| + z * |Bplus (Q ω) - Bd i (Q ω)|) = _
    rw [hA, hB, hAi, hBi]
  have hFullPlus : Integrable (fun ω : Ω0 => Ap ω + z * Bp ω) P :=
    hFull.congr hFullEq.symm
  have hDeletedPlus (i : Fin n) : Integrable (fun ω : Ω0 =>
      min |ξ0 i ω| (1 + z)⁻¹ *
        (|Ap ω - Adp i ω| + z * |Bp ω - Bdp i ω|)) P :=
    (hDeleted i).congr (hDeletedEq i).symm
  have hDomA0 : ∀ᵐ ω ∂P, |D1 (Q ω)| ≤ Aplus (Q ω) := by
    filter_upwards [hD1A] with ω hω
    exact hω.trans (le_max_right 0 (Aenv (Q ω)))
  have hDomB0 : ∀ᵐ ω ∂P, |D2 (Q ω)| ≤ Bplus (Q ω) := by
    filter_upwards [hD2B] with ω hω
    exact hω.trans (le_max_right 0 (Benv (Q ω)))
  have hDomAMeas : MeasurableSet {o : (∀ i : Fin n, X i) | |D1 o| ≤ Aplus o} :=
    measurableSet_le (continuous_abs.measurable.comp hD1) hAplus
  have hDomBMeas : MeasurableSet {o : (∀ i : Fin n, X i) | |D2 o| ≤ Bplus o} :=
    measurableSet_le (continuous_abs.measurable.comp hD2) hBplus
  have hPosMeas : MeasurableSet {o : (∀ i : Fin n, X i) | 0 < 1 + D2 o} :=
    measurableSet_lt
      (measurable_const : Measurable (fun _ : (∀ i : Fin n, X i) => (0 : ℝ)))
      ((measurable_const : Measurable (fun _ : (∀ i : Fin n, X i) => (1 : ℝ))).add hD2)
  have hDomA : ∀ᵐ o ∂μ, |D1 o| ≤ Aplus o :=
    (ae_map_iff hQ.aemeasurable hDomAMeas).2 hDomA0
  have hDomB : ∀ᵐ o ∂μ, |D2 o| ≤ Bplus o :=
    (ae_map_iff hQ.aemeasurable hDomBMeas).2 hDomB0
  have hPos : ∀ᵐ o ∂μ, 0 < 1 + D2 o :=
    (ae_map_iff hQ.aemeasurable hPosMeas).2 hD2pos
  let G : Set (∀ i : Fin n, X i) :=
    {o | 0 < 1 + D2 o ∧ |D1 o| ≤ Aplus o ∧ |D2 o| ≤ Bplus o}
  let D1rawM : ℕ → (∀ i : Fin n, X i) → ℝ :=
    fun M o => max (-(M : ℝ)) (min (D1 o) (M : ℝ))
  let D2rawM : ℕ → (∀ i : Fin n, X i) → ℝ :=
    fun M o => min (D2 o) (M : ℝ)
  let AM : ℕ → (∀ i : Fin n, X i) → ℝ := fun M o => min (Aplus o) (M : ℝ)
  let BM : ℕ → (∀ i : Fin n, X i) → ℝ := fun M o => min (Bplus o) (M : ℝ)
  let AdM : ℕ → ∀ i : Fin n, (∀ j : {j : Fin n // j ≠ i}, X j.1) → ℝ :=
    fun M i t => min (AplusDelete i t) (M : ℝ)
  let BdM : ℕ → ∀ i : Fin n, (∀ j : {j : Fin n // j ≠ i}, X j.1) → ℝ :=
    fun M i t => min (BplusDelete i t) (M : ℝ)
  let D1goodM : ℕ → (∀ i : Fin n, X i) → ℝ :=
    fun M o => if o ∈ G then D1rawM M o else 0
  let D2goodM : ℕ → (∀ i : Fin n, X i) → ℝ :=
    fun M o => if o ∈ G then D2rawM M o else 0
  have hclip := Shao.OQ6.WeightedCostClipping.natural_clipping_envelope_contract
    μ n D1 D2 Aplus Bplus Ad Bd hD1 hD2 hAplus hBplus hAd hBd
    (fun o => le_max_left 0 (Aenv o)) (fun o => le_max_left 0 (Benv o))
    (fun i o => le_max_left 0 (Adeleted i (fun j => o j.1)))
    (fun i o => le_max_left 0 (Bdeleted i (fun j => o j.1))) hDomA hDomB hPos
  rcases hclip with
    ⟨_hGmeas, _hGmass, hMMeas, _hDeletedMMeas, hMbound, _hDeletedMbound,
      _hClipDiff, hMInt, _hDInt, _hRawValid, hGoodValid, _hGoodAE, _hEventually⟩
  have hQG : ∀ᵐ ω ∂P, Q ω ∈ G := by
    filter_upwards [hD2pos, hDomA0, hDomB0] with ω hp ha hb
    exact ⟨hp, ha, hb⟩
  have hGoodRaw (M : ℕ) : ∀ᵐ ω ∂P,
      D1goodM M (Q ω) = D1rawM M (Q ω) ∧ D2goodM M (Q ω) = D2rawM M (Q ω) := by
    filter_upwards [hQG] with ω hω
    exact ⟨if_pos hω, if_pos hω⟩
  have hAMmeas (M : ℕ) : Measurable (AM M) := (hMMeas M).2.2.1
  have hBMmeas (M : ℕ) : Measurable (BM M) := (hMMeas M).2.2.2.1
  have hD1goodMeas (M : ℕ) : Measurable (D1goodM M) := (hMMeas M).2.2.2.2.1
  have hD2goodMeas (M : ℕ) : Measurable (D2goodM M) := (hMMeas M).2.2.2.2.2
  have hAdMmeas (M : ℕ) (i : Fin n) : Measurable (AdM M i) :=
    (hAplusDelete i).min (measurable_const : Measurable
      (fun _ : (∀ j : {j : Fin n // j ≠ i}, X j.1) => (M : ℝ)))
  have hBdMmeas (M : ℕ) (i : Fin n) : Measurable (BdM M i) :=
    (hBplusDelete i).min (measurable_const : Measurable
      (fun _ : (∀ j : {j : Fin n // j ≠ i}, X j.1) => (M : ℝ)))
  have hAMint (M : ℕ) : Integrable (fun ω : Ω0 => AM M (Q ω)) P :=
    (hMInt M).1.comp_measurable hQ
  have hBMint (M : ℕ) : Integrable (fun ω : Ω0 => BM M (Q ω)) P :=
    (hMInt M).2.1.comp_measurable hQ
  have hAdMint (M : ℕ) (i : Fin n) :
      Integrable (fun ω : Ω0 => AdM M i (fun j => O j.1 ω)) P :=
    ((hMInt M).2.2 i).1.comp_measurable hQ
  have hBdMint (M : ℕ) (i : Fin n) :
      Integrable (fun ω : Ω0 => BdM M i (fun j => O j.1 ω)) P :=
    ((hMInt M).2.2 i).2.comp_measurable hQ
  let compactDeletedM : ℕ → Fin n → Ω0 → ℝ := fun M i ω =>
    min |ξ0 i ω| (1 + z)⁻¹ *
      (|AM M (Q ω) - AdM M i (fun j => O j.1 ω)| +
        z * |BM M (Q ω) - BdM M i (fun j => O j.1 ω)|)
  let costM : ℕ → ℝ := fun M => L0 + (∫ ω, AM M (Q ω) + z * BM M (Q ω) ∂P) +
    ∑ i : Fin n, ∫ ω, compactDeletedM M i ω ∂P
  let FgoodM : ℕ → Set Ω0 := fun M => {ω : Ω0 |
    W0 ω + D1goodM M (Q ω) ≤ z * V0 ω * Real.sqrt (1 + D2goodM M (Q ω))}
  let TgoodM : ℕ → Ω0 → ℝ := fun M ω => if V0 ω = 0 then κ ω else
    (W0 ω + D1goodM M (Q ω)) / (V0 ω * Real.sqrt (1 + D2goodM M (Q ω)))
  have hFixed (M : ℕ) (hM : 1 ≤ M) :
      |P.real (FgoodM M) - Shao.OQ4.standardNormalCDF z| ≤ C * costM M ∧
      |P.real {ω : Ω0 | TgoodM M ω ≤ z} - Shao.OQ4.standardNormalCDF z| ≤ C * costM M + p0 := by
    have hb := Shao.OQ6.AmbientCanonicalIntegrableCDF.ambient_canonical_integrable_cdf_bounds
      C hSZ P n hn O hO hOindep g hg hg2 hgmean hgenergy
      (D1goodM M) (D2goodM M) (AM M) (BM M) (AdM M) (BdM M)
      (hD1goodMeas M) (hD2goodMeas M) (hAMmeas M) (hBMmeas M)
      (hAdMmeas M) (hBdMmeas M)
      (fun o => (hMbound M o).1) (fun o => (hMbound M o).2.2.2.1)
      (fun i t => le_min (le_max_left 0 (Adeleted i t)) (Nat.cast_nonneg M))
      (fun i t => le_min (le_max_left 0 (Bdeleted i t)) (Nat.cast_nonneg M))
      (fun o => (hGoodValid M hM o).2.1) (fun o => (hGoodValid M hM o).2.2)
      (Filter.Eventually.of_forall (fun ω => (hGoodValid M hM (Q ω)).1))
      (hAMint M) (hBMint M) (hAdMint M) (hBdMint M) κ hκ z hz
    exact hb
  let positiveCost : ℝ := L0 + (∫ ω, Ap ω + z * Bp ω ∂P) +
    ∑ i : Fin n, ∫ ω, min |ξ0 i ω| (1 + z)⁻¹ *
      (|Ap ω - Adp i ω| + z * |Bp ω - Bdp i ω|) ∂P
  have hCosts := Shao.OQ6.WeightedCostClipping.actual_continuous_compact_cost_clipping_limits
    P n ξ0 hξ hg2 Ap Bp Adp Bdp hAp hBp hAdp hBdp
    (fun ω => le_max_left 0 (Aenv (Q ω))) (fun ω => le_max_left 0 (Benv (Q ω)))
    (fun i ω => le_max_left 0 (Adeleted i (fun j => O j.1 ω)))
    (fun i ω => le_max_left 0 (Bdeleted i (fun j => O j.1 ω))) z hz hFullPlus hDeletedPlus
  rcases hCosts with ⟨_hAint, _hBint, _hDeltaInt, _hFullMspec, _hDeletedMspec,
    _hEventuallyCost, _hL1Full, _hL1Deleted, _hFullIntLim, _hDeletedIntLim,
    _hCostSplit, _hCostMSplit, _hZeroCost, _hCostBound, hCostLim⟩
  have hPositiveCost : positiveCost = compactCost0 := by
    dsimp only [positiveCost, compactCost0]
    rw [integral_congr_ae hFullEq]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => integral_congr_ae (hDeletedEq i))
  change Filter.Tendsto costM Filter.atTop (nhds positiveCost) at hCostLim
  have hCostLim0 : Filter.Tendsto costM Filter.atTop (nhds compactCost0) := by
    rw [← hPositiveCost]
    exact hCostLim
  let FrawM : ℕ → Set Ω0 := fun M => {ω : Ω0 |
    W0 ω + D1rawM M (Q ω) ≤ z * V0 ω * Real.sqrt (1 + D2rawM M (Q ω))}
  let TrawM : ℕ → Ω0 → ℝ := fun M ω => if V0 ω = 0 then κ ω else
    (W0 ω + D1rawM M (Q ω)) / (V0 ω * Real.sqrt (1 + D2rawM M (Q ω)))
  have hEvents := Shao.OQ6.WeightedCostClipping.actual_clipped_event_probabilities
    P n ξ0 hξ (fun ω : Ω0 => D1 (Q ω)) (fun ω : Ω0 => D2 (Q ω)) κ
    (hD1.comp hQ) (hD2.comp hQ) hκ hD2pos z hz
  rcases hEvents with ⟨_hWmeas, _hVmeas, _hTmeas, _hTMmeas, _hZmeas,
    _hZfixed, _hEventuallyEvents, _hCompare, hEventLimits, _hNumLimit, _hDenLimit⟩
  rcases hEventLimits (fun a b : ℝ => a ≤ b) (Or.inl rfl) with ⟨hFEvent, hTEvent⟩
  rcases hFEvent with ⟨_hFmeas, _hFMmeas, _hFEventually, _hFIndicator,
    _hFIndicatorLim, _hFSymmLim, hFrawLim⟩
  rcases hTEvent with ⟨_hQmeas, _hQMmeas, _hQEventually, _hQIndicator,
    _hQIndicatorLim, _hQSymmLim, hTrawLim⟩
  change Filter.Tendsto (fun M : ℕ => P.real (FrawM M)) Filter.atTop
    (nhds (P.real F0)) at hFrawLim
  change Filter.Tendsto (fun M : ℕ => P.real {ω : Ω0 | TrawM M ω ≤ z}) Filter.atTop
    (nhds (P.real {ω : Ω0 | T0 ω ≤ z})) at hTrawLim
  have hFprobEq (M : ℕ) : P.real (FgoodM M) = P.real (FrawM M) := by
    have hm : P (FgoodM M) = P (FrawM M) := by
      apply measure_congr
      filter_upwards [hGoodRaw M] with ω hω
      simp only [FgoodM, FrawM, Set.mem_setOf_eq, hω.1, hω.2]
    exact congrArg ENNReal.toReal hm
  have hTprobEq (M : ℕ) :
      P.real {ω : Ω0 | TgoodM M ω ≤ z} = P.real {ω : Ω0 | TrawM M ω ≤ z} := by
    have hm : P {ω : Ω0 | TgoodM M ω ≤ z} = P {ω : Ω0 | TrawM M ω ≤ z} := by
      apply measure_congr
      filter_upwards [hGoodRaw M] with ω hω
      simp only [TgoodM, TrawM, Set.mem_setOf_eq, hω.1, hω.2]
    exact congrArg ENNReal.toReal hm
  have hFgoodLim : Filter.Tendsto (fun M : ℕ => P.real (FgoodM M)) Filter.atTop
      (nhds (P.real F0)) := by
    have hf : (fun M : ℕ => P.real (FgoodM M)) = (fun M : ℕ => P.real (FrawM M)) :=
      funext hFprobEq
    rw [hf]
    exact hFrawLim
  have hTgoodLim : Filter.Tendsto (fun M : ℕ => P.real {ω : Ω0 | TgoodM M ω ≤ z})
      Filter.atTop (nhds (P.real {ω : Ω0 | T0 ω ≤ z})) := by
    have hf : (fun M : ℕ => P.real {ω : Ω0 | TgoodM M ω ≤ z}) =
        (fun M : ℕ => P.real {ω : Ω0 | TrawM M ω ≤ z}) := funext hTprobEq
    rw [hf]
    exact hTrawLim
  have hFabsLim : Filter.Tendsto
      (fun M : ℕ => |P.real (FgoodM M) - Shao.OQ4.standardNormalCDF z|)
      Filter.atTop (nhds |P.real F0 - Shao.OQ4.standardNormalCDF z|) :=
    (continuous_abs : Continuous (fun t : ℝ => |t|)).continuousAt.tendsto.comp
      (hFgoodLim.sub tendsto_const_nhds)
  have hTabsLim : Filter.Tendsto
      (fun M : ℕ => |P.real {ω : Ω0 | TgoodM M ω ≤ z} - Shao.OQ4.standardNormalCDF z|)
      Filter.atTop (nhds |P.real {ω : Ω0 | T0 ω ≤ z} - Shao.OQ4.standardNormalCDF z|) :=
    (continuous_abs : Continuous (fun t : ℝ => |t|)).continuousAt.tendsto.comp
      (hTgoodLim.sub tendsto_const_nhds)
  have hRHSLim : Filter.Tendsto (fun M : ℕ => C * costM M) Filter.atTop
      (nhds (C * compactCost0)) := tendsto_const_nhds.mul hCostLim0
  have hTRHSLim : Filter.Tendsto (fun M : ℕ => C * costM M + p0) Filter.atTop
      (nhds (C * compactCost0 + p0)) := hRHSLim.add tendsto_const_nhds
  have hMlarge : ∀ᶠ M : ℕ in Filter.atTop, 1 ≤ M := Filter.eventually_ge_atTop 1
  constructor
  · apply le_of_tendsto_of_tendsto hFabsLim hRHSLim
    filter_upwards [hMlarge] with M hM
    exact (hFixed M hM).1
  · apply le_of_tendsto_of_tendsto hTabsLim hTRHSLim
    filter_upwards [hMlarge] with M hM
    exact (hFixed M hM).2

end

end Shao.OQ6.WeightedAECDFBounds
