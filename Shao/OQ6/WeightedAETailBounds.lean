import Shao.OQ6.CanonicalIntegrableTailBounds
import Shao.OQ6.WeightedCostClipping
import Shao.OQ6.AmbientCanonicalCodingTransport
import Mathlib.Topology.Order.OrderClosed

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Shao.OQ6.WeightedAETailBounds

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology

universe u v

theorem ambient_weighted_ae_tail_bounds
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
    (cSZ C1 C2 C3 C4 : ℝ)
    (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{v}
      cSZ C1 C2 C3 C4)
    (x : ℝ) (hx : 1 ≤ x)
    (hFull : Integrable (fun ω : Ω0 =>
      (x * Aenv (fun i => O i ω) + x ^ 2 * Benv (fun i => O i ω)) *
      Real.exp (∑ i : Fin n,
        (x * g i (O i ω) - (x * g i (O i ω)) ^ 2 / 2))) P)
    (hDeleted : ∀ i : Fin n, Integrable (fun ω : Ω0 =>
      (min |x * g i (O i ω)| 1 *
        (|Aenv (fun j => O j ω) - Adeleted i (fun j => O j.1 ω)| +
          x * |Benv (fun j => O j ω) - Bdeleted i (fun j => O j.1 ω)|)) *
      Real.exp (∑ j ∈ Finset.univ.erase i,
        (x * g j (O j ω) - (x * g j (O j ω)) ^ 2 / 2))) P)
    (hδ : ∀ i : Fin n,
      (∫ ω, (x * g i (O i ω)) ^ 2 * min |x * g i (O i ω)| 1 ∂P) ≤ (1 / 2 : ℝ))
    (hL : (∑ i : Fin n, ∫ ω, (x * g i (O i ω)) ^ 2 * min |x * g i (O i ω)| 1 ∂P) ≤
      (cSZ / 2) * x ^ 2) :
    let Q : Ω0 → (∀ i : Fin n, X i) := fun ω i => O i ω
    let ξ0 : Fin n → Ω0 → ℝ := fun i ω => g i (O i ω)
    let W0 : Ω0 → ℝ := fun ω => ∑ i : Fin n, ξ0 i ω
    let V0 : Ω0 → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ0 i ω) ^ 2)
    let b0 : Ω0 → ℝ := fun ω => Real.sqrt (1 + D2 (Q ω))
    let T0 : Ω0 → ℝ := fun ω => if V0 ω = 0 then κ ω else (W0 ω + D1 (Q ω)) / (V0 ω * b0 ω)
    let F0 : Set Ω0 := {ω : Ω0 | x * V0 ω * b0 ω ≤ W0 ω + D1 (Q ω)}
    let Z0 : Set Ω0 := {ω : Ω0 | V0 ω = 0}
    let p0 : ℝ := P.real Z0
    let δ0 : Fin n → ℝ := fun i => ∫ ω, (x * ξ0 i ω) ^ 2 * min |x * ξ0 i ω| 1 ∂P
    let L0 : ℝ := ∑ i : Fin n, δ0 i
    let S0 : Ω0 → ℝ := fun ω => ∑ i : Fin n, (x * ξ0 i ω - (x * ξ0 i ω) ^ 2 / 2)
    let S0minus : Fin n → Ω0 → ℝ := fun i ω => ∑ j ∈ Finset.univ.erase i, (x * ξ0 j ω - (x * ξ0 j ω) ^ 2 / 2)
    let I0 : ℝ := ∫ ω, Real.exp (S0 ω) ∂P
    let full0 : Ω0 → ℝ := fun ω => (x * Aenv (Q ω) + x ^ 2 * Benv (Q ω)) * Real.exp (S0 ω)
    let deleted0 : Fin n → Ω0 → ℝ := fun i ω => (min |x * ξ0 i ω| 1 * (|Aenv (Q ω) - Adeleted i (fun j => O j.1 ω)| + x * |Benv (Q ω) - Bdeleted i (fun j => O j.1 ω)|)) * Real.exp (S0minus i ω)
    let R0 : ℝ := ((∫ ω, full0 ω ∂P) + ∑ i : Fin n, ∫ ω, deleted0 i ω ∂P) / I0
    let lower0 : ℝ := Shao.standardNormalTail x * Real.exp (-C1 * L0) * (1 - C2 * R0)
    let upper0 : ℝ := Shao.standardNormalTail x * Real.exp (C3 * L0) * (1 + C4 * R0)
    let numeratorBad0 : Set Ω0 := {ω : Ω0 | x * |D1 (Q ω)| > V0 ω / 8}
    let denominatorBad0 : Set Ω0 := {ω : Ω0 | x ^ 2 * |D2 (Q ω)| > (1 / 4 : ℝ)}
    lower0 ≤ P.real F0 ∧
    P.real F0 ≤ upper0 + P.real numeratorBad0 + P.real denominatorBad0 + p0 ∧
    lower0 - p0 ≤ P.real {ω : Ω0 | x ≤ T0 ω} ∧
    P.real {ω : Ω0 | x ≤ T0 ω} ≤
      upper0 + P.real numeratorBad0 + P.real denominatorBad0 + 2 * p0 := by
  classical
  dsimp only
  let Q : Ω0 → (∀ i : Fin n, X i) := fun ω i => O i ω
  let ξ0 : Fin n → Ω0 → ℝ := fun i ω => g i (O i ω)
  let W0 : Ω0 → ℝ := fun ω => ∑ i : Fin n, ξ0 i ω
  let V0 : Ω0 → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ0 i ω) ^ 2)
  let b0 : Ω0 → ℝ := fun ω => Real.sqrt (1 + D2 (Q ω))
  let T0 : Ω0 → ℝ := fun ω => if V0 ω = 0 then κ ω else (W0 ω + D1 (Q ω)) / (V0 ω * b0 ω)
  let F0 : Set Ω0 := {ω : Ω0 | x * V0 ω * b0 ω ≤ W0 ω + D1 (Q ω)}
  let Z0 : Set Ω0 := {ω : Ω0 | V0 ω = 0}
  let p0 : ℝ := P.real Z0
  let δ0 : Fin n → ℝ := fun i => ∫ ω, (x * ξ0 i ω) ^ 2 * min |x * ξ0 i ω| 1 ∂P
  let L0 : ℝ := ∑ i : Fin n, δ0 i
  let S0 : Ω0 → ℝ := fun ω => ∑ i : Fin n, (x * ξ0 i ω - (x * ξ0 i ω) ^ 2 / 2)
  let S0minus : Fin n → Ω0 → ℝ := fun i ω => ∑ j ∈ Finset.univ.erase i, (x * ξ0 j ω - (x * ξ0 j ω) ^ 2 / 2)
  let I0 : ℝ := ∫ ω, Real.exp (S0 ω) ∂P
  let full0 : Ω0 → ℝ := fun ω => (x * Aenv (Q ω) + x ^ 2 * Benv (Q ω)) * Real.exp (S0 ω)
  let deleted0 : Fin n → Ω0 → ℝ := fun i ω => (min |x * ξ0 i ω| 1 * (|Aenv (Q ω) - Adeleted i (fun j => O j.1 ω)| + x * |Benv (Q ω) - Bdeleted i (fun j => O j.1 ω)|)) * Real.exp (S0minus i ω)
  let R0 : ℝ := ((∫ ω, full0 ω ∂P) + ∑ i : Fin n, ∫ ω, deleted0 i ω ∂P) / I0
  let lower0 : ℝ := Shao.standardNormalTail x * Real.exp (-C1 * L0) * (1 - C2 * R0)
  let upper0 : ℝ := Shao.standardNormalTail x * Real.exp (C3 * L0) * (1 + C4 * R0)
  let numeratorBad0 : Set Ω0 := {ω : Ω0 | x * |D1 (Q ω)| > V0 ω / 8}
  let denominatorBad0 : Set Ω0 := {ω : Ω0 | x ^ 2 * |D2 (Q ω)| > (1 / 4 : ℝ)}
  change lower0 ≤ P.real F0 ∧
    P.real F0 ≤ upper0 + P.real numeratorBad0 + P.real denominatorBad0 + p0 ∧
    lower0 - p0 ≤ P.real {ω : Ω0 | x ≤ T0 ω} ∧
    P.real {ω : Ω0 | x ≤ T0 ω} ≤
      upper0 + P.real numeratorBad0 + P.real denominatorBad0 + 2 * p0
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hxnonneg : 0 ≤ x := le_of_lt hxpos
  have hQ : Measurable Q := measurable_pi_iff.2 hO
  have hξ : ∀ i : Fin n, Measurable (ξ0 i) := fun i => (hg i).comp (hO i)
  let μ : Measure (∀ i : Fin n, X i) := P.map Q
  letI : IsProbabilityMeasure μ := inferInstance
  have hQmp : MeasurePreserving Q P μ := ⟨hQ, rfl⟩
  let Ap : (∀ i : Fin n, X i) → ℝ := fun o => max 0 (Aenv o)
  let Bp : (∀ i : Fin n, X i) → ℝ := fun o => max 0 (Benv o)
  let Adp : ∀ i : Fin n, (∀ j : {j : Fin n // j ≠ i}, X j.1) → ℝ :=
    fun i o => max 0 (Adeleted i o)
  let Bdp : ∀ i : Fin n, (∀ j : {j : Fin n // j ≠ i}, X j.1) → ℝ :=
    fun i o => max 0 (Bdeleted i o)
  let omitTuple : ∀ i : Fin n, (∀ j : Fin n, X j) →
      (∀ j : {j : Fin n // j ≠ i}, X j.1) := fun i o j => o j.1
  have hzeroTuple : Measurable (fun _ : (∀ i : Fin n, X i) => (0 : ℝ)) :=
    measurable_const
  have honeTuple : Measurable (fun _ : (∀ i : Fin n, X i) => (1 : ℝ)) :=
    measurable_const
  have hAp : Measurable Ap := hzeroTuple.max hAenv
  have hBp : Measurable Bp := hzeroTuple.max hBenv
  have hAdp : ∀ i : Fin n, Measurable (Adp i) := by
    intro i
    have hz : Measurable (fun _ : (∀ j : {j : Fin n // j ≠ i}, X j.1) => (0 : ℝ)) :=
      measurable_const
    exact hz.max (hAdeleted i)
  have hBdp : ∀ i : Fin n, Measurable (Bdp i) := by
    intro i
    have hz : Measurable (fun _ : (∀ j : {j : Fin n // j ≠ i}, X j.1) => (0 : ℝ)) :=
      measurable_const
    exact hz.max (hBdeleted i)
  have homit : ∀ i : Fin n, Measurable (omitTuple i) := by
    intro i
    exact measurable_pi_iff.2 (fun j => measurable_pi_apply j.1)
  have hAdlift : ∀ i : Fin n, Measurable (fun o => Adp i (omitTuple i o)) :=
    fun i => (hAdp i).comp (homit i)
  have hBdlift : ∀ i : Fin n, Measurable (fun o => Bdp i (omitTuple i o)) :=
    fun i => (hBdp i).comp (homit i)
  have hApAE : (fun ω : Ω0 => Ap (Q ω)) =ᵐ[P] (fun ω => Aenv (Q ω)) := by
    filter_upwards [hAnonneg] with ω hω
    exact max_eq_right hω
  have hBpAE : (fun ω : Ω0 => Bp (Q ω)) =ᵐ[P] (fun ω => Benv (Q ω)) := by
    filter_upwards [hBnonneg] with ω hω
    exact max_eq_right hω
  have hAdpAE : ∀ i : Fin n,
      (fun ω : Ω0 => Adp i (fun j => O j.1 ω)) =ᵐ[P]
        (fun ω => Adeleted i (fun j => O j.1 ω)) := by
    intro i
    filter_upwards [hAdeletenonneg i] with ω hω
    exact max_eq_right hω
  have hBdpAE : ∀ i : Fin n,
      (fun ω : Ω0 => Bdp i (fun j => O j.1 ω)) =ᵐ[P]
        (fun ω => Bdeleted i (fun j => O j.1 ω)) := by
    intro i
    filter_upwards [hBdeletenonneg i] with ω hω
    exact max_eq_right hω
  have hD1Ap : ∀ᵐ ω ∂P, |D1 (Q ω)| ≤ Ap (Q ω) := by
    filter_upwards [hD1A] with ω hω
    exact hω.trans (le_max_right _ _)
  have hD2Bp : ∀ᵐ ω ∂P, |D2 (Q ω)| ≤ Bp (Q ω) := by
    filter_upwards [hD2B] with ω hω
    exact hω.trans (le_max_right _ _)
  have hD1set : MeasurableSet {o : (∀ i : Fin n, X i) | |D1 o| ≤ Ap o} :=
    measurableSet_le (continuous_abs.measurable.comp hD1) hAp
  have hD2set : MeasurableSet {o : (∀ i : Fin n, X i) | |D2 o| ≤ Bp o} :=
    measurableSet_le (continuous_abs.measurable.comp hD2) hBp
  have hOneD2 : Measurable (fun o : (∀ i : Fin n, X i) => 1 + D2 o) :=
    honeTuple.add hD2
  have hPosset : MeasurableSet {o : (∀ i : Fin n, X i) | 0 < 1 + D2 o} :=
    measurableSet_lt hzeroTuple hOneD2
  have hD1μ : ∀ᵐ o ∂μ, |D1 o| ≤ Ap o := by
    change ∀ᵐ o ∂(P.map Q), |D1 o| ≤ Ap o
    exact (ae_map_iff (μ := P) hQ.aemeasurable hD1set).2 hD1Ap
  have hD2μ : ∀ᵐ o ∂μ, |D2 o| ≤ Bp o := by
    change ∀ᵐ o ∂(P.map Q), |D2 o| ≤ Bp o
    exact (ae_map_iff (μ := P) hQ.aemeasurable hD2set).2 hD2Bp
  have hPosμ : ∀ᵐ o ∂μ, 0 < 1 + D2 o := by
    change ∀ᵐ o ∂(P.map Q), 0 < 1 + D2 o
    exact (ae_map_iff (μ := P) hQ.aemeasurable hPosset).2 hD2pos
  let D1raw : ℕ → (∀ i : Fin n, X i) → ℝ :=
    fun M o => max (-(M : ℝ)) (min (D1 o) (M : ℝ))
  let D2raw : ℕ → (∀ i : Fin n, X i) → ℝ :=
    fun M o => min (D2 o) (M : ℝ)
  let AM : ℕ → (∀ i : Fin n, X i) → ℝ := fun M o => min (Ap o) (M : ℝ)
  let BM : ℕ → (∀ i : Fin n, X i) → ℝ := fun M o => min (Bp o) (M : ℝ)
  let AdM : ℕ → ∀ i : Fin n, (∀ j : {j : Fin n // j ≠ i}, X j.1) → ℝ :=
    fun M i o => min (Adp i o) (M : ℝ)
  let BdM : ℕ → ∀ i : Fin n, (∀ j : {j : Fin n // j ≠ i}, X j.1) → ℝ :=
    fun M i o => min (Bdp i o) (M : ℝ)
  let G : Set (∀ i : Fin n, X i) :=
    {o | 0 < 1 + D2 o ∧ |D1 o| ≤ Ap o ∧ |D2 o| ≤ Bp o}
  let D1good : ℕ → (∀ i : Fin n, X i) → ℝ :=
    fun M o => if o ∈ G then D1raw M o else 0
  let D2good : ℕ → (∀ i : Fin n, X i) → ℝ :=
    fun M o => if o ∈ G then D2raw M o else 0
  have hclip := Shao.OQ6.WeightedCostClipping.natural_clipping_envelope_contract
    μ n D1 D2 Ap Bp (fun i o => Adp i (omitTuple i o)) (fun i o => Bdp i (omitTuple i o))
    hD1 hD2 hAp hBp hAdlift hBdlift
    (fun _ => le_max_left _ _) (fun _ => le_max_left _ _)
    (fun _ _ => le_max_left _ _) (fun _ _ => le_max_left _ _)
    hD1μ hD2μ hPosμ
  dsimp only at hclip
  rcases hclip with ⟨hGmeas, hGmass, hMMeas, hMdMeas, hMbounds, hMdbounds,
    hClipDifference, hMints, hDints, hRawValid, hGoodValid, hGoodAE, hClipEventually⟩
  have hGP : ∀ᵐ ω ∂P, Q ω ∈ G := by
    filter_upwards [hD2pos, hD1Ap, hD2Bp] with ω hp ha hb
    exact ⟨hp, ha, hb⟩
  have hGoodAt : ∀ M : ℕ, ∀ᵐ ω ∂P,
      D1good M (Q ω) = D1raw M (Q ω) ∧ D2good M (Q ω) = D2raw M (Q ω) := by
    intro M
    filter_upwards [hGP] with ω hω
    exact ⟨if_pos hω, if_pos hω⟩
  have hAMMeas : ∀ M : ℕ, Measurable (AM M) := fun M => (hMMeas M).2.2.1
  have hBMMeas : ∀ M : ℕ, Measurable (BM M) := fun M => (hMMeas M).2.2.2.1
  have hD1goodMeas : ∀ M : ℕ, Measurable (D1good M) :=
    fun M => (hMMeas M).2.2.2.2.1
  have hD2goodMeas : ∀ M : ℕ, Measurable (D2good M) :=
    fun M => (hMMeas M).2.2.2.2.2
  have hAdMMeas : ∀ (M : ℕ) (i : Fin n), Measurable (AdM M i) := by
    intro M i
    have hm : Measurable (fun _ : (∀ j : {j : Fin n // j ≠ i}, X j.1) => (M : ℝ)) :=
      measurable_const
    exact (hAdp i).min hm
  have hBdMMeas : ∀ (M : ℕ) (i : Fin n), Measurable (BdM M i) := by
    intro M i
    have hm : Measurable (fun _ : (∀ j : {j : Fin n // j ≠ i}, X j.1) => (M : ℝ)) :=
      measurable_const
    exact (hBdp i).min hm
  have hAMint : ∀ M : ℕ, Integrable (fun ω : Ω0 => AM M (Q ω)) P := by
    intro M
    exact hQmp.integrable_comp_of_integrable (hMints M).1
  have hBMint : ∀ M : ℕ, Integrable (fun ω : Ω0 => BM M (Q ω)) P := by
    intro M
    exact hQmp.integrable_comp_of_integrable (hMints M).2.1
  have hAdMint : ∀ (M : ℕ) (i : Fin n),
      Integrable (fun ω : Ω0 => AdM M i (fun j => O j.1 ω)) P := by
    intro M i
    exact hQmp.integrable_comp_of_integrable ((hMints M).2.2 i).1
  have hBdMint : ∀ (M : ℕ) (i : Fin n),
      Integrable (fun ω : Ω0 => BdM M i (fun j => O j.1 ω)) P := by
    intro M i
    exact hQmp.integrable_comp_of_integrable ((hMints M).2.2 i).2
  let fullp : Ω0 → ℝ := fun ω =>
    (x * Ap (Q ω) + x ^ 2 * Bp (Q ω)) * Real.exp (S0 ω)
  let deletedp : Fin n → Ω0 → ℝ := fun i ω =>
    (min |x * ξ0 i ω| 1 *
      (|Ap (Q ω) - Adp i (fun j => O j.1 ω)| +
        x * |Bp (Q ω) - Bdp i (fun j => O j.1 ω)|)) * Real.exp (S0minus i ω)
  have hFullEq : fullp =ᵐ[P] full0 := by
    filter_upwards [hApAE, hBpAE] with ω ha hb
    dsimp only [fullp, full0]
    rw [ha, hb]
  have hDeletedEq : ∀ i : Fin n, deletedp i =ᵐ[P] deleted0 i := by
    intro i
    filter_upwards [hApAE, hBpAE, hAdpAE i, hBdpAE i] with ω ha hb hai hbi
    dsimp only [deletedp, deleted0]
    rw [ha, hb, hai, hbi]
  have hfull0int : Integrable full0 P := hFull
  have hdeleted0int : ∀ i : Fin n, Integrable (deleted0 i) P := hDeleted
  have hfullpint : Integrable fullp P := hfull0int.congr hFullEq.symm
  have hdeletedpint : ∀ i : Fin n, Integrable (deletedp i) P :=
    fun i => (hdeleted0int i).congr (hDeletedEq i).symm
  let RM : ℕ → ℝ := fun M =>
    ((∫ ω, (x * AM M (Q ω) + x ^ 2 * BM M (Q ω)) * Real.exp (S0 ω) ∂P) +
      ∑ i : Fin n, ∫ ω,
        (min |x * ξ0 i ω| 1 *
          (|AM M (Q ω) - AdM M i (fun j => O j.1 ω)| +
            x * |BM M (Q ω) - BdM M i (fun j => O j.1 ω)|)) *
          Real.exp (S0minus i ω) ∂P) / I0
  let Rp : ℝ := ((∫ ω, fullp ω ∂P) + ∑ i : Fin n, ∫ ω, deletedp i ω ∂P) / I0
  have hcost := Shao.OQ6.WeightedCostClipping.actual_weighted_source_cost_clipping_limits
    P n hn ξ0 hξ (fun ω => Ap (Q ω)) (fun ω => Bp (Q ω))
    (fun i ω => Adp i (fun j => O j.1 ω)) (fun i ω => Bdp i (fun j => O j.1 ω))
    (hAp.comp hQ) (hBp.comp hQ)
    (fun i => (hAdp i).comp (measurable_pi_iff.2 (fun j => hO j.1)))
    (fun i => (hBdp i).comp (measurable_pi_iff.2 (fun j => hO j.1)))
    (fun _ => le_max_left _ _) (fun _ => le_max_left _ _)
    (fun _ _ => le_max_left _ _) (fun _ _ => le_max_left _ _)
    x hxpos hfullpint hdeletedpint
  dsimp only at hcost
  rcases hcost with ⟨hExpInt, hIpositive, hJpositive, hFullDensityInt, hFullDensityMass,
    hPartialDensities, hFullClipTests, hDeletedClipTests, hCostEventually,
    hFullL1Limit, hDeletedL1Limit, hFullIntegralLimit, hDeletedIntegralLimit,
    hFullNormalizedLimit, hDeletedNormalizedLimits, hCostOrder, hCostLimit⟩
  have hRMLimitPositive : Filter.Tendsto RM Filter.atTop (nhds Rp) := hCostLimit
  have hDeletedIntegralEq :
      (∑ i : Fin n, ∫ ω, deletedp i ω ∂P) = ∑ i : Fin n, ∫ ω, deleted0 i ω ∂P := by
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_congr_ae (hDeletedEq i)
  have hRp : Rp = R0 := by
    dsimp only [Rp, R0]
    rw [integral_congr_ae hFullEq, hDeletedIntegralEq]
  have hRMLimit : Filter.Tendsto RM Filter.atTop (nhds R0) := by
    simpa only [hRp] using hRMLimitPositive
  let lowerM : ℕ → ℝ := fun M =>
    Shao.standardNormalTail x * Real.exp (-C1 * L0) * (1 - C2 * RM M)
  let upperM : ℕ → ℝ := fun M =>
    Shao.standardNormalTail x * Real.exp (C3 * L0) * (1 + C4 * RM M)
  have hLowerLimit : Filter.Tendsto lowerM Filter.atTop (nhds lower0) := by
    dsimp only [lowerM, lower0]
    exact tendsto_const_nhds.mul
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul hRMLimit))
  have hUpperLimit : Filter.Tendsto upperM Filter.atTop (nhds upper0) := by
    dsimp only [upperM, upper0]
    exact tendsto_const_nhds.mul
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hRMLimit))
  let TrawM : ℕ → Ω0 → ℝ := fun M ω => if V0 ω = 0 then κ ω else
    (W0 ω + D1raw M (Q ω)) / (V0 ω * Real.sqrt (1 + D2raw M (Q ω)))
  let TgoodM : ℕ → Ω0 → ℝ := fun M ω => if V0 ω = 0 then κ ω else
    (W0 ω + D1good M (Q ω)) / (V0 ω * Real.sqrt (1 + D2good M (Q ω)))
  let FrawM : ℕ → Set Ω0 := fun M =>
    {ω | x * V0 ω * Real.sqrt (1 + D2raw M (Q ω)) ≤ W0 ω + D1raw M (Q ω)}
  let FgoodM : ℕ → Set Ω0 := fun M =>
    {ω | x * V0 ω * Real.sqrt (1 + D2good M (Q ω)) ≤ W0 ω + D1good M (Q ω)}
  let QrawM : ℕ → Set Ω0 := fun M => {ω | x ≤ TrawM M ω}
  let QgoodM : ℕ → Set Ω0 := fun M => {ω | x ≤ TgoodM M ω}
  let NrawM : ℕ → Set Ω0 := fun M => {ω | x * |D1raw M (Q ω)| > V0 ω / 8}
  let NgoodM : ℕ → Set Ω0 := fun M => {ω | x * |D1good M (Q ω)| > V0 ω / 8}
  let DrawM : ℕ → Set Ω0 := fun M => {ω | x ^ 2 * |D2raw M (Q ω)| > (1 / 4 : ℝ)}
  let DgoodM : ℕ → Set Ω0 := fun M => {ω | x ^ 2 * |D2good M (Q ω)| > (1 / 4 : ℝ)}
  have hevents := Shao.OQ6.WeightedCostClipping.actual_clipped_event_probabilities
    P n ξ0 hξ (fun ω => D1 (Q ω)) (fun ω => D2 (Q ω)) κ
    (hD1.comp hQ) (hD2.comp hQ) hκ hD2pos x hxnonneg
  dsimp only at hevents
  rcases hevents with ⟨hWMeas, hVMeas, hTMeas, hTMMeas, hZMeas, hZeroFixed,
    hRawEventually, hPositiveComparisons, hComparisonLimits, hNumeratorLimits,
    hDenominatorLimits⟩
  let Rcomp : ℝ → ℝ → Prop := fun a b => b ≤ a
  have hComparison := hComparisonLimits Rcomp (Or.inr (Or.inr (Or.inl rfl)))
  rcases hComparison.1 with ⟨hFMeas, hFMMeas, hFEventually, hFIndicators,
    hFIndicatorLimit, hFSymmetricLimit, hFProbabilityLimit⟩
  rcases hComparison.2 with ⟨hQMeas, hQMMeas, hQEventually, hQIndicators,
    hQIndicatorLimit, hQSymmetricLimit, hQProbabilityLimit⟩
  rcases hNumeratorLimits with ⟨hNMeas, hNMMeas, hNEventually, hNIndicators,
    hNIndicatorLimit, hNSymmetricLimit, hNProbabilityLimit⟩
  rcases hDenominatorLimits with ⟨hDMeas, hDMMeas, hDEventually, hDIndicators,
    hDIndicatorLimit, hDSymmetricLimit, hDProbabilityLimit⟩
  have hFrawLimit : Filter.Tendsto (fun M => P.real (FrawM M))
      Filter.atTop (nhds (P.real F0)) := hFProbabilityLimit
  have hQrawLimit : Filter.Tendsto (fun M => P.real (QrawM M))
      Filter.atTop (nhds (P.real {ω : Ω0 | x ≤ T0 ω})) := hQProbabilityLimit
  have hNrawLimit : Filter.Tendsto (fun M => P.real (NrawM M))
      Filter.atTop (nhds (P.real numeratorBad0)) := hNProbabilityLimit
  have hDrawLimit : Filter.Tendsto (fun M => P.real (DrawM M))
      Filter.atTop (nhds (P.real denominatorBad0)) := hDProbabilityLimit
  have hRealCongr : ∀ (s t : Set Ω0), s =ᵐ[P] t → P.real s = P.real t := by
    intro s t hst
    exact congrArg ENNReal.toReal (measure_congr hst)
  have hFProbEq : ∀ M : ℕ, P.real (FgoodM M) = P.real (FrawM M) := by
    intro M
    apply hRealCongr
    filter_upwards [hGoodAt M] with ω hω
    apply propext
    change (x * V0 ω * Real.sqrt (1 + D2good M (Q ω)) ≤ W0 ω + D1good M (Q ω)) ↔
      (x * V0 ω * Real.sqrt (1 + D2raw M (Q ω)) ≤ W0 ω + D1raw M (Q ω))
    rw [hω.1, hω.2]
  have hQProbEq : ∀ M : ℕ, P.real (QgoodM M) = P.real (QrawM M) := by
    intro M
    apply hRealCongr
    filter_upwards [hGoodAt M] with ω hω
    apply propext
    change (x ≤ TgoodM M ω) ↔ (x ≤ TrawM M ω)
    dsimp only [TgoodM, TrawM]
    rw [hω.1, hω.2]
  have hNProbEq : ∀ M : ℕ, P.real (NgoodM M) = P.real (NrawM M) := by
    intro M
    apply hRealCongr
    filter_upwards [hGoodAt M] with ω hω
    apply propext
    change (x * |D1good M (Q ω)| > V0 ω / 8) ↔
      (x * |D1raw M (Q ω)| > V0 ω / 8)
    rw [hω.1]
  have hDProbEq : ∀ M : ℕ, P.real (DgoodM M) = P.real (DrawM M) := by
    intro M
    apply hRealCongr
    filter_upwards [hGoodAt M] with ω hω
    apply propext
    change (x ^ 2 * |D2good M (Q ω)| > (1 / 4 : ℝ)) ↔
      (x ^ 2 * |D2raw M (Q ω)| > (1 / 4 : ℝ))
    rw [hω.2]
  have hFgoodLimit : Filter.Tendsto (fun M => P.real (FgoodM M))
      Filter.atTop (nhds (P.real F0)) := by
    simpa only [hFProbEq] using hFrawLimit
  have hQgoodLimit : Filter.Tendsto (fun M => P.real (QgoodM M))
      Filter.atTop (nhds (P.real {ω : Ω0 | x ≤ T0 ω})) := by
    simpa only [hQProbEq] using hQrawLimit
  have hNgoodLimit : Filter.Tendsto (fun M => P.real (NgoodM M))
      Filter.atTop (nhds (P.real numeratorBad0)) := by
    simpa only [hNProbEq] using hNrawLimit
  have hDgoodLimit : Filter.Tendsto (fun M => P.real (DgoodM M))
      Filter.atTop (nhds (P.real denominatorBad0)) := by
    simpa only [hDProbEq] using hDrawLimit
  have hBounds : ∀ M : ℕ, 1 ≤ M →
      lowerM M ≤ P.real (FgoodM M) ∧
      P.real (FgoodM M) ≤ upperM M + P.real (NgoodM M) + P.real (DgoodM M) + p0 ∧
      lowerM M - p0 ≤ P.real (QgoodM M) ∧
      P.real (QgoodM M) ≤ upperM M + P.real (NgoodM M) + P.real (DgoodM M) + 2 * p0 := by
    intro M hM
    have hAMnonneg : ∀ o : (∀ i : Fin n, X i), 0 ≤ AM M o :=
      fun o => (hMbounds M o).1
    have hBMnonneg : ∀ o : (∀ i : Fin n, X i), 0 ≤ BM M o :=
      fun o => (hMbounds M o).2.2.2.1
    have hAdMnonneg : ∀ (i : Fin n) (o : ∀ j : {j : Fin n // j ≠ i}, X j.1),
        0 ≤ AdM M i o := fun _ _ => le_min (le_max_left _ _) (Nat.cast_nonneg _)
    have hBdMnonneg : ∀ (i : Fin n) (o : ∀ j : {j : Fin n // j ≠ i}, X j.1),
        0 ≤ BdM M i o := fun _ _ => le_min (le_max_left _ _) (Nat.cast_nonneg _)
    have hD1bound : ∀ o : (∀ i : Fin n, X i), |D1good M o| ≤ AM M o :=
      fun o => (hGoodValid M hM o).2.1
    have hD2bound : ∀ o : (∀ i : Fin n, X i), |D2good M o| ≤ BM M o :=
      fun o => (hGoodValid M hM o).2.2
    have hD2positive : ∀ᵐ ω ∂P, 0 < 1 + D2good M (Q ω) :=
      Filter.Eventually.of_forall (fun ω => (hGoodValid M hM (Q ω)).1)
    have hb := Shao.OQ6.CanonicalIntegrableTailBounds.ambient_canonical_integrable_tail_bounds
      P n hn O hO hOindep g hg hg2 hgmean hgenergy
      (D1good M) (D2good M) (AM M) (BM M) (AdM M) (BdM M)
      (hD1goodMeas M) (hD2goodMeas M) (hAMMeas M) (hBMMeas M)
      (hAdMMeas M) (hBdMMeas M) hAMnonneg hBMnonneg hAdMnonneg hBdMnonneg
      hD1bound hD2bound hD2positive
      (hAMint M) (hBMint M) (hAdMint M) (hBdMint M)
      κ hκ cSZ C1 C2 C3 C4 hSZ x hx hδ hL
    exact hb
  have hUpperBadLimit : Filter.Tendsto
      (fun M => upperM M + P.real (NgoodM M) + P.real (DgoodM M) + p0)
      Filter.atTop (nhds (upper0 + P.real numeratorBad0 + P.real denominatorBad0 + p0)) :=
    ((hUpperLimit.add hNgoodLimit).add hDgoodLimit).add tendsto_const_nhds
  have hLowerZeroLimit : Filter.Tendsto (fun M => lowerM M - p0)
      Filter.atTop (nhds (lower0 - p0)) := hLowerLimit.sub tendsto_const_nhds
  have hUpperTwoZeroLimit : Filter.Tendsto
      (fun M => upperM M + P.real (NgoodM M) + P.real (DgoodM M) + 2 * p0)
      Filter.atTop (nhds (upper0 + P.real numeratorBad0 + P.real denominatorBad0 + 2 * p0)) :=
    ((hUpperLimit.add hNgoodLimit).add hDgoodLimit).add tendsto_const_nhds
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_of_tendsto_of_tendsto hLowerLimit hFgoodLimit
      ((Filter.eventually_ge_atTop 1).mono (fun M hM => (hBounds M hM).1))
  · exact le_of_tendsto_of_tendsto hFgoodLimit hUpperBadLimit
      ((Filter.eventually_ge_atTop 1).mono (fun M hM => (hBounds M hM).2.1))
  · exact le_of_tendsto_of_tendsto hLowerZeroLimit hQgoodLimit
      ((Filter.eventually_ge_atTop 1).mono (fun M hM => (hBounds M hM).2.2.1))
  · exact le_of_tendsto_of_tendsto hQgoodLimit hUpperTwoZeroLimit
      ((Filter.eventually_ge_atTop 1).mono (fun M hM => (hBounds M hM).2.2.2))

end

end Shao.OQ6.WeightedAETailBounds
