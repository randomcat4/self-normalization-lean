import Shao.OQ6.NormalizedRawNumeratorBuffer

noncomputable section
open MeasureTheory
open scoped BigOperators Classical Topology

namespace Shao.OQ6.NormalizedUpperErrorGoodsetPayment

set_option autoImplicit false

theorem actual_normalized_upper_error_goodset_payment
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (hξ2 : ∀ i : Fin n, MemLp (ξ i) 2 ν)
    (hξmean : ∀ i : Fin n, (∫ ω, ξ i ω ∂ν) = 0)
    (hξenergy : (∑ i : Fin n, ∫ ω, (ξ i ω) ^ 2 ∂ν) = 1)
    (Y : ℕ → Fin n → Ω → ℝ)
    (hY : ∀ (k : ℕ) (i : Fin n), Measurable (Y k i))
    (ε : ℕ → ℝ) (hε : ∀ k : ℕ, 0 < ε k)
    (hεsmall : ∀ k : ℕ, ε k < 1 / (4 * Real.sqrt (n : ℝ)))
    (hεlim : Filter.Tendsto ε Filter.atTop (nhds (0 : ℝ)))
    (herr : ∀ (k : ℕ) (i : Fin n) (ω : Ω),
      |Y k i ω - ξ i ω| ≤ ε k)
    (D1 D2 : Ω → ℝ)
    (hD1 : Measurable D1) (hD2 : Measurable D2)
    (z : ℝ) (hz : 1 ≤ z)
    (H : Set Ω) (hH : MeasurableSet H)
    (hgood : ∀ ω : Ω, ω ∈ H →
      0 < Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2) ∧
      z * |D1 ω| ≤ Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2) / 8 ∧
      z ^ 2 * |D2 ω| ≤ (1 / 8 : ℝ)) :
    let η : ℕ → Fin n → Ω → ℝ := fun k =>
      Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
    let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
    let Wη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, η k i ω
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
    let Vη : ℕ → Ω → ℝ := fun k ω =>
      Real.sqrt (∑ i : Fin n, (η k i ω) ^ 2)
    let b : Ω → ℝ := fun ω => Real.sqrt (1 + D2 ω)
    let Q : ℕ → Ω → ℝ := fun k ω =>
      W ω - Wη k ω + z * b ω * (Vη k ω - V ω)
    let Dη : ℕ → Ω → ℝ := fun k ω => D1 ω + Q k ω
    let E : ℕ → Set Ω := fun k =>
      {ω : Ω | z * |Dη k ω| > Vη k ω / 4}
    let E2 : Set Ω := {ω : Ω | z ^ 2 * |D2 ω| > (1 / 4 : ℝ)}
    let Z : Set Ω := {ω : Ω | V ω = 0}
    (∀ (k : ℕ) (i : Fin n), Measurable (η k i)) ∧
    (∀ k : ℕ, Measurable (Q k) ∧ Measurable (Dη k) ∧
      MeasurableSet (E k)) ∧
    (MeasurableSet E2 ∧ MeasurableSet Z) ∧
    (∀ (i : Fin n) (ω : Ω),
      Filter.Tendsto (fun k : ℕ => η k i ω) Filter.atTop (nhds (ξ i ω))) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => Wη k ω)
      Filter.atTop (nhds (W ω))) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => Vη k ω)
      Filter.atTop (nhds (V ω))) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => Q k ω)
      Filter.atTop (nhds (0 : ℝ))) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => Dη k ω)
      Filter.atTop (nhds (D1 ω))) ∧
    (∀ ω : Ω, ω ∈ H → (7 / 8 : ℝ) ≤ 1 + D2 ω ∧ 0 < b ω) ∧
    (∀ ω : Ω, ω ∈ H → ∀ᶠ k : ℕ in Filter.atTop,
      0 < Vη k ω ∧ z * |Dη k ω| ≤ Vη k ω / 4) ∧
    E2 ⊆ Hᶜ ∧
    Z ⊆ Hᶜ ∧
    ν.real E2 ≤ ν.real Hᶜ ∧
    ν.real Z ≤ ν.real Hᶜ ∧
    (∀ δ : ℝ, 0 < δ → ∀ᶠ k : ℕ in Filter.atTop,
      ν.real (E k) ≤ ν.real Hᶜ + δ) ∧
    Filter.limsup (fun k : ℕ => ν.real (E k)) Filter.atTop ≤ ν.real Hᶜ := by
  classical
  dsimp only
  let η : ℕ → Fin n → Ω → ℝ := fun k =>
    Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
  let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
  let Wη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, η k i ω
  let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
  let Vη : ℕ → Ω → ℝ := fun k ω =>
    Real.sqrt (∑ i : Fin n, (η k i ω) ^ 2)
  let b : Ω → ℝ := fun ω => Real.sqrt (1 + D2 ω)
  let Q : ℕ → Ω → ℝ := fun k ω =>
    W ω - Wη k ω + z * b ω * (Vη k ω - V ω)
  let Dη : ℕ → Ω → ℝ := fun k ω => D1 ω + Q k ω
  let E : ℕ → Set Ω := fun k =>
    {ω : Ω | z * |Dη k ω| > Vη k ω / 4}
  let E2 : Set Ω := {ω : Ω | z ^ 2 * |D2 ω| > (1 / 4 : ℝ)}
  let Z : Set Ω := {ω : Ω | V ω = 0}
  let Eorig : Set Ω := {ω : Ω | z * |D1 ω| > V ω / 8}
  let U : ℕ → Set Ω := fun N => ⋃ k : ℕ, ⋃ (_ : N ≤ k), E k
  let L : Set Ω := ⋂ N : ℕ, U N
  have hDbridge (k : ℕ) (ω : Ω) :
      D1 ω + W ω - Wη k ω + z * b ω * (Vη k ω - V ω) = Dη k ω := by
    dsimp only [Dη, Q]
    ring
  rcases Shao.OQ6.NormalizedAnalyticCostLimits.actual_normalization_sequence_limits
      ν n hn ξ hξ hξ2 hξmean hξenergy Y hY ε hε hεsmall hεlim herr with
    ⟨_, _, _, _, _, hηspec, _, hηpoint, _, _, _, _⟩
  have hηm (k : ℕ) (i : Fin n) : Measurable (η k i) := (hηspec k i).1
  have hz0 : 0 ≤ z := le_trans (by norm_num) hz
  rcases Shao.OQ6.NormalizedRawNumeratorBuffer.actual_normalized_raw_numerator_bad_event_limsup
      ν n hn ξ hξ hξ2 hξmean hξenergy Y hY ε hε hεsmall hεlim herr
      D1 D2 hD1 hD2 z hz0 with
    ⟨hDηmRaw, hEmRaw, _, hZm, _, _, _, _, hWpoint, hVpoint, hDpointRaw,
      _, _, hsafeRaw, hLcoverRaw, _, _, _, _, _, _, _, _, _, _, _,
      hUreallimRaw, _, _, _⟩
  have hDηm (k : ℕ) : Measurable (Dη k) := by
    have hm : Measurable (fun ω : Ω =>
        D1 ω + W ω - Wη k ω + z * b ω * (Vη k ω - V ω)) := hDηmRaw k
    simpa only [hDbridge] using hm
  have hQm (k : ℕ) : Measurable (Q k) := by
    have hm := (hDηm k).sub hD1
    change Measurable (fun ω : Ω => Dη k ω - D1 ω) at hm
    simpa only [Dη, add_sub_cancel_left] using hm
  have hEm (k : ℕ) : MeasurableSet (E k) := by
    have hm : MeasurableSet {ω : Ω |
        z * |D1 ω + W ω - Wη k ω + z * b ω * (Vη k ω - V ω)| >
          Vη k ω / 4} := hEmRaw k
    simpa only [E, hDbridge] using hm
  have hE2m : MeasurableSet E2 := by
    exact measurableSet_lt measurable_const
      (measurable_const.mul (continuous_abs.measurable.comp hD2))
  have hDpoint (ω : Ω) : Filter.Tendsto (fun k : ℕ => Dη k ω)
      Filter.atTop (nhds (D1 ω)) := by
    have hp : Filter.Tendsto (fun k : ℕ =>
        D1 ω + W ω - Wη k ω + z * b ω * (Vη k ω - V ω))
        Filter.atTop (nhds (D1 ω)) := hDpointRaw ω
    simpa only [hDbridge] using hp
  have hQpoint (ω : Ω) : Filter.Tendsto (fun k : ℕ => Q k ω)
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [Dη, add_sub_cancel_left, sub_self] using
      (hDpoint ω).sub (tendsto_const_nhds (x := D1 ω))
  have hD2good (ω : Ω) (hω : ω ∈ H) :
      (7 / 8 : ℝ) ≤ 1 + D2 ω ∧ 0 < b ω := by
    have hm : z ^ 2 * |D2 ω| ≤ (1 / 8 : ℝ) := (hgood ω hω).2.2
    have hz2 : (1 : ℝ) ≤ z ^ 2 := by nlinarith [sq_nonneg (z - 1)]
    have hp : 0 ≤ (z ^ 2 - 1) * |D2 ω| :=
      mul_nonneg (sub_nonneg.mpr hz2) (abs_nonneg (D2 ω))
    have habs : |D2 ω| ≤ (1 / 8 : ℝ) := by nlinarith
    have hlow : (7 / 8 : ℝ) ≤ 1 + D2 ω := by
      have hneg := (abs_le.mp habs).1
      linarith
    refine ⟨hlow, ?_⟩
    change 0 < Real.sqrt (1 + D2 ω)
    exact Real.sqrt_pos.mpr (by linarith)
  have hsafe (ω : Ω) (hω : ω ∈ H) :
      ∀ᶠ k : ℕ in Filter.atTop,
        0 < Vη k ω ∧ z * |Dη k ω| ≤ Vη k ω / 4 := by
    have hmargin : 0 < V ω ∧ z * |D1 ω| ≤ V ω / 8 ∧
        z ^ 2 * |D2 ω| ≤ (1 / 8 : ℝ) := hgood ω hω
    have hs : ∀ᶠ k : ℕ in Filter.atTop,
        z * |D1 ω + W ω - Wη k ω + z * b ω * (Vη k ω - V ω)| ≤
          Vη k ω / 4 := hsafeRaw ω hmargin.1 hmargin.2.1
    have hs' : ∀ᶠ k : ℕ in Filter.atTop,
        z * |Dη k ω| ≤ Vη k ω / 4 := by
      simpa only [hDbridge] using hs
    have hv : ∀ᶠ k : ℕ in Filter.atTop, 0 < Vη k ω :=
      (hVpoint ω).eventually (lt_mem_nhds hmargin.1)
    filter_upwards [hv, hs'] with k hkpos hksafe
    exact ⟨hkpos, hksafe⟩
  have hLcover : L ⊆ Eorig ∪ Z := by
    have hc :
        (⋂ N : ℕ, ⋃ k : ℕ, ⋃ (_ : N ≤ k), {ω : Ω |
          z * |D1 ω + W ω - Wη k ω + z * b ω * (Vη k ω - V ω)| >
            Vη k ω / 4}) ⊆ Eorig ∪ Z := hLcoverRaw
    simpa only [L, U, E, hDbridge] using hc
  have hLsub : L ⊆ Hᶜ := by
    intro ω hLω hHω
    rcases hLcover hLω with hbad | hzero
    · exact (not_lt_of_ge (hgood ω hHω).2.1) hbad
    · exact (ne_of_gt (hgood ω hHω).1) hzero
  have hrealcover : ν.real L ≤ ν.real Hᶜ := measureReal_mono hLsub
  have hUreallim : Filter.Tendsto (fun N : ℕ => ν.real (U N))
      Filter.atTop (nhds (ν.real L)) := by
    have ht : Filter.Tendsto
        (fun N : ℕ => ν.real (⋃ k : ℕ, ⋃ (_ : N ≤ k), {ω : Ω |
          z * |D1 ω + W ω - Wη k ω + z * b ω * (Vη k ω - V ω)| >
            Vη k ω / 4}))
        Filter.atTop (nhds (ν.real
          (⋂ N : ℕ, ⋃ k : ℕ, ⋃ (_ : N ≤ k), {ω : Ω |
            z * |D1 ω + W ω - Wη k ω + z * b ω * (Vη k ω - V ω)| >
              Vη k ω / 4}))) := hUreallimRaw
    simpa only [L, U, E, hDbridge] using ht
  have hE2sub : E2 ⊆ Hᶜ := by
    intro ω hbad hHω
    have hm : z ^ 2 * |D2 ω| ≤ (1 / 8 : ℝ) := (hgood ω hHω).2.2
    change z ^ 2 * |D2 ω| > (1 / 4 : ℝ) at hbad
    linarith
  have hZsub : Z ⊆ Hᶜ := by
    intro ω hzero hHω
    exact (ne_of_gt (hgood ω hHω).1) hzero
  have heventual (δ : ℝ) (hδ : 0 < δ) :
      ∀ᶠ k : ℕ in Filter.atTop, ν.real (E k) ≤ ν.real Hᶜ + δ := by
    have hc : ν.real L < ν.real L + δ := by linarith
    have htail : ∀ᶠ N : ℕ in Filter.atTop, ν.real (U N) < ν.real L + δ :=
      hUreallim.eventually (gt_mem_nhds hc)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 htail
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro k hk
    have hsub : E k ⊆ U N := by
      intro ω hω
      exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hk, hω⟩⟩
    have hmono : ν.real (E k) ≤ ν.real (U N) := measureReal_mono hsub
    have hNself := hN N le_rfl
    linarith
  have hprob (k : ℕ) : 0 ≤ ν.real (E k) ∧ ν.real (E k) ≤ 1 :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  have hcobounded := Filter.isCoboundedUnder_le_of_le (Filter.atTop : Filter ℕ)
    (x := (0 : ℝ)) (fun k : ℕ => (hprob k).1)
  have hlimupper (δ : ℝ) (hδ : 0 < δ) :
      Filter.limsup (fun k : ℕ => ν.real (E k)) Filter.atTop ≤ ν.real Hᶜ + δ :=
    Filter.limsup_le_of_le hcobounded (heventual δ hδ)
  have hlimsup : Filter.limsup (fun k : ℕ => ν.real (E k)) Filter.atTop ≤
      ν.real Hᶜ := by
    apply le_of_not_gt
    intro hgt
    have hhalf : 0 <
        (Filter.limsup (fun k : ℕ => ν.real (E k)) Filter.atTop - ν.real Hᶜ) / 2 := by
      linarith
    have hb := hlimupper
      ((Filter.limsup (fun k : ℕ => ν.real (E k)) Filter.atTop - ν.real Hᶜ) / 2) hhalf
    linarith
  exact ⟨hηm, (fun k => ⟨hQm k, hDηm k, hEm k⟩), ⟨hE2m, hZm⟩,
    hηpoint, hWpoint, hVpoint, hQpoint, hDpoint, hD2good, hsafe,
    hE2sub, hZsub, measureReal_mono hE2sub, measureReal_mono hZsub,
    heventual, hlimsup⟩

end Shao.OQ6.NormalizedUpperErrorGoodsetPayment
