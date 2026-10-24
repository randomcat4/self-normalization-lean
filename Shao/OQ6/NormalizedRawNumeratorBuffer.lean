import Shao.OQ6.NormalizedAnalyticCostLimits
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.LiminfLimsup

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Shao.OQ6.NormalizedRawNumeratorBuffer

noncomputable section

open MeasureTheory
open scoped BigOperators Classical Topology

theorem actual_normalized_raw_numerator_bad_event_limsup
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
    (herr : ∀ (k : ℕ) (i : Fin n) (ω : Ω), |Y k i ω - ξ i ω| ≤ ε k)
    (D1 D2 : Ω → ℝ)
    (hD1 : Measurable D1) (hD2 : Measurable D2)
    (x : ℝ) (hx : 0 ≤ x) :
    let η : ℕ → Fin n → Ω → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
    let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
    let Wη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, η k i ω
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
    let Vη : ℕ → Ω → ℝ := fun k ω => Real.sqrt (∑ i : Fin n, (η k i ω) ^ 2)
    let b : Ω → ℝ := fun ω => Real.sqrt (1 + D2 ω)
    let Dη : ℕ → Ω → ℝ := fun k ω => D1 ω + W ω - Wη k ω + x * b ω * (Vη k ω - V ω)
    let E : ℕ → Set Ω := fun k => {ω : Ω | x * |Dη k ω| > Vη k ω / 4}
    let Eorig : Set Ω := {ω : Ω | x * |D1 ω| > V ω / 8}
    let Z : Set Ω := {ω : Ω | V ω = 0}
    let p0 : ℝ := ν.real Z
    let U : ℕ → Set Ω := fun N => ⋃ k : ℕ, ⋃ (_ : N ≤ k), E k
    let L : Set Ω := ⋂ N : ℕ, U N
    (∀ k : ℕ, Measurable (Dη k)) ∧
    (∀ k : ℕ, MeasurableSet (E k)) ∧
    MeasurableSet Eorig ∧
    MeasurableSet Z ∧
    (∀ N : ℕ, MeasurableSet (U N)) ∧
    MeasurableSet L ∧
    (∀ ω : Ω, 0 ≤ V ω) ∧
    (∀ (k : ℕ) (ω : Ω), 0 ≤ Vη k ω) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => Wη k ω) Filter.atTop (nhds (W ω))) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => Vη k ω) Filter.atTop (nhds (V ω))) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => Dη k ω) Filter.atTop (nhds (D1 ω))) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => x * |Dη k ω| - Vη k ω / 4)
      Filter.atTop (nhds (x * |D1 ω| - V ω / 4))) ∧
    (∀ ω : Ω, 0 < V ω → x * |D1 ω| ≤ V ω / 8 →
      x * |D1 ω| - V ω / 4 ≤ -(V ω / 8) ∧ -(V ω / 8) < 0) ∧
    (∀ ω : Ω, 0 < V ω → x * |D1 ω| ≤ V ω / 8 →
      ∀ᶠ k : ℕ in Filter.atTop, x * |Dη k ω| ≤ Vη k ω / 4) ∧
    L ⊆ Eorig ∪ Z ∧
    Antitone U ∧
    (∀ k : ℕ, ν (E k) ≠ ⊤) ∧
    ν Eorig ≠ ⊤ ∧
    ν Z ≠ ⊤ ∧
    (∀ N : ℕ, ν (U N) ≠ ⊤) ∧
    ν L ≠ ⊤ ∧
    ν L ≤ ν (Eorig ∪ Z) ∧
    ν (Eorig ∪ Z) ≤ ν Eorig + ν Z ∧
    Filter.Tendsto (fun N : ℕ => ν (U N)) Filter.atTop (nhds (ν L)) ∧
    (∀ k : ℕ, 0 ≤ ν.real (E k) ∧ ν.real (E k) ≤ 1) ∧
    (∀ N : ℕ, 0 ≤ ν.real (U N) ∧ ν.real (U N) ≤ 1) ∧
    Filter.Tendsto (fun N : ℕ => ν.real (U N)) Filter.atTop (nhds (ν.real L)) ∧
    ν.real L ≤ ν.real Eorig + p0 ∧
    (∀ δ : ℝ, 0 < δ → ∀ᶠ k : ℕ in Filter.atTop,
      ν.real (E k) ≤ ν.real Eorig + p0 + δ) ∧
    Filter.limsup (fun k : ℕ => ν.real (E k)) Filter.atTop ≤ ν.real Eorig + p0 := by
  classical
  dsimp only
  let η : ℕ → Fin n → Ω → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
  let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
  let Wη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, η k i ω
  let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
  let Vη : ℕ → Ω → ℝ := fun k ω => Real.sqrt (∑ i : Fin n, (η k i ω) ^ 2)
  let b : Ω → ℝ := fun ω => Real.sqrt (1 + D2 ω)
  let Dη : ℕ → Ω → ℝ := fun k ω => D1 ω + W ω - Wη k ω + x * b ω * (Vη k ω - V ω)
  let E : ℕ → Set Ω := fun k => {ω : Ω | x * |Dη k ω| > Vη k ω / 4}
  let Eorig : Set Ω := {ω : Ω | x * |D1 ω| > V ω / 8}
  let Z : Set Ω := {ω : Ω | V ω = 0}
  let p0 : ℝ := ν.real Z
  let U : ℕ → Set Ω := fun N => ⋃ k : ℕ, ⋃ (_ : N ≤ k), E k
  let L : Set Ω := ⋂ N : ℕ, U N
  rcases Shao.OQ6.NormalizedAnalyticCostLimits.actual_normalization_sequence_limits
    ν n hn ξ hξ hξ2 hξmean hξenergy Y hY ε hε hεsmall hεlim herr with
    ⟨_, _, _, _, _, hηspec, _, _, hWpoint, hVpoint, _, _⟩
  have hηm (k : ℕ) (i : Fin n) : Measurable (η k i) := (hηspec k i).1
  have hWm : Measurable W :=
    Finset.measurable_sum Finset.univ (fun i _ => hξ i)
  have hWηm (k : ℕ) : Measurable (Wη k) :=
    Finset.measurable_sum Finset.univ (fun i _ => hηm k i)
  have hVm : Measurable V := by
    apply Measurable.sqrt
    exact Finset.measurable_sum Finset.univ (fun i _ =>
      (hξ i).pow (measurable_const : Measurable (fun _ : Ω => (2 : ℕ))))
  have hVηm (k : ℕ) : Measurable (Vη k) := by
    apply Measurable.sqrt
    exact Finset.measurable_sum Finset.univ (fun i _ =>
      (hηm k i).pow (measurable_const : Measurable (fun _ : Ω => (2 : ℕ))))
  have hbm : Measurable b := (measurable_const.add hD2).sqrt
  have hDηm (k : ℕ) : Measurable (Dη k) :=
    ((hD1.add hWm).sub (hWηm k)).add
      ((measurable_const.mul hbm).mul ((hVηm k).sub hVm))
  have hEm (k : ℕ) : MeasurableSet (E k) := by
    exact measurableSet_lt ((hVηm k).div measurable_const)
      (measurable_const.mul (continuous_abs.measurable.comp (hDηm k)))
  have hEorigm : MeasurableSet Eorig := by
    exact measurableSet_lt (hVm.div measurable_const) (measurable_const.mul (continuous_abs.measurable.comp hD1))
  have hZm : MeasurableSet Z := measurableSet_eq_fun hVm measurable_const
  have hUm (N : ℕ) : MeasurableSet (U N) := by
    exact MeasurableSet.iUnion (fun k : ℕ =>
      MeasurableSet.iUnion (fun _ : N ≤ k => hEm k))
  have hLm : MeasurableSet L := MeasurableSet.iInter hUm
  have hVnonneg (ω : Ω) : 0 ≤ V ω := Real.sqrt_nonneg _
  have hVηnonneg (k : ℕ) (ω : Ω) : 0 ≤ Vη k ω := Real.sqrt_nonneg _
  have hDpoint (ω : Ω) : Filter.Tendsto (fun k : ℕ => Dη k ω)
      Filter.atTop (nhds (D1 ω)) := by
    have hWpoint' : Filter.Tendsto (fun k : ℕ => Wη k ω)
        Filter.atTop (nhds (W ω)) := hWpoint ω
    have hVpoint' : Filter.Tendsto (fun k : ℕ => Vη k ω)
        Filter.atTop (nhds (V ω)) := hVpoint ω
    simpa only [Dη, sub_self, mul_zero, add_zero, add_sub_cancel_right] using
      ((tendsto_const_nhds (x := D1 ω + W ω)).sub hWpoint').add
        ((hVpoint'.sub (tendsto_const_nhds (x := V ω))).const_mul (x * b ω))
  have hgaplim (ω : Ω) :
      Filter.Tendsto (fun k : ℕ => x * |Dη k ω| - Vη k ω / 4)
        Filter.atTop (nhds (x * |D1 ω| - V ω / 4)) := by
    simpa only [div_eq_mul_inv] using
      ((hDpoint ω).abs.const_mul x).sub ((hVpoint ω).mul_const ((4 : ℝ)⁻¹))
  have hstrict (ω : Ω) (hVpos : 0 < V ω) (hsmall : x * |D1 ω| ≤ V ω / 8) :
      x * |D1 ω| - V ω / 4 ≤ -(V ω / 8) ∧ -(V ω / 8) < 0 := by
    constructor <;> linarith
  have hsafe (ω : Ω) (hVpos : 0 < V ω) (hsmall : x * |D1 ω| ≤ V ω / 8) :
      ∀ᶠ k : ℕ in Filter.atTop, x * |Dη k ω| ≤ Vη k ω / 4 := by
    have hneg : x * |D1 ω| - V ω / 4 < 0 :=
      lt_of_le_of_lt (hstrict ω hVpos hsmall).1 (hstrict ω hVpos hsmall).2
    have hevent := (hgaplim ω).eventually (gt_mem_nhds hneg)
    filter_upwards [hevent] with k hk
    linarith
  have hLcover : L ⊆ Eorig ∪ Z := by
    intro ω hLω
    by_contra hnot
    have hnotE : ω ∉ Eorig := fun h => hnot (Or.inl h)
    have hnotZ : ω ∉ Z := fun h => hnot (Or.inr h)
    have hVne : V ω ≠ 0 := hnotZ
    have hVpos : 0 < V ω := by
      by_contra hnV
      exact hVne (le_antisymm (le_of_not_gt hnV) (hVnonneg ω))
    have hsmall : x * |D1 ω| ≤ V ω / 8 := le_of_not_gt hnotE
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hsafe ω hVpos hsmall)
    have hUω : ω ∈ U N := Set.mem_iInter.mp hLω N
    rcases Set.mem_iUnion.mp hUω with ⟨k, hk⟩
    rcases Set.mem_iUnion.mp hk with ⟨hNk, hEk⟩
    exact (not_lt_of_ge (hN k hNk)) hEk
  have hUanti : Antitone U := by
    intro N M hNM ω hMω
    rcases Set.mem_iUnion.mp hMω with ⟨k, hk⟩
    rcases Set.mem_iUnion.mp hk with ⟨hMk, hEk⟩
    exact Set.mem_iUnion.mpr ⟨k,
      Set.mem_iUnion.mpr ⟨le_trans hNM hMk, hEk⟩⟩
  have hfinite (S : Set Ω) : ν S ≠ ⊤ := measure_ne_top ν S
  have hcoverμ : ν L ≤ ν (Eorig ∪ Z) := measure_mono hLcover
  have hunionμ : ν (Eorig ∪ Z) ≤ ν Eorig + ν Z := measure_union_le Eorig Z
  have hUmeasurelim : Filter.Tendsto (fun N : ℕ => ν (U N))
      Filter.atTop (nhds (ν L)) := by
    exact tendsto_measure_iInter_atTop (μ := ν)
      (fun N => (hUm N).nullMeasurableSet) hUanti ⟨0, hfinite (U 0)⟩
  have hprob (k : ℕ) : 0 ≤ ν.real (E k) ∧ ν.real (E k) ≤ 1 :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  have hUprob (N : ℕ) : 0 ≤ ν.real (U N) ∧ ν.real (U N) ≤ 1 :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  have hUreallim : Filter.Tendsto (fun N : ℕ => ν.real (U N))
      Filter.atTop (nhds (ν.real L)) := by
    have hreal := (ENNReal.continuousAt_toReal (hfinite L)).tendsto.comp hUmeasurelim
    simpa only [Function.comp_def, ← measureReal_def] using hreal
  have hrealcover : ν.real L ≤ ν.real Eorig + p0 := by
    calc
      ν.real L ≤ ν.real (Eorig ∪ Z) := measureReal_mono hLcover
      _ ≤ ν.real Eorig + p0 := by
        simpa only [p0] using (measureReal_union_le (μ := ν) Eorig Z)
  have heventual (δ : ℝ) (hδ : 0 < δ) :
      ∀ᶠ k : ℕ in Filter.atTop, ν.real (E k) ≤ ν.real Eorig + p0 + δ := by
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
  have hcobounded := Filter.isCoboundedUnder_le_of_le (Filter.atTop : Filter ℕ)
    (x := (0 : ℝ)) (fun k : ℕ => (hprob k).1)
  have hlimupper (δ : ℝ) (hδ : 0 < δ) :
      Filter.limsup (fun k : ℕ => ν.real (E k)) Filter.atTop ≤
        ν.real Eorig + p0 + δ :=
    Filter.limsup_le_of_le hcobounded (heventual δ hδ)
  have hlimsup : Filter.limsup (fun k : ℕ => ν.real (E k)) Filter.atTop ≤
      ν.real Eorig + p0 := by
    apply le_of_not_gt
    intro hgt
    have hhalf : 0 <
        (Filter.limsup (fun k : ℕ => ν.real (E k)) Filter.atTop -
          (ν.real Eorig + p0)) / 2 := by linarith
    have hb := hlimupper
      ((Filter.limsup (fun k : ℕ => ν.real (E k)) Filter.atTop -
        (ν.real Eorig + p0)) / 2) hhalf
    linarith
  exact ⟨hDηm, hEm, hEorigm, hZm, hUm, hLm, hVnonneg, hVηnonneg,
    hWpoint, hVpoint, hDpoint, hgaplim, hstrict, hsafe, hLcover, hUanti,
    (fun k => hfinite (E k)), hfinite Eorig, hfinite Z,
    (fun N => hfinite (U N)), hfinite L, hcoverμ, hunionμ, hUmeasurelim,
    hprob, hUprob, hUreallim, hrealcover, heventual, hlimsup⟩

end

end Shao.OQ6.NormalizedRawNumeratorBuffer
