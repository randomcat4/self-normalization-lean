import Shao.OQ6.WeightedCostClipping
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

namespace Shao.OQ6.CompactCostParameterLimits

noncomputable section

open MeasureTheory
open scoped BigOperators Classical Topology

theorem actual_continuous_compact_cost_parameter_sequence_limits
    {Ω : Type u} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (hξ2 : ∀ i : Fin n, MemLp (ξ i) 2 ν)
    (A B : Ω → ℝ) (Adelete Bdelete : Fin n → Ω → ℝ)
    (hA : Measurable A) (hB : Measurable B)
    (hAdelete : ∀ i : Fin n, Measurable (Adelete i))
    (hBdelete : ∀ i : Fin n, Measurable (Bdelete i))
    (hAnonneg : ∀ᵐ ω ∂ν, 0 ≤ A ω)
    (hBnonneg : ∀ᵐ ω ∂ν, 0 ≤ B ω)
    (x : ℝ) (hx : 0 ≤ x)
    (hFull : Integrable (fun ω => A ω + x * B ω) ν)
    (hDeleted : ∀ i : Fin n, Integrable (fun ω =>
      min |ξ i ω| (1 + x)⁻¹ * (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)) ν)
    (τ : ℕ → ℝ)
    (hτbounds : ∀ k : ℕ, 0 ≤ τ k ∧ τ k ≤ x)
    (hτlimit : Filter.Tendsto τ Filter.atTop (nhds x)) :
    let cap : Fin n → Ω → ℝ := fun i ω => min |ξ i ω| (1 + x)⁻¹
    let capSeq : ℕ → Fin n → Ω → ℝ := fun k i ω => min |ξ i ω| (1 + τ k)⁻¹
    let moment : Fin n → Ω → ℝ := fun i ω => ((1 + x) * ξ i ω) ^ 2 * min |(1 + x) * ξ i ω| 1
    let momentSeq : ℕ → Fin n → Ω → ℝ := fun k i ω => ((1 + τ k) * ξ i ω) ^ 2 * min |(1 + τ k) * ξ i ω| 1
    let full : Ω → ℝ := fun ω => A ω + x * B ω
    let fullSeq : ℕ → Ω → ℝ := fun k ω => A ω + τ k * B ω
    let deleted : Fin n → Ω → ℝ := fun i ω => cap i ω * (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)
    let deletedSeq : ℕ → Fin n → Ω → ℝ := fun k i ω => capSeq k i ω * (|A ω - Adelete i ω| + τ k * |B ω - Bdelete i ω|)
    let δcompact : Fin n → ℝ := fun i => ∫ ω, moment i ω ∂ν
    let δcompactSeq : ℕ → Fin n → ℝ := fun k i => ∫ ω, momentSeq k i ω ∂ν
    let Lcompact : ℝ := ∑ i : Fin n, δcompact i
    let LcompactSeq : ℕ → ℝ := fun k => ∑ i : Fin n, δcompactSeq k i
    let compactCost : ℝ := Lcompact + (∫ ω, full ω ∂ν) + ∑ i : Fin n, ∫ ω, deleted i ω ∂ν
    let compactCostSeq : ℕ → ℝ := fun k => LcompactSeq k + (∫ ω, fullSeq k ω ∂ν) + ∑ i : Fin n, ∫ ω, deletedSeq k i ω ∂ν
    (∀ i : Fin n, Integrable (moment i) ν) ∧
    (∀ k : ℕ, Integrable (fullSeq k) ν ∧
      ∀ i : Fin n, Integrable (deletedSeq k i) ν ∧ Integrable (momentSeq k i) ν) ∧
    Filter.Tendsto (fun k : ℕ => ∫ ω, |fullSeq k ω - full ω| ∂ν)
      Filter.atTop (nhds (0 : ℝ)) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => ∫ ω, |deletedSeq k i ω - deleted i ω| ∂ν)
      Filter.atTop (nhds (0 : ℝ))) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => δcompactSeq k i)
      Filter.atTop (nhds (δcompact i))) ∧
    Filter.Tendsto (fun k : ℕ => ∫ ω, fullSeq k ω ∂ν)
      Filter.atTop (nhds (∫ ω, full ω ∂ν)) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => ∫ ω, deletedSeq k i ω ∂ν)
      Filter.atTop (nhds (∫ ω, deleted i ω ∂ν))) ∧
    Filter.Tendsto LcompactSeq Filter.atTop (nhds Lcompact) ∧
    Filter.Tendsto compactCostSeq Filter.atTop (nhds compactCost) := by
  classical
  dsimp only
  let cap : Fin n → Ω → ℝ := fun i ω => min |ξ i ω| (1 + x)⁻¹
  let capSeq : ℕ → Fin n → Ω → ℝ := fun k i ω => min |ξ i ω| (1 + τ k)⁻¹
  let moment : Fin n → Ω → ℝ := fun i ω => ((1 + x) * ξ i ω) ^ 2 * min |(1 + x) * ξ i ω| 1
  let momentSeq : ℕ → Fin n → Ω → ℝ := fun k i ω => ((1 + τ k) * ξ i ω) ^ 2 * min |(1 + τ k) * ξ i ω| 1
  let full : Ω → ℝ := fun ω => A ω + x * B ω
  let fullSeq : ℕ → Ω → ℝ := fun k ω => A ω + τ k * B ω
  let deleted : Fin n → Ω → ℝ := fun i ω => cap i ω * (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)
  let deletedSeq : ℕ → Fin n → Ω → ℝ := fun k i ω => capSeq k i ω * (|A ω - Adelete i ω| + τ k * |B ω - Bdelete i ω|)
  let δcompact : Fin n → ℝ := fun i => ∫ ω, moment i ω ∂ν
  let δcompactSeq : ℕ → Fin n → ℝ := fun k i => ∫ ω, momentSeq k i ω ∂ν
  let Lcompact : ℝ := ∑ i : Fin n, δcompact i
  let LcompactSeq : ℕ → ℝ := fun k => ∑ i : Fin n, δcompactSeq k i
  let compactCost : ℝ := Lcompact + (∫ ω, full ω ∂ν) + ∑ i : Fin n, ∫ ω, deleted i ω ∂ν
  let compactCostSeq : ℕ → ℝ := fun k => LcompactSeq k + (∫ ω, fullSeq k ω ∂ν) + ∑ i : Fin n, ∫ ω, deletedSeq k i ω ∂ν
  have hqpos : 0 < 1 + x := by linarith
  have hqnonneg : 0 ≤ 1 + x := le_of_lt hqpos
  have hτpos (k : ℕ) : 0 < 1 + τ k := by linarith [(hτbounds k).1]
  have hcapm (i : Fin n) : Measurable (cap i) :=
    (continuous_abs.measurable.comp (hξ i)).min measurable_const
  have hcapSeqm (k : ℕ) (i : Fin n) : Measurable (capSeq k i) :=
    (continuous_abs.measurable.comp (hξ i)).min measurable_const
  have hcap0 (i : Fin n) (ω : Ω) : 0 ≤ cap i ω :=
    le_min (abs_nonneg _) (le_of_lt (inv_pos.mpr hqpos))
  have hcapSeq0 (k : ℕ) (i : Fin n) (ω : Ω) : 0 ≤ capSeq k i ω :=
    le_min (abs_nonneg _) (le_of_lt (inv_pos.mpr (hτpos k)))
  have hcapBound (k : ℕ) (i : Fin n) (ω : Ω) :
      capSeq k i ω ≤ (1 + x) * cap i ω := by
    dsimp only [capSeq, cap]
    by_cases ha : |ξ i ω| ≤ (1 + x)⁻¹
    · rw [min_eq_left ha]
      calc
        min |ξ i ω| (1 + τ k)⁻¹ ≤ |ξ i ω| := min_le_left _ _
        _ ≤ (1 + x) * |ξ i ω| := by
          nlinarith [mul_nonneg hx (abs_nonneg (ξ i ω))]
    · rw [min_eq_right (le_of_not_ge ha)]
      calc
        min |ξ i ω| (1 + τ k)⁻¹ ≤ (1 + τ k)⁻¹ := min_le_right _ _
        _ ≤ 1 := by
          have hinv0 : 0 ≤ (1 + τ k)⁻¹ := le_of_lt (inv_pos.mpr (hτpos k))
          have hinvEq : (1 + τ k) * (1 + τ k)⁻¹ = 1 :=
            mul_inv_cancel₀ (hτpos k).ne'
          nlinarith [mul_nonneg (hτbounds k).1 hinv0]
        _ = (1 + x) * (1 + x)⁻¹ := by rw [mul_inv_cancel₀ hqpos.ne']
  have hfullm : Measurable full := hA.add (measurable_const.mul hB)
  have hfullSeqm (k : ℕ) : Measurable (fullSeq k) :=
    hA.add (measurable_const.mul hB)
  have hdeletedm (i : Fin n) : Measurable (deleted i) :=
    (hcapm i).mul ((continuous_abs.measurable.comp (hA.sub (hAdelete i))).add
      (measurable_const.mul (continuous_abs.measurable.comp (hB.sub (hBdelete i)))))
  have hdeletedSeqm (k : ℕ) (i : Fin n) : Measurable (deletedSeq k i) :=
    (hcapSeqm k i).mul ((continuous_abs.measurable.comp (hA.sub (hAdelete i))).add
      (measurable_const.mul (continuous_abs.measurable.comp (hB.sub (hBdelete i)))))
  have hfullI : Integrable full ν := hFull
  have hdeletedI (i : Fin n) : Integrable (deleted i) ν := hDeleted i
  have hfull0 : ∀ᵐ ω ∂ν, 0 ≤ full ω := by
    filter_upwards [hAnonneg, hBnonneg] with ω ha hb
    exact add_nonneg ha (mul_nonneg hx hb)
  have hfullSeqBounds (k : ℕ) :
      ∀ᵐ ω ∂ν, 0 ≤ fullSeq k ω ∧ fullSeq k ω ≤ full ω := by
    filter_upwards [hAnonneg, hBnonneg] with ω ha hb
    constructor
    · exact add_nonneg ha (mul_nonneg (hτbounds k).1 hb)
    · dsimp only [fullSeq, full]
      nlinarith [mul_nonneg (sub_nonneg.mpr (hτbounds k).2) hb]
  have hdeleted0 (i : Fin n) (ω : Ω) : 0 ≤ deleted i ω :=
    mul_nonneg (hcap0 i ω)
      (add_nonneg (abs_nonneg _) (mul_nonneg hx (abs_nonneg _)))
  have hdeletedSeqBounds (k : ℕ) (i : Fin n) (ω : Ω) :
      0 ≤ deletedSeq k i ω ∧ deletedSeq k i ω ≤ (1 + x) * deleted i ω := by
    have hp0 : 0 ≤ |A ω - Adelete i ω| + τ k * |B ω - Bdelete i ω| :=
      add_nonneg (abs_nonneg _) (mul_nonneg (hτbounds k).1 (abs_nonneg _))
    have hpLe : |A ω - Adelete i ω| + τ k * |B ω - Bdelete i ω| ≤
        |A ω - Adelete i ω| + x * |B ω - Bdelete i ω| := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (hτbounds k).2)
        (abs_nonneg (B ω - Bdelete i ω))]
    refine ⟨mul_nonneg (hcapSeq0 k i ω) hp0, ?_⟩
    dsimp only [deletedSeq, deleted]
    calc
      capSeq k i ω * (|A ω - Adelete i ω| + τ k * |B ω - Bdelete i ω|) ≤
          ((1 + x) * cap i ω) *
            (|A ω - Adelete i ω| + τ k * |B ω - Bdelete i ω|) :=
        mul_le_mul_of_nonneg_right (hcapBound k i ω) hp0
      _ ≤ ((1 + x) * cap i ω) *
          (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|) :=
        mul_le_mul_of_nonneg_left hpLe (mul_nonneg hqnonneg (hcap0 i ω))
      _ = (1 + x) *
          (cap i ω * (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)) := by ring
  have hfullSeqI (k : ℕ) : Integrable (fullSeq k) ν := by
    apply hfullI.mono' (hfullSeqm k).aestronglyMeasurable
    filter_upwards [hfullSeqBounds k] with ω h
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2
  have hdeletedSeqI (k : ℕ) (i : Fin n) : Integrable (deletedSeq k i) ν := by
    apply ((hdeletedI i).const_mul (1 + x)).mono'
      (hdeletedSeqm k i).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hdeletedSeqBounds k i ω).1]
      exact (hdeletedSeqBounds k i ω).2
  have hmomentMeas (t : ℝ) (i : Fin n) : Measurable (fun ω : Ω =>
      ((1 + t) * ξ i ω) ^ 2 * min |(1 + t) * ξ i ω| 1) := by
    have hu : Measurable (fun ω : Ω => (1 + t) * ξ i ω) :=
      measurable_const.mul (hξ i)
    exact (hu.pow_const 2).mul
      ((continuous_abs.measurable.comp hu).min measurable_const)
  have hmomentBounds (t : ℝ) (ht0 : 0 ≤ t) (htx : t ≤ x)
      (i : Fin n) (ω : Ω) :
      0 ≤ ((1 + t) * ξ i ω) ^ 2 * min |(1 + t) * ξ i ω| 1 ∧
      ((1 + t) * ξ i ω) ^ 2 * min |(1 + t) * ξ i ω| 1 ≤
        (1 + x) ^ 2 * (ξ i ω) ^ 2 := by
    have hscale : (1 + t) ^ 2 ≤ (1 + x) ^ 2 := by
      have hs0 : 0 ≤ 2 + x + t := by linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr htx) hs0]
    refine ⟨mul_nonneg (sq_nonneg _) (le_min (abs_nonneg _) (by norm_num)), ?_⟩
    calc
      ((1 + t) * ξ i ω) ^ 2 * min |(1 + t) * ξ i ω| 1 ≤
          ((1 + t) * ξ i ω) ^ 2 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (min_le_right |(1 + t) * ξ i ω| 1) (sq_nonneg ((1 + t) * ξ i ω))
      _ = (1 + t) ^ 2 * (ξ i ω) ^ 2 := mul_pow _ _ _
      _ ≤ (1 + x) ^ 2 * (ξ i ω) ^ 2 :=
        mul_le_mul_of_nonneg_right hscale (sq_nonneg _)
  have hmomentI (t : ℝ) (ht0 : 0 ≤ t) (htx : t ≤ x) (i : Fin n) :
      Integrable (fun ω : Ω =>
        ((1 + t) * ξ i ω) ^ 2 * min |(1 + t) * ξ i ω| 1) ν := by
    apply ((hξ2 i).integrable_sq.const_mul ((1 + x) ^ 2)).mono'
      (hmomentMeas t i).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hmomentBounds t ht0 htx i ω).1]
      exact (hmomentBounds t ht0 htx i ω).2
  have hmomentRefI (i : Fin n) : Integrable (moment i) ν :=
    hmomentI x hx le_rfl i
  have hmomentSeqI (k : ℕ) (i : Fin n) : Integrable (momentSeq k i) ν :=
    hmomentI (τ k) (hτbounds k).1 (hτbounds k).2 i
  have hOneLimit : Filter.Tendsto (fun k : ℕ => 1 + τ k)
      Filter.atTop (nhds (1 + x)) :=
    tendsto_const_nhds.add hτlimit
  have hInvLimit : Filter.Tendsto (fun k : ℕ => (1 + τ k)⁻¹)
      Filter.atTop (nhds ((1 + x)⁻¹)) :=
    hOneLimit.inv₀ hqpos.ne'
  have hcapLimit (i : Fin n) (ω : Ω) :
      Filter.Tendsto (fun k : ℕ => capSeq k i ω) Filter.atTop (nhds (cap i ω)) :=
    tendsto_const_nhds.min hInvLimit
  have hfullLimit (ω : Ω) :
      Filter.Tendsto (fun k : ℕ => fullSeq k ω) Filter.atTop (nhds (full ω)) := by
    change Filter.Tendsto (fun k : ℕ => A ω + τ k * B ω)
      Filter.atTop (nhds (A ω + x * B ω))
    exact tendsto_const_nhds.add (hτlimit.mul tendsto_const_nhds)
  have hdeletedLimit (i : Fin n) (ω : Ω) :
      Filter.Tendsto (fun k : ℕ => deletedSeq k i ω)
        Filter.atTop (nhds (deleted i ω)) := by
    have hp : Filter.Tendsto (fun k : ℕ =>
        |A ω - Adelete i ω| + τ k * |B ω - Bdelete i ω|)
        Filter.atTop (nhds (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)) :=
      tendsto_const_nhds.add (hτlimit.mul tendsto_const_nhds)
    exact (hcapLimit i ω).mul hp
  have hmomentLimit (i : Fin n) (ω : Ω) :
      Filter.Tendsto (fun k : ℕ => momentSeq k i ω)
        Filter.atTop (nhds (moment i ω)) := by
    have hu : Filter.Tendsto (fun k : ℕ => (1 + τ k) * ξ i ω)
        Filter.atTop (nhds ((1 + x) * ξ i ω)) :=
      hOneLimit.mul tendsto_const_nhds
    exact (hu.pow 2).mul (hu.abs.min tendsto_const_nhds)
  have hfullRaw : Filter.Tendsto (fun k : ℕ => ∫ ω, fullSeq k ω ∂ν)
      Filter.atTop (nhds (∫ ω, full ω ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (μ := ν)
      (F := fullSeq) (f := full) full
      (fun k => (hfullSeqm k).aestronglyMeasurable) hfullI
    · intro k
      filter_upwards [hfullSeqBounds k] with ω h
      rw [Real.norm_eq_abs, abs_of_nonneg h.1]
      exact h.2
    · exact Filter.Eventually.of_forall hfullLimit
  have hdeletedRaw (i : Fin n) :
      Filter.Tendsto (fun k : ℕ => ∫ ω, deletedSeq k i ω ∂ν)
        Filter.atTop (nhds (∫ ω, deleted i ω ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (μ := ν)
      (F := fun k => deletedSeq k i) (f := deleted i)
      (fun ω => (1 + x) * deleted i ω)
      (fun k => (hdeletedSeqm k i).aestronglyMeasurable)
      ((hdeletedI i).const_mul (1 + x))
    · intro k
      exact Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hdeletedSeqBounds k i ω).1]
        exact (hdeletedSeqBounds k i ω).2
    · exact Filter.Eventually.of_forall (hdeletedLimit i)
  have hδLimit (i : Fin n) :
      Filter.Tendsto (fun k : ℕ => δcompactSeq k i)
        Filter.atTop (nhds (δcompact i)) := by
    apply tendsto_integral_of_dominated_convergence (μ := ν)
      (F := fun k => momentSeq k i) (f := moment i)
      (fun ω => (1 + x) ^ 2 * (ξ i ω) ^ 2)
      (fun k => (hmomentMeas (τ k) i).aestronglyMeasurable)
      ((hξ2 i).integrable_sq.const_mul ((1 + x) ^ 2))
    · intro k
      exact Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (hmomentBounds (τ k) (hτbounds k).1 (hτbounds k).2 i ω).1]
        exact (hmomentBounds (τ k) (hτbounds k).1 (hτbounds k).2 i ω).2
    · exact Filter.Eventually.of_forall (hmomentLimit i)
  have herrorLimit (f : Ω → ℝ) (F : ℕ → Ω → ℝ) (bound : Ω → ℝ)
      (hfm : Measurable f) (hFm : ∀ k : ℕ, Measurable (F k))
      (hbI : Integrable bound ν)
      (hdom : ∀ k : ℕ, ∀ᵐ ω ∂ν, ‖|F k ω - f ω|‖ ≤ bound ω)
      (hp : ∀ ω : Ω, Filter.Tendsto (fun k : ℕ => F k ω)
        Filter.atTop (nhds (f ω))) :
      Filter.Tendsto (fun k : ℕ => ∫ ω, |F k ω - f ω| ∂ν)
        Filter.atTop (nhds (0 : ℝ)) := by
    have hz (ω : Ω) : Filter.Tendsto (fun k : ℕ => |F k ω - f ω|)
        Filter.atTop (nhds (0 : ℝ)) := by
      have hs : Filter.Tendsto (fun k : ℕ => F k ω - f ω)
          Filter.atTop (nhds (f ω - f ω)) :=
        (hp ω).sub tendsto_const_nhds
      simpa only [sub_self, abs_zero] using hs.abs
    have herr := tendsto_integral_of_dominated_convergence (μ := ν)
      (F := fun k ω => |F k ω - f ω|) (f := fun _ : Ω => (0 : ℝ)) bound
      (fun k => (continuous_abs.measurable.comp ((hFm k).sub hfm)).aestronglyMeasurable)
      hbI hdom (Filter.Eventually.of_forall hz)
    simpa only [integral_zero] using herr
  have hfullError : Filter.Tendsto (fun k : ℕ => ∫ ω, |fullSeq k ω - full ω| ∂ν)
      Filter.atTop (nhds (0 : ℝ)) := by
    apply herrorLimit full fullSeq full hfullm hfullSeqm hfullI
    · intro k
      filter_upwards [hfullSeqBounds k] with ω h
      rw [Real.norm_eq_abs, abs_abs, abs_of_nonpos (sub_nonpos.mpr h.2)]
      linarith [h.1]
    · exact hfullLimit
  have hdeletedError (i : Fin n) :
      Filter.Tendsto (fun k : ℕ => ∫ ω, |deletedSeq k i ω - deleted i ω| ∂ν)
        Filter.atTop (nhds (0 : ℝ)) := by
    apply herrorLimit (deleted i) (fun k => deletedSeq k i)
      (fun ω => ((1 + x) + 1) * deleted i ω) (hdeletedm i)
      (fun k => hdeletedSeqm k i) ((hdeletedI i).const_mul ((1 + x) + 1))
    · intro k
      exact Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_abs]
        apply abs_le.mpr
        constructor
        · nlinarith [(hdeletedSeqBounds k i ω).1,
            mul_nonneg hqnonneg (hdeleted0 i ω)]
        · nlinarith [(hdeletedSeqBounds k i ω).2, hdeleted0 i ω]
    · exact hdeletedLimit i
  have hL : Filter.Tendsto LcompactSeq Filter.atTop (nhds Lcompact) := by
    dsimp only [LcompactSeq, Lcompact]
    exact tendsto_finsetSum Finset.univ (fun i _ => hδLimit i)
  have hDeletedSum : Filter.Tendsto
      (fun k : ℕ => ∑ i : Fin n, ∫ ω, deletedSeq k i ω ∂ν)
      Filter.atTop (nhds (∑ i : Fin n, ∫ ω, deleted i ω ∂ν)) :=
    tendsto_finsetSum Finset.univ (fun i _ => hdeletedRaw i)
  have hK : Filter.Tendsto compactCostSeq Filter.atTop (nhds compactCost) :=
    (hL.add hfullRaw).add hDeletedSum
  refine ⟨hmomentRefI, ?_, hfullError, hdeletedError, hδLimit,
    hfullRaw, hdeletedRaw, hL, hK⟩
  intro k
  exact ⟨hfullSeqI k, fun i => ⟨hdeletedSeqI k i, hmomentSeqI k i⟩⟩
end

end Shao.OQ6.CompactCostParameterLimits
