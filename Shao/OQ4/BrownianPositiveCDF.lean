import Shao.Probability.BrownianSup
import Shao.Probability.BrownianFirstTerm
import Shao.OQ4.BrownianSurvivalBoundary
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

-- Complete local implementation of the parent-frozen proposal; no Lean check yet.
noncomputable section
namespace Shao.OQ4.BrownianPositiveCDF
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
set_option autoImplicit false
variable {Ω : Type*} [MeasurableSpace Ω]

private def scaledProcess (B : ℝ≥0 → Ω → ℝ) (c : ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun t ω => (Real.sqrt (c : ℝ))⁻¹ * B (c * t) ω

private theorem isBrownian_scaledProcess
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : IsBrownianReal B P) (c : ℝ≥0) (hc : 0 < c) :
    IsBrownianReal (scaledProcess B c) P := by
  change IsBrownianReal (fun t ω => (Real.sqrt (c : ℝ))⁻¹ * B (c * t) ω) P
  exact hB.smul (ne_of_gt hc)

private theorem time_change_bijection (c : ℝ≥0) (hc : 0 < c) :
    (fun t : ℝ≥0 => c * t) '' Icc 0 c⁻¹ = Icc 0 1 := by
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨bot_le, (mul_le_mul_of_nonneg_left ht.2 (bot_le : 0 ≤ c)).trans_eq
      (mul_inv_cancel₀ (ne_of_gt hc))⟩
  · intro hs
    refine ⟨c⁻¹ * s, ⟨bot_le, ?_⟩, ?_⟩
    · simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hs.2 (show (0 : ℝ≥0) ≤ c⁻¹ from bot_le)
    · simp only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul]

private theorem rawSup_scaled_level
    (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (hc : Continuous (B · ω))
    (x : ℝ) (hx : 0 < x) :
    BrownianSurvivalBoundary.pathSup
      (scaledProcess B (Real.toNNReal (x ^ 2)))
      (Real.toNNReal (x ^ 2))⁻¹ 0 ω =
        Shao.Probability.BrownianSup.pathSup B ω / x := by
  let c : ℝ≥0 := Real.toNNReal (x ^ 2)
  have hcpos : 0 < c := Real.toNNReal_pos.mpr (sq_pos_of_pos hx)
  have hsqrt : Real.sqrt (c : ℝ) = x := by
    simp only [c, Real.coe_toNNReal _ (sq_nonneg x), Real.sqrt_sq_eq_abs, abs_of_pos hx]
  have hval (t : ℝ≥0) :
      |0 + scaledProcess B c t ω| = |B (c * t) ω| / x := by
    simp only [scaledProcess, zero_add, hsqrt, abs_mul, abs_inv, abs_of_pos hx,
      div_eq_mul_inv]
    ring
  have hcont : Continuous (fun t : ℝ≥0 => |B t ω|) := hc.abs
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ≥0) 1).Nonempty from ⟨0, by simp⟩) hcont.continuousOn
  have hb : BddAbove ((fun t : ℝ≥0 => |B t ω|) '' Icc 0 1) :=
    (isCompact_Icc.image hcont).bddAbove
  have hsup : Shao.Probability.BrownianSup.pathSup B ω = |B s ω| := by
    apply le_antisymm
    · apply csSup_le
      · exact ⟨_, ⟨s, hs, rfl⟩⟩
      · rintro _ ⟨t, ht, rfl⟩
        exact hmax ht
    · exact le_csSup hb ⟨s, hs, rfl⟩
  have hbound (t : ℝ≥0) (ht : t ∈ Icc 0 c⁻¹) :
      |0 + scaledProcess B c t ω| ≤ |B s ω| / x := by
    rw [hval]
    have hct : c * t ∈ Icc (0 : ℝ≥0) 1 := by
      rw [← time_change_bijection c hcpos]
      exact mem_image_of_mem _ ht
    exact div_le_div_of_nonneg_right (hmax hct) hx.le
  have hpre : c⁻¹ * s ∈ Icc (0 : ℝ≥0) c⁻¹ := by
    exact ⟨bot_le, by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hs.2 (show (0 : ℝ≥0) ≤ c⁻¹ from bot_le)⟩
  have hatt : |0 + scaledProcess B c (c⁻¹ * s) ω| = |B s ω| / x := by
    rw [hval]
    simp only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcpos), one_mul]
  rw [hsup]
  change sSup ((fun t : ℝ≥0 => |0 + scaledProcess B c t ω|) '' Icc 0 c⁻¹) = _
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, ⟨c⁻¹ * s, hpre, rfl⟩⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact hbound t ht
  · rw [← hatt]
    exact le_csSup ⟨|B s ω| / x, by
      rintro _ ⟨t, ht, rfl⟩
      exact hbound t ht⟩ ⟨c⁻¹ * s, hpre, rfl⟩

private theorem cdf_continuousAt_of_null_atom
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z) (x : ℝ)
    (hAtom : P {ω | Z ω = x} = 0) :
    ContinuousAt (fun y : ℝ => P.real {ω | Z ω ≤ y}) x := by
  classical
  let I : ℝ → Ω → ℝ := fun y => {ω | Z ω ≤ y}.indicator (fun _ => 1)
  have hm (y : ℝ) : AEStronglyMeasurable (I y) P :=
    (measurable_const.indicator (measurableSet_le hZ measurable_const)).aestronglyMeasurable
  have hb : ∃ C : ℝ, ∀ᶠ y in 𝓝 x, ∀ᵐ ω ∂P, ‖I y ω‖ ≤ C := by
    refine ⟨1, Eventually.of_forall fun y => ae_of_all _ fun ω => ?_⟩
    by_cases h : Z ω ≤ y <;> simp [I, h]
  have hne : ∀ᵐ ω ∂P, Z ω ≠ x := by
    rw [ae_iff]
    simpa only [not_not] using hAtom
  have hl : ∀ᵐ ω ∂P, Tendsto (fun y : ℝ => I y ω) (𝓝 x) (𝓝 (I x ω)) := by
    filter_upwards [hne] with ω hω
    by_cases hlt : Z ω < x
    · have heq : (fun _ : ℝ => I x ω) =ᶠ[𝓝 x] fun y => I y ω := by
        filter_upwards [eventually_gt_nhds hlt] with y hy
        simp [I, hlt.le, hy.le]
      exact tendsto_const_nhds.congr' heq
    · have hxlt : x < Z ω := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hω)
      have heq : (fun _ : ℝ => I x ω) =ᶠ[𝓝 x] fun y => I y ω := by
        filter_upwards [eventually_lt_nhds hxlt] with y hy
        simp [I, not_le.mpr hxlt, not_le.mpr hy]
      exact tendsto_const_nhds.congr' heq
  have hlim := tendsto_integral_filter_of_norm_le_const
    (Eventually.of_forall hm) hb hl
  have hi (y : ℝ) : (∫ ω, I y ω ∂P) = P.real {ω | Z ω ≤ y} := by
    change (∫ ω, {ω | Z ω ≤ y}.indicator (1 : Ω → ℝ) ω ∂P) = _
    exact integral_indicator_one (μ := P) (measurableSet_le hZ measurable_const)
  change Tendsto (fun y : ℝ => P.real {ω | Z ω ≤ y}) (𝓝 x)
    (𝓝 (P.real {ω | Z ω ≤ x}))
  simpa only [hi] using hlim

theorem measure_U_eq_zero
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (x : ℝ) (hx : 0 < x) :
    P {ω | Shao.Probability.BrownianSup.U B P hB ω = x} = 0 := by
  let c : ℝ≥0 := Real.toNNReal (x ^ 2)
  have hc : 0 < c := Real.toNNReal_pos.mpr (sq_pos_of_pos hx)
  have hC := isBrownian_scaledProcess B P hB c hc
  have heq : {ω | Shao.Probability.BrownianSup.U B P hB ω = x} =ᵐ[P]
      {ω | BrownianSurvivalBoundary.pathSup (scaledProcess B c) c⁻¹ 0 ω = 1} := by
    filter_upwards [hB.cont, Shao.Probability.BrownianSup.U_ae_eq_pathSup B P hB]
      with ω hcont hU
    apply propext
    change Shao.Probability.BrownianSup.U B P hB ω = x ↔ _
    rw [show BrownianSurvivalBoundary.pathSup (scaledProcess B c) c⁻¹ 0 ω =
      Shao.Probability.BrownianSup.pathSup B ω / x from
        rawSup_scaled_level B ω hcont x hx, ← hU]
    constructor
    · intro h
      rw [h]
      exact div_self (ne_of_gt hx)
    · intro h
      have hh := (div_eq_iff (ne_of_gt hx)).mp h
      simpa only [one_mul] using hh
  exact (measure_congr heq).trans
    (BrownianSurvivalBoundary.measure_pathSup_eq_one_eq_zero
      (scaledProcess B c) P hC c⁻¹ (inv_pos.mpr hc) 0 (by norm_num))

theorem probability_mono
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    Monotone (Shao.Probability.BrownianSup.probability B P hB) := by
  intro x y hxy
  change P.real {ω | Shao.Probability.BrownianSup.U B P hB ω ≤ x} ≤
    P.real {ω | Shao.Probability.BrownianSup.U B P hB ω ≤ y}
  exact measureReal_mono (fun ω hω => hω.trans hxy)

theorem probability_continuousAt
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (x : ℝ) (hx : 0 < x) :
    ContinuousAt (Shao.Probability.BrownianSup.probability B P hB) x := by
  exact cdf_continuousAt_of_null_atom P (Shao.Probability.BrownianSup.U B P hB)
    (Shao.Probability.BrownianSup.measurable_U B P hB) x
    (measure_U_eq_zero B P hB x hx)

theorem probability_tendsto
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (r : ℕ → ℝ) (x : ℝ) (hx : 0 < x)
    (hr : Tendsto r atTop (𝓝 x)) :
    Tendsto (fun j => Shao.Probability.BrownianSup.probability B P hB (r j))
      atTop (𝓝 (Shao.Probability.BrownianSup.probability B P hB x)) := by
  exact (probability_continuousAt B P hB x hx).tendsto.comp hr

theorem probability_pos
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (x : ℝ) (hx : 0 < x) :
    0 < Shao.Probability.BrownianSup.probability B P hB x := by
  obtain ⟨δ, hδ, hp⟩ :=
    Shao.Probability.BrownianSup.actual_brownian_eventually_positive B P hB
  let y : ℝ := min x δ / 2
  have hy : 0 < y := div_pos (lt_min hx hδ) (by norm_num)
  have hyδ : y < δ := by
    have hm := min_le_right x δ
    dsimp [y]
    linarith
  have hyx : y ≤ x := by
    have hm := min_le_left x δ
    dsimp [y]
    linarith
  exact (hp y hy hyδ).1.trans_le (probability_mono B P hB hyx)

private theorem closedSurvival_eq_scaled_fullStrip
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (hT : 0 < T) :
    BrownianSurvivalBoundary.closedSurvival B T 0 =
      Shao.Probability.BrownianSup.fullStrip (scaledProcess B T)
        (1 / Real.sqrt (T : ℝ)) := by
  have hs : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr (NNReal.coe_pos.mpr hT)
  have hv (t : ℝ≥0) (ω : Ω) :
      |scaledProcess B T t ω| = |B (T * t) ω| / Real.sqrt (T : ℝ) := by
    simp only [scaledProcess, abs_mul, abs_inv, abs_of_pos hs, div_eq_mul_inv]
    ring
  ext ω
  change (∀ t : ℝ≥0, t ≤ T → |0 + B t ω| ≤ 1) ↔
    ∀ t ∈ Icc (0 : ℝ≥0) 1, |scaledProcess B T t ω| ≤ 1 / Real.sqrt (T : ℝ)
  constructor
  · intro h t ht
    rw [hv]
    apply div_le_div_of_nonneg_right _ hs.le
    simpa only [zero_add] using h (T * t)
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 (bot_le : 0 ≤ T))
  · intro h t ht
    have hsTime : t / T ∈ Icc (0 : ℝ≥0) 1 :=
      ⟨bot_le, (div_le_one hT).mpr ht⟩
    have htime : T * (t / T) = t := by field_simp [ne_of_gt hT]
    have hh := h (t / T) hsTime
    rw [hv, htime] at hh
    simpa only [zero_add] using (div_le_div_iff_of_pos_right hs).mp hh

theorem survival_time_eq_probability
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (hT : 0 < T) :
    P.real (BrownianSurvivalBoundary.closedSurvival B T 0) =
      Shao.Probability.BrownianSup.probability B P hB (1 / Real.sqrt (T : ℝ)) := by
  have hC := isBrownian_scaledProcess B P hB T hT
  rw [closedSurvival_eq_scaled_fullStrip B T hT,
    ← Shao.Probability.BrownianSup.probability_eq_fullStrip (scaledProcess B T) P hC]
  exact Shao.Probability.BrownianSup.probability_eq_probability
    (scaledProcess B T) P B P hC hB _

end Shao.OQ4.BrownianPositiveCDF
end
