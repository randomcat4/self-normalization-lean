import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-! The actual source cutoff, test function and unit-frequency Fourier transform. -/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory
open scoped ContDiff

noncomputable def sourceKernelCutoff (q : ℝ) : ℝ :=
  let χ : ContDiffBump (25 / 16 : ℝ) :=
    ⟨23 / 16, 47 / 32, by norm_num, by norm_num⟩
  χ q

private noncomputable def kernelBump : ContDiffBump (25 / 16 : ℝ) :=
  ⟨23 / 16, 47 / 32, by norm_num, by norm_num⟩

theorem sourceKernelCutoff_data :
    ContDiff ℝ ∞ sourceKernelCutoff ∧
      HasCompactSupport sourceKernelCutoff ∧
      (∀ q : ℝ, 0 ≤ sourceKernelCutoff q ∧ sourceKernelCutoff q ≤ 1) ∧
      (∀ q : ℝ, q ∈ Set.Icc (1 / 8 : ℝ) 3 → sourceKernelCutoff q = 1) ∧
      tsupport sourceKernelCutoff ⊆ Set.Ioo (1 / 16 : ℝ) 4 := by
  refine ⟨kernelBump.contDiff, kernelBump.hasCompactSupport,
    fun q => ⟨kernelBump.nonneg, kernelBump.le_one⟩, ?_, ?_⟩
  · intro q hq
    apply kernelBump.one_of_mem_closedBall
    change dist q (25 / 16 : ℝ) ≤ 23 / 16
    rw [Real.dist_eq]
    exact abs_le.mpr ⟨by linarith [hq.1], by linarith [hq.2]⟩
  · intro q hq
    change q ∈ tsupport (kernelBump : ℝ → ℝ) at hq
    rw [kernelBump.tsupport_eq] at hq
    change dist q (25 / 16 : ℝ) ≤ 47 / 32 at hq
    rw [Real.dist_eq] at hq
    have ha := abs_le.mp hq
    constructor <;> linarith [ha.1, ha.2]

noncomputable def sourceFourierTest (y : ℝ) (p : ℝ × ℝ) : ℝ :=
  sourceKernelCutoff p.2 *
    (if |p.1| < y * Real.sqrt p.2 then 1 else 0)

noncomputable def sourceFourierTestTransform (y u v : ℝ) : ℂ :=
  ∫ p : ℝ × ℝ, (sourceFourierTest y p : ℂ) *
    Complex.exp (-(((u * p.1 + v * p.2 : ℝ) : ℂ) * Complex.I))

private lemma test_measurable (y : ℝ) : Measurable (sourceFourierTest y) := by
  let A : Set (ℝ × ℝ) := {p | |p.1| < y * Real.sqrt p.2}
  have hA : MeasurableSet A := (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet
  have hc : Measurable (fun p : ℝ × ℝ => sourceKernelCutoff p.2) :=
    sourceKernelCutoff_data.1.continuous.measurable.comp measurable_snd
  have he : sourceFourierTest y = A.indicator (fun p => sourceKernelCutoff p.2) := by
    funext p
    by_cases h : p ∈ A <;> simp [sourceFourierTest, Set.indicator, A] at h ⊢
  rw [he]
  exact hc.indicator hA

private lemma test_norm_le_one (y : ℝ) (p : ℝ × ℝ) : ‖sourceFourierTest y p‖ ≤ 1 := by
  unfold sourceFourierTest
  split_ifs
  · simpa only [mul_one, Real.norm_eq_abs,
      abs_of_nonneg (sourceKernelCutoff_data.2.2.1 p.2).1] using
      (sourceKernelCutoff_data.2.2.1 p.2).2
  · simp

private lemma test_support (y : ℝ) (hy : 0 ≤ y) :
    Function.support (sourceFourierTest y) ⊆
      Set.Icc (-2 * y) (2 * y) ×ˢ Set.Icc (1 / 16 : ℝ) 4 := by
  intro p hp
  have hn : sourceFourierTest y p ≠ 0 := hp
  by_cases hw : |p.1| < y * Real.sqrt p.2
  · have hc : sourceKernelCutoff p.2 ≠ 0 := by
      simpa only [sourceFourierTest, ite_eq_left hw, mul_one] using hn
    have hmem : p.2 ∈ tsupport sourceKernelCutoff := subset_closure hc
    have hq := sourceKernelCutoff_data.2.2.2.2 hmem
    have hs : Real.sqrt p.2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith [hq.2]⟩
    have hwidth : |p.1| ≤ 2 * y := by
      calc
        _ ≤ y * Real.sqrt p.2 := hw.le
        _ ≤ y * 2 := mul_le_mul_of_nonneg_left hs hy
        _ = _ := mul_comm _ _
    have hw' := abs_le.mp hwidth
    exact ⟨⟨by linarith [hw'.1], hw'.2⟩, hq.1.le, hq.2.le⟩
  · simp [sourceFourierTest, hw] at hn

theorem sourceFourierTest_integrable (y : ℝ) (hy : 0 ≤ y) :
    Integrable (sourceFourierTest y) (volume : Measure (ℝ × ℝ)) := by
  let K : Set (ℝ × ℝ) := Set.Icc (-2 * y) (2 * y) ×ˢ Set.Icc (1 / 16 : ℝ) 4
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hi : Integrable (K.indicator (fun _ => (1 : ℝ))) volume :=
    (integrable_indicator_iff hK.measurableSet).mpr (integrableOn_const hK.measure_ne_top)
  refine hi.mono' (test_measurable y).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  by_cases hp : p ∈ K
  · simpa only [Set.indicator_of_mem hp] using test_norm_le_one y p
  · have hzero : sourceFourierTest y p = 0 := by
      by_contra hn
      exact hp (test_support y hy hn)
    simp [Set.indicator_of_notMem hp, hzero]

private noncomputable def negativePhase (t : ℝ) : ℂ :=
  Complex.exp (-((t : ℂ) * Complex.I))

private lemma negativePhase_norm (t : ℝ) : ‖negativePhase t‖ = 1 := by
  simp [negativePhase, Complex.norm_exp, Complex.mul_re]

private lemma negativePhase_continuous : Continuous negativePhase := by
  unfold negativePhase
  fun_prop

private lemma negativePhase_add (s t : ℝ) :
    negativePhase (s + t) = negativePhase s * negativePhase t := by
  unfold negativePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma transform_integrable (y : ℝ) (hy : 0 ≤ y) (u v : ℝ) :
    Integrable (fun p : ℝ × ℝ => (sourceFourierTest y p : ℂ) *
      negativePhase (u * p.1 + v * p.2)) volume := by
  have h := sourceFourierTest_integrable y hy
  refine h.norm.mono' ((h.ofReal (𝕜 := ℂ)).aestronglyMeasurable.mul
    (negativePhase_continuous.comp (by fun_prop)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p => ?_)
  simp only [norm_mul, negativePhase_norm, mul_one, Complex.norm_real]
  exact le_rfl

private lemma interval_phase_integral (a : ℝ) (ha : 0 ≤ a) (u : ℝ) :
    (∫ w in Set.Ioo (-a) a, negativePhase (u * w)) =
      ((if u = 0 then 2 * a else 2 * Real.sin (u * a) / u : ℝ) : ℂ) := by
  change (∫ w, negativePhase (u * w) ∂volume.restrict (Set.Ioo (-a) a)) = _
  rw [restrict_Ioo_eq_restrict_Ioc,
    ← intervalIntegral.integral_of_le (show -a ≤ a by linarith)]
  by_cases hu : u = 0
  · subst u
    simp [negativePhase, two_mul]
  · rw [ite_eq_right hu]
    have hc : (-(u : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hu)) Complex.I_ne_zero
    have he : (fun w : ℝ => negativePhase (u * w)) =
        (fun w : ℝ => Complex.exp ((-(u : ℂ) * Complex.I) * (w : ℂ))) := by
      funext w
      unfold negativePhase
      congr 1
      push_cast
      ring
    rw [he, integral_exp_mul_complex hc]
    have hp : (-(u : ℂ) * Complex.I) * (a : ℂ) = ((-(u * a) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    have hm : (-(u : ℂ) * Complex.I) * ((-a : ℝ) : ℂ) = ((u * a : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hp, hm]
    simp only [Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    field_simp
    ring

private lemma inner_transform (y : ℝ) (hy : 0 ≤ y) (u v r : ℝ) :
    (∫ w : ℝ, (sourceFourierTest y (w, r) : ℂ) *
      negativePhase (u * w + v * r)) =
      ((sourceKernelCutoff r *
        (if u = 0 then 2 * y * Real.sqrt r
          else 2 * Real.sin (u * y * Real.sqrt r) / u) : ℝ) : ℂ) *
          negativePhase (v * r) := by
  let a : ℝ := y * Real.sqrt r
  let b : ℂ := (sourceKernelCutoff r : ℂ) * negativePhase (v * r)
  have ha : 0 ≤ a := mul_nonneg hy (Real.sqrt_nonneg r)
  have he : (fun w : ℝ => (sourceFourierTest y (w, r) : ℂ) *
      negativePhase (u * w + v * r)) =
      (Set.Ioo (-a) a).indicator (fun w => b * negativePhase (u * w)) := by
    funext w
    by_cases hw : |w| < a
    · have hm : w ∈ Set.Ioo (-a) a := abs_lt.mp hw
      simp only [sourceFourierTest, show y * Real.sqrt r = a from rfl,
        ite_eq_left hw, mul_one, Set.indicator_of_mem hm, negativePhase_add]
      dsimp [b]
      ring
    · have hm : w ∉ Set.Ioo (-a) a := fun h => hw (abs_lt.mpr h)
      simp only [sourceFourierTest, show y * Real.sqrt r = a from rfl,
        ite_eq_right hw, mul_zero, Complex.ofReal_zero, zero_mul, Set.indicator_of_notMem hm]
  rw [he, integral_indicator measurableSet_Ioo, integral_const_mul,
    interval_phase_integral a ha u]
  by_cases hu : u = 0
  · simp only [ite_eq_left hu, a, b]
    push_cast
    ring
  · simp only [ite_eq_right hu, a, b]
    push_cast
    ring

theorem sourceFourierTestTransform_eq (y : ℝ) (hy : 0 ≤ y) (u v : ℝ) :
    sourceFourierTestTransform y u v =
      ∫ r : ℝ,
        ((sourceKernelCutoff r *
          (if u = 0 then 2 * y * Real.sqrt r
            else 2 * Real.sin (u * y * Real.sqrt r) / u) : ℝ) : ℂ) *
          Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I)) := by
  change (∫ p : ℝ × ℝ, (sourceFourierTest y p : ℂ) *
    negativePhase (u * p.1 + v * p.2)) = _
  rw [Measure.volume_eq_prod ℝ ℝ]
  rw [integral_prod_symm _ (transform_integrable y hy u v)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun r => inner_transform y hy u v r

end Shao.Probability
