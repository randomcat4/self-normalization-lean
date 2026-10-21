import Shao.OQ4.CosineCoefficients
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# One-step killed cosine residual

The interval is closed and killing occurs only on strict exit.  These are the
frozen finite R1--R2 inputs; no long-time killed-kernel estimate is asserted.
-/

namespace Shao.OQ4

open MeasureTheory

/-- One step of the cosine observable, retaining both endpoints of the interval. -/
noncomputable def Kcos (ν : Measure ℝ) (a h z : ℝ) : ℝ :=
  ∫ y, if |z + y| ≤ h then Real.cos (a * (z + y)) else 0 ∂ν

/-- The ordinary, un-killed one-step cosine coefficient. -/
noncomputable def cosineCoefficient (ν : Measure ℝ) (a : ℝ) : ℝ :=
  ∫ y, Real.cos (a * y) ∂ν

/-- The ordinary, un-killed one-step sine coefficient. -/
noncomputable def sineCoefficient (ν : Measure ℝ) (a : ℝ) : ℝ :=
  ∫ y, Real.sin (a * y) ∂ν

/-- The strict-exit set integral equals its pointwise zero-on-survival form. -/
theorem integral_strict_exit_cosine_eq (ν : Measure ℝ) (a h z : ℝ) :
    (∫ y in {y : ℝ | h < |z + y|}, Real.cos (a * (z + y)) ∂ν) =
      ∫ y, if |z + y| ≤ h then 0 else Real.cos (a * (z + y)) ∂ν := by
  have hs : MeasurableSet {y : ℝ | h < |z + y|} :=
    measurableSet_lt measurable_const (by fun_prop)
  rw [← integral_indicator hs]
  congr 1
  funext y
  by_cases hy : |z + y| ≤ h
  · simp only [Set.indicator, Set.mem_ofPred_eq, not_lt.mpr hy, ite_false, hy, ite_true]
  · simp only [Set.indicator, Set.mem_ofPred_eq, lt_of_not_ge hy, ite_true, hy, ite_false]

/-- Exact ordinary cosine addition and strict-exit subtraction, at any real a,h,z. -/
theorem killed_cosine_identity (ν : Measure ℝ) [IsProbabilityMeasure ν] (a h z : ℝ) :
    Kcos ν a h z - cosineCoefficient ν a * Real.cos (a * z) =
      -sineCoefficient ν a * Real.sin (a * z) -
        ∫ y in {y : ℝ | h < |z + y|}, Real.cos (a * (z + y)) ∂ν := by
  have hfull : Integrable (fun y : ℝ => Real.cos (a * (z + y))) ν := by
    refine Integrable.of_bound (by fun_prop : Measurable
      (fun y : ℝ => Real.cos (a * (z + y)))).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun y => by
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (a * (z + y))
  have hc : Integrable (fun y : ℝ => Real.cos (a * y)) ν := by
    refine Integrable.of_bound (by fun_prop : Measurable
      (fun y : ℝ => Real.cos (a * y))).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun y => by
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (a * y)
  have hs : Integrable (fun y : ℝ => Real.sin (a * y)) ν := by
    refine Integrable.of_bound (by fun_prop : Measurable
      (fun y : ℝ => Real.sin (a * y))).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun y => by
      simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (a * y)
  have hclosed : MeasurableSet {y : ℝ | |z + y| ≤ h} :=
    measurableSet_le (by fun_prop) measurable_const
  have hinside : Integrable
      (fun y : ℝ => if |z + y| ≤ h then Real.cos (a * (z + y)) else 0) ν := by
    have heq : ({y : ℝ | |z + y| ≤ h}.indicator
        (fun y => Real.cos (a * (z + y)))) =
        (fun y : ℝ => if |z + y| ≤ h then Real.cos (a * (z + y)) else 0) := by
      funext y
      simp only [Set.indicator, Set.mem_ofPred_eq]
    rw [← heq]
    exact hfull.indicator hclosed
  have hexit : Integrable
      (fun y : ℝ => if |z + y| ≤ h then 0 else Real.cos (a * (z + y))) ν := by
    have heq : (fun y : ℝ => if |z + y| ≤ h then 0 else Real.cos (a * (z + y))) =
        (fun y : ℝ => Real.cos (a * (z + y)) -
          (if |z + y| ≤ h then Real.cos (a * (z + y)) else 0)) := by
      funext y
      by_cases hy : |z + y| ≤ h <;> simp only [hy, ite_true, ite_false, sub_self, sub_zero]
    rw [heq]
    exact hfull.sub hinside
  have hsplit : (∫ y, Real.cos (a * (z + y)) ∂ν) = Kcos ν a h z +
      ∫ y in {y : ℝ | h < |z + y|}, Real.cos (a * (z + y)) ∂ν := by
    rw [integral_strict_exit_cosine_eq, Kcos, ← integral_add hinside hexit]
    congr 1
    funext y
    by_cases hy : |z + y| ≤ h <;> simp only [hy, ite_true, ite_false, add_zero, zero_add]
  have hfree : (∫ y, Real.cos (a * (z + y)) ∂ν) =
      Real.cos (a * z) * cosineCoefficient ν a - Real.sin (a * z) * sineCoefficient ν a := by
    simp_rw [mul_add, Real.cos_add]
    rw [integral_sub (hc.const_mul _) (hs.const_mul _), integral_const_mul, integral_const_mul]
    rfl
  nlinarith only [hsplit, hfree]

/-- Every strict exit is paid by the full positive overshoot, even for arbitrarily large jumps. -/
theorem killed_cosine_boundary_bound (h z y : ℝ) (hh : 0 < h) (_hz : |z| ≤ h) :
    |if |z + y| ≤ h then 0 else Real.cos ((Real.pi / (2 * h)) * (z + y))| ≤
      (Real.pi / (2 * h)) * max (|y| - (h - |z|)) 0 := by
  let a : ℝ := Real.pi / (2 * h)
  have ha : 0 < a := div_pos Real.pi_pos (by positivity)
  change |if |z + y| ≤ h then 0 else Real.cos (a * (z + y))| ≤
    a * max (|y| - (h - |z|)) 0
  by_cases hy : |z + y| ≤ h
  · rw [ite_eq_left hy, abs_zero]
    exact mul_nonneg ha.le (le_max_right _ _)
  · rw [ite_eq_right hy]
    have hexit : h < |z + y| := lt_of_not_ge hy
    have hah : a * h = Real.pi / 2 := by dsimp only [a]; field_simp
    have hboundary : Real.cos (a * h) = 0 := by rw [hah, Real.cos_pi_div_two]
    have hcosabs : Real.cos (a * |z + y|) = Real.cos (a * (z + y)) := by
      rcases le_total 0 (z + y) with hx | hx
      · rw [abs_of_nonneg hx]
      · rw [abs_of_nonpos hx, mul_neg, Real.cos_neg]
    have hdiff : |a * |z + y| - a * h| = a * (|z + y| - h) := by
      rw [← mul_sub, abs_mul, abs_of_pos ha, abs_of_nonneg (sub_nonneg.mpr hexit.le)]
    have hlip := Real.abs_cos_sub_cos_le (a * |z + y|) (a * h)
    rw [hboundary, sub_zero, hdiff, hcosabs] at hlip
    calc
      |Real.cos (a * (z + y))| ≤ a * (|z + y| - h) := hlip
      _ ≤ a * max (|y| - (h - |z|)) 0 := by
        apply mul_le_mul_of_nonneg_left _ ha.le
        exact (by linarith [abs_add_le z y] : |z + y| - h ≤ |y| - (h - |z|)).trans
          (le_max_left _ _)

/-- The one-step killed cosine residual under the frozen centered unit-variance moment law. -/
theorem killed_cosine_residual_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h z : ℝ) (hh : 0 < h) (hz : |z| ≤ h)
    (hId : Integrable (fun y : ℝ => y) ν)
    (hSq : Integrable (fun y : ℝ => y ^ 2) ν)
    (hCube : Integrable (fun y : ℝ => |y| ^ 3) ν)
    (hmean : (∫ y : ℝ, y ∂ν) = 0)
    (hsecond : (∫ y : ℝ, y ^ 2 ∂ν) = 1) :
    let β : ℝ := ∫ y : ℝ, |y| ^ 3 ∂ν
    Integrable (fun y : ℝ => max (|y| - (h - |z|)) 0) ν ∧
      |Kcos ν (Real.pi / (2 * h)) h z - cosineCoefficient ν (Real.pi / (2 * h)) *
        Real.cos (Real.pi * z / (2 * h))| ≤
        Real.pi ^ 3 * β / (48 * h ^ 3) + (Real.pi / (2 * h)) *
          ∫ y : ℝ, max (|y| - (h - |z|)) 0 ∂ν := by
  dsimp only
  have hd : 0 ≤ h - |z| := sub_nonneg.mpr hz
  have hover : Integrable (fun y : ℝ => max (|y| - (h - |z|)) 0) ν := by
    apply hId.abs.mono' (by fun_prop : Measurable
      (fun y : ℝ => max (|y| - (h - |z|)) 0)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (sub_le_self _ hd) (abs_nonneg y)
  refine ⟨hover, ?_⟩
  let a : ℝ := Real.pi / (2 * h)
  have hη : |sineCoefficient ν a| ≤
      Real.pi ^ 3 * (∫ y : ℝ, |y| ^ 3 ∂ν) / (48 * h ^ 3) := by
    simpa only [sineCoefficient] using
      (cosine_coefficients_h_bound ν (fun y : ℝ => y) h hh hId hSq hCube hmean hsecond).2
  have hexit : |∫ y in {y : ℝ | h < |z + y|}, Real.cos (a * (z + y)) ∂ν| ≤
      a * ∫ y : ℝ, max (|y| - (h - |z|)) 0 ∂ν := by
    rw [integral_strict_exit_cosine_eq]
    calc
      _ ≤ ∫ y : ℝ, a * max (|y| - (h - |z|)) 0 ∂ν := by
        rw [← Real.norm_eq_abs]
        apply norm_integral_le_of_norm_le (hover.const_mul a)
        exact Filter.Eventually.of_forall fun y => by
          simpa only [Real.norm_eq_abs] using killed_cosine_boundary_bound h z y hh hz
      _ = _ := integral_const_mul _ _
  have hsin : |sineCoefficient ν a| * |Real.sin (a * z)| ≤ |sineCoefficient ν a| := by
    calc
      _ ≤ |sineCoefficient ν a| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
      _ = _ := mul_one _
  have haz : a * z = Real.pi * z / (2 * h) := by dsimp only [a]; ring
  rw [← haz]
  calc
    |Kcos ν a h z - cosineCoefficient ν a * Real.cos (a * z)| =
        |-sineCoefficient ν a * Real.sin (a * z) +
          (-(∫ y in {y : ℝ | h < |z + y|}, Real.cos (a * (z + y)) ∂ν))| := by
      rw [killed_cosine_identity]
      rfl
    _ ≤ |-sineCoefficient ν a * Real.sin (a * z)| +
        |-(∫ y in {y : ℝ | h < |z + y|}, Real.cos (a * (z + y)) ∂ν)| := abs_add_le _ _
    _ = |sineCoefficient ν a| * |Real.sin (a * z)| +
        |∫ y in {y : ℝ | h < |z + y|}, Real.cos (a * (z + y)) ∂ν| := by
      simp only [abs_mul, abs_neg]
    _ ≤ |sineCoefficient ν a| +
        |∫ y in {y : ℝ | h < |z + y|}, Real.cos (a * (z + y)) ∂ν| := add_le_add hsin le_rfl
    _ ≤ Real.pi ^ 3 * (∫ y : ℝ, |y| ^ 3 ∂ν) / (48 * h ^ 3) +
        a * ∫ y : ℝ, max (|y| - (h - |z|)) 0 ∂ν := add_le_add hη hexit

end Shao.OQ4
