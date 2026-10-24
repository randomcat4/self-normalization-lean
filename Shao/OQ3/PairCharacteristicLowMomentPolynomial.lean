import Shao.OQ3.PairProjectionAbsoluteMoments
import Mathlib.MeasureTheory.Function.L2Space

namespace Shao.OQ3

open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

theorem pair_probability_directional_first_two_moments
    (law : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure law]
    (hL2 : ∀ j : Fin 2, MemLp (fun y : Fin 2 → ℝ => y j) 2 law)
    (hmean : ∀ j : Fin 2, (∫ y : Fin 2 → ℝ, y j ∂law) = 0)
    (hcov : ∀ j k : Fin 2, ProbabilityTheory.covariance
      (fun y : Fin 2 → ℝ => y j) (fun y : Fin 2 → ℝ => y k) law =
        if j = k then 1 else 0) (u v : ℝ) :
    let L : (Fin 2 → ℝ) → ℝ := fun y => u * y 0 + v * y 1
    MemLp L 2 law ∧ Integrable L law ∧
      Integrable (fun y => L y ^ 2) law ∧
      (∫ y, L y ∂law) = 0 ∧
      (∫ y, L y ^ 2 ∂law) = u ^ 2 + v ^ 2 := by
  intro L
  have ha := (hL2 0).const_mul u
  have hb := (hL2 1).const_mul v
  have hLp : MemLp L 2 law := ha.add hb
  have hma : Integrable (fun y : Fin 2 → ℝ => u * y 0) law :=
    ha.integrable (by norm_num)
  have hmb : Integrable (fun y : Fin 2 → ℝ => v * y 1) law :=
    hb.integrable (by norm_num)
  have hfirst : (∫ y, L y ∂law) = 0 := by
    dsimp only [L]
    rw [integral_add hma hmb, integral_const_mul, integral_const_mul,
      hmean 0, hmean 1]
    ring
  have hcovL : ProbabilityTheory.covariance L L law = u ^ 2 + v ^ 2 := by
    change ProbabilityTheory.covariance
      ((fun y : Fin 2 → ℝ => u * y 0) + (fun y : Fin 2 → ℝ => v * y 1))
      ((fun y : Fin 2 → ℝ => u * y 0) + (fun y : Fin 2 → ℝ => v * y 1)) law = _
    rw [covariance_add_left ha hb (ha.add hb), covariance_add_right ha ha hb,
      covariance_add_right hb ha hb]
    norm_num [covariance_const_mul_left, covariance_const_mul_right, hcov]
    <;> ring
  have hsecond : (∫ y, L y ^ 2 ∂law) = u ^ 2 + v ^ 2 := by
    calc
      _ = ProbabilityTheory.covariance L L law := by
        simpa only [Pi.mul_apply, pow_two, hfirst, mul_zero, sub_zero] using
          (covariance_eq_sub hLp hLp).symm
      _ = u ^ 2 + v ^ 2 := hcovL
  exact ⟨hLp, hLp.integrable (by norm_num), hLp.integrable_sq, hfirst, hsecond⟩

theorem pair_probability_degree_four_moment_polynomial
    (law : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure law]
    (hL2 : ∀ j : Fin 2, MemLp (fun y : Fin 2 → ℝ => y j) 2 law)
    (hmean : ∀ j : Fin 2, (∫ y : Fin 2 → ℝ, y j ∂law) = 0)
    (hcov : ∀ j k : Fin 2, ProbabilityTheory.covariance
      (fun y : Fin 2 → ℝ => y j) (fun y : Fin 2 → ℝ => y k) law =
        if j = k then 1 else 0)
    (hI3 : Integrable
      (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3) law)
    (hI4 : Integrable
      (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 4) law) (u v : ℝ) :
    let L : (Fin 2 → ℝ) → ℝ := fun y => u * y 0 + v * y 1
    Integrable (fun y => L y ^ 3) law ∧ Integrable (fun y => L y ^ 4) law ∧
      (∑ j ∈ Finset.range 5, (Complex.I ^ j / (j.factorial : ℂ)) *
        ((∫ y, L y ^ j ∂law : ℝ) : ℂ)) =
      1 - ((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2 -
        Complex.I * ((∫ y, L y ^ 3 ∂law : ℝ) : ℂ) / 6 +
          ((∫ y, L y ^ 4 ∂law : ℝ) : ℂ) / 24 := by
  intro L
  obtain ⟨hLp, hIL, hIL2, hfirst, hsecond⟩ :=
    pair_probability_directional_first_two_moments law hL2 hmean hcov u v
  have hfirstL : (∫ y, L y ∂law) = 0 := hfirst
  have hsecondL : (∫ y, L y ^ 2 ∂law) = u ^ 2 + v ^ 2 := hsecond
  have hcont : Continuous L := by
    dsimp only [L]
    fun_prop
  have hs3 : Integrable (fun y => L y ^ 3) law := by
    apply (integrable_norm_iff (hcont.pow 3).aestronglyMeasurable).mp
    change Integrable (fun y : Fin 2 → ℝ => ‖L y ^ 3‖) law
    simpa only [Real.norm_eq_abs, abs_pow, L] using
      (pair_projection_absolute_moment_bound law 3 hI3 u v).1
  have hs4 : Integrable (fun y => L y ^ 4) law := by
    apply (integrable_norm_iff (hcont.pow 4).aestronglyMeasurable).mp
    change Integrable (fun y : Fin 2 → ℝ => ‖L y ^ 4‖) law
    simpa only [Real.norm_eq_abs, abs_pow, L] using
      (pair_projection_absolute_moment_bound law 4 hI4 u v).1
  have hzero : (∫ y, L y ^ 0 ∂law) = 1 := by simp
  have hone : (∫ y, L y ^ 1 ∂law) = 0 := by
    simpa only [pow_one] using hfirst
  have hphase3 : Complex.I ^ 3 = -Complex.I := by
    calc
      Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
      _ = -Complex.I := by rw [Complex.I_sq]; ring
  have hphase4 : Complex.I ^ 4 = 1 := by
    calc
      Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
      _ = 1 := by rw [Complex.I_sq]; norm_num
  refine ⟨hs3, hs4, ?_⟩
  norm_num [Finset.sum_range_succ, Nat.factorial, hzero, hone,
    hfirstL, hsecondL, hphase3, hphase4, Complex.I_sq] <;> ring

end
end Shao.OQ3
