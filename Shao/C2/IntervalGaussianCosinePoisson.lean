import Shao.C2.IntervalSineHighTimeProfiles
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

noncomputable section
namespace Shao.C2.IntervalGaussianCosinePoisson
open MeasureTheory Set Filter
open scoped BigOperators Topology

theorem complex_gaussian_quadratic_summable (a b : ℂ) (ha : 0 < a.re) :
    Summable (fun n : ℤ => Complex.exp (-(Real.pi : ℂ) * a * (n : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * b * (n : ℂ))) := by
  have hneg : (-(Real.pi : ℂ) * a).re < 0 := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
    nlinarith only [mul_pos Real.pi_pos ha]
  have hd := (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact
    (a := -(Real.pi : ℂ) * a) hneg (2 * (Real.pi : ℂ) * b) (-2 : ℝ)).isBigO
  have hs := summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
    (hd.comp_tendsto Int.tendsto_coe_cofinite)
  simpa only [Function.comp_def, Complex.ofReal_intCast, mul_assoc] using hs

theorem shifted_gaussian_summable (c u : ℝ) (hc : 0 < c) :
    Summable (fun n : ℤ => Real.exp (-((n : ℝ) + u) ^ 2 / c)) := by
  let A : ℂ := ((1 / (Real.pi * c) : ℝ) : ℂ)
  let B : ℂ := ((-u / (Real.pi * c) : ℝ) : ℂ)
  let K : ℂ := Complex.exp (((-u ^ 2 / c : ℝ) : ℂ))
  have hA : 0 < A.re := by dsimp only [A]; simp only [Complex.ofReal_re]; positivity
  have hs := complex_gaussian_quadratic_summable A B hA
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc)
  have hpC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have he (n : ℤ) : K * Complex.exp (-(Real.pi : ℂ) * A * (n : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * B * (n : ℂ)) = ((Real.exp (-((n : ℝ) + u) ^ 2 / c) : ℝ) : ℂ) := by
    dsimp only [K]
    rw [← Complex.exp_add, Complex.ofReal_exp]
    congr 1
    dsimp only [A, B]
    push_cast
    field_simp [hcC, hpC] <;> ring
  have hsEmbed : Summable (fun n : ℤ => ((Real.exp (-((n : ℝ) + u) ^ 2 / c) : ℝ) : ℂ)) :=
    (hs.mul_left K).congr he
  exact Complex.summable_ofReal.mp hsEmbed

theorem gaussian_cosine_summable (c u : ℝ) (hc : 0 < c) :
    Summable (fun n : ℤ => Real.exp (-(Real.pi ^ 2) * c * (n : ℝ) ^ 2) *
      Real.cos (2 * Real.pi * (n : ℝ) * u)) := by
  let A : ℂ := ((Real.pi * c : ℝ) : ℂ)
  let B : ℂ := -Complex.I * (u : ℂ)
  have hA : 0 < A.re := by dsimp only [A]; simpa using mul_pos Real.pi_pos hc
  have hs := complex_gaussian_quadratic_summable A B hA
  have hphase (n : ℤ) : -(Real.pi : ℂ) * A * (n : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * B * (n : ℂ) =
        ((-(Real.pi ^ 2) * c * (n : ℝ) ^ 2 : ℝ) : ℂ) -
          ((2 * Real.pi * (n : ℝ) * u : ℝ) : ℂ) * Complex.I := by
    dsimp only [A, B]
    push_cast
    ring
  have hterm (n : ℤ) : (Complex.exp (-(Real.pi : ℂ) * A * (n : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * B * (n : ℂ))).re =
        Real.exp (-(Real.pi ^ 2) * c * (n : ℝ) ^ 2) * Real.cos (2 * Real.pi * (n : ℝ) * u) := by
    rw [hphase n, Complex.exp_re]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
      mul_one, sub_zero, zero_sub, zero_add, add_zero, Real.cos_neg]
  exact ((Complex.hasSum_re hs.hasSum).summable).congr hterm

theorem shifted_gaussian_cosine_poisson (c u : ℝ) (hc : 0 < c) :
    (∑' m : ℤ, Real.exp (-((m : ℝ) + u) ^ 2 / c)) =
      Real.sqrt (Real.pi * c) *
        (∑' n : ℤ, Real.exp (-(Real.pi ^ 2) * c * (n : ℝ) ^ 2) *
          Real.cos (2 * Real.pi * (n : ℝ) * u)) := by
  let A : ℂ := ((Real.pi * c : ℝ) : ℂ)
  let B : ℂ := -Complex.I * (u : ℂ)
  have hA : 0 < A.re := by dsimp only [A]; simpa using mul_pos Real.pi_pos hc
  have hs := complex_gaussian_quadratic_summable A B hA
  have hphase (n : ℤ) : -(Real.pi : ℂ) * A * (n : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * B * (n : ℂ) =
        ((-(Real.pi ^ 2) * c * (n : ℝ) ^ 2 : ℝ) : ℂ) -
          ((2 * Real.pi * (n : ℝ) * u : ℝ) : ℂ) * Complex.I := by
    dsimp only [A, B]
    push_cast
    ring
  have hterm (n : ℤ) : (Complex.exp (-(Real.pi : ℂ) * A * (n : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * B * (n : ℂ))).re =
        Real.exp (-(Real.pi ^ 2) * c * (n : ℝ) ^ 2) * Real.cos (2 * Real.pi * (n : ℝ) * u) := by
    rw [hphase n, Complex.exp_re]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
      mul_one, sub_zero, zero_sub, zero_add, add_zero, Real.cos_neg]
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc)
  have hpC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hIB : Complex.I * B = (u : ℂ) := by
    dsimp only [B]
    calc
      _ = -(Complex.I * Complex.I) * (u : ℂ) := by ring
      _ = _ := by rw [← pow_two, Complex.I_sq]; ring
  have hright (m : ℤ) : Complex.exp (-(Real.pi : ℂ) / A * ((m : ℂ) + Complex.I * B) ^ 2) =
      ((Real.exp (-((m : ℝ) + u) ^ 2 / c) : ℝ) : ℂ) := by
    rw [hIB, Complex.ofReal_exp]
    congr 1
    dsimp only [A]
    push_cast
    field_simp [hcC, hpC] <;> ring
  have hhalf : A ^ (1 / 2 : ℂ) = (Real.sqrt (Real.pi * c) : ℂ) := by
    dsimp only [A]
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ Real.pi * c)]
    push_cast
    rfl
  have hsG := shifted_gaussian_summable c u hc
  have hsEmbed : Summable (fun m : ℤ => ((Real.exp (-((m : ℝ) + u) ^ 2 / c) : ℝ) : ℂ)) :=
    Complex.summable_ofReal.mpr hsG
  have hsRight : Summable (fun m : ℤ =>
      Complex.exp (-(Real.pi : ℂ) / A * ((m : ℂ) + Complex.I * B) ^ 2)) :=
    hsEmbed.congr (fun m => (hright m).symm)
  have hrightRe : (∑' m : ℤ,
      Complex.exp (-(Real.pi : ℂ) / A * ((m : ℂ) + Complex.I * B) ^ 2)).re =
        ∑' m : ℤ, Real.exp (-((m : ℝ) + u) ^ 2 / c) := by
    rw [Complex.re_tsum hsRight]
    apply tsum_congr
    intro m
    rw [hright m, Complex.ofReal_re]
  have htheta := Complex.tsum_exp_neg_quadratic hA B
  have hroot : 0 < Real.sqrt (Real.pi * c) := by positivity
  have hrootC : (Real.sqrt (Real.pi * c) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hroot)
  have hscaled : (Real.sqrt (Real.pi * c) : ℂ) *
      (∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) * A * (n : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * B * (n : ℂ))) =
      ∑' m : ℤ, Complex.exp (-(Real.pi : ℂ) / A * ((m : ℂ) + Complex.I * B) ^ 2) := by
    rw [htheta, hhalf]
    calc
      _ = ((Real.sqrt (Real.pi * c) : ℂ) * (1 / (Real.sqrt (Real.pi * c) : ℂ))) *
          (∑' m : ℤ, Complex.exp (-(Real.pi : ℂ) / A * ((m : ℂ) + Complex.I * B) ^ 2)) := by ring
      _ = _ := by simp only [one_div, mul_inv_cancel₀ hrootC, one_mul]
  have hreal := congrArg Complex.re hscaled
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hreal
  rw [Complex.re_tsum hs, hrightRe] at hreal
  simp_rw [hterm] at hreal
  exact hreal.symm

end Shao.C2.IntervalGaussianCosinePoisson
