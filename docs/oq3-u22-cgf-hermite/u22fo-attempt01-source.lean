import Shao.OQ3.GaussianOscillatoryIntegral
import Mathlib.Analysis.Fourier.FourierTransformDeriv

namespace Shao.OQ3
open MeasureTheory Real
open scoped BigOperators FourierTransform
noncomputable section

theorem real_gaussian_complex_moment_integrable
    (b : ℝ) (hb : 0 < b) (n : ℕ) :
    Integrable (fun t : ℝ =>
      (t : ℂ) ^ n * Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2)) := by
  have hr : Integrable (fun t : ℝ => t ^ n * Real.exp (-b * t ^ 2)) := by
    simpa only [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq (b := b) hb
        (s := (n : ℝ)) (by positivity : (-1 : ℝ) < (n : ℝ)))
  have hnorm (t : ℝ) :
      ‖(t : ℂ) ^ n * Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2)‖ =
        ‖t ^ n * Real.exp (-b * t ^ 2)‖ := by
    simp [Complex.norm_exp, pow_two, Complex.mul_re, abs_mul]
  have hcont : Continuous (fun t : ℝ =>
      (t : ℂ) ^ n * Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2)) := by fun_prop
  apply hr.norm.mono' hcont.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => (hnorm t).le)

theorem real_gaussian_oscillatory_moment_derivative
    (b : ℝ) (hb : 0 < b) (n : ℕ) (x : ℝ) :
    let F : ℝ → ℂ := fun y =>
      (Real.sqrt (Real.pi / b) : ℂ) *
        Complex.exp (-(((2 * Real.pi * y) ^ 2 / (4 * b) : ℝ) : ℂ))
    Integrable (fun t : ℝ =>
      Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ)) *
        (Complex.I * (t : ℂ)) ^ n *
          Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2)) ∧
      (∫ t : ℝ, Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ)) *
        (Complex.I * (t : ℂ)) ^ n *
          Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2)) =
        ((-2 * (Real.pi : ℂ)) ^ n)⁻¹ *
          iteratedDeriv n F (x / (2 * Real.pi)) := by
  intro F
  let g : ℝ → ℂ := fun t => Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2)
  have hm (m : ℕ) : Integrable (fun t : ℝ => (t : ℂ) ^ m * g t) :=
    real_gaussian_complex_moment_integrable b hb m
  have hreal (m : ℕ) : Integrable (fun t : ℝ => t ^ m • g t) := by
    simpa [Algebra.smul_def, g] using hm m
  have hkernel (t : ℝ) :
      ‖Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  have hpower (t : ℝ) : ‖(Complex.I * (t : ℂ)) ^ n‖ = ‖(t : ℂ) ^ n‖ := by
    simp [norm_pow, norm_mul]
  have hint : Integrable (fun t : ℝ =>
      Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ)) *
        (Complex.I * (t : ℂ)) ^ n * g t) := by
    have hcont : Continuous (fun t : ℝ =>
        Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ)) *
          (Complex.I * (t : ℂ)) ^ n * g t) := by dsimp [g]; fun_prop
    apply (hm n).norm.mono' hcont.aestronglyMeasurable
    filter_upwards [] with t
    simp only [norm_mul, hkernel, hpower, one_mul]
  refine ⟨hint, ?_⟩
  have hF : (𝓕 g) = F := by
    funext y
    rw [fourier_real_eq_integral_exp_smul]
    simp only [smul_eq_mul]
    have hphase (t : ℝ) :
        Complex.exp (((-2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I) =
          Complex.exp (-Complex.I * ((2 * Real.pi * y : ℝ) : ℂ) * (t : ℂ)) := by
      congr 1
      push_cast
      ring
    simp_rw [hphase]
    exact (real_gaussian_oscillatory_integral b hb (2 * Real.pi * y)).2
  have hD := congrFun
    (Real.iteratedDeriv_fourier (f := g) (N := ⊤) (n := n)
      (fun m _ => hreal m) (by exact le_top)) (x / (2 * Real.pi))
  rw [hF, fourier_real_eq_integral_exp_smul] at hD
  simp only [smul_eq_mul] at hD
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hphase (t : ℝ) :
      Complex.exp (((-2 * Real.pi * t * (x / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ)) := by
    congr 1
    push_cast
    field_simp [hpi]
    ring
  have hfactor (t : ℝ) :
      (-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ n =
        (-2 * (Real.pi : ℂ)) ^ n * (Complex.I * (t : ℂ)) ^ n := by
    rw [show -2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) =
      (-2 * (Real.pi : ℂ)) * (Complex.I * (t : ℂ)) by ring, mul_pow]
  have hrelation :
      iteratedDeriv n F (x / (2 * Real.pi)) =
        (-2 * (Real.pi : ℂ)) ^ n *
          (∫ t : ℝ, Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ)) *
            (Complex.I * (t : ℂ)) ^ n * g t) := by
    calc
      _ = ∫ t : ℝ,
          Complex.exp (((-2 * Real.pi * t * (x / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) *
            ((-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ n * g t) := hD
      _ = ∫ t : ℝ, (-2 * (Real.pi : ℂ)) ^ n *
          (Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ)) *
            (Complex.I * (t : ℂ)) ^ n * g t) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun t => by rw [hphase, hfactor]; ring)
      _ = _ := by rw [integral_const_mul]
  have hc : (-2 * (Real.pi : ℂ)) ^ n ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (by norm_num) hpi)
  calc
    _ = ((-2 * (Real.pi : ℂ)) ^ n)⁻¹ *
        ((-2 * (Real.pi : ℂ)) ^ n *
          (∫ t : ℝ, Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ)) *
            (Complex.I * (t : ℂ)) ^ n * g t)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    _ = _ := by rw [hrelation]

end
end Shao.OQ3
