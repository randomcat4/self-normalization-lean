import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Prod

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem real_gaussian_oscillatory_integral
    (b : ℝ) (hb : 0 < b) (x : ℝ) :
    Integrable (fun t : ℝ =>
      Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ)) *
        Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2)) ∧
      (∫ t : ℝ, Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ)) *
        Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2)) =
        (Real.sqrt (Real.pi / b) : ℂ) *
          Complex.exp (-((x ^ 2 / (4 * b) : ℝ) : ℂ)) := by
  have hquad := integrable_cexp_quadratic
    (b := (b : ℂ)) (show 0 < (b : ℂ).re from hb) (-Complex.I * (x : ℂ)) 0
  have hid (t : ℝ) :
      Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ)) *
          Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2) =
        Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2 +
          (-Complex.I * (x : ℂ)) * (t : ℂ) + 0) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  refine ⟨hquad.congr (Filter.Eventually.of_forall (fun t => (hid t).symm)), ?_⟩
  have hphase (t : ℝ) :
      Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ)) =
        Complex.exp (Complex.I * (-(x : ℂ)) * (t : ℂ)) := by
    congr 1
    ring
  simp_rw [hphase]
  rw [fourierIntegral_gaussian (show 0 < (b : ℂ).re from hb) (-(x : ℂ))]
  have hpref : ((Real.pi : ℂ) / (b : ℂ)) ^ (1 / 2 : ℂ) =
      (Real.sqrt (Real.pi / b) : ℂ) := by
    simpa [Real.sqrt_eq_rpow] using
      (Complex.ofReal_cpow (show 0 ≤ Real.pi / b by positivity) (1 / 2 : ℝ)).symm
  have harg : - (-(x : ℂ)) ^ 2 / (4 * (b : ℂ)) =
      -((x ^ 2 / (4 * b) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hpref, harg]

theorem pair_gaussian_oscillatory_integral
    (b : ℝ) (hb : 0 < b) (x : ℝ × ℝ) :
    Integrable (fun z : ℝ × ℝ =>
      Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
        Complex.exp (-(b : ℂ) * ((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ))) ∧
      (∫ z : ℝ × ℝ,
        Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
          Complex.exp (-(b : ℂ) * ((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ))) =
        ((Real.pi / b : ℝ) : ℂ) *
          Complex.exp (-(((x.1 ^ 2 + x.2 ^ 2) / (4 * b) : ℝ) : ℂ)) := by
  let f : ℝ → ℝ → ℂ := fun s t =>
    Complex.exp (-Complex.I * (s : ℂ) * (t : ℂ)) *
      Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2)
  obtain ⟨hi1, hv1⟩ := real_gaussian_oscillatory_integral b hb x.1
  obtain ⟨hi2, hv2⟩ := real_gaussian_oscillatory_integral b hb x.2
  have hprod : Integrable (fun z : ℝ × ℝ => f x.1 z.1 * f x.2 z.2) :=
    hi1.mul_prod hi2
  have hid (z : ℝ × ℝ) :
      Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
          Complex.exp (-(b : ℂ) * ((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ)) =
        f x.1 z.1 * f x.2 z.2 := by
    dsimp only [f]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring
  refine ⟨hprod.congr (Filter.Eventually.of_forall (fun z => (hid z).symm)), ?_⟩
  have hsq : (Real.sqrt (Real.pi / b) : ℂ) * (Real.sqrt (Real.pi / b) : ℂ) =
      ((Real.pi / b : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt (by positivity : 0 ≤ Real.pi / b)]
  have hexp :
      Complex.exp (-((x.1 ^ 2 / (4 * b) : ℝ) : ℂ)) *
          Complex.exp (-((x.2 ^ 2 / (4 * b) : ℝ) : ℂ)) =
        Complex.exp (-(((x.1 ^ 2 + x.2 ^ 2) / (4 * b) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = ∫ z : ℝ × ℝ, f x.1 z.1 * f x.2 z.2 :=
      integral_congr_ae (Filter.Eventually.of_forall hid)
    _ = (∫ t : ℝ, f x.1 t) * (∫ t : ℝ, f x.2 t) := integral_prod_mul _ _
    _ = ((Real.sqrt (Real.pi / b) : ℂ) *
          Complex.exp (-((x.1 ^ 2 / (4 * b) : ℝ) : ℂ))) *
        ((Real.sqrt (Real.pi / b) : ℂ) *
          Complex.exp (-((x.2 ^ 2 / (4 * b) : ℝ) : ℂ))) := by
      rw [hv1, hv2]
    _ = ((Real.sqrt (Real.pi / b) : ℂ) * (Real.sqrt (Real.pi / b) : ℂ)) *
        (Complex.exp (-((x.1 ^ 2 / (4 * b) : ℝ) : ℂ)) *
          Complex.exp (-((x.2 ^ 2 / (4 * b) : ℝ) : ℂ))) := by ring
    _ = _ := by rw [hsq, hexp]

end
end Shao.OQ3
