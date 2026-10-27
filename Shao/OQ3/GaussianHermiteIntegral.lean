import Shao.OQ3.GaussianFourierMomentDerivative
import Shao.OQ3.GaussianHermiteScaledDerivative

namespace Shao.OQ3
open MeasureTheory Real
noncomputable section

theorem real_standard_gaussian_hermite_integral (n : ℕ) (x : ℝ) :
    Integrable (fun t : ℝ =>
      Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ)) *
        (Complex.I * (t : ℂ)) ^ n * Complex.exp (-(t : ℂ) ^ 2 / 2)) ∧
      (∫ t : ℝ, Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ)) *
        (Complex.I * (t : ℂ)) ^ n * Complex.exp (-(t : ℂ) ^ 2 / 2)) =
        ((Real.sqrt (2 * Real.pi) * (gaussianHermitePolynomial n).eval x *
          Real.exp (-x ^ 2 / 2) : ℝ) : ℂ) := by
  let c : ℝ := Real.sqrt (2 * Real.pi)
  have hgauss (t : ℝ) :
      Complex.exp (-((1 / 2 : ℝ) : ℂ) * (t : ℂ) ^ 2) =
        Complex.exp (-(t : ℂ) ^ 2 / 2) := by
    congr 1
    push_cast
    ring
  have hbase := real_gaussian_oscillatory_moment_derivative (1 / 2) (by norm_num) n x
  dsimp only at hbase
  simp_rw [hgauss] at hbase
  refine ⟨hbase.1, ?_⟩
  have hF :
      (fun y : ℝ => (Real.sqrt (Real.pi / (1 / 2)) : ℂ) *
        Complex.exp (-(((2 * Real.pi * y) ^ 2 / (4 * (1 / 2)) : ℝ) : ℂ))) =
        (fun y : ℝ => (c : ℂ) *
          Complex.exp (((-(2 * Real.pi * y) ^ 2 / 2 : ℝ) : ℂ))) := by
    funext y
    have hc : Real.sqrt (Real.pi / (1 / 2)) = c := by
      dsimp [c]
      congr 1
      ring
    rw [hc]
    apply congrArg (fun z : ℂ => (c : ℂ) * Complex.exp z)
    push_cast
    ring
  have hx : (2 * Real.pi) * (x / (2 * Real.pi)) = x := by
    field_simp [Real.pi_ne_zero]
  rw [hbase.2, hF, gaussian_hermite_scaled_complex_iterated_derivative, hx]
  let v : ℂ := ((c * (gaussianHermitePolynomial n).eval x *
    Real.exp (-x ^ 2 / 2) : ℝ) : ℂ)
  change ((-2 * (Real.pi : ℂ)) ^ n)⁻¹ *
    ((c * (2 * Real.pi) ^ n *
      ((-1 : ℝ) ^ n * (gaussianHermitePolynomial n).eval x *
        Real.exp (-x ^ 2 / 2)) : ℝ) : ℂ) = v
  have hsign : (2 * (Real.pi : ℂ)) ^ n * (-1 : ℂ) ^ n =
      (-2 * (Real.pi : ℂ)) ^ n := by
    rw [← mul_pow]
    congr 1
    ring
  have hnum :
      ((c * (2 * Real.pi) ^ n *
        ((-1 : ℝ) ^ n * (gaussianHermitePolynomial n).eval x *
          Real.exp (-x ^ 2 / 2)) : ℝ) : ℂ) =
        (-2 * (Real.pi : ℂ)) ^ n * v := by
    dsimp [v]
    push_cast
    rw [← hsign]
    ring
  have hne : (-2 * (Real.pi : ℂ)) ^ n ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  rw [hnum, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

theorem pair_standard_gaussian_hermite_integral (m n : ℕ) (x : ℝ × ℝ) :
    Integrable (fun z : ℝ × ℝ =>
      Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
        (Complex.I * (z.1 : ℂ)) ^ m * (Complex.I * (z.2 : ℂ)) ^ n *
          Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) ∧
      (∫ z : ℝ × ℝ,
        Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
          (Complex.I * (z.1 : ℂ)) ^ m * (Complex.I * (z.2 : ℂ)) ^ n *
            Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) =
        ((2 * Real.pi *
          (gaussianHermitePolynomial m).eval x.1 *
          (gaussianHermitePolynomial n).eval x.2 *
            Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 2) : ℝ) : ℂ) := by
  let f : ℕ → ℝ → ℝ → ℂ := fun k u t =>
    Complex.exp (-Complex.I * (u : ℂ) * (t : ℂ)) *
      (Complex.I * (t : ℂ)) ^ k * Complex.exp (-(t : ℂ) ^ 2 / 2)
  obtain ⟨hi1, hv1⟩ := real_standard_gaussian_hermite_integral m x.1
  obtain ⟨hi2, hv2⟩ := real_standard_gaussian_hermite_integral n x.2
  have hprod : Integrable (fun z : ℝ × ℝ => f m x.1 z.1 * f n x.2 z.2) :=
    hi1.mul_prod hi2
  have hid (z : ℝ × ℝ) :
      Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
        (Complex.I * (z.1 : ℂ)) ^ m * (Complex.I * (z.2 : ℂ)) ^ n *
          Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2) =
        f m x.1 z.1 * f n x.2 z.2 := by
    have hphase :
        Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) =
          Complex.exp (-Complex.I * (x.1 : ℂ) * (z.1 : ℂ)) *
            Complex.exp (-Complex.I * (x.2 : ℂ) * (z.2 : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have he : Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2) =
        Complex.exp (-(z.1 : ℂ) ^ 2 / 2) *
          Complex.exp (-(z.2 : ℂ) ^ 2 / 2) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    dsimp only [f]
    rw [hphase, he]
    ring
  refine ⟨hprod.congr (Filter.Eventually.of_forall (fun z => (hid z).symm)), ?_⟩
  have hsq : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi := by
    rw [← pow_two, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
  have he : Real.exp (-x.1 ^ 2 / 2) * Real.exp (-x.2 ^ 2 / 2) =
      Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = ∫ z : ℝ × ℝ, f m x.1 z.1 * f n x.2 z.2 :=
      integral_congr_ae (Filter.Eventually.of_forall hid)
    _ = (∫ t : ℝ, f m x.1 t) * (∫ t : ℝ, f n x.2 t) := integral_prod_mul _ _
    _ = ((Real.sqrt (2 * Real.pi) * (gaussianHermitePolynomial m).eval x.1 *
          Real.exp (-x.1 ^ 2 / 2) : ℝ) : ℂ) *
        ((Real.sqrt (2 * Real.pi) * (gaussianHermitePolynomial n).eval x.2 *
          Real.exp (-x.2 ^ 2 / 2) : ℝ) : ℂ) := by
      change (∫ t : ℝ, Complex.exp (-Complex.I * (x.1 : ℂ) * (t : ℂ)) *
        (Complex.I * (t : ℂ)) ^ m * Complex.exp (-(t : ℂ) ^ 2 / 2)) *
          (∫ t : ℝ, Complex.exp (-Complex.I * (x.2 : ℂ) * (t : ℂ)) *
            (Complex.I * (t : ℂ)) ^ n * Complex.exp (-(t : ℂ) ^ 2 / 2)) = _
      rw [hv1, hv2]
    _ = _ := by
      rw [← Complex.ofReal_mul]
      apply congrArg Complex.ofReal
      calc
        _ = (Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi)) *
            (gaussianHermitePolynomial m).eval x.1 *
            (gaussianHermitePolynomial n).eval x.2 *
              (Real.exp (-x.1 ^ 2 / 2) * Real.exp (-x.2 ^ 2 / 2)) := by ring
        _ = _ := by rw [hsq, he]

end
end Shao.OQ3
