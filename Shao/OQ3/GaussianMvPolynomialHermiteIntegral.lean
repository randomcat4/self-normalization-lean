import Shao.OQ3.GaussianFiniteHermiteIntegral
import Mathlib.Algebra.MvPolynomial.Eval

namespace Shao.OQ3
open MeasureTheory Real
open scoped BigOperators
noncomputable section

theorem pair_mv_polynomial_gaussian_hermite_integral
    (P : MvPolynomial (Fin 2) ℝ) (x : ℝ × ℝ) :
    Integrable (fun z : ℝ × ℝ =>
      Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
        MvPolynomial.eval₂ Complex.ofRealHom
          ![Complex.I * (z.1 : ℂ), Complex.I * (z.2 : ℂ)] P *
            Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) ∧
      (∫ z : ℝ × ℝ,
        Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
          MvPolynomial.eval₂ Complex.ofRealHom
            ![Complex.I * (z.1 : ℂ), Complex.I * (z.2 : ℂ)] P *
              Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) =
        ((2 * Real.pi *
          (∑ d ∈ P.support, P.coeff d *
            (gaussianHermitePolynomial (d 0)).eval x.1 *
              (gaussianHermitePolynomial (d 1)).eval x.2) *
                Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 2) : ℝ) : ℂ) := by
  classical
  let e : (Fin 2 →₀ ℕ) → ℕ × ℕ := fun d => (d 0, d 1)
  let back : (ℕ × ℕ) → (Fin 2 →₀ ℕ) := fun k =>
    Finsupp.single 0 k.1 + Finsupp.single 1 k.2
  have hback (d : Fin 2 →₀ ℕ) : back (e d) = d := by
    ext i
    fin_cases i <;> simp [back, e]
  have hinj : Function.Injective e := by
    intro d d' h
    have hb := congrArg back h
    simpa only [hback] using hb
  let s : Finset (ℕ × ℕ) := P.support.image e
  let a : (ℕ × ℕ) → ℝ := fun k => P.coeff (back k)
  have heval (z : ℝ × ℝ) :
      MvPolynomial.eval₂ Complex.ofRealHom
          ![Complex.I * (z.1 : ℂ), Complex.I * (z.2 : ℂ)] P =
        ∑ k ∈ s, (a k : ℂ) *
          (Complex.I * (z.1 : ℂ)) ^ k.1 * (Complex.I * (z.2 : ℂ)) ^ k.2 := by
    dsimp only [s, a]
    rw [Finset.sum_image (fun d _ d' _ h => hinj h)]
    rw [MvPolynomial.eval₂_eq']
    apply Finset.sum_congr rfl
    intro d _
    rw [hback]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    change (P.coeff d : ℂ) *
      ((Complex.I * (z.1 : ℂ)) ^ d 0 * (Complex.I * (z.2 : ℂ)) ^ d 1) =
        (P.coeff d : ℂ) * (Complex.I * (z.1 : ℂ)) ^ d 0 *
          (Complex.I * (z.2 : ℂ)) ^ d 1
    ring
  have hsum :
      (∑ k ∈ s, a k * (gaussianHermitePolynomial k.1).eval x.1 *
        (gaussianHermitePolynomial k.2).eval x.2) =
      ∑ d ∈ P.support, P.coeff d * (gaussianHermitePolynomial (d 0)).eval x.1 *
        (gaussianHermitePolynomial (d 1)).eval x.2 := by
    dsimp only [s, a]
    rw [Finset.sum_image (fun d _ d' _ h => hinj h)]
    apply Finset.sum_congr rfl
    intro d _
    rw [hback]
  have h := pair_standard_gaussian_finite_hermite_integral s a x
  simpa only [← heval, hsum] using h

end
end Shao.OQ3
