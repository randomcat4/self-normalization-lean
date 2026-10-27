import Shao.OQ3.DirectionalCGFCumulantHomogeneousPolynomial

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem pair_homogeneous_polynomial_eval_imaginary
    (P : MvPolynomial (Fin 2) ℝ) (n : ℕ) (hP : P.IsHomogeneous n)
    (u v : ℝ) :
    MvPolynomial.eval₂ Complex.ofRealHom
      ![Complex.I * (u : ℂ), Complex.I * (v : ℂ)] P =
        Complex.I ^ n * ((MvPolynomial.eval ![u, v] P : ℝ) : ℂ) := by
  classical
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval_eq']
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : d 0 + d 1 = n := by
    have hw := hP (Finsupp.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using hw
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  change (P.coeff d : ℂ) *
      ((Complex.I * (u : ℂ)) ^ d 0 * (Complex.I * (v : ℂ)) ^ d 1) =
        Complex.I ^ n * ((P.coeff d : ℂ) * ((u : ℂ) ^ d 0 * (v : ℂ) ^ d 1))
  have hI : Complex.I ^ n = Complex.I ^ d 0 * Complex.I ^ d 1 := by
    rw [← pow_add, hdeg]
  rw [mul_pow, mul_pow, hI]
  ring

theorem pair_directional_cgf_complex_homogeneous_polynomial
    (mu : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure mu]
    (h0 : ∀ u v : ℝ, 0 ∈ interior
      (ProbabilityTheory.integrableExpSet
        (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) mu))
    (hM : ∀ k : ℕ, Integrable (fun y : Fin 2 → ℝ =>
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ k) mu) (n : ℕ) :
    ∃ P : MvPolynomial (Fin 2) ℝ, P.IsHomogeneous n ∧
      (∀ u v : ℝ, MvPolynomial.eval ![u, v] P =
        iteratedDeriv n (ProbabilityTheory.cgf
          (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) mu) 0) ∧
      ∀ u v : ℝ, MvPolynomial.eval₂ Complex.ofRealHom
        ![Complex.I * (u : ℂ), Complex.I * (v : ℂ)] P =
          Complex.I ^ n *
            ((iteratedDeriv n (ProbabilityTheory.cgf
              (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) mu) 0 : ℝ) : ℂ) := by
  obtain ⟨P, hP, he⟩ :=
    pair_directional_cgf_cumulant_homogeneous_polynomial mu h0 hM n
  refine ⟨P, hP, he, ?_⟩
  intro u v
  rw [pair_homogeneous_polynomial_eval_imaginary P n hP u v, he u v]

end
end Shao.OQ3
