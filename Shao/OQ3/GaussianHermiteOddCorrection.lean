import Shao.OQ3.GaussianHermitePolynomialRecursor
import Shao.OQ3.DirectionalCGFCumulantHomogeneousPolynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem gaussian_hermite_polynomial_parity (n : ℕ) (x : ℝ) :
    (gaussianHermitePolynomial n).eval (-x) =
      (-1 : ℝ) ^ n * (gaussianHermitePolynomial n).eval x := by
  have hf : (fun z : ℝ => Real.exp (-(-z) ^ 2 / 2)) =
      (fun z : ℝ => Real.exp (-z ^ 2 / 2)) := by
    ext z
    simp only [neg_sq]
  have h := iteratedDeriv_comp_neg n (fun z : ℝ => Real.exp (-z ^ 2 / 2)) x
  rw [hf, gaussian_hermite_iterated_derivative,
    gaussian_hermite_iterated_derivative] at h
  simp only [smul_eq_mul, neg_sq] at h
  have hs : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  apply mul_right_cancel₀ (Real.exp_ne_zero (-x ^ 2 / 2))
  calc
    (gaussianHermitePolynomial n).eval (-x) * Real.exp (-x ^ 2 / 2) =
        ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
          ((gaussianHermitePolynomial n).eval (-x) * Real.exp (-x ^ 2 / 2)) := by
            rw [hs, one_mul]
    _ = (-1 : ℝ) ^ n * ((-1 : ℝ) ^ n *
        (gaussianHermitePolynomial n).eval (-x) * Real.exp (-x ^ 2 / 2)) := by ring
    _ = _ := h.symm

theorem gaussian_hermite_polynomial_odd_zero (k : ℕ) :
    (gaussianHermitePolynomial (2 * k + 1)).eval 0 = 0 := by
  have h := gaussian_hermite_polynomial_parity (2 * k + 1) 0
  have hs : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
    norm_num [pow_add, pow_mul]
  simp only [neg_zero, hs, neg_one_mul] at h
  linarith

theorem homogeneous_odd_hermite_sum_zero
    (P : MvPolynomial (Fin 2) ℝ) (k : ℕ) (hP : P.IsHomogeneous (2 * k + 1)) :
    (∑ d ∈ P.support, P.coeff d *
      (gaussianHermitePolynomial (d 0)).eval 0 *
        (gaussianHermitePolynomial (d 1)).eval 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro d hd
  have hdeg : d 0 + d 1 = 2 * k + 1 := by
    have hw := hP (Finsupp.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using hw
  by_cases hleft : d 0 % 2 = 1
  · have hd0 : d 0 = 2 * (d 0 / 2) + 1 := by omega
    rw [hd0, gaussian_hermite_polynomial_odd_zero]
    ring
  · have hd1 : d 1 = 2 * (d 1 / 2) + 1 := by omega
    rw [hd1, gaussian_hermite_polynomial_odd_zero]
    ring

theorem actual_directional_cgf_odd_hermite_sum_zero
    (mu : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure mu]
    (h0 : ∀ u v : ℝ, 0 ∈ interior
      (ProbabilityTheory.integrableExpSet
        (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) mu))
    (hM : ∀ j : ℕ, Integrable (fun y : Fin 2 → ℝ =>
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ j) mu) (k : ℕ) :
    ∃ P : MvPolynomial (Fin 2) ℝ, P.IsHomogeneous (2 * k + 1) ∧
      (∀ u v : ℝ, MvPolynomial.eval ![u, v] P =
        iteratedDeriv (2 * k + 1) (ProbabilityTheory.cgf
          (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) mu) 0) ∧
      (∑ d ∈ P.support, P.coeff d *
        (gaussianHermitePolynomial (d 0)).eval 0 *
          (gaussianHermitePolynomial (d 1)).eval 0) = 0 := by
  obtain ⟨P, hP, he⟩ :=
    pair_directional_cgf_cumulant_homogeneous_polynomial mu h0 hM (2 * k + 1)
  exact ⟨P, hP, he, homogeneous_odd_hermite_sum_zero P k hP⟩

end
end Shao.OQ3
