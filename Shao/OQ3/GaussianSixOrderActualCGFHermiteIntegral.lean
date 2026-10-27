import Shao.OQ3.DirectionalCGFComplexHomogeneousPolynomial
import Shao.OQ3.GaussianMvPolynomialHermiteIntegral

namespace Shao.OQ3
open MeasureTheory Real
open scoped BigOperators
noncomputable section

theorem pair_directional_cgf_six_order_gaussian_hermite_integral
    (mu : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure mu]
    (h0 : ∀ u v : ℝ, 0 ∈ interior
      (ProbabilityTheory.integrableExpSet
        (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) mu))
    (hM : ∀ k : ℕ, Integrable (fun y : Fin 2 → ℝ =>
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ k) mu) (n : ℕ) (hn : 1 ≤ n) :
    let kappa : (ℝ × ℝ) → ℕ → ℝ := fun z j =>
      iteratedDeriv j (ProbabilityTheory.cgf
        (fun y : Fin 2 → ℝ => z.1 * y 0 + z.2 * y 1) mu) 0
    let a : (ℝ × ℝ) → Fin 6 → ℂ := fun z j =>
      (Complex.I ^ (j.val + 3) / ((j.val + 3).factorial : ℂ)) *
        (kappa z (j.val + 3) : ℂ) /
          (Real.sqrt (n : ℝ) : ℂ) ^ (j.val + 1)
    let S : (ℝ × ℝ) → ℂ := fun z =>
      ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
        ∑ sigma : Fin q.val → Fin 6,
          if (∑ i, ((sigma i).val + 1)) ≤ 6 then ∏ i, a z (sigma i) else 0
    ∃ P : MvPolynomial (Fin 2) ℝ,
      (∀ z : ℝ × ℝ, MvPolynomial.eval₂ Complex.ofRealHom
        ![Complex.I * (z.1 : ℂ), Complex.I * (z.2 : ℂ)] P = S z) ∧
      ∀ x : ℝ × ℝ,
        Integrable (fun z : ℝ × ℝ =>
          Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
            S z * Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) ∧
          (∫ z : ℝ × ℝ,
            Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
              S z * Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) =
            ((2 * Real.pi *
              (∑ d ∈ P.support, P.coeff d *
                (gaussianHermitePolynomial (d 0)).eval x.1 *
                  (gaussianHermitePolynomial (d 1)).eval x.2) *
                    Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 2) : ℝ) : ℂ) := by
  classical
  intro kappa a S
  have hfamily (j : Fin 6) :
      ∃ K : MvPolynomial (Fin 2) ℝ, K.IsHomogeneous (j.val + 3) ∧
        (∀ u v : ℝ, MvPolynomial.eval ![u, v] K =
          iteratedDeriv (j.val + 3) (ProbabilityTheory.cgf
            (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) mu) 0) ∧
        ∀ u v : ℝ, MvPolynomial.eval₂ Complex.ofRealHom
          ![Complex.I * (u : ℂ), Complex.I * (v : ℂ)] K =
            Complex.I ^ (j.val + 3) *
              ((iteratedDeriv (j.val + 3) (ProbabilityTheory.cgf
                (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) mu) 0 : ℝ) : ℂ) :=
    pair_directional_cgf_complex_homogeneous_polynomial mu h0 hM (j.val + 3)
  choose K hKh hKr hKi using hfamily
  let B : Fin 6 → MvPolynomial (Fin 2) ℝ := fun j =>
    MvPolynomial.C (1 / (((j.val + 3).factorial : ℝ) *
      Real.sqrt (n : ℝ) ^ (j.val + 1))) * K j
  have hnreal : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hn)
  have hsn : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 hnreal))
  have hB (z : ℝ × ℝ) (j : Fin 6) :
      MvPolynomial.eval₂ Complex.ofRealHom
        ![Complex.I * (z.1 : ℂ), Complex.I * (z.2 : ℂ)] (B j) = a z j := by
    dsimp only [B, a]
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, hKi j z.1 z.2]
    have hfact : ((j.val + 3).factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (j.val + 3)
    change ((1 / (((j.val + 3).factorial : ℝ) *
      Real.sqrt (n : ℝ) ^ (j.val + 1)) : ℝ) : ℂ) *
        (Complex.I ^ (j.val + 3) * (kappa z (j.val + 3) : ℂ)) = _
    push_cast
    field_simp [hfact, hsn] <;> ring
  let P : MvPolynomial (Fin 2) ℝ :=
    ∑ q : Fin 7, MvPolynomial.C (1 / (q.val.factorial : ℝ)) *
      ∑ sigma : Fin q.val → Fin 6,
        if (∑ i, ((sigma i).val + 1)) ≤ 6 then ∏ i, B (sigma i) else 0
  have heval (z : ℝ × ℝ) : MvPolynomial.eval₂ Complex.ofRealHom
      ![Complex.I * (z.1 : ℂ), Complex.I * (z.2 : ℂ)] P = S z := by
    dsimp only [P, S]
    simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
    apply Finset.sum_congr rfl
    intro q _
    have hcoef : Complex.ofRealHom (1 / (q.val.factorial : ℝ)) =
        1 / (q.val.factorial : ℂ) := by
      change ((1 / (q.val.factorial : ℝ) : ℝ) : ℂ) = _
      push_cast <;> rfl
    rw [hcoef]
    congr 1
    apply Finset.sum_congr rfl
    intro sigma _
    split_ifs with hweight
    · rw [MvPolynomial.eval₂_prod]
      apply Finset.prod_congr rfl
      intro i _
      exact hB z (sigma i)
    · simp only [MvPolynomial.eval₂_zero]
  refine ⟨P, heval, ?_⟩
  intro x
  simpa only [heval] using pair_mv_polynomial_gaussian_hermite_integral P x

end
end Shao.OQ3
