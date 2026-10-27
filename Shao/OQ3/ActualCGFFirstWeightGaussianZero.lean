import Shao.OQ3.DirectionalCGFComplexHomogeneousPolynomial
import Shao.OQ3.GaussianMvPolynomialHermiteIntegral
import Shao.OQ3.GaussianHermiteOddCorrection

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem six_order_word_weight_one (a : Fin 6 → ℂ) :
    (∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
      ∑ sigma : Fin q.val → Fin 6,
        if (∑ i, ((sigma i).val + 1)) = 1 then ∏ i, a (sigma i) else 0) = a 0 := by
  classical
  let e : (Fin 1 → Fin 6) ≃ Fin 6 :=
    { toFun := fun sigma => sigma 0
      invFun := fun j _ => j
      left_inv := by
        intro sigma
        funext i
        exact congrArg sigma (Subsingleton.elim (0 : Fin 1) i)
      right_inv := by intro j; rfl }
  have hinner :
      (∑ sigma : Fin 1 → Fin 6,
        if (∑ i, ((sigma i).val + 1)) = 1 then ∏ i, a (sigma i) else 0) = a 0 := by
    calc
      _ = ∑ j : Fin 6, if j = 0 then a j else 0 := by
        apply Fintype.sum_equiv e
        intro sigma
        simp only [Fin.sum_univ_one, Fin.prod_univ_one]
        change (if (sigma 0).val + 1 = 1 then a (sigma 0) else 0) =
          if sigma 0 = 0 then a (sigma 0) else 0
        have he : (sigma 0).val + 1 = 1 ↔ sigma 0 = 0 := by
          constructor
          · intro h
            apply Fin.ext
            change (sigma 0).val = 0
            omega
          · intro h
            rw [h]
            rfl
        simp only [he]
      _ = a 0 := by simp
  have hsum :
      (∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
        ∑ sigma : Fin q.val → Fin 6,
          if (∑ i, ((sigma i).val + 1)) = 1 then ∏ i, a (sigma i) else 0) =
        (1 / (Nat.factorial 1 : ℂ)) *
          ∑ sigma : Fin 1 → Fin 6,
            if (∑ i, ((sigma i).val + 1)) = 1 then ∏ i, a (sigma i) else 0 := by
    apply Finset.sum_eq_single (1 : Fin 7)
    · intro q _ hq
      by_cases hq0 : q = 0
      · subst q
        simp
      · have hqv0 : q.val ≠ 0 := by
          intro h
          apply hq0
          exact Fin.ext h
        have hqv1 : q.val ≠ 1 := by
          intro h
          apply hq
          exact Fin.ext h
        have hq2 : 2 ≤ q.val := by omega
        have hzero :
            (∑ sigma : Fin q.val → Fin 6,
              if (∑ i, ((sigma i).val + 1)) = 1 then ∏ i, a (sigma i) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro sigma _
          have hlow : q.val ≤ ∑ i : Fin q.val, ((sigma i).val + 1) := by
            calc
              q.val = ∑ _i : Fin q.val, 1 := by simp
              _ ≤ _ := Finset.sum_le_sum (by intro i _; omega)
          have hne : (∑ i, ((sigma i).val + 1)) ≠ 1 := by omega
          rw [if_neg hne]
        rw [hzero, mul_zero]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  simpa only [hinner, Nat.factorial_one, Nat.cast_one, div_one, one_mul] using hsum

theorem actual_cgf_cubic_gaussian_integral_zero
    (mu : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure mu]
    (h0 : ∀ u v : ℝ, 0 ∈ interior
      (ProbabilityTheory.integrableExpSet
        (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) mu))
    (hM : ∀ j : ℕ, Integrable (fun y : Fin 2 → ℝ =>
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ j) mu) (c : ℂ) :
    Integrable (fun z : ℝ × ℝ => c * Complex.I ^ 3 *
      ((iteratedDeriv 3 (ProbabilityTheory.cgf
        (fun y : Fin 2 → ℝ => z.1 * y 0 + z.2 * y 1) mu) 0 : ℝ) : ℂ) *
      Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) ∧
    (∫ z : ℝ × ℝ, c * Complex.I ^ 3 *
      ((iteratedDeriv 3 (ProbabilityTheory.cgf
        (fun y : Fin 2 → ℝ => z.1 * y 0 + z.2 * y 1) mu) 0 : ℝ) : ℂ) *
      Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) = 0 := by
  obtain ⟨P, hP, _, heval⟩ :=
    pair_directional_cgf_complex_homogeneous_polynomial mu h0 hM 3
  have hsum :
      (∑ d ∈ P.support, P.coeff d *
        (gaussianHermitePolynomial (d 0)).eval 0 *
          (gaussianHermitePolynomial (d 1)).eval 0) = 0 := by
    exact homogeneous_odd_hermite_sum_zero P 1 hP
  have hbase :
      Integrable (fun z : ℝ × ℝ =>
        MvPolynomial.eval₂ Complex.ofRealHom
          ![Complex.I * (z.1 : ℂ), Complex.I * (z.2 : ℂ)] P *
          Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) ∧
      (∫ z : ℝ × ℝ,
        MvPolynomial.eval₂ Complex.ofRealHom
          ![Complex.I * (z.1 : ℂ), Complex.I * (z.2 : ℂ)] P *
          Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) = 0 := by
    simpa [hsum] using pair_mv_polynomial_gaussian_hermite_integral P (0, 0)
  have hf :
      (fun z : ℝ × ℝ => c * Complex.I ^ 3 *
        ((iteratedDeriv 3 (ProbabilityTheory.cgf
          (fun y : Fin 2 → ℝ => z.1 * y 0 + z.2 * y 1) mu) 0 : ℝ) : ℂ) *
        Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) =
      fun z : ℝ × ℝ => c *
        (MvPolynomial.eval₂ Complex.ofRealHom
          ![Complex.I * (z.1 : ℂ), Complex.I * (z.2 : ℂ)] P *
          Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) := by
    funext z
    rw [heval z.1 z.2]
    ring
  rw [hf]
  constructor
  · exact hbase.1.const_mul c
  · rw [integral_const_mul, hbase.2, mul_zero]

theorem actual_cgf_six_order_weight_one_gaussian_integral_zero
    (mu : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure mu]
    (h0 : ∀ u v : ℝ, 0 ∈ interior
      (ProbabilityTheory.integrableExpSet
        (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) mu))
    (hM : ∀ j : ℕ, Integrable (fun y : Fin 2 → ℝ =>
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ j) mu) (n : ℕ) :
    let kappa : (ℝ × ℝ) → ℕ → ℝ := fun z j =>
      iteratedDeriv j (ProbabilityTheory.cgf
        (fun y : Fin 2 → ℝ => z.1 * y 0 + z.2 * y 1) mu) 0
    let a : (ℝ × ℝ) → Fin 6 → ℂ := fun z j =>
      (Complex.I ^ (j.val + 3) / ((j.val + 3).factorial : ℂ)) *
        (kappa z (j.val + 3) : ℂ) /
          (Real.sqrt (n : ℝ) : ℂ) ^ (j.val + 1)
    let S1 : (ℝ × ℝ) → ℂ := fun z =>
      ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
        ∑ sigma : Fin q.val → Fin 6,
          if (∑ i, ((sigma i).val + 1)) = 1 then ∏ i, a z (sigma i) else 0
    Integrable (fun z : ℝ × ℝ => S1 z *
      Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) ∧
    (∫ z : ℝ × ℝ, S1 z *
      Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) = 0 := by
  intro kappa a S1
  have hS (z : ℝ × ℝ) : S1 z = a z 0 := six_order_word_weight_one (a z)
  let c : ℂ := (1 / (Nat.factorial 3 : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)
  have ha (z : ℝ × ℝ) : a z 0 = c * Complex.I ^ 3 *
      ((iteratedDeriv 3 (ProbabilityTheory.cgf
        (fun y : Fin 2 → ℝ => z.1 * y 0 + z.2 * y 1) mu) 0 : ℝ) : ℂ) := by
    change (Complex.I ^ 3 / (Nat.factorial 3 : ℂ)) *
      ((iteratedDeriv 3 (ProbabilityTheory.cgf
        (fun y : Fin 2 → ℝ => z.1 * y 0 + z.2 * y 1) mu) 0 : ℝ) : ℂ) /
        (Real.sqrt (n : ℝ) : ℂ) ^ 1 = _
    dsimp only [c]
    simp only [div_eq_mul_inv, pow_one]
    ring
  have h := actual_cgf_cubic_gaussian_integral_zero mu h0 hM c
  simpa only [hS, ha] using h

end
end Shao.OQ3
