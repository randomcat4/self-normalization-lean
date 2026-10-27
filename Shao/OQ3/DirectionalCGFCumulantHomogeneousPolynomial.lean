import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Shao.OQ3.DirectionalMomentPolynomialContinuity
import Shao.OQ3.ActualMomentCumulantRecurrence

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem pair_directional_moment_homogeneous_polynomial
    (mu : Measure (Fin 2 → ℝ)) (k : ℕ)
    (hM : Integrable (fun y : Fin 2 → ℝ =>
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ k) mu) :
    let b : ℕ → ℝ := fun j =>
      ∫ y : Fin 2 → ℝ, y 0 ^ j * y 1 ^ (k - j) ∂mu
    let P : MvPolynomial (Fin 2) ℝ :=
      ∑ j ∈ Finset.range (k + 1),
        MvPolynomial.C ((k.choose j : ℝ) * b j) *
          MvPolynomial.X 0 ^ j * MvPolynomial.X 1 ^ (k - j)
    P.IsHomogeneous k ∧
      ∀ u v : ℝ, MvPolynomial.eval ![u, v] P =
        ∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ k ∂mu := by
  classical
  intro b P
  obtain ⟨hmixed, hformula, hcontinuous⟩ :=
    pair_directional_moment_binomial_continuous mu k hM
  refine ⟨?_, ?_⟩
  · apply MvPolynomial.IsHomogeneous.sum
    intro j hj
    have hjle : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    simpa only [Nat.add_sub_of_le hjle] using
      (MvPolynomial.isHomogeneous_C_mul_X_pow
        ((k.choose j : ℝ) * b j) (0 : Fin 2) j).mul
          (MvPolynomial.isHomogeneous_X_pow (R := ℝ) (1 : Fin 2) (k - j))
  · intro u v
    change MvPolynomial.eval ![u, v]
      (∑ j ∈ Finset.range (k + 1),
        MvPolynomial.C ((k.choose j : ℝ) * b j) *
          MvPolynomial.X 0 ^ j * MvPolynomial.X 1 ^ (k - j)) = _
    have hform := hformula (u, v)
    dsimp only at hform
    rw [MvPolynomial.eval_sum, hform]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [map_mul, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

theorem pair_directional_cgf_cumulant_homogeneous_polynomial
    (mu : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure mu]
    (h0 : ∀ u v : ℝ, 0 ∈ interior
      (ProbabilityTheory.integrableExpSet
        (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) mu))
    (hM : ∀ k : ℕ, Integrable (fun y : Fin 2 → ℝ =>
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ k) mu) (n : ℕ) :
    ∃ P : MvPolynomial (Fin 2) ℝ, P.IsHomogeneous n ∧
      ∀ u v : ℝ, MvPolynomial.eval ![u, v] P =
        iteratedDeriv n (ProbabilityTheory.cgf
          (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) mu) 0 := by
  classical
  have hmom (k : ℕ) : ∃ P : MvPolynomial (Fin 2) ℝ,
      P.IsHomogeneous k ∧ ∀ u v : ℝ,
        MvPolynomial.eval ![u, v] P =
          ∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ k ∂mu := by
    exact ⟨_, pair_directional_moment_homogeneous_polynomial mu k (hM k)⟩
  choose M hMh hMe using hmom
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      refine ⟨0, MvPolynomial.isHomogeneous_zero (Fin 2) ℝ 0, ?_⟩
      intro u v
      simp
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      let K : ℕ → MvPolynomial (Fin 2) ℝ := fun k =>
        if hk : k < m + 1 then Classical.choose (ih k hk) else 0
      have hKh (k : ℕ) (hk : k < m + 1) : (K k).IsHomogeneous k := by
        dsimp only [K]
        rw [dite_eq_left hk]
        exact (Classical.choose_spec (ih k hk)).1
      have hKe (k : ℕ) (hk : k < m + 1) (u v : ℝ) :
          MvPolynomial.eval ![u, v] (K k) =
            iteratedDeriv k (ProbabilityTheory.cgf
              (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) mu) 0 := by
        dsimp only [K]
        rw [dite_eq_left hk]
        exact (Classical.choose_spec (ih k hk)).2 u v
      let P : MvPolynomial (Fin 2) ℝ := M (m + 1) -
        ∑ j ∈ Finset.range m,
          MvPolynomial.C (m.choose j : ℝ) * K (j + 1) * M (m - j)
      refine ⟨P, (hMh (m + 1)).sub ?_, ?_⟩
      · apply MvPolynomial.IsHomogeneous.sum
        intro j hj
        have hjlt : j < m := Finset.mem_range.mp hj
        have hdeg : j + 1 + (m - j) = m + 1 := by omega
        simpa only [hdeg] using
          ((hKh (j + 1) (by omega)).C_mul (m.choose j : ℝ)).mul (hMh (m - j))
      · intro u v
        have hr := actual_moment_cgf_derivative_recursion mu
          (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) (h0 u v) m
        rw [Finset.sum_range_succ] at hr
        have hlast :
            (m.choose m : ℝ) *
                iteratedDeriv (m + 1) (ProbabilityTheory.cgf
                  (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) mu) 0 *
              (∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ (m - m) ∂mu) =
            iteratedDeriv (m + 1) (ProbabilityTheory.cgf
              (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) mu) 0 := by simp
        rw [hlast] at hr
        calc
          MvPolynomial.eval ![u, v] P =
              MvPolynomial.eval ![u, v] (M (m + 1)) -
                ∑ j ∈ Finset.range m, (m.choose j : ℝ) *
                  MvPolynomial.eval ![u, v] (K (j + 1)) *
                    MvPolynomial.eval ![u, v] (M (m - j)) := by
            simp [P]
          _ = (∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ (m + 1) ∂mu) -
                ∑ j ∈ Finset.range m, (m.choose j : ℝ) *
                  iteratedDeriv (j + 1) (ProbabilityTheory.cgf
                    (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) mu) 0 *
                    (∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ (m - j) ∂mu) := by
            rw [hMe (m + 1) u v]
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            rw [hKe (j + 1) (by have := Finset.mem_range.mp hj; omega) u v,
              hMe (m - j) u v]
          _ = _ := by linarith [hr]

end
end Shao.OQ3
