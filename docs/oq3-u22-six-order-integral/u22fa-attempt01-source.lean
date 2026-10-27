import Shao.OQ3.DirectionalMomentPolynomialContinuity
import Shao.OQ3.ActualMomentCumulantRecurrence

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

set_option maxHeartbeats 1000000 in
theorem continuous_directional_actual_cgf_cumulants
    (mu : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure mu]
    (h0 : ∀ u v : ℝ, 0 ∈ interior (ProbabilityTheory.integrableExpSet
      (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) mu))
    (hM : ∀ k : ℕ, Integrable (fun y : Fin 2 → ℝ =>
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ k) mu) :
    let X : (ℝ × ℝ) → (Fin 2 → ℝ) → ℝ :=
      fun z y => z.1 * y 0 + z.2 * y 1
    let kappa : ℕ → (ℝ × ℝ) → ℝ :=
      fun k z => iteratedDeriv k (ProbabilityTheory.cgf (X z) mu) 0
    ∀ k : ℕ, Continuous (kappa k) := by
  intro X kappa
  let m : ℕ → (ℝ × ℝ) → ℝ := fun j z =>
    ∫ y : Fin 2 → ℝ, X z y ^ j ∂mu
  have hm0 (z : ℝ × ℝ) : m 0 z = 1 := by simp [m]
  have hmcont (j : ℕ) : Continuous (m j) :=
    (pair_directional_moment_binomial_continuous mu j (hM j)).2.2
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      have hz : kappa 0 = (fun _ : ℝ × ℝ => (0 : ℝ)) := by
        funext z
        simp [kappa]
      rw [hz]
      exact continuous_const
    | succ n =>
      have heq : kappa (n + 1) = fun z => m (n + 1) z -
          ∑ j ∈ Finset.range n, (n.choose j : ℝ) * kappa (j + 1) z * m (n - j) z := by
        funext z
        have hrec : m (n + 1) z =
            ∑ j ∈ Finset.range (n + 1),
              (n.choose j : ℝ) * kappa (j + 1) z * m (n - j) z :=
          actual_moment_cgf_derivative_recursion mu (X z) (h0 z.1 z.2) n
        rw [Finset.sum_range_succ] at hrec
        simp only [Nat.choose_self, Nat.sub_self, Nat.cast_one, one_mul, hm0, mul_one] at hrec
        linarith only [hrec]
      rw [heq]
      apply (hmcont (n + 1)).sub
      apply continuous_finset_sum
      intro j hj
      exact (continuous_const.mul
        (ih (j + 1) (Nat.succ_lt_succ (Finset.mem_range.mp hj)))).mul (hmcont (n - j))

set_option maxHeartbeats 1000000 in
theorem continuous_actual_cgf_six_order_edgeworth_polynomial
    (mu : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure mu]
    (h0 : ∀ u v : ℝ, 0 ∈ interior (ProbabilityTheory.integrableExpSet
      (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) mu))
    (hM : ∀ k : ℕ, Integrable (fun y : Fin 2 → ℝ =>
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ k) mu) (n : ℕ) :
    let X : (ℝ × ℝ) → (Fin 2 → ℝ) → ℝ :=
      fun z y => z.1 * y 0 + z.2 * y 1
    let kappa : ℕ → (ℝ × ℝ) → ℝ :=
      fun k z => iteratedDeriv k (ProbabilityTheory.cgf (X z) mu) 0
    let a : (ℝ × ℝ) → Fin 6 → ℂ := fun z j =>
      (Complex.I ^ (j.val + 3) / ((j.val + 3).factorial : ℂ)) *
        (kappa (j.val + 3) z : ℂ) / (Real.sqrt (n : ℝ) : ℂ) ^ (j.val + 1)
    let Pn : (ℝ × ℝ) → ℂ := fun z =>
      Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2) *
        ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
          ∑ sigma : Fin q.val → Fin 6,
            if (∑ i, ((sigma i).val + 1)) ≤ 6 then ∏ i, a z (sigma i) else 0
    Continuous Pn := by
  intro X kappa a Pn
  have hk (k : ℕ) : Continuous (kappa k) :=
    continuous_directional_actual_cgf_cumulants mu h0 hM k
  have ha (j : Fin 6) : Continuous (fun z : ℝ × ℝ => a z j) := by
    dsimp only [a]
    exact (continuous_const.mul (Complex.continuous_ofReal.comp (hk (j.val + 3)))).div_const _
  dsimp only [Pn]
  apply Continuous.mul (by fun_prop)
  apply continuous_finset_sum
  intro q hq
  apply continuous_const.mul
  apply continuous_finset_sum
  intro sigma hsigma
  by_cases h : (∑ i, ((sigma i).val + 1)) ≤ 6
  · simp only [if_pos h]
    exact continuous_finset_prod _ (fun i hi => ha (sigma i))
  · simp only [if_neg h]
    exact continuous_const

end
end Shao.OQ3
