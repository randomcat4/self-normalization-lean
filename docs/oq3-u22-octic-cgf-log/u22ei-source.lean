import Shao.OQ3.PairMomentEdgeworthExponentialError
import Shao.OQ3.ActualMomentCumulantRecurrence

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators Topology
noncomputable section

theorem uniform_pair_cgf_cumulant_bounds
    {ι : Type*} (law : ι → Measure (Fin 2 → ℝ))
    (hprob : ∀ i, IsProbabilityMeasure (law i))
    (h0 : ∀ i, ∀ u v : ℝ, 0 ∈ interior (ProbabilityTheory.integrableExpSet
      (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) (law i)))
    (M : ℕ → ℝ)
    (hI : ∀ k : ℕ, ∀ i, Integrable
      (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ k) (law i))
    (hM : ∀ k : ℕ, ∀ i, (∫ y : Fin 2 → ℝ,
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ k ∂law i) ≤ M k) :
    ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ i, ∀ u v : ℝ,
      |iteratedDeriv k (ProbabilityTheory.cgf
        (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) (law i)) 0| ≤
        C * Real.sqrt (u ^ 2 + v ^ 2) ^ k := by
  classical
  let N : ℕ → ℝ := fun j => |M j| + 1
  have hN (j : ℕ) : 0 < N j := by dsimp [N]; positivity
  have hm (i : ι) (u v : ℝ) (j : ℕ) :
      |∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ j ∂law i| ≤
        N j * Real.sqrt (u ^ 2 + v ^ 2) ^ j := by
    have hb := (pair_projection_signed_moment_bound (law i) j (hI j i) u v).2
    have hMN : M j ≤ N j := (le_abs_self _).trans (by dsimp [N]; linarith)
    exact hb.trans (by
      calc
        _ ≤ Real.sqrt (u ^ 2 + v ^ 2) ^ j * N j :=
          mul_le_mul_of_nonneg_left ((hM j i).trans hMN) (by positivity)
        _ = _ := mul_comm _ _)
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      refine ⟨1, zero_lt_one, ?_⟩
      intro i u v
      letI : IsProbabilityMeasure (law i) := hprob i
      simp
    | succ n =>
      have hprev : ∀ j : ℕ, ∃ B : ℝ, 0 < B ∧
          (j < n → ∀ i, ∀ u v : ℝ,
            |iteratedDeriv (j + 1) (ProbabilityTheory.cgf
              (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) (law i)) 0| ≤
                B * Real.sqrt (u ^ 2 + v ^ 2) ^ (j + 1)) := by
        intro j
        by_cases hj : j < n
        · obtain ⟨B, hB, hb⟩ := ih (j + 1) (by omega)
          exact ⟨B, hB, fun _ => hb⟩
        · exact ⟨1, zero_lt_one, fun h => False.elim (hj h)⟩
      choose B hB hb using hprev
      let C : ℝ := N (n + 1) +
        ∑ j ∈ Finset.range n, (n.choose j : ℝ) * B j * N (n - j) + 1
      have hsum : 0 ≤ ∑ j ∈ Finset.range n,
          (n.choose j : ℝ) * B j * N (n - j) := by
        apply Finset.sum_nonneg
        intro j hj
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB j).le) (hN _).le
      have hC : 0 < C := by dsimp [C]; linarith [hN (n + 1)]
      refine ⟨C, hC, ?_⟩
      intro i u v
      letI : IsProbabilityMeasure (law i) := hprob i
      let r : ℝ := Real.sqrt (u ^ 2 + v ^ 2)
      let X : (Fin 2 → ℝ) → ℝ := fun y => u * y 0 + v * y 1
      let m : ℕ → ℝ := fun j => ∫ y : Fin 2 → ℝ, X y ^ j ∂law i
      let K : ℕ → ℝ := fun j => iteratedDeriv j (ProbabilityTheory.cgf X (law i)) 0
      have hr : 0 ≤ r := Real.sqrt_nonneg _
      have hm0 : m 0 = 1 := by simp [m]
      have hrec : m (n + 1) =
          ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * K (j + 1) * m (n - j) :=
        actual_moment_cgf_derivative_recursion (law i) X (h0 i u v) n
      rw [Finset.sum_range_succ] at hrec
      simp only [Nat.choose_self, Nat.sub_self, Nat.cast_one, one_mul, hm0, mul_one] at hrec
      have hsolve : K (n + 1) = m (n + 1) -
          ∑ j ∈ Finset.range n, (n.choose j : ℝ) * K (j + 1) * m (n - j) := by
        linarith only [hrec]
      have hterm (j : ℕ) (hj : j ∈ Finset.range n) :
          |(n.choose j : ℝ) * K (j + 1) * m (n - j)| ≤
            ((n.choose j : ℝ) * B j * N (n - j)) * r ^ (n + 1) := by
        have hjn : j < n := Finset.mem_range.mp hj
        have hk : |K (j + 1)| ≤ B j * r ^ (j + 1) := hb j hjn i u v
        have hmoment : |m (n - j)| ≤ N (n - j) * r ^ (n - j) := hm i u v (n - j)
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        calc
          _ ≤ (n.choose j : ℝ) * (B j * r ^ (j + 1)) *
              (N (n - j) * r ^ (n - j)) := by
            apply mul_le_mul
              (mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg _)) hmoment (abs_nonneg _)
            exact mul_nonneg (Nat.cast_nonneg _)
              (mul_nonneg (hB j).le (pow_nonneg hr _))
          _ = ((n.choose j : ℝ) * B j * N (n - j)) *
              (r ^ (j + 1) * r ^ (n - j)) := by ring
          _ = _ := by rw [← pow_add]; congr 2; omega
      change |K (n + 1)| ≤ C * r ^ (n + 1)
      calc
        _ = |m (n + 1) - ∑ j ∈ Finset.range n,
            (n.choose j : ℝ) * K (j + 1) * m (n - j)| := congrArg abs hsolve
        _ ≤ |m (n + 1)| + |∑ j ∈ Finset.range n,
            (n.choose j : ℝ) * K (j + 1) * m (n - j)| := abs_sub _ _
        _ ≤ N (n + 1) * r ^ (n + 1) + ∑ j ∈ Finset.range n,
            |(n.choose j : ℝ) * K (j + 1) * m (n - j)| :=
          add_le_add (hm i u v (n + 1)) (Finset.abs_sum_le_sum_abs _ _)
        _ ≤ N (n + 1) * r ^ (n + 1) + ∑ j ∈ Finset.range n,
            ((n.choose j : ℝ) * B j * N (n - j)) * r ^ (n + 1) :=
          add_le_add (le_refl _) (Finset.sum_le_sum hterm)
        _ = (N (n + 1) + ∑ j ∈ Finset.range n,
            (n.choose j : ℝ) * B j * N (n - j)) * r ^ (n + 1) := by
          rw [← Finset.sum_mul]; ring
        _ ≤ C * r ^ (n + 1) :=
          mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (pow_nonneg hr _)

end
end Shao.OQ3
