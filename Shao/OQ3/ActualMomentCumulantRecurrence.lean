import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Shao.OQ3.ScalarCGFThirdFourthDerivatives

namespace Shao.OQ3
open MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section

theorem actual_moment_cgf_derivative_recursion
    {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (X : Ω → ℝ)
    (h0 : 0 ∈ interior (ProbabilityTheory.integrableExpSet X mu)) (n : ℕ) :
    (∫ w, (X w) ^ (n + 1) ∂mu) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        iteratedDeriv (j + 1) (ProbabilityTheory.cgf X mu) 0 *
          (∫ w, (X w) ^ (n - j) ∂mu) := by
  have heq : deriv (ProbabilityTheory.mgf X mu) =ᶠ[𝓝 (0 : ℝ)]
      (deriv (ProbabilityTheory.cgf X mu) * ProbabilityTheory.mgf X mu) := by
    filter_upwards [isOpen_interior.eventually_mem h0] with t ht
    change deriv (ProbabilityTheory.mgf X mu) t =
      deriv (ProbabilityTheory.cgf X mu) t * ProbabilityTheory.mgf X mu t
    rw [ProbabilityTheory.deriv_cgf ht, ProbabilityTheory.deriv_mgf ht]
    have hp := ProbabilityTheory.mgf_pos (X := X) (μ := mu) (t := t) (interior_subset ht)
    exact (div_mul_cancel₀ _ hp.ne').symm
  calc
    _ = iteratedDeriv (n + 1) (ProbabilityTheory.mgf X mu) 0 :=
      (ProbabilityTheory.iteratedDeriv_mgf_zero h0 (n + 1)).symm
    _ = iteratedDeriv n (deriv (ProbabilityTheory.mgf X mu)) 0 := by
      rw [iteratedDeriv_succ']
    _ = iteratedDeriv n (deriv (ProbabilityTheory.cgf X mu) * ProbabilityTheory.mgf X mu) 0 :=
      heq.iteratedDeriv_eq n
    _ = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        iteratedDeriv j (deriv (ProbabilityTheory.cgf X mu)) 0 *
          iteratedDeriv (n - j) (ProbabilityTheory.mgf X mu) 0 :=
      iteratedDeriv_mul (ProbabilityTheory.analyticAt_cgf h0).deriv.contDiffAt
        (ProbabilityTheory.analyticAt_mgf h0).contDiffAt
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← iteratedDeriv_succ', ProbabilityTheory.iteratedDeriv_mgf_zero h0 (n - j)]
      apply congrArg (fun a : ℝ =>
        (n.choose j : ℝ) * iteratedDeriv (j + 1) (ProbabilityTheory.cgf X mu) 0 * a)
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun w => by simp only [Pi.pow_apply])

theorem centered_cgf_fifth_to_eighth_derivatives
    {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (X : Ω → ℝ)
    (h0 : 0 ∈ interior (ProbabilityTheory.integrableExpSet X mu))
    (hmean : (∫ w, X w ∂mu) = 0) :
    let m : ℕ → ℝ := fun k => ∫ w, (X w) ^ k ∂mu
    let kappa : ℕ → ℝ := fun k => iteratedDeriv k (ProbabilityTheory.cgf X mu) 0
    kappa 5 = m 5 - 10 * m 3 * m 2 ∧
      kappa 6 = m 6 - 15 * m 4 * m 2 - 10 * (m 3) ^ 2 + 30 * (m 2) ^ 3 ∧
      kappa 7 = m 7 - 21 * m 5 * m 2 - 35 * m 4 * m 3 + 210 * m 3 * (m 2) ^ 2 ∧
      kappa 8 = m 8 - 28 * m 6 * m 2 - 56 * m 5 * m 3 - 35 * (m 4) ^ 2 +
        420 * m 4 * (m 2) ^ 2 + 560 * (m 3) ^ 2 * m 2 - 630 * (m 2) ^ 4 := by
  intro m kappa
  have hm0 : m 0 = 1 := by simp [m]
  have hm1 : m 1 = 0 := by simpa [m] using hmean
  have hk1 : kappa 1 = 0 := by
    simpa [kappa, iteratedDeriv_one, hmean] using ProbabilityTheory.deriv_cgf_zero h0
  have hk2 : kappa 2 = m 2 := by
    have h := ProbabilityTheory.iteratedDeriv_two_cgf h0
    rw [ProbabilityTheory.deriv_cgf_zero h0] at h
    simpa [kappa, m, hmean] using h
  obtain ⟨hk3, hk4⟩ := centered_cgf_third_fourth_derivatives mu X h0 hmean
  change kappa 3 = m 3 at hk3
  change kappa 4 = m 4 - 3 * (m 2) ^ 2 at hk4
  have hr (n : ℕ) : m (n + 1) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * kappa (j + 1) * m (n - j) :=
    actual_moment_cgf_derivative_recursion mu X h0 n
  have h5 := hr 4
  norm_num [Finset.sum_range_succ, Nat.choose, hm0, hm1, hk1, hk2, hk3, hk4] at h5
  have hk5 : kappa 5 = m 5 - 10 * m 3 * m 2 := by linear_combination -h5
  have h6 := hr 5
  norm_num [Finset.sum_range_succ, Nat.choose, hm0, hm1, hk1, hk2, hk3, hk4, hk5] at h6
  have hk6 : kappa 6 = m 6 - 15 * m 4 * m 2 - 10 * (m 3) ^ 2 + 30 * (m 2) ^ 3 := by
    linear_combination -h6
  have h7 := hr 6
  norm_num [Finset.sum_range_succ, Nat.choose, hm0, hm1, hk1, hk2, hk3, hk4, hk5, hk6] at h7
  have hk7 : kappa 7 = m 7 - 21 * m 5 * m 2 - 35 * m 4 * m 3 +
      210 * m 3 * (m 2) ^ 2 := by linear_combination -h7
  have h8 := hr 7
  norm_num [Finset.sum_range_succ, Nat.choose, hm0, hm1, hk1, hk2, hk3, hk4, hk5, hk6, hk7] at h8
  have hk8 : kappa 8 = m 8 - 28 * m 6 * m 2 - 56 * m 5 * m 3 - 35 * (m 4) ^ 2 +
      420 * m 4 * (m 2) ^ 2 + 560 * (m 3) ^ 2 * m 2 - 630 * (m 2) ^ 4 := by
    linear_combination -h8
  exact ⟨hk5, hk6, hk7, hk8⟩

end
end Shao.OQ3
