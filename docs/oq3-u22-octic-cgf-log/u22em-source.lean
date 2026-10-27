import Shao.OQ3.ActualMomentCumulantRecurrence
import Shao.OQ3.ScalarCGFThirdFourthDerivatives
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators Topology
noncomputable section

theorem centered_actual_cgf_octic_log_polynomial
    {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (X : Ω → ℝ)
    (h0 : 0 ∈ interior (ProbabilityTheory.integrableExpSet X mu))
    (hmean : (∫ w, X w ∂mu) = 0) :
    let m : ℕ → ℝ := fun k => ∫ w, (X w) ^ k ∂mu
    let kappa : ℕ → ℝ := fun k => iteratedDeriv k (ProbabilityTheory.cgf X mu) 0
    let a : ℂ := -(m 2 : ℂ) / 2
    let b : ℂ := -Complex.I * (m 3 : ℂ) / 6
    let c : ℂ := (m 4 : ℂ) / 24
    let d : ℂ := Complex.I * (m 5 : ℂ) / 120
    let e : ℂ := -(m 6 : ℂ) / 720
    let f : ℂ := -Complex.I * (m 7 : ℂ) / 5040
    let g : ℂ := (m 8 : ℂ) / 40320
    let Q : ℂ := a + b + c + d + e + f + g -
      (a ^ 2 + 2 * a * b + 2 * a * c + b ^ 2 + 2 * a * d +
        2 * b * c + 2 * a * e + 2 * b * d + c ^ 2) / 2 +
      (a ^ 3 + 3 * a ^ 2 * b + 3 * a ^ 2 * c + 3 * a * b ^ 2) / 3 - a ^ 4 / 4
    Q = ∑ j ∈ Finset.range 9,
      (Complex.I ^ j / (j.factorial : ℂ)) * (kappa j : ℂ) := by
  intro m kappa a b c d e f g Q
  have hm0 : m 0 = 1 := by simp [m]
  have hm1 : m 1 = 0 := by simpa [m] using hmean
  have hk0 : kappa 0 = 0 := by simp [kappa]
  have hk1 : kappa 1 = 0 := by
    simpa [kappa, iteratedDeriv_one, hmean] using ProbabilityTheory.deriv_cgf_zero h0
  have hr := actual_moment_cgf_derivative_recursion mu X h0 1
  change m 2 = ∑ j ∈ Finset.range 2,
    (Nat.choose 1 j : ℝ) * kappa (j + 1) * m (1 - j) at hr
  norm_num [Finset.sum_range_succ, Nat.choose, hm0, hm1, hk1] at hr
  have hk2 : kappa 2 = m 2 := hr.symm
  obtain ⟨hk3, hk4⟩ := centered_cgf_third_fourth_derivatives mu X h0 hmean
  change kappa 3 = m 3 at hk3
  change kappa 4 = m 4 - 3 * (m 2) ^ 2 at hk4
  obtain ⟨hk5, hk6, hk7, hk8⟩ := centered_cgf_fifth_to_eighth_derivatives mu X h0 hmean
  change kappa 5 = m 5 - 10 * m 3 * m 2 at hk5
  change kappa 6 = m 6 - 15 * m 4 * m 2 - 10 * (m 3) ^ 2 + 30 * (m 2) ^ 3 at hk6
  change kappa 7 = m 7 - 21 * m 5 * m 2 - 35 * m 4 * m 3 +
    210 * m 3 * (m 2) ^ 2 at hk7
  change kappa 8 = m 8 - 28 * m 6 * m 2 - 56 * m 5 * m 3 - 35 * (m 4) ^ 2 +
    420 * m 4 * (m 2) ^ 2 + 560 * (m 3) ^ 2 * m 2 - 630 * (m 2) ^ 4 at hk8
  norm_num [Finset.sum_range_succ, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8,
    Q, a, b, c, d, e, f, g, pow_succ, Complex.I_sq]
  push_cast
  ring_nf
  norm_num [Complex.I_sq, pow_succ] <;> ring

end
end Shao.OQ3
