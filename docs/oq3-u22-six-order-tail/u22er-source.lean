import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators Topology
noncomputable section

theorem centered_actual_cgf_normalized_octic_polynomial
    {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (X : Ω → ℝ)
    (h0 : 0 ∈ interior (ProbabilityTheory.integrableExpSet X mu))
    (hmean : (∫ w, X w ∂mu) = 0) (n : ℕ) (hn : 1 ≤ n) :
    let kappa : ℕ → ℝ := fun j => iteratedDeriv j (ProbabilityTheory.cgf X mu) 0
    let Qn8 : ℂ := ∑ j ∈ Finset.range 9,
      (Complex.I ^ j / (j.factorial : ℂ)) * (kappa j : ℂ) *
        (n : ℂ) / (Real.sqrt (n : ℝ) : ℂ) ^ j
    Qn8 = -((∫ w, X w ^ 2 ∂mu : ℝ) : ℂ) / 2 +
      ∑ j ∈ Finset.range 6,
        (Complex.I ^ (j + 3) / ((j + 3).factorial : ℂ)) *
          (kappa (j + 3) : ℂ) / (Real.sqrt (n : ℝ) : ℂ) ^ (j + 1) := by
  classical
  intro kappa Qn8
  have hderiv : deriv (ProbabilityTheory.cgf X mu) 0 = 0 := by
    rw [ProbabilityTheory.deriv_cgf_zero h0, hmean, zero_div]
  have hk0 : kappa 0 = 0 := by simp [kappa]
  have hk1 : kappa 1 = 0 := by simpa [kappa] using hderiv
  have hk2 : kappa 2 = ∫ w, X w ^ 2 ∂mu := by
    dsimp only [kappa]
    rw [ProbabilityTheory.iteratedDeriv_two_cgf h0]
    simp [hderiv]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnR).ne'
  have hsnC : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsn
  have hsqC : (Real.sqrt (n : ℝ) : ℂ) ^ 2 = (n : ℂ) := by
    exact_mod_cast Real.sq_sqrt hnR.le
  dsimp only [Qn8]
  norm_num [Finset.sum_range_succ, hk0, hk1, hk2, pow_succ, Complex.I_sq]
  rw [← hsqC]
  field_simp [hsnC] <;> ring

end
end Shao.OQ3
