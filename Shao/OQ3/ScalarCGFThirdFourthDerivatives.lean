import Mathlib.Probability.Moments.MGFAnalytic

namespace Shao.OQ3
open MeasureTheory Filter
open scoped Topology
noncomputable section

theorem cgf_third_derivative_actual_moments
    {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (X : Ω → ℝ) (v : ℝ)
    (hv : v ∈ interior (ProbabilityTheory.integrableExpSet X mu)) :
    let M : ℕ → ℝ := fun k => ∫ w, (X w) ^ k * Real.exp (v * X w) ∂mu
    iteratedDeriv 3 (ProbabilityTheory.cgf X mu) v =
      M 3 / M 0 - 3 * M 2 * M 1 / (M 0) ^ 2 + 2 * (M 1) ^ 3 / (M 0) ^ 3 := by
  intro M
  let F : ℕ → ℝ → ℝ := fun k t => ∫ w, (X w) ^ k * Real.exp (t * X w) ∂mu
  have hF (k : ℕ) (t : ℝ)
      (ht : t ∈ interior (ProbabilityTheory.integrableExpSet X mu)) :
      HasDerivAt (F k) (F (k + 1) t) t :=
    ProbabilityTheory.hasDerivAt_integral_pow_mul_exp_real ht k
  have hpos : 0 < F 0 v := by
    simpa only [F, ProbabilityTheory.mgf, pow_zero, one_mul] using
      (ProbabilityTheory.mgf_pos (X := X) (μ := mu) (t := v) (interior_subset hv))
  have hlocal : iteratedDeriv 2 (ProbabilityTheory.cgf X mu) =ᶠ[𝓝 v]
      (F 2 / F 0 - (F 1 / F 0) ^ 2) := by
    filter_upwards [isOpen_interior.eventually_mem hv] with t ht
    simp only [Pi.sub_apply, Pi.div_apply, Pi.pow_apply]
    rw [ProbabilityTheory.iteratedDeriv_two_cgf ht, ProbabilityTheory.deriv_cgf ht]
    simp only [F, ProbabilityTheory.mgf, pow_zero, pow_one, one_mul]
  have hD := ((hF 2 v hv).div (hF 0 v hv) hpos.ne').sub
    (((hF 1 v hv).div (hF 0 v hv) hpos.ne').pow 2)
  rw [iteratedDeriv_succ, hlocal.deriv_eq, hD.deriv]
  change _ = F 3 v / F 0 v - 3 * F 2 v * F 1 v / (F 0 v) ^ 2 +
    2 * (F 1 v) ^ 3 / (F 0 v) ^ 3
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceSub, pow_one,
    Pi.div_apply, Pi.pow_apply]
  field_simp [hpos.ne'] <;> ring

theorem cgf_fourth_derivative_actual_moments
    {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (X : Ω → ℝ) (v : ℝ)
    (hv : v ∈ interior (ProbabilityTheory.integrableExpSet X mu)) :
    let M : ℕ → ℝ := fun k => ∫ w, (X w) ^ k * Real.exp (v * X w) ∂mu
    iteratedDeriv 4 (ProbabilityTheory.cgf X mu) v =
      M 4 / M 0 - 4 * M 3 * M 1 / (M 0) ^ 2 - 3 * (M 2) ^ 2 / (M 0) ^ 2 +
        12 * M 2 * (M 1) ^ 2 / (M 0) ^ 3 - 6 * (M 1) ^ 4 / (M 0) ^ 4 := by
  intro M
  let F : ℕ → ℝ → ℝ := fun k t => ∫ w, (X w) ^ k * Real.exp (t * X w) ∂mu
  have hF (k : ℕ) (t : ℝ)
      (ht : t ∈ interior (ProbabilityTheory.integrableExpSet X mu)) :
      HasDerivAt (F k) (F (k + 1) t) t :=
    ProbabilityTheory.hasDerivAt_integral_pow_mul_exp_real ht k
  have hpos : 0 < F 0 v := by
    simpa only [F, ProbabilityTheory.mgf, pow_zero, one_mul] using
      (ProbabilityTheory.mgf_pos (X := X) (μ := mu) (t := v) (interior_subset hv))
  have hlocal : iteratedDeriv 3 (ProbabilityTheory.cgf X mu) =ᶠ[𝓝 v]
      (F 3 / F 0 - (fun t => 3 * F 2 t) * F 1 / F 0 ^ 2 +
        (fun t => 2 * (F 1 ^ 3) t) / F 0 ^ 3) := by
    filter_upwards [isOpen_interior.eventually_mem hv] with t ht
    simpa only [Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.mul_apply, Pi.pow_apply] using
      cgf_third_derivative_actual_moments mu X t ht
  have hD := (((hF 3 v hv).div (hF 0 v hv) hpos.ne').sub
    ((((hF 2 v hv).const_mul 3).mul (hF 1 v hv)).div
      ((hF 0 v hv).pow 2) (pow_ne_zero 2 hpos.ne'))).add
    ((((hF 1 v hv).pow 3).const_mul 2).div
      ((hF 0 v hv).pow 3) (pow_ne_zero 3 hpos.ne'))
  rw [iteratedDeriv_succ, hlocal.deriv_eq, hD.deriv]
  change _ = F 4 v / F 0 v - 4 * F 3 v * F 1 v / (F 0 v) ^ 2 -
    3 * (F 2 v) ^ 2 / (F 0 v) ^ 2 +
      12 * F 2 v * (F 1 v) ^ 2 / (F 0 v) ^ 3 - 6 * (F 1 v) ^ 4 / (F 0 v) ^ 4
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceSub, pow_one,
    Pi.div_apply, Pi.mul_apply, Pi.pow_apply]
  field_simp [hpos.ne'] <;> ring

theorem centered_cgf_third_fourth_derivatives
    {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (X : Ω → ℝ)
    (h0 : 0 ∈ interior (ProbabilityTheory.integrableExpSet X mu))
    (hmean : (∫ w, X w ∂mu) = 0) :
    iteratedDeriv 3 (ProbabilityTheory.cgf X mu) 0 = (∫ w, (X w) ^ 3 ∂mu) ∧
      iteratedDeriv 4 (ProbabilityTheory.cgf X mu) 0 =
        (∫ w, (X w) ^ 4 ∂mu) - 3 * (∫ w, (X w) ^ 2 ∂mu) ^ 2 := by
  constructor
  · simpa [hmean] using cgf_third_derivative_actual_moments mu X 0 h0
  · simpa [hmean] using cgf_fourth_derivative_actual_moments mu X 0 h0

end
end Shao.OQ3
