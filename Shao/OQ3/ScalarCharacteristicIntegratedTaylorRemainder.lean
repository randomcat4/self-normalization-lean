import Shao.OQ3.ImaginaryExponentialTaylorRemainder
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem scalar_characteristic_integrated_taylor_remainder
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (m : ℕ)
    (hM : Integrable (fun x : ℝ => |x| ^ m) ν) (t : ℝ) :
    let e : ℝ → ℂ := fun x => Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)
    let P : ℝ → ℂ := fun x =>
      ∑ j ∈ Finset.range m, (((t * x : ℝ) : ℂ) * Complex.I) ^ j / (j.factorial : ℂ)
    Integrable e ν ∧ Integrable P ν ∧ Integrable (fun x => e x - P x) ν ∧
      ‖(∫ x, e x ∂ν) - (∫ x, P x ∂ν)‖ ≤
        (Real.exp 1 + (m : ℝ) + 1) * |t| ^ m * (∫ x, |x| ^ m ∂ν) := by
  classical
  intro e P
  let C : ℝ := (Real.exp 1 + (m : ℝ) + 1) * |t| ^ m
  have hec : Continuous e := by
    dsimp [e]
    fun_prop
  have hPc : Continuous P := by
    dsimp [P]
    fun_prop
  have he : Integrable e ν := by
    apply (integrable_const (1 : ℝ)).mono' hec.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by
      simp only [e, Complex.norm_exp_ofReal_mul_I, le_refl])
  have hbound : ∀ x : ℝ, ‖e x - P x‖ ≤ C * |x| ^ m := by
    intro x
    calc
      _ ≤ (Real.exp 1 + (m : ℝ) + 1) * |t * x| ^ m :=
        imaginary_exponential_taylor_remainder_bound m (t * x)
      _ = C * |x| ^ m := by
        simp only [C, abs_mul, mul_pow, mul_assoc]
  have hmajor : Integrable (fun x : ℝ => C * |x| ^ m) ν := hM.const_mul C
  have hr : Integrable (fun x => e x - P x) ν :=
    hmajor.mono' (hec.sub hPc).aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  have hP : Integrable P ν := by
    exact (he.sub hr).congr (Filter.Eventually.of_forall (fun x =>
      sub_sub_cancel (e x) (P x)))
  refine ⟨he, hP, hr, ?_⟩
  calc
    _ = ‖∫ x, e x - P x ∂ν‖ := by rw [integral_sub he hP]
    _ ≤ ∫ x, ‖e x - P x‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ x, C * |x| ^ m ∂ν := integral_mono hr.norm hmajor hbound
    _ = (Real.exp 1 + (m : ℝ) + 1) * |t| ^ m * (∫ x, |x| ^ m ∂ν) := by
      rw [integral_const_mul]

end
end Shao.OQ3

