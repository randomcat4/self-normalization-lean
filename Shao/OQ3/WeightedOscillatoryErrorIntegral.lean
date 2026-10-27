import Shao.OQ3.ComplexGaussianWeightedLocalIntegral

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem pair_weighted_oscillatory_error_integral_bound
    (e : (ℝ × ℝ) → ℂ) (he : Continuous e)
    (s : Set (ℝ × ℝ)) (k : ℕ)
    (hInt : IntegrableOn (fun z : ℝ × ℝ =>
      Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ k * ‖e z‖) s) :
    let weight : (ℝ × ℝ) → ℝ := fun z =>
      Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ k
    let kernel : (ℝ × ℝ) → (ℝ × ℝ) → ℂ := fun x z =>
      Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ))
    ∀ x : ℝ × ℝ,
      IntegrableOn (fun z => kernel x z * (weight z : ℂ) * e z) s ∧
        ‖∫ z in s, kernel x z * (weight z : ℂ) * e z‖ ≤
          ∫ z in s, weight z * ‖e z‖ := by
  intro weight kernel x
  have hw : Continuous weight := by dsimp [weight]; fun_prop
  have hw0 (z : ℝ × ℝ) : 0 ≤ weight z := by
    dsimp [weight]
    positivity
  have hkernel : Continuous (kernel x) := by dsimp [kernel]; fun_prop
  have hkernelNorm (z : ℝ × ℝ) : ‖kernel x z‖ = 1 := by
    simp [kernel, Complex.norm_exp, Complex.mul_re]
  have hnorm (z : ℝ × ℝ) :
      ‖kernel x z * (weight z : ℂ) * e z‖ = weight z * ‖e z‖ := by
    rw [norm_mul, norm_mul, hkernelNorm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hw0 z), one_mul]
  have hcomplex : Continuous
      (fun z : ℝ × ℝ => kernel x z * (weight z : ℂ) * e z) := by
    fun_prop
  have hi : IntegrableOn
      (fun z : ℝ × ℝ => kernel x z * (weight z : ℂ) * e z) s := by
    apply hInt.mono' hcomplex.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => (hnorm z).le)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ z in s, ‖kernel x z * (weight z : ℂ) * e z‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ z in s, weight z * ‖e z‖ :=
      integral_congr_ae (Filter.Eventually.of_forall hnorm)

end
end Shao.OQ3
