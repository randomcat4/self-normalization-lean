import Shao.OQ3.WeightedOscillatoryErrorIntegral

namespace Shao.OQ3
open MeasureTheory
noncomputable section

theorem pair_gaussian_damped_weighted_error_integral_bound
    (e : (ℝ × ℝ) → ℂ) (he : Continuous e)
    (s : Set (ℝ × ℝ)) (k : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hInt : IntegrableOn (fun z : ℝ × ℝ =>
      Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ k * ‖e z‖) s) :
    let weight : (ℝ × ℝ) → ℝ := fun z =>
      Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ k
    let damping : (ℝ × ℝ) → ℝ := fun z => Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2))
    let kernel : (ℝ × ℝ) → (ℝ × ℝ) → ℂ := fun x z =>
      Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ))
    IntegrableOn (fun z => weight z * ‖(damping z : ℂ) * e z‖) s ∧
      (∫ z in s, weight z * ‖(damping z : ℂ) * e z‖) ≤
        ∫ z in s, weight z * ‖e z‖ ∧
      ∀ x : ℝ × ℝ,
        IntegrableOn (fun z => kernel x z * (weight z : ℂ) *
          ((damping z : ℂ) * e z)) s ∧
          ‖∫ z in s, kernel x z * (weight z : ℂ) * ((damping z : ℂ) * e z)‖ ≤
            ∫ z in s, weight z * ‖e z‖ := by
  intro weight damping kernel
  let eD : (ℝ × ℝ) → ℂ := fun z => (damping z : ℂ) * e z
  have hw : Continuous weight := by dsimp [weight]; fun_prop
  have hd : Continuous damping := by dsimp [damping]; fun_prop
  have hDE : Continuous eD := by dsimp [eD]; fun_prop
  have hw0 (z : ℝ × ℝ) : 0 ≤ weight z := by dsimp [weight]; positivity
  have hd0 (z : ℝ × ℝ) : 0 ≤ damping z := (Real.exp_pos _).le
  have hd1 (z : ℝ × ℝ) : damping z ≤ 1 := by
    calc
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by
        have hQ : 0 ≤ z.1 ^ 2 + z.2 ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) hQ)
      _ = 1 := Real.exp_zero
  have hNorm (z : ℝ × ℝ) : ‖eD z‖ ≤ ‖e z‖ := by
    change ‖(damping z : ℂ) * e z‖ ≤ ‖e z‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd0 z)]
    calc
      damping z * ‖e z‖ ≤ 1 * ‖e z‖ :=
        mul_le_mul_of_nonneg_right (hd1 z) (norm_nonneg _)
      _ = ‖e z‖ := one_mul _
  have hDInt : IntegrableOn (fun z => weight z * ‖eD z‖) s := by
    apply hInt.mono' (hw.mul hDE.norm).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by
      change ‖weight z * ‖eD z‖‖ ≤ weight z * ‖e z‖
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 z) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hNorm z) (hw0 z))
  have hComp : (∫ z in s, weight z * ‖eD z‖) ≤
      ∫ z in s, weight z * ‖e z‖ :=
    integral_mono hDInt hInt (fun z => mul_le_mul_of_nonneg_left (hNorm z) (hw0 z))
  have H := pair_weighted_oscillatory_error_integral_bound eD hDE s k hDInt
  refine ⟨hDInt, hComp, ?_⟩
  intro x
  exact ⟨(H x).1, (H x).2.trans hComp⟩

end
end Shao.OQ3
