import Shao.OQ3.GaussianDampedWeightedErrorIntegral

namespace Shao.OQ3
open MeasureTheory
noncomputable section

theorem pair_gaussian_reference_damping_error_bound
    (P : (ℝ × ℝ) → ℂ) (hPc : Continuous P) (hP : Integrable P)
    (hQP : Integrable (fun z : ℝ × ℝ => (z.1 ^ 2 + z.2 ^ 2) * ‖P z‖))
    (b : ℝ) (hb : 0 ≤ b) :
    let damping : (ℝ × ℝ) → ℝ := fun z => Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2))
    let kernel : (ℝ × ℝ) → (ℝ × ℝ) → ℂ := fun x z =>
      Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ))
    ∀ x : ℝ × ℝ,
      Integrable (fun z => kernel x z * ((damping z : ℂ) * P z)) ∧
        Integrable (fun z => kernel x z * P z) ∧
          ‖(∫ z : ℝ × ℝ, kernel x z * ((damping z : ℂ) * P z)) -
            (∫ z : ℝ × ℝ, kernel x z * P z)‖ ≤
              b * (∫ z : ℝ × ℝ, (z.1 ^ 2 + z.2 ^ 2) * ‖P z‖) := by
  intro damping kernel
  have hd : Continuous damping := by dsimp [damping]; fun_prop
  have hd0 (z : ℝ × ℝ) : 0 ≤ damping z := (Real.exp_pos _).le
  have hd1 (z : ℝ × ℝ) : damping z ≤ 1 := by
    apply Real.exp_le_one_iff.2
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb)
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hrem (z : ℝ × ℝ) : 1 - damping z ≤ b * (z.1 ^ 2 + z.2 ^ 2) := by
    have h := Real.add_one_le_exp (-b * (z.1 ^ 2 + z.2 ^ 2))
    dsimp only [damping]
    linarith
  have hnorm (z : ℝ × ℝ) :
      ‖(damping z : ℂ) * P z - P z‖ ≤ b * ((z.1 ^ 2 + z.2 ^ 2) * ‖P z‖) := by
    have hid : (damping z : ℂ) * P z - P z = ((damping z - 1 : ℝ) : ℂ) * P z := by
      push_cast
      ring
    rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (hd1 z))]
    have h := mul_le_mul_of_nonneg_right (hrem z) (norm_nonneg (P z))
    nlinarith [h]
  intro x
  have hk : Continuous (kernel x) := by dsimp [kernel]; fun_prop
  have hkNorm (z : ℝ × ℝ) : ‖kernel x z‖ = 1 := by
    simp [kernel, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hi : Integrable (fun z => kernel x z * P z) := by
    apply hP.norm.mono' (hk.mul hPc).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by rw [norm_mul, hkNorm, one_mul])
  have hiD : Integrable (fun z => kernel x z * ((damping z : ℂ) * P z)) := by
    apply hP.norm.mono' (by
      have h : Continuous (fun z => kernel x z * ((damping z : ℂ) * P z)) := by fun_prop
      exact h.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun z => by
      rw [norm_mul, hkNorm, one_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hd0 z)]
      exact mul_le_of_le_one_left (norm_nonneg _) (hd1 z))
  refine ⟨hiD, hi, ?_⟩
  rw [← integral_sub hiD hi]
  calc
    _ ≤ ∫ z : ℝ × ℝ, ‖kernel x z * ((damping z : ℂ) * P z) - kernel x z * P z‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z : ℝ × ℝ, b * ((z.1 ^ 2 + z.2 ^ 2) * ‖P z‖) := by
      apply integral_mono (hiD.sub hi).norm (hQP.const_mul b)
      intro z
      rw [← mul_sub, norm_mul, hkNorm, one_mul]
      exact hnorm z
    _ = _ := integral_const_mul _ _

end
end Shao.OQ3
