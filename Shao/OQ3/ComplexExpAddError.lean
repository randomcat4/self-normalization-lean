import Mathlib.Analysis.Complex.Trigonometric

namespace Shao.OQ3
open scoped BigOperators
noncomputable section

theorem norm_complex_exp_add_error (z e : ℂ) :
    ‖Complex.exp (z + e) - Complex.exp z‖ ≤
      ‖e‖ * Real.exp (z.re + ‖e‖) := by
  have h : ‖Complex.exp e - 1‖ ≤ ‖e‖ * Real.exp ‖e‖ := by
    simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp e 1
  have hid : Complex.exp (z + e) - Complex.exp z =
      Complex.exp z * (Complex.exp e - 1) := by
    rw [Complex.exp_add]
    ring
  calc
    ‖Complex.exp (z + e) - Complex.exp z‖ =
        Real.exp z.re * ‖Complex.exp e - 1‖ := by
      rw [hid, Complex.norm_mul, Complex.norm_exp]
    _ ≤ Real.exp z.re * (‖e‖ * Real.exp ‖e‖) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = ‖e‖ * Real.exp (z.re + ‖e‖) := by
      rw [Real.exp_add]
      ring

theorem norm_complex_exp_add_error_of_re_le (z e : ℂ) (a b : ℝ)
    (hz : z.re ≤ -a) (he : ‖e‖ ≤ b) (hb : b ≤ a / 2) :
    ‖Complex.exp (z + e) - Complex.exp z‖ ≤
      ‖e‖ * Real.exp (-a / 2) := by
  have hexp : Real.exp (z.re + ‖e‖) ≤ Real.exp (-a / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  exact (norm_complex_exp_add_error z e).trans
    (mul_le_mul_of_nonneg_left hexp (norm_nonneg e))

end
end Shao.OQ3
