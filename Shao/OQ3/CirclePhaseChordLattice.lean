import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace Shao.OQ3
noncomputable section

theorem circle_phase_chord_nearest_lattice (theta phi : ℝ) :
    let k : ℤ := round ((theta - phi) / (2 * Real.pi))
    let d : ℝ := |theta - phi - 2 * Real.pi * (k : ℝ)|
    d ≤ Real.pi ∧
      (∀ m : ℤ, d ≤ |theta - phi - 2 * Real.pi * (m : ℝ)|) ∧
      (2 / Real.pi) * d ≤
        ‖Complex.exp ((theta : ℂ) * Complex.I) - Complex.exp ((phi : ℂ) * Complex.I)‖ ∧
      ‖Complex.exp ((theta : ℂ) * Complex.I) - Complex.exp ((phi : ℂ) * Complex.I)‖ ≤ d := by
  intro k d
  let q : ℝ := (theta - phi) / (2 * Real.pi)
  let x : ℝ := theta - phi - 2 * Real.pi * (k : ℝ)
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hscale (m : ℤ) : |theta - phi - 2 * Real.pi * (m : ℝ)| =
      (2 * Real.pi) * |q - (m : ℝ)| := by
    calc
      _ = |(2 * Real.pi) * (q - (m : ℝ))| := by
        congr 1
        dsimp [q]
        field_simp
      _ = _ := by rw [abs_mul, abs_of_pos hp]
  have hd : d ≤ Real.pi := by
    change |theta - phi - 2 * Real.pi * (k : ℝ)| ≤ Real.pi
    rw [hscale]
    calc
      _ ≤ (2 * Real.pi) * (1 / 2) :=
        mul_le_mul_of_nonneg_left (abs_sub_round q) hp.le
      _ = _ := by ring
  have hnearest (m : ℤ) : d ≤ |theta - phi - 2 * Real.pi * (m : ℝ)| := by
    change |theta - phi - 2 * Real.pi * (k : ℝ)| ≤ _
    rw [hscale, hscale]
    exact mul_le_mul_of_nonneg_left (round_le q m) hp.le
  have hExp : Complex.exp ((x : ℂ) * Complex.I) =
      Complex.exp (((theta - phi : ℝ) : ℂ) * Complex.I) := by
    have harg : (x : ℂ) * Complex.I =
        (((theta - phi : ℝ) : ℂ) * Complex.I) -
          (k : ℂ) * (2 * Real.pi * Complex.I) := by
      dsimp [x]
      push_cast
      ring
    rw [harg, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]
  have hFactor :
      Complex.exp ((theta : ℂ) * Complex.I) - Complex.exp ((phi : ℂ) * Complex.I) =
        Complex.exp ((phi : ℂ) * Complex.I) *
          (Complex.exp (((theta - phi : ℝ) : ℂ) * Complex.I) - 1) := by
    have he : Complex.exp ((theta : ℂ) * Complex.I) =
        Complex.exp ((phi : ℂ) * Complex.I) *
          Complex.exp (((theta - phi : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [he]
    ring
  have hNorm :
      ‖Complex.exp ((theta : ℂ) * Complex.I) - Complex.exp ((phi : ℂ) * Complex.I)‖ =
        ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ := by
    rw [hFactor, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, hExp]
  have hx : |x| ≤ Real.pi := hd
  have hhalf : |x / 2| ≤ Real.pi / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hsin := Real.mul_abs_le_abs_sin hhalf
  have hNormSin : ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ =
      2 * |Real.sin (x / 2)| := by
    rw [mul_comm (x : ℂ) Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
    simp [Real.norm_eq_abs, abs_mul]
  refine ⟨hd, hnearest, ?_, ?_⟩
  · rw [hNorm]
    change (2 / Real.pi) * |x| ≤ _
    calc
      _ = 2 * ((2 / Real.pi) * |x / 2|) := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        ring
      _ ≤ 2 * |Real.sin (x / 2)| := mul_le_mul_of_nonneg_left hsin (by norm_num)
      _ = _ := hNormSin.symm
  · rw [hNorm]
    change ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ≤ |x|
    simpa only [mul_comm (x : ℂ) Complex.I, Real.norm_eq_abs] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x))

end
end Shao.OQ3
