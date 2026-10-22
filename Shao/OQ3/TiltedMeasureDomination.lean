import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

namespace Shao.OQ3
open MeasureTheory
noncomputable section

private theorem square_le_of_abs_le (x M : ℝ) (hx : |x| ≤ M) : x ^ 2 ≤ M ^ 2 := by
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) hx 2

theorem quadratic_exp_integrable_of_ae_abs_le (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (u v : ℝ) :
    Integrable (fun x : ℝ => Real.exp (u * x + v * x ^ 2)) mu := by
  have _hC : 0 ≤ |u| * M + |v| * M ^ 2 :=
    add_nonneg (mul_nonneg (abs_nonneg u) hM) (mul_nonneg (abs_nonneg v) (sq_nonneg M))
  refine Integrable.of_bound (by fun_prop) (Real.exp (|u| * M + |v| * M ^ 2)) ?_
  filter_upwards [hb] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    u * x + v * x ^ 2 ≤ |u * x| + |v * x ^ 2| :=
      add_le_add (le_abs_self _) (le_abs_self _)
    _ = |u| * |x| + |v| * x ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg x)]
    _ ≤ |u| * M + |v| * M ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg u))
        (mul_le_mul_of_nonneg_left (square_le_of_abs_le x M hx) (abs_nonneg v))

theorem tilted_measure_domination_of_abs_sub_le (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (f g : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : Integrable (fun x => Real.exp (f x)) mu)
    (hg : Integrable (fun x => Real.exp (g x)) mu)
    (hfg : ∀ᵐ x ∂mu, |g x - f x| ≤ B) :
    ENNReal.ofReal (Real.exp (-2 * B)) • mu.tilted f ≤ mu.tilted g := by
  let Zf : ℝ := ∫ x, Real.exp (f x) ∂mu
  let Zg : ℝ := ∫ x, Real.exp (g x) ∂mu
  have hZf : 0 < Zf := integral_exp_pos hf
  have hZg : 0 < Zg := integral_exp_pos hg
  have _hscale : Real.exp (-2 * B) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hu : ∀ᵐ x ∂mu, Real.exp (g x) ≤ Real.exp B * Real.exp (f x) := by
    filter_upwards [hfg] with x hx
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hx).2])
  have hupper : Zg ≤ Real.exp B * Zf := by
    have hi := integral_mono_ae hg (hf.const_mul (Real.exp B)) hu
    simpa only [Zf, Zg, integral_const_mul] using hi
  have hc : Real.exp (-2 * B) * Real.exp B = Real.exp (-B) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold Measure.tilted
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  apply withDensity_mono
  filter_upwards [hfg] with x hx
  change ENNReal.ofReal (Real.exp (-2 * B)) *
      ENNReal.ofReal (Real.exp (f x) / Zf) ≤ ENNReal.ofReal (Real.exp (g x) / Zg)
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  have hlower : Real.exp (-B) * Real.exp (f x) ≤ Real.exp (g x) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hx).1])
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hZf hZg).mpr
  calc
    (Real.exp (-2 * B) * Real.exp (f x)) * Zg ≤
        (Real.exp (-2 * B) * Real.exp (f x)) * (Real.exp B * Zf) :=
      mul_le_mul_of_nonneg_left hupper (by positivity)
    _ = (Real.exp (-B) * Real.exp (f x)) * Zf := by
      calc
        _ = (Real.exp (-2 * B) * Real.exp B) * Real.exp (f x) * Zf := by ring
        _ = _ := by rw [hc]
    _ ≤ Real.exp (g x) * Zf := mul_le_mul_of_nonneg_right hlower hZf.le

theorem quadratic_tilted_measure_domination (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (u0 v0 u v : ℝ)
    (hu : |u - u0| ≤ L) (hv : |v - v0| ≤ L) :
    ENNReal.ofReal (Real.exp (-2 * (L * (M + M ^ 2)))) •
      mu.tilted (fun x => u0 * x + v0 * x ^ 2) ≤
        mu.tilted (fun x => u * x + v * x ^ 2) := by
  apply tilted_measure_domination_of_abs_sub_le mu _ _ (L * (M + M ^ 2)) (by positivity)
  · exact quadratic_exp_integrable_of_ae_abs_le mu M hM hb u0 v0
  · exact quadratic_exp_integrable_of_ae_abs_le mu M hM hb u v
  · filter_upwards [hb] with x hx
    rw [show (u * x + v * x ^ 2) - (u0 * x + v0 * x ^ 2) =
      (u - u0) * x + (v - v0) * x ^ 2 by ring]
    calc
      |(u - u0) * x + (v - v0) * x ^ 2| ≤
          |(u - u0) * x| + |(v - v0) * x ^ 2| := abs_add_le _ _
      _ = |u - u0| * |x| + |v - v0| * x ^ 2 := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg x)]
      _ ≤ L * M + L * M ^ 2 :=
        add_le_add (mul_le_mul hu hx (abs_nonneg x) hL)
          (mul_le_mul hv (square_le_of_abs_le x M hx) (sq_nonneg x) hL)
      _ = L * (M + M ^ 2) := by ring

end
end Shao.OQ3
