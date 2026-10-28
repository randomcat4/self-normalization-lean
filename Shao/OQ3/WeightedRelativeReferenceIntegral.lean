import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Ring

namespace Shao.OQ3
open MeasureTheory
noncomputable section

theorem nonnegative_weighted_relative_reference_error
    (phi reference f : (ℝ × ℝ) → ℝ)
    (hphi : Measurable phi) (href : Measurable reference) (hf : Measurable f)
    (hfi : Integrable f)
    (hf0 : ∀ z : ℝ × ℝ, 0 ≤ f z) (hphi0 : ∀ z : ℝ × ℝ, 0 ≤ phi z)
    (B delta : ℝ) (hB : 0 ≤ B) (hdelta : 0 ≤ delta)
    (hphiBound : ∀ z : ℝ × ℝ, phi z ≤ B)
    (herror : ∀ z : ℝ × ℝ, f z ≠ 0 → |reference z - phi z| ≤ delta * phi z) :
    Integrable (fun z : ℝ × ℝ => f z * phi z) ∧
      Integrable (fun z : ℝ × ℝ => f z * reference z) ∧
        0 ≤ (∫ z : ℝ × ℝ, f z * phi z) ∧
          |(∫ z : ℝ × ℝ, f z * reference z) -
            (∫ z : ℝ × ℝ, f z * phi z)| ≤ delta * (∫ z : ℝ × ℝ, f z * phi z) := by
  have hMainPoint (z : ℝ × ℝ) : ‖f z * phi z‖ ≤ B * f z := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 z) (hphi0 z))]
    calc
      _ ≤ f z * B := mul_le_mul_of_nonneg_left (hphiBound z) (hf0 z)
      _ = _ := mul_comm _ _
  have hiPhi : Integrable (fun z : ℝ × ℝ => f z * phi z) := by
    apply (hfi.const_mul B).mono' (hf.mul hphi).aestronglyMeasurable
    exact Filter.Eventually.of_forall hMainPoint
  have hDiffPoint (z : ℝ × ℝ) :
      ‖f z * (reference z - phi z)‖ ≤ delta * (f z * phi z) := by
    by_cases hz : f z = 0
    · simp [hz]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf0 z)]
    calc
      _ ≤ f z * (delta * phi z) := mul_le_mul_of_nonneg_left (herror z hz) (hf0 z)
      _ = _ := by ring
  have hiDiff : Integrable (fun z : ℝ × ℝ => f z * (reference z - phi z)) := by
    apply (hiPhi.const_mul delta).mono' (hf.mul (href.sub hphi)).aestronglyMeasurable
    exact Filter.Eventually.of_forall hDiffPoint
  have hiRef : Integrable (fun z : ℝ × ℝ => f z * reference z) := by
    apply (hiDiff.add hiPhi).congr
    exact Filter.Eventually.of_forall (fun z => by
      change f z * (reference z - phi z) + f z * phi z = f z * reference z
      ring)
  refine ⟨hiPhi, hiRef, integral_nonneg (fun z => mul_nonneg (hf0 z) (hphi0 z)), ?_⟩
  calc
    _ = ‖∫ z : ℝ × ℝ, f z * (reference z - phi z)‖ := by
      rw [Real.norm_eq_abs, ← integral_sub hiRef hiPhi]
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by
        change f z * reference z - f z * phi z = f z * (reference z - phi z)
        ring)
    _ ≤ ∫ z : ℝ × ℝ, ‖f z * (reference z - phi z)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z : ℝ × ℝ, delta * (f z * phi z) :=
      integral_mono hiDiff.norm (hiPhi.const_mul delta) hDiffPoint
    _ = _ := integral_const_mul _ _

end
end Shao.OQ3
