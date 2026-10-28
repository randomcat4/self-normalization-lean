import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.Ring

namespace Shao.OQ3
open MeasureTheory
noncomputable section

theorem bounded_support_test_integrable_l1_bound
    (f : (ℝ × ℝ) → ℝ) (hf : Measurable f)
    (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hbound : ∀ z : ℝ × ℝ, |f z| ≤ C)
    (hzero : ∀ z : ℝ × ℝ, R < ‖z‖ → f z = 0) :
    Integrable f ∧ (∫ z : ℝ × ℝ, |f z|) ≤ 4 * C * R ^ 2 := by
  classical
  let B : Set (ℝ × ℝ) := Set.Icc (-R) R ×ˢ Set.Icc (-R) R
  have hBm : MeasurableSet B := measurableSet_Icc.prod measurableSet_Icc
  have hBfinite : volume B ≠ ⊤ := (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hiB : Integrable (B.indicator (fun _ : ℝ × ℝ => C)) :=
    (integrableOn_const hBfinite).integrable_indicator hBm
  have hDom (z : ℝ × ℝ) : |f z| ≤ B.indicator (fun _ => C) z := by
    by_cases hz : z ∈ B
    · rw [Set.indicator_of_mem hz]
      exact hbound z
    · have hnorm : R < ‖z‖ := by
        by_contra hn
        have hnR : ‖z‖ ≤ R := le_of_not_gt hn
        change max |z.1| |z.2| ≤ R at hnR
        apply hz
        exact ⟨abs_le.mp ((le_max_left _ _).trans hnR),
          abs_le.mp ((le_max_right _ _).trans hnR)⟩
      rw [hzero z hnorm, abs_zero, Set.indicator_of_notMem hz]
  have hi : Integrable f := by
    apply hiB.mono' hf.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hDom z)
  have hlen : (volume : Measure ℝ).real (Set.Icc (-R) R) = 2 * R := by
    rw [Real.volume_real_Icc, max_eq_left (by linarith : 0 ≤ R - -R)]
    ring
  have hBvol : (volume : Measure (ℝ × ℝ)).real B = 4 * R ^ 2 := by
    change ((volume : Measure ℝ).prod volume).real (Set.Icc (-R) R ×ˢ Set.Icc (-R) R) = _
    rw [measureReal_prod_prod, hlen]
    ring
  refine ⟨hi, ?_⟩
  have hiAbs : Integrable (fun z : ℝ × ℝ => |f z|) := by
    simpa only [Real.norm_eq_abs] using hi.norm
  calc
    _ ≤ ∫ z : ℝ × ℝ, B.indicator (fun _ => C) z := integral_mono hiAbs hiB hDom
    _ = _ := by
      rw [integral_indicator_const C hBm, smul_eq_mul, hBvol]
      ring

end
end Shao.OQ3
