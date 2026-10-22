import Shao.OQ5.P52.FixedLayerNormalizedRealStatistics
import Shao.OQ5.P52.FixedLayerTailLimits

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

namespace Shao.OQ5.P52

noncomputable section

theorem fixedNormalizedRealSampleStudentizedTailProbability_ge_quarter_exp_eventually :
    ∀ᶠ j : ℕ in atTop,
      (1 / 4 : ℝ) * Real.exp
        (-2 * (fixedLayerN j : ℝ) ^ fixedLayerTau j) ≤
        fixedNormalizedRealSampleStudentizedTailProbability
          (fixedLayerN j) (fixedLayerTailThreshold (fixedLayerN j)) := by
  simpa only [fixedNormalizedRealSampleStudentizedTailProbability_eq] using
    fixedSampleStudentizedTailProbability_ge_quarter_exp_eventually

theorem fixedNormalizedRealSampleStudentizedTailProbability_eventually_pos :
    ∀ᶠ j : ℕ in atTop,
      0 < fixedNormalizedRealSampleStudentizedTailProbability
        (fixedLayerN j) (fixedLayerTailThreshold (fixedLayerN j)) := by
  simpa only [fixedNormalizedRealSampleStudentizedTailProbability_eq] using
    fixedSampleStudentizedTailProbability_eventually_pos

theorem fixedNormalizedRealLayer_log_tail_ratio_tendsto_zero :
    Tendsto (fun j : ℕ =>
      Real.log (fixedNormalizedRealSampleStudentizedTailProbability
          (fixedLayerN j) (fixedLayerTailThreshold (fixedLayerN j))) /
        (-((fixedLayerTailThreshold (fixedLayerN j)) ^ 2) / 2))
      atTop (nhds 0) := by
  simpa only [fixedNormalizedRealSampleStudentizedTailProbability_eq] using
    fixedLayer_log_tail_ratio_tendsto_zero

theorem fixedNormalizedRealLayer_relative_tail_ratio_tendsto_atTop :
    Tendsto (fun j : ℕ =>
      fixedNormalizedRealSampleStudentizedTailProbability
          (fixedLayerN j) (fixedLayerTailThreshold (fixedLayerN j)) /
        Shao.OQ5.P35.standardNormalUpperTail
          (fixedLayerTailThreshold (fixedLayerN j)))
      atTop atTop := by
  simpa only [fixedNormalizedRealSampleStudentizedTailProbability_eq] using
    fixedLayer_relative_tail_ratio_tendsto_atTop

theorem fixedNormalizedRealLayer_full_log_tail_ratio_not_tendsto_one :
    ¬ Tendsto (fun n : ℕ =>
      Real.log (fixedNormalizedRealSampleStudentizedTailProbability
          n (fixedLayerTailThreshold n)) /
        (-((fixedLayerTailThreshold n) ^ 2) / 2))
      atTop (nhds 1) := by
  simpa only [fixedNormalizedRealSampleStudentizedTailProbability_eq] using
    fixedLayer_full_log_tail_ratio_not_tendsto_one

theorem fixedNormalizedRealLayer_full_relative_tail_ratio_not_tendsto_one :
    ¬ Tendsto (fun n : ℕ =>
      fixedNormalizedRealSampleStudentizedTailProbability n (fixedLayerTailThreshold n) /
        Shao.OQ5.P35.standardNormalUpperTail (fixedLayerTailThreshold n))
      atTop (nhds 1) := by
  simpa only [fixedNormalizedRealSampleStudentizedTailProbability_eq] using
    fixedLayer_full_relative_tail_ratio_not_tendsto_one

theorem fixedNormalizedRealLayer_uniform_relative_tail_window_fails :
    ¬ (∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        ∀ x : ℝ, 0 ≤ x → x ≤ 2 * fixedLayerTailThreshold n →
          |fixedNormalizedRealSampleStudentizedTailProbability n x /
            Shao.OQ5.P35.standardNormalUpperTail x - 1| ≤ ε) := by
  simpa only [fixedNormalizedRealSampleStudentizedTailProbability_eq] using
    fixedLayer_uniform_relative_tail_window_fails

end
end Shao.OQ5.P52
