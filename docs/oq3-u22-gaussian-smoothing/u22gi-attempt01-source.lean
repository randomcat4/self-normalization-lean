import Shao.OQ3.IndependentSumSmoothingBounds
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Measure.Real

namespace Shao.OQ3
open MeasureTheory
noncomputable section

theorem independent_sum_cthickening_bounds
    (nu eta : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu] [IsProbabilityMeasure eta]
    (s : Set (ℝ × ℝ)) (hs : MeasurableSet s) (eps : ℝ) :
    let rho : Measure (ℝ × ℝ) := (nu.prod eta).map (fun q => q.1 + q.2)
    nu s ≤ rho (Metric.cthickening eps s) + eta {y : ℝ × ℝ | eps < ‖y‖} ∧
      rho ((Metric.cthickening eps sᶜ)ᶜ) ≤ nu s + eta {y : ℝ × ℝ | eps < ‖y‖} := by
  intro rho
  have hout : MeasurableSet (Metric.cthickening eps s) :=
    Metric.isClosed_cthickening.measurableSet
  have hin : MeasurableSet ((Metric.cthickening eps sᶜ)ᶜ) :=
    Metric.isClosed_cthickening.measurableSet.compl
  constructor
  · apply independent_sum_source_set_le nu eta s (Metric.cthickening eps s) hs hout eps
    intro x hx y hy
    apply Metric.mem_cthickening_of_dist_le (x + y) x eps s hx
    simpa only [dist_eq_norm, add_sub_cancel_left] using hy
  · apply independent_sum_image_set_le nu eta ((Metric.cthickening eps sᶜ)ᶜ) s hin hs eps
    intro x y hxy hy
    by_contra hx
    have hm : x + y ∈ Metric.cthickening eps sᶜ := by
      apply Metric.mem_cthickening_of_dist_le (x + y) x eps sᶜ hx
      simpa only [dist_eq_norm, add_sub_cancel_left] using hy
    exact hxy hm

theorem independent_sum_cthickening_real_sandwich
    (nu eta : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu] [IsProbabilityMeasure eta]
    (s : Set (ℝ × ℝ)) (hs : MeasurableSet s) (eps : ℝ) :
    let rho : Measure (ℝ × ℝ) := (nu.prod eta).map (fun q => q.1 + q.2)
    rho.real ((Metric.cthickening eps sᶜ)ᶜ) - eta.real {y : ℝ × ℝ | eps < ‖y‖} ≤ nu.real s ∧
      nu.real s ≤ rho.real (Metric.cthickening eps s) + eta.real {y : ℝ × ℝ | eps < ‖y‖} := by
  intro rho
  letI : IsProbabilityMeasure rho := by dsimp only [rho]; infer_instance
  obtain ⟨hu, hl⟩ := independent_sum_cthickening_bounds nu eta s hs eps
  have hn : nu s ≠ ∞ := measure_ne_top nu s
  have he : eta {y : ℝ × ℝ | eps < ‖y‖} ≠ ∞ := measure_ne_top eta _
  have hr : rho (Metric.cthickening eps s) ≠ ∞ := measure_ne_top rho _
  have hlr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hn, he⟩) hl
  have hur := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hr, he⟩) hu
  rw [ENNReal.toReal_add hn he] at hlr
  rw [ENNReal.toReal_add hr he] at hur
  change rho.real ((Metric.cthickening eps sᶜ)ᶜ) ≤ nu.real s +
    eta.real {y : ℝ × ℝ | eps < ‖y‖} at hlr
  change nu.real s ≤ rho.real (Metric.cthickening eps s) +
    eta.real {y : ℝ × ℝ | eps < ‖y‖} at hur
  exact ⟨by linarith, hur⟩

end
end Shao.OQ3
