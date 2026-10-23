import Shao.OQ4.IntervalConcentration
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Measure.Prod

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory
open scoped Topology
noncomputable section

theorem standard_gaussian_plane_closed_ball_bound
    (r : ℝ) (hr : 0 ≤ r) :
    ((ProbabilityTheory.gaussianReal 0 1).prod
      (ProbabilityTheory.gaussianReal 0 1)).real
        (Metric.closedBall (0 : ℝ × ℝ) r) ≤ 4 * r ^ 2 := by
  let γ : Measure ℝ := gaussianReal 0 1
  let I : Set ℝ := Set.Icc (-r) r
  have hI : γ.real I ≤ 2 * r := by
    have hCDF : ∀ x, |γ.real (Set.Iic x) - Shao.OQ4.standardNormalCDF x| ≤ 0 := by
      intro x
      change |(gaussianReal 0 1).real (Set.Iic x) - Shao.OQ4.standardNormalCDF x| ≤ 0
      rw [← Shao.OQ4.standardNormalCDF_eq_real]
      simp
    have hi := Shao.OQ4.closed_interval_mass_bound_from_cdf γ 1 0
      Shao.OQ4.standardNormalCDF (by norm_num) (by norm_num)
      (by intro x y; simpa only [one_mul] using Shao.OQ4.standardNormalCDF_lipschitz x y)
      hCDF (-r) r (by linarith)
    simpa only [I, one_mul, mul_zero, add_zero, sub_neg_eq_add, two_mul] using hi
  have hsub : Metric.closedBall (0 : ℝ × ℝ) r ⊆ I ×ˢ I := by
    intro z hz
    have hn : max |z.1| |z.2| ≤ r := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using hz
    have h1 := abs_le.mp ((le_max_left _ _).trans hn)
    have h2 := abs_le.mp ((le_max_right _ _).trans hn)
    exact ⟨h1, h2⟩
  calc
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
        (Metric.closedBall (0 : ℝ × ℝ) r) ≤ (γ.prod γ).real (I ×ˢ I) :=
      measureReal_mono hsub (measure_ne_top (γ.prod γ) _)
    _ = γ.real I * γ.real I := measureReal_prod_prod I I
    _ ≤ (2 * r) * (2 * r) :=
      mul_le_mul hI hI (measureReal_nonneg (μ := γ)) (by linarith)
    _ = 4 * r ^ 2 := by ring

theorem standard_gaussian_plane_cell_thickening_bound
    (A : Set (ℝ × ℝ)) (r h : ℝ) (hr : 0 ≤ r) (hh : 0 ≤ h)
    (hA : A ⊆ Metric.closedBall (0 : ℝ × ℝ) r) :
    ((ProbabilityTheory.gaussianReal 0 1).prod
      (ProbabilityTheory.gaussianReal 0 1)).real
        (Metric.cthickening h A) ≤ 4 * (r + h) ^ 2 := by
  have hball : Metric.cthickening h (Metric.closedBall (0 : ℝ × ℝ) r) ⊆
      Metric.closedBall (0 : ℝ × ℝ) (r + h) := by
    have hs := Metric.cthickening_cthickening_subset hh hr ({0} : Set (ℝ × ℝ))
    rw [Metric.cthickening_singleton 0 hr,
      Metric.cthickening_singleton 0 (add_nonneg hh hr)] at hs
    simpa only [add_comm] using hs
  have hsub := (Metric.cthickening_subset_of_subset h hA).trans hball
  calc
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).real (Metric.cthickening h A) ≤
        ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
          (Metric.closedBall (0 : ℝ × ℝ) (r + h)) :=
      measureReal_mono hsub
        (measure_ne_top ((gaussianReal 0 1).prod (gaussianReal 0 1)) _)
    _ ≤ 4 * (r + h) ^ 2 :=
      standard_gaussian_plane_closed_ball_bound (r + h) (add_nonneg hr hh)

end
end Shao.OQ3
