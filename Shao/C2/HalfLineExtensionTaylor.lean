import Shao.C2.HalfLineSpatialExtension

noncomputable section
namespace Shao.C2.HalfLineExtensionTaylor
open Shao.C2.HalfLineSpatialExtension Shao.C2.HalfLineReflectionFormula
open Shao.C2.HalfLineCompensatedBounds

theorem upperSpatialExtension_hasDerivAt_interior (a T z y : ℝ) (hy : y < a) :
    HasDerivAt (upperSpatialExtension a T z)
      (-(2 * (a - z) / T) * Real.exp (-2 * (a - y) * (a - z) / T)) y := by
  apply (upperReflection_hasDerivAt a y T z).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hy] with x hx
  exact if_pos hx

theorem lowerSpatialExtension_hasDerivAt_interior (a T z y : ℝ) (hy : -a < y) :
    HasDerivAt (lowerSpatialExtension a T z)
      ((2 * (a + z) / T) * Real.exp (-2 * (a + y) * (a + z) / T)) y := by
  apply (lowerReflection_hasDerivAt a y T z).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hy] with x hx
  exact if_pos hx

theorem upperSpatialExtension_small_taylor_bound (a y z T b : ℝ) (ha : 0 < a)
    (hy : y < a) (hz : z < a) (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2)
    (hnew : y + b ≤ a) :
    |upperSpatialExtension a (T - b ^ 2) z (y + b) - upperSpatialExtension a T z y -
        (b - b ^ 2 * (z - y) / T) * deriv (upperSpatialExtension a T z) y| ≤
      8000100 * |b| ^ 3 * (1 / Real.sqrt T) ^ 3 *
        (1 + |z - y| / Real.sqrt T) ^ 3 *
          Real.exp (-(max (a - y - |b|) 0) * (a - z) / T) := by
  rw [upperSpatialExtension_eq_closed a (T - b ^ 2) z (y + b) hnew,
    upperSpatialExtension_eq_closed a T z y hy.le,
    (upperSpatialExtension_hasDerivAt_interior a T z y hy).deriv]
  have h := upperReflection_small_taylor_bound a y z T b ha hy hz hT hsmall hnew
  rw [(upperReflection_hasDerivAt a y T z).deriv] at h
  exact h

theorem lowerSpatialExtension_small_taylor_bound (a y z T b : ℝ) (ha : 0 < a)
    (hy : -a < y) (hz : -a < z) (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2)
    (hnew : -a ≤ y + b) :
    |lowerSpatialExtension a (T - b ^ 2) z (y + b) - lowerSpatialExtension a T z y -
        (b - b ^ 2 * (z - y) / T) * deriv (lowerSpatialExtension a T z) y| ≤
      8000100 * |b| ^ 3 * (1 / Real.sqrt T) ^ 3 *
        (1 + |z - y| / Real.sqrt T) ^ 3 *
          Real.exp (-(max (a + y - |b|) 0) * (a + z) / T) := by
  rw [lowerSpatialExtension_eq_closed a (T - b ^ 2) z (y + b) hnew,
    lowerSpatialExtension_eq_closed a T z y hy.le,
    (lowerSpatialExtension_hasDerivAt_interior a T z y hy).deriv]
  have h := lowerReflection_small_taylor_bound a y z T b ha hy hz hT hsmall hnew
  rw [(lowerReflection_hasDerivAt a y T z).deriv] at h
  exact h

end Shao.C2.HalfLineExtensionTaylor
