import Shao.C2.HalfLineExtensionTimeProfiles

noncomputable section
namespace Shao.C2.HalfLineExtensionPDE
open Shao.C2.HalfLineSpatialExtension Shao.C2.HalfLineExtensionTimeProfiles
open Shao.C2.HalfLineReflectionFormula Shao.C2.HalfLineTimeProfiles
open Shao.C2.HalfLineMixedProfiles

theorem upperSpatialExtension_wall_time_function (a z : ℝ) :
    (fun t : ℝ => upperSpatialExtension a t z a) = (fun _ : ℝ => 0) := by
  funext t
  simp only [upperSpatialExtension, lt_self_iff_false, if_false]

theorem lowerSpatialExtension_wall_time_function (a z : ℝ) :
    (fun t : ℝ => lowerSpatialExtension a t z (-a)) = (fun _ : ℝ => 0) := by
  funext t
  simp only [lowerSpatialExtension, lt_self_iff_false, if_false]

theorem upperSpatialExtension_heat_equation (a y z T : ℝ) (ha : 0 < a)
    (hy : y ≤ a) (hz : z < a) (hT : 0 < T) :
    deriv (fun t : ℝ => upperSpatialExtension a t z y) T =
      (1 / 2 : ℝ) * iteratedDerivWithin 2
        (fun x : ℝ => upperSpatialExtension a T z x - 1) (Set.Iic a) y +
      ((z - y) / T) * iteratedDerivWithin 1
        (fun x : ℝ => upperSpatialExtension a T z x - 1) (Set.Iic a) y := by
  have hf : (fun t : ℝ => upperSpatialExtension a t z y) = timeCompletion (2 * (a - y) * (a - z)) := by
    funext t
    rw [upperSpatialExtension_eq_closed a t z y hy, upperReflection_eq_timeCompletion]
  have hs := upperSpatialExtension_spatial_time_functions a y z hy
  have h1 := congrArg (fun f : ℝ → ℝ => f T) hs.1
  have h2 := congrArg (fun f : ℝ → ℝ => f T) hs.2
  change iteratedDerivWithin 1 (fun x : ℝ => upperSpatialExtension a T z x - 1) (Set.Iic a) y =
    -slopeTime (a - y) (a - z) T at h1
  change iteratedDerivWithin 2 (fun x : ℝ => upperSpatialExtension a T z x - 1) (Set.Iic a) y =
    curvatureTime (a - y) (a - z) T at h2
  rw [hf, (timeCompletion_hasDerivAt (2 * (a - y) * (a - z)) T hT).deriv, h1, h2]
  dsimp only [slopeTime, curvatureTime]
  simp only [neg_mul]
  field_simp [ne_of_gt hT] <;> ring

theorem lowerSpatialExtension_heat_equation (a y z T : ℝ) (ha : 0 < a)
    (hy : -a ≤ y) (hz : -a < z) (hT : 0 < T) :
    deriv (fun t : ℝ => lowerSpatialExtension a t z y) T =
      (1 / 2 : ℝ) * iteratedDerivWithin 2
        (fun x : ℝ => lowerSpatialExtension a T z x - 1) (Set.Ici (-a)) y +
      ((z - y) / T) * iteratedDerivWithin 1
        (fun x : ℝ => lowerSpatialExtension a T z x - 1) (Set.Ici (-a)) y := by
  have hf : (fun t : ℝ => lowerSpatialExtension a t z y) = timeCompletion (2 * (a + y) * (a + z)) := by
    funext t
    rw [lowerSpatialExtension_eq_closed a t z y hy, lowerReflection_eq_timeCompletion]
  have hs := lowerSpatialExtension_spatial_time_functions a y z hy
  have h1 := congrArg (fun f : ℝ → ℝ => f T) hs.1
  have h2 := congrArg (fun f : ℝ → ℝ => f T) hs.2
  change iteratedDerivWithin 1 (fun x : ℝ => lowerSpatialExtension a T z x - 1) (Set.Ici (-a)) y =
    slopeTime (a + y) (a + z) T at h1
  change iteratedDerivWithin 2 (fun x : ℝ => lowerSpatialExtension a T z x - 1) (Set.Ici (-a)) y =
    curvatureTime (a + y) (a + z) T at h2
  rw [hf, (timeCompletion_hasDerivAt (2 * (a + y) * (a + z)) T hT).deriv, h1, h2]
  dsimp only [slopeTime, curvatureTime]
  simp only [neg_mul]
  field_simp [ne_of_gt hT] <;> ring

end Shao.C2.HalfLineExtensionPDE
