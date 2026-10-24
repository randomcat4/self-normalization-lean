import Shao.C2.HalfLineExtensionTaylor

noncomputable section
namespace Shao.C2.HalfLineExtensionTimeProfiles
open Shao.C2.HalfLineSpatialExtension Shao.C2.HalfLineReflectionFormula
open Shao.C2.HalfLineSpatialProfiles Shao.C2.HalfLineWallProfiles
open Shao.C2.HalfLineMixedProfiles Shao.C2.HalfLineTimeProfiles
open Shao.C2.CompletionFirstProfile

theorem upperSpatialExtension_spatial_time_functions (a y z : ℝ) (hy : y ≤ a) :
    (fun t : ℝ => iteratedDerivWithin 1
      (fun x : ℝ => upperSpatialExtension a t z x - 1) (Set.Iic a) y) =
        (fun t : ℝ => -slopeTime (a - y) (a - z) t) ∧
    (fun t : ℝ => iteratedDerivWithin 2
      (fun x : ℝ => upperSpatialExtension a t z x - 1) (Set.Iic a) y) =
        (fun t : ℝ => curvatureTime (a - y) (a - z) t) := by
  constructor <;> funext t
  · rw [upperSpatialExtension_iteratedWithin_eq 1 a t z y hy, upperReflection_iteratedDeriv]
    dsimp only [slopeTime]
    norm_num only [pow_one]
    ring
  · rw [upperSpatialExtension_iteratedWithin_eq 2 a t z y hy, upperReflection_iteratedDeriv]
    rfl

theorem lowerSpatialExtension_spatial_time_functions (a y z : ℝ) (hy : -a ≤ y) :
    (fun t : ℝ => iteratedDerivWithin 1
      (fun x : ℝ => lowerSpatialExtension a t z x - 1) (Set.Ici (-a)) y) =
        (fun t : ℝ => slopeTime (a + y) (a + z) t) ∧
    (fun t : ℝ => iteratedDerivWithin 2
      (fun x : ℝ => lowerSpatialExtension a t z x - 1) (Set.Ici (-a)) y) =
        (fun t : ℝ => curvatureTime (a + y) (a + z) t) := by
  constructor <;> funext t
  · rw [lowerSpatialExtension_iteratedWithin_eq 1 a t z y hy, lowerReflection_iteratedDeriv]
    dsimp only [slopeTime]
    norm_num only [pow_one]
    ring
  · rw [lowerSpatialExtension_iteratedWithin_eq 2 a t z y hy, lowerReflection_iteratedDeriv]
    simp only [curvatureTime, neg_sq]

theorem upperSpatialExtension_mixed_time_profiles (a y z T : ℝ)
    (hy : y ≤ a) (hz : z < a) (hT : 0 < T) :
    let F₁ := fun t : ℝ => iteratedDerivWithin 1
      (fun x : ℝ => upperSpatialExtension a t z x - 1) (Set.Iic a) y
    let F₂ := fun t : ℝ => iteratedDerivWithin 2
      (fun x : ℝ => upperSpatialExtension a t z x - 1) (Set.Iic a) y
    |deriv F₁ T| ≤ 80 / (T * Real.sqrt T) * (1 + |z - y| / Real.sqrt T) * upperProfile a y T z ∧
    |deriv F₂ T| ≤ 6144 / T ^ 2 * (1 + |z - y| / Real.sqrt T) ^ 2 * upperProfile a y T z ∧
    |deriv (deriv F₁) T| ≤ 800 / (T ^ 2 * Real.sqrt T) *
      (1 + |z - y| / Real.sqrt T) * upperProfile a y T z := by
  dsimp only
  have hf := upperSpatialExtension_spatial_time_functions a y z hy
  rw [hf.1, hf.2]
  have h := mixed_time_profiles_nonneg (a - y) (a - z) T (sub_nonneg.mpr hy) (sub_pos.mpr hz) hT
  have hn1 : deriv (fun t : ℝ => -slopeTime (a - y) (a - z) t) =
      fun t : ℝ => -deriv (slopeTime (a - y) (a - z)) t := by
    funext t
    change deriv (-slopeTime (a - y) (a - z)) t = -deriv (slopeTime (a - y) (a - z)) t
    exact deriv.neg
  have hn2 : deriv (deriv (fun t : ℝ => -slopeTime (a - y) (a - z) t)) T =
      -deriv (deriv (slopeTime (a - y) (a - z))) T := by
    rw [hn1]
    change deriv (-deriv (slopeTime (a - y) (a - z))) T = -deriv (deriv (slopeTime (a - y) (a - z))) T
    exact deriv.neg
  rw [hn2, hn1]
  simpa only [abs_neg, upperProfile, show a - y - (a - z) = z - y by ring] using h

theorem lowerSpatialExtension_mixed_time_profiles (a y z T : ℝ)
    (hy : -a ≤ y) (hz : -a < z) (hT : 0 < T) :
    let F₁ := fun t : ℝ => iteratedDerivWithin 1
      (fun x : ℝ => lowerSpatialExtension a t z x - 1) (Set.Ici (-a)) y
    let F₂ := fun t : ℝ => iteratedDerivWithin 2
      (fun x : ℝ => lowerSpatialExtension a t z x - 1) (Set.Ici (-a)) y
    |deriv F₁ T| ≤ 80 / (T * Real.sqrt T) * (1 + |z - y| / Real.sqrt T) * lowerProfile a y T z ∧
    |deriv F₂ T| ≤ 6144 / T ^ 2 * (1 + |z - y| / Real.sqrt T) ^ 2 * lowerProfile a y T z ∧
    |deriv (deriv F₁) T| ≤ 800 / (T ^ 2 * Real.sqrt T) *
      (1 + |z - y| / Real.sqrt T) * lowerProfile a y T z := by
  dsimp only
  have hf := lowerSpatialExtension_spatial_time_functions a y z hy
  rw [hf.1, hf.2]
  have h := mixed_time_profiles_nonneg (a + y) (a + z) T (by linarith) (by linarith) hT
  simpa only [lowerProfile, show a + y - (a + z) = y - z by ring, abs_sub_comm y z] using h

theorem upperSpatialExtension_pure_time_profiles (a y z T : ℝ)
    (hy : y ≤ a) (hz : z < a) (hT : 0 < T) :
    |deriv (fun t : ℝ => upperSpatialExtension a t z y) T| ≤ 2 / T * upperProfile a y T z ∧
    |deriv (deriv (fun t : ℝ => upperSpatialExtension a t z y)) T| ≤ 12 / T ^ 2 * upperProfile a y T z ∧
    |deriv (deriv (deriv (fun t : ℝ => upperSpatialExtension a t z y))) T| ≤
      108 / T ^ 3 * upperProfile a y T z := by
  have hf : (fun t : ℝ => upperSpatialExtension a t z y) = timeCompletion (2 * (a - y) * (a - z)) := by
    funext t
    rw [upperSpatialExtension_eq_closed a t z y hy, upperReflection_eq_timeCompletion]
  rw [hf]
  have hu : 0 ≤ a - y := sub_nonneg.mpr hy
  have hv : 0 < a - z := sub_pos.mpr hz
  have h := timeCompletion_time_profiles (2 * (a - y) * (a - z)) T (by positivity) hT
  have he : -(2 * (a - y) * (a - z)) / (2 * T) = -(a - y) * (a - z) / T := by
    field_simp [ne_of_gt hT] <;> ring
  simpa only [upperProfile, he] using h

theorem lowerSpatialExtension_pure_time_profiles (a y z T : ℝ)
    (hy : -a ≤ y) (hz : -a < z) (hT : 0 < T) :
    |deriv (fun t : ℝ => lowerSpatialExtension a t z y) T| ≤ 2 / T * lowerProfile a y T z ∧
    |deriv (deriv (fun t : ℝ => lowerSpatialExtension a t z y)) T| ≤ 12 / T ^ 2 * lowerProfile a y T z ∧
    |deriv (deriv (deriv (fun t : ℝ => lowerSpatialExtension a t z y))) T| ≤
      108 / T ^ 3 * lowerProfile a y T z := by
  have hf : (fun t : ℝ => lowerSpatialExtension a t z y) = timeCompletion (2 * (a + y) * (a + z)) := by
    funext t
    rw [lowerSpatialExtension_eq_closed a t z y hy, lowerReflection_eq_timeCompletion]
  rw [hf]
  have hu : 0 ≤ a + y := by linarith
  have hv : 0 < a + z := by linarith
  have h := timeCompletion_time_profiles (2 * (a + y) * (a + z)) T (by positivity) hT
  have he : -(2 * (a + y) * (a + z)) / (2 * T) = -(a + y) * (a + z) / T := by
    field_simp [ne_of_gt hT] <;> ring
  simpa only [lowerProfile, he] using h

end Shao.C2.HalfLineExtensionTimeProfiles
