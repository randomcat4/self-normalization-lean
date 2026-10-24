import Shao.C2.HalfLineMixedProfiles

noncomputable section
namespace Shao.C2.HalfLineWallProfiles
open Shao.C2.HalfLineReflectionFormula Shao.C2.CompletionFirstProfile
open Shao.C2.HalfLineSpatialProfiles Shao.C2.HalfLineMixedProfiles

theorem bound_on_nonneg_of_continuous (F G : ℝ → ℝ) (hF : Continuous F)
    (hG : Continuous G) (hpos : ∀ x : ℝ, 0 < x → F x ≤ G x)
    (u : ℝ) (hu : 0 ≤ u) : F u ≤ G u := by
  have hs : IsClosed {x : ℝ | F x ≤ G x} := isClosed_le hF hG
  have hi : Set.Ioi (0 : ℝ) ⊆ {x : ℝ | F x ≤ G x} := fun x hx => hpos x hx
  have hu' : u ∈ closure (Set.Ioi (0 : ℝ)) := by simpa only [closure_Ioi, Set.mem_Ici] using hu
  exact closure_minimal hi hs hu'

theorem reflection_power_profile_nonneg (u v T : ℝ)
    (hu : 0 ≤ u) (hv : 0 < v) (hT : 0 < T) (j : ℕ) (hj : 0 < j) :
    (2 * v / T) ^ j * Real.exp (-2 * u * v / T) ≤
      (8 * (j : ℝ) / Real.sqrt T * (1 + |u - v| / Real.sqrt T)) ^ j *
        Real.exp (-u * v / T) := by
  refine bound_on_nonneg_of_continuous
    (fun x : ℝ => (2 * v / T) ^ j * Real.exp (-2 * x * v / T))
    (fun x : ℝ => (8 * (j : ℝ) / Real.sqrt T * (1 + |x - v| / Real.sqrt T)) ^ j *
      Real.exp (-x * v / T)) (by fun_prop) (by fun_prop) ?_ u hu
  intro x hx
  exact positive_reflection_power_profile x v T hx hv hT j hj

theorem reflection_power_monomial_profile_nonneg (u v T : ℝ)
    (hu : 0 ≤ u) (hv : 0 < v) (hT : 0 < T) (j : ℕ) (hj : 0 < j) (m : ℕ) :
    (2 * v / T) ^ j * (2 * u * v / T) ^ m * Real.exp (-2 * u * v / T) ≤
      (16 * (j : ℝ) / Real.sqrt T * (1 + |u - v| / Real.sqrt T)) ^ j *
        ((4 : ℝ) ^ m * (Nat.factorial m : ℝ)) * Real.exp (-u * v / T) := by
  refine bound_on_nonneg_of_continuous
    (fun x : ℝ => (2 * v / T) ^ j * (2 * x * v / T) ^ m * Real.exp (-2 * x * v / T))
    (fun x : ℝ => (16 * (j : ℝ) / Real.sqrt T * (1 + |x - v| / Real.sqrt T)) ^ j *
      ((4 : ℝ) ^ m * (Nat.factorial m : ℝ)) * Real.exp (-x * v / T))
    (by fun_prop) (by fun_prop) ?_ u hu
  intro x hx
  exact positive_reflection_power_monomial_profile x v T hx hv hT j hj m

theorem mixed_time_profiles_nonneg (u v T : ℝ) (hu : 0 ≤ u) (hv : 0 < v) (hT : 0 < T) :
    |deriv (slopeTime u v) T| ≤
      80 / (T * Real.sqrt T) * (1 + |u - v| / Real.sqrt T) * Real.exp (-u * v / T) ∧
    |deriv (curvatureTime u v) T| ≤
      6144 / T ^ 2 * (1 + |u - v| / Real.sqrt T) ^ 2 * Real.exp (-u * v / T) ∧
    |deriv (deriv (slopeTime u v)) T| ≤
      800 / (T ^ 2 * Real.sqrt T) * (1 + |u - v| / Real.sqrt T) * Real.exp (-u * v / T) := by
  have hsval (x : ℝ) : deriv (slopeTime x v) T =
      (2 * v / T ^ 2) * (2 * x * v / T - 1) * Real.exp (-2 * x * v / T) :=
    (slopeTime_hasDerivAt x v T hT).deriv
  have hcval (x : ℝ) : deriv (curvatureTime x v) T =
      (2 * v / T) ^ 2 / T * (2 - 2 * x * v / T) * Real.exp (-2 * x * v / T) :=
    (curvatureTime_hasDerivAt x v T hT).deriv
  have hssval (x : ℝ) : deriv (deriv (slopeTime x v)) T =
      (2 * v / T ^ 3) * (2 - 4 * (2 * x * v / T) + (2 * x * v / T) ^ 2) *
        Real.exp (-2 * x * v / T) := (slopeTime_second_hasDerivAt x v T hT).deriv
  have hsc : Continuous (fun x : ℝ => deriv (slopeTime x v) T) := by
    simp_rw [hsval]
    fun_prop
  have hcc : Continuous (fun x : ℝ => deriv (curvatureTime x v) T) := by
    simp_rw [hcval]
    fun_prop
  have hssc : Continuous (fun x : ℝ => deriv (deriv (slopeTime x v)) T) := by
    simp_rw [hssval]
    fun_prop
  refine ⟨?_, ?_, ?_⟩
  · exact bound_on_nonneg_of_continuous
      (fun x : ℝ => |deriv (slopeTime x v) T|)
      (fun x : ℝ => 80 / (T * Real.sqrt T) * (1 + |x - v| / Real.sqrt T) * Real.exp (-x * v / T))
      hsc.abs (by fun_prop) (fun x hx => (mixed_time_profiles x v T hx hv hT).1) u hu
  · exact bound_on_nonneg_of_continuous
      (fun x : ℝ => |deriv (curvatureTime x v) T|)
      (fun x : ℝ => 6144 / T ^ 2 * (1 + |x - v| / Real.sqrt T) ^ 2 * Real.exp (-x * v / T))
      hcc.abs (by fun_prop) (fun x hx => (mixed_time_profiles x v T hx hv hT).2.1) u hu
  · exact bound_on_nonneg_of_continuous
      (fun x : ℝ => |deriv (deriv (slopeTime x v)) T|)
      (fun x : ℝ => 800 / (T ^ 2 * Real.sqrt T) * (1 + |x - v| / Real.sqrt T) * Real.exp (-x * v / T))
      hssc.abs (by fun_prop) (fun x hx => (mixed_time_profiles x v T hx hv hT).2.2) u hu

theorem upperReflection_closed_iterated_profile (j : ℕ) (hj : 0 < j)
    (a y T z : ℝ) (hT : 0 < T) (hy : y ≤ a) (hz : z < a) :
    |iteratedDeriv j (fun x : ℝ => upperReflection a x T z - 1) y| ≤
      (8 * (j : ℝ) / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j *
        upperProfile a y T z := by
  rw [upperReflection_iteratedDeriv, abs_mul, abs_neg, abs_pow,
    abs_of_pos (show 0 < 2 * (a - z) / T by positivity), abs_of_pos (Real.exp_pos _)]
  have h := reflection_power_profile_nonneg (a - y) (a - z) T (by linarith) (by linarith) hT j hj
  simpa only [upperProfile, show a - y - (a - z) = z - y by ring] using h

theorem lowerReflection_closed_iterated_profile (j : ℕ) (hj : 0 < j)
    (a y T z : ℝ) (hT : 0 < T) (hy : -a ≤ y) (hz : -a < z) :
    |iteratedDeriv j (fun x : ℝ => lowerReflection a x T z - 1) y| ≤
      (8 * (j : ℝ) / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j *
        lowerProfile a y T z := by
  have haz : 0 < a + z := by linarith
  rw [lowerReflection_iteratedDeriv, abs_mul, abs_neg, abs_pow, abs_neg,
    abs_of_pos (show 0 < 2 * (a + z) / T by positivity), abs_of_pos (Real.exp_pos _)]
  have h := reflection_power_profile_nonneg (a + y) (a + z) T (by linarith) (by linarith) hT j hj
  simpa only [lowerProfile, show a + y - (a + z) = y - z by ring, abs_sub_comm y z] using h

end Shao.C2.HalfLineWallProfiles
