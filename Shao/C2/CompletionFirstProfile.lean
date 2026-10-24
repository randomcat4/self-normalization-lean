import Shao.C2.IntervalDerivativeBound

noncomputable section
namespace Shao.C2.CompletionFirstProfile
open MeasureTheory
open Shao.C2.BridgeDomination Shao.C2.HalfLineReflectionFormula
open Shao.C2.IntervalDerivativeBound

def upperProfile (a y T z : ℝ) : ℝ := Real.exp (-(a - y) * (a - z) / T)
def lowerProfile (a y T z : ℝ) : ℝ := Real.exp (-(a + y) * (a + z) / T)
def intervalProfile (a y T z : ℝ) : ℝ := upperProfile a y T z + lowerProfile a y T z

theorem reflection_deficit_le_profile (u v T : ℝ) (hu : 0 < u) (hv : 0 < v) (hT : 0 < T) :
    Real.exp (-2 * u * v / T) ≤ Real.exp (-u * v / T) := by
  apply Real.exp_le_exp.2
  apply (div_le_div_iff_of_pos_right hT).2
  nlinarith

theorem positive_reflection_slope_profile (u v T : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hT : 0 < T) :
    (2 * v / T) * Real.exp (-2 * u * v / T) ≤
      (8 / Real.sqrt T * (1 + |u - v| / Real.sqrt T)) * Real.exp (-u * v / T) := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hs2 : Real.sqrt T ≤ Real.sqrt (2 * T) := Real.sqrt_le_sqrt (by linarith)
  have hhalf : (v / T) * Real.exp (-u * v / T) ≤
      4 / Real.sqrt T * (1 + |u - v| / Real.sqrt T) := by
    have h := positive_reflection_slope_bound u v (2 * T) hu hv (by positivity)
    have hc : 2 * v / (2 * T) = v / T := by field_simp <;> ring
    have he : -2 * u * v / (2 * T) = -u * v / T := by field_simp <;> ring
    rw [hc, he] at h
    refine h.trans ?_
    apply mul_le_mul
    · exact div_le_div_of_nonneg_left (by norm_num) hs hs2
    · have hd := div_le_div_of_nonneg_left (abs_nonneg (u - v)) hs hs2
      linarith
    · positivity
    · positivity
  have hdouble : (2 * v / T) * Real.exp (-u * v / T) ≤
      8 / Real.sqrt T * (1 + |u - v| / Real.sqrt T) := by
    convert mul_le_mul_of_nonneg_left hhalf (show (0 : ℝ) ≤ 2 by norm_num) using 1 <;> ring
  have he : Real.exp (-2 * u * v / T) =
      Real.exp (-u * v / T) * Real.exp (-u * v / T) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hdouble (le_of_lt (Real.exp_pos _))

theorem upperReflection_deriv_profile (a y T z : ℝ) (hT : 0 < T) (hy : y < a) (hz : z < a) :
    |deriv (fun u : ℝ => upperReflection a u T z) y| ≤
      (8 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) * upperProfile a y T z := by
  rw [(upperReflection_hasDerivAt a y T z).deriv, abs_mul, abs_neg,
    abs_of_pos (show 0 < 2 * (a - z) / T by positivity), abs_of_pos (Real.exp_pos _)]
  have h := positive_reflection_slope_profile (a - y) (a - z) T (by linarith) (by linarith) hT
  simpa only [upperProfile, show a - y - (a - z) = z - y by ring] using h

theorem lowerReflection_deriv_profile (a y T z : ℝ) (hT : 0 < T) (hy : -a < y) (hz : -a < z) :
    |deriv (fun u : ℝ => lowerReflection a u T z) y| ≤
      (8 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) * lowerProfile a y T z := by
  have haz : 0 < a + z := by linarith
  rw [(lowerReflection_hasDerivAt a y T z).deriv, abs_mul,
    abs_of_pos (show 0 < 2 * (a + z) / T by positivity), abs_of_pos (Real.exp_pos _)]
  have h := positive_reflection_slope_profile (a + y) (a + z) T (by linarith) (by linarith) hT
  simpa only [lowerProfile, show a + y - (a + z) = y - z by ring, abs_sub_comm y z] using h

theorem interval_deficit_profile_of_reflection
    (P : Measure BridgeNoise) [IsProbabilityMeasure P]
    (a y T z : ℝ) (hT : 0 < T) (hy : |y| < a) (hz : |z| < a)
    (hUpper : upperCompletion P a y T z = upperReflection a y T z)
    (hLower : lowerCompletion P a y T z = lowerReflection a y T z) :
    |intervalCompletion P a y T z - 1| ≤ intervalProfile a y T z := by
  obtain ⟨hyl, hyu⟩ := abs_lt.mp hy
  obtain ⟨hzl, hzu⟩ := abs_lt.mp hz
  have hu := reflection_deficit_le_profile (a - y) (a - z) T (by linarith) (by linarith) hT
  have hl := reflection_deficit_le_profile (a + y) (a + z) T (by linarith) (by linarith) hT
  change Real.exp (-2 * (a - y) * (a - z) / T) ≤ upperProfile a y T z at hu
  change Real.exp (-2 * (a + y) * (a + z) / T) ≤ lowerProfile a y T z at hl
  have hUnion := measureReal_union_add_inter (μ := P) (s := strictUpper a y T z)
    (measurableSet_strictLower a y T z)
  change P.real (strictUpper a y T z ∪ strictLower a y T z) + intervalCompletion P a y T z =
    upperCompletion P a y T z + lowerCompletion P a y T z at hUnion
  have hb : P.real (strictUpper a y T z ∪ strictLower a y T z) ≤ 1 := by
    calc
      _ ≤ P.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := probReal_univ
  rw [hUpper, hLower, upperReflection, lowerReflection] at hUnion
  obtain ⟨_, _, _, _, _, hi⟩ := completion_bounds P a y T z
  rw [abs_of_nonpos (by linarith : intervalCompletion P a y T z - 1 ≤ 0)]
  dsimp only [intervalProfile]
  linarith

theorem interval_deriv_profile_of_reflection
    (P : Measure BridgeNoise) [IsProbabilityMeasure P]
    (a y T z : ℝ) (hT : 0 < T) (hy : |y| < a) (hz : |z| < a)
    (hUpper : ∀ s : ℝ, s < a → upperCompletion P a s T z = upperReflection a s T z)
    (hLower : ∀ s : ℝ, -a < s → lowerCompletion P a s T z = lowerReflection a s T z)
    (hRegular : DifferentiableAt ℝ (fun s : ℝ => intervalCompletion P a s T z) y) :
    |deriv (fun s : ℝ => intervalCompletion P a s T z) y| ≤
      (8 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) * intervalProfile a y T z := by
  obtain ⟨hyl, hyu⟩ := abs_lt.mp hy
  obtain ⟨hzl, hzu⟩ := abs_lt.mp hz
  have hu := upperCompletion_hasDerivAt_of_reflection P a y T z hyu hUpper
  have hl := lowerCompletion_hasDerivAt_of_reflection P a y T z hyl hLower
  have hdom := signed_derivative_domination_of_hasDerivAt P a y T z _ _ _
    hu hRegular.hasDerivAt hl
  have hub := upperReflection_deriv_profile a y T z hT hyu hzu
  have hlb := lowerReflection_deriv_profile a y T z hT hyl hzl
  have hB : 0 ≤ 8 / Real.sqrt T * (1 + |z - y| / Real.sqrt T) := by positivity
  have hup : upperProfile a y T z ≤ intervalProfile a y T z :=
    le_add_of_nonneg_right (le_of_lt (Real.exp_pos _))
  have hlp : lowerProfile a y T z ≤ intervalProfile a y T z :=
    le_add_of_nonneg_left (le_of_lt (Real.exp_pos _))
  have huabs := hub.trans (mul_le_mul_of_nonneg_left hup hB)
  have hlabs := hlb.trans (mul_le_mul_of_nonneg_left hlp hB)
  exact abs_le.mpr ⟨(abs_le.mp huabs).1.trans hdom.1, hdom.2.trans (abs_le.mp hlabs).2⟩

end Shao.C2.CompletionFirstProfile
