import Shao.C2.CompletionFirstProfile

noncomputable section
namespace Shao.C2.HalfLineSpatialProfiles
open Shao.C2.HalfLineReflectionFormula Shao.C2.CompletionFirstProfile

theorem scaled_reflection_slope (u v T M : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hT : 0 < T) (hM : 1 ≤ M) :
    (2 * v / T) * Real.exp (-2 * u * v / (M * T)) ≤
      4 * M / Real.sqrt T * (1 + |u - v| / Real.sqrt T) := by
  have hMp : 0 < M := by linarith
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hsM : Real.sqrt T ≤ Real.sqrt (M * T) := Real.sqrt_le_sqrt (by nlinarith)
  have h := positive_reflection_slope_bound u v (M * T) hu hv (mul_pos hMp hT)
  have hfactor : 4 / Real.sqrt (M * T) * (1 + |u - v| / Real.sqrt (M * T)) ≤
      4 / Real.sqrt T * (1 + |u - v| / Real.sqrt T) := by
    apply mul_le_mul
    · exact div_le_div_of_nonneg_left (by norm_num) hs hsM
    · have hd := div_le_div_of_nonneg_left (abs_nonneg (u - v)) hs hsM
      linarith
    · positivity
    · positivity
  have hh := mul_le_mul_of_nonneg_left (h.trans hfactor) hMp.le
  convert hh using 1 <;> field_simp [ne_of_gt hMp, ne_of_gt hT, ne_of_gt hs] <;> ring

theorem positive_reflection_power_profile (u v T : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hT : 0 < T) (j : ℕ) (hj : 0 < j) :
    (2 * v / T) ^ j * Real.exp (-2 * u * v / T) ≤
      (8 * (j : ℝ) / Real.sqrt T * (1 + |u - v| / Real.sqrt T)) ^ j *
        Real.exp (-u * v / T) := by
  have hjp : 0 < (j : ℝ) := by exact_mod_cast hj
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hj)
  have h := scaled_reflection_slope u v T (2 * (j : ℝ)) hu hv hT (by linarith)
  have he : -2 * u * v / ((2 * (j : ℝ)) * T) = -u * v / ((j : ℝ) * T) := by
    field_simp [ne_of_gt hjp, ne_of_gt hT] <;> ring
  rw [he] at h
  have hbase : (2 * v / T) * Real.exp (-u * v / ((j : ℝ) * T)) ≤
      8 * (j : ℝ) / Real.sqrt T * (1 + |u - v| / Real.sqrt T) := by
    convert h using 1 <;> ring
  have hp := pow_le_pow_left₀ (show 0 ≤ (2 * v / T) * Real.exp (-u * v / ((j : ℝ) * T))
    by positivity) hbase j
  have hepower : Real.exp (-u * v / ((j : ℝ) * T)) ^ j = Real.exp (-u * v / T) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp [ne_of_gt hjp, ne_of_gt hT] <;> ring
  rw [mul_pow, hepower] at hp
  have he2 : Real.exp (-2 * u * v / T) =
      Real.exp (-u * v / T) * Real.exp (-u * v / T) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he2, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hp (le_of_lt (Real.exp_pos _))

theorem upperReflection_iteratedDeriv (j : ℕ) (a y T z : ℝ) :
    iteratedDeriv j (fun u : ℝ => upperReflection a u T z - 1) y =
      -((2 * (a - z) / T) ^ j) * Real.exp (-2 * (a - y) * (a - z) / T) := by
  let c : ℝ := 2 * (a - z) / T
  let b : ℝ := -2 * a * (a - z) / T
  have hfun : (fun u : ℝ => upperReflection a u T z - 1) =
      (fun u : ℝ => -Real.exp b * Real.exp (c * u)) := by
    funext u
    change 1 - Real.exp (-2 * (a - u) * (a - z) / T) - 1 = _
    calc
      _ = -Real.exp (-2 * (a - u) * (a - z) / T) := by ring
      _ = -(Real.exp b * Real.exp (c * u)) := by
        rw [← Real.exp_add]
        congr 2 <;> dsimp [b, c] <;> ring
      _ = -Real.exp b * Real.exp (c * u) := by ring
  rw [hfun, iteratedDeriv_const_mul_field, iteratedDeriv_exp_const_mul]
  change -Real.exp b * (c ^ j * Real.exp (c * y)) =
    -(c ^ j) * Real.exp (-2 * (a - y) * (a - z) / T)
  calc
    _ = -(c ^ j) * (Real.exp b * Real.exp (c * y)) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2 <;> dsimp [b, c] <;> ring

theorem lowerReflection_iteratedDeriv (j : ℕ) (a y T z : ℝ) :
    iteratedDeriv j (fun u : ℝ => lowerReflection a u T z - 1) y =
      -((-(2 * (a + z) / T)) ^ j) * Real.exp (-2 * (a + y) * (a + z) / T) := by
  let c : ℝ := -(2 * (a + z) / T)
  let b : ℝ := -2 * a * (a + z) / T
  have hfun : (fun u : ℝ => lowerReflection a u T z - 1) =
      (fun u : ℝ => -Real.exp b * Real.exp (c * u)) := by
    funext u
    change 1 - Real.exp (-2 * (a + u) * (a + z) / T) - 1 = _
    calc
      _ = -Real.exp (-2 * (a + u) * (a + z) / T) := by ring
      _ = -(Real.exp b * Real.exp (c * u)) := by
        rw [← Real.exp_add]
        congr 2 <;> dsimp [b, c] <;> ring
      _ = -Real.exp b * Real.exp (c * u) := by ring
  rw [hfun, iteratedDeriv_const_mul_field, iteratedDeriv_exp_const_mul]
  change -Real.exp b * (c ^ j * Real.exp (c * y)) =
    -(c ^ j) * Real.exp (-2 * (a + y) * (a + z) / T)
  calc
    _ = -(c ^ j) * (Real.exp b * Real.exp (c * y)) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2 <;> dsimp [b, c] <;> ring

theorem upperReflection_iterated_profile (j : ℕ) (hj : 0 < j)
    (a y T z : ℝ) (hT : 0 < T) (hy : y < a) (hz : z < a) :
    |iteratedDeriv j (fun u : ℝ => upperReflection a u T z - 1) y| ≤
      (8 * (j : ℝ) / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j *
        upperProfile a y T z := by
  rw [upperReflection_iteratedDeriv, abs_mul, abs_neg, abs_pow,
    abs_of_pos (show 0 < 2 * (a - z) / T by positivity), abs_of_pos (Real.exp_pos _)]
  have h := positive_reflection_power_profile (a - y) (a - z) T (by linarith) (by linarith) hT j hj
  simpa only [upperProfile, show a - y - (a - z) = z - y by ring] using h

theorem lowerReflection_iterated_profile (j : ℕ) (hj : 0 < j)
    (a y T z : ℝ) (hT : 0 < T) (hy : -a < y) (hz : -a < z) :
    |iteratedDeriv j (fun u : ℝ => lowerReflection a u T z - 1) y| ≤
      (8 * (j : ℝ) / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j *
        lowerProfile a y T z := by
  have haz : 0 < a + z := by linarith
  rw [lowerReflection_iteratedDeriv, abs_mul, abs_neg, abs_pow, abs_neg,
    abs_of_pos (show 0 < 2 * (a + z) / T by positivity), abs_of_pos (Real.exp_pos _)]
  have h := positive_reflection_power_profile (a + y) (a + z) T (by linarith) (by linarith) hT j hj
  simpa only [lowerProfile, show a + y - (a + z) = y - z by ring, abs_sub_comm y z] using h

end Shao.C2.HalfLineSpatialProfiles
