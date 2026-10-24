import Shao.C2.HalfLineSpatialProfiles
import Shao.C2.HalfLineTimeProfiles

noncomputable section
namespace Shao.C2.HalfLineMixedProfiles
open Shao.C2.HalfLineReflectionFormula Shao.C2.HalfLineHeatEquation
open Shao.C2.CompletionFirstProfile Shao.C2.HalfLineSpatialProfiles Shao.C2.HalfLineTimeProfiles

def slopeTime (u v T : ℝ) : ℝ := (2 * v / T) * Real.exp (-2 * u * v / T)
def curvatureTime (u v T : ℝ) : ℝ := -((2 * v / T) ^ 2) * Real.exp (-2 * u * v / T)

theorem positive_reflection_power_monomial_profile (u v T : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hT : 0 < T) (j : ℕ) (hj : 0 < j) (m : ℕ) :
    (2 * v / T) ^ j * (2 * u * v / T) ^ m * Real.exp (-2 * u * v / T) ≤
      (16 * (j : ℝ) / Real.sqrt T * (1 + |u - v| / Real.sqrt T)) ^ j *
        ((4 : ℝ) ^ m * (Nat.factorial m : ℝ)) * Real.exp (-u * v / T) := by
  let q : ℝ := 2 * u * v / T
  let A : ℝ := 8 * (j : ℝ) / Real.sqrt T * (1 + |u - v| / Real.sqrt T)
  let B : ℝ := 16 * (j : ℝ) / Real.sqrt T * (1 + |u - v| / Real.sqrt T)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hjp : 0 < (j : ℝ) := by exact_mod_cast hj
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hs2 : Real.sqrt T ≤ Real.sqrt (2 * T) := Real.sqrt_le_sqrt (by linarith)
  have h := positive_reflection_power_profile u v (2 * T) hu hv (by positivity) j hj
  have he1 : -2 * u * v / (2 * T) = -q / 2 := by dsimp [q]; field_simp [ne_of_gt hT] <;> ring
  have he2 : -u * v / (2 * T) = -q / 4 := by dsimp [q]; field_simp [ne_of_gt hT] <;> ring
  rw [he1, he2] at h
  have hf : 8 * (j : ℝ) / Real.sqrt (2 * T) * (1 + |u - v| / Real.sqrt (2 * T)) ≤ A := by
    apply mul_le_mul
    · exact div_le_div_of_nonneg_left (by positivity) hs hs2
    · have hd := div_le_div_of_nonneg_left (abs_nonneg (u - v)) hs hs2
      linarith
    · positivity
    · positivity
  have hp := h.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) hf j) (le_of_lt (Real.exp_pos _)))
  have hc : (2 : ℝ) * (2 * v / (2 * T)) = 2 * v / T := by field_simp [ne_of_gt hT] <;> ring
  have hAB : 2 * A = B := by dsimp [A, B]; ring
  have hSpatial : (2 * v / T) ^ j * Real.exp (-q / 2) ≤ B ^ j * Real.exp (-q / 4) := by
    calc
      _ = (2 : ℝ) ^ j * ((2 * v / (2 * T)) ^ j * Real.exp (-q / 2)) := by rw [← hc, mul_pow]; ring
      _ ≤ (2 : ℝ) ^ j * (A ^ j * Real.exp (-q / 4)) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = B ^ j * Real.exp (-q / 4) := by rw [← mul_assoc, ← mul_pow, hAB]
  have hm := nonneg_exp_monomial_profile (q / 2) (by positivity) m
  have hMoment : q ^ m * Real.exp (-q / 2) ≤
      ((4 : ℝ) ^ m * (Nat.factorial m : ℝ)) * Real.exp (-q / 4) := by
    have he : -(q / 2) = -q / 2 := by ring
    have he' : -q / 2 / 2 = -q / 4 := by ring
    rw [he, he'] at hm
    calc
      _ = (2 : ℝ) ^ m * ((q / 2) ^ m * Real.exp (-q / 2)) := by
        rw [← mul_assoc, ← mul_pow, show (2 : ℝ) * (q / 2) = q by ring]
      _ ≤ (2 : ℝ) ^ m * ((2 : ℝ) ^ m * (Nat.factorial m : ℝ) * Real.exp (-q / 4)) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ = ((2 : ℝ) ^ m * 2 ^ m) * (Nat.factorial m : ℝ) * Real.exp (-q / 4) := by ring
      _ = _ := by rw [← mul_pow]; norm_num
  have hProd := mul_le_mul hSpatial hMoment (by positivity) (by dsimp [B]; positivity)
  have heHalf : Real.exp (-q / 2) * Real.exp (-q / 2) = Real.exp (-q) := by rw [← Real.exp_add]; congr 1; ring
  have heQuarter : Real.exp (-q / 4) * Real.exp (-q / 4) = Real.exp (-q / 2) := by rw [← Real.exp_add]; congr 1; ring
  have he : Real.exp (-2 * u * v / T) = Real.exp (-q) := by congr 1; dsimp [q]; ring
  have he' : Real.exp (-u * v / T) = Real.exp (-q / 2) := by congr 1; dsimp [q]; field_simp [ne_of_gt hT] <;> ring
  rw [he, he']
  change (2 * v / T) ^ j * q ^ m * Real.exp (-q) ≤
    B ^ j * ((4 : ℝ) ^ m * (Nat.factorial m : ℝ)) * Real.exp (-q / 2)
  calc
    _ = ((2 * v / T) ^ j * Real.exp (-q / 2)) * (q ^ m * Real.exp (-q / 2)) := by rw [← heHalf]; ring
    _ ≤ (B ^ j * Real.exp (-q / 4)) * (((4 : ℝ) ^ m * (Nat.factorial m : ℝ)) * Real.exp (-q / 4)) := hProd
    _ = _ := by rw [← heQuarter]; ring

theorem slopeTime_hasDerivAt (u v T : ℝ) (hT : 0 < T) :
    HasDerivAt (slopeTime u v)
      ((2 * v / T ^ 2) * (2 * u * v / T - 1) * Real.exp (-2 * u * v / T)) T := by
  have hc := (hasDerivAt_const T (2 * v)).div (hasDerivAt_id T) (ne_of_gt hT)
  have he := ((hasDerivAt_const T (-2 * u * v)).div (hasDerivAt_id T) (ne_of_gt hT)).exp
  have h := hc.mul he
  convert h using 1
  · rfl
  · dsimp only [Pi.div_apply, id_eq]
    field_simp [ne_of_gt hT] <;> ring

theorem slopeTime_second_hasDerivAt (u v T : ℝ) (hT : 0 < T) :
    HasDerivAt (deriv (slopeTime u v))
      ((2 * v / T ^ 3) * (2 - 4 * (2 * u * v / T) + (2 * u * v / T) ^ 2) *
        Real.exp (-2 * u * v / T)) T := by
  have ha := (hasDerivAt_const T (2 * v * (2 * u * v))).div ((hasDerivAt_id T).pow 3)
    (pow_ne_zero 3 (ne_of_gt hT))
  have hb := (hasDerivAt_const T (2 * v)).div ((hasDerivAt_id T).pow 2)
    (pow_ne_zero 2 (ne_of_gt hT))
  have he := ((hasDerivAt_const T (-2 * u * v)).div (hasDerivAt_id T) (ne_of_gt hT)).exp
  have h := (ha.sub hb).mul he
  have hf : HasDerivAt (fun t : ℝ => (2 * v * (2 * u * v) / t ^ 3 - 2 * v / t ^ 2) * Real.exp (-2 * u * v / t))
      ((2 * v / T ^ 3) * (2 - 4 * (2 * u * v / T) + (2 * u * v / T) ^ 2) * Real.exp (-2 * u * v / T)) T := by
    convert h using 1
    · rfl
    · dsimp only [Pi.div_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
      field_simp [ne_of_gt hT] <;> ring
  apply hf.congr_of_eventuallyEq
  refine Filter.mem_of_superset (Ioi_mem_nhds hT) ?_
  intro t ht
  have ht0 : 0 < t := ht
  change deriv (slopeTime u v) t = (2 * v * (2 * u * v) / t ^ 3 - 2 * v / t ^ 2) * Real.exp (-2 * u * v / t)
  rw [(slopeTime_hasDerivAt u v t ht).deriv]
  field_simp [ne_of_gt ht0] <;> ring

theorem curvatureTime_hasDerivAt (u v T : ℝ) (hT : 0 < T) :
    HasDerivAt (curvatureTime u v)
      ((2 * v / T) ^ 2 / T * (2 - 2 * u * v / T) * Real.exp (-2 * u * v / T)) T := by
  have hc := (hasDerivAt_const T (-((2 * v) ^ 2))).div ((hasDerivAt_id T).pow 2)
    (pow_ne_zero 2 (ne_of_gt hT))
  have he := ((hasDerivAt_const T (-2 * u * v)).div (hasDerivAt_id T) (ne_of_gt hT)).exp
  have h := hc.mul he
  convert h using 1
  · funext t
    dsimp only [curvatureTime, Pi.mul_apply, Pi.div_apply, Pi.pow_apply, id_eq]
    rw [div_pow]
    ring
  · dsimp only [Pi.div_apply, Pi.pow_apply, id_eq]
    field_simp [ne_of_gt hT] <;> ring

theorem mixed_time_profiles (u v T : ℝ) (hu : 0 < u) (hv : 0 < v) (hT : 0 < T) :
    |deriv (slopeTime u v) T| ≤
      80 / (T * Real.sqrt T) * (1 + |u - v| / Real.sqrt T) * Real.exp (-u * v / T) ∧
    |deriv (curvatureTime u v) T| ≤
      6144 / T ^ 2 * (1 + |u - v| / Real.sqrt T) ^ 2 * Real.exp (-u * v / T) ∧
    |deriv (deriv (slopeTime u v)) T| ≤
      800 / (T ^ 2 * Real.sqrt T) * (1 + |u - v| / Real.sqrt T) * Real.exp (-u * v / T) := by
  let q : ℝ := 2 * u * v / T
  let c : ℝ := 2 * v / T
  let E : ℝ := Real.exp (-q)
  let P : ℝ := Real.exp (-q / 2)
  let D : ℝ := 1 + |u - v| / Real.sqrt T
  let B1 : ℝ := 16 / Real.sqrt T * D
  let B2 : ℝ := 32 / Real.sqrt T * D
  let S0 : ℝ := c * E
  let S1 : ℝ := c * q * E
  let S2 : ℝ := c * q ^ 2 * E
  let K0 : ℝ := c ^ 2 * E
  let K1 : ℝ := c ^ 2 * q * E
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hE : 0 < E := Real.exp_pos _
  have hP : 0 < P := Real.exp_pos _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hB1 : 0 ≤ B1 := by dsimp [B1]; positivity
  have hB2 : 0 ≤ B2 := by dsimp [B2]; positivity
  have hS0 := positive_reflection_power_monomial_profile u v T hu hv hT 1 (by norm_num) 0
  have hS1 := positive_reflection_power_monomial_profile u v T hu hv hT 1 (by norm_num) 1
  have hS2 := positive_reflection_power_monomial_profile u v T hu hv hT 1 (by norm_num) 2
  have hK0 := positive_reflection_power_monomial_profile u v T hu hv hT 2 (by norm_num) 0
  have hK1 := positive_reflection_power_monomial_profile u v T hu hv hT 2 (by norm_num) 1
  have he : Real.exp (-2 * u * v / T) = E := by dsimp only [E, q]; congr 1; ring
  have hp : Real.exp (-u * v / T) = P := by dsimp only [P, q]; congr 1; field_simp [ne_of_gt hT] <;> ring
  rw [he, hp] at hS0 hS1 hS2 hK0 hK1
  norm_num at hS0 hS1 hS2 hK0 hK1
  change S0 ≤ B1 * P at hS0
  change S1 ≤ B1 * 4 * P at hS1
  change S2 ≤ B1 * 32 * P at hS2
  change K0 ≤ B2 ^ 2 * P at hK0
  change K1 ≤ B2 ^ 2 * 4 * P at hK1
  have nS0 : 0 ≤ S0 := mul_nonneg hc hE.le
  have nS1 : 0 ≤ S1 := mul_nonneg (mul_nonneg hc hq) hE.le
  have nS2 : 0 ≤ S2 := mul_nonneg (mul_nonneg hc (sq_nonneg q)) hE.le
  have nK0 : 0 ≤ K0 := mul_nonneg (sq_nonneg c) hE.le
  have nK1 : 0 ≤ K1 := mul_nonneg (mul_nonneg (sq_nonneg c) hq) hE.le
  have ha1 : |S1 - S0| ≤ 5 * B1 * P := by apply abs_le.mpr; constructor <;> nlinarith
  have ha2 : |2 * K0 - K1| ≤ 6 * B2 ^ 2 * P := by apply abs_le.mpr; constructor <;> nlinarith
  have ha3 : |2 * S0 - 4 * S1 + S2| ≤ 50 * B1 * P := by apply abs_le.mpr; constructor <;> nlinarith
  have hf1 : deriv (slopeTime u v) T = (S1 - S0) / T := by
    rw [(slopeTime_hasDerivAt u v T hT).deriv, he]
    dsimp only [S1, S0, c, q]
    field_simp [ne_of_gt hT] <;> ring
  have hf2 : deriv (curvatureTime u v) T = (2 * K0 - K1) / T := by
    rw [(curvatureTime_hasDerivAt u v T hT).deriv, he]
    dsimp only [K0, K1, c, q]
    field_simp [ne_of_gt hT] <;> ring
  have hf3 : deriv (deriv (slopeTime u v)) T = (2 * S0 - 4 * S1 + S2) / T ^ 2 := by
    rw [(slopeTime_second_hasDerivAt u v T hT).deriv, he]
    dsimp only [S0, S1, S2, c, q]
    field_simp [ne_of_gt hT] <;> ring
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hr1 : (5 * B1 * P) / T = 80 / (T * Real.sqrt T) * D * P := by
    dsimp only [B1]; field_simp [ne_of_gt hT, ne_of_gt hs] <;> ring
  have hr2 : (6 * B2 ^ 2 * P) / T = 6144 / T ^ 2 * D ^ 2 * P := by
    dsimp only [B2]
    rw [mul_pow, div_pow, Real.sq_sqrt hT.le]
    field_simp [ne_of_gt hT] <;> ring
  have hr3 : (50 * B1 * P) / T ^ 2 = 800 / (T ^ 2 * Real.sqrt T) * D * P := by
    dsimp only [B1]; field_simp [ne_of_gt hT, ne_of_gt hs] <;> ring
  rw [hp]
  refine ⟨?_, ?_, ?_⟩
  · rw [hf1, abs_div, abs_of_pos hT]
    exact ((div_le_div_iff_of_pos_right hT).2 ha1).trans_eq hr1
  · rw [hf2, abs_div, abs_of_pos hT]
    exact ((div_le_div_iff_of_pos_right hT).2 ha2).trans_eq hr2
  · rw [hf3, abs_div, abs_of_pos (pow_pos hT 2)]
    exact ((div_le_div_iff_of_pos_right (pow_pos hT 2)).2 ha3).trans_eq hr3

theorem upperReflection_mixed_functions (a y z : ℝ) :
    (fun t : ℝ => deriv (fun w : ℝ => upperReflection a w t z) y) =
      (fun t : ℝ => -slopeTime (a - y) (a - z) t) ∧
    (fun t : ℝ => deriv (deriv (fun w : ℝ => upperReflection a w t z)) y) =
      (fun t : ℝ => curvatureTime (a - y) (a - z) t) := by
  constructor
  · funext t
    rw [(upperReflection_hasDerivAt a y t z).deriv]
    unfold slopeTime
    ring
  · funext t
    exact (upperReflection_second_hasDerivAt a y t z).deriv

theorem lowerReflection_mixed_functions (a y z : ℝ) :
    (fun t : ℝ => deriv (fun w : ℝ => lowerReflection a w t z) y) =
      (fun t : ℝ => slopeTime (a + y) (a + z) t) ∧
    (fun t : ℝ => deriv (deriv (fun w : ℝ => lowerReflection a w t z)) y) =
      (fun t : ℝ => curvatureTime (a + y) (a + z) t) := by
  constructor
  · funext t
    exact (lowerReflection_hasDerivAt a y t z).deriv
  · funext t
    exact (lowerReflection_second_hasDerivAt a y t z).deriv

end Shao.C2.HalfLineMixedProfiles
