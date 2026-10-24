import Shao.C2.HalfLineTaylorRemainder

noncomputable section
namespace Shao.C2.HalfLineSmallTaylor
open Shao.C2.HalfLineTaylorSegment Shao.C2.HalfLineTaylorPath
open Shao.C2.HalfLineTaylorRemainder Shao.C2.HalfLineMixedProfiles
open Shao.C2.HalfLineTimeProfiles Shao.C2.HalfLineSpatialProfiles

theorem normalized_power_domination (q D : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hD : 1 ≤ D) (k j : ℕ) (hj : j ≤ 3) :
    q ^ (3 + k) * D ^ j ≤ q ^ 3 * D ^ 3 := by
  have hq : q ^ (3 + k) ≤ q ^ 3 := by
    rw [pow_add]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (pow_le_one₀ hq0 hq1 : q ^ k ≤ 1) (pow_nonneg hq0 3)
  exact mul_le_mul hq (pow_le_pow_right₀ hD hj)
    (pow_nonneg (zero_le_one.trans hD) j) (pow_nonneg hq0 3)

theorem third_path_profile_at (u v T b θ : ℝ)
    (hE : 0 < segmentEnergy T b θ) (hU : 0 < segmentDistance u b θ) (hv : 0 < v)
    (hb : b ^ 2 ≤ segmentEnergy T b θ) :
    |deriv (deriv (deriv (completionAlongSegment u v T b))) θ| ≤
      34764 * |b| ^ 3 * (1 / Real.sqrt (segmentEnergy T b θ)) ^ 3 *
        (1 + |segmentDistance u b θ - v| / Real.sqrt (segmentEnergy T b θ)) ^ 3 *
          Real.exp (-segmentDistance u b θ * v / segmentEnergy T b θ) := by
  let E := segmentEnergy T b θ
  let U := segmentDistance u b θ
  let s := Real.sqrt E
  let D := 1 + |U - v| / s
  let P := Real.exp (-U * v / E)
  let q := |b| / s
  have hE' : 0 < E := hE
  have hU' : 0 < U := hU
  have hs : 0 < s := Real.sqrt_pos.2 hE
  have hs2 : s ^ 2 = E := Real.sq_sqrt hE.le
  have hbs : |b| ≤ s := by nlinarith [sq_abs b, abs_nonneg b]
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := (div_le_one hs).2 hbs
  have hD : 1 ≤ D := by
    dsimp only [D]
    linarith [div_nonneg (abs_nonneg (U - v)) hs.le]
  let A := -b ^ 3 * ((2 * v / E) ^ 3 * Real.exp (-2 * U * v / E))
  let B := 3 * b ^ 4 * deriv (curvatureTime U v) E
  let C := 3 * b ^ 5 * deriv (deriv (slopeTime U v)) E
  let F := b ^ 6 * deriv (deriv (deriv (timeCompletion (2 * U * v)))) E
  have hd : deriv (deriv (deriv (completionAlongSegment u v T b))) θ = A - B - C - F :=
    third_path_derivative_decomposition u v T b θ hE
  have hA : |A| ≤ 13824 * q ^ 3 * D ^ 3 * P := by
    have hp := positive_reflection_power_profile U v E hU hv hE 3 (by norm_num)
    calc
      |A| = |b| ^ 3 * ((2 * v / E) ^ 3 * Real.exp (-2 * U * v / E)) := by
        dsimp only [A]
        rw [abs_mul, abs_neg, abs_pow,
          abs_of_nonneg (mul_nonneg (pow_nonneg (div_nonneg (by positivity : (0 : ℝ) ≤ 2 * v) hE'.le) 3)
            (Real.exp_pos (-2 * U * v / E)).le)]
      _ ≤ |b| ^ 3 * ((8 * (3 : ℝ) / s * D) ^ 3 * P) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by dsimp only [q]; ring
  have hm := mixed_time_profiles U v E hU hv hE
  have hB : |B| ≤ 18432 * q ^ 4 * D ^ 2 * P := by
    calc
      |B| = 3 * |b| ^ 4 * |deriv (curvatureTime U v) E| := by
        dsimp only [B]; simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      _ ≤ 3 * |b| ^ 4 * (6144 / E ^ 2 * D ^ 2 * P) :=
        mul_le_mul_of_nonneg_left hm.2.1 (by positivity)
      _ = _ := by dsimp only [q]; rw [← hs2]; field_simp [ne_of_gt hs] <;> ring
  have hC : |C| ≤ 2400 * q ^ 5 * D * P := by
    calc
      |C| = 3 * |b| ^ 5 * |deriv (deriv (slopeTime U v)) E| := by
        dsimp only [C]; simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      _ ≤ 3 * |b| ^ 5 * (800 / (E ^ 2 * s) * D * P) :=
        mul_le_mul_of_nonneg_left hm.2.2 (by positivity)
      _ = _ := by dsimp only [q]; rw [← hs2]; field_simp [ne_of_gt hs] <;> ring
  have ht := (timeCompletion_time_profiles (2 * U * v) E (by positivity) hE).2.2
  have hpe : -(2 * U * v) / (2 * E) = -U * v / E := by field_simp [ne_of_gt hE] <;> ring
  rw [hpe] at ht
  have hF : |F| ≤ 108 * q ^ 6 * P := by
    calc
      |F| = |b| ^ 6 * |deriv (deriv (deriv (timeCompletion (2 * U * v)))) E| := by
        dsimp only [F]; simp only [abs_mul, abs_pow]
      _ ≤ |b| ^ 6 * (108 / E ^ 3 * P) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by dsimp only [q]; rw [← hs2]; field_simp [ne_of_gt hs] <;> ring
  have hnB := mul_le_mul_of_nonneg_right (normalized_power_domination q D hq0 hq1 hD 1 2 (by norm_num))
    (Real.exp_pos (-U * v / E)).le
  have hnC := mul_le_mul_of_nonneg_right (normalized_power_domination q D hq0 hq1 hD 2 1 (by norm_num))
    (Real.exp_pos (-U * v / E)).le
  have hnF := mul_le_mul_of_nonneg_right (normalized_power_domination q D hq0 hq1 hD 3 0 (by norm_num))
    (Real.exp_pos (-U * v / E)).le
  have hB' : |B| ≤ 18432 * q ^ 3 * D ^ 3 * P := by
    exact hB.trans (by nlinarith only [hnB])
  have hC' : |C| ≤ 2400 * q ^ 3 * D ^ 3 * P := by
    exact hC.trans (by nlinarith only [hnC])
  have hF' : |F| ≤ 108 * q ^ 3 * D ^ 3 * P := by
    exact hF.trans (by nlinarith only [hnF])
  have htri : |A - B - C - F| ≤ |A| + |B| + |C| + |F| := by
    calc
      _ ≤ |A - B - C| + |F| := by simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (A - B - C) (-F)
      _ ≤ (|A - B| + |C|) + |F| := by
        gcongr
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (A - B) (-C)
      _ ≤ _ := by
        gcongr
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le A (-B)
  have htotal : |deriv (deriv (deriv (completionAlongSegment u v T b))) θ| ≤
      34764 * q ^ 3 * D ^ 3 * P := by
    rw [hd]
    linarith only [htri, hA, hB', hC', hF']
  convert htotal using 1 <;> dsimp only [q, D, P, s, U, E] <;> ring

theorem third_path_segment_bound (u v T b θ : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2) (hnew : 0 ≤ u - b)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    |deriv (deriv (deriv (completionAlongSegment u v T b))) θ| ≤
      8000000 * |b| ^ 3 * (1 / Real.sqrt T) ^ 3 *
        (1 + |u - v| / Real.sqrt T) ^ 3 * incrementProfile u v T b := by
  have he := segment_energy_bounds T b θ hT hsmall hθ0 hθ1.le
  have huθ := segment_distance_pos u b θ hu hnew hθ0 hθ1
  have hb : b ^ 2 ≤ segmentEnergy T b θ := hsmall.trans he.2.1
  have h := third_path_profile_at u v T b θ he.1 huθ hv hb
  have hdis : segmentDistance u b θ - v = (u - v) - θ * b := by dsimp only [segmentDistance]; ring
  rw [hdis] at h
  have hp := segment_profile_transport u v (u - v) T b θ hu hv.le hT hsmall hnew hθ0 hθ1.le 3 3
  have hh := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ 34764 * |b| ^ 3)
  have hK : 0 ≤ |b| ^ 3 * (1 / Real.sqrt T) ^ 3 *
      (1 + |u - v| / Real.sqrt T) ^ 3 * incrementProfile u v T b := by
    unfold incrementProfile
    positivity
  calc
    _ ≤ 34764 * |b| ^ 3 * (1 / Real.sqrt (segmentEnergy T b θ)) ^ 3 *
        (1 + |(u - v) - θ * b| / Real.sqrt (segmentEnergy T b θ)) ^ 3 *
          Real.exp (-segmentDistance u b θ * v / segmentEnergy T b θ) := h
    _ ≤ 7509024 * (|b| ^ 3 * (1 / Real.sqrt T) ^ 3 *
        (1 + |u - v| / Real.sqrt T) ^ 3 * incrementProfile u v T b) := by
      convert hh using 1 <;> norm_num <;> ring
    _ ≤ 8000000 * (|b| ^ 3 * (1 / Real.sqrt T) ^ 3 *
        (1 + |u - v| / Real.sqrt T) ^ 3 * incrementProfile u v T b) :=
      mul_le_mul_of_nonneg_right (by norm_num) hK
    _ = _ := by ring

theorem compensation_correction_bound (u v T b : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2) (hnew : 0 ≤ u - b) :
    |b ^ 3 * deriv (slopeTime u v) T +
        (1 / 2 : ℝ) * b ^ 4 * deriv (deriv (timeCompletion (2 * u * v))) T| ≤
      86 * |b| ^ 3 * (1 / Real.sqrt T) ^ 3 *
        (1 + |u - v| / Real.sqrt T) ^ 3 * incrementProfile u v T b := by
  let s := Real.sqrt T
  let D := 1 + |u - v| / s
  let P := Real.exp (-u * v / T)
  let q := |b| / s
  have hs : 0 < s := Real.sqrt_pos.2 hT
  have hs2 : s ^ 2 = T := Real.sq_sqrt hT.le
  have hbs : |b| ≤ s := by nlinarith [sq_abs b, abs_nonneg b]
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := (div_le_one hs).2 hbs
  have hD : 1 ≤ D := by
    dsimp only [D]
    linarith [div_nonneg (abs_nonneg (u - v)) hs.le]
  have h1 : |b ^ 3 * deriv (slopeTime u v) T| ≤ 80 * q ^ 3 * D * P := by
    calc
      _ = |b| ^ 3 * |deriv (slopeTime u v) T| := by rw [abs_mul, abs_pow]
      _ ≤ |b| ^ 3 * (80 / (T * s) * D * P) :=
        mul_le_mul_of_nonneg_left (mixed_time_profiles u v T hu hv hT).1 (by positivity)
      _ = _ := by dsimp only [q]; rw [← hs2]; field_simp [ne_of_gt hs] <;> ring
  have ht := (timeCompletion_time_profiles (2 * u * v) T (by positivity) hT).2.1
  have hpe : -(2 * u * v) / (2 * T) = -u * v / T := by field_simp [ne_of_gt hT] <;> ring
  rw [hpe] at ht
  have h2 : |(1 / 2 : ℝ) * b ^ 4 * deriv (deriv (timeCompletion (2 * u * v))) T| ≤ 6 * q ^ 4 * P := by
    calc
      _ = (1 / 2 : ℝ) * |b| ^ 4 * |deriv (deriv (timeCompletion (2 * u * v))) T| := by
        rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      _ ≤ (1 / 2 : ℝ) * |b| ^ 4 * (12 / T ^ 2 * P) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by dsimp only [q]; rw [← hs2]; field_simp [ne_of_gt hs] <;> ring
  have hn1 := mul_le_mul_of_nonneg_right (normalized_power_domination q D hq0 hq1 hD 0 1 (by norm_num))
    (Real.exp_pos (-u * v / T)).le
  have hn2 := mul_le_mul_of_nonneg_right (normalized_power_domination q D hq0 hq1 hD 1 0 (by norm_num))
    (Real.exp_pos (-u * v / T)).le
  have h1' : |b ^ 3 * deriv (slopeTime u v) T| ≤ 80 * q ^ 3 * D ^ 3 * P :=
    h1.trans (by nlinarith only [hn1])
  have h2' : |(1 / 2 : ℝ) * b ^ 4 * deriv (deriv (timeCompletion (2 * u * v))) T| ≤ 6 * q ^ 3 * D ^ 3 * P :=
    h2.trans (by nlinarith only [hn2])
  have ha := abs_add_le (b ^ 3 * deriv (slopeTime u v) T)
    ((1 / 2 : ℝ) * b ^ 4 * deriv (deriv (timeCompletion (2 * u * v))) T)
  have hp := segment_profile_le_increment u v T b 0 hu hv.le hT hsmall hnew (by norm_num) (by norm_num)
  simp only [segmentEnergy, segmentDistance, zero_mul, sub_zero] at hp
  have hh := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ 86 * q ^ 3 * D ^ 3)
  have htotal : |b ^ 3 * deriv (slopeTime u v) T +
        (1 / 2 : ℝ) * b ^ 4 * deriv (deriv (timeCompletion (2 * u * v))) T| ≤
      86 * q ^ 3 * D ^ 3 * incrementProfile u v T b := by
    linarith only [ha, h1', h2', hh]
  convert htotal using 1 <;> dsimp only [q, D, s] <;> ring

theorem compensated_small_taylor_bound (u v T b : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2) (hnew : 0 ≤ u - b) :
    |completionAlongSegment u v T b 1 - completionAlongSegment u v T b 0 -
        (b - b ^ 2 * (u - v) / T) * (-slopeTime u v T)| ≤
      8000100 * |b| ^ 3 * (1 / Real.sqrt T) ^ 3 *
        (1 + |u - v| / Real.sqrt T) ^ 3 * incrementProfile u v T b := by
  obtain ⟨θ, hθ, heq⟩ := compensated_lagrange_remainder u v T b hT hsmall
  let K := |b| ^ 3 * (1 / Real.sqrt T) ^ 3 *
    (1 + |u - v| / Real.sqrt T) ^ 3 * incrementProfile u v T b
  have hK : 0 ≤ K := by dsimp only [K]; unfold incrementProfile; positivity
  have hd : |deriv (deriv (deriv (completionAlongSegment u v T b))) θ| ≤ 8000000 * K := by
    convert third_path_segment_bound u v T b θ hu hv hT hsmall hnew hθ.1.le hθ.2 using 1 <;> dsimp only [K] <;> ring
  have hc : |b ^ 3 * deriv (slopeTime u v) T +
      (1 / 2 : ℝ) * b ^ 4 * deriv (deriv (timeCompletion (2 * u * v))) T| ≤ 86 * K := by
    convert compensation_correction_bound u v T b hu hv hT hsmall hnew using 1 <;> dsimp only [K] <;> ring
  calc
    _ = |(1 / 6 : ℝ) * deriv (deriv (deriv (completionAlongSegment u v T b))) θ +
        (b ^ 3 * deriv (slopeTime u v) T +
          (1 / 2 : ℝ) * b ^ 4 * deriv (deriv (timeCompletion (2 * u * v))) T)| := by
      rw [heq]
      congr 1 <;> ring
    _ ≤ (1 / 6 : ℝ) * |deriv (deriv (deriv (completionAlongSegment u v T b))) θ| +
        |b ^ 3 * deriv (slopeTime u v) T +
          (1 / 2 : ℝ) * b ^ 4 * deriv (deriv (timeCompletion (2 * u * v))) T| := by
      simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6)] using
        abs_add_le ((1 / 6 : ℝ) * deriv (deriv (deriv (completionAlongSegment u v T b))) θ)
          (b ^ 3 * deriv (slopeTime u v) T +
            (1 / 2 : ℝ) * b ^ 4 * deriv (deriv (timeCompletion (2 * u * v))) T)
    _ ≤ (1 / 6 : ℝ) * (8000000 * K) + 86 * K :=
      add_le_add (mul_le_mul_of_nonneg_left hd (by norm_num)) hc
    _ ≤ 8000100 * K := by nlinarith only [hK]
    _ = _ := by dsimp only [K]; ring

end Shao.C2.HalfLineSmallTaylor
