import Shao.C2.GaussianWallEnvelope
import Shao.C2.HalfLineSmallTaylor

noncomputable section
namespace Shao.C2.HalfLineGaussianStep
open Shao.C2.GaussianWallEnvelope Shao.C2.HalfLineTaylorSegment
open Shao.C2.HalfLineTaylorPath Shao.C2.HalfLineMixedProfiles
open Shao.C2.HalfLineSpatialProfiles Shao.C2.HalfLineSmallTaylor

def completion (u v T : ℝ) : ℝ :=
  if 0 < u ∧ 0 < v then
    if 0 < T then 1 - Real.exp (-2 * u * v / T)
    else if T = 0 ∧ u = v then 1 else 0
  else 0

def localRemainder (u v T b : ℝ) : ℝ :=
  completion (u - b) v (T - b ^ 2) - completion u v T -
    (b - b ^ 2 * (u - v) / T) * (-slopeTime u v T)

def retainedRemainder (u v T b : ℝ) : ℝ :=
  if b ^ 2 ≤ T / 2 ∧ u - b ≤ 0 then localRemainder u v T u
  else localRemainder u v T b

theorem completion_positive_time (u v T : ℝ) (hu : 0 ≤ u) (hv : 0 < v) (hT : 0 < T) :
    completion u v T = 1 - Real.exp (-2 * u * v / T) := by
  by_cases hp : 0 < u
  · simp [completion, hp, hv, hT]
  · have he : u = 0 := le_antisymm (le_of_not_gt hp) hu
    subst u
    simp [completion]

theorem completion_bounds (u v T : ℝ) :
    0 ≤ completion u v T ∧ completion u v T ≤ 1 := by
  by_cases h : 0 < u ∧ 0 < v
  · by_cases ht : 0 < T
    · rw [completion, if_pos h, if_pos ht]
      have hx : -2 * u * v / T ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by nlinarith [mul_pos h.1 h.2]) ht.le
      have he : Real.exp (-2 * u * v / T) ≤ 1 := by
        simpa only [Real.exp_zero] using Real.exp_le_exp.2 hx
      constructor <;> linarith [Real.exp_pos (-2 * u * v / T)]
    · by_cases hz : T = 0 ∧ u = v <;> simp [completion, h, ht, hz]
  · simp [completion, h]

theorem completion_reachable_zero_time (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (h : u = v) :
    completion u v 0 = 1 := by
  simp [completion, hu, hv, h]

theorem compensation_envelope_bound (u v T b : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hT : 0 < T) (hb : b ^ 2 ≤ T) :
    |(b - b ^ 2 * (u - v) / T) * (-slopeTime u v T)| ≤
      8 * (|b| / Real.sqrt T) * (1 + |u - v| / Real.sqrt T) ^ 2 *
        wallEnvelope u |b| (u - v) T := by
  let s := Real.sqrt T
  let q := |b| / s
  let t := |u - v| / s
  let D := 1 + t
  let P := wallEnvelope u |b| (u - v) T
  have hs : 0 < s := Real.sqrt_pos.2 hT
  have hs2 : s ^ 2 = T := Real.sq_sqrt hT.le
  have hbs : |b| ≤ s := by nlinarith [sq_abs b, abs_nonneg b]
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := (div_le_one hs).2 hbs
  have hq2 : q ^ 2 ≤ q := by nlinarith
  have ht : 0 ≤ t := by positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hP : 0 ≤ P := (wallEnvelope_bounds u |b| (u - v) T hT).1.le
  have he : u - v < u := by linarith
  have hi : Real.exp (-u * v / T) ≤ P := by
    convert initial_profile_le_wallEnvelope u (u - v) T b hu he hT using 1 <;> ring
  have hsl := positive_reflection_power_profile u v T hu hv hT 1 (by norm_num)
  norm_num only [Nat.cast_one, mul_one, pow_one] at hsl
  have hsl' : slopeTime u v T ≤ 8 / s * D * P := by
    have hh := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 8 / s * D)
    exact hsl.trans hh
  have hc : |b - b ^ 2 * (u - v) / T| ≤ |b| + b ^ 2 * |u - v| / T := by
    have hh := abs_add_le b (-(b ^ 2 * (u - v) / T))
    simpa only [sub_eq_add_neg, abs_neg, abs_div, abs_mul, abs_pow, sq_abs,
      abs_of_pos hT] using hh
  have hc0 : 0 ≤ |b| + b ^ 2 * |u - v| / T := by positivity
  have hsl0 : 0 ≤ slopeTime u v T := by dsimp only [slopeTime]; positivity
  calc
    _ = |b - b ^ 2 * (u - v) / T| * slopeTime u v T := by
      rw [abs_mul, abs_neg, abs_of_nonneg hsl0]
    _ ≤ (|b| + b ^ 2 * |u - v| / T) * (8 / s * D * P) :=
      mul_le_mul hc hsl' hsl0 hc0
    _ = 8 * (q + q ^ 2 * t) * D * P := by
      dsimp only [q, t]
      rw [← hs2, ← sq_abs b]
      field_simp [ne_of_gt hs] <;> ring
    _ ≤ 8 * (q + q * t) * D * P := by
      have hh := mul_le_mul_of_nonneg_right hq2 ht
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (add_le_add (le_refl q) hh) (by norm_num : (0 : ℝ) ≤ 8)) hD) hP
    _ = _ := by dsimp only [q, t, D, P, s]; ring

theorem future_deficit_envelope_bound (u v T b : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hT : 0 < T) (hb : b ^ 2 ≤ T) (hnew : 0 ≤ u - b)
    (hzero : T - b ^ 2 = 0 → u - b = v) :
    1 - completion (u - b) v (T - b ^ 2) ≤ wallEnvelope u |b| (u - v) T := by
  have hE : 0 ≤ T - b ^ 2 := sub_nonneg.mpr hb
  by_cases hz : T - b ^ 2 = 0
  · have heq := hzero hz
    have hp : 0 < u - b := by rw [heq]; exact hv
    rw [hz, completion_reachable_zero_time (u - b) v hp hv heq, sub_self]
    exact (wallEnvelope_bounds u |b| (u - v) T hT).1.le
  · have hp : 0 < T - b ^ 2 := lt_of_le_of_ne hE (Ne.symm hz)
    rw [completion_positive_time (u - b) v (T - b ^ 2) hnew hv hp]
    have he : u - v < u := by linarith
    convert future_reflection_deficit_le_wallEnvelope u (u - v) T b hu he hT hnew hp using 1 <;> ring

theorem completion_difference_envelope_bound (u v T b : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hT : 0 < T) (hb : b ^ 2 ≤ T)
    (hzero : T - b ^ 2 = 0 → u - b = v) :
    |completion (u - b) v (T - b ^ 2) - completion u v T| ≤
      2 * wallEnvelope u |b| (u - v) T := by
  have hf := completion_bounds u v T
  have hg := completion_bounds (u - b) v (T - b ^ 2)
  have hP := (wallEnvelope_bounds u |b| (u - v) T hT).1.le
  by_cases hn : 0 ≤ u - b
  · have hgP := future_deficit_envelope_bound u v T b hu hv hT hb hn hzero
    have hfP : 1 - completion u v T ≤ wallEnvelope u |b| (u - v) T := by
      rw [completion_positive_time u v T hu.le hv hT]
      have he : u - v < u := by linarith
      have hh : Real.exp (-u * v / T) ≤ wallEnvelope u |b| (u - v) T := by
        convert initial_profile_le_wallEnvelope u (u - v) T b hu he hT using 1 <;> ring
      have hx : -2 * u * v / T ≤ -u * v / T := by
        apply (div_le_div_iff_of_pos_right hT).2
        nlinarith [mul_pos hu hv]
      have h := (Real.exp_le_exp.2 hx).trans hh
      linarith only [h]
    have hh : |completion (u - b) v (T - b ^ 2) - completion u v T| ≤
        (1 - completion (u - b) v (T - b ^ 2)) + (1 - completion u v T) := by
      apply abs_le.mpr
      constructor <;> linarith only [hf.2, hg.2]
    linarith only [hh, hfP, hgP]
  · have hc : u ≤ |b| := le_trans (by linarith only [hn]) (le_abs_self b)
    rw [crossing_wallEnvelope_eq_one u b (u - v) T hu hc]
    have hz : completion (u - b) v (T - b ^ 2) = 0 := by
      rw [completion, if_neg (by intro h; linarith only [hn, h.1])]
    rw [hz, zero_sub, abs_neg, abs_of_nonneg hf.1]
    linarith only [hf.2]

theorem local_small_envelope_bound (u v T b : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hT : 0 < T) (hb : b ^ 2 ≤ T / 2) (hnew : 0 ≤ u - b) :
    |localRemainder u v T b| ≤
      8000100 * (|b| / Real.sqrt T) ^ 3 * (1 + |u - v| / Real.sqrt T) ^ 3 *
        wallEnvelope u |b| (u - v) T := by
  have hE : 0 < T - b ^ 2 := by linarith only [hb, hT]
  have hh := compensated_small_taylor_bound u v T b hu hv hT hb hnew
  dsimp only [completionAlongSegment, segmentDistance, segmentEnergy] at hh
  simp only [one_mul, zero_mul, sub_zero] at hh
  have he : u - v < u := by linarith
  have hp : incrementProfile u v T b ≤ wallEnvelope u |b| (u - v) T := by
    convert increment_profile_le_wallEnvelope u (u - v) T b hu he hT using 1 <;> ring
  have hd := mul_le_mul_of_nonneg_left hp (by positivity :
    0 ≤ 8000100 * |b| ^ 3 * (1 / Real.sqrt T) ^ 3 * (1 + |u - v| / Real.sqrt T) ^ 3)
  rw [localRemainder, completion_positive_time (u - b) v (T - b ^ 2) hnew hv hE,
    completion_positive_time u v T hu.le hv hT]
  convert hh.trans hd using 1 <;> ring

theorem local_large_envelope_bound (u v T b : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hT : 0 < T) (hb : b ^ 2 ≤ T) (hlarge : T / 2 < b ^ 2)
    (hzero : T - b ^ 2 = 0 → u - b = v) :
    |localRemainder u v T b| ≤
      8000100 * (|b| / Real.sqrt T) ^ 3 * (1 + |u - v| / Real.sqrt T) ^ 3 *
        wallEnvelope u |b| (u - v) T := by
  let s := Real.sqrt T
  let q := |b| / s
  let D := 1 + |u - v| / s
  let P := wallEnvelope u |b| (u - v) T
  have hs : 0 < s := Real.sqrt_pos.2 hT
  have hs2 : s ^ 2 = T := Real.sq_sqrt hT.le
  have hq0 : 0 ≤ q := by positivity
  have hbs : |b| ≤ s := by nlinarith [sq_abs b, abs_nonneg b]
  have hq1 : q ≤ 1 := (div_le_one hs).2 hbs
  have hqeq : q ^ 2 = b ^ 2 / T := by dsimp only [q]; rw [div_pow, sq_abs, hs2]
  have hqbig : (1 / 2 : ℝ) < q ^ 2 := by
    rw [hqeq]
    apply (lt_div_iff₀ hT).2
    linarith only [hlarge]
  have hqhalf : (1 / 2 : ℝ) ≤ q := by
    by_contra h
    have hh := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge h)) hq0
    nlinarith only [hh, hqbig]
  have hqpay : 1 ≤ 4 * q ^ 3 := by
    have hh := mul_le_mul_of_nonneg_left hqhalf (sq_nonneg q)
    nlinarith only [hh, hqbig]
  have hD : 1 ≤ D := by
    dsimp only [D]
    linarith only [div_nonneg (abs_nonneg (u - v)) hs.le]
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hD3 : 1 ≤ D ^ 3 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hD 3
  have hD23 : D ^ 2 ≤ D ^ 3 := pow_le_pow_right₀ hD (by norm_num)
  have hqD : q * D ^ 2 ≤ D ^ 3 :=
    (mul_le_mul_of_nonneg_right hq1 (sq_nonneg D)).trans (by simpa only [one_mul] using hD23)
  have hP : 0 ≤ P := (wallEnvelope_bounds u |b| (u - v) T hT).1.le
  have hd := completion_difference_envelope_bound u v T b hu hv hT hb hzero
  have hc := compensation_envelope_bound u v T b hu hv hT hb
  have ha : |localRemainder u v T b| ≤ 2 * P + 8 * q * D ^ 2 * P := by
    have hh := abs_add_le (completion (u - b) v (T - b ^ 2) - completion u v T)
      (-((b - b ^ 2 * (u - v) / T) * (-slopeTime u v T)))
    rw [abs_neg] at hh
    change |completion (u - b) v (T - b ^ 2) - completion u v T| ≤ 2 * P at hd
    change |(b - b ^ 2 * (u - v) / T) * (-slopeTime u v T)| ≤ 8 * q * D ^ 2 * P at hc
    simpa only [localRemainder, sub_eq_add_neg] using hh.trans (add_le_add hd hc)
  have hnorm : 2 + 8 * q * D ^ 2 ≤ 10 * D ^ 3 := by nlinarith only [hqD, hD3]
  calc
    _ ≤ 2 * P + 8 * q * D ^ 2 * P := ha
    _ = (2 + 8 * q * D ^ 2) * P := by ring
    _ ≤ 10 * D ^ 3 * P := mul_le_mul_of_nonneg_right hnorm hP
    _ ≤ 40 * q ^ 3 * D ^ 3 * P := by
      have hh := mul_le_mul_of_nonneg_right hqpay (by positivity : 0 ≤ 10 * D ^ 3 * P)
      convert hh using 1 <;> ring
    _ ≤ 8000100 * q ^ 3 * D ^ 3 * P := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (by norm_num : (40 : ℝ) ≤ 8000100) (pow_nonneg hq0 3)) (pow_nonneg hD0 3)) hP
    _ = _ := rfl

theorem retained_envelope_bound (u v T b : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hT : 0 < T) (hb : b ^ 2 ≤ T)
    (hzero : T - b ^ 2 = 0 → u - b = v) :
    |retainedRemainder u v T b| ≤
      8000100 * (|b| / Real.sqrt T) ^ 3 * (1 + |u - v| / Real.sqrt T) ^ 3 *
        wallEnvelope u |b| (u - v) T := by
  unfold retainedRemainder
  by_cases hs : b ^ 2 ≤ T / 2
  · by_cases hc : u - b ≤ 0
    · rw [if_pos ⟨hs, hc⟩]
      have hub : u ≤ |b| := le_trans (by linarith only [hc]) (le_abs_self b)
      have husq : u ^ 2 ≤ b ^ 2 := by nlinarith only [hub, hu, sq_abs b]
      have hsmall : u ^ 2 ≤ T / 2 := husq.trans hs
      have hh := local_small_envelope_bound u v T u hu hv hT hsmall (by norm_num)
      rw [crossing_wallEnvelope_eq_one u u (u - v) T hu (le_abs_self u), abs_of_pos hu] at hh
      rw [crossing_wallEnvelope_eq_one u b (u - v) T hu hub]
      have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
      have hratio := (div_le_div_iff_of_pos_right hsqrt).2 hub
      have hp := pow_le_pow_left₀ (by positivity : 0 ≤ u / Real.sqrt T) hratio 3
      have ht := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp
        (by norm_num : (0 : ℝ) ≤ 8000100))
        (by positivity : 0 ≤ (1 + |u - v| / Real.sqrt T) ^ 3)
      simpa only [mul_one] using hh.trans (by simpa only [mul_one] using ht)
    · rw [if_neg (by intro h; exact hc h.2)]
      exact local_small_envelope_bound u v T b hu hv hT hs (by linarith only [hc])
  · rw [if_neg (by intro h; exact hs h.1)]
    exact local_large_envelope_bound u v T b hu hv hT hb (lt_of_not_ge hs) hzero

end Shao.C2.HalfLineGaussianStep
