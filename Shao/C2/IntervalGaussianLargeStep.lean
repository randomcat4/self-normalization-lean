import Shao.C2.ActualIntervalProjection
import Shao.C2.HalfLineGaussianStep
import Shao.C2.IntervalDerivativeBound

noncomputable section
namespace Shao.C2.IntervalGaussianLargeStep
open MeasureTheory Set
open Shao.C2.BridgeDomination Shao.C2.SourceIntervalCompletion
open Shao.C2.ActualIntervalProjection Shao.C2.GaussianWallEnvelope
open Shao.C2.HalfLineReflectionFormula Shao.C2.HalfLineMixedProfiles
open Shao.C2.IntervalDerivativeBound

def intervalEnvelope (a y T z b : ℝ) : ℝ :=
  wallEnvelope (a - y) |b| (z - y) T + wallEnvelope (a + y) |b| (y - z) T

theorem intervalEnvelope_nonneg (a y T z b : ℝ) (hT : 0 < T) :
    0 ≤ intervalEnvelope a y T z b := by
  exact add_nonneg (wallEnvelope_bounds (a - y) |b| (z - y) T hT).1.le
    (wallEnvelope_bounds (a + y) |b| (y - z) T hT).1.le

theorem intervalEnvelope_crossing (a y T z b : ℝ) (hy : |y| < a) (hT : 0 < T)
    (hcross : ¬ |y + b| < a) : 1 ≤ intervalEnvelope a y T z b := by
  obtain ⟨hyl, hyu⟩ := abs_lt.mp hy
  have hu : 0 < a - y := sub_pos.mpr hyu
  have hl : 0 < a + y := by linarith only [hyl]
  by_cases hup : a ≤ y + b
  · have hc : a - y ≤ |b| := le_trans (by linarith only [hup]) (le_abs_self b)
    dsimp only [intervalEnvelope]
    rw [crossing_wallEnvelope_eq_one (a - y) b (z - y) T hu hc]
    linarith only [(wallEnvelope_bounds (a + y) |b| (y - z) T hT).1.le]
  · have hlo : y + b ≤ -a := by
      by_contra h
      apply hcross
      exact abs_lt.mpr ⟨by linarith only [h], lt_of_not_ge hup⟩
    have hc : a + y ≤ |b| := le_trans (by linarith only [hlo]) (neg_le_abs b)
    have hh := crossing_wallEnvelope_eq_one (a + y) (-b) (y - z) T hl
      (by simpa only [abs_neg] using hc)
    simp only [abs_neg] at hh
    dsimp only [intervalEnvelope]
    rw [hh]
    linarith only [(wallEnvelope_bounds (a - y) |b| (z - y) T hT).1.le]

theorem interval_deficit_le_halfline_deficits (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (a y T z : ℝ) :
    1 - intervalCompletion ν a y T z ≤
      (1 - upperCompletion ν a y T z) + (1 - lowerCompletion ν a y T z) := by
  have hh := measureReal_union_add_inter (μ := ν) (s := strictUpper a y T z)
    (measurableSet_strictLower a y T z)
  change ν.real (strictUpper a y T z ∪ strictLower a y T z) + intervalCompletion ν a y T z =
    upperCompletion ν a y T z + lowerCompletion ν a y T z at hh
  have hu : ν.real (strictUpper a y T z ∪ strictLower a y T z) ≤ 1 := by
    calc
      _ ≤ ν.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := probReal_univ
  linarith only [hh, hu]

theorem initial_deficit_envelope_bound (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (a y T z b : ℝ) (hy : |y| < a) (hz : |z| < a) (hT : 0 < T)
    (hUpper : upperCompletion ν a y T z = upperReflection a y T z)
    (hLower : lowerCompletion ν a y T z = lowerReflection a y T z) :
    1 - sourceIntervalCompletion ν a y T z ≤ intervalEnvelope a y T z b := by
  rw [sourceIntervalCompletion_pos ν a y T z hT]
  obtain ⟨hyl, hyu⟩ := abs_lt.mp hy
  obtain ⟨hzl, hzu⟩ := abs_lt.mp hz
  have hh := interval_deficit_le_halfline_deficits ν a y T z
  rw [hUpper, hLower, upperReflection, lowerReflection] at hh
  have hu1 := Shao.C2.CompletionFirstProfile.reflection_deficit_le_profile
    (a - y) (a - z) T (sub_pos.mpr hyu) (sub_pos.mpr hzu) hT
  have hl1 := Shao.C2.CompletionFirstProfile.reflection_deficit_le_profile
    (a + y) (a + z) T (by linarith only [hyl]) (by linarith only [hzl]) hT
  have hu2 : Real.exp (-(a - y) * (a - z) / T) ≤ wallEnvelope (a - y) |b| (z - y) T := by
    convert initial_profile_le_wallEnvelope (a - y) (z - y) T b
      (sub_pos.mpr hyu) (by linarith only [hzu]) hT using 1 <;> ring
  have hl2 : Real.exp (-(a + y) * (a + z) / T) ≤ wallEnvelope (a + y) |b| (y - z) T := by
    convert initial_profile_le_wallEnvelope (a + y) (y - z) T b
      (by linarith only [hyl]) (by linarith only [hzl]) hT using 1 <;> ring
  dsimp only [intervalEnvelope]
  linarith only [hh, hu1, hl1, hu2, hl2]

theorem future_deficit_envelope_bound (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (a y T z b : ℝ) (hy : |y| < a) (hz : |z| < a) (hT : 0 < T)
    (hb : b ^ 2 ≤ T) (hnew : |y + b| < a)
    (hzero : T - b ^ 2 = 0 → y + b = z)
    (hUpper : ∀ S : ℝ, 0 < S → ∀ w : ℝ, w < a →
      upperCompletion ν a w S z = upperReflection a w S z)
    (hLower : ∀ S : ℝ, 0 < S → ∀ w : ℝ, -a < w →
      lowerCompletion ν a w S z = lowerReflection a w S z) :
    1 - sourceIntervalCompletion ν a (y + b) (T - b ^ 2) z ≤ intervalEnvelope a y T z b := by
  have hE : 0 ≤ T - b ^ 2 := sub_nonneg.mpr hb
  by_cases he : T - b ^ 2 = 0
  · rw [he, hzero he, sourceIntervalCompletion_reachable_zero, if_pos hz, sub_self]
    exact intervalEnvelope_nonneg a y T z b hT
  · have hEp : 0 < T - b ^ 2 := lt_of_le_of_ne hE (Ne.symm he)
    obtain ⟨hyl, hyu⟩ := abs_lt.mp hy
    obtain ⟨hzl, hzu⟩ := abs_lt.mp hz
    obtain ⟨hnl, hnu⟩ := abs_lt.mp hnew
    rw [sourceIntervalCompletion_pos ν a (y + b) (T - b ^ 2) z hEp]
    have hh := interval_deficit_le_halfline_deficits ν a (y + b) (T - b ^ 2) z
    rw [hUpper (T - b ^ 2) hEp (y + b) hnu,
      hLower (T - b ^ 2) hEp (y + b) hnl, upperReflection, lowerReflection] at hh
    have hu : Real.exp (-2 * (a - (y + b)) * (a - z) / (T - b ^ 2)) ≤
        wallEnvelope (a - y) |b| (z - y) T := by
      convert future_reflection_deficit_le_wallEnvelope (a - y) (z - y) T b
        (sub_pos.mpr hyu) (by linarith only [hzu]) hT
        (by linarith only [hnu]) hEp using 1 <;> ring
    have hl : Real.exp (-2 * (a + (y + b)) * (a + z) / (T - b ^ 2)) ≤
        wallEnvelope (a + y) |b| (y - z) T := by
      have hp := future_reflection_deficit_le_wallEnvelope (a + y) (y - z) T (-b)
        (by linarith only [hyl]) (by linarith only [hzl]) hT
        (by linarith only [hnl]) (by simpa only [neg_sq] using hEp)
      simp only [abs_neg, neg_sq] at hp
      convert hp using 1 <;> ring
    dsimp only [intervalEnvelope]
    linarith only [hh, hu, hl]

theorem completion_difference_envelope_bound (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (a y T z b : ℝ) (hy : |y| < a) (hz : |z| < a) (hT : 0 < T) (hb : b ^ 2 ≤ T)
    (hzero : T - b ^ 2 = 0 → y + b = z)
    (hUpper : ∀ S : ℝ, 0 < S → ∀ w : ℝ, w < a →
      upperCompletion ν a w S z = upperReflection a w S z)
    (hLower : ∀ S : ℝ, 0 < S → ∀ w : ℝ, -a < w →
      lowerCompletion ν a w S z = lowerReflection a w S z) :
    |sourceIntervalCompletion ν a (y + b) (T - b ^ 2) z - sourceIntervalCompletion ν a y T z| ≤
      2 * intervalEnvelope a y T z b := by
  have hf := sourceIntervalCompletion_bounds ν a y T z
  have hg := sourceIntervalCompletion_bounds ν a (y + b) (T - b ^ 2) z
  have hP := intervalEnvelope_nonneg a y T z b hT
  by_cases hn : |y + b| < a
  · have hgP := future_deficit_envelope_bound ν a y T z b hy hz hT hb hn hzero hUpper hLower
    have hfP := initial_deficit_envelope_bound ν a y T z b hy hz hT
      (hUpper T hT y (abs_lt.mp hy).2) (hLower T hT y (abs_lt.mp hy).1)
    have hh : |sourceIntervalCompletion ν a (y + b) (T - b ^ 2) z - sourceIntervalCompletion ν a y T z| ≤
        (1 - sourceIntervalCompletion ν a (y + b) (T - b ^ 2) z) +
          (1 - sourceIntervalCompletion ν a y T z) := by
      apply abs_le.mpr
      constructor <;> linarith only [hf.2, hg.2]
    linarith only [hh, hfP, hgP]
  · have hz0 : sourceIntervalCompletion ν a (y + b) (T - b ^ 2) z = 0 :=
      sourceIntervalCompletion_exterior ν a (y + b) (T - b ^ 2) z (by intro h; exact hn h.1)
    have hc := intervalEnvelope_crossing a y T z b hy hT hn
    rw [hz0, zero_sub, abs_neg, abs_of_nonneg hf.1]
    linarith only [hf.2, hc, hP]

theorem compensation_envelope_bound (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (a y T z b : ℝ) (hy : |y| < a) (hz : |z| < a) (hT : 0 < T) (hb : b ^ 2 ≤ T)
    (hRegular : DifferentiableAt ℝ (fun w => sourceIntervalCompletion ν a w T z) y)
    (hUpper : ∀ w : ℝ, w < a → upperCompletion ν a w T z = upperReflection a w T z)
    (hLower : ∀ w : ℝ, -a < w → lowerCompletion ν a w T z = lowerReflection a w T z) :
    |(b - b ^ 2 * (z - y) / T) * deriv (fun w => sourceIntervalCompletion ν a w T z) y| ≤
      8 * (|b| / Real.sqrt T) * (1 + |z - y| / Real.sqrt T) ^ 2 * intervalEnvelope a y T z b := by
  have hfun : (fun w => sourceIntervalCompletion ν a w T z) =
      (fun w => intervalCompletion ν a w T z) :=
    funext (fun w => sourceIntervalCompletion_pos ν a w T z hT)
  rw [hfun] at hRegular ⊢
  obtain ⟨hyl, hyu⟩ := abs_lt.mp hy
  obtain ⟨hzl, hzu⟩ := abs_lt.mp hz
  let U := slopeTime (a - y) (a - z) T
  let L := slopeTime (a + y) (a + z) T
  let G := deriv (fun w => intervalCompletion ν a w T z) y
  let C := b - b ^ 2 * (z - y) / T
  have hU0 : 0 ≤ U := by dsimp only [U, slopeTime]; positivity
  have hL0 : 0 ≤ L := by
    have haz : 0 < a + z := by linarith only [hzl]
    dsimp only [L, slopeTime]
    positivity
  have hu := upperCompletion_hasDerivAt_of_reflection ν a y T z hyu hUpper
  have hl := lowerCompletion_hasDerivAt_of_reflection ν a y T z hyl hLower
  have hdu : deriv (fun w => upperReflection a w T z) y = -U := by
    rw [(upperReflection_hasDerivAt a y T z).deriv]
    dsimp only [U, slopeTime]
    ring
  have hdl : deriv (fun w => lowerReflection a w T z) y = L := by
    rw [(lowerReflection_hasDerivAt a y T z).deriv]
    rfl
  rw [hdu] at hu
  rw [hdl] at hl
  have hdom := signed_derivative_domination_of_hasDerivAt ν a y T z _ _ _
    hu hRegular.hasDerivAt hl
  change -U ≤ G ∧ G ≤ L at hdom
  have hG : |G| ≤ U + L := by
    apply abs_le.mpr
    constructor <;> linarith only [hdom.1, hdom.2, hU0, hL0]
  have hcU := Shao.C2.HalfLineGaussianStep.compensation_envelope_bound
    (a - y) (a - z) T b (sub_pos.mpr hyu) (sub_pos.mpr hzu) hT hb
  rw [show a - y - (a - z) = z - y by ring] at hcU
  have hcL := Shao.C2.HalfLineGaussianStep.compensation_envelope_bound
    (a + y) (a + z) T (-b) (by linarith only [hyl]) (by linarith only [hzl]) hT
      (by simpa only [neg_sq] using hb)
  rw [show a + y - (a + z) = y - z by ring] at hcL
  have heq : (-b - (-b) ^ 2 * (y - z) / T) * (-L) = C * L := by dsimp only [C]; ring
  change |(-b - (-b) ^ 2 * (y - z) / T) * (-L)| ≤ _ at hcL
  rw [heq, abs_neg, abs_sub_comm y z] at hcL
  change |C * G| ≤ _
  calc
    _ = |C| * |G| := abs_mul C G
    _ ≤ |C| * (U + L) := mul_le_mul_of_nonneg_left hG (abs_nonneg C)
    _ = |C * (-U)| + |C * L| := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hU0, abs_of_nonneg hL0]
      ring
    _ ≤ 8 * (|b| / Real.sqrt T) * (1 + |z - y| / Real.sqrt T) ^ 2 *
        wallEnvelope (a - y) |b| (z - y) T +
        8 * (|b| / Real.sqrt T) * (1 + |z - y| / Real.sqrt T) ^ 2 *
          wallEnvelope (a + y) |b| (y - z) T := add_le_add hcU hcL
    _ = _ := by dsimp only [intervalEnvelope]; ring

theorem actual_interval_large_gaussian_bound (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (a y T z b : ℝ) (hy : |y| < a) (hz : |z| < a) (hT : 0 < T)
    (hb : b ^ 2 ≤ T) (hlarge : T / 2 < b ^ 2) (hzero : T - b ^ 2 = 0 → y + b = z)
    (hRegular : DifferentiableAt ℝ (fun w => sourceIntervalCompletion ν a w T z) y)
    (hUpper : ∀ S : ℝ, 0 < S → ∀ w : ℝ, w < a →
      upperCompletion ν a w S z = upperReflection a w S z)
    (hLower : ∀ S : ℝ, 0 < S → ∀ w : ℝ, -a < w →
      lowerCompletion ν a w S z = lowerReflection a w S z) :
    |sourceRemainder ν a y T z b| ≤
      40 * (|b| / Real.sqrt T) ^ 3 * (1 + |z - y| / Real.sqrt T) ^ 3 * intervalEnvelope a y T z b := by
  let s := Real.sqrt T
  let q := |b| / s
  let D := 1 + |z - y| / s
  let P := intervalEnvelope a y T z b
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
    linarith only [div_nonneg (abs_nonneg (z - y)) hs.le]
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hD3 : 1 ≤ D ^ 3 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hD 3
  have hD23 : D ^ 2 ≤ D ^ 3 := pow_le_pow_right₀ hD (by norm_num)
  have hqD : q * D ^ 2 ≤ D ^ 3 :=
    (mul_le_mul_of_nonneg_right hq1 (sq_nonneg D)).trans (by simpa only [one_mul] using hD23)
  have hP : 0 ≤ P := intervalEnvelope_nonneg a y T z b hT
  have hd := completion_difference_envelope_bound ν a y T z b hy hz hT hb hzero hUpper hLower
  have hc := compensation_envelope_bound ν a y T z b hy hz hT hb hRegular (hUpper T hT) (hLower T hT)
  have ha : |sourceRemainder ν a y T z b| ≤ 2 * P + 8 * q * D ^ 2 * P := by
    have hh := abs_add_le (sourceIntervalCompletion ν a (y + b) (T - b ^ 2) z - sourceIntervalCompletion ν a y T z)
      (-((b - b ^ 2 * (z - y) / T) * deriv (fun w => sourceIntervalCompletion ν a w T z) y))
    rw [abs_neg] at hh
    change |sourceIntervalCompletion ν a (y + b) (T - b ^ 2) z - sourceIntervalCompletion ν a y T z| ≤ 2 * P at hd
    change |(b - b ^ 2 * (z - y) / T) * deriv (fun w => sourceIntervalCompletion ν a w T z) y| ≤ 8 * q * D ^ 2 * P at hc
    simpa only [sourceRemainder, sub_eq_add_neg] using hh.trans (add_le_add hd hc)
  have hnorm : 2 + 8 * q * D ^ 2 ≤ 10 * D ^ 3 := by nlinarith only [hqD, hD3]
  calc
    _ ≤ 2 * P + 8 * q * D ^ 2 * P := ha
    _ = (2 + 8 * q * D ^ 2) * P := by ring
    _ ≤ 10 * D ^ 3 * P := mul_le_mul_of_nonneg_right hnorm hP
    _ ≤ 40 * q ^ 3 * D ^ 3 * P := by
      have hh := mul_le_mul_of_nonneg_right hqpay (by positivity : 0 ≤ 10 * D ^ 3 * P)
      convert hh using 1 <;> ring
    _ = _ := rfl

end Shao.C2.IntervalGaussianLargeStep
