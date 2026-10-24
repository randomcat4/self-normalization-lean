import Shao.C2.IntervalGaussianLargeStep

noncomputable section
namespace Shao.C2.IntervalGaussianLocal
open MeasureTheory
open Shao.C2.BridgeDomination Shao.C2.SourceIntervalCompletion
open Shao.C2.ActualIntervalProjection Shao.C2.IntervalGaussianLargeStep
open Shao.C2.HalfLineTaylorSegment Shao.C2.GaussianWallEnvelope
open Shao.C2.HalfLineReflectionFormula

def intervalIncrementProfile (a y T z b : ℝ) : ℝ :=
  incrementProfile (a - y) (a - z) T b + incrementProfile (a + y) (a + z) T b

def retainedRemainder (ν : Measure BridgeNoise) (a y T z b : ℝ) : ℝ :=
  if b ^ 2 ≤ T / 2 ∧ ¬ |y + b| < a then
    if a ≤ y + b then sourceRemainder ν a y T z (a - y)
    else sourceRemainder ν a y T z (-a - y)
  else sourceRemainder ν a y T z b

def negativeOvershoot (ν : Measure BridgeNoise) (a y T z b : ℝ) : ℝ :=
  if b ^ 2 ≤ T / 2 ∧ ¬ |y + b| < a then
    if a ≤ y + b then max (-upperOvershoot ν a y T z b) 0
    else max (-lowerOvershoot ν a y T z b) 0
  else 0

theorem intervalIncrementProfile_bounds (a y T z b : ℝ) (hy : |y| < a)
    (hz : |z| < a) (hT : 0 < T) :
    0 ≤ intervalIncrementProfile a y T z b ∧ intervalIncrementProfile a y T z b ≤ 2 := by
  have hp (u v : ℝ) (hv : 0 ≤ v) :
      0 ≤ incrementProfile u v T b ∧ incrementProfile u v T b ≤ 1 := by
    dsimp only [incrementProfile]
    constructor
    · exact (Real.exp_pos _).le
    · apply Real.exp_le_one_iff.2
      apply div_nonpos_of_nonpos_of_nonneg _ hT.le
      exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (le_max_right (u - |b|) 0)) hv
  have hu := hp (a - y) (a - z) (sub_pos.mpr (abs_lt.mp hz).2).le
  have hl := hp (a + y) (a + z) (by linarith only [(abs_lt.mp hz).1])
  dsimp only [intervalIncrementProfile]
  constructor <;> linarith only [hu.1, hu.2, hl.1, hl.2]

theorem intervalIncrementProfile_le_envelope (a y T z b : ℝ) (hy : |y| < a)
    (hz : |z| < a) (hT : 0 < T) :
    intervalIncrementProfile a y T z b ≤ intervalEnvelope a y T z b := by
  have hu : incrementProfile (a - y) (a - z) T b ≤ wallEnvelope (a - y) |b| (z - y) T := by
    convert increment_profile_le_wallEnvelope (a - y) (z - y) T b
      (sub_pos.mpr (abs_lt.mp hy).2) (by linarith only [(abs_lt.mp hz).2]) hT using 1 <;> ring
  have hl : incrementProfile (a + y) (a + z) T b ≤ wallEnvelope (a + y) |b| (y - z) T := by
    convert increment_profile_le_wallEnvelope (a + y) (y - z) T b
      (by linarith only [(abs_lt.mp hy).1]) (by linarith only [(abs_lt.mp hz).1]) hT using 1 <;> ring
  exact add_le_add hu hl

theorem source_projected_budget_of_small_taylor (ν : Measure BridgeNoise)
    (a y T z β C : ℝ) (hy : |y| < a) (hz : |z| < a) (hT : 0 < T) (hC : 0 ≤ C)
    (hsmall : β ^ 2 ≤ T / 2) (hnew : |y + β| ≤ a)
    (hTaylor : |sourceRemainder ν a y T z β| ≤
      C * |β| ^ 3 * (1 / Real.sqrt T) ^ 3 * (1 + |z - y| / Real.sqrt T) ^ 3 *
        intervalIncrementProfile a y T z β) :
    |sourceRemainder ν a y T z β| ≤
      (2 * C * (1 / Real.sqrt T) ^ 3 * (1 + |z - y| / Real.sqrt T) ^ 3) * |β| ^ 3 := by
  have hp := (intervalIncrementProfile_bounds a y T z β hy hz hT).2
  have hh := mul_le_mul_of_nonneg_left hp (by positivity :
    0 ≤ C * |β| ^ 3 * (1 / Real.sqrt T) ^ 3 * (1 + |z - y| / Real.sqrt T) ^ 3)
  convert hTaylor.trans hh using 1 <;> ring

theorem actual_interval_local_gaussian_bound (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (a y T z b C : ℝ) (ha : 0 < a) (hy : |y| < a) (hz : |z| < a)
    (hT : 0 < T) (hb : b ^ 2 ≤ T) (hC : 0 ≤ C)
    (hzero : T - b ^ 2 = 0 → y + b = z)
    (hRegular : DifferentiableAt ℝ (fun w => sourceIntervalCompletion ν a w T z) y)
    (hUpper : ∀ S : ℝ, 0 < S → ∀ w : ℝ, w < a →
      upperCompletion ν a w S z = upperReflection a w S z)
    (hLower : ∀ S : ℝ, 0 < S → ∀ w : ℝ, -a < w →
      lowerCompletion ν a w S z = lowerReflection a w S z)
    (hSmall : ∀ β : ℝ, β ^ 2 ≤ T / 2 → |y + β| ≤ a →
      |sourceRemainder ν a y T z β| ≤
        C * |β| ^ 3 * (1 / Real.sqrt T) ^ 3 * (1 + |z - y| / Real.sqrt T) ^ 3 *
          intervalIncrementProfile a y T z β) :
    |retainedRemainder ν a y T z b| + negativeOvershoot ν a y T z b ≤
      (2 * C + 40) * (|b| / Real.sqrt T) ^ 3 * (1 + |z - y| / Real.sqrt T) ^ 3 *
        intervalEnvelope a y T z b := by
  let D := 1 + |z - y| / Real.sqrt T
  let P := intervalEnvelope a y T z b
  let A := (|b| / Real.sqrt T) ^ 3 * D ^ 3 * P
  let K := 2 * C * (1 / Real.sqrt T) ^ 3 * D ^ 3
  have hP0 : 0 ≤ P := intervalEnvelope_nonneg a y T z b hT
  have hA0 : 0 ≤ A := by dsimp only [A, D]; positivity
  have hK0 : 0 ≤ K := by dsimp only [K, D]; positivity
  have hpay (hP1 : 1 ≤ P) : K * |b| ^ 3 ≤ (2 * C + 40) * A := by
    calc
      _ = (2 * C) * ((|b| / Real.sqrt T) ^ 3 * D ^ 3) := by dsimp only [K]; ring
      _ ≤ (2 * C) * ((|b| / Real.sqrt T) ^ 3 * D ^ 3) * P := by
        have hh := mul_le_mul_of_nonneg_left hP1 (by positivity :
          0 ≤ (2 * C) * ((|b| / Real.sqrt T) ^ 3 * D ^ 3))
        simpa only [mul_one] using hh
      _ = 2 * C * A := by dsimp only [A]; ring
      _ ≤ (2 * C + 40) * A := by nlinarith only [hA0]
  suffices hh : |retainedRemainder ν a y T z b| + negativeOvershoot ν a y T z b ≤
      (2 * C + 40) * A by
    convert hh using 1 <;> dsimp only [A, D, P] <;> ring
  by_cases hs : b ^ 2 ≤ T / 2
  · by_cases hint : |y + b| < a
    · have hg : ¬ (b ^ 2 ≤ T / 2 ∧ ¬ |y + b| < a) := by intro h; exact h.2 hint
      simp only [retainedRemainder, negativeOvershoot, if_neg hg, add_zero]
      have ht := hSmall b hs hint.le
      have hp := intervalIncrementProfile_le_envelope a y T z b hy hz hT
      have hm := mul_le_mul_of_nonneg_left hp (by positivity :
        0 ≤ C * |b| ^ 3 * (1 / Real.sqrt T) ^ 3 * (1 + |z - y| / Real.sqrt T) ^ 3)
      have hh : |sourceRemainder ν a y T z b| ≤ C * A := by
        convert ht.trans hm using 1 <;> dsimp only [A, D, P] <;> ring
      exact hh.trans (mul_le_mul_of_nonneg_right (by linarith only [hC]) hA0)
    · have hg : b ^ 2 ≤ T / 2 ∧ ¬ |y + b| < a := ⟨hs, hint⟩
      have hP1 : 1 ≤ P := intervalEnvelope_crossing a y T z b hy hT hint
      by_cases hup : a ≤ y + b
      · simp only [retainedRemainder, negativeOvershoot, if_pos hg, if_pos hup]
        have hu : 0 < a - y := sub_pos.mpr (abs_lt.mp hy).2
        have hub : a - y ≤ b := by linarith only [hup]
        have hpsq : (a - y) ^ 2 ≤ T / 2 :=
          (pow_le_pow_left₀ hu.le hub 2).trans hs
        have hnew : |y + (a - y)| ≤ a := by
          rw [show y + (a - y) = a by ring, abs_of_pos ha]
        have hp := source_projected_budget_of_small_taylor ν a y T z (a - y) C
          hy hz hT hC hpsq hnew (hSmall (a - y) hpsq hnew)
        change |sourceRemainder ν a y T z (a - y)| ≤ K * |a - y| ^ 3 at hp
        have hh := source_upper_projection_negative_budget ν a y T z b K ha hy hz hT hs hup hK0 hRegular hp
        exact (hh.1.trans hh.2).trans (hpay hP1)
      · have hlo : y + b ≤ -a := by
          by_contra h
          apply hint
          exact abs_lt.mpr ⟨by linarith only [h], lt_of_not_ge hup⟩
        simp only [retainedRemainder, negativeOvershoot, if_pos hg, if_neg hup]
        have hu : 0 < a + y := by linarith only [(abs_lt.mp hy).1]
        have hub : a + y ≤ -b := by linarith only [hlo]
        have hpsq : (-a - y) ^ 2 ≤ T / 2 := by
          calc
            _ = (a + y) ^ 2 := by ring
            _ ≤ (-b) ^ 2 := pow_le_pow_left₀ hu.le hub 2
            _ = b ^ 2 := neg_sq b
            _ ≤ _ := hs
        have hnew : |y + (-a - y)| ≤ a := by
          rw [show y + (-a - y) = -a by ring, abs_neg, abs_of_pos ha]
        have hp := source_projected_budget_of_small_taylor ν a y T z (-a - y) C
          hy hz hT hC hpsq hnew (hSmall (-a - y) hpsq hnew)
        change |sourceRemainder ν a y T z (-a - y)| ≤ K * |-a - y| ^ 3 at hp
        have hh := source_lower_projection_negative_budget ν a y T z b K ha hy hz hT hs hlo hK0 hRegular hp
        exact (hh.1.trans hh.2).trans (hpay hP1)
  · have hg : ¬ (b ^ 2 ≤ T / 2 ∧ ¬ |y + b| < a) := by intro h; exact hs h.1
    simp only [retainedRemainder, negativeOvershoot, if_neg hg, add_zero]
    have ht := actual_interval_large_gaussian_bound ν a y T z b hy hz hT hb
      (lt_of_not_ge hs) hzero hRegular hUpper hLower
    have hh : |sourceRemainder ν a y T z b| ≤ 40 * A := by
      convert ht using 1 <;> dsimp only [A, D, P] <;> ring
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith only [hC]) hA0)

end Shao.C2.IntervalGaussianLocal
