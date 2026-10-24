import Shao.C2.IntervalSineNormalizedDerivatives

noncomputable section
namespace Shao.C2.IntervalSineNormalizedHighTime
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalReciprocalDerivatives Shao.C2.IntervalReciprocalHighTime
open Shao.C2.IntervalSineSeries Shao.C2.IntervalSineHighTime
open Shao.C2.IntervalSineNormalizedDerivatives

def normalizedDerivativeConstant (j l : ℕ) : ℝ :=
  reciprocalHighTimeConstant *
    (∑ i ∈ Finset.range (j + 1), ∑ k ∈ Finset.range (l + 1),
      (Nat.choose j i : ℝ) * (Nat.choose l k : ℝ) * sineDerivativeConstant (j - i) (l - k))

theorem normalizedDerivativeConstant_nonneg (j l : ℕ) :
    0 ≤ normalizedDerivativeConstant j l := by
  dsimp only [normalizedDerivativeConstant]
  apply mul_nonneg (by dsimp only [reciprocalHighTimeConstant]; positivity)
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (by positivity) (sineDerivativeConstant_nonneg (j - i) (l - k))

theorem reciprocal_sine_product_highTime_bound (i k p q : ℕ) (a z T y : ℝ)
    (hik : i + k ≤ 3) (ha : 0 < a) (hT : 0 < T) (hlarge : a ^ 2 ≤ T)
    (hy : |y| ≤ a) (hz : |z| ≤ a) :
    ‖reciprocalMixedFamily i k z T y * mixedSineSeries p q a z T y‖ ≤
      (reciprocalHighTimeConstant * sineDerivativeConstant p q) *
        (1 / Real.sqrt T) ^ (i + p + 2 * (k + q)) := by
  have hR : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hd : |z - y| ≤ 2 * Real.sqrt T :=
    (div_le_iff₀ hR).mp
      (Shao.C2.IntervalHighTimeProfiles.highTime_drift_bound a y z T ha hy hz hT hlarge).1
  have hG := reciprocalMixedFamily_drift_bound i k z T y hik hT hd
  have hS := mixedSineSeries_highTime_bound p q a z T y ha hT hlarge
  have hGB : 0 ≤ reciprocalHighTimeConstant * Real.sqrt T *
      (1 / Real.sqrt T) ^ (i + 2 * k) := by
    dsimp only [reciprocalHighTimeConstant]
    positivity
  have he : (i + 2 * k) + (p + 2 * q + 1) = (i + p + 2 * (k + q)) + 1 := by omega
  have hp : (1 / Real.sqrt T) ^ (i + 2 * k) *
      (1 / Real.sqrt T) ^ (p + 2 * q + 1) =
        (1 / Real.sqrt T) ^ ((i + p + 2 * (k + q)) + 1) := by rw [← pow_add, he]
  rw [norm_mul]
  calc
    _ ≤ (reciprocalHighTimeConstant * Real.sqrt T * (1 / Real.sqrt T) ^ (i + 2 * k)) *
        (sineDerivativeConstant p q * (1 / Real.sqrt T) ^ (p + 2 * q + 1)) :=
      mul_le_mul hG hS (norm_nonneg _) hGB
    _ = (reciprocalHighTimeConstant * sineDerivativeConstant p q) *
        (Real.sqrt T * ((1 / Real.sqrt T) ^ (i + 2 * k) *
          (1 / Real.sqrt T) ^ (p + 2 * q + 1))) := by ring
    _ = (reciprocalHighTimeConstant * sineDerivativeConstant p q) *
        (Real.sqrt T * (1 / Real.sqrt T) ^ ((i + p + 2 * (k + q)) + 1)) := by rw [hp]
    _ = (reciprocalHighTimeConstant * sineDerivativeConstant p q) *
        ((Real.sqrt T * (1 / Real.sqrt T)) * (1 / Real.sqrt T) ^ (i + p + 2 * (k + q))) := by
      rw [pow_succ]
      ring
    _ = _ := by simp only [one_div, mul_inv_cancel₀ (ne_of_gt hR), one_mul]

theorem normalizedMixedFamily_highTime_bound (j l : ℕ) (a z T y : ℝ)
    (hjl : j + l ≤ 3) (ha : 0 < a) (hT : 0 < T) (hlarge : a ^ 2 ≤ T)
    (hy : |y| ≤ a) (hz : |z| ≤ a) :
    ‖normalizedMixedFamily j l a z T y‖ ≤
      normalizedDerivativeConstant j l * (1 / Real.sqrt T) ^ (j + 2 * l) := by
  rw [normalizedMixedFamily]
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1),
        ‖∑ k ∈ Finset.range (l + 1), (Nat.choose j i : ℝ) * (Nat.choose l k : ℝ) *
          reciprocalMixedFamily i k z T y * mixedSineSeries (j - i) (l - k) a z T y‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (j + 1), ∑ k ∈ Finset.range (l + 1),
        ‖(Nat.choose j i : ℝ) * (Nat.choose l k : ℝ) *
          reciprocalMixedFamily i k z T y * mixedSineSeries (j - i) (l - k) a z T y‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (j + 1), ∑ k ∈ Finset.range (l + 1),
        (Nat.choose j i : ℝ) * (Nat.choose l k : ℝ) *
          (reciprocalHighTimeConstant * sineDerivativeConstant (j - i) (l - k)) *
            (1 / Real.sqrt T) ^ (j + 2 * l) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro k hk
      have hi' : i ≤ j := by have h := Finset.mem_range.mp hi; omega
      have hk' : k ≤ l := by have h := Finset.mem_range.mp hk; omega
      have hik : i + k ≤ 3 := by omega
      have he : i + (j - i) + 2 * (k + (l - k)) = j + 2 * l := by omega
      have hp := reciprocal_sine_product_highTime_bound i k (j - i) (l - k)
        a z T y hik ha hT hlarge hy hz
      rw [he] at hp
      let c : ℝ := (Nat.choose j i : ℝ) * (Nat.choose l k : ℝ)
      have hc : 0 ≤ c := by dsimp only [c]; positivity
      change ‖c * reciprocalMixedFamily i k z T y * mixedSineSeries (j - i) (l - k) a z T y‖ ≤
        c * (reciprocalHighTimeConstant * sineDerivativeConstant (j - i) (l - k)) *
          (1 / Real.sqrt T) ^ (j + 2 * l)
      calc
        _ = c * ‖reciprocalMixedFamily i k z T y * mixedSineSeries (j - i) (l - k) a z T y‖ := by
          rw [mul_assoc, norm_mul, Real.norm_eq_abs, abs_of_nonneg hc]
        _ ≤ c * ((reciprocalHighTimeConstant * sineDerivativeConstant (j - i) (l - k)) *
            (1 / Real.sqrt T) ^ (j + 2 * l)) := mul_le_mul_of_nonneg_left hp hc
        _ = _ := by ring
    _ = _ := by
      dsimp only [normalizedDerivativeConstant]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      ring

theorem normalizedSineCandidate_mixed_highTime_bound (j l : ℕ) (a z T y : ℝ)
    (hjl : j + l ≤ 3) (ha : 0 < a) (hT : 0 < T) (hlarge : a ^ 2 ≤ T)
    (hy : |y| ≤ a) (hz : |z| ≤ a) :
    ‖iteratedDeriv l (fun S => iteratedDeriv j (normalizedSineCandidate a z S) y) T‖ ≤
      normalizedDerivativeConstant j l * (1 / Real.sqrt T) ^ (j + 2 * l) := by
  rw [normalizedSineCandidate_mixed_iteratedDeriv j l a z T y hjl ha hT]
  exact normalizedMixedFamily_highTime_bound j l a z T y hjl ha hT hlarge hy hz

theorem normalizedSineCandidate_commuted_highTime_bound (j l : ℕ) (a z T y : ℝ)
    (hjl : j + l ≤ 3) (ha : 0 < a) (hT : 0 < T) (hlarge : a ^ 2 ≤ T)
    (hy : |y| ≤ a) (hz : |z| ≤ a) :
    ‖iteratedDeriv j (fun w => iteratedDeriv l (fun S => normalizedSineCandidate a z S w) T) y‖ ≤
      normalizedDerivativeConstant j l * (1 / Real.sqrt T) ^ (j + 2 * l) := by
  rw [normalizedSineCandidate_mixed_commutation j l a z T y hjl ha hT]
  exact normalizedSineCandidate_mixed_highTime_bound j l a z T y hjl ha hT hlarge hy hz

end Shao.C2.IntervalSineNormalizedHighTime
