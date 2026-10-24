import Shao.C2.IntervalSineNormalizedHighTime

noncomputable section
namespace Shao.C2.IntervalSineHighTimeProfiles
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.CompletionFirstProfile Shao.C2.IntervalHighTimeProfiles
open Shao.C2.IntervalSineNormalizedDerivatives Shao.C2.IntervalSineNormalizedHighTime

def normalizedProfileConstant (j l : ℕ) : ℝ :=
  (Real.exp 4 / 2) * (normalizedDerivativeConstant j l + 1)

theorem normalizedProfileConstant_nonneg (j l : ℕ) :
    0 ≤ normalizedProfileConstant j l := by
  have hC := normalizedDerivativeConstant_nonneg j l
  dsimp only [normalizedProfileConstant]
  positivity

theorem normalizedSineCandidate_sub_one_mixed_iteratedDeriv (j l : ℕ) (a z T y : ℝ)
    (hjl : j + l ≤ 3) (hpos : 0 < j + l) (ha : 0 < a) (hT : 0 < T) :
    iteratedDeriv l (fun S => iteratedDeriv j (fun w => normalizedSineCandidate a z S w - 1) y) T =
      normalizedMixedFamily j l a z T y := by
  have hshift (n : ℕ) (f : ℝ → ℝ) (x : ℝ) (hn : 0 < n) :
      iteratedDeriv n (fun w => f w - 1) x = iteratedDeriv n f x := by
    have heq : (fun w => f w - 1) = (fun w => (-1 : ℝ) + f w) := by funext w; ring
    rw [heq]
    exact iteratedDeriv_const_add hn (-1 : ℝ)
  by_cases hj : j = 0
  · subst j
    have hl : 0 < l := by omega
    change iteratedDeriv l (fun S => normalizedSineCandidate a z S y - 1) T = _
    rw [hshift l (fun S => normalizedSineCandidate a z S y) T hl]
    simpa only [iteratedDeriv_zero] using
      normalizedSineCandidate_mixed_iteratedDeriv 0 l a z T y hjl ha hT
  · have hj' : 0 < j := by omega
    have heq : (fun S => iteratedDeriv j (fun w => normalizedSineCandidate a z S w - 1) y) =
        (fun S => iteratedDeriv j (normalizedSineCandidate a z S) y) := by
      funext S
      exact hshift j (normalizedSineCandidate a z S) y hj'
    rw [heq]
    exact normalizedSineCandidate_mixed_iteratedDeriv j l a z T y hjl ha hT

theorem normalizedSineCandidate_sub_one_mixed_commutation (j l : ℕ) (a z T y : ℝ)
    (hjl : j + l ≤ 3) (ha : 0 < a) (hT : 0 < T) :
    iteratedDeriv j (fun w => iteratedDeriv l (fun S => normalizedSineCandidate a z S w - 1) T) y =
      iteratedDeriv l (fun S => iteratedDeriv j (fun w => normalizedSineCandidate a z S w - 1) y) T := by
  have hshift (n : ℕ) (f : ℝ → ℝ) (x : ℝ) (hn : 0 < n) :
      iteratedDeriv n (fun w => f w - 1) x = iteratedDeriv n f x := by
    have heq : (fun w => f w - 1) = (fun w => (-1 : ℝ) + f w) := by funext w; ring
    rw [heq]
    exact iteratedDeriv_const_add hn (-1 : ℝ)
  cases j with
  | zero => simp only [iteratedDeriv_zero]
  | succ j =>
    cases l with
    | zero => simp only [iteratedDeriv_zero]
    | succ l =>
      have heqT : (fun w => iteratedDeriv (l + 1) (fun S => normalizedSineCandidate a z S w - 1) T) =
          (fun w => iteratedDeriv (l + 1) (fun S => normalizedSineCandidate a z S w) T) := by
        funext w
        exact hshift (l + 1) (fun S => normalizedSineCandidate a z S w) T (by omega)
      have heqY : (fun S => iteratedDeriv (j + 1) (fun w => normalizedSineCandidate a z S w - 1) y) =
          (fun S => iteratedDeriv (j + 1) (normalizedSineCandidate a z S) y) := by
        funext S
        exact hshift (j + 1) (normalizedSineCandidate a z S) y (by omega)
      rw [heqT, heqY]
      exact normalizedSineCandidate_mixed_commutation (j + 1) (l + 1) a z T y hjl ha hT

theorem normalizedSineCandidate_sub_one_highTime_norm_bound (j l : ℕ) (a z T y : ℝ)
    (hjl : j + l ≤ 3) (ha : 0 < a) (hT : 0 < T) (hlarge : a ^ 2 ≤ T)
    (hy : |y| ≤ a) (hz : |z| ≤ a) :
    ‖iteratedDeriv l (fun S => iteratedDeriv j (fun w => normalizedSineCandidate a z S w - 1) y) T‖ ≤
      (normalizedDerivativeConstant j l + 1) * (1 / Real.sqrt T) ^ (j + 2 * l) := by
  by_cases hzero : j + l = 0
  · have hj : j = 0 := by omega
    have hl : l = 0 := by omega
    subst j
    subst l
    have hN : ‖normalizedSineCandidate a z T y‖ ≤ normalizedDerivativeConstant 0 0 := by
      simpa only [iteratedDeriv_zero, Nat.zero_add, Nat.mul_zero, pow_zero, mul_one] using
        normalizedSineCandidate_mixed_highTime_bound 0 0 a z T y (by omega) ha hT hlarge hy hz
    have hb : ‖normalizedSineCandidate a z T y - 1‖ ≤ normalizedDerivativeConstant 0 0 + 1 := by
      calc
        _ ≤ ‖normalizedSineCandidate a z T y‖ + ‖(1 : ℝ)‖ := norm_sub_le _ _
        _ ≤ _ := by simpa only [norm_one] using add_le_add hN (le_refl (1 : ℝ))
    simpa only [iteratedDeriv_zero, Nat.zero_add, Nat.mul_zero, pow_zero, mul_one] using hb
  · have hpos : 0 < j + l := by omega
    rw [normalizedSineCandidate_sub_one_mixed_iteratedDeriv j l a z T y hjl hpos ha hT]
    calc
      _ ≤ normalizedDerivativeConstant j l * (1 / Real.sqrt T) ^ (j + 2 * l) :=
        normalizedMixedFamily_highTime_bound j l a z T y hjl ha hT hlarge hy hz
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

theorem normalizedSineCandidate_sub_one_highTime_profile (j l : ℕ) (a z T y : ℝ)
    (hjl : j + l ≤ 3) (ha : 0 < a) (hT : 0 < T) (hlarge : a ^ 2 ≤ T)
    (hy : |y| ≤ a) (hz : |z| ≤ a) :
    ‖iteratedDeriv l (fun S => iteratedDeriv j (fun w => normalizedSineCandidate a z S w - 1) y) T‖ ≤
      normalizedProfileConstant j l * (1 / Real.sqrt T) ^ (j + 2 * l) *
        (1 + |z - y| / Real.sqrt T) ^ j * intervalProfile a y T z := by
  let R := iteratedDeriv l (fun S => iteratedDeriv j (fun w => normalizedSineCandidate a z S w - 1) y) T
  let B := (normalizedDerivativeConstant j l + 1) * (1 / Real.sqrt T) ^ (j + 2 * l)
  have hC := normalizedDerivativeConstant_nonneg j l
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hR : |R| ≤ B := by
    simpa only [R, B, Real.norm_eq_abs] using
      normalizedSineCandidate_sub_one_highTime_norm_bound j l a z T y hjl ha hT hlarge hy hz
  have hP : |R| ≤ (normalizedProfileConstant j l * (1 / Real.sqrt T) ^ (j + 2 * l)) *
      intervalProfile a y T z := by
    calc
      _ ≤ (Real.exp 4 / 2 * B) * intervalProfile a y T z :=
        highTime_bound_to_profile a y z T R B ha hy hz hT hlarge hB hR
      _ = _ := by dsimp only [B, normalizedProfileConstant]; ring
  have hD : 1 ≤ 1 + |z - y| / Real.sqrt T := by
    have hq := div_nonneg (abs_nonneg (z - y)) (Real.sqrt_nonneg T)
    linarith only [hq]
  have hDp : 1 ≤ (1 + |z - y| / Real.sqrt T) ^ j := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hD j
  have hCP : 0 ≤ normalizedProfileConstant j l * (1 / Real.sqrt T) ^ (j + 2 * l) :=
    mul_nonneg (normalizedProfileConstant_nonneg j l) (by positivity)
  have hP0 : 0 ≤ intervalProfile a y T z := by
    dsimp only [intervalProfile, upperProfile, lowerProfile]
    positivity
  rw [Real.norm_eq_abs]
  change |R| ≤ _
  calc
    _ ≤ (normalizedProfileConstant j l * (1 / Real.sqrt T) ^ (j + 2 * l)) * intervalProfile a y T z := hP
    _ ≤ _ := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDp hCP) hP0

theorem normalizedSineCandidate_sub_one_commuted_highTime_profile (j l : ℕ) (a z T y : ℝ)
    (hjl : j + l ≤ 3) (ha : 0 < a) (hT : 0 < T) (hlarge : a ^ 2 ≤ T)
    (hy : |y| ≤ a) (hz : |z| ≤ a) :
    ‖iteratedDeriv j (fun w => iteratedDeriv l (fun S => normalizedSineCandidate a z S w - 1) T) y‖ ≤
      normalizedProfileConstant j l * (1 / Real.sqrt T) ^ (j + 2 * l) *
        (1 + |z - y| / Real.sqrt T) ^ j * intervalProfile a y T z := by
  rw [normalizedSineCandidate_sub_one_mixed_commutation j l a z T y hjl ha hT]
  exact normalizedSineCandidate_sub_one_highTime_profile j l a z T y hjl ha hT hlarge hy hz

end Shao.C2.IntervalSineHighTimeProfiles
