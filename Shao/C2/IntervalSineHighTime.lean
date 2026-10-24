import Shao.C2.IntervalSineSeries

noncomputable section
namespace Shao.C2.IntervalSineHighTime
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalSineTerms Shao.C2.IntervalSineSeries Shao.C2.IntervalSpectralGaussian

def sineDerivativeConstant (j l : ℕ) : ℝ :=
  (Real.pi / 2) ^ j * (Real.pi ^ 2 / 8) ^ l *
    spectralConstant (Real.pi ^ 2 / 8) (j + 2 * l)

theorem sineDerivativeConstant_nonneg (j l : ℕ) : 0 ≤ sineDerivativeConstant j l := by
  have hC := spectralConstant_nonneg (Real.pi ^ 2 / 8) (j + 2 * l) (by positivity)
  dsimp only [sineDerivativeConstant]
  positivity

theorem sine_scaling_identity (j l : ℕ) (a T : ℝ) (ha : 0 < a) (hT : 0 < T) :
    ((1 / a) * (Real.pi / (2 * a)) ^ j * (Real.pi ^ 2 / (8 * a ^ 2)) ^ l) /
        (Real.sqrt (T / a ^ 2)) ^ (j + 2 * l + 1) =
      ((Real.pi / 2) ^ j * (Real.pi ^ 2 / 8) ^ l) *
        (1 / Real.sqrt T) ^ (j + 2 * l + 1) := by
  rw [Real.sqrt_div hT.le, Real.sqrt_sq ha.le]
  simp only [div_pow, mul_pow, pow_add, pow_mul]
  field_simp [ne_of_gt ha, ne_of_gt (Real.sqrt_pos.mpr hT)] <;> ring

theorem mixedSineSeries_highTime_bound (j l : ℕ) (a z T y : ℝ)
    (ha : 0 < a) (hT : 0 < T) (hlarge : a ^ 2 ≤ T) :
    ‖mixedSineSeries j l a z T y‖ ≤
      sineDerivativeConstant j l * (1 / Real.sqrt T) ^ (j + 2 * l + 1) := by
  let A := (1 / a) * (Real.pi / (2 * a)) ^ j * (Real.pi ^ 2 / (8 * a ^ 2)) ^ l
  let C := spectralConstant (Real.pi ^ 2 / 8) (j + 2 * l)
  let x := T / a ^ 2
  have hx : 1 ≤ x := (le_div_iff₀ (sq_pos_of_pos ha)).mpr (by simpa only [one_mul] using hlarge)
  have hxsqrt : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by dsimp only [x]; positivity)
  have hs := weightedGaussian_scaled_bound (Real.pi ^ 2 / 8) x (j + 2 * l) (by positivity) hx
  have hsum : (∑' n : ℕ, weightedGaussian (Real.pi ^ 2 / 8) (j + 2 * l) x n) ≤
      C / (Real.sqrt x) ^ (j + 2 * l + 1) := by
    apply (le_div_iff₀ (pow_pos hxsqrt _)).mpr
    simpa only [C, mul_comm] using hs
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  calc
    ‖mixedSineSeries j l a z T y‖ ≤
        A * (∑' n : ℕ, weightedGaussian (Real.pi ^ 2 / 8) (j + 2 * l) x n) :=
      mixedSineSeries_weighted_bound j l a z T y ha hT
    _ ≤ A * (C / (Real.sqrt x) ^ (j + 2 * l + 1)) := mul_le_mul_of_nonneg_left hsum hA
    _ = (A / (Real.sqrt x) ^ (j + 2 * l + 1)) * C := by ring
    _ = _ := by
      dsimp only [A, x]
      rw [sine_scaling_identity j l a T ha hT]
      dsimp only [C, sineDerivativeConstant]
      ring

theorem sineSeries_mixed_highTime_bound (j l : ℕ) (a z T y : ℝ)
    (ha : 0 < a) (hT : 0 < T) (hlarge : a ^ 2 ≤ T) :
    ‖iteratedDeriv l (fun S => iteratedDeriv j (mixedSineSeries 0 0 a z S) y) T‖ ≤
      sineDerivativeConstant j l * (1 / Real.sqrt T) ^ (j + 2 * l + 1) := by
  rw [sineSeries_mixed_iteratedDeriv j l a z T y ha hT]
  exact mixedSineSeries_highTime_bound j l a z T y ha hT hlarge

theorem sineSeries_commuted_highTime_bound (j l : ℕ) (a z T y : ℝ)
    (ha : 0 < a) (hT : 0 < T) (hlarge : a ^ 2 ≤ T) :
    ‖iteratedDeriv j (fun w => iteratedDeriv l (fun S => mixedSineSeries 0 0 a z S w) T) y‖ ≤
      sineDerivativeConstant j l * (1 / Real.sqrt T) ^ (j + 2 * l + 1) := by
  rw [sineSeries_mixed_commutation j l a z T y ha hT]
  exact sineSeries_mixed_highTime_bound j l a z T y ha hT hlarge

end Shao.C2.IntervalSineHighTime
