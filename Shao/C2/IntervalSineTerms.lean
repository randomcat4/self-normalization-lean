import Shao.C2.IntervalHighTimeProfiles
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section
namespace Shao.C2.IntervalSineTerms
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageSpatialProfiles Shao.C2.IntervalSpectralGaussian

def frequency (a : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) * Real.pi / (2 * a)

def sineTerm (a z T y : ℝ) (n : ℕ) : ℝ :=
  (1 / a) * Real.exp (-(frequency a n) ^ 2 * T / 2) *
    Real.sin (frequency a n * (y + a)) * Real.sin (frequency a n * (z + a))

def mixedSineTerm (j l : ℕ) (a z T y : ℝ) (n : ℕ) : ℝ :=
  iteratedDeriv l (fun S => iteratedDeriv j (fun w => sineTerm a z S w n) y) T

theorem frequency_pos (a : ℝ) (n : ℕ) (ha : 0 < a) : 0 < frequency a n := by
  dsimp only [frequency]
  positivity

theorem affine_sin_iteratedDeriv (j : ℕ) (ω q y : ℝ) :
    iteratedDeriv j (fun w => Real.sin (ω * w + q)) y =
      ω ^ j * Real.sin (ω * y + q + (j : ℝ) * Real.pi / 2) := by
  induction j generalizing y with
  | zero => simp only [iteratedDeriv_zero, pow_zero, Nat.cast_zero, zero_mul, zero_div, add_zero, one_mul]
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have hf : iteratedDeriv j (fun w => Real.sin (ω * w + q)) =
        (fun w => ω ^ j * Real.sin (ω * w + q + (j : ℝ) * Real.pi / 2)) := by
      funext w
      exact ih w
    rw [hf]
    have hc : HasDerivAt (fun w : ℝ => ω * w + q + (j : ℝ) * Real.pi / 2) ω y := by
      simpa only [id_eq, mul_one] using
        (((hasDerivAt_id y).const_mul ω).add_const q).add_const ((j : ℝ) * Real.pi / 2)
    have hd := hc.sin.const_mul (ω ^ j)
    rw [hd.deriv]
    have hp : ω * y + q + ((j + 1 : ℕ) : ℝ) * Real.pi / 2 =
        (ω * y + q + (j : ℝ) * Real.pi / 2) + Real.pi / 2 := by
      push_cast
      ring
    rw [hp, Real.sin_add_pi_div_two, pow_succ]
    ring

theorem sineTerm_spatial_iteratedDeriv (j : ℕ) (a z T y : ℝ) (n : ℕ) :
    iteratedDeriv j (fun w => sineTerm a z T w n) y =
      (1 / a) * Real.exp (-(frequency a n) ^ 2 * T / 2) * (frequency a n) ^ j *
        Real.sin (frequency a n * (y + a) + (j : ℝ) * Real.pi / 2) *
          Real.sin (frequency a n * (z + a)) := by
  let ω := frequency a n
  let K := (1 / a) * Real.exp (-ω ^ 2 * T / 2) * Real.sin (ω * (z + a))
  have hf : (fun w => sineTerm a z T w n) = (fun w => K * Real.sin (ω * w + ω * a)) := by
    funext w
    have hp : ω * (w + a) = ω * w + ω * a := by ring
    dsimp only [sineTerm]
    change (1 / a) * Real.exp (-ω ^ 2 * T / 2) * Real.sin (ω * (w + a)) *
      Real.sin (ω * (z + a)) = K * Real.sin (ω * w + ω * a)
    rw [hp]
    dsimp only [K]
    ring
  rw [hf, iteratedDeriv_const_mul_field, affine_sin_iteratedDeriv]
  have hp : ω * y + ω * a + (j : ℝ) * Real.pi / 2 =
      ω * (y + a) + (j : ℝ) * Real.pi / 2 := by ring
  rw [hp]
  dsimp only [K, ω]
  ring

theorem mixedSineTerm_formula (j l : ℕ) (a z T y : ℝ) (n : ℕ) :
    mixedSineTerm j l a z T y n =
      (1 / a) * (frequency a n) ^ j * (-(frequency a n) ^ 2 / 2) ^ l *
        Real.exp (-(frequency a n) ^ 2 * T / 2) *
          Real.sin (frequency a n * (y + a) + (j : ℝ) * Real.pi / 2) *
            Real.sin (frequency a n * (z + a)) := by
  let ω := frequency a n
  let rate := ω ^ 2 / 2
  let K := (1 / a) * ω ^ j * Real.sin (ω * (y + a) + (j : ℝ) * Real.pi / 2) *
    Real.sin (ω * (z + a))
  have he (S : ℝ) : -ω ^ 2 * S / 2 = -(rate * S + 0) / 1 := by dsimp only [rate]; ring
  have hf : (fun S => iteratedDeriv j (fun w => sineTerm a z S w n) y) =
      (fun S => K * affineImageTerm rate 0 1 S) := by
    funext S
    rw [sineTerm_spatial_iteratedDeriv]
    change (1 / a) * Real.exp (-ω ^ 2 * S / 2) * ω ^ j *
      Real.sin (ω * (y + a) + (j : ℝ) * Real.pi / 2) * Real.sin (ω * (z + a)) =
        K * Real.exp (-(rate * S + 0) / 1)
    rw [he]
    dsimp only [K]
    ring
  rw [mixedSineTerm, hf, iteratedDeriv_const_mul_field, affineImageTerm_iteratedDeriv]
  rw [← he T]
  have hrate : -rate / 1 = -ω ^ 2 / 2 := by dsimp only [rate]; ring
  rw [hrate]
  dsimp only [K, ω]
  ring

theorem mixedSineTerm_spatial_hasDerivAt (j l : ℕ) (a z T y : ℝ) (n : ℕ) :
    HasDerivAt (fun w => mixedSineTerm j l a z T w n) (mixedSineTerm (j + 1) l a z T y n) y := by
  let ω := frequency a n
  let C := (1 / a) * ω ^ j * (-ω ^ 2 / 2) ^ l * Real.exp (-ω ^ 2 * T / 2) *
    Real.sin (ω * (z + a))
  have hf : (fun w => mixedSineTerm j l a z T w n) =
      (fun w => C * Real.sin (ω * (w + a) + (j : ℝ) * Real.pi / 2)) := by
    funext w
    rw [mixedSineTerm_formula]
    dsimp only [C, ω]
    ring
  have hc : HasDerivAt (fun w : ℝ => ω * (w + a) + (j : ℝ) * Real.pi / 2) ω y := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id y).add_const a).const_mul ω).add_const ((j : ℝ) * Real.pi / 2)
  have hd := hc.sin.const_mul C
  rw [hf, mixedSineTerm_formula]
  have hp : ω * (y + a) + ((j + 1 : ℕ) : ℝ) * Real.pi / 2 =
      (ω * (y + a) + (j : ℝ) * Real.pi / 2) + Real.pi / 2 := by push_cast; ring
  change HasDerivAt _ ((1 / a) * ω ^ (j + 1) * (-ω ^ 2 / 2) ^ l * Real.exp (-ω ^ 2 * T / 2) *
    Real.sin (ω * (y + a) + ((j + 1 : ℕ) : ℝ) * Real.pi / 2) * Real.sin (ω * (z + a))) y
  rw [hp, Real.sin_add_pi_div_two, pow_succ]
  convert hd using 1 <;> dsimp only [C] <;> ring

theorem mixedSineTerm_time_hasDerivAt (j l : ℕ) (a z T y : ℝ) (n : ℕ) :
    HasDerivAt (fun S => mixedSineTerm j l a z S y n) (mixedSineTerm j (l + 1) a z T y n) T := by
  let ω := frequency a n
  let C := (1 / a) * ω ^ j * (-ω ^ 2 / 2) ^ l *
    Real.sin (ω * (y + a) + (j : ℝ) * Real.pi / 2) * Real.sin (ω * (z + a))
  have hf : (fun S => mixedSineTerm j l a z S y n) =
      (fun S => C * Real.exp (-ω ^ 2 * S / 2)) := by
    funext S
    rw [mixedSineTerm_formula]
    dsimp only [C, ω]
    ring
  have hc : HasDerivAt (fun S : ℝ => -ω ^ 2 * S / 2) (-ω ^ 2 / 2) T := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id T).const_mul (-ω ^ 2)).div_const 2
  have hd := hc.exp.const_mul C
  rw [hf, mixedSineTerm_formula, pow_succ]
  convert hd using 1 <;> dsimp only [C, ω] <;> ring

theorem mixedSineTerm_norm_bound (j l : ℕ) (a z T y : ℝ) (n : ℕ) (ha : 0 < a) :
    ‖mixedSineTerm j l a z T y n‖ ≤
      (1 / a) * (frequency a n) ^ j * ((frequency a n) ^ 2 / 2) ^ l *
        Real.exp (-(frequency a n) ^ 2 * T / 2) := by
  have hω := frequency_pos a n ha
  let P := (1 / a) * (frequency a n) ^ j * ((frequency a n) ^ 2 / 2) ^ l *
    Real.exp (-(frequency a n) ^ 2 * T / 2)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  rw [mixedSineTerm_formula, Real.norm_eq_abs]
  calc
    _ = P * |Real.sin (frequency a n * (y + a) + (j : ℝ) * Real.pi / 2)| *
        |Real.sin (frequency a n * (z + a))| := by
      dsimp only [P]
      simp only [abs_mul, abs_pow, abs_div, abs_one, abs_of_pos ha, abs_of_pos hω,
        abs_neg, abs_of_pos (Real.exp_pos _), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ P * 1 * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hP) (Real.abs_sin_le_one _)
      (abs_nonneg _) (by positivity)
    _ = _ := by dsimp only [P]; ring

theorem mixedSineTerm_weighted_bound (j l : ℕ) (a z T y : ℝ) (n : ℕ) (ha : 0 < a) :
    ‖mixedSineTerm j l a z T y n‖ ≤
      ((1 / a) * (Real.pi / (2 * a)) ^ j * (Real.pi ^ 2 / (8 * a ^ 2)) ^ l) *
        weightedGaussian (Real.pi ^ 2 / 8) (j + 2 * l) (T / a ^ 2) n := by
  let N : ℝ := (n : ℝ) + 1
  have hω : frequency a n = N * (Real.pi / (2 * a)) := by dsimp only [frequency, N]; ring
  have hrate : (frequency a n) ^ 2 / 2 = N ^ 2 * (Real.pi ^ 2 / (8 * a ^ 2)) := by
    rw [hω]
    field_simp [ne_of_gt ha] <;> ring
  have he : -(frequency a n) ^ 2 * T / 2 = -(Real.pi ^ 2 / 8) * N ^ 2 * (T / a ^ 2) := by
    rw [hω]
    field_simp [ne_of_gt ha] <;> ring
  calc
    _ ≤ (1 / a) * (frequency a n) ^ j * ((frequency a n) ^ 2 / 2) ^ l *
        Real.exp (-(frequency a n) ^ 2 * T / 2) := mixedSineTerm_norm_bound j l a z T y n ha
    _ = _ := by
      rw [hrate, he, hω]
      dsimp only [weightedGaussian, N]
      simp only [mul_pow, pow_add, pow_mul]
      ring

theorem mixedSineTerm_summable (j l : ℕ) (a z T y : ℝ) (ha : 0 < a) (hT : 0 < T) :
    Summable (fun n : ℕ => mixedSineTerm j l a z T y n) := by
  have hs := weightedGaussian_summable (Real.pi ^ 2 / 8) (T / a ^ 2) (j + 2 * l)
    (by positivity) (by positivity)
  exact (hs.mul_left ((1 / a) * (Real.pi / (2 * a)) ^ j *
    (Real.pi ^ 2 / (8 * a ^ 2)) ^ l)).of_norm_bounded
    (fun n => mixedSineTerm_weighted_bound j l a z T y n ha)

end Shao.C2.IntervalSineTerms

