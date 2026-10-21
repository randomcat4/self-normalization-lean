import Shao.OQ4.CosineCoefficients
import Shao.OQ4.KilledCosine
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Explicit finite-power bounds for the free cosine coefficient

The coefficient is the actual free one-step expectation. No killed-kernel
eigenvalue, occupation, or long-time assertion is used.
-/

namespace Shao.OQ4

open MeasureTheory

theorem cosine_powers_scalar_bounds (M h ρ : ℝ) (hM : 0 ≤ M) (hh1 : 1 ≤ h)
    (hlarge : Real.pi * (1 + M) ≤ h)
    (herr : |ρ - (1 - Real.pi ^ 2 / (8 * h ^ 2))| ≤ Real.pi ^ 3 * M / (48 * h ^ 3)) :
    1 - Real.pi ^ 2 / (4 * h ^ 2) ≤ ρ ∧
      ρ ≤ 1 - Real.pi ^ 2 / (16 * h ^ 2) ∧ (3 : ℝ) / 4 ≤ ρ ∧ ρ < 1 := by
  have hh : 0 < h := by linarith
  have hpi : Real.pi ≤ h := by nlinarith [Real.pi_pos]
  have hpiM : Real.pi * M ≤ h := by nlinarith [Real.pi_pos]
  let q : ℝ := Real.pi ^ 2 / h ^ 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 :=
    (div_le_one (sq_pos_of_pos hh)).2 (pow_le_pow_left₀ (le_of_lt Real.pi_pos) hpi 2)
  have hratio : Real.pi * M / h ≤ 1 := (div_le_one hh).2 hpiM
  have heq : Real.pi ^ 3 * M / (48 * h ^ 3) = (q / 48) * (Real.pi * M / h) := by
    dsimp [q]
    field_simp
  have he : Real.pi ^ 3 * M / (48 * h ^ 3) ≤ q / 48 := by
    rw [heq]
    simpa using mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ q / 48)
  have hcenter : Real.pi ^ 2 / (8 * h ^ 2) = q / 8 := by dsimp [q]; ring
  have hfour : Real.pi ^ 2 / (4 * h ^ 2) = q / 4 := by dsimp [q]; ring
  have hsixteen : Real.pi ^ 2 / (16 * h ^ 2) = q / 16 := by dsimp [q]; ring
  rw [hcenter] at herr
  have ht := abs_le.mp (herr.trans he)
  rw [hfour, hsixteen]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem cosine_powers_inverse_scalar (h ρ : ℝ) (_hh : 0 < h)
    (hlower : 1 - Real.pi ^ 2 / (4 * h ^ 2) ≤ ρ)
    (hthree : (3 : ℝ) / 4 ≤ ρ) (hupper : ρ ≤ 1) (n : ℕ) :
    (ρ ^ n)⁻¹ ≤ Real.exp (Real.pi ^ 2 * n / (2 * h ^ 2)) := by
  have hρ : 0 < ρ := by linarith
  have hu : 0 ≤ 1 - ρ := by linarith
  have hratio : ρ⁻¹ - 1 ≤ 2 * (1 - ρ) := by
    have heq : ρ⁻¹ - 1 = (1 - ρ) / ρ := by field_simp
    rw [heq]
    apply (div_le_iff₀ hρ).2
    have hp := mul_nonneg hu (show 0 ≤ 2 * ρ - 1 by linarith)
    nlinarith
  have hscale : Real.pi ^ 2 / (2 * h ^ 2) = 2 * (Real.pi ^ 2 / (4 * h ^ 2)) := by ring
  have hlog : -Real.log ρ ≤ Real.pi ^ 2 / (2 * h ^ 2) := by
    rw [hscale]
    linarith [Real.one_sub_inv_le_log_of_pos hρ]
  calc
    (ρ ^ n)⁻¹ = Real.exp (-((n : ℝ) * Real.log ρ)) := by
      rw [← Real.log_pow, ← Real.log_inv, Real.exp_log (inv_pos.mpr (pow_pos hρ n))]
    _ ≤ Real.exp (Real.pi ^ 2 * n / (2 * h ^ 2)) := by
      apply Real.exp_le_exp.mpr
      convert mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg n) using 1 <;> ring

/-- A safe quadratic logarithm estimate, obtained from elementary log bounds. -/
theorem cosine_powers_log_linear_scalar (ρ : ℝ) (hhalf : (1 : ℝ) / 2 ≤ ρ)
    (_hupper : ρ ≤ 1) : |Real.log ρ + (1 - ρ)| ≤ 2 * (1 - ρ) ^ 2 := by
  have hρ : 0 < ρ := by linarith
  have hlogupper := Real.log_le_sub_one_of_pos hρ
  have hloglower := Real.one_sub_inv_le_log_of_pos hρ
  calc
    |Real.log ρ + (1 - ρ)| = (ρ - 1) - Real.log ρ := by
      rw [abs_of_nonpos (by linarith)]
      ring
    _ ≤ (ρ - 1) - (1 - ρ⁻¹) := by linarith
    _ = (1 - ρ) ^ 2 / ρ := by field_simp; ring
    _ ≤ 2 * (1 - ρ) ^ 2 := by
      apply (div_le_iff₀ hρ).2
      have hp := mul_nonneg (sub_nonneg.mpr hhalf) (sq_nonneg (1 - ρ))
      nlinarith

theorem cosine_powers_log_error_scalar (M h ρ : ℝ) (_hM : 0 ≤ M) (hh1 : 1 ≤ h)
    (hlower : 1 - Real.pi ^ 2 / (4 * h ^ 2) ≤ ρ)
    (hthree : (3 : ℝ) / 4 ≤ ρ) (hupper : ρ ≤ 1)
    (herr : |ρ - (1 - Real.pi ^ 2 / (8 * h ^ 2))| ≤ Real.pi ^ 3 * M / (48 * h ^ 3)) :
    |Real.log ρ + Real.pi ^ 2 / (8 * h ^ 2)| ≤
      (Real.pi ^ 3 * M / 48 + Real.pi ^ 4 / 8) / h ^ 3 := by
  have hh : 0 < h := by linarith
  have hu : 0 ≤ 1 - ρ := by linarith
  have huq : 1 - ρ ≤ Real.pi ^ 2 / (4 * h ^ 2) := by linarith
  have hsquare : (1 - ρ) ^ 2 ≤ (Real.pi ^ 2 / (4 * h ^ 2)) ^ 2 :=
    pow_le_pow_left₀ hu huq 2
  have hlin := cosine_powers_log_linear_scalar ρ (by linarith) hupper
  have hquad : 2 * (1 - ρ) ^ 2 ≤ Real.pi ^ 4 / (8 * h ^ 4) := by
    have heq : 2 * (Real.pi ^ 2 / (4 * h ^ 2)) ^ 2 = Real.pi ^ 4 / (8 * h ^ 4) := by ring
    rw [← heq]
    linarith
  have hpow : h ^ 3 ≤ h ^ 4 := by
    have hp := mul_nonneg (pow_nonneg (le_of_lt hh) 3) (sub_nonneg.mpr hh1)
    nlinarith
  have hden : Real.pi ^ 4 / (8 * h ^ 4) ≤ Real.pi ^ 4 / (8 * h ^ 3) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  calc
    |Real.log ρ + Real.pi ^ 2 / (8 * h ^ 2)| =
        |(Real.log ρ + (1 - ρ)) + (ρ - (1 - Real.pi ^ 2 / (8 * h ^ 2)))| := by congr 1; ring
    _ ≤ |Real.log ρ + (1 - ρ)| + |ρ - (1 - Real.pi ^ 2 / (8 * h ^ 2))| := abs_add_le _ _
    _ ≤ 2 * (1 - ρ) ^ 2 + Real.pi ^ 3 * M / (48 * h ^ 3) := add_le_add hlin herr
    _ ≤ Real.pi ^ 4 / (8 * h ^ 3) + Real.pi ^ 3 * M / (48 * h ^ 3) :=
      add_le_add ((hquad.trans hden)) le_rfl
    _ = (Real.pi ^ 3 * M / 48 + Real.pi ^ 4 / 8) / h ^ 3 := by ring

section ActualCoefficient

variable (ν : Measure ℝ) [IsProbabilityMeasure ν] (M h : ℝ)
variable (hId : Integrable (fun y : ℝ => y) ν)
  (hSq : Integrable (fun y : ℝ => y ^ 2) ν)
  (hCube : Integrable (fun y : ℝ => |y| ^ 3) ν)
  (hmean : (∫ y : ℝ, y ∂ν) = 0) (hsecond : (∫ y : ℝ, y ^ 2 ∂ν) = 1)
  (hM : 0 ≤ M) (hβ : (∫ y : ℝ, |y| ^ 3 ∂ν) ≤ M)
  (hh1 : 1 ≤ h) (hlarge : Real.pi * (1 + M) ≤ h)

include hId hSq hCube hmean hsecond hM hβ hh1 hlarge

omit hM hlarge in
theorem cosineCoefficient_large_h_remainder :
    |cosineCoefficient ν (Real.pi / (2 * h)) - (1 - Real.pi ^ 2 / (8 * h ^ 2))| ≤
      Real.pi ^ 3 * M / (48 * h ^ 3) := by
  have hh : 0 < h := by linarith
  have ht := (cosine_coefficients_h_bound ν (fun y : ℝ => y) h hh
    hId hSq hCube hmean hsecond).1
  calc
    _ ≤ Real.pi ^ 3 * (∫ y : ℝ, |y| ^ 3 ∂ν) / (48 * h ^ 3) := ht
    _ ≤ Real.pi ^ 3 * M / (48 * h ^ 3) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hβ (by positivity)) (by positivity)

theorem cosineCoefficient_large_h_bounds :
    1 - Real.pi ^ 2 / (4 * h ^ 2) ≤ cosineCoefficient ν (Real.pi / (2 * h)) ∧
      cosineCoefficient ν (Real.pi / (2 * h)) ≤ 1 - Real.pi ^ 2 / (16 * h ^ 2) ∧
      (3 : ℝ) / 4 ≤ cosineCoefficient ν (Real.pi / (2 * h)) ∧
      cosineCoefficient ν (Real.pi / (2 * h)) < 1 :=
  cosine_powers_scalar_bounds M h _ hM hh1 hlarge
    (cosineCoefficient_large_h_remainder ν M h hId hSq hCube hmean hsecond hβ hh1)

theorem cosineCoefficient_inverse_pow_bound (n : ℕ) :
    (cosineCoefficient ν (Real.pi / (2 * h)) ^ n)⁻¹ ≤
      Real.exp (Real.pi ^ 2 * n / (2 * h ^ 2)) := by
  have hb := cosineCoefficient_large_h_bounds ν M h hId hSq hCube hmean hsecond hM hβ hh1 hlarge
  exact cosine_powers_inverse_scalar h _ (by linarith) hb.1 hb.2.2.1 hb.2.2.2.le n

theorem cosineCoefficient_inverse_pow_uniform (n : ℕ) (hn : (n : ℝ) ≤ 2 * h ^ 2) :
    (cosineCoefficient ν (Real.pi / (2 * h)) ^ n)⁻¹ ≤ Real.exp (Real.pi ^ 2) := by
  apply (cosineCoefficient_inverse_pow_bound ν M h hId hSq hCube hmean hsecond hM hβ hh1 hlarge n).trans
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ (by positivity : 0 < 2 * h ^ 2)).2
  nlinarith [mul_le_mul_of_nonneg_left hn (sq_nonneg Real.pi)]

theorem cosineCoefficient_floor_inverse_bounds :
    (cosineCoefficient ν (Real.pi / (2 * h)) ^ (⌊h ^ 2⌋₊ + 1))⁻¹ ≤ Real.exp (Real.pi ^ 2) ∧
      (cosineCoefficient ν (Real.pi / (2 * h)) ^ (2 * ⌊h ^ 2⌋₊))⁻¹ ≤ Real.exp (Real.pi ^ 2) := by
  have hf : (⌊h ^ 2⌋₊ : ℝ) ≤ h ^ 2 := Nat.floor_le (sq_nonneg h)
  have hs : 1 ≤ h ^ 2 := by nlinarith
  constructor
  · apply cosineCoefficient_inverse_pow_uniform ν M h hId hSq hCube hmean hsecond hM hβ hh1 hlarge
    push_cast
    linarith
  · apply cosineCoefficient_inverse_pow_uniform ν M h hId hSq hCube hmean hsecond hM hβ hh1 hlarge
    push_cast
    linarith

theorem cosineCoefficient_log_error :
    |Real.log (cosineCoefficient ν (Real.pi / (2 * h))) + Real.pi ^ 2 / (8 * h ^ 2)| ≤
      (Real.pi ^ 3 * M / 48 + Real.pi ^ 4 / 8) / h ^ 3 := by
  have hb := cosineCoefficient_large_h_bounds ν M h hId hSq hCube hmean hsecond hM hβ hh1 hlarge
  exact cosine_powers_log_error_scalar M h _ hM hh1 hb.1 hb.2.2.1 hb.2.2.2.le
    (cosineCoefficient_large_h_remainder ν M h hId hSq hCube hmean hsecond hβ hh1)

theorem cosineCoefficient_log_error_mul (N : ℕ) :
    |(N : ℝ) * Real.log (cosineCoefficient ν (Real.pi / (2 * h))) +
      Real.pi ^ 2 * N / (8 * h ^ 2)| ≤
      (Real.pi ^ 3 * M / 48 + Real.pi ^ 4 / 8) * N / h ^ 3 := by
  have ht := cosineCoefficient_log_error ν M h hId hSq hCube hmean hsecond hM hβ hh1 hlarge
  calc
    _ = (N : ℝ) * |Real.log (cosineCoefficient ν (Real.pi / (2 * h))) +
        Real.pi ^ 2 / (8 * h ^ 2)| := by
      calc
        _ = |(N : ℝ) * (Real.log (cosineCoefficient ν (Real.pi / (2 * h))) +
            Real.pi ^ 2 / (8 * h ^ 2))| := by congr 1; ring
        _ = _ := by rw [abs_mul, abs_of_nonneg (show 0 ≤ (N : ℝ) from Nat.cast_nonneg N)]
    _ ≤ (N : ℝ) * ((Real.pi ^ 3 * M / 48 + Real.pi ^ 4 / 8) / h ^ 3) :=
      mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg N)
    _ = (Real.pi ^ 3 * M / 48 + Real.pi ^ 4 / 8) * N / h ^ 3 := by ring

end ActualCoefficient

end Shao.OQ4
