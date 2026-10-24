import Shao.C2.HalfLineHeatEquation
import Mathlib.Analysis.Calculus.Deriv.Pow

noncomputable section
namespace Shao.C2.HalfLineTimeProfiles
open Shao.C2.HalfLineReflectionFormula

def timeCompletion (C T : ℝ) : ℝ := 1 - Real.exp (-C / T)

theorem nonneg_exp_monomial_profile (q : ℝ) (hq : 0 ≤ q) (m : ℕ) :
    q ^ m * Real.exp (-q) ≤
      (2 : ℝ) ^ m * (Nat.factorial m : ℝ) * Real.exp (-q / 2) := by
  have hfact : 0 < (Nat.factorial m : ℝ) := by exact_mod_cast (Nat.factorial_pos m)
  have h := Real.pow_div_factorial_le_exp (q / 2) (show 0 ≤ q / 2 by positivity) m
  have hp : q ^ m ≤ (2 : ℝ) ^ m * (Nat.factorial m : ℝ) * Real.exp (q / 2) := by
    have hh := (div_le_iff₀ hfact).1 h
    calc
      q ^ m = (2 : ℝ) ^ m * (q / 2) ^ m := by rw [← mul_pow]; congr 1; ring
      _ ≤ (2 : ℝ) ^ m * (Real.exp (q / 2) * (Nat.factorial m : ℝ)) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ((2 : ℝ) ^ m * (Nat.factorial m : ℝ) * Real.exp (q / 2)) * Real.exp (-q) :=
      mul_le_mul_of_nonneg_right hp (le_of_lt (Real.exp_pos _))
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem timeCompletion_hasDerivAt (C T : ℝ) (hT : 0 < T) :
    HasDerivAt (timeCompletion C)
      (-(C / T ^ 2) * Real.exp (-C / T)) T := by
  have he := (hasDerivAt_const T (-C)).div (hasDerivAt_id T) (ne_of_gt hT)
  have h := (hasDerivAt_const T 1).sub he.exp
  convert h using 1
  · rfl
  · dsimp only [Pi.div_apply, id_eq]
    ring

theorem timeCompletion_second_hasDerivAt (C T : ℝ) (hT : 0 < T) :
    HasDerivAt (deriv (timeCompletion C))
      ((2 * C / T ^ 3 - C ^ 2 / T ^ 4) * Real.exp (-C / T)) T := by
  have hc := (hasDerivAt_const T (-C)).div ((hasDerivAt_id T).pow 2)
    (pow_ne_zero 2 (ne_of_gt hT))
  have he := ((hasDerivAt_const T (-C)).div (hasDerivAt_id T) (ne_of_gt hT)).exp
  have h := hc.mul he
  have hf : HasDerivAt (fun t : ℝ => (-C / t ^ 2) * Real.exp (-C / t))
      ((2 * C / T ^ 3 - C ^ 2 / T ^ 4) * Real.exp (-C / T)) T := by
    convert h using 1
    · rfl
    · dsimp only [Pi.div_apply, Pi.pow_apply, id_eq]
      field_simp [ne_of_gt hT] <;> ring
  apply hf.congr_of_eventuallyEq
  refine Filter.mem_of_superset (Ioi_mem_nhds hT) ?_
  intro t ht
  change deriv (timeCompletion C) t = (-C / t ^ 2) * Real.exp (-C / t)
  rw [(timeCompletion_hasDerivAt C t ht).deriv]
  congr 1 <;> ring

theorem timeCompletion_third_hasDerivAt (C T : ℝ) (hT : 0 < T) :
    HasDerivAt (deriv (deriv (timeCompletion C)))
      ((-6 * C / T ^ 4 + 6 * C ^ 2 / T ^ 5 - C ^ 3 / T ^ 6) * Real.exp (-C / T)) T := by
  have ha := (hasDerivAt_const T (2 * C)).div ((hasDerivAt_id T).pow 3)
    (pow_ne_zero 3 (ne_of_gt hT))
  have hb := (hasDerivAt_const T (C ^ 2)).div ((hasDerivAt_id T).pow 4)
    (pow_ne_zero 4 (ne_of_gt hT))
  have he := ((hasDerivAt_const T (-C)).div (hasDerivAt_id T) (ne_of_gt hT)).exp
  have h := (ha.sub hb).mul he
  have hf : HasDerivAt (fun t : ℝ => (2 * C / t ^ 3 - C ^ 2 / t ^ 4) * Real.exp (-C / t))
      ((-6 * C / T ^ 4 + 6 * C ^ 2 / T ^ 5 - C ^ 3 / T ^ 6) * Real.exp (-C / T)) T := by
    convert h using 1
    · rfl
    · dsimp only [Pi.div_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
      field_simp [ne_of_gt hT] <;> ring
  apply hf.congr_of_eventuallyEq
  exact Filter.mem_of_superset (Ioi_mem_nhds hT)
    (fun t ht => (timeCompletion_second_hasDerivAt C t ht).deriv)

theorem timeCompletion_time_profiles (C T : ℝ) (hC : 0 ≤ C) (hT : 0 < T) :
    |deriv (timeCompletion C) T| ≤ 2 / T * Real.exp (-C / (2 * T)) ∧
    |deriv (deriv (timeCompletion C)) T| ≤ 12 / T ^ 2 * Real.exp (-C / (2 * T)) ∧
    |deriv (deriv (deriv (timeCompletion C))) T| ≤ 108 / T ^ 3 * Real.exp (-C / (2 * T)) := by
  let q : ℝ := C / T
  let E : ℝ := Real.exp (-q)
  let P : ℝ := Real.exp (-q / 2)
  have hq : 0 ≤ q := div_nonneg hC hT.le
  have hEp : 0 < E := Real.exp_pos _
  have hPp : 0 < P := Real.exp_pos _
  have h1 := nonneg_exp_monomial_profile q hq 1
  have h2 := nonneg_exp_monomial_profile q hq 2
  have h3 := nonneg_exp_monomial_profile q hq 3
  norm_num at h1 h2 h3
  change q * E ≤ 2 * P at h1
  change q ^ 2 * E ≤ 8 * P at h2
  change q ^ 3 * E ≤ 48 * P at h3
  have hqE : 0 ≤ q * E := mul_nonneg hq hEp.le
  have hq2E : 0 ≤ q ^ 2 * E := mul_nonneg (sq_nonneg q) hEp.le
  have hq3E : 0 ≤ q ^ 3 * E := mul_nonneg (pow_nonneg hq 3) hEp.le
  have hp2 : |(2 * q - q ^ 2) * E| ≤ 12 * P := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have hp3 : |(-6 * q + 6 * q ^ 2 - q ^ 3) * E| ≤ 108 * P := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have he : Real.exp (-C / T) = E := by
    dsimp only [E, q]
    congr 1
    ring
  have hprof : Real.exp (-C / (2 * T)) = P := by
    dsimp only [P, q]
    congr 1
    field_simp [ne_of_gt hT] <;> ring
  have hf1 : deriv (timeCompletion C) T = -(q * E) / T := by
    rw [(timeCompletion_hasDerivAt C T hT).deriv, he]
    dsimp only [q]
    field_simp [ne_of_gt hT] <;> ring
  have hf2 : deriv (deriv (timeCompletion C)) T = ((2 * q - q ^ 2) * E) / T ^ 2 := by
    rw [(timeCompletion_second_hasDerivAt C T hT).deriv, he]
    dsimp only [q]
    field_simp [ne_of_gt hT] <;> ring
  have hf3 : deriv (deriv (deriv (timeCompletion C))) T =
      ((-6 * q + 6 * q ^ 2 - q ^ 3) * E) / T ^ 3 := by
    rw [(timeCompletion_third_hasDerivAt C T hT).deriv, he]
    dsimp only [q]
    field_simp [ne_of_gt hT] <;> ring
  rw [hprof]
  refine ⟨?_, ?_, ?_⟩
  · rw [hf1, abs_div, abs_neg, abs_of_nonneg hqE, abs_of_pos hT]
    convert (div_le_div_iff_of_pos_right hT).2 h1 using 1 <;> ring
  · rw [hf2, abs_div, abs_of_pos (pow_pos hT 2)]
    convert (div_le_div_iff_of_pos_right (pow_pos hT 2)).2 hp2 using 1 <;> ring
  · rw [hf3, abs_div, abs_of_pos (pow_pos hT 3)]
    convert (div_le_div_iff_of_pos_right (pow_pos hT 3)).2 hp3 using 1 <;> ring

theorem upperReflection_eq_timeCompletion (a y T z : ℝ) :
    upperReflection a y T z = timeCompletion (2 * (a - y) * (a - z)) T := by
  unfold upperReflection timeCompletion
  congr 2
  ring

theorem lowerReflection_eq_timeCompletion (a y T z : ℝ) :
    lowerReflection a y T z = timeCompletion (2 * (a + y) * (a + z)) T := by
  unfold lowerReflection timeCompletion
  congr 2
  ring

end Shao.C2.HalfLineTimeProfiles
