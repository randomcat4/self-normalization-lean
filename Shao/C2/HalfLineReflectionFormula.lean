import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section
namespace Shao.C2.HalfLineReflectionFormula

def upperReflection (a y T z : ℝ) : ℝ :=
  1 - Real.exp (-2 * (a - y) * (a - z) / T)

def lowerReflection (a y T z : ℝ) : ℝ :=
  1 - Real.exp (-2 * (a + y) * (a + z) / T)

theorem gaussian_linear_absorption (r : ℝ) :
    r * Real.exp (-(r ^ 2)) ≤ 1 := by
  have h : r ≤ Real.exp (r ^ 2) := by
    have he := Real.add_one_le_exp (r ^ 2)
    nlinarith [sq_nonneg (r - 1 / 2)]
  calc
    r * Real.exp (-(r ^ 2)) ≤ Real.exp (r ^ 2) * Real.exp (-(r ^ 2)) :=
      mul_le_mul_of_nonneg_right h (le_of_lt (Real.exp_pos _))
    _ = 1 := by rw [← Real.exp_add]; simp

theorem positive_reflection_slope_bound (u v T : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hT : 0 < T) :
    (2 * v / T) * Real.exp (-2 * u * v / T) ≤
      4 / Real.sqrt T * (1 + |u - v| / Real.sqrt T) := by
  let s := Real.sqrt T
  have hs : 0 < s := Real.sqrt_pos.2 hT
  have hs2 : s ^ 2 = T := Real.sq_sqrt hT.le
  have hs0 : s ≠ 0 := ne_of_gt hs
  have ht0 : T ≠ 0 := ne_of_gt hT
  have hc : 0 ≤ 2 * v / T := by positivity
  have hd : 0 ≤ |u - v| / s := by positivity
  by_cases hsmall : v ≤ 2 * |u - v|
  · have he : Real.exp (-2 * u * v / T) ≤ 1 := by
      apply Real.exp_le_one_iff.2
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hT.le
    calc
      (2 * v / T) * Real.exp (-2 * u * v / T) ≤ 2 * v / T := by
        simpa using mul_le_mul_of_nonneg_left he hc
      _ ≤ 4 * |u - v| / T := (div_le_div_iff_of_pos_right hT).2 (by linarith)
      _ = 4 / s * (|u - v| / s) := by rw [← hs2]; field_simp
      _ ≤ 4 / s * (1 + |u - v| / s) := by
        apply mul_le_mul_of_nonneg_left (by linarith)
        positivity
  · have huv : v ^ 2 ≤ 2 * u * v := by
      have ha := neg_abs_le (u - v)
      have hvu : v ≤ 2 * u := by linarith
      nlinarith
    have hexp : -2 * u * v / T ≤ -((v / s) ^ 2) := by
      rw [div_pow, hs2, ← neg_div]
      exact (div_le_div_iff_of_pos_right hT).2 (by nlinarith)
    calc
      (2 * v / T) * Real.exp (-2 * u * v / T) =
          2 / s * ((v / s) * Real.exp (-2 * u * v / T)) := by
            rw [← hs2]; field_simp
      _ ≤ 2 / s * ((v / s) * Real.exp (-((v / s) ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) (by positivity)
      _ ≤ 2 / s * 1 :=
        mul_le_mul_of_nonneg_left (gaussian_linear_absorption (v / s)) (by positivity)
      _ ≤ 4 / s * (1 + |u - v| / s) := by
        have hp : 0 ≤ 2 / s := by positivity
        have hp2 : 0 ≤ 4 / s * (|u - v| / s) := by positivity
        ring_nf at hp hp2 ⊢
        linarith

theorem upperReflection_hasDerivAt (a y T z : ℝ) :
    HasDerivAt (fun u : ℝ => upperReflection a u T z)
      (-(2 * (a - z) / T) * Real.exp (-2 * (a - y) * (a - z) / T)) y := by
  have he := ((((hasDerivAt_const y a).sub (hasDerivAt_id y)).const_mul (-2)).mul_const
    (a - z)).div_const T
  have h := (hasDerivAt_const y 1).sub he.exp
  convert h using 1
  · rfl
  · dsimp only [Pi.sub_apply, id_eq]
    ring

theorem lowerReflection_hasDerivAt (a y T z : ℝ) :
    HasDerivAt (fun u : ℝ => lowerReflection a u T z)
      ((2 * (a + z) / T) * Real.exp (-2 * (a + y) * (a + z) / T)) y := by
  have he := ((((hasDerivAt_const y a).add (hasDerivAt_id y)).const_mul (-2)).mul_const
    (a + z)).div_const T
  have h := (hasDerivAt_const y 1).sub he.exp
  convert h using 1
  · rfl
  · dsimp only [Pi.add_apply, id_eq]
    ring

theorem upperReflection_deriv_bound (a y T z : ℝ) (hT : 0 < T) (hy : y < a) (hz : z < a) :
    |deriv (fun u : ℝ => upperReflection a u T z) y| ≤
      4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T) := by
  rw [(upperReflection_hasDerivAt a y T z).deriv, abs_mul, abs_neg,
    abs_of_pos (show 0 < 2 * (a - z) / T by positivity),
    abs_of_pos (Real.exp_pos _)]
  have h := positive_reflection_slope_bound (a - y) (a - z) T (by linarith)
    (by linarith) hT
  simpa only [show a - y - (a - z) = z - y by ring] using h

theorem lowerReflection_deriv_bound (a y T z : ℝ) (hT : 0 < T) (hy : -a < y) (hz : -a < z) :
    |deriv (fun u : ℝ => lowerReflection a u T z) y| ≤
      4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T) := by
  have haz : 0 < a + z := by linarith
  rw [(lowerReflection_hasDerivAt a y T z).deriv, abs_mul,
    abs_of_pos (show 0 < 2 * (a + z) / T by positivity),
    abs_of_pos (Real.exp_pos _)]
  have h := positive_reflection_slope_bound (a + y) (a + z) T (by linarith)
    (by linarith) hT
  have he : a + y - (a + z) = y - z := by ring
  simpa only [he, abs_sub_comm y z] using h

end Shao.C2.HalfLineReflectionFormula
