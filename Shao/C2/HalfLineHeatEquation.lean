import Shao.C2.HalfLineReflectionFormula
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section
namespace Shao.C2.HalfLineHeatEquation
open Shao.C2.HalfLineReflectionFormula

theorem upperReflection_second_hasDerivAt (a y T z : ℝ) :
    HasDerivAt (deriv (fun u : ℝ => upperReflection a u T z))
      (-((2 * (a - z) / T) ^ 2) * Real.exp (-2 * (a - y) * (a - z) / T)) y := by
  have he := ((((hasDerivAt_const y a).sub (hasDerivAt_id y)).const_mul (-2)).mul_const
    (a - z)).div_const T
  have h := he.exp.const_mul (-(2 * (a - z) / T))
  convert h using 1
  · funext u
    exact (upperReflection_hasDerivAt a u T z).deriv
  · dsimp only [Pi.sub_apply, id_eq]
    ring

theorem lowerReflection_second_hasDerivAt (a y T z : ℝ) :
    HasDerivAt (deriv (fun u : ℝ => lowerReflection a u T z))
      (-((2 * (a + z) / T) ^ 2) * Real.exp (-2 * (a + y) * (a + z) / T)) y := by
  have he := ((((hasDerivAt_const y a).add (hasDerivAt_id y)).const_mul (-2)).mul_const
    (a + z)).div_const T
  have h := he.exp.const_mul ((2 * (a + z) / T))
  convert h using 1
  · funext u
    exact (lowerReflection_hasDerivAt a u T z).deriv
  · dsimp only [Pi.add_apply, id_eq]
    ring

theorem upperReflection_time_hasDerivAt (a y T z : ℝ) (hT : 0 < T) :
    HasDerivAt (fun t : ℝ => upperReflection a y t z)
      (-(2 * (a - y) * (a - z) / T ^ 2) * Real.exp (-2 * (a - y) * (a - z) / T)) T := by
  have he := (hasDerivAt_const T (-2 * (a - y) * (a - z))).div
    (hasDerivAt_id T) (ne_of_gt hT)
  have h := (hasDerivAt_const T 1).sub he.exp
  convert h using 1
  · rfl
  · dsimp only [Pi.div_apply, id_eq]
    ring

theorem lowerReflection_time_hasDerivAt (a y T z : ℝ) (hT : 0 < T) :
    HasDerivAt (fun t : ℝ => lowerReflection a y t z)
      (-(2 * (a + y) * (a + z) / T ^ 2) * Real.exp (-2 * (a + y) * (a + z) / T)) T := by
  have he := (hasDerivAt_const T (-2 * (a + y) * (a + z))).div
    (hasDerivAt_id T) (ne_of_gt hT)
  have h := (hasDerivAt_const T 1).sub he.exp
  convert h using 1
  · rfl
  · dsimp only [Pi.div_apply, id_eq]
    ring

theorem upperReflection_heat_equation (a y T z : ℝ) (hT : 0 < T) :
    deriv (fun t : ℝ => upperReflection a y t z) T =
      (1 / 2 : ℝ) * deriv (deriv (fun u : ℝ => upperReflection a u T z)) y +
        (z - y) / T * deriv (fun u : ℝ => upperReflection a u T z) y := by
  rw [(upperReflection_time_hasDerivAt a y T z hT).deriv,
    (upperReflection_second_hasDerivAt a y T z).deriv, (upperReflection_hasDerivAt a y T z).deriv]
  field_simp [ne_of_gt hT] <;> ring

theorem lowerReflection_heat_equation (a y T z : ℝ) (hT : 0 < T) :
    deriv (fun t : ℝ => lowerReflection a y t z) T =
      (1 / 2 : ℝ) * deriv (deriv (fun u : ℝ => lowerReflection a u T z)) y +
        (z - y) / T * deriv (fun u : ℝ => lowerReflection a u T z) y := by
  rw [(lowerReflection_time_hasDerivAt a y T z hT).deriv,
    (lowerReflection_second_hasDerivAt a y T z).deriv, (lowerReflection_hasDerivAt a y T z).deriv]
  field_simp [ne_of_gt hT] <;> ring

end Shao.C2.HalfLineHeatEquation
