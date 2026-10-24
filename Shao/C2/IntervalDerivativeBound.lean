import Shao.C2.BridgeDomination
import Shao.C2.HalfLineReflectionFormula

noncomputable section
namespace Shao.C2.IntervalDerivativeBound
open MeasureTheory Set
open Shao.C2.BridgeDomination Shao.C2.HalfLineReflectionFormula

theorem upperCompletion_hasDerivAt_of_reflection
    (P : Measure BridgeNoise) (a y T z : ℝ) (hy : y < a)
    (hReflection : ∀ s : ℝ, s < a → upperCompletion P a s T z = upperReflection a s T z) :
    HasDerivAt (fun s : ℝ => upperCompletion P a s T z)
      (deriv (fun s : ℝ => upperReflection a s T z) y) y := by
  have h := upperReflection_hasDerivAt a y T z
  rw [h.deriv]
  exact h.congr_of_eventuallyEq
    (Filter.mem_of_superset (Iio_mem_nhds hy) (fun s hs => hReflection s hs))

theorem lowerCompletion_hasDerivAt_of_reflection
    (P : Measure BridgeNoise) (a y T z : ℝ) (hy : -a < y)
    (hReflection : ∀ s : ℝ, -a < s → lowerCompletion P a s T z = lowerReflection a s T z) :
    HasDerivAt (fun s : ℝ => lowerCompletion P a s T z)
      (deriv (fun s : ℝ => lowerReflection a s T z) y) y := by
  have h := lowerReflection_hasDerivAt a y T z
  rw [h.deriv]
  exact h.congr_of_eventuallyEq
    (Filter.mem_of_superset (Ioi_mem_nhds hy) (fun s hs => hReflection s hs))

theorem interval_deriv_bound_of_reflection
    (P : Measure BridgeNoise) [IsProbabilityMeasure P]
    (a y T z : ℝ) (hT : 0 < T) (hy : |y| < a) (hz : |z| < a)
    (hUpper : ∀ s : ℝ, s < a → upperCompletion P a s T z = upperReflection a s T z)
    (hLower : ∀ s : ℝ, -a < s → lowerCompletion P a s T z = lowerReflection a s T z)
    (hRegular : DifferentiableAt ℝ (fun s : ℝ => intervalCompletion P a s T z) y) :
    |deriv (fun s : ℝ => intervalCompletion P a s T z) y| ≤
      4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T) := by
  obtain ⟨hyl, hyu⟩ := abs_lt.mp hy
  obtain ⟨hzl, hzu⟩ := abs_lt.mp hz
  have hu := upperCompletion_hasDerivAt_of_reflection P a y T z hyu hUpper
  have hl := lowerCompletion_hasDerivAt_of_reflection P a y T z hyl hLower
  have hdom := signed_derivative_domination_of_hasDerivAt P a y T z _ _ _
    hu hRegular.hasDerivAt hl
  have hub := upperReflection_deriv_bound a y T z hT hyu hzu
  have hlb := lowerReflection_deriv_bound a y T z hT hyl hzl
  exact abs_le.mpr ⟨(abs_le.mp hub).1.trans hdom.1, hdom.2.trans (abs_le.mp hlb).2⟩

theorem interval_deriv_uniform_bound_of_reflection
    (P : Measure BridgeNoise) [IsProbabilityMeasure P]
    (a y T z H A : ℝ) (hH : 0 < H) (hHT : H ≤ T) (haA : a ≤ A)
    (hy : |y| < a) (hz : |z| < a)
    (hUpper : ∀ s : ℝ, s < a → upperCompletion P a s T z = upperReflection a s T z)
    (hLower : ∀ s : ℝ, -a < s → lowerCompletion P a s T z = lowerReflection a s T z)
    (hRegular : DifferentiableAt ℝ (fun s : ℝ => intervalCompletion P a s T z) y) :
    |deriv (fun s : ℝ => intervalCompletion P a s T z) y| ≤
      4 / Real.sqrt H * (1 + 2 * A / Real.sqrt H) := by
  have hT : 0 < T := hH.trans_le hHT
  have hsH : 0 < Real.sqrt H := Real.sqrt_pos.2 hH
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hs : Real.sqrt H ≤ Real.sqrt T := Real.sqrt_le_sqrt hHT
  obtain ⟨hyl, hyu⟩ := abs_lt.mp hy
  obtain ⟨hzl, hzu⟩ := abs_lt.mp hz
  have hd : |z - y| ≤ 2 * A := by
    apply abs_le.mpr
    constructor <;> linarith
  have h4 : (4 : ℝ) / Real.sqrt T ≤ 4 / Real.sqrt H :=
    div_le_div_of_nonneg_left (by norm_num) hsH hs
  have hdist : |z - y| / Real.sqrt T ≤ 2 * A / Real.sqrt H :=
    (div_le_div_of_nonneg_left (abs_nonneg _) hsH hs).trans
      ((div_le_div_iff_of_pos_right hsH).2 hd)
  refine (interval_deriv_bound_of_reflection P a y T z hT hy hz hUpper hLower hRegular).trans ?_
  exact mul_le_mul h4 (by linarith) (by positivity) (by positivity)

end Shao.C2.IntervalDerivativeBound
