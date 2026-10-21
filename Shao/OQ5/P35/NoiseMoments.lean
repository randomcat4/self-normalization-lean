import Shao.OQ5.P35.RealLaw
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Continuous noise moments for the fixed p35 law

Source: `current/oq56/inputs02/p35.md`, §3. The noise law is normalized
Lebesgue measure on [-1,1]. This module proves only its bounded absolute
moments, zero mean and exact second moment; it asserts no category moments.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

open MeasureTheory

noncomputable section

private theorem integrable_noiseLaw_of_continuous {f : ℝ → ℝ}
    (hf : Continuous f) : Integrable f noiseLaw := by
  have hi : Integrable f (volume.restrict (Set.Icc (-1 : ℝ) 1)) :=
    hf.integrableOn_Icc
  unfold noiseLaw ProbabilityTheory.cond
  exact hi.smul_measure (by rw [Real.volume_Icc]; norm_num)

private theorem integral_noiseLaw_eq_interval (f : ℝ → ℝ) :
    (∫ a, f a ∂noiseLaw) =
      (1 / 2 : ℝ) * ∫ a in (-1 : ℝ)..1, f a := by
  unfold noiseLaw ProbabilityTheory.cond
  rw [integral_smul_measure, Real.volume_Icc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  norm_num [smul_eq_mul]

theorem integrable_noiseLaw_abs_pow (r : ℕ) (hr : r ≤ 3) :
    Integrable (fun a : ℝ => |a| ^ r) noiseLaw := by
  have hc : Continuous (fun a : ℝ => |a| ^ (min r 3)) :=
    continuous_id.abs.pow (min r 3)
  simpa only [Nat.min_eq_left hr] using integrable_noiseLaw_of_continuous hc

theorem integrable_noiseLaw_id : Integrable (fun a : ℝ => a) noiseLaw :=
  integrable_noiseLaw_of_continuous continuous_id

theorem integral_noiseLaw_id : (∫ a : ℝ, a ∂noiseLaw) = 0 := by
  have hderiv (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
    convert (((hasDerivAt_id' x).pow 2).div_const 2) using 1
    norm_num
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (-1 : ℝ)) (b := 1) (fun x _ => hderiv x)
    (continuous_id.intervalIntegrable (-1 : ℝ) 1)
  norm_num at hi
  rw [integral_noiseLaw_eq_interval, hi]
  norm_num

theorem integrable_noiseLaw_sq :
    Integrable (fun a : ℝ => a ^ 2) noiseLaw :=
  integrable_noiseLaw_of_continuous (continuous_id.pow 2)

theorem integral_noiseLaw_sq :
    (∫ a : ℝ, a ^ 2 ∂noiseLaw) = (1 / 3 : ℝ) := by
  have hderiv (x : ℝ) :
      HasDerivAt (fun y : ℝ => y ^ 3 / 3) (x ^ 2) x := by
    convert (((hasDerivAt_id' x).pow 3).div_const 3) using 1
    norm_num
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (-1 : ℝ)) (b := 1) (fun x _ => hderiv x)
    ((continuous_id.pow 2).intervalIntegrable (-1 : ℝ) 1)
  norm_num at hi
  rw [integral_noiseLaw_eq_interval, hi]
  norm_num

end
end Shao.OQ5.P35
