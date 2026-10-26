import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace Shao.C2.OriginalMomentEnvelope
open Filter Topology

theorem original_moment_envelope_tendsto_zero
    (p moment sigma : ℝ) (hp : 2 < p) (hMoment : 0 ≤ moment) (hSigma : 0 < sigma)
    (b : ℕ → ℝ) (hb : ∀ n : ℕ, 0 ≤ b n)
    (hRate : Tendsto
      (fun n : ℕ => b n / Real.rpow (n : ℝ) ((p - 2) / (2 * p)))
      atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ => Real.rpow (1 + b n) p *
        (moment / (Real.rpow sigma p * Real.rpow (n : ℝ) ((p - 2) / 2))))
      atTop (𝓝 0) := by
  let alpha : ℝ := (p - 2) / (2 * p)
  have hp0 : 0 < p := by linarith only [hp]
  have hAlpha : 0 < alpha := by
    exact div_pos (sub_pos.mpr hp) (mul_pos (by norm_num) hp0)
  change Tendsto (fun n : ℕ => b n / Real.rpow (n : ℝ) alpha) atTop (𝓝 0) at hRate
  have hNat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hNeg := (tendsto_rpow_neg_atTop hAlpha).comp hNat
  have hInverse : Tendsto (fun n : ℕ => 1 / Real.rpow (n : ℝ) alpha)
      atTop (𝓝 0) := by
    refine hNeg.congr' (Filter.Eventually.of_forall fun n => ?_)
    simp only [Real.rpow_eq_pow, Function.comp_apply, Real.rpow_neg (Nat.cast_nonneg n), one_div]
  have hRatio : Tendsto (fun n : ℕ => (1 + b n) / Real.rpow (n : ℝ) alpha)
      atTop (𝓝 0) := by
    simpa only [add_div, zero_add] using hInverse.add hRate
  have hPower := hRatio.rpow_const_nhds_zero hp0
  have hTotal : Tendsto
      (fun n : ℕ => (moment / Real.rpow sigma p) *
        Real.rpow ((1 + b n) / Real.rpow (n : ℝ) alpha) p) atTop (𝓝 0) := by
    simpa only [Real.rpow_eq_pow, mul_zero] using hPower.const_mul (moment / Real.rpow sigma p)
  refine hTotal.congr' (Filter.Eventually.of_forall fun n => ?_)
  have hExponent : alpha * p = (p - 2) / 2 := by
    dsimp only [alpha]
    field_simp [hp0.ne']
    <;> ring
  have hDenominator : Real.rpow (Real.rpow (n : ℝ) alpha) p =
      Real.rpow (n : ℝ) ((p - 2) / 2) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul (Nat.cast_nonneg n), hExponent]
  simp only [Real.rpow_eq_pow] at hDenominator ⊢
  rw [Real.div_rpow (by linarith only [hb n])
    (Real.rpow_nonneg (Nat.cast_nonneg n) alpha) p, hDenominator]
  simp only [div_eq_mul_inv, mul_inv_rev]
  <;> ring

end Shao.C2.OriginalMomentEnvelope
