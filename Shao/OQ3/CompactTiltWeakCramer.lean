import Shao.OQ3.CharacteristicMeasureDomination
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Compact quadratic tilts preserve the actual weak Cramer bound

Source: current/oq3/proofs/r2/report.md 343–369.
Source SHA256: 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55.
Frozen U21a scope: b539efde780e8033134f2503dcfd8070a811fbae8db759814bc75d3c1829ea77.
-/

namespace Shao.OQ3
open MeasureTheory
open scoped ENNReal NNReal
noncomputable section

theorem exists_compact_tilted_weakCramer_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (u0 v0 beta c R : ℝ) (hc : 0 < c)
    (hWC : ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic (mu.tilted (fun x => u0 * x + v0 * x ^ 2)) xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) :
    let mu0 : Measure ℝ := mu.tilted (fun x => u0 * x + v0 * x ^ 2)
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ 0 < m ^ 2 * c / 2 ∧
      ∀ p ∈ K,
        (ENNReal.ofReal m • mu0 ≤
          mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) ∧
        (∀ xi eta : ℝ,
          m ^ 2 * (1 - ‖jointCharacteristic mu0 xi eta‖ ^ 2) ≤
            1 - ‖jointCharacteristic
              (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) xi eta‖ ^ 2) ∧
        ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
          ‖jointCharacteristic
            (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) xi eta‖ ≤
              1 - (m ^ 2 * c / 2) *
                Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta) := by
  obtain ⟨m0, hm0, hfamily⟩ :=
    exists_compact_quadratic_tilted_domination mu M hM hb K hK u0 v0
  let m : ℝ := min m0 1
  have hm : 0 < m := lt_min hm0 (by norm_num)
  have hm1 : m ≤ 1 := min_le_right _ _
  let mu0 : Measure ℝ := mu.tilted (fun x => u0 * x + v0 * x ^ 2)
  letI : IsProbabilityMeasure mu0 := isProbabilityMeasure_tilted
    (quadratic_exp_integrable_of_ae_abs_le mu M hM hb u0 v0)
  have hscaled : ENNReal.ofReal m • mu0 ≤ ENNReal.ofReal m0 • mu0 := by
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul (ENNReal.ofReal_le_ofReal (show m ≤ m0 from min_le_left _ _))
      (le_refl (mu0 A)) zero_le zero_le
  have hnewc : 0 < m ^ 2 * c / 2 :=
    div_pos (mul_pos (pow_pos hm 2) hc) (by norm_num)
  refine ⟨m, hm, hm1, hnewc, ?_⟩
  intro p hp
  let mup : Measure ℝ := mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
  letI : IsProbabilityMeasure mup := isProbabilityMeasure_tilted
    (quadratic_exp_integrable_of_ae_abs_le mu M hM hb p.1 p.2)
  have hlower : ENNReal.ofReal m • mu0 ≤ mup := hscaled.trans (hfamily p hp).1
  have hbound := (jointCharacteristic_norm_le_of_measure_lower mu0 mup m hm.le hlower).2
  refine ⟨hlower, ?_, ?_⟩
  · intro xi eta
    let a : ℝ := ‖jointCharacteristic mu0 xi eta‖
    let b : ℝ := ‖jointCharacteristic mup xi eta‖
    let A : ℝ := 1 - m * (1 - a)
    have ha : a ≤ 1 := jointCharacteristic_norm_le_one mu0 xi eta
    have hbnd : b ≤ A := hbound xi eta
    have hsq : b ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hbnd 2
    have hprod : 0 ≤ 2 * m * (1 - m) * (1 - a) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hm.le)
        (sub_nonneg.mpr hm1)) (sub_nonneg.mpr ha)
    have hid : 1 - A ^ 2 - m ^ 2 * (1 - a ^ 2) =
        2 * m * (1 - m) * (1 - a) := by
      dsimp [A]
      ring
    change m ^ 2 * (1 - a ^ 2) ≤ 1 - b ^ 2
    nlinarith only [hsq, hprod, hid]
  · intro xi eta hfreq
    let a : ℝ := ‖jointCharacteristic mu0 xi eta‖
    let b : ℝ := ‖jointCharacteristic mup xi eta‖
    let rho : ℝ := Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)
    have hrho : 0 ≤ rho := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hdelta : 0 ≤ c * rho := mul_nonneg hc.le hrho
    have hwa : a ≤ 1 - c * rho := hWC xi eta hfreq
    have hba : b ≤ 1 - m * (1 - a) := hbound xi eta
    have hmprod : 0 ≤ m * (1 - m) := mul_nonneg hm.le (sub_nonneg.mpr hm1)
    have hfac : m ^ 2 / 2 ≤ m := by nlinarith only [hmprod, hm.le]
    have hdelta_le := mul_le_mul_of_nonneg_right hfac hdelta
    have hgap : c * rho ≤ 1 - a := by linarith only [hwa]
    have hscaled_gap := mul_le_mul_of_nonneg_left hgap hm.le
    change b ≤ 1 - (m ^ 2 * c / 2) * rho
    nlinarith only [hba, hdelta_le, hscaled_gap]

end
end Shao.OQ3
