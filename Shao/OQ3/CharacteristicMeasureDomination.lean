import Shao.OQ3.FiniteFarArc
import Shao.OQ3.CompactTiltDomination
import Mathlib.MeasureTheory.Measure.Sub

namespace Shao.OQ3

open MeasureTheory

noncomputable section

private theorem jointPhase_integrable_finite (mu : Measure ℝ) [IsFiniteMeasure mu]
    (xi eta : ℝ) : Integrable (jointPhase xi eta) mu := by
  have hf : Continuous (jointPhase xi eta) := by unfold jointPhase; fun_prop
  apply Integrable.of_bound hf.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun x => (jointPhase_norm xi eta x).le

theorem jointCharacteristic_norm_le_of_measure_lower (mu nu : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (m : ℝ) (hm : 0 ≤ m)
    (hlower : ENNReal.ofReal m • mu ≤ nu) :
    m ≤ 1 ∧ ∀ xi eta : ℝ,
      ‖jointCharacteristic nu xi eta‖ ≤
        1 - m * (1 - ‖jointCharacteristic mu xi eta‖) := by
  let lambda : Measure ℝ := ENNReal.ofReal m • mu
  let : IsFiniteMeasure lambda := Measure.smul_finite mu ENNReal.ofReal_ne_top
  let rho : Measure ℝ := nu - lambda
  have hdecomp : rho + lambda = nu := Measure.sub_add_cancel_of_le hlower
  have hscaled : lambda.real Set.univ = m := by
    simp only [lambda, measureReal_def, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one, ENNReal.toReal_ofReal hm]
  have hmassadd : rho.real Set.univ + m = 1 := by
    calc
      rho.real Set.univ + m = rho.real Set.univ + lambda.real Set.univ := by rw [hscaled]
      _ = (rho + lambda).real Set.univ :=
        (measureReal_add_apply (measure_ne_top rho _) (measure_ne_top lambda _)).symm
      _ = 1 := by rw [hdecomp]; simp [measureReal_def]
  have hm1 : m ≤ 1 := by
    have hnonneg : 0 ≤ rho.real Set.univ := ENNReal.toReal_nonneg
    linarith only [hmassadd, hnonneg]
  have hmass : rho.real Set.univ = 1 - m := by linarith only [hmassadd]
  refine ⟨hm1, ?_⟩
  intro xi eta
  have hI_rho := jointPhase_integrable_finite rho xi eta
  have hI_scaled : Integrable (jointPhase xi eta) lambda :=
    (integrable_jointPhase mu xi eta).smul_measure ENNReal.ofReal_ne_top
  have hsplit : jointCharacteristic nu xi eta =
      (∫ x : ℝ, jointPhase xi eta x ∂rho) + m • jointCharacteristic mu xi eta := by
    unfold jointCharacteristic
    rw [← hdecomp, integral_add_measure hI_rho hI_scaled,
      show lambda = ENNReal.ofReal m • mu from rfl, integral_smul_measure,
      ENNReal.toReal_ofReal hm]
  have hresnorm : ‖∫ x : ℝ, jointPhase xi eta x ∂rho‖ ≤ 1 - m := by
    have hh := norm_integral_le_of_norm_le_const (μ := rho) (f := jointPhase xi eta)
      (C := 1) (Filter.Eventually.of_forall fun x => (jointPhase_norm xi eta x).le)
    simpa only [one_mul, hmass] using hh
  rw [hsplit]
  calc
    ‖(∫ x : ℝ, jointPhase xi eta x ∂rho) + m • jointCharacteristic mu xi eta‖ ≤
        ‖∫ x : ℝ, jointPhase xi eta x ∂rho‖ + ‖m • jointCharacteristic mu xi eta‖ := norm_add_le _ _
    _ = ‖∫ x : ℝ, jointPhase xi eta x ∂rho‖ + m * ‖jointCharacteristic mu xi eta‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hm]
    _ ≤ (1 - m) + m * ‖jointCharacteristic mu xi eta‖ := add_le_add hresnorm (le_refl _)
    _ = 1 - m * (1 - ‖jointCharacteristic mu xi eta‖) := by ring

theorem exists_compact_tilted_characteristic_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (K : Set (ℝ × ℝ)) (hK : IsCompact K) (u0 v0 : ℝ) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ ∀ p ∈ K, ∀ xi eta : ℝ,
      ‖jointCharacteristic (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) xi eta‖ ≤
        1 - m * (1 -
          ‖jointCharacteristic (mu.tilted (fun x => u0 * x + v0 * x ^ 2)) xi eta‖) := by
  obtain ⟨m0, hm0, hfamily⟩ := exists_compact_quadratic_tilted_domination mu M hM hb K hK u0 v0
  let m : ℝ := min m0 1
  have hm : 0 < m := lt_min hm0 (by norm_num)
  let mu0 := mu.tilted (fun x => u0 * x + v0 * x ^ 2)
  let : IsProbabilityMeasure mu0 := isProbabilityMeasure_tilted
    (quadratic_exp_integrable_of_ae_abs_le mu M hM hb u0 v0)
  have hscaled : ENNReal.ofReal m • mu0 ≤ ENNReal.ofReal m0 • mu0 := by
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul (ENNReal.ofReal_le_ofReal (show m ≤ m0 from min_le_left _ _))
      (le_refl (mu0 A)) zero_le zero_le
  refine ⟨m, hm, min_le_right _ _, ?_⟩
  intro p hp xi eta
  let mu1 := mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
  let : IsProbabilityMeasure mu1 := isProbabilityMeasure_tilted
    (quadratic_exp_integrable_of_ae_abs_le mu M hM hb p.1 p.2)
  have hdom : ENNReal.ofReal m • mu0 ≤ mu1 := hscaled.trans (hfamily p hp).1
  exact (jointCharacteristic_norm_le_of_measure_lower mu0 mu1 m hm.le hdom).2 xi eta

end
end Shao.OQ3
