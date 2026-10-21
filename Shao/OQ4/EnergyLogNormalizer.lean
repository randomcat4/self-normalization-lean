import Shao.OQ4.TruncatedEnergy
import Shao.OQ4.IntervalConcentration
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Finite actual log-normalizer error with a T-only coefficient and explicit common threshold. -/

namespace Shao.OQ4

open MeasureTheory

noncomputable def energyLogThreshold (M T : ℝ) : ℝ :=
  2 * (1 + M + T + energyNormalizerErrorConstant T * M)

noncomputable def energyLogErrorConstant (T : ℝ) : ℝ :=
  energyNormalizerErrorConstant T + 4 * T ^ 2 + 4 * energyNormalizerErrorConstant T ^ 2

theorem energyLog_constants_nonneg (M T : ℝ) (hM : 0 ≤ M) (hT : 0 ≤ T) :
    0 ≤ energyLogThreshold M T ∧ 0 ≤ energyLogErrorConstant T := by
  have hC := energyNormalizerErrorConstant_nonneg T hT
  unfold energyLogThreshold energyLogErrorConstant
  constructor <;> positivity

theorem energyLog_threshold_bounds (M T : ℝ) (hM : 0 ≤ M) (hT : 0 ≤ T) :
    2 ≤ energyLogThreshold M T ∧ M ≤ energyLogThreshold M T ∧
      2 * (T + energyNormalizerErrorConstant T * M) ≤ energyLogThreshold M T := by
  have hp := mul_nonneg (energyNormalizerErrorConstant_nonneg T hT) hM
  unfold energyLogThreshold
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The actual expansion internally supplies integrability, the common height facts and positive Z. -/
theorem energyLog_normalizer_close (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (M T h s : ℝ) (hM : 0 ≤ M) (hT : 0 ≤ T) (hh : energyLogThreshold M T ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (hβM : (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M) :
    Integrable (energyWeight h s) ν ∧ 2 ≤ h ∧ (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M ∧ M ≤ h ∧
    |energyNormalizer ν h s - 1| ≤ T / h ^ 2 +
      energyNormalizerErrorConstant T * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 3 ∧
    |energyNormalizer ν h s - 1| ≤ (1 / 2 : ℝ) ∧
    ((1 / 2 : ℝ) ≤ energyNormalizer ν h s ∧ energyNormalizer ν h s ≤ (3 / 2 : ℝ)) ∧
    0 < energyNormalizer ν h s := by
  have hp := energyLog_threshold_bounds M T hM hT
  have hh2 : 2 ≤ h := hp.1.trans hh
  have hMh : M ≤ h := hp.2.1.trans hh
  have hA : 2 * (T + energyNormalizerErrorConstant T * M) ≤ h := hp.2.2.trans hh
  have hh0 : 0 < h := by linarith
  have hh1 : 1 ≤ h := by linarith
  have hC := energyNormalizerErrorConstant_nonneg T hT
  have hβ0 : 0 ≤ ∫ x : ℝ, |x| ^ 3 ∂ν := integral_nonneg fun x => pow_nonneg (abs_nonneg x) 3
  have hraw : |energyNormalizer ν h s - 1| ≤ T / h ^ 2 +
      energyNormalizerErrorConstant T * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 3 := by
    calc
      _ = |s / h ^ 2 + (energyNormalizer ν h s - 1 - s / h ^ 2)| := congrArg abs (by ring)
      _ ≤ |s / h ^ 2| + |energyNormalizer ν h s - 1 - s / h ^ 2| := abs_add_le _ _
      _ ≤ _ := add_le_add
        (by rw [abs_div, abs_of_nonneg (sq_nonneg h)]; exact div_le_div_of_nonneg_right hs (sq_nonneg h))
        (energyNormalizer_expansion ν T h s hT hh1 hs hSq hCube hsecond)
  have hp2 : h ≤ h ^ 2 := by nlinarith
  have hp3 : h ≤ h ^ 3 := by
    have ht := mul_nonneg hh0.le (show 0 ≤ h ^ 2 - 1 by nlinarith)
    nlinarith
  have hq : energyNormalizerErrorConstant T * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 3 ≤
      energyNormalizerErrorConstant T * M / h := by
    calc
      _ ≤ energyNormalizerErrorConstant T * M / h ^ 3 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hβM hC) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hC hM) hh0 hp3
  have hc : |energyNormalizer ν h s - 1| ≤ (1 / 2 : ℝ) := by
    calc
      _ ≤ T / h ^ 2 + energyNormalizerErrorConstant T * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 3 := hraw
      _ ≤ T / h + energyNormalizerErrorConstant T * M / h :=
        add_le_add (div_le_div_of_nonneg_left hT hh0 hp2) hq
      _ = (T + energyNormalizerErrorConstant T * M) / h := by ring
      _ ≤ 1 / 2 := (div_le_iff₀ hh0).2 (by linarith)
  have hbounds := abs_le.mp hc
  exact ⟨energyWeight_integrable ν T h s hT hh0 hs, hh2, hβM, hMh, hraw, hc,
    ⟨by linarith [hbounds.1], by linarith [hbounds.2]⟩, by linarith [hbounds.1]⟩

/-- No upper constraint z ≤ 1 is needed: both signs of the logarithm correction are covered. -/
theorem energyLog_quadratic_bound (z : ℝ) (hz : (1 / 2 : ℝ) ≤ z) :
    |Real.log z - (z - 1)| ≤ 2 * (z - 1) ^ 2 := by
  have hz0 : 0 < z := by linarith
  have hu := Real.log_le_sub_one_of_pos hz0
  have hl := Real.one_sub_inv_le_log_of_pos hz0
  calc
    _ = (z - 1) - Real.log z := by rw [abs_of_nonpos (by linarith)]; ring
    _ ≤ (z - 1) - (1 - z⁻¹) := by linarith
    _ = (z - 1) ^ 2 / z := by field_simp
    _ ≤ _ := by
      apply (div_le_iff₀ hz0).2
      have hp := mul_nonneg (sub_nonneg.mpr hz) (sq_nonneg (z - 1))
      nlinarith

theorem energyLog_square_payment (T C β h v : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hβ : 1 ≤ β) (hh : 1 ≤ h) (hβh : β ≤ h)
    (hv : |v| ≤ T / h ^ 2 + C * β / h ^ 3) :
    2 * v ^ 2 ≤ (4 * T ^ 2 + 4 * C ^ 2) * β / h ^ 3 := by
  have hh0 : 0 < h := by linarith
  have hβ0 : 0 ≤ β := by linarith
  have hab : 0 ≤ T / h ^ 2 + C * β / h ^ 3 := by positivity
  have hv2 := pow_le_pow_left₀ (abs_nonneg v) hv 2
  have hsq : 2 * v ^ 2 ≤ 4 * (T / h ^ 2) ^ 2 + 4 * (C * β / h ^ 3) ^ 2 := by
    nlinarith [sq_abs v, sq_nonneg (T / h ^ 2 - C * β / h ^ 3)]
  have hr1 : 1 / h ^ 4 ≤ β / h ^ 3 := by
    apply (div_le_div_iff₀ (pow_pos hh0 4) (pow_pos hh0 3)).2
    have hb : 1 ≤ β * h := by nlinarith
    have hp := mul_le_mul_of_nonneg_right hb (pow_nonneg hh0.le 3)
    nlinarith
  have hhh : h ≤ h ^ 3 := by
    have hp := mul_nonneg hh0.le (show 0 ≤ h ^ 2 - 1 by nlinarith)
    nlinarith
  have hr0 : 0 ≤ β / h ^ 3 := by positivity
  have hrle : β / h ^ 3 ≤ 1 := (div_le_iff₀ (pow_pos hh0 3)).2 (by linarith [hβh.trans hhh])
  have hr2 : β ^ 2 / h ^ 6 ≤ β / h ^ 3 := by
    calc
      _ = (β / h ^ 3) ^ 2 := by ring
      _ ≤ _ := by nlinarith
  calc
    _ ≤ 4 * (T / h ^ 2) ^ 2 + 4 * (C * β / h ^ 3) ^ 2 := hsq
    _ = 4 * T ^ 2 * (1 / h ^ 4) + 4 * C ^ 2 * (β ^ 2 / h ^ 6) := by ring
    _ ≤ 4 * T ^ 2 * (β / h ^ 3) + 4 * C ^ 2 * (β / h ^ 3) :=
      add_le_add (mul_le_mul_of_nonneg_left hr1 (by positivity))
        (mul_le_mul_of_nonneg_left hr2 (by positivity))
    _ = _ := by ring

/-- The finite actual log expansion, with no center/id or separate positivity/error premise. -/
theorem energyLog_normalizer_error (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (M T h s : ℝ) (hM : 0 ≤ M) (hT : 0 ≤ T) (hh : energyLogThreshold M T ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (hβM : (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M) :
    |Real.log (energyNormalizer ν h s) - s / h ^ 2| ≤
      energyLogErrorConstant T * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 3 := by
  obtain ⟨_hw, hh2, _hβM, hMh, hraw, _hc, hZbounds, _hZ⟩ :=
    energyLog_normalizer_close ν M T h s hM hT hh hs hSq hCube hsecond hβM
  have hh1 : 1 ≤ h := by linarith
  have hβ := third_absolute_moment_ge_one ν hSq hCube hsecond
  have hp := energyLog_square_payment T (energyNormalizerErrorConstant T)
    (∫ x : ℝ, |x| ^ 3 ∂ν) h (energyNormalizer ν h s - 1) hT
    (energyNormalizerErrorConstant_nonneg T hT) hβ hh1 (hβM.trans hMh) hraw
  calc
    _ = |(Real.log (energyNormalizer ν h s) - (energyNormalizer ν h s - 1)) +
        (energyNormalizer ν h s - 1 - s / h ^ 2)| := congrArg abs (by ring)
    _ ≤ |Real.log (energyNormalizer ν h s) - (energyNormalizer ν h s - 1)| +
        |energyNormalizer ν h s - 1 - s / h ^ 2| := abs_add_le _ _
    _ ≤ 2 * (energyNormalizer ν h s - 1) ^ 2 +
        energyNormalizerErrorConstant T * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 3 :=
      add_le_add (energyLog_quadratic_bound _ hZbounds.1)
        (energyNormalizer_expansion ν T h s hT hh1 hs hSq hCube hsecond)
    _ ≤ (4 * T ^ 2 + 4 * energyNormalizerErrorConstant T ^ 2) * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 3 +
        energyNormalizerErrorConstant T * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 3 := add_le_add hp le_rfl
    _ = _ := by unfold energyLogErrorConstant; ring

end Shao.OQ4
