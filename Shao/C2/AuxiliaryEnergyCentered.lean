import Shao.C2.AuxiliaryEnergyMoments

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.C2.AuxiliaryEnergyCentered
open MeasureTheory ProbabilityTheory

theorem auxiliary_absolute_third_moment_ge_one
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1) :
    1 ≤ ∫ z : ℝ, |z| ^ 3 ∂nu := by
  have hPoint (z : ℝ) : 3 * z ^ 2 ≤ 1 + 2 * |z| ^ 3 := by
    have hh := mul_nonneg (sq_nonneg (|z| - 1))
      (show 0 ≤ 2 * |z| + 1 by positivity)
    nlinarith [sq_abs z]
  have hh := integral_mono (h2.const_mul 3)
    ((integrable_const (1 : ℝ)).add (h3.const_mul 2)) hPoint
  simp only [Pi.add_apply] at hh
  rw [integral_const_mul, integral_add (integrable_const _) (h3.const_mul 2),
    integral_const_mul, hnorm] at hh
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
  linarith

theorem auxiliary_energy_tilt_small_parameter
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (s : ℝ) (hs : 0 ≤ s)
    (hsmall : s * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2 ≤ 1 / 128) :
    let rho : Measure ℝ := nu.tilted (fun z => -s * z ^ 2)
    let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
    let mu : ℝ := ∫ z : ℝ, z ∂rho
    IsProbabilityMeasure rho ∧
      Integrable (id : ℝ → ℝ) rho ∧
      Integrable (fun z : ℝ => z - mu) rho ∧
      (∫ z : ℝ, z - mu ∂rho) = 0 ∧
      Integrable (fun z : ℝ => (z - mu) ^ 2) rho ∧
      Integrable (fun z : ℝ => |z - mu| ^ 3) rho ∧
      |mu| ≤ 2 * s * beta ∧
      1 / 2 ≤ variance (id : ℝ → ℝ) rho ∧
      variance (id : ℝ → ℝ) rho ≤ 2 ∧
      (∫ z : ℝ, |z - mu| ^ 3 ∂rho) ≤ 12 * beta := by
  intro rho beta mu
  rcases Shao.C2.AuxiliaryEnergyTilt.auxiliary_energy_tilt_normalizer_and_drift
      nu h2 h3 hmean hnorm s hs with
    ⟨_hV, _hZpos, _hZlower, _hZle, hRho, hId, hDrift⟩
  rcases Shao.C2.AuxiliaryEnergyMoments.auxiliary_energy_tilt_moments_and_variance
      nu h2 h3 hmean hnorm s hs with
    ⟨_hRho, h2Rho, h3Rho, _h2lower, _h2upper, h3upper, _hVar, hVarLower, hVarUpper⟩
  letI : IsProbabilityMeasure rho := hRho
  have hBeta : 1 ≤ beta := auxiliary_absolute_third_moment_ge_one nu h2 h3 hnorm
  have hBeta0 : 0 ≤ beta := zero_le_one.trans hBeta
  have hBeta2 : 1 ≤ beta ^ 2 := by nlinarith
  change s * beta ^ 2 ≤ 1 / 128 at hsmall
  have hsBound : s ≤ 1 / 128 := by
    have hh := mul_nonneg hs (sub_nonneg.mpr hBeta2)
    nlinarith
  have hExp : Real.exp s ≤ 2 := by
    calc
      Real.exp s ≤ 1 / (1 - s) :=
        Real.exp_bound_div_one_sub_of_interval hs (by linarith)
      _ ≤ 2 := (div_le_iff₀ (by linarith : 0 < 1 - s)).2 (by linarith)
  have hSqrt : Real.sqrt s * beta ≤ 1 / 8 := by
    have ht0 : 0 ≤ Real.sqrt s * beta := mul_nonneg (Real.sqrt_nonneg _) hBeta0
    have hh : (Real.sqrt s * beta) ^ 2 ≤ 1 / 128 := by
      rwa [mul_pow, Real.sq_sqrt hs]
    nlinarith
  have hsBeta : s * beta ≤ 1 / 128 := by
    have hh := mul_nonneg (mul_nonneg hs hBeta0) (sub_nonneg.mpr hBeta)
    nlinarith
  let D := s * Real.exp s * beta
  have hD0 : 0 ≤ D := mul_nonneg (mul_nonneg hs (Real.exp_pos _).le) hBeta0
  have hD : D ≤ 2 * s * beta := by
    calc
      D = Real.exp s * (s * beta) := by dsimp [D]; ring
      _ ≤ 2 * (s * beta) := mul_le_mul_of_nonneg_right hExp (mul_nonneg hs hBeta0)
      _ = _ := by ring
  have hDsmall : D ≤ 1 / 64 := by linarith
  have hDsq : D ^ 2 ≤ (1 / 64 : ℝ) ^ 2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hDsmall)
      (show 0 ≤ 1 / 64 + D by linarith)
    nlinarith
  have hMu : |mu| ≤ D := hDrift
  have hMean : |mu| ≤ 2 * s * beta := hMu.trans hD
  have hMuSmall : |mu| ≤ 1 / 64 := hMu.trans hDsmall
  have hVarianceLower : 1 / 2 ≤ variance (id : ℝ → ℝ) rho := by
    change 1 - Real.sqrt s * beta - D ^ 2 ≤ _ at hVarLower
    linarith
  have hVarianceUpper : variance (id : ℝ → ℝ) rho ≤ 2 := hVarUpper.trans hExp
  have hMuCube : |mu| ^ 3 ≤ beta := by
    calc
      |mu| ^ 3 ≤ (1 : ℝ) ^ 3 :=
        pow_le_pow_left₀ (abs_nonneg mu) (by linarith : |mu| ≤ 1) 3
      _ = 1 := by norm_num
      _ ≤ beta := hBeta
  have hCubePoint (z : ℝ) : |z - mu| ^ 3 ≤ 4 * (|z| ^ 3 + |mu| ^ 3) := by
    have hAbs : |z - mu| ≤ |z| + |mu| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le z mu
    have hp := pow_le_pow_left₀ (abs_nonneg (z - mu)) hAbs 3
    have hh := mul_nonneg (add_nonneg (abs_nonneg z) (abs_nonneg mu))
      (sq_nonneg (|z| - |mu|))
    nlinarith
  have hEnvelope : Integrable (fun z : ℝ => 4 * (|z| ^ 3 + |mu| ^ 3)) rho :=
    (h3Rho.add (integrable_const _)).const_mul 4
  have hCenterCube : Integrable (fun z : ℝ => |z - mu| ^ 3) rho :=
    hEnvelope.mono' (by fun_prop) (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg (z - mu)) 3)]
      exact hCubePoint z)
  have hThird : (∫ z : ℝ, |z - mu| ^ 3 ∂rho) ≤ 12 * beta := by
    calc
      (∫ z : ℝ, |z - mu| ^ 3 ∂rho) ≤
          ∫ z : ℝ, 4 * (|z| ^ 3 + |mu| ^ 3) ∂rho :=
        integral_mono hCenterCube hEnvelope hCubePoint
      _ = 4 * ((∫ z : ℝ, |z| ^ 3 ∂rho) + |mu| ^ 3) := by
        rw [integral_const_mul, integral_add h3Rho (integrable_const _)]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
        rfl
      _ ≤ 12 * beta := by
        have hh : (∫ z : ℝ, |z| ^ 3 ∂rho) ≤ 2 * beta :=
          h3upper.trans (mul_le_mul_of_nonneg_right hExp hBeta0)
        linarith
  have hCentered : Integrable (fun z : ℝ => z - mu) rho :=
    hId.sub (integrable_const _)
  have hZero : (∫ z : ℝ, z - mu ∂rho) = 0 := by
    rw [integral_sub (show Integrable (fun z : ℝ => z) rho from hId)
      (integrable_const mu)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    change mu - mu = 0
    ring
  have hL2 : MemLp (id : ℝ → ℝ) 2 rho :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 h2Rho
  have hCenteredSquare : Integrable (fun z : ℝ => (z - mu) ^ 2) rho :=
    (hL2.sub (memLp_const mu)).integrable_sq
  exact ⟨hRho, hId, hCentered, hZero, hCenteredSquare, hCenterCube,
    hMean, hVarianceLower, hVarianceUpper, hThird⟩

end Shao.C2.AuxiliaryEnergyCentered
