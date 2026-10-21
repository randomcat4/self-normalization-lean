import Shao.OQ4.ReflectedSurvival

/-! Explicit ordinary-sum BE and two original SP inputs supply actual finite kernel D8. -/

namespace Shao.OQ4

open MeasureTheory

/-- The actual third moment supplies β ≥ 1 and both existing probability predicates. -/
theorem spitzer_kernel_probability_inputs (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hSq : Integrable (fun y : ℝ => y ^ 2) ν)
    (hCube : Integrable (fun y : ℝ => |y| ^ 3) ν)
    (hsecond : (∫ y : ℝ, y ^ 2 ∂ν) = 1) (C_BE : ℝ) (hC : 0 ≤ C_BE)
    (hCDF : ∀ t : ℕ, 1 ≤ t → ∀ x : ℝ,
      |(Measure.pi (fun _ : Fin t => ν)).real
          {a | Shao.prefixSum a t / Real.sqrt (t : ℝ) ≤ x} - standardNormalCDF x| ≤
        C_BE * (∫ y : ℝ, |y| ^ 3 ∂ν) / Real.sqrt (t : ℝ))
    (hSP : ∀ L : ℝ, 0 < L → ∀ s : ℝ, 0 < s → s < 1 →
      laplaceG (maxLaplaceMean ν L) s = Real.exp (laplaceW (endpointLaplaceMean ν L) s))
    (hSPneg : ∀ L : ℝ, 0 < L → ∀ s : ℝ, 0 < s → s < 1 →
      laplaceG (maxLaplaceMean (reflectedLaw ν) L) s =
        Real.exp (laplaceW (endpointLaplaceMean (reflectedLaw ν) L) s)) :
    1 ≤ (∫ y : ℝ, |y| ^ 3 ∂ν) ∧
    0 ≤ Real.sqrt 2 * Real.exp (6 + 3 * C_BE) ∧ 0 ≤ 1 + 2 * C_BE ∧
    iidOneSidedSurvival ν (∫ y : ℝ, |y| ^ 3 ∂ν) (Real.sqrt 2 * Real.exp (6 + 3 * C_BE)) ∧
    iidIntervalConcentration ν (∫ y : ℝ, |y| ^ 3 ∂ν) (1 + 2 * C_BE) := by
  have hβ := third_absolute_moment_ge_one ν hSq hCube hsecond
  exact ⟨hβ, iid_survival_and_concentration_of_cdf_and_two_original_sp ν _ C_BE
    hβ hC hCDF hSP hSPneg⟩

/-- Actual measurable and row-integrable R3, and actual R4, with no block input assumed. -/
theorem spitzer_kernel_block_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (M h C_BE : ℝ) (hh3 : 3 ≤ h)
    (hId : Integrable (fun y : ℝ => y) ν)
    (hSq : Integrable (fun y : ℝ => y ^ 2) ν)
    (hCube : Integrable (fun y : ℝ => |y| ^ 3) ν)
    (hmean : (∫ y : ℝ, y ∂ν) = 0) (hsecond : (∫ y : ℝ, y ^ 2 ∂ν) = 1)
    (hM : 0 ≤ M) (hβM : (∫ y : ℝ, |y| ^ 3 ∂ν) ≤ M) (hC : 0 ≤ C_BE)
    (hCDF : ∀ t : ℕ, 1 ≤ t → ∀ x : ℝ,
      |(Measure.pi (fun _ : Fin t => ν)).real
          {a | Shao.prefixSum a t / Real.sqrt (t : ℝ) ≤ x} - standardNormalCDF x| ≤
        C_BE * (∫ y : ℝ, |y| ^ 3 ∂ν) / Real.sqrt (t : ℝ))
    (hSP : ∀ L : ℝ, 0 < L → ∀ s : ℝ, 0 < s → s < 1 →
      laplaceG (maxLaplaceMean ν L) s = Real.exp (laplaceW (endpointLaplaceMean ν L) s))
    (hSPneg : ∀ L : ℝ, 0 < L → ∀ s : ℝ, 0 < s → s < 1 →
      laplaceG (maxLaplaceMean (reflectedLaw ν) L) s =
        Real.exp (laplaceW (endpointLaplaceMean (reflectedLaw ν) L) s))
    (z : ℝ) (hz : |z| ≤ h) :
    let Cq : ℝ := 1 + 2 * C_BE
    let Cs : ℝ := Real.sqrt 2 * Real.exp (6 + 3 * C_BE)
    let Clayer : ℝ := 12 * Cq * Cs * M * (1 + M)
    let E : ℝ := Real.pi ^ 3 * M / 48 + 2 * Real.pi * Clayer * (1 + 2 * M)
    Measurable (fun w => |cosineResidual ν (Real.pi / (2 * h)) h w|) ∧
    Integrable (fun w => |cosineResidual ν (Real.pi / (2 * h)) h w|)
      (killedIterKernel ν h ⌊h ^ 2⌋₊ z) ∧
    killedAction ν h ⌊h ^ 2⌋₊ (fun w => |cosineResidual ν (Real.pi / (2 * h)) h w|) z ≤ E / h ^ 3 ∧
    killedMass ν h ⌊h ^ 2⌋₊ z ≤ (2 * Cs) * principalCosine h z + (2 * Cs * M) / h := by
  dsimp only
  obtain ⟨hβ, hCs, hCq, hS, hAC⟩ :=
    spitzer_kernel_probability_inputs ν hSq hCube hsecond C_BE hC hCDF hSP hSPneg
  have hr := killed_block_residual_bound ν M h (1 + 2 * C_BE)
    (Real.sqrt 2 * Real.exp (6 + 3 * C_BE)) hh3 hId hSq hCube hmean hsecond
    hM hβM hCq hCs hAC hS z hz
  refine ⟨continuous_abs.measurable.comp (principalResidual_measurable ν h), hr.1, ?_, ?_⟩
  · simpa only [killedResidualConstant, killedLayerConstant] using hr.2
  · exact killed_block_mass_bound ν h z _ M _ hh3 hz (by linarith) hM hβM hCs hS

/-- Explicit BE, the two original SP identities, moments and numerical smallness imply finite D8. -/
theorem spitzer_kernel_finite_absorption (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (M h C_BE : ℝ) (hh3 : 3 ≤ h)
    (hId : Integrable (fun y : ℝ => y) ν)
    (hSq : Integrable (fun y : ℝ => y ^ 2) ν)
    (hCube : Integrable (fun y : ℝ => |y| ^ 3) ν)
    (hmean : (∫ y : ℝ, y ∂ν) = 0) (hsecond : (∫ y : ℝ, y ^ 2 ∂ν) = 1)
    (hM : 0 ≤ M) (hβM : (∫ y : ℝ, |y| ^ 3 ∂ν) ≤ M) (hC : 0 ≤ C_BE)
    (hCDF : ∀ t : ℕ, 1 ≤ t → ∀ x : ℝ,
      |(Measure.pi (fun _ : Fin t => ν)).real
          {a | Shao.prefixSum a t / Real.sqrt (t : ℝ) ≤ x} - standardNormalCDF x| ≤
        C_BE * (∫ y : ℝ, |y| ^ 3 ∂ν) / Real.sqrt (t : ℝ))
    (hSP : ∀ L : ℝ, 0 < L → ∀ s : ℝ, 0 < s → s < 1 →
      laplaceG (maxLaplaceMean ν L) s = Real.exp (laplaceW (endpointLaplaceMean ν L) s))
    (hSPneg : ∀ L : ℝ, 0 < L → ∀ s : ℝ, 0 < s → s < 1 →
      laplaceG (maxLaplaceMean (reflectedLaw ν) L) s =
        Real.exp (laplaceW (endpointLaplaceMean (reflectedLaw ν) L) s))
    (hlarge : Real.pi * (1 + M) ≤ h) (N : ℕ) (hmN : ⌊h ^ 2⌋₊ ≤ N)
    (hsmall :
      let Cq : ℝ := 1 + 2 * C_BE
      let Cs : ℝ := Real.sqrt 2 * Real.exp (6 + 3 * C_BE)
      let Clayer : ℝ := 12 * Cq * Cs * M * (1 + M)
      let E : ℝ := Real.pi ^ 3 * M / 48 + 2 * Real.pi * Clayer * (1 + 2 * M)
      let R : ℝ := Real.exp (Real.pi ^ 2)
      ((2 * Cs) * R) * (E * R / h ^ 3) * (N : ℝ) + (2 * Cs * M) * R / h ≤ (1 / 2 : ℝ))
    (z : ℝ) (hz : |z| ≤ h) :
    let Cq : ℝ := 1 + 2 * C_BE
    let Cs : ℝ := Real.sqrt 2 * Real.exp (6 + 3 * C_BE)
    let Clayer : ℝ := 12 * Cq * Cs * M * (1 + M)
    let E : ℝ := Real.pi ^ 3 * M / 48 + 2 * Real.pi * Clayer * (1 + 2 * M)
    let R : ℝ := Real.exp (Real.pi ^ 2)
    let H : ℝ := 2 * (1 + (2 * Cs) * R) * R
    (∀ k, k ≤ N → 0 ≤ normalizedKernelMass ν h k z ∧ normalizedKernelMass ν h k z ≤ H) ∧
    (∀ k, ⌊h ^ 2⌋₊ ≤ k → k ≤ N →
      |normalizedKernelCosine ν h k z - normalizedKernelCosine ν h ⌊h ^ 2⌋₊ z| ≤
        (E * R / h ^ 3) * ((k - ⌊h ^ 2⌋₊ : ℕ) : ℝ) * H) := by
  obtain ⟨_hβ, hCs, hCq, hS, hAC⟩ :=
    spitzer_kernel_probability_inputs ν hSq hCube hsecond C_BE hC hCDF hSP hSPneg
  simpa only [killedResidualConstant, killedLayerConstant] using
    killed_block_finite_absorption ν M h (1 + 2 * C_BE)
      (Real.sqrt 2 * Real.exp (6 + 3 * C_BE)) hh3 hId hSq hCube hmean hsecond
      hM hβM hCq hCs hAC hS hlarge N hmN hsmall z hz

end Shao.OQ4
