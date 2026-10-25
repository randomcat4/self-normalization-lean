import Shao.OQ6.ConditionalUniformStandardizedResidual
import Shao.OQ6.ConditionalTrueProjectionCarrier

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Shao.OQ6.ConditionalResidualExponentialEnvelope

noncomputable section

open MeasureTheory ProbabilityTheory

theorem actual_conditional_residual_exponential_envelope
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun z : Ω × Ω => h z.1 z.2))
    (hh2 : MemLp (fun z : Ω × Ω => h z.1 z.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ z : Ω × Ω, h z.1 z.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (w : Ω → ℝ)
    (hw : Measurable w)
    (hwone : ∀ᵐ o ∂μ, 1 ≤ w o)
    (α τ : ℝ) (hα : 0 < α) (hτ : 0 < τ)
    (hwexp : Integrable (fun o => Real.exp (τ * Real.rpow (w o) α)) μ)
    (henvelope : ∀ᵐ z : Ω × Ω ∂(μ.prod μ),
      |h z.1 z.2 - (∫ y, h z.1 y ∂μ) - (∫ y, h z.2 y ∂μ)| ≤
        w z.1 * w z.2)
    (p : ℝ) (hp : 2 < p ∧ p ≤ 3)
    (hgp : Integrable
      (fun o => Real.rpow |∫ y, h o y ∂μ| p) μ) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let M : ℝ := ∫ o, w o ^ 2 ∂μ
    let W2 : ℝ := Real.sqrt M
    let Cenv : ℝ := 2 * (1 + 2 * W2) ^ 2
    let aenv : ℝ := Real.sqrt Cenv
    let wstd : Ω → ℝ := fun o => aenv * w o
    let tauStd : ℝ := τ / Real.rpow aenv α
    let Mexp : ℝ := ∫ o, Real.exp (τ * Real.rpow (w o) α) ∂μ
    1 ≤ aenv ∧ aenv ^ 2 = Cenv ∧ 0 < tauStd ∧ 1 ≤ Mexp ∧
      Measurable wstd ∧ MemLp wstd 2 μ ∧
      ∃ N0 : ℕ, 1 ≤ N0 ∧
      ∀ R : ℝ, (N0 : ℝ) ≤ R →
      let C : Set Ω := {o : Ω | w o ≤ R}
      let d : ℝ := μ.real C
      let ν : Measure Ω := (μ C)⁻¹ • μ.restrict C
      MeasurableSet C ∧ (1 / 2 : ℝ) ≤ d ∧
        IsProbabilityMeasure ν ∧ ν ≪ μ ∧ ν C = 1 ∧
        (∀ᵐ o ∂ν, 1 ≤ wstd o ∧ wstd o ≤ aenv * R) ∧
        MemLp wstd 2 ν ∧
        Integrable (fun o => Real.exp (tauStd * Real.rpow (wstd o) α)) ν ∧
        (∫ o, Real.exp (tauStd * Real.rpow (wstd o) α) ∂ν) =
          (∫ o in C, Real.exp (τ * Real.rpow (w o) α) ∂μ) / d ∧
        (∫ o, Real.exp (tauStd * Real.rpow (wstd o) α) ∂ν) ≤ 2 * Mexp ∧
        ∀ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 →
        let H : Ω → Ω → ℝ := fun o y => g o + g y + lam * r o y
        let κ : ℝ := ∫ z : Ω × Ω, H z.1 z.2 ∂(ν.prod ν)
        let G : Ω → ℝ := fun o => (∫ y, H o y ∂ν) - κ
        let σ2 : ℝ := ∫ o, G o ^ 2 ∂ν
        let σ : ℝ := Real.sqrt σ2
        let K : Ω → Ω → ℝ := fun o y => H o y - κ - G o - G y
        let Kstd : Ω → Ω → ℝ := fun o y => K o y / σ
        (∀ᵐ z : Ω × Ω ∂(ν.prod ν),
          |Kstd z.1 z.2| ≤ wstd z.1 * wstd z.2) ∧
        (∀ᵐ z : Ω × Ω ∂(ν.prod ν),
          |Kstd z.1 z.2| ≤ (aenv * R) ^ 2) := by
  classical
  have h181 : let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let M : ℝ := ∫ o, w o ^ 2 ∂μ
    let W2 : ℝ := Real.sqrt M
    let Cenv : ℝ := 2 * (1 + 2 * W2) ^ 2
    let RhoBound : ℝ := 4 * Cenv ^ 2 * M ^ 2
    MemLp w 2 μ ∧ Integrable (fun o => w o ^ 2) μ ∧
      1 ≤ M ∧ 1 ≤ W2 ∧ W2 ^ 2 = M ∧ 0 < Cenv ∧ 0 < RhoBound ∧
      ∃ N0 : ℕ, 1 ≤ N0 ∧
      ∀ R : ℝ, (N0 : ℝ) ≤ R →
      let C : Set Ω := {o : Ω | w o ≤ R}
      let d : ℝ := μ.real C
      let ν : Measure Ω := (μ C)⁻¹ • μ.restrict C
      let b : ℝ := ∫ o in Cᶜ, w o ∂μ
      let c : ℝ := b / d
      let Mν : ℝ := ∫ o, w o ^ 2 ∂ν
      MeasurableSet C ∧ (1 / 2 : ℝ) ≤ d ∧
        IsProbabilityMeasure ν ∧ ν ≪ μ ∧ (ν.prod ν) ≪ (μ.prod μ) ∧
        ν C = 1 ∧ (∀ᵐ o ∂ν, 1 ≤ w o ∧ w o ≤ R) ∧
        MemLp w 2 ν ∧ Integrable (fun o => w o ^ 2) ν ∧
        0 ≤ Mν ∧ Mν ≤ 2 * M ∧
        0 ≤ b ∧ b ≤ W2 ∧ 0 ≤ c ∧ c ≤ 2 * W2 ∧
        MemLp (fun z : Ω × Ω => w z.1 * w z.2) 2 (ν.prod ν) ∧
        Integrable (fun z : Ω × Ω => (w z.1 * w z.2) ^ 2) (ν.prod ν) ∧
        (∫ z : Ω × Ω, (w z.1 * w z.2) ^ 2 ∂(ν.prod ν)) = Mν ^ 2 ∧
        ∀ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 →
        let H : Ω → Ω → ℝ := fun o y => g o + g y + lam * r o y
        let κ : ℝ := ∫ z : Ω × Ω, H z.1 z.2 ∂(ν.prod ν)
        let G : Ω → ℝ := fun o => (∫ y, H o y ∂ν) - κ
        let σ2 : ℝ := ∫ o, G o ^ 2 ∂ν
        let σ : ℝ := Real.sqrt σ2
        let K : Ω → Ω → ℝ := fun o y => H o y - κ - G o - G y
        let Kstd : Ω → Ω → ℝ := fun o y => K o y / σ
        let ρ2 : ℝ := ∫ z : Ω × Ω, Kstd z.1 z.2 ^ 2 ∂(ν.prod ν)
        Measurable (fun z : Ω × Ω => H z.1 z.2) ∧
          MemLp (fun z : Ω × Ω => H z.1 z.2) 2 (ν.prod ν) ∧
          Measurable G ∧ MemLp G 2 ν ∧
          Integrable (fun o => G o ^ 2) ν ∧ (∫ o, G o ∂ν) = 0 ∧
          (1 / 2 : ℝ) ≤ σ2 ∧ σ2 ≤ (3 / 2 : ℝ) ∧
          (1 / 2 : ℝ) ≤ σ ∧ 0 < σ ∧ σ ^ 2 = σ2 ∧
          Measurable (fun z : Ω × Ω => K z.1 z.2) ∧
          MemLp (fun z : Ω × Ω => K z.1 z.2) 2 (ν.prod ν) ∧
          (∀ o y, K o y = K y o) ∧
          Measurable (fun z : Ω × Ω => Kstd z.1 z.2) ∧
          MemLp (fun z : Ω × Ω => Kstd z.1 z.2) 2 (ν.prod ν) ∧
          Integrable (fun z : Ω × Ω => Kstd z.1 z.2 ^ 2) (ν.prod ν) ∧
          (∀ o y, Kstd o y = Kstd y o) ∧
          (∀ᵐ o ∂ν, Integrable (Kstd o) ν ∧ (∫ y, Kstd o y ∂ν) = 0) ∧
          (∫ z : Ω × Ω, Kstd z.1 z.2 ∂(ν.prod ν)) = 0 ∧
          (∀ᵐ z : Ω × Ω ∂(ν.prod ν),
            |Kstd z.1 z.2| ≤ Cenv * w z.1 * w z.2) ∧
          (∀ᵐ z : Ω × Ω ∂(ν.prod ν), |Kstd z.1 z.2| ≤ Cenv * R ^ 2) ∧
          0 ≤ ρ2 ∧ ρ2 ≤ RhoBound := Shao.OQ6.ConditionalUniformStandardizedResidual.actual_conditional_uniform_standardized_residual μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone α τ hα hτ hwexp henvelope p hp hgp
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let M : ℝ := ∫ o, w o ^ 2 ∂μ
  let W2 : ℝ := Real.sqrt M
  let Cenv : ℝ := 2 * (1 + 2 * W2) ^ 2
  let aenv : ℝ := Real.sqrt Cenv
  let wstd : Ω → ℝ := fun o => aenv * w o
  let tauStd : ℝ := τ / Real.rpow aenv α
  let Mexp : ℝ := ∫ o, Real.exp (τ * Real.rpow (w o) α) ∂μ
  let F : Ω → ℝ := fun o => Real.exp (τ * Real.rpow (w o) α)
  let Fstd : Ω → ℝ := fun o => Real.exp (tauStd * Real.rpow (wstd o) α)
  have haenvNonneg : 0 ≤ aenv := Real.sqrt_nonneg Cenv
  have haenvSquare : aenv ^ 2 = Cenv := by
    exact Real.sq_sqrt (le_of_lt h181.2.2.2.2.2.1)
  have haenvOne : 1 ≤ aenv := by
    have hW2One : 1 ≤ W2 := h181.2.2.2.1
    by_contra hnot
    have haenvLt : aenv < 1 := lt_of_not_ge hnot
    have hProduct : 0 ≤ (1 - aenv) * aenv :=
      mul_nonneg (by linarith only [haenvLt]) haenvNonneg
    dsimp only [Cenv] at haenvSquare
    nlinarith [sq_nonneg W2]
  have haenvPos : 0 < aenv := by
    linarith only [haenvOne]
  have haenvPowPos : 0 < Real.rpow aenv α := Real.rpow_pos_of_pos haenvPos α
  have hTauStdPos : 0 < tauStd := by
    exact div_pos hτ haenvPowPos
  have hMexpOne : 1 ≤ Mexp := by
    have hFone : ∀ᵐ o ∂μ, (1 : ℝ) ≤ F o := by
      filter_upwards [hwone] with o hwo
      have hwoNonneg : 0 ≤ w o := by linarith only [hwo]
      exact Real.one_le_exp_iff.mpr
        (mul_nonneg (le_of_lt hτ) (Real.rpow_nonneg hwoNonneg α))
    have hIntegralLower : (∫ _ : Ω, (1 : ℝ) ∂μ) ≤ ∫ o, F o ∂μ :=
      integral_mono_ae (integrable_const (1 : ℝ)) hwexp hFone
    simpa only [integral_const, probReal_univ, one_smul] using hIntegralLower
  have hwstdMeas : Measurable wstd := hw.const_mul aenv
  have hwstd2μ : MemLp wstd 2 μ := h181.1.const_mul aenv
  have h181Threshold : ∃ N0 : ℕ, 1 ≤ N0 ∧
      ∀ R : ℝ, (N0 : ℝ) ≤ R →
      let C : Set Ω := {o : Ω | w o ≤ R}
      let d : ℝ := μ.real C
      let ν : Measure Ω := (μ C)⁻¹ • μ.restrict C
      let b : ℝ := ∫ o in Cᶜ, w o ∂μ
      let c : ℝ := b / d
      let Mν : ℝ := ∫ o, w o ^ 2 ∂ν
      MeasurableSet C ∧ (1 / 2 : ℝ) ≤ d ∧
        IsProbabilityMeasure ν ∧ ν ≪ μ ∧ (ν.prod ν) ≪ (μ.prod μ) ∧
        ν C = 1 ∧ (∀ᵐ o ∂ν, 1 ≤ w o ∧ w o ≤ R) ∧
        MemLp w 2 ν ∧ Integrable (fun o => w o ^ 2) ν ∧
        0 ≤ Mν ∧ Mν ≤ 2 * M ∧
        0 ≤ b ∧ b ≤ W2 ∧ 0 ≤ c ∧ c ≤ 2 * W2 ∧
        MemLp (fun z : Ω × Ω => w z.1 * w z.2) 2 (ν.prod ν) ∧
        Integrable (fun z : Ω × Ω => (w z.1 * w z.2) ^ 2) (ν.prod ν) ∧
        (∫ z : Ω × Ω, (w z.1 * w z.2) ^ 2 ∂(ν.prod ν)) = Mν ^ 2 ∧
        ∀ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 →
        let H : Ω → Ω → ℝ := fun o y => g o + g y + lam * r o y
        let κ : ℝ := ∫ z : Ω × Ω, H z.1 z.2 ∂(ν.prod ν)
        let G : Ω → ℝ := fun o => (∫ y, H o y ∂ν) - κ
        let σ2 : ℝ := ∫ o, G o ^ 2 ∂ν
        let σ : ℝ := Real.sqrt σ2
        let K : Ω → Ω → ℝ := fun o y => H o y - κ - G o - G y
        let Kstd : Ω → Ω → ℝ := fun o y => K o y / σ
        let ρ2 : ℝ := ∫ z : Ω × Ω, Kstd z.1 z.2 ^ 2 ∂(ν.prod ν)
        Measurable (fun z : Ω × Ω => H z.1 z.2) ∧
          MemLp (fun z : Ω × Ω => H z.1 z.2) 2 (ν.prod ν) ∧
          Measurable G ∧ MemLp G 2 ν ∧
          Integrable (fun o => G o ^ 2) ν ∧ (∫ o, G o ∂ν) = 0 ∧
          (1 / 2 : ℝ) ≤ σ2 ∧ σ2 ≤ (3 / 2 : ℝ) ∧
          (1 / 2 : ℝ) ≤ σ ∧ 0 < σ ∧ σ ^ 2 = σ2 ∧
          Measurable (fun z : Ω × Ω => K z.1 z.2) ∧
          MemLp (fun z : Ω × Ω => K z.1 z.2) 2 (ν.prod ν) ∧
          (∀ o y, K o y = K y o) ∧
          Measurable (fun z : Ω × Ω => Kstd z.1 z.2) ∧
          MemLp (fun z : Ω × Ω => Kstd z.1 z.2) 2 (ν.prod ν) ∧
          Integrable (fun z : Ω × Ω => Kstd z.1 z.2 ^ 2) (ν.prod ν) ∧
          (∀ o y, Kstd o y = Kstd y o) ∧
          (∀ᵐ o ∂ν, Integrable (Kstd o) ν ∧ (∫ y, Kstd o y ∂ν) = 0) ∧
          (∫ z : Ω × Ω, Kstd z.1 z.2 ∂(ν.prod ν)) = 0 ∧
          (∀ᵐ z : Ω × Ω ∂(ν.prod ν),
            |Kstd z.1 z.2| ≤ Cenv * w z.1 * w z.2) ∧
          (∀ᵐ z : Ω × Ω ∂(ν.prod ν), |Kstd z.1 z.2| ≤ Cenv * R ^ 2) ∧
          0 ≤ ρ2 ∧ ρ2 ≤ (4 * Cenv ^ 2 * M ^ 2) := h181.2.2.2.2.2.2.2
  let N0 : ℕ := Classical.choose h181Threshold
  have hN0Spec : 1 ≤ N0 ∧
      ∀ R : ℝ, (N0 : ℝ) ≤ R →
      let C : Set Ω := {o : Ω | w o ≤ R}
      let d : ℝ := μ.real C
      let ν : Measure Ω := (μ C)⁻¹ • μ.restrict C
      let b : ℝ := ∫ o in Cᶜ, w o ∂μ
      let c : ℝ := b / d
      let Mν : ℝ := ∫ o, w o ^ 2 ∂ν
      MeasurableSet C ∧ (1 / 2 : ℝ) ≤ d ∧
        IsProbabilityMeasure ν ∧ ν ≪ μ ∧ (ν.prod ν) ≪ (μ.prod μ) ∧
        ν C = 1 ∧ (∀ᵐ o ∂ν, 1 ≤ w o ∧ w o ≤ R) ∧
        MemLp w 2 ν ∧ Integrable (fun o => w o ^ 2) ν ∧
        0 ≤ Mν ∧ Mν ≤ 2 * M ∧
        0 ≤ b ∧ b ≤ W2 ∧ 0 ≤ c ∧ c ≤ 2 * W2 ∧
        MemLp (fun z : Ω × Ω => w z.1 * w z.2) 2 (ν.prod ν) ∧
        Integrable (fun z : Ω × Ω => (w z.1 * w z.2) ^ 2) (ν.prod ν) ∧
        (∫ z : Ω × Ω, (w z.1 * w z.2) ^ 2 ∂(ν.prod ν)) = Mν ^ 2 ∧
        ∀ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 →
        let H : Ω → Ω → ℝ := fun o y => g o + g y + lam * r o y
        let κ : ℝ := ∫ z : Ω × Ω, H z.1 z.2 ∂(ν.prod ν)
        let G : Ω → ℝ := fun o => (∫ y, H o y ∂ν) - κ
        let σ2 : ℝ := ∫ o, G o ^ 2 ∂ν
        let σ : ℝ := Real.sqrt σ2
        let K : Ω → Ω → ℝ := fun o y => H o y - κ - G o - G y
        let Kstd : Ω → Ω → ℝ := fun o y => K o y / σ
        let ρ2 : ℝ := ∫ z : Ω × Ω, Kstd z.1 z.2 ^ 2 ∂(ν.prod ν)
        Measurable (fun z : Ω × Ω => H z.1 z.2) ∧
          MemLp (fun z : Ω × Ω => H z.1 z.2) 2 (ν.prod ν) ∧
          Measurable G ∧ MemLp G 2 ν ∧
          Integrable (fun o => G o ^ 2) ν ∧ (∫ o, G o ∂ν) = 0 ∧
          (1 / 2 : ℝ) ≤ σ2 ∧ σ2 ≤ (3 / 2 : ℝ) ∧
          (1 / 2 : ℝ) ≤ σ ∧ 0 < σ ∧ σ ^ 2 = σ2 ∧
          Measurable (fun z : Ω × Ω => K z.1 z.2) ∧
          MemLp (fun z : Ω × Ω => K z.1 z.2) 2 (ν.prod ν) ∧
          (∀ o y, K o y = K y o) ∧
          Measurable (fun z : Ω × Ω => Kstd z.1 z.2) ∧
          MemLp (fun z : Ω × Ω => Kstd z.1 z.2) 2 (ν.prod ν) ∧
          Integrable (fun z : Ω × Ω => Kstd z.1 z.2 ^ 2) (ν.prod ν) ∧
          (∀ o y, Kstd o y = Kstd y o) ∧
          (∀ᵐ o ∂ν, Integrable (Kstd o) ν ∧ (∫ y, Kstd o y ∂ν) = 0) ∧
          (∫ z : Ω × Ω, Kstd z.1 z.2 ∂(ν.prod ν)) = 0 ∧
          (∀ᵐ z : Ω × Ω ∂(ν.prod ν),
            |Kstd z.1 z.2| ≤ Cenv * w z.1 * w z.2) ∧
          (∀ᵐ z : Ω × Ω ∂(ν.prod ν), |Kstd z.1 z.2| ≤ Cenv * R ^ 2) ∧
          0 ≤ ρ2 ∧ ρ2 ≤ (4 * Cenv ^ 2 * M ^ 2) := Classical.choose_spec h181Threshold
  refine ⟨haenvOne, haenvSquare, hTauStdPos, hMexpOne, hwstdMeas,
    hwstd2μ, N0, hN0Spec.1, ?_⟩
  intro R
  intro hR
  let C : Set Ω := {o : Ω | w o ≤ R}
  let d : ℝ := μ.real C
  let ν : Measure Ω := (μ C)⁻¹ • μ.restrict C
  have hC : MeasurableSet C := (hN0Spec.2 R hR).1
  have hd : (1 / 2 : ℝ) ≤ d := (hN0Spec.2 R hR).2.1
  have hνprob : IsProbabilityMeasure ν := (hN0Spec.2 R hR).2.2.1
  have hνac : ν ≪ μ := (hN0Spec.2 R hR).2.2.2.1
  have hνC : ν C = 1 := (hN0Spec.2 R hR).2.2.2.2.2.1
  have hwνBounds : ∀ᵐ o ∂ν, 1 ≤ w o ∧ w o ≤ R := (hN0Spec.2 R hR).2.2.2.2.2.2.1
  have hwν2 : MemLp w 2 ν := (hN0Spec.2 R hR).2.2.2.2.2.2.2.1
  have hcutoff : 0 < μ.real {o : Ω | w o ≤ R} := by
    change 0 < d
    linarith only [hd]
  have hLamZero : 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1 := by
    norm_num
  letI instν : IsProbabilityMeasure ν := hνprob
  have hcarrier : let N : ℕ := Nat.ceil (2 / α)
    let Aexp : ℝ := (N.factorial : ℝ) / τ ^ N
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let C : Set Ω := {o : Ω | w o ≤ R}
    let π : ℝ := μ.real Cᶜ
    let d : ℝ := μ.real C
    let ν : Measure Ω := (μ C)⁻¹ • μ.restrict C
    let b : ℝ := ∫ o in Cᶜ, w o ∂μ
    let c : ℝ := b / d
    let u : ℝ := ∫ o, g o ∂ν
    let a : Ω → ℝ := fun o => ∫ y, r o y ∂ν
    let θ : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ∂(ν.prod ν)
    let H : Ω → Ω → ℝ := fun o y => g o + g y + (0 : ℝ) * r o y
    let q : ℝ := ∫ z : Ω × Ω, H z.1 z.2 ∂(ν.prod ν)
    let G : Ω → ℝ := fun o => (∫ y, H o y ∂ν) - q
    let rC : Ω → Ω → ℝ := fun o y => r o y - a o - a y + θ
    let K : Ω → Ω → ℝ := fun o y => H o y - q - G o - G y
    0 < Aexp ∧
      (∀ t : ℝ, 1 ≤ t → t ^ 2 ≤ Aexp * Real.exp (τ * Real.rpow t α)) ∧
      MeasurableSet C ∧
      d = 1 - π ∧ 0 < d ∧ 0 ≤ π ∧ π < 1 ∧
      IsProbabilityMeasure ν ∧
      ν ≪ μ ∧ (ν.prod ν) ≪ (μ.prod μ) ∧ ν C = 1 ∧
      (∀ A : Set Ω, MeasurableSet A → ν.real A = μ.real (A ∩ C) / d) ∧
      (∀ f : Ω → ℝ, Integrable f μ →
        Integrable f ν ∧ (∫ o, f o ∂ν) = (∫ o in C, f o ∂μ) / d) ∧
      MemLp w 2 μ ∧ MemLp w 2 ν ∧
      (∫ o, w o ^ 2 ∂ν) ≤ (∫ o, w o ^ 2 ∂μ) / d ∧
      Measurable a ∧ MemLp a 2 μ ∧ MemLp a 2 ν ∧
      (∀ᵐ o ∂μ, Integrable (r o) μ ∧ Integrable (r o) ν ∧
        a o = -(∫ y in Cᶜ, r o y ∂μ) / d ∧ |a o| ≤ c * w o) ∧
      θ = (∫ o, a o ∂ν) ∧
      θ = (∫ z in Cᶜ ×ˢ Cᶜ, r z.1 z.2 ∂(μ.prod μ)) / d ^ 2 ∧
      |θ| ≤ b ^ 2 / d ^ 2 ∧
      Measurable (fun z : Ω × Ω => H z.1 z.2) ∧
      MemLp (fun z : Ω × Ω => H z.1 z.2) 2 (ν.prod ν) ∧
      q = 2 * u + (0 : ℝ) * θ ∧
      Measurable G ∧ MemLp G 2 ν ∧
      (∀ᵐ o ∂μ, Integrable (H o) ν ∧
        G o = g o - u + (0 : ℝ) * (a o - θ)) ∧
      (∫ o, G o ∂ν) = 0 ∧
      Measurable (fun z : Ω × Ω => rC z.1 z.2) ∧
      MemLp (fun z : Ω × Ω => rC z.1 z.2) 2 (ν.prod ν) ∧
      (∀ o y, rC o y = rC y o) ∧
      (∀ᵐ o ∂ν, (∫ y, rC o y ∂ν) = 0) ∧
      MemLp (fun z : Ω × Ω => K z.1 z.2) 2 (ν.prod ν) ∧
      (∀ᵐ z : Ω × Ω ∂(ν.prod ν), K z.1 z.2 = (0 : ℝ) * rC z.1 z.2) ∧
      (∀ᵐ o ∂ν, (∫ y, K o y ∂ν) = 0) ∧
      (∀ᵐ z : Ω × Ω ∂(μ.prod μ),
        |rC z.1 z.2| ≤ (w z.1 + c) * (w z.2 + c) ∧
        |(0 : ℝ) * rC z.1 z.2| ≤ (1 + c) ^ 2 * w z.1 * w z.2) ∧
      (∀ᵐ z : Ω × Ω ∂(ν.prod ν), |K z.1 z.2| ≤ (R + c) ^ 2) := Shao.OQ6.ConditionalTrueProjectionCarrier.actual_conditional_true_projection_carrier μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone α τ hα hτ hwexp henvelope R hcutoff 0 hLamZero
  have hνint : ∀ f : Ω → ℝ, Integrable f μ → Integrable f ν ∧ (∫ o, f o ∂ν) = (∫ o in C, f o ∂μ) / d := (hcarrier).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hFν : Integrable F ν ∧ (∫ o, F o ∂ν) = (∫ o in C, F o ∂μ) / d := hνint F hwexp
  have hScaleν : F =ᵐ[ν] Fstd := by
    filter_upwards [hwνBounds] with o hwo
    have hwoNonneg : 0 ≤ w o := by linarith only [hwo.1]
    change Real.exp (τ * Real.rpow (w o) α) =
      Real.exp (tauStd * Real.rpow (wstd o) α)
    congr 1
    dsimp only [tauStd, wstd]
    have hMulRpow : Real.rpow (aenv * w o) α =
        Real.rpow aenv α * Real.rpow (w o) α := by
      simpa only [Real.rpow_eq_pow] using
        (Real.mul_rpow (x := aenv) (y := w o) (z := α) haenvNonneg hwoNonneg)
    rw [hMulRpow]
    field_simp [ne_of_gt haenvPowPos] <;> ring
  have hFstdν : Integrable Fstd ν := hFν.1.congr hScaleν
  have hExpIdentity : (∫ o, Fstd o ∂ν) = (∫ o in C, F o ∂μ) / d := by
    calc
      (∫ o, Fstd o ∂ν) = ∫ o, F o ∂ν := (integral_congr_ae hScaleν).symm
      _ = (∫ o in C, F o ∂μ) / d := hFν.2
  have hExpBound : (∫ o, Fstd o ∂ν) ≤ 2 * Mexp := by
    have hdPos : 0 < d := by linarith only [hd]
    have hFnonneg : ∀ᵐ o ∂μ, 0 ≤ F o := by
      filter_upwards [] with o
      exact (Real.exp_pos _).le
    have hSetBound : (∫ o in C, F o ∂μ) ≤ Mexp :=
      setIntegral_le_integral hwexp hFnonneg
    have hMexpNonneg : 0 ≤ Mexp := by linarith only [hMexpOne]
    have hPayment : Mexp ≤ 2 * Mexp * d := by
      nlinarith [mul_nonneg hMexpNonneg (show 0 ≤ d - 1 / 2 by linarith only [hd])]
    rw [hExpIdentity]
    exact (div_le_iff₀ hdPos).2 (hSetBound.trans hPayment)
  have hwstdνBounds : ∀ᵐ o ∂ν, 1 ≤ wstd o ∧ wstd o ≤ aenv * R := by
    filter_upwards [hwνBounds] with o hwo
    change 1 ≤ aenv * w o ∧ aenv * w o ≤ aenv * R
    constructor
    · calc
        1 ≤ aenv := haenvOne
        _ = aenv * 1 := by ring
        _ ≤ aenv * w o := mul_le_mul_of_nonneg_left hwo.1 haenvNonneg
    · exact mul_le_mul_of_nonneg_left hwo.2 haenvNonneg
  have hwstd2ν : MemLp wstd 2 ν := hwν2.const_mul aenv
  refine ⟨hC, hd, hνprob, hνac, hνC, hwstdνBounds, hwstd2ν,
    hFstdν, hExpIdentity, hExpBound, ?_⟩
  intro lam
  intro hLam
  let H : Ω → Ω → ℝ := fun o y => g o + g y + lam * r o y
  let κ : ℝ := ∫ z : Ω × Ω, H z.1 z.2 ∂(ν.prod ν)
  let G : Ω → ℝ := fun o => (∫ y, H o y ∂ν) - κ
  let σ2 : ℝ := ∫ o, G o ^ 2 ∂ν
  let σ : ℝ := Real.sqrt σ2
  let K : Ω → Ω → ℝ := fun o y => H o y - κ - G o - G y
  let Kstd : Ω → Ω → ℝ := fun o y => K o y / σ
  have h181Envelope : ∀ᵐ z : Ω × Ω ∂(ν.prod ν), |Kstd z.1 z.2| ≤ Cenv * w z.1 * w z.2 := ((hN0Spec.2 R hR).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 lam hLam).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h181Cutoff : ∀ᵐ z : Ω × Ω ∂(ν.prod ν), |Kstd z.1 z.2| ≤ Cenv * R ^ 2 := ((hN0Spec.2 R hR).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 lam hLam).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  constructor
  · filter_upwards [h181Envelope] with z hz
    calc
      |Kstd z.1 z.2| ≤ Cenv * w z.1 * w z.2 := hz
      _ = wstd z.1 * wstd z.2 := by
        dsimp only [wstd]
        rw [← haenvSquare]
        ring
  · filter_upwards [h181Cutoff] with z hzCut
    calc
      |Kstd z.1 z.2| ≤ Cenv * R ^ 2 := hzCut
      _ = (aenv * R) ^ 2 := by
        rw [← haenvSquare]
        ring

end

end Shao.OQ6.ConditionalResidualExponentialEnvelope
