import Shao.OQ6.OriginalLogarithmicConditionalFullWindowUncenteredPhysicalTail
import Shao.OQ5.P41.FixedMaskConditionalBackgroundPhysicalTail

set_option autoImplicit false

universe u

open MeasureTheory
open scoped ENNReal NNReal BigOperators Classical
open Shao.OQ5.P41.FiniteBackgroundPerturbation (backgroundScale)
open Shao.OQ5.P41.FiniteBackgroundPhysicalTransport
  (backgroundSample scaledResidual physicalStatistic)
open Shao.OQ5.P41.FixedMaskConditionalBackgroundPhysicalTail
  (fixedMaskEvent backgroundClosedTail originalBackgroundClosedTail)

namespace Shao.OQ6.OriginalLogarithmicFixedMaskBackgroundFullWindowPhysicalTail

noncomputable section

theorem background_physicalStatistic_eq_Tuncenter
    {n : ℕ} {Ω : Type u}
    (B : Finset (Fin n)) (g : Ω → ℝ) (r : Ω → Ω → ℝ) :
    let m : ℕ := B.card
    let H : Ω → Ω → ℝ :=
      fun o y => g o + g y + backgroundScale B * r o y
    let sampleH : (Fin m → Ω) → Fin m → Fin m → ℝ :=
      fun ζ i j => H (ζ i) (ζ j)
    let U : (Fin m → Ω) → ℝ :=
      fun ζ => Shao.OQ6.FiniteRows.uStatistic (sampleH ζ)
    let RH : (Fin m → Ω) → ℝ :=
      fun ζ => Real.sqrt (Shao.OQ6.FiniteRows.jackknifeSq (sampleH ζ))
    let Tuncenter : (Fin m → Ω) → ℝ := fun ζ =>
      if RH ζ = 0 then 0 else Real.sqrt (m : ℝ) * U ζ / RH ζ
    ∀ ζ : Fin m → Ω,
      physicalStatistic m g (scaledResidual B r) ζ = Tuncenter ζ
:= by
  classical
  intro m H sampleH U RH Tuncenter ζ
  rfl

theorem actual_original_logarithmic_fixed_mask_background_full_window_physical_tail
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun z : Ω × Ω => h z.1 z.2))
    (hh2 : MemLp (fun z : Ω × Ω => h z.1 z.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ z : Ω × Ω, h z.1 z.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond : (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (w : Ω → ℝ) (hw : Measurable w)
    (hwone : ∀ᵐ o ∂μ, 1 ≤ w o)
    (α τ : ℝ) (hα : 0 < α) (hτ : 0 < τ)
    (hwexp : Integrable (fun o => Real.exp (τ * Real.rpow (w o) α)) μ)
    (henvelope : ∀ᵐ z : Ω × Ω ∂(μ.prod μ),
      |h z.1 z.2 - (∫ y, h z.1 y ∂μ) - (∫ y, h z.2 y ∂μ)| ≤
        w z.1 * w z.2)
    (p : ℝ) (hp : 2 < p ∧ p ≤ 3)
    (hgp : Integrable (fun o => Real.rpow |∫ y, h o y ∂μ| p) μ)
    (J : ℝ) (hJ : (1 / 2 : ℝ) ≤ J)
    (cSZ C1 C2 C3 C4 : ℝ)
    (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
      cSZ C1 C2 C3 C4)
    (CCDF : ℝ)
    (hSZC : Shao.OQ6.NormalizedIntegrableCDFAssembly.ScalarShaoZhouFiniteCostCDFInput.{u} CCDF)
    (t0 : ℝ) (ht0 : 0 < t0) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
    let A : ℝ := 2 * (J + 1) / (1 - 2 / p)
    let qpow : ℝ := (p - 2) / (2 * p)
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
      ∃ N : ℕ, 8 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
      let Rn : ℝ := Real.rpow (A * Real.log (n : ℝ) / τ) (1 / α)
      let Cn : Set Ω := {o : Ω | w o ≤ Rn}
      let dn : ℝ := μ.real Cn
      let νn : Measure Ω := (μ Cn)⁻¹ • μ.restrict Cn
      let Pn : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
      (2 : ℝ) ≤ c * Real.rpow (n : ℝ) qpow ∧
        MeasurableSet Cn ∧ (1 / 2 : ℝ) ≤ dn ∧ IsProbabilityMeasure νn ∧
        ∀ (B : Finset (Fin n)) (e : Fin B.card ≃ {i : Fin n // i ∈ B}),
          n ≤ 2 * B.card → B.card ≤ n →
          let E : Set (Fin n → Ω) := fixedMaskEvent Cn B
          let P : Measure (Fin B.card → Ω) := Measure.pi (fun _ : Fin B.card => νn)
          4 ≤ B.card ∧
            0 ≤ backgroundScale B ∧ backgroundScale B ≤ 1 ∧
            Pn.real E = dn ^ B.card * (1 - dn) ^ (n - B.card) ∧
            ∀ z : ℝ, 1 ≤ z → z ≤ c * Real.rpow (n : ℝ) qpow →
              Pn.real (originalBackgroundClosedTail B g r z ∩ E) =
                Pn.real E * P.real (backgroundClosedTail B g r z) ∧
              |Pn.real (originalBackgroundClosedTail B g r z ∩ E) /
                  Shao.standardNormalTail z - Pn.real E| ≤
                Pn.real E * K * (β * Real.rpow (1 + z) p *
                  Real.rpow (n : ℝ) (-((p - 2) / 2)) +
                  (1 + z) ^ 3 / Real.sqrt (n : ℝ))
:= by
  classical
  intro g r β A qpow
  have hg : Measurable g :=
    hh.stronglyMeasurable.integral_prod_right'.measurable
  have hr : Measurable (Function.uncurry r) := by
    change Measurable (fun z : Ω × Ω => h z.1 z.2 - g z.1 - g z.2)
    exact (hh.sub (hg.comp measurable_fst)).sub (hg.comp measurable_snd)
  have hrsym : ∀ a b : Ω, r a b = r b a := by
    intro a b
    dsimp only [r]
    rw [hhsymm a b]
    ring
  rcases Shao.OQ6.OriginalLogarithmicConditionalFullWindowUncenteredPhysicalTail.actual_original_logarithmic_conditional_full_window_uncentered_physical_tail
      μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone α τ hα hτ
      hwexp henvelope p hp hgp J hJ cSZ C1 C2 C3 C4 hSZ CCDF hSZC t0 ht0 with
    ⟨_, _, _, c, K, hc, hK, N, hN8, hAll⟩
  refine ⟨c, K, hc, hK, N, hN8, ?_⟩
  intro n hn Rn Cn dn νn Pn
  rcases hAll n hn with ⟨hWindow, hCn, hdn, hνn, _, _, hLams⟩
  have hn8 : 8 ≤ n := hN8.trans hn
  refine ⟨hWindow, hCn, hdn, hνn, ?_⟩
  intro B e hhalf hcard E P
  have hm4 : 4 ≤ B.card :=
    Shao.OQ5.P41.FiniteBackgroundPhysicalTransport.card_ge_four_of_half_sample
      B hn8 hhalf
  have hnR8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn8
  have hmR4 : (4 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hm4
  have hmnR : (B.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcard
  have hden : 0 < (n : ℝ) - 2 := by linarith only [hnR8]
  have hnum : 0 ≤ (B.card : ℝ) - 2 := by linarith only [hmR4]
  have hLambda : 0 ≤ backgroundScale B ∧ backgroundScale B ≤ 1 := by
    dsimp only [backgroundScale]
    constructor
    · exact div_nonneg hnum hden.le
    · apply (div_le_iff₀ hden).2
      linarith only [hmnR]
  have hMass : Pn.real E = dn ^ B.card * (1 - dn) ^ (n - B.card) :=
    Shao.OQ5.P41.FixedMaskConditionalBackgroundPhysicalTail.fixedMask_real
      μ Cn hCn B
  rcases hLams (backgroundScale B) hLambda with ⟨_, hSamples⟩
  rcases hSamples B.card hhalf hcard with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hLevels⟩
  refine ⟨hm4, hLambda.1, hLambda.2, hMass, ?_⟩
  intro z hz hzw
  rcases hLevels z hz hzw with ⟨_, _, _, _, _, _, hTail, _⟩
  have hPhysicalTail :
      |P.real (backgroundClosedTail B g r z) /
          Shao.standardNormalTail z - 1| ≤
        K * (β * Real.rpow (1 + z) p *
          Real.rpow (n : ℝ) (-((p - 2) / 2)) +
          (1 + z) ^ 3 / Real.sqrt (n : ℝ)) := by
    simpa only [backgroundClosedTail, background_physicalStatistic_eq_Tuncenter]
      using hTail
  have hInter :
      Pn.real (originalBackgroundClosedTail B g r z ∩ E) =
        Pn.real E * P.real (backgroundClosedTail B g r z) := by
    rw [hMass]
    exact
      Shao.OQ5.P41.FixedMaskConditionalBackgroundPhysicalTail.fixedMask_physical_closed_tail_intersection
        μ Cn hCn B e g r hg hr hrsym hm4 z
  refine ⟨hInter, ?_⟩
  have hWeight : 0 ≤ Pn.real E := measureReal_nonneg
  have hFactor :
      Pn.real E * P.real (backgroundClosedTail B g r z) /
          Shao.standardNormalTail z - Pn.real E =
        Pn.real E * (P.real (backgroundClosedTail B g r z) /
          Shao.standardNormalTail z - 1) := by
    ring
  rw [hInter, hFactor, abs_mul, abs_of_nonneg hWeight]
  calc
    Pn.real E * |P.real (backgroundClosedTail B g r z) /
        Shao.standardNormalTail z - 1| ≤
      Pn.real E * (K * (β * Real.rpow (1 + z) p *
        Real.rpow (n : ℝ) (-((p - 2) / 2)) +
        (1 + z) ^ 3 / Real.sqrt (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hPhysicalTail hWeight
    _ = Pn.real E * K * (β * Real.rpow (1 + z) p *
        Real.rpow (n : ℝ) (-((p - 2) / 2)) +
        (1 + z) ^ 3 / Real.sqrt (n : ℝ)) :=
      (mul_assoc _ _ _).symm

end

end Shao.OQ6.OriginalLogarithmicFixedMaskBackgroundFullWindowPhysicalTail
