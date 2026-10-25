import Shao.OQ6.ConditionalResidualExponentialEnvelope
import Shao.OQ6.StretchedExponentialSumMoments

set_option autoImplicit false

universe u

namespace Shao.OQ6.ConditionalGhostSquareMoments

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem square_pair_exponential_domination
    (α τ : ℝ) (hα : 0 < α) (hτ : 0 < τ)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.exp ((τ / Real.rpow (2 : ℝ) α) *
      Real.rpow ((u + v) ^ 2) (α / 2)) ≤
      Real.exp (τ * Real.rpow u α) *
        Real.exp (τ * Real.rpow v α) := by
  change Real.exp ((τ / (2 : ℝ) ^ α) * (((u + v) ^ 2 : ℝ) ^ (α / 2))) ≤
    Real.exp (τ * u ^ α) * Real.exp (τ * v ^ α)
  have hsum : 0 ≤ u + v := add_nonneg hu hv
  have hpow : ((u + v) ^ 2 : ℝ) ^ (α / 2) = (u + v) ^ α := by
    rw [← Real.rpow_two (u + v), ← Real.rpow_mul hsum]
    congr 1 <;> ring
  have hbound : (u + v) ^ α ≤ (2 : ℝ) ^ α * (u ^ α + v ^ α) := by
    by_cases huv : u ≤ v
    · calc
        (u + v) ^ α ≤ (2 * v) ^ α :=
          Real.rpow_le_rpow hsum (by linarith) hα.le
        _ = (2 : ℝ) ^ α * v ^ α := Real.mul_rpow (by norm_num) hv
        _ ≤ (2 : ℝ) ^ α * (u ^ α + v ^ α) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) α)
          exact le_add_of_nonneg_left (Real.rpow_nonneg hu α)
    · have huvNot : ¬ u ≤ v := huv
      clear huv
      have hvu : v ≤ u := le_of_not_ge huvNot
      calc
        (u + v) ^ α ≤ (2 * u) ^ α :=
          Real.rpow_le_rpow hsum (by linarith) hα.le
        _ = (2 : ℝ) ^ α * u ^ α := Real.mul_rpow (by norm_num) hu
        _ ≤ (2 : ℝ) ^ α * (u ^ α + v ^ α) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) α)
          exact le_add_of_nonneg_right (Real.rpow_nonneg hv α)
  have htwo : 0 < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [hpow]
  calc
    (τ / (2 : ℝ) ^ α) * (u + v) ^ α ≤
        (τ / (2 : ℝ) ^ α) * ((2 : ℝ) ^ α * (u ^ α + v ^ α)) :=
      mul_le_mul_of_nonneg_left hbound (div_pos hτ htwo).le
    _ = τ * u ^ α + τ * v ^ α := by
      field_simp [htwo.ne']
      <;> ring

private theorem pair_square_exponential_integral
    {Ω : Type u} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (v : Ω → ℝ) (hv : Measurable v)
    (hvnonneg : ∀ᵐ o ∂ν, 0 ≤ v o)
    (α τ : ℝ) (hα : 0 < α) (hτ : 0 < τ)
    (hFint : Integrable
      (fun o => Real.exp (τ * Real.rpow (v o) α)) ν) :
    Integrable
      (fun z : Ω × Ω => Real.exp ((τ / Real.rpow (2 : ℝ) α) *
        Real.rpow ((v z.1 + v z.2) ^ 2) (α / 2))) (ν.prod ν) ∧
      (∫ z : Ω × Ω, Real.exp ((τ / Real.rpow (2 : ℝ) α) *
        Real.rpow ((v z.1 + v z.2) ^ 2) (α / 2)) ∂(ν.prod ν)) ≤
        (∫ o, Real.exp (τ * Real.rpow (v o) α) ∂ν) ^ 2 := by
  let F : Ω → ℝ := fun o : Ω => Real.exp (τ * Real.rpow (v o) α)
  let D : Ω × Ω → ℝ := fun z : Ω × Ω => F z.1 * F z.2
  let E : Ω × Ω → ℝ := fun z : Ω × Ω =>
    Real.exp ((τ / Real.rpow (2 : ℝ) α) *
      Real.rpow ((v z.1 + v z.2) ^ 2) (α / 2))
  have hDint : Integrable D (ν.prod ν) := hFint.mul_prod hFint
  have hEmeas : Measurable E := by
    exact (measurable_const.mul
      ((((hv.comp measurable_fst).add (hv.comp measurable_snd)).pow_const
        (2 : ℕ)).pow_const (α / 2))).exp
  have hEnonneg : ∀ᵐ z : Ω × Ω ∂(ν.prod ν), 0 ≤ E z := by
    exact Filter.Eventually.of_forall (fun z => Real.exp_nonneg _)
  have hED : ∀ᵐ z : Ω × Ω ∂(ν.prod ν), E z ≤ D z := by
    filter_upwards [
      (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := ν)).ae hvnonneg,
      (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := ν)).ae hvnonneg]
      with z hfirst hsecond
    exact square_pair_exponential_domination α τ hα hτ
      (v z.1) (v z.2) hfirst hsecond
  have hEint : Integrable E (ν.prod ν) :=
    hDint.mono_nonneg hEmeas.aestronglyMeasurable hEnonneg hED
  refine ⟨hEint, ?_⟩
  calc
    (∫ z : Ω × Ω, E z ∂(ν.prod ν)) ≤
        (∫ z : Ω × Ω, D z ∂(ν.prod ν)) :=
      integral_mono_ae hEint hDint hED
    _ = (∫ o, F o ∂ν) ^ 2 := by
      change (∫ z : Ω × Ω, F z.1 * F z.2 ∂(ν.prod ν)) = _
      rw [integral_prod_mul]
      ring

theorem actual_conditional_ghost_square_moments
    {Ω : Type u} [MeasurableSpace Ω]
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
    (α τ : ℝ) (hα : 0 < α) (hαtwo : α ≤ 2) (hτ : 0 < τ)
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
    let β : ℝ := α / 2
    let tauPair : ℝ := tauStd / Real.rpow (2 : ℝ) α
    let Mpair : ℝ := (2 * Mexp) ^ 2
    let Cmom : ℝ :=
      Shao.OQ6.StretchedExponentialSumMoments.sumMomentScale β tauPair Mpair
    1 ≤ aenv ∧ aenv ^ 2 = Cenv ∧ 0 < tauStd ∧ 1 ≤ Mexp ∧
      Measurable wstd ∧ MemLp wstd 2 μ ∧
      0 < β ∧ β ≤ 1 ∧ 0 < tauPair ∧ 1 ≤ Mpair ∧ 0 < Cmom ∧
      ∃ N0 : ℕ, 1 ≤ N0 ∧
      ∀ R : ℝ, (N0 : ℝ) ≤ R →
      let C : Set Ω := {o : Ω | w o ≤ R}
      let d : ℝ := μ.real C
      let ν : Measure Ω := (μ C)⁻¹ • μ.restrict C
      let pairLaw : Measure (Ω × Ω) := ν.prod ν
      let W : Ω × Ω → ℝ := fun z => wstd z.1 + wstd z.2
      let Y : Ω × Ω → ℝ := fun z => (W z) ^ 2
      MeasurableSet C ∧ (1 / 2 : ℝ) ≤ d ∧
        IsProbabilityMeasure ν ∧ ν ≪ μ ∧ ν C = 1 ∧
        (∀ᵐ o ∂ν, 1 ≤ wstd o ∧ wstd o ≤ aenv * R) ∧
        MemLp wstd 2 ν ∧
        Integrable (fun o => Real.exp (tauStd * Real.rpow (wstd o) α)) ν ∧
        (∫ o, Real.exp (tauStd * Real.rpow (wstd o) α) ∂ν) =
          (∫ o in C, Real.exp (τ * Real.rpow (w o) α) ∂μ) / d ∧
        (∫ o, Real.exp (tauStd * Real.rpow (wstd o) α) ∂ν) ≤ 2 * Mexp ∧
        IsProbabilityMeasure pairLaw ∧ Measurable W ∧ Measurable Y ∧
        (∀ z : Ω × Ω, 0 ≤ Y z) ∧
        Integrable (fun z => Real.exp (tauPair * Real.rpow (Y z) β)) pairLaw ∧
        (∫ z, Real.exp (tauPair * Real.rpow (Y z) β) ∂pairLaw) ≤ Mpair ∧
        (∀ n : ℕ,
          let νn : Fin n → Measure (Ω × Ω) := fun _ => pairLaw
          let Yn : Fin n → (Ω × Ω) → ℝ := fun _ => Y
          let S : (Fin n → Ω × Ω) → ℝ :=
            Shao.OQ6.StretchedExponentialSumMoments.coordinateSum Yn
          ∀ q : ℝ, 1 ≤ q →
          Integrable (fun x => Real.rpow (S x) q) (Measure.pi νn) ∧
            Real.rpow (∫ x, Real.rpow (S x) q ∂(Measure.pi νn)) (1 / q) ≤
              Cmom * ((n : ℝ) + Real.rpow q (1 / β))) ∧
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
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let M : ℝ := ∫ o, w o ^ 2 ∂μ
  let W2 : ℝ := Real.sqrt M
  let Cenv : ℝ := 2 * (1 + 2 * W2) ^ 2
  let aenv : ℝ := Real.sqrt Cenv
  let wstd : Ω → ℝ := fun o => aenv * w o
  let tauStd : ℝ := τ / Real.rpow aenv α
  let Mexp : ℝ := ∫ o, Real.exp (τ * Real.rpow (w o) α) ∂μ
  let β : ℝ := α / 2
  let tauPair : ℝ := tauStd / Real.rpow (2 : ℝ) α
  let Mpair : ℝ := (2 * Mexp) ^ 2
  let Cmom : ℝ :=
    Shao.OQ6.StretchedExponentialSumMoments.sumMomentScale β tauPair Mpair
  have h182Result :=
    Shao.OQ6.ConditionalResidualExponentialEnvelope.actual_conditional_residual_exponential_envelope
      μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone
      α τ hα hτ hwexp henvelope p hp hgp
  have haenv : 1 ≤ aenv := h182Result.1
  have haenvsq : aenv ^ 2 = Cenv := h182Result.2.1
  have htauStd : 0 < tauStd := h182Result.2.2.1
  have hMexp : 1 ≤ Mexp := h182Result.2.2.2.1
  have h182Threshold : ∃ N0 : ℕ, 1 ≤ N0 ∧
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
          |Kstd z.1 z.2| ≤ (aenv * R) ^ 2) := h182Result.2.2.2.2.2.2
  have hβ : 0 < β := by dsimp only [β]; linarith
  have hβone : β ≤ 1 := by dsimp only [β]; linarith
  have htauPair : 0 < tauPair :=
    div_pos htauStd (Real.rpow_pos_of_pos (by norm_num) α)
  have hMpair : 1 ≤ Mpair := by
    dsimp only [Mpair]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * Mexp - 1)
      (by linarith : 0 ≤ 2 * Mexp + 1)]
  have h183Uniform : ∃ C : ℝ, 0 < C ∧ C = Shao.OQ6.StretchedExponentialSumMoments.sumMomentScale β tauPair Mpair ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω]
        (n : ℕ) (μ : Fin n → Measure Ω)
        (hμ : ∀ i : Fin n, IsProbabilityMeasure (μ i))
        (Y : Fin n → Ω → ℝ)
        (hY : ∀ i : Fin n, Measurable (Y i))
        (hYnonneg : ∀ i : Fin n, ∀ᵐ ω ∂(μ i), 0 ≤ Y i ω)
        (hYexpInt : ∀ i : Fin n,
          Integrable (fun ω : Ω => Real.exp (tauPair * (Y i ω) ^ β)) (μ i))
        (hYexpBound : ∀ i : Fin n,
          (∫ ω : Ω, Real.exp (tauPair * (Y i ω) ^ β) ∂(μ i)) ≤ Mpair)
        (q : ℝ) (hq : 1 ≤ q),
        Integrable (fun x : Fin n → Ω => (Shao.OQ6.StretchedExponentialSumMoments.coordinateSum Y x) ^ q) (Measure.pi μ) ∧
          (∫ x : Fin n → Ω, (Shao.OQ6.StretchedExponentialSumMoments.coordinateSum Y x) ^ q ∂(Measure.pi μ)) ^ (1 / q) ≤
            C * ((n : ℝ) + q ^ (1 / β)) :=
    Shao.OQ6.StretchedExponentialSumMoments.exists_uniform_sum_real_moment_bound
      β tauPair Mpair hβ hβone htauPair hMpair
  let C0 : ℝ := Classical.choose h183Uniform
  have hC0Spec : 0 < C0 ∧ C0 = Shao.OQ6.StretchedExponentialSumMoments.sumMomentScale β tauPair Mpair ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω]
        (n : ℕ) (μ : Fin n → Measure Ω)
        (hμ : ∀ i : Fin n, IsProbabilityMeasure (μ i))
        (Y : Fin n → Ω → ℝ)
        (hY : ∀ i : Fin n, Measurable (Y i))
        (hYnonneg : ∀ i : Fin n, ∀ᵐ ω ∂(μ i), 0 ≤ Y i ω)
        (hYexpInt : ∀ i : Fin n,
          Integrable (fun ω : Ω => Real.exp (tauPair * (Y i ω) ^ β)) (μ i))
        (hYexpBound : ∀ i : Fin n,
          (∫ ω : Ω, Real.exp (tauPair * (Y i ω) ^ β) ∂(μ i)) ≤ Mpair)
        (q : ℝ) (hq : 1 ≤ q),
        Integrable (fun x : Fin n → Ω => (Shao.OQ6.StretchedExponentialSumMoments.coordinateSum Y x) ^ q) (Measure.pi μ) ∧
          (∫ x : Fin n → Ω, (Shao.OQ6.StretchedExponentialSumMoments.coordinateSum Y x) ^ q ∂(Measure.pi μ)) ^ (1 / q) ≤
            C0 * ((n : ℝ) + q ^ (1 / β)) := Classical.choose_spec h183Uniform
  have hCmom : 0 < Cmom := by
    simpa only [Cmom, hC0Spec.2.1] using hC0Spec.1
  let N0 : ℕ := Classical.choose h182Threshold
  have hN0Spec : 1 ≤ N0 ∧
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
          |Kstd z.1 z.2| ≤ (aenv * R) ^ 2) := Classical.choose_spec h182Threshold
  change 1 ≤ aenv ∧ aenv ^ 2 = Cenv ∧ 0 < tauStd ∧ 1 ≤ Mexp ∧
    Measurable wstd ∧ MemLp wstd 2 μ ∧ 0 < β ∧ β ≤ 1 ∧
    0 < tauPair ∧ 1 ≤ Mpair ∧ 0 < Cmom ∧ _
  refine ⟨haenv, haenvsq, htauStd, hMexp, h182Result.2.2.2.2.1,
    h182Result.2.2.2.2.2.1, hβ, hβone, htauPair, hMpair, hCmom,
    N0, hN0Spec.1, ?_⟩
  intro R hR
  let C : Set Ω := {o : Ω | w o ≤ R}
  let d : ℝ := μ.real C
  let ν : Measure Ω := (μ C)⁻¹ • μ.restrict C
  let pairLaw : Measure (Ω × Ω) := ν.prod ν
  let W : Ω × Ω → ℝ := fun z => wstd z.1 + wstd z.2
  let Y : Ω × Ω → ℝ := fun z => (W z) ^ 2
  have hR182 := hN0Spec.2 R hR
  rcases hR182 with ⟨hCmeas, hd, hνprob, hνac, hνC, hwstdBounds,
    hwstdL2ν, hFstdInt, hFstdEq, hFstdBound, hKstd⟩
  have hwstdMeas : Measurable wstd := h182Result.2.2.2.2.1
  have hwstdNonneg : ∀ᵐ o ∂ν, 0 ≤ wstd o := by
    filter_upwards [hwstdBounds] with o ho
    exact le_trans zero_le_one ho.1
  letI instProbν : IsProbabilityMeasure ν := hνprob
  have hpairProbability : IsProbabilityMeasure pairLaw := by
    dsimp only [pairLaw]
    infer_instance
  have hWMeas : Measurable W :=
    (hwstdMeas.comp measurable_fst).add (hwstdMeas.comp measurable_snd)
  have hYMeas : Measurable Y := hWMeas.pow_const (2 : ℕ)
  have hYnonneg : ∀ z : Ω × Ω, 0 ≤ Y z := fun z => sq_nonneg (W z)
  have hpair := pair_square_exponential_integral
    ν wstd hwstdMeas hwstdNonneg α tauStd hα htauStd hFstdInt
  have hYexpInt :
      Integrable (fun z => Real.exp (tauPair * Real.rpow (Y z) β)) pairLaw :=
    hpair.1
  have hFstdIntegralNonneg :
      0 ≤ (∫ o, Real.exp (tauStd * Real.rpow (wstd o) α) ∂ν) :=
    integral_nonneg (fun o => Real.exp_nonneg _)
  have hFstdSquareBound :
      (∫ o, Real.exp (tauStd * Real.rpow (wstd o) α) ∂ν) ^ 2 ≤ Mpair := by
    dsimp only [Mpair]
    nlinarith [mul_nonneg (sub_nonneg.mpr hFstdBound)
      (add_nonneg hFstdIntegralNonneg (by linarith [hMexp] : 0 ≤ 2 * Mexp))]
  have hYexpBound :
      (∫ z, Real.exp (tauPair * Real.rpow (Y z) β) ∂pairLaw) ≤ Mpair :=
    le_trans hpair.2 hFstdSquareBound
  refine ⟨hCmeas, hd, hνprob, hνac, hνC, hwstdBounds, hwstdL2ν,
    hFstdInt, hFstdEq, hFstdBound, hpairProbability, hWMeas, hYMeas,
    hYnonneg, hYexpInt, hYexpBound, ?_, ?_⟩
  · intro n
    let νn : Fin n → Measure (Ω × Ω) := fun _ => pairLaw
    let Yn : Fin n → (Ω × Ω) → ℝ := fun _ => Y
    let S : (Fin n → Ω × Ω) → ℝ :=
      Shao.OQ6.StretchedExponentialSumMoments.coordinateSum Yn
    have hνn : ∀ i : Fin n, IsProbabilityMeasure (νn i) :=
      fun _ => hpairProbability
    have hYnMeas : ∀ i : Fin n, Measurable (Yn i) := fun _ => hYMeas
    have hYnNonneg : ∀ i : Fin n, ∀ᵐ z ∂(νn i), 0 ≤ Yn i z :=
      fun _ => Filter.Eventually.of_forall hYnonneg
    have hYnExpInt : ∀ i : Fin n,
        Integrable (fun z : Ω × Ω => Real.exp (tauPair * (Yn i z) ^ β)) (νn i) :=
      fun _ => hYexpInt
    have hYnExpBound : ∀ i : Fin n,
        (∫ z : Ω × Ω, Real.exp (tauPair * (Yn i z) ^ β) ∂(νn i)) ≤ Mpair :=
      fun _ => hYexpBound
    change ∀ q : ℝ, 1 ≤ q →
      Integrable (fun x => Real.rpow (S x) q) (Measure.pi νn) ∧
        Real.rpow (∫ x, Real.rpow (S x) q ∂(Measure.pi νn)) (1 / q) ≤
          Cmom * ((n : ℝ) + Real.rpow q (1 / β))
    intro q hq
    simpa only [Cmom, S, hC0Spec.2.1, Real.rpow_eq_pow] using
      (hC0Spec.2.2 (Ω × Ω) n νn hνn Yn hYnMeas hYnNonneg
        hYnExpInt hYnExpBound q hq)
  · intro lam hlam
    let H : Ω → Ω → ℝ := fun o y => g o + g y + lam * r o y
    let κ : ℝ := ∫ z : Ω × Ω, H z.1 z.2 ∂(ν.prod ν)
    let G : Ω → ℝ := fun o => (∫ y, H o y ∂ν) - κ
    let σ2 : ℝ := ∫ o, G o ^ 2 ∂ν
    let σ : ℝ := Real.sqrt σ2
    let K : Ω → Ω → ℝ := fun o y => H o y - κ - G o - G y
    let Kstd : Ω → Ω → ℝ := fun o y => K o y / σ
    exact hKstd lam hlam


end

end Shao.OQ6.ConditionalGhostSquareMoments
