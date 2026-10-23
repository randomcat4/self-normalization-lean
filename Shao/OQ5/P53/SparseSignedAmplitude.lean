import Shao.OQ5.P53.SparseCoefficientMoments
import Shao.OQ5.P53.SparseSignedLabelLaw

set_option autoImplicit false

open scoped BigOperators ENNReal
open MeasureTheory

noncomputable section

namespace Shao.OQ5.P53

def sparseSignedAmplitude (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (z : ℕ × Bool) : ℝ :=
  if z.2 = true then sparseLevelAmplitude α x N z.1
  else -sparseLevelAmplitude α x N z.1

private def signedAmplitudeFlip (z : ℕ × Bool) : ℕ × Bool := (z.1, !z.2)

private theorem signedAmplitudeFlip_preimage_singleton (j : ℕ) (b : Bool) :
    signedAmplitudeFlip ⁻¹' ({(j, b)} : Set (ℕ × Bool)) = {(j, !b)} := by
  ext z
  rcases z with ⟨k, c⟩
  cases b <;> cases c <;> simp [signedAmplitudeFlip]

private theorem signedAmplitudeFlip_preserves (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) :
    (sparseSignedLabelMeasure α x N).map signedAmplitudeFlip =
      sparseSignedLabelMeasure α x N := by
  apply Measure.ext_of_singleton
  rintro ⟨j, b⟩
  rw [Measure.map_apply (measurable_of_countable signedAmplitudeFlip)
    (measurableSet_singleton (j, b)), signedAmplitudeFlip_preimage_singleton]
  exact (sparseSignedLabelMeasure_singleton α x N j (!b)).trans
    (sparseSignedLabelMeasure_singleton α x N j b).symm

private theorem signedAmplitude_integrable (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (g : ℝ → ℝ) (hneg : ∀ t : ℝ, ‖g (-t)‖ = ‖g t‖)
    (hs : Summable (fun j : ℕ =>
      sparseLabelMass α x N j * ‖g (sparseLevelAmplitude α x N j)‖)) :
    Integrable (fun z => g (sparseSignedAmplitude α x N z))
      (sparseSignedLabelMeasure α x N) := by
  apply (integrable_sparseSignedLabelMeasure_iff α x N _).2
  have hrow :
      (fun j : ℕ => (sparseLabelMass α x N j / 2) *
        (‖g (sparseSignedAmplitude α x N (j, false))‖ +
          ‖g (sparseSignedAmplitude α x N (j, true))‖)) =
      (fun j : ℕ => sparseLabelMass α x N j *
        ‖g (sparseLevelAmplitude α x N j)‖) := by
    funext j
    change (sparseLabelMass α x N j / 2) *
      (‖g (-sparseLevelAmplitude α x N j)‖ +
        ‖g (sparseLevelAmplitude α x N j)‖) = _
    rw [hneg]
    ring
  rw [hrow]
  exact hs

private theorem signedAmplitude_integral_even (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (g : ℝ → ℝ) (heven : ∀ t : ℝ, g (-t) = g t)
    (hsigned : Integrable (fun z => g (sparseSignedAmplitude α x N z))
      (sparseSignedLabelMeasure α x N))
    (hlabel : Integrable (fun j => g (sparseLevelAmplitude α x N j))
      (sparseLabelMeasure α x N)) :
    (∫ z, g (sparseSignedAmplitude α x N z) ∂(sparseSignedLabelMeasure α x N)) =
      ∫ j, g (sparseLevelAmplitude α x N j) ∂(sparseLabelMeasure α x N) := by
  rw [integral_sparseSignedLabelMeasure α x N _ hsigned,
    integral_sparseLabelMeasure α x N _ hlabel]
  apply tsum_congr
  intro j
  change (sparseLabelMass α x N j / 2) *
    (g (-sparseLevelAmplitude α x N j) + g (sparseLevelAmplitude α x N j)) = _
  rw [heven]
  ring

theorem measurable_sparseSignedAmplitude :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), Measurable (sparseSignedAmplitude α x N) := by
  intro α x N
  exact measurable_of_countable (sparseSignedAmplitude α x N)

theorem sparseSignedAmplitude_symmetric :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparseSignedLabelMeasure α x N).map (fun z => -sparseSignedAmplitude α x N z) =
    (sparseSignedLabelMeasure α x N).map (sparseSignedAmplitude α x N) := by
  intro α x N
  have hcomp : sparseSignedAmplitude α x N ∘ signedAmplitudeFlip =
      (fun z => -sparseSignedAmplitude α x N z) := by
    funext z
    rcases z with ⟨j, b⟩
    cases b <;> simp [signedAmplitudeFlip, sparseSignedAmplitude]
  calc
    (sparseSignedLabelMeasure α x N).map (fun z => -sparseSignedAmplitude α x N z) =
        (sparseSignedLabelMeasure α x N).map
          (sparseSignedAmplitude α x N ∘ signedAmplitudeFlip) := by rw [hcomp]
    _ = ((sparseSignedLabelMeasure α x N).map signedAmplitudeFlip).map
        (sparseSignedAmplitude α x N) :=
      (Measure.map_map (measurable_sparseSignedAmplitude α x N)
        (measurable_of_countable signedAmplitudeFlip)).symm
    _ = (sparseSignedLabelMeasure α x N).map (sparseSignedAmplitude α x N) := by
      rw [signedAmplitudeFlip_preserves]

theorem integrable_sparseSignedAmplitude :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → Integrable (sparseSignedAmplitude α x N) (sparseSignedLabelMeasure α x N) := by
  intro α x N hα
  apply signedAmplitude_integrable α x N (fun t : ℝ => t) (fun t => norm_neg t)
  simpa only [Real.norm_eq_abs, Real.rpow_one] using
    summable_sparseLabelMass_amplitude_rpow α x N hα 1 (by norm_num)

theorem integral_sparseSignedAmplitude_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α →
  (∫ z, sparseSignedAmplitude α x N z ∂(sparseSignedLabelMeasure α x N)) = 0 := by
  intro α x N hα
  rw [integral_sparseSignedLabelMeasure α x N _
    (integrable_sparseSignedAmplitude α x N hα)]
  have hrow :
      (fun j : ℕ => (sparseLabelMass α x N j / 2) *
        (sparseSignedAmplitude α x N (j, false) +
          sparseSignedAmplitude α x N (j, true))) = (fun _ : ℕ => (0 : ℝ)) := by
    funext j
    change (sparseLabelMass α x N j / 2) *
      (-sparseLevelAmplitude α x N j + sparseLevelAmplitude α x N j) = 0
    ring
  rw [hrow, tsum_zero]

theorem integrable_sparseSignedAmplitude_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ q : ℝ, 0 < q →
  Integrable (fun z => |sparseSignedAmplitude α x N z| ^ q) (sparseSignedLabelMeasure α x N) := by
  intro α x N hα q hq
  apply signedAmplitude_integrable α x N (fun t : ℝ => |t| ^ q)
  · intro t
    rw [abs_neg]
  · have hnorm (j : ℕ) :
        ‖|sparseLevelAmplitude α x N j| ^ q‖ = |sparseLevelAmplitude α x N j| ^ q := by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (sparseLevelAmplitude α x N j)) q)]
    simpa only [hnorm] using summable_sparseLabelMass_amplitude_rpow α x N hα q hq

theorem integral_sparseSignedAmplitude_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ q : ℝ, 0 < q →
  (∫ z, |sparseSignedAmplitude α x N z| ^ q ∂(sparseSignedLabelMeasure α x N)) =
    ∫ j, |sparseLevelAmplitude α x N j| ^ q ∂(sparseLabelMeasure α x N) := by
  intro α x N hα q hq
  exact signedAmplitude_integral_even α x N (fun t : ℝ => |t| ^ q)
    (fun t => by rw [abs_neg])
    (integrable_sparseSignedAmplitude_rpow α x N hα q hq)
    (integrable_sparseLabelMeasure_amplitude_rpow α x N hα q hq)

theorem integrable_sparseSignedAmplitude_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α →
  Integrable (fun z => (sparseSignedAmplitude α x N z) ^ 2) (sparseSignedLabelMeasure α x N) := by
  intro α x N hα
  simpa only [Real.rpow_two, sq_abs] using
    integrable_sparseSignedAmplitude_rpow α x N hα 2 (by norm_num)

theorem integral_sparseSignedAmplitude_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α →
  (∫ z, (sparseSignedAmplitude α x N z) ^ 2 ∂(sparseSignedLabelMeasure α x N)) =
    ∫ j, (sparseLevelAmplitude α x N j) ^ 2 ∂(sparseLabelMeasure α x N) := by
  intro α x N hα
  simpa only [Real.rpow_two, sq_abs] using
    integral_sparseSignedAmplitude_rpow α x N hα 2 (by norm_num)

theorem integral_sparseSignedAmplitude_sq_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  0 < ∫ z, (sparseSignedAmplitude α x N z) ^ 2 ∂(sparseSignedLabelMeasure α x N) := by
  intro α x N hα hN
  rw [integral_sparseSignedAmplitude_sq α x N hα]
  exact integral_sparseLabelMeasure_amplitude_sq_pos α x N hα hN

theorem integrable_sparseSignedAmplitude_exp :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
  Integrable (fun z => Real.exp (τ * |sparseSignedAmplitude α x N z| ^ α))
    (sparseSignedLabelMeasure α x N) := by
  intro α x N hα τ hτ hτ1
  apply signedAmplitude_integrable α x N (fun t : ℝ => Real.exp (τ * |t| ^ α))
  · intro t
    rw [abs_neg]
  · have hnorm (j : ℕ) :
        ‖Real.exp (τ * |sparseLevelAmplitude α x N j| ^ α)‖ =
          Real.exp (τ * |sparseLevelAmplitude α x N j| ^ α) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simpa only [hnorm] using
      summable_sparseLabelMass_amplitude_exp α x N hα τ hτ hτ1

theorem integral_sparseSignedAmplitude_exp :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
  (∫ z, Real.exp (τ * |sparseSignedAmplitude α x N z| ^ α) ∂(sparseSignedLabelMeasure α x N)) =
    ∫ j, Real.exp (τ * |sparseLevelAmplitude α x N j| ^ α) ∂(sparseLabelMeasure α x N) := by
  intro α x N hα τ hτ hτ1
  exact signedAmplitude_integral_even α x N (fun t : ℝ => Real.exp (τ * |t| ^ α))
    (fun t => by rw [abs_neg])
    (integrable_sparseSignedAmplitude_exp α x N hα τ hτ hτ1)
    (integrable_sparseLabelMeasure_amplitude_exp α x N hα τ hτ hτ1)

theorem integral_sparseSignedAmplitude_exp_le :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
  (∫ z, Real.exp (τ * |sparseSignedAmplitude α x N z| ^ α) ∂(sparseSignedLabelMeasure α x N)) ≤ (5 / 4 : ℝ) := by
  intro α x N hα τ hτ hτ1
  rw [integral_sparseSignedAmplitude_exp α x N hα τ hτ hτ1]
  exact integral_sparseLabelMeasure_amplitude_exp_le α x N hα τ hτ hτ1

end Shao.OQ5.P53
