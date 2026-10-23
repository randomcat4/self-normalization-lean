import Shao.OQ5.P53.SparseCoefficientMoments
import Shao.OQ5.P53.SparseSignedLabelLaw

set_option autoImplicit false

open scoped BigOperators ENNReal
open MeasureTheory

noncomputable section

namespace Shao.OQ5.P53

def sparseSignedShift (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (z : ℕ × Bool) : ℝ :=
  if z.2 = true then sparseLevelShift α x N z.1
  else -sparseLevelShift α x N z.1

private def signedShiftFlip (z : ℕ × Bool) : ℕ × Bool := (z.1, !z.2)

private theorem signedShiftFlip_preimage_singleton (j : ℕ) (b : Bool) :
    signedShiftFlip ⁻¹' ({(j, b)} : Set (ℕ × Bool)) = {(j, !b)} := by
  ext z
  rcases z with ⟨k, c⟩
  cases b <;> cases c <;> simp [signedShiftFlip]

private theorem signedShiftFlip_preserves (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) :
    (sparseSignedLabelMeasure α x N).map signedShiftFlip =
      sparseSignedLabelMeasure α x N := by
  apply Measure.ext_of_singleton
  rintro ⟨j, b⟩
  rw [Measure.map_apply (measurable_of_countable signedShiftFlip)
    (measurableSet_singleton (j, b)), signedShiftFlip_preimage_singleton]
  exact (sparseSignedLabelMeasure_singleton α x N j (!b)).trans
    (sparseSignedLabelMeasure_singleton α x N j b).symm

private theorem signedShift_integrable (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (g : ℝ → ℝ) (hneg : ∀ t : ℝ, ‖g (-t)‖ = ‖g t‖)
    (hs : Summable (fun j : ℕ =>
      sparseLabelMass α x N j * ‖g (sparseLevelShift α x N j)‖)) :
    Integrable (fun z => g (sparseSignedShift α x N z))
      (sparseSignedLabelMeasure α x N) := by
  apply (integrable_sparseSignedLabelMeasure_iff α x N _).2
  have hrow :
      (fun j : ℕ => (sparseLabelMass α x N j / 2) *
        (‖g (sparseSignedShift α x N (j, false))‖ +
          ‖g (sparseSignedShift α x N (j, true))‖)) =
      (fun j : ℕ => sparseLabelMass α x N j *
        ‖g (sparseLevelShift α x N j)‖) := by
    funext j
    change (sparseLabelMass α x N j / 2) *
      (‖g (-sparseLevelShift α x N j)‖ +
        ‖g (sparseLevelShift α x N j)‖) = _
    rw [hneg]
    ring
  rw [hrow]
  exact hs

private theorem signedShift_integral_even (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (g : ℝ → ℝ) (heven : ∀ t : ℝ, g (-t) = g t)
    (hsigned : Integrable (fun z => g (sparseSignedShift α x N z))
      (sparseSignedLabelMeasure α x N))
    (hlabel : Integrable (fun j => g (sparseLevelShift α x N j))
      (sparseLabelMeasure α x N)) :
    (∫ z, g (sparseSignedShift α x N z) ∂(sparseSignedLabelMeasure α x N)) =
      ∫ j, g (sparseLevelShift α x N j) ∂(sparseLabelMeasure α x N) := by
  rw [integral_sparseSignedLabelMeasure α x N _ hsigned,
    integral_sparseLabelMeasure α x N _ hlabel]
  apply tsum_congr
  intro j
  change (sparseLabelMass α x N j / 2) *
    (g (-sparseLevelShift α x N j) + g (sparseLevelShift α x N j)) = _
  rw [heven]
  ring

theorem measurable_sparseSignedShift :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), Measurable (sparseSignedShift α x N) := by
  intro α x N
  exact measurable_of_countable (sparseSignedShift α x N)

theorem sparseSignedShift_symmetric :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparseSignedLabelMeasure α x N).map (fun z => -sparseSignedShift α x N z) =
    (sparseSignedLabelMeasure α x N).map (sparseSignedShift α x N) := by
  intro α x N
  have hcomp : sparseSignedShift α x N ∘ signedShiftFlip =
      (fun z => -sparseSignedShift α x N z) := by
    funext z
    rcases z with ⟨j, b⟩
    cases b <;> simp [signedShiftFlip, sparseSignedShift]
  calc
    (sparseSignedLabelMeasure α x N).map (fun z => -sparseSignedShift α x N z) =
        (sparseSignedLabelMeasure α x N).map
          (sparseSignedShift α x N ∘ signedShiftFlip) := by rw [hcomp]
    _ = ((sparseSignedLabelMeasure α x N).map signedShiftFlip).map
        (sparseSignedShift α x N) :=
      (Measure.map_map (measurable_sparseSignedShift α x N)
        (measurable_of_countable signedShiftFlip)).symm
    _ = (sparseSignedLabelMeasure α x N).map (sparseSignedShift α x N) := by
      rw [signedShiftFlip_preserves]

theorem integrable_sparseSignedShift :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → SparseSelectionCore α x N → Integrable (sparseSignedShift α x N) (sparseSignedLabelMeasure α x N) := by
  intro α x N hα hN
  apply signedShift_integrable α x N (fun t : ℝ => t) (fun t => norm_neg t)
  simpa only [Real.norm_eq_abs, Real.rpow_one] using
    summable_sparseLabelMass_shift_rpow α x N hα hN 1 (by norm_num)

theorem integral_sparseSignedShift_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (∫ z, sparseSignedShift α x N z ∂(sparseSignedLabelMeasure α x N)) = 0 := by
  intro α x N hα hN
  rw [integral_sparseSignedLabelMeasure α x N _
    (integrable_sparseSignedShift α x N hα hN)]
  have hrow :
      (fun j : ℕ => (sparseLabelMass α x N j / 2) *
        (sparseSignedShift α x N (j, false) +
          sparseSignedShift α x N (j, true))) = (fun _ : ℕ => (0 : ℝ)) := by
    funext j
    change (sparseLabelMass α x N j / 2) *
      (-sparseLevelShift α x N j + sparseLevelShift α x N j) = 0
    ring
  rw [hrow, tsum_zero]

theorem integrable_sparseSignedShift_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ q : ℝ, 0 < q →
  Integrable (fun z => |sparseSignedShift α x N z| ^ q) (sparseSignedLabelMeasure α x N) := by
  intro α x N hα hN q hq
  apply signedShift_integrable α x N (fun t : ℝ => |t| ^ q)
  · intro t
    rw [abs_neg]
  · have hnorm (j : ℕ) :
        ‖|sparseLevelShift α x N j| ^ q‖ = |sparseLevelShift α x N j| ^ q := by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (sparseLevelShift α x N j)) q)]
    simpa only [hnorm] using summable_sparseLabelMass_shift_rpow α x N hα hN q hq

theorem integral_sparseSignedShift_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ q : ℝ, 0 < q →
  (∫ z, |sparseSignedShift α x N z| ^ q ∂(sparseSignedLabelMeasure α x N)) =
    ∫ j, |sparseLevelShift α x N j| ^ q ∂(sparseLabelMeasure α x N) := by
  intro α x N hα hN q hq
  exact signedShift_integral_even α x N (fun t : ℝ => |t| ^ q)
    (fun t => by rw [abs_neg])
    (integrable_sparseSignedShift_rpow α x N hα hN q hq)
    (integrable_sparseLabelMeasure_shift_rpow α x N hα hN q hq)

theorem integrable_sparseSignedShift_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  Integrable (fun z => (sparseSignedShift α x N z) ^ 2) (sparseSignedLabelMeasure α x N) := by
  intro α x N hα hN
  simpa only [Real.rpow_two, sq_abs] using
    integrable_sparseSignedShift_rpow α x N hα hN 2 (by norm_num)

theorem integral_sparseSignedShift_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (∫ z, (sparseSignedShift α x N z) ^ 2 ∂(sparseSignedLabelMeasure α x N)) =
    ∫ j, (sparseLevelShift α x N j) ^ 2 ∂(sparseLabelMeasure α x N) := by
  intro α x N hα hN
  simpa only [Real.rpow_two, sq_abs] using
    integral_sparseSignedShift_rpow α x N hα hN 2 (by norm_num)

end Shao.OQ5.P53
