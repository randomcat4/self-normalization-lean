import Shao.OQ3.AtomicMeasure
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The centered original law obtained by inverse tilt

Source: current/oq3/proofs/r1/report.md, lines 137-145.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U4 scope: dc793b872b31118dba4ae1bd85c5cf2f4f5b24007c7e3749c3034552f4720b56.
-/

namespace Shao.OQ3

open MeasureTheory
open scoped Matrix

noncomputable section

def inverseNormalizer (ell : ℝ) (w : AtomicIndex → ℝ) : ℝ :=
  ∫ x, Real.exp (-ell * normalValue x) ∂atomicMeasure w

def originalMeasure (ell : ℝ) (w : AtomicIndex → ℝ) : Measure ℝ :=
  (atomicMeasure w).tilted (fun x => -ell * normalValue x)

theorem integrable_continuous_of_fixed_bounds (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable f mu := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact
    (Set.Icc (-(4 + Real.sqrt 10)) (4 + Real.sqrt 10))).exists_bound_of_continuousOn
      hf.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [hb] with x hx
  exact hC x (abs_le.mp hx)

theorem inverseExp_integrable (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) :
    Integrable (fun x => Real.exp (-ell * normalValue x)) (atomicMeasure w) := by
  let := atomicMeasure_isProbabilityMeasure w hw hs
  apply integrable_continuous_of_fixed_bounds (atomicMeasure w)
    ((atomicMeasure_ae_bounds w).mono fun _ hx => hx.2)
  unfold normalValue
  fun_prop

theorem inverseNormalizer_pos (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) :
    0 < inverseNormalizer ell w := by
  let := atomicMeasure_isProbabilityMeasure w hw hs
  exact integral_exp_pos (inverseExp_integrable ell w hw hs)

theorem originalMeasure_isProbabilityMeasure (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) :
    IsProbabilityMeasure (originalMeasure ell w) := by
  let := atomicMeasure_isProbabilityMeasure w hw hs
  exact isProbabilityMeasure_tilted (inverseExp_integrable ell w hw hs)

theorem originalMeasure_ae_bounds (ell : ℝ) (w : AtomicIndex → ℝ) :
    ∀ᵐ x ∂originalMeasure ell w, 1 ≤ |x| ∧ |x| ≤ 4 + Real.sqrt 10 := by
  exact (tilted_absolutelyContinuous (atomicMeasure w)
    (fun x => -ell * normalValue x)).ae_le (atomicMeasure_ae_bounds w)

theorem originalMeasure_integrable_id (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) :
    Integrable (fun x : ℝ => x) (originalMeasure ell w) := by
  let := originalMeasure_isProbabilityMeasure ell w hw hs
  exact integrable_continuous_of_fixed_bounds (originalMeasure ell w)
    ((originalMeasure_ae_bounds ell w).mono fun _ hx => hx.2) _ continuous_id

theorem originalMeasure_singleton (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (i : AtomicIndex) :
    originalMeasure ell w {fixedAtom i} = ENNReal.ofReal
      (w i * Real.exp (-ell * normalValue (fixedAtom i)) / inverseNormalizer ell w) := by
  let := atomicMeasure_isProbabilityMeasure w hw hs
  rw [originalMeasure, tilted_apply_eq_ofReal_integral,
    integral_singleton, atomicMeasure_real_singleton w hw i]
  congr 1
  simp only [smul_eq_mul, inverseNormalizer]
  ring

theorem originalMeasure_real_singleton (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (i : AtomicIndex) :
    (originalMeasure ell w).real {fixedAtom i} =
      w i * Real.exp (-ell * normalValue (fixedAtom i)) / inverseNormalizer ell w := by
  rw [measureReal_def, originalMeasure_singleton ell w hw hs i]
  exact ENNReal.toReal_ofReal (div_nonneg
    (mul_nonneg (hw i) (Real.exp_pos _).le) (inverseNormalizer_pos ell w hw hs).le)

theorem originalMeasure_atom_pos (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (i : AtomicIndex) (hi : 0 < w i) :
    0 < (originalMeasure ell w).real {fixedAtom i} := by
  rw [originalMeasure_real_singleton ell w hw hs i]
  exact div_pos (mul_pos hi (Real.exp_pos _)) (inverseNormalizer_pos ell w hw hs)

theorem originalMeasure_centered (ell q : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) :
    Integrable (fun x : ℝ => x) (originalMeasure ell w) ∧
      (∫ x, x ∂originalMeasure ell w) = 0 := by
  have hmass : HasSum w 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  have hc : (∫ x, centeringFeature ell x ∂atomicMeasure w) = 0 := by
    simpa [constraintFeature, constraintTarget] using
      (atomicMeasure_constraints ell q w hw hm 2).2
  refine ⟨originalMeasure_integrable_id ell w hw hmass, ?_⟩
  rw [originalMeasure, integral_tilted]
  change (∫ x, (Real.exp (-ell * normalValue x) / inverseNormalizer ell w) * x
    ∂atomicMeasure w) = 0
  have hfun : (fun x => (Real.exp (-ell * normalValue x) / inverseNormalizer ell w) * x) =
      (fun x => centeringFeature ell x / inverseNormalizer ell w) := by
    funext x
    unfold centeringFeature
    ring
  rw [hfun, integral_div, hc, zero_div]

theorem originalMeasure_retilt (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) :
    (originalMeasure ell w).tilted (fun x => ell * normalValue x) = atomicMeasure w := by
  let := atomicMeasure_isProbabilityMeasure w hw hs
  have hneg : -(fun x : ℝ => -ell * normalValue x) = (fun x => ell * normalValue x) := by
    funext x
    simp only [Pi.neg_apply]
    ring
  have hret := tilted_neg_same (f := fun x => -ell * normalValue x)
    (inverseExp_integrable ell w hw hs)
  rw [hneg] at hret
  exact hret

theorem originalMeasure_forward_normalizer (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) :
    Integrable (fun x => Real.exp (ell * normalValue x)) (originalMeasure ell w) ∧
      (∫ x, Real.exp (ell * normalValue x) ∂originalMeasure ell w) =
        (inverseNormalizer ell w)⁻¹ := by
  let := atomicMeasure_isProbabilityMeasure w hw hs
  let := originalMeasure_isProbabilityMeasure ell w hw hs
  constructor
  · apply integrable_continuous_of_fixed_bounds (originalMeasure ell w)
      ((originalMeasure_ae_bounds ell w).mono fun _ hx => hx.2)
    unfold normalValue
    fun_prop
  · rw [originalMeasure, integral_exp_tilted]
    have hzero : (fun x => -ell * normalValue x) + (fun x => ell * normalValue x) = 0 := by
      funext x
      simp only [Pi.add_apply, Pi.zero_apply]
      ring
    rw [hzero]
    simp [inverseNormalizer]

theorem exists_source_original_family :
    ∃ (p : Fin 4 → ℝ) (q eps : ℝ), (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧
      0 < eps ∧ (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
      ∀ (r : ℕ → ℝ), (∀ j, 0 < r j) → Summable r → (∑' j, r j) < eps →
        IsProbabilityMeasure (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
        (Integrable (fun x : ℝ => x) (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
          (∫ x, x ∂originalMeasure sourceEll (limitingMass sourceEll p r)) = 0) ∧
        (∀ i, 0 < (originalMeasure sourceEll (limitingMass sourceEll p r)).real {fixedAtom i}) ∧
        (∀ᵐ x ∂originalMeasure sourceEll (limitingMass sourceEll p r),
          1 ≤ |x| ∧ |x| ≤ 4 + Real.sqrt 10) ∧
        (originalMeasure sourceEll (limitingMass sourceEll p r)).tilted
          (fun x => sourceEll * normalValue x) = atomicMeasure (limitingMass sourceEll p r) := by
  obtain ⟨p, q, eps, hp, hlo, hhi, heps, hc, hfamily⟩ := exists_source_limit_family
  refine ⟨p, q, eps, hp, hlo, hhi, heps, hc, ?_⟩
  intro r hr hs ht
  obtain ⟨hpos, hm⟩ := hfamily r hr hs ht
  have hnonneg := fun i => (hpos i).le
  have hmass : HasSum (limitingMass sourceEll p r) 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  exact ⟨originalMeasure_isProbabilityMeasure _ _ hnonneg hmass,
    originalMeasure_centered sourceEll q _ hnonneg hm,
    fun i => originalMeasure_atom_pos _ _ hnonneg hmass i (hpos i),
    originalMeasure_ae_bounds _ _, originalMeasure_retilt _ _ hnonneg hmass⟩

end
end Shao.OQ3
