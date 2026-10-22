import Shao.OQ3.AtomicProductControl
import Shao.OQ3.PositiveRate

/-!
# Exact finite-product change of measure for the fixed atom laws

Source: current/oq3/proofs/r1/report.md, lines 499-520.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U9b scope: cac22df661588663b9fdcda118a1d71021df105867bc1545378f0c5dbf50a015.
-/

namespace Shao.OQ3

open MeasureTheory
open scoped Matrix

noncomputable section

def normalizedTailCoefficient (ell q : ℝ) (w : AtomicIndex → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (2 * Real.pi * (n : ℝ)) * Real.exp ((n : ℝ) * saddleRate ell q w) *
    (Measure.pi (fun _ : Fin n => originalMeasure ell w)).real (sourceTail q n)

def tiltedTailCoefficient (ell q : ℝ) (w : AtomicIndex → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (2 * Real.pi * (n : ℝ)) *
    (∫ z, (sourceTail q n).indicator (fun z => Real.exp (-ell * normalDeviation q z)) z
      ∂Measure.pi (fun _ : Fin n => atomicMeasure w))

theorem iid_inverseNormalizer (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (n : ℕ) :
  Integrable (fun z : Shao.Path n => Real.exp (-ell * (∑ i, normalValue (z i))))
    (Measure.pi (fun _ : Fin n => atomicMeasure w)) ∧
    (∫ z : Shao.Path n, Real.exp (-ell * (∑ i, normalValue (z i)))
      ∂Measure.pi (fun _ : Fin n => atomicMeasure w)) = (inverseNormalizer ell w) ^ n := by
  let := atomicMeasure_isProbabilityMeasure w hw hs
  have hfun : (fun z : Shao.Path n => Real.exp (-ell * (∑ i, normalValue (z i)))) =
      (fun z => ∏ i, Real.exp (-ell * normalValue (z i))) := by
    funext z
    rw [Finset.mul_sum, Real.exp_sum]
  rw [hfun]
  refine ⟨Integrable.fintype_prod (fun _ : Fin n => inverseExp_integrable ell w hw hs), ?_⟩
  simpa only [inverseNormalizer, Fintype.card_fin] using
    (integral_fintype_prod_eq_pow (ι := Fin n) (μ := atomicMeasure w)
      (fun x => Real.exp (-ell * normalValue x)))

theorem original_iid_eq_tilted (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (n : ℕ) :
  Measure.pi (fun _ : Fin n => originalMeasure ell w) =
    (Measure.pi (fun _ : Fin n => atomicMeasure w)).tilted
      (fun z => -ell * (∑ i, normalValue (z i))) := by
  classical
  let := atomicMeasure_isProbabilityMeasure w hw hs
  let := originalMeasure_isProbabilityMeasure ell w hw hs
  have hZ := inverseNormalizer_pos ell w hw hs
  have hnorm := iid_inverseNormalizer ell w hw hs n
  have hdensity : (fun z : Shao.Path n =>
      Real.exp (-ell * (∑ i, normalValue (z i))) / (inverseNormalizer ell w) ^ n) =
      (fun z => ∏ i, Real.exp (-ell * normalValue (z i)) / inverseNormalizer ell w) := by
    funext z
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_sum, ← Finset.mul_sum]
  apply Measure.pi_eq
  intro s hsets
  rw [tilted_apply' _ _ (MeasurableSet.univ_pi hsets), hnorm.2]
  change (∫⁻ z in Set.univ.pi s, ENNReal.ofReal
    (Real.exp (-ell * (∑ i, normalValue (z i))) / (inverseNormalizer ell w) ^ n)
    ∂Measure.pi (fun _ : Fin n => atomicMeasure w)) = _
  simp_rw [congrFun hdensity]
  rw [Measure.restrict_pi_pi]
  have hcoord (i : Fin n) : Integrable
      (fun x => Real.exp (-ell * normalValue x) / inverseNormalizer ell w)
      ((atomicMeasure w).restrict (s i)) :=
    (inverseExp_integrable ell w hw hs).integrableOn.div_const _
  have hprod := Integrable.fintype_prod hcoord
  rw [← ofReal_integral_eq_lintegral_ofReal hprod
    (Filter.Eventually.of_forall (fun z => Finset.prod_nonneg
      (fun i _ => div_nonneg (Real.exp_pos _).le hZ.le)))]
  rw [integral_fintype_prod_eq_prod (fun _ : Fin n =>
    fun x : ℝ => Real.exp (-ell * normalValue x) / inverseNormalizer ell w)]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg
    (fun x => div_nonneg (Real.exp_pos _).le hZ.le))]
  apply Finset.prod_congr rfl
  intro i _
  rw [originalMeasure, tilted_apply_eq_ofReal_integral' _ (hsets i)]
  rfl

theorem iid_event_change_of_measure (ell q : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (n : ℕ)
    (E : Set (Shao.Path n)) (hE : MeasurableSet E) :
  Real.exp ((n : ℝ) * saddleRate ell q w) *
      (Measure.pi (fun _ : Fin n => originalMeasure ell w)).real E =
    ∫ z, E.indicator (fun z => Real.exp (-ell * normalDeviation q z)) z
      ∂Measure.pi (fun _ : Fin n => atomicMeasure w) := by
  let := atomicMeasure_isProbabilityMeasure w hw hs
  let := originalMeasure_isProbabilityMeasure ell w hw hs
  have hZ := inverseNormalizer_pos ell w hw hs
  have hZn : 0 < (inverseNormalizer ell w) ^ n := pow_pos hZ n
  have hnorm := iid_inverseNormalizer ell w hw hs n
  have hprob : (Measure.pi (fun _ : Fin n => originalMeasure ell w)).real E =
      ∫ z in E, Real.exp (-ell * (∑ i, normalValue (z i))) /
        (inverseNormalizer ell w) ^ n
        ∂Measure.pi (fun _ : Fin n => atomicMeasure w) := by
    rw [measureReal_def, original_iid_eq_tilted ell w hw hs n,
      tilted_apply_eq_ofReal_integral' _ hE, hnorm.2]
    exact ENNReal.toReal_ofReal (integral_nonneg
      (fun z => div_nonneg (Real.exp_pos _).le hZn.le))
  have hrate : Real.exp ((n : ℝ) * saddleRate ell q w) =
      Real.exp ((n : ℝ) * (ell * q)) * (inverseNormalizer ell w) ^ n := by
    simp only [saddleRate, mul_add, Real.exp_add, Real.exp_nat_mul, Real.exp_log hZ]
  have hpoint (z : Shao.Path n) : Real.exp ((n : ℝ) * saddleRate ell q w) *
      (Real.exp (-ell * (∑ i, normalValue (z i))) / (inverseNormalizer ell w) ^ n) =
      Real.exp (-ell * normalDeviation q z) := by
    calc
      _ = Real.exp ((n : ℝ) * (ell * q)) *
          Real.exp (-ell * (∑ i, normalValue (z i))) := by
        rw [hrate]
        field_simp
      _ = Real.exp ((n : ℝ) * (ell * q) + -ell * (∑ i, normalValue (z i))) :=
        (Real.exp_add _ _).symm
      _ = _ := by congr 1; unfold normalDeviation; ring
  rw [hprob, ← integral_const_mul, integral_indicator hE]
  exact integral_congr_ae (Filter.Eventually.of_forall hpoint)

theorem normalizedTailCoefficient_eq_tilted (ell q : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (n : ℕ) :
  normalizedTailCoefficient ell q w n = tiltedTailCoefficient ell q w n := by
  unfold normalizedTailCoefficient tiltedTailCoefficient
  rw [mul_assoc, iid_event_change_of_measure ell q w hw hs n _ (sourceTail_measurable q n)]

theorem finite_limit_normalized_tail_error_le (ell : ℝ) (hell : 0 ≤ ell) (q : ℝ)
    (hq : q ≤ 2) (p : Fin 4 → ℝ) (r : ℕ → ℝ)
    (hr : ∀ j, 0 ≤ r j) (hs : Summable r) (J : ℕ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hl : ∀ i, 0 ≤ limitingBase ell p r i) (hj : ∀ i, 0 ≤ finiteBase ell p r J i)
    (n : ℕ) :
  |normalizedTailCoefficient ell q (limitingMass ell p r) n -
      normalizedTailCoefficient ell q (finiteMass ell p r J) n| ≤
    Real.sqrt (2 * Real.pi * (n : ℝ)) * Real.exp (11 * ell * (n : ℝ)) *
      (n : ℝ) * compensationTailConstant ell * (∑' j, r (J + j)) := by
  have hwl : ∀ i, 0 ≤ limitingMass ell p r i := by
    intro i
    cases i with
    | inl i => exact hl i
    | inr j => exact hr j
  have hwj := finiteMass_nonneg ell p r J hj hr
  have hml : HasSum (limitingMass ell p r) 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using
      limitingMoment_hasSum ell q hell p r hM hc hr hs 0
  have hmj : HasSum (finiteMass ell p r J) 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using
      finiteMass_constraints ell q p r J hM hc 0
  rw [normalizedTailCoefficient_eq_tilted ell q _ hwl hml n,
    normalizedTailCoefficient_eq_tilted ell q _ hwj hmj n]
  unfold tiltedTailCoefficient
  rw [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (mul_le_mul_of_nonneg_left
    (finite_limit_likelihood_tail_le ell hell q hq p r hr hs J hM hc hl hj n)
    (Real.sqrt_nonneg _)).trans_eq (by ring)

end
end Shao.OQ3
