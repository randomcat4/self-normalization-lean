import Shao.OQ3.SummableAtoms
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The fixed atomic tilted law and its integrable constraints

Source: current/oq3/proofs/r1/report.md, lines 127-153.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U3b scope: 23b4e846a76bbc1f88a8e286a7baf6451e70f4c002f125125c746174269172d2.
This constructs the tilted law pi. The inverse-tilted original law is a
separate subsequent construction.
-/

namespace Shao.OQ3

open MeasureTheory
open scoped Matrix

noncomputable section

def atomicMeasure (w : AtomicIndex → ℝ) : Measure ℝ :=
  Measure.sum fun i => ENNReal.ofReal (w i) • Measure.dirac (fixedAtom i)

theorem atomicMeasure_singleton (w : AtomicIndex → ℝ) (i : AtomicIndex) :
    atomicMeasure w {fixedAtom i} = ENNReal.ofReal (w i) := by
  classical
  rw [atomicMeasure, Measure.sum_apply _ (measurableSet_singleton _)]
  rw [tsum_eq_single i]
  · simp
  · intro j hji
    have hne : fixedAtom j ≠ fixedAtom i := fun h => hji (fixedAtom_injective h)
    simp [hne]

theorem atomicMeasure_real_singleton (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (i : AtomicIndex) :
    (atomicMeasure w).real {fixedAtom i} = w i := by
  rw [measureReal_def, atomicMeasure_singleton, ENNReal.toReal_ofReal (hw i)]

theorem atomicMeasure_isProbabilityMeasure (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) :
    IsProbabilityMeasure (atomicMeasure w) :=
  HasSum.isProbabilityMeasure_sum_dirac hw hs

theorem atomicMeasure_ae_range (w : AtomicIndex → ℝ) :
    ∀ᵐ x ∂atomicMeasure w, x ∈ Set.range fixedAtom := by
  apply Measure.ae_sum_iff.mpr
  intro i
  apply Measure.ae_smul_measure
  exact (ae_dirac_iff (Set.countable_range fixedAtom).measurableSet).mpr ⟨i, rfl⟩

theorem atomicMeasure_ae_bounds (w : AtomicIndex → ℝ) :
    ∀ᵐ x ∂atomicMeasure w, 1 ≤ |x| ∧ |x| ≤ 4 + Real.sqrt 10 := by
  filter_upwards [atomicMeasure_ae_range w] with x hx
  obtain ⟨i, rfl⟩ := hx
  exact fixedAtom_bounds i

theorem integrable_atomicMeasure_iff (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (f : ℝ → ℝ) :
    Integrable f (atomicMeasure w) ↔
      Summable (fun i => w i * ‖f (fixedAtom i)‖) := by
  unfold atomicMeasure
  simpa only [ENNReal.toReal_ofReal (hw _)] using
    (integrable_sum_dirac_iff (f := f) (x := fixedAtom)
      (c := fun i => ENNReal.ofReal (w i)) (fun _ => ENNReal.ofReal_ne_top))

theorem integral_atomicMeasure (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (f : ℝ → ℝ) (hf : Integrable f (atomicMeasure w)) :
    (∫ x, f x ∂atomicMeasure w) = ∑' i, w i * f (fixedAtom i) := by
  have hs : Summable (fun i =>
      (ENNReal.ofReal (w i)).toReal * ‖f (fixedAtom i)‖) := by
    simpa only [ENNReal.toReal_ofReal (hw _)] using
      (integrable_atomicMeasure_iff w hw f).mp hf
  simpa only [atomicMeasure, ENNReal.toReal_ofReal (hw _), smul_eq_mul] using
    (integral_sum_dirac_eq_tsum (f := f) (x := fixedAtom)
      (c := fun i => ENNReal.ofReal (w i)) (fun _ => ENNReal.ofReal_ne_top) hs)

theorem atomicMeasure_integral_of_hasSum (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (f : ℝ → ℝ) (z : ℝ)
    (hs : HasSum (fun i => w i * f (fixedAtom i)) z) :
    Integrable f (atomicMeasure w) ∧ (∫ x, f x ∂atomicMeasure w) = z := by
  have hnorm : Summable (fun i => w i * ‖f (fixedAtom i)‖) := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw _)] using hs.summable.abs
  have hf := (integrable_atomicMeasure_iff w hw f).mpr hnorm
  exact ⟨hf, (integral_atomicMeasure w hw f hf).trans hs.tsum_eq⟩

theorem atomicMeasure_constraints (ell q : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) :
    ∀ k, Integrable (fun x => constraintFeature ell x k) (atomicMeasure w) ∧
      (∫ x, constraintFeature ell x k ∂atomicMeasure w) = constraintTarget q k := by
  intro k
  exact atomicMeasure_integral_of_hasSum w hw
    (fun x => constraintFeature ell x k) (constraintTarget q k) (hm k)

theorem atomicMeasure_mean (ell q : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) :
    Integrable (fun x : ℝ => x) (atomicMeasure w) ∧
      (∫ x, x ∂atomicMeasure w) = q / 4 := by
  have hsum : HasSum (fun i => w i * fixedAtom i) (q / 4) := by
    convert ((hm 3).sub (hm 1)).div_const 4 using 1
    · funext i
      change w i * fixedAtom i =
        (w i * fixedAtom i ^ 2 - w i * (fixedAtom i ^ 2 - 4 * fixedAtom i)) / 4
      ring
    · norm_num [constraintTarget]
  exact atomicMeasure_integral_of_hasSum w hw (fun x => x) (q / 4) hsum

theorem exists_source_measure_family :
    ∃ (p : Fin 4 → ℝ) (q eps : ℝ), (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧
      0 < eps ∧ (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
      ∀ (r : ℕ → ℝ), (∀ j, 0 < r j) → Summable r → (∑' j, r j) < eps →
        IsProbabilityMeasure (atomicMeasure (limitingMass sourceEll p r)) ∧
        (∀ i, (atomicMeasure (limitingMass sourceEll p r)).real {fixedAtom i} =
          limitingMass sourceEll p r i ∧ 0 < limitingMass sourceEll p r i) ∧
        (∀ k, Integrable (fun x => constraintFeature sourceEll x k)
          (atomicMeasure (limitingMass sourceEll p r)) ∧
          (∫ x, constraintFeature sourceEll x k ∂atomicMeasure (limitingMass sourceEll p r)) =
            constraintTarget q k) ∧
        (Integrable (fun x : ℝ => x) (atomicMeasure (limitingMass sourceEll p r)) ∧
          (∫ x, x ∂atomicMeasure (limitingMass sourceEll p r)) = q / 4) ∧
        (∀ᵐ x ∂atomicMeasure (limitingMass sourceEll p r),
          1 ≤ |x| ∧ |x| ≤ 4 + Real.sqrt 10) := by
  obtain ⟨p, q, eps, hp, hlo, hhi, heps, hc, hfamily⟩ := exists_source_limit_family
  refine ⟨p, q, eps, hp, hlo, hhi, heps, hc, ?_⟩
  intro r hr hs ht
  obtain ⟨hpos, hm⟩ := hfamily r hr hs ht
  have hnonneg := fun i => (hpos i).le
  have hmass : HasSum (limitingMass sourceEll p r) 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  exact ⟨atomicMeasure_isProbabilityMeasure _ hnonneg hmass,
    fun i => ⟨atomicMeasure_real_singleton _ hnonneg i, hpos i⟩,
    atomicMeasure_constraints sourceEll q _ hnonneg hm,
    atomicMeasure_mean sourceEll q _ hnonneg hm, atomicMeasure_ae_bounds _⟩

end
end Shao.OQ3
