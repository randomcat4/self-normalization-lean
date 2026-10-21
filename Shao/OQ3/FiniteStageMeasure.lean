import Shao.OQ3.InverseTilt

/-!
# Finite original laws sharing their parameters with the limiting law

Source: current/oq3/proofs/r1/report.md, lines 113-145.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U3c scope: 1693b5970255be976c08172fff0dab38afd4d9669f0a0774bba8bbd1f1d80d88.
-/

namespace Shao.OQ3

open MeasureTheory
open scoped Matrix

noncomputable section

def finiteMass (ell : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ) (J : ℕ) : AtomicIndex → ℝ :=
  Sum.elim (finiteBase ell p r J) (fun j => if j < J then r j else 0)

theorem finiteMass_constraints (ell q : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ) (J : ℕ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q) :
  ∀ k, HasSum (fun i => finiteMass ell p r J i * constraintFeature ell (fixedAtom i) k)
    (constraintTarget q k) := by
  classical
  have hv : (constraintMatrix ell) *ᵥ finiteBase ell p r J +
      addedMoment ell (fun j : Fin J => addedAtom j.val) (fun j : Fin J => r j.val) =
      constraintTarget q := by
    rw [finiteBase, compensatedBase, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec, hc]
    exact sub_add_cancel _ _
  intro k
  have hnat : HasSum (fun j : ℕ => (if j < J then r j else 0) *
      constraintFeature ell (addedAtom j) k)
      (addedMoment ell (fun j : Fin J => addedAtom j.val) (fun j : Fin J => r j.val) k) := by
    have hh : HasSum (fun j : ℕ => (if j < J then r j else 0) *
        constraintFeature ell (addedAtom j) k)
        (∑ j ∈ Finset.range J, (if j < J then r j else 0) *
          constraintFeature ell (addedAtom j) k) := by
      apply hasSum_sum_of_ne_finset_zero
      intro j hj
      have hnot : ¬j < J := by simpa only [Finset.mem_range] using hj
      simp [hnot]
    convert hh using 1
    unfold addedMoment
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    simp only [ite_eq_left j.isLt]
  have hsum : HasSum (fun i => finiteMass ell p r J i *
      constraintFeature ell (fixedAtom i) k)
      (((constraintMatrix ell) *ᵥ finiteBase ell p r J) k +
        addedMoment ell (fun j : Fin J => addedAtom j.val) (fun j : Fin J => r j.val) k) := by
    apply HasSum.sum
    · simpa [finiteMass, fixedAtom, Function.comp_def, constraintMatrix,
        Matrix.mulVec, dotProduct, mul_comm] using
        (hasSum_fintype (fun i : Fin 4 =>
          finiteBase ell p r J i * constraintFeature ell (baseAtom i) k))
    · simpa [finiteMass, fixedAtom, Function.comp_def] using hnat
  exact congrFun hv k ▸ hsum

theorem exists_uniform_finite_radius (ell : ℝ) (hell : 0 ≤ ell) (p : Fin 4 → ℝ)
    (hp : ∀ i, 0 < p i) :
  ∃ eps : ℝ, 0 < eps ∧ ∀ (r : ℕ → ℝ),
    (∀ j, 0 ≤ r j) → Summable r → (∑' j, r j) < eps →
    ∀ (J : ℕ) (i : Fin 4), 0 < finiteBase ell p r J i := by
  obtain ⟨eps, heps, hrad⟩ := exists_compensation_radius ell p hp
    ((4 + Real.sqrt 10) ^ 2) (sq_nonneg _)
  refine ⟨eps, heps, ?_⟩
  intro r hr hs ht J i
  have hsum : (∑ j : Fin J, r j.val) < eps := by
    rw [Fin.sum_univ_eq_sum_range]
    exact (hs.sum_le_tsum (Finset.range J) (fun j _ => hr j)).trans_lt ht
  exact hrad J (fun j => addedAtom j.val) (fun j => r j.val)
    (fun j => hr j.val) (fun j k => addedAtom_feature_bound ell hell j.val k) hsum i

theorem finiteMass_nonneg (ell : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ) (J : ℕ)
    (hp : ∀ i, 0 ≤ finiteBase ell p r J i) (hr : ∀ j, 0 ≤ r j) :
  ∀ i, 0 ≤ finiteMass ell p r J i := by
  intro i
  cases i with
  | inl i => exact hp i
  | inr j =>
    change 0 ≤ if j < J then r j else 0
    split_ifs
    · exact hr j
    · exact le_rfl

theorem atomicMeasure_finiteMass_ae_range (ell : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ) (J : ℕ) :
  ∀ᵐ x ∂atomicMeasure (finiteMass ell p r J),
    x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i) := by
  have hset : MeasurableSet (Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i)) :=
    (Set.countable_range _).measurableSet
  apply Measure.ae_sum_iff.mpr
  intro i
  cases i with
  | inl i =>
    apply Measure.ae_smul_measure
    exact (ae_dirac_iff hset).mpr ⟨Sum.inl i, rfl⟩
  | inr j =>
    by_cases hj : j < J
    · apply Measure.ae_smul_measure
      exact (ae_dirac_iff hset).mpr ⟨Sum.inr ⟨j, hj⟩, rfl⟩
    · simp [finiteMass, hj]

theorem originalMeasure_finiteMass_ae_range (ell : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ) (J : ℕ) :
  ∀ᵐ x ∂originalMeasure ell (finiteMass ell p r J),
    x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i) := by
  exact (tilted_absolutelyContinuous (atomicMeasure (finiteMass ell p r J))
    (fun x => -ell * normalValue x)).ae_le (atomicMeasure_finiteMass_ae_range ell p r J)

theorem finite_original_properties (ell q : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ) (J : ℕ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hp : ∀ i, 0 ≤ finiteBase ell p r J i) (hr : ∀ j, 0 ≤ r j) :
  IsProbabilityMeasure (originalMeasure ell (finiteMass ell p r J)) ∧
    (Integrable (fun x : ℝ => x) (originalMeasure ell (finiteMass ell p r J)) ∧
      (∫ x, x ∂originalMeasure ell (finiteMass ell p r J)) = 0) ∧
    (∀ᵐ x ∂originalMeasure ell (finiteMass ell p r J),
      1 ≤ |x| ∧ |x| ≤ 4 + Real.sqrt 10) ∧
    (originalMeasure ell (finiteMass ell p r J)).tilted
      (fun x => ell * normalValue x) = atomicMeasure (finiteMass ell p r J) := by
  have hw := finiteMass_nonneg ell p r J hp hr
  have hm := finiteMass_constraints ell q p r J hM hc
  have hmass : HasSum (finiteMass ell p r J) 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  exact ⟨originalMeasure_isProbabilityMeasure _ _ hw hmass,
    originalMeasure_centered ell q _ hw hm, originalMeasure_ae_bounds _ _,
    originalMeasure_retilt _ _ hw hmass⟩

theorem finite_original_atom_pos (ell q : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ) (J : ℕ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hp : ∀ i, 0 < finiteBase ell p r J i) (hr : ∀ j, 0 < r j)
    (i : Fin 4 ⊕ Fin J) :
  0 < (originalMeasure ell (finiteMass ell p r J)).real
    {stageAtom (fun j : Fin J => addedAtom j.val) i} := by
  have hw := finiteMass_nonneg ell p r J (fun i => (hp i).le) (fun j => (hr j).le)
  have hm := finiteMass_constraints ell q p r J hM hc
  have hmass : HasSum (finiteMass ell p r J) 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  cases i with
  | inl i =>
    have hi : 0 < finiteMass ell p r J (Sum.inl i) := hp i
    simpa [stageAtom, fixedAtom] using
      originalMeasure_atom_pos ell _ hw hmass (Sum.inl i) hi
  | inr j =>
    have hi : 0 < finiteMass ell p r J (Sum.inr j.val) := by
      simpa [finiteMass, j.isLt] using hr j.val
    simpa [stageAtom, fixedAtom] using
      originalMeasure_atom_pos ell _ hw hmass (Sum.inr j.val) hi

theorem exists_source_finite_and_limit_family :
  ∃ (p : Fin 4 → ℝ) (q eps : ℝ), (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧
    0 < eps ∧ (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
    ∀ (r : ℕ → ℝ), (∀ j, 0 < r j) → Summable r → (∑' j, r j) < eps →
      (∀ i, 0 < limitingMass sourceEll p r i) ∧
      (∀ k, HasSum (fun i => limitingMass sourceEll p r i *
        constraintFeature sourceEll (fixedAtom i) k) (constraintTarget q k)) ∧
      ∀ J : ℕ, (∀ i, 0 < finiteBase sourceEll p r J i) ∧
        (∀ k, HasSum (fun i => finiteMass sourceEll p r J i *
          constraintFeature sourceEll (fixedAtom i) k) (constraintTarget q k)) ∧
        IsProbabilityMeasure (originalMeasure sourceEll (finiteMass sourceEll p r J)) ∧
        (Integrable (fun x : ℝ => x) (originalMeasure sourceEll (finiteMass sourceEll p r J)) ∧
          (∫ x, x ∂originalMeasure sourceEll (finiteMass sourceEll p r J)) = 0) ∧
        (∀ᵐ x ∂originalMeasure sourceEll (finiteMass sourceEll p r J),
          x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
            stageAtom (fun j : Fin J => addedAtom j.val) i)) := by
  obtain ⟨p, q, hp, hlo, hhi, hc⟩ := exists_source_starter
  obtain ⟨epsf, hepsf, hfinite⟩ := exists_uniform_finite_radius sourceEll sourceEll_pos.le p hp
  obtain ⟨epsl, hepsl, hlimit⟩ := exists_limiting_radius sourceEll sourceEll_pos.le p hp
  refine ⟨p, q, min epsf epsl, hp, hlo, hhi, lt_min hepsf hepsl, hc, ?_⟩
  intro r hr hs ht
  have hnonneg := fun j => (hr j).le
  have hf := hfinite r hnonneg hs (ht.trans_le (min_le_left _ _))
  refine ⟨limitingMass_pos_of_lower sourceEll p r hp hr
    (hlimit r hnonneg hs (ht.trans_le (min_le_right _ _))),
    (fun k => limitingMoment_hasSum sourceEll q sourceEll_pos.le p r
      source_constraintMatrix_nonsingular hc hnonneg hs k), ?_⟩
  intro J
  have hm := finiteMass_constraints sourceEll q p r J source_constraintMatrix_nonsingular hc
  have hprops := finite_original_properties sourceEll q p r J
    source_constraintMatrix_nonsingular hc (fun i => (hf J i).le) hnonneg
  exact ⟨hf J, hm, hprops.1, hprops.2.1, originalMeasure_finiteMass_ae_range _ _ _ _⟩

end
end Shao.OQ3
