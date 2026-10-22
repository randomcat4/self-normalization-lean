import Shao.OQ3.FiniteStageMeasure
import Shao.OQ3.PositiveRate

/-!
# The actual finite law determined by a finite positive prefix

Source: current/oq3/proofs/r1/report.md, lines 113–145 and 486–550.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U17p scope63. The uniform radius precedes all stages and prefixes.
-/

namespace Shao.OQ3
open MeasureTheory Filter
open scoped Matrix Topology BigOperators
noncomputable section

def prefixMass (ell : ℝ) (p : Fin 4 → ℝ) (J : ℕ) (u : Fin J → ℝ) : AtomicIndex → ℝ :=
  finiteMass ell p (fun j => if hj : j < J then u ⟨j, hj⟩ else 0) J

private theorem prefix_sequence_hasSum (J : ℕ) (u : Fin J → ℝ) :
    HasSum (fun j => if hj : j < J then u ⟨j, hj⟩ else 0) (∑ i, u i) := by
  classical
  let s : ℕ → ℝ := fun j => if hj : j < J then u ⟨j, hj⟩ else 0
  change HasSum s (∑ i, u i)
  have hh : HasSum s (∑ j ∈ Finset.range J, s j) := by
    apply hasSum_sum_of_ne_finset_zero
    intro j hj
    have hnot : ¬j < J := by simpa only [Finset.mem_range] using hj
    simp [s, hnot]
  convert hh using 1
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl (fun i _ => by simp [s, i.isLt])

theorem finiteMass_eq_prefixMass (ell : ℝ) (p : Fin 4 → ℝ) (J : ℕ)
    (u : Fin J → ℝ) (r : ℕ → ℝ) (hpref : ∀ i : Fin J, r i.val = u i) :
    finiteMass ell p r J = prefixMass ell p J u := by
  let s : ℕ → ℝ := fun j => if hj : j < J then u ⟨j, hj⟩ else 0
  change finiteMass ell p r J = finiteMass ell p s J
  have hrestrict : (fun j : Fin J => r j.val) = (fun j : Fin J => s j.val) := by
    funext j
    simpa [s, j.isLt] using hpref j
  have hb : finiteBase ell p r J = finiteBase ell p s J := by
    unfold finiteBase
    rw [hrestrict]
  funext i
  cases i with
  | inl i => change finiteBase ell p r J i = finiteBase ell p s J i; rw [hb]
  | inr j =>
    change (if j < J then r j else 0) = if j < J then s j else 0
    by_cases hj : j < J
    · simp only [if_pos hj]
      exact congrFun hrestrict ⟨j, hj⟩
    · simp [hj]

theorem exists_source_prefix_radius (p : Fin 4 → ℝ) (q : ℝ)
    (hp : ∀ i, 0 < p i)
    (hc : (constraintMatrix sourceEll) *ᵥ p = constraintTarget q) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ (J : ℕ) (u : Fin J → ℝ),
      (∀ i, 0 < u i) → (∑ i, u i) < eps →
      (∀ i : AtomicIndex, 0 ≤ prefixMass sourceEll p J u i) ∧
      HasSum (prefixMass sourceEll p J u) 1 ∧
      (∫ x : ℝ, normalValue x ∂atomicMeasure (prefixMass sourceEll p J u)) = q ∧
      (∫ x : ℝ, x ∂atomicMeasure (prefixMass sourceEll p J u)) = q / 4 ∧
      (∀ᵐ x ∂atomicMeasure (prefixMass sourceEll p J u),
        x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
          stageAtom (fun j : Fin J => addedAtom j.val) i)) ∧
      (∀ i : Fin 4 ⊕ Fin J, 0 < (atomicMeasure (prefixMass sourceEll p J u)).real
        {stageAtom (fun j : Fin J => addedAtom j.val) i}) := by
  obtain ⟨eps, heps, hfinite⟩ := exists_uniform_finite_radius sourceEll sourceEll_pos.le p hp
  refine ⟨eps, heps, ?_⟩
  intro J u hu hsu
  let s : ℕ → ℝ := fun j => if hj : j < J then u ⟨j, hj⟩ else 0
  have hss : HasSum s (∑ i, u i) := prefix_sequence_hasSum J u
  have hnonneg : ∀ j, 0 ≤ s j := by
    intro j
    dsimp only [s]
    split_ifs with hj
    · exact (hu ⟨j, hj⟩).le
    · exact le_rfl
  have hsmall : (∑' j, s j) < eps := by rw [hss.tsum_eq]; exact hsu
  have hbase : ∀ i, 0 < finiteBase sourceEll p s J i :=
    hfinite s hnonneg hss.summable hsmall J
  let w : AtomicIndex → ℝ := prefixMass sourceEll p J u
  have hw : ∀ i, 0 ≤ w i :=
    finiteMass_nonneg sourceEll p s J (fun i => (hbase i).le) hnonneg
  have hm := finiteMass_constraints sourceEll q p s J source_constraintMatrix_nonsingular hc
  have hmass : HasSum w 1 := by
    change HasSum (finiteMass sourceEll p s J) 1
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  refine ⟨hw, hmass, ?_, ?_, ?_, ?_⟩
  · exact (atomicMeasure_normalValue sourceEll q w hw hm).2
  · exact (atomicMeasure_mean sourceEll q w hw hm).2
  · exact atomicMeasure_finiteMass_ae_range sourceEll p s J
  · intro i
    cases i with
    | inl i =>
      change 0 < (atomicMeasure w).real {fixedAtom (Sum.inl i)}
      rw [atomicMeasure_real_singleton w hw]
      change 0 < finiteBase sourceEll p s J i
      exact hbase i
    | inr j =>
      change 0 < (atomicMeasure w).real {fixedAtom (Sum.inr j.val)}
      rw [atomicMeasure_real_singleton w hw]
      change 0 < (if j.val < J then s j.val else 0)
      simpa [s, j.isLt] using hu j

end
end Shao.OQ3
