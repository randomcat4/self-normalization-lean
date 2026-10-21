import Shao.Probability.ConditionalIID

/-!
# The actual retained index set and its fixed fibers

`retentionSet X B` is the good/retained set. The deleted set in the source is
its complement, obtained by using `Bᶜ`. Conditional iid is asserted only on a
fixed positive-probability fiber with a nonempty retained set.
-/

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

variable {n : ℕ} {Ω : Type*}

/-- Actual indices whose observed values lie in the good set. -/
noncomputable def retentionSet (X : Fin n → Ω → ℝ) (B : Set ℝ) (ω : Ω) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => X i ω ∈ B)

/-- The true fixed fiber is exactly the mixed coordinate event. -/
theorem retentionSet_eq_event (X : Fin n → Ω → ℝ) (B : Set ℝ)
    (s : Finset (Fin n)) :
    {ω | retentionSet X B ω = s} =
      ⋂ i, X i ⁻¹' (if i ∈ s then B else Bᶜ) := by
  classical
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
  constructor
  · intro h i
    by_cases hi : i ∈ s
    · have hmem : i ∈ retentionSet X B ω := h.symm ▸ hi
      simpa [retentionSet, hi] using hmem
    · have hnot : i ∉ retentionSet X B ω := by
        intro hmem
        exact hi (h ▸ hmem)
      simpa [retentionSet, hi] using hnot
  · intro h
    apply Finset.ext
    intro i
    by_cases hi : i ∈ s
    · have hgood : X i ω ∈ B := by simpa [hi] using h i
      simp [retentionSet, hi, hgood]
    · have hbad : X i ω ∉ B := by simpa [hi] using h i
      simp [retentionSet, hi, hbad]

/-- Selecting the bad set gives the exact complement of the retained set. -/
theorem retentionSet_compl (X : Fin n → Ω → ℝ) (B : Set ℝ) (ω : Ω) :
    retentionSet X Bᶜ ω = (retentionSet X B ω)ᶜ := by
  classical
  ext i
  simp [retentionSet]

variable [MeasurableSpace Ω]

/-- Every fixed fiber of the actual selector is measurable. -/
theorem measurableSet_retentionSet_eq {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (B : Set ℝ) (hB : MeasurableSet B)
    (s : Finset (Fin n)) : MeasurableSet {ω | retentionSet X B ω = s} := by
  rw [retentionSet_eq_event]
  apply MeasurableSet.iInter
  intro i
  apply hX i
  split_ifs
  · exact hB
  · exact hB.compl

/-- On one fixed positive-probability retained-set fiber, its increasing sample
is iid with the original common law conditioned on the good set. -/
theorem iid_retained_cond_retentionSet_eq
    {μ : Measure Ω} {ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (s : Finset (Fin n)) (hs : 0 < s.card)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hA : μ {ω | retentionSet X B ω = s} ≠ 0) :
    ν B ≠ 0 ∧
    iIndepFun (fun r : Fin s.card => X (Shao.retainedIndex s r))
      (cond μ {ω | retentionSet X B ω = s}) ∧
    ∀ r : Fin s.card,
      IdentDistrib (X (Shao.retainedIndex s r)) (id : ℝ → ℝ)
        (cond μ {ω | retentionSet X B ω = s}) (cond ν B) := by
  rw [retentionSet_eq_event X B s] at hA
  simpa only [retentionSet_eq_event X B s] using
    iid_retained_cond_coordinate_event hX hIndep hLaw s hs B hB hA

end Shao.Probability
