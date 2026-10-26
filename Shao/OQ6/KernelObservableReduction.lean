import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

set_option autoImplicit false

universe u

namespace Shao.OQ6.KernelObservableReduction

noncomputable section

open scoped Classical MeasureTheory

/- Original p51 S1 observable-information prerequisite only.
   The original arbitrary observation sigma algebra is not assumed countably generated.
   The same h and scalar f are retained pointwise, including on empty spaces.
   No law, integral, statistic, scalar-code or CDF transport is asserted.
   Inherited p54 repair boundaries and Shao-Zhou (2016) attribution remain;
   this classical measurable reduction carries no novelty claim. -/

private theorem exists_countable_generators_for_measurableSet
    {X : Type u} (C : Set (Set X)) (s : Set X)
    (hs : MeasurableSet[MeasurableSpace.generateFrom C] s) :
    ∃ D : Set (Set X), D.Countable ∧ D ⊆ C ∧
      MeasurableSet[MeasurableSpace.generateFrom D] s := by
  classical
  refine MeasurableSpace.generateFrom_induction C
    (fun t _ => ∃ D : Set (Set X), D.Countable ∧ D ⊆ C ∧
      MeasurableSet[MeasurableSpace.generateFrom D] t)
    ?_ ?_ ?_ ?_ s hs
  · intro t ht _
    refine ⟨{t}, Set.countable_singleton t, ?_, ?_⟩
    · intro a ha
      have hat : a = t := Set.mem_singleton_iff.mp ha
      rw [hat]
      exact ht
    · exact MeasurableSpace.measurableSet_generateFrom
        (by simp only [Set.mem_singleton_iff])
  · exact ⟨∅, Set.countable_empty, Set.empty_subset C, @MeasurableSet.empty X (MeasurableSpace.generateFrom (∅ : Set (Set X)))⟩
  · intro t ht hrec
    rcases hrec with ⟨D, hDcount, hDsub, hDmeas⟩
    exact ⟨D, hDcount, hDsub, hDmeas.compl⟩
  · intro t ht hrec
    let D : ℕ → Set (Set X) := fun k => Classical.choose (hrec k)
    have hDcount (k : ℕ) : (D k).Countable :=
      (Classical.choose_spec (hrec k)).1
    have hDsub (k : ℕ) : D k ⊆ C :=
      (Classical.choose_spec (hrec k)).2.1
    have hDmeas (k : ℕ) :
        MeasurableSet[MeasurableSpace.generateFrom (D k)] (t k) :=
      (Classical.choose_spec (hrec k)).2.2
    let E : Set (Set X) := ⋃ k : ℕ, D k
    have hEcount : E.Countable := Set.countable_iUnion hDcount
    have hEsub : E ⊆ C := by
      intro a ha
      rcases Set.mem_iUnion.mp ha with ⟨k, hak⟩
      exact hDsub k hak
    have hDle (k : ℕ) :
        MeasurableSpace.generateFrom (D k) ≤ MeasurableSpace.generateFrom E :=
      MeasurableSpace.generateFrom_mono
        (fun a ha => Set.mem_iUnion.mpr ⟨k, ha⟩)
    refine ⟨E, hEcount, hEsub, ?_⟩
    exact MeasurableSet.iUnion (fun k => hDle k (t k) (hDmeas k))

theorem exists_countably_generated_observable_subspace
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (h : Ω → Ω → ℝ)
    (hh : Measurable[mΩ.prod mΩ, borel ℝ]
      (fun t : Ω × Ω => h t.1 t.2))
    (f : ℕ → Ω → ℝ)
    (hf : ∀ k : ℕ, Measurable[mΩ, borel ℝ] (f k)) :
    ∃ m₀ : MeasurableSpace Ω,
      m₀ ≤ mΩ ∧
      @MeasurableSpace.CountablyGenerated Ω m₀ ∧
      Measurable[m₀.prod m₀, borel ℝ]
        (fun t : Ω × Ω => h t.1 t.2) ∧
      ∀ k : ℕ, Measurable[m₀, borel ℝ] (f k) := by
  classical
  let B : ℕ → Set ℝ := MeasurableSpace.natGeneratingSequence ℝ
  have hBgen : MeasurableSpace.generateFrom (Set.range B) = borel ℝ := by
    change MeasurableSpace.generateFrom
      (Set.range (MeasurableSpace.natGeneratingSequence ℝ)) = borel ℝ
    have hReal : (inferInstance : MeasurableSpace ℝ) = borel ℝ :=
      BorelSpace.measurable_eq
    exact (MeasurableSpace.generateFrom_natGeneratingSequence ℝ).trans hReal
  have hBmeas (k : ℕ) : MeasurableSet[borel ℝ] (B k) := by
    rw [← hBgen]
    exact MeasurableSpace.measurableSet_generateFrom ⟨k, rfl⟩
  let R : Set (Set (Ω × Ω)) :=
    Set.image2 (fun A B : Set Ω => A ×ˢ B)
      {A : Set Ω | MeasurableSet[mΩ] A}
      {A : Set Ω | MeasurableSet[mΩ] A}
  have hRgen : MeasurableSpace.generateFrom R = mΩ.prod mΩ :=
    @generateFrom_prod Ω Ω mΩ mΩ
  have hSupport (k : ℕ) :
      ∃ D : Set (Set (Ω × Ω)), D.Countable ∧ D ⊆ R ∧
        MeasurableSet[MeasurableSpace.generateFrom D]
          ((fun t : Ω × Ω => h t.1 t.2) ⁻¹' B k) := by
    apply exists_countable_generators_for_measurableSet R
    rw [hRgen]
    exact hh (hBmeas k)
  let D : ℕ → Set (Set (Ω × Ω)) := fun k => Classical.choose (hSupport k)
  have hDcount (k : ℕ) : (D k).Countable :=
    (Classical.choose_spec (hSupport k)).1
  have hDsub (k : ℕ) : D k ⊆ R :=
    (Classical.choose_spec (hSupport k)).2.1
  have hDmeas (k : ℕ) :
      MeasurableSet[MeasurableSpace.generateFrom (D k)]
        ((fun t : Ω × Ω => h t.1 t.2) ⁻¹' B k) :=
    (Classical.choose_spec (hSupport k)).2.2
  let T : Set (Set (Ω × Ω)) := ⋃ k : ℕ, D k
  have hTcount : T.Countable := Set.countable_iUnion hDcount
  have hTsub : T ⊆ R := by
    intro s hs
    rcases Set.mem_iUnion.mp hs with ⟨k, hsk⟩
    exact hDsub k hsk
  let : Countable T := hTcount.to_subtype
  have hSides (selected : T) :
      ∃ A B : Set Ω, MeasurableSet[mΩ] A ∧ MeasurableSet[mΩ] B ∧
        selected.val = A ×ˢ B := by
    have hselected : selected.val ∈ R := hTsub selected.property
    change selected.val ∈ Set.image2 (fun A B : Set Ω => A ×ˢ B)
      {A : Set Ω | MeasurableSet[mΩ] A}
      {A : Set Ω | MeasurableSet[mΩ] A} at hselected
    rcases hselected with ⟨A, hA, B, hB, hAB⟩
    exact ⟨A, B, hA, hB, hAB.symm⟩
  let leftSide : T → Set Ω := fun selected => Classical.choose (hSides selected)
  let rightSide : T → Set Ω := fun selected =>
    Classical.choose (Classical.choose_spec (hSides selected))
  have hSideSpec (selected : T) :
      MeasurableSet[mΩ] (leftSide selected) ∧
      MeasurableSet[mΩ] (rightSide selected) ∧
      selected.val = leftSide selected ×ˢ rightSide selected :=
    Classical.choose_spec (Classical.choose_spec (hSides selected))
  let scalarPreimage : (ℕ × ℕ) → Set Ω :=
    fun kj => (f kj.1) ⁻¹' B kj.2
  let G : Set (Set Ω) :=
    (Set.range leftSide ∪ Set.range rightSide) ∪ Set.range scalarPreimage
  have hGcount : G.Countable :=
    ((Set.countable_range leftSide).union (Set.countable_range rightSide)).union
      (Set.countable_range scalarPreimage)
  have hGmeas : ∀ A ∈ G, MeasurableSet[mΩ] A := by
    intro A hA
    rcases hA with (hA | hA) | hA
    · rcases hA with ⟨selected, rfl⟩
      exact (hSideSpec selected).1
    · rcases hA with ⟨selected, rfl⟩
      exact (hSideSpec selected).2.1
    · rcases hA with ⟨kj, rfl⟩
      exact hf kj.1 (hBmeas kj.2)
  let m₀ : MeasurableSpace Ω := MeasurableSpace.generateFrom G
  have hm₀le : m₀ ≤ mΩ := MeasurableSpace.generateFrom_le hGmeas
  have hm₀count : @MeasurableSpace.CountablyGenerated Ω m₀ :=
    ⟨⟨G, hGcount, rfl⟩⟩
  have hLeftMeas (selected : T) :
      MeasurableSet[m₀] (leftSide selected) := by
    apply MeasurableSpace.measurableSet_generateFrom
    exact Or.inl (Or.inl ⟨selected, rfl⟩)
  have hRightMeas (selected : T) :
      MeasurableSet[m₀] (rightSide selected) := by
    apply MeasurableSpace.measurableSet_generateFrom
    exact Or.inl (Or.inr ⟨selected, rfl⟩)
  have hScalarMeas (k j : ℕ) :
      MeasurableSet[m₀] ((f k) ⁻¹' B j) := by
    apply MeasurableSpace.measurableSet_generateFrom
    exact Or.inr ⟨(k, j), rfl⟩
  have hTmeas : ∀ s ∈ T, MeasurableSet[m₀.prod m₀] s := by
    intro s hs
    let selected : T := ⟨s, hs⟩
    have hEq : s = leftSide selected ×ˢ rightSide selected :=
      (hSideSpec selected).2.2
    rw [hEq]
    exact @MeasurableSet.prod Ω Ω m₀ m₀ (leftSide selected)
      (rightSide selected) (hLeftMeas selected) (hRightMeas selected)
  have hDle (k : ℕ) : MeasurableSpace.generateFrom (D k) ≤ m₀.prod m₀ :=
    MeasurableSpace.generateFrom_le
      (fun s hs => hTmeas s (Set.mem_iUnion.mpr ⟨k, hs⟩))
  have hh₀ : Measurable[m₀.prod m₀, borel ℝ]
      (fun t : Ω × Ω => h t.1 t.2) := by
    apply measurable_iff_comap_le.mpr
    rw [← hBgen, MeasurableSpace.comap_generateFrom]
    apply MeasurableSpace.generateFrom_le
    rintro s ⟨U, hU, rfl⟩
    rcases hU with ⟨k, rfl⟩
    exact hDle k _ (hDmeas k)
  refine ⟨m₀, hm₀le, hm₀count, hh₀, ?_⟩
  intro k
  apply measurable_iff_comap_le.mpr
  rw [← hBgen, MeasurableSpace.comap_generateFrom]
  apply MeasurableSpace.generateFrom_le
  rintro s ⟨U, hU, rfl⟩
  rcases hU with ⟨j, rfl⟩
  exact hScalarMeas k j

end

end Shao.OQ6.KernelObservableReduction
