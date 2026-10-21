import Shao.Basic.OrderedSelection
import Shao.Probability.FiniteIID
import Mathlib.Probability.ConditionalProbability

/-!
# Finite independent samples conditioned on fixed coordinate events

All conditional measures are the actual normalized restrictions `cond`. The
retained-set corollary conditions on one fixed mixed coordinate event and
enumerates its retained coordinates increasingly.
-/

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

variable {ι Ω α : Type*} [Fintype ι]
  [MeasurableSpace Ω] [MeasurableSpace α]

omit [Fintype ι] [MeasurableSpace α] in
private theorem coordinate_event_ne_zero_of_joint_ne_zero
    {μ : Measure Ω} {X : ι → Ω → α} {B : ι → Set α}
    (hA : μ (⋂ i, X i ⁻¹' B i) ≠ 0) (i : ι) :
    μ (X i ⁻¹' B i) ≠ 0 := by
  apply ne_of_gt
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hA)
    (measure_mono (Set.iInter_subset (fun j => X j ⁻¹' B j) i))

private theorem map_cond_preimage {μ : Measure Ω} {f : Ω → α}
    (hf : Measurable f) {B : Set α} (hB : MeasurableSet B) :
    Measure.map f (cond μ (f ⁻¹' B)) = cond (Measure.map f μ) B := by
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul _ hf.aemeasurable, ← Measure.restrict_map hf hB,
    Measure.map_apply hf hB]

private theorem indep_cond_coordinate_events
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → α}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (B : ι → Set α) (hB : ∀ i, MeasurableSet (B i))
    (hA : μ (⋂ i, X i ⁻¹' B i) ≠ 0) :
    iIndepFun X (cond μ (⋂ i, X i ⁻¹' B i)) := by
  have hpair : iIndepFun (fun i ω => (X i ω, X i ω)) μ :=
    hIndep.comp (fun _ z => (z, z)) (fun _ => measurable_id.prodMk measurable_id)
  exact iIndepFun.cond hX hpair
    (coordinate_event_ne_zero_of_joint_ne_zero hA) hB

private theorem indep_cond_coordinate_map
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → α}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (B : ι → Set α) (hB : ∀ i, MeasurableSet (B i))
    (hA : μ (⋂ i, X i ⁻¹' B i) ≠ 0) (i : ι) :
    Measure.map (X i) (cond μ (⋂ j, X j ⁻¹' B j)) =
      cond (Measure.map (X i) μ) (B i) := by
  classical
  rw [← map_cond_preimage (hX i) (hB i)]
  apply Measure.ext
  intro C hC
  rw [Measure.map_apply (hX i) hC, Measure.map_apply (hX i) hC]
  have hpair : iIndepFun (fun j ω => (X j ω, X j ω)) μ :=
    hIndep.comp (fun _ z => (z, z)) (fun _ => measurable_id.prodMk measurable_id)
  have hsingleton := cond_iInter (X := X) (Y := X) (s := {i})
    (f := fun j => X j ⁻¹' C) (t := B) hX hpair
    (fun _ _ => ⟨C, hC, rfl⟩)
    (fun j _ => coordinate_event_ne_zero_of_joint_ne_zero hA j) hB
  simpa using hsingleton

/-- Conditioning independent coordinates on fixed measurable coordinate events
gives the product of their genuine one-coordinate conditional laws. -/
theorem indep_cond_joint_map_eq_pi
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → α}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (B : ι → Set α) (hB : ∀ i, MeasurableSet (B i))
    (hA : μ (⋂ i, X i ⁻¹' B i) ≠ 0) :
    Measure.map (fun ω i => X i ω) (cond μ (⋂ i, X i ⁻¹' B i)) =
      Measure.pi (fun i => cond (Measure.map (X i) μ) (B i)) := by
  have hcond := indep_cond_coordinate_events hX hIndep B hB hA
  rw [hcond.map_fun_eq_pi_map (fun i => (hX i).aemeasurable)]
  congr 1
  funext i
  exact indep_cond_coordinate_map hX hIndep B hB hA i

/-- On a fixed positive-probability mixed membership event, a nonempty retained
sample is iid with the original common law conditioned on the good set. -/
theorem iid_retained_cond_coordinate_event
    {n : ℕ} {μ : Measure Ω} {ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (s : Finset (Fin n)) (hs : 0 < s.card)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hA : μ (⋂ i, X i ⁻¹' (if i ∈ s then B else Bᶜ)) ≠ 0) :
    ν B ≠ 0 ∧
    iIndepFun (fun r : Fin s.card => X (Shao.retainedIndex s r))
      (cond μ (⋂ i, X i ⁻¹' (if i ∈ s then B else Bᶜ))) ∧
    ∀ r : Fin s.card,
      IdentDistrib (X (Shao.retainedIndex s r)) (id : ℝ → ℝ)
        (cond μ (⋂ i, X i ⁻¹' (if i ∈ s then B else Bᶜ))) (cond ν B) := by
  classical
  let C : Fin n → Set ℝ := fun i => if i ∈ s then B else Bᶜ
  have hC : ∀ i, MeasurableSet (C i) := by
    intro i
    dsimp [C]
    split_ifs
    · exact hB
    · exact hB.compl
  have hmap : ∀ i, Measure.map (X i) μ = ν := by
    intro i
    simpa only [Measure.map_id] using (hLaw i).map_eq
  have hcond : iIndepFun X (cond μ (⋂ i, X i ⁻¹' C i)) :=
    indep_cond_coordinate_events hX hIndep C hC hA
  have hmarg : ∀ i,
      Measure.map (X i) (cond μ (⋂ j, X j ⁻¹' C j)) = cond ν (C i) := by
    intro i
    rw [indep_cond_coordinate_map hX hIndep C hC hA i, hmap i]
  have hBpos : ν B ≠ 0 := by
    let i : Fin n := Shao.retainedIndex s ⟨0, hs⟩
    have hi : i ∈ s := Shao.retainedIndex_mem s ⟨0, hs⟩
    have hp := coordinate_event_ne_zero_of_joint_ne_zero (B := C) hA i
    have hCi : C i = B := by simp [C, hi]
    rw [hCi, ← Measure.map_apply (hX i) hB, hmap i] at hp
    exact hp
  refine ⟨hBpos, hcond.precomp (Shao.retainedIndex s).injective, ?_⟩
  intro r
  have hr : Shao.retainedIndex s r ∈ s := Shao.retainedIndex_mem s r
  refine ⟨(hX (Shao.retainedIndex s r)).aemeasurable,
    measurable_id.aemeasurable, ?_⟩
  simpa [C, hr] using hmarg (Shao.retainedIndex s r)

end Shao.Probability
