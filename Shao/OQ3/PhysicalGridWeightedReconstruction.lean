import Shao.OQ3.ParabolaGridCardinality
import Shao.OQ3.StandardizedCellChangeOfMeasure

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology BigOperators
noncomputable section

theorem iid_parabola_finite_grid_weighted_reconstruction
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (n : ℕ) (hn : 1 ≤ n)
    (level a0 rho : ℝ) (hrho : 0 ≤ rho) :
    let V : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
    let cell : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k =>
      (Set.Ioc ((k.1 : ℝ) / (n : ℝ)) (((k.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
       Set.Ioc ((k.2 : ℝ) / (n : ℝ)) (((k.2 : ℝ) + 1) / (n : ℝ))) ∩ V
    let C : ℝ := (2 * rho + 2) * ((|a0| + rho) ^ 2 / level ^ 2 + rho + 2)
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
    let M : Shao.Path n → (ℝ × ℝ) := fun z =>
      ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
    0 < C ∧ ∃ K : Finset (ℤ × ℤ),
      (∀ k : ℤ × ℤ, k ∈ K ↔ (cell k).Nonempty) ∧
      (K.card : ℝ) ≤ C * (n : ℝ) ^ 2 ∧
      P.real (M ⁻¹' V) = ∑ k ∈ K, P.real (M ⁻¹' cell k) ∧
      ∀ theta : (ℤ × ℤ) → (ℝ × ℝ),
        (∀ k ∈ K, theta k ∈
          Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))) →
      ∀ (y : (ℤ × ℤ) → (ℝ × ℝ))
        (E : (ℤ × ℤ) → ((ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))),
      let logZ : (ℤ × ℤ) → ℝ := fun k => Real.log
        (∫ x : ℝ, Real.exp ((theta k).1 * x + (theta k).2 * x ^ 2) ∂mu)
      let Q : (ℤ × ℤ) → Measure (Shao.Path n) := fun k =>
        Measure.pi (fun _ : Fin n =>
          mu.tilted (fun x => (theta k).1 * x + (theta k).2 * x ^ 2))
      let F : (ℤ × ℤ) → (ℝ × ℝ) → (ℝ × ℝ) := fun k w =>
        Real.sqrt (n : ℝ) • E k (w - y k)
      let T : (ℤ × ℤ) → Shao.Path n → (ℝ × ℝ) := fun k z => F k (M z)
      let laws : (ℤ × ℤ) → Measure (ℝ × ℝ) := fun k => (Q k).map (T k)
      let B : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k => F k '' cell k
      let g : (ℤ × ℤ) → (ℝ × ℝ) → ℝ := fun k v =>
        Real.exp (-Real.sqrt (n : ℝ) *
          ((theta k).1 * ((E k).symm v).1 + (theta k).2 * ((E k).symm v).2))
      (∀ k ∈ K, MeasurableSet (B k) ∧ Integrable (g k) (laws k)) ∧
      P.real (M ⁻¹' V) =
        ∑ k ∈ K, Real.exp (-(n : ℝ) *
          ((theta k).1 * (y k).1 + (theta k).2 * (y k).2 - logZ k)) *
          ∫ v : ℝ × ℝ in B k, g k v ∂laws k := by
  classical
  dsimp only
  let V : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
    0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
  let cell : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k =>
    (Set.Ioc ((k.1 : ℝ) / (n : ℝ)) (((k.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
     Set.Ioc ((k.2 : ℝ) / (n : ℝ)) (((k.2 : ℝ) + 1) / (n : ℝ))) ∩ V
  let C : ℝ := (2 * rho + 2) * ((|a0| + rho) ^ 2 / level ^ 2 + rho + 2)
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
  let M : Shao.Path n → (ℝ × ℝ) := fun z =>
    ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
  have hc := actual_parabola_active_grid_cardinality_bound n hn level a0 rho hrho
  dsimp only at hc
  rcases hc with ⟨hC, hfinite, hcount⟩
  let K : Finset (ℤ × ℤ) := hfinite.toFinset
  have hK (k : ℤ × ℤ) : k ∈ K ↔ (cell k).Nonempty := by
    simp only [K, Set.Finite.mem_toFinset]
    rfl
  rw [Set.ncard_eq_toFinset_card _ hfinite] at hcount
  have hb := actual_parabola_finite_half_open_grid_cover n hn level a0 rho hrho
  dsimp only at hb
  rcases hb with ⟨_, _, hunion, hdisjoint⟩
  have hcover : (⋃ k ∈ K, cell k) = V := by
    apply Set.Subset.antisymm
    · intro w hw
      rcases Set.mem_iUnion.mp hw with ⟨k, hk⟩
      rcases Set.mem_iUnion.mp hk with ⟨_, hcell⟩
      exact hcell.2
    · intro w hw
      have hw' := (Set.ext_iff.mp hunion w).mpr hw
      rcases Set.mem_iUnion.mp hw' with ⟨k, hk⟩
      rcases Set.mem_iUnion.mp hk with ⟨_, hcell⟩
      exact Set.mem_iUnion.mpr ⟨k,
        Set.mem_iUnion.mpr ⟨(hK k).2 ⟨w, hcell⟩, hcell⟩⟩
  have hV : MeasurableSet V :=
    (actual_parabola_window_isCompact level a0 rho hrho).measurableSet
  have hcell (k : ℤ × ℤ) : MeasurableSet (cell k) :=
    (measurableSet_Ioc.prod measurableSet_Ioc).inter hV
  have hM : Measurable M := by dsimp [M, Shao.energy]; fun_prop
  have hpre : (⋃ k ∈ K, M ⁻¹' cell k) = M ⁻¹' V := by
    ext z
    simpa only [Set.mem_iUnion, Set.mem_preimage] using Set.ext_iff.mp hcover (M z)
  have hd : Set.Pairwise (K : Set (ℤ × ℤ))
      (fun i j => Disjoint (M ⁻¹' cell i) (M ⁻¹' cell j)) := by
    intro i _ j _ hij
    exact (hdisjoint hij).preimage M
  have hsum : P.real (M ⁻¹' V) = ∑ k ∈ K, P.real (M ⁻¹' cell k) := by
    rw [← hpre]
    exact measureReal_biUnion_finset (μ := P) hd (fun k _ => (hcell k).preimage hM)
  refine ⟨hC, K, hK, hcount, hsum, ?_⟩
  intro theta htheta y E
  let logZ : (ℤ × ℤ) → ℝ := fun k => Real.log
    (∫ x : ℝ, Real.exp ((theta k).1 * x + (theta k).2 * x ^ 2) ∂mu)
  let Q : (ℤ × ℤ) → Measure (Shao.Path n) := fun k =>
    Measure.pi (fun _ : Fin n =>
      mu.tilted (fun x => (theta k).1 * x + (theta k).2 * x ^ 2))
  let F : (ℤ × ℤ) → (ℝ × ℝ) → (ℝ × ℝ) := fun k w =>
    Real.sqrt (n : ℝ) • E k (w - y k)
  let T : (ℤ × ℤ) → Shao.Path n → (ℝ × ℝ) := fun k z => F k (M z)
  let laws : (ℤ × ℤ) → Measure (ℝ × ℝ) := fun k => (Q k).map (T k)
  let B : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k => F k '' cell k
  let g : (ℤ × ℤ) → (ℝ × ℝ) → ℝ := fun k v =>
    Real.exp (-Real.sqrt (n : ℝ) *
      ((theta k).1 * ((E k).symm v).1 + (theta k).2 * ((E k).symm v).2))
  have hchange (k : ℤ × ℤ) (hk : k ∈ K) :
      MeasurableSet (B k) ∧ Integrable (g k) (laws k) ∧
      P.real (M ⁻¹' cell k) = Real.exp (-(n : ℝ) *
        ((theta k).1 * (y k).1 + (theta k).2 * (y k).2 - logZ k)) *
        ∫ v : ℝ × ℝ in B k, g k v ∂laws k := by
    have h := iid_quadratic_standardized_cell_change_of_measure
      mu (theta k) (htheta k hk) n hn (y k) (E k) (cell k) (hcell k)
    dsimp only at h
    rcases h with ⟨hB, hBeq, hg, hid⟩
    have hBeq' : {v : ℝ × ℝ |
        y k + (Real.sqrt (n : ℝ))⁻¹ • (E k).symm v ∈ cell k} = B k := hBeq
    have hB' : MeasurableSet (B k) := hBeq' ▸ hB
    rw [hBeq] at hid
    exact ⟨hB', hg, hid⟩
  refine ⟨fun k hk => ⟨(hchange k hk).1, (hchange k hk).2.1⟩, hsum.trans ?_⟩
  exact Finset.sum_congr rfl (fun k hk => (hchange k hk).2.2)

end
end Shao.OQ3
