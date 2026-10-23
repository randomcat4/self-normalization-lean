import Shao.OQ5.P53.SparseBalancedEvent
import Shao.OQ5.P53.SparseRealSample

/-!
# Mass of the actual sparse balanced event

This is the exact fixed-population event in p53 section 4, equation (8).
Both label coordinates and both prescribed signs are measured in their
actual nested product law. Noise is unrestricted. The infinite-sample
statement uses the whole population prefix law.
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

namespace Shao.OQ5.P53

local notation "SparseObs" => ((ℝ × (ℕ × Bool)) × (ℕ × Bool))

private theorem balanced_mass_prior_nonneg
    (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) :
    0 ≤ sparsePriorMass α x N j := by
  unfold sparsePriorMass
  exact Finset.sum_nonneg (fun k _ => sparseLabelMass_nonneg α x N k)

private theorem balanced_mass_label_pos
    (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) (hj : 1 ≤ j) :
    0 < sparseLabelMass α x N j := by
  rw [sparseLabelMass_eq_positiveMass α x N j hj]
  exact sparsePositiveMass_pos α x N j hj

theorem sparsePopulationMeasure_lowObservation :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  sparsePopulationMeasure α x N (sparseLowObservation j) =
    ENNReal.ofReal (sparsePriorMass α x N j ^ 2) := by
  intro α x N j
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  have hlow : sparseSignedLabelMeasure α x N
      ((Prod.fst : ℕ × Bool → ℕ) ⁻¹' Set.Iio j) =
      ENNReal.ofReal (sparsePriorMass α x N j) := by
    rw [← Measure.map_apply measurable_fst measurableSet_Iio,
      sparseSignedLabelMeasure_first, sparseLabelMeasure_Iio]
  have hset : sparseLowObservation j =
      ((Set.univ : Set ℝ) ×ˢ ((Prod.fst : ℕ × Bool → ℕ) ⁻¹' Set.Iio j)) ×ˢ
        ((Prod.fst : ℕ × Bool → ℕ) ⁻¹' Set.Iio j) := by
    ext z
    simp [sparseLowObservation]
  rw [hset, sparsePopulationMeasure, sparseGBaseMeasure,
    Measure.prod_prod, Measure.prod_prod, measure_univ, one_mul]
  simp only [hlow]
  rw [← ENNReal.ofReal_mul (balanced_mass_prior_nonneg α x N j)]
  congr 1
  ring

theorem sparsePopulationMeasure_real_lowObservation :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  (sparsePopulationMeasure α x N).real (sparseLowObservation j) =
    sparsePriorMass α x N j ^ 2 := by
  intro α x N j
  rw [measureReal_def, sparsePopulationMeasure_lowObservation,
    ENNReal.toReal_ofReal (sq_nonneg _)]

theorem sparsePopulationMeasure_targetObservation :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) (b : Bool),
  sparsePopulationMeasure α x N (sparseTargetObservation j b) =
    ENNReal.ofReal (sparseLabelMass α x N j ^ 2 / 4) := by
  intro α x N j b
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  have hset : sparseTargetObservation j b =
      ((Set.univ : Set ℝ) ×ˢ ({(j, true)} : Set (ℕ × Bool))) ×ˢ
        ({(j, b)} : Set (ℕ × Bool)) := by
    ext z
    simp [sparseTargetObservation]
  rw [hset, sparsePopulationMeasure, sparseGBaseMeasure,
    Measure.prod_prod, Measure.prod_prod, measure_univ, one_mul]
  simp only [sparseSignedLabelMeasure_singleton]
  rw [← ENNReal.ofReal_mul
    (div_nonneg (sparseLabelMass_nonneg α x N j) (by norm_num))]
  congr 1
  ring

theorem sparsePopulationMeasure_real_targetObservation :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) (b : Bool),
  (sparsePopulationMeasure α x N).real (sparseTargetObservation j b) =
    sparseLabelMass α x N j ^ 2 / 4 := by
  intro α x N j b
  rw [measureReal_def, sparsePopulationMeasure_targetObservation,
    ENNReal.toReal_ofReal (div_nonneg (sq_nonneg _) (by norm_num))]

theorem sparseBalancedPairPattern_real_mass :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool), i < k →
  (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N)).real
    (sparseBalancedPairPattern j i k b) =
      sparseLabelMass α x N j ^ 4 * sparsePriorMass α x N j ^ (2 * (n - 2)) / 16 := by
  intro α x N n j i k b hik
  classical
  let : IsProbabilityMeasure (sparsePopulationMeasure α x N) :=
    sparsePopulationMeasure_probability α x N
  have hikne : i ≠ k := ne_of_lt hik
  let J : Finset (Fin n) := {i, k}
  have hJcard : J.card = 2 := by simp [J, hikne]
  have hfilter : (Finset.univ : Finset (Fin n)).filter (fun l => l ∈ J) = J := by
    ext l
    simp
  have hnot : (Finset.univ : Finset (Fin n)).filter (fun l => l ∉ J) =
      Finset.univ \ J := by
    ext l
    simp
  calc
    (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N)).real
        (sparseBalancedPairPattern j i k b) =
        ∏ l : Fin n, (sparsePopulationMeasure α x N).real
          (if l = i then sparseTargetObservation j b
           else if l = k then sparseTargetObservation j (!b)
           else sparseLowObservation j) := by
      rw [measureReal_def, sparseBalancedPairPattern_eq_pi n j i k b hik,
        Measure.pi_pi, ENNReal.toReal_prod]
      rfl
    _ = ∏ l : Fin n, if l ∈ J then sparseLabelMass α x N j ^ 2 / 4
        else sparsePriorMass α x N j ^ 2 := by
      apply Finset.prod_congr rfl
      intro l _
      by_cases hli : l = i
      · subst l
        simp [J, sparsePopulationMeasure_real_targetObservation]
      · by_cases hlk : l = k
        · subst l
          simp [J, hli, sparsePopulationMeasure_real_targetObservation]
        · simp [J, hli, hlk, sparsePopulationMeasure_real_lowObservation]
    _ = (sparseLabelMass α x N j ^ 2 / 4) ^ 2 *
        (sparsePriorMass α x N j ^ 2) ^ (n - 2) := by
      rw [Finset.prod_ite, hfilter, hnot, Finset.prod_const, Finset.prod_const,
        Finset.card_sdiff]
      simp [hJcard]
    _ = sparseLabelMass α x N j ^ 4 *
        sparsePriorMass α x N j ^ (2 * (n - 2)) / 16 := by
      rw [← pow_mul]
      ring

theorem sparseBalancedPairEvent_real_mass :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n), i < k →
  (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N)).real
    (sparseBalancedPairEvent j i k) =
      sparseLabelMass α x N j ^ 4 * sparsePriorMass α x N j ^ (2 * (n - 2)) / 8 := by
  intro α x N n j i k hik
  let : IsProbabilityMeasure (sparsePopulationMeasure α x N) :=
    sparsePopulationMeasure_probability α x N
  change ((Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N))
    (sparseBalancedPairPattern j i k false ∪ sparseBalancedPairPattern j i k true)).toReal = _
  rw [measure_union (sparseBalancedPairPattern_disjoint n j i k)
    (measurableSet_sparseBalancedPairPattern n j i k true),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  change (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N)).real
      (sparseBalancedPairPattern j i k false) +
    (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N)).real
      (sparseBalancedPairPattern j i k true) = _
  rw [sparseBalancedPairPattern_real_mass α x N n j i k false hik,
    sparseBalancedPairPattern_real_mass α x N n j i k true hik]
  ring

private theorem balanced_sorted_pair_count (n : ℕ) :
    (∑ i : Fin n, ∑ k : Fin n, if i < k then (1 : ℝ) else 0) =
      (n.choose 2 : ℝ) := by
  classical
  have hdouble := Shao.OQ5.P35.offDiagonalSum_eq_two_unordered
    (n := n) (fun _ _ => (1 : ℝ)) (by intro i k; rfl)
  have hleft : (∑ i : Fin n, ∑ k ∈ Finset.univ.erase i, (1 : ℝ)) =
      (n : ℝ) * ((n : ℝ) - 1) := by
    calc
      (∑ i : Fin n, ∑ k ∈ Finset.univ.erase i, (1 : ℝ)) =
          ∑ _i : Fin n, ((n : ℝ) - 1) := by
        apply Finset.sum_congr rfl
        intro i _
        have hn : 1 ≤ n := by
          have hi := i.isLt
          omega
        simp [Finset.card_erase_of_mem, Nat.cast_sub hn]
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hleft] at hdouble
  change (n : ℝ) * ((n : ℝ) - 1) =
    2 * (∑ i : Fin n, ∑ k : Fin n, if i < k then (1 : ℝ) else 0) at hdouble
  have hc := Shao.OQ5.P35.pairCount_eq_choose n
  unfold Shao.OQ5.P35.pairCount at hc
  linarith

theorem sparseBalancedEvent_real_mass :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ),
  (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N)).real
    (sparseBalancedEvent n j) =
      (n.choose 2 : ℝ) * sparseLabelMass α x N j ^ 4 *
        sparsePriorMass α x N j ^ (2 * (n - 2)) / 8 := by
  intro α x N n j
  classical
  let : IsProbabilityMeasure (sparsePopulationMeasure α x N) :=
    sparsePopulationMeasure_probability α x N
  let S : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 < p.2)
  have hset : sparseBalancedEvent n j =
      ⋃ p ∈ S, sparseBalancedPairEvent j p.1 p.2 := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨i, hω⟩
      rcases Set.mem_iUnion.mp hω with ⟨k, hω⟩
      have hik : i < k := by
        rcases hω with hω | hω <;> exact hω.1
      exact Set.mem_iUnion.mpr ⟨(i, k), Set.mem_iUnion.mpr ⟨by simp [S, hik], hω⟩⟩
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨p, hω⟩
      rcases Set.mem_iUnion.mp hω with ⟨_hp, hω⟩
      exact Set.mem_iUnion.mpr ⟨p.1, Set.mem_iUnion.mpr ⟨p.2, hω⟩⟩
  have hcard : (S.card : ℝ) = (n.choose 2 : ℝ) := by
    calc
      (S.card : ℝ) = ∑ _p ∈ S, (1 : ℝ) := by simp
      _ = ∑ p : Fin n × Fin n, if p.1 < p.2 then (1 : ℝ) else 0 := by
        simp only [S, Finset.sum_filter]
      _ = ∑ i : Fin n, ∑ k : Fin n, if i < k then (1 : ℝ) else 0 := by
        rw [Fintype.sum_prod_type]
      _ = (n.choose 2 : ℝ) := balanced_sorted_pair_count n
  rw [hset, measureReal_biUnion_finset
    (fun p hp q hq hpq => sparseBalancedPairEvent_disjoint n j p.1 p.2 q.1 q.2
      (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2 hpq)
    (fun p _ => measurableSet_sparseBalancedPairEvent n j p.1 p.2)]
  calc
    (∑ p ∈ S, (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N)).real
        (sparseBalancedPairEvent j p.1 p.2)) =
        ∑ _p ∈ S, sparseLabelMass α x N j ^ 4 *
          sparsePriorMass α x N j ^ (2 * (n - 2)) / 8 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact sparseBalancedPairEvent_real_mass α x N n j p.1 p.2
        (Finset.mem_filter.mp hp).2
    _ = (n.choose 2 : ℝ) * sparseLabelMass α x N j ^ 4 *
        sparsePriorMass α x N j ^ (2 * (n - 2)) / 8 := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
      ring

theorem sparseBalancedPrefixEvent_real_mass :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ),
  (sparsePopulationSampleMeasure α x N).real (sparseBalancedPrefixEvent n j) =
    (n.choose 2 : ℝ) * sparseLabelMass α x N j ^ 4 *
      sparsePriorMass α x N j ^ (2 * (n - 2)) / 8 := by
  intro α x N n j
  have hm : Measurable (fun ω : ℕ → SparseObs => fun i : Fin n => ω i.val) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_pi_apply i.val
  change ((sparsePopulationSampleMeasure α x N)
    ((fun ω : ℕ → SparseObs => fun i : Fin n => ω i.val) ⁻¹'
      sparseBalancedEvent n j)).toReal = _
  rw [← Measure.map_apply hm (measurableSet_sparseBalancedEvent n j),
    sparsePopulationSample_prefix_law]
  exact sparseBalancedEvent_real_mass α x N n j

theorem sparseBalancedPrefixEvent_positive_level_mass :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ), 1 ≤ j →
  (sparsePopulationSampleMeasure α x N).real (sparseBalancedPrefixEvent n j) =
    (n.choose 2 : ℝ) * sparsePositiveMass α x N j ^ 4 *
      sparsePriorMass α x N j ^ (2 * (n - 2)) / 8 := by
  intro α x N n j hj
  rw [sparseBalancedPrefixEvent_real_mass,
    sparseLabelMass_eq_positiveMass α x N j hj]

theorem sparseBalancedPairPattern_real_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  1 ≤ j → i < k →
  0 < (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N)).real
    (sparseBalancedPairPattern j i k b) := by
  intro α x N n j i k b hj hik
  rw [sparseBalancedPairPattern_real_mass α x N n j i k b hik]
  have hq : 0 < sparsePriorMass α x N j := by
    linarith [(sparsePriorMass_bounds α x N j hj).1]
  exact div_pos (mul_pos (pow_pos (balanced_mass_label_pos α x N j hj) _)
    (pow_pos hq _)) (by norm_num)

theorem sparseBalancedPrefixEvent_real_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ), 2 ≤ n → 1 ≤ j →
  0 < (sparsePopulationSampleMeasure α x N).real (sparseBalancedPrefixEvent n j) := by
  intro α x N n j hn hj
  rw [sparseBalancedPrefixEvent_real_mass]
  have hc : 0 < (n.choose 2 : ℝ) := by exact_mod_cast Nat.choose_pos hn
  have hq : 0 < sparsePriorMass α x N j := by
    linarith [(sparsePriorMass_bounds α x N j hj).1]
  exact div_pos (mul_pos (mul_pos hc (pow_pos (balanced_mass_label_pos α x N j hj) _))
    (pow_pos hq _)) (by norm_num)

theorem sparseBalancedPairPattern_cond_probability :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  1 ≤ j → i < k →
  IsProbabilityMeasure (ProbabilityTheory.cond
    (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N))
      (sparseBalancedPairPattern j i k b)) := by
  intro α x N n j i k b hj hik
  let : IsProbabilityMeasure (sparsePopulationMeasure α x N) :=
    sparsePopulationMeasure_probability α x N
  apply ProbabilityTheory.cond_isProbabilityMeasure
  intro hz
  have hpos := sparseBalancedPairPattern_real_pos α x N n j i k b hj hik
  simp only [measureReal_def, hz, ENNReal.toReal_zero, lt_self_iff_false] at hpos

theorem sparseBalancedPrefixEvent_cond_probability :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ), 2 ≤ n → 1 ≤ j →
  IsProbabilityMeasure (ProbabilityTheory.cond (sparsePopulationSampleMeasure α x N)
    (sparseBalancedPrefixEvent n j)) := by
  intro α x N n j hn hj
  let : IsProbabilityMeasure (sparsePopulationSampleMeasure α x N) :=
    sparsePopulationSampleMeasure_probability α x N
  apply ProbabilityTheory.cond_isProbabilityMeasure
  intro hz
  have hpos := sparseBalancedPrefixEvent_real_pos α x N n j hn hj
  simp only [measureReal_def, hz, ENNReal.toReal_zero, lt_self_iff_false] at hpos

end Shao.OQ5.P53
