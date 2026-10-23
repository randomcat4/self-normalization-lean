import Shao.OQ5.P53.SparseSampleStatistics
import Shao.OQ5.P45.BalancedBlock

/-!
# The actual p53 two-target balanced event

The event restricts both labels of every background observation, leaves all
noise coordinates free, and separates the two target sign orientations. Only
set structure and pointwise original-statistic algebra are proved here.
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace Shao.OQ5.P53

local notation "SparseObs" => ((ℝ × (ℕ × Bool)) × (ℕ × Bool))

def sparseLowObservation (j : ℕ) : Set SparseObs :=
  {z | z.1.2.1 < j ∧ z.2.1 < j}

def sparseTargetObservation (j : ℕ) (b : Bool) : Set SparseObs :=
  {z | z.1.2 = (j, true) ∧ z.2 = (j, b)}

def sparseBalancedPairPattern {n : ℕ} (j : ℕ) (i k : Fin n) (b : Bool) : Set (Fin n → SparseObs) :=
  {ω | i < k ∧ ω i ∈ sparseTargetObservation j b ∧
    ω k ∈ sparseTargetObservation j (!b) ∧
    ∀ l : Fin n, l ≠ i → l ≠ k → ω l ∈ sparseLowObservation j}

def sparseBalancedPairEvent {n : ℕ} (j : ℕ) (i k : Fin n) : Set (Fin n → SparseObs) :=
  sparseBalancedPairPattern j i k false ∪ sparseBalancedPairPattern j i k true

def sparseBalancedEvent (n j : ℕ) : Set (Fin n → SparseObs) :=
  ⋃ i : Fin n, ⋃ k : Fin n, sparseBalancedPairEvent j i k

def sparseBalancedPrefixEvent (n j : ℕ) : Set (ℕ → SparseObs) :=
  {ω | (fun i : Fin n => ω i.val) ∈ sparseBalancedEvent n j}

theorem measurableSet_sparseLowObservation :
  ∀ j : ℕ, MeasurableSet (sparseLowObservation j) := by
  intro j
  exact (measurableSet_lt measurable_fst.snd.fst measurable_const).inter
    (measurableSet_lt measurable_snd.fst measurable_const)

theorem measurableSet_sparseTargetObservation :
  ∀ (j : ℕ) (b : Bool), MeasurableSet (sparseTargetObservation j b) := by
  intro j b
  exact ((measurableSet_singleton (j, true)).preimage measurable_fst.snd).inter
    ((measurableSet_singleton (j, b)).preimage measurable_snd)

theorem measurableSet_sparseBalancedPairPattern :
  ∀ (n j : ℕ) (i k : Fin n) (b : Bool),
  MeasurableSet (sparseBalancedPairPattern j i k b) := by
  intro n j i k b
  have hlow : MeasurableSet
      {ω : Fin n → SparseObs | ∀ l : Fin n, l ≠ i → l ≠ k →
        ω l ∈ sparseLowObservation j} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ =>
        (measurableSet_sparseLowObservation j).preimage (measurable_pi_apply l)
  by_cases hik : i < k
  · have heq : sparseBalancedPairPattern j i k b =
        ((fun ω : Fin n → SparseObs => ω i) ⁻¹' sparseTargetObservation j b) ∩
          (((fun ω : Fin n → SparseObs => ω k) ⁻¹' sparseTargetObservation j (!b)) ∩
            {ω : Fin n → SparseObs | ∀ l : Fin n, l ≠ i → l ≠ k →
              ω l ∈ sparseLowObservation j}) := by
      ext ω
      simp only [sparseBalancedPairPattern, Set.mem_ofPred_eq, Set.mem_inter_iff,
        Set.mem_preimage, hik, true_and]
    rw [heq]
    exact ((measurableSet_sparseTargetObservation j b).preimage
      (measurable_pi_apply i)).inter
      (((measurableSet_sparseTargetObservation j (!b)).preimage
        (measurable_pi_apply k)).inter hlow)
  · have heq : sparseBalancedPairPattern j i k b = ∅ := by
      ext ω
      simp only [sparseBalancedPairPattern, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        hik, false_and]
    rw [heq]
    exact MeasurableSet.empty

theorem measurableSet_sparseBalancedPairEvent :
  ∀ (n j : ℕ) (i k : Fin n), MeasurableSet (sparseBalancedPairEvent j i k) := by
  intro n j i k
  exact (measurableSet_sparseBalancedPairPattern n j i k false).union
    (measurableSet_sparseBalancedPairPattern n j i k true)

theorem measurableSet_sparseBalancedEvent :
  ∀ n j : ℕ, MeasurableSet (sparseBalancedEvent n j) := by
  intro n j
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun k =>
    measurableSet_sparseBalancedPairEvent n j i k

theorem measurableSet_sparseBalancedPrefixEvent :
  ∀ n j : ℕ, MeasurableSet (sparseBalancedPrefixEvent n j) := by
  intro n j
  exact (measurableSet_sparseBalancedEvent n j).preimage
    (measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val))

theorem sparseBalancedPairPattern_eq_pi :
  ∀ (n j : ℕ) (i k : Fin n) (b : Bool), i < k →
  sparseBalancedPairPattern j i k b =
    Set.pi Set.univ (fun l : Fin n =>
      if l = i then sparseTargetObservation j b
      else if l = k then sparseTargetObservation j (!b)
      else sparseLowObservation j) := by
  intro n j i k b hik
  ext ω
  constructor
  · intro hω
    change ∀ l ∈ Set.univ, ω l ∈ _
    intro l _
    by_cases hli : l = i
    · subst l
      simpa only [ite_true] using hω.2.1
    · by_cases hlk : l = k
      · subst l
        simpa only [ite_eq_right (ne_of_gt hik), ite_true] using hω.2.2.1
      · simpa only [ite_eq_right hli, ite_eq_right hlk] using hω.2.2.2 l hli hlk
  · intro hω
    change ∀ l ∈ Set.univ, ω l ∈ _ at hω
    refine ⟨hik, ?_, ?_, ?_⟩
    · simpa only [ite_true] using hω i (Set.mem_univ i)
    · simpa only [ite_eq_right (ne_of_gt hik), ite_true] using hω k (Set.mem_univ k)
    · intro l hli hlk
      simpa only [ite_eq_right hli, ite_eq_right hlk] using hω l (Set.mem_univ l)

theorem sparseBalancedPairPattern_disjoint :
  ∀ (n j : ℕ) (i k : Fin n),
  Disjoint (sparseBalancedPairPattern j i k false)
    (sparseBalancedPairPattern j i k true) := by
  intro n j i k
  apply Set.disjoint_left.mpr
  intro ω hfalse htrue
  have heq : (false : Bool) = true :=
    congrArg Prod.snd (hfalse.2.1.2.symm.trans htrue.2.1.2)
  exact Bool.false_ne_true heq

private theorem target_not_low {j : ℕ} {b : Bool} {z : SparseObs}
    (ht : z ∈ sparseTargetObservation j b) : z ∉ sparseLowObservation j := by
  intro hl
  have hlabel : z.1.2.1 = j := congrArg Prod.fst ht.1
  have hlt := hl.1
  rw [hlabel] at hlt
  exact (lt_irrefl j) hlt

private theorem target_index_of_pattern {n j : ℕ} {a c l : Fin n} {b d : Bool}
    {ω : Fin n → SparseObs} (hp : ω ∈ sparseBalancedPairPattern j a c b)
    (ht : ω l ∈ sparseTargetObservation j d) : l = a ∨ l = c := by
  by_cases hla : l = a
  · exact Or.inl hla
  · by_cases hlc : l = c
    · exact Or.inr hlc
    · exact False.elim (target_not_low ht (hp.2.2.2 l hla hlc))

theorem sparseBalancedPairEvent_disjoint :
  ∀ (n j : ℕ) (i k a c : Fin n), i < k → a < c → (i, k) ≠ (a, c) →
  Disjoint (sparseBalancedPairEvent j i k) (sparseBalancedPairEvent j a c) := by
  intro n j i k a c hik hac hne
  apply Set.disjoint_left.mpr
  intro ω hfirst hsecond
  have hconflict : ∀ b d : Bool,
      ω ∈ sparseBalancedPairPattern j i k b →
      ω ∈ sparseBalancedPairPattern j a c d → False := by
    intro b d hleft hright
    have hi := target_index_of_pattern hright hleft.2.1
    have hk := target_index_of_pattern hright hleft.2.2.1
    rcases hi with hia | hic
    · rcases hk with hka | hkc
      · exact (ne_of_lt hik) (hia.trans hka.symm)
      · exact hne (Prod.ext hia hkc)
    · rcases hk with hka | hkc
      · have hca : c < a := by simpa only [hic, hka] using hik
        exact (not_lt_of_ge hac.le) hca
      · exact (ne_of_lt hik) (hic.trans hkc.symm)
  rcases hfirst with hfirst | hfirst <;> rcases hsecond with hsecond | hsecond
  · exact hconflict false false hfirst hsecond
  · exact hconflict false true hfirst hsecond
  · exact hconflict true false hfirst hsecond
  · exact hconflict true true hfirst hsecond

private theorem target_projection (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    {j : ℕ} {b : Bool} {z : SparseObs} (ht : z ∈ sparseTargetObservation j b) :
    sparsePopulationG α x N z = z.1.1 + sparseLevelShift α x N j := by
  change z.1.1 + sparseSignedShift α x N z.1.2 = _
  rw [ht.1]
  simp only [sparseSignedShift, ite_true]

private theorem target_feature_sq (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    {j : ℕ} {b : Bool} {z : SparseObs} (ht : z ∈ sparseTargetObservation j b) :
    sparsePopulationZ α x N z ^ 2 = sparseLevelAmplitude α x N j ^ 2 := by
  change sparseSignedAmplitude α x N z.2 ^ 2 = _
  rw [ht.2]
  cases b <;> simp [sparseSignedAmplitude]

private theorem level_shift_eq_amplitude_sq (α : ℝ) (x : ℕ → ℝ)
    (N : ℕ → ℕ) (j : ℕ) :
    sparseLevelShift α x N j = sparseLevelAmplitude α x N j ^ 2 / ((N j : ℝ) - 2) := by
  by_cases hj : j = 0 <;>
    simp [sparseLevelShift, sparseLevelAmplitude, sparseShift, hj]

theorem sparseBalancedPairPattern_balancedTarget :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ)
    (i k : Fin (N j)) (b : Bool) (ω : Fin (N j) → SparseObs),
  ω ∈ sparseBalancedPairPattern j i k b →
  Shao.OQ5.P45.BalancedTarget (fun l => (ω l).1.1)
    (fun l => sparsePopulationG α x N (ω l))
    (fun l => sparsePopulationZ α x N (ω l))
    ({i, k} : Finset (Fin (N j)))
    (sparseLevelAmplitude α x N j) (sparseLevelShift α x N j) := by
  intro α x N j i k b ω hω
  classical
  have hik : i ≠ k := ne_of_lt hω.1
  refine ⟨?_, ?_, ?_, level_shift_eq_amplitude_sq α x N j⟩
  · intro l hl
    rcases Finset.mem_insert.mp hl with rfl | hl
    · exact target_projection α x N hω.2.1
    · have hlk := Finset.mem_singleton.mp hl
      subst l
      exact target_projection α x N hω.2.2.1
  · intro l hl
    rcases Finset.mem_insert.mp hl with rfl | hl
    · exact target_feature_sq α x N hω.2.1
    · have hlk := Finset.mem_singleton.mp hl
      subst l
      exact target_feature_sq α x N hω.2.2.1
  · rw [Finset.sum_pair hik]
    change sparseSignedAmplitude α x N (ω i).2 +
      sparseSignedAmplitude α x N (ω k).2 = 0
    rw [hω.2.1.2, hω.2.2.1.2]
    cases b <;> simp [sparseSignedAmplitude]

theorem sparseSampleAdjustedRow_balancedPair_target :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ), 3 ≤ N j →
  ∀ (i k : Fin (N j)) (b : Bool) (ω : Fin (N j) → SparseObs),
  ω ∈ sparseBalancedPairPattern j i k b →
  ∀ l : Fin (N j), l ∈ ({i, k} : Finset (Fin (N j))) →
  sparseSampleAdjustedRow α x N ω l = (ω l).1.1 +
    sparsePopulationZ α x N (ω l) *
      Shao.OQ5.P35.backgroundSum ({i, k} : Finset (Fin (N j)))
        (fun a => sparsePopulationZ α x N (ω a)) / ((N j : ℝ) - 2) := by
  intro α x N j hn i k b ω hω l hl
  have hblock := sparseBalancedPairPattern_balancedTarget α x N j i k b ω hω
  rw [sparseSampleAdjustedRow, sparseSampleResidualRow_eq_factor]
  exact Shao.OQ5.P45.adjustedRow_eq_target (fun a => (ω a).1.1)
    (fun a => sparsePopulationG α x N (ω a))
    (fun a => sparsePopulationZ α x N (ω a)) hn
    ({i, k} : Finset (Fin (N j)))
    (sparseLevelAmplitude α x N j) (sparseLevelShift α x N j) hblock l hl

theorem sparseSampleAdjustedRow_balancedPair_background :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ), 3 ≤ N j →
  ∀ (i k : Fin (N j)) (b : Bool) (ω : Fin (N j) → SparseObs),
  ω ∈ sparseBalancedPairPattern j i k b →
  ∀ l : Fin (N j), l ∉ ({i, k} : Finset (Fin (N j))) →
  sparseSampleAdjustedRow α x N ω l = sparsePopulationG α x N (ω l) +
    sparsePopulationZ α x N (ω l) *
      (Shao.OQ5.P35.backgroundSum ({i, k} : Finset (Fin (N j)))
        (fun a => sparsePopulationZ α x N (ω a)) - sparsePopulationZ α x N (ω l)) /
          ((N j : ℝ) - 2) := by
  intro α x N j hn i k b ω hω l hl
  have hblock := sparseBalancedPairPattern_balancedTarget α x N j i k b ω hω
  rw [sparseSampleAdjustedRow, sparseSampleResidualRow_eq_factor]
  exact Shao.OQ5.P45.adjustedRow_eq_background
    (fun a => sparsePopulationG α x N (ω a))
    (fun a => sparsePopulationZ α x N (ω a)) hn
    ({i, k} : Finset (Fin (N j))) hblock.2.2.1 l hl

theorem sparseSampleU_balancedPair_formula :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ), 3 ≤ N j →
  ∀ (i k : Fin (N j)) (b : Bool) (ω : Fin (N j) → SparseObs),
  ω ∈ sparseBalancedPairPattern j i k b →
  sparseSampleU α x N ω =
    2 * sparseLevelShift α x N j / ((N j : ℝ) - 1) +
    (2 / (N j : ℝ)) * ((ω i).1.1 + (ω k).1.1) +
    (2 / (N j : ℝ)) *
      (∑ l : Fin (N j), if l ∈ ({i, k} : Finset (Fin (N j))) then 0
        else sparsePopulationG α x N (ω l)) +
    (Shao.OQ5.P35.backgroundSum ({i, k} : Finset (Fin (N j)))
        (fun l => sparsePopulationZ α x N (ω l)) ^ 2 -
      Shao.OQ5.P35.backgroundSqSum ({i, k} : Finset (Fin (N j)))
        (fun l => sparsePopulationZ α x N (ω l))) /
          ((N j : ℝ) * ((N j : ℝ) - 1)) := by
  intro α x N j hn i k b ω hω
  classical
  have hik : i ≠ k := ne_of_lt hω.1
  have hblock := sparseBalancedPairPattern_balancedTarget α x N j i k b ω hω
  have hbridge := Shao.OQ5.P45.uStatistic_eq_balancedBlock
    (fun a => (ω a).1.1)
    (fun a => sparsePopulationG α x N (ω a))
    (fun a => sparsePopulationZ α x N (ω a)) hn
    ({i, k} : Finset (Fin (N j)))
    (sparseLevelAmplitude α x N j) (sparseLevelShift α x N j) hblock
  change Shao.OQ6.FiniteRows.uStatistic
    (Shao.OQ5.P45.positiveKernel
      (fun a => sparsePopulationG α x N (ω a))
      (fun a => sparsePopulationZ α x N (ω a))) = _
  simpa only [Finset.card_pair hik, Nat.cast_ofNat, Finset.sum_pair hik] using hbridge

private theorem center_energy_le {n : ℕ} (v : Fin n → ℝ) (hn : 0 < n) :
    (∑ l, Shao.OQ5.P35.center v l ^ 2) ≤ ∑ l, v l ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm : (n : ℝ) * Shao.OQ5.P35.mean v = ∑ l, v l := by
    unfold Shao.OQ5.P35.mean
    field_simp
  have he : (∑ l, Shao.OQ5.P35.center v l ^ 2) =
      (∑ l, v l ^ 2) - 2 * Shao.OQ5.P35.mean v * (∑ l, v l) +
        (n : ℝ) * Shao.OQ5.P35.mean v ^ 2 := by
    simp only [Shao.OQ5.P35.center, sub_sq, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have hc : (∑ l : Fin n, 2 * v l * Shao.OQ5.P35.mean v) =
        (2 * Shao.OQ5.P35.mean v) * ∑ l : Fin n, v l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [hc]
  rw [he, ← hm]
  nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    (sq_nonneg (Shao.OQ5.P35.mean v))]

theorem sparseSampleStudentizerSq_balancedPair_le :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ), 3 ≤ N j →
  ∀ (i k : Fin (N j)) (b : Bool) (ω : Fin (N j) → SparseObs),
  ω ∈ sparseBalancedPairPattern j i k b →
  sparseSampleStudentizerSq α x N ω ≤ (4 / ((N j : ℝ) - 1)) *
    ∑ l : Fin (N j),
      (if l ∈ ({i, k} : Finset (Fin (N j))) then
        (ω l).1.1 + sparsePopulationZ α x N (ω l) *
          Shao.OQ5.P35.backgroundSum ({i, k} : Finset (Fin (N j)))
            (fun a => sparsePopulationZ α x N (ω a)) / ((N j : ℝ) - 2)
      else sparsePopulationG α x N (ω l) + sparsePopulationZ α x N (ω l) *
        (Shao.OQ5.P35.backgroundSum ({i, k} : Finset (Fin (N j)))
          (fun a => sparsePopulationZ α x N (ω a)) - sparsePopulationZ α x N (ω l)) /
            ((N j : ℝ) - 2)) ^ 2 := by
  intro α x N j hn i k b ω hω
  classical
  have hn' : (3 : ℝ) ≤ N j := by exact_mod_cast hn
  have hc : 0 ≤ 4 / ((N j : ℝ) - 1) :=
    div_nonneg (by norm_num) (by linarith)
  rw [sparseSampleStudentizerSq_eq_centered_adjusted_rows α x N (N j) hn ω]
  apply mul_le_mul_of_nonneg_left _ hc
  calc
    (∑ l : Fin (N j), Shao.OQ5.P35.center (sparseSampleAdjustedRow α x N ω) l ^ 2) ≤
        ∑ l : Fin (N j), sparseSampleAdjustedRow α x N ω l ^ 2 :=
      center_energy_le _ (lt_of_lt_of_le (by decide : 0 < 3) hn)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _
      by_cases hl : l ∈ ({i, k} : Finset (Fin (N j)))
      · rw [ite_eq_left hl, sparseSampleAdjustedRow_balancedPair_target α x N j hn i k b ω hω l hl]
      · rw [ite_eq_right hl, sparseSampleAdjustedRow_balancedPair_background α x N j hn i k b ω hω l hl]

end Shao.OQ5.P53
