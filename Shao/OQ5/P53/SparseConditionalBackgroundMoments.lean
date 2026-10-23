import Shao.OQ5.P53.SparseConditionalLaw
import Shao.OQ5.P35.FiniteIIDMoments

/-!
# Exact moments under the actual sparse balanced conditional law

Only the genuine low coordinates are reindexed. The reindexing need not
preserve order: pair sums are transported through their symmetric quadratic
identity. All stochastic products in the finite iid moment interface use
distinct coordinates and require only second moments.
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace Shao.OQ5.P53

local notation "SparseObs" => ((ℝ × (ℕ × Bool)) × (ℕ × Bool))

def sparseBalancedPatternMeasure (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n j : ℕ) (i k : Fin n) (b : Bool) : Measure (Fin n → SparseObs) :=
  ProbabilityTheory.cond (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N))
    (sparseBalancedPairPattern j i k b)

theorem sparseBalancedPatternMeasure_probability :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  1 ≤ j → i < k →
  IsProbabilityMeasure (sparseBalancedPatternMeasure α x N n j i k b) := by
  intro α x N n j i k b hj hik
  classical
  rw [sparseBalancedPatternMeasure,
    sparseBalancedPairPattern_cond_eq_pi α x N n j i k b hj hik]
  let ν : Fin n → Measure SparseObs := fun l =>
    if l = i then sparseTargetObservationMeasure α x N j b
    else if l = k then sparseTargetObservationMeasure α x N j (!b)
    else sparseLowObservationMeasure α x N j
  let : ∀ l, IsProbabilityMeasure (ν l) := by
    intro l
    dsimp [ν]
    split_ifs
    · exact sparseTargetObservationMeasure_probability α x N j b hj
    · exact sparseTargetObservationMeasure_probability α x N j (!b) hj
    · exact sparseLowObservationMeasure_probability α x N j hj
  change IsProbabilityMeasure (Measure.pi ν)
  infer_instance

private def lowIndices {n : ℕ} (i k : Fin n) : Finset (Fin n) :=
  Finset.univ \ {i, k}

private theorem lowIndices_card {n : ℕ} (i k : Fin n) (hik : i < k) :
    (lowIndices i k).card = n - 2 := by
  classical
  simp [lowIndices, Finset.card_sdiff, ne_of_lt hik]

private def lowEquiv {n : ℕ} (i k : Fin n) (hik : i < k) :
    Fin (n - 2) ≃ lowIndices i k :=
  (Finset.equivFinOfCardEq (lowIndices_card i k hik)).symm

private theorem lowEquiv_not_target {n : ℕ} (i k : Fin n) (hik : i < k)
    (r : Fin (n - 2)) : (lowEquiv i k hik r).val ∉ ({i, k} : Finset (Fin n)) := by
  classical
  exact (Finset.mem_sdiff.mp (lowEquiv i k hik r).property).2

private theorem masked_sum_reindex {n : ℕ} (i k : Fin n) (hik : i < k)
    (f : Fin n → ℝ) (F : ℝ → ℝ) (hF : F 0 = 0) :
    (∑ l : Fin n, F (Shao.OQ5.P35.backgroundFeature {i, k} f l)) =
      ∑ r : Fin (n - 2), F (f (lowEquiv i k hik r).val) := by
  classical
  have hs : (∑ l : Fin n, F (Shao.OQ5.P35.backgroundFeature {i, k} f l)) =
      ∑ l ∈ lowIndices i k, F (f l) := by
    have hset : lowIndices i k = Finset.univ.filter
        (fun l : Fin n => l ∉ ({i, k} : Finset (Fin n))) := by
      ext l
      simp [lowIndices]
    rw [hset, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : l ∈ ({i, k} : Finset (Fin n)) <;>
      simp [Shao.OQ5.P35.backgroundFeature, hl, hF]
  rw [hs]
  symm
  refine Finset.sum_bij (fun r _ => (lowEquiv i k hik r).val) ?_ ?_ ?_ ?_
  · intro r _
    exact (lowEquiv i k hik r).property
  · intro r _ s _ hrs
    exact (lowEquiv i k hik).injective (Subtype.ext hrs)
  · intro l hl
    obtain ⟨r, hr⟩ := (lowEquiv i k hik).surjective ⟨l, hl⟩
    exact ⟨r, Finset.mem_univ _, congrArg Subtype.val hr⟩
  · intro r _
    rfl

private theorem masked_featureSum_reindex {n : ℕ} (i k : Fin n) (hik : i < k)
    {Ω : Type*} (f : Fin n → Ω → ℝ) :
    Shao.OQ5.P35.finiteFeatureSum
      (fun l ω => Shao.OQ5.P35.backgroundFeature {i, k} (fun a => f a ω) l) =
    Shao.OQ5.P35.finiteFeatureSum (fun r ω => f (lowEquiv i k hik r).val ω) := by
  funext ω
  exact masked_sum_reindex i k hik (fun a => f a ω) id rfl

private theorem pair_quadratic_identity {m : ℕ} (z : Fin m → ℝ) :
    2 * Shao.OQ5.P35.unorderedPairSum (fun a c => z a * z c) =
      (∑ a, z a) ^ 2 - ∑ a, z a ^ 2 := by
  classical
  rw [← Shao.OQ5.P35.offDiagonalSum_eq_two_unordered
    (fun a c => z a * z c) (by intro a c; exact mul_comm _ _)]
  calc
    (∑ a : Fin m, ∑ c ∈ Finset.univ.erase a, z a * z c) =
        ∑ a : Fin m, (z a * (∑ c : Fin m, z c) - z a ^ 2) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_erase_eq_sub (by simp), ← Finset.mul_sum]
      ring
    _ = (∑ a : Fin m, z a) ^ 2 - ∑ a : Fin m, z a ^ 2 := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring

private theorem masked_pair_reindex {n : ℕ} (i k : Fin n) (hik : i < k)
    {Ω : Type*} (f : Fin n → Ω → ℝ) :
    Shao.OQ5.P35.finitePairProductSum
      (fun l ω => Shao.OQ5.P35.backgroundFeature {i, k} (fun a => f a ω) l) =
    Shao.OQ5.P35.finitePairProductSum (fun r ω => f (lowEquiv i k hik r).val ω) := by
  funext ω
  have h₁ := pair_quadratic_identity
    (fun l => Shao.OQ5.P35.backgroundFeature {i, k} (fun a => f a ω) l)
  have h₂ := pair_quadratic_identity (fun r => f (lowEquiv i k hik r).val ω)
  have hs := masked_sum_reindex i k hik (fun a => f a ω) id rfl
  simp only [id_eq] at hs
  rw [hs,
    masked_sum_reindex i k hik (fun a => f a ω) (fun t => t ^ 2) (by norm_num)] at h₁
  change _ = _
  dsimp only [Shao.OQ5.P35.finitePairProductSum]
  linarith

private theorem masked_leaveOwn_reindex {n : ℕ} (i k : Fin n) (hik : i < k)
    {Ω : Type*} (f : Fin n → Ω → ℝ) :
    Shao.OQ5.P35.finiteLeaveOwnSquareSum
      (fun l ω => Shao.OQ5.P35.backgroundFeature {i, k} (fun a => f a ω) l) =
    Shao.OQ5.P35.finiteLeaveOwnSquareSum (fun r ω => f (lowEquiv i k hik r).val ω) := by
  funext ω
  unfold Shao.OQ5.P35.finiteLeaveOwnSquareSum
  rw [masked_featureSum_reindex i k hik f]
  exact masked_sum_reindex i k hik (fun a => f a ω)
    (fun t => t ^ 2 *
      (Shao.OQ5.P35.finiteFeatureSum (fun r ω => f (lowEquiv i k hik r).val ω) ω - t) ^ 2)
    (by simp)

private theorem low_selected_indep (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n j : ℕ) (i k : Fin n) (b : Bool) (hj : 1 ≤ j) (hik : i < k)
    (f : SparseObs → ℝ) (hf : Measurable f) :
    ProbabilityTheory.iIndepFun
      (fun r : Fin (n - 2) => fun ω : Fin n → SparseObs =>
        f (ω (lowEquiv i k hik r).val))
      (sparseBalancedPatternMeasure α x N n j i k b) := by
  have he : Function.Injective (fun r : Fin (n - 2) => (lowEquiv i k hik r).val) := by
    intro r s hrs
    exact (lowEquiv i k hik).injective (Subtype.ext hrs)
  exact ((iIndepFun_sparseBalancedPairPattern_cond α x N n j i k b hj hik).precomp he).comp
    (fun _ => f) (fun _ => hf)

private theorem low_selected_law (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n j : ℕ) (i k : Fin n) (b : Bool) (hj : 1 ≤ j) (hik : i < k)
    (f : SparseObs → ℝ) (hf : Measurable f) (r : Fin (n - 2)) :
    ProbabilityTheory.IdentDistrib
      (fun ω : Fin n → SparseObs => f (ω (lowEquiv i k hik r).val))
      (id : ℝ → ℝ) (sparseBalancedPatternMeasure α x N n j i k b)
      ((sparseLowObservationMeasure α x N j).map f) := by
  classical
  refine ⟨(hf.comp (measurable_pi_apply _)).aemeasurable, measurable_id.aemeasurable, ?_⟩
  rw [Measure.map_id]
  have hnot := lowEquiv_not_target i k hik r
  have hi : (lowEquiv i k hik r).val ≠ i := by
    intro h
    exact hnot (by simp [h])
  have hk : (lowEquiv i k hik r).val ≠ k := by
    intro h
    exact hnot (by simp [h])
  change Measure.map (f ∘ (fun ω : Fin n → SparseObs => ω (lowEquiv i k hik r).val)) _ = _
  rw [← Measure.map_map hf (measurable_pi_apply _)]
  rw [sparseBalancedPatternMeasure,
    sparseBalancedPairPattern_cond_coordinate_law α x N n j i k b hj hik]
  simp only [hi, hk, ite_false]

private theorem mapped_memLp {μ : Measure SparseObs} (f : SparseObs → ℝ)
    (hf : Measurable f) (h₂ : MemLp f 2 μ) : MemLp (id : ℝ → ℝ) 2 (μ.map f) := by
  exact (memLp_map_measure_iff aestronglyMeasurable_id hf.aemeasurable).mpr h₂

private theorem mapped_mean {μ : Measure SparseObs} (f : SparseObs → ℝ)
    (hf : Measurable f) : (∫ z : ℝ, z ∂μ.map f) = ∫ z, f z ∂μ := by
  exact integral_map hf.aemeasurable aestronglyMeasurable_id

private theorem mapped_second {μ : Measure SparseObs} (f : SparseObs → ℝ)
    (hf : Measurable f) : (∫ z : ℝ, z ^ 2 ∂μ.map f) = ∫ z, f z ^ 2 ∂μ := by
  exact integral_map hf.aemeasurable (measurable_id.pow_const 2).aestronglyMeasurable

private theorem low_sum_memLp (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n j : ℕ) (i k : Fin n) (b : Bool) (hj : 1 ≤ j) (hik : i < k)
    (f : SparseObs → ℝ) (hf : Measurable f)
    (h₂ : MemLp f 2 (sparseLowObservationMeasure α x N j)) :
    MemLp (fun ω : Fin n → SparseObs => Shao.OQ5.P35.backgroundSum {i, k}
      (fun l => f (ω l))) 2 (sparseBalancedPatternMeasure α x N n j i k b) := by
  let : IsProbabilityMeasure (sparseLowObservationMeasure α x N j) :=
    sparseLowObservationMeasure_probability α x N j hj
  let : IsProbabilityMeasure (sparseBalancedPatternMeasure α x N n j i k b) :=
    sparseBalancedPatternMeasure_probability α x N n j i k b hj hik
  change MemLp (Shao.OQ5.P35.finiteFeatureSum
    (fun (l : Fin n) (ω : Fin n → SparseObs) =>
      Shao.OQ5.P35.backgroundFeature {i, k} (fun a => f (ω a)) l)) 2
    (sparseBalancedPatternMeasure α x N n j i k b)
  rw [masked_featureSum_reindex i k hik (fun (a : Fin n) (ω : Fin n → SparseObs) => f (ω a))]
  exact memLp_finsetSum Finset.univ (fun r _ =>
    (low_selected_law α x N n j i k b hj hik f hf r).memLp_iff.mpr
      (mapped_memLp f hf h₂))

private theorem low_sum_mean (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n j : ℕ) (i k : Fin n) (b : Bool) (hj : 1 ≤ j) (hik : i < k)
    (f : SparseObs → ℝ) (hf : Measurable f)
    (h₂ : MemLp f 2 (sparseLowObservationMeasure α x N j))
    (h₀ : (∫ z, f z ∂sparseLowObservationMeasure α x N j) = 0) :
    (∫ ω : Fin n → SparseObs, Shao.OQ5.P35.backgroundSum {i, k}
      (fun l => f (ω l)) ∂sparseBalancedPatternMeasure α x N n j i k b) = 0 := by
  let : IsProbabilityMeasure (sparseLowObservationMeasure α x N j) :=
    sparseLowObservationMeasure_probability α x N j hj
  let : IsProbabilityMeasure (sparseBalancedPatternMeasure α x N n j i k b) :=
    sparseBalancedPatternMeasure_probability α x N n j i k b hj hik
  change (∫ ω : Fin n → SparseObs, Shao.OQ5.P35.finiteFeatureSum
    (fun (l : Fin n) (η : Fin n → SparseObs) =>
      Shao.OQ5.P35.backgroundFeature {i, k} (fun a => f (η a)) l) ω
    ∂sparseBalancedPatternMeasure α x N n j i k b) = 0
  rw [masked_featureSum_reindex i k hik (fun (a : Fin n) (ω : Fin n → SparseObs) => f (ω a))]
  unfold Shao.OQ5.P35.finiteFeatureSum
  rw [integral_finsetSum _ (fun r _ =>
    ((low_selected_law α x N n j i k b hj hik f hf r).memLp_iff.mpr
      (mapped_memLp f hf h₂)).integrable (by norm_num))]
  have hterm (r : Fin (n - 2)) :
      (∫ ω : Fin n → SparseObs, f (ω (lowEquiv i k hik r).val)
        ∂sparseBalancedPatternMeasure α x N n j i k b) = 0 := by
    rw [(low_selected_law α x N n j i k b hj hik f hf r).integral_eq]
    simp only [id_eq]
    rw [mapped_mean f hf, h₀]
  simp only [hterm, Finset.sum_const_zero]

private theorem low_sum_second (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n j : ℕ) (i k : Fin n) (b : Bool) (hj : 1 ≤ j) (hik : i < k)
    (f : SparseObs → ℝ) (hf : Measurable f)
    (h₂ : MemLp f 2 (sparseLowObservationMeasure α x N j))
    (h₀ : (∫ z, f z ∂sparseLowObservationMeasure α x N j) = 0) :
    (∫ ω : Fin n → SparseObs, (Shao.OQ5.P35.backgroundSum {i, k}
      (fun l => f (ω l))) ^ 2 ∂sparseBalancedPatternMeasure α x N n j i k b) =
      ((n - 2 : ℕ) : ℝ) * (∫ z, f z ^ 2 ∂sparseLowObservationMeasure α x N j) := by
  let : IsProbabilityMeasure (sparseLowObservationMeasure α x N j) :=
    sparseLowObservationMeasure_probability α x N j hj
  let : IsProbabilityMeasure ((sparseLowObservationMeasure α x N j).map f) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).mpr inferInstance
  let : IsProbabilityMeasure (sparseBalancedPatternMeasure α x N n j i k b) :=
    sparseBalancedPatternMeasure_probability α x N n j i k b hj hik
  change (∫ ω : Fin n → SparseObs, (Shao.OQ5.P35.finiteFeatureSum
    (fun (l : Fin n) (η : Fin n → SparseObs) =>
      Shao.OQ5.P35.backgroundFeature {i, k} (fun a => f (η a)) l) ω) ^ 2
    ∂sparseBalancedPatternMeasure α x N n j i k b) = _
  rw [masked_featureSum_reindex i k hik (fun (a : Fin n) (ω : Fin n → SparseObs) => f (ω a))]
  rw [Shao.OQ5.P35.finite_iid_sumSquare_integral
    (Z := fun (r : Fin (n - 2)) (ω : Fin n → SparseObs) =>
      f (ω (lowEquiv i k hik r).val))
    (fun r => hf.comp (measurable_pi_apply _))
    (low_selected_indep α x N n j i k b hj hik f hf)
    (low_selected_law α x N n j i k b hj hik f hf) (mapped_memLp f hf h₂),
    mapped_mean f hf, mapped_second f hf, h₀]
  ring

private theorem centered_iid_pair_leave {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (Z : Fin m → Ω → ℝ) (hZ : ∀ r, Measurable (Z r))
    (hI : ProbabilityTheory.iIndepFun Z μ)
    (hL : ∀ r, ProbabilityTheory.IdentDistrib (Z r) (id : ℝ → ℝ) μ ν)
    (h₂ : MemLp (id : ℝ → ℝ) 2 ν) (h₀ : (∫ z : ℝ, z ∂ν) = 0) :
    MemLp (Shao.OQ5.P35.finitePairProductSum Z) 2 μ ∧
    (∫ ω, Shao.OQ5.P35.finitePairProductSum Z ω ∂μ) = 0 ∧
    (∫ ω, Shao.OQ5.P35.finitePairProductSum Z ω ^ 2 ∂μ) =
      (m.choose 2 : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) ^ 2 ∧
    Integrable (Shao.OQ5.P35.finiteLeaveOwnSquareSum Z) μ ∧
    (∫ ω, Shao.OQ5.P35.finiteLeaveOwnSquareSum Z ω ∂μ) =
      (m : ℝ) * ((m - 1 : ℕ) : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) ^ 2 := by
  have hp₂ := Shao.OQ5.P35.finite_iid_pairProduct_memLp_two hZ hI hL h₂
  have hp₀ : (∫ ω, Shao.OQ5.P35.finitePairProductSum Z ω ∂μ) = 0 := by
    rw [Shao.OQ5.P35.finite_iid_pairProduct_integral hZ hI hL h₂, h₀]
    ring
  have hvν : ProbabilityTheory.variance (id : ℝ → ℝ) ν = ∫ z : ℝ, z ^ 2 ∂ν := by
    rw [ProbabilityTheory.variance_eq_integral measurable_id.aemeasurable]
    simp only [id_eq, h₀, sub_zero]
  have hpv := Shao.OQ5.P35.finite_iid_pairProduct_variance hZ hI hL h₂
  rw [ProbabilityTheory.variance_eq_integral hp₂.aemeasurable, hp₀, hvν, h₀] at hpv
  simp only [sub_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul,
    add_zero] at hpv
  refine ⟨hp₂, hp₀, hpv, Shao.OQ5.P35.finite_iid_leaveOwnSquare_integrable hZ hI hL h₂, ?_⟩
  rw [Shao.OQ5.P35.finite_iid_leaveOwnSquare_integral hZ hI hL h₂, h₀]
  ring

private theorem low_pair_leave_moments (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n j : ℕ) (i k : Fin n) (b : Bool) (hj : 1 ≤ j) (hik : i < k)
    (f : SparseObs → ℝ) (hf : Measurable f)
    (h₂ : MemLp f 2 (sparseLowObservationMeasure α x N j))
    (h₀ : (∫ z, f z ∂sparseLowObservationMeasure α x N j) = 0) :
    let Z := fun l : Fin n => fun ω : Fin n → SparseObs =>
      Shao.OQ5.P35.backgroundFeature {i, k} (fun a => f (ω a)) l
    MemLp (Shao.OQ5.P35.finitePairProductSum Z) 2
      (sparseBalancedPatternMeasure α x N n j i k b) ∧
    (∫ ω, Shao.OQ5.P35.finitePairProductSum Z ω
      ∂sparseBalancedPatternMeasure α x N n j i k b) = 0 ∧
    (∫ ω, Shao.OQ5.P35.finitePairProductSum Z ω ^ 2
      ∂sparseBalancedPatternMeasure α x N n j i k b) =
      ((n - 2).choose 2 : ℝ) * (∫ z, f z ^ 2 ∂sparseLowObservationMeasure α x N j) ^ 2 ∧
    Integrable (Shao.OQ5.P35.finiteLeaveOwnSquareSum Z)
      (sparseBalancedPatternMeasure α x N n j i k b) ∧
    (∫ ω, Shao.OQ5.P35.finiteLeaveOwnSquareSum Z ω
      ∂sparseBalancedPatternMeasure α x N n j i k b) =
      ((n - 2 : ℕ) : ℝ) * ((n - 3 : ℕ) : ℝ) *
        (∫ z, f z ^ 2 ∂sparseLowObservationMeasure α x N j) ^ 2 := by
  let : IsProbabilityMeasure (sparseLowObservationMeasure α x N j) :=
    sparseLowObservationMeasure_probability α x N j hj
  let : IsProbabilityMeasure ((sparseLowObservationMeasure α x N j).map f) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).mpr inferInstance
  let : IsProbabilityMeasure (sparseBalancedPatternMeasure α x N n j i k b) :=
    sparseBalancedPatternMeasure_probability α x N n j i k b hj hik
  dsimp only
  rw [masked_pair_reindex i k hik (fun (a : Fin n) (ω : Fin n → SparseObs) => f (ω a)),
    masked_leaveOwn_reindex i k hik (fun (a : Fin n) (ω : Fin n → SparseObs) => f (ω a))]
  have hmean : (∫ z : ℝ, z ∂(sparseLowObservationMeasure α x N j).map f) = 0 := by
    rw [mapped_mean f hf, h₀]
  have h := centered_iid_pair_leave
    (fun (r : Fin (n - 2)) (ω : Fin n → SparseObs) => f (ω (lowEquiv i k hik r).val))
    (fun r => hf.comp (measurable_pi_apply _))
    (low_selected_indep α x N n j i k b hj hik f hf)
    (low_selected_law α x N n j i k b hj hik f hf) (mapped_memLp f hf h₂) hmean
  simpa only [mapped_second f hf, Nat.sub_sub, show 2 + 1 = (3 : ℕ) by rfl] using h

private def targetIndex {n : ℕ} (i k : Fin n) (r : Fin 2) : Fin n :=
  if r = 0 then i else k

private theorem targetIndex_injective {n : ℕ} (i k : Fin n) (hik : i < k) :
    Function.Injective (targetIndex i k) := by
  intro r s hrs
  by_cases hr : r = 0 <;> by_cases hs : s = 0
  · exact hr.trans hs.symm
  · have heq : i = k := by simpa [targetIndex, hr, hs] using hrs
    exact False.elim ((ne_of_lt hik) heq)
  · have heq : k = i := by simpa [targetIndex, hr, hs] using hrs
    exact False.elim ((ne_of_lt hik).symm heq)
  · apply Fin.ext
    have hr₀ : r.val ≠ 0 := fun h => hr (Fin.ext h)
    have hs₀ : s.val ≠ 0 := fun h => hs (Fin.ext h)
    have hr₂ := r.isLt
    have hs₂ := s.isLt
    omega

private theorem target_noise_law (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n j : ℕ) (i k : Fin n) (b : Bool) (hj : 1 ≤ j) (hik : i < k) (r : Fin 2) :
    ProbabilityTheory.IdentDistrib
      (fun ω : Fin n → SparseObs => (ω (targetIndex i k r)).1.1) (id : ℝ → ℝ)
      (sparseBalancedPatternMeasure α x N n j i k b) Shao.OQ5.P35.noiseLaw := by
  classical
  refine ⟨(measurable_fst.comp (measurable_fst.comp (measurable_pi_apply _))).aemeasurable,
    measurable_id.aemeasurable, ?_⟩
  rw [Measure.map_id]
  change Measure.map ((Prod.fst ∘ Prod.fst : SparseObs → ℝ) ∘
    (fun ω : Fin n → SparseObs => ω (targetIndex i k r))) _ = _
  rw [← Measure.map_map (measurable_fst.comp measurable_fst) (measurable_pi_apply _),
    sparseBalancedPatternMeasure,
    sparseBalancedPairPattern_cond_coordinate_law α x N n j i k b hj hik]
  by_cases hr : r = 0
  · simpa [targetIndex, hr, Function.comp_def] using
      sparseTargetObservation_noise_law α x N j b hj
  · simpa [targetIndex, hr, (ne_of_lt hik).symm, Function.comp_def] using
      sparseTargetObservation_noise_law α x N j (!b) hj

private theorem target_noise_moments (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n j : ℕ) (i k : Fin n) (b : Bool) (hj : 1 ≤ j) (hik : i < k) :
    MemLp (fun ω : Fin n → SparseObs => (ω i).1.1 + (ω k).1.1) 2
      (sparseBalancedPatternMeasure α x N n j i k b) ∧
    (∫ ω : Fin n → SparseObs, (ω i).1.1 + (ω k).1.1
      ∂sparseBalancedPatternMeasure α x N n j i k b) = 0 ∧
    (∫ ω : Fin n → SparseObs, ((ω i).1.1 + (ω k).1.1) ^ 2
      ∂sparseBalancedPatternMeasure α x N n j i k b) = 2 / 3 := by
  let μ := sparseBalancedPatternMeasure α x N n j i k b
  let : IsProbabilityMeasure μ := sparseBalancedPatternMeasure_probability α x N n j i k b hj hik
  let Z : Fin 2 → (Fin n → SparseObs) → ℝ := fun r ω => (ω (targetIndex i k r)).1.1
  have hZ (r : Fin 2) : Measurable (Z r) :=
    measurable_fst.comp (measurable_fst.comp (measurable_pi_apply _))
  have hL (r : Fin 2) : ProbabilityTheory.IdentDistrib (Z r) (id : ℝ → ℝ)
      μ Shao.OQ5.P35.noiseLaw := target_noise_law α x N n j i k b hj hik r
  have h₂ : MemLp (id : ℝ → ℝ) 2 Shao.OQ5.P35.noiseLaw :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr Shao.OQ5.P35.integrable_noiseLaw_sq
  have hcoord₂ (r : Fin 2) : MemLp (Z r) 2 μ := (hL r).memLp_iff.mpr h₂
  have hcoord₀ (r : Fin 2) : (∫ ω, Z r ω ∂μ) = 0 := by
    rw [(hL r).integral_eq]
    simpa only [id_eq] using Shao.OQ5.P35.integral_noiseLaw_id
  have hI : ProbabilityTheory.iIndepFun Z μ :=
    ((iIndepFun_sparseBalancedPairPattern_cond α x N n j i k b hj hik).precomp
      (targetIndex_injective i k hik)).comp (fun _ => fun z : SparseObs => z.1.1)
      (fun _ => measurable_fst.comp measurable_fst)
  have hsum : Shao.OQ5.P35.finiteFeatureSum Z =
      (fun ω : Fin n → SparseObs => (ω i).1.1 + (ω k).1.1) := by
    funext ω
    simp [Shao.OQ5.P35.finiteFeatureSum, Fin.sum_univ_two, Z, targetIndex]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hsum]
    exact memLp_finsetSum Finset.univ (fun r _ => hcoord₂ r)
  · rw [← hsum]
    unfold Shao.OQ5.P35.finiteFeatureSum
    rw [integral_finsetSum _ (fun r _ => (hcoord₂ r).integrable (by norm_num))]
    simp only [hcoord₀, Finset.sum_const_zero]
  · have hsquare := Shao.OQ5.P35.finite_iid_sumSquare_integral hZ hI hL h₂
    rw [Shao.OQ5.P35.integral_noiseLaw_id, Shao.OQ5.P35.integral_noiseLaw_sq] at hsquare
    norm_num at hsquare
    simpa only [hsum] using hsquare


theorem memLp_sparseBalancedBackgroundG_two :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  0 < α → SparseSelectionCore α x N → 1 ≤ j → i < k →
  MemLp (fun ω : Fin n → SparseObs =>
    Shao.OQ5.P35.backgroundSum ({i, k} : Finset (Fin n))
      (fun l => sparsePopulationG α x N (ω l))) 2 (sparseBalancedPatternMeasure α x N n j i k b) := by
  intro α x N n j i k b hα hN hj hik
  exact low_sum_memLp α x N n j i k b hj hik (sparsePopulationG α x N)
    (measurable_sparsePopulationG α x N) (memLp_sparseLowObservationG_two α x N j hα hN hj)

theorem integral_sparseBalancedBackgroundG_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  0 < α → SparseSelectionCore α x N → 1 ≤ j → i < k →
  (∫ ω : Fin n → SparseObs, Shao.OQ5.P35.backgroundSum ({i, k} : Finset (Fin n))
      (fun l => sparsePopulationG α x N (ω l))
    ∂sparseBalancedPatternMeasure α x N n j i k b) = 0 := by
  intro α x N n j i k b hα hN hj hik
  exact low_sum_mean α x N n j i k b hj hik (sparsePopulationG α x N)
    (measurable_sparsePopulationG α x N) (memLp_sparseLowObservationG_two α x N j hα hN hj)
    (integral_sparseLowObservationG_zero α x N j hα hN hj)

theorem integral_sparseBalancedBackgroundG_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  0 < α → SparseSelectionCore α x N → 1 ≤ j → i < k →
  (∫ ω : Fin n → SparseObs, (Shao.OQ5.P35.backgroundSum ({i, k} : Finset (Fin n))
      (fun l => sparsePopulationG α x N (ω l))) ^ 2
    ∂sparseBalancedPatternMeasure α x N n j i k b) =
    ((n - 2 : ℕ) : ℝ) * (∫ z, sparsePopulationG α x N z ^ 2 ∂sparseLowObservationMeasure α x N j) := by
  intro α x N n j i k b hα hN hj hik
  exact low_sum_second α x N n j i k b hj hik (sparsePopulationG α x N)
    (measurable_sparsePopulationG α x N) (memLp_sparseLowObservationG_two α x N j hα hN hj)
    (integral_sparseLowObservationG_zero α x N j hα hN hj)

theorem memLp_sparseBalancedBackgroundZ_two :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  0 < α → 1 ≤ j → i < k →
  MemLp (fun ω : Fin n → SparseObs =>
    Shao.OQ5.P35.backgroundSum ({i, k} : Finset (Fin n))
      (fun l => sparsePopulationZ α x N (ω l))) 2 (sparseBalancedPatternMeasure α x N n j i k b) := by
  intro α x N n j i k b hα hj hik
  exact low_sum_memLp α x N n j i k b hj hik (sparsePopulationZ α x N)
    (measurable_sparsePopulationZ α x N) (memLp_sparseLowObservationZ_two α x N j hα hj)

theorem integral_sparseBalancedBackgroundZ_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  0 < α → 1 ≤ j → i < k →
  (∫ ω : Fin n → SparseObs, Shao.OQ5.P35.backgroundSum ({i, k} : Finset (Fin n))
      (fun l => sparsePopulationZ α x N (ω l))
    ∂sparseBalancedPatternMeasure α x N n j i k b) = 0 := by
  intro α x N n j i k b hα hj hik
  exact low_sum_mean α x N n j i k b hj hik (sparsePopulationZ α x N)
    (measurable_sparsePopulationZ α x N) (memLp_sparseLowObservationZ_two α x N j hα hj)
    (integral_sparseLowObservationZ_zero α x N j hα hj)

theorem integral_sparseBalancedBackgroundZ_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  0 < α → 1 ≤ j → i < k →
  (∫ ω : Fin n → SparseObs, (Shao.OQ5.P35.backgroundSum ({i, k} : Finset (Fin n))
      (fun l => sparsePopulationZ α x N (ω l))) ^ 2
    ∂sparseBalancedPatternMeasure α x N n j i k b) =
    ((n - 2 : ℕ) : ℝ) * (∫ z, sparsePopulationZ α x N z ^ 2 ∂sparseLowObservationMeasure α x N j) := by
  intro α x N n j i k b hα hj hik
  exact low_sum_second α x N n j i k b hj hik (sparsePopulationZ α x N)
    (measurable_sparsePopulationZ α x N) (memLp_sparseLowObservationZ_two α x N j hα hj)
    (integral_sparseLowObservationZ_zero α x N j hα hj)

theorem memLp_sparseBalancedBackgroundPair_two :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  0 < α → 1 ≤ j → i < k →
  MemLp (fun ω : Fin n → SparseObs => Shao.OQ5.P35.finitePairProductSum
      (fun l : Fin n => fun ω : Fin n → SparseObs =>
        Shao.OQ5.P35.backgroundFeature ({i, k} : Finset (Fin n))
          (fun a => sparsePopulationZ α x N (ω a)) l) ω) 2
    (sparseBalancedPatternMeasure α x N n j i k b) := by
  intro α x N n j i k b hα hj hik
  exact (low_pair_leave_moments α x N n j i k b hj hik (sparsePopulationZ α x N)
    (measurable_sparsePopulationZ α x N) (memLp_sparseLowObservationZ_two α x N j hα hj)
    (integral_sparseLowObservationZ_zero α x N j hα hj)).1

theorem integral_sparseBalancedBackgroundPair_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  0 < α → 1 ≤ j → i < k →
  (∫ ω : Fin n → SparseObs, Shao.OQ5.P35.finitePairProductSum
      (fun l : Fin n => fun ω : Fin n → SparseObs =>
        Shao.OQ5.P35.backgroundFeature ({i, k} : Finset (Fin n))
          (fun a => sparsePopulationZ α x N (ω a)) l) ω
    ∂sparseBalancedPatternMeasure α x N n j i k b) = 0 := by
  intro α x N n j i k b hα hj hik
  exact (low_pair_leave_moments α x N n j i k b hj hik (sparsePopulationZ α x N)
    (measurable_sparsePopulationZ α x N) (memLp_sparseLowObservationZ_two α x N j hα hj)
    (integral_sparseLowObservationZ_zero α x N j hα hj)).2.1

theorem integral_sparseBalancedBackgroundPair_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  0 < α → 1 ≤ j → i < k →
  (∫ ω : Fin n → SparseObs, (Shao.OQ5.P35.finitePairProductSum
      (fun l : Fin n => fun ω : Fin n → SparseObs =>
        Shao.OQ5.P35.backgroundFeature ({i, k} : Finset (Fin n))
          (fun a => sparsePopulationZ α x N (ω a)) l) ω) ^ 2
    ∂sparseBalancedPatternMeasure α x N n j i k b) =
    ((n - 2).choose 2 : ℝ) * (∫ z, sparsePopulationZ α x N z ^ 2 ∂sparseLowObservationMeasure α x N j) ^ 2 := by
  intro α x N n j i k b hα hj hik
  exact (low_pair_leave_moments α x N n j i k b hj hik (sparsePopulationZ α x N)
    (measurable_sparsePopulationZ α x N) (memLp_sparseLowObservationZ_two α x N j hα hj)
    (integral_sparseLowObservationZ_zero α x N j hα hj)).2.2.1

theorem integrable_sparseBalancedBackgroundLeaveOwnSquare :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  0 < α → 1 ≤ j → i < k →
  Integrable (fun ω : Fin n → SparseObs => Shao.OQ5.P35.finiteLeaveOwnSquareSum
      (fun l : Fin n => fun ω : Fin n → SparseObs =>
        Shao.OQ5.P35.backgroundFeature ({i, k} : Finset (Fin n))
          (fun a => sparsePopulationZ α x N (ω a)) l) ω)
    (sparseBalancedPatternMeasure α x N n j i k b) := by
  intro α x N n j i k b hα hj hik
  exact (low_pair_leave_moments α x N n j i k b hj hik (sparsePopulationZ α x N)
    (measurable_sparsePopulationZ α x N) (memLp_sparseLowObservationZ_two α x N j hα hj)
    (integral_sparseLowObservationZ_zero α x N j hα hj)).2.2.2.1

theorem integral_sparseBalancedBackgroundLeaveOwnSquare :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  0 < α → 1 ≤ j → i < k →
  (∫ ω : Fin n → SparseObs, Shao.OQ5.P35.finiteLeaveOwnSquareSum
      (fun l : Fin n => fun ω : Fin n → SparseObs =>
        Shao.OQ5.P35.backgroundFeature ({i, k} : Finset (Fin n))
          (fun a => sparsePopulationZ α x N (ω a)) l) ω
    ∂sparseBalancedPatternMeasure α x N n j i k b) =
    ((n - 2 : ℕ) : ℝ) * ((n - 3 : ℕ) : ℝ) * (∫ z, sparsePopulationZ α x N z ^ 2 ∂sparseLowObservationMeasure α x N j) ^ 2 := by
  intro α x N n j i k b hα hj hik
  exact (low_pair_leave_moments α x N n j i k b hj hik (sparsePopulationZ α x N)
    (measurable_sparsePopulationZ α x N) (memLp_sparseLowObservationZ_two α x N j hα hj)
    (integral_sparseLowObservationZ_zero α x N j hα hj)).2.2.2.2

theorem memLp_sparseBalancedTargetNoiseSum_two :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  1 ≤ j → i < k →
  MemLp (fun ω : Fin n → SparseObs => (ω i).1.1 + (ω k).1.1) 2
    (sparseBalancedPatternMeasure α x N n j i k b) := by
  intro α x N n j i k b hj hik
  exact (target_noise_moments α x N n j i k b hj hik).1

theorem integral_sparseBalancedTargetNoiseSum_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  1 ≤ j → i < k →
  (∫ ω : Fin n → SparseObs, (ω i).1.1 + (ω k).1.1
    ∂sparseBalancedPatternMeasure α x N n j i k b) = 0 := by
  intro α x N n j i k b hj hik
  exact (target_noise_moments α x N n j i k b hj hik).2.1

theorem integral_sparseBalancedTargetNoiseSum_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  1 ≤ j → i < k →
  (∫ ω : Fin n → SparseObs, ((ω i).1.1 + (ω k).1.1) ^ 2
    ∂sparseBalancedPatternMeasure α x N n j i k b) = 2 / 3 := by
  intro α x N n j i k b hj hik
  exact (target_noise_moments α x N n j i k b hj hik).2.2

end Shao.OQ5.P53
