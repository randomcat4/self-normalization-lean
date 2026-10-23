import Shao.OQ5.P53.SparseConditionalBackgroundMoments

/-!
# True conditional numerator and centered-row jackknife bounds

The measure throughout is the actual balanced-pattern conditional law.
The numerator identity is used only almost everywhere on that pattern.
For the studentizer, the original random centering is removed by the
qualified centered-energy inequality before the canceled rows are bounded.
Only original and conditional second moments are used.
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace Shao.OQ5.P53

local notation "SparseObs" => ((ℝ × (ℕ × Bool)) × (ℕ × Bool))

def sparseSampleNumerator (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ}
    (ω : Fin n → SparseObs) : ℝ :=
  Real.sqrt (n : ℝ) * sparseSampleU α x N ω

def sparseBalancedNumeratorMean (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) : ℝ :=
  2 * Real.sqrt (N j : ℝ) * sparseLevelShift α x N j / ((N j : ℝ) - 1)

def sparseNumeratorMomentBound (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : ℝ :=
  4 + 24 * (∫ z, sparsePopulationG α x N z ^ 2 ∂sparsePopulationMeasure α x N) +
    12 * (∫ z, sparsePopulationZ α x N z ^ 2 ∂sparsePopulationMeasure α x N) ^ 2

def sparseStudentizerMomentBound (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : ℝ :=
  4 + 16 * (∫ z, sparsePopulationG α x N z ^ 2 ∂sparsePopulationMeasure α x N) +
    16 * (∫ z, sparsePopulationZ α x N z ^ 2 ∂sparsePopulationMeasure α x N) ^ 2 + 72 * (∫ z, sparsePopulationZ α x N z ^ 2 ∂sparsePopulationMeasure α x N)

private def bgG (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ}
    (i k : Fin n) (ω : Fin n → SparseObs) : ℝ :=
  Shao.OQ5.P35.backgroundSum {i, k} (fun l => sparsePopulationG α x N (ω l))

private def bgZ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ}
    (i k : Fin n) (ω : Fin n → SparseObs) : ℝ :=
  Shao.OQ5.P35.backgroundSum {i, k} (fun l => sparsePopulationZ α x N (ω l))

private def bgPair (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ}
    (i k : Fin n) (ω : Fin n → SparseObs) : ℝ :=
  Shao.OQ5.P35.finitePairProductSum
    (fun l : Fin n => fun ω : Fin n → SparseObs =>
      Shao.OQ5.P35.backgroundFeature {i, k}
        (fun a => sparsePopulationZ α x N (ω a)) l) ω

private def bgLeave (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ}
    (i k : Fin n) (ω : Fin n → SparseObs) : ℝ :=
  Shao.OQ5.P35.finiteLeaveOwnSquareSum
    (fun l : Fin n => fun ω : Fin n → SparseObs =>
      Shao.OQ5.P35.backgroundFeature {i, k}
        (fun a => sparsePopulationZ α x N (ω a)) l) ω

private def bgGsq (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ}
    (i k : Fin n) (ω : Fin n → SparseObs) : ℝ :=
  ∑ l ∈ (Finset.univ \ {i, k}), sparsePopulationG α x N (ω l) ^ 2

private theorem integral_add_explicit {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F G : Ω → ℝ} (hF : Integrable F μ) (hG : Integrable G μ) :
    (∫ ω, F ω + G ω ∂μ) = (∫ ω, F ω ∂μ) + ∫ ω, G ω ∂μ := by
  simpa only [Pi.add_apply] using integral_add hF hG

private theorem selected_size (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ)
    (hN : SparseSelectionCore α x N) (hj : 1 ≤ j) :
    4 ≤ N j ∧ 0 ≤ sparseLevelAmplitude α x N j ∧
      sparseLevelAmplitude α x N j ≤ (N j : ℝ) := by
  have he : j - 1 + 1 = j := by omega
  have hs := hN.2.2 (j - 1)
  simp only [he] at hs
  exact ⟨hs.2.1, le_of_lt hs.2.2.2.2.1, hs.2.2.2.2.2.2.2.1⟩

private theorem pattern_ae (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n j : ℕ) (i k : Fin n) (b : Bool) :
    ∀ᵐ ω : Fin n → SparseObs ∂sparseBalancedPatternMeasure α x N n j i k b,
      ω ∈ sparseBalancedPairPattern j i k b := by
  exact ProbabilityTheory.ae_cond_mem (measurableSet_sparseBalancedPairPattern n j i k b)

private theorem pair_quadratic_identity {n : ℕ} (z : Fin n → ℝ) :
    2 * Shao.OQ5.P35.unorderedPairSum (fun a c => z a * z c) =
      (∑ a, z a) ^ 2 - ∑ a, z a ^ 2 := by
  classical
  rw [← Shao.OQ5.P35.offDiagonalSum_eq_two_unordered
    (fun a c => z a * z c) (by intro a c; exact mul_comm _ _)]
  calc
    (∑ a : Fin n, ∑ c ∈ Finset.univ.erase a, z a * z c) =
        ∑ a : Fin n, (z a * (∑ c : Fin n, z c) - z a ^ 2) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_erase_eq_sub (by simp), ← Finset.mul_sum]
      ring
    _ = (∑ a : Fin n, z a) ^ 2 - ∑ a : Fin n, z a ^ 2 := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring

private theorem bgPair_quadratic (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ}
    (i k : Fin n) (ω : Fin n → SparseObs) :
    2 * bgPair α x N i k ω = bgZ α x N i k ω ^ 2 -
      Shao.OQ5.P35.backgroundSqSum {i, k} (fun l => sparsePopulationZ α x N (ω l)) := by
  exact pair_quadratic_identity
    (Shao.OQ5.P35.backgroundFeature {i, k} (fun l => sparsePopulationZ α x N (ω l)))

private theorem low_second_comparison (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hα : 0 < α) (hN : SparseSelectionCore α x N) (hj : 1 ≤ j) :
    (∫ z, sparsePopulationG α x N z ^ 2 ∂sparseLowObservationMeasure α x N j) ≤
      2 * (∫ z, sparsePopulationG α x N z ^ 2 ∂sparsePopulationMeasure α x N) ∧
    (∫ z, sparsePopulationZ α x N z ^ 2 ∂sparseLowObservationMeasure α x N j) ≤
      2 * (∫ z, sparsePopulationZ α x N z ^ 2 ∂sparsePopulationMeasure α x N) := by
  have hq := (sparsePriorMass_bounds α x N j hj).1
  have hqpos : 0 < sparsePriorMass α x N j := by linarith
  have hq₂ : 0 < sparsePriorMass α x N j ^ 2 := sq_pos_of_pos hqpos
  have hqhalf : (1 / 2 : ℝ) ≤ sparsePriorMass α x N j ^ 2 := by
    nlinarith [sq_nonneg (sparsePriorMass α x N j - (3 / 4 : ℝ))]
  have hdiv (a : ℝ) (ha : 0 ≤ a) : a / sparsePriorMass α x N j ^ 2 ≤ 2 * a := by
    apply (div_le_iff₀ hq₂).mpr
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hqhalf)]
  exact ⟨(integral_sparseLowObservationG_sq_le α x N j hα hN hj).trans
      (hdiv _ (integral_nonneg (fun z => sq_nonneg _))),
    (integral_sparseLowObservationZ_sq_le α x N j hα hj).trans
      (hdiv _ (integral_nonneg (fun z => sq_nonneg _)))⟩

private theorem numerator_ae_formula (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hn : 3 ≤ N j) (i k : Fin (N j)) (b : Bool) :
    ∀ᵐ ω : Fin (N j) → SparseObs ∂sparseBalancedPatternMeasure α x N (N j) j i k b,
    sparseSampleNumerator α x N ω = sparseBalancedNumeratorMean α x N j +
      (Real.sqrt (N j : ℝ) * (2 / (N j : ℝ))) * ((ω i).1.1 + (ω k).1.1) +
      (Real.sqrt (N j : ℝ) * (2 / (N j : ℝ))) * bgG α x N i k ω +
      (Real.sqrt (N j : ℝ) * (2 / ((N j : ℝ) * ((N j : ℝ) - 1)))) *
        bgPair α x N i k ω := by
  classical
  filter_upwards [pattern_ae α x N (N j) j i k b] with ω hω
  rw [sparseSampleNumerator, sparseSampleU_balancedPair_formula α x N j hn i k b ω hω]
  have hp := bgPair_quadratic α x N i k ω
  dsimp only [bgZ] at hp
  rw [← hp]
  dsimp only [bgG, Shao.OQ5.P35.backgroundSum, Shao.OQ5.P35.backgroundFeature,
    sparseBalancedNumeratorMean]
  ring

private theorem numerator_data (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hα : 0 < α) (hN : SparseSelectionCore α x N) (hj : 1 ≤ j)
    (i k : Fin (N j)) (b : Bool) (hik : i < k) :
    MemLp (fun ω : Fin (N j) → SparseObs => sparseSampleNumerator α x N ω) 2
      (sparseBalancedPatternMeasure α x N (N j) j i k b) ∧
    (∫ ω : Fin (N j) → SparseObs, sparseSampleNumerator α x N ω
      ∂sparseBalancedPatternMeasure α x N (N j) j i k b) = sparseBalancedNumeratorMean α x N j ∧
    (∫ ω : Fin (N j) → SparseObs,
      (sparseSampleNumerator α x N ω - sparseBalancedNumeratorMean α x N j) ^ 2
      ∂sparseBalancedPatternMeasure α x N (N j) j i k b) ≤ sparseNumeratorMomentBound α x N := by
  let μ := sparseBalancedPatternMeasure α x N (N j) j i k b
  let : IsProbabilityMeasure μ := sparseBalancedPatternMeasure_probability α x N (N j) j i k b hj hik
  let a : ℝ := Real.sqrt (N j : ℝ) * (2 / (N j : ℝ))
  let c : ℝ := Real.sqrt (N j : ℝ) * (2 / ((N j : ℝ) * ((N j : ℝ) - 1)))
  let A : (Fin (N j) → SparseObs) → ℝ := fun ω : Fin (N j) → SparseObs => a * ((ω i).1.1 + (ω k).1.1)
  let G : (Fin (N j) → SparseObs) → ℝ := fun ω : Fin (N j) → SparseObs => a * bgG α x N i k ω
  let P : (Fin (N j) → SparseObs) → ℝ := fun ω : Fin (N j) → SparseObs => c * bgPair α x N i k ω
  let vg : ℝ := ∫ z, sparsePopulationG α x N z ^ 2 ∂sparseLowObservationMeasure α x N j
  let vz : ℝ := ∫ z, sparsePopulationZ α x N z ^ 2 ∂sparseLowObservationMeasure α x N j
  have hn4 := (selected_size α x N j hN hj).1
  have hn : 3 ≤ N j := by omega
  have hnr : (4 : ℝ) ≤ (N j : ℝ) := by exact_mod_cast hn4
  have hnpos : 0 < (N j : ℝ) := by linarith
  have hn1pos : 0 < (N j : ℝ) - 1 := by linarith
  have hn0 : (N j : ℝ) ≠ 0 := by linarith
  have hn1 : (N j : ℝ) - 1 ≠ 0 := by linarith
  have hA : MemLp A 2 μ := (memLp_sparseBalancedTargetNoiseSum_two α x N (N j) j i k b hj hik).const_mul a
  have hG : MemLp G 2 μ := (memLp_sparseBalancedBackgroundG_two α x N (N j) j i k b hα hN hj hik).const_mul a
  have hP : MemLp P 2 μ := (memLp_sparseBalancedBackgroundPair_two α x N (N j) j i k b hα hj hik).const_mul c
  have heq : (fun ω : Fin (N j) → SparseObs => sparseSampleNumerator α x N ω) =ᵐ[μ]
      (fun ω : Fin (N j) → SparseObs => sparseBalancedNumeratorMean α x N j + A ω + G ω + P ω) :=
    numerator_ae_formula α x N j hn i k b
  have hNum : MemLp (fun ω : Fin (N j) → SparseObs => sparseSampleNumerator α x N ω) 2 μ :=
    (memLp_congr_ae heq).mpr
      ((((memLp_const (sparseBalancedNumeratorMean α x N j)).add hA).add hG).add hP)
  have hbgMean : (∫ ω : Fin (N j) → SparseObs, bgG α x N i k ω ∂μ) = 0 :=
    integral_sparseBalancedBackgroundG_zero α x N (N j) j i k b hα hN hj hik
  have hpairMean : (∫ ω : Fin (N j) → SparseObs, bgPair α x N i k ω ∂μ) = 0 :=
    integral_sparseBalancedBackgroundPair_zero α x N (N j) j i k b hα hj hik
  have hbgSq : (∫ ω : Fin (N j) → SparseObs, bgG α x N i k ω ^ 2 ∂μ) =
      ((N j - 2 : ℕ) : ℝ) * vg :=
    integral_sparseBalancedBackgroundG_sq α x N (N j) j i k b hα hN hj hik
  have hpairSq : (∫ ω : Fin (N j) → SparseObs, bgPair α x N i k ω ^ 2 ∂μ) =
      ((N j - 2).choose 2 : ℝ) * vz ^ 2 :=
    integral_sparseBalancedBackgroundPair_sq α x N (N j) j i k b hα hj hik
  have hA₀ : (∫ ω : Fin (N j) → SparseObs, A ω ∂μ) = 0 := by
    dsimp only [A]
    rw [integral_const_mul, integral_sparseBalancedTargetNoiseSum_zero α x N (N j) j i k b hj hik, mul_zero]
  have hG₀ : (∫ ω : Fin (N j) → SparseObs, G ω ∂μ) = 0 := by
    dsimp only [G]
    rw [integral_const_mul, hbgMean, mul_zero]
  have hP₀ : (∫ ω : Fin (N j) → SparseObs, P ω ∂μ) = 0 := by
    dsimp only [P]
    rw [integral_const_mul, hpairMean, mul_zero]
  have hmean : (∫ ω : Fin (N j) → SparseObs, sparseSampleNumerator α x N ω ∂μ) =
      sparseBalancedNumeratorMean α x N j := by
    rw [integral_congr_ae heq,
      integral_add_explicit (F := fun ω : Fin (N j) → SparseObs => sparseBalancedNumeratorMean α x N j + A ω + G ω) (G := P)
        (((integrable_const (sparseBalancedNumeratorMean α x N j)).add (hA.integrable (by norm_num))).add (hG.integrable (by norm_num))) (hP.integrable (by norm_num)),
      integral_add_explicit (F := fun ω : Fin (N j) → SparseObs => sparseBalancedNumeratorMean α x N j + A ω) (G := G)
        ((integrable_const (sparseBalancedNumeratorMean α x N j)).add (hA.integrable (by norm_num))) (hG.integrable (by norm_num)),
      integral_add_explicit (F := fun _ω : Fin (N j) → SparseObs => sparseBalancedNumeratorMean α x N j) (G := A)
        (integrable_const (sparseBalancedNumeratorMean α x N j)) (hA.integrable (by norm_num)), hA₀, hG₀, hP₀]
    simp
  have ha₂ : a ^ 2 = 4 / (N j : ℝ) := by
    dsimp [a]
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    field_simp [hn0, hn1]
    ring
  have hc₂ : c ^ 2 = 4 / ((N j : ℝ) * ((N j : ℝ) - 1) ^ 2) := by
    dsimp [c]
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    field_simp [hn0, hn1]
    ring
  have hA₂ : (∫ ω : Fin (N j) → SparseObs, A ω ^ 2 ∂μ) = 8 / (3 * (N j : ℝ)) := by
    simp_rw [A, mul_pow]
    rw [integral_const_mul, integral_sparseBalancedTargetNoiseSum_sq α x N (N j) j i k b hj hik, ha₂]
    ring
  have hG₂ : (∫ ω : Fin (N j) → SparseObs, G ω ^ 2 ∂μ) = (4 / (N j : ℝ)) * ((N j : ℝ) - 2) * vg := by
    simp_rw [G, mul_pow]
    rw [integral_const_mul, hbgSq, ha₂,
      Nat.cast_sub (by omega : 2 ≤ N j)]
    norm_num only [Nat.cast_ofNat]
    ring
  have hP₂ : (∫ ω : Fin (N j) → SparseObs, P ω ^ 2 ∂μ) =
      (2 * ((N j : ℝ) - 2) * ((N j : ℝ) - 3) /
        ((N j : ℝ) * ((N j : ℝ) - 1) ^ 2)) * vz ^ 2 := by
    simp_rw [P, mul_pow]
    rw [integral_const_mul, hpairSq, hc₂,
      ← Shao.OQ5.P35.pairCount_eq_choose]
    unfold Shao.OQ5.P35.pairCount
    rw [Nat.cast_sub (by omega : 2 ≤ N j)]
    norm_num only [Nat.cast_ofNat]
    ring
  have hcenter : Integrable (fun ω : Fin (N j) → SparseObs =>
      (sparseSampleNumerator α x N ω - sparseBalancedNumeratorMean α x N j) ^ 2) μ :=
    (hNum.sub (memLp_const _)).integrable_sq
  have hdom : ∀ᵐ ω : Fin (N j) → SparseObs ∂μ,
      (sparseSampleNumerator α x N ω - sparseBalancedNumeratorMean α x N j) ^ 2 ≤
        3 * (A ω ^ 2 + G ω ^ 2 + P ω ^ 2) := by
    filter_upwards [heq] with ω hω
    rw [hω]
    nlinarith only [sq_nonneg (A ω - G ω), sq_nonneg (A ω - P ω), sq_nonneg (G ω - P ω)]
  have hdomI : Integrable (fun ω : Fin (N j) → SparseObs => 3 * (A ω ^ 2 + G ω ^ 2 + P ω ^ 2)) μ :=
    ((hA.integrable_sq.add hG.integrable_sq).add hP.integrable_sq).const_mul 3
  have hbound := integral_mono_ae hcenter hdomI hdom
  rw [integral_const_mul,
    integral_add_explicit (F := fun ω : Fin (N j) → SparseObs => A ω ^ 2 + G ω ^ 2)
      (G := fun ω : Fin (N j) → SparseObs => P ω ^ 2) (hA.integrable_sq.add hG.integrable_sq) hP.integrable_sq,
    integral_add_explicit (F := fun ω : Fin (N j) → SparseObs => A ω ^ 2)
      (G := fun ω : Fin (N j) → SparseObs => G ω ^ 2) hA.integrable_sq hG.integrable_sq, hA₂, hG₂, hP₂] at hbound
  have hvg : 0 ≤ vg := integral_nonneg (fun z => sq_nonneg _)
  have hvz : 0 ≤ vz := integral_nonneg (fun z => sq_nonneg _)
  have hcomp := low_second_comparison α x N j hα hN hj
  have hz₂ : vz ^ 2 ≤ 4 * (∫ z, sparsePopulationZ α x N z ^ 2 ∂sparsePopulationMeasure α x N) ^ 2 := by
    have hz₀ : 0 ≤ ∫ z, sparsePopulationZ α x N z ^ 2 ∂sparsePopulationMeasure α x N :=
      integral_nonneg (fun z => sq_nonneg _)
    nlinarith only [mul_nonneg (sub_nonneg.mpr hcomp.2) (by linarith only [hz₀, hvz] : 0 ≤ 2 * (∫ z, sparsePopulationZ α x N z ^ 2 ∂sparsePopulationMeasure α x N) + vz)]
  have hconst : 3 * (8 / (3 * (N j : ℝ))) ≤ 4 := by
    rw [show 3 * (8 / (3 * (N j : ℝ))) = 8 / (N j : ℝ) by ring]
    exact (div_le_iff₀ (by linarith : 0 < (N j : ℝ))).mpr (by linarith)
  have hlin : 3 * ((4 / (N j : ℝ)) * ((N j : ℝ) - 2) * vg) ≤ 12 * vg := by
    have hc : 12 * ((N j : ℝ) - 2) / (N j : ℝ) ≤ 12 :=
      (div_le_iff₀ (by linarith : 0 < (N j : ℝ))).mpr (by linarith)
    convert mul_le_mul_of_nonneg_right hc hvg using 1
    ring
  have hcoef : 3 * (2 * ((N j : ℝ) - 2) * ((N j : ℝ) - 3) /
      ((N j : ℝ) * ((N j : ℝ) - 1) ^ 2)) ≤ 3 := by
    have hp : 0 < (N j : ℝ) * ((N j : ℝ) - 1) ^ 2 :=
      mul_pos hnpos (sq_pos_of_pos hn1pos)
    rw [show 3 * (2 * ((N j : ℝ) - 2) * ((N j : ℝ) - 3) /
      ((N j : ℝ) * ((N j : ℝ) - 1) ^ 2)) =
      6 * ((N j : ℝ) - 2) * ((N j : ℝ) - 3) /
        ((N j : ℝ) * ((N j : ℝ) - 1) ^ 2) by ring]
    apply (div_le_iff₀ hp).mpr
    nlinarith only [hnr, mul_nonneg (sq_nonneg (N j : ℝ)) (by linarith only [hnr] : 0 ≤ (N j : ℝ) - 4)]
  have hquad := mul_le_mul_of_nonneg_right hcoef (sq_nonneg vz)
  refine ⟨hNum, hmean, hbound.trans ?_⟩
  dsimp only [sparseNumeratorMomentBound]
  nlinarith only [hconst, hlin, hquad, hz₂, hcomp.1]

theorem sparseNumeratorMomentBound_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < sparseNumeratorMomentBound α x N := by
  intro α x N
  unfold sparseNumeratorMomentBound
  have hg : 0 ≤ ∫ z, sparsePopulationG α x N z ^ 2 ∂sparsePopulationMeasure α x N :=
    integral_nonneg (fun z => sq_nonneg _)
  positivity

theorem sparseStudentizerMomentBound_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < sparseStudentizerMomentBound α x N := by
  intro α x N
  unfold sparseStudentizerMomentBound
  have hg : 0 ≤ ∫ z, sparsePopulationG α x N z ^ 2 ∂sparsePopulationMeasure α x N :=
    integral_nonneg (fun z => sq_nonneg _)
  have hz : 0 ≤ ∫ z, sparsePopulationZ α x N z ^ 2 ∂sparsePopulationMeasure α x N :=
    integral_nonneg (fun z => sq_nonneg _)
  positivity

theorem memLp_sparseSampleNumerator_cond_balanced_two :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  ∀ (i k : Fin (N j)) (b : Bool), i < k →
  MemLp (fun ω : Fin (N j) → SparseObs => sparseSampleNumerator α x N ω) 2
    (sparseBalancedPatternMeasure α x N (N j) j i k b) := by
  intro α x N j hα hN hj i k b hik
  exact (numerator_data α x N j hα hN hj i k b hik).1

theorem integral_sparseSampleNumerator_cond_balanced :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  ∀ (i k : Fin (N j)) (b : Bool), i < k →
  (∫ ω : Fin (N j) → SparseObs, sparseSampleNumerator α x N ω
    ∂sparseBalancedPatternMeasure α x N (N j) j i k b) = sparseBalancedNumeratorMean α x N j := by
  intro α x N j hα hN hj i k b hik
  exact (numerator_data α x N j hα hN hj i k b hik).2.1

theorem integral_sparseSampleNumerator_centered_sq_le :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  ∀ (i k : Fin (N j)) (b : Bool), i < k →
  (∫ ω : Fin (N j) → SparseObs,
    (sparseSampleNumerator α x N ω - sparseBalancedNumeratorMean α x N j) ^ 2
    ∂sparseBalancedPatternMeasure α x N (N j) j i k b) ≤ sparseNumeratorMomentBound α x N := by
  intro α x N j hα hN hj i k b hik
  exact (numerator_data α x N j hα hN hj i k b hik).2.2

theorem variance_sparseSampleNumerator_cond_balanced_le :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  ∀ (i k : Fin (N j)) (b : Bool), i < k →
  ProbabilityTheory.variance (fun ω : Fin (N j) → SparseObs => sparseSampleNumerator α x N ω)
    (sparseBalancedPatternMeasure α x N (N j) j i k b) ≤ sparseNumeratorMomentBound α x N := by
  intro α x N j hα hN hj i k b hik
  have h₂ := memLp_sparseSampleNumerator_cond_balanced_two α x N j hα hN hj i k b hik
  let : IsProbabilityMeasure (sparseBalancedPatternMeasure α x N (N j) j i k b) :=
    sparseBalancedPatternMeasure_probability α x N (N j) j i k b hj hik
  rw [ProbabilityTheory.variance_eq_integral h₂.aemeasurable,
    integral_sparseSampleNumerator_cond_balanced α x N j hα hN hj i k b hik]
  exact integral_sparseSampleNumerator_centered_sq_le α x N j hα hN hj i k b hik

private theorem sum_pair_complement {n : ℕ} (i k : Fin n) (hik : i < k)
    (F : Fin n → ℝ) :
    (∑ l : Fin n, F l) = F i + F k + ∑ l ∈ (Finset.univ \ {i, k}), F l := by
  classical
  have hs : (Finset.univ.erase i).erase k = (Finset.univ \ {i, k} : Finset (Fin n)) := by
    ext l
    simp [and_comm]
  rw [← hs, Finset.sum_erase_eq_sub (by simp [(ne_of_lt hik).symm]),
    Finset.sum_erase_eq_sub (by simp)]
  ring

private theorem low_coordinate_map (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n j : ℕ) (i k : Fin n) (b : Bool) (hj : 1 ≤ j) (hik : i < k)
    (l : Fin n) (hl : l ∈ (Finset.univ \ {i, k} : Finset (Fin n))) :
    (sparseBalancedPatternMeasure α x N n j i k b).map (fun ω : Fin n → SparseObs => ω l) =
      sparseLowObservationMeasure α x N j := by
  classical
  have hnot := (Finset.mem_sdiff.mp hl).2
  have hi : l ≠ i := by intro h; exact hnot (by simp [h])
  have hk : l ≠ k := by intro h; exact hnot (by simp [h])
  simpa only [sparseBalancedPatternMeasure, hi, hk, ite_false] using
    sparseBalancedPairPattern_cond_coordinate_law α x N n j i k b hj hik l

private theorem low_coordinate_square (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n j : ℕ) (i k : Fin n) (b : Bool) (hj : 1 ≤ j) (hik : i < k)
    (f : SparseObs → ℝ) (hf : Measurable f)
    (h₂ : MemLp f 2 (sparseLowObservationMeasure α x N j))
    (l : Fin n) (hl : l ∈ (Finset.univ \ {i, k} : Finset (Fin n))) :
    Integrable (fun ω : Fin n → SparseObs => f (ω l) ^ 2)
      (sparseBalancedPatternMeasure α x N n j i k b) ∧
    (∫ ω : Fin n → SparseObs, f (ω l) ^ 2 ∂sparseBalancedPatternMeasure α x N n j i k b) =
      ∫ z, f z ^ 2 ∂sparseLowObservationMeasure α x N j := by
  have hmap := low_coordinate_map α x N n j i k b hj hik l hl
  have hc : MemLp (fun ω : Fin n → SparseObs => f (ω l)) 2
      (sparseBalancedPatternMeasure α x N n j i k b) := by
    rw [← hmap] at h₂
    exact (memLp_map_measure_iff hf.aestronglyMeasurable (measurable_pi_apply l).aemeasurable).mp h₂
  refine ⟨hc.integrable_sq, ?_⟩
  rw [← hmap]
  have hEval : AEMeasurable (fun ω : Fin n → SparseObs => ω l)
      (sparseBalancedPatternMeasure α x N n j i k b) := (measurable_pi_apply l).aemeasurable
  have hSquare : AEStronglyMeasurable (fun z : SparseObs => f z ^ 2)
      ((sparseBalancedPatternMeasure α x N n j i k b).map (fun ω : Fin n → SparseObs => ω l)) :=
    (hf.pow_const 2).aestronglyMeasurable
  exact (integral_map hEval hSquare).symm

private theorem bgGsq_data (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n j : ℕ) (i k : Fin n) (b : Bool) (hα : 0 < α)
    (hN : SparseSelectionCore α x N) (hj : 1 ≤ j) (hik : i < k) :
    Integrable (bgGsq α x N i k) (sparseBalancedPatternMeasure α x N n j i k b) ∧
    (∫ ω : Fin n → SparseObs, bgGsq α x N i k ω ∂sparseBalancedPatternMeasure α x N n j i k b) =
      ((n - 2 : ℕ) : ℝ) *
        (∫ z, sparsePopulationG α x N z ^ 2 ∂sparseLowObservationMeasure α x N j) := by
  classical
  have hd (l : Fin n) (hl : l ∈ (Finset.univ \ {i, k} : Finset (Fin n))) :=
    low_coordinate_square α x N n j i k b hj hik (sparsePopulationG α x N)
      (measurable_sparsePopulationG α x N) (memLp_sparseLowObservationG_two α x N j hα hN hj) l hl
  have hI := integrable_finsetSum (Finset.univ \ {i, k}) (fun l hl => (hd l hl).1)
  refine ⟨hI, ?_⟩
  change (∫ ω : Fin n → SparseObs,
    (∑ l ∈ (Finset.univ \ {i, k}), sparsePopulationG α x N (ω l) ^ 2)
      ∂sparseBalancedPatternMeasure α x N n j i k b) = _
  rw [integral_finsetSum _ (fun l hl => (hd l hl).1)]
  calc
    (∑ l ∈ (Finset.univ \ {i, k}), ∫ ω : Fin n → SparseObs,
        sparsePopulationG α x N (ω l) ^ 2 ∂sparseBalancedPatternMeasure α x N n j i k b) =
      ∑ _l ∈ (Finset.univ \ {i, k} : Finset (Fin n)),
        (∫ z, sparsePopulationG α x N z ^ 2 ∂sparseLowObservationMeasure α x N j) := by
      exact Finset.sum_congr rfl (fun l hl => (hd l hl).2)
    _ = _ := by simp [Finset.card_sdiff, ne_of_lt hik]

private theorem target_noise_square (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n j : ℕ) (i k : Fin n) (b : Bool) (hj : 1 ≤ j) (hik : i < k)
    (l : Fin n) (hl : l = i ∨ l = k) :
    Integrable (fun ω : Fin n → SparseObs => (ω l).1.1 ^ 2)
      (sparseBalancedPatternMeasure α x N n j i k b) ∧
    (∫ ω : Fin n → SparseObs, (ω l).1.1 ^ 2
      ∂sparseBalancedPatternMeasure α x N n j i k b) = 1 / 3 := by
  classical
  let μ := sparseBalancedPatternMeasure α x N n j i k b
  have hm := sparseBalancedPairPattern_cond_coordinate_law α x N n j i k b hj hik l
  obtain ⟨b', hobs⟩ : ∃ b' : Bool,
      μ.map (fun ω : Fin n → SparseObs => ω l) = sparseTargetObservationMeasure α x N j b' := by
    rcases hl with rfl | rfl
    · exact ⟨b, by simpa [μ, sparseBalancedPatternMeasure] using hm⟩
    · exact ⟨!b, by simpa [μ, sparseBalancedPatternMeasure, (ne_of_lt hik).symm] using hm⟩
  have hmeas : Measurable (fun ω : Fin n → SparseObs => (ω l).1.1) :=
    measurable_fst.comp (measurable_fst.comp (measurable_pi_apply l))
  have hmap : μ.map (fun ω : Fin n → SparseObs => (ω l).1.1) = Shao.OQ5.P35.noiseLaw := by
    change μ.map ((Prod.fst ∘ Prod.fst : SparseObs → ℝ) ∘
      (fun ω : Fin n → SparseObs => ω l)) = _
    rw [← Measure.map_map (measurable_fst.comp measurable_fst) (measurable_pi_apply l), hobs]
    simpa only [Function.comp_def] using sparseTargetObservation_noise_law α x N j b' hj
  have h₂ : MemLp (id : ℝ → ℝ) 2 Shao.OQ5.P35.noiseLaw :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr Shao.OQ5.P35.integrable_noiseLaw_sq
  have hc : MemLp (fun ω : Fin n → SparseObs => (ω l).1.1) 2 μ := by
    rw [← hmap] at h₂
    exact (memLp_map_measure_iff aestronglyMeasurable_id hmeas.aemeasurable).mp h₂
  refine ⟨hc.integrable_sq, ?_⟩
  calc
    (∫ ω : Fin n → SparseObs, (ω l).1.1 ^ 2 ∂μ) =
        ∫ z : ℝ, z ^ 2 ∂μ.map (fun ω : Fin n → SparseObs => (ω l).1.1) :=
      (integral_map hmeas.aemeasurable (measurable_id.pow_const 2).aestronglyMeasurable).symm
    _ = 1 / 3 := by rw [hmap, Shao.OQ5.P35.integral_noiseLaw_sq]

private theorem bgLeave_eq_complement (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    {n : ℕ} (i k : Fin n) (hik : i < k) (ω : Fin n → SparseObs) :
    bgLeave α x N i k ω = ∑ l ∈ (Finset.univ \ {i, k}),
      sparsePopulationZ α x N (ω l) ^ 2 *
        (bgZ α x N i k ω - sparsePopulationZ α x N (ω l)) ^ 2 := by
  classical
  unfold bgLeave Shao.OQ5.P35.finiteLeaveOwnSquareSum
  change (∑ l : Fin n,
    Shao.OQ5.P35.backgroundFeature {i, k} (fun a => sparsePopulationZ α x N (ω a)) l ^ 2 *
      (bgZ α x N i k ω - Shao.OQ5.P35.backgroundFeature {i, k}
        (fun a => sparsePopulationZ α x N (ω a)) l) ^ 2) = _
  rw [sum_pair_complement i k hik]
  have hiJ : i ∈ ({i, k} : Finset (Fin n)) := by simp
  have hkJ : k ∈ ({i, k} : Finset (Fin n)) := by simp
  simp only [Shao.OQ5.P35.backgroundFeature, hiJ, hkJ,
    ite_true, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_mul, zero_add]
  apply Finset.sum_congr rfl
  intro l hl
  have hnot := (Finset.mem_sdiff.mp hl).2
  simp only [hnot, ite_false]

private def rowEnergyBound (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ)
    (i k : Fin (N j)) (ω : Fin (N j) → SparseObs) : ℝ :=
  (4 / ((N j : ℝ) - 1)) *
    (2 * ((ω i).1.1 ^ 2 + (ω k).1.1 ^ 2) +
      (4 * sparseLevelAmplitude α x N j ^ 2 / ((N j : ℝ) - 2) ^ 2) * bgZ α x N i k ω ^ 2 +
      2 * bgGsq α x N i k ω + (2 / ((N j : ℝ) - 2) ^ 2) * bgLeave α x N i k ω)

private theorem studentizer_ae_energy (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hn : 3 ≤ N j) (i k : Fin (N j)) (b : Bool) (hik : i < k) :
    ∀ᵐ ω : Fin (N j) → SparseObs ∂sparseBalancedPatternMeasure α x N (N j) j i k b,
      sparseSampleStudentizerSq α x N ω ≤ rowEnergyBound α x N j i k ω := by
  classical
  have hnr : (3 : ℝ) ≤ N j := by exact_mod_cast hn
  have hd : (N j : ℝ) - 2 ≠ 0 := by linarith
  filter_upwards [pattern_ae α x N (N j) j i k b] with ω hω
  have ht := (sparseBalancedPairPattern_balancedTarget α x N j i k b ω hω).2.1
  have hiJ : i ∈ ({i, k} : Finset (Fin (N j))) := by simp
  have hkJ : k ∈ ({i, k} : Finset (Fin (N j))) := by simp
  have htarget (l : Fin (N j)) (hl : l ∈ ({i, k} : Finset (Fin (N j)))) :
      ((ω l).1.1 + sparsePopulationZ α x N (ω l) * bgZ α x N i k ω / ((N j : ℝ) - 2)) ^ 2 ≤
        2 * (ω l).1.1 ^ 2 +
          (2 * sparseLevelAmplitude α x N j ^ 2 / ((N j : ℝ) - 2) ^ 2) * bgZ α x N i k ω ^ 2 := by
    calc
      _ ≤ 2 * (ω l).1.1 ^ 2 +
          2 * (sparsePopulationZ α x N (ω l) * bgZ α x N i k ω / ((N j : ℝ) - 2)) ^ 2 := by
        nlinarith [sq_nonneg ((ω l).1.1 -
          sparsePopulationZ α x N (ω l) * bgZ α x N i k ω / ((N j : ℝ) - 2))]
      _ = _ := by rw [div_pow, mul_pow, ht l hl]; ring
  have hbackground (l : Fin (N j)) :
      (sparsePopulationG α x N (ω l) + sparsePopulationZ α x N (ω l) *
        (bgZ α x N i k ω - sparsePopulationZ α x N (ω l)) / ((N j : ℝ) - 2)) ^ 2 ≤
      2 * sparsePopulationG α x N (ω l) ^ 2 + (2 / ((N j : ℝ) - 2) ^ 2) *
        (sparsePopulationZ α x N (ω l) ^ 2 *
          (bgZ α x N i k ω - sparsePopulationZ α x N (ω l)) ^ 2) := by
    calc
      _ ≤ 2 * sparsePopulationG α x N (ω l) ^ 2 +
          2 * (sparsePopulationZ α x N (ω l) *
            (bgZ α x N i k ω - sparsePopulationZ α x N (ω l)) / ((N j : ℝ) - 2)) ^ 2 := by
        nlinarith [sq_nonneg (sparsePopulationG α x N (ω l) - sparsePopulationZ α x N (ω l) *
          (bgZ α x N i k ω - sparsePopulationZ α x N (ω l)) / ((N j : ℝ) - 2))]
      _ = _ := by rw [div_pow, mul_pow]; ring
  have hbg : (∑ l ∈ (Finset.univ \ {i, k}),
      (sparsePopulationG α x N (ω l) + sparsePopulationZ α x N (ω l) *
        (bgZ α x N i k ω - sparsePopulationZ α x N (ω l)) / ((N j : ℝ) - 2)) ^ 2) ≤
      2 * bgGsq α x N i k ω + (2 / ((N j : ℝ) - 2) ^ 2) * bgLeave α x N i k ω := by
    calc
      _ ≤ ∑ l ∈ (Finset.univ \ {i, k}),
          (2 * sparsePopulationG α x N (ω l) ^ 2 + (2 / ((N j : ℝ) - 2) ^ 2) *
            (sparsePopulationZ α x N (ω l) ^ 2 *
              (bgZ α x N i k ω - sparsePopulationZ α x N (ω l)) ^ 2)) :=
        Finset.sum_le_sum (fun l _ => hbackground l)
      _ = _ := by
        rw [bgLeave_eq_complement α x N i k hik ω]
        simp only [bgGsq, Finset.sum_add_distrib, Finset.mul_sum]
  have hraw := sparseSampleStudentizerSq_balancedPair_le α x N j hn i k b ω hω
  apply hraw.trans
  unfold rowEnergyBound
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (div_pos (by norm_num) (by linarith)))
  rw [sum_pair_complement i k hik]
  simp only [hiJ, hkJ, ite_true]
  have hrest : (∑ l ∈ (Finset.univ \ {i, k}),
      (if l ∈ ({i, k} : Finset (Fin (N j))) then
        (ω l).1.1 + sparsePopulationZ α x N (ω l) * bgZ α x N i k ω / ((N j : ℝ) - 2)
      else sparsePopulationG α x N (ω l) + sparsePopulationZ α x N (ω l) *
        (bgZ α x N i k ω - sparsePopulationZ α x N (ω l)) / ((N j : ℝ) - 2)) ^ 2) =
      ∑ l ∈ (Finset.univ \ {i, k}),
        (sparsePopulationG α x N (ω l) + sparsePopulationZ α x N (ω l) *
          (bgZ α x N i k ω - sparsePopulationZ α x N (ω l)) / ((N j : ℝ) - 2)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro l hl
    simp only [(Finset.mem_sdiff.mp hl).2, ite_false]
  change ((ω i).1.1 + sparsePopulationZ α x N (ω i) * bgZ α x N i k ω / ((N j : ℝ) - 2)) ^ 2 +
      ((ω k).1.1 + sparsePopulationZ α x N (ω k) * bgZ α x N i k ω / ((N j : ℝ) - 2)) ^ 2 +
      (∑ l ∈ (Finset.univ \ {i, k}),
        (if l ∈ ({i, k} : Finset (Fin (N j))) then
          (ω l).1.1 + sparsePopulationZ α x N (ω l) * bgZ α x N i k ω / ((N j : ℝ) - 2)
        else sparsePopulationG α x N (ω l) + sparsePopulationZ α x N (ω l) *
          (bgZ α x N i k ω - sparsePopulationZ α x N (ω l)) / ((N j : ℝ) - 2)) ^ 2) ≤ _
  rw [hrest]
  convert add_le_add (add_le_add (htarget i hiJ) (htarget k hkJ)) hbg using 1
  ring

private theorem studentizer_data (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hα : 0 < α) (hN : SparseSelectionCore α x N) (hj : 1 ≤ j)
    (i k : Fin (N j)) (b : Bool) (hik : i < k) :
    Integrable (fun ω : Fin (N j) → SparseObs => sparseSampleStudentizerSq α x N ω)
      (sparseBalancedPatternMeasure α x N (N j) j i k b) ∧
    (∫ ω : Fin (N j) → SparseObs, sparseSampleStudentizerSq α x N ω
      ∂sparseBalancedPatternMeasure α x N (N j) j i k b) ≤
      sparseStudentizerMomentBound α x N *
        (1 + 2 * sparseLevelAmplitude α x N j ^ 2 / (N j : ℝ) ^ 2) := by
  let μ := sparseBalancedPatternMeasure α x N (N j) j i k b
  let vg : ℝ := ∫ z, sparsePopulationG α x N z ^ 2 ∂sparseLowObservationMeasure α x N j
  let vz : ℝ := ∫ z, sparsePopulationZ α x N z ^ 2 ∂sparseLowObservationMeasure α x N j
  let g₂ : ℝ := ∫ z, sparsePopulationG α x N z ^ 2 ∂sparsePopulationMeasure α x N
  let z₂ : ℝ := ∫ z, sparsePopulationZ α x N z ^ 2 ∂sparsePopulationMeasure α x N
  let t : ℝ := sparseLevelAmplitude α x N j
  let r : ℝ := t ^ 2 / (N j : ℝ) ^ 2
  have hn4 := (selected_size α x N j hN hj).1
  have hn : 3 ≤ N j := by omega
  have hnR : (4 : ℝ) ≤ (N j : ℝ) := by exact_mod_cast hn4
  have hnpos : 0 < (N j : ℝ) := by linarith
  have h1pos : 0 < (N j : ℝ) - 1 := by linarith
  have h2pos : 0 < (N j : ℝ) - 2 := by linarith
  have hn0 := ne_of_gt hnpos
  have h1 := ne_of_gt h1pos
  have h2 := ne_of_gt h2pos
  have hni := target_noise_square α x N (N j) j i k b hj hik i (Or.inl rfl)
  have hnk := target_noise_square α x N (N j) j i k b hj hik k (Or.inr rfl)
  have hG := bgGsq_data α x N (N j) j i k b hα hN hj hik
  have hZ := memLp_sparseBalancedBackgroundZ_two α x N (N j) j i k b hα hj hik
  have hL := integrable_sparseBalancedBackgroundLeaveOwnSquare α x N (N j) j i k b hα hj hik
  have hH : Integrable (rowEnergyBound α x N j i k) μ :=
    (((((hni.1.add hnk.1).const_mul 2).add
      (hZ.integrable_sq.const_mul (4 * t ^ 2 / ((N j : ℝ) - 2) ^ 2))).add
        (hG.1.const_mul 2)).add (hL.const_mul (2 / ((N j : ℝ) - 2) ^ 2))).const_mul (4 / ((N j : ℝ) - 1))
  let T : (Fin (N j) → SparseObs) → ℝ := fun ω => 2 * ((ω i).1.1 ^ 2 + (ω k).1.1 ^ 2)
  let B : (Fin (N j) → SparseObs) → ℝ := fun ω =>
    (4 * t ^ 2 / ((N j : ℝ) - 2) ^ 2) * bgZ α x N i k ω ^ 2
  let C : (Fin (N j) → SparseObs) → ℝ := fun ω => 2 * bgGsq α x N i k ω
  let D : (Fin (N j) → SparseObs) → ℝ := fun ω =>
    (2 / ((N j : ℝ) - 2) ^ 2) * bgLeave α x N i k ω
  have hTI : Integrable T μ := (hni.1.add hnk.1).const_mul 2
  have hBI : Integrable B μ := hZ.integrable_sq.const_mul _
  have hCI : Integrable C μ := hG.1.const_mul 2
  have hDI : Integrable D μ := hL.const_mul _
  have hZsq : (∫ ω : Fin (N j) → SparseObs, bgZ α x N i k ω ^ 2 ∂μ) =
      ((N j - 2 : ℕ) : ℝ) * vz :=
    integral_sparseBalancedBackgroundZ_sq α x N (N j) j i k b hα hj hik
  have hGSq : (∫ ω : Fin (N j) → SparseObs, bgGsq α x N i k ω ∂μ) =
      ((N j - 2 : ℕ) : ℝ) * vg := hG.2
  have hLeaveMean : (∫ ω : Fin (N j) → SparseObs, bgLeave α x N i k ω ∂μ) =
      ((N j - 2 : ℕ) : ℝ) * ((N j - 3 : ℕ) : ℝ) * vz ^ 2 :=
    integral_sparseBalancedBackgroundLeaveOwnSquare α x N (N j) j i k b hα hj hik
  have hTmean : (∫ ω : Fin (N j) → SparseObs, T ω ∂μ) = 4 / 3 := by
    dsimp only [T]
    rw [integral_const_mul, integral_add_explicit hni.1 hnk.1, hni.2, hnk.2]
    norm_num
  have hBmean : (∫ ω : Fin (N j) → SparseObs, B ω ∂μ) =
      (4 * t ^ 2 / ((N j : ℝ) - 2) ^ 2) * ((N j - 2 : ℕ) : ℝ) * vz := by
    dsimp only [B]
    rw [integral_const_mul, hZsq]
    ring
  have hCmean : (∫ ω : Fin (N j) → SparseObs, C ω ∂μ) = 2 * ((N j - 2 : ℕ) : ℝ) * vg := by
    dsimp only [C]
    rw [integral_const_mul, hGSq]
    ring
  have hDmean : (∫ ω : Fin (N j) → SparseObs, D ω ∂μ) =
      (2 / ((N j : ℝ) - 2) ^ 2) * ((N j - 2 : ℕ) : ℝ) * ((N j - 3 : ℕ) : ℝ) * vz ^ 2 := by
    dsimp only [D]
    rw [integral_const_mul, hLeaveMean]
    ring
  have hHint : (∫ ω : Fin (N j) → SparseObs, rowEnergyBound α x N j i k ω ∂μ) =
      (4 / ((N j : ℝ) - 1)) * (4 / 3 +
        (4 * t ^ 2 / ((N j : ℝ) - 2) ^ 2) * ((N j : ℝ) - 2) * vz +
        2 * ((N j : ℝ) - 2) * vg +
        (2 / ((N j : ℝ) - 2) ^ 2) * ((N j : ℝ) - 2) * ((N j : ℝ) - 3) * vz ^ 2) := by
    change (∫ ω : Fin (N j) → SparseObs,
      (4 / ((N j : ℝ) - 1)) * (T ω + B ω + C ω + D ω) ∂μ) = _
    rw [integral_const_mul,
      integral_add_explicit (F := fun ω : Fin (N j) → SparseObs => T ω + B ω + C ω) (G := D) ((hTI.add hBI).add hCI) hDI,
      integral_add_explicit (F := fun ω : Fin (N j) → SparseObs => T ω + B ω) (G := C) (hTI.add hBI) hCI,
      integral_add_explicit (F := T) (G := B) hTI hBI,
      hTmean, hBmean, hCmean, hDmean,
      Nat.cast_sub (by omega : 2 ≤ N j), Nat.cast_sub (by omega : 3 ≤ N j)]
    norm_num only [Nat.cast_ofNat]
  have hdom := studentizer_ae_energy α x N j hn i k b hik
  have hRI : Integrable (fun ω : Fin (N j) → SparseObs => sparseSampleStudentizerSq α x N ω) μ :=
    hH.mono' (measurable_sparseSampleStudentizerSq α x N (N j)).aestronglyMeasurable
      (hdom.mono (fun ω hω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sparseSampleStudentizerSq_nonneg α x N (N j) hn ω)]
        exact hω))
  have hbound := integral_mono_ae hRI hH hdom
  rw [hHint] at hbound
  have hvg : 0 ≤ vg := integral_nonneg (fun z => sq_nonneg _)
  have hvz : 0 ≤ vz := integral_nonneg (fun z => sq_nonneg _)
  have hg₂ : 0 ≤ g₂ := integral_nonneg (fun z => sq_nonneg _)
  have hz₂ : 0 ≤ z₂ := integral_nonneg (fun z => sq_nonneg _)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hcomp := low_second_comparison α x N j hα hN hj
  have hzsq : vz ^ 2 ≤ 4 * z₂ ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hcomp.2) (by linarith only [hz₂, hvz] : 0 ≤ 2 * z₂ + vz)]
  have hconst : (4 / ((N j : ℝ) - 1)) * (4 / 3) ≤ 8 / 3 := by
    have hc : 4 / ((N j : ℝ) - 1) ≤ 2 :=
      (div_le_iff₀ h1pos).mpr (by linarith only [hnR])
    calc
      _ ≤ 2 * (4 / 3) := mul_le_mul_of_nonneg_right hc (by norm_num)
      _ = _ := by norm_num
  have hlin : (4 / ((N j : ℝ) - 1)) * (2 * ((N j : ℝ) - 2) * vg) ≤ 8 * vg := by
    have hc : 8 * ((N j : ℝ) - 2) / ((N j : ℝ) - 1) ≤ 8 :=
      (div_le_iff₀ h1pos).mpr (by linarith)
    convert mul_le_mul_of_nonneg_right hc hvg using 1
    ring
  have hzcoef : 8 * ((N j : ℝ) - 3) / (((N j : ℝ) - 1) * ((N j : ℝ) - 2)) ≤ 4 := by
    apply (div_le_iff₀ (mul_pos h1pos h2pos)).mpr
    nlinarith only [sq_nonneg ((N j : ℝ) - (5 / 2 : ℝ))]
  have hquad : (4 / ((N j : ℝ) - 1)) *
      ((2 / ((N j : ℝ) - 2) ^ 2) * ((N j : ℝ) - 2) * ((N j : ℝ) - 3) * vz ^ 2) ≤ 4 * vz ^ 2 := by
    convert mul_le_mul_of_nonneg_right hzcoef (sq_nonneg vz) using 1
    field_simp [h1, h2]
    ring
  have htcoef : 16 / (((N j : ℝ) - 1) * ((N j : ℝ) - 2)) ≤ 72 / (N j : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (mul_pos h1pos h2pos) (by positivity : 0 < (N j : ℝ) ^ 2)).mpr
    nlinarith only [hnR, mul_nonneg (le_of_lt hnpos) (by linarith only [hnR] : 0 ≤ (N j : ℝ) - 4)]
  have htbound : (4 / ((N j : ℝ) - 1)) *
      ((4 * t ^ 2 / ((N j : ℝ) - 2) ^ 2) * ((N j : ℝ) - 2) * vz) ≤ 72 * vz * r := by
    convert mul_le_mul_of_nonneg_right htcoef (mul_nonneg (sq_nonneg t) hvz) using 1
    · field_simp [h1, h2]
      ring
    · dsimp [r]
      ring
  have hsimple : (∫ ω : Fin (N j) → SparseObs, sparseSampleStudentizerSq α x N ω ∂μ) ≤
      8 * vg + 8 / 3 + 4 * vz ^ 2 + 72 * vz * r := by
    apply hbound.trans
    convert add_le_add (add_le_add (add_le_add hconst htbound) hlin) hquad using 1 <;> ring
  have hfirst : 8 * vg + 8 / 3 + 4 * vz ^ 2 ≤ sparseStudentizerMomentBound α x N := by
    change 8 * vg + 8 / 3 + 4 * vz ^ 2 ≤ 4 + 16 * g₂ + 16 * z₂ ^ 2 + 72 * z₂
    nlinarith only [hcomp.1, hzsq, hz₂]
  have hzC : 72 * z₂ ≤ sparseStudentizerMomentBound α x N := by
    change 72 * z₂ ≤ 4 + 16 * g₂ + 16 * z₂ ^ 2 + 72 * z₂
    nlinarith only [hg₂, sq_nonneg z₂]
  have htail : 72 * vz * r ≤ 2 * sparseStudentizerMomentBound α x N * r := by
    have hvr := mul_le_mul_of_nonneg_right hcomp.2 hr
    have hCr := mul_le_mul_of_nonneg_right hzC hr
    nlinarith only [hvr, hCr]
  refine ⟨hRI, hsimple.trans ?_⟩
  change _ ≤ sparseStudentizerMomentBound α x N * (1 + 2 * t ^ 2 / (N j : ℝ) ^ 2)
  calc
    8 * vg + 8 / 3 + 4 * vz ^ 2 + 72 * vz * r ≤
        sparseStudentizerMomentBound α x N + 2 * sparseStudentizerMomentBound α x N * r := by
      linarith only [hfirst, htail]
    _ = _ := by dsimp only [r]; ring

theorem integrable_sparseSampleStudentizerSq_cond_balanced :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  ∀ (i k : Fin (N j)) (b : Bool), i < k →
  Integrable (fun ω : Fin (N j) → SparseObs => sparseSampleStudentizerSq α x N ω)
    (sparseBalancedPatternMeasure α x N (N j) j i k b) := by
  intro α x N j hα hN hj i k b hik
  exact (studentizer_data α x N j hα hN hj i k b hik).1

theorem integral_sparseSampleStudentizerSq_cond_balanced_le :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  ∀ (i k : Fin (N j)) (b : Bool), i < k →
  (∫ ω : Fin (N j) → SparseObs, sparseSampleStudentizerSq α x N ω
    ∂sparseBalancedPatternMeasure α x N (N j) j i k b) ≤
    sparseStudentizerMomentBound α x N *
      (1 + 2 * sparseLevelAmplitude α x N j ^ 2 / (N j : ℝ) ^ 2) := by
  intro α x N j hα hN hj i k b hik
  exact (studentizer_data α x N j hα hN hj i k b hik).2

theorem integral_sparseSampleStudentizerSq_cond_balanced_uniform_le :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  ∀ (i k : Fin (N j)) (b : Bool), i < k →
  (∫ ω : Fin (N j) → SparseObs, sparseSampleStudentizerSq α x N ω
    ∂sparseBalancedPatternMeasure α x N (N j) j i k b) ≤ 3 * sparseStudentizerMomentBound α x N := by
  intro α x N j hα hN hj i k b hik
  have hs := selected_size α x N j hN hj
  have hn : (4 : ℝ) ≤ N j := by exact_mod_cast hs.1
  have hnpos : 0 < (N j : ℝ) := by linarith
  have hsq : sparseLevelAmplitude α x N j ^ 2 ≤ (N j : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2.2) (add_nonneg hs.2.1 (Nat.cast_nonneg (N j)))]
  have hratio : sparseLevelAmplitude α x N j ^ 2 / (N j : ℝ) ^ 2 ≤ 1 :=
    (div_le_one (sq_pos_of_pos hnpos)).mpr hsq
  have hC := le_of_lt (sparseStudentizerMomentBound_pos α x N)
  have hfactor : 1 + 2 * sparseLevelAmplitude α x N j ^ 2 / (N j : ℝ) ^ 2 ≤ 3 := by
    calc
      _ = 1 + 2 * (sparseLevelAmplitude α x N j ^ 2 / (N j : ℝ) ^ 2) := by ring
      _ ≤ 1 + 2 * 1 := by
        simpa only [add_comm] using add_le_add_left
          (mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 2)) 1
      _ = 3 := by norm_num
  have hmul := mul_le_mul_of_nonneg_left hfactor hC
  exact (integral_sparseSampleStudentizerSq_cond_balanced_le α x N j hα hN hj i k b hik).trans
    (hmul.trans_eq (mul_comm _ _))

end Shao.OQ5.P53
