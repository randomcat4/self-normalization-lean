import Shao.Basic.Events
import Shao.Basic.OrderedSelection
import Shao.Basic.DeletionNumeric

/-!
# Deterministic deletion in the original chronological order

The original-length masked implication is connected to the genuinely compressed
retained path. Both events are weak crossings at genuine nonempty prefixes, and
all energies are actual sums of squared observations. Zero energy is included.
-/

set_option autoImplicit false

namespace Shao

open scoped BigOperators

variable {n : ℕ}

/-- Original-length path with exactly the deleted coordinates zeroed. -/
abbrev retainedMasked (a : Path n) (J : Finset (Fin n)) : Path n :=
  zeroOutside a (Finset.univ \ J)

/-- Original-length path supported on the deleted coordinates. -/
abbrev deletedMasked (a : Path n) (J : Finset (Fin n)) : Path n :=
  zeroOutside a J

/-- A zero-filled path has exactly the selected genuine energy. -/
theorem energy_zeroOutside (a : Path n) (s : Finset (Fin n)) :
    energy (zeroOutside a s) = ∑ i ∈ s, (a i) ^ 2 := by
  classical
  simp [energy, zeroOutside]

/-- The two masks partition each original prefix without changing its order. -/
theorem prefixSum_deletion_split (a : Path n) (J : Finset (Fin n)) (k : ℕ) :
    prefixSum a k = prefixSum (retainedMasked a J) k +
      prefixSum (deletedMasked a J) k := by
  classical
  unfold prefixSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [retainedMasked, deletedMasked, zeroOutside, Finset.mem_sdiff,
    Finset.mem_univ, true_and]
  by_cases hi : i ∈ J <;> simp [hi]

/-- Final energy is the sum of the retained and deleted genuine energies. -/
theorem energy_deletion_split (a : Path n) (J : Finset (Fin n)) :
    energy a = energy (retainedMasked a J) + energy (deletedMasked a J) := by
  classical
  unfold energy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [retainedMasked, deletedMasked, zeroOutside, Finset.mem_sdiff,
    Finset.mem_univ, true_and]
  by_cases hi : i ∈ J <;> simp [hi]

/-- Cauchy--Schwarz controls every deleted part of an original prefix. -/
theorem deleted_prefix_le (a : Path n) (J : Finset (Fin n)) (k : ℕ) :
    prefixSum (deletedMasked a J) k ≤
      Real.sqrt (J.card : ℝ) * Real.sqrt (energy (deletedMasked a J)) := by
  classical
  rw [deletedMasked, prefixSum_zeroOutside]
  unfold retainedPrefixSum
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt
    (J.filter (fun i => i.val < k)) (fun _ => (1 : ℝ)) a
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hcard : ((J.filter (fun i => i.val < k)).card : ℝ) ≤ (J.card : ℝ) := by
    exact_mod_cast Finset.card_filter_le J (fun i => i.val < k)
  have henergy : (∑ i ∈ J.filter (fun i => i.val < k), (a i) ^ 2) ≤
      energy (deletedMasked a J) := by
    rw [deletedMasked, energy_zeroOutside]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => sq_nonneg (a i))
  exact hcs.trans (mul_le_mul (Real.sqrt_le_sqrt hcard) (Real.sqrt_le_sqrt henergy)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- A weak original crossing survives deletion in the zero-filled path.

The assumption `hJ` matches the source deletion contract, although the
original-length masked implication itself does not need a retained coordinate.
-/
theorem upperCrossing_retainedMasked (a : Path n) (J : Finset (Fin n))
    (hn : 0 < n) (hJ : J.card < n) (x : ℝ) (hx : 0 < x)
    (hxx : (J.card : ℝ) < x ^ 2) (h : a ∈ upperCrossing hn x) :
    retainedMasked a J ∈ upperCrossing hn (Real.sqrt (x ^ 2 - (J.card : ℝ))) := by
  change x * Real.sqrt (energy a) ≤ upperMax a hn at h
  obtain ⟨k, hk, hkn, hcross⟩ := (upperMax_ge_iff a hn _).mp h
  change Real.sqrt (x ^ 2 - (J.card : ℝ)) * Real.sqrt (energy (retainedMasked a J)) ≤
    upperMax (retainedMasked a J) hn
  apply (upperMax_ge_iff (retainedMasked a J) hn _).mpr
  refine ⟨k, hk, hkn, ?_⟩
  apply deletion_numeric x (J.card : ℝ) (energy (retainedMasked a J))
    (energy (deletedMasked a J)) (prefixSum (retainedMasked a J) k)
    (prefixSum (deletedMasked a J) k) hx (Nat.cast_nonneg _) hxx
    (energy_nonneg _) (energy_nonneg _) (deleted_prefix_le a J k)
  rwa [← energy_deletion_split, ← prefixSum_deletion_split]

/-- Deleting fewer than all positions leaves a genuinely nonempty sample. -/
theorem retained_card_pos_of_deleted_card_lt (J : Finset (Fin n)) (hJ : J.card < n) :
    0 < (Finset.univ \ J).card := by
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  exact Nat.sub_pos_of_lt hJ

/-- The source deletion implication for the genuinely compressed retained path.

Positive retained energy gives a positive threshold, so the empty prefix cannot
create the crossing. At zero retained energy, every retained observation is zero
and the nonempty retained sample has a weak crossing.
-/
theorem upperCrossing_retainedPath_of_deletion (a : Path n) (J : Finset (Fin n))
    (hn : 0 < n) (hJ : J.card < n) (x : ℝ) (hx : 0 < x)
    (hxx : (J.card : ℝ) < x ^ 2) (h : a ∈ upperCrossing hn x) :
    retainedPath a (Finset.univ \ J) ∈
      upperCrossing (retained_card_pos_of_deleted_card_lt J hJ)
        (Real.sqrt (x ^ 2 - (J.card : ℝ))) := by
  have henergy : energy (retainedPath a (Finset.univ \ J)) =
      energy (retainedMasked a J) := by
    rw [energy_retainedPath, retainedMasked, energy_zeroOutside]
  by_cases hQ : energy (retainedMasked a J) = 0
  · exact mem_upperCrossing_of_energy_eq_zero _ _ _ (henergy.trans hQ)
  · have hQpos : 0 < energy (retainedMasked a J) :=
      lt_of_le_of_ne (energy_nonneg _) (Ne.symm hQ)
    have ht : 0 < Real.sqrt (x ^ 2 - (J.card : ℝ)) *
        Real.sqrt (energy (retainedMasked a J)) :=
      mul_pos (Real.sqrt_pos.mpr (sub_pos.mpr hxx)) (Real.sqrt_pos.mpr hQpos)
    have hmask := upperCrossing_retainedMasked a J hn hJ x hx hxx h
    change Real.sqrt (x ^ 2 - (J.card : ℝ)) * Real.sqrt (energy (retainedMasked a J)) ≤
      upperMax (retainedMasked a J) hn at hmask
    have hmax : Real.sqrt (x ^ 2 - (J.card : ℝ)) *
        Real.sqrt (energy (retainedMasked a J)) ≤ maxWithZero (retainedMasked a J) := by
      apply hmask.trans
      rw [maxWithZero_eq _ hn]
      exact le_max_right _ _
    have hret := (positive_crossing_retainedPath a (Finset.univ \ J)
      (retained_card_pos_of_deleted_card_lt J hJ) _ ht).mp hmax
    change Real.sqrt (x ^ 2 - (J.card : ℝ)) *
      Real.sqrt (energy (retainedPath a (Finset.univ \ J))) ≤
        upperMax (retainedPath a (Finset.univ \ J)) _
    rwa [henergy]

/-- Original-path weak crossings are contained in the compressed deletion event. -/
theorem upperCrossing_subset_retainedPath_of_deletion (J : Finset (Fin n))
    (hn : 0 < n) (hJ : J.card < n) (x : ℝ) (hx : 0 < x)
    (hxx : (J.card : ℝ) < x ^ 2) :
    upperCrossing hn x ⊆
      (fun a : Path n => retainedPath a (Finset.univ \ J)) ⁻¹'
        upperCrossing (retained_card_pos_of_deleted_card_lt J hJ)
          (Real.sqrt (x ^ 2 - (J.card : ℝ))) := by
  intro a h
  exact upperCrossing_retainedPath_of_deletion a J hn hJ x hx hxx h

end Shao
