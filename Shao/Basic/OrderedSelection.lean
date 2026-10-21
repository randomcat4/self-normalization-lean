import Shao.Basic.FinitePath
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

/-!
# Retaining observations in their original order

The finite set `s` records retained positions, not deleted positions. The
compressed path lists these positions increasingly, and uses actual squares.
-/

namespace Shao

open scoped BigOperators

variable {n : ℕ}

/-- Increasing enumeration of the retained positions. -/
def retainedIndex (s : Finset (Fin n)) : Fin s.card ↪o Fin n :=
  s.orderEmbOfFin rfl

/-- The retained sample, in the original chronological order. -/
def retainedPath (a : Path n) (s : Finset (Fin n)) : Path s.card :=
  fun i => a (retainedIndex s i)

/-- Number of retained positions strictly before the original cutoff `k`. -/
def retainedCount (s : Finset (Fin n)) (k : ℕ) : ℕ :=
  (s.filter (fun i => i.val < k)).card

/-- Sum of retained observations strictly before the original cutoff `k`. -/
def retainedPrefixSum (a : Path n) (s : Finset (Fin n)) (k : ℕ) : ℝ :=
  ∑ i ∈ s.filter (fun i => i.val < k), a i

/-- Original-length path with deleted observations replaced by zero. -/
def zeroOutside (a : Path n) (s : Finset (Fin n)) : Path n :=
  fun i => if i ∈ s then a i else 0

@[simp] theorem retainedIndex_mem (s : Finset (Fin n)) (i : Fin s.card) :
    retainedIndex s i ∈ s :=
  Finset.orderEmbOfFin_mem s rfl i

theorem retainedCount_le (s : Finset (Fin n)) (k : ℕ) :
    retainedCount s k ≤ s.card :=
  Finset.card_filter_le _ _

@[simp] theorem retainedCount_zero (s : Finset (Fin n)) :
    retainedCount s 0 = 0 := by
  simp [retainedCount]

@[simp] theorem retainedCount_length (s : Finset (Fin n)) :
    retainedCount s n = s.card := by
  simp only [retainedCount]
  rw [Finset.filter_eq_self.mpr (fun i _ => i.is_lt)]

theorem energy_retainedPath (a : Path n) (s : Finset (Fin n)) :
    energy (retainedPath a s) = ∑ i ∈ s, (a i) ^ 2 := by
  conv_rhs => rw [← Finset.image_orderEmbOfFin_univ s rfl]
  rw [Finset.sum_image]
  · rfl
  · intro i _ j _ hij
    exact (retainedIndex s).injective hij

theorem prefixSum_zeroOutside (a : Path n) (s : Finset (Fin n)) (k : ℕ) :
    prefixSum (zeroOutside a s) k = retainedPrefixSum a s k := by
  unfold prefixSum zeroOutside retainedPrefixSum
  symm
  calc
    _ = ∑ i ∈ s.filter (fun i => i.val < k), (if i ∈ s then a i else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [(Finset.mem_filter.mp hi).1]
    _ = _ := by
      apply Finset.sum_subset
      · intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
      · intro i hi hnot
        have his : i ∉ s := by
          intro his
          exact hnot (Finset.mem_filter.mpr ⟨his, (Finset.mem_filter.mp hi).2⟩)
        simp [his]

private theorem retained_filter_image (s : Finset (Fin n)) (k : ℕ) :
    (Finset.univ.filter (fun i : Fin s.card => (retainedIndex s i).val < k)).image
      (retainedIndex s) = s.filter (fun i => i.val < k) := by
  calc
    _ = (Finset.univ.image (retainedIndex s)).filter (fun i => i.val < k) :=
      (Finset.filter_image (s := Finset.univ) (f := retainedIndex s)
        (p := fun i : Fin n => i.val < k)).symm
    _ = _ := by
      change (Finset.univ.image (s.orderEmbOfFin rfl)).filter _ = _
      rw [Finset.image_orderEmbOfFin_univ]

private theorem retained_filter_card (s : Finset (Fin n)) (k : ℕ) :
    (Finset.univ.filter (fun i : Fin s.card => (retainedIndex s i).val < k)).card =
      retainedCount s k := by
  rw [retainedCount, ← retained_filter_image,
    Finset.card_image_of_injective _ (retainedIndex s).injective]

/-- A retained observation lies before `k` exactly when its compressed rank is
below the number retained before `k`. -/
theorem retainedIndex_lt_iff (s : Finset (Fin n)) (k : ℕ) (i : Fin s.card) :
    (retainedIndex s i).val < k ↔ i.val < retainedCount s k := by
  let t := Finset.univ.filter (fun j : Fin s.card => (retainedIndex s j).val < k)
  have ht : t.card = retainedCount s k := retained_filter_card s k
  constructor
  · intro hi
    have hsub : Finset.Iic i ⊆ t := by
      intro j hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hle := (retainedIndex s).monotone (Finset.mem_Iic.mp hj)
      exact lt_of_le_of_lt hle hi
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic, ht] at hcard
    omega
  · intro hi
    by_contra hnot
    have hsub : t ⊆ Finset.Iio i := by
      intro j hj
      have hjk := (Finset.mem_filter.mp hj).2
      apply Finset.mem_Iio.mpr
      apply (retainedIndex s).lt_iff_lt.mp
      show (retainedIndex s j).val < (retainedIndex s i).val
      omega
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio, ht] at hcard
    omega

/-- Each original prefix is exactly a compressed prefix at the retained count. -/
theorem prefixSum_retainedPath_count (a : Path n) (s : Finset (Fin n)) (k : ℕ) :
    prefixSum (retainedPath a s) (retainedCount s k) = retainedPrefixSum a s k := by
  unfold retainedPrefixSum
  rw [← retained_filter_image, Finset.sum_image]
  · unfold prefixSum retainedPath
    apply Finset.sum_congr
    · ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (retainedIndex_lt_iff s k i).symm
    · intro i _
      rfl
  · intro i _ j _ hij
    exact (retainedIndex s).injective hij

/-- Cutting immediately before a retained observation recovers its rank. -/
theorem retainedCount_at_index (s : Finset (Fin n)) (r : Fin s.card) :
    retainedCount s (retainedIndex s r).val = r.val := by
  rw [← retained_filter_card]
  have hset :
      Finset.univ.filter
        (fun i : Fin s.card => (retainedIndex s i).val < (retainedIndex s r).val) =
      Finset.Iio r := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    exact (retainedIndex s).lt_iff_lt
  rw [hset, Fin.card_Iio]

/-- Every compressed prefix has an original cutoff, including the two endpoints. -/
theorem exists_original_cutoff (a : Path n) (s : Finset (Fin n)) (r : ℕ)
    (hr : r ≤ s.card) :
    ∃ k : ℕ, k ≤ n ∧ retainedCount s k = r ∧
      prefixSum (retainedPath a s) r = retainedPrefixSum a s k := by
  by_cases heq : r = s.card
  · subst r
    exact ⟨n, le_rfl, retainedCount_length s,
      by simpa using prefixSum_retainedPath_count a s n⟩
  · have hlt : r < s.card := lt_of_le_of_ne hr heq
    let i : Fin s.card := ⟨r, hlt⟩
    refine ⟨(retainedIndex s i).val, (retainedIndex s i).is_lt.le, ?_, ?_⟩
    · exact retainedCount_at_index s i
    · simpa only [retainedCount_at_index] using
        prefixSum_retainedPath_count a s (retainedIndex s i).val

/-- Adding zero entries in deleted locations changes no maximum including zero. -/
theorem maxWithZero_retainedPath (a : Path n) (s : Finset (Fin n)) :
    maxWithZero (retainedPath a s) = maxWithZero (zeroOutside a s) := by
  apply le_antisymm
  · apply (maxWithZero_le_iff _ _).mpr
    intro r hr
    obtain ⟨k, hk, _, hsum⟩ := exists_original_cutoff a s r hr
    rw [hsum, ← prefixSum_zeroOutside]
    exact (maxWithZero_le_iff _ _).mp le_rfl k hk
  · apply (maxWithZero_le_iff _ _).mpr
    intro k _
    rw [prefixSum_zeroOutside, ← prefixSum_retainedPath_count]
    exact (maxWithZero_le_iff _ _).mp le_rfl _ (retainedCount_le s k)

/-- At a positive threshold, the empty prefix cannot create a retained crossing. -/
theorem positive_crossing_retainedPath (a : Path n) (s : Finset (Fin n))
    (hs : 0 < s.card) (t : ℝ) (ht : 0 < t) :
    t ≤ maxWithZero (zeroOutside a s) ↔ t ≤ upperMax (retainedPath a s) hs := by
  rw [← maxWithZero_retainedPath, maxWithZero_eq _ hs, le_max_iff]
  exact or_iff_right (not_le.mpr ht)

@[simp] theorem maxWithZero_retainedPath_empty (a : Path n) :
    maxWithZero (retainedPath a ∅) = 0 := by
  apply le_antisymm
  · apply (maxWithZero_le_iff _ _).mpr
    intro k hk
    have : k = 0 := by simpa using hk
    rw [this, prefixSum_zero]
  · exact maxWithZero_nonneg _

end Shao
