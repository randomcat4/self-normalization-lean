import Shao.Basic.OrderedSelection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Closed survival events and deletion of one coordinate

The events monitor every prefix length from zero through the path length.
Thus `S₀ = 0` is included even for an empty path. All walls are weak (`≤`),
including their endpoints. These are separate events from the complements of
the weak crossing events.

Source interfaces: OQ4 `energy01.md`, E3, and `b01/proof01.md`, Section 4.
The paths are arbitrary real finite paths; no probability assumptions occur.
-/

set_option autoImplicit false

namespace Shao

open scoped BigOperators

variable {n : ℕ}

/-- Closed two-sided strip survival, including the initial zero prefix. -/
def closedStrip (h : ℝ) : Set (Path n) :=
  {a | ∀ k : ℕ, k ≤ n → |prefixSum a k| ≤ h}

/-- Closed one-sided survival, including the initial zero prefix. -/
def closedUpper (d : ℝ) : Set (Path n) :=
  {a | ∀ k : ℕ, k ≤ n → prefixSum a k ≤ d}

/-- The zero prefix forces a nonnegative strip radius. -/
theorem nonneg_of_mem_closedStrip (a : Path n) (h : ℝ) (ha : a ∈ closedStrip h) :
    0 ≤ h := by
  simpa using ha 0 (Nat.zero_le n)

/-- The zero prefix forces a nonnegative upper wall. -/
theorem nonneg_of_mem_closedUpper (a : Path n) (d : ℝ) (ha : a ∈ closedUpper d) :
    0 ≤ d := by
  simpa using ha 0 (Nat.zero_le n)

/-- At a nonnegative radius, monitoring zero adds no condition to `absMax`. -/
theorem mem_closedStrip_iff_absMax_le (a : Path n) (hn : 0 < n) (h : ℝ)
    (hh : 0 ≤ h) : a ∈ closedStrip h ↔ absMax a hn ≤ h := by
  constructor
  · intro ha
    exact (absMax_le_iff a hn h).mpr (fun k _ hkn => ha k hkn)
  · intro hmax k hkn
    by_cases hk : k = 0
    · simpa [hk] using hh
    · exact (absMax_le_iff a hn h).mp hmax k (Nat.one_le_iff_ne_zero.mpr hk) hkn

/-- At a nonnegative wall, monitoring zero adds no condition to `upperMax`. -/
theorem mem_closedUpper_iff_upperMax_le (a : Path n) (hn : 0 < n) (d : ℝ)
    (hd : 0 ≤ d) : a ∈ closedUpper d ↔ upperMax a hn ≤ d := by
  constructor
  · intro ha
    exact (upperMax_le_iff a hn d).mpr (fun k _ hkn => ha k hkn)
  · intro hmax k hkn
    by_cases hk : k = 0
    · simpa [hk] using hd
    · exact (upperMax_le_iff a hn d).mp hmax k (Nat.one_le_iff_ne_zero.mpr hk) hkn

/-- The upper event agrees with the maximum including zero at every length. -/
theorem mem_closedUpper_iff_maxWithZero_le (a : Path n) (d : ℝ) :
    a ∈ closedUpper d ↔ maxWithZero a ≤ d := by
  exact (maxWithZero_le_iff a d).symm

/-- Consecutive prefixes differ by exactly the intervening coordinate. -/
theorem prefixSum_coordinate_step (a : Path n) (i : Fin n) :
    prefixSum a (i.val + 1) = a i + prefixSum a i.val := by
  classical
  have hset : Finset.univ.filter (fun j : Fin n => j.val < i.val + 1) =
      insert i (Finset.univ.filter (fun j : Fin n => j.val < i.val)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hj
      by_cases hji : j = i
      · exact Or.inl hji
      · apply Or.inr
        have hv : j.val ≠ i.val := by
          intro hval
          exact hji (Fin.ext hval)
        omega
    · rintro (rfl | hj)
      · omega
      · omega
  unfold prefixSum
  rw [hset, Finset.sum_insert (by simp)]

/-- Closed strip survival bounds every observation, including endpoint equality. -/
theorem abs_coordinate_le_two_mul_of_mem_closedStrip (a : Path n) (h : ℝ)
    (ha : a ∈ closedStrip h) (i : Fin n) : |a i| ≤ 2 * h := by
  have hnext := ha (i.val + 1) (Nat.succ_le_of_lt i.is_lt)
  have hprev := ha i.val i.is_lt.le
  have hstep : a i = prefixSum a (i.val + 1) - prefixSum a i.val := by
    rw [prefixSum_coordinate_step]
    ring
  rw [hstep]
  calc
    _ ≤ |prefixSum a (i.val + 1)| + |prefixSum a i.val| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le (prefixSum a (i.val + 1)) 0 (prefixSum a i.val)
    _ ≤ h + h := add_le_add hnext hprev
    _ = 2 * h := by ring

/-- The coordinate bound expressed directly through the existing absolute maximum. -/
theorem abs_coordinate_le_two_mul_of_absMax_le (a : Path n) (hn : 0 < n)
    (h : ℝ) (hh : 0 ≤ h) (ha : absMax a hn ≤ h) (i : Fin n) :
    |a i| ≤ 2 * h := by
  exact abs_coordinate_le_two_mul_of_mem_closedStrip a h
    ((mem_closedStrip_iff_absMax_le a hn h hh).mpr ha) i

/-- Deleting one observation subtracts it precisely from the later prefixes. -/
theorem prefixSum_zeroOutside_erase (a : Path n) (i : Fin n) (k : ℕ) :
    prefixSum (zeroOutside a (Finset.univ.erase i)) k =
      prefixSum a k - (if i.val < k then a i else 0) := by
  classical
  rw [prefixSum_zeroOutside]
  unfold retainedPrefixSum prefixSum
  rw [Finset.filter_erase]
  by_cases hik : i.val < k
  · have hi : i ∈ Finset.univ.filter (fun j : Fin n => j.val < k) := by
      simp [hik]
    have hsum := Finset.sum_erase_add
      (Finset.univ.filter (fun j : Fin n => j.val < k)) a hi
    rw [ite_eq_left hik]
    linarith
  · have hi : i ∉ Finset.univ.filter (fun j : Fin n => j.val < k) := by
      simp [hik]
    rw [Finset.erase_eq_of_notMem hi, ite_eq_right hik, sub_zero]

/-- Closed upper survival passes to genuine ordered deletion with the negative-part shift.

The output path may be empty, so this statement also covers a one-coordinate
input path. Every prefix, including its initial zero, remains monitored.
-/
theorem closedUpper_retainedPath_erase (a : Path n) (i : Fin n) (d : ℝ)
    (ha : a ∈ closedUpper d) :
    retainedPath a (Finset.univ.erase i) ∈ closedUpper (d + max (-(a i)) 0) := by
  intro r hr
  obtain ⟨k, hkn, _, hsum⟩ := exists_original_cutoff a (Finset.univ.erase i) r hr
  rw [hsum, ← prefixSum_zeroOutside, prefixSum_zeroOutside_erase]
  have hsrc := ha k hkn
  split_ifs
  · linarith [le_max_left (-(a i)) 0]
  · linarith [le_max_right (-(a i)) 0]

/-- The deleted maximum including zero obeys the same closed bound at every length. -/
theorem maxWithZero_retainedPath_erase_le (a : Path n) (i : Fin n) (d : ℝ)
    (ha : a ∈ closedUpper d) :
    maxWithZero (retainedPath a (Finset.univ.erase i)) ≤ d + max (-(a i)) 0 := by
  exact (mem_closedUpper_iff_maxWithZero_le _ _).mp
    (closedUpper_retainedPath_erase a i d ha)

/-- The genuinely nonempty deleted upper maximum obeys the shifted closed wall. -/
theorem upperMax_retainedPath_erase_le (a : Path n) (i : Fin n) (d : ℝ)
    (ha : a ∈ closedUpper d) (hs : 0 < (Finset.univ.erase i).card) :
    upperMax (retainedPath a (Finset.univ.erase i)) hs ≤ d + max (-(a i)) 0 := by
  apply (upperMax_le_iff _ hs _).mpr
  intro k _ hkn
  exact closedUpper_retainedPath_erase a i d ha k hkn

end Shao
