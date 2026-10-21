import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Finite real paths and their genuine energy

One-sided maxima exclude the empty prefix. The maximum including that prefix
is a separate object. No independence or centering assumption is imposed here.
-/

namespace Shao

open scoped BigOperators

abbrev Path (n : ℕ) := Fin n → ℝ

variable {n : ℕ}

/-- Sum of the first k coordinates, saturated at the path length. -/
def prefixSum (a : Path n) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), a i

/-- Actual squared coordinates in the first k positions. -/
def prefixSquares (a : Path n) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), (a i) ^ 2

/-- Genuine final energy, without centering or replacement by variance. -/
def energy (a : Path n) : ℝ := ∑ i, (a i) ^ 2

@[simp] theorem prefixSum_zero (a : Path n) : prefixSum a 0 = 0 := by
  simp [prefixSum]

@[simp] theorem prefixSquares_zero (a : Path n) : prefixSquares a 0 = 0 := by
  simp [prefixSquares]

@[simp] theorem prefixSum_length (a : Path n) : prefixSum a n = ∑ i, a i := by
  unfold prefixSum
  rw [Finset.filter_eq_self.mpr (fun i _ => i.is_lt)]

@[simp] theorem prefixSquares_length (a : Path n) : prefixSquares a n = energy a := by
  unfold prefixSquares energy
  rw [Finset.filter_eq_self.mpr (fun i _ => i.is_lt)]

theorem prefixSquares_nonneg (a : Path n) (k : ℕ) : 0 ≤ prefixSquares a k := by
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem energy_nonneg (a : Path n) : 0 ≤ energy a := by
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem energy_eq_zero_iff (a : Path n) : energy a = 0 ↔ ∀ i, a i = 0 := by
  constructor
  · intro h i
    have hi : (a i) ^ 2 ≤ energy a :=
      Finset.single_le_sum (fun j _ => sq_nonneg (a j)) (Finset.mem_univ i)
    have hs : (a i) ^ 2 = 0 := le_antisymm (h ▸ hi) (sq_nonneg _)
    exact sq_eq_zero_iff.mp hs
  · intro h
    simp [energy, h]

@[simp] theorem prefixSum_neg (a : Path n) (k : ℕ) :
    prefixSum (-a) k = -prefixSum a k := by
  simp [prefixSum]

@[simp] theorem prefixSquares_neg (a : Path n) (k : ℕ) :
    prefixSquares (-a) k = prefixSquares a k := by
  simp [prefixSquares]

@[simp] theorem energy_neg (a : Path n) : energy (-a) = energy a := by
  simp [energy]

@[simp] theorem prefixSum_smul (c : ℝ) (a : Path n) (k : ℕ) :
    prefixSum (c • a) k = c * prefixSum a k := by
  simp [prefixSum, Finset.mul_sum, smul_eq_mul]

@[simp] theorem prefixSquares_smul (c : ℝ) (a : Path n) (k : ℕ) :
    prefixSquares (c • a) k = c ^ 2 * prefixSquares a k := by
  simp [prefixSquares, mul_pow, Finset.mul_sum, smul_eq_mul]

@[simp] theorem energy_smul (c : ℝ) (a : Path n) :
    energy (c • a) = c ^ 2 * energy a := by
  simp [energy, mul_pow, Finset.mul_sum, smul_eq_mul]

theorem prefixSum_eq_zero_of_energy_eq_zero (a : Path n)
    (h : energy a = 0) (k : ℕ) : prefixSum a k = 0 := by
  simp [prefixSum, (energy_eq_zero_iff a).mp h]

private theorem positivePrefixes_nonempty (hn : 0 < n) : (Finset.Icc 1 n).Nonempty :=
  ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hn⟩⟩

private theorem allPrefixes_nonempty (n : ℕ) : (Finset.Icc 0 n).Nonempty :=
  ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le n⟩⟩

/-- Upper maximum over prefix lengths 1 through n; excludes the empty prefix. -/
noncomputable def upperMax (a : Path n) (hn : 0 < n) : ℝ :=
  (Finset.Icc 1 n).sup' (positivePrefixes_nonempty hn) (prefixSum a)

/-- Upper maximum with the empty prefix included. -/
noncomputable def maxWithZero (a : Path n) : ℝ :=
  (Finset.Icc 0 n).sup' (allPrefixes_nonempty n) (prefixSum a)

noncomputable def lowerMax (a : Path n) (hn : 0 < n) : ℝ := upperMax (-a) hn

noncomputable def absMax (a : Path n) (hn : 0 < n) : ℝ :=
  max (upperMax a hn) (lowerMax a hn)

theorem upperMax_le_iff (a : Path n) (hn : 0 < n) (b : ℝ) :
    upperMax a hn ≤ b ↔ ∀ k : ℕ, 1 ≤ k → k ≤ n → prefixSum a k ≤ b := by
  unfold upperMax
  rw [Finset.sup'_le_iff]
  simp only [Finset.mem_Icc, and_imp]

theorem upperMax_ge_iff (a : Path n) (hn : 0 < n) (b : ℝ) :
    b ≤ upperMax a hn ↔ ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ b ≤ prefixSum a k := by
  unfold upperMax
  rw [Finset.le_sup'_iff]
  simp only [Finset.mem_Icc]
  exact ⟨fun ⟨k, hk, hb⟩ => ⟨k, hk.1, hk.2, hb⟩,
    fun ⟨k, hk, hkn, hb⟩ => ⟨k, ⟨hk, hkn⟩, hb⟩⟩

theorem le_upperMax (a : Path n) (hn : 0 < n) (k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ n) : prefixSum a k ≤ upperMax a hn := by
  exact (upperMax_ge_iff a hn _).mpr ⟨k, hk, hkn, le_rfl⟩

theorem upperMax_attained (a : Path n) (hn : 0 < n) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ upperMax a hn = prefixSum a k := by
  obtain ⟨k, hk, hkn, h⟩ := (upperMax_ge_iff a hn _).mp le_rfl
  exact ⟨k, hk, hkn, le_antisymm h (le_upperMax a hn k hk hkn)⟩

theorem maxWithZero_le_iff (a : Path n) (b : ℝ) :
    maxWithZero a ≤ b ↔ ∀ k : ℕ, k ≤ n → prefixSum a k ≤ b := by
  unfold maxWithZero
  rw [Finset.sup'_le_iff]
  simp only [Finset.mem_Icc, Nat.zero_le, true_and]

theorem maxWithZero_nonneg (a : Path n) : 0 ≤ maxWithZero a := by
  have h := (maxWithZero_le_iff a (maxWithZero a)).mp le_rfl 0 (Nat.zero_le n)
  simpa using h

theorem maxWithZero_eq (a : Path n) (hn : 0 < n) :
    maxWithZero a = max 0 (upperMax a hn) := by
  apply le_antisymm
  · apply (maxWithZero_le_iff a _).mpr
    intro k hkn
    by_cases hk : k = 0
    · simp [hk]
    · exact (le_upperMax a hn k (Nat.one_le_iff_ne_zero.mpr hk) hkn).trans
        (le_max_right _ _)
  · apply max_le (maxWithZero_nonneg a)
    apply (upperMax_le_iff a hn _).mpr
    intro k _ hkn
    exact (maxWithZero_le_iff a _).mp le_rfl k hkn

@[simp] theorem upperMax_neg (a : Path n) (hn : 0 < n) :
    upperMax (-a) hn = lowerMax a hn := rfl

@[simp] theorem lowerMax_neg (a : Path n) (hn : 0 < n) :
    lowerMax (-a) hn = upperMax a hn := by
  simp only [lowerMax, neg_neg]

@[simp] theorem absMax_neg (a : Path n) (hn : 0 < n) :
    absMax (-a) hn = absMax a hn := by
  simp only [absMax, upperMax_neg, lowerMax_neg, max_comm]

theorem upperMax_eq_zero_of_energy_eq_zero (a : Path n) (hn : 0 < n)
    (h : energy a = 0) : upperMax a hn = 0 := by
  apply le_antisymm
  · exact (upperMax_le_iff a hn 0).mpr
      (fun k _ _ => (prefixSum_eq_zero_of_energy_eq_zero a h k).le)
  · exact (upperMax_ge_iff a hn 0).mpr
      ⟨1, le_rfl, hn, (prefixSum_eq_zero_of_energy_eq_zero a h 1).ge⟩

theorem lowerMax_eq_zero_of_energy_eq_zero (a : Path n) (hn : 0 < n)
    (h : energy a = 0) : lowerMax a hn = 0 := by
  exact upperMax_eq_zero_of_energy_eq_zero (-a) hn (by simpa using h)

theorem absMax_eq_zero_of_energy_eq_zero (a : Path n) (hn : 0 < n)
    (h : energy a = 0) : absMax a hn = 0 := by
  simp [absMax, upperMax_eq_zero_of_energy_eq_zero a hn h,
    lowerMax_eq_zero_of_energy_eq_zero a hn h]

theorem upperMax_smul_of_nonneg (c : ℝ) (hc : 0 ≤ c) (a : Path n) (hn : 0 < n) :
    upperMax (c • a) hn = c * upperMax a hn := by
  apply le_antisymm
  · apply (upperMax_le_iff (c • a) hn _).mpr
    intro k hk hkn
    rw [prefixSum_smul]
    exact mul_le_mul_of_nonneg_left (le_upperMax a hn k hk hkn) hc
  · obtain ⟨k, hk, hkn, heq⟩ := upperMax_attained a hn
    apply (upperMax_ge_iff (c • a) hn _).mpr
    exact ⟨k, hk, hkn, by rw [prefixSum_smul, heq]⟩

theorem lowerMax_smul_of_nonneg (c : ℝ) (hc : 0 ≤ c) (a : Path n) (hn : 0 < n) :
    lowerMax (c • a) hn = c * lowerMax a hn := by
  unfold lowerMax
  have hneg : -(c • a) = c • (-a) := by
    funext i
    simp [smul_eq_mul]
  rw [hneg, upperMax_smul_of_nonneg c hc]

theorem absMax_smul_of_nonneg (c : ℝ) (hc : 0 ≤ c) (a : Path n) (hn : 0 < n) :
    absMax (c • a) hn = c * absMax a hn := by
  simp only [absMax, upperMax_smul_of_nonneg c hc, lowerMax_smul_of_nonneg c hc]
  exact (mul_max_of_nonneg _ _ hc).symm

@[simp] theorem prefixSum_one (a : Path 1) : prefixSum a 1 = a 0 := by
  simp [prefixSum_length]

@[simp] theorem energy_one (a : Path 1) : energy a = (a 0) ^ 2 := by
  simp [energy]

@[simp] theorem upperMax_one (a : Path 1) : upperMax a (by decide) = a 0 := by
  simp [upperMax]


/-- The named absolute maximum is exactly the upper bound of all absolute prefixes. -/
theorem absMax_le_iff (a : Path n) (hn : 0 < n) (b : ℝ) :
    absMax a hn ≤ b ↔ ∀ k : ℕ, 1 ≤ k → k ≤ n → |prefixSum a k| ≤ b := by
  simp only [absMax, lowerMax, max_le_iff, upperMax_le_iff, prefixSum_neg]
  constructor
  · rintro ⟨hp, hm⟩ k hk hkn
    exact abs_le.mpr ⟨neg_le.mp (hm k hk hkn), hp k hk hkn⟩
  · intro h
    exact ⟨fun k hk hkn => (abs_le.mp (h k hk hkn)).2,
      fun k hk hkn => neg_le.mpr (abs_le.mp (h k hk hkn)).1⟩

/-- Crossing the absolute maximum has a nonempty prefix witness. -/
theorem absMax_ge_iff (a : Path n) (hn : 0 < n) (b : ℝ) :
    b ≤ absMax a hn ↔ ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ b ≤ |prefixSum a k| := by
  simp only [absMax, lowerMax, le_max_iff, upperMax_ge_iff, prefixSum_neg]
  constructor
  · rintro (⟨k, hk, hkn, h⟩ | ⟨k, hk, hkn, h⟩)
    · exact ⟨k, hk, hkn, h.trans (le_abs_self _)⟩
    · exact ⟨k, hk, hkn, h.trans (neg_le_abs _)⟩
  · rintro ⟨k, hk, hkn, h⟩
    rcases le_abs.mp h with hp | hm
    · exact Or.inl ⟨k, hk, hkn, hp⟩
    · exact Or.inr ⟨k, hk, hkn, hm⟩

theorem absMax_nonneg (a : Path n) (hn : 0 < n) : 0 ≤ absMax a hn := by
  exact (absMax_ge_iff a hn 0).mpr ⟨1, le_rfl, hn, abs_nonneg _⟩

theorem le_absMax (a : Path n) (hn : 0 < n) (k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ n) : |prefixSum a k| ≤ absMax a hn := by
  exact (absMax_ge_iff a hn _).mpr ⟨k, hk, hkn, le_rfl⟩

theorem absMax_attained (a : Path n) (hn : 0 < n) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ absMax a hn = |prefixSum a k| := by
  obtain ⟨k, hk, hkn, h⟩ := (absMax_ge_iff a hn _).mp le_rfl
  exact ⟨k, hk, hkn, le_antisymm h (le_absMax a hn k hk hkn)⟩

end Shao
