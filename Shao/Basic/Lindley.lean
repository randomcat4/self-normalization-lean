import Shao.Basic.FinitePath
import Mathlib.Data.Fin.Rev
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite Lindley recursion and path reversal

The state is defined by its actual reflected recursion. It is only evaluated
at a bounded original time `k ≤ n`, with no extension after the path ends.
-/

namespace Shao

open scoped BigOperators

variable {n : ℕ}

/-- The original first `k` observations, with their original order. -/
def prefixPath (a : Path n) (k : ℕ) (hk : k ≤ n) : Path k :=
  fun i => a ⟨i.val, lt_of_lt_of_le i.is_lt hk⟩

/-- The observations in reverse chronological order. -/
def reversePath (a : Path n) : Path n := fun i => a i.rev

/-- The genuine reflected recursion, starting at zero. -/
def lindleyState (a : Path n) : (k : ℕ) → k ≤ n → ℝ
  | 0, _ => 0
  | k + 1, hk => max 0 (lindleyState a k (Nat.le_of_succ_le hk) +
      a ⟨k, Nat.lt_of_succ_le hk⟩)

@[simp] theorem prefixPath_length (a : Path n) : prefixPath a n le_rfl = a := by
  funext i
  rfl

@[simp] theorem reversePath_reversePath (a : Path n) :
    reversePath (reversePath a) = a := by
  funext i
  simp [reversePath]

theorem energy_reversePath (a : Path n) : energy (reversePath a) = energy a := by
  exact Equiv.sum_comp Fin.revPerm (fun i => (a i) ^ 2)

@[simp] theorem lindleyState_zero (a : Path n) (hk : 0 ≤ n) :
    lindleyState a 0 hk = 0 := rfl

theorem lindleyState_succ (a : Path n) (k : ℕ) (hk : k + 1 ≤ n) :
    lindleyState a (k + 1) hk =
      max 0 (lindleyState a k (Nat.le_of_succ_le hk) +
        a ⟨k, Nat.lt_of_succ_le hk⟩) := rfl

private theorem maxWithZero_nil (a : Path 0) : maxWithZero a = 0 := by
  apply le_antisymm
  · apply (maxWithZero_le_iff a 0).mpr
    intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    rw [hk0, prefixSum_zero]
  · exact maxWithZero_nonneg a

private theorem prefixSum_cons (a : Path (n + 1)) (k : ℕ) :
    prefixSum a (k + 1) = a 0 + prefixSum (fun i : Fin n => a i.succ) k := by
  simp only [prefixSum, Finset.sum_filter, Fin.sum_univ_succ,
    Fin.val_zero, Fin.val_succ, Nat.zero_lt_succ, Nat.succ_lt_succ_iff, ite_true]

private theorem maxWithZero_cons (a : Path (n + 1)) :
    maxWithZero a = max 0 (a 0 + maxWithZero (fun i : Fin n => a i.succ)) := by
  apply le_antisymm
  · apply (maxWithZero_le_iff a _).mpr
    intro k hk
    cases k with
    | zero =>
      rw [prefixSum_zero]
      exact le_max_left _ _
    | succ k =>
      rw [prefixSum_cons]
      have htail : prefixSum (fun i : Fin n => a i.succ) k ≤
          maxWithZero (fun i : Fin n => a i.succ) :=
        (maxWithZero_le_iff _ _).mp le_rfl k (Nat.le_of_succ_le_succ hk)
      exact (add_le_add (le_refl (a 0)) htail).trans (le_max_right _ _)
  · apply max_le (maxWithZero_nonneg a)
    have htail : maxWithZero (fun i : Fin n => a i.succ) ≤ maxWithZero a - a 0 := by
      apply (maxWithZero_le_iff _ _).mpr
      intro k hk
      apply (le_sub_iff_add_le).mpr
      rw [add_comm, ← prefixSum_cons]
      exact (maxWithZero_le_iff a _).mp le_rfl (k + 1) (Nat.succ_le_succ hk)
    simpa only [add_comm] using (le_sub_iff_add_le.mp htail)

/-- At every original time, the state is the maximum of reversed prefix sums,
including the empty sum. -/
theorem lindleyState_eq_maxWithZero_reverse_prefix (a : Path n) (k : ℕ)
    (hk : k ≤ n) :
    lindleyState a k hk = maxWithZero (reversePath (prefixPath a k hk)) := by
  induction k with
  | zero =>
    rw [lindleyState_zero, maxWithZero_nil]
  | succ k ih =>
    rw [lindleyState_succ, ih, maxWithZero_cons]
    have hhead : reversePath (prefixPath a (k + 1) hk) 0 =
        a ⟨k, Nat.lt_of_succ_le hk⟩ := by
      simp only [reversePath, Fin.rev_zero, prefixPath, Fin.val_last]
    have htail :
        (fun i : Fin k => reversePath (prefixPath a (k + 1) hk) i.succ) =
        reversePath (prefixPath a k (Nat.le_of_succ_le hk)) := by
      funext i
      simp only [reversePath, Fin.rev_succ, prefixPath, Fin.val_castSucc]
    rw [hhead, htail, add_comm]

/-- The final state of the true recursion is the reversed path maximum. -/
theorem lindleyState_length (a : Path n) :
    lindleyState a n le_rfl = maxWithZero (reversePath a) := by
  simpa only [prefixPath_length] using
    lindleyState_eq_maxWithZero_reverse_prefix a n le_rfl

end Shao
