import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite third-moment payment for the killed cosine boundary defect

Source: current/oq4/b01/proof01.md, Section 6, (R6).
This pointwise finite sum bound does not assume a probability law or prove
the boundary occupation estimate. Its uniformity in the cutoff is the input
needed before integrating and taking monotone limits in the R3 argument.
-/

set_option autoImplicit false

namespace Shao.OQ4

open scoped BigOperators

/-- The nonnegative unit-cell contribution to the overshoot convolution. -/
def overshootCell (u : ℝ) (j : ℕ) : ℝ :=
  ((j : ℝ) + 1) * max (u - (j : ℝ)) 0

theorem overshootCell_nonneg (u : ℝ) (j : ℕ) : 0 ≤ overshootCell u j := by
  exact mul_nonneg (by positivity) (le_max_right _ _)

/-- A finite version of R6, uniform over every cutoff, including zero. -/
theorem overshoot_sum_le_cubic (u : ℝ) (hu : 0 ≤ u) (L : ℕ) :
    (∑ j ∈ Finset.range L, overshootCell u j) ≤ 4 * (u + u ^ 3) := by
  let J : ℕ := ⌊u⌋₊ + 1
  have huJ : u < (J : ℝ) := by
    simpa only [J, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one u
  have hJu : (J : ℝ) ≤ u + 1 := by
    dsimp [J]
    push_cast
    linarith [Nat.floor_le hu]
  have hzero (j : ℕ) (hj : J ≤ j) : overshootCell u j = 0 := by
    have hjR : (J : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hj
    simp only [overshootCell, max_eq_right (by linarith : u - (j : ℝ) ≤ 0), mul_zero]
  have hcut :
      (∑ j ∈ Finset.range (min L J), overshootCell u j) =
        ∑ j ∈ Finset.range L, overshootCell u j := by
    apply Finset.sum_subset (Finset.range_mono (min_le_left L J))
    intro j hjL hjmin
    have hjL' : j < L := Finset.mem_range.mp hjL
    have hmin : min L J ≤ j := Nat.le_of_not_gt (fun h => hjmin (Finset.mem_range.mpr h))
    exact hzero j (by omega)
  rw [← hcut]
  have hcell (j : ℕ) (hj : j ∈ Finset.range (min L J)) :
      overshootCell u j ≤ (u + 1) * u := by
    have hjJ : j < J := lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_right L J)
    have hjfloor : j ≤ ⌊u⌋₊ := by dsimp [J] at hjJ; omega
    have hju : (j : ℝ) ≤ u := (Nat.cast_le.mpr hjfloor).trans (Nat.floor_le hu)
    have hleft : 0 ≤ (j : ℝ) + 1 := by positivity
    have hmax : max (u - (j : ℝ)) 0 ≤ u := by
      exact max_le (sub_le_self _ (Nat.cast_nonneg j)) hu
    exact (mul_le_mul_of_nonneg_left hmax hleft).trans
      (mul_le_mul_of_nonneg_right (by linarith : (j : ℝ) + 1 ≤ u + 1) hu)
  calc
    (∑ j ∈ Finset.range (min L J), overshootCell u j)
        ≤ ∑ _j ∈ Finset.range (min L J), (u + 1) * u :=
      Finset.sum_le_sum hcell
    _ = (min L J : ℕ) * ((u + 1) * u) := by simp
    _ ≤ (J : ℝ) * ((u + 1) * u) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (min_le_right L J))
        (mul_nonneg (by linarith) hu)
    _ ≤ (u + 1) * ((u + 1) * u) :=
      mul_le_mul_of_nonneg_right hJu (mul_nonneg (by linarith) hu)
    _ ≤ 4 * (u + u ^ 3) := by
      nlinarith [mul_nonneg hu (sq_nonneg (u - 1)), pow_nonneg hu 3]

end Shao.OQ4
