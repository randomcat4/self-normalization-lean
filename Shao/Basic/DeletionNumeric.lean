import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The scalar inequality behind deterministic path deletion

The quantities `q` and `r` are the genuine retained and deleted square sums.
Zero square sums are allowed. No probabilistic or centering assumptions occur.
-/

set_option autoImplicit false

namespace Shao

/-- The two-term Cauchy--Schwarz bound used for deletion. -/
theorem deletion_sqrt_bound (x j q r : ℝ) (hx : 0 < x) (hj : 0 ≤ j)
    (hxx : j < x ^ 2) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    Real.sqrt (x ^ 2 - j) * Real.sqrt q + Real.sqrt j * Real.sqrt r ≤
      x * Real.sqrt (q + r) := by
  have hc : 0 ≤ x ^ 2 - j := sub_nonneg.mpr hxx.le
  have hsq :
      (Real.sqrt (x ^ 2 - j) * Real.sqrt q + Real.sqrt j * Real.sqrt r) ^ 2 ≤
        x ^ 2 * (q + r) := by
    calc
      _ = ((Real.sqrt (x ^ 2 - j)) ^ 2 + (Real.sqrt j) ^ 2) *
            ((Real.sqrt q) ^ 2 + (Real.sqrt r) ^ 2) -
          (Real.sqrt (x ^ 2 - j) * Real.sqrt r - Real.sqrt j * Real.sqrt q) ^ 2 := by
        ring
      _ ≤ ((Real.sqrt (x ^ 2 - j)) ^ 2 + (Real.sqrt j) ^ 2) *
            ((Real.sqrt q) ^ 2 + (Real.sqrt r) ^ 2) :=
        sub_le_self _ (sq_nonneg _)
      _ = x ^ 2 * (q + r) := by
        rw [Real.sq_sqrt hc, Real.sq_sqrt hj, Real.sq_sqrt hq, Real.sq_sqrt hr]
        ring
  have hroot := Real.le_sqrt_of_sq_le hsq
  rw [Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx.le] at hroot
  exact hroot

/-- Removing a sum controlled by the deleted energy preserves the new threshold. -/
theorem deletion_numeric (x j q r s d : ℝ) (hx : 0 < x) (hj : 0 ≤ j)
    (hxx : j < x ^ 2) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hd : d ≤ Real.sqrt j * Real.sqrt r)
    (hcross : x * Real.sqrt (q + r) ≤ s + d) :
    Real.sqrt (x ^ 2 - j) * Real.sqrt q ≤ s := by
  have hbound := deletion_sqrt_bound x j q r hx hj hxx hq hr
  linarith

end Shao
