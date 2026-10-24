import Shao.OQ5.P35.RowIdentity

/-!
# Original-length incident-edge residual deletion

Finite deterministic identities from original p39, lines 129–151, with the
fixed original-length deletion convention of p38, line 68. The diagonal is
excluded from every row sum. No statistical normalization or tilted estimate
is asserted here.
-/

set_option autoImplicit false

namespace Shao.OQ6.ResidualDeletion

noncomputable section

open scoped BigOperators

variable {n : ℕ}

def eraseIncident (r : Fin n → Fin n → ℝ) (i : Fin n) :
    Fin n → Fin n → ℝ :=
  fun j k => if j = i ∨ k = i then 0 else r j k

def rowSum (r : Fin n → Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ k ∈ Finset.univ.erase j, r j k

theorem rowSum_eraseIncident
    (r : Fin n → Fin n → ℝ) (i j : Fin n) :
    rowSum (eraseIncident r i) j =
      if j = i then 0 else rowSum r j - r j i := by
  classical
  by_cases hji : j = i
  · subst j
    simp [rowSum, eraseIncident]
  · rw [if_neg hji]
    have hi : i ∈ (Finset.univ : Finset (Fin n)).erase j :=
      Finset.mem_erase.mpr ⟨Ne.symm hji, Finset.mem_univ i⟩
    calc
      rowSum (eraseIncident r i) j =
          ∑ k ∈ Finset.univ.erase j, if k = i then 0 else r j k := by
        simp only [rowSum, eraseIncident, hji, false_or]
      _ = ∑ k ∈ (Finset.univ.erase j).erase i,
          if k = i then 0 else r j k := by
        symm
        exact Finset.sum_erase (s := Finset.univ.erase j)
          (f := fun k => if k = i then (0 : ℝ) else r j k) (a := i) (by simp)
      _ = ∑ k ∈ (Finset.univ.erase j).erase i, r j k := by
        apply Finset.sum_congr rfl
        intro k hk
        exact if_neg (Finset.mem_erase.mp hk).1
      _ = rowSum r j - r j i := by
        rw [Finset.sum_erase_eq_sub hi]
        rfl

private theorem sum_eq_self_add_erase (f : Fin n → ℝ) (i : Fin n) :
    (∑ j : Fin n, f j) = f i + ∑ j ∈ Finset.univ.erase i, f j := by
  classical
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  ring

private theorem eraseIncident_symmetric
    (r : Fin n → Fin n → ℝ)
    (hr : ∀ j k, r j k = r k j) (i : Fin n) :
    ∀ j k, eraseIncident r i j k = eraseIncident r i k j := by
  intro j k
  by_cases hj : j = i
  · subst j
    simp [eraseIncident]
  · by_cases hk : k = i
    · subst k
      simp [eraseIncident]
    · simpa [eraseIncident, hj, hk] using hr j k

theorem unorderedPairSum_sub_eraseIncident
    (r : Fin n → Fin n → ℝ)
    (hr : ∀ j k, r j k = r k j) (i : Fin n) :
    Shao.OQ5.P35.unorderedPairSum r -
        Shao.OQ5.P35.unorderedPairSum (eraseIncident r i) =
      rowSum r i := by
  classical
  have hi : rowSum (eraseIncident r i) i = 0 := by
    simp [rowSum_eraseIncident]
  have hrows :
      (∑ j : Fin n, rowSum r j) -
          (∑ j : Fin n, rowSum (eraseIncident r i) j) =
        2 * rowSum r i := by
    calc
      (∑ j : Fin n, rowSum r j) -
          (∑ j : Fin n, rowSum (eraseIncident r i) j) =
          rowSum r i +
            ∑ j ∈ Finset.univ.erase i,
              (rowSum r j - rowSum (eraseIncident r i) j) := by
        rw [sum_eq_self_add_erase (rowSum r) i,
          sum_eq_self_add_erase (rowSum (eraseIncident r i)) i,
          hi, Finset.sum_sub_distrib]
        ring
      _ = rowSum r i + ∑ j ∈ Finset.univ.erase i, r i j := by
        apply congrArg (fun t : ℝ => rowSum r i + t)
        apply Finset.sum_congr rfl
        intro j hj
        rw [rowSum_eraseIncident r i j,
          if_neg (Finset.mem_erase.mp hj).1, hr j i]
        ring
      _ = 2 * rowSum r i := by
        unfold rowSum
        ring
  have hfull :
      (∑ j : Fin n, rowSum r j) =
        2 * Shao.OQ5.P35.unorderedPairSum r :=
    Shao.OQ5.P35.offDiagonalSum_eq_two_unordered r hr
  have hdeleted :
      (∑ j : Fin n, rowSum (eraseIncident r i) j) =
        2 * Shao.OQ5.P35.unorderedPairSum (eraseIncident r i) :=
    Shao.OQ5.P35.offDiagonalSum_eq_two_unordered
      (eraseIncident r i) (eraseIncident_symmetric r hr i)
  calc
    Shao.OQ5.P35.unorderedPairSum r -
        Shao.OQ5.P35.unorderedPairSum (eraseIncident r i) =
        (2 * Shao.OQ5.P35.unorderedPairSum r -
          2 * Shao.OQ5.P35.unorderedPairSum (eraseIncident r i)) / 2 := by ring
    _ = ((∑ j : Fin n, rowSum r j) -
        (∑ j : Fin n, rowSum (eraseIncident r i) j)) / 2 := by
      rw [hfull, hdeleted]
    _ = rowSum r i := by
      rw [hrows]
      ring

theorem rowSqSum_sub_eraseIncident
    (r : Fin n → Fin n → ℝ)
    (hr : ∀ j k, r j k = r k j) (i : Fin n) :
    (∑ j : Fin n, rowSum r j ^ 2) -
        (∑ j : Fin n, rowSum (eraseIncident r i) j ^ 2) =
      rowSum r i ^ 2 +
        ∑ j ∈ Finset.univ.erase i,
          (2 * r i j * (rowSum r j - r i j) + r i j ^ 2) := by
  classical
  have hi : rowSum (eraseIncident r i) i = 0 := by
    simp [rowSum_eraseIncident]
  calc
    (∑ j : Fin n, rowSum r j ^ 2) -
        (∑ j : Fin n, rowSum (eraseIncident r i) j ^ 2) =
        rowSum r i ^ 2 +
          ∑ j ∈ Finset.univ.erase i,
            (rowSum r j ^ 2 - rowSum (eraseIncident r i) j ^ 2) := by
      rw [sum_eq_self_add_erase (fun j => rowSum r j ^ 2) i,
        sum_eq_self_add_erase (fun j => rowSum (eraseIncident r i) j ^ 2) i,
        hi, Finset.sum_sub_distrib]
      ring
    _ = rowSum r i ^ 2 +
        ∑ j ∈ Finset.univ.erase i,
          (2 * r i j * (rowSum r j - r i j) + r i j ^ 2) := by
      apply congrArg (fun t : ℝ => rowSum r i ^ 2 + t)
      apply Finset.sum_congr rfl
      intro j hj
      rw [rowSum_eraseIncident r i j,
        if_neg (Finset.mem_erase.mp hj).1, hr j i]
      ring

end

end Shao.OQ6.ResidualDeletion
