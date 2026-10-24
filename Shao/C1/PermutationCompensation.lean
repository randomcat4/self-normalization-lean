import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section
namespace Shao.C1.PermutationCompensation
open scoped BigOperators

theorem remaining_sum (n : ℕ) (a : Fin n → ℝ)
    (r : Fin n) (σ : Equiv.Perm (Fin n)) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => r.val ≤ i.val), a (σ i)) =
      (∑ i : Fin n, a i) -
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < r.val), a (σ i) := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : Fin n => i.val < r.val) (fun i => a (σ i))
  simp only [not_lt] at hsplit
  have htotal : (∑ i : Fin n, a (σ i)) = ∑ i : Fin n, a i :=
    Equiv.sum_comp σ a
  linarith only [hsplit, htotal]

theorem remaining_square_sum (n : ℕ) (a : Fin n → ℝ)
    (r : Fin n) (σ : Equiv.Perm (Fin n)) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => r.val ≤ i.val), (a (σ i)) ^ 2) =
      (∑ i : Fin n, (a i) ^ 2) -
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < r.val), (a (σ i)) ^ 2 := by
  exact remaining_sum n (fun i => (a i) ^ 2) r σ

theorem conditional_uniform_compensation
    (n : ℕ) (a : Fin n → ℝ) (r : Fin n)
    (H : ℝ) (hH : 0 < H) (w : Equiv.Perm (Fin n) → ℝ)
    (hw : ∀ σ τ : Equiv.Perm (Fin n),
      (∀ i : Fin n, i.val < r.val → σ i = τ i) → w σ = w τ) :
    let d : Equiv.Perm (Fin n) → ℝ := fun σ =>
      (∑ i : Fin n, a i) -
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < r.val), a (σ i)
    let T : Equiv.Perm (Fin n) → ℝ := fun σ =>
      (∑ i : Fin n, (a i) ^ 2) -
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < r.val), (a (σ i)) ^ 2
    (∑ σ : Equiv.Perm (Fin n),
      w σ * (if H ≤ T σ then a (σ r) - (a (σ r)) ^ 2 * d σ / T σ else 0)) = 0 := by
  classical
  intro d T
  let U : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => r.val ≤ i.val)
  let F : Equiv.Perm (Fin n) → Fin n → ℝ := fun σ j =>
    w σ * (if H ≤ T σ then a (σ j) - (a (σ j)) ^ 2 * d σ / T σ else 0)
  have hd (σ : Equiv.Perm (Fin n)) : (∑ j ∈ U, a (σ j)) = d σ :=
    remaining_sum n a r σ
  have hT (σ : Equiv.Perm (Fin n)) : (∑ j ∈ U, (a (σ j)) ^ 2) = T σ :=
    remaining_square_sum n a r σ
  have hswap (j : Fin n) (hj : j ∈ U) (σ : Equiv.Perm (Fin n)) :
      F (σ * Equiv.swap r j) r = F σ j := by
    have hrj : r.val ≤ j.val := (Finset.mem_filter.mp hj).2
    have hprefix : ∀ i : Fin n, i.val < r.val →
        (σ * Equiv.swap r j) i = σ i := by
      intro i hi
      have hir : i ≠ r := by intro he; subst i; omega
      have hij : i ≠ j := by intro he; subst i; omega
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hir hij]
    have hw' : w (σ * Equiv.swap r j) = w σ := hw _ _ hprefix
    have hd' : d (σ * Equiv.swap r j) = d σ := by
      dsimp only [d]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hprefix i (Finset.mem_filter.mp hi).2]
    have hT' : T (σ * Equiv.swap r j) = T σ := by
      dsimp only [T]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hprefix i (Finset.mem_filter.mp hi).2]
    dsimp only [F]
    rw [hw', hd', hT']
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  have hsum (j : Fin n) (hj : j ∈ U) :
      (∑ σ : Equiv.Perm (Fin n), F σ r) = ∑ σ : Equiv.Perm (Fin n), F σ j := by
    calc
      (∑ σ : Equiv.Perm (Fin n), F σ r) =
          ∑ σ : Equiv.Perm (Fin n), F (σ * Equiv.swap r j) r :=
        (Equiv.sum_comp (Equiv.mulRight (Equiv.swap r j)) (fun σ => F σ r)).symm
      _ = ∑ σ : Equiv.Perm (Fin n), F σ j :=
        Finset.sum_congr rfl (fun σ _ => hswap j hj σ)
  have hinner (σ : Equiv.Perm (Fin n)) : (∑ j ∈ U, F σ j) = 0 := by
    by_cases hselect : H ≤ T σ
    · have hTne : T σ ≠ 0 := ne_of_gt (hH.trans_le hselect)
      calc
        (∑ j ∈ U, F σ j) = w σ * (d σ - T σ * d σ / T σ) := by
          simp only [F, if_pos hselect, ← Finset.mul_sum, Finset.sum_sub_distrib,
            div_eq_mul_inv, ← Finset.sum_mul, hd σ, hT σ]
        _ = 0 := by rw [mul_div_cancel_left₀ _ hTne, sub_self, mul_zero]
    · simp [F, hselect]
  have hcard : (U.card : ℝ) * (∑ σ : Equiv.Perm (Fin n), F σ r) = 0 := by
    calc
      (U.card : ℝ) * (∑ σ : Equiv.Perm (Fin n), F σ r) =
          ∑ j ∈ U, (∑ σ : Equiv.Perm (Fin n), F σ r) := by simp
      _ = ∑ j ∈ U, (∑ σ : Equiv.Perm (Fin n), F σ j) :=
        Finset.sum_congr rfl (fun j hj => hsum j hj)
      _ = ∑ σ : Equiv.Perm (Fin n), (∑ j ∈ U, F σ j) := Finset.sum_comm
      _ = 0 := by simp only [hinner, Finset.sum_const_zero]
  have hU : U.Nonempty := ⟨r, by simp [U]⟩
  have hUp : (0 : ℝ) < U.card := Nat.cast_pos.mpr hU.card_pos
  exact (mul_eq_zero.mp hcard).resolve_left (ne_of_gt hUp)

end Shao.C1.PermutationCompensation
