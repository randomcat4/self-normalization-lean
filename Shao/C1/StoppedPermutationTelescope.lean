import Shao.C1.PermutationCompensation
import Mathlib.Data.Finset.Fin
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
noncomputable section
namespace Shao.C1.PermutationCompensation
open scoped BigOperators

private theorem finite_stopped_sum
    (n m : ℕ) (hm : m ≤ n) (v : ℕ → ℝ) :
    (∑ i : Fin n, if i.val < m then v (i.val + 1) - v i.val else 0) = v m - v 0 := by
  classical
  induction n generalizing m with
  | zero =>
    have hm0 : m = 0 := by omega
    subst m
    simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    by_cases hmn : m ≤ n
    · rw [ih m hmn]
      simp only [show ¬n < m by omega, ite_false, add_zero]
    · have hmeq : m = n + 1 := by omega
      subst m
      have hhead :
          (∑ i : Fin n, if i.val < n + 1 then v (i.val + 1) - v i.val else 0) =
            v n - v 0 := by
        simpa only [Fin.is_lt, ite_true, show ∀ i : Fin n, i.val < n + 1 from
          fun i => i.is_lt.trans_le (Nat.le_succ n)] using ih n le_rfl
      rw [hhead, if_pos (Nat.lt_succ_self n)]
      ring

theorem finite_stopped_compensation
    (n : ℕ) (a : Fin n → ℝ)
    (ν : Equiv.Perm (Fin n) → ℕ) (hν : ∀ σ, ν σ ≤ n)
    (hνobs : ∀ (r : Fin n) (σ τ : Equiv.Perm (Fin n)),
      (∀ i : Fin n, i.val < r.val → σ i = τ i) →
        (r.val < ν σ ↔ r.val < ν τ))
    (W : Equiv.Perm (Fin n) → Fin n → ℝ)
    (hW : ∀ (r : Fin n) (σ τ : Equiv.Perm (Fin n)),
      (∀ i : Fin n, i.val < r.val → σ i = τ i) → W σ r = W τ r)
    (H : ℝ) (hH : 0 < H)
    (hcutoff : ∀ (σ : Equiv.Perm (Fin n)) (r : Fin n), r.val < ν σ →
      H ≤ (∑ i : Fin n, (a i) ^ 2) -
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < r.val), (a (σ i)) ^ 2) :
    let d : Equiv.Perm (Fin n) → Fin n → ℝ := fun σ r =>
      (∑ i : Fin n, a i) -
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < r.val), a (σ i)
    let T : Equiv.Perm (Fin n) → Fin n → ℝ := fun σ r =>
      (∑ i : Fin n, (a i) ^ 2) -
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < r.val), (a (σ i)) ^ 2
    ∀ V : Equiv.Perm (Fin n) → ℕ → ℝ,
      (∑ σ : Equiv.Perm (Fin n), (V σ (ν σ) - V σ 0)) =
        ∑ σ : Equiv.Perm (Fin n), ∑ r : Fin n,
          if r.val < ν σ then
            V σ (r.val + 1) - V σ r.val -
              W σ r * (a (σ r) - (a (σ r)) ^ 2 * d σ r / T σ r)
          else 0 := by
  classical
  intro d T V
  have hstep (r : Fin n) :
      (∑ σ : Equiv.Perm (Fin n),
        if r.val < ν σ then
          W σ r * (a (σ r) - (a (σ r)) ^ 2 * d σ r / T σ r)
        else 0) = 0 := by
    let wr : Equiv.Perm (Fin n) → ℝ := fun σ => if r.val < ν σ then W σ r else 0
    have hwr : ∀ σ τ : Equiv.Perm (Fin n),
        (∀ i : Fin n, i.val < r.val → σ i = τ i) → wr σ = wr τ := by
      intro σ τ hprefix
      dsimp only [wr]
      simp only [hνobs r σ τ hprefix, hW r σ τ hprefix]
    have hc := conditional_uniform_compensation n a r H hH wr hwr
    change (∑ σ : Equiv.Perm (Fin n), wr σ *
      (if H ≤ T σ r then a (σ r) - (a (σ r)) ^ 2 * d σ r / T σ r else 0)) = 0 at hc
    calc
      _ = ∑ σ : Equiv.Perm (Fin n), wr σ *
          (if H ≤ T σ r then a (σ r) - (a (σ r)) ^ 2 * d σ r / T σ r else 0) := by
        apply Finset.sum_congr rfl
        intro σ _
        dsimp only [wr]
        by_cases hs : r.val < ν σ
        · have hguard : H ≤ T σ r := hcutoff σ r hs
          simp only [if_pos hs, if_pos hguard]
        · simp only [if_neg hs, zero_mul]
      _ = 0 := hc
  have htel (σ : Equiv.Perm (Fin n)) :
      (∑ r : Fin n, if r.val < ν σ then V σ (r.val + 1) - V σ r.val else 0) =
        V σ (ν σ) - V σ 0 := finite_stopped_sum n (ν σ) (hν σ) (V σ)
  symm
  calc
    _ = ∑ σ : Equiv.Perm (Fin n),
        ((∑ r : Fin n, if r.val < ν σ then V σ (r.val + 1) - V σ r.val else 0) -
          ∑ r : Fin n, if r.val < ν σ then
            W σ r * (a (σ r) - (a (σ r)) ^ 2 * d σ r / T σ r) else 0) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r _
      by_cases hs : r.val < ν σ <;> simp only [hs, ite_true, ite_false, sub_zero, sub_self]
    _ = (∑ σ : Equiv.Perm (Fin n), (V σ (ν σ) - V σ 0)) -
        ∑ σ : Equiv.Perm (Fin n), ∑ r : Fin n,
          if r.val < ν σ then
            W σ r * (a (σ r) - (a (σ r)) ^ 2 * d σ r / T σ r) else 0 := by
      simp_rw [htel]
      rw [Finset.sum_sub_distrib]
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [hstep, Finset.sum_const_zero, sub_zero]

end Shao.C1.PermutationCompensation
