import Shao.OQ5.P35.RowIdentity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Finite three-state canonical layer and two-target cancellation

Finite algebra from original p50.md §2, reused without parameter changes by
p52.md §2. This file asserts no probability law, convergence or tail result.
-/

set_option autoImplicit false

namespace Shao.OQ5.P50

noncomputable section

open scoped BigOperators

/-- Weights of states base0, target1 and compensator2. -/
def layerWeight (p q : ℝ) (a : Fin 3) : ℝ :=
  if a = 0 then 1-p-q else if a = 1 then p else q

/-- The exact symmetric three-state matrix; N is cast before real subtraction. -/
def layerKernel (N : ℕ) (t p q : ℝ) (a b : Fin 3) : ℝ :=
  if a = 0 then
    if b = 0 then 0 else if b = 1 then t else -p*t/q
  else if a = 1 then
    if b = 0 then t else if b = 1 then -((N : ℝ)-4)*t
    else -t*(1-p-q-p*((N : ℝ)-4))/q
  else
    if b = 0 then -p*t/q
    else if b = 1 then -t*(1-p-q-p*((N : ℝ)-4))/q
    else p*t*(2-2*q-p*((N : ℝ)-2))/q^2

/-- A target set is in state1, and every other sample coordinate in state0. -/
def twoTargetState {N : ℕ} (J : Finset (Fin N)) (i : Fin N) : Fin 3 :=
  if i ∈ J then 1 else 0

theorem layerKernel_symmetric (N : ℕ) (t p q : ℝ) (a b : Fin 3) :
  layerKernel N t p q a b = layerKernel N t p q b a := by
  fin_cases a <;> fin_cases b <;> simp [layerKernel]

theorem layerKernel_weighted_row_zero (N : ℕ) (t p q : ℝ) (hq : q ≠ 0) (a : Fin 3) :
  (∑ b : Fin 3, layerWeight p q b * layerKernel N t p q a b) = 0 := by
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  fin_cases a <;> simp [huniv, layerWeight, layerKernel] <;>
    field_simp [hq] <;> ring

private theorem sum_if_mem {N : ℕ} (J : Finset (Fin N)) (a b : ℝ) :
    (∑ l : Fin N, if l ∈ J then a else b) =
      (J.card : ℝ) * a + ((N : ℝ) - (J.card : ℝ)) * b := by
  classical
  have hpoint : ∀ l : Fin N,
      (if l ∈ J then a else b) = (if l ∈ J then a-b else 0) + b := by
    intro l
    split_ifs <;> ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem_eq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem twoTarget_row_sum (N : ℕ) (hn : 3 ≤ N) (t p q : ℝ)
  (J : Finset (Fin N)) (hJ : J.card = 2) (i : Fin N) :
  (∑ l ∈ Finset.univ.erase i,
    layerKernel N t p q (twoTargetState J i) (twoTargetState J l)) = 2*t := by
  classical
  have _ := hn
  rw [Finset.sum_erase_eq_sub (by simp)]
  by_cases hi : i ∈ J
  · have hrow : ∀ l : Fin N,
        layerKernel N t p q (twoTargetState J i) (twoTargetState J l) =
          if l ∈ J then -((N : ℝ)-4)*t else t := by
      intro l
      by_cases hl : l ∈ J <;> simp [twoTargetState, layerKernel, hi, hl]
    simp_rw [hrow]
    rw [sum_if_mem]
    simp only [hJ, Nat.cast_ofNat, ite_eq_left hi]
    ring
  · have hrow : ∀ l : Fin N,
        layerKernel N t p q (twoTargetState J i) (twoTargetState J l) =
          if l ∈ J then t else 0 := by
      intro l
      by_cases hl : l ∈ J <;> simp [twoTargetState, layerKernel, hi, hl]
    simp_rw [hrow]
    rw [sum_if_mem]
    simp [hJ, hi]

theorem twoTarget_pair_sum (N : ℕ) (hn : 3 ≤ N) (t p q : ℝ)
  (J : Finset (Fin N)) (hJ : J.card = 2) :
  Shao.OQ5.P35.unorderedPairSum (fun i l =>
    layerKernel N t p q (twoTargetState J i) (twoTargetState J l)) = (N : ℝ)*t := by
  have hcount := Shao.OQ5.P35.offDiagonalSum_eq_two_unordered
    (fun i l => layerKernel N t p q (twoTargetState J i) (twoTargetState J l))
    (fun i l => layerKernel_symmetric N t p q (twoTargetState J i) (twoTargetState J l))
  simp_rw [twoTarget_row_sum N hn t p q J hJ] at hcount
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hcount
  linarith

theorem twoTarget_layerU (N : ℕ) (hn : 3 ≤ N) (t p q : ℝ)
  (J : Finset (Fin N)) (hJ : J.card = 2) :
  (Shao.OQ5.P35.pairCount N)⁻¹ *
    Shao.OQ5.P35.unorderedPairSum (fun i l =>
      layerKernel N t p q (twoTargetState J i) (twoTargetState J l)) =
    2*t/((N : ℝ)-1) := by
  have hN : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
  have h0 : (N : ℝ) ≠ 0 := by linarith
  have h1 : (N : ℝ)-1 ≠ 0 := by linarith
  rw [twoTarget_pair_sum N hn t p q J hJ]
  unfold Shao.OQ5.P35.pairCount
  field_simp [h0, h1]

theorem twoTarget_centered_row_zero (N : ℕ) (hn : 3 ≤ N) (t p q : ℝ)
  (J : Finset (Fin N)) (hJ : J.card = 2) (i : Fin N) :
  Shao.OQ5.P35.center
    (fun k => ((N : ℝ)-1)⁻¹ * ∑ l ∈ Finset.univ.erase k,
      layerKernel N t p q (twoTargetState J k) (twoTargetState J l)) i = 0 := by
  have hN : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
  have h0 : (N : ℝ) ≠ 0 := by linarith
  unfold Shao.OQ5.P35.center Shao.OQ5.P35.mean
  simp_rw [twoTarget_row_sum N hn t p q J hJ]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [h0]
  ring

end

end Shao.OQ5.P50
