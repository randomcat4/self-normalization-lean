import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.Basic

namespace Shao.OQ3
open scoped BigOperators
noncomputable section

theorem finite_word_monomial_encoding
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (sigma : ι → κ) :
    let p : κ → ℕ := fun j => Fintype.card {i : ι // sigma i = j}
    (∑ j, p j) = Fintype.card ι ∧
      (∀ w : κ → ℕ, (∑ j, w j * p j) = ∑ i, w (sigma i)) ∧
      (∀ a : κ → ℂ, (∏ j, a j ^ p j) = ∏ i, a (sigma i)) := by
  classical
  intro p
  have hweight (w : κ → ℕ) : (∑ j, w j * p j) = ∑ i, w (sigma i) := by
    have hinner (j : κ) :
        (∑ i : {i : ι // sigma i = j}, w (sigma i)) = w j * p j := by
      calc
        _ = ∑ _i : {i : ι // sigma i = j}, w j :=
          Finset.sum_congr rfl (fun i _ => by rw [i.property])
        _ = _ := by simp [p, Nat.mul_comm]
    calc
      _ = ∑ j, ∑ i : {i : ι // sigma i = j}, w (sigma i) :=
        Finset.sum_congr rfl (fun j _ => (hinner j).symm)
      _ = _ := Fintype.sum_fiberwise sigma (fun i => w (sigma i))
  refine ⟨?_, hweight, ?_⟩
  · simpa using hweight (fun _ => 1)
  · intro a
    have hinner (j : κ) :
        (∏ i : {i : ι // sigma i = j}, a (sigma i)) = a j ^ p j := by
      calc
        _ = ∏ _i : {i : ι // sigma i = j}, a j :=
          Finset.prod_congr rfl (fun i _ => by rw [i.property])
        _ = _ := by simp [p]
    calc
      _ = ∏ j, ∏ i : {i : ι // sigma i = j}, a (sigma i) :=
        Finset.prod_congr rfl (fun j _ => (hinner j).symm)
      _ = _ := Fintype.prod_fiberwise sigma (fun i => a (sigma i))

theorem fin_six_word_physical_degree_bounds
    (q : ℕ) (hq : q ≤ 6) (sigma : Fin q → Fin 6)
    (hdegree : 7 ≤ ∑ i, ((sigma i).val + 1)) :
    9 ≤ ∑ i, ((sigma i).val + 3) ∧ (∑ i, ((sigma i).val + 3)) ≤ 48 := by
  classical
  have hqpos : 1 ≤ q := by
    by_contra h
    have hq0 : q = 0 := by omega
    subst q
    norm_num at hdegree
  have hsplit :
      (∑ i, ((sigma i).val + 3)) = (∑ i, ((sigma i).val + 1)) + 2 * q := by
    have heq (i : Fin q) : (sigma i).val + 3 = ((sigma i).val + 1) + 2 := by omega
    simp_rw [heq]
    rw [Finset.sum_add_distrib]
    simp [Nat.mul_comm]
  have hupper : (∑ i, ((sigma i).val + 3)) ≤ q * 8 := by
    calc
      _ ≤ ∑ _i : Fin q, (8 : ℕ) :=
        Finset.sum_le_sum (fun i _ => by have hi := (sigma i).isLt; omega)
      _ = _ := by simp
  constructor <;> omega

end
end Shao.OQ3
