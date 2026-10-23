import Shao.OQ3.ParabolaFiniteGridCover
import Mathlib.Data.Set.Card

namespace Shao.OQ3
noncomputable section

theorem real_ioc_grid_interval_cardinality_bound
    (n : ℕ) (hn : 1 ≤ n) (lo hi : ℝ) (hle : lo ≤ hi) :
    ((Finset.Icc (Int.ceil ((n : ℝ) * lo) - 1)
      (Int.ceil ((n : ℝ) * hi) - 1)).card : ℝ) ≤
        (hi - lo + 2) * (n : ℝ) := by
  have hN : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hceil := Int.ceil_mono (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg n))
  have hord : Int.ceil ((n : ℝ) * lo) - 1 ≤
      (Int.ceil ((n : ℝ) * hi) - 1) + 1 := by omega
  have hcount := Int.card_Icc_of_le _ _ hord
  have hcast := congrArg (fun z : ℤ => (z : ℝ)) hcount
  have hrealcount :
      ((Finset.Icc (Int.ceil ((n : ℝ) * lo) - 1)
        (Int.ceil ((n : ℝ) * hi) - 1)).card : ℝ) =
      (Int.ceil ((n : ℝ) * hi) : ℝ) - (Int.ceil ((n : ℝ) * lo) : ℝ) + 1 := by
    push_cast at hcast
    linarith
  rw [hrealcount]
  nlinarith [Int.le_ceil ((n : ℝ) * lo), Int.ceil_lt_add_one ((n : ℝ) * hi)]

theorem actual_parabola_active_grid_cardinality_bound
    (n : ℕ) (hn : 1 ≤ n) (level a0 rho : ℝ) (hrho : 0 ≤ rho) :
    let V : Set (ℝ × ℝ) := {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
    let cell : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k =>
      (Set.Ioc ((k.1 : ℝ) / (n : ℝ)) (((k.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
        Set.Ioc ((k.2 : ℝ) / (n : ℝ)) (((k.2 : ℝ) + 1) / (n : ℝ))) ∩ V
    let C : ℝ := (2 * rho + 2) * ((|a0| + rho) ^ 2 / level ^ 2 + rho + 2)
    0 < C ∧ {k : ℤ × ℤ | (cell k).Nonempty}.Finite ∧
      ({k : ℤ × ℤ | (cell k).Nonempty}.ncard : ℝ) ≤ C * (n : ℝ) ^ 2 := by
  let V : Set (ℝ × ℝ) := {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
    0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
  let cell : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k =>
    (Set.Ioc ((k.1 : ℝ) / (n : ℝ)) (((k.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
      Set.Ioc ((k.2 : ℝ) / (n : ℝ)) (((k.2 : ℝ) + 1) / (n : ℝ))) ∩ V
  let C : ℝ := (2 * rho + 2) * ((|a0| + rho) ^ 2 / level ^ 2 + rho + 2)
  let R : ℝ := (|a0| + rho) ^ 2 / level ^ 2
  let K : Set (ℤ × ℤ) := Set.Icc
    (Int.ceil ((n : ℝ) * (a0 - rho)) - 1, Int.ceil ((n : ℝ) * (-rho)) - 1)
    (Int.ceil ((n : ℝ) * (a0 + rho)) - 1, Int.ceil ((n : ℝ) * R) - 1)
  let F : Finset (ℤ × ℤ) := Finset.Icc
    (Int.ceil ((n : ℝ) * (a0 - rho)) - 1, Int.ceil ((n : ℝ) * (-rho)) - 1)
    (Int.ceil ((n : ℝ) * (a0 + rho)) - 1, Int.ceil ((n : ℝ) * R) - 1)
  change 0 < C ∧ {k : ℤ × ℤ | (cell k).Nonempty}.Finite ∧
    ({k : ℤ × ℤ | (cell k).Nonempty}.ncard : ℝ) ≤ C * (n : ℝ) ^ 2
  have hR : 0 ≤ R := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hC : 0 < C := by
    change 0 < (2 * rho + 2) * (R + rho + 2)
    exact mul_pos (by linarith) (by linarith)
  have hcover := actual_parabola_finite_half_open_grid_cover n hn level a0 rho hrho
  have hKfinite : K.Finite := hcover.1
  have hsub : {k : ℤ × ℤ | (cell k).Nonempty} ⊆ K := hcover.2.1
  have hFK : (F : Set (ℤ × ℤ)) = K := by
    ext k
    simp only [F, K, Finset.mem_coe, Finset.mem_Icc, Set.mem_Icc]
  have hKcard : K.ncard = F.card := by rw [← hFK, Set.ncard_coe_finset]
  have hprod : F.card =
      (Finset.Icc (Int.ceil ((n : ℝ) * (a0 - rho)) - 1)
        (Int.ceil ((n : ℝ) * (a0 + rho)) - 1)).card *
      (Finset.Icc (Int.ceil ((n : ℝ) * (-rho)) - 1)
        (Int.ceil ((n : ℝ) * R) - 1)).card :=
    Finset.card_Icc_prod _ _
  have ha := real_ioc_grid_interval_cardinality_bound n hn
    (a0 - rho) (a0 + rho) (by linarith)
  have hq := real_ioc_grid_interval_cardinality_bound n hn (-rho) R (by linarith)
  have hpositive : 0 ≤ ((a0 + rho) - (a0 - rho) + 2) * (n : ℝ) :=
    mul_nonneg (by linarith) (Nat.cast_nonneg n)
  have hFbound : (F.card : ℝ) ≤ C * (n : ℝ) ^ 2 := by
    calc
      (F.card : ℝ) =
          ((Finset.Icc (Int.ceil ((n : ℝ) * (a0 - rho)) - 1)
            (Int.ceil ((n : ℝ) * (a0 + rho)) - 1)).card : ℝ) *
          ((Finset.Icc (Int.ceil ((n : ℝ) * (-rho)) - 1)
            (Int.ceil ((n : ℝ) * R) - 1)).card : ℝ) := by rw [hprod, Nat.cast_mul]
      _ ≤ (((a0 + rho) - (a0 - rho) + 2) * (n : ℝ)) *
          ((R - (-rho) + 2) * (n : ℝ)) :=
        mul_le_mul ha hq (Nat.cast_nonneg _) hpositive
      _ = C * (n : ℝ) ^ 2 := by dsimp only [C, R]; ring
  refine ⟨hC, hKfinite.subset hsub, ?_⟩
  calc
    ({k : ℤ × ℤ | (cell k).Nonempty}.ncard : ℝ) ≤ (K.ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hsub hKfinite
    _ = (F.card : ℝ) := by rw [hKcard]
    _ ≤ C * (n : ℝ) ^ 2 := hFbound

end
end Shao.OQ3
