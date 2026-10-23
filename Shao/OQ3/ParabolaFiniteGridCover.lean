import Shao.OQ3.ParabolaHalfOpenGridPartition
import Mathlib.Data.Int.Interval

namespace Shao.OQ3
noncomputable section

theorem actual_parabola_window_bounded_box
    (level a0 rho : ℝ) (hrho : 0 ≤ rho) :
    let V : Set (ℝ × ℝ) := {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
    V ⊆ Set.Icc (a0 - rho) (a0 + rho) ×ˢ
      Set.Icc (-rho) ((|a0| + rho) ^ 2 / level ^ 2) := by
  change {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
    0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho} ⊆
    Set.Icc (a0 - rho) (a0 + rho) ×ˢ
      Set.Icc (-rho) ((|a0| + rho) ^ 2 / level ^ 2)
  intro w hw
  have ha := abs_le.mp hw.1
  have hM : 0 ≤ |a0| + rho := add_nonneg (abs_nonneg a0) hrho
  have habs : |w.1| ≤ |a0| + rho := by
    calc
      |w.1| = |(w.1 - a0) + a0| := by congr 1; ring
      _ ≤ |w.1 - a0| + |a0| := abs_add_le _ _
      _ ≤ |a0| + rho := by linarith [hw.1]
  have hsq : w.1 ^ 2 ≤ (|a0| + rho) ^ 2 := by
    apply sq_le_sq.mpr
    simpa only [abs_of_nonneg hM] using habs
  have hdiv := div_le_div_of_nonneg_right hsq (sq_nonneg level)
  have hdiv0 : 0 ≤ w.1 ^ 2 / level ^ 2 :=
    div_nonneg (sq_nonneg w.1) (sq_nonneg level)
  exact ⟨⟨by linarith [ha.1], by linarith [ha.2]⟩,
    ⟨by linarith [hw.2.2], by linarith [hw.2.1]⟩⟩

theorem actual_parabola_window_isCompact
    (level a0 rho : ℝ) (hrho : 0 ≤ rho) :
    IsCompact {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho} := by
  let g : (ℝ × ℝ) → ℝ := fun w => w.1 ^ 2 / level ^ 2 - w.2
  have hg : Continuous g := by fun_prop
  have hclosed : IsClosed {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho} := by
    change IsClosed ({w : ℝ × ℝ | |w.1 - a0| ≤ rho} ∩
      ({w : ℝ × ℝ | 0 ≤ g w} ∩ {w : ℝ × ℝ | g w ≤ rho}))
    exact (isClosed_le (by fun_prop) continuous_const).inter
      ((isClosed_le continuous_const hg).inter (isClosed_le hg continuous_const))
  have hbox : IsCompact (Set.Icc (a0 - rho) (a0 + rho) ×ˢ
      Set.Icc (-rho) ((|a0| + rho) ^ 2 / level ^ 2)) :=
    isCompact_Icc.prod isCompact_Icc
  exact hbox.of_isClosed_subset hclosed (actual_parabola_window_bounded_box level a0 rho hrho)

theorem actual_parabola_finite_half_open_grid_cover
    (n : ℕ) (hn : 1 ≤ n) (level a0 rho : ℝ) (hrho : 0 ≤ rho) :
    let V : Set (ℝ × ℝ) := {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
    let cell : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k =>
      (Set.Ioc ((k.1 : ℝ) / (n : ℝ)) (((k.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
        Set.Ioc ((k.2 : ℝ) / (n : ℝ)) (((k.2 : ℝ) + 1) / (n : ℝ))) ∩ V
    let K : Set (ℤ × ℤ) := Set.Icc
      (Int.ceil ((n : ℝ) * (a0 - rho)) - 1,
        Int.ceil ((n : ℝ) * (-rho)) - 1)
      (Int.ceil ((n : ℝ) * (a0 + rho)) - 1,
        Int.ceil ((n : ℝ) * ((|a0| + rho) ^ 2 / level ^ 2)) - 1)
    K.Finite ∧ {k : ℤ × ℤ | (cell k).Nonempty} ⊆ K ∧
      (⋃ k ∈ K, cell k) = V ∧
      Pairwise (fun i j : ℤ × ℤ => Disjoint (cell i) (cell j)) := by
  let V : Set (ℝ × ℝ) := {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
    0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
  let cell : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k =>
    (Set.Ioc ((k.1 : ℝ) / (n : ℝ)) (((k.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
      Set.Ioc ((k.2 : ℝ) / (n : ℝ)) (((k.2 : ℝ) + 1) / (n : ℝ))) ∩ V
  let K : Set (ℤ × ℤ) := Set.Icc
    (Int.ceil ((n : ℝ) * (a0 - rho)) - 1,
      Int.ceil ((n : ℝ) * (-rho)) - 1)
    (Int.ceil ((n : ℝ) * (a0 + rho)) - 1,
      Int.ceil ((n : ℝ) * ((|a0| + rho) ^ 2 / level ^ 2)) - 1)
  change K.Finite ∧ {k : ℤ × ℤ | (cell k).Nonempty} ⊆ K ∧
    (⋃ k ∈ K, cell k) = V ∧
    Pairwise (fun i j : ℤ × ℤ => Disjoint (cell i) (cell j))
  have hN : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcontained : {k : ℤ × ℤ | (cell k).Nonempty} ⊆ K := by
    intro k hk
    obtain ⟨w, hw⟩ := hk
    have hb := actual_parabola_window_bounded_box level a0 rho hrho hw.2
    have hi1 := (real_ioc_grid_index_iff n hn w.1 k.1).mp hw.1.1
    have hi2 := (real_ioc_grid_index_iff n hn w.2 k.2).mp hw.1.2
    change (Int.ceil ((n : ℝ) * (a0 - rho)) - 1 ≤ k.1 ∧
      Int.ceil ((n : ℝ) * (-rho)) - 1 ≤ k.2) ∧
      (k.1 ≤ Int.ceil ((n : ℝ) * (a0 + rho)) - 1 ∧
      k.2 ≤ Int.ceil ((n : ℝ) * ((|a0| + rho) ^ 2 / level ^ 2)) - 1)
    rw [hi1, hi2]
    exact ⟨⟨sub_le_sub_right (Int.ceil_mono
        (mul_le_mul_of_nonneg_left hb.1.1 hN)) 1,
      sub_le_sub_right (Int.ceil_mono
        (mul_le_mul_of_nonneg_left hb.2.1 hN)) 1⟩,
      ⟨sub_le_sub_right (Int.ceil_mono
        (mul_le_mul_of_nonneg_left hb.1.2 hN)) 1,
      sub_le_sub_right (Int.ceil_mono
        (mul_le_mul_of_nonneg_left hb.2.2 hN)) 1⟩⟩
  have hpartition := actual_parabola_half_open_grid_partition n hn level a0 rho
  refine ⟨Set.finite_Icc _ _, hcontained, ?_, hpartition.2⟩
  apply Set.Subset.antisymm
  · intro w hw
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hw
    obtain ⟨_, hwk⟩ := Set.mem_iUnion.mp hk
    exact hwk.2
  · intro w hw
    have hu : w ∈ ⋃ k : ℤ × ℤ, cell k := hpartition.1.symm ▸ hw
    obtain ⟨k, hwk⟩ := Set.mem_iUnion.mp hu
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hcontained ⟨w, hwk⟩, hwk⟩⟩

end
end Shao.OQ3
