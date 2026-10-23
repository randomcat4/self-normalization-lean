import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Instances.Real.Lemmas

namespace Shao.OQ3
noncomputable section

theorem real_ioc_grid_index_iff
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (i : ℤ) :
    x ∈ Set.Ioc ((i : ℝ) / (n : ℝ)) (((i : ℝ) + 1) / (n : ℝ)) ↔
      i = Int.ceil ((n : ℝ) * x) - 1 := by
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
  constructor
  · intro hx
    have hl : (i : ℝ) < (n : ℝ) * x := by
      simpa only [mul_comm] using (div_lt_iff₀ hN).mp hx.1
    have hu : (n : ℝ) * x ≤ (i : ℝ) + 1 := by
      simpa only [mul_comm] using (le_div_iff₀ hN).mp hx.2
    have hc : Int.ceil ((n : ℝ) * x) = i + 1 := Int.ceil_eq_iff.mpr (by
      simpa only [Int.cast_add, Int.cast_one, add_sub_cancel_right] using And.intro hl hu)
    exact eq_sub_iff_add_eq.mpr hc.symm
  · intro hi
    have hc : Int.ceil ((n : ℝ) * x) = i + 1 := (eq_sub_iff_add_eq.mp hi).symm
    have hb : (i : ℝ) < (n : ℝ) * x ∧ (n : ℝ) * x ≤ (i : ℝ) + 1 := by
      simpa only [Int.cast_add, Int.cast_one, add_sub_cancel_right] using Int.ceil_eq_iff.mp hc
    exact ⟨(div_lt_iff₀ hN).mpr (by simpa only [mul_comm] using hb.1),
      (le_div_iff₀ hN).mpr (by simpa only [mul_comm] using hb.2)⟩

theorem actual_parabola_half_open_grid_partition
    (n : ℕ) (hn : 1 ≤ n) (level a0 rho : ℝ) :
    let V : Set (ℝ × ℝ) := {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
    let cell : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k =>
      (Set.Ioc ((k.1 : ℝ) / (n : ℝ)) (((k.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
        Set.Ioc ((k.2 : ℝ) / (n : ℝ)) (((k.2 : ℝ) + 1) / (n : ℝ))) ∩ V
    (⋃ k : ℤ × ℤ, cell k) = V ∧
      Pairwise (fun i j : ℤ × ℤ => Disjoint (cell i) (cell j)) := by
  let V : Set (ℝ × ℝ) := {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
    0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
  let cell : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k =>
    (Set.Ioc ((k.1 : ℝ) / (n : ℝ)) (((k.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
      Set.Ioc ((k.2 : ℝ) / (n : ℝ)) (((k.2 : ℝ) + 1) / (n : ℝ))) ∩ V
  change (⋃ k : ℤ × ℤ, cell k) = V ∧
    Pairwise (fun i j : ℤ × ℤ => Disjoint (cell i) (cell j))
  refine ⟨?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro w hw
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hw
      exact hk.2
    · intro w hw
      let k : ℤ × ℤ :=
        (Int.ceil ((n : ℝ) * w.1) - 1, Int.ceil ((n : ℝ) * w.2) - 1)
      refine Set.mem_iUnion.mpr ⟨k, ⟨⟨?_, ?_⟩, hw⟩⟩
      · exact (real_ioc_grid_index_iff n hn w.1 k.1).mpr rfl
      · exact (real_ioc_grid_index_iff n hn w.2 k.2).mpr rfl
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro w hiw hjw
    apply hij
    apply Prod.ext
    · exact ((real_ioc_grid_index_iff n hn w.1 i.1).mp hiw.1.1).trans
        ((real_ioc_grid_index_iff n hn w.1 j.1).mp hjw.1.1).symm
    · exact ((real_ioc_grid_index_iff n hn w.2 i.2).mp hiw.1.2).trans
        ((real_ioc_grid_index_iff n hn w.2 j.2).mp hjw.1.2).symm

end
end Shao.OQ3

