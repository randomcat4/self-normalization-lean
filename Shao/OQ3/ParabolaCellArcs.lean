import Shao.OQ3.ParabolaWindowCellFrontier
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace Shao.OQ3
open scoped Topology
noncomputable section

theorem actual_parabola_window_cell_six_compact_arcs
    (aL aR qL qR level a0 rho : ℝ) :
    let L : ℝ := max aL (a0 - rho)
    let R : ℝ := min aR (a0 + rho)
    let A : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩
      {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
        0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
    let curve : Fin 6 → ℝ → ℝ × ℝ := ![
      (fun t => (L + t * (R - L), qL)),
      (fun t => (L + t * (R - L), qR)),
      (fun t => (L, qL + t * (qR - qL))),
      (fun t => (R, qL + t * (qR - qL))),
      (fun t => (L + t * (R - L), (L + t * (R - L)) ^ 2 / level ^ 2)),
      (fun t => (L + t * (R - L), (L + t * (R - L)) ^ 2 / level ^ 2 - rho))]
    (∀ i : Fin 6, IsCompact (curve i '' Set.Icc (0 : ℝ) 1)) ∧
      frontier A ⊆ ⋃ i : Fin 6, curve i '' Set.Icc (0 : ℝ) 1 := by
  classical
  let L : ℝ := max aL (a0 - rho)
  let R : ℝ := min aR (a0 + rho)
  let A : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩
    {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
  let curve : Fin 6 → ℝ → ℝ × ℝ := ![
    (fun t => (L + t * (R - L), qL)),
    (fun t => (L + t * (R - L), qR)),
    (fun t => (L, qL + t * (qR - qL))),
    (fun t => (R, qL + t * (qR - qL))),
    (fun t => (L + t * (R - L), (L + t * (R - L)) ^ 2 / level ^ 2)),
    (fun t => (L + t * (R - L), (L + t * (R - L)) ^ 2 / level ^ 2 - rho))]
  have hcontinuous (i : Fin 6) : Continuous (curve i) := by
    fin_cases i <;> simp only [curve, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> fun_prop
  have hparam (b c x : ℝ) (hx : x ∈ Set.Icc b c) :
      ∃ t ∈ Set.Icc (0 : ℝ) 1, x = b + t * (c - b) := by
    by_cases hbc : b = c
    · subst c
      refine ⟨0, ⟨by norm_num, by norm_num⟩, ?_⟩
      simpa only [zero_mul, add_zero] using (le_antisymm hx.2 hx.1)
    · have hpos : 0 < c - b :=
        sub_pos.mpr (lt_of_le_of_ne (hx.1.trans hx.2) hbc)
      refine ⟨(x - b) / (c - b), ⟨div_nonneg (sub_nonneg.mpr hx.1) hpos.le, ?_⟩, ?_⟩
      · apply (div_le_iff₀ hpos).mpr
        linarith [hx.2]
      · calc
          x = b + (x - b) := by ring
          _ = b + ((x - b) / (c - b)) * (c - b) := by
            rw [div_mul_cancel₀ _ hpos.ne']
  have hfront := actual_parabola_window_cell_frontier aL aR qL qR level a0 rho
  refine ⟨fun i => isCompact_Icc.image (hcontinuous i), ?_⟩
  intro w hw
  rcases hfront w hw with hvertical | hhorizontal | hgraph
  · obtain ⟨hside, hqL, hqR⟩ := hvertical
    obtain ⟨t, ht, hrep⟩ := hparam qL qR w.2 ⟨hqL, hqR⟩
    rcases hside with hleft | hright
    · refine Set.mem_iUnion.mpr ⟨(2 : Fin 6), ⟨t, ht, ?_⟩⟩
      change (L, qL + t * (qR - qL)) = w
      exact Prod.ext hleft.symm hrep.symm
    · refine Set.mem_iUnion.mpr ⟨(3 : Fin 6), ⟨t, ht, ?_⟩⟩
      change (R, qL + t * (qR - qL)) = w
      exact Prod.ext hright.symm hrep.symm
  · obtain ⟨hside, haL, haR⟩ := hhorizontal
    obtain ⟨t, ht, hrep⟩ := hparam L R w.1 ⟨haL, haR⟩
    rcases hside with hbottom | htop
    · refine Set.mem_iUnion.mpr ⟨(0 : Fin 6), ⟨t, ht, ?_⟩⟩
      change (L + t * (R - L), qL) = w
      exact Prod.ext hrep.symm hbottom.symm
    · refine Set.mem_iUnion.mpr ⟨(1 : Fin 6), ⟨t, ht, ?_⟩⟩
      change (L + t * (R - L), qR) = w
      exact Prod.ext hrep.symm htop.symm
  · obtain ⟨haL, haR, hside⟩ := hgraph
    obtain ⟨t, ht, hrep⟩ := hparam L R w.1 ⟨haL, haR⟩
    rcases hside with hupper | hlower
    · refine Set.mem_iUnion.mpr ⟨(4 : Fin 6), ⟨t, ht, ?_⟩⟩
      change (L + t * (R - L), (L + t * (R - L)) ^ 2 / level ^ 2) = w
      apply Prod.ext hrep.symm
      rw [← hrep]
      exact hupper.symm
    · refine Set.mem_iUnion.mpr ⟨(5 : Fin 6), ⟨t, ht, ?_⟩⟩
      change (L + t * (R - L), (L + t * (R - L)) ^ 2 / level ^ 2 - rho) = w
      apply Prod.ext hrep.symm
      rw [← hrep]
      exact hlower.symm

end
end Shao.OQ3
