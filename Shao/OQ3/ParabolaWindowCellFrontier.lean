import Shao.OQ3.BoundaryLaplaceEventGeometry

namespace Shao.OQ3
open scoped Topology
noncomputable section

theorem parabola_strip_cell_frontier_of_sandwich
    (aL aR qL qR level rho : ℝ) (A : Set (ℝ × ℝ))
    (hinside : {w : ℝ × ℝ | aL < w.1 ∧ w.1 < aR ∧ qL < w.2 ∧ w.2 < qR ∧
      0 < w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 < rho} ⊆ A)
    (houtside : A ⊆ {w : ℝ × ℝ | aL ≤ w.1 ∧ w.1 ≤ aR ∧ qL ≤ w.2 ∧ w.2 ≤ qR ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}) :
    ∀ w ∈ frontier A,
      ((w.1 = aL ∨ w.1 = aR) ∧ qL ≤ w.2 ∧ w.2 ≤ qR) ∨
      ((w.2 = qL ∨ w.2 = qR) ∧ aL ≤ w.1 ∧ w.1 ≤ aR) ∨
      (aL ≤ w.1 ∧ w.1 ≤ aR ∧
        (w.2 = w.1 ^ 2 / level ^ 2 ∨ w.2 = w.1 ^ 2 / level ^ 2 - rho)) := by
  classical
  let g : (ℝ × ℝ) → ℝ := fun w => w.1 ^ 2 / level ^ 2 - w.2
  let O : Set (ℝ × ℝ) := {w | aL < w.1 ∧ w.1 < aR ∧ qL < w.2 ∧ w.2 < qR ∧
    0 < g w ∧ g w < rho}
  let C : Set (ℝ × ℝ) := {w | aL ≤ w.1 ∧ w.1 ≤ aR ∧ qL ≤ w.2 ∧ w.2 ≤ qR ∧
    0 ≤ g w ∧ g w ≤ rho}
  have hg : Continuous g := by
    dsimp only [g]
    fun_prop
  have hO : IsOpen O :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_const).inter
        ((isOpen_lt continuous_const continuous_snd).inter
          ((isOpen_lt continuous_snd continuous_const).inter
            ((isOpen_lt continuous_const hg).inter (isOpen_lt hg continuous_const)))))
  have hC : IsClosed C :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_const).inter
        ((isClosed_le continuous_const continuous_snd).inter
          ((isClosed_le continuous_snd continuous_const).inter
            ((isClosed_le continuous_const hg).inter (isClosed_le hg continuous_const)))))
  have hclosure : closure A ⊆ C := closure_minimal houtside hC
  have hinterior : O ⊆ interior A := interior_maximal hinside hO
  intro w hw
  obtain ⟨haL, haR, hqL, hqR, hg0, hgR⟩ := hclosure hw.1
  by_cases hleft : w.1 = aL
  · exact Or.inl ⟨Or.inl hleft, hqL, hqR⟩
  by_cases hright : w.1 = aR
  · exact Or.inl ⟨Or.inr hright, hqL, hqR⟩
  by_cases hbottom : w.2 = qL
  · exact Or.inr (Or.inl ⟨Or.inl hbottom, haL, haR⟩)
  by_cases htop : w.2 = qR
  · exact Or.inr (Or.inl ⟨Or.inr htop, haL, haR⟩)
  by_cases hzero : g w = 0
  · right
    right
    refine ⟨haL, haR, Or.inl ?_⟩
    dsimp only [g] at hzero
    linarith
  by_cases hrho : g w = rho
  · right
    right
    refine ⟨haL, haR, Or.inr ?_⟩
    dsimp only [g] at hrho
    linarith
  have hwO : w ∈ O :=
    ⟨lt_of_le_of_ne haL (Ne.symm hleft), lt_of_le_of_ne haR hright,
      lt_of_le_of_ne hqL (Ne.symm hbottom), lt_of_le_of_ne hqR htop,
      lt_of_le_of_ne hg0 (Ne.symm hzero), lt_of_le_of_ne hgR hrho⟩
  exact (hw.2 (hinterior hwO)).elim

theorem actual_parabola_window_cell_frontier
    (aL aR qL qR level a0 rho : ℝ) :
    let L : ℝ := max aL (a0 - rho)
    let R : ℝ := min aR (a0 + rho)
    let A : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩
      {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
        0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
    ∀ w ∈ frontier A,
      ((w.1 = L ∨ w.1 = R) ∧ qL ≤ w.2 ∧ w.2 ≤ qR) ∨
      ((w.2 = qL ∨ w.2 = qR) ∧ L ≤ w.1 ∧ w.1 ≤ R) ∨
      (L ≤ w.1 ∧ w.1 ≤ R ∧
        (w.2 = w.1 ^ 2 / level ^ 2 ∨ w.2 = w.1 ^ 2 / level ^ 2 - rho)) := by
  let L : ℝ := max aL (a0 - rho)
  let R : ℝ := min aR (a0 + rho)
  let A : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩
    {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
  have hinside : {w : ℝ × ℝ | L < w.1 ∧ w.1 < R ∧ qL < w.2 ∧ w.2 < qR ∧
      0 < w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 < rho} ⊆ A := by
    intro w hw
    obtain ⟨hL, hR, hqL, hqR, hg0, hgrho⟩ := hw
    have haL : aL < w.1 := (le_max_left aL (a0 - rho)).trans_lt hL
    have haR : w.1 ≤ aR := hR.le.trans (min_le_left aR (a0 + rho))
    have ha0L : a0 - rho ≤ w.1 := (le_max_right aL (a0 - rho)).trans hL.le
    have ha0R : w.1 ≤ a0 + rho := hR.le.trans (min_le_right aR (a0 + rho))
    exact ⟨⟨⟨haL, haR⟩, ⟨hqL, hqR.le⟩⟩,
      ⟨abs_le.mpr ⟨by linarith, by linarith⟩, hg0.le, hgrho.le⟩⟩
  have houtside : A ⊆ {w : ℝ × ℝ | L ≤ w.1 ∧ w.1 ≤ R ∧ qL ≤ w.2 ∧ w.2 ≤ qR ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho} := by
    intro w hw
    obtain ⟨⟨ha, hq⟩, habs, hg0, hgrho⟩ := hw
    have hnear := abs_le.mp habs
    exact ⟨max_le ha.1.le (by linarith [hnear.1]),
      le_min ha.2 (by linarith [hnear.2]), hq.1.le, hq.2, hg0, hgrho⟩
  exact parabola_strip_cell_frontier_of_sandwich L R qL qR level rho A hinside houtside

end
end Shao.OQ3
