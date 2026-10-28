import Shao.OQ3.ParabolaCellRateAnchor

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem actual_high_energy_exterior_rate_gap_of_unique_minimum
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (level a0 B eta rho J0 : ℝ) (heta : 0 < eta) (hrho : 0 < rho) :
    let I : (ℝ × ℝ) → EReal :=
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
    let center : ℝ × ℝ := (a0, a0 ^ 2 / level ^ 2)
    let Tail : Set (ℝ × ℝ) := {w | 0 < w.2 ∧ level * Real.sqrt w.2 ≤ w.1}
    let U : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
      |w.1 ^ 2 / level ^ 2 - w.2| ≤ rho}
    let Carrier : Set (ℝ × ℝ) := Set.Icc (-B) B ×ˢ Set.Icc 0 (B ^ 2)
    let A : Set (ℝ × ℝ) := (Tail \ U) ∩ {w | eta ≤ w.2}
    I center = (J0 : EReal) →
      (∀ w ∈ Tail, I center ≤ I w ∧ (I w = I center ↔ w = center)) →
        ∃ delta : ℝ, 0 < delta ∧ ∀ w ∈ Carrier ∩ closure A,
          ((J0 + delta : ℝ) : EReal) < I w := by
  classical
  intro I center Tail U Carrier A hRate hUnique
  let C : Set (ℝ × ℝ) := {w | eta ≤ w.2 ∧ level * Real.sqrt w.2 ≤ w.1}
  have hC : IsClosed C := by
    change IsClosed ({w : ℝ × ℝ | eta ≤ w.2} ∩
      {w : ℝ × ℝ | level * Real.sqrt w.2 ≤ w.1})
    exact (isClosed_le continuous_const continuous_snd).inter
      (isClosed_le (by fun_prop) continuous_fst)
  have hAC : A ⊆ C := fun _ hw => ⟨hw.2, hw.1.1.2⟩
  have hClosureC : closure A ⊆ C := closure_minimal hAC hC
  let O : Set (ℝ × ℝ) := {w | |w.1 - a0| < rho ∧
    |w.1 ^ 2 / level ^ 2 - w.2| < rho}
  have hO : IsOpen O := by
    change IsOpen ({w : ℝ × ℝ | |w.1 - a0| < rho} ∩
      {w : ℝ × ℝ | |w.1 ^ 2 / level ^ 2 - w.2| < rho})
    exact (isOpen_lt (by fun_prop) continuous_const).inter
      (isOpen_lt (by fun_prop) continuous_const)
  have hOU : O ⊆ U := fun _ hw => ⟨hw.1.le, hw.2.le⟩
  have hCenterO : center ∈ O := by
    change |a0 - a0| < rho ∧ |a0 ^ 2 / level ^ 2 - a0 ^ 2 / level ^ 2| < rho
    simpa only [sub_self, abs_zero] using And.intro hrho hrho
  have hCenter : center ∈ interior U := (interior_maximal hOU hO) hCenterO
  have hAOut : A ⊆ (interior U)ᶜ := by
    intro w hw hInt
    exact hw.1.2 (interior_subset hInt)
  have hClosureOut : closure A ⊆ (interior U)ᶜ :=
    closure_minimal hAOut isOpen_interior.isClosed_compl
  let F : Set (ℝ × ℝ) := Carrier ∩ closure A
  have hCarrier : IsCompact Carrier := isCompact_Icc.prod isCompact_Icc
  have hF : IsCompact F := hCarrier.of_isClosed_subset
    (hCarrier.isClosed.inter isClosed_closure) (fun _ hw => hw.1)
  have hStrict (w : ℝ × ℝ) (hw : w ∈ F) : (J0 : EReal) < I w := by
    have hc := hClosureC hw.2
    have hTail : w ∈ Tail := ⟨heta.trans_le hc.1, hc.2⟩
    have hne : w ≠ center := by
      intro heq
      exact (hClosureOut hw.2) (heq.symm ▸ hCenter)
    obtain ⟨hmin, heq⟩ := hUnique w hTail
    have hh : I center < I w :=
      lt_of_le_of_ne hmin (fun h => hne (heq.mp h.symm))
    simpa only [hRate] using hh
  by_cases hNonempty : F.Nonempty
  · obtain ⟨y, hy, hMin⟩ := LowerSemicontinuousOn.exists_isMinOn hNonempty hF
      ((bivariate_legendre_rate_lower_semicontinuous mu
        (fun x : ℝ => (x, x ^ 2))).lowerSemicontinuousOn F)
    obtain ⟨r, hrL, hrU⟩ := EReal.exists_rat_btwn_of_lt (hStrict y hy)
    have hr : J0 < (r : ℝ) := EReal.coe_lt_coe_iff.mp hrL
    refine ⟨(r : ℝ) - J0, sub_pos.mpr hr, ?_⟩
    intro w hw
    have heq : J0 + ((r : ℝ) - J0) = (r : ℝ) := by ring
    rw [heq]
    exact hrU.trans_le (hMin hw)
  · refine ⟨1, by norm_num, ?_⟩
    intro w hw
    exact False.elim (hNonempty ⟨w, hw⟩)

end
end Shao.OQ3
