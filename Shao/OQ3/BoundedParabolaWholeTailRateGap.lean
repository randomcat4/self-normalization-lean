import Shao.OQ3.BoundedParabolaLegendreCompactSublevels

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem bounded_parabola_whole_tail_rate_gap_of_unique_minimum
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (lower upper : ℝ) (hlower : 0 < lower)
    (henergy : ∀ᵐ x ∂mu, lower ≤ x ^ 2 ∧ x ^ 2 ≤ upper)
    (level a0 rho J0 : ℝ) (hrho : 0 < rho) :
    let I : (ℝ × ℝ) → EReal :=
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
    let center : ℝ × ℝ := (a0, a0 ^ 2 / level ^ 2)
    let Tail : Set (ℝ × ℝ) := {w | 0 < w.2 ∧ level * Real.sqrt w.2 ≤ w.1}
    let U : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
      |w.1 ^ 2 / level ^ 2 - w.2| ≤ rho}
    I center = (J0 : EReal) →
      (∀ w ∈ Tail, I center ≤ I w ∧ (I w = I center ↔ w = center)) →
        ∃ delta : ℝ, 0 < delta ∧ ∀ w ∈ Tail \ U,
          ((J0 + delta : ℝ) : EReal) < I w := by
  classical
  intro I center Tail U hRate hUnique
  obtain ⟨hout, hcompact⟩ :=
    bounded_parabola_legendre_compact_sublevels mu M hM hb lower upper henergy
  let K : Set (ℝ × ℝ) := {w | I w ≤ ((J0 + 1 : ℝ) : EReal)}
  let C : Set (ℝ × ℝ) := {w | lower ≤ w.2 ∧ level * Real.sqrt w.2 ≤ w.1}
  let O : Set (ℝ × ℝ) := {w | |w.1 - a0| < rho ∧
    |w.1 ^ 2 / level ^ 2 - w.2| < rho}
  let F : Set (ℝ × ℝ) := K ∩ (C ∩ Oᶜ)
  have hK : IsCompact K := hcompact (J0 + 1)
  have hC : IsClosed C := by
    change IsClosed ({w : ℝ × ℝ | lower ≤ w.2} ∩
      {w : ℝ × ℝ | level * Real.sqrt w.2 ≤ w.1})
    exact (isClosed_le continuous_const continuous_snd).inter
      (isClosed_le (by fun_prop) continuous_fst)
  have hO : IsOpen O := by
    change IsOpen ({w : ℝ × ℝ | |w.1 - a0| < rho} ∩
      {w : ℝ × ℝ | |w.1 ^ 2 / level ^ 2 - w.2| < rho})
    exact (isOpen_lt (by fun_prop) continuous_const).inter
      (isOpen_lt (by fun_prop) continuous_const)
  have hCenter : center ∈ O := by
    change |a0 - a0| < rho ∧ |a0 ^ 2 / level ^ 2 - a0 ^ 2 / level ^ 2| < rho
    simpa only [sub_self, abs_zero] using And.intro hrho hrho
  have hF : IsCompact F := hK.of_isClosed_subset
    (hK.isClosed.inter (hC.inter hO.isClosed_compl)) (fun _ hw => hw.1)
  have hStrict (w : ℝ × ℝ) (hw : w ∈ F) : (J0 : EReal) < I w := by
    have hc : lower ≤ w.2 ∧ level * Real.sqrt w.2 ≤ w.1 := hw.2.1
    have ht : w ∈ Tail := ⟨hlower.trans_le hc.1, hc.2⟩
    have hne : w ≠ center := by
      intro heq
      exact hw.2.2 (heq.symm ▸ hCenter)
    obtain ⟨hmin, heq⟩ := hUnique w ht
    have hh : I center < I w :=
      lt_of_le_of_ne hmin (fun h => hne (heq.mp h.symm))
    simpa only [hRate] using hh
  have hgap : ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 / 2 ∧
      ∀ w ∈ F, ((J0 + delta : ℝ) : EReal) < I w := by
    by_cases hNonempty : F.Nonempty
    · obtain ⟨y, hy, hMin⟩ := LowerSemicontinuousOn.exists_isMinOn hNonempty hF
        ((bivariate_legendre_rate_lower_semicontinuous mu
          (fun x : ℝ => (x, x ^ 2))).lowerSemicontinuousOn F)
      obtain ⟨r, hrL, hrU⟩ := EReal.exists_between_coe_real (hStrict y hy)
      have hr : J0 < r := EReal.coe_lt_coe_iff.mp hrL
      refine ⟨min ((r - J0) / 2) (1 / 2),
        lt_min (half_pos (sub_pos.mpr hr)) (by norm_num), min_le_right _ _, ?_⟩
      intro w hw
      apply lt_of_lt_of_le ?_ (hMin hw)
      apply lt_trans ?_ hrU
      apply EReal.coe_lt_coe_iff.mpr
      have hh := min_le_left ((r - J0) / 2) (1 / 2)
      linarith
    · refine ⟨1 / 2, by norm_num, le_refl _, ?_⟩
      intro w hw
      exact False.elim (hNonempty ⟨w, hw⟩)
  obtain ⟨delta, hdelta, hdeltaHalf, hgapF⟩ := hgap
  refine ⟨delta, hdelta, ?_⟩
  intro w hw
  by_cases hcap : I w ≤ ((J0 + 1 : ℝ) : EReal)
  · have hqLower : lower ≤ w.2 := by
      by_contra hn
      have htop : I w = ⊤ := hout w (Or.inr (Or.inr (Or.inl (lt_of_not_ge hn))))
      rw [htop] at hcap
      exact (EReal.coe_lt_top (J0 + 1)).not_ge hcap
    have hOut : w ∉ O := by
      intro hwo
      exact hw.2 ⟨hwo.1.le, hwo.2.le⟩
    exact hgapF w ⟨hcap, ⟨⟨hqLower, hw.1.2⟩, hOut⟩⟩
  · exact (EReal.coe_lt_coe_iff.mpr (by linarith : J0 + delta < J0 + 1)).trans
      (lt_of_not_ge hcap)

end
end Shao.OQ3
