import Shao.OQ3.BoundedParabolaLegendreCompactSublevels

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem bounded_parabola_tail_global_minimum_of_finite_test
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (lower upper : ℝ) (hlower : 0 < lower)
    (henergy : ∀ᵐ x ∂mu, lower ≤ x ^ 2 ∧ x ^ 2 ≤ upper)
    (level L : ℝ) (w : ℝ × ℝ) (hwcone : level * Real.sqrt w.2 ≤ w.1)
    (hwfinite : Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w ≤
      (L : EReal)) :
    ∃ z : ℝ × ℝ, 0 < z.2 ∧ level * Real.sqrt z.2 ≤ z.1 ∧
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z ≤ (L : EReal) ∧
      ∀ y : ℝ × ℝ, 0 < y.2 → level * Real.sqrt y.2 ≤ y.1 →
        Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z ≤
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y := by
  let I : (ℝ × ℝ) → EReal :=
    Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
  have hsupport := bounded_parabola_legendre_compact_sublevels mu M hM hb lower upper henergy
  let C : Set (ℝ × ℝ) := {z | I z ≤ (L : EReal)} ∩
    {z | level * Real.sqrt z.2 ≤ z.1}
  have hsubclosed : IsClosed {z : ℝ × ℝ | I z ≤ (L : EReal)} :=
    (bivariate_legendre_rate_lower_semicontinuous mu (fun x : ℝ => (x, x ^ 2))).isClosed_preimage
      (L : EReal)
  have hconeclosed : IsClosed {z : ℝ × ℝ | level * Real.sqrt z.2 ≤ z.1} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hCclosed : IsClosed C := hsubclosed.inter hconeclosed
  have hCcompact : IsCompact C :=
    (hsupport.2 L).of_isClosed_subset hCclosed Set.inter_subset_left
  have hCnonempty : C.Nonempty := ⟨w, hwfinite, hwcone⟩
  obtain ⟨z, hz, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hCnonempty hCcompact
    ((bivariate_legendre_rate_lower_semicontinuous mu
      (fun x : ℝ => (x, x ^ 2))).lowerSemicontinuousOn C)
  have hzbound : I z ≤ (L : EReal) := hz.1
  have hzlower : lower ≤ z.2 := by
    by_contra h
    have htop : I z = ⊤ := hsupport.1 z
      (Or.inr (Or.inr (Or.inl (lt_of_not_ge h))))
    have hbad := hzbound
    rw [htop] at hbad
    exact (EReal.coe_lt_top L).not_ge hbad
  refine ⟨z, hlower.trans_le hzlower, hz.2, hzbound, ?_⟩
  intro y _hyq hycone
  by_cases hy : I y ≤ (L : EReal)
  · exact hmin ⟨hy, hycone⟩
  · exact hzbound.trans (lt_of_not_ge hy).le

end
end Shao.OQ3
