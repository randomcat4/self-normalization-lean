import Shao.Probability.BivariateLegendre
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem bivariate_legendre_rate_lower_semicontinuous
    {Ω : Type*} [MeasurableSpace Ω] (mu : MeasureTheory.Measure Ω) [NeZero mu]
    (W : Ω → ℝ × ℝ) :
    LowerSemicontinuous (Shao.Probability.bivariateLegendreRate mu W) := by
  change LowerSemicontinuous (fun z : ℝ × ℝ =>
    ⨆ theta : Shao.Probability.bivariateMGFDomain mu W,
      (((theta : ℝ × ℝ).1 * z.1 + (theta : ℝ × ℝ).2 * z.2 -
        Shao.Probability.bivariateLogMGF mu W theta : ℝ) : EReal))
  apply lowerSemicontinuous_iSup
  intro theta
  have htest : Continuous (fun z : ℝ × ℝ =>
      (theta : ℝ × ℝ).1 * z.1 + (theta : ℝ × ℝ).2 * z.2 -
        Shao.Probability.bivariateLogMGF mu W theta) := by fun_prop
  exact (continuous_coe_real_ereal.comp htest).lowerSemicontinuous

theorem actual_parabola_cell_closure_rate_anchor
    (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu]
    (aL aR qL qR level a0 rho : ℝ)
    (hA : (((Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩
      {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
        0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}) :
          Set (ℝ × ℝ)).Nonempty) :
    let V : Set (ℝ × ℝ) := {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
    let A : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩ V
    let Q : Set (ℝ × ℝ) := Set.Icc aL aR ×ˢ Set.Icc qL qR
    IsCompact (closure A) ∧
      ∃ y ∈ closure A, y ∈ Q ∩ V ∧
        ∀ w ∈ closure A,
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y ≤
            Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w := by
  let V : Set (ℝ × ℝ) := {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
    0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
  let A : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩ V
  let Q : Set (ℝ × ℝ) := Set.Icc aL aR ×ˢ Set.Icc qL qR
  let g : (ℝ × ℝ) → ℝ := fun w => w.1 ^ 2 / level ^ 2 - w.2
  have hg : Continuous g := by fun_prop
  have hQ : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  have hAQ : A ⊆ Q := by
    intro w hw
    exact ⟨⟨hw.1.1.1.le, hw.1.1.2⟩, ⟨hw.1.2.1.le, hw.1.2.2⟩⟩
  have hAV : A ⊆ V := fun _ hw => hw.2
  have hV : IsClosed V := by
    change IsClosed ({w : ℝ × ℝ | |w.1 - a0| ≤ rho} ∩
      ({w : ℝ × ℝ | 0 ≤ g w} ∩ {w : ℝ × ℝ | g w ≤ rho}))
    exact (isClosed_le (by fun_prop) continuous_const).inter
      ((isClosed_le continuous_const hg).inter (isClosed_le hg continuous_const))
  have hclosureQ : closure A ⊆ Q := closure_minimal hAQ hQ.isClosed
  have hclosureV : closure A ⊆ V := closure_minimal hAV hV
  have hcompact : IsCompact (closure A) :=
    hQ.of_isClosed_subset isClosed_closure hclosureQ
  have hnonempty : (closure A).Nonempty := hA.closure
  obtain ⟨y, hy, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hnonempty hcompact
    ((bivariate_legendre_rate_lower_semicontinuous mu
      (fun x : ℝ => (x, x ^ 2))).lowerSemicontinuousOn (closure A))
  refine ⟨hcompact, y, hy, ⟨hclosureQ hy, hclosureV hy⟩, ?_⟩
  intro w hw
  exact hmin hw

end
end Shao.OQ3

