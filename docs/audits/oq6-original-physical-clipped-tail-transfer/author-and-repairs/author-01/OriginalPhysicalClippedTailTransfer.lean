import Shao.OQ6.ActualGoodsetPhysicalUnion
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Group.Arithmetic

set_option autoImplicit false
universe u
open Filter MeasureTheory
open scoped BigOperators Classical ENNReal symmDiff
open Shao.OQ5.P51
open Shao.OQ6.BoundedProductEnvelopeTails (tailScale)
open Shao.OQ6.CanonicalDoubleGhostRowMoments (sampleLaw)

namespace Shao.OQ6.OriginalPhysicalClippedTailTransfer
noncomputable section

theorem physical_clipped_globally_measurable
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (n : ℕ) (g : Ω → ℝ) (r : Ω → Ω → ℝ)
    (hg : Measurable g) (hr : Measurable (Function.uncurry r))
    (C0 rho y : ℝ) :
    let physical : (Fin n → Ω) → ℝ := fun x : Fin n → Ω =>
      if Real.sqrt (centeredSq n g r x) = 0 then 0 else
        (projectionW n g x + residualStatisticD n r x) /
          Real.sqrt (centeredSq n g r x)
    let clipped : (Fin n → Ω) → ℝ :=
      clippedCenteredStatistic n g r C0 rho y
    let Eclip : Set (Fin n → Ω) := {x : Fin n → Ω | clipped x ≠ physical x}
    Measurable physical ∧ Measurable clipped ∧ MeasurableSet Eclip := by
  classical
  intro physical clipped Eclip
  let W : (Fin n → Ω) → ℝ := projectionW n g
  let V : (Fin n → Ω) → ℝ := projectionV n g
  let D : (Fin n → Ω) → ℝ := residualStatisticD n r
  let Jenergy : (Fin n → Ω) → ℝ := residualEnergyJ n r
  let s2 : (Fin n → Ω) → ℝ := centeredSq n g r
  let s : (Fin n → Ω) → ℝ := fun x : Fin n → Ω => Real.sqrt (s2 x)
  let d : (Fin n → Ω) → ℝ := centeredDelta n g r
  let B : (Fin n → Ω) → ℝ := studentizerClipBudget n r C0 rho y
  let e : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r C0 rho y
  have hgcoord (i : Fin n) :
      Measurable (fun x : Fin n → Ω => g (x i)) :=
    hg.comp (measurable_pi_apply i)
  have hrcoord (i j : Fin n) :
      Measurable (fun x : Fin n → Ω => r (x i) (x j)) := by
    exact hr.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
  have hW : Measurable W := by
    change Measurable (fun x : Fin n → Ω =>
      (∑ i : Fin n, g (x i)) / Real.sqrt (n : ℝ))
    exact (Finset.measurable_sum Finset.univ
      (fun (i : Fin n) (_hi : i ∈ Finset.univ) => hgcoord i)).div_const _
  have hgsquares : Measurable (fun x : Fin n → Ω =>
      ∑ i : Fin n, g (x i) ^ (2 : ℕ)) := by
    apply Finset.measurable_sum Finset.univ
    intro i _hi
    simpa only [pow_two, Pi.mul_def] using (hgcoord i).mul (hgcoord i)
  have hV : Measurable V := by
    change Measurable (fun x : Fin n → Ω =>
      Real.sqrt ((∑ i : Fin n, g (x i) ^ (2 : ℕ)) / (n : ℝ)))
    exact (hgsquares.div_const (n : ℝ)).sqrt
  have hupper : Measurable
      (Shao.OQ6.CanonicalDoubleGhostScalarMoments.originalUpper n r) := by
    unfold Shao.OQ6.CanonicalDoubleGhostScalarMoments.originalUpper
    apply Finset.measurable_sum Finset.univ
    intro i _hi
    apply Finset.measurable_sum Finset.univ
    intro j _hj
    by_cases hij : i < j
    · simpa only [if_pos hij] using hrcoord i j
    · simpa only [if_neg hij] using
        (measurable_const : Measurable (fun _x : Fin n → Ω => (0 : ℝ)))
  have hD : Measurable D := by
    change Measurable (fun x : Fin n → Ω =>
      Shao.OQ6.CanonicalDoubleGhostScalarMoments.originalUpper n r x /
        (Real.sqrt (n : ℝ) * ((n : ℝ) - 1)))
    exact hupper.div_const _
  have hrow (i : Fin n) : Measurable (fun x : Fin n → Ω =>
      Shao.OQ6.CanonicalDoubleGhostRowMoments.originalRows n r x i) := by
    change Measurable (fun x : Fin n → Ω =>
      ∑ j : Fin n, if i = j then (0 : ℝ) else r (x i) (x j))
    apply Finset.measurable_sum Finset.univ
    intro j _hj
    by_cases hij : i = j
    · simpa only [if_pos hij] using
        (measurable_const : Measurable (fun _x : Fin n → Ω => (0 : ℝ)))
    · simpa only [if_neg hij] using hrcoord i j
  have hJenergy : Measurable Jenergy := by
    change Measurable (fun x : Fin n → Ω =>
      ∑ i : Fin n,
        (Shao.OQ6.CanonicalDoubleGhostRowMoments.originalRows n r x i /
          ((n : ℝ) - 2)) ^ (2 : ℕ))
    apply Finset.measurable_sum Finset.univ
    intro i _hi
    simpa only [pow_two, Pi.mul_def] using
      ((hrow i).div_const ((n : ℝ) - 2)).mul
        ((hrow i).div_const ((n : ℝ) - 2))
  have hsample (i j : Fin n) : Measurable (fun x : Fin n → Ω =>
      sampledKernel n g r x i j) :=
    ((hgcoord i).add (hgcoord j)).add (hrcoord i j)
  have hrowMean (i : Fin n) : Measurable (fun x : Fin n → Ω =>
      Shao.OQ6.FiniteRows.rowMean (sampledKernel n g r x) i) := by
    unfold Shao.OQ6.FiniteRows.rowMean
    exact measurable_const.mul
      (Finset.measurable_sum (Finset.univ.erase i)
        (fun (j : Fin n) (_hj : j ∈ Finset.univ.erase i) => hsample i j))
  have huStatistic : Measurable (fun x : Fin n → Ω =>
      Shao.OQ6.FiniteRows.uStatistic (sampledKernel n g r x)) := by
    unfold Shao.OQ6.FiniteRows.uStatistic Shao.OQ5.P35.unorderedPairSum
    apply Measurable.mul measurable_const
    apply Finset.measurable_sum Finset.univ
    intro i _hi
    apply Finset.measurable_sum Finset.univ
    intro j _hj
    by_cases hij : i < j
    · simpa only [if_pos hij] using hsample i j
    · simpa only [if_neg hij] using
        (measurable_const : Measurable (fun _x : Fin n → Ω => (0 : ℝ)))
  have hcenteredSquares : Measurable (fun x : Fin n → Ω =>
      ∑ i : Fin n,
        (Shao.OQ6.FiniteRows.rowMean (sampledKernel n g r x) i -
          Shao.OQ6.FiniteRows.uStatistic (sampledKernel n g r x)) ^ (2 : ℕ)) := by
    apply Finset.measurable_sum Finset.univ
    intro i _hi
    simpa only [pow_two, Pi.mul_def, Pi.sub_def] using
      ((hrowMean i).sub huStatistic).mul ((hrowMean i).sub huStatistic)
  have hs2 : Measurable s2 := by
    change Measurable (fun x : Fin n → Ω =>
      ((4 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ (2 : ℕ)) *
        ∑ i : Fin n,
          (Shao.OQ6.FiniteRows.rowMean (sampledKernel n g r x) i -
            Shao.OQ6.FiniteRows.uStatistic (sampledKernel n g r x)) ^ (2 : ℕ)) / 4)
    exact (measurable_const.mul hcenteredSquares).div_const 4
  have hs : Measurable s := hs2.sqrt
  have hVzero : MeasurableSet {x : Fin n → Ω | V x = 0} :=
    measurableSet_eq_fun hV measurable_const
  have hszero : MeasurableSet {x : Fin n → Ω | s x = 0} :=
    measurableSet_eq_fun hs measurable_const
  have hVsquare : Measurable (fun x : Fin n → Ω => V x ^ (2 : ℕ)) := by
    simpa only [pow_two, Pi.mul_def] using hV.mul hV
  have hd : Measurable d := by
    change Measurable (fun x : Fin n → Ω =>
      if V x = 0 then 0 else s2 x / V x ^ (2 : ℕ) - 1)
    exact Measurable.ite hVzero measurable_const
      ((hs2.div hVsquare).sub measurable_const)
  have hB : Measurable B := by
    change Measurable (fun x : Fin n → Ω =>
      C0 * (((1 + rho) * y) / Real.sqrt (n : ℝ) +
        Jenergy x / ((1 + rho) * y * Real.sqrt (n : ℝ))))
    exact measurable_const.mul (measurable_const.add (hJenergy.div_const _))
  have hclipvalue : Measurable (fun x : Fin n → Ω =>
      studentizerClip (B x) (d x)) := by
    unfold studentizerClip
    exact ((hB.min measurable_const).neg).max (hd.min hB)
  have he : Measurable e := by
    change Measurable (fun x : Fin n → Ω =>
      if V x = 0 then 0 else studentizerClip (B x) (d x))
    exact Measurable.ite hVzero measurable_const hclipvalue
  have hphysical : Measurable physical := by
    change Measurable (fun x : Fin n → Ω =>
      if s x = 0 then 0 else (W x + D x) / s x)
    exact Measurable.ite hszero measurable_const ((hW.add hD).div hs)
  have hclipped : Measurable clipped := by
    change Measurable (fun x : Fin n → Ω =>
      if V x = 0 then 0 else
        (W x + D x) / (V x * Real.sqrt (1 + e x)))
    exact Measurable.ite hVzero measurable_const
      ((hW.add hD).div (hV.mul (measurable_const.add he).sqrt))
  refine ⟨hphysical, hclipped, ?_⟩
  change MeasurableSet {x : Fin n → Ω | ¬ clipped x = physical x}
  exact (measurableSet_eq_fun hclipped hphysical).compl

theorem fixed_original_physical_clipped_closed_threshold_transfer
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgmean : (∫ o : Ω, g o ∂μ) = 0)
    (hgsecond : (∫ o : Ω, (g o) ^ (2 : ℕ) ∂μ) = 1) :
    ∃ cg : ℝ, 0 < cg ∧
      ∀ (C a t0 M : ℝ)
        (hC : 0 ≤ C) (ha : 0 ≤ a) (ht0 : 0 < t0) (hM : 0 ≤ M),
        let cCommon : ℝ :=
          min (remainderWindowScale (tailScale M) t0)
            (min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ)))
        0 < cCommon ∧
          ∀ᶠ n : ℕ in atTop,
            4 ≤ n ∧
              (1 : ℝ) ≤ cCommon * Real.rpow (n : ℝ) (1 / 6 : ℝ) ∧
              ∀ (r : Ω → Ω → ℝ) (w : Ω → ℝ)
                (hr : Measurable (Function.uncurry r))
                (hr1 : Integrable (Function.uncurry r) (μ.prod μ))
                (hcR : ∀ᵐ o : Ω ∂μ, (∫ o' : Ω, r o o' ∂μ) = 0)
                (hcL : ∀ᵐ o' : Ω ∂μ, (∫ o : Ω, r o o' ∂μ) = 0)
                (hW : ∀ᵐ o : Ω ∂μ, 0 ≤ w o)
                (hWR : ∀ᵐ o : Ω ∂μ, w o ≤ boundedPolylogHeight C a n)
                (hSq : Integrable (fun o : Ω => (w o) ^ (2 : ℕ)) μ)
                (hSqBound : (∫ o : Ω, (w o) ^ (2 : ℕ) ∂μ) ≤ M)
                (hEnv : ∀ᵐ p : Ω × Ω ∂μ.prod μ,
                  |r p.1 p.2| ≤ w p.1 * w p.2)
                (hsym : ∀ o o' : Ω, r o o' = r o' o)
                (rho : ℝ) (hrho : 0 ≤ rho)
                (hStudentizerWindow : 1 + rho ≤ Real.sqrt (n : ℝ))
                (z : ℝ) (hz : (1 : ℝ) ≤ z)
                (hzWindow : z ≤ cCommon * Real.rpow (n : ℝ) (1 / 6 : ℝ)),
                let q : ℝ := boundedPolylogMomentOrder t0 n
                let physical : (Fin n → Ω) → ℝ := fun x : Fin n → Ω =>
                  if Real.sqrt (centeredSq n g r x) = 0 then 0 else
                    (projectionW n g x + residualStatisticD n r x) /
                      Real.sqrt (centeredSq n g r x)
                let clipped : (Fin n → Ω) → ℝ :=
                  clippedCenteredStatistic n g r 512 rho 1
                let Eclip : Set (Fin n → Ω) := {x : Fin n → Ω | clipped x ≠ physical x}
                Measurable physical ∧ Measurable clipped ∧ MeasurableSet Eclip ∧
                  (sampleLaw n μ).real Eclip ≤
                    (6 : ℝ) * Real.exp (-q) +
                      (2 : ℝ) * Real.exp (-cg * (n : ℝ)) +
                      (8 : ℝ) * Real.exp (-(Real.sqrt (n : ℝ)) / (2 : ℝ)) ∧
                  (sampleLaw n μ).real Eclip ≤
                    Real.exp (-(t0 / (2 : ℝ)) *
                      Real.rpow (n : ℝ) (1 / 3 : ℝ)) * Shao.standardNormalTail z ∧
                  (∀ t : ℝ,
                    |(sampleLaw n μ).real {x : Fin n → Ω | t ≤ physical x} -
                        (sampleLaw n μ).real {x : Fin n → Ω | t ≤ clipped x}| ≤
                      (sampleLaw n μ).real Eclip ∧
                    |(sampleLaw n μ).real {x : Fin n → Ω | physical x ≤ t} -
                        (sampleLaw n μ).real {x : Fin n → Ω | clipped x ≤ t}| ≤
                      (sampleLaw n μ).real Eclip) := by
  classical
  let cg : ℝ := Classical.choose
    (Shao.OQ6.ActualGoodsetPhysicalUnion.fixed_original_goodset_physical_exceptional_union
      μ g hg hg2 hgmean hgsecond)
  have h237All := Classical.choose_spec
    (Shao.OQ6.ActualGoodsetPhysicalUnion.fixed_original_goodset_physical_exceptional_union
      μ g hg hg2 hgmean hgsecond)
  refine ⟨cg, h237All.1, ?_⟩
  intro C a t0 M hC ha ht0 hM cCommon
  have h237Window := h237All.2 C a t0 M hC ha ht0 hM
  refine ⟨h237Window.1, ?_⟩
  filter_upwards [h237Window.2] with n hn
  refine ⟨hn.1, hn.2.1, ?_⟩
  intro r w hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hsym
    rho hrho hStudentizerWindow z hz hzWindow
  intro q physical clipped Eclip
  let Pn : Measure (Fin n → Ω) := sampleLaw n μ
  letI instPn : IsProbabilityMeasure Pn :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => μ)))
  let K : ℝ := tailScale M
  let Gz : Set (Fin n → Ω) := projectionGood n g z
  let C2 : Set (Fin n → Ω) :=
    {x : Fin n → Ω |
      |Shao.OQ6.CanonicalDoubleGhostScalarMoments.originalUpper n r x| ≤
        K * (n : ℝ) * q ∧
      ‖Shao.OQ6.CanonicalDoubleGhostRowMoments.originalRows n r x‖ ^ (2 : ℕ) ≤
        K * (n : ℝ) ^ (2 : ℕ) * q}
  let H : Set (Fin n → Ω) := Gz ∩ C2
  let J : Set (Fin n → Ω) := H \ Eclip
  have h237 := hn.2.2 r w hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hsym
    rho hrho hStudentizerWindow z hz hzWindow
  have hJfee : Pn.real Jᶜ ≤
      (6 : ℝ) * Real.exp (-q) +
        (2 : ℝ) * Real.exp (-cg * (n : ℝ)) +
        (8 : ℝ) * Real.exp (-(Real.sqrt (n : ℝ)) / (2 : ℝ)) :=
    h237.2.2.2.2.2.2.1
  have hJgaussian : Pn.real Jᶜ ≤
      Real.exp (-(t0 / (2 : ℝ)) *
        Real.rpow (n : ℝ) (1 / 3 : ℝ)) * Shao.standardNormalTail z :=
    h237.2.2.2.2.2.2.2
  have hEJ : Eclip ⊆ Jᶜ := by
    intro x hx hJx
    exact hJx.2 hx
  have hEJprob : Pn.real Eclip ≤ Pn.real Jᶜ :=
    measureReal_mono (μ := Pn) hEJ (measure_ne_top Pn Jᶜ)
  have hmeas := physical_clipped_globally_measurable n g r hg hr 512 rho 1
  have hphysical : Measurable physical := hmeas.1
  have hclipped : Measurable clipped := hmeas.2.1
  have hEclip : MeasurableSet Eclip := hmeas.2.2
  refine ⟨hphysical, hclipped, hEclip, hEJprob.trans hJfee,
    hEJprob.trans hJgaussian, ?_⟩
  intro t
  let Aupper : Set (Fin n → Ω) := {x : Fin n → Ω | t ≤ physical x}
  let Bupper : Set (Fin n → Ω) := {x : Fin n → Ω | t ≤ clipped x}
  let Alower : Set (Fin n → Ω) := {x : Fin n → Ω | physical x ≤ t}
  let Blower : Set (Fin n → Ω) := {x : Fin n → Ω | clipped x ≤ t}
  have hAupper : MeasurableSet Aupper := by
    simpa only [Aupper, Set.compl_setOf, not_lt] using
      (measurableSet_lt hphysical
        (measurable_const : Measurable (fun _x : Fin n → Ω => t))).compl
  have hBupper : MeasurableSet Bupper := by
    simpa only [Bupper, Set.compl_setOf, not_lt] using
      (measurableSet_lt hclipped
        (measurable_const : Measurable (fun _x : Fin n → Ω => t))).compl
  have hAlower : MeasurableSet Alower := by
    simpa only [Alower, Set.compl_setOf, not_lt] using
      (measurableSet_lt
        (measurable_const : Measurable (fun _x : Fin n → Ω => t)) hphysical).compl
  have hBlower : MeasurableSet Blower := by
    simpa only [Blower, Set.compl_setOf, not_lt] using
      (measurableSet_lt
        (measurable_const : Measurable (fun _x : Fin n → Ω => t)) hclipped).compl
  have hupperSub : (Aupper ∆ Bupper) ⊆ Eclip := by
    intro x hx
    change clipped x ≠ physical x
    intro heq
    rcases hx with hx | hx
    · apply hx.2
      change t ≤ clipped x
      rw [heq]
      exact hx.1
    · apply hx.2
      change t ≤ physical x
      rw [← heq]
      exact hx.1
  have hlowerSub : (Alower ∆ Blower) ⊆ Eclip := by
    intro x hx
    change clipped x ≠ physical x
    intro heq
    rcases hx with hx | hx
    · apply hx.2
      change clipped x ≤ t
      rw [heq]
      exact hx.1
    · apply hx.2
      change physical x ≤ t
      rw [← heq]
      exact hx.1
  have hupperDiff : |Pn.real Aupper - Pn.real Bupper| ≤ Pn.real Eclip := by
    calc
      |Pn.real Aupper - Pn.real Bupper| ≤ Pn.real (Aupper ∆ Bupper) :=
        abs_measureReal_sub_le_measureReal_symmDiff (μ := Pn)
          hAupper.nullMeasurableSet hBupper.nullMeasurableSet
      _ ≤ Pn.real Eclip :=
        measureReal_mono (μ := Pn) hupperSub (measure_ne_top Pn Eclip)
  have hlowerDiff : |Pn.real Alower - Pn.real Blower| ≤ Pn.real Eclip := by
    calc
      |Pn.real Alower - Pn.real Blower| ≤ Pn.real (Alower ∆ Blower) :=
        abs_measureReal_sub_le_measureReal_symmDiff (μ := Pn)
          hAlower.nullMeasurableSet hBlower.nullMeasurableSet
      _ ≤ Pn.real Eclip :=
        measureReal_mono (μ := Pn) hlowerSub (measure_ne_top Pn Eclip)
  exact ⟨hupperDiff, hlowerDiff⟩

end
end Shao.OQ6.OriginalPhysicalClippedTailTransfer
