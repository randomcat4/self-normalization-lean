import Shao.Probability.OriginalCDFPullback
import Shao.C2.TwoSided

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
noncomputable section
namespace Shao.C2.ActualOriginalDoublePullback
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

theorem source_truncation_original_double_pullback :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 →
        (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ x epsilon : ℝ, 0 < x → 0 < epsilon → epsilon ≤ 1 / 800 →
          Shao.truncationBudget nu n x ≤ epsilon ^ 3 / 8 →
          let h : ℝ := epsilon / (1 + x)
          let N : Set (Shao.Path n) := {v | ∀ j : Fin n, |v j| ≤ h}
          let P0 : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
          let rho : Measure ℝ := ProbabilityTheory.cond nu {z | |z| ≤ h}
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
          let p : ℝ := P0.real N
          let R : ℝ := Shao.truncationBudget nu n x
          (7 / 8 : ℝ) ≤ p ∧ p ≤ 1 ∧ 1 - p ≤ R / epsilon ^ 3 ∧
            IsProbabilityMeasure rho ∧ IsProbabilityMeasure P ∧
            ProbabilityTheory.cond P0 N = P ∧
            ∀ d : ℝ, 0 ≤ d → d ≤ 2 * Shao.standardNormalTail x →
              P0.real (Shao.C2.doubleCrossing hn x) - d =
                p * (P.real (Shao.C2.doubleCrossing hn x) - d) +
                  P0.real (Shao.C2.doubleCrossing hn x ∩ Nᶜ) - (1 - p) * d ∧
              0 ≤ P0.real (Shao.C2.doubleCrossing hn x ∩ Nᶜ) ∧
              P0.real (Shao.C2.doubleCrossing hn x ∩ Nᶜ) + (1 - p) * d ≤
                C / epsilon ^ 3 * R * Shao.standardNormalTail x ∧
              |(P0.real (Shao.C2.doubleCrossing hn x) - d) -
                  p * (P.real (Shao.C2.doubleCrossing hn x) - d)| ≤
                C / epsilon ^ 3 * R * Shao.standardNormalTail x := by
  classical
  obtain ⟨_Cpull, _hCpull, hPull⟩ :=
    Shao.Probability.sourceTruncation_original_max_cdf_pullback
  obtain ⟨Cb, hCb, hBad⟩ :=
    Shao.Probability.sourceTruncation_original_two_signs_bad_crossing
  refine ⟨Cb + 2, by linarith only [hCb], ?_⟩
  intro nu _ n hn h2 hmean hnorm x epsilon hx he he800 hR
  intro h N P0 rho P p R
  rcases hPull nu n hn h2 hmean hnorm x epsilon hx.le he he800 hR with
    ⟨hp, hp1, hcomp, hRho, hP, hcond, _hCDFIdentity, _hCDFPayment⟩
  change (7 / 8 : ℝ) ≤ p at hp
  change p ≤ 1 at hp1
  change 1 - p ≤ R / epsilon ^ 3 at hcomp
  change IsProbabilityMeasure rho at hRho
  change IsProbabilityMeasure P at hP
  change ProbabilityTheory.cond P0 N = P at hcond
  letI : IsProbabilityMeasure rho := hRho
  letI : IsProbabilityMeasure P := hP
  let D : Set (Shao.Path n) := Shao.C2.doubleCrossing hn x
  have hNm : MeasurableSet N := by
    have hNset : N = ⋂ i : Fin n, {v : Shao.Path n | |v i| ≤ h} := by
      ext v
      simp only [N, Set.mem_setOf_eq, Set.mem_iInter]
    rw [hNset]
    exact MeasurableSet.iInter (fun i : Fin n => measurableSet_le
      (continuous_abs.measurable.comp
        (measurable_pi_apply i : Measurable (fun v : Shao.Path n => v i))) measurable_const)
  have hProduct : P.real D * p = P0.real (N ∩ D) := by
    simpa only [hcond, p, Measure.real_def, ENNReal.toReal_mul] using
      congrArg ENNReal.toReal (cond_mul_eq_inter hNm D P0)
  have hSplit := measureReal_inter_add_sdiff (μ := P0) (s := D) hNm
  have hDiff : D \ N = D ∩ Nᶜ := rfl
  rw [hDiff, Set.inter_comm D N, ← hProduct] at hSplit
  have hUpperBad : P0.real (Shao.upperCrossing hn x ∩ Nᶜ) ≤
      Cb / epsilon ^ 3 * (R * Shao.standardNormalTail x) := by
    have hb := (hBad nu n hn h2 hmean hnorm x epsilon hx.le he he800 hR
      x hx (by simpa only [sub_self, abs_zero] using (one_div_pos.mpr (show 0 < 1 + x by linarith only [hx])).le)).1 1 (Or.inl rfl)
    simpa only [one_smul] using hb
  have hDoubleSubset : D ∩ Nᶜ ⊆ Shao.upperCrossing hn x ∩ Nᶜ := by
    intro v hv
    exact ⟨hv.1.1, hv.2⟩
  have hDoubleBad : P0.real (D ∩ Nᶜ) ≤
      Cb / epsilon ^ 3 * (R * Shao.standardNormalTail x) :=
    (measureReal_mono hDoubleSubset).trans hUpperBad
  have hBadNonneg : 0 ≤ P0.real (D ∩ Nᶜ) := measureReal_nonneg
  have hRnonneg : 0 ≤ R := Shao.truncationBudget_nonneg nu n h2 x
  have heCube : 0 < epsilon ^ 3 := pow_pos he 3
  have hBudgetNonneg : 0 ≤ R / epsilon ^ 3 := div_nonneg hRnonneg heCube.le
  refine ⟨hp, hp1, hcomp, hRho, hP, hcond, ?_⟩
  intro d hd hdTail
  have hBiasNonneg : 0 ≤ (1 - p) * d := mul_nonneg (sub_nonneg.mpr hp1) hd
  have hBiasBound : (1 - p) * d ≤
      (R / epsilon ^ 3) * (2 * Shao.standardNormalTail x) :=
    mul_le_mul hcomp hdTail hd hBudgetNonneg
  have hSum : P0.real (D ∩ Nᶜ) + (1 - p) * d ≤
      (Cb + 2) / epsilon ^ 3 * R * Shao.standardNormalTail x := by
    calc
      P0.real (D ∩ Nᶜ) + (1 - p) * d ≤
          Cb / epsilon ^ 3 * (R * Shao.standardNormalTail x) +
            (R / epsilon ^ 3) * (2 * Shao.standardNormalTail x) :=
        add_le_add hDoubleBad hBiasBound
      _ = (Cb + 2) / epsilon ^ 3 * R * Shao.standardNormalTail x := by ring
  have hMix : P0.real D - d =
      p * (P.real D - d) + P0.real (D ∩ Nᶜ) - (1 - p) * d := by
    nlinarith only [hSplit]
  have hError : |(P0.real D - d) - p * (P.real D - d)| ≤
      (Cb + 2) / epsilon ^ 3 * R * Shao.standardNormalTail x := by
    rw [hMix]
    apply abs_le.mpr
    constructor
    · nlinarith only [hBadNonneg, hBiasNonneg, hSum]
    · nlinarith only [hBadNonneg, hBiasNonneg, hSum]
  exact ⟨hMix, hBadNonneg, hSum, hError⟩

end Shao.C2.ActualOriginalDoublePullback
