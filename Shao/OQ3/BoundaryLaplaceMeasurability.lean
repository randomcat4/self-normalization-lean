import Shao.OQ3.BoundaryLaplaceIntegral
import Mathlib.Analysis.Calculus.ContDiff.Defs

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem boundary_laplace_cutoff_aestronglyMeasurable_of_continuousOn
    (F A : (ℝ × ℝ) → ℝ) (rho t : ℝ)
    (hF : ContinuousOn F {w : ℝ × ℝ | |w.1| ≤ rho ∧ 0 ≤ w.2 ∧ w.2 ≤ rho})
    (hA : ContinuousOn A {w : ℝ × ℝ | |w.1| ≤ rho ∧ 0 ≤ w.2 ∧ w.2 ≤ rho}) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      if |t * p.1| ≤ rho ∧ t ^ 2 * p.2 ≤ rho then
        A (t * p.1, t ^ 2 * p.2) *
          Real.exp (-((F (t * p.1, t ^ 2 * p.2) - F (0, 0)) / t ^ 2)) else 0)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0)))
 := by
  let mu : Measure (ℝ × ℝ) :=
    (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0))
  let S : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ |t * p.1| ≤ rho ∧ t ^ 2 * p.2 ≤ rho}
  let T : (ℝ × ℝ) → (ℝ × ℝ) := fun p => (t * p.1, t ^ 2 * p.2)
  let H : (ℝ × ℝ) → ℝ := fun p =>
    A (T p) * Real.exp (-((F (T p) - F (0, 0)) / t ^ 2))
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_const measurable_snd).inter
      ((measurableSet_le (show Measurable (fun p : ℝ × ℝ => |t * p.1|) from
        (show Continuous (fun p : ℝ × ℝ => |t * p.1|) from by fun_prop).measurable) measurable_const).inter
        (measurableSet_le (measurable_const.mul measurable_snd) measurable_const))
  have hT : Continuous T := by dsimp [T]; fun_prop
  have hmap : Set.MapsTo T S
      {w : ℝ × ℝ | |w.1| ≤ rho ∧ 0 ≤ w.2 ∧ w.2 ≤ rho} := by
    intro p hp
    exact ⟨hp.2.1, mul_nonneg (sq_nonneg t) hp.1, hp.2.2⟩
  have hH : ContinuousOn H S :=
    (hA.comp hT.continuousOn hmap).mul
      (Real.continuous_exp.comp_continuousOn
        (((hF.comp hT.continuousOn hmap).sub continuousOn_const).div_const (t ^ 2)).neg)
  have hI : AEStronglyMeasurable (S.indicator H) mu :=
    (aestronglyMeasurable_indicator_iff hS).mpr (hH.aestronglyMeasurable hS)
  have hvAE : ∀ᵐ p : ℝ × ℝ ∂mu, 0 ≤ p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le measurable_const measurable_snd)).mpr
    exact Filter.Eventually.of_forall fun _ => ae_restrict_mem measurableSet_Ici
  refine hI.congr ?_
  filter_upwards [hvAE] with p hp
  by_cases hc : |t * p.1| ≤ rho ∧ t ^ 2 * p.2 ≤ rho
  · simp [S, H, T, Set.indicator, hp, hc]
  · have hn : p ∉ S := by simpa only [S, Set.mem_setOf_eq, hp, true_and] using hc
    simp only [Set.indicator_of_notMem hn, if_neg hc]

theorem exists_boundary_continuous_cutoff_window
    (F A : (ℝ × ℝ) → ℝ)
    (hF : ContDiffAt ℝ 1 F (0, 0)) (hA : ContDiffAt ℝ 1 A (0, 0))
    (Q : (ℝ × ℝ) → Prop) (hQ : ∀ᶠ w in 𝓝 (0, 0), Q w)
    (rho0 : ℝ) (hrho0 : 0 < rho0) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ rho0 ∧
      (∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho → Q (r, z)) ∧
      ContinuousOn F {w : ℝ × ℝ | |w.1| ≤ rho ∧ 0 ≤ w.2 ∧ w.2 ≤ rho} ∧
      ContinuousOn A {w : ℝ × ℝ | |w.1| ≤ rho ∧ 0 ≤ w.2 ∧ w.2 ≤ rho} ∧
      ∀ t : ℝ, AEStronglyMeasurable (fun p : ℝ × ℝ =>
        if |t * p.1| ≤ rho ∧ t ^ 2 * p.2 ≤ rho then
          A (t * p.1, t ^ 2 * p.2) *
            Real.exp (-((F (t * p.1, t ^ 2 * p.2) - F (0, 0)) / t ^ 2)) else 0)
        ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0))) := by
  have hnear : ∀ᶠ w in 𝓝 (0, 0), ContinuousAt F w ∧ ContinuousAt A w ∧ Q w := by
    filter_upwards [hF.eventually (by norm_num), hA.eventually (by norm_num), hQ] with w hf ha hq
    exact ⟨hf.continuousAt, ha.continuousAt, hq⟩
  obtain ⟨delta, hdelta, hpoint⟩ := Metric.eventually_nhds_iff.mp hnear
  let rho : ℝ := min rho0 (delta / 2)
  have hrho : 0 < rho := lt_min hrho0 (by linarith)
  have hrect : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      ContinuousAt F (r, z) ∧ ContinuousAt A (r, z) ∧ Q (r, z) := by
    intro r z hr hz hzr
    apply hpoint
    rw [show (0, 0) = (0 : ℝ × ℝ) from rfl, dist_zero_right, Prod.norm_def,
      Real.norm_eq_abs, Real.norm_eq_abs, max_lt_iff]
    have hrd : rho ≤ delta / 2 := min_le_right _ _
    exact ⟨by linarith, by rw [abs_of_nonneg hz]; linarith⟩
  have hFc : ContinuousOn F {w : ℝ × ℝ | |w.1| ≤ rho ∧ 0 ≤ w.2 ∧ w.2 ≤ rho} := by
    intro w hw
    exact (hrect w.1 w.2 hw.1 hw.2.1 hw.2.2).1.continuousWithinAt
  have hAc : ContinuousOn A {w : ℝ × ℝ | |w.1| ≤ rho ∧ 0 ≤ w.2 ∧ w.2 ≤ rho} := by
    intro w hw
    exact (hrect w.1 w.2 hw.1 hw.2.1 hw.2.2).2.1.continuousWithinAt
  refine ⟨rho, hrho, min_le_left _ _, ?_, hFc, hAc, ?_⟩
  · intro r z hr hz hzr
    exact (hrect r z hr hz hzr).2.2
  · intro t
    exact boundary_laplace_cutoff_aestronglyMeasurable_of_continuousOn F A rho t hFc hAc

end
end Shao.OQ3
