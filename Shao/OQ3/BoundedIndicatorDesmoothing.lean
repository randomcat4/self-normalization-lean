import Shao.OQ3.IndependentSumTestOscillation
import Shao.OQ3.BoundedDensityGaussianComparison

namespace Shao.OQ3
open MeasureTheory
noncomputable section

theorem indicator_open_ball_oscillation_support_bound
    (A : Set (ℝ × ℝ)) (g : (ℝ × ℝ) → ℝ) (R h : ℝ)
    (hA : ∀ u ∈ A, ‖u‖ ≤ R) (z : ℝ × ℝ) (hz : R + h < ‖z‖) :
    openBallOscillation (A.indicator g) h z = 0 := by
  classical
  have hzero (u : ℝ × ℝ) (hu : u ∈ Metric.ball z h) : A.indicator g u = 0 := by
    have huA : u ∉ A := by
      intro huA
      have hbound := hA u huA
      have hd : dist z u < h := by simpa only [Metric.mem_ball, dist_comm] using hu
      have htri : ‖z‖ ≤ dist z u + ‖u‖ := by
        simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - u) u
      linarith
    exact Set.indicator_of_notMem huA _
  let S : Set ℝ := insert 0 {r : ℝ | ∃ u ∈ Metric.ball z h, ∃ v ∈ Metric.ball z h,
    r = |A.indicator g u - A.indicator g v|}
  have hupper (r : ℝ) (hr : r ∈ S) : r ≤ 0 := by
    rcases Set.mem_insert_iff.mp hr with rfl | hr
    · exact le_rfl
    · obtain ⟨u, hu, v, hv, rfl⟩ := hr
      rw [hzero u hu, hzero v hv, sub_self, abs_zero]
  change sSup S = 0
  exact le_antisymm (csSup_le ⟨0, Set.mem_insert _ _⟩ hupper)
    (le_csSup ⟨0, hupper⟩ (Set.mem_insert _ _))

theorem bounded_density_indicator_desmoothing_bound
    (nu eta : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu] [IsProbabilityMeasure eta]
    (A : Set (ℝ × ℝ)) (hAm : MeasurableSet A)
    (g : (ℝ × ℝ) → ℝ) (hg : Measurable g)
    (C R h K : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) (hh : 0 < h) (hK : 0 ≤ K)
    (hbound : ∀ u ∈ A, |g u| ≤ C) (hA : ∀ u ∈ A, ‖u‖ ≤ R) :
    let f : (ℝ × ℝ) → ℝ := A.indicator g
    let rho : Measure (ℝ × ℝ) := (nu.prod eta).map (fun q => q.1 + q.2)
    ∀ k : (ℝ × ℝ) → ℝ, Measurable k →
      (∀ z : ℝ × ℝ, 0 ≤ k z ∧ k z ≤ K) →
      rho = volume.withDensity (fun z => ENNReal.ofReal (k z)) →
      let Phi : Measure (ℝ × ℝ) :=
        (ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1)
      IsProbabilityMeasure rho ∧ Integrable f nu ∧ Integrable f rho ∧
        Integrable (openBallOscillation f h) rho ∧
          Integrable (openBallOscillation f h) Phi ∧
            |(∫ z : ℝ × ℝ, f z ∂rho) - (∫ z : ℝ × ℝ, f z ∂nu)| ≤
              ((2 * Real.pi) * K * Real.exp ((R + h) ^ 2)) *
                (∫ z : ℝ × ℝ, openBallOscillation f h z ∂Phi) +
                  2 * C * eta.real {d : ℝ × ℝ | h / 2 < ‖d‖} := by
  classical
  intro f rho k hk hkbound hrho Phi
  have hf : Measurable f := hg.indicator hAm
  have hfBound (z : ℝ × ℝ) : |f z| ≤ C := by
    by_cases hz : z ∈ A
    · exact (show |A.indicator g z| ≤ C by simpa only [Set.indicator_of_mem hz] using hbound z hz)
    · change |A.indicator g z| ≤ C
      rw [Set.indicator_of_notMem hz, abs_zero]
      exact hC
  have hcpl := independent_sum_bounded_test_oscillation_bound nu eta f hf C h hC hh hfBound
  letI : IsProbabilityMeasure rho := hcpl.1
  obtain ⟨hsize, hpair, hopen, hmeas⟩ := open_ball_oscillation_properties f C h hC hfBound
  have hz (z : ℝ × ℝ) (hzz : R + h < ‖z‖) : openBallOscillation f h z = 0 :=
    indicator_open_ball_oscillation_support_bound A g R h hA z hzz
  have hcomparison := bounded_density_compact_test_gaussian_comparison rho k hk
    (fun z => (hkbound z).1) hrho K (R + h) (2 * C) hK (by linarith) (by positivity)
    (fun z => (hkbound z).2) (openBallOscillation f h) hmeas
    (fun z => (hsize z).1) (fun z => (hsize z).2) hz
  refine ⟨hcpl.1, hcpl.2.1, hcpl.2.2.1, hcpl.2.2.2.1, hcomparison.2.1, ?_⟩
  exact hcpl.2.2.2.2.trans (add_le_add hcomparison.2.2 le_rfl)

end
end Shao.OQ3
