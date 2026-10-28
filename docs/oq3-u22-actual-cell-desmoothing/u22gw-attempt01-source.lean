import Shao.OQ3.OpenBallOscillation
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real

namespace Shao.OQ3
open MeasureTheory
noncomputable section

theorem independent_sum_bounded_test_oscillation_bound
    (nu eta : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu] [IsProbabilityMeasure eta]
    (f : (ℝ × ℝ) → ℝ) (hf : Measurable f) (C h : ℝ)
    (hC : 0 ≤ C) (hh : 0 < h) (hbound : ∀ z : ℝ × ℝ, |f z| ≤ C) :
    let rho : Measure (ℝ × ℝ) := (nu.prod eta).map (fun q => q.1 + q.2)
    IsProbabilityMeasure rho ∧ Integrable f nu ∧ Integrable f rho ∧
      Integrable (openBallOscillation f h) rho ∧
      |(∫ z : ℝ × ℝ, f z ∂rho) - (∫ z : ℝ × ℝ, f z ∂nu)| ≤
        (∫ z : ℝ × ℝ, openBallOscillation f h z ∂rho) +
          2 * C * eta.real {d : ℝ × ℝ | h / 2 < ‖d‖} := by
  classical
  intro rho
  have hm : Measurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => q.1 + q.2) := by fun_prop
  have hrho : IsProbabilityMeasure rho := by dsimp only [rho]; infer_instance
  letI : IsProbabilityMeasure rho := hrho
  have hInt {alpha : Type*} [MeasurableSpace alpha]
      (m : Measure alpha) [IsProbabilityMeasure m] (g : alpha → ℝ)
      (hg : Measurable g) (B : ℝ) (hgB : ∀ z, |g z| ≤ B) : Integrable g m := by
    apply (integrable_const B).mono' hg.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hgB z)
  have hnu : Integrable f nu := hInt nu f hf C hbound
  have hRho : Integrable f rho := hInt rho f hf C hbound
  obtain ⟨hsize, hpair, hopen, hmeas⟩ := open_ball_oscillation_properties f C h hC hbound
  have hOi : Integrable (openBallOscillation f h) rho :=
    open_ball_oscillation_integrable rho f C h hC hbound
  refine ⟨hrho, hnu, hRho, hOi, ?_⟩
  let F : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ := fun q => f (q.1 + q.2)
  let O : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ := fun q => openBallOscillation f h (q.1 + q.2)
  let B : Set (ℝ × ℝ) := {d | h / 2 < ‖d‖}
  let e : (ℝ × ℝ) → ℝ := B.indicator (fun _ => 2 * C)
  have hB : MeasurableSet B := by
    dsimp only [B]
    exact isOpen_lt continuous_const continuous_norm |>.measurableSet
  have he0 (d : ℝ × ℝ) : 0 ≤ e d := by
    by_cases hd : d ∈ B
    · simp only [e, Set.indicator_of_mem hd]; positivity
    · simp only [e, Set.indicator_of_not_mem hd]; exact le_rfl
  have heBound (d : ℝ × ℝ) : |e d| ≤ 2 * C := by
    rw [abs_of_nonneg (he0 d)]
    by_cases hd : d ∈ B
    · simp only [e, Set.indicator_of_mem hd]; exact le_rfl
    · simp only [e, Set.indicator_of_not_mem hd]; positivity
  have hiF : Integrable F (nu.prod eta) :=
    hInt (nu.prod eta) F (hf.comp hm) C (fun q => hbound (q.1 + q.2))
  have hiFst : Integrable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => f q.1) (nu.prod eta) :=
    hInt (nu.prod eta) _ (hf.comp measurable_fst) C (fun q => hbound q.1)
  have hiO : Integrable O (nu.prod eta) :=
    hInt (nu.prod eta) O (hmeas.comp hm) (2 * C) (fun q => by
      rw [abs_of_nonneg (hsize (q.1 + q.2)).1]
      exact (hsize (q.1 + q.2)).2)
  have hme : Measurable e := measurable_const.indicator hB
  have hiE : Integrable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => e q.2) (nu.prod eta) :=
    hInt (nu.prod eta) _ (hme.comp measurable_snd) (2 * C) (fun q => heBound q.2)
  have hdom (q : (ℝ × ℝ) × (ℝ × ℝ)) : |F q - f q.1| ≤ O q + e q.2 := by
    by_cases hd : q.2 ∈ B
    · have htri : |f (q.1 + q.2) - f q.1| ≤ |f (q.1 + q.2)| + |f q.1| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (f (q.1 + q.2)) (-f q.1)
      have ho0 := (hsize (q.1 + q.2)).1
      change |f (q.1 + q.2) - f q.1| ≤ openBallOscillation f h (q.1 + q.2) + e q.2
      rw [show e q.2 = 2 * C by exact Set.indicator_of_mem hd _]
      linarith [hbound (q.1 + q.2), hbound q.1]
    · have hgood : ‖q.2‖ ≤ h / 2 := le_of_not_gt hd
      have hu : q.1 + q.2 ∈ Metric.ball (q.1 + q.2) h := Metric.mem_ball_self hh
      have hv : q.1 ∈ Metric.ball (q.1 + q.2) h := by
        change dist q.1 (q.1 + q.2) < h
        rw [dist_eq_norm, show q.1 - (q.1 + q.2) = -q.2 by abel, norm_neg]
        linarith
      have hp := hpair (q.1 + q.2) (q.1 + q.2) hu q.1 hv
      simpa only [F, O, e, Set.indicator_of_not_mem hd, add_zero] using hp
  have hmap : (∫ z : ℝ × ℝ, f z ∂rho) = ∫ q, F q ∂nu.prod eta :=
    integral_map_of_stronglyMeasurable hm hf.stronglyMeasurable
  have hOmap : (∫ z : ℝ × ℝ, openBallOscillation f h z ∂rho) =
      ∫ q, O q ∂nu.prod eta :=
    integral_map_of_stronglyMeasurable hm hmeas.stronglyMeasurable
  have hfstVal : (∫ q : (ℝ × ℝ) × (ℝ × ℝ), f q.1 ∂nu.prod eta) =
      ∫ z : ℝ × ℝ, f z ∂nu := by
    rw [integral_prod _ hiFst]
    simp
  have hEVal : (∫ q : (ℝ × ℝ) × (ℝ × ℝ), e q.2 ∂nu.prod eta) = 2 * C * eta.real B := by
    rw [integral_prod _ hiE]
    simp only [integral_const, measureReal_univ_eq_one, one_smul]
    dsimp only [e]
    rw [integral_indicator hB, setIntegral_const, smul_eq_mul]
    ring
  have hMain : |(∫ q, F q ∂nu.prod eta) -
      (∫ q : (ℝ × ℝ) × (ℝ × ℝ), f q.1 ∂nu.prod eta)| ≤
        (∫ q, O q ∂nu.prod eta) + (∫ q : (ℝ × ℝ) × (ℝ × ℝ), e q.2 ∂nu.prod eta) := by
    calc
      _ = ‖∫ q : (ℝ × ℝ) × (ℝ × ℝ), F q - f q.1 ∂nu.prod eta‖ := by
        rw [integral_sub hiF hiFst, Real.norm_eq_abs]
      _ ≤ ∫ q : (ℝ × ℝ) × (ℝ × ℝ), ‖F q - f q.1‖ ∂nu.prod eta :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ q : (ℝ × ℝ) × (ℝ × ℝ), (O q + e q.2) ∂nu.prod eta := by
        apply integral_mono (hiF.sub hiFst).norm (hiO.add hiE)
        intro q
        change ‖F q - f q.1‖ ≤ O q + e q.2
        rw [Real.norm_eq_abs]
        exact hdom q
      _ = _ := integral_add hiO hiE
  calc
    _ = |(∫ q, F q ∂nu.prod eta) -
        (∫ q : (ℝ × ℝ) × (ℝ × ℝ), f q.1 ∂nu.prod eta)| := by rw [hmap, hfstVal]
    _ ≤ (∫ q, O q ∂nu.prod eta) + (∫ q : (ℝ × ℝ) × (ℝ × ℝ), e q.2 ∂nu.prod eta) := hMain
    _ = _ := by rw [← hOmap, hEVal]

end
end Shao.OQ3
