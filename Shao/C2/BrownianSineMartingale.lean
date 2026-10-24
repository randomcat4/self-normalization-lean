import Shao.C2.IntervalSineGaussianAction

noncomputable section
namespace Shao.C2.BrownianSineMartingale
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
open Shao.C2.BridgeDomination Shao.C2.IntervalSineTerms Shao.C2.IntervalSineSeries
open Shao.C2.IntervalSpectralGaussian Shao.C2.IntervalSineGaussianAction
open Shao.C2.BrownianPathWeakMarkov Shao.OQ4.PolygonalBrownianWeakLimit

private theorem sineSeries_measurable_bounded (a z H : ℝ) (ha : 0 < a) (hH : 0 < H) :
    Measurable (mixedSineSeries 0 0 a z H) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |mixedSineSeries 0 0 a z H x| ≤ M := by
  have hc : Continuous (mixedSineSeries 0 0 a z H) :=
    continuous_iff_continuousAt.mpr fun x =>
      (mixedSineSeries_spatial_hasDerivAt 0 0 a z H x ha hH).continuousAt
  let M := (1 / a) * ∑' n : ℕ, weightedGaussian (Real.pi ^ 2 / 8) 0 (H / a ^ 2) n
  have hb (x : ℝ) : |mixedSineSeries 0 0 a z H x| ≤ M := by
    simpa only [Real.norm_eq_abs, pow_zero, Nat.cast_zero, mul_zero, zero_add,
      one_mul, mul_one] using mixedSineSeries_weighted_bound 0 0 a z H x ha hH
  exact ⟨hc.measurable, M, (abs_nonneg _).trans (hb 0), hb⟩

theorem brownian_increment_past_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T S : ℝ≥0) :
    HasLaw (fun ω => (B (T + S) ω - B T ω, brownianUnitPath B T ω))
      ((gaussianReal 0 S).prod (brownianUnitPathLaw B T P)) P := by
  let C : ℝ≥0 → Ω → ℝ := fun u ω => B (T + u) ω - B T ω
  have hC : IsBrownianReal C P := hB.shift T
  have hInc : HasLaw (fun ω => B (T + S) ω - B T ω) (gaussianReal 0 S) P :=
    hC.toIsPreBrownianReal.hasLaw_eval S
  have hPast : HasLaw (brownianUnitPath B T) (brownianUnitPathLaw B T P) P :=
    { aemeasurable := aemeasurable_brownianUnitPath B T P hB, map_eq := rfl }
  have hInd : IndepFun (fun ω => brownianUnitPath C S ω 1) (brownianUnitPath B T) P := by
    simpa only [Function.comp_def, id_eq] using
      (indepFun_shifted_unitPath B P hB T S).comp
        (ContinuousMap.measurable_eval (1 : BridgeTime)) measurable_id
  have heq : (fun ω => brownianUnitPath C S ω 1) =ᵐ[P]
      (fun ω => B (T + S) ω - B T ω) := by
    filter_upwards [ae_brownianUnitPath_eq C S P hC] with ω hp
    calc
      _ = C (S * 1) ω := hp 1
      _ = _ := by rw [mul_one]
  exact (indepFun_iff_hasLaw_prodMk_prod hInc hPast).mp
    (hInd.congr heq (Eventually.of_forall fun _ => rfl))

theorem brownian_sine_backward_weighted {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a z H y : ℝ) (ha : 0 < a) (hH : 0 < H)
    (T S : ℝ≥0) (F : C(BridgeTime, ℝ) → ℝ) (hF : Measurable F)
    (hbound : ∃ M : ℝ, ∀ p, |F p| ≤ M) :
    Integrable (fun ω => F (brownianUnitPath B T ω) *
      mixedSineSeries 0 0 a z H (y + B (T + S) ω)) P ∧
    Integrable (fun ω => F (brownianUnitPath B T ω) *
      mixedSineSeries 0 0 a z (H + (S : ℝ)) (y + B T ω)) P ∧
    (∫ ω, F (brownianUnitPath B T ω) * mixedSineSeries 0 0 a z H (y + B (T + S) ω) ∂P) =
      ∫ ω, F (brownianUnitPath B T ω) * mixedSineSeries 0 0 a z (H + (S : ℝ)) (y + B T ω) ∂P := by
  let μ := brownianUnitPathLaw B T P
  let V := brownianUnitPath B T
  let Q : ℝ × C(BridgeTime, ℝ) → ℝ := fun q =>
    F q.2 * mixedSineSeries 0 0 a z H (y + q.2 1 + q.1)
  rcases sineSeries_measurable_bounded a z H ha hH with ⟨hu, M, hM0, hU⟩
  have hHS : 0 < H + (S : ℝ) := add_pos_of_pos_of_nonneg hH S.property
  rcases sineSeries_measurable_bounded a z (H + (S : ℝ)) ha hHS with ⟨huS, M', hM'0, hU'⟩
  obtain ⟨N, hN⟩ := hbound
  have hN0 : 0 ≤ N := (abs_nonneg (F 0)).trans (hN 0)
  have hVA : AEMeasurable V P := aemeasurable_brownianUnitPath B T P hB
  have hFV : AEMeasurable (fun ω => F (V ω)) P := hF.comp_aemeasurable hVA
  have hY (t : ℝ≥0) : AEMeasurable (fun ω => y + B t ω) P :=
    aemeasurable_const.add (hB.toIsPreBrownianReal.aemeasurable t)
  have hiL : Integrable (fun ω => F (V ω) * mixedSineSeries 0 0 a z H (y + B (T + S) ω)) P := by
    apply Integrable.of_bound (hFV.mul (hu.comp_aemeasurable (hY (T + S)))).aestronglyMeasurable (N * M)
    exact Eventually.of_forall fun ω => by
      change ‖F (V ω) * mixedSineSeries 0 0 a z H (y + B (T + S) ω)‖ ≤ N * M
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hN (V ω)) (hU _) (abs_nonneg _) hN0
  have hiR : Integrable (fun ω => F (V ω) * mixedSineSeries 0 0 a z (H + (S : ℝ)) (y + B T ω)) P := by
    apply Integrable.of_bound (hFV.mul (huS.comp_aemeasurable (hY T))).aestronglyMeasurable (N * M')
    exact Eventually.of_forall fun ω => by
      change ‖F (V ω) * mixedSineSeries 0 0 a z (H + (S : ℝ)) (y + B T ω)‖ ≤ N * M'
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hN (V ω)) (hU' _) (abs_nonneg _) hN0
  refine ⟨hiL, hiR, ?_⟩
  have hPast : HasLaw V μ P := { aemeasurable := hVA, map_eq := rfl }
  have hLaw := brownian_increment_past_hasLaw B P hB T S
  letI : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hVA).mpr inferInstance
  have heval : Measurable (fun q : ℝ × C(BridgeTime, ℝ) => y + q.2 1 + q.1) :=
    (measurable_const.add ((ContinuousMap.measurable_eval (1 : BridgeTime)).comp measurable_snd)).add measurable_fst
  have hQ : Measurable Q := (hF.comp measurable_snd).mul (hu.comp heval)
  have hQi : Integrable Q ((gaussianReal 0 S).prod μ) := by
    apply Integrable.of_bound hQ.aestronglyMeasurable (N * M)
    exact Eventually.of_forall fun q => by
      change ‖F q.2 * mixedSineSeries 0 0 a z H (y + q.2 1 + q.1)‖ ≤ N * M
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hN q.2) (hU _) (abs_nonneg _) hN0
  have hR : Measurable (fun p : C(BridgeTime, ℝ) => F p *
      mixedSineSeries 0 0 a z (H + (S : ℝ)) (y + p 1)) :=
    hF.mul (huS.comp (measurable_const.add (ContinuousMap.measurable_eval (1 : BridgeTime))))
  have hEnd : ∀ᵐ ω ∂P, V ω 1 = B T ω := by
    filter_upwards [ae_brownianUnitPath_eq B T P hB] with ω hp
    calc
      _ = B (T * 1) ω := hp 1
      _ = _ := by rw [mul_one]
  calc
    _ = ∫ ω, Q (B (T + S) ω - B T ω, V ω) ∂P := by
      apply integral_congr_ae
      filter_upwards [hEnd] with ω hp
      change F (V ω) * mixedSineSeries 0 0 a z H (y + B (T + S) ω) =
        F (V ω) * mixedSineSeries 0 0 a z H (y + V ω 1 + (B (T + S) ω - B T ω))
      rw [hp]
      congr 2
      ring
    _ = ∫ q, Q q ∂(gaussianReal 0 S).prod μ := hLaw.integral_comp hQ.aestronglyMeasurable
    _ = ∫ p : C(BridgeTime, ℝ), ∫ x : ℝ, Q (x, p) ∂gaussianReal 0 S ∂μ := integral_prod_symm Q hQi
    _ = ∫ p : C(BridgeTime, ℝ), F p * mixedSineSeries 0 0 a z (H + (S : ℝ)) (y + p 1) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        change (∫ x : ℝ, F p * mixedSineSeries 0 0 a z H ((y + p 1) + x) ∂gaussianReal 0 S) = _
        rw [integral_const_mul, (sineSeries_gaussian_action a z H (y + p 1) ha hH S).2]
    _ = ∫ ω, F (V ω) * mixedSineSeries 0 0 a z (H + (S : ℝ)) (y + V ω 1) ∂P :=
      (hPast.integral_comp hR.aestronglyMeasurable).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hEnd] with ω hp
      change F (V ω) * mixedSineSeries 0 0 a z (H + (S : ℝ)) (y + V ω 1) = _
      rw [hp]

end Shao.C2.BrownianSineMartingale
