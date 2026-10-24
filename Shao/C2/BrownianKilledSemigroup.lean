import Shao.C2.BrownianSurvivalSplit

noncomputable section
namespace Shao.C2.BrownianKilledSemigroup
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.BrownianKilledKernel Shao.C2.BrownianKilledAction
open Shao.C2.BrownianBridgeProductKernel Shao.C2.BrownianSurvivalSplit
open Shao.OQ4.PolygonalBrownianWeakLimit

private theorem product_real_section {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsFiniteMeasure μ] (ν : Measure β) [IsFiniteMeasure ν]
    (E : Set (α × β)) (hE : MeasurableSet E) :
    (μ.prod ν).real E = ∫ b : β, μ.real {a | (a, b) ∈ E} ∂ν := by
  let F : α × β → ℝ := E.indicator (fun _ => 1)
  have hF : Integrable F (μ.prod ν) := (integrable_const 1).indicator hE
  calc
    (μ.prod ν).real E = ∫ p, F p ∂μ.prod ν := (integral_indicator_one hE).symm
    _ = ∫ b : β, ∫ a : α, F (a, b) ∂μ ∂ν := integral_prod_symm F hF
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun b => by
        have hsec : MeasurableSet {a : α | (a, b) ∈ E} :=
          hE.preimage (measurable_id.prodMk measurable_const)
        change (∫ a, ({a : α | (a, b) ∈ E}).indicator (fun _ => (1 : ℝ)) a ∂μ) = _
        exact integral_indicator_one hsec

private theorem physical_survival_ae_unitPath {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y : ℝ) (T : ℝ≥0) (hT : T ≠ 0) :
    {ω | ∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a} =ᵐ[P]
      (brownianUnitPath B T) ⁻¹'
        {p : C(BridgeTime, ℝ) | ‖ContinuousMap.const BridgeTime y + p‖ < a} := by
  have hTpos : 0 < (T : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hT : 0 < T)
  filter_upwards [ae_brownianUnitPath_eq B T P hB] with ω hp
  apply propext
  change (∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a) ↔
    ‖ContinuousMap.const BridgeTime y + brownianUnitPath B T ω‖ < a
  rw [ContinuousMap.norm_lt_iff_of_nonempty]
  have hp' (t : BridgeTime) : brownianUnitPath B T ω t =
      B (T * ⟨(t : ℝ), t.property.1⟩) ω := hp t
  simp only [ContinuousMap.add_apply, ContinuousMap.const_apply, Real.norm_eq_abs, hp']
  constructor
  · intro h t
    apply h
    let u : ℝ≥0 := ⟨(t : ℝ), t.property.1⟩
    change T * u ≤ T
    have hu : u ≤ 1 := by
      apply NNReal.coe_le_coe.mp
      exact t.property.2
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hu (show (0 : ℝ≥0) ≤ T from zero_le)
  · intro h s hsT
    let t : BridgeTime := ⟨(s : ℝ) / (T : ℝ), div_nonneg s.property T.property,
      (div_le_one hTpos).2 (by exact_mod_cast hsT)⟩
    let u : ℝ≥0 := ⟨(t : ℝ), t.property.1⟩
    have heq : T * u = s := by
      apply NNReal.eq
      change (T : ℝ) * ((s : ℝ) / (T : ℝ)) = (s : ℝ)
      field_simp
    have ht := h t
    change |y + B (T * u) ω| < a at ht
    simpa only [heq] using ht

private theorem past_path_restricted_action {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y : ℝ) (T : ℝ≥0) (hT : T ≠ 0)
    (f : ℝ → ℝ) (hf : Measurable f) (hbound : ∃ M : ℝ, ∀ z, |f z| ≤ M) :
    (∫ p : C(BridgeTime, ℝ) in {p | ‖ContinuousMap.const BridgeTime y + p‖ < a},
        f (y + p 1) ∂brownianUnitPathLaw B T P) =
      ∫ z : ℝ, f z ∂actualIntervalKernel B P a T y := by
  let N : Set C(BridgeTime, ℝ) := {p | ‖ContinuousMap.const BridgeTime y + p‖ < a}
  let V : Set Ω := {ω | ∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a}
  have hN : MeasurableSet N :=
    (isOpen_lt (continuous_const.add continuous_id).norm continuous_const).measurableSet
  have heval : Measurable (fun p : C(BridgeTime, ℝ) => y + p 1) :=
    measurable_const.add (ContinuousMap.measurable_eval (1 : BridgeTime))
  have hF : Measurable (fun p : C(BridgeTime, ℝ) => f (y + p 1)) := hf.comp heval
  have hevent : V =ᵐ[P] (brownianUnitPath B T) ⁻¹' N :=
    physical_survival_ae_unitPath B P hB a y T hT
  calc
    _ = ∫ ω in (brownianUnitPath B T) ⁻¹' N, f (y + brownianUnitPath B T ω 1) ∂P :=
      setIntegral_map hN hF.aestronglyMeasurable (aemeasurable_brownianUnitPath B T P hB)
    _ = ∫ ω in V, f (y + B T ω) ∂P := by
      rw [Measure.restrict_congr_set hevent.symm]
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (ae_brownianUnitPath_eq B T P hB)] with ω hp
      have hp1 : brownianUnitPath B T ω 1 = B T ω := by
        calc
          _ = B (T * 1) ω := hp 1
          _ = _ := by rw [mul_one]
      rw [hp1]
    _ = _ := (actualIntervalKernel_action_bounded B P hB a y T hT f hf hbound).2.2.symm

theorem actualIntervalKernel_semigroup_real {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y : ℝ) (T S : ℝ≥0) (hT : T ≠ 0) (hS : S ≠ 0)
    (A : Set ℝ) (hA : MeasurableSet A) :
    Integrable (fun z : ℝ => (actualIntervalKernel B P a S z).real A)
      (actualIntervalKernel B P a T y) ∧
    (actualIntervalKernel B P a (T + S) y).real A =
      ∫ z : ℝ, (actualIntervalKernel B P a S z).real A ∂actualIntervalKernel B P a T y := by
  let ρ := (bridgeLaw B P).prod (gaussianReal 0 1)
  let μ := brownianUnitPathLaw B T P
  let N : Set C(BridgeTime, ℝ) := {p | ‖ContinuousMap.const BridgeTime y + p‖ < a}
  let f : ℝ → ℝ := fun z => (actualIntervalKernel B P a S z).real A
  have hf : Measurable f :=
    ENNReal.measurable_toReal.comp ((actualIntervalKernel B P a S).measurable_coe hA)
  have hbound : ∃ M : ℝ, ∀ z, |f z| ≤ M := by
    refine ⟨1, fun z => ?_⟩
    rw [abs_of_nonneg (show 0 ≤ f z from measureReal_nonneg)]
    dsimp only [f]
    rw [actualIntervalKernel_real_eq_survival B P hB a z S hS A hA]
    exact measureReal_le_one
  have hi := actualIntervalKernel_action_bounded B P hB a y T hT f hf hbound
  refine ⟨hi.1, ?_⟩
  letI : IsProbabilityMeasure (bridgeLaw B P) := isProbabilityMeasure_bridgeLaw B P hB
  letI : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff (aemeasurable_brownianUnitPath B T P hB)).mpr inferInstance
  have hN : MeasurableSet N :=
    (isOpen_lt (continuous_const.add continuous_id).norm continuous_const).measurableSet
  have hTS : T + S ≠ 0 :=
    (add_pos (pos_iff_ne_zero.mpr hT) (pos_iff_ne_zero.mpr hS)).ne'
  calc
    _ = P.real {ω | (∀ s : ℝ≥0, s ≤ T + S → |y + B s ω| < a) ∧
        y + B (T + S) ω ∈ A} :=
      actualIntervalKernel_real_eq_survival B P hB a y (T + S) hTS A hA
    _ = (ρ.prod μ).real (splitSurvivalEvent a y (S : ℝ) A) :=
      brownian_split_event_probability B P hB a y T S hT hS A hA
    _ = ∫ p : C(BridgeTime, ℝ), ρ.real {q | (q, p) ∈ splitSurvivalEvent a y (S : ℝ) A} ∂μ :=
      product_real_section ρ μ _ (measurableSet_splitSurvivalEvent a y (S : ℝ) A hA)
    _ = ∫ p : C(BridgeTime, ℝ), N.indicator (fun p => f (y + p 1)) p ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        change ρ.real {q : BridgeNoise × ℝ | (q, p) ∈ splitSurvivalEvent a y (S : ℝ) A} =
          N.indicator (fun p => f (y + p 1)) p
        by_cases hp : p ∈ N
        · have heq : {q : BridgeNoise × ℝ | (q, p) ∈ splitSurvivalEvent a y (S : ℝ) A} =
              Shao.C2.ScaledBrownianIdentity.scaledInitialSurvival a (y + p 1) (S : ℝ) ∩
                {q | y + p 1 + Real.sqrt (S : ℝ) * q.2 ∈ A} := by
            ext q
            have hp' : ‖ContinuousMap.const BridgeTime y + p‖ < a := hp
            simp only [splitSurvivalEvent, Set.mem_setOf_eq, Set.mem_inter_iff, hp', true_and]
          rw [heq, Set.indicator_of_mem hp]
          exact bridgeProduct_initial_joint_real B P hB a (y + p 1) S hS A hA
        · have heq : {q : BridgeNoise × ℝ | (q, p) ∈ splitSurvivalEvent a y (S : ℝ) A} = ∅ := by
            ext q
            have hp' : ¬ ‖ContinuousMap.const BridgeTime y + p‖ < a := hp
            simp only [splitSurvivalEvent, Set.mem_setOf_eq, hp', false_and, Set.mem_empty_iff_false]
          rw [heq, measureReal_empty, Set.indicator_of_notMem hp]
    _ = ∫ p : C(BridgeTime, ℝ) in N, f (y + p 1) ∂μ := integral_indicator hN
    _ = _ := past_path_restricted_action B P hB a y T hT f hf hbound

end Shao.C2.BrownianKilledSemigroup
