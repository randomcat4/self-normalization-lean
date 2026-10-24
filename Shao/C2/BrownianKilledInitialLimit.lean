import Shao.C2.BrownianKilledDensitySemigroup
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
namespace Shao.C2.BrownianKilledInitialLimit
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw Shao.C2.ScaledBrownianIdentity
open Shao.C2.BrownianKilledKernel Shao.C2.BrownianKilledAction
open Shao.C2.BrownianBridgeProductKernel

theorem actualIntervalKernel_action_bridgeProduct {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y : ℝ) (T : ℝ≥0) (hT : T ≠ 0)
    (f : ℝ → ℝ) (hf : Measurable f) (hbound : ∃ M : ℝ, ∀ z, |f z| ≤ M) :
    Integrable f (actualIntervalKernel B P a T y) ∧
      Integrable ((scaledInitialSurvival a y (T : ℝ)).indicator
        (fun p : BridgeNoise × ℝ => f (y + Real.sqrt (T : ℝ) * p.2)))
        ((bridgeLaw B P).prod (gaussianReal 0 1)) ∧
      (∫ z : ℝ, f z ∂actualIntervalKernel B P a T y) =
        ∫ p : BridgeNoise × ℝ, (scaledInitialSurvival a y (T : ℝ)).indicator
          (fun p => f (y + Real.sqrt (T : ℝ) * p.2)) p
          ∂((bridgeLaw B P).prod (gaussianReal 0 1)) := by
  let ρ := (bridgeLaw B P).prod (gaussianReal 0 1)
  let g : BridgeNoise × ℝ → ℝ := fun p => f (y + Real.sqrt (T : ℝ) * p.2)
  letI : IsProbabilityMeasure (bridgeLaw B P) := isProbabilityMeasure_bridgeLaw B P hB
  have hE : Measurable (fun p : BridgeNoise × ℝ => y + Real.sqrt (T : ℝ) * p.2) := by fun_prop
  have hg : Measurable g := hf.comp hE
  obtain ⟨M, hM⟩ := hbound
  have hgi : Integrable g ρ := by
    apply Integrable.of_bound hg.aestronglyMeasurable M
    exact Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hM (y + Real.sqrt (T : ℝ) * p.2)
  have hsurv := measurableSet_scaledInitialSurvival a y (T : ℝ)
  refine ⟨(actualIntervalKernel_action_bounded B P hB a y T hT f hf ⟨M, hM⟩).1,
    hgi.indicator hsurv, ?_⟩
  calc
    _ = ∫ p in scaledInitialSurvival a y (T : ℝ), g p ∂ρ := by
      rw [actualIntervalKernel_eq_bridgeProductEndpointMeasure B P hB a y T hT,
        bridgeProductEndpointMeasure]
      exact integral_map hE.aemeasurable hf.aestronglyMeasurable
    _ = _ := (integral_indicator hsurv).symm

private theorem bridgeProduct_initial_pointwise (a y : ℝ) (hy : |y| < a)
    (f : ℝ → ℝ) (hf : Continuous f) (p : BridgeNoise × ℝ) :
    Tendsto (fun T : ℝ≥0 => (scaledInitialSurvival a y (T : ℝ)).indicator
      (fun q : BridgeNoise × ℝ => f (y + Real.sqrt (T : ℝ) * q.2)) p)
      (𝓝 0) (𝓝 (f y)) := by
  let L : ℝ≥0 → C(BridgeTime, ℝ) := fun T =>
    y • leftWeight + (y + Real.sqrt (T : ℝ) * p.2) • rightWeight +
      Real.sqrt (T : ℝ) • p.1.val
  have hs : Continuous (fun T : ℝ≥0 => Real.sqrt (T : ℝ)) :=
    Real.continuous_sqrt.comp NNReal.continuous_coe
  have hL : Continuous L :=
    (continuous_const.add ((continuous_const.add (hs.mul continuous_const)).smul continuous_const)).add
      (hs.smul continuous_const)
  have hL0 : L 0 = ContinuousMap.const BridgeTime y := by
    ext t
    simp only [L, NNReal.coe_zero, Real.sqrt_zero, zero_mul, add_zero, zero_smul,
      ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul,
      leftWeight, rightWeight, ContinuousMap.coe_mk, ContinuousMap.const_apply]
    ring
  have hn : ‖L 0‖ < a := by
    rw [hL0]
    rw [ContinuousMap.norm_lt_iff_of_nonempty]
    intro t
    simpa only [ContinuousMap.const_apply, Real.norm_eq_abs] using hy
  have hev : ∀ᶠ T : ℝ≥0 in 𝓝 0, p ∈ scaledInitialSurvival a y (T : ℝ) :=
    (isOpen_lt hL.norm continuous_const).mem_nhds hn
  have hc : Continuous (fun T : ℝ≥0 => f (y + Real.sqrt (T : ℝ) * p.2)) :=
    hf.comp (continuous_const.add (hs.mul continuous_const))
  have ht : Tendsto (fun T : ℝ≥0 => f (y + Real.sqrt (T : ℝ) * p.2)) (𝓝 0) (𝓝 (f y)) := by
    simpa only [NNReal.coe_zero, Real.sqrt_zero, zero_mul, add_zero] using hc.tendsto 0
  apply ht.congr'
  filter_upwards [hev] with T hT
  rw [Set.indicator_of_mem hT]

theorem actualIntervalKernel_initial_limit {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y : ℝ) (hy : |y| < a)
    (f : ℝ → ℝ) (hf : Continuous f) (hbound : ∃ M : ℝ, ∀ z, |f z| ≤ M) :
    Tendsto (fun T : ℝ≥0 => ∫ z : ℝ, f z ∂actualIntervalKernel B P a T y)
      (𝓝[>] 0) (𝓝 (f y)) := by
  let ρ := (bridgeLaw B P).prod (gaussianReal 0 1)
  let G : ℝ≥0 → BridgeNoise × ℝ → ℝ := fun T =>
    (scaledInitialSurvival a y (T : ℝ)).indicator
      (fun p => f (y + Real.sqrt (T : ℝ) * p.2))
  letI : IsProbabilityMeasure (bridgeLaw B P) := isProbabilityMeasure_bridgeLaw B P hB
  obtain ⟨M, hM⟩ := hbound
  have hM0 : 0 ≤ M := (abs_nonneg (f 0)).trans (hM 0)
  have hG (T : ℝ≥0) : Measurable (G T) :=
    (hf.measurable.comp (by fun_prop)).indicator (measurableSet_scaledInitialSurvival a y (T : ℝ))
  have hb : ∀ T : ℝ≥0, ∀ᵐ p ∂ρ, ‖G T p‖ ≤ M := by
    intro T
    exact Eventually.of_forall fun p => by
      by_cases hp : p ∈ scaledInitialSurvival a y (T : ℝ)
      · simpa only [G, Set.indicator_of_mem hp, Real.norm_eq_abs] using hM (y + Real.sqrt (T : ℝ) * p.2)
      · simpa only [G, Set.indicator_of_notMem hp, norm_zero] using hM0
  have hlim : ∀ᵐ p ∂ρ, Tendsto (fun T : ℝ≥0 => G T p) (𝓝[>] 0) (𝓝 (f y)) :=
    Eventually.of_forall fun p => (bridgeProduct_initial_pointwise a y hy f hf p).mono_left inf_le_left
  have hd := tendsto_integral_filter_of_dominated_convergence (μ := ρ) (l := 𝓝[>] (0 : ℝ≥0))
    (fun _ => M) (Eventually.of_forall fun T => (hG T).aestronglyMeasurable)
    (Eventually.of_forall hb) (integrable_const M) hlim
  have hd' : Tendsto (fun T : ℝ≥0 => ∫ p, G T p ∂ρ) (𝓝[>] 0) (𝓝 (f y)) := by
    simpa using hd
  apply hd'.congr'
  filter_upwards [self_mem_nhdsWithin] with T hT
  exact (actualIntervalKernel_action_bridgeProduct B P hB a y T (ne_of_gt hT)
    f hf.measurable ⟨M, hM⟩).2.2.symm

end Shao.C2.BrownianKilledInitialLimit
