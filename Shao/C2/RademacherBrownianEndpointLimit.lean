import Shao.C2.PolygonalRademacherReflection

noncomputable section
namespace Shao.C2.RademacherBrownianEndpointLimit
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Shao.C2.BridgeDomination Shao.C2.BrownianUpperJointLimit
open Shao.C2.PolygonalPrefixEvents
open Shao.OQ4.PolygonalPathTightness Shao.OQ4.PolygonalBrownianWeakLimit

private theorem ae_unit_eval_one {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, brownianUnitPath B 1 ω 1 = B 1 ω := by
  filter_upwards [ae_brownianUnitPath_eq B 1 P hB] with ω hω
  calc
    _ = B (1 * (1 : ℝ≥0)) ω := hω 1
    _ = B 1 ω := congrArg (fun s : ℝ≥0 => B s ω) (one_mul _)

theorem rademacher_moments :
    Integrable (fun x : ℝ => |x| ^ 3) Shao.OQ4.RademacherCosine.law ∧
      (∫ x : ℝ, x ∂Shao.OQ4.RademacherCosine.law) = 0 ∧
      (∫ x : ℝ, x ^ 2 ∂Shao.OQ4.RademacherCosine.law) = 1 ∧
      (∫ x : ℝ, |x| ^ 3 ∂Shao.OQ4.RademacherCosine.law) = 1 := by
  have hhalf : Shao.OQ4.RademacherCosine.halfENNReal ≠ ⊤ := by
    norm_num [Shao.OQ4.RademacherCosine.halfENNReal]
  have hreal : Shao.OQ4.RademacherCosine.halfENNReal.toReal = (1 / 2 : ℝ) := by
    norm_num [Shao.OQ4.RademacherCosine.halfENNReal, ENNReal.toReal_div]
  have hp (f : ℝ → ℝ) :
      Integrable f (Shao.OQ4.RademacherCosine.halfENNReal • Measure.dirac (1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure hhalf
  have hn (f : ℝ → ℝ) :
      Integrable f (Shao.OQ4.RademacherCosine.halfENNReal • Measure.dirac (-1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure hhalf
  have hi (f : ℝ → ℝ) : Integrable f Shao.OQ4.RademacherCosine.law := by
    rw [Shao.OQ4.RademacherCosine.law]
    exact (hp f).add_measure (hn f)
  have hformula (f : ℝ → ℝ) :
      (∫ x : ℝ, f x ∂Shao.OQ4.RademacherCosine.law) =
        (1 / 2 : ℝ) * f 1 + (1 / 2 : ℝ) * f (-1) := by
    rw [Shao.OQ4.RademacherCosine.law, integral_add_measure (hp f) (hn f),
      integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac, hreal]
    rfl
  refine ⟨hi _, ?_, ?_, ?_⟩
  · norm_num [hformula]
  · norm_num [hformula]
  · norm_num [hformula]

theorem rademacher_pathLaw_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    Tendsto (β := ProbabilityMeasure C(BridgeTime, ℝ)) (fun j : ℕ =>
      (⟨polygonalPathLaw 1 ((j + 1) ^ 2) ((j : ℝ) + 1) Shao.OQ4.RademacherCosine.law,
        isProbabilityMeasure_polygonalPathLaw 1 ((j + 1) ^ 2) ((j : ℝ) + 1)
          Shao.OQ4.RademacherCosine.law⟩ : ProbabilityMeasure C(BridgeTime, ℝ))) atTop
      (𝓝 (⟨brownianUnitPathLaw B 1 P,
        isProbabilityMeasure_brownianUnitPathLaw B 1 P hB⟩ : ProbabilityMeasure C(BridgeTime, ℝ))) := by
  obtain ⟨h3, hmean, hsecond, hthird⟩ := rademacher_moments
  have hh : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro r
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop r)] with j hj
    linarith
  exact tendsto_polygonalPathLaw_brownianUnitPathLaw B 1 P hB
    (fun _ => Shao.OQ4.RademacherCosine.law) (fun _ => h3) (fun _ => hmean)
    (fun _ => hsecond) 1 (fun _ => hthird.le) (fun j : ℕ => (j : ℝ) + 1)
    (by intro j; positivity) hh (fun j => (j + 1) ^ 2)
    (by intro j; simp only [NNReal.coe_one, one_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, le_refl])

theorem brownian_endpoint_real {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (S : Set ℝ) (hS : MeasurableSet S) :
    (brownianUnitPathLaw B 1 P).real {f : C(BridgeTime, ℝ) | f 1 ∈ S} =
      (gaussianReal 0 1).real S := by
  have hm : Measurable (fun f : C(BridgeTime, ℝ) => f 1) := ContinuousMap.measurable_eval 1
  have hs : MeasurableSet {f : C(BridgeTime, ℝ) | f 1 ∈ S} := hS.preimage hm
  rw [brownianUnitPathLaw, measureReal_def, Measure.map_apply_of_aemeasurable
    (aemeasurable_brownianUnitPath B 1 P hB) hs, measureReal_def]
  apply congrArg ENNReal.toReal
  calc
    _ = P {ω | B 1 ω ∈ S} := measure_congr (by
      filter_upwards [ae_unit_eval_one B P hB] with ω hω
      apply propext
      change (brownianUnitPath B 1 ω 1 ∈ S) ↔ B 1 ω ∈ S
      rw [hω])
    _ = (gaussianReal 0 1) S := (hB.toIsPreBrownianReal.hasLaw_eval 1).measure_eq hS

theorem polygonal_endpoint_real (n : ℕ) (h : ℝ) (hh : 0 < h)
    (hsq : h ^ 2 = (n : ℝ)) (ν : Measure ℝ) (S : Set ℝ) (hS : MeasurableSet S) :
    (polygonalPathLaw 1 n h ν).real {f : C(BridgeTime, ℝ) | f 1 ∈ S} =
      (Measure.pi (fun _ : Fin n => ν)).real {p : Shao.Path n | Shao.prefixSum p n / h ∈ S} := by
  have hm : Measurable (fun f : C(BridgeTime, ℝ) => f 1) := ContinuousMap.measurable_eval 1
  have hs : MeasurableSet {f : C(BridgeTime, ℝ) | f 1 ∈ S} := hS.preimage hm
  simp only [measureReal_def, polygonalPathLaw]
  rw [Measure.map_apply (measurable_unitPolygonalPath 1 n h) hs]
  apply congrArg ENNReal.toReal
  apply congrArg (Measure.pi (fun _ : Fin n => ν))
  ext p
  change (unitPolygonalPath 1 n h p 1 ∈ S) ↔ (Shao.prefixSum p n / h ∈ S)
  rw [unitPolygonalPath_one n h hh hsq p]

private theorem endpoint_set_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (S : Set ℝ) (hS : MeasurableSet S)
    (r : ℝ) (hfront : frontier S ⊆ {r}) :
    Tendsto (fun j : ℕ =>
      (Measure.pi (fun _ : Fin ((j + 1) ^ 2) => Shao.OQ4.RademacherCosine.law)).real
        {p : Shao.Path ((j + 1) ^ 2) | Shao.prefixSum p ((j + 1) ^ 2) / ((j : ℝ) + 1) ∈ S})
      atTop (𝓝 ((gaussianReal 0 1).real S)) := by
  letI := isProbabilityMeasure_brownianUnitPathLaw B 1 P hB
  have hc : Continuous (fun f : C(BridgeTime, ℝ) => f 1) := by fun_prop
  have hb : frontier {f : C(BridgeTime, ℝ) | f 1 ∈ S} ⊆
      {f : C(BridgeTime, ℝ) | f 1 = r} :=
    (hc.frontier_preimage_subset S).trans (Set.preimage_mono hfront)
  have hz := measure_mono_null hb (brownianUnitPathLaw_endpoint_zero B P hB r)
  have hset := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (rademacher_pathLaw_tendsto B P hB) hz
  have hr := (ENNReal.continuousAt_toReal
    (measure_ne_top (brownianUnitPathLaw B 1 P) {f : C(BridgeTime, ℝ) | f 1 ∈ S})).tendsto.comp hset
  change Tendsto (fun j : ℕ =>
    (polygonalPathLaw 1 ((j + 1) ^ 2) ((j : ℝ) + 1) Shao.OQ4.RademacherCosine.law).real
      {f : C(BridgeTime, ℝ) | f 1 ∈ S}) atTop
      (𝓝 ((brownianUnitPathLaw B 1 P).real {f : C(BridgeTime, ℝ) | f 1 ∈ S})) at hr
  have hfun : (fun j : ℕ =>
      (polygonalPathLaw 1 ((j + 1) ^ 2) ((j : ℝ) + 1) Shao.OQ4.RademacherCosine.law).real
        {f : C(BridgeTime, ℝ) | f 1 ∈ S}) =
      (fun j : ℕ =>
        (Measure.pi (fun _ : Fin ((j + 1) ^ 2) => Shao.OQ4.RademacherCosine.law)).real
          {p : Shao.Path ((j + 1) ^ 2) | Shao.prefixSum p ((j + 1) ^ 2) / ((j : ℝ) + 1) ∈ S}) := by
    funext j
    apply polygonal_endpoint_real _ _ (by positivity) _ _ S hS
    simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  rw [hfun, brownian_endpoint_real B P hB S hS] at hr
  exact hr

theorem rademacher_endpoint_cdf_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (v : ℝ) :
    Tendsto (fun j : ℕ =>
      (Measure.pi (fun _ : Fin ((j + 1) ^ 2) => Shao.OQ4.RademacherCosine.law)).real
        {p : Shao.Path ((j + 1) ^ 2) | Shao.prefixSum p ((j + 1) ^ 2) / ((j : ℝ) + 1) ≤ v})
      atTop (𝓝 ((gaussianReal 0 1).real (Iic v))) := by
  simpa only [Set.mem_Iic] using
    endpoint_set_tendsto B P hB (Iic v) measurableSet_Iic v (frontier_Iic_subset v)

theorem rademacher_endpoint_tail_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (v : ℝ) :
    Tendsto (fun j : ℕ =>
      (Measure.pi (fun _ : Fin ((j + 1) ^ 2) => Shao.OQ4.RademacherCosine.law)).real
        {p : Shao.Path ((j + 1) ^ 2) | v ≤ Shao.prefixSum p ((j + 1) ^ 2) / ((j : ℝ) + 1)})
      atTop (𝓝 ((gaussianReal 0 1).real (Ici v))) := by
  simpa only [Set.mem_Ici] using
    endpoint_set_tendsto B P hB (Ici v) measurableSet_Ici v (frontier_Ici_subset v)

theorem rademacher_upper_joint_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a v : ℝ) (ha : 0 < a) :
    Tendsto (fun j : ℕ =>
      (polygonalPathLaw 1 ((j + 1) ^ 2) ((j : ℝ) + 1) Shao.OQ4.RademacherCosine.law).real
        (upperJointSet a v)) atTop
      (𝓝 (P.real {ω | (∀ t : BridgeTime, B ⟨(t : ℝ), t.property.1⟩ ω < a) ∧ B 1 ω ≤ v})) := by
  obtain ⟨h3, hmean, hsecond, hthird⟩ := rademacher_moments
  have hh : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro r
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop r)] with j hj
    linarith
  exact row_upper_joint_tendsto_brownian B P hB
    (fun _ => Shao.OQ4.RademacherCosine.law) (fun _ => h3) (fun _ => hmean)
    (fun _ => hsecond) 1 (fun _ => hthird.le) (fun j : ℕ => (j : ℝ) + 1)
    (by intro j; positivity) hh (fun j => (j + 1) ^ 2)
    (by intro j; simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, le_refl]) a v ha

end Shao.C2.RademacherBrownianEndpointLimit
