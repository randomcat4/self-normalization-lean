import Shao.C2.BrownianKilledAction
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

noncomputable section
namespace Shao.C2.BrownianPathWeakMarkov
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.PhysicalBrownianEndpointDensity
open Shao.OQ4.PolygonalBrownianWeakLimit

private theorem indepFun_continuousPaths_of_evaluations {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F G : Ω → C(BridgeTime, ℝ))
    (h : IndepFun (fun ω (t : BridgeTime) => F ω t) (fun ω (t : BridgeTime) => G ω t) P) :
    IndepFun F G P := by
  let φ : C(BridgeTime, ℝ) → (BridgeTime → ℝ) := fun f t => f t
  have hm : (inferInstance : MeasurableSpace C(BridgeTime, ℝ)) =
      (inferInstance : MeasurableSpace (BridgeTime → ℝ)).comap φ := by
    rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval]
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    rfl
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro A D hA hD
  have hA' : MeasurableSet[(inferInstance : MeasurableSpace (BridgeTime → ℝ)).comap φ] A := by
    rw [← hm]
    exact hA
  have hD' : MeasurableSet[(inferInstance : MeasurableSpace (BridgeTime → ℝ)).comap φ] D := by
    rw [← hm]
    exact hD
  rcases hA' with ⟨A', hA', hpreA⟩
  rcases hD' with ⟨D', hD', hpreD⟩
  have hFA : F ⁻¹' A = (fun ω t => F ω t) ⁻¹' A' := by
    rw [← hpreA]
    rfl
  have hGD : G ⁻¹' D = (fun ω t => G ω t) ⁻¹' D' := by
    rw [← hpreD]
    rfl
  rw [hFA, hGD]
  exact h A' D' hA' hD'

private theorem indepFun_unitPaths_of_raw {Ω : Type*} [MeasurableSpace Ω]
    (B C : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hC : IsBrownianReal C P) (T U : ℝ≥0)
    (h : IndepFun (fun ω (t : ℝ≥0) => C t ω)
      (fun ω (t : Iic T) => B t ω) P) :
    IndepFun (brownianUnitPath C U) (brownianUnitPath B T) P := by
  let e : BridgeTime → ℝ≥0 := fun t => NNReal.mk (t : ℝ) t.property.1
  have hbound (t : BridgeTime) : T * e t ≤ T := by
    have he : e t ≤ 1 := by
      apply NNReal.coe_le_coe.mp
      simpa only [e, NNReal.coe_mk, NNReal.coe_one] using t.property.2
    calc
      T * e t ≤ T * 1 := mul_le_mul_of_nonneg_left he (show (0 : ℝ≥0) ≤ T from zero_le)
      _ = T := mul_one T
  let φ : (ℝ≥0 → ℝ) → (BridgeTime → ℝ) := fun f t => f (U * e t)
  let ψ : (Iic T → ℝ) → (BridgeTime → ℝ) := fun f t => f ⟨T * e t, hbound t⟩
  have hφ : Measurable φ := Measurable.of_eval fun t =>
    measurable_pi_apply (X := fun _ : ℝ≥0 => ℝ) (U * e t)
  have hψ : Measurable ψ := Measurable.of_eval fun t =>
    measurable_pi_apply (X := fun _ : Iic T => ℝ) ⟨T * e t, hbound t⟩
  have hh := h.comp hφ hψ
  apply indepFun_continuousPaths_of_evaluations P (brownianUnitPath C U) (brownianUnitPath B T)
  apply hh.congr
  · filter_upwards [ae_brownianUnitPath_eq C U P hC] with ω hω
    funext t
    exact (hω t).symm
  · filter_upwards [ae_brownianUnitPath_eq B T P hB] with ω hω
    funext t
    exact (hω t).symm

theorem indepFun_shifted_unitPath {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T U : ℝ≥0) :
    IndepFun (brownianUnitPath (fun t ω => B (T + t) ω - B T ω) U)
      (brownianUnitPath B T) P := by
  exact indepFun_unitPaths_of_raw B (fun t ω => B (T + t) ω - B T ω) P hB
    (hB.shift T) T U (hB.toIsPreBrownianReal.indepFun_shift T)

theorem normalized_bridge_endpoint_indep_past {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T S : ℝ≥0) (hS : S ≠ 0) :
    IndepFun (fun ω =>
      (bridgeNoise (normalizedPhysicalBrownian (fun t ω => B (T + t) ω - B T ω) S) ω,
        normalizedPhysicalBrownian (fun t ω => B (T + t) ω - B T ω) S 1 ω))
      (brownianUnitPath B T) P := by
  let C : ℝ≥0 → Ω → ℝ :=
    normalizedPhysicalBrownian (fun t ω => B (T + t) ω - B T ω) S
  have hC : IsBrownianReal C P :=
    isBrownianReal_normalizedPhysicalBrownian _ P (hB.shift T) S hS
  let scale : (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) :=
    fun f t => (Real.sqrt (S : ℝ))⁻¹ * f (S * t)
  have hscale : Measurable scale := Measurable.of_eval fun t =>
    (measurable_pi_apply (X := fun _ : ℝ≥0 => ℝ) (S * t)).const_mul _
  have hraw : IndepFun (fun ω (t : ℝ≥0) => C t ω)
      (fun ω (t : Iic T) => B t ω) P := by
    have hh := (hB.toIsPreBrownianReal.indepFun_shift T).comp hscale measurable_id
    simpa only [Function.comp_def, id_eq, C, scale, normalizedPhysicalBrownian] using hh
  have hpath := indepFun_unitPaths_of_raw B C P hB hC T 1 hraw
  let q : C(BridgeTime, ℝ) → BridgeNoise × ℝ := fun f => (pinPath f, f 1)
  have hq : Measurable q := continuous_pinPath.measurable.prodMk (ContinuousMap.measurable_eval 1)
  have hh := hpath.comp hq measurable_id
  apply hh.congr
  · filter_upwards [ae_brownianUnitPath_eq C 1 P hC] with ω hω
    apply Prod.ext
    · rfl
    · have he := hω (1 : BridgeTime)
      change brownianUnitPath C 1 ω 1 = C (1 * 1) ω at he
      change brownianUnitPath C 1 ω 1 = C 1 ω
      simpa only [one_mul] using he
  · exact Eventually.of_forall fun _ => rfl

end Shao.C2.BrownianPathWeakMarkov
