import Shao.C2.PhysicalBrownianEndpointDensity
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

noncomputable section
namespace Shao.C2.BrownianBridgeLawUniversality
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.PhysicalBrownianEndpointDensity

private theorem bridgeNoise_measure_eq_of_eval_law_eq (μ ν : Measure BridgeNoise)
    (h : μ.map (fun g : BridgeNoise => fun t : BridgeTime => g.val t) =
      ν.map (fun g : BridgeNoise => fun t : BridgeTime => g.val t)) : μ = ν := by
  let φ : BridgeNoise → (BridgeTime → ℝ) := fun g t => g.val t
  have hφ : Measurable φ := by
    apply measurable_pi_lambda
    intro t
    exact (ContinuousMap.measurable_eval t).comp measurable_subtype_coe
  have hm : (inferInstance : MeasurableSpace BridgeNoise) =
      (inferInstance : MeasurableSpace (BridgeTime → ℝ)).comap φ := by
    change (inferInstance : MeasurableSpace C(BridgeTime, ℝ)).comap
      (fun g : BridgeNoise => g.val) = _
    rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval]
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    rfl
  apply Measure.ext
  intro A hA
  have hs : MeasurableSet[(inferInstance : MeasurableSpace (BridgeTime → ℝ)).comap φ] A := by
    rw [← hm]
    exact hA
  rcases hs with ⟨S, hS, hpre⟩
  calc
    μ A = (μ.map φ) S := by rw [Measure.map_apply hφ hS, hpre]
    _ = (ν.map φ) S := congrArg (fun m : Measure (BridgeTime → ℝ) => m S) h
    _ = ν A := by rw [Measure.map_apply hφ hS, hpre]

theorem bridgeLaw_eq_of_isBrownianReal {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (B : ℝ≥0 → Ω → ℝ) (C : ℝ≥0 → Ω' → ℝ)
    (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hB : IsBrownianReal B P) (hC : IsBrownianReal C Q) :
    bridgeLaw B P = bridgeLaw C Q := by
  classical
  let φ : BridgeNoise → (BridgeTime → ℝ) := fun g t => g.val t
  have hφ : Measurable φ := by
    apply measurable_pi_lambda
    intro t
    exact (ContinuousMap.measurable_eval t).comp measurable_subtype_coe
  let X : Ω → (BridgeTime → ℝ) := φ ∘ bridgeNoise B
  let Y : Ω' → (BridgeTime → ℝ) := φ ∘ bridgeNoise C
  have hX : AEMeasurable X P := hφ.comp_aemeasurable (aemeasurable_bridgeNoise B P hB)
  have hY : AEMeasurable Y Q := hφ.comp_aemeasurable (aemeasurable_bridgeNoise C Q hC)
  have hfinite (I : Finset BridgeTime) :
      P.map (fun ω => I.restrict (X ω)) = Q.map (fun ω => I.restrict (Y ω)) := by
    let e : BridgeTime → ℝ≥0 := fun t => ⟨(t : ℝ), t.property.1⟩
    let J : Finset ℝ≥0 := insert 1 (I.image e)
    have he (i : I) : e i.val ∈ J :=
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem e i.property)
    have hone : (1 : ℝ≥0) ∈ J := Finset.mem_insert_self _ _
    let L : (J → ℝ) → (I → ℝ) := fun v i =>
      v ⟨e i.val, he i⟩ - ((i.val : BridgeTime) : ℝ) * v ⟨1, hone⟩
    have hL : Measurable L := by
      apply measurable_pi_lambda
      intro i
      exact (measurable_pi_apply (X := fun _ : J => ℝ) (⟨e i.val, he i⟩ : J)).sub
        ((measurable_pi_apply (X := fun _ : J => ℝ) (⟨1, hone⟩ : J)).const_mul _)
    have hJB := hB.toIsPreBrownianReal.hasLaw J
    have hJC := hC.toIsPreBrownianReal.hasLaw J
    have hJ : IdentDistrib (fun ω => J.restrict (fun t => B t ω))
        (fun ω => J.restrict (fun t => C t ω)) P Q :=
      ⟨hJB.aemeasurable, hJC.aemeasurable, hJB.map_eq.trans hJC.map_eq.symm⟩
    have hLB : P.map (fun ω => I.restrict (X ω)) =
        P.map (L ∘ (fun ω => J.restrict (fun t => B t ω))) := by
      apply Measure.map_congr
      filter_upwards [ae_bridgeNoise_eq B P hB] with ω hω
      funext i
      exact hω i.val
    have hLC : Q.map (fun ω => I.restrict (Y ω)) =
        Q.map (L ∘ (fun ω => J.restrict (fun t => C t ω))) := by
      apply Measure.map_congr
      filter_upwards [ae_bridgeNoise_eq C Q hC] with ω hω
      funext i
      exact hω i.val
    exact hLB.trans ((hJ.comp hL).map_eq.trans hLC.symm)
  have hPX : IsProjectiveLimit (P.map X)
      (fun I : Finset BridgeTime => Q.map (fun ω => I.restrict (Y ω))) := by
    intro I
    rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict I).aemeasurable hX]
    simpa only [Function.comp_def] using hfinite I
  have hPY : IsProjectiveLimit (Q.map Y)
      (fun I : Finset BridgeTime => Q.map (fun ω => I.restrict (Y ω))) := by
    intro I
    rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict I).aemeasurable hY]
    rfl
  have hXY : P.map X = Q.map Y := hPX.unique hPY
  apply bridgeNoise_measure_eq_of_eval_law_eq
  change (P.map (bridgeNoise B)).map φ = (Q.map (bridgeNoise C)).map φ
  rw [AEMeasurable.map_map_of_aemeasurable hφ.aemeasurable (aemeasurable_bridgeNoise B P hB),
    AEMeasurable.map_map_of_aemeasurable hφ.aemeasurable (aemeasurable_bridgeNoise C Q hC)]
  exact hXY

theorem bridgeLaw_normalizedPhysicalBrownian {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (hT : T ≠ 0) :
    bridgeLaw (normalizedPhysicalBrownian B T) P = bridgeLaw B P := by
  exact bridgeLaw_eq_of_isBrownianReal (normalizedPhysicalBrownian B T) B P P
    (isBrownianReal_normalizedPhysicalBrownian B P hB T hT) hB

private theorem physical_survival_event_iff {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (a y : ℝ) (T : ℝ≥0) (hT : T ≠ 0) (ω : Ω) :
    (∀ t : BridgeTime, |y + B (T * ⟨(t : ℝ), t.property.1⟩) ω| < a) ↔
      ∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a := by
  have hTpos : 0 < (T : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hT : 0 < T)
  constructor
  · intro h s hs
    let t : BridgeTime := ⟨(s : ℝ) / (T : ℝ),
      div_nonneg s.property T.property,
      (div_le_one hTpos).2 (by exact_mod_cast hs)⟩
    let u : ℝ≥0 := ⟨(t : ℝ), t.property.1⟩
    have heq : T * u = s := by
      apply NNReal.eq
      change (T : ℝ) * ((s : ℝ) / (T : ℝ)) = (s : ℝ)
      field_simp
    have ht := h t
    change |y + B (T * u) ω| < a at ht
    simpa only [heq] using ht
  · intro h t
    apply h
    have hh : (T : ℝ) * (t : ℝ) ≤ (T : ℝ) := by
      nlinarith [t.property.2]
    exact_mod_cast hh

theorem brownian_physical_interval_joint_hasDerivAt_fixedLaw {Ω : Type*}
    [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y z : ℝ) (T : ℝ≥0) (hT : T ≠ 0) :
    HasDerivAt (fun v : ℝ => P.real {ω |
      (∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a) ∧ y + B T ω ≤ v})
      (gaussianPDFReal y T z * intervalCompletion (bridgeLaw B P) a y (T : ℝ) z) z := by
  have hd := brownian_physical_interval_joint_hasDerivAt B P hB a y z T hT
  rw [bridgeLaw_normalizedPhysicalBrownian B P hB T hT] at hd
  have heq : (fun v : ℝ => P.real {ω |
      (∀ t : BridgeTime, |y + B (T * ⟨(t : ℝ), t.property.1⟩) ω| < a) ∧ y + B T ω ≤ v}) =
      (fun v : ℝ => P.real {ω |
        (∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a) ∧ y + B T ω ≤ v}) := by
    funext v
    congr 1
    ext ω
    exact and_congr (physical_survival_event_iff B a y T hT ω) Iff.rfl
  rw [heq] at hd
  exact hd

theorem brownian_physical_interval_density_ratio_fixedLaw {Ω : Type*}
    [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y z : ℝ) (T : ℝ≥0) (hT : T ≠ 0) :
    deriv (fun v : ℝ => P.real {ω |
      (∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a) ∧ y + B T ω ≤ v}) z /
        gaussianPDFReal y T z = intervalCompletion (bridgeLaw B P) a y (T : ℝ) z := by
  rw [(brownian_physical_interval_joint_hasDerivAt_fixedLaw B P hB a y z T hT).deriv]
  have hp : gaussianPDFReal y T z ≠ 0 := (gaussianPDFReal_pos y T z hT).ne'
  field_simp [hp]

end Shao.C2.BrownianBridgeLawUniversality
