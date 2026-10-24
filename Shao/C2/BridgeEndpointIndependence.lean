import Shao.C2.BrownianBridgeLaw
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

open scoped NNReal

noncomputable section
namespace Shao.C2.BrownianBridgeLaw
open MeasureTheory ProbabilityTheory
open Shao.C2.BridgeDomination

def bridgeJointProcess {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) :
    BridgeTime ⊕ Unit → Ω → ℝ :=
  Sum.elim
    (fun t ω => B ⟨(t : ℝ), t.property.1⟩ ω - (t : ℝ) * B 1 ω)
    (fun _ ω => B 1 ω)

theorem isGaussianProcess_bridgeJointProcess {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) : IsGaussianProcess (bridgeJointProcess B) P := by
  classical
  apply hB.toIsPreBrownianReal.isGaussianProcess.of_isGaussianProcess
  intro s
  cases s with
  | inl t =>
    let u : ℝ≥0 := ⟨(t : ℝ), t.property.1⟩
    refine ⟨{u, 1},
      { toFun := fun f => f ⟨u, by simp⟩ - (t : ℝ) * f ⟨1, by simp⟩
        map_add' := by intros; simp only [Pi.add_apply]; ring
        map_smul' := by intros; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }, ?_⟩
    intro ω
    rfl
  | inr s =>
    refine ⟨{1},
      { toFun := fun f => f ⟨1, by simp⟩
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }, ?_⟩
    intro ω
    rfl

theorem covariance_bridge_endpoint {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (t : BridgeTime) :
    cov[fun ω => B ⟨(t : ℝ), t.property.1⟩ ω - (t : ℝ) * B 1 ω, B 1; P] = 0 := by
  let u : ℝ≥0 := ⟨(t : ℝ), t.property.1⟩
  have htu := (hB.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_eval u).memLp_two
  have ht1 := (hB.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_eval 1).memLp_two
  rw [covariance_fun_sub_left htu (ht1.const_mul (t : ℝ)) ht1,
    covariance_const_mul_left,
    hB.toIsPreBrownianReal.covariance_eval u 1,
    hB.toIsPreBrownianReal.covariance_eval 1 1]
  change min (t : ℝ) 1 - (t : ℝ) * min (1 : ℝ) 1 = 0
  rw [min_eq_left t.property.2, min_self, mul_one, sub_self]

theorem raw_bridge_indep_endpoint {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    IndepFun (fun ω (t : BridgeTime) =>
      B ⟨(t : ℝ), t.property.1⟩ ω - (t : ℝ) * B 1 ω) (B 1) P := by
  have hg : IsGaussianProcess (Sum.elim
      (fun t : BridgeTime => fun ω =>
        B ⟨(t : ℝ), t.property.1⟩ ω - (t : ℝ) * B 1 ω)
      (fun _ : Unit => B 1)) P := isGaussianProcess_bridgeJointProcess B P hB
  have hi := hg.indepFun_of_covariance_eq_zero
    (fun t => (hB.toIsPreBrownianReal.aemeasurable ⟨(t : ℝ), t.property.1⟩).sub
      ((hB.toIsPreBrownianReal.aemeasurable 1).const_mul (t : ℝ)))
    (fun _ => hB.toIsPreBrownianReal.aemeasurable 1)
    (fun t _ => covariance_bridge_endpoint B P hB t)
  simpa only [Function.comp_def, id_eq] using
    hi.comp measurable_id (measurable_pi_apply ())

theorem bridgeNoise_indep_endpoint {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) : IndepFun (bridgeNoise B) (B 1) P := by
  let f : Ω → BridgeTime → ℝ := fun ω t => (bridgeNoise B ω).val t
  have hraw : (fun ω (t : BridgeTime) =>
      B ⟨(t : ℝ), t.property.1⟩ ω - (t : ℝ) * B 1 ω) =ᵐ[P] f := by
    filter_upwards [ae_bridgeNoise_eq B P hB] with ω hω
    funext t
    exact (hω t).symm
  have hi : IndepFun f (B 1) P :=
    (raw_bridge_indep_endpoint B P hB).congr hraw (Filter.Eventually.of_forall fun _ => rfl)
  rw [IndepFun_iff_Indep] at hi ⊢
  have hspace :
      MeasurableSpace.comap (bridgeNoise B) (inferInstance : MeasurableSpace BridgeNoise) =
        MeasurableSpace.comap f (inferInstance : MeasurableSpace (BridgeTime → ℝ)) := by
    change MeasurableSpace.comap (bridgeNoise B)
      (MeasurableSpace.comap Subtype.val (inferInstance : MeasurableSpace C(BridgeTime, ℝ))) = _
    rw [MeasurableSpace.comap_comp, ContinuousMap.measurableSpace_eq_iSup_comap_eval,
      MeasurableSpace.comap_iSup]
    change _ = MeasurableSpace.comap f MeasurableSpace.pi
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp, Function.comp_def, f]
  rw [hspace]
  exact hi

theorem bridge_endpoint_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    HasLaw (fun ω => (bridgeNoise B ω, B 1 ω))
      ((bridgeLaw B P).prod (gaussianReal 0 1)) P := by
  have hG := aemeasurable_bridgeNoise B P hB
  have hE := hB.toIsPreBrownianReal.aemeasurable 1
  refine ⟨hG.prodMk hE, ?_⟩
  rw [(bridgeNoise_indep_endpoint B P hB).map_prod_eq_prod_map_map hG hE]
  change (bridgeLaw B P).prod (P.map (B 1)) = _
  rw [(hB.toIsPreBrownianReal.hasLaw_eval 1).map_eq]

end Shao.C2.BrownianBridgeLaw
