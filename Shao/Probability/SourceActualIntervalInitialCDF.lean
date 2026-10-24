/- Actual original-iid interval rank0 initial value and genuine Brownian marginal/joint budgets. -/
import Shao.Probability.SourceScalarInitialBudget
import Shao.Probability.SourceOriginalZeroEnergyBudget
import Shao.Probability.SourcePermutationReveal
import Shao.C2.RawInitialCompletion
import Shao.C2.InitialCompletionError

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000

noncomputable section
namespace Shao.Probability.SourceActualIntervalInitialCDF
open MeasureTheory ProbabilityTheory
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.Probability.SourcePermutationReveal
open scoped BigOperators NNReal

theorem original_iid_actual_interval_initial_cdf_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω ΩB : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩB]
        (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
        IsBrownianReal B PB →
        ∀ (mu : Measure Ω) (rho : Measure ℝ)
          [IsProbabilityMeasure mu] [IsProbabilityMeasure rho]
          (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ),
          (∀ i, AEMeasurable (X i) mu) →
          iIndepFun X mu →
          (∀ i, IdentDistrib (X i) (id : ℝ → ℝ) mu rho) →
          Integrable (fun z : ℝ => z ^ 2) rho →
          (∫ z : ℝ, z ∂rho) = 0 →
          (0 < ∫ z : ℝ, z ^ 2 ∂rho) →
          let population : Ω → Shao.Path n := Shao.Probability.samplePath X
          let rawEnergy : Ω → ℝ := fun omega => ∑ i : Fin n, (X i omega) ^ 2
          let rawTerminal : Ω → ℝ := fun omega => ∑ i : Fin n, X i omega
          let W : Ω → ℝ := fun omega => Shao.C1.normalizedEndpoint (population omega)
          let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
          let scale : ℝ := Real.sqrt ((n : ℝ) * sigmaSq)
          let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / scale) rho
          let R : ℝ := Shao.truncationBudget normalizedLaw n 0
          let Q : Measure BridgeNoise := bridgeLaw B PB
          ∀ x : ℝ, 0 ≤ x →
            let V0 : LabelPerm n → Ω → ℝ := fun sigma omega =>
              sourceValue .interval (eventCompletionKernel .interval Q)
                (population omega) x 0 sigma
            (∀ omega : Ω,
              Shao.energy (population omega) = rawEnergy omega ∧
              Shao.prefixSum (population omega) n = rawTerminal omega ∧
              W omega = if 0 < rawEnergy omega then
                rawTerminal omega / Real.sqrt (rawEnergy omega) else 0) ∧
            (∀ sigma : LabelPerm n,
              (∀ omega : Ω,
                V0 sigma omega = Shao.C2.RawInitialCompletion.rawInitial Q x (population omega) ∧
                V0 sigma omega = if 0 < rawEnergy omega then
                  intervalCompletion Q x 0 1 (W omega) else 0) ∧
              Integrable (V0 sigma) mu ∧
              |(∫ omega : Ω, V0 sigma omega ∂mu) -
                PB.real {omegaB : ΩB | ∀ t : BridgeTime,
                  |B ⟨(t : ℝ), t.property.1⟩ omegaB| < x}| ≤ C * R ∧
              ∀ v : ℝ,
                Integrable (fun omega : Ω => if W omega ≤ v then V0 sigma omega else 0) mu ∧
                |(∫ omega : Ω, (if W omega ≤ v then V0 sigma omega else 0) ∂mu) -
                  PB.real {omegaB : ΩB |
                    (∀ t : BridgeTime, |B ⟨(t : ℝ), t.property.1⟩ omegaB| < x) ∧
                      B 1 omegaB ≤ v}| ≤ C * R) := by
  classical
  obtain ⟨Cs, hCs, hScalar⟩ :=
    Shao.Probability.SourceScalarInitialBudget.finite_second_scalar_closed_cdf_budget
  refine ⟨2 * Cs + 16, by positivity, ?_⟩
  intro Ω ΩB _ _ B PB _ hB mu rho _ _ n hn X hX hIndep hLaw h2 hmean hsecond
    population rawEnergy rawTerminal W sigmaSq scale normalizedLaw R Q x hx V0
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
  have : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw B PB hB
  have hscale : scale = Real.sqrt sigmaSq * Real.sqrt (n : ℝ) := by
    dsimp only [scale]
    rw [Real.sqrt_mul (show 0 ≤ (n : ℝ) by positivity)]
    exact mul_comm _ _
  have hR : 0 ≤ R := by
    dsimp only [R, Shao.truncationBudget]
    exact mul_nonneg (Nat.cast_nonneg n) (integral_nonneg fun z => Shao.truncationF_nonneg _)
  have hPopulation : AEMeasurable population mu := AEMeasurable.of_eval hX
  have hMap : Measure.map population mu = P := by
    change Measure.map (fun omega i => X i omega) mu = _
    rw [hIndep.map_fun_eq_pi_map hX]
    congr 1
    funext i
    simpa only [Measure.map_id] using (hLaw i).map_eq
  have hPair : IdentDistrib population (id : Shao.Path n → Shao.Path n) mu P :=
    ⟨hPopulation, measurable_id.aemeasurable, by simpa only [Measure.map_id] using hMap⟩
  have hTransfer (A : Set (Shao.Path n)) (hA : MeasurableSet A) :
      mu.real {omega : Ω | population omega ∈ A} = P.real A := by
    simpa only [Measure.real, Set.preimage, id_eq, Set.ofPred_mem_eq] using
      congrArg ENNReal.toReal (hPair.measure_mem_eq hA)
  have hZeroEnergy : P.real {a : Shao.Path n | Shao.energy a = 0} ≤ 16 * R := by
    have hz := SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget
      mu rho n hn X hX hIndep hLaw h2 hsecond
    change mu.real {omega : Ω | population omega ∈
      {a : Shao.Path n | Shao.energy a = 0}} ≤ 16 * R at hz
    rw [hTransfer _ (measurableSet_eq_fun Shao.measurable_energy measurable_const)] at hz
    exact hz
  have hCDF : ∀ v : ℝ,
      |P.real {a : Shao.Path n | Shao.C1.normalizedEndpoint a ≤ v} -
        (gaussianReal 0 1).real (Set.Iic v)| ≤ Cs * R := by
    intro v
    have h := hScalar rho n hn h2 hmean hsecond v
    change |P.real {a : Shao.Path n | Shao.C1.normalizedEndpoint a ≤ v} -
        (gaussianReal 0 1).real (Set.Iic v)| ≤
      Cs * Shao.truncationBudget
        (Measure.map (fun z : ℝ => z / (Real.sqrt sigmaSq * Real.sqrt (n : ℝ))) rho) n 0 at h
    rw [← hscale] at h
    exact h
  have hState (omega : Ω) :
      Shao.energy (population omega) = rawEnergy omega ∧
      Shao.prefixSum (population omega) n = rawTerminal omega ∧
      W omega = if 0 < rawEnergy omega then
        rawTerminal omega / Real.sqrt (rawEnergy omega) else 0 := by
    refine ⟨rfl, ?_, ?_⟩
    · rw [Shao.prefixSum_length]
      rfl
    · change Shao.C1.normalizedEndpoint (population omega) = _
      by_cases hq : 0 < rawEnergy omega
      · rw [if_pos hq, Shao.C1.normalizedEndpoint_of_energy_pos (population omega) hq,
          Shao.prefixSum_length]
        rfl
      · have hz : Shao.energy (population omega) = 0 :=
          le_antisymm (le_of_not_gt hq) (Shao.energy_nonneg _)
        rw [if_neg hq, Shao.C1.normalizedEndpoint_of_energy_eq_zero _ hz]
  have hInitial (a : Shao.Path n) (sigma : LabelPerm n) :
      sourceValue .interval (eventCompletionKernel .interval Q) a x 0 sigma =
        Shao.C2.RawInitialCompletion.rawInitial Q x a := by
    by_cases ha : sourceAlive .interval a x 0 sigma
    · have h0 : Interior .interval (actualWall a x) 0 := by
        simpa only [Shao.prefixSum_zero] using ha.2.2 0 le_rfl
      have hw : 0 < actualWall a x := h0.2
      have hi : 0 < actualWall a x ∧ Interior .interval (actualWall a x) 0 ∧
          Interior .interval (actualWall a x) (Shao.prefixSum a n) := ⟨hw, h0, ha.2.1⟩
      simp only [sourceValue, if_pos ha, Shao.prefixSum_zero, remainingEnergy,
        Shao.prefixSquares_zero, sub_zero, completionExt, if_pos hi, if_pos ha.1,
        Shao.C2.RawInitialCompletion.rawInitial, eventCompletionKernel]
      rfl
    · rw [sourceValue, if_neg ha]
      unfold Shao.C2.RawInitialCompletion.rawInitial
      by_cases hq : 0 < Shao.energy a
      · rw [if_pos hq]
        have hevent : strictInterval (actualWall a x) 0 (Shao.energy a)
            (Shao.prefixSum a n) = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro g hg
          apply ha
          have hp := bridgePath_endpoints 0 (Shao.energy a) (Shao.prefixSum a n) g
          refine ⟨hq, ?_, ?_⟩
          · exact ⟨by simpa only [hp.2] using hg.2 1,
              by simpa only [hp.2] using hg.1 1⟩
          · intro k hk
            have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
            subst k
            simp only [Shao.prefixSum_zero]
            exact ⟨by simpa only [hp.1] using hg.2 0,
              by simpa only [hp.1] using hg.1 0⟩
        change 0 = Q.real (strictInterval (actualWall a x) 0 (Shao.energy a) (Shao.prefixSum a n))
        rw [hevent, measureReal_empty]
      · rw [if_neg hq]
  have hRawMeas : Measurable (Shao.C2.RawInitialCompletion.rawInitial Q x : Shao.Path n → ℝ) :=
    Shao.C2.RawInitialCompletion.measurable_rawInitial n Q x
  have hRawLaw : IdentDistrib
      (fun omega : Ω => Shao.C2.RawInitialCompletion.rawInitial Q x (population omega))
      (Shao.C2.RawInitialCompletion.rawInitial Q x : Shao.Path n → ℝ) mu P := by
    simpa only [Function.comp_def, id_eq] using hPair.comp hRawMeas
  have hMarginal :
      |(∫ a : Shao.Path n, Shao.C2.RawInitialCompletion.rawInitial Q x a ∂P) -
        PB.real {omegaB : ΩB | ∀ t : BridgeTime,
          |B ⟨(t : ℝ), t.property.1⟩ omegaB| < x}| ≤ (2 * Cs + 16) * R := by
    have h := Shao.C2.InitialCompletionError.initial_marginal_error_of_cdf
      P Shao.C1.normalizedEndpoint Shao.energy
      Shao.C1.measurable_normalizedEndpoint.aemeasurable Shao.measurable_energy
      (Filter.Eventually.of_forall Shao.energy_nonneg) B PB hB (Cs * R)
      (mul_nonneg hCs.le hR) hCDF x
    have he : (fun a : Shao.Path n => if 0 < Shao.energy a then
        intervalCompletion Q x 0 1 (Shao.C1.normalizedEndpoint a) else 0) =
        Shao.C2.RawInitialCompletion.rawInitial Q x := by
      funext a
      exact (Shao.C2.RawInitialCompletion.rawInitial_eq_normalized n Q x a).symm
    rw [he] at h
    exact h.trans (by nlinarith [hZeroEnergy])
  have hJoint (v : ℝ) :
      |(∫ a : Shao.Path n, (if Shao.C1.normalizedEndpoint a ≤ v then
          Shao.C2.RawInitialCompletion.rawInitial Q x a else 0) ∂P) -
        PB.real {omegaB : ΩB |
          (∀ t : BridgeTime, |B ⟨(t : ℝ), t.property.1⟩ omegaB| < x) ∧
            B 1 omegaB ≤ v}| ≤ (2 * Cs + 16) * R := by
    have h := Shao.C2.InitialCompletionError.initial_joint_error_of_cdf
      P Shao.C1.normalizedEndpoint Shao.energy
      Shao.C1.measurable_normalizedEndpoint.aemeasurable Shao.measurable_energy
      (Filter.Eventually.of_forall Shao.energy_nonneg) B PB hB (Cs * R)
      (mul_nonneg hCs.le hR) hCDF x v
    have he (a : Shao.Path n) :
        (if 0 < Shao.energy a then (if Shao.C1.normalizedEndpoint a ≤ v then
          intervalCompletion Q x 0 1 (Shao.C1.normalizedEndpoint a) else 0) else 0) =
        (if Shao.C1.normalizedEndpoint a ≤ v then
          Shao.C2.RawInitialCompletion.rawInitial Q x a else 0) := by
      rw [Shao.C2.RawInitialCompletion.rawInitial_eq_normalized]
      split_ifs <;> rfl
    have hf : (fun a : Shao.Path n => if 0 < Shao.energy a then
        (if Shao.C1.normalizedEndpoint a ≤ v then
          intervalCompletion Q x 0 1 (Shao.C1.normalizedEndpoint a) else 0) else 0) =
        (fun a : Shao.Path n => if Shao.C1.normalizedEndpoint a ≤ v then
          Shao.C2.RawInitialCompletion.rawInitial Q x a else 0) := funext he
    rw [hf] at h
    exact h.trans (by nlinarith [hZeroEnergy])
  refine ⟨hState, ?_⟩
  intro sigma
  have hVeq : V0 sigma = fun omega =>
      Shao.C2.RawInitialCompletion.rawInitial Q x (population omega) :=
    funext fun omega => hInitial (population omega) sigma
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro omega
    refine ⟨congrFun hVeq omega, ?_⟩
    rw [congrFun hVeq omega]
    exact Shao.C2.RawInitialCompletion.rawInitial_eq_normalized n Q x (population omega)
  · rw [hVeq]
    exact hRawLaw.integrable_iff.mpr
      (Shao.C2.RawInitialCompletion.integrable_rawInitial_and_joint n Q P x 0).1
  · rw [hVeq, hRawLaw.integral_eq]
    exact hMarginal
  · intro v
    let F : Shao.Path n → ℝ := fun a => if Shao.C1.normalizedEndpoint a ≤ v then
      Shao.C2.RawInitialCompletion.rawInitial Q x a else 0
    have hF : Measurable F := Measurable.ite
      (measurableSet_le Shao.C1.measurable_normalizedEndpoint measurable_const)
      hRawMeas measurable_const
    have hFLaw : IdentDistrib (fun omega : Ω => if W omega ≤ v then
        Shao.C2.RawInitialCompletion.rawInitial Q x (population omega) else 0) F mu P := by
      simpa only [Function.comp_def, id_eq] using hPair.comp hF
    constructor
    · simp_rw [hVeq]
      exact hFLaw.integrable_iff.mpr
        (Shao.C2.RawInitialCompletion.integrable_rawInitial_and_joint n Q P x v).2
    · simp_rw [hVeq]
      rw [hFLaw.integral_eq]
      exact hJoint v

end Shao.Probability.SourceActualIntervalInitialCDF
