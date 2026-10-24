/- Mathematical candidate only. No production body or Lean/AX check.
   The actual interval-initial CDF dependency is not formally qualified yet. -/
import Shao.Probability.SourceActualGaussianTransfer
import Shao.Probability.SourceActualIntervalInitialCDF
import Shao.Probability.SourceScalarInitialBudget
import Shao.C2.BridgeLowerIdentification
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace Shao.Probability.SourceOriginalBrownianComparison
open MeasureTheory ProbabilityTheory
open SourcePermutationReveal
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open scoped BigOperators Classical NNReal

local instance labelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

theorem original_iid_actual_brownian_small_window_comparison :
    ∀ Csmall : ℝ, 0 ≤ Csmall → ∃ C : ℝ, 0 < C ∧
      ∀ {Ω ΩB : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩB]
        (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
        IsBrownianReal B PB →
        let Q : Measure BridgeNoise := bridgeLaw B PB
        (∀ w y T z : ℝ, 0 < w → 0 < T → |y| < w → |z| < w →
          DifferentiableAt ℝ
            (fun s : ℝ => Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w s T z) y) →
        (∀ w y T z beta : ℝ, 0 < w → 0 < T → |y| < w → |z| < w →
          beta ^ 2 ≤ T / 2 → |y + beta| ≤ w →
          |Shao.C2.ActualIntervalProjection.sourceRemainder Q w y T z beta| ≤
            Csmall * |beta| ^ 3 * (1 / Real.sqrt T) ^ 3 *
              (1 + |z - y| / Real.sqrt T) ^ 3 *
                Shao.C2.IntervalGaussianLocal.intervalIncrementProfile w y T z beta) →
        ∀ (mu : Measure Ω) (rho : Measure ℝ)
          [IsProbabilityMeasure mu] [IsProbabilityMeasure rho]
          (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ),
          (∀ i, AEMeasurable (X i) mu) →
          iIndepFun X mu →
          (∀ i, IdentDistrib (X i) (id : ℝ → ℝ) mu rho) →
          Integrable (fun z : ℝ => z ^ 2) rho →
          (∫ z : ℝ, z ∂rho) = 0 → 0 < (∫ z : ℝ, z ^ 2 ∂rho) →
          let population : Ω → Shao.Path n := Shao.Probability.samplePath X
          let rawEnergy : Ω → ℝ := fun omega => ∑ i : Fin n, (X i omega) ^ 2
          let rawTerminal : Ω → ℝ := fun omega => ∑ i : Fin n, X i omega
          let M : Ω → ℝ := fun omega => Shao.absMax (population omega) hn
          let W : Ω → ℝ := fun omega => Shao.C1.normalizedEndpoint (population omega)
          let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
          let scale : ℝ := Real.sqrt ((n : ℝ) * sigmaSq)
          let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / scale) rho
          let R : ℝ := Shao.truncationBudget normalizedLaw n 0
          ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
            let strictSurvival : Set Ω :=
              {omega | M omega < x * Real.sqrt (rawEnergy omega)}
            let weakCrossing : Set Ω :=
              {omega | x * Real.sqrt (rawEnergy omega) ≤ M omega}
            let brownianStrictSurvival : Set ΩB :=
              {omegaB | ∀ t : BridgeTime, |B ⟨(t : ℝ), t.property.1⟩ omegaB| < x}
            let brownianWeakCrossing : Set ΩB :=
              {omegaB | ∃ t : BridgeTime, x ≤ |B ⟨(t : ℝ), t.property.1⟩ omegaB|}
            (∀ omega : Ω,
              Shao.energy (population omega) = rawEnergy omega ∧
              Shao.prefixSum (population omega) n = rawTerminal omega ∧
              W omega = if 0 < rawEnergy omega then
                rawTerminal omega / Real.sqrt (rawEnergy omega) else 0) ∧
            AEMeasurable rawEnergy mu ∧ AEMeasurable M mu ∧ AEMeasurable W mu ∧
            |mu.real strictSurvival - PB.real brownianStrictSurvival| ≤ C * R ∧
            |mu.real weakCrossing - PB.real brownianWeakCrossing| ≤ C * R ∧
            (∀ v : ℝ,
              |mu.real (strictSurvival ∩ {omega : Ω | W omega ≤ v}) -
                PB.real (brownianStrictSurvival ∩ {omegaB : ΩB | B 1 omegaB ≤ v})| ≤ C * R ∧
              |mu.real (weakCrossing ∩ {omega : Ω | W omega ≤ v}) -
                PB.real (brownianWeakCrossing ∩ {omegaB : ΩB | B 1 omegaB ≤ v})| ≤ C * R) := by
  classical
  intro Csmall hCs
  obtain ⟨CT, hCT, hTransfer⟩ :=
    SourceActualGaussianTransfer.actual_brownian_three_domain_transfer_budget Csmall hCs
  obtain ⟨CI, hCI, hInitial⟩ :=
    SourceActualIntervalInitialCDF.original_iid_actual_interval_initial_cdf_budget
  obtain ⟨CS, hCS, hScalar⟩ := SourceScalarInitialBudget.finite_second_scalar_closed_cdf_budget
  refine ⟨CT + CI + CS, by positivity, ?_⟩
  intro Ω ΩB hΩ hΩB B PB hPB hB Q hRegular hSmall mu rho hmu hrho n hn X hX hIndep hLaw
    h2 hmean hsecond population rawEnergy rawTerminal M W sigmaSq scale normalizedLaw R x hx0 hx1
    strictSurvival weakCrossing brownianStrictSurvival brownianWeakCrossing
  letI : IsProbabilityMeasure PB := hPB
  letI : IsProbabilityMeasure mu := hmu
  letI : IsProbabilityMeasure rho := hrho
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw B PB hB
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hR : 0 < R := (raw_truncation_budget_suffix_geometry rho n hn h2 hsecond).1
  have hPop : AEMeasurable population mu := AEMeasurable.of_eval hX
  have hPopMap : Measure.map population mu = P := by
    change Measure.map (fun omega i => X i omega) mu = _
    rw [hIndep.map_fun_eq_pi_map hX]
    congr 1
    funext i
    simpa only [Measure.map_id] using (hLaw i).map_eq
  have hPopPair : IdentDistrib population (id : Shao.Path n → Shao.Path n) mu P :=
    ⟨hPop, measurable_id.aemeasurable, by simpa only [Measure.map_id] using hPopMap⟩
  have hEvent (E : Set (Shao.Path n)) (hE : MeasurableSet E) :
      mu.real {omega : Ω | population omega ∈ E} = P.real E := by
    simpa only [Measure.real, Set.preimage, id_eq, Set.ofPred_mem_eq] using
      congrArg ENNReal.toReal (hPopPair.measure_mem_eq hE)
  have hInitF := hInitial B PB hB mu rho n hn X hX hIndep hLaw h2 hmean hsecond x hx0
  have hEnergy : AEMeasurable rawEnergy mu := Shao.measurable_energy.comp_aemeasurable hPop
  have hM : AEMeasurable M mu := (Shao.measurable_absMax hn).comp_aemeasurable hPop
  have hW : AEMeasurable W mu := Shao.C1.measurable_normalizedEndpoint.comp_aemeasurable hPop
  have hScale : Real.sqrt sigmaSq * Real.sqrt (n : ℝ) = scale := by
    dsimp only [scale]
    rw [Real.sqrt_mul (Nat.cast_nonneg n)]
    ring
  have hCDF (v : ℝ) :
      |mu.real {omega : Ω | W omega ≤ v} - (gaussianReal 0 1).real (Set.Iic v)| ≤ CS * R := by
    have he := hEvent {a : Shao.Path n | Shao.C1.normalizedEndpoint a ≤ v}
      (measurableSet_le Shao.C1.measurable_normalizedEndpoint measurable_const)
    have hh := hScalar rho n hn h2 hmean hsecond v
    change |P.real {a : Shao.Path n | Shao.C1.normalizedEndpoint a ≤ v} -
      (gaussianReal 0 1).real (Set.Iic v)| ≤ CS * Shao.truncationBudget
      (Measure.map (fun z : ℝ => z / (Real.sqrt sigmaSq * Real.sqrt (n : ℝ))) rho) n 0 at hh
    rw [hScale] at hh
    change mu.real {omega : Ω | W omega ≤ v} =
      P.real {a : Shao.Path n | Shao.C1.normalizedEndpoint a ≤ v} at he
    rw [he]
    exact hh
  have hEndpoint (v : ℝ) :
      PB.real {omegaB : ΩB | B 1 omegaB ≤ v} = (gaussianReal 0 1).real (Set.Iic v) :=
    (hB.toIsPreBrownianReal.hasLaw_eval 1).measureReal_eq measurableSet_Iic
  have hEnd (v : ℝ) :
      |mu.real {omega : Ω | W omega ≤ v} - PB.real {omegaB : ΩB | B 1 omegaB ≤ v}| ≤ CS * R := by
    rw [hEndpoint]
    exact hCDF v
  let S : Set (Shao.Path n) := {a | Shao.absMax a hn < x * Real.sqrt (Shao.energy a)}
  let A : Shao.Path n → ℝ := S.indicator (fun _ => (1 : ℝ))
  let I : Shao.Path n → ℝ := Shao.C2.RawInitialCompletion.rawInitial Q x
  have hSm : MeasurableSet S :=
    measurableSet_lt (Shao.measurable_absMax hn) (Shao.measurable_energyWall x)
  have hSn : NullMeasurableSet strictSurvival mu := hPop.nullMeasurableSet_preimage hSm
  have hBPreAE : AEMeasurable (fun omegaB : ΩB => (bridgeNoise B omegaB, B 1 omegaB)) PB :=
    (aemeasurable_bridgeNoise B PB hB).prodMk (hB.toIsPreBrownianReal.aemeasurable 1)
  have hBAE : (fun omegaB : ΩB => (bridgeNoise B omegaB, B 1 omegaB)) ⁻¹' initialSurvival x
      =ᵐ[PB] brownianStrictSurvival := by
    filter_upwards [ae_bridgeNoise_eq B PB hB] with omegaB homega
    apply propext
    rw [Set.mem_preimage, mem_initialSurvival_iff]
    have he (t : BridgeTime) : bridgePath 0 1 (B 1 omegaB) (bridgeNoise B omegaB) t =
        B ⟨(t : ℝ), t.property.1⟩ omegaB := by
      simp only [bridgePath, ContinuousMap.coe_mk, mul_zero, zero_add, Real.sqrt_one, one_mul]
      rw [homega t]
      ring
    simp only [he, brownianStrictSurvival, Set.mem_setOf_eq]
  have hBSn : NullMeasurableSet brownianStrictSurvival PB :=
    (hBPreAE.nullMeasurableSet_preimage (measurableSet_initialSurvival x)).congr hBAE
  have hWC : weakCrossing = strictSurvivalᶜ := by
    ext omega
    simp only [weakCrossing, strictSurvival, Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
  have hBWC : brownianWeakCrossing = brownianStrictSurvivalᶜ := by
    ext omegaB
    simp only [brownianWeakCrossing, brownianStrictSurvival, Set.mem_setOf_eq,
      Set.mem_compl_iff, not_forall, not_lt]
  have hCSle : CS * R ≤ (CT + CI + CS) * R := by
    nlinarith only [mul_nonneg hCT.le hR.le, mul_nonneg hCI.le hR.le]
  have hTCle : (CT + CI) * R ≤ (CT + CI + CS) * R := by
    nlinarith only [mul_nonneg hCS.le hR.le]
  refine ⟨hInitF.1, hEnergy, hM, hW, ?_⟩
  by_cases hxzero : x = 0
  · have hSzero : strictSurvival = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro omega ho
      change M omega < x * Real.sqrt (rawEnergy omega) at ho
      rw [hxzero, zero_mul] at ho
      exact (not_lt_of_ge (Shao.absMax_nonneg (population omega) hn)) ho
    have hBSzero : brownianStrictSurvival = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro omegaB ho
      have h0 := ho (0 : BridgeTime)
      rw [hxzero] at h0
      exact (not_lt_of_ge (abs_nonneg _)) h0
    have hCzero : weakCrossing = Set.univ := by rw [hWC, hSzero, Set.compl_empty]
    have hBCzero : brownianWeakCrossing = Set.univ := by rw [hBWC, hBSzero, Set.compl_empty]
    simp only [hSzero, hBSzero, hCzero, hBCzero, measureReal_empty, probReal_univ,
      sub_self, abs_zero, Set.empty_inter, Set.univ_inter]
    exact ⟨by positivity, by positivity, fun v => ⟨by positivity, (hEnd v).trans hCSle⟩⟩
  have hx : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxzero)
  have hReflection : SourceActualLocalProfileBudget.HalflineReflectionIdentities Q := by
    constructor
    · intro w y T z _hw hT hy hz
      exact Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula B PB hB w y T z hT hy hz
    · intro w y T z _hw hT hy hz
      exact Shao.C2.BridgeLowerIdentification.bridge_lower_formula B PB hB w y T z hT hy hz
  have hBudget := hTransfer PB B hB hReflection hRegular hSmall rho n hn h2 hmean hsecond x hx0 hx1
  have hq (a : Shao.Path n) (sigma : LabelPerm n) :
      Shao.energy (Spitzer.reorder a sigma) = Shao.energy a := by
    simpa only [Shao.energy, Spitzer.reorder] using Equiv.sum_comp sigma (fun i => (a i)^2)
  have hs (a : Shao.Path n) (sigma : LabelPerm n) :
      Shao.prefixSum (Spitzer.reorder a sigma) n = Shao.prefixSum a n := by
    simpa only [Shao.prefixSum_length, Spitzer.reorder] using Equiv.sum_comp sigma a
  have hWI (a : Shao.Path n) (sigma : LabelPerm n) :
      Shao.C1.normalizedEndpoint (Spitzer.reorder a sigma) = Shao.C1.normalizedEndpoint a := by
    simp only [Shao.C1.normalizedEndpoint, hq, hs]
  let Y : Fin n → Shao.Path n → ℝ := fun i a => a i
  have hY (i : Fin n) : Measurable (Y i) := measurable_pi_apply i
  have hYL (i : Fin n) : IdentDistrib (Y i) (id : ℝ → ℝ) P rho := by
    refine ⟨(hY i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [Measure.map_id] using
      (measurePreserving_eval (μ := fun _ : Fin n => rho) i).map_eq
  have hYIndep : iIndepFun Y P :=
    iIndepFun_pi (X := fun _ : Fin n => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)
  have hIPerm (a : Shao.Path n) (sigma : LabelPerm n) : I (Spitzer.reorder a sigma) = I a := by
    simp only [I, Shao.C2.RawInitialCompletion.rawInitial, hq, hs]
  have hAlive (a : Shao.Path n) (sigma : LabelPerm n) :
      sourceAlive .interval a x n sigma ↔
        Shao.absMax (Spitzer.reorder a sigma) hn < actualWall a x := by
    constructor
    · intro ha
      obtain ⟨k, hk, hkn, hEq⟩ := Shao.absMax_attained (Spitzer.reorder a sigma) hn
      rw [hEq]
      exact abs_lt.mpr (ha.2.2 k hkn)
    · intro ha
      have hw : 0 < actualWall a x := (Shao.absMax_nonneg (Spitzer.reorder a sigma) hn).trans_lt ha
      have hqpos : 0 < Shao.energy a := by
        by_contra hh
        have he : Shao.energy a = 0 := le_antisymm (le_of_not_gt hh) (Shao.energy_nonneg a)
        simpa only [actualWall, he, Real.sqrt_zero, mul_zero, lt_self_iff_false] using hw
      have hp (k : ℕ) (hkn : k ≤ n) :
          |Shao.prefixSum (Spitzer.reorder a sigma) k| < actualWall a x := by
        by_cases hk : k = 0
        · simpa only [hk, Shao.prefixSum_zero, abs_zero] using hw
        · exact (Shao.le_absMax (Spitzer.reorder a sigma) hn k (Nat.one_le_iff_ne_zero.mpr hk) hkn).trans_lt ha
      refine ⟨hqpos, ?_, ?_⟩
      · have hz := abs_lt.mp (hp n le_rfl)
        rw [hs] at hz
        exact hz
      · intro k hk
        exact abs_lt.mp (hp k hk)
  have hAeq (p : Shao.Path n × LabelPerm n) :
      (if sourceAlive .interval p.1 x n p.2 then (1 : ℝ) else 0) = A (randomReorder p) := by
    simp only [A, Set.indicator, S, Set.mem_setOf_eq, randomReorder, hq, hAlive, actualWall]
  let lambda : Measure (LabelPerm n) := uniformPermutationLaw n
  let eta : Measure (Ω × LabelPerm n) := mu.prod lambda
  let Phi : (Ω × LabelPerm n) → (Shao.Path n × LabelPerm n) := fun p => (population p.1, p.2)
  have hPhi : AEMeasurable Phi eta := hPop.prodMap measurable_id.aemeasurable
  have hPhiMap : Measure.map Phi eta = revealLaw P := by
    have he := Measure.map_prod_map_of_aemeasurable mu lambda hPop measurable_id.aemeasurable
    rw [hPopMap, Measure.map_id] at he
    exact he.symm
  have hPhiPair : IdentDistrib Phi (id : Shao.Path n × LabelPerm n → Shao.Path n × LabelPerm n)
      eta (revealLaw P) :=
    ⟨hPhi, measurable_id.aemeasurable, by simpa only [Measure.map_id] using hPhiMap⟩
  have hTMap : Measure.map (randomReorder (n := n)) (revealLaw P) = P :=
    iid_randomPermutation_map_eq_pi P rho Y hY hYIndep hYL
  have hRm : Measurable (randomReorder (n := n)) := by
    apply measurable_from_prod_countable_left
    intro sigma
    exact Measurable.of_eval (fun i => measurable_pi_apply (sigma i))
  have hTPair : IdentDistrib (randomReorder (n := n)) (id : Shao.Path n → Shao.Path n)
      (revealLaw P) P :=
    ⟨hRm.aemeasurable, measurable_id.aemeasurable, by simpa only [Measure.map_id] using hTMap⟩
  have hZPair : IdentDistrib (fun p => randomReorder (Phi p)) (id : Shao.Path n → Shao.Path n) eta P :=
    (hPhiPair.comp hRm).trans hTPair
  have hAm : Measurable A := measurable_const.indicator hSm
  have hIm : Measurable I := Shao.C2.RawInitialCompletion.measurable_rawInitial n Q x
  have hAi : Integrable A P := (integrable_const (1 : ℝ)).indicator hSm
  have hIi : Integrable I P := (Shao.C2.RawInitialCompletion.integrable_rawInitial_and_joint n Q P x 0).1
  have hAiMu : Integrable (fun omega => A (population omega)) mu :=
    (hPopPair.comp hAm).integrable_iff.mpr hAi
  have hIiMu : Integrable (fun omega => I (population omega)) mu :=
    (hPopPair.comp hIm).integrable_iff.mpr hIi
  have hMasked (m : Shao.Path n → ℝ) (hmm : Measurable m) (hmb : ∀ a, |m a| ≤ 1)
      (hInv : PermutationInvariant m) :
      |(∫ omega : Ω, m (population omega) *
        (A (population omega) - I (population omega)) ∂mu)| ≤ CT * R := by
    let f : Shao.Path n × LabelPerm n → ℝ := fun p => m p.1 *
      ((if sourceAlive .interval p.1 x n p.2 then 1 else 0) -
        sourceValue .interval (eventCompletionKernel .interval Q) p.1 x 0 p.2)
    let g : Shao.Path n → ℝ := fun a => m a * (A a - I a)
    have hb := hBudget.2.2.2 m hmm hmb hInv
    have hfi : Integrable f (revealLaw P) := hb.1
    have hfb : |(∫ p, f p ∂revealLaw P)| ≤ CT * R := hb.2
    have hfAE : AEMeasurable f (Measure.map Phi eta) := by
      rw [hPhiMap]
      exact hfi.aestronglyMeasurable.aemeasurable
    have hFlaw := hPhiPair.comp_of_aemeasurable hfAE
    have hgm : Measurable g := hmm.mul (hAm.sub hIm)
    have hEq (p : Ω × LabelPerm n) : f (Phi p) = g (randomReorder (Phi p)) := by
      have hi : sourceValue .interval (eventCompletionKernel .interval Q)
          (population p.1) x 0 p.2 = I (population p.1) := ((hInitF.2 p.2).1 p.1).1
      dsimp only [f, g, Phi]
      rw [hAeq (population p.1, p.2), hi, ← hIPerm (population p.1) p.2]
      simpa only [randomReorder] using
        congrArg (fun z : ℝ => z * (A (randomReorder (Phi p)) - I (randomReorder (Phi p))))
          (hInv (population p.1) p.2).symm
    have hIntEq : (∫ p, f p ∂revealLaw P) =
        ∫ omega : Ω, m (population omega) * (A (population omega) - I (population omega)) ∂mu := by
      calc
        _ = ∫ p, f (Phi p) ∂eta := hFlaw.integral_eq.symm
        _ = ∫ p, g (randomReorder (Phi p)) ∂eta := integral_congr_ae (ae_of_all _ fun p => hEq p)
        _ = ∫ a, g a ∂P := (hZPair.comp hgm).integral_eq
        _ = _ := (hPopPair.comp hgm).integral_eq.symm
    rw [← hIntEq]
    exact hfb
  have hSprob : mu.real strictSurvival = P.real S := hEvent S hSm
  have hAIntegral : (∫ omega : Ω, A (population omega) ∂mu) = mu.real strictSurvival := by
    calc
      _ = ∫ a, A a ∂P := (hPopPair.comp hAm).integral_eq
      _ = P.real S := integral_indicator_one hSm
      _ = _ := hSprob.symm
  have hIIntegralEq : (∫ omega : Ω, I (population omega) ∂mu) =
      ∫ omega : Ω, sourceValue .interval (eventCompletionKernel .interval Q)
        (population omega) x 0 (Equiv.refl (Fin n)) ∂mu := by
    apply integral_congr_ae
    exact ae_of_all _ fun omega => (((hInitF.2 (Equiv.refl (Fin n))).1 omega).1).symm
  have hInitialMarg : |(∫ omega : Ω, I (population omega) ∂mu) -
      PB.real brownianStrictSurvival| ≤ CI * R := by
    rw [hIIntegralEq]
    exact (hInitF.2 (Equiv.refl (Fin n))).2.2.1
  have hStrictMarg : |mu.real strictSurvival - PB.real brownianStrictSurvival| ≤ (CT + CI) * R := by
    have ht := hMasked (fun _ => 1) measurable_const (fun _ => by norm_num) (fun _ _ => rfl)
    simp only [one_mul] at ht
    rw [integral_sub hAiMu hIiMu, hAIntegral] at ht
    calc
      _ ≤ |mu.real strictSurvival - (∫ omega : Ω, I (population omega) ∂mu)| +
          |(∫ omega : Ω, I (population omega) ∂mu) - PB.real brownianStrictSurvival| := abs_sub_le _ _ _
      _ ≤ CT * R + CI * R := add_le_add ht hInitialMarg
      _ = _ := by ring
  have hWeakMarg : |mu.real weakCrossing - PB.real brownianWeakCrossing| ≤ (CT + CI) * R := by
    rw [hWC, hBWC, probReal_compl_eq_one_sub₀ hSn, probReal_compl_eq_one_sub₀ hBSn]
    have he : (1 - mu.real strictSurvival) - (1 - PB.real brownianStrictSurvival) =
        -(mu.real strictSurvival - PB.real brownianStrictSurvival) := by ring
    rw [he, abs_neg]
    exact hStrictMarg
  refine ⟨hStrictMarg.trans hTCle, hWeakMarg.trans hTCle, ?_⟩
  intro v
  let E : Set (Shao.Path n) := {a | Shao.C1.normalizedEndpoint a ≤ v}
  let mv : Shao.Path n → ℝ := E.indicator (fun _ => (1 : ℝ))
  have hEm : MeasurableSet E := measurableSet_le Shao.C1.measurable_normalizedEndpoint measurable_const
  have hmvm : Measurable mv := measurable_const.indicator hEm
  have hmvb (a : Shao.Path n) : |mv a| ≤ 1 := by simp only [mv, Set.indicator]; split_ifs <;> norm_num
  have hmvInv : PermutationInvariant mv := by
    intro a sigma
    simp only [mv, Set.indicator, E, Set.mem_setOf_eq, hWI]
  have hJointInt := (hAi.bdd_mul hmvm.aestronglyMeasurable
    (ae_of_all _ fun a => by simpa only [Real.norm_eq_abs] using hmvb a))
  have hJointIntI := (hIi.bdd_mul hmvm.aestronglyMeasurable
    (ae_of_all _ fun a => by simpa only [Real.norm_eq_abs] using hmvb a))
  have hJointMu : Integrable (fun omega => mv (population omega) * A (population omega)) mu :=
    (hPopPair.comp (hmvm.mul hAm)).integrable_iff.mpr hJointInt
  have hJointMuI : Integrable (fun omega => mv (population omega) * I (population omega)) mu :=
    (hPopPair.comp (hmvm.mul hIm)).integrable_iff.mpr hJointIntI
  have hProdIndicator : (fun a => mv a * A a) = (S ∩ E).indicator (fun _ => (1 : ℝ)) := by
    funext a
    by_cases hs : a ∈ S <;> by_cases he : a ∈ E <;> simp [mv, A, hs, he]
  have hJointProbability : (∫ omega : Ω, mv (population omega) * A (population omega) ∂mu) =
      mu.real (strictSurvival ∩ {omega : Ω | W omega ≤ v}) := by
    calc
      _ = ∫ a, mv a * A a ∂P := (hPopPair.comp (hmvm.mul hAm)).integral_eq
      _ = P.real (S ∩ E) := by rw [hProdIndicator]; exact integral_indicator_one (hSm.inter hEm)
      _ = _ := (hEvent (S ∩ E) (hSm.inter hEm)).symm
  have hJointIeq : (∫ omega : Ω, mv (population omega) * I (population omega) ∂mu) =
      ∫ omega : Ω, (if W omega ≤ v then sourceValue .interval (eventCompletionKernel .interval Q)
        (population omega) x 0 (Equiv.refl (Fin n)) else 0) ∂mu := by
    apply integral_congr_ae
    apply ae_of_all
    intro omega
    simp only [mv, Set.indicator, E, Set.mem_setOf_eq]
    split_ifs <;> simp only [one_mul, zero_mul]
    exact (((hInitF.2 (Equiv.refl (Fin n))).1 omega).1).symm
  have hInitialJoint : |(∫ omega : Ω, mv (population omega) * I (population omega) ∂mu) -
      PB.real (brownianStrictSurvival ∩ {omegaB : ΩB | B 1 omegaB ≤ v})| ≤ CI * R := by
    rw [hJointIeq]
    exact ((hInitF.2 (Equiv.refl (Fin n))).2.2.2 v).2
  have hStrictJoint : |mu.real (strictSurvival ∩ {omega : Ω | W omega ≤ v}) -
      PB.real (brownianStrictSurvival ∩ {omegaB : ΩB | B 1 omegaB ≤ v})| ≤ (CT + CI) * R := by
    have ht := hMasked mv hmvm hmvb hmvInv
    simp only [mul_sub] at ht
    rw [integral_sub hJointMu hJointMuI, hJointProbability] at ht
    calc
      _ ≤ |mu.real (strictSurvival ∩ {omega : Ω | W omega ≤ v}) -
            (∫ omega : Ω, mv (population omega) * I (population omega) ∂mu)| +
          |(∫ omega : Ω, mv (population omega) * I (population omega) ∂mu) -
            PB.real (brownianStrictSurvival ∩ {omegaB : ΩB | B 1 omegaB ≤ v})| := abs_sub_le _ _ _
      _ ≤ CT * R + CI * R := add_le_add ht hInitialJoint
      _ = _ := by ring
  have hSubtract : mu.real (weakCrossing ∩ {omega : Ω | W omega ≤ v}) =
      mu.real {omega : Ω | W omega ≤ v} - mu.real (strictSurvival ∩ {omega : Ω | W omega ≤ v}) := by
    have hh := measureReal_inter_add_sdiff₀ (s := {omega : Ω | W omega ≤ v}) hSn
    have he : {omega : Ω | W omega ≤ v} \ strictSurvival =
        weakCrossing ∩ {omega : Ω | W omega ≤ v} := by rw [hWC]; ext omega; simp [and_comm]
    rw [Set.inter_comm _ strictSurvival, he] at hh
    linarith only [hh]
  have hBSubtract : PB.real (brownianWeakCrossing ∩ {omegaB : ΩB | B 1 omegaB ≤ v}) =
      PB.real {omegaB : ΩB | B 1 omegaB ≤ v} -
        PB.real (brownianStrictSurvival ∩ {omegaB : ΩB | B 1 omegaB ≤ v}) := by
    have hh := measureReal_inter_add_sdiff₀ (s := {omegaB : ΩB | B 1 omegaB ≤ v}) hBSn
    have he : {omegaB : ΩB | B 1 omegaB ≤ v} \ brownianStrictSurvival =
        brownianWeakCrossing ∩ {omegaB : ΩB | B 1 omegaB ≤ v} := by rw [hBWC]; ext omegaB; simp [and_comm]
    rw [Set.inter_comm _ brownianStrictSurvival, he] at hh
    linarith only [hh]
  refine ⟨hStrictJoint.trans hTCle, ?_⟩
  rw [hSubtract, hBSubtract]
  have he : (mu.real {omega : Ω | W omega ≤ v} -
      mu.real (strictSurvival ∩ {omega : Ω | W omega ≤ v})) -
      (PB.real {omegaB : ΩB | B 1 omegaB ≤ v} -
        PB.real (brownianStrictSurvival ∩ {omegaB : ΩB | B 1 omegaB ≤ v})) =
      (mu.real {omega : Ω | W omega ≤ v} - PB.real {omegaB : ΩB | B 1 omegaB ≤ v}) -
      (mu.real (strictSurvival ∩ {omega : Ω | W omega ≤ v}) -
        PB.real (brownianStrictSurvival ∩ {omegaB : ΩB | B 1 omegaB ≤ v})) := by ring
  rw [he]
  calc
    _ ≤ |mu.real {omega : Ω | W omega ≤ v} - PB.real {omegaB : ΩB | B 1 omegaB ≤ v}| +
      |mu.real (strictSurvival ∩ {omega : Ω | W omega ≤ v}) -
        PB.real (brownianStrictSurvival ∩ {omegaB : ΩB | B 1 omegaB ≤ v})| := abs_sub _ _
    _ ≤ CS * R + (CT + CI) * R := add_le_add (hEnd v) hStrictJoint
    _ = _ := by ring

end Shao.Probability.SourceOriginalBrownianComparison
