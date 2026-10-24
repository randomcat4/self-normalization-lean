/- Mathematical candidate only: no production source or Lean/AX execution.
   One public head; no new definitions or instances.
   The two signed events use the original positive prefixes 1,...,n. -/
import Shao.Probability.SourceOriginalIIDHalflineBudget
import Shao.Probability.SourceTerminalEnvelope
import Shao.Probability.SourceScalarInitialBudget
import Shao.Probability.SourceOriginalZeroEnergyBudget
import Shao.Probability.SourceOriginalZeroWallBudget
import Shao.C2.BridgeUpperAffineIdentification
import Shao.C2.BridgeLowerIdentification
import Shao.C2.BridgeEndpointIndependence
import Shao.C2.EndpointCDFTransfer
import Shao.C2.InitialCompletionError

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000

noncomputable section
namespace Shao.Probability.SourceOriginalHalflineComparison
open MeasureTheory ProbabilityTheory
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.Probability.SourcePermutationReveal
open SourceActualLocalProfileBudget SourceSeparatedOvershoot
open scoped BigOperators NNReal

theorem original_iid_signed_halfline_compact_comparison :
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
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
          letI : MeasurableSpace (LabelPerm n) := ⊤
          let labelLaw : Measure (LabelPerm n) := uniformPermutationLaw n
          let jointLaw : Measure (Ω × LabelPerm n) := mu.prod labelLaw
          let pairedPopulation : Ω × LabelPerm n → Shao.Path n × LabelPerm n :=
            fun p => (population p.1, p.2)
          let shuffled : Ω × LabelPerm n → Shao.Path n :=
            fun p => Shao.Probability.Spitzer.reorder (population p.1) p.2
          let Q : Measure BridgeNoise := bridgeLaw B PB
          HasLaw population P mu ∧
          HasLaw pairedPopulation (P.prod labelLaw) jointLaw ∧
          HasLaw shuffled P jointLaw ∧
          (∀ omega : Ω,
            Shao.energy (population omega) = rawEnergy omega ∧
            Shao.prefixSum (population omega) n = rawTerminal omega ∧
            W omega = if 0 < rawEnergy omega then
              rawTerminal omega / Real.sqrt (rawEnergy omega) else 0) ∧
          (∀ p : Ω × LabelPerm n,
            Shao.energy (shuffled p) = rawEnergy p.1 ∧
            Shao.prefixSum (shuffled p) n = rawTerminal p.1 ∧
            Shao.C1.normalizedEndpoint (shuffled p) = W p.1) ∧
          ∀ (s x : ℝ), (s = 1 ∨ s = -1) → 0 ≤ x → x ≤ 1 →
            let signedMax : Ω → ℝ := fun omega => Shao.upperMax (s • population omega) hn
            let J : MonitoredDomain := if s = 1 then .upper else .lower
            let V0 : LabelPerm n → Ω → ℝ := fun sigma omega =>
              sourceValue J (eventCompletionKernel J Q) (population omega) x 0 sigma
            let A : Set Ω := {omega | signedMax omega < x * Real.sqrt (rawEnergy omega)}
            let AB : Set ΩB := {omegaB | ∀ t : BridgeTime,
              s * B ⟨(t : ℝ), t.property.1⟩ omegaB < x}
            (∀ sigma : LabelPerm n,
              (∀ omega : Ω,
                V0 sigma omega = if 0 < rawEnergy omega then
                  eventCompletionKernel J Q (x, 0, 1, W omega) else 0) ∧
              Integrable (V0 sigma) mu) ∧
            Integrable (A.indicator (fun _ : Ω => (1 : ℝ))) mu ∧
            Integrable (AB.indicator (fun _ : ΩB => (1 : ℝ))) PB ∧
            |mu.real A - PB.real AB| ≤ C * R ∧
            |mu.real {omega : Ω | x * Real.sqrt (rawEnergy omega) ≤ signedMax omega} -
              PB.real {omegaB : ΩB | ∃ t : BridgeTime,
                x ≤ s * B ⟨(t : ℝ), t.property.1⟩ omegaB}| ≤ C * R ∧
            ∀ v : ℝ,
              Integrable (fun omega : Ω => if W omega ≤ v then
                A.indicator (fun _ : Ω => (1 : ℝ)) omega else 0) mu ∧
              Integrable (fun omegaB : ΩB => if B 1 omegaB ≤ v then
                AB.indicator (fun _ : ΩB => (1 : ℝ)) omegaB else 0) PB ∧
              |mu.real {omega : Ω | omega ∈ A ∧ W omega ≤ v} -
                PB.real {omegaB : ΩB | omegaB ∈ AB ∧ B 1 omegaB ≤ v}| ≤ C * R ∧
              |mu.real {omega : Ω |
                  x * Real.sqrt (rawEnergy omega) ≤ signedMax omega ∧ W omega ≤ v} -
                PB.real {omegaB : ΩB |
                  (∃ t : BridgeTime, x ≤ s * B ⟨(t : ℝ), t.property.1⟩ omegaB) ∧
                    B 1 omegaB ≤ v}| ≤ C * R := by
  classical
  obtain ⟨CB, hCB, hLocalB⟩ :=
    SourceOriginalIIDHalflineBudget.original_iid_actual_cutoff_two_halfline_budget
  obtain ⟨CE, hCE, hTerminalE⟩ := Shao.Probability.actual_terminal_at_energy_cutoff
  obtain ⟨CG, hCG, hHostG⟩ := SourceScalarInitialBudget.finite_second_analytic_initial_host_gap
  obtain ⟨Cs, hCs, hScalar⟩ := SourceScalarInitialBudget.finite_second_scalar_closed_cdf_budget
  obtain ⟨C0, hC0, hZeroWall⟩ :=
    SourceOriginalZeroWallBudget.original_iid_one_sided_zero_wall_budget
  refine ⟨1 + 2 * CB + 2 * CE + CG + 3 * Cs + 16 + C0, by positivity, ?_⟩
  intro Ω ΩB _ _ B PB _ hB mu rho _ _ n hn X hX hIndep hLaw h2 hmean hsecond
    population rawEnergy rawTerminal W sigmaSq scale normalizedLaw R P
    labelLaw jointLaw pairedPopulation shuffled Q
  letI : MeasurableSpace (LabelPerm n) := ⊤
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw B PB hB
  letI : IsProbabilityMeasure labelLaw := by dsimp [labelLaw]; infer_instance
  letI : IsProbabilityMeasure jointLaw := by dsimp [jointLaw]; infer_instance
  have hPopulation : AEMeasurable population mu := AEMeasurable.of_eval hX
  have hMap : Measure.map population mu = P := by
    change Measure.map (fun omega i => X i omega) mu = _
    rw [hIndep.map_fun_eq_pi_map hX]
    congr 1
    funext i
    simpa only [Measure.map_id] using (hLaw i).map_eq
  have hPopulationLaw : HasLaw population P mu := ⟨hPopulation, hMap⟩
  have hPhi : AEMeasurable pairedPopulation jointLaw :=
    hPopulation.prodMap measurable_id.aemeasurable
  have hPairedMap : Measure.map pairedPopulation jointLaw = P.prod labelLaw := by
    have he := Measure.map_prod_map_of_aemeasurable mu labelLaw
      hPopulation measurable_id.aemeasurable
    rw [hMap, Measure.map_id] at he
    exact he.symm
  have hPairedLaw : HasLaw pairedPopulation (P.prod labelLaw) jointLaw := ⟨hPhi, hPairedMap⟩
  have hPair : IdentDistrib population (id : Shao.Path n → Shao.Path n) mu P :=
    ⟨hPopulation, measurable_id.aemeasurable, by simpa only [Measure.map_id] using hMap⟩
  have hRandomMeas : Measurable (randomReorder : Shao.Path n × LabelPerm n → Shao.Path n) := by
    apply measurable_from_prod_countable_left
    intro pi
    exact Measurable.of_eval fun i => measurable_pi_apply (pi i)
  have hCanonicalIndep : iIndepFun (fun i : Fin n => Function.eval i) P :=
    iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)
  have hCanonicalLaw (i : Fin n) : IdentDistrib (Function.eval i) (id : ℝ → ℝ) P rho := by
    refine ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    exact (measurePreserving_eval (fun _ : Fin n => rho) i).map_eq.trans Measure.map_id.symm
  have hRandomMap : Measure.map randomReorder (P.prod labelLaw) = P := by
    exact iid_randomPermutation_map_eq_pi P rho
      (fun i : Fin n => Function.eval i) (fun i => measurable_pi_apply i)
      hCanonicalIndep hCanonicalLaw
  have hShuffleMeas : AEMeasurable shuffled jointLaw := hRandomMeas.comp_aemeasurable hPhi
  have hShuffleMap : Measure.map shuffled jointLaw = P := by
    change Measure.map (randomReorder ∘ pairedPopulation) jointLaw = P
    rw [← AEMeasurable.map_map_of_aemeasurable hRandomMeas.aemeasurable hPhi, hPairedMap]
    exact hRandomMap
  have hShuffleLaw : HasLaw shuffled P jointLaw := ⟨hShuffleMeas, hShuffleMap⟩
  have hReorderEnergy (a : Shao.Path n) (pi : LabelPerm n) :
      Shao.energy (Spitzer.reorder a pi) = Shao.energy a := by
    dsimp only [Shao.energy, Spitzer.reorder]
    exact Equiv.sum_comp pi (fun i => (a i) ^ 2)
  have hReorderTerminal (a : Shao.Path n) (pi : LabelPerm n) :
      Shao.prefixSum (Spitzer.reorder a pi) n = Shao.prefixSum a n := by
    simp only [Shao.prefixSum_length, Spitzer.reorder]
    exact Equiv.sum_comp pi a
  have hReorderW (a : Shao.Path n) (pi : LabelPerm n) :
      Shao.C1.normalizedEndpoint (Spitzer.reorder a pi) = Shao.C1.normalizedEndpoint a := by
    simp only [Shao.C1.normalizedEndpoint, hReorderEnergy, hReorderTerminal]
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
  have hShuffleState (p : Ω × LabelPerm n) :
      Shao.energy (shuffled p) = rawEnergy p.1 ∧
      Shao.prefixSum (shuffled p) n = rawTerminal p.1 ∧
      Shao.C1.normalizedEndpoint (shuffled p) = W p.1 := by
    exact ⟨(hReorderEnergy _ _).trans (hState p.1).1,
      (hReorderTerminal _ _).trans (hState p.1).2.1, hReorderW _ _⟩
  refine ⟨hPopulationLaw, hPairedLaw, hShuffleLaw, hState, hShuffleState, ?_⟩
  intro s x hs hx hx1 signedMax J V0 A AB
  have hJ : J = .upper ∨ J = .lower := by
    dsimp only [J]
    split_ifs <;> simp
  have hscale : scale = Real.sqrt sigmaSq * Real.sqrt (n : ℝ) := by
    dsimp only [scale]
    rw [Real.sqrt_mul (show 0 ≤ (n : ℝ) by positivity)]
    exact mul_comm _ _
  have hGeometry := Shao.Probability.raw_truncation_budget_suffix_geometry rho n hn h2 hsecond
  have hRpos : 0 < R := hGeometry.1
  have hRone : R ≤ 1 := hGeometry.2.1
  have hR : 0 ≤ R := hRpos.le
  let h : ℝ := 4 * (n : ℝ) * sigmaSq * R ^ 2
  have hh : 0 < h := hGeometry.2.2.2.1
  have hReflection : SourceActualLocalProfileBudget.HalflineReflectionIdentities Q := by
    constructor
    · intro w y T z hw hT hy hz
      exact Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula B PB hB w y T z hT hy hz
    · intro w y T z hw hT hy hz
      exact Shao.C2.BridgeLowerIdentification.bridge_lower_formula B PB hB w y T z hT hy hz
  have hK := SourceActualLocalProfileBudget.actual_halfline_kernel_data Q hReflection J hJ
  have hF := eventCompletionKernel_data J Q
  have hAm : AEMeasurable (A.indicator (fun _ : Ω => (1 : ℝ))) mu := by
    have hm : Measurable (fun a : Shao.Path n => Shao.upperMax (s • a) hn) :=
      (Shao.measurable_upperMax hn).comp (by fun_prop)
    exact (measurable_const.indicator
      (measurableSet_lt hm (measurable_const.mul Shao.measurable_energy.sqrt))).aemeasurable.comp_aemeasurable hPopulation
  have hAi : Integrable (A.indicator (fun _ : Ω => (1 : ℝ))) mu :=
    Integrable.of_bound hAm.aestronglyMeasurable 1 (ae_of_all _ fun omega => by
      simp only [Set.indicator]; split_ifs <;> norm_num)
  let K : ℝ → ℝ := fun u => eventCompletionKernel J Q (x, 0, 1, u)
  have hKm : Measurable K := hF.1.comp (by fun_prop)
  have hK0 (u : ℝ) : 0 ≤ K u := (hF.2.1 _).1
  have hK1 (u : ℝ) : K u ≤ 1 := (hF.2.1 _).2
  have hExterior (w y T z : ℝ) (hz : ¬ Interior J w z) :
      eventCompletionKernel J Q (w, y, T, z) = 0 := by
    rcases hJ with hJu | hJl
    · rw [hJu] at hz ⊢
      change Q.real (strictUpper w y T z) = 0
      have he : strictUpper w y T z = ∅ := by
        ext g
        constructor
        · intro hg
          exact (hz (by simpa only [Interior, (bridgePath_endpoints y T z g).2] using hg 1)).elim
        · intro hg
          exact hg.elim
      rw [he, measureReal_empty]
    · rw [hJl] at hz ⊢
      change Q.real (strictLower w y T z) = 0
      have he : strictLower w y T z = ∅ := by
        ext g
        constructor
        · intro hg
          exact (hz (by simpa only [Interior, (bridgePath_endpoints y T z g).2] using hg 1)).elim
        · intro hg
          exact hg.elim
      rw [he, measureReal_empty]
  have hZeroSource (a : Shao.Path n) (r : ℕ) (pi : LabelPerm n) :
      sourceValue J (eventCompletionKernel J Q) a 0 r pi = 0 := by
    have hd : ¬ sourceAlive J a 0 r pi := by
      intro ha
      have h0 := ha.2.2 0 (Nat.zero_le r)
      rcases hJ with hJu | hJl
      · simpa only [hJu, Interior, actualWall, zero_mul, Shao.prefixSum_zero,
          lt_self_iff_false] using h0
      · simpa only [hJl, Interior, actualWall, zero_mul, Shao.prefixSum_zero, neg_zero,
          lt_self_iff_false] using h0
    simp only [sourceValue, if_neg hd]
  have hZeroKernel (u : ℝ) : eventCompletionKernel J Q (0, 0, 1, u) = 0 := by
    rcases hJ with hJu | hJl
    · rw [hJu]
      change Q.real (strictUpper 0 0 1 u) = 0
      have he : strictUpper 0 0 1 u = ∅ := by
        ext g
        constructor
        · intro hg
          have h0 := hg 0
          simpa only [(bridgePath_endpoints 0 1 u g).1, lt_self_iff_false] using h0
        · intro hg
          exact hg.elim
      rw [he, measureReal_empty]
    · rw [hJl]
      change Q.real (strictLower 0 0 1 u) = 0
      have he : strictLower 0 0 1 u = ∅ := by
        ext g
        constructor
        · intro hg
          have h0 := hg 0
          simpa only [(bridgePath_endpoints 0 1 u g).1, neg_zero, lt_self_iff_false] using h0
        · intro hg
          exact hg.elim
      rw [he, measureReal_empty]
  have hInitial (a : Shao.Path n) (pi : LabelPerm n) :
      sourceValue J (eventCompletionKernel J Q) a x 0 pi =
        if 0 < Shao.energy a then K (Shao.C1.normalizedEndpoint a) else 0 := by
    by_cases hq : 0 < Shao.energy a
    · rw [if_pos hq]
      by_cases hx0 : x = 0
      · rw [hx0, hZeroSource]
        simpa only [K, hx0] using (hZeroKernel (Shao.C1.normalizedEndpoint a)).symm
      have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      have hroot : 0 < Real.sqrt (Shao.energy a) := Real.sqrt_pos.mpr hq
      have hw : 0 < actualWall a x := mul_pos hxp hroot
      have hInteriorZero : Interior J (actualWall a x) 0 := by
        rcases hJ with hJu | hJl
        · simpa only [hJu, Interior] using hw
        · rw [hJl]
          change -(actualWall a x) < 0
          linarith
      have hScale : eventCompletionKernel J Q
          (actualWall a x, 0, Shao.energy a, Shao.prefixSum a n) =
          K (Shao.C1.normalizedEndpoint a) := by
        rw [Shao.C1.normalizedEndpoint_of_energy_pos a hq]
        have hpath (g : BridgeNoise) (t : BridgeTime) :
            bridgePath 0 (Shao.energy a) (Shao.prefixSum a n) g t =
              Real.sqrt (Shao.energy a) *
                bridgePath 0 1 (Shao.prefixSum a n / Real.sqrt (Shao.energy a)) g t := by
          simp only [bridgePath, ContinuousMap.coe_mk, mul_zero, zero_add,
            Real.sqrt_one, one_mul]
          field_simp [ne_of_gt hroot]
        rcases hJ with hJu | hJl
        · simp only [K, hJu, eventCompletionKernel]
          apply congrArg (fun E : Set BridgeNoise => Q.real E)
          ext g
          constructor <;> intro hg t
          · have ht := hg t
            rw [hpath] at ht
            exact (mul_lt_mul_iff_right₀ hroot).mp (by simpa only [actualWall, mul_comm] using ht)
          · have ht := mul_lt_mul_of_pos_left (hg t) hroot
            rw [hpath]
            simpa only [actualWall, mul_comm] using ht
        · simp only [K, hJl, eventCompletionKernel]
          apply congrArg (fun E : Set BridgeNoise => Q.real E)
          ext g
          constructor <;> intro hg t
          · have ht := hg t
            rw [hpath] at ht
            exact (mul_lt_mul_iff_right₀ hroot).mp (by simpa only [actualWall, mul_neg, neg_mul, mul_comm] using ht)
          · have ht := mul_lt_mul_of_pos_left (hg t) hroot
            rw [hpath]
            simpa only [actualWall, mul_neg, neg_mul, mul_comm] using ht
      by_cases hz : Interior J (actualWall a x) (Shao.prefixSum a n)
      · have ha : sourceAlive J a x 0 pi := by
          refine ⟨hq, hz, ?_⟩
          intro k hk
          have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
          simpa only [hk0, Shao.prefixSum_zero] using hInteriorZero
        simp only [sourceValue, if_pos ha, Shao.prefixSum_zero, remainingEnergy,
          Shao.prefixSquares_zero, sub_zero]
        rw [hF.2.2 (actualWall a x) 0 (Shao.energy a) (Shao.prefixSum a n)
          hw hq.le (fun he => False.elim ((ne_of_gt hq) he))]
        exact hScale
      · have ha : ¬ sourceAlive J a x 0 pi := fun ha => hz ha.2.1
        rw [sourceValue, if_neg ha]
        exact ((hScale.symm.trans (hExterior _ _ _ _ hz))).symm
    · have ha : ¬ sourceAlive J a x 0 pi := fun ha => hq ha.1
      simp only [sourceValue, if_neg ha, if_neg hq]
  let V : Shao.Path n → ℝ := fun a =>
    if 0 < Shao.energy a then K (Shao.C1.normalizedEndpoint a) else 0
  have hVm : Measurable V := Measurable.ite
    (measurableSet_lt measurable_const Shao.measurable_energy)
    (hKm.comp Shao.C1.measurable_normalizedEndpoint) measurable_const
  have hVi : Integrable V P := Integrable.of_bound hVm.aestronglyMeasurable 1
    (ae_of_all _ fun a => by
      dsimp only [V]
      split_ifs
      · rw [Real.norm_eq_abs, abs_of_nonneg (hK0 _)]
        exact hK1 _
      · norm_num)
  have hInitOutput (pi : LabelPerm n) :
      (∀ omega : Ω,
        V0 pi omega = if 0 < rawEnergy omega then
          eventCompletionKernel J Q (x, 0, 1, W omega) else 0) ∧ Integrable (V0 pi) mu := by
    have he : V0 pi = V ∘ population := by
      funext omega
      exact hInitial _ _
    refine ⟨fun omega => hInitial _ _, ?_⟩
    rw [he]
    exact (hPair.comp hVm).integrable_iff.mpr hVi
  let gamma : Measure ℝ := gaussianReal 0 1
  let tuple : ΩB → BridgeNoise × ℝ := fun omega => (bridgeNoise B omega, B 1 omega)
  let E : Set (BridgeNoise × ℝ) := {p | ∀ t : BridgeTime,
    s * bridgePath 0 1 p.2 p.1 t < x}
  have hEm : MeasurableSet E := by
    have hc : Continuous (fun p : BridgeNoise × ℝ => s • bridgePath 0 1 p.2 p.1) := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun p : (BridgeNoise × ℝ) × BridgeTime =>
        s * ((1 - (p.2 : ℝ)) * 0 + (p.2 : ℝ) * p.1.2 +
          Real.sqrt 1 * p.1.1.val p.2))
      fun_prop
    have ho := ContinuousMap.isOpen_setOfPred_mapsTo
      (X := BridgeTime) isCompact_univ (isOpen_Iio (a := x))
    simpa [E, Set.MapsTo, ContinuousMap.smul_apply, smul_eq_mul] using
      (ho.preimage hc).measurableSet
  have hSection (u : ℝ) : Q.real {g : BridgeNoise | (g, u) ∈ E} = K u := by
    rcases hs with hs | hs
    · have hJu : J = .upper := by simp [J, hs]
      simp only [K, hJu, eventCompletionKernel]
      apply congrArg (fun S : Set BridgeNoise => Q.real S)
      ext g
      simp only [E, Set.mem_setOf_eq, hs, one_mul, strictUpper]
    · have hJl : J = .lower := by simp only [J, hs]; norm_num
      simp only [K, hJl, eventCompletionKernel]
      apply congrArg (fun S : Set BridgeNoise => Q.real S)
      ext g
      change (∀ t : BridgeTime, s * bridgePath 0 1 u g t < x) ↔
        ∀ t : BridgeTime, -x < bridgePath 0 1 u g t
      rw [hs]
      constructor <;> intro hg t <;> linarith [hg t]
  have hEvent : AB =ᵐ[PB] tuple ⁻¹' E := by
    filter_upwards [ae_bridgeNoise_eq B PB hB] with omega homega
    apply propext
    change (∀ t : BridgeTime, s * B ⟨(t : ℝ), t.property.1⟩ omega < x) ↔
      ∀ t : BridgeTime, s * bridgePath 0 1 (B 1 omega) (bridgeNoise B omega) t < x
    have heq (t : BridgeTime) :
        bridgePath 0 1 (B 1 omega) (bridgeNoise B omega) t =
          B ⟨(t : ℝ), t.property.1⟩ omega := by
      simp only [bridgePath, ContinuousMap.coe_mk, mul_zero, zero_add, Real.sqrt_one, one_mul]
      rw [homega t]
      ring
    simp only [heq]
  have hTuple : HasLaw tuple (Q.prod gamma) PB := bridge_endpoint_hasLaw B PB hB
  have hEventIndicator : AB.indicator (fun _ : ΩB => (1 : ℝ)) =ᵐ[PB]
      (fun omega => E.indicator (fun _ : BridgeNoise × ℝ => (1 : ℝ)) (tuple omega)) := by
    filter_upwards [hEvent] with omega homega
    exact congrArg (fun p : Prop => if p then (1 : ℝ) else 0) homega
  have hBi : Integrable (AB.indicator (fun _ : ΩB => (1 : ℝ))) PB :=
    (hTuple.integrable_comp ((integrable_const (1 : ℝ)).indicator hEm)).congr hEventIndicator.symm
  have hFubini (S : Set (BridgeNoise × ℝ)) (hS : MeasurableSet S) :
      (Q.prod gamma).real S = ∫ u : ℝ, Q.real {g : BridgeNoise | (g, u) ∈ S} ∂gamma := by
    let f : BridgeNoise × ℝ → ℝ := S.indicator (fun _ => 1)
    have hi : Integrable f (Q.prod gamma) := (integrable_const 1).indicator hS
    calc
      _ = ∫ p, f p ∂(Q.prod gamma) := (integral_indicator_one hS).symm
      _ = ∫ u : ℝ, ∫ g : BridgeNoise, f (g, u) ∂Q ∂gamma := integral_prod_symm f hi
      _ = _ := by
        apply integral_congr_ae
        exact ae_of_all _ fun u => by
          exact integral_indicator_one (hS.preimage (measurable_id.prodMk measurable_const))
  have hBrownianMarginal : PB.real AB = ∫ u : ℝ, K u ∂gamma := by
    calc
      _ = PB.real (tuple ⁻¹' E) := measureReal_congr hEvent
      _ = (Q.prod gamma).real E := hTuple.measureReal_eq hEm
      _ = ∫ u : ℝ, Q.real {g : BridgeNoise | (g, u) ∈ E} ∂gamma := hFubini E hEm
      _ = _ := integral_congr_ae (ae_of_all _ hSection)
  have hBrownianJoint (v : ℝ) :
      PB.real {omegaB : ΩB | omegaB ∈ AB ∧ B 1 omegaB ≤ v} =
        ∫ u : ℝ, (if u ≤ v then K u else 0) ∂gamma := by
    let S : Set (BridgeNoise × ℝ) := E ∩ {p | p.2 ≤ v}
    have hS : MeasurableSet S := hEm.inter (measurableSet_le measurable_snd measurable_const)
    have hEv : {omegaB : ΩB | omegaB ∈ AB ∧ B 1 omegaB ≤ v} =ᵐ[PB] tuple ⁻¹' S := by
      filter_upwards [hEvent] with omega homega
      apply propext
      exact and_congr (Iff.of_eq homega) Iff.rfl
    calc
      _ = PB.real (tuple ⁻¹' S) := measureReal_congr hEv
      _ = (Q.prod gamma).real S := hTuple.measureReal_eq hS
      _ = ∫ u : ℝ, Q.real {g : BridgeNoise | (g, u) ∈ S} ∂gamma := hFubini S hS
      _ = _ := by
        apply integral_congr_ae
        exact ae_of_all _ fun u => by
          change Q.real {g : BridgeNoise | (g, u) ∈ S} = if u ≤ v then K u else 0
          by_cases hu : u ≤ v
          · have he : {g : BridgeNoise | (g, u) ∈ S} = {g : BridgeNoise | (g, u) ∈ E} := by
              ext g
              simp only [S, Set.mem_setOf_eq, Set.mem_inter_iff, hu, and_true]
            rw [he, if_pos hu, hSection]
          · have he : {g : BridgeNoise | (g, u) ∈ S} = ∅ := by
              ext g
              simp only [S, Set.mem_setOf_eq, Set.mem_inter_iff, hu, and_false, Set.mem_empty_iff_false]
            rw [he, if_neg hu, measureReal_empty]
  have hWm : AEMeasurable W mu := Shao.C1.measurable_normalizedEndpoint.comp_aemeasurable hPopulation
  have hMaskedAi (v : ℝ) : Integrable (fun omega : Ω =>
      if W omega ≤ v then A.indicator (fun _ : Ω => (1 : ℝ)) omega else 0) mu := by
    have hm : AEMeasurable (fun omega : Ω =>
        (Set.Iic v).indicator (fun _ : ℝ => (1 : ℝ)) (W omega) *
          A.indicator (fun _ : Ω => (1 : ℝ)) omega) mu :=
      ((measurable_const.indicator measurableSet_Iic).comp_aemeasurable hWm).mul hAm
    have he : (fun omega : Ω => if W omega ≤ v then
        A.indicator (fun _ : Ω => (1 : ℝ)) omega else 0) =
      (fun omega : Ω => (Set.Iic v).indicator (fun _ : ℝ => (1 : ℝ)) (W omega) *
        A.indicator (fun _ : Ω => (1 : ℝ)) omega) := by
      funext omega
      by_cases hv : W omega ≤ v <;> simp only [Set.indicator, Set.mem_Iic, hv, ite_true, ite_false,
        one_mul, zero_mul]
    refine Integrable.of_bound (he ▸ hm).aestronglyMeasurable 1 (ae_of_all _ fun omega => ?_)
    simp only [Set.indicator]
    split_ifs <;> norm_num
  have hMaskedBi (v : ℝ) : Integrable (fun omegaB : ΩB => if B 1 omegaB ≤ v then
      AB.indicator (fun _ : ΩB => (1 : ℝ)) omegaB else 0) PB := by
    have hm : AEMeasurable (fun omega : ΩB =>
        (Set.Iic v).indicator (fun _ : ℝ => (1 : ℝ)) (B 1 omega) *
          AB.indicator (fun _ : ΩB => (1 : ℝ)) omega) PB :=
      ((measurable_const.indicator measurableSet_Iic).comp_aemeasurable
        (hB.toIsPreBrownianReal.aemeasurable 1)).mul hBi.aemeasurable
    have he : (fun omega : ΩB => if B 1 omega ≤ v then
        AB.indicator (fun _ : ΩB => (1 : ℝ)) omega else 0) =
      (fun omega : ΩB => (Set.Iic v).indicator (fun _ : ℝ => (1 : ℝ)) (B 1 omega) *
        AB.indicator (fun _ : ΩB => (1 : ℝ)) omega) := by
      funext omega
      by_cases hv : B 1 omega ≤ v <;> simp only [Set.indicator, Set.mem_Iic, hv, ite_true, ite_false,
        one_mul, zero_mul]
    refine Integrable.of_bound (he ▸ hm).aestronglyMeasurable 1 (ae_of_all _ fun omega => ?_)
    simp only [Set.indicator]
    split_ifs <;> norm_num
  let endpointLaw : Measure ℝ := P.map Shao.C1.normalizedEndpoint
  letI : IsProbabilityMeasure endpointLaw :=
    (Measure.isProbabilityMeasure_map_iff Shao.C1.measurable_normalizedEndpoint.aemeasurable).mpr inferInstance
  have hEndpointLaw : HasLaw (Shao.C1.normalizedEndpoint : Shao.Path n → ℝ) endpointLaw P :=
    ⟨Shao.C1.measurable_normalizedEndpoint.aemeasurable, rfl⟩
  have hCDF (v : ℝ) :
      |P.real {a : Shao.Path n | Shao.C1.normalizedEndpoint a ≤ v} -
        gamma.real (Set.Iic v)| ≤ Cs * R := by
    have he := hScalar rho n hn h2 hmean hsecond v
    change |P.real {a : Shao.Path n | Shao.C1.normalizedEndpoint a ≤ v} -
        gamma.real (Set.Iic v)| ≤ Cs * Shao.truncationBudget
          (Measure.map (fun z : ℝ => z / (Real.sqrt sigmaSq * Real.sqrt (n : ℝ))) rho) n 0 at he
    rw [← hscale] at he
    exact he
  have hCDFLaw (v : ℝ) : |endpointLaw.real (Set.Iic v) - gamma.real (Set.Iic v)| ≤ Cs * R := by
    have he := hEndpointLaw.measureReal_eq (measurableSet_Iic (a := v))
    change P.real {a : Shao.Path n | Shao.C1.normalizedEndpoint a ≤ v} = endpointLaw.real (Set.Iic v) at he
    rw [← he]
    exact hCDF v
  have hUnitIntegrable (f : ℝ → ℝ) (hf : Measurable f)
      (hf0 : ∀ u, 0 ≤ f u) (hf1 : ∀ u, f u ≤ 1)
      (L : Measure ℝ) [IsProbabilityMeasure L] : Integrable f L := by
    refine Integrable.of_bound hf.aestronglyMeasurable 1 (ae_of_all _ fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 u)]
    exact hf1 u
  have hAntiError (f : ℝ → ℝ) (hf : Antitone f)
      (hf0 : ∀ u, 0 ≤ f u) (hf1 : ∀ u, f u ≤ 1) :
      |(∫ u, f u ∂endpointLaw) - ∫ u, f u ∂gamma| ≤ Cs * R :=
    Shao.C2.EndpointCDFTransfer.antitone_unit_expectation_error endpointLaw gamma
      (Cs * R) (mul_nonneg hCs.le hR) hCDFLaw f hf hf0 hf1
  have hMonoError (f : ℝ → ℝ) (hf : Monotone f)
      (hf0 : ∀ u, 0 ≤ f u) (hf1 : ∀ u, f u ≤ 1) :
      |(∫ u, f u ∂endpointLaw) - ∫ u, f u ∂gamma| ≤ Cs * R := by
    have ha : Antitone (fun u => 1 - f u) := fun u v huv => sub_le_sub_left (hf huv) 1
    have he := hAntiError (fun u => 1 - f u) ha (fun u => sub_nonneg.mpr (hf1 u))
      (fun u => by linarith [hf0 u])
    have hiL := hUnitIntegrable f hf.measurable hf0 hf1 endpointLaw
    have hiG := hUnitIntegrable f hf.measurable hf0 hf1 gamma
    have hid : ((∫ u, (1 - f u) ∂endpointLaw) - ∫ u, (1 - f u) ∂gamma) =
        -((∫ u, f u ∂endpointLaw) - ∫ u, f u ∂gamma) := by
      rw [integral_sub (integrable_const 1) hiL, integral_sub (integrable_const 1) hiG]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      ring
    rwa [hid, abs_neg] at he
  have hKMonotonicity : Antitone K ∨ Monotone K := by
    rcases hJ with hJu | hJl
    · left
      intro u v huv
      simp only [K, hJu, eventCompletionKernel]
      change Q.real (strictUpper x 0 1 v) ≤ Q.real (strictUpper x 0 1 u)
      refine measureReal_mono ?_ (by finiteness)
      intro g hg t
      exact (bridgePath_mono 0 0 1 u v le_rfl huv g t).trans_lt (hg t)
    · right
      intro u v huv
      simp only [K, hJl, eventCompletionKernel]
      change Q.real (strictLower x 0 1 u) ≤ Q.real (strictLower x 0 1 v)
      refine measureReal_mono ?_ (by finiteness)
      intro g hg t
      exact (hg t).trans_le (bridgePath_mono 0 0 1 u v le_rfl huv g t)
  have hKError : |(∫ u, K u ∂endpointLaw) - ∫ u, K u ∂gamma| ≤ 2 * Cs * R := by
    have he : |(∫ u, K u ∂endpointLaw) - ∫ u, K u ∂gamma| ≤ Cs * R :=
      hKMonotonicity.elim (fun h => hAntiError K h hK0 hK1) (fun h => hMonoError K h hK0 hK1)
    nlinarith [mul_nonneg hCs.le hR]
  have hMaskedKError (v : ℝ) :
      |(∫ u, (if u ≤ v then K u else 0) ∂endpointLaw) -
        ∫ u, (if u ≤ v then K u else 0) ∂gamma| ≤ 2 * Cs * R := by
    rcases hKMonotonicity with hKa | hKm'
    · have ha : Antitone (fun u => if u ≤ v then K u else 0) := by
        intro u w huw
        by_cases hw : w ≤ v
        · have hu : u ≤ v := huw.trans hw
          simpa only [if_pos hu, if_pos hw] using hKa huw
        · by_cases hu : u ≤ v
          · simpa only [if_neg hw, if_pos hu] using hK0 u
          · simp only [if_neg hw, if_neg hu, le_refl]
      have he := hAntiError (fun u => if u ≤ v then K u else 0) ha
        (fun u => by split_ifs <;> first | exact hK0 _ | exact le_refl 0)
        (fun u => by split_ifs <;> first | exact hK1 _ | norm_num)
      nlinarith [mul_nonneg hCs.le hR]
    · let H : ℝ → ℝ := fun u => if v < u then K u else 0
      have hHm : Monotone H := by
        intro u w huw
        by_cases hu : v < u
        · have hw : v < w := hu.trans_le huw
          simpa only [H, if_pos hu, if_pos hw] using hKm' huw
        · by_cases hw : v < w
          · simpa only [H, if_neg hu, if_pos hw] using hK0 w
          · simp only [H, if_neg hu, if_neg hw, le_refl]
      have hH0 (u : ℝ) : 0 ≤ H u := by dsimp only [H]; split_ifs <;> first | exact hK0 _ | rfl
      have hH1 (u : ℝ) : H u ≤ 1 := by dsimp only [H]; split_ifs <;> first | exact hK1 _ | norm_num
      have heK := hMonoError K hKm' hK0 hK1
      have heH := hMonoError H hHm hH0 hH1
      have hKiL := hUnitIntegrable K hKm hK0 hK1 endpointLaw
      have hKiG := hUnitIntegrable K hKm hK0 hK1 gamma
      have hHiL := hUnitIntegrable H hHm.measurable hH0 hH1 endpointLaw
      have hHiG := hUnitIntegrable H hHm.measurable hH0 hH1 gamma
      have hfun : (fun u => if u ≤ v then K u else 0) = fun u => K u - H u := by
        funext u
        by_cases hu : u ≤ v
        · simp only [if_pos hu, H, if_neg (not_lt.mpr hu), sub_zero]
        · simp only [if_neg hu, H, if_pos (lt_of_not_ge hu), sub_self]
      rw [hfun, integral_sub hKiL hHiL, integral_sub hKiG hHiG]
      calc
        _ = |((∫ u, K u ∂endpointLaw) - ∫ u, K u ∂gamma) -
            ((∫ u, H u ∂endpointLaw) - ∫ u, H u ∂gamma)| := by congr 1 <;> ring
        _ ≤ |(∫ u, K u ∂endpointLaw) - ∫ u, K u ∂gamma| +
            |(∫ u, H u ∂endpointLaw) - ∫ u, H u ∂gamma| := abs_sub _ _
        _ ≤ Cs * R + Cs * R := add_le_add heK heH
        _ = _ := by ring
  have hZeroEnergy : P.real {a : Shao.Path n | Shao.energy a = 0} ≤ 16 * R :=
    SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget P rho n hn
      (fun i : Fin n => Function.eval i) (fun i => (measurable_pi_apply i).aemeasurable)
      hCanonicalIndep hCanonicalLaw h2 hsecond
  have hInitialGap : |(∫ a, V a ∂P) - PB.real AB| ≤ (2 * Cs + 16) * R := by
    have hcost := Shao.C2.InitialCompletionError.zero_energy_removal P
      Shao.C1.normalizedEndpoint Shao.energy Shao.C1.measurable_normalizedEndpoint.aemeasurable
      Shao.measurable_energy (ae_of_all _ Shao.energy_nonneg) K hKm hK0 hK1
    have hmap : (∫ u, K u ∂endpointLaw) = ∫ a : Shao.Path n, K (Shao.C1.normalizedEndpoint a) ∂P :=
      integral_map Shao.C1.measurable_normalizedEndpoint.aemeasurable hKm.aestronglyMeasurable
    rw [hmap, ← hBrownianMarginal] at hKError
    calc
      _ ≤ |(∫ a, V a ∂P) - ∫ a : Shao.Path n, K (Shao.C1.normalizedEndpoint a) ∂P| +
          |(∫ a : Shao.Path n, K (Shao.C1.normalizedEndpoint a) ∂P) - PB.real AB| := abs_sub_le _ _ _
      _ ≤ 16 * R + 2 * Cs * R := add_le_add (hcost.trans hZeroEnergy) hKError
      _ = _ := by ring
  have hMaskedInitialGap (v : ℝ) :
      |(∫ a : Shao.Path n, (if Shao.C1.normalizedEndpoint a ≤ v then V a else 0) ∂P) -
        PB.real {omegaB : ΩB | omegaB ∈ AB ∧ B 1 omegaB ≤ v}| ≤ (2 * Cs + 16) * R := by
    let f : ℝ → ℝ := fun u => if u ≤ v then K u else 0
    have hfm : Measurable f := Measurable.ite (measurableSet_le measurable_id measurable_const)
      hKm measurable_const
    have hf0 (u : ℝ) : 0 ≤ f u := by dsimp only [f]; split_ifs <;> first | exact hK0 _ | rfl
    have hf1 (u : ℝ) : f u ≤ 1 := by dsimp only [f]; split_ifs <;> first | exact hK1 _ | norm_num
    have hcost := Shao.C2.InitialCompletionError.zero_energy_removal P
      Shao.C1.normalizedEndpoint Shao.energy Shao.C1.measurable_normalizedEndpoint.aemeasurable
      Shao.measurable_energy (ae_of_all _ Shao.energy_nonneg) f hfm hf0 hf1
    have he : (fun a : Shao.Path n => if 0 < Shao.energy a then f (Shao.C1.normalizedEndpoint a) else 0) =
        (fun a : Shao.Path n => if Shao.C1.normalizedEndpoint a ≤ v then V a else 0) := by
      funext a
      dsimp only [f, V]
      split_ifs <;> rfl
    rw [he] at hcost
    have hmap : (∫ u, f u ∂endpointLaw) = ∫ a : Shao.Path n, f (Shao.C1.normalizedEndpoint a) ∂P :=
      integral_map Shao.C1.measurable_normalizedEndpoint.aemeasurable hfm.aestronglyMeasurable
    have herr := hMaskedKError v
    change |(∫ u, f u ∂endpointLaw) - ∫ u, f u ∂gamma| ≤ 2 * Cs * R at herr
    rw [hmap, ← hBrownianJoint v] at herr
    calc
      _ ≤ |(∫ a : Shao.Path n, (if Shao.C1.normalizedEndpoint a ≤ v then V a else 0) ∂P) -
          ∫ a : Shao.Path n, f (Shao.C1.normalizedEndpoint a) ∂P| +
          |(∫ a : Shao.Path n, f (Shao.C1.normalizedEndpoint a) ∂P) -
            PB.real {omegaB : ΩB | omegaB ∈ AB ∧ B 1 omegaB ≤ v}| := abs_sub_le _ _ _
      _ ≤ 16 * R + 2 * Cs * R := add_le_add (hcost.trans hZeroEnergy) herr
      _ = _ := by ring
  have hInteriorSign (w y : ℝ) : Interior J w y ↔ s * y < w := by
    rcases hs with hs | hs
    · simp [J, hs, Interior]
    · have hJl : J = .lower := by norm_num [J, hs]
      rw [hJl]
      change -w < y ↔ s * y < w
      rw [hs]
      constructor <;> intro h <;> linarith
  have hUpperLt (a : Shao.Path n) (w : ℝ) :
      Shao.upperMax a hn < w ↔ ∀ k : ℕ, 1 ≤ k → k ≤ n → Shao.prefixSum a k < w := by
    constructor
    · intro he k hk hkn
      exact (Shao.le_upperMax a hn k hk hkn).trans_lt he
    · intro he
      obtain ⟨k, hk, hkn, hmax⟩ := Shao.upperMax_attained a hn
      rw [hmax]
      exact he k hk hkn
  have hAliveHost (hxp : 0 < x) (a : Shao.Path n) (pi : LabelPerm n) :
      sourceAlive J a x n pi ↔
        Shao.maxWithZero (s • Spitzer.reorder a pi) < x * Real.sqrt (Shao.energy a) := by
    constructor
    · intro ha
      rw [Shao.maxWithZero_eq _ hn, max_lt_iff]
      refine ⟨mul_pos hxp (Real.sqrt_pos.mpr ha.1), (hUpperLt _ _).mpr ?_⟩
      intro k hk hkn
      rw [Shao.prefixSum_smul]
      exact (hInteriorSign _ _).mp (ha.2.2 k hkn)
    · intro he
      have hw : 0 < actualWall a x := (Shao.maxWithZero_nonneg _).trans_lt he
      have hq : 0 < Shao.energy a := by
        by_contra hq
        have hq0 : Shao.energy a = 0 := le_antisymm (le_of_not_gt hq) (Shao.energy_nonneg a)
        simpa only [actualWall, hq0, Real.sqrt_zero, mul_zero, lt_self_iff_false] using hw
      have hp (k : ℕ) (hkn : k ≤ n) :
          Interior J (actualWall a x) (Shao.prefixSum (Spitzer.reorder a pi) k) := by
        apply (hInteriorSign _ _).mpr
        have hle := (Shao.maxWithZero_le_iff (s • Spitzer.reorder a pi)
          (Shao.maxWithZero (s • Spitzer.reorder a pi))).mp le_rfl k hkn
        rw [Shao.prefixSum_smul] at hle
        exact hle.trans_lt he
      exact ⟨hq, by simpa only [hReorderTerminal] using hp n le_rfl, hp⟩
  have hHostOriginal (hxp : 0 < x) (a : Shao.Path n) :
      Shao.maxWithZero (s • a) < x * Real.sqrt (Shao.energy a) ↔
        Shao.upperMax (s • a) hn < x * Real.sqrt (Shao.energy a) := by
    rw [Shao.maxWithZero_eq _ hn, max_lt_iff]
    by_cases hq : 0 < Shao.energy a
    · exact and_iff_right (mul_pos hxp (Real.sqrt_pos.mpr hq))
    · have hq0 : Shao.energy a = 0 := le_antisymm (le_of_not_gt hq) (Shao.energy_nonneg a)
      have hqs : Shao.energy (s • a) = 0 := by rw [Shao.energy_smul, hq0, mul_zero]
      simp only [Shao.upperMax_eq_zero_of_energy_eq_zero _ hn hqs, hq0,
        Real.sqrt_zero, mul_zero, lt_self_iff_false, and_false]
  have hKernelAnalytic (hxp : 0 < x) (u : ℝ) :
      K u = if s * u < x then 1 - Real.exp (-2 * x * (x - s * u)) else 0 := by
    rcases hs with hs | hs
    · have hJu : J = .upper := by simp [J, hs]
      by_cases hu : u < x
      · have he := Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula
          B PB hB x 0 1 u (by norm_num) hxp hu
        simpa only [K, hJu, eventCompletionKernel, hs, one_mul, if_pos hu, sub_zero, div_one] using he
      · have he := hExterior x 0 1 u (by simpa only [hJu, Interior] using hu)
        simpa only [K, hs, one_mul, if_neg hu] using he
    · have hJl : J = .lower := by norm_num [J, hs]
      by_cases hu : -x < u
      · have he := Shao.C2.BridgeLowerIdentification.bridge_lower_formula
          B PB hB x 0 1 u (by norm_num) (by linarith) hu
        have hu' : s * u < x := by rw [hs]; linarith
        rw [if_pos hu']
        simpa only [K, hJl, eventCompletionKernel, hs, neg_one_mul, sub_neg_eq_add,
          add_zero, div_one] using he
      · have he := hExterior x 0 1 u (by simpa only [hJl, Interior] using hu)
        have hu' : ¬ s * u < x := by rw [hs]; linarith
        simpa only [K, if_neg hu'] using he
  let kappa : Shao.Path n → LabelPerm n → ℕ := fun a pi => energyCutoff a h pi
  let F : BridgeKernel := eventCompletionKernel J Q
  let G : BridgeKernel := halflineDerivative J
  let Af : Shao.Path n × LabelPerm n → ℝ := fun p => if sourceAlive J p.1 x n p.2 then 1 else 0
  let Vf : Shao.Path n × LabelPerm n → ℝ := fun p => sourceValue J F p.1 x (kappa p.1 p.2) p.2
  let Lf : (Shao.Path n × LabelPerm n) → ℕ → ℝ := fun p r =>
    sourceRetainedRemainder J F G p.1 x (kappa p.1) r p.2
  let Of : (Shao.Path n × LabelPerm n) → ℕ → ℝ := fun p r =>
    sourceSeparatedOvershoot J G p.1 x (kappa p.1) r p.2
  let Lsum : Shao.Path n × LabelPerm n → ℝ := fun p => ∑ r ∈ Finset.range n, Lf p r
  let Osum : Shao.Path n × LabelPerm n → ℝ := fun p => ∑ r ∈ Finset.range n, Of p r
  let Labs : Shao.Path n × LabelPerm n → ℝ := fun p => ∑ r ∈ Finset.range n, |Lf p r|
  let reveal : Measure (Shao.Path n × LabelPerm n) := revealLaw P
  letI : IsProbabilityMeasure reveal := by dsimp [reveal, revealLaw]; infer_instance
  have hKap (pi : LabelPerm n) : Measurable (fun a => kappa a pi) :=
    actual_energy_cutoff_measurable h hh pi
  have hKapBound (a : Shao.Path n) (pi : LabelPerm n) : kappa a pi ≤ n :=
    (energy_cutoff_data a h hh).1.1 pi
  have hRemainingReorder (a : Shao.Path n) (pi : LabelPerm n) (r : ℕ) :
      remainingEnergy (Spitzer.reorder a pi) r (Equiv.refl (Fin n)) = remainingEnergy a r pi := by
    simp only [remainingEnergy, hReorderEnergy]
    rfl
  have hKapReorder (a : Shao.Path n) (pi : LabelPerm n) :
      kappa (Spitzer.reorder a pi) (Equiv.refl (Fin n)) = kappa a pi := by
    simp only [kappa, energyCutoff, hRemainingReorder]
  have hAliveReorder (a : Shao.Path n) (pi : LabelPerm n) (r : ℕ) :
      sourceAlive J (Spitzer.reorder a pi) x r (Equiv.refl (Fin n)) ↔ sourceAlive J a x r pi := by
    simp only [sourceAlive, actualWall, hReorderEnergy, hReorderTerminal, Spitzer.reorder, Equiv.refl_apply]
    rfl
  have hValueReorder (a : Shao.Path n) (pi : LabelPerm n) (r : ℕ) :
      sourceValue J F (Spitzer.reorder a pi) x r (Equiv.refl (Fin n)) = sourceValue J F a x r pi := by
    simp only [sourceValue, hAliveReorder, actualWall, hReorderEnergy,
      hReorderTerminal, hRemainingReorder, Spitzer.reorder, Equiv.refl_apply]
    rfl
  have hRandomLaw : HasLaw randomReorder P reveal := ⟨hRandomMeas.aemeasurable, hRandomMap⟩
  have hEint : Integrable (fun p => |Vf p - Af p|) reveal ∧
      (∫ p, |Vf p - Af p| ∂reveal) ≤ CE * R ^ 2 := by
    have he := hTerminalE PB B hB rho n hn h2 hmean hsecond x hx hx1 J
    let d : Shao.Path n → ℝ := fun a =>
      |sourceValue J F a x (kappa a (Equiv.refl (Fin n))) (Equiv.refl (Fin n)) -
        (if sourceAlive J a x n (Equiv.refl (Fin n)) then 1 else 0)|
    change Integrable d P ∧ (∫ a, d a ∂P) ≤ CE * R ^ 2 at he
    have hd : (d ∘ randomReorder) = fun p => |Vf p - Af p| := by
      funext p
      dsimp only [d, Function.comp_def, randomReorder, Vf, Af]
      rw [hKapReorder, hValueReorder, hAliveReorder]
    have hi := hRandomLaw.integrable_comp he.1
    have hint := hRandomLaw.integral_comp he.1.aestronglyMeasurable
    rw [hd] at hi hint
    exact ⟨hi, hint.trans_le he.2⟩
  have hOvershootNonneg (hxp : 0 < x) (p : Shao.Path n × LabelPerm n) (r : ℕ) : 0 ≤ Of p r := by
    dsimp only [Of, sourceSeparatedOvershoot]
    split_ifs with hr hsel
    · dsimp only [localSeparatedOvershoot]
      split_ifs with hb
      · let w := actualWall p.1 x
        let y := Shao.prefixSum (Spitzer.reorder p.1 p.2) r
        let T := remainingEnergy p.1 r p.2
        let z := Shao.prefixSum p.1 n
        let b := p.1 (p.2 ⟨r, hr⟩)
        have hT : 0 < T := hb.1
        have hb2 : b ^ 2 ≤ T / 2 := hb.2
        have hy : Interior J w y := hsel.2.1.2.2 r le_rfl
        have hz : Interior J w z := hsel.2.1.2.1
        change 0 ≤ -(b - projectionIncrement J w y b) *
          (1 - (b + projectionIncrement J w y b) * (z - y) / T) * G (w, y, T, z)
        rcases hJ with hJu | hJl
        · rw [hJu] at hy hz
          change y < w at hy
          change z < w at hz
          by_cases hc : w ≤ y + b
          · have hproj : projectionIncrement J w y b = w - y := by
              simp only [hJu, projectionIncrement, if_pos hc]
            have hu : 0 < w - y := sub_pos.mpr hy
            have hbu : w - y ≤ b := by linarith
            have hb0 : 0 ≤ b := hu.le.trans hbu
            have hsum : 0 ≤ b + (w - y) := by linarith
            have hdz : z - y ≤ w - y := by change z < w at hz; linarith
            have hprod := mul_le_mul_of_nonneg_left hdz hsum
            have hbu2 := mul_le_mul_of_nonneg_left hbu hb0
            have hu2 := mul_nonneg (sub_nonneg.mpr hbu) hsum
            have hc0 : 0 ≤ 1 - (b + (w - y)) * (z - y) / T := by
              apply sub_nonneg.mpr
              apply (div_le_one hT).mpr
              nlinarith only [hprod, hbu2, hu2, hb2]
            have hG : G (w, y, T, z) ≤ 0 := by
              dsimp only [G]
              rw [hJu]
              change -Shao.C2.HalfLineMixedProfiles.slopeTime (w-y) (w-z) T ≤ 0
              unfold Shao.C2.HalfLineMixedProfiles.slopeTime
              have hv : 0 < w - z := sub_pos.mpr hz
              apply neg_nonpos.mpr
              positivity
            rw [hproj]
            exact mul_nonneg_of_nonpos_of_nonpos
              (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr hbu)) hc0) hG
          · have hproj : projectionIncrement J w y b = b := by
              simp only [hJu, projectionIncrement, if_neg hc]
            rw [hproj, sub_self, neg_zero, zero_mul, zero_mul]
        · rw [hJl] at hy hz
          change -w < y at hy
          change -w < z at hz
          by_cases hc : y + b ≤ -w
          · have hproj : projectionIncrement J w y b = -w - y := by
              simp only [hJl, projectionIncrement, if_pos hc]
            have hu : -w - y < 0 := by change -w < y at hy; linarith
            have hbu : b ≤ -w - y := by linarith
            have hb0 : b ≤ 0 := hbu.trans hu.le
            have hsum : b + (-w - y) ≤ 0 := by linarith
            have hdz : -w - y ≤ z - y := by change -w < z at hz; linarith
            have hprod := mul_le_mul_of_nonpos_left hdz hsum
            have hbu2 := mul_le_mul_of_nonpos_left hbu hb0
            have hu2 := mul_nonneg (sub_nonneg.mpr hbu) (by linarith : 0 ≤ -(-w-y)-b)
            have hc0 : 0 ≤ 1 - (b + (-w - y)) * (z - y) / T := by
              apply sub_nonneg.mpr
              apply (div_le_one hT).mpr
              nlinarith only [hprod, hbu2, hu2, hb2]
            have hG : 0 ≤ G (w, y, T, z) := by
              dsimp only [G]
              rw [hJl]
              change 0 ≤ Shao.C2.HalfLineMixedProfiles.slopeTime (w+y) (w+z) T
              unfold Shao.C2.HalfLineMixedProfiles.slopeTime
              have hv : 0 < w + z := by change -w < z at hz; linarith
              positivity
            rw [hproj]
            exact mul_nonneg (mul_nonneg (neg_nonneg.mpr (sub_nonpos.mpr hbu)) hc0) hG
          · have hproj : projectionIncrement J w y b = b := by
              simp only [hJl, projectionIncrement, if_neg hc]
            rw [hproj, sub_self, neg_zero, zero_mul, zero_mul]
      · exact le_refl 0
    · exact le_refl 0
    · exact le_refl 0
  let AH : Set (Shao.Path n) := {a | Shao.maxWithZero (s • a) < x * Real.sqrt (Shao.energy a)}
  have hAHm : MeasurableSet AH := measurableSet_lt
    (Shao.measurable_maxWithZero.comp (by fun_prop)) (measurable_const.mul Shao.measurable_energy.sqrt)
  have hAfEq (hxp : 0 < x) : Af = AH.indicator (fun _ : Shao.Path n => (1 : ℝ)) ∘ randomReorder := by
    funext p
    change (if sourceAlive J p.1 x n p.2 then (1 : ℝ) else 0) =
      (if Shao.maxWithZero (s • Spitzer.reorder p.1 p.2) <
        x * Real.sqrt (Shao.energy (Spitzer.reorder p.1 p.2)) then 1 else 0)
    rw [hReorderEnergy, hAliveHost hxp]
  have hAfi (hxp : 0 < x) : Integrable Af reveal := by
    rw [hAfEq hxp]
    exact hRandomLaw.integrable_comp ((integrable_const 1).indicator hAHm)
  have hAfIntegral (hxp : 0 < x) : (∫ p, Af p ∂reveal) = P.real AH := by
    rw [hAfEq hxp, hRandomLaw.integral_comp (measurable_const.indicator hAHm).aestronglyMeasurable]
    exact integral_indicator_one hAHm
  have hHostError (hxp : 0 < x) : |P.real AH - ∫ a, V a ∂P| ≤ CG * R := by
    have he := (hHostG rho n hn h2 hmean hsecond x hxp hx1 s hs).2.2
    have hfun : (fun a : Shao.Path n => if 0 < Shao.energy a then
        (if s * Shao.C1.normalizedEndpoint a < x then
          1 - Real.exp (-2 * x * (x - s * Shao.C1.normalizedEndpoint a)) else 0) else 0) = V := by
      funext a
      dsimp only [V]
      rw [hKernelAnalytic hxp]
    change |P.real AH - ∫ a : Shao.Path n, (if 0 < Shao.energy a then
        (if s * Shao.C1.normalizedEndpoint a < x then
          1 - Real.exp (-2 * x * (x - s * Shao.C1.normalizedEndpoint a)) else 0) else 0) ∂P| ≤
      CG * Shao.truncationBudget
        (Measure.map (fun z : ℝ => z / (Real.sqrt sigmaSq * Real.sqrt (n : ℝ))) rho) n 0 at he
    rw [hfun, ← hscale] at he
    exact he
  have hParts (hxp : 0 < x) := source_parts_measurable_integrable J F G hF.1 hK.1
    4 hK.2.1 P x hxp kappa hKap
  have hBdata (hxp : 0 < x) := hLocalB P rho Q hReflection n hn
    (fun i : Fin n => Function.eval i) (fun i => (measurable_pi_apply i).aemeasurable)
    hCanonicalIndep hCanonicalLaw h2 hmean hsecond x hx hx1
  have hLabsi (hxp : 0 < x) : Integrable Labs reveal := ((hBdata hxp).2.2.1 J hJ).2
  have hLBudget (hxp : 0 < x) : (∫ p, Labs p ∂reveal) ≤ CB * R := by
    have he := (hBdata hxp).2.2.2
    let S : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ := fun I p =>
      ∑ r ∈ Finset.range n, |sourceRetainedRemainder I (eventCompletionKernel I Q)
        (halflineDerivative I) p.1 x (kappa p.1) r p.2|
    change (∫ p, S .upper p ∂reveal) + (∫ p, S .lower p ∂reveal) ≤ CB * R at he
    have hu : 0 ≤ ∫ p, S .upper p ∂reveal :=
      integral_nonneg fun p => Finset.sum_nonneg fun r hr => abs_nonneg _
    have hl : 0 ≤ ∫ p, S .lower p ∂reveal :=
      integral_nonneg fun p => Finset.sum_nonneg fun r hr => abs_nonneg _
    change (∫ p, S J p ∂reveal) ≤ CB * R
    rcases hJ with hJu | hJl
    · rw [hJu]
      linarith
    · rw [hJl]
      linarith
  have hLsumI (hxp : 0 < x) : Integrable Lsum reveal := (hParts hxp).2.2.1
  have hOsumI (hxp : 0 < x) : Integrable Osum reveal := (hParts hxp).2.2.2
  have hOsumNonneg (hxp : 0 < x) (p : Shao.Path n × LabelPerm n) : 0 ≤ Osum p :=
    Finset.sum_nonneg fun r hr => hOvershootNonneg hxp p r
  have hLsumAbs (p : Shao.Path n × LabelPerm n) : |Lsum p| ≤ Labs p :=
    Finset.abs_sum_le_sum_abs _ _
  have hDecomposition (hxp : 0 < x) (p : Shao.Path n × LabelPerm n) :
      stoppedRemainderSum J F G p.1 x (kappa p.1) p.2 = Lsum p + Osum p := by
    dsimp only [stoppedRemainderSum, Lsum, Osum, Lf, Of]
    simp_rw [source_selected_remainder_decomposition J F G p.1 x hxp (kappa p.1)]
    exact Finset.sum_add_distrib
  have hMaskedTransfer (hxp : 0 < x) (m : Shao.Path n → ℝ)
      (hmm : Measurable m) (hmb : ∀ a, |m a| ≤ 1) :
      |(∫ p, m p.1 * Af p ∂reveal) - ∫ a, m a * V a ∂P| ≤ (2 * CB + 2 * CE + CG) * R := by
    have hStop (m : Shao.Path n → ℝ) (hmm : Measurable m) (hmb : ∀ a, |m a| ≤ 1) :=
      source_stopped_integrability J F G hF.1 hK.1 4 hK.2.1 P x hxp kappa hKap hKapBound m hmm hmb
    have hTel (m : Shao.Path n → ℝ) (hmm : Measurable m) (hmb : ∀ a, |m a| ≤ 1) :=
      source_masked_stopped_telescope_integral J F G hF.1 hK.1 4 hK.2.1 P x hxp h hh kappa hKap
        (fun a => (energy_cutoff_data a h hh).1) (fun a pi => le_refl _) m hmm hmb
    have hInitialIntegral (m : Shao.Path n → ℝ) (hmm : Measurable m) (hmb : ∀ a, |m a| ≤ 1) :
        (∫ p : Shao.Path n × LabelPerm n, m p.1 * sourceValue J F p.1 x 0 p.2 ∂reveal) =
          ∫ a, m a * V a ∂P := by
      calc
        _ = ∫ a : Shao.Path n, ∫ pi : LabelPerm n, m a * sourceValue J F a x 0 pi ∂labelLaw ∂P :=
          integral_prod _ (hStop m hmm hmb).2.1
        _ = _ := by
          apply integral_congr_ae
          exact ae_of_all _ fun a => by
            change (∫ pi : LabelPerm n,
              m a * sourceValue J (eventCompletionKernel J Q) a x 0 pi ∂labelLaw) = m a * V a
            have he : (fun pi : LabelPerm n =>
                m a * sourceValue J (eventCompletionKernel J Q) a x 0 pi) = fun _ => m a * V a := by
              funext pi
              rw [hInitial]
            rw [he]
            simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have hVfi : Integrable Vf reveal := by
      simpa only [one_mul] using (hStop (fun _ => 1) measurable_const (fun _ => by norm_num)).1
    have hAi := hAfi hxp
    have hOneTel := hTel (fun _ => 1) measurable_const (fun _ => by norm_num)
    rw [hInitialIntegral _ measurable_const (fun _ => by norm_num)] at hOneTel
    simp only [one_mul] at hOneTel
    have hRIntegral : (∫ p, stoppedRemainderSum J F G p.1 x (kappa p.1) p.2 ∂reveal) =
        (∫ p, Lsum p ∂reveal) + ∫ p, Osum p ∂reveal := by
      simp_rw [hDecomposition hxp]
      exact integral_add (hLsumI hxp) (hOsumI hxp)
    rw [hRIntegral] at hOneTel
    have hEV : |(∫ p, Vf p ∂reveal) - ∫ p, Af p ∂reveal| ≤ CE * R ^ 2 := by
      rw [← integral_sub hVfi hAi]
      exact abs_integral_le_integral_abs.trans hEint.2
    have hGerror : |(∫ p, Af p ∂reveal) - ∫ a, V a ∂P| ≤ CG * R := by
      rw [hAfIntegral hxp]
      exact hHostError hxp
    have hEL : |∫ p, Lsum p ∂reveal| ≤ CB * R := by
      calc
        _ ≤ ∫ p, |Lsum p| ∂reveal := abs_integral_le_integral_abs
        _ ≤ ∫ p, Labs p ∂reveal := integral_mono (hLsumI hxp).abs (hLabsi hxp) hLsumAbs
        _ ≤ _ := hLBudget hxp
    have hEO : (∫ p, Osum p ∂reveal) ≤ CB * R + CE * R ^ 2 + CG * R := by
      have heV := (abs_le.mp hEV).2
      have heG := (abs_le.mp hGerror).2
      have heL := (abs_le.mp hEL).1
      change (∫ p, Vf p ∂reveal) - (∫ a, V a ∂P) =
        (∫ p, Lsum p ∂reveal) + ∫ p, Osum p ∂reveal at hOneTel
      linarith only [hOneTel, heV, heG, heL]
    have hMVfi : Integrable (fun p => m p.1 * Vf p) reveal := (hStop m hmm hmb).1
    have hMAfi : Integrable (fun p => m p.1 * Af p) reveal := by
      refine (hAfi hxp).bdd_mul (c := 1) (hmm.comp measurable_fst).aestronglyMeasurable
        (ae_of_all _ fun p => ?_)
      simpa only [Real.norm_eq_abs] using hmb p.1
    have hMLi : Integrable (fun p => m p.1 * Lsum p) reveal := by
      refine (hLsumI hxp).bdd_mul (c := 1) (hmm.comp measurable_fst).aestronglyMeasurable
        (ae_of_all _ fun p => ?_)
      simpa only [Real.norm_eq_abs] using hmb p.1
    have hMOi : Integrable (fun p => m p.1 * Osum p) reveal := by
      refine (hOsumI hxp).bdd_mul (c := 1) (hmm.comp measurable_fst).aestronglyMeasurable
        (ae_of_all _ fun p => ?_)
      simpa only [Real.norm_eq_abs] using hmb p.1
    have hTerminalMask : |(∫ p, m p.1 * Af p ∂reveal) - ∫ p, m p.1 * Vf p ∂reveal| ≤ CE * R ^ 2 := by
      rw [← integral_sub hMAfi hMVfi]
      calc
        _ ≤ ∫ p, |m p.1 * Af p - m p.1 * Vf p| ∂reveal := abs_integral_le_integral_abs
        _ ≤ ∫ p, |Vf p - Af p| ∂reveal := by
          apply integral_mono (hMAfi.sub hMVfi).abs hEint.1
          intro p
          change |m p.1 * Af p - m p.1 * Vf p| ≤ |Vf p - Af p|
          rw [← mul_sub, abs_mul, abs_sub_comm (Af p) (Vf p)]
          exact mul_le_of_le_one_left (abs_nonneg _) (hmb p.1)
        _ ≤ _ := hEint.2
    have hMLbound : |∫ p, m p.1 * Lsum p ∂reveal| ≤ CB * R := by
      calc
        _ ≤ ∫ p, |m p.1 * Lsum p| ∂reveal := abs_integral_le_integral_abs
        _ ≤ ∫ p, Labs p ∂reveal := by
          apply integral_mono hMLi.abs (hLabsi hxp)
          intro p
          change |m p.1 * Lsum p| ≤ Labs p
          rw [abs_mul]
          exact (mul_le_of_le_one_left (abs_nonneg _) (hmb p.1)).trans (hLsumAbs p)
        _ ≤ _ := hLBudget hxp
    have hMObound : |∫ p, m p.1 * Osum p ∂reveal| ≤ ∫ p, Osum p ∂reveal := by
      calc
        _ ≤ ∫ p, |m p.1 * Osum p| ∂reveal := abs_integral_le_integral_abs
        _ ≤ _ := by
          apply integral_mono hMOi.abs (hOsumI hxp)
          intro p
          change |m p.1 * Osum p| ≤ Osum p
          rw [abs_mul, abs_of_nonneg (hOsumNonneg hxp p)]
          exact mul_le_of_le_one_left (hOsumNonneg hxp p) (hmb p.1)
    have hMTel := hTel m hmm hmb
    rw [hInitialIntegral m hmm hmb] at hMTel
    have hMRIntegral : (∫ p, m p.1 * stoppedRemainderSum J F G p.1 x (kappa p.1) p.2 ∂reveal) =
        (∫ p, m p.1 * Lsum p ∂reveal) + ∫ p, m p.1 * Osum p ∂reveal := by
      simp_rw [hDecomposition hxp, mul_add]
      exact integral_add hMLi hMOi
    rw [hMRIntegral] at hMTel
    have hid : (∫ p, m p.1 * Af p ∂reveal) - (∫ a, m a * V a ∂P) =
        ((∫ p, m p.1 * Af p ∂reveal) - ∫ p, m p.1 * Vf p ∂reveal) +
        (∫ p, m p.1 * Lsum p ∂reveal) + ∫ p, m p.1 * Osum p ∂reveal := by
      change (∫ p, m p.1 * Vf p ∂reveal) - (∫ a, m a * V a ∂P) = _ at hMTel
      linarith only [hMTel]
    rw [hid]
    calc
      _ ≤ |(∫ p, m p.1 * Af p ∂reveal) - ∫ p, m p.1 * Vf p ∂reveal| +
          |∫ p, m p.1 * Lsum p ∂reveal| + |∫ p, m p.1 * Osum p ∂reveal| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
      _ ≤ CE * R ^ 2 + CB * R + ∫ p, Osum p ∂reveal :=
        add_le_add (add_le_add hTerminalMask hMLbound) hMObound
      _ ≤ 2 * CB * R + 2 * CE * R ^ 2 + CG * R := by linarith only [hEO]
      _ ≤ _ := by
        have hr2 : R ^ 2 ≤ R := by
          have hp := mul_le_mul_of_nonneg_left hRone hR
          nlinarith only [hp]
        nlinarith only [mul_le_mul_of_nonneg_left hr2 hCE.le]
  let AC : Set (Shao.Path n) := {a | Shao.upperMax (s • a) hn < x * Real.sqrt (Shao.energy a)}
  have hACm : MeasurableSet AC := measurableSet_lt
    ((Shao.measurable_upperMax hn).comp (by fun_prop)) (measurable_const.mul Shao.measurable_energy.sqrt)
  have hAnull : NullMeasurableSet A mu := hPopulation.nullMeasurable hACm
  have hABnull : NullMeasurableSet AB PB := (hTuple.aemeasurable.nullMeasurable hEm).congr hEvent.symm
  have hOriginalA : mu.real A = P.real AC := hPopulationLaw.measureReal_eq hACm
  have hOriginalJoint (v : ℝ) :
      mu.real {omega : Ω | omega ∈ A ∧ W omega ≤ v} =
        P.real {a : Shao.Path n | a ∈ AC ∧ Shao.C1.normalizedEndpoint a ≤ v} :=
    hPopulationLaw.measureReal_eq (hACm.inter
      (measurableSet_le Shao.C1.measurable_normalizedEndpoint measurable_const))
  have hBrownianEndpoint (v : ℝ) : PB.real {omegaB : ΩB | B 1 omegaB ≤ v} = gamma.real (Set.Iic v) := by
    let S : Set (BridgeNoise × ℝ) := {p | p.2 ≤ v}
    have hS : MeasurableSet S := measurableSet_le measurable_snd measurable_const
    have he := hTuple.measureReal_eq hS
    change PB.real {omegaB : ΩB | B 1 omegaB ≤ v} = (Q.prod gamma).real S at he
    rw [he]
    have hset : S = Set.univ ×ˢ Set.Iic v := by ext p; simp only [S, Set.mem_setOf_eq,
      Set.mem_prod, Set.mem_univ, Set.mem_Iic, true_and]
    rw [hset]
    change ((Q.prod gamma) (Set.univ ×ˢ Set.Iic v)).toReal = (gamma (Set.Iic v)).toReal
    rw [Measure.prod_prod, measure_univ, one_mul]
  have hEndpointBudget (v : ℝ) :
      |mu.real {omega : Ω | W omega ≤ v} - PB.real {omegaB : ΩB | B 1 omegaB ≤ v}| ≤ Cs * R := by
    rw [hBrownianEndpoint v]
    have hS : MeasurableSet {a : Shao.Path n | Shao.C1.normalizedEndpoint a ≤ v} :=
      measurableSet_le Shao.C1.measurable_normalizedEndpoint measurable_const
    have he := hPopulationLaw.measureReal_eq hS
    change mu.real {omega : Ω | W omega ≤ v} =
      P.real {a : Shao.Path n | Shao.C1.normalizedEndpoint a ≤ v} at he
    rw [he]
    exact hCDF v
  have hFinalIntegral (hxp : 0 < x) (m : Shao.Path n → ℝ)
      (hmm : Measurable m) (hinv : PermutationInvariant m) :
      (∫ p, m p.1 * Af p ∂reveal) = ∫ a, m a * AC.indicator (fun _ : Shao.Path n => (1 : ℝ)) a ∂P := by
    have hACAH : AC = AH := by
      ext a
      exact (hHostOriginal hxp a).symm
    have hfun : (fun p : Shao.Path n × LabelPerm n => m p.1 * Af p) =
        (fun a : Shao.Path n => m a * AC.indicator (fun _ : Shao.Path n => (1 : ℝ)) a) ∘ randomReorder := by
      funext p
      rw [congrFun (hAfEq hxp) p]
      change m p.1 * AH.indicator (fun _ => (1 : ℝ)) (randomReorder p) =
        m (randomReorder p) * AC.indicator (fun _ => (1 : ℝ)) (randomReorder p)
      rw [show m (randomReorder p) = m p.1 from hinv p.1 p.2, hACAH]
    rw [hfun]
    exact hRandomLaw.integral_comp (hmm.mul (measurable_const.indicator hACm)).aestronglyMeasurable
  let D : ℝ := 1 + 2 * CB + 2 * CE + CG + 2 * Cs + 16 + C0
  have hStrictBounds : |mu.real A - PB.real AB| ≤ D * R ∧
      ∀ v : ℝ,
        |mu.real {omega : Ω | omega ∈ A ∧ W omega ≤ v} -
          PB.real {omegaB : ΩB | omegaB ∈ AB ∧ B 1 omegaB ≤ v}| ≤ D * R := by
    by_cases hx0 : x = 0
    · have hz := (hZeroWall mu rho n hn X hX hIndep hLaw h2 hmean hsecond s hs).2.1
      have hAZ : mu.real A ≤ C0 * R := by
        simpa only [A, hx0, zero_mul] using hz
      have hAE : AB =ᵐ[PB] (∅ : Set ΩB) := by
        filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with omega homega
        apply propext
        constructor
        · intro ha
          have ht := ha (0 : BridgeTime)
          change s * B 0 omega < x at ht
          rw [homega, hx0, mul_zero] at ht
          exact (lt_irrefl 0 ht).elim
        · intro he
          exact he.elim
      have hBZ : PB.real AB = 0 := (measureReal_congr hAE).trans measureReal_empty
      have hinc : C0 ≤ D := by dsimp only [D]; linarith
      have hAZD : mu.real A ≤ D * R := hAZ.trans (mul_le_mul_of_nonneg_right hinc hR)
      refine ⟨?_, ?_⟩
      · simpa only [hBZ, sub_zero, abs_of_nonneg measureReal_nonneg] using hAZD
      · intro v
        have hBj : PB.real {omegaB : ΩB | omegaB ∈ AB ∧ B 1 omegaB ≤ v} = 0 :=
          measureReal_mono_null (fun omega homega => homega.1) hBZ
        rw [hBj, sub_zero, abs_of_nonneg measureReal_nonneg]
        have hm : mu.real {omega : Ω | omega ∈ A ∧ W omega ≤ v} ≤ mu.real A :=
          measureReal_mono (fun omega homega => homega.1) (by finiteness)
        exact hm.trans hAZD
    · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      have hinc : (2 * CB + 2 * CE + CG) + (2 * Cs + 16) ≤ D := by
        dsimp only [D]
        linarith
      have hmarg : |mu.real A - ∫ a, V a ∂P| ≤ (2 * CB + 2 * CE + CG) * R := by
        have he := hFinalIntegral hxp (fun _ => 1) measurable_const (fun _ _ => rfl)
        have hd := hMaskedTransfer hxp (fun _ => 1) measurable_const (fun _ => by norm_num)
        simp only [one_mul] at he hd
        have hi : (∫ a : Shao.Path n, AC.indicator (fun _ : Shao.Path n => (1 : ℝ)) a ∂P) = P.real AC :=
          integral_indicator_one hACm
        rw [hi, ← hOriginalA] at he
        rwa [he] at hd
      refine ⟨?_, ?_⟩
      · calc
          _ ≤ |mu.real A - ∫ a, V a ∂P| + |(∫ a, V a ∂P) - PB.real AB| := abs_sub_le _ _ _
          _ ≤ (2 * CB + 2 * CE + CG) * R + (2 * Cs + 16) * R := add_le_add hmarg hInitialGap
          _ ≤ D * R := by nlinarith only [mul_le_mul_of_nonneg_right hinc hR]
      · intro v
        let m : Shao.Path n → ℝ := fun a => if Shao.C1.normalizedEndpoint a ≤ v then 1 else 0
        have hmm : Measurable m := Measurable.ite
          (measurableSet_le Shao.C1.measurable_normalizedEndpoint measurable_const) measurable_const measurable_const
        have hmb (a : Shao.Path n) : |m a| ≤ 1 := by dsimp only [m]; split_ifs <;> norm_num
        have hinv : PermutationInvariant m := by intro a pi; simp only [m, hReorderW]
        have he := hFinalIntegral hxp m hmm hinv
        have hd := hMaskedTransfer hxp m hmm hmb
        have hfun : (fun a : Shao.Path n => m a * AC.indicator (fun _ : Shao.Path n => (1 : ℝ)) a) =
            ({a : Shao.Path n | a ∈ AC ∧ Shao.C1.normalizedEndpoint a ≤ v}).indicator (fun _ => (1 : ℝ)) := by
          funext a
          by_cases ha : a ∈ AC <;> by_cases hv : Shao.C1.normalizedEndpoint a ≤ v <;>
            simp only [m, Set.indicator, Set.mem_setOf_eq, ha, hv, and_true, and_false,
              true_and, false_and, ite_true, ite_false, mul_one, mul_zero, one_mul, zero_mul]
        rw [hfun] at he
        have hi : (∫ a : Shao.Path n,
            ({a : Shao.Path n | a ∈ AC ∧ Shao.C1.normalizedEndpoint a ≤ v}).indicator (fun _ => (1 : ℝ)) a ∂P) =
            P.real {a : Shao.Path n | a ∈ AC ∧ Shao.C1.normalizedEndpoint a ≤ v} :=
          integral_indicator_one (hACm.inter (measurableSet_le Shao.C1.measurable_normalizedEndpoint measurable_const))
        rw [hi, ← hOriginalJoint v] at he
        rw [he] at hd
        have hinit : (fun a : Shao.Path n => m a * V a) =
            fun a : Shao.Path n => if Shao.C1.normalizedEndpoint a ≤ v then V a else 0 := by
          funext a
          dsimp only [m]
          split_ifs <;> simp only [one_mul, zero_mul]
        rw [hinit] at hd
        calc
          _ ≤ |mu.real {omega : Ω | omega ∈ A ∧ W omega ≤ v} -
              ∫ a : Shao.Path n, (if Shao.C1.normalizedEndpoint a ≤ v then V a else 0) ∂P| +
              |(∫ a : Shao.Path n, (if Shao.C1.normalizedEndpoint a ≤ v then V a else 0) ∂P) -
                PB.real {omegaB : ΩB | omegaB ∈ AB ∧ B 1 omegaB ≤ v}| := abs_sub_le _ _ _
          _ ≤ (2 * CB + 2 * CE + CG) * R + (2 * Cs + 16) * R := add_le_add hd (hMaskedInitialGap v)
          _ ≤ D * R := by nlinarith only [mul_le_mul_of_nonneg_right hinc hR]
  have hDfull : D ≤ 1 + 2 * CB + 2 * CE + CG + 3 * Cs + 16 + C0 := by dsimp only [D]; linarith
  have hCross : {omega : Ω | x * Real.sqrt (rawEnergy omega) ≤ signedMax omega} = Aᶜ := by
    ext omega
    simp only [A, Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
  have hBCross : {omegaB : ΩB | ∃ t : BridgeTime, x ≤ s * B ⟨(t : ℝ), t.property.1⟩ omegaB} = ABᶜ := by
    ext omega
    simp only [AB, Set.mem_setOf_eq, Set.mem_compl_iff, not_forall, not_lt]
  refine ⟨hInitOutput, hAi, hBi, hStrictBounds.1.trans (mul_le_mul_of_nonneg_right hDfull hR), ?_, ?_⟩
  · rw [hCross, hBCross, measureReal_compl₀ hAnull, measureReal_compl₀ hABnull]
    simp only [probReal_univ]
    have he : (1 - mu.real A) - (1 - PB.real AB) = -(mu.real A - PB.real AB) := by ring
    rw [he, abs_neg]
    exact hStrictBounds.1.trans (mul_le_mul_of_nonneg_right hDfull hR)
  · intro v
    refine ⟨hMaskedAi v, hMaskedBi v,
      (hStrictBounds.2 v).trans (mul_le_mul_of_nonneg_right hDfull hR), ?_⟩
    have hsa := measureReal_inter_add_sdiff₀ (μ := mu) (s := {omega : Ω | W omega ≤ v}) hAnull
    have hsb := measureReal_inter_add_sdiff₀ (μ := PB) (s := {omega : ΩB | B 1 omega ≤ v}) hABnull
    have hia : {omega : Ω | W omega ≤ v} ∩ A = {omega : Ω | omega ∈ A ∧ W omega ≤ v} := by
      ext omega
      exact and_comm
    have hda : {omega : Ω | W omega ≤ v} \ A =
        {omega : Ω | x * Real.sqrt (rawEnergy omega) ≤ signedMax omega ∧ W omega ≤ v} := by
      ext omega
      simp only [A, Set.mem_sdiff, Set.mem_setOf_eq, not_lt]
      exact and_comm
    have hib : {omegaB : ΩB | B 1 omegaB ≤ v} ∩ AB =
        {omegaB : ΩB | omegaB ∈ AB ∧ B 1 omegaB ≤ v} := by ext omega; exact and_comm
    have hdb : {omegaB : ΩB | B 1 omegaB ≤ v} \ AB =
        {omegaB : ΩB | (∃ t : BridgeTime, x ≤ s * B ⟨(t : ℝ), t.property.1⟩ omegaB) ∧ B 1 omegaB ≤ v} := by
      ext omega
      simp only [AB, Set.mem_sdiff, Set.mem_setOf_eq, not_forall, not_lt]
      exact and_comm
    rw [hia, hda] at hsa
    rw [hib, hdb] at hsb
    have he :
        (mu.real {omega : Ω | x * Real.sqrt (rawEnergy omega) ≤ signedMax omega ∧ W omega ≤ v} -
          PB.real {omegaB : ΩB | (∃ t : BridgeTime, x ≤ s * B ⟨(t : ℝ), t.property.1⟩ omegaB) ∧ B 1 omegaB ≤ v}) =
        (mu.real {omega : Ω | W omega ≤ v} - PB.real {omegaB : ΩB | B 1 omegaB ≤ v}) -
          (mu.real {omega : Ω | omega ∈ A ∧ W omega ≤ v} - PB.real {omegaB : ΩB | omegaB ∈ AB ∧ B 1 omegaB ≤ v}) := by
      linarith only [hsa, hsb]
    rw [he]
    calc
      _ ≤ |mu.real {omega : Ω | W omega ≤ v} - PB.real {omegaB : ΩB | B 1 omegaB ≤ v}| +
          |mu.real {omega : Ω | omega ∈ A ∧ W omega ≤ v} - PB.real {omegaB : ΩB | omegaB ∈ AB ∧ B 1 omegaB ≤ v}| := abs_sub _ _
      _ ≤ Cs * R + D * R := add_le_add (hEndpointBudget v) (hStrictBounds.2 v)
      _ = _ := by dsimp only [D]; ring


end Shao.Probability.SourceOriginalHalflineComparison
