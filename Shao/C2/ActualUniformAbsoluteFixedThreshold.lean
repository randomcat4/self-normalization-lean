/- Unit220 complete all-threshold absolute and fixed-M comparison source candidate; not yet kernel qualified. -/
import Shao.C2.ActualBoundedCenteredFixed
import Shao.C2.UniformGaussianTailPolynomial

set_option autoImplicit false
noncomputable section
namespace Shao.C2.ActualUniformAbsoluteFixedThreshold
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical NNReal ENNReal
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.ActualSignedDoubleTelescope
open Shao.C2.ActualRetainedResidualBudgets
open Shao.Probability.SourcePermutationReveal
open Shao.Probability.SourceSeparatedOvershoot
open Shao.Probability.SourceIIDGaussianProfileBudget
open Shao.Probability.SourceMarkedSuffixAveraging

local instance uaf_labelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

private theorem uaf_legal_c1_all_thresholds :
    ∃ rhoStar epsilonF C1 K1 : ℝ,
      0 < rhoStar ∧ rhoStar ≤ 1 / 16 ∧
      epsilonF = min (rhoStar / 27) (1 / 8) ∧ 0 < epsilonF ∧ 0 < C1 ∧ 0 < K1 ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (bound : ℝ), 0 < bound → (∀ᵐ z : ℝ ∂rho, |z| ≤ bound) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        ∀ (n : ℕ) (hn : 0 < n) (x : ℝ), (1 / 2 : ℝ) ≤ x →
          bound ≤ Real.sqrt (n : ℝ) / (100 * x) →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          let delta : ℝ := beta / Real.sqrt (n : ℝ)
          delta * x ^ 3 ≤ epsilonF →
          let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) rho
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
          Shao.truncationBudget normalizedLaw n x = delta * (1 + x) ^ 3 ∧
          Shao.truncationBudget normalizedLaw n x ≤ rhoStar ∧ delta ≤ 1 ∧
          ∀ s : ℝ, (s = 1 ∨ s = -1) →
            let U : Set (Shao.Path n) := {a | x * Real.sqrt (Shao.energy a) ≤ Shao.upperMax (s • a) hn}
            |P.real U - 2 * Shao.standardNormalTail x| ≤ C1 * delta * (1 + x) ^ 3 * Shao.standardNormalTail x ∧
            |P.real U - 2 * Shao.standardNormalTail x| ≤ K1 * delta := by
  classical
  obtain ⟨rhoStar, C1, hrho, hrho16, hC1, hOriginal⟩ :=
    Shao.Probability.original_one_sided_relative_error_iid
  let epsilonF : ℝ := min (rhoStar / 27) (1 / 8)
  let Kpsi : ℝ := 1 + (16 / 3 : ℝ) * (Real.sqrt (2 * Real.pi))⁻¹
  let K1 : ℝ := C1 * Kpsi
  have heps : 0 < epsilonF := lt_min (by positivity) (by norm_num)
  have hK1 : 0 < K1 := by dsimp [K1, Kpsi]; positivity
  refine ⟨rhoStar, epsilonF, C1, K1, hrho, hrho16, rfl, heps, hC1, hK1, ?_⟩
  intro rho hProb bound hb hsupport hmean hsecond n hn x hx hscale beta delta hsmall normalizedLaw P
  letI : IsProbabilityMeasure rho := hProb
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  rcases Shao.C2.ActualBoundedCenteredFixed.iid_actual_bounded_own_budget_identities rho bound hb hsupport hmean hsecond n hn x hx hscale with
    ⟨h1, h2, h3, hbound1, hbeta, hdelta, hH, hnlarge, hR0, hRx, hcut, hPrefixBudget⟩
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hOnePlus : 1 + x ≤ 3 * x := by linarith only [hx]
  have hRxBound : Shao.truncationBudget normalizedLaw n x ≤ rhoStar := by
    rw [hRx]
    calc
      delta * (1 + x) ^ 3 ≤ delta * (3 * x) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hOnePlus 3) hdelta.le
      _ = 27 * (delta * x ^ 3) := by ring
      _ ≤ 27 * epsilonF := mul_le_mul_of_nonneg_left hsmall (by norm_num)
      _ ≤ rhoStar := by
        have hh : epsilonF ≤ rhoStar / 27 := min_le_left _ _
        linarith only [hh]
  have hdelta1 : delta ≤ 1 := by
    have hx3 : (1 / 8 : ℝ) ≤ x ^ 3 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hx 3
      norm_num at hh
      exact hh
    have hh := mul_le_mul_of_nonneg_left hx3 hdelta.le
    have heps8 : epsilonF ≤ 1 / 8 := min_le_right _ _
    nlinarith only [hh, hsmall, heps8]
  refine ⟨hRx, hRxBound, hdelta1, ?_⟩
  intro s hs U
  let X : Fin n → Shao.Path n → ℝ := fun i a => a i
  have hX (i : Fin n) : Measurable (X i) := measurable_pi_apply i
  have hLaw (i : Fin n) : IdentDistrib (X i) (id : ℝ → ℝ) P rho :=
    ⟨(hX i).aemeasurable, measurable_id.aemeasurable, by
      simpa only [Measure.map_id] using (measurePreserving_eval (μ := fun _ : Fin n => rho) i).map_eq⟩
  have hInd : iIndepFun X P := iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hIdent (i : Fin n) : IdentDistrib (X i) (X ⟨0, hn⟩) P P :=
    (hLaw i).trans (hLaw ⟨0, hn⟩).symm
  have hY2 : Integrable (fun a : Shao.Path n => X ⟨0, hn⟩ a ^ 2) P :=
    ((hLaw ⟨0, hn⟩).comp (by fun_prop : Measurable (fun z : ℝ => z ^ 2))).integrable_iff.mpr h2
  have hYmean : (∫ a : Shao.Path n, X ⟨0, hn⟩ a ∂P) = 0 :=
    (hLaw ⟨0, hn⟩).integral_eq.trans hmean
  have hYsecond : (∫ a : Shao.Path n, X ⟨0, hn⟩ a ^ 2 ∂P) = 1 :=
    ((hLaw ⟨0, hn⟩).comp (by fun_prop : Measurable (fun z : ℝ => z ^ 2))).integral_eq.trans hsecond
  have hY3 : Integrable (fun a : Shao.Path n => Real.rpow |X ⟨0, hn⟩ a| (3 : ℝ)) P := by
    have hi := ((hLaw ⟨0, hn⟩).comp
      (by fun_prop : Measurable (fun z : ℝ => |z| ^ 3))).integrable_iff.mpr h3
    change Integrable (fun a : Shao.Path n => |X ⟨0, hn⟩ a| ^ (3 : ℕ)) P at hi
    have he : (fun a : Shao.Path n => Real.rpow |X ⟨0, hn⟩ a| (3 : ℝ)) =
        (fun a : Shao.Path n => |X ⟨0, hn⟩ a| ^ (3 : ℕ)) := by
      funext a
      exact Real.rpow_natCast _ 3
    rw [he]
    exact hi
  have hMapX : Measure.map (X ⟨0, hn⟩) P = rho := by
    simpa only [Measure.map_id] using (hLaw ⟨0, hn⟩).map_eq
  have hNorm : Measure.map (fun a : Shao.Path n => X ⟨0, hn⟩ a / Real.sqrt (n : ℝ)) P = normalizedLaw := by
    calc
      _ = Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) (Measure.map (X ⟨0, hn⟩) P) :=
        (Measure.map_map (by fun_prop) (hX ⟨0, hn⟩)).symm
      _ = _ := by rw [hMapX]
  have hCall := hOriginal 3 (by norm_num) (by norm_num) P n hn X hX hInd hIdent hY2 hYmean
    (by rw [hYsecond]; norm_num) hY3
  dsimp only at hCall
  rw [hYsecond] at hCall
  simp only [Real.sqrt_one, one_mul] at hCall
  rw [hNorm] at hCall
  have hRel := hCall x hx0 (Or.inr hRxBound) s hs
  change |P.real U / Shao.standardNormalTail x - 2| ≤ C1 * Shao.truncationBudget normalizedLaw n x at hRel
  have htail : 0 < Shao.standardNormalTail x := (Shao.standardNormalTail_basic.2.2.1 x).1
  have hAbs : |P.real U - 2 * Shao.standardNormalTail x| ≤
      C1 * delta * (1 + x) ^ 3 * Shao.standardNormalTail x := by
    have he : (P.real U / Shao.standardNormalTail x - 2) * Shao.standardNormalTail x =
        P.real U - 2 * Shao.standardNormalTail x := by
      field_simp [htail.ne']
    calc
      _ = |P.real U / Shao.standardNormalTail x - 2| * Shao.standardNormalTail x := by
        rw [← he, abs_mul, abs_of_pos htail]
      _ ≤ (C1 * Shao.truncationBudget normalizedLaw n x) * Shao.standardNormalTail x :=
        mul_le_mul_of_nonneg_right hRel htail.le
      _ = _ := by rw [hRx]; ring
  refine ⟨hAbs, hAbs.trans ?_⟩
  have hpoly : (1 + x) ^ 3 * Shao.standardNormalTail x ≤ Kpsi := by
    have h := Shao.C2.UniformGaussianTailPolynomial.standardNormalTail_cubic_uniform_bound x hx0
    dsimp [Kpsi]
    linarith only [h]
  calc
    C1 * delta * (1 + x) ^ 3 * Shao.standardNormalTail x =
        (C1 * delta) * ((1 + x) ^ 3 * Shao.standardNormalTail x) := by ring
    _ ≤ (C1 * delta) * Kpsi :=
      mul_le_mul_of_nonneg_left hpoly (mul_nonneg hC1.le hdelta.le)
    _ = K1 * delta := by dsimp [K1]; ring

private theorem uaf_absolute_comparison_all_thresholds :
    ∃ epsilonF CA : ℝ, 0 < epsilonF ∧ epsilonF ≤ 1 / 8 ∧ 0 < CA ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (bound : ℝ), 0 < bound → (∀ᵐ z : ℝ ∂rho, |z| ≤ bound) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        ∀ (n : ℕ) (hn : 0 < n) (x : ℝ), (1 / 2 : ℝ) ≤ x →
          bound ≤ Real.sqrt (n : ℝ) / (100 * x) →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          let delta : ℝ := beta / Real.sqrt (n : ℝ)
          delta * x ^ 3 ≤ epsilonF →
          ∀ {ΩB : Type*} [MeasurableSpace ΩB]
            (Bm : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
            IsBrownianReal Bm PB →
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
            |P.real {a | x * Real.sqrt (Shao.energy a) ≤ Shao.absMax a hn} -
              PB.real {omegaB | ∃ t : BridgeTime,
                x ≤ |Bm ⟨(t : ℝ), t.property.1⟩ omegaB|}| ≤ CA * delta := by
  classical
  obtain ⟨CB, hCB, hBill⟩ := Shao.C2.ActualBoundedCenteredFixed.iid_actual_all_level_retained_negative_budget
  obtain ⟨CE, hCE, hTerminal⟩ := Shao.C2.ActualBoundedCenteredFixed.iid_actual_all_level_h0_terminal_budget
  obtain ⟨CS, hCS, hHalfInitial⟩ := Shao.C2.ActualBoundedCenteredFixed.iid_actual_halfline_initial_all_positive
  obtain ⟨rhoStar, epsilonF, C1, K1, hrho, hrho16, hepsEq, heps, hC1, hK1, hC1Segment⟩ :=
    uaf_legal_c1_all_thresholds
  obtain ⟨CI, hCI, hIntervalInitial⟩ :=
    Shao.Probability.SourceActualIntervalInitialCDF.original_iid_actual_interval_initial_cdf_budget
  let KG : ℝ := K1 + CS
  let CA : ℝ := 3 * CB + 3 * CE + 2 * KG + CI + 1
  have hKG : 0 < KG := add_pos hK1 hCS
  refine ⟨epsilonF, CA, heps, ?_, by dsimp [CA]; positivity, ?_⟩
  · rw [hepsEq]
    exact min_le_right _ _
  intro rho hProb bound hb hsupport hmean hsecond n hn x hx hscale beta delta hsmall
    ΩB hΩB Bm PB hPB hBm P
  letI : IsProbabilityMeasure rho := hProb
  letI : IsProbabilityMeasure PB := hPB
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  let Q : Measure BridgeNoise := bridgeLaw Bm PB
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw Bm PB hBm
  letI : IsProbabilityMeasure (revealLaw P) := by unfold revealLaw; infer_instance
  rcases Shao.C2.ActualBoundedCenteredFixed.iid_actual_bounded_own_budget_identities rho bound hb hsupport hmean hsecond n hn x hx hscale with
    ⟨h1, h2, h3, hbound1, hbeta, hdelta, hH, hnlarge, hR0, hRx, hcut, hPrefixBudget⟩
  let H : ℝ := 4 * beta ^ 2
  change 0 < H at hH
  have hxpos : 0 < x := by linarith only [hx]
  have hC1Data := hC1Segment rho bound hb hsupport hmean hsecond n hn x hx hscale hsmall
  have hd1 : delta ≤ 1 := hC1Data.2.2.1
  have hd2 : delta ^ 2 ≤ delta := by nlinarith only [hdelta, hd1]
  have hBoundRoot : bound ≤ Real.sqrt (n : ℝ) := by
    have hh : (100 * x) * bound ≤ Real.sqrt (n : ℝ) := by
      simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < 100 * x)).mp hscale
    exact (le_mul_of_one_le_left hb.le (by linarith only [hx] : 1 ≤ 100 * x)).trans hh
  have hHalf := hHalfInitial rho bound hb hsupport hmean hsecond n hn hBoundRoot Bm PB hBm x hxpos
  let X : Fin n → Shao.Path n → ℝ := fun i a => a i
  have hX (i : Fin n) : Measurable (X i) := measurable_pi_apply i
  have hInd : iIndepFun X P := iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hLaw (i : Fin n) : IdentDistrib (X i) (id : ℝ → ℝ) P rho :=
    ⟨(hX i).aemeasurable, measurable_id.aemeasurable, by
      simpa only [Measure.map_id] using (measurePreserving_eval (μ := fun _ : Fin n => rho) i).map_eq⟩
  have hInit := hIntervalInitial Bm PB hBm P rho n hn X (fun i => (hX i).aemeasurable)
    hInd hLaw h2 hmean (by rw [hsecond]; norm_num) x hxpos.le
  simp only [hsecond, mul_one, hR0] at hInit
  have hq (a : Shao.Path n) (sigma : LabelPerm n) :
      Shao.energy (Shao.Probability.Spitzer.reorder a sigma) = Shao.energy a :=
    Equiv.sum_comp sigma (fun i => (a i) ^ 2)
  have hs (a : Shao.Path n) (sigma : LabelPerm n) :
      Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) n = Shao.prefixSum a n := by
    simpa only [Shao.prefixSum_length, Shao.Probability.Spitzer.reorder] using Equiv.sum_comp sigma a
  have hmReorder : Measurable (randomReorder : Shao.Path n × LabelPerm n → Shao.Path n) :=
    measurable_from_prod_countable_left (fun sigma =>
      Measurable.of_eval (fun i => measurable_pi_apply (sigma i)))
  have hReorderMap : Measure.map (randomReorder : Shao.Path n × LabelPerm n → Shao.Path n)
      (revealLaw P) = P := by
    have hh := iid_randomPermutation_map_eq_pi P rho X hX hInd hLaw
    have hfun : (fun p : Shao.Path n × LabelPerm n =>
        Shao.Probability.Spitzer.reorder (Shao.Probability.samplePath X p.1) p.2) = randomReorder := by
      funext p i
      rfl
    change Measure.map (fun p => Shao.Probability.Spitzer.reorder (Shao.Probability.samplePath X p.1) p.2) (revealLaw P) = P at hh
    rw [hfun] at hh
    exact hh
  have hReorderLaw : IdentDistrib (randomReorder : Shao.Path n × LabelPerm n → Shao.Path n)
      (id : Shao.Path n → Shao.Path n) (revealLaw P) P :=
    ⟨hmReorder.aemeasurable, measurable_id.aemeasurable, by simpa only [Measure.map_id] using hReorderMap⟩
  let S : MonitoredDomain → Set (Shao.Path n) := fun J => match J with
    | .upper => {a | Shao.upperMax a hn < actualWall a x}
    | .lower => {a | Shao.upperMax (-a) hn < actualWall a x}
    | .interval => {a | Shao.absMax a hn < actualWall a x}
  have hSm (J : MonitoredDomain) : MeasurableSet (S J) := by
    cases J with
    | upper => exact measurableSet_lt (Shao.measurable_upperMax hn) (Shao.measurable_energyWall x)
    | lower => exact measurableSet_lt ((Shao.measurable_upperMax hn).comp (by fun_prop)) (Shao.measurable_energyWall x)
    | interval => exact measurableSet_lt (Shao.measurable_absMax hn) (Shao.measurable_energyWall x)
  have hSignedAlive (J : MonitoredDomain) (s : ℝ)
      (hJs : (J = .upper ∧ s = 1) ∨ (J = .lower ∧ s = -1)) (a : Shao.Path n) (sigma : LabelPerm n) :
      sourceAlive J a x n sigma ↔
        Shao.upperMax (s • Shao.Probability.Spitzer.reorder a sigma) hn < actualWall a x := by
    have hsign : s = 1 ∨ s = -1 := hJs.imp And.right And.right
    have hEnergy : Shao.energy (s • Shao.Probability.Spitzer.reorder a sigma) = Shao.energy a := by
      rcases hsign with rfl | rfl <;> simpa using hq a sigma
    constructor
    · intro ha
      obtain ⟨k, hk, hkn, hEq⟩ := Shao.upperMax_attained (s • Shao.Probability.Spitzer.reorder a sigma) hn
      rw [hEq, Shao.prefixSum_smul]
      have hp := ha.2.2 k hkn
      rcases hJs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa only [Interior, one_mul] using hp
      · change -actualWall a x < Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) k at hp
        simp only [neg_one_mul]
        linarith only [hp]
    · intro ha
      have hE : 0 < Shao.energy a := by
        by_contra hh
        have hz : Shao.energy a = 0 := le_antisymm (le_of_not_gt hh) (Shao.energy_nonneg a)
        have hz' : Shao.energy (s • Shao.Probability.Spitzer.reorder a sigma) = 0 := hEnergy.trans hz
        rw [Shao.upperMax_eq_zero_of_energy_eq_zero _ hn hz', actualWall, hz, Real.sqrt_zero, mul_zero] at ha
        exact (lt_irrefl 0) ha
      have hw : 0 < actualWall a x := mul_pos hxpos (Real.sqrt_pos.mpr hE)
      have hp (k : ℕ) (hkn : k ≤ n) : s * Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) k < actualWall a x := by
        by_cases hk : k = 0
        · simpa only [hk, Shao.prefixSum_zero, mul_zero] using hw
        · have hh := (Shao.le_upperMax (s • Shao.Probability.Spitzer.reorder a sigma) hn k
            (Nat.one_le_iff_ne_zero.mpr hk) hkn).trans_lt ha
          simpa only [Shao.prefixSum_smul] using hh
      refine ⟨hE, ?_, ?_⟩
      · have hz := hp n le_rfl
        rw [hs a sigma] at hz
        rcases hJs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simpa only [Interior, one_mul] using hz
        · change -actualWall a x < Shao.prefixSum a n
          simp only [neg_one_mul] at hz
          linarith only [hz]
      · intro k hk
        have hz := hp k hk
        rcases hJs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simpa only [Interior, one_mul] using hz
        · change -actualWall a x < Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) k
          simp only [neg_one_mul] at hz
          linarith only [hz]
  have hAlive (J : MonitoredDomain) (a : Shao.Path n) (sigma : LabelPerm n) :
      sourceAlive J a x n sigma ↔ Shao.Probability.Spitzer.reorder a sigma ∈ S J := by
    cases J with
    | upper => simpa only [S, Set.mem_setOf_eq, one_smul, actualWall, hq] using
        hSignedAlive .upper 1 (Or.inl ⟨rfl, rfl⟩) a sigma
    | lower => simpa only [S, Set.mem_setOf_eq, neg_one_smul, actualWall, hq] using
        hSignedAlive .lower (-1) (Or.inr ⟨rfl, rfl⟩) a sigma
    | interval =>
        change sourceAlive .interval a x n sigma ↔ Shao.absMax (Shao.Probability.Spitzer.reorder a sigma) hn <
          actualWall (Shao.Probability.Spitzer.reorder a sigma) x
        rw [show actualWall (Shao.Probability.Spitzer.reorder a sigma) x = actualWall a x by simp only [actualWall, hq]]
        constructor
        · intro ha
          obtain ⟨k, hk, hkn, hEq⟩ := Shao.absMax_attained (Shao.Probability.Spitzer.reorder a sigma) hn
          rw [hEq]
          exact abs_lt.mpr (ha.2.2 k hkn)
        · intro ha
          have hw : 0 < actualWall a x := (Shao.absMax_nonneg _ hn).trans_lt ha
          have hE : 0 < Shao.energy a := by
            by_contra hh
            have hz : Shao.energy a = 0 := le_antisymm (le_of_not_gt hh) (Shao.energy_nonneg a)
            simpa only [actualWall, hz, Real.sqrt_zero, mul_zero, lt_self_iff_false] using hw
          have hp (k : ℕ) (hk : k ≤ n) : |Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) k| < actualWall a x := by
            by_cases hk0 : k = 0
            · simpa only [hk0, Shao.prefixSum_zero, abs_zero] using hw
            · exact (Shao.le_absMax _ hn k (Nat.one_le_iff_ne_zero.mpr hk0) hk).trans_lt ha
          refine ⟨hE, ?_, fun k hk => abs_lt.mp (hp k hk)⟩
          have hz := abs_lt.mp (hp n le_rfl)
          rw [hs a sigma] at hz
          exact hz
  let A : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ := fun J p =>
    if sourceAlive J p.1 x n p.2 then 1 else 0
  let V0 : MonitoredDomain → Shao.Path n → ℝ := fun J a =>
    sourceValue J (eventCompletionKernel J Q) a x 0 (Equiv.refl (Fin n))
  let Vinitial : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ := fun J p =>
    sourceValue J (eventCompletionKernel J Q) p.1 x 0 p.2
  have hInitialEq (J : MonitoredDomain) (p : Shao.Path n × LabelPerm n) : Vinitial J p = V0 J p.1 := by
    exact (source_observables_prefix J (eventCompletionKernel J Q) (actualDerivativeFamily Q J) p.1 x 0).2.2.2.1
      p.2 (Equiv.refl (Fin n)) (fun i hi => by omega)
  have hV0I (J : MonitoredDomain) : Integrable (V0 J) P := by
    cases J with
    | upper => exact (hHalf.1 .upper (Or.inl rfl)).1
    | lower => exact (hHalf.1 .lower (Or.inr rfl)).1
    | interval => exact (hInit.2 (Equiv.refl (Fin n))).2.1
  have hApoint (J : MonitoredDomain) (p : Shao.Path n × LabelPerm n) :
      A J p = (S J).indicator (fun _ => (1 : ℝ)) (randomReorder p) := by
    by_cases hp : randomReorder p ∈ S J
    · have ha : sourceAlive J p.1 x n p.2 := (hAlive J p.1 p.2).mpr hp
      simp only [A, if_pos ha, Set.indicator_of_mem hp]
    · have ha : ¬ sourceAlive J p.1 x n p.2 := fun h => hp ((hAlive J p.1 p.2).mp h)
      simp only [A, if_neg ha, Set.indicator_of_notMem hp]
  have hAI (J : MonitoredDomain) : Integrable (A J) (revealLaw P) := by
    have hi := (hReorderLaw.comp
      ((measurable_const : Measurable (fun _ : Shao.Path n => (1 : ℝ))).indicator (hSm J))).integrable_iff.mpr
      ((integrable_const (1 : ℝ)).indicator (hSm J))
    exact hi.congr (ae_of_all _ fun p => (hApoint J p).symm)
  have hAIntegral (J : MonitoredDomain) : (∫ p, A J p ∂revealLaw P) = P.real (S J) := by
    calc
      _ = ∫ p, (S J).indicator (fun _ => (1 : ℝ)) (randomReorder p) ∂revealLaw P :=
        integral_congr_ae (ae_of_all _ (hApoint J))
      _ = ∫ a, (S J).indicator (fun _ => (1 : ℝ)) a ∂P :=
        (hReorderLaw.comp (measurable_const.indicator (hSm J))).integral_eq
      _ = _ := integral_indicator_one (hSm J)
  have hFstMap : Measure.map (Prod.fst : Shao.Path n × LabelPerm n → Shao.Path n) (revealLaw P) = P :=
    (measurePreserving_fst (μ := P) (ν := uniformPermutationLaw n)).map_eq
  have hInitialIntegral (J : MonitoredDomain) : (∫ p, Vinitial J p ∂revealLaw P) = ∫ a, V0 J a ∂P := by
    have hVm : AEStronglyMeasurable (V0 J) (Measure.map Prod.fst (revealLaw P)) := by
      rw [hFstMap]
      exact (hV0I J).aestronglyMeasurable
    have he := integral_map (μ := revealLaw P) (φ := Prod.fst) measurable_fst.aemeasurable hVm
    rw [hFstMap] at he
    exact (integral_congr_ae (ae_of_all _ (hInitialEq J))).trans he.symm
  have hRfl : Shao.Probability.SourceActualLocalProfileBudget.HalflineReflectionIdentities Q := by
    constructor
    · intro w y T z _ hT hy hz
      exact Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula Bm PB hBm w y T z hT hy hz
    · intro w y T z _ hT hy hz
      exact Shao.C2.BridgeLowerIdentification.bridge_lower_formula Bm PB hBm w y T z hT hy hz
  have hReg : ∀ w y T z : ℝ, 0 < w → 0 < T → |y| < w → |z| < w →
      DifferentiableAt ℝ (fun a => Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w a T z) y := by
    intro w y T z hw hT hy hz
    exact Shao.C2.ActualBridgeIntervalTelescope.actual_source_interval_differentiable Bm PB hBm w y T z hw hy hz hT
  have hKernel (J : MonitoredDomain) : Measurable (actualDerivativeFamily Q J) ∧
      KernelBounds J (eventCompletionKernel J Q) (actualDerivativeFamily Q J) 4 ∧
      ∀ w y T z : ℝ, 0 < w → 0 < T → Interior J w y → Interior J w z →
        HasDerivAt (fun a => eventCompletionKernel J Q (w, a, T, z)) (actualDerivativeFamily Q J (w, y, T, z)) y := by
    cases J with
    | upper => exact Shao.Probability.SourceActualLocalProfileBudget.actual_halfline_kernel_data Q hRfl .upper (Or.inl rfl)
    | lower => exact Shao.Probability.SourceActualLocalProfileBudget.actual_halfline_kernel_data Q hRfl .lower (Or.inr rfl)
    | interval =>
        simpa only [actualDerivativeFamily, Interior, abs_lt] using
          Shao.Probability.SourceActualIntervalProfileBudget.actual_interval_kernel_data Q hRfl hReg
  let nu : Shao.Path n → LabelPerm n → ℕ := fun a sigma => energyCutoff a H sigma
  let future : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ := fun J p =>
    (Finset.range (n + 1)).sup'
      ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩
      (fun j => if energyCutoff p.1 H p.2 ≤ j then
        |sourceValue J (eventCompletionKernel J Q) p.1 x j p.2 -
          (if sourceAlive J p.1 x n p.2 then 1 else 0)| else 0)
  have hnum (sigma : LabelPerm n) : Measurable (fun a : Shao.Path n => nu a sigma) :=
    Shao.Probability.SourceActualLocalProfileBudget.actual_energy_cutoff_measurable H hH sigma
  have hnub (a : Shao.Path n) (sigma : LabelPerm n) : nu a sigma ≤ n := (energy_cutoff_data a H hH).1.1 sigma
  have hnustop (a : Shao.Path n) : IsRevealStoppingRank (nu a) := (energy_cutoff_data a H hH).1
  let L : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℕ → ℝ := fun J p r =>
    sourceRetainedRemainder J (eventCompletionKernel J Q) (actualDerivativeFamily Q J) p.1 x (nu p.1) r p.2
  let O : (Shao.Path n × LabelPerm n) → ℕ → ℝ := fun p r =>
    sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval) p.1 x (nu p.1) r p.2
  have hParts (J : MonitoredDomain) := source_parts_measurable_integrable J (eventCompletionKernel J Q)
    (actualDerivativeFamily Q J) (eventCompletionKernel_data J Q).1 (hKernel J).1 4 (hKernel J).2.1 P x hxpos nu hnum
  have hLI (J : MonitoredDomain) (r : ℕ) : Integrable (fun p => |L J p r|) (revealLaw P) :=
    ((hParts J).2.1 r).1.abs
  have hOI (r : ℕ) : Integrable (fun p => max (-O p r) 0) (revealLaw P) := by
    have hi := ((((hParts .interval).2.1 r).2.abs).sub ((hParts .interval).2.1 r).2).div_const 2
    change Integrable (fun p => (|O p r| - O p r) / 2) (revealLaw P) at hi
    have he : (fun p => (|O p r| - O p r) / 2) = (fun p => max (-O p r) 0) := by
      funext p
      by_cases ho : 0 ≤ O p r
      · rw [abs_of_nonneg ho, max_eq_right (neg_nonpos.mpr ho)]
        ring
      · have hn : O p r ≤ 0 := le_of_not_ge ho
        rw [abs_of_nonpos hn, max_eq_left (neg_nonneg.mpr hn)]
        ring
    rw [he] at hi
    exact hi
  have hInitialI (J : MonitoredDomain) : Integrable (Vinitial J) (revealLaw P) := by
    have hh := (source_stopped_integrability J (eventCompletionKernel J Q) (actualDerivativeFamily Q J)
      (eventCompletionKernel_data J Q).1 (hKernel J).1 4 (hKernel J).2.1 P x hxpos nu hnum hnub
      (fun _ => 1) measurable_const (fun _ => by norm_num)).2.1
    simpa only [one_mul] using hh
  have hBData := hBill rho bound hb hsupport hmean hsecond n hn x hx hscale Bm PB hBm nu hnum (fun _ _ => le_rfl)
  have hB : ((∫ p, ∑ r ∈ Finset.range n, |L .upper p r| ∂revealLaw P) +
      (∫ p, ∑ r ∈ Finset.range n, |L .lower p r| ∂revealLaw P) +
      (∫ p, ∑ r ∈ Finset.range n, |L .interval p r| ∂revealLaw P) +
      (∫ p, ∑ r ∈ Finset.range n, max (-O p r) 0 ∂revealLaw P)) ≤ CB * delta := by
    simp_rw [← Fin.sum_univ_eq_sum_range]
    have hi (J : MonitoredDomain) : Integrable (fun p => ∑ r : Fin n, |L J p r.val|) (revealLaw P) :=
      integrable_finsetSum _ (fun r _ => hLI J r.val)
    have hio : Integrable (fun p => ∑ r : Fin n, max (-O p r.val) 0) (revealLaw P) :=
      integrable_finsetSum _ (fun r _ => hOI r.val)
    have he1 := integral_add (hi .upper) (hi .lower)
    have he2 := integral_add ((hi .upper).add (hi .lower)) (hi .interval)
    have he3 := integral_add (((hi .upper).add (hi .lower)).add (hi .interval)) hio
    simp only [Pi.add_apply] at he1 he2 he3
    rw [← he1, ← he2, ← he3]
    have heq : (fun p => ((∑ r : Fin n, |L .upper p r.val|) + (∑ r : Fin n, |L .lower p r.val|)) +
        (∑ r : Fin n, |L .interval p r.val|) + (∑ r : Fin n, max (-O p r.val) 0)) =
        (fun p => ∑ r : Fin n, actualRetainedAbsoluteRank Q p.1 x (nu p.1) r p.2) := by
      funext p
      simp only [actualRetainedAbsoluteRank, L, O, Finset.sum_add_distrib]
      ring
    rw [heq]
    exact hBData.2.2.2.2.1
  have hE : ∀ J : MonitoredDomain,
      (∫ p, |sourceValue J (eventCompletionKernel J Q) p.1 x (nu p.1 p.2) p.2 - A J p| ∂revealLaw P) ≤ CE * delta := by
    intro J
    rcases hTerminal rho bound hb hsupport hmean hsecond n hn x hx hscale Bm PB hBm J with
      ⟨hidm, hidi, hidr, hid0, hidB, hfm, hfi, hfr, hf0, hfB⟩
    have hStopI : Integrable (fun p => sourceValue J (eventCompletionKernel J Q) p.1 x (nu p.1 p.2) p.2) (revealLaw P) := by
      have hh := (source_stopped_integrability J (eventCompletionKernel J Q) (actualDerivativeFamily Q J)
        (eventCompletionKernel_data J Q).1 (hKernel J).1 4 (hKernel J).2.1 P x hxpos nu hnum hnub
        (fun _ => 1) measurable_const (fun _ => by norm_num)).1
      simpa only [one_mul] using hh
    calc
      _ ≤ ∫ p, future J p ∂revealLaw P := by
        apply integral_mono (hStopI.sub (hAI J)).abs hfi
        intro p
        have hh := Finset.le_sup'
          (fun j => if nu p.1 p.2 ≤ j then |sourceValue J (eventCompletionKernel J Q) p.1 x j p.2 - A J p| else 0)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le (hnub p.1 p.2)))
        simpa only [if_pos le_rfl, future, nu, A, Pi.sub_apply,
          H, Q, Nat.succ_eq_add_one] using hh
      _ ≤ CE * delta ^ 2 := hfB
      _ ≤ CE * delta := mul_le_mul_of_nonneg_left hd2 hCE.le
  have hG : ∀ J : MonitoredDomain, J = .upper ∨ J = .lower →
      |(∫ p, A J p ∂revealLaw P) - (∫ p, Vinitial J p ∂revealLaw P)| ≤ KG * delta := by
    intro J hJ
    obtain ⟨s, hsign, hJs⟩ : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
        ((J = .upper ∧ s = 1) ∨ (J = .lower ∧ s = -1)) := by
      rcases hJ with rfl | rfl
      · exact ⟨1, Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨-1, Or.inr rfl, Or.inr ⟨rfl, rfl⟩⟩
    let U : Set (Shao.Path n) := {a | x * Real.sqrt (Shao.energy a) ≤ Shao.upperMax (s • a) hn}
    have hUm : MeasurableSet U := measurableSet_le (Shao.measurable_energyWall x)
      ((Shao.measurable_upperMax hn).comp (Measurable.of_eval fun i => measurable_const.mul (measurable_pi_apply i)))
    have hComp : S J = Uᶜ := by
      ext a
      rcases hJs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [S, U, Set.mem_setOf_eq, Set.mem_compl_iff, not_le, one_smul, neg_one_smul, actualWall]
    have hCross := (hC1Data.2.2.2 s hsign).2
    change |P.real U - 2 * Shao.standardNormalTail x| ≤ K1 * delta at hCross
    have hSurv : |P.real (S J) - (1 - 2 * Shao.standardNormalTail x)| ≤ K1 * delta := by
      rw [hComp, measureReal_compl hUm, probReal_univ]
      have he : (1 - P.real U) - (1 - 2 * Shao.standardNormalTail x) =
          -(P.real U - 2 * Shao.standardNormalTail x) := by ring
      rw [he, abs_neg]
      exact hCross
    have hVGap := (hHalf.1 J hJ).2
    rw [hAIntegral J, hInitialIntegral J]
    calc
      _ ≤ |P.real (S J) - (1 - 2 * Shao.standardNormalTail x)| +
          |(1 - 2 * Shao.standardNormalTail x) - (∫ a, V0 J a ∂P)| := abs_sub_le _ _ _
      _ ≤ K1 * delta + CS * delta := by
        apply add_le_add hSurv
        simpa only [abs_sub_comm] using hVGap
      _ = KG * delta := by dsimp [KG]; ring
  have hTransfer := source_three_domain_overshoot_transfer P Q (actualDerivativeFamily Q)
    (fun J => (hKernel J).1) 4 (by norm_num)
    (fun J => (hKernel J).2.1.derivative_bound) (fun J => (hKernel J).2.2)
    x hxpos H hH nu hnum hnustop (fun _ _ => le_rfl) (CB * delta) (CE * delta) (KG * delta) hB hE hG
  have ht := hTransfer.2.2 (fun _ => 1) measurable_const (fun _ => by norm_num) (fun _ _ => rfl)
  simp only [one_mul] at ht
  change |(∫ p, A .interval p - Vinitial .interval p ∂revealLaw P)| ≤
    3 * (CB * delta) + 3 * (CE * delta) + 2 * (KG * delta) at ht
  rw [integral_sub (hAI .interval) (hInitialI .interval), hAIntegral .interval, hInitialIntegral .interval] at ht
  let SB : Set ΩB := {omegaB | ∀ t : BridgeTime, |Bm ⟨(t : ℝ), t.property.1⟩ omegaB| < x}
  have hInitB : |(∫ a, V0 .interval a ∂P) - PB.real SB| ≤ CI * delta :=
    (hInit.2 (Equiv.refl (Fin n))).2.2.1
  have hStrict : |P.real (S .interval) - PB.real SB| ≤ CA * delta := by
    calc
      _ ≤ |P.real (S .interval) - ∫ a, V0 .interval a ∂P| + |(∫ a, V0 .interval a ∂P) - PB.real SB| := abs_sub_le _ _ _
      _ ≤ (3 * (CB * delta) + 3 * (CE * delta) + 2 * (KG * delta)) + CI * delta := add_le_add ht hInitB
      _ ≤ CA * delta := by dsimp [CA]; nlinarith only [hdelta]
  have hBPair : AEMeasurable (fun omegaB : ΩB => (bridgeNoise Bm omegaB, Bm 1 omegaB)) PB :=
    (aemeasurable_bridgeNoise Bm PB hBm).prodMk (hBm.toIsPreBrownianReal.aemeasurable 1)
  have hBAE : (fun omegaB : ΩB => (bridgeNoise Bm omegaB, Bm 1 omegaB)) ⁻¹' initialSurvival x =ᵐ[PB] SB := by
    filter_upwards [ae_bridgeNoise_eq Bm PB hBm] with omegaB homegaB
    apply propext
    rw [Set.mem_preimage, mem_initialSurvival_iff]
    have he (t : BridgeTime) : bridgePath 0 1 (Bm 1 omegaB) (bridgeNoise Bm omegaB) t =
        Bm ⟨(t : ℝ), t.property.1⟩ omegaB := by
      simp only [bridgePath, ContinuousMap.coe_mk, mul_zero, zero_add, Real.sqrt_one, one_mul]
      rw [homegaB t]
      ring
    simp only [he, SB, Set.mem_setOf_eq]
  have hSBnull : NullMeasurableSet SB PB :=
    (hBPair.nullMeasurableSet_preimage (measurableSet_initialSurvival x)).congr hBAE
  have hWeak : {a : Shao.Path n | x * Real.sqrt (Shao.energy a) ≤ Shao.absMax a hn} = (S .interval)ᶜ := by
    ext a
    simp only [S, Set.mem_setOf_eq, Set.mem_compl_iff, not_lt, actualWall]
  have hBWeak : {omegaB | ∃ t : BridgeTime, x ≤ |Bm ⟨(t : ℝ), t.property.1⟩ omegaB|} = SBᶜ := by
    ext omegaB
    simp only [SB, Set.mem_setOf_eq, Set.mem_compl_iff, not_forall, not_lt]
  rw [hWeak, hBWeak, measureReal_compl (hSm .interval), measureReal_compl₀ hSBnull, probReal_univ]
  simp only [probReal_univ]
  have he : (1 - P.real (S .interval)) - (1 - PB.real SB) = -(P.real (S .interval) - PB.real SB) := by ring
  rw [he, abs_neg]
  exact hStrict

theorem iid_actual_bounded_centered_uniform_absolute_fixed_threshold_comparison :
    ∃ epsilonF CA KD : ℝ, 0 < epsilonF ∧ epsilonF ≤ 1 / 8 ∧ 0 < CA ∧ 0 < KD ∧
      ∀ (M : ℝ), (1 / 2 : ℝ) ≤ M → ∃ CF : ℝ, 0 < CF ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (bound : ℝ), 0 < bound → (∀ᵐ z : ℝ ∂rho, |z| ≤ bound) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        ∀ (n : ℕ) (hn : 0 < n) (x : ℝ), (1 / 2 : ℝ) ≤ x →
          bound ≤ Real.sqrt (n : ℝ) / (100 * x) →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          let delta : ℝ := beta / Real.sqrt (n : ℝ)
          delta * x ^ 3 ≤ epsilonF →
          ∀ {ΩB : Type*} [MeasurableSpace ΩB]
            (Bm : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
            IsBrownianReal Bm PB →
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
            let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) rho
            let brownianDouble : Set ΩB := {omegaB |
              (∃ t : BridgeTime, x ≤ Bm ⟨(t : ℝ), t.property.1⟩ omegaB) ∧
              (∃ t : BridgeTime, Bm ⟨(t : ℝ), t.property.1⟩ omegaB ≤ -x)}
            Shao.truncationBudget normalizedLaw n 0 = delta ∧
              Shao.truncationBudget normalizedLaw n x = delta * (1 + x) ^ 3 ∧
              |P.real (doubleCrossingEvent x) - PB.real brownianDouble| ≤ KD * delta ∧
              (x ≤ M → |P.real (doubleCrossingEvent x) - PB.real brownianDouble| ≤
                CF * delta * (1 + x) ^ 3 * Shao.standardNormalTail x) ∧
              |P.real {a | x * Real.sqrt (Shao.energy a) ≤ Shao.absMax a hn} -
                PB.real {omegaB | ∃ t : BridgeTime,
                  x ≤ |Bm ⟨(t : ℝ), t.property.1⟩ omegaB|}| ≤ CA * delta := by
  classical
  obtain ⟨epsA, CA, hEpsA, hEpsA8, hCA, hAbsolute⟩ := uaf_absolute_comparison_all_thresholds
  obtain ⟨rhoStar, eps1, C1, K1, hrho, hrho16, hEps1Eq, hEps1, hC1, hK1, hSegment⟩ :=
    uaf_legal_c1_all_thresholds
  obtain ⟨CS, hCS, hHalfInitial⟩ :=
    Shao.C2.ActualBoundedCenteredFixed.iid_actual_halfline_initial_all_positive
  let epsilonF : ℝ := min epsA eps1
  let KD : ℝ := 2 * K1 + CA
  have hKD : 0 < KD := by dsimp [KD]; positivity
  refine ⟨epsilonF, CA, KD, lt_min hEpsA hEps1, (min_le_left _ _).trans hEpsA8, hCA, hKD, ?_⟩
  intro M hM
  let CF : ℝ := 1 + KD / Shao.standardNormalTail M
  have htM : 0 < Shao.standardNormalTail M := (Shao.standardNormalTail_basic.2.2.1 M).1
  have hCF : 0 < CF := by dsimp [CF]; positivity
  refine ⟨CF, hCF, ?_⟩
  intro rho hProb bound hb hsupport hmean hsecond n hn x hx hscale beta delta hsmall
    ΩB hΩB Bm PB hPB hBm P normalizedLaw brownianDouble
  letI : IsProbabilityMeasure rho := hProb
  letI : IsProbabilityMeasure PB := hPB
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  rcases Shao.C2.ActualBoundedCenteredFixed.iid_actual_bounded_own_budget_identities rho bound hb hsupport hmean hsecond n hn x hx hscale with
    ⟨h1, h2, h3, hbound1, hbeta, hdelta, hH, hnlarge, hR0, hRx, hcut, hPrefixBudget⟩
  have hxpos : 0 < x := by linarith only [hx]
  have hsmallA : delta * x ^ 3 ≤ epsA := hsmall.trans (min_le_left _ _)
  have hsmall1 : delta * x ^ 3 ≤ eps1 := hsmall.trans (min_le_right _ _)
  have hC1Data := hSegment rho bound hb hsupport hmean hsecond n hn x hx hscale hsmall1
  have hAbs := hAbsolute rho bound hb hsupport hmean hsecond n hn x hx hscale hsmallA Bm PB hBm
  have hBoundRoot : bound ≤ Real.sqrt (n : ℝ) := by
    have hh : (100 * x) * bound ≤ Real.sqrt (n : ℝ) := by
      simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < 100 * x)).mp hscale
    exact (le_mul_of_one_le_left hb.le (by linarith only [hx] : 1 ≤ 100 * x)).trans hh
  have hHalf := hHalfInitial rho bound hb hsupport hmean hsecond n hn hBoundRoot Bm PB hBm x hxpos
  let U : Set (Shao.Path n) := {a | actualWall a x ≤ Shao.upperMax a hn}
  let L : Set (Shao.Path n) := {a | actualWall a x ≤ Shao.upperMax (-a) hn}
  let W : Set (Shao.Path n) := {a | actualWall a x ≤ Shao.absMax a hn}
  let UB : Set ΩB := {omegaB | ∃ t : BridgeTime, x ≤ Bm ⟨(t : ℝ), t.property.1⟩ omegaB}
  let LB : Set ΩB := {omegaB | ∃ t : BridgeTime, Bm ⟨(t : ℝ), t.property.1⟩ omegaB ≤ -x}
  let WB : Set ΩB := {omegaB | ∃ t : BridgeTime, x ≤ |Bm ⟨(t : ℝ), t.property.1⟩ omegaB|}
  have hUm : MeasurableSet U := measurableSet_le (Shao.measurable_energyWall x) (Shao.measurable_upperMax hn)
  have hLm : MeasurableSet L := measurableSet_le (Shao.measurable_energyWall x)
    ((Shao.measurable_upperMax hn).comp (by fun_prop))
  have hHit (s : ℝ) (hsign : s = 1 ∨ s = -1) (a : Shao.Path n) :
      (∃ r : ℕ, r ≤ n ∧ actualWall a x ≤ s * Shao.prefixSum a r) ↔
        actualWall a x ≤ Shao.upperMax (s • a) hn := by
    constructor
    · rintro ⟨r, hr, hc⟩
      by_cases hr0 : r = 0
      · have hw0 : actualWall a x ≤ 0 := by simpa only [hr0, Shao.prefixSum_zero, mul_zero] using hc
        have hE0 : Shao.energy a = 0 := by
          by_contra hne
          have hp : 0 < Shao.energy a := lt_of_le_of_ne (Shao.energy_nonneg a) (Ne.symm hne)
          exact (not_lt_of_ge hw0) (mul_pos hxpos (Real.sqrt_pos.mpr hp))
        have hSigned0 : Shao.energy (s • a) = 0 := by
          rcases hsign with rfl | rfl <;> simpa using hE0
        rw [Shao.upperMax_eq_zero_of_energy_eq_zero _ hn hSigned0]
        exact hw0
      · have hp := Shao.le_upperMax (s • a) hn r (Nat.one_le_iff_ne_zero.mpr hr0) hr
        rw [Shao.prefixSum_smul] at hp
        exact hc.trans hp
    · intro hc
      obtain ⟨r, hr, hrn, hEq⟩ := Shao.upperMax_attained (s • a) hn
      refine ⟨r, hrn, ?_⟩
      rw [hEq, Shao.prefixSum_smul] at hc
      exact hc
  have hDouble : doubleCrossingEvent x = U ∩ L := by
    ext a
    change ((∃ r : ℕ, r ≤ n ∧ actualWall a x ≤ Shao.prefixSum a r) ∧
      (∃ r : ℕ, r ≤ n ∧ Shao.prefixSum a r ≤ -actualWall a x)) ↔
      (actualWall a x ≤ Shao.upperMax a hn ∧ actualWall a x ≤ Shao.upperMax (-a) hn)
    constructor
    · rintro ⟨⟨r, hr, hc⟩, ⟨t, ht, hd⟩⟩
      constructor
      · simpa only [one_smul] using (hHit 1 (Or.inl rfl) a).mp ⟨r, hr, by simpa only [one_mul] using hc⟩
      · simpa only [neg_one_smul] using
          (hHit (-1) (Or.inr rfl) a).mp ⟨t, ht, by simp only [neg_one_mul]; linarith only [hd]⟩
    · rintro ⟨hu, hl⟩
      obtain ⟨r, hr, hc⟩ := (hHit 1 (Or.inl rfl) a).mpr (by simpa only [one_smul] using hu)
      obtain ⟨t, ht, hd⟩ := (hHit (-1) (Or.inr rfl) a).mpr (by simpa only [neg_one_smul] using hl)
      refine ⟨⟨r, hr, by simpa only [one_mul] using hc⟩, ⟨t, ht, ?_⟩⟩
      simp only [neg_one_mul] at hd
      linarith only [hd]
  have hUnion : U ∪ L = W := by
    ext a
    simp only [U, L, W, Set.mem_union, Set.mem_setOf_eq, Shao.absMax, Shao.lowerMax, le_max_iff]
  have hBUnion : UB ∪ LB = WB := by
    ext omegaB
    constructor
    · rintro (⟨t, ht⟩ | ⟨t, ht⟩)
      · exact ⟨t, ht.trans (le_abs_self _)⟩
      · exact ⟨t, (by linarith only [ht] : x ≤ -Bm ⟨(t : ℝ), t.property.1⟩ omegaB).trans (neg_le_abs _)⟩
    · rintro ⟨t, ht⟩
      by_cases hz : 0 ≤ Bm ⟨(t : ℝ), t.property.1⟩ omegaB
      · rw [abs_of_nonneg hz] at ht
        exact Or.inl ⟨t, ht⟩
      · rw [abs_of_neg (lt_of_not_ge hz)] at ht
        exact Or.inr ⟨t, by linarith only [ht]⟩
  have hBDouble : brownianDouble = UB ∩ LB := by
    ext omegaB
    rfl
  have hUpperNull (Y : ℝ≥0 → ΩB → ℝ) (hY : IsBrownianReal Y PB) :
      NullMeasurableSet {omegaB | ∃ t : BridgeTime, x ≤ Y ⟨(t : ℝ), t.property.1⟩ omegaB} PB := by
    let K : Set (ContinuousMap BridgeTime ℝ) := {f | ∃ t : BridgeTime, x ≤ f t}
    have ho : IsOpen {f : ContinuousMap BridgeTime ℝ | ∀ t : BridgeTime, f t < x} := by
      simpa [Set.MapsTo] using
        (ContinuousMap.isOpen_setOfPred_mapsTo (X := BridgeTime) isCompact_univ (isOpen_Iio (a := x)))
    have hK : MeasurableSet K := by
      have he : K = {f : ContinuousMap BridgeTime ℝ | ∀ t : BridgeTime, f t < x}ᶜ := by
        ext f
        simp only [K, Set.mem_setOf_eq, Set.mem_compl_iff, not_forall, not_lt]
      rw [he]
      exact ho.measurableSet.compl
    have hm := (Shao.OQ4.PolygonalBrownianWeakLimit.aemeasurable_brownianUnitPath Y 1 PB hY).nullMeasurableSet_preimage hK
    apply hm.congr
    filter_upwards [Shao.OQ4.PolygonalBrownianWeakLimit.ae_brownianUnitPath_eq Y 1 PB hY] with omegaB homegaB
    apply propext
    change (∃ t : BridgeTime, x ≤ Shao.OQ4.PolygonalBrownianWeakLimit.brownianUnitPath Y 1 omegaB t) ↔ _
    have ht (t : BridgeTime) : Shao.OQ4.PolygonalBrownianWeakLimit.brownianUnitPath Y 1 omegaB t =
        Y ⟨(t : ℝ), t.property.1⟩ omegaB := by
      have hh := homegaB t
      change Shao.OQ4.PolygonalBrownianWeakLimit.brownianUnitPath Y 1 omegaB t =
        Y (1 * ⟨(t : ℝ), t.property.1⟩) omegaB at hh
      exact hh.trans (congrArg (fun q : ℝ≥0 => Y q omegaB) (_root_.one_mul _))
    simp only [ht]
  have hUBnull : NullMeasurableSet UB PB := hUpperNull Bm hBm
  have hLBnull : NullMeasurableSet LB PB := by
    have he : LB = {omegaB | ∃ t : BridgeTime, x ≤ (-Bm) ⟨(t : ℝ), t.property.1⟩ omegaB} := by
      ext omegaB
      change (∃ t : BridgeTime, Bm ⟨(t : ℝ), t.property.1⟩ omegaB ≤ -x) ↔
        ∃ t : BridgeTime, x ≤ -(Bm ⟨(t : ℝ), t.property.1⟩ omegaB)
      constructor <;> rintro ⟨t, ht⟩ <;> exact ⟨t, by linarith only [ht]⟩
    rw [he]
    exact hUpperNull (-Bm) hBm.neg
  have hUB : PB.real UB = 2 * Shao.standardNormalTail x := by simpa only [one_mul] using hHalf.2 1 (Or.inl rfl)
  have hLB : PB.real LB = 2 * Shao.standardNormalTail x := by
    have he : LB = {omegaB | ∃ t : BridgeTime, x ≤ (-1 : ℝ) * Bm ⟨(t : ℝ), t.property.1⟩ omegaB} := by
      ext omegaB
      simp only [LB, Set.mem_setOf_eq, neg_one_mul]
      constructor <;> rintro ⟨t, ht⟩ <;> exact ⟨t, by linarith only [ht]⟩
    rw [he]
    exact hHalf.2 (-1) (Or.inr rfl)
  have hUError : |P.real U - 2 * Shao.standardNormalTail x| ≤ K1 * delta := by
    simpa only [one_smul, U, actualWall] using (hC1Data.2.2.2 1 (Or.inl rfl)).2
  have hLError : |P.real L - 2 * Shao.standardNormalTail x| ≤ K1 * delta := by
    simpa only [neg_one_smul, L, actualWall] using (hC1Data.2.2.2 (-1) (Or.inr rfl)).2
  have hWError : |P.real W - PB.real WB| ≤ CA * delta := hAbs
  have hFiniteIE := measureReal_union_add_inter₀ (μ := P) (s := U) hLm.nullMeasurableSet
  rw [hUnion, ← hDouble] at hFiniteIE
  have hBrownianIE := measureReal_union_add_inter₀ (μ := PB) (s := UB) hLBnull
  rw [hBUnion, ← hBDouble, hUB, hLB] at hBrownianIE
  have hDoubleError : |P.real (doubleCrossingEvent x) - PB.real brownianDouble| ≤ KD * delta := by
    have he : P.real (doubleCrossingEvent x) - PB.real brownianDouble =
        (P.real U - 2 * Shao.standardNormalTail x) + (P.real L - 2 * Shao.standardNormalTail x) -
        (P.real W - PB.real WB) := by linarith only [hFiniteIE, hBrownianIE]
    rw [he]
    calc
      _ ≤ |(P.real U - 2 * Shao.standardNormalTail x) + (P.real L - 2 * Shao.standardNormalTail x)| +
          |P.real W - PB.real WB| := abs_sub _ _
      _ ≤ (|P.real U - 2 * Shao.standardNormalTail x| + |P.real L - 2 * Shao.standardNormalTail x|) +
          |P.real W - PB.real WB| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ (K1 * delta + K1 * delta) + CA * delta := add_le_add (add_le_add hUError hLError) hWError
      _ = KD * delta := by dsimp [KD]; ring
  refine ⟨hR0, hRx, hDoubleError, ?_, hAbs⟩
  intro hxM
  have hWeight : Shao.standardNormalTail M ≤ (1 + x) ^ 3 * Shao.standardNormalTail x := by
    have ht : Shao.standardNormalTail M ≤ Shao.standardNormalTail x := Shao.standardNormalTail_basic.1 hxM
    have hc : (1 : ℝ) ≤ (1 + x) ^ 3 := by
      calc
        (1 : ℝ) = 1 ^ 3 := by norm_num
        _ ≤ (1 + x) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith only [hx]) 3
    exact ht.trans (le_mul_of_one_le_left (Shao.standardNormalTail_basic.2.2.1 x).1.le hc)
  have hCFPay : KD ≤ CF * Shao.standardNormalTail M := by
    have he : CF * Shao.standardNormalTail M = Shao.standardNormalTail M + KD := by
      dsimp only [CF]
      field_simp [htM.ne']
      <;> ring
    rw [he]
    linarith only [htM]
  calc
    |P.real (doubleCrossingEvent x) - PB.real brownianDouble| ≤ KD * delta := hDoubleError
    _ ≤ (CF * Shao.standardNormalTail M) * delta := mul_le_mul_of_nonneg_right hCFPay hdelta.le
    _ ≤ (CF * ((1 + x) ^ 3 * Shao.standardNormalTail x)) * delta :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWeight hCF.le) hdelta.le
    _ = CF * delta * (1 + x) ^ 3 * Shao.standardNormalTail x := by ring

end Shao.C2.ActualUniformAbsoluteFixedThreshold
