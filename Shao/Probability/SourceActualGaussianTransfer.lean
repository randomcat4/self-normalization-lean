/- Mathematical candidate only. Exact original Brownian three-domain consumer.
   PR309 and the scalar second frozen head are dependencies pending their own final qualification.
   No production bodies, no Lean/AX/cache execution. -/
import Shao.Probability.SourceActualTransferAssembly
import Shao.Probability.SourceScalarInitialBudget

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.Probability.SourceActualGaussianTransfer
open MeasureTheory ProbabilityTheory
open SourcePermutationReveal SourceSeparatedOvershoot SourceActualLocalProfileBudget
open SourceActualIntervalProfileBudget
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open scoped BigOperators Classical NNReal

local instance labelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

theorem actual_brownian_three_domain_transfer_budget :
    ∀ Csmall : ℝ, 0 ≤ Csmall → ∃ C : ℝ, 0 < C ∧
      ∀ {ΩB : Type*} [MeasurableSpace ΩB]
        (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : ℝ≥0 → ΩB → ℝ), IsBrownianReal B PB →
        let Q : Measure BridgeNoise := bridgeLaw B PB
        HalflineReflectionIdentities Q →
        (∀ w y T z : ℝ, 0 < w → 0 < T → |y| < w → |z| < w →
          DifferentiableAt ℝ
            (fun s : ℝ => Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w s T z) y) →
        (∀ w y T z beta : ℝ, 0 < w → 0 < T → |y| < w → |z| < w →
          beta ^ 2 ≤ T / 2 → |y + beta| ≤ w →
          |Shao.C2.ActualIntervalProjection.sourceRemainder Q w y T z beta| ≤
            Csmall * |beta| ^ 3 * (1 / Real.sqrt T) ^ 3 *
              (1 + |z - y| / Real.sqrt T) ^ 3 *
                Shao.C2.IntervalGaussianLocal.intervalIncrementProfile w y T z beta) →
        ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho] (n : ℕ), 0 < n →
          Integrable (fun z : ℝ => z ^ 2) rho →
          (∫ z : ℝ, z ∂rho) = 0 → 0 < (∫ z : ℝ, z ^ 2 ∂rho) →
          let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
          let scale : ℝ := Real.sqrt ((n : ℝ) * sigmaSq)
          let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / scale) rho
          let R : ℝ := Shao.truncationBudget normalizedLaw n 0
          let h : ℝ := 4 * (n : ℝ) * sigmaSq * R ^ 2
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
          let nu : Shao.Path n → LabelPerm n → ℕ := fun a sigma => energyCutoff a h sigma
          ∀ (x : ℝ), 0 ≤ x → x ≤ 1 →
            let F : MonitoredDomain → BridgeKernel := fun J => eventCompletionKernel J Q
            let FY : MonitoredDomain → BridgeKernel := fun J => match J with
              | .upper => halflineDerivative .upper
              | .lower => halflineDerivative .lower
              | .interval => intervalDerivative Q
            let Vinitial : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ :=
              fun J p => sourceValue J (F J) p.1 x 0 p.2
            let Afinal : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ :=
              fun J p => if sourceAlive J p.1 x n p.2 then 1 else 0
            let O : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℕ → ℝ :=
              fun J p r => sourceSeparatedOvershoot J (FY J) p.1 x (nu p.1) r p.2
            let rawAbsolute : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
              ∑ r ∈ Finset.range n,
                |if r < nu p.1 p.2 then
                  sourceRemainder .interval (F .interval) (FY .interval) p.1 x r p.2
                else 0|
            (∀ J : MonitoredDomain, J = .upper ∨ J = .lower →
              Integrable (fun p => ∑ r ∈ Finset.range n, O J p r) (revealLaw P) ∧
              0 ≤ (∫ p, ∑ r ∈ Finset.range n, O J p r ∂revealLaw P) ∧
              (∫ p, ∑ r ∈ Finset.range n, O J p r ∂revealLaw P) ≤ C * R) ∧
            Integrable rawAbsolute (revealLaw P) ∧
            (∫ p, rawAbsolute p ∂revealLaw P) ≤ C * R ∧
            (∀ (m : Shao.Path n → ℝ), Measurable m → (∀ a, |m a| ≤ 1) →
              PermutationInvariant m →
              Integrable (fun p => m p.1 * (Afinal .interval p - Vinitial .interval p)) (revealLaw P) ∧
              |(∫ p, m p.1 * (Afinal .interval p - Vinitial .interval p) ∂revealLaw P)| ≤
                C * R) := by
  classical
  intro Csmall hCs
  obtain ⟨CA, hCA, hAssembly⟩ :=
    SourceActualTransferAssembly.actual_brownian_transfer_with_initial_gap Csmall hCs
  obtain ⟨CG, hCG, hInitial⟩ :=
    SourceScalarInitialBudget.finite_second_analytic_initial_host_gap
  refine ⟨CA + 2 * CG, by positivity, ?_⟩
  intro ΩB hΩB PB hPB B hB Q hReflection hRegular hSmall rho hrho n hn h2 hmean hsecond
    sigmaSq scale normalizedLaw R h P nu x hx0 hx1 F FY Vinitial Afinal O rawAbsolute
  letI : IsProbabilityMeasure PB := hPB
  letI : IsProbabilityMeasure rho := hrho
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw B PB hB
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hR : 0 < R := (raw_truncation_budget_suffix_geometry rho n hn h2 hsecond).1
  let Gamma : ℝ := max
    |(∫ p, Afinal .upper p ∂revealLaw P) - (∫ p, Vinitial .upper p ∂revealLaw P)|
    |(∫ p, Afinal .lower p ∂revealLaw P) - (∫ p, Vinitial .lower p ∂revealLaw P)|
  have hAsm := hAssembly PB B hB hReflection hRegular hSmall rho n hn h2 hmean hsecond x hx0 hx1
  have hGamma : Gamma ≤ CG * R := by
    by_cases hxzero : x = 0
    · have hdead (J : MonitoredDomain) (a : Shao.Path n) (r : ℕ) (sigma : LabelPerm n) :
          ¬ sourceAlive J a x r sigma := by
        intro ha
        have hz := ha.2.2 0 (Nat.zero_le r)
        cases J <;> simpa [Interior, actualWall, hxzero, Shao.prefixSum_zero] using hz
      have hz : Gamma = 0 := by
        simp [Gamma, Afinal, Vinitial, sourceValue, hdead]
      rw [hz]
      positivity
    have hx : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxzero)
    have hScale : Real.sqrt sigmaSq * Real.sqrt (n : ℝ) = scale := by
      dsimp only [scale]
      rw [Real.sqrt_mul (Nat.cast_nonneg n)]
      ring
    have hq (a : Shao.Path n) (sigma : LabelPerm n) :
        Shao.energy (Spitzer.reorder a sigma) = Shao.energy a := by
      simpa only [Shao.energy, Spitzer.reorder] using Equiv.sum_comp sigma (fun i => (a i)^2)
    have hs (a : Shao.Path n) (sigma : LabelPerm n) :
        Shao.prefixSum (Spitzer.reorder a sigma) n = Shao.prefixSum a n := by
      simpa only [Shao.prefixSum_length, Spitzer.reorder] using Equiv.sum_comp sigma a
    let X : Fin n → Shao.Path n → ℝ := fun i a => a i
    have hX (i : Fin n) : Measurable (X i) := measurable_pi_apply i
    have hLaw (i : Fin n) : IdentDistrib (X i) (id : ℝ → ℝ) P rho := by
      refine ⟨(hX i).aemeasurable, measurable_id.aemeasurable, ?_⟩
      simpa only [Measure.map_id] using
        (measurePreserving_eval (μ := fun _ : Fin n => rho) i).map_eq
    have hIndep : iIndepFun X P :=
      iIndepFun_pi (X := fun _ : Fin n => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)
    have hMap : Measure.map (randomReorder (n := n)) (revealLaw P) = P :=
      iid_randomPermutation_map_eq_pi P rho X hX hIndep hLaw
    have hRm : Measurable (randomReorder (n := n)) := by
      apply measurable_from_prod_countable_left
      intro sigma
      exact Measurable.of_eval (fun i => measurable_pi_apply (sigma i))
    have hPath : IdentDistrib (randomReorder (n := n)) (id : Shao.Path n → Shao.Path n)
        (revealLaw P) P :=
      ⟨hRm.aemeasurable, measurable_id.aemeasurable, by simpa only [Measure.map_id] using hMap⟩
    have hGap (J : MonitoredDomain) (s : ℝ)
        (hJs : (J = .upper ∧ s = 1) ∨ (J = .lower ∧ s = -1)) :
        |(∫ p, Afinal J p ∂revealLaw P) - (∫ p, Vinitial J p ∂revealLaw P)| ≤ CG * R := by
      have hsign : s = 1 ∨ s = -1 := hJs.imp And.right And.right
      let g : ℝ → ℝ := fun v => if v < x then 1 - Real.exp (-2*x*(x-v)) else 0
      let V : Shao.Path n → ℝ := fun a =>
        if 0 < Shao.energy a then g (s * Shao.C1.normalizedEndpoint a) else 0
      let E : Set (Shao.Path n) :=
        {a | Shao.maxWithZero (s • a) < x * Real.sqrt (Shao.energy a)}
      let A : Shao.Path n → ℝ := E.indicator (fun _ => (1 : ℝ))
      have hScalar : Integrable V P ∧
          (∀ a : Shao.Path n, V a = if 0 < Shao.energy a then
            Shao.C2.HalfLinePhysicalGaussian.upperCompletion
              (x * Real.sqrt (Shao.energy a)) 0 (Shao.energy a) (s * Shao.prefixSum a n)
            else 0) ∧
          |P.real E - (∫ a, V a ∂P)| ≤ CG * R := by
        have hi := hInitial rho n hn h2 hmean hsecond x hx hx1 s hsign
        change Integrable V P ∧
          (∀ a : Shao.Path n, V a = if 0 < Shao.energy a then
            Shao.C2.HalfLinePhysicalGaussian.upperCompletion
              (x * Real.sqrt (Shao.energy a)) 0 (Shao.energy a) (s * Shao.prefixSum a n)
            else 0) ∧
          |P.real E - (∫ a, V a ∂P)| ≤ CG * Shao.truncationBudget
            (Measure.map (fun z : ℝ => z / (Real.sqrt sigmaSq * Real.sqrt (n : ℝ))) rho) n 0 at hi
        rw [hScale] at hi
        exact hi
      have hLive0 (a : Shao.Path n) (sigma : LabelPerm n) :
          sourceAlive J a x 0 sigma ↔
            0 < Shao.energy a ∧ Interior J (actualWall a x) (Shao.prefixSum a n) := by
        refine ⟨fun ha => ⟨ha.1, ha.2.1⟩, ?_⟩
        rintro ⟨ha, hz⟩
        refine ⟨ha, hz, ?_⟩
        intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
        subst k
        have hw : 0 < actualWall a x := mul_pos hx (Real.sqrt_pos.2 ha)
        rcases hJs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simpa only [Shao.prefixSum_zero, Interior] using hw
        · change -actualWall a x < Shao.prefixSum (Spitzer.reorder a sigma) 0
          rw [Shao.prefixSum_zero]
          linarith only [hw]
      have hV (a : Shao.Path n) (sigma : LabelPerm n) : Vinitial J (a, sigma) = V a := by
        rw [hScalar.2.1 a]
        change sourceValue J (eventCompletionKernel J Q) a x 0 sigma = _
        rw [sourceValue]
        simp only [Shao.prefixSum_zero, remainingEnergy, Shao.prefixSquares_zero, sub_zero]
        by_cases ha : 0 < Shao.energy a
        · have hw : 0 < actualWall a x := mul_pos hx (Real.sqrt_pos.2 ha)
          have hcurrent : Interior J (actualWall a x) 0 := by
            rcases hJs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hw
            · change -actualWall a x < 0
              linarith only [hw]
          by_cases hz : Interior J (actualWall a x) (Shao.prefixSum a n)
          · have hlive := (hLive0 a sigma).2 ⟨ha, hz⟩
            rw [if_pos hlive, if_pos ha, completionExt, if_pos ⟨hw, hcurrent, hz⟩, if_pos ha]
            rcases hJs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · change upperCompletion Q (actualWall a x) 0 (Shao.energy a) (Shao.prefixSum a n) = _
              rw [hReflection.1 _ _ _ _ hw ha hw hz]
              change 1 - Real.exp (-2 * (actualWall a x - 0) *
                (actualWall a x - Shao.prefixSum a n) / Shao.energy a) =
                Shao.C2.HalfLinePhysicalGaussian.upperCompletion
                  (actualWall a x) 0 (Shao.energy a) (1 * Shao.prefixSum a n)
              simp only [Shao.C2.HalfLinePhysicalGaussian.upperCompletion,
                Shao.C2.HalfLineGaussianStep.completion, one_mul, sub_zero,
                if_pos (show 0 < actualWall a x ∧ 0 < actualWall a x - Shao.prefixSum a n from
                  ⟨hw, sub_pos.mpr hz⟩), if_pos ha]
            · change lowerCompletion Q (actualWall a x) 0 (Shao.energy a) (Shao.prefixSum a n) = _
              have hc : -actualWall a x < 0 := by linarith only [hw]
              rw [hReflection.2 _ _ _ _ hw ha hc hz]
              change 1 - Real.exp (-2 * (actualWall a x + 0) *
                (actualWall a x + Shao.prefixSum a n) / Shao.energy a) =
                Shao.C2.HalfLinePhysicalGaussian.upperCompletion
                  (actualWall a x) 0 (Shao.energy a) ((-1) * Shao.prefixSum a n)
              have hv : 0 < actualWall a x + Shao.prefixSum a n := by
                change -actualWall a x < Shao.prefixSum a n at hz
                linarith only [hz]
              simp only [Shao.C2.HalfLinePhysicalGaussian.upperCompletion,
                Shao.C2.HalfLineGaussianStep.completion, neg_one_mul, sub_zero,
                sub_neg_eq_add, add_zero, if_pos (show 0 < actualWall a x ∧
                  0 < actualWall a x + Shao.prefixSum a n from ⟨hw, hv⟩), if_pos ha]
          · have hdead : ¬ sourceAlive J a x 0 sigma := fun hlive => hz hlive.2.1
            rw [if_neg hdead, if_pos ha]
            rcases hJs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · change 0 = Shao.C2.HalfLinePhysicalGaussian.upperCompletion
                (actualWall a x) 0 (Shao.energy a) (1 * Shao.prefixSum a n)
              have hv : ¬ 0 < actualWall a x - Shao.prefixSum a n := by
                change ¬ Shao.prefixSum a n < actualWall a x at hz
                exact fun hv => hz (sub_pos.mp hv)
              simp only [Shao.C2.HalfLinePhysicalGaussian.upperCompletion,
                Shao.C2.HalfLineGaussianStep.completion, one_mul, sub_zero,
                if_neg (show ¬ (0 < actualWall a x ∧
                  0 < actualWall a x - Shao.prefixSum a n) from fun h => hv h.2)]
            · change 0 = Shao.C2.HalfLinePhysicalGaussian.upperCompletion
                (actualWall a x) 0 (Shao.energy a) ((-1) * Shao.prefixSum a n)
              have hv : ¬ 0 < actualWall a x + Shao.prefixSum a n := by
                change ¬ -actualWall a x < Shao.prefixSum a n at hz
                intro hv
                apply hz
                linarith only [hv]
              simp only [Shao.C2.HalfLinePhysicalGaussian.upperCompletion,
                Shao.C2.HalfLineGaussianStep.completion, neg_one_mul, sub_zero, sub_neg_eq_add,
                if_neg (show ¬ (0 < actualWall a x ∧
                  0 < actualWall a x + Shao.prefixSum a n) from fun h => hv h.2)]
        · have hdead : ¬ sourceAlive J a x 0 sigma := fun hlive => ha hlive.1
          rw [if_neg hdead, if_neg ha]
      have hVperm (a : Shao.Path n) (sigma : LabelPerm n) : V (Spitzer.reorder a sigma) = V a := by
        rw [hScalar.2.1 (Spitzer.reorder a sigma), hScalar.2.1 a, hq, hs]
      have hAlive (a : Shao.Path n) (sigma : LabelPerm n) :
          sourceAlive J a x n sigma ↔
            Shao.maxWithZero (s • Spitzer.reorder a sigma) < actualWall a x := by
        have hs0 := hs a sigma
        constructor
        · intro ha
          unfold Shao.maxWithZero
          rw [Finset.sup'_lt_iff]
          intro k hk
          rw [Shao.prefixSum_smul]
          have hp := ha.2.2 k (Finset.mem_Icc.1 hk).2
          rcases hJs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simpa only [one_mul, Interior] using hp
          · change -actualWall a x < Shao.prefixSum (Spitzer.reorder a sigma) k at hp
            simp only [neg_one_mul]
            linarith only [hp]
        · intro ha
          have hpre : ∀ k : ℕ, k ≤ n →
              s * Shao.prefixSum (Spitzer.reorder a sigma) k < actualWall a x := by
            unfold Shao.maxWithZero at ha
            rw [Finset.sup'_lt_iff] at ha
            intro k hk
            simpa only [Shao.prefixSum_smul] using ha k (Finset.mem_Icc.2 ⟨Nat.zero_le k, hk⟩)
          have hw : 0 < actualWall a x := by
            simpa only [Shao.prefixSum_zero, mul_zero] using hpre 0 (Nat.zero_le n)
          have hqpos : 0 < Shao.energy a := by
            by_contra hneg
            have he : Shao.energy a = 0 := le_antisymm (le_of_not_gt hneg) (Shao.energy_nonneg a)
            simpa only [actualWall, he, Real.sqrt_zero, mul_zero, lt_self_iff_false] using hw
          refine ⟨hqpos, ?_, ?_⟩
          · have hz := hpre n le_rfl
            rw [hs0] at hz
            rcases hJs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · simpa only [one_mul, Interior] using hz
            · change -actualWall a x < Shao.prefixSum a n
              simp only [neg_one_mul] at hz
              linarith only [hz]
          · intro k hk
            have hp := hpre k hk
            rcases hJs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · simpa only [one_mul, Interior] using hp
            · change -actualWall a x < Shao.prefixSum (Spitzer.reorder a sigma) k
              simp only [neg_one_mul] at hp
              linarith only [hp]
      have hAEq (p : Shao.Path n × LabelPerm n) : Afinal J p = A (randomReorder p) := by
        simp only [Afinal, A, Set.indicator, E, Set.mem_setOf_eq, randomReorder, hq, hAlive, actualWall]
      have hVEq (p : Shao.Path n × LabelPerm n) : Vinitial J p = V (randomReorder p) := by
        exact (hV p.1 p.2).trans (hVperm p.1 p.2).symm
      have hsm : Measurable (fun a : Shao.Path n => s • a) :=
        Measurable.of_eval fun i => measurable_const.mul (measurable_pi_apply i)
      have hEm : MeasurableSet E := measurableSet_lt
        (Shao.measurable_maxWithZero.comp hsm) (Shao.measurable_energyWall x)
      have hAm : Measurable A := measurable_const.indicator hEm
      have hAlaw := hPath.comp hAm
      have hVm : AEMeasurable V (Measure.map (randomReorder (n := n)) (revealLaw P)) := by
        rw [hMap]
        exact hScalar.1.aestronglyMeasurable.aemeasurable
      have hVlaw := hPath.comp_of_aemeasurable hVm
      have hAI : (∫ p, Afinal J p ∂revealLaw P) = P.real E := by
        calc
          _ = ∫ p, A (randomReorder p) ∂revealLaw P := integral_congr_ae (ae_of_all _ hAEq)
          _ = ∫ a, A a ∂P := hAlaw.integral_eq
          _ = P.real E := integral_indicator_one hEm
      have hVI : (∫ p, Vinitial J p ∂revealLaw P) = ∫ a, V a ∂P := by
        calc
          _ = ∫ p, V (randomReorder p) ∂revealLaw P := integral_congr_ae (ae_of_all _ hVEq)
          _ = _ := hVlaw.integral_eq
      rw [hAI, hVI]
      exact hScalar.2.2
    exact max_le (hGap .upper 1 (Or.inl ⟨rfl, rfl⟩))
      (hGap .lower (-1) (Or.inr ⟨rfl, rfl⟩))
  have hCGR : 0 ≤ CG * R := mul_nonneg hCG.le hR.le
  refine ⟨?_, hAsm.2.1, ?_, ?_⟩
  · intro J hJ
    refine ⟨(hAsm.1 J hJ).1, (hAsm.1 J hJ).2.1, ?_⟩
    have ht := (hAsm.1 J hJ).2.2
    change (∫ p, ∑ r ∈ Finset.range n, O J p r ∂revealLaw P) ≤ CA * R + Gamma at ht
    nlinarith only [ht, hGamma, hCGR]
  · have ht := hAsm.2.2.1
    nlinarith only [ht, hGamma]
  · intro m hmm hmb hInvariant
    have ht := hAsm.2.2.2 m hmm hmb hInvariant
    refine ⟨ht.1, ?_⟩
    nlinarith only [ht.2, hGamma]

end Shao.Probability.SourceActualGaussianTransfer
