/- Mathematical candidate: actual Brownian B/E assembly with literal unpaid initial gap.
   No new generic transfer, terminal producer, or target E/G budget premise. -/
import Shao.Probability.SourceActualLocalProfileBudget
import Shao.Probability.SourceActualIntervalProfileBudget
import Shao.Probability.SourceTerminalEnvelope

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.Probability.SourceActualTransferAssembly
open MeasureTheory ProbabilityTheory
open SourcePermutationReveal SourceSeparatedOvershoot SourceActualLocalProfileBudget
open SourceActualIntervalProfileBudget
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open scoped BigOperators Classical NNReal

local instance labelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

private theorem actual_terminal_reveal_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ΩB : Type*} [MeasurableSpace ΩB]
        (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : ℝ≥0 → ΩB → ℝ), IsBrownianReal B PB →
        ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho] (n : ℕ), 0 < n →
          Integrable (fun z : ℝ => z ^ 2) rho →
          (∫ z : ℝ, z ∂rho) = 0 → 0 < (∫ z : ℝ, z ^ 2 ∂rho) →
          let Q : Measure BridgeNoise := bridgeLaw B PB
          let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
          let scale : ℝ := Real.sqrt ((n : ℝ) * sigmaSq)
          let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / scale) rho
          let R : ℝ := Shao.truncationBudget normalizedLaw n 0
          let h : ℝ := 4 * (n : ℝ) * sigmaSq * R ^ 2
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
          let nu : Shao.Path n → LabelPerm n → ℕ := fun a sigma => energyCutoff a h sigma
          ∀ (x : ℝ), 0 ≤ x → x ≤ 1 → ∀ J : MonitoredDomain,
            let F : BridgeKernel := eventCompletionKernel J Q
            let D : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
              |sourceValue J F p.1 x (nu p.1 p.2) p.2 -
                (if sourceAlive J p.1 x n p.2 then 1 else 0)|
            Integrable D (revealLaw P) ∧ (∫ p, D p ∂revealLaw P) ≤ C * R ^ 2 := by
  classical
  obtain ⟨C, hC, hTerminal⟩ := actual_terminal_at_energy_cutoff
  refine ⟨C, hC, ?_⟩
  intro ΩB hΩB PB hPB B hB rho hrho n hn h2 hmean hsecond
    Q sigmaSq scale normalizedLaw R h P nu x hx0 hx1 J F D
  letI : IsProbabilityMeasure PB := hPB
  letI : IsProbabilityMeasure rho := hrho
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw B PB hB
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  let D0 : Shao.Path n → ℝ := fun a =>
    |sourceValue J F a x (energyCutoff a h (Equiv.refl (Fin n))) (Equiv.refl (Fin n)) -
      (if sourceAlive J a x n (Equiv.refl (Fin n)) then 1 else 0)|
  have hBudget := hTerminal PB B hB rho n hn h2 hmean hsecond x hx0 hx1 J
  have hD0i : Integrable D0 P := hBudget.1
  have hD0b : (∫ a, D0 a ∂P) ≤ C * R ^ 2 := hBudget.2
  have hh : 0 < h :=
    (raw_truncation_budget_suffix_geometry rho n hn h2 hsecond).2.2.2.1
  have hq (a : Shao.Path n) (sigma : LabelPerm n) :
      Shao.energy (Spitzer.reorder a sigma) = Shao.energy a := by
    simpa only [Shao.energy, Spitzer.reorder] using Equiv.sum_comp sigma (fun i => (a i)^2)
  have hs (a : Shao.Path n) (sigma : LabelPerm n) :
      Shao.prefixSum (Spitzer.reorder a sigma) n = Shao.prefixSum a n := by
    simpa only [Shao.prefixSum_length, Spitzer.reorder] using Equiv.sum_comp sigma a
  have hRem (a : Shao.Path n) (sigma : LabelPerm n) (k : ℕ) :
      remainingEnergy (Spitzer.reorder a sigma) k (Equiv.refl (Fin n)) = remainingEnergy a k sigma := by
    unfold remainingEnergy
    rw [hq]
    rfl
  have hWall (a : Shao.Path n) (sigma : LabelPerm n) :
      actualWall (Spitzer.reorder a sigma) x = actualWall a x := by
    unfold actualWall
    rw [hq]
  have hId (a : Shao.Path n) : Spitzer.reorder a (Equiv.refl (Fin n)) = a := rfl
  have hAlive (a : Shao.Path n) (sigma : LabelPerm n) (k : ℕ) :
      sourceAlive J (Spitzer.reorder a sigma) x k (Equiv.refl (Fin n)) ↔
        sourceAlive J a x k sigma := by
    simp only [sourceAlive, hq, hs, hWall, hId]
  have hValue (a : Shao.Path n) (sigma : LabelPerm n) (k : ℕ) :
      sourceValue J F (Spitzer.reorder a sigma) x k (Equiv.refl (Fin n)) =
        sourceValue J F a x k sigma := by
    simp only [sourceValue, hAlive, hWall, hs, hRem, hId]
  have hCut (a : Shao.Path n) (sigma : LabelPerm n) :
      energyCutoff (Spitzer.reorder a sigma) h (Equiv.refl (Fin n)) = energyCutoff a h sigma := by
    have hA := energy_cutoff_data a h hh
    have hS := energy_cutoff_data (Spitzer.reorder a sigma) h hh
    apply Nat.le_antisymm
    · apply (hS.2.1 (Equiv.refl (Fin n)) _ (hA.1.1 sigma)).mpr
      rw [hRem]
      exact (hA.2.1 sigma _ (hA.1.1 sigma)).mp le_rfl
    · apply (hA.2.1 sigma _ (hS.1.1 (Equiv.refl (Fin n)))).mpr
      rw [← hRem a sigma]
      exact (hS.2.1 (Equiv.refl (Fin n)) _ (hS.1.1 (Equiv.refl (Fin n)))).mp le_rfl
  have hD (p : Shao.Path n × LabelPerm n) : D p = D0 (randomReorder p) := by
    dsimp only [D, D0, randomReorder, nu]
    rw [hCut, hValue, hAlive]
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
  have hAE : AEMeasurable D0 (Measure.map (randomReorder (n := n)) (revealLaw P)) := by
    rw [hMap]
    exact hD0i.aestronglyMeasurable.aemeasurable
  have hDlaw := hPath.comp_of_aemeasurable hAE
  have hEq : D = D0 ∘ randomReorder := funext hD
  refine ⟨hEq ▸ hDlaw.integrable_iff.mpr hD0i, ?_⟩
  calc
    _ = ∫ a, D0 a ∂P := by
      rw [hEq]
      exact hDlaw.integral_eq
    _ ≤ _ := hD0b


theorem actual_brownian_transfer_with_initial_gap :
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
            let initialGap : ℝ := max
              |(∫ p, Afinal .upper p ∂revealLaw P) - (∫ p, Vinitial .upper p ∂revealLaw P)|
              |(∫ p, Afinal .lower p ∂revealLaw P) - (∫ p, Vinitial .lower p ∂revealLaw P)|
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
              (∫ p, ∑ r ∈ Finset.range n, O J p r ∂revealLaw P) ≤ C * R + initialGap) ∧
            Integrable rawAbsolute (revealLaw P) ∧
            (∫ p, rawAbsolute p ∂revealLaw P) ≤ C * R + 2 * initialGap ∧
            (∀ (m : Shao.Path n → ℝ), Measurable m → (∀ a, |m a| ≤ 1) →
              PermutationInvariant m →
              Integrable (fun p => m p.1 * (Afinal .interval p - Vinitial .interval p)) (revealLaw P) ∧
              |(∫ p, m p.1 * (Afinal .interval p - Vinitial .interval p) ∂revealLaw P)| ≤
                C * R + 2 * initialGap) := by
  classical
  intro Csmall hCs
  obtain ⟨CH, hCH, hHalfline⟩ := iid_actual_cutoff_two_halfline_budget
  obtain ⟨CI, hCI, hInterval⟩ := iid_actual_interval_retained_negative_budget Csmall hCs
  obtain ⟨CT, hCT, hTerminal⟩ := actual_terminal_reveal_budget
  let CB : ℝ := CH + CI
  have hCB : 0 < CB := add_pos hCH hCI
  refine ⟨3 * CB + 3 * CT, by positivity, ?_⟩
  intro ΩB hΩB PB hPB B hB Q hReflection hRegular hSmall rho hrho n hn h2 hmean hsecond
    sigmaSq scale normalizedLaw R h P nu x hx0 hx1 F FY Vinitial Afinal initialGap O rawAbsolute
  letI : IsProbabilityMeasure PB := hPB
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw B PB hB
  letI : IsProbabilityMeasure rho := hrho
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hGeom := raw_truncation_budget_suffix_geometry rho n hn h2 hsecond
  have hR : 0 < R := hGeom.1
  have hR1 : R ≤ 1 := hGeom.2.1
  have hh : 0 < h := hGeom.2.2.2.1
  by_cases hxzero : x = 0
  · have hdead (J : MonitoredDomain) (a : Shao.Path n) (r : ℕ) (sigma : LabelPerm n) :
        ¬ sourceAlive J a x r sigma := by
      intro ha
      have hz := ha.2.2 0 (Nat.zero_le r)
      cases J <;> simpa [Interior, actualWall, hxzero, Shao.prefixSum_zero] using hz
    have hV (J : MonitoredDomain) (p : Shao.Path n × LabelPerm n) : Vinitial J p = 0 := by
      simp only [Vinitial, sourceValue, if_neg (hdead J p.1 0 p.2)]
    have hA (J : MonitoredDomain) (p : Shao.Path n × LabelPerm n) : Afinal J p = 0 := by
      simp only [Afinal, if_neg (hdead J p.1 n p.2)]
    have hO (J : MonitoredDomain) (p : Shao.Path n × LabelPerm n) (r : ℕ) : O J p r = 0 := by
      dsimp only [O]
      unfold sourceSeparatedOvershoot
      split_ifs <;> simp_all only [and_false, false_and, if_false]
    have hRem (p : Shao.Path n × LabelPerm n) (r : ℕ) :
        sourceRemainder .interval (F .interval) (FY .interval) p.1 x r p.2 = 0 := by
      unfold sourceRemainder
      split_ifs <;> simp_all only [and_false, false_and, if_false]
    simp only [hO, hA, hV, rawAbsolute, hRem, ite_self, abs_zero,
      Finset.sum_const_zero, integral_zero, initialGap, sub_self, max_self,
      mul_zero, zero_mul, sub_zero, add_zero]
    refine ⟨fun _ _ => ⟨integrable_zero _ _ _, le_rfl, by positivity⟩,
      integrable_zero _ _ _, by positivity, ?_⟩
    intro m hmm hmb hInvariant
    exact ⟨integrable_zero _ _ _, by positivity⟩
  have hx : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxzero)
  have hFd (J : MonitoredDomain) := eventCompletionKernel_data J Q
  have hData (J : MonitoredDomain) :
      Measurable (FY J) ∧ KernelBounds J (F J) (FY J) 4 ∧
      (∀ w y T z : ℝ, 0 < w → 0 < T → Interior J w y → Interior J w z →
        HasDerivAt (fun s : ℝ => eventCompletionKernel J Q (w, s, T, z))
          (FY J (w, y, T, z)) y) := by
    cases J with
    | upper => exact actual_halfline_kernel_data Q hReflection .upper (Or.inl rfl)
    | lower => exact actual_halfline_kernel_data Q hReflection .lower (Or.inr rfl)
    | interval =>
      have hi := actual_interval_kernel_data Q hReflection hRegular
      refine ⟨hi.1, hi.2.1, ?_⟩
      intro w y T z hw hT hy hz
      exact hi.2.2 w y T z hw hT (abs_lt.mpr hy) (abs_lt.mpr hz)
  have hnum (sigma : LabelPerm n) : Measurable (fun a : Shao.Path n => nu a sigma) :=
    actual_energy_cutoff_measurable h hh sigma
  have hnu (a : Shao.Path n) : IsRevealStoppingRank (nu a) := (energy_cutoff_data a h hh).1
  have hcap (a : Shao.Path n) (sigma : LabelPerm n) : nu a sigma ≤ energyCutoff a h sigma := le_rfl
  let L : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℕ → ℝ :=
    fun J p r => sourceRetainedRemainder J (F J) (FY J) p.1 x (nu p.1) r p.2
  have hParts (J : MonitoredDomain) := source_parts_measurable_integrable J (F J) (FY J)
    (hFd J).1 (hData J).1 4 (hData J).2.1 P x hx nu hnum
  have hLi (J : MonitoredDomain) (r : ℕ) :
      Integrable (fun p => L J p r) (revealLaw P) := ((hParts J).2.1 r).1
  have hOi (J : MonitoredDomain) (r : ℕ) :
      Integrable (fun p => O J p r) (revealLaw P) := ((hParts J).2.1 r).2
  let LA (J : MonitoredDomain) (p : Shao.Path n × LabelPerm n) : ℝ :=
    ∑ r ∈ Finset.range n, |L J p r|
  let NN (p : Shao.Path n × LabelPerm n) : ℝ :=
    ∑ r ∈ Finset.range n, max (-O .interval p r) 0
  have hLAi (J : MonitoredDomain) : Integrable (LA J) (revealLaw P) :=
    integrable_finsetSum _ (fun r _ => (hLi J r).abs)
  have hNNi : Integrable NN (revealLaw P) := by
    apply integrable_finsetSum
    intro r _
    have hi := ((hOi .interval r).abs.sub (hOi .interval r)).const_mul (1 / 2 : ℝ)
    apply hi.congr
    apply ae_of_all
    intro p
    change (1 / 2 : ℝ) * (|O .interval p r| - O .interval p r) = max (-O .interval p r) 0
    by_cases hp : 0 ≤ O .interval p r
    · rw [abs_of_nonneg hp, max_eq_right (neg_nonpos.mpr hp)]
      ring
    · have hp' : O .interval p r ≤ 0 := (lt_of_not_ge hp).le
      rw [abs_of_nonpos hp', max_eq_left (neg_nonneg.mpr hp')]
      ring
  have hHB := hHalfline Q hReflection rho n hn h2 hmean hsecond x hx hx1
  have hIB := hInterval Q hReflection hRegular hSmall rho n hn h2 hmean hsecond x hx0 hx1
  have hHB' : (∫ p, LA .upper p ∂revealLaw P) +
      (∫ p, LA .lower p ∂revealLaw P) ≤ CH * R := hHB.2
  have hIB' : (∫ p, LA .interval p ∂revealLaw P) +
      (∫ p, NN p ∂revealLaw P) ≤ CI * R := by
    have he : (fun p : Shao.Path n × LabelPerm n =>
        ∑ r ∈ Finset.range n, (|L .interval p r| + max (-O .interval p r) 0)) =
        (fun p => LA .interval p + NN p) := by
      funext p
      exact Finset.sum_add_distrib
    have hi : (∫ p, ∑ r ∈ Finset.range n,
        (|L .interval p r| + max (-O .interval p r) 0) ∂revealLaw P) ≤ CI * R := hIB.2.2.2.2
    rw [he, integral_add (hLAi .interval) hNNi] at hi
    exact hi
  have hBudget : (∫ p, LA .upper p ∂revealLaw P) +
      (∫ p, LA .lower p ∂revealLaw P) +
      (∫ p, LA .interval p ∂revealLaw P) + (∫ p, NN p ∂revealLaw P) ≤ CB * R := by
    dsimp only [CB]
    nlinarith only [hHB', hIB']
  have hE (J : MonitoredDomain) :
      Integrable (fun p : Shao.Path n × LabelPerm n =>
        |sourceValue J (F J) p.1 x (nu p.1 p.2) p.2 - Afinal J p|) (revealLaw P) ∧
      (∫ p, |sourceValue J (F J) p.1 x (nu p.1 p.2) p.2 - Afinal J p| ∂revealLaw P) ≤
        CT * R ^ 2 := hTerminal PB B hB rho n hn h2 hmean hsecond x hx0 hx1 J
  have hGap (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower) :
      |(∫ p, Afinal J p ∂revealLaw P) - (∫ p, Vinitial J p ∂revealLaw P)| ≤ initialGap := by
    rcases hJ with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hTransfer := source_three_domain_overshoot_transfer P Q FY
    (fun J => (hData J).1) 4 (by norm_num)
    (fun J => (hData J).2.1.derivative_bound) (fun J => (hData J).2.2)
    x hx h hh nu hnum hnu hcap (CB * R) (CT * R ^ 2) initialGap hBudget
    (fun J => (hE J).2) hGap
  have hR2 : R ^ 2 ≤ R := by nlinarith only [mul_nonneg hR.le (sub_nonneg.mpr hR1)]
  have hCT2 : CT * R ^ 2 ≤ CT * R := mul_le_mul_of_nonneg_left hR2 hCT.le
  have hCBR : 0 ≤ CB * R := mul_nonneg hCB.le hR.le
  have hCTR : 0 ≤ CT * R := mul_nonneg hCT.le hR.le
  have hRawi : Integrable rawAbsolute (revealLaw P) := by
    apply integrable_finsetSum
    intro r _
    apply ((hLi .interval r).add (hOi .interval r)).abs.congr
    apply ae_of_all
    intro p
    exact congrArg abs (source_selected_remainder_decomposition .interval
      (F .interval) (FY .interval) p.1 x hx (nu p.1) r p.2).symm
  refine ⟨?_, hRawi, ?_, ?_⟩
  · intro J hJ
    refine ⟨integrable_finsetSum _ (fun r _ => hOi J r), (hTransfer.1 J hJ).1, ?_⟩
    have ht := (hTransfer.1 J hJ).2
    nlinarith only [ht, hCT2, hCBR, hCTR]
  · have ht := hTransfer.2.1
    nlinarith only [ht, hCT2, hCTR]
  · intro m hmm hmb hInvariant
    have hMV := source_stopped_integrability .interval (F .interval) (FY .interval)
      (hFd .interval).1 (hData .interval).1 4 (hData .interval).2.1 P x hx
      (fun _ _ => n) (fun _ => measurable_const) (fun _ _ => le_rfl) m hmm hmb
    have hAeq (p : Shao.Path n × LabelPerm n) :
        sourceValue .interval (F .interval) p.1 x n p.2 = Afinal .interval p := by
      have hs : Shao.prefixSum (Spitzer.reorder p.1 p.2) n = Shao.prefixSum p.1 n := by
        simpa only [Shao.prefixSum_length, Spitzer.reorder] using Equiv.sum_comp p.2 p.1
      have he : Shao.energy (Spitzer.reorder p.1 p.2) = Shao.energy p.1 := by
        simpa only [Shao.energy, Spitzer.reorder] using
          Equiv.sum_comp p.2 (fun i => (p.1 i) ^ 2)
      have ht : remainingEnergy p.1 n p.2 = 0 := by
        rw [remainingEnergy, Shao.prefixSquares_length, he, sub_self]
      by_cases hlive : sourceAlive .interval p.1 x n p.2
      · have hw : 0 < actualWall p.1 x := mul_pos hx (Real.sqrt_pos.2 hlive.1)
        simp only [sourceValue, Afinal, hlive, ite_true]
        rw [hs, ht]
        rw [completionExt, if_pos ⟨hw, hlive.2.1, hlive.2.1⟩]
        norm_num
      · simp only [sourceValue, Afinal, hlive, ite_false]
    have hMA : Integrable (fun p : Shao.Path n × LabelPerm n => m p.1 * Afinal .interval p)
        (revealLaw P) := hMV.1.congr (ae_of_all _ (fun p => congrArg (m p.1 * ·) (hAeq p)))
    have hInt : Integrable (fun p : Shao.Path n × LabelPerm n =>
        m p.1 * (Afinal .interval p - Vinitial .interval p)) (revealLaw P) := by
      apply (hMA.sub hMV.2.1).congr
      exact ae_of_all _ (fun p => by
        change m p.1 * Afinal .interval p -
          m p.1 * sourceValue .interval (F .interval) p.1 x 0 p.2 =
          m p.1 * (Afinal .interval p - sourceValue .interval (F .interval) p.1 x 0 p.2)
        ring)
    refine ⟨hInt, ?_⟩
    have ht := hTransfer.2.2 m hmm hmb hInvariant
    nlinarith only [ht, hCT2]

end Shao.Probability.SourceActualTransferAssembly
