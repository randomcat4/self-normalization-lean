/- Mathematical candidate only: one actual original-iid family consumer.
   No Lean checks, no production source, no new generic map producer. -/
import Shao.Probability.SourceActualLocalProfileBudget
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.Probability.SourceOriginalIIDHalflineBudget
open MeasureTheory ProbabilityTheory
open SourcePermutationReveal SourceSeparatedOvershoot SourceActualLocalProfileBudget
open Shao.C2.BridgeDomination
open scoped BigOperators Classical

local instance labelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

theorem original_iid_actual_cutoff_two_halfline_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        (mu : Measure Ω) (rho : Measure ℝ)
        [IsProbabilityMeasure mu] [IsProbabilityMeasure rho]
        (Q : Measure BridgeNoise) [IsProbabilityMeasure Q],
        HalflineReflectionIdentities Q →
        ∀ (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ),
          (∀ i, AEMeasurable (X i) mu) →
          iIndepFun X mu →
          (∀ i, IdentDistrib (X i) (id : ℝ → ℝ) mu rho) →
          Integrable (fun z : ℝ => z ^ 2) rho →
          (∫ z : ℝ, z ∂rho) = 0 → 0 < (∫ z : ℝ, z ^ 2 ∂rho) →
          let population : Ω → Shao.Path n := samplePath X
          let rawEnergy : Ω → ℝ := fun omega => ∑ i : Fin n, (X i omega) ^ 2
          let rawTerminal : Ω → ℝ := fun omega => ∑ i : Fin n, X i omega
          let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
          let scale : ℝ := Real.sqrt ((n : ℝ) * sigmaSq)
          let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / scale) rho
          let R : ℝ := Shao.truncationBudget normalizedLaw n 0
          let h : ℝ := 4 * (n : ℝ) * sigmaSq * R ^ 2
          let nu : Ω → LabelPerm n → ℕ := fun omega sigma =>
            energyCutoff (population omega) h sigma
          let jointLaw : Measure (Ω × LabelPerm n) :=
            mu.prod (uniformPermutationLaw n)
          ∀ (x : ℝ), 0 ≤ x → x ≤ 1 →
            let L : MonitoredDomain → (Ω × LabelPerm n) → ℕ → ℝ := fun J p r =>
              sourceRetainedRemainder J (eventCompletionKernel J Q) (halflineDerivative J)
                (population p.1) x (nu p.1) r p.2
            (∀ omega : Ω,
              Shao.energy (population omega) = rawEnergy omega ∧
              Shao.prefixSum (population omega) n = rawTerminal omega) ∧
            (∀ sigma : LabelPerm n, AEMeasurable (fun omega => nu omega sigma) mu) ∧
            (∀ J : MonitoredDomain, J = .upper ∨ J = .lower →
              (∀ r : ℕ, Integrable (fun p => L J p r) jointLaw) ∧
              Integrable (fun p => ∑ r ∈ Finset.range n, |L J p r|) jointLaw) ∧
            ((∫ p, ∑ r ∈ Finset.range n, |L .upper p r| ∂jointLaw) +
              (∫ p, ∑ r ∈ Finset.range n, |L .lower p r| ∂jointLaw)) ≤ C * R
 := by
  classical
  obtain ⟨C, hC, hCanonical⟩ := iid_actual_cutoff_two_halfline_budget
  refine ⟨C, hC, ?_⟩
  intro Ω hΩ mu rho hmu hrho Q hQ hReflection n hn X hX hIndep hLaw h2 hmean hsecond
    population rawEnergy rawTerminal sigmaSq scale normalizedLaw R h nu jointLaw x hx hx1 L
  letI : IsProbabilityMeasure mu := hmu
  letI : IsProbabilityMeasure rho := hrho
  letI : IsProbabilityMeasure Q := hQ
  have hGeometry := Shao.Probability.raw_truncation_budget_suffix_geometry rho n hn h2 hsecond
  have hh : 0 < h := hGeometry.2.2.2.1
  have hR : 0 ≤ R := hGeometry.1.le
  have hPopulation : AEMeasurable population mu := AEMeasurable.of_eval hX
  have hState (omega : Ω) :
      Shao.energy (population omega) = rawEnergy omega ∧
      Shao.prefixSum (population omega) n = rawTerminal omega := by
    constructor
    · rfl
    · rw [Shao.prefixSum_length]
      rfl
  have hNu (sigma : LabelPerm n) : AEMeasurable (fun omega => nu omega sigma) mu :=
    (actual_energy_cutoff_measurable h hh sigma).comp_aemeasurable hPopulation
  refine ⟨hState, hNu, ?_⟩
  by_cases hx0 : x = 0
  · subst x
    have hZero (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower)
        (p : Ω × LabelPerm n) (r : ℕ) : L J p r = 0 := by
      have hDead : ¬ sourceAlive J (population p.1) 0 r p.2 := by
        intro ha
        have h0 := ha.2.2 0 (Nat.zero_le r)
        rcases hJ with rfl | rfl <;> simpa [Interior, actualWall] using h0
      change sourceRetainedRemainder J (eventCompletionKernel J Q) (halflineDerivative J)
        (population p.1) 0 (nu p.1) r p.2 = 0
      by_cases hr : r < n
      · rw [sourceRetainedRemainder, dif_pos hr, if_neg (by tauto)]
      · rw [sourceRetainedRemainder, dif_neg hr]
    refine ⟨?_, ?_⟩
    · intro J hJ
      constructor
      · intro r
        simpa only [hZero J hJ] using
          (integrable_const (0 : ℝ) : Integrable (fun _ : Ω × LabelPerm n => (0 : ℝ)) jointLaw)
      · simpa only [hZero J hJ, abs_zero, Finset.sum_const_zero] using
          (integrable_const (0 : ℝ) : Integrable (fun _ : Ω × LabelPerm n => (0 : ℝ)) jointLaw)
    · simp only [hZero .upper (Or.inl rfl), hZero .lower (Or.inr rfl), abs_zero,
        Finset.sum_const_zero, integral_zero, zero_add]
      exact mul_nonneg hC.le hR
  · have hxPos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
    let lambda : Measure (LabelPerm n) := uniformPermutationLaw n
    let Phi : (Ω × LabelPerm n) → (Shao.Path n × LabelPerm n) :=
      fun p => (population p.1, p.2)
    let kappa : Shao.Path n → LabelPerm n → ℕ := fun a sigma => energyCutoff a h sigma
    let L0 : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℕ → ℝ := fun J p r =>
      sourceRetainedRemainder J (eventCompletionKernel J Q) (halflineDerivative J)
        p.1 x (kappa p.1) r p.2
    let S0 : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ := fun J p =>
      ∑ r ∈ Finset.range n, |L0 J p r|
    letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
    have hMap : Measure.map population mu = P := by
      change Measure.map (fun omega i => X i omega) mu = _
      rw [hIndep.map_fun_eq_pi_map hX]
      congr 1
      funext i
      simpa only [Measure.map_id] using (hLaw i).map_eq
    have hPhi : AEMeasurable Phi jointLaw :=
      hPopulation.prodMap measurable_id.aemeasurable
    have hPairedMap : Measure.map Phi jointLaw = revealLaw P := by
      have he := Measure.map_prod_map_of_aemeasurable mu lambda
        hPopulation measurable_id.aemeasurable
      rw [hMap, Measure.map_id] at he
      exact he.symm
    have hPair : IdentDistrib Phi (id : (Shao.Path n × LabelPerm n) →
        (Shao.Path n × LabelPerm n)) jointLaw (revealLaw P) :=
      ⟨hPhi, measurable_id.aemeasurable, by simpa only [Measure.map_id] using hPairedMap⟩
    have hKappa (sigma : LabelPerm n) : Measurable (fun a => kappa a sigma) :=
      actual_energy_cutoff_measurable h hh sigma
    have hParts (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower) :=
      source_parts_measurable_integrable J (eventCompletionKernel J Q) (halflineDerivative J)
        (eventCompletionKernel_data J Q).1 (actual_halfline_kernel_data Q hReflection J hJ).1
        4 (actual_halfline_kernel_data Q hReflection J hJ).2.1 P x hxPos kappa hKappa
    have hL0m (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower) (r : ℕ) :
        Measurable (fun p => L0 J p r) := by
      apply measurable_from_prod_countable_left
      intro sigma
      exact ((hParts J hJ).1 sigma r).1
    have hS0m (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower) :
        Measurable (S0 J) :=
      Finset.measurable_sum _ (fun r _ => continuous_abs.measurable.comp (hL0m J hJ r))
    have hBudget := hCanonical Q hReflection rho n hn h2 hmean hsecond x hxPos hx1
    have hInt (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower) :
        (∫ p, ∑ r ∈ Finset.range n, |L J p r| ∂jointLaw) =
          ∫ p, S0 J p ∂revealLaw P :=
      (hPair.comp (hS0m J hJ)).integral_eq
    refine ⟨?_, ?_⟩
    · intro J hJ
      refine ⟨fun r => (hPair.comp (hL0m J hJ r)).integrable_iff.mpr
        (((hParts J hJ).2.1 r).1), ?_⟩
      exact (hPair.comp (hS0m J hJ)).integrable_iff.mpr (hBudget.1 J hJ)
    · calc
        _ = (∫ p, S0 .upper p ∂revealLaw P) +
            (∫ p, S0 .lower p ∂revealLaw P) :=
          congrArg₂ (fun u v : ℝ => u + v) (hInt .upper (Or.inl rfl)) (hInt .lower (Or.inr rfl))
        _ ≤ _ := hBudget.2

end Shao.Probability.SourceOriginalIIDHalflineBudget
