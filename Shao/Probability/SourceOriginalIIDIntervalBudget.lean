/- Next source-bound mathematical candidate only. No production authority or Lean checks.
   The canonical producer PR302 still requires fresh independent qualification. -/
import Shao.Probability.SourceActualIntervalProfileBudget
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.Probability.SourceOriginalIIDIntervalBudget
open MeasureTheory ProbabilityTheory
open SourcePermutationReveal SourceSeparatedOvershoot SourceActualLocalProfileBudget
open SourceActualIntervalProfileBudget
open Shao.C2.BridgeDomination
open scoped BigOperators Classical

local instance labelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

theorem original_iid_actual_interval_retained_negative_budget :
    ∀ Csmall : ℝ, 0 ≤ Csmall → ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        (mu : Measure Ω) (rho : Measure ℝ)
        [IsProbabilityMeasure mu] [IsProbabilityMeasure rho]
        (Q : Measure BridgeNoise) [IsProbabilityMeasure Q],
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
            let L : (Ω × LabelPerm n) → ℕ → ℝ := fun p r =>
              sourceRetainedRemainder .interval (eventCompletionKernel .interval Q)
                (intervalDerivative Q) (population p.1) x (nu p.1) r p.2
            let O : (Ω × LabelPerm n) → ℕ → ℝ := fun p r =>
              sourceSeparatedOvershoot .interval (intervalDerivative Q)
                (population p.1) x (nu p.1) r p.2
            (∀ omega : Ω,
              Shao.energy (population omega) = rawEnergy omega ∧
              Shao.prefixSum (population omega) n = rawTerminal omega) ∧
            (∀ sigma : LabelPerm n, AEMeasurable (fun omega => nu omega sigma) mu) ∧
            (∀ r : ℕ,
              AEMeasurable (fun p => L p r) jointLaw ∧
              AEMeasurable (fun p => O p r) jointLaw) ∧
            (∀ r : ℕ, Integrable (fun p => L p r) jointLaw ∧
              Integrable (fun p => O p r) jointLaw) ∧
            Integrable (fun p => ∑ r ∈ Finset.range n, (|L p r| + max (-O p r) 0)) jointLaw ∧
            (∫ p, ∑ r ∈ Finset.range n, (|L p r| + max (-O p r) 0) ∂jointLaw) ≤ C * R := by
  classical
  intro Csmall hCs
  obtain ⟨C, hC, hCanonical⟩ := iid_actual_interval_retained_negative_budget Csmall hCs
  refine ⟨C, hC, ?_⟩
  intro Ω hΩ mu rho hmu hrho Q hQ hReflection hRegular hSmall n hn X hX hIndep hLaw h2 hmean hsecond
    population rawEnergy rawTerminal sigmaSq scale normalizedLaw R h nu jointLaw x hx0 hx1 L O
  letI : IsProbabilityMeasure mu := hmu
  letI : IsProbabilityMeasure rho := hrho
  letI : IsProbabilityMeasure Q := hQ
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
  let lambda : Measure (LabelPerm n) := uniformPermutationLaw n
  let Phi : (Ω × LabelPerm n) → (Shao.Path n × LabelPerm n) := fun p => (population p.1, p.2)
  let kappa : Shao.Path n → LabelPerm n → ℕ := fun a sigma => energyCutoff a h sigma
  let L0 : (Shao.Path n × LabelPerm n) → ℕ → ℝ := fun p r =>
    sourceRetainedRemainder .interval (eventCompletionKernel .interval Q)
      (intervalDerivative Q) p.1 x (kappa p.1) r p.2
  let O0 : (Shao.Path n × LabelPerm n) → ℕ → ℝ := fun p r =>
    sourceSeparatedOvershoot .interval (intervalDerivative Q) p.1 x (kappa p.1) r p.2
  let S0 : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
    ∑ r ∈ Finset.range n, (|L0 p r| + max (-O0 p r) 0)
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hPopulation : AEMeasurable population mu := AEMeasurable.of_eval hX
  have hState (omega : Ω) :
      Shao.energy (population omega) = rawEnergy omega ∧
      Shao.prefixSum (population omega) n = rawTerminal omega := by
    constructor
    · rfl
    · rw [Shao.prefixSum_length]
      rfl
  have hMap : Measure.map population mu = P := by
    change Measure.map (fun omega i => X i omega) mu = _
    rw [hIndep.map_fun_eq_pi_map hX]
    congr 1
    funext i
    simpa only [Measure.map_id] using (hLaw i).map_eq
  have hPhi : AEMeasurable Phi jointLaw := hPopulation.prodMap measurable_id.aemeasurable
  have hPairedMap : Measure.map Phi jointLaw = revealLaw P := by
    have he := Measure.map_prod_map_of_aemeasurable mu lambda hPopulation measurable_id.aemeasurable
    rw [hMap, Measure.map_id] at he
    exact he.symm
  have hPair : IdentDistrib Phi (id : (Shao.Path n × LabelPerm n) →
      (Shao.Path n × LabelPerm n)) jointLaw (revealLaw P) :=
    ⟨hPhi, measurable_id.aemeasurable, by simpa only [Measure.map_id] using hPairedMap⟩
  have hBudget := hCanonical Q hReflection hRegular hSmall rho n hn h2 hmean hsecond x hx0 hx1
  have hNu (sigma : LabelPerm n) : AEMeasurable (fun omega => nu omega sigma) mu :=
    (hBudget.1 sigma).comp_aemeasurable hPopulation
  have hL0m (r : ℕ) : Measurable (fun p => L0 p r) := (hBudget.2.1 r).1
  have hO0m (r : ℕ) : Measurable (fun p => O0 p r) := (hBudget.2.1 r).2
  have hS0m : Measurable S0 := by
    apply Finset.measurable_sum
    intro r _
    exact (continuous_abs.measurable.comp (hL0m r)).add
      ((hO0m r).neg.max measurable_const)
  have hFamilyMeas (r : ℕ) :
      AEMeasurable (fun p => L p r) jointLaw ∧ AEMeasurable (fun p => O p r) jointLaw :=
    ⟨(hPair.comp (hL0m r)).aemeasurable_fst, (hPair.comp (hO0m r)).aemeasurable_fst⟩
  have hFamilyInt (r : ℕ) :
      Integrable (fun p => L p r) jointLaw ∧ Integrable (fun p => O p r) jointLaw :=
    ⟨(hPair.comp (hL0m r)).integrable_iff.mpr ((hBudget.2.2.1 r).1),
      (hPair.comp (hO0m r)).integrable_iff.mpr ((hBudget.2.2.1 r).2)⟩
  refine ⟨hState, hNu, hFamilyMeas, hFamilyInt,
    (hPair.comp hS0m).integrable_iff.mpr hBudget.2.2.2.1, ?_⟩
  calc
    _ = ∫ p, S0 p ∂revealLaw P := (hPair.comp hS0m).integral_eq
    _ ≤ _ := hBudget.2.2.2.2


end Shao.Probability.SourceOriginalIIDIntervalBudget
