import Shao.OQ6.CoordinateBorelFactorization
import Shao.OQ6.FiniteUniformCodingAssembly
import Shao.OQ6.NormalizedEventTransport
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Shao.OQ6.AmbientCanonicalCodingTransport

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical symmDiff

theorem ambient_independent_uniform_observation_transport
    {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Type*}
    [mX : ∀ i : Fin n, MeasurableSpace (X i)]
    (O : ∀ i : Fin n, A → X i)
    (hO : ∀ i : Fin n, Measurable (O i))
    (hOindep : iIndepFun O P) :
    let μ : ∀ i : Fin n, Measure (X i) := fun i => P.map (O i)
    let μ0 : Measure (∀ i : Fin n, X i) := Measure.pi μ
    let Q : A → (∀ i : Fin n, X i) := fun ω i => O i ω
    let lambda01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
    let νlocal : ∀ i : Fin n, Measure (X i × ℝ) := fun i => (μ i).prod lambda01
    let ν : Measure (∀ i : Fin n, X i × ℝ) := Measure.pi νlocal
    let q : (∀ i : Fin n, X i × ℝ) → (∀ i : Fin n, X i) := fun x i => (x i).1
    let U : (∀ i : Fin n, X i × ℝ) → (Fin n → ℝ) := fun x i => (x i).2
    let Λ : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => lambda01)
    (∀ i : Fin n, IsProbabilityMeasure (μ i)) ∧
    IsProbabilityMeasure μ0 ∧ IsProbabilityMeasure ν ∧
    MeasurePreserving Q P μ0 ∧ MeasurePreserving q ν μ0 ∧
    MeasurePreserving U ν Λ ∧ IndepFun q U ν ∧
    (∀ (m : ℕ) (H : (∀ i : Fin n, X i) → (Fin m → ℝ)), Measurable H →
      Measure.map (fun x : (∀ i : Fin n, X i × ℝ) => H (q x)) ν =
        Measure.map (fun ω : A => H (Q ω)) P) ∧
    (∀ (h : (∀ i : Fin n, X i) → ℝ), Measurable h →
      Measure.map (fun x : (∀ i : Fin n, X i × ℝ) => h (q x)) ν =
        Measure.map (fun ω : A => h (Q ω)) P) ∧
    (∀ (h : (∀ i : Fin n, X i) → ℝ), Measurable h →
      Integrable (fun ω : A => h (Q ω)) P →
        Integrable h μ0 ∧
        (∫ o, h o ∂μ0) = ∫ ω, h (Q ω) ∂P ∧
        Integrable (fun x : (∀ i : Fin n, X i × ℝ) => h (q x)) ν ∧
        (∫ x, h (q x) ∂ν) = ∫ ω, h (Q ω) ∂P) ∧
    (∀ (h : (∀ i : Fin n, X i) → ℝ), Measurable h →
      MemLp (fun ω : A => h (Q ω)) 2 P →
        MemLp h 2 μ0 ∧
        MemLp (fun x : (∀ i : Fin n, X i × ℝ) => h (q x)) 2 ν) ∧
    (∀ (i : Fin n) (d : (∀ j : {j : Fin n // j ≠ i}, X j.1) → ℝ),
      Measurable d →
        Measure.map (fun x : (∀ j : Fin n, X j × ℝ) => d (fun j => (x j.1).1)) ν =
          Measure.map (fun ω : A => d (fun j => O j.1 ω)) P) ∧
    (∀ (E : Set (∀ i : Fin n, X i)), MeasurableSet E →
      ν (q ⁻¹' E) = P (Q ⁻¹' E) ∧
      ν.real (q ⁻¹' E) = P.real (Q ⁻¹' E)) := by
  classical
  dsimp only
  let μ : ∀ i : Fin n, Measure (X i) := fun i => P.map (O i)
  let μ0 : Measure (∀ i : Fin n, X i) := Measure.pi μ
  let Q : A → (∀ i : Fin n, X i) := fun ω i => O i ω
  let lambda01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
  let νlocal : ∀ i : Fin n, Measure (X i × ℝ) := fun i => (μ i).prod lambda01
  let ν : Measure (∀ i : Fin n, X i × ℝ) := Measure.pi νlocal
  let q : (∀ i : Fin n, X i × ℝ) → (∀ i : Fin n, X i) := fun x i => (x i).1
  let U : (∀ i : Fin n, X i × ℝ) → (Fin n → ℝ) := fun x i => (x i).2
  let Λ : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => lambda01)
  have hμprob (i : Fin n) : IsProbabilityMeasure (μ i) := by
    dsimp only [μ]
    infer_instance
  letI : ∀ i : Fin n, IsProbabilityMeasure (μ i) := hμprob
  have hμ0prob : IsProbabilityMeasure μ0 := by
    dsimp only [μ0]
    infer_instance
  letI : IsProbabilityMeasure μ0 := hμ0prob
  have hQmeas : Measurable Q :=
    measurable_pi_iff.2 hO
  have hQ : MeasurePreserving Q P μ0 := by
    refine ⟨hQmeas, ?_⟩
    exact (iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Fin n => (hO i).aemeasurable)).1 hOindep
  rcases Shao.OQ6.FiniteUniformCodingAssembly.finite_uniform_augmentation_spec μ with
    ⟨hLambda, hlocalProb, hprob, hq, hU, hgroup, heval, hobs, hunif,
      hindAug, hindU, hindqU, hfullLaw, hdeletedLaw⟩
  letI : IsProbabilityMeasure ν := hprob
  have hvectorLaw (m : ℕ) (H : (∀ i : Fin n, X i) → (Fin m → ℝ))
      (hH : Measurable H) :
      Measure.map (fun x : (∀ i : Fin n, X i × ℝ) => H (q x)) ν =
        Measure.map (fun ω : A => H (Q ω)) P := by
    calc
      Measure.map (fun x : (∀ i : Fin n, X i × ℝ) => H (q x)) ν =
          Measure.map H (Measure.map q ν) := by
        simpa only [Function.comp_def] using (Measure.map_map hH hq.measurable).symm
      _ = Measure.map H μ0 := by rw [hq.map_eq]
      _ = Measure.map (fun ω : A => H (Q ω)) P := by
        rw [← hQ.map_eq]
        simpa only [Function.comp_def] using Measure.map_map hH hQmeas
  have hrealLaw (h : (∀ i : Fin n, X i) → ℝ) (hh : Measurable h) :
      Measure.map (fun x : (∀ i : Fin n, X i × ℝ) => h (q x)) ν =
        Measure.map (fun ω : A => h (Q ω)) P := by
    calc
      Measure.map (fun x : (∀ i : Fin n, X i × ℝ) => h (q x)) ν =
          Measure.map h (Measure.map q ν) := by
        simpa only [Function.comp_def] using (Measure.map_map hh hq.measurable).symm
      _ = Measure.map h μ0 := by rw [hq.map_eq]
      _ = Measure.map (fun ω : A => h (Q ω)) P := by
        rw [← hQ.map_eq]
        simpa only [Function.comp_def] using Measure.map_map hh hQmeas
  have hintegral (h : (∀ i : Fin n, X i) → ℝ) (hh : Measurable h)
      (hhOriginal : Integrable (fun ω : A => h (Q ω)) P) :
      Integrable h μ0 ∧
      (∫ o, h o ∂μ0) = ∫ ω, h (Q ω) ∂P ∧
      Integrable (fun x : (∀ i : Fin n, X i × ℝ) => h (q x)) ν ∧
      (∫ x, h (q x) ∂ν) = ∫ ω, h (Q ω) ∂P := by
    have hh0 : Integrable h μ0 :=
      (hQ.integrable_comp hh.aestronglyMeasurable).1 hhOriginal
    have hhν : Integrable (fun x : (∀ i : Fin n, X i × ℝ) => h (q x)) ν :=
      hq.integrable_comp_of_integrable hh0
    have hhMapQ : AEStronglyMeasurable h (P.map Q) := by
      rw [hQ.map_eq]
      exact hh0.aestronglyMeasurable
    have hfirst : (∫ o, h o ∂μ0) = ∫ ω, h (Q ω) ∂P := by
      have hi := integral_map hQ.aemeasurable hhMapQ
      rw [hQ.map_eq] at hi
      exact hi
    have hhMapq : AEStronglyMeasurable h (ν.map q) := by
      rw [hq.map_eq]
      exact hh0.aestronglyMeasurable
    have hsecond : (∫ x, h (q x) ∂ν) = ∫ o, h o ∂μ0 := by
      have hi := integral_map hq.aemeasurable hhMapq
      rw [hq.map_eq] at hi
      exact hi.symm
    exact ⟨hh0, hfirst, hhν, hsecond.trans hfirst⟩
  have hL2 (h : (∀ i : Fin n, X i) → ℝ) (hh : Measurable h)
      (hhOriginal : MemLp (fun ω : A => h (Q ω)) 2 P) :
      MemLp h 2 μ0 ∧
      MemLp (fun x : (∀ i : Fin n, X i × ℝ) => h (q x)) 2 ν := by
    have hm : MemLp h 2 (P.map Q) :=
      (memLp_map_measure_iff hh.aestronglyMeasurable hQ.aemeasurable).2 hhOriginal
    rw [hQ.map_eq] at hm
    exact ⟨hm, hm.comp_measurePreserving hq⟩
  have hdeleted (i : Fin n)
      (d : (∀ j : {j : Fin n // j ≠ i}, X j.1) → ℝ) (hd : Measurable d) :
      Measure.map (fun x : (∀ j : Fin n, X j × ℝ) => d (fun j => (x j.1).1)) ν =
        Measure.map (fun ω : A => d (fun j => O j.1 ω)) P := by
    exact hrealLaw (fun o => d (fun j => o j.1))
      (hd.comp (measurable_pi_iff.2 (fun j => measurable_pi_apply j.1)))
  have hEvents (E : Set (∀ i : Fin n, X i)) (hE : MeasurableSet E) :
      ν (q ⁻¹' E) = P (Q ⁻¹' E) ∧
      ν.real (q ⁻¹' E) = P.real (Q ⁻¹' E) := by
    have hqE : ν (q ⁻¹' E) = μ0 E := by
      have he := Measure.map_apply (μ := ν) hq.measurable hE
      rw [hq.map_eq] at he
      exact he.symm
    have hQE : P (Q ⁻¹' E) = μ0 E := by
      have he := Measure.map_apply (μ := P) hQmeas hE
      rw [hQ.map_eq] at he
      exact he.symm
    have he : ν (q ⁻¹' E) = P (Q ⁻¹' E) := hqE.trans hQE.symm
    refine ⟨he, ?_⟩
    change (ν (q ⁻¹' E)).toReal = (P (Q ⁻¹' E)).toReal
    exact congrArg ENNReal.toReal he
  exact ⟨hμprob, hμ0prob, hprob, hQ, hq, hU, hindqU, hvectorLaw, hrealLaw,
    hintegral, hL2, hdeleted, hEvents⟩

theorem ambient_canonical_normalized_observation_consumer
    {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n) {X : Fin n → Type*}
    [mX : ∀ i : Fin n, MeasurableSpace (X i)]
    [∀ i : Fin n, MeasurableSpace.CountablyGenerated (X i)]
    (O : ∀ i : Fin n, A → X i)
    (hO : ∀ i : Fin n, Measurable (O i))
    (hOindep : iIndepFun O P)
    (g : ∀ i : Fin n, X i → ℝ)
    (hg : ∀ i : Fin n, Measurable (g i))
    (hg2 : ∀ i : Fin n, MemLp (fun ω : A => g i (O i ω)) 2 P)
    (hgmean : ∀ i : Fin n, (∫ ω, g i (O i ω) ∂P) = 0)
    (hgenergy : (∑ i : Fin n, ∫ ω, (g i (O i ω)) ^ 2 ∂P) = 1)
    (D1 D2 : (∀ i : Fin n, X i) → ℝ)
    (hD1 : Measurable D1) (hD2 : Measurable D2)
    (κ : A → ℝ) (hκ : Measurable κ)
    (hD2pos : ∀ᵐ ω ∂P, 0 < 1 + D2 (fun i => O i ω))
    (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε < 1 / (4 * Real.sqrt (n : ℝ))) :
    let μ : ∀ i : Fin n, Measure (X i) := fun i => P.map (O i)
    let μ0 : Measure (∀ i : Fin n, X i) := Measure.pi μ
    let Q : A → (∀ i : Fin n, X i) := fun ω i => O i ω
    let lambda01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
    let νlocal : ∀ i : Fin n, Measure (X i × ℝ) := fun i => (μ i).prod lambda01
    let ν : Measure (∀ i : Fin n, X i × ℝ) := Measure.pi νlocal
    let q : (∀ i : Fin n, X i × ℝ) → (∀ i : Fin n, X i) := fun x i => (x i).1
    let c : ∀ i : Fin n, (X i × ℝ) → ℝ := fun i => Shao.OQ6.ScalarObservationCoding.baseFourIndicatorCode (MeasurableSpace.natGeneratingSequence (X i × ℝ))
    let ξlocal : ∀ i : Fin n, (X i × ℝ) → ℝ := fun i z => g i z.1
    let Ylocal : ∀ i : Fin n, (X i × ℝ) → ℝ := fun i => Shao.OQ6.QuantizedObservationCoding.quantizedObservation ε (ξlocal i) (c i)
    let ξ : Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun i x => g i (x i).1
    let Y : Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun i x => Ylocal i (x i)
    let a : Fin n → ℝ := Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν Y
    let s : ℝ := Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν Y
    let ηlocal : ∀ i : Fin n, (X i × ℝ) → ℝ := fun i => Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation (a i) s (Ylocal i)
    let η : Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν Y
    let C : (∀ i : Fin n, X i × ℝ) → (Fin n → ℝ) := fun x i => η i x
    let W0 : A → ℝ := fun ω => ∑ i : Fin n, g i (O i ω)
    let V0 : A → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (g i (O i ω)) ^ 2)
    let W : (∀ i : Fin n, X i × ℝ) → ℝ := fun x => ∑ i : Fin n, ξ i x
    let V : (∀ i : Fin n, X i × ℝ) → ℝ := fun x => Real.sqrt (∑ i : Fin n, (ξ i x) ^ 2)
    let Wη : (∀ i : Fin n, X i × ℝ) → ℝ := fun x => ∑ i : Fin n, η i x
    let Vη : (∀ i : Fin n, X i × ℝ) → ℝ := fun x => Real.sqrt (∑ i : Fin n, (η i x) ^ 2)
    let b : (∀ i : Fin n, X i × ℝ) → ℝ := fun x => Real.sqrt (1 + D2 (q x))
    let Dη : ℝ → (∀ i : Fin n, X i × ℝ) → ℝ := fun z x => D1 (q x) + W x - Wη x + z * b x * (Vη x - V x)
    let T0 : A → ℝ := fun ω => if V0 ω = 0 then κ ω else (W0 ω + D1 (Q ω)) / (V0 ω * Real.sqrt (1 + D2 (Q ω)))
    let Tη : ℝ → (∀ i : Fin n, X i × ℝ) → ℝ := fun z x => (Wη x + Dη z x) / (Vη x * b x)
    let Z0 : Set A := {ω : A | V0 ω = 0}
    let Z : Set (∀ i : Fin n, X i × ℝ) := {x : (∀ i : Fin n, X i × ℝ) | V x = 0}
    let p0 : ℝ := P.real Z0
    let comparisons : Set (ℝ → ℝ → Prop) := {R | R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨ R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨ R = (fun a b : ℝ => a = b)}
    let F0 : (ℝ → ℝ → Prop) → ℝ → Set A := fun R z => {ω : A | R (W0 ω + D1 (Q ω)) (z * V0 ω * Real.sqrt (1 + D2 (Q ω)))}
    let A0 : (ℝ → ℝ → Prop) → ℝ → Set A := fun R z => {ω : A | R (T0 ω) z}
    let Eη : (ℝ → ℝ → Prop) → ℝ → Set (∀ i : Fin n, X i × ℝ) := fun R z => {x : (∀ i : Fin n, X i × ℝ) | R (Tη z x) z}
    IsProbabilityMeasure ν ∧
    MeasurePreserving Q P μ0 ∧ MeasurePreserving q ν μ0 ∧
    (1 / 2 : ℝ) < s ∧
    (∀ (i : Fin n) (x : ∀ j : Fin n, X j × ℝ), η i x = ηlocal i (x i)) ∧
    iIndepFun η ν ∧
    (∀ i : Fin n, Measurable (η i) ∧ MemLp (η i) 2 ν) ∧
    (∀ i : Fin n, Integrable (η i) ν ∧ Integrable (fun x => (η i x) ^ 2) ν) ∧
    (∀ i : Fin n, (∫ x, η i x ∂ν) = 0) ∧
    (∑ i : Fin n, ∫ x, (η i x) ^ 2 ∂ν) = 1 ∧
    (∀ (i : Fin n) (t : ℝ), ν ({x : (∀ j : Fin n, X j × ℝ) | η i x = t}) = 0) ∧
    ν ({x : (∀ i : Fin n, X i × ℝ) | Vη x = 0}) = 0 ∧
    (∀ᵐ x ∂ν, 0 < Vη x) ∧
    Measurable[(inferInstance : MeasurableSpace (∀ i : Fin n, X i × ℝ)), borel (Fin n → ℝ)] C ∧
    MeasurableSpace.comap C (borel (Fin n → ℝ)) = (inferInstance : MeasurableSpace (∀ i : Fin n, X i × ℝ)) ∧
    (∀ (h : (∀ i : Fin n, X i × ℝ) → ℝ), Measurable h →
      ∃ F : (Fin n → ℝ) → ℝ, Measurable[borel (Fin n → ℝ), borel ℝ] F ∧
        ∀ x : (∀ i : Fin n, X i × ℝ), h x = F (C x)) ∧
    (∀ (i : Fin n) (d : (∀ j : {j : Fin n // j ≠ i}, X j.1 × ℝ) → ℝ), Measurable d →
      ∃ F : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] F ∧
        (∀ y : (∀ j : {j : Fin n // j ≠ i}, X j.1 × ℝ), d y = F (fun j => ηlocal j.1 (y j))) ∧
        Measurable[borel (Fin n → ℝ), borel ℝ] (fun v : Fin n → ℝ => F (fun j => v j.1)) ∧
        ∀ x : (∀ j : Fin n, X j × ℝ), d (fun j => x j.1) = F (fun j => η j.1 x)) ∧
    (∃ G2 : (Fin n → ℝ) → ℝ,
      Measurable[borel (Fin n → ℝ), borel ℝ] G2 ∧
      (∀ x : (∀ i : Fin n, X i × ℝ), D2 (q x) = G2 (C x)) ∧
      ∀ z : ℝ, ∃ G1 : (Fin n → ℝ) → ℝ,
        Measurable[borel (Fin n → ℝ), borel ℝ] G1 ∧
        ∀ x : (∀ i : Fin n, X i × ℝ), Dη z x = G1 (C x)) ∧
    Measurable T0 ∧ (∀ z : ℝ, Measurable (Tη z)) ∧
    MeasurableSet Z0 ∧ MeasurableSet Z ∧
    ν Z = P Z0 ∧ ν.real Z = p0 ∧
    (∀ (z : ℝ) (x : ∀ i : Fin n, X i × ℝ),
      Wη x + Dη z x - z * Vη x * b x = W x + D1 (q x) - z * V x * b x) ∧
    (∀ (z : ℝ) (R : ℝ → ℝ → Prop), R ∈ comparisons →
      MeasurableSet (A0 R z) ∧ MeasurableSet (F0 R z) ∧ MeasurableSet (Eη R z) ∧
      ν (Eη R z) = P (F0 R z) ∧
      (∀ᵐ ω ∂P, ω ∈ (A0 R z ∆ F0 R z) → ω ∈ Z0) ∧
      P (A0 R z ∆ F0 R z) ≤ P Z0 ∧
      |P.real (A0 R z) - ν.real (Eη R z)| ≤ p0) := by
  classical
  dsimp only
  let μ : ∀ i : Fin n, Measure (X i) := fun i => P.map (O i)
  let μ0 : Measure (∀ i : Fin n, X i) := Measure.pi μ
  let Q : A → (∀ i : Fin n, X i) := fun ω i => O i ω
  let lambda01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
  let νlocal : ∀ i : Fin n, Measure (X i × ℝ) := fun i => (μ i).prod lambda01
  let ν : Measure (∀ i : Fin n, X i × ℝ) := Measure.pi νlocal
  let q : (∀ i : Fin n, X i × ℝ) → (∀ i : Fin n, X i) := fun x i => (x i).1
  let c : ∀ i : Fin n, (X i × ℝ) → ℝ := fun i => Shao.OQ6.ScalarObservationCoding.baseFourIndicatorCode (MeasurableSpace.natGeneratingSequence (X i × ℝ))
  let ξlocal : ∀ i : Fin n, (X i × ℝ) → ℝ := fun i z => g i z.1
  let Ylocal : ∀ i : Fin n, (X i × ℝ) → ℝ := fun i => Shao.OQ6.QuantizedObservationCoding.quantizedObservation ε (ξlocal i) (c i)
  let ξ : Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun i x => g i (x i).1
  let Y : Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun i x => Ylocal i (x i)
  let a : Fin n → ℝ := Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν Y
  let s : ℝ := Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν Y
  let ηlocal : ∀ i : Fin n, (X i × ℝ) → ℝ := fun i => Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation (a i) s (Ylocal i)
  let η : Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν Y
  let C : (∀ i : Fin n, X i × ℝ) → (Fin n → ℝ) := fun x i => η i x
  let W0 : A → ℝ := fun ω => ∑ i : Fin n, g i (O i ω)
  let V0 : A → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (g i (O i ω)) ^ 2)
  let W : (∀ i : Fin n, X i × ℝ) → ℝ := fun x => ∑ i : Fin n, ξ i x
  let V : (∀ i : Fin n, X i × ℝ) → ℝ := fun x => Real.sqrt (∑ i : Fin n, (ξ i x) ^ 2)
  let Wη : (∀ i : Fin n, X i × ℝ) → ℝ := fun x => ∑ i : Fin n, η i x
  let Vη : (∀ i : Fin n, X i × ℝ) → ℝ := fun x => Real.sqrt (∑ i : Fin n, (η i x) ^ 2)
  let b : (∀ i : Fin n, X i × ℝ) → ℝ := fun x => Real.sqrt (1 + D2 (q x))
  let Dη : ℝ → (∀ i : Fin n, X i × ℝ) → ℝ := fun z x => D1 (q x) + W x - Wη x + z * b x * (Vη x - V x)
  let T0 : A → ℝ := fun ω => if V0 ω = 0 then κ ω else (W0 ω + D1 (Q ω)) / (V0 ω * Real.sqrt (1 + D2 (Q ω)))
  let Tη : ℝ → (∀ i : Fin n, X i × ℝ) → ℝ := fun z x => (Wη x + Dη z x) / (Vη x * b x)
  let Z0 : Set A := {ω : A | V0 ω = 0}
  let Z : Set (∀ i : Fin n, X i × ℝ) := {x : (∀ i : Fin n, X i × ℝ) | V x = 0}
  let p0 : ℝ := P.real Z0
  let comparisons : Set (ℝ → ℝ → Prop) := {R | R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨ R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨ R = (fun a b : ℝ => a = b)}
  let F0 : (ℝ → ℝ → Prop) → ℝ → Set A := fun R z => {ω : A | R (W0 ω + D1 (Q ω)) (z * V0 ω * Real.sqrt (1 + D2 (Q ω)))}
  let A0 : (ℝ → ℝ → Prop) → ℝ → Set A := fun R z => {ω : A | R (T0 ω) z}
  let Eη : (ℝ → ℝ → Prop) → ℝ → Set (∀ i : Fin n, X i × ℝ) := fun R z => {x : (∀ i : Fin n, X i × ℝ) | R (Tη z x) z}
  rcases ambient_independent_uniform_observation_transport P O hO hOindep with
    ⟨hμprob, hμ0prob, hprob, hQ, hq, hU, hindqU, hvectorLaw, hrealLaw,
      hintegral, hL2, hdeletedLaw, hEvents⟩
  letI : ∀ i : Fin n, IsProbabilityMeasure (μ i) := hμprob
  letI : IsProbabilityMeasure μ0 := hμ0prob
  letI : IsProbabilityMeasure ν := hprob
  have hgLocal2 (i : Fin n) : MemLp (g i) 2 (μ i) := by
    change MemLp (g i) 2 (P.map (O i))
    exact (memLp_map_measure_iff (hg i).aestronglyMeasurable
      (hO i).aemeasurable).2 (hg2 i)
  have hgLocalInt (i : Fin n) : Integrable (g i) (μ i) :=
    MemLp.integrable (by norm_num) (hgLocal2 i)
  have hgLocalSqInt (i : Fin n) : Integrable (fun o => (g i o) ^ 2) (μ i) :=
    (hgLocal2 i).integrable_sq
  have hgLocalFirst (i : Fin n) :
      (∫ o, g i o ∂(μ i)) = ∫ ω, g i (O i ω) ∂P := by
    have hm : AEStronglyMeasurable (g i) (P.map (O i)) :=
      (hgLocalInt i).aestronglyMeasurable
    exact integral_map (hO i).aemeasurable hm
  have hgLocalSecond (i : Fin n) :
      (∫ o, (g i o) ^ 2 ∂(μ i)) = ∫ ω, (g i (O i ω)) ^ 2 ∂P := by
    have hm : AEStronglyMeasurable (fun o : X i => (g i o) ^ 2) (P.map (O i)) :=
      (hgLocalSqInt i).aestronglyMeasurable
    exact integral_map (hO i).aemeasurable hm
  have hgLocalMean (i : Fin n) : (∫ o, g i o ∂(μ i)) = 0 :=
    (hgLocalFirst i).trans (hgmean i)
  have hgLocalEnergy : (∑ i : Fin n, ∫ o, (g i o) ^ 2 ∂(μ i)) = 1 := by
    calc
      (∑ i : Fin n, ∫ o, (g i o) ^ 2 ∂(μ i)) =
          ∑ i : Fin n, ∫ ω, (g i (O i ω)) ^ 2 ∂P :=
        Finset.sum_congr rfl (fun i _ => hgLocalSecond i)
      _ = 1 := hgenergy
  rcases Shao.OQ6.FiniteUniformCodingAssembly.actual_finite_normalized_coding_spec
      n hn μ g hg hgLocal2 hgLocalMean hgLocalEnergy ε hε hεsmall with
    ⟨hprob152, hobs, hξmeas, hξ2, hξFirst, hξSecond, hξmean, hξenergy,
      hYlocalMeas, hYmeas, herr, hYlocal2, hYlocalInt, hameanLocal,
      hameanBound, hs, hηlocalMeas, hηlocalComap, hηlocalNull, hηeval,
      hηindep, hηmeas, hη2, hηInt, hηSqInt, hηmean, hηenergy,
      hηnull, hVηnull, hVηpos⟩
  have hfull := Shao.OQ6.CoordinateBorelFactorization.finite_coordinate_code_tuple_spec
    (I := Fin n) (X := fun i : Fin n => X i × ℝ) ηlocal hηlocalComap
  have hCeq : C = Shao.OQ6.CoordinateBorelFactorization.coordinateCodeTuple ηlocal := by
    funext x i
    exact hηeval i x
  have hCmeas :
      Measurable[(inferInstance : MeasurableSpace (∀ i : Fin n, X i × ℝ)),
        borel (Fin n → ℝ)] C := by
    rw [hCeq]
    exact hfull.1
  have hCcomap : MeasurableSpace.comap C (borel (Fin n → ℝ)) =
      (inferInstance : MeasurableSpace (∀ i : Fin n, X i × ℝ)) := by
    rw [hCeq]
    exact hfull.2.1
  have hfactor (h : (∀ i : Fin n, X i × ℝ) → ℝ) (hh : Measurable h) :
      ∃ F : (Fin n → ℝ) → ℝ,
        Measurable[borel (Fin n → ℝ), borel ℝ] F ∧
        ∀ x : (∀ i : Fin n, X i × ℝ), h x = F (C x) := by
    obtain ⟨F, hF, hEq⟩ := hfull.2.2 h hh
    refine ⟨F, hF, ?_⟩
    intro x
    rw [hCeq]
    exact hEq x
  have hdelete (i : Fin n)
      (d : (∀ j : {j : Fin n // j ≠ i}, X j.1 × ℝ) → ℝ) (hd : Measurable d) :
      ∃ F : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] F ∧
        (∀ y : (∀ j : {j : Fin n // j ≠ i}, X j.1 × ℝ),
          d y = F (fun j => ηlocal j.1 (y j))) ∧
        Measurable[borel (Fin n → ℝ), borel ℝ]
          (fun v : Fin n → ℝ => F (fun j => v j.1)) ∧
        ∀ x : (∀ j : Fin n, X j × ℝ),
          d (fun j => x j.1) = F (fun j => η j.1 x) := by
    rcases Shao.OQ6.CoordinateBorelFactorization.finite_deleted_code_factorization
        (X := fun j : Fin n => X j × ℝ) ηlocal hηlocalComap i with
      ⟨hpX, hpR, hCdel, hCdelComap, hcomm, hLiftComap, hfactorDel⟩
    obtain ⟨F, hF, hEq, hFlift, hEqLift⟩ := hfactorDel d hd
    refine ⟨F, hF, hEq, hFlift, ?_⟩
    intro x
    calc
      d (fun j => x j.1) = F (fun j => ηlocal j.1 (x j.1)) := hEqLift x
      _ = F (fun j => η j.1 x) := by
        congr 1
  have hD1q : Measurable (fun x : (∀ i : Fin n, X i × ℝ) => D1 (q x)) :=
    hD1.comp hq.measurable
  have hD2q : Measurable (fun x : (∀ i : Fin n, X i × ℝ) => D2 (q x)) :=
    hD2.comp hq.measurable
  have hPosBaseMeas : MeasurableSet {o : (∀ i : Fin n, X i) | 0 < 1 + D2 o} :=
    measurableSet_lt measurable_const (measurable_const.add hD2)
  have hPosBase : ∀ᵐ o ∂μ0, 0 < 1 + D2 o := by
    have hm : ∀ᵐ o ∂P.map Q, 0 < 1 + D2 o :=
      (ae_map_iff hQ.aemeasurable hPosBaseMeas).2 hD2pos
    rw [hQ.map_eq] at hm
    exact hm
  have hPosν : ∀ᵐ x ∂ν, 0 < 1 + D2 (q x) := by
    have hm : ∀ᵐ o ∂ν.map q, 0 < 1 + D2 o := by
      rw [hq.map_eq]
      exact hPosBase
    exact ae_of_ae_map hq.aemeasurable hm
  rcases Shao.OQ6.NormalizedEventTransport.actual_normalized_quotient_projection_zero_transport
      ν ξ Y hξmeas hYmeas (fun x => D1 (q x)) (fun x => D2 (q x))
      (fun _ => (0 : ℝ)) hD1q hD2q measurable_const hPosν hVηpos with
    ⟨hηmeas153, hWmeas, hWηmeas, hVmeas, hVηmeas, hbmeas, hDηmeas,
      hTaugmeas, hTηmeas, hZmeas, hcommon, hphysicalAug, hcomparisonAug⟩
  have hscalar :
      ∃ G2 : (Fin n → ℝ) → ℝ,
        Measurable[borel (Fin n → ℝ), borel ℝ] G2 ∧
        (∀ x : (∀ i : Fin n, X i × ℝ), D2 (q x) = G2 (C x)) ∧
        ∀ z : ℝ, ∃ G1 : (Fin n → ℝ) → ℝ,
          Measurable[borel (Fin n → ℝ), borel ℝ] G1 ∧
          ∀ x : (∀ i : Fin n, X i × ℝ), Dη z x = G1 (C x) := by
    obtain ⟨G2, hG2, hEq2⟩ := hfactor (fun x => D2 (q x)) hD2q
    refine ⟨G2, hG2, hEq2, ?_⟩
    intro z
    exact hfactor (Dη z) (hDηmeas z)
  let Wbase : (∀ i : Fin n, X i) → ℝ := fun o => ∑ i : Fin n, g i (o i)
  let Vbase : (∀ i : Fin n, X i) → ℝ := fun o => Real.sqrt (∑ i : Fin n, (g i (o i)) ^ 2)
  have hWbaseMeas : Measurable Wbase := by
    exact Finset.measurable_sum Finset.univ
      (fun i _ => (hg i).comp (measurable_pi_apply i))
  have hVbaseMeas : Measurable Vbase := by
    apply Measurable.sqrt
    exact Finset.measurable_sum Finset.univ (fun i _ =>
      ((hg i).comp (measurable_pi_apply i)).pow
        (measurable_const : Measurable (fun _ : (∀ j : Fin n, X j) => (2 : ℕ))))
  have hW0meas : Measurable W0 := hWbaseMeas.comp hQ.measurable
  have hV0meas : Measurable V0 := hVbaseMeas.comp hQ.measurable
  have hD1Q : Measurable (fun ω : A => D1 (Q ω)) := hD1.comp hQ.measurable
  have hD2Q : Measurable (fun ω : A => D2 (Q ω)) := hD2.comp hQ.measurable
  have hb0meas : Measurable (fun ω : A => Real.sqrt (1 + D2 (Q ω))) :=
    (measurable_const.add hD2Q).sqrt
  have hZ0meas : MeasurableSet Z0 := measurableSet_eq_fun hV0meas measurable_const
  have hT0meas : Measurable T0 := by
    exact Measurable.ite hZ0meas hκ
      ((hW0meas.add hD1Q).div (hV0meas.mul hb0meas))
  have hZbaseMeas : MeasurableSet {o : (∀ i : Fin n, X i) | Vbase o = 0} :=
    measurableSet_eq_fun hVbaseMeas measurable_const
  have hZlaw : ν Z = P Z0 := by
    exact (hEvents {o : (∀ i : Fin n, X i) | Vbase o = 0} hZbaseMeas).1
  have hZreal : ν.real Z = p0 := by
    change (ν Z).toReal = (P Z0).toReal
    exact congrArg ENNReal.toReal hZlaw
  have hsigned : ∀ (z : ℝ) (x : ∀ i : Fin n, X i × ℝ),
      Wη x + Dη z x - z * Vη x * b x =
        W x + D1 (q x) - z * V x * b x :=
    (Shao.OQ6.NormalizedEventTransport.actual_normalized_signed_distance_transport
      ν ξ Y (fun x => D1 (q x)) (fun x => D2 (q x))).1
  have hrelOriginal (f t : A → ℝ) (hf : Measurable f) (ht : Measurable t)
      (R : ℝ → ℝ → Prop) (hR : R ∈ comparisons) :
      MeasurableSet {x : A | R (f x) (t x)} := by
    change R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨
      R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨
      R = (fun a b : ℝ => a = b) at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl
    · exact measurableSet_le hf ht
    · exact measurableSet_lt hf ht
    · exact measurableSet_le ht hf
    · exact measurableSet_lt ht hf
    · exact measurableSet_eq_fun hf ht
  have hrelBase (f t : (∀ i : Fin n, X i) → ℝ)
      (hf : Measurable f) (ht : Measurable t)
      (R : ℝ → ℝ → Prop) (hR : R ∈ comparisons) :
      MeasurableSet {x : (∀ i : Fin n, X i) | R (f x) (t x)} := by
    change R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨
      R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨
      R = (fun a b : ℝ => a = b) at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl
    · exact measurableSet_le hf ht
    · exact measurableSet_lt hf ht
    · exact measurableSet_le ht hf
    · exact measurableSet_lt ht hf
    · exact measurableSet_eq_fun hf ht
  have hdivCompare (u v z : ℝ) (hv : 0 < v)
      (R : ℝ → ℝ → Prop) (hR : R ∈ comparisons) :
      (R (u / v) z ↔ R u (z * v)) := by
    change R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨
      R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨
      R = (fun a b : ℝ => a = b) at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl
    · exact div_le_iff₀ hv
    · exact div_lt_iff₀ hv
    · exact le_div_iff₀ hv
    · exact lt_div_iff₀ hv
    · constructor
      · intro h
        exact le_antisymm ((div_le_iff₀ hv).mp h.le) ((le_div_iff₀ hv).mp h.ge)
      · intro h
        exact le_antisymm ((div_le_iff₀ hv).mpr h.le) ((le_div_iff₀ hv).mpr h.ge)
  have hphysical0 (ω : A) (hv : 0 < V0 ω) (hd : 0 < 1 + D2 (Q ω))
      (z : ℝ) (R : ℝ → ℝ → Prop) (hR : R ∈ comparisons) :
      (R (T0 ω) z ↔ R (W0 ω + D1 (Q ω))
        (z * V0 ω * Real.sqrt (1 + D2 (Q ω)))) := by
    have hbpos : 0 < Real.sqrt (1 + D2 (Q ω)) := Real.sqrt_pos.mpr hd
    have hc : 0 < V0 ω * Real.sqrt (1 + D2 (Q ω)) := mul_pos hv hbpos
    simpa only [T0, if_neg (ne_of_gt hv), mul_assoc] using
      hdivCompare (W0 ω + D1 (Q ω))
        (V0 ω * Real.sqrt (1 + D2 (Q ω))) z hc R hR
  refine ⟨hprob, hQ, hq, hs, hηeval, hηindep,
    (fun i => ⟨hηmeas i, hη2 i⟩), (fun i => ⟨hηInt i, hηSqInt i⟩),
    hηmean, hηenergy, hηnull, hVηnull, hVηpos, hCmeas, hCcomap,
    hfactor, hdelete, hscalar, hT0meas, hTηmeas, hZ0meas, hZmeas,
    hZlaw, hZreal, hsigned, ?_⟩
  intro z R hR
  have hA0meas : MeasurableSet (A0 R z) :=
    hrelOriginal T0 (fun _ => z) hT0meas measurable_const R hR
  have hF0meas : MeasurableSet (F0 R z) :=
    hrelOriginal (fun ω => W0 ω + D1 (Q ω))
      (fun ω => z * V0 ω * Real.sqrt (1 + D2 (Q ω)))
      (hW0meas.add hD1Q) ((measurable_const.mul hV0meas).mul hb0meas) R hR
  rcases hcomparisonAug z R hR with
    ⟨hFaugMeas, hAaugMeas, hEηmeas, hEFaug, hAFaug, hAFaugMeasure,
      hAFaugReal, hAEaugMeasure, hAEaugReal⟩
  let Fbase : Set (∀ i : Fin n, X i) :=
    {o : (∀ i : Fin n, X i) | R (Wbase o + D1 o)
      (z * Vbase o * Real.sqrt (1 + D2 o))}
  have hFbaseMeas : MeasurableSet Fbase :=
    hrelBase (fun o => Wbase o + D1 o)
      (fun o => z * Vbase o * Real.sqrt (1 + D2 o))
      (hWbaseMeas.add hD1)
      ((measurable_const.mul hVbaseMeas).mul (measurable_const.add hD2).sqrt) R hR
  have hFlaw :
      ν ({x : (∀ i : Fin n, X i × ℝ) |
        R (W x + D1 (q x)) (z * V x * b x)}) = P (F0 R z) :=
    (hEvents Fbase hFbaseMeas).1
  have hEventEq : ν (Eη R z) = P (F0 R z) := hEFaug.trans hFlaw
  have hAF0 : ∀ᵐ ω ∂P, ω ∈ (A0 R z ∆ F0 R z) → ω ∈ Z0 := by
    filter_upwards [hD2pos] with ω hd
    intro hdiff
    by_contra hnot
    have hvne : V0 ω ≠ 0 := hnot
    have hv : 0 < V0 ω :=
      lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hvne)
    have heq : (ω ∈ A0 R z ↔ ω ∈ F0 R z) := hphysical0 ω hv hd z R hR
    rcases Set.mem_symmDiff.mp hdiff with ⟨ha, hf⟩ | ⟨hf, ha⟩
    · exact hf (heq.mp ha)
    · exact ha (heq.mpr hf)
  have hAFmeasure : P (A0 R z ∆ F0 R z) ≤ P Z0 := measure_mono_ae hAF0
  have hinter : (A0 R z ∆ F0 R z) =ᵐ[P] ((A0 R z ∆ F0 R z) ∩ Z0) := by
    filter_upwards [hAF0] with ω h
    exact propext ⟨fun hω => ⟨hω, h hω⟩, fun hω => hω.1⟩
  have hAFrealSubset : P.real (A0 R z ∆ F0 R z) ≤ p0 := by
    calc
      P.real (A0 R z ∆ F0 R z) = P.real ((A0 R z ∆ F0 R z) ∩ Z0) :=
        measureReal_congr hinter
      _ ≤ P.real Z0 := measureReal_mono (fun _ h => h.2) (measure_ne_top P Z0)
      _ = p0 := rfl
  have hEventRealEq : ν.real (Eη R z) = P.real (F0 R z) := by
    change (ν (Eη R z)).toReal = (P (F0 R z)).toReal
    exact congrArg ENNReal.toReal hEventEq
  have hRealBound : |P.real (A0 R z) - ν.real (Eη R z)| ≤ p0 := by
    rw [hEventRealEq]
    exact (abs_measureReal_sub_le_measureReal_symmDiff
      hA0meas.nullMeasurableSet hF0meas.nullMeasurableSet).trans hAFrealSubset
  exact ⟨hA0meas, hF0meas, hEηmeas, hEventEq, hAF0, hAFmeasure, hRealBound⟩

end

end Shao.OQ6.AmbientCanonicalCodingTransport
