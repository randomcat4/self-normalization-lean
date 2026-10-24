import Shao.OQ6.ActualMomentNormalization
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Shao.OQ6.FiniteUniformCodingAssembly

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

theorem finite_uniform_augmentation_spec
    {n : ℕ} {Ω : Fin n → Type*}
    [mΩ : ∀ i : Fin n, MeasurableSpace (Ω i)]
    (μ : ∀ i : Fin n, Measure (Ω i))
    [hμ : ∀ i : Fin n, IsProbabilityMeasure (μ i)] :
    let lambda01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
    let μ0 : Measure (∀ i : Fin n, Ω i) := Measure.pi μ
    let νlocal : ∀ i : Fin n, Measure (Ω i × ℝ) := fun i => (μ i).prod lambda01
    let ν : Measure (∀ i : Fin n, Ω i × ℝ) := Measure.pi νlocal
    let Λ : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => lambda01)
    let q : (∀ i : Fin n, Ω i × ℝ) → (∀ i : Fin n, Ω i) := fun x i => (x i).1
    let U : (∀ i : Fin n, Ω i × ℝ) → (Fin n → ℝ) := fun x i => (x i).2
    IsProbabilityMeasure lambda01 ∧
    (∀ i : Fin n, IsProbabilityMeasure (νlocal i)) ∧
    IsProbabilityMeasure ν ∧
    MeasurePreserving q ν μ0 ∧
    MeasurePreserving U ν Λ ∧
    MeasurePreserving (fun x : (∀ i : Fin n, Ω i × ℝ) => (q x, U x)) ν (μ0.prod Λ) ∧
    (∀ i : Fin n, MeasurePreserving (Function.eval i) ν (νlocal i)) ∧
    (∀ i : Fin n, MeasurePreserving (fun x : (∀ j : Fin n, Ω j × ℝ) => (x i).1) ν (μ i)) ∧
    (∀ i : Fin n, MeasurePreserving (fun x : (∀ j : Fin n, Ω j × ℝ) => (x i).2) ν lambda01) ∧
    iIndepFun (fun (i : Fin n) (x : ∀ j : Fin n, Ω j × ℝ) => x i) ν ∧
    iIndepFun (fun (i : Fin n) (x : ∀ j : Fin n, Ω j × ℝ) => (x i).2) ν ∧
    IndepFun q U ν ∧
    (∀ (F : (∀ i : Fin n, Ω i) → ℝ), Measurable F →
      Measure.map (fun x : (∀ i : Fin n, Ω i × ℝ) => F (q x)) ν = Measure.map F μ0) ∧
    (∀ (i : Fin n) (d : (∀ j : {j : Fin n // j ≠ i}, Ω j.1) → ℝ), Measurable d →
      Measure.map (fun x : (∀ j : Fin n, Ω j × ℝ) => d (fun j => (x j.1).1)) ν =
        Measure.map (fun o : (∀ j : Fin n, Ω j) => d (fun j => o j.1)) μ0) := by
  classical
  dsimp only
  let lambda01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
  let μ0 : Measure (∀ i : Fin n, Ω i) := Measure.pi μ
  let νlocal : ∀ i : Fin n, Measure (Ω i × ℝ) := fun i => (μ i).prod lambda01
  let ν : Measure (∀ i : Fin n, Ω i × ℝ) := Measure.pi νlocal
  let Λ : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => lambda01)
  let q : (∀ i : Fin n, Ω i × ℝ) → (∀ i : Fin n, Ω i) := fun x i => (x i).1
  let U : (∀ i : Fin n, Ω i × ℝ) → (Fin n → ℝ) := fun x i => (x i).2
  have hLambda : IsProbabilityMeasure lambda01 :=
    (Shao.OQ6.ScalarObservationCoding.countable_uniform_augmented_base_four_code
      (Measure.dirac (0 : ℝ))).1
  letI : IsProbabilityMeasure lambda01 := hLambda
  have hlocalProb (i : Fin n) : IsProbabilityMeasure (νlocal i) := by
    dsimp only [νlocal]
    infer_instance
  letI : ∀ i : Fin n, IsProbabilityMeasure (νlocal i) := hlocalProb
  have hprob : IsProbabilityMeasure ν := by
    dsimp only [ν]
    infer_instance
  letI : IsProbabilityMeasure ν := hprob
  have heval (i : Fin n) :
      MeasurePreserving (Function.eval i) ν (νlocal i) :=
    measurePreserving_eval νlocal i
  have hfst (i : Fin n) : MeasurePreserving Prod.fst (νlocal i) (μ i) :=
    measurePreserving_fst (μ := μ i) (ν := lambda01)
  have hsnd (i : Fin n) : MeasurePreserving Prod.snd (νlocal i) lambda01 :=
    measurePreserving_snd (μ := μ i) (ν := lambda01)
  have hobs (i : Fin n) :
      MeasurePreserving (fun x : (∀ j : Fin n, Ω j × ℝ) => (x i).1) ν (μ i) :=
    (hfst i).comp (heval i)
  have hunif (i : Fin n) :
      MeasurePreserving (fun x : (∀ j : Fin n, Ω j × ℝ) => (x i).2) ν lambda01 :=
    (hsnd i).comp (heval i)
  have hqmeas : Measurable q :=
    measurable_pi_iff.2 (fun i => (hobs i).measurable)
  have hUmeas : Measurable U :=
    measurable_pi_iff.2 (fun i => (hunif i).measurable)
  have hmapfst (i : Fin n) :
      (νlocal i).map (Prod.fst : Ω i × ℝ → Ω i) = μ i := (hfst i).map_eq
  have hmapsnd (i : Fin n) :
      (νlocal i).map (Prod.snd : Ω i × ℝ → ℝ) = lambda01 := (hsnd i).map_eq
  letI : ∀ i : Fin n, SigmaFinite ((νlocal i).map (Prod.fst : Ω i × ℝ → Ω i)) :=
    fun i => by rw [hmapfst i]; infer_instance
  letI : ∀ i : Fin n, SigmaFinite ((νlocal i).map (Prod.snd : Ω i × ℝ → ℝ)) :=
    fun i => by rw [hmapsnd i]; infer_instance
  have hq : MeasurePreserving q ν μ0 := by
    refine ⟨hqmeas, ?_⟩
    have h := Measure.pi_map_pi
      (μ := νlocal) (f := fun i => (Prod.fst : Ω i × ℝ → Ω i))
      (fun i => measurable_fst.aemeasurable)
    simpa only [ν, q, μ0, hmapfst] using h
  have hU : MeasurePreserving U ν Λ := by
    refine ⟨hUmeas, ?_⟩
    have h := Measure.pi_map_pi
      (μ := νlocal) (f := fun i => (Prod.snd : Ω i × ℝ → ℝ))
      (fun i => measurable_snd.aemeasurable)
    simpa only [ν, U, Λ, hmapsnd] using h
  let E : (∀ i : Fin n, Ω i × ℝ) ≃ᵐ ((∀ i : Fin n, Ω i) × (Fin n → ℝ)) :=
    { toFun := fun x => (q x, U x)
      invFun := fun z i => (z.1 i, z.2 i)
      left_inv := by intro x; rfl
      right_inv := by intro z; cases z; rfl
      measurable_toFun := hqmeas.prodMk hUmeas
      measurable_invFun := by
        apply measurable_pi_iff.2
        intro i
        exact ((measurable_pi_apply i).comp measurable_fst).prodMk
          ((measurable_pi_apply i).comp measurable_snd) }
  have hgroup :
      MeasurePreserving (fun x : (∀ i : Fin n, Ω i × ℝ) => (q x, U x)) ν
        (μ0.prod Λ) := by
    refine ⟨hqmeas.prodMk hUmeas, ?_⟩
    change (Measure.pi νlocal).map E =
      (Measure.pi μ).prod (Measure.pi (fun _ : Fin n => lambda01))
    refine (Measure.FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((Measure.FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).prod
        (Measure.FiniteSpanningSetsIn.pi
          (fun _ : Fin n => lambda01.toFiniteSpanningSetsIn))) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      · exact (Measure.FiniteSpanningSetsIn.pi
          (fun i => (μ i).toFiniteSpanningSetsIn)).isCountablySpanning
      · exact (Measure.FiniteSpanningSetsIn.pi
          (fun _ : Fin n => lambda01.toFiniteSpanningSetsIn)).isCountablySpanning
    · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
      rw [MeasurableEquiv.map_apply]
      have hpre : E ⁻¹' (Set.univ.pi s ×ˢ Set.univ.pi t) =
          Set.univ.pi (fun i => s i ×ˢ t i) := by
        ext x
        simp [E, q, U, Set.mem_pi, forall_and]
      rw [hpre]
      simp only [Measure.prod_prod, Measure.pi_pi, νlocal, Finset.prod_mul_distrib]
  have hindAug :
      iIndepFun (fun (i : Fin n) (x : ∀ j : Fin n, Ω j × ℝ) => x i) ν :=
    iIndepFun_pi (fun i => (measurable_id : Measurable (id : Ω i × ℝ → Ω i × ℝ)).aemeasurable)
  have hindU :
      iIndepFun (fun (i : Fin n) (x : ∀ j : Fin n, Ω j × ℝ) => (x i).2) ν :=
    iIndepFun_pi (fun i => (measurable_snd : Measurable (Prod.snd : Ω i × ℝ → ℝ)).aemeasurable)
  have hindqU : IndepFun q U ν := by
    apply (indepFun_iff_map_prod_eq_prod_map_map hqmeas.aemeasurable
      hUmeas.aemeasurable).2
    rw [hq.map_eq, hU.map_eq]
    exact hgroup.map_eq
  have hfullLaw (F : (∀ i : Fin n, Ω i) → ℝ) (hF : Measurable F) :
      Measure.map (fun x : (∀ i : Fin n, Ω i × ℝ) => F (q x)) ν =
        Measure.map F μ0 := by
    calc
      Measure.map (fun x : (∀ i : Fin n, Ω i × ℝ) => F (q x)) ν =
          Measure.map F (Measure.map q ν) := by
        simpa only [Function.comp_def] using (Measure.map_map hF hqmeas).symm
      _ = Measure.map F μ0 := by rw [hq.map_eq]
  have hdeletedLaw (i : Fin n)
      (d : (∀ j : {j : Fin n // j ≠ i}, Ω j.1) → ℝ) (hd : Measurable d) :
      Measure.map (fun x : (∀ j : Fin n, Ω j × ℝ) => d (fun j => (x j.1).1)) ν =
        Measure.map (fun o : (∀ j : Fin n, Ω j) => d (fun j => o j.1)) μ0 := by
    exact hfullLaw (fun o => d (fun j => o j.1))
      (hd.comp (measurable_pi_iff.2 (fun j => measurable_pi_apply j.1)))
  exact ⟨hLambda, hlocalProb, hprob, hq, hU, hgroup, heval, hobs, hunif,
    hindAug, hindU, hindqU, hfullLaw, hdeletedLaw⟩

theorem actual_finite_normalized_coding_spec
    (n : ℕ) (hn : 1 ≤ n) {Ω : Fin n → Type*}
    [mΩ : ∀ i : Fin n, MeasurableSpace (Ω i)]
    [∀ i : Fin n, MeasurableSpace.CountablyGenerated (Ω i)]
    (μ : ∀ i : Fin n, Measure (Ω i))
    [hμ : ∀ i : Fin n, IsProbabilityMeasure (μ i)]
    (g : ∀ i : Fin n, Ω i → ℝ)
    (hg : ∀ i : Fin n, Measurable (g i))
    (hg2 : ∀ i : Fin n, MemLp (g i) 2 (μ i))
    (hgmean : ∀ i : Fin n, (∫ o, g i o ∂(μ i)) = 0)
    (hgenergy : (∑ i : Fin n, ∫ o, (g i o) ^ 2 ∂(μ i)) = 1)
    (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε < 1 / (4 * Real.sqrt (n : ℝ))) :
    let lambda01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
    let νlocal : ∀ i : Fin n, Measure (Ω i × ℝ) := fun i => (μ i).prod lambda01
    let ν : Measure (∀ i : Fin n, Ω i × ℝ) := Measure.pi νlocal
    let c : ∀ i : Fin n, (Ω i × ℝ) → ℝ := fun i => Shao.OQ6.ScalarObservationCoding.baseFourIndicatorCode (MeasurableSpace.natGeneratingSequence (Ω i × ℝ))
    let ξlocal : ∀ i : Fin n, (Ω i × ℝ) → ℝ := fun i z => g i z.1
    let Ylocal : ∀ i : Fin n, (Ω i × ℝ) → ℝ := fun i => Shao.OQ6.QuantizedObservationCoding.quantizedObservation ε (ξlocal i) (c i)
    let ξ : Fin n → (∀ i : Fin n, Ω i × ℝ) → ℝ := fun i x => g i (x i).1
    let Y : Fin n → (∀ i : Fin n, Ω i × ℝ) → ℝ := fun i x => Ylocal i (x i)
    let a : Fin n → ℝ := Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν Y
    let s : ℝ := Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν Y
    let ηlocal : ∀ i : Fin n, (Ω i × ℝ) → ℝ := fun i => Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation (a i) s (Ylocal i)
    let η : Fin n → (∀ i : Fin n, Ω i × ℝ) → ℝ := Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν Y
    let Vη : (∀ i : Fin n, Ω i × ℝ) → ℝ := fun x => Real.sqrt (∑ i : Fin n, (η i x) ^ 2)
    IsProbabilityMeasure ν ∧
    (∀ i : Fin n, MeasurePreserving (fun x : (∀ j : Fin n, Ω j × ℝ) => (x i).1) ν (μ i)) ∧
    (∀ i : Fin n, Measurable (ξ i)) ∧
    (∀ i : Fin n, MemLp (ξ i) 2 ν) ∧
    (∀ i : Fin n, (∫ x, ξ i x ∂ν) = ∫ o, g i o ∂(μ i)) ∧
    (∀ i : Fin n, (∫ x, (ξ i x) ^ 2 ∂ν) = ∫ o, (g i o) ^ 2 ∂(μ i)) ∧
    (∀ i : Fin n, (∫ x, ξ i x ∂ν) = 0) ∧
    (∑ i : Fin n, ∫ x, (ξ i x) ^ 2 ∂ν) = 1 ∧
    (∀ i : Fin n, Measurable (Ylocal i)) ∧
    (∀ i : Fin n, Measurable (Y i)) ∧
    (∀ (i : Fin n) (x : ∀ j : Fin n, Ω j × ℝ), |Y i x - ξ i x| ≤ ε) ∧
    (∀ i : Fin n, MemLp (Ylocal i) 2 (νlocal i)) ∧
    (∀ i : Fin n, Integrable (Ylocal i) (νlocal i)) ∧
    (∀ i : Fin n, a i = ∫ z, Ylocal i z ∂(νlocal i)) ∧
    (∀ i : Fin n, |a i| ≤ ε) ∧
    (1 / 2 : ℝ) < s ∧
    (∀ i : Fin n, Measurable (ηlocal i)) ∧
    (∀ i : Fin n, MeasurableSpace.comap (ηlocal i) (borel ℝ) = (inferInstance : MeasurableSpace (Ω i × ℝ))) ∧
    (∀ (i : Fin n) (t : ℝ), νlocal i ({z : Ω i × ℝ | ηlocal i z = t}) = 0) ∧
    (∀ (i : Fin n) (x : ∀ j : Fin n, Ω j × ℝ), η i x = ηlocal i (x i)) ∧
    iIndepFun η ν ∧
    (∀ i : Fin n, Measurable (η i)) ∧
    (∀ i : Fin n, MemLp (η i) 2 ν) ∧
    (∀ i : Fin n, Integrable (η i) ν) ∧
    (∀ i : Fin n, Integrable (fun x => (η i x) ^ 2) ν) ∧
    (∀ i : Fin n, (∫ x, η i x ∂ν) = 0) ∧
    (∑ i : Fin n, ∫ x, (η i x) ^ 2 ∂ν) = 1 ∧
    (∀ (i : Fin n) (t : ℝ), ν ({x : (∀ j : Fin n, Ω j × ℝ) | η i x = t}) = 0) ∧
    ν ({x : (∀ j : Fin n, Ω j × ℝ) | Vη x = 0}) = 0 ∧
    (∀ᵐ x ∂ν, 0 < Vη x) := by
  classical
  dsimp only
  let lambda01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
  let νlocal : ∀ i : Fin n, Measure (Ω i × ℝ) := fun i => (μ i).prod lambda01
  let ν : Measure (∀ i : Fin n, Ω i × ℝ) := Measure.pi νlocal
  let c : ∀ i : Fin n, (Ω i × ℝ) → ℝ := fun i =>
    Shao.OQ6.ScalarObservationCoding.baseFourIndicatorCode
      (MeasurableSpace.natGeneratingSequence (Ω i × ℝ))
  let ξlocal : ∀ i : Fin n, (Ω i × ℝ) → ℝ := fun i z => g i z.1
  let Ylocal : ∀ i : Fin n, (Ω i × ℝ) → ℝ := fun i =>
    Shao.OQ6.QuantizedObservationCoding.quantizedObservation ε (ξlocal i) (c i)
  let ξ : Fin n → (∀ i : Fin n, Ω i × ℝ) → ℝ := fun i x => g i (x i).1
  let Y : Fin n → (∀ i : Fin n, Ω i × ℝ) → ℝ := fun i x => Ylocal i (x i)
  let a : Fin n → ℝ := Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν Y
  let s : ℝ := Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν Y
  let ηlocal : ∀ i : Fin n, (Ω i × ℝ) → ℝ := fun i =>
    Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation (a i) s (Ylocal i)
  let η : Fin n → (∀ i : Fin n, Ω i × ℝ) → ℝ :=
    Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν Y
  let Vη : (∀ i : Fin n, Ω i × ℝ) → ℝ := fun x =>
    Real.sqrt (∑ i : Fin n, (η i x) ^ 2)
  rcases finite_uniform_augmentation_spec μ with
    ⟨hLambda, hlocalProb, hprob, hq, hU, hgroup, heval, hobs, hunif,
      hindAug, hindU, hindqU, hfullLaw, hdeletedLaw⟩
  letI : IsProbabilityMeasure lambda01 := hLambda
  letI : ∀ i : Fin n, IsProbabilityMeasure (νlocal i) := hlocalProb
  letI : IsProbabilityMeasure ν := hprob
  have hξmeas (i : Fin n) : Measurable (ξ i) :=
    (hg i).comp (hobs i).measurable
  have hξ2 (i : Fin n) : MemLp (ξ i) 2 ν :=
    (hg2 i).comp_measurePreserving (hobs i)
  have hgInt (i : Fin n) : Integrable (g i) (μ i) :=
    MemLp.integrable (by norm_num) (hg2 i)
  have hgSqInt (i : Fin n) : Integrable (fun o => (g i o) ^ 2) (μ i) :=
    (hg2 i).integrable_sq
  have hξInt (i : Fin n) : Integrable (ξ i) ν :=
    MemLp.integrable (by norm_num) (hξ2 i)
  have hξSqInt (i : Fin n) : Integrable (fun x => (ξ i x) ^ 2) ν :=
    (hξ2 i).integrable_sq
  have hξFirst (i : Fin n) : (∫ x, ξ i x ∂ν) = ∫ o, g i o ∂(μ i) := by
    have hm : AEStronglyMeasurable (g i)
        (ν.map (fun x : (∀ j : Fin n, Ω j × ℝ) => (x i).1)) := by
      rw [(hobs i).map_eq]
      exact (hgInt i).aestronglyMeasurable
    have hi := integral_map (hobs i).aemeasurable hm
    rw [(hobs i).map_eq] at hi
    exact hi.symm
  have hξSecond (i : Fin n) :
      (∫ x, (ξ i x) ^ 2 ∂ν) = ∫ o, (g i o) ^ 2 ∂(μ i) := by
    have hm : AEStronglyMeasurable (fun o : Ω i => (g i o) ^ 2)
        (ν.map (fun x : (∀ j : Fin n, Ω j × ℝ) => (x i).1)) := by
      rw [(hobs i).map_eq]
      exact (hgSqInt i).aestronglyMeasurable
    have hi := integral_map (hobs i).aemeasurable hm
    rw [(hobs i).map_eq] at hi
    exact hi.symm
  have hξmean (i : Fin n) : (∫ x, ξ i x ∂ν) = 0 := by
    rw [hξFirst i, hgmean i]
  have hξenergy : (∑ i : Fin n, ∫ x, (ξ i x) ^ 2 ∂ν) = 1 := by
    calc
      (∑ i : Fin n, ∫ x, (ξ i x) ^ 2 ∂ν) =
          ∑ i : Fin n, ∫ o, (g i o) ^ 2 ∂(μ i) :=
        Finset.sum_congr rfl (fun i _ => hξSecond i)
      _ = 1 := hgenergy
  have hcode (i : Fin n) :
      Measurable (c i) ∧
      (∀ z : Ω i × ℝ, (1 / 3 : ℝ) ≤ c i z ∧ c i z ≤ (2 / 3 : ℝ)) ∧
      MeasurableSpace.comap (c i) (borel ℝ) =
        (inferInstance : MeasurableSpace (Ω i × ℝ)) ∧
      (∀ t : ℝ, νlocal i ({z : Ω i × ℝ | c i z = t}) = 0) := by
    rcases Shao.OQ6.ScalarObservationCoding.countable_uniform_augmented_base_four_code
        (μ i) with
      ⟨_, _, _, hrange, hmeas, _, _, hcomap, _, hnull⟩
    exact ⟨hmeas, hrange, hcomap, hnull⟩
  have hYdata (i : Fin n) :
      Measurable (Ylocal i) ∧
      (∀ z : Ω i × ℝ, |Ylocal i z - ξlocal i z| ≤ ε) ∧
      MeasurableSpace.comap (Ylocal i) (borel ℝ) =
        (inferInstance : MeasurableSpace (Ω i × ℝ)) ∧
      (∀ t : ℝ, νlocal i ({z : Ω i × ℝ | Ylocal i z = t}) = 0) := by
    rcases Shao.OQ6.QuantizedObservationCoding.quantized_observation_spec
        (ξlocal i) (c i) ((hg i).comp measurable_fst)
        (hcode i).1 (hcode i).2.1 (hcode i).2.2.1 ε hε with
      ⟨hYmeas, _, herr, _, _, hcomap, hnull⟩
    exact ⟨hYmeas, herr, hcomap, hnull (νlocal i) (hcode i).2.2.2⟩
  have hYmeas (i : Fin n) : Measurable (Y i) :=
    (hYdata i).1.comp (heval i).measurable
  have herr (i : Fin n) (x : ∀ j : Fin n, Ω j × ℝ) :
      |Y i x - ξ i x| ≤ ε :=
    (hYdata i).2.1 (x i)
  rcases Shao.OQ6.ActualMomentNormalization.actual_centering_and_scale_spec
      ν n hn ξ Y hξmeas hξ2 hξmean hξenergy hYmeas ε hε.le herr with
    ⟨hY2, hYInt, hYSqInt, hZmeas, hZ2, hZInt, hZSqInt,
      hameanBound, hZerr, hZmean, hssq, hsclose⟩
  rcases Shao.OQ6.ActualMomentNormalization.actual_moment_normalization_spec
      ν n hn ξ Y hξmeas hξ2 hξmean hξenergy hYmeas ε hε hεsmall herr with
    ⟨hs, hηmeas, hη2, hηInt, hηSqInt, hηmean, hηenergy,
      hreconstruct, hvectorError, hVError, hWError, hηcap, hηcoordError⟩
  have hYlocal2 (i : Fin n) : MemLp (Ylocal i) 2 (νlocal i) := by
    have hm : AEStronglyMeasurable (Ylocal i) (ν.map (Function.eval i)) := by
      rw [(heval i).map_eq]
      exact (hYdata i).1.aestronglyMeasurable
    have hm2 : MemLp (Ylocal i) 2 (ν.map (Function.eval i)) :=
      (memLp_map_measure_iff (p := 2) hm (heval i).aemeasurable).2 (hY2 i)
    exact Eq.mp
      (congrArg (fun ρ : Measure (Ω i × ℝ) => MemLp (Ylocal i) 2 ρ)
        (heval i).map_eq) hm2
  have hYlocalInt (i : Fin n) : Integrable (Ylocal i) (νlocal i) :=
    MemLp.integrable (by norm_num) (hYlocal2 i)
  have hameanLocal (i : Fin n) : a i = ∫ z, Ylocal i z ∂(νlocal i) := by
    have hm : AEStronglyMeasurable (Ylocal i) (ν.map (Function.eval i)) := by
      rw [(heval i).map_eq]
      exact (hYlocalInt i).aestronglyMeasurable
    have hi := integral_map (heval i).aemeasurable hm
    rw [(heval i).map_eq] at hi
    exact hi.symm
  have hspos : 0 < s := lt_trans (by norm_num) hs
  have hηdata (i : Fin n) :
      Measurable (ηlocal i) ∧
      MeasurableSpace.comap (ηlocal i) (borel ℝ) =
        (inferInstance : MeasurableSpace (Ω i × ℝ)) ∧
      (∀ t : ℝ, νlocal i ({z : Ω i × ℝ | ηlocal i z = t}) = 0) := by
    rcases Shao.OQ6.QuantizedObservationCoding.deterministic_affine_observation_spec
        (Ylocal i) (hYdata i).1 (hYdata i).2.2.1 (a i) s hspos with
      ⟨hmeas, _, _, hcomap, hnull⟩
    exact ⟨hmeas, hcomap, hnull (νlocal i) (hYdata i).2.2.2⟩
  have hηeval (i : Fin n) (x : ∀ j : Fin n, Ω j × ℝ) :
      η i x = ηlocal i (x i) := rfl
  have hηindep : iIndepFun η ν := by
    have hfamily : η = (fun (i : Fin n) (x : ∀ j : Fin n, Ω j × ℝ) => ηlocal i (x i)) :=
      funext (fun i => funext (hηeval i))
    have hlocalIndep :
        iIndepFun (fun (i : Fin n) (x : ∀ j : Fin n, Ω j × ℝ) => ηlocal i (x i)) ν :=
      iIndepFun_pi (μ := νlocal) (X := ηlocal)
        (fun i => (hηdata i).1.aemeasurable)
    exact Eq.mpr
      (congrArg (fun F : Fin n → (∀ j : Fin n, Ω j × ℝ) → ℝ => iIndepFun F ν) hfamily)
      hlocalIndep
  have hηnull (i : Fin n) (t : ℝ) :
      ν ({x : (∀ j : Fin n, Ω j × ℝ) | η i x = t}) = 0 := by
    have hlevel : {x : (∀ j : Fin n, Ω j × ℝ) | η i x = t} =
        Function.eval i ⁻¹' {z : Ω i × ℝ | ηlocal i z = t} := by
      ext x
      constructor
      · intro hx
        exact (hηeval i x).symm.trans hx
      · intro hx
        exact (hηeval i x).trans hx
    have hlocalNull :
        ν (Function.eval i ⁻¹' {z : Ω i × ℝ | ηlocal i z = t}) = 0 :=
      Measure.pi_eval_preimage_null νlocal ((hηdata i).2.2 t)
    exact Eq.mpr
      (congrArg (fun A : Set (∀ j : Fin n, Ω j × ℝ) => ν A = 0) hlevel)
      hlocalNull
  let i0 : Fin n := ⟨0, lt_of_lt_of_le Nat.zero_lt_one hn⟩
  have hzeroSubset :
      {x : (∀ j : Fin n, Ω j × ℝ) | Vη x = 0} ⊆
        {x : (∀ j : Fin n, Ω j × ℝ) | η i0 x = 0} := by
    intro x hx
    have hsumNonneg : 0 ≤ ∑ i : Fin n, (η i x) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg (η i x))
    change Real.sqrt (∑ i : Fin n, (η i x) ^ 2) = 0 at hx
    have hsumZero : (∑ i : Fin n, (η i x) ^ 2) = 0 := by
      nlinarith only [Real.sq_sqrt hsumNonneg, hx]
    have hterm : (η i0 x) ^ 2 ≤ ∑ i : Fin n, (η i x) ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (η i x)) (Finset.mem_univ i0)
    have hsq : (η i0 x) ^ 2 = 0 :=
      le_antisymm (by simpa only [hsumZero] using hterm) (sq_nonneg (η i0 x))
    exact sq_eq_zero_iff.mp hsq
  have hVnull : ν ({x : (∀ j : Fin n, Ω j × ℝ) | Vη x = 0}) = 0 :=
    measure_mono_null hzeroSubset (hηnull i0 0)
  have hVpos : ∀ᵐ x ∂ν, 0 < Vη x := by
    have hne : ∀ᵐ x ∂ν, Vη x ≠ 0 := by
      rw [ae_iff]
      simpa only [not_not] using hVnull
    filter_upwards [hne] with x hx
    exact lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hx)
  exact ⟨hprob, hobs, hξmeas, hξ2, hξFirst, hξSecond, hξmean, hξenergy,
    fun i => (hYdata i).1, hYmeas, herr, hYlocal2, hYlocalInt, hameanLocal,
    hameanBound, hs, fun i => (hηdata i).1, fun i => (hηdata i).2.1,
    fun i => (hηdata i).2.2, hηeval, hηindep, hηmeas, hη2, hηInt,
    hηSqInt, hηmean, hηenergy, hηnull, hVnull, hVpos⟩

end

end Shao.OQ6.FiniteUniformCodingAssembly
