import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.MeasureTheory.Function.LpSeminorm.Trim
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

set_option autoImplicit false

universe u v

namespace Shao.OQ6.OriginalKernelObservableTransport

noncomputable section

open MeasureTheory
open scoped MeasureTheory ENNReal

theorem actual_normalized_kernel_observable_trim_transport
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    {J : Type v} [Fintype J]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (m₀ : MeasurableSpace Ω) (hm₀ : m₀ ≤ mΩ)
    (hh₀ : Measurable[m₀.prod m₀, borel ℝ]
      (fun t : Ω × Ω => h t.1 t.2)) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ :=
      ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω mΩ mΩ μ μ)
    let rho : ℝ := Real.sqrt v
    let rowIntegrable : Ω → Prop := fun o => Integrable (h o) μ
    let gLp : ℝ≥0∞ → Prop := fun p => MemLp g p μ
    let projectionLaw : Measure ℝ :=
      @Measure.map Ω ℝ mΩ (borel ℝ) g μ
    let pairLaw : @Measure (Ω × Ω) (mΩ.prod mΩ) :=
      @Measure.prod Ω Ω mΩ mΩ μ μ
    let mJ : MeasurableSpace (J → Ω) :=
      @MeasurableSpace.pi J (fun _ : J => Ω) (fun _ : J => mΩ)
    let mJ₀ : MeasurableSpace (J → Ω) :=
      @MeasurableSpace.pi J (fun _ : J => Ω) (fun _ : J => m₀)
    let P : @Measure (J → Ω) mJ :=
      @Measure.pi J (fun _ : J => Ω) (inferInstance : Fintype J)
        (fun _ : J => mΩ) (fun _ : J => μ)
    let μ₀ : @Measure Ω m₀ := μ.trim hm₀
    letI : MeasurableSpace Ω := m₀
    let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
    let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
    let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(μ₀.prod μ₀)
    let rho₀ : ℝ := Real.sqrt v₀
    let P₀ : @Measure (J → Ω) mJ₀ := Measure.pi (fun _ : J => μ₀)
    IsProbabilityMeasure μ₀ ∧
      (∀ o : Ω, g₀ o = g o) ∧
      (∀ o y : Ω, r₀ o y = r o y) ∧
      (∀ o : Ω, Integrable (h o) μ₀ ↔ rowIntegrable o) ∧
      MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ₀.prod μ₀) ∧
      (∫ t : Ω × Ω, h t.1 t.2 ∂(μ₀.prod μ₀)) = 0 ∧
      Measurable g₀ ∧ MemLp g₀ 2 μ₀ ∧
      (∫ o, g₀ o ∂μ₀) = 0 ∧
      (∫ o, g₀ o ^ 2 ∂μ₀) = 1 ∧
      Measurable (fun t : Ω × Ω => r₀ t.1 t.2) ∧
      MemLp (fun t : Ω × Ω => r₀ t.1 t.2) 2 (μ₀.prod μ₀) ∧
      (∀ o y : Ω, r₀ o y = r₀ y o) ∧
      (∀ᵐ o ∂μ₀, (∫ y, r₀ o y ∂μ₀) = 0) ∧
      v₀ = v ∧ rho₀ = rho ∧
      μ₀.map g₀ = projectionLaw ∧
      (∀ p : ℝ≥0∞, MemLp g₀ p μ₀ ↔ gLp p) ∧
      μ₀.prod μ₀ =
        @Measure.map (Ω × Ω) (Ω × Ω)
          (mΩ.prod mΩ) (m₀.prod m₀) id pairLaw ∧
      IsProbabilityMeasure P₀ ∧
      P₀ = @Measure.map (J → Ω) (J → Ω) mJ mJ₀ id P ∧
      (∀ T : (J → Ω) → ℝ,
        Measurable[mJ₀, borel ℝ] T →
          P₀.map T = @Measure.map (J → Ω) ℝ mJ (borel ℝ) T P)
:= by
  classical
  dsimp only
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let v : ℝ :=
    ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω mΩ mΩ μ μ)
  let rho : ℝ := Real.sqrt v
  let rowIntegrable : Ω → Prop := fun o => Integrable (h o) μ
  let gLp : ℝ≥0∞ → Prop := fun p => MemLp g p μ
  let projectionLaw : Measure ℝ :=
    @Measure.map Ω ℝ mΩ (borel ℝ) g μ
  let pairLaw : @Measure (Ω × Ω) (mΩ.prod mΩ) :=
    @Measure.prod Ω Ω mΩ mΩ μ μ
  let mJ : MeasurableSpace (J → Ω) :=
    @MeasurableSpace.pi J (fun _ : J => Ω) (fun _ : J => mΩ)
  let mJ₀ : MeasurableSpace (J → Ω) :=
    @MeasurableSpace.pi J (fun _ : J => Ω) (fun _ : J => m₀)
  let P : @Measure (J → Ω) mJ :=
    @Measure.pi J (fun _ : J => Ω) (inferInstance : Fintype J)
      (fun _ : J => mΩ) (fun _ : J => μ)
  let μ₀ : @Measure Ω m₀ := μ.trim hm₀
  have hOriginalSecond : (∫ o, g o ^ 2 ∂μ) = 1 := hprojectionsecond
  have hid : Measurable[mΩ, m₀] (id : Ω → Ω) :=
    measurable_id'' hm₀
  have hμmap : μ₀ = @Measure.map Ω Ω mΩ m₀ id μ :=
    trim_eq_map (μ := μ) hm₀
  have hμ₀prob : @IsProbabilityMeasure Ω m₀ μ₀ := by
    constructor
    change μ.trim hm₀ Set.univ = 1
    rw [trim_measurableSet_eq hm₀ (@MeasurableSet.univ Ω m₀)]
    exact measure_univ
  let : MeasurableSpace Ω := m₀
  let reducedProbability : IsProbabilityMeasure μ₀ := hμ₀prob
  let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
  let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
  let v₀ : ℝ := ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(μ₀.prod μ₀)
  let rho₀ : ℝ := Real.sqrt v₀
  let P₀ : @Measure (J → Ω) mJ₀ := Measure.pi (fun _ : J => μ₀)
  change IsProbabilityMeasure μ₀ ∧
    (∀ o : Ω, g₀ o = g o) ∧
    (∀ o y : Ω, r₀ o y = r o y) ∧
    (∀ o : Ω, Integrable (h o) μ₀ ↔ rowIntegrable o) ∧
    MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ₀.prod μ₀) ∧
    (∫ t : Ω × Ω, h t.1 t.2 ∂(μ₀.prod μ₀)) = 0 ∧
    Measurable g₀ ∧ MemLp g₀ 2 μ₀ ∧
    (∫ o, g₀ o ∂μ₀) = 0 ∧
    (∫ o, g₀ o ^ 2 ∂μ₀) = 1 ∧
    Measurable (fun t : Ω × Ω => r₀ t.1 t.2) ∧
    MemLp (fun t : Ω × Ω => r₀ t.1 t.2) 2 (μ₀.prod μ₀) ∧
    (∀ o y : Ω, r₀ o y = r₀ y o) ∧
    (∀ᵐ o ∂μ₀, (∫ y, r₀ o y ∂μ₀) = 0) ∧
    v₀ = v ∧ rho₀ = rho ∧
    μ₀.map g₀ = projectionLaw ∧
    (∀ p : ℝ≥0∞, MemLp g₀ p μ₀ ↔ gLp p) ∧
    μ₀.prod μ₀ =
      @Measure.map (Ω × Ω) (Ω × Ω)
        (mΩ.prod mΩ) (m₀.prod m₀) id pairLaw ∧
    IsProbabilityMeasure P₀ ∧
    P₀ = @Measure.map (J → Ω) (J → Ω) mJ mJ₀ id P ∧
    (∀ T : (J → Ω) → ℝ,
      Measurable[mJ₀, borel ℝ] T →
        P₀.map T = @Measure.map (J → Ω) ℝ mJ (borel ℝ) T P)

  have hrowMeasurable : ∀ o : Ω, Measurable (h o) := by
    intro o
    exact hh₀.comp measurable_prodMk_left
  have hgPointwise : ∀ o : Ω, g₀ o = g o := by
    intro o
    exact (integral_trim (μ := μ) hm₀
      (hrowMeasurable o).stronglyMeasurable).symm
  have hgFunction : g₀ = g := funext hgPointwise
  have hrPointwise : ∀ o y : Ω, r₀ o y = r o y := by
    intro o y
    dsimp only [r₀, r]
    rw [hgPointwise o, hgPointwise y]
  have hrowIntegrable : ∀ o : Ω,
      Integrable (h o) μ₀ ↔ rowIntegrable o := by
    intro o
    constructor
    · intro ho
      exact integrable_of_integrable_trim hm₀ ho
    · intro ho
      exact ho.trim hm₀ (hrowMeasurable o).stronglyMeasurable

  have hidPair :
      Measurable[mΩ.prod mΩ, m₀.prod m₀] (id : Ω × Ω → Ω × Ω) := by
    exact (hid.comp (@measurable_fst Ω Ω mΩ mΩ)).prodMk
      (hid.comp (@measurable_snd Ω Ω mΩ mΩ))
  have hPair :
      μ₀.prod μ₀ =
        @Measure.map (Ω × Ω) (Ω × Ω)
          (mΩ.prod mΩ) (m₀.prod m₀) id pairLaw := by
    change μ₀.prod μ₀ =
      @Measure.map (Ω × Ω) (Ω × Ω)
        (mΩ.prod mΩ) (m₀.prod m₀)
        (Prod.map (id : Ω → Ω) (id : Ω → Ω)) pairLaw
    rw [hμmap]
    exact @Measure.map_prod_map Ω Ω Ω mΩ m₀ mΩ Ω m₀
      (id : Ω → Ω) (id : Ω → Ω) μ μ
      (inferInstance : @SFinite Ω mΩ μ) hid hid
  have hh₂₀ :
      MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ₀.prod μ₀) := by
    rw [hPair]
    exact (memLp_map_measure_iff
      hh₀.stronglyMeasurable.aestronglyMeasurable
      hidPair.aemeasurable).2 hh2
  have hcenter₀ :
      (∫ t : Ω × Ω, h t.1 t.2 ∂(μ₀.prod μ₀)) = 0 := by
    rw [hPair, integral_map_of_stronglyMeasurable
      hidPair hh₀.stronglyMeasurable]
    exact hcenter
  have hgMeasurable : Measurable g₀ :=
    hh₀.stronglyMeasurable.integral_prod_right'.measurable
  have hgSecond : (∫ o, g₀ o ^ 2 ∂μ₀) = 1 := by
    calc
      (∫ o, g₀ o ^ 2 ∂μ₀) = ∫ o, g₀ o ^ 2 ∂μ :=
        (integral_trim (μ := μ) hm₀
          (hgMeasurable.pow_const 2).stronglyMeasurable).symm
      _ = ∫ o, g o ^ 2 ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall
          (fun o => congrArg (fun t : ℝ => t ^ 2) (hgPointwise o))
      _ = 1 := hOriginalSecond
  have hgSquareIntegrable : Integrable (fun o => g₀ o ^ 2) μ₀ := by
    by_contra hnot
    have hzero : (∫ o, g₀ o ^ 2 ∂μ₀) = 0 := integral_undef hnot
    exact one_ne_zero (hgSecond.symm.trans hzero)
  have hg₂₀ : MemLp g₀ 2 μ₀ :=
    (memLp_two_iff_integrable_sq hgMeasurable.aestronglyMeasurable).2
      hgSquareIntegrable
  have hhIntegrable : Integrable (fun t : Ω × Ω => h t.1 t.2)
      (μ₀.prod μ₀) := hh₂₀.integrable one_le_two
  have hgIntegrable : Integrable g₀ μ₀ := hg₂₀.integrable one_le_two
  have hgMean : (∫ o, g₀ o ∂μ₀) = 0 := by
    calc
      (∫ o, g₀ o ∂μ₀) =
          ∫ t : Ω × Ω, h t.1 t.2 ∂(μ₀.prod μ₀) :=
        integral_integral hhIntegrable
      _ = 0 := hcenter₀

  have hrMeasurable : Measurable (fun t : Ω × Ω => r₀ t.1 t.2) :=
    (hh₀.sub (hgMeasurable.comp measurable_fst)).sub
      (hgMeasurable.comp measurable_snd)
  have hr₂₀ :
      MemLp (fun t : Ω × Ω => r₀ t.1 t.2) 2 (μ₀.prod μ₀) := by
    exact (hh₂₀.sub
      (hg₂₀.comp_measurePreserving
        (measurePreserving_fst (μ := μ₀) (ν := μ₀)))).sub
      (hg₂₀.comp_measurePreserving
        (measurePreserving_snd (μ := μ₀) (ν := μ₀)))
  have hrSymmetric : ∀ o y : Ω, r₀ o y = r₀ y o := by
    intro o y
    dsimp only [r₀]
    rw [hhsymm o y]
    exact sub_right_comm _ _ _
  have hrCanonical :
      ∀ᵐ o ∂μ₀, (∫ y, r₀ o y ∂μ₀) = 0 := by
    filter_upwards [hhIntegrable.prod_right_ae] with o ho
    have hconst : Integrable (fun _ : Ω => g₀ o) μ₀ := integrable_const _
    change (∫ y, h o y - g₀ o - g₀ y ∂μ₀) = 0
    have hsub : Integrable (fun y : Ω => h o y - g₀ o) μ₀ :=
      ho.sub hconst
    calc
      (∫ y, h o y - g₀ o - g₀ y ∂μ₀) =
          (∫ y, h o y - g₀ o ∂μ₀) - ∫ y, g₀ y ∂μ₀ :=
        integral_sub hsub hgIntegrable
      _ = 0 := by
        rw [integral_sub ho hconst, integral_const, probReal_univ,
          one_smul, hgMean]
        change g₀ o - g₀ o - 0 = 0
        simp
  have hv : v₀ = v := by
    dsimp only [v₀, v]
    rw [hPair, integral_map_of_stronglyMeasurable
      hidPair (hrMeasurable.pow_const 2).stronglyMeasurable]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall
      (fun t => congrArg (fun z : ℝ => z ^ 2) (hrPointwise t.1 t.2))
  have hrho : rho₀ = rho := congrArg Real.sqrt hv
  have hgLaw : μ₀.map g₀ = projectionLaw := by
    rw [hμmap, Measure.map_map hgMeasurable hid]
    apply Measure.map_congr
    exact Filter.Eventually.of_forall hgPointwise
  have hgLpEquiv : ∀ p : ℝ≥0∞, MemLp g₀ p μ₀ ↔ gLp p := by
    intro p
    constructor
    · intro hp
      have hpOld : MemLp g₀ p μ := memLp_of_memLp_trim hm₀ hp
      simpa only [gLp, hgFunction] using hpOld
    · intro hp
      have hpOld : MemLp g₀ p μ := by
        simpa only [gLp, hgFunction] using hp
      exact (le_of_eq (eLpNorm_trim (μ := μ) (p := p) hm₀
        hgMeasurable.stronglyMeasurable)).trans_lt hpOld

  have hP₀prob : IsProbabilityMeasure P₀ := by
    dsimp only [P₀]
    infer_instance
  have hidJ : Measurable[mJ, mJ₀] (id : (J → Ω) → J → Ω) := by
    apply (@measurable_pi_iff (J → Ω) J (fun _ : J => Ω)
      mJ (fun _ : J => m₀) (id : (J → Ω) → J → Ω)).2
    intro j
    exact hid.comp
      (@measurable_pi_apply J (fun _ : J => Ω) (fun _ : J => mΩ) j)
  let mappedSigmaFinite :
      ∀ _ : J, SigmaFinite (@Measure.map Ω Ω mΩ m₀ id μ) :=
    fun _ => by
      rw [← hμmap]
      infer_instance
  have hPiRaw :
      @Measure.map (J → Ω) (J → Ω) mJ mJ₀
        (fun ξ j => (id : Ω → Ω) (ξ j)) P =
      Measure.pi (fun _ : J => @Measure.map Ω Ω mΩ m₀ id μ) := by
    exact Measure.pi_map_pi (mX := fun _ : J => mΩ)
      (μ := fun _ : J => μ) (f := fun _ : J => (id : Ω → Ω))
      (fun _ : J => hid.aemeasurable)
  have hSample :
      P₀ = @Measure.map (J → Ω) (J → Ω) mJ mJ₀ id P := by
    calc
      P₀ = Measure.pi (fun _ : J => @Measure.map Ω Ω mΩ m₀ id μ) := by
        simp only [P₀, hμmap]
      _ = @Measure.map (J → Ω) (J → Ω) mJ mJ₀ id P := hPiRaw.symm
  have hStatisticLaw : ∀ T : (J → Ω) → ℝ,
      Measurable[mJ₀, borel ℝ] T →
        P₀.map T = @Measure.map (J → Ω) ℝ mJ (borel ℝ) T P := by
    intro T hT
    rw [hSample, Measure.map_map hT hidJ]
    rfl

  exact ⟨hμ₀prob, hgPointwise, hrPointwise, hrowIntegrable, hh₂₀,
    hcenter₀, hgMeasurable, hg₂₀, hgMean, hgSecond, hrMeasurable, hr₂₀,
    hrSymmetric, hrCanonical, hv, hrho, hgLaw, hgLpEquiv, hPair,
    hP₀prob, hSample, hStatisticLaw⟩

end

end Shao.OQ6.OriginalKernelObservableTransport
