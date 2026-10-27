import Shao.OQ6.KernelObservableReduction
import Shao.OQ6.OriginalKernelObservableTransport
import Shao.OQ6.OriginalClippedStatisticMeasurable

set_option autoImplicit false

universe u v w

open MeasureTheory
open scoped BigOperators MeasureTheory ENNReal
open Shao.OQ5.P51

namespace Shao.OQ6.OriginalCountablyGeneratedModel

noncomputable section

theorem actual_normalized_original_countably_generated_model
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1) :
    let f : ℕ → Ω → ℝ := fun (_k : ℕ) (_o : Ω) => (0 : ℝ)
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
    ∃ (m₀ : MeasurableSpace Ω) (hm₀ : m₀ ≤ mΩ),
      @MeasurableSpace.CountablyGenerated Ω m₀ ∧
      Measurable[m₀.prod m₀, borel ℝ]
        (fun t : Ω × Ω => h t.1 t.2) ∧
      (∀ k : ℕ, Measurable[m₀, borel ℝ] (f k)) ∧
      let μ₀ : @Measure Ω m₀ := μ.trim hm₀
      letI : MeasurableSpace Ω := m₀
      let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
      let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
      let v₀ : ℝ :=
        ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
      let rho₀ : ℝ := Real.sqrt v₀
      IsProbabilityMeasure μ₀ ∧
      μ₀ = @Measure.map Ω Ω mΩ m₀ id μ ∧
      g₀ = g ∧ r₀ = r ∧ v₀ = v ∧ rho₀ = rho ∧
      (∀ o : Ω, Integrable (h o) μ₀ ↔ rowIntegrable o) ∧
      MemLp (fun t : Ω × Ω => h t.1 t.2) 2
        (@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀) ∧
      (∫ t : Ω × Ω, h t.1 t.2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)) = 0 ∧
      Measurable g₀ ∧ MemLp g₀ 2 μ₀ ∧
      (∫ o, g₀ o ∂μ₀) = 0 ∧ (∫ o, g₀ o ^ 2 ∂μ₀) = 1 ∧
      Measurable (fun t : Ω × Ω => r₀ t.1 t.2) ∧
      MemLp (fun t : Ω × Ω => r₀ t.1 t.2) 2
        (@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀) ∧
      (∀ o y : Ω, r₀ o y = r₀ y o) ∧
      (∀ᵐ o ∂μ₀, (∫ y, r₀ o y ∂μ₀) = 0) ∧
      @Measure.map Ω ℝ m₀ (borel ℝ) g₀ μ₀ = projectionLaw ∧
      (∀ p : ℝ≥0∞, MemLp g₀ p μ₀ ↔ gLp p) ∧
      @Measure.prod Ω Ω m₀ m₀ μ₀ μ₀ =
        @Measure.map (Ω × Ω) (Ω × Ω)
          (mΩ.prod mΩ) (m₀.prod m₀) id pairLaw ∧
      (∀ (J : Type v) (instJ : Fintype J),
        let mJ : MeasurableSpace (J → Ω) :=
          @MeasurableSpace.pi J (fun _ : J => Ω) (fun _ : J => mΩ)
        let mJ₀ : MeasurableSpace (J → Ω) :=
          @MeasurableSpace.pi J (fun _ : J => Ω) (fun _ : J => m₀)
        let P : @Measure (J → Ω) mJ :=
          @Measure.pi J (fun _ : J => Ω) instJ
            (fun _ : J => mΩ) (fun _ : J => μ)
        let P₀ : @Measure (J → Ω) mJ₀ :=
          @Measure.pi J (fun _ : J => Ω) instJ
            (fun _ : J => m₀) (fun _ : J => μ₀)
        @IsProbabilityMeasure (J → Ω) mJ₀ P₀ ∧
        Measurable[mJ, mJ₀] (id : (J → Ω) → J → Ω) ∧
        P₀ = @Measure.map (J → Ω) (J → Ω) mJ mJ₀ id P ∧
        ∀ (B : Type w) (mB : MeasurableSpace B) (T : (J → Ω) → B),
          Measurable[mJ₀, mB] T →
          @Measure.map (J → Ω) B mJ₀ mB T P₀ =
            @Measure.map (J → Ω) B mJ mB T P) ∧
      (∀ (n : ℕ) (hn : 4 ≤ n)
          (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1)
          (C0 : ℝ) (hC0 : 0 ≤ C0),
        let mN : MeasurableSpace (Fin n → Ω) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => mΩ)
        let mN₀ : MeasurableSpace (Fin n → Ω) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => m₀)
        let P : @Measure (Fin n → Ω) mN :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => mΩ) (fun _ : Fin n => μ)
        let P₀ : @Measure (Fin n → Ω) mN₀ :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => m₀) (fun _ : Fin n => μ₀)
        let N : ℝ := Real.sqrt (n : ℝ)
        let W : (Fin n → Ω) → ℝ := projectionW n g
        let V : (Fin n → Ω) → ℝ := projectionV n g
        let D : (Fin n → Ω) → ℝ := residualStatisticD n r
        let J : (Fin n → Ω) → ℝ := residualEnergyJ n r
        let Ddel : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
        let Jdel : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
        let A : (Fin n → Ω) → ℝ := fun ξ => |D ξ|
        let Adel : (Fin n → Ω) → Fin n → ℝ := fun ξ i => |Ddel ξ i|
        let B1 : (Fin n → Ω) → ℝ := studentizerClipBudget n r C0 rho 1
        let B1del : (Fin n → Ω) → Fin n → ℝ := studentizerClipBudgetDeleted n r C0 rho 1
        let s2 : (Fin n → Ω) → ℝ := centeredSq n g r
        let s : (Fin n → Ω) → ℝ := fun ξ => Real.sqrt (s2 ξ)
        let d : (Fin n → Ω) → ℝ := centeredDelta n g r
        let e : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r C0 rho 1
        let Tclip : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r C0 rho 1
        let Tactual : (Fin n → Ω) → ℝ :=
          fun ξ => @ite ℝ (s ξ = 0) (Classical.propDecidable (s ξ = 0))
            0 ((W ξ + D ξ) / s ξ)
        let cap : (Fin n → Ω) → Fin n → ℝ :=
          fun ξ i => min (|g (ξ i)| / N) (1 / (1 + z))
        let deletedTest : (Fin n → Ω) → Fin n → ℝ :=
          fun ξ i => cap ξ i * (|A ξ - Adel ξ i| + z * |B1 ξ - B1del ξ i|)
        Measurable[mN₀, borel ℝ] W ∧ Measurable[mN₀, borel ℝ] V ∧
        Measurable[mN₀, borel ℝ] D ∧ Measurable[mN₀, borel ℝ] J ∧
        Measurable[mN₀, borel ℝ] A ∧ Measurable[mN₀, borel ℝ] B1 ∧
        Measurable[mN₀, borel ℝ] s2 ∧ Measurable[mN₀, borel ℝ] s ∧
        Measurable[mN₀, borel ℝ] d ∧ Measurable[mN₀, borel ℝ] e ∧
        Measurable[mN₀, borel ℝ] Tclip ∧ Measurable[mN₀, borel ℝ] Tactual ∧
        MeasurableSet[mN₀] {ξ : Fin n → Ω | V ξ = 0} ∧
        MeasurableSet[mN₀] {ξ : Fin n → Ω | s ξ = 0} ∧
        (∀ ξ : Fin n → Ω, (1 / 2 : ℝ) ≤ 1 + e ξ) ∧
        (∀ ξ : Fin n → Ω, V ξ = 0 → d ξ = 0 ∧ e ξ = 0 ∧ Tclip ξ = 0) ∧
        @Measure.map (Fin n → Ω) ℝ mN₀ (borel ℝ) Tclip P₀ =
          @Measure.map (Fin n → Ω) ℝ mN (borel ℝ) Tclip P ∧
        @Measure.map (Fin n → Ω) ℝ mN₀ (borel ℝ) Tactual P₀ =
          @Measure.map (Fin n → Ω) ℝ mN (borel ℝ) Tactual P ∧
        (∀ i : Fin n,
          Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => cap ξ i) ∧
          Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => Ddel ξ i) ∧
          Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => Jdel ξ i) ∧
          Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => Adel ξ i) ∧
          Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => B1del ξ i) ∧
          Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => deletedTest ξ i) ∧
          let mRet : MeasurableSpace ({j : Fin n // j ≠ i} → Ω) :=
            @MeasurableSpace.pi {j : Fin n // j ≠ i}
              (fun _ : {j : Fin n // j ≠ i} => Ω)
              (fun _ : {j : Fin n // j ≠ i} => mΩ)
          let mRet₀ : MeasurableSpace ({j : Fin n // j ≠ i} → Ω) :=
            @MeasurableSpace.pi {j : Fin n // j ≠ i}
              (fun _ : {j : Fin n // j ≠ i} => Ω)
              (fun _ : {j : Fin n // j ≠ i} => m₀)
          let PRet : @Measure ({j : Fin n // j ≠ i} → Ω) mRet :=
            @Measure.pi {j : Fin n // j ≠ i}
              (fun _ : {j : Fin n // j ≠ i} => Ω)
              (inferInstance : Fintype {j : Fin n // j ≠ i})
              (fun _ : {j : Fin n // j ≠ i} => mΩ)
              (fun _ : {j : Fin n // j ≠ i} => μ)
          let PRet₀ : @Measure ({j : Fin n // j ≠ i} → Ω) mRet₀ :=
            @Measure.pi {j : Fin n // j ≠ i}
              (fun _ : {j : Fin n // j ≠ i} => Ω)
              (inferInstance : Fintype {j : Fin n // j ≠ i})
              (fun _ : {j : Fin n // j ≠ i} => m₀)
              (fun _ : {j : Fin n // j ≠ i} => μ₀)
          ∃ E : ({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ,
            Measurable[mRet₀, borel (ℝ × ℝ × ℝ)] E ∧
            (∀ ξ : Fin n → Ω,
              (Ddel ξ i, Jdel ξ i, B1del ξ i) =
                E (fun j : {j : Fin n // j ≠ i} => ξ j.val)) ∧
            @Measure.map (Fin n → Ω) (ℝ × ℝ × ℝ) mN₀ (borel (ℝ × ℝ × ℝ))
                (fun ξ : Fin n → Ω => (Ddel ξ i, Jdel ξ i, B1del ξ i)) P₀ =
              @Measure.map (Fin n → Ω) (ℝ × ℝ × ℝ) mN (borel (ℝ × ℝ × ℝ))
                (fun ξ : Fin n → Ω => (Ddel ξ i, Jdel ξ i, B1del ξ i)) P ∧
            @Measure.map ({j : Fin n // j ≠ i} → Ω) (ℝ × ℝ × ℝ)
                mRet₀ (borel (ℝ × ℝ × ℝ)) E PRet₀ =
              @Measure.map ({j : Fin n // j ≠ i} → Ω) (ℝ × ℝ × ℝ)
                mRet (borel (ℝ × ℝ × ℝ)) E PRet))
:= by
  intro f g r v rho rowIntegrable gLp projectionLaw pairLaw
  have hf : ∀ k : ℕ, Measurable[mΩ, borel ℝ] (f k) := by
    intro k
    exact measurable_const
  obtain ⟨m₀, hm₀, hcount₀, hh₀, hf₀⟩ :=
    Shao.OQ6.KernelObservableReduction.exists_countably_generated_observable_subspace
      h hh f hf
  refine ⟨m₀, hm₀, hcount₀, hh₀, hf₀, ?_⟩
  let μ₀ : @Measure Ω m₀ := μ.trim hm₀
  have hμmap : μ₀ = @Measure.map Ω Ω mΩ m₀ id μ :=
    trim_eq_map (μ := μ) hm₀
  have hid : Measurable[mΩ, m₀] (id : Ω → Ω) :=
    measurable_id'' hm₀
  have hbase :=
    @Shao.OQ6.OriginalKernelObservableTransport.actual_normalized_kernel_observable_trim_transport
      Ω mΩ (Fin 0) (inferInstance : Fintype (Fin 0)) μ
      (inferInstance : @IsProbabilityMeasure Ω mΩ μ)
      h hh hh2 hhsymm hcenter hprojectionsecond m₀ hm₀ hh₀
  dsimp only at hbase
  rcases hbase with
    ⟨hprob₀, hgpoint, hrpoint, hrow, hh₂₀, hcenter₀, hgmeas, hg₂₀,
      hgmean, hgsecond, hrmeas, hr₂₀, hrsymm, hrcanonical, hv, hrho,
      hglaw, hglp, hpair, _, _, _⟩
  letI : MeasurableSpace Ω := m₀
  let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
  let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
  let v₀ : ℝ :=
    ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
  let rho₀ : ℝ := Real.sqrt v₀
  letI : IsProbabilityMeasure μ₀ := hprob₀
  have hgeq : g₀ = g := funext hgpoint
  have hreq : r₀ = r := funext (fun o => funext (hrpoint o))
  refine ⟨hprob₀, hμmap, hgeq, hreq, hv, hrho, hrow, hh₂₀,
    hcenter₀, hgmeas, hg₂₀, hgmean, hgsecond, hrmeas, hr₂₀, hrsymm,
    hrcanonical, hglaw, hglp, hpair, ?_, ?_⟩
  · intro J instJ mJ mJ₀ P P₀
    have hfinite :=
      @Shao.OQ6.OriginalKernelObservableTransport.actual_normalized_kernel_observable_trim_transport
        Ω mΩ J instJ μ (inferInstance : @IsProbabilityMeasure Ω mΩ μ)
        h hh hh2 hhsymm hcenter hprojectionsecond m₀ hm₀ hh₀
    dsimp only at hfinite
    rcases hfinite with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hPprob, hPmap, _⟩
    have hidJ : Measurable[mJ, mJ₀] (id : (J → Ω) → J → Ω) := by
      apply (@measurable_pi_iff (J → Ω) J (fun _ : J => Ω)
        mJ (fun _ : J => m₀) (id : (J → Ω) → J → Ω)).2
      intro j
      exact hid.comp
        (@measurable_pi_apply J (fun _ : J => Ω) (fun _ : J => mΩ) j)
    refine ⟨hPprob, hidJ, hPmap, ?_⟩
    intro B mB T hT
    rw [hPmap, Measure.map_map hT hidJ]
    rfl
  · intro n hn z hz hz1 C0 hC0
    intro mN mN₀ P P₀ N W V D J Ddel Jdel A Adel B1 B1del s2 s d e
      Tclip Tactual cap deletedTest
    have hsample :=
      @Shao.OQ6.OriginalKernelObservableTransport.actual_normalized_kernel_observable_trim_transport
        Ω mΩ (Fin n) (inferInstance : Fintype (Fin n)) μ
        (inferInstance : @IsProbabilityMeasure Ω mΩ μ)
        h hh hh2 hhsymm hcenter hprojectionsecond m₀ hm₀ hh₀
    dsimp only at hsample
    rcases hsample with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, hPmap, _⟩
    have hidN : Measurable[mN, mN₀] (id : (Fin n → Ω) → Fin n → Ω) := by
      apply (@measurable_pi_iff (Fin n → Ω) (Fin n) (fun _ : Fin n => Ω)
        mN (fun _ : Fin n => m₀) (id : (Fin n → Ω) → Fin n → Ω)).2
      intro j
      exact hid.comp
        (@measurable_pi_apply (Fin n) (fun _ : Fin n => Ω)
          (fun _ : Fin n => mΩ) j)
    have hobservable :=
      @Shao.OQ6.OriginalClippedStatisticMeasurable.actual_normalized_compact_clipped_observables
        Ω m₀ μ₀ hprob₀ h hh₀ hh₂₀ hhsymm hcenter₀ hgsecond
        n hn z hz hz1 C0 hC0
    change
      let g : Ω → ℝ := g₀
      let r : Ω → Ω → ℝ := r₀
      let v : ℝ := v₀
      let rho : ℝ := rho₀
      let N : ℝ := Real.sqrt (n : ℝ)
      let W : (Fin n → Ω) → ℝ := projectionW n g
      let V : (Fin n → Ω) → ℝ := projectionV n g
      let D : (Fin n → Ω) → ℝ := residualStatisticD n r
      let J : (Fin n → Ω) → ℝ := residualEnergyJ n r
      let Ddel : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
      let Jdel : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
      let A : (Fin n → Ω) → ℝ := fun ξ => |D ξ|
      let Adel : (Fin n → Ω) → Fin n → ℝ := fun ξ i => |Ddel ξ i|
      let B1 : (Fin n → Ω) → ℝ := studentizerClipBudget n r C0 rho 1
      let B1del : (Fin n → Ω) → Fin n → ℝ := studentizerClipBudgetDeleted n r C0 rho 1
      let s2 : (Fin n → Ω) → ℝ := centeredSq n g r
      let s : (Fin n → Ω) → ℝ := fun ξ => Real.sqrt (s2 ξ)
      let d : (Fin n → Ω) → ℝ := centeredDelta n g r
      let e : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r C0 rho 1
      let Tclip : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r C0 rho 1
      let Tactual : (Fin n → Ω) → ℝ := fun ξ => if s ξ = 0 then 0 else (W ξ + D ξ) / s ξ
      let cap : (Fin n → Ω) → Fin n → ℝ := fun ξ i => min (|g (ξ i)| / N) (1 / (1 + z))
      let deletedTest : (Fin n → Ω) → Fin n → ℝ := fun ξ i => cap ξ i * (|A ξ - Adel ξ i| + z * |B1 ξ - B1del ξ i|)
      Measurable W ∧ Measurable V ∧ Measurable D ∧ Measurable J ∧
        Measurable A ∧ Measurable B1 ∧
        Measurable s2 ∧ Measurable s ∧ Measurable d ∧ Measurable e ∧
        Measurable Tclip ∧ Measurable Tactual ∧
        MeasurableSet {ξ : Fin n → Ω | V ξ = 0} ∧
        MeasurableSet {ξ : Fin n → Ω | s ξ = 0} ∧
        (∀ ξ : Fin n → Ω, (1 / 2 : ℝ) ≤ 1 + e ξ) ∧
        (∀ ξ : Fin n → Ω, V ξ = 0 →
          d ξ = 0 ∧ e ξ = 0 ∧ Tclip ξ = 0) ∧
        (∀ i : Fin n,
          Measurable (fun ξ : Fin n → Ω => cap ξ i) ∧
          Measurable (fun ξ : Fin n → Ω => Ddel ξ i) ∧
          Measurable (fun ξ : Fin n → Ω => Jdel ξ i) ∧
          Measurable (fun ξ : Fin n → Ω => Adel ξ i) ∧
          Measurable (fun ξ : Fin n → Ω => B1del ξ i) ∧
          Measurable (fun ξ : Fin n → Ω => deletedTest ξ i) ∧
          ∃ E : ({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ,
            Measurable E ∧
            ∀ ξ : Fin n → Ω,
              (Ddel ξ i, Jdel ξ i, B1del ξ i) =
                E (fun j : {j : Fin n // j ≠ i} => ξ j.val))
    at hobservable
    rw [hgeq, hreq, hrho] at hobservable
    dsimp only at hobservable
    rcases hobservable with
      ⟨hW, hV, hD, hJ, hA, hB1, hs2, hs, hd, he, hTclip,
        hTphysical, hzeroV, hzeroS, hlower, hzero, hdeleted⟩
    have hphysicalSame :
        (fun ξ : Fin n → Ω =>
          @ite ℝ (s ξ = 0) (Real.decidableEq (s ξ) 0)
            0 ((W ξ + D ξ) / s ξ)) = Tactual := by
      funext ξ
      by_cases hszero : s ξ = 0
      · simp only [Tactual, if_pos hszero]
      · simp only [Tactual, if_neg hszero]
    change Measurable[mN₀, borel ℝ]
      (fun ξ : Fin n → Ω =>
        @ite ℝ (s ξ = 0) (Real.decidableEq (s ξ) 0)
          0 ((W ξ + D ξ) / s ξ)) at hTphysical
    rw [hphysicalSame] at hTphysical
    have hTclipLaw :
        @Measure.map (Fin n → Ω) ℝ mN₀ (borel ℝ) Tclip P₀ =
          @Measure.map (Fin n → Ω) ℝ mN (borel ℝ) Tclip P := by
      rw [hPmap, Measure.map_map hTclip hidN]
      rfl
    have hTactualLaw :
        @Measure.map (Fin n → Ω) ℝ mN₀ (borel ℝ) Tactual P₀ =
          @Measure.map (Fin n → Ω) ℝ mN (borel ℝ) Tactual P := by
      rw [hPmap, Measure.map_map hTphysical hidN]
      rfl
    have hTripleBorel :
        (inferInstance : MeasurableSpace (ℝ × ℝ × ℝ)) =
          borel (ℝ × ℝ × ℝ) := BorelSpace.measurable_eq
    have hdeletedZero : ∀ i : Fin n,
        ∃ E : ({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ,
          Measurable[
            @MeasurableSpace.pi {j : Fin n // j ≠ i}
              (fun _ : {j : Fin n // j ≠ i} => Ω)
              (fun _ : {j : Fin n // j ≠ i} => m₀),
            borel (ℝ × ℝ × ℝ)] E ∧
          ∀ ξ : Fin n → Ω,
            (Ddel ξ i, Jdel ξ i, B1del ξ i) =
              E (fun j : {j : Fin n // j ≠ i} => ξ j.val) := by
      intro i
      have hzeroObservable :=
        @Shao.OQ6.OriginalClippedStatisticMeasurable.actual_normalized_compact_clipped_observables
          Ω m₀ μ₀ hprob₀ h hh₀ hh₂₀ hhsymm hcenter₀ hgsecond
          n hn (0 : ℝ) (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1)
          C0 hC0
      dsimp only at hzeroObservable
      rcases hzeroObservable with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hzeroDeleted⟩
      rcases hzeroDeleted i with ⟨_, _, _, _, _, _, E, hE, hEeq⟩
      refine ⟨E, ?_, ?_⟩
      · rw [← hTripleBorel]
        exact hE
      · intro ξ
        have hEeqξ := hEeq ξ
        change
          (residualStatisticDDeleted n r₀ ξ i,
            residualEnergyJDeleted n r₀ ξ i,
            studentizerClipBudgetDeleted n r₀ C0 rho₀ 1 ξ i) =
              E (fun j : {j : Fin n // j ≠ i} => ξ j.val) at hEeqξ
        rw [hreq, hrho] at hEeqξ
        exact hEeqξ
    refine ⟨hW, hV, hD, hJ, hA, hB1, hs2, hs, hd, he, hTclip,
      hTphysical, hzeroV, hzeroS, hlower, hzero, hTclipLaw, hTactualLaw, ?_⟩
    intro i
    rcases hdeleted i with ⟨hcap, hDdel, hJdel, hAdel, hB1del, hdeletedTest, _⟩
    refine ⟨hcap, hDdel, hJdel, hAdel, hB1del, hdeletedTest, ?_⟩
    intro mRet mRet₀ PRet PRet₀
    obtain ⟨E, hE, hEeq⟩ := hdeletedZero i
    refine ⟨E, hE, hEeq, ?_, ?_⟩
    · have htriple : Measurable[mN₀, borel (ℝ × ℝ × ℝ)]
          (fun ξ : Fin n → Ω => (Ddel ξ i, Jdel ξ i, B1del ξ i)) := by
        rw [← hTripleBorel]
        exact hDdel.prodMk (hJdel.prodMk hB1del)
      rw [hPmap, Measure.map_map htriple hidN]
      rfl
    · have hretained :=
        @Shao.OQ6.OriginalKernelObservableTransport.actual_normalized_kernel_observable_trim_transport
          Ω mΩ {j : Fin n // j ≠ i}
          (inferInstance : Fintype {j : Fin n // j ≠ i}) μ
          (inferInstance : @IsProbabilityMeasure Ω mΩ μ)
          h hh hh2 hhsymm hcenter hprojectionsecond m₀ hm₀ hh₀
      dsimp only at hretained
      rcases hretained with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, hPRetMap, _⟩
      have hidRet : Measurable[mRet, mRet₀]
          (id : ({j : Fin n // j ≠ i} → Ω) → {j : Fin n // j ≠ i} → Ω) := by
        apply (@measurable_pi_iff ({j : Fin n // j ≠ i} → Ω)
          {j : Fin n // j ≠ i} (fun _ : {j : Fin n // j ≠ i} => Ω)
          mRet (fun _ : {j : Fin n // j ≠ i} => m₀)
          (id : ({j : Fin n // j ≠ i} → Ω) → {j : Fin n // j ≠ i} → Ω)).2
        intro j
        exact hid.comp
          (@measurable_pi_apply {j : Fin n // j ≠ i}
            (fun _ : {j : Fin n // j ≠ i} => Ω)
            (fun _ : {j : Fin n // j ≠ i} => mΩ) j)
      rw [hPRetMap, Measure.map_map hE hidRet]
      rfl

end

end Shao.OQ6.OriginalCountablyGeneratedModel
