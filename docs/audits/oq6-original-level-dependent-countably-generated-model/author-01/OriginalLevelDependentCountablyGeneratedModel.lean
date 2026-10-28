import Shao.OQ6.OriginalCountablyGeneratedModel
import Shao.OQ6.OriginalLevelDependentClippedSourcePackage
import Shao.OQ6.OriginalLevelDependentCorrectionEnvelope

set_option autoImplicit false

universe u v w

open MeasureTheory
open scoped BigOperators Topology MeasureTheory ENNReal
open Shao.OQ5.P51

namespace Shao.OQ6.OriginalLevelDependentCountablyGeneratedModel

noncomputable section

theorem actual_original_level_dependent_countably_generated_model
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
          (z : ℝ) (hz : 1 ≤ z)
          (hwindow : z ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ))),
        (
            let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
            let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
            let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ₀.prod μ₀)
            let rho : ℝ := Real.sqrt v
            let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ₀)
            let N : ℝ := Real.sqrt (n : ℝ)
            let W : (Fin n → Ω) → ℝ := projectionW n g
            let V : (Fin n → Ω) → ℝ := projectionV n g
            let D : (Fin n → Ω) → ℝ := residualStatisticD n r
            let J : (Fin n → Ω) → ℝ := residualEnergyJ n r
            let Ddelete : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
            let Jdelete : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
            let A : (Fin n → Ω) → ℝ := fun ζ => |D ζ|
            let Adelete : (Fin n → Ω) → Fin n → ℝ := fun ζ i => |Ddelete ζ i|
            let B : (Fin n → Ω) → ℝ := studentizerClipBudget n r 512 rho z
            let Bdelete : (Fin n → Ω) → Fin n → ℝ :=
              studentizerClipBudgetDeleted n r 512 rho z
            let d : (Fin n → Ω) → ℝ := centeredDelta n g r
            let e : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r 512 rho z
            let Tclip : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho z
            let s : (Fin n → Ω) → ℝ := fun ζ => Real.sqrt (centeredSq n g r ζ)
            let Tphysical : (Fin n → Ω) → ℝ := fun ζ =>
              if s ζ = 0 then 0 else (W ζ + D ζ) / s ζ
            let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => g (ζ i) / N
            let cap : (Fin n → Ω) → Fin n → ℝ := fun ζ i => min |z * ξ0 i ζ| 1
            let S : (Fin n → Ω) → ℝ := fun ζ =>
              ∑ j : Fin n, (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)
            let Sdelete : (Fin n → Ω) → Fin n → ℝ := fun ζ i =>
              ∑ j ∈ Finset.univ.erase i, (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)
            let fullTest : (Fin n → Ω) → ℝ := fun ζ => z * A ζ + z ^ 2 * B ζ
            let deletedTest : (Fin n → Ω) → Fin n → ℝ := fun ζ i =>
              cap ζ i * (|A ζ - Adelete ζ i| + z * |B ζ - Bdelete ζ i|)
            let I : ℝ := ∫ ζ, Real.exp (S ζ) ∂P
            let sourceCost : ℝ :=
              ((∫ ζ, fullTest ζ * Real.exp (S ζ) ∂P) +
                ∑ i : Fin n, ∫ ζ, deletedTest ζ i * Real.exp (Sdelete ζ i) ∂P) / I
            Measurable W ∧ Measurable V ∧ Measurable D ∧ Measurable J ∧
            Measurable A ∧ Measurable B ∧ Measurable d ∧ Measurable e ∧
            Measurable s ∧ Measurable Tclip ∧ Measurable Tphysical ∧
            Measurable fullTest ∧
            MeasurableSet {ζ : Fin n → Ω | V ζ = 0} ∧
            MeasurableSet {ζ : Fin n → Ω | s ζ = 0} ∧
            (∀ ζ : Fin n → Ω,
              (1 / 2 : ℝ) ≤ 1 + e ζ ∧ |e ζ| ≤ B ζ ∧ |e ζ| ≤ |d ζ| ∧
              (0 < V ζ → 0 < V ζ * Real.sqrt (1 + e ζ))) ∧
            (∀ ζ : Fin n → Ω, V ζ = 0 → d ζ = 0 ∧ e ζ = 0 ∧ Tclip ζ = 0) ∧
            (∀ ζ : Fin n → Ω, s ζ = 0 → Tphysical ζ = 0) ∧
            (∀ i : Fin n,
              Measurable (fun ζ : Fin n → Ω => cap ζ i) ∧
              Measurable (fun ζ : Fin n → Ω => Ddelete ζ i) ∧
              Measurable (fun ζ : Fin n → Ω => Jdelete ζ i) ∧
              Measurable (fun ζ : Fin n → Ω => Adelete ζ i) ∧
              Measurable (fun ζ : Fin n → Ω => Bdelete ζ i) ∧
              Measurable (fun ζ : Fin n → Ω => deletedTest ζ i) ∧
              ∃ E : ({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ,
                Measurable E ∧ ∀ ζ : Fin n → Ω,
                  (Ddelete ζ i, Jdelete ζ i, Bdelete ζ i) =
                    E (fun j : {j : Fin n // j ≠ i} => ζ j.val)) ∧
            ((1 + rho) * z ≤ N →
              (∀ ζ : Fin n → Ω, ζ ∈ projectionGood n g z →
                -(1 / 2 : ℝ) ≤ d ζ →
                e ζ = d ζ ∧ 0 < V ζ * Real.sqrt (1 + e ζ) ∧
                0 < s ζ ∧ V ζ * Real.sqrt (1 + e ζ) = s ζ ∧
                Tclip ζ = Tphysical ζ) ∧
              {ζ : Fin n → Ω | Tclip ζ ≠ Tphysical ζ} ⊆
                (projectionGood n g z)ᶜ ∪ lowerStudentizerBad n g r z) ∧
            0 < I ∧
            Integrable (fun ζ => fullTest ζ * Real.exp (S ζ)) P ∧
            (∀ i : Fin n,
              Integrable (fun ζ => deletedTest ζ i * Real.exp (Sdelete ζ i)) P) ∧
            0 ≤ sourceCost ∧
            sourceCost ≤
              64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + rho) *
                (1 + z) ^ 3 / Real.sqrt (n : ℝ)
        ) ∧
        (
            let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
            let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
            let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ₀.prod μ₀)
            let rho : ℝ := Real.sqrt v
            let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ₀)
            let N : ℝ := Real.sqrt (n : ℝ)
            let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => g (ζ i) / N
            let D : (Fin n → Ω) → ℝ := residualStatisticD n r
            let J : (Fin n → Ω) → ℝ := residualEnergyJ n r
            let Ddelete : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
            let Jdelete : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
            let A : (Fin n → Ω) → ℝ := fun ζ => |D ζ|
            let Adelete : Fin n → (Fin n → Ω) → ℝ := fun i ζ => |Ddelete ζ i|
            let B : (Fin n → Ω) → ℝ := studentizerClipBudget n r 512 rho z
            let Bdelete : Fin n → (Fin n → Ω) → ℝ :=
              fun i ζ => studentizerClipBudgetDeleted n r 512 rho z ζ i
            let e : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r 512 rho z
            let V : (Fin n → Ω) → ℝ := fun ζ => Real.sqrt (∑ j : Fin n, (ξ0 j ζ) ^ 2)
            let Vdelete : Fin n → (Fin n → Ω) → ℝ := fun i ζ =>
              Real.sqrt (∑ j ∈ Finset.univ.erase i, (ξ0 j ζ) ^ 2)
            let H : (Fin n → Ω) → ℝ := fun ζ => (1 + V ζ) * (N + z * Real.sqrt (1 + B ζ))
            let Hdelete : Fin n → (Fin n → Ω) → ℝ := fun i ζ =>
              (1 + Vdelete i ζ) * (N + z * Real.sqrt (1 + Bdelete i ζ))
            let M : ℝ → (Fin n → Ω) → ℝ := fun ε ζ => 4 * ε * N * H ζ
            let Mdelete : ℝ → Fin n → (Fin n → Ω) → ℝ := fun ε i ζ =>
              4 * ε * N * Hdelete i ζ
            let κ : Fin n → ℝ := fun i =>
              4 * N * ((∫ ζ, H ζ ∂P) + (∫ ζ, Hdelete i ζ ∂P))
            let Δ : ℝ → Fin n → (Fin n → Ω) → ℝ := fun ε i ζ =>
              (A ζ + M ε ζ) - (Adelete i ζ + Mdelete ε i ζ) - (A ζ - Adelete i ζ)
            MemLp D 2 P ∧
            (∀ i : Fin n, MemLp (fun ζ => Ddelete ζ i) 2 P) ∧
            Integrable J P ∧ (∀ i : Fin n, Integrable (fun ζ => Jdelete ζ i) P) ∧
            Integrable A P ∧ (∀ i : Fin n, Integrable (Adelete i) P) ∧
            Integrable B P ∧ (∀ i : Fin n, Integrable (Bdelete i) P) ∧ Integrable e P ∧
            (∀ ζ : Fin n → Ω, 0 ≤ A ζ ∧ 0 ≤ B ζ ∧ |e ζ| ≤ B ζ) ∧
            (∀ (i : Fin n) (ζ : Fin n → Ω), 0 ≤ Adelete i ζ ∧ 0 ≤ Bdelete i ζ) ∧
            (∀ i : Fin n, Measurable (ξ0 i) ∧ MemLp (ξ0 i) 2 P ∧ (∫ ζ, ξ0 i ζ ∂P) = 0) ∧
            (∑ i : Fin n, ∫ ζ, (ξ0 i ζ) ^ 2 ∂P) = 1 ∧
            (∀ ζ : Fin n → Ω, V ζ = projectionV n g ζ) ∧
            Measurable H ∧ Integrable H P ∧
            (∀ i : Fin n, Measurable (Hdelete i) ∧ Integrable (Hdelete i) P) ∧
            (∀ ζ : Fin n → Ω, 0 < H ζ) ∧
            (∀ (i : Fin n) (ζ : Fin n → Ω), 0 < Hdelete i ζ) ∧
            (∀ ε : ℝ, Measurable (M ε) ∧ Integrable (M ε) P ∧
              Integrable (fun ζ => |M ε ζ|) P) ∧
            (∀ (ε : ℝ) (i : Fin n), Measurable (Mdelete ε i) ∧ Integrable (Mdelete ε i) P ∧
              Integrable (fun ζ => |Mdelete ε i ζ|) P) ∧
            (∀ ε : ℝ, 0 ≤ ε → ∀ ζ : Fin n → Ω,
              0 ≤ M ε ζ ∧ ∀ i : Fin n, 0 ≤ Mdelete ε i ζ) ∧
            (∀ i : Fin n, 0 ≤ κ i) ∧
            (∀ (ε : ℝ) (i : Fin n),
              (∫ ζ, M ε ζ ∂P) + (∫ ζ, Mdelete ε i ζ ∂P) = ε * κ i) ∧
            (∀ (ε : ℝ) (i : Fin n),
              (∫ ζ, |M ε ζ| ∂P) + (∫ ζ, |Mdelete ε i ζ| ∂P) = |ε| * κ i) ∧
            (∀ (ε : ℝ) (i : Fin n) (ζ : Fin n → Ω),
              Δ ε i ζ = M ε ζ - Mdelete ε i ζ) ∧
            (∀ (ε : ℝ) (i : Fin n) (ζ : Fin n → Ω),
              |Δ ε i ζ| ≤ |M ε ζ| + |Mdelete ε i ζ|) ∧
            (∀ (ε : ℝ) (i : Fin n), Measurable (Δ ε i) ∧ Integrable (Δ ε i) P ∧
              Integrable (fun ζ => |Δ ε i ζ|) P ∧
              (∫ ζ, |Δ ε i ζ| ∂P) ≤ |ε| * κ i) ∧
            (∀ i : Fin n, Filter.Tendsto (fun ε : ℝ => ∫ ζ, |Δ ε i ζ| ∂P)
              (nhds (0 : ℝ)) (nhds (0 : ℝ)))
        ))
:= by
  classical
  intro f g r v rho rowIntegrable gLp projectionLaw pairLaw
  obtain ⟨m₀, hm₀, hcount₀, hh₀, hf₀, hcore⟩ :=
    @Shao.OQ6.OriginalCountablyGeneratedModel.actual_normalized_original_countably_generated_model.{u, v, w}
      Ω mΩ μ (inferInstance : @IsProbabilityMeasure Ω mΩ μ)
      h hh hh2 hhsymm hcenter hprojectionsecond
  refine ⟨m₀, hm₀, hcount₀, hh₀, hf₀, ?_⟩
  let μ₀ : @Measure Ω m₀ := μ.trim hm₀
  letI : MeasurableSpace Ω := m₀
  let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
  let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
  let v₀ : ℝ :=
    ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
  let rho₀ : ℝ := Real.sqrt v₀
  rcases hcore with
    ⟨hprob₀, hμmap, hgeq, hreq, hv, hrho, hrow, hh₂₀,
      hcenter₀, hgmeas, hg₂₀, hgmean, hgsecond, hrmeas, hr₂₀, hrsymm,
      hrcanonical, hglaw, hglp, hpair, hfinite, _hfixed⟩
  letI : IsProbabilityMeasure μ₀ := hprob₀
  refine ⟨hprob₀, hμmap, hgeq, hreq, hv, hrho, hrow, hh₂₀,
    hcenter₀, hgmeas, hg₂₀, hgmean, hgsecond, hrmeas, hr₂₀, hrsymm,
    hrcanonical, hglaw, hglp, hpair, hfinite, ?_⟩
  intro n hn z hz hwindow
  exact ⟨
    @Shao.OQ6.OriginalLevelDependentClippedSourcePackage.actual_original_level_dependent_clipped_source_package
      Ω m₀ μ₀ hprob₀ h hh₀ hh₂₀ hhsymm hcenter₀ hgsecond n hn z hz hwindow,
    @Shao.OQ6.OriginalLevelDependentCorrectionEnvelope.actual_original_level_dependent_correction_envelope
      Ω m₀ μ₀ hprob₀ h hh₀ hh₂₀ hhsymm hcenter₀ hgsecond n hn z hz hwindow⟩

end

end Shao.OQ6.OriginalLevelDependentCountablyGeneratedModel
