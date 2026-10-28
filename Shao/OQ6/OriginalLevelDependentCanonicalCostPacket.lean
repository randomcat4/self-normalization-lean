import Shao.OQ6.OriginalLevelDependentCanonicalCoding
import Shao.OQ6.OriginalLevelDependentWeightedSourceCost
import Shao.OQ6.OriginalLevelDependentCorrectionEnvelope
import Mathlib.MeasureTheory.Function.L1Space.Integrable

set_option autoImplicit false

universe u

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical symmDiff
open Shao.OQ5.P51

namespace Shao.OQ6.OriginalLevelDependentCanonicalCostPacket

noncomputable section

theorem actual_original_level_dependent_canonical_cost_packet
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ :=
      ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω mΩ mΩ μ μ)
    let rho : ℝ := Real.sqrt v
    ∃ (m₀ : MeasurableSpace Ω) (hm₀ : m₀ ≤ mΩ)
        (hcg : @MeasurableSpace.CountablyGenerated Ω m₀),
      let μ₀ : @Measure Ω m₀ := μ.trim hm₀
      letI : MeasurableSpace Ω := m₀
      letI : MeasurableSpace.CountablyGenerated Ω := hcg
      IsProbabilityMeasure μ₀ ∧
      ∀ (n : ℕ) (hn : 4 ≤ n)
          (y : ℝ) (hy : 1 ≤ y)
          (hywindow : y ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ)))
          (ε : ℝ) (hε : 0 < ε)
          (hεsmall : ε < 1 / (4 * Real.sqrt (n : ℝ))),
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
        let O : Fin n → (Fin n → Ω) → Ω := fun i ξ => ξ i
        let gcoord : Fin n → Ω → ℝ := fun _ o => g o / N
        let Q : (Fin n → Ω) → (Fin n → Ω) := fun ξ i => O i ξ
        let D1 : (Fin n → Ω) → ℝ := residualStatisticD n r
        let D2 : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r 512 rho y
        let Tclip : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho y
        let Ddel : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
        let Jdel : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
        let Bdelete : (Fin n → Ω) → Fin n → ℝ := studentizerClipBudgetDeleted n r 512 rho y
        let κ : (Fin n → Ω) → ℝ := fun _ => 0
        let W0 : (Fin n → Ω) → ℝ := fun ξ => ∑ i : Fin n, gcoord i (O i ξ)
        let V0 : (Fin n → Ω) → ℝ :=
          fun ξ => Real.sqrt (∑ i : Fin n, (gcoord i (O i ξ)) ^ 2)
        let T0 : (Fin n → Ω) → ℝ := fun ξ =>
          if V0 ξ = 0 then κ ξ else
            (W0 ξ + D1 (Q ξ)) / (V0 ξ * Real.sqrt (1 + D2 (Q ξ)))
        let lambda01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
        let mAugLocal : MeasurableSpace (Ω × ℝ) := m₀.prod (borel ℝ)
        let mAug : MeasurableSpace (Fin n → Ω × ℝ) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (fun _ : Fin n => mAugLocal)
        let νlocal : Fin n → @Measure (Ω × ℝ) mAugLocal :=
          fun _ => @Measure.prod Ω ℝ m₀ (borel ℝ) μ₀ lambda01
        let ν : @Measure (Fin n → Ω × ℝ) mAug :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => mAugLocal) νlocal
        let q : (Fin n → Ω × ℝ) → (Fin n → Ω) := fun x i => (x i).1
        let c : Fin n → (Ω × ℝ) → ℝ := fun _ =>
          Shao.OQ6.ScalarObservationCoding.baseFourIndicatorCode
            (MeasurableSpace.natGeneratingSequence (Ω × ℝ))
        let ξlocal : Fin n → (Ω × ℝ) → ℝ := fun i t => gcoord i t.1
        let Ylocal : Fin n → (Ω × ℝ) → ℝ := fun i =>
          Shao.OQ6.QuantizedObservationCoding.quantizedObservation ε (ξlocal i) (c i)
        let ξ : Fin n → (Fin n → Ω × ℝ) → ℝ := fun i x => gcoord i (x i).1
        let Y : Fin n → (Fin n → Ω × ℝ) → ℝ := fun i x => Ylocal i (x i)
        let a : Fin n → ℝ := Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν Y
        let s : ℝ := Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν Y
        let ηlocal : Fin n → (Ω × ℝ) → ℝ := fun i =>
          Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation (a i) s (Ylocal i)
        let η : Fin n → (Fin n → Ω × ℝ) → ℝ :=
          Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν Y
        let C : (Fin n → Ω × ℝ) → (Fin n → ℝ) := fun x i => η i x
        let W : (Fin n → Ω × ℝ) → ℝ := fun x => ∑ i : Fin n, ξ i x
        let V : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (∑ i : Fin n, (ξ i x) ^ 2)
        let Wη : (Fin n → Ω × ℝ) → ℝ := fun x => ∑ i : Fin n, η i x
        let Vη : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (∑ i : Fin n, (η i x) ^ 2)
        let b : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (1 + D2 (q x))
        let Dη : ℝ → (Fin n → Ω × ℝ) → ℝ :=
          fun z x => D1 (q x) + W x - Wη x + z * b x * (Vη x - V x)
        let Tη : ℝ → (Fin n → Ω × ℝ) → ℝ :=
          fun z x => (Wη x + Dη z x) / (Vη x * b x)
        let Z0 : Set (Fin n → Ω) := {ξ | projectionV n g ξ = 0}
        let Z : Set (Fin n → Ω × ℝ) := {x | V x = 0}
        let p0 : ℝ := P.real Z0
        let comparisons : Set (ℝ → ℝ → Prop) :=
          {R | R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨
            R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨
            R = (fun a b : ℝ => a = b)}
        let F0 : (ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω) := fun R z =>
          {ξ | R (projectionW n g ξ + D1 ξ)
            (z * projectionV n g ξ * Real.sqrt (1 + D2 ξ))}
        let A0 : (ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω) :=
          fun R z => {ξ | R (Tclip ξ) z}
        let Eη : (ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω × ℝ) :=
          fun R z => {x | R (Tη z x) z}
        let J : (Fin n → Ω) → ℝ := residualEnergyJ n r
        let A : (Fin n → Ω) → ℝ := fun ξ : Fin n → Ω => |D1 ξ|
        let Adel : (Fin n → Ω) → Fin n → ℝ :=
          fun (ξ : Fin n → Ω) (i : Fin n) => |Ddel ξ i|
        let B : (Fin n → Ω) → ℝ := studentizerClipBudget n r 512 rho y
        let deletionMass : (Fin n → Ω) → Fin n → ℝ :=
          fun (ξ : Fin n → Ω) (i : Fin n) =>
            |A ξ - Adel ξ i| + |B ξ - Bdelete ξ i|
        let deletionTotal : (Fin n → Ω) → ℝ :=
          fun ξ : Fin n → Ω => ∑ i : Fin n, deletionMass ξ i
        let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => gcoord i (O i ζ)
        let S0 : (Fin n → Ω) → ℝ := fun ζ =>
          ∑ j : Fin n, (y * ξ0 j ζ - (y * ξ0 j ζ) ^ 2 / 2)
        let S0delete : (Fin n → Ω) → Fin n → ℝ := fun ζ i =>
          ∑ j ∈ Finset.univ.erase i, (y * ξ0 j ζ - (y * ξ0 j ζ) ^ 2 / 2)
        let Sν : (Fin n → Ω × ℝ) → ℝ := fun x =>
          ∑ j : Fin n, (y * ξ j x - (y * ξ j x) ^ 2 / 2)
        let Sνdelete : (Fin n → Ω × ℝ) → Fin n → ℝ := fun x i =>
          ∑ j ∈ Finset.univ.erase i, (y * ξ j x - (y * ξ j x) ^ 2 / 2)
        let fullTest0 : (Fin n → Ω) → ℝ := fun ζ => y * A ζ + y ^ 2 * B ζ
        let deleteTest0 : (Fin n → Ω) → Fin n → ℝ := fun ζ i =>
          min |y * ξ0 i ζ| 1 * (|A ζ - Adel ζ i| + y * |B ζ - Bdelete ζ i|)
        let fullTestν : (Fin n → Ω × ℝ) → ℝ := fun x => fullTest0 (q x)
        let deleteTestν : (Fin n → Ω × ℝ) → Fin n → ℝ := fun x i => deleteTest0 (q x) i
        let Ioriginal : ℝ := ∫ ζ : Fin n → Ω, Real.exp (S0 ζ) ∂P
        let Ireduced : ℝ := ∫ ζ : Fin n → Ω, Real.exp (S0 ζ) ∂P₀
        let Icoded : ℝ := ∫ x : Fin n → Ω × ℝ, Real.exp (Sν x) ∂ν
        let costOriginal : ℝ :=
          ((∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P) +
            ∑ i : Fin n, ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P) / Ioriginal
        let costReduced : ℝ :=
          ((∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P₀) +
            ∑ i : Fin n, ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P₀) / Ireduced
        let costCoded : ℝ :=
          ((∫ x, fullTestν x * Real.exp (Sν x) ∂ν) +
            ∑ i : Fin n, ∫ x, deleteTestν x i * Real.exp (Sνdelete x i) ∂ν) / Icoded
        @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ ∧
        P₀ = @Measure.map (Fin n → Ω) (Fin n → Ω) mN mN₀ id P ∧
        (∀ i : Fin n, Measurable (O i) ∧ MeasurePreserving (O i) P₀ μ₀) ∧
        iIndepFun O P₀ ∧
        (∀ i : Fin n, Measurable (gcoord i) ∧
          MemLp (fun ξ => gcoord i (O i ξ)) 2 P₀ ∧
          (∫ ξ, gcoord i (O i ξ) ∂P₀) = 0 ∧
          (∫ ξ, (gcoord i (O i ξ)) ^ 2 ∂P₀) = 1 / (n : ℝ)) ∧
        (∑ i : Fin n, ∫ ξ, (gcoord i (O i ξ)) ^ 2 ∂P₀) = 1 ∧
        Q = id ∧ W0 = projectionW n g ∧ V0 = projectionV n g ∧ T0 = Tclip ∧
        Measurable D1 ∧ Measurable D2 ∧
        (∀ ξ : Fin n → Ω, (1 / 2 : ℝ) ≤ 1 + D2 ξ) ∧
        Measurable[mN₀, borel ℝ] Tclip ∧ Measurable[mN, borel ℝ] Tclip ∧
        @Measure.map (Fin n → Ω) ℝ mN₀ (borel ℝ) Tclip P₀ =
          @Measure.map (Fin n → Ω) ℝ mN (borel ℝ) Tclip P ∧
        IsProbabilityMeasure ν ∧ MeasurePreserving q ν P₀ ∧
        (1 / 2 : ℝ) < s ∧
        (∀ (i : Fin n) (x : Fin n → Ω × ℝ), η i x = ηlocal i (x i)) ∧
        iIndepFun η ν ∧
        (∀ i : Fin n, Measurable (η i) ∧ MemLp (η i) 2 ν) ∧
        (∀ i : Fin n, Integrable (η i) ν ∧ Integrable (fun x => (η i x) ^ 2) ν) ∧
        (∀ i : Fin n, (∫ x, η i x ∂ν) = 0) ∧
        (∑ i : Fin n, ∫ x, (η i x) ^ 2 ∂ν) = 1 ∧
        (∀ (i : Fin n) (t : ℝ), ν {x : Fin n → Ω × ℝ | η i x = t} = 0) ∧
        ν {x : Fin n → Ω × ℝ | Vη x = 0} = 0 ∧
        (∀ᵐ x ∂ν, 0 < Vη x ∧ 0 < b x ∧ 0 < Vη x * b x) ∧
        Measurable[mAug, borel (Fin n → ℝ)] C ∧
        MeasurableSpace.comap C (borel (Fin n → ℝ)) = mAug ∧
        (∀ (H : (Fin n → Ω × ℝ) → ℝ), Measurable H →
          ∃ F : (Fin n → ℝ) → ℝ, Measurable[borel (Fin n → ℝ), borel ℝ] F ∧
            ∀ x : Fin n → Ω × ℝ, H x = F (C x)) ∧
        (∀ (i : Fin n) (d : ({j : Fin n // j ≠ i} → Ω × ℝ) → ℝ), Measurable d →
          ∃ F : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
            Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] F ∧
            (∀ y : {j : Fin n // j ≠ i} → Ω × ℝ,
              d y = F (fun j => ηlocal j.val (y j))) ∧
            Measurable[borel (Fin n → ℝ), borel ℝ]
              (fun t : Fin n → ℝ => F (fun j => t j.val)) ∧
            ∀ x : Fin n → Ω × ℝ, d (fun j => x j.val) = F (fun j => η j.val x)) ∧
        (∃ G2 : (Fin n → ℝ) → ℝ,
          Measurable[borel (Fin n → ℝ), borel ℝ] G2 ∧
          (∀ x : Fin n → Ω × ℝ, D2 (q x) = G2 (C x)) ∧
          ∀ z : ℝ, ∃ G1 : (Fin n → ℝ) → ℝ,
            Measurable[borel (Fin n → ℝ), borel ℝ] G1 ∧
            ∀ x : Fin n → Ω × ℝ, Dη z x = G1 (C x)) ∧
        (∀ i : Fin n,
          ∃ Fdel : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ,
            Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdel ∧
            ∀ x : Fin n → Ω × ℝ,
              (Ddel (q x) i, Jdel (q x) i, Bdelete (q x) i) =
                Fdel (fun j : {j : Fin n // j ≠ i} => η j.val x)) ∧
        (∀ z : ℝ, Measurable (Dη z) ∧ Measurable (Tη z)) ∧
        MeasurableSet[mN₀] Z0 ∧ MeasurableSet[mN] Z0 ∧ MeasurableSet Z ∧
        ν Z = P₀ Z0 ∧ P₀ Z0 = P Z0 ∧ ν.real Z = p0 ∧
        (∀ (z : ℝ) (x : Fin n → Ω × ℝ),
          Wη x + Dη z x - z * Vη x * b x = W x + D1 (q x) - z * V x * b x) ∧
        (∀ (z : ℝ) (R : ℝ → ℝ → Prop), R ∈ comparisons →
          MeasurableSet[mN₀] (A0 R z) ∧ MeasurableSet[mN] (A0 R z) ∧
          MeasurableSet[mN₀] (F0 R z) ∧ MeasurableSet[mN] (F0 R z) ∧
          MeasurableSet (Eη R z) ∧
          ν (Eη R z) = P₀ (F0 R z) ∧ P₀ (F0 R z) = P (F0 R z) ∧
          (∀ ξ : Fin n → Ω, ξ ∈ (A0 R z ∆ F0 R z) → ξ ∈ Z0) ∧
          P (A0 R z ∆ F0 R z) ≤ P Z0 ∧
          |P.real (A0 R z) - ν.real (Eη R z)| ≤ p0) ∧
        (∀ ξ : Fin n → Ω, 0 ≤ A ξ ∧ 0 ≤ B ξ ∧ |D2 ξ| ≤ B ξ) ∧
        (∀ (i : Fin n) (ξ : Fin n → Ω), 0 ≤ Adel ξ i ∧ 0 ≤ Bdelete ξ i) ∧
        Measurable[mN₀, borel ℝ] J ∧
        Measurable[mN₀, borel ℝ] A ∧ Measurable[mN₀, borel ℝ] B ∧
        (∀ i : Fin n,
          Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => Ddel ξ i) ∧
          Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => Jdel ξ i) ∧
          Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => Adel ξ i) ∧
          Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => Bdelete ξ i)) ∧
        Integrable A P₀ ∧ Integrable B P₀ ∧ Integrable D2 P₀ ∧
        (∀ i : Fin n,
          Integrable (fun ξ : Fin n → Ω => Adel ξ i) P₀ ∧
          Integrable (fun ξ : Fin n → Ω => Bdelete ξ i) P₀ ∧
          Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => |A ξ - Adel ξ i|) ∧
          Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => |B ξ - Bdelete ξ i|) ∧
          Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => deletionMass ξ i) ∧
          Integrable (fun ξ : Fin n → Ω => |A ξ - Adel ξ i|) P₀ ∧
          Integrable (fun ξ : Fin n → Ω => |B ξ - Bdelete ξ i|) P₀ ∧
          Integrable (fun ξ : Fin n → Ω => deletionMass ξ i) P₀) ∧
        Measurable[mN₀, borel ℝ] deletionTotal ∧ Integrable deletionTotal P₀ ∧
        Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => A (q x)) ∧
        Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => B (q x)) ∧
        Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => D2 (q x)) ∧
        Integrable (fun x : Fin n → Ω × ℝ => A (q x)) ν ∧
        Integrable (fun x : Fin n → Ω × ℝ => B (q x)) ν ∧
        Integrable (fun x : Fin n → Ω × ℝ => D2 (q x)) ν ∧
        (∀ i : Fin n,
          Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => Adel (q x) i) ∧
          Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => Bdelete (q x) i) ∧
          Integrable (fun x : Fin n → Ω × ℝ => Adel (q x) i) ν ∧
          Integrable (fun x : Fin n → Ω × ℝ => Bdelete (q x) i) ν ∧
          Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => |A (q x) - Adel (q x) i|) ∧
          Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => |B (q x) - Bdelete (q x) i|) ∧
          Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => deletionMass (q x) i) ∧
          Integrable (fun x : Fin n → Ω × ℝ => |A (q x) - Adel (q x) i|) ν ∧
          Integrable (fun x : Fin n → Ω × ℝ => |B (q x) - Bdelete (q x) i|) ν ∧
          Integrable (fun x : Fin n → Ω × ℝ => deletionMass (q x) i) ν) ∧
        Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => deletionTotal (q x)) ∧
        Integrable (fun x : Fin n → Ω × ℝ => deletionTotal (q x)) ν ∧
        (∀ x : Fin n → Ω × ℝ, Sν x = S0 (q x)) ∧
        (∀ (i : Fin n) (x : Fin n → Ω × ℝ), Sνdelete x i = S0delete (q x) i) ∧
        0 < Ioriginal ∧ Ireduced = Ioriginal ∧ Icoded = Ioriginal ∧
        0 < Ireduced ∧ 0 < Icoded ∧
        Integrable (fun ζ => fullTest0 ζ * Real.exp (S0 ζ)) P ∧
        (∀ i : Fin n,
          Integrable (fun ζ => deleteTest0 ζ i * Real.exp (S0delete ζ i)) P) ∧
        Integrable (fun ζ => fullTest0 ζ * Real.exp (S0 ζ)) P₀ ∧
        (∀ i : Fin n,
          Integrable (fun ζ => deleteTest0 ζ i * Real.exp (S0delete ζ i)) P₀) ∧
        Integrable (fun x => fullTestν x * Real.exp (Sν x)) ν ∧
        (∀ i : Fin n,
          Integrable (fun x => deleteTestν x i * Real.exp (Sνdelete x i)) ν) ∧
        (∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P₀) =
          ∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P ∧
        (∫ x, fullTestν x * Real.exp (Sν x) ∂ν) =
          ∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P ∧
        (∀ i : Fin n,
          (∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P₀) =
            ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P) ∧
        (∀ i : Fin n,
          (∫ x, deleteTestν x i * Real.exp (Sνdelete x i) ∂ν) =
            ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P) ∧
        costReduced = costOriginal ∧ costCoded = costOriginal ∧
        0 ≤ costOriginal ∧ 0 ≤ costReduced ∧ 0 ≤ costCoded ∧
        costOriginal ≤
          64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + rho) *
            (1 + y) ^ 3 / Real.sqrt (n : ℝ) ∧
        costReduced ≤
          64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + rho) *
            (1 + y) ^ 3 / Real.sqrt (n : ℝ) ∧
        costCoded ≤
          64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + rho) *
            (1 + y) ^ 3 / Real.sqrt (n : ℝ)
:= by
  classical
  intro g r v rho
  have hcanonical :=
    Shao.OQ6.OriginalLevelDependentCanonicalCoding.actual_original_level_dependent_canonical_normalized_coding
      μ h hh hh2 hhsymm hcenter hprojectionsecond
  dsimp only at hcanonical
  rcases hcanonical with ⟨m₀, hm₀, hcg, hbase⟩
  refine ⟨m₀, hm₀, hcg, ?_⟩
  intro μ₀
  letI : MeasurableSpace Ω := m₀
  letI : MeasurableSpace.CountablyGenerated Ω := hcg
  rcases hbase with ⟨hμ₀prob, hfor⟩
  refine ⟨hμ₀prob, ?_⟩
  intro n hn y hy hywindow ε hε hεsmall
  intro mN mN₀ P P₀ N O gcoord Q D1 D2 Tclip Ddel Jdel Bdelete κ W0 V0 T0
    lambda01 mAugLocal mAug νlocal ν q c ξlocal Ylocal ξ Y a s ηlocal η C W V
    Wη Vη b Dη Tη Z0 Z p0 comparisons F0 A0 Eη
    J A Adel B deletionMass deletionTotal
    ξ0 S0 S0delete Sν Sνdelete fullTest0 deleteTest0 fullTestν deleteTestν
    Ioriginal Ireduced Icoded costOriginal costReduced costCoded
  have hcan := hfor n hn y hy hywindow ε hε hεsmall
  rcases hcan with
    ⟨hP₀prob, hP₀map, hO, hOindep, hgcoord, hgenergy,
      hQid, hW0eq, hV0eq, hT0eq, hD1m, hD2m, hhalf,
      hTclipm, hTclipOriginal, hTcliplaw, hνprob, hqpres,
      hs, hηeval, hηindep, hηL2, hηInts, hηmean, hηenergy,
      hηnull, hVηnull, hpositiveDenominator, hCmeas, hCcomap,
      hfactor, hretained, hscalar, hdeletedFactor, hTηmeas,
      hZ0m, hZ0Original, hZmeas, hZcodedlaw, hZ0law,
      hZcodedreal, hsigned, hcomparison⟩
  change Measurable[mN₀, borel ℝ] D1 at hD1m
  change Measurable[mN₀, borel ℝ] D2 at hD2m
  change @MeasurePreserving (Fin n → Ω × ℝ) (Fin n → Ω) mAug mN₀
    q ν P₀ at hqpres
  change P₀ = @Measure.map (Fin n → Ω) (Fin n → Ω) mN mN₀ id P at hP₀map
  have hcost :=
    @Shao.OQ6.OriginalLevelDependentCorrectionEnvelope.actual_original_level_dependent_correction_envelope
      Ω mΩ μ (inferInstance : @IsProbabilityMeasure Ω mΩ μ)
      h hh hh2 hhsymm hcenter hprojectionsecond n hn y hy hywindow
  dsimp only at hcost
  rcases hcost with
    ⟨_, _, _, _, hAIP, hAdelIP, hBIP, hBdeleteIP, heIP,
      hFullBounds, hDeletedBounds, _⟩
  change Integrable A P at hAIP
  change ∀ i : Fin n, Integrable (fun ζ : Fin n → Ω => Adel ζ i) P at hAdelIP
  change Integrable B P at hBIP
  change ∀ i : Fin n, Integrable (fun ζ : Fin n → Ω => Bdelete ζ i) P at hBdeleteIP
  change Integrable D2 P at heIP
  change ∀ ζ : Fin n → Ω, 0 ≤ A ζ ∧ 0 ≤ B ζ ∧ |D2 ζ| ≤ B ζ at hFullBounds
  change ∀ (i : Fin n) (ζ : Fin n → Ω), 0 ≤ Adel ζ i ∧ 0 ≤ Bdelete ζ i at hDeletedBounds
  let τ : (Fin n → Ω) → (Fin n → Ω × ℝ) :=
    fun (ζ : Fin n → Ω) (i : Fin n) => (ζ i, (1 / 2 : ℝ))
  let Rdel : ∀ i : Fin n, (Fin n → Ω) → ({j : Fin n // j ≠ i} → ℝ) :=
    fun (i : Fin n) (ζ : Fin n → Ω) (j : {j : Fin n // j ≠ i}) => η j.val (τ ζ)
  let K : ℝ := N * ((n : ℝ) - 1)
  let psi : (Fin n → Ω) → Fin n → ℝ :=
    fun (ζ : Fin n → Ω) (i : Fin n) =>
      Shao.OQ6.ResidualDeletion.rowSum
        (fun (j k : Fin n) => r (ζ j) (ζ k)) i
  have hτm : Measurable[mN₀, mAug] τ := by
    apply Measurable.of_eval
    intro i
    exact (measurable_pi_apply i).prodMk measurable_const
  have hqτ (ζ : Fin n → Ω) : q (τ ζ) = ζ := by
    funext i
    rfl
  have hTripleBorel :
      (inferInstance : MeasurableSpace (ℝ × ℝ × ℝ)) =
        borel (ℝ × ℝ × ℝ) := BorelSpace.measurable_eq
  have hDeletedMeasurable (i : Fin n) :
      Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => Ddel ζ i) ∧
      Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => Jdel ζ i) ∧
      Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => Bdelete ζ i) := by
    rcases hdeletedFactor i with ⟨Fdel, hFdel, hFdelpoint⟩
    have hRetainedBorel :
        (inferInstance : MeasurableSpace ({j : Fin n // j ≠ i} → ℝ)) =
          borel ({j : Fin n // j ≠ i} → ℝ) := BorelSpace.measurable_eq
    have hRdel : Measurable[mN₀, borel ({j : Fin n // j ≠ i} → ℝ)] (Rdel i) := by
      rw [← hRetainedBorel]
      apply Measurable.of_eval
      intro j
      exact ((hηL2 j.val).1).comp hτm
    have hTriplePoint :
        (fun ζ : Fin n → Ω => (Ddel ζ i, Jdel ζ i, Bdelete ζ i)) =
          (fun ζ : Fin n → Ω => Fdel (Rdel i ζ)) := by
      funext ζ
      simpa only [hqτ, Rdel] using hFdelpoint (τ ζ)
    have hTriple : Measurable[mN₀, borel (ℝ × ℝ × ℝ)]
        (fun ζ : Fin n → Ω => (Ddel ζ i, Jdel ζ i, Bdelete ζ i)) := by
      rw [hTriplePoint]
      exact hFdel.comp hRdel
    have hTripleProduct :
        Measurable[mN₀, (inferInstance : MeasurableSpace (ℝ × ℝ × ℝ))]
          (fun ζ : Fin n → Ω => (Ddel ζ i, Jdel ζ i, Bdelete ζ i)) := by
      rw [hTripleBorel]
      exact hTriple
    exact ⟨hTripleProduct.fst, hTripleProduct.snd.fst, hTripleProduct.snd.snd⟩
  have hrsymm (o y : Ω) : r o y = r y o := by
    change h o y - g o - g y = h y o - g y - g o
    rw [hhsymm o y]
    ring
  have hn4R : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hNpos : 0 < N := Real.sqrt_pos.2 (by linarith only [hn4R])
  have hKne : K ≠ 0 := by
    exact ne_of_gt (mul_pos hNpos (by linarith only [hn4R]))
  have hpsiPoint (ζ : Fin n → Ω) (i : Fin n) :
      psi ζ i = K * (D1 ζ - Ddel ζ i) := by
    have hIncident :=
      Shao.OQ6.ResidualDeletion.unorderedPairSum_sub_eraseIncident
        (fun (j k : Fin n) => r (ζ j) (ζ k))
        (fun (j k : Fin n) => hrsymm (ζ j) (ζ k)) i
    change Shao.OQ5.P35.unorderedPairSum (fun (j k : Fin n) => r (ζ j) (ζ k)) -
      Shao.OQ5.P35.unorderedPairSum
        (Shao.OQ6.ResidualDeletion.eraseIncident
          (fun (j k : Fin n) => r (ζ j) (ζ k)) i) = psi ζ i at hIncident
    change psi ζ i = K *
      (Shao.OQ5.P35.unorderedPairSum (fun (j k : Fin n) => r (ζ j) (ζ k)) / K -
        Shao.OQ5.P35.unorderedPairSum
          (Shao.OQ6.ResidualDeletion.eraseIncident
            (fun (j k : Fin n) => r (ζ j) (ζ k)) i) / K)
    rw [← sub_div, hIncident]
    field_simp [hKne] <;> ring
  have hpsiMeasurable (i : Fin n) :
      Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => psi ζ i) := by
    have hEq : (fun ζ : Fin n → Ω => psi ζ i) =
        (fun ζ : Fin n → Ω => K * (D1 ζ - Ddel ζ i)) := by
      funext ζ
      exact hpsiPoint ζ i
    rw [hEq]
    exact measurable_const.mul (hD1m.sub (hDeletedMeasurable i).1)
  have hJm : Measurable[mN₀, borel ℝ] J := by
    have hEq : J = (fun ζ : Fin n → Ω =>
        (∑ i : Fin n, (psi ζ i) ^ 2) / ((n : ℝ) - 2) ^ 2) := by
      funext ζ
      exact residualEnergyJ_eq_rowSqSum n r ζ
    rw [hEq]
    exact (Finset.measurable_sum Finset.univ
      (fun (i : Fin n) (_hi : i ∈ (Finset.univ : Finset (Fin n))) =>
        (hpsiMeasurable i).pow_const 2)).div_const (((n : ℝ) - 2) ^ 2)
  have hAm : Measurable[mN₀, borel ℝ] A := by
    simpa only [Real.norm_eq_abs] using hD1m.norm
  have hAdelm (i : Fin n) :
      Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => Adel ζ i) := by
    simpa only [Real.norm_eq_abs] using (hDeletedMeasurable i).1.norm
  have hBm : Measurable[mN₀, borel ℝ] B := by
    change Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω =>
      512 * (((1 + rho) * y) / N + J ζ / ((1 + rho) * y * N)))
    exact measurable_const.mul
      (measurable_const.add (hJm.div_const ((1 + rho) * y * N)))
  have hBdeletem (i : Fin n) :
      Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => Bdelete ζ i) :=
    (hDeletedMeasurable i).2.2
  have hidΩ : Measurable[mΩ, m₀] (id : Ω → Ω) := measurable_id'' hm₀
  have hidN : Measurable[mN, mN₀] (id : (Fin n → Ω) → (Fin n → Ω)) := by
    apply (@measurable_pi_iff (Fin n → Ω) (Fin n) (fun _ : Fin n => Ω)
      mN (fun _ : Fin n => m₀) (id : (Fin n → Ω) → (Fin n → Ω))).2
    intro i
    exact hidΩ.comp
      (@measurable_pi_apply (Fin n) (fun _ : Fin n => Ω)
        (fun _ : Fin n => mΩ) i)
  have hId : @MeasurePreserving (Fin n → Ω) (Fin n → Ω) mN mN₀ id P P₀ :=
    @MeasurePreserving.mk (Fin n → Ω) (Fin n → Ω) mN mN₀
      id P P₀ hidN hP₀map.symm
  have hAI : Integrable A P₀ := by
    apply (hId.integrable_comp hAm.aestronglyMeasurable).mp
    simpa only [Function.comp_def, id_eq] using hAIP
  have hBI : Integrable B P₀ := by
    apply (hId.integrable_comp hBm.aestronglyMeasurable).mp
    simpa only [Function.comp_def, id_eq] using hBIP
  have heI : Integrable D2 P₀ := by
    apply (hId.integrable_comp hD2m.aestronglyMeasurable).mp
    simpa only [Function.comp_def, id_eq] using heIP
  have hAdelI (i : Fin n) : Integrable (fun ζ : Fin n → Ω => Adel ζ i) P₀ := by
    apply (hId.integrable_comp (hAdelm i).aestronglyMeasurable).mp
    simpa only [Function.comp_def, id_eq] using hAdelIP i
  have hBdeleteI (i : Fin n) : Integrable (fun ζ : Fin n → Ω => Bdelete ζ i) P₀ := by
    apply (hId.integrable_comp (hBdeletem i).aestronglyMeasurable).mp
    simpa only [Function.comp_def, id_eq] using hBdeleteIP i
  have hDiff (i : Fin n) :
      Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => |A ζ - Adel ζ i|) ∧
      Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => |B ζ - Bdelete ζ i|) ∧
      Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => deletionMass ζ i) ∧
      Integrable (fun ζ : Fin n → Ω => |A ζ - Adel ζ i|) P₀ ∧
      Integrable (fun ζ : Fin n → Ω => |B ζ - Bdelete ζ i|) P₀ ∧
      Integrable (fun ζ : Fin n → Ω => deletionMass ζ i) P₀ := by
    have hADm : Measurable[mN₀, borel ℝ]
        (fun ζ : Fin n → Ω => |A ζ - Adel ζ i|) := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hAm.sub (hAdelm i)).norm
    have hBDm : Measurable[mN₀, borel ℝ]
        (fun ζ : Fin n → Ω => |B ζ - Bdelete ζ i|) := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hBm.sub (hBdeletem i)).norm
    exact ⟨hADm, hBDm, hADm.add hBDm,
      (hAI.sub (hAdelI i)).abs, (hBI.sub (hBdeleteI i)).abs,
      ((hAI.sub (hAdelI i)).abs).add ((hBI.sub (hBdeleteI i)).abs)⟩
  have hTotalm : Measurable[mN₀, borel ℝ] deletionTotal :=
    Finset.measurable_sum Finset.univ
      (fun (i : Fin n) (_hi : i ∈ (Finset.univ : Finset (Fin n))) =>
        (hDiff i).2.2.1)
  have hTotalI : Integrable deletionTotal P₀ :=
    integrable_finsetSum Finset.univ
      (fun (i : Fin n) (_hi : i ∈ (Finset.univ : Finset (Fin n))) =>
        (hDiff i).2.2.2.2.2)
  have hAugDeleted (i : Fin n) :
      Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => Adel (q x) i) ∧
      Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => Bdelete (q x) i) ∧
      Integrable (fun x : Fin n → Ω × ℝ => Adel (q x) i) ν ∧
      Integrable (fun x : Fin n → Ω × ℝ => Bdelete (q x) i) ν ∧
      Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => |A (q x) - Adel (q x) i|) ∧
      Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => |B (q x) - Bdelete (q x) i|) ∧
      Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => deletionMass (q x) i) ∧
      Integrable (fun x : Fin n → Ω × ℝ => |A (q x) - Adel (q x) i|) ν ∧
      Integrable (fun x : Fin n → Ω × ℝ => |B (q x) - Bdelete (q x) i|) ν ∧
      Integrable (fun x : Fin n → Ω × ℝ => deletionMass (q x) i) ν := by
    rcases hDiff i with ⟨hADm, hBDm, hMassm, hADi, hBDi, hMassi⟩
    exact ⟨(hAdelm i).comp hqpres.measurable,
      (hBdeletem i).comp hqpres.measurable,
      hqpres.integrable_comp_of_integrable (hAdelI i),
      hqpres.integrable_comp_of_integrable (hBdeleteI i),
      hADm.comp hqpres.measurable, hBDm.comp hqpres.measurable,
      hMassm.comp hqpres.measurable,
      hqpres.integrable_comp_of_integrable hADi,
      hqpres.integrable_comp_of_integrable hBDi,
      hqpres.integrable_comp_of_integrable hMassi⟩
  have hweighted :=
    @Shao.OQ6.OriginalLevelDependentWeightedSourceCost.actual_original_level_dependent_weighted_source_cost
      Ω mΩ μ (inferInstance : @IsProbabilityMeasure Ω mΩ μ)
      h hh hh2 hhsymm hcenter hprojectionsecond n hn y hy hywindow 512 (by norm_num)
  dsimp only at hweighted
  rcases hweighted with ⟨hIoriginalPos, hFullOriginalI, hDeleteOriginalI,
    hCostOriginalNonneg, hCostOriginalBound⟩
  change 0 < Ioriginal at hIoriginalPos
  change Integrable (fun ζ => fullTest0 ζ * Real.exp (S0 ζ)) P at hFullOriginalI
  change ∀ i : Fin n,
    Integrable (fun ζ => deleteTest0 ζ i * Real.exp (S0delete ζ i)) P at hDeleteOriginalI
  change 0 ≤ costOriginal at hCostOriginalNonneg
  change costOriginal ≤
    64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + rho) *
      (1 + y) ^ 3 / Real.sqrt (n : ℝ) at hCostOriginalBound
  have hξ0m (i : Fin n) : Measurable[mN₀, borel ℝ] (ξ0 i) :=
    (hgcoord i).1.comp (hO i).1
  have hphase0m (j : Fin n) : Measurable[mN₀, borel ℝ]
      (fun ζ : Fin n → Ω => y * ξ0 j ζ - (y * ξ0 j ζ) ^ 2 / 2) :=
    ((hξ0m j).const_mul y).sub
      ((((hξ0m j).const_mul y).pow_const (2 : ℕ)).div_const 2)
  have hS0m : Measurable[mN₀, borel ℝ] S0 :=
    Finset.measurable_sum Finset.univ (fun j _ => hphase0m j)
  have hS0deletem (i : Fin n) :
      Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => S0delete ζ i) :=
    Finset.measurable_sum (Finset.univ.erase i) (fun j _ => hphase0m j)
  have hcap0m (i : Fin n) : Measurable[mN₀, borel ℝ]
      (fun ζ : Fin n → Ω => min |y * ξ0 i ζ| 1) := by
    simpa only [Real.norm_eq_abs] using
      ((hξ0m i).const_mul y).norm.min measurable_const
  have hFullWeightedm : Measurable[mN₀, borel ℝ]
      (fun ζ : Fin n → Ω => fullTest0 ζ * Real.exp (S0 ζ)) :=
    ((hAm.const_mul y).add (hBm.const_mul (y ^ 2))).mul hS0m.exp
  have hDeleteWeightedm (i : Fin n) : Measurable[mN₀, borel ℝ]
      (fun ζ : Fin n → Ω => deleteTest0 ζ i * Real.exp (S0delete ζ i)) :=
    ((hcap0m i).mul ((hDiff i).1.add ((hDiff i).2.1.const_mul y))).mul
      (hS0deletem i).exp
  have hSνpoint (x : Fin n → Ω × ℝ) : Sν x = S0 (q x) := by
    rfl
  have hSνdeletepoint (i : Fin n) (x : Fin n → Ω × ℝ) :
      Sνdelete x i = S0delete (q x) i := by
    rfl
  have hFullReducedI : Integrable (fun ζ => fullTest0 ζ * Real.exp (S0 ζ)) P₀ := by
    apply (hId.integrable_comp hFullWeightedm.aestronglyMeasurable).mp
    simpa only [Function.comp_def, id_eq] using hFullOriginalI
  have hDeleteReducedI (i : Fin n) :
      Integrable (fun ζ => deleteTest0 ζ i * Real.exp (S0delete ζ i)) P₀ := by
    apply (hId.integrable_comp (hDeleteWeightedm i).aestronglyMeasurable).mp
    simpa only [Function.comp_def, id_eq] using hDeleteOriginalI i
  have hFullCodedI : Integrable (fun x => fullTestν x * Real.exp (Sν x)) ν := by
    simpa only [Function.comp_def, fullTestν, hSνpoint] using
      hqpres.integrable_comp_of_integrable hFullReducedI
  have hDeleteCodedI (i : Fin n) :
      Integrable (fun x => deleteTestν x i * Real.exp (Sνdelete x i)) ν := by
    simpa only [Function.comp_def, deleteTestν, hSνdeletepoint] using
      hqpres.integrable_comp_of_integrable (hDeleteReducedI i)
  have hIreducedEq : Ireduced = Ioriginal := by
    change (∫ ζ, Real.exp (S0 ζ) ∂P₀) = ∫ ζ, Real.exp (S0 ζ) ∂P
    rw [hP₀map]
    exact integral_map hidN.aemeasurable hS0m.exp.aestronglyMeasurable
  have hIcodedEq : Icoded = Ioriginal := by
    change (∫ x, Real.exp (S0 (q x)) ∂ν) = Ioriginal
    calc
      _ = ∫ ζ, Real.exp (S0 ζ) ∂ν.map q :=
        (integral_map hqpres.measurable.aemeasurable hS0m.exp.aestronglyMeasurable).symm
      _ = Ireduced := by rw [hqpres.map_eq]
      _ = Ioriginal := hIreducedEq
  have hIreducedPos : 0 < Ireduced := by
    rw [hIreducedEq]
    exact hIoriginalPos
  have hIcodedPos : 0 < Icoded := by
    rw [hIcodedEq]
    exact hIoriginalPos
  have hFullReducedEq :
      (∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P₀) =
        ∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P := by
    rw [hP₀map]
    exact integral_map hidN.aemeasurable hFullWeightedm.aestronglyMeasurable
  have hFullCodedEq :
      (∫ x, fullTestν x * Real.exp (Sν x) ∂ν) =
        ∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P := by
    change (∫ x, fullTest0 (q x) * Real.exp (S0 (q x)) ∂ν) = _
    calc
      _ = ∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂ν.map q :=
        (integral_map hqpres.measurable.aemeasurable hFullWeightedm.aestronglyMeasurable).symm
      _ = ∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P₀ := by rw [hqpres.map_eq]
      _ = _ := hFullReducedEq
  have hDeleteReducedEq (i : Fin n) :
      (∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P₀) =
        ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P := by
    rw [hP₀map]
    exact integral_map hidN.aemeasurable (hDeleteWeightedm i).aestronglyMeasurable
  have hDeleteCodedEq (i : Fin n) :
      (∫ x, deleteTestν x i * Real.exp (Sνdelete x i) ∂ν) =
        ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P := by
    change (∫ x, deleteTest0 (q x) i * Real.exp (S0delete (q x) i) ∂ν) = _
    calc
      _ = ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂ν.map q :=
        (integral_map hqpres.measurable.aemeasurable
          (hDeleteWeightedm i).aestronglyMeasurable).symm
      _ = ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P₀ := by rw [hqpres.map_eq]
      _ = _ := hDeleteReducedEq i
  have hCostReducedEq : costReduced = costOriginal := by
    simp only [costReduced, costOriginal, hIreducedEq, hFullReducedEq, hDeleteReducedEq]
  have hCostCodedEq : costCoded = costOriginal := by
    simp only [costCoded, costOriginal, hIcodedEq, hFullCodedEq, hDeleteCodedEq]
  have hCostReducedNonneg : 0 ≤ costReduced := by
    rw [hCostReducedEq]
    exact hCostOriginalNonneg
  have hCostCodedNonneg : 0 ≤ costCoded := by
    rw [hCostCodedEq]
    exact hCostOriginalNonneg
  have hCostReducedBound : costReduced ≤
      64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + rho) *
        (1 + y) ^ 3 / Real.sqrt (n : ℝ) := by
    rw [hCostReducedEq]
    exact hCostOriginalBound
  have hCostCodedBound : costCoded ≤
      64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + rho) *
        (1 + y) ^ 3 / Real.sqrt (n : ℝ) := by
    rw [hCostCodedEq]
    exact hCostOriginalBound
  exact ⟨hP₀prob, hP₀map, hO, hOindep, hgcoord, hgenergy,
    hQid, hW0eq, hV0eq, hT0eq, hD1m, hD2m, hhalf,
    hTclipm, hTclipOriginal, hTcliplaw, hνprob, hqpres,
    hs, hηeval, hηindep, hηL2, hηInts, hηmean, hηenergy,
    hηnull, hVηnull, hpositiveDenominator, hCmeas, hCcomap,
    hfactor, hretained, hscalar, hdeletedFactor, hTηmeas,
    hZ0m, hZ0Original, hZmeas, hZcodedlaw, hZ0law,
    hZcodedreal, hsigned, hcomparison,
    hFullBounds, hDeletedBounds, hJm, hAm, hBm,
    (fun i : Fin n => ⟨(hDeletedMeasurable i).1, (hDeletedMeasurable i).2.1,
      hAdelm i, hBdeletem i⟩), hAI, hBI, heI,
    (fun i : Fin n => ⟨hAdelI i, hBdeleteI i, (hDiff i).1,
      (hDiff i).2.1, (hDiff i).2.2.1, (hDiff i).2.2.2.1,
      (hDiff i).2.2.2.2.1, (hDiff i).2.2.2.2.2⟩),
    hTotalm, hTotalI,
    hAm.comp hqpres.measurable, hBm.comp hqpres.measurable,
    hD2m.comp hqpres.measurable,
    hqpres.integrable_comp_of_integrable hAI,
    hqpres.integrable_comp_of_integrable hBI,
    hqpres.integrable_comp_of_integrable heI, hAugDeleted,
    hTotalm.comp hqpres.measurable,
    hqpres.integrable_comp_of_integrable hTotalI,
    hSνpoint, hSνdeletepoint, hIoriginalPos, hIreducedEq, hIcodedEq,
    hIreducedPos, hIcodedPos, hFullOriginalI, hDeleteOriginalI,
    hFullReducedI, hDeleteReducedI, hFullCodedI, hDeleteCodedI,
    hFullReducedEq, hFullCodedEq, hDeleteReducedEq, hDeleteCodedEq,
    hCostReducedEq, hCostCodedEq, hCostOriginalNonneg, hCostReducedNonneg,
    hCostCodedNonneg, hCostOriginalBound, hCostReducedBound, hCostCodedBound⟩

end

end Shao.OQ6.OriginalLevelDependentCanonicalCostPacket
