import Shao.OQ6.OriginalLevelDependentLiteralWeightedConsumer
import Shao.OQ6.IIDSourceStrictMomentBudgets
import Shao.OQ6.NormalizedStrictMomentBudgets

set_option autoImplicit false
universe u
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology MeasureTheory symmDiff
open Shao.OQ5.P51

namespace Shao.OQ6.OriginalLevelDependentStrictMomentFrontier
noncomputable section

theorem actual_original_level_dependent_strict_moment_frontier
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
      (∀ (n : ℕ) (hn : 4 ≤ n)
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
            (1 + y) ^ 3 / Real.sqrt (n : ℝ)) ∧
      ∀ (n : ℕ) (hn : 4 ≤ n)
          (z : ℝ) (hz : 1 ≤ z)
          (hwindow : z ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ))),
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
        let K : ℝ := 4 * Real.sqrt (n : ℝ)
        let ε : ℕ → ℝ := fun k => 1 / (8 * Real.sqrt (n : ℝ) * ((k : ℝ) + 1))
        let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => g (ζ i) / N
        let D1 : (Fin n → Ω) → ℝ := residualStatisticD n r
        let D2 : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r 512 rho z
        let T0 : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho z
        let A0 : (Fin n → Ω) → ℝ := fun ζ => |D1 ζ|
        let B0 : (Fin n → Ω) → ℝ := studentizerClipBudget n r 512 rho z
        let A0delete : Fin n → (Fin n → Ω) → ℝ :=
          fun i ζ => |residualStatisticDDeleted n r ζ i|
        let B0delete : Fin n → (Fin n → Ω) → ℝ :=
          fun i ζ => studentizerClipBudgetDeleted n r 512 rho z ζ i
        let lambda01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
        let mAugLocal : MeasurableSpace (Ω × ℝ) := m₀.prod (borel ℝ)
        let mAug : MeasurableSpace (Fin n → Ω × ℝ) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (fun _ : Fin n => mAugLocal)
        let νlocal : Fin n → @Measure (Ω × ℝ) mAugLocal :=
          fun _ => @Measure.prod Ω ℝ m₀ (borel ℝ) μ₀ lambda01
        let ν : @Measure (Fin n → Ω × ℝ) mAug :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (inferInstance : Fintype (Fin n)) (fun _ : Fin n => mAugLocal) νlocal
        let q : (Fin n → Ω × ℝ) → (Fin n → Ω) := fun x i => (x i).1
        let c : Fin n → (Ω × ℝ) → ℝ := fun _ =>
          Shao.OQ6.ScalarObservationCoding.baseFourIndicatorCode
            (MeasurableSpace.natGeneratingSequence (Ω × ℝ))
        let ξlocal : Fin n → (Ω × ℝ) → ℝ := fun i t => g t.1 / N
        let Ylocal : ℕ → Fin n → (Ω × ℝ) → ℝ := fun k i =>
          Shao.OQ6.QuantizedObservationCoding.quantizedObservation (ε k) (ξlocal i) (c i)
        let ξ : Fin n → (Fin n → Ω × ℝ) → ℝ := fun i x => ξlocal i (x i)
        let Y : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x => Ylocal k i (x i)
        let a : ℕ → Fin n → ℝ := fun k =>
          Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν (Y k)
        let s : ℕ → ℝ := fun k =>
          Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν (Y k)
        let ηlocal : ℕ → Fin n → (Ω × ℝ) → ℝ := fun k i =>
          Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation (a k i) (s k) (Ylocal k i)
        let η : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k =>
          Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
        let C : ℕ → (Fin n → Ω × ℝ) → (Fin n → ℝ) := fun k x i => η k i x
        let W : (Fin n → Ω × ℝ) → ℝ := fun x => ∑ i : Fin n, ξ i x
        let V : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (∑ i : Fin n, (ξ i x) ^ 2)
        let Wη : ℕ → (Fin n → Ω × ℝ) → ℝ := fun k x => ∑ i : Fin n, η k i x
        let Vη : ℕ → (Fin n → Ω × ℝ) → ℝ := fun k x => Real.sqrt (∑ i : Fin n, (η k i x) ^ 2)
        let b : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (1 + D2 (q x))
        let Qε : ℕ → (Fin n → Ω × ℝ) → ℝ :=
          fun k x => W x - Wη k x + z * b x * (Vη k x - V x)
        let Dη : ℕ → (Fin n → Ω × ℝ) → ℝ :=
          fun k x => D1 (q x) + W x - Wη k x + z * b x * (Vη k x - V x)
        let Tη : ℕ → (Fin n → Ω × ℝ) → ℝ := fun k x => (Wη k x + Dη k x) / (Vη k x * b x)
        let A : (Fin n → Ω × ℝ) → ℝ := fun x => A0 (q x)
        let B : (Fin n → Ω × ℝ) → ℝ := fun x => B0 (q x)
        let Adelete : Fin n → (Fin n → Ω × ℝ) → ℝ := fun i x => A0delete i (q x)
        let Bdelete : Fin n → (Fin n → Ω × ℝ) → ℝ := fun i x => B0delete i (q x)
        let Vdelete : Fin n → (Fin n → Ω × ℝ) → ℝ :=
          fun i x => Real.sqrt (∑ j ∈ Finset.univ.erase i, (ξ j x) ^ 2)
        let H : (Fin n → Ω × ℝ) → ℝ :=
          fun x => (1 + V x) * (N + z * Real.sqrt (1 + B x))
        let Hdelete : Fin n → (Fin n → Ω × ℝ) → ℝ :=
          fun i x => (1 + Vdelete i x) * (N + z * Real.sqrt (1 + Bdelete i x))
        let M : ℕ → (Fin n → Ω × ℝ) → ℝ := fun k x => K * ε k * H x
        let Mdelete : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x => K * ε k * Hdelete i x
        let Anew : ℕ → (Fin n → Ω × ℝ) → ℝ := fun k x => A x + M k x
        let AdeleteNew : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x => Adelete i x + Mdelete k i x
        let Δ : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ :=
          fun k i x => (Anew k x - AdeleteNew k i x) - (A x - Adelete i x)
        let ℓ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => z * ξ0 i ζ - (z * ξ0 i ζ) ^ 2 / 2
        let ℓη : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x => z * η k i x - (z * η k i x) ^ 2 / 2
        let S0 : (Fin n → Ω) → ℝ := fun ζ => ∑ i : Fin n, ℓ0 i ζ
        let Sη : ℕ → (Fin n → Ω × ℝ) → ℝ := fun k x => ∑ i : Fin n, ℓη k i x
        let S0minus : Fin n → (Fin n → Ω) → ℝ := fun i ζ => ∑ j ∈ Finset.univ.erase i, ℓ0 j ζ
        let Sηminus : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x => ∑ j ∈ Finset.univ.erase i, ℓη k j x
        let I0 : ℝ := ∫ ζ, Real.exp (S0 ζ) ∂P
        let Iη : ℕ → ℝ := fun k => ∫ x, Real.exp (Sη k x) ∂ν
        let fullTest0 : (Fin n → Ω) → ℝ := fun ζ => z * A0 ζ + z ^ 2 * B0 ζ
        let fullTestη : ℕ → (Fin n → Ω × ℝ) → ℝ := fun k x => z * Anew k x + z ^ 2 * B x
        let deletedTest0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ =>
          min |z * ξ0 i ζ| 1 * (|A0 ζ - A0delete i ζ| + z * |B0 ζ - B0delete i ζ|)
        let deletedTestη : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x =>
          min |z * η k i x| 1 * (|Anew k x - AdeleteNew k i x| + z * |B x - Bdelete i x|)
        let compactDeletedTest0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ =>
          min |ξ0 i ζ| (1 + z)⁻¹ * (|A0 ζ - A0delete i ζ| + z * |B0 ζ - B0delete i ζ|)
        let compactDeletedTestη : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x =>
          min |η k i x| (1 + z)⁻¹ * (|Anew k x - AdeleteNew k i x| + z * |B x - Bdelete i x|)
        let Lcompact0 : ℝ := ∑ i : Fin n,
          ∫ ζ, ((1 + z) * ξ0 i ζ) ^ 2 * min |(1 + z) * ξ0 i ζ| 1 ∂P
        let Lcompactη : ℕ → ℝ := fun k => ∑ i : Fin n,
          ∫ x, ((1 + z) * η k i x) ^ 2 * min |(1 + z) * η k i x| 1 ∂ν
        let sourceCost0 : ℝ :=
          ((∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P) +
            ∑ i : Fin n, ∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P) / I0
        let sourceCostη : ℕ → ℝ := fun k =>
          ((∫ x, fullTestη k x * Real.exp (Sη k x) ∂ν) +
            ∑ i : Fin n, ∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν) / Iη k
        let compactCost0 : ℝ := Lcompact0 + (∫ ζ, A0 ζ ∂P) + z * (∫ ζ, B0 ζ ∂P) +
          ∑ i : Fin n, ∫ ζ, compactDeletedTest0 i ζ ∂P
        let compactCostη : ℕ → ℝ := fun k => Lcompactη k + (∫ x, Anew k x ∂ν) +
          z * (∫ x, B x ∂ν) + ∑ i : Fin n, ∫ x, compactDeletedTestη k i x ∂ν
        (
        @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ ∧
        P₀ = @Measure.map (Fin n → Ω) (Fin n → Ω) mN mN₀ id P ∧
        IsProbabilityMeasure ν ∧ MeasurePreserving q ν P₀ ∧
        (∀ k : ℕ, 0 < ε k ∧ ε k < 1 / (4 * Real.sqrt (n : ℝ))) ∧
        Filter.Tendsto ε Filter.atTop (nhds (0 : ℝ)) ∧
        (∀ i : Fin n, Measurable[mAug, borel ℝ] (ξ i) ∧ MemLp (ξ i) 2 ν ∧
          (∫ x, ξ i x ∂ν) = 0) ∧
        (∑ i : Fin n, ∫ x, (ξ i x) ^ 2 ∂ν) = 1 ∧
        (∀ (k : ℕ) (i : Fin n), Measurable[mAugLocal, borel ℝ] (Ylocal k i) ∧
          Measurable[mAug, borel ℝ] (Y k i) ∧ ∀ x : Fin n → Ω × ℝ, |Y k i x - ξ i x| ≤ ε k) ∧
        (∀ ζ : Fin n → Ω, (1 / 2 : ℝ) ≤ 1 + D2 ζ ∧ |D2 ζ| ≤ B0 ζ) ∧
        (∀ ζ : Fin n → Ω, projectionV n g ζ = 0 → T0 ζ = 0) ∧
        (∀ (k : ℕ) (x : Fin n → Ω × ℝ), Vη k x = 0 → Tη k x = 0) ∧
        (∀ k : ℕ, (1 / 2 : ℝ) < s k ∧
          (∀ (i : Fin n) (x : Fin n → Ω × ℝ), η k i x = ηlocal k i (x i)) ∧
          iIndepFun (η k) ν ∧
          (∀ i : Fin n, Measurable[mAug, borel ℝ] (η k i) ∧ MemLp (η k i) 2 ν ∧
            (∫ x, η k i x ∂ν) = 0) ∧
          (∑ i : Fin n, ∫ x, (η k i x) ^ 2 ∂ν) = 1 ∧
          ν {x : Fin n → Ω × ℝ | Vη k x = 0} = 0 ∧
          (∀ᵐ x ∂ν, 0 < Vη k x ∧ 0 < b x ∧ 0 < Vη k x * b x)) ∧
        (∀ (k : ℕ) (x : Fin n → Ω × ℝ),
          Dη k x = D1 (q x) + Qε k x ∧
          Wη k x + Dη k x - z * Vη k x * b x = W x + D1 (q x) - z * V x * b x ∧
          |Qε k x| ≤ M k x ∧ |Dη k x| ≤ Anew k x) ∧
        Measurable[mAug, borel ℝ] H ∧ Integrable[mAug] H ν ∧
        (∀ i : Fin n, Measurable[mAug, borel ℝ] (Hdelete i) ∧ Integrable[mAug] (Hdelete i) ν) ∧
        (∀ k : ℕ, Measurable[mAug, borel ℝ] (Qε k) ∧ Integrable[mAug] (Qε k) ν ∧
          Integrable[mAug] (fun x => |Qε k x|) ν ∧
          (∫ x, |Qε k x| ∂ν) ≤ K * ε k * (∫ x, H x ∂ν)) ∧
        Filter.Tendsto (fun k => ∫ x, |Qε k x| ∂ν) Filter.atTop (nhds (0 : ℝ)) ∧
        (∀ k : ℕ, Measurable[mAug, borel ℝ] (Anew k) ∧ Integrable[mAug] (Anew k) ν ∧
          ∀ x : Fin n → Ω × ℝ, 0 ≤ Anew k x) ∧
        (∀ (k : ℕ) (i : Fin n), Measurable[mAug, borel ℝ] (AdeleteNew k i) ∧
          Integrable[mAug] (AdeleteNew k i) ν ∧ ∀ x : Fin n → Ω × ℝ, 0 ≤ AdeleteNew k i x) ∧
        (∀ k : ℕ, Integrable[mAug] (fun x => |Anew k x - A x|) ν ∧
          (∫ x, |Anew k x - A x| ∂ν) = ε k * (K * (∫ x, H x ∂ν))) ∧
        (∀ (k : ℕ) (i : Fin n), Integrable[mAug] (fun x => |AdeleteNew k i x - Adelete i x|) ν ∧
          (∫ x, |AdeleteNew k i x - Adelete i x| ∂ν) = ε k * (K * (∫ x, Hdelete i x ∂ν))) ∧
        Filter.Tendsto (fun k => ∫ x, |Anew k x - A x| ∂ν) Filter.atTop (nhds (0 : ℝ)) ∧
        (∀ i : Fin n, Filter.Tendsto (fun k => ∫ x, |AdeleteNew k i x - Adelete i x| ∂ν)
          Filter.atTop (nhds (0 : ℝ))) ∧
        (∀ (k : ℕ) (i : Fin n) (x : Fin n → Ω × ℝ),
          Δ k i x = M k x - Mdelete k i x ∧ |Δ k i x| ≤ M k x + Mdelete k i x) ∧
        (∀ (k : ℕ) (i : Fin n), Integrable[mAug] (fun x => |Δ k i x|) ν ∧
          (∫ x, |Δ k i x| ∂ν) ≤ ε k * (K * ((∫ x, H x ∂ν) + (∫ x, Hdelete i x ∂ν)))) ∧
        (∀ k : ℕ, ∃ Ffull : (Fin n → ℝ) → ℝ × ℝ × ℝ,
          Measurable[borel (Fin n → ℝ), borel (ℝ × ℝ × ℝ)] Ffull ∧
          ∀ x : Fin n → Ω × ℝ, (M k x, Anew k x, B x) = Ffull (C k x)) ∧
        (∀ (k : ℕ) (i : Fin n), ∃ Fdelete : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ,
          Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdelete ∧
          ∀ x : Fin n → Ω × ℝ,
            (Mdelete k i x, AdeleteNew k i x, Bdelete i x) =
              Fdelete (fun j : {j : Fin n // j ≠ i} => η k j.val x)) ∧
        (∀ k : ℕ, ∃ G1 G2 : (Fin n → ℝ) → ℝ,
          Measurable[borel (Fin n → ℝ), borel ℝ] G1 ∧
          Measurable[borel (Fin n → ℝ), borel ℝ] G2 ∧
          ∀ x : Fin n → Ω × ℝ, Dη k x = G1 (C k x) ∧ D2 (q x) = G2 (C k x)) ∧
        Integrable[mN] (fun ζ => fullTest0 ζ * Real.exp (S0 ζ)) P ∧
        (∀ k : ℕ, Integrable[mAug] (fun x => fullTestη k x * Real.exp (Sη k x)) ν) ∧
        (∀ i : Fin n, Integrable[mN] (fun ζ => deletedTest0 i ζ * Real.exp (S0minus i ζ)) P) ∧
        (∀ (k : ℕ) (i : Fin n), Integrable[mAug] (fun x => deletedTestη k i x * Real.exp (Sηminus k i x)) ν) ∧
        (∀ i : Fin n, Integrable[mN] (compactDeletedTest0 i) P) ∧
        (∀ (k : ℕ) (i : Fin n), Integrable[mAug] (compactDeletedTestη k i) ν) ∧
        0 < I0 ∧ (∀ k : ℕ, 0 < Iη k) ∧
        Filter.Tendsto Iη Filter.atTop (nhds I0) ∧
        Filter.Tendsto (fun k => ∫ x, fullTestη k x * Real.exp (Sη k x) ∂ν)
          Filter.atTop (nhds (∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P)) ∧
        (∀ i : Fin n, Filter.Tendsto (fun k => ∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν)
          Filter.atTop (nhds (∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P))) ∧
        Filter.Tendsto (fun k => (∫ x, fullTestη k x * Real.exp (Sη k x) ∂ν) / Iη k)
          Filter.atTop (nhds ((∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P) / I0)) ∧
        (∀ i : Fin n, Filter.Tendsto (fun k => (∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν) / Iη k)
          Filter.atTop (nhds ((∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P) / I0))) ∧
        (∀ i : Fin n, Filter.Tendsto (fun k => ∫ x, compactDeletedTestη k i x ∂ν)
          Filter.atTop (nhds (∫ ζ, compactDeletedTest0 i ζ ∂P))) ∧
        Filter.Tendsto sourceCostη Filter.atTop (nhds sourceCost0) ∧
        Filter.Tendsto compactCostη Filter.atTop (nhds compactCost0) ∧
        0 ≤ sourceCost0 ∧
        sourceCost0 ≤
          64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) *
            (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ) ∧
        (∀ δ : ℝ, 0 < δ → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
          sourceCostη k ≤
            64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) *
              (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ) + δ)
        ) ∧
        ∀ (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
          (hgp : Integrable[mΩ] (fun o : Ω => Real.rpow |g o| p) μ)
          (cBudget : ℝ) (hcBudget : 0 < cBudget),
        let β : ℝ := ∫ o : Ω, Real.rpow |g o| p ∂μ
        let cWindow : ℝ := Real.rpow (min (1 / 2 : ℝ) cBudget / 2) (1 / p)
        let Fz : ℝ → ℝ := fun t => (z * t) ^ 2 * min |z * t| 1
        let δoriginal : Fin n → ℝ := fun i => ∫ ζ, Fz (ξ0 i ζ) ∂P
        let δ0 : Fin n → ℝ := fun i => ∫ x, Fz (ξ i x) ∂ν
        let δη : ℕ → Fin n → ℝ := fun k i => ∫ x, Fz (η k i x) ∂ν
        let Loriginal : ℝ := ∑ i : Fin n, δoriginal i
        let L0 : ℝ := ∑ i : Fin n, δ0 i
        let Lη : ℕ → ℝ := fun k => ∑ i : Fin n, δη k i
        0 ≤ β ∧ 0 < cWindow ∧
        Real.rpow cWindow p = min (1 / 2 : ℝ) cBudget / 2 ∧
        Real.rpow cWindow p < min (1 / 2 : ℝ) cBudget ∧
        (∀ i : Fin n, Integrable[mN] (fun ζ => Fz (ξ0 i ζ)) P) ∧
        (∀ i : Fin n, Integrable[mAug] (fun x => Fz (ξ i x)) ν) ∧
        (∀ i : Fin n, δ0 i = δoriginal i) ∧
        L0 = Loriginal ∧
        (∀ i : Fin n, 0 ≤ δ0 i) ∧ 0 ≤ L0 ∧
        L0 ≤ β * Real.rpow z p / Real.rpow (n : ℝ) ((p - 2) / 2) ∧
        (β = 0 → L0 = 0 ∧ ∀ i : Fin n, δ0 i = 0) ∧
        ((β = 0 ∨ (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
            Real.rpow (n : ℝ) ((p - 2) / (2 * p)))) →
          (∀ i : Fin n, δ0 i < (1 / 2 : ℝ)) ∧
          L0 < cBudget * z ^ 2 ∧
          (∀ (k : ℕ) (i : Fin n),
            Integrable[mAug] (fun x => Fz (η k i x)) ν) ∧
          (∀ i : Fin n, Filter.Tendsto (fun k => δη k i)
            Filter.atTop (nhds (δ0 i))) ∧
          Filter.Tendsto Lη Filter.atTop (nhds L0) ∧
          (∀ (τ δ : ℝ), 0 < τ → 0 < δ →
            ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
              (∀ i : Fin n, δη k i < (1 / 2 : ℝ)) ∧
              Lη k < cBudget * z ^ 2 ∧
              (∫ x, |Qε k x| ∂ν) < τ ∧
              |sourceCostη k - sourceCost0| < τ ∧
              |compactCostη k - compactCost0| < τ ∧
              sourceCostη k ≤
                64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) *
                  (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ) + δ))
:= by
  classical
  intro g r v rho
  -- Establish these facts in the original measurable space before selecting m₀.
  have hgOriginal : Measurable[mΩ, borel ℝ] g :=
    hh.stronglyMeasurable.integral_prod_right'.measurable
  have hgSecond : (∫ o, g o ^ 2 ∂μ) = 1 := hprojectionsecond
  have hgSquareIntegrable : Integrable[mΩ] (fun o => g o ^ 2) μ := by
    by_contra hnot
    have hzero : (∫ o, g o ^ 2 ∂μ) = 0 := integral_undef hnot
    exact one_ne_zero (hgSecond.symm.trans hzero)
  have hg2Original : MemLp g 2 μ :=
    (memLp_two_iff_integrable_sq hgOriginal.aestronglyMeasurable).2
      hgSquareIntegrable
  have hOriginal :=
    Shao.OQ6.OriginalLevelDependentLiteralWeightedConsumer.actual_original_level_dependent_literal_weighted_consumer
      μ h hh hh2 hhsymm hcenter hprojectionsecond
  dsimp only at hOriginal
  rcases hOriginal with ⟨m₀, hm₀, hcg, hbase⟩
  refine ⟨m₀, hm₀, hcg, ?_⟩
  intro μ₀
  letI : MeasurableSpace Ω := m₀
  letI : MeasurableSpace.CountablyGenerated Ω := hcg
  rcases hbase with ⟨hμ₀prob, hfor, hconsumer⟩
  letI : IsProbabilityMeasure μ₀ := hμ₀prob
  -- Both retained packets use this one witness, selected before p and cBudget.
  refine ⟨hμ₀prob, hfor, ?_⟩
  intro n hn z hz hwindow
  intro mN mN₀ P P₀ N K ε ξ0 D1 D2 T0 A0 B0 A0delete B0delete
    lambda01 mAugLocal mAug νlocal ν q c ξlocal Ylocal ξ Y a s ηlocal η C
    W V Wη Vη b Qε Dη Tη A B Adelete Bdelete Vdelete H Hdelete
    M Mdelete Anew AdeleteNew Δ ℓ0 ℓη S0 Sη S0minus Sηminus I0 Iη
    fullTest0 fullTestη deletedTest0 deletedTestη compactDeletedTest0
    compactDeletedTestη Lcompact0 Lcompactη sourceCost0 sourceCostη compactCost0 compactCostη
  have hAnalytic := hconsumer n hn z hz hwindow
  refine ⟨hAnalytic, ?_⟩
  rcases hAnalytic with
    ⟨hP₀prob, hP₀map, hνprob, hq, hε, hεlim, hξPacket, hξenergy, hYpacket,
      hD2bounds, hT0zero, hTηzero, hηpacket, hSigned, hHm, hHint, hHd,
      hQspec, hQlim, hAnew, hAdnew, hAnewL1, hAdnewL1, hAlim, hAdlim,
      hΔeq, hΔI, hFullFactor, hDeletedFactor, hRemainderFactor,
      hFullI, hFullηI, hDelI, hDelηI, hCompactI, hCompactηI,
      hIpos, hIηpos, hIlim, hFullLim, hDelLim, hFullRatio, hDelRatio,
      hCompactLim, hSourceLim, hCostLim, hSourceNonneg, hSourceBound,
      hSourceEventually⟩
  letI : @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ := hP₀prob
  letI : @IsProbabilityMeasure (Fin n → Ω × ℝ) mAug ν := hνprob
  change @MeasurePreserving (Fin n → Ω × ℝ) (Fin n → Ω) mAug mN₀ q ν P₀ at hq
  have hn1 : 1 ≤ n := by omega
  have hPacket0 := hfor n hn z hz hwindow (ε 0) (hε 0).1 (hε 0).2
  rcases hPacket0 with
    ⟨hPacketP₀prob, hPacketP₀map, hO, hOindep, hgcoord, hPacketRest⟩
  have hξ0Reduced (i : Fin n) : Measurable[mN₀, borel ℝ] (ξ0 i) :=
    ((hgcoord i).1).comp (hO i).1
  have hidΩ : Measurable[mΩ, m₀] (id : Ω → Ω) := measurable_id'' hm₀
  have hidN : Measurable[mN, mN₀] (id : (Fin n → Ω) → (Fin n → Ω)) := by
    apply (@measurable_pi_iff (Fin n → Ω) (Fin n) (fun _ : Fin n => Ω)
      mN (fun _ : Fin n => m₀) (id : (Fin n → Ω) → (Fin n → Ω))).2
    intro i
    exact hidΩ.comp
      (@measurable_pi_apply (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => mΩ) i)
  have hId : @MeasurePreserving (Fin n → Ω) (Fin n → Ω) mN mN₀ id P P₀ :=
    @MeasurePreserving.mk (Fin n → Ω) (Fin n → Ω) mN mN₀ id P P₀
      hidN hP₀map.symm
  intro p hp2 hp3 hgp cBudget hcBudget
  intro β cWindow Fz δoriginal δ0 δη Loriginal L0 Lη
  -- The moment hypothesis and β belong to the original μ, never to μ₀.
  have hOriginalBudget :=
    @Shao.OQ6.IIDSourceStrictMomentBudgets.actual_iid_source_z_strict_moment_budgets
      Ω mΩ μ (inferInstance : @IsProbabilityMeasure Ω mΩ μ)
      g hgOriginal hg2Original p hp2 hp3 hgp cBudget hcBudget
  dsimp only at hOriginalBudget
  rcases hOriginalBudget with ⟨hβ, hcWindow, hcWindowPower, hcWindowSmall, hSource⟩
  rcases hSource n hn1 z hz with
    ⟨hPprob, hScalarI, hSourceI, hδScalar, hLScalar, hLi, hδNonneg,
      hLNonneg, hRate, hZero, hSourceStrict⟩
  change @IsProbabilityMeasure (Fin n → Ω) mN P at hPprob
  change (∀ i : Fin n, Integrable[mN] (fun ζ => Fz (ξ0 i ζ)) P) at hSourceI
  change (∀ i : Fin n, 0 ≤ δoriginal i) at hδNonneg
  change 0 ≤ Loriginal at hLNonneg
  change Loriginal ≤ β * Real.rpow z p / Real.rpow (n : ℝ) ((p - 2) / 2) at hRate
  change (β = 0 → Loriginal = 0 ∧ (∀ i : Fin n, δoriginal i = 0)) at hZero
  have hFzReduced (i : Fin n) :
      Measurable[mN₀, borel ℝ] (fun ζ => Fz (ξ0 i ζ)) := by
    exact ((measurable_const.mul (hξ0Reduced i)).pow_const 2).mul
      ((continuous_abs.measurable.comp
        (measurable_const.mul (hξ0Reduced i))).min measurable_const)
  have hOriginalIntegral (i : Fin n) :
      (∫ ζ, Fz (ξ0 i ζ) ∂P₀) = δoriginal i := by
    have hm :=
      @integral_map_of_stronglyMeasurable (Fin n → Ω) ℝ
        (inferInstance : NormedAddCommGroup ℝ) (inferInstance : NormedSpace ℝ ℝ)
        mN P (Fin n → Ω) mN₀ id hidN (fun ζ => Fz (ξ0 i ζ))
        ((hFzReduced i).stronglyMeasurable :
          StronglyMeasurable (fun ζ => Fz (ξ0 i ζ)))
    rw [hP₀map.symm] at hm
    simpa only [δoriginal, Function.comp_def, id_eq] using hm
  have hAugIntegral (i : Fin n) :
      δ0 i = (∫ ζ, Fz (ξ0 i ζ) ∂P₀) := by
    have hm :=
      @integral_map (Fin n → Ω × ℝ) ℝ
        (inferInstance : NormedAddCommGroup ℝ) (inferInstance : NormedSpace ℝ ℝ)
        mAug ν (Fin n → Ω) mN₀ q hq.aemeasurable (fun ζ => Fz (ξ0 i ζ))
        ((hFzReduced i).aestronglyMeasurable :
          AEStronglyMeasurable (fun ζ => Fz (ξ0 i ζ))
            (@Measure.map (Fin n → Ω × ℝ) (Fin n → Ω) mAug mN₀ q ν))
    rw [hq.map_eq] at hm
    simpa only [δ0, Function.comp_def, ξ, ξlocal, ξ0, q] using hm.symm
  have hReducedI (i : Fin n) :
      Integrable[mN₀] (fun ζ => Fz (ξ0 i ζ)) P₀ :=
    (hId.integrable_comp (hFzReduced i).aestronglyMeasurable).1 (hSourceI i)
  have hAugI (i : Fin n) : Integrable[mAug] (fun x => Fz (ξ i x)) ν := by
    have hi := hq.integrable_comp_of_integrable (hReducedI i)
    simpa only [Function.comp_def, ξ, ξlocal, ξ0, q] using hi
  have hδJoin (i : Fin n) : δ0 i = δoriginal i :=
    (hAugIntegral i).trans (hOriginalIntegral i)
  have hLJoin : L0 = Loriginal :=
    Finset.sum_congr rfl (fun i _ => hδJoin i)
  have hδ0Nonneg (i : Fin n) : 0 ≤ δ0 i := by
    rw [hδJoin i]
    exact hδNonneg i
  have hL0Nonneg : 0 ≤ L0 := by
    rw [hLJoin]
    exact hLNonneg
  have hRate0 : L0 ≤ β * Real.rpow z p / Real.rpow (n : ℝ) ((p - 2) / 2) := by
    rw [hLJoin]
    exact hRate
  have hZero0 : β = 0 → L0 = 0 ∧ (∀ i : Fin n, δ0 i = 0) := by
    intro hβzero
    refine ⟨hLJoin.trans (hZero hβzero).1, ?_⟩
    intro i
    exact (hδJoin i).trans ((hZero hβzero).2 i)
  refine ⟨hβ, hcWindow, hcWindowPower, hcWindowSmall, hSourceI, hAugI,
    hδJoin, hLJoin, hδ0Nonneg, hL0Nonneg, hRate0, hZero0, ?_⟩
  intro hMomentWindow
  rcases hSourceStrict hMomentWindow with ⟨hLc, hδHalf, hLStrict⟩
  change (∀ i : Fin n, δoriginal i < (1 / 2 : ℝ)) at hδHalf
  change Loriginal < cBudget * z ^ 2 at hLStrict
  have hδ0Half : ∀ i : Fin n, δ0 i < (1 / 2 : ℝ) := by
    intro i
    rw [hδJoin i]
    exact hδHalf i
  have hL0Strict : L0 < cBudget * z ^ 2 := by
    rw [hLJoin]
    exact hLStrict
  have hNormalized :=
    @Shao.OQ6.NormalizedStrictMomentBudgets.actual_source_z_strict_truncated_moment_budgets
      (Fin n → Ω × ℝ) mAug ν hνprob n hn1 ξ
      (fun i => (hξPacket i).1) (fun i => (hξPacket i).2.1)
      (fun i => (hξPacket i).2.2) hξenergy Y
      (fun k i => (hYpacket k i).2.1) ε
      (fun k => (hε k).1) (fun k => (hε k).2) hεlim
      (fun k i => (hYpacket k i).2.2) z hz cBudget hcBudget
  dsimp only at hNormalized
  rcases hNormalized hδ0Half hL0Strict with
    ⟨hδ0I, hδηI, hδlim, hLlim, kStrict, hkStrict⟩
  change (∀ (k : ℕ) (i : Fin n),
    Integrable[mAug] (fun x => Fz (η k i x)) ν) at hδηI
  change (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => δη k i)
    Filter.atTop (nhds (δ0 i))) at hδlim
  change Filter.Tendsto Lη Filter.atTop (nhds L0) at hLlim
  change (∀ k : ℕ, kStrict ≤ k →
    (∀ i : Fin n, δη k i < (1 / 2 : ℝ)) ∧ Lη k < cBudget * z ^ 2) at hkStrict
  refine ⟨hδ0Half, hL0Strict, hδηI, hδlim, hLlim, ?_⟩
  intro τ δ hτ hδ
  have hStrictEvent : ∀ᶠ k : ℕ in Filter.atTop,
      (∀ i : Fin n, δη k i < (1 / 2 : ℝ)) ∧ Lη k < cBudget * z ^ 2 :=
    Filter.eventually_atTop.2 ⟨kStrict, hkStrict⟩
  have hQEvent : ∀ᶠ k : ℕ in Filter.atTop, (∫ x, |Qε k x| ∂ν) < τ :=
    hQlim.eventually (eventually_lt_nhds hτ)
  have hSourceEvent : ∀ᶠ k : ℕ in Filter.atTop,
      |sourceCostη k - sourceCost0| < τ := by
    change Filter.Tendsto sourceCostη Filter.atTop (nhds sourceCost0) at hSourceLim
    exact (hSourceLim.sub_const sourceCost0).abs.eventually
      (by simpa only [sub_self, abs_zero] using (eventually_lt_nhds hτ))
  have hCostEvent : ∀ᶠ k : ℕ in Filter.atTop,
      |compactCostη k - compactCost0| < τ := by
    change Filter.Tendsto compactCostη Filter.atTop (nhds compactCost0) at hCostLim
    exact (hCostLim.sub_const compactCost0).abs.eventually
      (by simpa only [sub_self, abs_zero] using (eventually_lt_nhds hτ))
  have hSourceBoundEvent : ∀ᶠ k : ℕ in Filter.atTop,
      sourceCostη k ≤
        64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) *
          (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ) + δ :=
    Filter.eventually_atTop.2 (hSourceEventually δ hδ)
  have hJointEventually : ∀ᶠ k : ℕ in Filter.atTop,
      (∀ i : Fin n, δη k i < (1 / 2 : ℝ)) ∧
      Lη k < cBudget * z ^ 2 ∧
      (∫ x, |Qε k x| ∂ν) < τ ∧
      |sourceCostη k - sourceCost0| < τ ∧
      |compactCostη k - compactCost0| < τ ∧
      sourceCostη k ≤
        64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) *
          (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ) + δ := by
    filter_upwards [hStrictEvent, hQEvent, hSourceEvent, hCostEvent, hSourceBoundEvent]
      with k hkStrictTail hkQ hkSource hkCost hkSourceBound
    exact ⟨hkStrictTail.1, hkStrictTail.2, hkQ, hkSource, hkCost, hkSourceBound⟩
  exact Filter.eventually_atTop.1 hJointEventually


end

end Shao.OQ6.OriginalLevelDependentStrictMomentFrontier
