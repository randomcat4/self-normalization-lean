import Shao.OQ6.OriginalLevelDependentStrictMomentFrontier
import Shao.OQ6.OriginalCurrentLevelGoodsetPhysicalPayment
import Shao.OQ6.NormalizedUpperErrorGoodsetPayment
import Shao.OQ6.ActualQuadraticTiltMoments

set_option autoImplicit false
universe u
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology MeasureTheory symmDiff
open Shao.OQ5.P51

namespace Shao.OQ6.OriginalLevelDependentUpperPhysicalFrontier
noncomputable section
theorem actual_original_level_dependent_upper_physical_frontier
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
      (
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
      ) ∧
      ∃ cg : ℝ, 0 < cg ∧
      ∀ (Cenv aenv t0 Menv : ℝ)
        (hCenv : 0 ≤ Cenv) (haenv : 0 ≤ aenv)
        (ht0 : 0 < t0) (hMenv : 0 ≤ Menv),
        ∀ᶠ n : ℕ in Filter.atTop,
          4 ≤ n ∧
          ∀ (w : Ω → ℝ)
            (hW : ∀ᵐ o : Ω ∂μ, 0 ≤ w o)
            (hWR : ∀ᵐ o : Ω ∂μ, w o ≤ boundedPolylogHeight Cenv aenv n)
            (hSq : Integrable[mΩ] (fun o : Ω => (w o) ^ (2 : ℕ)) μ)
            (hSqBound : (∫ o : Ω, (w o) ^ (2 : ℕ) ∂μ) ≤ Menv)
            (hEnv : ∀ᵐ t : Ω × Ω ∂(@Measure.prod Ω Ω mΩ mΩ μ μ),
              |r t.1 t.2| ≤ w t.1 * w t.2)
            (z : ℝ) (hz : 1 ≤ z)
            (hTiltWindow : z ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ)))
            (hEnvelopeWindow : z ≤ remainderWindowScale
              (Shao.OQ6.BoundedProductEnvelopeTails.tailScale Menv) t0 *
                Real.rpow (n : ℝ) (1 / 6 : ℝ))
            (hGeometry : (1 + rho) * z ≤ Real.sqrt (n : ℝ)),
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
        let V0 : (Fin n → Ω) → ℝ := projectionV n g
        let qOrder : ℝ := boundedPolylogMomentOrder t0 n
        let Ktail : ℝ := Shao.OQ6.BoundedProductEnvelopeTails.tailScale Menv
        let Gsource : Set (Fin n → Ω) := projectionGood n g z
        let C2source : Set (Fin n → Ω) :=
          {ζ : Fin n → Ω |
            |Shao.OQ6.CanonicalDoubleGhostScalarMoments.originalUpper n r ζ| ≤
              Ktail * (n : ℝ) * qOrder ∧
            ‖Shao.OQ6.CanonicalDoubleGhostRowMoments.originalRows n r ζ‖ ^ (2 : ℕ) ≤
              Ktail * (n : ℝ) ^ (2 : ℕ) * qOrder}
        let Hsource : Set (Fin n → Ω) := Gsource ∩ C2source
        let Ssafe : Set (Fin n → Ω) :=
          {ζ : Fin n → Ω |
            0 < V0 ζ ∧ z * |D1 ζ| ≤ V0 ζ / 8 ∧
              z ^ (2 : ℕ) * |D2 ζ| ≤ (1 / 8 : ℝ)}
        let Jsafe : Set (Fin n → Ω × ℝ) := q ⁻¹' Ssafe
        let E : ℕ → Set (Fin n → Ω × ℝ) := fun k =>
          {x : Fin n → Ω × ℝ | z * |Dη k x| > Vη k x / 4}
        let E2 : Set (Fin n → Ω × ℝ) :=
          {x : Fin n → Ω × ℝ | z ^ (2 : ℕ) * |D2 (q x)| > (1 / 4 : ℝ)}
        let Z : Set (Fin n → Ω × ℝ) := {x : Fin n → Ω × ℝ | V x = 0}
        let physical : (Fin n → Ω) → ℝ := fun ζ : Fin n → Ω =>
          if Real.sqrt (centeredSq n g r ζ) = 0 then 0 else
            (projectionW n g ζ + D1 ζ) / Real.sqrt (centeredSq n g r ζ)
        let Eclip : Set (Fin n → Ω) := {ζ : Fin n → Ω | T0 ζ ≠ physical ζ}
        let E2original : Set (Fin n → Ω) :=
          {ζ : Fin n → Ω | z ^ (2 : ℕ) * |D2 ζ| > (1 / 4 : ℝ)}
        let Z0 : Set (Fin n → Ω) := {ζ : Fin n → Ω | V0 ζ = 0}
        let Zphysical : Set (Fin n → Ω) :=
          {ζ : Fin n → Ω | Real.sqrt (centeredSq n g r ζ) = 0}
        let physicalBad : Set (Fin n → Ω) := E2original ∪ Z0 ∪ Eclip ∪ Zphysical
        let payment : ℝ :=
          (3 : ℝ) * Real.exp (-qOrder) + Real.exp (-cg * (n : ℝ)) +
            (4 : ℝ) * Real.exp (-(z * Real.sqrt (n : ℝ)) / (2 : ℝ))
        @IsProbabilityMeasure (Fin n → Ω) mN P ∧
        @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ ∧
        @IsProbabilityMeasure (Fin n → Ω × ℝ) mAug ν ∧
        @MeasurePreserving (Fin n → Ω) (Fin n → Ω) mN mN₀ id P P₀ ∧
        @MeasurePreserving (Fin n → Ω × ℝ) (Fin n → Ω) mAug mN₀ q ν P₀ ∧
        (∀ i : Fin n, Measurable[mN₀, borel ℝ] (ξ0 i)) ∧
        Measurable[mN₀, borel ℝ] V0 ∧
        Measurable[mN₀, borel ℝ] D1 ∧ Measurable[mN₀, borel ℝ] D2 ∧
        Measurable[mAug, borel ℝ] (fun x => D1 (q x)) ∧
        Measurable[mAug, borel ℝ] (fun x => D2 (q x)) ∧
        (∀ ζ : Fin n → Ω, V0 ζ = Real.sqrt (∑ i : Fin n, (ξ0 i ζ) ^ (2 : ℕ))) ∧
        (∀ x : Fin n → Ω × ℝ, W x = projectionW n g (q x) ∧ V x = V0 (q x)) ∧
        Measurable[mN₀, borel ℝ] T0 ∧ Measurable[mN, borel ℝ] T0 ∧
        @Measure.map (Fin n → Ω) ℝ mN₀ (borel ℝ) T0 P₀ =
          @Measure.map (Fin n → Ω) ℝ mN (borel ℝ) T0 P ∧
        @Measure.map (Fin n → Ω × ℝ) ℝ mAug (borel ℝ) (fun x => T0 (q x)) ν =
          @Measure.map (Fin n → Ω) ℝ mN (borel ℝ) T0 P ∧
        Measurable[mN, borel ℝ] physical ∧
        MeasurableSet[mN] Hsource ∧ MeasurableSet[mN] Eclip ∧
        MeasurableSet[mN₀] Ssafe ∧ MeasurableSet[mN] Ssafe ∧
        MeasurableSet[mAug] Jsafe ∧
        Hsource ⊆ Ssafe ∧
        (∀ ζ : Fin n → Ω, ζ ∈ Hsource →
          0 < V0 ζ ∧ z * |D1 ζ| ≤ V0 ζ / 8 ∧
          z ^ (2 : ℕ) * |D2 ζ| ≤ (1 / 32 : ℝ) ∧
          0 < Real.sqrt (centeredSq n g r ζ) ∧
          Real.sqrt (centeredSq n g r ζ) =
            V0 ζ * Real.sqrt (1 + centeredDelta n g r ζ) ∧
          D2 ζ = centeredDelta n g r ζ ∧ T0 ζ = physical ζ) ∧
        (Ssafeᶜ ∪ Eclip ∪ Zphysical) ⊆ Hsourceᶜ ∧
        (E2original ∪ Z0) ⊆ Ssafeᶜ ∧
        (∀ x : Fin n → Ω × ℝ, x ∈ Jsafe →
          0 < V x ∧ z * |D1 (q x)| ≤ V x / 8 ∧
            z ^ (2 : ℕ) * |D2 (q x)| ≤ (1 / 8 : ℝ)) ∧
        ν.real Jsafeᶜ = P₀.real Ssafeᶜ ∧
        P₀.real Ssafeᶜ = P.real Ssafeᶜ ∧
        P.real Ssafeᶜ ≤ P.real Hsourceᶜ ∧
        P.real Hsourceᶜ ≤ payment ∧ ν.real Jsafeᶜ ≤ payment ∧
        P.real Ssafeᶜ ≤ payment ∧
        P.real physicalBad ≤ payment ∧ P.real Eclip ≤ payment ∧
        (∀ (BorelEvent : Set ℝ), MeasurableSet[borel ℝ] BorelEvent →
          |P.real (physical ⁻¹' BorelEvent) -
            ν.real ((fun x => T0 (q x)) ⁻¹' BorelEvent)| ≤ P.real Eclip ∧
          |P.real (physical ⁻¹' BorelEvent) -
            ν.real ((fun x => T0 (q x)) ⁻¹' BorelEvent)| ≤ payment) ∧
        (∀ (k : ℕ) (i : Fin n), Measurable[mAug, borel ℝ] (η k i)) ∧
        (∀ k : ℕ, Measurable[mAug, borel ℝ] (Qε k) ∧
          Measurable[mAug, borel ℝ] (Dη k) ∧ MeasurableSet[mAug] (E k)) ∧
        MeasurableSet[mAug] E2 ∧ MeasurableSet[mAug] Z ∧
        (∀ (i : Fin n) (x : Fin n → Ω × ℝ),
          Filter.Tendsto (fun k : ℕ => η k i x) Filter.atTop (nhds (ξ i x))) ∧
        (∀ x : Fin n → Ω × ℝ, Filter.Tendsto (fun k : ℕ => Wη k x)
          Filter.atTop (nhds (W x))) ∧
        (∀ x : Fin n → Ω × ℝ, Filter.Tendsto (fun k : ℕ => Vη k x)
          Filter.atTop (nhds (V x))) ∧
        (∀ x : Fin n → Ω × ℝ, Filter.Tendsto (fun k : ℕ => Qε k x)
          Filter.atTop (nhds (0 : ℝ))) ∧
        (∀ x : Fin n → Ω × ℝ, Filter.Tendsto (fun k : ℕ => Dη k x)
          Filter.atTop (nhds (D1 (q x)))) ∧
        (∀ x : Fin n → Ω × ℝ, x ∈ Jsafe →
          (7 / 8 : ℝ) ≤ 1 + D2 (q x) ∧ 0 < b x) ∧
        (∀ x : Fin n → Ω × ℝ, x ∈ Jsafe →
          ∀ᶠ k : ℕ in Filter.atTop, 0 < Vη k x ∧ z * |Dη k x| ≤ Vη k x / 4) ∧
        E2 ⊆ Jsafeᶜ ∧ Z ⊆ Jsafeᶜ ∧
        ν.real E2 ≤ ν.real Jsafeᶜ ∧ ν.real Z ≤ ν.real Jsafeᶜ ∧
        ν.real E2 ≤ payment ∧ ν.real Z ≤ payment ∧
        (∀ γ : ℝ, 0 < γ → ∀ᶠ k : ℕ in Filter.atTop,
          ν.real (E k) ≤ ν.real Jsafeᶜ + γ) ∧
        Filter.limsup (fun k : ℕ => ν.real (E k)) Filter.atTop ≤ ν.real Jsafeᶜ ∧
        (∀ γ : ℝ, 0 < γ → ∀ᶠ k : ℕ in Filter.atTop,
          ν.real (E k) ≤ payment + γ ∧
          ν.real (E k) + P.real physicalBad ≤ 2 * payment + γ) ∧
        Filter.limsup (fun k : ℕ => ν.real (E k)) Filter.atTop ≤ payment ∧
        Filter.limsup (fun k : ℕ => ν.real (E k) + P.real physicalBad)
          Filter.atTop ≤ 2 * payment ∧
        ∀ (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
          (hgp : Integrable[mΩ] (fun o : Ω => Real.rpow |g o| p) μ)
          (cBudget : ℝ) (hcBudget : 0 < cBudget),
        let β : ℝ := ∫ o : Ω, Real.rpow |g o| p ∂μ
        let cWindow : ℝ := Real.rpow (min (1 / 2 : ℝ) cBudget / 2) (1 / p)
        let Fz : ℝ → ℝ := fun t => (z * t) ^ 2 * min |z * t| 1
        let δ0 : Fin n → ℝ := fun i => ∫ x, Fz (ξ i x) ∂ν
        let δη : ℕ → Fin n → ℝ := fun k i => ∫ x, Fz (η k i x) ∂ν
        let L0 : ℝ := ∑ i : Fin n, δ0 i
        let Lη : ℕ → ℝ := fun k => ∑ i : Fin n, δη k i
        ((β = 0 ∨ (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
            Real.rpow (n : ℝ) ((p - 2) / (2 * p)))) →
          ∀ (τ δ γ : ℝ), 0 < τ → 0 < δ → 0 < γ →
            ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
              (∀ i : Fin n, δη k i < (1 / 2 : ℝ)) ∧
              Lη k < cBudget * z ^ 2 ∧
              (∫ x, |Qε k x| ∂ν) < τ ∧
              |sourceCostη k - sourceCost0| < τ ∧
              |compactCostη k - compactCost0| < τ ∧
              sourceCostη k ≤
                64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) *
                  (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ) + δ ∧
              ν.real (E k) ≤ payment + γ ∧
              ν.real (E k) + P.real physicalBad ≤ 2 * payment + γ)
:= by
  classical
  intro g r v rho
  -- Derive all probability hypotheses in the original measurable space.
  have hCanonical :=
    Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
      μ h hh hh2 hhsymm hcenter hprojectionsecond
      3 (by norm_num) 0 (by norm_num) (by positivity)
  dsimp only at hCanonical
  rcases hCanonical with
    ⟨hg, hg2, hgmean, hgsecond, hr, hr2, hsym, hcR, _⟩
  change Measurable[mΩ, borel ℝ] g at hg
  change MemLp g 2 μ at hg2
  change (∫ o : Ω, g o ∂μ) = 0 at hgmean
  change (∫ o : Ω, (g o) ^ (2 : ℕ) ∂μ) = 1 at hgsecond
  change Measurable (Function.uncurry r) at hr
  change MemLp (Function.uncurry r) 2 (μ.prod μ) at hr2
  change (∀ o y : Ω, r o y = r y o) at hsym
  change (∀ᵐ o : Ω ∂μ, (∫ y : Ω, r o y ∂μ) = 0) at hcR
  have hr1 : Integrable (Function.uncurry r) (μ.prod μ) :=
    hr2.integrable one_le_two
  have hcL : ∀ᵐ y : Ω ∂μ, (∫ o : Ω, r o y ∂μ) = 0 := by
    filter_upwards [hcR] with y hy
    have hEq : (fun o : Ω => r o y) = fun o : Ω => r y o :=
      funext (fun o => hsym o y)
    rw [hEq]
    exact hy
  rcases Shao.OQ6.OriginalCurrentLevelGoodsetPhysicalPayment.actual_original_current_level_goodset_physical_payment
      μ g hg hg2 hgmean hgsecond with ⟨cg, hcgPositive, hPhysicalAll⟩
  have hOriginal :=
    Shao.OQ6.OriginalLevelDependentStrictMomentFrontier.actual_original_level_dependent_strict_moment_frontier
      μ h hh hh2 hhsymm hcenter hprojectionsecond
  dsimp only at hOriginal
  rcases hOriginal with ⟨m₀, hm₀, hcg, hRetained⟩
  refine ⟨m₀, hm₀, hcg, ?_⟩
  intro μ₀
  letI : MeasurableSpace Ω := m₀
  letI : MeasurableSpace.CountablyGenerated Ω := hcg
  rcases hRetained with ⟨hμ₀prob, hfor, hfrontier⟩
  letI : IsProbabilityMeasure μ₀ := hμ₀prob
  refine ⟨⟨hμ₀prob, hfor, hfrontier⟩, cg, hcgPositive, ?_⟩
  intro Cenv aenv t0 Menv hCenv haenv ht0 hMenv
  filter_upwards [hPhysicalAll Cenv aenv t0 Menv hCenv haenv ht0 hMenv] with n hn
  refine ⟨hn.1, ?_⟩
  intro w hW hWR hSq hSqBound hEnv z hz hTiltWindow hEnvelopeWindow hGeometry
  intro mN mN₀ P P₀ N K ε ξ0 D1 D2 T0 A0 B0 A0delete B0delete
    lambda01 mAugLocal mAug νlocal ν q c ξlocal Ylocal ξ Y η
    W V Wη Vη b Qε Dη A B Adelete Bdelete Vdelete H Hdelete
    M Mdelete Anew AdeleteNew ℓ0 ℓη S0 Sη S0minus Sηminus I0 Iη
    fullTest0 fullTestη deletedTest0 deletedTestη compactDeletedTest0
    compactDeletedTestη Lcompact0 Lcompactη sourceCost0 sourceCostη compactCost0 compactCostη
    V0 qOrder Ktail Gsource C2source Hsource Ssafe Jsafe E E2 Z physical Eclip
    E2original Z0 Zphysical physicalBad payment
  -- These are the explicit let terms of the retained current-z packet.
  have hCurrent := hfrontier n hn.1 z hz hTiltWindow
  rcases hCurrent with ⟨hAnalytic, hMomentPacket⟩
  rcases hAnalytic with
    ⟨hP₀prob, hP₀map, hνprob, hq, hε, hεlim, hξPacket, hξenergy, hYpacket,
      hD2bounds, hT0zero, hTηzero, hηpacket, hSigned, hAnalyticRest⟩
  letI : @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ := hP₀prob
  letI : @IsProbabilityMeasure (Fin n → Ω × ℝ) mAug ν := hνprob
  have hPprob : @IsProbabilityMeasure (Fin n → Ω) mN P := by
    dsimp only [P, mN]
    infer_instance
  letI : @IsProbabilityMeasure (Fin n → Ω) mN P := hPprob
  change @MeasurePreserving (Fin n → Ω × ℝ) (Fin n → Ω) mAug mN₀ q ν P₀ at hq
  -- ε 0 is the positive first sequence term, not the real number zero.
  have hPacket0 := hfor n hn.1 z hz hTiltWindow (ε 0) (hε 0).1 (hε 0).2
  rcases hPacket0 with
    ⟨hPacketP₀prob, hPacketP₀map, hO, hOindep, hgcoord, hPacketEnergy,
      hQid, hW0eq, hV0eq, hT0eq, hD1m, hD2m, hD2pos,
      hT0m, hT0Original, hT0Law, hPacketRest⟩
  change Measurable[mN₀, borel ℝ] D1 at hD1m
  change Measurable[mN₀, borel ℝ] D2 at hD2m
  change Measurable[mN₀, borel ℝ] T0 at hT0m
  change Measurable[mN, borel ℝ] T0 at hT0Original
  change @Measure.map (Fin n → Ω) ℝ mN₀ (borel ℝ) T0 P₀ =
    @Measure.map (Fin n → Ω) ℝ mN (borel ℝ) T0 P at hT0Law
  have hξ0m (i : Fin n) : Measurable[mN₀, borel ℝ] (ξ0 i) :=
    ((hgcoord i).1).comp (hO i).1
  have hNsq : N ^ (2 : ℕ) = (n : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg n)
  have hV0Eq (ζ : Fin n → Ω) :
      V0 ζ = Real.sqrt (∑ i : Fin n, (ξ0 i ζ) ^ (2 : ℕ)) := by
    dsimp only [V0, projectionV, projectionEnergy, ξ0]
    apply congrArg Real.sqrt
    simp only [div_pow, ← Finset.sum_div, hNsq]
  have hV0m : Measurable[mN₀, borel ℝ] V0 := by
    have hEq : V0 = fun ζ => Real.sqrt (∑ i : Fin n, (ξ0 i ζ) ^ (2 : ℕ)) :=
      funext hV0Eq
    rw [hEq]
    exact Real.continuous_sqrt.measurable.comp
      (Finset.measurable_fun_sum (Finset.univ : Finset (Fin n))
        (fun i _ => (hξ0m i).pow_const (2 : ℕ)))
  have hWV (x : Fin n → Ω × ℝ) :
      W x = projectionW n g (q x) ∧ V x = V0 (q x) := by
    constructor
    · dsimp only [W, ξ, ξlocal, q, projectionW, N]
      rw [Finset.sum_div]
    · change Real.sqrt (∑ i : Fin n, (ξ0 i (q x)) ^ (2 : ℕ)) = V0 (q x)
      exact (hV0Eq (q x)).symm
  have hD1aug : Measurable[mAug, borel ℝ] (fun x => D1 (q x)) :=
    hD1m.comp hq.measurable
  have hD2aug : Measurable[mAug, borel ℝ] (fun x => D2 (q x)) :=
    hD2m.comp hq.measurable
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
  have hSsafe : MeasurableSet[mN₀] Ssafe := by
    change MeasurableSet[mN₀]
      {ζ : Fin n → Ω | 0 < V0 ζ ∧ z * |D1 ζ| ≤ V0 ζ / 8 ∧
        z ^ (2 : ℕ) * |D2 ζ| ≤ (1 / 8 : ℝ)}
    exact (measurableSet_lt measurable_const hV0m).inter
      ((measurableSet_le
        (measurable_const.mul (continuous_abs.measurable.comp hD1m))
        (hV0m.div_const 8)).inter
        (measurableSet_le
          (measurable_const.mul (continuous_abs.measurable.comp hD2m))
          measurable_const))
  have hSoriginal : MeasurableSet[mN] Ssafe := by
    simpa only [Set.preimage_id] using hSsafe.preimage hidN
  have hJm : MeasurableSet[mAug] Jsafe := hSsafe.preimage hq.measurable
  -- Qualified258 applies only to original P; its Hsource is never reduced.
  have hPhysical := hn.2 r w hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hsym
    rho z (Real.sqrt_nonneg v) hz hEnvelopeWindow hGeometry
  rcases hPhysical with
    ⟨hHmeas, hPhysicalMeas, hClippedMeas, hEclipMeas, hHsubset, hOn,
      hUnionSubset, hRemainderSubset, hHpay, hSafeFee, hAllFee, hEclipFee⟩
  change MeasurableSet[mN] Hsource at hHmeas
  change Measurable[mN, borel ℝ] physical at hPhysicalMeas
  change MeasurableSet[mN] Eclip at hEclipMeas
  change Hsource ⊆ Ssafe at hHsubset
  change P.real Hsourceᶜ ≤ payment at hHpay
  change P.real Ssafeᶜ ≤ payment at hSafeFee
  change P.real physicalBad ≤ payment at hAllFee
  change P.real Eclip ≤ payment at hEclipFee
  have hJmargin (x : Fin n → Ω × ℝ) (hx : x ∈ Jsafe) :
      0 < V x ∧ z * |D1 (q x)| ≤ V x / 8 ∧
        z ^ (2 : ℕ) * |D2 (q x)| ≤ (1 / 8 : ℝ) := by
    change 0 < V0 (q x) ∧ z * |D1 (q x)| ≤ V0 (q x) / 8 ∧
      z ^ (2 : ℕ) * |D2 (q x)| ≤ (1 / 8 : ℝ) at hx
    simpa only [(hWV x).2] using hx
  have hνSafe : ν.real Jsafeᶜ = P₀.real Ssafeᶜ := by
    simpa only [hq.map_eq, Jsafe, Set.preimage_compl] using
      (map_measureReal_apply (μ := ν) hq.measurable hSsafe.compl).symm
  have hPSafe : P₀.real Ssafeᶜ = P.real Ssafeᶜ := by
    change P₀ = @Measure.map (Fin n → Ω) (Fin n → Ω) mN mN₀ id P at hP₀map
    rw [hP₀map]
    simpa only [Set.preimage_id] using
      (map_measureReal_apply (μ := P) hidN hSsafe.compl)
  have hPcmono : P.real Ssafeᶜ ≤ P.real Hsourceᶜ := by
    refine measureReal_mono (μ := P) ?_ (measure_ne_top P Hsourceᶜ)
    intro ζ hζ hH
    exact hζ (hHsubset hH)
  have hJpay : ν.real Jsafeᶜ ≤ payment := by
    calc
      ν.real Jsafeᶜ = P₀.real Ssafeᶜ := hνSafe
      _ = P.real Ssafeᶜ := hPSafe
      _ ≤ P.real Hsourceᶜ := hPcmono
      _ ≤ payment := hHpay
  have hCodedLaw :
      @Measure.map (Fin n → Ω × ℝ) ℝ mAug (borel ℝ) (fun x => T0 (q x)) ν =
        @Measure.map (Fin n → Ω) ℝ mN (borel ℝ) T0 P := by
    calc
      @Measure.map (Fin n → Ω × ℝ) ℝ mAug (borel ℝ) (fun x => T0 (q x)) ν =
          @Measure.map (Fin n → Ω) ℝ mN₀ (borel ℝ) T0
            (@Measure.map (Fin n → Ω × ℝ) (Fin n → Ω) mAug mN₀ q ν) := by
        simpa only [Function.comp_def] using (Measure.map_map hT0m hq.measurable).symm
      _ = @Measure.map (Fin n → Ω) ℝ mN (borel ℝ) T0 P := by
        rw [hq.map_eq]
        exact hT0Law
  have hLawPayment (BorelEvent : Set ℝ) (hBorel : MeasurableSet[borel ℝ] BorelEvent) :
      |P.real (physical ⁻¹' BorelEvent) -
        ν.real ((fun x => T0 (q x)) ⁻¹' BorelEvent)| ≤ P.real Eclip ∧
      |P.real (physical ⁻¹' BorelEvent) -
        ν.real ((fun x => T0 (q x)) ⁻¹' BorelEvent)| ≤ payment := by
    have hCodedEvent : ν.real ((fun x => T0 (q x)) ⁻¹' BorelEvent) =
        P.real (T0 ⁻¹' BorelEvent) := by
      have hAug := map_measureReal_apply (μ := ν) (hT0m.comp hq.measurable) hBorel
      have hOrig := map_measureReal_apply (μ := P) hT0Original hBorel
      rw [hCodedLaw] at hAug
      exact hAug.symm.trans hOrig
    have hA : MeasurableSet[mN] (physical ⁻¹' BorelEvent) :=
      hBorel.preimage hPhysicalMeas
    have hB : MeasurableSet[mN] (T0 ⁻¹' BorelEvent) :=
      hBorel.preimage hT0Original
    have hSub : ((physical ⁻¹' BorelEvent) ∆ (T0 ⁻¹' BorelEvent)) ⊆ Eclip := by
      intro ζ hζ
      change T0 ζ ≠ physical ζ
      intro heq
      rcases hζ with hζ | hζ
      · apply hζ.2
        change T0 ζ ∈ BorelEvent
        rw [heq]
        exact hζ.1
      · apply hζ.2
        change physical ζ ∈ BorelEvent
        rw [← heq]
        exact hζ.1
    have hDiff : |P.real (physical ⁻¹' BorelEvent) -
        ν.real ((fun x => T0 (q x)) ⁻¹' BorelEvent)| ≤ P.real Eclip := by
      rw [hCodedEvent]
      exact (abs_measureReal_sub_le_measureReal_symmDiff (μ := P)
        hA.nullMeasurableSet hB.nullMeasurableSet).trans
          (measureReal_mono (μ := P) hSub (measure_ne_top P Eclip))
    exact ⟨hDiff, hDiff.trans hEclipFee⟩
  -- Apply the generic upper theorem to exactly the retained normalized family.
  have hPayment :=
    @Shao.OQ6.NormalizedUpperErrorGoodsetPayment.actual_normalized_upper_error_goodset_payment
      (Fin n → Ω × ℝ) mAug ν hνprob n (by omega) ξ
      (fun i => (hξPacket i).1) (fun i => (hξPacket i).2.1)
      (fun i => (hξPacket i).2.2) hξenergy Y
      (fun k i => (hYpacket k i).2.1) ε
      (fun k => (hε k).1) (fun k => (hε k).2) hεlim
      (fun k i => (hYpacket k i).2.2)
      (fun x => D1 (q x)) (fun x => D2 (q x))
      hD1aug hD2aug z hz Jsafe hJm hJmargin
  dsimp only at hPayment
  rcases hPayment with
    ⟨hηm, hNumMeas, hE2Zmeas, hηpoint, hWpoint, hVpoint, hQpoint,
      hDpoint, hD2good, hSafe, hE2subset, hZsubset, hE2fee, hZfee,
      hEventual, hLimsup⟩
  have hDηbridge (k : ℕ) (x : Fin n → Ω × ℝ) :
      D1 (q x) + Qε k x = Dη k x := (hSigned k x).1.symm
  change (∀ k : ℕ,
    Measurable[mAug, borel ℝ] (Qε k) ∧
    Measurable[mAug, borel ℝ] (fun x => D1 (q x) + Qε k x) ∧
    MeasurableSet[mAug]
      {x : Fin n → Ω × ℝ | z * |D1 (q x) + Qε k x| > Vη k x / 4}) at hNumMeas
  simp only [hDηbridge] at hNumMeas
  change (∀ k : ℕ, Measurable[mAug, borel ℝ] (Qε k) ∧
    Measurable[mAug, borel ℝ] (Dη k) ∧ MeasurableSet[mAug] (E k)) at hNumMeas
  change (∀ x : Fin n → Ω × ℝ,
    Filter.Tendsto (fun k : ℕ => D1 (q x) + Qε k x)
      Filter.atTop (nhds (D1 (q x)))) at hDpoint
  simp only [hDηbridge] at hDpoint
  change (∀ x : Fin n → Ω × ℝ, x ∈ Jsafe → ∀ᶠ k : ℕ in Filter.atTop,
    0 < Vη k x ∧ z * |D1 (q x) + Qε k x| ≤ Vη k x / 4) at hSafe
  simp only [hDηbridge] at hSafe
  change E2 ⊆ Jsafeᶜ at hE2subset
  change Z ⊆ Jsafeᶜ at hZsubset
  change ν.real E2 ≤ ν.real Jsafeᶜ at hE2fee
  change ν.real Z ≤ ν.real Jsafeᶜ at hZfee
  change (∀ γ : ℝ, 0 < γ → ∀ᶠ k : ℕ in Filter.atTop,
    ν.real {x : Fin n → Ω × ℝ |
      z * |D1 (q x) + Qε k x| > Vη k x / 4} ≤ ν.real Jsafeᶜ + γ) at hEventual
  simp only [hDηbridge] at hEventual
  change (∀ γ : ℝ, 0 < γ → ∀ᶠ k : ℕ in Filter.atTop,
    ν.real (E k) ≤ ν.real Jsafeᶜ + γ) at hEventual
  change Filter.limsup
    (fun k : ℕ => ν.real {x : Fin n → Ω × ℝ |
      z * |D1 (q x) + Qε k x| > Vη k x / 4}) Filter.atTop ≤ ν.real Jsafeᶜ at hLimsup
  simp only [hDηbridge] at hLimsup
  change Filter.limsup (fun k : ℕ => ν.real (E k)) Filter.atTop ≤ ν.real Jsafeᶜ at hLimsup
  have hEventualPay (γ : ℝ) (hγ : 0 < γ) : ∀ᶠ k : ℕ in Filter.atTop,
      ν.real (E k) ≤ payment + γ ∧
      ν.real (E k) + P.real physicalBad ≤ 2 * payment + γ := by
    filter_upwards [hEventual γ hγ] with k hk
    constructor <;> linarith only [hk, hJpay, hAllFee]
  have hSumNonneg (k : ℕ) : 0 ≤ ν.real (E k) + P.real physicalBad :=
    add_nonneg measureReal_nonneg measureReal_nonneg
  have hSumCobounded := Filter.isCoboundedUnder_le_of_le (Filter.atTop : Filter ℕ)
    (x := (0 : ℝ)) (fun k : ℕ => hSumNonneg k)
  have hSumUpper (γ : ℝ) (hγ : 0 < γ) :
      Filter.limsup (fun k : ℕ => ν.real (E k) + P.real physicalBad)
        Filter.atTop ≤ 2 * payment + γ :=
    Filter.limsup_le_of_le hSumCobounded ((hEventualPay γ hγ).mono (fun _ hk => hk.2))
  have hSumLimsup :
      Filter.limsup (fun k : ℕ => ν.real (E k) + P.real physicalBad)
        Filter.atTop ≤ 2 * payment := by
    apply le_of_not_gt
    intro hgt
    have hhalf : 0 <
        (Filter.limsup (fun k : ℕ => ν.real (E k) + P.real physicalBad)
          Filter.atTop - 2 * payment) / 2 := by linarith
    have hb := hSumUpper
      ((Filter.limsup (fun k : ℕ => ν.real (E k) + P.real physicalBad)
        Filter.atTop - 2 * payment) / 2) hhalf
    linarith
  refine ⟨hPprob, hP₀prob, hνprob, hId, hq, hξ0m, hV0m, hD1m, hD2m,
    hD1aug, hD2aug, hV0Eq, hWV, hT0m, hT0Original, hT0Law, hCodedLaw,
    hPhysicalMeas, hHmeas, hEclipMeas, hSsafe, hSoriginal, hJm, hHsubset,
    hOn, hUnionSubset, hRemainderSubset, hJmargin, hνSafe, hPSafe, hPcmono,
    hHpay, hJpay, hSafeFee, hAllFee, hEclipFee, hLawPayment,
    hηm, hNumMeas, hE2Zmeas.1, hE2Zmeas.2, hηpoint, hWpoint, hVpoint,
    hQpoint, hDpoint, hD2good, hSafe, hE2subset, hZsubset, hE2fee, hZfee,
    hE2fee.trans hJpay, hZfee.trans hJpay, hEventual, hLimsup, hEventualPay,
    hLimsup.trans hJpay, hSumLimsup, ?_⟩
  intro p hp2 hp3 hgp cBudget hcBudget
  intro β cWindow Fz δη Lη
  have hMoment := hMomentPacket p hp2 hp3 hgp cBudget hcBudget
  rcases hMoment with
    ⟨hβ, hcWindow, hcWindowPower, hcWindowSmall, hOriginalI, hAugI,
      hδJoin, hLJoin, hδNonneg, hLNonneg, hRate, hZero, hMomentWindow⟩
  intro hWindow τ δ γ hτ hδ hγ
  rcases hMomentWindow hWindow with
    ⟨hδHalf, hLStrict, hδηI, hδlim, hLlim, hJointStrictCost⟩
  obtain ⟨kStrict, hkStrict⟩ := hJointStrictCost τ δ hτ hδ
  have hStrictEvent := Filter.eventually_atTop.2 ⟨kStrict, hkStrict⟩
  have hJointEvent := hStrictEvent.and (hEventualPay γ hγ)
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.1 hJointEvent
  refine ⟨k₀, ?_⟩
  intro k hk
  rcases hk₀ k hk with ⟨hStrictCost, hUpper, hSum⟩
  rcases hStrictCost with ⟨hStrictCoordinates, hStrictTotal, hQsmall,
    hSourceSmall, hCompactSmall, hCubic⟩
  exact ⟨hStrictCoordinates, hStrictTotal, hQsmall, hSourceSmall,
    hCompactSmall, hCubic, hUpper, hSum⟩

end
end Shao.OQ6.OriginalLevelDependentUpperPhysicalFrontier
