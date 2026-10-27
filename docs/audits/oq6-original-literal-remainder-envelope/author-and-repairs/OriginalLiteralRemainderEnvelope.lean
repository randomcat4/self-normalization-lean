import Shao.OQ6.OriginalClippedCanonicalCostPacket
import Shao.OQ6.LiteralDeletedRemainderEnvelope

set_option autoImplicit false

universe u

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical symmDiff Topology MeasureTheory
open Shao.OQ5.P51

namespace Shao.OQ6.OriginalLiteralRemainderEnvelope

noncomputable section

theorem actual_original_literal_remainder_envelope
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
      ∀ (n : ℕ) (hn : 4 ≤ n) (C0 : ℝ) (hC0 : 0 ≤ C0)
          (z : ℝ) (hz : 0 ≤ z) (K : ℝ) (hK : 0 ≤ K),
        let mFixedLocal : MeasurableSpace (Ω × ℝ) := m₀.prod (borel ℝ)
        let mFixed : MeasurableSpace (Fin n → Ω × ℝ) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (fun _ : Fin n => mFixedLocal)
        let νFixedLocal : Fin n → @Measure (Ω × ℝ) mFixedLocal :=
          fun _ => @Measure.prod Ω ℝ m₀ (borel ℝ) μ₀
            ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1))
        let νFixed : @Measure (Fin n → Ω × ℝ) mFixed :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => mFixedLocal) νFixedLocal
        let ξFixed : Fin n → (Fin n → Ω × ℝ) → ℝ :=
          fun (i : Fin n) (x : Fin n → Ω × ℝ) => g (x i).1 / Real.sqrt (n : ℝ)
        let VFixed : (Fin n → Ω × ℝ) → ℝ :=
          fun x : Fin n → Ω × ℝ => Real.sqrt (∑ j : Fin n, (ξFixed j x) ^ 2)
        let VdeleteFixed : Fin n → (Fin n → Ω × ℝ) → ℝ :=
          fun (i : Fin n) (x : Fin n → Ω × ℝ) =>
            Real.sqrt (∑ j ∈ Finset.univ.erase i, (ξFixed j x) ^ 2)
        let BFixed : (Fin n → Ω × ℝ) → ℝ :=
          fun x : Fin n → Ω × ℝ => studentizerClipBudget n r C0 rho 1 (fun j : Fin n => (x j).1)
        let BdeleteFixed : Fin n → (Fin n → Ω × ℝ) → ℝ :=
          fun (i : Fin n) (x : Fin n → Ω × ℝ) =>
            studentizerClipBudgetDeleted n r C0 rho 1 (fun j : Fin n => (x j).1) i
        let HFixed : (Fin n → Ω × ℝ) → ℝ :=
          fun x : Fin n → Ω × ℝ =>
            (1 + VFixed x) * (Real.sqrt (n : ℝ) + z * Real.sqrt (1 + BFixed x))
        let HdeleteFixed : Fin n → (Fin n → Ω × ℝ) → ℝ :=
          fun (i : Fin n) (x : Fin n → Ω × ℝ) =>
            (1 + VdeleteFixed i x) *
              (Real.sqrt (n : ℝ) + z * Real.sqrt (1 + BdeleteFixed i x))
        let payment : Fin n → ℝ :=
          fun i : Fin n => K *
            ((∫ x, HFixed x ∂νFixed) + (∫ x, HdeleteFixed i x ∂νFixed))
        let paymentTotal : ℝ := ∑ i : Fin n, payment i
        ∀ (ε : ℝ) (hε : 0 < ε)
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
          let D2 : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r C0 rho 1
          let Tclip : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r C0 rho 1
          let Ddel : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
          let Jdel : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
          let B1del : (Fin n → Ω) → Fin n → ℝ := studentizerClipBudgetDeleted n r C0 rho 1
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
          let B1 : (Fin n → Ω) → ℝ := studentizerClipBudget n r C0 rho 1
          let deletionMass : (Fin n → Ω) → Fin n → ℝ :=
            fun (ξ : Fin n → Ω) (i : Fin n) =>
              |A ξ - Adel ξ i| + |B1 ξ - B1del ξ i|
          let deletionTotal : (Fin n → Ω) → ℝ :=
            fun ξ : Fin n → Ω => ∑ i : Fin n, deletionMass ξ i
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
                (Ddel (q x) i, Jdel (q x) i, B1del (q x) i) =
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
          (∀ ξ : Fin n → Ω, 0 ≤ A ξ ∧ 0 ≤ B1 ξ ∧ |D2 ξ| ≤ B1 ξ) ∧
          (∀ (i : Fin n) (ξ : Fin n → Ω), 0 ≤ Adel ξ i ∧ 0 ≤ B1del ξ i) ∧
          Measurable[mN₀, borel ℝ] J ∧
          Measurable[mN₀, borel ℝ] A ∧ Measurable[mN₀, borel ℝ] B1 ∧
          (∀ i : Fin n,
            Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => Ddel ξ i) ∧
            Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => Jdel ξ i) ∧
            Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => Adel ξ i) ∧
            Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => B1del ξ i)) ∧
          Integrable A P₀ ∧ Integrable B1 P₀ ∧ Integrable D2 P₀ ∧
          (∀ i : Fin n,
            Integrable (fun ξ : Fin n → Ω => Adel ξ i) P₀ ∧
            Integrable (fun ξ : Fin n → Ω => B1del ξ i) P₀ ∧
            Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => |A ξ - Adel ξ i|) ∧
            Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => |B1 ξ - B1del ξ i|) ∧
            Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => deletionMass ξ i) ∧
            Integrable (fun ξ : Fin n → Ω => |A ξ - Adel ξ i|) P₀ ∧
            Integrable (fun ξ : Fin n → Ω => |B1 ξ - B1del ξ i|) P₀ ∧
            Integrable (fun ξ : Fin n → Ω => deletionMass ξ i) P₀) ∧
          Measurable[mN₀, borel ℝ] deletionTotal ∧ Integrable deletionTotal P₀ ∧
          Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => A (q x)) ∧
          Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => B1 (q x)) ∧
          Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => D2 (q x)) ∧
          Integrable (fun x : Fin n → Ω × ℝ => A (q x)) ν ∧
          Integrable (fun x : Fin n → Ω × ℝ => B1 (q x)) ν ∧
          Integrable (fun x : Fin n → Ω × ℝ => D2 (q x)) ν ∧
          (∀ i : Fin n,
            Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => Adel (q x) i) ∧
            Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => B1del (q x) i) ∧
            Integrable (fun x : Fin n → Ω × ℝ => Adel (q x) i) ν ∧
            Integrable (fun x : Fin n → Ω × ℝ => B1del (q x) i) ν ∧
            Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => |A (q x) - Adel (q x) i|) ∧
            Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => |B1 (q x) - B1del (q x) i|) ∧
            Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => deletionMass (q x) i) ∧
            Integrable (fun x : Fin n → Ω × ℝ => |A (q x) - Adel (q x) i|) ν ∧
            Integrable (fun x : Fin n → Ω × ℝ => |B1 (q x) - B1del (q x) i|) ν ∧
            Integrable (fun x : Fin n → Ω × ℝ => deletionMass (q x) i) ν) ∧
          Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => deletionTotal (q x)) ∧
          Integrable (fun x : Fin n → Ω × ℝ => deletionTotal (q x)) ν ∧
          let Afull : (Fin n → Ω × ℝ) → ℝ := fun x : Fin n → Ω × ℝ => A (q x)
          let Adelete : Fin n → (Fin n → Ω × ℝ) → ℝ :=
            fun (i : Fin n) (x : Fin n → Ω × ℝ) => Adel (q x) i
          let B : (Fin n → Ω × ℝ) → ℝ := fun x : Fin n → Ω × ℝ => B1 (q x)
          let Bdelete : Fin n → (Fin n → Ω × ℝ) → ℝ :=
            fun (i : Fin n) (x : Fin n → Ω × ℝ) => B1del (q x) i
          let Vdelete : Fin n → (Fin n → Ω × ℝ) → ℝ :=
            fun (i : Fin n) (x : Fin n → Ω × ℝ) =>
              Real.sqrt (∑ j ∈ Finset.univ.erase i, (ξ j x) ^ 2)
          let Cbudget : (Fin n → Ω × ℝ) → ℝ :=
            fun x : Fin n → Ω × ℝ => Real.sqrt (1 + B x)
          let CbudgetDelete : Fin n → (Fin n → Ω × ℝ) → ℝ :=
            fun (i : Fin n) (x : Fin n → Ω × ℝ) => Real.sqrt (1 + Bdelete i x)
          let H : (Fin n → Ω × ℝ) → ℝ :=
            fun x : Fin n → Ω × ℝ => (1 + V x) * (Real.sqrt (n : ℝ) + z * Cbudget x)
          let Hdelete : Fin n → (Fin n → Ω × ℝ) → ℝ :=
            fun (i : Fin n) (x : Fin n → Ω × ℝ) =>
              (1 + Vdelete i x) * (Real.sqrt (n : ℝ) + z * CbudgetDelete i x)
          let M : ℝ → (Fin n → Ω × ℝ) → ℝ :=
            fun (θ : ℝ) (x : Fin n → Ω × ℝ) => K * θ * H x
          let Mdelete : ℝ → Fin n → (Fin n → Ω × ℝ) → ℝ :=
            fun (θ : ℝ) (i : Fin n) (x : Fin n → Ω × ℝ) => K * θ * Hdelete i x
          let Aenvelope : ℝ → (Fin n → Ω × ℝ) → ℝ :=
            fun (θ : ℝ) (x : Fin n → Ω × ℝ) => Afull x + M θ x
          let AenvelopeDelete : ℝ → Fin n → (Fin n → Ω × ℝ) → ℝ :=
            fun (θ : ℝ) (i : Fin n) (x : Fin n → Ω × ℝ) => Adelete i x + Mdelete θ i x
          let Δ : ℝ → Fin n → (Fin n → Ω × ℝ) → ℝ :=
            fun (θ : ℝ) (i : Fin n) (x : Fin n → Ω × ℝ) =>
              (Aenvelope θ x - AenvelopeDelete θ i x) - (Afull x - Adelete i x)
          let fee : ℝ → Fin n → (Fin n → Ω × ℝ) → ℝ :=
            fun (θ : ℝ) (i : Fin n) (x : Fin n → Ω × ℝ) =>
              |Aenvelope θ x - AenvelopeDelete θ i x| + |B x - Bdelete i x|
          let feeTotal : ℝ → (Fin n → Ω × ℝ) → ℝ :=
            fun (θ : ℝ) (x : Fin n → Ω × ℝ) => ∑ i : Fin n, fee θ i x
          (∀ i : Fin n, Measurable[mAug, borel ℝ] (ξ i) ∧ MemLp (ξ i) 2 ν) ∧
          (∀ i : Fin n, (∫ x, (ξ i x) ^ 2 ∂ν) = 1 / (n : ℝ)) ∧
          (∑ i : Fin n, ∫ x, (ξ i x) ^ 2 ∂ν) = 1 ∧
          Measurable[mAug, borel ℝ] V ∧
          (∀ i : Fin n, Measurable[mAug, borel ℝ] (Vdelete i)) ∧
          (∀ (i : Fin n) (x : Fin n → Ω × ℝ), 0 ≤ Vdelete i x ∧ Vdelete i x ≤ V x) ∧
          Measurable[mAug, borel ℝ] Cbudget ∧
          (∀ i : Fin n, Measurable[mAug, borel ℝ] (CbudgetDelete i)) ∧
          (∀ x : Fin n → Ω × ℝ, 1 ≤ Cbudget x) ∧
          (∀ (i : Fin n) (x : Fin n → Ω × ℝ), 1 ≤ CbudgetDelete i x) ∧
          Measurable[mAug, borel ℝ] H ∧ Integrable[mAug] H ν ∧
          (∀ i : Fin n, Measurable[mAug, borel ℝ] (Hdelete i) ∧ Integrable[mAug] (Hdelete i) ν) ∧
          (∀ x : Fin n → Ω × ℝ, 0 < H x) ∧
          (∀ (i : Fin n) (x : Fin n → Ω × ℝ), 0 < Hdelete i x) ∧
          (∀ θ : ℝ, Measurable[mAug, borel ℝ] (M θ) ∧
            ∀ i : Fin n, Measurable[mAug, borel ℝ] (Mdelete θ i)) ∧
          (∀ θ : ℝ, Integrable[mAug] (M θ) ν ∧
            ∀ i : Fin n, Integrable[mAug] (Mdelete θ i) ν) ∧
          (∀ θ : ℝ, Integrable[mAug] (fun x : Fin n → Ω × ℝ => |M θ x|) ν ∧
            ∀ i : Fin n, Integrable[mAug] (fun x : Fin n → Ω × ℝ => |Mdelete θ i x|) ν) ∧
          (∀ θ : ℝ, 0 ≤ θ → ∀ x : Fin n → Ω × ℝ,
            0 ≤ M θ x ∧ ∀ i : Fin n, 0 ≤ Mdelete θ i x) ∧
          (∀ θ : ℝ, (∫ x, M θ x ∂ν) = K * θ * (∫ x, H x ∂ν)) ∧
          (∀ (θ : ℝ) (i : Fin n),
            (∫ x, Mdelete θ i x ∂ν) = K * θ * (∫ x, Hdelete i x ∂ν)) ∧
          (∀ θ : ℝ, (∫ x, |M θ x| ∂ν) = K * |θ| * (∫ x, H x ∂ν)) ∧
          (∀ (θ : ℝ) (i : Fin n),
            (∫ x, |Mdelete θ i x| ∂ν) = K * |θ| * (∫ x, Hdelete i x ∂ν)) ∧
          (∀ i : Fin n, payment i = K * ((∫ x, H x ∂ν) + (∫ x, Hdelete i x ∂ν))) ∧
          (∀ i : Fin n, 0 ≤ payment i) ∧
          0 ≤ paymentTotal ∧
          (∀ (θ : ℝ) (i : Fin n),
            (∫ x, M θ x ∂ν) + (∫ x, Mdelete θ i x ∂ν) = θ * payment i) ∧
          (∀ (θ : ℝ) (i : Fin n),
            (∫ x, |M θ x| ∂ν) + (∫ x, |Mdelete θ i x| ∂ν) = |θ| * payment i) ∧
          (∀ θ : ℝ,
            (∑ i : Fin n, ((∫ x, M θ x ∂ν) + (∫ x, Mdelete θ i x ∂ν))) = θ * paymentTotal) ∧
          (∀ θ : ℝ,
            (∑ i : Fin n, ((∫ x, |M θ x| ∂ν) + (∫ x, |Mdelete θ i x| ∂ν))) = |θ| * paymentTotal) ∧
          Filter.Tendsto (fun θ : ℝ => ∫ x, M θ x ∂ν) (nhds (0 : ℝ)) (nhds (0 : ℝ)) ∧
          Filter.Tendsto (fun θ : ℝ => ∫ x, |M θ x| ∂ν) (nhds (0 : ℝ)) (nhds (0 : ℝ)) ∧
          (∀ i : Fin n, Filter.Tendsto (fun θ : ℝ => ∫ x, Mdelete θ i x ∂ν)
            (nhds (0 : ℝ)) (nhds (0 : ℝ))) ∧
          (∀ i : Fin n, Filter.Tendsto (fun θ : ℝ => ∫ x, |Mdelete θ i x| ∂ν)
            (nhds (0 : ℝ)) (nhds (0 : ℝ))) ∧
          (∀ θ : ℝ, Measurable[mAug, borel ℝ] (Aenvelope θ) ∧ Integrable[mAug] (Aenvelope θ) ν) ∧
          (∀ (θ : ℝ) (i : Fin n), Measurable[mAug, borel ℝ] (AenvelopeDelete θ i) ∧
            Integrable[mAug] (AenvelopeDelete θ i) ν) ∧
          (∀ θ : ℝ, 0 ≤ θ → ∀ x : Fin n → Ω × ℝ,
            0 ≤ Aenvelope θ x ∧ ∀ i : Fin n, 0 ≤ AenvelopeDelete θ i x) ∧
          (∀ θ : ℝ, ∃ Ffull : (Fin n → ℝ) → ℝ × ℝ × ℝ,
            Measurable[borel (Fin n → ℝ), borel (ℝ × ℝ × ℝ)] Ffull ∧
            ∀ x : Fin n → Ω × ℝ,
              (M θ x, Aenvelope θ x, B x) = Ffull (C x)) ∧
          (∀ (θ : ℝ) (i : Fin n),
            ∃ Fdelete : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ,
              Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdelete ∧
              ∀ x : Fin n → Ω × ℝ,
                (Mdelete θ i x, AenvelopeDelete θ i x, Bdelete i x) =
                  Fdelete (fun j : {j : Fin n // j ≠ i} => η j.val x)) ∧
          (∀ (θ : ℝ) (i : Fin n) (x : Fin n → Ω × ℝ),
            Δ θ i x = M θ x - Mdelete θ i x) ∧
          (∀ (θ : ℝ) (i : Fin n) (x : Fin n → Ω × ℝ),
            |Δ θ i x| ≤ |M θ x| + |Mdelete θ i x|) ∧
          (∀ θ : ℝ, 0 ≤ θ → ∀ (i : Fin n) (x : Fin n → Ω × ℝ),
            |Δ θ i x| ≤ M θ x + Mdelete θ i x) ∧
          (∀ (θ : ℝ) (i : Fin n), Measurable[mAug, borel ℝ] (Δ θ i) ∧
            Integrable[mAug] (Δ θ i) ν ∧
            Integrable[mAug] (fun x : Fin n → Ω × ℝ => |Δ θ i x|) ν) ∧
          (∀ (θ : ℝ) (i : Fin n), (∫ x, |Δ θ i x| ∂ν) ≤ |θ| * payment i) ∧
          (∀ i : Fin n, Filter.Tendsto (fun θ : ℝ => ∫ x, |Δ θ i x| ∂ν)
            (nhds (0 : ℝ)) (nhds (0 : ℝ))) ∧
          (∀ (θ : ℝ) (i : Fin n), Measurable[mAug, borel ℝ] (fee θ i) ∧
            Integrable[mAug] (fee θ i) ν) ∧
          (∀ θ : ℝ, Measurable[mAug, borel ℝ] (feeTotal θ) ∧ Integrable[mAug] (feeTotal θ) ν) ∧
          (∀ (θ : ℝ) (i : Fin n) (x : Fin n → Ω × ℝ),
            |fee θ i x - deletionMass (q x) i| ≤ |M θ x| + |Mdelete θ i x|) ∧
          (∀ (θ : ℝ) (i : Fin n),
            |(∫ x, fee θ i x ∂ν) - (∫ x, deletionMass (q x) i ∂ν)| ≤ |θ| * payment i) ∧
          (∀ θ : ℝ,
            |(∫ x, feeTotal θ x ∂ν) - (∫ x, deletionTotal (q x) ∂ν)| ≤ |θ| * paymentTotal) ∧
          (∀ i : Fin n, Filter.Tendsto (fun θ : ℝ => ∫ x, fee θ i x ∂ν)
            (nhds (0 : ℝ)) (nhds (∫ x, deletionMass (q x) i ∂ν))) ∧
          Filter.Tendsto (fun θ : ℝ => ∫ x, feeTotal θ x ∂ν)
            (nhds (0 : ℝ)) (nhds (∫ x, deletionTotal (q x) ∂ν))
:= by
  classical
  intro g r v rho
  have hcanonical :=
    Shao.OQ6.OriginalClippedCanonicalCostPacket.actual_original_clipped_canonical_cost_packet
      μ h hh hh2 hhsymm hcenter hprojectionsecond
  dsimp only at hcanonical
  rcases hcanonical with ⟨m₀, hm₀, hcg, hbase⟩
  refine ⟨m₀, hm₀, hcg, ?_⟩
  intro μ₀
  letI : MeasurableSpace Ω := m₀
  letI : MeasurableSpace.CountablyGenerated Ω := hcg
  rcases hbase with ⟨hμ₀prob, hfor⟩
  refine ⟨hμ₀prob, ?_⟩
  intro n hn C0 hC0 z hz K hK
  intro mFixedLocal mFixed νFixedLocal νFixed ξFixed VFixed VdeleteFixed
    BFixed BdeleteFixed HFixed HdeleteFixed payment paymentTotal
  intro ε hε hεsmall
  intro mN mN₀ P P₀ N O gcoord Q D1 D2 Tclip Ddel Jdel B1del κ W0 V0 T0
    lambda01 mAugLocal mAug νlocal ν q c ξlocal Ylocal ξ Y a s ηlocal η C W V
    Wη Vη b Dη Tη Z0 Z p0 comparisons F0 A0 Eη
    J A Adel B1 deletionMass deletionTotal
  have hcan := hfor n hn C0 hC0 ε hε hεsmall
  rcases hcan with
    ⟨hP₀prob, hP₀map, hO, hOindep, hgcoord, hgenergy,
      hQid, hW0eq, hV0eq, hT0eq, hD1m, hD2m, hhalf,
      hTclipm, hTclipOriginal, hTcliplaw, hνprob, hqpres,
      hs, hηeval, hηindep, hηL2, hηInts, hηmean, hηenergy,
      hηnull, hVηnull, hpositiveDenominator, hCmeas, hCcomap,
      hfactor, hretained, hscalar, hdeletedFactor, hTηmeas,
      hZ0m, hZ0Original, hZmeas, hZcodedlaw, hZ0law,
      hZcodedreal, hsigned, hcomparison, hFullBounds, hDeletedBounds,
      hJm, hAm, hB1m, hDeletedMeasurableAndAbs, hAI, hB1I, heI,
      hDeletedCostsAndDifferences, hTotalm, hTotalI, hAugAm, hAugB1m,
      hAugD2m, hAugAI, hAugB1I, hAugD2I, hAugDeletedCostsAndDifferences,
      hAugTotalm, hAugTotalI⟩
  refine ⟨hP₀prob, hP₀map, hO, hOindep, hgcoord, hgenergy,
    hQid, hW0eq, hV0eq, hT0eq, hD1m, hD2m, hhalf,
    hTclipm, hTclipOriginal, hTcliplaw, hνprob, hqpres,
    hs, hηeval, hηindep, hηL2, hηInts, hηmean, hηenergy,
    hηnull, hVηnull, hpositiveDenominator, hCmeas, hCcomap,
    hfactor, hretained, hscalar, hdeletedFactor, hTηmeas,
    hZ0m, hZ0Original, hZmeas, hZcodedlaw, hZ0law,
    hZcodedreal, hsigned, hcomparison, hFullBounds, hDeletedBounds,
    hJm, hAm, hB1m, hDeletedMeasurableAndAbs, hAI, hB1I, heI,
    hDeletedCostsAndDifferences, hTotalm, hTotalI, hAugAm, hAugB1m,
    hAugD2m, hAugAI, hAugB1I, hAugD2I, hAugDeletedCostsAndDifferences,
    hAugTotalm, hAugTotalI, ?_⟩
  intro Afull Adelete B Bdelete Vdelete Cbudget CbudgetDelete H Hdelete
    M Mdelete Aenvelope AenvelopeDelete Δ fee feeTotal
  have hLiteralNu : νFixed = ν := rfl
  have hLiteralXi : ξFixed = ξ := rfl
  have hLiteralV : VFixed = V := rfl
  have hLiteralVdelete : VdeleteFixed = Vdelete := rfl
  have hLiteralB : BFixed = B := rfl
  have hLiteralBdelete : BdeleteFixed = Bdelete := rfl
  have hLiteralH : HFixed = H := rfl
  have hLiteralHdelete : HdeleteFixed = Hdelete := rfl
  have hPaymentTypeJoin (i : Fin n) :
      payment i = K * ((∫ x, H x ∂ν) + (∫ x, Hdelete i x ∂ν)) := rfl
  have hPaymentTotalTypeJoin : paymentTotal = ∑ i : Fin n, payment i := rfl
  have hn1 : 1 ≤ n := by omega
  have hn4R : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hNpos : 0 < N := Real.sqrt_pos.2 (by linarith only [hn4R])
  have hFourNpos : 0 < 4 * Real.sqrt (n : ℝ) :=
    mul_pos (by norm_num) hNpos
  have hFourNne : 4 * Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hFourNpos
  change @MeasurePreserving (Fin n → Ω × ℝ) (Fin n → Ω) mAug mN₀
    q ν P₀ at hqpres
  have hGiMeas (i : Fin n) :
      Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => gcoord i (O i ζ)) :=
    ((hgcoord i).1).comp (hO i).1
  have hGiSquareMeas (i : Fin n) :
      Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => (gcoord i (O i ζ)) ^ 2) :=
    (hGiMeas i).pow_const (2 : ℕ)
  have hGiSquareMapAESM (i : Fin n) :
      AEStronglyMeasurable (fun ζ : Fin n → Ω => (gcoord i (O i ζ)) ^ 2)
        (@Measure.map (Fin n → Ω × ℝ) (Fin n → Ω) mAug mN₀ q ν) := by
    rw [hqpres.map_eq]
    exact (hGiSquareMeas i).aestronglyMeasurable
  have hOriginalXiMeas (i : Fin n) : Measurable[mAug, borel ℝ] (ξ i) := by
    simpa only [ξ, O, q, Function.comp_def] using
      (hGiMeas i).comp hqpres.measurable
  have hOriginalXiL2 (i : Fin n) : MemLp (ξ i) 2 ν := by
    simpa only [ξ, O, q, Function.comp_def] using
      ((hgcoord i).2.1).comp_measurePreserving hqpres
  have hOriginalXiSecondTransport (i : Fin n) :
      (∫ x, (ξ i x) ^ 2 ∂ν) =
        (∫ ζ : Fin n → Ω, (gcoord i (O i ζ)) ^ 2 ∂P₀) := by
    have hmap := integral_map hqpres.aemeasurable (hGiSquareMapAESM i)
    rw [hqpres.map_eq] at hmap
    simpa only [ξ, O, q] using hmap.symm
  have hOriginalXiSecond (i : Fin n) :
      (∫ x, (ξ i x) ^ 2 ∂ν) = 1 / (n : ℝ) := by
    rw [hOriginalXiSecondTransport i]
    exact (hgcoord i).2.2.2
  have hOriginalXiEnergy : (∑ i : Fin n, ∫ x, (ξ i x) ^ 2 ∂ν) = 1 := by
    simp_rw [hOriginalXiSecondTransport]
    exact hgenergy
  have hBNonnegative (x : Fin n → Ω × ℝ) : 0 ≤ B x := (hFullBounds (q x)).2.1
  have hBdeleteNonnegative (i : Fin n) (x : Fin n → Ω × ℝ) :
      0 ≤ Bdelete i x := (hDeletedBounds i (q x)).2
  let δ : ℝ → ℝ := fun θ : ℝ => (K / (4 * Real.sqrt (n : ℝ))) * θ
  let Uret : ∀ i : Fin n, ({j : Fin n // j ≠ i} → Ω × ℝ) → ℝ :=
    fun (i : Fin n) (y : ({j : Fin n // j ≠ i} → Ω × ℝ)) =>
      ∑ j : {j : Fin n // j ≠ i}, (gcoord j.val (y j).1) ^ 2
  have hDeltaScale (θ : ℝ) : 4 * δ θ * Real.sqrt (n : ℝ) = K * θ := by
    dsimp only [δ]
    field_simp [hFourNne, ne_of_gt hNpos] <;> ring
  have hDeltaAbs (θ : ℝ) :
      |δ θ| = (K / (4 * Real.sqrt (n : ℝ))) * |θ| := by
    dsimp only [δ]
    rw [abs_mul, abs_of_nonneg (div_nonneg hK hFourNpos.le)]
  have hDeltaScaleAbs (θ : ℝ) :
      |4 * δ θ * Real.sqrt (n : ℝ)| = K * |θ| := by
    rw [hDeltaScale θ, abs_mul, abs_of_nonneg hK]
  have hDeltaNonnegative (θ : ℝ) (hθ : 0 ≤ θ) : 0 ≤ δ θ :=
    mul_nonneg (div_nonneg hK hFourNpos.le) hθ
  have hDeltaLimit : Filter.Tendsto δ (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
    simpa only [δ, mul_zero] using
      (Filter.Tendsto.const_mul (K / (4 * Real.sqrt (n : ℝ)))
        (Filter.tendsto_id : Filter.Tendsto (fun θ : ℝ => θ)
          (nhds (0 : ℝ)) (nhds (0 : ℝ))))
  have hScaledGenericPayment (θ : ℝ) (i : Fin n) :
      δ θ * (4 * Real.sqrt (n : ℝ) * ((∫ x, H x ∂ν) + (∫ x, Hdelete i x ∂ν))) =
        θ * payment i := by
    rw [hPaymentTypeJoin i]
    calc
      δ θ * (4 * Real.sqrt (n : ℝ) * ((∫ x, H x ∂ν) + (∫ x, Hdelete i x ∂ν))) =
          (4 * δ θ * Real.sqrt (n : ℝ)) *
            ((∫ x, H x ∂ν) + (∫ x, Hdelete i x ∂ν)) := by ring
      _ = θ * (K * ((∫ x, H x ∂ν) + (∫ x, Hdelete i x ∂ν))) := by
        rw [hDeltaScale θ]
        ring
  have hScaledGenericAbsPayment (θ : ℝ) (i : Fin n) :
      |δ θ| * (4 * Real.sqrt (n : ℝ) * ((∫ x, H x ∂ν) + (∫ x, Hdelete i x ∂ν))) =
        |θ| * payment i := by
    rw [hDeltaAbs θ, hPaymentTypeJoin i]
    field_simp [hFourNne, ne_of_gt hNpos] <;> ring
  have hLinearFiniteSum (θ : ℝ) :
      (∑ i : Fin n, θ * payment i) = θ * paymentTotal := by
    rw [hPaymentTotalTypeJoin, Finset.mul_sum]
  have hAbsoluteLinearFiniteSum (θ : ℝ) :
      (∑ i : Fin n, |θ| * payment i) = |θ| * paymentTotal := by
    rw [hPaymentTotalTypeJoin, Finset.mul_sum]
  have hTripleBorel :
      (inferInstance : MeasurableSpace (ℝ × ℝ × ℝ)) = borel (ℝ × ℝ × ℝ) :=
    BorelSpace.measurable_eq
  have hFullCodeBorel :
      (inferInstance : MeasurableSpace (Fin n → ℝ)) = borel (Fin n → ℝ) :=
    BorelSpace.measurable_eq
  have hRetainedCodeBorel (i : Fin n) :
      (inferInstance : MeasurableSpace ({j : Fin n // j ≠ i} → ℝ)) =
        borel ({j : Fin n // j ≠ i} → ℝ) := BorelSpace.measurable_eq
  have hUretMeas (i : Fin n) :
      Measurable[
        @MeasurableSpace.pi {j : Fin n // j ≠ i}
          (fun _ : {j : Fin n // j ≠ i} => Ω × ℝ)
          (fun _ : {j : Fin n // j ≠ i} => mAugLocal), borel ℝ] (Uret i) := by
    exact Finset.measurable_sum Finset.univ
      (fun (j : {j : Fin n // j ≠ i})
        (_hj : j ∈ (Finset.univ : Finset {j : Fin n // j ≠ i})) =>
          (((hgcoord j.val).1).comp
            (measurable_fst.comp (measurable_pi_apply j))).pow_const (2 : ℕ))
  have hSubtypeSum (i : Fin n) (f : Fin n → ℝ) :
      (∑ j : {j : Fin n // j ≠ i}, f j.val) = ∑ j ∈ Finset.univ.erase i, f j := by
    letI : Fintype {j : Fin n // j = i} := Subtype.fintype (fun j : Fin n => j = i)
    have hsplit := Fintype.sum_subtype_add_sum_subtype (fun j : Fin n => j = i) f
    have hSingleSubtypeSum : (∑ j : {j : Fin n // j = i}, f j.val) = f i := by
      letI : Unique {j : Fin n // j = i} :=
        { default := ⟨i, rfl⟩
          uniq := fun j => Subtype.ext j.property }
      simp only [Fintype.sum_unique]
      rw [(default : {j : Fin n // j = i}).property]
    rw [hSingleSubtypeSum] at hsplit
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    linarith
  have hUretPoint (i : Fin n) (x : Fin n → Ω × ℝ) :
      Uret i (fun j : {j : Fin n // j ≠ i} => x j.val) =
        ∑ j ∈ Finset.univ.erase i, (ξ j x) ^ 2 := by
    simpa only [Uret, ξ] using
      hSubtypeSum i (fun j : Fin n => (ξ j x) ^ 2)
  have hVretPoint (i : Fin n) (x : Fin n → Ω × ℝ) :
      Real.sqrt (Uret i (fun j : {j : Fin n // j ≠ i} => x j.val)) = Vdelete i x := by
    rw [hUretPoint i x]
    rfl
  have hgeneric :=
    @Shao.OQ6.LiteralDeletedRemainderEnvelope.literal_deleted_remainder_envelope_spec
      (Fin n → Ω × ℝ) mAug ν hνprob n hn1 ξ hOriginalXiMeas hOriginalXiL2
      hOriginalXiEnergy B Bdelete hAugB1m
      (fun i : Fin n => (hAugDeletedCostsAndDifferences i).2.1)
      hBNonnegative hBdeleteNonnegative hAugB1I
      (fun i : Fin n => (hAugDeletedCostsAndDifferences i).2.2.2.1) z hz
  rcases hgeneric with
    ⟨hVm225, hVdeleteM225, hVdeleteBounds225, hCm225, hCdeleteM225,
      hCone225, hCdeleteOne225, hHm225, hHint225, hHdeleteSpec225,
      hHpositive225, hHdeletePositive225, hMMeas225, hMInt225, hMAbsInt225,
      hMnonneg225, hMIntegral225, hMdeleteIntegral225, hMAbsIntegral225,
      hMdeleteAbsIntegral225, hκnonnegative225, hPairIntegral225,
      hPairAbsIntegral225, hMLimit225, hMAbsLimit225, hMdeleteLimit225,
      hMdeleteAbsLimit225, hΔeq225, hΔabsbound225, hΔsourcebound225,
      hΔspec225, hΔintegral225, hΔlimit225⟩
  have hNew01 :
      (∀ i : Fin n, Measurable[mAug, borel ℝ] (ξ i) ∧ MemLp (ξ i) 2 ν) := by
    intro i
    exact ⟨hOriginalXiMeas i, hOriginalXiL2 i⟩
  have hNew02 :
      (∀ i : Fin n, (∫ x, (ξ i x) ^ 2 ∂ν) = 1 / (n : ℝ)) := by
    exact hOriginalXiSecond
  have hNew03 :
      (∑ i : Fin n, ∫ x, (ξ i x) ^ 2 ∂ν) = 1 := by
    exact hOriginalXiEnergy
  have hNew04 :
      Measurable[mAug, borel ℝ] V := by
    exact hVm225
  have hNew05 :
      (∀ i : Fin n, Measurable[mAug, borel ℝ] (Vdelete i)) := by
    exact hVdeleteM225
  have hNew06 :
      (∀ (i : Fin n) (x : Fin n → Ω × ℝ), 0 ≤ Vdelete i x ∧ Vdelete i x ≤ V x) := by
    exact hVdeleteBounds225
  have hNew07 :
      Measurable[mAug, borel ℝ] Cbudget := by
    exact hCm225
  have hNew08 :
      (∀ i : Fin n, Measurable[mAug, borel ℝ] (CbudgetDelete i)) := by
    exact hCdeleteM225
  have hNew09 :
      (∀ x : Fin n → Ω × ℝ, 1 ≤ Cbudget x) := by
    exact hCone225
  have hNew10 :
      (∀ (i : Fin n) (x : Fin n → Ω × ℝ), 1 ≤ CbudgetDelete i x) := by
    exact hCdeleteOne225
  have hNew11 :
      Measurable[mAug, borel ℝ] H := by
    exact hHm225
  have hNew12 :
      Integrable[mAug] H ν := by
    exact hHint225
  have hNew13 :
      (∀ i : Fin n, Measurable[mAug, borel ℝ] (Hdelete i) ∧ Integrable[mAug] (Hdelete i) ν) := by
    exact hHdeleteSpec225
  have hNew14 :
      (∀ x : Fin n → Ω × ℝ, 0 < H x) := by
    exact hHpositive225
  have hNew15 :
      (∀ (i : Fin n) (x : Fin n → Ω × ℝ), 0 < Hdelete i x) := by
    exact hHdeletePositive225
  have hNew16 :
      (∀ θ : ℝ, Measurable[mAug, borel ℝ] (M θ) ∧
                ∀ i : Fin n, Measurable[mAug, borel ℝ] (Mdelete θ i)) := by
    intro θ
    exact ⟨measurable_const.mul hNew11,
      fun i : Fin n => measurable_const.mul (hNew13 i).1⟩
  have hNew17 :
      (∀ θ : ℝ, Integrable[mAug] (M θ) ν ∧
                ∀ i : Fin n, Integrable[mAug] (Mdelete θ i) ν) := by
    intro θ
    exact ⟨hNew12.const_mul (K * θ),
      fun i : Fin n => ((hNew13 i).2).const_mul (K * θ)⟩
  have hNew18 :
      (∀ θ : ℝ, Integrable[mAug] (fun x : Fin n → Ω × ℝ => |M θ x|) ν ∧
                ∀ i : Fin n, Integrable[mAug] (fun x : Fin n → Ω × ℝ => |Mdelete θ i x|) ν) := by
    intro θ
    refine ⟨?_, ?_⟩
    · simpa only [Real.norm_eq_abs] using (hNew17 θ).1.norm
    · intro i
      simpa only [Real.norm_eq_abs] using ((hNew17 θ).2 i).norm
  have hNew19 :
      (∀ θ : ℝ, 0 ≤ θ → ∀ x : Fin n → Ω × ℝ,
                0 ≤ M θ x ∧ ∀ i : Fin n, 0 ≤ Mdelete θ i x) := by
    intro θ hθ x
    exact ⟨mul_nonneg (mul_nonneg hK hθ) (hNew14 x).le,
      fun i : Fin n => mul_nonneg (mul_nonneg hK hθ) (hNew15 i x).le⟩
  have hNew20 :
      (∀ θ : ℝ, (∫ x, M θ x ∂ν) = K * θ * (∫ x, H x ∂ν)) := by
    intro θ
    exact integral_const_mul (K * θ) H
  have hNew21 :
      (∀ (θ : ℝ) (i : Fin n),
                (∫ x, Mdelete θ i x ∂ν) = K * θ * (∫ x, Hdelete i x ∂ν)) := by
    intro θ i
    exact integral_const_mul (K * θ) (Hdelete i)
  have hNew22 :
      (∀ θ : ℝ, (∫ x, |M θ x| ∂ν) = K * |θ| * (∫ x, H x ∂ν)) := by
    intro θ
    calc
      (∫ x, |M θ x| ∂ν) = ∫ x, K * |θ| * H x ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x : Fin n → Ω × ℝ => by
          dsimp only [M]
          rw [abs_mul, abs_mul, abs_of_nonneg hK,
            abs_of_nonneg (hNew14 x).le])
      _ = K * |θ| * (∫ x, H x ∂ν) := integral_const_mul (K * |θ|) H
  have hNew23 :
      (∀ (θ : ℝ) (i : Fin n),
                (∫ x, |Mdelete θ i x| ∂ν) = K * |θ| * (∫ x, Hdelete i x ∂ν)) := by
    intro θ i
    calc
      (∫ x, |Mdelete θ i x| ∂ν) = ∫ x, K * |θ| * Hdelete i x ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x : Fin n → Ω × ℝ => by
          dsimp only [Mdelete]
          rw [abs_mul, abs_mul, abs_of_nonneg hK,
            abs_of_nonneg (hNew15 i x).le])
      _ = K * |θ| * (∫ x, Hdelete i x ∂ν) :=
        integral_const_mul (K * |θ|) (Hdelete i)
  have hNew24 :
      (∀ i : Fin n, payment i = K * ((∫ x, H x ∂ν) + (∫ x, Hdelete i x ∂ν))) := by
    exact hPaymentTypeJoin
  have hNew25 :
      (∀ i : Fin n, 0 ≤ payment i) := by
    intro i
    rw [hPaymentTypeJoin i]
    exact mul_nonneg hK
      (add_nonneg (integral_nonneg (fun x : Fin n → Ω × ℝ => (hNew14 x).le))
        (integral_nonneg (fun x : Fin n → Ω × ℝ => (hNew15 i x).le)))
  have hNew26 :
      0 ≤ paymentTotal := by
    change 0 ≤ ∑ i : Fin n, payment i
    exact Finset.sum_nonneg (fun (i : Fin n) (_hi : i ∈ (Finset.univ : Finset (Fin n))) =>
      hNew25 i)
  have hNew27 :
      (∀ (θ : ℝ) (i : Fin n),
                (∫ x, M θ x ∂ν) + (∫ x, Mdelete θ i x ∂ν) = θ * payment i) := by
    intro θ i
    rw [hNew20 θ, hNew21 θ i, hPaymentTypeJoin i]
    ring
  have hNew28 :
      (∀ (θ : ℝ) (i : Fin n),
                (∫ x, |M θ x| ∂ν) + (∫ x, |Mdelete θ i x| ∂ν) = |θ| * payment i) := by
    intro θ i
    rw [hNew22 θ, hNew23 θ i, hPaymentTypeJoin i]
    ring
  have hNew29 :
      (∀ θ : ℝ,
                (∑ i : Fin n, ((∫ x, M θ x ∂ν) + (∫ x, Mdelete θ i x ∂ν))) = θ * paymentTotal) := by
    intro θ
    simp_rw [hNew27 θ]
    exact hLinearFiniteSum θ
  have hNew30 :
      (∀ θ : ℝ,
                (∑ i : Fin n, ((∫ x, |M θ x| ∂ν) + (∫ x, |Mdelete θ i x| ∂ν))) = |θ| * paymentTotal) := by
    intro θ
    simp_rw [hNew28 θ]
    exact hAbsoluteLinearFiniteSum θ
  have hNew31 :
      Filter.Tendsto (fun θ : ℝ => ∫ x, M θ x ∂ν) (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
    simpa only [hNew20, mul_zero, zero_mul] using
      (Filter.Tendsto.mul_const (∫ x, H x ∂ν)
        (Filter.Tendsto.const_mul K
          (Filter.tendsto_id : Filter.Tendsto (fun θ : ℝ => θ)
            (nhds (0 : ℝ)) (nhds (0 : ℝ)))))
  have hNew32 :
      Filter.Tendsto (fun θ : ℝ => ∫ x, |M θ x| ∂ν) (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
    simpa only [hNew22, abs_zero, mul_zero, zero_mul] using
      (Filter.Tendsto.mul_const (∫ x, H x ∂ν)
        (Filter.Tendsto.const_mul K
          (Filter.tendsto_id : Filter.Tendsto (fun θ : ℝ => θ)
            (nhds (0 : ℝ)) (nhds (0 : ℝ))).abs))
  have hNew33 :
      (∀ i : Fin n, Filter.Tendsto (fun θ : ℝ => ∫ x, Mdelete θ i x ∂ν)
                (nhds (0 : ℝ)) (nhds (0 : ℝ))) := by
    intro i
    simpa only [hNew21, mul_zero, zero_mul] using
      (Filter.Tendsto.mul_const (∫ x, Hdelete i x ∂ν)
        (Filter.Tendsto.const_mul K
          (Filter.tendsto_id : Filter.Tendsto (fun θ : ℝ => θ)
            (nhds (0 : ℝ)) (nhds (0 : ℝ)))))
  have hNew34 :
      (∀ i : Fin n, Filter.Tendsto (fun θ : ℝ => ∫ x, |Mdelete θ i x| ∂ν)
                (nhds (0 : ℝ)) (nhds (0 : ℝ))) := by
    intro i
    simpa only [hNew23, abs_zero, mul_zero, zero_mul] using
      (Filter.Tendsto.mul_const (∫ x, Hdelete i x ∂ν)
        (Filter.Tendsto.const_mul K
          (Filter.tendsto_id : Filter.Tendsto (fun θ : ℝ => θ)
            (nhds (0 : ℝ)) (nhds (0 : ℝ))).abs))
  have hNew35 :
      (∀ θ : ℝ, Measurable[mAug, borel ℝ] (Aenvelope θ) ∧ Integrable[mAug] (Aenvelope θ) ν) := by
    intro θ
    exact ⟨hAugAm.add (hNew16 θ).1, hAugAI.add (hNew17 θ).1⟩
  have hNew36 :
      (∀ (θ : ℝ) (i : Fin n), Measurable[mAug, borel ℝ] (AenvelopeDelete θ i) ∧
                Integrable[mAug] (AenvelopeDelete θ i) ν) := by
    intro θ i
    exact ⟨((hAugDeletedCostsAndDifferences i).1).add ((hNew16 θ).2 i),
      ((hAugDeletedCostsAndDifferences i).2.2.1).add ((hNew17 θ).2 i)⟩
  have hNew37 :
      (∀ θ : ℝ, 0 ≤ θ → ∀ x : Fin n → Ω × ℝ,
                0 ≤ Aenvelope θ x ∧ ∀ i : Fin n, 0 ≤ AenvelopeDelete θ i x) := by
    intro θ hθ x
    refine ⟨add_nonneg (hFullBounds (q x)).1 (hNew19 θ hθ x).1, ?_⟩
    intro i
    exact add_nonneg (hDeletedBounds i (q x)).1 ((hNew19 θ hθ x).2 i)
  have hNew38 :
      (∀ θ : ℝ, ∃ Ffull : (Fin n → ℝ) → ℝ × ℝ × ℝ,
                Measurable[borel (Fin n → ℝ), borel (ℝ × ℝ × ℝ)] Ffull ∧
                ∀ x : Fin n → Ω × ℝ,
                  (M θ x, Aenvelope θ x, B x) = Ffull (C x)) := by
    intro θ
    rcases hfactor (M θ) (hNew16 θ).1 with ⟨FM, hFMMeas, hFMPoint⟩
    rcases hfactor (Aenvelope θ) (hNew35 θ).1 with ⟨FA, hFAMeas, hFAPoint⟩
    rcases hfactor B hAugB1m with ⟨FB, hFBMeas, hFBPoint⟩
    let Ffull : (Fin n → ℝ) → ℝ × ℝ × ℝ :=
      fun t : Fin n → ℝ => (FM t, FA t, FB t)
    have hFfullMeas : Measurable[borel (Fin n → ℝ), borel (ℝ × ℝ × ℝ)] Ffull := by
      rw [← hTripleBorel]
      exact hFMMeas.prodMk (hFAMeas.prodMk hFBMeas)
    have hFfullPoint (x : Fin n → Ω × ℝ) :
        (M θ x, Aenvelope θ x, B x) = Ffull (C x) := by
      change (M θ x, Aenvelope θ x, B x) = (FM (C x), FA (C x), FB (C x))
      rw [hFMPoint x, hFAPoint x, hFBPoint x]
    exact ⟨Ffull, hFfullMeas, hFfullPoint⟩
  have hNew39 :
      (∀ (θ : ℝ) (i : Fin n),
                ∃ Fdelete : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ,
                  Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdelete ∧
                  ∀ x : Fin n → Ω × ℝ,
                    (Mdelete θ i x, AenvelopeDelete θ i x, Bdelete i x) =
                      Fdelete (fun j : {j : Fin n // j ≠ i} => η j.val x)) := by
    intro θ i
    rcases hdeletedFactor i with ⟨Fdel, hFdelMeas, hFdelPoint⟩
    rcases hretained i (Uret i) (hUretMeas i) with
      ⟨FU, hFUMeas, hFULocalPoint, hFUFullRestrictionMeas, hFUPoint⟩
    let Fdelete : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ :=
      fun t : ({j : Fin n // j ≠ i} → ℝ) =>
        (K * θ * ((1 + Real.sqrt (FU t)) *
          (Real.sqrt (n : ℝ) + z * Real.sqrt (1 + (Fdel t).2.2))),
         |(Fdel t).1| + K * θ * ((1 + Real.sqrt (FU t)) *
          (Real.sqrt (n : ℝ) + z * Real.sqrt (1 + (Fdel t).2.2))),
         (Fdel t).2.2)
    have hFdeleteMeas :
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdelete := by
      rw [← hTripleBorel] at hFdelMeas ⊢
      apply Measurable.prodMk
      · exact measurable_const.mul
          ((measurable_const.add hFUMeas.sqrt).mul
            (measurable_const.add (measurable_const.mul
              (measurable_const.add hFdelMeas.snd.snd).sqrt)))
      · apply Measurable.prodMk
        · simpa only [Real.norm_eq_abs] using
            hFdelMeas.fst.norm.add
              (measurable_const.mul
                ((measurable_const.add hFUMeas.sqrt).mul
                  (measurable_const.add (measurable_const.mul
                    (measurable_const.add hFdelMeas.snd.snd).sqrt))))
        · exact hFdelMeas.snd.snd
    have hFdeletePoint (x : Fin n → Ω × ℝ) :
        (Mdelete θ i x, AenvelopeDelete θ i x, Bdelete i x) =
          Fdelete (fun j : {j : Fin n // j ≠ i} => η j.val x) := by
      dsimp only [Fdelete]
      simp only [← hFdelPoint x, ← hFUPoint x, hVretPoint i x]
      rfl
    exact ⟨Fdelete, hFdeleteMeas, hFdeletePoint⟩
  have hNew40 :
      (∀ (θ : ℝ) (i : Fin n) (x : Fin n → Ω × ℝ),
                Δ θ i x = M θ x - Mdelete θ i x) := by
    intro θ i x
    dsimp only [Δ, Aenvelope, AenvelopeDelete]
    ring
  have hNew41 :
      (∀ (θ : ℝ) (i : Fin n) (x : Fin n → Ω × ℝ),
                |Δ θ i x| ≤ |M θ x| + |Mdelete θ i x|) := by
    intro θ i x
    rw [hNew40 θ i x]
    simpa only [sub_eq_add_neg, abs_neg] using
      (abs_add_le (M θ x) (-(Mdelete θ i x)))
  have hNew42 :
      (∀ θ : ℝ, 0 ≤ θ → ∀ (i : Fin n) (x : Fin n → Ω × ℝ),
                |Δ θ i x| ≤ M θ x + Mdelete θ i x) := by
    intro θ hθ i x
    simpa only [abs_of_nonneg (hNew19 θ hθ x).1,
      abs_of_nonneg ((hNew19 θ hθ x).2 i)] using hNew41 θ i x
  have hNew43 :
      (∀ (θ : ℝ) (i : Fin n), Measurable[mAug, borel ℝ] (Δ θ i) ∧
                Integrable[mAug] (Δ θ i) ν ∧
                Integrable[mAug] (fun x : Fin n → Ω × ℝ => |Δ θ i x|) ν) := by
    intro θ i
    refine ⟨?_, ?_, ?_⟩
    · convert (hNew16 θ).1.sub ((hNew16 θ).2 i) using 1
      funext x
      exact hNew40 θ i x
    · convert (hNew17 θ).1.sub ((hNew17 θ).2 i) using 1
      funext x
      exact hNew40 θ i x
    · convert ((hNew17 θ).1.sub ((hNew17 θ).2 i)).abs using 1
      funext x
      rw [hNew40 θ i x]
  have hNew44 :
      (∀ (θ : ℝ) (i : Fin n), (∫ x, |Δ θ i x| ∂ν) ≤ |θ| * payment i) := by
    intro θ i
    calc
      (∫ x, |Δ θ i x| ∂ν) ≤ ∫ x, |M θ x| + |Mdelete θ i x| ∂ν :=
        integral_mono (hNew43 θ i).2.2
          ((hNew18 θ).1.add ((hNew18 θ).2 i)) (hNew41 θ i)
      _ = (∫ x, |M θ x| ∂ν) + (∫ x, |Mdelete θ i x| ∂ν) :=
        integral_add (hNew18 θ).1 ((hNew18 θ).2 i)
      _ = |θ| * payment i := hNew28 θ i
  have hPaymentLimit :
      ∀ i : Fin n,
        Filter.Tendsto (fun θ : ℝ => |θ| * payment i) (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
    intro i
    simpa only [abs_zero, zero_mul] using
      (Filter.Tendsto.mul_const (payment i)
        (Filter.tendsto_id : Filter.Tendsto (fun θ : ℝ => θ)
          (nhds (0 : ℝ)) (nhds (0 : ℝ))).abs)
  have hNew45 :
      (∀ i : Fin n, Filter.Tendsto (fun θ : ℝ => ∫ x, |Δ θ i x| ∂ν)
                (nhds (0 : ℝ)) (nhds (0 : ℝ))) := by
    intro i
    refine Metric.tendsto_nhds.2 ?_
    intro e he
    filter_upwards [Metric.tendsto_nhds.1 (hPaymentLimit i) e he] with θ hθ
    rw [Real.dist_eq, sub_zero] at hθ
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (integral_nonneg (fun x : Fin n → Ω × ℝ => abs_nonneg (Δ θ i x)))]
    exact (hNew44 θ i).trans_lt ((le_abs_self (|θ| * payment i)).trans_lt hθ)
  have hNew46 :
      (∀ (θ : ℝ) (i : Fin n), Measurable[mAug, borel ℝ] (fee θ i) ∧
                Integrable[mAug] (fee θ i) ν) := by
    intro θ i
    refine ⟨?_, ?_⟩
    · simpa only [fee, Real.norm_eq_abs, Pi.sub_apply] using
        (((hNew35 θ).1.sub (hNew36 θ i).1).norm).add
          ((hAugB1m.sub (hAugDeletedCostsAndDifferences i).2.1).norm)
    · exact (((hNew35 θ).2.sub (hNew36 θ i).2).abs).add
        ((hAugB1I.sub (hAugDeletedCostsAndDifferences i).2.2.2.1).abs)
  have hNew47 :
      (∀ θ : ℝ, Measurable[mAug, borel ℝ] (feeTotal θ) ∧ Integrable[mAug] (feeTotal θ) ν) := by
    intro θ
    refine ⟨?_, ?_⟩
    · exact Finset.measurable_sum Finset.univ
        (fun (i : Fin n) (_hi : i ∈ (Finset.univ : Finset (Fin n))) => (hNew46 θ i).1)
    · exact integrable_finsetSum Finset.univ
        (fun (i : Fin n) (_hi : i ∈ (Finset.univ : Finset (Fin n))) => (hNew46 θ i).2)
  have hFeePointwiseNorm :
      ∀ (θ : ℝ) (i : Fin n) (x : Fin n → Ω × ℝ),
        |fee θ i x - deletionMass (q x) i| ≤ |Δ θ i x| := by
    intro θ i x
    change |(|Aenvelope θ x - AenvelopeDelete θ i x| + |B x - Bdelete i x|) -
      (|Afull x - Adelete i x| + |B x - Bdelete i x|)| ≤
        |(Aenvelope θ x - AenvelopeDelete θ i x) - (Afull x - Adelete i x)|
    convert abs_abs_sub_abs_le_abs_sub
      (Aenvelope θ x - AenvelopeDelete θ i x) (Afull x - Adelete i x) using 1
    congr 1
    ring
  have hNew48 :
      (∀ (θ : ℝ) (i : Fin n) (x : Fin n → Ω × ℝ),
                |fee θ i x - deletionMass (q x) i| ≤ |M θ x| + |Mdelete θ i x|) := by
    intro θ i x
    exact (hFeePointwiseNorm θ i x).trans (hNew41 θ i x)
  have hFeeDifferenceL1 :
      ∀ (θ : ℝ) (i : Fin n),
        Integrable[mAug] (fun x : Fin n → Ω × ℝ => fee θ i x - deletionMass (q x) i) ν := by
    intro θ i
    exact (hNew46 θ i).2.sub
      (hAugDeletedCostsAndDifferences i).2.2.2.2.2.2.2.2.2
  have hFeeDifferenceIntegral :
      ∀ (θ : ℝ) (i : Fin n),
        (∫ x, fee θ i x - deletionMass (q x) i ∂ν) =
          (∫ x, fee θ i x ∂ν) - (∫ x, deletionMass (q x) i ∂ν) := by
    intro θ i
    exact integral_sub (hNew46 θ i).2
      (hAugDeletedCostsAndDifferences i).2.2.2.2.2.2.2.2.2
  have hNew49 :
      (∀ (θ : ℝ) (i : Fin n),
                |(∫ x, fee θ i x ∂ν) - (∫ x, deletionMass (q x) i ∂ν)| ≤ |θ| * payment i) := by
    intro θ i
    calc
      |(∫ x, fee θ i x ∂ν) - (∫ x, deletionMass (q x) i ∂ν)| =
          |∫ x, fee θ i x - deletionMass (q x) i ∂ν| :=
        congrArg abs (hFeeDifferenceIntegral θ i).symm
      _ ≤ ∫ x, |fee θ i x - deletionMass (q x) i| ∂ν := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm
            (fun x : Fin n → Ω × ℝ => fee θ i x - deletionMass (q x) i))
      _ ≤ ∫ x, |M θ x| + |Mdelete θ i x| ∂ν :=
        integral_mono (hFeeDifferenceL1 θ i).abs
          ((hNew18 θ).1.add ((hNew18 θ).2 i)) (hNew48 θ i)
      _ = (∫ x, |M θ x| ∂ν) + (∫ x, |Mdelete θ i x| ∂ν) :=
        integral_add (hNew18 θ).1 ((hNew18 θ).2 i)
      _ = |θ| * payment i := hNew28 θ i
  have hFeeTotalIntegral :
      ∀ θ : ℝ,
        (∫ x, feeTotal θ x ∂ν) = ∑ i : Fin n, ∫ x, fee θ i x ∂ν := by
    intro θ
    exact integral_finsetSum Finset.univ
      (fun (i : Fin n) (_hi : i ∈ (Finset.univ : Finset (Fin n))) => (hNew46 θ i).2)
  have hOriginalTotalIntegral :
      
        (∫ x, deletionTotal (q x) ∂ν) = ∑ i : Fin n, ∫ x, deletionMass (q x) i ∂ν := by
    exact integral_finsetSum Finset.univ
      (fun (i : Fin n) (_hi : i ∈ (Finset.univ : Finset (Fin n))) =>
        (hAugDeletedCostsAndDifferences i).2.2.2.2.2.2.2.2.2)
  have hNew50 :
      (∀ θ : ℝ,
                |(∫ x, feeTotal θ x ∂ν) - (∫ x, deletionTotal (q x) ∂ν)| ≤ |θ| * paymentTotal) := by
    intro θ
    rw [hFeeTotalIntegral θ, hOriginalTotalIntegral, ← Finset.sum_sub_distrib]
    calc
      |∑ i : Fin n, ((∫ x, fee θ i x ∂ν) - (∫ x, deletionMass (q x) i ∂ν))| ≤
          ∑ i : Fin n, |(∫ x, fee θ i x ∂ν) - (∫ x, deletionMass (q x) i ∂ν)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, |θ| * payment i :=
        Finset.sum_le_sum
          (fun (i : Fin n) (_hi : i ∈ (Finset.univ : Finset (Fin n))) => hNew49 θ i)
      _ = |θ| * paymentTotal := hAbsoluteLinearFiniteSum θ
  have hNew51 :
      (∀ i : Fin n, Filter.Tendsto (fun θ : ℝ => ∫ x, fee θ i x ∂ν)
                (nhds (0 : ℝ)) (nhds (∫ x, deletionMass (q x) i ∂ν))) := by
    intro i
    refine Metric.tendsto_nhds.2 ?_
    intro e he
    filter_upwards [Metric.tendsto_nhds.1 (hPaymentLimit i) e he] with θ hθ
    rw [Real.dist_eq, sub_zero] at hθ
    rw [Real.dist_eq]
    exact (hNew49 θ i).trans_lt ((le_abs_self (|θ| * payment i)).trans_lt hθ)
  have hPaymentTotalLimit :
      
        Filter.Tendsto (fun θ : ℝ => |θ| * paymentTotal) (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
    simpa only [abs_zero, zero_mul] using
      (Filter.Tendsto.mul_const paymentTotal
        (Filter.tendsto_id : Filter.Tendsto (fun θ : ℝ => θ)
          (nhds (0 : ℝ)) (nhds (0 : ℝ))).abs)
  have hNew52 :
      Filter.Tendsto (fun θ : ℝ => ∫ x, feeTotal θ x ∂ν)
                (nhds (0 : ℝ)) (nhds (∫ x, deletionTotal (q x) ∂ν)) := by
    refine Metric.tendsto_nhds.2 ?_
    intro e he
    filter_upwards [Metric.tendsto_nhds.1 hPaymentTotalLimit e he] with θ hθ
    rw [Real.dist_eq, sub_zero] at hθ
    rw [Real.dist_eq]
    exact (hNew50 θ).trans_lt ((le_abs_self (|θ| * paymentTotal)).trans_lt hθ)
  exact ⟨hNew01, hNew02, hNew03, hNew04, hNew05, hNew06, hNew07, hNew08, hNew09, hNew10, hNew11, hNew12, hNew13, hNew14, hNew15, hNew16, hNew17, hNew18, hNew19, hNew20, hNew21, hNew22, hNew23, hNew24, hNew25, hNew26, hNew27, hNew28, hNew29, hNew30, hNew31, hNew32, hNew33, hNew34, hNew35, hNew36, hNew37, hNew38, hNew39, hNew40, hNew41, hNew42, hNew43, hNew44, hNew45, hNew46, hNew47, hNew48, hNew49, hNew50, hNew51, hNew52⟩

end

end Shao.OQ6.OriginalLiteralRemainderEnvelope
