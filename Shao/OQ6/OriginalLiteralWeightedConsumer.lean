-- STAGE1 CANDIDATE ONLY. Not frozen, implemented, elaborated, or kernel checked.
-- Proposed target: Shao/OQ6/OriginalLiteralWeightedConsumer.lean
import Shao.OQ6.OriginalLiteralRemainderEnvelope
import Shao.OQ6.LiteralDeletedWeightedCosts
import Shao.OQ6.NormalizedRemainderEnvelope

set_option autoImplicit false
universe u
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology MeasureTheory
open Shao.OQ5.P51

namespace Shao.OQ6.OriginalLiteralWeightedConsumer
noncomputable section

theorem actual_original_literal_weighted_consumer
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond : (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω mΩ mΩ μ μ)
    let rho : ℝ := Real.sqrt v
    ∃ (m₀ : MeasurableSpace Ω) (hm₀ : m₀ ≤ mΩ)
        (hcg : @MeasurableSpace.CountablyGenerated Ω m₀),
      let μ₀ : @Measure Ω m₀ := μ.trim hm₀
      letI : MeasurableSpace Ω := m₀
      letI : MeasurableSpace.CountablyGenerated Ω := hcg
      IsProbabilityMeasure μ₀ ∧
      ∀ (n : ℕ) (hn : 4 ≤ n) (C0 : ℝ) (hC0 : 0 ≤ C0)
          (z : ℝ) (hz : 0 ≤ z),
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
        let D2 : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r C0 rho 1
        let T0 : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r C0 rho 1
        let A0 : (Fin n → Ω) → ℝ := fun ζ => |D1 ζ|
        let B0 : (Fin n → Ω) → ℝ := studentizerClipBudget n r C0 rho 1
        let A0delete : Fin n → (Fin n → Ω) → ℝ :=
          fun i ζ => |residualStatisticDDeleted n r ζ i|
        let B0delete : Fin n → (Fin n → Ω) → ℝ :=
          fun i ζ => studentizerClipBudgetDeleted n r C0 rho 1 ζ i
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
        Filter.Tendsto compactCostη Filter.atTop (nhds compactCost0)
 := by
  classical
  intro g r v rho
  have hOriginal :=
    Shao.OQ6.OriginalLiteralRemainderEnvelope.actual_original_literal_remainder_envelope
      μ h hh hh2 hhsymm hcenter hprojectionsecond
  dsimp only at hOriginal
  rcases hOriginal with ⟨m₀, hm₀, hcg, hbase⟩
  refine ⟨m₀, hm₀, hcg, ?_⟩
  intro μ₀
  letI : MeasurableSpace Ω := m₀
  letI : MeasurableSpace.CountablyGenerated Ω := hcg
  rcases hbase with ⟨hμ₀prob, hfor⟩
  letI : IsProbabilityMeasure μ₀ := hμ₀prob
  refine ⟨hμ₀prob, ?_⟩
  intro n hn C0 hC0 z hz
  intro mN mN₀ P P₀ N K ε ξ0 D1 D2 T0 A0 B0 A0delete B0delete
    lambda01 mAugLocal mAug νlocal ν q c ξlocal Ylocal ξ Y a s ηlocal η C
    W V Wη Vη b Qε Dη Tη A B Adelete Bdelete Vdelete H Hdelete
    M Mdelete Anew AdeleteNew Δ ℓ0 ℓη S0 Sη S0minus Sηminus I0 Iη
    fullTest0 fullTestη deletedTest0 deletedTestη compactDeletedTest0
    compactDeletedTestη Lcompact0 Lcompactη sourceCost0 sourceCostη compactCost0 compactCostη
  have hn1 : 1 ≤ n := by omega
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hNpos : 0 < N := Real.sqrt_pos.2 (by linarith only [hnR])
  have hRootPos : 0 < Real.sqrt (n : ℝ) := hNpos
  have hK : 0 ≤ K := mul_nonneg (by norm_num) hNpos.le
  have hε (k : ℕ) : 0 < ε k := by dsimp only [ε]; positivity
  have hεsmall (k : ℕ) : ε k < 1 / (4 * Real.sqrt (n : ℝ)) := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    dsimp only [ε]
    apply (div_lt_div_iff₀
      (by positivity : 0 < 8 * Real.sqrt (n : ℝ) * ((k : ℝ) + 1))
      (by positivity : 0 < 4 * Real.sqrt (n : ℝ))).2
    nlinarith [mul_nonneg hNpos.le hk]
  have hεeq : ε = fun k : ℕ =>
      (1 / (8 * Real.sqrt (n : ℝ))) * (1 / ((k : ℝ) + 1)) := by
    funext k
    simp only [ε, div_eq_mul_inv, one_mul, mul_inv_rev]
    ring
  have hεlim : Filter.Tendsto ε Filter.atTop (nhds (0 : ℝ)) := by
    rw [hεeq]
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto
        (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhds (0 : ℝ))).const_mul
          (1 / (8 * Real.sqrt (n : ℝ)))
  have hKε (k : ℕ) : 4 * ε k * Real.sqrt (n : ℝ) = K * ε k := by
    dsimp only [K]
    ring
  -- Fixed-law information is extracted only after the explicit ε(0) application.
  have hPacket0 := hfor n hn C0 hC0 z hz K hK (ε 0) (hε 0) (hεsmall 0)
  rcases hPacket0 with
    ⟨hP₀prob, hP₀map, hO, hOindep, hgcoord, hgenergy,
      hQid, hW0eq, hV0eq, hT0eq, hD1m0, hD2m0, hhalf0,
      hTclipm, hTclipOriginal, hTcliplaw, hνprob, hq,
      hs0, hηeval0, hηindep0, hηL20, hηInts0, hηmean0, hηenergy0,
      hηnull0, hVηnull0, hpositive0, hCmeas0, hCcomap0,
      hfactor0, hretained0, hscalar0, hdeletedFactor0, hTηmeas0,
      hZ0m, hZ0Original, hZmeas, hZcodedlaw, hZ0law,
      hZcodedreal, hsigned0, hcomparison0, hFullBounds, hDeletedBounds,
      hJm, hA0, hB0, hDeletedMeasurableAndAbs, hA0I, hB0I, heI,
      hDeletedCostsAndDifferences, hTotalm, hTotalI, hA, hB,
      hD2, hAint, hBint, hD2int, hAugDeletedCostsAndDifferences,
      hAugTotalm, hAugTotalI, hSuffix0⟩
  rcases hSuffix0 with ⟨hξPacket, hξSecond, hξenergy, hSuffixRest0⟩
  letI : @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ := hP₀prob
  letI : @IsProbabilityMeasure (Fin n → Ω × ℝ) mAug ν := hνprob
  change @MeasurePreserving (Fin n → Ω × ℝ) (Fin n → Ω) mAug mN₀ q ν P₀ at hq
  have hξ (i : Fin n) : Measurable[mAug, borel ℝ] (ξ i) := (hξPacket i).1
  have hξ2 (i : Fin n) : MemLp (ξ i) 2 ν := (hξPacket i).2
  have hξ0m (i : Fin n) : Measurable[mN₀, borel ℝ] (ξ0 i) :=
    ((hgcoord i).1).comp (hO i).1
  have hξ0mean (i : Fin n) : (∫ ζ, ξ0 i ζ ∂P₀) = 0 := (hgcoord i).2.2.1
  have hfiMapAESM (i : Fin n) : AEStronglyMeasurable (ξ0 i)
      (@Measure.map (Fin n → Ω × ℝ) (Fin n → Ω) mAug mN₀ q ν) := by
    rw [hq.map_eq]
    exact (hξ0m i).aestronglyMeasurable
  have hξmeanTransport (i : Fin n) :
      (∫ x, ξ i x ∂ν) = (∫ ζ, ξ0 i ζ ∂P₀) := by
    have hmap := integral_map hq.aemeasurable (hfiMapAESM i)
    rw [hq.map_eq] at hmap
    simpa only [ξ, ξlocal, ξ0, q] using hmap.symm
  have hξmean (i : Fin n) : (∫ x, ξ i x ∂ν) = 0 :=
    (hξmeanTransport i).trans (hξ0mean i)
  have hD1 : Measurable[mAug, borel ℝ] (fun x => D1 (q x)) := hD1m0.comp hq.measurable
  have hAdelete (i : Fin n) : Measurable[mAug, borel ℝ] (Adelete i) :=
    (hAugDeletedCostsAndDifferences i).1
  have hBdelete (i : Fin n) : Measurable[mAug, borel ℝ] (Bdelete i) :=
    (hAugDeletedCostsAndDifferences i).2.1
  have hAdeleteint (i : Fin n) : Integrable[mAug] (Adelete i) ν :=
    (hAugDeletedCostsAndDifferences i).2.2.1
  have hBdeleteint (i : Fin n) : Integrable[mAug] (Bdelete i) ν :=
    (hAugDeletedCostsAndDifferences i).2.2.2.1
  have hAnonneg (x : Fin n → Ω × ℝ) : 0 ≤ A x := (hFullBounds (q x)).1
  have hBnonneg (x : Fin n → Ω × ℝ) : 0 ≤ B x := (hFullBounds (q x)).2.1
  have hAdeletenonneg (i : Fin n) (x : Fin n → Ω × ℝ) : 0 ≤ Adelete i x :=
    (hDeletedBounds i (q x)).1
  have hBdeletenonneg (i : Fin n) (x : Fin n → Ω × ℝ) : 0 ≤ Bdelete i x :=
    (hDeletedBounds i (q x)).2
  have hD1A (x : Fin n → Ω × ℝ) : |D1 (q x)| ≤ A x := le_rfl
  have hD2B (x : Fin n → Ω × ℝ) : |D2 (q x)| ≤ B x := (hFullBounds (q x)).2.2
  have hA0delete (i : Fin n) : Measurable[mN₀, borel ℝ] (A0delete i) :=
    (hDeletedMeasurableAndAbs i).2.2.1
  have hB0delete (i : Fin n) : Measurable[mN₀, borel ℝ] (B0delete i) :=
    (hDeletedMeasurableAndAbs i).2.2.2
  have hξlocalMeas (i : Fin n) : Measurable[mAugLocal, borel ℝ] (ξlocal i) :=
    ((hgcoord i).1).comp measurable_fst
  have hcode := Shao.OQ6.ScalarObservationCoding.countable_uniform_augmented_base_four_code μ₀
  rcases hcode with ⟨hLambdaProb, hLocalProb, hCodeSum, hCodeRange, hCodeMeas,
    hCodeSets, hCodeRecover, hCodeComap, hCodeFiber, hCodeNull⟩
  have hYlocalSpec (k : ℕ) (i : Fin n) :
      Measurable[mAugLocal, borel ℝ] (Ylocal k i) ∧
      ∀ t : Ω × ℝ, |Ylocal k i t - ξlocal i t| ≤ ε k := by
    have hquant := Shao.OQ6.QuantizedObservationCoding.quantized_observation_spec
      (ξlocal i) (c i) (hξlocalMeas i) hCodeMeas hCodeRange hCodeComap (ε k) (hε k)
    exact ⟨hquant.1, hquant.2.2.1⟩
  have hYlocal (k : ℕ) (i : Fin n) : Measurable[mAugLocal, borel ℝ] (Ylocal k i) :=
    (hYlocalSpec k i).1
  have hY (k : ℕ) (i : Fin n) : Measurable[mAug, borel ℝ] (Y k i) :=
    (hYlocal k i).comp (measurable_pi_apply i)
  have herr (k : ℕ) (i : Fin n) (x : Fin n → Ω × ℝ) : |Y k i x - ξ i x| ≤ ε k :=
    (hYlocalSpec k i).2 (x i)
  have hWeighted :=
    @Shao.OQ6.LiteralDeletedWeightedCosts.literal_deleted_weighted_cost_limits
      (Fin n → Ω × ℝ) mAug ν hνprob n hn1 ξ hξ hξ2 hξmean hξenergy
      Y hY ε hε hεsmall hεlim herr A B Adelete Bdelete hA hB hAdelete hBdelete
      hAnonneg hBnonneg hAdeletenonneg hBdeletenonneg
      hAint hBint hAdeleteint hBdeleteint z hz K hK
  rcases hWeighted with
    ⟨hHm, hHint, hHdeleteSpec, hHnonneg, hHdnonneg, hAnewSpec, hAdnewSpec,
      hAnewL1, hAdnewL1, hAnewLim, hAdnewLim, hFullIν, hFullηI,
      hDeletedIν, hDeletedηI, hCompactIν, hCompactηI, hIposν, hIηpos,
      hIlimν, hFullLimν, hDeletedLimν, hFullRatioν, hDeletedRatioν,
      hCompactLimν, hSourceLimν, hCompactCostLimν⟩
  -- Each normalization and factorization below is taken at its own current ε(k).
  have hCurrent (k : ℕ) :
      ((1 / 2 : ℝ) < s k ∧
        (∀ (i : Fin n) (x : Fin n → Ω × ℝ), η k i x = ηlocal k i (x i)) ∧
        iIndepFun (η k) ν ∧
        (∀ i : Fin n, Measurable[mAug, borel ℝ] (η k i) ∧ MemLp (η k i) 2 ν ∧
          (∫ x, η k i x ∂ν) = 0) ∧
        (∑ i : Fin n, ∫ x, (η k i x) ^ 2 ∂ν) = 1 ∧
        ν {x : Fin n → Ω × ℝ | Vη k x = 0} = 0 ∧
        (∀ᵐ x ∂ν, 0 < Vη k x ∧ 0 < b x ∧ 0 < Vη k x * b x)) ∧
      (∀ x : Fin n → Ω × ℝ,
        Wη k x + Dη k x - z * Vη k x * b x = W x + D1 (q x) - z * V x * b x) ∧
      (∃ Ffull : (Fin n → ℝ) → ℝ × ℝ × ℝ,
        Measurable[borel (Fin n → ℝ), borel (ℝ × ℝ × ℝ)] Ffull ∧
        ∀ x : Fin n → Ω × ℝ, (M k x, Anew k x, B x) = Ffull (C k x)) ∧
      (∀ i : Fin n, ∃ Fdelete : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ,
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdelete ∧
        ∀ x : Fin n → Ω × ℝ,
          (Mdelete k i x, AdeleteNew k i x, Bdelete i x) =
            Fdelete (fun j : {j : Fin n // j ≠ i} => η k j.val x)) ∧
      (∃ G1 G2 : (Fin n → ℝ) → ℝ,
        Measurable[borel (Fin n → ℝ), borel ℝ] G1 ∧
        Measurable[borel (Fin n → ℝ), borel ℝ] G2 ∧
        ∀ x : Fin n → Ω × ℝ, Dη k x = G1 (C k x) ∧ D2 (q x) = G2 (C k x)) ∧
      (∀ (i : Fin n) (x : Fin n → Ω × ℝ),
        Δ k i x = M k x - Mdelete k i x ∧ |Δ k i x| ≤ M k x + Mdelete k i x) ∧
      (∀ i : Fin n, Integrable[mAug] (fun x => |Δ k i x|) ν ∧
        (∫ x, |Δ k i x| ∂ν) ≤ ε k * (K * ((∫ x, H x ∂ν) + (∫ x, Hdelete i x ∂ν)))) := by
    have hPacket := hfor n hn C0 hC0 z hz K hK (ε k) (hε k) (hεsmall k)
    rcases hPacket with
      ⟨hP₀probK, hP₀mapK, hOK, hOindepK, hgcoordK, hgenergyK,
        hQidK, hW0eqK, hV0eqK, hT0eqK, hD1mK, hD2mK, hhalfK,
        hTclipmK, hTclipOriginalK, hTcliplawK, hνprobK, hqK,
        hsK, hηevalK, hηindepK, hηL2K, hηIntsK, hηmeanK, hηenergyK,
        hηnullK, hVηnullK, hpositiveK, hCmeasK, hCcomapK,
        hfactorK, hretainedK, hscalarK, hdeletedFactorK, hTηmeasK,
        hZ0mK, hZ0OriginalK, hZmeasK, hZcodedlawK, hZ0lawK,
        hZcodedrealK, hsignedK, hcomparisonK, hFullBoundsK, hDeletedBoundsK,
        hJmK, hAmK, hB1mK, hDeletedMeasurableK, hAIK, hB1IK, heIK,
        hDeletedCostsK, hTotalmK, hTotalIK, hAugAmK, hAugBmK,
        hAugD2mK, hAugAIK, hAugBIK, hAugD2IK, hAugDeletedK,
        hAugTotalmK, hAugTotalIK, hSuffixK⟩
    rcases hSuffixK with
      ⟨hNew01, hNew02, hNew03, hNew04, hNew05, hNew06, hNew07, hNew08,
        hNew09, hNew10, hNew11, hNew12, hNew13, hNew14, hNew15, hNew16,
        hNew17, hNew18, hNew19, hNew20, hNew21, hNew22, hNew23, hNew24,
        hNew25, hNew26, hNew27, hNew28, hNew29, hNew30, hNew31, hNew32,
        hNew33, hNew34, hNew35, hNew36, hNew37, hNew38, hNew39, hNew40,
        hNew41, hNew42, hNew43, hNew44, hNew45, hNew46, hNew47, hNew48,
        hNew49, hNew50, hNew51, hNew52⟩
    refine ⟨⟨hsK, hηevalK, hηindepK,
      (fun i => ⟨(hηL2K i).1, (hηL2K i).2, hηmeanK i⟩),
      hηenergyK, hVηnullK, hpositiveK⟩, hsignedK z, hNew38 (ε k),
      hNew39 (ε k), ?_, ?_, ?_⟩
    · rcases hscalarK with ⟨G2, hG2, hG2eq, hG1for⟩
      rcases hG1for z with ⟨G1, hG1, hG1eq⟩
      exact ⟨G1, G2, hG1, hG2, fun x => ⟨hG1eq x, hG2eq x⟩⟩
    · intro i x
      exact ⟨hNew40 (ε k) i x, hNew42 (ε k) (hε k).le i x⟩
    · intro i
      refine ⟨(hNew43 (ε k) i).2.2, ?_⟩
      have hi := hNew44 (ε k) i
      change (∫ x, |Δ k i x| ∂ν) ≤
        |ε k| * (K * ((∫ x, H x ∂ν) + (∫ x, Hdelete i x ∂ν))) at hi
      simpa only [abs_of_pos (hε k)] using hi
  have hQeq (k : ℕ) (x : Fin n → Ω × ℝ) : Dη k x - D1 (q x) = Qε k x := by
    dsimp only [Dη, Qε]
    ring
  have hErrorSpec (k : ℕ) :
      Measurable[mAug, borel ℝ] (Qε k) ∧ Integrable[mAug] (Qε k) ν ∧
      Integrable[mAug] (fun x => |Qε k x|) ν ∧
      (∫ x, |Qε k x| ∂ν) ≤ K * ε k * (∫ x, H x ∂ν) ∧
      (∀ x : Fin n → Ω × ℝ, |Qε k x| ≤ M k x ∧ |Dη k x| ≤ Anew k x) := by
    have hEnvelope :=
      @Shao.OQ6.NormalizedRemainderEnvelope.actual_normalized_remainder_envelope_spec
        (Fin n → Ω × ℝ) mAug ν hνprob n hn1 ξ (Y k) hξ hξ2 hξmean hξenergy (hY k)
        (fun x => D1 (q x)) (fun x => D2 (q x)) A B Adelete Bdelete
        hD1 hD2 hA hB hAnonneg hBnonneg hD1A hD2B hAint hBint
        (ε k) (hε k) (hεsmall k) (herr k) z hz
    rcases hEnvelope with
      ⟨hηmE, hWmE, hWηmE, hVmE, hVηmE, hbmE, hCmE, hHmE, hDηmE,
        hAεmE, hBmE, hbboundsE, hHposE, hρposE, hρltE, hHintE,
        hD1IE, hDηIE, hAεIE, hδIE, hδAbsIE, hρHE, hAHE,
        hErrorE, hEnvelopeE, hAεnonnegE, hAεdomE, hBboundsE,
        hBεeqE, hAdεeqE, hBdεeqE, hAdelDomE, hBdelDomE,
        hIntegralErrorE, hIntegralAErrorE, hIntegralAE⟩
    change Measurable[mAug, borel ℝ] (Dη k) at hDηmE
    change Integrable[mAug] (fun x => Dη k x - D1 (q x)) ν at hδIE
    change Integrable[mAug] (fun x => |Dη k x - D1 (q x)|) ν at hδAbsIE
    change (∀ x : Fin n → Ω × ℝ,
      |Dη k x - D1 (q x)| ≤ (4 * ε k * Real.sqrt (n : ℝ)) * H x) at hErrorE
    change (∀ x : Fin n → Ω × ℝ,
      |Dη k x| ≤ A x + (4 * ε k * Real.sqrt (n : ℝ)) * H x) at hEnvelopeE
    change (∫ x, |Dη k x - D1 (q x)| ∂ν) ≤
      (4 * ε k * Real.sqrt (n : ℝ)) * (∫ x, H x ∂ν) at hIntegralErrorE
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have hm : Measurable[mAug, borel ℝ] (fun x => Dη k x - D1 (q x)) := hDηmE.sub hD1
      simpa only [hQeq k] using hm
    · simpa only [hQeq k] using hδIE
    · simpa only [hQeq k] using hδAbsIE
    · simpa only [hQeq k, hKε k] using hIntegralErrorE
    · intro x
      refine ⟨?_, ?_⟩
      · simpa only [hQeq k, hKε k, M] using hErrorE x
      · simpa only [hKε k, Anew, M] using hEnvelopeE x
  have hQlim : Filter.Tendsto (fun k : ℕ => ∫ x, |Qε k x| ∂ν)
      Filter.atTop (nhds (0 : ℝ)) := by
    have hBoundLim : Filter.Tendsto (fun k : ℕ => K * ε k * (∫ x, H x ∂ν))
        Filter.atTop (nhds (0 : ℝ)) := by
      simpa only [mul_zero, zero_mul] using
        (hεlim.const_mul K).mul_const (∫ x, H x ∂ν)
    exact squeeze_zero'
      (Filter.Eventually.of_forall (fun k : ℕ => integral_nonneg (fun x => abs_nonneg (Qε k x))))
      (Filter.Eventually.of_forall (fun k : ℕ => (hErrorSpec k).2.2.2.1)) hBoundLim
  -- Both transports have the same reduced target space and the same target function.
  have hidΩ : Measurable[mΩ, m₀] (id : Ω → Ω) := measurable_id'' hm₀
  have hidN : Measurable[mN, mN₀] (id : (Fin n → Ω) → (Fin n → Ω)) := by
    apply (@measurable_pi_iff (Fin n → Ω) (Fin n) (fun _ : Fin n => Ω)
      mN (fun _ : Fin n => m₀) (id : (Fin n → Ω) → (Fin n → Ω))).2
    intro i
    exact hidΩ.comp
      (@measurable_pi_apply (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => mΩ) i)
  have hId : @MeasurePreserving (Fin n → Ω) (Fin n → Ω) mN mN₀ id P P₀ :=
    @MeasurePreserving.mk (Fin n → Ω) (Fin n → Ω) mN mN₀ id P P₀ hidN hP₀map.symm
  have hIntEq (f : (Fin n → Ω) → ℝ) (hf : Measurable[mN₀, borel ℝ] f) :
      (∫ x, f (q x) ∂ν) = (∫ ζ, f ζ ∂P) := by
    have h1 :=
      @integral_map (Fin n → Ω × ℝ) ℝ
        (inferInstance : NormedAddCommGroup ℝ) (inferInstance : NormedSpace ℝ ℝ)
        mAug ν (Fin n → Ω) mN₀ q hq.aemeasurable f
        (hf.aestronglyMeasurable : AEStronglyMeasurable f
          (@Measure.map (Fin n → Ω × ℝ) (Fin n → Ω) mAug mN₀ q ν))
    have h2 :=
      @integral_map_of_stronglyMeasurable (Fin n → Ω) ℝ
        (inferInstance : NormedAddCommGroup ℝ) (inferInstance : NormedSpace ℝ ℝ)
        mN P (Fin n → Ω) mN₀ id hidN f
        (hf.stronglyMeasurable : StronglyMeasurable f)
    rw [hq.map_eq] at h1
    rw [hP₀map.symm] at h2
    simpa only [Function.comp_def, id_eq] using h1.symm.trans h2
  have hIntFromν (f : (Fin n → Ω) → ℝ) (hf : Measurable[mN₀, borel ℝ] f)
      (hi : Integrable[mAug] (fun x => f (q x)) ν) : Integrable[mN] f P := by
    have hi0 : Integrable[mN₀] f P₀ := (hq.integrable_comp hf.aestronglyMeasurable).1 hi
    simpa only [Function.comp_def, id_eq] using hId.integrable_comp_of_integrable hi0
  have hS0m : Measurable[mN₀, borel ℝ] S0 :=
    Finset.measurable_sum Finset.univ (fun i _ =>
      (measurable_const.mul (hξ0m i)).sub
        (((measurable_const.mul (hξ0m i)).pow_const 2).div_const 2))
  have hS0minusm (i : Fin n) : Measurable[mN₀, borel ℝ] (S0minus i) :=
    Finset.measurable_sum (Finset.univ.erase i) (fun j _ =>
      (measurable_const.mul (hξ0m j)).sub
        (((measurable_const.mul (hξ0m j)).pow_const 2).div_const 2))
  have hFull0m : Measurable[mN₀, borel ℝ] (fun ζ => fullTest0 ζ * Real.exp (S0 ζ)) :=
    ((measurable_const.mul hA0).add (measurable_const.mul hB0)).mul hS0m.exp
  have hGap (i : Fin n) : Measurable[mN₀, borel ℝ]
      (fun ζ => |A0 ζ - A0delete i ζ| + z * |B0 ζ - B0delete i ζ|) :=
    (continuous_abs.measurable.comp (hA0.sub (hA0delete i))).add
      (measurable_const.mul (continuous_abs.measurable.comp (hB0.sub (hB0delete i))))
  have hDeleted0m (i : Fin n) :
      Measurable[mN₀, borel ℝ] (fun ζ => deletedTest0 i ζ * Real.exp (S0minus i ζ)) :=
    (((continuous_abs.measurable.comp
      (measurable_const.mul (hξ0m i))).min measurable_const).mul
      (hGap i)).mul (hS0minusm i).exp
  have hCompact0m (i : Fin n) : Measurable[mN₀, borel ℝ] (compactDeletedTest0 i) :=
    ((continuous_abs.measurable.comp (hξ0m i)).min measurable_const).mul (hGap i)
  have hTrunc0m (i : Fin n) : Measurable[mN₀, borel ℝ]
      (fun ζ => ((1 + z) * ξ0 i ζ) ^ 2 * min |(1 + z) * ξ0 i ζ| 1) :=
    ((measurable_const.mul (hξ0m i)).pow_const 2).mul
      ((continuous_abs.measurable.comp
        (measurable_const.mul (hξ0m i))).min measurable_const)
  have hIeq : (∫ x, Real.exp (S0 (q x)) ∂ν) = I0 :=
    hIntEq (fun ζ => Real.exp (S0 ζ)) hS0m.exp
  have hFeq : (∫ x, fullTest0 (q x) * Real.exp (S0 (q x)) ∂ν) =
      (∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P) :=
    hIntEq (fun ζ => fullTest0 ζ * Real.exp (S0 ζ)) hFull0m
  have hDeq (i : Fin n) :
      (∫ x, deletedTest0 i (q x) * Real.exp (S0minus i (q x)) ∂ν) =
        (∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P) :=
    hIntEq (fun ζ => deletedTest0 i ζ * Real.exp (S0minus i ζ)) (hDeleted0m i)
  have hCeq (i : Fin n) : (∫ x, compactDeletedTest0 i (q x) ∂ν) =
      (∫ ζ, compactDeletedTest0 i ζ ∂P) := hIntEq (compactDeletedTest0 i) (hCompact0m i)
  have hAeq : (∫ x, A0 (q x) ∂ν) = (∫ ζ, A0 ζ ∂P) := hIntEq A0 hA0
  have hBeq : (∫ x, B0 (q x) ∂ν) = (∫ ζ, B0 ζ ∂P) := hIntEq B0 hB0
  have hTruncEq (i : Fin n) :
      (∫ x, ((1 + z) * ξ0 i (q x)) ^ 2 * min |(1 + z) * ξ0 i (q x)| 1 ∂ν) =
        (∫ ζ, ((1 + z) * ξ0 i ζ) ^ 2 * min |(1 + z) * ξ0 i ζ| 1 ∂P) :=
    hIntEq (fun ζ => ((1 + z) * ξ0 i ζ) ^ 2 * min |(1 + z) * ξ0 i ζ| 1) (hTrunc0m i)
  have hLcompactEq :
      (∑ i : Fin n, ∫ x, ((1 + z) * ξ0 i (q x)) ^ 2 * min |(1 + z) * ξ0 i (q x)| 1 ∂ν) =
        Lcompact0 := Finset.sum_congr rfl (fun i _ => hTruncEq i)
  change Integrable[mAug] (fun x => fullTest0 (q x) * Real.exp (S0 (q x))) ν at hFullIν
  change (∀ i : Fin n, Integrable[mAug]
    (fun x => deletedTest0 i (q x) * Real.exp (S0minus i (q x))) ν) at hDeletedIν
  change (∀ i : Fin n, Integrable[mAug] (fun x => compactDeletedTest0 i (q x)) ν) at hCompactIν
  have hFull0I : Integrable[mN] (fun ζ => fullTest0 ζ * Real.exp (S0 ζ)) P :=
    hIntFromν (fun ζ => fullTest0 ζ * Real.exp (S0 ζ)) hFull0m hFullIν
  have hDeleted0I (i : Fin n) :
      Integrable[mN] (fun ζ => deletedTest0 i ζ * Real.exp (S0minus i ζ)) P :=
    hIntFromν (fun ζ => deletedTest0 i ζ * Real.exp (S0minus i ζ)) (hDeleted0m i) (hDeletedIν i)
  have hCompact0I (i : Fin n) : Integrable[mN] (compactDeletedTest0 i) P :=
    hIntFromν (compactDeletedTest0 i) (hCompact0m i) (hCompactIν i)
  have hI0pos : 0 < I0 := by
    rw [← hIeq]
    exact hIposν
  have hIlim : Filter.Tendsto Iη Filter.atTop (nhds I0) := by
    change Filter.Tendsto Iη Filter.atTop (nhds (∫ x, Real.exp (S0 (q x)) ∂ν)) at hIlimν
    simpa only [hIeq] using hIlimν
  have hFullLim : Filter.Tendsto
      (fun k : ℕ => ∫ x, fullTestη k x * Real.exp (Sη k x) ∂ν) Filter.atTop
      (nhds (∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P)) := by
    change Filter.Tendsto
      (fun k : ℕ => ∫ x, fullTestη k x * Real.exp (Sη k x) ∂ν) Filter.atTop
      (nhds (∫ x, fullTest0 (q x) * Real.exp (S0 (q x)) ∂ν)) at hFullLimν
    simpa only [hFeq] using hFullLimν
  have hDeletedLim (i : Fin n) : Filter.Tendsto
      (fun k : ℕ => ∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν) Filter.atTop
      (nhds (∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P)) := by
    have ht := hDeletedLimν i
    change Filter.Tendsto
      (fun k : ℕ => ∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν) Filter.atTop
      (nhds (∫ x, deletedTest0 i (q x) * Real.exp (S0minus i (q x)) ∂ν)) at ht
    simpa only [hDeq i] using ht
  have hFullRatio : Filter.Tendsto
      (fun k : ℕ => (∫ x, fullTestη k x * Real.exp (Sη k x) ∂ν) / Iη k) Filter.atTop
      (nhds ((∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P) / I0)) := by
    change Filter.Tendsto
      (fun k : ℕ => (∫ x, fullTestη k x * Real.exp (Sη k x) ∂ν) / Iη k) Filter.atTop
      (nhds ((∫ x, fullTest0 (q x) * Real.exp (S0 (q x)) ∂ν) /
        (∫ x, Real.exp (S0 (q x)) ∂ν))) at hFullRatioν
    simpa only [hFeq, hIeq] using hFullRatioν
  have hDeletedRatio (i : Fin n) : Filter.Tendsto
      (fun k : ℕ => (∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν) / Iη k) Filter.atTop
      (nhds ((∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P) / I0)) := by
    have ht := hDeletedRatioν i
    change Filter.Tendsto
      (fun k : ℕ => (∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν) / Iη k) Filter.atTop
      (nhds ((∫ x, deletedTest0 i (q x) * Real.exp (S0minus i (q x)) ∂ν) /
        (∫ x, Real.exp (S0 (q x)) ∂ν))) at ht
    simpa only [hDeq i, hIeq] using ht
  have hCompactLim (i : Fin n) : Filter.Tendsto
      (fun k : ℕ => ∫ x, compactDeletedTestη k i x ∂ν) Filter.atTop
      (nhds (∫ ζ, compactDeletedTest0 i ζ ∂P)) := by
    have ht := hCompactLimν i
    change Filter.Tendsto
      (fun k : ℕ => ∫ x, compactDeletedTestη k i x ∂ν) Filter.atTop
      (nhds (∫ x, compactDeletedTest0 i (q x) ∂ν)) at ht
    simpa only [hCeq i] using ht
  have hSourceLim : Filter.Tendsto sourceCostη Filter.atTop (nhds sourceCost0) := by
    change Filter.Tendsto sourceCostη Filter.atTop
      (nhds (((∫ x, fullTest0 (q x) * Real.exp (S0 (q x)) ∂ν) +
        ∑ i : Fin n, ∫ x, deletedTest0 i (q x) * Real.exp (S0minus i (q x)) ∂ν) /
        (∫ x, Real.exp (S0 (q x)) ∂ν))) at hSourceLimν
    rw [hFeq, hIeq] at hSourceLimν
    simp_rw [hDeq] at hSourceLimν
    exact hSourceLimν
  have hCompactCostLim : Filter.Tendsto compactCostη Filter.atTop (nhds compactCost0) := by
    change Filter.Tendsto compactCostη Filter.atTop
      (nhds ((∑ i : Fin n,
        ∫ x, ((1 + z) * ξ0 i (q x)) ^ 2 * min |(1 + z) * ξ0 i (q x)| 1 ∂ν) +
        (∫ x, A0 (q x) ∂ν) + z * (∫ x, B0 (q x) ∂ν) +
        ∑ i : Fin n, ∫ x, compactDeletedTest0 i (q x) ∂ν)) at hCompactCostLimν
    rw [hLcompactEq, hAeq, hBeq] at hCompactCostLimν
    simp_rw [hCeq] at hCompactCostLimν
    exact hCompactCostLimν
  have hT0zero (ζ : Fin n → Ω) (hV : projectionV n g ζ = 0) : T0 ζ = 0 := by
    simp only [T0, clippedCenteredStatistic, if_pos hV]
  have hTηzero (k : ℕ) (x : Fin n → Ω × ℝ) (hV : Vη k x = 0) : Tη k x = 0 := by
    change (Wη k x + Dη k x) / (Vη k x * b x) = 0
    rw [hV, zero_mul, div_zero]
  have hAnewL1ε (k : ℕ) : Integrable[mAug] (fun x => |Anew k x - A x|) ν ∧
      (∫ x, |Anew k x - A x| ∂ν) = ε k * (K * (∫ x, H x ∂ν)) := by
    simpa only [abs_of_pos (hε k)] using hAnewL1 k
  have hAdnewL1ε (k : ℕ) (i : Fin n) :
      Integrable[mAug] (fun x => |AdeleteNew k i x - Adelete i x|) ν ∧
      (∫ x, |AdeleteNew k i x - Adelete i x| ∂ν) = ε k * (K * (∫ x, Hdelete i x ∂ν)) := by
    simpa only [abs_of_pos (hε k)] using hAdnewL1 k i
  refine ⟨hP₀prob, hP₀map, hνprob, hq, (fun k => ⟨hε k, hεsmall k⟩), hεlim,
    (fun i => ⟨hξ i, hξ2 i, hξmean i⟩), hξenergy,
    (fun k i => ⟨hYlocal k i, hY k i, herr k i⟩),
    (fun ζ => ⟨hhalf0 ζ, (hFullBounds ζ).2.2⟩), hT0zero, hTηzero,
    (fun k => (hCurrent k).1), ?_, hHm, hHint, hHdeleteSpec,
    (fun k => ⟨(hErrorSpec k).1, (hErrorSpec k).2.1, (hErrorSpec k).2.2.1,
      (hErrorSpec k).2.2.2.1⟩), hQlim, hAnewSpec, hAdnewSpec,
    hAnewL1ε, hAdnewL1ε, hAnewLim, hAdnewLim,
    (fun k i x => (hCurrent k).2.2.2.2.2.1 i x),
    (fun k i => (hCurrent k).2.2.2.2.2.2 i),
    (fun k => (hCurrent k).2.2.1),
    (fun k i => (hCurrent k).2.2.2.1 i),
    (fun k => (hCurrent k).2.2.2.2.1),
    hFull0I, hFullηI, hDeleted0I, hDeletedηI, hCompact0I, hCompactηI,
    hI0pos, hIηpos, hIlim, hFullLim, hDeletedLim, hFullRatio, hDeletedRatio,
    hCompactLim, hSourceLim, hCompactCostLim⟩
  intro k x
  refine ⟨?_, (hCurrent k).2.1 x, (hErrorSpec k).2.2.2.2 x⟩
  dsimp only [Dη, Qε]
  ring

end

end Shao.OQ6.OriginalLiteralWeightedConsumer
