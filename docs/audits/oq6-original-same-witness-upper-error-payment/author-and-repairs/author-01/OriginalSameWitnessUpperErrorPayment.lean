import Shao.OQ6.OriginalSingleWitnessAnalyticStrictFrontier
import Shao.OQ6.NormalizedUpperErrorGoodsetPayment
import Shao.OQ6.P54ActualGoodsetFrontier
import Shao.OQ6.ActualQuadraticTiltMoments
import Shao.OQ6.OriginalLiteralWeightedConsumer
import Shao.OQ6.NormalizedStrictMomentBudgets
import Shao.OQ6.IIDSourceStrictMomentBudgets

set_option autoImplicit false
universe u
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology MeasureTheory
open Shao.OQ5.P51
namespace Shao.OQ6.OriginalSameWitnessUpperErrorPayment
noncomputable section

theorem actual_original_same_witness_upper_error_payment
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond : (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
    (hgp : Integrable (fun o : Ω => Real.rpow |∫ y, h o y ∂μ| p) μ)
    (cBudget : ℝ) (hcBudget : 0 < cBudget) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω mΩ mΩ μ μ)
    let rho : ℝ := Real.sqrt v
    let β : ℝ := ∫ o : Ω, Real.rpow |g o| p ∂μ
    let cWindow : ℝ := Real.rpow (min (1 / 2 : ℝ) cBudget / 2) (1 / p)
    Measurable[mΩ, borel ℝ] g ∧ MemLp g 2 μ ∧
    0 ≤ β ∧ 0 < cWindow ∧
    Real.rpow cWindow p = min (1 / 2 : ℝ) cBudget / 2 ∧
    Real.rpow cWindow p < min (1 / 2 : ℝ) cBudget ∧
    ∃ cg : ℝ, 0 < cg ∧
    ∃ (m₀ : MeasurableSpace Ω) (hm₀ : m₀ ≤ mΩ)
        (hcg : @MeasurableSpace.CountablyGenerated Ω m₀),
      let μ₀ : @Measure Ω m₀ := μ.trim hm₀
      letI : MeasurableSpace Ω := m₀
      letI : MeasurableSpace.CountablyGenerated Ω := hcg
      IsProbabilityMeasure μ₀ ∧
      (∀ (n : ℕ) (hn : 4 ≤ n) (C0 : ℝ) (hC0 : 0 ≤ C0)
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
        let Fz : ℝ → ℝ := fun t => (z * t) ^ 2 * min |z * t| 1
        let δ0 : Fin n → ℝ := fun i => ∫ ζ, Fz (ξ0 i ζ) ∂P
        let δreduced : Fin n → ℝ := fun i => ∫ ζ, Fz (ξ0 i ζ) ∂P₀
        let δν : Fin n → ℝ := fun i => ∫ x, Fz (ξ i x) ∂ν
        let δη : ℕ → Fin n → ℝ := fun k i => ∫ x, Fz (η k i x) ∂ν
        let L0 : ℝ := ∑ i : Fin n, δ0 i
        let Lν : ℝ := ∑ i : Fin n, δν i
        let Lη : ℕ → ℝ := fun k => ∑ i : Fin n, δη k i
        let scalarBudget : ℝ := ∫ o : Ω, Fz (g o / N) ∂μ
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
        (1 ≤ z →
          Integrable[mΩ] (fun o : Ω => Fz (g o / N)) μ ∧
          (∀ i : Fin n,
            Measurable[mN₀, borel ℝ] (fun ζ => Fz (ξ0 i ζ)) ∧
            Integrable[mN] (fun ζ => Fz (ξ0 i ζ)) P ∧
            Integrable[mN₀] (fun ζ => Fz (ξ0 i ζ)) P₀ ∧
            Integrable[mAug] (fun x => Fz (ξ i x)) ν ∧
            δreduced i = δ0 i ∧ δν i = δ0 i ∧ δ0 i = scalarBudget) ∧
          L0 = (n : ℝ) * scalarBudget ∧
          (∀ i : Fin n, L0 = (n : ℝ) * δ0 i) ∧
          (∀ i : Fin n, 0 ≤ δ0 i) ∧ 0 ≤ L0 ∧ Lν = L0 ∧
          L0 ≤ β * Real.rpow z p / Real.rpow (n : ℝ) ((p - 2) / 2) ∧
          (β = 0 → L0 = 0 ∧ (∀ i : Fin n, δ0 i = 0)) ∧
          ((β = 0 ∨
              (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                Real.rpow (n : ℝ) ((p - 2) / (2 * p)))) →
            L0 ≤ Real.rpow cWindow p ∧
            (∀ i : Fin n, δ0 i < (1 / 2 : ℝ)) ∧
            L0 < cBudget * z ^ 2 ∧
            (∀ (k : ℕ) (i : Fin n),
              Integrable[mAug] (fun x => Fz (η k i x)) ν) ∧
            (∀ i : Fin n,
              Filter.Tendsto (fun k : ℕ => δη k i) Filter.atTop (nhds (δ0 i))) ∧
            Filter.Tendsto Lη Filter.atTop (nhds L0) ∧
            (∀ (τ : ℝ), 0 < τ →
              ∃ k0 : ℕ, ∀ (k : ℕ), k0 ≤ k →
                (∀ i : Fin n, δη k i < (1 / 2 : ℝ)) ∧
                Lη k < cBudget * z ^ 2 ∧
                (∀ i : Fin n, |δη k i - δ0 i| < τ) ∧
                |Lη k - L0| < τ ∧
                (∫ x, |Qε k x| ∂ν) < τ ∧
                (∫ x, |Anew k x - A x| ∂ν) < τ ∧
                (∀ i : Fin n, (∫ x, |AdeleteNew k i x - Adelete i x| ∂ν) < τ) ∧
                |Iη k - I0| < τ ∧
                |(∫ x, fullTestη k x * Real.exp (Sη k x) ∂ν) -
                  (∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P)| < τ ∧
                (∀ i : Fin n,
                  |(∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν) -
                    (∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P)| < τ) ∧
                |((∫ x, fullTestη k x * Real.exp (Sη k x) ∂ν) / Iη k) -
                  ((∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P) / I0)| < τ ∧
                (∀ i : Fin n,
                  |((∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν) / Iη k) -
                    ((∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P) / I0)| < τ) ∧
                (∀ i : Fin n,
                  |(∫ x, compactDeletedTestη k i x ∂ν) -
                    (∫ ζ, compactDeletedTest0 i ζ ∂P)| < τ) ∧
                |sourceCostη k - sourceCost0| < τ ∧
                |compactCostη k - compactCost0| < τ)))) ∧
      (∀ (Cenv aenv t0 Menv : ℝ)
          (hCenv : 0 ≤ Cenv) (haenv : 0 ≤ aenv)
          (ht0 : 0 < t0) (hMenv : 0 ≤ Menv),
        ∀ᶠ n : ℕ in Filter.atTop,
          4 ≤ n ∧
          ∀ (w : Ω → ℝ)
            (hW : ∀ᵐ o : Ω ∂μ, 0 ≤ w o)
            (hWR : ∀ᵐ o : Ω ∂μ,
              w o ≤ boundedPolylogHeight Cenv aenv n)
            (hSq : Integrable[mΩ] (fun o : Ω => (w o) ^ (2 : ℕ)) μ)
            (hSqBound : (∫ o : Ω, (w o) ^ (2 : ℕ) ∂μ) ≤ Menv)
            (hEnv : ∀ᵐ t : Ω × Ω ∂(@Measure.prod Ω Ω mΩ mΩ μ μ),
              |r t.1 t.2| ≤ w t.1 * w t.2)
            (z : ℝ) (hz : (1 : ℝ) ≤ z)
            (hzWindow : z ≤ remainderWindowScale
              (Shao.OQ6.BoundedProductEnvelopeTails.tailScale Menv) t0 *
                Real.rpow (n : ℝ) (1 / 6 : ℝ)),
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
        let ε : ℕ → ℝ := fun k => 1 / (8 * Real.sqrt (n : ℝ) * ((k : ℝ) + 1))
        let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => g (ζ i) / N
        let D1 : (Fin n → Ω) → ℝ := residualStatisticD n r
        let D2 : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r 512 rho 1
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
          {x : Fin n → Ω × ℝ |
            z ^ (2 : ℕ) * |D2 (q x)| > (1 / 4 : ℝ)}
        let Z : Set (Fin n → Ω × ℝ) :=
          {x : Fin n → Ω × ℝ | V x = 0}
        let payment : ℝ :=
          (3 : ℝ) * Real.exp (-qOrder) + Real.exp (-cg * (n : ℝ)) +
            (4 : ℝ) * Real.exp (-(z * Real.sqrt (n : ℝ)) / (2 : ℝ))
        Measurable[mN₀, borel ℝ] V0 ∧
        Measurable[mN₀, borel ℝ] D1 ∧
        Measurable[mN₀, borel ℝ] D2 ∧
        Measurable[mAug, borel ℝ] (fun x => D1 (q x)) ∧
        Measurable[mAug, borel ℝ] (fun x => D2 (q x)) ∧
        (∀ x : Fin n → Ω × ℝ,
          W x = projectionW n g (q x) ∧ V x = V0 (q x)) ∧
        @MeasurableSet (Fin n → Ω) mN Hsource ∧
        @MeasurableSet (Fin n → Ω) mN₀ Ssafe ∧
        @MeasurableSet (Fin n → Ω) mN Ssafe ∧
        @MeasurableSet (Fin n → Ω × ℝ) mAug Jsafe ∧
        Hsource ⊆ Ssafe ∧
        (∀ x : Fin n → Ω × ℝ, x ∈ Jsafe →
          0 < V x ∧ z * |D1 (q x)| ≤ V x / 8 ∧
            z ^ (2 : ℕ) * |D2 (q x)| ≤ (1 / 8 : ℝ)) ∧
        ν.real Jsafeᶜ = P₀.real Ssafeᶜ ∧
        P₀.real Ssafeᶜ = P.real Ssafeᶜ ∧
        P.real Ssafeᶜ ≤ P.real Hsourceᶜ ∧
        P.real Hsourceᶜ ≤ payment ∧
        ν.real Jsafeᶜ ≤ payment ∧
        (({ζ : Fin n → Ω | V0 ζ = 0} ∪
          {ζ : Fin n → Ω | Real.sqrt (centeredSq n g r ζ) = 0}) ⊆
            Hsourceᶜ) ∧
        (∀ (k : ℕ) (i : Fin n),
          Measurable[mAug, borel ℝ] (η k i)) ∧
        (∀ k : ℕ, Measurable[mAug, borel ℝ] (Qε k) ∧
          Measurable[mAug, borel ℝ] (Dη k) ∧
          @MeasurableSet (Fin n → Ω × ℝ) mAug (E k)) ∧
        (@MeasurableSet (Fin n → Ω × ℝ) mAug E2 ∧
          @MeasurableSet (Fin n → Ω × ℝ) mAug Z) ∧
        (∀ (i : Fin n) (x : Fin n → Ω × ℝ),
          Filter.Tendsto (fun k : ℕ => η k i x)
            Filter.atTop (nhds (ξ i x))) ∧
        (∀ x : Fin n → Ω × ℝ,
          Filter.Tendsto (fun k : ℕ => Wη k x)
            Filter.atTop (nhds (W x))) ∧
        (∀ x : Fin n → Ω × ℝ,
          Filter.Tendsto (fun k : ℕ => Vη k x)
            Filter.atTop (nhds (V x))) ∧
        (∀ x : Fin n → Ω × ℝ,
          Filter.Tendsto (fun k : ℕ => Qε k x)
            Filter.atTop (nhds (0 : ℝ))) ∧
        (∀ x : Fin n → Ω × ℝ,
          Filter.Tendsto (fun k : ℕ => Dη k x)
            Filter.atTop (nhds (D1 (q x)))) ∧
        (∀ x : Fin n → Ω × ℝ, x ∈ Jsafe →
          (7 / 8 : ℝ) ≤ 1 + D2 (q x) ∧ 0 < b x) ∧
        (∀ x : Fin n → Ω × ℝ, x ∈ Jsafe →
          ∀ᶠ k : ℕ in Filter.atTop,
            0 < Vη k x ∧ z * |Dη k x| ≤ Vη k x / 4) ∧
        E2 ⊆ Jsafeᶜ ∧ Z ⊆ Jsafeᶜ ∧
        ν.real E2 ≤ ν.real Jsafeᶜ ∧
        ν.real Z ≤ ν.real Jsafeᶜ ∧
        ν.real E2 ≤ payment ∧ ν.real Z ≤ payment ∧
        (∀ δ : ℝ, 0 < δ →
          ∀ᶠ k : ℕ in Filter.atTop,
            ν.real (E k) ≤ ν.real Jsafeᶜ + δ) ∧
        Filter.limsup (fun k : ℕ => ν.real (E k))
          Filter.atTop ≤ ν.real Jsafeᶜ ∧
        (∀ δ : ℝ, 0 < δ →
          ∀ᶠ k : ℕ in Filter.atTop,
            ν.real (E k) ≤ payment + δ) ∧
        Filter.limsup (fun k : ℕ => ν.real (E k))
          Filter.atTop ≤ payment) := by
  classical
  intro g r v rho β cWindow
  -- Original-law canonical data, before any reduced measurable-space choice.
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
  let cg : ℝ := Classical.choose
    (Shao.OQ6.P54.fixed_original_boundedPolylog_goodset_frontier
      μ g hg hg2 hgmean hgsecond)
  have hcgpos : 0 < cg :=
    (Classical.choose_spec
      (Shao.OQ6.P54.fixed_original_boundedPolylog_goodset_frontier
        μ g hg hg2 hgmean hgsecond)).1
  have hConcentration :=
    (Classical.choose_spec
      (Shao.OQ6.P54.fixed_original_boundedPolylog_goodset_frontier
        μ g hg hg2 hgmean hgsecond)).2
  -- Conjunction elimination from234 is the only source of the model existential.
  have hOriginal :=
    Shao.OQ6.OriginalSingleWitnessAnalyticStrictFrontier.actual_original_single_witness_analytic_strict_frontier
      μ h hh hh2 hhsymm hcenter hprojectionsecond p hp2 hp3 hgp cBudget hcBudget
  dsimp only at hOriginal
  rcases hOriginal with
    ⟨_, _, hβ, hcWindow, hcWindowPower, hcWindowSmall, hModelExists⟩
  let m₀ : MeasurableSpace Ω := Classical.choose hModelExists
  obtain ⟨hm₀, hcg, hbase⟩ := Classical.choose_spec hModelExists
  refine ⟨hg, hg2, hβ, hcWindow, hcWindowPower, hcWindowSmall,
    cg, hcgpos, m₀, hm₀, hcg, ?_⟩
  intro μ₀
  letI : MeasurableSpace Ω := m₀
  letI : MeasurableSpace.CountablyGenerated Ω := hcg
  rcases hbase with ⟨hμ₀prob, hfor⟩
  letI : IsProbabilityMeasure μ₀ := hμ₀prob
  -- The full original234 universal analytic and strict-budget packet is passed intact.
  refine ⟨hμ₀prob, hfor, ?_⟩
  intro Cenv aenv t0 Menv hCenv haenv ht0 hMenv
  filter_upwards [hConcentration Cenv aenv t0 Menv hCenv haenv ht0 hMenv]
    with n hnConcentration
  refine ⟨hnConcentration.1, ?_⟩
  intro w hW hWR hSq hSqBound hEnv z hz hzWindow
  intro mN mN₀ P P₀ N ε ξ0 D1 D2 lambda01 mAugLocal mAug νlocal ν q c
    ξlocal Ylocal ξ Y a s ηlocal η C W V Wη Vη b Qε Dη
    V0 qOrder Ktail Gsource C2source Hsource Ssafe Jsafe E E2 Z payment
  have h234 := hfor n hnConcentration.1 512 (by norm_num) z
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) hz)
  rcases h234 with
    ⟨hP₀prob, hP₀map, hνprob, hq, hε, hεlim, hξPacket, hξenergy, hYpacket,
      _, _, _, hηpacket, hSigned, _, _, _, hQspec,
      _, _, _, _, _, _, _, _, _, _, _, hRemainderFactor, _⟩
  letI : @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ := hP₀prob
  letI : @IsProbabilityMeasure (Fin n → Ω × ℝ) mAug ν := hνprob
  letI : @IsProbabilityMeasure (Fin n → Ω) mN P := by
    dsimp only [P, mN]
    infer_instance
  change @MeasurePreserving (Fin n → Ω × ℝ) (Fin n → Ω)
    mAug mN₀ q ν P₀ at hq
  have hFactor0 :
      ∃ G1 G2 : (Fin n → ℝ) → ℝ,
        Measurable[borel (Fin n → ℝ), borel ℝ] G1 ∧
        Measurable[borel (Fin n → ℝ), borel ℝ] G2 ∧
        ∀ x : Fin n → Ω × ℝ,
          Dη 0 x = G1 (C 0 x) ∧ D2 (q x) = G2 (C 0 x) :=
    hRemainderFactor 0
  let G1 : (Fin n → ℝ) → ℝ := Classical.choose hFactor0
  let G2 : (Fin n → ℝ) → ℝ :=
    Classical.choose (Classical.choose_spec hFactor0)
  have hFactors :
      Measurable[borel (Fin n → ℝ), borel ℝ] G1 ∧
      Measurable[borel (Fin n → ℝ), borel ℝ] G2 ∧
      ∀ x : Fin n → Ω × ℝ,
        Dη 0 x = G1 (C 0 x) ∧ D2 (q x) = G2 (C 0 x) :=
    Classical.choose_spec (Classical.choose_spec hFactor0)
  have hCm : Measurable[mAug, borel (Fin n → ℝ)] (C 0) := by
    rw [borel_pi]
    apply measurable_pi_iff.2
    intro i
    exact (((hηpacket 0).2.2.2.1) i).1
  have hDη0m : Measurable[mAug, borel ℝ] (Dη 0) := by
    have hEq : Dη 0 = fun x => G1 (C 0 x) :=
      funext (fun x => (hFactors.2.2 x).1)
    rw [hEq]
    exact hFactors.1.comp hCm
  have hD2aug : Measurable[mAug, borel ℝ] (fun x => D2 (q x)) := by
    have hEq : (fun x => D2 (q x)) = fun x => G2 (C 0 x) :=
      funext (fun x => (hFactors.2.2 x).2)
    rw [hEq]
    exact hFactors.2.1.comp hCm
  have hD1aug : Measurable[mAug, borel ℝ] (fun x => D1 (q x)) := by
    have hEq : (fun x => D1 (q x)) = fun x => Dη 0 x - Qε 0 x := by
      funext x
      have hsigned : Dη 0 x = D1 (q x) + Qε 0 x := (hSigned 0 x).1
      linarith only [hsigned]
    rw [hEq]
    exact hDη0m.sub (hQspec 0).1
  -- The fixed section is used only for measurability, never for probability transport.
  let t : (Fin n → Ω) → (Fin n → Ω × ℝ) :=
    fun ζ i => (ζ i, (1 / 2 : ℝ))
  have ht : Measurable[mN₀, mAug] t := by
    apply (@measurable_pi_iff (Fin n → Ω) (Fin n) (fun _ : Fin n => Ω × ℝ)
      mN₀ (fun _ : Fin n => mAugLocal) t).2
    intro i
    exact (@measurable_pi_apply (Fin n) (fun _ : Fin n => Ω)
      (fun _ : Fin n => m₀) i).prodMk measurable_const
  have hD1m : Measurable[mN₀, borel ℝ] D1 := by
    have hm := hD1aug.comp ht
    simpa only [Function.comp_def, q, t] using hm
  have hD2m : Measurable[mN₀, borel ℝ] D2 := by
    have hm := hD2aug.comp ht
    simpa only [Function.comp_def, q, t] using hm
  have hξ0m (i : Fin n) : Measurable[mN₀, borel ℝ] (ξ0 i) := by
    have hm := ((hξPacket i).1).comp ht
    simpa only [Function.comp_def, ξ, ξlocal, ξ0, t] using hm
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
  have hSsafe : @MeasurableSet (Fin n → Ω) mN₀ Ssafe := by
    change @MeasurableSet (Fin n → Ω) mN₀
      {ζ : Fin n → Ω | 0 < V0 ζ ∧ z * |D1 ζ| ≤ V0 ζ / 8 ∧
        z ^ (2 : ℕ) * |D2 ζ| ≤ (1 / 8 : ℝ)}
    exact (measurableSet_lt measurable_const hV0m).inter
      ((measurableSet_le
        (measurable_const.mul (continuous_abs.measurable.comp hD1m))
        (hV0m.div_const 8)).inter
        (measurableSet_le
          (measurable_const.mul (continuous_abs.measurable.comp hD2m))
          measurable_const))
  let idΩ : Ω → Ω := id
  let idSample : (Fin n → Ω) → (Fin n → Ω) := id
  have hidΩ : Measurable[mΩ, m₀] idΩ := measurable_id'' hm₀
  have hidN : Measurable[mN, mN₀] idSample := by
    apply (@measurable_pi_iff (Fin n → Ω) (Fin n) (fun _ : Fin n => Ω)
      mN (fun _ : Fin n => m₀) idSample).2
    intro i
    exact hidΩ.comp
      (@measurable_pi_apply (Fin n) (fun _ : Fin n => Ω)
        (fun _ : Fin n => mΩ) i)
  have hSoriginal : @MeasurableSet (Fin n → Ω) mN Ssafe := by
    have hm := hSsafe.preimage hidN
    simpa only [idSample, Set.preimage_id] using hm
  have hJm : @MeasurableSet (Fin n → Ω × ℝ) mAug Jsafe :=
    hSsafe.preimage hq.measurable
  -- Original233 supplies a concentration subset and fee, without reduced H measurability.
  have hOriginalGood := hnConcentration.2 r w hr hr1 hcR hcL
    hW hWR hSq hSqBound hEnv hsym 512 rho z
    (by norm_num) (Real.sqrt_nonneg v) hz hzWindow
  rcases hOriginalGood with ⟨hHsourceMeas, hHmargin, hZeroOriginal, hHpay⟩
  change @MeasurableSet (Fin n → Ω) mN Hsource at hHsourceMeas
  change P.real Hsourceᶜ ≤ payment at hHpay
  change ({ζ : Fin n → Ω | V0 ζ = 0} ∪
    {ζ : Fin n → Ω | Real.sqrt (centeredSq n g r ζ) = 0}) ⊆ Hsourceᶜ
    at hZeroOriginal
  have hHsubset : Hsource ⊆ Ssafe := by
    intro ζ hζ
    rcases hHmargin ζ hζ with
      ⟨hVpos, _, hNum, _, _, _, _, _, hClipScaled, _⟩
    change 0 < V0 ζ ∧ z * |D1 ζ| ≤ V0 ζ / 8 ∧
      z ^ (2 : ℕ) * |D2 ζ| ≤ (1 / 8 : ℝ)
    change z ^ (2 : ℕ) * |D2 ζ| ≤ (1 / 32 : ℝ) at hClipScaled
    refine ⟨hVpos, hNum, ?_⟩
    linarith only [hClipScaled]
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
    rw [hP₀map]
    simpa only [idSample, Set.preimage_id] using
      (map_measureReal_apply (μ := P) hidN hSsafe.compl)
  have hPcmono : P.real Ssafeᶜ ≤ P.real Hsourceᶜ := by
    apply measureReal_mono
    intro ζ hζ hH
    exact hζ (hHsubset hH)
  have hJpay : ν.real Jsafeᶜ ≤ payment := by
    calc
      ν.real Jsafeᶜ = P₀.real Ssafeᶜ := hνSafe
      _ = P.real Ssafeᶜ := hPSafe
      _ ≤ P.real Hsourceᶜ := hPcmono
      _ ≤ payment := hHpay
  -- Apply232 to the literal same normalized family from the one retained model.
  have hPayment :=
    @Shao.OQ6.NormalizedUpperErrorGoodsetPayment.actual_normalized_upper_error_goodset_payment
      (Fin n → Ω × ℝ) mAug ν hνprob n
      (Nat.le_trans (by norm_num : (1 : ℕ) ≤ 4) hnConcentration.1) ξ
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
    @MeasurableSet (Fin n → Ω × ℝ) mAug
      {x : Fin n → Ω × ℝ | z * |D1 (q x) + Qε k x| > Vη k x / 4})
    at hNumMeas
  simp only [hDηbridge] at hNumMeas
  change (∀ k : ℕ, Measurable[mAug, borel ℝ] (Qε k) ∧
    Measurable[mAug, borel ℝ] (Dη k) ∧
    @MeasurableSet (Fin n → Ω × ℝ) mAug (E k)) at hNumMeas
  change (∀ x : Fin n → Ω × ℝ,
    Filter.Tendsto (fun k : ℕ => D1 (q x) + Qε k x)
      Filter.atTop (nhds (D1 (q x)))) at hDpoint
  simp only [hDηbridge] at hDpoint
  change (∀ x : Fin n → Ω × ℝ, x ∈ Jsafe →
    ∀ᶠ k : ℕ in Filter.atTop,
      0 < Vη k x ∧ z * |D1 (q x) + Qε k x| ≤ Vη k x / 4) at hSafe
  simp only [hDηbridge] at hSafe
  change E2 ⊆ Jsafeᶜ at hE2subset
  change Z ⊆ Jsafeᶜ at hZsubset
  change ν.real E2 ≤ ν.real Jsafeᶜ at hE2fee
  change ν.real Z ≤ ν.real Jsafeᶜ at hZfee
  change (∀ δ : ℝ, 0 < δ →
    ∀ᶠ k : ℕ in Filter.atTop,
      ν.real {x : Fin n → Ω × ℝ |
        z * |D1 (q x) + Qε k x| > Vη k x / 4} ≤ ν.real Jsafeᶜ + δ)
    at hEventual
  simp only [hDηbridge] at hEventual
  change (∀ δ : ℝ, 0 < δ →
    ∀ᶠ k : ℕ in Filter.atTop, ν.real (E k) ≤ ν.real Jsafeᶜ + δ)
    at hEventual
  change Filter.limsup
    (fun k : ℕ => ν.real {x : Fin n → Ω × ℝ |
      z * |D1 (q x) + Qε k x| > Vη k x / 4})
    Filter.atTop ≤ ν.real Jsafeᶜ at hLimsup
  simp only [hDηbridge] at hLimsup
  change Filter.limsup (fun k : ℕ => ν.real (E k))
    Filter.atTop ≤ ν.real Jsafeᶜ at hLimsup
  have hEventualPay (δ : ℝ) (hδ : 0 < δ) :
      ∀ᶠ k : ℕ in Filter.atTop, ν.real (E k) ≤ payment + δ := by
    filter_upwards [hEventual δ hδ] with k hk
    exact hk.trans (add_le_add_right hJpay δ)
  exact ⟨hV0m, hD1m, hD2m, hD1aug, hD2aug, hWV,
    hHsourceMeas, hSsafe, hSoriginal, hJm, hHsubset, hJmargin,
    hνSafe, hPSafe, hPcmono, hHpay, hJpay, hZeroOriginal,
    hηm, hNumMeas, hE2Zmeas, hηpoint, hWpoint, hVpoint, hQpoint,
    hDpoint, hD2good, hSafe, hE2subset, hZsubset, hE2fee, hZfee,
    hE2fee.trans hJpay, hZfee.trans hJpay, hEventual, hLimsup,
    hEventualPay, hLimsup.trans hJpay⟩


end
end Shao.OQ6.OriginalSameWitnessUpperErrorPayment
