import Shao.OQ6.OriginalLiteralWeightedConsumer
import Shao.OQ6.NormalizedStrictMomentBudgets
import Shao.OQ6.IIDSourceStrictMomentBudgets

set_option autoImplicit false
universe u
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology MeasureTheory
open Shao.OQ5.P51
namespace Shao.OQ6.OriginalSingleWitnessAnalyticStrictFrontier
noncomputable section

theorem actual_original_single_witness_analytic_strict_frontier
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
                |compactCostη k - compactCost0| < τ))) := by
  classical
  intro g r v rho β cWindow
  have hgOriginal : Measurable[mΩ, borel ℝ] g :=
    hh.stronglyMeasurable.integral_prod_right'.measurable
  have hgSecond : (∫ o, g o ^ 2 ∂μ) = 1 := hprojectionsecond
  have hgSquareIntegrable : Integrable (fun o => g o ^ 2) μ := by
    by_contra hnot
    have hzero : (∫ o, g o ^ 2 ∂μ) = 0 := integral_undef hnot
    exact one_ne_zero (hgSecond.symm.trans hzero)
  have hg2Original : MemLp g 2 μ :=
    (memLp_two_iff_integrable_sq hgOriginal.aestronglyMeasurable).2
      hgSquareIntegrable
  have hOriginalBudget :=
    Shao.OQ6.IIDSourceStrictMomentBudgets.actual_iid_source_z_strict_moment_budgets
      μ g hgOriginal hg2Original p hp2 hp3 hgp cBudget hcBudget
  dsimp only at hOriginalBudget
  rcases hOriginalBudget with ⟨hβ, hcWindow, hcWindowPower, hcWindowSmall, hSource⟩
  refine ⟨hgOriginal, hg2Original, hβ, hcWindow, hcWindowPower, hcWindowSmall, ?_⟩
  have hOriginal :=
    Shao.OQ6.OriginalLiteralWeightedConsumer.actual_original_literal_weighted_consumer
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
  intro
    mN mN₀ P P₀ N K ε ξ0 D1
    D2 T0 A0 B0 A0delete B0delete lambda01 mAugLocal mAug
    νlocal ν q c ξlocal Ylocal ξ Y a
    s ηlocal η C W V Wη Vη b
    Qε Dη Tη A B Adelete Bdelete Vdelete H
    Hdelete M Mdelete Anew AdeleteNew Δ ℓ0 ℓη S0
    Sη S0minus Sηminus I0 Iη fullTest0 fullTestη deletedTest0 deletedTestη
    compactDeletedTest0 compactDeletedTestη Lcompact0 Lcompactη sourceCost0 sourceCostη compactCost0 compactCostη Fz
    δ0 δreduced δν δη L0 Lν Lη scalarBudget
  have hAnalytic := hfor n hn C0 hC0 z hz
  rcases hAnalytic with
    ⟨hP₀prob, hP₀map, hνprob, hq, hε, hεlim, hξPacket, hξenergy, hYpacket,
      hD2bounds, hT0zero, hTηzero, hηpacket, hSigned, hHm, hHint, hHd,
      hQspec, hQlim, hAnew, hAdnew, hAnewL1, hAdnewL1, hAlim, hAdlim,
      hΔeq, hΔI, hFullFactor, hDeletedFactor, hRemainderFactor,
      hFullI, hFullηI, hDelI, hDelηI, hCompactI, hCompactηI,
      hIpos, hIηpos, hIlim, hFullLim, hDelLim, hFullRatio, hDelRatio,
      hCompactLim, hSourceLim, hCostLim⟩
  letI : @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ := hP₀prob
  letI : @IsProbabilityMeasure (Fin n → Ω × ℝ) mAug ν := hνprob
  change @MeasurePreserving (Fin n → Ω × ℝ) (Fin n → Ω) mAug mN₀ q ν P₀ at hq
  refine ⟨hP₀prob, hP₀map, hνprob, hq, hε, hεlim, hξPacket, hξenergy, hYpacket,
    hD2bounds, hT0zero, hTηzero, hηpacket, hSigned, hHm, hHint, hHd,
    hQspec, hQlim, hAnew, hAdnew, hAnewL1, hAdnewL1, hAlim, hAdlim,
    hΔeq, hΔI, hFullFactor, hDeletedFactor, hRemainderFactor,
    hFullI, hFullηI, hDelI, hDelηI, hCompactI, hCompactηI,
    hIpos, hIηpos, hIlim, hFullLim, hDelLim, hFullRatio, hDelRatio,
    hCompactLim, hSourceLim, hCostLim, ?_⟩
  intro hz1
  have hn1 : 1 ≤ n := by omega
  rcases hSource n hn1 z hz1 with
    ⟨hPprob, hScalarI, hSourceI, hδScalar, hLScalar, hLi, hδNonneg,
      hLNonneg, hRate, hZero, hSourceStrict⟩
  change @IsProbabilityMeasure (Fin n → Ω) mN P at hPprob
  letI : @IsProbabilityMeasure (Fin n → Ω) mN P := hPprob
  change Integrable[mΩ] (fun o : Ω => Fz (g o / N)) μ at hScalarI
  change (∀ i : Fin n, Integrable[mN] (fun ζ => Fz (ξ0 i ζ)) P) at hSourceI
  change (∀ i : Fin n, δ0 i = scalarBudget) at hδScalar
  change L0 = (n : ℝ) * scalarBudget at hLScalar
  change (∀ i : Fin n, L0 = (n : ℝ) * δ0 i) at hLi
  change (∀ i : Fin n, 0 ≤ δ0 i) at hδNonneg
  change 0 ≤ L0 at hLNonneg
  change L0 ≤ β * Real.rpow z p / Real.rpow (n : ℝ) ((p - 2) / 2) at hRate
  change (β = 0 → L0 = 0 ∧ (∀ i : Fin n, δ0 i = 0)) at hZero
  let «section» : (Fin n → Ω) → (Fin n → Ω × ℝ) :=
    fun ζ i => (ζ i, (1 / 2 : ℝ))
  let sourceTest : Fin n → (Fin n → Ω) → ℝ :=
    fun i ζ => Fz (ξ0 i ζ)
  let augmentedTest : Fin n → (Fin n → Ω × ℝ) → ℝ :=
    fun i x => Fz (ξ i x)
  have hSection : Measurable[mN₀, mAug] «section» := by
    apply (@measurable_pi_iff (Fin n → Ω) (Fin n) (fun _ : Fin n => Ω × ℝ)
      mN₀ (fun _ : Fin n => mAugLocal) «section»).2
    intro i
    exact (@measurable_pi_apply (Fin n) (fun _ : Fin n => Ω)
      (fun _ : Fin n => m₀) i).prodMk measurable_const
  have hqSection (ζ : Fin n → Ω) : q («section» ζ) = ζ := by
    rfl
  have hξ0Section (i : Fin n) (ζ : Fin n → Ω) :
      ξ i («section» ζ) = ξ0 i ζ := by
    rfl
  have hξ0Reduced (i : Fin n) : Measurable[mN₀, borel ℝ] (ξ0 i) := by
    have hm := ((hξPacket i).1).comp hSection
    simpa only [Function.comp_def, hξ0Section] using hm
  have hFzReduced (i : Fin n) :
      Measurable[mN₀, borel ℝ] (sourceTest i) := by
    change Measurable[mN₀, borel ℝ]
      (fun ζ => (z * ξ0 i ζ) ^ 2 * min |z * ξ0 i ζ| 1)
    exact ((measurable_const.mul (hξ0Reduced i)).pow_const 2).mul
      ((continuous_abs.measurable.comp
        (measurable_const.mul (hξ0Reduced i))).min measurable_const)
  have hidΩ : Measurable[mΩ, m₀] (id : Ω → Ω) :=
    measurable_id'' hm₀
  have hidN : Measurable[mN, mN₀] (id : (Fin n → Ω) → (Fin n → Ω)) := by
    apply (@measurable_pi_iff (Fin n → Ω) (Fin n) (fun _ : Fin n => Ω)
      mN (fun _ : Fin n => m₀) (id : (Fin n → Ω) → (Fin n → Ω))).2
    intro i
    exact hidΩ.comp
      (@measurable_pi_apply (Fin n) (fun _ : Fin n => Ω)
        (fun _ : Fin n => mΩ) i)
  have hId : @MeasurePreserving (Fin n → Ω) (Fin n → Ω) mN mN₀ id P P₀ :=
    @MeasurePreserving.mk (Fin n → Ω) (Fin n → Ω) mN mN₀ id P P₀
      hidN hP₀map.symm
  have hOriginalIntegral (i : Fin n) : δreduced i = δ0 i := by
    have hm :=
      @integral_map_of_stronglyMeasurable (Fin n → Ω) ℝ
        (inferInstance : NormedAddCommGroup ℝ) (inferInstance : NormedSpace ℝ ℝ)
        mN P (Fin n → Ω) mN₀ id hidN (sourceTest i)
        ((hFzReduced i).stronglyMeasurable : StronglyMeasurable (sourceTest i))
    rw [hP₀map.symm] at hm
    simpa only [δreduced, δ0, sourceTest, Function.comp_def, id_eq] using hm
  have hAugIntegral (i : Fin n) : δν i = δreduced i := by
    have hm :=
      @integral_map (Fin n → Ω × ℝ) ℝ
        (inferInstance : NormedAddCommGroup ℝ) (inferInstance : NormedSpace ℝ ℝ)
        mAug ν (Fin n → Ω) mN₀ q hq.aemeasurable (sourceTest i)
        ((hFzReduced i).aestronglyMeasurable :
          AEStronglyMeasurable (sourceTest i)
            (@Measure.map (Fin n → Ω × ℝ) (Fin n → Ω) mAug mN₀ q ν))
    rw [hq.map_eq] at hm
    simpa only [δν, δreduced, sourceTest, Function.comp_def, ξ, ξlocal, ξ0, q]
      using hm.symm
  have hReducedI (i : Fin n) : Integrable[mN₀] (sourceTest i) P₀ :=
    (hId.integrable_comp (hFzReduced i).aestronglyMeasurable).1 (hSourceI i)
  have hAugI (i : Fin n) : Integrable[mAug] (augmentedTest i) ν := by
    have hi := hq.integrable_comp_of_integrable (hReducedI i)
    simpa only [Function.comp_def, augmentedTest, sourceTest, ξ, ξlocal, ξ0, q]
      using hi
  have hδJoin (i : Fin n) : δν i = δ0 i :=
    (hAugIntegral i).trans (hOriginalIntegral i)
  have hLJoin : Lν = L0 :=
    Finset.sum_congr rfl (fun i _ => hδJoin i)
  refine ⟨hScalarI, ?_, hLScalar, hLi, hδNonneg, hLNonneg, hLJoin, hRate, hZero, ?_⟩
  · intro i
    exact ⟨hFzReduced i, hSourceI i, hReducedI i, hAugI i,
      hOriginalIntegral i, hδJoin i, hδScalar i⟩
  intro hwindow
  rcases hSourceStrict hwindow with ⟨hLc, hδHalf, hLStrict⟩
  change L0 ≤ Real.rpow cWindow p at hLc
  change (∀ i : Fin n, δ0 i < (1 / 2 : ℝ)) at hδHalf
  change L0 < cBudget * z ^ 2 at hLStrict
  have hδνHalf : ∀ i : Fin n, δν i < (1 / 2 : ℝ) := by
    intro i
    rw [hδJoin i]
    exact hδHalf i
  have hLνStrict : Lν < cBudget * z ^ 2 := by
    rw [hLJoin]
    exact hLStrict
  have h229 :=
    @Shao.OQ6.NormalizedStrictMomentBudgets.actual_source_z_strict_truncated_moment_budgets
      (Fin n → Ω × ℝ) mAug ν hνprob n hn1 ξ
      (fun i => (hξPacket i).1) (fun i => (hξPacket i).2.1)
      (fun i => (hξPacket i).2.2) hξenergy Y
      (fun k i => (hYpacket k i).2.1) ε
      (fun k => (hε k).1) (fun k => (hε k).2) hεlim
      (fun k i => (hYpacket k i).2.2) z hz1 cBudget hcBudget
  dsimp only at h229
  rcases h229 hδνHalf hLνStrict with
    ⟨hδνI, hδηI, hδlim, hLlim, kStrict, hkStrict⟩
  change (∀ (k : ℕ) (i : Fin n),
    Integrable[mAug] (fun x => Fz (η k i x)) ν) at hδηI
  change (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => δη k i)
    Filter.atTop (nhds (δν i))) at hδlim
  simp_rw [hδJoin] at hδlim
  change Filter.Tendsto Lη Filter.atTop (nhds Lν) at hLlim
  rw [hLJoin] at hLlim
  change (∀ k : ℕ, kStrict ≤ k →
    (∀ i : Fin n, δη k i < (1 / 2 : ℝ)) ∧ Lη k < cBudget * z ^ 2) at hkStrict
  refine ⟨hLc, hδHalf, hLStrict, hδηI, hδlim, hLlim, ?_⟩
  intro τ hτ
  have hStrictEvent : ∀ᶠ k : ℕ in Filter.atTop,
      (∀ i : Fin n, δη k i < (1 / 2 : ℝ)) ∧ Lη k < cBudget * z ^ 2 :=
    Filter.eventually_atTop.2 ⟨kStrict, hkStrict⟩
  have hδEvent : ∀ᶠ k : ℕ in Filter.atTop,
      ∀ i : Fin n, |δη k i - δ0 i| < τ := by
    apply Filter.eventually_all.2
    intro i
    exact
      ((hδlim i).sub_const (δ0 i)).abs.eventually (by simpa only [sub_self, abs_zero] using (eventually_lt_nhds hτ))
  have hLEvent : ∀ᶠ k : ℕ in Filter.atTop, |Lη k - L0| < τ := by
    exact
      (hLlim.sub_const L0).abs.eventually (by simpa only [sub_self, abs_zero] using (eventually_lt_nhds hτ))
  have hQEvent : ∀ᶠ k : ℕ in Filter.atTop, (∫ x, |Qε k x| ∂ν) < τ :=
    hQlim.eventually (by simpa only [sub_self, abs_zero] using (eventually_lt_nhds hτ))
  have hAEvent : ∀ᶠ k : ℕ in Filter.atTop,
      (∫ x, |Anew k x - A x| ∂ν) < τ :=
    hAlim.eventually (by simpa only [sub_self, abs_zero] using (eventually_lt_nhds hτ))
  have hAdEvent : ∀ᶠ k : ℕ in Filter.atTop,
      ∀ i : Fin n, (∫ x, |AdeleteNew k i x - Adelete i x| ∂ν) < τ :=
    Filter.eventually_all.2 (fun i =>
      (hAdlim i).eventually (by simpa only [sub_self, abs_zero] using (eventually_lt_nhds hτ)))
  have hIEvent : ∀ᶠ k : ℕ in Filter.atTop, |Iη k - I0| < τ := by
    exact
      (hIlim.sub_const I0).abs.eventually (by simpa only [sub_self, abs_zero] using (eventually_lt_nhds hτ))
  have hFullEvent : ∀ᶠ k : ℕ in Filter.atTop,
      |(∫ x, fullTestη k x * Real.exp (Sη k x) ∂ν) -
        (∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P)| < τ := by
    exact
      (hFullLim.sub_const
        (∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P)).abs.eventually
          (by simpa only [sub_self, abs_zero] using (eventually_lt_nhds hτ))
  have hDelEvent : ∀ᶠ k : ℕ in Filter.atTop,
      ∀ i : Fin n,
        |(∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν) -
          (∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P)| < τ := by
    apply Filter.eventually_all.2
    intro i
    exact
      ((hDelLim i).sub_const
        (∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P)).abs.eventually
          (by simpa only [sub_self, abs_zero] using (eventually_lt_nhds hτ))
  have hFullRatioEvent : ∀ᶠ k : ℕ in Filter.atTop,
      |((∫ x, fullTestη k x * Real.exp (Sη k x) ∂ν) / Iη k) -
        ((∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P) / I0)| < τ := by
    exact
      (hFullRatio.sub_const
        ((∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P) / I0)).abs.eventually
          (by simpa only [sub_self, abs_zero] using (eventually_lt_nhds hτ))
  have hDelRatioEvent : ∀ᶠ k : ℕ in Filter.atTop,
      ∀ i : Fin n,
        |((∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν) / Iη k) -
          ((∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P) / I0)| < τ := by
    apply Filter.eventually_all.2
    intro i
    exact
      ((hDelRatio i).sub_const
        ((∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P) / I0)).abs.eventually
          (by simpa only [sub_self, abs_zero] using (eventually_lt_nhds hτ))
  have hCompactEvent : ∀ᶠ k : ℕ in Filter.atTop,
      ∀ i : Fin n,
        |(∫ x, compactDeletedTestη k i x ∂ν) -
          (∫ ζ, compactDeletedTest0 i ζ ∂P)| < τ := by
    apply Filter.eventually_all.2
    intro i
    exact
      ((hCompactLim i).sub_const
        (∫ ζ, compactDeletedTest0 i ζ ∂P)).abs.eventually
          (by simpa only [sub_self, abs_zero] using (eventually_lt_nhds hτ))
  have hSourceEvent : ∀ᶠ k : ℕ in Filter.atTop,
      |sourceCostη k - sourceCost0| < τ := by
    exact
      (hSourceLim.sub_const sourceCost0).abs.eventually (by simpa only [sub_self, abs_zero] using (eventually_lt_nhds hτ))
  have hCostEvent : ∀ᶠ k : ℕ in Filter.atTop,
      |compactCostη k - compactCost0| < τ := by
    exact
      (hCostLim.sub_const compactCost0).abs.eventually (by simpa only [sub_self, abs_zero] using (eventually_lt_nhds hτ))
  have hJointEventually : ∀ᶠ k : ℕ in Filter.atTop,
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
                |compactCostη k - compactCost0| < τ := by
    filter_upwards [hStrictEvent, hδEvent, hLEvent, hQEvent, hAEvent, hAdEvent,
      hIEvent, hFullEvent, hDelEvent, hFullRatioEvent, hDelRatioEvent,
      hCompactEvent, hSourceEvent, hCostEvent] with k hkStrict hkδ hkL hkQ hkA hkAd
        hkI hkFull hkDel hkFullRatio hkDelRatio hkCompact hkSource hkCost
    exact ⟨hkStrict.1, hkStrict.2, hkδ, hkL, hkQ, hkA, hkAd, hkI,
      hkFull, hkDel, hkFullRatio, hkDelRatio, hkCompact, hkSource, hkCost⟩
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.1 hJointEventually
  exact ⟨k0, hk0⟩


end
end Shao.OQ6.OriginalSingleWitnessAnalyticStrictFrontier
