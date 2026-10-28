import Shao.OQ6.OriginalSameWitnessClippedPaidTailApplication
import Shao.OQ6.OriginalClippedStatisticMeasurable
import Shao.OQ5.P51.LiteralClippedComparison
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

set_option autoImplicit false
universe u
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology MeasureTheory symmDiff
open Shao.OQ5.P51
namespace Shao.OQ6.OriginalSameWitnessPhysicalPaidTailApplication
noncomputable section

theorem actual_original_same_witness_physical_paid_scalar_tail_application :
  ∀
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
    (cBudget : ℝ) (hcBudget : 0 < cBudget),
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
        let deletedTestUnperturbedη : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x =>
          min |z * η k i x| 1 * (|Anew k x - Adelete i x| + z * |B x - Bdelete i x|)
        let unperturbedSourceCostη : ℕ → ℝ := fun k =>
          ((∫ x, fullTestη k x * Real.exp (Sη k x) ∂ν) +
            ∑ i : Fin n, ∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) / Iη k
        (∀ i : Fin n, Measurable[mAugLocal, borel ℝ] (ξlocal i)) ∧
        (∀ (k : ℕ) (i : Fin n),
          Measurable[mAugLocal, borel ℝ] (ηlocal k i) ∧
          MeasurableSpace.comap (ηlocal k i) (borel ℝ) = mAugLocal) ∧
        (∀ k : ℕ,
          Measurable[mAug, borel (Fin n → ℝ)] (C k) ∧
          MeasurableSpace.comap (C k) (borel (Fin n → ℝ)) = mAug ∧
          ∀ (f : (Fin n → Ω × ℝ) → ℝ), Measurable[mAug, borel ℝ] f →
            ∃ F : (Fin n → ℝ) → ℝ,
              Measurable[borel (Fin n → ℝ), borel ℝ] F ∧
              ∀ x : Fin n → Ω × ℝ, f x = F (C k x)) ∧
        (∀ (k : ℕ) (i : Fin n),
          let J : Type := {j : Fin n // j ≠ i}
          let mDel : MeasurableSpace (J → Ω × ℝ) :=
            @MeasurableSpace.pi J (fun _ : J => Ω × ℝ) (fun _ : J => mAugLocal)
          let Cdel : (J → Ω × ℝ) → (J → ℝ) :=
            fun y j => ηlocal k j.val (y j)
          let pX : (Fin n → Ω × ℝ) → (J → Ω × ℝ) := fun x j => x j.val
          let pR : (Fin n → ℝ) → (J → ℝ) := fun t j => t j.val
          Measurable[mAug, mDel] pX ∧
          Measurable[borel (Fin n → ℝ), borel (J → ℝ)] pR ∧
          Measurable[mDel, borel (J → ℝ)] Cdel ∧
          MeasurableSpace.comap Cdel (borel (J → ℝ)) = mDel ∧
          (∀ x : Fin n → Ω × ℝ, pR (C k x) = Cdel (pX x)) ∧
          MeasurableSpace.comap (fun x : Fin n → Ω × ℝ => pR (C k x))
              (borel (J → ℝ)) = MeasurableSpace.comap pX mDel ∧
          ∀ (d : (J → Ω × ℝ) → ℝ), Measurable[mDel, borel ℝ] d →
            ∃ F : (J → ℝ) → ℝ,
              Measurable[borel (J → ℝ), borel ℝ] F ∧
              (∀ y : J → Ω × ℝ, d y = F (Cdel y)) ∧
              Measurable[borel (Fin n → ℝ), borel ℝ] (fun t => F (pR t)) ∧
              ∀ x : Fin n → Ω × ℝ, d (pX x) = F (pR (C k x))) ∧
        (∀ (k : ℕ) (i : Fin n),
          ∃ FAdelete FBdelete : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
            Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] FAdelete ∧
            Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] FBdelete ∧
            ∀ x : Fin n → Ω × ℝ,
              Adelete i x = FAdelete (fun j : {j : Fin n // j ≠ i} => η k j.val x) ∧
              Bdelete i x = FBdelete (fun j : {j : Fin n // j ≠ i} => η k j.val x)) ∧
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
        (∀ (k : ℕ) (x : Fin n → Ω × ℝ),
          A x + (4 * ε k * Real.sqrt (n : ℝ)) * H x = Anew k x) ∧
        (∀ (k : ℕ) (i : Fin n),
          Measurable[mAug, borel ℝ] (fun x =>
            deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
              deletedTestη k i x * Real.exp (Sηminus k i x)) ∧
          Integrable[mAug] (fun x =>
            deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
              deletedTestη k i x * Real.exp (Sηminus k i x)) ν ∧
          Integrable[mAug] (fun x =>
            |deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
              deletedTestη k i x * Real.exp (Sηminus k i x)|) ν ∧
          Integrable[mAug] (fun x =>
            deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x)) ν ∧
          (∫ x, |deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
            deletedTestη k i x * Real.exp (Sηminus k i x)| ∂ν) ≤
              |ε k| * (Real.exp ((n : ℝ) / 2) * (K * (∫ x, Hdelete i x ∂ν))) ∧
          |(∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) -
            (∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν)| ≤
              |ε k| * (Real.exp ((n : ℝ) / 2) * (K * (∫ x, Hdelete i x ∂ν)))) ∧
        (∀ i : Fin n,
          Filter.Tendsto (fun k : ℕ =>
            ∫ x, |deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
              deletedTestη k i x * Real.exp (Sηminus k i x)| ∂ν)
            Filter.atTop (nhds (0 : ℝ)) ∧
          Filter.Tendsto (fun k : ℕ =>
            (∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) -
              (∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν))
            Filter.atTop (nhds (0 : ℝ)) ∧
          Filter.Tendsto (fun k : ℕ =>
            ∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν)
            Filter.atTop (nhds (∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P)) ∧
          Filter.Tendsto (fun k : ℕ =>
            (∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) / Iη k)
            Filter.atTop (nhds ((∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P) / I0))) ∧
        (∀ k : ℕ,
          |(∑ i : Fin n, ∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) -
            (∑ i : Fin n, ∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν)| ≤
              |ε k| * ∑ i : Fin n,
                Real.exp ((n : ℝ) / 2) * (K * (∫ x, Hdelete i x ∂ν))) ∧
        Filter.Tendsto (fun k : ℕ =>
          (∑ i : Fin n, ∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) -
            (∑ i : Fin n, ∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν))
          Filter.atTop (nhds (0 : ℝ)) ∧
        Filter.Tendsto (fun k : ℕ => unperturbedSourceCostη k - sourceCostη k)
          Filter.atTop (nhds (0 : ℝ)) ∧
        Filter.Tendsto unperturbedSourceCostη Filter.atTop (nhds sourceCost0) ∧
        (∀ (cSZ C1 C2 C3 C4 : ℝ)
            (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
              cSZ C1 C2 C3 C4)
            (k : ℕ) (hz1 : 1 ≤ z)
            (hδη : ∀ i : Fin n, δη k i ≤ 1)
            (hLη : Lη k ≤ cSZ * z ^ 2),
          Shao.standardNormalTail z * Real.exp (-C1 * Lη k) *
              (1 - C2 * unperturbedSourceCostη k) ≤
            ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} ∧
          ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} ≤
            Shao.standardNormalTail z * Real.exp (C3 * Lη k) *
                (1 + C4 * unperturbedSourceCostη k) +
              ν.real {x : Fin n → Ω × ℝ | z * |Dη k x| > Vη k x / 4} +
              ν.real {x : Fin n → Ω × ℝ |
                z ^ 2 * |D2 (q x)| > (1 / 4 : ℝ)}) ∧
        (∀ (C1 C2 C3 C4 : ℝ)
            (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
              cBudget C1 C2 C3 C4)
            (hz1 : 1 ≤ z)
            (hzWindow : β = 0 ∨
              (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                Real.rpow (n : ℝ) ((p - 2) / (2 * p))))
            (τ : ℝ) (hτ : 0 < τ),
          ∃ k0 : ℕ, ∀ (k : ℕ), k0 ≤ k →
            (∀ i : Fin n, δη k i ≤ 1) ∧
            Lη k ≤ cBudget * z ^ 2 ∧
            |unperturbedSourceCostη k - sourceCost0| < τ ∧
            Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                (1 - C2 * sourceCost0) - τ ≤
              ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} ∧
            ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} ≤
              Shao.standardNormalTail z * Real.exp (C3 * L0) *
                  (1 + C4 * sourceCost0) +
                ν.real {x : Fin n → Ω × ℝ | z * |Dη k x| > Vη k x / 4} +
                ν.real {x : Fin n → Ω × ℝ |
                  z ^ 2 * |D2 (q x)| > (1 / 4 : ℝ)} + τ) ∧
        @MeasurableSet (Fin n → Ω) mN₀
          {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
        @MeasurableSet (Fin n → Ω) mN
          {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
        @MeasurableSet (Fin n → Ω × ℝ) mAug
          {x : Fin n → Ω × ℝ | z ≤ T0 (q x)} ∧
        @MeasurableSet (Fin n → Ω) mN₀
          {ζ : Fin n → Ω | projectionV n g ζ = 0} ∧
        @MeasurableSet (Fin n → Ω) mN
          {ζ : Fin n → Ω | projectionV n g ζ = 0} ∧
        @MeasurableSet (Fin n → Ω × ℝ) mAug
          {x : Fin n → Ω × ℝ | V x = 0} ∧
        ν.real {x : Fin n → Ω × ℝ | z ≤ T0 (q x)} =
          P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
        ν.real {x : Fin n → Ω × ℝ | V x = 0} =
          P.real {ζ : Fin n → Ω | projectionV n g ζ = 0} ∧
        (∀ k : ℕ,
          @MeasurableSet (Fin n → Ω × ℝ) mAug
            {x : Fin n → Ω × ℝ | z ≤ Tη k x} ∧
          ν ({x : Fin n → Ω × ℝ | z ≤ Tη k x} ∆
            {x : Fin n → Ω × ℝ | z ≤ T0 (q x)}) ≤
              ν {x : Fin n → Ω × ℝ | V x = 0} ∧
          |ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} -
            P.real {ζ : Fin n → Ω | z ≤ T0 ζ}| ≤
              P.real {ζ : Fin n → Ω | projectionV n g ζ = 0}) ∧
        (∀ (C1 C2 C3 C4 : ℝ)
            (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
              cBudget C1 C2 C3 C4)
            (hz1 : 1 ≤ z)
            (hzWindow : β = 0 ∨
              (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                Real.rpow (n : ℝ) ((p - 2) / (2 * p)))),
          Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                (1 - C2 * sourceCost0) -
            P.real {ζ : Fin n → Ω | projectionV n g ζ = 0} ≤
            P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
          ∀ (τ : ℝ) (hτ : 0 < τ),
            ∃ k0 : ℕ, ∀ (k : ℕ), k0 ≤ k →
              (∀ i : Fin n, δη k i ≤ 1) ∧
              Lη k ≤ cBudget * z ^ 2 ∧
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
              |compactCostη k - compactCost0| < τ ∧
              |unperturbedSourceCostη k - sourceCost0| < τ ∧
              Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                              (1 - C2 * sourceCost0) - τ -
                            P.real {ζ : Fin n → Ω | projectionV n g ζ = 0} ≤
                            P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
              P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ≤
                            Shao.standardNormalTail z * Real.exp (C3 * L0) *
                                (1 + C4 * sourceCost0) +
                              ν.real {x : Fin n → Ω × ℝ | z * |Dη k x| > Vη k x / 4} +
                              ν.real {x : Fin n → Ω × ℝ |
                                z ^ 2 * |D2 (q x)| > (1 / 4 : ℝ)} +
                              P.real {ζ : Fin n → Ω | projectionV n g ζ = 0} + τ) ∧
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
        let T0 : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho 1
        let L0 : ℝ := ∑ i : Fin n,
          ∫ ζ, (z * ξ0 i ζ) ^ 2 * min |z * ξ0 i ζ| 1 ∂P
        let sourceCost0 : ℝ :=
          ((∫ ζ,
              (z * |D1 ζ| + z ^ 2 * studentizerClipBudget n r 512 rho 1 ζ) *
                Real.exp (∑ j : Fin n, (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P) +
            ∑ i : Fin n, ∫ ζ,
              (min |z * ξ0 i ζ| 1 *
                (|(|D1 ζ|) - (|residualStatisticDDeleted n r ζ i|)| +
                  z * |studentizerClipBudget n r 512 rho 1 ζ -
                    studentizerClipBudgetDeleted n r 512 rho 1 ζ i|)) *
                Real.exp (∑ j ∈ Finset.univ.erase i,
                  (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P) /
            (∫ ζ, Real.exp (∑ j : Fin n,
              (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P)
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
        (∀ (C1 C2 C3 C4 : ℝ)
            (hSZcBudget : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
              cBudget C1 C2 C3 C4)
            (hzMomentWindow : β = 0 ∨
              (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                Real.rpow (n : ℝ) ((p - 2) / (2 * p)))),
          Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                (1 - C2 * sourceCost0) - payment ≤
            P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
          P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ≤
            Shao.standardNormalTail z * Real.exp (C3 * L0) *
                (1 + C4 * sourceCost0) + 3 * payment) ∧
        Filter.limsup (fun k : ℕ => ν.real (E k))
          Filter.atTop ≤ payment ∧
        (
          let Tphysical : (Fin n → Ω) → ℝ := fun ζ : Fin n → Ω =>
            if Real.sqrt (centeredSq n g r ζ) = 0 then 0 else
              (projectionW n g ζ + residualStatisticD n r ζ) /
                Real.sqrt (centeredSq n g r ζ)
          let H1source : Set (Fin n → Ω) := projectionGood n g 1 ∩ C2source
          let payment1 : ℝ := (3 : ℝ) * Real.exp (-qOrder) + Real.exp (-cg * (n : ℝ)) +
              (4 : ℝ) * Real.exp (-Real.sqrt (n : ℝ) / (2 : ℝ))
          let Ephysical : Set (Fin n → Ω) := {ζ : Fin n → Ω | T0 ζ ≠ Tphysical ζ}
          (1 : ℝ) ≤ remainderWindowScale Ktail t0 *
            Real.rpow (n : ℝ) (1 / 6 : ℝ) ∧
          @MeasurableSet (Fin n → Ω) mN H1source ∧
          P.real H1sourceᶜ ≤ payment1 ∧
          Measurable[mN, borel ℝ] Tphysical ∧
          Measurable[mN, borel ℝ] T0 ∧
          @MeasurableSet (Fin n → Ω) mN Ephysical ∧
          (∀ ζ : Fin n → Ω, ζ ∈ H1source →
            0 < projectionV n g ζ ∧
            |centeredDelta n g r ζ| ≤ (1 / 32 : ℝ) ∧
            -(1 / 2 : ℝ) ≤ centeredDelta n g r ζ) ∧
          (1 + rho ≤ Real.sqrt (n : ℝ) →
            (∀ ζ : Fin n → Ω, ζ ∈ H1source →
              D2 ζ = centeredDelta n g r ζ ∧
              0 < V0 ζ * Real.sqrt (1 + D2 ζ) ∧
              0 < Real.sqrt (centeredSq n g r ζ) ∧
              V0 ζ * Real.sqrt (1 + D2 ζ) =
                Real.sqrt (centeredSq n g r ζ) ∧
              T0 ζ = Tphysical ζ) ∧
            Ephysical ⊆ H1sourceᶜ ∧
            P.real Ephysical ≤ P.real H1sourceᶜ ∧
            P.real Ephysical ≤ payment1 ∧
            (∀ t : ℝ,
              @MeasurableSet (Fin n → Ω) mN
                {ζ : Fin n → Ω | t ≤ Tphysical ζ} ∧
              @MeasurableSet (Fin n → Ω) mN
                {ζ : Fin n → Ω | t ≤ T0 ζ} ∧
              @MeasurableSet (Fin n → Ω) mN
                {ζ : Fin n → Ω | Tphysical ζ ≤ t} ∧
              @MeasurableSet (Fin n → Ω) mN
                {ζ : Fin n → Ω | T0 ζ ≤ t} ∧
              ({ζ : Fin n → Ω | t ≤ Tphysical ζ} ∆
                {ζ : Fin n → Ω | t ≤ T0 ζ}) ⊆ Ephysical ∧
              ({ζ : Fin n → Ω | Tphysical ζ ≤ t} ∆
                {ζ : Fin n → Ω | T0 ζ ≤ t}) ⊆ Ephysical ∧
              |P.real {ζ : Fin n → Ω | t ≤ Tphysical ζ} -
                P.real {ζ : Fin n → Ω | t ≤ T0 ζ}| ≤ P.real Ephysical ∧
              |P.real {ζ : Fin n → Ω | Tphysical ζ ≤ t} -
                P.real {ζ : Fin n → Ω | T0 ζ ≤ t}| ≤ P.real Ephysical ∧
              |P.real {ζ : Fin n → Ω | t ≤ Tphysical ζ} -
                P.real {ζ : Fin n → Ω | t ≤ T0 ζ}| ≤ payment1 ∧
              |P.real {ζ : Fin n → Ω | Tphysical ζ ≤ t} -
                P.real {ζ : Fin n → Ω | T0 ζ ≤ t}| ≤ payment1) ∧
            (∀ (C1 C2 C3 C4 : ℝ)
                (hSZcBudget : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
                  cBudget C1 C2 C3 C4)
                (hzMomentWindow : β = 0 ∨
                  (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                    Real.rpow (n : ℝ) ((p - 2) / (2 * p)))),
              Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                    (1 - C2 * sourceCost0) - payment - payment1 ≤
                P.real {ζ : Fin n → Ω | z ≤ Tphysical ζ} ∧
              P.real {ζ : Fin n → Ω | z ≤ Tphysical ζ} ≤
                Shao.standardNormalTail z * Real.exp (C3 * L0) *
                    (1 + C4 * sourceCost0) + 3 * payment + payment1))))
 := by
  intro Ω mΩ μ hμProbability h hh hh2 hhsymm hcenter hprojectionsecond p hp2 hp3 hgp cBudget hcBudget
  have h247 :=
    Shao.OQ6.OriginalSameWitnessClippedPaidTailApplication.actual_original_same_witness_clipped_paid_scalar_tail_application
      μ h hh hh2 hhsymm hcenter hprojectionsecond p hp2 hp3 hgp cBudget hcBudget
  intro g r v rho β cWindow
  have hrSymm :
      ∀ o y : Ω, r o y = r y o :=
      by
        intro o y
        dsimp only [r]
        rw [hhsymm o y]
        ring
  have hRhoNonneg :
      0 ≤ rho :=
      Real.sqrt_nonneg v
  have hCg :
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
              let deletedTestUnperturbedη : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x =>
                min |z * η k i x| 1 * (|Anew k x - Adelete i x| + z * |B x - Bdelete i x|)
              let unperturbedSourceCostη : ℕ → ℝ := fun k =>
                ((∫ x, fullTestη k x * Real.exp (Sη k x) ∂ν) +
                  ∑ i : Fin n, ∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) / Iη k
              (∀ i : Fin n, Measurable[mAugLocal, borel ℝ] (ξlocal i)) ∧
              (∀ (k : ℕ) (i : Fin n),
                Measurable[mAugLocal, borel ℝ] (ηlocal k i) ∧
                MeasurableSpace.comap (ηlocal k i) (borel ℝ) = mAugLocal) ∧
              (∀ k : ℕ,
                Measurable[mAug, borel (Fin n → ℝ)] (C k) ∧
                MeasurableSpace.comap (C k) (borel (Fin n → ℝ)) = mAug ∧
                ∀ (f : (Fin n → Ω × ℝ) → ℝ), Measurable[mAug, borel ℝ] f →
                  ∃ F : (Fin n → ℝ) → ℝ,
                    Measurable[borel (Fin n → ℝ), borel ℝ] F ∧
                    ∀ x : Fin n → Ω × ℝ, f x = F (C k x)) ∧
              (∀ (k : ℕ) (i : Fin n),
                let J : Type := {j : Fin n // j ≠ i}
                let mDel : MeasurableSpace (J → Ω × ℝ) :=
                  @MeasurableSpace.pi J (fun _ : J => Ω × ℝ) (fun _ : J => mAugLocal)
                let Cdel : (J → Ω × ℝ) → (J → ℝ) :=
                  fun y j => ηlocal k j.val (y j)
                let pX : (Fin n → Ω × ℝ) → (J → Ω × ℝ) := fun x j => x j.val
                let pR : (Fin n → ℝ) → (J → ℝ) := fun t j => t j.val
                Measurable[mAug, mDel] pX ∧
                Measurable[borel (Fin n → ℝ), borel (J → ℝ)] pR ∧
                Measurable[mDel, borel (J → ℝ)] Cdel ∧
                MeasurableSpace.comap Cdel (borel (J → ℝ)) = mDel ∧
                (∀ x : Fin n → Ω × ℝ, pR (C k x) = Cdel (pX x)) ∧
                MeasurableSpace.comap (fun x : Fin n → Ω × ℝ => pR (C k x))
                    (borel (J → ℝ)) = MeasurableSpace.comap pX mDel ∧
                ∀ (d : (J → Ω × ℝ) → ℝ), Measurable[mDel, borel ℝ] d →
                  ∃ F : (J → ℝ) → ℝ,
                    Measurable[borel (J → ℝ), borel ℝ] F ∧
                    (∀ y : J → Ω × ℝ, d y = F (Cdel y)) ∧
                    Measurable[borel (Fin n → ℝ), borel ℝ] (fun t => F (pR t)) ∧
                    ∀ x : Fin n → Ω × ℝ, d (pX x) = F (pR (C k x))) ∧
              (∀ (k : ℕ) (i : Fin n),
                ∃ FAdelete FBdelete : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
                  Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] FAdelete ∧
                  Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] FBdelete ∧
                  ∀ x : Fin n → Ω × ℝ,
                    Adelete i x = FAdelete (fun j : {j : Fin n // j ≠ i} => η k j.val x) ∧
                    Bdelete i x = FBdelete (fun j : {j : Fin n // j ≠ i} => η k j.val x)) ∧
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
              (∀ (k : ℕ) (x : Fin n → Ω × ℝ),
                A x + (4 * ε k * Real.sqrt (n : ℝ)) * H x = Anew k x) ∧
              (∀ (k : ℕ) (i : Fin n),
                Measurable[mAug, borel ℝ] (fun x =>
                  deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
                    deletedTestη k i x * Real.exp (Sηminus k i x)) ∧
                Integrable[mAug] (fun x =>
                  deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
                    deletedTestη k i x * Real.exp (Sηminus k i x)) ν ∧
                Integrable[mAug] (fun x =>
                  |deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
                    deletedTestη k i x * Real.exp (Sηminus k i x)|) ν ∧
                Integrable[mAug] (fun x =>
                  deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x)) ν ∧
                (∫ x, |deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
                  deletedTestη k i x * Real.exp (Sηminus k i x)| ∂ν) ≤
                    |ε k| * (Real.exp ((n : ℝ) / 2) * (K * (∫ x, Hdelete i x ∂ν))) ∧
                |(∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) -
                  (∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν)| ≤
                    |ε k| * (Real.exp ((n : ℝ) / 2) * (K * (∫ x, Hdelete i x ∂ν)))) ∧
              (∀ i : Fin n,
                Filter.Tendsto (fun k : ℕ =>
                  ∫ x, |deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
                    deletedTestη k i x * Real.exp (Sηminus k i x)| ∂ν)
                  Filter.atTop (nhds (0 : ℝ)) ∧
                Filter.Tendsto (fun k : ℕ =>
                  (∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) -
                    (∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν))
                  Filter.atTop (nhds (0 : ℝ)) ∧
                Filter.Tendsto (fun k : ℕ =>
                  ∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν)
                  Filter.atTop (nhds (∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P)) ∧
                Filter.Tendsto (fun k : ℕ =>
                  (∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) / Iη k)
                  Filter.atTop (nhds ((∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P) / I0))) ∧
              (∀ k : ℕ,
                |(∑ i : Fin n, ∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) -
                  (∑ i : Fin n, ∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν)| ≤
                    |ε k| * ∑ i : Fin n,
                      Real.exp ((n : ℝ) / 2) * (K * (∫ x, Hdelete i x ∂ν))) ∧
              Filter.Tendsto (fun k : ℕ =>
                (∑ i : Fin n, ∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) -
                  (∑ i : Fin n, ∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν))
                Filter.atTop (nhds (0 : ℝ)) ∧
              Filter.Tendsto (fun k : ℕ => unperturbedSourceCostη k - sourceCostη k)
                Filter.atTop (nhds (0 : ℝ)) ∧
              Filter.Tendsto unperturbedSourceCostη Filter.atTop (nhds sourceCost0) ∧
              (∀ (cSZ C1 C2 C3 C4 : ℝ)
                  (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
                    cSZ C1 C2 C3 C4)
                  (k : ℕ) (hz1 : 1 ≤ z)
                  (hδη : ∀ i : Fin n, δη k i ≤ 1)
                  (hLη : Lη k ≤ cSZ * z ^ 2),
                Shao.standardNormalTail z * Real.exp (-C1 * Lη k) *
                    (1 - C2 * unperturbedSourceCostη k) ≤
                  ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} ∧
                ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} ≤
                  Shao.standardNormalTail z * Real.exp (C3 * Lη k) *
                      (1 + C4 * unperturbedSourceCostη k) +
                    ν.real {x : Fin n → Ω × ℝ | z * |Dη k x| > Vη k x / 4} +
                    ν.real {x : Fin n → Ω × ℝ |
                      z ^ 2 * |D2 (q x)| > (1 / 4 : ℝ)}) ∧
              (∀ (C1 C2 C3 C4 : ℝ)
                  (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
                    cBudget C1 C2 C3 C4)
                  (hz1 : 1 ≤ z)
                  (hzWindow : β = 0 ∨
                    (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                      Real.rpow (n : ℝ) ((p - 2) / (2 * p))))
                  (τ : ℝ) (hτ : 0 < τ),
                ∃ k0 : ℕ, ∀ (k : ℕ), k0 ≤ k →
                  (∀ i : Fin n, δη k i ≤ 1) ∧
                  Lη k ≤ cBudget * z ^ 2 ∧
                  |unperturbedSourceCostη k - sourceCost0| < τ ∧
                  Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                      (1 - C2 * sourceCost0) - τ ≤
                    ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} ∧
                  ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} ≤
                    Shao.standardNormalTail z * Real.exp (C3 * L0) *
                        (1 + C4 * sourceCost0) +
                      ν.real {x : Fin n → Ω × ℝ | z * |Dη k x| > Vη k x / 4} +
                      ν.real {x : Fin n → Ω × ℝ |
                        z ^ 2 * |D2 (q x)| > (1 / 4 : ℝ)} + τ) ∧
              @MeasurableSet (Fin n → Ω) mN₀
                {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
              @MeasurableSet (Fin n → Ω) mN
                {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
              @MeasurableSet (Fin n → Ω × ℝ) mAug
                {x : Fin n → Ω × ℝ | z ≤ T0 (q x)} ∧
              @MeasurableSet (Fin n → Ω) mN₀
                {ζ : Fin n → Ω | projectionV n g ζ = 0} ∧
              @MeasurableSet (Fin n → Ω) mN
                {ζ : Fin n → Ω | projectionV n g ζ = 0} ∧
              @MeasurableSet (Fin n → Ω × ℝ) mAug
                {x : Fin n → Ω × ℝ | V x = 0} ∧
              ν.real {x : Fin n → Ω × ℝ | z ≤ T0 (q x)} =
                P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
              ν.real {x : Fin n → Ω × ℝ | V x = 0} =
                P.real {ζ : Fin n → Ω | projectionV n g ζ = 0} ∧
              (∀ k : ℕ,
                @MeasurableSet (Fin n → Ω × ℝ) mAug
                  {x : Fin n → Ω × ℝ | z ≤ Tη k x} ∧
                ν ({x : Fin n → Ω × ℝ | z ≤ Tη k x} ∆
                  {x : Fin n → Ω × ℝ | z ≤ T0 (q x)}) ≤
                    ν {x : Fin n → Ω × ℝ | V x = 0} ∧
                |ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} -
                  P.real {ζ : Fin n → Ω | z ≤ T0 ζ}| ≤
                    P.real {ζ : Fin n → Ω | projectionV n g ζ = 0}) ∧
              (∀ (C1 C2 C3 C4 : ℝ)
                  (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
                    cBudget C1 C2 C3 C4)
                  (hz1 : 1 ≤ z)
                  (hzWindow : β = 0 ∨
                    (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                      Real.rpow (n : ℝ) ((p - 2) / (2 * p)))),
                Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                      (1 - C2 * sourceCost0) -
                  P.real {ζ : Fin n → Ω | projectionV n g ζ = 0} ≤
                  P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
                ∀ (τ : ℝ) (hτ : 0 < τ),
                  ∃ k0 : ℕ, ∀ (k : ℕ), k0 ≤ k →
                    (∀ i : Fin n, δη k i ≤ 1) ∧
                    Lη k ≤ cBudget * z ^ 2 ∧
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
                    |compactCostη k - compactCost0| < τ ∧
                    |unperturbedSourceCostη k - sourceCost0| < τ ∧
                    Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                                    (1 - C2 * sourceCost0) - τ -
                                  P.real {ζ : Fin n → Ω | projectionV n g ζ = 0} ≤
                                  P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
                    P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ≤
                                  Shao.standardNormalTail z * Real.exp (C3 * L0) *
                                      (1 + C4 * sourceCost0) +
                                    ν.real {x : Fin n → Ω × ℝ | z * |Dη k x| > Vη k x / 4} +
                                    ν.real {x : Fin n → Ω × ℝ |
                                      z ^ 2 * |D2 (q x)| > (1 / 4 : ℝ)} +
                                    P.real {ζ : Fin n → Ω | projectionV n g ζ = 0} + τ) ∧
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
              let T0 : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho 1
              let L0 : ℝ := ∑ i : Fin n,
                ∫ ζ, (z * ξ0 i ζ) ^ 2 * min |z * ξ0 i ζ| 1 ∂P
              let sourceCost0 : ℝ :=
                ((∫ ζ,
                    (z * |D1 ζ| + z ^ 2 * studentizerClipBudget n r 512 rho 1 ζ) *
                      Real.exp (∑ j : Fin n, (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P) +
                  ∑ i : Fin n, ∫ ζ,
                    (min |z * ξ0 i ζ| 1 *
                      (|(|D1 ζ|) - (|residualStatisticDDeleted n r ζ i|)| +
                        z * |studentizerClipBudget n r 512 rho 1 ζ -
                          studentizerClipBudgetDeleted n r 512 rho 1 ζ i|)) *
                      Real.exp (∑ j ∈ Finset.univ.erase i,
                        (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P) /
                  (∫ ζ, Real.exp (∑ j : Fin n,
                    (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P)
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
              (∀ (C1 C2 C3 C4 : ℝ)
                  (hSZcBudget : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
                    cBudget C1 C2 C3 C4)
                  (hzMomentWindow : β = 0 ∨
                    (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                      Real.rpow (n : ℝ) ((p - 2) / (2 * p)))),
                Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                      (1 - C2 * sourceCost0) - payment ≤
                  P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
                P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ≤
                  Shao.standardNormalTail z * Real.exp (C3 * L0) *
                      (1 + C4 * sourceCost0) + 3 * payment) ∧
              Filter.limsup (fun k : ℕ => ν.real (E k))
                Filter.atTop ≤ payment) :=
      h247.2.2.2.2.2.2
  let cg : ℝ := Classical.choose hCg
  have hcgpos :
      0 < cg :=
      (Classical.choose_spec hCg).1
  have hModel :
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
              let deletedTestUnperturbedη : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x =>
                min |z * η k i x| 1 * (|Anew k x - Adelete i x| + z * |B x - Bdelete i x|)
              let unperturbedSourceCostη : ℕ → ℝ := fun k =>
                ((∫ x, fullTestη k x * Real.exp (Sη k x) ∂ν) +
                  ∑ i : Fin n, ∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) / Iη k
              (∀ i : Fin n, Measurable[mAugLocal, borel ℝ] (ξlocal i)) ∧
              (∀ (k : ℕ) (i : Fin n),
                Measurable[mAugLocal, borel ℝ] (ηlocal k i) ∧
                MeasurableSpace.comap (ηlocal k i) (borel ℝ) = mAugLocal) ∧
              (∀ k : ℕ,
                Measurable[mAug, borel (Fin n → ℝ)] (C k) ∧
                MeasurableSpace.comap (C k) (borel (Fin n → ℝ)) = mAug ∧
                ∀ (f : (Fin n → Ω × ℝ) → ℝ), Measurable[mAug, borel ℝ] f →
                  ∃ F : (Fin n → ℝ) → ℝ,
                    Measurable[borel (Fin n → ℝ), borel ℝ] F ∧
                    ∀ x : Fin n → Ω × ℝ, f x = F (C k x)) ∧
              (∀ (k : ℕ) (i : Fin n),
                let J : Type := {j : Fin n // j ≠ i}
                let mDel : MeasurableSpace (J → Ω × ℝ) :=
                  @MeasurableSpace.pi J (fun _ : J => Ω × ℝ) (fun _ : J => mAugLocal)
                let Cdel : (J → Ω × ℝ) → (J → ℝ) :=
                  fun y j => ηlocal k j.val (y j)
                let pX : (Fin n → Ω × ℝ) → (J → Ω × ℝ) := fun x j => x j.val
                let pR : (Fin n → ℝ) → (J → ℝ) := fun t j => t j.val
                Measurable[mAug, mDel] pX ∧
                Measurable[borel (Fin n → ℝ), borel (J → ℝ)] pR ∧
                Measurable[mDel, borel (J → ℝ)] Cdel ∧
                MeasurableSpace.comap Cdel (borel (J → ℝ)) = mDel ∧
                (∀ x : Fin n → Ω × ℝ, pR (C k x) = Cdel (pX x)) ∧
                MeasurableSpace.comap (fun x : Fin n → Ω × ℝ => pR (C k x))
                    (borel (J → ℝ)) = MeasurableSpace.comap pX mDel ∧
                ∀ (d : (J → Ω × ℝ) → ℝ), Measurable[mDel, borel ℝ] d →
                  ∃ F : (J → ℝ) → ℝ,
                    Measurable[borel (J → ℝ), borel ℝ] F ∧
                    (∀ y : J → Ω × ℝ, d y = F (Cdel y)) ∧
                    Measurable[borel (Fin n → ℝ), borel ℝ] (fun t => F (pR t)) ∧
                    ∀ x : Fin n → Ω × ℝ, d (pX x) = F (pR (C k x))) ∧
              (∀ (k : ℕ) (i : Fin n),
                ∃ FAdelete FBdelete : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
                  Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] FAdelete ∧
                  Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] FBdelete ∧
                  ∀ x : Fin n → Ω × ℝ,
                    Adelete i x = FAdelete (fun j : {j : Fin n // j ≠ i} => η k j.val x) ∧
                    Bdelete i x = FBdelete (fun j : {j : Fin n // j ≠ i} => η k j.val x)) ∧
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
              (∀ (k : ℕ) (x : Fin n → Ω × ℝ),
                A x + (4 * ε k * Real.sqrt (n : ℝ)) * H x = Anew k x) ∧
              (∀ (k : ℕ) (i : Fin n),
                Measurable[mAug, borel ℝ] (fun x =>
                  deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
                    deletedTestη k i x * Real.exp (Sηminus k i x)) ∧
                Integrable[mAug] (fun x =>
                  deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
                    deletedTestη k i x * Real.exp (Sηminus k i x)) ν ∧
                Integrable[mAug] (fun x =>
                  |deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
                    deletedTestη k i x * Real.exp (Sηminus k i x)|) ν ∧
                Integrable[mAug] (fun x =>
                  deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x)) ν ∧
                (∫ x, |deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
                  deletedTestη k i x * Real.exp (Sηminus k i x)| ∂ν) ≤
                    |ε k| * (Real.exp ((n : ℝ) / 2) * (K * (∫ x, Hdelete i x ∂ν))) ∧
                |(∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) -
                  (∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν)| ≤
                    |ε k| * (Real.exp ((n : ℝ) / 2) * (K * (∫ x, Hdelete i x ∂ν)))) ∧
              (∀ i : Fin n,
                Filter.Tendsto (fun k : ℕ =>
                  ∫ x, |deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
                    deletedTestη k i x * Real.exp (Sηminus k i x)| ∂ν)
                  Filter.atTop (nhds (0 : ℝ)) ∧
                Filter.Tendsto (fun k : ℕ =>
                  (∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) -
                    (∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν))
                  Filter.atTop (nhds (0 : ℝ)) ∧
                Filter.Tendsto (fun k : ℕ =>
                  ∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν)
                  Filter.atTop (nhds (∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P)) ∧
                Filter.Tendsto (fun k : ℕ =>
                  (∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) / Iη k)
                  Filter.atTop (nhds ((∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P) / I0))) ∧
              (∀ k : ℕ,
                |(∑ i : Fin n, ∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) -
                  (∑ i : Fin n, ∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν)| ≤
                    |ε k| * ∑ i : Fin n,
                      Real.exp ((n : ℝ) / 2) * (K * (∫ x, Hdelete i x ∂ν))) ∧
              Filter.Tendsto (fun k : ℕ =>
                (∑ i : Fin n, ∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) -
                  (∑ i : Fin n, ∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν))
                Filter.atTop (nhds (0 : ℝ)) ∧
              Filter.Tendsto (fun k : ℕ => unperturbedSourceCostη k - sourceCostη k)
                Filter.atTop (nhds (0 : ℝ)) ∧
              Filter.Tendsto unperturbedSourceCostη Filter.atTop (nhds sourceCost0) ∧
              (∀ (cSZ C1 C2 C3 C4 : ℝ)
                  (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
                    cSZ C1 C2 C3 C4)
                  (k : ℕ) (hz1 : 1 ≤ z)
                  (hδη : ∀ i : Fin n, δη k i ≤ 1)
                  (hLη : Lη k ≤ cSZ * z ^ 2),
                Shao.standardNormalTail z * Real.exp (-C1 * Lη k) *
                    (1 - C2 * unperturbedSourceCostη k) ≤
                  ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} ∧
                ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} ≤
                  Shao.standardNormalTail z * Real.exp (C3 * Lη k) *
                      (1 + C4 * unperturbedSourceCostη k) +
                    ν.real {x : Fin n → Ω × ℝ | z * |Dη k x| > Vη k x / 4} +
                    ν.real {x : Fin n → Ω × ℝ |
                      z ^ 2 * |D2 (q x)| > (1 / 4 : ℝ)}) ∧
              (∀ (C1 C2 C3 C4 : ℝ)
                  (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
                    cBudget C1 C2 C3 C4)
                  (hz1 : 1 ≤ z)
                  (hzWindow : β = 0 ∨
                    (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                      Real.rpow (n : ℝ) ((p - 2) / (2 * p))))
                  (τ : ℝ) (hτ : 0 < τ),
                ∃ k0 : ℕ, ∀ (k : ℕ), k0 ≤ k →
                  (∀ i : Fin n, δη k i ≤ 1) ∧
                  Lη k ≤ cBudget * z ^ 2 ∧
                  |unperturbedSourceCostη k - sourceCost0| < τ ∧
                  Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                      (1 - C2 * sourceCost0) - τ ≤
                    ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} ∧
                  ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} ≤
                    Shao.standardNormalTail z * Real.exp (C3 * L0) *
                        (1 + C4 * sourceCost0) +
                      ν.real {x : Fin n → Ω × ℝ | z * |Dη k x| > Vη k x / 4} +
                      ν.real {x : Fin n → Ω × ℝ |
                        z ^ 2 * |D2 (q x)| > (1 / 4 : ℝ)} + τ) ∧
              @MeasurableSet (Fin n → Ω) mN₀
                {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
              @MeasurableSet (Fin n → Ω) mN
                {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
              @MeasurableSet (Fin n → Ω × ℝ) mAug
                {x : Fin n → Ω × ℝ | z ≤ T0 (q x)} ∧
              @MeasurableSet (Fin n → Ω) mN₀
                {ζ : Fin n → Ω | projectionV n g ζ = 0} ∧
              @MeasurableSet (Fin n → Ω) mN
                {ζ : Fin n → Ω | projectionV n g ζ = 0} ∧
              @MeasurableSet (Fin n → Ω × ℝ) mAug
                {x : Fin n → Ω × ℝ | V x = 0} ∧
              ν.real {x : Fin n → Ω × ℝ | z ≤ T0 (q x)} =
                P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
              ν.real {x : Fin n → Ω × ℝ | V x = 0} =
                P.real {ζ : Fin n → Ω | projectionV n g ζ = 0} ∧
              (∀ k : ℕ,
                @MeasurableSet (Fin n → Ω × ℝ) mAug
                  {x : Fin n → Ω × ℝ | z ≤ Tη k x} ∧
                ν ({x : Fin n → Ω × ℝ | z ≤ Tη k x} ∆
                  {x : Fin n → Ω × ℝ | z ≤ T0 (q x)}) ≤
                    ν {x : Fin n → Ω × ℝ | V x = 0} ∧
                |ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} -
                  P.real {ζ : Fin n → Ω | z ≤ T0 ζ}| ≤
                    P.real {ζ : Fin n → Ω | projectionV n g ζ = 0}) ∧
              (∀ (C1 C2 C3 C4 : ℝ)
                  (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
                    cBudget C1 C2 C3 C4)
                  (hz1 : 1 ≤ z)
                  (hzWindow : β = 0 ∨
                    (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                      Real.rpow (n : ℝ) ((p - 2) / (2 * p)))),
                Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                      (1 - C2 * sourceCost0) -
                  P.real {ζ : Fin n → Ω | projectionV n g ζ = 0} ≤
                  P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
                ∀ (τ : ℝ) (hτ : 0 < τ),
                  ∃ k0 : ℕ, ∀ (k : ℕ), k0 ≤ k →
                    (∀ i : Fin n, δη k i ≤ 1) ∧
                    Lη k ≤ cBudget * z ^ 2 ∧
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
                    |compactCostη k - compactCost0| < τ ∧
                    |unperturbedSourceCostη k - sourceCost0| < τ ∧
                    Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                                    (1 - C2 * sourceCost0) - τ -
                                  P.real {ζ : Fin n → Ω | projectionV n g ζ = 0} ≤
                                  P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
                    P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ≤
                                  Shao.standardNormalTail z * Real.exp (C3 * L0) *
                                      (1 + C4 * sourceCost0) +
                                    ν.real {x : Fin n → Ω × ℝ | z * |Dη k x| > Vη k x / 4} +
                                    ν.real {x : Fin n → Ω × ℝ |
                                      z ^ 2 * |D2 (q x)| > (1 / 4 : ℝ)} +
                                    P.real {ζ : Fin n → Ω | projectionV n g ζ = 0} + τ) ∧
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
              let T0 : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho 1
              let L0 : ℝ := ∑ i : Fin n,
                ∫ ζ, (z * ξ0 i ζ) ^ 2 * min |z * ξ0 i ζ| 1 ∂P
              let sourceCost0 : ℝ :=
                ((∫ ζ,
                    (z * |D1 ζ| + z ^ 2 * studentizerClipBudget n r 512 rho 1 ζ) *
                      Real.exp (∑ j : Fin n, (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P) +
                  ∑ i : Fin n, ∫ ζ,
                    (min |z * ξ0 i ζ| 1 *
                      (|(|D1 ζ|) - (|residualStatisticDDeleted n r ζ i|)| +
                        z * |studentizerClipBudget n r 512 rho 1 ζ -
                          studentizerClipBudgetDeleted n r 512 rho 1 ζ i|)) *
                      Real.exp (∑ j ∈ Finset.univ.erase i,
                        (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P) /
                  (∫ ζ, Real.exp (∑ j : Fin n,
                    (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P)
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
              (∀ (C1 C2 C3 C4 : ℝ)
                  (hSZcBudget : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
                    cBudget C1 C2 C3 C4)
                  (hzMomentWindow : β = 0 ∨
                    (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                      Real.rpow (n : ℝ) ((p - 2) / (2 * p)))),
                Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                      (1 - C2 * sourceCost0) - payment ≤
                  P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
                P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ≤
                  Shao.standardNormalTail z * Real.exp (C3 * L0) *
                      (1 + C4 * sourceCost0) + 3 * payment) ∧
              Filter.limsup (fun k : ℕ => ν.real (E k))
                Filter.atTop ≤ payment) :=
      (Classical.choose_spec hCg).2
  let m₀ : MeasurableSpace Ω := Classical.choose hModel
  have hm₀ :
      m₀ ≤ mΩ :=
      Classical.choose (Classical.choose_spec hModel)
  have hcg :
      @MeasurableSpace.CountablyGenerated Ω m₀ :=
      Classical.choose (Classical.choose_spec (Classical.choose_spec hModel))
  let μ₀ : @Measure Ω m₀ := μ.trim hm₀
  letI : MeasurableSpace Ω := m₀
  letI : MeasurableSpace.CountablyGenerated Ω := hcg
  have hRetained247 :
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
        let deletedTestUnperturbedη : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x =>
          min |z * η k i x| 1 * (|Anew k x - Adelete i x| + z * |B x - Bdelete i x|)
        let unperturbedSourceCostη : ℕ → ℝ := fun k =>
          ((∫ x, fullTestη k x * Real.exp (Sη k x) ∂ν) +
            ∑ i : Fin n, ∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) / Iη k
        (∀ i : Fin n, Measurable[mAugLocal, borel ℝ] (ξlocal i)) ∧
        (∀ (k : ℕ) (i : Fin n),
          Measurable[mAugLocal, borel ℝ] (ηlocal k i) ∧
          MeasurableSpace.comap (ηlocal k i) (borel ℝ) = mAugLocal) ∧
        (∀ k : ℕ,
          Measurable[mAug, borel (Fin n → ℝ)] (C k) ∧
          MeasurableSpace.comap (C k) (borel (Fin n → ℝ)) = mAug ∧
          ∀ (f : (Fin n → Ω × ℝ) → ℝ), Measurable[mAug, borel ℝ] f →
            ∃ F : (Fin n → ℝ) → ℝ,
              Measurable[borel (Fin n → ℝ), borel ℝ] F ∧
              ∀ x : Fin n → Ω × ℝ, f x = F (C k x)) ∧
        (∀ (k : ℕ) (i : Fin n),
          let J : Type := {j : Fin n // j ≠ i}
          let mDel : MeasurableSpace (J → Ω × ℝ) :=
            @MeasurableSpace.pi J (fun _ : J => Ω × ℝ) (fun _ : J => mAugLocal)
          let Cdel : (J → Ω × ℝ) → (J → ℝ) :=
            fun y j => ηlocal k j.val (y j)
          let pX : (Fin n → Ω × ℝ) → (J → Ω × ℝ) := fun x j => x j.val
          let pR : (Fin n → ℝ) → (J → ℝ) := fun t j => t j.val
          Measurable[mAug, mDel] pX ∧
          Measurable[borel (Fin n → ℝ), borel (J → ℝ)] pR ∧
          Measurable[mDel, borel (J → ℝ)] Cdel ∧
          MeasurableSpace.comap Cdel (borel (J → ℝ)) = mDel ∧
          (∀ x : Fin n → Ω × ℝ, pR (C k x) = Cdel (pX x)) ∧
          MeasurableSpace.comap (fun x : Fin n → Ω × ℝ => pR (C k x))
              (borel (J → ℝ)) = MeasurableSpace.comap pX mDel ∧
          ∀ (d : (J → Ω × ℝ) → ℝ), Measurable[mDel, borel ℝ] d →
            ∃ F : (J → ℝ) → ℝ,
              Measurable[borel (J → ℝ), borel ℝ] F ∧
              (∀ y : J → Ω × ℝ, d y = F (Cdel y)) ∧
              Measurable[borel (Fin n → ℝ), borel ℝ] (fun t => F (pR t)) ∧
              ∀ x : Fin n → Ω × ℝ, d (pX x) = F (pR (C k x))) ∧
        (∀ (k : ℕ) (i : Fin n),
          ∃ FAdelete FBdelete : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
            Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] FAdelete ∧
            Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] FBdelete ∧
            ∀ x : Fin n → Ω × ℝ,
              Adelete i x = FAdelete (fun j : {j : Fin n // j ≠ i} => η k j.val x) ∧
              Bdelete i x = FBdelete (fun j : {j : Fin n // j ≠ i} => η k j.val x)) ∧
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
        (∀ (k : ℕ) (x : Fin n → Ω × ℝ),
          A x + (4 * ε k * Real.sqrt (n : ℝ)) * H x = Anew k x) ∧
        (∀ (k : ℕ) (i : Fin n),
          Measurable[mAug, borel ℝ] (fun x =>
            deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
              deletedTestη k i x * Real.exp (Sηminus k i x)) ∧
          Integrable[mAug] (fun x =>
            deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
              deletedTestη k i x * Real.exp (Sηminus k i x)) ν ∧
          Integrable[mAug] (fun x =>
            |deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
              deletedTestη k i x * Real.exp (Sηminus k i x)|) ν ∧
          Integrable[mAug] (fun x =>
            deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x)) ν ∧
          (∫ x, |deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
            deletedTestη k i x * Real.exp (Sηminus k i x)| ∂ν) ≤
              |ε k| * (Real.exp ((n : ℝ) / 2) * (K * (∫ x, Hdelete i x ∂ν))) ∧
          |(∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) -
            (∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν)| ≤
              |ε k| * (Real.exp ((n : ℝ) / 2) * (K * (∫ x, Hdelete i x ∂ν)))) ∧
        (∀ i : Fin n,
          Filter.Tendsto (fun k : ℕ =>
            ∫ x, |deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) -
              deletedTestη k i x * Real.exp (Sηminus k i x)| ∂ν)
            Filter.atTop (nhds (0 : ℝ)) ∧
          Filter.Tendsto (fun k : ℕ =>
            (∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) -
              (∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν))
            Filter.atTop (nhds (0 : ℝ)) ∧
          Filter.Tendsto (fun k : ℕ =>
            ∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν)
            Filter.atTop (nhds (∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P)) ∧
          Filter.Tendsto (fun k : ℕ =>
            (∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) / Iη k)
            Filter.atTop (nhds ((∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P) / I0))) ∧
        (∀ k : ℕ,
          |(∑ i : Fin n, ∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) -
            (∑ i : Fin n, ∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν)| ≤
              |ε k| * ∑ i : Fin n,
                Real.exp ((n : ℝ) / 2) * (K * (∫ x, Hdelete i x ∂ν))) ∧
        Filter.Tendsto (fun k : ℕ =>
          (∑ i : Fin n, ∫ x, deletedTestUnperturbedη k i x * Real.exp (Sηminus k i x) ∂ν) -
            (∑ i : Fin n, ∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν))
          Filter.atTop (nhds (0 : ℝ)) ∧
        Filter.Tendsto (fun k : ℕ => unperturbedSourceCostη k - sourceCostη k)
          Filter.atTop (nhds (0 : ℝ)) ∧
        Filter.Tendsto unperturbedSourceCostη Filter.atTop (nhds sourceCost0) ∧
        (∀ (cSZ C1 C2 C3 C4 : ℝ)
            (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
              cSZ C1 C2 C3 C4)
            (k : ℕ) (hz1 : 1 ≤ z)
            (hδη : ∀ i : Fin n, δη k i ≤ 1)
            (hLη : Lη k ≤ cSZ * z ^ 2),
          Shao.standardNormalTail z * Real.exp (-C1 * Lη k) *
              (1 - C2 * unperturbedSourceCostη k) ≤
            ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} ∧
          ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} ≤
            Shao.standardNormalTail z * Real.exp (C3 * Lη k) *
                (1 + C4 * unperturbedSourceCostη k) +
              ν.real {x : Fin n → Ω × ℝ | z * |Dη k x| > Vη k x / 4} +
              ν.real {x : Fin n → Ω × ℝ |
                z ^ 2 * |D2 (q x)| > (1 / 4 : ℝ)}) ∧
        (∀ (C1 C2 C3 C4 : ℝ)
            (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
              cBudget C1 C2 C3 C4)
            (hz1 : 1 ≤ z)
            (hzWindow : β = 0 ∨
              (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                Real.rpow (n : ℝ) ((p - 2) / (2 * p))))
            (τ : ℝ) (hτ : 0 < τ),
          ∃ k0 : ℕ, ∀ (k : ℕ), k0 ≤ k →
            (∀ i : Fin n, δη k i ≤ 1) ∧
            Lη k ≤ cBudget * z ^ 2 ∧
            |unperturbedSourceCostη k - sourceCost0| < τ ∧
            Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                (1 - C2 * sourceCost0) - τ ≤
              ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} ∧
            ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} ≤
              Shao.standardNormalTail z * Real.exp (C3 * L0) *
                  (1 + C4 * sourceCost0) +
                ν.real {x : Fin n → Ω × ℝ | z * |Dη k x| > Vη k x / 4} +
                ν.real {x : Fin n → Ω × ℝ |
                  z ^ 2 * |D2 (q x)| > (1 / 4 : ℝ)} + τ) ∧
        @MeasurableSet (Fin n → Ω) mN₀
          {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
        @MeasurableSet (Fin n → Ω) mN
          {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
        @MeasurableSet (Fin n → Ω × ℝ) mAug
          {x : Fin n → Ω × ℝ | z ≤ T0 (q x)} ∧
        @MeasurableSet (Fin n → Ω) mN₀
          {ζ : Fin n → Ω | projectionV n g ζ = 0} ∧
        @MeasurableSet (Fin n → Ω) mN
          {ζ : Fin n → Ω | projectionV n g ζ = 0} ∧
        @MeasurableSet (Fin n → Ω × ℝ) mAug
          {x : Fin n → Ω × ℝ | V x = 0} ∧
        ν.real {x : Fin n → Ω × ℝ | z ≤ T0 (q x)} =
          P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
        ν.real {x : Fin n → Ω × ℝ | V x = 0} =
          P.real {ζ : Fin n → Ω | projectionV n g ζ = 0} ∧
        (∀ k : ℕ,
          @MeasurableSet (Fin n → Ω × ℝ) mAug
            {x : Fin n → Ω × ℝ | z ≤ Tη k x} ∧
          ν ({x : Fin n → Ω × ℝ | z ≤ Tη k x} ∆
            {x : Fin n → Ω × ℝ | z ≤ T0 (q x)}) ≤
              ν {x : Fin n → Ω × ℝ | V x = 0} ∧
          |ν.real {x : Fin n → Ω × ℝ | z ≤ Tη k x} -
            P.real {ζ : Fin n → Ω | z ≤ T0 ζ}| ≤
              P.real {ζ : Fin n → Ω | projectionV n g ζ = 0}) ∧
        (∀ (C1 C2 C3 C4 : ℝ)
            (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
              cBudget C1 C2 C3 C4)
            (hz1 : 1 ≤ z)
            (hzWindow : β = 0 ∨
              (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                Real.rpow (n : ℝ) ((p - 2) / (2 * p)))),
          Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                (1 - C2 * sourceCost0) -
            P.real {ζ : Fin n → Ω | projectionV n g ζ = 0} ≤
            P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
          ∀ (τ : ℝ) (hτ : 0 < τ),
            ∃ k0 : ℕ, ∀ (k : ℕ), k0 ≤ k →
              (∀ i : Fin n, δη k i ≤ 1) ∧
              Lη k ≤ cBudget * z ^ 2 ∧
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
              |compactCostη k - compactCost0| < τ ∧
              |unperturbedSourceCostη k - sourceCost0| < τ ∧
              Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                              (1 - C2 * sourceCost0) - τ -
                            P.real {ζ : Fin n → Ω | projectionV n g ζ = 0} ≤
                            P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
              P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ≤
                            Shao.standardNormalTail z * Real.exp (C3 * L0) *
                                (1 + C4 * sourceCost0) +
                              ν.real {x : Fin n → Ω × ℝ | z * |Dη k x| > Vη k x / 4} +
                              ν.real {x : Fin n → Ω × ℝ |
                                z ^ 2 * |D2 (q x)| > (1 / 4 : ℝ)} +
                              P.real {ζ : Fin n → Ω | projectionV n g ζ = 0} + τ) ∧
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
        let T0 : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho 1
        let L0 : ℝ := ∑ i : Fin n,
          ∫ ζ, (z * ξ0 i ζ) ^ 2 * min |z * ξ0 i ζ| 1 ∂P
        let sourceCost0 : ℝ :=
          ((∫ ζ,
              (z * |D1 ζ| + z ^ 2 * studentizerClipBudget n r 512 rho 1 ζ) *
                Real.exp (∑ j : Fin n, (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P) +
            ∑ i : Fin n, ∫ ζ,
              (min |z * ξ0 i ζ| 1 *
                (|(|D1 ζ|) - (|residualStatisticDDeleted n r ζ i|)| +
                  z * |studentizerClipBudget n r 512 rho 1 ζ -
                    studentizerClipBudgetDeleted n r 512 rho 1 ζ i|)) *
                Real.exp (∑ j ∈ Finset.univ.erase i,
                  (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P) /
            (∫ ζ, Real.exp (∑ j : Fin n,
              (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P)
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
        (∀ (C1 C2 C3 C4 : ℝ)
            (hSZcBudget : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
              cBudget C1 C2 C3 C4)
            (hzMomentWindow : β = 0 ∨
              (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                Real.rpow (n : ℝ) ((p - 2) / (2 * p)))),
          Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                (1 - C2 * sourceCost0) - payment ≤
            P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
          P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ≤
            Shao.standardNormalTail z * Real.exp (C3 * L0) *
                (1 + C4 * sourceCost0) + 3 * payment) ∧
        Filter.limsup (fun k : ℕ => ν.real (E k))
          Filter.atTop ≤ payment) :=
      Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hModel))
  have hμ₀Probability :
      IsProbabilityMeasure μ₀ :=
      hRetained247.1
  have hPaymentAll247 :
      ∀ (Cenv aenv t0 Menv : ℝ)
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
              let T0 : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho 1
              let L0 : ℝ := ∑ i : Fin n,
                ∫ ζ, (z * ξ0 i ζ) ^ 2 * min |z * ξ0 i ζ| 1 ∂P
              let sourceCost0 : ℝ :=
                ((∫ ζ,
                    (z * |D1 ζ| + z ^ 2 * studentizerClipBudget n r 512 rho 1 ζ) *
                      Real.exp (∑ j : Fin n, (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P) +
                  ∑ i : Fin n, ∫ ζ,
                    (min |z * ξ0 i ζ| 1 *
                      (|(|D1 ζ|) - (|residualStatisticDDeleted n r ζ i|)| +
                        z * |studentizerClipBudget n r 512 rho 1 ζ -
                          studentizerClipBudgetDeleted n r 512 rho 1 ζ i|)) *
                      Real.exp (∑ j ∈ Finset.univ.erase i,
                        (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P) /
                  (∫ ζ, Real.exp (∑ j : Fin n,
                    (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P)
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
              (∀ (C1 C2 C3 C4 : ℝ)
                  (hSZcBudget : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
                    cBudget C1 C2 C3 C4)
                  (hzMomentWindow : β = 0 ∨
                    (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                      Real.rpow (n : ℝ) ((p - 2) / (2 * p)))),
                Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                      (1 - C2 * sourceCost0) - payment ≤
                  P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
                P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ≤
                  Shao.standardNormalTail z * Real.exp (C3 * L0) *
                      (1 + C4 * sourceCost0) + 3 * payment) ∧
              Filter.limsup (fun k : ℕ => ν.real (E k))
                Filter.atTop ≤ payment :=
      hRetained247.2.2
  refine ⟨h247.1, h247.2.1, h247.2.2.1, h247.2.2.2.1, h247.2.2.2.2.1, h247.2.2.2.2.2.1,
    cg, hcgpos, m₀, hm₀, hcg, hμ₀Probability, hRetained247.2.1, ?_⟩
  intro Cenv aenv t0 Menv hCenv haenv ht0 hMenv
  refine Filter.Eventually.mono
    (hPaymentAll247 Cenv aenv t0 Menv hCenv haenv ht0 hMenv)
    (fun (n : ℕ) (hAllAtN247 : 4 ≤ n ∧
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
        let T0 : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho 1
        let L0 : ℝ := ∑ i : Fin n,
          ∫ ζ, (z * ξ0 i ζ) ^ 2 * min |z * ξ0 i ζ| 1 ∂P
        let sourceCost0 : ℝ :=
          ((∫ ζ,
              (z * |D1 ζ| + z ^ 2 * studentizerClipBudget n r 512 rho 1 ζ) *
                Real.exp (∑ j : Fin n, (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P) +
            ∑ i : Fin n, ∫ ζ,
              (min |z * ξ0 i ζ| 1 *
                (|(|D1 ζ|) - (|residualStatisticDDeleted n r ζ i|)| +
                  z * |studentizerClipBudget n r 512 rho 1 ζ -
                    studentizerClipBudgetDeleted n r 512 rho 1 ζ i|)) *
                Real.exp (∑ j ∈ Finset.univ.erase i,
                  (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P) /
            (∫ ζ, Real.exp (∑ j : Fin n,
              (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P)
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
        (∀ (C1 C2 C3 C4 : ℝ)
            (hSZcBudget : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
              cBudget C1 C2 C3 C4)
            (hzMomentWindow : β = 0 ∨
              (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                Real.rpow (n : ℝ) ((p - 2) / (2 * p)))),
          Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                (1 - C2 * sourceCost0) - payment ≤
            P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
          P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ≤
            Shao.standardNormalTail z * Real.exp (C3 * L0) *
                (1 + C4 * sourceCost0) + 3 * payment) ∧
        Filter.limsup (fun k : ℕ => ν.real (E k))
          Filter.atTop ≤ payment) => ?_)
  have hn : 4 ≤ n := hAllAtN247.1
  have hPaymentAtN247 :
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
      let T0 : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho 1
      let L0 : ℝ := ∑ i : Fin n,
        ∫ ζ, (z * ξ0 i ζ) ^ 2 * min |z * ξ0 i ζ| 1 ∂P
      let sourceCost0 : ℝ :=
        ((∫ ζ,
            (z * |D1 ζ| + z ^ 2 * studentizerClipBudget n r 512 rho 1 ζ) *
              Real.exp (∑ j : Fin n, (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P) +
          ∑ i : Fin n, ∫ ζ,
            (min |z * ξ0 i ζ| 1 *
              (|(|D1 ζ|) - (|residualStatisticDDeleted n r ζ i|)| +
                z * |studentizerClipBudget n r 512 rho 1 ζ -
                  studentizerClipBudgetDeleted n r 512 rho 1 ζ i|)) *
              Real.exp (∑ j ∈ Finset.univ.erase i,
                (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P) /
          (∫ ζ, Real.exp (∑ j : Fin n,
            (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P)
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
      (∀ (C1 C2 C3 C4 : ℝ)
          (hSZcBudget : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
            cBudget C1 C2 C3 C4)
          (hzMomentWindow : β = 0 ∨
            (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
              Real.rpow (n : ℝ) ((p - 2) / (2 * p)))),
        Shao.standardNormalTail z * Real.exp (-C1 * L0) *
              (1 - C2 * sourceCost0) - payment ≤
          P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
        P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ≤
          Shao.standardNormalTail z * Real.exp (C3 * L0) *
              (1 + C4 * sourceCost0) + 3 * payment) ∧
      Filter.limsup (fun k : ℕ => ν.real (E k))
        Filter.atTop ≤ payment :=
      hAllAtN247.2
  refine ⟨hn, ?_⟩
  intro w hW hWR hSq hSqBound hEnv z hz hzWindow
  intro mN mN₀ P P₀ N ε ξ0 D1 D2 lambda01 mAugLocal mAug νlocal ν q c ξlocal Ylocal ξ Y a s ηlocal η C W V Wη Vη b Qε Dη V0 qOrder Ktail Gsource C2source Hsource Ssafe Jsafe E E2 Z payment T0 L0 sourceCost0
  have hAtCurrent247 :
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
      let T0 : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho 1
      let L0 : ℝ := ∑ i : Fin n,
        ∫ ζ, (z * ξ0 i ζ) ^ 2 * min |z * ξ0 i ζ| 1 ∂P
      let sourceCost0 : ℝ :=
        ((∫ ζ,
            (z * |D1 ζ| + z ^ 2 * studentizerClipBudget n r 512 rho 1 ζ) *
              Real.exp (∑ j : Fin n, (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P) +
          ∑ i : Fin n, ∫ ζ,
            (min |z * ξ0 i ζ| 1 *
              (|(|D1 ζ|) - (|residualStatisticDDeleted n r ζ i|)| +
                z * |studentizerClipBudget n r 512 rho 1 ζ -
                  studentizerClipBudgetDeleted n r 512 rho 1 ζ i|)) *
              Real.exp (∑ j ∈ Finset.univ.erase i,
                (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P) /
          (∫ ζ, Real.exp (∑ j : Fin n,
            (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)) ∂P)
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
      (∀ (C1 C2 C3 C4 : ℝ)
          (hSZcBudget : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
            cBudget C1 C2 C3 C4)
          (hzMomentWindow : β = 0 ∨
            (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
              Real.rpow (n : ℝ) ((p - 2) / (2 * p)))),
        Shao.standardNormalTail z * Real.exp (-C1 * L0) *
              (1 - C2 * sourceCost0) - payment ≤
          P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
        P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ≤
          Shao.standardNormalTail z * Real.exp (C3 * L0) *
              (1 + C4 * sourceCost0) + 3 * payment) ∧
      Filter.limsup (fun k : ℕ => ν.real (E k))
        Filter.atTop ≤ payment :=
    hPaymentAtN247 w hW hWR hSq hSqBound hEnv z hz hzWindow
  have hClippedCurrentBounds :
      (∀ (C1 C2 C3 C4 : ℝ)
                  (hSZcBudget : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
                    cBudget C1 C2 C3 C4)
                  (hzMomentWindow : β = 0 ∨
                    (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                      Real.rpow (n : ℝ) ((p - 2) / (2 * p)))),
                Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                      (1 - C2 * sourceCost0) - payment ≤
                  P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ∧
                P.real {ζ : Fin n → Ω | z ≤ T0 ζ} ≤
                  Shao.standardNormalTail z * Real.exp (C3 * L0) *
                      (1 + C4 * sourceCost0) + 3 * payment) :=
      hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hNewPhysicalWhole :
      (
                let Tphysical : (Fin n → Ω) → ℝ := fun ζ : Fin n → Ω =>
                  if Real.sqrt (centeredSq n g r ζ) = 0 then 0 else
                    (projectionW n g ζ + residualStatisticD n r ζ) /
                      Real.sqrt (centeredSq n g r ζ)
                let H1source : Set (Fin n → Ω) := projectionGood n g 1 ∩ C2source
                let payment1 : ℝ := (3 : ℝ) * Real.exp (-qOrder) + Real.exp (-cg * (n : ℝ)) +
                    (4 : ℝ) * Real.exp (-Real.sqrt (n : ℝ) / (2 : ℝ))
                let Ephysical : Set (Fin n → Ω) := {ζ : Fin n → Ω | T0 ζ ≠ Tphysical ζ}
                (1 : ℝ) ≤ remainderWindowScale Ktail t0 *
                  Real.rpow (n : ℝ) (1 / 6 : ℝ) ∧
                @MeasurableSet (Fin n → Ω) mN H1source ∧
                P.real H1sourceᶜ ≤ payment1 ∧
                Measurable[mN, borel ℝ] Tphysical ∧
                Measurable[mN, borel ℝ] T0 ∧
                @MeasurableSet (Fin n → Ω) mN Ephysical ∧
                (∀ ζ : Fin n → Ω, ζ ∈ H1source →
                  0 < projectionV n g ζ ∧
                  |centeredDelta n g r ζ| ≤ (1 / 32 : ℝ) ∧
                  -(1 / 2 : ℝ) ≤ centeredDelta n g r ζ) ∧
                (1 + rho ≤ Real.sqrt (n : ℝ) →
                  (∀ ζ : Fin n → Ω, ζ ∈ H1source →
                    D2 ζ = centeredDelta n g r ζ ∧
                    0 < V0 ζ * Real.sqrt (1 + D2 ζ) ∧
                    0 < Real.sqrt (centeredSq n g r ζ) ∧
                    V0 ζ * Real.sqrt (1 + D2 ζ) =
                      Real.sqrt (centeredSq n g r ζ) ∧
                    T0 ζ = Tphysical ζ) ∧
                  Ephysical ⊆ H1sourceᶜ ∧
                  P.real Ephysical ≤ P.real H1sourceᶜ ∧
                  P.real Ephysical ≤ payment1 ∧
                  (∀ t : ℝ,
                    @MeasurableSet (Fin n → Ω) mN
                      {ζ : Fin n → Ω | t ≤ Tphysical ζ} ∧
                    @MeasurableSet (Fin n → Ω) mN
                      {ζ : Fin n → Ω | t ≤ T0 ζ} ∧
                    @MeasurableSet (Fin n → Ω) mN
                      {ζ : Fin n → Ω | Tphysical ζ ≤ t} ∧
                    @MeasurableSet (Fin n → Ω) mN
                      {ζ : Fin n → Ω | T0 ζ ≤ t} ∧
                    ({ζ : Fin n → Ω | t ≤ Tphysical ζ} ∆
                      {ζ : Fin n → Ω | t ≤ T0 ζ}) ⊆ Ephysical ∧
                    ({ζ : Fin n → Ω | Tphysical ζ ≤ t} ∆
                      {ζ : Fin n → Ω | T0 ζ ≤ t}) ⊆ Ephysical ∧
                    |P.real {ζ : Fin n → Ω | t ≤ Tphysical ζ} -
                      P.real {ζ : Fin n → Ω | t ≤ T0 ζ}| ≤ P.real Ephysical ∧
                    |P.real {ζ : Fin n → Ω | Tphysical ζ ≤ t} -
                      P.real {ζ : Fin n → Ω | T0 ζ ≤ t}| ≤ P.real Ephysical ∧
                    |P.real {ζ : Fin n → Ω | t ≤ Tphysical ζ} -
                      P.real {ζ : Fin n → Ω | t ≤ T0 ζ}| ≤ payment1 ∧
                    |P.real {ζ : Fin n → Ω | Tphysical ζ ≤ t} -
                      P.real {ζ : Fin n → Ω | T0 ζ ≤ t}| ≤ payment1) ∧
                  (∀ (C1 C2 C3 C4 : ℝ)
                      (hSZcBudget : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
                        cBudget C1 C2 C3 C4)
                      (hzMomentWindow : β = 0 ∨
                        (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                          Real.rpow (n : ℝ) ((p - 2) / (2 * p)))),
                    Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                          (1 - C2 * sourceCost0) - payment - payment1 ≤
                      P.real {ζ : Fin n → Ω | z ≤ Tphysical ζ} ∧
                    P.real {ζ : Fin n → Ω | z ≤ Tphysical ζ} ≤
                      Shao.standardNormalTail z * Real.exp (C3 * L0) *
                          (1 + C4 * sourceCost0) + 3 * payment + payment1))) :=
      by
        intro Tphysical H1source payment1 Ephysical
        -- The following block uses the original sample sigma algebra and original P.
        letI : MeasurableSpace (Fin n → Ω) := mN
        letI : @IsProbabilityMeasure (Fin n → Ω) mN P :=
          (inferInstance : @IsProbabilityMeasure (Fin n → Ω) mN P)
        have hWindowOne :
            (1 : ℝ) ≤ remainderWindowScale Ktail t0 * Real.rpow (n : ℝ) (1 / 6 : ℝ) :=
            hz.trans hzWindow
        have hWindowOnePublic :
            (1 : ℝ) ≤ remainderWindowScale Ktail t0 *
                        Real.rpow (n : ℝ) (1 / 6 : ℝ) :=
            hWindowOne
        have hKtailNonneg :
            0 ≤ Ktail :=
            by
              dsimp only [Ktail, Shao.OQ6.BoundedProductEnvelopeTails.tailScale,
                Shao.OQ6.BoundedProductEnvelopeTails.squareTailScale]
              exact le_trans
                (mul_nonneg (le_of_lt (Real.exp_pos 1))
                  (show 0 ≤ Menv + 1 by linarith only [hMenv]))
                (le_max_left _ _)
        have hAtOne247 :
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
              fun k x => W x - Wη k x + (1 : ℝ) * b x * (Vη k x - V x)
            let Dη : ℕ → (Fin n → Ω × ℝ) → ℝ :=
              fun k x => D1 (q x) + W x - Wη k x + (1 : ℝ) * b x * (Vη k x - V x)
            let V0 : (Fin n → Ω) → ℝ := projectionV n g
            let qOrder : ℝ := boundedPolylogMomentOrder t0 n
            let Ktail : ℝ := Shao.OQ6.BoundedProductEnvelopeTails.tailScale Menv
            let Gsource : Set (Fin n → Ω) := projectionGood n g (1 : ℝ)
            let C2source : Set (Fin n → Ω) :=
              {ζ : Fin n → Ω |
                |Shao.OQ6.CanonicalDoubleGhostScalarMoments.originalUpper n r ζ| ≤
                  Ktail * (n : ℝ) * qOrder ∧
                ‖Shao.OQ6.CanonicalDoubleGhostRowMoments.originalRows n r ζ‖ ^ (2 : ℕ) ≤
                  Ktail * (n : ℝ) ^ (2 : ℕ) * qOrder}
            let Hsource : Set (Fin n → Ω) := Gsource ∩ C2source
            let Ssafe : Set (Fin n → Ω) :=
              {ζ : Fin n → Ω |
                0 < V0 ζ ∧ (1 : ℝ) * |D1 ζ| ≤ V0 ζ / 8 ∧
                  (1 : ℝ) ^ (2 : ℕ) * |D2 ζ| ≤ (1 / 8 : ℝ)}
            let Jsafe : Set (Fin n → Ω × ℝ) := q ⁻¹' Ssafe
            let E : ℕ → Set (Fin n → Ω × ℝ) := fun k =>
              {x : Fin n → Ω × ℝ | (1 : ℝ) * |Dη k x| > Vη k x / 4}
            let E2 : Set (Fin n → Ω × ℝ) :=
              {x : Fin n → Ω × ℝ |
                (1 : ℝ) ^ (2 : ℕ) * |D2 (q x)| > (1 / 4 : ℝ)}
            let Z : Set (Fin n → Ω × ℝ) :=
              {x : Fin n → Ω × ℝ | V x = 0}
            let payment : ℝ :=
              (3 : ℝ) * Real.exp (-qOrder) + Real.exp (-cg * (n : ℝ)) +
                (4 : ℝ) * Real.exp (-((1 : ℝ) * Real.sqrt (n : ℝ)) / (2 : ℝ))
            let T0 : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho 1
            let L0 : ℝ := ∑ i : Fin n,
              ∫ ζ, ((1 : ℝ) * ξ0 i ζ) ^ 2 * min |(1 : ℝ) * ξ0 i ζ| 1 ∂P
            let sourceCost0 : ℝ :=
              ((∫ ζ,
                  ((1 : ℝ) * |D1 ζ| + (1 : ℝ) ^ 2 * studentizerClipBudget n r 512 rho 1 ζ) *
                    Real.exp (∑ j : Fin n, ((1 : ℝ) * ξ0 j ζ - ((1 : ℝ) * ξ0 j ζ) ^ 2 / 2)) ∂P) +
                ∑ i : Fin n, ∫ ζ,
                  (min |(1 : ℝ) * ξ0 i ζ| 1 *
                    (|(|D1 ζ|) - (|residualStatisticDDeleted n r ζ i|)| +
                      (1 : ℝ) * |studentizerClipBudget n r 512 rho 1 ζ -
                        studentizerClipBudgetDeleted n r 512 rho 1 ζ i|)) *
                    Real.exp (∑ j ∈ Finset.univ.erase i,
                      ((1 : ℝ) * ξ0 j ζ - ((1 : ℝ) * ξ0 j ζ) ^ 2 / 2)) ∂P) /
                (∫ ζ, Real.exp (∑ j : Fin n,
                  ((1 : ℝ) * ξ0 j ζ - ((1 : ℝ) * ξ0 j ζ) ^ 2 / 2)) ∂P)
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
              0 < V x ∧ (1 : ℝ) * |D1 (q x)| ≤ V x / 8 ∧
                (1 : ℝ) ^ (2 : ℕ) * |D2 (q x)| ≤ (1 / 8 : ℝ)) ∧
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
                0 < Vη k x ∧ (1 : ℝ) * |Dη k x| ≤ Vη k x / 4) ∧
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
            (∀ (C1 C2 C3 C4 : ℝ)
                (hSZcBudget : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
                  cBudget C1 C2 C3 C4)
                (hzMomentWindow : β = 0 ∨
                  (0 < β ∧ (1 : ℝ) ≤ cWindow * Real.rpow β (-1 / p) *
                    Real.rpow (n : ℝ) ((p - 2) / (2 * p)))),
              Shao.standardNormalTail (1 : ℝ) * Real.exp (-C1 * L0) *
                    (1 - C2 * sourceCost0) - payment ≤
                P.real {ζ : Fin n → Ω | (1 : ℝ) ≤ T0 ζ} ∧
              P.real {ζ : Fin n → Ω | (1 : ℝ) ≤ T0 ζ} ≤
                Shao.standardNormalTail (1 : ℝ) * Real.exp (C3 * L0) *
                    (1 + C4 * sourceCost0) + 3 * payment) ∧
            Filter.limsup (fun k : ℕ => ν.real (E k))
              Filter.atTop ≤ payment :=
            hPaymentAtN247 w hW hWR hSq hSqBound hEnv 1 (le_refl 1) hWindowOne
        have hH1Measurable :
            @MeasurableSet (Fin n → Ω) mN H1source :=
            hAtOne247.2.2.2.2.2.2.1
        have hH1Payment :
            P.real H1sourceᶜ ≤ payment1 :=
            by
              simpa only [one_mul] using hAtOne247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hMeas220 :
            let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
            let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
            let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω mΩ mΩ μ μ)
            let rho : ℝ := Real.sqrt v
            let N : ℝ := Real.sqrt (n : ℝ)
            let W : (Fin n → Ω) → ℝ := projectionW n g
            let V : (Fin n → Ω) → ℝ := projectionV n g
            let D : (Fin n → Ω) → ℝ := residualStatisticD n r
            let J : (Fin n → Ω) → ℝ := residualEnergyJ n r
            let Ddel : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
            let Jdel : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
            let A : (Fin n → Ω) → ℝ := fun ξ => |D ξ|
            let Adel : (Fin n → Ω) → Fin n → ℝ := fun ξ i => |Ddel ξ i|
            let B1 : (Fin n → Ω) → ℝ := studentizerClipBudget n r (512 : ℝ) rho 1
            let B1del : (Fin n → Ω) → Fin n → ℝ := studentizerClipBudgetDeleted n r (512 : ℝ) rho 1
            let s2 : (Fin n → Ω) → ℝ := centeredSq n g r
            let s : (Fin n → Ω) → ℝ := fun ξ => Real.sqrt (s2 ξ)
            let d : (Fin n → Ω) → ℝ := centeredDelta n g r
            let e : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r (512 : ℝ) rho 1
            let Tclip : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r (512 : ℝ) rho 1
            let Tactual : (Fin n → Ω) → ℝ := fun ξ => if s ξ = 0 then 0 else (W ξ + D ξ) / s ξ
            let cap : (Fin n → Ω) → Fin n → ℝ := fun ξ i => min (|g (ξ i)| / N) (1 / (1 + (0 : ℝ)))
            let deletedTest : (Fin n → Ω) → Fin n → ℝ := fun ξ i => cap ξ i * (|A ξ - Adel ξ i| + (0 : ℝ) * |B1 ξ - B1del ξ i|)
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
                      E (fun j : {j : Fin n // j ≠ i} => ξ j.val)) :=
            @Shao.OQ6.OriginalClippedStatisticMeasurable.actual_normalized_compact_clipped_observables
              Ω mΩ μ hμProbability h hh hh2 hhsymm hcenter hprojectionsecond
              n hn 0 (by norm_num) (by norm_num) 512 (by norm_num)
        have hPhysicalMeasurable :
            Measurable[mN, borel ℝ] Tphysical :=
            hMeas220.2.2.2.2.2.2.2.2.2.2.2.1
        have hClippedMeasurable :
            Measurable[mN, borel ℝ] T0 :=
            hMeas220.2.2.2.2.2.2.2.2.2.2.1
        have hDisagreementMeasurable :
            @MeasurableSet (Fin n → Ω) mN Ephysical :=
            (measurableSet_eq_fun hClippedMeasurable hPhysicalMeasurable).compl
        have hSmallOne :
            ∀ ζ : Fin n → Ω, ζ ∈ H1source →
              0 < projectionV n g ζ ∧
              (1 : ℝ) * |residualStatisticD n r ζ| / projectionV n g ζ ≤ (1 / 8 : ℝ) ∧
              (1 : ℝ) ^ (2 : ℕ) * |centeredDelta n g r ζ| ≤ (1 / 32 : ℝ) ∧
              |centeredDelta n g r ζ| ≤ (1 / 32 : ℝ) :=
            by
              intro ζ hζ
              exact bounded_remainder_small_window n g r ζ Ktail t0 1
                hrSymm hn hKtailNonneg ht0 (le_refl 1) hWindowOne
                hζ.2.1 hζ.2.2 hζ.1
        have hSmallAndLowerOne :
            (∀ ζ : Fin n → Ω, ζ ∈ H1source →
                        0 < projectionV n g ζ ∧
                        |centeredDelta n g r ζ| ≤ (1 / 32 : ℝ) ∧
                        -(1 / 2 : ℝ) ≤ centeredDelta n g r ζ) :=
            by
              intro ζ hζ
              refine ⟨(hSmallOne ζ hζ).1, (hSmallOne ζ hζ).2.2.2, ?_⟩
              linarith only [(abs_le.mp (hSmallOne ζ hζ).2.2.2).1]
        have hPhysicalFinite :
            ∀ s : Set (Fin n → Ω), P s ≠ (⊤ : ENNReal) :=
            fun s => measure_ne_top P s
        have hPhysicalGuardedPackage :
            (1 + rho ≤ Real.sqrt (n : ℝ) →
                        (∀ ζ : Fin n → Ω, ζ ∈ H1source →
                          D2 ζ = centeredDelta n g r ζ ∧
                          0 < V0 ζ * Real.sqrt (1 + D2 ζ) ∧
                          0 < Real.sqrt (centeredSq n g r ζ) ∧
                          V0 ζ * Real.sqrt (1 + D2 ζ) =
                            Real.sqrt (centeredSq n g r ζ) ∧
                          T0 ζ = Tphysical ζ) ∧
                        Ephysical ⊆ H1sourceᶜ ∧
                        P.real Ephysical ≤ P.real H1sourceᶜ ∧
                        P.real Ephysical ≤ payment1 ∧
                        (∀ t : ℝ,
                          @MeasurableSet (Fin n → Ω) mN
                            {ζ : Fin n → Ω | t ≤ Tphysical ζ} ∧
                          @MeasurableSet (Fin n → Ω) mN
                            {ζ : Fin n → Ω | t ≤ T0 ζ} ∧
                          @MeasurableSet (Fin n → Ω) mN
                            {ζ : Fin n → Ω | Tphysical ζ ≤ t} ∧
                          @MeasurableSet (Fin n → Ω) mN
                            {ζ : Fin n → Ω | T0 ζ ≤ t} ∧
                          ({ζ : Fin n → Ω | t ≤ Tphysical ζ} ∆
                            {ζ : Fin n → Ω | t ≤ T0 ζ}) ⊆ Ephysical ∧
                          ({ζ : Fin n → Ω | Tphysical ζ ≤ t} ∆
                            {ζ : Fin n → Ω | T0 ζ ≤ t}) ⊆ Ephysical ∧
                          |P.real {ζ : Fin n → Ω | t ≤ Tphysical ζ} -
                            P.real {ζ : Fin n → Ω | t ≤ T0 ζ}| ≤ P.real Ephysical ∧
                          |P.real {ζ : Fin n → Ω | Tphysical ζ ≤ t} -
                            P.real {ζ : Fin n → Ω | T0 ζ ≤ t}| ≤ P.real Ephysical ∧
                          |P.real {ζ : Fin n → Ω | t ≤ Tphysical ζ} -
                            P.real {ζ : Fin n → Ω | t ≤ T0 ζ}| ≤ payment1 ∧
                          |P.real {ζ : Fin n → Ω | Tphysical ζ ≤ t} -
                            P.real {ζ : Fin n → Ω | T0 ζ ≤ t}| ≤ payment1) ∧
                        (∀ (C1 C2 C3 C4 : ℝ)
                            (hSZcBudget : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
                              cBudget C1 C2 C3 C4)
                            (hzMomentWindow : β = 0 ∨
                              (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
                                Real.rpow (n : ℝ) ((p - 2) / (2 * p)))),
                          Shao.standardNormalTail z * Real.exp (-C1 * L0) *
                                (1 - C2 * sourceCost0) - payment - payment1 ≤
                            P.real {ζ : Fin n → Ω | z ≤ Tphysical ζ} ∧
                          P.real {ζ : Fin n → Ω | z ≤ Tphysical ζ} ≤
                            Shao.standardNormalTail z * Real.exp (C3 * L0) *
                                (1 + C4 * sourceCost0) + 3 * payment + payment1)) :=
            by
              intro hStudentizerWindow
              have hLiteralComparison :
                  ∀ ζ : Fin n → Ω, ζ ∈ H1source →
                    clippedCenteredDelta n g r 512 rho 1 ζ = centeredDelta n g r ζ ∧
                    0 < projectionV n g ζ * Real.sqrt (1 + clippedCenteredDelta n g r 512 rho 1 ζ) ∧
                    0 < Real.sqrt (centeredSq n g r ζ) ∧
                    projectionV n g ζ * Real.sqrt (1 + clippedCenteredDelta n g r 512 rho 1 ζ) = Real.sqrt (centeredSq n g r ζ) ∧
                    clippedCenteredStatistic n g r 512 rho 1 ζ = (if Real.sqrt (centeredSq n g r ζ) = 0 then 0 else (projectionW n g ζ + residualStatisticD n r ζ) / Real.sqrt (centeredSq n g r ζ)) :=
                  by
                    intro ζ hζ
                    exact literal_clippedCentered_comparison_on_projectionGood n g r rho 1 ζ
                      hn (le_refl 1) hrSymm hRhoNonneg
                      (by simpa only [mul_one] using hStudentizerWindow) hζ.1
                      (hSmallAndLowerOne ζ hζ).2.2
              have hDisagreementSubset : Ephysical ⊆ H1sourceᶜ := by
                intro ζ hζ hGood
                exact hζ (hLiteralComparison ζ hGood).2.2.2.2
              have hDisagreementMono : P.real Ephysical ≤ P.real H1sourceᶜ :=
                measureReal_mono hDisagreementSubset (hPhysicalFinite H1sourceᶜ)
              have hDisagreementPayment : P.real Ephysical ≤ payment1 :=
                hDisagreementMono.trans hH1Payment
              have hClosedUpperDiff :
                  ∀ t : ℝ, ({ζ : Fin n → Ω | t ≤ Tphysical ζ} ∆ {ζ : Fin n → Ω | t ≤ T0 ζ}) ⊆ Ephysical :=
                  by
                    intro t ζ hζ hEq
                    rcases hζ with hζ | hζ
                    · exact hζ.2 (by simpa only [Set.mem_setOf_eq, hEq] using hζ.1)
                    · exact hζ.2 (by simpa only [Set.mem_setOf_eq, hEq] using hζ.1)
              have hClosedLowerDiff :
                  ∀ t : ℝ, ({ζ : Fin n → Ω | Tphysical ζ ≤ t} ∆ {ζ : Fin n → Ω | T0 ζ ≤ t}) ⊆ Ephysical :=
                  by
                    intro t ζ hζ hEq
                    rcases hζ with hζ | hζ
                    · exact hζ.2 (by simpa only [Set.mem_setOf_eq, hEq] using hζ.1)
                    · exact hζ.2 (by simpa only [Set.mem_setOf_eq, hEq] using hζ.1)
              have hUpperComparison : ∀ t : ℝ,
                  |P.real {ζ : Fin n → Ω | t ≤ Tphysical ζ} -
                    P.real {ζ : Fin n → Ω | t ≤ T0 ζ}| ≤ P.real Ephysical := by
                intro t
                exact (abs_measureReal_sub_le_measureReal_symmDiff (μ := P)
                  (hPhysicalMeasurable measurableSet_Ici).nullMeasurableSet
                  (hClippedMeasurable measurableSet_Ici).nullMeasurableSet).trans
                  (measureReal_mono (hClosedUpperDiff t) (hPhysicalFinite Ephysical))
              have hLowerComparison : ∀ t : ℝ,
                  |P.real {ζ : Fin n → Ω | Tphysical ζ ≤ t} -
                    P.real {ζ : Fin n → Ω | T0 ζ ≤ t}| ≤ P.real Ephysical := by
                intro t
                exact (abs_measureReal_sub_le_measureReal_symmDiff (μ := P)
                  (hPhysicalMeasurable measurableSet_Iic).nullMeasurableSet
                  (hClippedMeasurable measurableSet_Iic).nullMeasurableSet).trans
                  (measureReal_mono (hClosedLowerDiff t) (hPhysicalFinite Ephysical))
              refine ⟨hLiteralComparison, hDisagreementSubset, hDisagreementMono,
                hDisagreementPayment, ?_, ?_⟩
              · intro t
                exact ⟨hPhysicalMeasurable measurableSet_Ici,
                  hClippedMeasurable measurableSet_Ici,
                  hPhysicalMeasurable measurableSet_Iic,
                  hClippedMeasurable measurableSet_Iic,
                  hClosedUpperDiff t, hClosedLowerDiff t,
                  hUpperComparison t, hLowerComparison t,
                  (hUpperComparison t).trans hDisagreementPayment,
                  (hLowerComparison t).trans hDisagreementPayment⟩
              · intro C1 C2 C3 C4 hSZcBudget hzMomentWindow
                constructor
                · linarith only [
                    (hClippedCurrentBounds C1 C2 C3 C4 hSZcBudget hzMomentWindow).1,
                    (abs_le.mp ((hUpperComparison z).trans hDisagreementPayment)).1]
                · linarith only [
                    (hClippedCurrentBounds C1 C2 C3 C4 hSZcBudget hzMomentWindow).2,
                    (abs_le.mp ((hUpperComparison z).trans hDisagreementPayment)).2]
        exact ⟨hWindowOnePublic, hH1Measurable, hH1Payment,
          hPhysicalMeasurable, hClippedMeasurable, hDisagreementMeasurable,
          hSmallAndLowerOne, hPhysicalGuardedPackage⟩
  exact ⟨hAtCurrent247.1,
    hAtCurrent247.2.1,
    hAtCurrent247.2.2.1,
    hAtCurrent247.2.2.2.1,
    hAtCurrent247.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hAtCurrent247.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    hNewPhysicalWhole⟩

end

end Shao.OQ6.OriginalSameWitnessPhysicalPaidTailApplication
