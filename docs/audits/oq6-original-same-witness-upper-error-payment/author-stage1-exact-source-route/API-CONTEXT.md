# Exact public API source context

Copied declaration heads and ordinary values, without new proof bodies. No new review or machine qualification is claimed. Namespaces and imports are explicit. These signatures have not been elaborated anew.

## qualified232; namespace Shao.OQ6.NormalizedUpperErrorGoodsetPayment

{"path": "C:/game/shao lean/library/Shao/OQ6/NormalizedUpperErrorGoodsetPayment.lean", "sha256": "c95d036b852a66fb86fdef687cdff2ab4a0e6736b45cb015f8d57d3330f1ddf8", "bytes": 11214}

```lean
import Shao.OQ6.NormalizedRawNumeratorBuffer

theorem actual_normalized_upper_error_goodset_payment
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (hξ2 : ∀ i : Fin n, MemLp (ξ i) 2 ν)
    (hξmean : ∀ i : Fin n, (∫ ω, ξ i ω ∂ν) = 0)
    (hξenergy : (∑ i : Fin n, ∫ ω, (ξ i ω) ^ 2 ∂ν) = 1)
    (Y : ℕ → Fin n → Ω → ℝ)
    (hY : ∀ (k : ℕ) (i : Fin n), Measurable (Y k i))
    (ε : ℕ → ℝ) (hε : ∀ k : ℕ, 0 < ε k)
    (hεsmall : ∀ k : ℕ, ε k < 1 / (4 * Real.sqrt (n : ℝ)))
    (hεlim : Filter.Tendsto ε Filter.atTop (nhds (0 : ℝ)))
    (herr : ∀ (k : ℕ) (i : Fin n) (ω : Ω),
      |Y k i ω - ξ i ω| ≤ ε k)
    (D1 D2 : Ω → ℝ)
    (hD1 : Measurable D1) (hD2 : Measurable D2)
    (z : ℝ) (hz : 1 ≤ z)
    (H : Set Ω) (hH : MeasurableSet H)
    (hgood : ∀ ω : Ω, ω ∈ H →
      0 < Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2) ∧
      z * |D1 ω| ≤ Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2) / 8 ∧
      z ^ 2 * |D2 ω| ≤ (1 / 8 : ℝ)) :
    let η : ℕ → Fin n → Ω → ℝ := fun k =>
      Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
    let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
    let Wη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, η k i ω
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
    let Vη : ℕ → Ω → ℝ := fun k ω =>
      Real.sqrt (∑ i : Fin n, (η k i ω) ^ 2)
    let b : Ω → ℝ := fun ω => Real.sqrt (1 + D2 ω)
    let Q : ℕ → Ω → ℝ := fun k ω =>
      W ω - Wη k ω + z * b ω * (Vη k ω - V ω)
    let Dη : ℕ → Ω → ℝ := fun k ω => D1 ω + Q k ω
    let E : ℕ → Set Ω := fun k =>
      {ω : Ω | z * |Dη k ω| > Vη k ω / 4}
    let E2 : Set Ω := {ω : Ω | z ^ 2 * |D2 ω| > (1 / 4 : ℝ)}
    let Z : Set Ω := {ω : Ω | V ω = 0}
    (∀ (k : ℕ) (i : Fin n), Measurable (η k i)) ∧
    (∀ k : ℕ, Measurable (Q k) ∧ Measurable (Dη k) ∧
      MeasurableSet (E k)) ∧
    (MeasurableSet E2 ∧ MeasurableSet Z) ∧
    (∀ (i : Fin n) (ω : Ω),
      Filter.Tendsto (fun k : ℕ => η k i ω) Filter.atTop (nhds (ξ i ω))) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => Wη k ω)
      Filter.atTop (nhds (W ω))) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => Vη k ω)
      Filter.atTop (nhds (V ω))) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => Q k ω)
      Filter.atTop (nhds (0 : ℝ))) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => Dη k ω)
      Filter.atTop (nhds (D1 ω))) ∧
    (∀ ω : Ω, ω ∈ H → (7 / 8 : ℝ) ≤ 1 + D2 ω ∧ 0 < b ω) ∧
    (∀ ω : Ω, ω ∈ H → ∀ᶠ k : ℕ in Filter.atTop,
      0 < Vη k ω ∧ z * |Dη k ω| ≤ Vη k ω / 4) ∧
    E2 ⊆ Hᶜ ∧
    Z ⊆ Hᶜ ∧
    ν.real E2 ≤ ν.real Hᶜ ∧
    ν.real Z ≤ ν.real Hᶜ ∧
    (∀ δ : ℝ, 0 < δ → ∀ᶠ k : ℕ in Filter.atTop,
      ν.real (E k) ≤ ν.real Hᶜ + δ) ∧
    Filter.limsup (fun k : ℕ => ν.real (E k)) Filter.atTop ≤ ν.real Hᶜ
```

## qualified233; namespace Shao.OQ6.P54

{"path": "C:/game/shao lean/drafts/oq56/unit233/author-repair-01/P54ActualGoodsetFrontier.lean", "sha256": "8281cbb3a10297297d6e92fce7c258ad2d0c0ccd7406aae63aefd3194beccbab", "bytes": 14141}

```lean
import Shao.OQ5.P51.ClippedStudentizer
import Shao.OQ6.OriginalGoodEventBridge
import Mathlib.MeasureTheory.Measure.Real

theorem fixed_original_boundedPolylog_goodset_frontier
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgmean : (∫ o : Ω, g o ∂μ) = 0)
    (hgsecond : (∫ o : Ω, (g o) ^ (2 : ℕ) ∂μ) = 1) :
    ∃ cg : ℝ, 0 < cg ∧
      ∀ (C a t0 M : ℝ)
        (hC : 0 ≤ C) (ha : 0 ≤ a) (ht0 : 0 < t0) (hM : 0 ≤ M),
        ∀ᶠ n : ℕ in atTop,
          4 ≤ n ∧
          ∀ (r : Ω → Ω → ℝ) (w : Ω → ℝ)
            (hr : Measurable (Function.uncurry r))
            (hr1 : Integrable (Function.uncurry r) (μ.prod μ))
            (hcR : ∀ᵐ o : Ω ∂μ, (∫ o' : Ω, r o o' ∂μ) = 0)
            (hcL : ∀ᵐ o' : Ω ∂μ, (∫ o : Ω, r o o' ∂μ) = 0)
            (hW : ∀ᵐ o : Ω ∂μ, 0 ≤ w o)
            (hWR : ∀ᵐ o : Ω ∂μ, w o ≤ boundedPolylogHeight C a n)
            (hSq : Integrable (fun o : Ω => (w o) ^ (2 : ℕ)) μ)
            (hSqBound : (∫ o : Ω, (w o) ^ (2 : ℕ) ∂μ) ≤ M)
            (hEnv : ∀ᵐ p : Ω × Ω ∂μ.prod μ,
              |r p.1 p.2| ≤ w p.1 * w p.2)
            (hsym : ∀ o o' : Ω, r o o' = r o' o)
            (C0 rho z : ℝ) (hC0 : 0 ≤ C0) (hrho : 0 ≤ rho)
            (hz : (1 : ℝ) ≤ z)
            (hzWindow : z ≤ remainderWindowScale (tailScale M) t0 *
              Real.rpow (n : ℝ) (1 / 6 : ℝ)),
            let q : ℝ := boundedPolylogMomentOrder t0 n
            let K : ℝ := tailScale M
            let G : Set (Fin n → Ω) := projectionGood n g z
            let C2 : Set (Fin n → Ω) :=
              {x : Fin n → Ω |
                |originalUpper n r x| ≤ K * (n : ℝ) * q ∧
                ‖originalRows n r x‖ ^ (2 : ℕ) ≤
                  K * (n : ℝ) ^ (2 : ℕ) * q}
            let H : Set (Fin n → Ω) := G ∩ C2
            let e1 : (Fin n → Ω) → ℝ :=
              fun x : Fin n → Ω => clippedCenteredDelta n g r C0 rho 1 x
            MeasurableSet H ∧
              (∀ x : Fin n → Ω, x ∈ H →
                0 < projectionV n g x ∧
                (1 / 2 : ℝ) ≤ projectionEnergy n g x ∧
                z * |residualStatisticD n r x| ≤ projectionV n g x / 8 ∧
                z * |residualStatisticD n r x| < projectionV n g x / 4 ∧
                z ^ (2 : ℕ) * |centeredDelta n g r x| ≤ (1 / 32 : ℝ) ∧
                |centeredDelta n g r x| ≤ (1 / 32 : ℝ) ∧
                -(1 / 8 : ℝ) < centeredDelta n g r x ∧
                |e1 x| ≤ |centeredDelta n g r x| ∧
                z ^ (2 : ℕ) * |e1 x| ≤ (1 / 32 : ℝ) ∧
                z ^ (2 : ℕ) * |e1 x| < (1 / 8 : ℝ) ∧
                |e1 x| ≤ (1 / 32 : ℝ) ∧
                0 < projectionV n g x * Real.sqrt (1 + e1 x) ∧
                0 < Real.sqrt (centeredSq n g r x) ∧
                Real.sqrt (centeredSq n g r x) =
                  projectionV n g x *
                    Real.sqrt (1 + centeredDelta n g r x)) ∧
              (({x : Fin n → Ω | projectionV n g x = 0} ∪
                  {x : Fin n → Ω | Real.sqrt (centeredSq n g r x) = 0}) ⊆ Hᶜ) ∧
              (sampleLaw n μ).real Hᶜ ≤
                (3 : ℝ) * Real.exp (-q) + Real.exp (-cg * (n : ℝ)) +
                  (4 : ℝ) * Real.exp (-(z * Real.sqrt (n : ℝ)) / (2 : ℝ))
```

## qualified234; namespace Shao.OQ6.OriginalSingleWitnessAnalyticStrictFrontier

{"path": "C:/game/shao lean/drafts/oq56/unit234/author-repair-02/OriginalSingleWitnessAnalyticStrictFrontier.lean", "sha256": "8cc15a8f79707bc6ff88896cef3125030284e309907966e9eabeb7d4b3a1ca90", "bytes": 36755}

```lean
import Shao.OQ6.OriginalLiteralWeightedConsumer
import Shao.OQ6.NormalizedStrictMomentBudgets
import Shao.OQ6.IIDSourceStrictMomentBudgets

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
                |compactCostη k - compactCost0| < τ)))
```

## qualified235-adjacent-not-invoked; namespace Shao.OQ6.OriginalRetainedClipComparisonPayment

{"path": "C:/game/shao lean/drafts/oq56/unit235/author-01/OriginalRetainedClipComparisonPayment.lean", "sha256": "b16dcd02c4a14518bdbbd64b33ce94bcefe7c7770496e8f1a8a7c92872e3fb55", "bytes": 5430}

```lean
import Shao.OQ5.P51.LiteralClippedComparison
import Shao.OQ6.OriginalGoodEventBridge
import Mathlib.MeasureTheory.Measure.Real

theorem fixed_original_retained_clip_comparison_payment
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgmean : (∫ o : Ω, g o ∂μ) = 0)
    (hgsecond : (∫ o : Ω, (g o) ^ (2 : ℕ) ∂μ) = 1) :
    ∃ cg : ℝ, 0 < cg ∧
      ∀ (C a t0 M : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a)
        (ht0 : 0 < t0) (hM : 0 ≤ M),
        ∀ᶠ n : ℕ in atTop,
          4 ≤ n ∧
          ∀ (r : Ω → Ω → ℝ) (w : Ω → ℝ)
            (hr : Measurable (Function.uncurry r))
            (hr1 : Integrable (Function.uncurry r) (μ.prod μ))
            (hcR : ∀ᵐ o : Ω ∂μ, (∫ y : Ω, r o y ∂μ) = 0)
            (hcL : ∀ᵐ y : Ω ∂μ, (∫ o : Ω, r o y ∂μ) = 0)
            (hW : ∀ᵐ o : Ω ∂μ, 0 ≤ w o)
            (hWR : ∀ᵐ o : Ω ∂μ, w o ≤ boundedPolylogHeight C a n)
            (hSq : Integrable (fun o : Ω => (w o) ^ (2 : ℕ)) μ)
            (hSqBound : (∫ o : Ω, (w o) ^ (2 : ℕ) ∂μ) ≤ M)
            (hEnv : ∀ᵐ p : Ω × Ω ∂μ.prod μ,
              |r p.1 p.2| ≤ w p.1 * w p.2)
            (hsym : ∀ o y : Ω, r o y = r y o)
            (rho : ℝ) (hrho : 0 ≤ rho)
            (hStudentizerWindow : 1 + rho ≤ Real.sqrt (n : ℝ))
            (hSmallWindow : (1 : ℝ) ≤ remainderWindowScale (tailScale M) t0 *
              Real.rpow (n : ℝ) (1 / 6 : ℝ)),
            let q : ℝ := boundedPolylogMomentOrder t0 n
            let physical : (Fin n → Ω) → ℝ := fun x =>
              if Real.sqrt (centeredSq n g r x) = 0 then 0 else
                (projectionW n g x + residualStatisticD n r x) /
                  Real.sqrt (centeredSq n g r x)
            let clipped : (Fin n → Ω) → ℝ :=
              clippedCenteredStatistic n g r 512 rho 1
            let Eclip : Set (Fin n → Ω) := {x | clipped x ≠ physical x}
            Eclip ⊆ (projectionGood n g 1)ᶜ ∪ lowerStudentizerBad n g r 1 ∧
              (sampleLaw n μ).real Eclip ≤
                (3 : ℝ) * Real.exp (-q) + Real.exp (-cg * (n : ℝ)) +
                  (4 : ℝ) * Real.exp (-(Real.sqrt (n : ℝ)) / (2 : ℝ))
```

## qualified236-adjacent-not-invoked; namespace Shao.OQ6.OriginalExceptionalTailAbsorption

{"path": "C:/game/shao lean/drafts/oq56/unit236/author-repair-01/OriginalExceptionalTailAbsorption.lean", "sha256": "cb1ed434c1029e674ddff14a1be07ab55b2fb064060acbe92bea389a93f7df8f", "bytes": 11444}

```lean
import Shao.Probability.GaussianTail
import Shao.OQ5.P51.BoundedPolylogWindow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

theorem eventually_original_exceptional_payment_absorbed
    (t0 cg : ℝ) (ht0 : 0 < t0) (hcg : 0 < cg) :
    let cWindow : ℝ := min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ))
    0 < cWindow ∧
      ∀ᶠ n : ℕ in atTop,
        4 ≤ n ∧
          (1 : ℝ) ≤ cWindow * Real.rpow (n : ℝ) (1 / 6 : ℝ) ∧
          ∀ z : ℝ, (1 : ℝ) ≤ z →
            z ≤ cWindow * Real.rpow (n : ℝ) (1 / 6 : ℝ) →
            (6 : ℝ) *
                Real.exp (-Shao.OQ5.P51.boundedPolylogMomentOrder t0 n) +
              (2 : ℝ) * Real.exp (-cg * (n : ℝ)) +
              (8 : ℝ) * Real.exp (-(Real.sqrt (n : ℝ)) / (2 : ℝ)) ≤
              Real.exp (-(t0 / (2 : ℝ)) *
                Real.rpow (n : ℝ) (1 / 3 : ℝ)) *
                Shao.standardNormalTail z
```

## original-canonical-data; namespace Shao.OQ6.ActualQuadraticTiltMoments

{"path": "C:/game/shao lean/library/Shao/OQ6/ActualQuadraticTiltMoments.lean", "sha256": "f4772e78008aad28d89f99a6c52e63ba15329fab40c1b66fb41dc2ed3b249d10", "bytes": 23460}

```lean
import Shao.OQ6.QuadraticTilt
import Shao.OQ6.ObservationProductTilt
import Shao.OQ6.FiniteTiltedMoments
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem actual_quadratic_source_moments
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun z : Ω × Ω => h z.1 z.2))
    (hh2 : MemLp (fun z : Ω × Ω => h z.1 z.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ z : Ω × Ω, h z.1 z.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (n : ℕ) (hn : 3 ≤ n)
    (x : ℝ) (hx : 0 ≤ x)
    (hwindow : x ≤ Real.sqrt (n : ℝ) /
      (2 * Real.exp (1 / 2 : ℝ))) :
    let C : ℝ := Real.exp (1 / 2 : ℝ)
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)
    let s : ℝ := 1 + Real.sqrt v
    let a : ℝ := x / Real.sqrt (n : ℝ)
    let φ : Ω → ℝ := fun o => a * g o - (a * g o) ^ 2 / 2
    let w : Ω → ℝ := fun o => Real.exp (φ o)
    let m : ℝ := ∫ o, w o ∂μ
    let L : Ω → ℝ := fun o => w o / m
    let ρ : Measure Ω :=
      μ.withDensity (fun o => ENNReal.ofReal (L o))
    let P₀ : Measure (Fin n → Ω) :=
      Measure.pi (fun _ : Fin n => μ)
    let S : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ j : Fin n, φ (ξ j)
    let Pₐ : Measure (Fin n → Ω) := P₀.tilted S
    let F : (Fin n → Ω) → ℝ := fun ξ =>
      Shao.OQ5.P35.unorderedPairSum (fun i j => r (ξ i) (ξ j))
    let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Shao.OQ6.ResidualDeletion.rowSum
        (fun j k => r (ξ j) (ξ k)) i
    let Λsq : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ i : Fin n, ψ ξ i ^ 2
    let A : ℝ :=
      ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(ρ.prod ρ)
    let B : ℝ :=
      ∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
        ∂(ρ.prod (ρ.prod ρ))
    let D : ℝ :=
      ∫ d : (Ω × Ω) × (Ω × Ω),
        r d.1.1 d.1.2 * r d.2.1 d.2.2
        ∂((ρ.prod ρ).prod (ρ.prod ρ))
    Measurable g ∧ MemLp g 2 μ ∧ (∫ o, g o ∂μ) = 0 ∧
      (∫ o, g o ^ 2 ∂μ) = 1 ∧
      Measurable (fun z : Ω × Ω => r z.1 z.2) ∧
      MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ) ∧
      (∀ o y, r o y = r y o) ∧
      (∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0) ∧
      0 ≤ v ∧ 1 ≤ s ∧ v ≤ s ^ 2 ∧
      Integrable w μ ∧ (1 / 2 : ℝ) ≤ m ∧ m ≤ (3 / 2 : ℝ) ∧
      Measurable L ∧ Integrable L μ ∧
      (∀ o, 0 < L o ∧ L o ≤ 2 * C) ∧
      (∫ o, L o ∂μ) = 1 ∧
      Integrable (fun o => (L o - 1) ^ 2) μ ∧
      (∫ o, (L o - 1) ^ 2 ∂μ) ≤ 4 * C ^ 2 * a ^ 2 ∧
      μ.tilted φ = ρ ∧ IsProbabilityMeasure ρ ∧
      Integrable (fun ξ => Real.exp (S ξ)) P₀ ∧
      (∫ ξ, Real.exp (S ξ) ∂P₀) = m ^ n ∧ 0 < m ^ n ∧
      (∀ ξ, Real.exp (S ξ) / m ^ n =
        ∏ j : Fin n, L (ξ j)) ∧
      Pₐ = P₀.withDensity
        (fun ξ => ENNReal.ofReal (∏ j : Fin n, L (ξ j))) ∧
      Pₐ = Measure.pi (fun _ : Fin n => ρ) ∧
      IsProbabilityMeasure Pₐ ∧
      MemLp F 2 Pₐ ∧ Integrable (fun ξ => F ξ ^ 2) Pₐ ∧
      (∀ i : Fin n, MemLp (fun ξ => ψ ξ i) 2 Pₐ) ∧
      Integrable Λsq Pₐ ∧
      (∫ ξ, F ξ ^ 2 ∂Pₐ) =
        (n.choose 2 : ℝ) * A +
          6 * (n.choose 3 : ℝ) * B +
          6 * (n.choose 4 : ℝ) * D ∧
      (∫ ξ, Λsq ξ ∂Pₐ) =
        2 * (n.choose 2 : ℝ) * A +
          6 * (n.choose 3 : ℝ) * B ∧
      (∫ ξ, F ξ ^ 2 ∂Pₐ) ≤ s ^ 2 *
        (4 * C ^ 2 * (n.choose 2 : ℝ) +
          48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2 +
          96 * C ^ 4 * (n.choose 4 : ℝ) * a ^ 4) ∧
      (∫ ξ, Λsq ξ ∂Pₐ) ≤ s ^ 2 *
        (8 * C ^ 2 * (n.choose 2 : ℝ) +
          48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2) ∧
      (∫ ξ, F ξ ^ 2 ∂Pₐ) ≤ s ^ 2 * (n : ℝ) ^ 2 *
        (2 * C ^ 2 + 8 * C ^ 3 * x ^ 2 + 4 * C ^ 4 * x ^ 4) ∧
      (∫ ξ, Λsq ξ ∂Pₐ) ≤ s ^ 2 * (n : ℝ) ^ 2 *
        (4 * C ^ 2 + 8 * C ^ 3 * x ^ 2) ∧
      (∫ ξ, F ξ ^ 2 ∂Pₐ) ≤
        14 * C ^ 4 * s ^ 2 * (n : ℝ) ^ 2 * (1 + x ^ 4) ∧
      (∫ ξ, Λsq ξ ∂Pₐ) ≤
        14 * C ^ 4 * s ^ 2 * (n : ℝ) ^ 2 * (1 + x ^ 2)
```

## Ordinary definitions: actual normalization

{"path": "C:/game/shao lean/library/Shao/OQ6/ActualMomentNormalization.lean", "sha256": "7e781dc929166b43c69dd6ffe463c62e2d1508fa5283451852ea50afed18c237", "bytes": 22137}

```lean
noncomputable def actualCoordinateMean
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) {n : ℕ} (Y : Fin n → Ω → ℝ) (i : Fin n) : ℝ :=
  ∫ ω, Y i ω ∂ν

noncomputable def actualCenteredFamily
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) {n : ℕ} (Y : Fin n → Ω → ℝ)
    (i : Fin n) (ω : Ω) : ℝ :=
  Y i ω - actualCoordinateMean ν Y i

noncomputable def actualNormalizationScale
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) {n : ℕ} (Y : Fin n → Ω → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, ∫ ω, (actualCenteredFamily ν Y i ω) ^ 2 ∂ν)

noncomputable def actualNormalizedFamily
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) {n : ℕ} (Y : Fin n → Ω → ℝ)
    (i : Fin n) (ω : Ω) : ℝ :=
  Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation
    (actualCoordinateMean ν Y i) (actualNormalizationScale ν Y) (Y i) ω
```

## Ordinary definitions: coding

{"path": "C:/game/shao lean/library/Shao/OQ6/QuantizedObservationCoding.lean", "sha256": "c755dcb72b58931c797416f23ce4f13b383cd17b1b6ef5b2bd5b86b368290062", "bytes": 6921}

```lean
noncomputable def quantizedObservation
    {X : Type*} (ε : ℝ) (ξ c : X → ℝ) (x : X) : ℝ :=
  ε * ((Int.floor (ξ x / ε) : ℝ) + c x)

def deterministicAffineObservation
    {X : Type*} (a s : ℝ) (Y : X → ℝ) (x : X) : ℝ :=
  (Y x - a) / s
```

## Ordinary definitions: base-four code

{"path": "C:/game/shao lean/library/Shao/OQ6/ScalarObservationCoding.lean", "sha256": "78ba58ee64238fdff51a026d86ab939d34ac66787f804c562c4f0984dc96057c", "bytes": 14428}

```lean
noncomputable def baseFourIndicatorCode
    {X : Type*} (A : ℕ → Set X) (x : X) : ℝ :=
  ∑' k : ℕ,
    (if x ∈ A k then (2 : ℝ) else 1) / (4 : ℝ) ^ (k + 1)
```

## Ordinary definitions: finite studentizer

{"path": "C:/game/shao lean/library/Shao/OQ5/P51/BoundedStudentizerGeometry.lean", "sha256": "bc64d3e11a64f62ad654305ce579c1779546d4df37b5593090105af910502edc", "bytes": 33066}

```lean
def sampledKernel
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω) : Fin n → Fin n → ℝ :=
  fun (i j : Fin n) => g (x i) + g (x j) + r (x i) (x j)

-- D02

def projectionEnergy
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  (∑ i : Fin n, (g (x i)) ^ (2 : ℕ)) / (n : ℝ)

-- D03

def projectionV
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  Real.sqrt (projectionEnergy n g x)

-- D04

def projectionW
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  (∑ i : Fin n, g (x i)) / Real.sqrt (n : ℝ)

-- D05

def residualStatisticD
    (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  originalUpper n r x / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))

-- D06

def residualU
    (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (x : Fin n → Ω) : Fin n → ℝ :=
  fun i : Fin n => originalRows n r x i / ((n : ℝ) - 2)

-- D07

def residualEnergyJ
    (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  ∑ i : Fin n, (residualU n r x i) ^ (2 : ℕ)

-- D08

def centeredSq
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  Shao.OQ6.FiniteRows.jackknifeSq (sampledKernel n g r x) / 4

-- D09

def centeredDelta
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  @ite ℝ (projectionV n g x = 0)
    (Classical.propDecidable (projectionV n g x = 0))
    (0 : ℝ) (centeredSq n g r x / (projectionV n g x) ^ (2 : ℕ) - 1)

-- D10

def projectionGood
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (y : ℝ) : Set (Fin n → Ω) :=
  {x : Fin n → Ω | (1 / 2 : ℝ) ≤ projectionEnergy n g x ∧
    |projectionW n g x| ≤ Real.sqrt y * Real.sqrt (Real.sqrt (n : ℝ)) * (4 + projectionV n g x)}
```

## Ordinary definitions: clipping

{"path": "C:/game/shao lean/library/Shao/OQ5/P51/ClippedStudentizer.lean", "sha256": "a8bffbabb649cdc788b58517a89185691f72de92776a882f3b9ffdcddc0b748b", "bytes": 11786}

```lean
def studentizerClip (B d : ℝ) : ℝ :=
  max (-(min B (1 / 2 : ℝ))) (min d B)

def studentizerClipBudget (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (C0 rho y : ℝ) (x : Fin n → Ω) : ℝ :=
  C0 * (((1 + rho) * y) / Real.sqrt (n : ℝ) +
    residualEnergyJ n r x / ((1 + rho) * y * Real.sqrt (n : ℝ)))

def clippedCenteredDelta (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (C0 rho y : ℝ)
    (x : Fin n → Ω) : ℝ :=
  if projectionV n g x = 0 then 0 else
    studentizerClip (studentizerClipBudget n r C0 rho y x)
      (centeredDelta n g r x)

def clippedCenteredStatistic (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (C0 rho y : ℝ)
    (x : Fin n → Ω) : ℝ :=
  if projectionV n g x = 0 then 0 else
    (projectionW n g x + residualStatisticD n r x) /
      (projectionV n g x *
        Real.sqrt (1 + clippedCenteredDelta n g r C0 rho y x))
```

## Ordinary definitions: polylog

{"path": "C:/game/shao lean/library/Shao/OQ5/P51/BoundedPolylogWindow.lean", "sha256": "1d2ad2ca13be7c987c8e0520c5687dba60669af0db6e0dd01edcbc3105043b7e", "bytes": 9803}

```lean
def boundedPolylogHeight (C a : ℝ) (n : ℕ) : ℝ :=
  C * Real.rpow (Real.log (n : ℝ)) a

def boundedPolylogMomentOrder (t0 : ℝ) (n : ℕ) : ℝ :=
  t0 * Real.rpow (n : ℝ) (1 / 3 : ℝ)
```

## Ordinary definitions: window scale

{"path": "C:/game/shao lean/library/Shao/OQ5/P51/BoundedRemainderPayments.lean", "sha256": "c0102fa13835fb22b01148e42d66cf8ff5704d682b9a6142eb508d7172d95cc9", "bytes": 28173}

```lean
def remainderWindowScale (K t0 : ℝ) : ℝ :=
  min (1 : ℝ)
    (min (1 / ((32 : ℝ) * (K + 1) * (t0 + 1)))
      (1 / Real.sqrt ((32 : ℝ) * (studentizerGeometryScale K + 1) *
        (1 + Real.sqrt t0 + t0))))
```

## Ordinary definitions: tail scales

{"path": "C:/game/shao lean/library/Shao/OQ6/BoundedProductEnvelopeTails.lean", "sha256": "43367b3ce14f174a8c8e3db4152e3db3b553ab0dbc9c4521565a1db8ddac1b14", "bytes": 40651}

```lean
def commonMomentScale
    (M : ℝ) :
  ℝ :=
  64 * (M + 1)

def envelopeTailScale
    (M : ℝ) :
  ℝ :=
  4 * M + 8

def squareTailScale
    (M : ℝ) :
  ℝ :=
  Real.exp 1 * (M + 1)

def scalarTailScale
    (M : ℝ) :
  ℝ :=
  8 * Real.exp 1 * envelopeTailScale M

def rowTailScale
    (M : ℝ) :
  ℝ :=
  8 * (Real.exp 1) ^ 2 * (envelopeTailScale M) ^ 2

def tailScale
    (M : ℝ) :
  ℝ :=
  max (squareTailScale M) (max (scalarTailScale M) (rowTailScale M))
```

## Ordinary definitions: original sample law/rows

{"path": "C:/game/shao lean/library/Shao/OQ6/CanonicalDoubleGhostRowMoments.lean", "sha256": "0b7f38c8840ffefb15fc9185c8f54c2c6907da96cc49bd5e7ee3c5ed512250fc", "bytes": 38651}

```lean
def sampleLaw (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (ν : Measure Ω) : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => ν)

def pairSamples (n : ℕ) {Ω : Type*} (p : (Fin n → Ω) × (Fin n → Ω)) : Fin n → Ω × Ω := fun i : Fin n => (p.1 i, p.2 i)

def originalRows (n : ℕ) {Ω : Type*} (r : Ω → Ω → ℝ) (x : Fin n → Ω) : EuclideanSpace ℝ (Fin n) := WithLp.toLp (2 : ℝ≥0∞) (V := Fin n → ℝ) (fun i : Fin n => ∑ j : Fin n, if i = j then 0 else r (x i) (x j))
```

## Ordinary definitions: original upper sum

{"path": "C:/game/shao lean/library/Shao/OQ6/CanonicalDoubleGhostScalarMoments.lean", "sha256": "17790c480efcab2d11cb5d00ccd215a6853e289fb078b5b041ae3bba972ab68c", "bytes": 32159}

```lean
def originalUpper (n : ℕ) {Ω : Type*} (r : Ω → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then r (x i) (x j) else 0
```

## Observed project real-map application

This is an exact accepted project application, not a claim to have read the external Mathlib declaration source.

## map_measureReal_apply

{"path": "C:/game/shao lean/library/Shao/OQ6/OriginalSelfNormalizedTail.lean", "sha256": "cfa791fd240ee560b2a876ea69a64e46c7c84735c935e1380446025e69a9e61a", "bytes": 3989}

```lean
  have hpreimage : (M.prod M).real (F ⁻¹' D) = P.real D := by
    simpa only [hF.map_eq] using
      (map_measureReal_apply (μ := M.prod M) hF.measurable hD).symm
```

## Accepted234 deterministic section context

Existing accepted context, not new proof implementation:

## section and ξ0 measurability

{"path": "C:/game/shao lean/drafts/oq56/unit234/author-repair-02/OriginalSingleWitnessAnalyticStrictFrontier.lean", "sha256": "8cc15a8f79707bc6ff88896cef3125030284e309907966e9eabeb7d4b3a1ca90", "bytes": 36755}

```lean
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
```
