import Shao.OQ6.OriginalLevelDependentUpperPhysicalFrontier
import Shao.OQ6.CurrentLevelTrueDeletedConditionalTail
import Shao.OQ6.NormalizedAnalyticCostLimits

set_option autoImplicit false
universe u
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology MeasureTheory symmDiff
open Shao.OQ5.P51

namespace Shao.OQ6.OriginalCurrentLevelPhysicalFiniteCostTail
noncomputable section
theorem actual_original_current_level_physical_finite_cost_tail
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
          (hGeometry : (1 + rho) * z ≤ Real.sqrt (n : ℝ))
          (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
          (hgp : Integrable[mΩ] (fun o : Ω => Real.rpow |g o| p) μ)
          (cSZ C1 C2 C3 C4 : ℝ)
          (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u}
            cSZ C1 C2 C3 C4),
        let β : ℝ := ∫ o : Ω, Real.rpow |g o| p ∂μ
        let cWindow : ℝ := Real.rpow (min (1 / 2 : ℝ) cSZ / 2) (1 / p)
        (β = 0 ∨ (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) *
          Real.rpow (n : ℝ) ((p - 2) / (2 * p)))) →
        let mN : MeasurableSpace (Fin n → Ω) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => mΩ)
        let P : @Measure (Fin n → Ω) mN :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => mΩ) (fun _ : Fin n => μ)
        let ξ0 : Fin n → (Fin n → Ω) → ℝ :=
          fun i ζ => g (ζ i) / Real.sqrt (n : ℝ)
        let D1 : (Fin n → Ω) → ℝ := residualStatisticD n r
        let D2 : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r 512 rho z
        let A0 : (Fin n → Ω) → ℝ := fun ζ => |D1 ζ|
        let B0 : (Fin n → Ω) → ℝ := studentizerClipBudget n r 512 rho z
        let A0delete : Fin n → (Fin n → Ω) → ℝ :=
          fun i ζ => |residualStatisticDDeleted n r ζ i|
        let B0delete : Fin n → (Fin n → Ω) → ℝ :=
          fun i ζ => studentizerClipBudgetDeleted n r 512 rho z ζ i
        let ℓ0 : Fin n → (Fin n → Ω) → ℝ :=
          fun i ζ => z * ξ0 i ζ - (z * ξ0 i ζ) ^ 2 / 2
        let S0 : (Fin n → Ω) → ℝ := fun ζ => ∑ i : Fin n, ℓ0 i ζ
        let S0minus : Fin n → (Fin n → Ω) → ℝ :=
          fun i ζ => ∑ j ∈ Finset.univ.erase i, ℓ0 j ζ
        let I0 : ℝ := ∫ ζ, Real.exp (S0 ζ) ∂P
        let fullTest0 : (Fin n → Ω) → ℝ := fun ζ => z * A0 ζ + z ^ 2 * B0 ζ
        let deletedTest0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ =>
          min |z * ξ0 i ζ| 1 * (|A0 ζ - A0delete i ζ| + z * |B0 ζ - B0delete i ζ|)
        let sourceCost0 : ℝ :=
          ((∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P) +
            ∑ i : Fin n, ∫ ζ, deletedTest0 i ζ * Real.exp (S0minus i ζ) ∂P) / I0
        let δoriginal : Fin n → ℝ := fun i =>
          ∫ ζ, (z * ξ0 i ζ) ^ 2 * min |z * ξ0 i ζ| 1 ∂P
        let Loriginal : ℝ := ∑ i : Fin n, δoriginal i
        let physical : (Fin n → Ω) → ℝ := fun ζ =>
          if Real.sqrt (centeredSq n g r ζ) = 0 then 0 else
            (projectionW n g ζ + D1 ζ) / Real.sqrt (centeredSq n g r ζ)
        let payment : ℝ :=
          (3 : ℝ) * Real.exp (-boundedPolylogMomentOrder t0 n) +
            Real.exp (-cg * (n : ℝ)) +
            (4 : ℝ) * Real.exp (-(z * Real.sqrt (n : ℝ)) / (2 : ℝ))
        let cubicCost : ℝ :=
          64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) *
            (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ)
        0 ≤ sourceCost0 ∧ sourceCost0 ≤ cubicCost ∧
        Shao.standardNormalTail z * Real.exp (-C1 * Loriginal) *
            (1 - C2 * sourceCost0) - 2 * payment ≤
          P.real {ζ : Fin n → Ω | z ≤ physical ζ} ∧
        P.real {ζ : Fin n → Ω | z ≤ physical ζ} ≤
          Shao.standardNormalTail z * Real.exp (C3 * Loriginal) *
            (1 + C4 * sourceCost0) + 4 * payment ∧
        Shao.standardNormalTail z * Real.exp (-C1 * Loriginal) *
            (1 - C2 * cubicCost) - 2 * payment ≤
          P.real {ζ : Fin n → Ω | z ≤ physical ζ} ∧
        P.real {ζ : Fin n → Ω | z ≤ physical ζ} ≤
          Shao.standardNormalTail z * Real.exp (C3 * Loriginal) *
            (1 + C4 * cubicCost) + 4 * payment
:= by
  set_option maxHeartbeats 800000 in
    classical
    intro g r v rho
    -- This is the only selection of the canonical original coding witness.
    have hOriginal :=
      Shao.OQ6.OriginalLevelDependentUpperPhysicalFrontier.actual_original_level_dependent_upper_physical_frontier
        μ h hh hh2 hhsymm hcenter hprojectionsecond
    dsimp only at hOriginal
    rcases hOriginal with
      ⟨m₀, hm₀, hcg, hRetained, cg, hcgPositive, hPhysicalAll⟩
    let μ₀ : @Measure Ω m₀ := μ.trim hm₀
    letI : MeasurableSpace Ω := m₀
    letI : MeasurableSpace.CountablyGenerated Ω := hcg
    rcases hRetained with ⟨hμ₀prob, hFor, hFrontier⟩
    letI : IsProbabilityMeasure μ₀ := hμ₀prob
    refine ⟨cg, hcgPositive, ?_⟩
    intro Cenv aenv t0 Menv hCenv haenv ht0 hMenv
    filter_upwards [hPhysicalAll Cenv aenv t0 Menv hCenv haenv ht0 hMenv] with n hn
    refine ⟨hn.1, ?_⟩
    intro w hW hWR hSq hSqBound hEnv z hz hTiltWindow hEnvelopeWindow hGeometry
      p hp2 hp3 hgp cSZ C1 C2 C3 C4 hSZ
    intro β cWindow hMomentWindow
    -- The unused public D2 let is definitionally erased; the head is unchanged.
    intro mN P ξ0 D1 A0 B0 A0delete B0delete ℓ0 S0 S0minus I0
      fullTest0 deletedTest0 sourceCost0 δoriginal Loriginal physical payment cubicCost
    let mN₀ : MeasurableSpace (Fin n → Ω) :=
      @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => m₀)
    let P₀ : @Measure (Fin n → Ω) mN₀ :=
      @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
        (fun _ : Fin n => m₀) (fun _ : Fin n => μ₀)
    let N : ℝ := Real.sqrt (n : ℝ)
    let K : ℝ := 4 * Real.sqrt (n : ℝ)
    let ε : ℕ → ℝ := fun k => 1 / (8 * Real.sqrt (n : ℝ) * ((k : ℝ) + 1))
    let D2 : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r 512 rho z
    let T0 : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho z
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
    let ξlocal : Fin n → (Ω × ℝ) → ℝ := fun _ t => g t.1 / N
    let Ylocal : ℕ → Fin n → (Ω × ℝ) → ℝ := fun k i =>
      Shao.OQ6.QuantizedObservationCoding.quantizedObservation (ε k) (ξlocal i) (c i)
    let ξ : Fin n → (Fin n → Ω × ℝ) → ℝ := fun i x => ξlocal i (x i)
    let Y : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x => Ylocal k i (x i)
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
    let AdeleteNew : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ :=
      fun k i x => Adelete i x + Mdelete k i x
    let ℓη : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ :=
      fun k i x => z * η k i x - (z * η k i x) ^ 2 / 2
    let Sη : ℕ → (Fin n → Ω × ℝ) → ℝ := fun k x => ∑ i : Fin n, ℓη k i x
    let Sηminus : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ :=
      fun k i x => ∑ j ∈ Finset.univ.erase i, ℓη k j x
    let Iη : ℕ → ℝ := fun k => ∫ x, Real.exp (Sη k x) ∂ν
    let fullTestη : ℕ → (Fin n → Ω × ℝ) → ℝ := fun k x => z * Anew k x + z ^ 2 * B x
    let deletedTestη : ℕ → Fin n → (Fin n → Ω × ℝ) → ℝ := fun k i x =>
      min |z * η k i x| 1 * (|Anew k x - AdeleteNew k i x| + z * |B x - Bdelete i x|)
    let sourceCostη : ℕ → ℝ := fun k =>
      ((∫ x, fullTestη k x * Real.exp (Sη k x) ∂ν) +
        ∑ i : Fin n, ∫ x, deletedTestη k i x * Real.exp (Sηminus k i x) ∂ν) / Iη k
    let Fz : ℝ → ℝ := fun t => (z * t) ^ 2 * min |z * t| 1
    let δaug : Fin n → ℝ := fun i => ∫ x, Fz (ξ i x) ∂ν
    let δη : ℕ → Fin n → ℝ := fun k i => ∫ x, Fz (η k i x) ∂ν
    let Laug : ℝ := ∑ i : Fin n, δaug i
    let Lη : ℕ → ℝ := fun k => ∑ i : Fin n, δη k i
    let V0 : (Fin n → Ω) → ℝ := projectionV n g
    let codedClip : (Fin n → Ω × ℝ) → ℝ := fun x =>
      if V x = 0 then 0 else (W x + D1 (q x)) / (V x * b x)
    -- All data below come from this same retained current-z packet.
    have hCurrent := hFrontier n hn.1 z hz hTiltWindow
    rcases hCurrent with ⟨hAnalytic, hMomentPacket⟩
    rcases hAnalytic with
      ⟨hP₀prob, hP₀map, hνprob, hq, hε, hεlim, hξPacket, hξenergy, hYpacket,
        hD2bounds, hT0zero, hTηzero, hηpacket, hSigned,
        hHm, hHI, hHdelete, hQint, hQlim, hAnew, hAdeleteNew,
        hAnewErr, hAdeleteErr, hAnewLim, hAdeleteLim, hDelta, hDeltaInt,
        hFullFactor, hDeletedFactor, hDfactor, hOriginalFullInt, hFullInt,
        hOriginalDeletedInt, hDeletedInt, hOriginalCompactDeletedInt, hCompactDeletedInt,
        hI0positive, hIηpositive, hIlim, hFullLim, hDeletedLim,
        hNormalizedFullLim, hNormalizedDeletedLim, hCompactDelLim,
        hSourceLim, hCompactLim, hSourceNonneg, hSourceCubic, hEventualCubic⟩
    change @IsProbabilityMeasure (Fin n → Ω × ℝ) mAug ν at hνprob
    letI : @IsProbabilityMeasure (Fin n → Ω × ℝ) mAug ν := hνprob
    have hPhysical := hn.2 w hW hWR hSq hSqBound hEnv z hz
      hTiltWindow hEnvelopeWindow hGeometry
    rcases hPhysical with
      ⟨hPprob, hPhysicalP₀prob, hPhysicalνprob, hId, hPhysicalq,
        hξ0m, hV0m, hD1m, hD2m, hD1aug, hD2aug, hV0Eq, hWV,
        hT0m, hT0Original, hT0Law, hCodedLaw, hPhysicalMeas,
        hHmeas, hEclipMeas, hSsafe, hSoriginal, hJm, hHsubset,
        hOn, hUnionSubset, hRemainderSubset, hJmargin, hνSafe, hPSafe, hPcmono,
        hHpay, hJpay, hSafeFee, hAllFee, hEclipFee, hLawPayment,
        hηmPhysical, hNumMeas, hE2m, hZm, hηpoint, hWpoint, hVpoint,
        hQpoint, hDpoint, hD2good, hSafe, hE2subset, hZsubset,
        hE2fee, hZfee, hE2pay, hZpay, hUpperPay, hLimsup,
        hEventualPay, hLimsupPay, hSumLimsup, hStrictJoint⟩
    change @IsProbabilityMeasure (Fin n → Ω) mN P at hPprob
    letI : @IsProbabilityMeasure (Fin n → Ω) mN P := hPprob
    change Measurable[mAug, borel ℝ] (fun x => D1 (q x)) at hD1aug
    change Measurable[mAug, borel ℝ] (fun x => D2 (q x)) at hD2aug
    change Measurable[mN, borel ℝ] T0 at hT0Original
    change Measurable[mN, borel ℝ] physical at hPhysicalMeas
    change (∀ x : Fin n → Ω × ℝ,
      W x = projectionW n g (q x) ∧ V x = V0 (q x)) at hWV
    change @Measure.map (Fin n → Ω × ℝ) ℝ mAug (borel ℝ) (fun x => T0 (q x)) ν =
      @Measure.map (Fin n → Ω) ℝ mN (borel ℝ) T0 P at hCodedLaw
    change 0 ≤ sourceCost0 at hSourceNonneg
    change sourceCost0 ≤ cubicCost at hSourceCubic
    change Filter.Tendsto sourceCostη Filter.atTop (nhds sourceCost0) at hSourceLim
    change (∀ k : ℕ, 0 < Iη k) at hIηpositive
    have hn1 : 1 ≤ n := by omega
    have hcSZ : 0 < cSZ := hSZ.1
    have hC2 : 0 < C2 := hSZ.2.2.1
    have hC4 : 0 < C4 := hSZ.2.2.2.2.1
    -- The exact original p-window supplies strict budgets and original-P limits.
    have hMoment := hMomentPacket p hp2 hp3 hgp cSZ hcSZ
    rcases hMoment with
      ⟨hBeta, hcWindowPositive, hcWindowPower, hcWindowSmall,
        hOriginalδInt, hAugδInt, hδJoin, hLJoin, hδNonneg, hLNonneg,
        hRate, hZero, hWindow⟩
    rcases hWindow hMomentWindow with
      ⟨hδHalf, hLStrict, hδηInt, hδLim, hLlim, hJointStrictCost⟩
    change Laug = Loriginal at hLJoin
    change Filter.Tendsto Lη Filter.atTop (nhds Laug) at hLlim
    have hLoriginalLim : Filter.Tendsto Lη Filter.atTop (nhds Loriginal) := by
      simpa only [hLJoin] using hLlim
    obtain ⟨k₀, hk₀⟩ := hJointStrictCost 1 1 (by norm_num) (by norm_num)
    have hBudget : ∀ᶠ k : ℕ in Filter.atTop,
        (∀ i : Fin n, δη k i < (1 / 2 : ℝ)) ∧ Lη k < cSZ * z ^ 2 := by
      refine Filter.eventually_atTop.2 ⟨k₀, ?_⟩
      intro k hk
      exact ⟨(hk₀ k hk).1, (hk₀ k hk).2.1⟩
    have hηm (k : ℕ) (i : Fin n) : Measurable[mAug, borel ℝ] (η k i) :=
      ((hηpacket k).2.2.2.1 i).1
    have hηindep (k : ℕ) : iIndepFun (η k) ν := (hηpacket k).2.2.1
    have hη2 (k : ℕ) (i : Fin n) : MemLp (η k i) 2 ν :=
      ((hηpacket k).2.2.2.1 i).2.1
    have hηmean (k : ℕ) (i : Fin n) : (∫ x, η k i x ∂ν) = 0 :=
      ((hηpacket k).2.2.2.1 i).2.2
    have hηenergy (k : ℕ) : (∑ i : Fin n, ∫ x, (η k i x) ^ 2 ∂ν) = 1 :=
      (hηpacket k).2.2.2.2.1
    have hηpos (k : ℕ) : ∀ᵐ x ∂ν, 0 < Real.sqrt (∑ i : Fin n, (η k i x) ^ 2) := by
      filter_upwards [(hηpacket k).2.2.2.2.2.2] with x hx
      exact hx.1
    have hD2pos : ∀ᵐ x ∂ν, 0 < 1 + D2 (q x) :=
      Filter.Eventually.of_forall fun x =>
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hD2bounds (q x)).1
    -- Project the existing triple factors; true AdeleteNew remains unchanged.
    have hTripleSecond : Measurable[borel (ℝ × ℝ × ℝ), borel ℝ]
        (fun t : ℝ × ℝ × ℝ => t.2.1) :=
      (continuous_fst.comp continuous_snd).borel_measurable
    have hTripleThird : Measurable[borel (ℝ × ℝ × ℝ), borel ℝ]
        (fun t : ℝ × ℝ × ℝ => t.2.2) :=
      (continuous_snd.comp continuous_snd).borel_measurable
    have hFullFactorScalar : ∀ k : ℕ,
        ∃ F1 F2 FA FB : (Fin n → ℝ) → ℝ,
          Measurable[borel (Fin n → ℝ), borel ℝ] F1 ∧
          Measurable[borel (Fin n → ℝ), borel ℝ] F2 ∧
          Measurable[borel (Fin n → ℝ), borel ℝ] FA ∧
          Measurable[borel (Fin n → ℝ), borel ℝ] FB ∧
          ∀ x : Fin n → Ω × ℝ,
            Dη k x = F1 (C k x) ∧ D2 (q x) = F2 (C k x) ∧
              Anew k x = FA (C k x) ∧ B x = FB (C k x) := by
      intro k
      obtain ⟨G1, G2, hG1, hG2, hG⟩ := hDfactor k
      obtain ⟨Ffull, hFfull, hFfullEq⟩ := hFullFactor k
      refine ⟨G1, G2, (fun t => (Ffull t).2.1), (fun t => (Ffull t).2.2),
        hG1, hG2, hTripleSecond.comp hFfull, hTripleThird.comp hFfull, ?_⟩
      intro x
      have hAeq := congrArg (fun t : ℝ × ℝ × ℝ => t.2.1) (hFfullEq x)
      have hBeq := congrArg (fun t : ℝ × ℝ × ℝ => t.2.2) (hFfullEq x)
      exact ⟨(hG x).1, (hG x).2, hAeq, hBeq⟩
    have hDeletedFactorScalar : ∀ (k : ℕ) (i : Fin n),
        ∃ FAdelete FBdelete : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
          Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] FAdelete ∧
          Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] FBdelete ∧
          ∀ x : Fin n → Ω × ℝ,
            AdeleteNew k i x = FAdelete (fun j => η k j.val x) ∧
              Bdelete i x = FBdelete (fun j => η k j.val x) := by
      intro k i
      obtain ⟨Fdelete, hFdelete, hFdeleteEq⟩ := hDeletedFactor k i
      refine ⟨(fun t => (Fdelete t).2.1), (fun t => (Fdelete t).2.2),
        hTripleSecond.comp hFdelete, hTripleThird.comp hFdelete, ?_⟩
      intro x
      exact ⟨congrArg (fun t : ℝ × ℝ × ℝ => t.2.1) (hFdeleteEq x),
        congrArg (fun t : ℝ × ℝ × ℝ => t.2.2) (hFdeleteEq x)⟩
    have hFullNonneg (k : ℕ) (x : Fin n → Ω × ℝ) :
        0 ≤ Anew k x ∧ 0 ≤ B x :=
      ⟨(hAnew k).2.2 x, (abs_nonneg _).trans (hD2bounds (q x)).2⟩
    -- The original deleted budgets are already nonnegative in the all-epsilon packet.
    have hSingle := hFor n hn.1 z hz hTiltWindow (ε 0) (hε 0).1 (hε 0).2
    rcases hSingle with
      ⟨_, _, _, _, _, _, _, _, _, _, hSingleTail10⟩
    rcases hSingleTail10 with
      ⟨_, _, _, _, _, _, _, _, _, _, hSingleTail20⟩
    rcases hSingleTail20 with
      ⟨_, _, _, _, _, _, _, _, _, _, hSingleTail30⟩
    rcases hSingleTail30 with
      ⟨_, _, _, _, _, _, _, _, _, _, hSingleTail40⟩
    rcases hSingleTail40 with ⟨_, _, _, _, hOriginalDeletedNonneg, _⟩
    change (∀ (i : Fin n) (ζ : Fin n → Ω),
      0 ≤ A0delete i ζ ∧ 0 ≤ B0delete i ζ) at hOriginalDeletedNonneg
    have hDeletedNonneg (k : ℕ) (i : Fin n) (x : Fin n → Ω × ℝ) :
        0 ≤ AdeleteNew k i x ∧ 0 ≤ Bdelete i x :=
      ⟨(hAdeleteNew k i).2.2 x, (hOriginalDeletedNonneg i (q x)).2⟩
    have hDom (k : ℕ) : ∀ᵐ x ∂ν, |Dη k x| ≤ Anew k x ∧ |D2 (q x)| ≤ B x :=
      Filter.Eventually.of_forall fun x => ⟨(hSigned k x).2.2.2, (hD2bounds (q x)).2⟩
    -- Finite quadratic exponentials are bounded; no exponential-moment input is added.
    have hSηm (k : ℕ) : Measurable[mAug, borel ℝ] (Sη k) := by
      exact Finset.measurable_sum Finset.univ (fun i _ =>
        (measurable_const.mul (hηm k i)).sub
          (((measurable_const.mul (hηm k i)).pow_const 2).div_const 2))
    have hExpInt (k : ℕ) : Integrable[mAug] (fun x => Real.exp (Sη k x)) ν := by
      apply (integrable_const (Real.exp ((n : ℝ) / 2))).mono'
        (hSηm k).exp.aestronglyMeasurable
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        calc
          Sη k x ≤ ∑ _i : Fin n, (1 / 2 : ℝ) := by
            apply Finset.sum_le_sum
            intro i _
            dsimp only [ℓη]
            nlinarith only [sq_nonneg (z * η k i x - 1)]
          _ = (n : ℝ) / 2 := by simp [div_eq_mul_inv]
    have hTilt (k : ℕ) :
        Integrable[mAug] (fun x => Real.exp (Sη k x)) ν ∧ 0 < Iη k :=
      ⟨hExpInt k, hIηpositive k⟩
    have hClipEq : codedClip = fun x : Fin n → Ω × ℝ => T0 (q x) := by
      funext x
      simp only [codedClip, (hWV x).1, (hWV x).2,
        T0, clippedCenteredStatistic, V0, b, D1, D2]
    have hClippedLaw :
        @Measure.map (Fin n → Ω × ℝ) ℝ mAug (borel ℝ) codedClip ν =
          @Measure.map (Fin n → Ω) ℝ mN (borel ℝ) T0 P := by
      rw [hClipEq]
      exact hCodedLaw
    -- Each of the four fees is supplied by 259, with its own event kept intact.
    change P.real {ζ : Fin n → Ω | T0 ζ ≠ physical ζ} ≤ payment at hEclipFee
    change ν.real {x : Fin n → Ω × ℝ | V x = 0} ≤ payment at hZpay
    change ν.real {x : Fin n → Ω × ℝ | z ^ 2 * |D2 (q x)| > (1 / 4 : ℝ)} ≤
      payment at hE2pay
    have hUpperPayPayment (γ : ℝ) (hγ : 0 < γ) : ∀ᶠ k : ℕ in Filter.atTop,
        ν.real {x : Fin n → Ω × ℝ | z * |Dη k x| > Vη k x / 4} ≤ payment + γ := by
      filter_upwards [hEventualPay γ hγ] with k hk
      exact hk.1
    have hConsumer :=
      @Shao.OQ6.CurrentLevelTrueDeletedConditionalTail.actual_current_level_true_deleted_conditional_tail_consumer
        (Fin n → Ω × ℝ) mAug (Fin n → Ω) mN ν hνprob P hPprob n hn1
        ξ ξ0 η (fun x => D1 (q x)) (fun x => D2 (q x)) B Anew AdeleteNew Bdelete
        A0 B0 A0delete B0delete T0 physical
        (fun i => (hξPacket i).1) hD1aug hD2aug hT0Original hPhysicalMeas
        hηm hηindep hη2 hηmean hηenergy hD2pos hηpos
        cSZ C1 C2 C3 C4 hSZ z hz payment payment payment payment
    dsimp only at hConsumer
    have hResult := hConsumer hFullFactorScalar hDeletedFactorScalar
      hFullNonneg hDeletedNonneg hDom hTilt hFullInt hDeletedInt
      hBudget hLoriginalLim hSourceLim hClippedLaw hEclipFee hZpay hE2pay hUpperPayPayment
    rcases hResult with ⟨hEngine, hLowerLim, hUpperLim, hFixedTail,
      hLowerRaw, hUpperRaw, hLowerPhysical, hUpperPhysical, hPayment⟩
    have hExact := hPayment payment le_rfl le_rfl le_rfl le_rfl
    change
      (Shao.standardNormalTail z * Real.exp (-C1 * Loriginal) *
          (1 - C2 * sourceCost0) - 2 * payment ≤
        P.real {ζ : Fin n → Ω | z ≤ physical ζ}) ∧
      (P.real {ζ : Fin n → Ω | z ≤ physical ζ} ≤
        Shao.standardNormalTail z * Real.exp (C3 * Loriginal) *
          (1 + C4 * sourceCost0) + 4 * payment) at hExact
    -- Cubic replacement uses only coefficient monotonicity, not a positive lower factor.
    have hGaussian : 0 ≤ Shao.standardNormalTail z :=
      ((Shao.standardNormalTail_basic.2.2.1 z).1).le
    have hLowerPrefactor :
        0 ≤ Shao.standardNormalTail z * Real.exp (-C1 * Loriginal) :=
      mul_nonneg hGaussian (Real.exp_pos _).le
    have hUpperPrefactor :
        0 ≤ Shao.standardNormalTail z * Real.exp (C3 * Loriginal) :=
      mul_nonneg hGaussian (Real.exp_pos _).le
    have hLowerFactor : 1 - C2 * cubicCost ≤ 1 - C2 * sourceCost0 := by
      linarith only [mul_le_mul_of_nonneg_left hSourceCubic hC2.le]
    have hUpperFactor : 1 + C4 * sourceCost0 ≤ 1 + C4 * cubicCost := by
      linarith only [mul_le_mul_of_nonneg_left hSourceCubic hC4.le]
    have hCubicLower :=
      (sub_le_sub_right (mul_le_mul_of_nonneg_left hLowerFactor hLowerPrefactor)
        (2 * payment)).trans hExact.1
    have hCubicUpper := hExact.2.trans
      (_root_.add_le_add (mul_le_mul_of_nonneg_left hUpperFactor hUpperPrefactor)
        (le_refl (4 * payment)))
    exact ⟨hSourceNonneg, hSourceCubic, hExact.1, hExact.2, hCubicLower, hCubicUpper⟩

end
end Shao.OQ6.OriginalCurrentLevelPhysicalFiniteCostTail
