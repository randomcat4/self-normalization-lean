import Shao.OQ6.NormalizedAnalyticCostLimits
import Shao.OQ6.NormalizedEventTransport
import Shao.OQ4.IntervalConcentration
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.Order.OrderClosed

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Shao.OQ6.NormalizedIntegrableCDFAssembly

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology

universe u

def ScalarShaoZhouFiniteCostCDFInput
    (C : ℝ) : Prop :=
  1 < C ∧
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (ζ : Fin n → Ω → ℝ)
    (F1 F2 FA FB : (Fin n → ℝ) → ℝ)
    (FAdelete FBdelete : ∀ i : Fin n, ({j : Fin n // j ≠ i} → ℝ) → ℝ)
    (hζ : ∀ i : Fin n, Measurable (ζ i))
    (hζindep : iIndepFun ζ ν)
    (hζ2 : ∀ i : Fin n, MemLp (ζ i) 2 ν)
    (hζmean : ∀ i : Fin n, (∫ ω, ζ i ω ∂ν) = 0)
    (hζenergy : (∑ i : Fin n, ∫ ω, (ζ i ω) ^ 2 ∂ν) = 1)
    (hF1 : Measurable[borel (Fin n → ℝ), borel ℝ] F1)
    (hF2 : Measurable[borel (Fin n → ℝ), borel ℝ] F2)
    (hFA : Measurable[borel (Fin n → ℝ), borel ℝ] FA)
    (hFB : Measurable[borel (Fin n → ℝ), borel ℝ] FB)
    (hFAdelete : ∀ i : Fin n,
      Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] (FAdelete i))
    (hFBdelete : ∀ i : Fin n,
      Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] (FBdelete i))
    (z : ℝ),
    let tuple : Ω → (Fin n → ℝ) := fun ω i => ζ i ω
    let D1 : Ω → ℝ := fun ω => F1 (tuple ω)
    let D2 : Ω → ℝ := fun ω => F2 (tuple ω)
    let A : Ω → ℝ := fun ω => FA (tuple ω)
    let B : Ω → ℝ := fun ω => FB (tuple ω)
    let Adelete : Fin n → Ω → ℝ := fun i ω => FAdelete i (fun j => ζ j.1 ω)
    let Bdelete : Fin n → Ω → ℝ := fun i ω => FBdelete i (fun j => ζ j.1 ω)
    let W : Ω → ℝ := fun ω => ∑ i : Fin n, ζ i ω
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ζ i ω) ^ 2)
    let b : Ω → ℝ := fun ω => Real.sqrt (1 + D2 ω)
    let T : Ω → ℝ := fun ω => (W ω + D1 ω) / (V ω * b ω)
    let fullTest : Ω → ℝ := fun ω => A ω + z * B ω
    let compactDeletedTest : Fin n → Ω → ℝ := fun i ω =>
      min |ζ i ω| (1 + z)⁻¹ * (|A ω - Adelete i ω| + z * |B ω - Bdelete i ω|)
    let δcompact : Fin n → ℝ := fun i =>
      ∫ ω, ((1 + z) * ζ i ω) ^ 2 * min |(1 + z) * ζ i ω| 1 ∂ν
    let Lcompact : ℝ := ∑ i : Fin n, δcompact i
    let compactCost : ℝ := Lcompact + (∫ ω, fullTest ω ∂ν) +
      ∑ i : Fin n, ∫ ω, compactDeletedTest i ω ∂ν
    (∀ ω : Ω, 0 ≤ A ω ∧ 0 ≤ B ω) →
    (∀ (i : Fin n) (ω : Ω), 0 ≤ Adelete i ω ∧ 0 ≤ Bdelete i ω) →
    (∀ᵐ ω ∂ν, |D1 ω| ≤ A ω ∧ |D2 ω| ≤ B ω) →
    (∀ᵐ ω ∂ν, 0 < 1 + D2 ω) →
    (∀ᵐ ω ∂ν, 0 < V ω) →
    Integrable fullTest ν →
    (∀ i : Fin n, Integrable (compactDeletedTest i) ν) →
    0 ≤ z →
    |ν.real {ω : Ω | T ω ≤ z} - Shao.OQ4.standardNormalCDF z| ≤ C * compactCost

theorem actual_normalized_integrable_cdf_assembly
    (C : ℝ) (hSZ : ScalarShaoZhouFiniteCostCDFInput.{u} C)
    {Ω : Type u} [MeasurableSpace Ω]
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
    (herr : ∀ (k : ℕ) (i : Fin n) (ω : Ω), |Y k i ω - ξ i ω| ≤ ε k)
    (hηindep : ∀ k : ℕ, iIndepFun
      (Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)) ν)
    (hηpos : ∀ k : ℕ, ∀ᵐ ω ∂ν, 0 < Real.sqrt (∑ i : Fin n,
      (Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k) i ω) ^ 2))
    (hFullFactor : ∀ (k : ℕ) (h : Ω → ℝ), Measurable h →
      ∃ F : (Fin n → ℝ) → ℝ,
        Measurable[borel (Fin n → ℝ), borel ℝ] F ∧
        ∀ ω : Ω, h ω = F (fun i =>
          Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k) i ω))
    (D1 D2 κ A B : Ω → ℝ) (Adelete Bdelete : Fin n → Ω → ℝ)
    (hD1 : Measurable D1) (hD2 : Measurable D2) (hκ : Measurable κ)
    (hA : Measurable A) (hB : Measurable B)
    (hAdelete : ∀ i : Fin n, Measurable (Adelete i))
    (hBdelete : ∀ i : Fin n, Measurable (Bdelete i))
    (hAnonneg : ∀ ω : Ω, 0 ≤ A ω)
    (hBnonneg : ∀ ω : Ω, 0 ≤ B ω)
    (hAdeletenonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ Adelete i ω)
    (hBdeletenonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ Bdelete i ω)
    (hD1A : ∀ ω : Ω, |D1 ω| ≤ A ω)
    (hD2B : ∀ ω : Ω, |D2 ω| ≤ B ω)
    (hD2pos : ∀ᵐ ω ∂ν, 0 < 1 + D2 ω)
    (hAint : Integrable A ν) (hBint : Integrable B ν)
    (hAdeleteint : ∀ i : Fin n, Integrable (Adelete i) ν)
    (hBdeleteint : ∀ i : Fin n, Integrable (Bdelete i) ν)
    (hAdeleteFactor : ∀ (k : ℕ) (i : Fin n),
      ∃ F : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] F ∧
        ∀ ω : Ω, Adelete i ω = F (fun j =>
          Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k) j.1 ω))
    (hBdeleteFactor : ∀ (k : ℕ) (i : Fin n),
      ∃ F : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] F ∧
        ∀ ω : Ω, Bdelete i ω = F (fun j =>
          Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k) j.1 ω))
    (z : ℝ) (hz : 0 ≤ z) :
    let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
    let b : Ω → ℝ := fun ω => Real.sqrt (1 + D2 ω)
    let T : Ω → ℝ := fun ω => if V ω = 0 then κ ω else (W ω + D1 ω) / (V ω * b ω)
    let F : Set Ω := {ω : Ω | W ω + D1 ω ≤ z * V ω * b ω}
    let Z : Set Ω := {ω : Ω | V ω = 0}
    let p0 : ℝ := ν.real Z
    let δcompact : Fin n → ℝ := fun i =>
      ∫ ω, ((1 + z) * ξ i ω) ^ 2 * min |(1 + z) * ξ i ω| 1 ∂ν
    let Lcompact : ℝ := ∑ i : Fin n, δcompact i
    let compactDeletedTest : Fin n → Ω → ℝ := fun i ω =>
      min |ξ i ω| (1 + z)⁻¹ * (|A ω - Adelete i ω| + z * |B ω - Bdelete i ω|)
    let compactCost : ℝ := Lcompact + (∫ ω, A ω + z * B ω ∂ν) +
      ∑ i : Fin n, ∫ ω, compactDeletedTest i ω ∂ν
    |ν.real F - Shao.OQ4.standardNormalCDF z| ≤ C * compactCost ∧
    |ν.real {ω : Ω | T ω ≤ z} - Shao.OQ4.standardNormalCDF z| ≤ C * compactCost + p0 := by
  classical
  let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
  let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
  let b : Ω → ℝ := fun ω => Real.sqrt (1 + D2 ω)
  let T : Ω → ℝ := fun ω => if V ω = 0 then κ ω else (W ω + D1 ω) / (V ω * b ω)
  let F : Set Ω := {ω : Ω | W ω + D1 ω ≤ z * V ω * b ω}
  let Z : Set Ω := {ω : Ω | V ω = 0}
  let p0 : ℝ := ν.real Z
  let δcompact : Fin n → ℝ := fun i =>
    ∫ ω, ((1 + z) * ξ i ω) ^ 2 * min |(1 + z) * ξ i ω| 1 ∂ν
  let Lcompact : ℝ := ∑ i : Fin n, δcompact i
  let compactDeletedTest : Fin n → Ω → ℝ := fun i ω =>
    min |ξ i ω| (1 + z)⁻¹ * (|A ω - Adelete i ω| + z * |B ω - Bdelete i ω|)
  let compactCost : ℝ := Lcompact + (∫ ω, A ω + z * B ω ∂ν) +
    ∑ i : Fin n, ∫ ω, compactDeletedTest i ω ∂ν
  change |ν.real F - Shao.OQ4.standardNormalCDF z| ≤ C * compactCost ∧
    |ν.real {ω : Ω | T ω ≤ z} - Shao.OQ4.standardNormalCDF z| ≤ C * compactCost + p0
  let η : ℕ → Fin n → Ω → ℝ := fun k =>
    Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
  let Wη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, η k i ω
  let Vη : ℕ → Ω → ℝ := fun k ω => Real.sqrt (∑ i : Fin n, (η k i ω) ^ 2)
  let H : Ω → ℝ := fun ω =>
    (1 + V ω) * (Real.sqrt (n : ℝ) + z * Real.sqrt (1 + B ω))
  let ρ : ℕ → ℝ := fun k => 4 * ε k * Real.sqrt (n : ℝ)
  let Dη : ℕ → Ω → ℝ := fun k ω =>
    D1 ω + W ω - Wη k ω + z * b ω * (Vη k ω - V ω)
  let Aε : ℕ → Ω → ℝ := fun k ω => A ω + ρ k * H ω
  let Tη : ℕ → Ω → ℝ := fun k ω => (Wη k ω + Dη k ω) / (Vη k ω * b ω)
  let δcompactη : ℕ → Fin n → ℝ := fun k i =>
    ∫ ω, ((1 + z) * η k i ω) ^ 2 * min |(1 + z) * η k i ω| 1 ∂ν
  let Lcompactη : ℕ → ℝ := fun k => ∑ i : Fin n, δcompactη k i
  let compactDeletedTestη : ℕ → Fin n → Ω → ℝ := fun k i ω =>
    min |η k i ω| (1 + z)⁻¹ * (|Aε k ω - Adelete i ω| + z * |B ω - Bdelete i ω|)
  let compactCostη : ℕ → ℝ := fun k =>
    Lcompactη k + (∫ ω, Aε k ω + z * B ω ∂ν) +
      ∑ i : Fin n, ∫ ω, compactDeletedTestη k i ω ∂ν
  have hcosts :=
    Shao.OQ6.NormalizedAnalyticCostLimits.actual_normalized_remainder_analytic_cost_limits
      ν n hn ξ hξ hξ2 hξmean hξenergy Y hY ε hε hεsmall hεlim herr
      A B Adelete Bdelete hA hB hAdelete hBdelete hAnonneg hBnonneg
      hAdeletenonneg hBdeletenonneg hAint hBint hAdeleteint hBdeleteint z hz
  rcases hcosts with
    ⟨_hHint, hAεspec, _hAεlim, _hfullInt, _hfullηInt, _hdeletedInt,
      _hdeletedηInt, _hcompactInt, hcompactηInt, _hfullDom, _hdeletedDom,
      _hcompactDom, _hfullLim, _hdeletedLim, _hfullRatioLim,
      _hdeletedRatioLim, _hcompactLim, _hsourceCostLim, hcompactCostLim⟩
  have hAεint (k : ℕ) : Integrable (Aε k) ν := (hAεspec k).1
  have hcompactηint (k : ℕ) (i : Fin n) :
      Integrable (compactDeletedTestη k i) ν := hcompactηInt k i
  have hcombined (k : ℕ) :
      (∫ ω, Aε k ω + z * B ω ∂ν) =
        (∫ ω, Aε k ω ∂ν) + z * (∫ ω, B ω ∂ν) := by
    rw [integral_add (hAεint k) (hBint.const_mul z), integral_const_mul]
  have hcombinedOriginal :
      (∫ ω, A ω + z * B ω ∂ν) =
        (∫ ω, A ω ∂ν) + z * (∫ ω, B ω ∂ν) := by
    rw [integral_add hAint (hBint.const_mul z), integral_const_mul]
  have hsplitLim : Filter.Tendsto
      (fun k : ℕ => Lcompactη k + (∫ ω, Aε k ω ∂ν) +
        z * (∫ ω, B ω ∂ν) + ∑ i : Fin n, ∫ ω, compactDeletedTestη k i ω ∂ν)
      Filter.atTop
      (nhds (Lcompact + (∫ ω, A ω ∂ν) + z * (∫ ω, B ω ∂ν) +
        ∑ i : Fin n, ∫ ω, compactDeletedTest i ω ∂ν)) := hcompactCostLim
  have hcostηEq : compactCostη = fun k : ℕ =>
      Lcompactη k + (∫ ω, Aε k ω ∂ν) + z * (∫ ω, B ω ∂ν) +
        ∑ i : Fin n, ∫ ω, compactDeletedTestη k i ω ∂ν := by
    funext k
    dsimp only [compactCostη]
    rw [hcombined k]
    ring
  have hcostEq : compactCost =
      Lcompact + (∫ ω, A ω ∂ν) + z * (∫ ω, B ω ∂ν) +
        ∑ i : Fin n, ∫ ω, compactDeletedTest i ω ∂ν := by
    dsimp only [compactCost]
    rw [hcombinedOriginal]
    ring
  have hcostLim : Filter.Tendsto compactCostη Filter.atTop (nhds compactCost) := by
    rw [hcostηEq, hcostEq]
    exact hsplitLim
  have hremainder (k : ℕ) :
      Measurable (Dη k) ∧ Measurable (Aε k) ∧
        (∀ ω : Ω, |Dη k ω| ≤ Aε k ω) ∧ (∀ ω : Ω, 0 ≤ Aε k ω) := by
    have hr :=
      Shao.OQ6.NormalizedRemainderEnvelope.actual_normalized_remainder_envelope_spec
        ν n hn ξ (Y k) hξ hξ2 hξmean hξenergy (hY k)
        D1 D2 A B Adelete Bdelete hD1 hD2 hA hB hAnonneg hBnonneg
        hD1A hD2B hAint hBint (ε k) (hε k) (hεsmall k) (herr k) z hz
    rcases hr with
      ⟨_hηMeas, _hWMeas, _hWηMeas, _hVMeas, _hVηMeas, _hbMeas,
        _hCMeas, _hHMeas, hDηMeas, hAεMeas, _hBεMeas, _hbBounds,
        _hHPos, _hρPos, _hρLt, _hHInt, _hD1Int, _hDηInt, _hAεInt,
        _hDiffInt, _hAbsDiffInt, _hρHInt, _hAHInt, _hDiffDom,
        hDom, hNonneg, _hADom, _hBDom, _hBEq, _hAdeleteEq,
        _hBdeleteEq, _hAdeleteDiff, _hBdeleteDiff, _hDIntBound,
        _hADiffInt, _hAIntValue⟩
    exact ⟨hDηMeas, hAεMeas, hDom, hNonneg⟩
  have htransport (k : ℕ) :
      ν.real {ω : Ω | Tη k ω ≤ z} = ν.real F ∧
        |ν.real {ω : Ω | T ω ≤ z} - ν.real F| ≤ p0 := by
    have ht :=
      Shao.OQ6.NormalizedEventTransport.actual_normalized_quotient_projection_zero_transport
        ν ξ (Y k) hξ (hY k) D1 D2 κ hD1 hD2 hκ hD2pos (hηpos k)
    rcases ht with
      ⟨_hηMeas, _hWMeas, _hWηMeas, _hVMeas, _hVηMeas, _hbMeas,
        _hDηMeas, _hTMeas, _hTηMeas, _hZMeas, _hAE, _hOriginal,
        hComparisons⟩
    have hclosed := hComparisons z (fun a b : ℝ => a ≤ b) (Or.inl rfl)
    rcases hclosed with
      ⟨_hFMeas, _hAMeas, _hEMeas, hEF, _hAFAE, _hAFMeasure,
        hAFReal, _hAEMeasure, _hAEReal⟩
    have hEF' : ν {ω : Ω | Tη k ω ≤ z} = ν F := hEF
    have hEFReal : ν.real {ω : Ω | Tη k ω ≤ z} = ν.real F := by
      change (ν {ω : Ω | Tη k ω ≤ z}).toReal = (ν F).toReal
      exact congrArg ENNReal.toReal hEF'
    exact ⟨hEFReal, hAFReal⟩
  have hcodedBound (k : ℕ) :
      |ν.real F - Shao.OQ4.standardNormalCDF z| ≤ C * compactCostη k := by
    have hm := Shao.OQ6.ActualMomentNormalization.actual_moment_normalization_spec
      ν n hn ξ (Y k) hξ hξ2 hξmean hξenergy (hY k)
      (ε k) (hε k) (hεsmall k) (herr k)
    rcases hm with
      ⟨_hsPos, hηMeas, hηL2, _hηInt, _hηSqInt, hηMean, hηEnergy,
        _hRecovery, _hVectorError, _hVError, _hWError, _hCoordinateBound,
        _hCoordinateError⟩
    rcases hremainder k with ⟨hDηMeas, hAεMeas, hDom, hNonneg⟩
    rcases hFullFactor k (Dη k) hDηMeas with ⟨F1, hF1, hF1point⟩
    rcases hFullFactor k D2 hD2 with ⟨F2, hF2, hF2point⟩
    rcases hFullFactor k (Aε k) hAεMeas with ⟨FA, hFA, hFApoint⟩
    rcases hFullFactor k B hB with ⟨FB, hFB, hFBpoint⟩
    change ∀ ω : Ω, Dη k ω = F1 (fun i => η k i ω) at hF1point
    change ∀ ω : Ω, D2 ω = F2 (fun i => η k i ω) at hF2point
    change ∀ ω : Ω, Aε k ω = FA (fun i => η k i ω) at hFApoint
    change ∀ ω : Ω, B ω = FB (fun i => η k i ω) at hFBpoint
    let FAdelete : ∀ i : Fin n, ({j : Fin n // j ≠ i} → ℝ) → ℝ :=
      fun i => Classical.choose (hAdeleteFactor k i)
    let FBdelete : ∀ i : Fin n, ({j : Fin n // j ≠ i} → ℝ) → ℝ :=
      fun i => Classical.choose (hBdeleteFactor k i)
    have hFAdelete : ∀ i : Fin n,
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] (FAdelete i) :=
      fun i => (Classical.choose_spec (hAdeleteFactor k i)).1
    have hFBdelete : ∀ i : Fin n,
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] (FBdelete i) :=
      fun i => (Classical.choose_spec (hBdeleteFactor k i)).1
    have hFAdeletepoint : ∀ (i : Fin n) (ω : Ω),
        Adelete i ω = FAdelete i (fun j => η k j.1 ω) :=
      fun i ω => (Classical.choose_spec (hAdeleteFactor k i)).2 ω
    have hFBdeletepoint : ∀ (i : Fin n) (ω : Ω),
        Bdelete i ω = FBdelete i (fun j => η k j.1 ω) :=
      fun i ω => (Classical.choose_spec (hBdeleteFactor k i)).2 ω
    have hscalar := hSZ.2 ν n hn (η k) F1 F2 FA FB FAdelete FBdelete
      hηMeas (hηindep k) hηL2 hηMean hηEnergy
      hF1 hF2 hFA hFB hFAdelete hFBdelete z
    dsimp only at hscalar
    simp only [← hF1point, ← hF2point, ← hFApoint, ← hFBpoint,
      ← hFAdeletepoint, ← hFBdeletepoint] at hscalar
    have hscalarBound :
        |ν.real {ω : Ω | Tη k ω ≤ z} - Shao.OQ4.standardNormalCDF z| ≤
          C * compactCostη k :=
      hscalar (fun ω => ⟨hNonneg ω, hBnonneg ω⟩)
        (fun i ω => ⟨hAdeletenonneg i ω, hBdeletenonneg i ω⟩)
        (Filter.Eventually.of_forall (fun ω => ⟨hDom ω, hD2B ω⟩))
        hD2pos (hηpos k) ((hAεint k).add (hBint.const_mul z))
        (hcompactηint k) hz
    simpa only [(htransport k).1] using hscalarBound
  have hboundLim : Filter.Tendsto (fun k : ℕ => C * compactCostη k)
      Filter.atTop (nhds (C * compactCost)) := tendsto_const_nhds.mul hcostLim
  have hconstant : Filter.Tendsto
      (fun _ : ℕ => |ν.real F - Shao.OQ4.standardNormalCDF z|)
      Filter.atTop (nhds |ν.real F - Shao.OQ4.standardNormalCDF z|) := tendsto_const_nhds
  have hbound : |ν.real F - Shao.OQ4.standardNormalCDF z| ≤ C * compactCost :=
    le_of_tendsto_of_tendsto hconstant hboundLim (Filter.Eventually.of_forall hcodedBound)
  refine ⟨hbound, ?_⟩
  calc
    |ν.real {ω : Ω | T ω ≤ z} - Shao.OQ4.standardNormalCDF z| =
        |(ν.real {ω : Ω | T ω ≤ z} - ν.real F) +
          (ν.real F - Shao.OQ4.standardNormalCDF z)| := by congr 1 <;> ring
    _ ≤ |ν.real {ω : Ω | T ω ≤ z} - ν.real F| +
        |ν.real F - Shao.OQ4.standardNormalCDF z| := abs_add_le _ _
    _ ≤ p0 + C * compactCost := add_le_add (htransport 0).2 hbound
    _ = C * compactCost + p0 := add_comm _ _

end

end Shao.OQ6.NormalizedIntegrableCDFAssembly
