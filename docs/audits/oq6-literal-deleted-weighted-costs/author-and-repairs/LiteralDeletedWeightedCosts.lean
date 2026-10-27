import Shao.OQ6.NormalizedAnalyticCostLimits
import Shao.OQ6.LiteralDeletedRemainderEnvelope

set_option autoImplicit false

universe u

namespace Shao.OQ6.LiteralDeletedWeightedCosts

noncomputable section

open MeasureTheory
open scoped BigOperators Classical Topology

theorem literal_deleted_weighted_cost_limits
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω) [hν : IsProbabilityMeasure ν]
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
    (A B : Ω → ℝ) (Adelete Bdelete : Fin n → Ω → ℝ)
    (hA : Measurable A) (hB : Measurable B)
    (hAdelete : ∀ i : Fin n, Measurable (Adelete i))
    (hBdelete : ∀ i : Fin n, Measurable (Bdelete i))
    (hAnonneg : ∀ ω : Ω, 0 ≤ A ω)
    (hBnonneg : ∀ ω : Ω, 0 ≤ B ω)
    (hAdeletenonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ Adelete i ω)
    (hBdeletenonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ Bdelete i ω)
    (hAint : Integrable A ν) (hBint : Integrable B ν)
    (hAdeleteint : ∀ i : Fin n, Integrable (Adelete i) ν)
    (hBdeleteint : ∀ i : Fin n, Integrable (Bdelete i) ν)
    (x : ℝ) (hx : 0 ≤ x) (K : ℝ) (hK : 0 ≤ K) :
    let η : ℕ → Fin n → Ω → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
    let Vdelete : Fin n → Ω → ℝ := fun i ω => Real.sqrt (∑ j ∈ Finset.univ.erase i, (ξ j ω) ^ 2)
    let H : Ω → ℝ := fun ω => (1 + V ω) * (Real.sqrt (n : ℝ) + x * Real.sqrt (1 + B ω))
    let Hdelete : Fin n → Ω → ℝ := fun i ω => (1 + Vdelete i ω) * (Real.sqrt (n : ℝ) + x * Real.sqrt (1 + Bdelete i ω))
    let Anew : ℕ → Ω → ℝ := fun k ω => A ω + K * ε k * H ω
    let AdeleteNew : ℕ → Fin n → Ω → ℝ := fun k i ω => Adelete i ω + K * ε k * Hdelete i ω
    let ℓ : Fin n → Ω → ℝ := fun i ω => x * ξ i ω - (x * ξ i ω) ^ 2 / 2
    let ℓη : ℕ → Fin n → Ω → ℝ := fun k i ω => x * η k i ω - (x * η k i ω) ^ 2 / 2
    let S : Ω → ℝ := fun ω => ∑ i : Fin n, ℓ i ω
    let Sη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, ℓη k i ω
    let Sminus : Fin n → Ω → ℝ := fun i ω => ∑ j ∈ Finset.univ.erase i, ℓ j ω
    let Sηminus : ℕ → Fin n → Ω → ℝ := fun k i ω => ∑ j ∈ Finset.univ.erase i, ℓη k j ω
    let I : ℝ := ∫ ω, Real.exp (S ω) ∂ν
    let Iη : ℕ → ℝ := fun k => ∫ ω, Real.exp (Sη k ω) ∂ν
    let cap : Fin n → Ω → ℝ := fun i ω => min |x * ξ i ω| 1
    let capη : ℕ → Fin n → Ω → ℝ := fun k i ω => min |x * η k i ω| 1
    let compactCap : Fin n → Ω → ℝ := fun i ω => min |ξ i ω| (1 + x)⁻¹
    let compactCapη : ℕ → Fin n → Ω → ℝ := fun k i ω => min |η k i ω| (1 + x)⁻¹
    let fullTest : Ω → ℝ := fun ω => x * A ω + x ^ 2 * B ω
    let fullTestη : ℕ → Ω → ℝ := fun k ω => x * Anew k ω + x ^ 2 * B ω
    let deletedTest : Fin n → Ω → ℝ := fun i ω => cap i ω * (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)
    let deletedTestη : ℕ → Fin n → Ω → ℝ := fun k i ω => capη k i ω * (|Anew k ω - AdeleteNew k i ω| + x * |B ω - Bdelete i ω|)
    let compactDeletedTest : Fin n → Ω → ℝ := fun i ω => compactCap i ω * (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)
    let compactDeletedTestη : ℕ → Fin n → Ω → ℝ := fun k i ω => compactCapη k i ω * (|Anew k ω - AdeleteNew k i ω| + x * |B ω - Bdelete i ω|)
    let δcompact : Fin n → ℝ := fun i => ∫ ω, ((1 + x) * ξ i ω) ^ 2 * min |(1 + x) * ξ i ω| 1 ∂ν
    let δcompactη : ℕ → Fin n → ℝ := fun k i => ∫ ω, ((1 + x) * η k i ω) ^ 2 * min |(1 + x) * η k i ω| 1 ∂ν
    let Lcompact : ℝ := ∑ i : Fin n, δcompact i
    let Lcompactη : ℕ → ℝ := fun k => ∑ i : Fin n, δcompactη k i
    let sourceCost : ℝ := ((∫ ω, fullTest ω * Real.exp (S ω) ∂ν) + ∑ i : Fin n, ∫ ω, deletedTest i ω * Real.exp (Sminus i ω) ∂ν) / I
    let sourceCostη : ℕ → ℝ := fun k => ((∫ ω, fullTestη k ω * Real.exp (Sη k ω) ∂ν) + ∑ i : Fin n, ∫ ω, deletedTestη k i ω * Real.exp (Sηminus k i ω) ∂ν) / Iη k
    let compactCost : ℝ := Lcompact + (∫ ω, A ω ∂ν) + x * (∫ ω, B ω ∂ν) + ∑ i : Fin n, ∫ ω, compactDeletedTest i ω ∂ν
    let compactCostη : ℕ → ℝ := fun k => Lcompactη k + (∫ ω, Anew k ω ∂ν) + x * (∫ ω, B ω ∂ν) + ∑ i : Fin n, ∫ ω, compactDeletedTestη k i ω ∂ν
    Measurable H ∧ Integrable H ν ∧
    (∀ i : Fin n, Measurable (Hdelete i) ∧ Integrable (Hdelete i) ν) ∧
    (∀ ω : Ω, 0 ≤ H ω) ∧
    (∀ (i : Fin n) (ω : Ω), 0 ≤ Hdelete i ω) ∧
    (∀ k : ℕ, Measurable (Anew k) ∧ Integrable (Anew k) ν ∧ ∀ ω : Ω, 0 ≤ Anew k ω) ∧
    (∀ (k : ℕ) (i : Fin n), Measurable (AdeleteNew k i) ∧ Integrable (AdeleteNew k i) ν ∧ ∀ ω : Ω, 0 ≤ AdeleteNew k i ω) ∧
    (∀ k : ℕ, Integrable (fun ω => |Anew k ω - A ω|) ν ∧
      (∫ ω, |Anew k ω - A ω| ∂ν) = |ε k| * (K * (∫ ω, H ω ∂ν))) ∧
    (∀ (k : ℕ) (i : Fin n), Integrable (fun ω => |AdeleteNew k i ω - Adelete i ω|) ν ∧
      (∫ ω, |AdeleteNew k i ω - Adelete i ω| ∂ν) = |ε k| * (K * (∫ ω, Hdelete i ω ∂ν))) ∧
    Filter.Tendsto (fun k : ℕ => ∫ ω, |Anew k ω - A ω| ∂ν) Filter.atTop (nhds (0 : ℝ)) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => ∫ ω, |AdeleteNew k i ω - Adelete i ω| ∂ν) Filter.atTop (nhds (0 : ℝ))) ∧
    Integrable (fun ω => fullTest ω * Real.exp (S ω)) ν ∧
    (∀ k : ℕ, Integrable (fun ω => fullTestη k ω * Real.exp (Sη k ω)) ν) ∧
    (∀ i : Fin n, Integrable (fun ω => deletedTest i ω * Real.exp (Sminus i ω)) ν) ∧
    (∀ (k : ℕ) (i : Fin n), Integrable (fun ω => deletedTestη k i ω * Real.exp (Sηminus k i ω)) ν) ∧
    (∀ i : Fin n, Integrable (compactDeletedTest i) ν) ∧
    (∀ (k : ℕ) (i : Fin n), Integrable (compactDeletedTestη k i) ν) ∧
    0 < I ∧ (∀ k : ℕ, 0 < Iη k) ∧
    Filter.Tendsto Iη Filter.atTop (nhds I) ∧
    Filter.Tendsto (fun k : ℕ => ∫ ω, fullTestη k ω * Real.exp (Sη k ω) ∂ν)
      Filter.atTop (nhds (∫ ω, fullTest ω * Real.exp (S ω) ∂ν)) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => ∫ ω, deletedTestη k i ω * Real.exp (Sηminus k i ω) ∂ν)
      Filter.atTop (nhds (∫ ω, deletedTest i ω * Real.exp (Sminus i ω) ∂ν))) ∧
    Filter.Tendsto (fun k : ℕ => (∫ ω, fullTestη k ω * Real.exp (Sη k ω) ∂ν) / Iη k)
      Filter.atTop (nhds ((∫ ω, fullTest ω * Real.exp (S ω) ∂ν) / I)) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => (∫ ω, deletedTestη k i ω * Real.exp (Sηminus k i ω) ∂ν) / Iη k)
      Filter.atTop (nhds ((∫ ω, deletedTest i ω * Real.exp (Sminus i ω) ∂ν) / I))) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => ∫ ω, compactDeletedTestη k i ω ∂ν)
      Filter.atTop (nhds (∫ ω, compactDeletedTest i ω ∂ν))) ∧
    Filter.Tendsto sourceCostη Filter.atTop (nhds sourceCost) ∧
    Filter.Tendsto compactCostη Filter.atTop (nhds compactCost)
    := by
  classical
  dsimp only
  let η : ℕ → Fin n → Ω → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
  let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
  let Vdelete : Fin n → Ω → ℝ := fun i ω => Real.sqrt (∑ j ∈ Finset.univ.erase i, (ξ j ω) ^ 2)
  let H : Ω → ℝ := fun ω => (1 + V ω) * (Real.sqrt (n : ℝ) + x * Real.sqrt (1 + B ω))
  let Hdelete : Fin n → Ω → ℝ := fun i ω => (1 + Vdelete i ω) * (Real.sqrt (n : ℝ) + x * Real.sqrt (1 + Bdelete i ω))
  let Anew : ℕ → Ω → ℝ := fun k ω => A ω + K * ε k * H ω
  let AdeleteNew : ℕ → Fin n → Ω → ℝ := fun k i ω => Adelete i ω + K * ε k * Hdelete i ω
  let ℓ : Fin n → Ω → ℝ := fun i ω => x * ξ i ω - (x * ξ i ω) ^ 2 / 2
  let ℓη : ℕ → Fin n → Ω → ℝ := fun k i ω => x * η k i ω - (x * η k i ω) ^ 2 / 2
  let S : Ω → ℝ := fun ω => ∑ i : Fin n, ℓ i ω
  let Sη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, ℓη k i ω
  let Sminus : Fin n → Ω → ℝ := fun i ω => ∑ j ∈ Finset.univ.erase i, ℓ j ω
  let Sηminus : ℕ → Fin n → Ω → ℝ := fun k i ω => ∑ j ∈ Finset.univ.erase i, ℓη k j ω
  let I : ℝ := ∫ ω, Real.exp (S ω) ∂ν
  let Iη : ℕ → ℝ := fun k => ∫ ω, Real.exp (Sη k ω) ∂ν
  let cap : Fin n → Ω → ℝ := fun i ω => min |x * ξ i ω| 1
  let capη : ℕ → Fin n → Ω → ℝ := fun k i ω => min |x * η k i ω| 1
  let compactCap : Fin n → Ω → ℝ := fun i ω => min |ξ i ω| (1 + x)⁻¹
  let compactCapη : ℕ → Fin n → Ω → ℝ := fun k i ω => min |η k i ω| (1 + x)⁻¹
  let fullTest : Ω → ℝ := fun ω => x * A ω + x ^ 2 * B ω
  let fullTestη : ℕ → Ω → ℝ := fun k ω => x * Anew k ω + x ^ 2 * B ω
  let deletedTest : Fin n → Ω → ℝ := fun i ω => cap i ω * (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)
  let deletedTestη : ℕ → Fin n → Ω → ℝ := fun k i ω => capη k i ω * (|Anew k ω - AdeleteNew k i ω| + x * |B ω - Bdelete i ω|)
  let compactDeletedTest : Fin n → Ω → ℝ := fun i ω => compactCap i ω * (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)
  let compactDeletedTestη : ℕ → Fin n → Ω → ℝ := fun k i ω => compactCapη k i ω * (|Anew k ω - AdeleteNew k i ω| + x * |B ω - Bdelete i ω|)
  let δcompact : Fin n → ℝ := fun i => ∫ ω, ((1 + x) * ξ i ω) ^ 2 * min |(1 + x) * ξ i ω| 1 ∂ν
  let δcompactη : ℕ → Fin n → ℝ := fun k i => ∫ ω, ((1 + x) * η k i ω) ^ 2 * min |(1 + x) * η k i ω| 1 ∂ν
  let Lcompact : ℝ := ∑ i : Fin n, δcompact i
  let Lcompactη : ℕ → ℝ := fun k => ∑ i : Fin n, δcompactη k i
  let sourceCost : ℝ := ((∫ ω, fullTest ω * Real.exp (S ω) ∂ν) + ∑ i : Fin n, ∫ ω, deletedTest i ω * Real.exp (Sminus i ω) ∂ν) / I
  let sourceCostη : ℕ → ℝ := fun k => ((∫ ω, fullTestη k ω * Real.exp (Sη k ω) ∂ν) + ∑ i : Fin n, ∫ ω, deletedTestη k i ω * Real.exp (Sηminus k i ω) ∂ν) / Iη k
  let compactCost : ℝ := Lcompact + (∫ ω, A ω ∂ν) + x * (∫ ω, B ω ∂ν) + ∑ i : Fin n, ∫ ω, compactDeletedTest i ω ∂ν
  let compactCostη : ℕ → ℝ := fun k => Lcompactη k + (∫ ω, Anew k ω ∂ν) + x * (∫ ω, B ω ∂ν) + ∑ i : Fin n, ∫ ω, compactDeletedTestη k i ω ∂ν
  let c0 : ℝ := 4 * Real.sqrt (n : ℝ)
  let d : ℝ := |K - c0|
  let Aold : ℕ → Ω → ℝ := fun k ω => A ω + (4 * ε k * Real.sqrt (n : ℝ)) * H ω
  let fullOld : ℕ → Ω → ℝ := fun k ω => x * Aold k ω + x ^ 2 * B ω
  let deletedOld : ℕ → Fin n → Ω → ℝ := fun k i ω =>
    capη k i ω * (|Aold k ω - Adelete i ω| + x * |B ω - Bdelete i ω|)
  let compactOld : ℕ → Fin n → Ω → ℝ := fun k i ω =>
    compactCapη k i ω * (|Aold k ω - Adelete i ω| + x * |B ω - Bdelete i ω|)
  let F0 : Ω → ℝ := fun ω => fullTest ω * Real.exp (S ω)
  let Fo : ℕ → Ω → ℝ := fun k ω => fullOld k ω * Real.exp (Sη k ω)
  let Fn : ℕ → Ω → ℝ := fun k ω => fullTestη k ω * Real.exp (Sη k ω)
  let D0 : Fin n → Ω → ℝ := fun i ω => deletedTest i ω * Real.exp (Sminus i ω)
  let Do : ℕ → Fin n → Ω → ℝ := fun k i ω => deletedOld k i ω * Real.exp (Sηminus k i ω)
  let Dn : ℕ → Fin n → Ω → ℝ := fun k i ω => deletedTestη k i ω * Real.exp (Sηminus k i ω)
  let C0 : Fin n → Ω → ℝ := compactDeletedTest
  let Co : ℕ → Fin n → Ω → ℝ := compactOld
  let Cn : ℕ → Fin n → Ω → ℝ := compactDeletedTestη
  let Efull : ℝ := Real.exp ((n : ℝ) / 2)
  let Edel : ℝ := Real.exp (((n - 1 : ℕ) : ℝ) / 2)
  let b : ℝ := (1 + x)⁻¹
  let P : Fin n → Ω → ℝ := fun i ω => d * H ω + K * Hdelete i ω
  let Qfull : Ω → ℝ := fun ω => Efull * (x * d * H ω)
  let Qdel : Fin n → Ω → ℝ := fun i ω => Edel * P i ω
  let Qcompact : Fin n → Ω → ℝ := fun i ω => b * P i ω
  let mH : ℝ := ∫ ω, H ω ∂ν
  let mHdelete : Fin n → ℝ := fun i => ∫ ω, Hdelete i ω ∂ν
  let Cfull : ℝ := Efull * (x * d * mH)
  let Cdel : Fin n → ℝ := fun i => Edel * (d * mH + K * mHdelete i)
  let Ccompact : Fin n → ℝ := fun i => b * (d * mH + K * mHdelete i)
  let compactCostOld : ℕ → ℝ := fun k =>
    Lcompactη k + (∫ ω, Aold k ω ∂ν) + x * (∫ ω, B ω ∂ν) +
      ∑ i : Fin n, ∫ ω, Co k i ω ∂ν
  let CcompactTotal : ℝ := d * mH + ∑ i : Fin n, Ccompact i
  have hOld :=
    Shao.OQ6.NormalizedAnalyticCostLimits.actual_normalized_remainder_analytic_cost_limits
      ν n hn ξ hξ hξ2 hξmean hξenergy Y hY ε hε hεsmall hεlim herr
      A B Adelete Bdelete hA hB hAdelete hBdelete
      hAnonneg hBnonneg hAdeletenonneg hBdeletenonneg
      hAint hBint hAdeleteint hBdeleteint x hx
  rcases hOld with
    ⟨hOldHint, hAoldSpec, hAoldL1zero,
      hF0I, hFoI, hD0I, hDoI, hC0I, hCoI,
      hOldFullDom, hOldDelDom, hOldCompactDom,
      hFoLim, hDoLim, hFoRatio, hDoRatio, hCoLim,
      hOldSourceLim, hOldCompactLim⟩
  have h225 :=
    Shao.OQ6.LiteralDeletedRemainderEnvelope.literal_deleted_remainder_envelope_spec
      ν n hn ξ hξ hξ2 hξenergy B Bdelete hB hBdelete
      hBnonneg hBdeletenonneg hBint hBdeleteint x hx
  rcases h225 with
    ⟨_, _, _, _, _, _, _, hHm, hHint, hHdeleteSpec, hHpos, hHdeletePos, _⟩
  have hProj :=
    Shao.OQ6.NormalizedAnalyticCostLimits.actual_projection_tilt_and_truncated_cost_limits
      ν n hn ξ hξ hξ2 hξmean hξenergy Y hY ε hε hεsmall hεlim herr x
  rcases hProj with
    ⟨_, _, _, hIpos, hIηSpec, _, _, hSB, hSBη, hJB, hJBη, _, _, _, _, hIlim, _⟩
  have hHnonneg : ∀ ω : Ω, 0 ≤ H ω := fun ω => (hHpos ω).le
  have hHdnonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ Hdelete i ω :=
    fun i ω => (hHdeletePos i ω).le
  have hηm : ∀ (k : ℕ) (i : Fin n), Measurable (η k i) := by
    intro k i
    change Measurable (fun ω : Ω =>
      (Y k i ω - Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν (Y k) i) /
        Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν (Y k))
    exact ((hY k i).sub measurable_const).div_const _
  have hAnewM : ∀ k : ℕ, Measurable (Anew k) := by
    intro k
    exact hA.add (measurable_const.mul hHm)
  have hAdnewM : ∀ (k : ℕ) (i : Fin n), Measurable (AdeleteNew k i) := by
    intro k i
    exact (hAdelete i).add (measurable_const.mul (hHdeleteSpec i).1)
  have hAoldM : ∀ k : ℕ, Measurable (Aold k) := by
    intro k
    exact hA.add (measurable_const.mul hHm)
  have hSηm : ∀ k : ℕ, Measurable (Sη k) := by
    intro k
    exact Finset.measurable_sum Finset.univ (fun i _ =>
      (measurable_const.mul (hηm k i)).sub
        (((measurable_const.mul (hηm k i)).pow_const 2).div_const 2))
  have hSmηm : ∀ (k : ℕ) (i : Fin n), Measurable (Sηminus k i) := by
    intro k i
    exact Finset.measurable_sum (Finset.univ.erase i) (fun j _ =>
      (measurable_const.mul (hηm k j)).sub
        (((measurable_const.mul (hηm k j)).pow_const 2).div_const 2))
  have hcapηm : ∀ (k : ℕ) (i : Fin n), Measurable (capη k i) := by
    intro k i
    exact ((measurable_const.mul (hηm k i)).abs).min measurable_const
  have hcompactCapηm : ∀ (k : ℕ) (i : Fin n), Measurable (compactCapη k i) := by
    intro k i
    exact (hηm k i).abs.min measurable_const
  have hFoM : ∀ k : ℕ, Measurable (Fo k) := by
    intro k
    exact ((measurable_const.mul (hAoldM k)).add
      (measurable_const.mul hB)).mul (hSηm k).exp
  have hFnM : ∀ k : ℕ, Measurable (Fn k) := by
    intro k
    exact ((measurable_const.mul (hAnewM k)).add
      (measurable_const.mul hB)).mul (hSηm k).exp
  have hDoM : ∀ (k : ℕ) (i : Fin n), Measurable (Do k i) := by
    intro k i
    exact ((hcapηm k i).mul (((hAoldM k).sub (hAdelete i)).abs.add
      (measurable_const.mul ((hB.sub (hBdelete i)).abs)))).mul (hSmηm k i).exp
  have hDnM : ∀ (k : ℕ) (i : Fin n), Measurable (Dn k i) := by
    intro k i
    exact ((hcapηm k i).mul (((hAnewM k).sub (hAdnewM k i)).abs.add
      (measurable_const.mul ((hB.sub (hBdelete i)).abs)))).mul (hSmηm k i).exp
  have hCoM : ∀ (k : ℕ) (i : Fin n), Measurable (Co k i) := by
    intro k i
    exact (hcompactCapηm k i).mul (((hAoldM k).sub (hAdelete i)).abs.add
      (measurable_const.mul ((hB.sub (hBdelete i)).abs)))
  have hCnM : ∀ (k : ℕ) (i : Fin n), Measurable (Cn k i) := by
    intro k i
    exact (hcompactCapηm k i).mul (((hAnewM k).sub (hAdnewM k i)).abs.add
      (measurable_const.mul ((hB.sub (hBdelete i)).abs)))
  have hd : 0 ≤ d := abs_nonneg _
  have hb : 0 ≤ b := inv_nonneg.mpr (by linarith)
  have hPI : ∀ i : Fin n, Integrable (P i) ν := fun i =>
    (hHint.const_mul d).add ((hHdeleteSpec i).2.const_mul K)
  have hPnonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ P i ω := fun i ω =>
    add_nonneg (mul_nonneg hd (hHnonneg ω)) (mul_nonneg hK (hHdnonneg i ω))
  have hQfullI : Integrable Qfull ν := (hHint.const_mul (x * d)).const_mul Efull
  have hQdelI : ∀ i : Fin n, Integrable (Qdel i) ν := fun i => (hPI i).const_mul Edel
  have hQcompactI : ∀ i : Fin n, Integrable (Qcompact i) ν := fun i => (hPI i).const_mul b
  have hQfullNonneg : ∀ ω : Ω, 0 ≤ Qfull ω := fun ω =>
    mul_nonneg (Real.exp_pos _).le (mul_nonneg (mul_nonneg hx hd) (hHnonneg ω))
  have hQdelNonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ Qdel i ω := fun i ω =>
    mul_nonneg (Real.exp_pos _).le (hPnonneg i ω)
  have hQcompactNonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ Qcompact i ω := fun i ω =>
    mul_nonneg hb (hPnonneg i ω)
  have hmH : 0 ≤ mH := integral_nonneg hHnonneg
  have hmHdelete : ∀ i : Fin n, 0 ≤ mHdelete i := fun i => integral_nonneg (hHdnonneg i)
  have hCfull : 0 ≤ Cfull :=
    mul_nonneg (Real.exp_pos _).le (mul_nonneg (mul_nonneg hx hd) hmH)
  have hCdel : ∀ i : Fin n, 0 ≤ Cdel i := fun i =>
    mul_nonneg (Real.exp_pos _).le (add_nonneg (mul_nonneg hd hmH) (mul_nonneg hK (hmHdelete i)))
  have hCcompact : ∀ i : Fin n, 0 ≤ Ccompact i := fun i =>
    mul_nonneg hb (add_nonneg (mul_nonneg hd hmH) (mul_nonneg hK (hmHdelete i)))
  have hCcompactTotal : 0 ≤ CcompactTotal :=
    add_nonneg (mul_nonneg hd hmH) (Finset.sum_nonneg (fun i _ => hCcompact i))
  have hQfullIntegral : (∫ ω, Qfull ω ∂ν) = Cfull := by
    dsimp only [Qfull, Cfull, mH]
    rw [integral_const_mul, integral_const_mul]
  have hQdelIntegral : ∀ i : Fin n, (∫ ω, Qdel i ω ∂ν) = Cdel i := by
    intro i
    dsimp only [Qdel, Cdel, P, mH, mHdelete]
    rw [integral_const_mul, integral_add (hHint.const_mul d) ((hHdeleteSpec i).2.const_mul K),
      integral_const_mul, integral_const_mul]
  have hQcompactIntegral : ∀ i : Fin n, (∫ ω, Qcompact i ω ∂ν) = Ccompact i := by
    intro i
    dsimp only [Qcompact, Ccompact, P, mH, mHdelete]
    rw [integral_const_mul, integral_add (hHint.const_mul d) ((hHdeleteSpec i).2.const_mul K),
      integral_const_mul, integral_const_mul]
  have hAcompare : ∀ (k : ℕ) (ω : Ω),
      |Anew k ω - Aold k ω| = |ε k| * (d * H ω) := by
    intro k ω
    have heq : Anew k ω - Aold k ω = ε k * ((K - c0) * H ω) := by
      dsimp only [Anew, Aold, c0]
      ring
    rw [heq, abs_mul, abs_mul, abs_of_nonneg (hHnonneg ω)]
  have hFeeCompare : ∀ (k : ℕ) (i : Fin n) (ω : Ω),
      ||Anew k ω - AdeleteNew k i ω| - |Aold k ω - Adelete i ω|| ≤ |ε k| * P i ω := by
    intro k i ω
    have heq : (Anew k ω - AdeleteNew k i ω) - (Aold k ω - Adelete i ω) =
        ε k * ((K - c0) * H ω - K * Hdelete i ω) := by
      dsimp only [Anew, AdeleteNew, Aold, c0]
      ring
    calc
      ||Anew k ω - AdeleteNew k i ω| - |Aold k ω - Adelete i ω|| ≤
          |(Anew k ω - AdeleteNew k i ω) - (Aold k ω - Adelete i ω)| :=
        abs_abs_sub_abs_le_abs_sub _ _
      _ = |ε k| * |(K - c0) * H ω - K * Hdelete i ω| := by rw [heq, abs_mul]
      _ ≤ |ε k| * (|(K - c0) * H ω| + |K * Hdelete i ω|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
      _ = |ε k| * P i ω := by
        rw [abs_mul, abs_mul, abs_of_nonneg (hHnonneg ω), abs_of_nonneg hK,
          abs_of_nonneg (hHdnonneg i ω)]
  have hcapBounds : ∀ (k : ℕ) (i : Fin n) (ω : Ω),
      0 ≤ capη k i ω ∧ capη k i ω ≤ 1 := by
    intro k i ω
    exact ⟨le_min (abs_nonneg _) (by norm_num), min_le_right _ _⟩
  have hcompactCapBounds : ∀ (k : ℕ) (i : Fin n) (ω : Ω),
      0 ≤ compactCapη k i ω ∧ compactCapη k i ω ≤ b := by
    intro k i ω
    exact ⟨le_min (abs_nonneg _) hb, min_le_right _ _⟩
  have hFullCompare : ∀ (k : ℕ) (ω : Ω),
      |Fn k ω - Fo k ω| ≤ |ε k| * Qfull ω := by
    intro k ω
    have heq : Fn k ω - Fo k ω =
        x * (Anew k ω - Aold k ω) * Real.exp (Sη k ω) := by
      dsimp only [Fn, Fo, fullTestη, fullOld]
      ring
    calc
      |Fn k ω - Fo k ω| = x * |Anew k ω - Aold k ω| * Real.exp (Sη k ω) := by
        rw [heq, abs_mul, abs_mul, abs_of_nonneg hx, abs_of_pos (Real.exp_pos _)]
      _ ≤ x * |Anew k ω - Aold k ω| * Efull :=
        mul_le_mul_of_nonneg_left (hSBη k ω) (mul_nonneg hx (abs_nonneg _))
      _ = |ε k| * Qfull ω := by rw [hAcompare]; dsimp only [Qfull]; ring
  have hDelCompare : ∀ (k : ℕ) (i : Fin n) (ω : Ω),
      |Dn k i ω - Do k i ω| ≤ |ε k| * Qdel i ω := by
    intro k i ω
    have heq : Dn k i ω - Do k i ω =
        capη k i ω * (|Anew k ω - AdeleteNew k i ω| - |Aold k ω - Adelete i ω|) *
          Real.exp (Sηminus k i ω) := by
      dsimp only [Dn, Do, deletedTestη, deletedOld]
      ring
    calc
      |Dn k i ω - Do k i ω| =
          capη k i ω * ||Anew k ω - AdeleteNew k i ω| - |Aold k ω - Adelete i ω|| *
            Real.exp (Sηminus k i ω) := by
        rw [heq, abs_mul, abs_mul, abs_of_nonneg (hcapBounds k i ω).1,
          abs_of_pos (Real.exp_pos _)]
      _ ≤ capη k i ω * (|ε k| * P i ω) * Real.exp (Sηminus k i ω) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hFeeCompare k i ω) (hcapBounds k i ω).1)
          (Real.exp_pos _).le
      _ ≤ 1 * (|ε k| * P i ω) * Real.exp (Sηminus k i ω) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hcapBounds k i ω).2
            (mul_nonneg (abs_nonneg _) (hPnonneg i ω))) (Real.exp_pos _).le
      _ ≤ 1 * (|ε k| * P i ω) * Edel :=
        mul_le_mul_of_nonneg_left (hJBη k i ω)
          (mul_nonneg (by norm_num) (mul_nonneg (abs_nonneg _) (hPnonneg i ω)))
      _ = |ε k| * Qdel i ω := by dsimp only [Qdel]; ring
  have hCompactCompare : ∀ (k : ℕ) (i : Fin n) (ω : Ω),
      |Cn k i ω - Co k i ω| ≤ |ε k| * Qcompact i ω := by
    intro k i ω
    have heq : Cn k i ω - Co k i ω =
        compactCapη k i ω *
          (|Anew k ω - AdeleteNew k i ω| - |Aold k ω - Adelete i ω|) := by
      dsimp only [Cn, Co, compactOld, compactDeletedTestη]
      ring
    calc
      |Cn k i ω - Co k i ω| =
          compactCapη k i ω * ||Anew k ω - AdeleteNew k i ω| - |Aold k ω - Adelete i ω|| := by
        rw [heq, abs_mul, abs_of_nonneg (hcompactCapBounds k i ω).1]
      _ ≤ compactCapη k i ω * (|ε k| * P i ω) :=
        mul_le_mul_of_nonneg_left (hFeeCompare k i ω) (hcompactCapBounds k i ω).1
      _ ≤ b * (|ε k| * P i ω) :=
        mul_le_mul_of_nonneg_right (hcompactCapBounds k i ω).2
          (mul_nonneg (abs_nonneg _) (hPnonneg i ω))
      _ = |ε k| * Qcompact i ω := by dsimp only [Qcompact]; ring
  have hPerturb : ∀ (f g Q : Ω → ℝ) (r : ℝ),
      Measurable f → Measurable g → Integrable g ν →
      Integrable Q ν → (∀ ω : Ω, 0 ≤ Q ω) → 0 ≤ r →
      (∀ ω : Ω, |f ω - g ω| ≤ r * Q ω) →
      Integrable f ν ∧
      Integrable (fun ω : Ω => |f ω - g ω|) ν ∧
      (∫ ω, |f ω - g ω| ∂ν) ≤ r * (∫ ω, Q ω ∂ν) ∧
      |(∫ ω, f ω ∂ν) - (∫ ω, g ω ∂ν)| ≤ r * (∫ ω, Q ω ∂ν) := by
    intro f g Q r hfm hgm hgI hQI hQnonneg hr hbound
    have hdiffI : Integrable (fun ω : Ω => f ω - g ω) ν := by
      apply (hQI.const_mul r).mono' (hfm.sub hgm).aestronglyMeasurable
      exact Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs] using hbound ω
    have hfI : Integrable f ν := by
      simpa only [sub_add_cancel] using hdiffI.add hgI
    have hdiffAbsI : Integrable (fun ω : Ω => |f ω - g ω|) ν := hdiffI.abs
    have hAbsBound : (∫ ω, |f ω - g ω| ∂ν) ≤ r * (∫ ω, Q ω ∂ν) := by
      calc
        (∫ ω, |f ω - g ω| ∂ν) ≤ ∫ ω, r * Q ω ∂ν :=
          integral_mono hdiffAbsI (hQI.const_mul r) hbound
        _ = r * (∫ ω, Q ω ∂ν) := integral_const_mul r Q
    refine ⟨hfI, hdiffAbsI, hAbsBound, ?_⟩
    rw [← integral_sub hfI hgI]
    have hnorm : |∫ ω, f ω - g ω ∂ν| ≤ ∫ ω, |f ω - g ω| ∂ν := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := ν) (fun ω : Ω => f ω - g ω))
    exact hnorm.trans hAbsBound
  have hFullPerturb : ∀ k : ℕ, Integrable (Fn k) ν ∧
      Integrable (fun ω : Ω => |Fn k ω - Fo k ω|) ν ∧
      (∫ ω, |Fn k ω - Fo k ω| ∂ν) ≤ |ε k| * Cfull ∧
      |(∫ ω, Fn k ω ∂ν) - (∫ ω, Fo k ω ∂ν)| ≤ |ε k| * Cfull := by
    intro k
    simpa only [hQfullIntegral] using
      hPerturb (Fn k) (Fo k) Qfull |ε k|
        (hFnM k) (hFoM k) (hFoI k) hQfullI hQfullNonneg (abs_nonneg _) (hFullCompare k)
  have hDelPerturb : ∀ (k : ℕ) (i : Fin n), Integrable (Dn k i) ν ∧
      Integrable (fun ω : Ω => |Dn k i ω - Do k i ω|) ν ∧
      (∫ ω, |Dn k i ω - Do k i ω| ∂ν) ≤ |ε k| * Cdel i ∧
      |(∫ ω, Dn k i ω ∂ν) - (∫ ω, Do k i ω ∂ν)| ≤ |ε k| * Cdel i := by
    intro k i
    simpa only [hQdelIntegral i] using
      hPerturb (Dn k i) (Do k i) (Qdel i) |ε k|
        (hDnM k i) (hDoM k i) (hDoI k i) (hQdelI i)
        (hQdelNonneg i) (abs_nonneg _) (hDelCompare k i)
  have hCompactPerturb : ∀ (k : ℕ) (i : Fin n), Integrable (Cn k i) ν ∧
      Integrable (fun ω : Ω => |Cn k i ω - Co k i ω|) ν ∧
      (∫ ω, |Cn k i ω - Co k i ω| ∂ν) ≤ |ε k| * Ccompact i ∧
      |(∫ ω, Cn k i ω ∂ν) - (∫ ω, Co k i ω ∂ν)| ≤ |ε k| * Ccompact i := by
    intro k i
    simpa only [hQcompactIntegral i] using
      hPerturb (Cn k i) (Co k i) (Qcompact i) |ε k|
        (hCnM k i) (hCoM k i) (hCoI k i) (hQcompactI i)
        (hQcompactNonneg i) (abs_nonneg _) (hCompactCompare k i)
  have hFnI : ∀ k : ℕ, Integrable (Fn k) ν := fun k => (hFullPerturb k).1
  have hDnI : ∀ (k : ℕ) (i : Fin n), Integrable (Dn k i) ν := fun k i => (hDelPerturb k i).1
  have hCnI : ∀ (k : ℕ) (i : Fin n), Integrable (Cn k i) ν := fun k i => (hCompactPerturb k i).1
  have hFullL1Error : ∀ k : ℕ, Integrable (fun ω : Ω => |Fn k ω - Fo k ω|) ν ∧
      (∫ ω, |Fn k ω - Fo k ω| ∂ν) ≤ |ε k| * Cfull :=
    fun k => ⟨(hFullPerturb k).2.1, (hFullPerturb k).2.2.1⟩
  have hDelL1Error : ∀ (k : ℕ) (i : Fin n), Integrable (fun ω : Ω => |Dn k i ω - Do k i ω|) ν ∧
      (∫ ω, |Dn k i ω - Do k i ω| ∂ν) ≤ |ε k| * Cdel i :=
    fun k i => ⟨(hDelPerturb k i).2.1, (hDelPerturb k i).2.2.1⟩
  have hCompactL1Error : ∀ (k : ℕ) (i : Fin n), Integrable (fun ω : Ω => |Cn k i ω - Co k i ω|) ν ∧
      (∫ ω, |Cn k i ω - Co k i ω| ∂ν) ≤ |ε k| * Ccompact i :=
    fun k i => ⟨(hCompactPerturb k i).2.1, (hCompactPerturb k i).2.2.1⟩
  have hFullIntegralError : ∀ k : ℕ,
      |(∫ ω, Fn k ω ∂ν) - (∫ ω, Fo k ω ∂ν)| ≤ |ε k| * Cfull :=
    fun k => (hFullPerturb k).2.2.2
  have hDelIntegralError : ∀ (k : ℕ) (i : Fin n),
      |(∫ ω, Dn k i ω ∂ν) - (∫ ω, Do k i ω ∂ν)| ≤ |ε k| * Cdel i :=
    fun k i => (hDelPerturb k i).2.2.2
  have hCompactIntegralError : ∀ (k : ℕ) (i : Fin n),
      |(∫ ω, Cn k i ω ∂ν) - (∫ ω, Co k i ω ∂ν)| ≤ |ε k| * Ccompact i :=
    fun k i => (hCompactPerturb k i).2.2.2
  have hAoldNewIntegralError : ∀ k : ℕ,
      |(∫ ω, Anew k ω ∂ν) - (∫ ω, Aold k ω ∂ν)| ≤ |ε k| * (d * mH) := by
    intro k
    have h := hPerturb (Anew k) (Aold k) (fun ω : Ω => d * H ω) |ε k|
      (hAnewM k) (hAoldM k) (hAoldSpec k).1 (hHint.const_mul d)
      (fun ω : Ω => mul_nonneg hd (hHnonneg ω)) (abs_nonneg _)
      (fun ω : Ω => (hAcompare k ω).le)
    simpa only [integral_const_mul, mH] using h.2.2.2
  have hAbsEps : Filter.Tendsto (fun k : ℕ => |ε k|) Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [abs_zero] using hεlim.abs
  have hFullErrorZero : Filter.Tendsto
      (fun k : ℕ => ∫ ω, |Fn k ω - Fo k ω| ∂ν) Filter.atTop (nhds (0 : ℝ)) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun k => integral_nonneg (fun ω => abs_nonneg _))
      (Filter.Eventually.of_forall fun k => (hFullL1Error k).2)
    simpa only [zero_mul] using hAbsEps.mul_const Cfull
  have hDelErrorZero : ∀ i : Fin n, Filter.Tendsto
      (fun k : ℕ => ∫ ω, |Dn k i ω - Do k i ω| ∂ν) Filter.atTop (nhds (0 : ℝ)) := by
    intro i
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun k => integral_nonneg (fun ω => abs_nonneg _))
      (Filter.Eventually.of_forall fun k => (hDelL1Error k i).2)
    simpa only [zero_mul] using hAbsEps.mul_const (Cdel i)
  have hCompactErrorZero : ∀ i : Fin n, Filter.Tendsto
      (fun k : ℕ => ∫ ω, |Cn k i ω - Co k i ω| ∂ν) Filter.atTop (nhds (0 : ℝ)) := by
    intro i
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun k => integral_nonneg (fun ω => abs_nonneg _))
      (Filter.Eventually.of_forall fun k => (hCompactL1Error k i).2)
    simpa only [zero_mul] using hAbsEps.mul_const (Ccompact i)
  have hAnewI : ∀ k : ℕ, Integrable (Anew k) ν := fun k =>
    hAint.add (hHint.const_mul (K * ε k))
  have hAdnewI : ∀ (k : ℕ) (i : Fin n), Integrable (AdeleteNew k i) ν := fun k i =>
    (hAdeleteint i).add ((hHdeleteSpec i).2.const_mul (K * ε k))
  have hAnewNonneg : ∀ (k : ℕ) (ω : Ω), 0 ≤ Anew k ω := fun k ω =>
    add_nonneg (hAnonneg ω) (mul_nonneg (mul_nonneg hK (hε k).le) (hHnonneg ω))
  have hAdnewNonneg : ∀ (k : ℕ) (i : Fin n) (ω : Ω), 0 ≤ AdeleteNew k i ω := fun k i ω =>
    add_nonneg (hAdeletenonneg i ω) (mul_nonneg (mul_nonneg hK (hε k).le) (hHdnonneg i ω))
  have hAnewAbsSpec : ∀ k : ℕ, Integrable (fun ω => |Anew k ω - A ω|) ν ∧
      (∫ ω, |Anew k ω - A ω| ∂ν) = |ε k| * (K * mH) := by
    intro k
    refine ⟨((hAnewI k).sub hAint).abs, ?_⟩
    calc
      (∫ ω, |Anew k ω - A ω| ∂ν) = ∫ ω, |ε k| * (K * H ω) ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => by
          have heq : Anew k ω - A ω = K * ε k * H ω := by dsimp only [Anew]; ring
          rw [heq, abs_mul, abs_mul, abs_of_nonneg hK, abs_of_nonneg (hHnonneg ω)]
          ring
      _ = |ε k| * (K * mH) := by rw [integral_const_mul, integral_const_mul]
  have hAdnewAbsSpec : ∀ (k : ℕ) (i : Fin n),
      Integrable (fun ω => |AdeleteNew k i ω - Adelete i ω|) ν ∧
      (∫ ω, |AdeleteNew k i ω - Adelete i ω| ∂ν) = |ε k| * (K * mHdelete i) := by
    intro k i
    refine ⟨((hAdnewI k i).sub (hAdeleteint i)).abs, ?_⟩
    calc
      (∫ ω, |AdeleteNew k i ω - Adelete i ω| ∂ν) = ∫ ω, |ε k| * (K * Hdelete i ω) ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => by
          have heq : AdeleteNew k i ω - Adelete i ω = K * ε k * Hdelete i ω := by
            dsimp only [AdeleteNew]
            ring
          rw [heq, abs_mul, abs_mul, abs_of_nonneg hK, abs_of_nonneg (hHdnonneg i ω)]
          ring
      _ = |ε k| * (K * mHdelete i) := by rw [integral_const_mul, integral_const_mul]
  have hAnewZero : Filter.Tendsto (fun k : ℕ => ∫ ω, |Anew k ω - A ω| ∂ν)
      Filter.atTop (nhds (0 : ℝ)) := by
    have heq : (fun k : ℕ => ∫ ω, |Anew k ω - A ω| ∂ν) =
        (fun k : ℕ => |ε k| * (K * mH)) := funext (fun k => (hAnewAbsSpec k).2)
    rw [heq]
    simpa only [zero_mul] using hAbsEps.mul_const (K * mH)
  have hAdnewZero : ∀ i : Fin n, Filter.Tendsto
      (fun k : ℕ => ∫ ω, |AdeleteNew k i ω - Adelete i ω| ∂ν)
      Filter.atTop (nhds (0 : ℝ)) := by
    intro i
    have heq : (fun k : ℕ => ∫ ω, |AdeleteNew k i ω - Adelete i ω| ∂ν) =
        (fun k : ℕ => |ε k| * (K * mHdelete i)) := funext (fun k => (hAdnewAbsSpec k i).2)
    rw [heq]
    simpa only [zero_mul] using hAbsEps.mul_const (K * mHdelete i)
  have hTransfer : ∀ (f g : ℕ → ℝ) (L C : ℝ),
      0 ≤ C →
      (∀ k : ℕ, |f k - g k| ≤ |ε k| * C) →
      Filter.Tendsto g Filter.atTop (nhds L) →
      Filter.Tendsto f Filter.atTop (nhds L) := by
    intro f g L C hC hclose hg
    have hzero : Filter.Tendsto (fun k : ℕ => f k - g k) Filter.atTop (nhds (0 : ℝ)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simp only [sub_zero, Real.norm_eq_abs]
      apply squeeze_zero'
        (Filter.Eventually.of_forall fun k => abs_nonneg (f k - g k))
        (Filter.Eventually.of_forall hclose)
      simpa only [zero_mul] using hAbsEps.mul_const C
    simpa only [sub_add_cancel, zero_add] using hzero.add hg
  have hFnLim : Filter.Tendsto (fun k : ℕ => ∫ ω, Fn k ω ∂ν)
      Filter.atTop (nhds (∫ ω, F0 ω ∂ν)) :=
    hTransfer (fun k => ∫ ω, Fn k ω ∂ν) (fun k => ∫ ω, Fo k ω ∂ν)
      (∫ ω, F0 ω ∂ν) Cfull hCfull hFullIntegralError hFoLim
  have hDnLim : ∀ i : Fin n, Filter.Tendsto (fun k : ℕ => ∫ ω, Dn k i ω ∂ν)
      Filter.atTop (nhds (∫ ω, D0 i ω ∂ν)) := fun i =>
    hTransfer (fun k => ∫ ω, Dn k i ω ∂ν) (fun k => ∫ ω, Do k i ω ∂ν)
      (∫ ω, D0 i ω ∂ν) (Cdel i) (hCdel i) (fun k => hDelIntegralError k i) (hDoLim i)
  have hCnLim : ∀ i : Fin n, Filter.Tendsto (fun k : ℕ => ∫ ω, Cn k i ω ∂ν)
      Filter.atTop (nhds (∫ ω, C0 i ω ∂ν)) := fun i =>
    hTransfer (fun k => ∫ ω, Cn k i ω ∂ν) (fun k => ∫ ω, Co k i ω ∂ν)
      (∫ ω, C0 i ω ∂ν) (Ccompact i) (hCcompact i) (fun k => hCompactIntegralError k i) (hCoLim i)
  have hCompactCostCompare : ∀ k : ℕ,
      |compactCostη k - compactCostOld k| ≤ |ε k| * CcompactTotal := by
    intro k
    have heq : compactCostη k - compactCostOld k =
        ((∫ ω, Anew k ω ∂ν) - (∫ ω, Aold k ω ∂ν)) +
          ∑ i : Fin n, ((∫ ω, Cn k i ω ∂ν) - (∫ ω, Co k i ω ∂ν)) := by
      dsimp only [compactCostη, compactCostOld, Cn, Co]
      rw [Finset.sum_sub_distrib]
      ring
    rw [heq]
    calc
      |((∫ ω, Anew k ω ∂ν) - (∫ ω, Aold k ω ∂ν)) +
          ∑ i : Fin n, ((∫ ω, Cn k i ω ∂ν) - (∫ ω, Co k i ω ∂ν))| ≤
          |(∫ ω, Anew k ω ∂ν) - (∫ ω, Aold k ω ∂ν)| +
            |∑ i : Fin n, ((∫ ω, Cn k i ω ∂ν) - (∫ ω, Co k i ω ∂ν))| := abs_add _ _
      _ ≤ |ε k| * (d * mH) +
          ∑ i : Fin n, |(∫ ω, Cn k i ω ∂ν) - (∫ ω, Co k i ω ∂ν)| :=
        add_le_add (hAoldNewIntegralError k) (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ |ε k| * (d * mH) + ∑ i : Fin n, |ε k| * Ccompact i :=
        add_le_add_left (Finset.sum_le_sum (fun i _ => hCompactIntegralError k i)) _
      _ = |ε k| * CcompactTotal := by
        rw [← Finset.mul_sum]
        dsimp only [CcompactTotal]
        ring
  have hSourceLim : Filter.Tendsto sourceCostη Filter.atTop (nhds sourceCost) :=
    (hFnLim.add (tendsto_finsetSum Finset.univ (fun i _ => hDnLim i))).div hIlim hIpos.ne'
  have hCompactLim : Filter.Tendsto compactCostη Filter.atTop (nhds compactCost) :=
    hTransfer compactCostη compactCostOld compactCost CcompactTotal
      hCcompactTotal hCompactCostCompare hOldCompactLim
  exact ⟨hHm, hHint, hHdeleteSpec, hHnonneg, hHdnonneg,
    (fun k => ⟨hAnewM k, hAnewI k, hAnewNonneg k⟩),
    (fun k i => ⟨hAdnewM k i, hAdnewI k i, hAdnewNonneg k i⟩),
    hAnewAbsSpec, hAdnewAbsSpec, hAnewZero, hAdnewZero,
    hF0I, hFnI, hD0I, hDnI, hC0I, hCnI, hIpos, (fun k => (hIηSpec k).2), hIlim,
    hFnLim, hDnLim, hFnLim.div hIlim hIpos.ne',
    (fun i => (hDnLim i).div hIlim hIpos.ne'), hCnLim, hSourceLim, hCompactLim⟩

end

end Shao.OQ6.LiteralDeletedWeightedCosts
