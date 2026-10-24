import Shao.OQ6.NormalizedIntegrableCDFAssembly
import Shao.OQ6.CanonicalSequenceAnalyticCosts

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Shao.OQ6.AmbientCanonicalIntegrableCDF

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology

universe u v

theorem ambient_canonical_integrable_cdf_bounds
    (C : ℝ)
    (hSZ : Shao.OQ6.NormalizedIntegrableCDFAssembly.ScalarShaoZhouFiniteCostCDFInput.{v} C)
    {Ω0 : Type u} [MeasurableSpace Ω0]
    (P : Measure Ω0) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n) {X : Fin n → Type v}
    [mX : ∀ i : Fin n, MeasurableSpace (X i)]
    [∀ i : Fin n, MeasurableSpace.CountablyGenerated (X i)]
    (O : ∀ i : Fin n, Ω0 → X i)
    (hO : ∀ i : Fin n, Measurable (O i))
    (hOindep : iIndepFun O P)
    (g : ∀ i : Fin n, X i → ℝ)
    (hg : ∀ i : Fin n, Measurable (g i))
    (hg2 : ∀ i : Fin n, MemLp (fun ω : Ω0 => g i (O i ω)) 2 P)
    (hgmean : ∀ i : Fin n, (∫ ω, g i (O i ω) ∂P) = 0)
    (hgenergy : (∑ i : Fin n, ∫ ω, (g i (O i ω)) ^ 2 ∂P) = 1)
    (D1 D2 Aenv Benv : (∀ i : Fin n, X i) → ℝ)
    (Adeleted Bdeleted : ∀ i : Fin n, (∀ j : {j : Fin n // j ≠ i}, X j.1) → ℝ)
    (hD1 : Measurable D1) (hD2 : Measurable D2)
    (hAenv : Measurable Aenv) (hBenv : Measurable Benv)
    (hAdeleted : ∀ i : Fin n, Measurable (Adeleted i))
    (hBdeleted : ∀ i : Fin n, Measurable (Bdeleted i))
    (hAnonneg : ∀ o : (∀ i : Fin n, X i), 0 ≤ Aenv o)
    (hBnonneg : ∀ o : (∀ i : Fin n, X i), 0 ≤ Benv o)
    (hAdeletenonneg : ∀ (i : Fin n) (o : ∀ j : {j : Fin n // j ≠ i}, X j.1), 0 ≤ Adeleted i o)
    (hBdeletenonneg : ∀ (i : Fin n) (o : ∀ j : {j : Fin n // j ≠ i}, X j.1), 0 ≤ Bdeleted i o)
    (hD1A : ∀ o : (∀ i : Fin n, X i), |D1 o| ≤ Aenv o)
    (hD2B : ∀ o : (∀ i : Fin n, X i), |D2 o| ≤ Benv o)
    (hD2pos : ∀ᵐ ω ∂P, 0 < 1 + D2 (fun i => O i ω))
    (hAint : Integrable (fun ω : Ω0 => Aenv (fun i => O i ω)) P)
    (hBint : Integrable (fun ω : Ω0 => Benv (fun i => O i ω)) P)
    (hAdeleteint : ∀ i : Fin n, Integrable (fun ω : Ω0 => Adeleted i (fun j => O j.1 ω)) P)
    (hBdeleteint : ∀ i : Fin n, Integrable (fun ω : Ω0 => Bdeleted i (fun j => O j.1 ω)) P)
    (κ : Ω0 → ℝ) (hκ : Measurable κ)
    (z : ℝ) (hz : 0 ≤ z) :
    let Q : Ω0 → (∀ i : Fin n, X i) := fun ω i => O i ω
    let ξ0 : Fin n → Ω0 → ℝ := fun i ω => g i (O i ω)
    let W0 : Ω0 → ℝ := fun ω => ∑ i : Fin n, ξ0 i ω
    let V0 : Ω0 → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ0 i ω) ^ 2)
    let b0 : Ω0 → ℝ := fun ω => Real.sqrt (1 + D2 (Q ω))
    let T0 : Ω0 → ℝ := fun ω => if V0 ω = 0 then κ ω else (W0 ω + D1 (Q ω)) / (V0 ω * b0 ω)
    let F0 : Set Ω0 := {ω : Ω0 | W0 ω + D1 (Q ω) ≤ z * V0 ω * b0 ω}
    let Z0 : Set Ω0 := {ω : Ω0 | V0 ω = 0}
    let p0 : ℝ := P.real Z0
    let δ0 : Fin n → ℝ := fun i =>
      ∫ ω, ((1 + z) * ξ0 i ω) ^ 2 * min |(1 + z) * ξ0 i ω| 1 ∂P
    let L0 : ℝ := ∑ i : Fin n, δ0 i
    let compactDeleted0 : Fin n → Ω0 → ℝ := fun i ω =>
      min |ξ0 i ω| (1 + z)⁻¹ *
        (|Aenv (Q ω) - Adeleted i (fun j => O j.1 ω)| +
          z * |Benv (Q ω) - Bdeleted i (fun j => O j.1 ω)|)
    let compactCost0 : ℝ := L0 + (∫ ω, Aenv (Q ω) + z * Benv (Q ω) ∂P) +
      ∑ i : Fin n, ∫ ω, compactDeleted0 i ω ∂P
    |P.real F0 - Shao.OQ4.standardNormalCDF z| ≤ C * compactCost0 ∧
    |P.real {ω : Ω0 | T0 ω ≤ z} - Shao.OQ4.standardNormalCDF z| ≤ C * compactCost0 + p0 := by
  classical
  let Q : Ω0 → (∀ i : Fin n, X i) := fun ω i => O i ω
  let ξ0 : Fin n → Ω0 → ℝ := fun i ω => g i (O i ω)
  let W0 : Ω0 → ℝ := fun ω => ∑ i : Fin n, ξ0 i ω
  let V0 : Ω0 → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ0 i ω) ^ 2)
  let b0 : Ω0 → ℝ := fun ω => Real.sqrt (1 + D2 (Q ω))
  let T0 : Ω0 → ℝ := fun ω => if V0 ω = 0 then κ ω else (W0 ω + D1 (Q ω)) / (V0 ω * b0 ω)
  let F0 : Set Ω0 := {ω : Ω0 | W0 ω + D1 (Q ω) ≤ z * V0 ω * b0 ω}
  let Z0 : Set Ω0 := {ω : Ω0 | V0 ω = 0}
  let p0 : ℝ := P.real Z0
  let δ0 : Fin n → ℝ := fun i =>
      ∫ ω, ((1 + z) * ξ0 i ω) ^ 2 * min |(1 + z) * ξ0 i ω| 1 ∂P
  let L0 : ℝ := ∑ i : Fin n, δ0 i
  let compactDeleted0 : Fin n → Ω0 → ℝ := fun i ω =>
      min |ξ0 i ω| (1 + z)⁻¹ *
        (|Aenv (Q ω) - Adeleted i (fun j => O j.1 ω)| +
          z * |Benv (Q ω) - Bdeleted i (fun j => O j.1 ω)|)
  let compactCost0 : ℝ := L0 + (∫ ω, Aenv (Q ω) + z * Benv (Q ω) ∂P) +
      ∑ i : Fin n, ∫ ω, compactDeleted0 i ω ∂P
  change |P.real F0 - Shao.OQ4.standardNormalCDF z| ≤ C * compactCost0 ∧
    |P.real {ω : Ω0 | T0 ω ≤ z} - Shao.OQ4.standardNormalCDF z| ≤ C * compactCost0 + p0
  let Ω : Type v := ∀ i : Fin n, X i × ℝ
  let μ : ∀ i : Fin n, Measure (X i) := fun i => P.map (O i)
  let μ0 : Measure (∀ i : Fin n, X i) := Measure.pi μ
  let lambda01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
  let νlocal : ∀ i : Fin n, Measure (X i × ℝ) := fun i => (μ i).prod lambda01
  let ν : Measure Ω := Measure.pi νlocal
  let q : Ω → (∀ i : Fin n, X i) := fun y i => (y i).1
  let ε : ℕ → ℝ := fun k => 1 / (8 * Real.sqrt (n : ℝ) * ((k : ℝ) + 1))
  let c : ∀ i : Fin n, (X i × ℝ) → ℝ := fun i =>
    Shao.OQ6.ScalarObservationCoding.baseFourIndicatorCode
      (MeasurableSpace.natGeneratingSequence (X i × ℝ))
  let ξlocal : ∀ i : Fin n, (X i × ℝ) → ℝ := fun i t => g i t.1
  let Ylocal : ℕ → ∀ i : Fin n, (X i × ℝ) → ℝ := fun k i =>
    Shao.OQ6.QuantizedObservationCoding.quantizedObservation (ε k) (ξlocal i) (c i)
  let ξ : Fin n → Ω → ℝ := fun i y => g i (y i).1
  let Y : ℕ → Fin n → Ω → ℝ := fun k i y => Ylocal k i (y i)
  let η : ℕ → Fin n → Ω → ℝ := fun k =>
    Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
  let Vη : ℕ → Ω → ℝ := fun k y => Real.sqrt (∑ i : Fin n, (η k i y) ^ 2)
  let D1ν : Ω → ℝ := fun y => D1 (q y)
  let D2ν : Ω → ℝ := fun y => D2 (q y)
  let Aν : Ω → ℝ := fun y => Aenv (q y)
  let Bν : Ω → ℝ := fun y => Benv (q y)
  let Aνdelete : Fin n → Ω → ℝ := fun i y => Adeleted i (fun j => (y j.1).1)
  let Bνdelete : Fin n → Ω → ℝ := fun i y => Bdeleted i (fun j => (y j.1).1)
  let compactDeletedν : Fin n → Ω → ℝ := fun i y =>
    min |ξ i y| (1 + z)⁻¹ * (|Aν y - Aνdelete i y| + z * |Bν y - Bνdelete i y|)
  let compactCostν : ℝ :=
    (∑ i : Fin n, ∫ y, ((1 + z) * ξ i y) ^ 2 * min |(1 + z) * ξ i y| 1 ∂ν) +
      (∫ y, Aν y + z * Bν y ∂ν) +
        ∑ i : Fin n, ∫ y, compactDeletedν i y ∂ν
  let Fν : Set Ω := {y : Ω | (∑ i : Fin n, ξ i y) + D1ν y ≤
    z * Real.sqrt (∑ i : Fin n, (ξ i y) ^ 2) * Real.sqrt (1 + D2ν y)}
  have htransport :=
    Shao.OQ6.AmbientCanonicalCodingTransport.ambient_independent_uniform_observation_transport
      P O hO hOindep
  rcases htransport with
    ⟨hμprob, hμ0prob, hprob, hQ, hq, _hU, _hqU, _hvectorLaw,
      _hscalarLaw, hintegral, hL2, _hdeletedLaw, hevent⟩
  letI : ∀ i : Fin n, IsProbabilityMeasure (μ i) := hμprob
  letI : IsProbabilityMeasure μ0 := hμ0prob
  letI : IsProbabilityMeasure ν := hprob
  have hsequence :=
    Shao.OQ6.CanonicalSequenceAnalyticCosts.ambient_canonical_sequence_cost_limits_and_strict_budgets
      P n hn O hO hOindep g hg hg2 hgmean hgenergy
      Aenv Benv Adeleted Bdeleted hAenv hBenv hAdeleted hBdeleted
      hAnonneg hBnonneg hAdeletenonneg hBdeletenonneg
      hAint hBint hAdeleteint hBdeleteint z hz
  rcases hsequence with
    ⟨hεspec, hεlim, _hprobSequence, _hQsequence, _hqsequence,
      _hZ0meas, _hZmeas, _hZlaw, _hZreal, hYspec, herr,
      _habound, _hscale, _hηlocal, hηspec, hηmoments, _hηatoms,
      hηzero, _hCoded, hFullFactor, hDeletedFactor, _halim, _hslim,
      _hρlim, _hpointlim, _hVlim, _hL1lim, _hL2lim, _hHmeas,
      _hHint, _hAεspec, _hAεlim, _hexp0int, _hI0pos, _hIηspec,
      _hJ0spec, _hJηspec, _hpartial, _hfull0int, hdeleted0int,
      _hfullηint, _hdeletedηint, _hIlim, _hJlim, _hδlim, _hLlim,
      _hLcompactlim, _hsourceCostlim, _hcompactCostlim, _hstrict, _hhalf⟩
  have hε (k : ℕ) : 0 < ε k := (hεspec k).1
  have hεsmall (k : ℕ) : ε k < 1 / (4 * Real.sqrt (n : ℝ)) := (hεspec k).2
  have hY (k : ℕ) (i : Fin n) : Measurable (Y k i) := (hYspec k i).1
  have hηindep (k : ℕ) : iIndepFun (η k) ν := (hηmoments k).1
  have hηpos (k : ℕ) : ∀ᵐ y ∂ν, 0 < Vη k y := by
    have hne : ∀ᵐ y ∂ν, Vη k y ≠ 0 := by
      rw [ae_iff]
      simpa only [not_not] using hηzero k
    filter_upwards [hne] with y hy
    exact lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hy)
  have hgbase (i : Fin n) : Measurable (fun o : (∀ j : Fin n, X j) => g i (o i)) :=
    (hg i).comp (measurable_pi_apply i)
  have hξ (i : Fin n) : Measurable (ξ i) := (hgbase i).comp hq.measurable
  have hξ2 (i : Fin n) : MemLp (ξ i) 2 ν :=
    (hL2 (fun o : (∀ j : Fin n, X j) => g i (o i)) (hgbase i) (hg2 i)).2
  have hξmean (i : Fin n) : (∫ y, ξ i y ∂ν) = 0 := by
    have hi := hintegral (fun o : (∀ j : Fin n, X j) => g i (o i))
      (hgbase i) ((hg2 i).integrable (by norm_num))
    exact hi.2.2.2.trans (hgmean i)
  have hξsquare (i : Fin n) :
      (∫ y, (ξ i y) ^ 2 ∂ν) = ∫ ω, (ξ0 i ω) ^ 2 ∂P :=
    (hintegral (fun o : (∀ j : Fin n, X j) => (g i (o i)) ^ 2)
      ((hgbase i).pow_const 2) (hg2 i).integrable_sq).2.2.2
  have hξenergy : (∑ i : Fin n, ∫ y, (ξ i y) ^ 2 ∂ν) = 1 := by
    calc
      (∑ i : Fin n, ∫ y, (ξ i y) ^ 2 ∂ν) =
          ∑ i : Fin n, ∫ ω, (ξ0 i ω) ^ 2 ∂P :=
        Finset.sum_congr rfl (fun i _ => hξsquare i)
      _ = 1 := hgenergy
  have hD1ν : Measurable D1ν := hD1.comp hq.measurable
  have hD2ν : Measurable D2ν := hD2.comp hq.measurable
  have hAν : Measurable Aν := hAenv.comp hq.measurable
  have hBν : Measurable Bν := hBenv.comp hq.measurable
  have hAbaseDelete (i : Fin n) :
      Measurable (fun o : (∀ j : Fin n, X j) => Adeleted i (fun j => o j.1)) :=
    (hAdeleted i).comp (Measurable.of_eval (fun j => measurable_pi_apply j.1))
  have hBbaseDelete (i : Fin n) :
      Measurable (fun o : (∀ j : Fin n, X j) => Bdeleted i (fun j => o j.1)) :=
    (hBdeleted i).comp (Measurable.of_eval (fun j => measurable_pi_apply j.1))
  have hAνdelete (i : Fin n) : Measurable (Aνdelete i) :=
    (hAbaseDelete i).comp hq.measurable
  have hBνdelete (i : Fin n) : Measurable (Bνdelete i) :=
    (hBbaseDelete i).comp hq.measurable
  have hAνint : Integrable Aν ν := (hintegral Aenv hAenv hAint).2.2.1
  have hBνint : Integrable Bν ν := (hintegral Benv hBenv hBint).2.2.1
  have hAνdeleteint (i : Fin n) : Integrable (Aνdelete i) ν :=
    (hintegral (fun o : (∀ j : Fin n, X j) => Adeleted i (fun j => o j.1))
      (hAbaseDelete i) (hAdeleteint i)).2.2.1
  have hBνdeleteint (i : Fin n) : Integrable (Bνdelete i) ν :=
    (hintegral (fun o : (∀ j : Fin n, X j) => Bdeleted i (fun j => o j.1))
      (hBbaseDelete i) (hBdeleteint i)).2.2.1
  have hPosMeas : MeasurableSet {o : (∀ i : Fin n, X i) | 0 < 1 + D2 o} :=
    measurableSet_lt measurable_const (measurable_const.add hD2)
  have hPosBase : ∀ᵐ o ∂μ0, 0 < 1 + D2 o := by
    have hm : ∀ᵐ o ∂P.map Q, 0 < 1 + D2 o :=
      (ae_map_iff hQ.aemeasurable hPosMeas).2 hD2pos
    rw [hQ.map_eq] at hm
    exact hm
  have hPosν : ∀ᵐ y ∂ν, 0 < 1 + D2ν y := by
    have hm : ∀ᵐ o ∂ν.map q, 0 < 1 + D2 o := by
      rw [hq.map_eq]
      exact hPosBase
    exact ae_of_ae_map hq.aemeasurable hm
  have hAdeleteFactor : ∀ (k : ℕ) (i : Fin n),
      ∃ F : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] F ∧
        ∀ y : Ω, Aνdelete i y = F (fun j => η k j.1 y) := by
    intro k i
    have hd : Measurable
        (fun t : (∀ j : {j : Fin n // j ≠ i}, X j.1 × ℝ) =>
          Adeleted i (fun j => (t j).1)) :=
      (hAdeleted i).comp (Measurable.of_eval (fun j => measurable_fst.comp (measurable_pi_apply j)))
    rcases hDeletedFactor k i
      (fun t : (∀ j : {j : Fin n // j ≠ i}, X j.1 × ℝ) => Adeleted i (fun j => (t j).1))
      hd with ⟨F, hF, _hlocal, _hlift, hpoint⟩
    exact ⟨F, hF, hpoint⟩
  have hBdeleteFactor : ∀ (k : ℕ) (i : Fin n),
      ∃ F : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] F ∧
        ∀ y : Ω, Bνdelete i y = F (fun j => η k j.1 y) := by
    intro k i
    have hd : Measurable
        (fun t : (∀ j : {j : Fin n // j ≠ i}, X j.1 × ℝ) =>
          Bdeleted i (fun j => (t j).1)) :=
      (hBdeleted i).comp (Measurable.of_eval (fun j => measurable_fst.comp (measurable_pi_apply j)))
    rcases hDeletedFactor k i
      (fun t : (∀ j : {j : Fin n // j ≠ i}, X j.1 × ℝ) => Bdeleted i (fun j => (t j).1))
      hd with ⟨F, hF, _hlocal, _hlift, hpoint⟩
    exact ⟨F, hF, hpoint⟩
  let δtest : Fin n → (∀ i : Fin n, X i) → ℝ := fun i o =>
    ((1 + z) * g i (o i)) ^ 2 * min |(1 + z) * g i (o i)| 1
  let fullTest : (∀ i : Fin n, X i) → ℝ := fun o => Aenv o + z * Benv o
  let compactTest : Fin n → (∀ i : Fin n, X i) → ℝ := fun i o =>
    min |g i (o i)| (1 + z)⁻¹ *
      (|Aenv o - Adeleted i (fun j => o j.1)| + z * |Benv o - Bdeleted i (fun j => o j.1)|)
  have hδtest (i : Fin n) : Measurable (δtest i) := by
    have hu : Measurable (fun o : (∀ j : Fin n, X j) => (1 + z) * g i (o i)) :=
      measurable_const.mul (hgbase i)
    exact (hu.pow_const 2).mul ((continuous_abs.measurable.comp hu).min measurable_const)
  have hfullTest : Measurable fullTest := hAenv.add (measurable_const.mul hBenv)
  have hcompactTest (i : Fin n) : Measurable (compactTest i) :=
    ((continuous_abs.measurable.comp (hgbase i)).min measurable_const).mul
      ((continuous_abs.measurable.comp (hAenv.sub (hAbaseDelete i))).add
        (measurable_const.mul (continuous_abs.measurable.comp (hBenv.sub (hBbaseDelete i)))))
  have hδtestint (i : Fin n) : Integrable (fun ω : Ω0 => δtest i (Q ω)) P := by
    apply ((hg2 i).integrable_sq.const_mul ((1 + z) ^ 2)).mono'
      ((hδtest i).comp hQ.measurable).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      change ‖((1 + z) * ξ0 i ω) ^ 2 * min |(1 + z) * ξ0 i ω| 1‖ ≤
        (1 + z) ^ 2 * (ξ0 i ω) ^ 2
      have hnonneg : 0 ≤ ((1 + z) * ξ0 i ω) ^ 2 * min |(1 + z) * ξ0 i ω| 1 :=
        mul_nonneg (sq_nonneg _) (le_min (abs_nonneg _) zero_le_one)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      calc
        ((1 + z) * ξ0 i ω) ^ 2 * min |(1 + z) * ξ0 i ω| 1 ≤
            ((1 + z) * ξ0 i ω) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (sq_nonneg _)
        _ = (1 + z) ^ 2 * (ξ0 i ω) ^ 2 := by ring
  have hfullTestint : Integrable (fun ω : Ω0 => fullTest (Q ω)) P :=
    hAint.add (hBint.const_mul z)
  have hcompactTestint (i : Fin n) : Integrable (fun ω : Ω0 => compactTest i (Q ω)) P :=
    (hdeleted0int i).2
  have hδlaw (i : Fin n) : (∫ y, δtest i (q y) ∂ν) = δ0 i :=
    (hintegral (δtest i) (hδtest i) (hδtestint i)).2.2.2
  have hfullLaw : (∫ y, fullTest (q y) ∂ν) = ∫ ω, fullTest (Q ω) ∂P :=
    (hintegral fullTest hfullTest hfullTestint).2.2.2
  have hcompactLaw (i : Fin n) :
      (∫ y, compactTest i (q y) ∂ν) = ∫ ω, compactTest i (Q ω) ∂P :=
    (hintegral (compactTest i) (hcompactTest i) (hcompactTestint i)).2.2.2
  have hcostLaw : compactCostν = compactCost0 := by
    change
      (∑ i : Fin n, ∫ y, δtest i (q y) ∂ν) + (∫ y, fullTest (q y) ∂ν) +
        (∑ i : Fin n, ∫ y, compactTest i (q y) ∂ν) =
      (∑ i : Fin n, δ0 i) + (∫ ω, fullTest (Q ω) ∂P) +
        (∑ i : Fin n, ∫ ω, compactTest i (Q ω) ∂P)
    simp only [hδlaw, hfullLaw, hcompactLaw]
  let baseEvent : Set (∀ i : Fin n, X i) :=
    {o | (∑ i : Fin n, g i (o i)) + D1 o ≤
      z * Real.sqrt (∑ i : Fin n, (g i (o i)) ^ 2) * Real.sqrt (1 + D2 o)}
  have hWbase : Measurable (fun o : (∀ i : Fin n, X i) => ∑ i : Fin n, g i (o i)) :=
    Finset.measurable_sum _ (fun i _ => hgbase i)
  have hVbase : Measurable
      (fun o : (∀ i : Fin n, X i) => Real.sqrt (∑ i : Fin n, (g i (o i)) ^ 2)) :=
    Real.continuous_sqrt.measurable.comp
      (Finset.measurable_sum _ (fun i _ => (hgbase i).pow_const 2))
  have hbbase : Measurable (fun o : (∀ i : Fin n, X i) => Real.sqrt (1 + D2 o)) :=
    Real.continuous_sqrt.measurable.comp (measurable_const.add hD2)
  have hbaseEvent : MeasurableSet baseEvent :=
    measurableSet_le (hWbase.add hD1) ((measurable_const.mul hVbase).mul hbbase)
  have hFlaw : ν.real Fν = P.real F0 := by
    have he := (hevent baseEvent hbaseEvent).2
    change ν.real Fν = P.real F0 at he
    exact he
  have hgeneric :=
    Shao.OQ6.NormalizedIntegrableCDFAssembly.actual_normalized_integrable_cdf_assembly
      C hSZ ν n hn ξ hξ hξ2 hξmean hξenergy Y hY ε hε hεsmall hεlim herr
      hηindep hηpos hFullFactor D1ν D2ν (fun _ : Ω => 0) Aν Bν Aνdelete Bνdelete
      hD1ν hD2ν measurable_const hAν hBν hAνdelete hBνdelete
      (fun y => hAnonneg (q y)) (fun y => hBnonneg (q y))
      (fun i y => hAdeletenonneg i (fun j => (y j.1).1))
      (fun i y => hBdeletenonneg i (fun j => (y j.1).1))
      (fun y => hD1A (q y)) (fun y => hD2B (q y)) hPosν
      hAνint hBνint hAνdeleteint hBνdeleteint hAdeleteFactor hBdeleteFactor z hz
  have hgenericBound : |ν.real Fν - Shao.OQ4.standardNormalCDF z| ≤ C * compactCostν :=
    hgeneric.1
  have hbound : |P.real F0 - Shao.OQ4.standardNormalCDF z| ≤ C * compactCost0 := by
    rw [← hFlaw, ← hcostLaw]
    exact hgenericBound
  have hphysical :=
    Shao.OQ6.AmbientCanonicalCodingTransport.ambient_canonical_normalized_observation_consumer
      P n hn O hO hOindep g hg hg2 hgmean hgenergy D1 D2 hD1 hD2 κ hκ hD2pos
      (ε 0) (hε 0) (hεsmall 0)
  rcases hphysical with
    ⟨_hprobPhysical, _hQphysical, _hqphysical, _hscalePhysical, _hlocalPhysical,
      _hindPhysical, _hL2Physical, _hintsPhysical, _hmeanPhysical, _henergyPhysical,
      _hatomsPhysical, _hzeroPhysical, _hpositivePhysical, _hmeasCPhysical,
      _hcomapPhysical, _hfullPhysical, _hdeletedPhysical, _hG2G1,
      _hT0measPhysical, _hTηmeasPhysical, _hZ0measPhysical, _hZmeasPhysical,
      _hZeqPhysical, _hZrealPhysical, _hsignedPhysical, hcomparisons⟩
  have hclosed := hcomparisons z (fun a b : ℝ => a ≤ b) (Or.inl rfl)
  rcases hclosed with ⟨_hAMeas, _hFMeas, _hEMeas, hEF, _hAE, _hSymm, hDiff⟩
  have hphysicalBound : |P.real {ω : Ω0 | T0 ω ≤ z} - P.real F0| ≤ p0 := by
    simpa only [T0, F0, p0, Z0, W0, V0, b0, Q, ξ0, Measure.real, hEF] using hDiff
  refine ⟨hbound, ?_⟩
  calc
    |P.real {ω : Ω0 | T0 ω ≤ z} - Shao.OQ4.standardNormalCDF z| =
        |(P.real {ω : Ω0 | T0 ω ≤ z} - P.real F0) +
          (P.real F0 - Shao.OQ4.standardNormalCDF z)| := by congr 1 <;> ring
    _ ≤ |P.real {ω : Ω0 | T0 ω ≤ z} - P.real F0| +
        |P.real F0 - Shao.OQ4.standardNormalCDF z| := abs_add_le _ _
    _ ≤ p0 + C * compactCost0 := add_le_add hphysicalBound hbound
    _ = C * compactCost0 + p0 := add_comm _ _

end

end Shao.OQ6.AmbientCanonicalIntegrableCDF
