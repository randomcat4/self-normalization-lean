import Shao.OQ6.NormalizedIntegrableTailAssembly
import Shao.OQ6.CanonicalSequenceAnalyticCosts

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Shao.OQ6.CanonicalIntegrableTailBounds

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology

universe u v

theorem ambient_canonical_integrable_tail_bounds
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
    (cSZ C1 C2 C3 C4 : ℝ)
    (hSZ : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{v}
      cSZ C1 C2 C3 C4)
    (x : ℝ) (hx : 1 ≤ x)
    (hδ : ∀ i : Fin n,
      (∫ ω, (x * g i (O i ω)) ^ 2 * min |x * g i (O i ω)| 1 ∂P) ≤ (1 / 2 : ℝ))
    (hL : (∑ i : Fin n, ∫ ω, (x * g i (O i ω)) ^ 2 * min |x * g i (O i ω)| 1 ∂P) ≤
      (cSZ / 2) * x ^ 2) :
    let Q : Ω0 → (∀ i : Fin n, X i) := fun ω i => O i ω
    let ξ0 : Fin n → Ω0 → ℝ := fun i ω => g i (O i ω)
    let W0 : Ω0 → ℝ := fun ω => ∑ i : Fin n, ξ0 i ω
    let V0 : Ω0 → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ0 i ω) ^ 2)
    let b0 : Ω0 → ℝ := fun ω => Real.sqrt (1 + D2 (Q ω))
    let T0 : Ω0 → ℝ := fun ω => if V0 ω = 0 then κ ω else (W0 ω + D1 (Q ω)) / (V0 ω * b0 ω)
    let F0 : Set Ω0 := {ω : Ω0 | x * V0 ω * b0 ω ≤ W0 ω + D1 (Q ω)}
    let Z0 : Set Ω0 := {ω : Ω0 | V0 ω = 0}
    let p0 : ℝ := P.real Z0
    let δ0 : Fin n → ℝ := fun i => ∫ ω, (x * ξ0 i ω) ^ 2 * min |x * ξ0 i ω| 1 ∂P
    let L0 : ℝ := ∑ i : Fin n, δ0 i
    let S0 : Ω0 → ℝ := fun ω => ∑ i : Fin n, (x * ξ0 i ω - (x * ξ0 i ω) ^ 2 / 2)
    let S0minus : Fin n → Ω0 → ℝ := fun i ω => ∑ j ∈ Finset.univ.erase i, (x * ξ0 j ω - (x * ξ0 j ω) ^ 2 / 2)
    let I0 : ℝ := ∫ ω, Real.exp (S0 ω) ∂P
    let full0 : Ω0 → ℝ := fun ω => (x * Aenv (Q ω) + x ^ 2 * Benv (Q ω)) * Real.exp (S0 ω)
    let deleted0 : Fin n → Ω0 → ℝ := fun i ω => (min |x * ξ0 i ω| 1 * (|Aenv (Q ω) - Adeleted i (fun j => O j.1 ω)| + x * |Benv (Q ω) - Bdeleted i (fun j => O j.1 ω)|)) * Real.exp (S0minus i ω)
    let R0 : ℝ := ((∫ ω, full0 ω ∂P) + ∑ i : Fin n, ∫ ω, deleted0 i ω ∂P) / I0
    let lower0 : ℝ := Shao.standardNormalTail x * Real.exp (-C1 * L0) * (1 - C2 * R0)
    let upper0 : ℝ := Shao.standardNormalTail x * Real.exp (C3 * L0) * (1 + C4 * R0)
    let numeratorBad0 : Set Ω0 := {ω : Ω0 | x * |D1 (Q ω)| > V0 ω / 8}
    let denominatorBad0 : Set Ω0 := {ω : Ω0 | x ^ 2 * |D2 (Q ω)| > (1 / 4 : ℝ)}
    lower0 ≤ P.real F0 ∧
    P.real F0 ≤ upper0 + P.real numeratorBad0 + P.real denominatorBad0 + p0 ∧
    lower0 - p0 ≤ P.real {ω : Ω0 | x ≤ T0 ω} ∧
    P.real {ω : Ω0 | x ≤ T0 ω} ≤
      upper0 + P.real numeratorBad0 + P.real denominatorBad0 + 2 * p0 := by
  classical
  dsimp only
  let Q : Ω0 → (∀ i : Fin n, X i) := fun ω i => O i ω
  let ξ0 : Fin n → Ω0 → ℝ := fun i ω => g i (O i ω)
  let W0 : Ω0 → ℝ := fun ω => ∑ i : Fin n, ξ0 i ω
  let V0 : Ω0 → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ0 i ω) ^ 2)
  let b0 : Ω0 → ℝ := fun ω => Real.sqrt (1 + D2 (Q ω))
  let T0 : Ω0 → ℝ := fun ω => if V0 ω = 0 then κ ω else
    (W0 ω + D1 (Q ω)) / (V0 ω * b0 ω)
  let F0 : Set Ω0 := {ω : Ω0 | x * V0 ω * b0 ω ≤ W0 ω + D1 (Q ω)}
  let Z0 : Set Ω0 := {ω : Ω0 | V0 ω = 0}
  let p0 : ℝ := P.real Z0
  let δ0 : Fin n → ℝ := fun i => ∫ ω,
    (x * ξ0 i ω) ^ 2 * min |x * ξ0 i ω| 1 ∂P
  let L0 : ℝ := ∑ i : Fin n, δ0 i
  let S0 : Ω0 → ℝ := fun ω => ∑ i : Fin n,
    (x * ξ0 i ω - (x * ξ0 i ω) ^ 2 / 2)
  let S0minus : Fin n → Ω0 → ℝ := fun i ω =>
    ∑ j ∈ Finset.univ.erase i, (x * ξ0 j ω - (x * ξ0 j ω) ^ 2 / 2)
  let I0 : ℝ := ∫ ω, Real.exp (S0 ω) ∂P
  let full0 : Ω0 → ℝ := fun ω =>
    (x * Aenv (Q ω) + x ^ 2 * Benv (Q ω)) * Real.exp (S0 ω)
  let deleted0 : Fin n → Ω0 → ℝ := fun i ω =>
    (min |x * ξ0 i ω| 1 *
      (|Aenv (Q ω) - Adeleted i (fun j => O j.1 ω)| +
        x * |Benv (Q ω) - Bdeleted i (fun j => O j.1 ω)|)) *
      Real.exp (S0minus i ω)
  let R0 : ℝ := ((∫ ω, full0 ω ∂P) +
    ∑ i : Fin n, ∫ ω, deleted0 i ω ∂P) / I0
  let lower0 : ℝ := Shao.standardNormalTail x * Real.exp (-C1 * L0) * (1 - C2 * R0)
  let upper0 : ℝ := Shao.standardNormalTail x * Real.exp (C3 * L0) * (1 + C4 * R0)
  let numeratorBad0 : Set Ω0 := {ω : Ω0 | x * |D1 (Q ω)| > V0 ω / 8}
  let denominatorBad0 : Set Ω0 := {ω : Ω0 | x ^ 2 * |D2 (Q ω)| > (1 / 4 : ℝ)}
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx

  -- These are the actual qualified155/157 product construction and code sequence.
  let μ : ∀ i : Fin n, Measure (X i) := fun i => P.map (O i)
  let μ0 : Measure (∀ i : Fin n, X i) := Measure.pi μ
  let lambda01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
  let νlocal : ∀ i : Fin n, Measure (X i × ℝ) := fun i => (μ i).prod lambda01
  let ν : Measure (∀ i : Fin n, X i × ℝ) := Measure.pi νlocal
  let q : (∀ i : Fin n, X i × ℝ) → (∀ i : Fin n, X i) := fun y i => (y i).1
  let ε : ℕ → ℝ := fun k => 1 / (8 * Real.sqrt (n : ℝ) * ((k : ℝ) + 1))
  let c : ∀ i : Fin n, (X i × ℝ) → ℝ := fun i =>
    Shao.OQ6.ScalarObservationCoding.baseFourIndicatorCode
      (MeasurableSpace.natGeneratingSequence (X i × ℝ))
  let ξlocal : ∀ i : Fin n, (X i × ℝ) → ℝ := fun i z => g i z.1
  let Ylocal : ℕ → ∀ i : Fin n, (X i × ℝ) → ℝ := fun k i =>
    Shao.OQ6.QuantizedObservationCoding.quantizedObservation (ε k) (ξlocal i) (c i)
  let ξ : Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun i y => g i (y i).1
  let Y : ℕ → Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun k i y => Ylocal k i (y i)
  let η : ℕ → Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun k =>
    Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
  let Vη : ℕ → (∀ i : Fin n, X i × ℝ) → ℝ := fun k y =>
    Real.sqrt (∑ i : Fin n, (η k i y) ^ 2)
  let D1ν : (∀ i : Fin n, X i × ℝ) → ℝ := fun y => D1 (q y)
  let D2ν : (∀ i : Fin n, X i × ℝ) → ℝ := fun y => D2 (q y)
  let Aν : (∀ i : Fin n, X i × ℝ) → ℝ := fun y => Aenv (q y)
  let Bν : (∀ i : Fin n, X i × ℝ) → ℝ := fun y => Benv (q y)
  let Aνdelete : Fin n → (∀ i : Fin n, X i × ℝ) → ℝ :=
    fun i y => Adeleted i (fun j => (y j.1).1)
  let Bνdelete : Fin n → (∀ i : Fin n, X i × ℝ) → ℝ :=
    fun i y => Bdeleted i (fun j => (y j.1).1)

  have hLaw :=
    Shao.OQ6.AmbientCanonicalCodingTransport.ambient_independent_uniform_observation_transport
      P O hO hOindep
  dsimp only at hLaw
  rcases hLaw with ⟨hμprob, hμ0prob, hνprob, hQ, hq, hU, hqU,
    hVectorLaw, hRealLaw, hIntegralLaw, hL2Law, hDeletedLaw, hEventLaw⟩
  letI : IsProbabilityMeasure ν := hνprob
  have hCanonical :=
    Shao.OQ6.CanonicalSequenceAnalyticCosts.ambient_canonical_sequence_cost_limits_and_strict_budgets
      P n hn O hO hOindep g hg hg2 hgmean hgenergy
      Aenv Benv Adeleted Bdeleted hAenv hBenv hAdeleted hBdeleted
      hAnonneg hBnonneg hAdeletenonneg hBdeletenonneg
      hAint hBint hAdeleteint hBdeleteint x hx0
  dsimp only at hCanonical
  rcases hCanonical with ⟨hεrange, hεlim, hνprobCanonical, hQCanonical, hqCanonical,
    hZ0meas, hZνmeas, hZlaw, hp0law, hYspec, hYerror, haBound, hsBound,
    hηlocal, hηspec, hηmoments, hηNoAtoms, hηzero, hCode, hFullFactor,
    hDeletedFactor, haLimit, hsLimit, hρlimit, hηlimit, hVηlimit,
    hηL1limit, hηL2limit, hHmeas, hHint, hAεspec, hAεlimit,
    hExp0int, hI0pos, hExpη, hExpMinus0, hExpMinusη, hPartialMass,
    hFull0int, hDeleted0int, hFullηint, hDeletedηint, hIηlimit, hJηlimit,
    hδlimit, hLlimit, hCompactLlimit, hSourceCostLimit, hCompactCostLimit,
    hStrictBudgets, hStrictSZBudgets⟩

  have hξ0 : ∀ i : Fin n, Measurable (ξ0 i) := fun i => (hg i).comp (hO i)
  have hξbar : ∀ i : Fin n, Measurable (fun o : (∀ j : Fin n, X j) => g i (o i)) :=
    fun i => (hg i).comp (measurable_pi_apply i)
  have hξ : ∀ i : Fin n, Measurable (ξ i) :=
    fun i => (hg i).comp (measurable_pi_apply i).fst
  have hξ2 : ∀ i : Fin n, MemLp (ξ i) 2 ν := by
    intro i
    exact (hL2Law (fun o => g i (o i)) (hξbar i) (hg2 i)).2
  -- Qualified150 supplies genuine first and square integrability from the original L2 data.
  have hOriginalMoments :=
    Shao.OQ6.ActualMomentNormalization.actual_centering_and_scale_spec
      P n hn ξ0 ξ0 hξ0 hg2 hgmean hgenergy hξ0 0 (le_refl 0)
      (by intro i ω; simp only [sub_self, abs_zero, le_refl])
  dsimp only at hOriginalMoments
  rcases hOriginalMoments with ⟨hOriginalL2, hOriginalL1, hOriginalSquareL1, hOriginalRest⟩
  have hξmean : ∀ i : Fin n, (∫ y, ξ i y ∂ν) = 0 := by
    intro i
    exact (hIntegralLaw (fun o => g i (o i)) (hξbar i) (hOriginalL1 i)).2.2.2.trans
      (hgmean i)
  have hSquareLaw : ∀ i : Fin n,
      (∫ y, (ξ i y) ^ 2 ∂ν) = ∫ ω, (ξ0 i ω) ^ 2 ∂P := by
    intro i
    exact (hIntegralLaw (fun o => (g i (o i)) ^ 2) ((hξbar i).pow_const 2)
      (hOriginalSquareL1 i)).2.2.2
  have hξenergy : (∑ i : Fin n, ∫ y, (ξ i y) ^ 2 ∂ν) = 1 := by
    calc
      (∑ i : Fin n, ∫ y, (ξ i y) ^ 2 ∂ν) =
          ∑ i : Fin n, ∫ ω, (ξ0 i ω) ^ 2 ∂P :=
        Finset.sum_congr rfl (fun i _ => hSquareLaw i)
      _ = 1 := hgenergy

  have hOmit : ∀ i : Fin n, Measurable
      (fun o : (∀ j : Fin n, X j) => (fun j : {j : Fin n // j ≠ i} => o j.1)) := by
    intro i
    apply Measurable.of_eval
    intro j
    exact measurable_pi_apply j.1
  have hFirstOmit : ∀ i : Fin n, Measurable
      (fun z : (∀ j : {j : Fin n // j ≠ i}, X j.1 × ℝ) => (fun j => (z j).1)) := by
    intro i
    apply Measurable.of_eval
    intro j
    exact (measurable_pi_apply j).fst
  have hAν : Measurable Aν := hAenv.comp hq.measurable
  have hBν : Measurable Bν := hBenv.comp hq.measurable
  have hD1ν : Measurable D1ν := hD1.comp hq.measurable
  have hD2ν : Measurable D2ν := hD2.comp hq.measurable
  have hAνdelete : ∀ i : Fin n, Measurable (Aνdelete i) := by
    intro i
    exact ((hAdeleted i).comp (hOmit i)).comp hq.measurable
  have hBνdelete : ∀ i : Fin n, Measurable (Bνdelete i) := by
    intro i
    exact ((hBdeleted i).comp (hOmit i)).comp hq.measurable
  have hAνint : Integrable Aν ν :=
    (hIntegralLaw Aenv hAenv hAint).2.2.1
  have hBνint : Integrable Bν ν :=
    (hIntegralLaw Benv hBenv hBint).2.2.1
  have hAνdeleteint : ∀ i : Fin n, Integrable (Aνdelete i) ν := by
    intro i
    exact (hIntegralLaw (fun o => Adeleted i (fun j => o j.1))
      ((hAdeleted i).comp (hOmit i)) (hAdeleteint i)).2.2.1
  have hBνdeleteint : ∀ i : Fin n, Integrable (Bνdelete i) ν := by
    intro i
    exact (hIntegralLaw (fun o => Bdeleted i (fun j => o j.1))
      ((hBdeleted i).comp (hOmit i)) (hBdeleteint i)).2.2.1
  have hD2PositiveSet : MeasurableSet {o : (∀ i : Fin n, X i) | 0 < 1 + D2 o} :=
    measurableSet_lt measurable_const (measurable_const.add hD2)
  have hD2μ : ∀ᵐ o ∂μ0, 0 < 1 + D2 o := by
    have hOriginal : ∀ᵐ ω ∂P, 0 < 1 + D2 (Q ω) := hD2pos
    have hm := (ae_map_iff hQ.measurable.aemeasurable hD2PositiveSet).mpr hOriginal
    simpa only [hQ.map_eq] using hm
  have hD2νpos : ∀ᵐ y ∂ν, 0 < 1 + D2ν y := by
    have hm : ∀ᵐ o ∂ν.map q, 0 < 1 + D2 o := by
      rw [hq.map_eq]
      exact hD2μ
    exact ae_of_ae_map hq.aemeasurable hm
  have hηpositive : ∀ k : ℕ, ∀ᵐ y ∂ν, 0 < Vη k y := by
    intro k
    have hne : ∀ᵐ y ∂ν, Vη k y ≠ 0 := by
      rw [ae_iff]
      simpa only [not_not] using hηzero k
    filter_upwards [hne] with y hy
    exact lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hy)
  have hAνfactor : ∀ (k : ℕ) (i : Fin n),
      ∃ F : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] F ∧
        ∀ y : (∀ j : Fin n, X j × ℝ), Aνdelete i y = F (fun j => η k j.1 y) := by
    intro k i
    rcases hDeletedFactor k i (fun z => Adeleted i (fun j => (z j).1))
        ((hAdeleted i).comp (hFirstOmit i)) with ⟨F, hF, hPointwise, hLift, hLast⟩
    exact ⟨F, hF, hLast⟩
  have hBνfactor : ∀ (k : ℕ) (i : Fin n),
      ∃ F : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] F ∧
        ∀ y : (∀ j : Fin n, X j × ℝ), Bνdelete i y = F (fun j => η k j.1 y) := by
    intro k i
    rcases hDeletedFactor k i (fun z => Bdeleted i (fun j => (z j).1))
        ((hBdeleted i).comp (hFirstOmit i)) with ⟨F, hF, hPointwise, hLift, hLast⟩
    exact ⟨F, hF, hLast⟩

  -- Genuine original truncated-moment integrability, with no integrability premise added.
  have hOriginalProjection :=
    Shao.OQ6.NormalizedAnalyticCostLimits.actual_projection_tilt_and_truncated_cost_limits
      P n hn ξ0 hξ0 hg2 hgmean hgenergy (fun _ : ℕ => ξ0)
      (fun _ i => hξ0 i) ε (fun k => (hεrange k).1)
      (fun k => (hεrange k).2) hεlim
      (by
        intro k i ω
        simpa only [sub_self, abs_zero] using (le_of_lt (hεrange k).1)) x
  dsimp only at hOriginalProjection
  rcases hOriginalProjection with ⟨hOriginalM, hDummyM, hOriginalExp, hOriginalI,
    hDummyExp, hOriginalMinus, hDummyMinus, hOriginalExpBound, hDummyExpBound,
    hOriginalMinusBound, hDummyMinusBound, hδ0int, hProjectionRest⟩
  have hδtest : ∀ i : Fin n, Measurable
      (fun o : (∀ j : Fin n, X j) => (x * g i (o i)) ^ 2 * min |x * g i (o i)| 1) := by
    intro i
    have hm : Measurable (fun o : (∀ j : Fin n, X j) => x * g i (o i)) :=
      measurable_const.mul (hξbar i)
    exact (hm.pow_const 2).mul ((continuous_abs.measurable.comp hm).min measurable_const)
  have hδlaw : ∀ i : Fin n,
      (∫ y, (x * ξ i y) ^ 2 * min |x * ξ i y| 1 ∂ν) = δ0 i := by
    intro i
    exact (hIntegralLaw
      (fun o => (x * g i (o i)) ^ 2 * min |x * g i (o i)| 1)
      (hδtest i) (hδ0int i)).2.2.2
  have hδν : ∀ i : Fin n,
      (∫ y, (x * ξ i y) ^ 2 * min |x * ξ i y| 1 ∂ν) ≤ (1 / 2 : ℝ) := by
    intro i
    rw [hδlaw i]
    exact hδ i
  have hLν : (∑ i : Fin n, ∫ y,
      (x * ξ i y) ^ 2 * min |x * ξ i y| 1 ∂ν) ≤ (cSZ / 2) * x ^ 2 := by
    calc
      (∑ i : Fin n, ∫ y, (x * ξ i y) ^ 2 * min |x * ξ i y| 1 ∂ν) = L0 :=
        Finset.sum_congr rfl (fun i _ => hδlaw i)
      _ ≤ (cSZ / 2) * x ^ 2 := hL

  -- Only the multiplication clauses of160 will be used. Its augmented convention is zero.
  have hAssembly :=
    Shao.OQ6.NormalizedIntegrableTailAssembly.actual_normalized_integrable_tail_assembly
      (ν := ν) (n := n) (hn := hn) (ξ := ξ)
      (hξ := hξ) (hξ2 := hξ2) (hξmean := hξmean) (hξenergy := hξenergy)
      (Y := Y) (hY := fun k i => (hYspec k i).1)
      (ε := ε) (hε := fun k => (hεrange k).1)
      (hεsmall := fun k => (hεrange k).2) (hεlim := hεlim) (herr := hYerror)
      (hηindep := fun k => (hηmoments k).1) (hηpos := hηpositive)
      (hFullFactor := hFullFactor)
      (D1 := D1ν) (D2 := D2ν) (κ := fun _ => 0) (A := Aν) (B := Bν)
      (Adelete := Aνdelete) (Bdelete := Bνdelete)
      (hD1 := hD1ν) (hD2 := hD2ν) (hκ := measurable_const)
      (hA := hAν) (hB := hBν) (hAdelete := hAνdelete) (hBdelete := hBνdelete)
      (hAnonneg := fun y => hAnonneg (q y))
      (hBnonneg := fun y => hBnonneg (q y))
      (hAdeletenonneg := fun i y => hAdeletenonneg i (fun j => (y j.1).1))
      (hBdeletenonneg := fun i y => hBdeletenonneg i (fun j => (y j.1).1))
      (hD1A := fun y => hD1A (q y)) (hD2B := fun y => hD2B (q y))
      (hD2pos := hD2νpos) (hAint := hAνint) (hBint := hBνint)
      (hAdeleteint := hAνdeleteint) (hBdeleteint := hBνdeleteint)
      (hAdeleteFactor := hAνfactor) (hBdeleteFactor := hBνfactor)
      (cSZ := cSZ) (C1 := C1) (C2 := C2) (C3 := C3) (C4 := C4)
      (hSZ := hSZ) (x := x) (hx := hx) (hδ := hδν) (hL := hLν)
  dsimp only at hAssembly
  rcases hAssembly with ⟨hEncodedBudgets, hLowerLimit, hUpperLimit,
    hEncodedMultiplication, hLowerν, hUpperν, hUnusedPhysicalLower, hUnusedPhysicalUpper⟩

  let Wbar : (∀ i : Fin n, X i) → ℝ := fun o => ∑ i : Fin n, g i (o i)
  let Vbar : (∀ i : Fin n, X i) → ℝ := fun o =>
    Real.sqrt (∑ i : Fin n, (g i (o i)) ^ 2)
  let bbar : (∀ i : Fin n, X i) → ℝ := fun o => Real.sqrt (1 + D2 o)
  let Sbar : (∀ i : Fin n, X i) → ℝ := fun o =>
    ∑ i : Fin n, (x * g i (o i) - (x * g i (o i)) ^ 2 / 2)
  let SbarMinus : Fin n → (∀ i : Fin n, X i) → ℝ := fun i o =>
    ∑ j ∈ Finset.univ.erase i, (x * g j (o j) - (x * g j (o j)) ^ 2 / 2)
  let fullbar : (∀ i : Fin n, X i) → ℝ := fun o =>
    (x * Aenv o + x ^ 2 * Benv o) * Real.exp (Sbar o)
  let deletedbar : Fin n → (∀ i : Fin n, X i) → ℝ := fun i o =>
    (min |x * g i (o i)| 1 *
      (|Aenv o - Adeleted i (fun j => o j.1)| +
        x * |Benv o - Bdeleted i (fun j => o j.1)|)) * Real.exp (SbarMinus i o)
  let Fbar : Set (∀ i : Fin n, X i) :=
    {o | x * Vbar o * bbar o ≤ Wbar o + D1 o}
  let numeratorBadbar : Set (∀ i : Fin n, X i) :=
    {o | x * |D1 o| > Vbar o / 8}
  let denominatorBadbar : Set (∀ i : Fin n, X i) :=
    {o | x ^ 2 * |D2 o| > (1 / 4 : ℝ)}
  let Wν : (∀ i : Fin n, X i × ℝ) → ℝ := fun y => ∑ i : Fin n, ξ i y
  let Vν : (∀ i : Fin n, X i × ℝ) → ℝ := fun y =>
    Real.sqrt (∑ i : Fin n, (ξ i y) ^ 2)
  let bν : (∀ i : Fin n, X i × ℝ) → ℝ := fun y => Real.sqrt (1 + D2ν y)
  let Sν : (∀ i : Fin n, X i × ℝ) → ℝ := fun y =>
    ∑ i : Fin n, (x * ξ i y - (x * ξ i y) ^ 2 / 2)
  let Sνminus : Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun i y =>
    ∑ j ∈ Finset.univ.erase i, (x * ξ j y - (x * ξ j y) ^ 2 / 2)
  let Iν : ℝ := ∫ y, Real.exp (Sν y) ∂ν
  let fullν : (∀ i : Fin n, X i × ℝ) → ℝ := fun y =>
    (x * Aν y + x ^ 2 * Bν y) * Real.exp (Sν y)
  let deletedν : Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun i y =>
    (min |x * ξ i y| 1 * (|Aν y - Aνdelete i y| +
      x * |Bν y - Bνdelete i y|)) * Real.exp (Sνminus i y)
  let Lν : ℝ := ∑ i : Fin n, ∫ y,
    (x * ξ i y) ^ 2 * min |x * ξ i y| 1 ∂ν
  let Rν : ℝ := ((∫ y, fullν y ∂ν) +
    ∑ i : Fin n, ∫ y, deletedν i y ∂ν) / Iν
  let lowerν : ℝ := Shao.standardNormalTail x * Real.exp (-C1 * Lν) * (1 - C2 * Rν)
  let upperν : ℝ := Shao.standardNormalTail x * Real.exp (C3 * Lν) * (1 + C4 * Rν)
  let Fν : Set (∀ i : Fin n, X i × ℝ) :=
    {y | x * Vν y * bν y ≤ Wν y + D1ν y}
  let numeratorBadν : Set (∀ i : Fin n, X i × ℝ) :=
    {y | x * |D1ν y| > Vν y / 8}
  let denominatorBadν : Set (∀ i : Fin n, X i × ℝ) :=
    {y | x ^ 2 * |D2ν y| > (1 / 4 : ℝ)}
  change lowerν ≤ ν.real Fν at hLowerν
  change ν.real Fν ≤ upperν + ν.real numeratorBadν + ν.real denominatorBadν +
    ν.real {y | Vν y = 0} at hUpperν

  have hWbar : Measurable Wbar :=
    Finset.measurable_sum _ (fun i _ => hξbar i)
  have hVbar : Measurable Vbar := Real.continuous_sqrt.measurable.comp
    (Finset.measurable_sum _ (fun i _ => (hξbar i).pow_const 2))
  have hbbar : Measurable bbar :=
    Real.continuous_sqrt.measurable.comp (measurable_const.add hD2)
  have hℓbar : ∀ i : Fin n, Measurable
      (fun o : (∀ j : Fin n, X j) => x * g i (o i) - (x * g i (o i)) ^ 2 / 2) := by
    intro i
    have hm : Measurable (fun o : (∀ j : Fin n, X j) => x * g i (o i)) :=
      measurable_const.mul (hξbar i)
    exact hm.sub ((hm.pow_const 2).div_const 2)
  have hSbar : Measurable Sbar :=
    Finset.measurable_sum _ (fun i _ => hℓbar i)
  have hSbarMinus : ∀ i : Fin n, Measurable (SbarMinus i) := by
    intro i
    exact Finset.measurable_sum _ (fun j _ => hℓbar j)
  have hFullbar : Measurable fullbar :=
    ((measurable_const.mul hAenv).add (measurable_const.mul hBenv)).mul
      (Real.continuous_exp.measurable.comp hSbar)
  have hDeletedbar : ∀ i : Fin n, Measurable (deletedbar i) := by
    intro i
    have hcap : Measurable
        (fun o : (∀ j : Fin n, X j) => min |x * g i (o i)| 1) :=
      (continuous_abs.measurable.comp
        (measurable_const.mul (hξbar i))).min measurable_const
    have hAdiff := continuous_abs.measurable.comp
      (hAenv.sub ((hAdeleted i).comp (hOmit i)))
    have hBdiff := continuous_abs.measurable.comp
      (hBenv.sub ((hBdeleted i).comp (hOmit i)))
    exact (hcap.mul (hAdiff.add (measurable_const.mul hBdiff))).mul
      (Real.continuous_exp.measurable.comp (hSbarMinus i))
  have hFbar : MeasurableSet Fbar :=
    measurableSet_le ((measurable_const.mul hVbar).mul hbbar) (hWbar.add hD1)
  have hNumeratorBadbar : MeasurableSet numeratorBadbar :=
    measurableSet_lt (hVbar.div_const 8)
      (measurable_const.mul (continuous_abs.measurable.comp hD1))
  have hDenominatorBadbar : MeasurableSet denominatorBadbar :=
    measurableSet_lt measurable_const
      (measurable_const.mul (continuous_abs.measurable.comp hD2))

  -- The unperturbed full/deleted numerators retain the original common full I.
  have hIlaw : Iν = I0 :=
    (hIntegralLaw (fun o => Real.exp (Sbar o))
      (Real.continuous_exp.measurable.comp hSbar) hExp0int).2.2.2
  have hFulllaw : (∫ y, fullν y ∂ν) = ∫ ω, full0 ω ∂P :=
    (hIntegralLaw fullbar hFullbar hFull0int).2.2.2
  have hDeletedIntegralLaw : ∀ i : Fin n,
      (∫ y, deletedν i y ∂ν) = ∫ ω, deleted0 i ω ∂P := by
    intro i
    exact (hIntegralLaw (deletedbar i) (hDeletedbar i) (hDeleted0int i).1).2.2.2
  have hDeletedSumLaw : (∑ i : Fin n, ∫ y, deletedν i y ∂ν) =
      ∑ i : Fin n, ∫ ω, deleted0 i ω ∂P :=
    Finset.sum_congr rfl (fun i _ => hDeletedIntegralLaw i)
  have hRlaw : Rν = R0 := by
    dsimp only [Rν, R0]
    rw [hFulllaw, hDeletedSumLaw, hIlaw]
  have hLlaw : Lν = L0 :=
    Finset.sum_congr rfl (fun i _ => hδlaw i)
  have hLowerLaw : lowerν = lower0 := by
    dsimp only [lowerν, lower0]
    rw [hLlaw, hRlaw]
  have hUpperLaw : upperν = upper0 := by
    dsimp only [upperν, upper0]
    rw [hLlaw, hRlaw]
  have hFlaw : ν.real Fν = P.real F0 := (hEventLaw Fbar hFbar).2
  have hNumeratorLaw : ν.real numeratorBadν = P.real numeratorBad0 :=
    (hEventLaw numeratorBadbar hNumeratorBadbar).2
  have hDenominatorLaw : ν.real denominatorBadν = P.real denominatorBad0 :=
    (hEventLaw denominatorBadbar hDenominatorBadbar).2
  have hProjectionZeroLaw : ν.real {y | Vν y = 0} = p0 := hp0law
  have hLower0 : lower0 ≤ P.real F0 := by
    simpa only [hLowerLaw, hFlaw] using hLowerν
  have hUpper0 : P.real F0 ≤ upper0 + P.real numeratorBad0 +
      P.real denominatorBad0 + p0 := by
    simpa only [hUpperLaw, hFlaw, hNumeratorLaw, hDenominatorLaw, hProjectionZeroLaw] using hUpperν

  -- Original κ stays on Ω0. The qualified155 consumer contains the153 comparison.
  have hPhysical :=
    Shao.OQ6.AmbientCanonicalCodingTransport.ambient_canonical_normalized_observation_consumer
      P n hn O hO hOindep g hg hg2 hgmean hgenergy
      D1 D2 hD1 hD2 κ hκ hD2pos (ε 0) (hεrange 0).1 (hεrange 0).2
  dsimp only at hPhysical
  rcases hPhysical with ⟨hPhysicalProb, hPhysicalQ, hPhysicalq, hPhysicalScale,
    hPhysicalLocal, hPhysicalIndep, hPhysicalL2, hPhysicalIntegrable,
    hPhysicalMean, hPhysicalEnergy, hPhysicalNoAtoms, hPhysicalZero,
    hPhysicalPositive, hPhysicalCodeMeas, hPhysicalCodeComap,
    hPhysicalFullFactor, hPhysicalDeletedFactor, hPhysicalRemainderFactor,
    hT0meas, hPhysicalTMeas, hPhysicalZ0Meas, hPhysicalZMeas,
    hPhysicalZLaw, hPhysicalp0Law, hPhysicalSigned, hPhysicalCompare⟩
  have hComparison := hPhysicalCompare x (fun a b : ℝ => b ≤ a)
    (Or.inr (Or.inr (Or.inl rfl)))
  rcases hComparison with ⟨hTailMeas, hF0meas, hCodedTailMeas,
    hCodedTailLaw, hSymmDiffAE, hSymmDiffBound, hAbsComparison⟩
  have hOnePhysicalComparison :
      |P.real {ω : Ω0 | x ≤ T0 ω} - P.real F0| ≤ p0 := by
    simpa only [Measure.real, hCodedTailLaw, T0, F0, p0, Q, ξ0, W0, V0, b0, Z0]
      using hAbsComparison
  refine ⟨hLower0, hUpper0, ?_, ?_⟩
  · have hl := (abs_le.mp hOnePhysicalComparison).1
    linarith
  · have hu := (abs_le.mp hOnePhysicalComparison).2
    linarith

end

end Shao.OQ6.CanonicalIntegrableTailBounds
