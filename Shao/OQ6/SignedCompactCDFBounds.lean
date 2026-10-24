import Shao.OQ6.CompactTailBounds
import Shao.OQ4.ReflectedSurvival

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Shao.OQ6.SignedCompactCDFBounds

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology

universe u v

theorem ambient_weighted_ae_signed_compact_cdf_tail_bounds
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
    (hAnonneg : ∀ᵐ ω ∂P, 0 ≤ Aenv (fun i => O i ω))
    (hBnonneg : ∀ᵐ ω ∂P, 0 ≤ Benv (fun i => O i ω))
    (hAdeletenonneg : ∀ i : Fin n, ∀ᵐ ω ∂P,
      0 ≤ Adeleted i (fun j => O j.1 ω))
    (hBdeletenonneg : ∀ i : Fin n, ∀ᵐ ω ∂P,
      0 ≤ Bdeleted i (fun j => O j.1 ω))
    (hD1A : ∀ᵐ ω ∂P, |D1 (fun i => O i ω)| ≤ Aenv (fun i => O i ω))
    (hD2B : ∀ᵐ ω ∂P, |D2 (fun i => O i ω)| ≤ Benv (fun i => O i ω))
    (hD2pos : ∀ᵐ ω ∂P, 0 < 1 + D2 (fun i => O i ω))
    (κ : Ω0 → ℝ) (hκ : Measurable κ)
    (x : ℝ)
    (hFull : Integrable (fun ω : Ω0 =>
      Aenv (fun i => O i ω) + |x| * Benv (fun i => O i ω)) P)
    (hDeleted : ∀ i : Fin n, Integrable (fun ω : Ω0 =>
      min |g i (O i ω)| (1 + |x|)⁻¹ *
        (|Aenv (fun j => O j ω) - Adeleted i (fun j => O j.1 ω)| +
          |x| * |Benv (fun j => O j ω) - Bdeleted i (fun j => O j.1 ω)|)) P) :
    let r : ℝ := |x|
    let Q : Ω0 → (∀ i : Fin n, X i) := fun ω i => O i ω
    let ξ0 : Fin n → Ω0 → ℝ := fun i ω => g i (O i ω)
    let W0 : Ω0 → ℝ := fun ω => ∑ i : Fin n, ξ0 i ω
    let V0 : Ω0 → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ0 i ω) ^ 2)
    let b0 : Ω0 → ℝ := fun ω => Real.sqrt (1 + D2 (Q ω))
    let T0 : Ω0 → ℝ := fun ω => if V0 ω = 0 then κ ω else (W0 ω + D1 (Q ω)) / (V0 ω * b0 ω)
    let F0 : Set Ω0 := {ω : Ω0 | W0 ω + D1 (Q ω) ≤ x * V0 ω * b0 ω}
    let Z0 : Set Ω0 := {ω : Ω0 | V0 ω = 0}
    let p0 : ℝ := P.real Z0
    let δ0 : Fin n → ℝ := fun i =>
      ∫ ω, ((1 + r) * ξ0 i ω) ^ 2 * min |(1 + r) * ξ0 i ω| 1 ∂P
    let L0 : ℝ := ∑ i : Fin n, δ0 i
    let compactDeleted0 : Fin n → Ω0 → ℝ := fun i ω =>
      min |ξ0 i ω| (1 + r)⁻¹ *
        (|Aenv (Q ω) - Adeleted i (fun j => O j.1 ω)| +
          r * |Benv (Q ω) - Bdeleted i (fun j => O j.1 ω)|)
    let compactCost0 : ℝ := L0 + (∫ ω, Aenv (Q ω) + r * Benv (Q ω) ∂P) +
      ∑ i : Fin n, ∫ ω, compactDeleted0 i ω ∂P
    |P.real F0 - Shao.OQ4.standardNormalCDF x| ≤ C * compactCost0 ∧
    |P.real {ω : Ω0 | W0 ω + D1 (Q ω) < x * V0 ω * b0 ω} -
      Shao.OQ4.standardNormalCDF x| ≤ C * compactCost0 ∧
    |P.real {ω : Ω0 | x * V0 ω * b0 ω < W0 ω + D1 (Q ω)} -
      (1 - Shao.OQ4.standardNormalCDF x)| ≤ C * compactCost0 ∧
    |P.real {ω : Ω0 | x * V0 ω * b0 ω ≤ W0 ω + D1 (Q ω)} -
      (1 - Shao.OQ4.standardNormalCDF x)| ≤ C * compactCost0 ∧
    |P.real {ω : Ω0 | T0 ω ≤ x} - Shao.OQ4.standardNormalCDF x| ≤
      C * compactCost0 + p0 ∧
    |P.real {ω : Ω0 | T0 ω < x} - Shao.OQ4.standardNormalCDF x| ≤
      C * compactCost0 + p0 ∧
    |P.real {ω : Ω0 | x < T0 ω} - (1 - Shao.OQ4.standardNormalCDF x)| ≤
      C * compactCost0 + p0 ∧
    |P.real {ω : Ω0 | x ≤ T0 ω} - (1 - Shao.OQ4.standardNormalCDF x)| ≤
      C * compactCost0 + p0 := by
  classical
  let r : ℝ := |x|
  let Q : Ω0 → (∀ i : Fin n, X i) := fun ω i => O i ω
  let ξ0 : Fin n → Ω0 → ℝ := fun i ω => g i (O i ω)
  let W0 : Ω0 → ℝ := fun ω => ∑ i : Fin n, ξ0 i ω
  let V0 : Ω0 → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ0 i ω) ^ 2)
  let b0 : Ω0 → ℝ := fun ω => Real.sqrt (1 + D2 (Q ω))
  let T0 : Ω0 → ℝ := fun ω => if V0 ω = 0 then κ ω else (W0 ω + D1 (Q ω)) / (V0 ω * b0 ω)
  let F0 : Set Ω0 := {ω : Ω0 | W0 ω + D1 (Q ω) ≤ x * V0 ω * b0 ω}
  let Z0 : Set Ω0 := {ω : Ω0 | V0 ω = 0}
  let p0 : ℝ := P.real Z0
  let δ0 : Fin n → ℝ := fun i =>
      ∫ ω, ((1 + r) * ξ0 i ω) ^ 2 * min |(1 + r) * ξ0 i ω| 1 ∂P
  let L0 : ℝ := ∑ i : Fin n, δ0 i
  let compactDeleted0 : Fin n → Ω0 → ℝ := fun i ω =>
      min |ξ0 i ω| (1 + r)⁻¹ *
        (|Aenv (Q ω) - Adeleted i (fun j => O j.1 ω)| +
          r * |Benv (Q ω) - Bdeleted i (fun j => O j.1 ω)|)
  let compactCost0 : ℝ := L0 + (∫ ω, Aenv (Q ω) + r * Benv (Q ω) ∂P) +
      ∑ i : Fin n, ∫ ω, compactDeleted0 i ω ∂P
  let N0 : Ω0 → ℝ := fun ω => W0 ω + D1 (Q ω)
  let d0 : Ω0 → ℝ := fun ω => V0 ω * b0 ω
  let fullTest0 : Ω0 → ℝ := fun ω => Aenv (Q ω) + r * Benv (Q ω)
  let deltaIntegrand0 : Fin n → Ω0 → ℝ := fun i ω => ((1 + r) * ξ0 i ω) ^ 2 * min |(1 + r) * ξ0 i ω| 1
  let gNeg : ∀ i : Fin n, X i → ℝ := fun i o => -(g i o)
  let D1Neg : (∀ i : Fin n, X i) → ℝ := fun o => -(D1 o)
  let κNeg : Ω0 → ℝ := fun ω => -(κ ω)
  let ξNeg : Fin n → Ω0 → ℝ := fun i ω => gNeg i (O i ω)
  let WNeg : Ω0 → ℝ := fun ω => ∑ i : Fin n, ξNeg i ω
  let VNeg : Ω0 → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξNeg i ω) ^ 2)
  let bNeg : Ω0 → ℝ := fun ω => Real.sqrt (1 + D2 (Q ω))
  let TNeg : Ω0 → ℝ := fun ω => if VNeg ω = 0 then κNeg ω else (WNeg ω + D1Neg (Q ω)) / (VNeg ω * bNeg ω)
  let ZNeg : Set Ω0 := {ω : Ω0 | VNeg ω = 0}
  let pNeg : ℝ := P.real ZNeg
  let deltaIntegrandNeg : Fin n → Ω0 → ℝ := fun i ω => ((1 + r) * ξNeg i ω) ^ 2 * min |(1 + r) * ξNeg i ω| 1
  let δNeg : Fin n → ℝ := fun i => ∫ ω, deltaIntegrandNeg i ω ∂P
  let LNeg : ℝ := ∑ i : Fin n, δNeg i
  let fullTestNeg : Ω0 → ℝ := fun ω => Aenv (Q ω) + r * Benv (Q ω)
  let compactDeletedNeg : Fin n → Ω0 → ℝ := fun i ω => min |ξNeg i ω| (1 + r)⁻¹ * (|Aenv (Q ω) - Adeleted i (fun j => O j.1 ω)| + r * |Benv (Q ω) - Bdeleted i (fun j => O j.1 ω)|)
  let compactCostNeg : ℝ := LNeg + (∫ ω, fullTestNeg ω ∂P) + ∑ i : Fin n, ∫ ω, compactDeletedNeg i ω ∂P
  change
    |P.real F0 - Shao.OQ4.standardNormalCDF x| ≤ C * compactCost0 ∧
    |P.real {ω : Ω0 | W0 ω + D1 (Q ω) < x * V0 ω * b0 ω} -
      Shao.OQ4.standardNormalCDF x| ≤ C * compactCost0 ∧
    |P.real {ω : Ω0 | x * V0 ω * b0 ω < W0 ω + D1 (Q ω)} -
      (1 - Shao.OQ4.standardNormalCDF x)| ≤ C * compactCost0 ∧
    |P.real {ω : Ω0 | x * V0 ω * b0 ω ≤ W0 ω + D1 (Q ω)} -
      (1 - Shao.OQ4.standardNormalCDF x)| ≤ C * compactCost0 ∧
    |P.real {ω : Ω0 | T0 ω ≤ x} - Shao.OQ4.standardNormalCDF x| ≤
      C * compactCost0 + p0 ∧
    |P.real {ω : Ω0 | T0 ω < x} - Shao.OQ4.standardNormalCDF x| ≤
      C * compactCost0 + p0 ∧
    |P.real {ω : Ω0 | x < T0 ω} - (1 - Shao.OQ4.standardNormalCDF x)| ≤
      C * compactCost0 + p0 ∧
    |P.real {ω : Ω0 | x ≤ T0 ω} - (1 - Shao.OQ4.standardNormalCDF x)| ≤
      C * compactCost0 + p0
  have hr : 0 ≤ r := abs_nonneg x
  have hQ : Measurable Q := Measurable.of_eval hO
  have hξ (i : Fin n) : Measurable (ξ0 i) := (hg i).comp (hO i)
  have hW : Measurable W0 :=
    Finset.measurable_sum Finset.univ (fun i _ => hξ i)
  have hV : Measurable V0 := by
    apply Measurable.sqrt
    exact Finset.measurable_sum Finset.univ (fun i _ =>
      (hξ i).pow (measurable_const : Measurable (fun _ : Ω0 => (2 : ℕ))))
  have hb : Measurable b0 := (measurable_const.add (hD2.comp hQ)).sqrt
  have hN : Measurable N0 := hW.add (hD1.comp hQ)
  have hd : Measurable d0 := hV.mul hb
  have hxd : Measurable (fun ω : Ω0 => x * V0 ω * b0 ω) :=
    (measurable_const.mul hV).mul hb
  have hZ : MeasurableSet Z0 := measurableSet_eq_fun hV measurable_const
  have hT : Measurable T0 := Measurable.ite hZ hκ (hN.div hd)
  have hF0 : MeasurableSet F0 := measurableSet_le hN hxd
  have hFl : MeasurableSet
      {ω : Ω0 | W0 ω + D1 (Q ω) < x * V0 ω * b0 ω} :=
    measurableSet_lt hN hxd
  have hFu : MeasurableSet
      {ω : Ω0 | x * V0 ω * b0 ω < W0 ω + D1 (Q ω)} :=
    measurableSet_lt hxd hN
  have hFuw : MeasurableSet
      {ω : Ω0 | x * V0 ω * b0 ω ≤ W0 ω + D1 (Q ω)} :=
    measurableSet_le hxd hN
  have hTc : MeasurableSet {ω : Ω0 | T0 ω ≤ x} :=
    measurableSet_le hT measurable_const
  have hTl : MeasurableSet {ω : Ω0 | T0 ω < x} :=
    measurableSet_lt hT measurable_const
  have hTu : MeasurableSet {ω : Ω0 | x < T0 ω} :=
    measurableSet_lt measurable_const hT
  have hTuw : MeasurableSet {ω : Ω0 | x ≤ T0 ω} :=
    measurableSet_le measurable_const hT
  have hComplementError (E : Set Ω0) (hE : MeasurableSet E) (a : ℝ) :
      |P.real Eᶜ - (1 - a)| = |P.real E - a| := by
    have he : P.real Eᶜ = 1 - P.real E := by
      simpa only [probReal_univ] using measureReal_compl (μ := P) hE
    rw [he, show (1 - P.real E) - (1 - a) = -(P.real E - a) by ring, abs_neg]
  have hgNeg (i : Fin n) : Measurable (gNeg i) := (hg i).neg
  have hgNeg2 (i : Fin n) :
      MemLp (fun ω : Ω0 => gNeg i (O i ω)) 2 P := (hg2 i).neg
  have hgNegMean (i : Fin n) : (∫ ω, gNeg i (O i ω) ∂P) = 0 := by
    change (∫ ω, -(g i (O i ω)) ∂P) = 0
    rw [integral_neg, hgmean i, neg_zero]
  have hgNegEnergy : (∑ i : Fin n, ∫ ω, (gNeg i (O i ω)) ^ 2 ∂P) = 1 := by
    simpa only [gNeg, neg_sq] using hgenergy
  have hD1Neg : Measurable D1Neg := hD1.neg
  have hκNeg : Measurable κNeg := hκ.neg
  have hD1NegA : ∀ᵐ ω ∂P, |D1Neg (fun i => O i ω)| ≤ Aenv (fun i => O i ω) := by
    simpa only [D1Neg, abs_neg] using hD1A
  have hWNeg (ω : Ω0) : WNeg ω = -(W0 ω) := by
    simp only [WNeg, ξNeg, gNeg, W0, ξ0, Finset.sum_neg_distrib]
  have hVNeg (ω : Ω0) : VNeg ω = V0 ω := by
    simp only [VNeg, ξNeg, gNeg, neg_sq, V0, ξ0]
  have hbNeg (ω : Ω0) : bNeg ω = b0 ω := rfl
  have hNNeg (ω : Ω0) : WNeg ω + D1Neg (Q ω) = -(W0 ω + D1 (Q ω)) := by
    rw [hWNeg ω]
    change -(W0 ω) + -(D1 (Q ω)) = -(W0 ω + D1 (Q ω))
    ring
  have hTNeg (ω : Ω0) : TNeg ω = -(T0 ω) := by
    by_cases hz : V0 ω = 0
    · simp only [TNeg, T0, hVNeg ω, hz, if_pos, κNeg]
    · simp only [TNeg, T0, hVNeg ω, hz, if_neg, hNNeg ω, hbNeg ω]
      exact neg_div _ _
  have hZNeg : ZNeg = Z0 := by
    ext ω
    change (VNeg ω = 0) ↔ (V0 ω = 0)
    rw [hVNeg ω]
  have hpNeg : pNeg = p0 := by
    dsimp only [pNeg, p0]
    rw [hZNeg]
  have hFull0 : Integrable fullTest0 P := hFull
  have hFullNeg : Integrable fullTestNeg P := hFull0
  have hDeleted0 (i : Fin n) : Integrable (compactDeleted0 i) P := hDeleted i
  have hDeletedEq (i : Fin n) : compactDeletedNeg i = compactDeleted0 i := by
    funext ω
    simp only [compactDeletedNeg, compactDeleted0, ξNeg, gNeg, ξ0, abs_neg]
  have hDeletedNeg (i : Fin n) : Integrable (compactDeletedNeg i) P := by
    rw [hDeletedEq i]
    exact hDeleted0 i
  have hDeltaI (i : Fin n) : Integrable (deltaIntegrand0 i) P := by
    have hu : Measurable (fun ω : Ω0 => (1 + r) * ξ0 i ω) :=
      measurable_const.mul (hξ i)
    have hm : Measurable (deltaIntegrand0 i) :=
      (hu.pow_const 2).mul ((continuous_abs.measurable.comp hu).min measurable_const)
    apply ((hg2 i).integrable_sq.const_mul ((1 + r) ^ 2)).mono' hm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      change ‖((1 + r) * ξ0 i ω) ^ 2 * min |(1 + r) * ξ0 i ω| 1‖ ≤
        (1 + r) ^ 2 * (ξ0 i ω) ^ 2
      have hmnonneg : 0 ≤ ((1 + r) * ξ0 i ω) ^ 2 * min |(1 + r) * ξ0 i ω| 1 :=
        mul_nonneg (sq_nonneg _) (le_min (abs_nonneg _) (by norm_num))
      rw [Real.norm_eq_abs, abs_of_nonneg hmnonneg]
      calc
        ((1 + r) * ξ0 i ω) ^ 2 * min |(1 + r) * ξ0 i ω| 1 ≤
            ((1 + r) * ξ0 i ω) ^ 2 := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (min_le_right |(1 + r) * ξ0 i ω| 1) (sq_nonneg ((1 + r) * ξ0 i ω))
        _ = (1 + r) ^ 2 * (ξ0 i ω) ^ 2 := mul_pow _ _ _
  have hDeltaIntegrandEq (i : Fin n) : deltaIntegrandNeg i = deltaIntegrand0 i := by
    funext ω
    simp only [deltaIntegrandNeg, deltaIntegrand0, ξNeg, gNeg, ξ0, mul_neg, neg_sq, abs_neg]
  have hDeltaINeg (i : Fin n) : Integrable (deltaIntegrandNeg i) P := by
    rw [hDeltaIntegrandEq i]
    exact hDeltaI i
  have hδNeg (i : Fin n) : δNeg i = δ0 i := by
    change (∫ ω, deltaIntegrandNeg i ω ∂P) = (∫ ω, deltaIntegrand0 i ω ∂P)
    rw [hDeltaIntegrandEq i]
  have hLNeg : LNeg = L0 := by
    change (∑ i : Fin n, δNeg i) = ∑ i : Fin n, δ0 i
    exact Finset.sum_congr rfl (fun i _ => hδNeg i)
  have hFullEq : fullTestNeg = fullTest0 := rfl
  have hDeletedIntegralEq :
      (∑ i : Fin n, ∫ ω, compactDeletedNeg i ω ∂P) =
        ∑ i : Fin n, ∫ ω, compactDeleted0 i ω ∂P := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hDeletedEq i]
  have hCostNeg : compactCostNeg = compactCost0 := by
    dsimp only [compactCostNeg, compactCost0]
    rw [hLNeg, hFullEq, hDeletedIntegralEq]
  have hLower :
      |P.real F0 - Shao.OQ4.standardNormalCDF x| ≤ C * compactCost0 ∧
      |P.real {ω : Ω0 | W0 ω + D1 (Q ω) < x * V0 ω * b0 ω} -
        Shao.OQ4.standardNormalCDF x| ≤ C * compactCost0 ∧
      |P.real {ω : Ω0 | T0 ω ≤ x} - Shao.OQ4.standardNormalCDF x| ≤
        C * compactCost0 + p0 ∧
      |P.real {ω : Ω0 | T0 ω < x} - Shao.OQ4.standardNormalCDF x| ≤
        C * compactCost0 + p0 := by
    by_cases hx : 0 ≤ x
    · have hrx : r = x := abs_of_nonneg hx
      have hUpperR :
          |P.real {ω : Ω0 | r * V0 ω * b0 ω < W0 ω + D1 (Q ω)} -
            (1 - Shao.OQ4.standardNormalCDF r)| ≤ C * compactCost0 ∧
          |P.real {ω : Ω0 | r * V0 ω * b0 ω ≤ W0 ω + D1 (Q ω)} -
            (1 - Shao.OQ4.standardNormalCDF r)| ≤ C * compactCost0 ∧
          |P.real {ω : Ω0 | r < T0 ω} - (1 - Shao.OQ4.standardNormalCDF r)| ≤
            C * compactCost0 + p0 ∧
          |P.real {ω : Ω0 | r ≤ T0 ω} - (1 - Shao.OQ4.standardNormalCDF r)| ≤
            C * compactCost0 + p0 := by
        exact Shao.OQ6.CompactTailBounds.ambient_weighted_ae_compact_tail_bounds
          C hSZ P n hn O hO hOindep g hg hg2 hgmean hgenergy
          D1 D2 Aenv Benv Adeleted Bdeleted hD1 hD2 hAenv hBenv hAdeleted hBdeleted
          hAnonneg hBnonneg hAdeletenonneg hBdeletenonneg hD1A hD2B hD2pos
          κ hκ r hr hFull0 hDeleted0
      have hUpperX :
          |P.real {ω : Ω0 | x * V0 ω * b0 ω < W0 ω + D1 (Q ω)} -
            (1 - Shao.OQ4.standardNormalCDF x)| ≤ C * compactCost0 ∧
          |P.real {ω : Ω0 | x * V0 ω * b0 ω ≤ W0 ω + D1 (Q ω)} -
            (1 - Shao.OQ4.standardNormalCDF x)| ≤ C * compactCost0 ∧
          |P.real {ω : Ω0 | x < T0 ω} - (1 - Shao.OQ4.standardNormalCDF x)| ≤
            C * compactCost0 + p0 ∧
          |P.real {ω : Ω0 | x ≤ T0 ω} - (1 - Shao.OQ4.standardNormalCDF x)| ≤
            C * compactCost0 + p0 := by
        simpa only [hrx] using hUpperR
      rcases hUpperX with ⟨hMu, hMuw, hQu, hQuw⟩
      have hdouble : 1 - (1 - Shao.OQ4.standardNormalCDF x) =
          Shao.OQ4.standardNormalCDF x := by ring
      refine ⟨?_, ?_, ?_, ?_⟩
      · have he : F0 =
            {ω : Ω0 | x * V0 ω * b0 ω < W0 ω + D1 (Q ω)}ᶜ := by
          ext ω
          simp only [F0, Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
        have herror := hComplementError _ hFu (1 - Shao.OQ4.standardNormalCDF x)
        rw [hdouble, ← he] at herror
        rw [herror]
        exact hMu
      · have he : {ω : Ω0 | W0 ω + D1 (Q ω) < x * V0 ω * b0 ω} =
            {ω : Ω0 | x * V0 ω * b0 ω ≤ W0 ω + D1 (Q ω)}ᶜ := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
        have herror := hComplementError _ hFuw (1 - Shao.OQ4.standardNormalCDF x)
        rw [hdouble, ← he] at herror
        rw [herror]
        exact hMuw
      · have he : {ω : Ω0 | T0 ω ≤ x} = {ω : Ω0 | x < T0 ω}ᶜ := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
        have herror := hComplementError _ hTu (1 - Shao.OQ4.standardNormalCDF x)
        rw [hdouble, ← he] at herror
        rw [herror]
        exact hQu
      · have he : {ω : Ω0 | T0 ω < x} = {ω : Ω0 | x ≤ T0 ω}ᶜ := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
        have herror := hComplementError _ hTuw (1 - Shao.OQ4.standardNormalCDF x)
        rw [hdouble, ← he] at herror
        rw [herror]
        exact hQuw
    · have hxlt : x < 0 := lt_of_not_ge hx
      have hrneg : r = -x := abs_of_neg hxlt
      have hxneg : x = -r := by rw [hrneg]; ring
      have hPhi : Shao.OQ4.standardNormalCDF x =
          1 - Shao.OQ4.standardNormalCDF r := by
        rw [hxneg]
        exact Shao.OQ4.standardNormalCDF_reflection r
      have hThreshold (ω : Ω0) :
          r * VNeg ω * bNeg ω = -(x * V0 ω * b0 ω) := by
        rw [hVNeg ω, hbNeg ω, hrneg]
        ring
      have hMStrict :
          {ω : Ω0 | r * VNeg ω * bNeg ω < WNeg ω + D1Neg (Q ω)} =
            {ω : Ω0 | W0 ω + D1 (Q ω) < x * V0 ω * b0 ω} := by
        ext ω
        change (r * VNeg ω * bNeg ω < WNeg ω + D1Neg (Q ω)) ↔
          (W0 ω + D1 (Q ω) < x * V0 ω * b0 ω)
        rw [hThreshold ω, hNNeg ω]
        exact neg_lt_neg_iff
      have hMClosed :
          {ω : Ω0 | r * VNeg ω * bNeg ω ≤ WNeg ω + D1Neg (Q ω)} = F0 := by
        ext ω
        change (r * VNeg ω * bNeg ω ≤ WNeg ω + D1Neg (Q ω)) ↔
          (W0 ω + D1 (Q ω) ≤ x * V0 ω * b0 ω)
        rw [hThreshold ω, hNNeg ω]
        exact neg_le_neg_iff
      have hQStrict : {ω : Ω0 | r < TNeg ω} = {ω : Ω0 | T0 ω < x} := by
        ext ω
        change (r < TNeg ω) ↔ (T0 ω < x)
        rw [hrneg, hTNeg ω]
        exact neg_lt_neg_iff
      have hQClosed : {ω : Ω0 | r ≤ TNeg ω} = {ω : Ω0 | T0 ω ≤ x} := by
        ext ω
        change (r ≤ TNeg ω) ↔ (T0 ω ≤ x)
        rw [hrneg, hTNeg ω]
        exact neg_le_neg_iff
      have hUpperNeg :
          |P.real {ω : Ω0 | r * VNeg ω * bNeg ω < WNeg ω + D1Neg (Q ω)} -
            (1 - Shao.OQ4.standardNormalCDF r)| ≤ C * compactCostNeg ∧
          |P.real {ω : Ω0 | r * VNeg ω * bNeg ω ≤ WNeg ω + D1Neg (Q ω)} -
            (1 - Shao.OQ4.standardNormalCDF r)| ≤ C * compactCostNeg ∧
          |P.real {ω : Ω0 | r < TNeg ω} - (1 - Shao.OQ4.standardNormalCDF r)| ≤
            C * compactCostNeg + pNeg ∧
          |P.real {ω : Ω0 | r ≤ TNeg ω} - (1 - Shao.OQ4.standardNormalCDF r)| ≤
            C * compactCostNeg + pNeg := by
        exact Shao.OQ6.CompactTailBounds.ambient_weighted_ae_compact_tail_bounds
          C hSZ P n hn O hO hOindep gNeg hgNeg hgNeg2 hgNegMean hgNegEnergy
          D1Neg D2 Aenv Benv Adeleted Bdeleted hD1Neg hD2 hAenv hBenv hAdeleted hBdeleted
          hAnonneg hBnonneg hAdeletenonneg hBdeletenonneg hD1NegA hD2B hD2pos
          κNeg hκNeg r hr hFullNeg hDeletedNeg
      rw [hMStrict, hMClosed, hQStrict, hQClosed, ← hPhi, hCostNeg, hpNeg] at hUpperNeg
      rcases hUpperNeg with ⟨hMs, hMc, hQs, hQc⟩
      exact ⟨hMc, hMs, hQc, hQs⟩
  rcases hLower with ⟨hMc, hMs, hQc, hQs⟩
  refine ⟨hMc, hMs, ?_, ?_, hQc, hQs, ?_, ?_⟩
  · have he : {ω : Ω0 | x * V0 ω * b0 ω < W0 ω + D1 (Q ω)} = F0ᶜ := by
      ext ω
      simp only [F0, Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    rw [he, hComplementError F0 hF0 (Shao.OQ4.standardNormalCDF x)]
    exact hMc
  · have he : {ω : Ω0 | x * V0 ω * b0 ω ≤ W0 ω + D1 (Q ω)} =
        {ω : Ω0 | W0 ω + D1 (Q ω) < x * V0 ω * b0 ω}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
    rw [he, hComplementError _ hFl (Shao.OQ4.standardNormalCDF x)]
    exact hMs
  · have he : {ω : Ω0 | x < T0 ω} = {ω : Ω0 | T0 ω ≤ x}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    rw [he, hComplementError _ hTc (Shao.OQ4.standardNormalCDF x)]
    exact hQc
  · have he : {ω : Ω0 | x ≤ T0 ω} = {ω : Ω0 | T0 ω < x}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
    rw [he, hComplementError _ hTl (Shao.OQ4.standardNormalCDF x)]
    exact hQs

end

end Shao.OQ6.SignedCompactCDFBounds
