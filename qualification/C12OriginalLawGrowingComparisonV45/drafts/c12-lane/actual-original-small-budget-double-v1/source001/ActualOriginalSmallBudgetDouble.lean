import Shao.C2.ActualRetainedConditionalComparison
import Shao.C2.ActualOriginalDoublePullback
import Shao.Probability.SourceNonresidualBrownian

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace Shao.C2.ActualOriginalSmallBudgetDouble
open MeasureTheory ProbabilityTheory Set
open Shao.C2.BridgeDomination
open scoped BigOperators NNReal Topology Classical

theorem iid_actual_original_small_budget_double_comparison :
    ∃ eta C : ℝ, 0 < eta ∧ 0 < C ∧
      ∀ {ΩB : Type*} [MeasurableSpace ΩB]
        (Bm : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
        IsBrownianReal Bm PB →
        ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu]
          (n : ℕ) (hn : 0 < n)
          (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
          (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
          (hmean : (∫ z : ℝ, z ∂nu) = 0)
          (x : ℝ), 1 ≤ x → Shao.truncationBudget nu n x ≤ eta →
          |(Measure.pi (fun _ : Fin n => nu)).real (Shao.C2.doubleCrossing hn x) -
              PB.real {omega |
                (∃ s : BridgeTime, x ≤ Bm ⟨(s : ℝ), s.property.1⟩ omega) ∧
                ∃ s : BridgeTime, Bm ⟨(s : ℝ), s.property.1⟩ omega ≤ -x}| ≤
            C * Shao.truncationBudget nu n x * Shao.standardNormalTail x := by
  obtain ⟨epsilon, etaC, Cc, hepsilon, hepsilonCap, hetaC, hCc, hConditional⟩ :=
    Shao.C2.ActualRetainedConditionalComparison.source_truncation_actual_retained_double_comparison
  obtain ⟨Co, hCo, hPullback⟩ :=
    Shao.C2.ActualOriginalDoublePullback.source_truncation_original_double_pullback
  let eta : ℝ := min etaC (epsilon ^ 3 / 8)
  have heta : 0 < eta := lt_min hetaC (div_pos (pow_pos hepsilon 3) (by norm_num))
  refine ⟨eta, Cc + Co / epsilon ^ 3, heta, by positivity, ?_⟩
  intro ΩB _ Bm PB _ hBrownian nu _ n hn h2 hnorm hmean x hx hR
  let R : ℝ := Shao.truncationBudget nu n x
  let cutoff : ℝ := epsilon / (1 + x)
  let rho : Measure ℝ := ProbabilityTheory.cond nu {z | |z| ≤ cutoff}
  let P0 : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
  let N : Set (Shao.Path n) := {w | ∀ j : Fin n, |w j| ≤ cutoff}
  let p : ℝ := P0.real N
  let DB : Set ΩB := {omega |
    (∃ s : BridgeTime, x ≤ Bm ⟨(s : ℝ), s.property.1⟩ omega) ∧
      ∃ s : BridgeTime, Bm ⟨(s : ℝ), s.property.1⟩ omega ≤ -x}
  let d : ℝ := PB.real DB
  have hxpos : 0 < x := by linarith only [hx]
  have hRconditional : R ≤ etaC := hR.trans (min_le_left _ _)
  have hRcut : R ≤ epsilon ^ 3 / 8 := hR.trans (min_le_right _ _)
  have hComparison := hConditional Bm PB hBrownian nu n hn h2 hnorm hmean x hx hRconditional
  have hRho : IsProbabilityMeasure rho := hComparison.1
  letI : IsProbabilityMeasure rho := hRho
  have hCompared := hComparison.2
  change |P.real (Shao.C2.doubleCrossing hn x) - d| ≤
    Cc * R * Shao.standardNormalTail x at hCompared
  have hBrownianData :=
    Shao.Probability.SourceNonresidualBrownian.actual_brownian_weak_double_crossing
      Bm PB hBrownian x hxpos
  have hd0 : 0 ≤ d := hBrownianData.2.2.2.2.2.1
  have hd2 : d ≤ 2 * Shao.standardNormalTail x := hBrownianData.2.2.2.2.2.2.1
  rcases hPullback nu n hn h2 hmean hnorm x epsilon hxpos hepsilon hepsilonCap hRcut with
    ⟨hpLower, hpUpper, _hpRemoved, _hRho, _hP, _hConditionedProduct, hRest⟩
  change (7 / 8 : ℝ) ≤ p at hpLower
  change p ≤ 1 at hpUpper
  have hp0 : 0 ≤ p := by linarith only [hpLower]
  have hResidual := (hRest d hd0 hd2).2.2.2
  change |(P0.real (Shao.C2.doubleCrossing hn x) - d) -
      p * (P.real (Shao.C2.doubleCrossing hn x) - d)| ≤
        Co / epsilon ^ 3 * R * Shao.standardNormalTail x at hResidual
  have hCenteredPaid : |p * (P.real (Shao.C2.doubleCrossing hn x) - d)| ≤
      Cc * R * Shao.standardNormalTail x := by
    calc
      |p * (P.real (Shao.C2.doubleCrossing hn x) - d)| =
          p * |P.real (Shao.C2.doubleCrossing hn x) - d| := by
        rw [abs_mul, abs_of_nonneg hp0]
      _ ≤ 1 * |P.real (Shao.C2.doubleCrossing hn x) - d| :=
        mul_le_mul_of_nonneg_right hpUpper (abs_nonneg _)
      _ ≤ Cc * R * Shao.standardNormalTail x := by
        simpa only [one_mul] using hCompared
  change |P0.real (Shao.C2.doubleCrossing hn x) - d| ≤
    (Cc + Co / epsilon ^ 3) * R * Shao.standardNormalTail x
  calc
    |P0.real (Shao.C2.doubleCrossing hn x) - d| =
        |((P0.real (Shao.C2.doubleCrossing hn x) - d) -
            p * (P.real (Shao.C2.doubleCrossing hn x) - d)) +
          p * (P.real (Shao.C2.doubleCrossing hn x) - d)| := by
      congr 1
      ring
    _ ≤ |(P0.real (Shao.C2.doubleCrossing hn x) - d) -
          p * (P.real (Shao.C2.doubleCrossing hn x) - d)| +
        |p * (P.real (Shao.C2.doubleCrossing hn x) - d)| := abs_add _ _
    _ ≤ Co / epsilon ^ 3 * R * Shao.standardNormalTail x +
        Cc * R * Shao.standardNormalTail x := add_le_add hResidual hCenteredPaid
    _ = (Cc + Co / epsilon ^ 3) * R * Shao.standardNormalTail x := by ring

end Shao.C2.ActualOriginalSmallBudgetDouble
