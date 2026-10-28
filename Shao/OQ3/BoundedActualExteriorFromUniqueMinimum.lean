import Shao.OQ3.SelfNormalizedLowEnergyExponentialBound
import Shao.OQ3.ActualHighEnergyExteriorRateGap
import Shao.OQ3.BoundedActualQuadraticExteriorExponentialBound
import Shao.OQ3.SampleParabolaTailDomain

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators Topology
noncomputable section

theorem bounded_actual_exterior_exponential_bound_of_unique_minimum
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (B : ℝ) (hB : 0 ≤ B) (hbounded : ∀ᵐ x ∂mu, |x| ≤ B)
    (level a0 rho J0 : ℝ) (hlevel : 0 < level) (hrho : 0 < rho) :
    let I : (ℝ × ℝ) → EReal :=
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
    let center : ℝ × ℝ := (a0, a0 ^ 2 / level ^ 2)
    let Tail : Set (ℝ × ℝ) := {w | 0 < w.2 ∧ level * Real.sqrt w.2 ≤ w.1}
    let U : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
      |w.1 ^ 2 / level ^ 2 - w.2| ≤ rho}
    I center = (J0 : EReal) →
      (∀ w ∈ Tail, I center ≤ I w ∧ (I w = I center ↔ w = center)) →
        ∃ delta : ℝ, 0 < delta ∧ ∃ C : ℝ, 0 < C ∧
          ∀ n : ℕ, 1 ≤ n →
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
            let M : Shao.Path n → (ℝ × ℝ) := fun z =>
              ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
            P.real (M ⁻¹' (Tail \ U)) ≤
              C * Real.exp (-(n : ℝ) * (J0 + delta)) := by
  classical
  intro I center Tail U hRate hUnique
  let R0 : ℝ := |J0| + 1
  have hR0 : 0 < R0 := by dsimp only [R0]; positivity
  obtain ⟨eta, heta, hLow⟩ :=
    exists_self_normalized_low_energy_arbitrary_exponential_bound mu level R0 hlevel hR0
  obtain ⟨deltaH, hdeltaH, hGap⟩ :=
    actual_high_energy_exterior_rate_gap_of_unique_minimum mu level a0 B eta rho J0
      heta hrho hRate hUnique
  let A : Set (ℝ × ℝ) := (Tail \ U) ∩ {w | eta ≤ w.2}
  obtain ⟨CH, hCH, hHigh⟩ := bounded_actual_quadratic_exterior_exponential_bound
    mu B hB hbounded A (J0 + deltaH) hGap
  let delta : ℝ := min deltaH (1 / 2)
  have hdelta : 0 < delta := lt_min hdeltaH (by norm_num)
  have hdeltaHle : delta ≤ deltaH := min_le_left _ _
  have hdeltaHalf : delta ≤ 1 / 2 := min_le_right _ _
  refine ⟨delta, hdelta, 1 + CH, by positivity, ?_⟩
  intro n hn P M
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  let T : Set (Shao.Path n) := {z | level * Real.sqrt (n : ℝ) ≤
    (if Shao.energy z = 0 then 0 else (∑ i : Fin n, z i) / Real.sqrt (Shao.energy z))}
  let Low : Set (Shao.Path n) := T ∩ {z | Shao.energy z ≤ eta * (n : ℝ)}
  have hLowN : P.real Low ≤ Real.exp (-R0 * (n : ℝ)) := hLow n hn
  have hHighN : P.real (M ⁻¹' A) ≤ CH * Real.exp (-(n : ℝ) * (J0 + deltaH)) :=
    hHigh n hn
  have hSub : M ⁻¹' (Tail \ U) ⊆ Low ∪ M ⁻¹' A := by
    intro z hz
    by_cases hl : Shao.energy z ≤ eta * (n : ℝ)
    · left
      exact ⟨(sample_self_normalized_tail_iff level hlevel n hn z).mpr hz.1, hl⟩
    · right
      refine ⟨hz, ?_⟩
      change eta ≤ Shao.energy z / (n : ℝ)
      exact (le_div_iff₀ hnpos).mpr (lt_of_not_ge hl).le
  have hR0big : J0 + delta ≤ R0 := by
    dsimp only [R0]
    linarith [le_abs_self J0]
  have hLowExp : Real.exp (-R0 * (n : ℝ)) ≤
      Real.exp (-(n : ℝ) * (J0 + delta)) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hR0big hnpos.le
    nlinarith only [hh]
  have hHighExp : Real.exp (-(n : ℝ) * (J0 + deltaH)) ≤
      Real.exp (-(n : ℝ) * (J0 + delta)) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hdeltaHle hnpos.le
    nlinarith only [hh]
  calc
    P.real (M ⁻¹' (Tail \ U)) ≤ P.real (Low ∪ M ⁻¹' A) :=
      measureReal_mono hSub (measure_ne_top P _)
    _ ≤ P.real Low + P.real (M ⁻¹' A) := measureReal_union_le _ _
    _ ≤ Real.exp (-R0 * (n : ℝ)) + CH * Real.exp (-(n : ℝ) * (J0 + deltaH)) :=
      add_le_add hLowN hHighN
    _ ≤ Real.exp (-(n : ℝ) * (J0 + delta)) +
        CH * Real.exp (-(n : ℝ) * (J0 + delta)) :=
      add_le_add hLowExp (mul_le_mul_of_nonneg_left hHighExp hCH.le)
    _ = (1 + CH) * Real.exp (-(n : ℝ) * (J0 + delta)) := by ring

end
end Shao.OQ3
