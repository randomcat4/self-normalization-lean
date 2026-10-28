import Shao.OQ3.SelfNormalizedLowEnergyExponentialBound
import Shao.OQ3.SelfNormalizedHighEnergyExponentialBound
import Shao.OQ3.ActualHighEnergyExteriorRateGap
import Shao.OQ3.CompactParabolaRateProbability
import Shao.OQ3.SampleParabolaTailDomain
import Mathlib.Analysis.MeanInequalities

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators Topology
noncomputable section

theorem actual_exterior_exponential_bound_of_unique_minimum
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
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
  obtain ⟨Q, hQ, hHigh⟩ :=
    exists_self_normalized_high_energy_arbitrary_exponential_bound mu level R0 hlevel hR0
  let B : ℝ := Real.sqrt Q
  let Carrier : Set (ℝ × ℝ) := Set.Icc (-B) B ×ˢ Set.Icc 0 (B ^ 2)
  let A : Set (ℝ × ℝ) := (Tail \ U) ∩ {w | eta ≤ w.2}
  let F : Set (ℝ × ℝ) := Carrier ∩ closure A
  have hCarrier : IsCompact Carrier := isCompact_Icc.prod isCompact_Icc
  have hF : IsCompact F := hCarrier.of_isClosed_subset
    (hCarrier.isClosed.inter isClosed_closure) (fun _ hw => hw.1)
  obtain ⟨deltaH, hdeltaH, hGap⟩ :=
    actual_high_energy_exterior_rate_gap_of_unique_minimum mu level a0 B eta rho J0
      heta hrho hRate hUnique
  obtain ⟨Tests, hCM, _hCover, hMiddle⟩ :=
    compact_parabola_rate_probability_upper_bound mu F hF (J0 + deltaH) hGap
  let CM : ℝ := (Tests.card : ℝ) + 1
  have hCMpos : 0 < CM := hCM
  let delta : ℝ := min deltaH (1 / 2)
  have hdelta : 0 < delta := lt_min hdeltaH (by norm_num)
  have hdeltaHle : delta ≤ deltaH := min_le_left _ _
  have hdeltaHalf : delta ≤ 1 / 2 := min_le_right _ _
  refine ⟨delta, hdelta, 2 + CM, by positivity, ?_⟩
  intro n hn P M
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  let T : Set (Shao.Path n) := {z | level * Real.sqrt (n : ℝ) ≤
    (if Shao.energy z = 0 then 0 else (∑ i : Fin n, z i) / Real.sqrt (Shao.energy z))}
  let Low : Set (Shao.Path n) := T ∩ {z | Shao.energy z ≤ eta * (n : ℝ)}
  let High : Set (Shao.Path n) := T ∩ {z | Q * (n : ℝ) ≤ Shao.energy z}
  have hLowN : P.real Low ≤ Real.exp (-R0 * (n : ℝ)) := hLow n hn
  have hHighN : P.real High ≤ Real.exp (-R0 * (n : ℝ)) := hHigh n hn
  have hMiddleN : P.real (M ⁻¹' F) ≤ CM * Real.exp (-(n : ℝ) * (J0 + deltaH)) :=
    hMiddle n hn
  have hSub : M ⁻¹' (Tail \ U) ⊆ (Low ∪ High) ∪ M ⁻¹' F := by
    intro z hz
    have ht : z ∈ T := (sample_self_normalized_tail_iff level hlevel n hn z).mpr hz.1
    by_cases hl : Shao.energy z ≤ eta * (n : ℝ)
    · exact Or.inl (Or.inl ⟨ht, hl⟩)
    · by_cases hh : Q * (n : ℝ) ≤ Shao.energy z
      · exact Or.inl (Or.inr ⟨ht, hh⟩)
      · right
        have hEbound : Shao.energy z ≤ Q * (n : ℝ) := (lt_of_not_ge hh).le
        have hCauchy : (∑ i : Fin n, z i) ^ 2 ≤ (n : ℝ) * Shao.energy z := by
          have hc := Finset.sum_mul_sq_le_sq_mul_sq
            (Finset.univ : Finset (Fin n)) (fun _ : Fin n => (1 : ℝ)) z
          simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, mul_one] using hc
        have hSq : (M z).1 ^ 2 ≤ Q := by
          change ((∑ i : Fin n, z i) / (n : ℝ)) ^ 2 ≤ Q
          rw [div_pow]
          apply (div_le_iff₀ (sq_pos_of_pos hnpos)).mpr
          calc
            (∑ i : Fin n, z i) ^ 2 ≤ (n : ℝ) * Shao.energy z := hCauchy
            _ ≤ (n : ℝ) * (Q * (n : ℝ)) :=
              mul_le_mul_of_nonneg_left hEbound hnpos.le
            _ = Q * (n : ℝ) ^ 2 := by ring
        have habs : |(M z).1| ≤ B := by
          apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg Q)).mp
          simpa only [sq_abs, Real.sq_sqrt hQ.le] using hSq
        have hq0 : 0 ≤ (M z).2 := div_nonneg (Shao.energy_nonneg z) hnpos.le
        have hqB : (M z).2 ≤ B ^ 2 := by
          change Shao.energy z / (n : ℝ) ≤ (Real.sqrt Q) ^ 2
          rw [Real.sq_sqrt hQ.le]
          exact (div_le_iff₀ hnpos).mpr hEbound
        have hqEta : eta ≤ (M z).2 :=
          (le_div_iff₀ hnpos).mpr (lt_of_not_ge hl).le
        exact ⟨⟨abs_le.mp habs, hq0, hqB⟩, subset_closure ⟨hz, hqEta⟩⟩
  have hR0big : J0 + delta ≤ R0 := by
    dsimp only [R0]
    linarith [le_abs_self J0]
  have hRareExp : Real.exp (-R0 * (n : ℝ)) ≤
      Real.exp (-(n : ℝ) * (J0 + delta)) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hR0big hnpos.le
    nlinarith only [hh]
  have hMiddleExp : Real.exp (-(n : ℝ) * (J0 + deltaH)) ≤
      Real.exp (-(n : ℝ) * (J0 + delta)) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hdeltaHle hnpos.le
    nlinarith only [hh]
  calc
    P.real (M ⁻¹' (Tail \ U)) ≤ P.real ((Low ∪ High) ∪ M ⁻¹' F) :=
      measureReal_mono hSub (measure_ne_top P _)
    _ ≤ P.real (Low ∪ High) + P.real (M ⁻¹' F) := measureReal_union_le _ _
    _ ≤ (P.real Low + P.real High) + P.real (M ⁻¹' F) :=
      add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ (Real.exp (-R0 * (n : ℝ)) + Real.exp (-R0 * (n : ℝ))) +
        CM * Real.exp (-(n : ℝ) * (J0 + deltaH)) :=
      add_le_add (add_le_add hLowN hHighN) hMiddleN
    _ ≤ (Real.exp (-(n : ℝ) * (J0 + delta)) +
        Real.exp (-(n : ℝ) * (J0 + delta))) +
        CM * Real.exp (-(n : ℝ) * (J0 + delta)) :=
      add_le_add (add_le_add hRareExp hRareExp)
        (mul_le_mul_of_nonneg_left hMiddleExp hCMpos.le)
    _ = (2 + CM) * Real.exp (-(n : ℝ) * (J0 + delta)) := by ring

end
end Shao.OQ3
