import Shao.OQ3.CompactActualQuadraticRateExponentialBound

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem bounded_actual_quadratic_exterior_exponential_bound
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (B : ℝ) (hB : 0 ≤ B) (hbounded : ∀ᵐ x ∂mu, |x| ≤ B)
    (A : Set (ℝ × ℝ)) (r : ℝ)
    (hgap : ∀ w ∈ (Set.Icc (-B) B ×ˢ Set.Icc 0 (B ^ 2)) ∩ closure A,
      (r : EReal) <
        Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
      let M : Shao.Path n → (ℝ × ℝ) := fun z =>
        ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
      P.real (M ⁻¹' A) ≤ C * Real.exp (-(n : ℝ) * r) := by
  let K : Set (ℝ × ℝ) := Set.Icc (-B) B ×ˢ Set.Icc 0 (B ^ 2)
  let S : Set (ℝ × ℝ) := K ∩ closure A
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hS : IsCompact S := hK.of_isClosed_subset
    (hK.isClosed.inter isClosed_closure) (fun _ hw => hw.1)
  obtain ⟨C, hC, hbound⟩ :=
    compact_actual_quadratic_rate_exponential_bound mu S hS r hgap
  refine ⟨C, hC, ?_⟩
  intro n hn
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
  let M : Shao.Path n → (ℝ × ℝ) := fun z =>
    ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
  change P.real (M ⁻¹' A) ≤ C * Real.exp (-(n : ℝ) * r)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hcoords : ∀ᵐ z ∂P, ∀ i : Fin n, |z i| ≤ B := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => mu) (i := i)).eventually hbounded
  have hcarrier : ∀ᵐ z ∂P, M z ∈ K := by
    filter_upwards [hcoords] with z hz
    have hlow : (∑ i : Fin n, -B) ≤ ∑ i : Fin n, z i :=
      Finset.sum_le_sum (fun i _ => (abs_le.mp (hz i)).1)
    have hhigh : (∑ i : Fin n, z i) ≤ ∑ _i : Fin n, B :=
      Finset.sum_le_sum (fun i _ => (abs_le.mp (hz i)).2)
    have hsq : ∀ i : Fin n, (z i) ^ 2 ≤ B ^ 2 := by
      intro i
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (z i)) hB).2 (hz i)
    have henergy : Shao.energy z ≤ ∑ _i : Fin n, B ^ 2 :=
      Finset.sum_le_sum (fun i _ => hsq i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at
      hlow hhigh henergy
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact (le_div_iff₀ hnpos).mpr (by simpa only [mul_comm] using hlow)
    · exact (div_le_iff₀ hnpos).mpr (by simpa only [mul_comm] using hhigh)
    · exact div_nonneg (Shao.energy_nonneg z) hnpos.le
    · exact (div_le_iff₀ hnpos).mpr (by simpa only [mul_comm] using henergy)
  have hsub : M ⁻¹' A ≤ᵐ[P] M ⁻¹' S := by
    filter_upwards [hcarrier] with z hz
    intro hA
    exact ⟨hz, subset_closure hA⟩
  have hprob : P.real (M ⁻¹' A) ≤ P.real (M ⁻¹' S) :=
    ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)
  exact hprob.trans (hbound n hn)

end
end Shao.OQ3
