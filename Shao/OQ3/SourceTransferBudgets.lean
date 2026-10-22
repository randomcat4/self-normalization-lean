import Shao.OQ3.AdaptiveTailBudget
import Shao.OQ3.CorrectedScaleContinuity
import Shao.OQ3.SampleChangeOfMeasure

/-!
# Actual source-law budgets chosen before the future mass sequence

Source: current/oq3/proofs/r1/report.md, lines 499-550.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U11e scope: 0297c95b00d0ef8dacf55ad9acb41849592b68b16c3bebb7c7b71b012dc55346.
The finite-stage witness condition remains an explicit input.
-/

namespace Shao.OQ3

open MeasureTheory
open scoped Matrix

noncomputable section

private def prefixZero (J : ℕ) (u : Fin J → ℝ) (j : ℕ) : ℝ :=
  if h : j < J then u ⟨j, h⟩ else 0

private theorem prefixZero_nonneg (J : ℕ) (u : Fin J → ℝ) (hu : ∀ i, 0 ≤ u i) :
    ∀ j, 0 ≤ prefixZero J u j := by
  intro j
  unfold prefixZero
  split_ifs with h
  · exact hu ⟨j, h⟩
  · exact le_rfl

private theorem prefixZero_hasSum (J : ℕ) (u : Fin J → ℝ) :
    HasSum (prefixZero J u) (∑ i, u i) := by
  classical
  have hh : HasSum (prefixZero J u) (∑ j ∈ Finset.range J, prefixZero J u j) := by
    apply hasSum_sum_of_ne_finset_zero
    intro j hj
    have hnot : ¬j < J := by simpa only [Finset.mem_range] using hj
    simp [prefixZero, hnot]
  convert hh using 1
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl (fun i _ => by simp [prefixZero, i.isLt])

private theorem finiteMass_eq_of_same_prefix (ell : ℝ) (p : Fin 4 → ℝ)
    (s r : ℕ → ℝ) (J : ℕ) (hpref : ∀ j : Fin J, s j.val = r j.val) :
    finiteMass ell p s J = finiteMass ell p r J := by
  have hm : addedMoment ell (fun j : Fin J => addedAtom j.val) (fun j => s j.val) =
      addedMoment ell (fun j : Fin J => addedAtom j.val) (fun j => r j.val) := by
    funext k
    unfold addedMoment
    exact Finset.sum_congr rfl (fun j _ => by dsimp only; rw [hpref j])
  have hb : finiteBase ell p s J = finiteBase ell p r J := by
    unfold finiteBase compensatedBase
    rw [hm]
  funext i
  cases i with
  | inl i => change finiteBase ell p s J i = finiteBase ell p r J i; rw [hb]
  | inr j =>
    change (if j < J then s j else 0) = if j < J then r j else 0
    by_cases hj : j < J
    · simp [hj, hpref ⟨j, hj⟩]
    · simp [hj]

theorem exists_source_transfer_caps :
  ∃ (p : Fin 4 → ℝ) (q eps : ℝ),
    (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧ 0 < eps ∧
    (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
    (∀ (r : ℕ → ℝ), (∀ j, 0 < r j) → Summable r → (∑' j, r j) < eps →
      (∀ i, 0 < limitingBase sourceEll p r i) ∧
      ∀ J : ℕ, ∀ i, 0 < finiteBase sourceEll p r J i) ∧
    ∀ (eta : ℕ → ℝ), (∀ J, 0 < eta J) →
      ∃ cap : (J : ℕ) → (Fin J → ℝ) → ℕ → ℝ,
        (∀ (J : ℕ) (u : Fin J → ℝ),
          (∀ i, 0 < u i) → (∑ i, u i) < eps → ∀ n : ℕ, 0 < cap J u n) ∧
        ∀ (J : ℕ) (u : Fin J → ℝ),
          (∀ i, 0 < u i) → (∑ i, u i) < eps → ∀ (n : ℕ) (r : ℕ → ℝ),
          (∀ j, 0 < r j) → Summable r → (∑' j, r j) < eps →
          (∀ i : Fin J, r i.val = u i) → (∑' j, r (J + j)) < cap J u n →
            |normalizedTailCoefficient sourceEll q (limitingMass sourceEll p r) n -
              normalizedTailCoefficient sourceEll q (finiteMass sourceEll p r J) n| < eta J ∧
            |correctedInverseScale sourceEll q (atomicMeasure (limitingMass sourceEll p r)) -
              correctedInverseScale sourceEll q (atomicMeasure (finiteMass sourceEll p r J))| < eta J := by
  classical
  obtain ⟨p, q, hp, hlo, hhi, hc⟩ := exists_source_starter
  obtain ⟨epsf, hef, hfinite⟩ := exists_uniform_finite_radius sourceEll sourceEll_pos.le p hp
  obtain ⟨epsl, hel, hlimit⟩ := exists_limiting_radius sourceEll sourceEll_pos.le p hp
  let eps := min epsf epsl
  have hfinite' (r : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (hs : Summable r)
      (ht : (∑' j, r j) < eps) : ∀ J i, 0 < finiteBase sourceEll p r J i :=
    hfinite r hr hs (ht.trans_le (min_le_left _ _))
  have hlimit' (r : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (hs : Summable r)
      (ht : (∑' j, r j) < eps) : ∀ i, 0 < limitingBase sourceEll p r i := by
    intro i
    exact (half_pos (hp i)).trans_le (hlimit r hr hs (ht.trans_le (min_le_right _ _)) i)
  refine ⟨p, q, eps, hp, hlo, hhi, lt_min hef hel, hc, ?_, ?_⟩
  · intro r hr hs ht
    exact ⟨hlimit' r (fun j => (hr j).le) hs ht,
      hfinite' r (fun j => (hr j).le) hs ht⟩
  · intro eta heta
    have hlocal (J : ℕ) (u : Fin J → ℝ) (hu : ∀ i, 0 < u i)
        (hsu : (∑ i, u i) < eps) (n : ℕ) :
        ∃ c : ℝ, 0 < c ∧ ∀ (r : ℕ → ℝ),
          (∀ j, 0 < r j) → Summable r → (∑' j, r j) < eps →
          (∀ i : Fin J, r i.val = u i) → (∑' j, r (J + j)) < c →
            |normalizedTailCoefficient sourceEll q (limitingMass sourceEll p r) n -
              normalizedTailCoefficient sourceEll q (finiteMass sourceEll p r J) n| < eta J ∧
            |correctedInverseScale sourceEll q (atomicMeasure (limitingMass sourceEll p r)) -
              correctedInverseScale sourceEll q (atomicMeasure (finiteMass sourceEll p r J))| < eta J := by
      let r0 := prefixZero J u
      have hr0 : ∀ j, 0 ≤ r0 j := prefixZero_nonneg J u (fun i => (hu i).le)
      have hs0 : HasSum r0 (∑ i, u i) := prefixZero_hasSum J u
      have ht0 : (∑' j, r0 j) < eps := by rw [hs0.tsum_eq]; exact hsu
      have hp0 := hfinite' r0 hr0 hs0.summable ht0 J
      have hw0 := finiteMass_nonneg sourceEll p r0 J (fun i => (hp0 i).le) hr0
      have hm0 := finiteMass_constraints sourceEll q p r0 J source_constraintMatrix_nonsingular hc
      have hR := source_atomic_corrected_radicand_pos q hlo hhi
        (finiteMass sourceEll p r0 J) hw0 (fun i => hp0 i) hm0
      obtain ⟨cscale, hcscale, hscale⟩ := exists_corrected_scale_future_tail_cap
        sourceEll sourceEll_pos q (by linarith) p r0 hr0 J source_constraintMatrix_nonsingular
        hc (fun i => (hp0 i).le) hR (eta J) (heta J)
      let K : ℝ := Real.sqrt (2 * Real.pi * (n : ℝ)) *
        Real.exp (11 * sourceEll * (n : ℝ)) * (n : ℝ) * compensationTailConstant sourceEll
      have hC := compensationTailConstant_pos sourceEll
      have hK : 0 ≤ K := by dsimp [K]; positivity
      have hK1 : 0 < K + 1 := by linarith
      refine ⟨min cscale (eta J / (K + 1)), lt_min hcscale (div_pos (heta J) hK1), ?_⟩
      intro r hr hs ht hpref htail
      have hnonneg := fun j => (hr j).le
      have hpl := hlimit' r hnonneg hs ht
      have hpj := hfinite' r hnonneg hs ht J
      have hprefix : ∀ i : Fin J, r i.val = r0 i.val := by
        intro i
        simpa only [r0, prefixZero, dite_eq_left i.isLt] using hpref i
      have heq := finiteMass_eq_of_same_prefix sourceEll p r r0 J hprefix
      have hscl := hscale r hnonneg hs hprefix (fun i => (hpl i).le)
        (htail.trans_le (min_le_left _ _))
      have hnormalized := finite_limit_normalized_tail_error_le sourceEll sourceEll_pos.le q
        (by linarith) p r hnonneg hs J source_constraintMatrix_nonsingular hc
        (fun i => (hpl i).le) (fun i => (hpj i).le) n
      have hT : 0 ≤ ∑' j, r (J + j) := tsum_nonneg fun j => hnonneg _
      have hstrict : (K + 1) * (∑' j, r (J + j)) < eta J := by
        nlinarith [(lt_div_iff₀ hK1).mp (htail.trans_le (min_le_right _ _))]
      refine ⟨?_, ?_⟩
      · change _ ≤ K * (∑' j, r (J + j)) at hnormalized
        exact hnormalized.trans_lt ((mul_le_mul_of_nonneg_right
          (by linarith : K ≤ K + 1) hT).trans_lt hstrict)
      · rw [heq]
        exact hscl.2
    let cap : (J : ℕ) → (Fin J → ℝ) → ℕ → ℝ := fun J u n =>
      if h : (∀ i, 0 < u i) ∧ (∑ i, u i) < eps then
        Classical.choose (hlocal J u h.1 h.2 n) else 1
    refine ⟨cap, ?_, ?_⟩
    · intro J u hu hsu n
      have hvalid : (∀ i, 0 < u i) ∧ (∑ i, u i) < eps := ⟨hu, hsu⟩
      simpa only [cap, dite_eq_left hvalid] using (Classical.choose_spec (hlocal J u hu hsu n)).1
    · intro J u hu hsu n r hr hs ht hpref htail
      have hvalid : (∀ i, 0 < u i) ∧ (∑ i, u i) < eps := ⟨hu, hsu⟩
      apply (Classical.choose_spec (hlocal J u hu hsu n)).2 r hr hs ht hpref
      simpa only [cap, dite_eq_left hvalid] using htail

theorem exists_source_mass_with_witness_and_transfer :
  ∃ (p : Fin 4 → ℝ) (q eps : ℝ),
    (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧ 0 < eps ∧
    (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
    ∀ (eta : ℕ → ℝ), (∀ J, 0 < eta J) →
      ∀ (W : (J : ℕ) → (Fin J → ℝ) → ℕ → Prop),
        (∀ (J : ℕ) (u : Fin J → ℝ),
          (∀ i, 0 < u i) → (∑ i, u i) < eps → ∃ n : ℕ, W J u n) →
        ∃ chooseN : (J : ℕ) → (Fin J → ℝ) → ℕ,
          (∀ (J : ℕ) (u : Fin J → ℝ),
            (∀ i, 0 < u i) → (∑ i, u i) < eps → W J u (chooseN J u)) ∧
          ∃ r : ℕ → ℝ, (∀ j, 0 < r j) ∧ Summable r ∧ (∑' j, r j) < eps ∧
            IsProbabilityMeasure (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
            (Integrable (fun x : ℝ => x) (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
              (∫ x : ℝ, x ∂originalMeasure sourceEll (limitingMass sourceEll p r)) = 0) ∧
            ∀ J : ℕ,
              W J (fun i : Fin J => r i.val) (chooseN J (fun i : Fin J => r i.val)) ∧
              |normalizedTailCoefficient sourceEll q (limitingMass sourceEll p r)
                  (chooseN J (fun i : Fin J => r i.val)) -
                normalizedTailCoefficient sourceEll q (finiteMass sourceEll p r J)
                  (chooseN J (fun i : Fin J => r i.val))| < eta J ∧
              |correctedInverseScale sourceEll q (atomicMeasure (limitingMass sourceEll p r)) -
                correctedInverseScale sourceEll q (atomicMeasure (finiteMass sourceEll p r J))| < eta J := by
  obtain ⟨p, q, eps, hp, hlo, hhi, heps, hc, hfamily, hcaps⟩ := exists_source_transfer_caps
  refine ⟨p, q, eps, hp, hlo, hhi, heps, hc, ?_⟩
  intro eta heta W hW
  obtain ⟨cap, hcap, herror⟩ := hcaps eta heta
  obtain ⟨chooseN, hn, r, hr, hs, ht, htail⟩ :=
    exists_witness_first_positive_mass_with_tail_caps eps heps W hW cap
      (fun J u hu hsu n _ => hcap J u hu hsu n)
  obtain ⟨hpl, _⟩ := hfamily r hr hs ht
  have hnonneg := fun j => (hr j).le
  have hwl : ∀ i, 0 ≤ limitingMass sourceEll p r i := by
    intro i
    cases i with
    | inl i => exact (hpl i).le
    | inr j => exact hnonneg j
  have hm := limitingMoment_hasSum sourceEll q sourceEll_pos.le p r
    source_constraintMatrix_nonsingular hc hnonneg hs
  have hmass : HasSum (limitingMass sourceEll p r) 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  refine ⟨chooseN, hn, r, hr, hs, ht,
    originalMeasure_isProbabilityMeasure _ _ hwl hmass,
    originalMeasure_centered sourceEll q _ hwl hm, ?_⟩
  intro J
  have hpos : ∀ i : Fin J, 0 < r i.val := fun i => hr i.val
  have hsum : (∑ i : Fin J, r i.val) < eps := by
    rw [Fin.sum_univ_eq_sum_range]
    exact (hs.sum_le_tsum (Finset.range J) (fun j _ => hnonneg j)).trans_lt ht
  have herr := herror J (fun i : Fin J => r i.val) hpos hsum
    (chooseN J (fun i : Fin J => r i.val)) r hr hs ht (fun _ => rfl) (htail J)
  exact ⟨hn J _ hpos hsum, herr⟩

end
end Shao.OQ3
