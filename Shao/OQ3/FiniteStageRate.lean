import Shao.OQ3.PositiveRate
import Shao.OQ3.FiniteStageMeasure

/-!
# Positive entropy rates for nonnegative atomic weights and finite stages

Source: current/oq3/proofs/r1/report.md, lines 137-159 and 251-258.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U5b scope: f7d2180ec279d73d4775e3e92bb828a98d9d567eada6123198347b933bc57376.
-/

namespace Shao.OQ3

open MeasureTheory
open scoped Matrix

noncomputable section

theorem weighted_original_log_atom_ratio (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (i : AtomicIndex) :
  w i * Real.log (w i / (originalMeasure ell w).real {fixedAtom i}) =
    w i * (ell * normalValue (fixedAtom i) + Real.log (inverseNormalizer ell w)) := by
  by_cases hi : w i = 0
  · simp [hi]
  · rw [original_log_atom_ratio ell w hw hs i (lt_of_le_of_ne (hw i) (Ne.symm hi))]

theorem originalAtomEntropy_hasSum_of_nonneg (ell q : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) :
  HasSum (fun i => w i * Real.log (w i / (originalMeasure ell w).real {fixedAtom i}))
    (saddleRate ell q w) := by
  have hmass : HasSum w 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  have hb : HasSum (fun i => w i * boundaryFeature (fixedAtom i)) 0 := by
    simpa [constraintFeature, constraintTarget] using hm 1
  have hq : HasSum (fun i => w i * (fixedAtom i) ^ 2) q := by
    simpa [constraintFeature, constraintTarget] using hm 3
  have hY : HasSum (fun i => w i * normalValue (fixedAtom i)) q := by
    convert hq.sub (HasSum.mul_left 2 hb) using 1
    · funext i
      unfold normalValue boundaryFeature
      ring
    · ring
  have hsum := (HasSum.mul_left ell hY).add
    (HasSum.mul_right (Real.log (inverseNormalizer ell w)) hmass)
  convert hsum using 1
  · funext i
    rw [weighted_original_log_atom_ratio ell w hw hmass i]
    ring
  · unfold saddleRate
    ring

theorem originalAtomEntropy_eq_of_nonneg (ell q : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) :
  originalAtomEntropy ell w = saddleRate ell q w := by
  exact (originalAtomEntropy_hasSum_of_nonneg ell q w hw hm).tsum_eq

theorem inverseNormalizer_gt_exp_of_two_positive_atoms (ell q : ℝ) (hell : ell ≠ 0)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) (i j : AtomicIndex) (hi : 0 < w i) (hj : 0 < w j)
    (hne : normalValue (fixedAtom i) ≠ normalValue (fixedAtom j)) :
  Real.exp (-ell * q) < inverseNormalizer ell w := by
  have hmass : HasSum w 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  let := atomicMeasure_isProbabilityMeasure w hw hmass
  have hY := atomicMeasure_normalValue ell q w hw hm
  have hf : Integrable (fun x => -ell * normalValue x) (atomicMeasure w) := hY.1.const_mul (-ell)
  have hg : Integrable (Real.exp ∘ fun x => -ell * normalValue x) (atomicMeasure w) :=
    inverseExp_integrable ell w hw hmass
  have hsupp : ∀ᵐ x ∂atomicMeasure w, -ell * normalValue x ∈ (Set.univ : Set ℝ) :=
    Filter.Eventually.of_forall fun _ => Set.mem_univ _
  rcases strictConvexOn_exp.ae_eq_const_or_map_average_lt
    Real.continuous_exp.continuousOn isClosed_univ hsupp hf hg with hconst | hstrict
  · have hpoint (k : AtomicIndex) (hk : 0 < w k) : -ell * normalValue (fixedAtom k) =
        ⨍ x, -ell * normalValue x ∂atomicMeasure w := by
      by_contra hbad
      have hsub : ({fixedAtom k} : Set ℝ) ⊆
          {x | -ell * normalValue x ≠ ⨍ y, -ell * normalValue y ∂atomicMeasure w} := by
        intro x hx
        obtain rfl := Set.mem_singleton_iff.mp hx
        exact hbad
      have hnull : atomicMeasure w
          {x | -ell * normalValue x ≠ ⨍ y, -ell * normalValue y ∂atomicMeasure w} = 0 :=
        ae_iff.mp hconst
      have hzero : atomicMeasure w {fixedAtom k} = 0 :=
        le_antisymm ((measure_mono hsub).trans_eq hnull) (by positivity)
      have hreal : w k = 0 := by
        rw [← atomicMeasure_real_singleton w hw k]
        simp only [measureReal_def, hzero, ENNReal.toReal_zero]
      exact (ne_of_gt hk) hreal
    have heq := (hpoint i hi).trans (hpoint j hj).symm
    exact False.elim (hne (mul_left_cancel₀ (neg_ne_zero.mpr hell) heq))
  · simpa only [average_eq_integral, integral_const_mul, hY.2, inverseNormalizer] using hstrict

theorem entropy_rate_pos_of_two_positive_atoms (ell q : ℝ) (hell : ell ≠ 0)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) (i j : AtomicIndex) (hi : 0 < w i) (hj : 0 < w j)
    (hne : normalValue (fixedAtom i) ≠ normalValue (fixedAtom j)) :
  0 < saddleRate ell q w ∧ 0 < originalAtomEntropy ell w := by
  have hmass : HasSum w 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  have hlog := Real.strictMonoOn_log (Real.exp_pos (-ell * q))
    (inverseNormalizer_pos ell w hw hmass)
    (inverseNormalizer_gt_exp_of_two_positive_atoms ell q hell w hw hm i j hi hj hne)
  rw [Real.log_exp] at hlog
  have hrate : 0 < saddleRate ell q w := by
    unfold saddleRate
    linarith
  refine ⟨hrate, ?_⟩
  rw [originalAtomEntropy_eq_of_nonneg ell q w hw hm]
  exact hrate

theorem finite_original_entropy_rate (ell q : ℝ) (hell : ell ≠ 0)
    (p : Fin 4 → ℝ) (r : ℕ → ℝ) (J : ℕ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hp : ∀ i, 0 < finiteBase ell p r J i) (hr : ∀ j, 0 ≤ r j) :
  originalAtomEntropy ell (finiteMass ell p r J) = saddleRate ell q (finiteMass ell p r J) ∧
    0 < saddleRate ell q (finiteMass ell p r J) ∧
    0 < originalAtomEntropy ell (finiteMass ell p r J) := by
  have hw := finiteMass_nonneg ell p r J (fun i => (hp i).le) hr
  have hm := finiteMass_constraints ell q p r J hM hc
  have hi : 0 < finiteMass ell p r J (Sum.inl 0) := hp 0
  have hj : 0 < finiteMass ell p r J (Sum.inl 1) := hp 1
  have hne : normalValue (fixedAtom (Sum.inl 0)) ≠ normalValue (fixedAtom (Sum.inl 1)) := by
    norm_num [fixedAtom, baseAtom, normalValue]
  exact ⟨originalAtomEntropy_eq_of_nonneg ell q _ hw hm,
    entropy_rate_pos_of_two_positive_atoms ell q hell _ hw hm (Sum.inl 0) (Sum.inl 1) hi hj hne⟩

theorem exists_source_finite_and_limit_entropy_family :
  ∃ (p : Fin 4 → ℝ) (q eps : ℝ), (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧
    0 < eps ∧ (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
    ∀ (r : ℕ → ℝ), (∀ j, 0 < r j) → Summable r → (∑' j, r j) < eps →
      IsProbabilityMeasure (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
      (originalAtomEntropy sourceEll (limitingMass sourceEll p r) =
        saddleRate sourceEll q (limitingMass sourceEll p r) ∧
        0 < saddleRate sourceEll q (limitingMass sourceEll p r)) ∧
      ∀ J : ℕ, IsProbabilityMeasure (originalMeasure sourceEll (finiteMass sourceEll p r J)) ∧
        (originalAtomEntropy sourceEll (finiteMass sourceEll p r J) =
          saddleRate sourceEll q (finiteMass sourceEll p r J) ∧
          0 < saddleRate sourceEll q (finiteMass sourceEll p r J)) := by
  obtain ⟨p, q, eps, hp, hlo, hhi, heps, hc, hfamily⟩ := exists_source_finite_and_limit_family
  refine ⟨p, q, eps, hp, hlo, hhi, heps, hc, ?_⟩
  intro r hr hs ht
  obtain ⟨hpos, hm, hstages⟩ := hfamily r hr hs ht
  have hw := fun i => (hpos i).le
  have hmass : HasSum (limitingMass sourceEll p r) 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  refine ⟨originalMeasure_isProbabilityMeasure _ _ hw hmass,
    ⟨originalAtomEntropy_eq sourceEll q _ hpos hm,
      saddleRate_pos sourceEll q sourceEll_pos.ne' _ hpos hm⟩, ?_⟩
  intro J
  obtain ⟨hpJ, _, hprobJ, _, _⟩ := hstages J
  have hentropy := finite_original_entropy_rate sourceEll q sourceEll_pos.ne' p r J
    source_constraintMatrix_nonsingular hc hpJ (fun j => (hr j).le)
  exact ⟨hprobJ, hentropy.1, hentropy.2.1⟩

end
end Shao.OQ3
