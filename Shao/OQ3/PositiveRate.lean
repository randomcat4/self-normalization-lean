import Shao.OQ3.InverseTilt
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The actual discrete relative entropy and its strictly positive rate

Source: current/oq3/proofs/r1/report.md, lines 146-159.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U5a scope: 1de636f4c3d8cbd7d4fafd715ab8af5fad0e65e5d3a138d239c69b51a91d6eeb.
-/

namespace Shao.OQ3

open MeasureTheory
open scoped Matrix

noncomputable section

def saddleRate (ell q : ℝ) (w : AtomicIndex → ℝ) : ℝ :=
  ell * q + Real.log (inverseNormalizer ell w)

def originalAtomEntropy (ell : ℝ) (w : AtomicIndex → ℝ) : ℝ :=
  ∑' i, w i * Real.log (w i / (originalMeasure ell w).real {fixedAtom i})

theorem originalMeasure_ae_range (ell : ℝ) (w : AtomicIndex → ℝ) :
  ∀ᵐ x ∂originalMeasure ell w, x ∈ Set.range fixedAtom := by
  exact (tilted_absolutelyContinuous (atomicMeasure w)
    (fun x => -ell * normalValue x)).ae_le (atomicMeasure_ae_range w)

theorem atomicMeasure_normalValue (ell q : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) :
  Integrable normalValue (atomicMeasure w) ∧ (∫ x, normalValue x ∂atomicMeasure w) = q := by
  have hmass : HasSum w 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  let := atomicMeasure_isProbabilityMeasure w hw hmass
  have hY : Integrable normalValue (atomicMeasure w) := by
    apply integrable_continuous_of_fixed_bounds (atomicMeasure w)
      ((atomicMeasure_ae_bounds w).mono fun _ hx => hx.2)
    unfold normalValue
    fun_prop
  have hb : Integrable boundaryFeature (atomicMeasure w) ∧
      (∫ x, boundaryFeature x ∂atomicMeasure w) = 0 := by
    simpa [constraintFeature, constraintTarget] using atomicMeasure_constraints ell q w hw hm 1
  have hq : Integrable (fun x : ℝ => x ^ 2) (atomicMeasure w) ∧
      (∫ x, x ^ 2 ∂atomicMeasure w) = q := by
    simpa [constraintFeature, constraintTarget] using atomicMeasure_constraints ell q w hw hm 3
  refine ⟨hY, ?_⟩
  have hfun : normalValue = (fun x : ℝ => x ^ 2 - 2 * boundaryFeature x) := by
    funext x
    unfold normalValue boundaryFeature
    ring
  rw [hfun, integral_sub hq.1 (hb.1.const_mul 2), integral_const_mul, hq.2, hb.2]
  ring

theorem original_log_atom_ratio (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (i : AtomicIndex) (hi : 0 < w i) :
  Real.log (w i / (originalMeasure ell w).real {fixedAtom i}) =
    ell * normalValue (fixedAtom i) + Real.log (inverseNormalizer ell w) := by
  have hZ := inverseNormalizer_pos ell w hw hs
  have he := Real.exp_pos (-ell * normalValue (fixedAtom i))
  rw [originalMeasure_real_singleton ell w hw hs i]
  rw [Real.log_div hi.ne' (div_pos (mul_pos hi he) hZ).ne',
    Real.log_div (mul_pos hi he).ne' hZ.ne', Real.log_mul hi.ne' he.ne', Real.log_exp]
  ring

theorem originalAtomEntropy_hasSum (ell q : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 < w i)
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
    rw [original_log_atom_ratio ell w (fun i => (hw i).le) hmass i (hw i)]
    ring
  · unfold saddleRate
    ring

theorem originalAtomEntropy_eq (ell q : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 < w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) :
  originalAtomEntropy ell w = saddleRate ell q w := by
  exact (originalAtomEntropy_hasSum ell q w hw hm).tsum_eq

theorem inverseNormalizer_gt_exp_neg_mean (ell q : ℝ) (hell : ell ≠ 0)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 < w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) :
  Real.exp (-ell * q) < inverseNormalizer ell w := by
  have hnonneg := fun i => (hw i).le
  have hmass : HasSum w 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  let := atomicMeasure_isProbabilityMeasure w hnonneg hmass
  have hY := atomicMeasure_normalValue ell q w hnonneg hm
  have hf : Integrable (fun x => -ell * normalValue x) (atomicMeasure w) := hY.1.const_mul (-ell)
  have hg : Integrable (Real.exp ∘ fun x => -ell * normalValue x) (atomicMeasure w) :=
    inverseExp_integrable ell w hnonneg hmass
  have hsupp : ∀ᵐ x ∂atomicMeasure w, -ell * normalValue x ∈ (Set.univ : Set ℝ) :=
    Filter.Eventually.of_forall fun _ => Set.mem_univ _
  rcases strictConvexOn_exp.ae_eq_const_or_map_average_lt
    Real.continuous_exp.continuousOn isClosed_univ hsupp hf hg with hconst | hstrict
  · have hpoint (i : AtomicIndex) : -ell * normalValue (fixedAtom i) =
        ⨍ x, -ell * normalValue x ∂atomicMeasure w := by
      by_contra hbad
      have hsub : ({fixedAtom i} : Set ℝ) ⊆
          {x | -ell * normalValue x ≠ ⨍ y, -ell * normalValue y ∂atomicMeasure w} := by
        intro x hx
        obtain rfl := Set.mem_singleton_iff.mp hx
        exact hbad
      have hnull : atomicMeasure w
          {x | -ell * normalValue x ≠ ⨍ y, -ell * normalValue y ∂atomicMeasure w} = 0 :=
        ae_iff.mp hconst
      have hzero : atomicMeasure w {fixedAtom i} = 0 :=
        le_antisymm ((measure_mono hsub).trans_eq hnull) (by positivity)
      have hreal : w i = 0 := by
        rw [← atomicMeasure_real_singleton w hnonneg i]
        simp only [measureReal_def, hzero, ENNReal.toReal_zero]
      exact (ne_of_gt (hw i)) hreal
    have heq := (hpoint (Sum.inl 0)).trans (hpoint (Sum.inl 1)).symm
    norm_num [fixedAtom, baseAtom, normalValue] at heq
    exact False.elim (hell (by linarith))
  · simpa only [average_eq_integral, integral_const_mul, hY.2, inverseNormalizer] using hstrict

theorem saddleRate_pos (ell q : ℝ) (hell : ell ≠ 0) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 < w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) :
  0 < saddleRate ell q w := by
  have hmass : HasSum w 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  have hlog := Real.strictMonoOn_log (Real.exp_pos (-ell * q))
    (inverseNormalizer_pos ell w (fun i => (hw i).le) hmass)
    (inverseNormalizer_gt_exp_neg_mean ell q hell w hw hm)
  rw [Real.log_exp] at hlog
  unfold saddleRate
  linarith

theorem originalAtomEntropy_pos (ell q : ℝ) (hell : ell ≠ 0) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 < w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) :
  0 < originalAtomEntropy ell w := by
  rw [originalAtomEntropy_eq ell q w hw hm]
  exact saddleRate_pos ell q hell w hw hm

theorem exists_source_positive_entropy_family :
  ∃ (p : Fin 4 → ℝ) (q eps : ℝ), (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧
    0 < eps ∧ (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
    ∀ (r : ℕ → ℝ), (∀ j, 0 < r j) → Summable r → (∑' j, r j) < eps →
      IsProbabilityMeasure (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
      (Integrable (fun x : ℝ => x) (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
        (∫ x, x ∂originalMeasure sourceEll (limitingMass sourceEll p r)) = 0) ∧
      originalAtomEntropy sourceEll (limitingMass sourceEll p r) =
        saddleRate sourceEll q (limitingMass sourceEll p r) ∧
      0 < saddleRate sourceEll q (limitingMass sourceEll p r) ∧
      0 < originalAtomEntropy sourceEll (limitingMass sourceEll p r) := by
  obtain ⟨p, q, eps, hp, hlo, hhi, heps, hc, hfamily⟩ := exists_source_limit_family
  refine ⟨p, q, eps, hp, hlo, hhi, heps, hc, ?_⟩
  intro r hr hs ht
  obtain ⟨hpos, hm⟩ := hfamily r hr hs ht
  have hnonneg := fun i => (hpos i).le
  have hmass : HasSum (limitingMass sourceEll p r) 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  exact ⟨originalMeasure_isProbabilityMeasure _ _ hnonneg hmass,
    originalMeasure_centered sourceEll q _ hnonneg hm,
    originalAtomEntropy_eq sourceEll q _ hpos hm,
    saddleRate_pos sourceEll q sourceEll_pos.ne' _ hpos hm,
    originalAtomEntropy_pos sourceEll q sourceEll_pos.ne' _ hpos hm⟩

end
end Shao.OQ3
