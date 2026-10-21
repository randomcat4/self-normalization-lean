import Shao.OQ3.SourceStarter
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Summable atom weights with one fixed four-constraint target

Source: current/oq3/proofs/r1/report.md, lines 113-135.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U3a scope: 4841bac03aab4f42aeebf395308146d5198c832e964d1c05a815629a90f64893.
These are real weights and HasSum statements, not a probability-measure or
inverse-tilted-law construction.
-/

namespace Shao.OQ3

open scoped Matrix
open Filter

noncomputable section

abbrev AtomicIndex := Fin 4 ⊕ ℕ

def fixedAtom : AtomicIndex → ℝ := Sum.elim baseAtom addedAtom

def infiniteAddedMoment (ell : ℝ) (r : ℕ → ℝ) : Fin 4 → ℝ :=
  fun k => ∑' j, r j * constraintFeature ell (addedAtom j) k

def limitingBase (ell : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ) : Fin 4 → ℝ :=
  p - (constraintMatrix ell)⁻¹ *ᵥ infiniteAddedMoment ell r

def limitingMass (ell : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ) : AtomicIndex → ℝ :=
  Sum.elim (limitingBase ell p r) r

def finiteBase (ell : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ) (J : ℕ) : Fin 4 → ℝ :=
  compensatedBase ell p (fun i : Fin J => addedAtom i.val) (fun i : Fin J => r i.val)

theorem addedAtom_feature_bound (ell : ℝ) (hell : 0 ≤ ell) (j : ℕ) (k : Fin 4) :
    |constraintFeature ell (addedAtom j) k| ≤ (4 + Real.sqrt 10) ^ 2 := by
  let x := addedAtom j
  let beta := 4 + Real.sqrt 10
  have hx : 4 < x := addedAtom_gt_four j
  have hbeta : x < beta := addedAtom_lt_limit j
  have hbp : 4 ≤ beta := by dsimp [beta]; linarith [Real.sqrt_nonneg (10 : ℝ)]
  have hsq : x ^ 2 ≤ beta ^ 2 := by nlinarith
  have hm : 0 < dyadicMesh (j + 1) := by unfold dyadicMesh; positivity
  have hy : 0 ≤ normalValue x := by
    dsimp [x]
    rw [addedAtom_normalValue]
    linarith
  have he : Real.exp (-ell * normalValue x) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hell hy]
  have hep := Real.exp_pos (-ell * normalValue x)
  fin_cases k
  · change |(1 : ℝ)| ≤ beta ^ 2
    rw [abs_of_pos zero_lt_one]
    nlinarith
  · change |x ^ 2 - 4 * x| ≤ beta ^ 2
    rw [abs_of_nonneg (by nlinarith : 0 ≤ x ^ 2 - 4 * x)]
    nlinarith
  · change |x * Real.exp (-ell * normalValue x)| ≤ beta ^ 2
    rw [abs_of_nonneg (by positivity)]
    have hprod : x * Real.exp (-ell * normalValue x) ≤ x := by
      nlinarith [mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ x)]
    nlinarith
  · change |x ^ 2| ≤ beta ^ 2
    rw [abs_of_nonneg (sq_nonneg x)]
    exact hsq

theorem summable_addedFeature (ell : ℝ) (hell : 0 ≤ ell) (r : ℕ → ℝ)
    (hr : ∀ j, 0 ≤ r j) (hs : Summable r) (k : Fin 4) :
    Summable (fun j => r j * constraintFeature ell (addedAtom j) k) := by
  apply (hs.mul_right ((4 + Real.sqrt 10) ^ 2)).of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hr j)]
  exact mul_le_mul_of_nonneg_left (addedAtom_feature_bound ell hell j k) (hr j)

theorem finiteBase_tendsto (ell : ℝ) (hell : 0 ≤ ell) (p : Fin 4 → ℝ)
    (r : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (hs : Summable r) :
    Filter.Tendsto (finiteBase ell p r) Filter.atTop (nhds (limitingBase ell p r)) := by
  have hm (k : Fin 4) : Tendsto
      (fun J => ∑ j : Fin J, r j.val * constraintFeature ell (addedAtom j.val) k)
      atTop (nhds (infiniteAddedMoment ell r k)) := by
    have hfin (J : ℕ) :
        (∑ j : Fin J, r j.val * constraintFeature ell (addedAtom j.val) k) =
        ∑ j ∈ Finset.range J, r j * constraintFeature ell (addedAtom j) k :=
      Fin.sum_univ_eq_sum_range
        (fun j : ℕ => r j * constraintFeature ell (addedAtom j) k) J
    simp_rw [hfin]
    exact (summable_addedFeature ell hell r hr hs k).hasSum.tendsto_sum_nat
  apply tendsto_pi_nhds.mpr
  intro i
  have h0 := tendsto_const_nhds.mul (hm 0)
    (a := (constraintMatrix ell)⁻¹ i 0)
  have h1 := tendsto_const_nhds.mul (hm 1)
    (a := (constraintMatrix ell)⁻¹ i 1)
  have h2 := tendsto_const_nhds.mul (hm 2)
    (a := (constraintMatrix ell)⁻¹ i 2)
  have h3 := tendsto_const_nhds.mul (hm 3)
    (a := (constraintMatrix ell)⁻¹ i 3)
  simpa [finiteBase, compensatedBase, limitingBase, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, addedMoment] using
    (tendsto_const_nhds.sub (h0.add (h1.add (h2.add h3))) (a := p i))

theorem limitingMoment_hasSum (ell q : ℝ) (hell : 0 ≤ ell)
    (p : Fin 4 → ℝ) (r : ℕ → ℝ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hp : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hr : ∀ j, 0 ≤ r j) (hs : Summable r) (k : Fin 4) :
    HasSum (fun i => limitingMass ell p r i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k) := by
  have hv : (constraintMatrix ell) *ᵥ limitingBase ell p r + infiniteAddedMoment ell r =
      constraintTarget q := by
    rw [limitingBase, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec, hp]
    exact sub_add_cancel _ _
  have hsum : HasSum
      (fun i => limitingMass ell p r i * constraintFeature ell (fixedAtom i) k)
      (((constraintMatrix ell) *ᵥ limitingBase ell p r) k + infiniteAddedMoment ell r k) := by
    apply HasSum.sum
    · simpa [limitingMass, fixedAtom, Function.comp_def, constraintMatrix,
        Matrix.mulVec, dotProduct, mul_comm] using
        (hasSum_fintype (fun i : Fin 4 =>
          limitingBase ell p r i * constraintFeature ell (baseAtom i) k))
    · simpa [limitingMass, fixedAtom, Function.comp_def, infiniteAddedMoment] using
        (summable_addedFeature ell hell r hr hs k).hasSum
  exact congrFun hv k ▸ hsum

theorem exists_limiting_radius (ell : ℝ) (hell : 0 ≤ ell) (p : Fin 4 → ℝ)
    (hp : ∀ i, 0 < p i) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ (r : ℕ → ℝ),
      (∀ j, 0 ≤ r j) → Summable r → (∑' j, r j) < eps →
      ∀ i, p i / 2 ≤ limitingBase ell p r i := by
  obtain ⟨eps, heps, hrad⟩ := exists_compensation_radius ell (fun i => p i / 2)
    (fun i => half_pos (hp i)) ((4 + Real.sqrt 10) ^ 2) (sq_nonneg _)
  refine ⟨eps, heps, ?_⟩
  intro r hr hs ht i
  have hlower (J : ℕ) : p i / 2 ≤ finiteBase ell p r J i := by
    have hsum : (∑ j : Fin J, r j.val) < eps := by
      rw [Fin.sum_univ_eq_sum_range]
      exact (hs.sum_le_tsum (Finset.range J) (fun j _ => hr j)).trans_lt ht
    have hpos := hrad J (fun j => addedAtom j.val) (fun j => r j.val)
      (fun j => hr j.val) (fun j k => addedAtom_feature_bound ell hell j.val k) hsum i
    change 0 < p i / 2 -
      ((constraintMatrix ell)⁻¹ *ᵥ
        addedMoment ell (fun j : Fin J => addedAtom j.val) (fun j : Fin J => r j.val)) i at hpos
    change p i / 2 ≤ p i -
      ((constraintMatrix ell)⁻¹ *ᵥ
        addedMoment ell (fun j : Fin J => addedAtom j.val) (fun j : Fin J => r j.val)) i
    linarith
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds
    ((tendsto_pi_nhds.mp (finiteBase_tendsto ell hell p r hr hs)) i) hlower

theorem limitingMass_pos_of_lower (ell : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ)
    (hp : ∀ i, 0 < p i) (hr : ∀ j, 0 < r j)
    (hlower : ∀ i, p i / 2 ≤ limitingBase ell p r i) :
    ∀ i, 0 < limitingMass ell p r i := by
  intro i
  cases i with
  | inl i => exact (half_pos (hp i)).trans_le (hlower i)
  | inr j => exact hr j

theorem exists_source_limit_family :
    ∃ (p : Fin 4 → ℝ) (q eps : ℝ), (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧
      0 < eps ∧ (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
      ∀ (r : ℕ → ℝ), (∀ j, 0 < r j) → Summable r → (∑' j, r j) < eps →
        (∀ i, 0 < limitingMass sourceEll p r i) ∧
        (∀ k, HasSum (fun i => limitingMass sourceEll p r i *
          constraintFeature sourceEll (fixedAtom i) k) (constraintTarget q k)) := by
  obtain ⟨p, q, hp, hlo, hhi, hconstraint⟩ := exists_source_starter
  obtain ⟨eps, heps, hrad⟩ := exists_limiting_radius sourceEll sourceEll_pos.le p hp
  refine ⟨p, q, eps, hp, hlo, hhi, heps, hconstraint, ?_⟩
  intro r hr hs ht
  have hnonneg := fun j => (hr j).le
  exact ⟨limitingMass_pos_of_lower sourceEll p r hp hr (hrad r hnonneg hs ht),
    fun k => limitingMoment_hasSum sourceEll q sourceEll_pos.le p r
      source_constraintMatrix_nonsingular hconstraint hnonneg hs k⟩

theorem exists_positive_small_summable (eps : ℝ) (heps : 0 < eps) :
    ∃ r : ℕ → ℝ, (∀ j, 0 < r j) ∧ Summable r ∧ (∑' j, r j) < eps := by
  have hg := hasSum_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)
  have hsum : HasSum (fun j : ℕ => eps / 4 * (1 / 2) ^ j) (eps / 2) := by
    convert hg.mul_left (eps / 4) using 1
    norm_num
    ring
  refine ⟨fun j => eps / 4 * (1 / 2) ^ j, ?_, hsum.summable, ?_⟩
  · intro j
    positivity
  · rw [hsum.tsum_eq]
    linarith

theorem fixedAtom_injective : Function.Injective fixedAtom := by
  have hbase : Function.Injective baseAtom := by
    intro i j h
    fin_cases i <;> fin_cases j <;> norm_num [baseAtom] at * <;>
      nlinarith [Real.sqrt_nonneg (10 : ℝ)]
  have hcross (i : Fin 4) (j : ℕ) : baseAtom i ≠ addedAtom j := by
    have hlo := addedAtom_gt_four j
    have hhi := addedAtom_lt_limit j
    fin_cases i <;> norm_num [baseAtom] <;> intro h <;> linarith
  intro i j h
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (hbase h)
    | inr j => exact False.elim (hcross i j h)
  | inr i =>
    cases j with
    | inl j => exact False.elim (hcross j i h.symm)
    | inr j => exact congrArg Sum.inr (addedAtom_injective h)

theorem fixedAtom_bounds (i : AtomicIndex) :
    1 ≤ |fixedAtom i| ∧ |fixedAtom i| ≤ 4 + Real.sqrt 10 := by
  cases i with
  | inl i =>
    have hb : 0 ≤ 4 + Real.sqrt 10 := by positivity
    fin_cases i
    · norm_num [fixedAtom, baseAtom]
      linarith [Real.sqrt_nonneg (10 : ℝ)]
    · norm_num [fixedAtom, baseAtom]
      linarith [Real.sqrt_nonneg (10 : ℝ)]
    · change 1 ≤ |4 + Real.sqrt 10| ∧ |4 + Real.sqrt 10| ≤ 4 + Real.sqrt 10
      rw [abs_of_nonneg hb]
      exact ⟨by linarith [Real.sqrt_nonneg (10 : ℝ)], le_rfl⟩
    · norm_num [fixedAtom, baseAtom]
      linarith [Real.sqrt_nonneg (10 : ℝ)]
  | inr j =>
    have hlo := addedAtom_gt_four j
    have hhi := addedAtom_lt_limit j
    change 1 ≤ |addedAtom j| ∧ |addedAtom j| ≤ 4 + Real.sqrt 10
    rw [abs_of_pos (by linarith : 0 < addedAtom j)]
    exact ⟨by linarith, hhi.le⟩

end
end Shao.OQ3
