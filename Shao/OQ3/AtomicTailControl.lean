import Shao.OQ3.FiniteStageMeasure

/-!
# Explicit weight error from a summable future tail

Source: current/oq3/proofs/r1/report.md, lines 122-135 and 516-520.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U11b scope: 5006fc0c25fcc4d37194006a18cc31116e13665cd7933804ecae47bfdedc8bd7.
These are weight L1 bounds. A measure total-variation bridge is separate.
-/

namespace Shao.OQ3

open scoped Matrix

noncomputable section

def compensationTailConstant (ell : ℝ) : ℝ :=
  (4 + Real.sqrt 10) ^ 2 *
    (∑ i : Fin 4, ∑ k : Fin 4, |(constraintMatrix ell)⁻¹ i k|) + 1

def atomicMassL1 (w v : AtomicIndex → ℝ) : ℝ :=
  ∑' i, |w i - v i|

theorem compensationTailConstant_pos (ell : ℝ) :
  0 < compensationTailConstant ell := by
  unfold compensationTailConstant
  have h : 0 ≤ ∑ i : Fin 4, ∑ k : Fin 4, |(constraintMatrix ell)⁻¹ i k| := by
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  positivity

theorem infiniteAddedMoment_sub_prefix (ell : ℝ) (hell : 0 ≤ ell) (r : ℕ → ℝ)
    (hr : ∀ j, 0 ≤ r j) (hs : Summable r) (J : ℕ) (k : Fin 4) :
  infiniteAddedMoment ell r k -
      (∑ j : Fin J, r j.val * constraintFeature ell (addedAtom j.val) k) =
    ∑' j, r (J + j) * constraintFeature ell (addedAtom (J + j)) k := by
  have h := Summable.sum_add_tsum_nat_add J (summable_addedFeature ell hell r hr hs k)
  rw [← Fin.sum_univ_eq_sum_range] at h
  simpa only [infiniteAddedMoment, Nat.add_comm, sub_eq_iff_eq_add, add_comm] using h.symm

theorem addedMoment_tail_abs_le (ell : ℝ) (hell : 0 ≤ ell) (r : ℕ → ℝ)
    (hr : ∀ j, 0 ≤ r j) (hs : Summable r) (J : ℕ) (k : Fin 4) :
  |∑' j, r (J + j) * constraintFeature ell (addedAtom (J + j)) k| ≤
    (4 + Real.sqrt 10) ^ 2 * (∑' j, r (J + j)) := by
  have hsr : Summable (fun j => r (J + j)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff J).mpr hs
  have hsf : Summable (fun j => r (J + j) *
      constraintFeature ell (addedAtom (J + j)) k) := by
    simpa only [Nat.add_comm] using
      (summable_nat_add_iff J).mpr (summable_addedFeature ell hell r hr hs k)
  calc
    |∑' j, r (J + j) * constraintFeature ell (addedAtom (J + j)) k| ≤
        ∑' j, |r (J + j) * constraintFeature ell (addedAtom (J + j)) k| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsf.norm
    _ ≤ ∑' j, (4 + Real.sqrt 10) ^ 2 * r (J + j) := by
      apply Summable.tsum_le_tsum _ hsf.abs (hsr.mul_left _)
      intro j
      rw [abs_mul, abs_of_nonneg (hr _)]
      exact (mul_le_mul_of_nonneg_left (addedAtom_feature_bound ell hell _ k)
        (hr _)).trans_eq (mul_comm _ _)
    _ = (4 + Real.sqrt 10) ^ 2 * (∑' j, r (J + j)) := tsum_mul_left

theorem limitingBase_sub_finiteBase_tail (ell : ℝ) (hell : 0 ≤ ell) (p : Fin 4 → ℝ)
    (r : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (hs : Summable r) (J : ℕ) (i : Fin 4) :
  limitingBase ell p r i - finiteBase ell p r J i =
    -(∑ k : Fin 4, (constraintMatrix ell)⁻¹ i k *
      (∑' j, r (J + j) * constraintFeature ell (addedAtom (J + j)) k)) := by
  simp_rw [← infiniteAddedMoment_sub_prefix ell hell r hr hs J]
  simp only [limitingBase, finiteBase, compensatedBase, Pi.sub_apply,
    Matrix.mulVec, dotProduct, addedMoment, mul_sub, Finset.sum_sub_distrib]
  ring

theorem limitingBase_finiteBase_l1_le (ell : ℝ) (hell : 0 ≤ ell) (p : Fin 4 → ℝ)
    (r : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (hs : Summable r) (J : ℕ) :
  (∑ i : Fin 4, |limitingBase ell p r i - finiteBase ell p r J i|) ≤
    (compensationTailConstant ell - 1) * (∑' j, r (J + j)) := by
  have hi (i : Fin 4) : |limitingBase ell p r i - finiteBase ell p r J i| ≤
      ∑ k : Fin 4, |(constraintMatrix ell)⁻¹ i k| *
        ((4 + Real.sqrt 10) ^ 2 * (∑' j, r (J + j))) := by
    rw [limitingBase_sub_finiteBase_tail ell hell p r hr hs J i, abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro k _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (addedMoment_tail_abs_le ell hell r hr hs J k)
      (abs_nonneg _)
  calc
    (∑ i : Fin 4, |limitingBase ell p r i - finiteBase ell p r J i|) ≤
        ∑ i : Fin 4, ∑ k : Fin 4, |(constraintMatrix ell)⁻¹ i k| *
          ((4 + Real.sqrt 10) ^ 2 * (∑' j, r (J + j))) :=
      Finset.sum_le_sum fun i _ => hi i
    _ = (compensationTailConstant ell - 1) * (∑' j, r (J + j)) := by
      simp_rw [← Finset.sum_mul]
      unfold compensationTailConstant
      ring

theorem atomicMassL1_limiting_finite_hasSum (ell : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ)
    (hr : ∀ j, 0 ≤ r j) (hs : Summable r) (J : ℕ) :
  HasSum (fun i => |limitingMass ell p r i - finiteMass ell p r J i|)
    ((∑ i : Fin 4, |limitingBase ell p r i - finiteBase ell p r J i|) +
      (∑' j, r (J + j))) := by
  classical
  let f : ℕ → ℝ := fun j => if j < J then 0 else r j
  have hsr : Summable (fun j => r (J + j)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff J).mpr hs
  have hshift : HasSum (fun j => f (j + J)) (∑' j, r (J + j)) := by
    simpa [f, Nat.not_lt.mpr (Nat.le_add_left J _), Nat.add_comm] using hsr.hasSum
  have hf : HasSum f (∑' j, r (J + j)) := by
    have hprefix : (∑ j ∈ Finset.range J, f j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp [f, Finset.mem_range.mp hj]
    simpa only [hprefix, add_zero] using (hasSum_nat_add_iff J).mp hshift
  apply HasSum.sum
  · simpa [limitingMass, finiteMass, Function.comp_def] using
      hasSum_fintype (fun i : Fin 4 => |limitingBase ell p r i - finiteBase ell p r J i|)
  · convert hf using 1
    funext j
    dsimp [limitingMass, finiteMass, Function.comp_def, f]
    split_ifs with hj
    · simp
    · simp [abs_of_nonneg (hr j)]

theorem atomicMassL1_limiting_finite_le (ell : ℝ) (hell : 0 ≤ ell) (p : Fin 4 → ℝ)
    (r : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (hs : Summable r) (J : ℕ) :
  atomicMassL1 (limitingMass ell p r) (finiteMass ell p r J) ≤
    compensationTailConstant ell * (∑' j, r (J + j)) := by
  unfold atomicMassL1
  rw [(atomicMassL1_limiting_finite_hasSum ell p r hr hs J).tsum_eq]
  have h := limitingBase_finiteBase_l1_le ell hell p r hr hs J
  nlinarith

end
end Shao.OQ3
