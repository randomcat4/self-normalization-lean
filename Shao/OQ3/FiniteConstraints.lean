import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# Finite four-constraint compensation for the OQ3 tilted law

Source: current/oq3/proofs/r1/report.md, lines 18-25, 66-130.
Source SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen interface: first-unit-scope.md SHA256
68a0774f95291674f025c355c7a84ef20c9b11e27e1cca88ffb9861d9f035257.

These are finite real-weight identities and positivity estimates for pi_J.
They do not construct the original inverse-tilted law or the final fixed-law
counterexample. The actual starter and matrix nonsingularity remain U2 inputs.
-/

namespace Shao.OQ3

open scoped Matrix

noncomputable section

def normalValue (x : ℝ) : ℝ := 8 * x - x ^ 2

def boundaryFeature (x : ℝ) : ℝ := x ^ 2 - 4 * x

def centeringFeature (ell x : ℝ) : ℝ :=
  x * Real.exp (-ell * normalValue x)

def constraintFeature (ell x : ℝ) : Fin 4 → ℝ :=
  ![1, boundaryFeature x, centeringFeature ell x, x ^ 2]

def constraintTarget (q : ℝ) : Fin 4 → ℝ := ![1, 0, 0, q]

def baseAtom : Fin 4 → ℝ := ![-1, 1, 4 + Real.sqrt 10, 2]

def constraintMatrix (ell : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun k i => constraintFeature ell (baseAtom i) k

def dyadicMesh (j : ℕ) : ℝ := ((2 : ℝ) ^ j)⁻¹

def addedAtom (k : ℕ) : ℝ :=
  4 + Real.sqrt (10 - dyadicMesh (k + 1))

def addedMoment {J : ℕ} (ell : ℝ) (x r : Fin J → ℝ) : Fin 4 → ℝ :=
  fun k => ∑ j, r j * constraintFeature ell (x j) k

def compensatedBase {J : ℕ} (ell : ℝ)
    (p : Fin 4 → ℝ) (x r : Fin J → ℝ) : Fin 4 → ℝ :=
  p - (constraintMatrix ell)⁻¹ *ᵥ addedMoment ell x r

def stageAtom {J : ℕ} (x : Fin J → ℝ) : Fin 4 ⊕ Fin J → ℝ :=
  Sum.elim baseAtom x

def stageWeight {J : ℕ} (ell : ℝ)
    (p : Fin 4 → ℝ) (x r : Fin J → ℝ) : Fin 4 ⊕ Fin J → ℝ :=
  Sum.elim (compensatedBase ell p x r) r

def stageMoment {J : ℕ} (ell : ℝ) (x : Fin J → ℝ)
    (w : Fin 4 ⊕ Fin J → ℝ) : Fin 4 → ℝ :=
  fun k => ∑ i, w i * constraintFeature ell (stageAtom x i) k

theorem compensated_stageMoment {J : ℕ} (ell q : ℝ)
    (p : Fin 4 → ℝ) (x r : Fin J → ℝ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hp : (constraintMatrix ell) *ᵥ p = constraintTarget q) :
    stageMoment ell x (stageWeight ell p x r) = constraintTarget q := by
  have hsplit : stageMoment ell x (stageWeight ell p x r) =
      (constraintMatrix ell) *ᵥ compensatedBase ell p x r +
        addedMoment ell x r := by
    ext k
    simp [stageMoment, stageWeight, stageAtom, Fintype.sum_sum_type,
      constraintMatrix, Matrix.mulVec, dotProduct, addedMoment, mul_comm]
  rw [hsplit, compensatedBase, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec, hp]
  exact sub_add_cancel _ _

theorem compensatedBase_pos {J : ℕ} (ell : ℝ)
    (p : Fin 4 → ℝ) (x r : Fin J → ℝ)
    (hsmall : ∀ i, |((constraintMatrix ell)⁻¹ *ᵥ
      addedMoment ell x r) i| < p i) :
    ∀ i, 0 < compensatedBase ell p x r i := by
  intro i
  exact sub_pos.mpr ((le_abs_self _).trans_lt (hsmall i))

theorem stageWeight_pos {J : ℕ} (ell : ℝ)
    (p : Fin 4 → ℝ) (x r : Fin J → ℝ)
    (hsmall : ∀ i, |((constraintMatrix ell)⁻¹ *ᵥ
      addedMoment ell x r) i| < p i)
    (hr : ∀ j, 0 < r j) :
    ∀ i, 0 < stageWeight ell p x r i := by
  intro i
  cases i with
  | inl i => exact compensatedBase_pos ell p x r hsmall i
  | inr j => exact hr j

theorem exists_compensation_radius (ell : ℝ) (p : Fin 4 → ℝ)
    (hp : ∀ i, 0 < p i) (B : ℝ) (hB : 0 ≤ B) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ (J : ℕ) (x r : Fin J → ℝ),
      (∀ j, 0 ≤ r j) →
      (∀ j k, |constraintFeature ell (x j) k| ≤ B) →
      (∑ j, r j) < eps →
      ∀ i, 0 < compensatedBase ell p x r i := by
  let m : ℝ := min (min (p 0) (p 1)) (min (p 2) (p 3))
  have hm : 0 < m := lt_min (lt_min (hp 0) (hp 1)) (lt_min (hp 2) (hp 3))
  have hmi : ∀ i, m ≤ p i := by
    intro i
    fin_cases i
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  let A := (constraintMatrix ell)⁻¹
  let S : ℝ := ∑ i : Fin 4, ∑ k : Fin 4, |A i k|
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hrow : ∀ i, (∑ k, |A i k|) ≤ S := by
    intro i
    exact Finset.single_le_sum
      (fun j _ => Finset.sum_nonneg fun k _ => abs_nonneg (A j k)) (Finset.mem_univ i)
  have hden : 0 < 1 + B * S := by positivity
  refine ⟨m / (1 + B * S), div_pos hm hden, ?_⟩
  intro J x r hr hx ht
  have htotal : 0 ≤ ∑ j, r j := Finset.sum_nonneg fun j _ => hr j
  have hprod : B * S * (∑ j, r j) < m := by
    have h := (lt_div_iff₀ hden).mp ht
    nlinarith
  have hv : ∀ k, |addedMoment ell x r k| ≤ B * (∑ j, r j) := by
    intro k
    calc
      |addedMoment ell x r k| ≤ ∑ j, |r j * constraintFeature ell (x j) k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, r j * B := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_of_nonneg (hr j)]
        exact mul_le_mul_of_nonneg_left (hx j k) (hr j)
      _ = B * (∑ j, r j) := by rw [← Finset.sum_mul]; ring
  apply compensatedBase_pos ell p x r
  intro i
  have hc : |(A *ᵥ addedMoment ell x r) i| ≤ B * S * (∑ j, r j) := by
    calc
      |(A *ᵥ addedMoment ell x r) i| ≤ ∑ k, |A i k * addedMoment ell x r k| :=
        by simpa only [Matrix.mulVec, dotProduct] using
          (Finset.abs_sum_le_sum_abs
            (fun k : Fin 4 => A i k * addedMoment ell x r k) Finset.univ)
      _ ≤ ∑ k, |A i k| * (B * (∑ j, r j)) := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hv k) (abs_nonneg _)
      _ = (∑ k, |A i k|) * (B * (∑ j, r j)) := (Finset.sum_mul _ _ _).symm
      _ ≤ S * (B * (∑ j, r j)) :=
        mul_le_mul_of_nonneg_right (hrow i) (mul_nonneg hB htotal)
      _ = B * S * (∑ j, r j) := by ring
  exact hc.trans_lt (hprod.trans_le (hmi i))

theorem stage_mass_one {J : ℕ} (ell q : ℝ)
    (p : Fin 4 → ℝ) (x r : Fin J → ℝ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hp : (constraintMatrix ell) *ᵥ p = constraintTarget q) :
    (∑ i, stageWeight ell p x r i) = 1 := by
  simpa [stageMoment, constraintFeature, constraintTarget] using
    congrFun (compensated_stageMoment ell q p x r hM hp) (0 : Fin 4)

theorem stage_boundary_moment {J : ℕ} (ell q : ℝ)
    (p : Fin 4 → ℝ) (x r : Fin J → ℝ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hp : (constraintMatrix ell) *ᵥ p = constraintTarget q) :
    (∑ i, stageWeight ell p x r i * stageAtom x i) = q / 4 := by
  let w := stageWeight ell p x r
  have h := compensated_stageMoment ell q p x r hM hp
  have h1 : (∑ i, w i * ((stageAtom x i) ^ 2 - 4 * stageAtom x i)) = 0 := by
    simpa [stageMoment, constraintFeature, constraintTarget, boundaryFeature, w] using
      congrFun h (1 : Fin 4)
  have h3 : (∑ i, w i * (stageAtom x i) ^ 2) = q := by
    simpa [stageMoment, constraintFeature, constraintTarget, w] using
      congrFun h (3 : Fin 4)
  have hpoly : (∑ i, w i * ((stageAtom x i) ^ 2 - 4 * stageAtom x i)) =
      (∑ i, w i * (stageAtom x i) ^ 2) - 4 * (∑ i, w i * stageAtom x i) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hpoly, h3] at h1
  change (∑ i, w i * stageAtom x i) = q / 4
  linarith

private theorem dyadicMesh_pos (j : ℕ) : 0 < dyadicMesh j := by
  unfold dyadicMesh
  positivity

private theorem dyadicMesh_le_one (j : ℕ) : dyadicMesh j ≤ 1 := by
  unfold dyadicMesh
  exact (inv_le_one₀ (by positivity)).mpr (one_le_pow₀ (by norm_num))

theorem addedAtom_normalValue (k : ℕ) :
    normalValue (addedAtom k) = 6 + dyadicMesh (k + 1) := by
  have hn : 0 ≤ 10 - dyadicMesh (k + 1) := by
    linarith [dyadicMesh_le_one (k + 1)]
  dsimp [normalValue, addedAtom]
  nlinarith [Real.sq_sqrt hn]

theorem addedAtom_gt_four (k : ℕ) : 4 < addedAtom k := by
  have hn : 0 < 10 - dyadicMesh (k + 1) := by
    linarith [dyadicMesh_le_one (k + 1)]
  have hs := Real.sqrt_pos.mpr hn
  dsimp [addedAtom]
  linarith

theorem addedAtom_lt_limit (k : ℕ) : addedAtom k < 4 + Real.sqrt 10 := by
  have hn : 0 ≤ 10 - dyadicMesh (k + 1) := by
    linarith [dyadicMesh_le_one (k + 1)]
  have hlt : 10 - dyadicMesh (k + 1) < 10 := by
    linarith [dyadicMesh_pos (k + 1)]
  simpa [addedAtom, add_comm] using add_lt_add_left (Real.sqrt_lt_sqrt hn hlt) 4

theorem addedAtom_injective : Function.Injective addedAtom := by
  intro m n h
  have he := congrArg normalValue h
  rw [addedAtom_normalValue, addedAtom_normalValue] at he
  have hmesh : dyadicMesh (m + 1) = dyadicMesh (n + 1) := by linarith
  have hpow : (2 : ℝ) ^ (m + 1) = (2 : ℝ) ^ (n + 1) := inv_injective hmesh
  have heq := (pow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).injective hpow
  exact Nat.add_right_cancel heq

theorem normalValue_baseAtom :
    (fun i => normalValue (baseAtom i)) = ![-9, 7, 6, 12] := by
  ext i
  fin_cases i <;> norm_num [normalValue, baseAtom]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]

end
end Shao.OQ3
