import Mathlib.Analysis.InnerProductSpace.Basic

namespace Shao.OQ3
open scoped BigOperators
noncomputable section

theorem finite_weighted_unit_phase_gap
    (n : ℕ) (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hsum : ∑ k : Fin n, w k = 1)
    (z : Fin n → ℂ) (hz : ∀ k, ‖z k‖ = 1) :
    ∀ i j : Fin n,
      (w i * w j / 4) * ‖z i - z j‖ ^ 2 ≤
        1 - ‖∑ k : Fin n, w k • z k‖ := by
  classical
  let S : ℂ := ∑ k : Fin n, w k • z k
  have hcross : (∑ k : Fin n, ∑ l : Fin n,
      w k * w l * inner ℝ (z k) (z l)) = ‖S‖ ^ 2 := by
    calc
      _ = inner ℝ S S := by
        simp only [S, sum_inner, inner_sum, real_inner_smul_left,
          real_inner_smul_right]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = ‖S‖ ^ 2 := real_inner_self_eq_norm_sq S
  have hww : (∑ k : Fin n, ∑ l : Fin n, w k * w l) = 1 := by
    simp only [← Finset.mul_sum, hsum, mul_one]
  have hterm (k l : Fin n) : w k * w l * ‖z k - z l‖ ^ 2 =
      w k * w l + w k * w l - 2 * (w k * w l * inner ℝ (z k) (z l)) := by
    rw [norm_sub_sq_real, hz k, hz l]
    ring
  have hvar : (∑ k : Fin n, ∑ l : Fin n,
      w k * w l * ‖z k - z l‖ ^ 2) = 2 * (1 - ‖S‖ ^ 2) := by
    calc
      _ = (∑ k : Fin n, ∑ l : Fin n, w k * w l) +
          (∑ k : Fin n, ∑ l : Fin n, w k * w l) -
            2 * (∑ k : Fin n, ∑ l : Fin n, w k * w l * inner ℝ (z k) (z l)) := by
        simp_rw [hterm]
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      _ = 2 * (1 - ‖S‖ ^ 2) := by rw [hww, hcross]; ring
  intro i j
  have hnonneg (k l : Fin n) : 0 ≤ w k * w l * ‖z k - z l‖ ^ 2 :=
    mul_nonneg (mul_nonneg (hw k) (hw l)) (sq_nonneg _)
  have hinner : w i * w j * ‖z i - z j‖ ^ 2 ≤
      ∑ l : Fin n, w i * w l * ‖z i - z l‖ ^ 2 :=
    Finset.single_le_sum (fun l _ => hnonneg i l) (Finset.mem_univ j)
  have houter : (∑ l : Fin n, w i * w l * ‖z i - z l‖ ^ 2) ≤
      ∑ k : Fin n, ∑ l : Fin n, w k * w l * ‖z k - z l‖ ^ 2 :=
    Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => hnonneg k l))
      (Finset.mem_univ i)
  have hpair := hinner.trans houter
  rw [hvar] at hpair
  change (w i * w j / 4) * ‖z i - z j‖ ^ 2 ≤ 1 - ‖S‖
  nlinarith [sq_nonneg (‖S‖ - 1)]

end
end Shao.OQ3
