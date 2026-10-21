import Shao.OQ3.AtomProjection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Nested integer phases at frequencies escaping to infinity

Source: current/oq3/proofs/r1/report.md, lines 113-119 and 279-291.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U6c scope: 2eeae98c41b0eb3d7256182c84c61b8538b2ff24ace1e06a5eca2abc248e33fb.
-/

namespace Shao.OQ3

open Filter

noncomputable section

def resonanceXi (J : ℕ) : ℝ := 16 * Real.pi * (2 : ℝ) ^ J

def resonanceEta (J : ℕ) : ℝ := -2 * Real.pi * (2 : ℝ) ^ J

private theorem scaled_base_integer (J : ℕ) (i : Fin 4) :
    ∃ m : ℤ, (2 : ℝ) ^ J * normalValue (baseAtom i) = (m : ℝ) := by
  refine ⟨(2 : ℤ) ^ J * ![-9, 7, 6, 12] i, ?_⟩
  rw [congrFun normalValue_baseAtom i]
  fin_cases i <;> norm_num

private theorem scaled_added_integer (J j : ℕ) (hj : j + 1 ≤ J) :
    ∃ m : ℤ, (2 : ℝ) ^ J * normalValue (addedAtom j) = (m : ℝ) := by
  refine ⟨6 * (2 : ℤ) ^ J + (2 : ℤ) ^ (J - (j + 1)), ?_⟩
  have hp : (2 : ℝ) ^ J = (2 : ℝ) ^ (J - (j + 1)) * (2 : ℝ) ^ (j + 1) := by
    rw [← pow_add, Nat.sub_add_cancel hj]
  have hne : (2 : ℝ) ^ (j + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcancel : (2 : ℝ) ^ J * ((2 : ℝ) ^ (j + 1))⁻¹ =
      (2 : ℝ) ^ (J - (j + 1)) := by
    rw [hp, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  rw [addedAtom_normalValue, dyadicMesh]
  push_cast
  rw [mul_add, hcancel]
  ring

theorem stageAtom_normalValue_scaled_integer (J : ℕ) (i : Fin 4 ⊕ Fin J) :
    ∃ m : ℤ, (2 : ℝ) ^ J * normalValue
      (stageAtom (fun j : Fin J => addedAtom j.val) i) = (m : ℝ) := by
  cases i with
  | inl i => exact scaled_base_integer J i
  | inr j => exact scaled_added_integer J j.val (by omega)

theorem fixedAtom_eventually_scaled_integer (i : AtomicIndex) :
    ∀ᶠ J in Filter.atTop, ∃ m : ℤ,
      (2 : ℝ) ^ J * normalValue (fixedAtom i) = (m : ℝ) := by
  cases i with
  | inl i => exact Filter.Eventually.of_forall fun J => scaled_base_integer J i
  | inr j =>
    filter_upwards [eventually_ge_atTop (j + 1)] with J hJ
    exact scaled_added_integer J j hJ

theorem resonance_phase_normalValue (J : ℕ) (x : ℝ) :
    resonanceXi J * x + resonanceEta J * x ^ 2 =
      (2 * Real.pi) * (2 : ℝ) ^ J * normalValue x := by
  unfold resonanceXi resonanceEta normalValue
  ring

theorem resonance_frequency_escape :
    Filter.Tendsto (fun J => |resonanceXi J| + |resonanceEta J|)
      Filter.atTop Filter.atTop := by
  have hQ : Tendsto (fun J : ℕ => (2 : ℝ) ^ J) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  refine tendsto_atTop.2 ?_
  intro b
  have hbound : ∀ᶠ J in atTop, b / (16 * Real.pi) ≤ (2 : ℝ) ^ J :=
    hQ.eventually (eventually_ge_atTop _)
  filter_upwards [hbound] with J hJ
  have hc : 0 < 16 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hxi : b ≤ resonanceXi J := by
    simpa only [resonanceXi, mul_comm] using (div_le_iff₀ hc).mp hJ
  exact hxi.trans ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _)))

theorem fixedAtom_eventually_resonant (i : AtomicIndex) :
    ∀ᶠ J in Filter.atTop, ∃ m : ℤ,
      resonanceXi J * fixedAtom i + resonanceEta J * (fixedAtom i) ^ 2 =
        (2 * Real.pi) * (m : ℝ) := by
  filter_upwards [fixedAtom_eventually_scaled_integer i] with J hJ
  obtain ⟨m, hm⟩ := hJ
  refine ⟨m, ?_⟩
  rw [resonance_phase_normalValue, mul_assoc, hm]

end
end Shao.OQ3
