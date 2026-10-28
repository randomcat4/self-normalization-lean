import Shao.OQ3.RealRatioDiophantineAE
import Shao.OQ3.CoordinateSquareAffineAE

namespace Shao.OQ3
open MeasureTheory MeasureTheory.Measure
noncomputable section

theorem exists_positive_box_simultaneous_diophantine :
    ∃ r : Fin 7 → ℝ,
      (∀ j, 2 * ((j.val : ℝ) + 1) < r j ∧ r j < 2 * ((j.val : ℝ) + 1) + 1) ∧
      (∃ Q : ℝ, 0 ≤ Q ∧ ∀ q : ℤ, Q < |(q : ℝ)| → ∃ j : Fin 7, ∀ p : ℤ,
        Real.rpow |(q : ℝ)| (-(3 : ℝ) / 16) ≤ |(q : ℝ) * r j - (p : ℝ)|) ∧
      (∃ Q : ℝ, 0 ≤ Q ∧ ∀ q : ℤ, Q < |(q : ℝ)| → ∃ j : Fin 6, ∀ p : ℤ,
        Real.rpow |(q : ℝ)| (-(3 : ℝ) / 16) ≤
          |(q : ℝ) * ((r j.succ ^ 2 - 1) / (r 0 ^ 2 - 1)) - (p : ℝ)|) := by
  classical
  let D (n : ℕ) (v : Fin n → ℝ) : Prop :=
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ q : ℤ, Q < |(q : ℝ)| → ∃ j : Fin n, ∀ p : ℤ,
      Real.rpow |(q : ℝ)| (-(3 : ℝ) / 16) ≤ |(q : ℝ) * v j - (p : ℝ)|
  have h7 : ∀ᵐ r ∂(volume : Measure (Fin 7 → ℝ)), D 7 r :=
    real_ratio_diophantine_ae 7 (by norm_num)
  have hprod : ∀ᵐ z ∂(volume : Measure ℝ).prod (volume : Measure (Fin 6 → ℝ)),
      D 7 (Fin.cons z.1 z.2) := by
    have h := (measurePreserving_piFinSuccAbove (fun _ : Fin 7 => (volume : Measure ℝ)) (0 : Fin 7)).symm
    simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero] using h.quasiMeasurePreserving.ae h7
  have houter : ∀ᵐ a ∂(volume : Measure ℝ),
      ∀ᵐ v ∂(volume : Measure (Fin 6 → ℝ)), D 7 (Fin.cons a v) :=
    ae_ae_of_ae_prod hprod
  obtain ⟨a, ha, hlin⟩ := exists_mem_of_measure_ne_zero_of_ae
    (show (volume : Measure ℝ) (Set.Ioo 2 3) ≠ 0 by norm_num [Real.volume_Ioo])
    (ae_restrict_of_ae houter)
  have hden : a ^ 2 - 1 ≠ 0 := by nlinarith [ha.1]
  have h6 : ∀ᵐ v ∂(volume : Measure (Fin 6 → ℝ)), D 6 v :=
    real_ratio_diophantine_ae 6 (by norm_num)
  have hquad : ∀ᵐ v ∂(volume : Measure (Fin 6 → ℝ)), (∀ j, 0 < v j) →
      D 6 (fun j => (v j ^ 2 - 1) / (a ^ 2 - 1)) :=
    ae_coordinate_square_affine_preimage 6 1 (a ^ 2 - 1) hden (D 6) h6
  let box : Set (Fin 6 → ℝ) := Set.pi Set.univ (fun j =>
    Set.Ioo (2 * ((j.val : ℝ) + 2)) (2 * ((j.val : ℝ) + 2) + 1))
  have hbox : volume box ≠ 0 := by
    change volume (Set.pi Set.univ (fun j : Fin 6 =>
      Set.Ioo (2 * ((j.val : ℝ) + 2)) (2 * ((j.val : ℝ) + 2) + 1))) ≠ 0
    rw [volume_pi_pi]
    simp [Real.volume_Ioo]
  obtain ⟨v, hv, hgood⟩ := exists_mem_of_measure_ne_zero_of_ae hbox
    (ae_restrict_of_ae (hlin.and hquad))
  have hvj (j : Fin 6) : 2 * ((j.val : ℝ) + 2) < v j ∧
      v j < 2 * ((j.val : ℝ) + 2) + 1 := hv j (Set.mem_univ j)
  have hpos (j : Fin 6) : 0 < v j := by
    have hn : (0 : ℝ) ≤ j.val := by positivity
    linarith [(hvj j).1]
  refine ⟨Fin.cons a v, ?_, hgood.1, ?_⟩
  · intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa using ha
    · change 2 * (((k.val + 1 : ℕ) : ℝ) + 1) < v k ∧
        v k < 2 * (((k.val + 1 : ℕ) : ℝ) + 1) + 1
      push_cast
      constructor <;> linarith [(hvj k).1, (hvj k).2]
  · simpa only [Fin.cons_succ, Fin.cons_zero] using hgood.2 hpos

end
end Shao.OQ3
