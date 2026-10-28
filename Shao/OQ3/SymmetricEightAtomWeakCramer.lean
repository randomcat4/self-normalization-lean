import Shao.OQ3.SymmetricEightAtomCoordinateGaps
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Shao.OQ3
open MeasureTheory
noncomputable section

theorem symmetric_eight_atom_weak_cramer_of_coordinate_phase_bounds
    (a : Fin 8 → ℝ) (cL cQ TL TQ : ℝ)
    (hcL : 0 < cL) (hcQ : 0 < cQ) (hTL : 0 ≤ TL) (hTQ : 0 ≤ TQ)
    (hLinear : ∀ t : ℝ, TL < |t| → ∃ i : Fin 8,
      cL * Real.rpow |t| (-(3 : ℝ) / 8) ≤
        ‖jointPhase (2 * t) 0 (a i) - 1‖ ^ 2)
    (hQuadratic : ∀ t : ℝ, TQ < |t| → ∃ j : Fin 7,
      cQ * Real.rpow |t| (-(3 : ℝ) / 8) ≤
        ‖jointPhase 0 (2 * t) (a j.succ) - jointPhase 0 (2 * t) (a 0)‖ ^ 2) :
    let A : Fin (8 + 8) → ℝ := Fin.append a (fun i => -a i)
    let mu : Measure ℝ := Measure.sum fun k : Fin (8 + 8) =>
      ENNReal.ofReal ((1 : ℝ) / 16) • Measure.dirac (A k)
    ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, 0 ≤ R ∧ ∀ xi eta : ℝ,
      R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic mu xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-(3 : ℝ) / 8) := by
  intro A mu
  let c : ℝ := min (cL / 1024) (cQ / 4096)
  let R : ℝ := 2 * max TL TQ + 1
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hmax : 0 ≤ max TL TQ := le_trans hTL (le_max_left _ _)
  refine ⟨c, hc, R, by dsimp [R]; linarith, ?_⟩
  intro xi eta hR
  let r : ℝ := Real.sqrt (xi ^ 2 + eta ^ 2)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = xi ^ 2 + eta ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hRr : 2 * max TL TQ + 1 < r := hR
  have hr : 0 < r := by linarith
  have hx : |xi| ≤ r := by nlinarith [sq_abs xi, sq_nonneg eta, abs_nonneg xi]
  have hy : |eta| ≤ r := by nlinarith [sq_abs eta, sq_nonneg xi, abs_nonneg eta]
  have hLarge : r / 2 ≤ |xi| ∨ r / 2 ≤ |eta| := by
    by_contra hn
    have hsmall := not_or.mp hn
    have hxlt : |xi| < r / 2 := lt_of_not_ge hsmall.1
    have hylt : |eta| < r / 2 := lt_of_not_ge hsmall.2
    have hxp := mul_pos (sub_pos.mpr hxlt)
      (show 0 < r / 2 + |xi| by linarith [abs_nonneg xi])
    have hyp := mul_pos (sub_pos.mpr hylt)
      (show 0 < r / 2 + |eta| by linarith [abs_nonneg eta])
    nlinarith [sq_abs xi, sq_abs eta]
  have hGap := symmetric_eight_atom_coordinate_phase_gaps a xi eta
  have hrpow : 0 ≤ Real.rpow r (-(3 : ℝ) / 8) := Real.rpow_nonneg hr0 _
  rcases hLarge with hxi | heta
  · have ht : TL < |xi| := by have hm := le_max_left TL TQ; linarith
    have hxpos : 0 < |xi| := lt_of_le_of_lt hTL ht
    obtain ⟨i, hi⟩ := hLinear xi ht
    have hpow : Real.rpow r (-(3 : ℝ) / 8) ≤ Real.rpow |xi| (-(3 : ℝ) / 8) :=
      Real.rpow_le_rpow_of_nonpos hxpos hx (by norm_num)
    have hcoef : c ≤ cL / 1024 := min_le_left _ _
    have hsmall : c * Real.rpow r (-(3 : ℝ) / 8) ≤
        (cL / 1024) * Real.rpow |xi| (-(3 : ℝ) / 8) :=
      (mul_le_mul_of_nonneg_right hcoef hrpow).trans
        (mul_le_mul_of_nonneg_left hpow (by positivity))
    have hscaled := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 1 / 1024)
    have hactual := hGap.1 i
    change ‖jointCharacteristic mu xi eta‖ ≤ 1 - c * Real.rpow r (-(3 : ℝ) / 8)
    nlinarith
  · have ht : TQ < |eta| := by have hm := le_max_right TL TQ; linarith
    have hypos : 0 < |eta| := lt_of_le_of_lt hTQ ht
    obtain ⟨j, hj⟩ := hQuadratic eta ht
    have hpow : Real.rpow r (-(3 : ℝ) / 8) ≤ Real.rpow |eta| (-(3 : ℝ) / 8) :=
      Real.rpow_le_rpow_of_nonpos hypos hy (by norm_num)
    have hcoef : c ≤ cQ / 4096 := min_le_right _ _
    have hsmall : c * Real.rpow r (-(3 : ℝ) / 8) ≤
        (cQ / 4096) * Real.rpow |eta| (-(3 : ℝ) / 8) :=
      (mul_le_mul_of_nonneg_right hcoef hrpow).trans
        (mul_le_mul_of_nonneg_left hpow (by positivity))
    have hscaled := mul_le_mul_of_nonneg_left hj (by norm_num : (0 : ℝ) ≤ 1 / 4096)
    have hactual := hGap.2 j.succ 0
    change ‖jointCharacteristic mu xi eta‖ ≤ 1 - c * Real.rpow r (-(3 : ℝ) / 8)
    nlinarith

end
end Shao.OQ3
