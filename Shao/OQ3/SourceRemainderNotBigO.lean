import Shao.OQ3.SourceFixedLawCounterexample
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Failure of the standard inverse-square-root remainder for one source law

Source: current/oq3/proofs/r1/report.md, equation (31), lines 539-558.
Source SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U20b scope: a52d7fe2fa52fd79c0476775c1760f5e6229f15bfa5696850f644a5898cb58d9.
-/

namespace Shao.OQ3

open MeasureTheory
open scoped Matrix Topology BigOperators

noncomputable section

private theorem not_isBigO_inv_sqrt_of_scaled_witness (f : ℕ → ℝ) (nseq : ℕ → ℕ)
    (htop : Filter.Tendsto nseq Filter.atTop Filter.atTop)
    (hn : ∀ J : ℕ, 0 < nseq J ∧ (J : ℝ) < Real.sqrt (nseq J : ℝ) * f (nseq J)) :
    ¬ Asymptotics.IsBigO Filter.atTop f (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) := by
  intro hO
  obtain ⟨B, hB⟩ := hO.bound
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (htop.eventually hB)
  obtain ⟨J, hJ⟩ := exists_nat_gt (max B (N : ℝ))
  have hNJ : N ≤ J := by
    exact_mod_cast (le_max_right B (N : ℝ)).trans hJ.le
  have hBJ : B < (J : ℝ) := (le_max_left B (N : ℝ)).trans_lt hJ
  have hs0 : 0 < (nseq J : ℝ) := by exact_mod_cast (hn J).1
  have hsqrt : 0 < Real.sqrt (nseq J : ℝ) := Real.sqrt_pos.mpr hs0
  have hnorm : |f (nseq J)| ≤ B * (Real.sqrt (nseq J : ℝ))⁻¹ := by
    simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqrt)] using hN J hNJ
  have hscalar : f (nseq J) ≤ B * (Real.sqrt (nseq J : ℝ))⁻¹ :=
    (le_abs_self _).trans hnorm
  have hscaled : Real.sqrt (nseq J : ℝ) * f (nseq J) ≤ B := by
    calc
      _ ≤ Real.sqrt (nseq J : ℝ) * (B * (Real.sqrt (nseq J : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_left hscalar hsqrt.le
      _ = B * (Real.sqrt (nseq J : ℝ) * (Real.sqrt (nseq J : ℝ))⁻¹) := by ring
      _ = B := by rw [mul_inv_cancel₀ hsqrt.ne', mul_one]
  linarith only [hBJ, (hn J).2, hscaled]

theorem exists_source_fixed_law_not_isBigO :
    ∃ (q : ℝ) (w : AtomicIndex → ℝ),
      1 < q ∧ q < 103 / 100 ∧ (∀ i, 0 < w i) ∧
      (∀ k : Fin 4,
        HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
          (constraintTarget q k)) ∧
      let P : Measure ℝ := originalMeasure sourceEll w
      let x0 : ℝ := Real.sqrt q / 4
      IsProbabilityMeasure P ∧
      (Integrable (fun x : ℝ => x) P ∧ (∫ x : ℝ, x ∂P) = 0) ∧
      (∀ᵐ x ∂P, 1 ≤ |x| ∧ |x| ≤ 4 + Real.sqrt 10) ∧
      0 < P.real (Set.Ioi 0) ∧
      (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 → ‖jointCharacteristic P xi eta‖ < 1) ∧
      Filter.Tendsto (fun J => |resonanceXi J| + |resonanceEta J|)
        Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun J => ‖jointCharacteristic P (resonanceXi J) (resonanceEta J)‖)
        Filter.atTop (nhds (1 : ℝ)) ∧
      0 < x0 ∧ x0 < 1 / 2 ∧ 0 < saddleRate sourceEll q w ∧
      0 < correctedInverseScale sourceEll q (atomicMeasure w) ∧
      (∃ nseq : ℕ → ℕ, StrictMono nseq ∧
        Filter.Tendsto nseq Filter.atTop Filter.atTop ∧
        ∀ J : ℕ, 0 < nseq J ∧
          (J : ℝ) < Real.sqrt (nseq J : ℝ) *
            (normalizedTailCoefficient sourceEll q w (nseq J) -
              correctedInverseScale sourceEll q (atomicMeasure w))) ∧
      ¬ Asymptotics.IsBigO Filter.atTop
        (fun n : ℕ => normalizedTailCoefficient sourceEll q w n -
          correctedInverseScale sourceEll q (atomicMeasure w))
        (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) := by
  obtain ⟨q, w, hq0, hq1, hw, hm, hprob, hcenter, hb, hpositive, hnonlattice,
      hescape, hresonance, hxpos, hxupper, hrate, hscale, nseq, hmono, htop, hn⟩ :=
    exists_source_fixed_law_counterexample
  refine ⟨q, w, hq0, hq1, hw, hm, hprob, hcenter, hb, hpositive, hnonlattice,
    hescape, hresonance, hxpos, hxupper, hrate, hscale, ⟨nseq, hmono, htop, hn⟩, ?_⟩
  exact not_isBigO_inv_sqrt_of_scaled_witness
    (fun n => normalizedTailCoefficient sourceEll q w n -
      correctedInverseScale sourceEll q (atomicMeasure w)) nseq htop hn

end
end Shao.OQ3
