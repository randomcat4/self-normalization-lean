import Shao.OQ3.SourceFixedLawRemainder
import Shao.OQ3.ResonantLimit

/-!
# One final source law with increasing remainder witnesses

Source: current/oq3/proofs/r1/report.md, lines 137-159, 259-305, 486-558.
Source SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U20a scope: baf7463955fcf1cb3ae1d7211fa6167346b6469cde93a67fa51265f99f3a81e3.
-/

namespace Shao.OQ3

open MeasureTheory
open scoped Matrix Topology BigOperators

noncomputable section

private theorem increasing_remainder_witnesses (G : ℕ → ℝ)
    (h : ∀ (K : ℝ) (N : ℕ), ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ K < G n) :
    ∃ nseq : ℕ → ℕ, StrictMono nseq ∧
      Filter.Tendsto nseq Filter.atTop Filter.atTop ∧
      ∀ J : ℕ, 0 < nseq J ∧ (J : ℝ) < G (nseq J) := by
  classical
  choose pick hpick_ge hpick_pos hpick_gap using fun (J N : ℕ) => h (J : ℝ) N
  let nseq : ℕ → ℕ := Nat.rec (pick 0 1) (fun J prev => pick (J + 1) (prev + 1))
  have hstep (J : ℕ) : nseq J < nseq (J + 1) := by
    change nseq J < pick (J + 1) (nseq J + 1)
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (hpick_ge (J + 1) (nseq J + 1))
  have hmono : StrictMono nseq := strictMono_nat_of_lt_succ hstep
  refine ⟨nseq, hmono, hmono.tendsto_atTop, ?_⟩
  intro J
  cases J with
  | zero => exact ⟨hpick_pos 0 1, hpick_gap 0 1⟩
  | succ J => exact ⟨hpick_pos (J + 1) (nseq J + 1), hpick_gap (J + 1) (nseq J + 1)⟩

theorem exists_source_fixed_law_counterexample :
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
      ∃ nseq : ℕ → ℕ, StrictMono nseq ∧
        Filter.Tendsto nseq Filter.atTop Filter.atTop ∧
        ∀ J : ℕ, 0 < nseq J ∧
          (J : ℝ) < Real.sqrt (nseq J : ℝ) *
            (normalizedTailCoefficient sourceEll q w (nseq J) -
              correctedInverseScale sourceEll q (atomicMeasure w)) := by
  obtain ⟨p, q, eps, hp, hq0, hq1, heps, hc, r, hr, hsr, hsmall,
      hw, hm, hprob, hcenter, hgap⟩ := exists_source_fixed_law_unbounded_scaled_remainder
  let w : AtomicIndex → ℝ := limitingMass sourceEll p r
  let P : Measure ℝ := originalMeasure sourceEll w
  letI : IsProbabilityMeasure P := hprob
  have hmass : HasSum w 1 := by
    simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one] using hm 0
  have hnonneg (i : AtomicIndex) : 0 ≤ w i := (hw i).le
  have hpos (i : AtomicIndex) : 0 < P.real {fixedAtom i} :=
    originalMeasure_atom_pos sourceEll w hnonneg hmass i (hw i)
  have hpositive : 0 < P.real (Set.Ioi 0) := by
    have hsingle : 0 < P.real {(1 : ℝ)} := by
      simpa [fixedAtom, baseAtom] using hpos (Sum.inl 1)
    have hsub : ({(1 : ℝ)} : Set ℝ) ⊆ Set.Ioi 0 := by
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      norm_num
    exact lt_of_lt_of_le hsingle (measureReal_mono hsub)
  have hqpos : 0 < q := lt_trans zero_lt_one hq0
  have hxpos : 0 < Real.sqrt q / 4 := div_pos (Real.sqrt_pos.mpr hqpos) (by norm_num)
  have hxupper : Real.sqrt q / 4 < 1 / 2 := by
    nlinarith [Real.sq_sqrt hqpos.le, Real.sqrt_nonneg q]
  have hrate : 0 < saddleRate sourceEll q w :=
    saddleRate_pos sourceEll q sourceEll_pos.ne' w hw hm
  have hrad := source_atomic_corrected_radicand_pos q hq0 hq1 w hnonneg
    (fun i => hw (Sum.inl i)) hm
  have hscale : 0 < correctedInverseScale sourceEll q (atomicMeasure w) := by
    unfold correctedInverseScale
    exact inv_pos.mpr (mul_pos sourceEll_pos (Real.sqrt_pos.mpr hrad))
  obtain ⟨nseq, hmono, htop, hn⟩ := increasing_remainder_witnesses
    (fun n => Real.sqrt (n : ℝ) *
      (normalizedTailCoefficient sourceEll q w n -
        correctedInverseScale sourceEll q (atomicMeasure w))) hgap
  refine ⟨q, w, hq0, hq1, hw, hm, ?_⟩
  exact ⟨hprob, hcenter, originalMeasure_ae_bounds sourceEll w, hpositive,
    (fun xi eta hne => jointCharacteristic_norm_lt_one_of_positive_atoms P hpos xi eta hne),
    resonance_frequency_escape,
    jointCharacteristic_resonance_norm_tendsto_one P (originalMeasure_ae_range sourceEll w),
    hxpos, hxupper, hrate, hscale, nseq, hmono, htop, hn⟩

end
end Shao.OQ3
