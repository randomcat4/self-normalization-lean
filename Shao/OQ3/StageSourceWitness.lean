import Shao.OQ3.StagePhaseReturns
import Shao.OQ3.StageLayerSeriesLimit

/-!
# Arbitrarily large witnesses for the actual finite source stage

Source: current/oq3/proofs/r1/report.md, lines 486–497, equation (26).
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U17o scope62. The actual conditional-law continuity premise remains explicit.
-/

namespace Shao.OQ3
open MeasureTheory Filter
open scoped Topology BigOperators
noncomputable section

theorem exists_stage_source_witness
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1)
    (J : ℕ) (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (hmeanY : (∫ x : ℝ, normalValue x ∂atomicMeasure w) = q)
    (hmeanX : (∫ x : ℝ, x ∂atomicMeasure w) = q / 4)
    (hrange : ∀ᵐ x ∂atomicMeasure w, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < (atomicMeasure w).real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (hcont : ∀ d : ℕ → ℝ,
      (∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M) →
      (∀ᶠ n : ℕ in atTop, ∃ k : ℤ,
        d n + (n : ℝ) * q = dyadicMesh J * (k : ℝ)) →
      ∀ A : Set ℝ,
        (ProbabilityTheory.gaussianReal 0
          (Real.toNNReal (transverseVariance (atomicMeasure w)))) (frontier A) = 0 →
        Tendsto (fun n : ℕ =>
          (normalLayerConditionalLaw (atomicMeasure w) q (q / 4) (d n) n).real A)
          atTop (nhds ((ProbabilityTheory.gaussianReal 0
            (Real.toNNReal (transverseVariance (atomicMeasure w)))).real A)))
    (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 0 < n ∧
      correctedInverseScale sourceEll q (atomicMeasure w) +
        (3 * dyadicMesh J * Real.sqrt (dyadicMesh J)) / (16384 * Real.pi) ≤
          normalizedTailCoefficient sourceEll q w n ∧
      (J : ℝ) ≤ Real.sqrt (n : ℝ) * dyadicMesh J * Real.sqrt (dyadicMesh J) := by
  letI : IsProbabilityMeasure (atomicMeasure w) := atomicMeasure_isProbabilityMeasure w hw hs
  let h : ℝ := dyadicMesh J
  let C : ℝ := correctedInverseScale sourceEll q (atomicMeasure w)
  let L : ℝ := (h / Real.sqrt (normalVariance (atomicMeasure w))) *
    ∑' k : ℤ, sourceGaussianLayerWeight (atomicMeasure w) q sourceEll (h * (k : ℝ))
  have hh : 0 < h := by dsimp [h, dyadicMesh]; positivity
  have ha : 0 < h * Real.sqrt h := mul_pos hh (Real.sqrt_pos.mpr hh)
  obtain ⟨m, hm, hphase⟩ := exists_stage_phase_return_subsequence J q
  have hmTop : Tendsto m atTop atTop := hm.tendsto_atTop
  obtain ⟨_, hlim⟩ := normalizedTailCoefficient_stage_subsequence_tendsto
    w hw hs J q hq0 hq1 hmeanY hmeanX hrange hpos m hmTop hphase hcont
  have hlimL : Tendsto (fun j : ℕ => normalizedTailCoefficient sourceEll q w (m j))
      atTop (nhds L) := by simpa only [L, h] using hlim
  obtain ⟨_, hgap⟩ := stage_sourceGaussianLayerWeight_lattice_gap
    (atomicMeasure w) J q hq0 hq1 hmeanY hmeanX hrange hpos
  have hgapL : C + (h * Real.sqrt h) / (4096 * Real.pi) ≤ L := by
    simpa only [C, L, h, mul_comm] using hgap
  let delta : ℝ := h * Real.sqrt h / (16384 * Real.pi)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hsplit : h * Real.sqrt h / (4096 * Real.pi) =
      (3 * h * Real.sqrt h) / (16384 * Real.pi) + delta := by
    dsimp only [delta]
    field_simp
    <;> ring
  have hmargin : C + (3 * h * Real.sqrt h) / (16384 * Real.pi) < L := by
    rw [hsplit] at hgapL
    linarith only [hgapL, hdelta]
  have hcoef : ∀ᶠ j : ℕ in atTop,
      C + (3 * h * Real.sqrt h) / (16384 * Real.pi) <
        normalizedTailCoefficient sourceEll q w (m j) :=
    (tendsto_order.mp hlimL).1 _ hmargin
  obtain ⟨B, hB⟩ := exists_nat_gt (((J : ℝ) / (h * Real.sqrt h)) ^ 2)
  have hNtime : ∀ᶠ j : ℕ in atTop, N ≤ m j := hmTop.eventually (eventually_ge_atTop N)
  have hBtime : ∀ᶠ j : ℕ in atTop, B ≤ m j := hmTop.eventually (eventually_ge_atTop B)
  have hptime : ∀ᶠ j : ℕ in atTop, 1 ≤ m j := hmTop.eventually (eventually_ge_atTop 1)
  obtain ⟨j, hNj, hBj, hpj, hcj⟩ := (hNtime.and (hBtime.and (hptime.and hcoef))).exists
  refine ⟨m j, hNj, by omega, ?_, ?_⟩
  · simpa only [C, h] using hcj.le
  · have hBcast : (B : ℝ) ≤ (m j : ℝ) := by exact_mod_cast hBj
    have hsqrt : (J : ℝ) / (h * Real.sqrt h) ≤ Real.sqrt (m j : ℝ) :=
      Real.le_sqrt_of_sq_le (hB.le.trans hBcast)
    have H := (div_le_iff₀ ha).mp hsqrt
    simpa only [h, mul_assoc] using H

end
end Shao.OQ3
