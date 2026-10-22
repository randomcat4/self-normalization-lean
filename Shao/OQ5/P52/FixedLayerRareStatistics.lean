import Shao.OQ5.P52.FixedLayerErasedMixture
import Shao.OQ5.P52.FixedLayerSampleStatistics

/-!
# Original statistics under the actual two-target event

Original pair-law absolute convergence is pulled back only at distinct sample
indices, then transferred to conditioning. Constant selected-layer rows shift
both original row means and U equally, preserving the centered jackknife.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped BigOperators

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

private theorem sample_pair_mask (n : ℕ) :
    ∀ᵐ ω : ℕ → LayerObs ∂fixedSampleLaw,
      ∀ i k : Fin n, i ≠ k →
        (fixedSampleCoordinate i.val ω, fixedSampleCoordinate k.val ω) ∈
          fixedAbsoluteConvergenceSet := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro k
  by_cases hik : i = k
  · exact Eventually.of_forall fun _ h => False.elim (h hik)
  · have hp : MeasurePreserving
        (fun ω : ℕ → LayerObs =>
          (fixedSampleCoordinate i.val ω, fixedSampleCoordinate k.val ω))
        fixedSampleLaw (fixedObservationLaw.prod fixedObservationLaw) :=
      ⟨(measurable_fixedSampleCoordinate i.val).prodMk
        (measurable_fixedSampleCoordinate k.val),
        map_fixedSampleCoordinate_pair i.val k.val
          (fun he => hik (Fin.ext he))⟩
    exact (hp.quasiMeasurePreserving.ae ae_mem_fixedAbsoluteConvergenceSet).mono
      (fun _ hz _ => hz)

private theorem twoTarget_row_shift (j : ℕ)
    (x : Fin (fixedLayerN j) → LayerObs)
    (J : Finset (Fin (fixedLayerN j))) (hJ : J.card = 2)
    (hstate : ∀ i, (x i).2 j = Shao.OQ5.P50.twoTargetState J i)
    (hmask : ∀ i k, i ≠ k → (x i, x k) ∈ fixedAbsoluteConvergenceSet)
    (i : Fin (fixedLayerN j)) :
    Shao.OQ6.FiniteRows.rowMean (fun a b => fixedKernel (x a, x b)) i =
      Shao.OQ6.FiniteRows.rowMean
        (fun a b => fixedKernel (fixedEraseLayer j (x a), fixedEraseLayer j (x b))) i +
      (2 * fixedLayerT j) / ((fixedLayerN j : ℝ) - 1) := by
  classical
  have hn : 3 ≤ fixedLayerN j := le_trans (by decide : 3 ≤ 8) (fixedLayerN_ge_eight j)
  have hrow : (∑ k ∈ Finset.univ.erase i, fixedLayerTerm j (x i, x k)) =
      2 * fixedLayerT j := by
    change (∑ k ∈ Finset.univ.erase i,
      Shao.OQ5.P50.layerKernel (fixedLayerN j) (fixedLayerT j)
        (fixedLayerP j) (fixedLayerQ j) ((x i).2 j) ((x k).2 j)) = _
    simp_rw [hstate]
    exact Shao.OQ5.P50.twoTarget_row_sum (fixedLayerN j) hn
      (fixedLayerT j) (fixedLayerP j) (fixedLayerQ j) J hJ i
  have hsum : (∑ k ∈ Finset.univ.erase i, fixedKernel (x i, x k)) =
      (∑ k ∈ Finset.univ.erase i,
        fixedKernel (fixedEraseLayer j (x i), fixedEraseLayer j (x k))) +
        2 * fixedLayerT j := by
    calc
      _ = ∑ k ∈ Finset.univ.erase i,
          (fixedKernel (fixedEraseLayer j (x i), fixedEraseLayer j (x k)) +
            fixedLayerTerm j (x i, x k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (eq_sub_iff_add_eq.mp
          (fixedKernel_erase_pair_eq_sub j (x i, x k)
            (hmask i k (Finset.mem_erase.mp hk).1.symm))).symm
      _ = _ := by rw [Finset.sum_add_distrib, hrow]
  simp only [Shao.OQ6.FiniteRows.rowMean]
  rw [hsum, mul_add, div_eq_mul_inv]
  ring

private theorem row_shift_statistics {n : ℕ}
    (H K : Fin n → Fin n → ℝ)
    (hH : ∀ i k, H i k = H k i) (hK : ∀ i k, K i k = K k i)
    (hn : 3 ≤ n) (c : ℝ)
    (hq : ∀ i, Shao.OQ6.FiniteRows.rowMean H i =
      Shao.OQ6.FiniteRows.rowMean K i + c) :
    Shao.OQ6.FiniteRows.uStatistic H = Shao.OQ6.FiniteRows.uStatistic K + c ∧
      Shao.OQ6.FiniteRows.jackknifeSq H = Shao.OQ6.FiniteRows.jackknifeSq K := by
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le (by decide : 0 < 3) hn))
  have hsumH := Shao.OQ6.FiniteRows.sum_rowMean H hH hn
  have hsumK := Shao.OQ6.FiniteRows.sum_rowMean K hK hn
  have hu : Shao.OQ6.FiniteRows.uStatistic H =
      Shao.OQ6.FiniteRows.uStatistic K + c := by
    apply mul_left_cancel₀ hn0
    rw [mul_add, ← hsumH, ← hsumK]
    simp_rw [hq]
    simp only [Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine ⟨hu, ?_⟩
  unfold Shao.OQ6.FiniteRows.jackknifeSq
  rw [hu]
  simp_rw [hq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem twoTarget_statistics (j : ℕ)
    (x : Fin (fixedLayerN j) → LayerObs)
    (J : Finset (Fin (fixedLayerN j))) (hJ : J.card = 2)
    (hstate : ∀ i, (x i).2 j = Shao.OQ5.P50.twoTargetState J i)
    (hmask : ∀ i k, i ≠ k → (x i, x k) ∈ fixedAbsoluteConvergenceSet) :
    fixedSampleU x =
        fixedSampleU (fun i => fixedEraseLayer j (x i)) +
          (2 * fixedLayerT j) / ((fixedLayerN j : ℝ) - 1) ∧
      fixedSampleStudentizerSq x =
        fixedSampleStudentizerSq (fun i => fixedEraseLayer j (x i)) := by
  have hn : 3 ≤ fixedLayerN j := le_trans (by decide : 3 ≤ 8) (fixedLayerN_ge_eight j)
  exact row_shift_statistics
    (fun a b => fixedKernel (x a, x b))
    (fun a b => fixedKernel (fixedEraseLayer j (x a), fixedEraseLayer j (x b)))
    (fun a b => fixedKernel_symmetric (x a) (x b))
    (fun a b => fixedKernel_symmetric (fixedEraseLayer j (x a)) (fixedEraseLayer j (x b)))
    hn ((2 * fixedLayerT j) / ((fixedLayerN j : ℝ) - 1))
    (twoTarget_row_shift j x J hJ hstate hmask)

private theorem conditional_statistics (j : ℕ) :
    ∀ᵐ ω : ℕ → LayerObs
      ∂ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j),
      fixedSampleU (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω) =
          fixedSampleU (fun i : Fin (fixedLayerN j) =>
            fixedEraseLayer j (fixedSampleCoordinate i.val ω)) +
            (2 * fixedLayerT j) / ((fixedLayerN j : ℝ) - 1) ∧
        fixedSampleStudentizerSq
            (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω) =
          fixedSampleStudentizerSq (fun i : Fin (fixedLayerN j) =>
            fixedEraseLayer j (fixedSampleCoordinate i.val ω)) := by
  classical
  have hA : MeasurableSet (fixedLayerRareEvent j) :=
    measurableSet_fixedLayerExactEvent j (fixedLayerN j) 2
  have hmask :=
    (ProbabilityTheory.cond_absolutelyContinuous
      (μ := fixedSampleLaw) (s := fixedLayerRareEvent j)).ae_le
        (sample_pair_mask (fixedLayerN j))
  filter_upwards [hmask, ProbabilityTheory.ae_cond_mem (μ := fixedSampleLaw) hA]
    with ω hm hω
  have hEvent : ω ∈ fixedLayerExactEvent j (fixedLayerN j) 2 := hω
  rw [fixedLayerExactEvent_eq_biUnion] at hEvent
  rcases Set.mem_iUnion.mp hEvent with ⟨J, hEvent⟩
  rcases Set.mem_iUnion.mp hEvent with ⟨hJ, hpos⟩
  have hcard : J.card = 2 := (Finset.mem_powersetCard.mp hJ).2
  have hstate : ∀ i : Fin (fixedLayerN j),
      (fixedSampleCoordinate i.val ω).2 j = Shao.OQ5.P50.twoTargetState J i := by
    intro i
    by_cases hi : i ∈ J
    · have hx : fixedSampleCategory j i.val ω = 1 := by
        simpa only [hi, ite_true] using hpos i
      simpa only [Shao.OQ5.P50.twoTargetState, hi, ite_true,
        fixedSampleCategory] using hx
    · have hx : fixedSampleCategory j i.val ω = 0 := by
        simpa only [hi, ite_false] using hpos i
      simpa only [Shao.OQ5.P50.twoTargetState, hi, ite_false,
        fixedSampleCategory] using hx
  exact twoTarget_statistics j (fun i => fixedSampleCoordinate i.val ω) J hcard hstate hm

theorem fixedSampleU_fixedLayerRareEvent_cond_ae_eq (j : ℕ) :
    (fun ω : ℕ → LayerObs =>
      fixedSampleU (fun i : Fin (fixedLayerN j) =>
        fixedSampleCoordinate i.val ω))
      =ᵐ[ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)]
        (fun ω : ℕ → LayerObs =>
          fixedSampleU (fun i : Fin (fixedLayerN j) =>
            fixedEraseLayer j (fixedSampleCoordinate i.val ω)) +
          (2 * fixedLayerT j) / ((fixedLayerN j : ℝ) - 1)) :=
  (conditional_statistics j).mono (fun _ h => h.1)

theorem fixedSampleStudentizerSq_fixedLayerRareEvent_cond_ae_eq (j : ℕ) :
    (fun ω : ℕ → LayerObs =>
      fixedSampleStudentizerSq (fun i : Fin (fixedLayerN j) =>
        fixedSampleCoordinate i.val ω))
      =ᵐ[ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)]
        (fun ω : ℕ → LayerObs =>
          fixedSampleStudentizerSq (fun i : Fin (fixedLayerN j) =>
            fixedEraseLayer j (fixedSampleCoordinate i.val ω))) :=
  (conditional_statistics j).mono (fun _ h => h.2)

end
end Shao.OQ5.P52
