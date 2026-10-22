import Shao.OQ5.P52.FixedLayerErasedStatisticsMoments
import Shao.OQ5.P52.FixedLayerRareStatistics

/-!
# Conditional moments of the original statistics

The full erased-prefix pushforward transports honest L2/L1 first. The
conditional AE comparison retains the numerator shift and preserves the
original randomly centered Studentizer square.
-/

set_option autoImplicit false

open MeasureTheory Filter

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

attribute [local instance] fixedErasedLaw_isProbabilityMeasure

private theorem sample_size_ge_three (j : ℕ) : 3 ≤ fixedLayerN j :=
  le_trans (by norm_num : 3 ≤ 8) (fixedLayerN_ge_eight j)

private theorem rare_cond_probability (j : ℕ) :
    IsProbabilityMeasure (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) :=
  fixedLayerExactEvent_cond_isProbabilityMeasure j (fixedLayerN j) 2
    (le_trans (by norm_num : 2 ≤ 8) (fixedLayerN_ge_eight j))

attribute [local instance] rare_cond_probability

private theorem erased_prefix_mp (j : ℕ) :
    MeasurePreserving
      (fun ω (i : Fin (fixedLayerN j)) =>
        fixedEraseLayer j (fixedSampleCoordinate i.val ω))
      (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j))
      (Measure.pi (fun _ : Fin (fixedLayerN j) => fixedErasedLaw j)) :=
  ⟨measurable_pi_iff.mpr (fun i =>
      (measurable_fixedEraseLayer j).comp (measurable_fixedSampleCoordinate i.val)),
    map_fixedLayerRareEvent_cond_erasedPrefix j⟩

private theorem erased_prefix_integral (j : ℕ)
    (f : (Fin (fixedLayerN j) → LayerObs) → ℝ)
    (hf : Integrable f (Measure.pi (fun _ : Fin (fixedLayerN j) => fixedErasedLaw j))) :
    (∫ ω : ℕ → LayerObs,
      f (fun i : Fin (fixedLayerN j) =>
        fixedEraseLayer j (fixedSampleCoordinate i.val ω))
      ∂ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) =
      ∫ x : Fin (fixedLayerN j) → LayerObs, f x
        ∂Measure.pi (fun _ : Fin (fixedLayerN j) => fixedErasedLaw j) := by
  have hmap : Integrable f
      ((ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)).map
        (fun ω (i : Fin (fixedLayerN j)) =>
          fixedEraseLayer j (fixedSampleCoordinate i.val ω))) := by
    rw [map_fixedLayerRareEvent_cond_erasedPrefix j]
    exact hf
  calc
    _ = ∫ x, f x
        ∂(ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)).map
          (fun ω (i : Fin (fixedLayerN j)) =>
            fixedEraseLayer j (fixedSampleCoordinate i.val ω)) :=
      (integral_map (erased_prefix_mp j).aemeasurable hmap.aestronglyMeasurable).symm
    _ = _ := by rw [map_fixedLayerRareEvent_cond_erasedPrefix j]

private theorem erased_U_memLp_two (j : ℕ) :
    MemLp (fun ω : ℕ → LayerObs =>
      fixedSampleU (fun i : Fin (fixedLayerN j) =>
        fixedEraseLayer j (fixedSampleCoordinate i.val ω))) 2
      (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) :=
  (fixedSampleU_memLp_two_fixedErasedLaw j (fixedLayerN j) (sample_size_ge_three j)).comp_measurePreserving
    (erased_prefix_mp j)

private theorem erased_U_integral_zero (j : ℕ) :
    (∫ ω : ℕ → LayerObs,
      fixedSampleU (fun i : Fin (fixedLayerN j) =>
        fixedEraseLayer j (fixedSampleCoordinate i.val ω))
      ∂ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) = 0 := by
  have hI := (fixedSampleU_memLp_two_fixedErasedLaw j (fixedLayerN j)
    (sample_size_ge_three j)).integrable (by norm_num)
  exact (erased_prefix_integral j _ hI).trans
    (integral_fixedSampleU_fixedErasedLaw_eq_zero j (fixedLayerN j) (sample_size_ge_three j))

theorem fixedSampleU_memLp_two_fixedLayerRareEvent_cond (j : ℕ) :
    MemLp (fun ω : ℕ → LayerObs =>
      fixedSampleU (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω)) 2
      (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) := by
  apply (memLp_congr_ae (fixedSampleU_fixedLayerRareEvent_cond_ae_eq j)).mpr
  exact (erased_U_memLp_two j).add
    (memLp_const ((2 * fixedLayerT j) / ((fixedLayerN j : ℝ) - 1)))

theorem integrable_fixedSampleStudentizerSq_fixedLayerRareEvent_cond (j : ℕ) :
    Integrable (fun ω : ℕ → LayerObs =>
      fixedSampleStudentizerSq
        (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω))
      (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) := by
  have hI := (erased_prefix_mp j).integrable_comp_of_integrable
    (integrable_fixedSampleStudentizerSq_fixedErasedLaw j (fixedLayerN j) (sample_size_ge_three j))
  change Integrable (fun ω : ℕ → LayerObs =>
    fixedSampleStudentizerSq (fun i : Fin (fixedLayerN j) =>
      fixedEraseLayer j (fixedSampleCoordinate i.val ω)))
    (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) at hI
  exact hI.congr (fixedSampleStudentizerSq_fixedLayerRareEvent_cond_ae_eq j).symm

theorem integral_fixedSampleNumerator_fixedLayerRareEvent_cond (j : ℕ) :
    (∫ ω : ℕ → LayerObs,
      Real.sqrt (fixedLayerN j : ℝ) *
        fixedSampleU (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω)
      ∂ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) =
      (2 * fixedLayerT j * Real.sqrt (fixedLayerN j : ℝ)) /
        ((fixedLayerN j : ℝ) - 1) := by
  have _hZ := ((fixedSampleU_memLp_two_fixedLayerRareEvent_cond j).integrable
    (by norm_num)).const_mul (Real.sqrt (fixedLayerN j : ℝ))
  have hE : Integrable (fun ω : ℕ → LayerObs =>
      fixedSampleU (fun i : Fin (fixedLayerN j) =>
        fixedEraseLayer j (fixedSampleCoordinate i.val ω)))
      (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) :=
    (erased_U_memLp_two j).integrable (by norm_num)
  have hc : Integrable (fun _ω : ℕ → LayerObs =>
      (2 * fixedLayerT j) / ((fixedLayerN j : ℝ) - 1))
      (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) := integrable_const _
  have hmean : (∫ ω : ℕ → LayerObs,
      fixedSampleU (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω)
      ∂ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) =
      (2 * fixedLayerT j) / ((fixedLayerN j : ℝ) - 1) := by
    calc
      _ = ∫ ω : ℕ → LayerObs,
          fixedSampleU (fun i : Fin (fixedLayerN j) =>
            fixedEraseLayer j (fixedSampleCoordinate i.val ω)) +
              (2 * fixedLayerT j) / ((fixedLayerN j : ℝ) - 1)
          ∂ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j) :=
        integral_congr_ae (fixedSampleU_fixedLayerRareEvent_cond_ae_eq j)
      _ = _ := by
        rw [integral_add hE hc, erased_U_integral_zero]
        simp only [integral_const, probReal_univ, one_smul, zero_add]
  rw [integral_const_mul, hmean]
  ring

theorem integral_fixedSampleNumerator_centered_sq_fixedLayerRareEvent_cond (j : ℕ) :
    (∫ ω : ℕ → LayerObs,
      (Real.sqrt (fixedLayerN j : ℝ) *
          fixedSampleU (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω) -
        (2 * fixedLayerT j * Real.sqrt (fixedLayerN j : ℝ)) /
          ((fixedLayerN j : ℝ) - 1)) ^ 2
      ∂ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) =
      (4 / 3 : ℝ) + (2 / ((fixedLayerN j : ℝ) - 1)) *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) := by
  have hZ : MemLp (fun ω : ℕ → LayerObs =>
      Real.sqrt (fixedLayerN j : ℝ) *
        fixedSampleU (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω)) 2
      (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) :=
    (fixedSampleU_memLp_two_fixedLayerRareEvent_cond j).const_mul _
  have _hcenteredSq : Integrable (fun ω : ℕ → LayerObs =>
      (Real.sqrt (fixedLayerN j : ℝ) *
          fixedSampleU (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω) -
        (2 * fixedLayerT j * Real.sqrt (fixedLayerN j : ℝ)) /
          ((fixedLayerN j : ℝ) - 1)) ^ 2)
      (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) :=
    (hZ.sub (memLp_const _)).integrable_sq
  have hscaledSq : Integrable (fun x : Fin (fixedLayerN j) → LayerObs =>
      (fixedLayerN j : ℝ) * (fixedSampleU x) ^ 2)
      (Measure.pi (fun _ : Fin (fixedLayerN j) => fixedErasedLaw j)) :=
    (fixedSampleU_memLp_two_fixedErasedLaw j (fixedLayerN j)
      (sample_size_ge_three j)).integrable_sq.const_mul _
  have _hscaledPullback := (erased_prefix_mp j).integrable_comp_of_integrable hscaledSq
  calc
    _ = ∫ ω : ℕ → LayerObs,
        (fixedLayerN j : ℝ) *
          (fixedSampleU (fun i : Fin (fixedLayerN j) =>
            fixedEraseLayer j (fixedSampleCoordinate i.val ω))) ^ 2
        ∂ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j) := by
      apply integral_congr_ae
      filter_upwards [fixedSampleU_fixedLayerRareEvent_cond_ae_eq j] with ω hU
      rw [hU]
      have hshift :
          (2 * fixedLayerT j * Real.sqrt (fixedLayerN j : ℝ)) /
              ((fixedLayerN j : ℝ) - 1) =
            Real.sqrt (fixedLayerN j : ℝ) *
              ((2 * fixedLayerT j) / ((fixedLayerN j : ℝ) - 1)) := by ring
      rw [hshift]
      have hcancel : ∀ a b c : ℝ, a * (b + c) - a * c = a * b := by
        intros; ring
      rw [hcancel, mul_pow, Real.sq_sqrt (Nat.cast_nonneg (fixedLayerN j))]
    _ = ∫ x : Fin (fixedLayerN j) → LayerObs,
        (fixedLayerN j : ℝ) * (fixedSampleU x) ^ 2
        ∂Measure.pi (fun _ : Fin (fixedLayerN j) => fixedErasedLaw j) :=
      erased_prefix_integral j _ hscaledSq
    _ = _ := integral_fixedSampleU_scaled_sq_fixedErasedLaw j (fixedLayerN j) (sample_size_ge_three j)

theorem integral_fixedSampleStudentizerSq_fixedLayerRareEvent_cond (j : ℕ) :
    (∫ ω : ℕ → LayerObs,
      fixedSampleStudentizerSq
        (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω)
      ∂ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) =
      (4 / 3 : ℝ) + (4 / ((fixedLayerN j : ℝ) - 2)) *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) := by
  have _hOriginal := integrable_fixedSampleStudentizerSq_fixedLayerRareEvent_cond j
  have hI := integrable_fixedSampleStudentizerSq_fixedErasedLaw j (fixedLayerN j)
    (sample_size_ge_three j)
  calc
    _ = ∫ ω : ℕ → LayerObs,
        fixedSampleStudentizerSq (fun i : Fin (fixedLayerN j) =>
          fixedEraseLayer j (fixedSampleCoordinate i.val ω))
        ∂ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j) :=
      integral_congr_ae (fixedSampleStudentizerSq_fixedLayerRareEvent_cond_ae_eq j)
    _ = ∫ x : Fin (fixedLayerN j) → LayerObs, fixedSampleStudentizerSq x
        ∂Measure.pi (fun _ : Fin (fixedLayerN j) => fixedErasedLaw j) :=
      erased_prefix_integral j _ hI
    _ = _ := integral_fixedSampleStudentizerSq_fixedErasedLaw j (fixedLayerN j) (sample_size_ge_three j)

end
end Shao.OQ5.P52
