import Shao.OQ5.P52.FixedLayerConditionalMomentBounds
import Shao.OQ5.P52.FixedLayerPositiveStudentizer

/-!
# Conditional concentration for the actual original statistics

Honest centered-square and true-root-square L1 precede both Markov bounds.
Borel finite-sample algebra and the independently proved positive-root null
set license the final probability-real complement and union argument.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped BigOperators

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

private theorem sample_size_ge_three (j : ℕ) : 3 ≤ fixedLayerN j :=
  le_trans (by norm_num : 3 ≤ 8) (fixedLayerN_ge_eight j)

private theorem real_N_gt_one (j : ℕ) : (1 : ℝ) < fixedLayerN j := by
  have h : (8 : ℝ) ≤ fixedLayerN j := by exact_mod_cast fixedLayerN_ge_eight j
  linarith

private theorem rare_cond_probability (j : ℕ) :
    IsProbabilityMeasure (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) :=
  fixedLayerExactEvent_cond_isProbabilityMeasure j (fixedLayerN j) 2
    (le_trans (by norm_num : 2 ≤ 8) (fixedLayerN_ge_eight j))

attribute [local instance] rare_cond_probability

private theorem measurable_sample_U (n : ℕ) :
    Measurable (fun x : Fin n → LayerObs => fixedSampleU x) := by
  classical
  unfold fixedSampleU Shao.OQ6.FiniteRows.uStatistic Shao.OQ5.P35.unorderedPairSum
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro k _
  by_cases hik : i < k
  · simpa only [ite_eq_left hik, Function.comp_def] using
      measurable_fixedKernel.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply k))
  · simp only [ite_eq_right hik]
    exact measurable_const

private theorem measurable_sample_row (n : ℕ) (i : Fin n) :
    Measurable (fun x : Fin n → LayerObs =>
      Shao.OQ6.FiniteRows.rowMean (fun a b => fixedKernel (x a, x b)) i) := by
  classical
  unfold Shao.OQ6.FiniteRows.rowMean
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro k _
  exact measurable_fixedKernel.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply k))

private theorem measurable_sample_square (n : ℕ) :
    Measurable (fun x : Fin n → LayerObs => fixedSampleStudentizerSq x) := by
  unfold fixedSampleStudentizerSq Shao.OQ6.FiniteRows.jackknifeSq
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_sample_row n i).sub (measurable_sample_U n)).pow_const 2

private theorem measurable_prefix_U (n : ℕ) :
    Measurable (fun ω : ℕ → LayerObs =>
      fixedSampleU (fun i : Fin n => fixedSampleCoordinate i.val ω)) :=
  (measurable_sample_U n).comp
    (Measurable.of_eval (fun i => measurable_fixedSampleCoordinate i.val))

private theorem measurable_prefix_R (n : ℕ) :
    Measurable (fun ω : ℕ → LayerObs =>
      fixedSampleStudentizer (fun i : Fin n => fixedSampleCoordinate i.val ω)) :=
  (measurable_sample_square n).sqrt.comp
    (Measurable.of_eval (fun i => measurable_fixedSampleCoordinate i.val))

private theorem centered_square_integrable (j : ℕ) :
    Integrable (fun ω : ℕ → LayerObs =>
      (Real.sqrt (fixedLayerN j : ℝ) *
          fixedSampleU (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω) -
        (2 * fixedLayerT j * Real.sqrt (fixedLayerN j : ℝ)) /
          ((fixedLayerN j : ℝ) - 1)) ^ 2)
      (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) := by
  have hZ := (fixedSampleU_memLp_two_fixedLayerRareEvent_cond j).const_mul
    (Real.sqrt (fixedLayerN j : ℝ))
  exact (hZ.sub (memLp_const _)).integrable_sq

private theorem root_square_integrable (j : ℕ) :
    Integrable (fun ω : ℕ → LayerObs =>
      (fixedSampleStudentizer (fun i : Fin (fixedLayerN j) =>
        fixedSampleCoordinate i.val ω)) ^ 2)
      (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)) := by
  have hI := integrable_fixedSampleStudentizerSq_fixedLayerRareEvent_cond j
  exact hI.congr (Eventually.of_forall fun ω =>
    (fixedSampleStudentizer_sq (fixedLayerN j) (sample_size_ge_three j)
      (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω)).symm)

private theorem sixth_inv_square (j : ℕ) :
    (((fixedLayerN j : ℝ) ^ (1 / 6 : ℝ)) ^ 2)⁻¹ =
      (fixedLayerN j : ℝ) ^ (-1 / 3 : ℝ) := by
  have hN : (0 : ℝ) < fixedLayerN j := lt_trans zero_lt_one (real_N_gt_one j)
  have hp : ((fixedLayerN j : ℝ) ^ (1 / 6 : ℝ)) ^ 2 =
      (fixedLayerN j : ℝ) ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hN.le]
    congr 1
    norm_num
  rw [hp, ← Real.rpow_neg hN.le]
  congr 1
  norm_num

private theorem markov_event_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ)
    (hf : Integrable f μ) (hfn : ∀ x, 0 ≤ f x) (A : Set α)
    (t B : ℝ) (ht : 0 < t) (hA : ∀ x ∈ A, t ≤ f x)
    (hB : (∫ x, f x ∂μ) ≤ B) : μ.real A ≤ B / t := by
  have hmono : μ.real A ≤ μ.real {x | t ≤ f x} :=
    measureReal_mono (fun x hx => hA x hx)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hfn) hf t
  have hscaled : t * μ.real A ≤ B :=
    (mul_le_mul_of_nonneg_left hmono ht.le).trans (hmarkov.trans hB)
  apply (le_div_iff₀ ht).mpr
  simpa only [mul_comm] using hscaled

theorem fixedLayerRareEvent_cond_numerator_small_probability (j : ℕ) :
    (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)).real
      {ω : ℕ → LayerObs |
        Real.sqrt (fixedLayerN j : ℝ) *
            fixedSampleU (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω) <
          (fixedLayerN j : ℝ) ^ (1 / 6 : ℝ)} ≤
      ((4 / 3 : ℝ) + 4 *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂fixedObservationLaw.prod fixedObservationLaw)) *
        (fixedLayerN j : ℝ) ^ (-1 / 3 : ℝ) := by
  let Q := ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)
  let Z : (ℕ → LayerObs) → ℝ := fun ω => Real.sqrt (fixedLayerN j : ℝ) *
    fixedSampleU (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω)
  let M : ℝ := (2 * fixedLayerT j * Real.sqrt (fixedLayerN j : ℝ)) /
    ((fixedLayerN j : ℝ) - 1)
  let a : ℝ := (fixedLayerN j : ℝ) ^ (1 / 6 : ℝ)
  let B : ℝ := (4 / 3 : ℝ) + 4 *
    (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
      ∂fixedObservationLaw.prod fixedObservationLaw)
  have ha : 0 < a := Real.rpow_pos_of_pos (lt_trans zero_lt_one (real_N_gt_one j)) _
  have hM : 2 * a ≤ M := fixedLayerRareNumeratorMean_ge j
  have hf : Integrable (fun ω => (Z ω - M) ^ 2) Q := centered_square_integrable j
  have hbound : Q.real {ω | Z ω < a} ≤ B / a ^ 2 := by
    apply markov_event_bound Q (fun ω => (Z ω - M) ^ 2) hf (fun _ => sq_nonneg _)
      {ω | Z ω < a} (a ^ 2) B (sq_pos_of_pos ha)
    · intro ω hω
      change Z ω < a at hω
      have hh : 0 ≤ (M - Z ω - a) * (M - Z ω + a) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    · exact integral_fixedSampleNumerator_centered_sq_fixedLayerRareEvent_cond_le j
  calc
    _ ≤ B / a ^ 2 := hbound
    _ = _ := by
      dsimp only [a, B]
      rw [div_eq_mul_inv, sixth_inv_square j]

theorem fixedLayerRareEvent_cond_studentizer_large_probability (j : ℕ) :
    (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)).real
      {ω : ℕ → LayerObs |
        Real.log (fixedLayerN j : ℝ) <
          fixedSampleStudentizer
            (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω)} ≤
      ((4 / 3 : ℝ) + 4 *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂fixedObservationLaw.prod fixedObservationLaw)) /
        (Real.log (fixedLayerN j : ℝ)) ^ 2 := by
  let Q := ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)
  let R : (ℕ → LayerObs) → ℝ := fun ω =>
    fixedSampleStudentizer (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω)
  let L : ℝ := Real.log (fixedLayerN j : ℝ)
  let B : ℝ := (4 / 3 : ℝ) + 4 *
    (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
      ∂fixedObservationLaw.prod fixedObservationLaw)
  have hL : 0 < L := Real.log_pos (real_N_gt_one j)
  have hf : Integrable (fun ω => (R ω) ^ 2) Q := root_square_integrable j
  have hB : (∫ ω, (R ω) ^ 2 ∂Q) ≤ B := by
    calc
      _ = ∫ ω : ℕ → LayerObs,
          fixedSampleStudentizerSq (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω)
          ∂Q := integral_congr_ae (Eventually.of_forall fun ω =>
            fixedSampleStudentizer_sq (fixedLayerN j) (sample_size_ge_three j)
              (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω))
      _ ≤ _ := integral_fixedSampleStudentizerSq_fixedLayerRareEvent_cond_le j
  apply markov_event_bound Q (fun ω => (R ω) ^ 2) hf (fun _ => sq_nonneg _)
    {ω | L < R ω} (L ^ 2) B (sq_pos_of_pos hL) _ hB
  intro ω hω
  change L < R ω at hω
  have hR : 0 ≤ R ω := fixedSampleStudentizer_nonneg _
  have hh : 0 ≤ (R ω - L) * (R ω + L) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem fixedLayerRareEvent_cond_good_probability_lower (j : ℕ) :
    1 - ((4 / 3 : ℝ) + 4 *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂fixedObservationLaw.prod fixedObservationLaw)) *
        ((fixedLayerN j : ℝ) ^ (-1 / 3 : ℝ) +
          1 / (Real.log (fixedLayerN j : ℝ)) ^ 2) ≤
      (ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)).real
        {ω : ℕ → LayerObs |
          (fixedLayerN j : ℝ) ^ (1 / 6 : ℝ) ≤
              Real.sqrt (fixedLayerN j : ℝ) *
                fixedSampleU
                  (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω) ∧
          0 < fixedSampleStudentizer
              (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω) ∧
          fixedSampleStudentizer
              (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω) ≤
            Real.log (fixedLayerN j : ℝ)} := by
  let Q := ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j)
  let Z : (ℕ → LayerObs) → ℝ := fun ω => Real.sqrt (fixedLayerN j : ℝ) *
    fixedSampleU (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω)
  let R : (ℕ → LayerObs) → ℝ := fun ω =>
    fixedSampleStudentizer (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω)
  let a : ℝ := (fixedLayerN j : ℝ) ^ (1 / 6 : ℝ)
  let L : ℝ := Real.log (fixedLayerN j : ℝ)
  let B : ℝ := (4 / 3 : ℝ) + 4 *
    (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
      ∂fixedObservationLaw.prod fixedObservationLaw)
  let A : Set (ℕ → LayerObs) := {ω | Z ω < a}
  let D : Set (ℕ → LayerObs) := {ω | R ω ≤ 0}
  let C : Set (ℕ → LayerObs) := {ω | L < R ω}
  let G : Set (ℕ → LayerObs) := {ω | a ≤ Z ω ∧ 0 < R ω ∧ R ω ≤ L}
  have hZ : Measurable Z := (measurable_prefix_U (fixedLayerN j)).const_mul _
  have hR : Measurable R := measurable_prefix_R (fixedLayerN j)
  have _hA : MeasurableSet A := measurableSet_lt hZ measurable_const
  have _hD : MeasurableSet D := measurableSet_le hR measurable_const
  have _hC : MeasurableSet C := measurableSet_lt measurable_const hR
  have hG : MeasurableSet G :=
    (measurableSet_le measurable_const hZ).inter
      ((measurableSet_lt measurable_const hR).inter (measurableSet_le hR measurable_const))
  have hz : Q.real D = 0 := by
    have hz' : Q {ω | ¬0 < R ω} = 0 :=
      ae_iff.mp (fixedSampleStudentizer_fixedLayerRareEvent_cond_pos_ae j)
    have he : D = {ω | ¬0 < R ω} := by
      ext ω
      simp only [D, Set.mem_ofPred_eq, not_lt]
    change (Q D).toReal = 0
    rw [he, hz', ENNReal.toReal_zero]
  have hsub : Gᶜ ⊆ (A ∪ D) ∪ C := by
    intro ω hω
    change ¬(a ≤ Z ω ∧ 0 < R ω ∧ R ω ≤ L) at hω
    change (Z ω < a ∨ R ω ≤ 0) ∨ L < R ω
    by_cases hZa : a ≤ Z ω
    · by_cases hRp : 0 < R ω
      · exact Or.inr (lt_of_not_ge (fun hL => hω ⟨hZa, hRp, hL⟩))
      · exact Or.inl (Or.inr (le_of_not_gt hRp))
    · exact Or.inl (Or.inl (lt_of_not_ge hZa))
  have hle : Q.real Gᶜ ≤ Q.real A + Q.real D + Q.real C :=
    (measureReal_mono hsub).trans
      ((measureReal_union_le (μ := Q) (A ∪ D) C).trans
        (add_le_add (measureReal_union_le (μ := Q) A D) le_rfl))
  have hcomp : Q.real G + Q.real Gᶜ = 1 := probReal_add_probReal_compl hG
  have hA : Q.real A ≤ B * (fixedLayerN j : ℝ) ^ (-1 / 3 : ℝ) :=
    fixedLayerRareEvent_cond_numerator_small_probability j
  have hC : Q.real C ≤ B / L ^ 2 :=
    fixedLayerRareEvent_cond_studentizer_large_probability j
  change 1 - B * ((fixedLayerN j : ℝ) ^ (-1 / 3 : ℝ) + 1 / L ^ 2) ≤ Q.real G
  have hcost : B * ((fixedLayerN j : ℝ) ^ (-1 / 3 : ℝ) + 1 / L ^ 2) =
      B * (fixedLayerN j : ℝ) ^ (-1 / 3 : ℝ) + B / L ^ 2 := by ring
  rw [hcost]
  linarith

end
end Shao.OQ5.P52
