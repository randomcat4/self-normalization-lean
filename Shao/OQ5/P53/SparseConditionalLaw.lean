import Shao.OQ5.P53.SparseBalancedMass
import Shao.Probability.ConditionalIID

/-!
# Genuine conditional laws for the sparse balanced event

The whole observation law is conditioned on its actual two label events.
The finite conditional sample is their full product, with the prescribed
target orientations.  Low observations retain independent signs and noise;
only the original second moments are used below.
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace Shao.OQ5.P53

local notation "SparseObs" => ((ℝ × (ℕ × Bool)) × (ℕ × Bool))

def sparseLowObservationMeasure (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) : Measure SparseObs :=
  ProbabilityTheory.cond (sparsePopulationMeasure α x N) (sparseLowObservation j)

def sparseTargetObservationMeasure (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) (b : Bool) : Measure SparseObs :=
  ProbabilityTheory.cond (sparsePopulationMeasure α x N) (sparseTargetObservation j b)

private theorem conditional_prior_pos (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hj : 1 ≤ j) : 0 < sparsePriorMass α x N j := by
  linarith [(sparsePriorMass_bounds α x N j hj).1]

private theorem conditional_low_ne_zero (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hj : 1 ≤ j) :
    sparsePopulationMeasure α x N (sparseLowObservation j) ≠ 0 := by
  rw [sparsePopulationMeasure_lowObservation]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (conditional_prior_pos α x N j hj)))

private theorem conditional_signed_target_ne_zero (α : ℝ) (x : ℕ → ℝ)
    (N : ℕ → ℕ) (j : ℕ) (b : Bool) (hj : 1 ≤ j) :
    sparseSignedLabelMeasure α x N ({(j, b)} : Set (ℕ × Bool)) ≠ 0 := by
  rw [sparseSignedLabelMeasure_singleton, sparseLabelMass_eq_positiveMass α x N j hj]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr
    (div_pos (sparsePositiveMass_pos α x N j hj) (by norm_num)))

private theorem conditional_target_ne_zero (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (b : Bool) (hj : 1 ≤ j) :
    sparsePopulationMeasure α x N (sparseTargetObservation j b) ≠ 0 := by
  rw [sparsePopulationMeasure_targetObservation,
    sparseLabelMass_eq_positiveMass α x N j hj]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr
    (div_pos (sq_pos_of_pos (sparsePositiveMass_pos α x N j hj)) (by norm_num)))

theorem sparseLowObservationMeasure_probability :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ), 1 ≤ j →
  IsProbabilityMeasure (sparseLowObservationMeasure α x N j) := by
  intro α x N j hj
  let : IsProbabilityMeasure (sparsePopulationMeasure α x N) :=
    sparsePopulationMeasure_probability α x N
  exact ProbabilityTheory.cond_isProbabilityMeasure (conditional_low_ne_zero α x N j hj)

theorem sparseTargetObservationMeasure_probability :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) (b : Bool), 1 ≤ j →
  IsProbabilityMeasure (sparseTargetObservationMeasure α x N j b) := by
  intro α x N j b hj
  let : IsProbabilityMeasure (sparsePopulationMeasure α x N) :=
    sparsePopulationMeasure_probability α x N
  exact ProbabilityTheory.cond_isProbabilityMeasure (conditional_target_ne_zero α x N j b hj)

theorem sparseBalancedPairPattern_cond_eq_pi :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  1 ≤ j → i < k →
  ProbabilityTheory.cond (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N))
    (sparseBalancedPairPattern j i k b) =
  Measure.pi (fun l : Fin n =>
    if l = i then sparseTargetObservationMeasure α x N j b
    else if l = k then sparseTargetObservationMeasure α x N j (!b)
    else sparseLowObservationMeasure α x N j) := by
  intro α x N n j i k b hj hik
  classical
  let μ := sparsePopulationMeasure α x N
  let : IsProbabilityMeasure μ := sparsePopulationMeasure_probability α x N
  let B : Fin n → Set SparseObs := fun l =>
    if l = i then sparseTargetObservation j b
    else if l = k then sparseTargetObservation j (!b)
    else sparseLowObservation j
  have hB (l : Fin n) : MeasurableSet (B l) := by
    dsimp [B]
    split_ifs
    · exact measurableSet_sparseTargetObservation j b
    · exact measurableSet_sparseTargetObservation j (!b)
    · exact measurableSet_sparseLowObservation j
  have hset : sparseBalancedPairPattern j i k b =
      ⋂ l : Fin n, (fun ω : Fin n → SparseObs => ω l) ⁻¹' B l := by
    rw [sparseBalancedPairPattern_eq_pi n j i k b hik]
    ext ω
    simp [B, Set.mem_pi]
  have hA : (Measure.pi (fun _ : Fin n => μ))
      (⋂ l : Fin n, (fun ω : Fin n → SparseObs => ω l) ⁻¹' B l) ≠ 0 := by
    rw [← hset]
    intro hz
    change (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N))
      (sparseBalancedPairPattern j i k b) = 0 at hz
    have hp := sparseBalancedPairPattern_real_pos α x N n j i k b hj hik
    simp only [measureReal_def, hz, ENNReal.toReal_zero, lt_self_iff_false] at hp
  have h := Shao.Probability.indep_cond_joint_map_eq_pi
    (μ := Measure.pi (fun _ : Fin n => μ))
    (X := fun l : Fin n => fun ω : Fin n → SparseObs => ω l)
    (fun l => measurable_pi_apply l)
    (ProbabilityTheory.iIndepFun_pi (X := fun _ : Fin n => id)
      (fun _ => aemeasurable_id)) B hB hA
  have hm (l : Fin n) : (Measure.pi (fun _ : Fin n => μ)).map
      (fun ω : Fin n → SparseObs => ω l) = μ :=
    (measurePreserving_eval (fun _ : Fin n => μ) l).map_eq
  have hid : (fun ω : Fin n → SparseObs => fun l : Fin n => ω l) = id := rfl
  rw [hid, Measure.map_id, ← hset] at h
  calc
    ProbabilityTheory.cond (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N))
        (sparseBalancedPairPattern j i k b) =
        Measure.pi (fun l : Fin n => ProbabilityTheory.cond μ (B l)) := by
      simpa only [hm] using h
    _ = _ := by
      congr 1
      funext l
      dsimp only [B]
      split_ifs <;> rfl

theorem iIndepFun_sparseBalancedPairPattern_cond :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  1 ≤ j → i < k →
  ProbabilityTheory.iIndepFun (fun l : Fin n => fun ω : Fin n → SparseObs => ω l)
    (ProbabilityTheory.cond (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N))
      (sparseBalancedPairPattern j i k b)) := by
  intro α x N n j i k b hj hik
  classical
  rw [sparseBalancedPairPattern_cond_eq_pi α x N n j i k b hj hik]
  let ν : Fin n → Measure SparseObs := fun l =>
    if l = i then sparseTargetObservationMeasure α x N j b
    else if l = k then sparseTargetObservationMeasure α x N j (!b)
    else sparseLowObservationMeasure α x N j
  let : ∀ l : Fin n, IsProbabilityMeasure (ν l) := by
    intro l
    dsimp [ν]
    split_ifs
    · exact sparseTargetObservationMeasure_probability α x N j b hj
    · exact sparseTargetObservationMeasure_probability α x N j (!b) hj
    · exact sparseLowObservationMeasure_probability α x N j hj
  exact ProbabilityTheory.iIndepFun_pi (μ := ν) (X := fun _ : Fin n => id)
    (fun _ => aemeasurable_id)

theorem sparseBalancedPairPattern_cond_coordinate_law :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  1 ≤ j → i < k → ∀ l : Fin n,
  (ProbabilityTheory.cond (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N))
    (sparseBalancedPairPattern j i k b)).map (fun ω : Fin n → SparseObs => ω l) =
    if l = i then sparseTargetObservationMeasure α x N j b
    else if l = k then sparseTargetObservationMeasure α x N j (!b)
    else sparseLowObservationMeasure α x N j := by
  intro α x N n j i k b hj hik l
  classical
  rw [sparseBalancedPairPattern_cond_eq_pi α x N n j i k b hj hik]
  let ν : Fin n → Measure SparseObs := fun l =>
    if l = i then sparseTargetObservationMeasure α x N j b
    else if l = k then sparseTargetObservationMeasure α x N j (!b)
    else sparseLowObservationMeasure α x N j
  let : ∀ l : Fin n, IsProbabilityMeasure (ν l) := by
    intro l
    dsimp [ν]
    split_ifs
    · exact sparseTargetObservationMeasure_probability α x N j b hj
    · exact sparseTargetObservationMeasure_probability α x N j (!b) hj
    · exact sparseLowObservationMeasure_probability α x N j hj
  exact (measurePreserving_eval ν l).map_eq

private theorem conditional_prod {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (s : Set A) (t : Set B) :
    ProbabilityTheory.cond (μ.prod ν) (s ×ˢ t) =
      (ProbabilityTheory.cond μ s).prod (ProbabilityTheory.cond ν t) := by
  unfold ProbabilityTheory.cond
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.prod_prod, ENNReal.mul_inv (Or.inr (measure_ne_top ν t))
      (Or.inl (measure_ne_top μ s)), Measure.prod_restrict]

private theorem conditional_low_label_probability (α : ℝ) (x : ℕ → ℝ)
    (N : ℕ → ℕ) (j : ℕ) (hj : 1 ≤ j) :
    IsProbabilityMeasure (ProbabilityTheory.cond (sparseSignedLabelMeasure α x N)
      ((Prod.fst : ℕ × Bool → ℕ) ⁻¹' Set.Iio j)) := by
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  apply ProbabilityTheory.cond_isProbabilityMeasure
  rw [← Measure.map_apply measurable_fst measurableSet_Iio,
    sparseSignedLabelMeasure_first, sparseLabelMeasure_Iio]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (conditional_prior_pos α x N j hj))

private theorem conditional_low_product (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) :
    sparseLowObservationMeasure α x N j =
      (Shao.OQ5.P35.noiseLaw.prod
        (ProbabilityTheory.cond (sparseSignedLabelMeasure α x N)
          ((Prod.fst : ℕ × Bool → ℕ) ⁻¹' Set.Iio j))).prod
        (ProbabilityTheory.cond (sparseSignedLabelMeasure α x N)
          ((Prod.fst : ℕ × Bool → ℕ) ⁻¹' Set.Iio j)) := by
  let : IsProbabilityMeasure (sparseGBaseMeasure α x N) :=
    sparseGBaseMeasure_probability α x N
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  have hset : sparseLowObservation j =
      ((Set.univ : Set ℝ) ×ˢ ((Prod.fst : ℕ × Bool → ℕ) ⁻¹' Set.Iio j)) ×ˢ
        ((Prod.fst : ℕ × Bool → ℕ) ⁻¹' Set.Iio j) := by
    ext z
    simp [sparseLowObservation]
  rw [sparseLowObservationMeasure, hset, sparsePopulationMeasure,
    conditional_prod, sparseGBaseMeasure, conditional_prod, ProbabilityTheory.cond_univ]

theorem sparseLowObservationG_indep_Z :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ), 1 ≤ j →
  ProbabilityTheory.IndepFun (sparsePopulationG α x N) (sparsePopulationZ α x N)
    (sparseLowObservationMeasure α x N j) := by
  intro α x N j hj
  let ν := ProbabilityTheory.cond (sparseSignedLabelMeasure α x N)
    ((Prod.fst : ℕ × Bool → ℕ) ⁻¹' Set.Iio j)
  let : IsProbabilityMeasure ν := conditional_low_label_probability α x N j hj
  rw [conditional_low_product]
  exact ProbabilityTheory.indepFun_prod
    (μ := Shao.OQ5.P35.noiseLaw.prod ν) (ν := ν)
    (X := sparseG α x N) (Y := sparseSignedAmplitude α x N)
    (measurable_sparseG α x N) (measurable_sparseSignedAmplitude α x N)

private theorem conditional_memLp {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {s : Set A} {f : A → ℝ} (hf : MemLp f 2 μ) (hs : μ s ≠ 0) :
    MemLp f 2 (ProbabilityTheory.cond μ s) := by
  exact (hf.restrict s).smul_measure (by simpa using hs)

private theorem conditional_population_G_sq (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hα : 0 < α) (hN : SparseSelectionCore α x N) :
    Integrable (fun z => (sparsePopulationG α x N z) ^ 2) (sparsePopulationMeasure α x N) := by
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  exact (integrable_sparseG_sq α x N hα hN).comp_fst _

private theorem conditional_population_Z_sq (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hα : 0 < α) :
    Integrable (fun z => (sparsePopulationZ α x N z) ^ 2) (sparsePopulationMeasure α x N) := by
  let : IsProbabilityMeasure (sparseGBaseMeasure α x N) :=
    sparseGBaseMeasure_probability α x N
  exact (integrable_sparseSignedAmplitude_sq α x N hα).comp_snd _

theorem memLp_sparseLowObservationG_two :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  MemLp (sparsePopulationG α x N) 2 (sparseLowObservationMeasure α x N j) := by
  intro α x N j hα hN hj
  exact conditional_memLp
    ((memLp_two_iff_integrable_sq (measurable_sparsePopulationG α x N).aestronglyMeasurable).2
      (conditional_population_G_sq α x N hα hN)) (conditional_low_ne_zero α x N j hj)

theorem memLp_sparseLowObservationZ_two :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ), 0 < α → 1 ≤ j →
  MemLp (sparsePopulationZ α x N) 2 (sparseLowObservationMeasure α x N j) := by
  intro α x N j hα hj
  exact conditional_memLp
    ((memLp_two_iff_integrable_sq (measurable_sparsePopulationZ α x N).aestronglyMeasurable).2
      (conditional_population_Z_sq α x N hα)) (conditional_low_ne_zero α x N j hj)

private theorem conditional_integrable {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {s : Set A} {f : A → ℝ} (hf : Integrable f μ) (hs : μ s ≠ 0) :
    Integrable f (ProbabilityTheory.cond μ s) := by
  exact hf.restrict.smul_measure (by simpa using hs)

private theorem conditional_low_signed_mean (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (f : ℕ × Bool → ℝ)
    (hf : Integrable f (sparseSignedLabelMeasure α x N))
    (hflip : ∀ l : ℕ, f (l, false) + f (l, true) = 0) :
    (∫ z, f z ∂ProbabilityTheory.cond (sparseSignedLabelMeasure α x N)
      ((Prod.fst : ℕ × Bool → ℕ) ⁻¹' Set.Iio j)) = 0 := by
  let L := (Prod.fst : ℕ × Bool → ℕ) ⁻¹' Set.Iio j
  have hL : MeasurableSet L := measurableSet_Iio.preimage measurable_fst
  have hi : Integrable (L.indicator f) (sparseSignedLabelMeasure α x N) := hf.indicator hL
  unfold ProbabilityTheory.cond
  rw [integral_smul_measure, ← integral_indicator hL,
    integral_sparseSignedLabelMeasure α x N (L.indicator f) hi]
  have hz : (∑' l : ℕ, (sparseLabelMass α x N l / 2) *
      (L.indicator f (l, false) + L.indicator f (l, true))) = 0 := by
    have hterm (l : ℕ) : (sparseLabelMass α x N l / 2) *
        (L.indicator f (l, false) + L.indicator f (l, true)) = 0 := by
      by_cases hl : l < j
      · simp [L, hl, hflip l]
      · simp [L, hl]
    simp only [hterm, tsum_zero]
  rw [hz, smul_zero]

theorem integral_sparseLowObservationG_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  (∫ z, sparsePopulationG α x N z ∂sparseLowObservationMeasure α x N j) = 0 := by
  intro α x N j hα hN hj
  let ν := ProbabilityTheory.cond (sparseSignedLabelMeasure α x N)
    ((Prod.fst : ℕ × Bool → ℕ) ⁻¹' Set.Iio j)
  let : IsProbabilityMeasure ν := conditional_low_label_probability α x N j hj
  have hne : sparseSignedLabelMeasure α x N
      ((Prod.fst : ℕ × Bool → ℕ) ⁻¹' Set.Iio j) ≠ 0 := by
    let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
      sparseSignedLabelMeasure_probability α x N
    rw [← Measure.map_apply measurable_fst measurableSet_Iio,
      sparseSignedLabelMeasure_first, sparseLabelMeasure_Iio]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (conditional_prior_pos α x N j hj))
  have hD : Integrable (sparseSignedShift α x N) ν :=
    conditional_integrable (integrable_sparseSignedShift α x N hα hN) hne
  have hmean : (∫ z, sparseSignedShift α x N z ∂ν) = 0 :=
    conditional_low_signed_mean α x N j (sparseSignedShift α x N)
      (integrable_sparseSignedShift α x N hα hN) (by intro l; simp [sparseSignedShift])
  rw [conditional_low_product]
  change (∫ z : SparseObs, sparseG α x N z.1
    ∂((Shao.OQ5.P35.noiseLaw.prod ν).prod ν)) = 0
  rw [integral_fun_fst (μ := Shao.OQ5.P35.noiseLaw.prod ν) (ν := ν)]
  have hA := Shao.OQ5.P35.integrable_noiseLaw_id.comp_fst ν
  have hD' := hD.comp_snd Shao.OQ5.P35.noiseLaw
  change ν.real Set.univ *
    (∫ z : ℝ × (ℕ × Bool), z.1 + sparseSignedShift α x N z.2
      ∂(Shao.OQ5.P35.noiseLaw.prod ν)) = 0
  rw [integral_add hA hD',
    integral_fun_fst (μ := Shao.OQ5.P35.noiseLaw) (ν := ν) (fun a : ℝ => a),
    integral_fun_snd (μ := Shao.OQ5.P35.noiseLaw) (ν := ν) (sparseSignedShift α x N),
    Shao.OQ5.P35.integral_noiseLaw_id, hmean]
  simp

theorem integral_sparseLowObservationZ_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ), 0 < α → 1 ≤ j →
  (∫ z, sparsePopulationZ α x N z ∂sparseLowObservationMeasure α x N j) = 0 := by
  intro α x N j hα hj
  let ν := ProbabilityTheory.cond (sparseSignedLabelMeasure α x N)
    ((Prod.fst : ℕ × Bool → ℕ) ⁻¹' Set.Iio j)
  let : IsProbabilityMeasure ν := conditional_low_label_probability α x N j hj
  have hmean : (∫ z, sparseSignedAmplitude α x N z ∂ν) = 0 :=
    conditional_low_signed_mean α x N j (sparseSignedAmplitude α x N)
      (integrable_sparseSignedAmplitude α x N hα) (by intro l; simp [sparseSignedAmplitude])
  rw [conditional_low_product]
  change (∫ z : SparseObs, sparseSignedAmplitude α x N z.2
    ∂((Shao.OQ5.P35.noiseLaw.prod ν).prod ν)) = 0
  rw [integral_fun_snd, hmean]
  simp

private theorem conditional_second_le {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {s : Set A} {f : A → ℝ} {q : ℝ}
    (hf : Integrable (fun z => f z ^ 2) μ) (hq : 0 ≤ q)
    (hm : μ s = ENNReal.ofReal q) :
    (∫ z, f z ^ 2 ∂ProbabilityTheory.cond μ s) ≤ (∫ z, f z ^ 2 ∂μ) / q := by
  unfold ProbabilityTheory.cond
  rw [integral_smul_measure, ENNReal.toReal_inv, hm, ENNReal.toReal_ofReal hq,
    smul_eq_mul, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (setIntegral_le_integral hf (Filter.Eventually.of_forall
    (fun z => sq_nonneg (f z)))) (inv_nonneg.mpr hq)

theorem integral_sparseLowObservationG_sq_le :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  (∫ z, (sparsePopulationG α x N z) ^ 2 ∂sparseLowObservationMeasure α x N j) ≤
    (∫ z, (sparsePopulationG α x N z) ^ 2 ∂sparsePopulationMeasure α x N) /
      sparsePriorMass α x N j ^ 2 := by
  intro α x N j hα hN _hj
  exact conditional_second_le (conditional_population_G_sq α x N hα hN)
    (sq_nonneg _) (sparsePopulationMeasure_lowObservation α x N j)

theorem integral_sparseLowObservationZ_sq_le :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ), 0 < α → 1 ≤ j →
  (∫ z, (sparsePopulationZ α x N z) ^ 2 ∂sparseLowObservationMeasure α x N j) ≤
    (∫ z, (sparsePopulationZ α x N z) ^ 2 ∂sparsePopulationMeasure α x N) /
      sparsePriorMass α x N j ^ 2 := by
  intro α x N j hα _hj
  exact conditional_second_le (conditional_population_Z_sq α x N hα)
    (sq_nonneg _) (sparsePopulationMeasure_lowObservation α x N j)

private theorem conditional_target_product (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (b : Bool) :
    sparseTargetObservationMeasure α x N j b =
      (Shao.OQ5.P35.noiseLaw.prod
        (ProbabilityTheory.cond (sparseSignedLabelMeasure α x N) {(j, true)})).prod
        (ProbabilityTheory.cond (sparseSignedLabelMeasure α x N) {(j, b)}) := by
  let : IsProbabilityMeasure (sparseGBaseMeasure α x N) :=
    sparseGBaseMeasure_probability α x N
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  have hset : sparseTargetObservation j b =
      ((Set.univ : Set ℝ) ×ˢ ({(j, true)} : Set (ℕ × Bool))) ×ˢ
        ({(j, b)} : Set (ℕ × Bool)) := by
    ext z
    simp [sparseTargetObservation]
  rw [sparseTargetObservationMeasure, hset, sparsePopulationMeasure,
    conditional_prod, sparseGBaseMeasure, conditional_prod, ProbabilityTheory.cond_univ]

theorem sparseTargetObservation_noise_law :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) (b : Bool), 1 ≤ j →
  (sparseTargetObservationMeasure α x N j b).map (fun z : SparseObs => z.1.1) =
    Shao.OQ5.P35.noiseLaw := by
  intro α x N j b hj
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  let : IsProbabilityMeasure (ProbabilityTheory.cond (sparseSignedLabelMeasure α x N)
      ({(j, true)} : Set (ℕ × Bool))) :=
    ProbabilityTheory.cond_isProbabilityMeasure (conditional_signed_target_ne_zero α x N j true hj)
  let : IsProbabilityMeasure (ProbabilityTheory.cond (sparseSignedLabelMeasure α x N)
      ({(j, b)} : Set (ℕ × Bool))) :=
    ProbabilityTheory.cond_isProbabilityMeasure (conditional_signed_target_ne_zero α x N j b hj)
  rw [conditional_target_product]
  change Measure.map (Prod.fst ∘ Prod.fst) _ = _
  rw [← Measure.map_map measurable_fst measurable_fst, Measure.map_fst_prod,
    measure_univ, one_smul, Measure.map_fst_prod, measure_univ, one_smul]

private theorem conditional_target_ae_mem (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (b : Bool) :
    ∀ᵐ z : SparseObs ∂sparseTargetObservationMeasure α x N j b,
      z ∈ sparseTargetObservation j b := by
  exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_sparseTargetObservation j b)) _

theorem sparseTargetObservationG_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) (b : Bool), 1 ≤ j →
  ∀ᵐ z : SparseObs ∂sparseTargetObservationMeasure α x N j b,
    sparsePopulationG α x N z = z.1.1 + sparseLevelShift α x N j := by
  intro α x N j b _hj
  filter_upwards [conditional_target_ae_mem α x N j b] with z hz
  change z.1.2 = (j, true) ∧ z.2 = (j, b) at hz
  simp [sparsePopulationG, sparseG, sparseSignedShift, hz.1]

theorem sparseTargetObservationZ_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) (b : Bool), 1 ≤ j →
  ∀ᵐ z : SparseObs ∂sparseTargetObservationMeasure α x N j b,
    sparsePopulationZ α x N z =
      if b = true then sparseLevelAmplitude α x N j else -sparseLevelAmplitude α x N j := by
  intro α x N j b _hj
  filter_upwards [conditional_target_ae_mem α x N j b] with z hz
  change z.1.2 = (j, true) ∧ z.2 = (j, b) at hz
  simp [sparsePopulationZ, sparseSignedAmplitude, hz.2]

end Shao.OQ5.P53
