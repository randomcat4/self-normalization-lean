import Shao.OQ4.FiniteSurvivalLaplace
import Shao.OQ4.KilledBlockBounds

/-! Reflection transfers a single actual CDF premise to both actual survival inputs. -/

namespace Shao.OQ4

open MeasureTheory ProbabilityTheory

noncomputable def reflectedLaw (ν : Measure ℝ) : Measure ℝ := ν.map (fun x => -x)

instance reflectedLaw_isProbabilityMeasure (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (reflectedLaw ν) where
  measure_univ := by
    rw [reflectedLaw, Measure.map_apply measurable_neg MeasurableSet.univ]
    simp

/-- Coordinatewise reflection of the genuine product law, including the empty product. -/
theorem iid_reflected_product_law (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℕ) :
    Measure.pi (fun _ : Fin t => reflectedLaw ν) =
      (Measure.pi (fun _ : Fin t => ν)).map (fun a : Shao.Path t => -a) := by
  change Measure.pi (fun _ : Fin t => ν.map (fun x => -x)) =
    (Measure.pi (fun _ : Fin t => ν)).map (fun a i => -(a i))
  exact
    (Measure.pi_map_pi (μ := fun _ : Fin t => ν)
      (f := fun _ => fun x : ℝ => -x) (fun _ => measurable_neg.aemeasurable)).symm

theorem reflected_prefixSum {t : ℕ} (a : Shao.Path t) (k : ℕ) :
    Shao.prefixSum (-a) k = -Shao.prefixSum a k := Shao.prefixSum_neg a k

theorem reflection_preimage_closedUpper (t : ℕ) (d : ℝ) :
    (fun a : Shao.Path t => -a) ⁻¹' Shao.closedUpper d = lowerBlockSurvival d := rfl

theorem reflection_preimage_lowerBlockSurvival (t : ℕ) (d : ℝ) :
    (fun a : Shao.Path t => -a) ⁻¹' lowerBlockSurvival d = Shao.closedUpper d := by
  ext a
  simp [lowerBlockSurvival]

theorem lowerBlockSurvival_eq_closed_lower_prefixes (t : ℕ) (d : ℝ) :
    (lowerBlockSurvival d : Set (Shao.Path t)) =
      {a | ∀ k : ℕ, k ≤ t → -d ≤ Shao.prefixSum a k} := by
  ext a
  simp only [lowerBlockSurvival, Set.mem_ofPred_eq, Shao.closedUpper, Shao.prefixSum_neg]
  constructor <;> intro h k hk <;> specialize h k hk <;> linarith

theorem reflected_closedUpper_probability (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (t : ℕ) (d : ℝ) :
    (Measure.pi (fun _ : Fin t => reflectedLaw ν)).real (Shao.closedUpper d) =
      (Measure.pi (fun _ : Fin t => ν)).real (lowerBlockSurvival d) := by
  rw [iid_reflected_product_law, measureReal_def,
    Measure.map_apply (by fun_prop) (measurableSet_closedUpper t d)]
  rfl

theorem reflected_lowerBlockSurvival_probability (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (t : ℕ) (d : ℝ) :
    (Measure.pi (fun _ : Fin t => reflectedLaw ν)).real (lowerBlockSurvival d) =
      (Measure.pi (fun _ : Fin t => ν)).real (Shao.closedUpper d) := by
  rw [iid_reflected_product_law, measureReal_def,
    Measure.map_apply (by fun_prop) (measurableSet_lowerBlockSurvival t d),
    reflection_preimage_lowerBlockSurvival]
  rfl

/-- Reflection of the actual standard Gaussian CDF; only the Gaussian is atomless. -/
theorem standardNormalCDF_reflection (x : ℝ) :
    standardNormalCDF (-x) = 1 - standardNormalCDF x := by
  let γ := gaussianReal 0 1
  have : NullSingletonClass γ :=
    nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)
  have hmap : γ.map (fun y : ℝ => -y) = γ := by
    simpa [γ] using (gaussianReal_map_neg (μ := 0) (v := 1))
  have he : γ.real (Set.Iic (-x)) = γ.real (Set.Ici x) := by
    calc
      _ = (γ.map (fun y : ℝ => -y)).real (Set.Iic (-x)) := by rw [hmap]
      _ = γ.real (Set.Ici x) := by
        apply congrArg ENNReal.toReal
        rw [Measure.map_apply measurable_neg measurableSet_Iic]
        congr 1
        ext y
        simp
  have hne : ∀ᵐ y ∂γ, y ≠ x := by simp [ae_iff]
  have ha : γ.real (Set.Ici x) = γ.real (Set.Ioi x) := by
    apply measureReal_congr
    filter_upwards [hne] with y hy
    simp only [Set.mem_Ici, Set.mem_Ioi]
    simp [le_iff_lt_or_eq, Ne.symm hy]
  have hc := measureReal_add_measureReal_compl (μ := γ) (s := Set.Iic x) measurableSet_Iic
  simp only [Set.compl_Iic, probReal_univ] at hc
  rw [standardNormalCDF_eq_real, standardNormalCDF_eq_real]
  change γ.real (Set.Iic (-x)) = 1 - γ.real (Set.Iic x)
  linarith

/-- A left-cutoff limit preserves the CDF error even when the tested law has atoms. -/
theorem strict_cdf_error_of_standardNormalCDF_error {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (ε : ℝ)
    (hCDF : ∀ x, |P.real {a | X a ≤ x} - standardNormalCDF x| ≤ ε) (x : ℝ) :
    |P.real {a | X a < x} - standardNormalCDF x| ≤ ε := by
  have hu : P.real {a | X a < x} ≤ standardNormalCDF x + ε := by
    have hm : P.real {a | X a < x} ≤ P.real {a | X a ≤ x} :=
      measureReal_mono (fun a h => show X a ≤ x from (show X a < x from h).le)
    linarith [(abs_le.mp (hCDF x)).2]
  have hl : standardNormalCDF x - ε ≤ P.real {a | X a < x} := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    have hm : P.real {a | X a ≤ x - δ} ≤ P.real {a | X a < x} :=
      measureReal_mono (fun _ h => by dsimp only [Set.mem_ofPred_eq] at *; linarith)
    have hg := (abs_le.mp (standardNormalCDF_lipschitz x (x - δ))).2
    rw [show x - (x - δ) = δ by ring, abs_of_pos hδ] at hg
    linarith [(abs_le.mp (hCDF (x - δ))).1]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The reflected product has the same CDF error; no reflected BE input is assumed. -/
theorem iid_reflected_cdf_error (ν : Measure ℝ) [IsProbabilityMeasure ν] (β C_BE : ℝ)
    (hCDF : ∀ t : ℕ, 1 ≤ t → ∀ x : ℝ,
      |(Measure.pi (fun _ : Fin t => ν)).real
          {a | Shao.prefixSum a t / Real.sqrt (t : ℝ) ≤ x} - standardNormalCDF x| ≤
        C_BE * β / Real.sqrt (t : ℝ)) :
    ∀ t : ℕ, 1 ≤ t → ∀ x : ℝ,
      |(Measure.pi (fun _ : Fin t => reflectedLaw ν)).real
          {a | Shao.prefixSum a t / Real.sqrt (t : ℝ) ≤ x} - standardNormalCDF x| ≤
        C_BE * β / Real.sqrt (t : ℝ) := by
  intro t ht x
  let P := Measure.pi (fun _ : Fin t => ν)
  let X : Shao.Path t → ℝ := fun a => Shao.prefixSum a t / Real.sqrt (t : ℝ)
  have hX : Measurable X := (Shao.measurable_prefixSum t).div measurable_const
  have hs := strict_cdf_error_of_standardNormalCDF_error P X
    (C_BE * β / Real.sqrt (t : ℝ)) (hCDF t ht) (-x)
  have hm : MeasurableSet {a : Shao.Path t | Shao.prefixSum a t / Real.sqrt (t : ℝ) ≤ x} := by
    exact measurableSet_le hX measurable_const
  have he : (Measure.pi (fun _ : Fin t => reflectedLaw ν)).real
      {a | Shao.prefixSum a t / Real.sqrt (t : ℝ) ≤ x} =
      1 - P.real {a | X a < -x} := by
    rw [iid_reflected_product_law, measureReal_def,
      Measure.map_apply (show Measurable (fun a : Shao.Path t => -a) by fun_prop) hm]
    have hset : (fun a : Shao.Path t => -a) ⁻¹'
        {a | Shao.prefixSum a t / Real.sqrt (t : ℝ) ≤ x} = {a | X a < -x}ᶜ := by
      ext a
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Shao.prefixSum_neg,
        Set.mem_compl_iff, not_lt, X, neg_div]
      constructor <;> intro h <;> linarith
    rw [hset]
    change P.real {a | X a < -x}ᶜ = 1 - P.real {a | X a < -x}
    simpa only [probReal_univ] using measureReal_compl (μ := P) (measurableSet_lt hX measurable_const)
  rw [he]
  have hg := standardNormalCDF_reflection x
  exact abs_le.mpr ⟨by linarith [(abs_le.mp hs).2], by linarith [(abs_le.mp hs).1]⟩

/-- The actual interval predicate needs only an explicit BE parameter β ≥ 1, not moments. -/
theorem iidIntervalConcentration_of_standardNormalCDF_error (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (β C_BE : ℝ) (hβ : 1 ≤ β) (hC : 0 ≤ C_BE)
    (hCDF : ∀ t : ℕ, 1 ≤ t → ∀ x : ℝ,
      |(Measure.pi (fun _ : Fin t => ν)).real
          {a | Shao.prefixSum a t / Real.sqrt (t : ℝ) ≤ x} - standardNormalCDF x| ≤
        C_BE * β / Real.sqrt (t : ℝ)) :
    iidIntervalConcentration ν β (1 + 2 * C_BE) := by
  intro t ht a
  have hs : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < t by omega))
  let X : Shao.Path t → ℝ := fun b => Shao.prefixSum b t / Real.sqrt (t : ℝ)
  have hX : Measurable X := (Shao.measurable_prefixSum t).div measurable_const
  let μ : Measure ℝ := (Measure.pi (fun _ : Fin t => ν)).map X
  have : IsProbabilityMeasure μ := by
    constructor
    change ((Measure.pi (fun _ : Fin t => ν)).map X) Set.univ = 1
    rw [Measure.map_apply hX MeasurableSet.univ]
    simp
  have hCDFμ (x : ℝ) : |μ.real (Set.Iic x) - standardNormalCDF x| ≤
      C_BE * β / Real.sqrt (t : ℝ) := by
    change |(((Measure.pi (fun _ : Fin t => ν)).map X) (Set.Iic x)).toReal - standardNormalCDF x| ≤ _
    rw [Measure.map_apply hX measurableSet_Iic]
    exact hCDF t ht x
  have heq : X ⁻¹' Set.Icc (a / Real.sqrt (t : ℝ)) ((a + 1) / Real.sqrt (t : ℝ)) =
      {b | Shao.prefixSum b t ∈ Set.Icc a (a + 1)} := by
    ext b
    simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_ofPred_eq, X, div_le_div_iff_of_pos_right hs]
  have hlaw : (Measure.pi (fun _ : Fin t => ν)).real {b | Shao.prefixSum b t ∈ Set.Icc a (a + 1)} =
      μ.real (Set.Icc (a / Real.sqrt (t : ℝ)) ((a + 1) / Real.sqrt (t : ℝ))) := by
    simp only [μ, measureReal_def, Measure.map_apply hX measurableSet_Icc, heq]
  have hclosed := closed_interval_mass_bound_from_cdf μ 1 (C_BE * β / Real.sqrt (t : ℝ))
    standardNormalCDF (by norm_num) (by positivity)
    (fun x y => by simpa only [one_mul] using standardNormalCDF_lipschitz x y) hCDFμ
    (a / Real.sqrt (t : ℝ)) ((a + 1) / Real.sqrt (t : ℝ))
    ((div_le_div_iff_of_pos_right hs).2 (by linarith))
  rw [← hlaw] at hclosed
  calc
    _ ≤ 1 * ((a + 1) / Real.sqrt (t : ℝ) - a / Real.sqrt (t : ℝ)) +
        2 * (C_BE * β / Real.sqrt (t : ℝ)) := hclosed
    _ = (1 + 2 * C_BE * β) / Real.sqrt (t : ℝ) := by ring
    _ ≤ (1 + 2 * C_BE) * β / Real.sqrt (t : ℝ) :=
      div_le_div_of_nonneg_right (by nlinarith) hs.le

/-- Separate original SP identities give both genuine closed survival bounds. -/
theorem iidOneSidedSurvival_of_cdf_and_two_original_sp (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (β C_BE : ℝ) (hβ : 1 ≤ β) (hC : 0 ≤ C_BE)
    (hCDF : ∀ t : ℕ, 1 ≤ t → ∀ x : ℝ,
      |(Measure.pi (fun _ : Fin t => ν)).real
          {a | Shao.prefixSum a t / Real.sqrt (t : ℝ) ≤ x} - standardNormalCDF x| ≤
        C_BE * β / Real.sqrt (t : ℝ))
    (hSP : ∀ L : ℝ, 0 < L → ∀ s : ℝ, 0 < s → s < 1 →
      laplaceG (maxLaplaceMean ν L) s = Real.exp (laplaceW (endpointLaplaceMean ν L) s))
    (hSPneg : ∀ L : ℝ, 0 < L → ∀ s : ℝ, 0 < s → s < 1 →
      laplaceG (maxLaplaceMean (reflectedLaw ν) L) s =
        Real.exp (laplaceW (endpointLaplaceMean (reflectedLaw ν) L) s)) :
    iidOneSidedSurvival ν β (Real.sqrt 2 * Real.exp (6 + 3 * C_BE)) := by
  intro t ht d hd
  constructor
  · exact closedUpper_bound_of_cdf_and_original_sp ν C_BE β hC hβ hCDF hSP d hd t ht
  · rw [← reflected_closedUpper_probability ν t d]
    exact closedUpper_bound_of_cdf_and_original_sp (reflectedLaw ν) C_BE β hC hβ
      (iid_reflected_cdf_error ν β C_BE hCDF) hSPneg d hd t ht

theorem reflected_survival_constant_nonneg (C_BE : ℝ) :
    0 ≤ Real.sqrt 2 * Real.exp (6 + 3 * C_BE) := by positivity

theorem reflected_concentration_constant_nonneg (C_BE : ℝ) (hC : 0 ≤ C_BE) :
    0 ≤ 1 + 2 * C_BE := by positivity

/-- Joint source-bound inputs for KilledBlockBounds; BE and both SP identities remain premises. -/
theorem iid_survival_and_concentration_of_cdf_and_two_original_sp (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (β C_BE : ℝ) (hβ : 1 ≤ β) (hC : 0 ≤ C_BE)
    (hCDF : ∀ t : ℕ, 1 ≤ t → ∀ x : ℝ,
      |(Measure.pi (fun _ : Fin t => ν)).real
          {a | Shao.prefixSum a t / Real.sqrt (t : ℝ) ≤ x} - standardNormalCDF x| ≤
        C_BE * β / Real.sqrt (t : ℝ))
    (hSP : ∀ L : ℝ, 0 < L → ∀ s : ℝ, 0 < s → s < 1 →
      laplaceG (maxLaplaceMean ν L) s = Real.exp (laplaceW (endpointLaplaceMean ν L) s))
    (hSPneg : ∀ L : ℝ, 0 < L → ∀ s : ℝ, 0 < s → s < 1 →
      laplaceG (maxLaplaceMean (reflectedLaw ν) L) s =
        Real.exp (laplaceW (endpointLaplaceMean (reflectedLaw ν) L) s)) :
    0 ≤ Real.sqrt 2 * Real.exp (6 + 3 * C_BE) ∧ 0 ≤ 1 + 2 * C_BE ∧
    iidOneSidedSurvival ν β (Real.sqrt 2 * Real.exp (6 + 3 * C_BE)) ∧
    iidIntervalConcentration ν β (1 + 2 * C_BE) :=
  ⟨reflected_survival_constant_nonneg C_BE, reflected_concentration_constant_nonneg C_BE hC,
    iidOneSidedSurvival_of_cdf_and_two_original_sp ν β C_BE hβ hC hCDF hSP hSPneg,
    iidIntervalConcentration_of_standardNormalCDF_error ν β C_BE hβ hC hCDF⟩

end Shao.OQ4
