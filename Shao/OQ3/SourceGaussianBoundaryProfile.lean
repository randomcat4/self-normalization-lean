import Shao.OQ3.StageLayerSeriesLimit
import Shao.OQ3.GaussianBoundaryConstant

namespace Shao.OQ3

open MeasureTheory Filter
open scoped Topology BigOperators

noncomputable section

private theorem gaussian_square_mass_eq_boundary_weight
    (mu : Measure ℝ) (q d : ℝ) (hq : 0 < q)
    (hT : 0 < transverseVariance mu) :
    (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (transverseVariance mu))).real
        {x : ℝ | -((q / 16) * d) ≤ x ^ 2} =
      gaussianBoundaryWeight (boundaryKappa q mu) d := by
  let T : ℝ := transverseVariance mu
  let r : ℝ := Real.sqrt T
  let kappa : ℝ := boundaryKappa q mu
  let B : Set ℝ := {x : ℝ | -((q / 16) * d) ≤ x ^ 2}
  let A : Set ℝ := {z : ℝ | -((z / kappa) ^ 2) ≤ d}
  have hr : 0 < r := Real.sqrt_pos.mpr hT
  have hr2 : r ^ 2 = T := Real.sq_sqrt hT.le
  have hk : 0 < kappa := div_pos (Real.sqrt_pos.mpr hq)
    (mul_pos (by norm_num) hr)
  have hkT : kappa ^ 2 * T = q / 16 := by
    dsimp only [kappa, boundaryKappa]
    rw [div_pow, mul_pow, Real.sq_sqrt hq.le, Real.sq_sqrt hT.le]
    dsimp only [T]
    field_simp
    ring
  have hvar : NNReal.mk (r ^ 2) (sq_nonneg r) = Real.toNNReal T := by
    apply NNReal.eq
    exact hr2.trans (Real.coe_toNNReal T hT.le).symm
  have hmap : (ProbabilityTheory.gaussianReal 0 (1 : NNReal)).map (fun z : ℝ => r * z) =
      ProbabilityTheory.gaussianReal 0 (Real.toNNReal T) := by
    calc
      _ = ProbabilityTheory.gaussianReal 0 (NNReal.mk (r ^ 2) (sq_nonneg r)) := by
        simpa only [mul_zero, mul_one] using
          ProbabilityTheory.gaussianReal_map_const_mul (μ := 0) (v := 1) r
      _ = _ := congrArg (ProbabilityTheory.gaussianReal 0) hvar
  have hBm : MeasurableSet B := (isClosed_le continuous_const (by fun_prop)).measurableSet
  have hpre : (fun z : ℝ => r * z) ⁻¹' B = A := by
    ext z
    change -((q / 16) * d) ≤ (r * z) ^ 2 ↔ -((z / kappa) ^ 2) ≤ d
    rw [mul_pow, hr2, div_pow, ← neg_div, div_le_iff₀ (sq_pos_of_pos hk)]
    rw [← hkT]
    constructor
    · intro hz
      apply (mul_le_mul_iff_of_pos_left hT).mp
      nlinarith only [hz]
    · intro hz
      have H := mul_le_mul_of_nonneg_left hz hT.le
      nlinarith only [H]
  have hmass :
      (ProbabilityTheory.gaussianReal 0 (Real.toNNReal T)).real B =
        (ProbabilityTheory.gaussianReal 0 (1 : NNReal)).real A := by
    change ((ProbabilityTheory.gaussianReal 0 (Real.toNNReal T)) B).toReal =
      ((ProbabilityTheory.gaussianReal 0 (1 : NNReal)) A).toReal
    rw [← hmap, Measure.map_apply (by fun_prop) hBm, hpre]
  change (ProbabilityTheory.gaussianReal 0 (Real.toNNReal T)).real B = _
  rw [hmass, measureReal_def, ProbabilityTheory.gaussianReal_apply_eq_integral 0
    (by norm_num : (1 : NNReal) ≠ 0), ENNReal.toReal_ofReal
      (integral_nonneg (ProbabilityTheory.gaussianPDFReal_nonneg 0 (1 : NNReal)))]
  change (∫ z : ℝ in A, ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z) =
    ∫ z : ℝ in A, Real.exp (-(z ^ 2) / 2) / Real.sqrt (2 * Real.pi)
  apply integral_congr_ae
  apply ae_of_all
  intro z
  simp only [ProbabilityTheory.gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one]
  ring

theorem stage_sourceGaussianLayerWeight_profile_and_integral
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (J : ℕ) (q : ℝ)
    (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = q / 4)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    (∀ d : ℝ, sourceGaussianLayerWeight mu q sourceEll d =
      gaussianBoundaryProfile sourceEll (boundaryKappa q mu) d) ∧
    Integrable (sourceGaussianLayerWeight mu q sourceEll) ∧
      (1 / Real.sqrt (normalVariance mu)) *
        (∫ d : ℝ, sourceGaussianLayerWeight mu q sourceEll d) =
          correctedInverseScale sourceEll q mu := by
  have hq : 0 < q := lt_trans zero_lt_one hq0
  have hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10 := by
    filter_upwards [hrange] with x hx
    obtain ⟨i, rfl⟩ := hx
    cases i with
    | inl i => exact (fixedAtom_bounds (Sum.inl i)).2
    | inr j => exact (fixedAtom_bounds (Sum.inr j.val)).2
  have hbase : ∀ i : Fin 4, 0 < mu.real {baseAtom i} := fun i => hpos (Sum.inl i)
  have hS := normalVariance_pos mu hb hbase
  have hD := parabolaCovariance_det_pos mu hb hbase
  have hT := transverseVariance_pos mu hb hbase
  have hX : Integrable (fun x : ℝ => x) mu :=
    integrable_continuous_of_fixed_bounds mu hb _ continuous_id
  have hX2 : Integrable (fun x : ℝ => x ^ 2) mu :=
    integrable_continuous_of_fixed_bounds mu hb _ (by fun_prop)
  have hmoment : (∫ x : ℝ, normalValue x ∂mu) =
      8 * (∫ x : ℝ, x ∂mu) - (∫ x : ℝ, x ^ 2 ∂mu) := by
    change (∫ x : ℝ, 8 * x - x ^ 2 ∂mu) = _
    rw [integral_sub (hX.const_mul 8) hX2, integral_const_mul]
  have hsecond : (∫ x : ℝ, x ^ 2 ∂mu) = q := by
    rw [hmeanY, hmeanX] at hmoment
    linarith only [hmoment]
  have hLp : MemLp (fun x : ℝ => x) 2 mu :=
    MemLp.of_bound continuous_id.aestronglyMeasurable (4 + Real.sqrt 10)
      (by simpa only [Real.norm_eq_abs] using hb)
  have hVar : ProbabilityTheory.variance (fun x : ℝ => x) mu = q - q ^ 2 / 16 := by
    rw [ProbabilityTheory.variance_eq_sub hLp]
    change (∫ x : ℝ, x ^ 2 ∂mu) - (∫ x : ℝ, x ∂mu) ^ 2 = _
    rw [hsecond, hmeanX]
    ring
  have hle := transverseVariance_le_variance_id mu hb hbase
  rw [hVar] at hle
  have hfrac : (1 : ℝ) / 30 < q / (32 * transverseVariance mu) := by
    apply (lt_div_iff₀ (mul_pos (by norm_num) hT)).mpr
    nlinarith only [hle, sq_nonneg (q - 1), hq0, hq1]
  have hgap : sourceEll < q / (32 * transverseVariance mu) :=
    sourceEll_lt_one_div_thirty.trans hfrac
  have hsmall : 32 * sourceEll * transverseVariance mu < q := by
    have H := (lt_div_iff₀ (mul_pos (by norm_num) hT)).mp hgap
    nlinarith only [H]
  have hTS : transverseVariance mu * normalVariance mu = (parabolaCovariance mu).det := by
    unfold transverseVariance
    exact div_mul_cancel₀ _ hS.ne'
  have hR : 0 < normalVariance mu - (32 * sourceEll / q) * (parabolaCovariance mu).det := by
    apply sub_pos.mpr
    apply (mul_lt_mul_iff_of_pos_right hq).mp
    have heq : ((32 * sourceEll / q) * (parabolaCovariance mu).det) * q =
        32 * sourceEll * (transverseVariance mu * normalVariance mu) := by
      rw [hTS]
      field_simp
    rw [heq]
    nlinarith only [mul_lt_mul_of_pos_right hsmall hS]
  have hk : 0 < boundaryKappa q mu :=
    div_pos (Real.sqrt_pos.mpr hq)
      (mul_pos (by norm_num) (Real.sqrt_pos.mpr hT))
  have hkGap : 2 * sourceEll < boundaryKappa q mu ^ 2 := by
    rw [boundaryKappa_sq q mu hq hS hD]
    apply (lt_div_iff₀ (mul_pos (by norm_num) hD)).mpr
    have H := mul_lt_mul_of_pos_right (sub_pos.mp hR) hq
    have heq : ((32 * sourceEll / q) * (parabolaCovariance mu).det) * q =
        32 * sourceEll * (parabolaCovariance mu).det := by field_simp
    rw [heq] at H
    nlinarith only [H]
  have hfun : sourceGaussianLayerWeight mu q sourceEll =
      gaussianBoundaryProfile sourceEll (boundaryKappa q mu) := by
    funext d
    unfold sourceGaussianLayerWeight gaussianBoundaryProfile
    rw [gaussian_square_mass_eq_boundary_weight mu q d hq hT]
  refine ⟨fun d => congrFun hfun d, ?_, ?_⟩
  · rw [hfun]
    exact gaussianBoundaryProfile_integrable sourceEll (boundaryKappa q mu)
      sourceEll_pos hk hkGap
  · rw [hfun]
    exact gaussianBoundary_constant_eq_corrected sourceEll q mu sourceEll_pos hq hS hD hR

end
end Shao.OQ3
