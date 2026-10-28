import Shao.OQ3.GaussianSmoothedRealDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace Shao.OQ3
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

theorem bounded_density_compact_test_gaussian_comparison
    (rho : Measure (ℝ × ℝ)) [IsProbabilityMeasure rho]
    (k : (ℝ × ℝ) → ℝ) (hk : Measurable k)
    (hk0 : ∀ z : ℝ × ℝ, 0 ≤ k z)
    (hrho : rho = volume.withDensity (fun z => ENNReal.ofReal (k z)))
    (K R C : ℝ) (hK : 0 ≤ K) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hbound : ∀ z : ℝ × ℝ, k z ≤ K)
    (f : (ℝ × ℝ) → ℝ) (hf : Measurable f)
    (hf0 : ∀ z : ℝ × ℝ, 0 ≤ f z) (hfC : ∀ z : ℝ × ℝ, f z ≤ C)
    (hzero : ∀ z : ℝ × ℝ, R < ‖z‖ → f z = 0) :
    let Phi : Measure (ℝ × ℝ) :=
      (ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1)
    Integrable f rho ∧ Integrable f Phi ∧
      (∫ z : ℝ × ℝ, f z ∂rho) ≤
        ((2 * Real.pi) * K * Real.exp (R ^ 2)) * (∫ z : ℝ × ℝ, f z ∂Phi) := by
  intro Phi
  let phi : (ℝ × ℝ) → ℝ := fun z =>
    ProbabilityTheory.gaussianPDFReal 0 1 z.1 * ProbabilityTheory.gaussianPDFReal 0 1 z.2
  have hphi0 (z : ℝ × ℝ) : 0 ≤ phi z :=
    mul_nonneg (ProbabilityTheory.gaussianPDFReal_nonneg _ _ _)
      (ProbabilityTheory.gaussianPDFReal_nonneg _ _ _)
  have hphiM : Measurable phi := by
    dsimp only [phi]
    exact ((ProbabilityTheory.measurable_gaussianPDFReal 0 1).comp measurable_fst).mul
      ((ProbabilityTheory.measurable_gaussianPDFReal 0 1).comp measurable_snd)
  have hphiEq (z : ℝ × ℝ) :
      phi z = (1 / (2 * Real.pi)) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) := by
    have h := (pair_gaussian_pdf_normalization (1 / 2) (by norm_num) z).1
    norm_num at h
    dsimp only [phi]
    rw [h, show (-z.2 ^ 2 + -z.1 ^ 2) / 2 = -(z.1 ^ 2 + z.2 ^ 2) / 2 by ring]
    congr 1
    field_simp [Real.pi_ne_zero] <;> ring
  have hPhi : Phi = volume.withDensity (fun z => ENNReal.ofReal (phi z)) := by
    have h := (pair_gaussian_noise_withDensity (1 : ℝ≥0) (by norm_num)).1
    change Phi = volume.withDensity (fun z =>
      ProbabilityTheory.gaussianPDF 0 1 z.1 * ProbabilityTheory.gaussianPDF 0 1 z.2) at h
    rw [h]
    congr 1
    funext z
    exact (ENNReal.ofReal_mul (ProbabilityTheory.gaussianPDFReal_nonneg 0 1 z.1)).symm
  have hi {m : Measure (ℝ × ℝ)} [IsProbabilityMeasure m] : Integrable f m := by
    apply (integrable_const C).mono' hf.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 z)]
      exact hfC z)
  have hiRho : Integrable f rho := hi
  have hiPhi : Integrable f Phi := hi
  have hki : Integrable (fun z : ℝ × ℝ => k z * f z) := by
    have h := (integrable_withDensity_iff_integrable_smul' hk.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp
        (show Integrable f (volume.withDensity (fun z => ENNReal.ofReal (k z))) from
          hrho ▸ hiRho)
    simpa only [ENNReal.toReal_ofReal (hk0 _), smul_eq_mul] using h
  have hphii : Integrable (fun z : ℝ × ℝ => phi z * f z) := by
    have h := (integrable_withDensity_iff_integrable_smul' hphiM.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp
        (show Integrable f (volume.withDensity (fun z => ENNReal.ofReal (phi z))) from
          hPhi ▸ hiPhi)
    simpa only [ENNReal.toReal_ofReal (hphi0 _), smul_eq_mul] using h
  have hintRho : (∫ z : ℝ × ℝ, f z ∂rho) = ∫ z : ℝ × ℝ, k z * f z := by
    rw [hrho, integral_withDensity_eq_integral_toReal_smul hk.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hk0 _), smul_eq_mul]
  have hintPhi : (∫ z : ℝ × ℝ, f z ∂Phi) = ∫ z : ℝ × ℝ, phi z * f z := by
    rw [hPhi, integral_withDensity_eq_integral_toReal_smul hphiM.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hphi0 _), smul_eq_mul]
  let J : ℝ := (2 * Real.pi) * K * Real.exp (R ^ 2)
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hpoint (z : ℝ × ℝ) : k z * f z ≤ J * (phi z * f z) := by
    by_cases hz : R < ‖z‖
    · simp only [hzero z hz, mul_zero]
      exact le_rfl
    · have hzR : ‖z‖ ≤ R := le_of_not_gt hz
      change max |z.1| |z.2| ≤ R at hzR
      have h1 : |z.1| ≤ R := (le_max_left _ _).trans hzR
      have h2 : |z.2| ≤ R := (le_max_right _ _).trans hzR
      have hs1 : z.1 ^ 2 ≤ R ^ 2 := sq_le_sq.mpr (by rwa [abs_of_nonneg hR])
      have hs2 : z.2 ^ 2 ≤ R ^ 2 := sq_le_sq.mpr (by rwa [abs_of_nonneg hR])
      have he : Real.exp (-(R ^ 2)) ≤ Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) :=
        Real.exp_le_exp.2 (by linarith)
      have hp : (1 / (2 * Real.pi)) * Real.exp (-(R ^ 2)) ≤ phi z := by
        rw [hphiEq]
        exact mul_le_mul_of_nonneg_left he (by positivity)
      have hid : J * ((1 / (2 * Real.pi)) * Real.exp (-(R ^ 2))) = K := by
        dsimp only [J]
        rw [Real.exp_neg]
        field_simp [Real.pi_ne_zero, (Real.exp_pos (R ^ 2)).ne'] <;> ring
      have hdom : K ≤ J * phi z := by
        rw [← hid]
        exact mul_le_mul_of_nonneg_left hp hJ
      calc
        _ ≤ K * f z := mul_le_mul_of_nonneg_right (hbound z) (hf0 z)
        _ ≤ (J * phi z) * f z := mul_le_mul_of_nonneg_right hdom (hf0 z)
        _ = _ := by ring
  refine ⟨hiRho, hiPhi, ?_⟩
  rw [hintRho, hintPhi]
  calc
    _ ≤ ∫ z : ℝ × ℝ, J * (phi z * f z) :=
      integral_mono hki (hphii.const_mul J) hpoint
    _ = _ := integral_const_mul _ _

end
end Shao.OQ3
