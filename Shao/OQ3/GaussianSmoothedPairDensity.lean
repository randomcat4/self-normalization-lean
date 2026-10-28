import Shao.OQ3.GaussianSmoothedPairLaw
import Mathlib.MeasureTheory.Group.LIntegral

namespace Shao.OQ3
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

theorem pair_gaussian_noise_withDensity
    (v : ℝ≥0) (hv : v ≠ 0) :
    let gamma : Measure (ℝ × ℝ) :=
      (ProbabilityTheory.gaussianReal 0 v).prod (ProbabilityTheory.gaussianReal 0 v)
    gamma = (volume : Measure (ℝ × ℝ)).withDensity (fun x =>
      ProbabilityTheory.gaussianPDF 0 v x.1 * ProbabilityTheory.gaussianPDF 0 v x.2) ∧
      gamma ≪ volume := by
  intro gamma
  have heq : gamma = (volume : Measure (ℝ × ℝ)).withDensity (fun x =>
      ProbabilityTheory.gaussianPDF 0 v x.1 * ProbabilityTheory.gaussianPDF 0 v x.2) := by
    dsimp only [gamma]
    simp only [ProbabilityTheory.gaussianReal_of_var_ne_zero 0 hv]
    exact prod_withDensity (ProbabilityTheory.measurable_gaussianPDF 0 v)
      (ProbabilityTheory.measurable_gaussianPDF 0 v)
  refine ⟨heq, ?_⟩
  rw [heq]
  exact withDensity_absolutelyContinuous _ _

theorem pair_sum_withDensity_kernel
    (nu : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu]
    (k : (ℝ × ℝ) → ℝ≥0∞) (hk : Measurable k) :
    let gamma : Measure (ℝ × ℝ) := volume.withDensity k
    let rho : Measure (ℝ × ℝ) := (nu.prod gamma).map (fun q => q.1 + q.2)
    let K : (ℝ × ℝ) → ℝ≥0∞ := fun x => ∫⁻ w : ℝ × ℝ, k (x - w) ∂nu
    rho = volume.withDensity K ∧ Measurable K ∧ rho ≪ volume := by
  intro gamma rho K
  have hK : Measurable K := by
    dsimp only [K]
    exact (hk.comp (measurable_fst.sub measurable_snd)).lintegral_prod_right'
  have heq : rho = volume.withDensity K := by
    apply Measure.ext_of_lintegral
    intro f hf
    calc
      (∫⁻ x : ℝ × ℝ, f x ∂rho) =
          ∫⁻ w : ℝ × ℝ, (∫⁻ d : ℝ × ℝ, k d * f (w + d)) ∂nu := by
        dsimp only [rho, gamma]
        rw [lintegral_map hf (by fun_prop), lintegral_prod _ (by fun_prop)]
        apply lintegral_congr
        intro w
        exact lintegral_withDensity_eq_lintegral_mul _ hk (hf.comp (by fun_prop))
      _ = ∫⁻ w : ℝ × ℝ, (∫⁻ x : ℝ × ℝ, k (x - w) * f x) ∂nu := by
        apply lintegral_congr
        intro w
        simpa only [add_sub_cancel_left] using
          (lintegral_add_left_eq_self (μ := (volume : Measure (ℝ × ℝ)))
            (fun x => k (x - w) * f x) w)
      _ = ∫⁻ x : ℝ × ℝ, (∫⁻ w : ℝ × ℝ, k (x - w) * f x ∂nu) :=
        lintegral_lintegral_swap (by fun_prop)
      _ = ∫⁻ x : ℝ × ℝ, K x * f x := by
        apply lintegral_congr
        intro x
        exact lintegral_mul_const (f x) (hk.comp (measurable_const.sub measurable_id))
      _ = ∫⁻ x : ℝ × ℝ, f x ∂volume.withDensity K :=
        (lintegral_withDensity_eq_lintegral_mul _ hK hf).symm
  refine ⟨heq, hK, ?_⟩
  rw [heq]
  exact withDensity_absolutelyContinuous _ _

theorem gaussian_smoothed_pair_law_density
    (nu : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu]
    (v : ℝ≥0) (hv : v ≠ 0) :
    let gamma : Measure (ℝ × ℝ) :=
      (ProbabilityTheory.gaussianReal 0 v).prod (ProbabilityTheory.gaussianReal 0 v)
    let rho : Measure (ℝ × ℝ) := (nu.prod gamma).map (fun q => q.1 + q.2)
    let K : (ℝ × ℝ) → ℝ≥0∞ := fun x =>
      ∫⁻ w : ℝ × ℝ,
        ProbabilityTheory.gaussianPDF 0 v (x.1 - w.1) *
          ProbabilityTheory.gaussianPDF 0 v (x.2 - w.2) ∂nu
    IsProbabilityMeasure rho ∧ rho = volume.withDensity K ∧ Measurable K ∧ rho ≪ volume := by
  intro gamma rho K
  let k : (ℝ × ℝ) → ℝ≥0∞ := fun x =>
    ProbabilityTheory.gaussianPDF 0 v x.1 * ProbabilityTheory.gaussianPDF 0 v x.2
  have hk : Measurable k :=
    ((ProbabilityTheory.measurable_gaussianPDF 0 v).comp measurable_fst).mul
      ((ProbabilityTheory.measurable_gaussianPDF 0 v).comp measurable_snd)
  have hgamma : gamma = (volume : Measure (ℝ × ℝ)).withDensity k :=
    (pair_gaussian_noise_withDensity v hv).1
  letI : IsProbabilityMeasure gamma := (pair_gaussian_noise_characteristic v).1
  refine ⟨(pair_independent_sum_characteristic nu gamma).1, ?_⟩
  have hd := pair_sum_withDensity_kernel nu k hk
  dsimp only at hd
  rw [← hgamma] at hd
  simpa only [k, Prod.fst_sub, Prod.snd_sub] using hd

end
end Shao.OQ3
