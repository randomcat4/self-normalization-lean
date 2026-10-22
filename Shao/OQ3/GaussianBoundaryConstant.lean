import Shao.OQ3.CorrectedScaleContinuity
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The actual continuous Gaussian curved-boundary constant

Source: current/oq3/proofs/r1/report.md, lines 411-444, equation (20).
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U10a scope: e294a49d155254fb3f375e6f04251fdaa51e03143c0fde0c4471c66212c56ba2.
-/

namespace Shao.OQ3

open MeasureTheory

noncomputable section

def gaussianBoundaryWeight (kappa d : ℝ) : ℝ :=
  ∫ z : ℝ in {z : ℝ | -((z / kappa) ^ 2) ≤ d},
    Real.exp (-(z ^ 2) / 2) / Real.sqrt (2 * Real.pi)

def gaussianBoundaryProfile (ell kappa d : ℝ) : ℝ :=
  Real.exp (-ell * d) * gaussianBoundaryWeight kappa d

def boundaryKappa (q : ℝ) (mu : Measure ℝ) : ℝ :=
  Real.sqrt q / (4 * Real.sqrt (transverseVariance mu))

private def stdGaussian (z : ℝ) : ℝ :=
  Real.exp (-(z ^ 2) / 2) / Real.sqrt (2 * Real.pi)

private theorem stdGaussian_integrable : Integrable stdGaussian := by
  have heq : (fun z : ℝ => Real.exp (-(z ^ 2) / 2)) =
      (fun z : ℝ => Real.exp (-(1 / 2 : ℝ) * z ^ 2)) := by
    funext z
    congr 1
    ring
  exact (heq ▸ integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).div_const _

private theorem integral_stdGaussian : (∫ z : ℝ, stdGaussian z) = 1 := by
  have heq : (fun z : ℝ => Real.exp (-(z ^ 2) / 2)) =
      (fun z : ℝ => Real.exp (-(1 / 2 : ℝ) * z ^ 2)) := by
    funext z
    congr 1
    ring
  unfold stdGaussian
  rw [integral_div, heq, integral_gaussian]
  have harg : Real.pi / (1 / 2 : ℝ) = 2 * Real.pi := by ring
  rw [harg, div_self (Real.sqrt_ne_zero'.mpr (by positivity))]

theorem gaussianBoundaryWeight_eq_piecewise (kappa : ℝ) (hk : 0 < kappa) (d : ℝ) :
    gaussianBoundaryWeight kappa d =
      if 0 ≤ d then 1 else
        (2 / Real.sqrt (2 * Real.pi)) *
          ∫ z : ℝ in Set.Ioi (kappa * Real.sqrt (-d)), Real.exp (-(z ^ 2) / 2) := by
  classical
  by_cases hd : 0 ≤ d
  · have hset : {z : ℝ | -((z / kappa) ^ 2) ≤ d} = Set.univ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact (neg_nonpos.mpr (sq_nonneg _)).trans hd
    simpa only [gaussianBoundaryWeight, hset, Measure.restrict_univ, ite_eq_left hd,
      stdGaussian] using
      integral_stdGaussian
  · have hdn : d < 0 := lt_of_not_ge hd
    let a := kappa * Real.sqrt (-d)
    have ha : 0 < a := mul_pos hk (Real.sqrt_pos.mpr (by linarith))
    have ha2 : a ^ 2 = kappa ^ 2 * (-d) := by
      dsimp [a]
      rw [mul_pow, Real.sq_sqrt (by linarith)]
    have hset : {z : ℝ | -((z / kappa) ^ 2) ≤ d} =
        Set.Iic (-a) ∪ Set.Ici a := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici]
      have heq : -((z / kappa) ^ 2) ≤ d ↔ a ^ 2 ≤ z ^ 2 := by
        rw [neg_le, div_pow, le_div_iff₀ (sq_pos_of_pos hk)]
        rw [ha2]
        constructor <;> intro h <;> nlinarith
      rw [heq]
      constructor
      · intro h
        by_cases hz : 0 ≤ z
        · right; nlinarith
        · left; nlinarith
      · intro h
        rcases h with h | h <;> nlinarith
    have hdis : Disjoint (Set.Iic (-a)) (Set.Ici a) := by
      refine Set.disjoint_left.mpr ?_
      intro z hz hz'
      simp only [Set.mem_Iic, Set.mem_Ici] at hz hz'
      linarith
    have hreflect : (∫ z : ℝ in Set.Iic (-a), stdGaussian z) =
        ∫ z : ℝ in Set.Ioi a, stdGaussian z := by
      rw [← integral_comp_neg_Ioi a stdGaussian]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro z _
      simp [stdGaussian]
    change (∫ z : ℝ in {z : ℝ | -((z / kappa) ^ 2) ≤ d}, stdGaussian z) = _
    rw [ite_eq_right hd, hset, setIntegral_union hdis measurableSet_Ici
      stdGaussian_integrable.integrableOn stdGaussian_integrable.integrableOn,
      hreflect, integral_Ici_eq_integral_Ioi]
    unfold stdGaussian
    rw [integral_div]
    dsimp [a]
    ring

private def gaussianBoundaryKernel (ell kappa : ℝ) (v : ℝ × ℝ) : ℝ :=
  {v : ℝ × ℝ | -((v.1 / kappa) ^ 2) ≤ v.2}.indicator
    (fun v => Real.exp (-ell * v.2) * stdGaussian v.1) v

private theorem gaussianBoundaryKernel_nonneg (ell kappa z d : ℝ) :
    0 ≤ gaussianBoundaryKernel ell kappa (z, d) := by
  classical
  simp only [gaussianBoundaryKernel, Set.indicator, Set.mem_ofPred_eq]
  split_ifs
  · unfold stdGaussian
    positivity
  · exact le_rfl

private theorem gaussianBoundaryKernel_slice (ell kappa : ℝ) (hell : 0 < ell) (z : ℝ) :
    Integrable (fun d : ℝ => gaussianBoundaryKernel ell kappa (z, d)) := by
  have hI : IntegrableOn (fun d : ℝ => Real.exp (-ell * d))
      (Set.Ici (-((z / kappa) ^ 2))) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (f := fun d : ℝ => Real.exp (-ell * d))
      (μ := volume) (b := -((z / kappa) ^ 2)) (by finiteness)).mpr
      (integrableOn_exp_mul_Ioi (neg_neg_of_pos hell) _)
  have heq : (fun d : ℝ => gaussianBoundaryKernel ell kappa (z, d)) =
      (Set.Ici (-((z / kappa) ^ 2))).indicator
        (fun d : ℝ => Real.exp (-ell * d) * stdGaussian z) := by
    funext d
    simp [gaussianBoundaryKernel, Set.indicator]
  rw [heq]
  exact IntegrableOn.integrable_indicator (hI.mul_const _) measurableSet_Ici

private theorem integral_gaussianBoundaryKernel_slice (ell kappa : ℝ)
    (hell : 0 < ell) (hk : 0 < kappa) (z : ℝ) :
    (∫ d : ℝ, gaussianBoundaryKernel ell kappa (z, d)) =
      (1 / (ell * Real.sqrt (2 * Real.pi))) *
        Real.exp (-(1 / 2 - ell / kappa ^ 2) * z ^ 2) := by
  have heq : (fun d : ℝ => gaussianBoundaryKernel ell kappa (z, d)) =
      (Set.Ici (-((z / kappa) ^ 2))).indicator
        (fun d : ℝ => Real.exp (-ell * d) * stdGaussian z) := by
    funext d
    simp [gaussianBoundaryKernel, Set.indicator]
  rw [heq, integral_indicator measurableSet_Ici, integral_mul_const,
    integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi (neg_neg_of_pos hell)]
  have hexp : Real.exp (-ell * -((z / kappa) ^ 2)) * Real.exp (-(z ^ 2) / 2) =
      Real.exp (-(1 / 2 - ell / kappa ^ 2) * z ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    field_simp [hk.ne']; ring
  calc
    -Real.exp (-ell * -((z / kappa) ^ 2)) / -ell * stdGaussian z =
        (Real.exp (-ell * -((z / kappa) ^ 2)) * Real.exp (-(z ^ 2) / 2)) /
          (ell * Real.sqrt (2 * Real.pi)) := by
            unfold stdGaussian
            simp only [div_eq_mul_inv, mul_inv_rev, inv_neg, neg_mul]
            ring
    _ = _ := by rw [hexp]; ring

private theorem gaussianBoundaryKernel_integrable (ell kappa : ℝ)
    (hell : 0 < ell) (hk : 0 < kappa) (hgap : 2 * ell < kappa ^ 2) :
    Integrable (gaussianBoundaryKernel ell kappa) (volume.prod volume) := by
  have hb : 0 < 1 / 2 - ell / kappa ^ 2 := by
    have hdiv : ell / kappa ^ 2 < 1 / 2 :=
      (div_lt_iff₀ (sq_pos_of_pos hk)).mpr (by nlinarith)
    linarith
  have hset : MeasurableSet {v : ℝ × ℝ | -((v.1 / kappa) ^ 2) ≤ v.2} :=
    (isClosed_le (((continuous_fst.div_const kappa).pow 2).neg) continuous_snd).measurableSet
  have hbody : Continuous (fun v : ℝ × ℝ => Real.exp (-ell * v.2) * stdGaussian v.1) := by
    unfold stdGaussian
    fun_prop
  have hmeas : AEStronglyMeasurable (gaussianBoundaryKernel ell kappa) (volume.prod volume) :=
    (hbody.measurable.indicator hset).aestronglyMeasurable
  apply (integrable_prod_iff hmeas).mpr
  refine ⟨Filter.Eventually.of_forall (gaussianBoundaryKernel_slice ell kappa hell), ?_⟩
  have heq : (fun z : ℝ => ∫ d : ℝ, ‖gaussianBoundaryKernel ell kappa (z, d)‖) =
      (fun z : ℝ => (1 / (ell * Real.sqrt (2 * Real.pi))) *
        Real.exp (-(1 / 2 - ell / kappa ^ 2) * z ^ 2)) := by
    funext z
    simp_rw [Real.norm_of_nonneg (gaussianBoundaryKernel_nonneg ell kappa z _)]
    exact integral_gaussianBoundaryKernel_slice ell kappa hell hk z
  rw [heq]
  exact (integrable_exp_neg_mul_sq hb).const_mul _

private theorem gaussianBoundaryKernel_profile (ell kappa d : ℝ) :
    (∫ z : ℝ, gaussianBoundaryKernel ell kappa (z, d)) =
      gaussianBoundaryProfile ell kappa d := by
  classical
  have hset : MeasurableSet {z : ℝ | -((z / kappa) ^ 2) ≤ d} :=
    (isClosed_le (((continuous_id.div_const kappa).pow 2).neg) continuous_const).measurableSet
  rw [gaussianBoundaryProfile, gaussianBoundaryWeight, ← integral_indicator hset,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [gaussianBoundaryKernel, Set.indicator, Set.mem_ofPred_eq]
  split_ifs <;> simp [stdGaussian]

theorem gaussianBoundaryProfile_integrable (ell kappa : ℝ)
    (hell : 0 < ell) (hk : 0 < kappa) (hgap : 2 * ell < kappa ^ 2) :
    Integrable (gaussianBoundaryProfile ell kappa) := by
  exact (gaussianBoundaryKernel_integrable ell kappa hell hk hgap).integral_prod_right.congr
    (Filter.Eventually.of_forall (gaussianBoundaryKernel_profile ell kappa))

theorem integral_gaussianBoundaryProfile (ell kappa : ℝ)
    (hell : 0 < ell) (hk : 0 < kappa) (hgap : 2 * ell < kappa ^ 2) :
    (∫ d : ℝ, gaussianBoundaryProfile ell kappa d) =
      kappa / (ell * Real.sqrt (kappa ^ 2 - 2 * ell)) := by
  have hprod := gaussianBoundaryKernel_integrable ell kappa hell hk hgap
  have heq : gaussianBoundaryProfile ell kappa =
      (fun d : ℝ => ∫ z : ℝ, gaussianBoundaryKernel ell kappa (z, d)) :=
    funext (fun d => (gaussianBoundaryKernel_profile ell kappa d).symm)
  rw [heq, ← integral_integral_swap
    (f := fun z d : ℝ => gaussianBoundaryKernel ell kappa (z, d)) hprod]
  simp_rw [integral_gaussianBoundaryKernel_slice ell kappa hell hk]
  rw [integral_const_mul, integral_gaussian]
  have hb : 0 < 1 / 2 - ell / kappa ^ 2 := by
    have hdiv : ell / kappa ^ 2 < 1 / 2 :=
      (div_lt_iff₀ (sq_pos_of_pos hk)).mpr (by nlinarith)
    linarith
  have hg : 0 < kappa ^ 2 - 2 * ell := by linarith
  have hroot : Real.sqrt (Real.pi / (1 / 2 - ell / kappa ^ 2)) =
      Real.sqrt (2 * Real.pi) * kappa / Real.sqrt (kappa ^ 2 - 2 * ell) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
      Real.sq_sqrt hg.le]
    field_simp [hk.ne', hb.ne', hg.ne']
  rw [hroot]
  field_simp [hell.ne', (Real.sqrt_pos.mpr (by positivity : 0 < 2 * Real.pi)).ne',
    (Real.sqrt_pos.mpr hg).ne']

theorem boundaryKappa_sq (q : ℝ) (mu : Measure ℝ) (hq : 0 < q)
    (hS : 0 < normalVariance mu) (hD : 0 < (parabolaCovariance mu).det) :
    boundaryKappa q mu ^ 2 = q * normalVariance mu / (16 * (parabolaCovariance mu).det) := by
  have ht : 0 < transverseVariance mu := div_pos hD hS
  unfold boundaryKappa
  rw [div_pow, mul_pow, Real.sq_sqrt hq.le, Real.sq_sqrt ht.le, transverseVariance]
  field_simp; ring

theorem gaussianBoundary_constant_eq_corrected (ell q : ℝ) (mu : Measure ℝ)
    (hell : 0 < ell) (hq : 0 < q) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det)
    (hR : 0 < normalVariance mu - (32 * ell / q) * (parabolaCovariance mu).det) :
    (1 / Real.sqrt (normalVariance mu)) *
        (∫ d : ℝ, gaussianBoundaryProfile ell (boundaryKappa q mu) d) =
      correctedInverseScale ell q mu := by
  let S := normalVariance mu
  let D := (parabolaCovariance mu).det
  let R := S - (32 * ell / q) * D
  let k := boundaryKappa q mu
  have hk : 0 < k := by
    dsimp [k, boundaryKappa, transverseVariance]
    positivity
  have hk2 : k ^ 2 = q * S / (16 * D) := boundaryKappa_sq q mu hq hS hD
  have hDn : D ≠ 0 := hD.ne'
  have hgap_eq : k ^ 2 - 2 * ell = q * R / (16 * D) := by
    rw [hk2]
    dsimp [R]
    field_simp [hq.ne', hDn]; ring
  have hg : 0 < k ^ 2 - 2 * ell := by rw [hgap_eq]; exact div_pos (mul_pos hq hR) (by positivity)
  rw [integral_gaussianBoundaryProfile ell _ hell hk (by linarith)]
  have hid : S * (k ^ 2 - 2 * ell) = k ^ 2 * R := by
    rw [hgap_eq, hk2]
    ring
  have hroot : Real.sqrt S * Real.sqrt (k ^ 2 - 2 * ell) = k * Real.sqrt R := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt hS.le, Real.sq_sqrt hg.le, Real.sq_sqrt hR.le]
    exact hid
  change (1 / Real.sqrt S) * (k / (ell * Real.sqrt (k ^ 2 - 2 * ell))) =
    (ell * Real.sqrt R)⁻¹
  calc
    (1 / Real.sqrt S) * (k / (ell * Real.sqrt (k ^ 2 - 2 * ell))) =
        k / (ell * (Real.sqrt S * Real.sqrt (k ^ 2 - 2 * ell))) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = k / (k * (ell * Real.sqrt R)) := by rw [hroot]; ring
    _ = (ell * Real.sqrt R)⁻¹ := by
      field_simp [hk.ne', hell.ne', (Real.sqrt_pos.mpr hR).ne']

end
end Shao.OQ3
