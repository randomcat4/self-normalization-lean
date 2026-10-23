import Shao.OQ3.BoundaryLaplaceCutoff
import Shao.OQ3.BoundaryLaplaceEnvelope
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem boundary_laplace_leading_integral
    (lambda Lambda1 a0 : ℝ) (hlambda : 0 < lambda) (hLambda1 : 0 < Lambda1) :
    let mu : Measure (ℝ × ℝ) :=
      (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0))
    let L : (ℝ × ℝ) → ℝ := fun p =>
      a0 * Real.exp (-(lambda * p.2 + Lambda1 / 2 * p.1 ^ 2))
    Integrable L mu ∧ (∫ p : ℝ × ℝ, L p ∂mu) =
      a0 * (Real.sqrt (2 * Real.pi / Lambda1) / lambda)
 := by
  let mu : Measure (ℝ × ℝ) :=
    (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0))
  let L : (ℝ × ℝ) → ℝ := fun p =>
    a0 * Real.exp (-(lambda * p.2 + Lambda1 / 2 * p.1 ^ 2))
  have hU : Integrable (fun u : ℝ => Real.exp (-(Lambda1 / 2) * u ^ 2)) :=
    integrable_exp_neg_mul_sq (by linarith : 0 < Lambda1 / 2)
  have hV : IntegrableOn (fun v : ℝ => Real.exp (-lambda * v)) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (f := fun v : ℝ => Real.exp (-lambda * v))
      (μ := volume) (b := 0) (by finiteness)).mpr
        (integrableOn_exp_mul_Ioi (neg_neg_of_pos hlambda) 0)
  have hVI : (∫ v : ℝ in Set.Ici 0, Real.exp (-lambda * v)) = 1 / lambda := by
    rw [integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi (neg_neg_of_pos hlambda)]
    simp
  have heq : L = fun p : ℝ × ℝ =>
      a0 * (Real.exp (-(Lambda1 / 2) * p.1 ^ 2) * Real.exp (-lambda * p.2)) := by
    funext p
    dsimp only [L]
    rw [← Real.exp_add]
    congr 2
    ring
  have harg : Real.pi / (Lambda1 / 2) = 2 * Real.pi / Lambda1 := by
    field_simp
  refine ⟨?_, ?_⟩
  · change Integrable L mu
    rw [heq]
    exact (hU.mul_prod hV).const_mul a0
  · change (∫ p : ℝ × ℝ, L p ∂mu) = _
    rw [heq, integral_const_mul]
    dsimp only [mu]
    rw [integral_prod_mul (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ).restrict (Set.Ici 0))
      (fun u : ℝ => Real.exp (-(Lambda1 / 2) * u ^ 2))
      (fun v : ℝ => Real.exp (-lambda * v)), integral_gaussian, hVI, harg]
    ring

theorem boundary_laplace_cutoff_integral_error
    (F A : (ℝ × ℝ) → ℝ) (lambda Lambda1 rho CF CA c d : ℝ)
    (hCF : 0 ≤ CF) (hCA : 0 ≤ CA) (hrho : 0 < rho) (hd : 0 < d)
    (hdc : d ≤ c) (hdl : d ≤ lambda) (hdq : d ≤ Lambda1 / 2)
    (hbound : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |F (r, z) - F (0, 0) - lambda * z - Lambda1 / 2 * r ^ 2| ≤
        CF * (|r| ^ 3 + |r| * z + z ^ 2))
    (hmargin : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      c * (z + r ^ 2) ≤ F (r, z) - F (0, 0))
    (hamplitude : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |A (r, z) - A (0, 0)| ≤ CA * (|r| + z))
    (hmeas : ∀ t : ℝ, 0 < t → t ≤ 1 →
      AEStronglyMeasurable (fun p : ℝ × ℝ =>
        if |t * p.1| ≤ rho ∧ t ^ 2 * p.2 ≤ rho then
          A (t * p.1, t ^ 2 * p.2) *
            Real.exp (-((F (t * p.1, t ^ 2 * p.2) - F (0, 0)) / t ^ 2)) else 0)
        ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0)))) :
    let mu : Measure (ℝ × ℝ) :=
      (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0))
    let K : ℝ → (ℝ × ℝ) → ℝ := fun t p =>
      if |t * p.1| ≤ rho ∧ t ^ 2 * p.2 ≤ rho then
        A (t * p.1, t ^ 2 * p.2) *
          Real.exp (-((F (t * p.1, t ^ 2 * p.2) - F (0, 0)) / t ^ 2)) else 0
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      Integrable (K t) mu ∧
        |(∫ p : ℝ × ℝ, K t p ∂mu) -
          A (0, 0) * (Real.sqrt (2 * Real.pi / Lambda1) / lambda)| ≤ C * t
 := by
  let mu : Measure (ℝ × ℝ) :=
    (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0))
  let K : ℝ → (ℝ × ℝ) → ℝ := fun t p =>
    if |t * p.1| ≤ rho ∧ t ^ 2 * p.2 ≤ rho then
      A (t * p.1, t ^ 2 * p.2) *
        Real.exp (-((F (t * p.1, t ^ 2 * p.2) - F (0, 0)) / t ^ 2)) else 0
  let L : (ℝ × ℝ) → ℝ := fun p =>
    A (0, 0) * Real.exp (-(lambda * p.2 + Lambda1 / 2 * p.1 ^ 2))
  let Env : (ℝ × ℝ) → ℝ := fun p =>
    (CA * (|p.1| + p.2) + |A (0, 0)| * CF * (|p.1| ^ 3 + |p.1| * p.2 + p.2 ^ 2) +
      |A (0, 0)| / rho * (|p.1| + p.2)) * Real.exp (-d * (p.2 + p.1 ^ 2))
  have hEnv : Integrable Env mu :=
    boundary_laplace_error_envelope_integrable d CA CF (A (0, 0)) rho hd
  have hlambda : 0 < lambda := hd.trans_le hdl
  have hLambda1 : 0 < Lambda1 := by linarith [hd.trans_le hdq]
  obtain ⟨hL, hLI⟩ := boundary_laplace_leading_integral lambda Lambda1 (A (0, 0)) hlambda hLambda1
  have hL' : Integrable L mu := hL
  have hLI' : (∫ p : ℝ × ℝ, L p ∂mu) =
      A (0, 0) * (Real.sqrt (2 * Real.pi / Lambda1) / lambda) := hLI
  have hvAE : ∀ᵐ p : ℝ × ℝ ∂mu, 0 ≤ p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le measurable_const measurable_snd)).mpr
    exact Filter.Eventually.of_forall fun _ => ae_restrict_mem measurableSet_Ici
  let C : ℝ := |∫ p : ℝ × ℝ, Env p ∂mu| + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro t ht ht1
  have hdom : ∀ᵐ p : ℝ × ℝ ∂mu, ‖K t p - L p‖ ≤ t * Env p := by
    filter_upwards [hvAE] with p hp
    rw [Real.norm_eq_abs]
    have hh := boundary_weighted_scaled_cutoff_error F A lambda Lambda1 rho CF CA c d
      hCF hCA hrho hd hdc hdl hdq hbound hmargin hamplitude t p.1 p.2 ht ht1 hp
    simpa only [K, L, Env, mul_assoc] using hh
  have hDiff : Integrable (fun p => K t p - L p) mu :=
    (hEnv.const_mul t).mono' ((hmeas t ht ht1).sub hL'.aestronglyMeasurable) hdom
  have hK : Integrable (K t) mu := by
    convert hDiff.add hL' using 1
    funext p
    change K t p = (K t p - L p) + L p
    ring
  have herror := norm_integral_le_of_norm_le (hEnv.const_mul t) hdom
  rw [integral_sub hK hL', hLI', Real.norm_eq_abs, integral_const_mul] at herror
  refine ⟨hK, ?_⟩
  calc
    _ ≤ t * (∫ p : ℝ × ℝ, Env p ∂mu) := herror
    _ ≤ t * C := mul_le_mul_of_nonneg_left (by dsimp [C]; linarith [le_abs_self (∫ p : ℝ × ℝ, Env p ∂mu)]) ht.le
    _ = C * t := mul_comm _ _

end
end Shao.OQ3
