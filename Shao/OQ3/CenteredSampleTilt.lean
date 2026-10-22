import Shao.OQ3.CenteredLogMGF
import Shao.OQ3.SampleBoundary
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Integral.Pi

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

def centeredSampleProjection (q a v s : ℝ) (n : ℕ) (z : Shao.Path n) : ℝ :=
  ∑ i : Fin n, centeredNormalProjection q a v s (z i)

private theorem projection_exp_integrable (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a v s : ℝ) :
    Integrable (fun x : ℝ => Real.exp (centeredNormalProjection q a v s x)) mu := by
  apply integrable_continuous_of_fixed_bounds mu hb
  unfold centeredNormalProjection normalValue
  fun_prop

theorem iid_centeredSample_tilt (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a v s : ℝ) (n : ℕ) :
    Integrable (fun z : Shao.Path n => Real.exp (centeredSampleProjection q a v s n z))
      (Measure.pi (fun _ : Fin n => mu)) ∧
      (∫ z : Shao.Path n, Real.exp (centeredSampleProjection q a v s n z)
        ∂Measure.pi (fun _ : Fin n => mu)) =
        (∫ x : ℝ, Real.exp (centeredNormalProjection q a v s x) ∂mu) ^ n ∧
      (Measure.pi (fun _ : Fin n => mu)).tilted (centeredSampleProjection q a v s n) =
        Measure.pi (fun _ : Fin n => mu.tilted (centeredNormalProjection q a v s)) := by
  classical
  have hf := projection_exp_integrable mu hb q a v s
  let Z : ℝ := ∫ x : ℝ, Real.exp (centeredNormalProjection q a v s x) ∂mu
  have hZ : 0 < Z := integral_exp_pos hf
  let : IsProbabilityMeasure (mu.tilted (centeredNormalProjection q a v s)) :=
    isProbabilityMeasure_tilted hf
  have hfun : (fun z : Shao.Path n => Real.exp (centeredSampleProjection q a v s n z)) =
      (fun z => ∏ i : Fin n, Real.exp (centeredNormalProjection q a v s (z i))) := by
    funext z
    exact Real.exp_sum _ _
  have hF : Integrable (fun z : Shao.Path n => Real.exp (centeredSampleProjection q a v s n z))
      (Measure.pi (fun _ : Fin n => mu)) := by
    rw [hfun]
    exact Integrable.fintype_prod (fun _ : Fin n => hf)
  have hnorm : (∫ z : Shao.Path n, Real.exp (centeredSampleProjection q a v s n z)
      ∂Measure.pi (fun _ : Fin n => mu)) = Z ^ n := by
    rw [hfun]
    simpa only [Fintype.card_fin] using (integral_fintype_prod_eq_pow (ι := Fin n)
      (μ := mu) (fun x => Real.exp (centeredNormalProjection q a v s x)))
  have _hZn : 0 < Z ^ n := pow_pos hZ n
  let : IsProbabilityMeasure ((Measure.pi (fun _ : Fin n => mu)).tilted
      (centeredSampleProjection q a v s n)) := isProbabilityMeasure_tilted hF
  refine ⟨hF, hnorm, ?_⟩
  have hdensity : (fun z : Shao.Path n => Real.exp (centeredSampleProjection q a v s n z) / Z ^ n) =
      (fun z => ∏ i : Fin n, Real.exp (centeredNormalProjection q a v s (z i)) / Z) := by
    funext z
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_sum]
    rfl
  symm
  apply Measure.pi_eq
  intro A hA
  rw [tilted_apply' _ _ (MeasurableSet.univ_pi hA), hnorm]
  change (∫⁻ z in Set.univ.pi A, ENNReal.ofReal
    (Real.exp (centeredSampleProjection q a v s n z) / Z ^ n)
    ∂Measure.pi (fun _ : Fin n => mu)) = _
  simp_rw [congrFun hdensity]
  rw [Measure.restrict_pi_pi]
  have hcoord (i : Fin n) : Integrable
      (fun x => Real.exp (centeredNormalProjection q a v s x) / Z) (mu.restrict (A i)) :=
    hf.integrableOn.div_const Z
  have hprod := Integrable.fintype_prod hcoord
  rw [← ofReal_integral_eq_lintegral_ofReal hprod
    (Filter.Eventually.of_forall (fun z => Finset.prod_nonneg
      (fun i _ => div_nonneg (Real.exp_pos _).le hZ.le)))]
  rw [integral_fintype_prod_eq_prod (fun _ : Fin n =>
    fun x : ℝ => Real.exp (centeredNormalProjection q a v s x) / Z)]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg
    (fun x => div_nonneg (Real.exp_pos _).le hZ.le))]
  apply Finset.prod_congr rfl
  intro i _
  rw [tilted_apply_eq_ofReal_integral' _ (hA i)]

theorem centeredProjection_tilt_eq_quadratic (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a v s : ℝ) :
    mu.tilted (centeredNormalProjection q a v s) =
      mu.tilted (fun x : ℝ => (8 * v + s) * x + (-v) * x ^ 2) := by
  let g : ℝ → ℝ := fun x => (8 * v + s) * x + (-v) * x ^ 2
  have hg : Integrable (fun x : ℝ => Real.exp (g x)) mu := by
    apply integrable_continuous_of_fixed_bounds mu hb
    dsimp only [g]
    fun_prop
  let : IsProbabilityMeasure (mu.tilted g) := isProbabilityMeasure_tilted hg
  have hfun : centeredNormalProjection q a v s = g + (fun _ : ℝ => -(v * q + s * a)) := by
    funext x
    dsimp only [g, Pi.add_apply, centeredNormalProjection, normalValue]
    ring
  rw [hfun, ← tilted_tilted hg, tilted_const]

theorem iid_centeredSample_event_bound (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a v s : ℝ) (n : ℕ)
    (E : Set (Shao.Path n)) (hE : MeasurableSet E) (c : ℝ)
    (hlower : ∀ z ∈ E, c ≤ centeredSampleProjection q a v s n z) :
    (Measure.pi (fun _ : Fin n => mu)).real E ≤
      Real.exp ((n : ℝ) * centeredNormalLogMGF mu q a v s - c) *
        (Measure.pi (fun _ : Fin n =>
          mu.tilted (centeredNormalProjection q a v s))).real E := by
  have hf := projection_exp_integrable mu hb q a v s
  let Z : ℝ := ∫ x : ℝ, Real.exp (centeredNormalProjection q a v s x) ∂mu
  have hZ : 0 < Z := integral_exp_pos hf
  have hZn : 0 < Z ^ n := pow_pos hZ n
  let : IsProbabilityMeasure (mu.tilted (centeredNormalProjection q a v s)) :=
    isProbabilityMeasure_tilted hf
  have hnorm := iid_centeredSample_tilt mu hb q a v s n
  have hsampleZ : 0 < (∫ z : Shao.Path n, Real.exp (centeredSampleProjection q a v s n z)
      ∂Measure.pi (fun _ : Fin n => mu)) := by
    rw [hnorm.2.1]
    exact hZn
  let : IsProbabilityMeasure ((Measure.pi (fun _ : Fin n => mu)).tilted
      (centeredSampleProjection q a v s n)) := isProbabilityMeasure_tilted hnorm.1
  have hdensity : IntegrableOn (fun z : Shao.Path n =>
      Real.exp (centeredSampleProjection q a v s n z) / Z ^ n) E
      (Measure.pi (fun _ : Fin n => mu)) := hnorm.1.integrableOn.div_const _
  have hprob : (Measure.pi (fun _ : Fin n =>
      mu.tilted (centeredNormalProjection q a v s))).real E =
      ∫ z : Shao.Path n in E, Real.exp (centeredSampleProjection q a v s n z) / Z ^ n
        ∂Measure.pi (fun _ : Fin n => mu) := by
    rw [measureReal_def, ← hnorm.2.2, tilted_apply_eq_ofReal_integral' _ hE, hnorm.2.1]
    exact ENNReal.toReal_ofReal (integral_nonneg
      (fun z => div_nonneg (Real.exp_pos _).le hZn.le))
  have hminor : (Real.exp c / Z ^ n) * (Measure.pi (fun _ : Fin n => mu)).real E ≤
      (Measure.pi (fun _ : Fin n => mu.tilted (centeredNormalProjection q a v s))).real E := by
    rw [hprob]
    calc
      _ = ∫ _ : Shao.Path n in E, (Real.exp c / Z ^ n)
          ∂Measure.pi (fun _ : Fin n => mu) := by simp [smul_eq_mul, mul_comm, measureReal_def]
      _ ≤ _ := by
        apply integral_mono_ae (integrable_const _) hdensity
        filter_upwards [ae_restrict_mem hE] with z hz
        exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (hlower z hz)) hZn.le
  have hfactor : Real.exp ((n : ℝ) * centeredNormalLogMGF mu q a v s - c) *
      (Real.exp c / Z ^ n) = 1 := by
    change Real.exp ((n : ℝ) * Real.log Z - c) * (Real.exp c / Z ^ n) = 1
    rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hZ]
    field_simp
  calc
    _ = Real.exp ((n : ℝ) * centeredNormalLogMGF mu q a v s - c) *
        ((Real.exp c / Z ^ n) * (Measure.pi (fun _ : Fin n => mu)).real E) := by
      rw [← mul_assoc, hfactor, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hminor (Real.exp_pos _).le


end
end Shao.OQ3
