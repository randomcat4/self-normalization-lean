import Shao.Basic.FinitePath
import Shao.Probability.BivariateLegendre
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Integral.Pi

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem iid_quadratic_sample_tilt
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
    (n : ℕ) :
    let f : ℝ → ℝ := fun x => theta.1 * x + theta.2 * x ^ 2
    let S : Shao.Path n → ℝ := fun z => ∑ i : Fin n, f (z i)
    let Z : ℝ := ∫ x : ℝ, Real.exp (f x) ∂mu
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
    Integrable (fun z => Real.exp (S z)) P ∧
      (∫ z : Shao.Path n, Real.exp (S z) ∂P) = Z ^ n ∧
      P.tilted S = Measure.pi (fun _ : Fin n => mu.tilted f) := by
  classical
  let f : ℝ → ℝ := fun x => theta.1 * x + theta.2 * x ^ 2
  let S : Shao.Path n → ℝ := fun z => ∑ i : Fin n, f (z i)
  have hf : Integrable (fun x : ℝ => Real.exp (f x)) mu := htheta
  let Z : ℝ := ∫ x : ℝ, Real.exp (f x) ∂mu
  have hZ : 0 < Z := integral_exp_pos hf
  let : IsProbabilityMeasure (mu.tilted (f)) :=
    isProbabilityMeasure_tilted hf
  have hfun : (fun z : Shao.Path n => Real.exp (S z)) =
      (fun z => ∏ i : Fin n, Real.exp (f (z i))) := by
    funext z
    exact Real.exp_sum _ _
  have hF : Integrable (fun z : Shao.Path n => Real.exp (S z))
      (Measure.pi (fun _ : Fin n => mu)) := by
    rw [hfun]
    exact Integrable.fintype_prod (fun _ : Fin n => hf)
  have hnorm : (∫ z : Shao.Path n, Real.exp (S z)
      ∂Measure.pi (fun _ : Fin n => mu)) = Z ^ n := by
    rw [hfun]
    simpa only [Fintype.card_fin] using (integral_fintype_prod_eq_pow (ι := Fin n)
      (μ := mu) (fun x => Real.exp (f x)))
  have _hZn : 0 < Z ^ n := pow_pos hZ n
  let : IsProbabilityMeasure ((Measure.pi (fun _ : Fin n => mu)).tilted
      (S)) := isProbabilityMeasure_tilted hF
  refine ⟨hF, hnorm, ?_⟩
  have hdensity : (fun z : Shao.Path n => Real.exp (S z) / Z ^ n) =
      (fun z => ∏ i : Fin n, Real.exp (f (z i)) / Z) := by
    funext z
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_sum]
  symm
  apply Measure.pi_eq
  intro A hA
  rw [tilted_apply' _ _ (MeasurableSet.univ_pi hA), hnorm]
  change (∫⁻ z in Set.univ.pi A, ENNReal.ofReal
    (Real.exp (S z) / Z ^ n)
    ∂Measure.pi (fun _ : Fin n => mu)) = _
  simp_rw [congrFun hdensity]
  rw [Measure.restrict_pi_pi]
  have hcoord (i : Fin n) : Integrable
      (fun x => Real.exp (f x) / Z) (mu.restrict (A i)) :=
    hf.integrableOn.div_const Z
  have hprod := Integrable.fintype_prod hcoord
  rw [← ofReal_integral_eq_lintegral_ofReal hprod
    (Filter.Eventually.of_forall (fun z => Finset.prod_nonneg
      (fun i _ => div_nonneg (Real.exp_pos _).le hZ.le)))]
  rw [integral_fintype_prod_eq_prod (fun _ : Fin n =>
    fun x : ℝ => Real.exp (f x) / Z)]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg
    (fun x => div_nonneg (Real.exp_pos _).le hZ.le))]
  apply Finset.prod_congr rfl
  intro i _
  rw [tilted_apply_eq_ofReal_integral' _ (hA i)]

theorem iid_quadratic_cell_change_of_measure
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
    (n : ℕ) (y : ℝ × ℝ) (A : Set (ℝ × ℝ)) (hA : MeasurableSet A) :
    let f : ℝ → ℝ := fun x => theta.1 * x + theta.2 * x ^ 2
    let K : ℝ := Real.log (∫ x : ℝ, Real.exp (f x) ∂mu)
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
    let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu.tilted f)
    let M : Shao.Path n → (ℝ × ℝ) := fun z =>
      ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
    let E : Set (Shao.Path n) := M ⁻¹' A
    let G : Shao.Path n → ℝ := fun z => Real.exp (-(theta.1 *
      ((∑ i : Fin n, z i) - (n : ℝ) * y.1) +
      theta.2 * (Shao.energy z - (n : ℝ) * y.2)))
    Integrable G Q ∧
      P.real E = Real.exp (-(n : ℝ) * (theta.1 * y.1 + theta.2 * y.2 - K)) *
        ∫ z : Shao.Path n in E, G z ∂Q := by
  classical
  let f : ℝ → ℝ := fun x => theta.1 * x + theta.2 * x ^ 2
  let S : Shao.Path n → ℝ := fun z => ∑ i : Fin n, f (z i)
  let Z : ℝ := ∫ x : ℝ, Real.exp (f x) ∂mu
  let K : ℝ := Real.log Z
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
  let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu.tilted f)
  let M : Shao.Path n → (ℝ × ℝ) := fun z =>
    ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
  let E : Set (Shao.Path n) := M ⁻¹' A
  let G : Shao.Path n → ℝ := fun z => Real.exp (-(theta.1 *
    ((∑ i : Fin n, z i) - (n : ℝ) * y.1) +
    theta.2 * (Shao.energy z - (n : ℝ) * y.2)))
  have hf : Integrable (fun x : ℝ => Real.exp (f x)) mu := htheta
  have hZ : 0 < Z := integral_exp_pos hf
  have hZn : 0 < Z ^ n := pow_pos hZ n
  let : IsProbabilityMeasure (mu.tilted f) := isProbabilityMeasure_tilted hf
  have hM : Continuous M := by dsimp [M, Shao.energy]; fun_prop
  have hE : MeasurableSet E := hM.measurable hA
  obtain ⟨hS, hnorm, htilt⟩ := iid_quadratic_sample_tilt mu theta htheta n
  have hnorm0 : (∫ z : Shao.Path n, Real.exp (S z) ∂P) = Z ^ n := hnorm
  have htilt0 : P.tilted S = Q := htilt
  let c : ℝ := Real.exp ((n : ℝ) * (theta.1 * y.1 + theta.2 * y.2)) / Z ^ n
  have hSfun (z : Shao.Path n) : S z =
      theta.1 * (∑ i : Fin n, z i) + theta.2 * Shao.energy z := by
    simp only [S, f, Finset.sum_add_distrib, ← Finset.mul_sum, Shao.energy]
  have hcancel (z : Shao.Path n) :
      (Real.exp (S z) / Z ^ n) * G z = c := by
    have heq : S z + -(theta.1 * ((∑ i : Fin n, z i) - (n : ℝ) * y.1) +
        theta.2 * (Shao.energy z - (n : ℝ) * y.2)) =
        (n : ℝ) * (theta.1 * y.1 + theta.2 * y.2) := by
      rw [hSfun]
      ring
    dsimp only [G, c]
    rw [div_mul_eq_mul_div, ← Real.exp_add, heq]
  have hmeasS : Measurable S := by dsimp [S, f]; fun_prop
  have hdmeas : Measurable (fun z : Shao.Path n =>
      ENNReal.ofReal (Real.exp (S z) / Z ^ n)) :=
    ((Real.measurable_exp.comp hmeasS).div_const _).ennreal_ofReal
  have hG : Integrable G Q := by
    rw [← htilt0, Measure.tilted, hnorm0]
    apply (integrable_withDensity_iff hdmeas
      (Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))).mpr
    have hpoint : (fun z : Shao.Path n =>
        G z * (ENNReal.ofReal (Real.exp (S z) / Z ^ n)).toReal) = fun _ => c := by
      funext z
      rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hZn.le), mul_comm]
      exact hcancel z
    rw [hpoint]
    exact integrable_const _
  have hint : (∫ z : Shao.Path n in E, G z ∂Q) = c * P.real E := by
    rw [← htilt0, setIntegral_tilted' S G hE, hnorm0]
    simp only [smul_eq_mul]
    simp_rw [hcancel]
    simp [measureReal_def, mul_comm]
  have hfactor : Real.exp (-(n : ℝ) * (theta.1 * y.1 + theta.2 * y.2 - K)) * c = 1 := by
    dsimp only [c, K]
    have hnlog : Real.exp ((n : ℝ) * Real.log Z) = Z ^ n := by
      rw [Real.exp_nat_mul, Real.exp_log hZ]
    rw [show -(n : ℝ) * (theta.1 * y.1 + theta.2 * y.2 - Real.log Z) =
      (n : ℝ) * Real.log Z - (n : ℝ) * (theta.1 * y.1 + theta.2 * y.2) from by ring,
      Real.exp_sub, hnlog]
    field_simp
  refine ⟨hG, ?_⟩
  rw [hint, ← mul_assoc, hfactor, one_mul]

end
end Shao.OQ3
