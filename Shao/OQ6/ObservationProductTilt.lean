import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Integral.Pi

/-!
The finite observation product law used in p37 section 6 and the p39
quadratic-tilt estimates. Coordinates retain the full original observation
space, and all normalizers are actual integrals. The probability engine
in those sources is attributed to Shao and Zhou; this file supplies only
the finite-product change-of-measure mechanism.

Partial tilts and their additional inverse coordinate normalizer are later
consumers of this full family-exponent law.
-/

set_option autoImplicit false

namespace Shao.OQ6

noncomputable section

open MeasureTheory
open scoped BigOperators

theorem finite_observation_product_tilt
    {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (mu : Fin n → Measure Ω)
    [∀ j : Fin n, IsProbabilityMeasure (mu j)]
    (phi : Fin n → Ω → ℝ)
    (hExp : ∀ j : Fin n,
      Integrable (fun o : Ω => Real.exp (phi j o)) (mu j)) :
    let S : (Fin n → Ω) → ℝ := fun xi =>
      ∑ j : Fin n, phi j (xi j)
    let m : Fin n → ℝ := fun j =>
      ∫ o : Ω, Real.exp (phi j o) ∂(mu j)
    let P : Measure (Fin n → Ω) := Measure.pi mu
    Integrable (fun xi => Real.exp (S xi)) P ∧
      (∫ xi : Fin n → Ω, Real.exp (S xi) ∂P) =
        (∏ j : Fin n, m j) ∧
      0 < (∫ xi : Fin n → Ω, Real.exp (S xi) ∂P) ∧
      P.tilted S =
        Measure.pi (fun j : Fin n => (mu j).tilted (phi j)) := by
  classical
  let S : (Fin n → Ω) → ℝ := fun xi =>
    ∑ j : Fin n, phi j (xi j)
  let m : Fin n → ℝ := fun j =>
    ∫ o : Ω, Real.exp (phi j o) ∂(mu j)
  let P : Measure (Fin n → Ω) := Measure.pi mu
  have hm (j : Fin n) : 0 < m j := integral_exp_pos (hExp j)
  letI : ∀ j : Fin n, IsProbabilityMeasure ((mu j).tilted (phi j)) :=
    fun j => isProbabilityMeasure_tilted (hExp j)
  have hfun : (fun xi : Fin n → Ω => Real.exp (S xi)) =
      (fun xi => ∏ j : Fin n, Real.exp (phi j (xi j))) := by
    funext xi
    exact Real.exp_sum _ _
  have hS : Integrable (fun xi : Fin n → Ω => Real.exp (S xi)) P := by
    change Integrable (fun xi : Fin n → Ω => Real.exp (S xi)) (Measure.pi mu)
    rw [hfun]
    exact Integrable.fintype_prod hExp
  have hnorm : (∫ xi : Fin n → Ω, Real.exp (S xi) ∂P) =
      ∏ j : Fin n, m j := by
    change (∫ xi : Fin n → Ω, Real.exp (S xi) ∂Measure.pi mu) =
      ∏ j : Fin n, m j
    rw [hfun, integral_fintype_prod_eq_prod
      (fun j : Fin n => fun o : Ω => Real.exp (phi j o))]
  have hI : 0 < (∫ xi : Fin n → Ω, Real.exp (S xi) ∂P) :=
    integral_exp_pos hS
  letI : IsProbabilityMeasure (P.tilted S) := isProbabilityMeasure_tilted hS
  refine ⟨hS, hnorm, hI, ?_⟩
  have hdensity :
      (fun xi : Fin n → Ω => Real.exp (S xi) / (∏ j : Fin n, m j)) =
      (fun xi => ∏ j : Fin n, Real.exp (phi j (xi j)) / m j) := by
    funext xi
    rw [Finset.prod_div_distrib, ← Real.exp_sum]
  symm
  apply Measure.pi_eq
  intro A hA
  rw [tilted_apply' _ _ (MeasurableSet.univ_pi hA), hnorm]
  change (∫⁻ xi in Set.univ.pi A, ENNReal.ofReal
    (Real.exp (S xi) / (∏ j : Fin n, m j)) ∂Measure.pi mu) = _
  simp_rw [congrFun hdensity]
  rw [Measure.restrict_pi_pi]
  have hcoord (j : Fin n) : Integrable
      (fun o : Ω => Real.exp (phi j o) / m j) ((mu j).restrict (A j)) :=
    (hExp j).integrableOn.div_const (m j)
  have hprod := Integrable.fintype_prod hcoord
  rw [← ofReal_integral_eq_lintegral_ofReal hprod
    (Filter.Eventually.of_forall (fun xi => Finset.prod_nonneg
      (fun j _ => div_nonneg (Real.exp_pos _).le (hm j).le)))]
  rw [integral_fintype_prod_eq_prod
    (fun j : Fin n => fun o : Ω => Real.exp (phi j o) / m j)]
  rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => integral_nonneg
    (fun o => div_nonneg (Real.exp_pos _).le (hm j).le))]
  apply Finset.prod_congr rfl
  intro j _
  rw [tilted_apply_eq_ofReal_integral' _ (hA j)]

end

end Shao.OQ6
