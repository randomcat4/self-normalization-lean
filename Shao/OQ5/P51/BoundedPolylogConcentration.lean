/- Source-bound unit195 implementation of the five frozen declarations.
   Formal qualification is pending the designated server and independent review. -/

import Shao.OQ6.BoundedProductEnvelopeTails
import Shao.OQ5.P51.BoundedPolylogWindow
import Mathlib.MeasureTheory.Measure.Real
set_option autoImplicit false
universe u
open Filter MeasureTheory
open scoped BigOperators ENNReal
open Shao.OQ6.BoundedProductEnvelopeTails (squareSum tailScale)
open Shao.OQ6.CanonicalDoubleGhostRowMoments (sampleLaw originalRows)
open Shao.OQ6.CanonicalDoubleGhostScalarMoments (originalUpper)
namespace Shao.OQ5.P51
noncomputable section

def boundedProductFailure
    (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (w : Ω → ℝ) (M q : ℝ) :
    Set (Fin n → Ω) :=
  ({x : Fin n → Ω | tailScale M * (n : ℝ) < squareSum n w x} ∪
    {x : Fin n → Ω | tailScale M * (n : ℝ) * q < |originalUpper n r x|}) ∪
    {x : Fin n → Ω | tailScale M * (n : ℝ) ^ (2 : ℕ) * q < ‖originalRows n r x‖ ^ (2 : ℕ)}

theorem not_mem_boundedProductFailure_iff
    (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (w : Ω → ℝ) (M q : ℝ) (x : Fin n → Ω) :
    x ∉ boundedProductFailure n r w M q ↔
      squareSum n w x ≤ tailScale M * (n : ℝ) ∧
      |originalUpper n r x| ≤ tailScale M * (n : ℝ) * q ∧
      ‖originalRows n r x‖ ^ (2 : ℕ) ≤ tailScale M * (n : ℝ) ^ (2 : ℕ) * q := by
  simp only [boundedProductFailure, Set.mem_union, Set.mem_setOf_eq,
    not_or, not_lt, and_assoc]

theorem canonical_bounded_product_joint_failure
    (n : ℕ) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω) [hν : IsProbabilityMeasure ν]
    (r : Ω → Ω → ℝ) (w : Ω → ℝ) (R M q : ℝ)
    (hR0 : 0 ≤ R) (hM0 : 0 ≤ M)
    (hr : Measurable (Function.uncurry r))
    (hr1 : Integrable (Function.uncurry r) (ν.prod ν))
    (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0)
    (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0)
    (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hWR : ∀ᵐ a : Ω ∂ν, w a ≤ R)
    (hSq : Integrable (fun a : Ω => (w a) ^ (2 : ℕ)) ν)
    (hSqBound : (∫ a : Ω, (w a) ^ (2 : ℕ) ∂ν) ≤ M)
    (hEnv : ∀ᵐ z : Ω × Ω ∂ν.prod ν, |r z.1 z.2| ≤ w z.1 * w z.2)
    (hq : (2 : ℝ) ≤ q)
    (hsym : ∀ a b : Ω, r a b = r b a)
    (hWindow : (2 : ℝ) * R ^ (2 : ℕ) * q ≤ (n : ℝ)) :
    (sampleLaw n ν).real (boundedProductFailure n r w M q) ≤
      (3 : ℝ) * Real.exp (-q) := by
  have h193 :=
    Shao.OQ6.BoundedProductEnvelopeTails.canonical_bounded_product_tails
      n ν r w R M q hR0 hM0 hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hq hsym hWindow
  have hSum :
      (sampleLaw n ν).real ({x : Fin n → Ω | tailScale M * (n : ℝ) < squareSum n w x}) +
      (sampleLaw n ν).real ({x : Fin n → Ω | tailScale M * (n : ℝ) * q < |originalUpper n r x|}) +
      (sampleLaw n ν).real ({x : Fin n → Ω | tailScale M * (n : ℝ) ^ (2 : ℕ) * q < ‖originalRows n r x‖ ^ (2 : ℕ)}) ≤
        (3 : ℝ) * Real.exp (-q) :=
    h193.2.2.2.2
  have hInner :
      (sampleLaw n ν).real ({x : Fin n → Ω | tailScale M * (n : ℝ) < squareSum n w x} ∪ {x : Fin n → Ω | tailScale M * (n : ℝ) * q < |originalUpper n r x|}) ≤
        (sampleLaw n ν).real ({x : Fin n → Ω | tailScale M * (n : ℝ) < squareSum n w x}) +
          (sampleLaw n ν).real ({x : Fin n → Ω | tailScale M * (n : ℝ) * q < |originalUpper n r x|}) :=
    MeasureTheory.measureReal_union_le (μ := sampleLaw n ν)
      ({x : Fin n → Ω | tailScale M * (n : ℝ) < squareSum n w x})
      ({x : Fin n → Ω | tailScale M * (n : ℝ) * q < |originalUpper n r x|})
  have hOuter :
      (sampleLaw n ν).real (({x : Fin n → Ω | tailScale M * (n : ℝ) < squareSum n w x} ∪ {x : Fin n → Ω | tailScale M * (n : ℝ) * q < |originalUpper n r x|}) ∪ {x : Fin n → Ω | tailScale M * (n : ℝ) ^ (2 : ℕ) * q < ‖originalRows n r x‖ ^ (2 : ℕ)}) ≤
        (sampleLaw n ν).real ({x : Fin n → Ω | tailScale M * (n : ℝ) < squareSum n w x} ∪ {x : Fin n → Ω | tailScale M * (n : ℝ) * q < |originalUpper n r x|}) +
          (sampleLaw n ν).real ({x : Fin n → Ω | tailScale M * (n : ℝ) ^ (2 : ℕ) * q < ‖originalRows n r x‖ ^ (2 : ℕ)}) :=
    MeasureTheory.measureReal_union_le (μ := sampleLaw n ν)
      ({x : Fin n → Ω | tailScale M * (n : ℝ) < squareSum n w x} ∪ {x : Fin n → Ω | tailScale M * (n : ℝ) * q < |originalUpper n r x|})
      ({x : Fin n → Ω | tailScale M * (n : ℝ) ^ (2 : ℕ) * q < ‖originalRows n r x‖ ^ (2 : ℕ)})
  have hLifted :
      (sampleLaw n ν).real ({x : Fin n → Ω | tailScale M * (n : ℝ) < squareSum n w x} ∪ {x : Fin n → Ω | tailScale M * (n : ℝ) * q < |originalUpper n r x|}) +
        (sampleLaw n ν).real ({x : Fin n → Ω | tailScale M * (n : ℝ) ^ (2 : ℕ) * q < ‖originalRows n r x‖ ^ (2 : ℕ)}) ≤
      (sampleLaw n ν).real ({x : Fin n → Ω | tailScale M * (n : ℝ) < squareSum n w x}) +
      (sampleLaw n ν).real ({x : Fin n → Ω | tailScale M * (n : ℝ) * q < |originalUpper n r x|}) +
      (sampleLaw n ν).real ({x : Fin n → Ω | tailScale M * (n : ℝ) ^ (2 : ℕ) * q < ‖originalRows n r x‖ ^ (2 : ℕ)}) :=
    by linarith only [hInner]
  have hUnionSum :
      (sampleLaw n ν).real (({x : Fin n → Ω | tailScale M * (n : ℝ) < squareSum n w x} ∪ {x : Fin n → Ω | tailScale M * (n : ℝ) * q < |originalUpper n r x|}) ∪ {x : Fin n → Ω | tailScale M * (n : ℝ) ^ (2 : ℕ) * q < ‖originalRows n r x‖ ^ (2 : ℕ)}) ≤
      (sampleLaw n ν).real ({x : Fin n → Ω | tailScale M * (n : ℝ) < squareSum n w x}) +
      (sampleLaw n ν).real ({x : Fin n → Ω | tailScale M * (n : ℝ) * q < |originalUpper n r x|}) +
      (sampleLaw n ν).real ({x : Fin n → Ω | tailScale M * (n : ℝ) ^ (2 : ℕ) * q < ‖originalRows n r x‖ ^ (2 : ℕ)}) :=
    hOuter.trans hLifted
  have hResult :
      (sampleLaw n ν).real (boundedProductFailure n r w M q) ≤
        (3 : ℝ) * Real.exp (-q) :=
    hUnionSum.trans hSum
  exact hResult

theorem eventually_boundedPolylog_product_joint_failure
    (C a t0 M : ℝ)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (ht0 : 0 < t0) (hM0 : 0 ≤ M) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω]
        (ν : Measure Ω) [hν : IsProbabilityMeasure ν]
        (r : Ω → Ω → ℝ) (w : Ω → ℝ)
        (hr : Measurable (Function.uncurry r))
        (hr1 : Integrable (Function.uncurry r) (ν.prod ν))
        (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0)
        (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0)
        (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
        (hWR : ∀ᵐ o : Ω ∂ν, w o ≤ boundedPolylogHeight C a n)
        (hSq : Integrable (fun a : Ω => (w a) ^ (2 : ℕ)) ν)
        (hSqBound : (∫ a : Ω, (w a) ^ (2 : ℕ) ∂ν) ≤ M)
        (hEnv : ∀ᵐ z : Ω × Ω ∂ν.prod ν, |r z.1 z.2| ≤ w z.1 * w z.2)
        (hsym : ∀ a b : Ω, r a b = r b a),
        (sampleLaw n ν).real
            (boundedProductFailure n r w M (boundedPolylogMomentOrder t0 n)) ≤
          (3 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) := by
  have hWindowEventually :
      ∀ᶠ n : ℕ in atTop,
        1 < n ∧
          (2 : ℝ) ≤ boundedPolylogMomentOrder t0 n ∧
            (2 : ℝ) * (boundedPolylogHeight C a n) ^ (2 : ℕ) *
              boundedPolylogMomentOrder t0 n ≤ (n : ℝ) :=
    eventually_boundedPolylog_window C a t0 hC ha ht0
  refine hWindowEventually.mono ?_
  intro n hp
  have hnReal : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast hp.1
  have hlog0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (le_of_lt hnReal)
  have hpow0 : 0 ≤ Real.rpow (Real.log (n : ℝ)) a :=
    Real.rpow_nonneg hlog0 a
  have hR0 : 0 ≤ boundedPolylogHeight C a n := by
    simpa only [boundedPolylogHeight] using mul_nonneg hC hpow0
  have hq : (2 : ℝ) ≤ boundedPolylogMomentOrder t0 n :=
    hp.2.1
  have hWindow :
      (2 : ℝ) * (boundedPolylogHeight C a n) ^ (2 : ℕ) *
        boundedPolylogMomentOrder t0 n ≤ (n : ℝ) :=
    hp.2.2
  intro Ω mΩ ν hν r w hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hsym
  have hFiniteResult :
      (sampleLaw n ν).real
          (boundedProductFailure n r w M (boundedPolylogMomentOrder t0 n)) ≤
        (3 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) :=
    canonical_bounded_product_joint_failure n ν r w (boundedPolylogHeight C a n) M
      (boundedPolylogMomentOrder t0 n) hR0 hM0 hr hr1 hcR hcL hW hWR hSq hSqBound
      hEnv hq hsym hWindow
  exact hFiniteResult

theorem eventually_boundedLogCutoff_product_joint_failure
    (A tau alpha t0 M : ℝ)
    (hA : 0 < A) (htau : 0 < tau) (halpha : 0 < alpha)
    (ht0 : 0 < t0) (hM0 : 0 ≤ M) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω]
        (ν : Measure Ω) [hν : IsProbabilityMeasure ν]
        (r : Ω → Ω → ℝ) (w : Ω → ℝ)
        (hr : Measurable (Function.uncurry r))
        (hr1 : Integrable (Function.uncurry r) (ν.prod ν))
        (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0)
        (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0)
        (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
        (hWR : ∀ᵐ a : Ω ∂ν, w a ≤ boundedLogCutoffHeight A tau alpha n)
        (hSq : Integrable (fun a : Ω => (w a) ^ (2 : ℕ)) ν)
        (hSqBound : (∫ a : Ω, (w a) ^ (2 : ℕ) ∂ν) ≤ M)
        (hEnv : ∀ᵐ z : Ω × Ω ∂ν.prod ν, |r z.1 z.2| ≤ w z.1 * w z.2)
        (hsym : ∀ a b : Ω, r a b = r b a),
        (sampleLaw n ν).real
            (boundedProductFailure n r w M (boundedPolylogMomentOrder t0 n)) ≤
          (3 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) := by
  have hWindowEventually :
      ∀ᶠ n : ℕ in atTop,
        1 < n ∧
          (2 : ℝ) ≤ boundedPolylogMomentOrder t0 n ∧
            (2 : ℝ) * (boundedLogCutoffHeight A tau alpha n) ^ (2 : ℕ) *
              boundedPolylogMomentOrder t0 n ≤ (n : ℝ) :=
    eventually_boundedLogCutoff_window A tau alpha t0 hA htau halpha ht0
  refine hWindowEventually.mono ?_
  intro n hp
  have hnReal : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast hp.1
  have hlog0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (le_of_lt hnReal)
  have hBase0 : 0 ≤ A * Real.log (n : ℝ) / tau :=
    div_nonneg (mul_nonneg (le_of_lt hA) hlog0) (le_of_lt htau)
  have hR0 : 0 ≤ boundedLogCutoffHeight A tau alpha n := by
    simpa only [boundedLogCutoffHeight, Real.rpow_eq_pow] using
      Real.rpow_nonneg hBase0 (1 / alpha : ℝ)
  have hq : (2 : ℝ) ≤ boundedPolylogMomentOrder t0 n :=
    hp.2.1
  have hWindow :
      (2 : ℝ) * (boundedLogCutoffHeight A tau alpha n) ^ (2 : ℕ) *
        boundedPolylogMomentOrder t0 n ≤ (n : ℝ) :=
    hp.2.2
  intro Ω mΩ ν hν r w hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hsym
  have hFiniteResult :
      (sampleLaw n ν).real
          (boundedProductFailure n r w M (boundedPolylogMomentOrder t0 n)) ≤
        (3 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) :=
    canonical_bounded_product_joint_failure n ν r w
      (boundedLogCutoffHeight A tau alpha n) M (boundedPolylogMomentOrder t0 n)
      hR0 hM0 hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hq hsym hWindow
  exact hFiniteResult

end
end Shao.OQ5.P51
