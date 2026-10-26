/- Source-bound unit197 implementation of the eleven parent-frozen declarations.
   Qualification remains pending the designated server and independent review. -/

import Shao.OQ5.P51.BoundedPolylogConcentration
import Shao.OQ5.P51.BoundedStudentizerGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Real
set_option autoImplicit false
universe u
open Filter MeasureTheory
open scoped BigOperators ENNReal
open Shao.OQ6.BoundedProductEnvelopeTails (tailScale)
open Shao.OQ6.CanonicalDoubleGhostRowMoments (sampleLaw originalRows)
open Shao.OQ6.CanonicalDoubleGhostScalarMoments (originalUpper)
namespace Shao.OQ5.P51
noncomputable section

-- D01
def remainderWindowScale (K t0 : ℝ) : ℝ :=
  min (1 : ℝ)
    (min (1 / ((32 : ℝ) * (K + 1) * (t0 + 1)))
      (1 / Real.sqrt ((32 : ℝ) * (studentizerGeometryScale K + 1) *
        (1 + Real.sqrt t0 + t0))))

-- D02
def lowerStudentizerBad
    (n : ℕ) {Ω : Type u} (g : Ω → ℝ) (r : Ω → Ω → ℝ) (y : ℝ) :
    Set (Fin n → Ω) :=
  {x : Fin n → Ω | centeredDelta n g r x < -(1 / 2 : ℝ) ∧
    x ∈ projectionGood n g y}

-- D03
def numeratorRemainderBad
    (n : ℕ) {Ω : Type u} (g : Ω → ℝ) (r : Ω → Ω → ℝ) (y : ℝ) :
    Set (Fin n → Ω) :=
  {x : Fin n → Ω | projectionV n g x / 4 < y * |residualStatisticD n r x| ∧
    x ∈ projectionGood n g y}

-- D04
def denominatorRemainderBad
    (n : ℕ) {Ω : Type u} (g : Ω → ℝ) (r : Ω → Ω → ℝ) (y : ℝ) :
    Set (Fin n → Ω) :=
  {x : Fin n → Ω | (1 / 4 : ℝ) < y ^ (2 : ℕ) * |centeredDelta n g r x| ∧
    x ∈ projectionGood n g y}

-- D05
def remainderBadUnion
    (n : ℕ) {Ω : Type u} (g : Ω → ℝ) (r : Ω → Ω → ℝ) (y : ℝ) :
    Set (Fin n → Ω) :=
  (lowerStudentizerBad n g r y ∪ numeratorRemainderBad n g r y) ∪
    denominatorRemainderBad n g r y

-- D06
def remainderPayment
    (n : ℕ) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure (Fin n → Ω)) (g : Ω → ℝ) (r : Ω → Ω → ℝ) (y : ℝ) : ℝ :=
  (μ.real (lowerStudentizerBad n g r y) + μ.real (numeratorRemainderBad n g r y)) +
    μ.real (denominatorRemainderBad n g r y)

-- D07
theorem remainderWindowScale_bounds
    (K t0 : ℝ) (hK : 0 ≤ K) (ht0 : 0 < t0) :
    0 < remainderWindowScale K t0 ∧
      remainderWindowScale K t0 ≤ 1 ∧
      remainderWindowScale K t0 ≤ 1 / ((32 : ℝ) * (K + 1) * (t0 + 1)) ∧
      remainderWindowScale K t0 ≤
        1 / Real.sqrt ((32 : ℝ) * (studentizerGeometryScale K + 1) *
          (1 + Real.sqrt t0 + t0)) := by
  have hCg0 : 0 ≤ studentizerGeometryScale K := by
    dsimp only [studentizerGeometryScale]
    nlinarith only [hK, Real.sqrt_nonneg K]
  have hDen : 0 < (32 : ℝ) * (K + 1) * (t0 + 1) := by
    exact mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
  have hRad : 0 < (32 : ℝ) * (studentizerGeometryScale K + 1) *
      (1 + Real.sqrt t0 + t0) := by
    exact mul_pos (mul_pos (by norm_num) (by linarith))
      (by linarith [Real.sqrt_nonneg t0])
  have hRoot : 0 < Real.sqrt ((32 : ℝ) * (studentizerGeometryScale K + 1) *
      (1 + Real.sqrt t0 + t0)) := Real.sqrt_pos.mpr hRad
  unfold remainderWindowScale
  exact ⟨lt_min zero_lt_one (lt_min (one_div_pos.mpr hDen) (one_div_pos.mpr hRoot)),
    min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _)⟩

-- D08
theorem bounded_remainder_small_window
    (n : ℕ) {Ω : Type u} (g : Ω → ℝ) (r : Ω → Ω → ℝ)
    (x : Fin n → Ω) (K t0 y : ℝ)
    (hsym : ∀ a b : Ω, r a b = r b a) (hn : 4 ≤ n)
    (hK : 0 ≤ K) (ht0 : 0 < t0) (hy : (1 : ℝ) ≤ y)
    (hyWindow : y ≤ remainderWindowScale K t0 * Real.rpow (n : ℝ) (1 / 6 : ℝ))
    (hF : |originalUpper n r x| ≤ K * (n : ℝ) * boundedPolylogMomentOrder t0 n)
    (hRows : ‖originalRows n r x‖ ^ (2 : ℕ) ≤
      K * (n : ℝ) ^ (2 : ℕ) * boundedPolylogMomentOrder t0 n)
    (hGood : x ∈ projectionGood n g y) :
    0 < projectionV n g x ∧
      y * |residualStatisticD n r x| / projectionV n g x ≤ (1 / 8 : ℝ) ∧
      y ^ (2 : ℕ) * |centeredDelta n g r x| ≤ (1 / 32 : ℝ) ∧
      |centeredDelta n g r x| ≤ (1 / 32 : ℝ) := by
  have hNonnegSquareUnique (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
      (hSq : s ^ (2 : ℕ) = t ^ (2 : ℕ)) : s = t := by
    have hZero : (s - t) * (s + t) = 0 := by nlinarith only [hSq]
    rcases mul_eq_zero.mp hZero with hDiff | hSum
    · linarith only [hDiff]
    · linarith only [hs, ht, hSum]
  have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hsN : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have ha0 : 0 < Real.rpow (n : ℝ) (1 / 6 : ℝ) :=
    Real.rpow_pos_of_pos hn0 (1 / 6 : ℝ)
  have hb0 : 0 < Real.rpow (n : ℝ) (1 / 3 : ℝ) :=
    Real.rpow_pos_of_pos hn0 (1 / 3 : ℝ)
  have hb1 : 1 ≤ Real.rpow (n : ℝ) (1 / 3 : ℝ) := by
    simpa only [Real.rpow_eq_pow, Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le hn1
        (by norm_num : (0 : ℝ) ≤ (1 / 3 : ℝ)))
  have ha2 : (Real.rpow (n : ℝ) (1 / 6 : ℝ)) ^ (2 : ℕ) =
      Real.rpow (n : ℝ) (1 / 3 : ℝ) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hn0)]
    norm_num
  have ha6 : (Real.rpow (n : ℝ) (1 / 6 : ℝ)) ^ (6 : ℕ) = (n : ℝ) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hn0)]
    norm_num
  have hb3 : (Real.rpow (n : ℝ) (1 / 3 : ℝ)) ^ (3 : ℕ) = (n : ℝ) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hn0)]
    norm_num
  have ha3sq : ((Real.rpow (n : ℝ) (1 / 6 : ℝ)) ^ (3 : ℕ)) ^ (2 : ℕ) =
      (Real.sqrt (n : ℝ)) ^ (2 : ℕ) := by
    rw [← pow_mul, show (3 : ℕ) * 2 = 6 by norm_num, ha6,
      Real.sq_sqrt (le_of_lt hn0)]
  have ha3 : (Real.rpow (n : ℝ) (1 / 6 : ℝ)) ^ (3 : ℕ) =
      Real.sqrt (n : ℝ) := by
    exact hNonnegSquareUnique _ _ (pow_nonneg (le_of_lt ha0) (3 : ℕ))
      (Real.sqrt_nonneg (n : ℝ)) ha3sq
  have hq0 : 0 ≤ boundedPolylogMomentOrder t0 n := by
    dsimp only [boundedPolylogMomentOrder]
    exact mul_nonneg (le_of_lt ht0) (le_of_lt hb0)
  have hqDiv : boundedPolylogMomentOrder t0 n / (n : ℝ) =
      t0 / (Real.rpow (n : ℝ) (1 / 3 : ℝ)) ^ (2 : ℕ) := by
    dsimp only [boundedPolylogMomentOrder]
    apply (div_eq_div_iff (ne_of_gt hn0) (pow_ne_zero 2 (ne_of_gt hb0))).2
    calc
      (t0 * Real.rpow (n : ℝ) (1 / 3 : ℝ)) *
          (Real.rpow (n : ℝ) (1 / 3 : ℝ)) ^ (2 : ℕ) =
        t0 * (Real.rpow (n : ℝ) (1 / 3 : ℝ)) ^ (3 : ℕ) := by ring
      _ = t0 * (n : ℝ) := by rw [hb3]
  have hsRatio : Real.sqrt (boundedPolylogMomentOrder t0 n / (n : ℝ)) =
      Real.sqrt t0 / Real.rpow (n : ℝ) (1 / 3 : ℝ) := by
    have hLeft0 : 0 ≤ Real.sqrt (boundedPolylogMomentOrder t0 n / (n : ℝ)) :=
      Real.sqrt_nonneg _
    have hRight0 : 0 ≤ Real.sqrt t0 / Real.rpow (n : ℝ) (1 / 3 : ℝ) :=
      div_nonneg (Real.sqrt_nonneg t0) (le_of_lt hb0)
    have hLeftSq : (Real.sqrt (boundedPolylogMomentOrder t0 n / (n : ℝ))) ^ (2 : ℕ) =
        boundedPolylogMomentOrder t0 n / (n : ℝ) :=
      Real.sq_sqrt (div_nonneg hq0 (le_of_lt hn0))
    have hRightSq : (Real.sqrt t0 / Real.rpow (n : ℝ) (1 / 3 : ℝ)) ^ (2 : ℕ) =
        boundedPolylogMomentOrder t0 n / (n : ℝ) := by
      rw [div_pow, Real.sq_sqrt (le_of_lt ht0), hqDiv]
    exact hNonnegSquareUnique _ _ hLeft0 hRight0 (hLeftSq.trans hRightSq.symm)
  have hc : 0 < remainderWindowScale K t0 ∧
      remainderWindowScale K t0 ≤ 1 ∧
      remainderWindowScale K t0 ≤ 1 / ((32 : ℝ) * (K + 1) * (t0 + 1)) ∧
      remainderWindowScale K t0 ≤
        1 / Real.sqrt ((32 : ℝ) * (studentizerGeometryScale K + 1) *
          (1 + Real.sqrt t0 + t0)) := remainderWindowScale_bounds K t0 hK ht0
  have hy0 : 0 ≤ y := by linarith
  have hV : 0 < projectionV n g x := (projectionGood_bounds n g x y hn hy hGood).1
  have hD : |residualStatisticD n r x| / projectionV n g x ≤
      4 * K * boundedPolylogMomentOrder t0 n / Real.sqrt (n : ℝ) :=
    (bounded_studentizer_geometry n g r x K (boundedPolylogMomentOrder t0 n) y
      hsym hn hK hq0 hy hF hRows hGood).2.1
  have hd : |centeredDelta n g r x| ≤
      studentizerGeometryScale K * (y / Real.sqrt (n : ℝ) +
        Real.sqrt (boundedPolylogMomentOrder t0 n / (n : ℝ)) +
        boundedPolylogMomentOrder t0 n / (n : ℝ)) :=
    (bounded_studentizer_geometry n g r x K (boundedPolylogMomentOrder t0 n) y
      hsym hn hK hq0 hy hF hRows hGood).2.2.2
  have hNumerator : y * |residualStatisticD n r x| / projectionV n g x ≤
      4 * K * t0 * remainderWindowScale K t0 := by
    calc
      y * |residualStatisticD n r x| / projectionV n g x =
          y * (|residualStatisticD n r x| / projectionV n g x) := by ring
      _ ≤ y * (4 * K * boundedPolylogMomentOrder t0 n / Real.sqrt (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hD hy0
      _ = 4 * K * t0 * (y / Real.rpow (n : ℝ) (1 / 6 : ℝ)) := by
        dsimp only [boundedPolylogMomentOrder]
        rw [← ha2, ← ha3]
        field_simp [ne_of_gt ha0] <;> ring
      _ ≤ 4 * K * t0 * remainderWindowScale K t0 :=
        mul_le_mul_of_nonneg_left ((div_le_iff₀ ha0).2 hyWindow)
          (mul_nonneg (mul_nonneg (by norm_num) hK) (le_of_lt ht0))
  have hDen : 0 < (32 : ℝ) * (K + 1) * (t0 + 1) := by
    exact mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
  have hcDen : remainderWindowScale K t0 * ((32 : ℝ) * (K + 1) * (t0 + 1)) ≤ 1 :=
    (le_div_iff₀ hDen).1 hc.2.2.1
  have hNumGap : 0 ≤ remainderWindowScale K t0 *
      ((K + 1) * (t0 + 1) - K * t0) := by
    exact mul_nonneg (le_of_lt hc.1) (by nlinarith only [hK, ht0])
  have hNumeratorBudget : 4 * K * t0 * remainderWindowScale K t0 ≤ (1 / 8 : ℝ) := by
    nlinarith only [hcDen, hNumGap]
  have hySquareRaw : y ^ (2 : ℕ) ≤
      (remainderWindowScale K t0 * Real.rpow (n : ℝ) (1 / 6 : ℝ)) ^ (2 : ℕ) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hyWindow)
      (add_nonneg (mul_nonneg (le_of_lt hc.1) (le_of_lt ha0)) hy0)]
  have hySquare : y ^ (2 : ℕ) ≤ (remainderWindowScale K t0) ^ (2 : ℕ) *
      Real.rpow (n : ℝ) (1 / 3 : ℝ) := by
    simpa only [mul_pow, ha2] using hySquareRaw
  have hyCube : y ^ (3 : ℕ) ≤
      (remainderWindowScale K t0 * Real.rpow (n : ℝ) (1 / 6 : ℝ)) ^ (3 : ℕ) := by
    calc
      y ^ (3 : ℕ) = y ^ (2 : ℕ) * y := by ring
      _ ≤ (remainderWindowScale K t0 * Real.rpow (n : ℝ) (1 / 6 : ℝ)) ^ (2 : ℕ) *
          (remainderWindowScale K t0 * Real.rpow (n : ℝ) (1 / 6 : ℝ)) :=
        mul_le_mul hySquareRaw hyWindow hy0 (sq_nonneg _)
      _ = (remainderWindowScale K t0 * Real.rpow (n : ℝ) (1 / 6 : ℝ)) ^ (3 : ℕ) := by ring
  have hTermOne : y ^ (3 : ℕ) / Real.sqrt (n : ℝ) ≤
      (remainderWindowScale K t0) ^ (3 : ℕ) := by
    apply (div_le_iff₀ hsN).2
    simpa only [mul_pow, ha3] using hyCube
  have hTermTwo : y ^ (2 : ℕ) *
      Real.sqrt (boundedPolylogMomentOrder t0 n / (n : ℝ)) ≤
      (remainderWindowScale K t0) ^ (2 : ℕ) * Real.sqrt t0 := by
    rw [hsRatio]
    calc
      y ^ (2 : ℕ) * (Real.sqrt t0 / Real.rpow (n : ℝ) (1 / 3 : ℝ)) ≤
          ((remainderWindowScale K t0) ^ (2 : ℕ) * Real.rpow (n : ℝ) (1 / 3 : ℝ)) *
          (Real.sqrt t0 / Real.rpow (n : ℝ) (1 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_right hySquare
          (div_nonneg (Real.sqrt_nonneg t0) (le_of_lt hb0))
      _ = (remainderWindowScale K t0) ^ (2 : ℕ) * Real.sqrt t0 := by
        field_simp [ne_of_gt hb0] <;> ring
  have hTermThree : y ^ (2 : ℕ) * (boundedPolylogMomentOrder t0 n / (n : ℝ)) ≤
      (remainderWindowScale K t0) ^ (2 : ℕ) * t0 := by
    rw [hqDiv]
    calc
      y ^ (2 : ℕ) * (t0 / (Real.rpow (n : ℝ) (1 / 3 : ℝ)) ^ (2 : ℕ)) ≤
          ((remainderWindowScale K t0) ^ (2 : ℕ) * Real.rpow (n : ℝ) (1 / 3 : ℝ)) *
          (t0 / (Real.rpow (n : ℝ) (1 / 3 : ℝ)) ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_right hySquare
          (div_nonneg (le_of_lt ht0) (sq_nonneg _))
      _ = (remainderWindowScale K t0) ^ (2 : ℕ) * t0 /
          Real.rpow (n : ℝ) (1 / 3 : ℝ) := by
        field_simp [ne_of_gt hb0] <;> ring
      _ ≤ (remainderWindowScale K t0) ^ (2 : ℕ) * t0 := by
        apply (div_le_iff₀ hb0).2
        nlinarith only [mul_nonneg
          (mul_nonneg (sq_nonneg (remainderWindowScale K t0)) (le_of_lt ht0))
          (sub_nonneg.mpr hb1)]
  have hDensity : y ^ (2 : ℕ) * (y / Real.sqrt (n : ℝ) +
      Real.sqrt (boundedPolylogMomentOrder t0 n / (n : ℝ)) +
      boundedPolylogMomentOrder t0 n / (n : ℝ)) ≤
      (remainderWindowScale K t0) ^ (2 : ℕ) * (1 + Real.sqrt t0 + t0) := by
    calc
      y ^ (2 : ℕ) * (y / Real.sqrt (n : ℝ) +
          Real.sqrt (boundedPolylogMomentOrder t0 n / (n : ℝ)) +
          boundedPolylogMomentOrder t0 n / (n : ℝ)) =
          y ^ (3 : ℕ) / Real.sqrt (n : ℝ) +
          y ^ (2 : ℕ) * Real.sqrt (boundedPolylogMomentOrder t0 n / (n : ℝ)) +
          y ^ (2 : ℕ) * (boundedPolylogMomentOrder t0 n / (n : ℝ)) := by ring
      _ ≤ (remainderWindowScale K t0) ^ (3 : ℕ) +
          (remainderWindowScale K t0) ^ (2 : ℕ) * Real.sqrt t0 +
          (remainderWindowScale K t0) ^ (2 : ℕ) * t0 :=
        add_le_add (add_le_add hTermOne hTermTwo) hTermThree
      _ ≤ (remainderWindowScale K t0) ^ (2 : ℕ) * (1 + Real.sqrt t0 + t0) := by
        nlinarith only [mul_nonneg (sq_nonneg (remainderWindowScale K t0))
          (sub_nonneg.mpr hc.2.1)]
  have hCg0 : 0 ≤ studentizerGeometryScale K := by
    dsimp only [studentizerGeometryScale]
    nlinarith only [hK, Real.sqrt_nonneg K]
  have hA0 : 0 < (1 : ℝ) + Real.sqrt t0 + t0 := by
    linarith [Real.sqrt_nonneg t0]
  have hRad : 0 < (32 : ℝ) * (studentizerGeometryScale K + 1) *
      (1 + Real.sqrt t0 + t0) := by
    exact mul_pos (mul_pos (by norm_num) (by linarith)) hA0
  have hRoot : 0 < Real.sqrt ((32 : ℝ) * (studentizerGeometryScale K + 1) *
      (1 + Real.sqrt t0 + t0)) := Real.sqrt_pos.mpr hRad
  have hcRoot : remainderWindowScale K t0 *
      Real.sqrt ((32 : ℝ) * (studentizerGeometryScale K + 1) *
        (1 + Real.sqrt t0 + t0)) ≤ 1 :=
    (le_div_iff₀ hRoot).1 hc.2.2.2
  have hcRoot0 : 0 ≤ remainderWindowScale K t0 *
      Real.sqrt ((32 : ℝ) * (studentizerGeometryScale K + 1) *
        (1 + Real.sqrt t0 + t0)) :=
    mul_nonneg (le_of_lt hc.1) (Real.sqrt_nonneg _)
  have hcRootSq : (remainderWindowScale K t0 *
      Real.sqrt ((32 : ℝ) * (studentizerGeometryScale K + 1) *
        (1 + Real.sqrt t0 + t0))) ^ (2 : ℕ) ≤ 1 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hcRoot)
      (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) hcRoot0)]
  have hcSquare : (remainderWindowScale K t0) ^ (2 : ℕ) *
      ((32 : ℝ) * (studentizerGeometryScale K + 1) * (1 + Real.sqrt t0 + t0)) ≤ 1 := by
    simpa only [mul_pow, Real.sq_sqrt (le_of_lt hRad)] using hcRootSq
  have hBudget : studentizerGeometryScale K * (remainderWindowScale K t0) ^ (2 : ℕ) *
      (1 + Real.sqrt t0 + t0) ≤ (1 / 32 : ℝ) := by
    nlinarith only [hcSquare,
      mul_nonneg (sq_nonneg (remainderWindowScale K t0)) (le_of_lt hA0)]
  have hScaled : y ^ (2 : ℕ) * |centeredDelta n g r x| ≤
      studentizerGeometryScale K * (remainderWindowScale K t0) ^ (2 : ℕ) *
        (1 + Real.sqrt t0 + t0) := by
    calc
      y ^ (2 : ℕ) * |centeredDelta n g r x| ≤
          y ^ (2 : ℕ) * (studentizerGeometryScale K *
            (y / Real.sqrt (n : ℝ) + Real.sqrt (boundedPolylogMomentOrder t0 n / (n : ℝ)) +
              boundedPolylogMomentOrder t0 n / (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hd (sq_nonneg y)
      _ = studentizerGeometryScale K * (y ^ (2 : ℕ) *
          (y / Real.sqrt (n : ℝ) + Real.sqrt (boundedPolylogMomentOrder t0 n / (n : ℝ)) +
            boundedPolylogMomentOrder t0 n / (n : ℝ))) := by ring
      _ ≤ studentizerGeometryScale K * ((remainderWindowScale K t0) ^ (2 : ℕ) *
          (1 + Real.sqrt t0 + t0)) := mul_le_mul_of_nonneg_left hDensity hCg0
      _ = studentizerGeometryScale K * (remainderWindowScale K t0) ^ (2 : ℕ) *
          (1 + Real.sqrt t0 + t0) := by ring
  have hySquareOne : (1 : ℝ) ≤ y ^ (2 : ℕ) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hy)
      (add_nonneg hy0 (by norm_num : (0 : ℝ) ≤ 1))]
  have hAbsScaled : |centeredDelta n g r x| ≤ y ^ (2 : ℕ) * |centeredDelta n g r x| := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hySquareOne) (abs_nonneg (centeredDelta n g r x))]
  exact ⟨hV, hNumerator.trans hNumeratorBudget, hScaled.trans hBudget,
    hAbsScaled.trans (hScaled.trans hBudget)⟩

-- D09
theorem bounded_remainder_bad_subsets
    (n : ℕ) {Ω : Type u} (g : Ω → ℝ) (r : Ω → Ω → ℝ)
    (w : Ω → ℝ) (M t0 y : ℝ)
    (hM0 : 0 ≤ M) (ht0 : 0 < t0)
    (hsym : ∀ a b : Ω, r a b = r b a) (hn : 4 ≤ n) (hy : (1 : ℝ) ≤ y)
    (hyWindow : y ≤ remainderWindowScale (tailScale M) t0 *
      Real.rpow (n : ℝ) (1 / 6 : ℝ)) :
    lowerStudentizerBad n g r y ⊆
        boundedProductFailure n r w M (boundedPolylogMomentOrder t0 n) ∧
      numeratorRemainderBad n g r y ⊆
        boundedProductFailure n r w M (boundedPolylogMomentOrder t0 n) ∧
      denominatorRemainderBad n g r y ⊆
        boundedProductFailure n r w M (boundedPolylogMomentOrder t0 n) ∧
      remainderBadUnion n g r y ⊆
        boundedProductFailure n r w M (boundedPolylogMomentOrder t0 n) := by
  have hK : 0 < tailScale M :=
    (Shao.OQ6.BoundedProductEnvelopeTails.bounded_scales_pos M hM0).2.2.2.2.2
  have hSmall (x : Fin n → Ω)
      (hNot : x ∉ boundedProductFailure n r w M (boundedPolylogMomentOrder t0 n))
      (hGood : x ∈ projectionGood n g y) :
      0 < projectionV n g x ∧
        y * |residualStatisticD n r x| / projectionV n g x ≤ (1 / 8 : ℝ) ∧
        y ^ (2 : ℕ) * |centeredDelta n g r x| ≤ (1 / 32 : ℝ) ∧
        |centeredDelta n g r x| ≤ (1 / 32 : ℝ) := by
    have hBounds :
        Shao.OQ6.BoundedProductEnvelopeTails.squareSum n w x ≤ tailScale M * (n : ℝ) ∧
          |originalUpper n r x| ≤ tailScale M * (n : ℝ) * boundedPolylogMomentOrder t0 n ∧
          ‖originalRows n r x‖ ^ (2 : ℕ) ≤
            tailScale M * (n : ℝ) ^ (2 : ℕ) * boundedPolylogMomentOrder t0 n :=
      (not_mem_boundedProductFailure_iff n r w M (boundedPolylogMomentOrder t0 n) x).1 hNot
    exact bounded_remainder_small_window n g r x (tailScale M) t0 y hsym hn
      (le_of_lt hK) ht0 hy hyWindow hBounds.2.1 hBounds.2.2 hGood
  have hOne : lowerStudentizerBad n g r y ⊆
      boundedProductFailure n r w M (boundedPolylogMomentOrder t0 n) := by
    intro x hx
    apply Classical.byContradiction
    intro hNot
    have hBound : |centeredDelta n g r x| ≤ (1 / 32 : ℝ) :=
      (hSmall x hNot hx.2).2.2.2
    have hLower : -|centeredDelta n g r x| ≤ centeredDelta n g r x :=
      neg_abs_le (centeredDelta n g r x)
    nlinarith only [hx.1, hBound, hLower]
  have hTwo : numeratorRemainderBad n g r y ⊆
      boundedProductFailure n r w M (boundedPolylogMomentOrder t0 n) := by
    intro x hx
    apply Classical.byContradiction
    intro hNot
    have hV : 0 < projectionV n g x := (hSmall x hNot hx.2).1
    have hRatio : y * |residualStatisticD n r x| / projectionV n g x ≤ (1 / 8 : ℝ) :=
      (hSmall x hNot hx.2).2.1
    have hBound : y * |residualStatisticD n r x| ≤ (1 / 8 : ℝ) * projectionV n g x :=
      (div_le_iff₀ hV).1 hRatio
    nlinarith only [hx.1, hV, hBound]
  have hThree : denominatorRemainderBad n g r y ⊆
      boundedProductFailure n r w M (boundedPolylogMomentOrder t0 n) := by
    intro x hx
    apply Classical.byContradiction
    intro hNot
    have hBound : y ^ (2 : ℕ) * |centeredDelta n g r x| ≤ (1 / 32 : ℝ) :=
      (hSmall x hNot hx.2).2.2.1
    nlinarith only [hx.1, hBound]
  refine ⟨hOne, hTwo, hThree, ?_⟩
  intro x hx
  rcases hx with (hx | hx) | hx
  · exact hOne hx
  · exact hTwo hx
  · exact hThree hx

-- D10
theorem canonical_bounded_remainder_payments
    (n : ℕ) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω) [hν : IsProbabilityMeasure ν]
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (w : Ω → ℝ) (R M t0 y : ℝ)
    (hR0 : 0 ≤ R) (hM0 : 0 ≤ M) (ht0 : 0 < t0)
    (hr : Measurable (Function.uncurry r))
    (hr1 : Integrable (Function.uncurry r) (ν.prod ν))
    (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0)
    (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0)
    (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hWR : ∀ᵐ a : Ω ∂ν, w a ≤ R)
    (hSq : Integrable (fun a : Ω => (w a) ^ (2 : ℕ)) ν)
    (hSqBound : (∫ a : Ω, (w a) ^ (2 : ℕ) ∂ν) ≤ M)
    (hEnv : ∀ᵐ z : Ω × Ω ∂ν.prod ν, |r z.1 z.2| ≤ w z.1 * w z.2)
    (hq : (2 : ℝ) ≤ boundedPolylogMomentOrder t0 n)
    (hsym : ∀ a b : Ω, r a b = r b a)
    (hWindow : (2 : ℝ) * R ^ (2 : ℕ) * boundedPolylogMomentOrder t0 n ≤ (n : ℝ))
    (hn : 4 ≤ n) (hy : (1 : ℝ) ≤ y)
    (hyWindow : y ≤ remainderWindowScale (tailScale M) t0 *
      Real.rpow (n : ℝ) (1 / 6 : ℝ)) :
    (sampleLaw n ν).real (lowerStudentizerBad n g r y) ≤
        (3 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) ∧
      (sampleLaw n ν).real (numeratorRemainderBad n g r y) ≤
        (3 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) ∧
      (sampleLaw n ν).real (denominatorRemainderBad n g r y) ≤
        (3 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) ∧
      remainderPayment n (sampleLaw n ν) g r y ≤
        (9 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) ∧
      (sampleLaw n ν).real (remainderBadUnion n g r y) ≤
        (3 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) := by
  have hFailure : (sampleLaw n ν).real
      (boundedProductFailure n r w M (boundedPolylogMomentOrder t0 n)) ≤
      (3 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) :=
    canonical_bounded_product_joint_failure n ν r w R M (boundedPolylogMomentOrder t0 n)
      hR0 hM0 hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hq hsym hWindow
  letI instSample : IsProbabilityMeasure (sampleLaw n ν) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => ν)))
  have hSubsets : lowerStudentizerBad n g r y ⊆
        boundedProductFailure n r w M (boundedPolylogMomentOrder t0 n) ∧
      numeratorRemainderBad n g r y ⊆
        boundedProductFailure n r w M (boundedPolylogMomentOrder t0 n) ∧
      denominatorRemainderBad n g r y ⊆
        boundedProductFailure n r w M (boundedPolylogMomentOrder t0 n) ∧
      remainderBadUnion n g r y ⊆
        boundedProductFailure n r w M (boundedPolylogMomentOrder t0 n) :=
    bounded_remainder_bad_subsets n g r w M t0 y hM0 ht0 hsym hn hy hyWindow
  have hOne : (sampleLaw n ν).real (lowerStudentizerBad n g r y) ≤
      (3 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) :=
    (MeasureTheory.measureReal_mono (μ := sampleLaw n ν) hSubsets.1).trans hFailure
  have hTwo : (sampleLaw n ν).real (numeratorRemainderBad n g r y) ≤
      (3 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) :=
    (MeasureTheory.measureReal_mono (μ := sampleLaw n ν) hSubsets.2.1).trans hFailure
  have hThree : (sampleLaw n ν).real (denominatorRemainderBad n g r y) ≤
      (3 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) :=
    (MeasureTheory.measureReal_mono (μ := sampleLaw n ν) hSubsets.2.2.1).trans hFailure
  have hUnion : (sampleLaw n ν).real (remainderBadUnion n g r y) ≤
      (3 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) :=
    (MeasureTheory.measureReal_mono (μ := sampleLaw n ν) hSubsets.2.2.2).trans hFailure
  refine ⟨hOne, hTwo, hThree, ?_, hUnion⟩
  dsimp only [remainderPayment]
  linarith only [hOne, hTwo, hThree]

-- D11
theorem eventually_boundedPolylog_remainder_payments
    (C a t0 M : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a) (ht0 : 0 < t0) (hM0 : 0 ≤ M) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω]
        (ν : Measure Ω) [hν : IsProbabilityMeasure ν]
        (g : Ω → ℝ) (r : Ω → Ω → ℝ) (w : Ω → ℝ)
        (hr : Measurable (Function.uncurry r))
        (hr1 : Integrable (Function.uncurry r) (ν.prod ν))
        (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0)
        (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0)
        (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
        (hWR : ∀ᵐ o : Ω ∂ν, w o ≤ boundedPolylogHeight C a n)
        (hSq : Integrable (fun a : Ω => (w a) ^ (2 : ℕ)) ν)
        (hSqBound : (∫ a : Ω, (w a) ^ (2 : ℕ) ∂ν) ≤ M)
        (hEnv : ∀ᵐ z : Ω × Ω ∂ν.prod ν, |r z.1 z.2| ≤ w z.1 * w z.2)
        (hsym : ∀ a b : Ω, r a b = r b a)
        (y : ℝ) (hy : (1 : ℝ) ≤ y)
        (hyWindow : y ≤ remainderWindowScale (tailScale M) t0 *
          Real.rpow (n : ℝ) (1 / 6 : ℝ)),
        (sampleLaw n ν).real (lowerStudentizerBad n g r y) ≤
            (3 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) ∧
          (sampleLaw n ν).real (numeratorRemainderBad n g r y) ≤
            (3 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) ∧
          (sampleLaw n ν).real (denominatorRemainderBad n g r y) ≤
            (3 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) ∧
          remainderPayment n (sampleLaw n ν) g r y ≤
            (9 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) ∧
          (sampleLaw n ν).real (remainderBadUnion n g r y) ≤
            (3 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) := by
  filter_upwards [eventually_ge_atTop (4 : ℕ),
    eventually_boundedPolylog_product_joint_failure C a t0 M hC ha ht0 hM0] with n hn hAll
  intro Ω mΩ ν hν g r w hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hsym y hy hyWindow
  have hFailure : (sampleLaw n ν).real
      (boundedProductFailure n r w M (boundedPolylogMomentOrder t0 n)) ≤
      (3 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) :=
    hAll ν r w hr hr1 hcR hcL hW hWR hSq hSqBound hEnv hsym
  letI instSample : IsProbabilityMeasure (sampleLaw n ν) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => ν)))
  have hSubsets : lowerStudentizerBad n g r y ⊆
        boundedProductFailure n r w M (boundedPolylogMomentOrder t0 n) ∧
      numeratorRemainderBad n g r y ⊆
        boundedProductFailure n r w M (boundedPolylogMomentOrder t0 n) ∧
      denominatorRemainderBad n g r y ⊆
        boundedProductFailure n r w M (boundedPolylogMomentOrder t0 n) ∧
      remainderBadUnion n g r y ⊆
        boundedProductFailure n r w M (boundedPolylogMomentOrder t0 n) :=
    bounded_remainder_bad_subsets n g r w M t0 y hM0 ht0 hsym hn hy hyWindow
  have hOne : (sampleLaw n ν).real (lowerStudentizerBad n g r y) ≤
      (3 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) :=
    (MeasureTheory.measureReal_mono (μ := sampleLaw n ν) hSubsets.1).trans hFailure
  have hTwo : (sampleLaw n ν).real (numeratorRemainderBad n g r y) ≤
      (3 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) :=
    (MeasureTheory.measureReal_mono (μ := sampleLaw n ν) hSubsets.2.1).trans hFailure
  have hThree : (sampleLaw n ν).real (denominatorRemainderBad n g r y) ≤
      (3 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) :=
    (MeasureTheory.measureReal_mono (μ := sampleLaw n ν) hSubsets.2.2.1).trans hFailure
  have hUnion : (sampleLaw n ν).real (remainderBadUnion n g r y) ≤
      (3 : ℝ) * Real.exp (-(boundedPolylogMomentOrder t0 n)) :=
    (MeasureTheory.measureReal_mono (μ := sampleLaw n ν) hSubsets.2.2.2).trans hFailure
  refine ⟨hOne, hTwo, hThree, ?_, hUnion⟩
  dsimp only [remainderPayment]
  linarith only [hOne, hTwo, hThree]

end
end Shao.OQ5.P51
