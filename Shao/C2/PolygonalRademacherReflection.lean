import Shao.C2.PolygonalPrefixEvents
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section
namespace Shao.C2.PolygonalRademacherReflection
open MeasureTheory ProbabilityTheory Set
open Shao.C2.FiniteWalkReflection Shao.C2.FiniteWalkReflectionCount
open Shao.C2.RademacherReflectionProbability Shao.C2.PolygonalPrefixEvents
open Shao.C2.BrownianUpperJointLimit Shao.OQ4.PolygonalPathTightness

private theorem measurable_prefix (n k : ℕ) :
    Measurable (fun p : Shao.Path n => Shao.prefixSum p k) := by
  unfold Shao.prefixSum
  fun_prop

private theorem real_law_preimage (n : ℕ) (S : Set (Shao.Path n))
    (hS : MeasurableSet S) :
    (Measure.pi (fun _ : Fin n => Shao.OQ4.RademacherCosine.law)).real S =
      (wordLaw n).real (realWord ⁻¹' S) := by
  rw [← realWord_map_eq n]
  change (((wordLaw n).map realWord) S).toReal = _
  rw [Measure.map_apply (measurable_of_countable realWord) hS]
  rfl

theorem closed_prefix_reflection (n : ℕ) (a v : ℝ) (ha : 0 < a) (hv : v < a) :
    (Measure.pi (fun _ : Fin n => Shao.OQ4.RademacherCosine.law)).real
        {p : Shao.Path n | (∀ k : ℕ, k ≤ n → Shao.prefixSum p k ≤ a) ∧
          Shao.prefixSum p n ≤ v} +
      (Measure.pi (fun _ : Fin n => Shao.OQ4.RademacherCosine.law)).real
        {p : Shao.Path n | ((2 * (⌊a⌋ + 1) - ⌊v⌋ : ℤ) : ℝ) ≤ Shao.prefixSum p n} =
      (Measure.pi (fun _ : Fin n => Shao.OQ4.RademacherCosine.law)).real
        {p : Shao.Path n | Shao.prefixSum p n ≤ v} := by
  have hH : (0 : ℤ) < ⌊a⌋ + 1 := by
    have hz := Int.floor_nonneg.mpr ha.le
    omega
  have hX : ⌊v⌋ < ⌊a⌋ + 1 := by
    have hz := Int.floor_mono hv.le
    omega
  have hs : MeasurableSet {p : Shao.Path n | ∀ k : ℕ, k ≤ n → Shao.prefixSum p k ≤ a} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun hk =>
      measurableSet_le (measurable_prefix n k) measurable_const
  have h0 : MeasurableSet {p : Shao.Path n |
      (∀ k : ℕ, k ≤ n → Shao.prefixSum p k ≤ a) ∧ Shao.prefixSum p n ≤ v} :=
    hs.inter (measurableSet_le (measurable_prefix n n) (measurable_const (a := v)))
  have h1 : MeasurableSet {p : Shao.Path n |
      ((2 * (⌊a⌋ + 1) - ⌊v⌋ : ℤ) : ℝ) ≤ Shao.prefixSum p n} :=
    measurableSet_le measurable_const (measurable_prefix n n)
  have h2 : MeasurableSet {p : Shao.Path n | Shao.prefixSum p n ≤ v} :=
    measurableSet_le (measurable_prefix n n) measurable_const
  have hp0 : realWord ⁻¹' {p : Shao.Path n |
      (∀ k : ℕ, k ≤ n → Shao.prefixSum p k ≤ a) ∧ Shao.prefixSum p n ≤ v} =
      {w : Fin n → Bool | (∀ k : ℕ, k ≤ n → walkPrefix w k < ⌊a⌋ + 1) ∧
        walkPrefix w n ≤ ⌊v⌋} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_setOf_eq, realWord_prefix,
      ← Int.le_floor, Int.lt_add_one_iff]
  have hp1 : realWord ⁻¹' {p : Shao.Path n |
      ((2 * (⌊a⌋ + 1) - ⌊v⌋ : ℤ) : ℝ) ≤ Shao.prefixSum p n} =
      {w : Fin n → Bool | 2 * (⌊a⌋ + 1) - ⌊v⌋ ≤ walkPrefix w n} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_setOf_eq, realWord_prefix, Int.cast_le]
  have hp2 : realWord ⁻¹' {p : Shao.Path n | Shao.prefixSum p n ≤ v} =
      {w : Fin n → Bool | walkPrefix w n ≤ ⌊v⌋} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_setOf_eq, realWord_prefix, ← Int.le_floor]
  rw [real_law_preimage _ _ h0, real_law_preimage _ _ h1, real_law_preimage _ _ h2,
    hp0, hp1, hp2, wordLaw_real_card, wordLaw_real_card, wordLaw_real_card]
  simpa only [Set.coe_ofPred, Nat.cast_add, add_div] using
    congrArg (fun k : ℕ => (k : ℝ) / (2 : ℝ) ^ n)
      (killed_endpoint_cdf_card n (⌊a⌋ + 1) ⌊v⌋ hH hX)

theorem scaled_polygonal_reflection (n : ℕ) (h : ℝ) (hh : 0 < h)
    (hsq : h ^ 2 = (n : ℝ)) (a v : ℝ) (ha : 0 < a) (hv : v < a) :
    (polygonalPathLaw 1 n h Shao.OQ4.RademacherCosine.law).real (upperJointSet a v) +
      (Measure.pi (fun _ : Fin n => Shao.OQ4.RademacherCosine.law)).real
        {p : Shao.Path n |
          (((2 * (⌊a * h⌋ + 1) - ⌊v * h⌋ : ℤ) : ℝ) / h) ≤ Shao.prefixSum p n / h} =
      (Measure.pi (fun _ : Fin n => Shao.OQ4.RademacherCosine.law)).real
        {p : Shao.Path n | Shao.prefixSum p n / h ≤ v} := by
  rw [upperJoint_real_prefix n h hh hsq Shao.OQ4.RademacherCosine.law a v]
  have he := closed_prefix_reflection n (a * h) (v * h) (mul_pos ha hh)
    (mul_lt_mul_of_pos_right hv hh)
  have htail : {p : Shao.Path n |
      (((2 * (⌊a * h⌋ + 1) - ⌊v * h⌋ : ℤ) : ℝ) / h) ≤ Shao.prefixSum p n / h} =
      {p : Shao.Path n | ((2 * (⌊a * h⌋ + 1) - ⌊v * h⌋ : ℤ) : ℝ) ≤ Shao.prefixSum p n} := by
    ext p
    exact div_le_div_iff_of_pos_right hh
  have hend : {p : Shao.Path n | Shao.prefixSum p n / h ≤ v} =
      {p : Shao.Path n | Shao.prefixSum p n ≤ v * h} := by
    ext p
    exact div_le_iff₀ hh
  rw [htail, hend]
  exact he

theorem scaled_reflected_cut_bounds (a v h : ℝ) (hh : 0 < h) :
    0 ≤ (((2 * (⌊a * h⌋ + 1) - ⌊v * h⌋ : ℤ) : ℝ) / h) - (2 * a - v) ∧
      (((2 * (⌊a * h⌋ + 1) - ⌊v * h⌋ : ℤ) : ℝ) / h) - (2 * a - v) ≤ 3 / h := by
  have ha0 := Int.floor_le (a * h)
  have ha1 := Int.lt_floor_add_one (a * h)
  have hv0 := Int.floor_le (v * h)
  have hv1 := Int.lt_floor_add_one (v * h)
  have he : (((2 * (⌊a * h⌋ + 1) - ⌊v * h⌋ : ℤ) : ℝ) / h) - (2 * a - v) =
      (2 * (⌊a * h⌋ : ℝ) + 2 - (⌊v * h⌋ : ℝ) - (2 * a - v) * h) / h := by
    push_cast
    field_simp [ne_of_gt hh]
    <;> ring
  rw [he]
  constructor
  · apply div_nonneg _ hh.le
    nlinarith
  · apply div_le_div_of_nonneg_right _ hh.le
    nlinarith

end Shao.C2.PolygonalRademacherReflection
