import Shao.C2.FiniteWalkReflectionCount
import Shao.OQ4.RademacherCosine
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section
namespace Shao.C2.RademacherReflectionProbability
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open Shao.C2.FiniteWalkReflection Shao.C2.FiniteWalkReflectionCount

def boolCoin : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

def wordLaw (n : ℕ) : Measure (Fin n → Bool) :=
  Measure.pi (fun _ : Fin n => boolCoin)

def realWord {n : ℕ} (w : Fin n → Bool) : Shao.Path n :=
  fun i => (boolStep (w i) : ℝ)

theorem boolCoin_isProbabilityMeasure : IsProbabilityMeasure boolCoin := by
  constructor
  norm_num [boolCoin]
  simpa only [one_div] using ENNReal.add_halves (1 : ℝ≥0∞)

theorem boolCoin_singleton (b : Bool) : boolCoin {b} = (1 / 2 : ℝ≥0∞) := by
  cases b <;> norm_num [boolCoin]

theorem boolCoin_map_step :
    boolCoin.map (fun b : Bool => (boolStep b : ℝ)) = Shao.OQ4.RademacherCosine.law := by
  have hm : Measurable (fun b : Bool => (boolStep b : ℝ)) := measurable_of_countable _
  rw [boolCoin, Measure.map_add _ _ hm,
    Measure.map_smul _ hm.aemeasurable, Measure.map_smul _ hm.aemeasurable,
    Measure.map_dirac, Measure.map_dirac]
  simp [boolStep, Shao.OQ4.RademacherCosine.law, Shao.OQ4.RademacherCosine.halfENNReal]

theorem wordLaw_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (wordLaw n) := by
  letI := boolCoin_isProbabilityMeasure
  dsimp only [wordLaw]
  infer_instance

theorem wordLaw_eq_count (n : ℕ) :
    wordLaw n = (1 / 2 : ℝ≥0∞) ^ n • (Measure.count : Measure (Fin n → Bool)) := by
  letI := boolCoin_isProbabilityMeasure
  apply Measure.ext_of_singleton
  intro w
  simp [wordLaw, Measure.pi_singleton, boolCoin_singleton]

theorem wordLaw_real_card (n : ℕ) (S : Set (Fin n → Bool)) :
    (wordLaw n).real S = (Nat.card S : ℝ) / (2 : ℝ) ^ n := by
  have hc : (Measure.count : Measure (Fin n → Bool)) S = (Nat.card S : ℝ≥0∞) := by
    rw [Measure.count_apply_finite S (Set.toFinite S),
      Nat.card_eq_card_finite_toFinset (Set.toFinite S)]
  rw [wordLaw_eq_count]
  change (((1 / 2 : ℝ≥0∞) ^ n * (Measure.count : Measure (Fin n → Bool)) S).toReal) = _
  rw [hc, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  norm_num [ENNReal.toReal_div, div_pow, div_eq_mul_inv, mul_comm]

theorem realWord_map_eq (n : ℕ) :
    (wordLaw n).map realWord =
      Measure.pi (fun _ : Fin n => Shao.OQ4.RademacherCosine.law) := by
  letI := boolCoin_isProbabilityMeasure
  have hm : Measurable (fun b : Bool => (boolStep b : ℝ)) := measurable_of_countable _
  letI : IsProbabilityMeasure (boolCoin.map (fun b : Bool => (boolStep b : ℝ))) := by
    rw [boolCoin_map_step]
    infer_instance
  change (Measure.pi (fun _ : Fin n => boolCoin)).map (fun w i => (boolStep (w i) : ℝ)) = _
  simpa only [boolCoin_map_step] using
    (Measure.pi_map_pi (μ := fun _ : Fin n => boolCoin)
      (f := fun _ : Fin n => fun b : Bool => (boolStep b : ℝ)) (fun _ => hm.aemeasurable))

theorem realWord_prefix {n : ℕ} (w : Fin n → Bool) (k : ℕ) :
    Shao.prefixSum (realWord w) k = (walkPrefix w k : ℝ) := by
  classical
  induction k with
  | zero => simp [Shao.prefixSum, walkPrefix]
  | succ k ih =>
    by_cases hk : k < n
    · have hs : Finset.univ.filter (fun i : Fin n => i.val < k + 1) =
          insert ⟨k, hk⟩ (Finset.univ.filter (fun i : Fin n => i.val < k)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hi
          by_cases he : i.val = k
          · exact Or.inl (Fin.ext he)
          · exact Or.inr (by omega)
        · rintro (he | hi)
          · have hv := congrArg Fin.val he
            change i.val = k at hv
            omega
          · omega
      have hnot : (⟨k, hk⟩ : Fin n) ∉ Finset.univ.filter (fun i : Fin n => i.val < k) := by simp
      rw [Shao.prefixSum, hs, Finset.sum_insert hnot]
      change realWord w ⟨k, hk⟩ + Shao.prefixSum (realWord w) k = _
      rw [ih]
      simp only [realWord, walkPrefix, dif_pos hk, Int.cast_add]
      ring
    · have hs : Finset.univ.filter (fun i : Fin n => i.val < k + 1) =
          Finset.univ.filter (fun i : Fin n => i.val < k) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hi := i.is_lt
        omega
      rw [Shao.prefixSum, hs]
      change Shao.prefixSum (realWord w) k = _
      rw [ih]
      simp only [walkPrefix, dif_neg hk, add_zero]

theorem killed_endpoint_cdf_probability (n : ℕ) (h x : ℤ) (hh : 0 < h) (hx : x < h) :
    (Measure.pi (fun _ : Fin n => Shao.OQ4.RademacherCosine.law)).real
        {a : Shao.Path n | (∀ k : ℕ, k ≤ n → Shao.prefixSum a k < (h : ℝ)) ∧
          Shao.prefixSum a n ≤ (x : ℝ)} +
      (Measure.pi (fun _ : Fin n => Shao.OQ4.RademacherCosine.law)).real
        {a : Shao.Path n | ((2 * h - x : ℤ) : ℝ) ≤ Shao.prefixSum a n} =
      (Measure.pi (fun _ : Fin n => Shao.OQ4.RademacherCosine.law)).real
        {a : Shao.Path n | Shao.prefixSum a n ≤ (x : ℝ)} := by
  have hm (k : ℕ) : Measurable (fun a : Shao.Path n => Shao.prefixSum a k) := by
    unfold Shao.prefixSum
    fun_prop
  have hs : MeasurableSet {a : Shao.Path n | ∀ k : ℕ, k ≤ n → Shao.prefixSum a k < (h : ℝ)} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun hk =>
      measurableSet_lt (hm k) measurable_const
  have h0 : MeasurableSet {a : Shao.Path n |
      (∀ k : ℕ, k ≤ n → Shao.prefixSum a k < (h : ℝ)) ∧ Shao.prefixSum a n ≤ (x : ℝ)} :=
    hs.inter (measurableSet_le (hm n) (measurable_const (a := (x : ℝ))))
  have h1 : MeasurableSet {a : Shao.Path n | ((2 * h - x : ℤ) : ℝ) ≤ Shao.prefixSum a n} :=
    measurableSet_le measurable_const (hm n)
  have h2 : MeasurableSet {a : Shao.Path n | Shao.prefixSum a n ≤ (x : ℝ)} :=
    measurableSet_le (hm n) measurable_const
  have hevent (S : Set (Shao.Path n)) (hS : MeasurableSet S) :
      (Measure.pi (fun _ : Fin n => Shao.OQ4.RademacherCosine.law)).real S =
        (wordLaw n).real (realWord ⁻¹' S) := by
    rw [← realWord_map_eq n]
    change (((wordLaw n).map realWord) S).toReal = _
    rw [Measure.map_apply (measurable_of_countable realWord) hS]
    rfl
  have hp0 : realWord ⁻¹' {a : Shao.Path n |
      (∀ k : ℕ, k ≤ n → Shao.prefixSum a k < (h : ℝ)) ∧ Shao.prefixSum a n ≤ (x : ℝ)} =
      {w : Fin n → Bool | (∀ k : ℕ, k ≤ n → walkPrefix w k < h) ∧ walkPrefix w n ≤ x} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_setOf_eq, realWord_prefix, Int.cast_lt, Int.cast_le]
  have hp1 : realWord ⁻¹' {a : Shao.Path n | ((2 * h - x : ℤ) : ℝ) ≤ Shao.prefixSum a n} =
      {w : Fin n → Bool | 2 * h - x ≤ walkPrefix w n} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_setOf_eq, realWord_prefix, Int.cast_le]
  have hp2 : realWord ⁻¹' {a : Shao.Path n | Shao.prefixSum a n ≤ (x : ℝ)} =
      {w : Fin n → Bool | walkPrefix w n ≤ x} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_setOf_eq, realWord_prefix, Int.cast_le]
  rw [hevent _ h0, hevent _ h1, hevent _ h2, hp0, hp1, hp2,
    wordLaw_real_card, wordLaw_real_card, wordLaw_real_card]
  simpa only [Set.coe_ofPred, Nat.cast_add, add_div] using
    congrArg (fun k : ℕ => (k : ℝ) / (2 : ℝ) ^ n) (killed_endpoint_cdf_card n h x hh hx)

end Shao.C2.RademacherReflectionProbability
