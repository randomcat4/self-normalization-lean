import Shao.C2.InitialBrownianIdentity

noncomputable section
namespace Shao.C2.InitialCompletionVariation
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw

theorem closed_cutoff_variation_le (f : ℝ → ℝ)
    (hf0 : ∀ w, 0 ≤ f w) (hf1 : ∀ w, f w ≤ 1) (v : ℝ) :
    eVariationOn (fun w => if w ≤ v then f w else 0) Set.univ ≤
      eVariationOn f Set.univ + 1 := by
  let q : ℝ → ℝ := fun w => if w ≤ v then 1 else 0
  have hq : Antitone q := by
    intro x y hxy
    dsimp [q]
    split_ifs <;> linarith
  have hq0 (w : ℝ) : 0 ≤ q w := by dsimp [q]; split_ifs <;> norm_num
  have hq1 (w : ℝ) : q w ≤ 1 := by dsimp [q]; split_ifs <;> norm_num
  have hstep (x y : ℝ) (hxy : x ≤ y) :
      |(if x ≤ v then f x else 0) - (if y ≤ v then f y else 0)| ≤
        |f x - f y| + (q x - q y) := by
    dsimp [q]
    by_cases hx : x ≤ v <;> by_cases hy : y ≤ v
    · simp only [if_pos hx, if_pos hy, sub_self, add_zero, le_refl]
    · simp only [if_pos hx, if_neg hy, sub_zero, abs_of_nonneg (hf0 x)]
      linarith [hf1 x, abs_nonneg (f x - f y)]
    · exact False.elim (hx (hxy.trans hy))
    · simp only [if_neg hx, if_neg hy, sub_self, abs_zero, add_zero]
      exact abs_nonneg _
  apply iSup_le
  rintro ⟨n, w, hw, hmem⟩
  have ht (m : ℕ) :
      (∑ i ∈ Finset.range m, (q (w i) - q (w (i + 1)))) = q (w 0) - q (w m) := by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (edist (f (w i)) (f (w (i + 1))) +
          ENNReal.ofReal (q (w i) - q (w (i + 1)))) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [edist_dist, Real.dist_eq, edist_dist, Real.dist_eq,
        ← ENNReal.ofReal_add (abs_nonneg _) (sub_nonneg.mpr (hq (hw (Nat.le_succ i))))]
      apply ENNReal.ofReal_le_ofReal
      simpa only [abs_sub_comm] using hstep _ _ (hw (Nat.le_succ i))
    _ = (∑ i ∈ Finset.range n, edist (f (w i)) (f (w (i + 1)))) +
        ENNReal.ofReal (q (w 0) - q (w n)) := by
      rw [Finset.sum_add_distrib, ← ENNReal.ofReal_sum_of_nonneg, ht]
      intro i hi
      exact sub_nonneg.mpr (hq (hw (Nat.le_succ i)))
    _ ≤ eVariationOn f Set.univ + 1 := by
      apply add_le_add
      · simpa only [edist_comm] using
          (eVariationOn.sum_le (f := f) (n := n) hw (fun _ => Set.mem_univ _))
      have hb : q (w 0) - q (w n) ≤ 1 := by linarith [hq1 (w 0), hq0 (w n)]
      simpa using ENNReal.ofReal_le_ofReal hb

theorem initial_interval_measurable
    (ν : Measure BridgeNoise) [IsProbabilityMeasure ν] (a : ℝ) :
    Measurable (fun w : ℝ => intervalCompletion ν a 0 1 w) := by
  have hm := (measurable_measure_prodMk_right (μ := ν)
    (measurableSet_initialSurvival a)).ennreal_toReal
  convert hm using 1
  funext w
  change ν.real (strictInterval a 0 1 w) = ν.real {g | (g, w) ∈ initialSurvival a}
  congr 1
  ext g
  change g ∈ strictInterval a 0 1 w ↔ (g, w) ∈ initialSurvival a
  rw [mem_initialSurvival_iff]
  change ((∀ t : BridgeTime, bridgePath 0 1 w g t < a) ∧
    ∀ t : BridgeTime, -a < bridgePath 0 1 w g t) ↔
      ∀ t : BridgeTime, |bridgePath 0 1 w g t| < a
  simp only [abs_lt, forall_and, and_comm]

theorem initial_interval_integrable
    (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (a : ℝ) :
    Integrable (fun w : ℝ => intervalCompletion ν a 0 1 w) ρ := by
  refine (integrable_const (1 : ℝ)).mono' (initial_interval_measurable ν a).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun w => by
    rw [Real.norm_eq_abs, abs_of_nonneg (completion_bounds ν a 0 1 w).2.2.2.2.1]
    exact (completion_bounds ν a 0 1 w).2.2.2.2.2

theorem initial_joint_variation
    (ν : Measure BridgeNoise) [IsProbabilityMeasure ν] (a v : ℝ) :
    eVariationOn (fun w : ℝ => if w ≤ v then intervalCompletion ν a 0 1 w else 0)
      Set.univ ≤ 3 := by
  calc
    _ ≤ eVariationOn (fun w : ℝ => intervalCompletion ν a 0 1 w) Set.univ + 1 :=
      closed_cutoff_variation_le _ (fun w => (completion_bounds ν a 0 1 w).2.2.2.2.1)
        (fun w => (completion_bounds ν a 0 1 w).2.2.2.2.2) v
    _ ≤ 2 + 1 := add_le_add (initial_interval_variation ν a) le_rfl
    _ = 3 := by norm_num

theorem initial_joint_integrable
    (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (a v : ℝ) :
    Integrable (fun w : ℝ => if w ≤ v then intervalCompletion ν a 0 1 w else 0) ρ := by
  exact (initial_interval_integrable ν ρ a).indicator measurableSet_Iic

end Shao.C2.InitialCompletionVariation
