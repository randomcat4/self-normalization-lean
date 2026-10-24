import Shao.C2.InitialCompletionVariation
import Mathlib.MeasureTheory.Integral.Layercake

noncomputable section
namespace Shao.C2.EndpointCDFTransfer
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw

private theorem lower_set_cases (s : Set ℝ) (hs : IsLowerSet s) :
    s = ∅ ∨ s = Set.univ ∨ ∃ a : ℝ, s = Set.Iio a ∨ s = Set.Iic a := by
  classical
  by_cases he : s = ∅
  · exact Or.inl he
  by_cases hu : s = Set.univ
  · exact Or.inr (Or.inl hu)
  have hn : s.Nonempty := Set.nonempty_iff_ne_empty.mpr he
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b ∉ s := by simpa only [Set.eq_univ_iff_forall, not_forall] using hu
  have hB : BddAbove s := ⟨b, fun y hy => le_of_not_gt fun h => hb (hs h.le hy)⟩
  let a : ℝ := sSup s
  have hlo : Set.Iio a ⊆ s := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := (lt_csSup_iff hB hn).mp hx
    exact hs hxy.le hy
  have hhi : s ⊆ Set.Iic a := fun x hx => le_csSup hB hx
  refine Or.inr (Or.inr ⟨a, ?_⟩)
  by_cases ha : a ∈ s
  · exact Or.inr (Set.Subset.antisymm hhi (fun x hx => hs hx ha))
  · refine Or.inl (Set.Subset.antisymm ?_ hlo)
    intro x hx
    change x < a
    have hxle : x ≤ a := hhi hx
    exact lt_of_le_of_ne hxle (fun h : x = a => ha (h ▸ hx))

private theorem open_cdf_discrepancy
    (μ ρ : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    (δ : ℝ) (hCDF : ∀ x : ℝ, |μ.real (Set.Iic x) - ρ.real (Set.Iic x)| ≤ δ)
    (x : ℝ) :
    |μ.real (Set.Iio x) - ρ.real (Set.Iio x)| ≤ δ := by
  let r : ℕ → ℝ := fun n => x - 1 / (n + 1 : ℝ)
  have hr : Monotone r := by
    intro m n hmn
    dsimp [r]
    have hmn' : (m + 1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
    have hdiv := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < m + 1) hmn'
    linarith
  have hU : (⋃ n : ℕ, Set.Iic (r n)) = Set.Iio x := by
    ext y
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
      have hp : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
      change y ≤ x - 1 / (n + 1 : ℝ) at hn
      change y < x
      linarith
    · intro hy
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < x - y from sub_pos.mpr hy)
      apply Set.mem_iUnion.mpr
      exact ⟨n, by change y ≤ x - 1 / (n + 1 : ℝ); linarith⟩
  have hlim (κ : Measure ℝ) [IsProbabilityMeasure κ] :
      Tendsto (fun n : ℕ => κ.real (Set.Iic (r n))) atTop (𝓝 (κ.real (Set.Iio x))) := by
    have h := tendsto_measure_iUnion_atTop (fun i j hij => Set.Iic_subset_Iic.mpr (hr hij))
      (μ := κ)
    rw [hU] at h
    exact (ENNReal.continuousAt_toReal (measure_ne_top κ _)).tendsto.comp h
  exact le_of_tendsto ((hlim μ).sub (hlim ρ)).abs (Filter.Eventually.of_forall fun n => hCDF (r n))

theorem lower_set_discrepancy
    (μ ρ : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hCDF : ∀ x : ℝ, |μ.real (Set.Iic x) - ρ.real (Set.Iic x)| ≤ δ)
    (s : Set ℝ) (hs : IsLowerSet s) :
    |μ.real s - ρ.real s| ≤ δ := by
  rcases lower_set_cases s hs with he | hu | ⟨a, ho | hc⟩
  · simpa only [he, measureReal_empty, sub_self, abs_zero] using hδ
  · simpa only [hu, probReal_univ, sub_self, abs_zero] using hδ
  · rw [ho]
    exact open_cdf_discrepancy μ ρ δ hCDF a
  · rw [hc]
    exact hCDF a

theorem antitone_unit_expectation_error
    (μ ρ : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hCDF : ∀ x : ℝ, |μ.real (Set.Iic x) - ρ.real (Set.Iic x)| ≤ δ)
    (f : ℝ → ℝ) (hf : Antitone f) (hf0 : ∀ w, 0 ≤ f w) (hf1 : ∀ w, f w ≤ 1) :
    |(∫ w : ℝ, f w ∂μ) - ∫ w : ℝ, f w ∂ρ| ≤ δ := by
  have hi (κ : Measure ℝ) [IsProbabilityMeasure κ] : Integrable f κ := by
    refine (integrable_const (1 : ℝ)).mono' hf.measurable.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 w)]
      exact hf1 w
  let F : Measure ℝ → ℝ → ℝ := fun κ t => κ.real {w : ℝ | t ≤ f w}
  have hm (κ : Measure ℝ) [IsProbabilityMeasure κ] : Measurable (F κ) := by
    apply Antitone.measurable
    intro t t' htt
    exact measureReal_mono (fun w hw => htt.trans hw) (by finiteness)
  have hF (κ : Measure ℝ) [IsProbabilityMeasure κ] : IntegrableOn (F κ) (Set.Ioc 0 1) := by
    refine (integrableOn_const (by simp) : IntegrableOn (fun _ : ℝ => (1 : ℝ))
      (Set.Ioc 0 1)).mono' (hm κ).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      calc
        _ ≤ κ.real Set.univ := measureReal_mono (Set.subset_univ _) (by finiteness)
        _ = 1 := probReal_univ
  rw [(hi μ).integral_eq_integral_Ioc_meas_le
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hf1),
    (hi ρ).integral_eq_integral_Ioc_meas_le
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hf1)]
  change |(∫ t in Set.Ioc 0 1, F μ t) - ∫ t in Set.Ioc 0 1, F ρ t| ≤ δ
  rw [← integral_sub (hF μ) (hF ρ), ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ _ in Set.Ioc (0 : ℝ) 1, δ := by
      apply norm_integral_le_of_norm_le (integrableOn_const (by simp))
      exact Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs]
        exact lower_set_discrepancy μ ρ δ hδ hCDF {w : ℝ | t ≤ f w}
          (fun y z hzy hy => hy.trans (hf hzy))
    _ = δ := by simp

theorem initial_completion_expectation_error
    (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (μ ρ : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hCDF : ∀ x : ℝ, |μ.real (Set.Iic x) - ρ.real (Set.Iic x)| ≤ δ)
    (a : ℝ) :
    |(∫ w : ℝ, intervalCompletion ν a 0 1 w ∂μ) -
      ∫ w : ℝ, intervalCompletion ν a 0 1 w ∂ρ| ≤ 2 * δ := by
  let u : ℝ → ℝ := fun w => upperCompletion ν a 0 1 w
  let d : ℝ → ℝ := fun w => upperCompletion ν a 0 1 w - intervalCompletion ν a 0 1 w
  have hu : Antitone u := by
    intro w w' hww
    refine measureReal_mono ?_ (by finiteness)
    intro g hg t
    exact (bridgePath_mono 0 0 1 w w' le_rfl hww g t).trans_lt (hg t)
  have hd : Antitone d := fun w w' hww =>
    upper_deficit_antitone ν a 0 0 1 w w' le_rfl hww
  have hu0 (w : ℝ) : 0 ≤ u w := (completion_bounds ν a 0 1 w).1
  have hu1 (w : ℝ) : u w ≤ 1 := (completion_bounds ν a 0 1 w).2.1
  have hd0 (w : ℝ) : 0 ≤ d w := by
    dsimp [d]
    rw [upper_deficit_eq]
    exact measureReal_nonneg
  have hd1 (w : ℝ) : d w ≤ 1 := by
    dsimp [d]
    rw [upper_deficit_eq]
    calc
      _ ≤ ν.real Set.univ := measureReal_mono (Set.subset_univ _) (by finiteness)
      _ = 1 := probReal_univ
  have hi (κ : Measure ℝ) [IsProbabilityMeasure κ] (f : ℝ → ℝ) (hf : Antitone f)
      (hf0 : ∀ w, 0 ≤ f w) (hf1 : ∀ w, f w ≤ 1) : Integrable f κ := by
    refine (integrable_const (1 : ℝ)).mono' hf.measurable.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 w)]
      exact hf1 w
  have he : (fun w : ℝ => intervalCompletion ν a 0 1 w) = fun w => u w - d w := by
    funext w
    dsimp [u, d]
    ring
  rw [he, integral_sub (hi μ u hu hu0 hu1) (hi μ d hd hd0 hd1),
    integral_sub (hi ρ u hu hu0 hu1) (hi ρ d hd hd0 hd1)]
  have h1 := antitone_unit_expectation_error μ ρ δ hδ hCDF u hu hu0 hu1
  have h2 := antitone_unit_expectation_error μ ρ δ hδ hCDF d hd hd0 hd1
  have ht := norm_sub_le ((∫ w, u w ∂μ) - ∫ w, u w ∂ρ)
    ((∫ w, d w ∂μ) - ∫ w, d w ∂ρ)
  simp only [Real.norm_eq_abs] at ht
  have hr : ((∫ w, u w ∂μ) - ∫ w, d w ∂μ) -
      ((∫ w, u w ∂ρ) - ∫ w, d w ∂ρ) =
      ((∫ w, u w ∂μ) - ∫ w, u w ∂ρ) -
      ((∫ w, d w ∂μ) - ∫ w, d w ∂ρ) := by ring
  rw [hr]
  exact ht.trans (by linarith)

theorem initial_joint_expectation_error
    (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (μ ρ : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hCDF : ∀ x : ℝ, |μ.real (Set.Iic x) - ρ.real (Set.Iic x)| ≤ δ)
    (a v : ℝ) :
    |(∫ w : ℝ, (if w ≤ v then intervalCompletion ν a 0 1 w else 0) ∂μ) -
      ∫ w : ℝ, (if w ≤ v then intervalCompletion ν a 0 1 w else 0) ∂ρ| ≤ 2 * δ := by
  let u : ℝ → ℝ := fun w => if w ≤ v then upperCompletion ν a 0 1 w else 0
  let d : ℝ → ℝ := fun w => if w ≤ v then
    upperCompletion ν a 0 1 w - intervalCompletion ν a 0 1 w else 0
  have hu0 (w : ℝ) : 0 ≤ u w := by
    dsimp [u]
    split_ifs
    · exact (completion_bounds ν a 0 1 w).1
    · exact le_rfl
  have hu1 (w : ℝ) : u w ≤ 1 := by
    dsimp [u]
    split_ifs
    · exact (completion_bounds ν a 0 1 w).2.1
    · norm_num
  have hd0 (w : ℝ) : 0 ≤ d w := by
    dsimp [d]
    split_ifs
    · rw [upper_deficit_eq]
      exact measureReal_nonneg
    · exact le_rfl
  have hd1 (w : ℝ) : d w ≤ 1 := by
    dsimp [d]
    split_ifs
    · rw [upper_deficit_eq]
      calc
        _ ≤ ν.real Set.univ := measureReal_mono (Set.subset_univ _) (by finiteness)
        _ = 1 := probReal_univ
    · norm_num
  have hu : Antitone u := by
    intro w w' hww
    dsimp [u]
    by_cases hw : w ≤ v <;> by_cases hw' : w' ≤ v
    · simp only [if_pos hw, if_pos hw']
      refine measureReal_mono ?_ (by finiteness)
      intro g hg t
      exact (bridgePath_mono 0 0 1 w w' le_rfl hww g t).trans_lt (hg t)
    · simpa only [if_pos hw, if_neg hw'] using (completion_bounds ν a 0 1 w).1
    · exact False.elim (hw (hww.trans hw'))
    · simp only [if_neg hw, if_neg hw', le_refl]
  have hd : Antitone d := by
    intro w w' hww
    dsimp [d]
    by_cases hw : w ≤ v <;> by_cases hw' : w' ≤ v
    · simp only [if_pos hw, if_pos hw']
      exact upper_deficit_antitone ν a 0 0 1 w w' le_rfl hww
    · simpa only [d, if_pos hw, if_neg hw'] using hd0 w
    · exact False.elim (hw (hww.trans hw'))
    · simp only [if_neg hw, if_neg hw', le_refl]
  have hi (κ : Measure ℝ) [IsProbabilityMeasure κ] (f : ℝ → ℝ) (hf : Antitone f)
      (hf0 : ∀ w, 0 ≤ f w) (hf1 : ∀ w, f w ≤ 1) : Integrable f κ := by
    refine (integrable_const (1 : ℝ)).mono' hf.measurable.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 w)]
      exact hf1 w
  have he : (fun w : ℝ => if w ≤ v then intervalCompletion ν a 0 1 w else 0) =
      fun w => u w - d w := by
    funext w
    dsimp [u, d]
    split_ifs <;> ring
  rw [he, integral_sub (hi μ u hu hu0 hu1) (hi μ d hd hd0 hd1),
    integral_sub (hi ρ u hu hu0 hu1) (hi ρ d hd hd0 hd1)]
  have h1 := antitone_unit_expectation_error μ ρ δ hδ hCDF u hu hu0 hu1
  have h2 := antitone_unit_expectation_error μ ρ δ hδ hCDF d hd hd0 hd1
  have ht := norm_sub_le ((∫ w, u w ∂μ) - ∫ w, u w ∂ρ)
    ((∫ w, d w ∂μ) - ∫ w, d w ∂ρ)
  simp only [Real.norm_eq_abs] at ht
  have hr : ((∫ w, u w ∂μ) - ∫ w, d w ∂μ) -
      ((∫ w, u w ∂ρ) - ∫ w, d w ∂ρ) =
      ((∫ w, u w ∂μ) - ∫ w, u w ∂ρ) -
      ((∫ w, d w ∂μ) - ∫ w, d w ∂ρ) := by ring
  rw [hr]
  exact ht.trans (by linarith)

end Shao.C2.EndpointCDFTransfer
