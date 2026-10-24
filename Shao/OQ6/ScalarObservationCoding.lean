import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

namespace Shao.OQ6.ScalarObservationCoding

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

noncomputable def baseFourIndicatorCode
    {X : Type*} (A : ℕ → Set X) (x : X) : ℝ :=
  ∑' k : ℕ,
    (if x ∈ A k then (2 : ℝ) else 1) / (4 : ℝ) ^ (k + 1)

def baseFourOneSet (k : ℕ) : Set ℝ :=
  ⋃ m : ℤ,
    Set.Ico
      (((4 : ℝ) * (m : ℝ) + 2) / (4 : ℝ) ^ (k + 1))
      (((4 : ℝ) * (m : ℝ) + 3) / (4 : ℝ) ^ (k + 1))

private theorem base_four_code_numerical_spec
    {X : Type*} (A : ℕ → Set X) (x : X) :
    Summable (fun k : ℕ =>
      (if x ∈ A k then (2 : ℝ) else 1) / (4 : ℝ) ^ (k + 1)) ∧
    ((1 / 3 : ℝ) ≤ baseFourIndicatorCode A x ∧
      baseFourIndicatorCode A x ≤ (2 / 3 : ℝ)) ∧
    (∀ k : ℕ, x ∈ A k ↔
      baseFourIndicatorCode A x ∈ baseFourOneSet k) := by
  classical
  let d : ℕ → ℝ := fun j => if x ∈ A j then (2 : ℝ) else 1
  let f : ℕ → ℝ := fun j => d j / (4 : ℝ) ^ (j + 1)
  have hgeom : HasSum (fun j : ℕ => (1 : ℝ) / 4 ^ (j + 1))
      (1 / 3 : ℝ) := by
    have hbase : HasSum (fun j : ℕ => (1 / 4 : ℝ) ^ j)
        (1 - (1 / 4 : ℝ))⁻¹ :=
      hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
    convert hbase.mul_left (1 / 4 : ℝ) using 1
    · funext j
      simp [one_div, pow_succ, mul_comm, mul_left_comm, mul_assoc]
    · norm_num
  have hgeomTwo : HasSum (fun j : ℕ => (2 : ℝ) / 4 ^ (j + 1))
      (2 / 3 : ℝ) := by
    convert hgeom.mul_left (2 : ℝ) using 1
    · funext j
      ring
    · norm_num
  have hweighted (b : ℕ → ℝ)
      (hb : ∀ j : ℕ, (1 : ℝ) ≤ b j ∧ b j ≤ 2) :
      Summable (fun j : ℕ => b j / (4 : ℝ) ^ (j + 1)) ∧
      ((1 / 3 : ℝ) ≤ ∑' j : ℕ, b j / (4 : ℝ) ^ (j + 1)) ∧
      (∑' j : ℕ, b j / (4 : ℝ) ^ (j + 1)) ≤ (2 / 3 : ℝ) := by
    have hp (j : ℕ) : 0 < (4 : ℝ) ^ (j + 1) := pow_pos (by norm_num) _
    have hl (j : ℕ) : (1 : ℝ) / 4 ^ (j + 1) ≤
        b j / (4 : ℝ) ^ (j + 1) :=
      (div_le_div_iff_of_pos_right (hp j)).2 (hb j).1
    have hu (j : ℕ) : b j / (4 : ℝ) ^ (j + 1) ≤
        (2 : ℝ) / 4 ^ (j + 1) :=
      (div_le_div_iff_of_pos_right (hp j)).2 (hb j).2
    have hs : Summable (fun j : ℕ => b j / (4 : ℝ) ^ (j + 1)) :=
      Summable.of_nonneg_of_le
        (fun j => div_nonneg (le_trans (by norm_num) (hb j).1) (hp j).le)
        hu hgeomTwo.summable
    refine ⟨hs, ?_, ?_⟩
    · have hle := Summable.tsum_le_tsum hl hgeom.summable hs
      simpa only [hgeom.tsum_eq] using hle
    · have hle := Summable.tsum_le_tsum hu hs hgeomTwo.summable
      simpa only [hgeomTwo.tsum_eq] using hle
  have hd (j : ℕ) : (1 : ℝ) ≤ d j ∧ d j ≤ 2 := by
    dsimp only [d]
    split_ifs <;> norm_num
  have hmain := hweighted d hd
  have hs : Summable f := hmain.1
  have hrange : (1 / 3 : ℝ) ≤ baseFourIndicatorCode A x ∧
      baseFourIndicatorCode A x ≤ (2 / 3 : ℝ) := hmain.2
  refine ⟨hs, hrange, ?_⟩
  intro k
  let di : ℕ → ℤ := fun j => if x ∈ A j then (2 : ℤ) else 1
  let q : ℤ :=
    ∑ j ∈ Finset.range k, di j * (4 : ℤ) ^ (k - (j + 1))
  let tail : ℝ :=
    ∑' r : ℕ, d (k + 1 + r) / (4 : ℝ) ^ (r + 1)
  have hdi (j : ℕ) : (di j : ℝ) = d j := by
    dsimp only [di, d]
    split_ifs <;> norm_num
  have htail := hweighted (fun r : ℕ => d (k + 1 + r))
    (fun r => hd (k + 1 + r))
  have htlo : (1 / 3 : ℝ) ≤ tail := htail.2.1
  have hthi : tail ≤ (2 / 3 : ℝ) := htail.2.2
  have hsplit : baseFourIndicatorCode A x =
      (∑ j ∈ Finset.range (k + 1), f j) +
        ∑' r : ℕ, f (r + (k + 1)) := by
    exact (Summable.sum_add_tsum_nat_add (k + 1) hs).symm
  have hqcast : (q : ℝ) =
      ∑ j ∈ Finset.range k, (di j : ℝ) * (4 : ℝ) ^ (k - (j + 1)) := by
    simp only [q, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  have hfinite : (4 : ℝ) ^ (k + 1) *
      (∑ j ∈ Finset.range (k + 1), f j) = 4 * (q : ℝ) + d k := by
    rw [Finset.sum_range_succ, mul_add]
    have hprefix : (4 : ℝ) ^ (k + 1) *
        (∑ j ∈ Finset.range k, f j) = 4 * (q : ℝ) := by
      rw [hqcast, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hexp : k + 1 = (j + 1) + (k - (j + 1)) + 1 := by omega
      have hpj : (4 : ℝ) ^ (j + 1) ≠ 0 :=
        ne_of_gt (pow_pos (by norm_num) _)
      dsimp only [f]
      rw [hdi, hexp, pow_add, pow_add, pow_one]
      field_simp
      <;> ring
    have hlast : (4 : ℝ) ^ (k + 1) * f k = d k := by
      dsimp only [f]
      have hp : (4 : ℝ) ^ (k + 1) ≠ 0 :=
        ne_of_gt (pow_pos (by norm_num) _)
      field_simp
    rw [hprefix, hlast]
  have htailscale : (4 : ℝ) ^ (k + 1) *
      (∑' r : ℕ, f (r + (k + 1))) = tail := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro r
    have hexp : r + (k + 1) + 1 = (k + 1) + (r + 1) := by omega
    have hp : (4 : ℝ) ^ (k + 1) ≠ 0 :=
      ne_of_gt (pow_pos (by norm_num) _)
    dsimp only [f]
    rw [hexp, pow_add]
    have hindex : r + (k + 1) = k + 1 + r := by omega
    rw [hindex]
    field_simp
    <;> ring
  have hscaled : (4 : ℝ) ^ (k + 1) * baseFourIndicatorCode A x =
      4 * (q : ℝ) + d k + tail := by
    rw [hsplit, mul_add, hfinite, htailscale]
  have hp : 0 < (4 : ℝ) ^ (k + 1) := pow_pos (by norm_num) _
  constructor
  · intro hx
    have hdk : d k = 2 := by simp only [d, if_pos hx]
    change baseFourIndicatorCode A x ∈
      ⋃ m : ℤ, Set.Ico
        (((4 : ℝ) * (m : ℝ) + 2) / (4 : ℝ) ^ (k + 1))
        (((4 : ℝ) * (m : ℝ) + 3) / (4 : ℝ) ^ (k + 1))
    apply Set.mem_iUnion.mpr
    refine ⟨q, ?_⟩
    constructor
    · apply (div_le_iff₀ hp).2
      rw [hdk] at hscaled
      nlinarith
    · apply (lt_div_iff₀ hp).2
      rw [hdk] at hscaled
      nlinarith
  · intro hc
    by_contra hx
    have hdk : d k = 1 := by simp only [d, if_neg hx]
    change baseFourIndicatorCode A x ∈
      ⋃ m : ℤ, Set.Ico
        (((4 : ℝ) * (m : ℝ) + 2) / (4 : ℝ) ^ (k + 1))
        (((4 : ℝ) * (m : ℝ) + 3) / (4 : ℝ) ^ (k + 1)) at hc
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hc
    have hmlo := (div_le_iff₀ hp).1 hm.1
    have hmhi := (lt_div_iff₀ hp).1 hm.2
    rw [hdk] at hscaled
    have hmqlt : (m : ℝ) < (q : ℝ) := by nlinarith
    have hmq : m < q := by exact_mod_cast hmqlt
    have hnext : m + 1 ≤ q := by omega
    have hnextR : (m : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hnext
    nlinarith

private theorem measurable_base_four_indicator_code
    {X : Type*} [MeasurableSpace X]
    (A : ℕ → Set X)
    (hA : ∀ k : ℕ, MeasurableSet (A k)) :
    Measurable (baseFourIndicatorCode A) := by
  classical
  change Measurable (fun x : X =>
    ∑' k : ℕ,
      (if x ∈ A k then (2 : ℝ) else 1) / (4 : ℝ) ^ (k + 1))
  apply Measurable.tsum
  intro k
  have hAk : MeasurableSet (A k) := hA k
  simpa only [ite_div] using
    (Measurable.ite (p := fun x : X => x ∈ A k) hAk
      (measurable_const : Measurable (fun _ : X =>
        (2 : ℝ) / (4 : ℝ) ^ (k + 1)))
      (measurable_const : Measurable (fun _ : X =>
        (1 : ℝ) / (4 : ℝ) ^ (k + 1))))

private theorem measurableSet_base_four_one_set (k : ℕ) :
    MeasurableSet (baseFourOneSet k) := by
  unfold baseFourOneSet
  exact MeasurableSet.iUnion (fun _ : ℤ => measurableSet_Ico)

theorem base_four_indicator_code_spec
    {X : Type*} [mX : MeasurableSpace X]
    (A : ℕ → Set X)
    (hA : ∀ k : ℕ, MeasurableSet (A k))
    (hgen : MeasurableSpace.generateFrom (Set.range A) = mX) :
    let c : X → ℝ := baseFourIndicatorCode A
    (∀ x : X,
      Summable (fun k : ℕ =>
        (if x ∈ A k then (2 : ℝ) else 1) / (4 : ℝ) ^ (k + 1))) ∧
    (∀ x : X, (1 / 3 : ℝ) ≤ c x ∧ c x ≤ (2 / 3 : ℝ)) ∧
    Measurable c ∧
    (∀ k : ℕ, MeasurableSet (baseFourOneSet k)) ∧
    (∀ k : ℕ, A k = c ⁻¹' baseFourOneSet k) ∧
    MeasurableSpace.comap c (borel ℝ) = mX := by
  dsimp only
  have hm : Measurable (baseFourIndicatorCode A) :=
    measurable_base_four_indicator_code A hA
  have hdecode (k : ℕ) :
      A k = (baseFourIndicatorCode A) ⁻¹' baseFourOneSet k := by
    ext x
    exact (base_four_code_numerical_spec A x).2.2 k
  refine ⟨(fun x => (base_four_code_numerical_spec A x).1),
    (fun x => (base_four_code_numerical_spec A x).2.1),
    hm, measurableSet_base_four_one_set, hdecode, ?_⟩
  apply le_antisymm
  · exact hm.comap_le
  · rw [← hgen]
    apply MeasurableSpace.generateFrom_le
    intro s hs
    obtain ⟨k, rfl⟩ := hs
    exact MeasurableSpace.measurableSet_comap.mpr
      ⟨baseFourOneSet k, measurableSet_base_four_one_set k, (hdecode k).symm⟩

private theorem measurable_real_eq_of_code_fiber
    {X : Type*} [mX : MeasurableSpace X]
    (c : X → ℝ)
    (hcomap : MeasurableSpace.comap c (borel ℝ) = mX)
    (f : X → ℝ) (hf : Measurable f)
    {x y : X} (hxy : c x = c y) :
    f x = f y := by
  classical
  have hle (a b : X) (hab : c a = c b) : f a ≤ f b := by
    by_contra hnot
    have hlt : f b < f a := lt_of_not_ge hnot
    let s : Set X := f ⁻¹' Set.Iio (f a)
    have hs : MeasurableSet[MeasurableSpace.comap c (borel ℝ)] s := by
      rw [hcomap]
      exact hf measurableSet_Iio
    obtain ⟨B, hB, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hs
    have hbB : c b ∈ B := by
      change b ∈ c ⁻¹' B
      rw [hpre]
      exact hlt
    have haB : c a ∈ B := by
      rw [hab]
      exact hbB
    have haS : a ∈ s := by
      rw [← hpre]
      exact haB
    exact (lt_irrefl (f a)) haS
  exact le_antisymm (hle x y hxy) (hle y x hxy.symm)

private theorem unit_open_interval_volume_spec :
    let lambda01 : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
    IsProbabilityMeasure lambda01 ∧
    (∀ u : ℝ, lambda01 ({u} : Set ℝ) = 0) := by
  dsimp only
  refine ⟨⟨?_⟩, ?_⟩
  · rw [Measure.restrict_apply_univ, Real.volume_Ioo]
    norm_num
  · intro u
    apply le_antisymm _ bot_le
    calc
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)) ({u} : Set ℝ)
          ≤ (volume : Measure ℝ) ({u} : Set ℝ) :=
        Measure.restrict_apply_le _ _
      _ = 0 := by simp

private theorem product_code_level_null_of_snd_fiber
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (lambda01 : Measure ℝ) [IsProbabilityMeasure lambda01]
    (hLambda : ∀ u : ℝ, lambda01 ({u} : Set ℝ) = 0)
    (c : (Ω × ℝ) → ℝ)
    (hfiber : ∀ z z' : Ω × ℝ, c z = c z' → z.2 = z'.2)
    (t : ℝ) :
    (μ.prod lambda01) ({z : Ω × ℝ | c z = t}) = 0 := by
  classical
  by_cases hn : Set.Nonempty {z : Ω × ℝ | c z = t}
  · obtain ⟨z0, hz0⟩ := hn
    have hsub : {z : Ω × ℝ | c z = t} ⊆
        Set.univ ×ˢ ({z0.2} : Set ℝ) := by
      intro z hz
      refine ⟨Set.mem_univ z.1, ?_⟩
      exact hfiber z z0 (hz.trans hz0.symm)
    apply le_antisymm _ bot_le
    calc
      (μ.prod lambda01) ({z : Ω × ℝ | c z = t})
          ≤ (μ.prod lambda01) (Set.univ ×ˢ ({z0.2} : Set ℝ)) :=
        measure_mono hsub
      _ = μ Set.univ * lambda01 ({z0.2} : Set ℝ) := Measure.prod_prod _ _
      _ = 0 := by rw [hLambda]; simp
  · have he : {z : Ω × ℝ | c z = t} = ∅ := by
      ext z
      constructor
      · intro hz
        exact (hn ⟨z, hz⟩).elim
      · intro hz
        exact False.elim hz
    rw [he, measure_empty]

theorem countable_uniform_augmented_base_four_code
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    let H : ℕ → Set (Ω × ℝ) :=
      MeasurableSpace.natGeneratingSequence (Ω × ℝ)
    let c : (Ω × ℝ) → ℝ := baseFourIndicatorCode H
    let lambda01 : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
    let ν : Measure (Ω × ℝ) := μ.prod lambda01
    IsProbabilityMeasure lambda01 ∧
    IsProbabilityMeasure ν ∧
    (∀ z : Ω × ℝ,
      Summable (fun k : ℕ =>
        (if z ∈ H k then (2 : ℝ) else 1) / (4 : ℝ) ^ (k + 1))) ∧
    (∀ z : Ω × ℝ, (1 / 3 : ℝ) ≤ c z ∧ c z ≤ (2 / 3 : ℝ)) ∧
    Measurable c ∧
    (∀ k : ℕ, MeasurableSet (baseFourOneSet k)) ∧
    (∀ k : ℕ, H k = c ⁻¹' baseFourOneSet k) ∧
    MeasurableSpace.comap c (borel ℝ) =
      (inferInstance : MeasurableSpace (Ω × ℝ)) ∧
    (∀ z z' : Ω × ℝ, c z = c z' → z.2 = z'.2) ∧
    (∀ t : ℝ, ν ({z : Ω × ℝ | c z = t}) = 0) := by
  dsimp only
  let H : ℕ → Set (Ω × ℝ) :=
    MeasurableSpace.natGeneratingSequence (Ω × ℝ)
  let c : (Ω × ℝ) → ℝ := baseFourIndicatorCode H
  let lambda01 : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
  let ν : Measure (Ω × ℝ) := μ.prod lambda01
  have hH (k : ℕ) : MeasurableSet (H k) :=
    MeasurableSpace.measurableSet_natGeneratingSequence (α := Ω × ℝ) k
  have hHgen : MeasurableSpace.generateFrom (Set.range H) =
      (inferInstance : MeasurableSpace (Ω × ℝ)) :=
    MeasurableSpace.generateFrom_natGeneratingSequence (Ω × ℝ)
  obtain ⟨hs, hrange, hc, hE, hdecode, hcomap⟩ :=
    base_four_indicator_code_spec H hH hHgen
  have hu : IsProbabilityMeasure lambda01 ∧
      (∀ u : ℝ, lambda01 ({u} : Set ℝ) = 0) :=
    unit_open_interval_volume_spec
  letI : IsProbabilityMeasure lambda01 := hu.1
  have hν : IsProbabilityMeasure ν := by
    dsimp only [ν]
    infer_instance
  have hfiber : ∀ z z' : Ω × ℝ, c z = c z' → z.2 = z'.2 := by
    intro z z' hzz
    exact measurable_real_eq_of_code_fiber c hcomap Prod.snd measurable_snd hzz
  refine ⟨hu.1, hν, hs, hrange, hc, hE, hdecode, hcomap, hfiber, ?_⟩
  intro t
  exact product_code_level_null_of_snd_fiber μ lambda01 hu.2 c hfiber t

end

end Shao.OQ6.ScalarObservationCoding
