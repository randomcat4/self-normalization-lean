import Shao.OQ5.P35.ConditionalNumerator
import Shao.OQ5.P35.ConditionalStudentizer
import Shao.OQ5.P35.RareLowerBound
import Shao.OQ5.P35.ThresholdScales
import Mathlib.Probability.Moments.Variance

/-!
# Actual sparse Studentized tail lower bounds for p35

Source: original p35 §§6–7, formulas (18)–(19). Chebyshev, Markov
and a union bound concern the actual numerator and true Studentizer under
the normalized rare-event restriction of the one fixed sample law.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

-- These two probability estimates were supplied by the lead and are reused here.
private theorem numerator_bad_prob_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : MemLp f 2 μ) (k C : ℝ) (hk : 0 < k)
    (hm : 3 * k / 4 ≤ ∫ ω, f ω ∂μ) (hv : variance f μ ≤ C) :
    μ.real {ω | f ω < k / 2} ≤ 16 * C / k ^ 2 := by
  have hc : 0 < k / 4 := by positivity
  have hdev := meas_ge_le_variance_div_sq hf hc
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdev
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))] at hreal
  calc
    μ.real {ω | f ω < k / 2} ≤ μ.real {ω | k / 4 ≤ |f ω - ∫ x, f x ∂μ|} := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro ω hω
      have ha := neg_le_abs (f ω - ∫ x, f x ∂μ)
      change k / 4 ≤ |f ω - ∫ x, f x ∂μ|
      change f ω < k / 2 at hω
      linarith
    _ ≤ variance f μ / (k / 4) ^ 2 := hreal
    _ ≤ C / (k / 4) ^ 2 := div_le_div_of_nonneg_right hv (sq_nonneg _)
    _ = 16 * C / k ^ 2 := by ring

private theorem markov_strict_prob_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hn : 0 ≤ᵐ[μ] f) (c C : ℝ) (hc : 0 < c)
    (hb : (∫ ω, f ω ∂μ) ≤ C) : μ.real {ω | c < f ω} ≤ C / c := by
  have hm := mul_meas_ge_le_integral_of_nonneg hn hf c
  calc
    μ.real {ω | c < f ω} ≤ μ.real {ω | c ≤ f ω} :=
      measureReal_mono (fun ω h => (show c ≤ f ω from le_of_lt h))
    _ ≤ (∫ ω, f ω ∂μ) / c := (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hm)
    _ ≤ C / c := div_le_div_of_nonneg_right hb hc.le

private theorem quotient_lower (k N R : ℝ) (hk : 0 < k)
    (hN : k/2 ≤ N) (hR : 0 < R) (hupper : R ≤ 4*k^(2/5 : ℝ)) :
    k^(3/5 : ℝ)/8 ≤ N/R := by
  have hp : 0 < k^(2/5 : ℝ) := Real.rpow_pos_of_pos hk _
  have he : k^(3/5 : ℝ) * k^(2/5 : ℝ) = k := by
    rw [← Real.rpow_add hk]
    norm_num
  apply (le_div_iff₀ hR).mpr
  have hmul := mul_le_mul_of_nonneg_left hupper
    (show 0 ≤ k^(3/5 : ℝ)/8 by positivity)
  nlinarith

private theorem joint_probability_lower {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (N R Q : Ω → ℝ)
    (hNm : Measurable N) (hRm : Measurable R)
    (hN2 : MemLp N 2 μ) (hQ : Integrable Q μ)
    (hRQ : ∀ ω, R ω ^ 2 = Q ω) (hRp : ∀ᵐ ω ∂μ, 0 < R ω)
    (k r Cn Cr : ℝ) (hk : 0 < k) (hr : 0 < r)
    (hm : 3*k/4 ≤ ∫ ω, N ω ∂μ) (hv : variance N μ ≤ Cn)
    (hb : (∫ ω, Q ω ∂μ) ≤ Cr) :
    1-16*Cn/k^2-Cr/r^2 ≤
      μ.real {ω | k/2 ≤ N ω ∧ 0 < R ω ∧ R ω ≤ r} := by
  let E : Set Ω := {ω | k/2 ≤ N ω ∧ 0 < R ω ∧ R ω ≤ r}
  have hEm : MeasurableSet E :=
    (measurableSet_le measurable_const hNm).inter
      ((measurableSet_lt measurable_const hRm).inter (measurableSet_le hRm measurable_const))
  have hbadN := numerator_bad_prob_le hN2 k Cn hk hm hv
  have hQp : 0 ≤ᵐ[μ] Q := Filter.Eventually.of_forall (fun ω => by rw [← hRQ]; positivity)
  have hbadR : μ.real {ω | r < R ω} ≤ Cr/r^2 := by
    apply le_trans (measureReal_mono ?_) (markov_strict_prob_le hQ hQp (r^2) Cr (by positivity) hb)
    intro ω hω
    change r^2 < Q ω
    rw [← hRQ]
    change r < R ω at hω
    nlinarith
  have hzero : μ.real {ω | ¬ 0 < R ω} = 0 := by
    change (μ {ω | ¬ 0 < R ω}).toReal = 0
    rw [ae_iff.mp hRp]
    rfl
  have hsub : Eᶜ ⊆ {ω | N ω < k/2} ∪ ({ω | ¬ 0 < R ω} ∪ {ω | r < R ω}) := by
    intro ω hω
    change ¬ (k/2 ≤ N ω ∧ 0 < R ω ∧ R ω ≤ r) at hω
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    by_cases h1 : k/2 ≤ N ω
    · right
      by_cases h2 : 0 < R ω
      · right
        exact lt_of_not_ge (fun h3 => hω ⟨h1,h2,h3⟩)
      · exact Or.inl h2
    · exact Or.inl (lt_of_not_ge h1)
  have hcompl : μ.real Eᶜ ≤ 16*Cn/k^2+Cr/r^2 := by
    have h1 := measureReal_union_le (μ := μ)
      {ω | N ω < k/2} ({ω | ¬ 0 < R ω} ∪ {ω | r < R ω})
    have h2 := measureReal_union_le (μ := μ) {ω | ¬ 0 < R ω} {ω | r < R ω}
    have h3 := measureReal_mono (μ := μ) hsub
    linarith
  have htotal := probReal_add_probReal_compl (μ := μ) hEm
  change 1-16*Cn/k^2-Cr/r^2 ≤ μ.real E
  linarith

private theorem scale_pos_for_tail (j : ℕ) : 0 < categoryScale j :=
  lt_of_lt_of_le (by norm_num) (categoryScale_one_le j)

private theorem rare_size_three (j : ℕ) (hj : 1 ≤ j) : 3 ≤ rareSampleSize j := by
  have hk : 4 ≤ targetCategoryCount j := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    unfold targetCategoryCount
    rw [pow_succ]
    have : 1 ≤ 4^l := Nat.one_le_pow l 4 (by omega)
    omega
  unfold rareSampleSize
  have h := Nat.pow_le_pow_left hk 4
  norm_num at h
  omega

private theorem conditional_good_transfer {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (A G T : Set Ω)
    (hA : MeasurableSet A) (hsub : G ⊆ T) :
    (cond μ A).real G * μ.real A ≤ μ.real T := by
  have h := congrArg ENNReal.toReal (cond_mul_eq_inter hA G μ)
  simp only [ENNReal.toReal_mul] at h
  calc
    (cond μ A).real G * μ.real A = μ.real (A ∩ G) := h
    _ ≤ μ.real T := measureReal_mono (Set.inter_subset_right.trans hsub)

private theorem probability_le_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω) : μ.real A ≤ 1 := by
  simpa only [probReal_univ] using (measureReal_mono (μ := μ) (Set.subset_univ A))

private theorem error_tendsto_zero (Cn Cr : ℝ) :
    Tendsto (fun j : ℕ => 16*Cn/categoryScale j^2+
      Cr/(4*categoryScale j^(2/5 : ℝ))^2) atTop (nhds 0) := by
  have hk : Tendsto categoryScale atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)
  have h1 : Tendsto (fun j => (categoryScale j)^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hk
  have h2 : Tendsto (fun j => (4*categoryScale j^(2/5 : ℝ))^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 4)
        ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2/5)).comp hk))
  simpa using (tendsto_const_nhds.div_atTop h1).add (tendsto_const_nhds.div_atTop h2)

/-- The numerator signal and the positive, bounded actual Studentizer occur together. -/
def jointGoodEvent (j : ℕ) : Set (ℕ → ℝ) :=
  {ω | categoryScale j / 2 ≤ sampleCenteredNumerator (rareSampleSize j) ω ∧
    0 < sampleStudentizer (rareSampleSize j) ω ∧
    sampleStudentizer (rareSampleSize j) ω ≤ 4 * categoryScale j ^ (2 / 5 : ℝ)}

private theorem measurable_centeredNumerator_for_tail (n : ℕ) :
    Measurable (sampleCenteredNumerator n) :=
  ((measurable_sampleU n).sub measurable_const).const_mul _

theorem measurableSet_jointGoodEvent (j : ℕ) : MeasurableSet (jointGoodEvent j) :=
  (measurableSet_le measurable_const (measurable_centeredNumerator_for_tail _)).inter
    ((measurableSet_lt measurable_const (measurable_sampleStudentizer _)).inter
      (measurableSet_le (measurable_sampleStudentizer _) measurable_const))

theorem jointGoodEvent_subset_tail (j : ℕ) (hj : 1 ≤ j) :
    jointGoodEvent j ⊆ {ω | 2 * counterexampleThreshold (rareSampleSize j) ≤
      sampleStatistic (rareSampleSize j) ω} := by
  intro ω hω
  rcases hω with ⟨hN,hR,hupper⟩
  change 2*counterexampleThreshold (rareSampleSize j) ≤ sampleStatistic (rareSampleSize j) ω
  rw [sampleStatistic, ite_eq_left hR]
  change 2*counterexampleThreshold (rareSampleSize j) ≤
    sampleCenteredNumerator (rareSampleSize j) ω / sampleStudentizer (rareSampleSize j) ω
  rw [counterexampleThreshold_rareSampleSize]
  have h := quotient_lower (categoryScale j)
    (sampleCenteredNumerator (rareSampleSize j) ω)
    (sampleStudentizer (rareSampleSize j) ω) (scale_pos_for_tail j) hN hR hupper
  have _ := hj
  linarith

theorem jointGoodEvent_cond_probability_tendsto_one :
    Tendsto (fun j : ℕ =>
      (cond sampleLaw (rareCategoryEvent j)).real (jointGoodEvent j))
      atTop (nhds 1) := by
  obtain ⟨Cn, hCn, hvariance⟩ := variance_sampleCenteredNumerator_cond_uniform
  obtain ⟨Cr, hCr, hsecond⟩ := jackknifeSq_cond_uniform
  have hmean : ∀ᶠ j : ℕ in atTop, 3*categoryScale j/4 ≤
      ∫ ω, sampleCenteredNumerator (rareSampleSize j) ω
        ∂cond sampleLaw (rareCategoryEvent j) := by
    have h := integral_sampleCenteredNumerator_cond_rare_div_scale_tendsto_one.eventually
      (eventually_ge_nhds (by norm_num : (3/4 : ℝ) < 1))
    filter_upwards [h] with j hj
    have he := (le_div_iff₀ (scale_pos_for_tail j)).mp hj
    linarith
  have hl : Tendsto (fun j : ℕ => 1 -
      (16*Cn/categoryScale j^2+Cr/(4*categoryScale j^(2/5 : ℝ))^2))
      atTop (nhds 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub (error_tendsto_zero Cn Cr)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 1, hmean] with j hj hm
    let n := rareSampleSize j
    let μ := cond sampleLaw (rareCategoryEvent j)
    have : IsProbabilityMeasure (cond sampleLaw (rareCategoryEvent j)) :=
      cond_isProbabilityMeasure (show sampleLaw (rareCategoryEvent j) ≠ 0 from
        exactCategoryEvent_ne_zero n (targetCategoryCount j) j hj
          (targetCategoryCount_le_rareSampleSize j))
    have hn := rare_size_three j hj
    have hRQ (ω : ℕ → ℝ) : sampleStudentizer n ω^2 = jackknifeSq n ω :=
      Real.sq_sqrt (jackknifeSq_nonneg n hn ω)
    have hRp : ∀ᵐ ω ∂μ, 0 < sampleStudentizer n ω :=
      ae_iff.mpr ((cond_absolutelyContinuous (μ := sampleLaw) (s := rareCategoryEvent j))
        (ae_iff.mp (ae_sampleStudentizer_pos n hn)))
    have h := joint_probability_lower
      (sampleCenteredNumerator n) (sampleStudentizer n) (jackknifeSq n)
      (measurable_centeredNumerator_for_tail n) (measurable_sampleStudentizer n)
      (memLp_sampleCenteredNumerator_cond_rare j hj)
      (integrable_jackknifeSq_cond_rare j hj) hRQ hRp
      (categoryScale j) (4*categoryScale j^(2/5 : ℝ)) Cn Cr
      (scale_pos_for_tail j)
      (mul_pos (by norm_num) (Real.rpow_pos_of_pos (scale_pos_for_tail j) _))
      hm (hvariance j hj).2 (hsecond j hj).2
    change 1-16*Cn/categoryScale j^2-Cr/(4*categoryScale j^(2/5 : ℝ))^2 ≤
      μ.real (jointGoodEvent j) at h
    linarith
  · filter_upwards [eventually_ge_atTop 1] with j hj
    have : IsProbabilityMeasure (cond sampleLaw (rareCategoryEvent j)) :=
      cond_isProbabilityMeasure (show sampleLaw (rareCategoryEvent j) ≠ 0 from
        exactCategoryEvent_ne_zero (rareSampleSize j) (targetCategoryCount j) j hj
          (targetCategoryCount_le_rareSampleSize j))
    exact probability_le_one _ _

theorem rare_tail_probability_lower :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ j : ℕ in atTop,
        0 ≤ ε j ∧ ε j < 1 ∧
        (1-ε j)*Real.exp (-5*categoryScale j*Real.log (categoryScale j)) ≤
          sampleLaw.real {ω | 2*counterexampleThreshold (rareSampleSize j) ≤
            sampleStatistic (rareSampleSize j) ω} := by
  let ε : ℕ → ℝ := fun j => 1-(cond sampleLaw (rareCategoryEvent j)).real (jointGoodEvent j)
  have hlim : Tendsto ε atTop (nhds 0) := by
    simpa only [ε, sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub
        jointGoodEvent_cond_probability_tendsto_one
  have hhalf : ∀ᶠ j : ℕ in atTop,
      (1/2 : ℝ) ≤ (cond sampleLaw (rareCategoryEvent j)).real (jointGoodEvent j) :=
    jointGoodEvent_cond_probability_tendsto_one.eventually
      (eventually_ge_nhds (by norm_num : (1/2 : ℝ) < 1))
  refine ⟨ε,hlim,?_⟩
  filter_upwards [eventually_ge_atTop 1, hhalf, rareCategoryEvent_exp_lower] with j hj hq he
  have hA0 : sampleLaw (rareCategoryEvent j) ≠ 0 :=
    exactCategoryEvent_ne_zero (rareSampleSize j) (targetCategoryCount j) j hj
      (targetCategoryCount_le_rareSampleSize j)
  have := cond_isProbabilityMeasure (μ := sampleLaw) hA0
  have hq1 := probability_le_one (cond sampleLaw (rareCategoryEvent j)) (jointGoodEvent j)
  refine ⟨by dsimp [ε]; linarith, by dsimp [ε]; linarith, ?_⟩
  have hq0 : 0 ≤ (cond sampleLaw (rareCategoryEvent j)).real (jointGoodEvent j) :=
    measureReal_nonneg
  have htransfer := conditional_good_transfer (μ := sampleLaw)
    (rareCategoryEvent j) (jointGoodEvent j)
    {ω | 2*counterexampleThreshold (rareSampleSize j) ≤ sampleStatistic (rareSampleSize j) ω}
    (measurableSet_exactCategoryEvent _ _ _) (jointGoodEvent_subset_tail j hj)
  have hmul := mul_le_mul_of_nonneg_left he hq0
  dsimp only [ε]
  nlinarith

theorem rare_tail_probability_half_lower :
    ∀ᶠ j : ℕ in atTop,
      (1/2 : ℝ)*Real.exp (-5*categoryScale j*Real.log (categoryScale j)) ≤
        sampleLaw.real {ω | counterexampleThreshold (rareSampleSize j) ≤
          sampleStatistic (rareSampleSize j) ω} := by
  obtain ⟨ε,hlim,hbound⟩ := rare_tail_probability_lower
  have hhalf : ∀ᶠ j : ℕ in atTop, ε j ≤ (1/2 : ℝ) :=
    hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [eventually_ge_atTop 1,hhalf,hbound] with j hj hε hb
  have hx : 0 ≤ counterexampleThreshold (rareSampleSize j) :=
    (counterexampleThreshold_window _ (by have := rare_size_three j hj; omega)).1
  have hmono : sampleLaw.real {ω | 2*counterexampleThreshold (rareSampleSize j) ≤
        sampleStatistic (rareSampleSize j) ω} ≤
      sampleLaw.real {ω | counterexampleThreshold (rareSampleSize j) ≤
        sampleStatistic (rareSampleSize j) ω} := by
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro ω hω
    change counterexampleThreshold (rareSampleSize j) ≤ sampleStatistic (rareSampleSize j) ω
    change 2*counterexampleThreshold (rareSampleSize j) ≤ sampleStatistic (rareSampleSize j) ω at hω
    linarith
  exact (mul_le_mul_of_nonneg_right (by linarith : (1/2 : ℝ) ≤ 1-ε j)
    (Real.exp_pos _).le).trans (hb.2.2.trans hmono)

theorem rare_tail_probability_eventually_pos :
    ∀ᶠ j : ℕ in atTop,
      0 < sampleLaw.real {ω | counterexampleThreshold (rareSampleSize j) ≤
        sampleStatistic (rareSampleSize j) ω} := by
  filter_upwards [rare_tail_probability_half_lower] with j hj
  exact lt_of_lt_of_le (mul_pos (by norm_num) (Real.exp_pos _)) hj

end

end Shao.OQ5.P35
