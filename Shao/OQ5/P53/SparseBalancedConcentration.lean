import Shao.OQ5.P53.SparseConditionalStatisticBounds
import Shao.OQ5.P53.SparsePositiveStudentizer

/-!
# Actual balanced-pattern concentration and the finite event tail

Both bad-event estimates use the actual conditioned sample law and the true
centered-row jackknife. The last step sums the intersections of all disjoint
sorted-pair events, including both orientations. No monotonicity of the input
sequence is used, and no logarithmic or real-encoding transfer is claimed.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology BigOperators

noncomputable section

namespace Shao.OQ5.P53

local notation "SparseObs" => ((ℝ × (ℕ × Bool)) × (ℕ × Bool))

def sparseBalancedFailureBound (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) : ℝ :=
  sparseNumeratorMomentBound α x N /
    (sparseSlow α x (N j) ^ 2 * x (N j) ^ 2) +
  3 * sparseStudentizerMomentBound α x N / sparseSlow α x (N j)

private theorem selected_data (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ)
    (hN : SparseSelectionCore α x N) (hj : 1 ≤ j) :
    4 ≤ N j ∧ 0 < x (N j) ∧ 0 < sparseSlow α x (N j) := by
  have he : j - 1 + 1 = j := by omega
  have h := hN.2.2 (j - 1)
  simp only [he] at h
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩

/- The literal amplitude supplies this bound; it is not an extra moment
   or concentration assumption. -/
private theorem balanced_mean_ge_twice (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hN : SparseSelectionCore α x N) (hj : 1 ≤ j) :
    2 * sparseSlow α x (N j) * x (N j) ≤ sparseBalancedNumeratorMean α x N j := by
  obtain ⟨hn, hx, hs⟩ := selected_data α x N j hN hj
  have hnR : (4 : ℝ) ≤ N j := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < N j := by linarith
  have hn1 : 0 < (N j : ℝ) - 1 := by linarith
  have hn2 : 0 < (N j : ℝ) - 2 := by linarith
  have hj0 : j ≠ 0 := by omega
  have hp : ((N j : ℝ) ^ (3 / 4 : ℝ)) ^ 2 = (N j : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    norm_num
  have hq : Real.sqrt (N j : ℝ) * (N j : ℝ) ^ (3 / 2 : ℝ) = (N j : ℝ) ^ 2 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0]
    norm_num
  have hid : Real.sqrt (N j : ℝ) * sparseAmplitude α x (N j) ^ 2 =
      (N j : ℝ) ^ 2 * (sparseSlow α x (N j) * x (N j)) := by
    unfold sparseAmplitude
    rw [mul_pow, Real.sq_sqrt (mul_pos hs hx).le]
    rw [hp, ← mul_assoc, hq]
  have hshift : sparseLevelShift α x N j =
      sparseAmplitude α x (N j) ^ 2 / ((N j : ℝ) - 2) := by
    simp only [sparseLevelShift, ite_eq_right hj0, sparseShift]
  unfold sparseBalancedNumeratorMean
  rw [hshift]
  apply (le_div_iff₀ hn1).mpr
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hn2).mpr
  have hcorr : 0 ≤ (3 * (N j : ℝ) - 2) *
      (sparseSlow α x (N j) * x (N j)) :=
    mul_nonneg (by linarith) (mul_pos hs hx).le
  nlinarith [hid]

private theorem markov_event {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) (hfn : ∀ ω, 0 ≤ f ω) (A : Set Ω)
    (t B : ℝ) (ht : 0 < t) (hA : ∀ ω ∈ A, t ≤ f ω)
    (hB : (∫ ω, f ω ∂μ) ≤ B) : μ.real A ≤ B / t := by
  have hm : μ.real A ≤ μ.real {ω | t ≤ f ω} :=
    measureReal_mono (fun ω hω => hA ω hω)
  have hk := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hfn) hf t
  apply (le_div_iff₀ ht).mpr
  nlinarith [mul_le_mul_of_nonneg_left hm ht.le, hk.trans hB]

theorem sparseBalancedFailureBound_nonneg :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  0 ≤ sparseBalancedFailureBound α x N j := by
  intro α x N j _hα hN hj
  obtain ⟨_hn, _hx, hs⟩ := selected_data α x N j hN hj
  unfold sparseBalancedFailureBound
  exact add_nonneg
    (div_nonneg (sparseNumeratorMomentBound_pos α x N).le
      (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    (div_nonneg (mul_nonneg (by norm_num) (sparseStudentizerMomentBound_pos α x N).le) hs.le)

theorem sparseBalancedPairPattern_cond_tail_ge :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  1 ≤ sparseSlow α x (N j) →
  ∀ (i k : Fin (N j)) (b : Bool), i < k →
    1 - sparseBalancedFailureBound α x N j ≤
      (sparseBalancedPatternMeasure α x N (N j) j i k b).real
        {ω : Fin (N j) → SparseObs | x (N j) ≤ sparseSampleStudentized α x N ω} := by
  intro α x N j hα hN hj hs1 i k b hik
  obtain ⟨hn, hx, hs⟩ := selected_data α x N j hN hj
  have hn3 : 3 ≤ N j := by omega
  let Q := sparseBalancedPatternMeasure α x N (N j) j i k b
  let s := sparseSlow α x (N j)
  let u := x (N j)
  let Num := fun ω : Fin (N j) → SparseObs => sparseSampleNumerator α x N ω
  let R := fun ω : Fin (N j) → SparseObs => sparseSampleStudentizer α x N ω
  let M := sparseBalancedNumeratorMean α x N j
  let A : Set (Fin (N j) → SparseObs) := {ω | Num ω < s * u}
  let D : Set (Fin (N j) → SparseObs) := {ω | R ω ≤ 0}
  let C : Set (Fin (N j) → SparseObs) := {ω | Real.sqrt s < R ω}
  let G : Set (Fin (N j) → SparseObs) :=
    {ω | s * u ≤ Num ω ∧ 0 < R ω ∧ R ω ≤ Real.sqrt s}
  have : IsProbabilityMeasure Q := sparseBalancedPatternMeasure_probability α x N
    (N j) j i k b hj hik
  have hNum : Measurable Num := (measurable_sparseSampleU α x N (N j)).const_mul _
  have hR : Measurable R := measurable_sparseSampleStudentizer α x N (N j)
  have hG : MeasurableSet G :=
    (measurableSet_le measurable_const hNum).inter
      ((measurableSet_lt measurable_const hR).inter (measurableSet_le hR measurable_const))
  have hM : 2 * s * u ≤ M := balanced_mean_ge_twice α x N j hN hj
  have hnumLp : MemLp Num 2 Q :=
    memLp_sparseSampleNumerator_cond_balanced_two α x N j hα hN hj i k b hik
  have hA : Q.real A ≤ sparseNumeratorMomentBound α x N / (s ^ 2 * u ^ 2) := by
    apply markov_event Q (fun ω => (Num ω - M) ^ 2)
      (hnumLp.sub (memLp_const M)).integrable_sq (fun ω => sq_nonneg _) A
      (s ^ 2 * u ^ 2) (sparseNumeratorMomentBound α x N)
      (mul_pos (sq_pos_of_pos hs) (sq_pos_of_pos hx))
    · intro ω hω
      have ha : Num ω < s * u := hω
      have hl : 0 ≤ M - Num ω - s * u := by nlinarith
      have hr : 0 ≤ M - Num ω + s * u := by nlinarith [mul_pos hs hx]
      nlinarith [mul_nonneg hl hr]
    · exact integral_sparseSampleNumerator_centered_sq_le α x N j hα hN hj i k b hik
  have hC : Q.real C ≤ 3 * sparseStudentizerMomentBound α x N / s := by
    apply markov_event Q (fun ω => sparseSampleStudentizerSq α x N ω)
      (integrable_sparseSampleStudentizerSq_cond_balanced α x N j hα hN hj i k b hik)
      (sparseSampleStudentizerSq_nonneg α x N (N j) hn3) C
      s (3 * sparseStudentizerMomentBound α x N) hs
    · intro ω hω
      have hc : Real.sqrt s < R ω := hω
      have hroot := Real.sq_sqrt hs.le
      have hr := sparseSampleStudentizer_nonneg α x N (N j) ω
      have hr2 := sparseSampleStudentizer_sq α x N (N j) hn3 ω
      change (R ω) ^ 2 = _ at hr2
      nlinarith [Real.sqrt_nonneg s]
    · exact integral_sparseSampleStudentizerSq_cond_balanced_uniform_le
        α x N j hα hN hj i k b hik
  have hpositive : ∀ᵐ ω ∂Q, 0 < R ω := by
    exact (ProbabilityTheory.cond_absolutelyContinuous
      (μ := Measure.pi (fun _ : Fin (N j) => sparsePopulationMeasure α x N))
      (s := sparseBalancedPairPattern j i k b)).ae_le
      (sparseSampleStudentizer_pos_ae α x N (N j) hn3)
  have hDzero : Q D = 0 := by
    have hzero := ae_iff.mp hpositive
    simpa only [D, not_lt] using hzero
  have hD : Q.real D = 0 := by simp only [Measure.real, hDzero, ENNReal.toReal_zero]
  have hbadsub : Gᶜ ⊆ (A ∪ D) ∪ C := by
    intro ω hω
    by_cases ha : Num ω < s * u
    · exact Or.inl (Or.inl ha)
    by_cases hd : R ω ≤ 0
    · exact Or.inl (Or.inr hd)
    right
    change Real.sqrt s < R ω
    by_contra hc
    exact hω ⟨le_of_not_gt ha, lt_of_not_ge hd, le_of_not_gt hc⟩
  have hbad : Q.real Gᶜ ≤ sparseBalancedFailureBound α x N j := by
    have hm := measureReal_mono (μ := Q) hbadsub
    have hu := measureReal_union_le (μ := Q) (A ∪ D) C
    have hv := measureReal_union_le (μ := Q) A D
    dsimp only [sparseBalancedFailureBound]
    change Q.real Gᶜ ≤ sparseNumeratorMomentBound α x N / (s ^ 2 * u ^ 2) +
      3 * sparseStudentizerMomentBound α x N / s
    linarith
  have hgood : 1 - sparseBalancedFailureBound α x N j ≤ Q.real G := by
    rw [probReal_compl_eq_one_sub hG] at hbad
    linarith
  apply hgood.trans
  refine measureReal_mono ?_ (measure_ne_top Q _)
  intro ω hω
  obtain ⟨hnum, hrpos, hrbound⟩ := hω
  have hsqrt : Real.sqrt s ≤ s := Real.sqrt_le_self_iff.mpr (Or.inr hs1)
  have hprod : u * R ω ≤ s * u := by
    nlinarith [mul_le_mul_of_nonneg_left (hrbound.trans hsqrt) hx.le]
  change u ≤ Num ω / R ω
  exact (le_div_iff₀ hrpos).mpr (hprod.trans hnum)

theorem tendsto_sparseBalancedFailureBound_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  Tendsto (sparseBalancedFailureBound α x N) atTop (nhds 0) := by
  intro α x N hα hα1 hN hSuper hSmall
  have hNt := sparseSelectionCore_tendsto α x N hN
  have hs := (sparseSlow_tendsto α x hα hα1 hSuper hSmall).comp hNt
  have hx := (sparse_input_tendsto α x hα hα1 hSuper hSmall).comp hNt
  have his := tendsto_inv_atTop_zero.comp hs
  have hix := tendsto_inv_atTop_zero.comp hx
  have hfirst : Tendsto (fun j : ℕ => sparseNumeratorMomentBound α x N *
      ((sparseSlow α x (N j))⁻¹) ^ 2 * ((x (N j))⁻¹) ^ 2)
      atTop (nhds (sparseNumeratorMomentBound α x N * (0 : ℝ) ^ 2 * 0 ^ 2)) :=
    (tendsto_const_nhds.mul (his.pow 2)).mul (hix.pow 2)
  have hsecond : Tendsto (fun j : ℕ =>
      (3 * sparseStudentizerMomentBound α x N) * (sparseSlow α x (N j))⁻¹)
      atTop (nhds ((3 * sparseStudentizerMomentBound α x N) * (0 : ℝ))) :=
    tendsto_const_nhds.mul his
  have h : Tendsto (fun j : ℕ => sparseNumeratorMomentBound α x N *
      ((sparseSlow α x (N j))⁻¹) ^ 2 * ((x (N j))⁻¹) ^ 2 +
      (3 * sparseStudentizerMomentBound α x N) * (sparseSlow α x (N j))⁻¹)
      atTop (nhds (0 : ℝ)) := by
    simpa using hfirst.add hsecond
  convert h using 1
  · funext j
    simp only [sparseBalancedFailureBound, div_eq_mul_inv, mul_inv_rev, inv_pow]
    ring

theorem eventually_sparseBalancedPairPattern_cond_tail_half :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  ∀ᶠ j : ℕ in atTop, ∀ (i k : Fin (N j)) (b : Bool), i < k →
    (1 : ℝ) / 2 ≤
      (sparseBalancedPatternMeasure α x N (N j) j i k b).real
        {ω : Fin (N j) → SparseObs | x (N j) ≤ sparseSampleStudentized α x N ω} := by
  intro α x N hα hα1 hN hSuper hSmall
  have hs := (sparseSlow_tendsto α x hα hα1 hSuper hSmall).comp
    (sparseSelectionCore_tendsto α x N hN)
  have hf := tendsto_sparseBalancedFailureBound_zero α x N hα hα1 hN hSuper hSmall
  have hb : ∀ᶠ j in atTop, sparseBalancedFailureBound α x N j < (1 : ℝ) / 2 :=
    hf.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_ge_atTop (1 : ℕ), hs.eventually_ge_atTop 1, hb]
    with j hj hsj hbj
  intro i k b hik
  have h := sparseBalancedPairPattern_cond_tail_ge α x N j hα hN hj hsj i k b hik
  linarith

private theorem cond_real_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E T : Set Ω) (hE : MeasurableSet E) :
    (ProbabilityTheory.cond μ E).real T * μ.real E = μ.real (E ∩ T) := by
  simp only [Measure.real, ← ENNReal.toReal_mul,
    ProbabilityTheory.cond_mul_eq_inter hE T μ]

/- Sum the two actual orientations first. This does not replace the
   conditioned law by an assumed mixture. -/
private theorem pair_event_inter_half (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n j : ℕ) (i k : Fin n) (_hik : i < k) (T : Set (Fin n → SparseObs))
    (hT : MeasurableSet T)
    (h : ∀ b : Bool, (1 : ℝ) / 2 ≤
      (sparseBalancedPatternMeasure α x N n j i k b).real T) :
    (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N)).real
      (sparseBalancedPairEvent j i k) / 2 ≤
    (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N)).real
      (sparseBalancedPairEvent j i k ∩ T) := by
  have : IsProbabilityMeasure (sparsePopulationMeasure α x N) :=
    sparsePopulationMeasure_probability α x N
  let μ := Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N)
  have hp (b : Bool) : μ.real (sparseBalancedPairPattern j i k b) / 2 ≤
      μ.real (sparseBalancedPairPattern j i k b ∩ T) := by
    have hm := mul_le_mul_of_nonneg_right (h b)
      (measureReal_nonneg (μ := μ) (s := sparseBalancedPairPattern j i k b))
    have he := cond_real_mul μ (sparseBalancedPairPattern j i k b) T
      (measurableSet_sparseBalancedPairPattern n j i k b)
    change (sparseBalancedPatternMeasure α x N n j i k b).real T *
      μ.real (sparseBalancedPairPattern j i k b) = _ at he
    rw [he] at hm
    nlinarith
  have hd := sparseBalancedPairPattern_disjoint n j i k
  have hfalse := hp false
  have htrue := hp true
  change μ.real (sparseBalancedPairEvent j i k) / 2 ≤
    μ.real (sparseBalancedPairEvent j i k ∩ T)
  unfold sparseBalancedPairEvent
  rw [Set.union_inter_distrib_right,
    measureReal_union hd (measurableSet_sparseBalancedPairPattern n j i k true),
    measureReal_union (hd.mono Set.inter_subset_left Set.inter_subset_left)
      ((measurableSet_sparseBalancedPairPattern n j i k true).inter hT)]
  linarith

/- The remaining finite sum ranges over every sorted pair. Invalid ordered
   pairs in the literal event are empty by their defining i < k conjunct. -/
private theorem balanced_event_inter_half (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n j : ℕ) (T : Set (Fin n → SparseObs)) (hT : MeasurableSet T)
    (h : ∀ (i k : Fin n) (b : Bool), i < k → (1 : ℝ) / 2 ≤
      (sparseBalancedPatternMeasure α x N n j i k b).real T) :
    (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N)).real
      (sparseBalancedEvent n j) / 2 ≤
    (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N)).real T := by
  classical
  have : IsProbabilityMeasure (sparsePopulationMeasure α x N) :=
    sparsePopulationMeasure_probability α x N
  let μ := Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N)
  let I := {p : Fin n × Fin n // p.1 < p.2}
  let F : I → Set (Fin n → SparseObs) :=
    fun p => sparseBalancedPairEvent j p.val.1 p.val.2
  have hE : sparseBalancedEvent n j = ⋃ p : I, F p := by
    ext ω
    simp only [sparseBalancedEvent, Set.mem_iUnion]
    constructor
    · rintro ⟨i, k, hω⟩
      have hik : i < k := by
        rcases hω with hf | ht
        · exact hf.1
        · exact ht.1
      exact ⟨⟨(i, k), hik⟩, hω⟩
    · rintro ⟨p, hω⟩
      exact ⟨p.val.1, p.val.2, hω⟩
  have hd : Pairwise (fun p q : I => Disjoint (F p) (F q)) := by
    intro p q hpq
    exact sparseBalancedPairEvent_disjoint n j p.val.1 p.val.2 q.val.1 q.val.2
      p.property q.property (fun he => hpq (Subtype.ext he))
  have hm (p : I) : MeasurableSet (F p) :=
    measurableSet_sparseBalancedPairEvent n j p.val.1 p.val.2
  have hdT : Pairwise (fun p q : I => Disjoint (F p ∩ T) (F q ∩ T)) := by
    intro p q hpq
    exact (hd hpq).mono Set.inter_subset_left Set.inter_subset_left
  have heq : μ.real (sparseBalancedEvent n j) = ∑ p : I, μ.real (F p) := by
    rw [hE]
    exact measureReal_iUnion_fintype hd hm
  have hTeq : μ.real (sparseBalancedEvent n j ∩ T) = ∑ p : I, μ.real (F p ∩ T) := by
    rw [hE, Set.iUnion_inter]
    exact measureReal_iUnion_fintype hdT (fun p => (hm p).inter hT)
  have hsum : μ.real (sparseBalancedEvent n j) / 2 ≤
      μ.real (sparseBalancedEvent n j ∩ T) := by
    rw [heq, hTeq, Finset.sum_div]
    apply Finset.sum_le_sum
    intro p _hp
    exact pair_event_inter_half α x N n j p.val.1 p.val.2 p.property T hT
      (fun b => h p.val.1 p.val.2 b p.property)
  exact hsum.trans (measureReal_mono Set.inter_subset_right)

theorem eventually_sparseBalancedEvent_tail_half :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  ∀ᶠ j : ℕ in atTop,
    (Measure.pi (fun _ : Fin (N j) => sparsePopulationMeasure α x N)).real
        (sparseBalancedEvent (N j) j) / 2 ≤
      (Measure.pi (fun _ : Fin (N j) => sparsePopulationMeasure α x N)).real
        {ω : Fin (N j) → SparseObs | x (N j) ≤ sparseSampleStudentized α x N ω} := by
  intro α x N hα hα1 hN hSuper hSmall
  filter_upwards [eventually_sparseBalancedPairPattern_cond_tail_half
    α x N hα hα1 hN hSuper hSmall] with j hj
  exact balanced_event_inter_half α x N (N j) j _
    (measurableSet_le measurable_const (measurable_sparseSampleStudentized α x N (N j))) hj

end Shao.OQ5.P53
