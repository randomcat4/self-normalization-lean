import Shao.Probability.BrownianSup
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Order.LiminfLimsup

/-!
# Boundary of actual Brownian survival

The raw events refer to the given process, including time zero. The interior
argument uses countably many Gaussian bridge coordinates; the endpoint
argument uses time inversion and Kolmogorov's zero-one law for integer
increments. No stopping-time property is assumed.
-/

noncomputable section

namespace Shao.OQ4.BrownianSurvivalBoundary
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

def closedSurvival (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (u : ℝ) : Set Ω :=
  {ω | ∀ t : ℝ≥0, t ≤ T → |u + B t ω| ≤ 1}

def strictSurvival (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (u : ℝ) : Set Ω :=
  {ω | ∀ t : ℝ≥0, t ≤ T → |u + B t ω| < 1}

noncomputable def pathSup (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (u : ℝ) (ω : Ω) : ℝ :=
  sSup ((fun t : ℝ≥0 => |u + B t ω|) '' Icc 0 T)

private noncomputable def unitTime (n : ℕ) : ℝ≥0 :=
  Shao.Probability.BrownianSup.rationalTime n

private noncomputable def coeff (n : ℕ) : ℝ :=
  (unitTime n : ℝ)

private noncomputable def sampleTime (T : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  T * unitTime n

private def traceClosed (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (u r : ℝ) : Set Ω :=
  {ω | ∀ n : ℕ, |u + B (sampleTime T n) ω| ≤ r}

private def traceUniform (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (u : ℝ) : Set Ω :=
  ⋃ k : ℕ, traceClosed B T u (1 - 1 / ((k : ℝ) + 1))

private noncomputable def bridgeTrace (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℕ → ℝ :=
  fun n => B (sampleTime T n) ω - coeff n * B T ω

private def bridgeRegular : Set (ℕ → ℝ) :=
  {z | ∀ k : ℕ, ∃ m : ℕ, ∀ n : ℕ,
    coeff n ≤ 1 / ((m : ℝ) + 1) →
      |z n| ≤ 1 / ((k : ℝ) + 1)}

private def bridgeClosed (u r : ℝ) : Set ((ℕ → ℝ) × ℝ) :=
  {p | ∀ n : ℕ, |u + p.1 n + coeff n * p.2| ≤ r}

private def bridgeBoundary (u : ℝ) : Set ((ℕ → ℝ) × ℝ) :=
  bridgeClosed u 1 \
    ⋃ k : ℕ, bridgeClosed u (1 - 1 / ((k : ℝ) + 1))

private def walkUpperBounded (X : ℕ → Ω → ℝ) : Set Ω :=
  {ω | ∃ K : ℕ, ∀ n : ℕ,
    (∑ i ∈ Finset.range n, X i ω) ≤ (K : ℝ)}

private theorem unitTime_mem (n : ℕ) :
    unitTime n ∈ Icc (0 : ℝ≥0) 1 := by
  constructor
  · exact bot_le
  · change max 0 (min 1 _) ≤ (1 : ℝ)
    exact max_le (by norm_num) (min_le_left _ _)

private theorem traceClosed_nullMeasurable (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) (u r : ℝ) :
    NullMeasurableSet (traceClosed B T u r) P := by
  have heq : traceClosed B T u r =
      ⋂ n : ℕ, {ω | |u + B (sampleTime T n) ω| ≤ r} := by
    ext ω
    simp only [traceClosed, mem_setOf_eq, mem_iInter]
  rw [heq]
  apply NullMeasurableSet.iInter
  intro n
  exact (continuous_abs.measurable.comp_aemeasurable
    ((hB.aemeasurable (sampleTime T n)).const_add u)).nullMeasurableSet_preimage
      measurableSet_Iic

private theorem continuous_pathSup_characterization (B : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (u : ℝ) (ω : Ω) (hc : Continuous (B · ω)) :
    (ω ∈ closedSurvival B T u ↔ pathSup B T u ω ≤ 1) ∧
    (ω ∈ strictSurvival B T u ↔ pathSup B T u ω < 1) := by
  have hcont : Continuous (fun t : ℝ≥0 => |u + B t ω|) :=
    (continuous_const.add hc).abs
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ≥0) T).Nonempty from ⟨0, by simp⟩) hcont.continuousOn
  have hb : BddAbove ((fun t : ℝ≥0 => |u + B t ω|) '' Icc 0 T) :=
    (isCompact_Icc.image hcont).bddAbove
  have hsup : pathSup B T u ω = |u + B s ω| := by
    apply le_antisymm
    · apply csSup_le
      · exact ⟨_, ⟨s, hs, rfl⟩⟩
      · rintro _ ⟨t, ht, rfl⟩
        exact hmax ht
    · exact le_csSup hb ⟨s, hs, rfl⟩
  rw [hsup]
  constructor
  · constructor
    · intro h
      exact h s hs.2
    · intro h t ht
      exact (hmax ⟨bot_le, ht⟩).trans h
  · constructor
    · intro h
      exact h s hs.2
    · intro h t ht
      exact (hmax ⟨bot_le, ht⟩).trans_lt h

private theorem closedSurvival_ae_eq_traceClosed (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (u : ℝ) :
    closedSurvival B T u =ᵐ[P] traceClosed B T u 1 := by
  filter_upwards [hB.cont] with ω hc
  apply propext
  constructor
  · intro h n
    apply h
    exact (mul_le_mul_of_nonneg_left (unitTime_mem n).2 (show (0 : ℝ≥0) ≤ T from bot_le)).trans_eq (mul_one T)
  · intro h t ht
    by_cases hT : T = 0
    · have ht0 : t = 0 := le_antisymm (ht.trans_eq hT) (bot_le)
      simpa only [hT, ht0, sampleTime, zero_mul] using h 0
    · have hTp : 0 < (T : ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero hT)
      obtain ⟨q, _, _, hq⟩ := Real.exists_seq_rat_strictMono_tendsto ((t : ℝ) / T)
      let clamp : ℝ → ℝ≥0 := fun r => ⟨max 0 (min 1 r), le_max_left _ _⟩
      have hclamp : Continuous clamp := by
        unfold clamp
        fun_prop
      have htime : Continuous (fun r : ℝ => T * clamp r) := by fun_prop
      have hval : T * clamp ((t : ℝ) / T) = t := by
        apply Subtype.ext
        change (T : ℝ) * max 0 (min 1 ((t : ℝ) / T)) = t
        have hfrac0 : (0 : ℝ) ≤ (t : ℝ) / (T : ℝ) := div_nonneg t.2 T.2
        have hfrac1 : (t : ℝ) / (T : ℝ) ≤ 1 :=
          (div_le_one hTp).mpr (show (t : ℝ) ≤ T from ht)
        have hclamped : max (0 : ℝ) (min 1 ((t : ℝ) / (T : ℝ))) =
            (t : ℝ) / (T : ℝ) := by
          apply le_antisymm
          · exact max_le hfrac0 (min_le_right _ _)
          · exact (min_eq_right hfrac1).symm.trans_le (le_max_right _ _)
        rw [hclamped]
        field_simp [hTp.ne']
      have hlim : Tendsto (fun j => |u + B (T * clamp (q j : ℝ)) ω|)
          atTop (𝓝 |u + B t ω|) := by
        simpa only [hval, Function.comp_def] using
          (((show Continuous (fun r : ℝ => |u + B (T * clamp r) ω|) from
              (continuous_const.add (hc.comp htime)).abs)).tendsto ((t : ℝ) / T)).comp hq
      apply le_of_tendsto hlim
      apply Eventually.of_forall
      intro j
      simpa [sampleTime, unitTime, Shao.Probability.BrownianSup.rationalTime,
        clamp, Encodable.encodek] using h (Encodable.encode (q j))

private theorem strictSurvival_ae_eq_traceUniform (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (u : ℝ) :
    strictSurvival B T u =ᵐ[P] traceUniform B T u := by
  filter_upwards [hB.cont] with ω hc
  apply propext
  constructor
  · intro h
    have hcont : Continuous (fun t : ℝ≥0 => |u + B t ω|) :=
      (continuous_const.add hc).abs
    obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (show (Icc (0 : ℝ≥0) T).Nonempty from ⟨0, by simp⟩) hcont.continuousOn
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr (h s hs.2))
    apply mem_iUnion.mpr
    refine ⟨k, fun n => ?_⟩
    have htn : sampleTime T n ≤ T :=
      (mul_le_mul_of_nonneg_left (unitTime_mem n).2 (show (0 : ℝ≥0) ≤ T from bot_le)).trans_eq (mul_one T)
    have hm := hmax (show sampleTime T n ∈ Icc 0 T from ⟨bot_le, htn⟩)
    change |u + B (sampleTime T n) ω| ≤ |u + B s ω| at hm
    linarith
  · intro h
    obtain ⟨k, hk⟩ := mem_iUnion.mp h
    have hbound : ∀ t : ℝ≥0, t ≤ T →
        |u + B t ω| ≤ 1 - 1 / ((k : ℝ) + 1) := by
      intro t ht
      by_cases hT : T = 0
      · have ht0 : t = 0 := le_antisymm (ht.trans_eq hT) (bot_le)
        simpa only [hT, ht0, sampleTime, zero_mul] using hk 0
      · have hTp : 0 < (T : ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero hT)
        obtain ⟨q, _, _, hq⟩ := Real.exists_seq_rat_strictMono_tendsto ((t : ℝ) / T)
        let clamp : ℝ → ℝ≥0 := fun r => ⟨max 0 (min 1 r), le_max_left _ _⟩
        have hclamp : Continuous clamp := by unfold clamp; fun_prop
        have htime : Continuous (fun r : ℝ => T * clamp r) := by fun_prop
        have hval : T * clamp ((t : ℝ) / T) = t := by
          apply Subtype.ext
          change (T : ℝ) * max 0 (min 1 ((t : ℝ) / T)) = t
          have hfrac0 : (0 : ℝ) ≤ (t : ℝ) / (T : ℝ) := div_nonneg t.2 T.2
          have hfrac1 : (t : ℝ) / (T : ℝ) ≤ 1 :=
            (div_le_one hTp).mpr (show (t : ℝ) ≤ T from ht)
          have hclamped : max (0 : ℝ) (min 1 ((t : ℝ) / (T : ℝ))) =
              (t : ℝ) / (T : ℝ) := by
            apply le_antisymm
            · exact max_le hfrac0 (min_le_right _ _)
            · exact (min_eq_right hfrac1).symm.trans_le (le_max_right _ _)
          rw [hclamped]
          field_simp [hTp.ne']
        have hlim : Tendsto (fun j => |u + B (T * clamp (q j : ℝ)) ω|)
            atTop (𝓝 |u + B t ω|) := by
          simpa only [hval, Function.comp_def] using
            (((show Continuous (fun r : ℝ => |u + B (T * clamp r) ω|) from
              (continuous_const.add (hc.comp htime)).abs)).tendsto ((t : ℝ) / T)).comp hq
        apply le_of_tendsto hlim
        apply Eventually.of_forall
        intro j
        simpa [sampleTime, unitTime, Shao.Probability.BrownianSup.rationalTime,
          clamp, Encodable.encodek] using hk (Encodable.encode (q j))
    intro t ht
    have hp : 0 < 1 / ((k : ℝ) + 1) := by positivity
    linarith [hbound t ht]

private theorem bridgeTrace_aemeasurable (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    AEMeasurable (bridgeTrace B T) P := by
  exact AEMeasurable.of_eval fun n =>
    (hB.aemeasurable (sampleTime T n)).sub ((hB.aemeasurable T).const_mul (coeff n))

private theorem bridgeTrace_indep_terminal (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    IndepFun (bridgeTrace B T) (B T) P := by
  let X : ℕ → Ω → ℝ := fun n ω => bridgeTrace B T ω n
  let Y : Unit → Ω → ℝ := fun _ => B T
  have hjoint : IsGaussianProcess (Sum.elim X Y) P := by
    apply hB.isGaussianProcess.of_isGaussianProcess
    rintro (n | v)
    · refine ⟨{sampleTime T n, T},
        { toFun := fun z => z ⟨sampleTime T n, by simp⟩ - coeff n * z ⟨T, by simp⟩
          map_add' := by intros; simp; ring
          map_smul' := by intros; simp; ring }, ?_⟩
      intro ω
      rfl
    · refine ⟨{T},
        { toFun := fun z => z ⟨T, by simp⟩
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }, ?_⟩
      intro ω
      rfl
  have hcov (n : ℕ) (v : Unit) : cov[X n, Y v; P] = 0 := by
    have hst : sampleTime T n ≤ T :=
      (mul_le_mul_of_nonneg_left (unitTime_mem n).2
        (show (0 : ℝ≥0) ≤ T from bot_le)).trans_eq (mul_one T)
    change cov[fun ω => B (sampleTime T n) ω - coeff n * B T ω, B T; P] = 0
    rw [covariance_fun_sub_left, covariance_const_mul_left,
      hB.covariance_fun_eval, hB.covariance_fun_eval, min_self,
      min_eq_left hst]
    · simp only [sampleTime, coeff, NNReal.coe_mul]
      ring
    · exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
    · exact ((hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two).const_mul _
    · exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
  have hi := hjoint.indepFun_of_covariance_eq_zero
    (fun n => (measurable_pi_apply n).comp_aemeasurable
      (bridgeTrace_aemeasurable B P hB T))
    (fun _ => hB.aemeasurable T) hcov
  simpa only [X, Y, Function.comp_def, id_eq] using
    hi.comp measurable_id (measurable_pi_apply ())

private theorem bridgeRegular_measurable :
    MeasurableSet bridgeRegular := by
  have heq : bridgeRegular = ⋂ k : ℕ, ⋃ m : ℕ, ⋂ n : ℕ,
      {z : ℕ → ℝ | coeff n ≤ 1 / ((m : ℝ) + 1) → |z n| ≤ 1 / ((k : ℝ) + 1)} := by
    ext z
    simp only [bridgeRegular, mem_setOf_eq, mem_iInter, mem_iUnion]
  rw [heq]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iUnion
  intro m
  apply MeasurableSet.iInter
  intro n
  by_cases hn : coeff n ≤ 1 / ((m : ℝ) + 1)
  · simpa only [hn, true_implies] using
      (measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply n)) measurable_const :
        MeasurableSet {z : ℕ → ℝ | |z n| ≤ 1 / ((k : ℝ) + 1)})
  · simp only [hn, false_implies, setOf_true]
    exact MeasurableSet.univ

private theorem bridgeTrace_mem_regular_ae (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, bridgeTrace B T ω ∈ bridgeRegular := by
  filter_upwards [hB.cont, hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hc hzero
  intro k
  let f : ℝ≥0 → ℝ := fun s => B (T * s) ω - (s : ℝ) * B T ω
  have hfc : Continuous f := by unfold f; fun_prop
  have hf0 : f 0 = 0 := by simp [f, hzero]
  have hlim : Tendsto f (𝓝 0) (𝓝 0) := by simpa only [hf0] using hfc.tendsto 0
  have hev : ∀ᶠ s : ℝ≥0 in 𝓝 0, |f s| < 1 / ((k : ℝ) + 1) :=
    hlim.eventually (by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ)
        (by positivity : 0 < 1 / ((k : ℝ) + 1))] with y hy
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hy)
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp hev
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  refine ⟨m, fun n hn => ?_⟩
  have hd : dist (unitTime n) 0 < ε := by
    change dist (unitTime n : ℝ) (0 : ℝ) < ε
    rw [Real.dist_eq, sub_zero]
    calc
      |(unitTime n : ℝ)| = coeff n := abs_of_nonneg (unitTime n).2
      _ < ε := hn.trans_lt hm
  exact (he hd).le

private theorem bridgeBoundary_measurable (u : ℝ) :
    MeasurableSet (bridgeBoundary u) := by
  have hm (r : ℝ) : MeasurableSet (bridgeClosed u r) := by
    have heq : bridgeClosed u r = ⋂ n : ℕ,
        {p : (ℕ → ℝ) × ℝ | |u + p.1 n + coeff n * p.2| ≤ r} := by
      ext p
      simp only [bridgeClosed, mem_setOf_eq, mem_iInter]
    rw [heq]
    apply MeasurableSet.iInter
    intro n
    exact measurableSet_le (by fun_prop) measurable_const
  exact (hm 1).diff (MeasurableSet.iUnion fun k => hm _)

private theorem bridgeBoundary_section_finite
    (u : ℝ) (hu : |u| < 1) (z : ℕ → ℝ) (hz : z ∈ bridgeRegular) :
    ((Prod.mk z) ⁻¹' bridgeBoundary u).Finite := by
  apply Set.finite_of_forall_not_lt_lt
  intro x hx y hy w hw hxy hyw
  simp only [mem_preimage, bridgeBoundary, Set.mem_sdiff, bridgeClosed,
    mem_setOf_eq, mem_iUnion] at hx hy hw
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < (1 - |u|) / 4 by linarith)
  obtain ⟨m, hm⟩ := hz k
  let δ : ℝ := min (1 / ((m : ℝ) + 1)) ((1 - |u|) / (4 * (|y| + 1)))
  have hδ : 0 < δ := by
    apply lt_min
    · positivity
    · exact div_pos (sub_pos.mpr hu) (by positivity)
  have hδm : δ ≤ 1 / ((m : ℝ) + 1) := min_le_left _ _
  have hδy : δ * |y| ≤ (1 - |u|) / 4 := by
    have hd := (le_div_iff₀ (by positivity : 0 < 4 * (|y| + 1))).mp
      (show δ ≤ (1 - |u|) / (4 * (|y| + 1)) from min_le_right _ _)
    nlinarith [abs_nonneg y]
  let r : ℝ := min ((1 - |u|) / 2) (min (δ * (y - x)) (δ * (w - y)))
  have hr : 0 < r := by
    exact lt_min (by linarith) (lt_min
      (mul_pos hδ (sub_pos.mpr hxy)) (mul_pos hδ (sub_pos.mpr hyw)))
  have hr0 : r ≤ (1 - |u|) / 2 := min_le_left _ _
  have hr1 : r ≤ δ * (y - x) := (min_le_right _ _).trans (min_le_left _ _)
  have hr2 : r ≤ δ * (w - y) := (min_le_right _ _).trans (min_le_right _ _)
  have hybound : ∀ n : ℕ, |u + z n + coeff n * y| ≤ 1 - r := by
    intro n
    have han : 0 ≤ coeff n := (unitTime n).2
    by_cases hn : coeff n ≤ δ
    · have hzn := hm n (hn.trans hδm)
      have htri := abs_add_le (u + z n) (coeff n * y)
      have htri' := abs_add_le u (z n)
      rw [abs_mul, abs_of_nonneg han] at htri
      have hmul := mul_le_mul_of_nonneg_right hn (abs_nonneg y)
      linarith
    · have hdn : δ ≤ coeff n := (lt_of_not_ge hn).le
      have hlow := (abs_le.mp (hx.1 n)).1
      have hupp := (abs_le.mp (hw.1 n)).2
      have hmul1 := mul_le_mul_of_nonneg_right hdn (sub_nonneg.mpr hxy.le)
      have hmul2 := mul_le_mul_of_nonneg_right hdn (sub_nonneg.mpr hyw.le)
      apply abs_le.mpr
      constructor <;> nlinarith
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hr
  apply hy.2
  refine ⟨j, fun n => ?_⟩
  linarith [hybound n]

private theorem bridgeBoundary_product_null
    (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν]
    (T : ℝ≥0) (hT : 0 < T) (u : ℝ) (hu : |u| < 1)
    (hν : ∀ᵐ z ∂ν, z ∈ bridgeRegular) :
    (ν.prod (gaussianReal 0 T)) (bridgeBoundary u) = 0 := by
  letI : NullSingletonClass (gaussianReal 0 T) :=
    nullSingletonClass_gaussianReal (ne_of_gt hT)
  apply (Measure.measure_prod_null (bridgeBoundary_measurable u)).mpr
  filter_upwards [hν] with z hz
  exact (bridgeBoundary_section_finite u hu z hz).measure_zero _

private theorem interior_survival_sdiff_null (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (hT : 0 < T)
    (u : ℝ) (hu : |u| < 1) :
    P (closedSurvival B T u \ strictSurvival B T u) = 0 := by
  have hZa := bridgeTrace_aemeasurable B P hB.toIsPreBrownianReal T
  have hYa := hB.toIsPreBrownianReal.aemeasurable T
  let ν : Measure (ℕ → ℝ) := P.map (bridgeTrace B T)
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hν : ∀ᵐ z ∂ν, z ∈ bridgeRegular := by
    exact (ae_map_iff hZa bridgeRegular_measurable).mpr
      (bridgeTrace_mem_regular_ae B P hB T)
  have hprod : P.map (fun ω => (bridgeTrace B T ω, B T ω)) =
      ν.prod (gaussianReal 0 T) := by
    rw [(bridgeTrace_indep_terminal B P hB.toIsPreBrownianReal T).map_prod_eq_prod_map_map
      hZa hYa, (hB.toIsPreBrownianReal.hasLaw_eval T).map_eq]
  have heq : (fun ω => (bridgeTrace B T ω, B T ω)) ⁻¹' bridgeBoundary u =
      traceClosed B T u 1 \ traceUniform B T u := by
    ext ω
    simp only [mem_preimage, bridgeBoundary, Set.mem_sdiff, bridgeClosed,
      mem_setOf_eq, mem_iUnion, traceClosed, traceUniform, bridgeTrace]
    have hc (n : ℕ) : u + (B (sampleTime T n) ω - coeff n * B T ω) +
        coeff n * B T ω = u + B (sampleTime T n) ω := by ring
    simp only [hc]
  have hzero : P (traceClosed B T u 1 \ traceUniform B T u) = 0 := by
    rw [← heq, ← Measure.map_apply_of_aemeasurable (hZa.prodMk hYa)
      (bridgeBoundary_measurable u), hprod]
    exact bridgeBoundary_product_null ν T hT u hu hν
  rw [← hzero]
  apply measure_congr
  filter_upwards [closedSurvival_ae_eq_traceClosed B P hB T u,
    strictSurvival_ae_eq_traceUniform B P hB T u] with ω hc hd
  exact propext (and_congr (Iff.of_eq hc) (not_congr (Iff.of_eq hd)))

private theorem walkUpperBounded_tail
    (X : ℕ → Ω → ℝ) (hX : ∀ n : ℕ, Measurable (X n)) :
    MeasurableSet[
      Filter.limsup
        (fun n : ℕ => MeasurableSpace.comap (X n) (borel ℝ))
        Filter.atTop]
      (walkUpperBounded X) := by
  classical
  rw [limsup_eq_iInf_iSup_of_nat]
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro m
  let tailSpace : MeasurableSpace Ω :=
    ⨆ i : ℕ, ⨆ (_ : i ≥ m), MeasurableSpace.comap (X i) (borel ℝ)
  have hcoord (j : ℕ) : Measurable[tailSpace] (X (m + j)) := by
    apply (comap_measurable (X (m + j))).mono _ le_rfl
    exact le_iSup_of_le (m + j) (le_iSup_of_le (Nat.le_add_right m j) le_rfl)
  have heq : walkUpperBounded X =
      ⋃ K : ℕ, ⋂ n : ℕ,
        {ω | (∑ j ∈ Finset.range n, X (m + j) ω) ≤ (K : ℝ)} := by
    ext ω
    simp only [walkUpperBounded, mem_setOf_eq, mem_iUnion, mem_iInter]
    have hsum (n : ℕ) : (∑ i ∈ Finset.range (m + n), X i ω) =
        (∑ i ∈ Finset.range m, X i ω) + ∑ j ∈ Finset.range n, X (m + j) ω :=
      Finset.sum_range_add (fun i => X i ω) m n
    constructor
    · rintro ⟨K, hK⟩
      obtain ⟨L, hL⟩ := exists_nat_ge ((K : ℝ) - ∑ i ∈ Finset.range m, X i ω)
      refine ⟨L, fun n => ?_⟩
      have h := hK (m + n)
      rw [hsum] at h
      linarith
    · rintro ⟨K, hK⟩
      obtain ⟨L, hL⟩ := exists_nat_ge
        (max ((∑ i ∈ Finset.range m, X i ω) + (K : ℝ))
          (∑ i ∈ Finset.range m, |X i ω|))
      refine ⟨L, fun n => ?_⟩
      by_cases hn : m ≤ n
      · have h := hK (n - m)
        have he := hsum (n - m)
        rw [Nat.add_sub_of_le hn] at he
        have hbound := (le_max_left
          ((∑ i ∈ Finset.range m, X i ω) + (K : ℝ))
          (∑ i ∈ Finset.range m, |X i ω|)).trans hL
        linarith
      · have hnm : n ≤ m := (lt_of_not_ge hn).le
        have hbound := (le_max_right
          ((∑ i ∈ Finset.range m, X i ω) + (K : ℝ))
          (∑ i ∈ Finset.range m, |X i ω|)).trans hL
        calc
          (∑ i ∈ Finset.range n, X i ω) ≤ ∑ i ∈ Finset.range n, |X i ω| :=
            Finset.sum_le_sum fun i _ => le_abs_self _
          _ ≤ ∑ i ∈ Finset.range m, |X i ω| :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm)
              (fun i _ _ => abs_nonneg _)
          _ ≤ (L : ℝ) := hbound
  rw [heq]
  apply MeasurableSet.iUnion
  intro K
  apply MeasurableSet.iInter
  intro n
  exact measurableSet_le (Finset.measurable_sum _ fun j _ => hcoord j) measurable_const

private theorem gaussian_walkUpperBounded_null (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hXm : ∀ n : ℕ, Measurable (X n))
    (hXi : iIndepFun X P)
    (hSlaw : ∀ n : ℕ,
      HasLaw (fun ω => ∑ i ∈ Finset.range n, X i ω)
        (gaussianReal 0 (n : ℝ≥0)) P) :
    P (walkUpperBounded X) = 0 := by
  classical
  let U : ℕ → Set Ω := fun K =>
    {ω | ∀ n : ℕ, (∑ i ∈ Finset.range n, X i ω) ≤ (K : ℝ)}
  have hmono : Monotone U := by
    intro K L hKL ω hω n
    exact (hω n).trans (by exact_mod_cast hKL)
  have hU : walkUpperBounded X = ⋃ K : ℕ, U K := by
    ext ω
    simp only [walkUpperBounded, U, mem_setOf_eq, mem_iUnion]
  have hc : gaussianReal 0 1 (Iic (1 : ℝ)) ≠ 1 := by
    intro heq
    have hz : gaussianReal 0 1 (Iic (1 : ℝ))ᶜ = 0 :=
      (prob_compl_eq_zero_iff measurableSet_Iic).mpr heq
    have hv : (volume : Measure ℝ) (Iic (1 : ℝ))ᶜ = 0 :=
      gaussianReal_absolutelyContinuous' 0 (by norm_num) hz
    have hv' : (volume : Measure ℝ) (Ioc (1 : ℝ) 2) = 0 :=
      measure_mono_null (by
        intro x hx
        change ¬ x ≤ 1
        exact not_le.mpr hx.1) hv
    norm_num [Real.volume_Ioc] at hv'
  have hbound (K : ℕ) : P (U K) ≤ gaussianReal 0 1 (Iic (1 : ℝ)) := by
    have hp : 0 < (K : ℝ) + 1 := by positivity
    have hv : (((K + 1) ^ 2 : ℕ) : ℝ≥0) /
        (NNReal.mk (((K : ℝ) + 1) ^ 2) (sq_nonneg _)) = 1 := by
      apply Subtype.ext
      change ((((K + 1) ^ 2 : ℕ) : ℝ) / ((K : ℝ) + 1) ^ 2) = 1
      push_cast
      exact div_self (pow_ne_zero _ hp.ne')
    have hnorm : HasLaw
        (fun ω => (∑ i ∈ Finset.range ((K + 1) ^ 2), X i ω) / ((K : ℝ) + 1))
        (gaussianReal 0 1) P := by
      convert gaussianReal_div_const (hSlaw ((K + 1) ^ 2)) ((K : ℝ) + 1) using 1
      congr 1
      · exact (zero_div _).symm
      · exact hv.symm
    calc
      P (U K) ≤ P {ω | (∑ i ∈ Finset.range ((K + 1) ^ 2), X i ω) /
          ((K : ℝ) + 1) ≤ 1} := by
        apply measure_mono
        intro ω hω
        exact (div_le_one hp).mpr (by linarith [hω ((K + 1) ^ 2)])
      _ = gaussianReal 0 1 (Iic (1 : ℝ)) := hnorm.measure_eq measurableSet_Iic
  have hlt : P (walkUpperBounded X) ≤ gaussianReal 0 1 (Iic (1 : ℝ)) := by
    rw [hU, hmono.measure_iUnion]
    exact iSup_le hbound
  rcases measure_zero_or_one_of_measurableSet_limsup_atTop
      (fun n => (hXm n).comap_le) hXi.iIndep (walkUpperBounded_tail X hXm) with hz | ho
  · exact hz
  · exfalso
    apply hc
    exact le_antisymm prob_le_one (ho ▸ hlt)

private theorem preBrownian_integer_unboundedAbove_ae (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ a : ℝ, ∃ n : ℕ, a < B (n : ℝ≥0) ω := by
  let R : ℕ → Ω → ℝ := fun n ω =>
    B ((n + 1 : ℕ) : ℝ≥0) ω - B (n : ℝ≥0) ω
  have hRa (n : ℕ) : AEMeasurable (R n) P :=
    (hB.aemeasurable _).sub (hB.aemeasurable _)
  let X : ℕ → Ω → ℝ := fun n => (hRa n).mk (R n)
  have hXm (n : ℕ) : Measurable (X n) := (hRa n).measurable_mk
  have hRi : iIndepFun R P :=
    hB.hasIndepIncrements.nat (t := fun n : ℕ => (n : ℝ≥0))
      (fun a b h => by
        change (a : ℝ≥0) ≤ (b : ℝ≥0)
        exact_mod_cast h)
  have hXi : iIndepFun X P :=
    (iIndepFun_congr (fun n => (hRa n).ae_eq_mk)).mp hRi
  have hsum : ∀ᵐ ω ∂P, ∀ n : ℕ,
      (∑ i ∈ Finset.range n, X i ω) = B (n : ℝ≥0) ω := by
    have hcoords : ∀ᵐ ω ∂P, ∀ n : ℕ, X n ω = R n ω :=
      ae_all_iff.mpr (fun n => (hRa n).ae_eq_mk.symm)
    filter_upwards [hcoords, hB.eval_zero_ae_eq_zero] with ω hω hz
    intro n
    calc
      (∑ i ∈ Finset.range n, X i ω) =
          ∑ i ∈ Finset.range n,
            (B ((i + 1 : ℕ) : ℝ≥0) ω - B (i : ℝ≥0) ω) :=
        Finset.sum_congr rfl fun i _ => hω i
      _ = B (n : ℝ≥0) ω - B (0 : ℝ≥0) ω :=
        by simpa only [Nat.cast_zero] using
          Finset.sum_range_sub (fun i : ℕ => B (i : ℝ≥0) ω) n
      _ = B (n : ℝ≥0) ω := by rw [hz, sub_zero]
  have hSlaw (n : ℕ) : HasLaw
      (fun ω => ∑ i ∈ Finset.range n, X i ω) (gaussianReal 0 (n : ℝ≥0)) P :=
    (hB.hasLaw_eval (n : ℝ≥0)).congr (hsum.mono (fun ω hω => hω n))
  have hnull := gaussian_walkUpperBounded_null P X hXm hXi hSlaw
  have hnot : ∀ᵐ ω ∂P, ω ∉ walkUpperBounded X := by
    apply ae_iff.mpr
    exact measure_mono_null (by intro ω hω; exact not_not.mp hω) hnull
  filter_upwards [hsum, hnot] with ω hω hn
  intro a
  by_contra h
  obtain ⟨K, hK⟩ := exists_nat_ge a
  apply hn
  refine ⟨K, fun n => ?_⟩
  rw [hω n]
  exact (le_of_not_gt (fun hgt => h ⟨n, hgt⟩)).trans hK

private theorem preBrownian_crosses_both_before_ae (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, 0 < T →
      (∃ t : ℝ≥0, 0 < t ∧ t ≤ T ∧ 0 < B t ω) ∧
      (∃ t : ℝ≥0, 0 < t ∧ t ≤ T ∧ B t ω < 0) := by
  let W : ℝ≥0 → Ω → ℝ := fun t ω => (t : ℝ) * B (1 / t) ω
  let V : ℝ≥0 → Ω → ℝ := fun t ω => (t : ℝ) * (-B) (1 / t) ω
  have hW : IsPreBrownianReal W P := hB.inv
  have hV : IsPreBrownianReal V P := hB.neg.inv
  filter_upwards [preBrownian_integer_unboundedAbove_ae W P hW,
    preBrownian_integer_unboundedAbove_ae V P hV] with ω hw hv
  intro T hT
  have hTp : 0 < (T : ℝ) := hT
  have hfind (F : ℕ → ℝ) (hF : ∀ a : ℝ, ∃ n : ℕ, a < F n) :
      ∃ n : ℕ, 0 < n ∧ 1 / (n : ℝ≥0) ≤ T ∧ 0 < F n := by
    obtain ⟨N, hN⟩ := exists_nat_gt ((T : ℝ)⁻¹)
    obtain ⟨n, hn⟩ := hF ((∑ i ∈ Finset.range (N + 1), |F i|) + 1)
    have hnN : N < n := by
      by_contra h
      have hmem : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
      have hb : |F n| ≤ ∑ i ∈ Finset.range (N + 1), |F i| :=
        Finset.single_le_sum (fun i _ => abs_nonneg (F i)) hmem
      linarith [le_abs_self (F n)]
    have hnp : 0 < n := by omega
    have hnr : 0 < (n : ℝ) := by exact_mod_cast hnp
    have hrec : 1 / (n : ℝ≥0) ≤ T := by
      apply NNReal.coe_le_coe.mp
      change (1 : ℝ) / (n : ℝ) ≤ (T : ℝ)
      apply (div_le_iff₀ hnr).mpr
      have hni : (T : ℝ)⁻¹ < (n : ℝ) := hN.trans (by exact_mod_cast hnN)
      have hh := mul_lt_mul_of_pos_left hni hTp
      have hc : (T : ℝ) * (T : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hTp.ne'
      nlinarith
    refine ⟨n, hnp, hrec, ?_⟩
    have hs : 0 ≤ ∑ i ∈ Finset.range (N + 1), |F i| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  constructor
  · obtain ⟨n, hn, ht, hp⟩ := hfind (fun n => W (n : ℝ≥0) ω) hw
    refine ⟨1 / (n : ℝ≥0), by positivity, ht, ?_⟩
    change 0 < (n : ℝ) * B (1 / (n : ℝ≥0)) ω at hp
    by_contra hb
    have hneg := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n : (0 : ℝ) ≤ _)
      (le_of_not_gt hb)
    linarith
  · obtain ⟨n, hn, ht, hp⟩ := hfind (fun n => V (n : ℝ≥0) ω) hv
    refine ⟨1 / (n : ℝ≥0), by positivity, ht, ?_⟩
    change 0 < (n : ℝ) * (-B (1 / (n : ℝ≥0)) ω) at hp
    by_contra hb
    have hneg := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n : (0 : ℝ) ≤ _)
      (neg_nonpos.mpr (le_of_not_gt hb))
    linarith

theorem closedSurvival_nullMeasurable (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (u : ℝ) :
    NullMeasurableSet (closedSurvival B T u) P :=
  (traceClosed_nullMeasurable B P hB.toIsPreBrownianReal T u 1).congr
    (closedSurvival_ae_eq_traceClosed B P hB T u).symm

theorem strictSurvival_nullMeasurable (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (u : ℝ) :
    NullMeasurableSet (strictSurvival B T u) P := by
  apply (NullMeasurableSet.iUnion fun k : ℕ =>
    traceClosed_nullMeasurable B P hB.toIsPreBrownianReal T u
      (1 - 1 / ((k : ℝ) + 1))).congr
  exact (strictSurvival_ae_eq_traceUniform B P hB T u).symm

theorem survival_sdiff_ae_eq_pathSup_eq_one (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (u : ℝ) :
    closedSurvival B T u \ strictSurvival B T u =ᵐ[P]
      {ω | pathSup B T u ω = 1} := by
  filter_upwards [hB.cont] with ω hc
  apply propext
  change (ω ∈ closedSurvival B T u ∧ ω ∉ strictSurvival B T u) ↔
    pathSup B T u ω = 1
  have hchar := continuous_pathSup_characterization B T u ω hc
  rw [hchar.1, hchar.2]
  constructor
  · intro h
    exact le_antisymm h.1 (le_of_not_gt h.2)
  · intro h
    rw [h]
    exact ⟨le_rfl, lt_irrefl _⟩

theorem measure_closedSurvival_pos_endpoint_eq_zero (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (hT : 0 < T) :
    P (closedSurvival B T 1) = 0 := by
  have hnot : ∀ᵐ ω ∂P, ω ∉ closedSurvival B T 1 := by
    filter_upwards [preBrownian_crosses_both_before_ae B P hB.toIsPreBrownianReal]
      with ω hω
    intro hsurv
    obtain ⟨t, ht0, htT, htB⟩ := (hω T hT).1
    have hb := hsurv t htT
    have ha := le_abs_self (1 + B t ω)
    linarith
  exact measure_mono_null (by intro ω hω; exact not_not.mpr hω) (ae_iff.mp hnot)

theorem measure_closedSurvival_neg_endpoint_eq_zero (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (hT : 0 < T) :
    P (closedSurvival B T (-1)) = 0 := by
  have hnot : ∀ᵐ ω ∂P, ω ∉ closedSurvival B T (-1) := by
    filter_upwards [preBrownian_crosses_both_before_ae B P hB.toIsPreBrownianReal]
      with ω hω
    intro hsurv
    obtain ⟨t, ht0, htT, htB⟩ := (hω T hT).2
    have hb := hsurv t htT
    have ha := neg_le_abs (-1 + B t ω)
    linarith
  exact measure_mono_null (by intro ω hω; exact not_not.mpr hω) (ae_iff.mp hnot)

theorem measure_survival_sdiff_eq_zero (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (hT : 0 < T)
    (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    P (closedSurvival B T u \ strictSurvival B T u) = 0 := by
  rcases eq_or_lt_of_le hu.1 with hl | hl
  · have heq : u = -1 := hl.symm
    rw [heq]
    exact measure_mono_null sdiff_subset
      (measure_closedSurvival_neg_endpoint_eq_zero B P hB T hT)
  · rcases lt_or_eq_of_le hu.2 with hr | hr
    · exact interior_survival_sdiff_null B P hB T hT u (abs_lt.mpr ⟨hl, hr⟩)
    · rw [hr]
      exact measure_mono_null sdiff_subset
        (measure_closedSurvival_pos_endpoint_eq_zero B P hB T hT)

theorem measure_pathSup_eq_one_eq_zero (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (hT : 0 < T)
    (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    P {ω | pathSup B T u ω = 1} = 0 :=
  (measure_congr (survival_sdiff_ae_eq_pathSup_eq_one B P hB T u)).symm.trans
    (measure_survival_sdiff_eq_zero B P hB T hT u hu)

end Shao.OQ4.BrownianSurvivalBoundary
