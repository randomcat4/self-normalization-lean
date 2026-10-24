import Shao.OQ4.OriginalIIDWindow
import Shao.OQ4.RademacherOriginalStrictBoundary
import Shao.OQ4.BrownianPositiveCDF
import Shao.Probability.BrownianFirstTerm
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal Topology
universe uX uB

namespace Shao.OQ4.StrictIIDWindow
variable {ΩX : Type uX} [MeasurableSpace ΩX]
variable {ΩB : Type uB} [MeasurableSpace ΩB]

-- A01: reuse the existing generic positive-prefix event verbatim.
-- Its n=0 event is univ; the literal maximum event in A09 is empty at n=0.
def sourceStrictWindowError
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (μ : Measure ΩX) (X : ℕ → ΩX → ℝ)
    (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  sSup ((fun x : ℝ =>
    |μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X x) /
      Shao.Probability.BrownianSup.probability B P hB x - 1|) '' Ioo (a n) 1)

-- A02: exact positive-time bridge, all real boundaries and every path.
theorem source_strict_event_eq_max (n : ℕ) (hn : 0 < n)
    (X : ℕ → ΩX → ℝ) (x : ℝ) :
    RademacherOriginalStrictBoundary.sourceStrictEvent n X x =
      {ω | OriginalIIDWindow.sourceMaximum n X ω <
        x * Real.sqrt (OriginalIIDWindow.sourceEnergy n X ω)} := by
  classical
  have hp (k : ℕ) (hk : k ≤ n) (ω : ΩX) :
      Shao.prefixSum (OriginalIIDWindow.sourcePath n X ω) k =
        ∑ i ∈ Finset.range k, X (i + 1) ω := by
    unfold Shao.prefixSum OriginalIIDWindow.sourcePath
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i hi
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
    · intro i hi j hj hij
      exact Fin.ext hij
    · intro j hj
      have hjk := Finset.mem_range.mp hj
      refine ⟨⟨j, lt_of_lt_of_le hjk hk⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjk⟩
    · intro i hi
      rfl
  ext ω
  change (∀ k : ℕ, 1 ≤ k → k ≤ n → _) ↔ _
  constructor
  · intro h
    obtain ⟨k, hk, hkn, hatt⟩ := Shao.absMax_attained
      (OriginalIIDWindow.sourcePath n X ω) hn
    simpa only [Set.mem_setOf_eq, OriginalIIDWindow.sourceMaximum, dif_pos hn, hatt, hp k hkn ω]
      using h k hk hkn
  · intro h k hk hkn
    exact lt_of_le_of_lt
      ((OriginalIIDWindow.sourceMaximum_le_iff n hn X ω _).mp le_rfl k hk hkn) h

-- A03: the original AE interface; no law/moment/ordinary-measurability premise.
theorem nullMeasurableSet_sourceStrictEvent
    (μ : Measure ΩX) (X : ℕ → ΩX → ℝ)
    (hX : ∀ i : ℕ, AEMeasurable (X (i + 1)) μ) (n : ℕ) (x : ℝ) :
    NullMeasurableSet
      (RademacherOriginalStrictBoundary.sourceStrictEvent n X x) μ := by
  classical
  have hE : AEMeasurable (OriginalIIDWindow.sourceEnergy n X) μ := by
    have heq : OriginalIIDWindow.sourceEnergy n X =
        fun ω => ∑ i ∈ Finset.range n, (X (i + 1) ω) ^ 2 :=
      funext (OriginalIIDWindow.sourceEnergy_eq_sum n X)
    rw [heq]
    fun_prop
  have hS (k : ℕ) : AEMeasurable
      (fun ω => |∑ i ∈ Finset.range k, X (i + 1) ω|) μ := by
    fun_prop
  have hm (k : ℕ) : NullMeasurableSet
      {ω | |∑ i ∈ Finset.range k, X (i + 1) ω| <
        x * Real.sqrt (OriginalIIDWindow.sourceEnergy n X ω)} μ :=
    nullMeasurableSet_lt (hS k) (aemeasurable_const.mul hE.sqrt)
  simpa only [RademacherOriginalStrictBoundary.sourceStrictEvent, setOf_forall]
    using NullMeasurableSet.iInter (fun k : ℕ =>
      NullMeasurableSet.iInter (fun _ : 1 ≤ k =>
        NullMeasurableSet.iInter (fun _ : k ≤ n => hm k)))

-- A04: same-window left approximation; no probability or iid premise.
theorem source_strict_left_union (n : ℕ) (hn : 0 < n)
    (X : ℕ → ΩX → ℝ) (a x : ℝ) (ha : 0 < a) (hax : a < x) :
    (⋃ j : ℕ, OriginalIIDWindow.sourceEvent n X
      (x - (x - a) / ((j : ℝ) + 2))) =
        RademacherOriginalStrictBoundary.sourceStrictEvent n X x ∪
          {ω | OriginalIIDWindow.sourceEnergy n X ω = 0} ∧
    Disjoint (RademacherOriginalStrictBoundary.sourceStrictEvent n X x)
      {ω | OriginalIIDWindow.sourceEnergy n X ω = 0} := by
  classical
  have hzmax (ω : ΩX) (hz : OriginalIIDWindow.sourceEnergy n X ω = 0) :
      OriginalIIDWindow.sourceMaximum n X ω = 0 := by
    simpa only [OriginalIIDWindow.sourceMaximum, dif_pos hn] using
      Shao.absMax_eq_zero_of_energy_eq_zero (OriginalIIDWindow.sourcePath n X ω) hn hz
  have hden : Tendsto (fun j : ℕ => (j : ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono (fun j : ℕ => by linarith) tendsto_natCast_atTop_atTop
  have hy : Tendsto (fun j : ℕ => x - (x - a) / ((j : ℝ) + 2)) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hden)
  rw [source_strict_event_eq_max n hn X x]
  constructor
  · ext ω
    simp only [mem_iUnion, mem_union, mem_setOf_eq, OriginalIIDWindow.sourceEvent]
    constructor
    · rintro ⟨j, hj⟩
      by_cases hz : OriginalIIDWindow.sourceEnergy n X ω = 0
      · exact Or.inr hz
      · have hE := Shao.energy_nonneg (OriginalIIDWindow.sourcePath n X ω)
        have hV : 0 < Real.sqrt (OriginalIIDWindow.sourceEnergy n X ω) :=
          Real.sqrt_pos.mpr (lt_of_le_of_ne hE (Ne.symm hz))
        left
        exact hj.trans_lt (mul_lt_mul_of_pos_right
          (sub_lt_self x (div_pos (sub_pos.mpr hax) (by positivity))) hV)
    · rintro (hs | hz)
      · have hev := (hy.mul_const (Real.sqrt (OriginalIIDWindow.sourceEnergy n X ω))).eventually
          (eventually_gt_nhds hs)
        obtain ⟨j, hj⟩ := hev.exists
        exact ⟨j, hj.le⟩
      · exact ⟨0, by simp only [hzmax ω hz, hz, Real.sqrt_zero, mul_zero, le_refl]⟩
  · apply Set.disjoint_left.mpr
    intro ω hs hz
    change OriginalIIDWindow.sourceMaximum n X ω < _ at hs
    change OriginalIIDWindow.sourceEnergy n X ω = 0 at hz
    simpa only [hzmax ω hz, hz, Real.sqrt_zero, mul_zero, lt_self_iff_false] using hs

-- A05: exact zero-energy atom at EVERY n, including n=0.
-- Finite third moment and centering are not needed for this helper.
theorem source_zero_energy_facts
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hX : ∀ i : ℕ, AEMeasurable (X (i + 1)) μ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hIdent : ∀ i : ℕ, IdentDistrib (X (i + 1)) (X 1) μ μ)
    (hsecond : 0 < ∫ ω, (X 1 ω) ^ 2 ∂μ) :
    0 ≤ μ.real {ω | X 1 ω = 0} ∧
    μ.real {ω | X 1 ω = 0} < 1 ∧
    ∀ n : ℕ, μ.real {ω | OriginalIIDWindow.sourceEnergy n X ω = 0} =
      (μ.real {ω | X 1 ω = 0}) ^ n := by
  classical
  have hm : NullMeasurableSet {ω | X 1 ω = 0} μ :=
    nullMeasurableSet_eq_fun (by simpa using hX 0) aemeasurable_const
  have hp1 : μ.real {ω | X 1 ω = 0} ≤ 1 := by
    simpa using (measureReal_mono (μ := μ) (Set.subset_univ {ω | X 1 ω = 0}))
  have hpstrict : μ.real {ω | X 1 ω = 0} < 1 := by
    by_contra h
    have heq : μ.real {ω | X 1 ω = 0} = 1 := le_antisymm hp1 (le_of_not_gt h)
    have hc : μ.real {ω | X 1 ω = 0}ᶜ = 0 := by
      rw [probReal_compl_eq_one_sub₀ hm, heq, sub_self]
    have hae : ∀ᵐ ω ∂μ, X 1 ω = 0 := by
      rw [ae_iff]
      exact (measureReal_eq_zero_iff).mp hc
    have hi : (∫ ω, (X 1 ω) ^ 2 ∂μ) = 0 := by
      calc
        _ = ∫ ω, (0 : ℝ) ∂μ := integral_congr_ae (hae.mono fun ω hω => by simp [hω])
        _ = 0 := integral_zero _ _
    exact (ne_of_gt hsecond) hi
  refine ⟨measureReal_nonneg, hpstrict, ?_⟩
  intro n
  have hset : {ω | OriginalIIDWindow.sourceEnergy n X ω = 0} =
      ⋂ i ∈ Finset.range n, (X (i + 1)) ⁻¹' ({0} : Set ℝ) := by
    ext ω
    simp only [mem_setOf_eq, mem_iInter, mem_preimage, mem_singleton_iff]
    rw [OriginalIIDWindow.sourceEnergy, Shao.energy_eq_zero_iff]
    constructor
    · intro h i hi
      exact h ⟨i, Finset.mem_range.mp hi⟩
    · intro h i
      exact h i.val (Finset.mem_range.mpr i.is_lt)
  have hind := hIndep.measure_inter_preimage_eq_mul (Finset.range n)
    (sets := fun _ => ({0} : Set ℝ)) (fun _ _ => measurableSet_singleton 0)
  have heach (i : ℕ) : μ ((X (i + 1)) ⁻¹' ({0} : Set ℝ)) = μ {ω | X 1 ω = 0} :=
    (hIdent i).measure_mem_eq (measurableSet_singleton 0)
  rw [Measure.real, hset, hind]
  simp_rw [heach]
  simp only [Finset.prod_const, Finset.card_range, ENNReal.toReal_pow, Measure.real]

-- A06: actual Brownian rare-probability denominator; no antitonicity needed.
theorem geometric_over_brownian_tendsto
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 (0 : ℝ)))
    (hslow : Tendsto
      (fun n => a n * (n : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop) :
    Tendsto (fun n : ℕ => p ^ n /
      Shao.Probability.BrownianSup.probability B P hB (a n))
      atTop (𝓝 (0 : ℝ)) := by
  classical
  let F := Shao.Probability.BrownianSup.probability B P hB
  let L : ℝ := Real.pi ^ 2 / 8
  have hL : 0 < L := by dsimp [L]; positivity
  have htail : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 0 < a n := by
    filter_upwards [eventually_ge_atTop 1, hslow.eventually (eventually_gt_atTop 0)] with n hn hs
    refine ⟨hn, ?_⟩
    have hr := Real.rpow_nonneg (Nat.cast_nonneg n) ((1 : ℝ) / 6)
    nlinarith
  by_cases hp : p = 0
  · apply tendsto_const_nhds.congr'
    filter_upwards [htail] with n hn
    simp [hp, Nat.ne_of_gt hn.1]
  have hpp : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hp)
  have hlog : Real.log p < 0 := Real.log_neg hpp hp1
  have hE : Tendsto (fun n : ℕ => (a n) ^ 2 * (n : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hslow
    filter_upwards [eventually_ge_atTop 1, hslow.eventually (eventually_ge_atTop 1)] with n hn hs
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hr : ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 ≤ (n : ℝ) := by
      calc
        _ = (n : ℝ) ^ (((1 : ℝ) / 6) * 2) := by
          rw [Real.rpow_mul (Nat.cast_nonneg n)]
          norm_num only [Real.rpow_ofNat]
        _ ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hnr (by norm_num)
        _ = (n : ℝ) := Real.rpow_one _
    have hh := mul_le_mul_of_nonneg_left hr (sq_nonneg (a n))
    nlinarith
  have hz : Tendsto (fun n : ℕ => L / ((a n) ^ 2 * (n : ℝ))) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hE
  obtain ⟨δ, hδ, hfirst⟩ := Shao.Probability.BrownianSup.actual_brownian_firstTerm
    B P hB (1 / 2) (by norm_num)
  have hbound : ∀ᶠ n : ℕ in atTop,
      0 ≤ p ^ n / F (a n) ∧
      p ^ n / F (a n) ≤ (Real.pi / 2) * Real.exp ((Real.log p / 2) * (n : ℝ)) := by
    filter_upwards [htail, ha.eventually (eventually_lt_nhds hδ),
      hz.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < -Real.log p / 2))]
      with n hn hδn hzN
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn.1
    have haN : 0 < a n := hn.2
    have hFa : 0 < F (a n) := BrownianPositiveCDF.probability_pos B P hB _ haN
    have ht : 0 < Shao.Probability.BrownianSup.firstTerm (a n) := by
      unfold Shao.Probability.BrownianSup.firstTerm
      positivity
    have hlower : (2 / Real.pi) * Real.exp (-L / (a n) ^ 2) ≤ F (a n) := by
      have hr := (abs_lt.mp (hfirst (a n) haN hδn)).1
      have hh : (1 / 2 : ℝ) * Shao.Probability.BrownianSup.firstTerm (a n) ≤ F (a n) :=
        (le_div_iff₀ ht).mp (by dsimp [F]; linarith)
      dsimp only [Shao.Probability.BrownianSup.firstTerm, L] at hh ⊢
      convert hh using 1 <;> ring
    have hcost : L / (a n) ^ 2 ≤ (-Real.log p / 2) * (n : ℝ) := by
      have hh := (div_lt_iff₀ (mul_pos (sq_pos_of_pos haN) hnR)).mp hzN
      apply (div_le_iff₀ (sq_pos_of_pos haN)).mpr
      nlinarith
    have hpow : p ^ n = Real.exp ((n : ℝ) * Real.log p) := by
      rw [Real.exp_nat_mul, Real.exp_log hpp]
    have hExp : Real.exp ((n : ℝ) * Real.log p + L / (a n) ^ 2) ≤
        Real.exp ((Real.log p / 2) * (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      linarith
    have heq : p ^ n / ((2 / Real.pi) * Real.exp (-L / (a n) ^ 2)) =
        (Real.pi / 2) * Real.exp ((n : ℝ) * Real.log p + L / (a n) ^ 2) := by
      rw [hpow, Real.exp_add]
      have he : Real.exp (-L / (a n) ^ 2) = (Real.exp (L / (a n) ^ 2))⁻¹ := by
        rw [← Real.exp_neg]; congr 1; ring
      rw [he]
      field_simp
    refine ⟨div_nonneg (pow_nonneg hp0 n) hFa.le, ?_⟩
    calc
      _ ≤ p ^ n / ((2 / Real.pi) * Real.exp (-L / (a n) ^ 2)) :=
        div_le_div_of_nonneg_left (pow_nonneg hp0 n) (by positivity) hlower
      _ = _ := heq
      _ ≤ _ := mul_le_mul_of_nonneg_left hExp (by positivity)
  have hdecay : Tendsto (fun n : ℕ =>
      (Real.pi / 2) * Real.exp ((Real.log p / 2) * (n : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    have harg : Tendsto (fun n : ℕ => (Real.log p / 2) * (n : ℝ)) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg (by linarith : Real.log p / 2 < 0)).mpr
        tendsto_natCast_atTop_atTop
    simpa using (Real.tendsto_exp_atBot.comp harg).const_mul (Real.pi / 2)
  exact squeeze_zero' (hbound.mono fun _ h => h.1) (hbound.mono fun _ h => h.2) hdecay

-- A07: proper real sSup exists in the proof; the paid finite comparison.
theorem source_strict_window_bound
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (μ : Measure ΩX) [IsProbabilityMeasure μ]
    (X : ℕ → ΩX → ℝ)
    (hX : ∀ i : ℕ, AEMeasurable (X (i + 1)) μ)
    (a : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (ha0 : 0 < a n) (ha1 : a n < 1) :
    0 ≤ sourceStrictWindowError B P hB μ X a n ∧
    sourceStrictWindowError B P hB μ X a n ≤
      OriginalIIDWindow.sourceWindowError B P hB μ X a n +
        μ.real {ω | OriginalIIDWindow.sourceEnergy n X ω = 0} /
          Shao.Probability.BrownianSup.probability B P hB (a n) := by
  classical
  let F := Shao.Probability.BrownianSup.probability B P hB
  let Ew := OriginalIIDWindow.sourceWindowError B P hB μ X a n
  let Z := {ω | OriginalIIDWindow.sourceEnergy n X ω = 0}
  let E := (fun x : ℝ =>
    |μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X x) / F x - 1|)
  have hFa : 0 < F (a n) := BrownianPositiveCDF.probability_pos B P hB _ ha0
  have hspec := OriginalIIDWindow.sourceWindowError_spec B P hB μ X a n ha0 ha1
  have hb (x : ℝ) (hx : x ∈ Ioo (a n) 1) :
      E x ≤ Ew + μ.real Z / F (a n) := by
    let y : ℕ → ℝ := fun j => x - (x - a n) / ((j : ℝ) + 2)
    have hyx (j : ℕ) : a n < y j ∧ y j < x := by
      have hd : (0 : ℝ) < (j : ℝ) + 2 := by positivity
      have hd1 : (1 : ℝ) < (j : ℝ) + 2 := by
        have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        linarith
      have hqpos := div_pos (sub_pos.mpr hx.1) hd
      have hq : (x - a n) / ((j : ℝ) + 2) < x - a n :=
        (div_lt_self (sub_pos.mpr hx.1) hd1)
      dsimp [y]
      constructor <;> linarith
    have hy : Tendsto y atTop (𝓝 x) := by
      have hd : Tendsto (fun j : ℕ => (j : ℝ) + 2) atTop atTop :=
        tendsto_atTop_mono (fun j : ℕ => by linarith) tendsto_natCast_atTop_atTop
      simpa [y] using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hd)
    have hyMono : Monotone y := by
      intro j k hjk
      have hdj : (0 : ℝ) < (j : ℝ) + 2 := by positivity
      have hdjk : (j : ℝ) + 2 ≤ (k : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hjk 2
      have hh := div_le_div_of_nonneg_left (sub_pos.mpr hx.1).le hdj hdjk
      dsimp [y]
      linarith
    let W := fun j : ℕ => OriginalIIDWindow.sourceEvent n X (y j)
    have hW : Monotone W := by
      intro j k hjk ω hω
      change OriginalIIDWindow.sourceMaximum n X ω ≤ _ at hω ⊢
      exact hω.trans (mul_le_mul_of_nonneg_right (hyMono hjk) (Real.sqrt_nonneg _))
    have hu := source_strict_left_union n hn X (a n) x ha0 hx.1
    have hp : Tendsto (fun j : ℕ => μ.real (W j)) atTop
        (𝓝 (μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X x) + μ.real Z)) := by
      have hh := (ENNReal.tendsto_toReal (show μ (⋃ j, W j) ≠ ⊤ from by finiteness)).comp
        (tendsto_measure_iUnion_atTop (μ := μ) hW)
      have heq : μ.real (⋃ j, W j) =
          μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X x) + μ.real Z := by
        rw [show (⋃ j, W j) = RademacherOriginalStrictBoundary.sourceStrictEvent n X x ∪ Z from hu.1]
        exact measureReal_union₀' (nullMeasurableSet_sourceStrictEvent μ X hX n x) hu.2.aedisjoint
      change Tendsto (fun j => μ.real (W j)) atTop (𝓝 (μ.real (⋃ j, W j))) at hh
      rw [heq] at hh
      exact hh
    have hFx : 0 < F x := BrownianPositiveCDF.probability_pos B P hB _ (ha0.trans hx.1)
    have hF : Tendsto (fun j => F (y j)) atTop (𝓝 (F x)) :=
      BrownianPositiveCDF.probability_tendsto B P hB y x (ha0.trans hx.1) hy
    have hlim : |(μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X x) +
        μ.real Z) / F x - 1| ≤ Ew := by
      apply le_of_tendsto (((hp.div hF (ne_of_gt hFx)).sub_const 1).abs)
      exact Eventually.of_forall fun j => hspec.2.2.1.1
        ⟨y j, ⟨(hyx j).1, (hyx j).2.trans hx.2⟩, rfl⟩
    have hmono : F (a n) ≤ F x := BrownianPositiveCDF.probability_mono B P hB hx.1.le
    have hq : 0 ≤ μ.real Z / F x := div_nonneg measureReal_nonneg hFx.le
    have hqb : μ.real Z / F x ≤ μ.real Z / F (a n) :=
      div_le_div_of_nonneg_left measureReal_nonneg hFa hmono
    have heq : μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X x) / F x - 1 =
        ((μ.real (RademacherOriginalStrictBoundary.sourceStrictEvent n X x) + μ.real Z) / F x - 1) -
          μ.real Z / F x := by rw [add_div]; ring
    dsimp only [E]
    rw [heq]
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg hq]; exact add_le_add hlim hqb)
  have hne : (E '' Ioo (a n) 1).Nonempty := by
    refine ⟨_, (a n + 1) / 2, ⟨by linarith, by linarith⟩, rfl⟩
  have hbd : BddAbove (E '' Ioo (a n) 1) := by
    refine ⟨Ew + μ.real Z / F (a n), ?_⟩
    rintro z ⟨x, hx, rfl⟩
    exact hb x hx
  change 0 ≤ sSup (E '' Ioo (a n) 1) ∧ _
  constructor
  · obtain ⟨z, hz⟩ := hne
    obtain ⟨x, hx, rfl⟩ := hz
    exact (abs_nonneg _).trans (le_csSup hbd ⟨x, hx, rfl⟩)
  · exact csSup_le hne (by rintro z ⟨x, hx, rfl⟩; exact hb x hx)

-- A08: general fixed iid strict positive-prefix window, exact original premises.
theorem source_strict_window_ae_tendsto
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (μ : Measure ΩX) [IsProbabilityMeasure μ]
    (X : ℕ → ΩX → ℝ)
    (hX : ∀ i : ℕ, AEMeasurable (X (i + 1)) μ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hIdent : ∀ i : ℕ, IdentDistrib (X (i + 1)) (X 1) μ μ)
    (h3 : Integrable (fun ω => |X 1 ω| ^ 3) μ)
    (hmean : (∫ ω, X 1 ω ∂μ) = 0)
    (hsecond : 0 < ∫ ω, (X 1 ω) ^ 2 ∂μ)
    (a : ℕ → ℝ) (haAnti : Antitone a)
    (ha : Tendsto a atTop (𝓝 (0 : ℝ)))
    (hslow : Tendsto
      (fun n => a n * (n : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop) :
    Tendsto (sourceStrictWindowError B P hB μ X a) atTop (𝓝 (0 : ℝ)) := by
  have hz := source_zero_energy_facts μ X hX hIndep hIdent hsecond
  have hg := geometric_over_brownian_tendsto B P hB
    (μ.real {ω | X 1 ω = 0}) hz.1 hz.2.1 a ha hslow
  have hw := OriginalIIDWindow.source_window_ae_tendsto B P hB μ X hX
    hIndep hIdent h3 hmean hsecond a haAnti ha hslow
  have hsum := hw.add hg
  have hevent : ∀ᶠ n : ℕ in atTop,
      0 ≤ sourceStrictWindowError B P hB μ X a n ∧
      sourceStrictWindowError B P hB μ X a n ≤
        OriginalIIDWindow.sourceWindowError B P hB μ X a n +
          (μ.real {ω | X 1 ω = 0}) ^ n /
            Shao.Probability.BrownianSup.probability B P hB (a n) := by
    filter_upwards [eventually_ge_atTop 1, ha.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
      hslow.eventually (eventually_gt_atTop 0)] with n hn ha1 hs
    have ha0 : 0 < a n := by
      have hr := Real.rpow_nonneg (Nat.cast_nonneg n) ((1 : ℝ) / 6)
      nlinarith
    simpa only [hz.2.2 n] using source_strict_window_bound B P hB μ X hX a n hn ha0 ha1
  exact squeeze_zero' (hevent.mono fun _ h => h.1) (hevent.mono fun _ h => h.2)
    (by simpa only [zero_add] using hsum)

-- A09: displayed literal M_n < x sqrt(Q_n); equality with A08 only on n>0.
theorem original_iid_strict_sSup_tendsto
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (μ : Measure ΩX) [IsProbabilityMeasure μ]
    (X : ℕ → ΩX → ℝ)
    (hX : ∀ i : ℕ, AEMeasurable (X (i + 1)) μ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hIdent : ∀ i : ℕ, IdentDistrib (X (i + 1)) (X 1) μ μ)
    (h3 : Integrable (fun ω => |X 1 ω| ^ 3) μ)
    (hmean : (∫ ω, X 1 ω ∂μ) = 0)
    (hsecond : 0 < ∫ ω, (X 1 ω) ^ 2 ∂μ)
    (a : ℕ → ℝ) (haAnti : Antitone a)
    (ha : Tendsto a atTop (𝓝 (0 : ℝ)))
    (hslow : Tendsto
      (fun n => a n * (n : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop) :
    Tendsto (fun n : ℕ => sSup ((fun x : ℝ =>
      |μ.real {ω | OriginalIIDWindow.sourceMaximum n X ω <
        x * Real.sqrt (OriginalIIDWindow.sourceEnergy n X ω)} /
        Shao.Probability.BrownianSup.probability B P hB x - 1|) '' Ioo (a n) 1))
      atTop (𝓝 (0 : ℝ)) := by
  have h := source_strict_window_ae_tendsto B P hB μ X hX hIndep hIdent
    h3 hmean hsecond a haAnti ha hslow
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  unfold sourceStrictWindowError
  simp_rw [source_strict_event_eq_max n hn X]

end Shao.OQ4.StrictIIDWindow
end
