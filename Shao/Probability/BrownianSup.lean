import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Rat.Encodable

/-!
# Actual Brownian supremum and finite Gaussian survival approximations

For a given standard real Brownian motion, this file constructs a measurable
version of the supremum of its absolute value on [0,1], identifies its weak
event with the full continuous-time event, and obtains its probability from
finite Gaussian cylinders. It does not assert a small-ball asymptotic.
-/

namespace Shao.Probability.BrownianSup

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

private def clampTime (r : ℝ) : ℝ≥0 :=
  ⟨max 0 (min 1 r), le_max_left _ _⟩

noncomputable def rationalTime (n : ℕ) : ℝ≥0 :=
  ⟨max 0 (min 1 (((Encodable.decode (α := ℚ) n).getD 0 : ℚ) : ℝ)),
    le_max_left _ _⟩

noncomputable def grid (n : ℕ) : Finset ℝ≥0 := by
  classical
  exact insert 0 ((Finset.range n).image rationalTime)

private theorem rationalTime_mem (n : ℕ) : rationalTime n ∈ Icc (0 : ℝ≥0) 1 := by
  constructor
  · exact bot_le
  · change max 0 (min 1 _) ≤ (1 : ℝ)
    exact max_le (by norm_num) (min_le_left _ _)

private theorem grid_mono : Monotone grid := by
  classical
  intro n m hnm
  unfold grid
  exact Finset.insert_subset_insert 0 (Finset.image_subset_image (Finset.range_mono hnm))

variable {Ω : Type*} [MeasurableSpace Ω]
variable (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω)

noncomputable def pathSup (ω : Ω) : ℝ :=
  sSup ((fun t : ℝ≥0 => |B t ω|) '' Icc 0 1)

noncomputable def traceSup (ω : Ω) : ℝ :=
  ⨆ n : ℕ, |B (rationalTime n) ω|

def fullStrip (x : ℝ) : Set Ω :=
  {ω | ∀ t ∈ Icc (0 : ℝ≥0) 1, |B t ω| ≤ x}

def finiteStrip (n : ℕ) (x : ℝ) : Set Ω :=
  {ω | ∀ t ∈ grid n, |B t ω| ≤ x}

noncomputable def gaussianFinite (n : ℕ) (x : ℝ) : ℝ :=
  (ProbabilityTheory.BrownianReal.projectiveFamily (grid n)).real
    {v | ∀ t, |v t| ≤ x}

private theorem trace_bound_iff {ω : Ω} (hc : Continuous (B · ω)) (x : ℝ) :
    (∀ n : ℕ, |B (rationalTime n) ω| ≤ x) ↔ ω ∈ fullStrip B x := by
  constructor
  · intro h t ht
    obtain ⟨q, _, _, hq⟩ := Real.exists_seq_rat_strictMono_tendsto (t : ℝ)
    have hclamp : Continuous clampTime := by
      unfold clampTime
      fun_prop
    have hf : Continuous (fun r : ℝ => |B (clampTime r) ω|) :=
      (hc.comp hclamp).abs
    have htclamp : clampTime (t : ℝ) = t := by
      apply Subtype.ext
      change max 0 (min 1 (t : ℝ)) = (t : ℝ)
      rw [min_eq_right (show (t : ℝ) ≤ 1 from ht.2)]
      exact max_eq_right t.2
    have hlim : Tendsto (fun n => |B (clampTime (q n : ℝ)) ω|) atTop
        (𝓝 |B t ω|) := by
      simpa only [htclamp, Function.comp_def] using (hf.tendsto (t : ℝ)).comp hq
    apply le_of_tendsto hlim
    apply Eventually.of_forall
    intro n
    simpa [rationalTime, clampTime, Encodable.encodek] using h (Encodable.encode (q n))
  · intro h n
    exact h _ (rationalTime_mem n)

private theorem path_bddAbove {ω : Ω} (hc : Continuous (B · ω)) :
    BddAbove ((fun t : ℝ≥0 => |B t ω|) '' Icc 0 1) :=
  (isCompact_Icc.image hc.abs).bddAbove

private theorem trace_bddAbove {ω : Ω} (hc : Continuous (B · ω)) :
    BddAbove (range (fun n : ℕ => |B (rationalTime n) ω|)) := by
  apply (path_bddAbove B hc).mono
  rintro _ ⟨n, rfl⟩
  exact ⟨rationalTime n, rationalTime_mem n, rfl⟩

private theorem traceSup_le_iff {ω : Ω} (hc : Continuous (B · ω)) (x : ℝ) :
    traceSup B ω ≤ x ↔ ω ∈ fullStrip B x := by
  rw [traceSup, ciSup_le_iff (trace_bddAbove B hc)]
  exact trace_bound_iff B hc x

private theorem traceSup_eq_pathSup {ω : Ω} (hc : Continuous (B · ω)) :
    traceSup B ω = pathSup B ω := by
  have hne : ((fun t : ℝ≥0 => |B t ω|) '' Icc 0 1).Nonempty :=
    ⟨|B 0 ω|, ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩⟩
  apply le_antisymm
  · apply ciSup_le
    intro n
    exact le_csSup (path_bddAbove B hc) ⟨rationalTime n, rationalTime_mem n, rfl⟩
  · apply (csSup_le_iff (path_bddAbove B hc) hne).2
    rintro _ ⟨t, ht, rfl⟩
    exact (traceSup_le_iff B hc _).1 le_rfl t ht

variable [IsProbabilityMeasure P]

theorem traceSup_aemeasurable (hB : IsBrownianReal B P) :
    AEMeasurable (traceSup B) P :=
  AEMeasurable.iSup (fun n => continuous_abs.measurable.comp_aemeasurable (hB.toIsPreBrownianReal.aemeasurable (rationalTime n)))

noncomputable def U (hB : IsBrownianReal B P) : Ω → ℝ :=
  (traceSup_aemeasurable B P hB).mk (traceSup B)

noncomputable def probability (hB : IsBrownianReal B P) (x : ℝ) : ℝ :=
  P.real {ω | U B P hB ω ≤ x}

theorem measurable_U (hB : IsBrownianReal B P) : Measurable (U B P hB) :=
  (traceSup_aemeasurable B P hB).measurable_mk

theorem U_ae_eq_pathSup (hB : IsBrownianReal B P) :
    U B P hB =ᵐ[P] pathSup B := by
  filter_upwards [(traceSup_aemeasurable B P hB).ae_eq_mk, hB.cont] with ω hω hc
  exact hω.symm.trans (traceSup_eq_pathSup B hc)

theorem U_le_ae_iff_fullStrip (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ x : ℝ, U B P hB ω ≤ x ↔ ω ∈ fullStrip B x := by
  filter_upwards [(traceSup_aemeasurable B P hB).ae_eq_mk, hB.cont] with ω hω hc
  intro x
  rw [show U B P hB ω = traceSup B ω from hω.symm]
  exact traceSup_le_iff B hc x

theorem probability_eq_fullStrip (hB : IsBrownianReal B P) (x : ℝ) :
    probability B P hB x = P.real (fullStrip B x) := by
  unfold probability Measure.real
  congr 1
  apply measure_congr
  filter_upwards [U_le_ae_iff_fullStrip B P hB] with ω hω
  exact propext (hω x)

theorem finiteStrip_nullMeasurable (hB : IsBrownianReal B P) (n : ℕ) (x : ℝ) :
    NullMeasurableSet (finiteStrip B n x) P := by
  have heq : finiteStrip B n x = ⋂ t ∈ grid n, {ω | |B t ω| ≤ x} := by
    ext ω
    simp [finiteStrip]
  rw [heq]
  apply Finset.nullMeasurableSet_biInter
  intro t _
  exact (continuous_abs.measurable.comp_aemeasurable (hB.toIsPreBrownianReal.aemeasurable t)).nullMeasurableSet_preimage
    measurableSet_Iic

theorem finiteStrip_probability_eq_gaussian (hB : IsBrownianReal B P) (n : ℕ) (x : ℝ) :
    P.real (finiteStrip B n x) = gaussianFinite n x := by
  have hC : MeasurableSet {v : grid n → ℝ | ∀ t, |v t| ≤ x} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun t =>
      measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply t)) measurable_const
  simpa [finiteStrip, gaussianFinite, Finset.forall_coe] using
    (hB.toIsPreBrownianReal.hasLaw (grid n)).measureReal_eq hC

private theorem finiteStrip_antitone (x : ℝ) : Antitone (fun n => finiteStrip B n x) := by
  intro n m hnm ω hω t ht
  exact hω t (grid_mono hnm ht)

private theorem fullStrip_ae_eq_iInter (hB : IsBrownianReal B P) (x : ℝ) :
    fullStrip B x =ᵐ[P] ⋂ n : ℕ, finiteStrip B n x := by
  classical
  filter_upwards [hB.cont] with ω hc
  apply propext
  constructor
  · intro h
    simp only [mem_iInter]
    intro n t ht
    have ht' : t ∈ Icc (0 : ℝ≥0) 1 := by
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact ⟨le_rfl, zero_le_one⟩
      · rcases Finset.mem_image.mp ht with ⟨k, _, rfl⟩
        exact rationalTime_mem k
    exact h t ht'
  · intro h
    apply (trace_bound_iff B hc x).1
    intro n
    have hn : rationalTime n ∈ grid (n + 1) := by
      unfold grid
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), rfl⟩
    exact (mem_iInter.mp h (n + 1)) _ hn

theorem tendsto_gaussianFinite (hB : IsBrownianReal B P) (x : ℝ) :
    Tendsto (fun n : ℕ => gaussianFinite n x) atTop
      (𝓝 (probability B P hB x)) := by
  have hlim := tendsto_measure_iInter_atTop
    (fun n => finiteStrip_nullMeasurable B P hB n x)
    (finiteStrip_antitone B x) ⟨0, measure_ne_top P _⟩
  have heq : P (⋂ n : ℕ, finiteStrip B n x) = P (fullStrip B x) :=
    measure_congr (fullStrip_ae_eq_iInter B P hB x).symm
  rw [heq] at hlim
  have hreal := (ENNReal.continuousAt_toReal (measure_ne_top P (fullStrip B x))).tendsto.comp hlim
  simpa only [Function.comp_def, ← measureReal_def,
    finiteStrip_probability_eq_gaussian B P hB,
    ← probability_eq_fullStrip B P hB x] using hreal

variable {Ω' : Type*} [MeasurableSpace Ω']
variable (B' : ℝ≥0 → Ω' → ℝ) (P' : Measure Ω') [IsProbabilityMeasure P']

theorem probability_eq_probability (hB : IsBrownianReal B P)
    (hB' : IsBrownianReal B' P') (x : ℝ) :
    probability B P hB x = probability B' P' hB' x :=
  tendsto_nhds_unique (tendsto_gaussianFinite B P hB x)
    (tendsto_gaussianFinite B' P' hB' x)

end Shao.Probability.BrownianSup

