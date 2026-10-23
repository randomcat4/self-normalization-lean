/-
AUTHOR177 COMPLETE EXHAUSTIVE PROPOSAL ONLY. NOT FROZEN / IMPLEMENTED / CHECKED.
Proposed file: Shao/OQ4/RandomDenominatorAsymptotic.lean
Inventory: 16 imports, 1 option, 6 transparent noncomputable definitions,
24 theorem heads (10 private, 14 public). No additional top-level declaration.
ZERO abbrev/opaque/structure/class/instance/universe/notation/macro/axiom.
Proof-local symbols in proof.md add no top-level API. Every value is given in full.
Every theorem is a complete head; no proof placeholder or implementation follows.
New helpers/imports/options or changed heads/values require parent freeze amendment.
-/

import Shao.OQ4.UniformConditionalEnergy
import Shao.OQ4.RandomDenominatorFarTail
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace Shao.OQ4.RandomDenominatorAsymptotic

open MeasureTheory Filter Set
open RademacherScalarBounds (lambda)
open RandomDenominatorFarTail (randomDenominatorEvent farMainTerm)
open UniformConditionalEnergy (energyCoshExcessIntegral)
open scoped BigOperators Topology

-- VALUE 1. Signed perturbation: d=-epsilon is the lower center.
noncomputable def centerHeight (n : ℕ) (h d : ℝ) : ℝ :=
  h * Real.sqrt (1 + d / ((n : ℝ) / h ^ 2))

-- VALUE 2. All indices1..ceil(t/epsilon), including harmless extra cover.
noncomputable def middleIndices (n : ℕ) (h ε : ℝ) : Finset ℕ :=
  Finset.Icc 1 (Nat.ceil (((n : ℝ) / h ^ 2) / ε))

-- VALUE 3. Actual deterministic wall supplied by the energy upper endpoint.
noncomputable def middleHeight (n : ℕ) (h ε : ℝ) (j : ℕ) : ℝ :=
  centerHeight n h (((j : ℝ) + 1) * ε)

-- VALUE 4. Actual random-wall event and strict-left/closed-right energy band.
noncomputable def middleLayer (n : ℕ) (h ε : ℝ) (j : ℕ) : Set (Shao.Path n) :=
  randomDenominatorEvent n h ∩
    {a | (n : ℝ) + (j : ℝ) * ε * h ^ 2 < Shao.energy a ∧
      Shao.energy a ≤ (n : ℝ) + ((j : ℝ) + 1) * ε * h ^ 2}

-- VALUE 5. Exactly the source middle event, without a deterministic surrogate.
noncomputable def middleEvent (n : ℕ) (h ε : ℝ) : Set (Shao.Path n) :=
  randomDenominatorEvent n h ∩
    {a | (n : ℝ) + ε * h ^ 2 < Shao.energy a ∧
      Shao.energy a < 2 * (n : ℝ)}

-- VALUE 6. Entire numerical geometric payment, no supremum or error sequence.
noncomputable def middleSumConstant (s ε : ℝ) : ℝ :=
  8 * Real.exp (lambda * ε) * Real.exp (-(s - lambda) * ε) /
    ((1 - Real.exp (-s * ε)) ^ 2 *
      (1 - Real.exp (-(s - lambda) * ε)))

-- H01 PRIVATE. Pays the FAR square-integrability call from original h3 alone.
private theorem lower_moments_integrable
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν) :
    Integrable (fun x : ℝ => x) ν ∧
      Integrable (fun x : ℝ => x ^ 2) ν := by
  have hdom : Integrable (fun x : ℝ => 1 + |x| ^ 3) ν :=
    (integrable_const (1 : ℝ)).add h3
  have hsmall (r : ℝ) (hr : 0 ≤ r) : r ≤ 1 + r ^ 3 ∧ r ^ 2 ≤ 1 + r ^ 3 := by
    by_cases hr1 : r ≤ 1
    · have hp := mul_nonneg hr (sub_nonneg.mpr hr1)
      have hc : 0 ≤ r ^ 3 := pow_nonneg hr 3
      constructor <;> nlinarith
    · have hlarge : 1 ≤ r := (lt_of_not_ge hr1).le
      have hp := mul_nonneg hr (sub_nonneg.mpr hlarge)
      have hq := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hlarge)
      constructor <;> nlinarith
  constructor
  · exact hdom.mono' measurable_id.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, id_eq] using (hsmall |x| (abs_nonneg x)).1)
  · exact hdom.mono' (by fun_prop)
      (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_pow, id_eq] using (hsmall |x| (abs_nonneg x)).2)

-- H02 PRIVATE. All roots squared only after radicand nonnegativity is paid.
private theorem centerHeight_identities
    (n : ℕ) (hn : 0 < n) (h d : ℝ) (hh : 0 < h)
    (hd : 0 ≤ 1 + d / ((n : ℝ) / h ^ 2)) :
    0 ≤ centerHeight n h d ∧
      centerHeight n h d ^ 2 =
        h ^ 2 * (1 + d / ((n : ℝ) / h ^ 2)) ∧
      centerHeight n h d =
        h / Real.sqrt (n : ℝ) * Real.sqrt ((n : ℝ) + d * h ^ 2) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnz : (n : ℝ) ≠ 0 := hnR.ne'
  have hhz : h ≠ 0 := hh.ne'
  have hrad : (n : ℝ) + d * h ^ 2 =
      (n : ℝ) * (1 + d / ((n : ℝ) / h ^ 2)) := by
    field_simp [hnz, hhz]
    <;> ring
  have hrad0 : 0 ≤ (n : ℝ) + d * h ^ 2 := by
    rw [hrad]
    exact mul_nonneg hnR.le hd
  have hc : 0 ≤ centerHeight n h d :=
    mul_nonneg hh.le (Real.sqrt_nonneg _)
  have hcsq : centerHeight n h d ^ 2 =
      h ^ 2 * (1 + d / ((n : ℝ) / h ^ 2)) := by
    dsimp only [centerHeight]
    rw [mul_pow, Real.sq_sqrt hd]
  refine ⟨hc, hcsq, ?_⟩
  have hr : 0 ≤ h / Real.sqrt (n : ℝ) * Real.sqrt ((n : ℝ) + d * h ^ 2) :=
    mul_nonneg (div_nonneg hh.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  apply (sq_eq_sq₀ hc hr).mp
  rw [hcsq, mul_pow, div_pow, Real.sq_sqrt hnR.le, Real.sq_sqrt hrad0, hrad]
  field_simp [hnz, hhz]
  <;> ring

-- H03 PRIVATE. A scalar finite window, valid for either center sign.
private theorem centerHeight_window
    (n : ℕ) (hn : 0 < n) (h d : ℝ) (hh : 0 < h)
    (hd : 2 * |d| ≤ (n : ℝ) / h ^ 2) :
    h / 2 ≤ centerHeight n h d ∧ centerHeight n h d ≤ 2 * h := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have ht : 0 < (n : ℝ) / h ^ 2 := div_pos hnR (sq_pos_of_pos hh)
  have hdl : -((n : ℝ) / h ^ 2) / 2 ≤ d := by
    linarith [neg_abs_le d]
  have hdu : d ≤ ((n : ℝ) / h ^ 2) / 2 := by
    linarith [le_abs_self d]
  have hratio : (1 / 2 : ℝ) ≤ 1 + d / ((n : ℝ) / h ^ 2) ∧
      1 + d / ((n : ℝ) / h ^ 2) ≤ 3 / 2 := by
    constructor
    · have hquot : -(1 / 2 : ℝ) ≤ d / ((n : ℝ) / h ^ 2) :=
        (le_div_iff₀ ht).mpr (by linarith)
      linarith
    · have hquot : d / ((n : ℝ) / h ^ 2) ≤ (1 / 2 : ℝ) :=
        (div_le_iff₀ ht).mpr (by linarith)
      linarith
  obtain ⟨hc, hsq, _⟩ := centerHeight_identities n hn h d hh (by linarith)
  constructor
  · apply (sq_le_sq₀ (by positivity : 0 ≤ h / 2) hc).mp
    rw [hsq]
    have hp := mul_le_mul_of_nonneg_left hratio.1 (sq_nonneg h)
    nlinarith
  · apply (sq_le_sq₀ hc (by positivity : 0 ≤ 2 * h)).mp
    rw [hsq]
    have hp := mul_le_mul_of_nonneg_left hratio.2 (sq_nonneg h)
    nlinarith

-- H04 PUBLIC. Exact weak-energy endpoints and the same literal E throughout.
theorem center_event_inclusions
    (n : ℕ) (hn : 0 < n) (h ε : ℝ) (hh : 0 < h) (hε : 0 < ε)
    (ht : 2 * ε ≤ (n : ℝ) / h ^ 2) :
    ((@Shao.closedStrip n (centerHeight n h (-ε))) ∩
      {a : Shao.Path n | (n : ℝ) - ε * h ^ 2 ≤ Shao.energy a}) ⊆
        randomDenominatorEvent n h ∧
      (randomDenominatorEvent n h ∩
        {a : Shao.Path n | Shao.energy a ≤ (n : ℝ) + ε * h ^ 2}) ⊆
          (@Shao.closedStrip n (centerHeight n h ε))
    := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have htpos : 0 < (n : ℝ) / h ^ 2 := div_pos hnR (sq_pos_of_pos hh)
  have he : ε / ((n : ℝ) / h ^ 2) ≤ (1 / 2 : ℝ) :=
    (div_le_iff₀ htpos).mpr (by linarith)
  have hminus : 0 ≤ 1 + -ε / ((n : ℝ) / h ^ 2) := by
    rw [neg_div]
    linarith
  have hplus : 0 ≤ 1 + ε / ((n : ℝ) / h ^ 2) := by positivity
  have hcminus := (centerHeight_identities n hn h (-ε) hh hminus).2.2
  have hcplus := (centerHeight_identities n hn h ε hh hplus).2.2
  have hfactor : 0 ≤ h / Real.sqrt (n : ℝ) := by positivity
  constructor
  · intro a ha
    change ∀ k : ℕ, k ≤ n → |Shao.prefixSum a k| ≤
      h / Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy a)
    intro k hk
    have hsqrt : Real.sqrt ((n : ℝ) + -ε * h ^ 2) ≤ Real.sqrt (Shao.energy a) :=
      Real.sqrt_le_sqrt (by
        have henergy : (n : ℝ) - ε * h ^ 2 ≤ Shao.energy a := ha.2
        linarith)
    exact (ha.1 k hk).trans (by
      rw [hcminus]
      exact mul_le_mul_of_nonneg_left hsqrt hfactor)
  · intro a ha
    change ∀ k : ℕ, k ≤ n → |Shao.prefixSum a k| ≤ centerHeight n h ε
    intro k hk
    have hsqrt : Real.sqrt (Shao.energy a) ≤ Real.sqrt ((n : ℝ) + ε * h ^ 2) :=
      Real.sqrt_le_sqrt ha.2
    exact (ha.1 k hk).trans (by
      rw [hcplus]
      exact mul_le_mul_of_nonneg_left hsqrt hfactor)

-- H05 PUBLIC. Strict deviation; no zero-energy path is deleted.
theorem center_lower_probability_bound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 0 < n) (h ε : ℝ) (hh : 0 < h) (hε : 0 < ε)
    (ht : 2 * ε ≤ (n : ℝ) / h ^ 2) :
    (Measure.pi (fun _ : Fin n => ν)).real
        (@Shao.closedStrip n (centerHeight n h (-ε))) -
      (Measure.pi (fun _ : Fin n => ν)).real
        ((@Shao.closedStrip n (centerHeight n h (-ε))) ∩
          {a : Shao.Path n | ε * h ^ 2 < |Shao.energy a - (n : ℝ)|}) ≤
      (Measure.pi (fun _ : Fin n => ν)).real (randomDenominatorEvent n h) := by
  let μ : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ν)
  let A : Set (Shao.Path n) := Shao.closedStrip (centerHeight n h (-ε))
  let D : Set (Shao.Path n) := A ∩
    {a : Shao.Path n | ε * h ^ 2 < |Shao.energy a - (n : ℝ)|}
  have hsub : A ⊆ randomDenominatorEvent n h ∪ D := by
    intro a ha
    by_cases he : a ∈ randomDenominatorEvent n h
    · exact Or.inl he
    · apply Or.inr
      refine ⟨ha, ?_⟩
      have hnot : ¬ (n : ℝ) - ε * h ^ 2 ≤ Shao.energy a := by
        intro hQ
        exact he ((center_event_inclusions n hn h ε hh hε ht).1 ⟨ha, hQ⟩)
      have hQ := lt_of_not_ge hnot
      exact lt_of_lt_of_le (by linarith : ε * h ^ 2 < -(Shao.energy a - (n : ℝ)))
        (neg_le_abs _)
  have hbound : μ.real A ≤ μ.real (randomDenominatorEvent n h) + μ.real D :=
    (measureReal_mono hsub).trans (measureReal_union_le _ _)
  change μ.real A - μ.real D ≤ μ.real (randomDenominatorEvent n h)
  linarith

-- H06 PUBLIC. Center + entire middle + entire FAR, including Q=2n in FAR.
theorem randomDenominator_probability_upper_bound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 0 < n) (h ε : ℝ) (hh : 0 < h) (hε : 0 < ε)
    (ht : 2 * ε ≤ (n : ℝ) / h ^ 2) :
    (Measure.pi (fun _ : Fin n => ν)).real (randomDenominatorEvent n h) ≤
      (Measure.pi (fun _ : Fin n => ν)).real
          (@Shao.closedStrip n (centerHeight n h ε)) +
        (Measure.pi (fun _ : Fin n => ν)).real (middleEvent n h ε) +
        (Measure.pi (fun _ : Fin n => ν)).real
          (randomDenominatorEvent n h ∩
            {a : Shao.Path n | 2 * (n : ℝ) ≤ Shao.energy a})
    := by
  let μ : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ν)
  let A : Set (Shao.Path n) := Shao.closedStrip (centerHeight n h ε)
  let F : Set (Shao.Path n) := randomDenominatorEvent n h ∩
    {a : Shao.Path n | 2 * (n : ℝ) ≤ Shao.energy a}
  have hsub : randomDenominatorEvent n h ⊆ (A ∪ middleEvent n h ε) ∪ F := by
    intro a ha
    by_cases hc : Shao.energy a ≤ (n : ℝ) + ε * h ^ 2
    · exact Or.inl (Or.inl ((center_event_inclusions n hn h ε hh hε ht).2 ⟨ha, hc⟩))
    · by_cases hf : 2 * (n : ℝ) ≤ Shao.energy a
      · exact Or.inr ⟨ha, hf⟩
      · exact Or.inl (Or.inr ⟨ha, lt_of_not_ge hc, lt_of_not_ge hf⟩)
  change μ.real (randomDenominatorEvent n h) ≤
    μ.real A + μ.real (middleEvent n h ε) + μ.real F
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
    (add_le_add (measureReal_union_le A (middleEvent n h ε)) (le_refl (μ.real F))))

-- H07 PRIVATE. Witness ceil(w)-1; integer w is sent to the preceding layer.
private theorem ceil_layer_index (w T : ℝ) (hw : 1 < w) (hwT : w < T) :
    ∃ j ∈ Finset.Icc 1 (Nat.ceil T), (j : ℝ) < w ∧ w ≤ (j : ℝ) + 1 := by
  have hc2 : 2 ≤ Nat.ceil w := by
    exact (Nat.add_one_le_ceil_iff (n := 1)).mpr (by simpa using hw)
  have hc0 : Nat.ceil w ≠ 0 := by omega
  have hpred : Nat.ceil w - 1 + 1 = Nat.ceil w := Nat.sub_add_cancel (by omega)
  have hcast : ((Nat.ceil w - 1 : ℕ) : ℝ) + 1 = (Nat.ceil w : ℝ) := by
    exact_mod_cast hpred
  have hceil := (Nat.ceil_eq_iff hc0).mp (rfl : Nat.ceil w = Nat.ceil w)
  refine ⟨Nat.ceil w - 1, Finset.mem_Icc.mpr ⟨by omega, ?_⟩, hceil.1, ?_⟩
  · exact (Nat.sub_le _ _).trans (Nat.ceil_le_ceil hwT.le)
  · rw [hcast]
    exact hceil.2

-- H08 PUBLIC. WHOLE middle event, finite at every actual n,h,epsilon.
theorem middle_event_finite_cover
    (n : ℕ) (hn : 0 < n) (h ε : ℝ) (hh : 0 < h) (hε : 0 < ε) :
    middleEvent n h ε ⊆ ⋃ j ∈ middleIndices n h ε, middleLayer n h ε j := by
  intro a ha
  let w : ℝ := (Shao.energy a - (n : ℝ)) / (ε * h ^ 2)
  have hden : 0 < ε * h ^ 2 := mul_pos hε (sq_pos_of_pos hh)
  have hw : 1 < w := (lt_div_iff₀ hden).mpr (by
    have hl : (n : ℝ) + ε * h ^ 2 < Shao.energy a := ha.2.1
    linarith)
  have hwT : w < ((n : ℝ) / h ^ 2) / ε := by
    change (Shao.energy a - (n : ℝ)) / (ε * h ^ 2) < ((n : ℝ) / h ^ 2) / ε
    apply (div_lt_iff₀ hden).mpr
    have hid : (((n : ℝ) / h ^ 2) / ε) * (ε * h ^ 2) = (n : ℝ) := by
      field_simp [hε.ne', hh.ne']
    rw [hid]
    linarith [ha.2.2]
  obtain ⟨j, hj, hjw, hwj⟩ := ceil_layer_index w (((n : ℝ) / h ^ 2) / ε) hw hwT
  apply Set.mem_iUnion.mpr
  refine ⟨j, Set.mem_iUnion.mpr ⟨hj, ?_⟩⟩
  refine ⟨ha.1, ?_, ?_⟩
  · have hl := (lt_div_iff₀ hden).mp hjw
    nlinarith
  · have hu := (div_le_iff₀ hden).mp hwj
    nlinarith

-- H09 PUBLIC. One window for every enlarged finite index, no j*epsilon<t guard.
theorem middleHeight_geometry
    (n : ℕ) (hn : 0 < n) (h ε : ℝ) (hh : 0 < h) (hε : 0 < ε)
    (ht : ε ≤ (n : ℝ) / h ^ 2) (j : ℕ) (hj : j ∈ middleIndices n h ε) :
    h ≤ middleHeight n h ε j ∧ middleHeight n h ε j ≤ 2 * h ∧
      middleHeight n h ε j ^ 2 =
        h ^ 2 * (1 + ((j : ℝ) + 1) * ε / ((n : ℝ) / h ^ 2)) ∧
      (n : ℝ) / h ^ 2 - (n : ℝ) / middleHeight n h ε j ^ 2 ≤
        ((j : ℝ) + 1) * ε
    := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let t : ℝ := (n : ℝ) / h ^ 2
  let d : ℝ := ((j : ℝ) + 1) * ε
  have htpos : 0 < t := div_pos hnR (sq_pos_of_pos hh)
  have hdpos : 0 < d := by dsimp only [d]; positivity
  have hjN : j ≤ Nat.ceil (t / ε) := (Finset.mem_Icc.mp hj).2
  have hceil : (Nat.ceil (t / ε) : ℝ) < t / ε + 1 :=
    Nat.ceil_lt_add_one (div_nonneg htpos.le hε.le)
  have hjcast : (j : ℝ) ≤ (Nat.ceil (t / ε) : ℝ) := by exact_mod_cast hjN
  have hd : d < t + 2 * ε := by
    have hm := mul_lt_mul_of_pos_right (show (j : ℝ) + 1 < t / ε + 2 by linarith) hε
    dsimp only [d]
    have hid : (t / ε + 2) * ε = t + 2 * ε := by field_simp [hε.ne']
    rw [hid] at hm
    exact hm
  have hd3 : d ≤ 3 * t := by change ε ≤ t at ht; linarith
  have hu : 0 ≤ 1 + d / t := by positivity
  obtain ⟨hb, hbsq, _⟩ := centerHeight_identities n hn h d hh hu
  have hbsq' : middleHeight n h ε j ^ 2 = h ^ 2 * (1 + d / t) := hbsq
  have hlow : h ≤ middleHeight n h ε j := by
    apply (sq_le_sq₀ hh.le hb).mp
    change h ^ 2 ≤ middleHeight n h ε j ^ 2
    rw [hbsq']
    have hp := mul_nonneg (sq_nonneg h) (div_nonneg hdpos.le htpos.le)
    nlinarith
  have hu4 : 1 + d / t ≤ 4 := by
    have hdquot : d / t ≤ 3 := (div_le_iff₀ htpos).mpr (by linarith)
    linarith
  have hhigh : middleHeight n h ε j ≤ 2 * h := by
    apply (sq_le_sq₀ hb (by positivity : 0 ≤ 2 * h)).mp
    change middleHeight n h ε j ^ 2 ≤ (2 * h) ^ 2
    rw [hbsq']
    have hp := mul_le_mul_of_nonneg_left hu4 (sq_nonneg h)
    nlinarith
  refine ⟨hlow, hhigh, hbsq', ?_⟩
  have hupos : 0 < 1 + d / t := by positivity
  have hid : (n : ℝ) / middleHeight n h ε j ^ 2 = t / (1 + d / t) := by
    rw [hbsq']
    dsimp only [t]
    field_simp [hh.ne', hnR.ne', hupos.ne']
    <;> ring
  change t - (n : ℝ) / middleHeight n h ε j ^ 2 ≤ d
  rw [hid]
  have hid2 : t - t / (1 + d / t) = d / (1 + d / t) := by
    field_simp [htpos.ne', hupos.ne']
    <;> ring
  rw [hid2]
  apply (div_le_iff₀ hupos).mpr
  have hp := mul_nonneg hdpos.le (div_nonneg hdpos.le htpos.le)
  nlinarith

-- H10 PUBLIC. Finite actual random-wall containment and original h² threshold.
theorem middleLayer_subset_deviation
    (n : ℕ) (hn : 0 < n) (h ε : ℝ) (hh : 0 < h) (hε : 0 < ε)
    (j : ℕ) (hj : 1 ≤ j) :
    middleLayer n h ε j ⊆
      (@Shao.closedStrip n (middleHeight n h ε j)) ∩
        {a : Shao.Path n |
          (j : ℝ) * ε * h ^ 2 < |Shao.energy a - (n : ℝ)|}
    := by
  intro a ha
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have htpos : 0 < (n : ℝ) / h ^ 2 := div_pos hnR (sq_pos_of_pos hh)
  have hrad : 0 ≤ 1 + (((j : ℝ) + 1) * ε) / ((n : ℝ) / h ^ 2) := by positivity
  have hb := (centerHeight_identities n hn h (((j : ℝ) + 1) * ε) hh hrad).2.2
  refine ⟨?_, ?_⟩
  · intro k hk
    exact (ha.1 k hk).trans (by
      change h / Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy a) ≤ middleHeight n h ε j
      change _ ≤ centerHeight n h (((j : ℝ) + 1) * ε)
      rw [hb]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ha.2.2) (by positivity))
  · have hl : (j : ℝ) * ε * h ^ 2 < Shao.energy a - (n : ℝ) := by
      linarith [ha.2.1]
    exact hl.trans_le (le_abs_self _)

-- H11 PUBLIC. No desired survival/energy limit or survival positivity premise.
theorem middleLayer_markov_bound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 0 < n) (h ε s : ℝ)
    (hh : 0 < h) (hε : 0 < ε) (hs : 0 < s) (j : ℕ) (hj : 1 ≤ j) :
    0 < (Real.exp (s * ((j : ℝ) * ε)) +
      Real.exp (-(s * ((j : ℝ) * ε)))) / 2 - 1 ∧
      ((Real.exp (s * ((j : ℝ) * ε)) +
        Real.exp (-(s * ((j : ℝ) * ε)))) / 2 - 1) *
          (Measure.pi (fun _ : Fin n => ν)).real (middleLayer n h ε j) ≤
        energyCoshExcessIntegral ν n (middleHeight n h ε j) h s
    := by
  have hjR : 0 < (j : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hj)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have htpos : 0 < (n : ℝ) / h ^ 2 := div_pos hnR (sq_pos_of_pos hh)
  have hrad : 0 < 1 + (((j : ℝ) + 1) * ε) / ((n : ℝ) / h ^ 2) := by positivity
  have hb : 0 < middleHeight n h ε j := by
    exact mul_pos hh (Real.sqrt_pos.mpr hrad)
  have hf := UniformConditionalEnergy.energy_deviation_finite_bound
    ν n (middleHeight n h ε j) h s ((j : ℝ) * ε) hb hh hs (mul_pos hjR hε)
  refine ⟨hf.1, ?_⟩
  exact (mul_le_mul_of_nonneg_left
    (measureReal_mono (middleLayer_subset_deviation n hn h ε hh hε j hj)) hf.1.le).trans hf.2

-- H12 PRIVATE. Literal positive exp-pair denominator and the complete q^j bound.
private theorem exp_pair_geometric_majorant
    (s ε : ℝ) (hs : lambda < s) (hε : 0 < ε) (j : ℕ) (hj : 1 ≤ j) :
    0 < (Real.exp (s * ((j : ℝ) * ε)) +
      Real.exp (-(s * ((j : ℝ) * ε)))) / 2 - 1 ∧
      Real.exp (lambda * (((j : ℝ) + 1) * ε)) /
          ((Real.exp (s * ((j : ℝ) * ε)) +
            Real.exp (-(s * ((j : ℝ) * ε)))) / 2 - 1) ≤
        (2 * Real.exp (lambda * ε) / (1 - Real.exp (-s * ε)) ^ 2) *
          Real.exp (-(s - lambda) * ε) ^ j
    := by
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  have hs0 : 0 < s := hlambda.trans hs
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hjpos : 0 < (j : ℝ) := lt_of_lt_of_le zero_lt_one hjR
  let a : ℝ := s * ((j : ℝ) * ε)
  let u : ℝ := 1 - Real.exp (-s * ε)
  let D : ℝ := (Real.exp a + Real.exp (-a)) / 2 - 1
  let R : ℝ := (2 * Real.exp (lambda * ε) / u ^ 2) *
    Real.exp (-(s - lambda) * ε) ^ j
  have ha : 0 < a := by dsimp only [a]; positivity
  have hu : 0 < u := by
    dsimp only [u]
    have he : Real.exp (-s * ε) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (by nlinarith)
    rw [Real.exp_zero] at he
    linarith
  have hDpos : 0 < D := by
    dsimp only [D]
    have hstrict := Real.add_one_lt_exp ha.ne'
    nlinarith [Real.add_one_le_exp (-a)]
  have hidentity : D = Real.exp a * (1 - Real.exp (-a)) ^ 2 / 2 := by
    dsimp only [D]
    rw [Real.exp_neg]
    field_simp [(Real.exp_pos a).ne']
    <;> ring
  have hu_le : u ≤ 1 - Real.exp (-a) := by
    have harg : -a ≤ -s * ε := by
      dsimp only [a]
      have hm := mul_le_mul_of_nonneg_right hjR (mul_nonneg hs0.le hε.le)
      nlinarith
    have he := Real.exp_le_exp.mpr harg
    dsimp only [u]
    linarith
  have hv : 0 ≤ 1 - Real.exp (-a) := hu.le.trans hu_le
  have hsq : u ^ 2 ≤ (1 - Real.exp (-a)) ^ 2 :=
    (sq_le_sq₀ hu.le hv).mpr hu_le
  have hDlower : Real.exp a * u ^ 2 / 2 ≤ D := by
    rw [hidentity]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le) (by norm_num)
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hproduct : R * (Real.exp a * u ^ 2 / 2) =
      Real.exp (lambda * (((j : ℝ) + 1) * ε)) := by
    calc
      _ = Real.exp (lambda * ε) *
          (Real.exp (-(s - lambda) * ε) ^ j * Real.exp a) := by
        dsimp only [R]
        field_simp [hu.ne']
        <;> ring
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp only [a]
        ring
  refine ⟨hDpos, ?_⟩
  change Real.exp (lambda * (((j : ℝ) + 1) * ε)) / D ≤ R
  apply (div_le_iff₀ hDpos).mpr
  calc
    _ = R * (Real.exp a * u ^ 2 / 2) := hproduct.symm
    _ ≤ R * D := mul_le_mul_of_nonneg_left hDlower hR

-- H13 PRIVATE. Finite arbitrary positive-index set; no infinite series API.
private theorem finite_positive_geometric_sum_bound
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (S : Finset ℕ) (hS : ∀ j ∈ S, 1 ≤ j) :
    (∑ j ∈ S, q ^ j) ≤ q / (1 - q) := by
  classical
  let N : ℕ := ∑ j ∈ S, j
  have hSbound : S ⊆ Finset.Icc 1 N := by
    intro j hj
    refine Finset.mem_Icc.mpr ⟨hS j hj, ?_⟩
    exact Finset.single_le_sum (f := fun i : ℕ => i) (fun i _ => Nat.zero_le i) hj
  have hgeom (M : ℕ) :
      (1 - q) * (∑ j ∈ Finset.range M, q ^ j) = 1 - q ^ M := by
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith
  have hset : insert 0 (Finset.Icc 1 N) = Finset.range (N + 1) := by
    ext j
    simp only [Finset.mem_insert, Finset.mem_Icc, Finset.mem_range]
    omega
  have hzero : 0 ∉ Finset.Icc 1 N := by simp
  have hg := hgeom (N + 1)
  rw [← hset, Finset.sum_insert hzero] at hg
  simp only [pow_zero] at hg
  have hsum : (∑ j ∈ S, q ^ j) ≤ ∑ j ∈ Finset.Icc 1 N, q ^ j :=
    Finset.sum_le_sum_of_subset_of_nonneg hSbound (fun _ _ _ => pow_nonneg hq _)
  apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
  have hm := mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr hq1.le)
  have hp : 0 ≤ q ^ (N + 1) := pow_nonneg hq _
  nlinarith

-- H14 PUBLIC. Strict positivity pays all finite constant divisions.
theorem middleSumConstant_pos (s ε : ℝ) (hs : lambda < s) (hε : 0 < ε) :
    0 < middleSumConstant s ε := by
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  have hs0 : 0 < s := hlambda.trans hs
  have hu : 0 < 1 - Real.exp (-s * ε) := by
    have he : Real.exp (-s * ε) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (by nlinarith)
    rw [Real.exp_zero] at he
    linarith
  have hq : 0 < 1 - Real.exp (-(s - lambda) * ε) := by
    have he : Real.exp (-(s - lambda) * ε) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (by nlinarith)
    rw [Real.exp_zero] at he
    linarith
  dsimp only [middleSumConstant]
  exact div_pos (mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) (Real.exp_pos _))
    (mul_pos (sq_pos_of_pos hu) hq)

-- H15 PUBLIC. Finite local actual controls only; the root theorem supplies them.
theorem middle_finite_bound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 0 < n) (h ε s η : ℝ)
    (hh : 0 < h) (hε : 0 < ε) (hs : lambda < s) (hη : 0 ≤ η)
    (ht : ε ≤ (n : ℝ) / h ^ 2)
    (hG : 0 < (Measure.pi (fun _ : Fin n => ν)).real (@Shao.closedStrip n h))
    (hcontrols : ∀ j ∈ middleIndices n h ε,
      0 < (Measure.pi (fun _ : Fin n => ν)).real
          (@Shao.closedStrip n (middleHeight n h ε j)) ∧
        energyCoshExcessIntegral ν n (middleHeight n h ε j) h s /
            (Measure.pi (fun _ : Fin n => ν)).real
              (@Shao.closedStrip n (middleHeight n h ε j)) ≤ η ∧
        (Measure.pi (fun _ : Fin n => ν)).real
              (@Shao.closedStrip n (middleHeight n h ε j)) /
            (Measure.pi (fun _ : Fin n => ν)).real (@Shao.closedStrip n h) ≤
          4 * Real.exp (lambda * (((j : ℝ) + 1) * ε))) :
    (Measure.pi (fun _ : Fin n => ν)).real (middleEvent n h ε) /
        (Measure.pi (fun _ : Fin n => ν)).real (@Shao.closedStrip n h) ≤
      η * middleSumConstant s ε
    := by
  classical
  let μ : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ν)
  haveI : IsProbabilityMeasure μ := by dsimp only [μ]; infer_instance
  let G : ℝ := μ.real (@Shao.closedStrip n h)
  let S : Finset ℕ := middleIndices n h ε
  let u : ℝ := 1 - Real.exp (-s * ε)
  let q : ℝ := Real.exp (-(s - lambda) * ε)
  let C : ℝ := 2 * Real.exp (lambda * ε) / u ^ 2
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  have hs0 : 0 < s := hlambda.trans hs
  have hu : 0 < u := by
    dsimp only [u]
    have he : Real.exp (-s * ε) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (by nlinarith)
    rw [Real.exp_zero] at he
    linarith
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp only [q]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hGpos : 0 < G := hG
  have hlayer (j : ℕ) (hj : j ∈ S) :
      μ.real (middleLayer n h ε j) / G ≤ η * 4 * C * q ^ j := by
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    obtain ⟨hGj, hJ, hR⟩ := hcontrols j hj
    have hf := middleLayer_markov_bound ν n hn h ε s hh hε hs0 j hj1
    let D : ℝ := (Real.exp (s * ((j : ℝ) * ε)) +
      Real.exp (-(s * ((j : ℝ) * ε)))) / 2 - 1
    let e : ℝ := Real.exp (lambda * (((j : ℝ) + 1) * ε))
    have hD : 0 < D := hf.1
    have hJbound : energyCoshExcessIntegral ν n (middleHeight n h ε j) h s ≤
        η * μ.real (@Shao.closedStrip n (middleHeight n h ε j)) :=
      (div_le_iff₀ hGj).mp hJ
    have hGb : μ.real (@Shao.closedStrip n (middleHeight n h ε j)) ≤ 4 * e * G :=
      (div_le_iff₀ hGpos).mp hR
    have hprod : D * μ.real (middleLayer n h ε j) ≤ η * (4 * e * G) :=
      hf.2.trans (hJbound.trans (mul_le_mul_of_nonneg_left hGb hη))
    have hratio : μ.real (middleLayer n h ε j) / G ≤ η * 4 * (e / D) := by
      apply (div_le_iff₀ hGpos).mpr
      have hcmp : μ.real (middleLayer n h ε j) * D ≤
          (η * 4 * (e / D) * G) * D := by
        calc
          μ.real (middleLayer n h ε j) * D = D * μ.real (middleLayer n h ε j) := by ring
          _ ≤ η * (4 * e * G) := hprod
          _ = (η * 4 * (e / D) * G) * D := by
            field_simp [hD.ne']
            <;> ring
      by_contra hnot
      have hpositive := mul_pos (sub_pos.mpr (lt_of_not_ge hnot)) hD
      nlinarith [hcmp]
    have hmajor : e / D ≤ C * q ^ j :=
      (exp_pair_geometric_majorant s ε hs hε j hj1).2
    calc
      _ ≤ η * 4 * (e / D) := hratio
      _ ≤ η * 4 * (C * q ^ j) :=
        mul_le_mul_of_nonneg_left hmajor (mul_nonneg hη (by norm_num))
      _ = η * 4 * C * q ^ j := by ring
  have hsum : μ.real (middleEvent n h ε) / G ≤
      ∑ j ∈ S, μ.real (middleLayer n h ε j) / G := by
    calc
      _ ≤ μ.real (⋃ j ∈ S, middleLayer n h ε j) / G :=
        div_le_div_of_nonneg_right
          (measureReal_mono (h₂ := measure_ne_top μ _)
            (middle_event_finite_cover n hn h ε hh hε)) hGpos.le
      _ ≤ (∑ j ∈ S, μ.real (middleLayer n h ε j)) / G :=
        div_le_div_of_nonneg_right (measureReal_biUnion_finset_le S _) hGpos.le
      _ = _ := by rw [Finset.sum_div]
  have hgeom : (∑ j ∈ S, q ^ j) ≤ q / (1 - q) :=
    finite_positive_geometric_sum_bound q hq0 hq1 S
      (fun j hj => (Finset.mem_Icc.mp hj).1)
  change μ.real (middleEvent n h ε) / G ≤ η * middleSumConstant s ε
  calc
    _ ≤ ∑ j ∈ S, μ.real (middleLayer n h ε j) / G := hsum
    _ ≤ ∑ j ∈ S, η * 4 * C * q ^ j := Finset.sum_le_sum hlayer
    _ = (η * 4 * C) * ∑ j ∈ S, q ^ j := by rw [Finset.mul_sum]
    _ ≤ (η * 4 * C) * (q / (1 - q)) :=
      mul_le_mul_of_nonneg_left hgeom (mul_nonneg (mul_nonneg hη (by norm_num)) hC)
    _ = η * middleSumConstant s ε := by
      dsimp only [C, u, q, middleSumConstant]
      field_simp [hu.ne', (sub_pos.mpr hq1).ne']
      <;> ring

-- H16 PRIVATE. Eventual finite signs derived, never added all-index assumptions.
private theorem eventual_finite_conditions
    (n : ℕ → ℕ) (h : ℕ → ℝ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun k => (n k : ℝ) / h k ^ 2) atTop atTop)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, 0 < n k ∧ 0 < h k ∧ 2 * ε ≤ (n k : ℝ) / h k ^ 2 := by
  filter_upwards [hinfty.eventually_gt_atTop 0,
    hlong.eventually_ge_atTop (2 * ε)] with k hk ht
  have hn : 0 < n k := by
    by_contra hn
    have hz : n k = 0 := Nat.eq_zero_of_not_pos hn
    simp only [hz, Nat.cast_zero, zero_div] at ht
    linarith
  exact ⟨hn, hk, ht⟩

-- H17 PRIVATE. Calls actual public175 K controls, not its private K adapter.
private theorem closedStrip_relative_main_tendsto
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun k => (n k : ℝ) / h k ^ 2) atTop atTop)
    (hshort : Tendsto (fun k => (n k : ℝ) / h k ^ 3) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun k =>
      (Measure.pi (fun _ : Fin (n k) => ν)).real
          (@Shao.closedStrip (n k) (h k)) / farMainTerm (n k) (h k))
      atTop (𝓝 (1 : ℝ))
    := by
  have hm (N : ℕ) (b : ℝ) :
      (4 / Real.pi) * Real.exp (-lambda * (N : ℝ) / b ^ 2) = farMainTerm N b := by
    dsimp only [farMainTerm, lambda]
    congr 1
    congr 1
    ring
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hc := UniformConditionalEnergy.uniform_closedStrip_energy_controls
    ν h3 hmean hsecond h n hinfty hlong hshort 1 (by norm_num) 1 (by norm_num) δ hδ
  filter_upwards [hc, hinfty.eventually_gt_atTop 0] with k hk hh
  have hB := hk (h k) (by linarith) (by simp)
  rw [Real.dist_eq]
  simpa only [hm] using hB.2.1

-- H18 PRIVATE. Exact signed exponent difference, not merely a height-ratio limit.
private theorem centerHeight_tail_geometry
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun k => (n k : ℝ) / h k ^ 2) atTop atTop)
    (d : ℝ) :
    (∀ᶠ k in atTop, h k / 2 ≤ centerHeight (n k) (h k) d ∧
      centerHeight (n k) (h k) d ≤ 2 * h k) ∧
      Tendsto (fun k =>
        (n k : ℝ) / centerHeight (n k) (h k) d ^ 2 -
          (n k : ℝ) / h k ^ 2) atTop (𝓝 (-d))
    := by
  have hf := eventual_finite_conditions n h hinfty hlong (|d| + 1) (by positivity)
  have hwindow : ∀ᶠ k in atTop, h k / 2 ≤ centerHeight (n k) (h k) d ∧
      centerHeight (n k) (h k) d ≤ 2 * h k := by
    filter_upwards [hf] with k hk
    exact centerHeight_window (n k) hk.1 (h k) d hk.2.1 (by linarith [hk.2.2])
  refine ⟨hwindow, ?_⟩
  have hdlim : Tendsto (fun k => d / ((n k : ℝ) / h k ^ 2))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Pi.inv_apply, Pi.mul_apply, div_eq_mul_inv, mul_zero] using hlong.inv_tendsto_atTop.const_mul d
  have hdenlim : Tendsto (fun k => 1 + d / ((n k : ℝ) / h k ^ 2))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hdlim
  have hscalar : Tendsto (fun k => -d / (1 + d / ((n k : ℝ) / h k ^ 2)))
      atTop (𝓝 (-d)) := by
    simpa only [Pi.div_def, div_one] using
      (tendsto_const_nhds.div hdenlim (by norm_num : (1 : ℝ) ≠ 0))
  apply hscalar.congr'
  filter_upwards [hf] with k hk
  have hnR : 0 < (n k : ℝ) := by exact_mod_cast hk.1
  have htpos : 0 < (n k : ℝ) / h k ^ 2 := div_pos hnR (sq_pos_of_pos hk.2.1)
  have hdlo : -(1 / 2 : ℝ) ≤ d / ((n k : ℝ) / h k ^ 2) := by
    apply (le_div_iff₀ htpos).mpr
    linarith [neg_abs_le d, hk.2.2]
  have hrad : 0 < 1 + d / ((n k : ℝ) / h k ^ 2) := by linarith
  have hsq := (centerHeight_identities (n k) hk.1 (h k) d hk.2.1 hrad.le).2.1
  rw [hsq, div_mul_eq_div_div]
  symm
  apply (eq_div_iff hrad.ne').mpr
  rw [sub_mul, div_mul_cancel₀ _ hrad.ne']
  have hmul : (1 + d / ((n k : ℝ) / h k ^ 2)) * ((n k : ℝ) / h k ^ 2) =
      (n k : ℝ) / h k ^ 2 + d := by
    rw [add_mul, one_mul, div_mul_cancel₀ _ htpos.ne']
  nlinarith [hmul]

-- H19 PUBLIC. Actual center probability ratio under original law/scales alone.
theorem center_probability_ratio_tendsto
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun k => (n k : ℝ) / h k ^ 2) atTop atTop)
    (hshort : Tendsto (fun k => (n k : ℝ) / h k ^ 3) atTop (𝓝 (0 : ℝ)))
    (d : ℝ) :
    Tendsto (fun k =>
      (Measure.pi (fun _ : Fin (n k) => ν)).real
          (@Shao.closedStrip (n k) (centerHeight (n k) (h k) d)) /
        (Measure.pi (fun _ : Fin (n k) => ν)).real
          (@Shao.closedStrip (n k) (h k)))
      atTop (𝓝 (Real.exp (lambda * d)))
    := by
  let G : ℕ → ℝ → ℝ := fun k b =>
    (Measure.pi (fun _ : Fin (n k) => ν)).real (@Shao.closedStrip (n k) b)
  let c : ℕ → ℝ := fun k => centerHeight (n k) (h k) d
  let E : ℕ → ℝ := fun k => Real.exp (lambda *
    ((n k : ℝ) / h k ^ 2 - (n k : ℝ) / c k ^ 2))
  have hm (N : ℕ) (b : ℝ) :
      (4 / Real.pi) * Real.exp (-lambda * (N : ℝ) / b ^ 2) = farMainTerm N b := by
    dsimp only [farMainTerm, lambda]
    congr 1
    congr 1
    ring
  have hq (b : ℕ → ℝ)
      (hb : ∀ᶠ k in atTop, h k / 2 ≤ b k ∧ b k ≤ 2 * h k) :
      Tendsto (fun k => G k (b k) / farMainTerm (n k) (b k)) atTop (𝓝 (1 : ℝ)) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    have hc := UniformConditionalEnergy.uniform_closedStrip_energy_controls
      ν h3 hmean hsecond h n hinfty hlong hshort 2 (by norm_num) 1 (by norm_num) δ hδ
    filter_upwards [hc, hb] with k hk hbk
    have hB := hk (b k) hbk.1 hbk.2
    rw [Real.dist_eq]
    simpa only [hm] using hB.2.1
  have hgeo := centerHeight_tail_geometry h n hinfty hlong d
  have hcwin : ∀ᶠ k in atTop, h k / 2 ≤ c k ∧ c k ≤ 2 * h k := hgeo.1
  have hhwin : ∀ᶠ k in atTop, h k / 2 ≤ h k ∧ h k ≤ 2 * h k := by
    filter_upwards [hinfty.eventually_gt_atTop 0] with k hk
    constructor <;> linarith
  have hqc := hq c hcwin
  have hqh := hq h hhwin
  have harg : Tendsto (fun k => lambda *
      ((n k : ℝ) / h k ^ 2 - (n k : ℝ) / c k ^ 2)) atTop (𝓝 (lambda * d)) := by
    have ht := hgeo.2.const_mul (-lambda)
    change Tendsto (fun k => -lambda *
      ((n k : ℝ) / c k ^ 2 - (n k : ℝ) / h k ^ 2)) atTop
        (𝓝 (-lambda * -d)) at ht
    have heq : (fun k => -lambda *
        ((n k : ℝ) / c k ^ 2 - (n k : ℝ) / h k ^ 2)) =
        (fun k => lambda * ((n k : ℝ) / h k ^ 2 - (n k : ℝ) / c k ^ 2)) := by
      funext k
      ring
    rw [heq] at ht
    simpa only [neg_mul_neg] using ht
  have hE : Tendsto E atTop (𝓝 (Real.exp (lambda * d))) := harg.rexp
  have hlim := (hqc.div hqh (by norm_num : (1 : ℝ) ≠ 0)).mul hE
  have hlim' : Tendsto (fun k =>
      ((G k (c k) / farMainTerm (n k) (c k)) /
        (G k (h k) / farMainTerm (n k) (h k))) * E k)
      atTop (𝓝 (Real.exp (lambda * d))) := by
    simpa only [Pi.div_def, Pi.mul_def, one_div, inv_one, one_mul] using hlim
  have hpos := UniformConditionalEnergy.uniform_closedStrip_boundary_ratio_bound
    ν h3 hmean hsecond h n hinfty hlong hshort 2 (by norm_num)
  apply hlim'.congr'
  filter_upwards [hpos] with k hk
  have hGh : 0 < G k (h k) := hk.1
  have hmh : 0 < farMainTerm (n k) (h k) :=
    RandomDenominatorFarTail.farMainTerm_pos _ _
  have hEk : 0 < E k := Real.exp_pos _
  have hexp : Real.exp (-lambda * (n k : ℝ) / c k ^ 2) =
      E k * Real.exp (-lambda * (n k : ℝ) / h k ^ 2) := by
    dsimp only [E]
    rw [← Real.exp_add]
    congr 1
    ring
  have hmain : farMainTerm (n k) (c k) = E k * farMainTerm (n k) (h k) := by
    rw [← hm (n k) (c k), ← hm (n k) (h k), hexp]
    ring
  change ((G k (c k) / farMainTerm (n k) (c k)) /
    (G k (h k) / farMainTerm (n k) (h k))) * E k = G k (c k) / G k (h k)
  rw [hmain]
  field_simp [hGh.ne', hmh.ne', hEk.ne']
  <;> ring

-- H20 PRIVATE. Original h² deviation and actual lower center, relative to G_h.
private theorem center_deviation_relative_tendsto_zero
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun k => (n k : ℝ) / h k ^ 2) atTop atTop)
    (hshort : Tendsto (fun k => (n k : ℝ) / h k ^ 3) atTop (𝓝 (0 : ℝ)))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun k =>
      (Measure.pi (fun _ : Fin (n k) => ν)).real
          ((@Shao.closedStrip (n k) (centerHeight (n k) (h k) (-ε))) ∩
            {a : Shao.Path (n k) |
              ε * h k ^ 2 < |Shao.energy a - (n k : ℝ)|}) /
        (Measure.pi (fun _ : Fin (n k) => ν)).real
          (@Shao.closedStrip (n k) (h k)))
      atTop (𝓝 (0 : ℝ))
    := by
  let c : ℕ → ℝ := fun k => centerHeight (n k) (h k) (-ε)
  let G : ℕ → ℝ → ℝ := fun k b =>
    (Measure.pi (fun _ : Fin (n k) => ν)).real (@Shao.closedStrip (n k) b)
  let R : ℕ → ℝ := fun k =>
    (Measure.pi (fun _ : Fin (n k) => ν)).real
      ((@Shao.closedStrip (n k) (c k)) ∩
        {a : Shao.Path (n k) | ε * h k ^ 2 < |Shao.energy a - (n k : ℝ)|})
  have hgeo := (centerHeight_tail_geometry h n hinfty hlong (-ε)).1
  have hR : Tendsto (fun k => R k / G k (c k)) atTop (𝓝 (0 : ℝ)) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    have hc := UniformConditionalEnergy.uniform_energy_concentration
      ν h3 hmean hsecond h n hinfty hlong hshort 2 (by norm_num) ε hε δ hδ
    filter_upwards [hc, hgeo] with k hk hbk
    have hB := hk (c k) hbk.1 hbk.2
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hB.2.1]
    exact hB.2.2
  have hC := center_probability_ratio_tendsto ν h3 hmean hsecond h n
    hinfty hlong hshort (-ε)
  have hprod : Tendsto (fun k => (R k / G k (c k)) * (G k (c k) / G k (h k)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using hR.mul hC
  have hpos := UniformConditionalEnergy.uniform_closedStrip_boundary_ratio_bound
    ν h3 hmean hsecond h n hinfty hlong hshort 2 (by norm_num)
  apply hprod.congr'
  filter_upwards [hpos, hgeo] with k hk hbk
  have hGc : 0 < G k (c k) := (hk.2 (c k) hbk.1 hbk.2).1
  change (R k / G k (c k)) * (G k (c k) / G k (h k)) = R k / G k (h k)
  field_simp [hGc.ne', hk.1.ne']
  <;> ring

-- H21 PUBLIC. ENTIRE growing finite middle collection, no rate/supremum premise.
theorem middle_relative_tendsto_zero
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun k => (n k : ℝ) / h k ^ 2) atTop atTop)
    (hshort : Tendsto (fun k => (n k : ℝ) / h k ^ 3) atTop (𝓝 (0 : ℝ)))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun k =>
      (Measure.pi (fun _ : Fin (n k) => ν)).real (middleEvent (n k) (h k) ε) /
        (Measure.pi (fun _ : Fin (n k) => ν)).real
          (@Shao.closedStrip (n k) (h k)))
      atTop (𝓝 (0 : ℝ))
    := by
  let s : ℝ := lambda + 1
  have hs : lambda < s := by dsimp only [s]; linarith
  have hs0 : 0 < s := by dsimp only [s, lambda]; positivity
  let B : ℝ := middleSumConstant s ε
  have hB : 0 < B := middleSumConstant_pos s ε hs hε
  have hpos := UniformConditionalEnergy.uniform_closedStrip_boundary_ratio_bound
    ν h3 hmean hsecond h n hinfty hlong hshort 2 (by norm_num)
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hpos] with k hk
    exact ha.trans_le (div_nonneg measureReal_nonneg hk.1.le)
  · intro τ hτ
    let η : ℝ := τ / (B + 1)
    have hη : 0 < η := div_pos hτ (by linarith)
    have hc := UniformConditionalEnergy.uniform_closedStrip_energy_controls
      ν h3 hmean hsecond h n hinfty hlong hshort 2 (by norm_num) s hs0 η hη
    have hf := eventual_finite_conditions n h hinfty hlong ε hε
    filter_upwards [hc, hpos, hf] with k hk hpk hfk
    have hcontrols : ∀ j ∈ middleIndices (n k) (h k) ε,
        0 < (Measure.pi (fun _ : Fin (n k) => ν)).real
            (@Shao.closedStrip (n k) (middleHeight (n k) (h k) ε j)) ∧
          energyCoshExcessIntegral ν (n k) (middleHeight (n k) (h k) ε j) (h k) s /
              (Measure.pi (fun _ : Fin (n k) => ν)).real
                (@Shao.closedStrip (n k) (middleHeight (n k) (h k) ε j)) ≤ η ∧
          (Measure.pi (fun _ : Fin (n k) => ν)).real
                (@Shao.closedStrip (n k) (middleHeight (n k) (h k) ε j)) /
              (Measure.pi (fun _ : Fin (n k) => ν)).real (@Shao.closedStrip (n k) (h k)) ≤
            4 * Real.exp (lambda * (((j : ℝ) + 1) * ε)) := by
      intro j hj
      have hg := middleHeight_geometry (n k) hfk.1 (h k) ε hfk.2.1 hε
        (by linarith [hfk.2.2]) j hj
      have hlo : h k / 2 ≤ middleHeight (n k) (h k) ε j := by linarith [hg.1]
      have he := hk _ hlo hg.2.1
      have hr := hpk.2 _ hlo hg.2.1
      refine ⟨he.1, he.2.2.2.le, hr.2.trans ?_⟩
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hg.2.2.2 (by dsimp only [lambda]; positivity)
    have hfinite := middle_finite_bound ν (n k) hfk.1 (h k) ε s η hfk.2.1 hε hs hη.le
      (by linarith [hfk.2.2]) hpk.1 hcontrols
    have hsmall : η * B < τ := by
      dsimp only [η]
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ (show 0 < B + 1 by linarith)).mpr
      nlinarith
    exact hfinite.trans_lt hsmall

-- H22 PUBLIC. Reuses qualified entire FAR / actual literal main, then actual K.
theorem far_relative_closedStrip_tendsto_zero
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun k => (n k : ℝ) / h k ^ 2) atTop atTop)
    (hshort : Tendsto (fun k => (n k : ℝ) / h k ^ 3) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun k =>
      (Measure.pi (fun _ : Fin (n k) => ν)).real
          (randomDenominatorEvent (n k) (h k) ∩
            {a : Shao.Path (n k) | 2 * (n k : ℝ) ≤ Shao.energy a}) /
        (Measure.pi (fun _ : Fin (n k) => ν)).real
          (@Shao.closedStrip (n k) (h k)))
      atTop (𝓝 (0 : ℝ))
    := by
  have hSq := (lower_moments_integrable ν h3).2
  let s : ℝ := 4 * lambda + 1
  have hs : Real.pi ^ 2 / 2 < s := by dsimp only [s, lambda]; ring_nf; linarith
  have hfar := RandomDenominatorFarTail.far_tail_relative_tendsto_zero
    ν hSq h3 hsecond n h s hs hinfty hlong hshort
  have hK := closedStrip_relative_main_tendsto ν h3 hmean hsecond h n hinfty hlong hshort
  have hratio := hfar.div hK (by norm_num : (1 : ℝ) ≠ 0)
  have hratio' : Tendsto (fun k =>
      ((Measure.pi (fun _ : Fin (n k) => ν)).real
          (randomDenominatorEvent (n k) (h k) ∩
            {a : Shao.Path (n k) | 2 * (n k : ℝ) ≤ Shao.energy a}) /
        farMainTerm (n k) (h k)) /
      ((Measure.pi (fun _ : Fin (n k) => ν)).real
          (@Shao.closedStrip (n k) (h k)) / farMainTerm (n k) (h k)))
      atTop (𝓝 (0 : ℝ)) := by simpa only [Pi.div_def, zero_div] using hratio
  have hpos := UniformConditionalEnergy.uniform_closedStrip_boundary_ratio_bound
    ν h3 hmean hsecond h n hinfty hlong hshort 1 (by norm_num)
  apply hratio'.congr'
  filter_upwards [hpos] with k hk
  have hm := (RandomDenominatorFarTail.farMainTerm_pos (n k) (h k)).ne'
  field_simp [hm, hk.1.ne']
  <;> ring

-- H23 PUBLIC ROOT TARGET. Actual random denominator, original law/scales only.
theorem randomDenominator_relative_closedStrip_tendsto
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun k => (n k : ℝ) / h k ^ 2) atTop atTop)
    (hshort : Tendsto (fun k => (n k : ℝ) / h k ^ 3) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun k =>
      (Measure.pi (fun _ : Fin (n k) => ν)).real
          (randomDenominatorEvent (n k) (h k)) /
        (Measure.pi (fun _ : Fin (n k) => ν)).real
          (@Shao.closedStrip (n k) (h k)))
      atTop (𝓝 (1 : ℝ))
    := by
  let μ : (k : ℕ) → Measure (Shao.Path (n k)) :=
    fun k => Measure.pi (fun _ : Fin (n k) => ν)
  let G : ℕ → ℝ → ℝ := fun k b => (μ k).real (@Shao.closedStrip (n k) b)
  let R : ℝ → ℕ → ℝ := fun ε k => (μ k).real
    ((@Shao.closedStrip (n k) (centerHeight (n k) (h k) (-ε))) ∩
      {a : Shao.Path (n k) | ε * h k ^ 2 < |Shao.energy a - (n k : ℝ)|})
  let M : ℝ → ℕ → ℝ := fun ε k => (μ k).real (middleEvent (n k) (h k) ε)
  let F : ℕ → ℝ := fun k => (μ k).real
    (randomDenominatorEvent (n k) (h k) ∩
      {a : Shao.Path (n k) | 2 * (n k : ℝ) ≤ Shao.energy a})
  let f : ℕ → ℝ := fun k => (μ k).real (randomDenominatorEvent (n k) (h k)) / G k (h k)
  let L : ℝ → ℕ → ℝ := fun ε k =>
    G k (centerHeight (n k) (h k) (-ε)) / G k (h k) - R ε k / G k (h k)
  let U : ℝ → ℕ → ℝ := fun ε k =>
    G k (centerHeight (n k) (h k) ε) / G k (h k) +
      M ε k / G k (h k) + F k / G k (h k)
  have hL (ε : ℝ) (hε : 0 < ε) :
      Tendsto (L ε) atTop (𝓝 (Real.exp (-lambda * ε))) := by
    have hc := center_probability_ratio_tendsto ν h3 hmean hsecond h n
      hinfty hlong hshort (-ε)
    have hd := center_deviation_relative_tendsto_zero ν h3 hmean hsecond h n
      hinfty hlong hshort ε hε
    simpa only [L, μ, G, R, sub_zero, mul_neg, neg_mul] using hc.sub hd
  have hU (ε : ℝ) (hε : 0 < ε) :
      Tendsto (U ε) atTop (𝓝 (Real.exp (lambda * ε))) := by
    have hc := center_probability_ratio_tendsto ν h3 hmean hsecond h n
      hinfty hlong hshort ε
    have hm := middle_relative_tendsto_zero ν h3 hmean hsecond h n
      hinfty hlong hshort ε hε
    have hf := far_relative_closedStrip_tendsto_zero ν h3 hmean hsecond h n
      hinfty hlong hshort
    simpa only [U, μ, G, M, F, add_zero] using (hc.add hm).add hf
  have hpos := UniformConditionalEnergy.uniform_closedStrip_boundary_ratio_bound
    ν h3 hmean hsecond h n hinfty hlong hshort 1 (by norm_num)
  have hcompare (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ k in atTop, L ε k ≤ f k ∧ f k ≤ U ε k := by
    have hfinite := eventual_finite_conditions n h hinfty hlong ε hε
    filter_upwards [hfinite, hpos] with k hk hpk
    have hl := center_lower_probability_bound ν (n k) hk.1 (h k) ε
      hk.2.1 hε hk.2.2
    have hu := randomDenominator_probability_upper_bound ν (n k) hk.1 (h k) ε
      hk.2.1 hε hk.2.2
    have hl' := div_le_div_of_nonneg_right hl hpk.1.le
    have hu' := div_le_div_of_nonneg_right hu hpk.1.le
    constructor
    · simpa only [sub_div, L, f, μ, G, R] using hl'
    · simpa only [add_div, U, f, μ, G, M, F] using hu'
  change Tendsto f atTop (𝓝 (1 : ℝ))
  apply tendsto_order.2
  constructor
  · intro a ha
    have he : Tendsto (fun v : ℝ => Real.exp (-lambda * v⁻¹)) atTop (𝓝 (1 : ℝ)) := by
      simpa only [mul_zero, Real.exp_zero] using
        ((tendsto_inv_atTop_zero : Tendsto (fun v : ℝ => v⁻¹) atTop (𝓝 (0 : ℝ))).const_mul
          (-lambda)).rexp
    obtain ⟨v, hv, hve⟩ := ((eventually_gt_atTop (0 : ℝ)).and
      (he.eventually (lt_mem_nhds ha))).exists
    have hε : 0 < v⁻¹ := inv_pos.mpr hv
    filter_upwards [hcompare v⁻¹ hε,
      (hL v⁻¹ hε).eventually (lt_mem_nhds hve)] with k hk hl
    exact hl.trans_le hk.1
  · intro b hb
    have he : Tendsto (fun v : ℝ => Real.exp (lambda * v⁻¹)) atTop (𝓝 (1 : ℝ)) := by
      simpa only [mul_zero, Real.exp_zero] using
        ((tendsto_inv_atTop_zero : Tendsto (fun v : ℝ => v⁻¹) atTop (𝓝 (0 : ℝ))).const_mul
          lambda).rexp
    obtain ⟨v, hv, hve⟩ := ((eventually_gt_atTop (0 : ℝ)).and
      (he.eventually (gt_mem_nhds hb))).exists
    have hε : 0 < v⁻¹ := inv_pos.mpr hv
    filter_upwards [hcompare v⁻¹ hε,
      (hU v⁻¹ hε).eventually (gt_mem_nhds hve)] with k hk hu
    exact hk.2.trans_lt hu

-- H24 PUBLIC. Same actual E divided by the exact qualified positive literal main.
theorem randomDenominator_relative_main_tendsto
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (h : ℕ → ℝ) (n : ℕ → ℕ)
    (hinfty : Tendsto h atTop atTop)
    (hlong : Tendsto (fun k => (n k : ℝ) / h k ^ 2) atTop atTop)
    (hshort : Tendsto (fun k => (n k : ℝ) / h k ^ 3) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun k =>
      (Measure.pi (fun _ : Fin (n k) => ν)).real
          (randomDenominatorEvent (n k) (h k)) / farMainTerm (n k) (h k))
      atTop (𝓝 (1 : ℝ))
    := by
  have hE := randomDenominator_relative_closedStrip_tendsto
    ν h3 hmean hsecond h n hinfty hlong hshort
  have hK := closedStrip_relative_main_tendsto ν h3 hmean hsecond h n hinfty hlong hshort
  have hprod := hE.mul hK
  have hprod' : Tendsto (fun k =>
      ((Measure.pi (fun _ : Fin (n k) => ν)).real
          (randomDenominatorEvent (n k) (h k)) /
        (Measure.pi (fun _ : Fin (n k) => ν)).real (@Shao.closedStrip (n k) (h k))) *
      ((Measure.pi (fun _ : Fin (n k) => ν)).real (@Shao.closedStrip (n k) (h k)) /
        farMainTerm (n k) (h k))) atTop (𝓝 (1 : ℝ)) := by
    simpa only [one_mul] using hprod
  have hpos := UniformConditionalEnergy.uniform_closedStrip_boundary_ratio_bound
    ν h3 hmean hsecond h n hinfty hlong hshort 1 (by norm_num)
  apply hprod'.congr'
  filter_upwards [hpos] with k hk
  have hm := (RandomDenominatorFarTail.farMainTerm_pos (n k) (h k)).ne'
  field_simp [hk.1.ne', hm]
  <;> ring

end Shao.OQ4.RandomDenominatorAsymptotic
end
