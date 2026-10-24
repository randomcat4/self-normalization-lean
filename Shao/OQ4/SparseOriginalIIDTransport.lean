/-
Full source candidate under the parent-frozen V1 interface (context204).
LOCAL SOURCE AUTHORSHIP ONLY: no Lean/parser/kernel/axiom check has run.
SparseCriticalDenominator is an explicit frozen UNELABORATED dependency.
All 11 frozen public heads and full contexts/definition value are retained.
Final independent complete review and exact-source server gates remain open.
-/

import Shao.OQ4.OriginalIIDWindow
import Shao.OQ4.SparseCriticalDenominator

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology

universe uX uB

namespace Shao.OQ4.SparseOriginalIIDTransport

variable {ΩX : Type uX} [MeasurableSpace ΩX]
variable {ΩB : Type uB} [MeasurableSpace ΩB]

-- P01 full value. Literal source maximum; only the denominator is deterministic.
def sourceDetEvent (n : ℕ) (X : ℕ → ΩX → ℝ) (s : ℝ) : Set ΩX :=
  {ω | OriginalIIDWindow.sourceMaximum n X ω ≤ s * Real.sqrt (n : ℝ)}

-- P02. The law assumption includes AE measurability of each positive coordinate.
theorem sourcePath_identDistrib
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ SparseCriticalDenominator.law)
    (n : ℕ) :
    IdentDistrib (OriginalIIDWindow.sourcePath n X)
      (id : Shao.Path n → Shao.Path n) μ (SparseCriticalDenominator.pathLaw n) := by
  classical
  have hX (i : Fin n) : AEMeasurable (X (i.val + 1)) μ :=
    (hLaw i.val).aemeasurable_fst
  let Z : ΩX → Shao.Path n := fun ω i =>
    (hX i).mk (X (i.val + 1)) ω
  have hZ : Measurable Z :=
    Measurable.of_eval fun i => (hX i).measurable_mk
  have hcoords : ∀ᵐ ω ∂μ, ∀ i : Fin n,
      X (i.val + 1) ω = Z ω i :=
    ae_all_iff.mpr fun i => (hX i).ae_eq_mk
  have hFZ : OriginalIIDWindow.sourcePath n X =ᵐ[μ] Z := by
    filter_upwards [hcoords] with ω hω
    exact funext hω
  have hF : AEMeasurable (OriginalIIDWindow.sourcePath n X) μ :=
    ⟨Z, hZ, hFZ⟩
  have hfin : iIndepFun (fun i : Fin n => X (i.val + 1)) μ :=
    hIndep.precomp (show Function.Injective (fun i : Fin n => i.val) from
      fun i j hij => Fin.ext hij)
  have hmap : μ.map (OriginalIIDWindow.sourcePath n X) =
      SparseCriticalDenominator.pathLaw n := by
    change μ.map (fun ω (i : Fin n) => X (i.val + 1) ω) =
      Measure.pi (fun _ : Fin n => SparseCriticalDenominator.law)
    rw [hfin.map_fun_eq_pi_map hX]
    congr 1
    funext i
    simpa only [Measure.map_id] using (hLaw i.val).map_eq
  refine ⟨hF, measurable_id.aemeasurable, ?_⟩
  simpa only [Measure.map_id] using hmap


-- P03. Pointwise equalities, all n and all real s, with no probability premise.
theorem source_event_pullbacks (n : ℕ) (X : ℕ → ΩX → ℝ) (s : ℝ) :
    OriginalIIDWindow.sourceEvent n X s =
      OriginalIIDWindow.sourcePath n X ⁻¹' SparseCriticalDenominator.selfEvent n s ∧
    sourceDetEvent n X s =
      OriginalIIDWindow.sourcePath n X ⁻¹' SparseCriticalDenominator.detEvent n s := by
  classical
  have hmax (ω : ΩX) (w : ℝ) :
      OriginalIIDWindow.sourceMaximum n X ω ≤ w ↔
        ∀ k : ℕ, k ≤ n →
          |Shao.prefixSum (OriginalIIDWindow.sourcePath n X ω) k| ≤ w := by
    by_cases hn : 0 < n
    · rw [OriginalIIDWindow.sourceMaximum, dif_pos hn]
      constructor
      · intro h k hkn
        by_cases hk : k = 0
        · simpa only [hk, Shao.prefixSum_zero, abs_zero] using
            (Shao.absMax_nonneg (OriginalIIDWindow.sourcePath n X ω) hn).trans h
        · exact (Shao.absMax_le_iff _ hn w).mp h k
            (Nat.one_le_iff_ne_zero.mpr hk) hkn
      · intro h
        exact (Shao.absMax_le_iff _ hn w).mpr (fun k _ hkn => h k hkn)
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      simp [OriginalIIDWindow.sourceMaximum, Shao.prefixSum]
  constructor
  · ext ω
    change (OriginalIIDWindow.sourceMaximum n X ω ≤
      s * Real.sqrt (OriginalIIDWindow.sourceEnergy n X ω)) ↔
      ∀ k : ℕ, k ≤ n →
        |Shao.prefixSum (OriginalIIDWindow.sourcePath n X ω) k| ≤
          s * Real.sqrt (OriginalIIDWindow.sourceEnergy n X ω)
    exact hmax ω _
  · ext ω
    change (OriginalIIDWindow.sourceMaximum n X ω ≤ s * Real.sqrt (n : ℝ)) ↔
      ∀ k : ℕ, k ≤ n →
        |Shao.prefixSum (OriginalIIDWindow.sourcePath n X ω) k| ≤
          s * Real.sqrt (n : ℝ)
    exact hmax ω _


-- P04. Actual original sums, with X_0 unused and the empty sample exact.
theorem source_event_formulas (n : ℕ) (X : ℕ → ΩX → ℝ) (s : ℝ) :
    OriginalIIDWindow.sourceEvent n X s =
      {ω | ∀ k : ℕ, k ≤ n →
        |∑ i ∈ Finset.range k, X (i + 1) ω| ≤
          s * Real.sqrt (∑ i ∈ Finset.range n, (X (i + 1) ω) ^ 2)} ∧
    sourceDetEvent n X s =
      {ω | ∀ k : ℕ, k ≤ n →
        |∑ i ∈ Finset.range k, X (i + 1) ω| ≤ s * Real.sqrt (n : ℝ)} ∧
    OriginalIIDWindow.sourceEvent 0 X s = Set.univ ∧
    sourceDetEvent 0 X s = Set.univ := by
  classical
  have hprefix (k : ℕ) (hk : k ≤ n) (ω : ΩX) :
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
  obtain ⟨hself, hdet⟩ := source_event_pullbacks n X s
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hself]
    ext ω
    change (∀ k : ℕ, k ≤ n →
      |Shao.prefixSum (OriginalIIDWindow.sourcePath n X ω) k| ≤
        s * Real.sqrt (OriginalIIDWindow.sourceEnergy n X ω)) ↔ _
    constructor
    · intro h k hkn
      simpa only [hprefix k hkn ω, OriginalIIDWindow.sourceEnergy_eq_sum n X ω]
        using h k hkn
    · intro h k hkn
      simpa only [hprefix k hkn ω, OriginalIIDWindow.sourceEnergy_eq_sum n X ω]
        using h k hkn
  · rw [hdet]
    ext ω
    change (∀ k : ℕ, k ≤ n →
      |Shao.prefixSum (OriginalIIDWindow.sourcePath n X ω) k| ≤
        s * Real.sqrt (n : ℝ)) ↔ _
    constructor
    · intro h k hkn
      simpa only [hprefix k hkn ω] using h k hkn
    · intro h k hkn
      simpa only [hprefix k hkn ω] using h k hkn
  · ext ω
    simp [OriginalIIDWindow.sourceEvent, OriginalIIDWindow.sourceMaximum,
      OriginalIIDWindow.sourceEnergy, Shao.energy]
  · ext ω
    simp [sourceDetEvent, OriginalIIDWindow.sourceMaximum]


-- P05. This weaker measurable interface does not need a law or independence.
theorem nullMeasurableSet_sourceDetEvent
    (μ : Measure ΩX) (X : ℕ → ΩX → ℝ)
    (hX : ∀ i : ℕ, AEMeasurable (X (i + 1)) μ) (n : ℕ) (s : ℝ) :
    NullMeasurableSet (sourceDetEvent n X s) μ := by
  classical
  let Z : ΩX → Shao.Path n := fun ω i =>
    (hX i.val).mk (X (i.val + 1)) ω
  have hZ : Measurable Z :=
    Measurable.of_eval fun i => (hX i.val).measurable_mk
  have hcoords : ∀ᵐ ω ∂μ, ∀ i : Fin n,
      X (i.val + 1) ω = Z ω i :=
    ae_all_iff.mpr fun i => (hX i.val).ae_eq_mk
  have hFZ : OriginalIIDWindow.sourcePath n X =ᵐ[μ] Z := by
    filter_upwards [hcoords] with ω hω
    exact funext hω
  have hA : MeasurableSet (SparseCriticalDenominator.detEvent n s) := by
    simp only [SparseCriticalDenominator.detEvent, Shao.closedStrip,
      Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_le (continuous_abs.measurable.comp (Shao.measurable_prefixSum k)) measurable_const
  have hpull := (source_event_pullbacks n X s).2
  refine ⟨Z ⁻¹' SparseCriticalDenominator.detEvent n s, hA.preimage hZ, ?_⟩
  filter_upwards [hFZ] with ω hω
  apply propext
  rw [hpull]
  change (OriginalIIDWindow.sourcePath n X ω ∈
    SparseCriticalDenominator.detEvent n s) ↔
      Z ω ∈ SparseCriticalDenominator.detEvent n s
  rw [hω]


-- P06. The actual fixed law supplies every moment premise; independence is unused.
theorem source_moments
    (μ : Measure ΩX) (X : ℕ → ΩX → ℝ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ SparseCriticalDenominator.law) (i : ℕ) :
    Integrable (fun ω => |X (i + 1) ω| ^ 3) μ ∧
    (∫ ω, X (i + 1) ω ∂μ) = 0 ∧
    (∫ ω, (X (i + 1) ω) ^ 2 ∂μ) = 1 ∧
    (∫ ω, |X (i + 1) ω| ^ 3 ∂μ) = 2 ∧
    variance (X (i + 1)) μ = 1 := by
  have hm := SparseCriticalDenominator.law_moments
  have hcube : IdentDistrib (fun ω => |X (i + 1) ω| ^ 3)
      (fun z : ℝ => |z| ^ 3) μ SparseCriticalDenominator.law := by
    exact (hLaw i).comp (continuous_abs.measurable.pow_const (3 : ℕ))
  have hsquare : IdentDistrib (fun ω => (X (i + 1) ω) ^ 2)
      (fun z : ℝ => z ^ 2) μ SparseCriticalDenominator.law := by
    exact (hLaw i).comp (measurable_id.pow_const (2 : ℕ))
  refine ⟨hcube.integrable_iff.mpr hm.1, ?_, ?_, ?_, ?_⟩
  · calc
      (∫ ω, X (i + 1) ω ∂μ) =
          ∫ z : ℝ, z ∂SparseCriticalDenominator.law := by
        simpa only [id_eq] using (hLaw i).integral_eq
      _ = 0 := hm.2.1
  · exact hsquare.integral_eq.trans hm.2.2.1
  · exact hcube.integral_eq.trans hm.2.2.2.1
  · exact (hLaw i).variance_eq.trans hm.2.2.2.2


-- P07. Exact finite probabilities for the actual original events, before limits.
theorem source_probability_pair
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ SparseCriticalDenominator.law)
    (n : ℕ) (s : ℝ) :
    μ.real (OriginalIIDWindow.sourceEvent n X s) =
      (SparseCriticalDenominator.pathLaw n).real
        (SparseCriticalDenominator.selfEvent n s) ∧
    μ.real (sourceDetEvent n X s) =
      (SparseCriticalDenominator.pathLaw n).real
        (SparseCriticalDenominator.detEvent n s) := by
  have hpath := sourcePath_identDistrib μ X hIndep hLaw n
  have hself : MeasurableSet (SparseCriticalDenominator.selfEvent n s) := by
    simp only [SparseCriticalDenominator.selfEvent, Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_le (continuous_abs.measurable.comp (Shao.measurable_prefixSum k))
        (Shao.measurable_energyWall s)
  have hdet : MeasurableSet (SparseCriticalDenominator.detEvent n s) := by
    simp only [SparseCriticalDenominator.detEvent, Shao.closedStrip,
      Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_le (continuous_abs.measurable.comp (Shao.measurable_prefixSum k)) measurable_const
  obtain ⟨hpullself, hpulldet⟩ := source_event_pullbacks n X s
  constructor
  · rw [hpullself]
    exact congrArg ENNReal.toReal (hpath.measure_mem_eq hself)
  · rw [hpulldet]
    exact congrArg ENNReal.toReal (hpath.measure_mem_eq hdet)


-- P08. Pointwise zero/count equivalences do not require sparse support or any law.
theorem source_zero_energy (n : ℕ) (X : ℕ → ΩX → ℝ) (ω : ΩX) :
    (OriginalIIDWindow.sourceEnergy n X ω = 0 ↔
      ∀ i : Fin n, X (i.val + 1) ω = 0) ∧
    (SparseCriticalDenominator.count (OriginalIIDWindow.sourcePath n X ω) = 0 ↔
      ∀ i : Fin n, X (i.val + 1) ω = 0) ∧
    (OriginalIIDWindow.sourceEnergy n X ω = 0 →
      OriginalIIDWindow.sourceMaximum n X ω = 0) ∧
    (∀ s : ℝ, OriginalIIDWindow.sourceEnergy n X ω = 0 →
      ω ∈ OriginalIIDWindow.sourceEvent n X s ∧
      (0 ≤ s → ω ∈ sourceDetEvent n X s)) := by
  classical
  have henergy : OriginalIIDWindow.sourceEnergy n X ω = 0 ↔
      ∀ i : Fin n, X (i.val + 1) ω = 0 :=
    Shao.energy_eq_zero_iff (OriginalIIDWindow.sourcePath n X ω)
  have hcount : SparseCriticalDenominator.count
      (OriginalIIDWindow.sourcePath n X ω) = 0 ↔
        ∀ i : Fin n, X (i.val + 1) ω = 0 := by
    constructor
    · intro hc i
      by_contra hi
      have hpos : 0 < (Finset.univ.filter (fun j : Fin n =>
          (OriginalIIDWindow.sourcePath n X ω) j ≠ 0)).card :=
        Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
      change (Finset.univ.filter (fun j : Fin n =>
        (OriginalIIDWindow.sourcePath n X ω) j ≠ 0)).card = 0 at hc
      omega
    · intro h
      simp [SparseCriticalDenominator.count, OriginalIIDWindow.sourcePath, h]
  have hmax : OriginalIIDWindow.sourceEnergy n X ω = 0 →
      OriginalIIDWindow.sourceMaximum n X ω = 0 := by
    intro he
    by_cases hn : 0 < n
    · simpa only [OriginalIIDWindow.sourceMaximum, dif_pos hn] using
        Shao.absMax_eq_zero_of_energy_eq_zero
          (OriginalIIDWindow.sourcePath n X ω) hn he
    · simp only [OriginalIIDWindow.sourceMaximum, dif_neg hn]
  refine ⟨henergy, hcount, hmax, ?_⟩
  intro s he
  constructor
  · change OriginalIIDWindow.sourceMaximum n X ω ≤
      s * Real.sqrt (OriginalIIDWindow.sourceEnergy n X ω)
    simpa only [hmax he, he, Real.sqrt_zero, mul_zero] using
      (le_rfl : (0 : ℝ) ≤ 0)
  · intro hs
    change OriginalIIDWindow.sourceMaximum n X ω ≤ s * Real.sqrt (n : ℝ)
    rw [hmax he]
    exact mul_nonneg hs (Real.sqrt_nonneg _)


-- P09. Includes k=0, k>n, and n=0; the zero path keeps its positive mass.
theorem source_count_and_zero
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ SparseCriticalDenominator.law) (n : ℕ) :
    (∀ k : ℕ, μ.real
      {ω | SparseCriticalDenominator.count (OriginalIIDWindow.sourcePath n X ω) = k} =
        SparseCriticalDenominator.weight n k) ∧
    (∀ᵐ ω ∂μ, OriginalIIDWindow.sourceEnergy n X ω =
      4 * (SparseCriticalDenominator.count (OriginalIIDWindow.sourcePath n X ω) : ℝ)) ∧
    μ.real {ω | OriginalIIDWindow.sourceEnergy n X ω = 0} = (3 / 4 : ℝ) ^ n := by
  classical
  have hpath := sourcePath_identDistrib μ X hIndep hLaw n
  have hmeas : Measurable (@SparseCriticalDenominator.count n) := by
    have hsum (a : Shao.Path n) :
        SparseCriticalDenominator.count a =
          ∑ i : Fin n, if a i ≠ 0 then (1 : ℕ) else 0 := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, smul_eq_mul, mul_one,
        SparseCriticalDenominator.count]
    have hi (i : Fin n) : Measurable
        (fun a : Shao.Path n => if a i ≠ 0 then (1 : ℕ) else 0) := by
      exact Measurable.ite
        (isClosed_eq (continuous_apply i) continuous_const).measurableSet.compl
        measurable_const measurable_const
    convert Finset.measurable_sum (Finset.univ : Finset (Fin n))
      (fun i _ => hi i) using 1
    funext a
    exact hsum a
  have hmC (k : ℕ) : MeasurableSet
      {a : Shao.Path n | SparseCriticalDenominator.count a = k} :=
    hmeas (measurableSet_singleton k)
  have hcountprob (k : ℕ) : μ.real
      {ω | SparseCriticalDenominator.count (OriginalIIDWindow.sourcePath n X ω) = k} =
        SparseCriticalDenominator.weight n k := by
    have heq : μ
        {ω | SparseCriticalDenominator.count (OriginalIIDWindow.sourcePath n X ω) = k} =
        SparseCriticalDenominator.pathLaw n
          {a : Shao.Path n | SparseCriticalDenominator.count a = k} := by
      simpa only [Set.preimage_setOf_eq, id_eq] using
        hpath.measure_mem_eq (hmC k)
    exact (congrArg ENNReal.toReal heq).trans
      ((SparseCriticalDenominator.count_law n).1 k)
  have hM : MeasurableSet {a : Shao.Path n | Shao.energy a =
      4 * (SparseCriticalDenominator.count a : ℝ)} := by
    have heq : {a : Shao.Path n | Shao.energy a =
        4 * (SparseCriticalDenominator.count a : ℝ)} =
        ⋃ k : ℕ, {a : Shao.Path n | SparseCriticalDenominator.count a = k} ∩
          {a : Shao.Path n | Shao.energy a = 4 * (k : ℝ)} := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro ha
        exact ⟨SparseCriticalDenominator.count a, rfl, ha⟩
      · rintro ⟨k, hk, he⟩
        simpa only [hk] using he
    rw [heq]
    exact MeasurableSet.iUnion fun k =>
      (hmC k).inter (measurableSet_eq_fun Shao.measurable_energy measurable_const)
  have hAE : ∀ᵐ ω ∂μ, OriginalIIDWindow.sourceEnergy n X ω =
      4 * (SparseCriticalDenominator.count (OriginalIIDWindow.sourcePath n X ω) : ℝ) := by
    have hp := hpath.symm.ae_snd
      (p := fun a : Shao.Path n => Shao.energy a =
        4 * (SparseCriticalDenominator.count a : ℝ)) hM
      (by simpa only [id_eq] using (SparseCriticalDenominator.count_law n).2)
    simpa only [OriginalIIDWindow.sourceEnergy] using hp
  refine ⟨hcountprob, hAE, ?_⟩
  have hzero : {ω | OriginalIIDWindow.sourceEnergy n X ω = 0} =
      {ω | SparseCriticalDenominator.count (OriginalIIDWindow.sourcePath n X ω) = 0} := by
    ext ω
    have hz := source_zero_energy n X ω
    exact hz.1.trans hz.2.1.symm
  rw [hzero, hcountprob 0]
  simp only [SparseCriticalDenominator.weight, Nat.choose_zero_right,
    Nat.cast_one, pow_zero, one_mul, Nat.sub_zero]


-- P10. Genuine random denominator versus the deterministic denominator, same law.
theorem source_exact_mixtures
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ SparseCriticalDenominator.law)
    (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    μ.real (OriginalIIDWindow.sourceEvent n X s) =
      (∑ k ∈ Finset.range (n + 1), SparseCriticalDenominator.weight n k *
        RademacherS4Assembly.p k (s * Real.sqrt (k : ℝ))) ∧
    μ.real (sourceDetEvent n X s) =
      (∑ k ∈ Finset.range (n + 1), SparseCriticalDenominator.weight n k *
        RademacherS4Assembly.p k (s * Real.sqrt (n : ℝ) / 2)) := by
  have hp := source_probability_pair μ X hIndep hLaw n s
  have hm := SparseCriticalDenominator.exact_mixtures n s hs
  exact ⟨hp.1.trans hm.1, hp.2.trans hm.2⟩


-- P11. Literal original subsequence/threshold. ΩX and ΩB have independent universes.
theorem original_sparse_critical_limits
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ SparseCriticalDenominator.law) :
    Tendsto (fun m : ℕ =>
      μ.real (OriginalIIDWindow.sourceEvent ((2 * m) ^ 3) X
        (1 / Real.sqrt (2 * (m : ℝ)))) /
      Shao.Probability.BrownianSup.probability B P hB
        (1 / Real.sqrt (2 * (m : ℝ)))) atTop
      (𝓝 ((1 + Real.exp (Real.pi ^ 2 / 2)) / 2)) ∧
    Tendsto (fun m : ℕ =>
      μ.real (sourceDetEvent ((2 * m) ^ 3) X
        (1 / Real.sqrt (2 * (m : ℝ)))) /
      Shao.Probability.BrownianSup.probability B P hB
        (1 / Real.sqrt (2 * (m : ℝ)))) atTop
      (𝓝 (Real.exp (Real.pi ^ 2 / 2))) := by
  have hc := SparseCriticalDenominator.critical_limits B P hB
  have hr : (fun m : ℕ =>
      μ.real (OriginalIIDWindow.sourceEvent ((2 * m) ^ 3) X
        (1 / Real.sqrt (2 * (m : ℝ)))) /
      Shao.Probability.BrownianSup.probability B P hB
        (1 / Real.sqrt (2 * (m : ℝ)))) =ᶠ[atTop]
      SparseCriticalDenominator.randomRatio B P hB := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hx := (SparseCriticalDenominator.critical_scale m hm).2.2.2.1
    have hp := source_probability_pair μ X hIndep hLaw
      (SparseCriticalDenominator.time m) (SparseCriticalDenominator.criticalX m)
    change μ.real (OriginalIIDWindow.sourceEvent ((2 * m) ^ 3) X
        (1 / Real.sqrt (2 * (m : ℝ)))) /
      Shao.Probability.BrownianSup.probability B P hB
        (1 / Real.sqrt (2 * (m : ℝ))) =
      (SparseCriticalDenominator.pathLaw (SparseCriticalDenominator.time m)).real
        (SparseCriticalDenominator.selfEvent (SparseCriticalDenominator.time m)
          (SparseCriticalDenominator.criticalX m)) /
      Shao.Probability.BrownianSup.probability B P hB
        (SparseCriticalDenominator.criticalX m)
    rw [← hx]
    exact congrArg (fun z : ℝ => z /
      Shao.Probability.BrownianSup.probability B P hB
        (SparseCriticalDenominator.criticalX m))
      (by simpa only [SparseCriticalDenominator.time] using hp.1)
  have hd : (fun m : ℕ =>
      μ.real (sourceDetEvent ((2 * m) ^ 3) X
        (1 / Real.sqrt (2 * (m : ℝ)))) /
      Shao.Probability.BrownianSup.probability B P hB
        (1 / Real.sqrt (2 * (m : ℝ)))) =ᶠ[atTop]
      SparseCriticalDenominator.detRatio B P hB := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hx := (SparseCriticalDenominator.critical_scale m hm).2.2.2.1
    have hp := source_probability_pair μ X hIndep hLaw
      (SparseCriticalDenominator.time m) (SparseCriticalDenominator.criticalX m)
    change μ.real (sourceDetEvent ((2 * m) ^ 3) X
        (1 / Real.sqrt (2 * (m : ℝ)))) /
      Shao.Probability.BrownianSup.probability B P hB
        (1 / Real.sqrt (2 * (m : ℝ))) =
      (SparseCriticalDenominator.pathLaw (SparseCriticalDenominator.time m)).real
        (SparseCriticalDenominator.detEvent (SparseCriticalDenominator.time m)
          (SparseCriticalDenominator.criticalX m)) /
      Shao.Probability.BrownianSup.probability B P hB
        (SparseCriticalDenominator.criticalX m)
    rw [← hx]
    exact congrArg (fun z : ℝ => z /
      Shao.Probability.BrownianSup.probability B P hB
        (SparseCriticalDenominator.criticalX m))
      (by simpa only [SparseCriticalDenominator.time] using hp.2)
  exact ⟨hc.1.congr' hr.symm, hc.2.congr' hd.symm⟩


end Shao.OQ4.SparseOriginalIIDTransport
