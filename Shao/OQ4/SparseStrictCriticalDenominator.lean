import Shao.OQ4.SparseCriticalDenominator
import Shao.OQ4.RademacherStrictWeakBoundary

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
universe u

namespace Shao.OQ4.SparseStrictCriticalDenominator

-- Positive prefixes, including vacuous events at time zero.
-- The qualified transparent V appearing here is sqrt(Shao.energy a).
def selfEvent (n : ℕ) (s : ℝ) : Set (Shao.Path n) :=
  RademacherStrictCube.strictSelfNormalizedEvent n s

def detEvent (n : ℕ) (s : ℝ) : Set (Shao.Path n) :=
  RademacherStrictCube.strictEvent n (s * Real.sqrt (n : ℝ))

def randomRatio {Ω : Type u} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (m : ℕ) : ℝ :=
  (SparseCriticalDenominator.pathLaw (SparseCriticalDenominator.time m)).real
      (selfEvent (SparseCriticalDenominator.time m)
        (SparseCriticalDenominator.criticalX m)) /
    SparseCriticalDenominator.baseline B P hB m

def detRatio {Ω : Type u} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (m : ℕ) : ℝ :=
  (SparseCriticalDenominator.pathLaw (SparseCriticalDenominator.time m)).real
      (detEvent (SparseCriticalDenominator.time m)
        (SparseCriticalDenominator.criticalX m)) /
    SparseCriticalDenominator.baseline B P hB m

private def lowMass (m : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (SparseCriticalDenominator.time m + 1)).filter
      (fun k : ℕ => k < m ^ 3),
    SparseCriticalDenominator.weight (SparseCriticalDenominator.time m) k

-- integerIndicator has the qualified transparent value 1 at integers and 0
-- elsewhere. This avoids introducing a new noncomputable filter definition.
private def integerHitMass (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (SparseCriticalDenominator.time m + 1),
    SparseCriticalDenominator.weight (SparseCriticalDenominator.time m) k *
      RademacherStrictWeakBoundary.integerIndicator
        (SparseCriticalDenominator.randomHeight m k)

private def detTilt (m k : ℕ) : ℝ :=
  Real.exp (-(Real.pi ^ 2 / 8) *
    ((k : ℝ) - (SparseCriticalDenominator.meanIndex m : ℝ)) / (m : ℝ) ^ 2)

private def tiltMoment (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (SparseCriticalDenominator.time m + 1),
    SparseCriticalDenominator.weight (SparseCriticalDenominator.time m) k *
      detTilt m k

theorem measurable_events (n : ℕ) (s : ℝ) :
    MeasurableSet (selfEvent n s) ∧ MeasurableSet (detEvent n s) := by
  exact ⟨(RademacherStrictCube.measurable_events n 0 s).2.2,
    (RademacherStrictCube.measurable_events n (s * Real.sqrt (n : ℝ)) s).1⟩

theorem zero_time_events (s : ℝ) :
    selfEvent 0 s = Set.univ ∧ detEvent 0 s = Set.univ := by
  refine ⟨(RademacherStrictCube.zero_time 0 s).2.2.1, ?_⟩
  simpa [detEvent] using (RademacherStrictCube.zero_time (s * Real.sqrt (0 : ℝ)) s).1

theorem actual_event_bridges (n : ℕ) (hn : 0 < n)
    (s : ℝ) (a : Shao.Path n) :
    (a ∈ selfEvent n s ↔
      Shao.absMax a hn < s * Real.sqrt (Shao.energy a)) ∧
    (a ∈ detEvent n s ↔
      Shao.absMax a hn < s * Real.sqrt (n : ℝ)) ∧
    (Shao.energy a = 0 →
      a ∉ selfEvent n s ∧ (0 < s → a ∈ detEvent n s)) := by
  have hmax (b : ℝ) :
      (∀ j : ℕ, 1 ≤ j → j ≤ n → |Shao.prefixSum a j| < b) ↔
        Shao.absMax a hn < b := by
    constructor
    · intro h
      rcases Shao.absMax_attained a hn with ⟨j, hj, hjn, he⟩
      rw [he]
      exact h j hj hjn
    · intro h j hj hjn
      exact lt_of_le_of_lt (Shao.le_absMax a hn j hj hjn) h
  refine ⟨hmax _, hmax _, ?_⟩
  intro he
  have hz := Shao.absMax_eq_zero_of_energy_eq_zero a hn he
  constructor
  · intro ha
    have h := (hmax _).mp ha
    simpa [hz, he, RademacherS5Assembly.V] using h
  · intro hs
    apply (hmax _).mpr
    rw [hz]
    exact mul_pos hs (Real.sqrt_pos.2 (by exact_mod_cast hn))

private theorem ae_even_prefixes (n : ℕ) :
    ∀ᵐ a : Shao.Path n ∂SparseCriticalDenominator.pathLaw n,
      ∀ j : ℕ, j ≤ n → ∃ z : ℤ, Shao.prefixSum a j = 2 * (z : ℝ) := by
  classical
  have hs : ∀ᵐ z : ℝ ∂SparseCriticalDenominator.law,
      z = 0 ∨ z = 2 ∨ z = -2 := by
    rw [ae_iff]
    simp [SparseCriticalDenominator.law, Measure.add_apply, Measure.smul_apply]
  have hc (i : Fin n) : ∀ᵐ a : Shao.Path n ∂SparseCriticalDenominator.pathLaw n,
      a i = 0 ∨ a i = 2 ∨ a i = -2 := by
    rw [ae_iff] at hs ⊢
    exact Measure.pi_eval_preimage_null (fun _ : Fin n => SparseCriticalDenominator.law)
      (i := i) hs
  filter_upwards [ae_all_iff.2 hc] with a ha
  intro j _
  let z : Fin n → ℤ := fun i => if a i = 0 then 0 else if a i = 2 then 1 else -1
  have hz (i : Fin n) : a i = 2 * (z i : ℝ) := by
    rcases ha i with h | h | h <;> norm_num [z, h]
  refine ⟨∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < j), z i, ?_⟩
  simp only [Shao.prefixSum, Int.cast_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => hz i

theorem zero_energy_mass (n : ℕ) :
    (SparseCriticalDenominator.pathLaw n).real
        {a : Shao.Path n | Shao.energy a = 0} =
      SparseCriticalDenominator.weight n 0 ∧
    SparseCriticalDenominator.weight n 0 = (3 / 4 : ℝ) ^ n := by
  have he : {a : Shao.Path n | Shao.energy a = 0} =ᵐ[SparseCriticalDenominator.pathLaw n]
      {a : Shao.Path n | SparseCriticalDenominator.count a = 0} := by
    filter_upwards [(SparseCriticalDenominator.count_law n).2] with a ha
    apply propext
    simp only [Set.mem_setOf_eq, ha]
    constructor
    · intro h
      have : (SparseCriticalDenominator.count a : ℝ) = 0 := by linarith
      exact_mod_cast this
    · intro h
      simp [h]
  constructor
  · rw [measureReal_congr he]
    exact (SparseCriticalDenominator.count_law n).1 0
  · simp [SparseCriticalDenominator.weight]

theorem strict_conditional_strip_mass (n k : ℕ) (hk : k ≤ n)
    (h : ℝ) (hh : 0 < h) :
    (SparseCriticalDenominator.pathLaw n).real
      ({a : Shao.Path n | SparseCriticalDenominator.count a = k} ∩
        RademacherStrictCube.strictEvent n (2 * h)) =
      SparseCriticalDenominator.weight n k * RademacherStrictCube.strictP k h := by
  classical
  let H : ℝ := ((Nat.ceil h - 1 : ℕ) : ℝ)
  have hb := RademacherRealStrictBoundary.ceil_boundary_bridge k h hh
  have hH : 0 ≤ H := Nat.cast_nonneg _
  have hae :
      ({a : Shao.Path n | SparseCriticalDenominator.count a = k} ∩
        RademacherStrictCube.strictEvent n (2 * h)) =ᵐ[SparseCriticalDenominator.pathLaw n]
      ({a : Shao.Path n | SparseCriticalDenominator.count a = k} ∩
        @Shao.closedStrip n (2 * H)) := by
    filter_upwards [ae_even_prefixes n] with a ha
    apply propext
    simp only [Set.mem_inter_iff]
    apply and_congr_right
    intro _
    let v : Shao.Path n := (1 / 2 : ℝ) • a
    have hv (r : ℕ) (hr : r ≤ n) : ∃ z : ℤ, Shao.prefixSum v r = (z : ℝ) := by
      rcases ha r hr with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      simp only [v, Shao.prefixSum_smul, hz]
      ring
    have hc := (RademacherRealStrictBoundary.ceil_boundary_bridge n h hh).2.2.2.2.1 v hv
    have hs : a ∈ RademacherStrictCube.strictEvent n (2 * h) ↔
        v ∈ RademacherStrictCube.strictEvent n h := by
      simp only [RademacherStrictCube.strictEvent, Set.mem_setOf_eq, v,
        Shao.prefixSum_smul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      constructor <;> intro hs r hr hrn <;> have hh' := hs r hr hrn <;> linarith
    have hw : a ∈ @Shao.closedStrip n (2 * H) ↔ v ∈ @Shao.closedStrip n H := by
      simp only [Shao.closedStrip, Set.mem_setOf_eq, v,
        Shao.prefixSum_smul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      constructor <;> intro hs r hr <;> have hh' := hs r hr <;> linarith
    exact hs.trans (hc.trans hw.symm)
  rw [measureReal_congr hae, SparseCriticalDenominator.conditional_strip_mass n k hk H hH,
    hb.2.2.2.2.2.2]
  rfl

-- Positive n and positive s are deliberate. The self formula explicitly
-- subtracts the compressed time-zero term, which is not the original event.
theorem exact_mixtures (n : ℕ) (hn : 0 < n) (s : ℝ) (hs : 0 < s) :
    (SparseCriticalDenominator.pathLaw n).real (selfEvent n s) =
      (∑ k ∈ Finset.range (n + 1),
        SparseCriticalDenominator.weight n k *
          RademacherStrictCube.strictP k (s * Real.sqrt (k : ℝ))) -
        SparseCriticalDenominator.weight n 0 ∧
    (SparseCriticalDenominator.pathLaw n).real (detEvent n s) =
      (∑ k ∈ Finset.range (n + 1),
        SparseCriticalDenominator.weight n k *
          RademacherStrictCube.strictP k (s * Real.sqrt (n : ℝ) / 2)) := by
  classical
  letI : IsProbabilityMeasure (SparseCriticalDenominator.pathLaw n) := by
    dsimp only [SparseCriticalDenominator.pathLaw]
    infer_instance
  let C (k : ℕ) : Set (Shao.Path n) := {a | SparseCriticalDenominator.count a = k}
  have hmc : Measurable (@SparseCriticalDenominator.count n) := by
    have he (a : Shao.Path n) : SparseCriticalDenominator.count a =
        ∑ i : Fin n, if a i ≠ 0 then (1 : ℕ) else 0 := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, smul_eq_mul, mul_one, SparseCriticalDenominator.count]
    have hi (i : Fin n) : Measurable
        (fun a : Shao.Path n => if a i ≠ 0 then (1 : ℕ) else 0) := by
      exact Measurable.ite
        (isClosed_eq (continuous_apply i) continuous_const).measurableSet.compl
        measurable_const measurable_const
    convert Finset.measurable_sum (Finset.univ : Finset (Fin n)) (fun i _ => hi i) using 1
    funext a
    exact he a
  have hmC (k : ℕ) : MeasurableSet (C k) := hmc (measurableSet_singleton k)
  have hcountle (a : Shao.Path n) : SparseCriticalDenominator.count a ≤ n := by
    simpa only [SparseCriticalDenominator.count, Finset.card_univ, Fintype.card_fin] using
      Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => a i ≠ 0)
  have hpart (E : Set (Shao.Path n)) (hE : MeasurableSet E) :
      (SparseCriticalDenominator.pathLaw n).real E =
        ∑ k ∈ Finset.range (n + 1), (SparseCriticalDenominator.pathLaw n).real (C k ∩ E) := by
    have hEeq : E = ⋃ k ∈ Finset.range (n + 1), C k ∩ E := by
      ext a
      constructor
      · intro ha
        exact Set.mem_iUnion.mpr ⟨SparseCriticalDenominator.count a,
          Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hcountle a)), rfl, ha⟩⟩
      · intro ha
        rcases Set.mem_iUnion.mp ha with ⟨k, ha⟩
        rcases Set.mem_iUnion.mp ha with ⟨_, ha⟩
        exact ha.2
    conv_lhs => rw [hEeq]
    apply measureReal_biUnion_finset
    · intro i _ j _ hij
      apply Set.disjoint_left.2
      rintro a ⟨hai, _⟩ ⟨haj, _⟩
      exact hij (hai.symm.trans haj)
    · intro k _
      exact (hmC k).inter hE
    · intro k _
      exact measure_ne_top _ _
  have hself (k : ℕ) (hk : k ≤ n) :
      (SparseCriticalDenominator.pathLaw n).real (C k ∩ selfEvent n s) =
        if k = 0 then 0 else SparseCriticalDenominator.weight n k *
          RademacherStrictCube.strictP k (s * Real.sqrt (k : ℝ)) := by
    by_cases hk0 : k = 0
    · subst k
      rw [if_pos rfl]
      have he : C 0 ∩ selfEvent n s =ᵐ[SparseCriticalDenominator.pathLaw n] ∅ := by
        filter_upwards [(SparseCriticalDenominator.count_law n).2] with a ha
        apply propext
        simp only [Set.mem_empty_iff_false, iff_false, Set.mem_inter_iff]
        rintro ⟨hc, hs'⟩
        have hc' : SparseCriticalDenominator.count a = 0 := hc
        have hz : Shao.energy a = 0 := by simp only [hc', Nat.cast_zero, mul_zero] at ha; exact ha
        exact (actual_event_bridges n hn s a).2.2 hz |>.1 hs'
      rw [measureReal_congr he]
      simp
    · rw [if_neg hk0]
      have hroot : Real.sqrt (4 * (k : ℝ)) = 2 * Real.sqrt (k : ℝ) := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      have he : C k ∩ selfEvent n s =ᵐ[SparseCriticalDenominator.pathLaw n]
          C k ∩ RademacherStrictCube.strictEvent n (2 * (s * Real.sqrt (k : ℝ))) := by
        filter_upwards [(SparseCriticalDenominator.count_law n).2] with a ha
        apply propext
        by_cases hc : SparseCriticalDenominator.count a = k
        · simp only [C, Set.mem_inter_iff, Set.mem_setOf_eq, hc, true_and,
            selfEvent, RademacherStrictCube.strictSelfNormalizedEvent, RademacherS5Assembly.V,
            RademacherStrictCube.strictEvent, ha, hc, hroot,
            show s * (2 * Real.sqrt (k : ℝ)) = 2 * (s * Real.sqrt (k : ℝ)) by ring]
        · simp only [C, Set.mem_inter_iff, Set.mem_setOf_eq, hc, false_and]
      rw [measureReal_congr he]
      exact strict_conditional_strip_mass n k hk _
        (mul_pos hs (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hk0)))
  constructor
  · rw [hpart _ (measurable_events n s).1]
    have hsum : (∑ k ∈ Finset.range (n + 1),
        (SparseCriticalDenominator.pathLaw n).real (C k ∩ selfEvent n s)) =
        ∑ k ∈ Finset.range (n + 1),
          (SparseCriticalDenominator.weight n k *
            RademacherStrictCube.strictP k (s * Real.sqrt (k : ℝ)) -
            if k = 0 then SparseCriticalDenominator.weight n 0 else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hself k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
      by_cases hz : k = 0
      · subst k
        simp [(RademacherStrictCube.zero_time 0 s).2.1]
      · simp [hz]
    rw [hsum, Finset.sum_sub_distrib]
    simp
  · rw [hpart _ (measurable_events n s).2]
    apply Finset.sum_congr rfl
    intro k hk
    have hw : 2 * (s * Real.sqrt (n : ℝ) / 2) = s * Real.sqrt (n : ℝ) := by ring
    simpa only [C, detEvent, hw] using
      strict_conditional_strip_mass n k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
        (s * Real.sqrt (n : ℝ) / 2) (by positivity)

private theorem rade_comparison (n : ℕ) (h : ℝ) (hh : 0 ≤ h) :
    0 ≤ RademacherStrictCube.strictP n h ∧
    RademacherStrictCube.strictP n h ≤ RademacherS4Assembly.p n h ∧
    RademacherS4Assembly.p n h ≤ 1 ∧
    ((∀ z : ℤ, h ≠ (z : ℝ)) →
      RademacherStrictCube.strictP n h = RademacherS4Assembly.p n h) := by
  classical
  letI : IsProbabilityMeasure (RademacherS5Assembly.pathLaw n) :=
    (RademacherStrictCube.actual_path_support n).1
  have he : RademacherS4Assembly.p n h =
      (RademacherS5Assembly.pathLaw n).real (@Shao.closedStrip n h) := rfl
  have hsub : RademacherStrictCube.strictEvent n h ⊆ @Shao.closedStrip n h := by
    intro a ha j hj
    by_cases hz : j = 0
    · simp [hz, hh]
    · exact (ha j (by omega) hj).le
  refine ⟨measureReal_nonneg, ?_, ?_, ?_⟩
  · rw [he]
    exact measureReal_mono hsub
  · rw [he]
    exact measureReal_le_one
  · intro hni
    have hae : RademacherStrictCube.strictEvent n h =ᵐ[RademacherS5Assembly.pathLaw n]
        @Shao.closedStrip n h := by
      filter_upwards [(RademacherStrictCube.actual_path_support n).2.2] with a ha
      apply propext
      constructor
      · exact fun h => hsub h
      · intro hw j hj hjn
        have hle := hw j hjn
        apply lt_of_le_of_ne hle
        intro heq
        rcases ha.2.1 j hjn with ⟨z, hz⟩
        have hzabs : |(z : ℝ)| = ((|z| : ℤ) : ℝ) := Int.cast_abs.symm
        rw [hz, hzabs] at heq
        exact hni |z| heq.symm
    change (RademacherS5Assembly.pathLaw n).real _ = _
    rw [measureReal_congr hae, ← he]

private theorem weight_successor (n k : ℕ) (hk : k < n) :
    (3 * ((k : ℝ) + 1)) * SparseCriticalDenominator.weight n (k + 1) =
      ((n : ℝ) - (k : ℝ)) * SparseCriticalDenominator.weight n k := by
  have hrec : ((k + 1 : ℕ) : ℝ) * (n.choose (k + 1) : ℝ) =
      ((n - k : ℕ) : ℝ) * (n.choose k : ℝ) := by
    have hn : 0 < n := by omega
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    have h1 := Nat.add_one_mul_choose_eq r k
    have h2 := Nat.choose_mul_succ_eq r k
    have he : (k + 1) * (r + 1).choose (k + 1) = (r + 1 - k) * (r + 1).choose k := by
      nlinarith
    exact_mod_cast he
  have hsub : n - k = (n - (k + 1)) + 1 := by omega
  have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
    exact Nat.cast_sub hk.le
  have hp : (3 / 4 : ℝ) ^ (n - k) = (3 / 4 : ℝ) ^ (n - (k + 1)) * (3 / 4) := by
    rw [hsub, pow_succ]
  unfold SparseCriticalDenominator.weight
  rw [pow_succ, hp]
  push_cast at hrec
  rw [hcast] at hrec
  have hh := congrArg (fun x : ℝ => x * ((1 / 4 : ℝ) ^ k *
    (3 / 4 : ℝ) ^ (n - (k + 1)))) hrec
  nlinarith

private theorem central_adjacent_lower (m : ℕ) (hm : 2 ≤ m)
    (r : ℕ) (hr : r ≤ m) :
    (1 - (r : ℝ) / (2 * (m : ℝ))) *
        SparseCriticalDenominator.weight (SparseCriticalDenominator.time m)
          (SparseCriticalDenominator.meanIndex m) ≤
      SparseCriticalDenominator.weight (SparseCriticalDenominator.time m)
        (SparseCriticalDenominator.meanIndex m + r) := by
  have hm1 : 1 ≤ m := by omega
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hn := (SparseCriticalDenominator.critical_scale m hm1).1
  have hnon := (SparseCriticalDenominator.binomial_payments m hm1).1
  have hmu : (SparseCriticalDenominator.meanIndex m : ℝ) = 2 * (m : ℝ) ^ 3 := by
    simp [SparseCriticalDenominator.meanIndex]
  have hnR : (SparseCriticalDenominator.time m : ℝ) = 8 * (m : ℝ) ^ 3 := by
    exact_mod_cast hn
  have hstep (j : ℕ) (hj : j < m) :
      (1 - 1 / (2 * (m : ℝ))) *
        SparseCriticalDenominator.weight (SparseCriticalDenominator.time m)
          (SparseCriticalDenominator.meanIndex m + j) ≤
      SparseCriticalDenominator.weight (SparseCriticalDenominator.time m)
        (SparseCriticalDenominator.meanIndex m + (j + 1)) := by
    have hjR : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
    have hnNat : SparseCriticalDenominator.meanIndex m + j < SparseCriticalDenominator.time m := by
      rw [hn, SparseCriticalDenominator.meanIndex]
      have hmp : m ≤ m ^ 3 := by
        calc
          m = m * 1 := by omega
          _ ≤ m * (m * m) := Nat.mul_le_mul_left _ (by nlinarith)
          _ = m ^ 3 := by ring
      omega
    have hrec := weight_successor _ _ hnNat
    push_cast at hrec
    rw [hmu, hnR] at hrec
    have hcoef :
        (3 * (2 * (m : ℝ) ^ 3 + j + 1)) * (1 - 1 / (2 * (m : ℝ))) ≤
          8 * (m : ℝ) ^ 3 - (2 * (m : ℝ) ^ 3 + j) := by
      apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < 2 * m by positivity)).mp
      field_simp
      have hcube : 0 ≤ ((m : ℝ) - 2) * (m : ℝ) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      nlinarith
    have hcpos : 0 < 3 * (2 * (m : ℝ) ^ 3 + j + 1) := by positivity
    have hh := mul_le_mul_of_nonneg_right hcoef
      (hnon (SparseCriticalDenominator.meanIndex m + j))
    have hindex : SparseCriticalDenominator.meanIndex m + j + 1 =
        SparseCriticalDenominator.meanIndex m + (j + 1) := by omega
    rw [hindex] at hrec
    nlinarith
  have hall : ∀ j : ℕ, j ≤ m →
      (1 - (j : ℝ) / (2 * (m : ℝ))) *
          SparseCriticalDenominator.weight (SparseCriticalDenominator.time m)
            (SparseCriticalDenominator.meanIndex m) ≤
        SparseCriticalDenominator.weight (SparseCriticalDenominator.time m)
          (SparseCriticalDenominator.meanIndex m + j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have hj0 : j < m := by omega
      have hprev := ih (by omega)
      have hs := hstep j hj0
      have hc : 0 ≤ 1 - 1 / (2 * (m : ℝ)) := by
        apply sub_nonneg.mpr
        exact (div_le_one (by positivity)).mpr (by linarith)
      have hmul := mul_le_mul_of_nonneg_left hprev hc
      have hfac : 1 - ((j + 1 : ℕ) : ℝ) / (2 * (m : ℝ)) ≤
          (1 - 1 / (2 * (m : ℝ))) * (1 - (j : ℝ) / (2 * (m : ℝ))) := by
        have hid : (1 - 1 / (2 * (m : ℝ))) * (1 - (j : ℝ) / (2 * (m : ℝ))) -
            (1 - ((j + 1 : ℕ) : ℝ) / (2 * (m : ℝ))) = (j : ℝ) / (2 * (m : ℝ)) ^ 2 := by
          push_cast
          field_simp
          ring
        have hp : 0 ≤ (j : ℝ) / (2 * (m : ℝ)) ^ 2 := by positivity
        linarith
      have hh := (mul_le_mul_of_nonneg_right hfac
        (hnon (SparseCriticalDenominator.meanIndex m))).trans
          (by simpa only [mul_assoc] using hmul.trans hs)
      exact hh
  exact hall r hr

private theorem central_atom_bound (m : ℕ) (hm : 2 ≤ m) :
    SparseCriticalDenominator.weight (SparseCriticalDenominator.time m)
        (SparseCriticalDenominator.meanIndex m) ≤
      2 / ((m : ℝ) + 1) := by
  classical
  have hm1 : 1 ≤ m := by omega
  have hp := SparseCriticalDenominator.binomial_payments m hm1
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  let J := (Finset.range (m + 1)).image (fun j => SparseCriticalDenominator.meanIndex m + j)
  have hinj : Function.Injective (fun j : ℕ => SparseCriticalDenominator.meanIndex m + j) :=
    fun _ _ h => Nat.add_left_cancel h
  have hcard : J.card = m + 1 := by
    dsimp [J]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hsub : J ⊆ Finset.range (SparseCriticalDenominator.time m + 1) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
    have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [Finset.mem_range, (SparseCriticalDenominator.critical_scale m hm1).1,
      SparseCriticalDenominator.meanIndex]
    have hmp : m ≤ m ^ 3 := by
      calc
        m = m * 1 := by omega
        _ ≤ m * (m * m) := Nat.mul_le_mul_left _ (by nlinarith)
        _ = m ^ 3 := by ring
    omega
  have hlow : ((m : ℝ) + 1) *
      (SparseCriticalDenominator.weight (SparseCriticalDenominator.time m)
        (SparseCriticalDenominator.meanIndex m) / 2) ≤
      ∑ k ∈ J, SparseCriticalDenominator.weight (SparseCriticalDenominator.time m) k := by
    calc
      _ = ∑ k ∈ J, SparseCriticalDenominator.weight (SparseCriticalDenominator.time m)
          (SparseCriticalDenominator.meanIndex m) / 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul, hcard, Nat.cast_add, Nat.cast_one]
      _ ≤ _ := Finset.sum_le_sum fun k hk => by
        rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
        have hjm := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have ha := central_adjacent_lower m hm j hjm
        have hjR : (j : ℝ) ≤ m := by exact_mod_cast hjm
        have hfac : (1 / 2 : ℝ) ≤ 1 - (j : ℝ) / (2 * (m : ℝ)) := by
          apply (le_sub_iff_add_le).mpr
          have : (j : ℝ) / (2 * (m : ℝ)) ≤ 1 / 2 := by
            apply (div_le_iff₀ (by positivity)).mpr
            nlinarith
          linarith
        have hz := mul_le_mul_of_nonneg_right hfac
          (hp.1 (SparseCriticalDenominator.meanIndex m))
        nlinarith
  have hup : (∑ k ∈ J, SparseCriticalDenominator.weight (SparseCriticalDenominator.time m) k) ≤ 1 := by
    rw [← hp.2.1]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hp.1 k)
  apply (le_div_iff₀ (show (0 : ℝ) < (m : ℝ) + 1 by positivity)).mpr
  nlinarith

private theorem integer_height_iff (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    (∃ z : ℤ, SparseCriticalDenominator.randomHeight m k = (z : ℝ)) ↔
      ∃ j : ℕ, k = 2 * m * j ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hx := (SparseCriticalDenominator.critical_scale m hm).2.2.2.1
  have hnon : 0 ≤ SparseCriticalDenominator.randomHeight m k := by
    unfold SparseCriticalDenominator.randomHeight
    exact mul_nonneg (SparseCriticalDenominator.critical_scale m hm).2.2.1.le
      (Real.sqrt_nonneg _)
  have hsq : SparseCriticalDenominator.randomHeight m k ^ 2 = (k : ℝ) / (2 * (m : ℝ)) := by
    unfold SparseCriticalDenominator.randomHeight
    rw [hx, mul_pow, div_pow, one_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (Nat.cast_nonneg k)]
    ring
  constructor
  · rintro ⟨z, hz⟩
    have hz0 : 0 ≤ z := by exact_mod_cast (hz ▸ hnon)
    refine ⟨z.toNat, ?_⟩
    have hzc : (z : ℝ) = (z.toNat : ℝ) := by exact_mod_cast (Int.toNat_of_nonneg hz0).symm
    rw [hz, hzc] at hsq
    have he : (k : ℝ) = 2 * (m : ℝ) * (z.toNat : ℝ) ^ 2 := by
      apply (eq_div_iff (by positivity : (2 * (m : ℝ)) ≠ 0)).mp at hsq
      nlinarith
    exact_mod_cast he
  · rintro ⟨j, rfl⟩
    refine ⟨(j : ℤ), ?_⟩
    push_cast at hsq ⊢
    have he : SparseCriticalDenominator.randomHeight m (2 * m * j ^ 2) ^ 2 = (j : ℝ) ^ 2 := by
      rw [hsq]
      field_simp
    nlinarith [sq_nonneg (SparseCriticalDenominator.randomHeight m (2 * m * j ^ 2) - (j : ℝ))]

private theorem integer_height_separation (m : ℕ) (hm : 1 ≤ m)
    (k : ℕ)
    (hhit : ∃ z : ℤ, SparseCriticalDenominator.randomHeight m k = (z : ℝ))
    (hne : k ≠ SparseCriticalDenominator.meanIndex m) :
    2 * (m : ℝ) ^ 2 ≤
      |(k : ℝ) - (SparseCriticalDenominator.meanIndex m : ℝ)| := by
  rcases (integer_height_iff m hm k).mp hhit with ⟨j, rfl⟩
  have hjm : j ≠ m := by
    intro he
    apply hne
    rw [he, SparseCriticalDenominator.meanIndex]
    ring
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmu : (SparseCriticalDenominator.meanIndex m : ℝ) = 2 * (m : ℝ) ^ 3 := by
    simp [SparseCriticalDenominator.meanIndex]
  rw [hmu]
  push_cast
  rcases lt_or_gt_of_ne hjm with hj | hj
  · have hjR : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
    have hs : (j : ℝ) ^ 2 ≤ ((m : ℝ) - 1) ^ 2 := by nlinarith
    apply le_trans _ (neg_le_abs _)
    have hmpos : (0 : ℝ) ≤ m := by positivity
    nlinarith [mul_nonneg hmpos (sub_nonneg.mpr hs)]
  · have hjR : (m : ℝ) + 1 ≤ j := by exact_mod_cast hj
    have hs : ((m : ℝ) + 1) ^ 2 ≤ (j : ℝ) ^ 2 := by nlinarith
    apply le_trans _ (le_abs_self _)
    have hmpos : (0 : ℝ) ≤ m := by positivity
    nlinarith [mul_nonneg hmpos (sub_nonneg.mpr hs)]

private theorem integer_hit_mass_bound (m : ℕ) (hm : 2 ≤ m) :
    0 ≤ integerHitMass m ∧
    integerHitMass m ≤ 2 / ((m : ℝ) + 1) + 3 / (8 * (m : ℝ)) := by
  classical
  have hm1 : 1 ≤ m := by omega
  have hp := SparseCriticalDenominator.binomial_payments m hm1
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  let W (k : ℕ) := SparseCriticalDenominator.weight (SparseCriticalDenominator.time m) k
  let D (k : ℕ) := (k : ℝ) - (SparseCriticalDenominator.meanIndex m : ℝ)
  have hi (k : ℕ) : RademacherStrictWeakBoundary.integerIndicator
      (SparseCriticalDenominator.randomHeight m k) = 0 ∨
      RademacherStrictWeakBoundary.integerIndicator
        (SparseCriticalDenominator.randomHeight m k) = 1 := by
    unfold RademacherStrictWeakBoundary.integerIndicator
    split <;> simp
  have hn : 0 ≤ integerHitMass m := by
    apply Finset.sum_nonneg
    intro k _
    apply mul_nonneg (hp.1 k)
    rcases hi k with h | h <;> simp [h]
  refine ⟨hn, ?_⟩
  have hbound (k : ℕ) :
      W k * RademacherStrictWeakBoundary.integerIndicator (SparseCriticalDenominator.randomHeight m k) ≤
        (if k = SparseCriticalDenominator.meanIndex m then W k else 0) +
          W k * D k ^ 2 / (4 * (m : ℝ) ^ 4) := by
    by_cases hk : k = SparseCriticalDenominator.meanIndex m
    · subst k
      simp only [if_pos rfl, D, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
        zero_div, add_zero]
      rcases hi (SparseCriticalDenominator.meanIndex m) with h | h <;> simp [h, W, hp.1]
    · rw [if_neg hk, zero_add]
      by_cases hh : ∃ z : ℤ, SparseCriticalDenominator.randomHeight m k = (z : ℝ)
      · have hI : RademacherStrictWeakBoundary.integerIndicator
            (SparseCriticalDenominator.randomHeight m k) = 1 := by
          simp [RademacherStrictWeakBoundary.integerIndicator, hh]
        rw [hI, mul_one]
        have hs := integer_height_separation m hm1 k hh hk
        have hs2 : 4 * (m : ℝ) ^ 4 ≤ D k ^ 2 := by
          dsimp [D]
          nlinarith [sq_abs ((k : ℝ) - (SparseCriticalDenominator.meanIndex m : ℝ)),
            mul_nonneg (sub_nonneg.mpr hs) (show 0 ≤ |(k : ℝ) -
              (SparseCriticalDenominator.meanIndex m : ℝ)| + 2 * (m : ℝ) ^ 2 by positivity)]
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (m : ℝ) ^ 4)).mpr
        exact mul_le_mul_of_nonneg_left hs2 (hp.1 k)
      · simp only [RademacherStrictWeakBoundary.integerIndicator, if_neg hh, mul_zero]
        exact div_nonneg (mul_nonneg (hp.1 k) (sq_nonneg _)) (by positivity)
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range (SparseCriticalDenominator.time m + 1)) => hbound k)
  have hmem : SparseCriticalDenominator.meanIndex m < SparseCriticalDenominator.time m + 1 := by
    rw [(SparseCriticalDenominator.critical_scale m hm1).2.1]
    omega
  have heq : (∑ k ∈ Finset.range (SparseCriticalDenominator.time m + 1),
      ((if k = SparseCriticalDenominator.meanIndex m then W k else 0) +
        W k * D k ^ 2 / (4 * (m : ℝ) ^ 4))) =
      W (SparseCriticalDenominator.meanIndex m) + 3 / (8 * (m : ℝ)) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div]
    simp only [Finset.sum_ite_eq', Finset.mem_range, hmem, if_pos]
    have hv : (∑ k ∈ Finset.range (SparseCriticalDenominator.time m + 1), W k * D k ^ 2) =
        (3 / 2 : ℝ) * (m : ℝ) ^ 3 := hp.2.2.1
    rw [hv]
    field_simp
    ring
  change integerHitMass m ≤ _ at hs
  rw [heq] at hs
  have hc := central_atom_bound m hm
  dsimp only [W] at hs
  linarith

private theorem brownian_baseline_lower {Ω : Type u} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ m : ℕ, J ≤ m →
      (2 / Real.pi) * Real.exp (-(Real.pi ^ 2 / 4) * (m : ℝ)) ≤
        SparseCriticalDenominator.baseline B P hB m ∧
      0 < SparseCriticalDenominator.baseline B P hB m := by
  let lam : ℝ := Real.pi ^ 2 / 8
  have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpositive : ∀ᶠ m : ℕ in atTop, 1 ≤ m := eventually_ge_atTop 1
  have baseline_lower : ∀ᶠ m : ℕ in atTop,
      0 < SparseCriticalDenominator.baseline B P hB m ∧
      (2 / Real.pi) * Real.exp (-2 * lam * (m : ℝ)) ≤ SparseCriticalDenominator.baseline B P hB m := by
    have hxlim : Tendsto SparseCriticalDenominator.criticalX atTop (𝓝 (0 : ℝ)) := by
      have hs : Tendsto (fun m : ℕ => Real.sqrt (2 * (m : ℝ))) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp (hnat.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
      have h := tendsto_inv_atTop_zero.comp hs
      apply h.congr'
      filter_upwards [hpositive] with m hm
      simpa only [Function.comp_def, one_div] using (SparseCriticalDenominator.critical_scale m hm).2.2.2.1.symm
    obtain ⟨δ, hδ, hsmall⟩ := Shao.Probability.BrownianSup.actual_brownian_firstTerm
      B P hB (1 / 2) (by norm_num)
    filter_upwards [hpositive, hxlim.eventually (eventually_lt_nhds hδ)] with m hm hxδ
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
    rcases SparseCriticalDenominator.critical_scale m hm with ⟨_, _, hx, hxval, _⟩
    have hg : 0 < Shao.Probability.BrownianSup.firstTerm (SparseCriticalDenominator.criticalX m) := by
      dsimp [Shao.Probability.BrownianSup.firstTerm]
      exact mul_pos (div_pos (by norm_num) Real.pi_pos) (Real.exp_pos _)
    have hratio := (abs_lt.mp (hsmall (SparseCriticalDenominator.criticalX m) hx hxδ)).1
    have hbhalf : Shao.Probability.BrownianSup.firstTerm (SparseCriticalDenominator.criticalX m) / 2 <
        SparseCriticalDenominator.baseline B P hB m := by
      have hratio' : (1 / 2 : ℝ) < SparseCriticalDenominator.baseline B P hB m /
          Shao.Probability.BrownianSup.firstTerm (SparseCriticalDenominator.criticalX m) := by
        change -(1 / 2 : ℝ) < SparseCriticalDenominator.baseline B P hB m /
          Shao.Probability.BrownianSup.firstTerm (SparseCriticalDenominator.criticalX m) - 1 at hratio
        linarith
      have hmul := (lt_div_iff₀ hg).mp hratio'
      linarith
    have hgformula : Shao.Probability.BrownianSup.firstTerm (SparseCriticalDenominator.criticalX m) / 2 =
        (2 / Real.pi) * Real.exp (-2 * lam * (m : ℝ)) := by
      have hs : 0 ≤ 2 * (m : ℝ) := by positivity
      have hx2 : SparseCriticalDenominator.criticalX m ^ 2 = 1 / (2 * (m : ℝ)) := by
        rw [hxval, one_div_pow, Real.sq_sqrt hs]
      dsimp [Shao.Probability.BrownianSup.firstTerm]
      rw [hx2]
      have hexp : -(Real.pi ^ 2 / 8) / (1 / (2 * (m : ℝ))) =
          -2 * lam * (m : ℝ) := by
        dsimp [lam]
        field_simp [hmpos.ne']
        <;> ring
      rw [hexp]
      ring
    refine ⟨lt_trans (by positivity : 0 < Shao.Probability.BrownianSup.firstTerm (SparseCriticalDenominator.criticalX m) / 2)
      hbhalf, ?_⟩
    rw [← hgformula]
    exact hbhalf.le

  obtain ⟨J, hJ⟩ := eventually_atTop.1 baseline_lower
  refine ⟨max J 1, le_max_right _ _, ?_⟩
  intro m hm
  have hb := hJ m (le_trans (le_max_left _ _) hm)
  refine ⟨?_, hb.1⟩
  convert hb.2 using 1 <;> dsimp [lam] <;> congr 1 <;> ring

private theorem rare_payments {Ω : Type u} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    Tendsto (fun m : ℕ =>
      lowMass m / SparseCriticalDenominator.baseline B P hB m)
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun m : ℕ =>
      SparseCriticalDenominator.weight (SparseCriticalDenominator.time m) 0 /
        SparseCriticalDenominator.baseline B P hB m)
      atTop (𝓝 (0 : ℝ)) := by
  let lam : ℝ := Real.pi ^ 2 / 8
  let Low (m : ℕ) := lowMass m / SparseCriticalDenominator.baseline B P hB m
  have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpositive : ∀ᶠ m : ℕ in atTop, 1 ≤ m := eventually_ge_atTop 1
  have wpos (m : ℕ) (hm : 1 ≤ m) (k : ℕ) := (SparseCriticalDenominator.binomial_payments m hm).1 k
  have baseline_lower : ∀ᶠ m : ℕ in atTop,
      0 < SparseCriticalDenominator.baseline B P hB m ∧
      (2 / Real.pi) * Real.exp (-2 * lam * (m : ℝ)) ≤ SparseCriticalDenominator.baseline B P hB m := by
    obtain ⟨J, hJ, hb⟩ := brownian_baseline_lower B P hB
    filter_upwards [eventually_ge_atTop J] with m hm
    have h := hb m hm
    refine ⟨h.2, ?_⟩
    convert h.1 using 1 <;> dsimp [lam] <;> congr 1 <;> ring
  have low_limit : Tendsto Low atTop (𝓝 (0 : ℝ)) := by
    let c0 : ℝ := 1 - 2 / Real.exp 1
    have hc0 : 0 < c0 := by
      have h2 : (2 : ℝ) < Real.exp 1 := by
        have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
        linarith
      have he : 0 < Real.exp 1 := Real.exp_pos _
      dsimp [c0]
      have hd : 2 / Real.exp 1 < 1 := (div_lt_one he).mpr h2
      linarith
    let U (m : ℕ) : ℝ := (Real.pi / 2) *
      Real.exp (-c0 * (m : ℝ) ^ 3 + 2 * lam * (m : ℝ))
    have hcubic : Tendsto (fun m : ℕ => (m : ℝ) ^ 3) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp hnat
    have hneg : Tendsto (fun m : ℕ => -(c0 / 2) * (m : ℝ) ^ 3) atTop atBot := by
      simpa only [Function.comp_def, neg_mul] using tendsto_neg_atTop_atBot.comp
        (hcubic.const_mul_atTop (by positivity : 0 < c0 / 2))
    have hsq : Tendsto (fun m : ℕ => (m : ℝ) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hnat
    have hdom : ∀ᶠ m : ℕ in atTop,
        -c0 * (m : ℝ) ^ 3 + 2 * lam * (m : ℝ) ≤ -(c0 / 2) * (m : ℝ) ^ 3 := by
      filter_upwards [hpositive, hsq.eventually (eventually_ge_atTop (4 * lam / c0))]
        with m hm hm2
      have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      have hmul : 4 * lam ≤ (m : ℝ) ^ 2 * c0 := (div_le_iff₀ hc0).mp hm2
      have hmul' := mul_le_mul_of_nonneg_right hmul hm0
      nlinarith
    have hpoly : Tendsto (fun m : ℕ => -c0 * (m : ℝ) ^ 3 + 2 * lam * (m : ℝ))
        atTop atBot := by
      apply tendsto_atBot.mpr
      intro x
      filter_upwards [hdom, hneg.eventually (eventually_le_atBot x)] with m hm hx
      exact le_trans hm hx
    have hU : Tendsto U atTop (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_def, U, mul_zero] using (Real.tendsto_exp_atBot.comp hpoly).const_mul (Real.pi / 2)
    have hlower : ∀ᶠ m : ℕ in atTop, 0 ≤ Low m := by
      filter_upwards [hpositive, baseline_lower] with m hm hb
      exact div_nonneg (Finset.sum_nonneg fun k hk => wpos m hm k) hb.1.le
    have hupper : ∀ᶠ m : ℕ in atTop, Low m ≤ U m := by
      filter_upwards [hpositive, baseline_lower] with m hm hb
      have hL := (SparseCriticalDenominator.binomial_payments m hm).2.2.2.1
      have hbasepos : 0 < (2 / Real.pi) * Real.exp (-2 * lam * (m : ℝ)) := by positivity
      calc
        Low m ≤ Real.exp (-c0 * (m : ℝ) ^ 3) / SparseCriticalDenominator.baseline B P hB m := by
          exact div_le_div_of_nonneg_right hL hb.1.le
        _ ≤ Real.exp (-c0 * (m : ℝ) ^ 3) /
            ((2 / Real.pi) * Real.exp (-2 * lam * (m : ℝ))) :=
          div_le_div_of_nonneg_left (Real.exp_nonneg _) hbasepos hb.2
        _ = U m := by
          dsimp [U]
          rw [Real.exp_add, show -2 * lam * (m : ℝ) = -(2 * lam * (m : ℝ)) by ring,
            Real.exp_neg]
          field_simp [Real.pi_ne_zero, (Real.exp_pos (2 * lam * (m : ℝ))).ne']
          <;> ring
    exact squeeze_zero' hlower hupper hU

  refine ⟨low_limit, ?_⟩
  apply squeeze_zero' _ _ low_limit
  · filter_upwards [baseline_lower] with m hb
    exact div_nonneg (by unfold SparseCriticalDenominator.weight; positivity) hb.1.le
  · filter_upwards [hpositive, baseline_lower] with m hm hb
    apply div_le_div_of_nonneg_right _ hb.1.le
    apply Finset.single_le_sum (fun k _ => wpos m hm k)
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, pow_pos (by omega : 0 < m) 3⟩

private theorem uniform_random_bound {Ω : Type u} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ m : ℕ, J ≤ m →
      ∀ k : ℕ, m ^ 3 ≤ k → k ≤ SparseCriticalDenominator.time m →
        0 < SparseCriticalDenominator.baseline B P hB m ∧
        RademacherS4Assembly.p k (SparseCriticalDenominator.randomHeight m k) /
            SparseCriticalDenominator.baseline B P hB m ≤
          Real.exp (1 + (Real.pi ^ 2 / 2) * Real.sqrt 2) := by
  obtain ⟨J, hJ, hlog⟩ := SparseCriticalDenominator.uniform_log_pair B P hB 1 (by norm_num)
  refine ⟨J, hJ, ?_⟩
  intro m hm k hl hu
  have hm1 : 1 ≤ m := hJ.trans hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hkpos : 0 < k := lt_of_lt_of_le (pow_pos (by omega : 0 < m) 3) hl
  have hx := SparseCriticalDenominator.critical_scale m hm1
  let H := SparseCriticalDenominator.randomHeight m k
  have hH : 0 < H := mul_pos hx.2.2.1 (Real.sqrt_pos.2 (by exact_mod_cast hkpos))
  have hsq : H ^ 2 = (k : ℝ) / (2 * (m : ℝ)) := by
    dsimp only [H, SparseCriticalDenominator.randomHeight]
    rw [hx.2.2.2.1, mul_pow, div_pow, one_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (Nat.cast_nonneg k)]
    ring
  have hquad : 2 * (m : ℝ) * H ^ 2 = (k : ℝ) := by
    have h := (eq_div_iff (by positivity : (2 * (m : ℝ)) ≠ 0)).mp hsq
    nlinarith
  have hlR : (m : ℝ) ^ 3 ≤ k := by exact_mod_cast hl
  have hHsq : (m : ℝ) ^ 2 ≤ 2 * H ^ 2 := by
    by_contra hh
    have hh' := mul_pos hmR (sub_pos.mpr (lt_of_not_ge hh))
    nlinarith
  have hs2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hprod : (Real.sqrt 2 * H) ^ 2 = 2 * H ^ 2 := by rw [mul_pow, hs2]
  have hroot : (m : ℝ) ≤ Real.sqrt 2 * H := by
    by_contra hh
    have hnon : 0 ≤ Real.sqrt 2 * H := mul_nonneg (Real.sqrt_nonneg _) hH.le
    have hh' := mul_pos (sub_pos.mpr (lt_of_not_ge hh))
      (show 0 < (m : ℝ) + Real.sqrt 2 * H by positivity)
    nlinarith
  have hscale : (k : ℝ) / H ^ 3 ≤ 2 * Real.sqrt 2 := by
    apply (div_le_iff₀ (pow_pos hH 3)).mpr
    have hh := mul_le_mul_of_nonneg_right hroot (show 0 ≤ 2 * H ^ 2 by positivity)
    nlinarith
  have hphase : SparseCriticalDenominator.phaseExponent m k ≤ (Real.pi ^ 2 / 2) * Real.sqrt 2 := by
    have hdelta : (⌊H⌋₊ : ℝ) + 1 - H ≤ 1 := by have := Nat.floor_le hH.le; linarith
    have hsc0 : 0 ≤ (k : ℝ) / H ^ 3 := by positivity
    have ha0 : 0 ≤ Real.pi ^ 2 / 4 := by positivity
    have hmul := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hdelta hsc0) ha0
    have hscale' := mul_le_mul_of_nonneg_left hscale ha0
    dsimp only [SparseCriticalDenominator.phaseExponent]
    change (Real.pi ^ 2 / 4) * ((k : ℝ) / H ^ 3) * ((⌊H⌋₊ : ℝ) + 1 - H) ≤ _
    nlinarith
  have h := hlog m hm k hl hu
  refine ⟨h.1, ?_⟩
  have hlogbound : Real.log (RademacherS4Assembly.p k H /
      SparseCriticalDenominator.baseline B P hB m) ≤ 1 + (Real.pi ^ 2 / 2) * Real.sqrt 2 := by
    have he := (abs_lt.mp h.2.2.2.1).2
    dsimp only [H] at *
    linarith
  have he := Real.exp_le_exp.mpr hlogbound
  rw [Real.exp_log (div_pos h.2.1 h.1)] at he
  exact he

private theorem random_boundary_payment {Ω : Type u} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    Tendsto (fun m : ℕ =>
      SparseCriticalDenominator.randomRatio B P hB m - randomRatio B P hB m)
      atTop (𝓝 (0 : ℝ)) := by
  classical
  let C : ℝ := Real.exp (1 + (Real.pi ^ 2 / 2) * Real.sqrt 2)
  have hC : 0 ≤ C := Real.exp_nonneg _
  have hH : Tendsto integerHitMass atTop (𝓝 (0 : ℝ)) := by
    have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp hnat
    have hinv1 : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun m : ℕ => by linarith) hnat)
    have hb : Tendsto (fun m : ℕ => 2 / ((m : ℝ) + 1) + 3 / (8 * (m : ℝ))) atTop (𝓝 (0 : ℝ)) := by
      convert (hinv1.const_mul 2).add (hinv.const_mul (3 / 8 : ℝ)) using 1
      · funext m
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      · norm_num
    apply squeeze_zero' _ _ hb
    · filter_upwards [eventually_ge_atTop 2] with m hm
      exact (integer_hit_mass_bound m hm).1
    · filter_upwards [eventually_ge_atTop 2] with m hm
      exact (integer_hit_mass_bound m hm).2
  have hmajor := (rare_payments B P hB).1.add (hH.const_mul C)
  obtain ⟨J, hJ, hu⟩ := uniform_random_bound B P hB
  apply squeeze_zero' _ _ (by simpa using hmajor)
  all_goals filter_upwards [eventually_ge_atTop J] with m hm
  all_goals
    have hm1 : 1 ≤ m := hJ.trans hm
    have hscale := SparseCriticalDenominator.critical_scale m hm1
    have htpos : 0 < SparseCriticalDenominator.time m := by
      rw [hscale.1]
      positivity
    have hp := SparseCriticalDenominator.binomial_payments m hm1
    let I := Finset.range (SparseCriticalDenominator.time m + 1)
    let W (k : ℕ) := SparseCriticalDenominator.weight (SparseCriticalDenominator.time m) k
    let p (k : ℕ) := RademacherS4Assembly.p k (SparseCriticalDenominator.randomHeight m k)
    let q (k : ℕ) := RademacherStrictCube.strictP k (SparseCriticalDenominator.randomHeight m k)
    let F := SparseCriticalDenominator.baseline B P hB m
    let T (k : ℕ) := (W k * (p k - q k) + if k = 0 then W 0 else 0) / F
    have hbase : 0 < F := (hu m hm (m ^ 3) le_rfl (by rw [hscale.1]; omega)).1
    have hHnon (k : ℕ) : 0 ≤ SparseCriticalDenominator.randomHeight m k :=
      mul_nonneg hscale.2.2.1.le (Real.sqrt_nonneg _)
    have hcomp (k : ℕ) := rade_comparison k _ (hHnon k)
    have hzero : p 0 = 1 ∧ q 0 = 1 := by
      constructor
      · change (RademacherS5Assembly.pathLaw 0).real (@Shao.closedStrip 0 _) = 1
        have he : @Shao.closedStrip 0 (SparseCriticalDenominator.randomHeight m 0) = Set.univ := by
          ext a
          simp [Shao.closedStrip, SparseCriticalDenominator.randomHeight]
        letI : IsProbabilityMeasure (RademacherS5Assembly.pathLaw 0) :=
          (RademacherStrictCube.actual_path_support 0).1
        rw [he]
        simp
      · exact (RademacherStrictCube.zero_time _ 0).2.1
    have heq : SparseCriticalDenominator.randomRatio B P hB m - randomRatio B P hB m =
        ∑ k ∈ I, T k := by
      have hw := (SparseCriticalDenominator.exact_mixtures (SparseCriticalDenominator.time m)
        (SparseCriticalDenominator.criticalX m) hscale.2.2.1.le).1
      have hs := (exact_mixtures (SparseCriticalDenominator.time m) htpos
        (SparseCriticalDenominator.criticalX m) hscale.2.2.1).1
      have hz : (∑ k ∈ I, if k = 0 then W 0 else 0) = W 0 := by simp [I]
      simp only [SparseCriticalDenominator.randomRatio, randomRatio, hw, hs]
      change (∑ k ∈ I, W k * p k) / F - ((∑ k ∈ I, W k * q k) - W 0) / F = _
      dsimp only [T]
      rw [← Finset.sum_div, Finset.sum_add_distrib, hz]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      ring
    have hnon (k : ℕ) : 0 ≤ T k := by
      apply div_nonneg _ hbase.le
      exact add_nonneg (mul_nonneg (hp.1 k) (sub_nonneg.mpr (hcomp k).2.1))
        (by split_ifs; exact hp.1 0; exact le_rfl)
  · rw [heq]
    exact Finset.sum_nonneg fun k _ => hnon k
  · rw [heq]
    have hpoint (k : ℕ) (hk : k ∈ I) : T k ≤
        (if k < m ^ 3 then W k / F else 0) +
          C * (W k * RademacherStrictWeakBoundary.integerIndicator
            (SparseCriticalDenominator.randomHeight m k)) := by
      have hi0 : 0 ≤ RademacherStrictWeakBoundary.integerIndicator
          (SparseCriticalDenominator.randomHeight m k) := by
        unfold RademacherStrictWeakBoundary.integerIndicator
        split <;> norm_num
      by_cases hl : k < m ^ 3
      · rw [if_pos hl]
        have hT : T k ≤ W k / F := by
          apply div_le_div_of_nonneg_right _ hbase.le
          by_cases hz : k = 0
          · subst k
            simp [hzero]
          · simp only [if_neg hz, add_zero]
            have hp1 := (hcomp k).2.2.1
            have hq0 := (hcomp k).1
            have hh := mul_le_mul_of_nonneg_left (show p k - q k ≤ 1 by dsimp [p, q]; linarith) (hp.1 k)
            simpa using hh
        exact le_trans hT (le_add_of_nonneg_right (mul_nonneg hC (mul_nonneg (hp.1 k) hi0)))
      · rw [if_neg hl, zero_add]
        have hl' : m ^ 3 ≤ k := Nat.le_of_not_gt hl
        have hu' : k ≤ SparseCriticalDenominator.time m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        have hk0 : k ≠ 0 := by have : 0 < m ^ 3 := pow_pos (by omega) 3; omega
        have hz : (if k = 0 then W 0 else 0) = 0 := if_neg hk0
        by_cases hhit : ∃ z : ℤ, SparseCriticalDenominator.randomHeight m k = (z : ℝ)
        · have hI : RademacherStrictWeakBoundary.integerIndicator
              (SparseCriticalDenominator.randomHeight m k) = 1 := by
            simp [RademacherStrictWeakBoundary.integerIndicator, hhit]
          rw [hI, mul_one]
          have hb := (hu m hm k hl' hu').2
          change p k / F ≤ C at hb
          have hq0 : 0 ≤ q k := (hcomp k).1
          dsimp only [T]
          rw [hz, add_zero, mul_div_assoc]
          have hdiff : (p k - q k) / F ≤ C :=
            (div_le_div_of_nonneg_right (sub_le_self _ hq0) hbase.le).trans hb
          nlinarith [mul_le_mul_of_nonneg_left hdiff (hp.1 k)]
        · have hI : RademacherStrictWeakBoundary.integerIndicator
              (SparseCriticalDenominator.randomHeight m k) = 0 := by
            simp [RademacherStrictWeakBoundary.integerIndicator, hhit]
          have hni : ∀ z : ℤ, SparseCriticalDenominator.randomHeight m k ≠ (z : ℝ) := by
            simpa only [not_exists] using hhit
          have he : q k = p k := (hcomp k).2.2.2 hni
          simp [T, hz, he, hI]
    calc
      (∑ k ∈ I, T k) ≤ ∑ k ∈ I,
          ((if k < m ^ 3 then W k / F else 0) + C * (W k *
            RademacherStrictWeakBoundary.integerIndicator (SparseCriticalDenominator.randomHeight m k))) :=
        Finset.sum_le_sum hpoint
      _ = lowMass m / F + C * integerHitMass m := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        congr 1
        rw [lowMass, Finset.sum_div, Finset.sum_filter]
      _ = _ := rfl

private theorem uniform_integer_boundary :
    ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, 1 ≤ J ∧
      ∀ m : ℕ, J ≤ m →
        ∀ k : ℕ, m ^ 3 ≤ k → k ≤ SparseCriticalDenominator.time m →
          0 < RademacherS4Assembly.p k (m : ℝ) ∧
          0 < RademacherStrictCube.strictP k (m : ℝ) ∧
          |Real.log (RademacherS4Assembly.p k (m : ℝ) /
              RademacherStrictCube.strictP k (m : ℝ)) -
            (Real.pi ^ 2 / 4) * ((k : ℝ) / (m : ℝ) ^ 3)| < ε := by
  classical
  intro ε hε
  let G : ℕ → ℕ → Prop := fun m k =>
    0 < RademacherS4Assembly.p k (m : ℝ) ∧
    0 < RademacherStrictCube.strictP k (m : ℝ) ∧
    |Real.log (RademacherS4Assembly.p k (m : ℝ) /
        RademacherStrictCube.strictP k (m : ℝ)) -
      (Real.pi ^ 2 / 4) * ((k : ℝ) / (m : ℝ) ^ 3)| < ε
  have hseq : ∀ (M K : ℕ → ℕ),
      (∀ j : ℕ, j ≤ M j) →
      (∀ j : ℕ, (M j) ^ 3 ≤ K j) →
      (∀ j : ℕ, K j ≤ SparseCriticalDenominator.time (M j)) →
      ∀ᶠ j : ℕ in atTop, G (M j) (K j) := by
    intro M K hM hlow hupp
    have hMnat : Tendsto M atTop atTop :=
      tendsto_atTop_mono hM tendsto_id
    have hMr : Tendsto (fun j : ℕ => (M j : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hMnat
    have hgeom (j : ℕ) (hj : 1 ≤ j) :
        (M j : ℝ) ≤ (K j : ℝ) / (M j : ℝ) ^ 2 ∧
        (K j : ℝ) / (M j : ℝ) ^ 3 ≤ 8 := by
      have hmN : 0 < M j := lt_of_lt_of_le (by omega : 0 < j) (hM j)
      have hm : 0 < (M j : ℝ) := by exact_mod_cast hmN
      have hl : (M j : ℝ) ^ 3 ≤ (K j : ℝ) := by exact_mod_cast hlow j
      have huN : K j ≤ 8 * (M j) ^ 3 := by
        simpa only [SparseCriticalDenominator.time, mul_pow, show (2 : ℕ) ^ 3 = 8 by norm_num]
          using hupp j
      have hu : (K j : ℝ) ≤ 8 * (M j : ℝ) ^ 3 := by exact_mod_cast huN
      constructor
      · apply (le_div_iff₀ (by positivity : 0 < (M j : ℝ) ^ 2)).mpr
        nlinarith only [hl]
      · exact (div_le_iff₀ (by positivity : 0 < (M j : ℝ) ^ 3)).mpr hu
    have hs2 : Tendsto (fun j : ℕ => (K j : ℝ) / (M j : ℝ) ^ 2)
        atTop atTop := by
      apply tendsto_atTop.2
      intro b
      filter_upwards [hMr.eventually (eventually_ge_atTop b),
        eventually_ge_atTop (1 : ℕ)] with j hj hj1
      exact hj.trans (hgeom j hj1).1
    have hs3 : ∃ A : ℝ, 0 < A ∧ ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
        (K j : ℝ) / (M j : ℝ) ^ 3 ≤ A :=
      ⟨8, by norm_num, 1, fun j hj => (hgeom j hj).2⟩
    have hb := RademacherStrictWeakBoundary.boundary_main K
      (fun j : ℕ => (M j : ℝ)) hMr hs2 hs3
    have hlog : ∀ᶠ j : ℕ in atTop,
        |Real.log (RademacherStrictWeakBoundary.ratio (K j) (M j : ℝ)) -
          (Real.pi ^ 2 / 4) * ((K j : ℝ) / (M j : ℝ) ^ 3) *
            RademacherStrictWeakBoundary.integerIndicator (M j : ℝ)| < ε := by
      have he := hb.2.1.eventually (Metric.ball_mem_nhds (0 : ℝ) hε)
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using he
    filter_upwards [hb.1, hlog] with j hj hje
    have hi : RademacherStrictWeakBoundary.integerIndicator (M j : ℝ) = 1 := by
      have hz : ∃ z : ℤ, (M j : ℝ) = (z : ℝ) := ⟨(M j : ℤ), by simp⟩
      simp [RademacherStrictWeakBoundary.integerIndicator, hz]
    refine ⟨?_, hj.2.2.2.1, ?_⟩
    · simpa only [RademacherS5Assembly.p] using hj.2.2.1
    · simpa only [RademacherStrictWeakBoundary.ratio, RademacherS5Assembly.p,
        hi, mul_one] using hje
  have huniform : ∃ J : ℕ, ∀ m : ℕ, J ≤ m → ∀ k : ℕ,
      m ^ 3 ≤ k → k ≤ SparseCriticalDenominator.time m → G m k := by
    by_contra hnone
    push_neg at hnone
    let M : ℕ → ℕ := fun j => Classical.choose (hnone j)
    have hM (j : ℕ) := Classical.choose_spec (hnone j)
    let K : ℕ → ℕ := fun j => Classical.choose (hM j).2
    have hK (j : ℕ) := Classical.choose_spec (hM j).2
    have hgood : ∀ᶠ j : ℕ in atTop, G (M j) (K j) :=
      hseq M K (fun j => (hM j).1)
        (fun j => (hK j).1) (fun j => (hK j).2.1)
    obtain ⟨j, hj⟩ := hgood.exists
    exact (hK j).2.2 hj
  obtain ⟨J, hJ⟩ := huniform
  refine ⟨max J 1, le_max_right _ _, ?_⟩
  intro m hm k hl hu
  exact hJ m (le_trans (le_max_left _ _) hm) k hl hu

private theorem uniform_det_strict_log {Ω : Type u} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, 1 ≤ J ∧
      ∀ m : ℕ, J ≤ m →
        ∀ k : ℕ, m ^ 3 ≤ k → k ≤ SparseCriticalDenominator.time m →
          0 < SparseCriticalDenominator.baseline B P hB m ∧
          0 < RademacherStrictCube.strictP k (m : ℝ) ∧
          |Real.log (RademacherStrictCube.strictP k (m : ℝ) /
              SparseCriticalDenominator.baseline B P hB m) +
            (Real.pi ^ 2 / 8) *
              ((k : ℝ) - (SparseCriticalDenominator.meanIndex m : ℝ)) /
                (m : ℝ) ^ 2| < ε := by
  intro ε hε
  obtain ⟨JW, hJW, hW⟩ := SparseCriticalDenominator.uniform_log_pair B P hB
    (ε / 2) (by positivity)
  obtain ⟨JB, hJB, hBnd⟩ := uniform_integer_boundary (ε / 2) (by positivity)
  refine ⟨max JW JB, le_trans hJW (le_max_left _ _), ?_⟩
  intro m hm k hl hu
  have hw := hW m (le_trans (le_max_left _ _) hm) k hl hu
  have hb := hBnd m (le_trans (le_max_right _ _) hm) k hl hu
  refine ⟨hw.1, hb.2.1, ?_⟩
  have hp : RademacherS4Assembly.p k (m : ℝ) ≠ 0 := ne_of_gt hb.1
  have hq : RademacherStrictCube.strictP k (m : ℝ) ≠ 0 := ne_of_gt hb.2.1
  have hF : SparseCriticalDenominator.baseline B P hB m ≠ 0 := ne_of_gt hw.1
  have hweak := hw.2.2.2.2
  have hboundary := hb.2.2
  rw [Real.log_div hp hF] at hweak
  rw [Real.log_div hp hq] at hboundary
  rw [Real.log_div hq hF]
  have htriangle := abs_sub_le
    (Real.log (RademacherS4Assembly.p k (m : ℝ)) -
      Real.log (SparseCriticalDenominator.baseline B P hB m) +
      (Real.pi ^ 2 / 8) *
        ((k : ℝ) - (SparseCriticalDenominator.meanIndex m : ℝ)) / (m : ℝ) ^ 2 -
      (Real.pi ^ 2 / 4) * ((k : ℝ) / (m : ℝ) ^ 3))
    (0 : ℝ)
    (Real.log (RademacherS4Assembly.p k (m : ℝ)) -
      Real.log (RademacherStrictCube.strictP k (m : ℝ)) -
      (Real.pi ^ 2 / 4) * ((k : ℝ) / (m : ℝ) ^ 3))
  simp only [sub_zero, zero_sub, abs_neg] at htriangle
  have hid :
      (Real.log (RademacherS4Assembly.p k (m : ℝ)) -
        Real.log (SparseCriticalDenominator.baseline B P hB m) +
        (Real.pi ^ 2 / 8) *
          ((k : ℝ) - (SparseCriticalDenominator.meanIndex m : ℝ)) / (m : ℝ) ^ 2 -
        (Real.pi ^ 2 / 4) * ((k : ℝ) / (m : ℝ) ^ 3)) -
      (Real.log (RademacherS4Assembly.p k (m : ℝ)) -
        Real.log (RademacherStrictCube.strictP k (m : ℝ)) -
        (Real.pi ^ 2 / 4) * ((k : ℝ) / (m : ℝ) ^ 3)) =
      Real.log (RademacherStrictCube.strictP k (m : ℝ)) -
        Real.log (SparseCriticalDenominator.baseline B P hB m) +
        (Real.pi ^ 2 / 8) *
          ((k : ℝ) - (SparseCriticalDenominator.meanIndex m : ℝ)) / (m : ℝ) ^ 2 := by ring
  rw [hid] at htriangle
  linarith

private theorem tilt_payments :
    Tendsto tiltMoment atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (fun m : ℕ =>
      ∑ k ∈ (Finset.range (SparseCriticalDenominator.time m + 1)).filter
          (fun k : ℕ => k < m ^ 3),
        SparseCriticalDenominator.weight (SparseCriticalDenominator.time m) k *
          detTilt m k) atTop (𝓝 (0 : ℝ)) := by
  classical
  let lam : ℝ := Real.pi ^ 2 / 8
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpositive : ∀ᶠ m : ℕ in atTop, 1 ≤ m := eventually_ge_atTop 1
  have hinv : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hnat
  have weighted_square (S : Finset ℕ) (w z : ℕ → ℝ)
      (hw : ∀ k ∈ S, 0 ≤ w k) :
      (∑ k ∈ S, w k * z k) ^ 2 ≤
        (∑ k ∈ S, w k) * (∑ k ∈ S, w k * (z k) ^ 2) := by
    let q : ℝ := ∑ k ∈ S, w k
    let s : ℝ := ∑ k ∈ S, w k * z k
    let a : ℝ := ∑ k ∈ S, w k * (z k) ^ 2
    have hq : 0 ≤ q := Finset.sum_nonneg hw
    have ha : 0 ≤ a := Finset.sum_nonneg fun k hk =>
      mul_nonneg (hw k hk) (sq_nonneg _)
    change s ^ 2 ≤ q * a
    by_cases hq0 : q = 0
    · have hz (k : ℕ) (hk : k ∈ S) : w k = 0 := by
        have hsingle : w k ≤ ∑ j ∈ S, w j :=
          Finset.single_le_sum hw hk
        change w k ≤ q at hsingle
        exact le_antisymm (hq0 ▸ hsingle) (hw k hk)
      have hs : s = 0 := Finset.sum_eq_zero fun k hk => by rw [hz k hk, zero_mul]
      rw [hs, hq0]
      norm_num
    · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
      have hnonneg : 0 ≤ ∑ k ∈ S, w k * (z k - s / q) ^ 2 :=
        Finset.sum_nonneg fun k hk => mul_nonneg (hw k hk) (sq_nonneg _)
      have hexpand :
          (∑ k ∈ S, w k * (z k - s / q) ^ 2) =
            a - 2 * (s / q) * s + (s / q) ^ 2 * q := by
        calc
          _ = ∑ k ∈ S,
              (w k * (z k) ^ 2 - (2 * (s / q)) * (w k * z k) +
                (s / q) ^ 2 * w k) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
          _ = _ := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              Finset.mul_sum, q, s, a]
      rw [hexpand] at hnonneg
      have hmult := mul_nonneg hq hnonneg
      have halg : q * (a - 2 * (s / q) * s + (s / q) ^ 2 * q) =
          q * a - s ^ 2 := by
        field_simp [hq0]
        <;> ring
      rw [halg] at hmult
      linarith

  have hupperlim : Tendsto (fun m : ℕ => Real.exp (16 * lam ^ 2 / (m : ℝ)))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero, Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp (hinv.const_mul (16 * lam ^ 2))
  have hlowerlim : Tendsto (fun m : ℕ => 1 - Real.sqrt ((3 / 2 : ℝ) * lam ^ 2 / (m : ℝ)))
      atTop (𝓝 (1 : ℝ)) := by
    have hz : Tendsto (fun m : ℕ => (3 / 2 : ℝ) * lam ^ 2 / (m : ℝ)) atTop (𝓝 (0 : ℝ)) := by
      simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul ((3 / 2 : ℝ) * lam ^ 2)
    simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp hz).const_sub 1
  have hmoment : Tendsto tiltMoment atTop (𝓝 (1 : ℝ)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowerlim hupperlim
    · filter_upwards [hpositive] with m hm
      have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      have hp := SparseCriticalDenominator.binomial_payments m hm
      let I := Finset.range (SparseCriticalDenominator.time m + 1)
      let W (k : ℕ) := SparseCriticalDenominator.weight (SparseCriticalDenominator.time m) k
      let D (k : ℕ) := (k : ℝ) - (SparseCriticalDenominator.meanIndex m : ℝ)
      let t : ℝ := -lam / (m : ℝ) ^ 2
      let S : ℝ := ∑ k ∈ I, W k * D k
      have hs2 : S ^ 2 ≤ (3 / 2 : ℝ) * (m : ℝ) ^ 3 := by
        have hs := weighted_square I W D (fun k _ => hp.1 k)
        have hw : (∑ k ∈ I, W k) = 1 := hp.2.1
        have hv : (∑ k ∈ I, W k * D k ^ 2) = (3 / 2 : ℝ) * (m : ℝ) ^ 3 := hp.2.2.1
        simpa only [hw, hv, one_mul] using hs
      have hexp : 1 + t * S ≤ tiltMoment m := by
        calc
          _ = ∑ k ∈ I, W k * (1 + t * D k) := by
            simp only [mul_add, mul_one, Finset.sum_add_distrib]
            rw [show (∑ k ∈ I, W k) = 1 from hp.2.1]
            dsimp only [S]
            rw [Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro k _
            ring
          _ ≤ _ := Finset.sum_le_sum fun k _ => by
            have he := Real.add_one_le_exp (t * D k)
            have h := mul_le_mul_of_nonneg_left he (hp.1 k)
            have ht : detTilt m k = Real.exp (t * D k) := by
              dsimp [detTilt, t, lam, D]
              congr 1
              ring
            change W k * (1 + t * D k) ≤ W k * detTilt m k
            rw [ht]
            simpa only [add_comm] using h
      have hsquare : (t * S) ^ 2 ≤ (3 / 2 : ℝ) * lam ^ 2 / (m : ℝ) := by
        have hs := mul_le_mul_of_nonneg_left hs2 (sq_nonneg t)
        have he : t ^ 2 * ((3 / 2 : ℝ) * (m : ℝ) ^ 3) =
            (3 / 2 : ℝ) * lam ^ 2 / (m : ℝ) := by
          dsimp [t]
          field_simp <;> ring
        rw [he] at hs
        nlinarith
      have hroot := Real.sq_sqrt (show 0 ≤ (3 / 2 : ℝ) * lam ^ 2 / (m : ℝ) by positivity)
      have habs : |t * S| ≤ Real.sqrt ((3 / 2 : ℝ) * lam ^ 2 / (m : ℝ)) := by
        nlinarith [sq_abs (t * S), Real.sqrt_nonneg ((3 / 2 : ℝ) * lam ^ 2 / (m : ℝ))]
      linarith [neg_abs_le (t * S)]
    · filter_upwards [hpositive,
        ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hnat).eventually
          (eventually_ge_atTop lam)] with m hm hmsq
      have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      let t : ℝ := -lam / (m : ℝ) ^ 2
      have ht : |t| ≤ 1 := by
        dsimp [t]
        rw [abs_div, abs_neg, abs_of_pos hlam, abs_of_pos (sq_pos_of_pos hmR)]
        exact (div_le_one (sq_pos_of_pos hmR)).mpr hmsq
      have hmgf := (SparseCriticalDenominator.binomial_payments m hm).2.2.2.2 t ht
      have hexp : 2 * (SparseCriticalDenominator.time m : ℝ) * t ^ 2 =
          16 * lam ^ 2 / (m : ℝ) := by
        rw [(SparseCriticalDenominator.critical_scale m hm).1]
        dsimp [t]
        push_cast
        field_simp
        ring
      rw [hexp] at hmgf
      convert hmgf using 1
      apply Finset.sum_congr rfl
      intro k _
      dsimp [detTilt, t, lam]
      congr 2
      ring
  refine ⟨hmoment, ?_⟩
  let c : ℝ := 1 - 2 / Real.exp 1
  have hc : 0 < c := by
    have h2 : (2 : ℝ) < Real.exp 1 := by
      have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
      linarith
    have hh : 2 / Real.exp 1 < 1 := (div_lt_one (Real.exp_pos _)).mpr h2
    dsimp [c]
    linarith
  have hcubic : Tendsto (fun m : ℕ => (m : ℝ) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp hnat
  have hsq : Tendsto (fun m : ℕ => (m : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hnat
  have hneg : Tendsto (fun m : ℕ => -(c / 2) * (m : ℝ) ^ 3) atTop atBot := by
    simpa only [Function.comp_def, neg_mul] using tendsto_neg_atTop_atBot.comp
      (hcubic.const_mul_atTop (by positivity : 0 < c / 2))
  have hpoly : Tendsto (fun m : ℕ => -c * (m : ℝ) ^ 3 + 2 * lam * (m : ℝ)) atTop atBot := by
    apply tendsto_atBot.mpr
    intro x
    filter_upwards [hpositive, hsq.eventually (eventually_ge_atTop (4 * lam / c)),
      hneg.eventually (eventually_le_atBot x)] with m hm hmsq hx
    have hmul : 4 * lam ≤ (m : ℝ) ^ 2 * c := (div_le_iff₀ hc).mp hmsq
    have hh := mul_le_mul_of_nonneg_right hmul (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    have hdom : -c * (m : ℝ) ^ 3 + 2 * lam * (m : ℝ) ≤ -(c / 2) * (m : ℝ) ^ 3 := by nlinarith
    exact hdom.trans hx
  have hlim : Tendsto (fun m : ℕ => Real.exp (-c * (m : ℝ) ^ 3 + 2 * lam * (m : ℝ)))
      atTop (𝓝 (0 : ℝ)) := Real.tendsto_exp_atBot.comp hpoly
  apply squeeze_zero' _ _ hlim
  · exact Eventually.of_forall fun m => Finset.sum_nonneg fun k _ =>
      mul_nonneg (by unfold SparseCriticalDenominator.weight; positivity) (Real.exp_nonneg _)
  · filter_upwards [hpositive] with m hm
    have hp := SparseCriticalDenominator.binomial_payments m hm
    have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have ht (k : ℕ) : detTilt m k ≤ Real.exp (2 * lam * (m : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hmu : (SparseCriticalDenominator.meanIndex m : ℝ) = 2 * (m : ℝ) ^ 3 := by
        simp [SparseCriticalDenominator.meanIndex]
      change -lam * ((k : ℝ) - (SparseCriticalDenominator.meanIndex m : ℝ)) / (m : ℝ) ^ 2 ≤ _
      rw [hmu]
      apply (div_le_iff₀ (sq_pos_of_pos hmR)).mpr
      nlinarith [mul_nonneg hlam.le (Nat.cast_nonneg k)]
    calc
      _ ≤ ∑ k ∈ (Finset.range (SparseCriticalDenominator.time m + 1)).filter
          (fun k : ℕ => k < m ^ 3), SparseCriticalDenominator.weight (SparseCriticalDenominator.time m) k *
            Real.exp (2 * lam * (m : ℝ)) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (ht k) (hp.1 k)
      _ = lowMass m * Real.exp (2 * lam * (m : ℝ)) := (Finset.sum_mul _ _ _).symm
      _ ≤ Real.exp (-c * (m : ℝ) ^ 3) * Real.exp (2 * lam * (m : ℝ)) :=
        mul_le_mul_of_nonneg_right hp.2.2.2.1 (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm

theorem critical_limits {Ω : Type u} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    Tendsto (randomRatio B P hB) atTop
      (𝓝 ((1 + Real.exp (Real.pi ^ 2 / 2)) / 2)) ∧
    Tendsto (detRatio B P hB) atTop (𝓝 (1 : ℝ)) := by
  classical
  constructor
  · have h := (SparseCriticalDenominator.critical_limits B P hB).1.sub
      (random_boundary_payment B P hB)
    convert h using 1
    · funext m
      ring
    · ring
  · let L (m : ℕ) :=
      ∑ k ∈ (Finset.range (SparseCriticalDenominator.time m + 1)).filter (fun k : ℕ => k < m ^ 3),
        SparseCriticalDenominator.weight (SparseCriticalDenominator.time m) k * detTilt m k
    let A (m : ℕ) :=
      ∑ k ∈ (Finset.range (SparseCriticalDenominator.time m + 1)).filter (fun k : ℕ => m ^ 3 ≤ k),
        SparseCriticalDenominator.weight (SparseCriticalDenominator.time m) k * detTilt m k
    have hsplit (m : ℕ) : tiltMoment m = L m + A m := by
      dsimp only [tiltMoment, L, A]
      rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k < m ^ 3
      · simp [hk, Nat.not_le.mpr hk]
      · simp [hk, Nat.le_of_not_gt hk]
    have hA : Tendsto A atTop (𝓝 (1 : ℝ)) := by
      have h := tilt_payments.1.sub tilt_payments.2
      convert h using 1
      · funext m
        have hh := hsplit m
        change A m = tiltMoment m - L m
        linarith
      · norm_num
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hcont : ContinuousAt Real.exp (0 : ℝ) := Real.continuous_exp.continuousAt
    obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp hcont (ε / 4) (by positivity)
    let η : ℝ := δ / 2
    have hη : 0 < η := by dsimp [η]; positivity
    have hplus : |Real.exp η - 1| < ε / 4 := by
      have hd : dist η (0 : ℝ) < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos hη]; dsimp [η]; linarith
      simpa only [Real.dist_eq, Real.exp_zero] using hnear hd
    have hminus : |Real.exp (-η) - 1| < ε / 4 := by
      have hd : dist (-η) (0 : ℝ) < δ := by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hη]; dsimp [η]; linarith
      simpa only [Real.dist_eq, Real.exp_zero] using hnear hd
    let D : ℝ := Real.exp η + Real.exp (-η) + 1
    let τ : ℝ := ε / (4 * D)
    have hD : 0 < D := by dsimp [D]; positivity
    have hτ : 0 < τ := by dsimp [τ]; positivity
    have hτeq : 4 * D * τ = ε := by dsimp [τ]; field_simp
    have hprodplus : Real.exp η * τ ≤ ε / 4 := by
      have hd : Real.exp η ≤ D := by dsimp [D]; linarith [Real.exp_pos (-η)]
      have hh := mul_le_mul_of_nonneg_right hd hτ.le
      nlinarith
    have hprodminus : Real.exp (-η) * τ ≤ ε / 4 := by
      have hd : Real.exp (-η) ≤ D := by dsimp [D]; linarith [Real.exp_pos η]
      have hh := mul_le_mul_of_nonneg_right hd hτ.le
      nlinarith
    obtain ⟨JA, hJA⟩ := Metric.tendsto_atTop.mp hA τ hτ
    obtain ⟨JL, hJL⟩ := Metric.tendsto_atTop.mp (rare_payments B P hB).1 (ε / 4) (by positivity)
    obtain ⟨J, hJ, hlog⟩ := uniform_det_strict_log B P hB η hη
    refine ⟨max J (max JA JL), ?_⟩
    intro m hm
    have hmJ : J ≤ m := (le_max_left _ _).trans hm
    have hm1 : 1 ≤ m := hJ.trans hmJ
    have hmJA : JA ≤ m := (le_max_left JA JL).trans ((le_max_right J (max JA JL)).trans hm)
    have hmJL : JL ≤ m := (le_max_right JA JL).trans ((le_max_right J (max JA JL)).trans hm)
    have hAabs : |A m - 1| < τ := by simpa only [Real.dist_eq] using hJA m hmJA
    have hLow : lowMass m / SparseCriticalDenominator.baseline B P hB m < ε / 4 :=
      lt_of_le_of_lt (le_abs_self _) (by simpa only [Real.dist_eq, sub_zero] using hJL m hmJL)
    have hscale := SparseCriticalDenominator.critical_scale m hm1
    have htpos : 0 < SparseCriticalDenominator.time m := by rw [hscale.1]; positivity
    let I := Finset.range (SparseCriticalDenominator.time m + 1)
    let W (k : ℕ) := SparseCriticalDenominator.weight (SparseCriticalDenominator.time m) k
    let q (k : ℕ) := RademacherStrictCube.strictP k (m : ℝ)
    let F := SparseCriticalDenominator.baseline B P hB m
    have hp := SparseCriticalDenominator.binomial_payments m hm1
    have hbase : 0 < F := (hlog m hmJ (m ^ 3) le_rfl (by rw [hscale.1]; omega)).1
    have hqbound (k : ℕ) : 0 ≤ q k ∧ q k ≤ 1 := by
      have hh := rade_comparison k (m : ℝ) (Nat.cast_nonneg m)
      exact ⟨hh.1, hh.2.1.trans hh.2.2.1⟩
    have hR : detRatio B P hB m = ∑ k ∈ I, W k * (q k / F) := by
      have hs := (exact_mixtures (SparseCriticalDenominator.time m) htpos
        (SparseCriticalDenominator.criticalX m) hscale.2.2.1).2
      dsimp only [detRatio]
      rw [hs, hscale.2.2.2.2, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [W, q, F]
      ring
    have hgood (k : ℕ) (hl : m ^ 3 ≤ k) (hu : k ≤ SparseCriticalDenominator.time m) :
        Real.exp (-η) * detTilt m k ≤ q k / F ∧
        q k / F ≤ Real.exp η * detTilt m k := by
      have h := hlog m hmJ k hl hu
      let E := Real.log (q k / F) + (Real.pi ^ 2 / 8) *
        ((k : ℝ) - (SparseCriticalDenominator.meanIndex m : ℝ)) / (m : ℝ) ^ 2
      have he : |E| < η := h.2.2
      have halg : Real.exp E * detTilt m k = q k / F := by
        dsimp only [detTilt]
        rw [← Real.exp_add]
        convert Real.exp_log (div_pos h.2.1 hbase) using 1
        congr 1
        dsimp [E]
        ring
      have hlo := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (abs_lt.mp he).1.le)
        (show 0 ≤ detTilt m k by unfold detTilt; positivity)
      have hup := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (abs_lt.mp he).2.le)
        (show 0 ≤ detTilt m k by unfold detTilt; positivity)
      rw [halg] at hlo hup
      exact ⟨hlo, hup⟩
    have hlow : Real.exp (-η) * A m ≤ detRatio B P hB m := by
      rw [hR]
      change Real.exp (-η) * (∑ k ∈ I.filter (fun k : ℕ => m ^ 3 ≤ k), W k * detTilt m k) ≤ _
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_le_sum
      intro k hk
      by_cases hl : m ^ 3 ≤ k
      · rw [if_pos hl]
        have hh := mul_le_mul_of_nonneg_left (hgood k hl
          (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).1 (hp.1 k)
        nlinarith
      · rw [if_neg hl]
        exact mul_nonneg (hp.1 k) (div_nonneg (hqbound k).1 hbase.le)
    have hupp : detRatio B P hB m ≤ lowMass m / F + Real.exp η * A m := by
      rw [hR]
      have heq : lowMass m / F + Real.exp η * A m =
          ∑ k ∈ I, ((if k < m ^ 3 then W k / F else 0) +
            if m ^ 3 ≤ k then Real.exp η * (W k * detTilt m k) else 0) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [lowMass, Finset.sum_div, Finset.sum_filter]
        · change Real.exp η * (∑ k ∈ I.filter (fun k : ℕ => m ^ 3 ≤ k), W k * detTilt m k) = _
          rw [Finset.mul_sum, Finset.sum_filter]
      rw [heq]
      apply Finset.sum_le_sum
      intro k hk
      by_cases hl : k < m ^ 3
      · rw [if_pos hl, if_neg (Nat.not_le.mpr hl), add_zero]
        have hh := mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (hqbound k).2 hbase.le) (hp.1 k)
        calc
          W k * (q k / F) ≤ W k * (1 / F) := hh
          _ = W k / F := by ring
      · rw [if_neg hl, if_pos (Nat.le_of_not_gt hl), zero_add]
        have hh := mul_le_mul_of_nonneg_left (hgood k (Nat.le_of_not_gt hl)
          (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).2 (hp.1 k)
        nlinarith
    have htermplus : Real.exp η * |A m - 1| < ε / 4 :=
      (mul_lt_mul_of_pos_left hAabs (Real.exp_pos _)).trans_le hprodplus
    have htermminus : Real.exp (-η) * |A m - 1| < ε / 4 :=
      (mul_lt_mul_of_pos_left hAabs (Real.exp_pos _)).trans_le hprodminus
    rw [Real.dist_eq]
    apply abs_lt.mpr
    constructor
    · have hh := mul_le_mul_of_nonneg_left (neg_abs_le (A m - 1)) (Real.exp_nonneg (-η))
      have he := (abs_lt.mp hminus).1
      nlinarith
    · have hh := mul_le_mul_of_nonneg_left (le_abs_self (A m - 1)) (Real.exp_nonneg η)
      have he := (abs_lt.mp hplus).2
      change detRatio B P hB m - 1 < ε
      change lowMass m / F < ε / 4 at hLow
      nlinarith

end Shao.OQ4.SparseStrictCriticalDenominator
