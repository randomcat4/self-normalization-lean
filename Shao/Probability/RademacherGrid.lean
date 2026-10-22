import Shao.OQ4.RademacherCosine
import Mathlib.MeasureTheory.Constructions.Pi
import Shao.Probability.FiniteIID
import Shao.Probability.MeasurablePath
import Shao.Basic.ClosedSurvival
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Finite Rademacher grids

Actual finite product laws used by the Brownian grid comparison.
-/

namespace Shao.Probability.BrownianSup

open MeasureTheory
open scoped BigOperators

private instance rad_probability (n : ℕ) :
    IsProbabilityMeasure (Measure.pi
      (fun _ : Fin n => Shao.OQ4.RademacherCosine.law)) := inferInstance

noncomputable def radMeasure (n : ℕ) : Measure (Shao.Path n) :=
  Measure.pi (fun _ : Fin n => Shao.OQ4.RademacherCosine.law)

noncomputable def radSurvival (n : ℕ) (x : ℝ) : ℝ :=
  (radMeasure n).real (Shao.closedStrip (x * Real.sqrt (n : ℝ)))

def coarseStrip (d m : ℕ) (x : ℝ) : Set (Shao.Path (d * m)) :=
  {a | ∀ j : ℕ, j ≤ d →
    |Shao.prefixSum a (j * m)| ≤ x * Real.sqrt (d * m : ℝ)}

noncomputable def coarseProbability (d m : ℕ) (x : ℝ) : ℝ :=
  (radMeasure (d * m)).real (coarseStrip d m x)

private instance radMeasure_probability (n : ℕ) : IsProbabilityMeasure (radMeasure n) := by
  unfold radMeasure
  infer_instance

private def prepend {n : ℕ} (z : ℝ) (w : Shao.Path n) : Shao.Path (n + 1) :=
  @Fin.cons n (fun _ => ℝ) z w

private theorem measurable_cons (n : ℕ) (z : ℝ) :
    Measurable (prepend z : Shao.Path n → Shao.Path (n + 1)) := by
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [prepend] using (measurable_const : Measurable (fun _ : Shao.Path n => z))
  · simpa [prepend] using (measurable_pi_apply j : Measurable (fun w : Shao.Path n => w j))

private theorem radMeasure_succ (n : ℕ) :
    radMeasure (n + 1) =
      Shao.OQ4.RademacherCosine.halfENNReal • (radMeasure n).map (prepend (1 : ℝ)) +
      Shao.OQ4.RademacherCosine.halfENNReal • (radMeasure n).map (prepend (-1 : ℝ)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  have hpre (z : ℝ) :
      (prepend z : Shao.Path n → Shao.Path (n + 1)) ⁻¹' Set.univ.pi s =
        if z ∈ s 0 then Set.univ.pi (fun i : Fin n => s i.succ) else ∅ := by
    ext w
    simp [prepend, Set.mem_pi, Fin.forall_fin_succ]
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply (measurable_cons n 1) (.univ_pi hs),
    Measure.map_apply (measurable_cons n (-1)) (.univ_pi hs), hpre, hpre,
    Fin.prod_univ_succ]
  simp only [radMeasure, apply_ite, Measure.pi_pi, measure_empty, smul_eq_mul]
  have hlaw : Shao.OQ4.RademacherCosine.law (s 0) =
      Shao.OQ4.RademacherCosine.halfENNReal * (if 1 ∈ s 0 then 1 else 0) +
      Shao.OQ4.RademacherCosine.halfENNReal * (if -1 ∈ s 0 then 1 else 0) := by
    simp only [Shao.OQ4.RademacherCosine.law, Measure.add_apply,
      Measure.smul_apply, Measure.dirac_apply' _ (hs 0), smul_eq_mul,
      Set.indicator_apply, Pi.one_apply]
  rw [hlaw]
  split_ifs <;> simp_all <;> ring

private theorem radMeasure_real_succ (n : ℕ) (A : Set (Shao.Path (n + 1)))
    (hA : MeasurableSet A) :
    (radMeasure (n + 1)).real A =
      ((radMeasure n).real ((prepend (1 : ℝ)) ⁻¹' A) +
       (radMeasure n).real ((prepend (-1 : ℝ)) ⁻¹' A)) / 2 := by
  rw [radMeasure_succ, measureReal_def, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply (measurable_cons n 1) hA,
    Measure.map_apply (measurable_cons n (-1)) hA,
    smul_eq_mul, smul_eq_mul,
    ENNReal.toReal_add
      (ENNReal.mul_ne_top (by norm_num [Shao.OQ4.RademacherCosine.halfENNReal]) (by finiteness))
      (ENNReal.mul_ne_top (by norm_num [Shao.OQ4.RademacherCosine.halfENNReal]) (by finiteness))]
  simp [measureReal_def, Shao.OQ4.RademacherCosine.halfENNReal,
    ENNReal.toReal_mul, ENNReal.toReal_div]
  ring

private theorem prefix_cons (n : ℕ) (w : Shao.Path n) (z : ℝ) (k : ℕ) :
    Shao.prefixSum (prepend z w) (k + 1) = z + Shao.prefixSum w k := by
  simp [prepend, Shao.prefixSum, Fin.sum_univ_succ, Finset.sum_filter]

private def crossing (n : ℕ) (s a : ℝ) : Set (Shao.Path n) :=
  {w | ∃ k : ℕ, k ≤ n ∧ a < |s + Shao.prefixSum w k|}

private theorem crossing_measurable (n : ℕ) (s a : ℝ) :
    MeasurableSet (crossing n s a) := by
  unfold crossing
  simp only [Set.setOf_exists, Set.setOf_and]
  exact MeasurableSet.iUnion fun k =>
    (if h : k ≤ n then by
      simpa [h] using measurableSet_lt measurable_const
        ((continuous_abs.measurable).comp
          (measurable_const.add (Shao.measurable_prefixSum k)))
    else by simp [h])

private def fourthPotential (n : ℕ) (s : ℝ) : ℝ :=
  s ^ 4 + 6 * (n : ℝ) * s ^ 2 + 3 * (n : ℝ) ^ 2 - 2 * (n : ℝ)

private theorem fourthPotential_ge (n : ℕ) (s : ℝ) :
    s ^ 4 ≤ fourthPotential n s := by
  cases n with
  | zero => simp [fourthPotential]
  | succ n =>
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hs := sq_nonneg s
    dsimp [fourthPotential]
    push_cast
    nlinarith [mul_nonneg hn hs]

private theorem fourthPotential_step (n : ℕ) (s : ℝ) :
    (fourthPotential n (s + 1) + fourthPotential n (s - 1)) / 2 =
      fourthPotential (n + 1) s := by
  simp only [fourthPotential, Nat.cast_add, Nat.cast_one]
  ring

private theorem maximal_potential (n : ℕ) (s a : ℝ) (ha : 0 < a) :
    a ^ 4 * (radMeasure n).real (crossing n s a) ≤ fourthPotential n s := by
  induction n generalizing s with
  | zero =>
    by_cases hs : a < |s|
    · have he : crossing 0 s a = Set.univ := by ext w; simp [crossing, hs]
      rw [he, probReal_univ, mul_one]
      have hsq : a ^ 2 ≤ s ^ 2 := by nlinarith [sq_abs s]
      have h4 : a ^ 4 ≤ s ^ 4 := by nlinarith [sq_nonneg (s ^ 2 - a ^ 2)]
      simpa [fourthPotential] using h4
    · have he : crossing 0 s a = ∅ := by ext w; simp [crossing, hs]
      simpa [he, fourthPotential] using (show 0 ≤ s ^ 4 by positivity)
  | succ n ih =>
    by_cases hs : a < |s|
    · have he : crossing (n + 1) s a = Set.univ := by
        ext w
        simp only [crossing, Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact ⟨0, Nat.zero_le _, by simpa using hs⟩
      rw [he, probReal_univ, mul_one]
      have hsq : a ^ 2 ≤ s ^ 2 := by nlinarith [sq_abs s]
      have h4 : a ^ 4 ≤ s ^ 4 := by nlinarith [sq_nonneg (s ^ 2 - a ^ 2)]
      exact h4.trans (fourthPotential_ge _ _)
    · have he (z : ℝ) :
          (prepend z) ⁻¹' crossing (n + 1) s a = crossing n (s + z) a := by
        ext w
        constructor
        · rintro ⟨k, hk, hka⟩
          cases k with
          | zero => simp at hka; exact (hs hka).elim
          | succ k =>
            refine ⟨k, by omega, ?_⟩
            simpa [prefix_cons, add_assoc] using hka
        · rintro ⟨k, hk, hka⟩
          exact ⟨k + 1, by omega, by simpa [prefix_cons, add_assoc] using hka⟩
      rw [radMeasure_real_succ n _ (crossing_measurable _ _ _), he, he]
      have hp := ih (s + 1)
      have hm := ih (s - 1)
      have hv := fourthPotential_step n s
      simp only [sub_eq_add_neg] at hm hv
      nlinarith

theorem rademacher_max_fourth_tail (m : ℕ) (a : ℝ) (ha : 0 < a) :
    (radMeasure m).real
      {w | ∃ k : ℕ, k ≤ m ∧ a < |Shao.prefixSum w k|} ≤
        6 * (m : ℝ)^2 / a^4 := by
  have h := maximal_potential m 0 a ha
  simp only [crossing, zero_add, fourthPotential, zero_pow (by decide : 4 ≠ 0),
    zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, zero_add] at h
  apply (le_div_iff₀ (pow_pos ha 4)).mpr
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith [sq_nonneg (m : ℝ)]

private theorem radMeasure_map_select {n m : ℕ} (f : Fin m → Fin n)
    (hf : Function.Injective f) :
    (radMeasure n).map (fun w i => w (f i)) = radMeasure m := by
  have hi : ProbabilityTheory.iIndepFun
      (fun i : Fin n => fun w : Shao.Path n => w i) (radMeasure n) :=
    ProbabilityTheory.iIndepFun_pi (fun _ => aemeasurable_id)
  apply Shao.Probability.iid_samplePath_map_eq_pi
    (fun i => measurable_pi_apply (f i)) (hi.precomp hf)
  intro i
  refine ⟨(measurable_pi_apply (f i)).aemeasurable, aemeasurable_id, ?_⟩
  simpa only [Measure.map_id, radMeasure] using
    (measurePreserving_eval (fun _ : Fin n => Shao.OQ4.RademacherCosine.law) (f i)).map_eq

private def blockIndex (d m : ℕ) (j : Fin d) (i : Fin m) : Fin (d * m) :=
  ⟨j.val * m + i.val, by
    calc
      j.val * m + i.val < j.val * m + m := Nat.add_lt_add_left i.isLt _
      _ = (j.val + 1) * m := by ring
      _ ≤ d * m := Nat.mul_le_mul_right m j.isLt⟩

private theorem blockIndex_injective (d m : ℕ) (j : Fin d) :
    Function.Injective (blockIndex d m j) := by
  intro i k h
  apply Fin.ext
  have hval := congrArg Fin.val h
  dsimp [blockIndex] at hval
  omega

private def blockPath (d m : ℕ) (j : Fin d) (w : Shao.Path (d * m)) : Shao.Path m :=
  fun i => w (blockIndex d m j i)

private theorem blockPath_measurable (d m : ℕ) (j : Fin d) :
    Measurable (blockPath d m j) :=
  measurable_pi_iff.mpr (fun i => measurable_pi_apply (blockIndex d m j i))

private theorem blockPath_law (d m : ℕ) (j : Fin d) :
    (radMeasure (d * m)).map (blockPath d m j) = radMeasure m :=
  radMeasure_map_select _ (blockIndex_injective d m j)

private theorem prefix_step {n : ℕ} (w : Shao.Path n) (k : ℕ) (hk : k < n) :
    Shao.prefixSum w (k + 1) = Shao.prefixSum w k + w ⟨k, hk⟩ := by
  classical
  have hset : Finset.univ.filter (fun i : Fin n => i.val < k + 1) =
      insert ⟨k, hk⟩ (Finset.univ.filter (fun i : Fin n => i.val < k)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hi
      by_cases h : i.val = k
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (by omega)
    · rintro (h | h)
      · subst i; simp
      · omega
  have hnot : (⟨k, hk⟩ : Fin n) ∉ Finset.univ.filter (fun i : Fin n => i.val < k) := by
    simp
  simp only [Shao.prefixSum, hset, Finset.sum_insert hnot]
  ring

private theorem prefix_block (d m : ℕ) (j : Fin d) (w : Shao.Path (d * m))
    (k : ℕ) (hk : k ≤ m) :
    Shao.prefixSum w (j.val * m + k) = Shao.prefixSum w (j.val * m) +
      Shao.prefixSum (blockPath d m j w) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkm : k < m := by omega
    have hkn : j.val * m + k < d * m := (blockIndex d m j ⟨k, hkm⟩).isLt
    rw [show j.val * m + (k + 1) = (j.val * m + k) + 1 by omega,
      prefix_step w _ hkn, prefix_step (blockPath d m j w) k hkm, ih (by omega)]
    simp only [blockPath, blockIndex]
    ring

private def badBlocks (d m : ℕ) (a : ℝ) : Set (Shao.Path (d * m)) :=
  ⋃ j : Fin d, (blockPath d m j) ⁻¹' crossing m 0 a

private theorem badBlocks_bound (d m : ℕ) (a : ℝ) (ha : 0 < a) :
    (radMeasure (d * m)).real (badBlocks d m a) ≤
      (d : ℝ) * (6 * (m : ℝ)^2 / a^4) := by
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    (∑ j : Fin d, (radMeasure (d * m)).real
        ((blockPath d m j) ⁻¹' crossing m 0 a)) ≤
        ∑ _j : Fin d, 6 * (m : ℝ)^2 / a^4 := by
      apply Finset.sum_le_sum
      intro j _
      rw [← map_measureReal_apply (blockPath_measurable d m j) (crossing_measurable m 0 a),
        blockPath_law]
      simpa only [crossing, zero_add] using rademacher_max_fourth_tail m a ha
    _ = _ := by simp

private theorem coarse_subset (d m : ℕ) (x : ℝ) :
    Shao.closedStrip (x * Real.sqrt (d * m : ℝ)) ⊆ coarseStrip d m x := by
  intro w hw j hj
  exact hw (j * m) (Nat.mul_le_mul_right m hj)

private theorem coarse_subset_full_union (d m : ℕ) (hm : 0 < m)
    (x ε : ℝ) (hε : 0 ≤ ε) :
    coarseStrip d m x ⊆
      Shao.closedStrip ((x + ε) * Real.sqrt (d * m : ℝ)) ∪
        badBlocks d m (ε * Real.sqrt (d * m : ℝ)) := by
  classical
  intro w hw
  by_cases hb : w ∈ badBlocks d m (ε * Real.sqrt (d * m : ℝ))
  · exact Or.inr hb
  apply Or.inl
  intro k hk
  by_cases he : k = d * m
  · subst k
    have h := hw d le_rfl
    have hb0 := mul_nonneg hε (Real.sqrt_nonneg (d * m : ℝ))
    nlinarith
  · have hlt : k < d * m := lt_of_le_of_ne hk he
    have hj : k / m < d := (Nat.div_lt_iff_lt_mul hm).mpr hlt
    let j : Fin d := ⟨k / m, hj⟩
    have hr : k % m ≤ m := (Nat.mod_lt k hm).le
    have hincr : |Shao.prefixSum (blockPath d m j w) (k % m)| ≤
        ε * Real.sqrt (d * m : ℝ) := by
      apply le_of_not_gt
      intro hcross
      apply hb
      exact Set.mem_iUnion.mpr ⟨j, ⟨k % m, hr, by simpa [crossing] using hcross⟩⟩
    have hcoarse := hw j.val j.isLt.le
    have hdecomp := prefix_block d m j w (k % m) hr
    have hsplit : j.val * m + k % m = k := by
      dsimp [j]
      simpa [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div k m
    rw [hsplit] at hdecomp
    rw [hdecomp]
    exact (abs_add_le _ _).trans (by nlinarith)

theorem rademacher_coarse_comparison
    (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (x ε : ℝ) (hx : 0 ≤ x) (hε : 0 < ε) :
    radSurvival (d*m) x ≤ coarseProbability d m x ∧
    coarseProbability d m x ≤
      radSurvival (d*m) (x+ε) + 6 / ((d : ℝ)*ε^4) := by
  simp only [radSurvival, coarseProbability, Nat.cast_mul]
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hdm : 0 < (d * m : ℝ) := mul_pos hdR hmR
  have hs : 0 < Real.sqrt (d * m : ℝ) := Real.sqrt_pos.mpr hdm
  have ha : 0 < ε * Real.sqrt (d * m : ℝ) := mul_pos hε hs
  constructor
  · exact measureReal_mono (coarse_subset d m x)
  · apply (measureReal_mono (coarse_subset_full_union d m hm x ε hε.le)).trans
    apply (measureReal_union_le _ _).trans
    have hb := badBlocks_bound d m (ε * Real.sqrt (d * m : ℝ)) ha
    have hcalc : (d : ℝ) * (6 * (m : ℝ)^2 / (ε * Real.sqrt (d * m : ℝ))^4) =
        6 / ((d : ℝ) * ε^4) := by
      have hs4 : Real.sqrt (d * m : ℝ) ^ 4 = (d : ℝ)^2 * (m : ℝ)^2 := by
        calc
          Real.sqrt (d * m : ℝ)^4 = (Real.sqrt (d * m : ℝ)^2)^2 := by ring
          _ = ((d : ℝ) * (m : ℝ))^2 := by rw [Real.sq_sqrt hdm.le]
          _ = _ := by ring
      rw [mul_pow, hs4]
      field_simp [ne_of_gt hdR, ne_of_gt hmR, ne_of_gt hε]
      <;> ring
    rw [hcalc] at hb
    exact add_le_add (le_refl _) hb

end Shao.Probability.BrownianSup

