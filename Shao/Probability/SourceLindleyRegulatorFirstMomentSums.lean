import Shao.Probability.SourceLindleyRegulatorFirstMoment

/-!
# Prefix and summed first moments of the actual Lindley regulators

The longer iid path is projected to its original, chronologically ordered
prefix. Its true reflected recursion and prefix sum agree with those of that
prefix, whose product law is obtained from the independent coordinates.
The finite sum estimate uses a deterministic square-root telescoping bound.

Source: supplement LF2137–2174 and LF2217–2236. These results pay only the
unweighted first moments; no uniform source-law constant or second-moment,
survival, energy-tilt, or original root conclusion is asserted.
-/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem state_prefix_agrees {N : ℕ} (a : Shao.Path N)
    (m : ℕ) (hm : m ≤ N) (k : ℕ) (hk : k ≤ m) :
    Shao.lindleyState (Shao.prefixPath a m hm) k hk =
      Shao.lindleyState a k (hk.trans hm) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Shao.lindleyState_succ, Shao.lindleyState_succ, ih (by omega)]
    rfl

private theorem sum_prefix_agrees {N : ℕ} (a : Shao.Path N)
    (m : ℕ) (hm : m ≤ N) :
    Shao.prefixSum (Shao.prefixPath a m hm) m = Shao.prefixSum a m := by
  classical
  rw [Shao.prefixSum_length]
  unfold Shao.prefixSum
  refine Finset.sum_bij (fun j _ => (⟨j.val, lt_of_lt_of_le j.is_lt hm⟩ : Fin N))
    ?_ ?_ ?_ ?_
  · intro j _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact j.is_lt
  · intro j _ k _ h
    exact Fin.ext (congrArg (@Fin.val N) h)
  · intro j hj
    have hjm : j.val < m := (Finset.mem_filter.mp hj).2
    exact ⟨⟨j.val, hjm⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro j _
    rfl

private theorem measurable_state_prefix {m : ℕ} (k : ℕ) (hk : k ≤ m) :
    Measurable (fun a : Shao.Path m => Shao.lindleyState a k hk) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact measurable_const.max ((ih (by omega)).add (measurable_pi_apply _))

private theorem measurable_regulator_prefix {m : ℕ} (i : Fin m) :
    Measurable (fun a : Shao.Path m => lindleyRegulator a i) :=
  ((measurable_state_prefix i.val (Nat.le_of_lt i.is_lt)).add
    (measurable_pi_apply i)).neg.max measurable_const

private theorem prefix_measurePreserving
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (N m : ℕ) (hm : m ≤ N) :
    MeasurePreserving (fun a : Shao.Path N => Shao.prefixPath a m hm)
      (Measure.pi (fun _ : Fin N => ν)) (Measure.pi (fun _ : Fin m => ν)) := by
  let f : Fin m → Fin N := fun j => ⟨j.val, lt_of_lt_of_le j.is_lt hm⟩
  let X : Fin N → Shao.Path N → ℝ := fun j a => a j
  have hf : Function.Injective f := fun j k h => Fin.ext (congrArg (@Fin.val N) h)
  have hX : ∀ j, Measurable (X j) := fun j => measurable_pi_apply j
  have hIndep : iIndepFun X (Measure.pi (fun _ : Fin N => ν)) :=
    iIndepFun_pi (fun _ : Fin N => measurable_id.aemeasurable)
  have hLaw (j : Fin N) : IdentDistrib (X j) (id : ℝ → ℝ)
      (Measure.pi (fun _ : Fin N => ν)) ν := by
    refine ⟨(hX j).aemeasurable, measurable_id.aemeasurable, ?_⟩
    exact (measurePreserving_eval (fun _ : Fin N => ν) j).map_eq.trans
      Measure.map_id.symm
  refine ⟨Measurable.of_eval (fun j => measurable_pi_apply (f j)), ?_⟩
  exact iid_samplePath_map_eq_pi (fun j => hX (f j))
    (hIndep.precomp hf) (fun j => hLaw (f j))

/-- Every actual increment of the longer iid sample has its prefix first moment. -/
theorem iid_lindleyRegulator_prefix_first_moment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (N : ℕ) (i : Fin N) :
    let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ν)
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let V : ℝ := variance (id : ℝ → ℝ) ν
    Integrable (fun a : Shao.Path N => lindleyRegulator a i) P ∧
      ((i.val + 1 : ℕ) : ℝ) *
        (∫ a : Shao.Path N, lindleyRegulator a i ∂P) =
          ∫ a : Shao.Path N, max (-(Shao.prefixSum a (i.val + 1))) 0 ∂P ∧
      (∫ a : Shao.Path N, lindleyRegulator a i ∂P) ≤
        Real.sqrt V / Real.sqrt ((i.val + 1 : ℕ) : ℝ) + |μ| := by
  dsimp only
  let p : Shao.Path N → Shao.Path (i.val + 1) :=
    fun a => Shao.prefixPath a (i.val + 1) (by omega)
  let Q : Measure (Shao.Path (i.val + 1)) :=
    Measure.pi (fun _ : Fin (i.val + 1) => ν)
  let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ν)
  let U : Shao.Path (i.val + 1) → ℝ :=
    fun a => lindleyRegulator a (Fin.last i.val)
  let B : Shao.Path (i.val + 1) → ℝ :=
    fun a => max (-(Shao.prefixSum a (i.val + 1))) 0
  have hp : MeasurePreserving p P Q :=
    prefix_measurePreserving ν N (i.val + 1) (by omega)
  have hU : Measurable U := measurable_regulator_prefix (Fin.last i.val)
  have hB : Measurable B :=
    ((Shao.measurable_prefixSum (i.val + 1)).neg).max measurable_const
  have hUa (a : Shao.Path N) : U (p a) = lindleyRegulator a i := by
    dsimp only [U, lindleyRegulator, p]
    rw [state_prefix_agrees]
    rfl
  have hBa (a : Shao.Path N) : B (p a) =
      max (-(Shao.prefixSum a (i.val + 1))) 0 := by
    dsimp only [B, p]
    rw [sum_prefix_agrees]
  have h := iid_lindleyRegulator_last_first_moment ν h2 i.val
  dsimp only at h
  have hI : Integrable (fun a : Shao.Path N => lindleyRegulator a i) P := by
    have hIc : Integrable (fun a : Shao.Path N => U (p a)) P :=
      hp.integrable_comp_of_integrable h.1
    simpa only [hUa] using hIc
  have hd : IdentDistrib p (id : Shao.Path (i.val + 1) → Shao.Path (i.val + 1)) P Q := by
    exact ⟨hp.measurable.aemeasurable, measurable_id.aemeasurable,
      hp.map_eq.trans Measure.map_id.symm⟩
  have hUE : (∫ a : Shao.Path N, lindleyRegulator a i ∂P) = ∫ a, U a ∂Q := by
    have he : (∫ a : Shao.Path N, U (p a) ∂P) = ∫ a, U a ∂Q :=
      (hd.comp hU).integral_eq
    simpa only [hUa] using he
  have hBE : (∫ a : Shao.Path N, max (-(Shao.prefixSum a (i.val + 1))) 0 ∂P) =
      ∫ a, B a ∂Q := by
    have he : (∫ a : Shao.Path N, B (p a) ∂P) = ∫ a, B a ∂Q :=
      (hd.comp hB).integral_eq
    simpa only [hBa] using he
  refine ⟨hI, ?_, ?_⟩
  · rw [hUE, hBE]
    exact h.2.1
  · rw [hUE]
    exact h.2.2

private theorem reciprocal_sqrt_step (n : ℕ) :
    1 / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤
      2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hb : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hnp
  apply (div_le_iff₀ hb).mpr
  have ha2 := Real.sq_sqrt hn
  have hb2 := Real.sq_sqrt hnp.le
  have hd := sq_nonneg (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))
  norm_num only [Nat.cast_add, Nat.cast_one] at *
  nlinarith

private theorem reciprocal_sqrt_sum (N : ℕ) :
    (∑ i : Fin N, 1 / Real.sqrt ((i.val + 1 : ℕ) : ℝ)) ≤
      2 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    calc
      _ ≤ 2 * Real.sqrt (N : ℝ) +
          2 * (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) :=
        add_le_add ih (reciprocal_sqrt_step N)
      _ = _ := by ring

/-- The actual finite sum is integrable and obeys the general first-moment bound. -/
theorem iid_lindleyRegulator_sum_first_moment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (N : ℕ) :
    let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ν)
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let V : ℝ := variance (id : ℝ → ℝ) ν
    Integrable (fun a : Shao.Path N => ∑ i : Fin N, lindleyRegulator a i) P ∧
      (∫ a : Shao.Path N, ∑ i : Fin N, lindleyRegulator a i ∂P) ≤
        2 * Real.sqrt V * Real.sqrt (N : ℝ) + (N : ℝ) * |μ| := by
  classical
  dsimp only
  let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ν)
  let μ : ℝ := ∫ a : ℝ, a ∂ν
  let V : ℝ := variance (id : ℝ → ℝ) ν
  have h (i : Fin N) := iid_lindleyRegulator_prefix_first_moment ν h2 N i
  dsimp only at h
  have hI := integrable_finsetSum Finset.univ (fun i _ => (h i).1)
  refine ⟨hI, ?_⟩
  rw [integral_finsetSum Finset.univ (fun i _ => (h i).1)]
  calc
    _ ≤ ∑ i : Fin N, (Real.sqrt V / Real.sqrt ((i.val + 1 : ℕ) : ℝ) + |μ|) :=
      Finset.sum_le_sum (fun i _ => (h i).2.2)
    _ = Real.sqrt V * (∑ i : Fin N, 1 / Real.sqrt ((i.val + 1 : ℕ) : ℝ)) +
        (N : ℝ) * |μ| := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, mul_one_div,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ Real.sqrt V * (2 * Real.sqrt (N : ℝ)) + (N : ℝ) * |μ| :=
      add_le_add (mul_le_mul_of_nonneg_left (reciprocal_sqrt_sum N)
        (Real.sqrt_nonneg V)) le_rfl
    _ = _ := by ring

end Shao.Probability
