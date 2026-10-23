import Shao.Probability.LindleyTelescoping
import Shao.Probability.FiniteIIDMoments
import Mathlib.Algebra.Group.Fin.Basic

/-!
# The actual last Lindley regulator: cyclic sum and first moment

The deterministic argument removes the first increment from a full cycle.
For nonpositive total increment the full reflected state equals the reflected
state of this tail. Rotating and summing the genuine state recursion then
telescopes. This is the rolling-minimum argument without selecting a minimizer.

Source: supplement, proof of the regulator lemma, LF2137–2184. Only its
first-moment prerequisite is treated here.
-/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem prefix_step {m : ℕ} (a : Shao.Path m) (i : Fin m) :
    Shao.prefixSum a (i.val + 1) = Shao.prefixSum a i.val + a i := by
  have hf : Finset.univ.filter (fun j : Fin m => j.val < i.val + 1) =
      insert i (Finset.univ.filter (fun j : Fin m => j.val < i.val)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp h) with hlt | heq
      · exact Or.inr hlt
      · exact Or.inl (Fin.ext heq)
    · rintro (h | h)
      · subst j; exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt h
  unfold Shao.prefixSum
  rw [hf, Finset.sum_insert]
  · exact add_comm _ _
  · simp

private theorem state_nonneg {m : ℕ} (a : Shao.Path m) (k : ℕ) (hk : k ≤ m) :
    0 ≤ Shao.lindleyState a k hk := by
  cases k with
  | zero => rfl
  | succ k => exact le_max_left _ _

private theorem state_ge_sum {m : ℕ} (a : Shao.Path m) (k : ℕ) (hk : k ≤ m) :
    Shao.prefixSum a k ≤ Shao.lindleyState a k hk := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prefix_step a ⟨k, by omega⟩, Shao.lindleyState_succ]
    change Shao.prefixSum a k + a ⟨k, by omega⟩ ≤ _
    have h := ih (by omega)
    exact (by linarith : Shao.prefixSum a k + a ⟨k, by omega⟩ ≤
      Shao.lindleyState a k (by omega) + a ⟨k, by omega⟩).trans (le_max_right _ _)

private theorem state_cons {m : ℕ} (x : ℝ) (a : Shao.Path m)
    (k : ℕ) (hk : k ≤ m) :
    Shao.lindleyState (Fin.cons x a) (k + 1) (by omega) =
      max (x + Shao.prefixSum a k) (Shao.lindleyState a k hk) := by
  induction k with
  | zero => simp [Shao.lindleyState, max_comm]
  | succ k ih =>
    rw [Shao.lindleyState_succ, ih (by omega), Shao.lindleyState_succ,
      prefix_step a ⟨k, by omega⟩]
    change max 0 (max (x + Shao.prefixSum a k)
      (Shao.lindleyState a k _) + a ⟨k, by omega⟩) =
      max (x + (Shao.prefixSum a k + a ⟨k, by omega⟩))
        (max 0 (Shao.lindleyState a k _ + a ⟨k, by omega⟩))
    rw [← max_add_add_right, ← add_assoc, max_left_comm]

private theorem state_remove_first {n : ℕ} (a : Shao.Path (n + 1))
    (ht : Shao.prefixSum a (n + 1) ≤ 0) :
    Shao.lindleyState a (n + 1) le_rfl =
      Shao.lindleyState (fun k : Fin n => a k.succ) n le_rfl := by
  have ha : a = Fin.cons (a 0) (fun k : Fin n => a k.succ) := by
    exact (Fin.cons_self_tail a).symm
  have hs : Shao.prefixSum a (n + 1) =
      a 0 + Shao.prefixSum (fun k : Fin n => a k.succ) n := by
    simp only [Shao.prefixSum_length, Fin.sum_univ_succ]
  conv_lhs => rw [ha]
  rw [state_cons]
  rw [hs] at ht
  exact max_eq_right (ht.trans (state_nonneg _ _ _))

private theorem state_prefix {m : ℕ} (a : Shao.Path m) (k : ℕ) (hk : k ≤ m) :
    Shao.lindleyState a k hk =
      Shao.lindleyState (Shao.prefixPath a k hk) k le_rfl := by
  rw [Shao.lindleyState_eq_maxWithZero_reverse_prefix, Shao.lindleyState_length]

private theorem rotate_total {n : ℕ} (a : Shao.Path (n + 1)) (j : Fin (n + 1)) :
    Shao.prefixSum (fun k => a (k + j)) (n + 1) = Shao.prefixSum a (n + 1) := by
  simp only [Shao.prefixSum_length]
  exact Equiv.sum_comp (Equiv.addRight j) a

private theorem rotate_tail {n : ℕ} (a : Shao.Path (n + 1)) (j : Fin (n + 1)) :
    Shao.prefixPath (fun k : Fin (n + 1) => a (k + (j + 1))) n (by omega) =
      (fun k : Fin n => a (k.succ + j)) := by
  funext k
  apply congrArg a
  change k.castSucc + (j + 1) = k.succ + j
  have hk : k.succ = k.castSucc + 1 := by
    cases n with
    | zero => exact k.elim0
    | succ n =>
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_add, Fin.val_castSucc, Fin.val_one]
      rw [Nat.mod_eq_of_lt (by omega)]
  rw [hk]
  ac_rfl

private theorem regulator_balance {n : ℕ} (a : Shao.Path (n + 1)) :
    lindleyRegulator a (Fin.last n) =
      Shao.lindleyState a (n + 1) le_rfl -
        Shao.lindleyState a n (by omega) - a (Fin.last n) := by
  rw [Shao.lindleyState_succ]
  change max (-(Shao.lindleyState a n _ + a (Fin.last n))) 0 =
    max 0 (Shao.lindleyState a n _ + a (Fin.last n)) -
      Shao.lindleyState a n _ - a (Fin.last n)
  by_cases h : 0 ≤ Shao.lindleyState a n (by omega) + a (Fin.last n)
  · rw [max_eq_right (neg_nonpos.mpr h), max_eq_right h]; ring
  · rw [max_eq_left (neg_nonneg.mpr (le_of_not_ge h)),
      max_eq_left (le_of_not_ge h)]; ring

/-- The sum of the actual last regulators of the actual cyclic rotations. -/
theorem lindleyRegulator_cyclic_sum (n : ℕ) (a : Shao.Path (n + 1)) :
    (∑ j : Fin (n + 1),
      lindleyRegulator (fun k : Fin (n + 1) => a (k + j)) (Fin.last n)) =
      max (-(Shao.prefixSum a (n + 1))) 0 := by
  classical
  by_cases ht : 0 ≤ Shao.prefixSum a (n + 1)
  · rw [max_eq_right (neg_nonpos.mpr ht)]
    apply Finset.sum_eq_zero
    intro j _
    unfold lindleyRegulator
    change max (-(Shao.lindleyState (fun k : Fin (n + 1) => a (k + j)) n _ +
      a (Fin.last n + j))) 0 = 0
    apply max_eq_right
    apply neg_nonpos.mpr
    have h := state_ge_sum (fun k : Fin (n + 1) => a (k + j)) n (by omega)
    have hp := prefix_step (fun k : Fin (n + 1) => a (k + j)) (Fin.last n)
    simp only [Fin.val_last] at hp
    rw [rotate_total] at hp
    linarith
  · have ht' : Shao.prefixSum a (n + 1) ≤ 0 := le_of_not_ge ht
    let W : Fin (n + 1) → ℝ := fun j =>
      Shao.lindleyState (fun k : Fin (n + 1) => a (k + j)) (n + 1) le_rfl
    have hstep (j : Fin (n + 1)) :
        lindleyRegulator (fun k : Fin (n + 1) => a (k + (j + 1))) (Fin.last n) =
          W (j + 1) - W j - a j := by
      rw [regulator_balance]
      have hW : W j = Shao.lindleyState
          (fun k : Fin (n + 1) => a (k + (j + 1))) n (by omega) := by
        dsimp [W]
        rw [state_remove_first _ (by rwa [rotate_total]),
          state_prefix (fun k : Fin (n + 1) => a (k + (j + 1))) n (by omega),
          rotate_tail]
      rw [← hW]
      have hj : Fin.last n + (j + 1) = j := by
        calc
          _ = (Fin.last n + 1) + j := by ac_rfl
          _ = j := by rw [Fin.last_add_one, zero_add]
      rw [hj]
    have hr := Equiv.sum_comp (Equiv.addRight (1 : Fin (n + 1)))
      (fun j : Fin (n + 1) =>
        lindleyRegulator (fun k : Fin (n + 1) => a (k + j)) (Fin.last n))
    rw [← hr]
    change (∑ j : Fin (n + 1),
      lindleyRegulator (fun k : Fin (n + 1) => a (k + (j + 1))) (Fin.last n)) = _
    simp_rw [hstep]
    have hWsum := Equiv.sum_comp (Equiv.addRight (1 : Fin (n + 1))) W
    change (∑ j : Fin (n + 1), W (j + 1)) = ∑ j : Fin (n + 1), W j at hWsum
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      hWsum,
      sub_self, zero_sub, max_eq_left (neg_nonneg.mpr ht'), Shao.prefixSum_length]

private theorem measurable_state_actual {m : ℕ} (k : ℕ) (hk : k ≤ m) :
    Measurable (fun a : Shao.Path m => Shao.lindleyState a k hk) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact measurable_const.max ((ih (by omega)).add (measurable_pi_apply _))

private theorem measurable_regulator_actual {m : ℕ} (i : Fin m) :
    Measurable (fun a : Shao.Path m => lindleyRegulator a i) :=
  ((measurable_state_actual i.val (Nat.le_of_lt i.is_lt)).add
    (measurable_pi_apply i)).neg.max measurable_const

private theorem regulator_bounds {m : ℕ} (a : Shao.Path m) (i : Fin m) :
    0 ≤ lindleyRegulator a i ∧ lindleyRegulator a i ≤ |a i| := by
  constructor
  · exact le_max_right _ _
  · apply max_le _ (abs_nonneg _)
    have hW := state_nonneg a i.val (Nat.le_of_lt i.is_lt)
    have ha := neg_le_abs (a i)
    linarith

/-- The exact first moment and sharp source bound under the actual iid law. -/
theorem iid_lindleyRegulator_last_first_moment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (n : ℕ) :
    let P : Measure (Shao.Path (n + 1)) := Measure.pi (fun _ : Fin (n + 1) => ν)
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let V : ℝ := variance (id : ℝ → ℝ) ν
    Integrable (fun a : Shao.Path (n + 1) => lindleyRegulator a (Fin.last n)) P ∧
      ((n + 1 : ℕ) : ℝ) *
        (∫ a : Shao.Path (n + 1), lindleyRegulator a (Fin.last n) ∂P) =
          ∫ a : Shao.Path (n + 1), max (-(Shao.prefixSum a (n + 1))) 0 ∂P ∧
      (∫ a : Shao.Path (n + 1), lindleyRegulator a (Fin.last n) ∂P) ≤
        Real.sqrt V / Real.sqrt ((n + 1 : ℕ) : ℝ) + |μ| := by
  classical
  dsimp only
  let P : Measure (Shao.Path (n + 1)) := Measure.pi (fun _ : Fin (n + 1) => ν)
  let μ : ℝ := ∫ a : ℝ, a ∂ν
  let V : ℝ := variance (id : ℝ → ℝ) ν
  let X : Fin (n + 1) → Shao.Path (n + 1) → ℝ := fun i a => a i
  let S : Shao.Path (n + 1) → ℝ := fun a => Shao.prefixSum a (n + 1)
  let U : Shao.Path (n + 1) → ℝ := fun a => lindleyRegulator a (Fin.last n)
  have hν2 : MemLp (id : ℝ → ℝ) 2 ν :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr h2
  have hX (i : Fin (n + 1)) : Measurable (X i) := measurable_pi_apply i
  have hX2 (i : Fin (n + 1)) : MemLp (X i) 2 P :=
    hν2.comp_measurePreserving (measurePreserving_eval (fun _ : Fin (n + 1) => ν) i)
  have hLaw (i : Fin (n + 1)) : IdentDistrib (X i) (id : ℝ → ℝ) P ν := by
    refine ⟨(hX i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    exact (measurePreserving_eval (fun _ : Fin (n + 1) => ν) i).map_eq.trans
      Measure.map_id.symm
  have hIndep : iIndepFun X P :=
    iIndepFun_pi (fun _ : Fin (n + 1) => measurable_id.aemeasurable)
  have hUm : Measurable U := measurable_regulator_actual (Fin.last n)
  have hUI : Integrable U P := by
    apply ((hX2 (Fin.last n)).integrable (by norm_num)).abs.mono'
      hUm.aestronglyMeasurable
    exact ae_of_all P (fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (regulator_bounds a (Fin.last n)).1]
      exact (regulator_bounds a (Fin.last n)).2)
  have hperm (j : Fin (n + 1)) : IdentDistrib U
      (fun a : Shao.Path (n + 1) => U (fun k => a (k + j))) P P := by
    exact iid_observable_identDistrib_perm hX hIndep hLaw (Equiv.addRight j) hUm
  have hrotI (j : Fin (n + 1)) :
      Integrable (fun a : Shao.Path (n + 1) => U (fun k => a (k + j))) P :=
    (hperm j).integrable_snd hUI
  have hrotE (j : Fin (n + 1)) :
      (∫ a : Shao.Path (n + 1), U (fun k => a (k + j)) ∂P) = ∫ a, U a ∂P :=
    (hperm j).integral_eq.symm
  have hidentity : ((n + 1 : ℕ) : ℝ) * (∫ a, U a ∂P) =
      ∫ a, max (-(S a)) 0 ∂P := by
    calc
      _ = ∑ j : Fin (n + 1), ∫ a : Shao.Path (n + 1), U (fun k => a (k + j)) ∂P := by
        simp only [hrotE, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
      _ = ∫ a : Shao.Path (n + 1), ∑ j : Fin (n + 1), U (fun k => a (k + j)) ∂P :=
        (integral_finsetSum Finset.univ (fun j _ => hrotI j)).symm
      _ = _ := integral_congr_ae (ae_of_all P (fun a => lindleyRegulator_cyclic_sum n a))
  have hSm : Measurable S := Shao.measurable_prefixSum (n + 1)
  have hS2 : MemLp S 2 P := by
    simpa only [S, Shao.prefixSum_length] using
      memLp_finsetSum Finset.univ (fun i _ => hX2 i)
  have hSE : (∫ a, S a ∂P) = ((n + 1 : ℕ) : ℝ) * μ := by
    change (∫ a, Shao.prefixSum a (n + 1) ∂P) = _
    simp only [Shao.prefixSum_length]
    rw [integral_finsetSum Finset.univ (fun i _ => (hX2 i).integrable (by norm_num))]
    have he (i : Fin (n + 1)) : (∫ a : Shao.Path (n + 1), a i ∂P) = μ :=
      (hLaw i).integral_eq
    simp only [X, he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hSV : variance S P = ((n + 1 : ℕ) : ℝ) * V := by
    have hv := variance_sum_pi (fun _ : Fin (n + 1) => hν2)
    have hf : (∑ i : Fin (n + 1), fun a : Shao.Path (n + 1) => id (a i)) = S := by
      funext a
      simp only [S, Shao.prefixSum_length, Finset.sum_apply, id_eq]
    rw [hf] at hv
    simpa only [P, V,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hv
  have hcenter : (∫ a, (S a - ((n + 1 : ℕ) : ℝ) * μ) ^ 2 ∂P) =
      ((n + 1 : ℕ) : ℝ) * V := by
    rw [variance_eq_integral hSm.aemeasurable, hSE] at hSV
    exact hSV
  have hC2 : MemLp (fun a => S a - ((n + 1 : ℕ) : ℝ) * μ) 2 P :=
    hS2.sub (memLp_const _)
  have hA2 : MemLp (fun a => |S a - ((n + 1 : ℕ) : ℝ) * μ|) 2 P := by
    simpa only [Real.norm_eq_abs] using hC2.norm
  have hA : Integrable (fun a => |S a - ((n + 1 : ℕ) : ℝ) * μ|) P :=
    hA2.integrable (by norm_num)
  have hm : 0 < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hV : 0 ≤ V := variance_nonneg _ _
  have hCS : (∫ a, |S a - ((n + 1 : ℕ) : ℝ) * μ| ∂P) ≤
      Real.sqrt (((n + 1 : ℕ) : ℝ) * V) := by
    have hv := variance_nonneg (fun a => |S a - ((n + 1 : ℕ) : ℝ) * μ|) P
    rw [variance_eq_sub hA2] at hv
    simp only [Pi.pow_apply, sq_abs] at hv
    rw [hcenter] at hv
    have hs := Real.sq_sqrt (mul_nonneg hm.le hV)
    have hn := Real.sqrt_nonneg (((n + 1 : ℕ) : ℝ) * V)
    nlinarith
  have hnegI : Integrable (fun a => max (-(S a)) 0) P := by
    apply (hS2.integrable (by norm_num)).abs.mono'
      (hSm.neg.max measurable_const).aestronglyMeasurable
    exact ae_of_all P (fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (neg_le_abs (S a)) (abs_nonneg (S a)))
  have hnegative : (∫ a, max (-(S a)) 0 ∂P) ≤
      Real.sqrt (((n + 1 : ℕ) : ℝ) * V) + ((n + 1 : ℕ) : ℝ) * |μ| := by
    calc
      _ ≤ ∫ a, |S a - ((n + 1 : ℕ) : ℝ) * μ| + ((n + 1 : ℕ) : ℝ) * |μ| ∂P := by
        apply integral_mono hnegI (hA.add (integrable_const _))
        intro a
        change max (-S a) 0 ≤ |S a - ((n + 1 : ℕ) : ℝ) * μ| +
          ((n + 1 : ℕ) : ℝ) * |μ|
        apply max_le
        · have h₁ := neg_le_abs (S a - ((n + 1 : ℕ) : ℝ) * μ)
          have h₂ := mul_le_mul_of_nonneg_left (neg_le_abs μ) hm.le
          linarith
        · positivity
      _ = (∫ a, |S a - ((n + 1 : ℕ) : ℝ) * μ| ∂P) +
          ((n + 1 : ℕ) : ℝ) * |μ| := by
        rw [integral_add hA (integrable_const _), integral_const,
          probReal_univ, one_smul]
      _ ≤ _ := by linarith
  have hspos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hm
  have hscale : ((n + 1 : ℕ) : ℝ) *
      (Real.sqrt V / Real.sqrt ((n + 1 : ℕ) : ℝ) + |μ|) =
        Real.sqrt (((n + 1 : ℕ) : ℝ) * V) + ((n + 1 : ℕ) : ℝ) * |μ| := by
    rw [mul_add, Real.sqrt_mul hm.le]
    congr 1
    have hs := Real.sq_sqrt hm.le
    rw [← mul_div_assoc]
    apply (div_eq_iff hspos.ne').mpr
    calc
      _ = (Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2 * Real.sqrt V := by rw [hs]
      _ = _ := by ring
  refine ⟨hUI, hidentity, ?_⟩
  rw [← hidentity, ← hscale] at hnegative
  nlinarith

end Shao.Probability
