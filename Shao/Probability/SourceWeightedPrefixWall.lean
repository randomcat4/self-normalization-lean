import Shao.Probability.SourceCircularWitnessMoment
import Shao.Probability.FiniteIIDMoments
import Shao.Probability.SourceTrueEnergyStrip
import Shao.Probability.SourceMarkedSuffixAveraging
import Shao.Probability.SourceTrueWallProfile
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Lean

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
noncomputable section
namespace Shao.Probability.SourceWeightedPrefixWall
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical Topology ENNReal

private theorem pww_circular_witness_concatenation (k l : ℕ) :
    let L : (N : ℕ) → Shao.Path N → ℝ := fun N a =>
      if hN : 0 < N then
        sSup {w : ℝ | ∃ i : Fin N, ∃ q : Fin (N + 1),
          w = Shao.prefixSum a N -
            2 * ∑ z ∈ Finset.range q.val,
              a ⟨(i.val + z) % N, Nat.mod_lt _ hN⟩}
      else 0
    let joined : Shao.Path k → Shao.Path l → Shao.Path (k + l) := fun a b i =>
      if hi : i.val < k then a ⟨i.val, hi⟩
      else b ⟨i.val - k, by omega⟩
    ∀ (a : Shao.Path k) (b : Shao.Path l),
      L (k + l) (joined a b) ≤ L k a + L l b := by
  classical
  let L : (N : ℕ) → Shao.Path N → ℝ := fun N a =>
    if hN : 0 < N then
      sSup {w : ℝ | ∃ i : Fin N, ∃ q : Fin (N + 1),
        w = Shao.prefixSum a N - 2 * ∑ z ∈ Finset.range q.val,
          a ⟨(i.val + z) % N, Nat.mod_lt _ hN⟩}
    else 0
  let joined : Shao.Path k → Shao.Path l → Shao.Path (k + l) := fun a b i =>
    if hi : i.val < k then a ⟨i.val, hi⟩ else b ⟨i.val - k, by omega⟩
  change ∀ a b, L (k + l) (joined a b) ≤ L k a + L l b
  let A : (N : ℕ) → Shao.Path N → ℝ := fun N a =>
    sSup {w : ℝ | ∃ u v : Fin (N + 1), u.val ≤ v.val ∧
      w = Shao.prefixSum a v.val - Shao.prefixSum a u.val}
  let R : (N : ℕ) → Shao.Path N → ℝ := fun N a =>
    sSup {w : ℝ | ∃ u v : Fin (N + 1), u.val ≤ v.val ∧
      w = Shao.prefixSum a u.val - Shao.prefixSum a v.val}
  run_tac
    let n := Lean.mkPrivateNameCore ("Shao.Probability.SourceCircularWitnessMoment".toName)
      ("Shao.Probability.SourceCircularWitnessMoment.cwm_path_extrema_geometry".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hGeom".toName)) := $(Lean.mkIdent n)))
  have hG (N : ℕ) (a : Shao.Path N) :
      L N a = max (Shao.prefixSum a N + 2 * R N a)
        (2 * A N a - Shao.prefixSum a N) :=
    (hGeom N).2.2.2 a |>.2.2.2.2.2.2.1
  have hC (N : ℕ) (a : Shao.Path N) (u v : Fin (N + 1)) (huv : u.val ≤ v.val) :
      Shao.prefixSum a N + 2 * (Shao.prefixSum a u.val - Shao.prefixSum a v.val) ≤ L N a ∧
      2 * (Shao.prefixSum a v.val - Shao.prefixSum a u.val) - Shao.prefixSum a N ≤ L N a := by
    have hR : Shao.prefixSum a u.val - Shao.prefixSum a v.val ≤ R N a := by
      apply le_csSup
      · exact (Set.finite_range (fun p : Fin (N + 1) × Fin (N + 1) =>
          Shao.prefixSum a p.1.val - Shao.prefixSum a p.2.val)).bddAbove.mono
            (by rintro w ⟨u, v, _, rfl⟩; exact ⟨(u, v), rfl⟩)
      · exact ⟨u, v, huv, rfl⟩
    have hA : Shao.prefixSum a v.val - Shao.prefixSum a u.val ≤ A N a := by
      apply le_csSup
      · exact (Set.finite_range (fun p : Fin (N + 1) × Fin (N + 1) =>
          Shao.prefixSum a p.2.val - Shao.prefixSum a p.1.val)).bddAbove.mono
            (by rintro w ⟨u, v, _, rfl⟩; exact ⟨(u, v), rfl⟩)
      · exact ⟨u, v, huv, rfl⟩
    have hr := le_max_left (Shao.prefixSum a N + 2 * R N a)
      (2 * A N a - Shao.prefixSum a N)
    have ha := le_max_right (Shao.prefixSum a N + 2 * R N a)
      (2 * A N a - Shao.prefixSum a N)
    rw [← hG] at hr ha
    constructor <;> linarith
  intro a b
  have hPS (m : ℕ) : Shao.prefixSum (joined a b) m =
      Shao.prefixSum a (min m k) + Shao.prefixSum b (m - k) := by
    simp only [Shao.prefixSum, Finset.sum_filter]
    rw [Fin.sum_univ_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      have hi := i.isLt
      simp only [joined, Fin.val_castAdd, dif_pos hi]
      have hh : i.val < m ↔ i.val < min m k := by omega
      simp only [hh]
    · apply Finset.sum_congr rfl
      intro i _
      have hi : ¬ k + i.val < k := by omega
      simp only [joined, Fin.val_natAdd, dif_neg hi, Nat.add_sub_cancel_left]
      have hh : k + i.val < m ↔ i.val < m - k := by omega
      simp only [hh]
  have hPSL (m : ℕ) (hm : m ≤ k) :
      Shao.prefixSum (joined a b) m = Shao.prefixSum a m := by
    rw [hPS, min_eq_left hm, Nat.sub_eq_zero_of_le hm, Shao.prefixSum_zero, add_zero]
  have hPSR (m : ℕ) (hm : k ≤ m) :
      Shao.prefixSum (joined a b) m = Shao.prefixSum a k + Shao.prefixSum b (m - k) := by
    rw [hPS, min_eq_right hm]
  have hST : Shao.prefixSum (joined a b) (k + l) =
      Shao.prefixSum a k + Shao.prefixSum b l := by
    rw [hPSR (k + l) (by omega), Nat.add_sub_cancel_left]
  have hSa := hC k a ⟨0, by omega⟩ ⟨0, by omega⟩ le_rfl
  have hSb := hC l b ⟨0, by omega⟩ ⟨0, by omega⟩ le_rfl
  simp only [Shao.prefixSum_zero, sub_self, mul_zero, add_zero, zero_sub] at hSa hSb
  have hPairs (u v : Fin (k + l + 1)) (huv : u.val ≤ v.val) :
      Shao.prefixSum (joined a b) (k + l) +
        2 * (Shao.prefixSum (joined a b) u.val - Shao.prefixSum (joined a b) v.val) ≤ L k a + L l b ∧
      2 * (Shao.prefixSum (joined a b) v.val - Shao.prefixSum (joined a b) u.val) -
        Shao.prefixSum (joined a b) (k + l) ≤ L k a + L l b := by
    rw [hST]
    by_cases hv : v.val ≤ k
    · have hu : u.val ≤ k := by omega
      rw [hPSL u.val hu, hPSL v.val hv]
      have h := hC k a ⟨u.val, by omega⟩ ⟨v.val, by omega⟩ huv
      dsimp only at h
      constructor <;> linarith
    · by_cases hu : k ≤ u.val
      · have hv' : k ≤ v.val := by omega
        rw [hPSR u.val hu, hPSR v.val hv']
        have h := hC l b ⟨u.val - k, by omega⟩ ⟨v.val - k, by omega⟩ (by dsimp only; omega)
        dsimp only at h
        constructor <;> linarith
      · have hu' : u.val ≤ k := by omega
        have hv' : k ≤ v.val := by omega
        rw [hPSL u.val hu', hPSR v.val hv']
        have h1 := hC k a ⟨u.val, by omega⟩ ⟨k, by omega⟩ (by dsimp only; omega)
        have h2 := hC l b ⟨0, by omega⟩ ⟨v.val - k, by omega⟩ (by dsimp only; omega)
        dsimp only at h1 h2
        simp only [Shao.prefixSum_zero] at h2
        constructor <;> linarith
  have hRR : R (k + l) (joined a b) ≤
      (L k a + L l b - Shao.prefixSum (joined a b) (k + l)) / 2 := by
    apply csSup_le
    · exact ⟨0, ⟨⟨0, by omega⟩, ⟨0, by omega⟩, le_rfl, by simp⟩⟩
    · rintro w ⟨u, v, huv, rfl⟩
      have h := (hPairs u v huv).1
      linarith
  have hAA : A (k + l) (joined a b) ≤
      (L k a + L l b + Shao.prefixSum (joined a b) (k + l)) / 2 := by
    apply csSup_le
    · exact ⟨0, ⟨⟨0, by omega⟩, ⟨0, by omega⟩, le_rfl, by simp⟩⟩
    · rintro w ⟨u, v, huv, rfl⟩
      have h := (hPairs u v huv).2
      linarith
  rw [hG]
  apply max_le <;> linarith

private theorem pww_iid_quadratic_maximal_tail
    (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (h2 : Integrable (fun z : ℝ => z ^ 2) rho)
    (hmean : (∫ z : ℝ, z ∂rho) = 0)
    (hvar : (∫ z : ℝ, z ^ 2 ∂rho) = 1)
    (N : ℕ) (v : ℝ) (hv : 0 < v) :
    let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => rho)
    P.real {a : Shao.Path N | v ≤ Shao.maxWithZero (-a)} ≤
      (N : ℝ) / v ^ 2 := by
  classical
  let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => rho)
  let S : ℕ → Shao.Path N → ℝ := fun j a => Shao.prefixSum a j
  let E : Fin (N + 1) → Set (Shao.Path N) := fun j =>
    {a | v ≤ -S j.val a ∧ ∀ i : Fin (N + 1), i.val < j.val → -S i.val a < v}
  let D : Fin (N + 1) → Shao.Path N → ℝ := fun j a => S N a - S j.val a
  let Tail : Set (Shao.Path N) := {a | v ≤ Shao.maxWithZero (-a)}
  change P.real Tail ≤ (N : ℝ) / v ^ 2
  have hnu2 : MemLp (id : ℝ → ℝ) 2 rho :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr h2
  have hcoord2 (i : Fin N) : MemLp (fun a : Shao.Path N => a i) 2 P :=
    hnu2.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => rho) i)
  have hcoordInt (i : Fin N) : (∫ a : Shao.Path N, a i ∂P) = 0 := by
    have hmap := integral_map (measurePreserving_eval (fun _ : Fin N => rho) i).aemeasurable
      measurable_id.aestronglyMeasurable
    rw [(measurePreserving_eval (fun _ : Fin N => rho) i).map_eq] at hmap
    simpa only [id_eq, hmean] using hmap.symm
  have hS2 (j : ℕ) : MemLp (S j) 2 P := by
    exact memLp_finsetSum (Finset.univ.filter (fun i : Fin N => i.val < j))
      (fun i _ => hcoord2 i)
  have hSmean (j : ℕ) : (∫ a, S j a ∂P) = 0 := by
    change (∫ a, ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < j), a i ∂P) = 0
    rw [integral_finsetSum _ (fun i _ => (hcoord2 i).integrable (by norm_num))]
    simp only [hcoordInt, Finset.sum_const_zero]
  have hSm (j : ℕ) : Measurable (S j) := (Shao.continuous_prefixSum j).measurable
  have hEm (j : Fin (N + 1)) : MeasurableSet (E j) := by
    change MeasurableSet ({a | v ≤ -S j.val a} ∩
      {a | ∀ i : Fin (N + 1), i.val < j.val → -S i.val a < v})
    apply MeasurableSet.inter (measurableSet_le (measurable_const (a := v)) (hSm j.val).neg)
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      measurableSet_lt (hSm i.val).neg measurable_const
  have hDm (j : Fin (N + 1)) : Measurable (D j) := (hSm N).sub (hSm j.val)
  have hD2 (j : Fin (N + 1)) : MemLp (D j) 2 P := (hS2 N).sub (hS2 j.val)
  have hSN : (∫ a, S N a ^ 2 ∂P) = (N : ℝ) := by
    have hlaw (i : Fin N) : IdentDistrib (fun a : Shao.Path N => a i) (id : ℝ → ℝ) P rho :=
      ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable,
        (measurePreserving_eval (fun _ : Fin N => rho) i).map_eq.trans Measure.map_id.symm⟩
    have hh := Shao.Probability.finite_iid_sumSquare_integral
      (fun i : Fin N => measurable_pi_apply i)
      (iIndepFun_pi (fun _ : Fin N => measurable_id.aemeasurable)) hlaw hnu2
    simpa only [finiteFeatureSum, S, Shao.prefixSum_length, hmean, hvar,
      zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero, mul_one] using hh
  run_tac
    let n := Lean.mkPrivateNameCore ("Shao.Probability.SourceCircularWitnessMoment".toName)
      ("Shao.Probability.SourceCircularWitnessMoment.cwm_iid_adjacent_windows".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hWindows".toName)) := $(Lean.mkIdent n)))
  have hCross (j : Fin (N + 1)) :
      (∫ a, (E j).indicator (S j.val) a * D j a ∂P) = 0 := by
    let W1 : Shao.Path N → Shao.Path j.val := fun a i => a ⟨i.val, by omega⟩
    let W2 : Shao.Path N → Shao.Path (N - j.val) := fun a i =>
      a ⟨j.val + i.val, by have hi := i.isLt; omega⟩
    let H : Set (Shao.Path j.val) := {a | v ≤ -Shao.prefixSum a j.val ∧
      ∀ i : Fin (j.val + 1), i.val < j.val → -Shao.prefixSum a i.val < v}
    have hHm : MeasurableSet H := by
      change MeasurableSet ({a : Shao.Path j.val | v ≤ -Shao.prefixSum a j.val} ∩
        {a | ∀ i : Fin (j.val + 1), i.val < j.val → -Shao.prefixSum a i.val < v})
      apply MeasurableSet.inter
        (measurableSet_le (measurable_const (a := v)) (Shao.continuous_prefixSum j.val).measurable.neg)
      simp only [Set.setOf_forall]
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
        measurableSet_lt (Shao.continuous_prefixSum i.val).measurable.neg measurable_const
    have hW1m : Measurable W1 := Measurable.of_eval (fun _ => measurable_pi_apply _)
    have hW2m : Measurable W2 := Measurable.of_eval (fun _ => measurable_pi_apply _)
    have hh := hWindows rho N 0 j.val (Nat.zero_le _) (by omega)
    dsimp only at hh
    simp only [Nat.zero_add, Nat.sub_zero] at hh
    change P.map W1 = _ ∧ P.map W2 = _ ∧ IndepFun W1 W2 P ∧
      ∀ a, (∀ m : ℕ, m ≤ j.val → Shao.prefixSum (W1 a) m =
          S m a - S 0 a) ∧
        (∀ m : ℕ, m ≤ N - j.val → Shao.prefixSum (W2 a) m =
          S (j.val + m) a - S j.val a) at hh
    have hPS1 (a : Shao.Path N) (m : ℕ) (hm : m ≤ j.val) :
        Shao.prefixSum (W1 a) m = S m a := by
      simpa only [S, Shao.prefixSum_zero, sub_zero] using (hh.2.2.2 a).1 m hm
    have hPS2 (a : Shao.Path N) : Shao.prefixSum (W2 a) (N - j.val) = D j a := by
      have he : j.val + (N - j.val) = N := by omega
      simpa only [he, D] using (hh.2.2.2 a).2 (N - j.val) le_rfl
    have hE (a : Shao.Path N) : W1 a ∈ H ↔ a ∈ E j := by
      dsimp only [H, E]
      simp only [Set.mem_setOf_eq]
      rw [hPS1 a j.val le_rfl]
      constructor
      · rintro ⟨h, hpre⟩
        refine ⟨h, fun i hi => ?_⟩
        have hp := hpre ⟨i.val, by omega⟩ hi
        rwa [hPS1 a i.val (by omega)] at hp
      · rintro ⟨h, hpre⟩
        refine ⟨h, fun i hi => ?_⟩
        rw [hPS1 a i.val (by omega)]
        exact hpre ⟨i.val, by omega⟩ hi
    have hf (a : Shao.Path N) :
        H.indicator (fun u => Shao.prefixSum u j.val) (W1 a) = (E j).indicator (S j.val) a := by
      by_cases h : a ∈ E j
      · rw [Set.indicator_of_mem ((hE a).mpr h), Set.indicator_of_mem h, hPS1 a j.val le_rfl]
      · rw [Set.indicator_of_notMem (by simpa only [hE a] using h), Set.indicator_of_notMem h]
    have hind := hh.2.2.1.comp
      ((Shao.continuous_prefixSum j.val).measurable.indicator hHm)
      (Shao.continuous_prefixSum (N - j.val)).measurable
    have hm1 : AEStronglyMeasurable ((E j).indicator (S j.val)) P :=
      ((hSm j.val).indicator (hEm j)).aestronglyMeasurable
    have hm2 := (hDm j).aestronglyMeasurable (μ := P)
    have hind' : IndepFun ((E j).indicator (S j.val)) (D j) P := by
      convert hind using 1 <;> funext a
      · exact (hf a).symm
      · exact (hPS2 a).symm
    have he := hind'.integral_fun_mul_eq_mul_integral hm1 hm2
    rw [show (∫ a, D j a ∂P) = 0 by
      change (∫ a, S N a - S j.val a ∂P) = 0
      rw [integral_sub ((hS2 N).integrable (by norm_num)) ((hS2 j.val).integrable (by norm_num))]
      rw [hSmean, hSmean, sub_self], mul_zero] at he
    exact he
  have hEach (j : Fin (N + 1)) : v ^ 2 * P.real (E j) ≤
      ∫ a, (E j).indicator (fun a => S N a ^ 2) a ∂P := by
    have hprod : Integrable (fun a => (E j).indicator (S j.val) a * D j a) P :=
      ((hS2 j.val).indicator (hEm j).nullMeasurableSet).integrable_mul (hD2 j)
    have hsq : Integrable (fun a => (E j).indicator (fun a => S j.val a ^ 2) a) P :=
      (hS2 j.val).integrable_sq.indicator (hEm j)
    have hdsq : Integrable (fun a => (E j).indicator (fun a => D j a ^ 2) a) P :=
      (hD2 j).integrable_sq.indicator (hEm j)
    have heq : (fun a => (E j).indicator (fun a => S N a ^ 2) a) =
        (fun a => (E j).indicator (fun a => S j.val a ^ 2) a +
          2 * ((E j).indicator (S j.val) a * D j a) +
          (E j).indicator (fun a => D j a ^ 2) a) := by
      funext a
      by_cases h : a ∈ E j
      · simp only [Set.indicator_of_mem h, D]
        ring
      · simp only [Set.indicator_of_notMem h, mul_zero, zero_mul, add_zero]
    have hi1 := integral_add (hsq.add (hprod.const_mul 2)) hdsq
    have hi2 := integral_add hsq (hprod.const_mul 2)
    simp only [Pi.add_apply] at hi1 hi2
    rw [heq, hi1, hi2, integral_const_mul, hCross, mul_zero, add_zero]
    have hd : 0 ≤ ∫ a, (E j).indicator (fun a => D j a ^ 2) a ∂P :=
      integral_nonneg (fun a => Set.indicator_nonneg (fun _ _ => sq_nonneg _) a)
    have hl : v ^ 2 * P.real (E j) ≤
        ∫ a, (E j).indicator (fun a => S j.val a ^ 2) a ∂P := by
      calc
        _ = ∫ a, (E j).indicator (fun _ => v ^ 2) a ∂P := by
          rw [integral_indicator (hEm j), setIntegral_const]
          simp [smul_eq_mul, mul_comm]
        _ ≤ _ := by
          apply integral_mono ((integrable_const _).indicator (hEm j)) hsq
          intro a
          by_cases h : a ∈ E j
          · simp only [Set.indicator_of_mem h]
            have hvj := h.1
            nlinarith [sq_nonneg (S j.val a + v)]
          · simp only [Set.indicator_of_notMem h, le_refl]
    linarith
  have hDisj (i j : Fin (N + 1)) (hij : i ≠ j) : Disjoint (E i) (E j) := by
    apply Set.disjoint_left.2
    rintro a hi hj
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact (not_lt_of_ge hi.1) (hj.2 i h)
    · exact (not_lt_of_ge hj.1) (hi.2 j h)
  have hUnion : (⋃ j : Fin (N + 1), E j) = Tail := by
    ext a
    have hTail : a ∈ Tail ↔ ∃ j : Fin (N + 1), v ≤ -S j.val a := by
      change (v ≤ Shao.maxWithZero (-a)) ↔ _
      unfold Shao.maxWithZero
      rw [Finset.le_sup'_iff]
      simp only [Finset.mem_Icc, Nat.zero_le, true_and, Shao.prefixSum_neg]
      constructor
      · rintro ⟨j, hj, h⟩
        exact ⟨⟨j, by omega⟩, h⟩
      · rintro ⟨j, hj⟩
        exact ⟨j.val, by omega, hj⟩
    rw [Set.mem_iUnion, hTail]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, hj.1⟩
    · rintro ⟨j, hj⟩
      have hex : ∃ m : ℕ, m ≤ N ∧ v ≤ -S m a := ⟨j.val, by omega, hj⟩
      let m := Nat.find hex
      have hm : m ≤ N ∧ v ≤ -S m a := Nat.find_spec hex
      refine ⟨⟨m, by omega⟩, hm.2, fun i hi => ?_⟩
      have hmin := Nat.find_min hex hi
      by_contra hn
      exact hmin ⟨by omega, le_of_not_gt hn⟩
  have hMeasure : P.real Tail = ∑ j : Fin (N + 1), P.real (E j) := by
    rw [← hUnion, measureReal_iUnion_fintype hDisj hEm]
  have hSum : ∑ j : Fin (N + 1), (∫ a, (E j).indicator (fun a => S N a ^ 2) a ∂P) ≤
      (N : ℝ) := by
    rw [← integral_finsetSum Finset.univ
      (fun j _ => (hS2 N).integrable_sq.indicator (hEm j)), ← hSN]
    apply integral_mono
      (integrable_finsetSum _ (fun j _ => (hS2 N).integrable_sq.indicator (hEm j)))
      (hS2 N).integrable_sq
    intro a
    change (∑ i : Fin (N + 1), (E i).indicator (fun x => S N x ^ 2) a) ≤ S N a ^ 2
    by_cases h : ∃ j, a ∈ E j
    · obtain ⟨j, hj⟩ := h
      rw [Finset.sum_eq_single j]
      · rw [Set.indicator_of_mem hj]
      · intro i _ hij
        exact Set.indicator_of_notMem (fun hi => Set.disjoint_left.1 (hDisj i j hij) hi hj) _
      · simp
    · simp only [not_exists] at h
      simp only [Set.indicator_of_notMem (h _), Finset.sum_const_zero]
      exact sq_nonneg _
  have hBound : v ^ 2 * P.real Tail ≤ (N : ℝ) := by
    rw [hMeasure, Finset.mul_sum]
    exact (Finset.sum_le_sum (fun j _ => hEach j)).trans hSum
  exact (le_div_iff₀ (sq_pos_of_pos hv)).mpr (by nlinarith [hBound])

private theorem pww_ordinary_closed_lower_survival :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (B : ℝ), 0 < B → (∀ᵐ z : ℝ ∂rho, |z| ≤ B) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ (N : ℕ), 0 < N →
          let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => rho)
          ∀ b : ℝ, 0 ≤ b →
            P.real {a : Shao.Path N | ∀ k : Fin (N + 1),
              -b ≤ Shao.prefixSum a k.val} ≤
                C * (b + beta) / Real.sqrt (N : ℝ) := by
  classical
  rcases Shao.Probability.original_closed_survival_uniform with ⟨C0, hC0, hOS⟩
  refine ⟨max C0 1, le_max_right _ _, ?_⟩
  intro rho hprob B hB hs hmean hsecond beta N hN P b hb
  have hbase := boundedQuadraticTilt_density_moments rho B 0 0 hB (le_refl 0) hs
  rcases hbase with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hpows, _⟩
  have h2 : Integrable (fun z : ℝ => z ^ 2) rho := (hpows 2).1
  have h3 : Integrable (fun z : ℝ => |z| ^ 3) rho := (hpows 3).2.2.1
  have hb0 : 0 ≤ beta := integral_nonneg (fun z => pow_nonneg (abs_nonneg z) 3)
  let q : ℝ := Real.sqrt (N : ℝ)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hq : 0 < q := Real.sqrt_pos.2 hNr
  have hq2 : q ^ 2 = (N : ℝ) := Real.sq_sqrt hNr.le
  let f : ℝ → ℝ := fun z => -z / q
  have hf : Measurable f := by dsimp [f]; fun_prop
  let nu : Measure ℝ := rho.map f
  letI : IsProbabilityMeasure nu :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).mpr inferInstance
  have h2nu : Integrable (fun z : ℝ => z ^ 2) nu := by
    apply (integrable_map_measure (by fun_prop) hf.aemeasurable).2
    convert h2.div_const (q ^ 2) using 1
    funext z
    dsimp [f]
    ring
  have hMeannu : (∫ z : ℝ, z ∂nu) = 0 := by
    change (∫ z : ℝ, z ∂rho.map f) = 0
    rw [integral_map hf.aemeasurable (by fun_prop)]
    change (∫ z : ℝ, -z / q ∂rho) = 0
    rw [integral_div, integral_neg, hmean, neg_zero, zero_div]
  have hSecondnu : (∫ z : ℝ, z ^ 2 ∂nu) = 1 / q ^ 2 := by
    change (∫ z : ℝ, z ^ 2 ∂rho.map f) = 1 / q ^ 2
    rw [integral_map hf.aemeasurable (by fun_prop)]
    have he : (fun z : ℝ => (f z) ^ 2) = (fun z => z ^ 2 / q ^ 2) := by
      funext z
      dsimp [f]
      ring
    rw [he, integral_div, hsecond]
  have hNorm : (N : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 := by
    rw [hSecondnu, hq2]
    field_simp [ne_of_gt hNr]
  have h3f : Integrable (fun z : ℝ => |f z| ^ 3) rho := by
    convert h3.div_const (q ^ 3) using 1
    funext z
    dsimp [f]
    rw [abs_div, abs_neg, abs_of_pos hq, div_pow]
  have htrNu : Integrable Shao.truncationF nu := by
    simpa only [one_mul] using Shao.integrable_truncationF_mul nu h2nu 1
  have htrF : Integrable (fun z : ℝ => Shao.truncationF (f z)) rho := by
    exact (integrable_map_measure Shao.continuous_truncationF.measurable.aestronglyMeasurable
      hf.aemeasurable).1 htrNu
  have hInt : (∫ z : ℝ, Shao.truncationF (f z) ∂rho) ≤ beta / q ^ 3 := by
    calc
      _ ≤ ∫ z : ℝ, |f z| ^ 3 ∂rho := by
        apply integral_mono_ae htrF h3f
        exact ae_of_all _ (fun z => by
          dsimp only [Shao.truncationF]
          calc
            _ ≤ (f z) ^ 2 * |f z| :=
              mul_le_mul_of_nonneg_left (min_le_left _ _) (sq_nonneg _)
            _ = |f z| ^ 3 := by rw [← sq_abs (f z)]; ring)
      _ = beta / q ^ 3 := by
        dsimp [f]
        simp only [abs_div, abs_neg, abs_of_pos hq, div_pow, integral_div]
        rfl
  have hR : Shao.truncationBudget nu N 0 ≤ beta / q := by
    dsimp only [Shao.truncationBudget]
    simp only [add_zero, one_mul]
    rw [integral_map hf.aemeasurable Shao.continuous_truncationF.measurable.aestronglyMeasurable]
    calc
      _ ≤ (N : ℝ) * (beta / q ^ 3) := mul_le_mul_of_nonneg_left hInt hNr.le
      _ = beta / q := by
        rw [← hq2]
        field_simp [hq.ne']
        <;> ring
  let F : Shao.Path N → Shao.Path N := fun a i => f (a i)
  have hFm : Measurable F := by dsimp [F, f]; fun_prop
  have hMap : P.map F = Measure.pi (fun _ : Fin N => nu) :=
    Measure.pi_map_pi (fun _ : Fin N => hf.aemeasurable)
  have hPS (a : Shao.Path N) (m : ℕ) :
      Shao.prefixSum (F a) m = -Shao.prefixSum a m / q := by
    have he : F a = (-1 / q) • a := by
      funext i
      dsimp [F, f]
      ring
    rw [he, Shao.prefixSum_smul]
    ring
  have hEvent : F ⁻¹' {v : Shao.Path N | Shao.maxWithZero v ≤ b / q} =
      {a : Shao.Path N | ∀ k : Fin (N + 1), -b ≤ Shao.prefixSum a k.val} := by
    ext a
    change (Shao.maxWithZero (F a) ≤ b / q) ↔
      ∀ k : Fin (N + 1), -b ≤ Shao.prefixSum a k.val
    rw [Shao.maxWithZero_le_iff]
    constructor
    · intro h k
      have hh := h k.val (Nat.le_of_lt_succ k.isLt)
      rw [hPS] at hh
      have hh' := (div_le_div_iff_of_pos_right hq).1 hh
      linarith
    · intro h m hm
      have hh := h ⟨m, Nat.lt_succ_of_le hm⟩
      rw [hPS]
      apply (div_le_div_iff_of_pos_right hq).2
      linarith
  have hA : MeasurableSet {v : Shao.Path N | Shao.maxWithZero v ≤ b / q} :=
    measurableSet_le Shao.measurable_maxWithZero measurable_const
  have hh := hOS nu N hN h2nu hMeannu hNorm 1 (b / q) (Or.inl rfl) (div_nonneg hb hq.le)
  simp only [one_smul] at hh
  rw [← hMap, Measure.real_def, Measure.map_apply hFm hA, hEvent] at hh
  change P.real {a : Shao.Path N | ∀ k : Fin (N + 1), -b ≤ Shao.prefixSum a k.val} ≤
    C0 * (b / q + Shao.truncationBudget nu N 0) at hh
  calc
    _ ≤ C0 * (b / q + Shao.truncationBudget nu N 0) := hh
    _ ≤ C0 * (b / q + beta / q) :=
      mul_le_mul_of_nonneg_left (by linarith only [hR]) hC0.le
    _ = C0 * (b + beta) / q := by ring
    _ ≤ max C0 1 * (b + beta) / Real.sqrt (N : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C0 1) (add_nonneg hb hb0)) hq.le

private theorem pww_fixed_level_hit_before_lower_exit :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (B : ℝ), 0 < B → (∀ᵐ z : ℝ ∂rho, |z| ≤ B) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ N : ℕ,
          let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => rho)
          ∀ b v : ℝ, 0 ≤ b → 0 < v →
            let H : Set (Shao.Path N) := {a | ∃ k : Fin (N + 1),
              0 < k.val ∧ v ≤ Shao.prefixSum a k.val ∧
                ∀ j : Fin (N + 1), j.val ≤ k.val →
                  -b ≤ Shao.prefixSum a j.val}
            P.real H ≤ C * (b + beta) / v := by
  classical
  obtain ⟨C0, hC0, hOS⟩ := pww_ordinary_closed_lower_survival
  refine ⟨16 * C0, by linarith, ?_⟩
  intro rho hprob B hB hs hmean hvar beta N P b v hb hv H
  have hbase := boundedQuadraticTilt_density_moments rho B 0 0 hB (le_refl 0) hs
  rcases hbase with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hpows, _⟩
  have h2 := (hpows 2).1
  have h3 := (hpows 3).2.2.1
  have hbeta : 1 ≤ beta := by
    have hh : 3 * (∫ z : ℝ, z ^ 2 ∂rho) ≤ 2 * beta + 1 := by
      calc
        _ = ∫ z : ℝ, 3 * z ^ 2 ∂rho := (integral_const_mul _ _).symm
        _ ≤ ∫ z : ℝ, 2 * |z| ^ 3 + 1 ∂rho := by
          apply integral_mono (h2.const_mul 3) ((h3.const_mul 2).add (integrable_const 1))
          intro z
          change 3 * z ^ 2 ≤ 2 * |z| ^ 3 + 1
          have hh := mul_nonneg (sq_nonneg (|z| - 1)) (by positivity : 0 ≤ 2 * |z| + 1)
          rw [← sq_abs z]
          nlinarith only [hh]
        _ = 2 * beta + 1 := by rw [integral_add (h3.const_mul 2) (integrable_const 1), integral_const_mul]; simp [beta]
    rw [hvar] at hh
    linarith only [hh]
  have hsmall : v < 4 → P.real H ≤ 16 * C0 * (b + beta) / v := by
    intro hvs
    have hOne : 1 ≤ C0 * (b + beta) :=
      one_le_mul_of_one_le_of_one_le hC0 (by linarith only [hb, hbeta])
    have hnum : v ≤ 16 * C0 * (b + beta) := by nlinarith only [hOne, hvs]
    exact (measureReal_le_one (μ := P) (s := H)).trans ((le_div_iff₀ hv).2 (by nlinarith only [hnum]))
  by_cases hvs : v < 4
  · exact hsmall hvs
  have hv4 : 4 ≤ v := le_of_not_gt hvs
  let m : ℕ := ⌊v ^ 2 / 4⌋₊
  have hmup : (m : ℝ) ≤ v ^ 2 / 4 := Nat.floor_le (by positivity)
  have hmnear : v ^ 2 / 4 < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmlo : v ^ 2 / 8 ≤ (m : ℝ) := by nlinarith only [hmnear, hv4, sq_nonneg (v - 4)]
  have hmr : 0 < (m : ℝ) := by nlinarith only [hmlo, hv]
  have hm : 0 < m := by exact_mod_cast hmr
  have hmsq : v / 4 ≤ Real.sqrt (m : ℝ) := by
    have hsq := Real.sq_sqrt hmr.le
    have hnn := Real.sqrt_nonneg (m : ℝ)
    nlinarith only [hsq, hnn, hmlo, hv]
  let Q : (j : ℕ) → Measure (Shao.Path j) := fun j => Measure.pi (fun _ : Fin j => rho)
  let Alive : (j : ℕ) → Set (Shao.Path j) := fun j =>
    {a | ∀ i : Fin (j + 1), -b ≤ Shao.prefixSum a i.val}
  let Hit : (j : ℕ) → Set (Shao.Path j) := fun j =>
    {a | ∃ k : Fin (j + 1), 0 < k.val ∧ v ≤ Shao.prefixSum a k.val ∧
      ∀ i : Fin (j + 1), i.val ≤ k.val → -b ≤ Shao.prefixSum a i.val}
  have hAlive (j : ℕ) : MeasurableSet (Alive j) := by
    simp only [Alive, Set.setOf_forall]
    exact MeasurableSet.iInter fun i : Fin (j + 1) =>
      measurableSet_le (measurable_const (a := -b))
        ((Shao.continuous_prefixSum i.val).measurable : Measurable (fun a : Shao.Path j => Shao.prefixSum a i.val))
  have hHit (j : ℕ) : MeasurableSet (Hit j) := by
    simp only [Hit, Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro k
    by_cases hk : 0 < k.val
    · simp only [hk, true_and, Set.setOf_and, Set.setOf_forall]
      exact (measurableSet_le measurable_const (Shao.continuous_prefixSum k.val).measurable).inter
        (MeasurableSet.iInter fun i : Fin (j + 1) => MeasurableSet.iInter fun _ : i.val ≤ k.val =>
          measurableSet_le (measurable_const (a := -b))
            ((Shao.continuous_prefixSum i.val).measurable : Measurable (fun a : Shao.Path j => Shao.prefixSum a i.val)))
    · simp only [hk, false_and, Set.setOf_false]
      exact MeasurableSet.empty
  run_tac
    let n := Lean.mkPrivateNameCore ("Shao.Probability.SourceCircularWitnessMoment".toName)
      ("Shao.Probability.SourceCircularWitnessMoment.cwm_iid_adjacent_windows".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hWindows".toName)) := $(Lean.mkIdent n)))
  let E : Fin (m + 1) → Set (Shao.Path m) := fun j => {a |
    v ≤ Shao.prefixSum a j.val ∧
    (∀ i : Fin (m + 1), i.val < j.val → Shao.prefixSum a i.val < v) ∧
    ∀ i : Fin (m + 1), i.val ≤ j.val → -b ≤ Shao.prefixSum a i.val}
  have hPsm (q : ℕ) : Measurable (fun a : Shao.Path m => Shao.prefixSum a q) :=
    (Shao.continuous_prefixSum q).measurable
  have hEm (j : Fin (m + 1)) : MeasurableSet (E j) := by
    change MeasurableSet ({a : Shao.Path m | v ≤ Shao.prefixSum a j.val} ∩
      ({a | ∀ i : Fin (m + 1), i.val < j.val → Shao.prefixSum a i.val < v} ∩
       {a | ∀ i : Fin (m + 1), i.val ≤ j.val → -b ≤ Shao.prefixSum a i.val}))
    refine (measurableSet_le (measurable_const (a := v)) (hPsm j.val)).inter ?_
    apply MeasurableSet.inter
    · simp only [Set.setOf_forall]
      exact MeasurableSet.iInter fun i : Fin (m + 1) =>
        MeasurableSet.iInter fun _ : i.val < j.val =>
          measurableSet_lt (hPsm i.val) (measurable_const (a := v))
    · simp only [Set.setOf_forall]
      exact MeasurableSet.iInter fun i : Fin (m + 1) =>
        MeasurableSet.iInter fun _ : i.val ≤ j.val =>
          measurableSet_le (measurable_const (a := -b)) (hPsm i.val)
  have hDisj (i j : Fin (m + 1)) (hij : i ≠ j) : Disjoint (E i) (E j) := by
    apply Set.disjoint_left.2
    rintro a hi hj
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact (not_lt_of_ge hi.1) (hj.2.1 i h)
    · exact (not_lt_of_ge hj.1) (hi.2.1 j h)
  have hUnion : (⋃ j : Fin (m + 1), E j) = Hit m := by
    ext a
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩
      have hjp : 0 < j.val := by
        by_contra h
        have hz : j.val = 0 := by omega
        have hh := hj.1
        rw [hz, Shao.prefixSum_zero] at hh
        linarith
      exact ⟨j, hjp, hj.1, hj.2.2⟩
    · rintro ⟨k, hkp, hkv, hkpre⟩
      have hex : ∃ q : ℕ, q ≤ k.val ∧ v ≤ Shao.prefixSum a q := ⟨k.val, le_rfl, hkv⟩
      let q := Nat.find hex
      have hq : q ≤ k.val ∧ v ≤ Shao.prefixSum a q := Nat.find_spec hex
      refine ⟨⟨q, by omega⟩, hq.2, ?_, ?_⟩
      · intro i hi
        change i.val < q at hi
        by_contra hn
        exact Nat.find_min hex hi ⟨by omega, le_of_not_gt hn⟩
      · intro i hi
        change i.val ≤ q at hi
        exact hkpre i (by omega)
  let Good : (j : Fin (m + 1)) → Set (Shao.Path m) := fun j =>
    {a | Shao.maxWithZero (fun i : Fin (m - j.val) => -a ⟨j.val + i.val, by have hi := i.isLt; omega⟩) ≤ v + b}
  have hContinue (j : Fin (m + 1)) :
      (1 / 2 : ℝ) * (Q m).real (E j) ≤ (Q m).real (E j ∩ Good j) ∧
      E j ∩ Good j ⊆ Alive m := by
    let W1 : Shao.Path m → Shao.Path j.val := fun a i => a ⟨i.val, by omega⟩
    let W2 : Shao.Path m → Shao.Path (m - j.val) := fun a i => a ⟨j.val + i.val, by have hi := i.isLt; omega⟩
    let F : Set (Shao.Path j.val) := {a | v ≤ Shao.prefixSum a j.val ∧
      (∀ i : Fin (j.val + 1), i.val < j.val → Shao.prefixSum a i.val < v) ∧
      ∀ i : Fin (j.val + 1), i.val ≤ j.val → -b ≤ Shao.prefixSum a i.val}
    let G : Set (Shao.Path (m - j.val)) := {a | Shao.maxWithZero (-a) ≤ v + b}
    have hPSj (q : ℕ) : Measurable (fun a : Shao.Path j.val => Shao.prefixSum a q) :=
      (Shao.continuous_prefixSum q).measurable
    have hFm : MeasurableSet F := by
      change MeasurableSet ({a : Shao.Path j.val | v ≤ Shao.prefixSum a j.val} ∩
        ({a | ∀ i : Fin (j.val + 1), i.val < j.val → Shao.prefixSum a i.val < v} ∩
         {a | ∀ i : Fin (j.val + 1), i.val ≤ j.val → -b ≤ Shao.prefixSum a i.val}))
      refine (measurableSet_le (measurable_const (a := v)) (hPSj j.val)).inter ?_
      apply MeasurableSet.inter
      · simp only [Set.setOf_forall]
        exact MeasurableSet.iInter fun i : Fin (j.val + 1) =>
          MeasurableSet.iInter fun _ : i.val < j.val =>
            measurableSet_lt (hPSj i.val) (measurable_const (a := v))
      · simp only [Set.setOf_forall]
        exact MeasurableSet.iInter fun i : Fin (j.val + 1) =>
          MeasurableSet.iInter fun _ : i.val ≤ j.val =>
            measurableSet_le (measurable_const (a := -b)) (hPSj i.val)
    have hGm : MeasurableSet G := measurableSet_le (Shao.measurable_maxWithZero.comp measurable_neg) measurable_const
    have hW1m : Measurable W1 := Measurable.of_eval (fun _ => measurable_pi_apply _)
    have hW2m : Measurable W2 := Measurable.of_eval (fun _ => measurable_pi_apply _)
    have hh := hWindows rho m 0 j.val (Nat.zero_le _) (by omega)
    dsimp only at hh
    simp only [Nat.zero_add, Nat.sub_zero] at hh
    change (Q m).map W1 = Q j.val ∧ (Q m).map W2 = Q (m - j.val) ∧
      IndepFun W1 W2 (Q m) ∧ ∀ a,
        (∀ q : ℕ, q ≤ j.val → Shao.prefixSum (W1 a) q = Shao.prefixSum a q - Shao.prefixSum a 0) ∧
        (∀ q : ℕ, q ≤ m - j.val → Shao.prefixSum (W2 a) q =
          Shao.prefixSum a (j.val + q) - Shao.prefixSum a j.val) at hh
    have hPS (a : Shao.Path m) (q : ℕ) (hq : q ≤ j.val) :
        Shao.prefixSum (W1 a) q = Shao.prefixSum a q := by
      simpa only [Shao.prefixSum_zero, sub_zero] using (hh.2.2.2 a).1 q hq
    have hE : W1 ⁻¹' F = E j := by
      ext a
      change (v ≤ Shao.prefixSum (W1 a) j.val ∧
        (∀ i : Fin (j.val + 1), i.val < j.val → Shao.prefixSum (W1 a) i.val < v) ∧
        ∀ i : Fin (j.val + 1), i.val ≤ j.val → -b ≤ Shao.prefixSum (W1 a) i.val) ↔ _
      rw [hPS a j.val le_rfl]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, ?_, ?_⟩
        · intro i hi
          have ht := h2 ⟨i.val, by omega⟩ hi
          rwa [hPS a i.val (by omega)] at ht
        · intro i hi
          have ht := h3 ⟨i.val, by omega⟩ hi
          rwa [hPS a i.val hi] at ht
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, ?_, ?_⟩
        · intro i hi
          rw [hPS a i.val (by omega)]
          exact h2 ⟨i.val, by omega⟩ hi
        · intro i hi
          rw [hPS a i.val hi]
          exact h3 ⟨i.val, by omega⟩ hi
    have hG : W2 ⁻¹' G = Good j := rfl
    have hGood : (1 / 2 : ℝ) ≤ (Q (m - j.val)).real G := by
      have hpos : 0 < v + b := by linarith
      have ht := pww_iid_quadratic_maximal_tail rho h2 hmean hvar (m - j.val) (v + b) hpos
      have hcomp : (Q (m - j.val)).real Gᶜ ≤ ((m - j.val : ℕ) : ℝ) / (v + b) ^ 2 := by
        apply le_trans (measureReal_mono (show Gᶜ ⊆ {a | v + b ≤ Shao.maxWithZero (-a)} from ?_)) ht
        intro a ha
        change ¬ Shao.maxWithZero (-a) ≤ v + b at ha
        exact le_of_lt (lt_of_not_ge ha)
      have hfrac : ((m - j.val : ℕ) : ℝ) / (v + b) ^ 2 ≤ 1 / 4 := by
        apply (div_le_iff₀ (sq_pos_of_pos hpos)).2
        have hlen : ((m - j.val : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m j.val
        have hsquare : v ^ 2 ≤ (v + b) ^ 2 := (sq_le_sq₀ hv.le hpos.le).2 (by linarith only [hb])
        nlinarith only [hlen, hmup, hsquare]
      rw [measureReal_compl hGm, probReal_univ] at hcomp
      linarith
    have hFact : (Q m).real (E j ∩ Good j) =
        (Q m).real (E j) * (Q (m - j.val)).real G := by
      have ht := hh.2.2.1.measure_inter_preimage_eq_mul F G hFm hGm
      apply_fun ENNReal.toReal at ht
      simp only [ENNReal.toReal_mul] at ht
      change (Q m).real (W1 ⁻¹' F ∩ W2 ⁻¹' G) =
        (Q m).real (W1 ⁻¹' F) * (Q m).real (W2 ⁻¹' G) at ht
      have hgmap : (Q m).real (W2 ⁻¹' G) = (Q (m - j.val)).real G := by
        rw [← hh.2.1]
        simp only [Measure.real_def, Measure.map_apply hW2m hGm]
      rw [hE, hgmap, hG] at ht
      exact ht
    constructor
    · rw [hFact]
      calc
        _ = (Q m).real (E j) * (1 / 2 : ℝ) := mul_comm _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hGood measureReal_nonneg
    · rintro a ⟨hEa, hGa⟩ i
      by_cases hi : i.val ≤ j.val
      · exact hEa.2.2 i hi
      · have hg : Shao.maxWithZero (-(W2 a)) ≤ v + b := hGa
        have hsuf := (Shao.maxWithZero_le_iff (-(W2 a)) (v + b)).1 hg (i.val - j.val) (by omega)
        rw [Shao.prefixSum_neg, (hh.2.2.2 a).2 (i.val - j.val) (by omega)] at hsuf
        have he : j.val + (i.val - j.val) = i.val := by omega
        rw [he] at hsuf
        linarith [hEa.1]
  have hHalf : (1 / 2 : ℝ) * (Q m).real (Hit m) ≤ (Q m).real (Alive m) := by
    rw [← hUnion, measureReal_iUnion_fintype hDisj hEm, Finset.mul_sum]
    calc
      _ ≤ ∑ j : Fin (m + 1), (Q m).real (E j ∩ Good j) := Finset.sum_le_sum (fun j _ => (hContinue j).1)
      _ = (Q m).real (⋃ j : Fin (m + 1), E j ∩ Good j) := by
        symm
        apply measureReal_iUnion_fintype (μ := Q m)
        · intro i j hij
          exact (hDisj i j hij).mono Set.inter_subset_left Set.inter_subset_left
        · intro j
          exact (hEm j).inter (measurableSet_le (Shao.measurable_maxWithZero.comp (by fun_prop)) measurable_const)
      _ ≤ _ := measureReal_mono (by
        intro a ha
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ha
        exact (hContinue j).2 hj)
  let K : ℕ := max N m
  let W : (j : ℕ) → (hj : j ≤ K) → Shao.Path K → Shao.Path j := fun j hj a i => a ⟨i.val, by omega⟩
  have hProj (j : ℕ) (hj : j ≤ K) : (Q K).map (W j hj) = Q j ∧
      ∀ a q, q ≤ j → Shao.prefixSum (W j hj a) q = Shao.prefixSum a q := by
    have ht := hWindows rho K 0 j (Nat.zero_le _) hj
    dsimp only at ht
    simp only [Nat.zero_add, Nat.sub_zero] at ht
    refine ⟨ht.1, fun a q hq => ?_⟩
    simpa only [Shao.prefixSum_zero, sub_zero] using (ht.2.2.2 a).1 q hq
  have hNK : N ≤ K := le_max_left _ _
  have hmK : m ≤ K := le_max_right _ _
  have hIncl : (W N hNK) ⁻¹' Hit N ⊆
      (W m hmK) ⁻¹' Hit m ∪ (W m hmK) ⁻¹' Alive m := by
    rintro a ⟨j, hjp, hjv, hjlow⟩
    by_cases hjm : j.val ≤ m
    · left
      refine ⟨⟨j.val, by omega⟩, hjp, ?_, ?_⟩
      · rw [(hProj m hmK).2 a j.val hjm]
        rwa [(hProj N hNK).2 a j.val (by omega)] at hjv
      · intro i hi
        change i.val ≤ j.val at hi
        rw [(hProj m hmK).2 a i.val (by omega)]
        have ht := hjlow ⟨i.val, by omega⟩ hi
        rwa [(hProj N hNK).2 a i.val (by omega)] at ht
    · right
      intro i
      rw [(hProj m hmK).2 a i.val (by omega)]
      have ht := hjlow ⟨i.val, by omega⟩ (by dsimp only; omega)
      rwa [(hProj N hNK).2 a i.val (by omega)] at ht
  have hMaps (j : ℕ) (hj : j ≤ K) (F : Set (Shao.Path j)) (hFm : MeasurableSet F) :
      (Q K).real ((W j hj) ⁻¹' F) = (Q j).real F := by
    rw [← (hProj j hj).1]
    simp only [Measure.real_def, Measure.map_apply (show Measurable (W j hj) from
      Measurable.of_eval (fun _ => measurable_pi_apply _)) hFm]
  have hNbound : P.real H ≤ 3 * (Q m).real (Alive m) := by
    change (Q N).real (Hit N) ≤ _
    rw [← hMaps N hNK (Hit N) (hHit N)]
    have ht := (measureReal_mono (μ := Q K) hIncl (measure_ne_top _ _)).trans (measureReal_union_le _ _)
    rw [hMaps m hmK (Hit m) (hHit m), hMaps m hmK (Alive m) (hAlive m)] at ht
    linarith
  have hos := hOS rho B hB hs hmean hvar m hm b hb
  change (Q m).real (Alive m) ≤ C0 * (b + beta) / Real.sqrt (m : ℝ) at hos
  calc
    _ ≤ 3 * (Q m).real (Alive m) := hNbound
    _ ≤ 3 * (C0 * (b + beta) / Real.sqrt (m : ℝ)) := mul_le_mul_of_nonneg_left hos (by norm_num)
    _ ≤ 16 * C0 * (b + beta) / v := by
      apply (le_div_iff₀ hv).2
      have hspos := Real.sqrt_pos.2 hmr
      have hbb : 0 ≤ C0 * (b + beta) := mul_nonneg (by linarith only [hC0]) (by linarith only [hb, hbeta])
      rw [show 3 * (C0 * (b + beta) / Real.sqrt (m : ℝ)) * v =
        C0 * (b + beta) * (3 * v) / Real.sqrt (m : ℝ) by ring]
      apply (div_le_iff₀ hspos).2
      calc
        _ ≤ C0 * (b + beta) * (16 * Real.sqrt (m : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith only [hmsq, hspos]) hbb
        _ = _ := by ring

private theorem pww_circular_witness_coordinate_lipschitz (N : ℕ) :
    let L : Shao.Path N → ℝ := fun a =>
      if hN : 0 < N then
        sSup {w : ℝ | ∃ i : Fin N, ∃ k : Fin (N + 1),
          w = Shao.prefixSum a N -
            2 * ∑ r ∈ Finset.range k.val,
              a ⟨(i.val + r) % N, Nat.mod_lt _ hN⟩}
      else 0
    ∀ (a : Shao.Path N) (i : Fin N) (z z' : ℝ),
      |L (Function.update a i z') - L (Function.update a i z)| ≤ |z' - z| := by
  classical
  let L : Shao.Path N → ℝ := fun a =>
    if hN : 0 < N then
      sSup {w : ℝ | ∃ i : Fin N, ∃ k : Fin (N + 1),
        w = Shao.prefixSum a N - 2 * ∑ r ∈ Finset.range k.val,
          a ⟨(i.val + r) % N, Nat.mod_lt _ hN⟩}
    else 0
  change ∀ (a : Shao.Path N) (i : Fin N) (z z' : ℝ),
    |L (Function.update a i z') - L (Function.update a i z)| ≤ |z' - z|
  intro a i z z'
  have hN : 0 < N := by have hi := i.isLt; omega
  run_tac
    let n := Lean.mkPrivateNameCore ("Shao.Probability.SourceCircularWitnessMoment".toName)
      ("Shao.Probability.SourceCircularWitnessMoment.cwm_circular_arc_prefix_formula".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hArc".toName)) := $(Lean.mkIdent n)
        $(Lean.mkIdent ("N".toName)) $(Lean.mkIdent ("hN".toName))))
  let cand : Shao.Path N → Fin N → Fin (N + 1) → ℝ := fun b j q =>
    Shao.prefixSum b N - 2 * ∑ r ∈ Finset.range q.val,
      b ⟨(j.val + r) % N, Nat.mod_lt _ hN⟩
  have hPS (u v : ℝ) (m : ℕ) :
      Shao.prefixSum (Function.update a i u) m -
        Shao.prefixSum (Function.update a i v) m =
          if i.val < m then u - v else 0 := by
    dsimp only [Shao.prefixSum]
    by_cases him : i.val < m
    · have hi : i ∈ Finset.univ.filter (fun j : Fin N => j.val < m) := by simp [him]
      rw [Finset.sum_update_of_mem hi a u, Finset.sum_update_of_mem hi a v, if_pos him]
      ring
    · have hi : i ∉ Finset.univ.filter (fun j : Fin N => j.val < m) := by simp [him]
      rw [Finset.sum_update_of_notMem hi a u, Finset.sum_update_of_notMem hi a v,
        if_neg him]
      ring
  have hCand (u v : ℝ) (j : Fin N) (q : Fin (N + 1)) :
      |cand (Function.update a i u) j q - cand (Function.update a i v) j q| ≤ |u - v| := by
    have harc :
        ((∑ r ∈ Finset.range q.val,
          (Function.update a i u) ⟨(j.val + r) % N, Nat.mod_lt _ hN⟩) -
          ∑ r ∈ Finset.range q.val,
            (Function.update a i v) ⟨(j.val + r) % N, Nat.mod_lt _ hN⟩) = 0 ∨
        ((∑ r ∈ Finset.range q.val,
          (Function.update a i u) ⟨(j.val + r) % N, Nat.mod_lt _ hN⟩) -
          ∑ r ∈ Finset.range q.val,
            (Function.update a i v) ⟨(j.val + r) % N, Nat.mod_lt _ hN⟩) = u - v := by
      rw [hArc (Function.update a i u) j q, hArc (Function.update a i v) j q]
      split_ifs with hw
      · have he :
            (Shao.prefixSum (Function.update a i u) (j.val + q.val) -
              Shao.prefixSum (Function.update a i u) j.val) -
            (Shao.prefixSum (Function.update a i v) (j.val + q.val) -
              Shao.prefixSum (Function.update a i v) j.val) =
            (Shao.prefixSum (Function.update a i u) (j.val + q.val) -
              Shao.prefixSum (Function.update a i v) (j.val + q.val)) -
            (Shao.prefixSum (Function.update a i u) j.val -
              Shao.prefixSum (Function.update a i v) j.val) := by ring
        rw [he, hPS, hPS]
        split_ifs <;> first | (left; ring; done) | (right; ring; done) | omega
      · have he :
            (Shao.prefixSum (Function.update a i u) N -
              Shao.prefixSum (Function.update a i u) j.val +
              Shao.prefixSum (Function.update a i u) (j.val + q.val - N)) -
            (Shao.prefixSum (Function.update a i v) N -
              Shao.prefixSum (Function.update a i v) j.val +
              Shao.prefixSum (Function.update a i v) (j.val + q.val - N)) =
            (Shao.prefixSum (Function.update a i u) N -
              Shao.prefixSum (Function.update a i v) N) -
            (Shao.prefixSum (Function.update a i u) j.val -
              Shao.prefixSum (Function.update a i v) j.val) +
            (Shao.prefixSum (Function.update a i u) (j.val + q.val - N) -
              Shao.prefixSum (Function.update a i v) (j.val + q.val - N)) := by ring
        rw [he, hPS, hPS, hPS]
        simp only [if_pos i.isLt]
        have hq : q.val ≤ N := Nat.le_of_lt_succ q.isLt
        split_ifs <;> first | (left; ring; done) | (right; ring; done) | omega
    have he : cand (Function.update a i u) j q - cand (Function.update a i v) j q =
        (Shao.prefixSum (Function.update a i u) N -
          Shao.prefixSum (Function.update a i v) N) -
        2 * ((∑ r ∈ Finset.range q.val,
          (Function.update a i u) ⟨(j.val + r) % N, Nat.mod_lt _ hN⟩) -
          ∑ r ∈ Finset.range q.val,
            (Function.update a i v) ⟨(j.val + r) % N, Nat.mod_lt _ hN⟩) := by
      dsimp only [cand]
      ring
    rw [he, hPS]
    simp only [if_pos i.isLt]
    rcases harc with harc | harc
    · rw [harc]
      simp
    · rw [harc]
      have heq : (u - v) - 2 * (u - v) = -(u - v) := by ring
      rw [heq, abs_neg]
  have hLeq (b : Shao.Path N) :
      L b = sSup (Set.range (fun j : Fin N × Fin (N + 1) => cand b j.1 j.2)) := by
    dsimp only [L]
    rw [dif_pos hN]
    congr 1
    ext w
    constructor
    · rintro ⟨j, q, rfl⟩
      exact ⟨(j, q), rfl⟩
    · rintro ⟨⟨j, q⟩, rfl⟩
      exact ⟨j, q, rfl⟩
  have hUpper (u v : ℝ) : L (Function.update a i u) ≤
      L (Function.update a i v) + |u - v| := by
    rw [hLeq (Function.update a i u)]
    apply csSup_le
      (show Set.Nonempty (Set.range (fun j : Fin N × Fin (N + 1) =>
        cand (Function.update a i u) j.1 j.2)) from
          ⟨cand (Function.update a i u) i ⟨0, by omega⟩,
            ⟨(i, ⟨0, by omega⟩), rfl⟩⟩)
    rintro w ⟨⟨j, q⟩, rfl⟩
    have hm : cand (Function.update a i v) j q ≤ L (Function.update a i v) := by
      rw [hLeq (Function.update a i v)]
      exact le_csSup (Set.finite_range _).bddAbove ⟨(j, q), rfl⟩
    have hd := (abs_le.1 (hCand u v j q)).2
    linarith
  apply abs_le.2
  constructor
  · have hh := hUpper z z'
    rw [abs_sub_comm z z'] at hh
    linarith
  · have hh := hUpper z' z
    linarith

private theorem pww_circular_witness_reversal (N : ℕ) :
    let L : Shao.Path N → ℝ := fun a =>
      if hN : 0 < N then
        sSup {w : ℝ | ∃ i : Fin N, ∃ k : Fin (N + 1),
          w = Shao.prefixSum a N -
            2 * ∑ r ∈ Finset.range k.val,
              a ⟨(i.val + r) % N, Nat.mod_lt _ hN⟩}
      else 0
    let rev : Shao.Path N → Shao.Path N := fun a i => a (Fin.rev i)
    ∀ a : Shao.Path N, L (rev a) = L a := by
  classical
  let L : Shao.Path N → ℝ := fun a =>
    if hN : 0 < N then
      sSup {w : ℝ | ∃ i : Fin N, ∃ k : Fin (N + 1),
        w = Shao.prefixSum a N - 2 * ∑ r ∈ Finset.range k.val,
          a ⟨(i.val + r) % N, Nat.mod_lt _ hN⟩}
    else 0
  let rev : Shao.Path N → Shao.Path N := fun a i => a (Fin.rev i)
  change ∀ a : Shao.Path N, L (rev a) = L a
  have hPS (a : Shao.Path N) (m : ℕ) (hm : m ≤ N) :
      Shao.prefixSum (rev a) m = Shao.prefixSum a N - Shao.prefixSum a (N - m) := by
    have heq : (∑ i : Fin N, if i.val < m then a (Fin.rev i) else 0) =
        ∑ i : Fin N, if N - m ≤ i.val then a i else 0 := by
      let f : Fin N → ℝ := fun i => if N - m ≤ i.val then a i else 0
      calc
        _ = ∑ i : Fin N, f (Fin.rev i) := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp only [f]
          have hv : (Fin.rev i).val = N - 1 - i.val := by
            change N - (i.val + 1) = N - 1 - i.val
            omega
          have hi := i.isLt
          have hh : i.val < m ↔ N - m ≤ (Fin.rev i).val := by omega
          simp only [hh]
        _ = ∑ i : Fin N, f i := Equiv.sum_comp Fin.revPerm f
    calc
      Shao.prefixSum (rev a) m =
          ∑ i : Fin N, if i.val < m then a (Fin.rev i) else 0 := by
        simp only [Shao.prefixSum, Finset.sum_filter, rev]
      _ = ∑ i : Fin N, if N - m ≤ i.val then a i else 0 := heq
      _ = (∑ i : Fin N, a i) - ∑ i : Fin N, if i.val < N - m then a i else 0 := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp_all <;> omega
      _ = Shao.prefixSum a N - Shao.prefixSum a (N - m) := by
        rw [Shao.prefixSum_length]
        simp only [Shao.prefixSum, Finset.sum_filter]
  run_tac
    let n := Lean.mkPrivateNameCore ("Shao.Probability.SourceCircularWitnessMoment".toName)
      ("Shao.Probability.SourceCircularWitnessMoment.cwm_path_extrema_geometry".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hGeom".toName)) := $(Lean.mkIdent n) $(Lean.mkIdent ("N".toName))))
  let A : Shao.Path N → ℝ := fun a =>
    sSup {w : ℝ | ∃ u v : Fin (N + 1), u.val ≤ v.val ∧
      w = Shao.prefixSum a v.val - Shao.prefixSum a u.val}
  let R : Shao.Path N → ℝ := fun a =>
    sSup {w : ℝ | ∃ u v : Fin (N + 1), u.val ≤ v.val ∧
      w = Shao.prefixSum a u.val - Shao.prefixSum a v.val}
  change Measurable L ∧ Measurable A ∧ Measurable R ∧
    ∀ a, 0 ≤ L a ∧ L a ≤ ∑ i, |a i| ∧ 0 ≤ A a ∧ A a ≤ ∑ i, |a i| ∧
      0 ≤ R a ∧ R a ≤ ∑ i, |a i| ∧
      L a = max (Shao.prefixSum a N + 2 * R a) (2 * A a - Shao.prefixSum a N) ∧
      R (-a) = A a at hGeom
  intro a
  have hSets (e : ℝ) :
      {w : ℝ | ∃ u v : Fin (N + 1), u.val ≤ v.val ∧
        w = e * (Shao.prefixSum (rev a) v.val - Shao.prefixSum (rev a) u.val)} =
      {w : ℝ | ∃ u v : Fin (N + 1), u.val ≤ v.val ∧
        w = e * (Shao.prefixSum a v.val - Shao.prefixSum a u.val)} := by
    ext w
    constructor
    · rintro ⟨u, v, huv, rfl⟩
      refine ⟨⟨N - v.val, by omega⟩, ⟨N - u.val, by omega⟩, by dsimp only; omega, ?_⟩
      rw [hPS a v.val (by omega), hPS a u.val (by omega)]
      ring
    · rintro ⟨u, v, huv, rfl⟩
      refine ⟨⟨N - v.val, by omega⟩, ⟨N - u.val, by omega⟩, by dsimp only; omega, ?_⟩
      rw [hPS a (N - u.val) (by omega), hPS a (N - v.val) (by omega)]
      have hu : N - (N - u.val) = u.val := by omega
      have hv : N - (N - v.val) = v.val := by omega
      simp only [hu, hv]
      ring
  have hA : A (rev a) = A a := by
    dsimp only [A]
    congr 1
    simpa only [one_mul] using hSets 1
  have hR : R (rev a) = R a := by
    dsimp only [R]
    congr 1
    simpa only [neg_one_mul, neg_sub] using hSets (-1)
  rw [(hGeom.2.2.2 (rev a)).2.2.2.2.2.2.1,
    (hGeom.2.2.2 a).2.2.2.2.2.2.1, hA, hR, hPS a N le_rfl]
  simp

private theorem pww_actual_clipped_wall_statistic
    (k : ℕ) (R B x Q T : ℝ)
    (hR : 0 < R) (hB : 0 ≤ B) (hx : 0 ≤ x)
    (hQ : 0 ≤ Q) (hT : 0 ≤ T)
    (hsmall : 4 * x * B ≤ Real.sqrt R) :
    let clip : ℝ → ℝ := fun z => max (-B) (min z B)
    let F : Shao.Path k → ℝ := fun a =>
      Shao.prefixSum a k -
        x * Real.sqrt (max ((∑ i : Fin k, (clip (a i)) ^ 2) + Q) (R / 2) + T)
    Continuous F ∧
      (∀ (a : Shao.Path k) (i : Fin k) (z z' : ℝ), z ≤ z' →
        (1 / 2 : ℝ) * (z' - z) ≤
          F (Function.update a i z') - F (Function.update a i z) ∧
        F (Function.update a i z') - F (Function.update a i z) ≤
          (3 / 2 : ℝ) * (z' - z)) ∧
      ∀ a : Shao.Path k, (∀ i : Fin k, |a i| ≤ B) →
        R / 2 ≤ Shao.energy a + Q →
        F a = Shao.prefixSum a k - x * Real.sqrt (Shao.energy a + Q + T) := by
  classical
  let clip : ℝ → ℝ := fun z => max (-B) (min z B)
  let F : Shao.Path k → ℝ := fun a =>
    Shao.prefixSum a k -
      x * Real.sqrt (max ((∑ i : Fin k, (clip (a i)) ^ 2) + Q) (R / 2) + T)
  change Continuous F ∧
    (∀ (a : Shao.Path k) (i : Fin k) (z z' : ℝ), z ≤ z' →
      (1 / 2 : ℝ) * (z' - z) ≤
        F (Function.update a i z') - F (Function.update a i z) ∧
      F (Function.update a i z') - F (Function.update a i z) ≤
        (3 / 2 : ℝ) * (z' - z)) ∧
    ∀ a : Shao.Path k, (∀ i : Fin k, |a i| ≤ B) →
      R / 2 ≤ Shao.energy a + Q →
      F a = Shao.prefixSum a k - x * Real.sqrt (Shao.energy a + Q + T)
  have hclipBound (z : ℝ) : |clip z| ≤ B := by
    apply abs_le.2
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hclipLip (z z' : ℝ) : |clip z' - clip z| ≤ |z' - z| := by
    have h1 := abs_min_sub_min_le_max z' B z B
    have h2 := abs_max_sub_max_le_max (-B) (min z' B) (-B) (min z B)
    simp only [sub_self, abs_zero, max_eq_left (abs_nonneg (z' - z))] at h1
    simp only [sub_self, abs_zero,
      max_eq_right (abs_nonneg (min z' B - min z B))] at h2
    exact h2.trans h1
  have hclipSq (z z' : ℝ) : |clip z' ^ 2 - clip z ^ 2| ≤ 2 * B * |z' - z| := by
    have hsum : |clip z' + clip z| ≤ 2 * B :=
      (abs_add_le _ _).trans (by linarith only [hclipBound z', hclipBound z])
    calc
      _ = |clip z' - clip z| * |clip z' + clip z| := by
        rw [← abs_mul]; congr 1; ring
      _ ≤ |z' - z| * (2 * B) :=
        mul_le_mul (hclipLip z z') hsum (abs_nonneg _) (abs_nonneg _)
      _ = _ := by ring
  have hrootLip (C z z' : ℝ) :
      x * |Real.sqrt (max (C + clip z' ^ 2 + Q) (R / 2) + T) -
        Real.sqrt (max (C + clip z ^ 2 + Q) (R / 2) + T)| ≤ |z' - z| / 2 := by
    let U : ℝ := max (C + clip z' ^ 2 + Q) (R / 2) + T
    let V : ℝ := max (C + clip z ^ 2 + Q) (R / 2) + T
    have hUf : R / 2 ≤ U := by
      dsimp [U]; linarith only [le_max_right (C + clip z' ^ 2 + Q) (R / 2), hT]
    have hVf : R / 2 ≤ V := by
      dsimp [V]; linarith only [le_max_right (C + clip z ^ 2 + Q) (R / 2), hT]
    have hUn : 0 ≤ U := by linarith
    have hVn : 0 ≤ V := by linarith
    have hUr : Real.sqrt R / 2 ≤ Real.sqrt U := by
      apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg U)).1
      rw [Real.sq_sqrt hUn]
      nlinarith only [Real.sq_sqrt hR.le, hUf, hR.le]
    have hVr : Real.sqrt R / 2 ≤ Real.sqrt V := by
      apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg V)).1
      rw [Real.sq_sqrt hVn]
      nlinarith only [Real.sq_sqrt hR.le, hVf, hR.le]
    have hr : Real.sqrt R ≤ Real.sqrt U + Real.sqrt V := by linarith
    have hab : |U - V| ≤ |clip z' ^ 2 - clip z ^ 2| := by
      have hd : (C + clip z' ^ 2 + Q) - (C + clip z ^ 2 + Q) =
          clip z' ^ 2 - clip z ^ 2 := by ring
      calc
        _ = |max (C + clip z' ^ 2 + Q) (R / 2) -
            max (C + clip z ^ 2 + Q) (R / 2)| := by
          dsimp [U, V]; congr 1; ring
        _ ≤ max |(C + clip z' ^ 2 + Q) - (C + clip z ^ 2 + Q)|
            |R / 2 - R / 2| :=
          abs_max_sub_max_le_max _ _ _ _
        _ = _ := by
          simp only [hd, sub_self, abs_zero,
            max_eq_left (abs_nonneg (clip z' ^ 2 - clip z ^ 2))]
    have hprod : |Real.sqrt U - Real.sqrt V| * (Real.sqrt U + Real.sqrt V) =
        |U - V| := by
      rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg U) (Real.sqrt_nonneg V)),
        ← abs_mul]
      congr 1
      nlinarith only [Real.sq_sqrt hUn, Real.sq_sqrt hVn]
    have hmul : (x * |Real.sqrt U - Real.sqrt V|) * Real.sqrt R ≤
        (|z' - z| / 2) * Real.sqrt R := by
      calc
        _ = x * (|Real.sqrt U - Real.sqrt V| * Real.sqrt R) := by ring
        _ ≤ x * (|Real.sqrt U - Real.sqrt V| * (Real.sqrt U + Real.sqrt V)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hr (abs_nonneg _)) hx
        _ = x * |U - V| := by rw [hprod]
        _ ≤ x * (2 * B * |z' - z|) :=
          mul_le_mul_of_nonneg_left (hab.trans (hclipSq z z')) hx
        _ = (4 * x * B) * |z' - z| / 2 := by ring
        _ ≤ Real.sqrt R * |z' - z| / 2 :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hsmall (abs_nonneg _)) (by norm_num)
        _ = _ := by ring
    apply (mul_le_mul_iff_right₀ (Real.sqrt_pos.2 hR)).1
    simpa only [mul_comm (Real.sqrt R)] using hmul
  refine ⟨?_, ?_, ?_⟩
  · have hCF : Continuous (fun a : Shao.Path k =>
        max ((∑ i : Fin k, (clip (a i)) ^ 2) + Q) (R / 2) + T) := by
      dsimp [clip]
      fun_prop
    exact (Shao.continuous_prefixSum k).sub
      (continuous_const.mul (Real.continuous_sqrt.comp hCF))
  · intro a i z z' hzz
    have hsum (g : ℝ → ℝ) (v : ℝ) :
        (∑ j : Fin k, g (Function.update a i v j)) =
          (∑ j ∈ (Finset.univ : Finset (Fin k)).erase i, g (a j)) + g v := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      · simp
    have hS (v : ℝ) : Shao.prefixSum (Function.update a i v) k =
        (∑ j ∈ (Finset.univ : Finset (Fin k)).erase i, a j) + v := by
      simpa only [id_eq, Shao.prefixSum_length] using hsum id v
    have hK (v : ℝ) : (∑ j : Fin k, clip (Function.update a i v j) ^ 2) =
        (∑ j ∈ (Finset.univ : Finset (Fin k)).erase i, clip (a j) ^ 2) + clip v ^ 2 :=
      hsum (fun u => clip u ^ 2) v
    let C : ℝ := ∑ j ∈ (Finset.univ : Finset (Fin k)).erase i, clip (a j) ^ 2
    have hh := hrootLip C z z'
    have hd : |x * (Real.sqrt (max (C + clip z' ^ 2 + Q) (R / 2) + T) -
        Real.sqrt (max (C + clip z ^ 2 + Q) (R / 2) + T))| ≤ (z' - z) / 2 := by
      rw [abs_mul, abs_of_nonneg hx]
      simpa only [abs_of_nonneg (sub_nonneg.2 hzz)] using hh
    have he : F (Function.update a i z') - F (Function.update a i z) =
        (z' - z) - x * (Real.sqrt (max (C + clip z' ^ 2 + Q) (R / 2) + T) -
          Real.sqrt (max (C + clip z ^ 2 + Q) (R / 2) + T)) := by
      dsimp only [F]
      rw [hS z', hS z, hK z', hK z]
      dsimp only [C]
      ring
    rw [he]
    rcases abs_le.1 hd with ⟨hd1, hd2⟩
    constructor <;> linarith
  · intro a ha hg
    have hc (i : Fin k) : clip (a i) = a i := by
      have hi := abs_le.1 (ha i)
      dsimp only [clip]
      rw [min_eq_left hi.2, max_eq_right hi.1]
    have hs : (∑ i : Fin k, clip (a i) ^ 2) = Shao.energy a := by
      simp only [hc, Shao.energy]
    dsimp only [F]
    rw [hs, max_eq_left hg]

private theorem pww_weighted_survival_first_hit_tail :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (B : ℝ), 0 < B → (∀ᵐ z : ℝ ∂rho, |z| ≤ B) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ (N : ℕ), 0 < N →
          let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => rho)
          let L : Shao.Path N → ℝ := fun a =>
            if hN : 0 < N then
              sSup {w : ℝ | ∃ i : Fin N, ∃ k : Fin (N + 1),
                w = Shao.prefixSum a N -
                  2 * ∑ r ∈ Finset.range k.val,
                    a ⟨(i.val + r) % N, Nat.mod_lt _ hN⟩}
            else 0
          ∀ theta b : ℝ, 0 < theta → theta * B ≤ 1 / 100 → 0 ≤ b →
            let Alive : Set (Shao.Path N) := {a | ∀ k : Fin (N + 1), -b ≤ Shao.prefixSum a k.val}
            let lam : ℝ := (1001 / 997 : ℝ) * theta
            let u0 : ℝ := Real.sqrt (N : ℝ) + 10 * (B + b)
            ∀ u : ℝ, u0 ≤ u →
              P.real (Alive ∩ {a | u < L a}) ≤
                C * (b + beta) / u * (1 + (N : ℝ) * lam ^ 2) *
                  Real.exp ((1002001 / 2000000 : ℝ) * (N : ℝ) * lam ^ 2 +
                    C * (N : ℝ) * lam ^ 3 * beta + lam * (3 * B + 2 * b) -
                    (1001 / 1000 : ℝ) * theta * u) := by
  classical
  obtain ⟨CH, hCH, hHit⟩ := pww_fixed_level_hit_before_lower_exit
  obtain ⟨CM, hCM, hMom⟩ :=
    Shao.Probability.SourceCircularWitnessMoment.actual_circular_witness_small_parameter_moment
  let C : ℝ := max 1 (max (1000 * CH * CM) CM)
  have hC : 1 ≤ C := le_max_left _ _
  have hCOuter : 1000 * CH * CM ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCMajor : CM ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro rho hprob B hB hs hmean hvar beta N hN P L theta b htp hsmall hb Alive lam u0 u huBound
  have ht : 0 ≤ theta := htp.le
  have hbeta : 0 ≤ beta := integral_nonneg (fun z => pow_nonneg (abs_nonneg z) 3)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNr
  have hlamp : 0 < lam := mul_pos (by norm_num) htp
  have hlamB : lam * B ≤ 1 / 10 := by
    dsimp only [lam]
    nlinarith only [hsmall]
  have hlamTheta : theta ≤ lam := by
    dsimp only [lam]
    nlinarith only [ht]
  have hu0 : 0 < u0 := by dsimp only [u0]; positivity
  have hu0sqrt : Real.sqrt (N : ℝ) ≤ u0 := by
    dsimp only [u0]
    nlinarith only [hB, hb]
  let Major : ℝ := CM * (1 + (N : ℝ) * lam ^ 2) *
    Real.exp ((1002001 / 2000000 : ℝ) * (N : ℝ) * lam ^ 2 +
      CM * (N : ℝ) * lam ^ 3 * beta)
  have hMajor : 0 < Major := by dsimp only [Major]; positivity
  have hMomSuffix (j : ℕ) (hj : j ≤ N) :
      let Q : Measure (Shao.Path j) := Measure.pi (fun _ : Fin j => rho)
      let Lj : Shao.Path j → ℝ := fun a =>
        if hp : 0 < j then
          sSup {w : ℝ | ∃ i : Fin j, ∃ k : Fin (j + 1),
            w = Shao.prefixSum a j - 2 * ∑ r ∈ Finset.range k.val,
              a ⟨(i.val + r) % j, Nat.mod_lt _ hp⟩}
        else 0
      Integrable (fun a => Real.exp (lam * Lj a)) Q ∧
        (∫ a, Real.exp (lam * Lj a) ∂Q) ≤ Major := by
    intro Q Lj
    have hh := (hMom rho B hB hs hmean hvar j).2 lam hlamp.le hlamB
    refine ⟨hh.1, hh.2.trans ?_⟩
    have hlen : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hj
    have hfirst : CM * (1 + (j : ℝ) * lam ^ 2) ≤ CM * (1 + (N : ℝ) * lam ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith only [hCM])
      nlinarith only [hlen, sq_nonneg lam]
    have hpoly : 0 ≤ (1002001 / 2000000 : ℝ) * lam ^ 2 + CM * lam ^ 3 * beta := by positivity
    have htimes := mul_le_mul_of_nonneg_right hlen hpoly
    have he : Real.exp ((1002001 / 2000000 : ℝ) * (j : ℝ) * lam ^ 2 + CM * (j : ℝ) * lam ^ 3 * beta) ≤
        Real.exp ((1002001 / 2000000 : ℝ) * (N : ℝ) * lam ^ 2 + CM * (N : ℝ) * lam ^ 3 * beta) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [htimes]
    exact mul_le_mul hfirst he (Real.exp_pos _).le (by positivity)
  have hTail : P.real (Alive ∩ {a | u < L a}) ≤
      1000 * CH * (b + beta) / u * Major *
        Real.exp (lam * (3 * B + 2 * b) - (1001 / 1000 : ℝ) * theta * u) := by
    let LL : (j : ℕ) → Shao.Path j → ℝ := fun j a =>
      if hp : 0 < j then
        sSup {w : ℝ | ∃ i : Fin j, ∃ k : Fin (j + 1),
          w = Shao.prefixSum a j - 2 * ∑ r ∈ Finset.range k.val,
            a ⟨(i.val + r) % j, Nat.mod_lt _ hp⟩}
      else 0
    run_tac
      let n := Lean.mkPrivateNameCore ("Shao.Probability.SourceCircularWitnessMoment".toName)
        ("Shao.Probability.SourceCircularWitnessMoment.cwm_path_extrema_geometry".toName)
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        have $(Lean.mkIdent ("hGeom".toName)) := $(Lean.mkIdent n)))
    have hRange (j : ℕ) (a : Shao.Path j) (lo hi d : ℝ)
        (hAll : ∀ i : Fin (j + 1), lo ≤ Shao.prefixSum a i.val ∧ Shao.prefixSum a i.val ≤ hi)
        (hEnd : d ≤ Shao.prefixSum a j) :
        LL j a ≤ max (3 * hi - 2 * lo) (2 * hi - 2 * lo - d) := by
      let AA : ℝ := sSup {w : ℝ | ∃ p q : Fin (j + 1), p.val ≤ q.val ∧
        w = Shao.prefixSum a q.val - Shao.prefixSum a p.val}
      let RR : ℝ := sSup {w : ℝ | ∃ p q : Fin (j + 1), p.val ≤ q.val ∧
        w = Shao.prefixSum a p.val - Shao.prefixSum a q.val}
      have hAA : AA ≤ hi - lo := by
        apply csSup_le
        · exact ⟨0, ⟨⟨0, by omega⟩, ⟨0, by omega⟩, le_rfl, by simp⟩⟩
        · rintro w ⟨p, q, _, rfl⟩
          linarith only [(hAll p).1, (hAll q).2]
      have hRR : RR ≤ hi - lo := by
        apply csSup_le
        · exact ⟨0, ⟨⟨0, by omega⟩, ⟨0, by omega⟩, le_rfl, by simp⟩⟩
        · rintro w ⟨p, q, _, rfl⟩
          linarith only [(hAll p).2, (hAll q).1]
      have hG : LL j a = max (Shao.prefixSum a j + 2 * RR)
          (2 * AA - Shao.prefixSum a j) := (hGeom j).2.2.2 a |>.2.2.2.2.2.2.1
      rw [hG]
      apply max_le_max
      · have htop := (hAll ⟨j, by omega⟩).2
        dsimp only at htop
        linarith only [htop, hRR]
      · linarith only [hAA, hEnd]
    have hu : 0 < u := hu0.trans_le huBound
    let c : ℝ := u / 1000
    have hc : 0 < c := by dsimp only [c]; positivity
    have hbU : 10 * b ≤ u := by
      have hUBound : Real.sqrt (N : ℝ) + 10 * (B + b) ≤ u := huBound
      linarith only [hUBound, Real.sqrt_nonneg (N : ℝ), hB]
    have hExistsHit (a : Shao.Path N) (hA : a ∈ Alive) (hLu : u < L a) :
        ∃ j : Fin (N + 1), c ≤ Shao.prefixSum a j.val := by
      by_contra hh
      push_neg at hh
      have hR := hRange N a (-b) c (-b)
        (fun j => ⟨hA j, le_of_lt (hh j)⟩) (hA ⟨N, by omega⟩)
      change L a ≤ max (3 * c - 2 * -b) (2 * c - 2 * -b - -b) at hR
      have htop : max (3 * c - 2 * -b) (2 * c - 2 * -b - -b) < u := by
        apply max_lt
        · dsimp only [c]
          linarith only [hu, hbU]
        · dsimp only [c]
          linarith only [hu, hbU]
      exact (not_lt_of_ge (hR.trans htop.le)) hLu
    let E : Fin (N + 1) → Set (Shao.Path N) := fun j => {a |
      c ≤ Shao.prefixSum a j.val ∧
      (∀ i : Fin (N + 1), i.val < j.val → Shao.prefixSum a i.val < c) ∧
      ∀ i : Fin (N + 1), i.val ≤ j.val → -b ≤ Shao.prefixSum a i.val}
    have hPSNm (q : ℕ) : Measurable (fun a : Shao.Path N => Shao.prefixSum a q) :=
      (Shao.continuous_prefixSum q).measurable
    have hEm (j : Fin (N + 1)) : MeasurableSet (E j) := by
      change MeasurableSet ({a : Shao.Path N | c ≤ Shao.prefixSum a j.val} ∩
        ({a | ∀ i : Fin (N + 1), i.val < j.val → Shao.prefixSum a i.val < c} ∩
         {a | ∀ i : Fin (N + 1), i.val ≤ j.val → -b ≤ Shao.prefixSum a i.val}))
      refine (measurableSet_le (measurable_const (a := c)) (hPSNm j.val)).inter ?_
      apply MeasurableSet.inter
      · simp only [Set.setOf_forall]
        exact MeasurableSet.iInter fun i : Fin (N + 1) =>
          MeasurableSet.iInter fun _ : i.val < j.val =>
            measurableSet_lt (hPSNm i.val) (measurable_const (a := c))
      · simp only [Set.setOf_forall]
        exact MeasurableSet.iInter fun i : Fin (N + 1) =>
          MeasurableSet.iInter fun _ : i.val ≤ j.val =>
            measurableSet_le (measurable_const (a := -b)) (hPSNm i.val)
    have hDisj (i j : Fin (N + 1)) (hij : i ≠ j) : Disjoint (E i) (E j) := by
      apply Set.disjoint_left.2
      rintro a hi hj
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
      · exact (not_lt_of_ge hi.1) (hj.2.1 i h)
      · exact (not_lt_of_ge hj.1) (hi.2.1 j h)
    have hChoose (a : Shao.Path N) (ha : a ∈ Alive) (hLu : u < L a) :
        ∃ j : Fin (N + 1), a ∈ E j := by
      obtain ⟨j, hj⟩ := hExistsHit a ha hLu
      have hex : ∃ q : ℕ, q ≤ N ∧ c ≤ Shao.prefixSum a q := ⟨j.val, by omega, hj⟩
      let q := Nat.find hex
      have hq : q ≤ N ∧ c ≤ Shao.prefixSum a q := Nat.find_spec hex
      refine ⟨⟨q, by omega⟩, hq.2, ?_, fun i _ => ha i⟩
      intro i hi
      by_contra hn
      exact Nat.find_min hex hi ⟨by omega, le_of_not_gt hn⟩
    have hBox : ∀ᵐ a : Shao.Path N ∂P, ∀ i : Fin N, |a i| ≤ B := by
      apply ae_all_iff.2
      intro i
      exact (measurePreserving_eval (fun _ : Fin N => rho) i).quasiMeasurePreserving.ae hs
    have hPSucc (a : Shao.Path N) (k : ℕ) (hk : k < N) :
        Shao.prefixSum a (k + 1) = Shao.prefixSum a k + a ⟨k, hk⟩ := by
      have hset : Finset.univ.filter (fun i : Fin N => i.val < k + 1) =
          insert ⟨k, hk⟩ (Finset.univ.filter (fun i : Fin N => i.val < k)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hi
          by_cases he : i.val = k
          · left
            exact Fin.ext he
          · right
            omega
        · rintro (rfl | hi)
          · exact Nat.lt_succ_self _
          · omega
      have hnot : (⟨k, hk⟩ : Fin N) ∉ Finset.univ.filter (fun i : Fin N => i.val < k) := by simp
      dsimp only [Shao.prefixSum]
      rw [hset, Finset.sum_insert hnot]
      ring
    have hPrefixRange (a : Shao.Path N) (ha : ∀ i : Fin N, |a i| ≤ B)
        (j : Fin (N + 1)) (hj : a ∈ E j) :
        (∀ i : Fin (N + 1), i.val ≤ j.val →
          -b ≤ Shao.prefixSum a i.val ∧ Shao.prefixSum a i.val ≤ c + B) ∧
        c ≤ Shao.prefixSum a j.val := by
      have hjp : 0 < j.val := by
        by_contra hn
        have hz : j.val = 0 := by omega
        have hh := hj.1
        rw [hz, Shao.prefixSum_zero] at hh
        linarith only [hc, hh]
      have hjpred : j.val - 1 < N := by omega
      have hpred := hj.2.1 ⟨j.val - 1, by omega⟩ (by dsimp only; omega)
      have hEnd : Shao.prefixSum a j.val ≤ c + B := by
        have he := hPSucc a (j.val - 1) hjpred
        have hnat : j.val - 1 + 1 = j.val := by omega
        rw [hnat] at he
        have hcoord : a ⟨j.val - 1, hjpred⟩ ≤ B :=
          (le_abs_self _).trans (ha _)
        dsimp only at hpred
        linarith only [he, hpred, hcoord]
      refine ⟨?_, hj.1⟩
      intro i hi
      refine ⟨hj.2.2 i hi, ?_⟩
      by_cases he : i.val = j.val
      · simpa only [he] using hEnd
      · have hh := hj.2.1 i (by omega)
        linarith only [hh, hB]
    have hSumE : (∑ j : Fin (N + 1), P.real (E j)) ≤ CH * (b + beta) / c := by
      rw [← measureReal_iUnion_fintype hDisj hEm]
      have hIncl : (⋃ j : Fin (N + 1), E j) ⊆
          {a : Shao.Path N | ∃ k : Fin (N + 1), 0 < k.val ∧ c ≤ Shao.prefixSum a k.val ∧
            ∀ i : Fin (N + 1), i.val ≤ k.val → -b ≤ Shao.prefixSum a i.val} := by
        intro a ha
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ha
        have hjp : 0 < j.val := by
          by_contra hn
          have hz : j.val = 0 := by omega
          have hh := hj.1
          rw [hz, Shao.prefixSum_zero] at hh
          linarith only [hc, hh]
        exact ⟨j, hjp, hj.1, hj.2.2⟩
      exact (measureReal_mono hIncl).trans (hHit rho B hB hs hmean hvar N b c hb hc)
    have hFutureTail (j : ℕ) (hj : j ≤ N) (d : ℝ) :
        let Q : Measure (Shao.Path j) := Measure.pi (fun _ : Fin j => rho)
        Q.real {a | d < LL j a} ≤ Major * Real.exp (-(lam * d)) := by
      intro Q
      have hMj := hMomSuffix j hj
      change Integrable (fun a => Real.exp (lam * LL j a)) Q ∧
        (∫ a, Real.exp (lam * LL j a) ∂Q) ≤ Major at hMj
      have hLm : Measurable (LL j) := (hMom rho B hB hs hmean hvar j).1
      let F : Set (Shao.Path j) := {a | d < LL j a}
      have hFm : MeasurableSet F := measurableSet_lt measurable_const hLm
      have hMarkov : Real.exp (lam * d) * Q.real F ≤
          ∫ a, Real.exp (lam * LL j a) ∂Q := by
        calc
          _ = ∫ a, F.indicator (fun _ => Real.exp (lam * d)) a ∂Q := by
            rw [integral_indicator hFm, setIntegral_const]
            simp only [smul_eq_mul, mul_comm]
          _ ≤ _ := by
            apply integral_mono ((integrable_const _).indicator hFm) hMj.1
            intro a
            by_cases ha : a ∈ F
            · rw [Set.indicator_of_mem ha]
              exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ha.le hlamp.le)
            · rw [Set.indicator_of_notMem ha]
              exact (Real.exp_pos _).le
      calc
        Q.real F ≤ Major / Real.exp (lam * d) :=
          (le_div_iff₀ (Real.exp_pos _)).2 (by nlinarith only [hMarkov, hMj.2])
        _ = Major * Real.exp (-(lam * d)) := by rw [Real.exp_neg, div_eq_mul_inv]
    let d : ℝ := (997 / 1000 : ℝ) * u - 3 * B - 2 * b
    have hEach (j : Fin (N + 1)) :
        P.real (E j ∩ {a | u < L a}) ≤
          P.real (E j) * Major * Real.exp (-(lam * d)) := by
      rcases j with ⟨k, hk⟩
      obtain ⟨l, hlen⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt_succ hk)
      subst N
      let j : Fin (k + l + 1) := ⟨k, hk⟩
      change P.real (E j ∩ {a | u < L a}) ≤ P.real (E j) * Major * Real.exp (-(lam * d))
      let W1 : Shao.Path (k + l) → Shao.Path k := fun a i => a ⟨i.val, by omega⟩
      let W2 : Shao.Path (k + l) → Shao.Path l := fun a i => a ⟨k + i.val, by omega⟩
      let Ql : Measure (Shao.Path l) := Measure.pi (fun _ : Fin l => rho)
      let F : Set (Shao.Path k) := {a | c ≤ Shao.prefixSum a k ∧
        (∀ i : Fin (k + 1), i.val < k → Shao.prefixSum a i.val < c) ∧
        ∀ i : Fin (k + 1), i.val ≤ k → -b ≤ Shao.prefixSum a i.val}
      let Fut : Set (Shao.Path l) := {a | d < LL l a}
      have hPSkm (q : ℕ) : Measurable (fun a : Shao.Path k => Shao.prefixSum a q) :=
        (Shao.continuous_prefixSum q).measurable
      have hFm : MeasurableSet F := by
        change MeasurableSet ({a : Shao.Path k | c ≤ Shao.prefixSum a k} ∩
          ({a | ∀ i : Fin (k + 1), i.val < k → Shao.prefixSum a i.val < c} ∩
           {a | ∀ i : Fin (k + 1), i.val ≤ k → -b ≤ Shao.prefixSum a i.val}))
        refine (measurableSet_le (measurable_const (a := c)) (hPSkm k)).inter ?_
        apply MeasurableSet.inter
        · simp only [Set.setOf_forall]
          exact MeasurableSet.iInter fun i : Fin (k + 1) =>
            MeasurableSet.iInter fun _ : i.val < k =>
              measurableSet_lt (hPSkm i.val) (measurable_const (a := c))
        · simp only [Set.setOf_forall]
          exact MeasurableSet.iInter fun i : Fin (k + 1) =>
            MeasurableSet.iInter fun _ : i.val ≤ k =>
              measurableSet_le (measurable_const (a := -b)) (hPSkm i.val)
      have hFutm : MeasurableSet Fut :=
        measurableSet_lt measurable_const (hMom rho B hB hs hmean hvar l).1
      have hW1m : Measurable W1 := Measurable.of_eval (fun _ => measurable_pi_apply _)
      have hW2m : Measurable W2 := Measurable.of_eval (fun _ => measurable_pi_apply _)
      run_tac
        let n := Lean.mkPrivateNameCore ("Shao.Probability.SourceCircularWitnessMoment".toName)
          ("Shao.Probability.SourceCircularWitnessMoment.cwm_iid_adjacent_windows".toName)
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          have $(Lean.mkIdent ("hWindows".toName)) := $(Lean.mkIdent n)))
      have hh0 := hWindows rho (k + l) 0 k (Nat.zero_le _) (by omega)
      dsimp only at hh0
      simp only [Nat.zero_add, Nat.sub_zero] at hh0
      let V2 : Shao.Path (k + l) → Shao.Path (k + l - k) := fun a i =>
        a ⟨k + i.val, by have hi := i.isLt; omega⟩
      have hV2m : Measurable V2 := Measurable.of_eval (fun _ => measurable_pi_apply _)
      have hNativeMap : P.map V2 = Measure.pi (fun _ : Fin (k + l - k) => rho) := by
        simpa only [P, V2] using hh0.2.1
      have hNativeInd : IndepFun W1 V2 P := by
        simpa only [P, W1, V2] using hh0.2.2.1
      have hPS1 (a : Shao.Path (k + l)) (q : ℕ) (hq : q ≤ k) :
          Shao.prefixSum (W1 a) q = Shao.prefixSum a q := by
        simpa only [W1, Shao.prefixSum_zero, sub_zero] using (hh0.2.2.2 a).1 q hq
      let e : Shao.Path (k + l - k) ≃ᵐ Shao.Path l :=
        MeasurableEquiv.piCongrLeft (fun _ : Fin l => ℝ)
          (finCongr (Nat.add_sub_cancel_left k l))
      have he : MeasurePreserving e (Measure.pi (fun _ : Fin (k + l - k) => rho)) Ql :=
        measurePreserving_piCongrLeft (fun _ : Fin l => rho) (finCongr (Nat.add_sub_cancel_left k l))
      have hcomp : (fun a => e (V2 a)) = W2 := by
        funext a i
        dsimp only [e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft]
        change a ⟨k + i.val, _⟩ = a ⟨k + i.val, _⟩
        rfl
      have hMap2 : P.map W2 = Ql := by
        rw [← hcomp]
        change P.map (e ∘ V2) = Ql
        rw [← Measure.map_map e.measurable hV2m, hNativeMap]
        exact he.map_eq
      have hInd : IndepFun W1 W2 P := by
        have ht := hNativeInd.comp measurable_id e.measurable
        change IndepFun W1 (fun a => e (V2 a)) P at ht
        rwa [hcomp] at ht
      have hE : W1 ⁻¹' F = E j := by
        ext a
        change (c ≤ Shao.prefixSum (W1 a) k ∧
          (∀ i : Fin (k + 1), i.val < k → Shao.prefixSum (W1 a) i.val < c) ∧
          ∀ i : Fin (k + 1), i.val ≤ k → -b ≤ Shao.prefixSum (W1 a) i.val) ↔ _
        rw [hPS1 a k le_rfl]
        constructor
        · rintro ⟨h1, h2, h3⟩
          refine ⟨h1, ?_, ?_⟩
          · intro i hi
            change i.val < k at hi
            have ht := h2 ⟨i.val, by omega⟩ hi
            rwa [hPS1 a i.val (by omega)] at ht
          · intro i hi
            change i.val ≤ k at hi
            have ht := h3 ⟨i.val, by omega⟩ hi
            rwa [hPS1 a i.val hi] at ht
        · rintro ⟨h1, h2, h3⟩
          refine ⟨h1, ?_, ?_⟩
          · intro i hi
            rw [hPS1 a i.val (by omega)]
            exact h2 ⟨i.val, by omega⟩ hi
          · intro i hi
            rw [hPS1 a i.val hi]
            exact h3 ⟨i.val, by omega⟩ hi
      have hCat (a : Shao.Path (k + l)) : L a ≤ LL k (W1 a) + LL l (W2 a) := by
        have ht := pww_circular_witness_concatenation k l (W1 a) (W2 a)
        change L (fun i => if hi : i.val < k then (W1 a) ⟨i.val, hi⟩
          else (W2 a) ⟨i.val - k, by omega⟩) ≤ LL k (W1 a) + LL l (W2 a) at ht
        have heq : (fun i : Fin (k + l) => if hi : i.val < k then (W1 a) ⟨i.val, hi⟩
            else (W2 a) ⟨i.val - k, by omega⟩) = a := by
          funext i
          split_ifs with hi
          · rfl
          · dsimp only [W2]
            congr 1
            apply Fin.ext
            dsimp only
            omega
        rwa [heq] at ht
      have hPreL (a : Shao.Path (k + l)) (ha : ∀ i : Fin (k + l), |a i| ≤ B) (hEa : a ∈ E j) :
          LL k (W1 a) ≤ 3 * c + 3 * B + 2 * b := by
        have hPR := hPrefixRange a ha j hEa
        have ht := hRange k (W1 a) (-b) (c + B) c
          (fun i => by
            rw [hPS1 a i.val (by omega)]
            exact hPR.1 ⟨i.val, by omega⟩ (by dsimp only [j]; omega))
          (by rw [hPS1 a k le_rfl]; exact hEa.1)
        apply ht.trans
        apply max_le <;> linarith only [hc, hB]
      have hDom : P (E j ∩ {a | u < L a}) ≤ P (E j ∩ W2 ⁻¹' Fut) := by
        apply measure_mono_ae
        filter_upwards [hBox] with a ha
        rintro ⟨hEa, hLu⟩
        refine ⟨hEa, ?_⟩
        change d < LL l (W2 a)
        have hcat := hCat a
        have hpre := hPreL a ha hEa
        change u < L a at hLu
        dsimp only [c] at hpre
        dsimp only [d, c]
        linarith only [hcat, hpre, hLu]
      have hFact : P.real (E j ∩ W2 ⁻¹' Fut) = P.real (E j) * Ql.real Fut := by
        have ht := hInd.measure_inter_preimage_eq_mul F Fut hFm hFutm
        apply_fun ENNReal.toReal at ht
        simp only [ENNReal.toReal_mul] at ht
        change P.real (W1 ⁻¹' F ∩ W2 ⁻¹' Fut) = P.real (W1 ⁻¹' F) * P.real (W2 ⁻¹' Fut) at ht
        have hmap : P.real (W2 ⁻¹' Fut) = Ql.real Fut := by
          rw [← hMap2]
          simp only [Measure.real_def, Measure.map_apply hW2m hFutm]
        rwa [hE, hmap] at ht
      calc
        _ ≤ P.real (E j ∩ W2 ⁻¹' Fut) := ENNReal.toReal_mono (measure_ne_top _ _) hDom
        _ = P.real (E j) * Ql.real Fut := hFact
        _ ≤ P.real (E j) * (Major * Real.exp (-(lam * d))) :=
          mul_le_mul_of_nonneg_left (hFutureTail l (by omega) d) measureReal_nonneg
        _ = _ := by ring
    have hExp : -(lam * d) = lam * (3 * B + 2 * b) - (1001 / 1000 : ℝ) * theta * u := by
      dsimp only [lam, d]
      ring
    calc
      _ ≤ P.real (⋃ j : Fin (N + 1), E j ∩ {a | u < L a}) := by
        apply measureReal_mono (μ := P) (h₂ := measure_ne_top _ _)
        rintro a ⟨ha, hLu⟩
        obtain ⟨j, hj⟩ := hChoose a ha hLu
        exact Set.mem_iUnion.mpr ⟨j, hj, hLu⟩
      _ ≤ ∑ j : Fin (N + 1), P.real (E j ∩ {a | u < L a}) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ j : Fin (N + 1), P.real (E j) * Major * Real.exp (-(lam * d)) :=
        Finset.sum_le_sum (fun j _ => hEach j)
      _ = (∑ j : Fin (N + 1), P.real (E j)) * Major * Real.exp (-(lam * d)) := by
        rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ CH * (b + beta) / c * Major * Real.exp (-(lam * d)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSumE hMajor.le) (Real.exp_pos _).le
      _ = _ := by
        rw [hExp]
        dsimp only [c]
        field_simp [hu.ne']
        <;> ring
  have huPos : 0 < u := hu0.trans_le huBound
  have hpoly : 0 ≤ (b + beta) / u * (1 + (N : ℝ) * lam ^ 2) := by positivity
  have hfirst : (1000 * CH * CM) * ((b + beta) / u * (1 + (N : ℝ) * lam ^ 2)) ≤
      C * ((b + beta) / u * (1 + (N : ℝ) * lam ^ 2)) :=
    mul_le_mul_of_nonneg_right hCOuter hpoly
  have he : Real.exp ((1002001 / 2000000 : ℝ) * (N : ℝ) * lam ^ 2 +
      CM * (N : ℝ) * lam ^ 3 * beta + lam * (3 * B + 2 * b) -
      (1001 / 1000 : ℝ) * theta * u) ≤
      Real.exp ((1002001 / 2000000 : ℝ) * (N : ℝ) * lam ^ 2 +
      C * (N : ℝ) * lam ^ 3 * beta + lam * (3 * B + 2 * b) -
      (1001 / 1000 : ℝ) * theta * u) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hCMajor
      (show 0 ≤ (N : ℝ) * lam ^ 3 * beta by positivity)
    nlinarith only [hh]
  calc
    _ ≤ 1000 * CH * (b + beta) / u * Major *
        Real.exp (lam * (3 * B + 2 * b) - (1001 / 1000 : ℝ) * theta * u) := hTail
    _ = (1000 * CH * CM) * ((b + beta) / u * (1 + (N : ℝ) * lam ^ 2)) *
        Real.exp ((1002001 / 2000000 : ℝ) * (N : ℝ) * lam ^ 2 +
          CM * (N : ℝ) * lam ^ 3 * beta + lam * (3 * B + 2 * b) -
          (1001 / 1000 : ℝ) * theta * u) := by
      dsimp only [Major]
      simp only [Real.exp_add, Real.exp_sub]
      ring
    _ ≤ C * ((b + beta) / u * (1 + (N : ℝ) * lam ^ 2)) *
        Real.exp ((1002001 / 2000000 : ℝ) * (N : ℝ) * lam ^ 2 +
          C * (N : ℝ) * lam ^ 3 * beta + lam * (3 * B + 2 * b) -
          (1001 / 1000 : ℝ) * theta * u) :=
      mul_le_mul hfirst he (Real.exp_pos _).le (mul_nonneg (le_trans zero_le_one hC) hpoly)
    _ = _ := by ring

private theorem pww_weighted_closed_lower_survival :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (B : ℝ), 0 < B → (∀ᵐ z : ℝ ∂rho, |z| ≤ B) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ (N : ℕ), 0 < N →
          let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => rho)
          let L : Shao.Path N → ℝ := fun a =>
            if hN : 0 < N then
              sSup {w : ℝ | ∃ i : Fin N, ∃ k : Fin (N + 1),
                w = Shao.prefixSum a N -
                  2 * ∑ r ∈ Finset.range k.val,
                    a ⟨(i.val + r) % N, Nat.mod_lt _ hN⟩}
            else 0
          ∀ theta b : ℝ, 0 ≤ theta → theta * B ≤ 1 / 100 → 0 ≤ b →
            Integrable
              (fun a : Shao.Path N =>
                {v : Shao.Path N | ∀ k : Fin (N + 1),
                  -b ≤ Shao.prefixSum v k.val}.indicator
                    (fun v => Real.exp (theta * L v)) a) P ∧
              (∫ a : Shao.Path N,
                {v : Shao.Path N | ∀ k : Fin (N + 1),
                  -b ≤ Shao.prefixSum v k.val}.indicator
                    (fun v => Real.exp (theta * L v)) a ∂P) ≤
                C * (b + beta) / Real.sqrt (N : ℝ) *
                  (1 + (N : ℝ) * theta ^ 2) *
                  Real.exp ((253 / 500 : ℝ) * (N : ℝ) * theta ^ 2 +
                    C * (N : ℝ) * theta ^ 3 * beta + C * theta * (B + b)) := by
  classical
  obtain ⟨C0, hC0, hOS⟩ := pww_ordinary_closed_lower_survival
  obtain ⟨CT, hCT, hWT⟩ := pww_weighted_survival_first_hit_tail
  obtain ⟨CM, hCM, hMom⟩ :=
    Shao.Probability.SourceCircularWitnessMoment.actual_circular_witness_small_parameter_moment
  let C : ℝ := 20 + 4008 * CT + (1 + Real.exp 1) * C0
  have hC0nn : 0 ≤ C0 := le_trans zero_le_one hC0
  have hCTnn : 0 ≤ CT := le_trans zero_le_one hCT
  have hLast : 0 ≤ (1 + Real.exp 1) * C0 := by positivity
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hCTnn, hLast]
  refine ⟨C, hC, ?_⟩
  intro rho hprob B hB hs hmean hvar beta N hN P L theta b ht hsmall hb
  have hbeta : 0 ≤ beta := integral_nonneg (fun z => pow_nonneg (abs_nonneg z) 3)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNr
  let Alive : Set (Shao.Path N) := {a | ∀ k : Fin (N + 1), -b ≤ Shao.prefixSum a k.val}
  have hAlive : MeasurableSet Alive := by
    simp only [Alive, Set.setOf_forall]
    exact MeasurableSet.iInter fun k : Fin (N + 1) =>
      measurableSet_le (measurable_const (a := -b))
        ((Shao.continuous_prefixSum k.val).measurable : Measurable (fun a : Shao.Path N => Shao.prefixSum a k.val))
  have hM := hMom rho B hB hs hmean hvar N
  change Measurable L ∧ ∀ t : ℝ, 0 ≤ t → t * B ≤ 1 / 10 →
    Integrable (fun a => Real.exp (t * L a)) P ∧
      (∫ a, Real.exp (t * L a) ∂P) ≤ CM * (1 + (N : ℝ) * t ^ 2) *
        Real.exp ((1002001 / 2000000 : ℝ) * (N : ℝ) * t ^ 2 +
          CM * (N : ℝ) * t ^ 3 * beta) at hM
  have hInt := (hM.2 theta ht (by linarith only [hsmall])).1.indicator hAlive
  refine ⟨hInt, ?_⟩
  have hos := hOS rho B hB hs hmean hvar N hN b hb
  change P.real Alive ≤ C0 * (b + beta) / Real.sqrt (N : ℝ) at hos
  by_cases htz : theta = 0
  · simp only [htz, zero_mul, zero_pow (by norm_num : 2 ≠ 0),
      zero_pow (by norm_num : 3 ≠ 0), mul_zero, Real.exp_zero, add_zero, mul_one]
    rw [integral_indicator hAlive, setIntegral_const]
    simp only [smul_eq_mul, mul_one]
    exact hos.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (show C0 ≤ C by dsimp only [C]; nlinarith only [hCTnn, mul_nonneg (Real.exp_pos 1).le hC0nn])
        (add_nonneg hb hbeta)) hsqrt.le)
  have htp : 0 < theta := lt_of_le_of_ne ht (Ne.symm htz)
  let lam : ℝ := (1001 / 997 : ℝ) * theta
  let u0 : ℝ := Real.sqrt (N : ℝ) + 10 * (B + b)
  have hlamp : 0 < lam := by dsimp only [lam]; positivity
  have hu0 : 0 < u0 := by dsimp only [u0]; positivity
  have hu0sqrt : Real.sqrt (N : ℝ) ≤ u0 := by dsimp only [u0]; linarith only [hB, hb]
  let K : ℝ := CT * (b + beta) * (1 + (N : ℝ) * lam ^ 2) *
    Real.exp ((1002001 / 2000000 : ℝ) * (N : ℝ) * lam ^ 2 +
      CT * (N : ℝ) * lam ^ 3 * beta + lam * (3 * B + 2 * b))
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hTailExp (u : ℝ) (hu : u0 ≤ u) : P.real (Alive ∩ {a | u < L a}) ≤
      K / u * Real.exp (-((1001 / 1000 : ℝ) * theta * u)) := by
    have hh := hWT rho B hB hs hmean hvar N hN theta b htp hsmall hb u hu
    refine hh.trans_eq ?_
    dsimp only [K]
    simp only [Real.exp_sub, Real.exp_add, Real.exp_neg]
    ring
  let mu : Measure (Shao.Path N) := P.restrict Alive
  have hLnonneg (a : Shao.Path N) : 0 ≤ L a := by
    run_tac
      let n := Lean.mkPrivateNameCore ("Shao.Probability.SourceCircularWitnessMoment".toName)
        ("Shao.Probability.SourceCircularWitnessMoment.cwm_path_extrema_geometry".toName)
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        have $(Lean.mkIdent ("hGeometryNonneg".toName)) := $(Lean.mkIdent n)
          $(Lean.mkIdent ("N".toName))))
    exact (hGeometryNonneg.2.2.2 a).1
  have hPrimitive (q : ℝ) :
      (∫ t in (0 : ℝ)..q, theta * Real.exp (theta * t)) = Real.exp (theta * q) - 1 := by
    have hd (t : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (theta * t))
        (theta * Real.exp (theta * t)) t := by
      convert (Real.hasDerivAt_exp (theta * t)).comp t ((hasDerivAt_id t).const_mul theta) using 1 <;> first | rfl | ring
    have hi : IntervalIntegrable (fun t : ℝ => theta * Real.exp (theta * t)) volume 0 q :=
      (show Continuous (fun t : ℝ => theta * Real.exp (theta * t)) by fun_prop).intervalIntegrable _ _
    simpa only [mul_zero, Real.exp_zero] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  have hExpMu : Integrable (fun a => Real.exp (theta * L a)) mu :=
    (hM.2 theta ht (by linarith only [hsmall])).1.integrableOn
  have hDiffMu : Integrable (fun a => Real.exp (theta * L a) - 1) mu :=
    hExpMu.sub (integrable_const 1)
  have hDiffNN : 0 ≤ᵐ[mu] (fun a => Real.exp (theta * L a) - 1) := by
    apply ae_of_all
    intro a
    exact sub_nonneg.2 (Real.one_le_exp_iff.2 (mul_nonneg ht (hLnonneg a)))
  have hCake := lintegral_comp_eq_lintegral_meas_lt_mul mu
    (ae_of_all mu hLnonneg) hM.1.aemeasurable
    (fun q _ => (show Continuous (fun t : ℝ => theta * Real.exp (theta * t)) by fun_prop).intervalIntegrable _ _)
    (ae_of_all _ (fun t => mul_nonneg ht (Real.exp_pos _).le))
  simp_rw [hPrimitive] at hCake
  have hLayer : (∫ a, Real.exp (theta * L a) - 1 ∂mu) =
      (∫⁻ t : ℝ in Set.Ioi 0, mu {a | t < L a} *
        ENNReal.ofReal (theta * Real.exp (theta * t))).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae hDiffNN hDiffMu.aestronglyMeasurable]
    exact congrArg ENNReal.toReal hCake
  have hMuTail (q : ℝ) : mu {a | q < L a} = P (Alive ∩ {a | q < L a}) := by
    dsimp only [mu]
    rw [Measure.restrict_apply (measurableSet_lt measurable_const hM.1), Set.inter_comm]
  have hLayerExp : (∫ a, Alive.indicator (fun a => Real.exp (theta * L a)) a ∂P) =
      P.real Alive + (∫⁻ t : ℝ in Set.Ioi 0, P (Alive ∩ {a | t < L a}) *
        ENNReal.ofReal (theta * Real.exp (theta * t))).toReal := by
    rw [integral_indicator hAlive]
    change (∫ a, Real.exp (theta * L a) ∂mu) = _
    have heq : (fun a => Real.exp (theta * L a)) =
        (fun a => Real.exp (theta * L a) - 1) + (fun _ => (1 : ℝ)) := by
      funext a
      simp only [Pi.add_apply]
      ring
    rw [heq]
    change (∫ a, (Real.exp (theta * L a) - 1) + 1 ∂mu) = _
    rw [integral_add hDiffMu (integrable_const 1), hLayer]
    simp_rw [hMuTail]
    simp only [integral_const, smul_eq_mul, mul_one, mu, Measure.restrict_apply_univ, Measure.real_def]
    ring
  let PA : ℝ := P.real Alive
  let f : ℝ → ℝ≥0∞ := fun t => P (Alive ∩ {a | t < L a}) *
    ENNReal.ofReal (theta * Real.exp (theta * t))
  have hPA : 0 ≤ PA := measureReal_nonneg
  have hTailReal (t : ℝ) : P (Alive ∩ {a | t < L a}) =
      ENNReal.ofReal (P.real (Alive ∩ {a | t < L a})) := by
    exact (ENNReal.ofReal_toReal (measure_ne_top P _)).symm
  have hLowInt : IntegrableOn (fun t : ℝ => PA * (theta * Real.exp (theta * t)))
      (Set.Ioc 0 u0) := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hu0.le).1
      ((show Continuous (fun t : ℝ => PA * (theta * Real.exp (theta * t))) by fun_prop).intervalIntegrable _ _)
  have hLowValue : (∫ t : ℝ in Set.Ioc 0 u0,
      PA * (theta * Real.exp (theta * t))) = PA * (Real.exp (theta * u0) - 1) := by
    rw [← intervalIntegral.integral_of_le hu0.le, intervalIntegral.integral_const_mul, hPrimitive]
  have hLow : (∫⁻ t : ℝ in Set.Ioc 0 u0, f t) ≤
      ENNReal.ofReal (PA * (Real.exp (theta * u0) - 1)) := by
    calc
      _ ≤ ∫⁻ t : ℝ in Set.Ioc 0 u0,
          ENNReal.ofReal (PA * (theta * Real.exp (theta * t))) := by
        apply lintegral_mono
        intro t
        dsimp only [f]
        rw [hTailReal, ← ENNReal.ofReal_mul (measureReal_nonneg : 0 ≤ P.real (Alive ∩ {a | t < L a}))]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
          (measureReal_mono (μ := P) Set.inter_subset_left)
          (mul_nonneg ht (Real.exp_pos _).le))
      _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal hLowInt
          (ae_of_all _ (fun t => mul_nonneg hPA (mul_nonneg ht (Real.exp_pos _).le))), hLowValue]
  have hDecay : -(theta / 1000) < 0 := by linarith only [htp]
  have hHighInt : IntegrableOn (fun t : ℝ => K * theta / u0 *
      Real.exp (-(theta / 1000) * t)) (Set.Ioi u0) :=
    (integrableOn_exp_mul_Ioi hDecay u0).const_mul (K * theta / u0)
  have hHighValue : (∫ t : ℝ in Set.Ioi u0,
      K * theta / u0 * Real.exp (-(theta / 1000) * t)) ≤ 1000 * K / u0 := by
    rw [integral_const_mul, integral_exp_mul_Ioi hDecay]
    have he : Real.exp (-(theta / 1000) * u0) ≤ 1 :=
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hDecay.le hu0.le)
    calc
      _ = 1000 * K / u0 * Real.exp (-(theta / 1000) * u0) := by
        field_simp
        <;> ring
      _ ≤ 1000 * K / u0 * 1 :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := mul_one _
  have hHigh : (∫⁻ t : ℝ in Set.Ioi u0, f t) ≤ ENNReal.ofReal (1000 * K / u0) := by
    calc
      _ ≤ ∫⁻ t : ℝ in Set.Ioi u0,
          ENNReal.ofReal (K * theta / u0 * Real.exp (-(theta / 1000) * t)) := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro t htI
        have htt : 0 < t := lt_of_lt_of_le hu0 htI.le
        have hfr : P.real (Alive ∩ {a | t < L a}) * (theta * Real.exp (theta * t)) ≤
            K * theta / u0 * Real.exp (-(theta / 1000) * t) := by
          calc
            _ ≤ (K / t * Real.exp (-((1001 / 1000 : ℝ) * theta * t))) *
                (theta * Real.exp (theta * t)) :=
              mul_le_mul_of_nonneg_right (hTailExp t htI.le) (by positivity)
            _ = K * theta / t * Real.exp (-(theta / 1000) * t) := by
              have he : Real.exp (-((1001 / 1000 : ℝ) * theta * t)) * Real.exp (theta * t) =
                  Real.exp (-(theta / 1000) * t) := by
                rw [← Real.exp_add]
                congr 1
                ring
              calc
                _ = K * theta / t * (Real.exp (-((1001 / 1000 : ℝ) * theta * t)) *
                    Real.exp (theta * t)) := by ring
                _ = _ := by rw [he]
            _ ≤ _ := by
              apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
              exact div_le_div_of_nonneg_left (mul_nonneg hK ht) hu0 htI.le
        dsimp only [f]
        rw [hTailReal, ← ENNReal.ofReal_mul (measureReal_nonneg : 0 ≤ P.real (Alive ∩ {a | t < L a}))]
        exact ENNReal.ofReal_le_ofReal hfr
      _ ≤ _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal hHighInt
          (ae_of_all _ (fun t => mul_nonneg (by positivity) (Real.exp_pos _).le))]
        exact ENNReal.ofReal_le_ofReal hHighValue
  have hUnion : Set.Ioc (0 : ℝ) u0 ∪ Set.Ioi u0 = Set.Ioi 0 := by
    ext t
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨ht, _⟩ | ht)
      · exact ht
      · exact hu0.trans ht
    · intro ht
      by_cases htu : t ≤ u0
      · exact Or.inl ⟨ht, htu⟩
      · exact Or.inr (lt_of_not_ge htu)
  have hDisjoint : Disjoint (Set.Ioc (0 : ℝ) u0) (Set.Ioi u0) := by
    exact Set.disjoint_left.2 (fun _ h1 h2 => (not_lt_of_ge h1.2) h2)
  have hLayerBound : (∫⁻ t : ℝ in Set.Ioi 0, f t).toReal ≤
      PA * (Real.exp (theta * u0) - 1) + 1000 * K / u0 := by
    have hsum : (∫⁻ t : ℝ in Set.Ioi 0, f t) ≤
        ENNReal.ofReal (PA * (Real.exp (theta * u0) - 1)) +
          ENNReal.ofReal (1000 * K / u0) := by
      rw [← hUnion, lintegral_union measurableSet_Ioi hDisjoint]
      exact add_le_add hLow hHigh
    have hloNN : 0 ≤ PA * (Real.exp (theta * u0) - 1) := by
      exact mul_nonneg hPA (sub_nonneg.2 (Real.one_le_exp_iff.2 (mul_nonneg ht hu0.le)))
    rw [← ENNReal.ofReal_add hloNN (by positivity : 0 ≤ 1000 * K / u0)] at hsum
    exact (ENNReal.toReal_mono (by simp) hsum).trans_eq
      (ENNReal.toReal_ofReal (add_nonneg hloNN (by positivity)))
  have hIntegralBound : (∫ a : Shao.Path N,
      Alive.indicator (fun a => Real.exp (theta * L a)) a ∂P) ≤
      PA * Real.exp (theta * u0) + 1000 * K / u0 := by
    rw [hLayerExp]
    change PA + (∫⁻ t : ℝ in Set.Ioi 0, f t).toReal ≤ _
    linarith only [hLayerBound]
  let E : ℝ := (253 / 500 : ℝ) * (N : ℝ) * theta ^ 2 +
    C * (N : ℝ) * theta ^ 3 * beta + C * theta * (B + b)
  let D : ℝ := (b + beta) / Real.sqrt (N : ℝ) *
    (1 + (N : ℝ) * theta ^ 2) * Real.exp E
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hC10 : 10 ≤ C := by dsimp only [C]; linarith only [hCTnn, hLast]
  have hCCub : CT * (1001 / 997 : ℝ) ^ 3 ≤ C := by
    dsimp only [C]
    linarith only [hCTnn, hLast]
  have hC6 : 6 ≤ C := by linarith only [hC10]
  have hCubic : CT * (N : ℝ) * lam ^ 3 * beta ≤ C * (N : ℝ) * theta ^ 3 * beta := by
    calc
      _ = (CT * (1001 / 997 : ℝ) ^ 3) * ((N : ℝ) * theta ^ 3 * beta) := by dsimp only [lam]; ring
      _ ≤ C * ((N : ℝ) * theta ^ 3 * beta) := mul_le_mul_of_nonneg_right hCCub (by positivity)
      _ = _ := by ring
  have hHighE : (1002001 / 2000000 : ℝ) * (N : ℝ) * lam ^ 2 +
      CT * (N : ℝ) * lam ^ 3 * beta + lam * (3 * B + 2 * b) ≤ E := by
    have hquad : (1002001 / 2000000 : ℝ) * (N : ℝ) * lam ^ 2 ≤
        (253 / 500 : ℝ) * (N : ℝ) * theta ^ 2 := by
      dsimp only [lam]
      nlinarith only [mul_nonneg hNr.le (sq_nonneg theta)]
    have hlin : lam * (3 * B + 2 * b) ≤ C * theta * (B + b) := by
      have hC6mul := mul_le_mul_of_nonneg_right hC6 (mul_nonneg ht (add_nonneg hB.le hb))
      dsimp only [lam]
      nlinarith only [hC6mul, mul_nonneg ht hB.le, mul_nonneg ht hb]
    dsimp only [E]
    exact add_le_add (add_le_add hquad hCubic) hlin
  have hPoly : 1 + (N : ℝ) * lam ^ 2 ≤ 4 * (1 + (N : ℝ) * theta ^ 2) := by
    dsimp only [lam]
    nlinarith only [mul_nonneg hNr.le (sq_nonneg theta)]
  have hRatio : (b + beta) / u0 ≤ (b + beta) / Real.sqrt (N : ℝ) :=
    div_le_div_of_nonneg_left (add_nonneg hb hbeta) hsqrt hu0sqrt
  have hHighFinal : 1000 * K / u0 ≤ 4000 * CT * D := by
    calc
      _ = 1000 * CT * ((b + beta) / u0) * (1 + (N : ℝ) * lam ^ 2) *
          Real.exp ((1002001 / 2000000 : ℝ) * (N : ℝ) * lam ^ 2 +
            CT * (N : ℝ) * lam ^ 3 * beta + lam * (3 * B + 2 * b)) := by dsimp only [K]; ring
      _ ≤ 1000 * CT * ((b + beta) / Real.sqrt (N : ℝ)) *
          (4 * (1 + (N : ℝ) * theta ^ 2)) * Real.exp E := by
        gcongr
      _ = _ := by dsimp only [D]; ring
  have hLowE : theta * u0 ≤ 1 + E := by
    have hsqrt2 : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hNr.le
    have hyoung : theta * Real.sqrt (N : ℝ) ≤ 1 + (253 / 500 : ℝ) * (N : ℝ) * theta ^ 2 := by
      nlinarith only [sq_nonneg (theta * Real.sqrt (N : ℝ) - 1), mul_nonneg hNr.le (sq_nonneg theta), hsqrt2]
    have hlin := mul_le_mul_of_nonneg_right hC10 (mul_nonneg ht (add_nonneg hB.le hb))
    have hcub : 0 ≤ C * (N : ℝ) * theta ^ 3 * beta := by positivity
    dsimp only [u0, E]
    nlinarith only [hyoung, hlin, hcub]
  have hLowFinal : PA * Real.exp (theta * u0) ≤ Real.exp 1 * C0 * D := by
    have hexp : Real.exp (theta * u0) ≤ Real.exp 1 * Real.exp E := by
      simpa only [Real.exp_add] using Real.exp_le_exp.mpr hLowE
    calc
      _ ≤ (C0 * (b + beta) / Real.sqrt (N : ℝ)) *
          (Real.exp 1 * Real.exp E) := mul_le_mul hos hexp (Real.exp_pos _).le (by positivity)
      _ ≤ (C0 * (b + beta) / Real.sqrt (N : ℝ)) *
          (Real.exp 1 * Real.exp E) * (1 + (N : ℝ) * theta ^ 2) := by
        apply le_mul_of_one_le_right (by positivity)
        nlinarith only [mul_nonneg hNr.le (sq_nonneg theta)]
      _ = _ := by dsimp only [D]; ring
  have hCoeff : Real.exp 1 * C0 + 4000 * CT ≤ C := by
    dsimp only [C]
    nlinarith only [hCTnn, hC0nn]
  calc
    _ ≤ PA * Real.exp (theta * u0) + 1000 * K / u0 := hIntegralBound
    _ ≤ (Real.exp 1 * C0 + 4000 * CT) * D := by nlinarith only [hLowFinal, hHighFinal]
    _ ≤ C * D := mul_le_mul_of_nonneg_right hCoeff hD
    _ = _ := by dsimp only [D, E]; ring

private theorem pww_retained_copy_variance
    (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (h2 : Integrable (fun z : ℝ => z ^ 2) rho)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) rho)
    (hmean : (∫ z : ℝ, z ∂rho) = 0)
    (hvar : (∫ z : ℝ, z ^ 2 ∂rho) = 1) :
    let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
    let A : ℝ := 1024 * beta
    1 ≤ beta ∧ 0 < A ∧
      rho.real {z : ℝ | A < |z|} ≤ (1 / 1073741824 : ℝ) ∧
      (∫ z : ℝ, {w : ℝ | A < |w|}.indicator (fun w => w ^ 2) z ∂rho) ≤
        (1 / 1024 : ℝ) ∧
      ∀ z : ℝ,
        Integrable ({w : ℝ | |w| ≤ A}.indicator (fun w => (z - w) ^ 2)) rho ∧
          (1 / 2 : ℝ) ≤
            ∫ w : ℝ, {u : ℝ | |u| ≤ A}.indicator (fun u => (z - u) ^ 2) w ∂rho := by
  classical
  intro beta A
  have h1 : Integrable (fun z : ℝ => z) rho :=
    ((memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 h2).integrable (by norm_num)
  have hbeta : 1 ≤ beta := by
    have hh : 3 * (∫ z : ℝ, z ^ 2 ∂rho) ≤ 2 * beta + 1 := by
      calc
        _ = ∫ z : ℝ, 3 * z ^ 2 ∂rho := (integral_const_mul _ _).symm
        _ ≤ ∫ z : ℝ, 2 * |z| ^ 3 + 1 ∂rho := by
          apply integral_mono (h2.const_mul 3) ((h3.const_mul 2).add (integrable_const 1))
          intro z
          change 3 * z ^ 2 ≤ 2 * |z| ^ 3 + 1
          have hh := mul_nonneg (sq_nonneg (|z| - 1)) (by positivity : 0 ≤ 2 * |z| + 1)
          rw [← sq_abs z]
          nlinarith only [hh]
        _ = 2 * beta + 1 := by
          rw [integral_add (h3.const_mul 2) (integrable_const 1), integral_const_mul]
          simp [beta]
    rw [hvar] at hh
    linarith only [hh]
  have hbetap : 0 < beta := lt_of_lt_of_le zero_lt_one hbeta
  have hA : 0 < A := by dsimp only [A]; positivity
  let Bad : Set ℝ := {z | A < |z|}
  let Good : Set ℝ := {z | |z| ≤ A}
  have hBad : MeasurableSet Bad := measurableSet_lt measurable_const continuous_abs.measurable
  have hGood : MeasurableSet Good := measurableSet_le continuous_abs.measurable measurable_const
  have hBad2I : Integrable (Bad.indicator (fun z : ℝ => z ^ 2)) rho := h2.indicator hBad
  have hBad3I : Integrable (Bad.indicator (fun z : ℝ => |z| ^ 3)) rho := h3.indicator hBad
  have hBad3Le : (∫ z : ℝ, Bad.indicator (fun z => |z| ^ 3) z ∂rho) ≤ beta := by
    apply integral_mono hBad3I h3
    intro z
    by_cases hz : z ∈ Bad
    · simp [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz]
      positivity
  have hMarkov : A ^ 3 * rho.real Bad ≤ beta := by
    calc
      _ = ∫ z : ℝ, Bad.indicator (fun _ => A ^ 3) z ∂rho := by
        rw [integral_indicator hBad, setIntegral_const]
        simp only [smul_eq_mul]
        ring
      _ ≤ ∫ z : ℝ, Bad.indicator (fun z => |z| ^ 3) z ∂rho := by
        apply integral_mono ((integrable_const (A ^ 3)).indicator hBad) hBad3I
        intro z
        by_cases hz : z ∈ Bad
        · simp only [Set.indicator_of_mem hz]
          exact pow_le_pow_left₀ hA.le hz.le 3
        · simp [Set.indicator_of_notMem hz]
      _ ≤ beta := hBad3Le
  have hbetaCube : beta ≤ beta ^ 3 := by
    have hs : 1 ≤ beta ^ 2 := by nlinarith only [hbeta, sq_nonneg (beta - 1)]
    nlinarith only [mul_nonneg hbetap.le (sub_nonneg.2 hs)]
  have hBadProb : rho.real Bad ≤ (1 / 1073741824 : ℝ) := by
    calc
      _ ≤ beta / A ^ 3 := (le_div_iff₀ (pow_pos hA 3)).2 (by nlinarith only [hMarkov])
      _ ≤ _ := (div_le_iff₀ (pow_pos hA 3)).2 (by dsimp only [A]; nlinarith only [hbetaCube])
  have hBadSecond : (∫ z : ℝ, Bad.indicator (fun z => z ^ 2) z ∂rho) ≤ (1 / 1024 : ℝ) := by
    have hh : A * (∫ z : ℝ, Bad.indicator (fun z => z ^ 2) z ∂rho) ≤ beta := by
      calc
        _ = ∫ z : ℝ, A * Bad.indicator (fun z => z ^ 2) z ∂rho := (integral_const_mul _ _).symm
        _ ≤ ∫ z : ℝ, Bad.indicator (fun z => |z| ^ 3) z ∂rho := by
          apply integral_mono (hBad2I.const_mul A) hBad3I
          intro z
          by_cases hz : z ∈ Bad
          · simp only [Set.indicator_of_mem hz]
            have hzA : A ≤ |z| := hz.le
            rw [← sq_abs z]
            nlinarith only [mul_nonneg (sub_nonneg.2 hzA) (sq_nonneg |z|)]
          · simp [Set.indicator_of_notMem hz, mul_zero]
        _ ≤ beta := hBad3Le
    have hhdiv : (∫ z : ℝ, Bad.indicator (fun z => z ^ 2) z ∂rho) ≤ beta / A :=
      (le_div_iff₀ hA).2 (by nlinarith only [hh])
    have hratio : beta / A = (1 / 1024 : ℝ) := by dsimp only [A]; field_simp
    exact hhdiv.trans_eq hratio
  refine ⟨hbeta, hA, hBadProb, hBadSecond, ?_⟩
  intro z
  have hFullI : Integrable (fun w : ℝ => (z - w) ^ 2) rho := by
    convert ((integrable_const (z ^ 2)).sub (h1.const_mul (2 * z))).add h2 using 1
    funext w
    change (z - w) ^ 2 = z ^ 2 - (2 * z) * w + w ^ 2
    ring
  have hFull : (∫ w : ℝ, (z - w) ^ 2 ∂rho) = z ^ 2 + 1 := by
    calc
      _ = ∫ w : ℝ, z ^ 2 - (2 * z) * w + w ^ 2 ∂rho := by
        apply integral_congr_ae
        exact ae_of_all _ (fun w => by ring)
      _ = _ := by
        have hadd := integral_add ((integrable_const (z ^ 2)).sub (h1.const_mul (2 * z))) h2
        simp only [Pi.sub_apply] at hadd
        rw [hadd, integral_sub (integrable_const (z ^ 2)) (h1.const_mul (2 * z)),
          integral_const_mul, hmean, hvar]
        simp
  have hGInt := hFullI.indicator hGood
  have hBInt := hFullI.indicator hBad
  have hSplit : (∫ w : ℝ, Good.indicator (fun w => (z - w) ^ 2) w ∂rho) +
      (∫ w : ℝ, Bad.indicator (fun w => (z - w) ^ 2) w ∂rho) = z ^ 2 + 1 := by
    rw [← integral_add hGInt hBInt, ← hFull]
    apply integral_congr_ae
    apply ae_of_all
    intro w
    by_cases hw : |w| ≤ A
    · have hwG : w ∈ Good := hw
      have hwB : w ∉ Bad := not_lt_of_ge hw
      simp only [Set.indicator_of_mem hwG, Set.indicator_of_notMem hwB, add_zero]
    · have hwG : w ∉ Good := hw
      have hwB : w ∈ Bad := lt_of_not_ge hw
      simp only [Set.indicator_of_mem hwB, Set.indicator_of_notMem hwG, zero_add]
  have hBadUpper : (∫ w : ℝ, Bad.indicator (fun w => (z - w) ^ 2) w ∂rho) ≤
      2 * z ^ 2 * rho.real Bad + 2 *
        (∫ w : ℝ, Bad.indicator (fun w => w ^ 2) w ∂rho) := by
    let upper : ℝ → ℝ := Bad.indicator (fun w => 2 * z ^ 2 + 2 * w ^ 2)
    have hUpperInt : Integrable upper rho :=
      ((integrable_const (2 * z ^ 2)).add (h2.const_mul 2)).indicator hBad
    calc
      _ ≤ ∫ w : ℝ, upper w ∂rho := by
        apply integral_mono hBInt hUpperInt
        intro w
        by_cases hw : w ∈ Bad
        · simp only [Set.indicator_of_mem hw, upper]
          nlinarith only [sq_nonneg (z + w)]
        · simp [Set.indicator_of_notMem hw, upper]
      _ = _ := by
        have he : upper = (Bad.indicator (fun _ => 2 * z ^ 2)) +
            (fun w => 2 * Bad.indicator (fun u => u ^ 2) w) := by
          funext w
          by_cases hw : w ∈ Bad <;> simp [upper, hw]
        rw [he]
        change (∫ w : ℝ, Bad.indicator (fun _ => 2 * z ^ 2) w +
          2 * Bad.indicator (fun u => u ^ 2) w ∂rho) = _
        rw [integral_add ((integrable_const (2 * z ^ 2)).indicator hBad) (hBad2I.const_mul 2),
          integral_const_mul, integral_indicator hBad, setIntegral_const]
        simp only [smul_eq_mul]
        ring
  refine ⟨hGInt, ?_⟩
  have hBadQuant := hBadUpper.trans (add_le_add
    (mul_le_mul_of_nonneg_left hBadProb (by positivity : 0 ≤ 2 * z ^ 2))
    (mul_le_mul_of_nonneg_left hBadSecond (by norm_num : (0 : ℝ) ≤ 2)))
  nlinarith only [hSplit, hBadQuant, sq_nonneg z]

private theorem pww_iid_coordinate_copy_exchange
    (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (B : ℝ) (hB : 0 < B) (hs : ∀ᵐ z : ℝ ∂rho, |z| ≤ B)
    (hmean : (∫ z : ℝ, z ∂rho) = 0) (k : ℕ) :
    let P : Measure (Shao.Path k) := Measure.pi (fun _ : Fin k => rho)
    let J : Measure (Shao.Path k × ℝ) := P.prod rho
    (∀ i : Fin k,
      MeasurePreserving
        (fun p : Shao.Path k × ℝ => (Function.update p.1 i p.2, p.1 i)) J J) ∧
      ∀ (H : ℝ), 0 ≤ H →
        ∀ G : Shao.Path k → ℝ, Measurable G → (∀ a : Shao.Path k, |G a| ≤ H) →
          Integrable (fun a : Shao.Path k => Shao.prefixSum a k * G a) P ∧
            (∀ i : Fin k,
              Integrable (fun p : Shao.Path k × ℝ =>
                (p.1 i - p.2) * (G p.1 - G (Function.update p.1 i p.2))) J) ∧
            2 * (∫ a : Shao.Path k, Shao.prefixSum a k * G a ∂P) =
              ∑ i : Fin k, ∫ p : Shao.Path k × ℝ,
                (p.1 i - p.2) * (G p.1 - G (Function.update p.1 i p.2)) ∂J := by
  classical
  intro P J
  have hSwap (i : Fin k) : MeasurePreserving
      (fun p : Shao.Path k × ℝ => (Function.update p.1 i p.2, p.1 i)) J J := by
    cases k with
    | zero => exact Fin.elim0 i
    | succ m =>
      let R : Measure (Shao.Path m) := Measure.pi (fun _ : Fin m => rho)
      let e : Shao.Path (m + 1) ≃ᵐ (ℝ × Shao.Path m) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i
      have he : MeasurePreserving e P (rho.prod R) :=
        measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => rho) i
      let mid : ((ℝ × Shao.Path m) × ℝ) → ((ℝ × Shao.Path m) × ℝ) :=
        fun p => ((p.2, p.1.2), p.1.1)
      have hmid : MeasurePreserving mid ((rho.prod R).prod rho) ((rho.prod R).prod rho) := by
        have h1 := Measure.measurePreserving_swap (μ := rho.prod R) (ν := rho)
        have h2 := (measurePreserving_prodAssoc rho rho R).symm
        have h3 := (Measure.measurePreserving_swap (μ := rho) (ν := rho)).prod (MeasurePreserving.id R)
        have h4 := measurePreserving_prodAssoc rho rho R
        have h5 := Measure.measurePreserving_swap (μ := rho) (ν := rho.prod R)
        convert h5.comp (h4.comp (h3.comp (h2.comp h1))) using 1
        funext p
        rfl
      have hh := (he.symm.prod (MeasurePreserving.id rho)).comp
        (hmid.comp (he.prod (MeasurePreserving.id rho)))
      convert hh using 1
      funext p
      apply Prod.ext
      · change Function.update p.1 i p.2 =
          (Fin.insertNthEquiv (fun _ : Fin (m + 1) => ℝ) i)
            (p.2, Fin.removeNth i p.1)
        simp only [Fin.insertNthEquiv_apply, Fin.insertNth_removeNth]
      · rfl
  refine ⟨hSwap, ?_⟩
  intro H hH G hG hGB
  have hSupport : ∀ᵐ a : Shao.Path k ∂P, ∀ i : Fin k, |a i| ≤ B := by
    apply ae_all_iff.2
    intro i
    exact (measurePreserving_eval (fun _ : Fin k => rho) i).quasiMeasurePreserving.ae hs
  have hSupportJ : ∀ᵐ p : Shao.Path k × ℝ ∂J,
      (∀ i : Fin k, |p.1 i| ≤ B) ∧ |p.2| ≤ B := by
    have h1 := (measurePreserving_fst (μ := P) (ν := rho)).quasiMeasurePreserving.ae hSupport
    have h2 := (measurePreserving_snd (μ := P) (ν := rho)).quasiMeasurePreserving.ae hs
    exact h1.and h2
  have hGInt : Integrable G P := by
    apply (integrable_const H).mono' hG.aestronglyMeasurable
    exact ae_of_all _ (fun a => by simpa only [Real.norm_eq_abs] using hGB a)
  have hAiInt (i : Fin k) : Integrable (fun a : Shao.Path k => a i * G a) P := by
    apply (integrable_const (B * H)).mono' ((measurable_pi_apply i).mul hG).aestronglyMeasurable
    filter_upwards [hSupport] with a ha
    change |a i * G a| ≤ B * H
    rw [abs_mul]
    exact mul_le_mul (ha i) (hGB a) (abs_nonneg _) hB.le
  have hSGInt : Integrable (fun a : Shao.Path k => Shao.prefixSum a k * G a) P := by
    have hh : Integrable (fun a : Shao.Path k => ∑ i : Fin k, a i * G a) P :=
      integrable_finsetSum _ (fun i _ => hAiInt i)
    convert hh using 1
    funext a
    rw [Shao.prefixSum_length, Finset.sum_mul]
  have hFirstInt (i : Fin k) : Integrable
      (fun p : Shao.Path k × ℝ => (p.1 i - p.2) * G p.1) J := by
    apply (integrable_const (2 * B * H)).mono' (by fun_prop)
    filter_upwards [hSupportJ] with p hp
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_right ((abs_sub _ _).trans (by linarith only [hp.1 i, hp.2]))
      (abs_nonneg _)).trans (mul_le_mul_of_nonneg_left (hGB p.1) (by positivity))
  have hCopyInt (i : Fin k) : Integrable
      (fun p : Shao.Path k × ℝ => (p.1 i - p.2) * G (Function.update p.1 i p.2)) J := by
    apply (integrable_const (2 * B * H)).mono' (by fun_prop)
    filter_upwards [hSupportJ] with p hp
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_right ((abs_sub _ _).trans (by linarith only [hp.1 i, hp.2]))
      (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hGB (Function.update p.1 i p.2)) (by positivity))
  have hDiffInt (i : Fin k) : Integrable
      (fun p : Shao.Path k × ℝ => (p.1 i - p.2) *
        (G p.1 - G (Function.update p.1 i p.2))) J := by
    convert (hFirstInt i).sub (hCopyInt i) using 1
    funext p
    simp only [Pi.sub_apply]
    ring
  have hAnti (i : Fin k) :
      (∫ p : Shao.Path k × ℝ, (p.1 i - p.2) * G (Function.update p.1 i p.2) ∂J) =
        -(∫ p : Shao.Path k × ℝ, (p.1 i - p.2) * G p.1 ∂J) := by
    have hMapM : AEStronglyMeasurable
        (fun p : Shao.Path k × ℝ => (p.1 i - p.2) * G p.1)
        (J.map (fun p : Shao.Path k × ℝ => (Function.update p.1 i p.2, p.1 i))) := by
      rw [(hSwap i).map_eq]
      exact (hFirstInt i).aestronglyMeasurable
    have hh := integral_map (hSwap i).measurable.aemeasurable hMapM
    rw [(hSwap i).map_eq] at hh
    simp only [Function.update_apply, if_pos rfl] at hh
    have he : (fun p : Shao.Path k × ℝ => (p.2 - p.1 i) * G (Function.update p.1 i p.2)) =
        (fun p => -((p.1 i - p.2) * G (Function.update p.1 i p.2))) := by
      funext p
      ring
    change (∫ p : Shao.Path k × ℝ, (p.1 i - p.2) * G p.1 ∂J) =
      ∫ p : Shao.Path k × ℝ, (p.2 - p.1 i) * G (Function.update p.1 i p.2) ∂J at hh
    rw [he, integral_neg] at hh
    linarith only [hh]
  have hFirstValue (i : Fin k) :
      (∫ p : Shao.Path k × ℝ, (p.1 i - p.2) * G p.1 ∂J) =
        ∫ a : Shao.Path k, a i * G a ∂P := by
    have h1Int : Integrable (fun p : Shao.Path k × ℝ => p.1 i * G p.1) J :=
      (measurePreserving_fst (μ := P) (ν := rho)).integrable_comp_of_integrable (hAiInt i)
    have h2Int : Integrable (fun p : Shao.Path k × ℝ => p.2 * G p.1) J := by
      apply (integrable_const (B * H)).mono' (by fun_prop)
      filter_upwards [hSupportJ] with p hp
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul hp.2 (hGB p.1) (abs_nonneg _) hB.le
    calc
      _ = (∫ p : Shao.Path k × ℝ, p.1 i * G p.1 ∂J) -
          (∫ p : Shao.Path k × ℝ, p.2 * G p.1 ∂J) := by
        rw [← integral_sub h1Int h2Int]
        apply integral_congr_ae
        exact ae_of_all _ (fun p => by ring)
      _ = _ := by
        have hf : (∫ p : Shao.Path k × ℝ, p.1 i * G p.1 ∂J) =
            ∫ a : Shao.Path k, a i * G a ∂P := by
          change (∫ p : Shao.Path k × ℝ, (fun a : Shao.Path k => a i * G a) p.1 ∂P.prod rho) = _
          rw [integral_prod _ h1Int]
          simp
        have hz : (∫ p : Shao.Path k × ℝ, p.2 * G p.1 ∂J) = 0 := by
          have hc : (fun p : Shao.Path k × ℝ => p.2 * G p.1) =
              (fun p => G p.1 * p.2) := by funext p; ring
          rw [hc]
          change (∫ p : Shao.Path k × ℝ, G p.1 * (fun z : ℝ => z) p.2 ∂P.prod rho) = 0
          have hh := integral_prod_mul (μ := P) (ν := rho) G (fun z : ℝ => z)
          exact hh.trans (by rw [hmean, mul_zero])
        rw [hf, hz, sub_zero]
  refine ⟨hSGInt, hDiffInt, ?_⟩
  have hEach (i : Fin k) : (∫ p : Shao.Path k × ℝ,
      (p.1 i - p.2) * (G p.1 - G (Function.update p.1 i p.2)) ∂J) =
        2 * (∫ a : Shao.Path k, a i * G a ∂P) := by
    calc
      _ = (∫ p : Shao.Path k × ℝ, (p.1 i - p.2) * G p.1 ∂J) -
          (∫ p : Shao.Path k × ℝ, (p.1 i - p.2) * G (Function.update p.1 i p.2) ∂J) := by
        rw [← integral_sub (hFirstInt i) (hCopyInt i)]
        apply integral_congr_ae
        exact ae_of_all _ (fun p => by ring)
      _ = _ := by rw [hAnti, hFirstValue]; ring
  simp_rw [hEach]
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun i _ => hAiInt i)]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun a => by
    change Shao.prefixSum a k * G a = ∑ i : Fin k, a i * G a
    rw [Shao.prefixSum_length, Finset.sum_mul])

private theorem pww_iid_rare_coordinate_count
    (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (A : ℝ) (hp : rho.real {z : ℝ | A < |z|} ≤ (1 / 1073741824 : ℝ))
    (k : ℕ) :
    let P : Measure (Shao.Path k) := Measure.pi (fun _ : Fin k => rho)
    let badCount : Shao.Path k → ℕ := fun a =>
      (Finset.univ.filter (fun i : Fin k => A < |a i|)).card
    P.real {a : Shao.Path k | (k : ℝ) / 2 < (badCount a : ℝ)} ≤
      (1 / 4 : ℝ) ^ k := by
  classical
  intro P badCount
  let Bad : Set ℝ := {z | A < |z|}
  have hBad : MeasurableSet Bad := measurableSet_lt measurable_const continuous_abs.measurable
  let f : ℝ → ℝ := fun z => if z ∈ Bad then 256 else 1
  have hfm : Measurable f := Measurable.ite hBad measurable_const measurable_const
  have hfBound (z : ℝ) : |f z| ≤ 256 := by
    dsimp only [f]
    split_ifs <;> norm_num
  have hfNN (z : ℝ) : 0 ≤ f z := by
    dsimp only [f]
    split_ifs <;> norm_num
  have hfInt : Integrable f rho := by
    apply (integrable_const (256 : ℝ)).mono' hfm.aestronglyMeasurable
    exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hfBound z)
  have hfValue : (∫ z : ℝ, f z ∂rho) = 1 + 255 * rho.real Bad := by
    have he : f = fun z => 1 + 255 * Bad.indicator (fun _ => (1 : ℝ)) z := by
      funext z
      by_cases hz : z ∈ Bad <;> simp [f, hz] <;> norm_num
    rw [he, integral_add (integrable_const 1)
      (((integrable_const (1 : ℝ)).indicator hBad).const_mul 255), integral_const_mul,
      integral_indicator hBad, setIntegral_const]
    simp
  have hfSmall : (∫ z : ℝ, f z ∂rho) ≤ 2 := by
    rw [hfValue]
    change rho.real Bad ≤ (1 / 1073741824 : ℝ) at hp
    linarith only [hp]
  let F : Shao.Path k → ℝ := fun a => ∏ i : Fin k, f (a i)
  have hFInt : Integrable F P := Integrable.fintype_prod (fun _ : Fin k => hfInt)
  have hFValue : (∫ a : Shao.Path k, F a ∂P) = (∫ z : ℝ, f z ∂rho) ^ k := by
    simpa only [F, P, Fintype.card_fin] using
      (integral_fintype_prod_eq_pow (ι := Fin k) (μ := rho) f)
  have hFSmall : (∫ a : Shao.Path k, F a ∂P) ≤ (2 : ℝ) ^ k := by
    rw [hFValue]
    exact pow_le_pow_left₀ (integral_nonneg hfNN) hfSmall k
  have hFFormula (a : Shao.Path k) : F a = (256 : ℝ) ^ badCount a := by
    dsimp only [F, f, badCount, Bad]
    rw [Finset.prod_ite]
    simp
  let E : Set (Shao.Path k) := {a | (k : ℝ) / 2 < (badCount a : ℝ)}
  have hCountM : Measurable badCount := by
    have he : badCount = fun a : Shao.Path k => ∑ i : Fin k, if A < |a i| then (1 : ℕ) else 0 := by
      funext a
      simp only [badCount, Finset.card_filter]
    rw [he]
    apply Finset.measurable_sum
    intro i _
    exact Measurable.ite
      (measurableSet_lt measurable_const (continuous_abs.measurable.comp (measurable_pi_apply i)))
      measurable_const measurable_const
  have hE : MeasurableSet E := measurableSet_lt measurable_const
    ((measurable_of_countable (fun m : ℕ => (m : ℝ))).comp hCountM)
  have hOnE (a : Shao.Path k) (ha : a ∈ E) : (16 : ℝ) ^ k ≤ F a := by
    have hnat : k ≤ 2 * badCount a := by
      change (k : ℝ) / 2 < (badCount a : ℝ) at ha
      have hh : (k : ℝ) < (2 : ℝ) * (badCount a : ℝ) := by linarith only [ha]
      exact_mod_cast hh.le
    rw [hFFormula]
    calc
      (16 : ℝ) ^ k ≤ 16 ^ (2 * badCount a) := pow_le_pow_right₀ (by norm_num) hnat
      _ = (256 : ℝ) ^ badCount a := by rw [pow_mul]; norm_num
  have hMarkov : (16 : ℝ) ^ k * P.real E ≤ (2 : ℝ) ^ k := by
    calc
      _ = ∫ a : Shao.Path k, E.indicator (fun _ => (16 : ℝ) ^ k) a ∂P := by
        rw [integral_indicator hE, setIntegral_const]
        simp only [smul_eq_mul]
        ring
      _ ≤ ∫ a : Shao.Path k, F a ∂P := by
        apply integral_mono ((integrable_const ((16 : ℝ) ^ k)).indicator hE) hFInt
        intro a
        by_cases ha : a ∈ E
        · simpa only [Set.indicator_of_mem ha] using hOnE a ha
        · simp only [Set.indicator_of_notMem ha]
          exact Finset.prod_nonneg (fun i _ => hfNN (a i))
      _ ≤ _ := hFSmall
  calc
    P.real E ≤ (2 : ℝ) ^ k / (16 : ℝ) ^ k :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < 16 ^ k)).2 (by nlinarith only [hMarkov])
    _ = (1 / 8 : ℝ) ^ k := by rw [← div_pow]; norm_num
    _ ≤ (1 / 4 : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k

private theorem pww_weighted_coordinate_concentration :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (B : ℝ), 0 < B → (∀ᵐ z : ℝ ∂rho, |z| ≤ B) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ (k : ℕ), 0 < k →
          let P : Measure (Shao.Path k) := Measure.pi (fun _ : Fin k => rho)
          let L : Shao.Path k → ℝ := fun a =>
            if hk : 0 < k then
              sSup {w : ℝ | ∃ i : Fin k, ∃ q : Fin (k + 1),
                w = Shao.prefixSum a k -
                  2 * ∑ r ∈ Finset.range q.val,
                    a ⟨(i.val + r) % k, Nat.mod_lt _ hk⟩}
            else 0
          ∀ theta : ℝ, 0 < theta → theta * B ≤ 1 / 100 →
            ∀ F : Shao.Path k → ℝ, Measurable F →
              (∀ (a : Shao.Path k) (i : Fin k) (z z' : ℝ), z ≤ z' →
                (1 / 2 : ℝ) * (z' - z) ≤
                  F (Function.update a i z') - F (Function.update a i z) ∧
                F (Function.update a i z') - F (Function.update a i z) ≤
                  (3 / 2 : ℝ) * (z' - z)) →
              ∀ a v : ℝ, 0 ≤ v →
                Integrable
                  ({u : Shao.Path k | a ≤ F u ∧ F u ≤ a + v}.indicator
                    (fun u => Real.exp (theta * L u))) P ∧
                  (∫ u : Shao.Path k,
                    {u : Shao.Path k | a ≤ F u ∧ F u ≤ a + v}.indicator
                      (fun u => Real.exp (theta * L u)) u ∂P) ≤
                    C * (v + beta) * (theta + 1 / (theta * (k : ℝ))) *
                      (1 + (k : ℝ) * theta ^ 2) *
                      Real.exp ((503 / 1000 : ℝ) * (k : ℝ) * theta ^ 2 +
                        C * (k : ℝ) * theta ^ 3 * beta) := by
  classical
  obtain ⟨CM, hCM, hMoment⟩ :=
    Shao.Probability.SourceCircularWitnessMoment.actual_circular_witness_small_parameter_moment
  let C : ℝ := 10 ^ 12 * (1 + Real.exp 1) ^ 8 * (1 + CM)
  have hC : 1 ≤ C := by
    have he : 1 ≤ (1 + Real.exp 1) ^ 8 :=
      one_le_pow₀ (by linarith only [Real.exp_pos 1] : (1 : ℝ) ≤ 1 + Real.exp 1)
    have hm : 1 ≤ 1 + CM := by linarith only [hCM]
    have hfirst : 1 ≤ (10 : ℝ) ^ 12 * (1 + Real.exp 1) ^ 8 :=
      one_le_mul_of_one_le_of_one_le (by norm_num) he
    exact one_le_mul_of_one_le_of_one_le hfirst hm
  refine ⟨C, hC, ?_⟩
  intro rho hprob B hB hs hmean hvar beta k hk P L theta ht hsmall F hFm hF a v hv
  have hbase := boundedQuadraticTilt_density_moments rho B 0 0 hB (le_refl 0) hs
  rcases hbase with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hpows, _⟩
  have h2 := (hpows 2).1
  have h3 := (hpows 3).2.2.1
  let A : ℝ := 1024 * beta
  have hRetained := pww_retained_copy_variance rho h2 h3 hmean hvar
  change 1 ≤ beta ∧ 0 < A ∧
    rho.real {z : ℝ | A < |z|} ≤ (1 / 1073741824 : ℝ) ∧
    (∫ z : ℝ, {w : ℝ | A < |w|}.indicator (fun w => w ^ 2) z ∂rho) ≤ (1 / 1024 : ℝ) ∧
    ∀ z : ℝ, Integrable ({w : ℝ | |w| ≤ A}.indicator (fun w => (z - w) ^ 2)) rho ∧
      (1 / 2 : ℝ) ≤ ∫ w : ℝ, {u : ℝ | |u| ≤ A}.indicator (fun u => (z - u) ^ 2) w ∂rho at hRetained
  have hbeta : 1 ≤ beta := hRetained.1
  have hA : 0 < A := hRetained.2.1
  let H : ℝ := 2 * v + 4 * A
  let g : Shao.Path k → ℝ := fun u => min (max (2 * F u - 2 * a + 2 * A) 0) H
  let Omega : Shao.Path k → ℝ := fun u => Real.exp (theta * L u)
  let I : Set (Shao.Path k) := {u | a ≤ F u ∧ F u ≤ a + v}
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hgM : Measurable g := by dsimp only [g]; fun_prop
  have hI : MeasurableSet I :=
    (measurableSet_le measurable_const hFm).inter (measurableSet_le hFm measurable_const)
  have hgb (u : Shao.Path k) : 0 ≤ g u ∧ g u ≤ H :=
    ⟨le_min (le_max_right _ _) hH, min_le_right _ _⟩
  run_tac
    let n := Lean.mkPrivateNameCore ("Shao.Probability.SourceTrueEnergyStrip".toName)
      ("Shao.Probability.tes_clip_step".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hClipStep".toName)) := $(Lean.mkIdent n)))
  have hStep (u : Shao.Path k) (i : Fin k) (z : ℝ) :
      0 ≤ (u i - z) * (g u - g (Function.update u i z)) ∧
        (u ∈ I → |u i| ≤ A → |z| ≤ A →
          (u i - z) ^ 2 ≤ (u i - z) * (g u - g (Function.update u i z))) := by
    have hp : 0 ≤ u i - z → 2 * F (Function.update u i z) ≤ 2 * F u - (u i - z) := by
      intro hh
      have hslope := (hF u i z (u i) (by linarith only [hh])).1
      simp only [Function.update_eq_self] at hslope
      linarith only [hslope]
    have hn : u i - z ≤ 0 → 2 * F u - (u i - z) ≤ 2 * F (Function.update u i z) := by
      intro hh
      have hslope := (hF u i (u i) z (by linarith only [hh])).1
      simp only [Function.update_eq_self] at hslope
      linarith only [hslope]
    have hh := hClipStep (2 * a) (2 * (a + v)) (2 * A)
      (2 * F u) (2 * F (Function.update u i z)) (u i - z)
      (by linarith only [hv]) (by positivity) hp hn
    have hf : (fun t : ℝ => min (max (t - 2 * a + 2 * A) 0)
        (2 * (a + v) - 2 * a + 2 * (2 * A))) (2 * F u) = g u := by
      dsimp only [g, H]
      congr 1
      ring
    have hf' : (fun t : ℝ => min (max (t - 2 * a + 2 * A) 0)
        (2 * (a + v) - 2 * a + 2 * (2 * A))) (2 * F (Function.update u i z)) =
          g (Function.update u i z) := by
      dsimp only [g, H]
      congr 1
      ring
    change 0 ≤ (u i - z) * (_ - _) ∧ _ at hh
    rw [hf, hf'] at hh
    refine ⟨hh.1, ?_⟩
    intro hu hui hz
    apply hh.2 (by linarith only [hu.1]) (by linarith only [hu.2])
    exact (abs_sub (u i) z).trans (by linarith only [hui, hz])
  have hM := hMoment rho B hB hs hmean hvar k
  change Measurable L ∧ ∀ t : ℝ, 0 ≤ t → t * B ≤ 1 / 10 →
    Integrable (fun u => Real.exp (t * L u)) P ∧
      (∫ u, Real.exp (t * L u) ∂P) ≤ CM * (1 + (k : ℝ) * t ^ 2) *
        Real.exp ((1002001 / 2000000 : ℝ) * (k : ℝ) * t ^ 2 +
          CM * (k : ℝ) * t ^ 3 * beta) at hM
  have hLM : Measurable L := hM.1
  have hOmegaM : Measurable Omega := Real.continuous_exp.measurable.comp (measurable_const.mul hLM)
  have hPSM : Measurable (fun u : Shao.Path k => Shao.prefixSum u k) := (Shao.continuous_prefixSum k).measurable
  have hAbsPSM : Measurable (fun u : Shao.Path k => |Shao.prefixSum u k|) := continuous_abs.measurable.comp hPSM
  have hOmegaInt := (hM.2 theta ht.le (by linarith only [hsmall])).1
  have hTargetInt := hOmegaInt.indicator hI
  run_tac
    let n := Lean.mkPrivateNameCore ("Shao.Probability.SourceCircularWitnessMoment".toName)
      ("Shao.Probability.SourceCircularWitnessMoment.cwm_path_extrema_geometry".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hGeometry".toName)) := $(Lean.mkIdent n)
        $(Lean.mkIdent ("k".toName))))
  have hLNN (u : Shao.Path k) : 0 ≤ L u := (hGeometry.2.2.2 u).1
  have hLsum (u : Shao.Path k) : L u ≤ ∑ i : Fin k, |u i| := (hGeometry.2.2.2 u).2.1
  have hAbsS (u : Shao.Path k) : |Shao.prefixSum u k| ≤ L u := by
    have hg := hGeometry.2.2.2 u
    have hge := hg.2.2.2.2.2.2.1
    change L u = _ at hge
    have hAnn := hg.2.2.1
    have hRnn := hg.2.2.2.2.1
    have hPos : Shao.prefixSum u k ≤ L u := by
      rw [hge]
      refine le_trans ?_ (le_max_left _ _)
      linarith only [hRnn]
    have hNeg : -Shao.prefixSum u k ≤ L u := by
      rw [hge]
      refine le_trans ?_ (le_max_right _ _)
      linarith only [hAnn]
    exact abs_le.mpr ⟨by linarith only [hNeg], hPos⟩
  have hSupport : ∀ᵐ u : Shao.Path k ∂P, ∀ i : Fin k, |u i| ≤ B := by
    apply ae_all_iff.2
    intro i
    exact (measurePreserving_eval (fun _ : Fin k => rho) i).quasiMeasurePreserving.ae hs
  have hLSupport (u : Shao.Path k) (hu : ∀ i : Fin k, |u i| ≤ B) : L u ≤ (k : ℝ) * B := by
    calc
      _ ≤ ∑ i : Fin k, |u i| := hLsum u
      _ ≤ ∑ _ : Fin k, B := Finset.sum_le_sum (fun i _ => hu i)
      _ = _ := by simp
  let cap : ℝ := Real.exp (theta * ((k : ℝ) * B))
  let Gcap : Shao.Path k → ℝ := fun u => min (Omega u) cap * g u
  have hCap : 0 < cap := Real.exp_pos _
  have hGcapM : Measurable Gcap := by dsimp only [Gcap]; fun_prop
  have hGcapBound (u : Shao.Path k) : |Gcap u| ≤ cap * H := by
    have ho : 0 < Omega u := Real.exp_pos _
    dsimp only [Gcap]
    rw [abs_mul, abs_of_nonneg (le_min ho.le hCap.le), abs_of_nonneg (hgb u).1]
    exact mul_le_mul (min_le_right _ _) (hgb u).2 (hgb u).1 hCap.le
  have hGcapEq (u : Shao.Path k) (hu : ∀ i : Fin k, |u i| ≤ B) :
      Gcap u = Omega u * g u := by
    have ho : Omega u ≤ cap := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hLSupport u hu) ht.le)
    simp only [Gcap, min_eq_left ho]
  have hGcapAE : Gcap =ᵐ[P] (fun u => Omega u * g u) := by
    filter_upwards [hSupport] with u hu
    exact hGcapEq u hu
  let J : Measure (Shao.Path k × ℝ) := P.prod rho
  have hCopy := pww_iid_coordinate_copy_exchange rho B hB hs hmean k
  change (∀ i : Fin k, MeasurePreserving
    (fun q : Shao.Path k × ℝ => (Function.update q.1 i q.2, q.1 i)) J J) ∧ _ at hCopy
  obtain ⟨hSwap, hExchange⟩ := hCopy
  have hExchangeBound := hExchange (cap * H) (mul_nonneg hCap.le hH) Gcap hGcapM hGcapBound
  have hGcapAEFirst : ∀ᵐ q : Shao.Path k × ℝ ∂J,
      Gcap q.1 = Omega q.1 * g q.1 :=
    (measurePreserving_fst (μ := P) (ν := rho)).quasiMeasurePreserving.ae hGcapAE
  have hGcapAECopy (i : Fin k) : ∀ᵐ q : Shao.Path k × ℝ ∂J,
      Gcap (Function.update q.1 i q.2) =
        Omega (Function.update q.1 i q.2) * g (Function.update q.1 i q.2) :=
    (hSwap i).quasiMeasurePreserving.ae hGcapAEFirst
  have hSupportJ : ∀ᵐ q : Shao.Path k × ℝ ∂J,
      (∀ i : Fin k, |q.1 i| ≤ B) ∧ |q.2| ≤ B :=
    ((measurePreserving_fst (μ := P) (ν := rho)).quasiMeasurePreserving.ae hSupport).and
      ((measurePreserving_snd (μ := P) (ν := rho)).quasiMeasurePreserving.ae hs)
  have hOmegaDiff (u : Shao.Path k) (i : Fin k) (z : ℝ)
      (hui : |u i| ≤ B) (hz : |z| ≤ B) :
      |Omega u - Omega (Function.update u i z)| ≤
        2 * theta * |u i - z| * Omega u := by
    have hLip := pww_circular_witness_coordinate_lipschitz k u i (u i) z
    simp only [Function.update_eq_self] at hLip
    have hDiff : |L (Function.update u i z) - L u| ≤ |u i - z| := by
      simpa only [abs_sub_comm] using hLip
    have hdBound : |theta * (L (Function.update u i z) - L u)| ≤ 1 := by
      rw [abs_mul, abs_of_pos ht]
      have hdist : |u i - z| ≤ 2 * B := (abs_sub _ _).trans (by linarith only [hui, hz])
      nlinarith only [mul_le_mul_of_nonneg_left hDiff ht.le,
        mul_le_mul_of_nonneg_left hdist ht.le, hsmall]
    have hexp := Real.abs_exp_sub_one_le hdBound
    have he : Omega u - Omega (Function.update u i z) =
        Omega u * (1 - Real.exp (theta * (L (Function.update u i z) - L u))) := by
      dsimp only [Omega]
      rw [show theta * (L (Function.update u i z) - L u) =
        theta * L (Function.update u i z) - theta * L u by ring, Real.exp_sub, mul_sub, mul_one]
      field_simp
      <;> ring
    rw [he, abs_mul, abs_of_pos (Real.exp_pos _), abs_sub_comm]
    have hh := mul_le_mul_of_nonneg_left hexp (show 0 ≤ Omega u by exact (Real.exp_pos _).le)
    rw [abs_mul, abs_of_pos ht] at hh
    nlinarith only [hh, mul_le_mul_of_nonneg_left hDiff
      (show 0 ≤ 2 * theta * Omega u by dsimp only [Omega]; positivity)]
  have h1 : Integrable (fun z : ℝ => z) rho :=
    ((memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 h2).integrable (by norm_num)
  have hOmegaCap (u : Shao.Path k) (hu : ∀ i : Fin k, |u i| ≤ B) : Omega u ≤ cap :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hLSupport u hu) ht.le)
  have hUpdateSupport (u : Shao.Path k) (i : Fin k) (z : ℝ)
      (hu : ∀ j : Fin k, |u j| ≤ B) (hz : |z| ≤ B) :
      ∀ j : Fin k, |Function.update u i z j| ≤ B := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa [Function.update_apply] using hz
    · simpa [Function.update_apply, hji] using hu j
  let R : Fin k → Shao.Path k × ℝ → ℝ := fun i q =>
    (q.1 i - q.2) * (g q.1 - g (Function.update q.1 i q.2)) * Omega q.1
  let Err : Fin k → Shao.Path k × ℝ → ℝ := fun i q =>
    (q.1 i - q.2) * g (Function.update q.1 i q.2) *
      (Omega q.1 - Omega (Function.update q.1 i q.2))
  have hRNN (i : Fin k) (q : Shao.Path k × ℝ) : 0 ≤ R i q :=
    mul_nonneg (hStep q.1 i q.2).1 (Real.exp_pos _).le
  have hgDiff (u u' : Shao.Path k) : |g u - g u'| ≤ H := by
    exact abs_le.mpr ⟨by linarith only [(hgb u).1, (hgb u').2],
      by linarith only [(hgb u).2, (hgb u').1]⟩
  have hRInt (i : Fin k) : Integrable (R i) J := by
    apply (integrable_const (2 * B * H * cap)).mono' (by exact (show Measurable (R i) by dsimp only [R]; fun_prop).aestronglyMeasurable)
    filter_upwards [hSupportJ] with q hq
    change |(q.1 i - q.2) * (g q.1 - g (Function.update q.1 i q.2)) * Omega q.1| ≤ _
    rw [abs_mul, abs_mul, abs_of_pos (show 0 < Omega q.1 from Real.exp_pos _)]
    have hd : |q.1 i - q.2| ≤ 2 * B := (abs_sub _ _).trans (by linarith only [hq.1 i, hq.2])
    exact mul_le_mul (mul_le_mul hd (hgDiff _ _) (abs_nonneg _) (by positivity))
      (hOmegaCap q.1 hq.1) (Real.exp_pos _).le (by positivity)
  have hErrInt (i : Fin k) : Integrable (Err i) J := by
    apply (integrable_const (4 * B * H * cap)).mono' (by exact (show Measurable (Err i) by dsimp only [Err]; fun_prop).aestronglyMeasurable)
    filter_upwards [hSupportJ] with q hq
    have hu := hOmegaCap q.1 hq.1
    have hz := hOmegaCap (Function.update q.1 i q.2) (hUpdateSupport q.1 i q.2 hq.1 hq.2)
    have hdiff : |Omega q.1 - Omega (Function.update q.1 i q.2)| ≤ 2 * cap :=
      (abs_sub _ _).trans (by rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]; linarith only [hu, hz])
    change |(q.1 i - q.2) * g (Function.update q.1 i q.2) *
      (Omega q.1 - Omega (Function.update q.1 i q.2))| ≤ _
    rw [abs_mul, abs_mul, abs_of_nonneg (hgb _).1]
    have hd : |q.1 i - q.2| ≤ 2 * B := (abs_sub _ _).trans (by linarith only [hq.1 i, hq.2])
    calc
      _ ≤ (2 * B * H) * (2 * cap) :=
        mul_le_mul (mul_le_mul hd (hgb _).2 (hgb _).1 (by positivity)) hdiff (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hActualSInt : Integrable (fun u : Shao.Path k => Shao.prefixSum u k * (Omega u * g u)) P :=
    hExchangeBound.1.congr (by
      filter_upwards [hGcapAE] with u hu
      rw [hu])
  have hActualCopy (i : Fin k) :
      (∫ q : Shao.Path k × ℝ, (q.1 i - q.2) *
        (Omega q.1 * g q.1 - Omega (Function.update q.1 i q.2) * g (Function.update q.1 i q.2)) ∂J) =
      (∫ q : Shao.Path k × ℝ, (q.1 i - q.2) *
        (Gcap q.1 - Gcap (Function.update q.1 i q.2)) ∂J) := by
    apply integral_congr_ae
    filter_upwards [hGcapAEFirst, hGcapAECopy i] with q hq hz
    rw [hq, hz]
  have hIdentity : (∑ i : Fin k, ∫ q, R i q ∂J) +
      (∑ i : Fin k, ∫ q, Err i q ∂J) =
        2 * (∫ u : Shao.Path k, Shao.prefixSum u k * (Omega u * g u) ∂P) := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ i : Fin k, ∫ q : Shao.Path k × ℝ, (q.1 i - q.2) *
          (Omega q.1 * g q.1 - Omega (Function.update q.1 i q.2) * g (Function.update q.1 i q.2)) ∂J := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← integral_add (hRInt i) (hErrInt i)]
        apply integral_congr_ae
        exact ae_of_all _ (fun q => by dsimp only [R, Err]; ring)
      _ = ∑ i : Fin k, ∫ q : Shao.Path k × ℝ, (q.1 i - q.2) *
          (Gcap q.1 - Gcap (Function.update q.1 i q.2)) ∂J := by
        exact Finset.sum_congr rfl (fun i _ => hActualCopy i)
      _ = 2 * (∫ u : Shao.Path k, Shao.prefixSum u k * Gcap u ∂P) := hExchangeBound.2.2.symm
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hGcapAE] with u hu
        rw [hu]
  let W : Fin k → Shao.Path k → ℝ := fun i =>
    (I ∩ {u : Shao.Path k | |u i| ≤ A}).indicator Omega
  have hWInt (i : Fin k) : Integrable (W i) P :=
    hOmegaInt.indicator (hI.inter (measurableSet_le
      (continuous_abs.measurable.comp (measurable_pi_apply i)) measurable_const))
  have hRSectionInt (u : Shao.Path k) (i : Fin k) : Integrable (fun z : ℝ => R i (u, z)) rho := by
    apply (integrable_const ((|u i| + B) * H * Omega u)).mono' (by exact (show Measurable (fun z : ℝ => R i (u, z)) by dsimp only [R]; fun_prop).aestronglyMeasurable)
    filter_upwards [hs] with z hz
    change |(u i - z) * (g u - g (Function.update u i z)) * Omega u| ≤ _
    rw [abs_mul, abs_mul, abs_of_pos (show 0 < Omega u from Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul ((abs_sub _ _).trans (by linarith only [hz])) (hgDiff _ _)
        (abs_nonneg _) (by positivity)) (Real.exp_pos _).le
  have hRSectionLower (u : Shao.Path k) (i : Fin k) :
      (1 / 2 : ℝ) * W i u ≤ ∫ z : ℝ, R i (u, z) ∂rho := by
    by_cases hu : u ∈ I ∩ {u : Shao.Path k | |u i| ≤ A}
    · simp only [W, Set.indicator_of_mem hu]
      have hri := hRetained.2.2.2.2 (u i)
      calc
        (1 / 2 : ℝ) * Omega u ≤ Omega u *
            (∫ z : ℝ, {z : ℝ | |z| ≤ A}.indicator (fun z => (u i - z) ^ 2) z ∂rho) := by
          nlinarith only [mul_le_mul_of_nonneg_left hri.2 (show 0 ≤ Omega u from (Real.exp_pos _).le)]
        _ = ∫ z : ℝ, Omega u *
            {z : ℝ | |z| ≤ A}.indicator (fun z => (u i - z) ^ 2) z ∂rho := (integral_const_mul _ _).symm
        _ ≤ ∫ z : ℝ, R i (u, z) ∂rho := by
          apply integral_mono (hri.1.const_mul (Omega u)) (hRSectionInt u i)
          intro z
          change Omega u * (if |z| ≤ A then (u i - z) ^ 2 else 0) ≤ R i (u, z)
          by_cases hz : |z| ≤ A
          · rw [if_pos hz]
            dsimp only [R]
            have hh := (hStep u i z).2 hu.1 hu.2 hz
            nlinarith only [mul_le_mul_of_nonneg_right hh (show 0 ≤ Omega u from (Real.exp_pos _).le)]
          · rw [if_neg hz, mul_zero]
            exact hRNN i (u, z)
    · simp only [W, Set.indicator_of_notMem hu, mul_zero]
      exact integral_nonneg (fun z => hRNN i (u, z))
  have hRLower (i : Fin k) : (1 / 2 : ℝ) * (∫ u : Shao.Path k, W i u ∂P) ≤ ∫ q, R i q ∂J := by
    have hh := integral_mono ((hWInt i).const_mul (1 / 2 : ℝ))
      (hRInt i).integral_prod_left (fun u => hRSectionLower u i)
    rw [integral_const_mul] at hh
    rwa [integral_prod _ (hRInt i)]
  let Omega0 : Fin k → Shao.Path k → ℝ := fun i u =>
    Real.exp (theta * L (Function.update u i 0))
  have hOmegaCompare (u : Shao.Path k) (i : Fin k) (hui : |u i| ≤ B) :
      Omega u ≤ Real.exp 1 * Omega0 i u ∧ Omega0 i u ≤ Real.exp 1 * Omega u := by
    have hh := pww_circular_witness_coordinate_lipschitz k u i (u i) 0
    simp only [Function.update_eq_self, zero_sub, abs_neg] at hh
    have hvarL : |L (Function.update u i 0) - L u| ≤ B := hh.trans hui
    have h1 : theta * L u ≤ 1 + theta * L (Function.update u i 0) := by
      have hmul := mul_le_mul_of_nonneg_left (abs_le.mp hvarL).1 ht.le
      nlinarith only [hmul, hsmall]
    have h2 : theta * L (Function.update u i 0) ≤ 1 + theta * L u := by
      have hmul := mul_le_mul_of_nonneg_left (abs_le.mp hvarL).2 ht.le
      nlinarith only [hmul, hsmall]
    exact ⟨by simpa only [Omega, Omega0, Real.exp_add] using Real.exp_le_exp.2 h1,
      by simpa only [Omega, Omega0, Real.exp_add] using Real.exp_le_exp.2 h2⟩
  have hOmega0M (i : Fin k) : Measurable (Omega0 i) := by dsimp only [Omega0]; fun_prop
  have hOmega0Int (i : Fin k) : Integrable (Omega0 i) P := by
    apply (integrable_const cap).mono' (hOmega0M i).aestronglyMeasurable
    filter_upwards [hSupport] with u hu
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hOmegaCap (Function.update u i 0) (hUpdateSupport u i 0 hu (by simpa using hB.le))
  have hSquareInt (i : Fin k) : Integrable (fun u : Shao.Path k => (u i) ^ 2 * Omega u) P := by
    apply (integrable_const (B ^ 2 * cap)).mono' (by exact (show Measurable _ by fun_prop).aestronglyMeasurable)
    filter_upwards [hSupport] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (by nlinarith only [hu i, sq_abs (u i), abs_nonneg (u i)])
      (hOmegaCap u hu) (Real.exp_pos _).le (sq_nonneg B)
  have hSquare0Int (i : Fin k) : Integrable (fun u : Shao.Path k => (u i) ^ 2 * Omega0 i u) P := by
    apply (integrable_const (B ^ 2 * cap)).mono' (by exact ((measurable_pi_apply i).pow_const 2).mul (hOmega0M i) |>.aestronglyMeasurable)
    filter_upwards [hSupport] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (by nlinarith only [hu i, sq_abs (u i), abs_nonneg (u i)])
      (hOmegaCap (Function.update u i 0) (hUpdateSupport u i 0 hu (by simpa using hB.le)))
      (Real.exp_pos _).le (sq_nonneg B)
  have hZeroSquareFactor (i : Fin k) :
      (∫ u : Shao.Path k, (u i) ^ 2 * Omega0 i u ∂P) = ∫ u, Omega0 i u ∂P := by
    run_tac
      let n := Lean.mkPrivateNameCore ("Shao.Probability.SourceTrueEnergyStrip".toName)
        ("Shao.Probability.tes_zero_update_indep".toName)
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        have $(Lean.mkIdent ("hZeroIndep".toName)) := $(Lean.mkIdent n)
          $(Lean.mkIdent ("rho".toName)) $(Lean.mkIdent ("k".toName))
          $(Lean.mkIdent ("L".toName)) $(Lean.mkIdent ("hM".toName)).1
          $(Lean.mkIdent ("i".toName))))
    have hi : IndepFun (fun u : Shao.Path k => (u i) ^ 2) (Omega0 i) P :=
      hZeroIndep.comp (measurable_id.pow_const 2) ((Real.continuous_exp.measurable).comp (measurable_const.mul measurable_id))
    rw [hi.integral_fun_mul_eq_mul_integral
      ((measurable_pi_apply i).pow_const 2).aestronglyMeasurable (hOmega0Int i).aestronglyMeasurable]
    have hsq : (∫ u : Shao.Path k, (u i) ^ 2 ∂P) = 1 := by
      calc
        _ = ∫ z : ℝ, z ^ 2 ∂rho := by
          simpa only [P] using (integral_comp_eval (μ := fun _ : Fin k => rho)
            (i := i) (f := fun z : ℝ => z ^ 2) h2.aestronglyMeasurable)
        _ = 1 := hvar
    rw [hsq, one_mul]
  have hSquareBound (i : Fin k) :
      (∫ u : Shao.Path k, (u i) ^ 2 * Omega u ∂P) ≤
        (Real.exp 1) ^ 2 * (∫ u, Omega u ∂P) := by
    have hO0 : (∫ u : Shao.Path k, Omega0 i u ∂P) ≤ Real.exp 1 * (∫ u, Omega u ∂P) := by
      rw [← integral_const_mul]
      apply integral_mono_ae (hOmega0Int i) (hOmegaInt.const_mul (Real.exp 1))
      filter_upwards [hSupport] with u hu
      exact (hOmegaCompare u i (hu i)).2
    calc
      _ ≤ ∫ u : Shao.Path k, Real.exp 1 * ((u i) ^ 2 * Omega0 i u) ∂P := by
        apply integral_mono_ae (hSquareInt i) ((hSquare0Int i).const_mul (Real.exp 1))
        filter_upwards [hSupport] with u hu
        have hh := mul_le_mul_of_nonneg_left (hOmegaCompare u i (hu i)).1 (sq_nonneg (u i))
        nlinarith only [hh]
      _ = Real.exp 1 * (∫ u, Omega0 i u ∂P) := by rw [integral_const_mul, hZeroSquareFactor]
      _ ≤ (Real.exp 1) ^ 2 * (∫ u, Omega u ∂P) := by
        have hh := mul_le_mul_of_nonneg_left hO0 (Real.exp_pos 1).le
        nlinarith only [hh]
  have hD2Int (i : Fin k) : Integrable
      (fun q : Shao.Path k × ℝ => (q.1 i - q.2) ^ 2 * Omega q.1) J := by
    apply (integrable_const (4 * B ^ 2 * cap)).mono' (by exact (show Measurable _ by fun_prop).aestronglyMeasurable)
    filter_upwards [hSupportJ] with q hq
    change |(q.1 i - q.2) ^ 2 * Omega q.1| ≤ _
    rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_pos (Real.exp_pos _)]
    have hd : |q.1 i - q.2| ≤ 2 * B := (abs_sub _ _).trans (by linarith only [hq.1 i, hq.2])
    have hdsq : (q.1 i - q.2) ^ 2 ≤ 4 * B ^ 2 := by nlinarith only [hd, abs_nonneg (q.1 i - q.2), sq_abs (q.1 i - q.2)]
    exact mul_le_mul hdsq (hOmegaCap q.1 hq.1) (Real.exp_pos _).le (by positivity)
  have hD2Bound (i : Fin k) :
      (∫ q : Shao.Path k × ℝ, (q.1 i - q.2) ^ 2 * Omega q.1 ∂J) ≤
        2 * ((Real.exp 1) ^ 2 + 1) * (∫ u, Omega u ∂P) := by
    have hAi : Integrable (fun q : Shao.Path k × ℝ => (q.1 i) ^ 2 * Omega q.1) J :=
      (measurePreserving_fst (μ := P) (ν := rho)).integrable_comp_of_integrable (hSquareInt i)
    have hZi : Integrable (fun q : Shao.Path k × ℝ => q.2 ^ 2 * Omega q.1) J := by
      have hh := hOmegaInt.mul_prod h2
      simpa only [mul_comm] using hh
    have hvalA : (∫ q : Shao.Path k × ℝ, (q.1 i) ^ 2 * Omega q.1 ∂J) =
        ∫ u : Shao.Path k, (u i) ^ 2 * Omega u ∂P := by
      rw [integral_prod _ hAi]
      simp
    have hvalZ : (∫ q : Shao.Path k × ℝ, q.2 ^ 2 * Omega q.1 ∂J) = ∫ u, Omega u ∂P := by
      have hh := integral_prod_mul (μ := P) (ν := rho) Omega (fun z : ℝ => z ^ 2)
      simpa only [hvar, mul_one, one_mul, mul_comm, J] using hh
    calc
      _ ≤ ∫ q : Shao.Path k × ℝ, 2 * ((q.1 i) ^ 2 * Omega q.1) + 2 * (q.2 ^ 2 * Omega q.1) ∂J := by
        apply integral_mono (hD2Int i) ((hAi.const_mul 2).add (hZi.const_mul 2))
        intro q
        change (q.1 i - q.2) ^ 2 * Omega q.1 ≤
          2 * ((q.1 i) ^ 2 * Omega q.1) + 2 * (q.2 ^ 2 * Omega q.1)
        have hh : (q.1 i - q.2) ^ 2 ≤ 2 * (q.1 i) ^ 2 + 2 * q.2 ^ 2 := by nlinarith only [sq_nonneg (q.1 i + q.2)]
        have hm := mul_le_mul_of_nonneg_right hh (show 0 ≤ Omega q.1 from (Real.exp_pos _).le)
        nlinarith only [hm]
      _ = 2 * (∫ u : Shao.Path k, (u i) ^ 2 * Omega u ∂P) + 2 * (∫ u, Omega u ∂P) := by
        rw [integral_add (hAi.const_mul 2) (hZi.const_mul 2), integral_const_mul, integral_const_mul, hvalA, hvalZ]
      _ ≤ _ := by nlinarith only [hSquareBound i]
  let t1 : ℝ := (1001 / 1000 : ℝ) * theta
  let M1 : ℝ := ∫ u : Shao.Path k, Real.exp (t1 * L u) ∂P
  have ht1 : 0 < t1 := by dsimp only [t1]; positivity
  have ht1B : t1 * B ≤ 1 / 10 := by dsimp only [t1]; nlinarith only [hsmall]
  have hM1Int := (hM.2 t1 ht1.le ht1B).1
  have hM1One : 1 ≤ M1 := by
    calc
      (1 : ℝ) = ∫ _ : Shao.Path k, (1 : ℝ) ∂P := by simp
      _ ≤ ∫ u : Shao.Path k, Real.exp (t1 * L u) ∂P := by
        apply integral_mono (integrable_const 1) hM1Int
        intro u
        exact Real.one_le_exp_iff.2 (mul_nonneg ht1.le (hLNN u))
  have hMtheta : (∫ u : Shao.Path k, Omega u ∂P) ≤ M1 := by
    apply integral_mono hOmegaInt hM1Int
    intro u
    apply Real.exp_le_exp.2
    dsimp only [t1]
    nlinarith only [mul_nonneg ht.le (hLNN u)]
  have hAbsSInt : Integrable (fun u : Shao.Path k => |Shao.prefixSum u k| * Omega u) P := by
    apply (integrable_const ((k : ℝ) * B * cap)).mono' (by exact (show Measurable _ by fun_prop).aestronglyMeasurable)
    filter_upwards [hSupport] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul ((hAbsS u).trans (hLSupport u hu)) (hOmegaCap u hu)
      (Real.exp_pos _).le (by positivity)
  have hAbsSBound : (∫ u : Shao.Path k, |Shao.prefixSum u k| * Omega u ∂P) ≤ 1000 / theta * M1 := by
    rw [← integral_const_mul]
    apply integral_mono hAbsSInt (hM1Int.const_mul (1000 / theta))
    intro u
    have hx : theta * L u / 1000 ≤ Real.exp (theta * L u / 1000) := by
      linarith only [Real.add_one_le_exp (theta * L u / 1000)]
    have hm := mul_le_mul_of_nonneg_right hx (show 0 ≤ Omega u from (Real.exp_pos _).le)
    have he : Real.exp (theta * L u / 1000) * Omega u = Real.exp (t1 * L u) := by
      dsimp only [Omega, t1]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he] at hm
    have hl : L u * Omega u ≤ 1000 / theta * Real.exp (t1 * L u) := by
      have hh : L u * Omega u ≤ (1000 * Real.exp (t1 * L u)) / theta :=
        (le_div_iff₀ ht).2 (by nlinarith only [hm])
      convert hh using 1 <;> ring
    exact (mul_le_mul_of_nonneg_right (hAbsS u) (Real.exp_pos _).le).trans hl
  have hSGUpper : (∫ u : Shao.Path k, Shao.prefixSum u k * (Omega u * g u) ∂P) ≤
      H * (1000 / theta) * M1 := by
    have hh : (∫ u : Shao.Path k, Shao.prefixSum u k * (Omega u * g u) ∂P) ≤
        H * (∫ u : Shao.Path k, |Shao.prefixSum u k| * Omega u ∂P) := by
      rw [← integral_const_mul]
      apply integral_mono hActualSInt (hAbsSInt.const_mul H)
      intro u
      have hg := (hgb u).2
      have hm := mul_le_mul_of_nonneg_left hg
        (mul_nonneg (abs_nonneg (Shao.prefixSum u k)) (show 0 ≤ Omega u from (Real.exp_pos _).le))
      have hs := mul_le_mul_of_nonneg_right (le_abs_self (Shao.prefixSum u k))
        (mul_nonneg (show 0 ≤ Omega u from (Real.exp_pos _).le) (hgb u).1)
      nlinarith only [hm, hs]
    have hm := mul_le_mul_of_nonneg_left hAbsSBound hH
    nlinarith only [hh, hm]
  have hErrLower (i : Fin k) :
      -(4 * H * theta * ((Real.exp 1) ^ 2 + 1) * M1) ≤ ∫ q, Err i q ∂J := by
    have hLower : -(2 * H * theta) *
        (∫ q : Shao.Path k × ℝ, (q.1 i - q.2) ^ 2 * Omega q.1 ∂J) ≤
          ∫ q, Err i q ∂J := by
      rw [← integral_const_mul]
      apply integral_mono_ae ((hD2Int i).const_mul (-(2 * H * theta))) (hErrInt i)
      filter_upwards [hSupportJ] with q hq
      have he := hOmegaDiff q.1 i q.2 (hq.1 i) hq.2
      have hg := (hgb (Function.update q.1 i q.2)).2
      have hbnd : |Err i q| ≤ 2 * H * theta * (q.1 i - q.2) ^ 2 * Omega q.1 := by
        dsimp only [Err]
        rw [abs_mul, abs_mul, abs_of_nonneg (hgb _).1]
        have hh := mul_le_mul
          (mul_le_mul_of_nonneg_left hg (abs_nonneg (q.1 i - q.2))) he (abs_nonneg _)
          (mul_nonneg (abs_nonneg _) hH)
        calc
          _ ≤ (|q.1 i - q.2| * H) * (2 * theta * |q.1 i - q.2| * Omega q.1) := hh
          _ = _ := by rw [← sq_abs (q.1 i - q.2)]; ring
      have hm := neg_le_abs (Err i q)
      nlinarith only [hbnd, hm]
    have hD2 := (hD2Bound i).trans
      (mul_le_mul_of_nonneg_left hMtheta (by positivity : 0 ≤ 2 * ((Real.exp 1) ^ 2 + 1)))
    have hm := mul_le_mul_of_nonneg_left hD2 (show 0 ≤ 2 * H * theta by positivity)
    nlinarith only [hLower, hm]
  have hRsumUpper : (∑ i : Fin k, ∫ q, R i q ∂J) ≤
      2 * H * (1000 / theta) * M1 +
        4 * H * theta * ((Real.exp 1) ^ 2 + 1) * (k : ℝ) * M1 := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hErrLower i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    nlinarith only [hIdentity, hSGUpper, hh]
  let badCount : Shao.Path k → ℕ := fun u =>
    (Finset.univ.filter (fun i : Fin k => A < |u i|)).card
  let BadSet : Set (Shao.Path k) := {u | (k : ℝ) / 2 < (badCount u : ℝ)}
  have hBadCountM : Measurable badCount := by
    have he : badCount = fun u : Shao.Path k => ∑ i : Fin k, if A < |u i| then (1 : ℕ) else 0 := by
      funext u
      simp only [badCount, Finset.card_filter]
    rw [he]
    apply Finset.measurable_sum
    intro i _
    exact Measurable.ite (measurableSet_lt measurable_const
      (continuous_abs.measurable.comp (measurable_pi_apply i))) measurable_const measurable_const
  have hBadSet : MeasurableSet BadSet := measurableSet_lt measurable_const
    ((measurable_of_countable (fun m : ℕ => (m : ℝ))).comp hBadCountM)
  have hBadProb := pww_iid_rare_coordinate_count rho A hRetained.2.2.1 k
  change P.real BadSet ≤ (1 / 4 : ℝ) ^ k at hBadProb
  have hBadInt := hOmegaInt.indicator hBadSet
  have hBadCap : (∫ u : Shao.Path k, BadSet.indicator Omega u ∂P) ≤ cap * (1 / 4 : ℝ) ^ k := by
    calc
      _ ≤ ∫ u : Shao.Path k, BadSet.indicator (fun _ => cap) u ∂P := by
        apply integral_mono_ae hBadInt ((integrable_const cap).indicator hBadSet)
        filter_upwards [hSupport] with u hu
        by_cases hb : u ∈ BadSet
        · simpa only [Set.indicator_of_mem hb] using hOmegaCap u hu
        · simp only [Set.indicator_of_notMem hb, le_refl]
      _ = cap * P.real BadSet := by
        rw [integral_indicator hBadSet, setIntegral_const]
        simp only [smul_eq_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hBadProb hCap.le
  have hLogTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hExpSmall : Real.exp (1 / 100 : ℝ) ≤ 2 := by
    calc
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 (by linarith only [hLogTwo])
      _ = 2 := Real.exp_log (by norm_num)
  have hCapPow : cap ≤ (2 : ℝ) ^ k := by
    calc
      _ ≤ Real.exp ((k : ℝ) * (1 / 100 : ℝ)) := by
        apply Real.exp_le_exp.2
        have hh := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
        nlinarith only [hh]
      _ = Real.exp (1 / 100 : ℝ) ^ k := by rw [Real.exp_nat_mul]
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le hExpSmall k
  have hPowNat (m : ℕ) : (m : ℝ) + 1 ≤ (2 : ℝ) ^ m := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [pow_succ, Nat.cast_succ]
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith only [ih, hm]
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  have hksqrt : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkr
  have hSqrtLe : Real.sqrt (k : ℝ) ≤ (k : ℝ) + 1 := by
    nlinarith only [Real.sq_sqrt hkr.le, Real.sqrt_nonneg (k : ℝ), sq_nonneg (k : ℝ)]
  have hBadCost : (∫ u : Shao.Path k, BadSet.indicator Omega u ∂P) ≤ 1 / Real.sqrt (k : ℝ) := by
    calc
      _ ≤ cap * (1 / 4 : ℝ) ^ k := hBadCap
      _ ≤ (2 : ℝ) ^ k * (1 / 4 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right hCapPow (by positivity)
      _ = (1 / 2 : ℝ) ^ k := by rw [← mul_pow]; norm_num
      _ = 1 / (2 : ℝ) ^ k := by rw [one_div_pow]
      _ ≤ 1 / ((k : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (hPowNat k)
      _ ≤ _ := one_div_le_one_div_of_le hksqrt hSqrtLe
  let goodCount : Shao.Path k → ℕ := fun u =>
    (Finset.univ.filter (fun i : Fin k => |u i| ≤ A)).card
  have hCountSum (u : Shao.Path k) : goodCount u + badCount u = k := by
    calc
      _ = ∑ i : Fin k, ((if |u i| ≤ A then (1 : ℕ) else 0) +
          (if A < |u i| then (1 : ℕ) else 0)) := by
        simp only [goodCount, badCount, Finset.card_filter, Finset.sum_add_distrib]
      _ = ∑ _ : Fin k, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : |u i| ≤ A
        · simp [hi, not_lt_of_ge hi]
        · simp [hi, lt_of_not_ge hi]
      _ = k := by simp
  have hWSum (u : Shao.Path k) : (∑ i : Fin k, W i u) =
      I.indicator (fun u => Omega u * (goodCount u : ℝ)) u := by
    by_cases hu : u ∈ I
    · simp only [W, Set.indicator_apply, Set.mem_inter_iff, Set.mem_setOf_eq, hu, true_and, ite_true]
      have hc : goodCount u = ∑ i : Fin k, if |u i| ≤ A then (1 : ℕ) else 0 := by
        simp only [goodCount, Finset.card_filter]
      have hcr : (goodCount u : ℝ) = ∑ i : Fin k, if |u i| ≤ A then (1 : ℝ) else 0 := by
        rw [hc, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> norm_num
      rw [hcr, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    · simp [W, hu]
  have hWPoint (u : Shao.Path k) : (k : ℝ) / 2 *
      (I.indicator Omega u - BadSet.indicator Omega u) ≤ ∑ i : Fin k, W i u := by
    rw [hWSum]
    have ho : 0 ≤ Omega u := (Real.exp_pos _).le
    have hcn : (0 : ℝ) ≤ (goodCount u : ℝ) := Nat.cast_nonneg _
    by_cases hu : u ∈ I
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
      by_cases hb : u ∈ BadSet
      · rw [Set.indicator_of_mem hb, sub_self, mul_zero]
        exact mul_nonneg ho hcn
      · rw [Set.indicator_of_notMem hb, sub_zero]
        change ¬ (k : ℝ) / 2 < (badCount u : ℝ) at hb
        have hsum : (goodCount u : ℝ) + (badCount u : ℝ) = (k : ℝ) := by exact_mod_cast hCountSum u
        have hgood : (k : ℝ) / 2 ≤ (goodCount u : ℝ) := by linarith only [le_of_not_gt hb, hsum]
        nlinarith only [mul_le_mul_of_nonneg_left hgood ho]
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
      have hBadNN : 0 ≤ BadSet.indicator Omega u := Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) u
      nlinarith only [hBadNN, (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
  have hWLower : (k : ℝ) / 2 *
      ((∫ u : Shao.Path k, I.indicator Omega u ∂P) - (∫ u, BadSet.indicator Omega u ∂P)) ≤
        ∑ i : Fin k, ∫ u, W i u ∂P := by
    have hh := integral_mono ((hTargetInt.sub hBadInt).const_mul ((k : ℝ) / 2))
      (integrable_finsetSum _ (fun i _ => hWInt i)) hWPoint
    simp only [Pi.sub_apply] at hh
    rw [integral_const_mul, integral_sub hTargetInt hBadInt,
      integral_finsetSum _ (fun i _ => hWInt i)] at hh
    exact hh
  have hRsumLower : (k : ℝ) / 4 *
      ((∫ u : Shao.Path k, I.indicator Omega u ∂P) - (∫ u, BadSet.indicator Omega u ∂P)) ≤
        ∑ i : Fin k, ∫ q, R i q ∂J := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hRLower i)
    rw [← Finset.mul_sum] at hh
    nlinarith only [hWLower, hh]
  have hTargetBound : (∫ u : Shao.Path k, I.indicator Omega u ∂P) ≤
      8000 * H / (theta * (k : ℝ)) * M1 +
        16 * H * theta * ((Real.exp 1) ^ 2 + 1) * M1 +
          (∫ u, BadSet.indicator Omega u ∂P) := by
    have hh := hRsumLower.trans hRsumUpper
    have hd : (∫ u : Shao.Path k, I.indicator Omega u ∂P) -
        (∫ u, BadSet.indicator Omega u ∂P) ≤
      (2 * H * (1000 / theta) * M1 +
        4 * H * theta * ((Real.exp 1) ^ 2 + 1) * (k : ℝ) * M1) / ((k : ℝ) / 4) :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) / 4)).2 (by nlinarith only [hh])
    have he : (2 * H * (1000 / theta) * M1 +
        4 * H * theta * ((Real.exp 1) ^ 2 + 1) * (k : ℝ) * M1) / ((k : ℝ) / 4) =
      8000 * H / (theta * (k : ℝ)) * M1 +
        16 * H * theta * ((Real.exp 1) ^ 2 + 1) * M1 := by
      field_simp
      <;> ring
    rw [he] at hd
    linarith only [hd]
  let U : ℝ := theta + 1 / (theta * (k : ℝ))
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hThetaU : theta ≤ U := by
    exact le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ 1 / (theta * (k : ℝ)))
  have hInvU : 1 / (theta * (k : ℝ)) ≤ U := by dsimp only [U]; linarith only [ht]
  have hSqrtU : 1 / Real.sqrt (k : ℝ) ≤ U := by
    apply (div_le_iff₀ hksqrt).2
    have hh := sq_nonneg (theta * Real.sqrt (k : ℝ) - 1)
    have hsq := Real.sq_sqrt hkr.le
    dsimp only [U]
    apply (le_of_mul_le_mul_right _ (mul_pos ht hkr))
    field_simp
    have hmul := mul_nonneg (sq_nonneg (theta * Real.sqrt (k : ℝ) - 1)) hksqrt.le
    have he1 : theta ^ 2 * Real.sqrt (k : ℝ) ^ 3 = theta ^ 2 * (k : ℝ) * Real.sqrt (k : ℝ) := by
      calc
        _ = theta ^ 2 * Real.sqrt (k : ℝ) ^ 2 * Real.sqrt (k : ℝ) := by ring
        _ = _ := by rw [hsq]
    have he2 : theta * Real.sqrt (k : ℝ) ^ 2 = theta * (k : ℝ) := by rw [hsq]
    nlinarith only [hmul, he1, he2, mul_nonneg ht.le hkr.le]
  let X : ℝ := (v + beta) * U * M1
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hHBudget : H ≤ 4096 * (v + beta) := by dsimp only [H, A]; nlinarith only [hv]
  have hBadFinal : (∫ u : Shao.Path k, BadSet.indicator Omega u ∂P) ≤ X := by
    refine hBadCost.trans (hSqrtU.trans ?_)
    have hvb : 1 ≤ v + beta := by linarith only [hv, hbeta]
    have hm := mul_le_mul hvb hM1One (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
    have hh := mul_le_mul_of_nonneg_left hm hU
    dsimp only [X]
    nlinarith only [hh]
  have hFirstFinal : 8000 * H / (theta * (k : ℝ)) * M1 ≤ 32768000 * X := by
    have hh := mul_le_mul_of_nonneg_right hHBudget (show 0 ≤ 8000 * (1 / (theta * (k : ℝ))) * M1 by positivity)
    have hu := mul_le_mul_of_nonneg_left hInvU (show 0 ≤ 32768000 * (v + beta) * M1 by positivity)
    dsimp only [X]
    simp only [div_eq_mul_inv, one_mul] at hh hu ⊢
    nlinarith only [hh, hu]
  have hSecondFinal : 16 * H * theta * ((Real.exp 1) ^ 2 + 1) * M1 ≤
      65536 * ((Real.exp 1) ^ 2 + 1) * X := by
    have hh := mul_le_mul_of_nonneg_right hHBudget
      (show 0 ≤ 16 * theta * ((Real.exp 1) ^ 2 + 1) * M1 by positivity)
    have hu := mul_le_mul_of_nonneg_left hThetaU
      (show 0 ≤ 65536 * (v + beta) * ((Real.exp 1) ^ 2 + 1) * M1 by positivity)
    dsimp only [X]
    nlinarith only [hh, hu]
  let CE : ℝ := 32768001 + 65536 * ((Real.exp 1) ^ 2 + 1)
  have hCE : 0 ≤ CE := by dsimp only [CE]; positivity
  have hIntermediate : (∫ u : Shao.Path k, I.indicator Omega u ∂P) ≤ CE * X := by
    dsimp only [CE]
    nlinarith only [hTargetBound, hBadFinal, hFirstFinal, hSecondFinal]
  have hPower : 1 + (Real.exp 1) ^ 2 ≤ (1 + Real.exp 1) ^ 8 := by
    have hh : (1 + Real.exp 1) ^ 2 ≤ (1 + Real.exp 1) ^ 8 :=
      pow_le_pow_right₀ (by linarith only [Real.exp_pos 1] : (1 : ℝ) ≤ 1 + Real.exp 1) (by norm_num)
    nlinarith only [hh, Real.exp_pos 1]
  have hCubicCoeff : CM * (1001 / 1000 : ℝ) ^ 3 ≤ C := by
    have hp : 1 ≤ (1 + Real.exp 1) ^ 8 := by linarith only [hPower, sq_nonneg (Real.exp 1)]
    have hh := mul_le_mul_of_nonneg_right hp (show 0 ≤ 10 ^ 12 * (1 + CM) by positivity)
    dsimp only [C]
    nlinarith only [hh, hCM]
  have hFinalCoeff : 2 * CE * CM ≤ C := by
    have hce : CE ≤ 10 ^ 8 * (1 + (Real.exp 1) ^ 2) := by
      dsimp only [CE]
      nlinarith only [sq_nonneg (Real.exp 1)]
    have hh := mul_le_mul_of_nonneg_right (hce.trans
      (mul_le_mul_of_nonneg_left hPower (by norm_num : (0 : ℝ) ≤ 10 ^ 8)))
      (show 0 ≤ 2 * CM by positivity)
    have hp : 0 ≤ (1 + Real.exp 1) ^ 8 := by positivity
    have hm := mul_nonneg hp (show 0 ≤ 10 ^ 12 * (1 + CM) - 2 * 10 ^ 8 * CM by nlinarith only [hCM])
    dsimp only [C]
    nlinarith only [hh, hm]
  let EF : ℝ := (503 / 1000 : ℝ) * (k : ℝ) * theta ^ 2 + C * (k : ℝ) * theta ^ 3 * beta
  have hExponent : (1002001 / 2000000 : ℝ) * (k : ℝ) * t1 ^ 2 +
      CM * (k : ℝ) * t1 ^ 3 * beta ≤ EF := by
    have hq : (1002001 / 2000000 : ℝ) * (k : ℝ) * t1 ^ 2 ≤
        (503 / 1000 : ℝ) * (k : ℝ) * theta ^ 2 := by
      dsimp only [t1]
      nlinarith only [mul_nonneg hkr.le (sq_nonneg theta)]
    have hc : CM * (k : ℝ) * t1 ^ 3 * beta ≤ C * (k : ℝ) * theta ^ 3 * beta := by
      have hh := mul_le_mul_of_nonneg_right hCubicCoeff
        (show 0 ≤ (k : ℝ) * theta ^ 3 * beta by positivity)
      dsimp only [t1]
      nlinarith only [hh]
    exact add_le_add hq hc
  have hPoly : 1 + (k : ℝ) * t1 ^ 2 ≤ 2 * (1 + (k : ℝ) * theta ^ 2) := by
    dsimp only [t1]
    nlinarith only [mul_nonneg hkr.le (sq_nonneg theta)]
  have hM1Bound : M1 ≤ 2 * CM * (1 + (k : ℝ) * theta ^ 2) * Real.exp EF := by
    have hh := (hM.2 t1 ht1.le ht1B).2
    refine hh.trans ?_
    calc
      _ ≤ CM * (2 * (1 + (k : ℝ) * theta ^ 2)) * Real.exp EF := by gcongr
      _ = _ := by ring
  refine ⟨hTargetInt, ?_⟩
  calc
    _ ≤ CE * X := hIntermediate
    _ ≤ (2 * CE * CM) * ((v + beta) * U *
        (1 + (k : ℝ) * theta ^ 2) * Real.exp EF) := by
      have hh := mul_le_mul_of_nonneg_left hM1Bound (show 0 ≤ CE * (v + beta) * U by positivity)
      dsimp only [X]
      nlinarith only [hh]
    _ ≤ C * ((v + beta) * U * (1 + (k : ℝ) * theta ^ 2) * Real.exp EF) :=
      mul_le_mul_of_nonneg_right hFinalCoeff (by positivity)
    _ = _ := by dsimp only [U, EF]; ring

private theorem pww_tilted_gaussian_quadratic_kernel :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ T M beta theta : ℝ, 0 < T → 0 ≤ M → 0 ≤ beta → 0 ≤ theta →
        IntegrableOn
          (fun s : ℝ => (M + s + beta) ^ 2 * (2 * s / T) *
            Real.exp (-(s ^ 2) / T + theta * s)) (Set.Ioi 0) ∧
          (∫ s : ℝ in Set.Ioi 0,
            (M + s + beta) ^ 2 * (2 * s / T) *
              Real.exp (-(s ^ 2) / T + theta * s)) ≤
            C * (T + beta ^ 2) * (1 + M / Real.sqrt T) ^ 2 *
              (1 + theta * Real.sqrt T) ^ 3 * Real.exp (theta ^ 2 * T / 4) := by
  classical
  let g : ℝ → ℝ := fun u => (1 + |u| ^ 3) * Real.exp (-(u ^ 2))
  have hG0 : Integrable (fun u : ℝ => Real.exp (-(u ^ 2))) := by
    simpa only [one_mul, neg_one_mul] using (integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num))
  have hG3 : Integrable (fun u : ℝ => u ^ 3 * Real.exp (-(u ^ 2))) := by
    simpa only [Real.rpow_natCast, Real.rpow_ofNat, one_mul, neg_one_mul] using
      (integrable_rpow_mul_exp_neg_mul_sq (b := (1 : ℝ)) (s := (3 : ℝ)) (by norm_num) (by norm_num))
  have hG3a : Integrable (fun u : ℝ => |u| ^ 3 * Real.exp (-(u ^ 2))) := by
    convert hG3.norm using 1
    funext u
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  have hGI : Integrable g := by
    convert hG0.add hG3a using 1
    funext u
    dsimp only [g, Pi.add_apply]
    ring
  have hGN (u : ℝ) : 0 ≤ g u := by dsimp only [g]; positivity
  let J : ℝ := ∫ u : ℝ, g u
  have hJ : 0 ≤ J := integral_nonneg hGN
  let C : ℝ := 256 * (1 + J)
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hJ]
  refine ⟨C, hC, ?_⟩
  intro T M beta theta hT hM hBeta ht
  let t : ℝ := Real.sqrt T
  have htp : 0 < t := Real.sqrt_pos.2 hT
  have ht2 : t ^ 2 = T := Real.sq_sqrt hT.le
  let alpha : ℝ := theta * t
  have ha : 0 ≤ alpha := mul_nonneg ht htp.le
  let q : ℝ := 1 + alpha
  have hq : 1 ≤ q := by dsimp only [q]; linarith only [ha]
  let c : ℝ := theta * T / 2
  let u : ℝ → ℝ := fun s => (s - c) / t
  let A : ℝ := (T + beta ^ 2) * (1 + M / t) ^ 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hP : 1 ≤ (1 + M / t) ^ 2 :=
    one_le_pow₀ (by
      have hh : 0 ≤ M / t := by positivity
      linarith only [hh])
  have hAT : T ≤ A := by
    dsimp only [A]
    calc
      _ ≤ T + beta ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hP
  have hAB : beta ^ 2 ≤ A := by
    dsimp only [A]
    calc
      _ ≤ T + beta ^ 2 := le_add_of_nonneg_left hT.le
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hP
  have hAM : M ^ 2 ≤ A := by
    have hm0 : 0 ≤ M / t := div_nonneg hM htp.le
    have hmsq : (M / t) ^ 2 ≤ (1 + M / t) ^ 2 := by nlinarith only [hm0]
    have he : T * (M / t) ^ 2 = M ^ 2 := by rw [← ht2]; field_simp
    calc
      _ = T * (M / t) ^ 2 := he.symm
      _ ≤ T * (1 + M / t) ^ 2 := mul_le_mul_of_nonneg_left hmsq hT.le
      _ ≤ _ := by
        dsimp only [A]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg beta)) (sq_nonneg _)
  have hTriple : (M + beta + t) ^ 2 ≤ 9 * A := by
    have hh : (M + beta + t) ^ 2 ≤ 3 * (M ^ 2 + beta ^ 2 + t ^ 2) := by
      nlinarith only [sq_nonneg (M - beta), sq_nonneg (M - t), sq_nonneg (beta - t)]
    nlinarith only [hh, hAM, hAB, hAT, ht2]
  have huEq (s : ℝ) : s = t * (u s + alpha / 2) := by
    dsimp only [u, alpha, c]
    rw [← ht2]
    field_simp
    ring
  have hExponent (s : ℝ) : -(s ^ 2) / T + theta * s = -(u s) ^ 2 + theta ^ 2 * T / 4 := by
    dsimp only [u, c]
    rw [← ht2]
    field_simp
    ring
  let f : ℝ → ℝ := fun s => (M + s + beta) ^ 2 * (2 * s / T) *
    Real.exp (-(s ^ 2) / T + theta * s)
  let K : ℝ := 256 * A * q ^ 3 / t * Real.exp (theta ^ 2 * T / 4)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hPoint (s : ℝ) (hs : 0 < s) : f s ≤ K * g (u s) := by
    let z : ℝ := |u s|
    have hz : 0 ≤ z := abs_nonneg _
    have huz : u s ≤ z := le_abs_self _
    have hFactor : 1 ≤ q * (1 + z) := one_le_mul_of_one_le_of_one_le hq (by linarith only [hz])
    have hsBound : s ≤ t * (q * (1 + z)) := by
      have hh : u s + alpha / 2 ≤ q * (1 + z) := by
        dsimp only [q]
        nlinarith only [huz, hz, ha, mul_nonneg ha hz]
      exact (huEq s).trans_le (mul_le_mul_of_nonneg_left hh htp.le)
    have hSumBound : M + s + beta ≤ (M + beta + t) * (q * (1 + z)) := by
      have hm := le_mul_of_one_le_right (show 0 ≤ M + beta by positivity) hFactor
      nlinarith only [hm, hsBound]
    have hSquare : (M + s + beta) ^ 2 ≤ 9 * A * (q * (1 + z)) ^ 2 := by
      calc
        _ ≤ ((M + beta + t) * (q * (1 + z))) ^ 2 := by gcongr
        _ = (M + beta + t) ^ 2 * (q * (1 + z)) ^ 2 := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right hTriple (sq_nonneg _)
    have hDensity : 2 * s / T ≤ (2 / t) * (q * (1 + z)) := by
      apply (div_le_iff₀ hT).2
      rw [← ht2]
      have hh := mul_le_mul_of_nonneg_left hsBound (by norm_num : (0 : ℝ) ≤ 2)
      convert hh using 1 <;> field_simp <;> ring
    have hCube : (1 + z) ^ 3 ≤ 8 * (1 + z ^ 3) := by
      by_cases hz1 : z ≤ 1
      · have hh : (1 + z) ^ 3 ≤ (2 : ℝ) ^ 3 := by gcongr; linarith only [hz1]
        nlinarith only [hh, pow_nonneg hz 3]
      · have hz1' : 1 ≤ z := le_of_not_ge hz1
        have hh : (1 + z) ^ 3 ≤ (2 * z) ^ 3 := by gcongr; linarith only [hz1']
        nlinarith only [hh]
    have hPolynomial : (M + s + beta) ^ 2 * (2 * s / T) ≤
        (256 * A * q ^ 3 / t) * (1 + z ^ 3) := by
      calc
        _ ≤ (9 * A * (q * (1 + z)) ^ 2) * ((2 / t) * (q * (1 + z))) := by gcongr
        _ = (18 * A * q ^ 3 / t) * (1 + z) ^ 3 := by ring
        _ ≤ (18 * A * q ^ 3 / t) * (8 * (1 + z ^ 3)) :=
          mul_le_mul_of_nonneg_left hCube (by positivity)
        _ ≤ _ := by
          have hh : 0 ≤ A * q ^ 3 / t * (1 + z ^ 3) := by positivity
          convert mul_le_mul_of_nonneg_right (show (144 : ℝ) ≤ 256 by norm_num) hh using 1 <;> ring
    dsimp only [f, K, g]
    rw [hExponent, Real.exp_add]
    have hh := mul_le_mul_of_nonneg_right hPolynomial
      (show 0 ≤ Real.exp (-(u s) ^ 2) * Real.exp (theta ^ 2 * T / 4) by positivity)
    convert hh using 1 <;> dsimp only [z] <;> ring
  have hGIscaled : Integrable (fun s : ℝ => g (s / t)) := by
    simpa only [div_eq_mul_inv, mul_comm] using hGI.comp_mul_left' (inv_ne_zero htp.ne')
  have hGIshift : Integrable (fun s : ℝ => g (u s)) := hGIscaled.comp_sub_right c
  have hGIntegral : (∫ s : ℝ, g (u s)) = t * J := by
    change (∫ s : ℝ, (fun z : ℝ => g (z / t)) (s - c)) = t * J
    calc
      _ = ∫ s : ℝ, g (s / t) := integral_sub_right_eq_self (fun z : ℝ => g (z / t)) c
      _ = t * J := by rw [Measure.integral_comp_div, abs_of_pos htp, smul_eq_mul]
  have hMajorI : Integrable (fun s : ℝ => K * g (u s)) := hGIshift.const_mul K
  have hfI : IntegrableOn f (Set.Ioi 0) := by
    apply hMajorI.integrableOn.mono' (by exact (show Measurable f by dsimp only [f]; fun_prop).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := hs
    have hn : 0 ≤ f s := by dsimp only [f]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact hPoint s hs0
  refine ⟨hfI, ?_⟩
  calc
    _ ≤ ∫ s : ℝ in Set.Ioi 0, K * g (u s) := by
      apply integral_mono_ae hfI hMajorI.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact hPoint s hs
    _ ≤ ∫ s : ℝ, K * g (u s) := setIntegral_le_integral hMajorI (ae_of_all _ fun s => mul_nonneg hK (hGN _))
    _ = 256 * J * A * q ^ 3 * Real.exp (theta ^ 2 * T / 4) := by
      rw [integral_const_mul, hGIntegral]
      dsimp only [K]
      field_simp
    _ ≤ C * A * q ^ 3 * Real.exp (theta ^ 2 * T / 4) := by
      have hh : 256 * J ≤ C := by dsimp only [C]; linarith only [hJ]
      gcongr
    _ = _ := by dsimp only [A, q, alpha, t]; ring

theorem actual_circular_weighted_true_wall_closed_cdf :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (B : ℝ), 0 < B → (∀ᵐ z : ℝ ∂rho, |z| ≤ B) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ (n : ℕ), 0 < n →
          ∀ x : ℝ, 1 ≤ x → B ≤ Real.sqrt (n : ℝ) / (200 * x) →
            ∀ (r : ℕ), r ≤ n → (n : ℝ) / 2 ≤ (r : ℝ) →
              let P : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => rho)
              let L : Shao.Path r → ℝ := fun a =>
                if hr : 0 < r then
                  sSup {w : ℝ | ∃ i : Fin r, ∃ k : Fin (r + 1),
                    w = Shao.prefixSum a r -
                      2 * ∑ q ∈ Finset.range k.val,
                        a ⟨(i.val + q) % r, Nat.mod_lt _ hr⟩}
                else 0
              ∀ T : ℝ, 0 ≤ T →
                let wall : Shao.Path r → ℝ := fun a =>
                  x * Real.sqrt (Shao.energy a + T)
                let w : Shao.Path r → ℝ := fun a => wall a - Shao.prefixSum a r
                let A : Set (Shao.Path r) := {a | ∀ k : Fin (r + 1),
                  0 < k.val → Shao.prefixSum a k.val < wall a}
                let G : Set (Shao.Path r) := {a | (r : ℝ) / 2 ≤ Shao.energy a}
                ∀ theta v : ℝ, 0 ≤ theta → theta ≤ x / Real.sqrt (r : ℝ) →
                  0 ≤ v →
                  Integrable
                    ((A ∩ G ∩ {a | 0 < w a ∧ w a ≤ v}).indicator
                      (fun a => Real.exp (theta * L a))) P ∧
                    (∫ a : Shao.Path r,
                      (A ∩ G ∩ {a | 0 < w a ∧ w a ≤ v}).indicator
                        (fun a => Real.exp (theta * L a)) a ∂P) ≤
                      C * (v + beta) ^ 2 / (r : ℝ) *
                        (1 + theta * Real.sqrt (r : ℝ)) ^ 5 *
                        Real.exp ((53 / 100 : ℝ) * (r : ℝ) * theta ^ 2 +
                          C * (r : ℝ) * theta ^ 3 * beta + C * theta * B) := by
  classical
  obtain ⟨CE, hCE, hCoord⟩ := pww_weighted_coordinate_concentration
  obtain ⟨CW, hCW, hSurvival⟩ := pww_weighted_closed_lower_survival
  obtain ⟨CM, hCM, hMoment⟩ :=
    Shao.Probability.SourceCircularWitnessMoment.actual_circular_witness_small_parameter_moment
  let D : ℝ := max 1 (max CE (max CW CM))
  let C : ℝ := D + (10 : ℝ) ^ 9 * D ^ 2 * Real.exp ((10 : ℝ) ^ 6 * D ^ 2)
  have hD : 1 ≤ D := le_max_left _ _
  have hCD : D ≤ C := by exact le_add_of_nonneg_right (by positivity)
  have hC : 1 ≤ C := hD.trans hCD
  have hDCM : CM ≤ D := (le_max_right CW CM).trans
    ((le_max_right CE (max CW CM)).trans (le_max_right 1 (max CE (max CW CM))))
  have hDCE : CE ≤ D := (le_max_left CE (max CW CM)).trans (le_max_right 1 (max CE (max CW CM)))
  have hDCW : CW ≤ D := (le_max_left CW CM).trans
    ((le_max_right CE (max CW CM)).trans (le_max_right 1 (max CE (max CW CM))))
  have hCCM : CM ≤ C := hDCM.trans hCD
  refine ⟨C, hC, ?_⟩
  intro rho hprob B hB hs hmean hvar beta n hn x hx hBsmall r hrn hhalf P L T hT wall w A G theta v ht htx hv
  have hbase := boundedQuadraticTilt_density_moments rho B 0 0 hB (le_refl 0) hs
  rcases hbase with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hpows, _⟩
  have h2 := (hpows 2).1
  have h3 := (hpows 3).2.2.1
  have hBetaData := pww_retained_copy_variance rho h2 h3 hmean hvar
  have hbeta : 1 ≤ beta := hBetaData.1
  have hbetaB : beta ≤ B := by
    calc
      _ ≤ ∫ z : ℝ, B * z ^ 2 ∂rho := by
        apply integral_mono_ae h3 (h2.const_mul B)
        filter_upwards [hs] with z hz
        change |z| ^ 3 ≤ B * z ^ 2
        have hh := mul_le_mul_of_nonneg_right hz (sq_nonneg |z|)
        rw [sq_abs] at hh
        rw [pow_succ, sq_abs]
        nlinarith only [hh]
      _ = B := by rw [integral_const_mul, hvar, mul_one]
  have hBone : 1 ≤ B := hbeta.trans hbetaB
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrp : 0 < (r : ℝ) := by linarith only [hhalf, hnp]
  have hr : 0 < r := by exact_mod_cast hrp
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnp
  have hsr : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 hrp
  have hBprod : B * (200 * x) ≤ Real.sqrt (n : ℝ) := (le_div_iff₀ (by positivity)).1 hBsmall
  have hxSqrt : 200 * x ≤ Real.sqrt (n : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hBone (show 0 ≤ 200 * x by positivity)
    nlinarith only [hh, hBprod]
  have hnLarge : 40000 * x ^ 2 ≤ (n : ℝ) := by
    nlinarith only [hxSqrt, Real.sq_sqrt hnp.le, hxp, hsn]
  have hxSq : 1 ≤ x ^ 2 := by nlinarith only [hx, sq_nonneg (x - 1)]
  have hrLarge : 20000 ≤ (r : ℝ) := by nlinarith only [hnLarge, hhalf, hxSq]
  have hSqrtCompare : Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt (r : ℝ) := by
    nlinarith only [Real.sq_sqrt hnp.le, Real.sq_sqrt hrp.le, hsn, hsr, hhalf]
  have htB : theta * B ≤ 1 / 100 := by
    have hh := (le_div_iff₀ hsr).1 htx
    have hm := mul_le_mul_of_nonneg_right hh hB.le
    nlinarith only [hm, hBprod, hSqrtCompare, hsr]
  have hFextSmall : 4 * x * B ≤ Real.sqrt (r : ℝ) := by
    nlinarith only [hBprod, hSqrtCompare, hsr]
  have hEnergyM : Measurable (Shao.energy : Shao.Path r → ℝ) := by
    unfold Shao.energy
    fun_prop
  have hWallM : Measurable wall := by dsimp only [wall]; fun_prop
  have hwM : Measurable w := by
    exact hWallM.sub (Shao.continuous_prefixSum r).measurable
  have hAM : MeasurableSet A := by
    simp only [A, Set.setOf_forall]
    exact MeasurableSet.iInter (fun k : Fin (r + 1) => MeasurableSet.iInter
      (fun _ : 0 < k.val => measurableSet_lt (Shao.continuous_prefixSum k.val).measurable hWallM))
  have hGM : MeasurableSet G := measurableSet_le measurable_const hEnergyM
  have hBandM : MeasurableSet {a : Shao.Path r | 0 < w a ∧ w a ≤ v} :=
    (measurableSet_lt measurable_const hwM).inter (measurableSet_le hwM measurable_const)
  have hEventM : MeasurableSet (A ∩ G ∩ {a : Shao.Path r | 0 < w a ∧ w a ≤ v}) :=
    (hAM.inter hGM).inter hBandM
  have hM := hMoment rho B hB hs hmean hvar r
  change Measurable L ∧ ∀ t : ℝ, 0 ≤ t → t * B ≤ 1 / 10 →
    Integrable (fun a => Real.exp (t * L a)) P ∧
      (∫ a, Real.exp (t * L a) ∂P) ≤ CM * (1 + (r : ℝ) * t ^ 2) *
        Real.exp ((1002001 / 2000000 : ℝ) * (r : ℝ) * t ^ 2 +
          CM * (r : ℝ) * t ^ 3 * beta) at hM
  have hOmegaInt := (hM.2 theta ht (by linarith only [htB])).1
  have hTargetInt := hOmegaInt.indicator hEventM
  refine ⟨hTargetInt, ?_⟩
  by_cases hv0 : v = 0
  · have he : A ∩ G ∩ {a : Shao.Path r | 0 < w a ∧ w a ≤ v} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro a ha
      have h1 := ha.2.1
      have h2 := ha.2.2
      linarith only [h1, h2, hv0]
    rw [he]
    simp only [Set.indicator_empty, integral_zero]
    positivity
  by_cases hlarge : Real.sqrt (r : ℝ) ≤ v
  · have hPref : 1 ≤ (v + beta) ^ 2 / (r : ℝ) := by
      apply (le_div_iff₀ hrp).2
      have hh : Real.sqrt (r : ℝ) ≤ v + beta := by linarith only [hlarge, hbeta]
      nlinarith only [hh, Real.sq_sqrt hrp.le, hsr, hbeta]
    have hz : 0 ≤ theta * Real.sqrt (r : ℝ) := mul_nonneg ht hsr.le
    have hz2 : (theta * Real.sqrt (r : ℝ)) ^ 2 = (r : ℝ) * theta ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hrp.le]
      ring
    have hPoly : 1 + (r : ℝ) * theta ^ 2 ≤ (1 + theta * Real.sqrt (r : ℝ)) ^ 5 := by
      have hh : 1 + (r : ℝ) * theta ^ 2 ≤ (1 + theta * Real.sqrt (r : ℝ)) ^ 2 := by
        nlinarith only [hz, hz2]
      exact hh.trans (pow_le_pow_right₀ (by linarith only [hz]) (by norm_num))
    have hExp : (1002001 / 2000000 : ℝ) * (r : ℝ) * theta ^ 2 +
        CM * (r : ℝ) * theta ^ 3 * beta ≤
      (53 / 100 : ℝ) * (r : ℝ) * theta ^ 2 + C * (r : ℝ) * theta ^ 3 * beta + C * theta * B := by
      have hh := mul_le_mul_of_nonneg_right hCCM
        (show 0 ≤ (r : ℝ) * theta ^ 3 * beta by positivity)
      have hsupp : 0 ≤ C * theta * B := by positivity
      have hquad : 0 ≤ (r : ℝ) * theta ^ 2 := by positivity
      nlinarith only [hh, hsupp, hquad]
    have hNum : CM ≤ C * ((v + beta) ^ 2 / (r : ℝ)) :=
      hCCM.trans (le_mul_of_one_le_right (le_trans zero_le_one hC) hPref)
    calc
      _ ≤ ∫ a : Shao.Path r, Real.exp (theta * L a) ∂P := by
        apply integral_mono hTargetInt hOmegaInt
        intro a
        by_cases ha : a ∈ A ∩ G ∩ {a : Shao.Path r | 0 < w a ∧ w a ≤ v}
        · simp only [Set.indicator_of_mem ha, le_refl]
        · simp only [Set.indicator_of_notMem ha]
          exact (Real.exp_pos _).le
      _ ≤ CM * (1 + (r : ℝ) * theta ^ 2) *
          Real.exp ((1002001 / 2000000 : ℝ) * (r : ℝ) * theta ^ 2 + CM * (r : ℝ) * theta ^ 3 * beta) :=
        (hM.2 theta ht (by linarith only [htB])).2
      _ ≤ CM * (1 + theta * Real.sqrt (r : ℝ)) ^ 5 *
          Real.exp ((53 / 100 : ℝ) * (r : ℝ) * theta ^ 2 + C * (r : ℝ) * theta ^ 3 * beta + C * theta * B) := by
        gcongr
      _ ≤ C * (v + beta) ^ 2 / (r : ℝ) *
          (1 + theta * Real.sqrt (r : ℝ)) ^ 5 *
          Real.exp ((53 / 100 : ℝ) * (r : ℝ) * theta ^ 2 + C * (r : ℝ) * theta ^ 3 * beta + C * theta * B) := by
        have hh := mul_le_mul_of_nonneg_right hNum
          (show 0 ≤ (1 + theta * Real.sqrt (r : ℝ)) ^ 5 *
            Real.exp ((53 / 100 : ℝ) * (r : ℝ) * theta ^ 2 + C * (r : ℝ) * theta ^ 3 * beta + C * theta * B) by positivity)
        convert hh using 1 <;> ring
  have hvp : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
  have hvs : v < Real.sqrt (r : ℝ) := lt_of_not_ge hlarge
  let k : ℕ := r / 2
  let l : ℕ := r - k
  have hkl : k + l = r := by dsimp only [k, l]; omega
  have hrNatLarge : 20000 ≤ r := by exact_mod_cast hrLarge
  have hkNat : 0 < k := by dsimp only [k]; omega
  have hlNat : 0 < l := by dsimp only [k, l]; omega
  have hk3 : (r : ℝ) / 3 ≤ (k : ℝ) := by
    have hh : r ≤ 3 * k := by dsimp only [k]; omega
    have hhr : (r : ℝ) ≤ 3 * (k : ℝ) := by exact_mod_cast hh
    linarith only [hhr]
  have hl3 : (r : ℝ) / 3 ≤ (l : ℝ) := by
    have hh : r ≤ 3 * l := by dsimp only [k, l]; omega
    have hhr : (r : ℝ) ≤ 3 * (l : ℝ) := by exact_mod_cast hh
    linarith only [hhr]
  let lam : ℝ := max theta (1 / Real.sqrt (r : ℝ))
  have hlamTheta : theta ≤ lam := le_max_left _ _
  have hlamSqrt : 1 / Real.sqrt (r : ℝ) ≤ lam := le_max_right _ _
  have hlamp : 0 < lam := (by positivity : (0 : ℝ) < 1 / Real.sqrt (r : ℝ)).trans_le hlamSqrt
  have hInvB : (1 / Real.sqrt (r : ℝ)) * B ≤ 1 / 100 := by
    have hh : B ≤ B * x := by nlinarith only [mul_nonneg hB.le (sub_nonneg.2 hx)]
    have hBB : B ≤ Real.sqrt (r : ℝ) / 100 := by nlinarith only [hh, hBprod, hSqrtCompare]
    have hd := (div_le_iff₀ hsr).2 (show B ≤ (1 / 100 : ℝ) * Real.sqrt (r : ℝ) by nlinarith only [hBB])
    simpa only [one_div_mul_eq_div] using hd
  have hlamB : lam * B ≤ 1 / 100 := by
    dsimp only [lam]
    rw [max_mul_of_nonneg _ _ hB.le]
    exact max_le htB hInvB
  have hkn : k ≤ r := by dsimp only [k]; omega
  let Pk : Measure (Shao.Path k) := Measure.pi (fun _ : Fin k => rho)
  let Pl : Measure (Shao.Path l) := Measure.pi (fun _ : Fin l => rho)
  let Head : Shao.Path r → Shao.Path k := fun u => Spitzer.head u k hkn
  let Tail : Shao.Path r → Shao.Path l := fun u => Spitzer.tail u k hkn
  let RevTail : Shao.Path r → Shao.Path l := fun u i => Tail u (Fin.rev i)
  run_tac
    let m := "Shao.Probability.SourceTrueEnergyStrip".toName
    let n := Lean.mkPrivateNameCore m ("Shao.Probability.tes_head_tail_measurePreserving".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hPhysicalMP".toName)) := $(Lean.mkIdent n)
        $(Lean.mkIdent ("rho".toName)) $(Lean.mkIdent ("r".toName))
        $(Lean.mkIdent ("k".toName)) $(Lean.mkIdent ("hkn".toName))))
    let n := Lean.mkPrivateNameCore m ("Shao.Probability.tes_head_tail_sum".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hPhysicalSum".toName)) := @$(Lean.mkIdent n) $(Lean.mkIdent ("r".toName))))
    let n := Lean.mkPrivateNameCore m ("Shao.Probability.tes_reverse_tail_prefixSum".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hReversePhysical".toName)) := @$(Lean.mkIdent n) $(Lean.mkIdent ("r".toName))))
  have hPairMP : MeasurePreserving (fun u : Shao.Path r => (Head u, Tail u)) P (Pk.prod Pl) := hPhysicalMP
  have hSumSplit (u : Shao.Path r) : Shao.prefixSum u r =
      Shao.prefixSum (Head u) k + Shao.prefixSum (Tail u) l := by
    simpa only [Shao.prefixSum_length, Head, Tail, l] using hPhysicalSum u k hkn (fun z : ℝ => z)
  have hEnergySplit (u : Shao.Path r) : Shao.energy u = Shao.energy (Head u) + Shao.energy (Tail u) := by
    simpa only [Shao.energy, Head, Tail, l] using hPhysicalSum u k hkn (fun z : ℝ => z ^ 2)
  have hRevPrefix (u : Shao.Path r) (j : ℕ) (hj : j ≤ l) :
      Shao.prefixSum (RevTail u) j = Shao.prefixSum u r - Shao.prefixSum u (r - j) :=
    hReversePhysical u k hkn j hj
  let AliveTail : Set (Shao.Path l) := {b | ∀ j : Fin (l + 1), -v ≤ Shao.prefixSum (fun i : Fin l => b (Fin.rev i)) j.val}
  have hTailSurvival (u : Shao.Path r)
      (hu : u ∈ A ∩ G ∩ {u : Shao.Path r | 0 < w u ∧ w u ≤ v}) : Tail u ∈ AliveTail := by
    intro j
    have hj : j.val ≤ l := by omega
    have hidx : r - j.val ≤ r := Nat.sub_le _ _
    have hpos : 0 < r - j.val := by dsimp only [l] at hj; omega
    have ha := hu.1.1 ⟨r - j.val, by omega⟩ hpos
    change Shao.prefixSum u (r - j.val) < wall u at ha
    have hwv := hu.2.2
    change wall u - Shao.prefixSum u r ≤ v at hwv
    change -v ≤ Shao.prefixSum (RevTail u) j.val
    rw [hRevPrefix u j.val hj]
    linarith only [ha, hwv]
  let LL : (N : ℕ) → Shao.Path N → ℝ := fun N u =>
    if hN : 0 < N then
      sSup {w : ℝ | ∃ i : Fin N, ∃ q : Fin (N + 1),
        w = Shao.prefixSum u N - 2 * ∑ a ∈ Finset.range q.val,
          u ⟨(i.val + a) % N, Nat.mod_lt _ hN⟩}
    else 0
  have hLLTransport (i j : ℕ) (h : i = j) (u : Shao.Path i) :
      LL i u = LL j (fun q : Fin j => u (Fin.cast h.symm q)) := by
    subst j
    rfl
  let NativeJoin : Shao.Path k → Shao.Path l → Shao.Path (k + l) := fun a b i =>
    if hi : i.val < k then a ⟨i.val, hi⟩ else b ⟨i.val - k, by omega⟩
  have hNativeJoin (u : Shao.Path r) : NativeJoin (Head u) (Tail u) =
      (fun i : Fin (k + l) => u (Fin.cast hkl i)) := by
    funext i
    dsimp only [NativeJoin]
    split_ifs with hi
    · dsimp only [Head, Spitzer.head]
      congr 1
    · dsimp only [Tail, Spitzer.tail]
      congr 1
      apply Fin.ext
      change k + (i.val - k) = i.val
      omega
  have hLConcat (u : Shao.Path r) : L u ≤ LL k (Head u) + LL l (Tail u) := by
    have hh := pww_circular_witness_concatenation k l (Head u) (Tail u)
    change LL (k + l) (NativeJoin (Head u) (Tail u)) ≤ LL k (Head u) + LL l (Tail u) at hh
    rw [hNativeJoin] at hh
    have he := hLLTransport r (k + l) hkl.symm u
    change L u = LL (k + l) (fun q : Fin (k + l) => u (Fin.cast hkl q)) at he
    rwa [← he] at hh
  have hLReverse (b : Shao.Path l) : LL l (fun i : Fin l => b (Fin.rev i)) = LL l b :=
    pww_circular_witness_reversal l b
  have hK := hMoment rho B hB hs hmean hvar k
  have hLm := hMoment rho B hB hs hmean hvar l
  change Measurable (LL k) ∧ _ at hK
  change Measurable (LL l) ∧ _ at hLm
  have hKI : Integrable (fun a => Real.exp (lam * LL k a)) Pk :=
    (hK.2 lam hlamp.le (by linarith only [hlamB])).1
  have hLI : Integrable (fun b => Real.exp (lam * LL l b)) Pl :=
    (hLm.2 lam hlamp.le (by linarith only [hlamB])).1
  let clip : ℝ → ℝ := fun z => max (-B) (min z B)
  let FF : Shao.Path k × Shao.Path l → ℝ := fun p =>
    Shao.prefixSum p.1 k - x * Real.sqrt
      (max ((∑ i : Fin k, (clip (p.1 i)) ^ 2) + Shao.energy p.2) ((r : ℝ) / 2) + T)
  have hFFM : Measurable FF := by
    dsimp only [FF, clip, Shao.energy, Shao.prefixSum]
    fun_prop
  have hAliveM : MeasurableSet AliveTail := by
    simp only [AliveTail, Set.setOf_forall]
    exact MeasurableSet.iInter fun j : Fin (l + 1) =>
      measurableSet_le measurable_const
        ((Shao.continuous_prefixSum j.val).measurable.comp (Measurable.of_eval (fun _ => measurable_pi_apply _)))
  let Epair : Set (Shao.Path k × Shao.Path l) := {p |
    p.2 ∈ AliveTail ∧ -Shao.prefixSum p.2 l - v ≤ FF p ∧ FF p ≤ -Shao.prefixSum p.2 l}
  have hEpairM : MeasurableSet Epair := by
    exact (hAliveM.preimage measurable_snd).inter
      ((measurableSet_le (((Shao.continuous_prefixSum l).measurable.comp measurable_snd).neg.sub measurable_const) hFFM).inter
        (measurableSet_le hFFM ((Shao.continuous_prefixSum l).measurable.comp measurable_snd).neg))
  let HH : Shao.Path k × Shao.Path l → ℝ := Epair.indicator
    (fun p => Real.exp (lam * LL k p.1) * Real.exp (lam * LL l p.2))
  have hHHI : Integrable HH (Pk.prod Pl) := (hKI.mul_prod hLI).indicator hEpairM
  have hHHN (p : Shao.Path k × Shao.Path l) : 0 ≤ HH p :=
    Set.indicator_nonneg (fun p _ => by positivity) p
  have hCompI : Integrable (fun u : Shao.Path r => HH (Head u, Tail u)) P :=
    hPairMP.integrable_comp_of_integrable hHHI
  have hBox : ∀ᵐ u : Shao.Path r ∂P, ∀ i : Fin r, |u i| ≤ B := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun _ : Fin r => rho) i).quasiMeasurePreserving.ae hs
  have hPoint : ∀ᵐ u : Shao.Path r ∂P,
      (A ∩ G ∩ {u | 0 < w u ∧ w u ≤ v}).indicator
        (fun u => Real.exp (theta * L u)) u ≤ HH (Head u, Tail u) := by
    filter_upwards [hBox] with u huBox
    by_cases hu : u ∈ A ∩ G ∩ {u | 0 < w u ∧ w u ≤ v}
    · have hFrontBox (i : Fin k) : |Head u i| ≤ B := huBox _
      have hEnergy : (r : ℝ) / 2 ≤ Shao.energy (Head u) + Shao.energy (Tail u) := by
        rw [← hEnergySplit]
        exact hu.1.2
      have hF := pww_actual_clipped_wall_statistic k (r : ℝ) B x (Shao.energy (Tail u)) T
        hrp hB.le hxp.le (by unfold Shao.energy; positivity) hT hFextSmall
      have hFeq := hF.2.2 (Head u) hFrontBox hEnergy
      change FF (Head u, Tail u) = Shao.prefixSum (Head u) k -
        x * Real.sqrt (Shao.energy (Head u) + Shao.energy (Tail u) + T) at hFeq
      rw [← hEnergySplit] at hFeq
      have heq : FF (Head u, Tail u) = -Shao.prefixSum (Tail u) l - w u := by
        rw [hFeq]
        dsimp only [w, wall]
        rw [hSumSplit]
        ring
      have hp : (Head u, Tail u) ∈ Epair := by
        refine ⟨hTailSurvival u hu, ?_, ?_⟩
        · rw [heq]; linarith only [hu.2.2]
        · rw [heq]; linarith only [hu.2.1]
      rw [Set.indicator_of_mem hu, show HH (Head u, Tail u) =
        Real.exp (lam * LL k (Head u)) * Real.exp (lam * LL l (Tail u)) from Set.indicator_of_mem hp _]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have hLnn : 0 ≤ L u := by
        have hh := (hM.2 0 (le_refl 0) (by norm_num)).2
        run_tac
          let n := Lean.mkPrivateNameCore ("Shao.Probability.SourceCircularWitnessMoment".toName)
            ("Shao.Probability.SourceCircularWitnessMoment.cwm_path_extrema_geometry".toName)
          Lean.Elab.Tactic.evalTactic (← `(tactic|
            have $(Lean.mkIdent ("hGeomR".toName)) := $(Lean.mkIdent n) $(Lean.mkIdent ("r".toName))))
        exact (hGeomR.2.2.2 u).1
      have htheta := mul_le_mul_of_nonneg_right hlamTheta hLnn
      have hconcat := mul_le_mul_of_nonneg_left (hLConcat u) hlamp.le
      nlinarith only [htheta, hconcat]
    · rw [Set.indicator_of_notMem hu]
      exact hHHN _
  have hMapIntegral : (∫ u : Shao.Path r, HH (Head u, Tail u) ∂P) =
      ∫ p, HH p ∂Pk.prod Pl := by
    have hm : AEStronglyMeasurable HH (P.map (fun u : Shao.Path r => (Head u, Tail u))) := by
      rw [hPairMP.map_eq]
      exact hHHI.aestronglyMeasurable
    rw [← hPairMP.map_eq]
    exact (integral_map hPairMP.measurable.aemeasurable hm).symm
  let EK : ℝ := (503 / 1000 : ℝ) * (k : ℝ) * lam ^ 2 + CE * (k : ℝ) * lam ^ 3 * beta
  let KL : ℝ := CE * (v + beta) * (lam + 1 / (lam * (k : ℝ))) *
    (1 + (k : ℝ) * lam ^ 2) * Real.exp EK
  have hKL : 0 ≤ KL := by dsimp only [KL]; positivity
  have hSection (b : Shao.Path l) :
      (∫ a : Shao.Path k, HH (a, b) ∂Pk) ≤
        AliveTail.indicator (fun b => KL * Real.exp (lam * LL l b)) b := by
    by_cases hb : b ∈ AliveTail
    · let F : Shao.Path k → ℝ := fun a => FF (a, b)
      have hF := pww_actual_clipped_wall_statistic k (r : ℝ) B x (Shao.energy b) T
        hrp hB.le hxp.le (by unfold Shao.energy; positivity) hT hFextSmall
      have hFM : Measurable F := hF.1.measurable
      have hc := hCoord rho B hB hs hmean hvar k hkNat lam hlamp hlamB F hFM hF.2.1
        (-Shao.prefixSum b l - v) v hv
      change Integrable _ Pk ∧ (∫ a : Shao.Path k,
        {u | -Shao.prefixSum b l - v ≤ F u ∧ F u ≤ -Shao.prefixSum b l - v + v}.indicator
          (fun u => Real.exp (lam * LL k u)) a ∂Pk) ≤ KL at hc
      have he (a : Shao.Path k) : HH (a, b) =
          ({u | -Shao.prefixSum b l - v ≤ F u ∧ F u ≤ -Shao.prefixSum b l - v + v}.indicator
            (fun u => Real.exp (lam * LL k u)) a) * Real.exp (lam * LL l b) := by
        simp only [HH, Epair, Set.indicator_apply, Set.mem_setOf_eq, F, sub_add_cancel, hb, true_and]
        split_ifs <;> simp only [zero_mul]
      simp_rw [he]
      rw [integral_mul_const, Set.indicator_of_mem hb]
      exact mul_le_mul_of_nonneg_right hc.2 (Real.exp_pos _).le
    · have he : (fun a : Shao.Path k => HH (a, b)) = 0 := by
        funext a
        exact Set.indicator_of_notMem (by intro hh; exact hb hh.1) _
      rw [he, Set.indicator_of_notMem hb]
      change (∫ _ : Shao.Path k, (0 : ℝ) ∂Pk) ≤ 0
      rw [integral_zero]
  let rev : Shao.Path l → Shao.Path l := fun b i => b (Fin.rev i)
  have hRevMP : MeasurePreserving rev Pl Pl :=
    (measurePreserving_piCongrLeft (fun _ : Fin l => rho) Fin.revPerm).symm
  have hTail := hSurvival rho B hB hs hmean hvar l hlNat lam v hlamp.le hlamB hv
  let Alive : Set (Shao.Path l) := {b | ∀ j : Fin (l + 1), -v ≤ Shao.prefixSum b j.val}
  let WT : Shao.Path l → ℝ := AliveTail.indicator (fun b => Real.exp (lam * LL l b))
  have hWTComp (b : Shao.Path l) : WT b =
      Alive.indicator (fun b => Real.exp (lam * LL l b)) (rev b) := by
    by_cases hb : b ∈ AliveTail
    · have hbr : rev b ∈ Alive := hb
      change AliveTail.indicator (fun b => Real.exp (lam * LL l b)) b = _
      rw [Set.indicator_of_mem hb, Set.indicator_of_mem hbr]
      change Real.exp (lam * LL l b) = Real.exp (lam * LL l (fun i => b (Fin.rev i)))
      rw [hLReverse]
    · have hbr : rev b ∉ Alive := hb
      change AliveTail.indicator (fun b => Real.exp (lam * LL l b)) b = _
      rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hbr]
  have hWTI : Integrable WT Pl := by
    have hh := hRevMP.integrable_comp_of_integrable hTail.1
    convert hh using 1
    funext b
    exact hWTComp b
  have hWTIntegral : (∫ b, WT b ∂Pl) = ∫ b : Shao.Path l,
      Alive.indicator (fun b => Real.exp (lam * LL l b)) b ∂Pl := by
    have hm : AEStronglyMeasurable (Alive.indicator (fun b => Real.exp (lam * LL l b)))
        (Pl.map rev) := by rw [hRevMP.map_eq]; exact hTail.1.aestronglyMeasurable
    have hi := integral_map hRevMP.measurable.aemeasurable hm
    rw [hRevMP.map_eq] at hi
    calc
      _ = ∫ b, Alive.indicator (fun b => Real.exp (lam * LL l b)) (rev b) ∂Pl :=
        integral_congr_ae (ae_of_all _ hWTComp)
      _ = _ := hi.symm
  have hProdBound : (∫ p, HH p ∂Pk.prod Pl) ≤
      KL * (CW * (v + beta) / Real.sqrt (l : ℝ) *
        (1 + (l : ℝ) * lam ^ 2) *
        Real.exp ((253 / 500 : ℝ) * (l : ℝ) * lam ^ 2 +
          CW * (l : ℝ) * lam ^ 3 * beta + CW * lam * (B + v))) := by
    calc
      _ = ∫ b, ∫ a, HH (a, b) ∂Pk ∂Pl := integral_prod_symm HH hHHI
      _ ≤ ∫ b, KL * WT b ∂Pl := by
        apply integral_mono hHHI.integral_prod_right (hWTI.const_mul KL)
        intro b
        convert hSection b using 1
        simp only [WT, Set.indicator_apply]
        split_ifs <;> simp only [mul_zero]
      _ = KL * ∫ b, WT b ∂Pl := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hWTIntegral ▸ hTail.2) hKL
  have hTotal : (∫ u : Shao.Path r,
      (A ∩ G ∩ {u | 0 < w u ∧ w u ≤ v}).indicator
        (fun u => Real.exp (theta * L u)) u ∂P) ≤
      CE * CW * (v + beta) ^ 2 * (lam + 1 / (lam * (k : ℝ))) /
        Real.sqrt (l : ℝ) * (1 + (k : ℝ) * lam ^ 2) * (1 + (l : ℝ) * lam ^ 2) *
        Real.exp ((503 / 1000 : ℝ) * (k : ℝ) * lam ^ 2 +
          (253 / 500 : ℝ) * (l : ℝ) * lam ^ 2 +
          (CE * (k : ℝ) + CW * (l : ℝ)) * lam ^ 3 * beta + CW * lam * B + CW * lam * v) := by
    calc
      _ ≤ ∫ u : Shao.Path r, HH (Head u, Tail u) ∂P := integral_mono_ae hTargetInt hCompI hPoint
      _ = ∫ p, HH p ∂Pk.prod Pl := hMapIntegral
      _ ≤ _ := hProdBound
      _ = _ := by
        have he : (503 / 1000 : ℝ) * (k : ℝ) * lam ^ 2 +
            (253 / 500 : ℝ) * (l : ℝ) * lam ^ 2 +
            (CE * (k : ℝ) + CW * (l : ℝ)) * lam ^ 3 * beta + CW * lam * B + CW * lam * v =
            EK + ((253 / 500 : ℝ) * (l : ℝ) * lam ^ 2 + CW * (l : ℝ) * lam ^ 3 * beta + CW * lam * (B + v)) := by
          dsimp only [EK]; ring
        conv_rhs => rw [he, Real.exp_add]
        dsimp only [KL]
        ring
  have hkp : 0 < (k : ℝ) := by exact_mod_cast hkNat
  have hlp : 0 < (l : ℝ) := by exact_mod_cast hlNat
  have hklr : (k : ℝ) + (l : ℝ) = (r : ℝ) := by exact_mod_cast hkl
  have hkr : (k : ℝ) ≤ (r : ℝ) := by linarith only [hklr, hlp]
  have hlr : (l : ℝ) ≤ (r : ℝ) := by linarith only [hklr, hkp]
  have hsl : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.2 hlp
  let q : ℝ := lam * Real.sqrt (r : ℝ)
  have hq : 1 ≤ q := by exact (div_le_iff₀ hsr).1 hlamSqrt
  have hq2 : q ^ 2 = (r : ℝ) * lam ^ 2 := by
    dsimp only [q]
    rw [mul_pow, Real.sq_sqrt hrp.le]
    ring
  have hrl2 : 1 ≤ (r : ℝ) * lam ^ 2 := by nlinarith only [hq, hq2, sq_nonneg (q - 1)]
  have hU : lam + 1 / (lam * (k : ℝ)) ≤ 4 * lam := by
    have hh := mul_le_mul_of_nonneg_right hk3 (sq_nonneg lam)
    have hi : 1 ≤ 3 * lam ^ 2 * (k : ℝ) := by nlinarith only [hh, hrl2]
    have hd : 1 / (lam * (k : ℝ)) ≤ 3 * lam :=
      (div_le_iff₀ (mul_pos hlamp hkp)).2 (by nlinarith only [hi])
    linarith only [hd]
  have hInvSqrt : 1 / Real.sqrt (l : ℝ) ≤ 2 / Real.sqrt (r : ℝ) := by
    apply (div_le_div_iff₀ hsl hsr).2
    nlinarith only [Real.sq_sqrt hlp.le, Real.sq_sqrt hrp.le, hsr, hsl, hl3]
  have hPolyK : 1 + (k : ℝ) * lam ^ 2 ≤ (1 + q) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hkr (sq_nonneg lam)
    nlinarith only [hh, hq2, hq]
  have hPolyL : 1 + (l : ℝ) * lam ^ 2 ≤ (1 + q) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hlr (sq_nonneg lam)
    nlinarith only [hh, hq2, hq]
  have hPrefactor : (lam + 1 / (lam * (k : ℝ))) / Real.sqrt (l : ℝ) *
      (1 + (k : ℝ) * lam ^ 2) * (1 + (l : ℝ) * lam ^ 2) ≤
        8 / (r : ℝ) * (1 + q) ^ 5 := by
    calc
      _ = (lam + 1 / (lam * (k : ℝ))) * (1 / Real.sqrt (l : ℝ)) *
          (1 + (k : ℝ) * lam ^ 2) * (1 + (l : ℝ) * lam ^ 2) := by ring
      _ ≤ (4 * lam) * (2 / Real.sqrt (r : ℝ)) * (1 + q) ^ 2 * (1 + q) ^ 2 := by gcongr
      _ = 8 / (r : ℝ) * q * (1 + q) ^ 4 := by
        dsimp only [q]
        have hs2 := Real.sq_sqrt hrp.le
        field_simp
        nlinarith only [hs2]
      _ ≤ 8 / (r : ℝ) * (1 + q) ^ 5 := by
        have hh := mul_le_mul_of_nonneg_left
          (show q ≤ 1 + q by linarith) (show 0 ≤ 8 / (r : ℝ) * (1 + q) ^ 4 by positivity)
        convert hh using 1 <;> ring
  have hExpTotal : (503 / 1000 : ℝ) * (k : ℝ) * lam ^ 2 +
      (253 / 500 : ℝ) * (l : ℝ) * lam ^ 2 +
      (CE * (k : ℝ) + CW * (l : ℝ)) * lam ^ 3 * beta + CW * lam * B + CW * lam * v ≤
        (52 / 100 : ℝ) * (r : ℝ) * lam ^ 2 + D * (r : ℝ) * lam ^ 3 * beta +
          D * lam * B + 25 * D ^ 2 := by
    have hc : CE * (k : ℝ) + CW * (l : ℝ) ≤ D * (r : ℝ) := by
      have hk := mul_le_mul_of_nonneg_right hDCE hkp.le
      have hl := mul_le_mul_of_nonneg_right hDCW hlp.le
      calc
        _ ≤ D * (k : ℝ) + D * (l : ℝ) := add_le_add hk hl
        _ = _ := by rw [← mul_add, hklr]
    have hc3 := mul_le_mul_of_nonneg_right hc (show 0 ≤ lam ^ 3 * beta by positivity)
    have hb := mul_le_mul_of_nonneg_right hDCW (show 0 ≤ lam * B by positivity)
    have hvv : CW * lam * v ≤ D * q := by
      have hh := mul_le_mul_of_nonneg_right hDCW (show 0 ≤ lam * v by positivity)
      have hh2 := mul_le_mul_of_nonneg_left hvs.le (show 0 ≤ D * lam by positivity)
      dsimp only [q]
      nlinarith only [hh, hh2]
    have hyoung : D * q ≤ (1 / 100 : ℝ) * (r : ℝ) * lam ^ 2 + 25 * D ^ 2 := by
      nlinarith only [sq_nonneg (q / 10 - 5 * D), hq2]
    have hquad : (503 / 1000 : ℝ) * (k : ℝ) * lam ^ 2 +
        (253 / 500 : ℝ) * (l : ℝ) * lam ^ 2 ≤ (506 / 1000 : ℝ) * (r : ℝ) * lam ^ 2 := by
      nlinarith only [mul_nonneg hkp.le (sq_nonneg lam), hklr]
    nlinarith only [hc3, hb, hvv, hyoung, hquad, mul_nonneg hrp.le (sq_nonneg lam)]
  have hCECW : CE * CW ≤ D ^ 2 := by
    have hh := mul_le_mul hDCE hDCW (le_trans zero_le_one hCW) (le_trans zero_le_one hD)
    nlinarith only [hh]
  have hUnified : (∫ u : Shao.Path r,
      (A ∩ G ∩ {u | 0 < w u ∧ w u ≤ v}).indicator
        (fun u => Real.exp (theta * L u)) u ∂P) ≤
      (8 * D ^ 2 * Real.exp (25 * D ^ 2)) * (v + beta) ^ 2 / (r : ℝ) *
        (1 + q) ^ 5 * Real.exp ((52 / 100 : ℝ) * (r : ℝ) * lam ^ 2 +
          D * (r : ℝ) * lam ^ 3 * beta + D * lam * B) := by
    calc
      _ ≤ CE * CW * (v + beta) ^ 2 * (lam + 1 / (lam * (k : ℝ))) /
          Real.sqrt (l : ℝ) * (1 + (k : ℝ) * lam ^ 2) * (1 + (l : ℝ) * lam ^ 2) *
          Real.exp ((503 / 1000 : ℝ) * (k : ℝ) * lam ^ 2 +
            (253 / 500 : ℝ) * (l : ℝ) * lam ^ 2 +
            (CE * (k : ℝ) + CW * (l : ℝ)) * lam ^ 3 * beta + CW * lam * B + CW * lam * v) := hTotal
      _ = CE * CW * (v + beta) ^ 2 *
          ((lam + 1 / (lam * (k : ℝ))) / Real.sqrt (l : ℝ) *
            (1 + (k : ℝ) * lam ^ 2) * (1 + (l : ℝ) * lam ^ 2)) *
          Real.exp ((503 / 1000 : ℝ) * (k : ℝ) * lam ^ 2 +
            (253 / 500 : ℝ) * (l : ℝ) * lam ^ 2 +
            (CE * (k : ℝ) + CW * (l : ℝ)) * lam ^ 3 * beta + CW * lam * B + CW * lam * v) := by ring
      _ ≤ D ^ 2 * (v + beta) ^ 2 * (8 / (r : ℝ) * (1 + q) ^ 5) *
          Real.exp ((52 / 100 : ℝ) * (r : ℝ) * lam ^ 2 + D * (r : ℝ) * lam ^ 3 * beta +
            D * lam * B + 25 * D ^ 2) := by gcongr
      _ = _ := by rw [Real.exp_add]; ring
  have hConst (a : ℝ) (ha : a ≤ 1000000) :
      256 * D ^ 2 * Real.exp (a * D ^ 2) ≤ C := by
    have hnum : a ≤ (10 : ℝ) ^ 6 := by norm_num; exact ha
    have he := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hnum (sq_nonneg D))
    have hh : 256 * D ^ 2 * Real.exp (a * D ^ 2) ≤
        (10 : ℝ) ^ 9 * D ^ 2 * Real.exp ((10 : ℝ) ^ 6 * D ^ 2) := by
      calc
        _ ≤ (10 : ℝ) ^ 9 * D ^ 2 * Real.exp (a * D ^ 2) := by gcongr; norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)
    exact hh.trans (by dsimp only [C]; linarith only [le_trans zero_le_one hD])
  by_cases htbig : 1 / Real.sqrt (r : ℝ) ≤ theta
  · have hlam : lam = theta := max_eq_left htbig
    have hconst : 8 * D ^ 2 * Real.exp (25 * D ^ 2) ≤ C :=
      (by gcongr; norm_num : 8 * D ^ 2 * Real.exp (25 * D ^ 2) ≤ 256 * D ^ 2 * Real.exp (25 * D ^ 2)).trans
        (hConst 25 (by norm_num))
    have he : (52 / 100 : ℝ) * (r : ℝ) * theta ^ 2 + D * (r : ℝ) * theta ^ 3 * beta + D * theta * B ≤
        (53 / 100 : ℝ) * (r : ℝ) * theta ^ 2 + C * (r : ℝ) * theta ^ 3 * beta + C * theta * B := by
      have hc1 := mul_le_mul_of_nonneg_right hCD (show 0 ≤ (r : ℝ) * theta ^ 3 * beta by positivity)
      have hc2 := mul_le_mul_of_nonneg_right hCD (show 0 ≤ theta * B by positivity)
      nlinarith only [hc1, hc2, mul_nonneg hrp.le (sq_nonneg theta)]
    have hh := hUnified
    dsimp only [q] at hh
    rw [hlam] at hh
    exact hh.trans (by gcongr)
  · have hlam : lam = 1 / Real.sqrt (r : ℝ) := max_eq_right (le_of_not_ge htbig)
    have hqone : q = 1 := by dsimp only [q]; rw [hlam]; field_simp
    have hrEq : (r : ℝ) * lam ^ 2 = 1 := by rw [← hq2, hqone]; norm_num
    have hbetaLam : lam * beta ≤ 1 / 100 :=
      (mul_le_mul_of_nonneg_left hbetaB hlamp.le).trans hlamB
    have he : (52 / 100 : ℝ) * (r : ℝ) * lam ^ 2 + D * (r : ℝ) * lam ^ 3 * beta + D * lam * B +
        25 * D ^ 2 ≤ 26 * D ^ 2 := by
      have heq : (r : ℝ) * lam ^ 3 * beta = lam * beta := by
        calc
          _ = ((r : ℝ) * lam ^ 2) * (lam * beta) := by ring
          _ = _ := by rw [hrEq, one_mul]
      have hb := mul_le_mul_of_nonneg_left hbetaLam (le_trans zero_le_one hD)
      have hbb := mul_le_mul_of_nonneg_left hlamB (le_trans zero_le_one hD)
      have hDsq : D ≤ D ^ 2 := by nlinarith only [hD, sq_nonneg (D - 1)]
      have heqD : D * (r : ℝ) * lam ^ 3 * beta = D * (lam * beta) := by
        calc
          _ = D * ((r : ℝ) * lam ^ 3 * beta) := by ring
          _ = _ := by rw [heq]
      rw [heqD]
      nlinarith only [hb, hbb, hDsq, hD, hrEq]
    have hReduced : (∫ u : Shao.Path r,
        (A ∩ G ∩ {u | 0 < w u ∧ w u ≤ v}).indicator
          (fun u => Real.exp (theta * L u)) u ∂P) ≤
        256 * D ^ 2 * Real.exp (26 * D ^ 2) * (v + beta) ^ 2 / (r : ℝ) := by
      calc
        _ ≤ (8 * D ^ 2 * Real.exp (25 * D ^ 2)) * (v + beta) ^ 2 / (r : ℝ) *
            (1 + q) ^ 5 * Real.exp ((52 / 100 : ℝ) * (r : ℝ) * lam ^ 2 +
              D * (r : ℝ) * lam ^ 3 * beta + D * lam * B) := hUnified
        _ = 256 * D ^ 2 * (v + beta) ^ 2 / (r : ℝ) *
            Real.exp ((52 / 100 : ℝ) * (r : ℝ) * lam ^ 2 +
              D * (r : ℝ) * lam ^ 3 * beta + D * lam * B + 25 * D ^ 2) := by
          rw [hqone]
          conv_rhs => rw [Real.exp_add]
          ring
        _ ≤ _ := by
          have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 he)
            (show 0 ≤ 256 * D ^ 2 * (v + beta) ^ 2 / (r : ℝ) by positivity)
          convert hh using 1 <;> ring
    have hPolyOne : 1 ≤ (1 + theta * Real.sqrt (r : ℝ)) ^ 5 :=
      one_le_pow₀ (by have hh := mul_nonneg ht hsr.le; linarith only [hh])
    have hExpOne : 1 ≤ Real.exp ((53 / 100 : ℝ) * (r : ℝ) * theta ^ 2 +
        C * (r : ℝ) * theta ^ 3 * beta + C * theta * B) := Real.one_le_exp_iff.2 (by positivity)
    calc
      _ ≤ 256 * D ^ 2 * Real.exp (26 * D ^ 2) * (v + beta) ^ 2 / (r : ℝ) := hReduced
      _ ≤ C * (v + beta) ^ 2 / (r : ℝ) := by gcongr; exact hConst 26 (by norm_num)
      _ ≤ _ := by
        have hp : 0 ≤ C * (v + beta) ^ 2 / (r : ℝ) := by positivity
        have hh := le_mul_of_one_le_right hp (one_le_mul_of_one_le_of_one_le hPolyOne hExpOne)
        convert hh using 1 <;> ring

theorem actual_prior_opposite_hit_gaussian_wall_profile :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (B : ℝ), 0 < B → (∀ᵐ z : ℝ ∂rho, |z| ≤ B) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ (n : ℕ), 0 < n →
          ∀ x : ℝ, 1 ≤ x → B ≤ Real.sqrt (n : ℝ) / (200 * x) →
            ∀ (r : ℕ), r ≤ n → (n : ℝ) / 2 ≤ (r : ℝ) →
              let P : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => rho)
              ∀ T M : ℝ, 0 < T → 0 ≤ M →
                let wall : Shao.Path r → ℝ := fun a =>
                  x * Real.sqrt (Shao.energy a + T)
                let w : Shao.Path r → ℝ := fun a => wall a - Shao.prefixSum a r
                let A : Set (Shao.Path r) := {a | ∀ k : Fin (r + 1),
                  0 < k.val → Shao.prefixSum a k.val < wall a}
                let G : Set (Shao.Path r) := {a | (r : ℝ) / 2 ≤ Shao.energy a}
                let Pminus : Set (Shao.Path r) := {a | ∃ k : Fin (r + 1),
                  0 < k.val ∧ Shao.prefixSum a k.val ≤ -wall a}
                let a0 : ℝ := x * Real.sqrt ((r : ℝ) / 2 + T)
                let profile : Shao.Path r → ℝ := fun a =>
                  Real.exp (-((max (w a - M) 0) ^ 2) / T)
                ∀ theta : ℝ, 0 ≤ theta → theta ≤ x / Real.sqrt (r : ℝ) →
                  Integrable ((A ∩ G ∩ Pminus).indicator profile) P ∧
                    (∫ a : Shao.Path r, (A ∩ G ∩ Pminus).indicator profile a ∂P) ≤
                      C * (T + beta ^ 2) / (r : ℝ) *
                        (1 + theta * Real.sqrt (r : ℝ)) ^ 5 *
                        (1 + M / Real.sqrt T) ^ 2 *
                        (1 + theta * Real.sqrt T) ^ 3 *
                        Real.exp ((53 / 100 : ℝ) * (r : ℝ) * theta ^ 2 +
                          C * (r : ℝ) * theta ^ 3 * beta + C * theta * B -
                          3 * theta * a0 + theta * M + theta ^ 2 * T / 4) := by
  classical
  obtain ⟨CF, hCF, hCDF⟩ := actual_circular_weighted_true_wall_closed_cdf
  obtain ⟨CK, hCK, hKernel⟩ := pww_tilted_gaussian_quadratic_kernel
  let C : ℝ := CF * CK + CF + CK + 1
  have hFK : 0 ≤ CF * CK := mul_nonneg (le_trans zero_le_one hCF) (le_trans zero_le_one hCK)
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hCF, hCK, hFK]
  have hCCF : CF ≤ C := by dsimp only [C]; linarith only [hCF, hCK, hFK]
  have hCCK : CF * CK ≤ C := by dsimp only [C]; linarith only [hCF, hCK]
  refine ⟨C, hC, ?_⟩
  intro rho hprob B hB hs hmean hvar beta n hn x hx hBsmall r hrn hhalf P T M hT hM wall w A G Pminus a0 profile theta ht htx
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrp : 0 < (r : ℝ) := by linarith only [hhalf, hnp]
  have hr : 0 < r := by exact_mod_cast hrp
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hsr : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 hrp
  have hBeta : 0 ≤ beta := integral_nonneg (fun z => by positivity)
  have hEnergyM : Measurable (Shao.energy : Shao.Path r → ℝ) := by unfold Shao.energy; fun_prop
  have hWallM : Measurable wall := by dsimp only [wall]; fun_prop
  have hwM : Measurable w := hWallM.sub (Shao.continuous_prefixSum r).measurable
  have hAM : MeasurableSet A := by
    simp only [A, Set.setOf_forall]
    exact MeasurableSet.iInter fun j : Fin (r + 1) => MeasurableSet.iInter fun _ : 0 < j.val =>
      measurableSet_lt (Shao.continuous_prefixSum j.val).measurable hWallM
  have hGM : MeasurableSet G := measurableSet_le measurable_const hEnergyM
  have hPM : MeasurableSet Pminus := by
    simp only [Pminus, Set.setOf_exists]
    exact MeasurableSet.iUnion fun j : Fin (r + 1) =>
      by
        by_cases hj : 0 < j.val
        · simpa only [hj, true_and, Pi.neg_apply] using
            (measurableSet_le (Shao.continuous_prefixSum j.val).measurable hWallM.neg)
        · simp only [hj, false_and, Set.setOf_false, MeasurableSet.empty]
  let E : Set (Shao.Path r) := A ∩ G ∩ Pminus
  have hEM : MeasurableSet E := (hAM.inter hGM).inter hPM
  let L : Shao.Path r → ℝ := fun a =>
    if hr : 0 < r then
      sSup {z : ℝ | ∃ i : Fin r, ∃ k : Fin (r + 1),
        z = Shao.prefixSum a r - 2 * ∑ q ∈ Finset.range k.val,
          a ⟨(i.val + q) % r, Nat.mod_lt _ hr⟩}
    else 0
  have hActualCDF := hCDF rho B hB hs hmean hvar n hn x hx hBsmall r hrn hhalf T hT.le
  have hwPos (a : Shao.Path r) (ha : a ∈ E) : 0 < w a := by
    have hh := ha.1.1 ⟨r, by omega⟩ hr
    change Shao.prefixSum a r < wall a at hh
    exact sub_pos.2 hh
  have hWallLower (a : Shao.Path r) (ha : a ∈ E) : a0 ≤ wall a := by
    have hg : (r : ℝ) / 2 ≤ Shao.energy a := ha.1.2
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (show (r : ℝ) / 2 + T ≤ Shao.energy a + T by linarith only [hg])) hx0
  run_tac
    let n := Lean.mkPrivateNameCore ("Shao.Probability.SourceCircularWitnessMoment".toName)
      ("Shao.Probability.SourceCircularWitnessMoment.cwm_circular_arc_prefix_formula".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hArc".toName)) := $(Lean.mkIdent n)
        $(Lean.mkIdent ("r".toName)) $(Lean.mkIdent ("hr".toName))))
  have hWitness (a : Shao.Path r) (ha : a ∈ E) : 3 * a0 - w a ≤ L a := by
    obtain ⟨j, hj, hhit⟩ := ha.2
    let candidate : Fin r × Fin (r + 1) → ℝ := fun p =>
      Shao.prefixSum a r - 2 * ∑ q ∈ Finset.range p.2.val,
        a ⟨(p.1.val + q) % r, Nat.mod_lt _ hr⟩
    have hFinite : {z : ℝ | ∃ i : Fin r, ∃ j : Fin (r + 1), z = candidate (i, j)}.Finite := by
      apply (Set.finite_range candidate).subset
      rintro z ⟨i, j, rfl⟩
      exact ⟨(i, j), rfl⟩
    have hsup := le_csSup hFinite.bddAbove
      (show candidate (⟨0, hr⟩, j) ∈ {z : ℝ | ∃ i : Fin r, ∃ j : Fin (r + 1), z = candidate (i, j)}
        from ⟨⟨0, hr⟩, j, rfl⟩)
    have hArc0 := hArc a (⟨0, hr⟩ : Fin r) j
    have hjr : j.val ≤ r := by omega
    simp only [Fin.val_zero, zero_add, if_pos hjr, Shao.prefixSum_zero, sub_zero] at hArc0
    have hsup' : Shao.prefixSum a r - 2 * ∑ q ∈ Finset.range j.val,
        a ⟨(0 + q) % r, Nat.mod_lt _ hr⟩ ≤ L a := by
      simpa only [L, dif_pos hr, candidate] using hsup
    simp only [zero_add] at hsup'
    rw [hArc0] at hsup' 
    have hwall := hWallLower a ha
    change Shao.prefixSum a j.val ≤ -wall a at hhit
    change 3 * a0 - (wall a - Shao.prefixSum a r) ≤ L a
    linarith only [hsup', hwall, hhit]
  let K : ℝ := CF / (r : ℝ) * (1 + theta * Real.sqrt (r : ℝ)) ^ 5 *
    Real.exp ((53 / 100 : ℝ) * (r : ℝ) * theta ^ 2 +
      CF * (r : ℝ) * theta ^ 3 * beta + CF * theta * B - 3 * theta * a0)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hECDF (v : ℝ) (hv : 0 ≤ v) :
      P.real {a | a ∈ E ∧ w a ≤ v} ≤ K * (v + beta) ^ 2 * Real.exp (theta * v) := by
    have hb := hActualCDF theta v ht htx hv
    let Ev : Set (Shao.Path r) := {a | a ∈ E ∧ w a ≤ v}
    have hEvM : MeasurableSet Ev := hEM.inter (measurableSet_le hwM measurable_const)
    have hI : Integrable (Ev.indicator (fun _ => (1 : ℝ))) P := (integrable_const 1).indicator hEvM
    have hPoint (a : Shao.Path r) : Ev.indicator (fun _ => (1 : ℝ)) a ≤
        Real.exp (-3 * theta * a0 + theta * v) *
          (A ∩ G ∩ {a | 0 < w a ∧ w a ≤ v}).indicator (fun a => Real.exp (theta * L a)) a := by
      by_cases ha : a ∈ Ev
      · have haa : a ∈ A ∩ G ∩ {a | 0 < w a ∧ w a ≤ v} :=
          ⟨ha.1.1, hwPos a ha.1, ha.2⟩
        rw [Set.indicator_of_mem ha, Set.indicator_of_mem haa, ← Real.exp_add]
        apply Real.one_le_exp_iff.2
        have hh := mul_le_mul_of_nonneg_left (hWitness a ha.1) ht
        have hvv := mul_le_mul_of_nonneg_left ha.2 ht
        nlinarith only [hh, hvv]
      · rw [Set.indicator_of_notMem ha]
        exact mul_nonneg (Real.exp_pos _).le (Set.indicator_nonneg (fun a _ => (Real.exp_pos _).le) a)
    calc
      _ = ∫ a, Ev.indicator (fun _ => (1 : ℝ)) a ∂P := (integral_indicator_one hEvM).symm
      _ ≤ ∫ a, Real.exp (-3 * theta * a0 + theta * v) *
          (A ∩ G ∩ {a | 0 < w a ∧ w a ≤ v}).indicator (fun a => Real.exp (theta * L a)) a ∂P :=
        integral_mono hI (hb.1.const_mul _) hPoint
      _ = Real.exp (-3 * theta * a0 + theta * v) *
          ∫ a, (A ∩ G ∩ {a | 0 < w a ∧ w a ≤ v}).indicator
            (fun a => Real.exp (theta * L a)) a ∂P := integral_const_mul _ _
      _ ≤ Real.exp (-3 * theta * a0 + theta * v) *
          (CF * (v + beta) ^ 2 / (r : ℝ) * (1 + theta * Real.sqrt (r : ℝ)) ^ 5 *
            Real.exp ((53 / 100 : ℝ) * (r : ℝ) * theta ^ 2 +
              CF * (r : ℝ) * theta ^ 3 * beta + CF * theta * B)) :=
        mul_le_mul_of_nonneg_left hb.2 (Real.exp_pos _).le
      _ = _ := by
        dsimp only [K]
        have he : -3 * theta * a0 + theta * v +
            ((53 / 100 : ℝ) * (r : ℝ) * theta ^ 2 + CF * (r : ℝ) * theta ^ 3 * beta + CF * theta * B) =
            ((53 / 100 : ℝ) * (r : ℝ) * theta ^ 2 + CF * (r : ℝ) * theta ^ 3 * beta + CF * theta * B - 3 * theta * a0) + theta * v := by ring
        calc
          _ = (CF * (v + beta) ^ 2 / (r : ℝ) * (1 + theta * Real.sqrt (r : ℝ)) ^ 5) *
              (Real.exp (-3 * theta * a0 + theta * v) *
                Real.exp ((53 / 100 : ℝ) * (r : ℝ) * theta ^ 2 + CF * (r : ℝ) * theta ^ 3 * beta + CF * theta * B)) := by ring
          _ = _ := by rw [← Real.exp_add, he, Real.exp_add]; ring
  have hCake := Shao.Probability.gaussian_wall_profile_layer_cake P E hEM w hwM T M hT hM
  change Integrable (E.indicator profile) P ∧ _ at hCake
  refine ⟨hCake.1, ?_⟩
  have hGaussian := hKernel T M beta theta hT hM hBeta ht
  let f : ℝ → ℝ := fun s => (M + s + beta) ^ 2 * (2 * s / T) *
    Real.exp (-(s ^ 2) / T + theta * s)
  have hMajorI : IntegrableOn (fun s => K * Real.exp (theta * M) * f s) (Set.Ioi 0) :=
    hGaussian.1.const_mul _
  have hScalar : (∫ s : ℝ in Set.Ioi 0,
      P.real {a | a ∈ E ∧ w a ≤ M + s} * ((2 * s / T) * Real.exp (-(s ^ 2) / T))) ≤
      K * Real.exp (theta * M) * (CK * (T + beta ^ 2) *
        (1 + M / Real.sqrt T) ^ 2 * (1 + theta * Real.sqrt T) ^ 3 *
          Real.exp (theta ^ 2 * T / 4)) := by
    calc
      _ ≤ ∫ s : ℝ in Set.Ioi 0, K * Real.exp (theta * M) * f s := by
        apply integral_mono_ae hCake.2.1 hMajorI
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hs0 : 0 < s := hs
        have hh := mul_le_mul_of_nonneg_right (hECDF (M + s) (by linarith only [hM, hs0]))
          (show 0 ≤ (2 * s / T) * Real.exp (-(s ^ 2) / T) by positivity)
        exact hh.trans_eq (by
          dsimp only [f]
          rw [show theta * (M + s) = theta * M + theta * s by ring]
          simp only [Real.exp_add]
          ring)
      _ = K * Real.exp (theta * M) * ∫ s : ℝ in Set.Ioi 0, f s := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hGaussian.2 (by positivity)
  have hExp : (53 / 100 : ℝ) * (r : ℝ) * theta ^ 2 +
      CF * (r : ℝ) * theta ^ 3 * beta + CF * theta * B - 3 * theta * a0 +
      theta * M + theta ^ 2 * T / 4 ≤
      (53 / 100 : ℝ) * (r : ℝ) * theta ^ 2 +
      C * (r : ℝ) * theta ^ 3 * beta + C * theta * B - 3 * theta * a0 +
      theta * M + theta ^ 2 * T / 4 := by
    have h1 := mul_le_mul_of_nonneg_right hCCF (show 0 ≤ (r : ℝ) * theta ^ 3 * beta by positivity)
    have h2 := mul_le_mul_of_nonneg_right hCCF (show 0 ≤ theta * B by positivity)
    nlinarith only [h1, h2]
  calc
    _ = ∫ s : ℝ in Set.Ioi 0,
        P.real {a | a ∈ E ∧ w a ≤ M + s} * ((2 * s / T) * Real.exp (-(s ^ 2) / T)) := hCake.2.2
    _ ≤ K * Real.exp (theta * M) * (CK * (T + beta ^ 2) *
        (1 + M / Real.sqrt T) ^ 2 * (1 + theta * Real.sqrt T) ^ 3 *
          Real.exp (theta ^ 2 * T / 4)) := hScalar
    _ = (CF * CK) * (T + beta ^ 2) / (r : ℝ) *
        (1 + theta * Real.sqrt (r : ℝ)) ^ 5 * (1 + M / Real.sqrt T) ^ 2 *
        (1 + theta * Real.sqrt T) ^ 3 *
        Real.exp ((53 / 100 : ℝ) * (r : ℝ) * theta ^ 2 +
          CF * (r : ℝ) * theta ^ 3 * beta + CF * theta * B -
          3 * theta * a0 + theta * M + theta ^ 2 * T / 4) := by
      dsimp only [K]
      rw [Real.exp_add, Real.exp_add]
      ring
    _ ≤ _ := by gcongr

end Shao.Probability.SourceWeightedPrefixWall
