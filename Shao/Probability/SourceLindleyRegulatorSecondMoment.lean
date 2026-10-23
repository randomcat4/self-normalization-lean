import Shao.Probability.LindleyTelescoping
import Shao.Probability.SourceFourierScale
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Actual Lindley regulator square moments from an explicit survival input

The finite product law pays joint reversal and independence, integrability,
and strict-event disintegration. The quantitative survival bound is retained
as a premise; this module does not produce that source probability estimate.
-/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

noncomputable def lindleyRegulatorSquareCost
    (ν : Measure ℝ) (k : ℕ) (z : ℝ) : ℝ :=
  (max (-z) 0) ^ 2 *
    (Measure.pi (fun _ : Fin k => ν)).real
      {b : Shao.Path k | Shao.maxWithZero b < max (-z) 0}

def lindleyPrefixSurvivalBound
    (ν : Measure ℝ) (N : ℕ) (C : ℝ) : Prop :=
  let V : ℝ := variance (id : ℝ → ℝ) ν
  let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ν) / V
  ∀ k : ℕ, 1 ≤ k → k < N → ∀ r : ℝ, 0 ≤ r →
    (Measure.pi (fun _ : Fin k => ν)).real
        {b : Shao.Path k | Shao.maxWithZero b ≤ r} ≤
      C * min 1 ((r + gamma) /
        (Real.sqrt V * Real.sqrt ((k + 1 : ℕ) : ℝ)))

private theorem state_nonneg {N : ℕ} (a : Shao.Path N)
    (k : ℕ) (hk : k ≤ N) : 0 ≤ Shao.lindleyState a k hk := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact le_max_left _ _

private theorem measurable_state {N : ℕ} (k : ℕ) (hk : k ≤ N) :
    Measurable (fun a : Shao.Path N => Shao.lindleyState a k hk) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact measurable_const.max ((ih (by omega)).add (measurable_pi_apply _))

private theorem measurable_regulator {N : ℕ} (j : Fin N) :
    Measurable (fun a : Shao.Path N => lindleyRegulator a j) :=
  ((measurable_state j.val (Nat.le_of_lt j.is_lt)).add
    (measurable_pi_apply j)).neg.max measurable_const

private theorem negative_part_bounds (z : ℝ) :
    0 ≤ max (-z) 0 ∧ max (-z) 0 ≤ |z| :=
  ⟨le_max_right _ _, max_le (neg_le_abs z) (abs_nonneg z)⟩

private theorem regulator_bounds {N : ℕ} (a : Shao.Path N) (j : Fin N) :
    0 ≤ lindleyRegulator a j ∧ lindleyRegulator a j ≤ max (-(a j)) 0 := by
  refine ⟨le_max_right _ _, ?_⟩
  apply max_le _ (le_max_right _ _)
  have hW := state_nonneg a j.val (Nat.le_of_lt j.is_lt)
  have hn := le_max_left (-(a j)) (0 : ℝ)
  linarith

theorem lindleyRegulator_sq_le_strict_weight
    (N : ℕ) (a : Shao.Path N) (j : Fin N) :
    (lindleyRegulator a j) ^ 2 ≤
      if Shao.lindleyState a j.val (Nat.le_of_lt j.is_lt) <
          max (-(a j)) 0
      then (max (-(a j)) 0) ^ 2
      else 0 := by
  split_ifs with h
  · exact pow_le_pow_left₀ (regulator_bounds a j).1 (regulator_bounds a j).2 2
  · have hW : max (-(a j)) 0 ≤
        Shao.lindleyState a j.val (Nat.le_of_lt j.is_lt) := le_of_not_gt h
    have hn := le_max_left (-(a j)) (0 : ℝ)
    have hr : lindleyRegulator a j = 0 := by
      unfold lindleyRegulator
      rw [max_eq_right (by linarith)]
    simp only [hr, zero_pow (by decide : 2 ≠ 0), le_refl]

private theorem state_prefix {N : ℕ} (a : Shao.Path N)
    (m : ℕ) (hm : m ≤ N) (k : ℕ) (hk : k ≤ m) :
    Shao.lindleyState (Shao.prefixPath a m hm) k hk =
      Shao.lindleyState a k (hk.trans hm) := by
  rw [Shao.lindleyState_eq_maxWithZero_reverse_prefix,
    Shao.lindleyState_eq_maxWithZero_reverse_prefix]
  rfl

private theorem prefix_map_pi (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (N m : ℕ) (hm : m ≤ N) :
    Measure.map (fun a : Shao.Path N => Shao.prefixPath a m hm)
      (Measure.pi (fun _ : Fin N => ν)) =
        Measure.pi (fun _ : Fin m => ν) := by
  let e : Fin m → Fin N := fun t => ⟨t.val, lt_of_lt_of_le t.is_lt hm⟩
  have he : Function.Injective e := by
    intro s t h
    apply Fin.ext
    exact congrArg (fun q : Fin N => q.val) h
  have hI : iIndepFun (fun t : Fin N => Function.eval t)
      (Measure.pi (fun _ : Fin N => ν)) := by
    simpa using (iIndepFun_pi (μ := fun _ : Fin N => ν)
      (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable))
  have hmap := (hI.precomp he).map_fun_eq_pi_map
    (fun t => (measurable_pi_apply (e t)).aemeasurable)
  have hcoord (t : Fin m) :
      Measure.map (fun a : Shao.Path N => a (e t))
        (Measure.pi (fun _ : Fin N => ν)) = ν :=
    (measurePreserving_eval (fun _ : Fin N => ν) (e t)).map_eq
  change Measure.map (fun a : Shao.Path N => fun t : Fin m => a (e t))
    (Measure.pi (fun _ : Fin N => ν)) = Measure.pi (fun _ : Fin m => ν)
  simpa only [hcoord] using hmap

private theorem terminal_state_map (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (k : ℕ) :
    Measure.map (fun b : Shao.Path k => Shao.lindleyState b k le_rfl)
        (Measure.pi (fun _ : Fin k => ν)) =
      Measure.map (fun b : Shao.Path k => Shao.maxWithZero b)
        (Measure.pi (fun _ : Fin k => ν)) := by
  let P : Measure (Shao.Path k) := Measure.pi (fun _ : Fin k => ν)
  let X : Fin k → Shao.Path k → ℝ := fun t a => a t
  have hX (t : Fin k) : Measurable (X t) := measurable_pi_apply t
  have hI : iIndepFun X P :=
    iIndepFun_pi (fun _ : Fin k => measurable_id.aemeasurable)
  have hLaw (t : Fin k) : IdentDistrib (X t) (id : ℝ → ℝ) P ν := by
    refine ⟨(hX t).aemeasurable, measurable_id.aemeasurable, ?_⟩
    exact (measurePreserving_eval (fun _ : Fin k => ν) t).map_eq.trans
      Measure.map_id.symm
  have h := (iid_lindley_energy_identDistrib_maxWithZero hX hI hLaw).comp
    measurable_fst
  change IdentDistrib
    (fun b : Shao.Path k => Shao.lindleyState b k le_rfl)
    (fun b : Shao.Path k => Shao.maxWithZero b) P P at h
  exact h.map_eq

private theorem state_snoc (k : ℕ) (b : Shao.Path k) (z : ℝ) :
    Shao.lindleyState (Fin.snoc b z) k (Nat.le_succ k) =
      Shao.lindleyState b k le_rfl := by
  rw [Shao.lindleyState_eq_maxWithZero_reverse_prefix,
    Shao.lindleyState_length]
  congr 2
  funext t
  exact @Fin.snoc_castSucc k (fun _ : Fin (k + 1) => ℝ) z b t

private theorem last_joint_map (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (k : ℕ) :
    Measure.map (fun a : Shao.Path (k + 1) =>
        (Shao.lindleyState a k (Nat.le_succ k), a (Fin.last k)))
        (Measure.pi (fun _ : Fin (k + 1) => ν)) =
      (Measure.map (fun b : Shao.Path k => Shao.maxWithZero b)
        (Measure.pi (fun _ : Fin k => ν))).prod ν := by
  let P : Measure (Shao.Path k) := Measure.pi (fun _ : Fin k => ν)
  let F : Shao.Path (k + 1) → ℝ × ℝ := fun a =>
    (Shao.lindleyState a k (Nat.le_succ k), a (Fin.last k))
  let T : Shao.Path k → ℝ := fun b => Shao.lindleyState b k le_rfl
  have hF : Measurable F :=
    (measurable_state k (Nat.le_succ k)).prodMk (measurable_pi_apply _)
  have hT : Measurable T := measurable_state k le_rfl
  have hp := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (k + 1) => ν) (Fin.last k)).symm
  have hs : Measure.map F (Measure.pi (fun _ : Fin (k + 1) => ν)) =
      Measure.map (fun p : ℝ × Shao.Path k => (T p.2, p.1)) (ν.prod P) := by
    rw [← hp.map_eq, Measure.map_map hF hp.measurable]
    congr 1
    funext p
    simp only [Function.comp_def, F,
      MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
      Fin.insertNth_last', state_snoc, Fin.snoc_last, T]
  have hswap : Measure.map (Prod.swap : ℝ × Shao.Path k → Shao.Path k × ℝ)
      (ν.prod P) = P.prod ν := Measure.prod_swap
  calc
    _ = Measure.map (fun p : ℝ × Shao.Path k => (T p.2, p.1)) (ν.prod P) := hs
    _ = Measure.map (Prod.map T (id : ℝ → ℝ)) (P.prod ν) := by
      rw [← hswap, Measure.map_map (hT.prodMap measurable_id) measurable_swap]
      rfl
    _ = (Measure.map T P).prod ν := by
      rw [← Measure.map_prod_map P ν hT measurable_id, Measure.map_id]
    _ = _ := by rw [terminal_state_map ν k]

theorem iid_lindleyState_coordinate_map_eq_prod
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (N : ℕ) (j : Fin N) :
    Measure.map
        (fun a : Shao.Path N =>
          (Shao.lindleyState a j.val (Nat.le_of_lt j.is_lt), a j))
        (Measure.pi (fun _ : Fin N => ν)) =
      (Measure.map (fun b : Shao.Path j.val => Shao.maxWithZero b)
        (Measure.pi (fun _ : Fin j.val => ν))).prod ν := by
  let m := j.val + 1
  have hm : m ≤ N := Nat.succ_le_iff.mpr j.is_lt
  let F : Shao.Path m → ℝ × ℝ := fun a =>
    (Shao.lindleyState a j.val (Nat.le_succ _), a (Fin.last j.val))
  have hF : Measurable F :=
    (measurable_state j.val (Nat.le_succ _)).prodMk (measurable_pi_apply _)
  have hpre : Measurable (fun a : Shao.Path N => Shao.prefixPath a m hm) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  have heq : (fun a : Shao.Path N =>
      (Shao.lindleyState a j.val (Nat.le_of_lt j.is_lt), a j)) =
      F ∘ (fun a : Shao.Path N => Shao.prefixPath a m hm) := by
    funext a
    dsimp only [Function.comp_def, F]
    rw [state_prefix]
    rfl
  rw [heq, ← Measure.map_map hF hpre, prefix_map_pi ν N m hm]
  exact last_joint_map ν j.val

private theorem integrable_coordinate_sq (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (N : ℕ) (j : Fin N) :
    Integrable (fun a : Shao.Path N => (a j) ^ 2)
      (Measure.pi (fun _ : Fin N => ν)) :=
  (measurePreserving_eval (fun _ : Fin N => ν) j).integrable_comp_of_integrable h2

private theorem integral_coordinate (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (N : ℕ) (j : Fin N) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ a : Shao.Path N, f (a j) ∂Measure.pi (fun _ : Fin N => ν)) =
      ∫ z : ℝ, f z ∂ν := by
  have hp := measurePreserving_eval (fun _ : Fin N => ν) j
  calc
    _ = ∫ z : ℝ, f z ∂Measure.map (Function.eval j)
        (Measure.pi (fun _ : Fin N => ν)) :=
      (integral_map_of_stronglyMeasurable hp.measurable hf.stronglyMeasurable).symm
    _ = _ := by rw [hp.map_eq]

theorem integrable_lindleyRegulator_sq
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (N : ℕ) (j : Fin N) :
    let P : Measure (Shao.Path N) :=
      Measure.pi (fun _ : Fin N => ν)
    Integrable (fun a : Shao.Path N => (lindleyRegulator a j) ^ 2) P ∧
      (∫ a : Shao.Path N, (lindleyRegulator a j) ^ 2 ∂P) ≤
        ∫ z : ℝ, z ^ 2 ∂ν := by
  dsimp only
  have hdom (a : Shao.Path N) : (lindleyRegulator a j) ^ 2 ≤ (a j) ^ 2 := by
    have hb := (regulator_bounds a j).2.trans (negative_part_bounds (a j)).2
    simpa only [sq_abs] using
      pow_le_pow_left₀ (regulator_bounds a j).1 hb 2
  have hI := integrable_coordinate_sq ν h2 N j
  have hU : Integrable (fun a : Shao.Path N => (lindleyRegulator a j) ^ 2)
      (Measure.pi (fun _ : Fin N => ν)) := by
    apply hI.mono' ((measurable_regulator j).pow_const 2).aestronglyMeasurable
    exact ae_of_all _ (fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hdom a)
  refine ⟨hU, ?_⟩
  calc
    _ ≤ ∫ a : Shao.Path N, (a j) ^ 2 ∂Measure.pi (fun _ : Fin N => ν) :=
      integral_mono hU hI hdom
    _ = _ := integral_coordinate ν N j _ (continuous_id.pow 2).measurable

private noncomputable def strict_square (p : ℝ × ℝ) : ℝ :=
  if p.1 < max (-p.2) 0 then (max (-p.2) 0) ^ 2 else 0

private theorem measurable_strict_square : Measurable strict_square :=
  Measurable.ite
    (measurableSet_lt measurable_fst (measurable_snd.neg.max measurable_const))
    ((measurable_snd.neg.max measurable_const).pow_const 2) measurable_const

private theorem strict_square_bounds (p : ℝ × ℝ) :
    0 ≤ strict_square p ∧ strict_square p ≤ p.2 ^ 2 := by
  unfold strict_square
  split_ifs
  · refine ⟨sq_nonneg _, ?_⟩
    simpa only [sq_abs] using
      pow_le_pow_left₀ (negative_part_bounds p.2).1 (negative_part_bounds p.2).2 2
  · exact ⟨le_rfl, sq_nonneg _⟩

theorem iid_lindleyRegulator_sq_disintegration
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (N : ℕ) (j : Fin N) :
    let P : Measure (Shao.Path N) :=
      Measure.pi (fun _ : Fin N => ν)
    let F : Shao.Path N → ℝ := fun a =>
      if Shao.lindleyState a j.val (Nat.le_of_lt j.is_lt) <
          max (-(a j)) 0
      then (max (-(a j)) 0) ^ 2
      else 0
    Integrable F P ∧
      Integrable (lindleyRegulatorSquareCost ν j.val) ν ∧
      (∫ a : Shao.Path N, F a ∂P) =
        ∫ z : ℝ, lindleyRegulatorSquareCost ν j.val z ∂ν ∧
      (∫ a : Shao.Path N, (lindleyRegulator a j) ^ 2 ∂P) ≤
        ∫ z : ℝ, lindleyRegulatorSquareCost ν j.val z ∂ν := by
  dsimp only
  let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ν)
  let Q : Measure ℝ := Measure.map (fun b : Shao.Path j.val => Shao.maxWithZero b)
    (Measure.pi (fun _ : Fin j.val => ν))
  let T : Shao.Path N → ℝ × ℝ := fun a =>
    (Shao.lindleyState a j.val (Nat.le_of_lt j.is_lt), a j)
  have hT : Measurable T :=
    (measurable_state j.val (Nat.le_of_lt j.is_lt)).prodMk (measurable_pi_apply j)
  have hmap : Measure.map T P = Q.prod ν :=
    iid_lindleyState_coordinate_map_eq_prod ν N j
  have hH : Integrable strict_square (Q.prod ν) := by
    apply (h2.comp_snd Q).mono' measurable_strict_square.aestronglyMeasurable
    exact ae_of_all _ (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (strict_square_bounds p).1]
      exact (strict_square_bounds p).2)
  have hF : Integrable (strict_square ∘ T) P := by
    apply (integrable_map_measure measurable_strict_square.aestronglyMeasurable
      hT.aemeasurable).mp
    rwa [hmap]
  have hinner (z : ℝ) : (∫ w : ℝ, strict_square (w, z) ∂Q) =
      lindleyRegulatorSquareCost ν j.val z := by
    change (∫ w : ℝ,
      ({w : ℝ | w < max (-z) 0}.indicator
        (fun _ : ℝ => (max (-z) 0) ^ 2)) w ∂Q) = _
    rw [integral_indicator_const (μ := Q) ((max (-z) 0) ^ 2)
      (s := {w : ℝ | w < max (-z) 0})
      (measurableSet_lt measurable_id measurable_const)]
    simp only [smul_eq_mul, Q, measureReal_def,
      lindleyRegulatorSquareCost]
    rw [Measure.map_apply
      (f := fun b : Shao.Path j.val => Shao.maxWithZero b)
      (s := {w : ℝ | w < max (-z) 0}) Shao.measurable_maxWithZero
      (show MeasurableSet {w : ℝ | w < max (-z) 0} from measurableSet_Iio)]
    exact mul_comm
      ((Measure.pi (fun _ : Fin j.val => ν)).real
        {b : Shao.Path j.val | Shao.maxWithZero b < max (-z) 0})
      ((max (-z) 0) ^ 2)
  have hcost : Integrable (lindleyRegulatorSquareCost ν j.val) ν := by
    simpa only [hinner] using hH.integral_prod_right
  have heq : (∫ a : Shao.Path N, strict_square (T a) ∂P) =
      ∫ z : ℝ, lindleyRegulatorSquareCost ν j.val z ∂ν := by
    calc
      _ = ∫ p : ℝ × ℝ, strict_square p ∂Measure.map T P :=
        (integral_map_of_stronglyMeasurable hT
          measurable_strict_square.stronglyMeasurable).symm
      _ = ∫ p : ℝ × ℝ, strict_square p ∂Q.prod ν := by rw [hmap]
      _ = ∫ z : ℝ, ∫ w : ℝ, strict_square (w, z) ∂Q ∂ν :=
        integral_prod_symm _ hH
      _ = _ := by simp only [hinner]
  refine ⟨hF, hcost, heq, ?_⟩
  calc
    _ ≤ ∫ a : Shao.Path N, strict_square (T a) ∂P :=
      integral_mono (integrable_lindleyRegulator_sq ν h2 N j).1 hF
        (fun a => lindleyRegulator_sq_le_strict_weight N a j)
    _ = _ := heq

private theorem second_integrable_of_third (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) ν) :
    Integrable (fun z : ℝ => z ^ 2) ν := by
  apply ((integrable_const (1 : ℝ)).add h3).mono'
    (continuous_id.pow 2).aestronglyMeasurable
  exact ae_of_all ν (fun z => by
    change ‖z ^ 2‖ ≤ 1 + |z| ^ 3
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z)]
    have h := mul_nonneg (sq_nonneg (|z| - 1)) (show 0 ≤ |z| + 1 by positivity)
    nlinarith only [h, sq_abs z, abs_nonneg z])

private theorem raw_lyapunov (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) ν) :
    Real.sqrt (∫ z : ℝ, z ^ 2 ∂ν) * (∫ z : ℝ, z ^ 2 ∂ν) ≤
      ∫ z : ℝ, |z| ^ 3 ∂ν := by
  let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂ν
  let b : ℝ := Real.sqrt m2
  have hm2 : 0 ≤ m2 := integral_nonneg (fun z => sq_nonneg z)
  have hb : 0 ≤ b := Real.sqrt_nonneg m2
  have hb2 : b ^ 2 = m2 := Real.sq_sqrt hm2
  have hpoint (z : ℝ) : (3 * b) * z ^ 2 ≤ 2 * |z| ^ 3 + b ^ 3 := by
    have hfactor := mul_nonneg (sq_nonneg (|z| - b))
      (show 0 ≤ 2 * |z| + b by positivity)
    rw [← sq_abs z]
    nlinarith only [hfactor]
  have hint := integral_mono (h2.const_mul (3 * b))
    ((h3.const_mul 2).add (integrable_const (b ^ 3))) hpoint
  change (∫ z : ℝ, (3 * b) * z ^ 2 ∂ν) ≤
    ∫ z : ℝ, 2 * |z| ^ 3 + b ^ 3 ∂ν at hint
  rw [integral_const_mul, integral_add (h3.const_mul 2) (integrable_const (b ^ 3)),
    integral_const_mul] at hint
  simp only [integral_const, probReal_univ, one_smul] at hint
  change (3 * b) * m2 ≤ 2 * (∫ z : ℝ, |z| ^ 3 ∂ν) + b ^ 3 at hint
  have hb3 : b ^ 3 = b * m2 := by rw [pow_succ, hb2]; ring
  change b * m2 ≤ _
  linarith only [hint, hb3]

private theorem raw_second_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν) :
    (∫ z : ℝ, z ^ 2 ∂ν) ≤
      (∫ z : ℝ, |z| ^ 3 ∂ν) / Real.sqrt (variance (id : ℝ → ℝ) ν) := by
  have h2 := second_integrable_of_third ν h3
  have hL2 : MemLp (id : ℝ → ℝ) 2 ν :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr h2
  have hvar := variance_eq_sub hL2
  have hVm2 : variance (id : ℝ → ℝ) ν ≤ ∫ z : ℝ, z ^ 2 ∂ν := by
    rw [hvar]
    exact sub_le_self _ (sq_nonneg _)
  have hm2 : 0 ≤ ∫ z : ℝ, z ^ 2 ∂ν := integral_nonneg (fun z => sq_nonneg z)
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hV)).2
  calc
    _ ≤ (∫ z : ℝ, z ^ 2 ∂ν) * Real.sqrt (∫ z : ℝ, z ^ 2 ∂ν) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hVm2) hm2
    _ ≤ _ := by simpa only [mul_comm] using raw_lyapunov ν h2 h3

theorem iid_lindleyRegulator_one_second_moment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν) :
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂ν
    let P : Measure (Shao.Path 1) :=
      Measure.pi (fun _ : Fin 1 => ν)
    Integrable
        (fun a : Shao.Path 1 =>
          (lindleyRegulator a (Fin.last 0)) ^ 2) P ∧
      (∫ a : Shao.Path 1,
          (lindleyRegulator a (Fin.last 0)) ^ 2 ∂P) =
        ∫ z : ℝ, (max (-z) 0) ^ 2 ∂ν ∧
      (∫ a : Shao.Path 1,
          (lindleyRegulator a (Fin.last 0)) ^ 2 ∂P) ≤
        m3 / Real.sqrt V := by
  dsimp only
  have h2 := second_integrable_of_third ν h3
  have hbase := integrable_lindleyRegulator_sq ν h2 1 (Fin.last 0)
  refine ⟨hbase.1, ?_, hbase.2.trans (raw_second_bound ν h3 hV)⟩
  simpa only [lindleyRegulator, Fin.val_last, Shao.lindleyState_zero, zero_add] using
    integral_coordinate ν 1 (Fin.last 0) (fun z => (max (-z) 0) ^ 2)
      ((measurable_id.neg.max measurable_const).pow_const 2)

theorem iid_lindleyRegulator_second_moment_of_survival
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (hM2 : (∫ z : ℝ, z ^ 2 ∂ν) ≤
      2 * variance (id : ℝ → ℝ) ν)
    (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hSurvival : lindleyPrefixSurvivalBound ν N C) :
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂ν
    let P : Measure (Shao.Path N) :=
      Measure.pi (fun _ : Fin N => ν)
    ∀ j : Fin N,
      Integrable (fun a : Shao.Path N => (lindleyRegulator a j) ^ 2) P ∧
        (∫ a : Shao.Path N, (lindleyRegulator a j) ^ 2 ∂P) ≤
          max 1 (3 * C) * m3 /
            (Real.sqrt V * Real.sqrt ((j.val + 1 : ℕ) : ℝ)) := by
  dsimp only
  let V := variance (id : ℝ → ℝ) ν
  let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂ν
  let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂ν
  let gamma := m3 / V
  have h2 := second_integrable_of_third ν h3
  have hm3 : 0 ≤ m3 := integral_nonneg (fun z => pow_nonneg (abs_nonneg z) 3)
  have hgamma : 0 ≤ gamma := div_nonneg hm3 hV.le
  have hgm : gamma * m2 ≤ 2 * m3 := by
    calc
      _ ≤ gamma * (2 * V) := mul_le_mul_of_nonneg_left hM2 hgamma
      _ = 2 * ((m3 / V) * V) := by dsimp [gamma]; ring
      _ = 2 * m3 := by rw [div_mul_cancel₀ m3 hV.ne']
  intro j
  have hbase := integrable_lindleyRegulator_sq ν h2 N j
  refine ⟨hbase.1, ?_⟩
  by_cases hj : j.val = 0
  · have hfirst := hbase.2.trans (raw_second_bound ν h3 hV)
    have hm : m3 ≤ max 1 (3 * C) * m3 := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) (3 * C)) hm3
    simpa only [hj, zero_add, Nat.cast_one, Real.sqrt_one, mul_one] using
      hfirst.trans (div_le_div_of_nonneg_right hm (Real.sqrt_nonneg V))
  · have hj1 : 1 ≤ j.val := Nat.one_le_iff_ne_zero.mpr hj
    let D := Real.sqrt V * Real.sqrt ((j.val + 1 : ℕ) : ℝ)
    have hD : 0 < D := mul_pos (Real.sqrt_pos.mpr hV)
      (Real.sqrt_pos.mpr (by exact_mod_cast (Nat.succ_pos j.val)))
    have hcost (z : ℝ) : lindleyRegulatorSquareCost ν j.val z ≤
        (C / D) * (|z| ^ 3 + gamma * z ^ 2) := by
      let r := max (-z) 0
      have hr : 0 ≤ r := (negative_part_bounds z).1
      have hrabs : r ≤ |z| := (negative_part_bounds z).2
      have hstrict : (Measure.pi (fun _ : Fin j.val => ν)).real
          {b : Shao.Path j.val | Shao.maxWithZero b < r} ≤
          C * ((r + gamma) / D) := by
        calc
          _ ≤ (Measure.pi (fun _ : Fin j.val => ν)).real
              {b : Shao.Path j.val | Shao.maxWithZero b ≤ r} :=
            measureReal_mono (fun b h =>
              show Shao.maxWithZero b ≤ r from (show Shao.maxWithZero b < r from h).le)
          _ ≤ C * min 1 ((r + gamma) / D) :=
            hSurvival j.val hj1 j.is_lt r hr
          _ ≤ _ := mul_le_mul_of_nonneg_left (min_le_right _ _) hC
      have hr2 : r ^ 2 ≤ z ^ 2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ hr hrabs 2
      have hr3 : r ^ 3 ≤ |z| ^ 3 := pow_le_pow_left₀ hr hrabs 3
      calc
        _ = r ^ 2 * (Measure.pi (fun _ : Fin j.val => ν)).real
            {b : Shao.Path j.val | Shao.maxWithZero b < r} := rfl
        _ ≤ r ^ 2 * (C * ((r + gamma) / D)) :=
          mul_le_mul_of_nonneg_left hstrict (sq_nonneg r)
        _ = (C / D) * (r ^ 3 + gamma * r ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (add_le_add hr3 (mul_le_mul_of_nonneg_left hr2 hgamma))
          (div_nonneg hC hD.le)
    have hdis := iid_lindleyRegulator_sq_disintegration ν h2 N j
    have hupper : Integrable (fun z : ℝ => (C / D) * (|z| ^ 3 + gamma * z ^ 2)) ν :=
      (h3.add (h2.const_mul gamma)).const_mul (C / D)
    have hi := integral_mono hdis.2.1 hupper hcost
    rw [integral_const_mul, integral_add h3 (h2.const_mul gamma), integral_const_mul] at hi
    calc
      _ ≤ ∫ z : ℝ, lindleyRegulatorSquareCost ν j.val z ∂ν := hdis.2.2.2
      _ ≤ (C / D) * (m3 + gamma * m2) := hi
      _ ≤ (C / D) * (3 * m3) :=
        mul_le_mul_of_nonneg_left (by linarith only [hgm]) (div_nonneg hC hD.le)
      _ = (3 * C) * m3 / D := by ring
      _ ≤ max 1 (3 * C) * m3 / D := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) (3 * C)) hm3) hD.le

theorem sourceTruncation_lindleyRegulator_second_moment_of_survival
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (N : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (N : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : Shao.truncationBudget nu N x ≤ epsilon ^ 3 / 8)
    (C : ℝ) (hC : 0 ≤ C) :
    let rho : Measure ℝ :=
      ProbabilityTheory.cond nu {z | |z| ≤ epsilon / (1 + x)}
    let V : ℝ := variance (id : ℝ → ℝ) rho
    let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
    let P : Measure (Shao.Path N) :=
      Measure.pi (fun _ : Fin N => rho)
    lindleyPrefixSurvivalBound rho N C →
      ∀ j : Fin N,
        Integrable (fun a : Shao.Path N => (lindleyRegulator a j) ^ 2) P ∧
          (∫ a : Shao.Path N, (lindleyRegulator a j) ^ 2 ∂P) ≤
            max 1 (3 * C) * m3 /
              (Real.sqrt V * Real.sqrt ((j.val + 1 : ℕ) : ℝ)) := by
  dsimp only
  let rho : Measure ℝ :=
    ProbabilityTheory.cond nu {z | |z| ≤ epsilon / (1 + x)}
  let mu : ℝ := ∫ z : ℝ, z ∂rho
  let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
  let V := variance (id : ℝ → ℝ) rho
  obtain ⟨_, _, hp, _, _, h2r, h3r, _⟩ :=
    Shao.sourceTruncation_law_data nu N h2 hnorm x epsilon hx hepsilon hepsilonHalf hR
  letI : IsProbabilityMeasure rho := hp
  obtain ⟨_, _, hmu, hVeq, _, hVp, hVlo, _⟩ :=
    Shao.sourceTruncation_variance_bounds nu N h2 hnorm hmean x epsilon hx
      hepsilon hepsilonHalf hR
  change (N : ℝ) * mu ^ 2 ≤ (1 / 4 : ℝ) at hmu
  change (1 / 2 : ℝ) ≤ (N : ℝ) * V at hVlo
  have hN : 0 < N := by
    by_contra h
    have hz : N = 0 := Nat.eq_zero_of_not_pos h
    simp only [hz, Nat.cast_zero, zero_mul, zero_ne_one] at hnorm
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hscaled : (N : ℝ) * V = (N : ℝ) * m2 - (N : ℝ) * mu ^ 2 := by
    change V = m2 - mu ^ 2 at hVeq
    rw [hVeq]
    ring
  have hm2V : m2 ≤ 2 * V := by
    by_contra hbad
    have hpos := mul_pos hNp (sub_pos.mpr (lt_of_not_ge hbad))
    nlinarith only [hscaled, hmu, hVlo, hpos]
  exact fun hs => iid_lindleyRegulator_second_moment_of_survival rho h3r hVp hm2V N C hC hs

end Shao.Probability
