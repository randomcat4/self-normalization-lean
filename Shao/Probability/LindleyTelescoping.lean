import Shao.Probability.LindleyLaw
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite reflection defects and the Lindley Duhamel identity

The future kernel is the actual expectation over an independent finite
product sample. Its parameter measurability holds for every measurable
real test. For tests taking values in `[0,1]`, finite-product Fubini proves
the genuine semigroup and iid one-step relation, followed by the finite
Duhamel identity. The strict CDF corollary retains the positive-energy
restriction and the source's strict boundary. Empty paths are included.
-/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The genuine finite-product future expectation, for every starting pair. -/
noncomputable def lindleyFutureKernel (ν : Measure ℝ) (l : ℕ)
    (ψ : ℝ × ℝ → ℝ) (s : ℝ × ℝ) : ℝ :=
  ∫ b : Shao.Path l,
    ψ (s.1 + Shao.prefixSum b l, s.2 + Shao.energy b)
    ∂Measure.pi (fun _ : Fin l => ν)

/-- The actual negative part of the position just before reflection. -/
def lindleyRegulator {n : ℕ} (a : Shao.Path n) (i : Fin n) : ℝ :=
  max (-(Shao.lindleyState a i.val (Nat.le_of_lt i.is_lt) + a i)) 0

/-- The source's reflection defect, with its true partial square sum. -/
noncomputable def lindleyDelta {n : ℕ} (ν : Measure ℝ)
    (ψ : ℝ × ℝ → ℝ) (a : Shao.Path n) (i : Fin n) : ℝ :=
  lindleyFutureKernel ν (n - (i.val + 1)) ψ
      (0, Shao.prefixSquares a (i.val + 1)) -
    lindleyFutureKernel ν (n - (i.val + 1)) ψ
      (-lindleyRegulator a i, Shao.prefixSquares a (i.val + 1))

/-- Reflection changes only the first coordinate; no regularity of the test
is needed for this pointwise identity. -/
theorem lindley_reflection_defect (g : ℝ × ℝ → ℝ) (r q : ℝ) :
    g (max 0 r, q) - g (r, q) =
      g (0, q) - g (-(max (-r) 0), q) := by
  by_cases hr : 0 ≤ r
  · rw [max_eq_right hr, max_eq_right (neg_nonpos.mpr hr)]
    simp
  · have hr' : r ≤ 0 := le_of_not_ge hr
    rw [max_eq_left hr', max_eq_left (neg_nonneg.mpr hr')]
    simp

private theorem prefixSum_succ_at {n : ℕ} (a : Shao.Path n) (i : Fin n) :
    Shao.prefixSum a (i.val + 1) = Shao.prefixSum a i.val + a i := by
  have hf : Finset.univ.filter (fun j : Fin n => j.val < i.val + 1) =
      insert i (Finset.univ.filter (fun j : Fin n => j.val < i.val)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp h) with hlt | heq
      · exact Or.inr hlt
      · exact Or.inl (Fin.ext heq)
    · rintro (h | h)
      · subst j
        exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt h
  unfold Shao.prefixSum
  rw [hf, Finset.sum_insert]
  · exact add_comm _ _
  · simp

private theorem sum_fin_successive_sub {n : ℕ} (f : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, (f i.succ - f i.castSucc)) = f (Fin.last n) - f 0 := by
  rw [Finset.sum_sub_distrib]
  have hfirst := Fin.sum_univ_succ f
  have hlast := Fin.sum_univ_castSucc f
  linarith

/-- Telescope the actual mixed positions `W_k + S_n - S_k`, keeping the
same genuine full energy in every test. This includes an empty path. -/
theorem lindley_pathwise_telescoping {n : ℕ} (a : Shao.Path n)
    (ψ : ℝ × ℝ → ℝ) :
    ψ (Shao.lindleyState a n le_rfl, Shao.energy a) -
        ψ (Shao.prefixSum a n, Shao.energy a) =
      ∑ i : Fin n,
        (ψ (Shao.prefixSum a n - Shao.prefixSum a (i.val + 1),
            Shao.energy a) -
          ψ (Shao.prefixSum a n - Shao.prefixSum a (i.val + 1) -
              lindleyRegulator a i, Shao.energy a)) := by
  let T : Fin (n + 1) → ℝ := fun k =>
    ψ (Shao.lindleyState a k.val (Nat.le_of_lt_succ k.is_lt) +
        Shao.prefixSum a n - Shao.prefixSum a k.val, Shao.energy a)
  have hstep (i : Fin n) :
      T i.succ - T i.castSucc =
        ψ (Shao.prefixSum a n - Shao.prefixSum a (i.val + 1),
          Shao.energy a) -
          ψ (Shao.prefixSum a n - Shao.prefixSum a (i.val + 1) -
            lindleyRegulator a i, Shao.energy a) := by
    let w := Shao.lindleyState a i.val (Nat.le_of_lt i.is_lt)
    let r := w + a i
    let tail := Shao.prefixSum a n - Shao.prefixSum a (i.val + 1)
    have hbefore : w + Shao.prefixSum a n - Shao.prefixSum a i.val =
        r + tail := by
      dsimp [r, tail]
      rw [prefixSum_succ_at a i]
      ring
    have hafter : max 0 r + Shao.prefixSum a n -
        Shao.prefixSum a (i.val + 1) = max 0 r + tail := by
      dsimp [tail]
      ring
    change ψ (Shao.lindleyState a (i.val + 1) _ + Shao.prefixSum a n -
        Shao.prefixSum a (i.val + 1), Shao.energy a) -
      ψ (w + Shao.prefixSum a n - Shao.prefixSum a i.val, Shao.energy a) = _
    rw [Shao.lindleyState_succ]
    change ψ (max 0 r + Shao.prefixSum a n - Shao.prefixSum a (i.val + 1),
        Shao.energy a) -
      ψ (w + Shao.prefixSum a n - Shao.prefixSum a i.val, Shao.energy a) = _
    rw [hafter, hbefore]
    have href := lindley_reflection_defect
      (fun s : ℝ × ℝ => ψ (s.1 + tail, s.2)) r (Shao.energy a)
    simpa only [zero_add, neg_add_eq_sub, tail, lindleyRegulator, r, w] using href
  calc
    _ = T (Fin.last n) - T 0 := by simp [T]
    _ = ∑ i : Fin n, (T i.succ - T i.castSucc) :=
      (sum_fin_successive_sub T).symm
    _ = _ := Finset.sum_congr rfl (fun i _ => hstep i)

/-- An empty future contributes no increment, for any unused base measure. -/
theorem lindleyFutureKernel_zero (ν : Measure ℝ) (ψ : ℝ × ℝ → ℝ)
    (s : ℝ × ℝ) :
    lindleyFutureKernel ν 0 ψ s = ψ s := by
  simp [lindleyFutureKernel, Shao.prefixSum, Shao.energy, measureReal_def]

/-- General parameter-integral measurability; no boundedness of the test is
assumed in this statement or its proof. -/
theorem measurable_lindleyFutureKernel (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (l : ℕ) (ψ : ℝ × ℝ → ℝ)
    (hψ : Measurable ψ) :
    Measurable (lindleyFutureKernel ν l ψ) := by
  have h : Measurable (fun p : (ℝ × ℝ) × Shao.Path l =>
      ψ (p.1.1 + Shao.prefixSum p.2 l, p.1.2 + Shao.energy p.2)) :=
    hψ.comp ((measurable_fst.fst.add
      ((Shao.measurable_prefixSum l).comp measurable_snd)).prodMk
      (measurable_fst.snd.add (Shao.measurable_energy.comp measurable_snd)))
  exact h.stronglyMeasurable.integral_prod_right'.measurable

private theorem integrable_unit_bounded {α : Type*} [MeasurableSpace α]
    (ρ : Measure α) [IsFiniteMeasure ρ] {f : α → ℝ} (hf : Measurable f)
    (h01 : ∀ z, 0 ≤ f z ∧ f z ≤ 1) : Integrable f ρ := by
  apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
  exact ae_of_all ρ (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (h01 z).1]
    exact (h01 z).2)

private theorem measurable_future_integrand {l : ℕ} (ψ : ℝ × ℝ → ℝ)
    (hψ : Measurable ψ) (s : ℝ × ℝ) :
    Measurable (fun b : Shao.Path l =>
      ψ (s.1 + Shao.prefixSum b l, s.2 + Shao.energy b)) :=
  hψ.comp ((measurable_const.add (Shao.measurable_prefixSum l)).prodMk
    (measurable_const.add Shao.measurable_energy))

theorem lindleyFutureKernel_bounds (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (l : ℕ) (ψ : ℝ × ℝ → ℝ)
    (hψ : Measurable ψ) (hψ01 : ∀ s, 0 ≤ ψ s ∧ ψ s ≤ 1)
    (s : ℝ × ℝ) :
    0 ≤ lindleyFutureKernel ν l ψ s ∧
      lindleyFutureKernel ν l ψ s ≤ 1 := by
  have hint := integrable_unit_bounded (Measure.pi (fun _ : Fin l => ν))
    (measurable_future_integrand ψ hψ s) (fun b => hψ01 _)
  constructor
  · exact integral_nonneg (fun b => (hψ01 _).1)
  · have h := integral_mono hint (integrable_const (1 : ℝ)) (fun b => (hψ01 _).2)
    simpa [lindleyFutureKernel, integral_const, measureReal_def] using h

private theorem prefixSum_cons_full {l : ℕ} (z : ℝ) (b : Shao.Path l) :
    Shao.prefixSum (Fin.cons z b) (l + 1) = z + Shao.prefixSum b l := by
  simp only [Shao.prefixSum_length, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

private theorem energy_cons {l : ℕ} (z : ℝ) (b : Shao.Path l) :
    Shao.energy (Fin.cons z b) = z ^ 2 + Shao.energy b := by
  simp only [Shao.energy, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- Separate the actual first future observation from its remaining product
sample; this is proved from the product integral, not imposed recursively. -/
theorem lindleyFutureKernel_succ (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (l : ℕ) (ψ : ℝ × ℝ → ℝ)
    (hψ : Measurable ψ) (hψ01 : ∀ s, 0 ≤ ψ s ∧ ψ s ≤ 1)
    (s : ℝ × ℝ) :
    lindleyFutureKernel ν (l + 1) ψ s =
      ∫ z : ℝ, lindleyFutureKernel ν l ψ
        (s.1 + z, s.2 + z ^ 2) ∂ν := by
  let G : ℝ × Shao.Path l → ℝ := fun p =>
    ψ (s.1 + (p.1 + Shao.prefixSum p.2 l),
      s.2 + (p.1 ^ 2 + Shao.energy p.2))
  have hG : Measurable G :=
    hψ.comp ((measurable_const.add (measurable_fst.add
      ((Shao.measurable_prefixSum l).comp measurable_snd))).prodMk
      (measurable_const.add ((measurable_fst.pow_const 2).add
        (Shao.measurable_energy.comp measurable_snd))))
  have hGI := integrable_unit_bounded
    (ν.prod (Measure.pi (fun _ : Fin l => ν))) hG (fun p => hψ01 _)
  have hpres :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (l + 1) => ν)
      (0 : Fin (l + 1))).symm
  calc
    lindleyFutureKernel ν (l + 1) ψ s =
        ∫ p : ℝ × Shao.Path l, G p ∂ν.prod (Measure.pi (fun _ : Fin l => ν)) := by
      unfold lindleyFutureKernel
      rw [← hpres.integral_comp']
      congr 1
      funext p
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Equiv.coe_fn_mk, Fin.insertNth_zero, cast_eq, prefixSum_cons_full, energy_cons]
      rfl
    _ = ∫ z : ℝ, ∫ b : Shao.Path l, G (z, b)
        ∂Measure.pi (fun _ : Fin l => ν) ∂ν := integral_prod G hGI
    _ = _ := by simp only [G, lindleyFutureKernel, add_assoc]

private theorem measurable_state {n : ℕ} (k : ℕ) (hk : k ≤ n) :
    Measurable (fun a : Shao.Path n => Shao.lindleyState a k hk) := by
  have hp : Measurable (fun a : Shao.Path n => Shao.prefixPath a k hk) :=
    Measurable.of_eval (fun j => measurable_pi_apply _)
  have hr : Measurable (Shao.reversePath : Shao.Path k → Shao.Path k) :=
    Measurable.of_eval (fun j => measurable_pi_apply _)
  simpa only [Shao.lindleyState_eq_maxWithZero_reverse_prefix, Function.comp_def] using
    Shao.measurable_maxWithZero.comp (hr.comp hp)

private theorem measurable_regulator {n : ℕ} (i : Fin n) :
    Measurable (fun a : Shao.Path n => lindleyRegulator a i) :=
  ((measurable_state i.val (Nat.le_of_lt i.is_lt)).add
    (measurable_pi_apply i)).neg.max measurable_const

private theorem integrable_future_composition {α : Type*} [MeasurableSpace α]
    (ρ : Measure α) [IsFiniteMeasure ρ] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (l : ℕ) (ψ : ℝ × ℝ → ℝ) (hψ : Measurable ψ)
    (hψ01 : ∀ s, 0 ≤ ψ s ∧ ψ s ≤ 1)
    (s : α → ℝ × ℝ) (hs : Measurable s) :
    Integrable (fun z => lindleyFutureKernel ν l ψ (s z)) ρ :=
  integrable_unit_bounded ρ ((measurable_lindleyFutureKernel ν l ψ hψ).comp hs)
    (fun z => lindleyFutureKernel_bounds ν l ψ hψ hψ01 (s z))

private theorem prefixSquares_succ_at {n : ℕ} (a : Shao.Path n) (i : Fin n) :
    Shao.prefixSquares a (i.val + 1) = Shao.prefixSquares a i.val + (a i) ^ 2 :=
  prefixSum_succ_at (fun j => (a j) ^ 2) i

private theorem state_prefix_congr {n : ℕ} (a b : Shao.Path n) (k : ℕ)
    (hk : k ≤ n) (hab : ∀ j : Fin n, j.val < k → a j = b j) :
    Shao.lindleyState a k hk = Shao.lindleyState b k hk := by
  have hp : Shao.prefixPath a k hk = Shao.prefixPath b k hk := by
    funext j
    exact hab _ j.is_lt
  rw [Shao.lindleyState_eq_maxWithZero_reverse_prefix,
    Shao.lindleyState_eq_maxWithZero_reverse_prefix, hp]

private theorem squares_prefix_congr {n : ℕ} (a b : Shao.Path n) (k : ℕ)
    (hab : ∀ j : Fin n, j.val < k → a j = b j) :
    Shao.prefixSquares a k = Shao.prefixSquares b k := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [hab j (Finset.mem_filter.mp hj).2]

private theorem state_insertNth {n : ℕ} (i : Fin (n + 1))
    (z : ℝ) (b : Shao.Path n) :
    Shao.lindleyState (Fin.insertNth i z b) i.val (Nat.le_of_lt i.is_lt) =
      Shao.lindleyState (Fin.insertNth i 0 b) i.val (Nat.le_of_lt i.is_lt) := by
  apply state_prefix_congr
  intro j hj
  simp only [Fin.insertNth_apply_below (show j < i from hj)]

private theorem squares_insertNth {n : ℕ} (i : Fin (n + 1))
    (z : ℝ) (b : Shao.Path n) :
    Shao.prefixSquares (Fin.insertNth i z b) i.val =
      Shao.prefixSquares (Fin.insertNth i 0 b) i.val := by
  apply squares_prefix_congr
  intro j hj
  simp only [Fin.insertNth_apply_below (show j < i from hj)]

private theorem integral_pi_insertNth {n : ℕ} (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (F : Shao.Path (n + 1) → ℝ) (hF : Measurable F)
    (hF01 : ∀ a, 0 ≤ F a ∧ F a ≤ 1) (i : Fin (n + 1)) :
    (∫ a : Shao.Path (n + 1), F a ∂Measure.pi (fun _ : Fin (n + 1) => ν)) =
      ∫ b : Shao.Path n, ∫ z : ℝ, F (Fin.insertNth i z b) ∂ν
        ∂Measure.pi (fun _ : Fin n => ν) := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) i).symm
  have hm : Measurable (fun p : ℝ × Shao.Path n => F (Fin.insertNth i p.1 p.2)) := by
    simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv_apply]
      using hF.comp hp.measurable
  calc
    _ = ∫ p : ℝ × Shao.Path n, F (Fin.insertNth i p.1 p.2)
        ∂ν.prod (Measure.pi (fun _ : Fin n => ν)) := by
      rw [← hp.integral_comp']
      rfl
    _ = _ := integral_prod_symm _
      (integrable_unit_bounded _ hm (fun p => hF01 _))

section IID

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} {ν : Measure ℝ}
variable [hμ : IsProbabilityMeasure μ] [hν : IsProbabilityMeasure ν]
variable {X : Fin n → Ω → ℝ}
include hμ hν

private theorem iid_integral_path
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (F : Shao.Path n → ℝ) (hF : Measurable F) :
    (∫ ω, F (samplePath X ω) ∂μ) =
      ∫ a : Shao.Path n, F a ∂Measure.pi (fun _ : Fin n => ν) := by
  simpa only [Function.comp_def, id_eq] using
    ((iid_samplePath_identDistrib hX hIndep hLaw).comp hF).integral_eq

theorem iid_lindley_initial_futureKernel
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (ψ : ℝ × ℝ → ℝ) (hψ : Measurable ψ)
    (hψ01 : ∀ s, 0 ≤ ψ s ∧ ψ s ≤ 1) :
    lindleyFutureKernel ν n ψ (0, 0) =
      ∫ ω, ψ (Shao.prefixSum (samplePath X ω) n,
        Shao.energy (samplePath X ω)) ∂μ := by
  clear hψ01
  have h := (iid_samplePath_identDistrib hX hIndep hLaw).comp
    (hψ.comp ((Shao.measurable_prefixSum n).prodMk Shao.measurable_energy))
  simpa only [lindleyFutureKernel, zero_add, id_eq, Function.comp_def]
    using h.integral_eq.symm

theorem integrable_lindley_test_and_delta
    (hX : ∀ i, Measurable (X i))
    (ψ : ℝ × ℝ → ℝ) (hψ : Measurable ψ)
    (hψ01 : ∀ s, 0 ≤ ψ s ∧ ψ s ≤ 1) :
    Integrable (fun ω => ψ
        (Shao.lindleyState (samplePath X ω) n le_rfl,
          Shao.energy (samplePath X ω))) μ ∧
      Integrable (fun ω => ψ
        (Shao.prefixSum (samplePath X ω) n,
          Shao.energy (samplePath X ω))) μ ∧
      ∀ i : Fin n,
        Integrable (fun ω => lindleyDelta ν ψ (samplePath X ω) i) μ := by
  have hs := measurable_samplePath hX
  have hQ := Shao.measurable_energy.comp hs
  refine ⟨integrable_unit_bounded μ
      (hψ.comp (((measurable_state n le_rfl).comp hs).prodMk hQ))
      (fun ω => hψ01 _),
    integrable_unit_bounded μ
      (hψ.comp (((Shao.measurable_prefixSum n).comp hs).prodMk hQ))
      (fun ω => hψ01 _), ?_⟩
  intro i
  have hQi := (Shao.measurable_prefixSquares (i.val + 1)).comp hs
  have hUi := (measurable_regulator i).comp hs
  exact (integrable_future_composition μ ν (n - (i.val + 1)) ψ hψ hψ01
    (fun ω => (0, Shao.prefixSquares (samplePath X ω) (i.val + 1)))
    (measurable_const.prodMk hQi)).sub
    (integrable_future_composition μ ν (n - (i.val + 1)) ψ hψ hψ01
      (fun ω => (-lindleyRegulator (samplePath X ω) i,
        Shao.prefixSquares (samplePath X ω) (i.val + 1))) (hUi.neg.prodMk hQi))

/-- The unconditioned single-step identity for the actual iid sample. -/
theorem iid_lindley_future_step
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (ψ : ℝ × ℝ → ℝ) (hψ : Measurable ψ)
    (hψ01 : ∀ s, 0 ≤ ψ s ∧ ψ s ≤ 1) (i : Fin n) :
    (∫ ω, lindleyFutureKernel ν (n - (i.val + 1)) ψ
        (Shao.lindleyState (samplePath X ω) i.val
            (Nat.le_of_lt i.is_lt) + X i ω,
          Shao.prefixSquares (samplePath X ω) (i.val + 1)) ∂μ) =
      ∫ ω, lindleyFutureKernel ν (n - i.val) ψ
        (Shao.lindleyState (samplePath X ω) i.val
            (Nat.le_of_lt i.is_lt),
          Shao.prefixSquares (samplePath X ω) i.val) ∂μ := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
    let L : Shao.Path (m + 1) → ℝ := fun a =>
      lindleyFutureKernel ν (m + 1 - (i.val + 1)) ψ
        (Shao.lindleyState a i.val (Nat.le_of_lt i.is_lt) + a i,
          Shao.prefixSquares a (i.val + 1))
    let R : Shao.Path (m + 1) → ℝ := fun a =>
      lindleyFutureKernel ν (m + 1 - i.val) ψ
        (Shao.lindleyState a i.val (Nat.le_of_lt i.is_lt),
          Shao.prefixSquares a i.val)
    have hL : Measurable L :=
      (measurable_lindleyFutureKernel ν _ ψ hψ).comp
        (((measurable_state i.val _).add (measurable_pi_apply i)).prodMk
          (Shao.measurable_prefixSquares (i.val + 1)))
    have hR : Measurable R :=
      (measurable_lindleyFutureKernel ν _ ψ hψ).comp
        ((measurable_state i.val _).prodMk (Shao.measurable_prefixSquares i.val))
    have hL01 : ∀ a, 0 ≤ L a ∧ L a ≤ 1 := fun a =>
      lindleyFutureKernel_bounds ν _ ψ hψ hψ01 _
    have hR01 : ∀ a, 0 ≤ R a ∧ R a ≤ 1 := fun a =>
      lindleyFutureKernel_bounds ν _ ψ hψ hψ01 _
    change (∫ ω, L (samplePath X ω) ∂μ) = ∫ ω, R (samplePath X ω) ∂μ
    rw [iid_integral_path hX hIndep hLaw L hL,
      iid_integral_path hX hIndep hLaw R hR,
      integral_pi_insertNth ν L hL hL01 i, integral_pi_insertNth ν R hR hR01 i]
    apply integral_congr_ae
    exact ae_of_all _ (fun b => by
      have hlen : m + 1 - i.val = (m + 1 - (i.val + 1)) + 1 := by omega
      calc
        (∫ z : ℝ, L (Fin.insertNth i z b) ∂ν) =
            ∫ z : ℝ, lindleyFutureKernel ν (m + 1 - (i.val + 1)) ψ
              (Shao.lindleyState (Fin.insertNth i 0 b) i.val
                  (Nat.le_of_lt i.is_lt) + z,
                Shao.prefixSquares (Fin.insertNth i 0 b) i.val + z ^ 2) ∂ν := by
          apply integral_congr_ae
          exact ae_of_all ν (fun z => by
            dsimp [L]
            rw [prefixSquares_succ_at, Fin.insertNth_apply_same,
              state_insertNth, squares_insertNth])
        _ = lindleyFutureKernel ν (m + 1 - i.val) ψ
            (Shao.lindleyState (Fin.insertNth i 0 b) i.val (Nat.le_of_lt i.is_lt),
              Shao.prefixSquares (Fin.insertNth i 0 b) i.val) := by
          rw [hlen, lindleyFutureKernel_succ ν _ ψ hψ hψ01]
        _ = ∫ z : ℝ, R (Fin.insertNth i z b) ∂ν := by
          simp only [R, state_insertNth, squares_insertNth]
          simp [integral_const, measureReal_def])

/-- The finite Duhamel identity for the genuine reflected recursion and
square sums, with no centering or moment assumption. -/
theorem iid_lindley_telescoping
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (ψ : ℝ × ℝ → ℝ) (hψ : Measurable ψ)
    (hψ01 : ∀ s, 0 ≤ ψ s ∧ ψ s ≤ 1) :
    (∫ ω, ψ (Shao.lindleyState (samplePath X ω) n le_rfl,
        Shao.energy (samplePath X ω)) ∂μ) -
        (∫ ω, ψ (Shao.prefixSum (samplePath X ω) n,
          Shao.energy (samplePath X ω)) ∂μ) =
      ∑ i : Fin n, ∫ ω, lindleyDelta ν ψ (samplePath X ω) i ∂μ := by
  let T : Fin (n + 1) → ℝ := fun k =>
    ∫ ω, lindleyFutureKernel ν (n - k.val) ψ
      (Shao.lindleyState (samplePath X ω) k.val (Nat.le_of_lt_succ k.is_lt),
        Shao.prefixSquares (samplePath X ω) k.val) ∂μ
  have hs := measurable_samplePath hX
  have hstep (i : Fin n) : T i.succ - T i.castSucc =
      ∫ ω, lindleyDelta ν ψ (samplePath X ω) i ∂μ := by
    have hcurr := integrable_future_composition μ ν (n - (i.val + 1)) ψ hψ hψ01
      (fun ω => (Shao.lindleyState (samplePath X ω) (i.val + 1)
          (Nat.succ_le_of_lt i.is_lt),
        Shao.prefixSquares (samplePath X ω) (i.val + 1)))
      (((measurable_state (i.val + 1) (Nat.succ_le_of_lt i.is_lt)).comp hs).prodMk
        ((Shao.measurable_prefixSquares (i.val + 1)).comp hs))
    have hpre := integrable_future_composition μ ν (n - (i.val + 1)) ψ hψ hψ01
      (fun ω => (Shao.lindleyState (samplePath X ω) i.val
          (Nat.le_of_lt i.is_lt) + X i ω,
        Shao.prefixSquares (samplePath X ω) (i.val + 1)))
      ((((measurable_state i.val (Nat.le_of_lt i.is_lt)).comp hs).add (hX i)).prodMk
        ((Shao.measurable_prefixSquares (i.val + 1)).comp hs))
    have hsingle := iid_lindley_future_step hX hIndep hLaw ψ hψ hψ01 i
    change (∫ ω, lindleyFutureKernel ν (n - (i.val + 1)) ψ
        (Shao.lindleyState (samplePath X ω) (i.val + 1) _,
          Shao.prefixSquares (samplePath X ω) (i.val + 1)) ∂μ) -
      (∫ ω, lindleyFutureKernel ν (n - i.val) ψ
        (Shao.lindleyState (samplePath X ω) i.val _,
          Shao.prefixSquares (samplePath X ω) i.val) ∂μ) = _
    rw [← hsingle, ← integral_sub hcurr hpre]
    apply integral_congr_ae
    exact ae_of_all μ (fun ω => by
      dsimp only
      rw [Shao.lindleyState_succ]
      simpa only [lindleyDelta, lindleyRegulator, samplePath] using
        lindley_reflection_defect (lindleyFutureKernel ν (n - (i.val + 1)) ψ)
          (Shao.lindleyState (samplePath X ω) i.val (Nat.le_of_lt i.is_lt) + X i ω)
          (Shao.prefixSquares (samplePath X ω) (i.val + 1)))
  have hlast : T (Fin.last n) = ∫ ω, ψ
      (Shao.lindleyState (samplePath X ω) n le_rfl,
        Shao.energy (samplePath X ω)) ∂μ := by
    simp [T, lindleyFutureKernel_zero]
  have hzero : T 0 = ∫ ω, ψ (Shao.prefixSum (samplePath X ω) n,
      Shao.energy (samplePath X ω)) ∂μ := by
    calc
      T 0 = lindleyFutureKernel ν n ψ (0, 0) := by simp [T, measureReal_def]
      _ = _ := iid_lindley_initial_futureKernel hX hIndep hLaw ψ hψ hψ01
  calc
    _ = T (Fin.last n) - T 0 := by rw [hlast, hzero]
    _ = ∑ i : Fin n, (T i.succ - T i.castSucc) :=
      (sum_fin_successive_sub T).symm
    _ = _ := Finset.sum_congr rfl (fun i _ => hstep i)

/-- The source's strict, positive-energy CDF difference, using joint reversal
to identify the reflected terminal state with the maximum including zero. -/
theorem iid_maxWithZero_strictCDF_difference
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (t : ℝ) (ht : 0 < t) :
    let ψt : ℝ × ℝ → ℝ := fun s =>
      if 0 < s.2 ∧ |s.1| < t * Real.sqrt s.2 then 1 else 0
    (μ {ω | 0 < Shao.energy (samplePath X ω) ∧
        Shao.maxWithZero (samplePath X ω) <
          t * Real.sqrt (Shao.energy (samplePath X ω))}).toReal -
      (μ {ω | 0 < Shao.energy (samplePath X ω) ∧
        |Shao.prefixSum (samplePath X ω) n| <
          t * Real.sqrt (Shao.energy (samplePath X ω))}).toReal =
        ∑ i : Fin n, ∫ ω, lindleyDelta ν ψt (samplePath X ω) i ∂μ := by
  let E : Set (ℝ × ℝ) := {s | 0 < s.2 ∧ |s.1| < t * Real.sqrt s.2}
  let ψt : ℝ × ℝ → ℝ := fun s =>
    if 0 < s.2 ∧ |s.1| < t * Real.sqrt s.2 then 1 else 0
  change _ = ∑ i : Fin n, ∫ ω, lindleyDelta ν ψt (samplePath X ω) i ∂μ
  have hfst : Measurable (Prod.fst : ℝ × ℝ → ℝ) := measurable_fst
  have hsnd : Measurable (Prod.snd : ℝ × ℝ → ℝ) := measurable_snd
  have hE : MeasurableSet E :=
    (measurableSet_lt measurable_const hsnd).inter
      (measurableSet_lt (continuous_abs.measurable.comp hfst)
        (measurable_const.mul (Real.continuous_sqrt.measurable.comp hsnd)))
  have hψt : Measurable ψt := Measurable.ite hE measurable_const measurable_const
  have hψt01 : ∀ s, 0 ≤ ψt s ∧ ψt s ≤ 1 := by
    intro s
    dsimp [ψt]
    split_ifs <;> norm_num
  have hint (Y : Ω → ℝ × ℝ) (hY : Measurable Y) :
      (∫ ω, ψt (Y ω) ∂μ) =
        (μ {ω | 0 < (Y ω).2 ∧ |(Y ω).1| < t * Real.sqrt (Y ω).2}).toReal := by
    have hA : MeasurableSet {ω | 0 < (Y ω).2 ∧
        |(Y ω).1| < t * Real.sqrt (Y ω).2} := hE.preimage hY
    simpa only [ψt, Set.indicator, Set.mem_ofPred_eq, measureReal_def, Pi.one_apply]
      using (integral_indicator_one (μ := μ) hA)
  have hs := measurable_samplePath hX
  have hQ := Shao.measurable_energy.comp hs
  have hW : (∫ ω, ψt (Shao.lindleyState (samplePath X ω) n le_rfl,
      Shao.energy (samplePath X ω)) ∂μ) =
      (μ {ω | 0 < Shao.energy (samplePath X ω) ∧
        Shao.maxWithZero (samplePath X ω) <
          t * Real.sqrt (Shao.energy (samplePath X ω))}).toReal := by
    calc
      _ = ∫ ω, ψt (Shao.maxWithZero (samplePath X ω),
          Shao.energy (samplePath X ω)) ∂μ := by
        simpa only [Function.comp_def] using
          ((iid_lindley_energy_identDistrib_maxWithZero hX hIndep hLaw).comp hψt).integral_eq
      _ = _ := by
        have h := hint
          (fun ω => (Shao.maxWithZero (samplePath X ω), Shao.energy (samplePath X ω)))
          ((Shao.measurable_maxWithZero.comp hs).prodMk hQ)
        simpa only [abs_of_nonneg (Shao.maxWithZero_nonneg _)] using h
  have hS := hint
    (fun ω => (Shao.prefixSum (samplePath X ω) n, Shao.energy (samplePath X ω)))
    (((Shao.measurable_prefixSum n).comp hs).prodMk hQ)
  have htel := iid_lindley_telescoping hX hIndep hLaw ψt hψt hψt01
  rwa [hW, hS] at htel

end IID

end Shao.Probability
