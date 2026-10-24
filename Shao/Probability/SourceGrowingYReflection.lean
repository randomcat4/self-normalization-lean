import Shao.Probability.SourceGrowingKernelBounds
import Shao.Probability.SourceGrowingMicrotimeReflection
import Shao.Probability.SourceLindleyRegulatorEnergyWeightedSecond
import Shao.Probability.SourceLindleySurvival
import Shao.Probability.SourceClockBridge
import Shao.Probability.SourceFullNoiseBridge
import Shao.Probability.LindleySignedBlock
import Shao.Probability.GaussianTail

/-!
Actual growing-threshold reflection sums and smoothed maximum/endpoint comparison.
Source: main.tex 560--645; supplement.tex 568--596, 758--952, 3050--3150.
The early weighted sums, the history-local SIGNED bad-prefix block, and the
good-prefix «macro»/short/micro errors are paid from the original two budgets.
The conditional drift is retained. The maximum is transferred by its genuine
joint law with energy, and the same actual full noise and conditioned iid sample
are used throughout. This module does not assert unsmoothing or original root
closure. Private helper theorems introduce no new definition values.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

private theorem gy_test_data (y : ℝ) :
    Measurable (sourceFourierTest y) ∧
      ∀ p : ℝ × ℝ, 0 ≤ sourceFourierTest y p ∧ sourceFourierTest y p ≤ 1 := by
  constructor
  · have hA : MeasurableSet {p : ℝ × ℝ | |p.1| < y * Real.sqrt p.2} :=
      (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet
    exact (sourceKernelCutoff_data.1.continuous.measurable.comp measurable_snd).mul
      (Measurable.ite hA measurable_const measurable_const)
  · intro p
    unfold sourceFourierTest
    split_ifs
    · simpa using sourceKernelCutoff_data.2.2.1 p.2
    · simp

private theorem gy_noise_test_data (ν : Measure ℝ) (y : ℝ)
    [IsProbabilityMeasure (quadraticFullNoiseLaw ν)] :
    let ψ := fun p : ℝ × ℝ => ∫ z : ℝ × ℝ,
      sourceFourierTest y (p.1 + z.1, p.2 + z.2) ∂quadraticFullNoiseLaw ν
    Measurable ψ ∧ ∀ p, 0 ≤ ψ p ∧ ψ p ≤ 1 := by
  dsimp only
  have hm : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      sourceFourierTest y (p.1.1 + p.2.1, p.1.2 + p.2.2)) :=
    (gy_test_data y).1.comp (by fun_prop)
  refine ⟨hm.stronglyMeasurable.integral_prod_right'.measurable, ?_⟩
  intro p
  have hi : Integrable (fun z : ℝ × ℝ =>
      sourceFourierTest y (p.1 + z.1, p.2 + z.2)) (quadraticFullNoiseLaw ν) :=
    (integrable_const (1 : ℝ)).mono'
      ((gy_test_data y).1.comp (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg ((gy_test_data y).2 _).1]
          using ((gy_test_data y).2 (p.1 + z.1, p.2 + z.2)).2)
  refine ⟨integral_nonneg (fun z => ((gy_test_data y).2 _).1), ?_⟩
  simpa using integral_mono hi (integrable_const (1 : ℝ))
    (fun z => ((gy_test_data y).2 _).2)

private theorem gy_state_nonneg {n : ℕ} (a : Shao.Path n) (k : ℕ) (hk : k ≤ n) :
    0 ≤ Shao.lindleyState a k hk := by
  cases k with
  | zero => rfl
  | succ k => exact le_max_left _ _

private theorem gy_state_measurable {n : ℕ} (k : ℕ) (hk : k ≤ n) :
    Measurable (fun a : Shao.Path n => Shao.lindleyState a k hk) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact measurable_const.max ((ih (by omega)).add (measurable_pi_apply _))

private theorem gy_regulator_measurable {n : ℕ} (j : Fin n) :
    Measurable (fun a : Shao.Path n => lindleyRegulator a j) :=
  ((gy_state_measurable j.val (Nat.le_of_lt j.is_lt)).add
    (measurable_pi_apply j)).neg.max measurable_const

private theorem gy_regulator_bounds {n : ℕ} (a : Shao.Path n) (j : Fin n) :
    0 ≤ lindleyRegulator a j ∧ lindleyRegulator a j ≤ |a j| := by
  refine ⟨le_max_right _ _, max_le ?_ (abs_nonneg _)⟩
  have hs := gy_state_nonneg a j.val (Nat.le_of_lt j.is_lt)
  linarith [neg_le_abs (a j)]

private theorem gy_delta_measurable {n : ℕ} (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (ψ : ℝ × ℝ → ℝ) (hψ : Measurable ψ) (j : Fin n) :
    Measurable (fun a : Shao.Path n => lindleyDelta ν ψ a j) := by
  have hk := measurable_lindleyFutureKernel ν (n - (j.val + 1)) ψ hψ
  exact (hk.comp (measurable_const.prodMk (Shao.measurable_prefixSquares _))).sub
    (hk.comp ((gy_regulator_measurable j).neg.prodMk (Shao.measurable_prefixSquares _)))

private theorem gy_source_scale
    (ν0 : Measure ℝ) [IsProbabilityMeasure ν0] (n : ℕ)
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν0)
    (hn : (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1)
    (hm : (∫ a : ℝ, a ∂ν0) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x) (he : 0 < epsilon) (he2 : epsilon ≤ 1 / 2)
    (hR : Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8) :
    let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
    let mu : ℝ := ∫ a : ℝ, a ∂ρ
    let s : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
    let b : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
    let V : ℝ := variance (id : ℝ → ℝ) ρ
    let gamma : ℝ := b / V
    0 < n ∧ 0 < s ∧ 0 < b ∧ 0 < V ∧ 0 < gamma ∧ s ≤ gamma ^ 2 ∧
      (3 / 4 : ℝ) ≤ (n : ℝ) * s ∧ (n : ℝ) * s ≤ 4 / 3 ∧
      (1 / 2 : ℝ) ≤ (n : ℝ) * V ∧ (n : ℝ) * V ≤ 4 / 3 ∧
      (n : ℝ) * |mu| ≤ 1 / 8 := by
  dsimp only
  obtain ⟨hslo, hshi, _, hVeq, _, hV, hVlo, hVhi⟩ :=
    Shao.sourceTruncation_variance_bounds ν0 n h2 hn hm x epsilon hx he he2 hR
  obtain ⟨hb, hg, _, hsg, _⟩ :=
    Shao.sourceTruncation_gamma_bounds ν0 n h2 hn hm x epsilon hx he he2 hR
  have hn0 : 0 < n := by
    obtain ⟨_, _, hn64, _⟩ := Shao.sourceTruncation_sample_size ν0 n h2 hn x epsilon hx he he2 hR
    omega
  have hs : 0 < ∫ a : ℝ, a ^ 2 ∂ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)} := by
    nlinarith [sq_nonneg (∫ a : ℝ, a ∂ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)})]
  have hpaid := (Shao.sourceTruncation_paid_moments ν0 n h2 hn hm x epsilon hx he he2 hR).1
  have hden : 0 < epsilon ^ 2 * (1 + x) := by positivity
  have hmu := (le_div_iff₀ hden).1 hpaid
  have hbound : (n : ℝ) * |∫ a : ℝ, a ∂ProbabilityTheory.cond ν0
      {a | |a| ≤ epsilon / (1 + x)}| ≤ 1 / 8 := by
    have hmul : epsilon ^ 2 * (1 + x) / 8 ≤ epsilon ^ 2 * (1 + x) / 8 := le_rfl
    have he8 : epsilon ^ 3 / 4 ≤ epsilon ^ 2 * (1 + x) / 8 := by
      have hs2 : 0 < epsilon ^ 2 := sq_pos_of_pos he
      nlinarith [mul_nonneg hs2.le hx]
    apply (mul_le_mul_iff_left₀ hden).1
    nlinarith only [hmu, hR, he8]
  exact ⟨hn0, hs, hb, hV, hg, hsg, hslo, hshi, hVlo, hVhi, hbound⟩

private theorem gy_late_roots (N I V : ℝ) (hN : 0 < N) (hI : 0 < I) (hV : 0 < V)
    (hhalf : N ≤ 2 * I) (hlo : (1 / 2 : ℝ) ≤ N * V) (hhi : N * V ≤ 4 / 3) :
    Real.sqrt V / Real.sqrt I ≤ 2 / N ∧ 1 / (Real.sqrt V * Real.sqrt I) ≤ 2 := by
  have hv := Real.sqrt_nonneg V
  have hi := Real.sqrt_nonneg I
  have hv2 := Real.sq_sqrt hV.le
  have hi2 := Real.sq_sqrt hI.le
  have hvi : (1 / 4 : ℝ) ≤ V * I := by nlinarith
  have hprod2 : (Real.sqrt V * Real.sqrt I) ^ 2 = V * I := by rw [mul_pow, hv2, hi2]
  have hprod : 1 / 2 ≤ Real.sqrt V * Real.sqrt I := by
    nlinarith [mul_nonneg hv hi]
  refine ⟨?_, (div_le_iff₀ (by positivity)).2 (by linarith)⟩
  apply (div_le_div_iff₀ (Real.sqrt_pos.2 hI) hN).2
  have hNhi := mul_le_mul_of_nonneg_left hhi hN.le
  have hsq : (Real.sqrt V * N) ^ 2 ≤ (2 * Real.sqrt I) ^ 2 := by
    rw [mul_pow, hv2, mul_pow, hi2]
    nlinarith only [hNhi, hhalf, hI]
  nlinarith [mul_nonneg hv hN.le]

private theorem gy_source_late_moments
    (ν0 : Measure ℝ) [IsProbabilityMeasure ν0] (n : ℕ)
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν0)
    (hn : (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1)
    (hm : (∫ a : ℝ, a ∂ν0) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x) (he : 0 < epsilon) (he2 : epsilon ≤ 1 / 2)
    (hR : Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8) :
    let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
    let b : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ρ)
    ∀ j : Fin n, n / 2 < j.val + 1 →
      (∫ a : Shao.Path n, lindleyRegulator a j ∂P) ≤ 4 / (n : ℝ) ∧
      (∫ a : Shao.Path n, (lindleyRegulator a j) ^ 2 ∂P) ≤
        (96 * Real.exp (7 + 3 * (1024 : ℝ))) * b := by
  dsimp only
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
  obtain ⟨_, _, hp, _, _, h2ρ, _, _⟩ :=
    Shao.sourceTruncation_law_data ν0 n h2 hn x epsilon hx he he2 hR
  letI : IsProbabilityMeasure ρ := hp
  obtain ⟨hn0, _, _, hV, _, _, _, _, hVlo, hVhi, hmu⟩ :=
    gy_source_scale ν0 n h2 hn hm x epsilon hx he he2 hR
  have hN : (0 : ℝ) < n := by exact_mod_cast hn0
  intro j hj
  have hj0 : (0 : ℝ) < ((j.val + 1 : ℕ) : ℝ) := by positivity
  have hhalf : (n : ℝ) ≤ 2 * ((j.val + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show n ≤ 2 * (j.val + 1) by omega)
  obtain ⟨hroot, hinv⟩ := gy_late_roots (n : ℝ) ((j.val + 1 : ℕ) : ℝ)
    (variance (id : ℝ → ℝ) ρ) hN hj0 hV hhalf hVlo hVhi
  have hfirst := (iid_lindleyRegulator_prefix_first_moment ρ h2ρ n j).2.2
  have hsecond := (sourceTruncation_lindleyRegulator_second_moment
    ν0 n h2 hn hm x epsilon hx he he2 hR j).2
  constructor
  · apply hfirst.trans
    have hmu' : |∫ a : ℝ, a ∂ρ| ≤ (1 / 8 : ℝ) / n :=
      (le_div_iff₀ hN).2 (by simpa only [mul_comm] using hmu)
    calc
      _ ≤ 2 / (n : ℝ) + (1 / 8 : ℝ) / n := add_le_add hroot hmu'
      _ = (2 + 1 / 8 : ℝ) / n := by ring
      _ ≤ 4 / (n : ℝ) := div_le_div_of_nonneg_right (by norm_num) hN.le
  · apply hsecond.trans
    have hm3 : 0 ≤ ∫ a : ℝ, |a| ^ 3 ∂ρ := integral_nonneg (fun a => by positivity)
    calc
      _ = (48 * Real.exp (7 + 3 * (1024 : ℝ))) * (∫ a : ℝ, |a| ^ 3 ∂ρ) *
          (1 / (Real.sqrt (variance (id : ℝ → ℝ) ρ) *
            Real.sqrt ((j.val + 1 : ℕ) : ℝ))) := by ring
      _ ≤ (48 * Real.exp (7 + 3 * (1024 : ℝ))) * (∫ a : ℝ, |a| ^ 3 ∂ρ) * 2 :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring

private theorem gy_unit_integrable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (F : α → ℝ) (hF : Measurable F) (h01 : ∀ a, 0 ≤ F a ∧ F a ≤ 1) :
    Integrable F μ ∧ 0 ≤ ∫ a, F a ∂μ ∧ (∫ a, F a ∂μ) ≤ 1 := by
  have hi : Integrable F μ := (integrable_const (1 : ℝ)).mono' hF.aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (h01 a).1] using (h01 a).2)
  refine ⟨hi, integral_nonneg (fun a => (h01 a).1), ?_⟩
  simpa using integral_mono hi (integrable_const (1 : ℝ)) (fun a => (h01 a).2)

private theorem gy_delta_data (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n k : ℕ) (ψ : ℝ × ℝ → ℝ) (hψ : Measurable ψ)
    (h01 : ∀ p, 0 ≤ ψ p ∧ ψ p ≤ 1) (j : Fin n) :
    Integrable (fun a : Shao.Path n => lindleyDelta ν ψ a j)
        (Measure.pi (fun _ : Fin n => ν)) ∧
      Integrable (fun a : Shao.Path n => |lindleyDelta ν ψ a j|)
        (Measure.pi (fun _ : Fin n => ν)) ∧
      Integrable (fun a : Shao.Path n =>
        if (1 / 16 : ℝ) ≤ Shao.prefixSquares a k then
          |lindleyDelta ν ψ a j| else 0) (Measure.pi (fun _ : Fin n => ν)) := by
  have hi := (integrable_lindley_test_and_delta (ν := ν)
    (μ := Measure.pi (fun _ : Fin n => ν))
    (fun j : Fin n => measurable_pi_apply j) ψ hψ h01).2.2 j
  change Integrable (fun a : Shao.Path n => lindleyDelta ν ψ a j)
    (Measure.pi (fun _ : Fin n => ν)) at hi
  refine ⟨hi, hi.abs, ?_⟩
  have hm : MeasurableSet {a : Shao.Path n | (1 / 16 : ℝ) ≤ Shao.prefixSquares a k} :=
    measurableSet_le measurable_const (Shao.measurable_prefixSquares (n := n) k)
  convert hi.abs.indicator hm using 1
  funext a
  simp only [Set.indicator_apply, Set.mem_setOf_eq]

private theorem gy_prefix_mono {n : ℕ} (a : Shao.Path n) {k i : ℕ} (hki : k ≤ i) :
    Shao.prefixSquares a k ≤ Shao.prefixSquares a i := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      lt_of_lt_of_le (Finset.mem_filter.mp hj).2 hki⟩
  · intro j _ _
    exact sq_nonneg _

private theorem gy_prefix_energy {n : ℕ} (a : Shao.Path n) (k : ℕ) (hk : k ≤ n) :
    Shao.energy (Shao.prefixPath a k hk) = Shao.prefixSquares a k := by
  classical
  unfold Shao.energy Shao.prefixSquares
  refine Finset.sum_bij (fun j _ => (⟨j.val, lt_of_lt_of_le j.is_lt hk⟩ : Fin n))
    ?_ ?_ ?_ ?_
  · intro j _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact j.is_lt
  · intro j _ l _ he
    exact Fin.ext (congrArg (@Fin.val n) he)
  · intro j hj
    exact ⟨⟨j.val, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro j _
    rfl

private theorem gy_prefix_history {n : ℕ} (k : ℕ) (hk : k ≤ n) :
    MeasurableSet[lindleyHistory (fun j : Fin n => fun a : Shao.Path n => a j) k hk]
      {a : Shao.Path n | Shao.prefixSquares a k < (1 / 16 : ℝ)} := by
  have h := (measurableSet_lt Shao.measurable_energy measurable_const :
    MeasurableSet {b : Shao.Path k | Shao.energy b < (1 / 16 : ℝ)})
  change ∃ t, MeasurableSet t ∧
    (fun a : Shao.Path n => Shao.prefixPath a k hk) ⁻¹' t = _
  refine ⟨_, h, ?_⟩
  ext a
  simp only [Set.mem_preimage, Set.mem_setOf_eq, gy_prefix_energy]

private theorem gy_noise_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν) (b : ℝ)
    (hb : 0 < b) (hb128 : b ≤ 1 / 128)
    (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ b)
    (hg : (∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν ≤ 2 * b)
    (y w : ℝ) :
    (∫ z : ℝ × ℝ, sourceFourierTest y (w + z.1, 0 + z.2)
      ∂quadraticFullNoiseLaw ν) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [(quadraticFullNoise_support_moments ν h3 hV b hb hs hg).1] with z hz
  have hz2 : z.2 < (1 / 16 : ℝ) := by
    have hbb : b ^ 2 ≤ (1 / 128 : ℝ) ^ 2 := sq_le_sq₀ hb.le (by norm_num) |>.2 hb128
    linarith only [le_abs_self z.2, hz.2, hbb]
  have hc : sourceKernelCutoff z.2 = 0 := by
    by_contra hc
    have hmem : z.2 ∈ tsupport sourceKernelCutoff := subset_closure hc
    exact (not_lt_of_ge (sourceKernelCutoff_data.2.2.2.2 hmem).1.le) hz2
  simp only [sourceFourierTest, zero_add, hc, zero_mul, Pi.zero_apply]

private theorem gy_weighted_integrable {n : ℕ} (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (b s : ℝ) (hb : 0 ≤ b) (hs : 0 ≤ s)
    (hsupp : ∀ᵐ a : ℝ ∂ν, |a| ≤ b) (j : Fin n) :
    Integrable (fun a : Shao.Path n => lindleyRegulator a j *
      Real.exp (-s * Shao.prefixSquares a (j.val + 1)))
        (Measure.pi (fun _ : Fin n => ν)) ∧
      Integrable (fun a : Shao.Path n => lindleyRegulator a j ^ 2 *
        Real.exp (-s * Shao.prefixSquares a (j.val + 1)))
        (Measure.pi (fun _ : Fin n => ν)) := by
  have hcoord := (measurePreserving_eval (fun _ : Fin n => ν) j).quasiMeasurePreserving.ae hsupp
  have he (a : Shao.Path n) :
      0 ≤ Real.exp (-s * Shao.prefixSquares a (j.val + 1)) ∧
        Real.exp (-s * Shao.prefixSquares a (j.val + 1)) ≤ 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs)
        (Shao.prefixSquares_nonneg _ _))⟩
  constructor
  · apply (integrable_const b).mono'
      (((gy_regulator_measurable j).mul
        ((Shao.measurable_prefixSquares _).const_mul (-s)).exp).aestronglyMeasurable)
    filter_upwards [hcoord] with a ha
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gy_regulator_bounds _ _).1 (he a).1)]
    exact (mul_le_of_le_one_right (gy_regulator_bounds _ _).1 (he a).2).trans
      ((gy_regulator_bounds _ _).2.trans ha)
  · apply (integrable_const (b ^ 2)).mono'
      ((((gy_regulator_measurable j).pow_const 2).mul
        ((Shao.measurable_prefixSquares _).const_mul (-s)).exp).aestronglyMeasurable)
    filter_upwards [hcoord] with a ha
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (he a).1)]
    apply (mul_le_of_le_one_right (sq_nonneg _) (he a).2).trans
    exact (sq_le_sq₀ (gy_regulator_bounds _ _).1 hb).mpr
      ((gy_regulator_bounds _ _).2.trans ha)

private theorem gy_gaussian_pay (y : ℝ) (hy : 0 ≤ y) :
    Real.exp (-y ^ 2 / 2) / (1 + y) ≤
      Real.sqrt (2 * Real.pi) * Shao.standardNormalTail y ∧
    Real.exp (-y ^ 2 / 2) * Real.exp (-(3 / 128 : ℝ) * y ^ 2) ≤
      Real.sqrt (2 * Real.pi) * (2 + 128 / 3) * Shao.standardNormalTail y := by
  let A := Real.sqrt (2 * Real.pi)
  have hA : 0 < A := Real.sqrt_pos.mpr (by positivity)
  have hY : 0 < 1 + y := by linarith
  have hf : Shao.standardNormalDensity y = Real.exp (-y ^ 2 / 2) / A := by
    simp [Shao.standardNormalDensity, ProbabilityTheory.gaussianPDFReal, A, div_eq_mul_inv, mul_comm]
  have hmill := (Shao.standardNormal_mills_bounds y hy).1
  rw [hf] at hmill
  have hbase : Real.exp (-y ^ 2 / 2) / (1 + y) ≤ A * Shao.standardNormalTail y := by
    have hh := mul_le_mul_of_nonneg_left hmill hA.le
    convert hh using 1 <;> field_simp
  refine ⟨hbase, ?_⟩
  rw [show -(3 / 128 : ℝ) * y ^ 2 = -((3 / 128 : ℝ) * y ^ 2) by ring]
  have hbase' : Real.exp (-y ^ 2 / 2) ≤ A * (1 + y) * Shao.standardNormalTail y := by
    have hh := (div_le_iff₀ hY).mp hbase
    convert hh using 1 <;> ring
  let u := (3 / 128 : ℝ) * y ^ 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hE : 0 < Real.exp (-u) := Real.exp_pos _
  have hE1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have huE : u * Real.exp (-u) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp u) hE.le
    have heq : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
    nlinarith only [hh, heq, hE]
  have hfactor : (1 + y) * Real.exp (-u) ≤ 2 + 128 / 3 := by
    have hyq : y ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg (y - 1 / 2)]
    have hh := mul_le_mul_of_nonneg_right hyq hE.le
    have hu' : (3 / 128 : ℝ) * (y ^ 2 * Real.exp (-u)) ≤ 1 := by
      simpa only [u, mul_assoc] using huE
    nlinarith only [hh, hu', hE1]
  calc
    _ ≤ (A * (1 + y) * Shao.standardNormalTail y) * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right hbase' hE.le
    _ = A * ((1 + y) * Real.exp (-u)) * Shao.standardNormalTail y := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfactor hA.le) (Shao.standardNormalTail_basic.2.2.1 y).1.le

private theorem gy_smooth_fubini {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (noise : Measure (ℝ × ℝ))
    [IsProbabilityMeasure P] [IsProbabilityMeasure noise]
    (y : ℝ) (Z : Ω → ℝ × ℝ) (hZ : Measurable Z) :
    (∫ p : Ω × (ℝ × ℝ), sourceFourierTest y
      ((Z p.1).1 + p.2.1, (Z p.1).2 + p.2.2) ∂P.prod noise) =
      ∫ a : Ω, ∫ z : ℝ × ℝ, sourceFourierTest y
        ((Z a).1 + z.1, (Z a).2 + z.2) ∂noise ∂P := by
  have hm : Measurable (fun p : Ω × (ℝ × ℝ) => sourceFourierTest y
      ((Z p.1).1 + p.2.1, (Z p.1).2 + p.2.2)) :=
    (gy_test_data y).1.comp
      (((hZ.fst.comp measurable_fst).add measurable_snd.fst).prodMk
        ((hZ.snd.comp measurable_fst).add measurable_snd.snd))
  exact integral_prod _ (gy_unit_integrable _ _ hm (fun p => (gy_test_data y).2 _)).1

private theorem gy_clock_bound (ν0 : Measure ℝ) [IsProbabilityMeasure ν0]
    (n : ℕ) (h2 : Integrable (fun a : ℝ => a ^ 2) ν0)
    (hn : (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1)
    (hm : (∫ a : ℝ, a ∂ν0) = 0) (x epsilon y : ℝ)
    (hx : 0 ≤ x) (he : 0 < epsilon) (he8 : epsilon ≤ 1 / 8)
    (hR : Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8)
    (hy : 2 ≤ y) (hwindow : |y - x| ≤ 1 / (2 * (1 + x))) :
    let rho := ProbabilityTheory.cond ν0 {a : ℝ | |a| ≤ epsilon / (1 + x)}
    let P := Measure.pi (fun _ : Fin n => rho)
    P.real {a : Shao.Path n | Shao.prefixSquares a (n / 2) < (1 / 16 : ℝ)} +
      P.real {a : Shao.Path n | Shao.energy a ∉ Set.Icc (1 / 4 : ℝ) 2} ≤
        2048 * Real.sqrt (2 * Real.pi) *
          ((1 + y) ^ 3 * (n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂rho)) *
            Shao.standardNormalTail y := by
  let P0 := Measure.pi (fun _ : Fin n => ν0)
  have hLaw (j : Fin n) : IdentDistrib (fun a : Shao.Path n => a j)
      (id : ℝ → ℝ) P0 ν0 := by
    refine ⟨(measurable_pi_apply j).aemeasurable, aemeasurable_id, ?_⟩
    simpa only [Measure.map_id] using
      (measurePreserving_eval (fun _ : Fin n => ν0) j).map_eq
  have hInd : iIndepFun (fun j : Fin n => fun a : Shao.Path n => a j) P0 :=
    iIndepFun_pi (fun _ : Fin n => aemeasurable_id)
  have hs := sourceTruncation_conditioned_sample
    (fun j : Fin n => measurable_pi_apply j) hInd hLaw h2 x epsilon hx he (by linarith) hR
  have heq := hs.2.2.2.1
  change Measure.map (id : Shao.Path n → Shao.Path n) _ = _ at heq
  rw [Measure.map_id] at heq
  have hc := (sourceTruncation_clock_bad_probability_le
    (fun j : Fin n => measurable_pi_apply j) hInd hLaw h2 hn hm
      x epsilon hx he he8 hR y hy hwindow).1
  dsimp only at hc ⊢
  rw [heq] at hc
  exact hc

private theorem gy_signed_block (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n k : ℕ) (hk : k ≤ n) (ψ : ℝ × ℝ → ℝ) (hψ : Measurable ψ)
    (h01 : ∀ p, 0 ≤ ψ p ∧ ψ p ≤ 1) :
    let P := Measure.pi (fun _ : Fin n => ν)
    let E := {a : Shao.Path n | Shao.prefixSquares a k < (1 / 16 : ℝ)}
    |∫ a in E, (∑ j : Fin n,
      if k ≤ j.val then lindleyDelta ν ψ a j else 0) ∂P| ≤ P.real E := by
  have hLaw (j : Fin n) : IdentDistrib (fun a : Shao.Path n => a j)
      (id : ℝ → ℝ) (Measure.pi (fun _ : Fin n => ν)) ν := by
    refine ⟨(measurable_pi_apply j).aemeasurable, aemeasurable_id, ?_⟩
    simpa only [Measure.map_id] using
      (measurePreserving_eval (fun _ : Fin n => ν) j).map_eq
  exact iid_lindley_signedBlock_bound (fun j : Fin n => measurable_pi_apply j)
    (iIndepFun_pi (fun _ : Fin n => aemeasurable_id)) hLaw
    k hk _ (gy_prefix_history k hk) ψ hψ h01

private theorem gy_smooth_identity (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure (quadraticFullNoiseLaw ν)] (n : ℕ) (y : ℝ) :
    let P := Measure.pi (fun _ : Fin n => ν)
    let noise := quadraticFullNoiseLaw ν
    let ψ := fun p : ℝ × ℝ => ∫ z : ℝ × ℝ,
      sourceFourierTest y (p.1 + z.1, p.2 + z.2) ∂noise
    let Cmax := ∫ p : Shao.Path n × (ℝ × ℝ),
      sourceFourierTest y (Shao.maxWithZero p.1 + p.2.1, Shao.energy p.1 + p.2.2)
        ∂P.prod noise
    let Cend := ∫ p : Shao.Path n × (ℝ × ℝ),
      sourceFourierTest y (Shao.prefixSum p.1 n + p.2.1, Shao.energy p.1 + p.2.2)
        ∂P.prod noise
    0 ≤ Cmax ∧ Cmax ≤ 1 ∧ 0 ≤ Cend ∧ Cend ≤ 1 ∧
      Cmax - Cend = ∑ j : Fin n, ∫ a : Shao.Path n, lindleyDelta ν ψ a j ∂P := by
  dsimp only
  have hmax := gy_unit_integrable
    ((Measure.pi (fun _ : Fin n => ν)).prod (quadraticFullNoiseLaw ν)) _
    ((gy_test_data y).1.comp
      (((Shao.measurable_maxWithZero.comp measurable_fst).add measurable_snd.fst).prodMk
        ((Shao.measurable_energy.comp measurable_fst).add measurable_snd.snd)))
    (fun p => (gy_test_data y).2 _)
  have hend := gy_unit_integrable
    ((Measure.pi (fun _ : Fin n => ν)).prod (quadraticFullNoiseLaw ν)) _
    ((gy_test_data y).1.comp
      ((((Shao.measurable_prefixSum n).comp measurable_fst).add measurable_snd.fst).prodMk
        ((Shao.measurable_energy.comp measurable_fst).add measurable_snd.snd)))
    (fun p => (gy_test_data y).2 _)
  refine ⟨hmax.2.1, hmax.2.2, hend.2.1, hend.2.2, ?_⟩
  rw [gy_smooth_fubini _ _ y _
      (Shao.measurable_maxWithZero.prodMk Shao.measurable_energy),
    gy_smooth_fubini _ _ y _
      ((Shao.measurable_prefixSum n).prodMk Shao.measurable_energy)]
  have hψ := gy_noise_test_data ν y
  have hLaw (j : Fin n) : IdentDistrib (fun a : Shao.Path n => a j)
      (id : ℝ → ℝ) (Measure.pi (fun _ : Fin n => ν)) ν := by
    refine ⟨(measurable_pi_apply j).aemeasurable, aemeasurable_id, ?_⟩
    simpa only [Measure.map_id] using
      (measurePreserving_eval (fun _ : Fin n => ν) j).map_eq
  have hInd := iIndepFun_pi (fun _ : Fin n => (aemeasurable_id : AEMeasurable
    (id : ℝ → ℝ) ν))
  have heq := ((iid_lindley_energy_identDistrib_maxWithZero
    (fun j : Fin n => measurable_pi_apply j) hInd hLaw).comp hψ.1).integral_eq
  have htel := iid_lindley_telescoping (fun j : Fin n => measurable_pi_apply j)
    hInd hLaw _ hψ.1 hψ.2
  let psi := fun p : ℝ × ℝ => ∫ z : ℝ × ℝ,
    sourceFourierTest y (p.1 + z.1, p.2 + z.2) ∂quadraticFullNoiseLaw ν
  have heq' : (∫ a : Shao.Path n, psi (Shao.lindleyState a n le_rfl, Shao.energy a)
      ∂Measure.pi (fun _ : Fin n => ν)) =
      ∫ a : Shao.Path n, psi (Shao.maxWithZero a,Shao.energy a)
        ∂Measure.pi (fun _ : Fin n => ν) := heq
  have htel' : ((∫ a : Shao.Path n, psi (Shao.lindleyState a n le_rfl,Shao.energy a)
      ∂Measure.pi (fun _ : Fin n => ν)) -
      ∫ a : Shao.Path n, psi (Shao.prefixSum a n,Shao.energy a)
        ∂Measure.pi (fun _ : Fin n => ν)) =
      ∑ j : Fin n, ∫ a : Shao.Path n, lindleyDelta ν psi a j
        ∂Measure.pi (fun _ : Fin n => ν) := htel
  rw [heq'] at htel'
  exact htel'

private theorem gy_exp_factor (y q T c : ℝ) (hT : 0 < T) (hq : 0 ≤ q)
    (hc : c ≤ 1 / (2 * T)) :
    Real.exp (-(y ^ 2 * (q + T) / (2 * T))) ≤
      Real.exp (-y ^ 2 / 2) * Real.exp (-c * y ^ 2 * q) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg y) hq)
  have heq : -(y ^ 2 * (q + T) / (2 * T)) =
      -y ^ 2 / 2 - (1 / (2 * T)) * (y ^ 2 * q) := by field_simp; ring
  rw [heq]
  nlinarith only [hh]

private theorem gy_early_assembly {α ι : Type*} [MeasurableSpace α]
    [Fintype ι] [DecidableEq ι] (P : Measure α) (J : Finset ι)
    (D U V : ι → α → ℝ) (K E Lambda b m W1 W2 : ℝ)
    (hK : 0 ≤ K) (hE : 0 ≤ E) (hL : 0 ≤ Lambda) (hb : 0 < b)
    (hW1 : 0 ≤ W1) (hW2 : 0 ≤ W2)
    (hD : ∀ j, Integrable (D j) P) (hU : ∀ j, Integrable (U j) P)
    (hV : ∀ j, Integrable (V j) P)
    (hpoint : ∀ j ∈ J, ∀ᵐ a ∂P,
      D j a ≤ K * E * (Lambda * U j a + b / 2 * V j a))
    (hfirst : (∑ j ∈ J, ∫ a, U j a ∂P) ≤ W1 / b)
    (hsecond : (∑ j ∈ J, ∫ a, V j a ∂P) ≤ W2 * m / b)
    (hm : b * m ≤ Lambda) :
    (∑ j ∈ J, ∫ a, D j a ∂P) ≤
      K * (W1 + W2 / 2) * Lambda * E / b := by
  have hper (j : ι) (hj : j ∈ J) :
      (∫ a, D j a ∂P) ≤ K * E *
        (Lambda * (∫ a, U j a ∂P) + b / 2 * (∫ a, V j a ∂P)) := by
    have hh := integral_mono_ae (hD j)
      (((hU j).const_mul Lambda |>.add ((hV j).const_mul (b / 2))).const_mul (K * E))
      (hpoint j hj)
    change (∫ a, D j a ∂P) ≤
      (∫ a, K * E * (Lambda * U j a + b / 2 * V j a) ∂P) at hh
    rw [integral_const_mul, integral_add ((hU j).const_mul Lambda) ((hV j).const_mul (b / 2)),
      integral_const_mul, integral_const_mul] at hh
    exact hh
  calc
    _ ≤ ∑ j ∈ J, K * E *
        (Lambda * (∫ a, U j a ∂P) + b / 2 * (∫ a, V j a ∂P)) :=
      Finset.sum_le_sum hper
    _ = K * E * (Lambda * (∑ j ∈ J, ∫ a, U j a ∂P) +
        b / 2 * (∑ j ∈ J, ∫ a, V j a ∂P)) := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ K * E * (Lambda * (W1 / b) + b / 2 * (W2 * m / b)) := by gcongr
    _ = K * E * (Lambda * W1 / b + W2 * m / 2) := by field_simp <;> ring
    _ ≤ K * E * (Lambda * W1 / b + W2 * (Lambda / b) / 2) := by
      gcongr
      exact (le_div_iff₀ hb).mpr (by simpa only [mul_comm] using hm)
    _ = _ := by field_simp <;> ring

private theorem gy_late_assembly {α : Type*} [MeasurableSpace α]
    (P : Measure α) (n : ℕ) (J : Finset (Fin n))
    (G U V : Fin n → α → ℝ) (B Lambda d S m : ℝ)
    (hN : (0 : ℝ) < n) (hB : 0 ≤ B) (hL : 0 ≤ Lambda)
    (hd : 0 ≤ d) (hS : 0 ≤ S) (hm : 0 ≤ m)
    (hG : ∀ j, Integrable (G j) P) (hU : ∀ j, Integrable (U j) P)
    (hV : ∀ j, Integrable (V j) P)
    (hpoint : ∀ j ∈ J, ∀ᵐ a ∂P,
      G j a ≤ B * (Lambda * U j a + d / 2 * V j a))
    (hfirst : ∀ j ∈ J, (∫ a, U j a ∂P) ≤ 4 / (n : ℝ))
    (hsecond : ∀ j ∈ J, (∫ a, V j a ∂P) ≤ 2 * S * m)
    (hpay : d * (n : ℝ) * m ≤ Lambda) :
    (∑ j ∈ J, ∫ a, G j a ∂P) ≤ B * (4 + S) * Lambda := by
  have hper (j : Fin n) (hj : j ∈ J) :
      (∫ a, G j a ∂P) ≤ B * (4 * Lambda / (n : ℝ) + d * S * m) := by
    calc
      _ ≤ ∫ a, B * (Lambda * U j a + d / 2 * V j a) ∂P :=
        integral_mono_ae (hG j)
          (((hU j).const_mul Lambda |>.add ((hV j).const_mul (d / 2))).const_mul B)
          (hpoint j hj)
      _ = B * (Lambda * (∫ a, U j a ∂P) + d / 2 * (∫ a, V j a ∂P)) := by
        rw [integral_const_mul, integral_add ((hU j).const_mul Lambda)
          ((hV j).const_mul (d / 2)), integral_const_mul, integral_const_mul]
      _ ≤ B * (Lambda * (4 / (n : ℝ)) + d / 2 * (2 * S * m)) := by
        gcongr
        · exact hfirst j hj
        · exact hsecond j hj
      _ = _ := by ring
  have hcard : (J.card : ℝ) ≤ n := by
    exact_mod_cast (show J.card ≤ n by
      simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ J))
  have hnon : 0 ≤ B * (4 * Lambda / (n : ℝ) + d * S * m) := by positivity
  calc
    _ ≤ ∑ _j ∈ J, B * (4 * Lambda / (n : ℝ) + d * S * m) := Finset.sum_le_sum hper
    _ = (J.card : ℝ) * (B * (4 * Lambda / (n : ℝ) + d * S * m)) := by simp
    _ ≤ (n : ℝ) * (B * (4 * Lambda / (n : ℝ) + d * S * m)) :=
      mul_le_mul_of_nonneg_right hcard hnon
    _ = B * (4 * Lambda + S * (d * (n : ℝ) * m)) := by field_simp <;> ring
    _ ≤ B * (4 * Lambda + S * Lambda) := by gcongr
    _ = _ := by ring

private theorem gy_signed_split {α : Type*} [MeasurableSpace α]
    (P : Measure α) (n k : ℕ) (E : Set α) (hE : MeasurableSet E)
    (D : Fin n → α → ℝ) (hD : ∀ j, Integrable (D j) P) :
    |∑ j : Fin n, ∫ a, D j a ∂P| ≤
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k),
        ∫ a, |D j a| ∂P) +
      |∫ a in E, (∑ j : Fin n, if k ≤ j.val then D j a else 0) ∂P| +
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => k ≤ j.val),
        ∫ a, Eᶜ.indicator (fun a => |D j a|) a ∂P) := by
  classical
  let early := Finset.univ.filter (fun j : Fin n => j.val < k)
  let late := Finset.univ.filter (fun j : Fin n => k ≤ j.val)
  let F := fun a => ∑ j ∈ late, D j a
  have hF : Integrable F P := integrable_finsetSum _ (fun j _ => hD j)
  have hsplit : (∑ j : Fin n, ∫ a, D j a ∂P) =
      (∑ j ∈ early, ∫ a, D j a ∂P) + (∫ a in E, F a ∂P) +
        (∫ a in Eᶜ, F a ∂P) := by
    have hfin := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun j : Fin n => j.val < k) (f := fun j => ∫ a, D j a ∂P)
    simp only [not_lt] at hfin
    have hint : (∫ a, F a ∂P) = ∑ j ∈ late, ∫ a, D j a ∂P :=
      integral_finsetSum _ (fun j _ => hD j)
    rw [← hfin, ← hint, ← integral_add_compl hE hF]
    ring
  have hearly : |∑ j ∈ early, ∫ a, D j a ∂P| ≤
      ∑ j ∈ early, ∫ a, |D j a| ∂P :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun j _ => abs_integral_le_integral_abs))
  have hlate : |∫ a in Eᶜ, F a ∂P| ≤
      ∑ j ∈ late, ∫ a, Eᶜ.indicator (fun a => |D j a|) a ∂P := by
    calc
      _ ≤ ∫ a in Eᶜ, |F a| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ a in Eᶜ, (∑ j ∈ late, |D j a|) ∂P :=
        integral_mono hF.integrableOn.abs
          (integrable_finsetSum _ (fun j _ => (hD j).abs.integrableOn))
          (fun a => Finset.abs_sum_le_sum_abs _ _)
      _ = ∑ j ∈ late, ∫ a in Eᶜ, |D j a| ∂P :=
        integral_finsetSum _ (fun j _ => (hD j).abs.integrableOn)
      _ = _ := Finset.sum_congr rfl (fun j _ => (integral_indicator hE.compl).symm)
  rw [hsplit]
  have htri := (abs_add_le
    ((∑ j ∈ early, ∫ a, D j a ∂P) + ∫ a in E, F a ∂P)
    (∫ a in Eᶜ, F a ∂P)).trans
      (add_le_add (abs_add_le _ _) le_rfl)
  have hFeq (a : α) : F a = ∑ j : Fin n, if k ≤ j.val then D j a else 0 := by
    simp only [F, late, Finset.sum_filter]
  simpa only [hFeq] using htri.trans
    (add_le_add (add_le_add hearly le_rfl) hlate)





theorem sourceTruncation_growing_y_reflection_probability_comparison :
    let L : ℝ := 1600
    let L2 : ℝ := 16384
    let alpha : ℝ := 1 / 1024
    let epsilon0 : ℝ := min (1 / (64 * Real.sqrt L2)) (alpha / (8 * L))
    let t0 : ℝ := Real.exp (-(48 * alpha / epsilon0))
    let eta0 : ℝ := min (1 / 16)
      (min (Real.sqrt t0 / (2 * Real.sqrt L2))
        (min ((epsilon0 / 20480) ^ 2)
          (1 / (16384 * (1 + 3 / t0) *
            Real.exp (24 * epsilon0 / t0)))))
    let epsilon : ℝ := min (epsilon0 / 2)
      (1 / (4 * (8 * (1 + L) + 1) * L))
    0 < epsilon0 ∧ 0 < epsilon ∧ epsilon ≤ epsilon0 / 2 ∧
      0 < t0 ∧ t0 < (3 / 8 : ℝ) ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (nu0 : Measure ℝ), IsProbabilityMeasure nu0 →
          ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) nu0 →
            (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu0) = 1 →
            (∫ a : ℝ, a ∂nu0) = 0 →
            ∀ x : ℝ, 0 ≤ x →
              Shao.truncationBudget nu0 n x ≤ epsilon ^ 3 / 8 →
              Shao.truncationBudget nu0 n x ≤ epsilon ^ 2 * eta0 / 40 →
              let rho : Measure ℝ := ProbabilityTheory.cond nu0
                {a : ℝ | |a| ≤ epsilon / (1 + x)}
              let mu : ℝ := ∫ a : ℝ, a ∂rho
              let raw2 : ℝ := ∫ a : ℝ, a ^ 2 ∂rho
              let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂rho
              let V : ℝ := variance (id : ℝ → ℝ) rho
              let gamma : ℝ := m3 / V
              let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
              let noise : Measure (ℝ × ℝ) := quadraticFullNoiseLaw rho
              IsProbabilityMeasure rho ∧ IsProbabilityMeasure noise ∧
                IndepFun (fun p : Shao.Path n × (ℝ × ℝ) => p.1)
                  (fun p => p.2) (P.prod noise) ∧
                (∀ᵐ z : ℝ × ℝ ∂noise,
                  |z.1| + (1 + x) * |z.2| ≤ 100 * (epsilon / (1 + x))) ∧
                (∫ z : ℝ × ℝ, |z.1| ∂noise) +
                  (1 + x) * (∫ z : ℝ × ℝ, |z.2| ∂noise) ≤ 100 * gamma ∧
                ∀ y : ℝ, 2 ≤ y → |y - x| ≤ 1 / (2 * (1 + x)) →
                  let Lambda : ℝ := (1 + y) * (n : ℝ) * |mu| +
                    (1 + y) ^ 3 * (n : ℝ) * m3
                  let psi : ℝ × ℝ → ℝ := fun p =>
                    ∫ z : ℝ × ℝ,
                      sourceFourierTest y (p.1 + z.1, p.2 + z.2) ∂noise
                  let k : ℕ := n / 2
                  let E : Set (Shao.Path n) :=
                    {a | Shao.prefixSquares a k < (1 / 16 : ℝ)}
                  let T : Fin n → ℝ := fun j =>
                    ((n - (j.val + 1) : ℕ) : ℝ) * raw2
                  let Delta : Fin n → Shao.Path n → ℝ := fun j a =>
                    lindleyDelta rho psi a j
                  let G : Fin n → Shao.Path n → ℝ := fun j a =>
                    if (1 / 16 : ℝ) ≤ Shao.prefixSquares a k then
                      |Delta j a| else 0
                  let early : Finset (Fin n) :=
                    Finset.univ.filter (fun j : Fin n => j.val < k)
                  let «macro» : Finset (Fin n) :=
                    Finset.univ.filter (fun j : Fin n => k ≤ j.val ∧ t0 ≤ T j)
                  let short : Finset (Fin n) :=
                    Finset.univ.filter (fun j : Fin n =>
                      k ≤ j.val ∧ L2 * gamma ^ 2 ≤ T j ∧ T j < t0)
                  let micro : Finset (Fin n) :=
                    Finset.univ.filter (fun j : Fin n =>
                      k ≤ j.val ∧ T j < L2 * gamma ^ 2)
                  let Cmax : ℝ := ∫ p : Shao.Path n × (ℝ × ℝ),
                    sourceFourierTest y
                      (Shao.maxWithZero p.1 + p.2.1, Shao.energy p.1 + p.2.2)
                    ∂P.prod noise
                  let Cend : ℝ := ∫ p : Shao.Path n × (ℝ × ℝ),
                    sourceFourierTest y
                      (Shao.prefixSum p.1 n + p.2.1, Shao.energy p.1 + p.2.2)
                    ∂P.prod noise
                  0 < gamma ∧ 0 ≤ Lambda ∧
                    Measurable psi ∧ (∀ p, 0 ≤ psi p ∧ psi p ≤ 1) ∧
                    (∀ w : ℝ, psi (w, 0) = 0) ∧
                    (∀ j : Fin n,
                      Integrable (Delta j) P ∧
                        Integrable (fun a : Shao.Path n => |Delta j a|) P ∧
                        Integrable (G j) P) ∧
                    (∀ j : Fin n, n - (j.val + 1) = 0 →
                      ∀ᵐ a : Shao.Path n ∂P, Delta j a = 0) ∧
                    P.real E + P.real {a : Shao.Path n |
                      Shao.energy a ∉ Set.Icc (1 / 4 : ℝ) 2} ≤
                      C * Lambda * Shao.standardNormalTail y ∧
                    (∑ j ∈ early, ∫ a : Shao.Path n, |Delta j a| ∂P) ≤
                      C * Lambda * Shao.standardNormalTail y ∧
                    |∫ a in E, (∑ j : Fin n,
                      if k ≤ j.val then Delta j a else 0) ∂P| ≤
                      C * Lambda * Shao.standardNormalTail y ∧
                    (∑ j ∈ «macro», ∫ a : Shao.Path n, G j a ∂P) ≤
                      C * Lambda * Shao.standardNormalTail y ∧
                    (∑ j ∈ short, ∫ a : Shao.Path n, G j a ∂P) ≤
                      C * Lambda * Shao.standardNormalTail y ∧
                    (∑ j ∈ micro, ∫ a : Shao.Path n, G j a ∂P) ≤
                      C * Lambda * Shao.standardNormalTail y ∧
                    (∑ j ∈ Finset.univ.filter (fun j : Fin n => k ≤ j.val),
                      ∫ a : Shao.Path n, G j a ∂P) ≤
                      C * Lambda * Shao.standardNormalTail y ∧
                    |∑ j : Fin n, ∫ a : Shao.Path n, Delta j a ∂P| ≤
                      C * Lambda * Shao.standardNormalTail y ∧
                    0 ≤ Cmax ∧ Cmax ≤ 1 ∧ 0 ≤ Cend ∧ Cend ≤ 1 ∧
                    Cmax - Cend =
                      ∑ j : Fin n, ∫ a : Shao.Path n, Delta j a ∂P ∧
                    |Cmax - Cend| ≤ C * Lambda * Shao.standardNormalTail y ∧
                    |Cmax - Cend| ≤
                      (20 * Real.exp 2 * C / epsilon ^ 2) *
                        Shao.truncationBudget nu0 n x * Shao.standardNormalTail x ∧
                    (∀ (Omega : Type*) [MeasurableSpace Omega]
                      (base : Measure Omega), IsProbabilityMeasure base →
                      ∀ X : Fin n → Omega → ℝ,
                        (∀ j, Measurable (X j)) → iIndepFun X base →
                        (∀ j, IdentDistrib (X j) (id : ℝ → ℝ) base nu0) →
                        let A : Set Omega := ⋂ j : Fin n,
                          {omega | |X j omega| ≤ epsilon / (1 + x)}
                        let conditioned : Measure Omega :=
                          ProbabilityTheory.cond base A
                        let CmaxX : ℝ := ∫ p : Omega × (ℝ × ℝ),
                          sourceFourierTest y
                            (Shao.maxWithZero (samplePath X p.1) + p.2.1,
                              Shao.energy (samplePath X p.1) + p.2.2)
                          ∂conditioned.prod noise
                        let CendX : ℝ := ∫ p : Omega × (ℝ × ℝ),
                          sourceFourierTest y
                            (Shao.prefixSum (samplePath X p.1) n + p.2.1,
                              Shao.energy (samplePath X p.1) + p.2.2)
                          ∂conditioned.prod noise
                        IsProbabilityMeasure conditioned ∧
                          Measure.map (samplePath X) conditioned = P ∧
                          CmaxX = Cmax ∧ CendX = Cend ∧
                          |CmaxX - CendX| ≤
                            C * Lambda * Shao.standardNormalTail y ∧
                          |CmaxX - CendX| ≤
                            (20 * Real.exp 2 * C / epsilon ^ 2) *
                              Shao.truncationBudget nu0 n x *
                                Shao.standardNormalTail x) := by
  classical
  intro L L2 alpha epsilon0 t0 eta0 epsilon
  obtain ⟨he0, he, heSmall, ht0, ht38, heMicro, hL2scale, Kg, hKg, HG⟩ :=
    sourceTruncation_growing_kernel_derivative_local_shift_bounds
  change 0 < epsilon0 at he0
  change 0 < epsilon at he
  change epsilon ≤ epsilon0 / 2 at heSmall
  change 0 < t0 at ht0
  change t0 < (3 / 8 : ℝ) at ht38
  change epsilon0 ≤ 1 / (192 * Real.sqrt (L2 + 1)) at heMicro
  obtain ⟨Km, hKm, HM⟩ := sourceTruncation_growing_microtime_reflection_sum
  obtain ⟨_, he064, heClock, heTilt, _, _, htExp, htLog,
    heta, heta16, hetaClock, hetaShort, hetaMacro⟩ :=
      sourceGrowingTilt_explicit_constant_payment L L2 (by norm_num [L]) (by norm_num [L2])
  change epsilon0 ≤ (1 / 64 : ℝ) at he064
  let A : ℝ := Real.sqrt (2 * Real.pi)
  let kap : ℝ := 1 / 128
  let W1 : ℝ := 128 / Real.sqrt kap
  let W2 : ℝ := (1024 * Real.exp (16 + 3 * (1024 : ℝ))) / Real.sqrt kap
  let S : ℝ := 48 * Real.exp (7 + 3 * (1024 : ℝ))
  let Ce : ℝ := A * Kg * (W1 + W2 / 2)
  let Cb : ℝ := 2048 * A
  let Ca : ℝ := A * Kg * (4 + S) * (2 + 128 / 3)
  let Cs : ℝ := Kg * (4 + S)
  let Cm : ℝ := Km * (L2 + 1)
  let C : ℝ := 1 + Ce + Cb + Ca + Cs + Cm
  have hA : 0 < A := Real.sqrt_pos.mpr (by positivity)
  have hW1 : 0 < W1 := by dsimp only [W1, kap]; positivity
  have hW2 : 0 < W2 := by dsimp only [W2, kap]; positivity
  have hS : 0 < S := by dsimp only [S]; positivity
  have hCe : 0 ≤ Ce := by dsimp only [Ce]; positivity
  have hCb : 0 ≤ Cb := by dsimp only [Cb]; positivity
  have hCa : 0 ≤ Ca := by dsimp only [Ca]; positivity
  have hCs : 0 ≤ Cs := by dsimp only [Cs]; positivity
  have hCm : 0 ≤ Cm := by dsimp only [Cm]; positivity
  have hC : 0 < C := by dsimp only [C]; linarith only [hCe,hCb,hCa,hCs,hCm]
  have hCle : Ce + Cb + Ca + Cs + Cm ≤ C := by dsimp only [C]; linarith
  refine ⟨he0, he, heSmall, ht0, ht38, C, hC, ?_⟩
  intro nu0 hp n h2 hnorm hmean x hx hR hReta rho mu raw2 m3 V gamma P noise
  letI := hp
  have heHalf : epsilon ≤ 1 / 2 := by linarith only [heSmall,he064]
  have he128 : epsilon ≤ 1 / 128 := by linarith only [heSmall,he064]
  have hxp : 0 < 1 + x := by linarith only [hx]
  let b : ℝ := epsilon / (1 + x)
  have hb : 0 < b := div_pos he hxp
  have hbe : b ≤ epsilon := by
    apply (div_le_iff₀ hxp).mpr
    nlinarith only [mul_nonneg he.le hx]
  obtain ⟨_,_,hrho,hs,h1r,h2r,h3r,_⟩ :=
    Shao.sourceTruncation_law_data nu0 n h2 hnorm x epsilon hx he heHalf hR
  change IsProbabilityMeasure rho at hrho
  letI := hrho
  change ∀ᵐ a : ℝ ∂rho, |a| ≤ b at hs
  obtain ⟨hn0, hraw, hm3, hV, hgamma, hm2g, hrawlo, hrawhi, hVlo, hVhi, hnmu⟩ :=
    gy_source_scale nu0 n h2 hnorm hmean x epsilon hx he heHalf hR
  change 0 < raw2 at hraw
  change 0 < m3 at hm3
  change 0 < V at hV
  change 0 < gamma at hgamma
  change (n : ℝ) * raw2 ≤ (4 / 3 : ℝ) at hrawhi
  have hN : (0 : ℝ) < n := by exact_mod_cast hn0
  have hNF := Shao.sourceTruncation_fullNoise nu0 n h2 hnorm hmean x epsilon hx he heHalf hR
  change IsProbabilityMeasure noise ∧ _ at hNF
  letI := hNF.1
  refine ⟨hrho,hNF.1,hNF.2.1,hNF.2.2.1,hNF.2.2.2.1,?_⟩
  intro y hy hwindow Lambda psi k E T Delta G early «macro» short micro Cmax Cend
  have hyp : 0 < 1 + y := by linarith only [hy]
  have hy0 : 0 ≤ y := by linarith only [hy]
  have htail : 0 ≤ Shao.standardNormalTail y := (Shao.standardNormalTail_basic.2.2.1 y).1.le
  have hparams := sourceTruncation_growingTilt_parameter_payment nu0 n h2 hnorm hmean
    L L2 epsilon0 t0 eta0 (by norm_num [L]) (by norm_num [L2])
    he0 heClock heTilt ht0 ht38 htExp htLog heta heta16 hetaClock hetaShort hetaMacro
    x epsilon hx rfl hR hReta y hy hwindow
  obtain ⟨_,_,_,_,_,_,_,hh,hbh,_,hsH,_,_,_,_,_,_,_,_,_,_,_,_,hgc,_,hLambda,
    _,_,hclock,_⟩ := hparams
  change 0 < epsilon0 / (1 + y) at hh
  change b ≤ epsilon0 / (1 + y) at hbh
  change gamma ≤ 2 * b at hgc
  change 0 ≤ Lambda at hLambda
  have hpsi := gy_noise_test_data rho y
  change Measurable psi ∧ ∀ p, 0 ≤ psi p ∧ psi p ≤ 1 at hpsi
  have hdata (j : Fin n) := gy_delta_data rho n k psi hpsi.1 hpsi.2 j
  have hDI (j : Fin n) : Integrable (Delta j) P := (hdata j).1
  have hDAI (j : Fin n) : Integrable (fun a : Shao.Path n => |Delta j a|) P := (hdata j).2.1
  have hGI (j : Fin n) : Integrable (G j) P := (hdata j).2.2
  have hG0 (j : Fin n) (a : Shao.Path n) : 0 ≤ G j a := by
    dsimp only [G]
    split_ifs <;> positivity
  have hGT0 (j : Fin n) : 0 ≤ ∫ a : Shao.Path n, G j a ∂P := integral_nonneg (hG0 j)
  have hk : k ≤ n := Nat.div_le_self _ _
  let U : Fin n → Shao.Path n → ℝ := fun j a => lindleyRegulator a j
  let Q : Fin n → Shao.Path n → ℝ := fun j a => Shao.prefixSquares a (j.val + 1)
  have hU0 (j : Fin n) (a : Shao.Path n) : 0 ≤ U j a := (gy_regulator_bounds a j).1
  have hUb (j : Fin n) : ∀ᵐ a : Shao.Path n ∂P, U j a ≤ epsilon0 / (1 + y) := by
    filter_upwards [(measurePreserving_eval (fun _ : Fin n => rho) j).quasiMeasurePreserving.ae hs] with a ha
    exact (gy_regulator_bounds a j).2.trans (ha.trans hbh)
  have hUI (j : Fin n) : Integrable (U j) P :=
    (iid_lindleyRegulator_prefix_first_moment rho h2r n j).1
  have hU2I (j : Fin n) : Integrable (fun a : Shao.Path n => U j a ^ 2) P :=
    (sourceTruncation_lindleyRegulator_second_moment nu0 n h2 hnorm hmean x epsilon hx he heHalf hR j).1
  have hTup (j : Fin n) : T j ≤ 4 / 3 := by
    have hnsub : ((n - (j.val + 1) : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n (j.val + 1)
    exact (mul_le_mul_of_nonneg_right hnsub hraw.le).trans hrawhi
  have hsource := HG nu0 hp n h2 hnorm hmean x hx hR hReta y hy hwindow
  obtain ⟨_,_,_,HD⟩ := hsource
  have hDelta (j : Fin n) (a : Shao.Path n) : Delta j a =
      sourceFutureNoiseKernel rho (n - (j.val + 1)) y (0,Q j a) -
        sourceFutureNoiseKernel rho (n - (j.val + 1)) y (-U j a,Q j a) := rfl
  have hterminal (j : Fin n) (hj : n - (j.val + 1) = 0) :
      ∀ᵐ a : Shao.Path n ∂P, Delta j a = 0 := by
    filter_upwards [hUb j] with a ha
    have hz := ((HD (j.val + 1) (by omega)).2.2.2.1 hj).1
      (Q j a) (-U j a) (by
        change |-U j a| ≤ 2 * (epsilon0 / (1 + y))
        rw [abs_neg, abs_of_nonneg (hU0 j a)]
        linarith only [ha,hh])
    change sourceFutureNoiseKernel rho (n - (j.val + 1)) y (-U j a,Q j a) =
      sourceFutureNoiseKernel rho (n - (j.val + 1)) y (0,Q j a) at hz
    rw [hDelta, hz, sub_self]
  have hnm : (1 + y) * (n : ℝ) * m3 ≤ Lambda := by
    have hpow : 1 + y ≤ (1 + y) ^ 3 := by nlinarith only [sq_nonneg y, hy]
    have hh := mul_le_mul_of_nonneg_right hpow (show 0 ≤ (n : ℝ) * m3 by positivity)
    change (1 + y) * (n : ℝ) * m3 ≤
      (1 + y) * (n : ℝ) * |mu| + (1 + y) ^ 3 * (n : ℝ) * m3
    nlinarith only [hh, show 0 ≤ (1 + y) * (n : ℝ) * |mu| by positivity]
  have hnm1 : (n : ℝ) * m3 ≤ Lambda := by
    have hh := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 1 + y by linarith only [hy])
      (show 0 ≤ (n : ℝ) * m3 by positivity)
    nlinarith only [hh, hnm]
  let WU : Fin n → Shao.Path n → ℝ := fun j a =>
    U j a * Real.exp (-(kap * y ^ 2) * Q j a)
  let WU2 : Fin n → Shao.Path n → ℝ := fun j a =>
    U j a ^ 2 * Real.exp (-(kap * y ^ 2) * Q j a)
  have hWI (j : Fin n) := gy_weighted_integrable rho b (kap * y ^ 2) hb.le
    (by dsimp only [kap]; positivity) hs j
  obtain ⟨_,_,_,_,_,_,_,_,_,_,HF1⟩ :=
    sourceTruncation_lindleyRegulator_energy_weighted_first_sum nu0 n h2 hnorm hmean
      x epsilon epsilon0 kap y hx he he0 (by linarith only [he064]) heSmall hR
      (by norm_num [kap]) (by norm_num [kap]) (by linarith only [hy]) hwindow
  obtain ⟨_,_,hFB1⟩ := HF1 k hk
  change (∫ a : Shao.Path n, ∑ j ∈ early, WU j a ∂P) ≤
    128 / (Real.sqrt kap * (1 + y)) at hFB1
  rw [integral_finsetSum _ (fun j _ => (hWI j).1)] at hFB1
  have hfirst : (∑ j ∈ early, ∫ a : Shao.Path n, WU j a ∂P) ≤ W1 / (1 + y) := by
    convert hFB1 using 1 <;> dsimp only [W1] <;> field_simp <;> ring
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,HF2⟩ :=
    sourceTruncation_lindleyRegulator_energy_weighted_second_sum nu0 n h2 hnorm hmean
      x epsilon epsilon0 kap y hx he he0 (by linarith only [he064]) heSmall hR
      (by norm_num [kap]) (by norm_num [kap]) (by linarith only [hy]) hwindow
  obtain ⟨_,_,hFB2,_⟩ := HF2 k hk
  change (∫ a : Shao.Path n, ∑ j ∈ early, WU2 j a ∂P) ≤
    (1024 * Real.exp (16 + 3 * (1024 : ℝ))) * (n : ℝ) * m3 /
      (Real.sqrt kap * (1 + y)) at hFB2
  rw [integral_finsetSum _ (fun j _ => (hWI j).2)] at hFB2
  have hsecond : (∑ j ∈ early, ∫ a : Shao.Path n, WU2 j a ∂P) ≤
      W2 * ((n : ℝ) * m3) / (1 + y) := by
    convert hFB2 using 1 <;> dsimp only [W2] <;> field_simp <;> ring
  have hearlyPoint (j : Fin n) (hj : j ∈ early) : ∀ᵐ a : Shao.Path n ∂P,
      |Delta j a| ≤ Kg * Real.exp (-y ^ 2 / 2) *
        (Lambda * WU j a + (1 + y) / 2 * WU2 j a) := by
    have hi : j.val + 1 ≤ n / 2 := by
      have hjk := (Finset.mem_filter.mp hj).2
      change j.val < n / 2 at hjk
      omega
    filter_upwards [hUb j] with a ha
    have hUa := hU0 j a
    obtain ⟨hTpos,_,_,hshift⟩ := (HD (j.val + 1) (by omega)).2.2.2.2.1
      (Q j a) (Shao.prefixSquares_nonneg _ _) (Or.inl hi)
    have hbnd := hshift (U j a) (hU0 j a) ha
    rw [hDelta]
    have hc : kap ≤ 1 / (2 * T j) := by
      apply (le_div_iff₀ (show 0 < 2 * T j by positivity)).mpr
      dsimp only [kap]
      nlinarith only [hTup j]
    have hexp := gy_exp_factor y (Q j a) (T j) kap hTpos
      (Shao.prefixSquares_nonneg _ _) hc
    calc
      _ ≤ Kg * Real.exp (-(y ^ 2 * (Q j a + T j) / (2 * T j))) *
          (Lambda * U j a + (1 + y) * U j a ^ 2 / 2) := hbnd
      _ ≤ Kg * (Real.exp (-y ^ 2 / 2) * Real.exp (-kap * y ^ 2 * Q j a)) *
          (Lambda * U j a + (1 + y) * U j a ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hKg.le) (by positivity)
      _ = _ := by dsimp only [WU,WU2]; rw [neg_mul]; ring
  have hearly0 := gy_early_assembly P early (fun j a => |Delta j a|) WU WU2
    Kg (Real.exp (-y ^ 2 / 2)) Lambda (1 + y) ((n : ℝ) * m3) W1 W2
    hKg.le (Real.exp_pos _).le hLambda hyp hW1.le hW2.le hDAI
    (fun j => (hWI j).1) (fun j => (hWI j).2) hearlyPoint hfirst hsecond
    (by convert hnm using 1 <;> ring)
  have hgauss := gy_gaussian_pay y hy0
  have hearly : (∑ j ∈ early, ∫ a : Shao.Path n, |Delta j a| ∂P) ≤
      Ce * Lambda * Shao.standardNormalTail y := by
    apply hearly0.trans
    calc
      _ = Kg * (W1 + W2 / 2) * Lambda * (Real.exp (-y ^ 2 / 2) / (1 + y)) := by ring
      _ ≤ Kg * (W1 + W2 / 2) * Lambda * (A * Shao.standardNormalTail y) :=
        mul_le_mul_of_nonneg_left hgauss.1 (by positivity)
      _ = _ := by dsimp only [Ce]; ring

  have hclockB : P.real E + P.real {a : Shao.Path n |
      Shao.energy a ∉ Set.Icc (1 / 4 : ℝ) 2} ≤
        Cb * Lambda * Shao.standardNormalTail y := by
    have hc := gy_clock_bound nu0 n h2 hnorm hmean x epsilon y hx he
      (by linarith only [he128]) hR hy hwindow
    apply hc.trans
    change 2048 * A * ((1 + y) ^ 3 * (n : ℝ) * m3) * Shao.standardNormalTail y ≤ _
    have hthird : (1 + y) ^ 3 * (n : ℝ) * m3 ≤ Lambda := by
      change (1 + y) ^ 3 * (n : ℝ) * m3 ≤
        (1 + y) * (n : ℝ) * |mu| + (1 + y) ^ 3 * (n : ℝ) * m3
      linarith only [show 0 ≤ (1 + y) * (n : ℝ) * |mu| by positivity]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hthird (by positivity))
      (Shao.standardNormalTail_basic.2.2.1 y).1.le
  have hbad : |∫ a in E, (∑ j : Fin n,
      if k ≤ j.val then Delta j a else 0) ∂P| ≤
        Cb * Lambda * Shao.standardNormalTail y := by
    have hbnd := gy_signed_block rho n k hk psi hpsi.1 hpsi.2
    apply hbnd.trans
    exact (le_add_of_nonneg_right (show 0 ≤ P.real
      {a : Shao.Path n | Shao.energy a ∉ Set.Icc (1 / 4 : ℝ) 2} by positivity)).trans hclockB
  have hlateMoment (j : Fin n) (hj : k ≤ j.val) :
      (∫ a : Shao.Path n, U j a ∂P) ≤ 4 / (n : ℝ) ∧
        (∫ a : Shao.Path n, U j a ^ 2 ∂P) ≤ 2 * S * m3 := by
    have hmom := gy_source_late_moments nu0 n h2 hnorm hmean x epsilon hx he heHalf hR
      j (by change n / 2 ≤ j.val at hj; omega)
    change (∫ a : Shao.Path n, U j a ∂P) ≤ 4 / (n : ℝ) ∧
      (∫ a : Shao.Path n, U j a ^ 2 ∂P) ≤
        (96 * Real.exp (7 + 3 * (1024 : ℝ))) * m3 at hmom
    refine ⟨hmom.1,?_⟩
    convert hmom.2 using 1 <;> dsimp only [S] <;> ring
  have hmacroPoint (j : Fin n) (hj : j ∈ «macro») : ∀ᵐ a : Shao.Path n ∂P,
      G j a ≤ (Kg * Real.exp (-y ^ 2 / 2) * Real.exp (-(3 / 128 : ℝ) * y ^ 2)) *
        (Lambda * U j a + (1 + y) / 2 * U j a ^ 2) := by
    obtain ⟨hjlate,hjT⟩ := (Finset.mem_filter.mp hj).2
    filter_upwards [hUb j] with a ha
    have hUa := hU0 j a
    dsimp only [G]
    split_ifs with hgood
    · have hq : (1 / 16 : ℝ) ≤ Q j a :=
        hgood.trans (gy_prefix_mono a (by omega))
      obtain ⟨hTpos,_,_,hshift⟩ := (HD (j.val + 1) (by omega)).2.2.2.2.1
        (Q j a) (Shao.prefixSquares_nonneg _ _)
        (Or.inr ⟨by change n / 2 ≤ j.val at hjlate; omega,hjT,hq⟩)
      have hbnd := hshift (U j a) (hU0 j a) ha
      have hc : (3 / 8 : ℝ) ≤ 1 / (2 * T j) := by
        apply (le_div_iff₀ (show 0 < 2 * T j by positivity)).mpr
        nlinarith only [hTup j]
      have hexp := gy_exp_factor y (Q j a) (T j) (3 / 8) hTpos
        (Shao.prefixSquares_nonneg _ _) hc
      have hqexp : Real.exp (-(3 / 8 : ℝ) * y ^ 2 * Q j a) ≤
          Real.exp (-(3 / 128 : ℝ) * y ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [mul_le_mul_of_nonneg_right hq (sq_nonneg y)]
      rw [hDelta]
      calc
        _ ≤ Kg * Real.exp (-(y ^ 2 * (Q j a + T j) / (2 * T j))) *
            (Lambda * U j a + (1 + y) * U j a ^ 2 / 2) := hbnd
        _ ≤ Kg * (Real.exp (-y ^ 2 / 2) * Real.exp (-(3 / 128 : ℝ) * y ^ 2)) *
            (Lambda * U j a + (1 + y) * U j a ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (hexp.trans (mul_le_mul_of_nonneg_left hqexp (Real.exp_pos _).le)) hKg.le)
              (by positivity)
        _ = _ := by ring
    · positivity
  have hmacro0 := gy_late_assembly P n «macro» G U (fun j a => U j a ^ 2)
    (Kg * Real.exp (-y ^ 2 / 2) * Real.exp (-(3 / 128 : ℝ) * y ^ 2))
    Lambda (1 + y) S m3 hN (by positivity) hLambda hyp.le hS.le hm3.le
    hGI hUI hU2I hmacroPoint
    (fun j hj => (hlateMoment j (Finset.mem_filter.mp hj).2.1).1)
    (fun j hj => (hlateMoment j (Finset.mem_filter.mp hj).2.1).2) hnm
  have hmacro : (∑ j ∈ «macro», ∫ a : Shao.Path n, G j a ∂P) ≤
      Ca * Lambda * Shao.standardNormalTail y := by
    apply hmacro0.trans
    calc
      _ = Kg * (4 + S) * Lambda *
          (Real.exp (-y ^ 2 / 2) * Real.exp (-(3 / 128 : ℝ) * y ^ 2)) := by ring
      _ ≤ Kg * (4 + S) * Lambda * (A * (2 + 128 / 3) * Shao.standardNormalTail y) :=
        mul_le_mul_of_nonneg_left hgauss.2 (by positivity)
      _ = _ := by dsimp only [Ca]; ring
  have hshortPoint (j : Fin n) (hj : j ∈ short) : ∀ᵐ a : Shao.Path n ∂P,
      G j a ≤ (Kg * Shao.standardNormalTail y) *
        (Lambda * U j a + (1 : ℝ) / 2 * U j a ^ 2) := by
    obtain ⟨hjlate,hjclock,hjT⟩ := (Finset.mem_filter.mp hj).2
    obtain ⟨hTpos,hshort⟩ := (HD (j.val + 1) (by omega)).2.2.2.2.2
      (by change n / 2 ≤ j.val at hjlate; omega) hjclock hjT
    have hT1 : T j ≤ 1 := by linarith only [hjT,ht38]
    have hT2 : (T j) ^ 2 ≤ 1 := pow_le_one₀ hTpos.le hT1
    filter_upwards [hUb j] with a ha
    have hUa := hU0 j a
    dsimp only [G]
    split_ifs with hgood
    · have hq : (1 / 16 : ℝ) ≤ Q j a := hgood.trans (gy_prefix_mono a (by omega))
      have hbnd := (hshort (Q j a) hq).2.2 (U j a) (hU0 j a) ha
      rw [hDelta]
      calc
        _ ≤ Kg * Shao.standardNormalTail y * (T j) ^ 2 *
            (Lambda * U j a + U j a ^ 2 / 2) := hbnd
        _ ≤ Kg * Shao.standardNormalTail y * 1 *
            (Lambda * U j a + U j a ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT2
            (mul_nonneg hKg.le htail)) (by positivity)
        _ = _ := by ring
    · positivity
  have hshort0 := gy_late_assembly P n short G U (fun j a => U j a ^ 2)
    (Kg * Shao.standardNormalTail y) Lambda 1 S m3 hN (mul_nonneg hKg.le htail) hLambda
    (by norm_num) hS.le hm3.le hGI hUI hU2I hshortPoint
    (fun j hj => (hlateMoment j (Finset.mem_filter.mp hj).2.1).1)
    (fun j hj => (hlateMoment j (Finset.mem_filter.mp hj).2.1).2) (by simpa using hnm1)
  have hshort : (∑ j ∈ short, ∫ a : Shao.Path n, G j a ∂P) ≤
      Cs * Lambda * Shao.standardNormalTail y := by
    convert hshort0 using 1 <;> dsimp only [Cs] <;> ring
  have hmicroData := HM L2 epsilon0 (by norm_num [L2]) he0 heMicro
    nu0 hp n h2 hnorm hmean x epsilon hx he heSmall hR y hy hwindow
  let Dsmall := fun (j : Fin n) (a : Shao.Path n) =>
    if (1 / 16 : ℝ) ≤ Q j a then |Delta j a| else 0
  have hmicroI (j : Fin n) : Integrable (Dsmall j) P := hmicroData.1 j
  have hmicroSet : micro = Finset.univ.filter
      (fun j : Fin n => n / 2 < j.val + 1 ∧ T j < L2 * gamma ^ 2) := by
    ext j
    simp only [micro,Finset.mem_filter,Finset.mem_univ,true_and]
    change (k ≤ j.val ∧ T j < L2 * gamma ^ 2) ↔
      (n / 2 < j.val + 1 ∧ T j < L2 * gamma ^ 2)
    constructor
    · rintro ⟨hl,ht⟩
      exact ⟨by change n / 2 ≤ j.val at hl; omega,ht⟩
    · rintro ⟨hl,ht⟩
      exact ⟨by change n / 2 ≤ j.val; omega,ht⟩
  have hmicro : (∑ j ∈ micro, ∫ a : Shao.Path n, G j a ∂P) ≤
      Cm * Lambda * Shao.standardNormalTail y := by
    calc
      _ ≤ ∑ j ∈ micro, ∫ a : Shao.Path n, Dsmall j a ∂P := by
        apply Finset.sum_le_sum
        intro j hj
        have hjlate := (Finset.mem_filter.mp hj).2.1
        apply integral_mono (hGI j) (hmicroI j)
        intro a
        dsimp only [G,Dsmall]
        by_cases hg : (1 / 16 : ℝ) ≤ Shao.prefixSquares a k
        · rw [if_pos hg, if_pos (hg.trans (gy_prefix_mono a (by omega)))]
        · rw [if_neg hg]
          split_ifs <;> positivity
      _ ≤ _ := by
        rw [hmicroSet]
        exact hmicroData.2.2.2
  let late : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => k ≤ j.val)
  have hcover : (∑ j ∈ late, ∫ a : Shao.Path n, G j a ∂P) ≤
      (∑ j ∈ «macro», ∫ a : Shao.Path n, G j a ∂P) +
      (∑ j ∈ short, ∫ a : Shao.Path n, G j a ∂P) +
      (∑ j ∈ micro, ∫ a : Shao.Path n, G j a ∂P) := by
    simp only [late,«macro»,short,micro,Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    by_cases hl : k ≤ j.val
    · by_cases ht : t0 ≤ T j
      · simp only [hl,ht,true_and,ite_true]
        split_ifs <;> linarith only [hGT0 j]
      · have htt := lt_of_not_ge ht
        by_cases hs : L2 * gamma ^ 2 ≤ T j
        · simp only [hl,ht,hs,htt,true_and,and_self,ite_true,ite_false,not_lt_of_ge hs]
          linarith only [hGT0 j]
        · have hss := lt_of_not_ge hs
          simp only [hl,ht,hs,htt,hss,true_and,false_and,ite_true,ite_false]
          linarith only [hGT0 j]
    · simp only [hl,false_and,ite_false,zero_add]
      exact le_rfl
  have hlate : (∑ j ∈ late, ∫ a : Shao.Path n, G j a ∂P) ≤
      (Ca + Cs + Cm) * Lambda * Shao.standardNormalTail y := by
    have hh := hcover.trans (add_le_add (add_le_add hmacro hshort) hmicro)
    convert hh using 1 <;> ring
  have hEm : MeasurableSet E :=
    measurableSet_lt (Shao.measurable_prefixSquares k) measurable_const
  have hindicator (j : Fin n) : Eᶜ.indicator (fun a => |Delta j a|) = G j := by
    funext a
    simp only [E,G,Set.indicator_apply,Set.mem_compl_iff,Set.mem_setOf_eq,not_lt]
  have hsum : |∑ j : Fin n, ∫ a : Shao.Path n, Delta j a ∂P| ≤
      C * Lambda * Shao.standardNormalTail y := by
    have hh := gy_signed_split P n k E hEm Delta hDI
    simp only [hindicator] at hh
    have hh' := hh.trans (add_le_add (add_le_add hearly hbad) hlate)
    have hc := mul_le_mul_of_nonneg_right hCle
      (show 0 ≤ Lambda * Shao.standardNormalTail y by positivity)
    nlinarith only [hh',hc]
  have hsmooth := gy_smooth_identity rho n y
  have htel : Cmax - Cend = ∑ j : Fin n, ∫ a : Shao.Path n, Delta j a ∂P := hsmooth.2.2.2.2
  have hcomparison : |Cmax - Cend| ≤ C * Lambda * Shao.standardNormalTail y := by
    rw [htel]
    exact hsum
  have hweak : |y - x| ≤ 1 / (1 + x) := by
    apply hwindow.trans
    apply (div_le_div_iff₀ (show 0 < 2 * (1 + x) by positivity) hxp).mpr
    linarith only [hx]
  have hpayment := (Shao.sourceTruncation_nearby_payment nu0 n h2 hnorm hmean
    x epsilon hx he heHalf hR y hy0 hweak).2.2.2
  have hbudgetComparison : |Cmax - Cend| ≤
      (20 * Real.exp 2 * C / epsilon ^ 2) *
        Shao.truncationBudget nu0 n x * Shao.standardNormalTail x := by
    apply hcomparison.trans
    have hh := mul_le_mul_of_nonneg_left hpayment hC.le
    convert hh using 1 <;> ring
  have hcoef (c : ℝ) (hc : c ≤ C) :
      c * Lambda * Shao.standardNormalTail y ≤ C * Lambda * Shao.standardNormalTail y :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hLambda)
      (Shao.standardNormalTail_basic.2.2.1 y).1.le
  refine ⟨hgamma,hLambda,hpsi.1,hpsi.2,?_,hdata,hterminal,
    hclockB.trans (hcoef Cb (by linarith only [hCle,hCe,hCa,hCs,hCm])),
    hearly.trans (hcoef Ce (by linarith only [hCle,hCb,hCa,hCs,hCm])),
    hbad.trans (hcoef Cb (by linarith only [hCle,hCe,hCa,hCs,hCm])),
    hmacro.trans (hcoef Ca (by linarith only [hCle,hCe,hCb,hCs,hCm])),
    hshort.trans (hcoef Cs (by linarith only [hCle,hCe,hCb,hCa,hCm])),
    hmicro.trans (hcoef Cm (by linarith only [hCle,hCe,hCb,hCa,hCs])),
    hlate.trans (hcoef (Ca+Cs+Cm) (by linarith only [hCle,hCe,hCb])),
    hsum,hsmooth.1,hsmooth.2.1,hsmooth.2.2.1,hsmooth.2.2.2.1,
    htel,hcomparison,hbudgetComparison,?_⟩
  · intro w
    exact gy_noise_zero rho h3r hV b hb (hbe.trans he128) hs hgc y w
  · intro Omega inst base hbase X hX hInd hLaw A0 conditioned CmaxX CendX
    letI := hbase
    have hsample := sourceTruncation_conditioned_sample hX hInd hLaw h2
      x epsilon hx he (by linarith only [heHalf]) hR
    have hcond : IsProbabilityMeasure conditioned := hsample.2.2.1
    letI := hcond
    have hmap : Measure.map (samplePath X) conditioned = P := hsample.2.2.2.1
    have hdist : IdentDistrib (samplePath X) (id : Shao.Path n → Shao.Path n)
        conditioned P := by
      refine ⟨(measurable_samplePath hX).aemeasurable,aemeasurable_id,?_⟩
      simpa only [Measure.map_id] using hmap
    have hpull (Z : Shao.Path n → ℝ × ℝ) (hZ : Measurable Z) :
        (∫ p : Omega × (ℝ × ℝ), sourceFourierTest y
          ((Z (samplePath X p.1)).1 + p.2.1,(Z (samplePath X p.1)).2 + p.2.2)
            ∂conditioned.prod noise) =
          ∫ p : Shao.Path n × (ℝ × ℝ), sourceFourierTest y
            ((Z p.1).1 + p.2.1,(Z p.1).2 + p.2.2) ∂P.prod noise := by
      calc
        _ = ∫ a : Omega, psi (Z (samplePath X a)) ∂conditioned :=
          gy_smooth_fubini conditioned noise y (fun a => Z (samplePath X a))
            (hZ.comp (measurable_samplePath hX))
        _ = ∫ a : Shao.Path n, psi (Z a) ∂P :=
          (hdist.comp (hpsi.1.comp hZ)).integral_eq
        _ = _ := (gy_smooth_fubini P noise y Z hZ).symm
    have hmaxX : CmaxX = Cmax := hpull
      (fun a => (Shao.maxWithZero a,Shao.energy a))
      (Shao.measurable_maxWithZero.prodMk Shao.measurable_energy)
    have hendX : CendX = Cend := hpull
      (fun a => (Shao.prefixSum a n,Shao.energy a))
      ((Shao.measurable_prefixSum n).prodMk Shao.measurable_energy)
    exact ⟨hcond,hmap,hmaxX,hendX,by rw [hmaxX,hendX]; exact hcomparison,
      by rw [hmaxX,hendX]; exact hbudgetComparison⟩


end Shao.Probability
