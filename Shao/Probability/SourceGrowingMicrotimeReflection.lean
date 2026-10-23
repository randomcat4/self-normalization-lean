import Shao.Probability.SourceLocalizedMicrotimeDerivatives
import Shao.Probability.SourceLindleyRegulatorFirstMomentSums
import Shao.Probability.LindleyTelescoping
import Shao.Probability.GaussianTail

/-! The actual growing microclock reflection sum, supplement.tex 923--935.
The zero future is removed by local constancy before positive-clock counting. -/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem gm_test_data (y : ℝ) :
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

private theorem gm_noise_test_data (ν : Measure ℝ) (y : ℝ)
    [IsProbabilityMeasure (quadraticFullNoiseLaw ν)] :
    let ψ := fun p : ℝ × ℝ => ∫ z : ℝ × ℝ,
      sourceFourierTest y (p.1 + z.1, p.2 + z.2) ∂quadraticFullNoiseLaw ν
    Measurable ψ ∧ ∀ p, 0 ≤ ψ p ∧ ψ p ≤ 1 := by
  dsimp only
  have hm : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      sourceFourierTest y (p.1.1 + p.2.1, p.1.2 + p.2.2)) :=
    (gm_test_data y).1.comp (by fun_prop)
  refine ⟨hm.stronglyMeasurable.integral_prod_right'.measurable, ?_⟩
  intro p
  have hi : Integrable (fun z : ℝ × ℝ =>
      sourceFourierTest y (p.1 + z.1, p.2 + z.2)) (quadraticFullNoiseLaw ν) :=
    (integrable_const (1 : ℝ)).mono'
      ((gm_test_data y).1.comp (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg ((gm_test_data y).2 _).1]
          using ((gm_test_data y).2 (p.1 + z.1, p.2 + z.2)).2)
  refine ⟨integral_nonneg (fun z => ((gm_test_data y).2 _).1), ?_⟩
  simpa using integral_mono hi (integrable_const (1 : ℝ))
    (fun z => ((gm_test_data y).2 _).2)

private theorem gm_state_nonneg {n : ℕ} (a : Shao.Path n) (k : ℕ) (hk : k ≤ n) :
    0 ≤ Shao.lindleyState a k hk := by
  cases k with
  | zero => rfl
  | succ k => exact le_max_left _ _

private theorem gm_state_measurable {n : ℕ} (k : ℕ) (hk : k ≤ n) :
    Measurable (fun a : Shao.Path n => Shao.lindleyState a k hk) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact measurable_const.max ((ih (by omega)).add (measurable_pi_apply _))

private theorem gm_regulator_measurable {n : ℕ} (j : Fin n) :
    Measurable (fun a : Shao.Path n => lindleyRegulator a j) :=
  ((gm_state_measurable j.val (Nat.le_of_lt j.is_lt)).add
    (measurable_pi_apply j)).neg.max measurable_const

private theorem gm_regulator_bounds {n : ℕ} (a : Shao.Path n) (j : Fin n) :
    0 ≤ lindleyRegulator a j ∧ lindleyRegulator a j ≤ |a j| := by
  refine ⟨le_max_right _ _, max_le ?_ (abs_nonneg _)⟩
  have hs := gm_state_nonneg a j.val (Nat.le_of_lt j.is_lt)
  linarith [neg_le_abs (a j)]

private theorem gm_delta_measurable {n : ℕ} (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (ψ : ℝ × ℝ → ℝ) (hψ : Measurable ψ) (j : Fin n) :
    Measurable (fun a : Shao.Path n => lindleyDelta ν ψ a j) := by
  have hk := measurable_lindleyFutureKernel ν (n - (j.val + 1)) ψ hψ
  exact (hk.comp (measurable_const.prodMk (Shao.measurable_prefixSquares _))).sub
    (hk.comp ((gm_regulator_measurable j).neg.prodMk (Shao.measurable_prefixSquares _)))

private theorem gm_clock_integrable {n : ℕ} (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (ψ : ℝ × ℝ → ℝ) (hψ : Measurable ψ)
    (h01 : ∀ p, 0 ≤ ψ p ∧ ψ p ≤ 1) (j : Fin n) :
    Integrable (fun a : Shao.Path n =>
      if (1 / 16 : ℝ) ≤ Shao.prefixSquares a (j.val + 1) then
        |lindleyDelta ν ψ a j| else 0) (Measure.pi (fun _ : Fin n => ν)) := by
  have hm : Measurable (fun a : Shao.Path n =>
      if (1 / 16 : ℝ) ≤ Shao.prefixSquares a (j.val + 1) then
        |lindleyDelta ν ψ a j| else 0) :=
    Measurable.ite
      (measurableSet_le measurable_const (Shao.measurable_prefixSquares _))
      (continuous_abs.measurable.comp (gm_delta_measurable ν ψ hψ j)) measurable_const
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [] with a
  split_ifs with hq
  · rw [Real.norm_eq_abs, abs_abs]
    have h0 := lindleyFutureKernel_bounds ν (n - (j.val + 1)) ψ hψ h01
      (0, Shao.prefixSquares a (j.val + 1))
    have hU := lindleyFutureKernel_bounds ν (n - (j.val + 1)) ψ hψ h01
      (-lindleyRegulator a j, Shao.prefixSquares a (j.val + 1))
    exact abs_le.mpr ⟨by dsimp [lindleyDelta]; linarith, by dsimp [lindleyDelta]; linarith⟩
  · simp

private theorem gm_local_difference (f : ℝ → ℝ) (h B U : ℝ)
    (hU : 0 ≤ U) (hUh : U ≤ h)
    (hd : ∀ w, DifferentiableAt ℝ f w)
    (hb : ∀ w, |w| ≤ h → |deriv f w| ≤ B) :
    |f 0 - f (-U)| ≤ B * U := by
  have hh : 0 ≤ h := hU.trans hUh
  have H := (convex_Icc (-h) h).norm_image_sub_le_of_norm_deriv_le
    (fun w _ => hd w)
    (fun w hw => by simpa only [Real.norm_eq_abs] using hb w (abs_le.mpr hw))
    (show -U ∈ Set.Icc (-h) h by constructor <;> linarith)
    (show (0 : ℝ) ∈ Set.Icc (-h) h by constructor <;> linarith)
  simpa only [Real.norm_eq_abs, sub_neg_eq_add, zero_add, abs_of_nonneg hU] using H

private theorem gm_late_first_moment (N k V μ : ℝ) (hN : 0 < N) (hk : 0 < k)
    (hlate : N ≤ 2 * k) (hV : 0 ≤ V) (hVhi : N * V ≤ 4 / 3)
    (hμ : N * |μ| ≤ 1 / 8) :
    Real.sqrt V / Real.sqrt k + |μ| ≤ 4 / N := by
  have hsk := Real.sqrt_pos.mpr hk
  have hsqV := Real.sq_sqrt hV
  have hsqk := Real.sq_sqrt hk.le
  have hVscaled := mul_le_mul_of_nonneg_left hVhi hN.le
  have hsqscaled : (N * Real.sqrt V) ^ 2 = N ^ 2 * V := by
    rw [mul_pow, hsqV]
  have hroot : N * Real.sqrt V ≤ 3 * Real.sqrt k := by
    nlinarith [Real.sqrt_nonneg V, Real.sqrt_nonneg k,
      sq_nonneg (N * Real.sqrt V - 3 * Real.sqrt k)]
  have hfirst : Real.sqrt V / Real.sqrt k ≤ 3 / N :=
    (div_le_div_iff₀ hsk hN).mpr (by nlinarith only [hroot])
  have hmu : |μ| ≤ (1 / 8 : ℝ) / N :=
    (le_div_iff₀ hN).mpr (by nlinarith only [hμ])
  have hlast : 3 / N + (1 / 8 : ℝ) / N ≤ 4 / N := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by norm_num) hN.le
  exact (add_le_add hfirst hmu).trans hlast

private theorem gm_positive_count {n : ℕ} (S : Finset (Fin n)) (raw2 b : ℝ)
    (hr : 0 < raw2) (hb0 : 0 ≤ b)
    (hpos : ∀ j ∈ S, 0 < n - (j.val + 1))
    (hb : ∀ j ∈ S, ((n - (j.val + 1) : ℕ) : ℝ) * raw2 < b) :
    (S.card : ℝ) * raw2 ≤ b := by
  classical
  by_cases he : S.Nonempty
  · let B := S.image (fun j => n - (j.val + 1))
    have hB : B.Nonempty := he.image _
    have hinj : Function.Injective (fun j : Fin n => n - (j.val + 1)) := by
      intro j k hjk
      change n - (j.val + 1) = n - (k.val + 1) at hjk
      apply Fin.ext
      have hj := j.is_lt
      have hk := k.is_lt
      omega
    have hc : S.card = B.card := (Finset.card_image_of_injective S hinj).symm
    have hcmax : B.card ≤ B.max' hB := by
      have hsub : B ⊆ Finset.Icc 1 (B.max' hB) := by
        intro m hm
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
        exact Finset.mem_Icc.mpr ⟨hpos j hj, Finset.le_max' _ _ hm⟩
      have ht := Finset.card_le_card hsub
      simpa using ht
    obtain ⟨j, hj, hjmax⟩ := Finset.mem_image.mp (Finset.max'_mem B hB)
    have hm := hb j hj
    have hcard : (S.card : ℝ) ≤ ((n - (j.val + 1) : ℕ) : ℝ) := by
      exact_mod_cast (hc ▸ (hjmax ▸ hcmax))
    exact (mul_le_mul_of_nonneg_right hcard hr.le).trans hm.le
  · have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    subst S
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    exact hb0


set_option maxHeartbeats 10000000 in
theorem sourceTruncation_growing_microtime_reflection_sum :
    ∃ C : ℝ, 0 < C ∧
      ∀ L2 epsilon0 : ℝ, 0 < L2 → 0 < epsilon0 →
        epsilon0 ≤ 1 / (192 * Real.sqrt (L2 + 1)) →
        ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
          ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
            (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 →
            (∫ a : ℝ, a ∂ν0) = 0 →
            ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon →
              epsilon ≤ epsilon0 / 2 →
              Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
              ∀ y : ℝ, 2 ≤ y →
                |y - x| ≤ 1 / (2 * (1 + x)) →
                let rho := ProbabilityTheory.cond ν0
                  {a : ℝ | |a| ≤ epsilon / (1 + x)}
                let raw2 := ∫ a : ℝ, a ^ 2 ∂rho
                let m3 := ∫ a : ℝ, |a| ^ 3 ∂rho
                let V := variance (id : ℝ → ℝ) rho
                let gamma := m3 / V
                let P := Measure.pi (fun _ : Fin n => rho)
                let psi := fun p : ℝ × ℝ =>
                  ∫ z : ℝ × ℝ,
                    sourceFourierTest y (p.1 + z.1, p.2 + z.2)
                    ∂quadraticFullNoiseLaw rho
                let T := fun j : Fin n =>
                  ((n - (j.val + 1) : ℕ) : ℝ) * raw2
                let J := Finset.univ.filter (fun j : Fin n =>
                  n / 2 < j.val + 1 ∧ T j < L2 * gamma ^ 2)
                let D := fun (j : Fin n) (a : Shao.Path n) =>
                  if (1 / 16 : ℝ) ≤ Shao.prefixSquares a (j.val + 1) then
                    |lindleyDelta rho psi a j| else 0
                let Lambda :=
                  (1 + y) * (n : ℝ) * |∫ a : ℝ, a ∂rho| +
                    (1 + y) ^ 3 * (n : ℝ) * m3
                (∀ j : Fin n, Integrable (D j) P) ∧
                  (∀ j ∈ J, (∫ a : Shao.Path n, D j a ∂P) ≤
                    C / ((n : ℝ) * gamma) * Real.exp (-4 * y ^ 2)) ∧
                  (∑ j ∈ J, ∫ a : Shao.Path n, D j a ∂P) ≤
                    C * (L2 + 1) * ((n : ℝ) * m3) * Real.exp (-4 * y ^ 2) ∧
                  (∑ j ∈ J, ∫ a : Shao.Path n, D j a ∂P) ≤
                    C * (L2 + 1) * Lambda * Shao.standardNormalTail y := by
  classical
  obtain ⟨K, hK, HK⟩ := sourceTruncation_growing_microtime_derivative_bounds
  let A : ℝ := Real.sqrt (2 * Real.pi)
  have hA : 0 < A := Real.sqrt_pos.mpr (by positivity)
  let C : ℝ := 16 * K * (A + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro L2 epsilon0 hL2 he0 he0bound ν0 hp n h2 hnorm hmean x epsilon hx he heSmall hR y hy hwindow
  letI := hp
  dsimp only
  let rho := ProbabilityTheory.cond ν0 {a : ℝ | |a| ≤ epsilon / (1 + x)}
  let raw2 := ∫ a : ℝ, a ^ 2 ∂rho
  let m3 := ∫ a : ℝ, |a| ^ 3 ∂rho
  let V := variance (id : ℝ → ℝ) rho
  let gamma := m3 / V
  let P := Measure.pi (fun _ : Fin n => rho)
  let psi := fun p : ℝ × ℝ => ∫ z : ℝ × ℝ,
    sourceFourierTest y (p.1 + z.1, p.2 + z.2) ∂quadraticFullNoiseLaw rho
  let T := fun j : Fin n => ((n - (j.val + 1) : ℕ) : ℝ) * raw2
  let J := Finset.univ.filter (fun j : Fin n => n / 2 < j.val + 1 ∧ T j < L2 * gamma ^ 2)
  let D := fun (j : Fin n) (a : Shao.Path n) =>
    if (1 / 16 : ℝ) ≤ Shao.prefixSquares a (j.val + 1) then
      |lindleyDelta rho psi a j| else 0
  let Lambda := (1 + y) * (n : ℝ) * |∫ a : ℝ, a ∂rho| +
    (1 + y) ^ 3 * (n : ℝ) * m3
  let h := epsilon0 / (1 + y)
  let hcut := epsilon / (1 + x)
  change (∀ j : Fin n, Integrable (D j) P) ∧
    (∀ j ∈ J, (∫ a, D j a ∂P) ≤ C / ((n : ℝ) * gamma) * Real.exp (-4 * y ^ 2)) ∧
    (∑ j ∈ J, ∫ a, D j a ∂P) ≤ C * (L2 + 1) * ((n : ℝ) * m3) * Real.exp (-4 * y ^ 2) ∧
    (∑ j ∈ J, ∫ a, D j a ∂P) ≤ C * (L2 + 1) * Lambda * Shao.standardNormalTail y
  have hroot : 1 ≤ Real.sqrt (L2 + 1) := by
    have hs := Real.sq_sqrt (show 0 ≤ L2 + 1 by linarith)
    nlinarith [Real.sqrt_nonneg (L2 + 1)]
  have he192 : epsilon0 ≤ 1 / 192 := by
    apply he0bound.trans
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have heHalf : epsilon ≤ 1 / 2 := by linarith
  have hxp : 0 < 1 + x := by linarith
  have hyp : 0 < 1 + y := by linarith
  have hh : 0 < h := div_pos he0 hyp
  have hratio : 1 + y ≤ 2 * (1 + x) := by
    have hhalf : 1 / (2 * (1 + x)) ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ (show 0 < 2 * (1 + x) by positivity)).mpr
      linarith
    linarith [(abs_le.mp hwindow).2]
  have hcutH : hcut ≤ h := by
    apply (div_le_div_iff₀ hxp hyp).mpr
    calc
      epsilon * (1 + y) ≤ (epsilon0 / 2) * (1 + y) :=
        mul_le_mul_of_nonneg_right heSmall hyp.le
      _ ≤ (epsilon0 / 2) * (2 * (1 + x)) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = epsilon0 * (1 + x) := by ring
  obtain ⟨_, _, hprob, hs, _, h2r, h3r, _⟩ :=
    Shao.sourceTruncation_law_data ν0 n h2 hnorm x epsilon hx he heHalf hR
  change IsProbabilityMeasure rho at hprob
  letI := hprob
  change ∀ᵐ a : ℝ ∂rho, |a| ≤ hcut at hs
  obtain ⟨_, _, hn64, _⟩ := Shao.sourceTruncation_sample_size ν0 n h2 hnorm x epsilon hx he heHalf hR
  have hN : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨hrawlo, _, _, _, _, hV, hVlo, hVhi⟩ :=
    Shao.sourceTruncation_variance_bounds ν0 n h2 hnorm hmean x epsilon hx he heHalf hR
  change (3 / 4 : ℝ) ≤ (n : ℝ) * raw2 at hrawlo
  change 0 < V at hV
  change (1 / 2 : ℝ) ≤ (n : ℝ) * V at hVlo
  change (n : ℝ) * V ≤ (4 / 3 : ℝ) at hVhi
  have hraw : 0 < raw2 := by nlinarith
  obtain ⟨hm3, hg, _, _, hgcut, _, hgHi, _, _⟩ :=
    Shao.sourceTruncation_gamma_bounds ν0 n h2 hnorm hmean x epsilon hx he heHalf hR
  change 0 < m3 at hm3
  change 0 < gamma at hg
  change gamma ≤ 2 * hcut at hgcut
  change gamma ≤ 2 * (n : ℝ) * m3 at hgHi
  have hsupport : ∀ᵐ a : ℝ ∂rho, |a| ≤ h := hs.mono (fun a ha => ha.trans hcutH)
  have hnoise := quadraticFullNoise_law_data rho h3r hV h hh hsupport
  letI := hnoise.1
  letI := hnoise.2.2.1
  obtain ⟨hpsi, hpsi01⟩ := gm_noise_test_data rho y
  change Measurable psi at hpsi
  change ∀ p, 0 ≤ psi p ∧ psi p ≤ 1 at hpsi01
  have hDI (j : Fin n) : Integrable (D j) P := gm_clock_integrable rho psi hpsi hpsi01 j
  have hDnonneg (j : Fin n) (a : Shao.Path n) : 0 ≤ D j a := by
    dsimp [D]
    split_ifs <;> positivity
  have hU (j : Fin n) : ∀ᵐ a : Shao.Path n ∂P, lindleyRegulator a j ≤ h := by
    have hj : ∀ᵐ a : Shao.Path n ∂P, |a j| ≤ hcut :=
      (measurePreserving_eval (fun _ : Fin n => rho) j).quasiMeasurePreserving.ae hs
    filter_upwards [hj] with a ha
    exact (gm_regulator_bounds a j).2.trans (ha.trans hcutH)
  have hfuture (m : ℕ) (p : ℝ × ℝ) :
      lindleyFutureKernel rho m psi p = sourceFutureNoiseKernel rho m y p := rfl
  have HD (j : Fin n) (hj : j ∈ J) :=
    HK L2 epsilon0 hL2 he0 he0bound ν0 hp n h2 hnorm hmean x epsilon hx he heSmall hR
      y hy hwindow (n - (j.val + 1)) (Nat.sub_le _ _)
      ((Finset.mem_filter.mp hj).2.2.le)
  have hpoint (j : Fin n) (hj : j ∈ J) :
      ∀ᵐ a : Shao.Path n ∂P,
        D j a ≤ (K / gamma * Real.exp (-4 * y ^ 2)) * lindleyRegulator a j := by
    filter_upwards [hU j] with a ha
    have hUn := (gm_regulator_bounds a j).1
    dsimp only [D]
    split_ifs with hq
    · unfold lindleyDelta
      rw [hfuture, hfuture]
      by_cases hq5 : Shao.prefixSquares a (j.val + 1) ≤ 5
      · apply gm_local_difference
          (fun w => sourceFutureNoiseKernel rho (n - (j.val + 1)) y
            (w, Shao.prefixSquares a (j.val + 1))) h
          (K / gamma * Real.exp (-4 * y ^ 2)) _ hUn ha
        · exact fun w => ((HD j hj).1 _ w).1
        · intro w hw
          exact ((HD j hj).2.2.1 _ w ⟨hq, hq5⟩ hw).2.2.1
      · have hz := (HD j hj).2.1 _ (lt_of_not_ge hq5)
        have hz0 : sourceFutureNoiseKernel rho (n - (j.val + 1)) y
            (0, Shao.prefixSquares a (j.val + 1)) = 0 := (hz 0).1
        have hzU : sourceFutureNoiseKernel rho (n - (j.val + 1)) y
            (-lindleyRegulator a j, Shao.prefixSquares a (j.val + 1)) = 0 :=
          (hz (-lindleyRegulator a j)).1
        rw [hz0, hzU]
        simp only [sub_self, abs_zero]
        positivity
    · positivity
  have hterminal (j : Fin n) (hj : j ∈ J) (hz : n - (j.val + 1) = 0) :
      (∫ a, D j a ∂P) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hU j] with a ha
    dsimp only [D]
    split_ifs
    · unfold lindleyDelta
      rw [hfuture, hfuture]
      have heq := ((HD j hj).2.2.2 hz).1 (Shao.prefixSquares a (j.val + 1))
        (-lindleyRegulator a j) (by
          rw [abs_neg, abs_of_nonneg (gm_regulator_bounds a j).1]
          linarith)
      change sourceFutureNoiseKernel rho (n - (j.val + 1)) y
        (-lindleyRegulator a j, Shao.prefixSquares a (j.val + 1)) =
          sourceFutureNoiseKernel rho (n - (j.val + 1)) y
            (0, Shao.prefixSquares a (j.val + 1)) at heq
      rw [heq]
      simp
    · rfl
  have hpaid := (Shao.sourceTruncation_paid_moments ν0 n h2 hnorm hmean x epsilon hx he heHalf hR).1
  have hbias : (n : ℝ) * |∫ a : ℝ, a ∂rho| ≤ (1 / 8 : ℝ) := by
    apply hpaid.trans
    apply (div_le_iff₀ (mul_pos (pow_pos he 2) hxp)).2
    have hi := mul_le_mul_of_nonneg_left
      (show 2 * epsilon ≤ 1 + x by linarith) (sq_nonneg epsilon)
    nlinarith only [hR, hi]
  have hper (j : Fin n) (hj : j ∈ J) :
      (∫ a, D j a ∂P) ≤ 4 * K / ((n : ℝ) * gamma) * Real.exp (-4 * y ^ 2) := by
    have hmoment := iid_lindleyRegulator_prefix_first_moment rho h2r n j
    have hlate : (n : ℝ) ≤ 2 * ((j.val + 1 : ℕ) : ℝ) := by
      have hjlate := (Finset.mem_filter.mp hj).2.1
      have hnlate : n ≤ 2 * (j.val + 1) := by omega
      exact_mod_cast hnlate
    have hmom : (∫ a : Shao.Path n, lindleyRegulator a j ∂P) ≤ 4 / (n : ℝ) :=
      hmoment.2.2.trans (gm_late_first_moment _ _ _ _ hN (by positivity) hlate hV.le hVhi hbias)
    calc
      _ ≤ ∫ a, (K / gamma * Real.exp (-4 * y ^ 2)) * lindleyRegulator a j ∂P :=
        integral_mono_ae (hDI j) (hmoment.1.const_mul _) (hpoint j hj)
      _ = (K / gamma * Real.exp (-4 * y ^ 2)) *
          (∫ a : Shao.Path n, lindleyRegulator a j ∂P) := integral_const_mul _ _
      _ ≤ (K / gamma * Real.exp (-4 * y ^ 2)) * (4 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hmom (by positivity)
      _ = _ := by field_simp <;> ring
  let S := J.filter (fun j : Fin n => n - (j.val + 1) ≠ 0)
  have hsum : (∑ j ∈ J, ∫ a, D j a ∂P) = ∑ j ∈ S, ∫ a, D j a ∂P := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j hj hnj
    have hz : n - (j.val + 1) = 0 := by
      by_contra hnz
      exact hnj (Finset.mem_filter.mpr ⟨hj, hnz⟩)
    exact hterminal j hj hz
  have hcraw : (S.card : ℝ) * raw2 ≤ L2 * gamma ^ 2 :=
    gm_positive_count S raw2 (L2 * gamma ^ 2) hraw (by positivity)
      (fun j hj => Nat.pos_of_ne_zero (Finset.mem_filter.mp hj).2)
      (fun j hj => (Finset.mem_filter.mp ((Finset.mem_filter.mp hj).1)).2.2)
  have hcount : (S.card : ℝ) ≤ 2 * L2 * (n : ℝ) * gamma ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hcraw hN.le
    have hlower := mul_le_mul_of_nonneg_left hrawlo (Nat.cast_nonneg S.card)
    nlinarith
  have hsumK : (∑ j ∈ J, ∫ a, D j a ∂P) ≤
      16 * K * L2 * ((n : ℝ) * m3) * Real.exp (-4 * y ^ 2) := by
    rw [hsum]
    calc
      _ ≤ ∑ _j ∈ S, 4 * K / ((n : ℝ) * gamma) * Real.exp (-4 * y ^ 2) :=
        Finset.sum_le_sum fun j hj => hper j (Finset.mem_filter.mp hj).1
      _ = (S.card : ℝ) * (4 * K / ((n : ℝ) * gamma) * Real.exp (-4 * y ^ 2)) := by
        simp
      _ ≤ (2 * L2 * (n : ℝ) * gamma ^ 2) *
          (4 * K / ((n : ℝ) * gamma) * Real.exp (-4 * y ^ 2)) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = 8 * K * L2 * gamma * Real.exp (-4 * y ^ 2) := by field_simp <;> ring
      _ ≤ 8 * K * L2 * (2 * (n : ℝ) * m3) * Real.exp (-4 * y ^ 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hgHi (by positivity)) (Real.exp_pos _).le
      _ = _ := by ring
  have htail : ((n : ℝ) * m3) * Real.exp (-4 * y ^ 2) ≤
      A * Lambda * Shao.standardNormalTail y := by
    have hmills := (Shao.standardNormal_mills_bounds y (by linarith)).1
    have hphi : Shao.standardNormalDensity y = A⁻¹ * Real.exp (-y ^ 2 / 2) := by
      simp [Shao.standardNormalDensity, ProbabilityTheory.gaussianPDFReal, A]
    have hphiPaid : Real.exp (-y ^ 2 / 2) ≤
        A * (1 + y) * Shao.standardNormalTail y := by
      rw [hphi] at hmills
      have hm := (div_le_iff₀ hyp).mp hmills
      have hh := mul_le_mul_of_nonneg_left hm hA.le
      calc
        _ ≤ A * Shao.standardNormalTail y * (1 + y) := by
          simpa only [← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul] using hh
        _ = _ := by ring
    have hL : (1 + y) * ((n : ℝ) * m3) ≤ Lambda := by
      have hyn : 0 ≤ y := by linarith only [hy]
      have hpow : (1 + y) ≤ (1 + y) ^ 3 := by
        nlinarith only [hyn, sq_nonneg y, mul_nonneg hyn (sq_nonneg y)]
      have hp := mul_le_mul_of_nonneg_right hpow (mul_nonneg hN.le hm3.le)
      dsimp only [Lambda]
      nlinarith only [hp,
        mul_nonneg hyp.le (mul_nonneg hN.le (abs_nonneg (∫ a : ℝ, a ∂rho)))]
    calc
      _ ≤ ((n : ℝ) * m3) * Real.exp (-y ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith only [sq_nonneg y]))
          (by positivity)
      _ ≤ ((n : ℝ) * m3) * (A * (1 + y) * Shao.standardNormalTail y) :=
        mul_le_mul_of_nonneg_left hphiPaid (by positivity)
      _ = A * ((1 + y) * ((n : ℝ) * m3)) * Shao.standardNormalTail y := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL hA.le)
        (Shao.standardNormalTail_basic.2.2.1 y).1.le
  have hC4 : 4 * K ≤ C := by dsimp [C]; nlinarith only [hK, mul_pos hK hA]
  have hC16 : 16 * K ≤ C := by dsimp [C]; nlinarith only [mul_pos hK hA]
  have hCtail : 16 * K * A ≤ C := by dsimp [C]; nlinarith only [hK]
  refine ⟨hDI, ?_, ?_, ?_⟩
  · intro j hj
    exact (hper j hj).trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hC4 (mul_nonneg hN.le hg.le)) (Real.exp_pos _).le)
  · apply hsumK.trans
    have hcoef : 16 * K * L2 ≤ C * (L2 + 1) := by
      nlinarith only [mul_le_mul_of_nonneg_right hC16 hL2.le, hC]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (by positivity)) (Real.exp_pos _).le
  · calc
      _ ≤ (16 * K * L2) * (((n : ℝ) * m3) * Real.exp (-4 * y ^ 2)) := by
        simpa only [mul_assoc] using hsumK
      _ ≤ (16 * K * L2) * (A * Lambda * Shao.standardNormalTail y) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = (16 * K * A * L2) * Lambda * Shao.standardNormalTail y := by ring
      _ ≤ _ := by
        have hcoef : 16 * K * A * L2 ≤ C * (L2 + 1) := by
          nlinarith only [mul_le_mul_of_nonneg_right hCtail hL2.le, hC]
        have hLn : 0 ≤ Lambda := by dsimp [Lambda]; positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hLn)
          (Shao.standardNormalTail_basic.2.2.1 y).1.le

end Shao.Probability
