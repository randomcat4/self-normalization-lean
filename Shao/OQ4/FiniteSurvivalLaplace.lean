import Shao.OQ4.LaplaceTail
import Shao.OQ4.LaplaceGenerating
import Shao.Basic.ClosedSurvival
import Shao.Probability.FiniteIID
import Mathlib.Algebra.BigOperators.Fin

namespace Shao.OQ4
open MeasureTheory ProbabilityTheory Finset Set
open scoped Topology

noncomputable def maxLaplaceIntegrand {j : ℕ} (L : ℝ) (a : Shao.Path j) : ℝ :=
  Real.exp (-Shao.maxWithZero a / L)

noncomputable def endpointLaplaceIntegrand {k : ℕ} (L : ℝ) (a : Shao.Path k) : ℝ :=
  Real.exp (-max (Shao.prefixSum a k) 0 / L)

noncomputable def maxLaplaceMean (ν : Measure ℝ) (L : ℝ) (j : ℕ) : ℝ :=
  ∫ a : Shao.Path j, maxLaplaceIntegrand L a ∂Measure.pi (fun _ : Fin j => ν)

noncomputable def endpointLaplaceMean (ν : Measure ℝ) (L : ℝ) (k : ℕ) : ℝ :=
  ∫ a : Shao.Path k, endpointLaplaceIntegrand L a ∂Measure.pi (fun _ : Fin k => ν)

theorem measurable_maxLaplaceIntegrand (j : ℕ) (L : ℝ) :
    Measurable (maxLaplaceIntegrand L : Shao.Path j → ℝ) := by
  have hH := (Shao.measurable_maxWithZero (n := j)).neg.div_const L
  exact Real.measurable_exp.comp hH

theorem measurable_endpointLaplaceIntegrand (k : ℕ) (L : ℝ) :
    Measurable (endpointLaplaceIntegrand L : Shao.Path k → ℝ) := by
  have hT := ((Shao.measurable_prefixSum (n := k) k).max (show Measurable (fun _ : Shao.Path k => (0 : ℝ)) from measurable_const)).neg.div_const L
  exact Real.measurable_exp.comp hT

theorem maxLaplaceIntegrand_bounds {j : ℕ} {L : ℝ} (hL : 0 < L) (a : Shao.Path j) :
    0 ≤ maxLaplaceIntegrand L a ∧ maxLaplaceIntegrand L a ≤ 1 := by
  constructor
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Shao.maxWithZero_nonneg a)) hL.le

theorem endpointLaplaceIntegrand_bounds {k : ℕ} {L : ℝ} (hL : 0 < L) (a : Shao.Path k) :
    0 ≤ endpointLaplaceIntegrand L a ∧ endpointLaplaceIntegrand L a ≤ 1 := by
  constructor
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_max_right _ 0)) hL.le

theorem integrable_maxLaplaceIntegrand (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (j : ℕ) {L : ℝ} (hL : 0 < L) :
    Integrable (maxLaplaceIntegrand L : Shao.Path j → ℝ) (Measure.pi (fun _ : Fin j => ν)) := by
  apply Integrable.of_bound (measurable_maxLaplaceIntegrand j L).aestronglyMeasurable 1
  exact ae_of_all _ fun a => by
    rw [Real.norm_eq_abs, abs_of_nonneg (maxLaplaceIntegrand_bounds hL a).1]
    exact (maxLaplaceIntegrand_bounds hL a).2

theorem integrable_endpointLaplaceIntegrand (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (k : ℕ) {L : ℝ} (hL : 0 < L) :
    Integrable (endpointLaplaceIntegrand L : Shao.Path k → ℝ) (Measure.pi (fun _ : Fin k => ν)) := by
  apply Integrable.of_bound (measurable_endpointLaplaceIntegrand k L).aestronglyMeasurable 1
  exact ae_of_all _ fun a => by
    rw [Real.norm_eq_abs, abs_of_nonneg (endpointLaplaceIntegrand_bounds hL a).1]
    exact (endpointLaplaceIntegrand_bounds hL a).2

theorem maxLaplaceMean_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (j : ℕ) {L : ℝ} (hL : 0 < L) : 0 ≤ maxLaplaceMean ν L j ∧ maxLaplaceMean ν L j ≤ 1 := by
  constructor
  · exact integral_nonneg fun a => (maxLaplaceIntegrand_bounds hL a).1
  · calc
      _ ≤ ∫ _a : Shao.Path j, (1 : ℝ) ∂Measure.pi (fun _ : Fin j => ν) :=
        integral_mono (integrable_maxLaplaceIntegrand ν j hL) (integrable_const 1)
          (fun a => (maxLaplaceIntegrand_bounds hL a).2)
      _ = 1 := by simp

theorem endpointLaplaceMean_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (k : ℕ) {L : ℝ} (hL : 0 < L) : 0 ≤ endpointLaplaceMean ν L k ∧ endpointLaplaceMean ν L k ≤ 1 := by
  constructor
  · exact integral_nonneg fun a => (endpointLaplaceIntegrand_bounds hL a).1
  · calc
      _ ≤ ∫ _a : Shao.Path k, (1 : ℝ) ∂Measure.pi (fun _ : Fin k => ν) :=
        integral_mono (integrable_endpointLaplaceIntegrand ν k hL) (integrable_const 1)
          (fun a => (endpointLaplaceIntegrand_bounds hL a).2)
      _ = 1 := by simp

theorem maxWithZero_empty (a : Shao.Path 0) : Shao.maxWithZero a = 0 := by
  apply le_antisymm
  · apply (Shao.maxWithZero_le_iff a 0).mpr
    intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    simp [hk0]
  · exact Shao.maxWithZero_nonneg a

theorem maxLaplaceMean_zero (ν : Measure ℝ) [IsProbabilityMeasure ν] (L : ℝ) :
    maxLaplaceMean ν L 0 = 1 := by
  unfold maxLaplaceMean
  have hf : (maxLaplaceIntegrand L : Shao.Path 0 → ℝ) = fun _ => 1 := by
    ext a
    simp [maxLaplaceIntegrand, maxWithZero_empty]
  rw [hf]
  simp

theorem finiteSumLaplacePayment_eq_one_sub_endpoint (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (k : ℕ) {L : ℝ} (hL : 0 < L) :
    finiteSumLaplacePayment ν k L = 1 - endpointLaplaceMean ν L k := by
  unfold finiteSumLaplacePayment endpointLaplaceMean
  change (∫ a : Shao.Path k, 1 - endpointLaplaceIntegrand L a ∂Measure.pi (fun _ : Fin k => ν)) = _
  rw [integral_sub (integrable_const 1) (integrable_endpointLaplaceIntegrand ν k hL)]
  simp

/-- The original unconditioned product law has the exact preceding-coordinate marginal. -/
theorem prefix_projection_map_pi (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) :
    Measure.map (fun a : Shao.Path (n + 1) => fun i : Fin n => a i.castSucc)
      (Measure.pi (fun _ : Fin (n + 1) => ν)) = Measure.pi (fun _ : Fin n => ν) := by
  have hI : iIndepFun (fun i : Fin (n + 1) => Function.eval i)
      (Measure.pi (fun _ : Fin (n + 1) => ν)) := by
    simpa using (iIndepFun_pi (μ := fun _ : Fin (n + 1) => ν)
      (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable))
  have hpre := hI.precomp (Fin.castSucc_injective (n := n))
  have hmap := hpre.map_fun_eq_pi_map (fun i => (measurable_pi_apply i.castSucc).aemeasurable)
  have hcoord (i : Fin n) : Measure.map (fun a : Shao.Path (n + 1) => a i.castSucc)
      (Measure.pi (fun _ : Fin (n + 1) => ν)) = ν :=
    (measurePreserving_eval (fun _ : Fin (n + 1) => ν) i.castSucc).map_eq
  simpa only [hcoord] using hmap

theorem prefix_projection_prefixSum {n : ℕ} (a : Shao.Path (n + 1)) (k : ℕ) (hk : k ≤ n) :
    Shao.prefixSum (fun i : Fin n => a i.castSucc) k = Shao.prefixSum a k := by
  simp [Shao.prefixSum, Finset.sum_filter, Fin.sum_univ_castSucc, not_lt.mpr hk]

theorem prefix_projection_max_le {n : ℕ} (a : Shao.Path (n + 1)) :
    Shao.maxWithZero (fun i : Fin n => a i.castSucc) ≤ Shao.maxWithZero a := by
  apply (Shao.maxWithZero_le_iff _ _).mpr
  intro k hk
  rw [prefix_projection_prefixSum a k hk]
  exact (Shao.maxWithZero_le_iff a _).mp le_rfl k (hk.trans (Nat.le_succ n))


theorem measurable_paymentLaplaceIntegrand (k : ℕ) (L : ℝ) :
    Measurable (fun a : Shao.Path k => positiveLaplace L (Shao.prefixSum a k)) := by
  exact (show Measurable (positiveLaplace L) by unfold positiveLaplace; fun_prop).comp
    (Shao.measurable_prefixSum k)

/-- Antitonicity is proved between the actual different-dimensional product laws. -/
theorem maxLaplaceMean_antitone (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {L : ℝ} (hL : 0 < L) : Antitone (maxLaplaceMean ν L) := by
  apply antitone_nat_of_succ_le
  intro n
  have hp : Measurable (fun a : Shao.Path (n + 1) => fun i : Fin n => a i.castSucc) :=
    Measurable.of_eval (fun i => measurable_pi_apply i.castSucc)
  have hf : Integrable (fun a : Shao.Path (n + 1) => maxLaplaceIntegrand L (fun i : Fin n => a i.castSucc))
      (Measure.pi (fun _ : Fin (n + 1) => ν)) := by
    apply Integrable.of_bound ((measurable_maxLaplaceIntegrand n L).comp hp).aestronglyMeasurable 1
    exact ae_of_all _ fun a => by
      dsimp only [Function.comp_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (maxLaplaceIntegrand_bounds hL _).1]
      exact (maxLaplaceIntegrand_bounds hL _).2
  have he : (∫ a : Shao.Path (n + 1), maxLaplaceIntegrand L (fun i : Fin n => a i.castSucc)
      ∂Measure.pi (fun _ : Fin (n + 1) => ν)) = maxLaplaceMean ν L n := by
    have hm := integral_map (μ := Measure.pi (fun _ : Fin (n + 1) => ν))
      hp.aemeasurable (measurable_maxLaplaceIntegrand n L).aestronglyMeasurable
    rw [prefix_projection_map_pi ν n] at hm
    exact hm.symm
  calc
    _ ≤ ∫ a : Shao.Path (n + 1), maxLaplaceIntegrand L (fun i : Fin n => a i.castSucc)
        ∂Measure.pi (fun _ : Fin (n + 1) => ν) := by
      apply integral_mono (integrable_maxLaplaceIntegrand ν (n + 1) hL) hf
      intro a
      exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg (prefix_projection_max_le a)) hL.le)
    _ = _ := he

theorem summable_maxLaplace_series (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {L s : ℝ} (hL : 0 < L) (hs0 : 0 < s) (hs1 : s < 1) :
    Summable (fun j : ℕ => s ^ j * maxLaplaceMean ν L j) :=
  summable_laplaceG _ hs0 hs1 (fun j => maxLaplaceMean_bounds ν j hL)

theorem summable_endpointLaplace_series (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {L s : ℝ} (hL : 0 < L) (hs0 : 0 < s) (hs1 : s < 1) :
    Summable (fun k : ℕ => s ^ (k + 1) * endpointLaplaceMean ν L (k + 1) / (k + 1)) :=
  summable_laplaceW (endpointLaplaceMean ν L) hs0 hs1 (fun k _ => endpointLaplaceMean_bounds ν k hL)

theorem summable_paymentLaplace_series (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {L s : ℝ} (hL : 0 < L) (hs0 : 0 < s) (hs1 : s < 1) :
    Summable (fun k : ℕ => s ^ (k + 1) * finiteSumLaplacePayment ν (k + 1) L / (k + 1)) :=
  summable_laplaceW (fun k => finiteSumLaplacePayment ν k L) hs0 hs1 (fun k _ => finiteSumLaplacePayment_bounds ν k hL)

/-- Derive the normalized identity from the original SP form and true summable series. -/
theorem maxLaplace_original_sp_to_normalized (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {L s : ℝ} (hL : 0 < L) (hs0 : 0 < s) (hs1 : s < 1)
    (hSP : laplaceG (maxLaplaceMean ν L) s = Real.exp (laplaceW (endpointLaplaceMean ν L) s)) :
    laplaceG (maxLaplaceMean ν L) s = (1 - s)⁻¹ *
      Real.exp (-laplaceW (fun k => finiteSumLaplacePayment ν k L) s) := by
  have hlog := Real.hasSum_pow_div_log_of_abs_lt_one (show |s| < 1 by rwa [abs_of_pos hs0])
  have hA := summable_paymentLaplace_series ν hL hs0 hs1
  have hh := hlog.sub hA.hasSum
  have hf : (fun k : ℕ => s ^ (k + 1) / (k + 1) - s ^ (k + 1) * finiteSumLaplacePayment ν (k + 1) L / (k + 1)) =
      (fun k : ℕ => s ^ (k + 1) * endpointLaplaceMean ν L (k + 1) / (k + 1)) := by
    ext k
    rw [finiteSumLaplacePayment_eq_one_sub_endpoint ν (k + 1) hL]
    ring
  rw [hf] at hh
  have hb : laplaceW (endpointLaplaceMean ν L) s =
      -Real.log (1 - s) - laplaceW (fun k => finiteSumLaplacePayment ν k L) s := hh.tsum_eq
  rw [hSP, hb]
  have ht : 0 < 1 - s := by linarith
  rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg, Real.exp_log ht]

/-- Actual finite-path Laplace coefficients under the unproved original SP and CDF inputs. -/
theorem maxLaplaceMean_bound_of_cdf_and_original_sp (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (C_BE β : ℝ) (hC : 0 ≤ C_BE) (hβ : 1 ≤ β)
    (hCDF : ∀ k : ℕ, 1 ≤ k → ∀ x : ℝ,
      |(Measure.pi (fun _ : Fin k => ν)).real {a : Shao.Path k | Shao.prefixSum a k / Real.sqrt k ≤ x} -
        standardNormalCDF x| ≤ C_BE * β / Real.sqrt k)
    (hSP : ∀ L : ℝ, 0 < L → ∀ s : ℝ, 0 < s → s < 1 →
      laplaceG (maxLaplaceMean ν L) s = Real.exp (laplaceW (endpointLaplaceMean ν L) s))
    (d : ℝ) (hd : 0 ≤ d) (m : ℕ) (hm : 1 ≤ m) :
    maxLaplaceMean ν (d + β) m ≤ Real.sqrt 2 * Real.exp (5 + 3 * C_BE) * (d + β) / Real.sqrt m := by
  let L := d + β
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hLp : 0 < L := by linarith
  have hβL : β ≤ L := by dsimp [L]; linarith
  have hA (k : ℕ) (_hk : 1 ≤ k) :
      0 ≤ finiteSumLaplacePayment ν k L ∧ finiteSumLaplacePayment ν k L ≤ 1 :=
    finiteSumLaplacePayment_bounds ν k hLp
  have hS1 (k : ℕ) (hk : 1 ≤ k) :
      1 / 2 - (1 + C_BE) * L / Real.sqrt k ≤ finiteSumLaplacePayment ν k L :=
    finiteSumLaplacePayment_lower_bound_of_cdf ν k hk C_BE β L hC hβ hβL (hCDF k hk)
  have hSP' (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
      laplaceG (maxLaplaceMean ν L) s = (1 - s)⁻¹ *
        Real.exp (-laplaceW (fun k => finiteSumLaplacePayment ν k L) s) :=
    maxLaplace_original_sp_to_normalized ν hLp hs0 hs1 (hSP L hLp s hs0 hs1)
  have hh := laplace_coefficient_bound (fun k => finiteSumLaplacePayment ν k L)
    (maxLaplaceMean ν L) L (1 + C_BE) hL (by linarith) hA hS1
    (fun j => maxLaplaceMean_bounds ν j hLp) (maxLaplaceMean_antitone ν hLp) hSP' m hm
  have he : 2 + 3 * (1 + C_BE) = 5 + 3 * C_BE := by ring
  simpa only [he] using hh

theorem measurableSet_closedUpper_laplace (m : ℕ) (d : ℝ) :
    MeasurableSet (Shao.closedUpper d : Set (Shao.Path m)) := by
  have hs : (Shao.closedUpper d : Set (Shao.Path m)) = {a | Shao.maxWithZero a ≤ d} := by
    ext a
    exact Shao.mem_closedUpper_iff_maxWithZero_le a d
  rw [hs]
  exact measurableSet_le Shao.measurable_maxWithZero measurable_const

/-- Closed survival is paid by the actual integrable maximum transform, with all atoms retained. -/
theorem closedUpper_probability_le_laplace (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (m : ℕ) (d : ℝ) (_hd : 0 ≤ d) {L : ℝ} (hL : 0 < L) :
    (Measure.pi (fun _ : Fin m => ν)).real (Shao.closedUpper d) ≤
      Real.exp (d / L) * maxLaplaceMean ν L m := by
  have hs := measurableSet_closedUpper_laplace m d
  have hp (a : Shao.Path m) : (Shao.closedUpper d).indicator (fun _ => (1 : ℝ)) a ≤
      Real.exp (d / L) * maxLaplaceIntegrand L a := by
    by_cases ha : a ∈ Shao.closedUpper d
    · rw [Set.indicator_of_mem ha]
      have hH := (Shao.mem_closedUpper_iff_maxWithZero_le a d).mp ha
      have he : 0 ≤ d / L + -Shao.maxWithZero a / L := by
        rw [neg_div, ← sub_eq_add_neg]
        exact sub_nonneg.mpr (div_le_div_of_nonneg_right hH hL.le)
      have hh := Real.one_le_exp_iff.mpr he
      rwa [Real.exp_add] at hh
    · rw [Set.indicator_of_notMem ha]
      exact mul_nonneg (Real.exp_pos _).le (maxLaplaceIntegrand_bounds hL a).1
  have hi := integral_mono ((integrable_const (1 : ℝ)).indicator hs)
    ((integrable_maxLaplaceIntegrand ν m hL).const_mul (Real.exp (d / L))) hp
  rw [integral_indicator hs, integral_const_mul, setIntegral_const] at hi
  simpa only [smul_eq_mul, mul_one, maxLaplaceMean] using hi

/-- Conditional one-sided closed survival from the explicit CDF and original SP inputs. -/
theorem closedUpper_bound_of_cdf_and_original_sp (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (C_BE β : ℝ) (hC : 0 ≤ C_BE) (hβ : 1 ≤ β)
    (hCDF : ∀ k : ℕ, 1 ≤ k → ∀ x : ℝ,
      |(Measure.pi (fun _ : Fin k => ν)).real {a : Shao.Path k | Shao.prefixSum a k / Real.sqrt k ≤ x} -
        standardNormalCDF x| ≤ C_BE * β / Real.sqrt k)
    (hSP : ∀ L : ℝ, 0 < L → ∀ s : ℝ, 0 < s → s < 1 →
      laplaceG (maxLaplaceMean ν L) s = Real.exp (laplaceW (endpointLaplaceMean ν L) s))
    (d : ℝ) (hd : 0 ≤ d) (m : ℕ) (hm : 1 ≤ m) :
    (Measure.pi (fun _ : Fin m => ν)).real (Shao.closedUpper d) ≤
      Real.sqrt 2 * Real.exp (6 + 3 * C_BE) * (d + β) / Real.sqrt m := by
  have hL : 0 < d + β := by linarith
  have hr : d / (d + β) ≤ 1 := (div_le_one hL).mpr (by linarith)
  have he := Real.exp_le_exp.mpr hr
  have hcoef := maxLaplaceMean_bound_of_cdf_and_original_sp ν C_BE β hC hβ hCDF hSP d hd m hm
  have hconst : Real.exp 1 * Real.exp (5 + 3 * C_BE) = Real.exp (6 + 3 * C_BE) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ Real.exp (d / (d + β)) * maxLaplaceMean ν (d + β) m :=
      closedUpper_probability_le_laplace ν m d hd hL
    _ ≤ Real.exp 1 * maxLaplaceMean ν (d + β) m :=
      mul_le_mul_of_nonneg_right he (maxLaplaceMean_bounds ν m hL).1
    _ ≤ Real.exp 1 * (Real.sqrt 2 * Real.exp (5 + 3 * C_BE) * (d + β) / Real.sqrt m) :=
      mul_le_mul_of_nonneg_left hcoef (Real.exp_pos 1).le
    _ = Real.sqrt 2 * (Real.exp 1 * Real.exp (5 + 3 * C_BE)) * (d + β) / Real.sqrt m := by ring
    _ = _ := by rw [hconst]

end Shao.OQ4
