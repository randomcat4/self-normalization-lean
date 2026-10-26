/- Unit219 actual implementation prefix P1/P2/P3/public1. No later incomplete declarations. Native NOT_RUN. -/
import Shao.C2.ActualRetainedResidualBudgets
import Shao.Probability.SourceTerminalEnvelope
import Shao.Probability.SourceOneSidedRelativeError
import Shao.Probability.SourceScalarInitialBudget
import Shao.Probability.SourceActualIntervalInitialCDF
import Shao.Probability.SourceOriginalZeroEnergyBudget
import Shao.C2.BridgeHalfLineJointLaw

set_option autoImplicit false
noncomputable section
namespace Shao.C2.ActualBoundedCenteredFixed
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical NNReal ENNReal
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.ActualSignedDoubleTelescope
open Shao.C2.ActualRetainedResidualBudgets
open Shao.Probability.SourcePermutationReveal
open Shao.Probability.SourceSeparatedOvershoot
open Shao.Probability.SourceIIDGaussianProfileBudget
open Shao.Probability.SourceMarkedSuffixAveraging

local instance labelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

/- Five proposed transparent private values. No theorem proof occurs here.
   Existing firstValue, suffixD, actualRetainedAbsoluteRank and actualDoubleRetained
   are reused, with their complete old transparent values in consumed-interfaces. -/
private def abcf_suffixCubic (H : ℝ) {t : ℕ} (u : Shao.Path t) : ℝ :=
  if 0 < Shao.energy u ∧ H ≤ Shao.energy u then
    |firstValue u| ^ 3 / (Shao.energy u * Real.sqrt (Shao.energy u)) * suffixD u ^ 3
  else 0

private def abcf_suffixLate (H beta : ℝ) (n k : ℕ) {t : ℕ}
    (u : Shao.Path t) : ℝ :=
  if 0 < Shao.energy u ∧ H ≤ Shao.energy u then
    |firstValue u| ^ 3 / (Shao.energy u * Real.sqrt (Shao.energy u)) * suffixD u ^ k *
      (Shao.energy u / ((n - t : ℕ) : ℝ) + beta ^ 2 / ((n - t : ℕ) : ℝ))
  else 0

private def abcf_jointBill {n : ℕ} (Q : Measure BridgeNoise) (x : ℝ)
    (nu : Shao.Path n → LabelPerm n → ℕ) (p : Shao.Path n × LabelPerm n) : ℝ :=
  ∑ r : Fin n, actualRetainedAbsoluteRank Q p.1 x (nu p.1) r p.2

private def abcf_futureAt {n : ℕ} (J : MonitoredDomain) (Q : Measure BridgeNoise)
    (x : ℝ) (r : ℕ) (p : Shao.Path n × LabelPerm n) : ℝ :=
  (Finset.range (n + 1)).sup'
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩
    (fun j => if r ≤ j then
      |sourceValue J (eventCompletionKernel J Q) p.1 x j p.2 -
        (if sourceAlive J p.1 x n p.2 then 1 else 0)| else 0)

private def abcf_h0Future {n : ℕ} (J : MonitoredDomain) (Q : Measure BridgeNoise)
    (H x : ℝ) (p : Shao.Path n × LabelPerm n) : ℝ :=
  abcf_futureAt J Q x (energyCutoff p.1 H p.2) p

/- PRIVATE HEAD P1. Own-law identities and all moment/positivity obligations.
   n >= 2500 is a derived conclusion, never an added public assumption. -/
private theorem abcf_bounded_own_budget_identities
    (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (bound : ℝ) (hb : 0 < bound) (hsupport : ∀ᵐ z : ℝ ∂rho, |z| ≤ bound)
    (hmean : (∫ z : ℝ, z ∂rho) = 0)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂rho) = 1)
    (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : (1 / 2 : ℝ) ≤ x)
    (hscale : bound ≤ Real.sqrt (n : ℝ) / (100 * x)) :
    let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
    let delta : ℝ := beta / Real.sqrt (n : ℝ)
    let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) rho
    Integrable (fun z : ℝ => z) rho ∧
      Integrable (fun z : ℝ => z ^ 2) rho ∧ Integrable (fun z : ℝ => |z| ^ 3) rho ∧
      1 ≤ bound ∧ 1 ≤ beta ∧ 0 < delta ∧ 0 < 4 * beta ^ 2 ∧ 2500 ≤ n ∧
      Shao.truncationBudget normalizedLaw n 0 = delta ∧
      Shao.truncationBudget normalizedLaw n x = delta * (1 + x) ^ 3 ∧
      4 * (n : ℝ) * (Shao.truncationBudget normalizedLaw n 0) ^ 2 = 4 * beta ^ 2 ∧
      ∀ t ∈ Finset.Icc 1 (n / 2),
        Shao.truncationBudget
          (Measure.map (fun z : ℝ => z / Real.sqrt ((n - t : ℕ) : ℝ)) rho)
          (n - t) 0 = beta / Real.sqrt ((n - t : ℕ) : ℝ) := by
  classical
  intro beta delta normalizedLaw
  have hmem (k : ℕ) : MemLp (fun z : ℝ => |z| ^ k) 1 rho := by
    refine MemLp.of_bound (by fun_prop) (bound ^ k) ?_
    filter_upwards [hsupport] with z hz
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg z) k)] using
      pow_le_pow_left₀ (abs_nonneg z) hz k
  have h1 : Integrable (fun z : ℝ => z) rho := by
    apply memLp_one_iff_integrable.mp
    exact MemLp.of_bound continuous_id.aestronglyMeasurable bound
      (by simpa only [Real.norm_eq_abs] using hsupport)
  have h2 : Integrable (fun z : ℝ => z ^ 2) rho := by
    have hi := memLp_one_iff_integrable.mp (hmem 2)
    simpa only [sq_abs] using hi
  have h3 : Integrable (fun z : ℝ => |z| ^ 3) rho :=
    memLp_one_iff_integrable.mp (hmem 3)
  have hB : 1 ≤ bound := by
    have hb2 : (∫ z : ℝ, z ^ 2 ∂rho) ≤ bound ^ 2 := by
      calc
        _ ≤ ∫ _ : ℝ, bound ^ 2 ∂rho := integral_mono_ae h2 (integrable_const _)
          (hsupport.mono fun z hz => by
            simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z) hz 2)
        _ = bound ^ 2 := by simp
    rw [hsecond] at hb2
    nlinarith only [hb2, hb]
  have hbeta : 1 ≤ beta := by
    have hYoung (z : ℝ) : z ^ 2 ≤ (2 / 3 : ℝ) * |z| ^ 3 + 1 / 3 := by
      have hfactor : 0 ≤ (|z| - 1) ^ 2 * (2 * |z| + 1) :=
        mul_nonneg (sq_nonneg _) (by positivity)
      nlinarith only [hfactor, sq_abs z]
    have hi := integral_mono h2 ((h3.const_mul (2 / 3)).add (integrable_const (1 / 3))) hYoung
    change (∫ z : ℝ, z ^ 2 ∂rho) ≤ (∫ z : ℝ, (2 / 3 : ℝ) * |z| ^ 3 + 1 / 3 ∂rho) at hi
    rw [integral_add (h3.const_mul (2 / 3)) (integrable_const (1 / 3)),
      integral_const_mul, hsecond] at hi
    simp only [integral_const, probReal_univ, one_smul] at hi
    dsimp only [beta]
    linarith only [hi]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hs2 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hxpos : 0 < x := by linarith only [hx]
  have h100 : 1 ≤ 100 * x := by linarith only [hx]
  have hscaled : (100 * x) * bound ≤ Real.sqrt (n : ℝ) := by
    simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < 100 * x)).mp hscale
  have hBroot : bound ≤ Real.sqrt (n : ℝ) :=
    (le_mul_of_one_le_left hb.le h100).trans hscaled
  have h50 : 50 * bound ≤ Real.sqrt (n : ℝ) := by
    calc
      50 * bound ≤ (100 * x) * bound := mul_le_mul_of_nonneg_right (by linarith only [hx]) hb.le
      _ ≤ _ := hscaled
  have hn2500 : 2500 ≤ n := by
    have hroot50 : (50 : ℝ) ≤ Real.sqrt (n : ℝ) := by nlinarith only [h50, hB]
    have hh : (2500 : ℝ) ≤ (n : ℝ) := by nlinarith only [hroot50, hs2]
    exact_mod_cast hh
  have hbudget (m : ℕ) (hm : 0 < m) (u : ℝ) (hu : 0 ≤ u)
      (hsmall : ∀ᵐ z : ℝ ∂rho, |(1 + u) * (z / Real.sqrt (m : ℝ))| ≤ 1) :
      Shao.truncationBudget
        (Measure.map (fun z : ℝ => z / Real.sqrt (m : ℝ)) rho) m u =
          beta * (1 + u) ^ 3 / Real.sqrt (m : ℝ) := by
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
    have hsm2 : (Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) := Real.sq_sqrt hmR.le
    have hmap : Measurable (fun z : ℝ => z / Real.sqrt (m : ℝ)) := by fun_prop
    have hFm : AEStronglyMeasurable (fun z : ℝ => Shao.truncationF ((1 + u) * z))
        (Measure.map (fun z : ℝ => z / Real.sqrt (m : ℝ)) rho) := by
      unfold Shao.truncationF
      fun_prop
    unfold Shao.truncationBudget
    rw [integral_map hmap.aemeasurable hFm]
    have heq : (fun z : ℝ => Shao.truncationF ((1 + u) * (z / Real.sqrt (m : ℝ)))) =ᵐ[rho]
        (fun z : ℝ => ((1 + u) ^ 3 / (Real.sqrt (m : ℝ)) ^ 3) * |z| ^ 3) := by
      filter_upwards [hsmall] with z hz
      unfold Shao.truncationF
      rw [min_eq_left hz]
      have habs : |(1 + u) * (z / Real.sqrt (m : ℝ))| =
          (1 + u) * |z| / Real.sqrt (m : ℝ) := by
        rw [abs_mul, abs_div, abs_of_nonneg (by linarith only [hu]), abs_of_pos hsm]
        ring
      calc
        ((1 + u) * (z / Real.sqrt (m : ℝ))) ^ 2 *
            |(1 + u) * (z / Real.sqrt (m : ℝ))| =
            |(1 + u) * (z / Real.sqrt (m : ℝ))| ^ 2 *
              |(1 + u) * (z / Real.sqrt (m : ℝ))| := by rw [sq_abs]
        _ = |(1 + u) * (z / Real.sqrt (m : ℝ))| ^ 3 := by ring
        _ = _ := by rw [habs]; ring
    rw [integral_congr_ae heq, integral_const_mul]
    change (m : ℝ) * ((1 + u) ^ 3 / (Real.sqrt (m : ℝ)) ^ 3 * beta) = _
    calc
      _ = (Real.sqrt (m : ℝ)) ^ 2 *
          ((1 + u) ^ 3 / (Real.sqrt (m : ℝ)) ^ 3 * beta) := by rw [hsm2]
      _ = _ := by field_simp [hsm.ne'] <;> ring
  have hsmall0 : ∀ᵐ z : ℝ ∂rho, |(1 + (0 : ℝ)) * (z / Real.sqrt (n : ℝ))| ≤ 1 := by
    filter_upwards [hsupport] with z hz
    simpa only [add_zero, one_mul, abs_div, abs_of_pos hs] using
      (div_le_one hs).mpr (hz.trans hBroot)
  have hR0 : Shao.truncationBudget normalizedLaw n 0 = delta := by
    simpa only [normalizedLaw, delta, add_zero, one_pow, mul_one] using
      hbudget n hn 0 le_rfl hsmall0
  have hsmallx : ∀ᵐ z : ℝ ∂rho, |(1 + x) * (z / Real.sqrt (n : ℝ))| ≤ 1 := by
    filter_upwards [hsupport] with z hz
    rw [abs_mul, abs_div, abs_of_pos (by linarith only [hx] : 0 < 1 + x), abs_of_pos hs]
    rw [← mul_div_assoc, div_le_one hs]
    calc
      (1 + x) * |z| ≤ (100 * x) * bound :=
        mul_le_mul (by linarith only [hx]) hz (abs_nonneg z) (by positivity)
      _ ≤ _ := hscaled
  have hRx : Shao.truncationBudget normalizedLaw n x = delta * (1 + x) ^ 3 := by
    have hh := hbudget n hn x hxpos.le hsmallx
    simpa only [normalizedLaw, delta, div_mul_eq_mul_div] using hh
  have hcut : 4 * (n : ℝ) * (Shao.truncationBudget normalizedLaw n 0) ^ 2 = 4 * beta ^ 2 := by
    rw [hR0]
    dsimp only [delta]
    rw [div_pow]
    rw [hs2]
    field_simp [hnR.ne']
    <;> ring
  refine ⟨h1, h2, h3, hB, hbeta, by dsimp [delta]; positivity,
    by positivity, hn2500, hR0, hRx, hcut, ?_⟩
  intro t ht
  have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
  have htN : t ≤ n / 2 := (Finset.mem_Icc.mp ht).2
  have hm : 0 < n - t := by omega
  have hmR : 0 < ((n - t : ℕ) : ℝ) := by exact_mod_cast hm
  have hsm : 0 < Real.sqrt ((n - t : ℕ) : ℝ) := Real.sqrt_pos.mpr hmR
  have hsm2 : (Real.sqrt ((n - t : ℕ) : ℝ)) ^ 2 = ((n - t : ℕ) : ℝ) := Real.sq_sqrt hmR.le
  have hhalf : (n : ℝ) ≤ 2 * ((n - t : ℕ) : ℝ) := by exact_mod_cast (show n ≤ 2 * (n - t) by omega)
  have hbsq : bound ^ 2 ≤ ((n - t : ℕ) : ℝ) := by
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 50 * bound) hs.le).mpr h50
    nlinarith only [hsq, hs2, hhalf, sq_nonneg bound, hmR]
  have hbsm : bound ≤ Real.sqrt ((n - t : ℕ) : ℝ) := by
    nlinarith only [hbsq, hsm2, hsm.le, hb]
  have hsmall : ∀ᵐ z : ℝ ∂rho, |(1 + (0 : ℝ)) * (z / Real.sqrt ((n - t : ℕ) : ℝ))| ≤ 1 := by
    filter_upwards [hsupport] with z hz
    simpa only [add_zero, one_mul, abs_div, abs_of_pos hsm] using
      (div_le_one hsm).mpr (hz.trans hbsm)
  simpa only [add_zero, one_pow, mul_one] using hbudget (n - t) hm 0 le_rfl hsmall

private theorem abcf_suffix_grid_payment :
    ∃ CE CL : ℝ, 0 < CE ∧ 0 < CL ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (bound : ℝ), 0 < bound → (∀ᵐ z : ℝ ∂rho, |z| ≤ bound) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), (1 / 2 : ℝ) ≤ x →
          bound ≤ Real.sqrt (n : ℝ) / (100 * x) →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          let delta : ℝ := beta / Real.sqrt (n : ℝ)
          let H : ℝ := 4 * beta ^ 2
          let Pt : (t : ℕ) → Measure (Shao.Path t) := fun t => Measure.pi (fun _ : Fin t => rho)
          (∀ t ∈ Finset.Icc (n / 2 + 1) n,
            Measurable (@abcf_suffixCubic H t) ∧ Integrable (@abcf_suffixCubic H t) (Pt t) ∧
              ∀ u : Shao.Path t, 0 ≤ abcf_suffixCubic H u) ∧
          (∑ t ∈ Finset.Icc (n / 2 + 1) n, ∫ u, abcf_suffixCubic H u ∂Pt t) ≤ CE * delta ∧
          ∀ k : ℕ, (k = 3 ∨ k = 5) →
            (∀ t ∈ Finset.Icc 1 (n / 2),
              Measurable (@abcf_suffixLate H beta n k t) ∧
              Integrable (@abcf_suffixLate H beta n k t) (Pt t) ∧
              ∀ u : Shao.Path t, 0 ≤ abcf_suffixLate H beta n k u) ∧
            (∑ t ∈ Finset.Icc 1 (n / 2), ∫ u, abcf_suffixLate H beta n k u ∂Pt t) ≤ CL * delta := by
  classical
  obtain ⟨CE, hCE, hEarly⟩ := Shao.Probability.iid_early_cubic_suffix_budget
  obtain ⟨CL, hCL, hLate⟩ := Shao.Probability.iid_late_fifth_and_cubic_suffix_budgets
  refine ⟨4 * CE, CL, by positivity, hCL, ?_⟩
  intro rho hProb bound hb hsupport hmean hsecond n hn x hx hscale beta delta H Pt
  letI : IsProbabilityMeasure rho := hProb
  rcases abcf_bounded_own_budget_identities rho bound hb hsupport hmean hsecond n hn x hx hscale with
    ⟨h1, h2, h3, hB, hbeta, hdelta, hH, hnlarge, hR0, hRx, hcut, hprefix⟩
  change 0 < H at hH
  let P : Measure (Shao.Path n) := Pt n
  let Rprefix : ℕ → ℝ := fun t => Shao.truncationBudget
    (Measure.map (fun z : ℝ => z / Real.sqrt ((n - t : ℕ) : ℝ)) rho) (n - t) 0
  let E : (t : ℕ) → Shao.Path t → ℝ := fun t u =>
    if 0 < Shao.energy u ∧ H ≤ Shao.energy u then
      (if ht : 0 < t then |u ⟨0, ht⟩| ^ 3 else 0) /
        (Shao.energy u * Real.sqrt (Shao.energy u)) *
        (1 + |Shao.prefixSum u t| ^ 3 / (Shao.energy u * Real.sqrt (Shao.energy u)))
    else 0
  have hEdata :
      (∀ t ∈ Finset.Icc ((n + 1) / 2) n, Integrable (E t) (Pt t)) ∧
        (∑ t ∈ Finset.Icc ((n + 1) / 2) n, ∫ u, E t u ∂Pt t) ≤ CE * delta := by
    have he := hEarly rho n hn h2 hmean (by rw [hsecond]; norm_num)
    simp only [hsecond, mul_one] at he
    rw [hcut] at he
    simpa only [hR0, E, Pt] using he
  let oldLate : ℕ → Shao.Path n → ℝ := fun t a =>
    let u := Shao.Probability.Spitzer.tail a (n - t) (Nat.sub_le n t)
    if 0 < Shao.energy u ∧ H ≤ Shao.energy u then
      (suffixBeta u / (t : ℝ)) * suffixD u ^ 5 *
        (Shao.energy u / ((n - t : ℕ) : ℝ) + Rprefix t ^ 2) else 0
  have hOldLate :
      (∀ t ∈ Finset.Icc 1 (n / 2), Integrable (oldLate t) P) ∧
      (∑ t ∈ Finset.Icc 1 (n / 2), ∫ a, oldLate t a ∂P) ≤ CL * delta := by
    have he := hLate rho n hn h2 hmean (by rw [hsecond]; norm_num) 5 (Or.inr rfl)
    simp only [hsecond, mul_one] at he
    rw [hcut] at he
    simpa only [hR0, oldLate, suffixBeta, cubicMass, suffixD, Rprefix, Pt, P] using he
  have hLateEq (t : ℕ) (ht : t ∈ Finset.Icc 1 (n / 2)) :
      oldLate t = (fun a : Shao.Path n =>
        lateAveragedWeight H ((n - t : ℕ) : ℝ) (Rprefix t)
          (Shao.Probability.Spitzer.tail a (n - t) (Nat.sub_le n t))) := by
    have htn : t ≤ n := (Finset.mem_Icc.mp ht).2.trans (Nat.div_le_self n 2)
    have hlen : n - (n - t) = t := by omega
    funext a
    dsimp only [oldLate, lateAveragedWeight]
    by_cases hh : H ≤ Shao.energy (Shao.Probability.Spitzer.tail a (n - t) (Nat.sub_le n t))
    · have hp := hH.trans_le hh
      simp only [hh, hp, true_and, ite_true, hlen]
    · simp only [hh, and_false, ite_false]
  have hLateData :
      (∀ t ∈ Finset.Icc 1 (n / 2),
        Integrable (fun a : Shao.Path n => lateAveragedWeight H ((n - t : ℕ) : ℝ)
          (Rprefix t) (Shao.Probability.Spitzer.tail a (n - t) (Nat.sub_le n t))) P) ∧
      (∑ t ∈ Finset.Icc 1 (n / 2),
        ∫ a : Shao.Path n, lateAveragedWeight H ((n - t : ℕ) : ℝ)
          (Rprefix t) (Shao.Probability.Spitzer.tail a (n - t) (Nat.sub_le n t)) ∂P) ≤ CL * delta := by
    constructor
    · intro t ht
      rw [← hLateEq t ht]
      exact hOldLate.1 t ht
    · calc
        _ = ∑ t ∈ Finset.Icc 1 (n / 2), ∫ a, oldLate t a ∂P := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [hLateEq t ht]
        _ ≤ _ := hOldLate.2
  have hfirst (t : ℕ) : Measurable (firstValue : Shao.Path t → ℝ) := by
    change Measurable (fun u : Shao.Path t => if ht : 0 < t then u ⟨0, ht⟩ else 0)
    by_cases ht : 0 < t
    · simpa only [dif_pos ht] using (measurable_pi_apply (⟨0, ht⟩ : Fin t))
    · simpa only [dif_neg ht] using (measurable_const : Measurable (fun _ : Shao.Path t => (0 : ℝ)))
  have hDm (t : ℕ) : Measurable (suffixD : Shao.Path t → ℝ) := by
    exact Measurable.ite (measurableSet_lt measurable_const Shao.measurable_energy)
      (measurable_const.add ((continuous_abs.measurable.comp (Shao.measurable_prefixSum t)).div Shao.measurable_energy.sqrt)) measurable_const
  have hCubicM (t : ℕ) : Measurable (@abcf_suffixCubic H t) :=
    Measurable.ite ((measurableSet_lt measurable_const Shao.measurable_energy).inter
      (measurableSet_le measurable_const Shao.measurable_energy))
      ((((continuous_abs.measurable.comp (hfirst t)).pow_const 3).div (Shao.measurable_energy.mul Shao.measurable_energy.sqrt)).mul
        ((hDm t).pow_const 3)) measurable_const
  have hLateM (k t : ℕ) : Measurable (@abcf_suffixLate H beta n k t) :=
    Measurable.ite ((measurableSet_lt measurable_const Shao.measurable_energy).inter
      (measurableSet_le measurable_const Shao.measurable_energy))
      (((((continuous_abs.measurable.comp (hfirst t)).pow_const 3).div (Shao.measurable_energy.mul Shao.measurable_energy.sqrt)).mul
        ((hDm t).pow_const k)).mul ((Shao.measurable_energy.div_const _).add measurable_const)) measurable_const
  have hCubic0 (t : ℕ) (u : Shao.Path t) : 0 ≤ abcf_suffixCubic H u := by
    have hU0 := Shao.energy_nonneg u
    have hD0 : 0 ≤ suffixD u := by unfold suffixD; split_ifs <;> positivity
    unfold abcf_suffixCubic
    split_ifs <;> positivity
  have hLate0 (k t : ℕ) (u : Shao.Path t) : 0 ≤ abcf_suffixLate H beta n k u := by
    have hU0 := Shao.energy_nonneg u
    have hD0 : 0 ≤ suffixD u := by unfold suffixD; split_ifs <;> positivity
    unfold abcf_suffixLate
    split_ifs <;> positivity
  have hCubicLe (t : ℕ) (u : Shao.Path t) : abcf_suffixCubic H u ≤ 4 * E t u := by
    by_cases hh : 0 < Shao.energy u ∧ H ≤ Shao.energy u
    · have ht : 0 < t := by
        by_contra ht
        have ht0 : t = 0 := Nat.eq_zero_of_not_pos ht
        subst t
        simpa [Shao.energy] using hh.1
      have hs : 0 < Real.sqrt (Shao.energy u) := Real.sqrt_pos.mpr hh.1
      let z : ℝ := |Shao.prefixSum u t| / Real.sqrt (Shao.energy u)
      have hz : 0 ≤ z := by positivity
      have hpoly : (1 + z) ^ 3 ≤ 4 * (1 + z ^ 3) := by
        nlinarith [mul_nonneg (sq_nonneg (z - 1)) (by positivity : 0 ≤ z + 1)]
      have hden : (Real.sqrt (Shao.energy u)) ^ 3 = Shao.energy u * Real.sqrt (Shao.energy u) := by
        calc
          _ = (Real.sqrt (Shao.energy u)) ^ 2 * Real.sqrt (Shao.energy u) := by ring
          _ = _ := by rw [Real.sq_sqrt hh.1.le]
      have hsh : suffixD u ^ 3 ≤ 4 * (1 + |Shao.prefixSum u t| ^ 3 /
          (Shao.energy u * Real.sqrt (Shao.energy u))) := by
        simpa only [suffixD, if_pos hh.1, z, div_pow, hden] using hpoly
      dsimp only [abcf_suffixCubic, E]
      rw [if_pos hh, if_pos hh, firstValue, dif_pos ht, dif_pos ht]
      nlinarith only [mul_le_mul_of_nonneg_left hsh
        (show 0 ≤ |u ⟨0, ht⟩| ^ 3 / (Shao.energy u * Real.sqrt (Shao.energy u)) from
          div_nonneg (pow_nonneg (abs_nonneg _) 3)
            (mul_nonneg (Shao.energy_nonneg u) (Real.sqrt_nonneg (Shao.energy u))))]
    · simp only [abcf_suffixCubic, E, if_neg hh, mul_zero, le_refl]
  have hEarlyInt (t : ℕ) (ht : t ∈ Finset.Icc (n / 2 + 1) n) :
      Integrable (@abcf_suffixCubic H t) (Pt t) := by
    have ht' : t ∈ Finset.Icc ((n + 1) / 2) n := by
      apply Finset.mem_Icc.mpr
      have hh := Finset.mem_Icc.mp ht
      omega
    exact ((hEdata.1 t ht').const_mul 4).mono' (hCubicM t).aestronglyMeasurable
      (ae_of_all _ fun u => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hCubic0 t u)] using hCubicLe t u)
  have hEarlySum : (∑ t ∈ Finset.Icc (n / 2 + 1) n, ∫ u, abcf_suffixCubic H u ∂Pt t) ≤
      (4 * CE) * delta := by
    have hsub : Finset.Icc (n / 2 + 1) n ⊆ Finset.Icc ((n + 1) / 2) n := by
      intro t ht
      have hh := Finset.mem_Icc.mp ht
      apply Finset.mem_Icc.mpr
      omega
    calc
      _ ≤ ∑ t ∈ Finset.Icc (n / 2 + 1) n, 4 * (∫ u, E t u ∂Pt t) := by
        apply Finset.sum_le_sum
        intro t ht
        have hi := integral_mono (hEarlyInt t ht) ((hEdata.1 t (hsub ht)).const_mul 4) (hCubicLe t)
        simpa only [integral_const_mul] using hi
      _ = 4 * (∑ t ∈ Finset.Icc (n / 2 + 1) n, ∫ u, E t u ∂Pt t) := by rw [Finset.mul_sum]
      _ ≤ 4 * (∑ t ∈ Finset.Icc ((n + 1) / 2) n, ∫ u, E t u ∂Pt t) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro t _ _
        apply integral_nonneg
        intro u
        have hU0 := Shao.energy_nonneg u
        dsimp [E]
        split_ifs <;> positivity
      _ ≤ 4 * (CE * delta) := mul_le_mul_of_nonneg_left hEdata.2 (by norm_num)
      _ = _ := by ring
  have hLate5 (t : ℕ) (ht : t ∈ Finset.Icc 1 (n / 2)) :
      Integrable (@abcf_suffixLate H beta n 5 t) (Pt t) ∧
        (∫ u, abcf_suffixLate H beta n 5 u ∂Pt t) =
          ∫ a : Shao.Path n, lateAveragedWeight H ((n - t : ℕ) : ℝ) (Rprefix t)
            (Shao.Probability.Spitzer.tail a (n - t) (Nat.sub_le n t)) ∂P := by
    have ht0 : 0 < t := (Finset.mem_Icc.mp ht).1
    have htn : t ≤ n := (Finset.mem_Icc.mp ht).2.trans (Nat.div_le_self n 2)
    have hlen : n - (n - t) = t := by omega
    have hr : 0 < n - t := by have hh := (Finset.mem_Icc.mp ht).2; omega
    have hrR : 0 < ((n - t : ℕ) : ℝ) := by exact_mod_cast hr
    have hRt : Rprefix t = beta / Real.sqrt ((n - t : ℕ) : ℝ) := hprefix t ht
    have hRt2 : Rprefix t ^ 2 = beta ^ 2 / ((n - t : ℕ) : ℝ) := by
      rw [hRt, div_pow, Real.sq_sqrt hrR.le]
    let j : Fin t := ⟨0, ht0⟩
    have hm := iid_product_late_marked_integral_eq_average ht0 rho h2 H ((n - t : ℕ) : ℝ)
      (Rprefix t) hH hrR j
    have hmark (u : Shao.Path t) :
        lateMarkedWeight H ((n - t : ℕ) : ℝ) (Rprefix t) u j = abcf_suffixLate H beta n 5 u := by
      by_cases hh : H ≤ Shao.energy u
      · have hT := hH.trans_le hh
        simp only [lateMarkedWeight, normalizedCubicMark, abcf_suffixLate, hh, hT,
          and_self, ite_true, firstValue, dif_pos ht0, j, hRt2]
      · simp only [lateMarkedWeight, abcf_suffixLate, hh, and_false, ite_false]
    have hInt : Integrable (@abcf_suffixLate H beta n 5 t) (Pt t) := by
      have heq : (fun u : Shao.Path t => lateMarkedWeight H ((n - t : ℕ) : ℝ) (Rprefix t) u j) =
          @abcf_suffixLate H beta n 5 t := funext hmark
      rw [← heq]
      exact hm.1
    let m : ℕ := n - (n - t)
    let split : Shao.Path n → Shao.Path (n - t) × Shao.Path m := fun a =>
      (Shao.Probability.Spitzer.head a (n - t) (Nat.sub_le n t),
        Shao.Probability.Spitzer.tail a (n - t) (Nat.sub_le n t))
    let e : Fin (n - t) ⊕ Fin m ≃ Fin n :=
      finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le (Nat.sub_le n t)))
    have hsplit : MeasurePreserving split P ((Pt (n - t)).prod (Pt m)) := by
      convert (measurePreserving_sumPiEquivProdPi (fun _ : Fin (n - t) ⊕ Fin m => rho)).comp
        (measurePreserving_piCongrLeft (fun _ : Fin n => rho) e).symm using 1
      ext a i <;> change a _ = a _ <;> congr 1
    have htail : MeasurePreserving
        (fun a : Shao.Path n => Shao.Probability.Spitzer.tail a (n - t) (Nat.sub_le n t)) P (Pt m) :=
      (measurePreserving_snd (μ := Pt (n - t)) (ν := Pt m)).comp hsplit
    have hAm : Measurable (lateAveragedWeight H ((n - t : ℕ) : ℝ) (Rprefix t) : Shao.Path m → ℝ) :=
      (late_weights_measurable_and_covariant H ((n - t : ℕ) : ℝ) (Rprefix t)).2.1
    have hdist : IdentDistrib
        (fun a : Shao.Path n => Shao.Probability.Spitzer.tail a (n - t) (Nat.sub_le n t))
        (id : Shao.Path m → Shao.Path m) P (Pt m) := by
      exact ⟨htail.measurable.aemeasurable, measurable_id.aemeasurable, by
        simpa only [Measure.map_id] using htail.map_eq⟩
    have he := (hdist.comp hAm).integral_eq
    have he' : (∫ u : Shao.Path t, lateAveragedWeight H ((n - t : ℕ) : ℝ) (Rprefix t) u ∂Pt t) =
        ∫ a : Shao.Path n, lateAveragedWeight H ((n - t : ℕ) : ℝ) (Rprefix t)
          (Shao.Probability.Spitzer.tail a (n - t) (Nat.sub_le n t)) ∂P := by
      calc
        _ = ∫ u : Shao.Path m, lateAveragedWeight H ((n - t : ℕ) : ℝ) (Rprefix t) u ∂Pt m :=
          (congrArg (fun k : ℕ => ∫ u : Shao.Path k,
            lateAveragedWeight H ((n - t : ℕ) : ℝ) (Rprefix t) u ∂Pt k) hlen).symm
        _ = _ := by simpa only [Function.comp_def, id_eq] using he.symm
    refine ⟨hInt, ?_⟩
    calc
      _ = ∫ u : Shao.Path t, lateMarkedWeight H ((n - t : ℕ) : ℝ) (Rprefix t) u j ∂Pt t := by
        apply integral_congr_ae
        exact ae_of_all _ fun u => (hmark u).symm
      _ = ∫ u : Shao.Path t, lateAveragedWeight H ((n - t : ℕ) : ℝ) (Rprefix t) u ∂Pt t := hm.2.2
      _ = _ := he'
  have hLate5Sum :
      (∑ t ∈ Finset.Icc 1 (n / 2), ∫ u, abcf_suffixLate H beta n 5 u ∂Pt t) ≤ CL * delta := by
    calc
      _ = ∑ t ∈ Finset.Icc 1 (n / 2),
          ∫ a : Shao.Path n, lateAveragedWeight H ((n - t : ℕ) : ℝ) (Rprefix t)
            (Shao.Probability.Spitzer.tail a (n - t) (Nat.sub_le n t)) ∂P :=
        Finset.sum_congr rfl (fun t ht => (hLate5 t ht).2)
      _ ≤ _ := hLateData.2
  have hLateLe (k t : ℕ) (hk : k = 3 ∨ k = 5) (u : Shao.Path t) :
      abcf_suffixLate H beta n k u ≤ abcf_suffixLate H beta n 5 u := by
    have hU0 := Shao.energy_nonneg u
    have hD := (suffix_normalized_geometry u).2.2.2.2.2.1.1
    have hD0 : 0 ≤ suffixD u := le_trans (by norm_num) hD
    have hk5 : k ≤ 5 := by rcases hk with rfl | rfl <;> omega
    have hpow : suffixD u ^ k ≤ suffixD u ^ 5 := by gcongr
    unfold abcf_suffixLate
    split_ifs
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
    · exact le_rfl
  have hLateInt (k : ℕ) (hk : k = 3 ∨ k = 5) (t : ℕ) (ht : t ∈ Finset.Icc 1 (n / 2)) :
      Integrable (@abcf_suffixLate H beta n k t) (Pt t) :=
    (hLate5 t ht).1.mono' (hLateM k t).aestronglyMeasurable
      (ae_of_all _ fun u => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hLate0 k t u)] using hLateLe k t hk u)
  refine ⟨(fun t ht => ⟨hCubicM t, hEarlyInt t ht, hCubic0 t⟩), hEarlySum, ?_⟩
  intro k hk
  refine ⟨(fun t ht => ⟨hLateM k t, hLateInt k hk t ht, hLate0 k t⟩), ?_⟩
  calc
    _ ≤ ∑ t ∈ Finset.Icc 1 (n / 2), ∫ u, abcf_suffixLate H beta n 5 u ∂Pt t := by
      apply Finset.sum_le_sum
      intro t ht
      exact integral_mono (hLateInt k hk t ht) (hLate5 t ht).1 (hLateLe k t hk)
    _ ≤ _ := hLate5Sum

private theorem abcf_two_sign_gaussian_all_level_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (bound : ℝ), 0 < bound → (∀ᵐ z : ℝ ∂rho, |z| ≤ bound) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), (1 / 2 : ℝ) ≤ x →
          bound ≤ Real.sqrt (n : ℝ) / (100 * x) →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          let delta : ℝ := beta / Real.sqrt (n : ℝ)
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
          let G : Shao.Path n → ℝ := fun a => ∑ r : Fin n,
            (rankGaussianWeight (4 * beta ^ 2) x {1} false a r +
              rankGaussianWeight (4 * beta ^ 2) x {-1} false a r)
          Measurable G ∧ Integrable G P ∧ (∀ a, 0 ≤ G a) ∧
            (∫ a, G a ∂P) ≤ C * delta := by
  set_option maxHeartbeats 800000 in
    classical
    obtain ⟨CE, CL, hCE, hCL, hGrid⟩ := abcf_suffix_grid_payment
    obtain ⟨CS, hCS, hStrip⟩ :=
      Shao.C2.ActualBadIntervalNegativeBudget.actual_auxiliary_level_true_energy_closed_strip
    refine ⟨2 * CE + 16 * CS * CL, by positivity, ?_⟩
    intro rho hProb bound hb hsupport hmean hsecond n hn x hx hscale beta delta P G
    letI : IsProbabilityMeasure rho := hProb
    let Pt : (t : ℕ) → Measure (Shao.Path t) := fun t => Measure.pi (fun _ : Fin t => rho)
    let H : ℝ := 4 * beta ^ 2
    have hPaid := hGrid rho bound hb hsupport hmean hsecond n hn x hx hscale
    change
      (∀ t ∈ Finset.Icc (n / 2 + 1) n,
        Measurable (@abcf_suffixCubic H t) ∧ Integrable (@abcf_suffixCubic H t) (Pt t) ∧
          ∀ u, 0 ≤ abcf_suffixCubic H u) ∧
      (∑ t ∈ Finset.Icc (n / 2 + 1) n, ∫ u, abcf_suffixCubic H u ∂Pt t) ≤ CE * delta ∧
      ∀ k : ℕ, (k = 3 ∨ k = 5) →
        (∀ t ∈ Finset.Icc 1 (n / 2),
          Measurable (@abcf_suffixLate H beta n k t) ∧ Integrable (@abcf_suffixLate H beta n k t) (Pt t) ∧
            ∀ u, 0 ≤ abcf_suffixLate H beta n k u) ∧
        (∑ t ∈ Finset.Icc 1 (n / 2), ∫ u, abcf_suffixLate H beta n k u ∂Pt t) ≤ CL * delta at hPaid
    have hLatePaid := hPaid.2.2 5 (Or.inr rfl)
    have hH : 0 < H := by
      have hown := abcf_bounded_own_budget_identities rho bound hb hsupport hmean hsecond n hn x hx hscale
      exact hown.2.2.2.2.2.2.1
    have hCubic0 {t : ℕ} (u : Shao.Path t) : 0 ≤ abcf_suffixCubic H u := by
      have hU0 := Shao.energy_nonneg u
      have hD0 : 0 ≤ suffixD u := by unfold suffixD; split_ifs <;> positivity
      unfold abcf_suffixCubic
      split_ifs <;> positivity
    have hLate0 {t : ℕ} (u : Shao.Path t) : 0 ≤ abcf_suffixLate H beta n 5 u := by
      have hU0 := Shao.energy_nonneg u
      have hD0 : 0 ≤ suffixD u := by unfold suffixD; split_ifs <;> positivity
      unfold abcf_suffixLate
      split_ifs <;> positivity
    have hFixedI {r t : ℕ} (s : ℝ) (u : Shao.Path t) :
        Integrable (fun v : Shao.Path r => fixedGaussianWeight H x {s} false v u) (Pt r) := by
      have hd := fixed_gaussian_weight_measurable_bound r t H x {s} false
      exact (integrable_const ((1 + Real.sqrt (t : ℝ)) ^ 3)).mono'
        (hd.1.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        (ae_of_all _ fun v => by simpa using (hd.2.1 v u).2)
    have hFixedEarly {r t : ℕ} (s : ℝ) (v : Shao.Path r) (u : Shao.Path t) :
        fixedGaussianWeight H x {s} false v u ≤ abcf_suffixCubic H u := by
      have hD : 0 ≤ suffixD u := by
        unfold suffixD
        split_ifs <;> positivity
      by_cases hc : 0 < Shao.energy u ∧ H ≤ Shao.energy u
      · by_cases ha : prefixSurvival x {s} false v u
        · have hexp : Real.exp (-((max (x * Real.sqrt (Shao.energy u + Shao.energy v) -
                s * Shao.prefixSum v r - (|firstValue u| + max (s * Shao.prefixSum u t) 0)) 0) ^ 2) /
                Shao.energy u) ≤ 1 :=
            Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
              (neg_nonpos.mpr (sq_nonneg _)) hc.1.le)
          have hguard : 0 < Shao.energy u ∧ H ≤ Shao.energy u ∧ prefixSurvival x {s} false v u := ⟨hc.1, hc.2, ha⟩
          have hU0 := Shao.energy_nonneg u
          simpa only [fixedGaussianWeight, if_pos hguard, gaussianProfiles,
            if_pos hc.1, Finset.sum_singleton, abcf_suffixCubic, if_pos hc] using
            mul_le_of_le_one_right
              (show 0 ≤ |firstValue u| ^ 3 / (Shao.energy u * Real.sqrt (Shao.energy u)) * suffixD u ^ 3 by positivity)
              hexp
        · simp only [fixedGaussianWeight, if_neg (by tauto : ¬ (0 < Shao.energy u ∧ H ≤ Shao.energy u ∧
            prefixSurvival x {s} false v u))]
          exact hCubic0 u
      · simp only [fixedGaussianWeight, if_neg (by tauto : ¬ (0 < Shao.energy u ∧ H ≤ Shao.energy u ∧
          prefixSurvival x {s} false v u)), abcf_suffixCubic, if_neg hc, le_refl]
    have hFixedLate (r : Fin n) (hrlate : n ≤ 2 * r.val) (u : Shao.Path (n - r.val))
        (s : ℝ) (hsign : s = 1 ∨ s = -1) :
        (∫ v : Shao.Path r.val, fixedGaussianWeight H x {s} false v u ∂Pt r.val) ≤
          8 * CS * abcf_suffixLate H beta n 5 u := by
      have hr : 0 < r.val := by omega
      have hrR : 0 < (r.val : ℝ) := by exact_mod_cast hr
      have hsub : n - (n - r.val) = r.val := by omega
      let T : ℝ := Shao.energy u
      let d : ℝ := Shao.prefixSum u (n - r.val)
      let b : ℝ := firstValue u
      let D : ℝ := suffixD u
      by_cases hc : 0 < T ∧ H ≤ T
      · have hT : 0 < T := hc.1
        have hD1 : 1 ≤ D := (suffix_normalized_geometry u).2.2.2.2.2.1.1
        have hD0 : 0 ≤ D := le_trans (by norm_num) hD1
        have hD2 : 1 ≤ D ^ 2 := by nlinarith only [hD1, sq_nonneg (D - 1)]
        have ht : 0 < n - r.val := Nat.sub_pos_of_lt r.is_lt
        have hbT : b ^ 2 ≤ T := by
          simpa only [b, firstValue, dif_pos ht, T] using (suffix_normalized_geometry u).1 (⟨0, ht⟩ : Fin (n - r.val))
        have hab : |b| ≤ Real.sqrt T := by
          apply (sq_le_sq₀ (abs_nonneg b) (Real.sqrt_nonneg T)).mp
          simpa only [sq_abs, Real.sq_sqrt hT.le] using hbT
        let M : ℝ := |b| + max (s * d) 0
        have hM : 0 ≤ M := by dsimp [M]; positivity
        have hsd : s * d ≤ |d| := by
          rcases hsign with rfl | rfl
          · simpa only [one_mul] using le_abs_self d
          · simpa only [neg_one_mul] using neg_le_abs d
        have hMs : M ≤ Real.sqrt T * D := by
          have hMs0 : M ≤ Real.sqrt T + |d| :=
            add_le_add hab (max_le hsd (abs_nonneg d))
          have he : Real.sqrt T * D = Real.sqrt T + |d| := by
            dsimp only [D, suffixD]
            rw [if_pos hT]
            change Real.sqrt T * (1 + |d| / Real.sqrt T) = _
            field_simp [(Real.sqrt_pos.mpr hT).ne']
            <;> ring
          rw [he]
          exact hMs0
        have hMs2 : M ^ 2 ≤ T * D ^ 2 := by
          have hh := (sq_le_sq₀ hM (mul_nonneg (Real.sqrt_nonneg T) hD0)).mpr hMs
          simpa only [mul_pow, Real.sq_sqrt hT.le] using hh
        let wall : Shao.Path r.val → ℝ := fun v => x * Real.sqrt (T + Shao.energy v)
        let A : Set (Shao.Path r.val) := {v | prefixSurvival x {s} false v u}
        let w : Shao.Path r.val → ℝ := fun v => wall v - s * Shao.prefixSum v r.val
        have hwall : Measurable wall := measurable_const.mul ((measurable_const.add Shao.measurable_energy).sqrt)
        have hw : Measurable w := hwall.sub (measurable_const.mul (Shao.measurable_prefixSum r.val))
        have hAm : MeasurableSet A := by
          have he : A = {v | Shao.maxWithZero (s • v) < wall v} := by
            ext v
            simp only [A, prefixSurvival, Finset.mem_singleton, forall_eq, Bool.false_eq_true,
              ↓reduceIte, wall, T, Set.mem_setOf_eq]
          rw [he]
          exact measurableSet_lt
            (Shao.measurable_maxWithZero.comp (Measurable.of_eval fun i => measurable_const.mul (measurable_pi_apply i))) hwall
        have hR2 : (beta / Real.sqrt (r.val : ℝ)) ^ 2 = beta ^ 2 / (r.val : ℝ) := by
          rw [div_pow, Real.sq_sqrt hrR.le]
        have hCDF (v : ℝ) (hv : 0 ≤ v) :
            (Pt r.val).real {a | a ∈ A ∧ w a ≤ v} ≤
              (2 * CS) * (v ^ 2 / (r.val : ℝ) + (beta / Real.sqrt (r.val : ℝ)) ^ 2) := by
          have hraw := hStrip rho bound hb hsupport hmean hsecond n hn x hx hscale
            r.val hr r.is_lt.le hrlate T v s hT.le hv hsign
          have hsubset : {a | a ∈ A ∧ w a ≤ v} ⊆
              {a : Shao.Path r.val | Shao.maxWithZero (s • a) ≤ wall a ∧
                wall a - v ≤ s * Shao.prefixSum a r.val ∧ s * Shao.prefixSum a r.val ≤ wall a} := by
            intro a ha
            have hamax : Shao.maxWithZero (s • a) < wall a := by
              simpa only [A, Set.mem_setOf_eq, prefixSurvival, Finset.mem_singleton, forall_eq,
                Bool.false_eq_true, ↓reduceIte, wall, T] using ha.1
            have hsum := (Shao.maxWithZero_le_iff (s • a) (wall a)).mp hamax.le r.val le_rfl
            rw [Shao.prefixSum_smul] at hsum
            refine ⟨hamax.le, ?_, hsum⟩
            have hwv : wall a - s * Shao.prefixSum a r.val ≤ v := ha.2
            linarith only [hwv]
          calc
            _ ≤ (Pt r.val).real {a : Shao.Path r.val | Shao.maxWithZero (s • a) ≤ wall a ∧
                wall a - v ≤ s * Shao.prefixSum a r.val ∧ s * Shao.prefixSum a r.val ≤ wall a} :=
              measureReal_mono hsubset
            _ ≤ CS * (v + beta) ^ 2 / (r.val : ℝ) := hraw
            _ ≤ CS * (2 * v ^ 2 + 2 * beta ^ 2) / (r.val : ℝ) := by
              gcongr
              nlinarith only [sq_nonneg (v - beta)]
            _ = _ := by rw [hR2]; ring
        have hProfile := Shao.Probability.gaussian_wall_profile_of_quadratic_closed_cdf
          (Pt r.val) A hAm w hw (2 * CS) (beta / Real.sqrt (r.val : ℝ)) (r.val : ℝ) T M
          (by positivity) hrR hT hM hCDF
        have hProfileI := (Shao.Probability.gaussian_wall_profile_layer_cake
          (Pt r.val) A hAm w hw T M hT hM).1
        have hProfileBound : (∫ v, A.indicator (fun v =>
            Real.exp (-((max (w v - M) 0) ^ 2) / T)) v ∂Pt r.val) ≤
            8 * CS * D ^ 2 * (T / (r.val : ℝ) + beta ^ 2 / (r.val : ℝ)) := by
          apply hProfile.trans
          rw [hR2]
          have hMT : M ^ 2 + T ≤ 2 * T * D ^ 2 := by
            nlinarith only [hMs2, mul_nonneg hT.le (sub_nonneg.mpr hD2)]
          have hmain : 2 * (M ^ 2 + T) / (r.val : ℝ) ≤ 4 * D ^ 2 * (T / (r.val : ℝ)) := by
            calc
              _ ≤ 2 * (2 * T * D ^ 2) / (r.val : ℝ) := by gcongr
              _ = _ := by ring
          have hbetaPay : beta ^ 2 / (r.val : ℝ) ≤ D ^ 2 * (beta ^ 2 / (r.val : ℝ)) :=
            le_mul_of_one_le_left (by positivity) hD2
          have hpay0 : 0 ≤ D ^ 2 * (beta ^ 2 / (r.val : ℝ)) := by positivity
          nlinarith only [mul_le_mul_of_nonneg_left
            (show 2 * (M ^ 2 + T) / (r.val : ℝ) + beta ^ 2 / (r.val : ℝ) ≤
              4 * D ^ 2 * (T / (r.val : ℝ) + beta ^ 2 / (r.val : ℝ)) by
                nlinarith only [hmain, hbetaPay, hpay0]) (show 0 ≤ 2 * CS by positivity)]
        let c : ℝ := |b| ^ 3 / (T * Real.sqrt T) * D ^ 3
        have hc0 : 0 ≤ c := by dsimp [c]; positivity
        have hFun : (fun v : Shao.Path r.val => fixedGaussianWeight H x {s} false v u) =
            (fun v => c * A.indicator (fun v => Real.exp (-((max (w v - M) 0) ^ 2) / T)) v) := by
          funext v
          by_cases ha : v ∈ A
          · have ha' : prefixSurvival x {s} false v u := ha
            have hguard : 0 < Shao.energy u ∧ H ≤ Shao.energy u ∧ prefixSurvival x {s} false v u :=
              ⟨hc.1, hc.2, ha'⟩
            have henergy : 0 < Shao.energy u := hc.1
            simp only [fixedGaussianWeight, if_pos hguard, gaussianProfiles,
              if_pos henergy, Finset.sum_singleton, Set.indicator_of_mem ha, c, b, d, D, w, wall, M, T]
          · have ha' : ¬ prefixSurvival x {s} false v u := ha
            simp only [fixedGaussianWeight, if_neg (by tauto : ¬ (0 < Shao.energy u ∧ H ≤ Shao.energy u ∧
              prefixSurvival x {s} false v u)), Set.indicator_of_notMem ha, mul_zero]
        rw [hFun, integral_const_mul]
        calc
          _ ≤ c * (8 * CS * D ^ 2 * (T / (r.val : ℝ) + beta ^ 2 / (r.val : ℝ))) :=
            mul_le_mul_of_nonneg_left hProfileBound hc0
          _ = 8 * CS * abcf_suffixLate H beta n 5 u := by
            have hcU : 0 < Shao.energy u ∧ H ≤ Shao.energy u := hc
            simp only [abcf_suffixLate, if_pos hcU, hsub]
            dsimp only [c, b, T, D]
            ring
      · have hfzero : (fun v : Shao.Path r.val => fixedGaussianWeight H x {s} false v u) = 0 := by
          funext v
          simp only [fixedGaussianWeight, if_neg (by tauto : ¬ (0 < Shao.energy u ∧ H ≤ Shao.energy u ∧
            prefixSurvival x {s} false v u)), Pi.zero_apply]
        rw [hfzero]
        change (∫ _ : Shao.Path r.val, (0 : ℝ) ∂Pt r.val) ≤ _
        simpa only [integral_const, smul_zero] using
          mul_nonneg (by positivity : (0 : ℝ) ≤ 8 * CS) (hLate0 u)
    have hRankM (r : Fin n) (s : ℝ) : Measurable (fun a : Shao.Path n => rankGaussianWeight H x {s} false a r) := by
      have hm := (fixed_gaussian_weight_measurable_bound r.val (n - r.val) H x {s} false).1
      change Measurable (fun a : Shao.Path n => fixedGaussianWeight H x {s} false
        (Shao.Probability.Spitzer.head a r.val r.is_lt.le) (Shao.Probability.Spitzer.tail a r.val r.is_lt.le))
      exact hm.comp ((show Measurable (fun a : Shao.Path n => Shao.Probability.Spitzer.head a r.val r.is_lt.le) from
        Measurable.of_eval fun i => measurable_pi_apply (⟨i.val, lt_of_lt_of_le i.is_lt r.is_lt.le⟩ : Fin n)).prodMk
        (show Measurable (fun a : Shao.Path n => Shao.Probability.Spitzer.tail a r.val r.is_lt.le) from
          Measurable.of_eval fun i => measurable_pi_apply (⟨r.val + i.val, by omega⟩ : Fin n)))
    have hRankI (r : Fin n) (s : ℝ) : Integrable (fun a : Shao.Path n => rankGaussianWeight H x {s} false a r) P :=
      (iid_rank_gaussian_weight_fubini rho r H x {s} false).1
    have hRank0 (r : Fin n) (s : ℝ) (a : Shao.Path n) : 0 ≤ rankGaussianWeight H x {s} false a r :=
      ((fixed_gaussian_weight_measurable_bound r.val (n - r.val) H x {s} false).2.1 _ _).1
    let E : ℕ → ℝ := fun t => ∫ u, abcf_suffixCubic H u ∂Pt t
    let L : ℕ → ℝ := fun t => ∫ u, abcf_suffixLate H beta n 5 u ∂Pt t
    have hRankBound (r : Fin n) :
        (∫ a, rankGaussianWeight H x {1} false a r + rankGaussianWeight H x {-1} false a r ∂P) ≤
          if 2 * r.val < n then 2 * E (n - r.val) else 16 * CS * L (n - r.val) := by
      have hf1 := iid_rank_gaussian_weight_fubini rho r H x {1} false
      have hfm := iid_rank_gaussian_weight_fubini rho r H x {-1} false
      rw [integral_add (hRankI r 1) (hRankI r (-1)), hf1.2.2, hfm.2.2,
        ← integral_add hf1.2.1 hfm.2.1]
      by_cases he : 2 * r.val < n
      · rw [if_pos he]
        have ht : n - r.val ∈ Finset.Icc (n / 2 + 1) n := by apply Finset.mem_Icc.mpr; omega
        have hp (u : Shao.Path (n - r.val)) :
            (∫ v : Shao.Path r.val, fixedGaussianWeight H x {1} false v u ∂Pt r.val) +
              (∫ v : Shao.Path r.val, fixedGaussianWeight H x {-1} false v u ∂Pt r.val) ≤
                2 * abcf_suffixCubic H u := by
          have hbound (s : ℝ) := integral_mono (hFixedI s u)
            (integrable_const (abcf_suffixCubic H u) (μ := Pt r.val)) (fun v => hFixedEarly s v u)
          simpa only [integral_const, probReal_univ, one_smul, ← two_mul] using add_le_add (hbound 1) (hbound (-1))
        have hi := integral_mono (hf1.2.1.add hfm.2.1) ((hPaid.1 _ ht).2.1.const_mul 2) hp
        simpa only [Pi.add_apply, integral_const_mul, E, Pt] using hi
      · rw [if_neg he]
        have hl : n ≤ 2 * r.val := by omega
        have ht : n - r.val ∈ Finset.Icc 1 (n / 2) := by apply Finset.mem_Icc.mpr; omega
        have hp (u : Shao.Path (n - r.val)) := add_le_add
          (hFixedLate r hl u 1 (Or.inl rfl)) (hFixedLate r hl u (-1) (Or.inr rfl))
        have hi := integral_mono (hf1.2.1.add hfm.2.1)
          ((hLatePaid.1 _ ht).2.1.const_mul (16 * CS)) (fun u => by
            have hh := hp u
            simp only [Pi.add_apply, Pt] at hh ⊢
            nlinarith only [hh])
        simpa only [Pi.add_apply, integral_const_mul, L, Pt] using hi
    have hReindex (f : ℕ → ℝ) : (∑ r : Fin n, f (n - r.val)) = ∑ t ∈ Finset.Icc 1 n, f t := by
      apply Finset.sum_bij (fun r _ => n - r.val)
      · intro r _
        exact Finset.mem_Icc.mpr ⟨by omega, Nat.sub_le n r.val⟩
      · intro r _ q _ he
        apply Fin.ext
        omega
      · intro t ht
        have ht' := Finset.mem_Icc.mp ht
        refine ⟨⟨n - t, by omega⟩, Finset.mem_univ _, ?_⟩
        dsimp
        omega
      · intro r _
        rfl
    have hCost :
        (∑ r : Fin n, if 2 * r.val < n then 2 * E (n - r.val) else 16 * CS * L (n - r.val)) ≤
          2 * (CE * delta) + 16 * CS * (CL * delta) := by
      have hEq : (∑ r : Fin n, if 2 * r.val < n then 2 * E (n - r.val) else 16 * CS * L (n - r.val)) =
          ∑ t ∈ Finset.Icc 1 n, if n / 2 < t then 2 * E t else 16 * CS * L t := by
        rw [← hReindex]
        apply Finset.sum_congr rfl
        intro r _
        have he : 2 * r.val < n ↔ n / 2 < n - r.val := by omega
        simp only [he]
      rw [hEq, Finset.sum_ite]
      have hEarlySet : (Finset.Icc 1 n).filter (fun t => n / 2 < t) = Finset.Icc (n / 2 + 1) n := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      have hLateSet : (Finset.Icc 1 n).filter (fun t => ¬ n / 2 < t) = Finset.Icc 1 (n / 2) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      rw [hEarlySet, hLateSet, ← Finset.mul_sum, ← Finset.mul_sum]
      exact add_le_add (mul_le_mul_of_nonneg_left hPaid.2.1 (by norm_num))
        (mul_le_mul_of_nonneg_left hLatePaid.2 (by positivity))
    refine ⟨Finset.measurable_sum _ (fun r _ => (hRankM r 1).add (hRankM r (-1))),
      integrable_finsetSum _ (fun r _ => (hRankI r 1).add (hRankI r (-1))),
      (fun a => Finset.sum_nonneg fun r _ => add_nonneg (hRank0 r 1 a) (hRank0 r (-1) a)), ?_⟩
    change (∫ a, ∑ r : Fin n, (rankGaussianWeight H x {1} false a r +
      rankGaussianWeight H x {-1} false a r) ∂P) ≤ _
    have hSum : (∫ a, ∑ r : Fin n, (rankGaussianWeight H x {1} false a r +
        rankGaussianWeight H x {-1} false a r) ∂P) =
        ∑ r : Fin n, ∫ a, rankGaussianWeight H x {1} false a r +
          rankGaussianWeight H x {-1} false a r ∂P := by
      simpa only [Pi.add_apply] using
        (integral_finsetSum Finset.univ (fun (r : Fin n) _ => (hRankI r 1).add (hRankI r (-1))))
    rw [hSum]
    calc
      _ ≤ ∑ r : Fin n, if 2 * r.val < n then 2 * E (n - r.val) else 16 * CS * L (n - r.val) :=
        Finset.sum_le_sum (fun r _ => hRankBound r)
      _ ≤ 2 * (CE * delta) + 16 * CS * (CL * delta) := hCost
      _ = _ := by ring

theorem iid_actual_all_level_retained_negative_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (bound : ℝ), 0 < bound → (∀ᵐ z : ℝ ∂rho, |z| ≤ bound) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), (1 / 2 : ℝ) ≤ x →
          bound ≤ Real.sqrt (n : ℝ) / (100 * x) →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          let delta : ℝ := beta / Real.sqrt (n : ℝ)
          ∀ {ΩB : Type*} [MeasurableSpace ΩB]
            (Bm : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
            IsBrownianReal Bm PB →
            let Q : Measure BridgeNoise := bridgeLaw Bm PB
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
            ∀ (nu : Shao.Path n → LabelPerm n → ℕ),
              (∀ sigma, Measurable (fun a : Shao.Path n => nu a sigma)) →
              (∀ a sigma, nu a sigma ≤ energyCutoff a (4 * beta ^ 2) sigma) →
              let bill : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
                ∑ r : Fin n, actualRetainedAbsoluteRank Q p.1 x (nu p.1) r p.2
              let absoluteDouble : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
                ∑ r : Fin n, |actualDoubleRetained Q x p.1 (nu p.1) r.val p.2|
              let signedDouble : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
                ∑ r : Fin n, actualDoubleRetained Q x p.1 (nu p.1) r.val p.2
              Measurable bill ∧ Integrable bill (revealLaw P) ∧ (∀ p, 0 ≤ bill p) ∧
                0 ≤ (∫ p, bill p ∂revealLaw P) ∧ (∫ p, bill p ∂revealLaw P) ≤ C * delta ∧
                Measurable absoluteDouble ∧ Integrable absoluteDouble (revealLaw P) ∧
                (∀ p, absoluteDouble p ≤ bill p) ∧
                (∫ p, absoluteDouble p ∂revealLaw P) ≤ C * delta ∧
                Measurable signedDouble ∧ Integrable signedDouble (revealLaw P) ∧
                |(∫ p, signedDouble p ∂revealLaw P)| ≤ C * delta := by
  classical
  obtain ⟨CG, hCG, hGaussian⟩ := abcf_two_sign_gaussian_all_level_budget
  let K : ℝ := 8000100 + (2 * Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant + 40)
  have hK : 0 < K := by
    have hc := Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant_nonneg
    dsimp only [K]
    linarith only [hc]
  refine ⟨K * CG, mul_pos hK hCG, ?_⟩
  intro rho hProb bound hb hsupport hmean hsecond n hn x hx hscale beta delta
    ΩB hΩB Bm PB hPB hBm Q P nu hnum hcap bill absoluteDouble signedDouble
  letI : IsProbabilityMeasure rho := hProb
  letI : IsProbabilityMeasure PB := hPB
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw Bm PB hBm
  letI : IsProbabilityMeasure (revealLaw P) := by unfold revealLaw; infer_instance
  have hx0 : 0 < x := by linarith only [hx]
  have hown := abcf_bounded_own_budget_identities rho bound hb hsupport hmean hsecond n hn x hx hscale
  let H : ℝ := 4 * beta ^ 2
  have hH : 0 < H := hown.2.2.2.2.2.2.1
  let G : Shao.Path n → ℝ := fun a => ∑ r : Fin n,
    (rankGaussianWeight H x {1} false a r + rankGaussianWeight H x {-1} false a r)
  have hG := hGaussian rho bound hb hsupport hmean hsecond n hn x hx hscale
  change Measurable G ∧ Integrable G P ∧ (∀ a, 0 ≤ G a) ∧ (∫ a, G a ∂P) ≤ CG * delta at hG
  have hRfl : Shao.Probability.SourceActualLocalProfileBudget.HalflineReflectionIdentities Q := by
    constructor
    · intro w y T z _ hT hy hz
      exact Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula Bm PB hBm w y T z hT hy hz
    · intro w y T z _ hT hy hz
      exact Shao.C2.BridgeLowerIdentification.bridge_lower_formula Bm PB hBm w y T z hT hy hz
  have hReg : ∀ w y T z : ℝ, 0 < w → 0 < T → |y| < w → |z| < w →
      DifferentiableAt ℝ (fun a => Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w a T z) y := by
    intro w y T z hw hT hy hz
    exact Shao.C2.ActualBridgeIntervalTelescope.actual_source_interval_differentiable
      Bm PB hBm w y T z hw hy hz hT
  have hKernel (J : MonitoredDomain) :
      Measurable (actualDerivativeFamily Q J) ∧
        KernelBounds J (eventCompletionKernel J Q) (actualDerivativeFamily Q J) 4 := by
    rcases J with _ | _ | _
    · have hd := Shao.Probability.SourceActualLocalProfileBudget.actual_halfline_kernel_data Q hRfl
        .upper (Or.inl rfl)
      exact ⟨hd.1, hd.2.1⟩
    · have hd := Shao.Probability.SourceActualLocalProfileBudget.actual_halfline_kernel_data Q hRfl
        .lower (Or.inr rfl)
      exact ⟨hd.1, hd.2.1⟩
    · have hd := Shao.Probability.SourceActualIntervalProfileBudget.actual_interval_kernel_data Q hRfl hReg
      exact ⟨hd.1, hd.2.1⟩
  let L : MonitoredDomain → ℕ → (Shao.Path n × LabelPerm n) → ℝ := fun J r p =>
    sourceRetainedRemainder J (eventCompletionKernel J Q) (actualDerivativeFamily Q J)
      p.1 x (nu p.1) r p.2
  let O : ℕ → (Shao.Path n × LabelPerm n) → ℝ := fun r p =>
    sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval) p.1 x (nu p.1) r p.2
  have hParts (J : MonitoredDomain) := source_parts_measurable_integrable J
    (eventCompletionKernel J Q) (actualDerivativeFamily Q J)
    (eventCompletionKernel_data J Q).1 (hKernel J).1 4 (hKernel J).2 P x hx0 nu hnum
  have hLm (J : MonitoredDomain) (r : ℕ) : Measurable (L J r) :=
    measurable_from_prod_countable_left (fun sigma => ((hParts J).1 sigma r).1)
  have hOm (r : ℕ) : Measurable (O r) :=
    measurable_from_prod_countable_left (fun sigma => ((hParts .interval).1 sigma r).2)
  have hbillM : Measurable bill := by
    apply Finset.measurable_sum
    intro r _
    exact ((((continuous_abs.measurable.comp (hLm .interval r.val)).add
      (continuous_abs.measurable.comp (hLm .upper r.val))).add
      (continuous_abs.measurable.comp (hLm .lower r.val))).add ((hOm r.val).neg.max measurable_const))
  have hbill0 (p : Shao.Path n × LabelPerm n) : 0 ≤ bill p := by
    dsimp only [bill]
    apply Finset.sum_nonneg
    intro r _
    unfold actualRetainedAbsoluteRank
    positivity
  have hReorderM : Measurable (randomReorder : Shao.Path n × LabelPerm n → Shao.Path n) :=
    measurable_from_prod_countable_left (fun sigma =>
      Measurable.of_eval (fun i => measurable_pi_apply (sigma i)))
  have hReorderMap : Measure.map (randomReorder : Shao.Path n × LabelPerm n → Shao.Path n)
      (revealLaw P) = P := by
    let X : Fin n → Shao.Path n → ℝ := fun i a => a i
    have hX (i : Fin n) : Measurable (X i) := measurable_pi_apply i
    have hLaw (i : Fin n) : IdentDistrib (X i) (id : ℝ → ℝ) P rho := by
      exact ⟨(hX i).aemeasurable, measurable_id.aemeasurable, by
        simpa only [Measure.map_id] using (measurePreserving_eval (μ := fun _ : Fin n => rho) i).map_eq⟩
    have hInd : iIndepFun X P := iIndepFun_pi (fun _ => measurable_id.aemeasurable)
    have hh := iid_randomPermutation_map_eq_pi P rho X hX hInd hLaw
    have hfun : (fun p : Shao.Path n × LabelPerm n =>
        Shao.Probability.Spitzer.reorder (Shao.Probability.samplePath X p.1) p.2) = randomReorder := by
      funext p i
      rfl
    change Measure.map (fun p => Shao.Probability.Spitzer.reorder (Shao.Probability.samplePath X p.1) p.2) (revealLaw P) = P at hh
    rw [hfun] at hh
    exact hh
  have hMP : MeasurePreserving (randomReorder : Shao.Path n × LabelPerm n → Shao.Path n)
      (revealLaw P) P := ⟨hReorderM, hReorderMap⟩
  have hGRevealI : Integrable (fun p => G (randomReorder p)) (revealLaw P) :=
    hMP.integrable_comp_of_integrable hG.2.1
  have hbillDom (p : Shao.Path n × LabelPerm n) : bill p ≤ K * G (randomReorder p) := by
    calc
      _ ≤ ∑ r : Fin n, K * (rankGaussianWeight H x {1} false (randomReorder p) r +
          rankGaussianWeight H x {-1} false (randomReorder p) r) := by
        apply Finset.sum_le_sum
        intro r _
        exact (actual_retained_absolute_rank_gaussian_domination PB Bm hBm p.1 H x hH hx0
          (nu p.1) p.2 (hcap p.1 p.2) r).2
      _ = _ := by rw [Finset.mul_sum]
  have hbillI : Integrable bill (revealLaw P) :=
    (hGRevealI.const_mul K).mono' hbillM.aestronglyMeasurable
      (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hbill0 p)] using hbillDom p)
  have hGreveal : (∫ p, G (randomReorder p) ∂revealLaw P) = ∫ a, G a ∂P := by
    have he := integral_map (μ := revealLaw P) (φ := randomReorder) hReorderM.aemeasurable hG.1.aestronglyMeasurable
    rw [hReorderMap] at he
    exact he.symm
  have hbillBound : (∫ p, bill p ∂revealLaw P) ≤ (K * CG) * delta := by
    calc
      _ ≤ ∫ p, K * G (randomReorder p) ∂revealLaw P := integral_mono hbillI (hGRevealI.const_mul K) hbillDom
      _ = K * (∫ a, G a ∂P) := by rw [integral_const_mul, hGreveal]
      _ ≤ K * (CG * delta) := mul_le_mul_of_nonneg_left hG.2.2.2 hK.le
      _ = _ := by ring
  have hSignedM : Measurable signedDouble := by
    apply Finset.measurable_sum
    intro r _
    exact ((hLm .interval r.val).sub (hLm .upper r.val)).sub (hLm .lower r.val)
  have hAbsM : Measurable absoluteDouble := by
    apply Finset.measurable_sum
    intro r _
    exact continuous_abs.measurable.comp (((hLm .interval r.val).sub (hLm .upper r.val)).sub (hLm .lower r.val))
  have hAbs0 (p : Shao.Path n × LabelPerm n) : 0 ≤ absoluteDouble p :=
    Finset.sum_nonneg (fun r _ => abs_nonneg _)
  have hAbsDom (p : Shao.Path n × LabelPerm n) : absoluteDouble p ≤ bill p := by
    apply Finset.sum_le_sum
    intro r _
    let LR : MonitoredDomain → ℝ := fun J => sourceRetainedRemainder J (eventCompletionKernel J Q)
      (actualDerivativeFamily Q J) p.1 x (nu p.1) r.val p.2
    let OR : ℝ := sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
      p.1 x (nu p.1) r.val p.2
    change |(LR .interval - LR .upper) - LR .lower| ≤
      |LR .interval| + |LR .upper| + |LR .lower| + max (-OR) 0
    calc
      |(LR .interval - LR .upper) - LR .lower| ≤ |LR .interval - LR .upper| + |LR .lower| :=
        abs_sub _ _
      _ ≤ (|LR .interval| + |LR .upper|) + |LR .lower| :=
        add_le_add (abs_sub (LR .interval) (LR .upper)) le_rfl
      _ ≤ (|LR .interval| + |LR .upper|) + |LR .lower| + max (-OR) 0 :=
        le_add_of_nonneg_right (le_max_right _ _)
  have hAbsI : Integrable absoluteDouble (revealLaw P) :=
    hbillI.mono' hAbsM.aestronglyMeasurable
      (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hAbs0 p)] using hAbsDom p)
  have hSignedDom (p : Shao.Path n × LabelPerm n) : |signedDouble p| ≤ absoluteDouble p :=
    Finset.abs_sum_le_sum_abs _ _
  have hSignedI : Integrable signedDouble (revealLaw P) :=
    hAbsI.mono' hSignedM.aestronglyMeasurable
      (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hSignedDom p)
  have hAbsBound : (∫ p, absoluteDouble p ∂revealLaw P) ≤ (K * CG) * delta :=
    (integral_mono hAbsI hbillI hAbsDom).trans hbillBound
  refine ⟨hbillM, hbillI, hbill0, integral_nonneg hbill0, hbillBound,
    hAbsM, hAbsI, hAbsDom, hAbsBound, hSignedM, hSignedI, ?_⟩
  calc
    _ ≤ ∫ p, |signedDouble p| ∂revealLaw P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm signedDouble
    _ ≤ ∫ p, absoluteDouble p ∂revealLaw P := integral_mono hSignedI.abs hAbsI hSignedDom
    _ ≤ _ := hAbsBound

private theorem abcf_future_measurable_integrable
    {ΩB : Type*} [MeasurableSpace ΩB]
    (Bm : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hBm : IsBrownianReal Bm PB) (n : ℕ)
    (P : Measure (Shao.Path n)) [IsProbabilityMeasure P]
    (H x : ℝ) (hH : 0 < H) (hx : 0 ≤ x) :
    let Q : Measure BridgeNoise := bridgeLaw Bm PB
    (∀ (J : MonitoredDomain) (r : ℕ), r ≤ n →
      Measurable (abcf_futureAt (n := n) J Q x r) ∧
      Integrable (abcf_futureAt J Q x r) (revealLaw P) ∧
      ∀ p : Shao.Path n × LabelPerm n, 0 ≤ abcf_futureAt J Q x r p ∧ abcf_futureAt J Q x r p ≤ 1) ∧
    ∀ J : MonitoredDomain,
      Measurable (abcf_h0Future (n := n) J Q H x) ∧ Integrable (abcf_h0Future J Q H x) (revealLaw P) ∧
      Measurable (fun a => abcf_h0Future J Q H x (a, Equiv.refl (Fin n))) ∧
      Integrable (fun a => abcf_h0Future J Q H x (a, Equiv.refl (Fin n))) P ∧
      ∀ p : Shao.Path n × LabelPerm n, 0 ≤ abcf_h0Future J Q H x p ∧ abcf_h0Future J Q H x p ≤ 1 := by
  classical
  intro Q
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw Bm PB hBm
  letI : IsProbabilityMeasure (revealLaw P) := by unfold revealLaw; infer_instance
  have hInterior (J : MonitoredDomain) (W Y : Shao.Path n → ℝ)
      (hW : Measurable W) (hY : Measurable Y) :
      MeasurableSet {a | Interior J (W a) (Y a)} := by
    rcases J with _ | _ | _
    · exact measurableSet_lt hY hW
    · exact measurableSet_lt hW.neg hY
    · exact (measurableSet_lt hW.neg hY).inter (measurableSet_lt hY hW)
  have hWallM : Measurable (fun a : Shao.Path n => actualWall a x) :=
    measurable_const.mul Shao.measurable_energy.sqrt
  have hReorderM (sigma : LabelPerm n) :
      Measurable (fun a : Shao.Path n => Shao.Probability.Spitzer.reorder a sigma) :=
    Measurable.of_eval (fun i => measurable_pi_apply (sigma i))
  have hAliveM (J : MonitoredDomain) (j : ℕ) (sigma : LabelPerm n) :
      MeasurableSet {a : Shao.Path n | sourceAlive J a x j sigma} := by
    let V : Fin (j + 1) → Set (Shao.Path n) := fun k =>
      {a | Interior J (actualWall a x)
        (Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) k.val)}
    have hV (k : Fin (j + 1)) : MeasurableSet (V k) :=
      hInterior J _ _ hWallM ((Shao.measurable_prefixSum k.val).comp (hReorderM sigma))
    have hpre : MeasurableSet {a : Shao.Path n | ∀ k : Fin (j + 1), a ∈ V k} := by
      convert MeasurableSet.iInter hV using 1
      ext a
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
    have heq : {a : Shao.Path n | sourceAlive J a x j sigma} =
        {a : Shao.Path n | 0 < Shao.energy a} ∩
          ({a : Shao.Path n | Interior J (actualWall a x) (Shao.prefixSum a n)} ∩
            {a : Shao.Path n | ∀ k : Fin (j + 1), a ∈ V k}) := by
      ext a
      constructor
      · intro ha
        exact ⟨ha.1, ha.2.1, fun k => ha.2.2 k.val (by omega)⟩
      · rintro ⟨hpos, hend, hpre⟩
        refine ⟨hpos, hend, ?_⟩
        intro k hk
        exact hpre ⟨k, by omega⟩
    rw [heq]
    exact (measurableSet_lt measurable_const Shao.measurable_energy).inter
      ((hInterior J _ _ hWallM (Shao.measurable_prefixSum n)).inter hpre)
  have hSourceM (J : MonitoredDomain) (j : ℕ) (sigma : LabelPerm n) :
      Measurable (fun a : Shao.Path n => sourceValue J (eventCompletionKernel J Q) a x j sigma) := by
    let Y : Shao.Path n → ℝ := fun a => Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) j
    let T : Shao.Path n → ℝ := fun a => remainingEnergy a j sigma
    let Z : Shao.Path n → ℝ := fun a => Shao.prefixSum a n
    have hY : Measurable Y := (Shao.measurable_prefixSum j).comp (hReorderM sigma)
    have hT : Measurable T := Shao.measurable_energy.sub ((Shao.measurable_prefixSquares j).comp (hReorderM sigma))
    have hZ : Measurable Z := Shao.measurable_prefixSum n
    have hGate : MeasurableSet {a : Shao.Path n |
        0 < actualWall a x ∧ Interior J (actualWall a x) (Y a) ∧ Interior J (actualWall a x) (Z a)} :=
      (measurableSet_lt measurable_const hWallM).inter
        ((hInterior J _ _ hWallM hY).inter (hInterior J _ _ hWallM hZ))
    have hReach : MeasurableSet {a : Shao.Path n | T a = 0 ∧ Y a = Z a} :=
      (measurableSet_eq_fun hT measurable_const).inter (measurableSet_eq_fun hY hZ)
    have hExt : Measurable (fun a : Shao.Path n => completionExt J (eventCompletionKernel J Q)
        (actualWall a x) (Y a) (T a) (Z a)) := by
      apply Measurable.ite hGate
      · apply Measurable.ite (measurableSet_lt measurable_const hT)
        · exact (eventCompletionKernel_data J Q).1.comp (hWallM.prodMk (hY.prodMk (hT.prodMk hZ)))
        · exact Measurable.ite hReach measurable_const measurable_const
      · exact measurable_const
    exact Measurable.ite (hAliveM J j sigma) hExt measurable_const
  have hTerminalM (J : MonitoredDomain) (sigma : LabelPerm n) :
      Measurable (fun a : Shao.Path n => if sourceAlive J a x n sigma then (1 : ℝ) else 0) :=
    Measurable.ite (hAliveM J n sigma) measurable_const measurable_const
  have hValueRange (J : MonitoredDomain) (j : ℕ) (p : Shao.Path n × LabelPerm n) :
      0 ≤ sourceValue J (eventCompletionKernel J Q) p.1 x j p.2 ∧
        sourceValue J (eventCompletionKernel J Q) p.1 x j p.2 ≤ 1 := by
    unfold sourceValue completionExt
    split_ifs <;> try norm_num
    exact (eventCompletionKernel_data J Q).2.1 _
  have hSlot (J : MonitoredDomain) (r j : ℕ) (p : Shao.Path n × LabelPerm n) :
      0 ≤ (if r ≤ j then |sourceValue J (eventCompletionKernel J Q) p.1 x j p.2 -
          (if sourceAlive J p.1 x n p.2 then 1 else 0)| else 0) ∧
      (if r ≤ j then |sourceValue J (eventCompletionKernel J Q) p.1 x j p.2 -
          (if sourceAlive J p.1 x n p.2 then 1 else 0)| else 0) ≤ 1 := by
    by_cases hr : r ≤ j
    · rw [if_pos hr]
      have hv := hValueRange J j p
      have ht : 0 ≤ (if sourceAlive J p.1 x n p.2 then (1 : ℝ) else 0) ∧
          (if sourceAlive J p.1 x n p.2 then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
      exact ⟨abs_nonneg _, abs_le.mpr ⟨by linarith only [hv.1, ht.2], by linarith only [hv.2, ht.1]⟩⟩
    · simp only [if_neg hr, le_refl, zero_le_one, and_self]
  have hFutureRange (J : MonitoredDomain) (r : ℕ) (p : Shao.Path n × LabelPerm n) :
      0 ≤ abcf_futureAt J Q x r p ∧ abcf_futureAt J Q x r p ≤ 1 := by
    let seed : (Finset.range (n + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩
    change 0 ≤ (Finset.range (n + 1)).sup' seed _ ∧ (Finset.range (n + 1)).sup' seed _ ≤ 1
    constructor
    · exact (hSlot J r 0 p).1.trans
        (Finset.le_sup' (fun j => if r ≤ j then
          |sourceValue J (eventCompletionKernel J Q) p.1 x j p.2 -
            (if sourceAlive J p.1 x n p.2 then 1 else 0)| else 0)
          (Finset.mem_range.mpr (Nat.zero_lt_succ n)))
    · apply Finset.sup'_le
      intro j _
      exact (hSlot J r j p).2
  have hFutureM (J : MonitoredDomain) (tau : Shao.Path n × LabelPerm n → ℕ)
      (htau : ∀ sigma : LabelPerm n, Measurable (fun a : Shao.Path n => tau (a, sigma))) :
      Measurable (fun p : Shao.Path n × LabelPerm n => abcf_futureAt J Q x (tau p) p) := by
    apply measurable_from_prod_countable_left
    intro sigma
    have hslot (j : ℕ) (_hj : j ∈ Finset.range (n + 1)) :
        Measurable (fun a : Shao.Path n => if tau (a, sigma) ≤ j then
          |sourceValue J (eventCompletionKernel J Q) a x j sigma -
            (if sourceAlive J a x n sigma then 1 else 0)| else 0) :=
      Measurable.ite (measurableSet_le (htau sigma) measurable_const)
        (continuous_abs.measurable.comp ((hSourceM J j sigma).sub (hTerminalM J sigma))) measurable_const
    let seed : (Finset.range (n + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩
    convert Finset.measurable_sup' seed hslot using 1
    ext a
    exact (Finset.sup'_apply seed
      (fun j (a : Shao.Path n) => if tau (a, sigma) ≤ j then
        |sourceValue J (eventCompletionKernel J Q) a x j sigma -
          (if sourceAlive J a x n sigma then 1 else 0)| else 0) a).symm
  have hFutureI (J : MonitoredDomain) (tau : Shao.Path n × LabelPerm n → ℕ)
      (htau : ∀ sigma : LabelPerm n, Measurable (fun a : Shao.Path n => tau (a, sigma))) :
      Integrable (fun p : Shao.Path n × LabelPerm n => abcf_futureAt J Q x (tau p) p) (revealLaw P) := by
    apply Integrable.of_bound (hFutureM J tau htau).aestronglyMeasurable 1
    exact ae_of_all _ fun p => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hFutureRange J (tau p) p).1] using
        (hFutureRange J (tau p) p).2
  constructor
  · intro J r _hr
    exact ⟨hFutureM J (fun _ => r) (fun _ => measurable_const),
      hFutureI J (fun _ => r) (fun _ => measurable_const), hFutureRange J r⟩
  · intro J
    let tau : Shao.Path n × LabelPerm n → ℕ := fun p => energyCutoff p.1 H p.2
    have htau (sigma : LabelPerm n) : Measurable (fun a : Shao.Path n => tau (a, sigma)) :=
      Shao.Probability.SourceActualLocalProfileBudget.actual_energy_cutoff_measurable H hH sigma
    have hm : Measurable (abcf_h0Future J Q H x) := hFutureM J tau htau
    have hi : Integrable (abcf_h0Future J Q H x) (revealLaw P) := hFutureI J tau htau
    have hidm : Measurable (fun a : Shao.Path n => abcf_h0Future J Q H x (a, Equiv.refl (Fin n))) :=
      hm.comp (measurable_id.prodMk measurable_const)
    have hidi : Integrable (fun a : Shao.Path n => abcf_h0Future J Q H x (a, Equiv.refl (Fin n))) P := by
      apply Integrable.of_bound hidm.aestronglyMeasurable 1
      exact ae_of_all _ fun a => by
        simpa only [abcf_h0Future, tau, Real.norm_eq_abs, abs_of_nonneg (hFutureRange J (tau (a, Equiv.refl (Fin n)))
          (a, Equiv.refl (Fin n))).1] using
            (hFutureRange J (tau (a, Equiv.refl (Fin n))) (a, Equiv.refl (Fin n))).2
    exact ⟨hm, hi, hidm, hidi, fun p => hFutureRange J (tau p) p⟩

private theorem abcf_masked_future_eq_Icc
    {n : ℕ} (J : MonitoredDomain) (Q : Measure BridgeNoise) (x : ℝ)
    (a : Shao.Path n) (r : ℕ) (hr : r ≤ n) (sigma : LabelPerm n) :
    abcf_futureAt J Q x r (a, sigma) =
      (Finset.Icc r n).sup' ⟨r, Finset.mem_Icc.mpr ⟨le_rfl, hr⟩⟩
        (fun j => |sourceValue J (eventCompletionKernel J Q) a x j sigma -
          (if sourceAlive J a x n sigma then 1 else 0)|) := by
  classical
  let f : ℕ → ℝ := fun j => |sourceValue J (eventCompletionKernel J Q) a x j sigma -
    (if sourceAlive J a x n sigma then 1 else 0)|
  let seedR : (Finset.range (n + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩
  let seedI : (Finset.Icc r n).Nonempty := ⟨r, Finset.mem_Icc.mpr ⟨le_rfl, hr⟩⟩
  change (Finset.range (n + 1)).sup' seedR (fun j => if r ≤ j then f j else 0) =
    (Finset.Icc r n).sup' seedI f
  have hI0 : 0 ≤ (Finset.Icc r n).sup' seedI f :=
    (abs_nonneg _).trans (Finset.le_sup' f (Finset.mem_Icc.mpr ⟨le_rfl, hr⟩))
  apply le_antisymm
  · apply Finset.sup'_le
    intro j hj
    by_cases hrj : r ≤ j
    · rw [if_pos hrj]
      exact Finset.le_sup' f (Finset.mem_Icc.mpr ⟨hrj, by have hh := Finset.mem_range.mp hj; omega⟩)
    · simpa only [if_neg hrj] using hI0
  · apply Finset.sup'_le
    intro j hj
    have hji := Finset.mem_Icc.mp hj
    have hmem : j ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have hh := Finset.le_sup' (fun k => if r ≤ k then f k else 0) hmem
    simpa only [if_pos hji.1] using hh

private theorem abcf_append_future_corridor
    {ΩB : Type*} [MeasurableSpace ΩB]
    (Bm : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hBm : IsBrownianReal Bm PB) (r t : ℕ)
    (v : Shao.Path r) (u : Shao.Path t) (x : ℝ) (hx : 0 ≤ x) (J : MonitoredDomain) :
    let Q : Measure BridgeNoise := bridgeLaw Bm PB
    let U : ℝ := Shao.energy u
    let Jmax : ℝ := (Finset.range (t + 1)).sup'
      ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ t)⟩ (fun l => |Shao.prefixSum u l|)
    let wall : ℝ := x * Real.sqrt (U + Shao.energy v)
    let w : ℝ → ℝ := fun s => wall - s * Shao.prefixSum v r
    let D : ℝ := abcf_futureAt J Q x r (Fin.append v u, Equiv.refl (Fin (r + t)))
    (U = 0 → D = 0) ∧
      D ≤ if 0 < U then
        ∑ s ∈ Shao.Probability.SourceActualLocalProfileBudget.wallSigns J,
          (if Shao.maxWithZero (s • v) ≤ wall then
            (if 0 < w s ∧ w s ≤ 2 * Jmax then 1 else 0) +
            (if 2 * Jmax < w s then 2 * Real.exp (-(w s ^ 2) / (32 * U)) else 0)
          else 0)
      else 0 := by
  classical
  intro Q U Jmax wall w D
  let a : Shao.Path (r + t) := Fin.append v u
  have hEnergy : Shao.energy a = Shao.energy v + U := by
    simp only [a, Shao.energy, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    rfl
  have hPre (k : ℕ) (hk : k ≤ r) : Shao.prefixSum a k = Shao.prefixSum v k := by
    simp only [a, Shao.prefixSum, Finset.sum_filter, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    change (∑ i : Fin r, if i.val < k then v i else 0) +
      (∑ i : Fin t, if r + i.val < k then u i else 0) =
        ∑ i : Fin r, if i.val < k then v i else 0
    have hz : (∑ i : Fin t, if r + i.val < k then u i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact if_neg (by omega)
    rw [hz, add_zero]
  have hAfter (l : ℕ) :
      Shao.prefixSum a (r + l) = Shao.prefixSum v r + Shao.prefixSum u l := by
    simp only [a, Shao.prefixSum, Finset.sum_filter, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    change (∑ i : Fin r, if i.val < r + l then v i else 0) +
      (∑ i : Fin t, if r + i.val < r + l then u i else 0) =
        (∑ i : Fin r, if i.val < r then v i else 0) +
          (∑ i : Fin t, if i.val < l then u i else 0)
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [if_pos (by omega), if_pos i.is_lt]
    · apply Finset.sum_congr rfl
      intro i _
      simp only [Nat.add_lt_add_iff_left]
  have hSquare : Shao.prefixSquares a r = Shao.energy v := by
    simp only [a, Shao.prefixSquares, Finset.sum_filter, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    change (∑ i : Fin r, if i.val < r then (v i) ^ 2 else 0) +
      (∑ i : Fin t, if r + i.val < r then (u i) ^ 2 else 0) = ∑ i : Fin r, (v i) ^ 2
    have hz : (∑ i : Fin t, if r + i.val < r then (u i) ^ 2 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact if_neg (by omega)
    rw [hz, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    exact if_pos i.is_lt
  have hU : remainingEnergy a r (Equiv.refl (Fin (r + t))) = U := by
    change Shao.energy a - Shao.prefixSquares a r = U
    rw [hSquare, hEnergy]
    ring
  have hWall : actualWall a x = wall := by
    simp only [actualWall, hEnergy, wall, add_comm]
  have hJ :
      (Finset.Icc 0 ((r + t) - r)).sup'
        ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩
        (fun l => |Shao.prefixSum a (r + l) - Shao.prefixSum a r|) = Jmax := by
    have hset : Finset.Icc 0 t = Finset.range (t + 1) := by
      ext l
      simp only [Finset.mem_Icc, Finset.mem_range, Nat.zero_le, true_and]
      omega
    have hfun : (fun l => |Shao.prefixSum a (r + l) - Shao.prefixSum a r|) =
        (fun l => |Shao.prefixSum u l|) := by
      funext l
      rw [hAfter, hPre r le_rfl]
      congr 1
      ring
    simp only [Nat.add_sub_cancel_left, hfun, hset]
    rfl
  have hraw := Shao.Probability.actual_source_terminal_corridor_envelope PB Bm hBm
    (r + t) a r (Nat.le_add_right r t) x hx J
  dsimp only at hraw
  rw [← abcf_masked_future_eq_Icc J Q x a r (Nat.le_add_right r t) (Equiv.refl (Fin (r + t)))] at hraw
  rw [hU, hJ, hWall] at hraw
  simp only [hPre r le_rfl] at hraw
  change 0 ≤ D ∧ D ≤ 1 ∧ (U = 0 → D = 0) ∧ (x = 0 → D = 0) ∧
    D ≤ (if 0 < U ∧ sourceAlive J a x r (Equiv.refl (Fin (r + t))) then
      ∑ s ∈ Shao.Probability.SourceActualLocalProfileBudget.wallSigns J,
        ((if 0 < w s ∧ w s ≤ 2 * Jmax then 1 else 0) +
          (if 2 * Jmax < w s then 2 * Real.exp (-(w s ^ 2) / (32 * U)) else 0))
      else 0) at hraw
  have hClosed (ha : sourceAlive J a x r (Equiv.refl (Fin (r + t))))
      (s : ℝ) (hs : s ∈ Shao.Probability.SourceActualLocalProfileBudget.wallSigns J) :
      Shao.maxWithZero (s • v) ≤ wall := by
    apply (Shao.maxWithZero_le_iff (s • v) wall).mpr
    intro k hk
    rw [Shao.prefixSum_smul]
    have hp := ha.2.2 k hk
    change Interior J (actualWall a x) (Shao.prefixSum a k) at hp
    rw [hWall, hPre k hk] at hp
    cases J with
    | upper =>
        simp only [Shao.Probability.SourceActualLocalProfileBudget.wallSigns, Finset.mem_singleton] at hs
        subst s
        simpa only [one_mul] using hp.le
    | lower =>
        simp only [Shao.Probability.SourceActualLocalProfileBudget.wallSigns, Finset.mem_singleton] at hs
        subst s
        change -wall < Shao.prefixSum v k at hp
        simp only [neg_one_mul]
        linarith only [hp]
    | interval =>
        simp only [Shao.Probability.SourceActualLocalProfileBudget.wallSigns, Finset.mem_insert, Finset.mem_singleton] at hs
        rcases hs with rfl | rfl
        · simpa only [one_mul] using hp.2.le
        · simp only [neg_one_mul]
          linarith only [hp.1]
  refine ⟨hraw.2.2.1, hraw.2.2.2.2.trans ?_⟩
  by_cases hpos : 0 < U
  · rw [if_pos hpos]
    by_cases ha : sourceAlive J a x r (Equiv.refl (Fin (r + t)))
    · rw [if_pos ⟨hpos, ha⟩]
      apply Finset.sum_le_sum
      intro s hs
      rw [if_pos (hClosed ha s hs)]
    · rw [if_neg (by tauto : ¬ (0 < U ∧ sourceAlive J a x r (Equiv.refl (Fin (r + t)))))]
      apply Finset.sum_nonneg
      intro s _
      split_ifs <;> positivity
  · rw [if_neg hpos, if_neg (by tauto : ¬ (0 < U ∧ sourceAlive J a x r (Equiv.refl (Fin (r + t)))))]

private theorem abcf_h0_future_reorder
    {n : ℕ} (J : MonitoredDomain) (Q : Measure BridgeNoise) (H x : ℝ)
    (a : Shao.Path n) (sigma : LabelPerm n) :
    abcf_h0Future J Q H x (a, sigma) =
      abcf_h0Future J Q H x (Shao.Probability.Spitzer.reorder a sigma, Equiv.refl (Fin n)) := by
  classical
  have hE : Shao.energy (Shao.Probability.Spitzer.reorder a sigma) = Shao.energy a :=
    Equiv.sum_comp sigma (fun i => (a i) ^ 2)
  have hS : Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) n = Shao.prefixSum a n := by
    simpa only [Shao.prefixSum_length, Shao.Probability.Spitzer.reorder] using Equiv.sum_comp sigma a
  have hW : actualWall (Shao.Probability.Spitzer.reorder a sigma) x = actualWall a x := by
    simp only [actualWall, hE]
  have hRefl (b : Shao.Path n) : Shao.Probability.Spitzer.reorder b (Equiv.refl (Fin n)) = b := by
    funext i
    rfl
  have hR (j : ℕ) :
      remainingEnergy a j sigma =
        remainingEnergy (Shao.Probability.Spitzer.reorder a sigma) j (Equiv.refl (Fin n)) := by
    simp only [remainingEnergy, hE, hRefl]
  have hAlive (j : ℕ) :
      sourceAlive J a x j sigma ↔
        sourceAlive J (Shao.Probability.Spitzer.reorder a sigma) x j (Equiv.refl (Fin n)) := by
    simp only [sourceAlive, hE, hW, hS, hRefl]
  have hValue (j : ℕ) : sourceValue J (eventCompletionKernel J Q) a x j sigma =
      sourceValue J (eventCompletionKernel J Q) (Shao.Probability.Spitzer.reorder a sigma) x j (Equiv.refl (Fin n)) := by
    simp only [sourceValue, hAlive, hW, hS, ← hR, hRefl]
  have hCut : energyCutoff a H sigma =
      energyCutoff (Shao.Probability.Spitzer.reorder a sigma) H (Equiv.refl (Fin n)) := by
    simp only [energyCutoff, ← hR]
  unfold abcf_h0Future abcf_futureAt
  simp only [hCut, hValue, hAlive]

private theorem abcf_fixed_suffix_terminal_all_level :
    ∃ Ccorr : ℝ, 0 < Ccorr ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (bound : ℝ), 0 < bound → (∀ᵐ z : ℝ ∂rho, |z| ≤ bound) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        ∀ (r t : ℕ), 0 < r → 0 < t → r + t ≤ 2 * r →
          ∀ (x : ℝ), (1 / 2 : ℝ) ≤ x →
            bound ≤ Real.sqrt (r + t : ℝ) / (100 * x) →
            ∀ {ΩB : Type*} [MeasurableSpace ΩB]
              (Bm : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
              IsBrownianReal Bm PB →
              let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
              let H : ℝ := 4 * beta ^ 2
              let Q : Measure BridgeNoise := bridgeLaw Bm PB
              ∀ (J : MonitoredDomain) (u : Shao.Path t),
                let U : ℝ := Shao.energy u
                let Jmax : ℝ := (Finset.range (t + 1)).sup'
                  ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ t)⟩ (fun l => |Shao.prefixSum u l|)
                let Phi : Shao.Path r → ℝ := fun v =>
                  abcf_futureAt J Q x r (Fin.append v u, Equiv.refl (Fin (r + t)))
                Integrable Phi (Measure.pi (fun _ : Fin r => rho)) ∧
                  (∫ v, Phi v ∂Measure.pi (fun _ : Fin r => rho)) ≤
                    Ccorr / (r + t : ℝ) * (8 * Jmax ^ 2 + 128 * U + 2 * H) := by
  classical
  obtain ⟨CS, hCS, hStrip⟩ :=
    Shao.C2.ActualBadIntervalNegativeBudget.actual_auxiliary_level_true_energy_closed_strip
  refine ⟨128 * CS * (Real.exp 1 + 2), by positivity, ?_⟩
  intro rho hProb bound hb hsupport hmean hsecond r t hr ht hlate x hx hscale
    ΩB hΩB Bm PB hPB hBm beta H Q J u U Jmax Phi
  letI : IsProbabilityMeasure rho := hProb
  letI : IsProbabilityMeasure PB := hPB
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw Bm PB hBm
  let P : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => rho)
  have hn : 0 < r + t := by omega
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hnR : 0 < (r + t : ℝ) := by exact_mod_cast hn
  have hhalf : (r + t : ℝ) ≤ 2 * (r : ℝ) := by exact_mod_cast hlate
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hown := abcf_bounded_own_budget_identities rho bound hb hsupport hmean hsecond
    (r + t) hn x hx (by simpa only [Nat.cast_add] using hscale)
  have hH : 0 < H := hown.2.2.2.2.2.2.1
  have hU : 0 ≤ U := Shao.energy_nonneg u
  have hJ : 0 ≤ Jmax := by
    have hh := Finset.le_sup' (fun l => |Shao.prefixSum u l|)
      (Finset.mem_range.mpr (Nat.zero_lt_succ t))
    simpa only [Shao.prefixSum_zero, abs_zero] using hh
  have hAppendM : Measurable (fun v : Shao.Path r => Fin.append v u) := by
    apply Measurable.of_eval
    intro i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · simpa only [Fin.append_left] using (measurable_pi_apply k : Measurable (fun v : Shao.Path r => v k))
    · simpa only [Fin.append_right] using (measurable_const : Measurable (fun _ : Shao.Path r => u k))
  have hFull := abcf_future_measurable_integrable Bm PB hBm (r + t)
    (Measure.pi (fun _ : Fin (r + t) => rho)) H x hH hx0
  have hPhiM : Measurable Phi :=
    (hFull.1 J r (Nat.le_add_right r t)).1.comp (hAppendM.prodMk measurable_const)
  have hPhiRange (v : Shao.Path r) : 0 ≤ Phi v ∧ Phi v ≤ 1 :=
    (hFull.1 J r (Nat.le_add_right r t)).2.2 (Fin.append v u, Equiv.refl (Fin (r + t)))
  have hPhiI : Integrable Phi P := by
    apply Integrable.of_bound hPhiM.aestronglyMeasurable 1
    exact ae_of_all _ fun v => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hPhiRange v).1] using (hPhiRange v).2
  refine ⟨hPhiI, ?_⟩
  by_cases hUz : U = 0
  · have hzero : Phi = 0 := by
      funext v
      exact (abcf_append_future_corridor Bm PB hBm r t v u x hx0 J).1 hUz
    rw [hzero]
    simp only [Pi.zero_apply, integral_zero]
    positivity
  have hUp : 0 < U := lt_of_le_of_ne hU (Ne.symm hUz)
  let T : ℝ := 32 * (U + Jmax ^ 2)
  have hT : 0 < T := by dsimp [T]; positivity
  let signs : Finset ℝ := Shao.Probability.SourceActualLocalProfileBudget.wallSigns J
  let wall : Shao.Path r → ℝ := fun v => x * Real.sqrt (U + Shao.energy v)
  let w : ℝ → Shao.Path r → ℝ := fun s v => wall v - s * Shao.prefixSum v r
  let A : ℝ → Set (Shao.Path r) := fun s => {v | Shao.maxWithZero (s • v) ≤ wall v}
  let f : ℝ → Shao.Path r → ℝ := fun s v =>
    Real.exp (-((max (w s v) 0) ^ 2) / T)
  let profiles : Shao.Path r → ℝ := fun v => ∑ s ∈ signs, (A s).indicator (f s) v
  have hSigns : signs.card ≤ 2 ∧ ∀ s ∈ signs, s = 1 ∨ s = -1 := by
    cases J <;> norm_num [signs, Shao.Probability.SourceActualLocalProfileBudget.wallSigns]
  have hWallM : Measurable wall := measurable_const.mul ((measurable_const.add Shao.measurable_energy).sqrt)
  have hAm (s : ℝ) : MeasurableSet (A s) :=
    measurableSet_le (Shao.measurable_maxWithZero.comp
      (Measurable.of_eval fun i => measurable_const.mul (measurable_pi_apply i))) hWallM
  have hwM (s : ℝ) : Measurable (w s) := hWallM.sub (measurable_const.mul (Shao.measurable_prefixSum r))
  have hProfileI (s : ℝ) : Integrable ((A s).indicator (f s)) P := by
    simpa only [sub_zero] using
      (Shao.Probability.gaussian_wall_profile_layer_cake
        P (A s) (hAm s) (w s) (hwM s) T 0 hT le_rfl).1
  have hCDF (s : ℝ) (hs : s ∈ signs) (v : ℝ) (hv : 0 ≤ v) :
      P.real {a | a ∈ A s ∧ w s a ≤ v} ≤
        (2 * CS) * (v ^ 2 / (r : ℝ) + (beta / Real.sqrt (r : ℝ)) ^ 2) := by
    have hraw := hStrip rho bound hb hsupport hmean hsecond (r + t) hn x hx
      (by simpa only [Nat.cast_add] using hscale)
      r hr (Nat.le_add_right r t) hlate U v s hU hv (hSigns.2 s hs)
    have hsubset : {a | a ∈ A s ∧ w s a ≤ v} ⊆
        {a : Shao.Path r | Shao.maxWithZero (s • a) ≤ wall a ∧
          wall a - v ≤ s * Shao.prefixSum a r ∧ s * Shao.prefixSum a r ≤ wall a} := by
      intro a ha
      have hsum := (Shao.maxWithZero_le_iff (s • a) (wall a)).mp ha.1 r le_rfl
      rw [Shao.prefixSum_smul] at hsum
      refine ⟨ha.1, ?_, hsum⟩
      have hwa : wall a - s * Shao.prefixSum a r ≤ v := ha.2
      linarith only [hwa]
    calc
      _ ≤ P.real {a : Shao.Path r | Shao.maxWithZero (s • a) ≤ wall a ∧
          wall a - v ≤ s * Shao.prefixSum a r ∧ s * Shao.prefixSum a r ≤ wall a} := measureReal_mono hsubset
      _ ≤ CS * (v + beta) ^ 2 / (r : ℝ) := hraw
      _ ≤ CS * (2 * v ^ 2 + 2 * beta ^ 2) / (r : ℝ) := by
        gcongr
        nlinarith only [sq_nonneg (v - beta)]
      _ = _ := by rw [div_pow, Real.sq_sqrt hrR.le]; ring
  have hProfileBound (s : ℝ) (hs : s ∈ signs) :
      (∫ v, (A s).indicator (f s) v ∂P) ≤ 2 * CS * (2 * T / (r : ℝ) + beta ^ 2 / (r : ℝ)) := by
    have hh := Shao.Probability.gaussian_wall_profile_of_quadratic_closed_cdf
      P (A s) (hAm s) (w s) (hwM s) (2 * CS) (beta / Real.sqrt (r : ℝ)) (r : ℝ) T 0
      (by positivity) hrR hT le_rfl (hCDF s hs)
    simpa only [sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, div_pow,
      Real.sq_sqrt hrR.le] using hh
  have hProfilesI : Integrable profiles P := integrable_finsetSum _ (fun s _ => hProfileI s)
  have hProfilesBound : (∫ v, profiles v ∂P) ≤
      2 * (2 * CS * (2 * T / (r : ℝ) + beta ^ 2 / (r : ℝ))) := by
    rw [integral_finsetSum _ (fun s _ => hProfileI s)]
    calc
      _ ≤ ∑ _s ∈ signs, (2 * CS * (2 * T / (r : ℝ) + beta ^ 2 / (r : ℝ))) :=
        Finset.sum_le_sum (fun s hs => hProfileBound s hs)
      _ = (signs.card : ℝ) * (2 * CS * (2 * T / (r : ℝ) + beta ^ 2 / (r : ℝ))) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hSigns.1) (by positivity)
  have hProfilePoint (v : Shao.Path r) : Phi v ≤ (Real.exp 1 + 2) * profiles v := by
    have hc : Phi v ≤ if 0 < U then ∑ s ∈ signs,
        (if v ∈ A s then (if 0 < w s v ∧ w s v ≤ 2 * Jmax then 1 else 0) +
          (if 2 * Jmax < w s v then 2 * Real.exp (-(w s v ^ 2) / (32 * U)) else 0) else 0) else 0 :=
      (abcf_append_future_corridor Bm PB hBm r t v u x hx0 J).2
    rw [if_pos hUp] at hc
    apply hc.trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _hs
    by_cases ha : v ∈ A s
    · rw [if_pos ha, Set.indicator_of_mem ha]
      have hsum := (Shao.maxWithZero_le_iff (s • v) (wall v)).mp ha r le_rfl
      rw [Shao.prefixSum_smul] at hsum
      have hw0 : 0 ≤ w s v := sub_nonneg.mpr hsum
      have hf : f s v = Real.exp (-(w s v ^ 2) / T) := by
        simp only [f, max_eq_left hw0]
      rw [hf]
      have hNear : (if 0 < w s v ∧ w s v ≤ 2 * Jmax then (1 : ℝ) else 0) ≤
          Real.exp 1 * Real.exp (-(w s v ^ 2) / T) := by
        by_cases hh : 0 < w s v ∧ w s v ≤ 2 * Jmax
        · rw [if_pos hh, ← Real.exp_add]
          apply Real.one_le_exp_iff.mpr
          have hw2 : w s v ^ 2 ≤ 4 * Jmax ^ 2 := by nlinarith only [hh.1, hh.2, hJ]
          have hquot : w s v ^ 2 / T ≤ 1 := (div_le_one hT).mpr (by dsimp [T]; nlinarith only [hw2, hU, sq_nonneg Jmax])
          simpa only [neg_div, sub_eq_add_neg] using (sub_nonneg.mpr hquot)
        · rw [if_neg hh]
          positivity
      have hFar : (if 2 * Jmax < w s v then 2 * Real.exp (-(w s v ^ 2) / (32 * U)) else 0) ≤
          2 * Real.exp (-(w s v ^ 2) / T) := by
        by_cases hh : 2 * Jmax < w s v
        · rw [if_pos hh]
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.exp_le_exp.mpr
          have hd : 32 * U ≤ T := by dsimp [T]; nlinarith only [sq_nonneg Jmax]
          have hquot := div_le_div_of_nonneg_left (sq_nonneg (w s v))
            (by positivity : 0 < 32 * U) hd
          simpa only [neg_div] using neg_le_neg hquot
        · rw [if_neg hh]
          positivity
      nlinarith only [hNear, hFar]
    · rw [if_neg ha, Set.indicator_of_notMem ha, mul_zero]
  have hIntegral : (∫ v, Phi v ∂P) ≤ (Real.exp 1 + 2) *
      (2 * (2 * CS * (2 * T / (r : ℝ) + beta ^ 2 / (r : ℝ)))) := by
    calc
      _ ≤ ∫ v, (Real.exp 1 + 2) * profiles v ∂P :=
        integral_mono hPhiI (hProfilesI.const_mul _) hProfilePoint
      _ = (Real.exp 1 + 2) * (∫ v, profiles v ∂P) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hProfilesBound (by positivity)
  let Bpay : ℝ := 8 * Jmax ^ 2 + 128 * U + 2 * H
  have hB0 : 0 ≤ Bpay := by dsimp [Bpay]; positivity
  have hNumer : 2 * T + beta ^ 2 ≤ 16 * Bpay := by
    dsimp only [T, Bpay, H]
    nlinarith only [hU, sq_nonneg Jmax, sq_nonneg beta]
  have hReduced :
      2 * (2 * CS * (2 * T / (r : ℝ) + beta ^ 2 / (r : ℝ))) ≤ 64 * CS * Bpay / (r : ℝ) := by
    calc
      _ = 4 * CS * ((2 * T + beta ^ 2) / (r : ℝ)) := by ring
      _ ≤ 4 * CS * ((16 * Bpay) / (r : ℝ)) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ (Real.exp 1 + 2) * (2 * (2 * CS * (2 * T / (r : ℝ) + beta ^ 2 / (r : ℝ)))) := hIntegral
    _ ≤ (Real.exp 1 + 2) * (64 * CS * Bpay / (r : ℝ)) :=
      mul_le_mul_of_nonneg_left hReduced (by positivity)
    _ = (64 * CS * (Real.exp 1 + 2) * Bpay) / (r : ℝ) := by ring
    _ ≤ (128 * CS * (Real.exp 1 + 2) * Bpay) / (r + t : ℝ) := by
      apply (div_le_div_iff₀ hrR hnR).mpr
      have hh := mul_le_mul_of_nonneg_left hhalf
        (show 0 ≤ 64 * CS * (Real.exp 1 + 2) * Bpay by positivity)
      nlinarith only [hh]
    _ = (128 * CS * (Real.exp 1 + 2)) / (r + t : ℝ) *
        (8 * Jmax ^ 2 + 128 * U + 2 * H) := by dsimp only [Bpay]; ring

theorem iid_actual_all_level_h0_terminal_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (bound : ℝ), 0 < bound → (∀ᵐ z : ℝ ∂rho, |z| ≤ bound) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), (1 / 2 : ℝ) ≤ x →
          bound ≤ Real.sqrt (n : ℝ) / (100 * x) →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          let delta : ℝ := beta / Real.sqrt (n : ℝ)
          let H : ℝ := 4 * beta ^ 2
          ∀ {ΩB : Type*} [MeasurableSpace ΩB]
            (Bm : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
            IsBrownianReal Bm PB →
            let Q : Measure BridgeNoise := bridgeLaw Bm PB
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
            let future : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ := fun J p =>
              (Finset.range (n + 1)).sup'
                ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩
                (fun j => if energyCutoff p.1 H p.2 ≤ j then
                  |sourceValue J (eventCompletionKernel J Q) p.1 x j p.2 -
                    (if sourceAlive J p.1 x n p.2 then 1 else 0)| else 0)
            ∀ J : MonitoredDomain,
              let identityFuture : Shao.Path n → ℝ := fun a => future J (a, Equiv.refl (Fin n))
              Measurable identityFuture ∧ Integrable identityFuture P ∧
                (∀ a, 0 ≤ identityFuture a ∧ identityFuture a ≤ 1) ∧
                0 ≤ (∫ a, identityFuture a ∂P) ∧ (∫ a, identityFuture a ∂P) ≤ C * delta ^ 2 ∧
                Measurable (future J) ∧ Integrable (future J) (revealLaw P) ∧
                (∀ p, 0 ≤ future J p ∧ future J p ≤ 1) ∧
                0 ≤ (∫ p, future J p ∂revealLaw P) ∧
                (∫ p, future J p ∂revealLaw P) ≤ C * delta ^ 2 := by
  classical
  obtain ⟨Ccorr, hCcorr, hCorr⟩ := abcf_fixed_suffix_terminal_all_level
  let Cterm : ℝ := 7200 * Ccorr + 100
  have hCterm : 0 < Cterm := by dsimp [Cterm]; positivity
  refine ⟨Cterm, hCterm, ?_⟩
  intro rho hProb bound hb hsupport hmean hsecond n hn x hx hscale beta delta H
    ΩB hΩB Bm PB hPB hBm Q P future J identityFuture
  letI : IsProbabilityMeasure rho := hProb
  letI : IsProbabilityMeasure PB := hPB
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw Bm PB hBm
  letI : IsProbabilityMeasure (revealLaw P) := by unfold revealLaw; infer_instance
  rcases abcf_bounded_own_budget_identities rho bound hb hsupport hmean hsecond n hn x hx hscale with
    ⟨h1, h2, h3, hbound1, hbeta, hdelta, hH, hnlarge, hR0, hRx, hcut, hPrefixBudget⟩
  change 0 < H at hH
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn4 : 4 ≤ n := by omega
  have hFull := abcf_future_measurable_integrable Bm PB hBm n P H x hH hx0
  have hData := hFull.2 J
  change Measurable identityFuture ∧ Integrable identityFuture P ∧
    (∀ a, 0 ≤ identityFuture a ∧ identityFuture a ≤ 1) ∧
    0 ≤ (∫ a, identityFuture a ∂P) ∧ (∫ a, identityFuture a ∂P) ≤ Cterm * delta ^ 2 ∧
    Measurable (future J) ∧ Integrable (future J) (revealLaw P) ∧
    (∀ p, 0 ≤ future J p ∧ future J p ≤ 1) ∧
    0 ≤ (∫ p, future J p ∂revealLaw P) ∧
    (∫ p, future J p ∂revealLaw P) ≤ Cterm * delta ^ 2
  have hIdRange (a : Shao.Path n) : 0 ≤ identityFuture a ∧ identityFuture a ≤ 1 :=
    hData.2.2.2.2 (a, Equiv.refl (Fin n))
  have hIdI : Integrable identityFuture P := hData.2.2.2.1
  have hIdOne : (∫ a, identityFuture a ∂P) ≤ 1 := by
    calc
      _ ≤ ∫ _ : Shao.Path n, (1 : ℝ) ∂P :=
        integral_mono hIdI (integrable_const 1) (fun a => (hIdRange a).2)
      _ = 1 := by simp
  have hBase : 4 * (n : ℝ) * delta ^ 2 = H := by
    simpa only [hR0] using hcut
  have hIdBound : (∫ a, identityFuture a ∂P) ≤ Cterm * delta ^ 2 := by
    by_cases hsmall : delta < 1 / 2
    swap
    · apply hIdOne.trans
      have hd : (1 / 2 : ℝ) ≤ delta := le_of_not_gt hsmall
      have hd2 : (1 : ℝ) ≤ 4 * delta ^ 2 := by nlinarith only [hd, hdelta]
      have hC4 : (4 : ℝ) ≤ Cterm := by dsimp [Cterm]; linarith only [hCcorr]
      nlinarith only [hd2, mul_le_mul_of_nonneg_right hC4 (sq_nonneg delta)]
    let L : ℕ := n / 2
    let rev : Shao.Path n → Shao.Path n := fun a i => a (Fin.rev i)
    let Qrev : Shao.Path n → ℕ → ℝ := fun a k => Shao.prefixSquares (rev a) k
    let NH : Shao.Path n → ℕ := fun a =>
      @dite ℕ (∃ k : ℕ, k ≤ L ∧ H ≤ Qrev a k) (Classical.propDecidable _)
        (fun he => @Nat.find (fun k : ℕ => k ≤ L ∧ H ≤ Qrev a k)
          (fun k => Classical.propDecidable _) he)
        (fun _ => L)
    let N : Shao.Path n → ℕ := fun a => max 0 (NH a)
    let r : Shao.Path n → ℕ := fun a => n - N a
    let U : Shao.Path n → ℝ := fun a => Shao.energy a - Shao.prefixSquares a (r a)
    let Jmax : Shao.Path n → ℝ := fun a =>
      (Finset.Icc 0 (N a)).sup' ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩
        (fun l => |Shao.prefixSum a (r a + l) - Shao.prefixSum a (r a)|)
    let exceptional : Set (Shao.Path n) := {a | Qrev a L < H}
    let kappa : Shao.Path n → ℕ := fun a => energyCutoff a H (Equiv.refl (Fin n))
    let tau : Shao.Path n → ℕ := fun a => min (kappa a) n
    have hRawR : Shao.truncationBudget
        (Measure.map (fun z : ℝ => z / Real.sqrt ((n : ℝ) * (∫ z : ℝ, z ^ 2 ∂rho))) rho) n 0 ≤ 1 / 2 := by
      simpa only [hsecond, mul_one, hR0] using hsmall.le
    have hRawH : 4 * (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂rho) *
        (Shao.truncationBudget
          (Measure.map (fun z : ℝ => z / Real.sqrt ((n : ℝ) * (∫ z : ℝ, z ^ 2 ∂rho))) rho) n 0) ^ 2 ≤ H := by
      simpa only [hsecond, mul_one] using hcut.le
    rcases Shao.Probability.actual_backward_terminal_raw_data rho n hn4 h2 hmean
        (by rw [hsecond]; norm_num) hRawR H hRawH 0 (Nat.zero_le _)
        (by
          simpa only [Nat.cast_zero, hsecond, div_one] using
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hH.le)) with
      ⟨_, _, _, hmNH, hmN, hmU, hmJ, hmTau, hstat, hiNH, hiN, hiU, hiJ,
        hENH, hEN, hE, hEU, hEJ⟩
    change Measurable N at hmN
    change Measurable U at hmU
    change Measurable Jmax at hmJ
    change ∀ a, 1 ≤ NH a ∧ NH a ≤ N a ∧ N a ≤ L ∧
      U a = Qrev a (N a) ∧
      (a ∉ exceptional → tau a = if NH a ≤ 0 then r a else r a + 1) at hstat
    change Integrable U P at hiU
    change Integrable (fun a => Jmax a ^ 2) P at hiJ
    have hEN' : (∫ a, (N a : ℝ) ∂P) ≤ 7 * H := by
      change (∫ a, (N a : ℝ) ∂P) ≤ 7 * H / (∫ z : ℝ, z ^ 2 ∂rho) at hEN
      simpa only [hsecond, div_one] using hEN
    have hE' : P.real exceptional ≤ 12 * H / (n : ℝ) := by
      simpa only [hsecond, mul_one] using hE
    have hEU' : (∫ a, U a ∂P) = ∫ a, (N a : ℝ) ∂P := by
      change (∫ a, U a ∂P) = (∫ z : ℝ, z ^ 2 ∂rho) * (∫ a, (N a : ℝ) ∂P) at hEU
      simpa only [hsecond, one_mul] using hEU
    have hEJ' : (∫ a, Jmax a ^ 2 ∂P) ≤ 16 * (∫ a, (N a : ℝ) ∂P) := by
      change (∫ a, Jmax a ^ 2 ∂P) ≤ 16 * (∫ z : ℝ, z ^ 2 ∂rho) * (∫ a, (N a : ℝ) ∂P) at hEJ
      simpa only [hsecond, mul_one] using hEJ
    have hrn (a : Shao.Path n) : r a ≤ n := Nat.sub_le n (N a)
    have hNpos (a : Shao.Path n) : 1 ≤ N a := (hstat a).1.trans (hstat a).2.1
    have hmr : Measurable r :=
      (measurable_of_countable (fun k : ℕ => n - k)).comp hmN
    let Dr : Shao.Path n → ℝ := fun a => abcf_futureAt J Q x (r a) (a, Equiv.refl (Fin n))
    let jointFuture : Shao.Path n × ℕ → ℝ := fun p =>
      if p.2 ≤ n then abcf_futureAt J Q x p.2 (p.1, Equiv.refl (Fin n)) else 0
    have hmJoint : Measurable jointFuture := by
      apply measurable_from_prod_countable_left
      intro j
      by_cases hj : j ≤ n
      · simpa only [jointFuture, if_pos hj, Function.comp_def, id_eq, Q] using
          (hFull.1 J j hj).1.comp (measurable_id.prodMk measurable_const)
      · simpa only [jointFuture, if_neg hj] using
          (measurable_const : Measurable (fun _ : Shao.Path n => (0 : ℝ)))
    have hmDr : Measurable Dr := by
      convert hmJoint.comp (measurable_id.prodMk hmr) using 1
      funext a
      simp only [jointFuture, Function.comp_def, if_pos (hrn a)]
      rfl
    have hDrRange (a : Shao.Path n) : 0 ≤ Dr a ∧ Dr a ≤ 1 :=
      (hFull.1 J (r a) (hrn a)).2.2 (a, Equiv.refl (Fin n))
    have hiDr : Integrable Dr P := by
      apply Integrable.of_bound hmDr.aestronglyMeasurable 1
      exact ae_of_all _ fun a => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hDrRange a).1] using (hDrRange a).2
    let W : Shao.Path n → ℝ := fun a => 8 * Jmax a ^ 2 + 128 * U a + 2 * H
    have hiW : Integrable W P := ((hiJ.const_mul 8).add (hiU.const_mul 128)).add (integrable_const (2 * H))
    have hmW : Measurable W := (((hmJ.pow_const 2).const_mul 8).add (hmU.const_mul 128)).add_const (2 * H)
    have hW0 (a : Shao.Path n) : 0 ≤ W a := by
      have hu : 0 ≤ U a :=
        (remaining_population_geometry a (r a) (hrn a) (Equiv.refl (Fin n))).1
      dsimp [W]
      positivity
    let g : Shao.Path n → ℝ := fun a => (Ccorr / (n : ℝ)) * W a
    let c : Shao.Path n → ℝ := fun a => min (g a) 1
    have hg0 (a : Shao.Path n) : 0 ≤ g a := mul_nonneg (div_nonneg hCcorr.le hnR.le) (hW0 a)
    have hcm : Measurable c := (hmW.const_mul _).min measurable_const
    have hig : Integrable g P := hiW.const_mul _
    have hic : Integrable c P := by
      apply Integrable.of_bound hcm.aestronglyMeasurable 1
      exact ae_of_all _ fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hg0 a) (by norm_num))]
        exact min_le_right _ _
    have hslice (t : ℕ) : Integrable (fun a => if N a = t then Dr a - c a else 0) P := by
      have hS : MeasurableSet {a : Shao.Path n | N a = t} :=
        (measurableSet_singleton t).preimage hmN
      convert (hiDr.sub hic).indicator hS using 1
      funext a
      by_cases hat : N a = t <;>
        simp only [Set.indicator, Set.mem_setOf_eq, hat, if_true, if_false, Pi.sub_apply]
    have hpiecePositive (rt t : ℕ) (ht0 : 0 < t) (ht : t ≤ L) (hnt : rt + t = n) :
        (∫ a, (if N a = t then Dr a - c a else 0) ∂P) ≤ 0 := by
      subst n
      have hrt : 0 < rt := by dsimp [L] at ht; omega
      have hlate : rt + t ≤ 2 * rt := by dsimp [L] at ht; omega
      let prefixPart : Shao.Path (rt + t) → Shao.Path rt := fun a i =>
        a ⟨i.val, by omega⟩
      let suffixPart : Shao.Path (rt + t) → Shao.Path t := fun a i =>
        a ⟨rt + i.val, by omega⟩
      have hmerge (a : Shao.Path (rt + t)) : Fin.append (prefixPart a) (suffixPart a) = a := by
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · rw [Fin.append_left]
          congr 1
        · rw [Fin.append_right]
          congr 1
      have hEnergy (v : Shao.Path rt) (b : Shao.Path t) :
          Shao.energy (Fin.append v b) = Shao.energy v + Shao.energy b := by
        simp only [Shao.energy, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
      have hSquare (v : Shao.Path rt) (b : Shao.Path t) :
          Shao.prefixSquares (Fin.append v b) rt = Shao.energy v := by
        simp only [Shao.prefixSquares, Shao.energy, Finset.sum_filter, Fin.sum_univ_add,
          Fin.append_left, Fin.append_right]
        change (∑ i : Fin rt, if i.val < rt then (v i) ^ 2 else 0) +
          (∑ i : Fin t, if rt + i.val < rt then (b i) ^ 2 else 0) = ∑ i : Fin rt, (v i) ^ 2
        have hz : (∑ i : Fin t, if rt + i.val < rt then (b i) ^ 2 else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          exact if_neg (by omega)
        rw [hz, add_zero]
        apply Finset.sum_congr rfl
        intro i _
        exact if_pos i.is_lt
      have hAfter (v : Shao.Path rt) (b : Shao.Path t) (l : ℕ) :
          Shao.prefixSum (Fin.append v b) (rt + l) = Shao.prefixSum v rt + Shao.prefixSum b l := by
        simp only [Shao.prefixSum, Finset.sum_filter, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
        change (∑ i : Fin rt, if i.val < rt + l then v i else 0) +
          (∑ i : Fin t, if rt + i.val < rt + l then b i else 0) =
            (∑ i : Fin rt, if i.val < rt then v i else 0) +
              (∑ i : Fin t, if i.val < l then b i else 0)
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          rw [if_pos (by omega), if_pos i.is_lt]
        · apply Finset.sum_congr rfl
          intro i _
          simp only [Nat.add_lt_add_iff_left]
      have hTailEnergy (a : Shao.Path (rt + t)) :
          Shao.energy (suffixPart a) = Shao.energy a - Shao.prefixSquares a rt := by
        have he := hEnergy (prefixPart a) (suffixPart a)
        have hs := hSquare (prefixPart a) (suffixPart a)
        rw [hmerge a] at he hs
        linarith only [he, hs]
      have hTailSum (a : Shao.Path (rt + t)) (l : ℕ) :
          Shao.prefixSum (suffixPart a) l = Shao.prefixSum a (rt + l) - Shao.prefixSum a rt := by
        have ha := hAfter (prefixPart a) (suffixPart a) l
        have h0 := hAfter (prefixPart a) (suffixPart a) 0
        rw [hmerge a] at ha h0
        simp only [Nat.add_zero, Shao.prefixSum_zero, add_zero] at h0
        linarith only [ha, h0]
      let Jt : Shao.Path t → ℝ := fun b => (Finset.range (t + 1)).sup'
        ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ t)⟩ (fun l => |Shao.prefixSum b l|)
      let Wt : Shao.Path t → ℝ := fun b => 8 * Jt b ^ 2 + 128 * Shao.energy b + 2 * H
      let cost : Shao.Path t → ℝ := fun b => (Ccorr / (rt + t : ℝ)) * Wt b
      have hJtm : Measurable Jt := by
        have hslot (l : ℕ) (_hl : l ∈ Finset.range (t + 1)) :
            Measurable (fun b : Shao.Path t => |Shao.prefixSum b l|) :=
          continuous_abs.measurable.comp (Shao.measurable_prefixSum l)
        convert Finset.measurable_sup'
          (s := Finset.range (t + 1)) ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ t)⟩
          hslot using 1
        ext b
        exact (Finset.sup'_apply
          ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ t)⟩
          (fun l (b : Shao.Path t) => |Shao.prefixSum b l|) b).symm
      have hWtm : Measurable Wt :=
        (((hJtm.pow_const 2).const_mul 8).add (Shao.measurable_energy.const_mul 128)).add_const (2 * H)
      have hcostm : Measurable cost := hWtm.const_mul _
      have hcost0 (b : Shao.Path t) : 0 ≤ cost b := by
        have hu := Shao.energy_nonneg b
        dsimp [cost, Wt]
        positivity
      have hAppendM : Measurable (fun p : Shao.Path rt × Shao.Path t => Fin.append p.1 p.2) := by
        apply Measurable.of_eval
        intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa only [Fin.append_left, Function.comp_def] using (measurable_pi_apply j).comp measurable_fst
        · simpa only [Fin.append_right, Function.comp_def] using (measurable_pi_apply j).comp measurable_snd
      let Phi : Shao.Path rt × Shao.Path t → ℝ := fun p =>
        abcf_futureAt J Q x rt (Fin.append p.1 p.2, Equiv.refl (Fin (rt + t))) - min (cost p.2) 1
      have hPhim : Measurable Phi :=
        ((hFull.1 J rt (Nat.le_add_right rt t)).1.comp (hAppendM.prodMk measurable_const)).sub
          ((hcostm.comp measurable_snd).min measurable_const)
      have hPhib (p : Shao.Path rt × Shao.Path t) : |Phi p| ≤ 1 := by
        have hf := (hFull.1 J rt (Nat.le_add_right rt t)).2.2
          (Fin.append p.1 p.2, Equiv.refl (Fin (rt + t)))
        have hc0 : 0 ≤ min (cost p.2) 1 := le_min (hcost0 p.2) (by norm_num)
        have hc1 : min (cost p.2) 1 ≤ 1 := min_le_right _ _
        exact abs_le.mpr ⟨by dsimp [Phi]; linarith only [hf.1, hc1],
          by dsimp [Phi]; linarith only [hf.2, hc0]⟩
      have hsection (b : Shao.Path t) :
          (∫ v : Shao.Path rt, Phi (v, b) ∂Measure.pi (fun _ : Fin rt => rho)) ≤ 0 := by
        have hp := hCorr rho bound hb hsupport hmean hsecond rt t hrt ht0 hlate x hx
          (by simpa only [Nat.cast_add] using hscale) Bm PB hBm J b
        change Integrable
          (fun v : Shao.Path rt => abcf_futureAt J Q x rt (Fin.append v b, Equiv.refl (Fin (rt + t))))
          (Measure.pi (fun _ : Fin rt => rho)) ∧
          (∫ v : Shao.Path rt, abcf_futureAt J Q x rt (Fin.append v b, Equiv.refl (Fin (rt + t)))
            ∂Measure.pi (fun _ : Fin rt => rho)) ≤ cost b at hp
        have hone : (∫ v : Shao.Path rt,
            abcf_futureAt J Q x rt (Fin.append v b, Equiv.refl (Fin (rt + t)))
              ∂Measure.pi (fun _ : Fin rt => rho)) ≤ 1 := by
          calc
            _ ≤ ∫ _ : Shao.Path rt, (1 : ℝ) ∂Measure.pi (fun _ : Fin rt => rho) :=
              integral_mono hp.1 (integrable_const 1) (fun v =>
                ((hFull.1 J rt (Nat.le_add_right rt t)).2.2
                  (Fin.append v b, Equiv.refl (Fin (rt + t)))).2)
            _ = 1 := by simp
        change (∫ v : Shao.Path rt,
          (abcf_futureAt J Q x rt (Fin.append v b, Equiv.refl (Fin (rt + t))) - min (cost b) 1)
            ∂Measure.pi (fun _ : Fin rt => rho)) ≤ 0
        rw [integral_sub hp.1 (integrable_const _)]
        simp only [integral_const, probReal_univ, one_smul]
        exact sub_nonpos.mpr (le_min hp.2 hone)
      have hWt (a : Shao.Path (rt + t)) (hat : N a = t) : Wt (suffixPart a) = W a := by
        have hu : Shao.energy (suffixPart a) = U a := by
          simpa only [U, r, hat, Nat.add_sub_cancel] using hTailEnergy a
        have hj : Jt (suffixPart a) = Jmax a := by
          have hset : Finset.Icc 0 t = Finset.range (t + 1) := by
            ext l
            simp only [Finset.mem_Icc, Finset.mem_range, Nat.zero_le, true_and]
            omega
          dsimp only [Jt, Jmax, r]
          simp only [hat, Nat.add_sub_cancel, hset, hTailSum a]
        dsimp only [Wt, W]
        rw [hu, hj]
      have hPhiAt (a : Shao.Path (rt + t)) (hat : N a = t) :
          Phi (prefixPart a, suffixPart a) = Dr a - c a := by
        calc
          _ = abcf_futureAt J Q x rt (a, Equiv.refl (Fin (rt + t))) -
              min ((Ccorr / (rt + t : ℝ)) * W a) 1 := by
            dsimp only [Phi, cost]
            rw [hmerge a, hWt a hat]
          _ = Dr a - c a := by
            simp only [Dr, r, hat, Nat.add_sub_cancel, c, g, Nat.cast_add]
      have hStopped (k : ℕ) (hk : k = rt + t - t)
          (F : Shao.Path k × Shao.Path t → ℝ) (hFm : Measurable F)
          (hFb : ∀ p, |F p| ≤ 1)
          (hFs : ∀ b : Shao.Path t, (∫ v : Shao.Path k, F (v, b)
            ∂Measure.pi (fun _ : Fin k => rho)) ≤ 0) :
          (∫ a : Shao.Path (rt + t),
            (if N a = t then F
              ((fun i : Fin k => a ⟨i.val, by omega⟩),
                (fun i : Fin t => a ⟨k + i.val, by omega⟩)) else 0) ∂P) ≤ 0 := by
        subst k
        have hh := Shao.Probability.actual_backward_stopped_suffix_integral rho (rt + t) hn4 H hH 0
          (Nat.zero_le _) t ht F hFm hFb
        rw [hh.2.2.2]
        apply integral_nonpos
        intro b
        split_ifs <;> first | exact hFs b | exact le_rfl
      have hs := hStopped rt (by omega) Phi hPhim hPhib hsection
      have heqf : (fun a : Shao.Path (rt + t) => if N a = t then Dr a - c a else 0) =
          (fun a => if N a = t then Phi (prefixPart a, suffixPart a) else 0) := by
        funext a
        by_cases hat : N a = t
        · simp only [hat, ite_true, hPhiAt a hat]
        · simp only [hat, ite_false]
      rw [heqf]
      exact hs
    have hpiece (t : ℕ) (ht : t ≤ L) :
        (∫ a, (if N a = t then Dr a - c a else 0) ∂P) ≤ 0 := by
      by_cases ht0 : t = 0
      · subst t
        have hz (a : Shao.Path n) : N a ≠ 0 := by have hh := hNpos a; omega
        simp only [hz, if_false, integral_zero, le_refl]
      · have htn : t ≤ n := ht.trans (Nat.div_le_self n 2)
        exact hpiecePositive (n - t) t (Nat.pos_of_ne_zero ht0) ht (Nat.sub_add_cancel htn)
    have hpartition (a : Shao.Path n) :
        (∑ t ∈ Finset.range (L + 1), if N a = t then Dr a - c a else 0) = Dr a - c a := by
      rw [Finset.sum_eq_single (N a)]
      · simp
      · intro t _ ht
        exact if_neg (Ne.symm ht)
      · intro hh
        have hNL := (hstat a).2.2.1
        exact False.elim (hh (Finset.mem_range.mpr (by omega)))
    have hDiff : (∫ a, Dr a - c a ∂P) ≤ 0 := by
      calc
        _ = ∫ a, ∑ t ∈ Finset.range (L + 1), (if N a = t then Dr a - c a else 0) ∂P := by
          apply integral_congr_ae
          exact ae_of_all _ fun a => (hpartition a).symm
        _ = ∑ t ∈ Finset.range (L + 1), ∫ a, (if N a = t then Dr a - c a else 0) ∂P :=
          integral_finsetSum _ (fun t _ => hslice t)
        _ ≤ 0 := Finset.sum_nonpos fun t ht =>
          hpiece t (by have hh := Finset.mem_range.mp ht; omega)
    have hDrg : (∫ a, Dr a ∂P) ≤ ∫ a, g a ∂P := by
      have hDrc : (∫ a, Dr a ∂P) ≤ ∫ a, c a ∂P := by
        rw [integral_sub hiDr hic] at hDiff
        linarith only [hDiff]
      exact hDrc.trans (integral_mono hic hig (fun a => min_le_left _ _))
    have hEW : (∫ a, W a ∂P) ≤ 1794 * H := by
      have he : (∫ a, W a ∂P) = 8 * (∫ a, Jmax a ^ 2 ∂P) +
          128 * (∫ a, U a ∂P) + 2 * H := by
        have h12 := integral_add (hiJ.const_mul 8) (hiU.const_mul 128)
        have h123 := integral_add ((hiJ.const_mul 8).add (hiU.const_mul 128))
          (integrable_const (2 * H) (μ := P))
        simp only [Pi.add_apply] at h12 h123
        change (∫ a, (8 * Jmax a ^ 2 + 128 * U a) + 2 * H ∂P) = _
        rw [h123, h12, integral_const_mul, integral_const_mul]
        simp only [integral_const, probReal_univ, one_smul]
      rw [he, hEU']
      nlinarith only [hEJ', hEN']
    have hDrPay : (∫ a, Dr a ∂P) ≤ 1794 * Ccorr * H / (n : ℝ) := by
      apply hDrg.trans
      calc
        (∫ a, g a ∂P) = (Ccorr / (n : ℝ)) * (∫ a, W a ∂P) := integral_const_mul _ _
        _ ≤ (Ccorr / (n : ℝ)) * (1794 * H) :=
          mul_le_mul_of_nonneg_left hEW (div_nonneg hCcorr.le hnR.le)
        _ = _ := by ring
    have hEm : MeasurableSet exceptional := measurableSet_lt
      ((Shao.measurable_prefixSquares L).comp
        (Measurable.of_eval (fun i : Fin n => measurable_pi_apply (Fin.rev i)))) measurable_const
    have hiE : Integrable (exceptional.indicator (fun _ => (1 : ℝ))) P :=
      (integrable_const 1).indicator hEm
    have hKappa (a : Shao.Path n) : kappa a ≤ n :=
      (energy_cutoff_data a H hH).1.1 (Equiv.refl (Fin n))
    have hKappaOff (a : Shao.Path n) (ha : a ∉ exceptional) : kappa a = r a + 1 := by
      have hh := (hstat a).2.2.2.2 ha
      have hnot : ¬ NH a ≤ 0 := by have hp := (hstat a).1; omega
      simpa only [tau, Nat.min_eq_left (hKappa a), if_neg hnot] using hh
    have hDom (a : Shao.Path n) : identityFuture a ≤
        exceptional.indicator (fun _ => (1 : ℝ)) a + Dr a := by
      by_cases he : a ∈ exceptional
      · rw [Set.indicator_of_mem he]
        exact (hIdRange a).2.trans (by linarith only [(hDrRange a).1])
      · rw [Set.indicator_of_notMem he, zero_add]
        have hrk : r a ≤ kappa a := by rw [hKappaOff a he]; omega
        change abcf_futureAt J Q x (kappa a) (a, Equiv.refl (Fin n)) ≤
          abcf_futureAt J Q x (r a) (a, Equiv.refl (Fin n))
        unfold abcf_futureAt
        apply Finset.sup'_le
        intro j hj
        by_cases hkj : kappa a ≤ j
        · have hrj := hrk.trans hkj
          have hh := Finset.le_sup'
            (fun j => if r a ≤ j then
              |sourceValue J (eventCompletionKernel J Q) a x j (Equiv.refl (Fin n)) -
                (if sourceAlive J a x n (Equiv.refl (Fin n)) then 1 else 0)| else 0) hj
          simpa only [if_pos hkj, if_pos hrj] using hh
        · rw [if_neg hkj]
          exact (hDrRange a).1
    have hTerminal : (∫ a, identityFuture a ∂P) ≤
        (1794 * Ccorr + 12) * H / (n : ℝ) := by
      calc
        _ ≤ ∫ a, exceptional.indicator (fun _ => (1 : ℝ)) a + Dr a ∂P :=
          integral_mono hIdI (hiE.add hiDr) hDom
        _ = P.real exceptional + (∫ a, Dr a ∂P) := by
          rw [integral_add hiE hiDr, integral_indicator_const 1 hEm]
          simp only [smul_eq_mul, mul_one]
        _ ≤ 12 * H / (n : ℝ) + 1794 * Ccorr * H / (n : ℝ) := add_le_add hE' hDrPay
        _ = _ := by ring
    apply hTerminal.trans
    have hRatio : H / (n : ℝ) = 4 * delta ^ 2 := by
      rw [← hBase]
      field_simp [hnR.ne']
      <;> ring
    calc
      (1794 * Ccorr + 12) * H / (n : ℝ) = (7176 * Ccorr + 48) * delta ^ 2 := by
        rw [mul_div_assoc, hRatio]
        ring
      _ ≤ Cterm * delta ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg delta)
        dsimp [Cterm]
        linarith only [hCcorr]
  have hReorderM : Measurable (randomReorder : Shao.Path n × LabelPerm n → Shao.Path n) :=
    measurable_from_prod_countable_left (fun sigma =>
      Measurable.of_eval (fun i => measurable_pi_apply (sigma i)))
  have hReorderMap : Measure.map (randomReorder : Shao.Path n × LabelPerm n → Shao.Path n)
      (revealLaw P) = P := by
    let X : Fin n → Shao.Path n → ℝ := fun i a => a i
    have hX (i : Fin n) : Measurable (X i) := measurable_pi_apply i
    have hLaw (i : Fin n) : IdentDistrib (X i) (id : ℝ → ℝ) P rho :=
      ⟨(hX i).aemeasurable, measurable_id.aemeasurable, by
        simpa only [Measure.map_id] using (measurePreserving_eval (μ := fun _ : Fin n => rho) i).map_eq⟩
    have hInd : iIndepFun X P := iIndepFun_pi (fun _ => measurable_id.aemeasurable)
    have hh := iid_randomPermutation_map_eq_pi P rho X hX hInd hLaw
    have hfun : (fun p : Shao.Path n × LabelPerm n =>
        Shao.Probability.Spitzer.reorder (Shao.Probability.samplePath X p.1) p.2) = randomReorder := by
      funext p i
      rfl
    change Measure.map (fun p : Shao.Path n × LabelPerm n =>
      Shao.Probability.Spitzer.reorder (Shao.Probability.samplePath X p.1) p.2) (revealLaw P) = P at hh
    rw [hfun] at hh
    exact hh
  have hFutureEq : (future J) = (fun p => identityFuture (randomReorder p)) := by
    funext p
    exact abcf_h0_future_reorder J Q H x p.1 p.2
  have hIntegralEq : (∫ p, future J p ∂revealLaw P) = ∫ a, identityFuture a ∂P := by
    rw [hFutureEq]
    have he := integral_map (μ := revealLaw P) (φ := randomReorder)
      hReorderM.aemeasurable hData.2.2.1.aestronglyMeasurable
    rw [hReorderMap] at he
    exact he.symm
  refine ⟨hData.2.2.1, hIdI, hIdRange, integral_nonneg (fun a => (hIdRange a).1), hIdBound,
    hData.1, hData.2.1, hData.2.2.2.2, ?_, ?_⟩
  · exact integral_nonneg (fun p => (hData.2.2.2.2 p).1)
  · rw [hIntegralEq]
    exact hIdBound

private theorem abcf_halfline_initial_all_positive :
    ∃ C : ℝ, 0 < C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (bound : ℝ), 0 < bound → (∀ᵐ z : ℝ ∂rho, |z| ≤ bound) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        ∀ (n : ℕ), 0 < n → bound ≤ Real.sqrt (n : ℝ) →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          let delta : ℝ := beta / Real.sqrt (n : ℝ)
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
          ∀ {ΩB : Type*} [MeasurableSpace ΩB]
            (Bm : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
            IsBrownianReal Bm PB → ∀ (x : ℝ), 0 < x →
              let Q : Measure BridgeNoise := bridgeLaw Bm PB
              (∀ J : MonitoredDomain, (J = .upper ∨ J = .lower) →
                let V0 : Shao.Path n → ℝ := fun a =>
                  sourceValue J (eventCompletionKernel J Q) a x 0 (Equiv.refl (Fin n))
                Integrable V0 P ∧ |(∫ a, V0 a ∂P) - (1 - 2 * Shao.standardNormalTail x)| ≤ C * delta) ∧
              ∀ s : ℝ, (s = 1 ∨ s = -1) →
                PB.real {omegaB | ∃ t : BridgeTime,
                  x ≤ s * Bm ⟨(t : ℝ), t.property.1⟩ omegaB} = 2 * Shao.standardNormalTail x := by
  classical
  obtain ⟨CS, hCS, hScalar⟩ := Shao.Probability.SourceScalarInitialBudget.finite_second_scalar_closed_cdf_budget
  refine ⟨CS + 17, by positivity, ?_⟩
  intro rho hProb bound hb hsupport hmean hsecond n hn hscale beta delta P
    ΩB hΩB Bm PB hPB hBm x hx Q
  letI : IsProbabilityMeasure rho := hProb
  letI : IsProbabilityMeasure PB := hPB
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw Bm PB hBm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hs2 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hMom (k : ℕ) : Integrable (fun z : ℝ => |z| ^ k) rho := by
    apply memLp_one_iff_integrable.mp
    apply MemLp.of_bound (by fun_prop) (bound ^ k)
    filter_upwards [hsupport] with z hz
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg z) k)] using
      pow_le_pow_left₀ (abs_nonneg z) hz k
  have h2 : Integrable (fun z : ℝ => z ^ 2) rho := by simpa only [sq_abs] using hMom 2
  have hd0 : 0 ≤ delta := div_nonneg (integral_nonneg fun z => pow_nonneg (abs_nonneg z) 3) hs.le
  have hR0 : Shao.truncationBudget
      (Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) rho) n 0 = delta := by
    have hm : Measurable (fun z : ℝ => z / Real.sqrt (n : ℝ)) := by fun_prop
    unfold Shao.truncationBudget
    simp only [add_zero, one_mul]
    rw [integral_map hm.aemeasurable (Shao.continuous_truncationF.measurable.aestronglyMeasurable)]
    have heq : (fun z : ℝ => Shao.truncationF (z / Real.sqrt (n : ℝ))) =ᵐ[rho]
        (fun z : ℝ => (1 / (Real.sqrt (n : ℝ)) ^ 3) * |z| ^ 3) := by
      filter_upwards [hsupport] with z hz
      have hsmall : |z / Real.sqrt (n : ℝ)| ≤ 1 := by
        rw [abs_div, abs_of_pos hs]
        exact (div_le_one hs).mpr (hz.trans hscale)
      rw [Shao.truncationF_of_abs_le_one _ hsmall, abs_div, abs_of_pos hs]
      rw [div_pow]
      ring
    rw [integral_congr_ae heq, integral_const_mul]
    change (n : ℝ) * ((1 / (Real.sqrt (n : ℝ)) ^ 3) * beta) = beta / Real.sqrt (n : ℝ)
    calc
      _ = (Real.sqrt (n : ℝ)) ^ 2 * ((1 / (Real.sqrt (n : ℝ)) ^ 3) * beta) := by rw [hs2]
      _ = _ := by field_simp [hs.ne'] <;> ring
  let W : Shao.Path n → ℝ := Shao.C1.normalizedEndpoint
  have hWm : Measurable W := Shao.C1.measurable_normalizedEndpoint
  let endpointLaw : Measure ℝ := Measure.map W P
  letI : IsProbabilityMeasure endpointLaw :=
    (Measure.isProbabilityMeasure_map_iff hWm.aemeasurable).mpr inferInstance
  have hCDF (v : ℝ) : |endpointLaw.real (Set.Iic v) - (gaussianReal 0 1).real (Set.Iic v)| ≤ CS * delta := by
    have hh := hScalar rho n hn h2 hmean (by rw [hsecond]; norm_num) v
    simp only [hsecond, Real.sqrt_one, one_mul, hR0] at hh
    rw [Measure.real_def, Measure.map_apply hWm measurableSet_Iic]
    exact hh
  have hzero : P.real {a : Shao.Path n | Shao.energy a = 0} ≤ 16 * delta := by
    let X : Fin n → Shao.Path n → ℝ := fun i a => a i
    have hInd : iIndepFun X P := iIndepFun_pi (fun _ => measurable_id.aemeasurable)
    have hLaw (i : Fin n) : IdentDistrib (X i) (id : ℝ → ℝ) P rho :=
      ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, by
        simpa only [Measure.map_id] using (measurePreserving_eval (μ := fun _ : Fin n => rho) i).map_eq⟩
    have hz := Shao.Probability.SourceOriginalZeroEnergyBudget.original_iid_zero_energy_budget P rho n hn X
      (fun i => (measurable_pi_apply i).aemeasurable) hInd hLaw h2 (by rw [hsecond]; norm_num)
    simpa only [hsecond, mul_one, hR0, X, Shao.energy] using hz
  let g : ℝ → ℝ := fun w => if w < x then 1 - Real.exp (-2 * x * (x - w)) else 0
  have hg0 (w : ℝ) : 0 ≤ g w := by
    by_cases hw : w < x
    · have he : Real.exp (-2 * x * (x - w)) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have hp := mul_nonneg hx.le (sub_nonneg.mpr hw.le)
        nlinarith only [hp])
      dsimp only [g]
      rw [if_pos hw]
      linarith only [he]
    · simp only [g, if_neg hw, le_refl]
  have hg1 (w : ℝ) : g w ≤ 1 := by
    dsimp only [g]
    split_ifs <;> first | linarith [Real.exp_pos (-2 * x * (x - w))] | norm_num
  have hg : Antitone g := by
    intro u v huv
    by_cases hv : v < x
    · have hu : u < x := huv.trans_lt hv
      have he : Real.exp (-2 * x * (x - u)) ≤ Real.exp (-2 * x * (x - v)) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [mul_nonneg hx.le (sub_nonneg.mpr huv)]
      simp only [g, if_pos hu, if_pos hv]
      linarith only [he]
    · simpa only [g, if_neg hv] using hg0 u
  have hgi (mu : Measure ℝ) [IsProbabilityMeasure mu] : Integrable g mu := by
    apply Integrable.of_bound hg.measurable.aestronglyMeasurable 1
    exact ae_of_all _ fun w => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hg0 w)] using hg1 w
  have hGaussianIntegral : (∫ w : ℝ, g w ∂gaussianReal 0 1) = 1 - 2 * Shao.standardNormalTail x := by
    let phi : ℝ → ℝ := Shao.standardNormalDensity
    have hphi : Integrable phi := integrable_gaussianPDFReal 0 1
    have hform (w : ℝ) : phi w = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-w ^ 2 / 2) := by
      simp [phi, Shao.standardNormalDensity, gaussianPDFReal]
    have hAbsorb (w : ℝ) : phi w * Real.exp (-2 * x * (x - w)) = phi (w - 2 * x) := by
      rw [hform w, hform (w - 2 * x)]
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    have hShiftI : Integrable (fun w : ℝ => phi (w - 2 * x)) := by
      have he : (fun w : ℝ => phi (w - 2 * x)) = gaussianPDFReal (2 * x) 1 := by
        funext w
        simp [phi, Shao.standardNormalDensity, gaussianPDFReal]
      rw [he]
      exact integrable_gaussianPDFReal (2 * x) 1
    have hPoint (w : ℝ) : phi w * g w = (Set.Iio x).indicator phi w -
        (Set.Iio x).indicator (fun w : ℝ => phi (w - 2 * x)) w := by
      by_cases hw : w < x
      · rw [show g w = 1 - Real.exp (-2 * x * (x - w)) by simp only [g, if_pos hw],
          Set.indicator_of_mem hw, Set.indicator_of_mem hw]
        calc
          _ = phi w - phi w * Real.exp (-2 * x * (x - w)) := by ring
          _ = _ := by rw [hAbsorb w]
      · have hwI : w ∉ Set.Iio x := hw
        simp only [g, if_neg hw, Set.indicator_of_notMem hwI, mul_zero, sub_self]
    have hCut (v : ℝ) : (∫ w : ℝ, (Set.Iio v).indicator phi w) = 1 - Shao.standardNormalTail v := by
      have hDensity : (gaussianReal 0 1).real (Set.Iio v) = ∫ w : ℝ in Set.Iio v, phi w := by
        rw [Measure.real_def, gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
          ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg 0 1))]
        rfl
      have hc := measureReal_compl (μ := gaussianReal 0 1) (s := Set.Ici v) measurableSet_Ici
      simp only [Set.compl_Ici, probReal_univ] at hc
      have hRep : (gaussianReal 0 1).real (Set.Ici v) = Shao.standardNormalTail v :=
        (Shao.standardNormalTail_representation v).1.symm
      rw [hRep] at hc
      rw [integral_indicator measurableSet_Iio]
      exact hDensity.symm.trans hc
    have hShift : (∫ w : ℝ, (Set.Iio x).indicator (fun w : ℝ => phi (w - 2 * x)) w) =
        ∫ w : ℝ, (Set.Iio (-x)).indicator phi w := by
      calc
        _ = ∫ w : ℝ, (Set.Iio (-x)).indicator phi (w + (-2 * x)) := by
          apply integral_congr_ae
          exact ae_of_all _ fun w => by
            change (Set.Iio x).indicator (fun w : ℝ => phi (w - 2 * x)) w =
              (Set.Iio (-x)).indicator phi (w + (-2 * x))
            by_cases hw : w < x
            · have hv : w + (-2 * x) ∈ Set.Iio (-x) := by change w + (-2 * x) < -x; linarith only [hw]
              have hwI : w ∈ Set.Iio x := hw
              rw [Set.indicator_of_mem hwI, Set.indicator_of_mem hv]
              congr 1
              ring
            · have hv : w + (-2 * x) ∉ Set.Iio (-x) := by change ¬ w + (-2 * x) < -x; linarith only [hw]
              have hwI : w ∉ Set.Iio x := hw
              rw [Set.indicator_of_notMem hwI, Set.indicator_of_notMem hv]
        _ = _ := integral_add_right_eq_self ((Set.Iio (-x)).indicator phi) (-2 * x)
    rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
    change (∫ w : ℝ, phi w * g w) = _
    simp_rw [hPoint]
    rw [integral_sub (hphi.indicator measurableSet_Iio) (hShiftI.indicator measurableSet_Iio),
      hShift, hCut x, hCut (-x), Shao.standardNormalTail_basic.2.2.2 x]
    ring
  have hSignedError (s : ℝ) (hsign : s = 1 ∨ s = -1) :
      |(∫ a, g (s * W a) ∂P) - (1 - 2 * Shao.standardNormalTail x)| ≤ CS * delta := by
    have hUpper := Shao.C2.EndpointCDFTransfer.antitone_unit_expectation_error endpointLaw (gaussianReal 0 1)
      (CS * delta) (mul_nonneg hCS.le hd0) hCDF g hg hg0 hg1
    rcases hsign with rfl | rfl
    · have he : (∫ w : ℝ, g w ∂endpointLaw) = ∫ a, g (W a) ∂P :=
        integral_map hWm.aemeasurable hg.measurable.aestronglyMeasurable
      rw [he, hGaussianIntegral] at hUpper
      simpa only [one_mul] using hUpper
    · let f : ℝ → ℝ := fun w => 1 - g (-w)
      have hf : Antitone f := by
        intro u v huv
        have hh := hg (neg_le_neg huv)
        dsimp only [f]
        linarith only [hh]
      have hf0 (w : ℝ) : 0 ≤ f w := sub_nonneg.mpr (hg1 (-w))
      have hf1 (w : ℝ) : f w ≤ 1 := by dsimp [f]; linarith only [hg0 (-w)]
      have herr := Shao.C2.EndpointCDFTransfer.antitone_unit_expectation_error endpointLaw (gaussianReal 0 1)
        (CS * delta) (mul_nonneg hCS.le hd0) hCDF f hf hf0 hf1
      have hNegI (mu : Measure ℝ) [IsProbabilityMeasure mu] : Integrable (fun w => g (-w)) mu := by
        apply Integrable.of_bound (hg.measurable.comp measurable_neg).aestronglyMeasurable 1
        exact ae_of_all _ fun w => by
          change |g (-w)| ≤ 1
          rw [abs_of_nonneg (hg0 (-w))]
          exact hg1 (-w)
      have hNegNormal : (∫ w : ℝ, g (-w) ∂gaussianReal 0 1) = ∫ w : ℝ, g w ∂gaussianReal 0 1 := by
        have he := integral_map (μ := gaussianReal 0 1) (φ := fun w : ℝ => -w)
          measurable_neg.aemeasurable hg.measurable.aestronglyMeasurable
        rw [show Measure.map (fun w : ℝ => -w) (gaussianReal 0 1) = gaussianReal 0 1 by
          simpa only [neg_zero] using gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)] at he
        exact he.symm
      change |(∫ w, (1 - g (-w)) ∂endpointLaw) - ∫ w, (1 - g (-w)) ∂gaussianReal 0 1| ≤ _ at herr
      rw [integral_sub (integrable_const 1) (hNegI endpointLaw),
        integral_sub (integrable_const 1) (hNegI (gaussianReal 0 1))] at herr
      simp only [integral_const, probReal_univ, one_smul] at herr
      have he : (∫ w : ℝ, g (-w) ∂endpointLaw) = ∫ a, g (-(W a)) ∂P :=
        integral_map hWm.aemeasurable (hg.measurable.comp measurable_neg).aestronglyMeasurable
      have herr' : |(∫ w, g (-w) ∂endpointLaw) - ∫ w, g w ∂gaussianReal 0 1| ≤ CS * delta := by
        rw [show (1 - (∫ w, g (-w) ∂endpointLaw)) -
          (1 - (∫ w, g (-w) ∂gaussianReal 0 1)) =
          -((∫ w, g (-w) ∂endpointLaw) - ∫ w, g (-w) ∂gaussianReal 0 1) by ring,
          abs_neg, hNegNormal] at herr
        exact herr
      rw [he, hGaussianIntegral] at herr'
      simpa only [neg_one_mul] using herr'
  have hProfileAtZero (s : ℝ) (hsign : s = 1 ∨ s = -1) (J : MonitoredDomain)
      (hJs : (J = .upper ∧ s = 1) ∨ (J = .lower ∧ s = -1)) (a : Shao.Path n) :
      sourceValue J (eventCompletionKernel J Q) a x 0 (Equiv.refl (Fin n)) =
        if 0 < Shao.energy a then g (s * W a) else 0 := by
    by_cases hE : 0 < Shao.energy a
    swap
    · have hdead : ¬ sourceAlive J a x 0 (Equiv.refl (Fin n)) := fun hh => hE hh.1
      simp only [sourceValue, if_neg hdead, if_neg hE]
    let q : ℝ := Real.sqrt (Shao.energy a)
    have hq : 0 < q := Real.sqrt_pos.mpr hE
    have hq2 : q ^ 2 = Shao.energy a := Real.sq_sqrt hE.le
    have hw : 0 < x * q := mul_pos hx hq
    have hW : W a = Shao.prefixSum a n / q := Shao.C1.normalizedEndpoint_of_energy_pos a hE
    have hSigned : s * W a < x ↔ s * Shao.prefixSum a n < x * q := by
      rw [hW, ← mul_div_assoc]
      exact div_lt_iff₀ hq
    have hAlive : sourceAlive J a x 0 (Equiv.refl (Fin n)) ↔ s * W a < x := by
      rw [hSigned]
      rcases hJs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · constructor
        · intro hh
          simpa only [Interior, one_mul, actualWall, q] using hh.2.1
        · intro hh
          refine ⟨hE, ?_, ?_⟩
          · simpa only [Interior, actualWall, q, one_mul] using hh
          · intro k hk
            have hk0 : k = 0 := by omega
            subst k
            simpa only [Interior, actualWall, Shao.prefixSum_zero, q] using hw
      · constructor
        · intro hh
          have hend := hh.2.1
          change -actualWall a x < Shao.prefixSum a n at hend
          simp only [neg_one_mul]
          dsimp only [actualWall] at hend
          linarith only [hend]
        · intro hh
          simp only [neg_one_mul] at hh
          refine ⟨hE, ?_, ?_⟩
          · change -(x * Real.sqrt (Shao.energy a)) < Shao.prefixSum a n
            linarith only [hh]
          · intro k hk
            have hk0 : k = 0 := by omega
            subst k
            change -(x * Real.sqrt (Shao.energy a)) < Shao.prefixSum (Shao.Probability.Spitzer.reorder a _) 0
            rw [Shao.prefixSum_zero]
            linarith only [hw]
    by_cases he : s * W a < x
    · have ha := hAlive.mpr he
      have hend := hSigned.mp he
      have hExp : -2 * x * (x - s * W a) =
          -2 * (x * q) * (x * q - s * Shao.prefixSum a n) / Shao.energy a := by
        rw [hW, ← hq2]
        field_simp [hq.ne']
        <;> ring
      rw [if_pos hE]
      have hGate : 0 < actualWall a x ∧ Interior J (actualWall a x) 0 ∧
          Interior J (actualWall a x) (Shao.prefixSum a n) := by
        refine ⟨hw, ?_, ha.2.1⟩
        simpa only [Shao.prefixSum_zero] using ha.2.2 0 le_rfl
      simp only [sourceValue, if_pos ha, Shao.prefixSum_zero, remainingEnergy,
        Shao.prefixSquares_zero, sub_zero, completionExt, if_pos hGate, if_pos hE]
      rw [show g (s * W a) = 1 - Real.exp (-2 * x * (x - s * W a)) by simp only [g, if_pos he], hExp]
      rcases hJs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa only [eventCompletionKernel, actualWall, q, sub_zero, one_mul] using
          Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula Bm PB hBm
            (x * q) 0 (Shao.energy a) (Shao.prefixSum a n) hE hw (by simpa only [one_mul] using hend)
      · have hend' : -(x * q) < Shao.prefixSum a n := by
          simp only [neg_one_mul] at hend
          linarith only [hend]
        simpa only [eventCompletionKernel, actualWall, q, add_zero, neg_one_mul, sub_neg_eq_add] using
          Shao.C2.BridgeLowerIdentification.bridge_lower_formula Bm PB hBm
            (x * q) 0 (Shao.energy a) (Shao.prefixSum a n) hE (by linarith only [hw]) hend'
    · have ha : ¬ sourceAlive J a x 0 (Equiv.refl (Fin n)) := by simpa only [hAlive] using he
      simp only [sourceValue, if_neg ha, if_pos hE, g, if_neg he]
  constructor
  · intro J hJ
    obtain ⟨s, hs, hJs⟩ : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
        ((J = .upper ∧ s = 1) ∨ (J = .lower ∧ s = -1)) := by
      rcases hJ with rfl | rfl
      · exact ⟨1, Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨-1, Or.inr rfl, Or.inr ⟨rfl, rfl⟩⟩
    intro V0
    let profile : Shao.Path n → ℝ := fun a => g (s * W a)
    have hPm : Measurable profile := hg.measurable.comp (measurable_const.mul hWm)
    have hPi : Integrable profile P := by
      apply Integrable.of_bound hPm.aestronglyMeasurable 1
      exact ae_of_all _ fun a => by
        change |g (s * W a)| ≤ 1
        rw [abs_of_nonneg (hg0 _)]
        exact hg1 _
    have hVeq (a : Shao.Path n) : V0 a = if 0 < Shao.energy a then profile a else 0 :=
      hProfileAtZero s hs J hJs a
    have hVm : Measurable V0 := by
      have he : V0 = (fun a : Shao.Path n => if 0 < Shao.energy a then profile a else 0) := funext hVeq
      rw [he]
      exact Measurable.ite (measurableSet_lt measurable_const Shao.measurable_energy) hPm measurable_const
    have hVi : Integrable V0 P := by
      apply Integrable.of_bound hVm.aestronglyMeasurable 1
      exact ae_of_all _ fun a => by
        rw [hVeq a]
        split_ifs
        · change |g (s * W a)| ≤ 1
          rw [abs_of_nonneg (hg0 _)]
          exact hg1 _
        · norm_num
    have hZeroM : MeasurableSet {a : Shao.Path n | Shao.energy a = 0} :=
      measurableSet_eq_fun Shao.measurable_energy measurable_const
    have hDiff : |(∫ a, V0 a ∂P) - ∫ a, profile a ∂P| ≤ 16 * delta := by
      rw [← integral_sub hVi hPi, ← Real.norm_eq_abs]
      calc
        _ ≤ ∫ a, ({a : Shao.Path n | Shao.energy a = 0}).indicator (fun _ => (1 : ℝ)) a ∂P := by
          apply norm_integral_le_of_norm_le ((integrable_const 1).indicator hZeroM)
          exact ae_of_all _ fun a => by
            rw [hVeq a]
            by_cases he : 0 < Shao.energy a
            · have ha : a ∉ {a : Shao.Path n | Shao.energy a = 0} := ne_of_gt he
              simp only [if_pos he, sub_self, norm_zero, Set.indicator_of_notMem ha, le_refl]
            · have hz : Shao.energy a = 0 := le_antisymm (le_of_not_gt he) (Shao.energy_nonneg a)
              have ha : a ∈ {a : Shao.Path n | Shao.energy a = 0} := hz
              rw [if_neg he, Set.indicator_of_mem ha, zero_sub, norm_neg,
                Real.norm_eq_abs, abs_of_nonneg (hg0 _)]
              exact hg1 _
        _ = P.real {a : Shao.Path n | Shao.energy a = 0} := by
          rw [integral_indicator_const 1 hZeroM]
          simp only [smul_eq_mul, mul_one]
        _ ≤ _ := hzero
    refine ⟨hVi, ?_⟩
    have he := hSignedError s hs
    change |(∫ a, profile a ∂P) - (1 - 2 * Shao.standardNormalTail x)| ≤ CS * delta at he
    calc
      _ ≤ |(∫ a, V0 a ∂P) - ∫ a, profile a ∂P| +
          |(∫ a, profile a ∂P) - (1 - 2 * Shao.standardNormalTail x)| := abs_sub_le _ _ _
      _ ≤ 16 * delta + CS * delta := add_le_add hDiff he
      _ ≤ (CS + 17) * delta := by nlinarith only [hd0]
  · have hSingle (Y : ℝ≥0 → ΩB → ℝ) (hY : IsBrownianReal Y PB) :
        PB.real {omegaB | ∃ t : BridgeTime, x ≤ Y ⟨(t : ℝ), t.property.1⟩ omegaB} =
          2 * Shao.standardNormalTail x := by
      let QY : Measure BridgeNoise := bridgeLaw Y PB
      letI : IsProbabilityMeasure QY := isProbabilityMeasure_bridgeLaw Y PB hY
      have hKernel (w : ℝ) : upperCompletion QY x 0 1 w = g w := by
        by_cases hw : w < x
        · simpa only [QY, g, if_pos hw, sub_zero, div_one] using
            Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula Y PB hY x 0 1 w (by norm_num) hx hw
        · have hEmpty : strictUpper x 0 1 w = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro b hb
            have he := hb 1
            rw [(bridgePath_endpoints 0 1 w b).2] at he
            exact hw he
          simp only [upperCompletion, hEmpty, measureReal_empty, g, if_neg hw]
      let S : Set ΩB := {omegaB | ∀ t : BridgeTime, Y ⟨(t : ℝ), t.property.1⟩ omegaB < x}
      have hSurvival : PB.real S = 1 - 2 * Shao.standardNormalTail x := by
        have hj := Shao.C2.BridgeHalfLineJointLaw.brownian_upper_joint Y PB hY x 0 1 x
        have hLeft : {omegaB | (∀ t : BridgeTime,
            0 + Real.sqrt 1 * Y ⟨(t : ℝ), t.property.1⟩ omegaB < x) ∧
            0 + Real.sqrt 1 * Y 1 omegaB ≤ x} = S := by
          ext omegaB
          simp only [Real.sqrt_one, one_mul, zero_add, Set.mem_setOf_eq, S]
          constructor
          · exact And.left
          · intro hh
            exact ⟨hh, (hh 1).le⟩
        rw [hLeft] at hj
        have hRight (w : ℝ) : (if w ≤ x then upperCompletion QY x 0 1 w else 0) = g w := by
          rw [hKernel w]
          by_cases hw : w ≤ x
          · exact if_pos hw
          · simp only [if_neg hw, g, if_neg (by linarith only [hw] : ¬ w < x)]
        simp only [Real.sqrt_one, one_mul, zero_add] at hj
        have hInt : (∫ w : ℝ, (if w ≤ x then upperCompletion QY x 0 1 w else 0)
            ∂gaussianReal 0 1) = ∫ w : ℝ, g w ∂gaussianReal 0 1 :=
          integral_congr_ae (ae_of_all _ hRight)
        exact hj.trans (hInt.trans hGaussianIntegral)
      have hNull : NullMeasurableSet {omegaB | ∃ t : BridgeTime,
          x ≤ Y ⟨(t : ℝ), t.property.1⟩ omegaB} PB := by
        let K : Set (ContinuousMap BridgeTime ℝ) := {f | ∃ t : BridgeTime, x ≤ f t}
        have ho : IsOpen {f : ContinuousMap BridgeTime ℝ | ∀ t : BridgeTime, f t < x} := by
          simpa [Set.MapsTo] using
            (ContinuousMap.isOpen_setOfPred_mapsTo (X := BridgeTime) isCompact_univ (isOpen_Iio (a := x)))
        have hK : MeasurableSet K := by
          have he : K = {f : ContinuousMap BridgeTime ℝ | ∀ t : BridgeTime, f t < x}ᶜ := by
            ext f
            simp only [K, Set.mem_setOf_eq, Set.mem_compl_iff, not_forall, not_lt]
          rw [he]
          exact ho.measurableSet.compl
        have hm := (Shao.OQ4.PolygonalBrownianWeakLimit.aemeasurable_brownianUnitPath Y 1 PB hY).nullMeasurableSet_preimage hK
        apply hm.congr
        filter_upwards [Shao.OQ4.PolygonalBrownianWeakLimit.ae_brownianUnitPath_eq Y 1 PB hY] with omegaB homegaB
        apply propext
        change (∃ t : BridgeTime, x ≤ Shao.OQ4.PolygonalBrownianWeakLimit.brownianUnitPath Y 1 omegaB t) ↔ _
        have ht (t : BridgeTime) : Shao.OQ4.PolygonalBrownianWeakLimit.brownianUnitPath Y 1 omegaB t =
            Y ⟨(t : ℝ), t.property.1⟩ omegaB := by
          have hh := homegaB t
          change Shao.OQ4.PolygonalBrownianWeakLimit.brownianUnitPath Y 1 omegaB t =
            Y (1 * ⟨(t : ℝ), t.property.1⟩) omegaB at hh
          exact hh.trans (congrArg (fun q : ℝ≥0 => Y q omegaB) (_root_.one_mul _))
        simp only [ht]
      have hComplement : {omegaB | ∃ t : BridgeTime,
          x ≤ Y ⟨(t : ℝ), t.property.1⟩ omegaB}ᶜ = S := by
        ext omegaB
        simp only [S, Set.mem_compl_iff, Set.mem_setOf_eq, not_exists, not_le]
      have hp := measureReal_add_measureReal_compl₀ hNull
      rw [hComplement, probReal_univ, hSurvival] at hp
      linarith only [hp]
    intro s hs
    rcases hs with rfl | rfl
    · simpa only [one_mul] using hSingle Bm hBm
    · have hh := hSingle (-Bm) hBm.neg
      calc
        PB.real {omegaB | ∃ t : BridgeTime, x ≤ (-1 : ℝ) * Bm ⟨(t : ℝ), t.property.1⟩ omegaB} =
            PB.real {omegaB | ∃ t : BridgeTime, x ≤ (-Bm) ⟨(t : ℝ), t.property.1⟩ omegaB} := by
          congr 1
          ext omegaB
          constructor
          · rintro ⟨t, ht⟩
            refine ⟨t, ?_⟩
            change x ≤ -(Bm ⟨(t : ℝ), t.property.1⟩ omegaB)
            simpa only [neg_one_mul] using ht
          · rintro ⟨t, ht⟩
            refine ⟨t, ?_⟩
            change x ≤ -(Bm ⟨(t : ℝ), t.property.1⟩ omegaB) at ht
            simpa only [neg_one_mul] using ht
        _ = 2 * Shao.standardNormalTail x := hh

private theorem abcf_legal_c1_fixed_segment :
    ∃ rhoStar epsilonF C1 K1 : ℝ,
      0 < rhoStar ∧ rhoStar ≤ 1 / 16 ∧
      epsilonF = min (rhoStar / 27) (1 / 8) ∧ 0 < epsilonF ∧ 0 < C1 ∧ 0 < K1 ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (bound : ℝ), 0 < bound → (∀ᵐ z : ℝ ∂rho, |z| ≤ bound) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        ∀ (n : ℕ) (hn : 0 < n) (x : ℝ), (1 / 2 : ℝ) ≤ x → x ≤ 16 →
          bound ≤ Real.sqrt (n : ℝ) / (100 * x) →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          let delta : ℝ := beta / Real.sqrt (n : ℝ)
          delta * x ^ 3 ≤ epsilonF →
          let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) rho
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
          Shao.truncationBudget normalizedLaw n x = delta * (1 + x) ^ 3 ∧
          Shao.truncationBudget normalizedLaw n x ≤ rhoStar ∧ delta ≤ 1 ∧
          ∀ s : ℝ, (s = 1 ∨ s = -1) →
            let U : Set (Shao.Path n) := {a | x * Real.sqrt (Shao.energy a) ≤ Shao.upperMax (s • a) hn}
            |P.real U - 2 * Shao.standardNormalTail x| ≤ C1 * delta * (1 + x) ^ 3 * Shao.standardNormalTail x ∧
            |P.real U - 2 * Shao.standardNormalTail x| ≤ K1 * delta := by
  classical
  obtain ⟨rhoStar, C1, hrho, hrho16, hC1, hOriginal⟩ :=
    Shao.Probability.original_one_sided_relative_error_iid
  let epsilonF : ℝ := min (rhoStar / 27) (1 / 8)
  let K1 : ℝ := C1 * 17 ^ 3
  have heps : 0 < epsilonF := lt_min (by positivity) (by norm_num)
  have hK1 : 0 < K1 := by dsimp [K1]; positivity
  refine ⟨rhoStar, epsilonF, C1, K1, hrho, hrho16, rfl, heps, hC1, hK1, ?_⟩
  intro rho hProb bound hb hsupport hmean hsecond n hn x hx hx16 hscale beta delta hsmall normalizedLaw P
  letI : IsProbabilityMeasure rho := hProb
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  rcases abcf_bounded_own_budget_identities rho bound hb hsupport hmean hsecond n hn x hx hscale with
    ⟨h1, h2, h3, hbound1, hbeta, hdelta, hH, hnlarge, hR0, hRx, hcut, hPrefixBudget⟩
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hOnePlus : 1 + x ≤ 3 * x := by linarith only [hx]
  have hRxBound : Shao.truncationBudget normalizedLaw n x ≤ rhoStar := by
    rw [hRx]
    calc
      delta * (1 + x) ^ 3 ≤ delta * (3 * x) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hOnePlus 3) hdelta.le
      _ = 27 * (delta * x ^ 3) := by ring
      _ ≤ 27 * epsilonF := mul_le_mul_of_nonneg_left hsmall (by norm_num)
      _ ≤ rhoStar := by
        have hh : epsilonF ≤ rhoStar / 27 := min_le_left _ _
        linarith only [hh]
  have hdelta1 : delta ≤ 1 := by
    have hx3 : (1 / 8 : ℝ) ≤ x ^ 3 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hx 3
      norm_num at hh
      exact hh
    have hh := mul_le_mul_of_nonneg_left hx3 hdelta.le
    have heps8 : epsilonF ≤ 1 / 8 := min_le_right _ _
    nlinarith only [hh, hsmall, heps8]
  refine ⟨hRx, hRxBound, hdelta1, ?_⟩
  intro s hs U
  let X : Fin n → Shao.Path n → ℝ := fun i a => a i
  have hX (i : Fin n) : Measurable (X i) := measurable_pi_apply i
  have hLaw (i : Fin n) : IdentDistrib (X i) (id : ℝ → ℝ) P rho :=
    ⟨(hX i).aemeasurable, measurable_id.aemeasurable, by
      simpa only [Measure.map_id] using (measurePreserving_eval (μ := fun _ : Fin n => rho) i).map_eq⟩
  have hInd : iIndepFun X P := iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hIdent (i : Fin n) : IdentDistrib (X i) (X ⟨0, hn⟩) P P :=
    (hLaw i).trans (hLaw ⟨0, hn⟩).symm
  have hY2 : Integrable (fun a : Shao.Path n => X ⟨0, hn⟩ a ^ 2) P :=
    ((hLaw ⟨0, hn⟩).comp (by fun_prop : Measurable (fun z : ℝ => z ^ 2))).integrable_iff.mpr h2
  have hYmean : (∫ a : Shao.Path n, X ⟨0, hn⟩ a ∂P) = 0 :=
    (hLaw ⟨0, hn⟩).integral_eq.trans hmean
  have hYsecond : (∫ a : Shao.Path n, X ⟨0, hn⟩ a ^ 2 ∂P) = 1 :=
    ((hLaw ⟨0, hn⟩).comp (by fun_prop : Measurable (fun z : ℝ => z ^ 2))).integral_eq.trans hsecond
  have hY3 : Integrable (fun a : Shao.Path n => Real.rpow |X ⟨0, hn⟩ a| (3 : ℝ)) P := by
    have hi := ((hLaw ⟨0, hn⟩).comp
      (by fun_prop : Measurable (fun z : ℝ => |z| ^ 3))).integrable_iff.mpr h3
    change Integrable (fun a : Shao.Path n => |X ⟨0, hn⟩ a| ^ (3 : ℕ)) P at hi
    have hpow : (fun a : Shao.Path n => Real.rpow |X ⟨0, hn⟩ a| (3 : ℝ)) =
        (fun a : Shao.Path n => |X ⟨0, hn⟩ a| ^ (3 : ℕ)) := by
      funext a
      exact Real.rpow_natCast _ 3
    rw [hpow]
    exact hi
  have hMapX : Measure.map (X ⟨0, hn⟩) P = rho := by
    simpa only [Measure.map_id] using (hLaw ⟨0, hn⟩).map_eq
  have hNorm : Measure.map (fun a : Shao.Path n => X ⟨0, hn⟩ a / Real.sqrt (n : ℝ)) P = normalizedLaw := by
    calc
      _ = Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) (Measure.map (X ⟨0, hn⟩) P) :=
        (Measure.map_map (by fun_prop) (hX ⟨0, hn⟩)).symm
      _ = _ := by rw [hMapX]
  have hCall := hOriginal 3 (by norm_num) (by norm_num) P n hn X hX hInd hIdent hY2 hYmean
    (by rw [hYsecond]; norm_num) hY3
  dsimp only at hCall
  rw [hYsecond] at hCall
  simp only [Real.sqrt_one, one_mul] at hCall
  rw [hNorm] at hCall
  have hRel := hCall x hx0 (Or.inr hRxBound) s hs
  change |P.real U / Shao.standardNormalTail x - 2| ≤ C1 * Shao.truncationBudget normalizedLaw n x at hRel
  have htail : 0 < Shao.standardNormalTail x := (Shao.standardNormalTail_basic.2.2.1 x).1
  have htail1 : Shao.standardNormalTail x ≤ 1 := (Shao.standardNormalTail_basic.2.2.1 x).2.le
  have hAbs : |P.real U - 2 * Shao.standardNormalTail x| ≤
      C1 * delta * (1 + x) ^ 3 * Shao.standardNormalTail x := by
    have he : (P.real U / Shao.standardNormalTail x - 2) * Shao.standardNormalTail x =
        P.real U - 2 * Shao.standardNormalTail x := by
      field_simp [htail.ne']
    calc
      _ = |P.real U / Shao.standardNormalTail x - 2| * Shao.standardNormalTail x := by
        rw [← he, abs_mul, abs_of_pos htail]
      _ ≤ (C1 * Shao.truncationBudget normalizedLaw n x) * Shao.standardNormalTail x :=
        mul_le_mul_of_nonneg_right hRel htail.le
      _ = _ := by rw [hRx]; ring
  refine ⟨hAbs, hAbs.trans ?_⟩
  have h17 : (1 + x) ^ 3 ≤ (17 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hx16]) 3
  calc
    C1 * delta * (1 + x) ^ 3 * Shao.standardNormalTail x ≤ C1 * delta * 17 ^ 3 * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left h17 (mul_nonneg hC1.le hdelta.le)) htail1
        htail.le (by positivity)
    _ = K1 * delta := by dsimp [K1]; ring

private theorem abcf_fixed_absolute_comparison :
    ∃ epsilonF CA : ℝ, 0 < epsilonF ∧ epsilonF ≤ 1 / 8 ∧ 0 < CA ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (bound : ℝ), 0 < bound → (∀ᵐ z : ℝ ∂rho, |z| ≤ bound) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        ∀ (n : ℕ) (hn : 0 < n) (x : ℝ), (1 / 2 : ℝ) ≤ x → x ≤ 16 →
          bound ≤ Real.sqrt (n : ℝ) / (100 * x) →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          let delta : ℝ := beta / Real.sqrt (n : ℝ)
          delta * x ^ 3 ≤ epsilonF →
          ∀ {ΩB : Type*} [MeasurableSpace ΩB]
            (Bm : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
            IsBrownianReal Bm PB →
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
            |P.real {a | x * Real.sqrt (Shao.energy a) ≤ Shao.absMax a hn} -
              PB.real {omegaB | ∃ t : BridgeTime,
                x ≤ |Bm ⟨(t : ℝ), t.property.1⟩ omegaB|}| ≤ CA * delta := by
  classical
  obtain ⟨CB, hCB, hBill⟩ := iid_actual_all_level_retained_negative_budget
  obtain ⟨CE, hCE, hTerminal⟩ := iid_actual_all_level_h0_terminal_budget
  obtain ⟨CS, hCS, hHalfInitial⟩ := abcf_halfline_initial_all_positive
  obtain ⟨rhoStar, epsilonF, C1, K1, hrho, hrho16, hepsEq, heps, hC1, hK1, hC1Segment⟩ :=
    abcf_legal_c1_fixed_segment
  obtain ⟨CI, hCI, hIntervalInitial⟩ :=
    Shao.Probability.SourceActualIntervalInitialCDF.original_iid_actual_interval_initial_cdf_budget
  let KG : ℝ := K1 + CS
  let CA : ℝ := 3 * CB + 3 * CE + 2 * KG + CI + 1
  have hKG : 0 < KG := add_pos hK1 hCS
  refine ⟨epsilonF, CA, heps, ?_, by dsimp [CA]; positivity, ?_⟩
  · rw [hepsEq]
    exact min_le_right _ _
  intro rho hProb bound hb hsupport hmean hsecond n hn x hx hx16 hscale beta delta hsmall
    ΩB hΩB Bm PB hPB hBm P
  letI : IsProbabilityMeasure rho := hProb
  letI : IsProbabilityMeasure PB := hPB
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  let Q : Measure BridgeNoise := bridgeLaw Bm PB
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw Bm PB hBm
  letI : IsProbabilityMeasure (revealLaw P) := by unfold revealLaw; infer_instance
  rcases abcf_bounded_own_budget_identities rho bound hb hsupport hmean hsecond n hn x hx hscale with
    ⟨h1, h2, h3, hbound1, hbeta, hdelta, hH, hnlarge, hR0, hRx, hcut, hPrefixBudget⟩
  let H : ℝ := 4 * beta ^ 2
  change 0 < H at hH
  have hxpos : 0 < x := by linarith only [hx]
  have hC1Data := hC1Segment rho bound hb hsupport hmean hsecond n hn x hx hx16 hscale hsmall
  have hd1 : delta ≤ 1 := hC1Data.2.2.1
  have hd2 : delta ^ 2 ≤ delta := by nlinarith only [hdelta, hd1]
  have hBoundRoot : bound ≤ Real.sqrt (n : ℝ) := by
    have hh : (100 * x) * bound ≤ Real.sqrt (n : ℝ) := by
      simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < 100 * x)).mp hscale
    exact (le_mul_of_one_le_left hb.le (by linarith only [hx] : 1 ≤ 100 * x)).trans hh
  have hHalf := hHalfInitial rho bound hb hsupport hmean hsecond n hn hBoundRoot Bm PB hBm x hxpos
  let X : Fin n → Shao.Path n → ℝ := fun i a => a i
  have hX (i : Fin n) : Measurable (X i) := measurable_pi_apply i
  have hInd : iIndepFun X P := iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hLaw (i : Fin n) : IdentDistrib (X i) (id : ℝ → ℝ) P rho :=
    ⟨(hX i).aemeasurable, measurable_id.aemeasurable, by
      simpa only [Measure.map_id] using (measurePreserving_eval (μ := fun _ : Fin n => rho) i).map_eq⟩
  have hInit := hIntervalInitial Bm PB hBm P rho n hn X (fun i => (hX i).aemeasurable)
    hInd hLaw h2 hmean (by rw [hsecond]; norm_num) x hxpos.le
  simp only [hsecond, mul_one, hR0] at hInit
  have hq (a : Shao.Path n) (sigma : LabelPerm n) :
      Shao.energy (Shao.Probability.Spitzer.reorder a sigma) = Shao.energy a :=
    Equiv.sum_comp sigma (fun i => (a i) ^ 2)
  have hs (a : Shao.Path n) (sigma : LabelPerm n) :
      Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) n = Shao.prefixSum a n := by
    simpa only [Shao.prefixSum_length, Shao.Probability.Spitzer.reorder] using Equiv.sum_comp sigma a
  have hmReorder : Measurable (randomReorder : Shao.Path n × LabelPerm n → Shao.Path n) :=
    measurable_from_prod_countable_left (fun sigma =>
      Measurable.of_eval (fun i => measurable_pi_apply (sigma i)))
  have hReorderMap : Measure.map (randomReorder : Shao.Path n × LabelPerm n → Shao.Path n)
      (revealLaw P) = P := by
    have hh := iid_randomPermutation_map_eq_pi P rho X hX hInd hLaw
    have hfun : (fun p : Shao.Path n × LabelPerm n =>
        Shao.Probability.Spitzer.reorder (Shao.Probability.samplePath X p.1) p.2) = randomReorder := by
      funext p i
      rfl
    change Measure.map (fun p => Shao.Probability.Spitzer.reorder (Shao.Probability.samplePath X p.1) p.2) (revealLaw P) = P at hh
    rw [hfun] at hh
    exact hh
  have hReorderLaw : IdentDistrib (randomReorder : Shao.Path n × LabelPerm n → Shao.Path n)
      (id : Shao.Path n → Shao.Path n) (revealLaw P) P :=
    ⟨hmReorder.aemeasurable, measurable_id.aemeasurable, by simpa only [Measure.map_id] using hReorderMap⟩
  let S : MonitoredDomain → Set (Shao.Path n) := fun J => match J with
    | .upper => {a | Shao.upperMax a hn < actualWall a x}
    | .lower => {a | Shao.upperMax (-a) hn < actualWall a x}
    | .interval => {a | Shao.absMax a hn < actualWall a x}
  have hSm (J : MonitoredDomain) : MeasurableSet (S J) := by
    cases J with
    | upper => exact measurableSet_lt (Shao.measurable_upperMax hn) (Shao.measurable_energyWall x)
    | lower => exact measurableSet_lt ((Shao.measurable_upperMax hn).comp (by fun_prop)) (Shao.measurable_energyWall x)
    | interval => exact measurableSet_lt (Shao.measurable_absMax hn) (Shao.measurable_energyWall x)
  have hSignedAlive (J : MonitoredDomain) (s : ℝ)
      (hJs : (J = .upper ∧ s = 1) ∨ (J = .lower ∧ s = -1)) (a : Shao.Path n) (sigma : LabelPerm n) :
      sourceAlive J a x n sigma ↔
        Shao.upperMax (s • Shao.Probability.Spitzer.reorder a sigma) hn < actualWall a x := by
    have hsign : s = 1 ∨ s = -1 := hJs.imp And.right And.right
    have hEnergy : Shao.energy (s • Shao.Probability.Spitzer.reorder a sigma) = Shao.energy a := by
      rcases hsign with rfl | rfl <;> simpa using hq a sigma
    constructor
    · intro ha
      obtain ⟨k, hk, hkn, hEq⟩ := Shao.upperMax_attained (s • Shao.Probability.Spitzer.reorder a sigma) hn
      rw [hEq, Shao.prefixSum_smul]
      have hp := ha.2.2 k hkn
      rcases hJs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa only [Interior, one_mul] using hp
      · change -actualWall a x < Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) k at hp
        simp only [neg_one_mul]
        linarith only [hp]
    · intro ha
      have hE : 0 < Shao.energy a := by
        by_contra hh
        have hz : Shao.energy a = 0 := le_antisymm (le_of_not_gt hh) (Shao.energy_nonneg a)
        have hz' : Shao.energy (s • Shao.Probability.Spitzer.reorder a sigma) = 0 := hEnergy.trans hz
        rw [Shao.upperMax_eq_zero_of_energy_eq_zero _ hn hz', actualWall, hz, Real.sqrt_zero, mul_zero] at ha
        exact (lt_irrefl 0) ha
      have hw : 0 < actualWall a x := mul_pos hxpos (Real.sqrt_pos.mpr hE)
      have hp (k : ℕ) (hkn : k ≤ n) : s * Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) k < actualWall a x := by
        by_cases hk : k = 0
        · simpa only [hk, Shao.prefixSum_zero, mul_zero] using hw
        · have hh := (Shao.le_upperMax (s • Shao.Probability.Spitzer.reorder a sigma) hn k
            (Nat.one_le_iff_ne_zero.mpr hk) hkn).trans_lt ha
          simpa only [Shao.prefixSum_smul] using hh
      refine ⟨hE, ?_, ?_⟩
      · have hz := hp n le_rfl
        rw [hs a sigma] at hz
        rcases hJs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simpa only [Interior, one_mul] using hz
        · change -actualWall a x < Shao.prefixSum a n
          simp only [neg_one_mul] at hz
          linarith only [hz]
      · intro k hk
        have hz := hp k hk
        rcases hJs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simpa only [Interior, one_mul] using hz
        · change -actualWall a x < Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) k
          simp only [neg_one_mul] at hz
          linarith only [hz]
  have hAlive (J : MonitoredDomain) (a : Shao.Path n) (sigma : LabelPerm n) :
      sourceAlive J a x n sigma ↔ Shao.Probability.Spitzer.reorder a sigma ∈ S J := by
    cases J with
    | upper => simpa only [S, Set.mem_setOf_eq, one_smul, actualWall, hq] using
        hSignedAlive .upper 1 (Or.inl ⟨rfl, rfl⟩) a sigma
    | lower => simpa only [S, Set.mem_setOf_eq, neg_one_smul, actualWall, hq] using
        hSignedAlive .lower (-1) (Or.inr ⟨rfl, rfl⟩) a sigma
    | interval =>
        change sourceAlive .interval a x n sigma ↔ Shao.absMax (Shao.Probability.Spitzer.reorder a sigma) hn <
          actualWall (Shao.Probability.Spitzer.reorder a sigma) x
        rw [show actualWall (Shao.Probability.Spitzer.reorder a sigma) x = actualWall a x by simp only [actualWall, hq]]
        constructor
        · intro ha
          obtain ⟨k, hk, hkn, hEq⟩ := Shao.absMax_attained (Shao.Probability.Spitzer.reorder a sigma) hn
          rw [hEq]
          exact abs_lt.mpr (ha.2.2 k hkn)
        · intro ha
          have hw : 0 < actualWall a x := (Shao.absMax_nonneg _ hn).trans_lt ha
          have hE : 0 < Shao.energy a := by
            by_contra hh
            have hz : Shao.energy a = 0 := le_antisymm (le_of_not_gt hh) (Shao.energy_nonneg a)
            simpa only [actualWall, hz, Real.sqrt_zero, mul_zero, lt_self_iff_false] using hw
          have hp (k : ℕ) (hk : k ≤ n) : |Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) k| < actualWall a x := by
            by_cases hk0 : k = 0
            · simpa only [hk0, Shao.prefixSum_zero, abs_zero] using hw
            · exact (Shao.le_absMax _ hn k (Nat.one_le_iff_ne_zero.mpr hk0) hk).trans_lt ha
          refine ⟨hE, ?_, fun k hk => abs_lt.mp (hp k hk)⟩
          have hz := abs_lt.mp (hp n le_rfl)
          rw [hs a sigma] at hz
          exact hz
  let A : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ := fun J p =>
    if sourceAlive J p.1 x n p.2 then 1 else 0
  let V0 : MonitoredDomain → Shao.Path n → ℝ := fun J a =>
    sourceValue J (eventCompletionKernel J Q) a x 0 (Equiv.refl (Fin n))
  let Vinitial : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ := fun J p =>
    sourceValue J (eventCompletionKernel J Q) p.1 x 0 p.2
  have hInitialEq (J : MonitoredDomain) (p : Shao.Path n × LabelPerm n) : Vinitial J p = V0 J p.1 := by
    exact (source_observables_prefix J (eventCompletionKernel J Q) (actualDerivativeFamily Q J) p.1 x 0).2.2.2.1
      p.2 (Equiv.refl (Fin n)) (fun i hi => by omega)
  have hV0I (J : MonitoredDomain) : Integrable (V0 J) P := by
    cases J with
    | upper => exact (hHalf.1 .upper (Or.inl rfl)).1
    | lower => exact (hHalf.1 .lower (Or.inr rfl)).1
    | interval => exact (hInit.2 (Equiv.refl (Fin n))).2.1
  have hApoint (J : MonitoredDomain) (p : Shao.Path n × LabelPerm n) :
      A J p = (S J).indicator (fun _ => (1 : ℝ)) (randomReorder p) := by
    change (if sourceAlive J p.1 x n p.2 then (1 : ℝ) else 0) = _
    by_cases hp : randomReorder p ∈ S J
    · have ha : sourceAlive J p.1 x n p.2 := (hAlive J p.1 p.2).mpr hp
      rw [if_pos ha, Set.indicator_of_mem hp]
    · have ha : ¬ sourceAlive J p.1 x n p.2 := fun h => hp ((hAlive J p.1 p.2).mp h)
      rw [if_neg ha, Set.indicator_of_notMem hp]
  have hAI (J : MonitoredDomain) : Integrable (A J) (revealLaw P) := by
    have hi := (hReorderLaw.comp
      ((measurable_const : Measurable (fun _ : Shao.Path n => (1 : ℝ))).indicator (hSm J))).integrable_iff.mpr
      ((integrable_const (1 : ℝ)).indicator (hSm J))
    exact hi.congr (ae_of_all _ fun p => (hApoint J p).symm)
  have hAIntegral (J : MonitoredDomain) : (∫ p, A J p ∂revealLaw P) = P.real (S J) := by
    calc
      _ = ∫ p, (S J).indicator (fun _ => (1 : ℝ)) (randomReorder p) ∂revealLaw P :=
        integral_congr_ae (ae_of_all _ (hApoint J))
      _ = ∫ a, (S J).indicator (fun _ => (1 : ℝ)) a ∂P :=
        (hReorderLaw.comp (measurable_const.indicator (hSm J))).integral_eq
      _ = _ := integral_indicator_one (hSm J)
  have hFstMap : Measure.map (Prod.fst : Shao.Path n × LabelPerm n → Shao.Path n) (revealLaw P) = P :=
    (measurePreserving_fst (μ := P) (ν := uniformPermutationLaw n)).map_eq
  have hInitialIntegral (J : MonitoredDomain) : (∫ p, Vinitial J p ∂revealLaw P) = ∫ a, V0 J a ∂P := by
    have hVm : AEStronglyMeasurable (V0 J) (Measure.map Prod.fst (revealLaw P)) := by
      rw [hFstMap]
      exact (hV0I J).aestronglyMeasurable
    have he := integral_map (μ := revealLaw P) (φ := Prod.fst) measurable_fst.aemeasurable hVm
    rw [hFstMap] at he
    exact (integral_congr_ae (ae_of_all _ (hInitialEq J))).trans he.symm
  have hRfl : Shao.Probability.SourceActualLocalProfileBudget.HalflineReflectionIdentities Q := by
    constructor
    · intro w y T z _ hT hy hz
      exact Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula Bm PB hBm w y T z hT hy hz
    · intro w y T z _ hT hy hz
      exact Shao.C2.BridgeLowerIdentification.bridge_lower_formula Bm PB hBm w y T z hT hy hz
  have hReg : ∀ w y T z : ℝ, 0 < w → 0 < T → |y| < w → |z| < w →
      DifferentiableAt ℝ (fun a => Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w a T z) y := by
    intro w y T z hw hT hy hz
    exact Shao.C2.ActualBridgeIntervalTelescope.actual_source_interval_differentiable Bm PB hBm w y T z hw hy hz hT
  have hKernel (J : MonitoredDomain) : Measurable (actualDerivativeFamily Q J) ∧
      KernelBounds J (eventCompletionKernel J Q) (actualDerivativeFamily Q J) 4 ∧
      ∀ w y T z : ℝ, 0 < w → 0 < T → Interior J w y → Interior J w z →
        HasDerivAt (fun a => eventCompletionKernel J Q (w, a, T, z)) (actualDerivativeFamily Q J (w, y, T, z)) y := by
    cases J with
    | upper => exact Shao.Probability.SourceActualLocalProfileBudget.actual_halfline_kernel_data Q hRfl .upper (Or.inl rfl)
    | lower => exact Shao.Probability.SourceActualLocalProfileBudget.actual_halfline_kernel_data Q hRfl .lower (Or.inr rfl)
    | interval =>
        simpa only [actualDerivativeFamily, Interior, abs_lt] using
          Shao.Probability.SourceActualIntervalProfileBudget.actual_interval_kernel_data Q hRfl hReg
  let nu : Shao.Path n → LabelPerm n → ℕ := fun a sigma => energyCutoff a H sigma
  have hnum (sigma : LabelPerm n) : Measurable (fun a : Shao.Path n => nu a sigma) :=
    Shao.Probability.SourceActualLocalProfileBudget.actual_energy_cutoff_measurable H hH sigma
  have hnub (a : Shao.Path n) (sigma : LabelPerm n) : nu a sigma ≤ n := (energy_cutoff_data a H hH).1.1 sigma
  have hnustop (a : Shao.Path n) : IsRevealStoppingRank (nu a) := (energy_cutoff_data a H hH).1
  let L : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℕ → ℝ := fun J p r =>
    sourceRetainedRemainder J (eventCompletionKernel J Q) (actualDerivativeFamily Q J) p.1 x (nu p.1) r p.2
  let O : (Shao.Path n × LabelPerm n) → ℕ → ℝ := fun p r =>
    sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval) p.1 x (nu p.1) r p.2
  have hParts (J : MonitoredDomain) := source_parts_measurable_integrable J (eventCompletionKernel J Q)
    (actualDerivativeFamily Q J) (eventCompletionKernel_data J Q).1 (hKernel J).1 4 (hKernel J).2.1 P x hxpos nu hnum
  have hLI (J : MonitoredDomain) (r : ℕ) : Integrable (fun p => |L J p r|) (revealLaw P) :=
    ((hParts J).2.1 r).1.abs
  have hOI (r : ℕ) : Integrable (fun p => max (-O p r) 0) (revealLaw P) := by
    have hi := ((((hParts .interval).2.1 r).2.abs).sub ((hParts .interval).2.1 r).2).div_const 2
    change Integrable (fun p => (|O p r| - O p r) / 2) (revealLaw P) at hi
    have he : (fun p => (|O p r| - O p r) / 2) = (fun p => max (-O p r) 0) := by
      funext p
      by_cases ho : 0 ≤ O p r
      · rw [abs_of_nonneg ho, max_eq_right (neg_nonpos.mpr ho)]
        ring
      · have hn : O p r ≤ 0 := le_of_not_ge ho
        rw [abs_of_nonpos hn, max_eq_left (neg_nonneg.mpr hn)]
        ring
    rw [he] at hi
    exact hi
  have hInitialI (J : MonitoredDomain) : Integrable (Vinitial J) (revealLaw P) := by
    have hh := (source_stopped_integrability J (eventCompletionKernel J Q) (actualDerivativeFamily Q J)
      (eventCompletionKernel_data J Q).1 (hKernel J).1 4 (hKernel J).2.1 P x hxpos nu hnum hnub
      (fun _ => 1) measurable_const (fun _ => by norm_num)).2.1
    simpa only [one_mul] using hh
  have hBData := hBill rho bound hb hsupport hmean hsecond n hn x hx hscale Bm PB hBm nu hnum (fun _ _ => le_rfl)
  have hB : ((∫ p, ∑ r ∈ Finset.range n, |L .upper p r| ∂revealLaw P) +
      (∫ p, ∑ r ∈ Finset.range n, |L .lower p r| ∂revealLaw P) +
      (∫ p, ∑ r ∈ Finset.range n, |L .interval p r| ∂revealLaw P) +
      (∫ p, ∑ r ∈ Finset.range n, max (-O p r) 0 ∂revealLaw P)) ≤ CB * delta := by
    simp_rw [← Fin.sum_univ_eq_sum_range]
    have hi (J : MonitoredDomain) : Integrable (fun p => ∑ r : Fin n, |L J p r.val|) (revealLaw P) :=
      integrable_finsetSum _ (fun r _ => hLI J r.val)
    have hio : Integrable (fun p => ∑ r : Fin n, max (-O p r.val) 0) (revealLaw P) :=
      integrable_finsetSum _ (fun r _ => hOI r.val)
    have he1 := integral_add (hi .upper) (hi .lower)
    have he2 := integral_add ((hi .upper).add (hi .lower)) (hi .interval)
    have he3 := integral_add (((hi .upper).add (hi .lower)).add (hi .interval)) hio
    simp only [Pi.add_apply] at he1 he2 he3
    rw [← he1, ← he2, ← he3]
    have heq : (fun p => ((∑ r : Fin n, |L .upper p r.val|) + (∑ r : Fin n, |L .lower p r.val|)) +
        (∑ r : Fin n, |L .interval p r.val|) + (∑ r : Fin n, max (-O p r.val) 0)) =
        (fun p => ∑ r : Fin n, actualRetainedAbsoluteRank Q p.1 x (nu p.1) r p.2) := by
      funext p
      simp only [actualRetainedAbsoluteRank, L, O, Finset.sum_add_distrib]
      ring
    rw [heq]
    exact hBData.2.2.2.2.1
  have hE : ∀ J : MonitoredDomain,
      (∫ p, |sourceValue J (eventCompletionKernel J Q) p.1 x (nu p.1 p.2) p.2 - A J p| ∂revealLaw P) ≤ CE * delta := by
    intro J
    rcases hTerminal rho bound hb hsupport hmean hsecond n hn x hx hscale Bm PB hBm J with
      ⟨hidm, hidi, hidr, hid0, hidB, hfm, hfi, hfr, hf0, hfB⟩
    have hStopI : Integrable (fun p => sourceValue J (eventCompletionKernel J Q) p.1 x (nu p.1 p.2) p.2) (revealLaw P) := by
      have hh := (source_stopped_integrability J (eventCompletionKernel J Q) (actualDerivativeFamily Q J)
        (eventCompletionKernel_data J Q).1 (hKernel J).1 4 (hKernel J).2.1 P x hxpos nu hnum hnub
        (fun _ => 1) measurable_const (fun _ => by norm_num)).1
      simpa only [one_mul] using hh
    calc
      _ ≤ ∫ p, abcf_h0Future J Q H x p ∂revealLaw P := by
        apply integral_mono (hStopI.sub (hAI J)).abs hfi
        intro p
        have hh := Finset.le_sup'
          (fun j => if nu p.1 p.2 ≤ j then |sourceValue J (eventCompletionKernel J Q) p.1 x j p.2 - A J p| else 0)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le (hnub p.1 p.2)))
        simpa only [if_pos le_rfl, abcf_h0Future, abcf_futureAt, nu, A, Pi.sub_apply,
          H, Q, Nat.succ_eq_add_one] using hh
      _ ≤ CE * delta ^ 2 := hfB
      _ ≤ CE * delta := mul_le_mul_of_nonneg_left hd2 hCE.le
  have hG : ∀ J : MonitoredDomain, J = .upper ∨ J = .lower →
      |(∫ p, A J p ∂revealLaw P) - (∫ p, Vinitial J p ∂revealLaw P)| ≤ KG * delta := by
    intro J hJ
    obtain ⟨s, hsign, hJs⟩ : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
        ((J = .upper ∧ s = 1) ∨ (J = .lower ∧ s = -1)) := by
      rcases hJ with rfl | rfl
      · exact ⟨1, Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨-1, Or.inr rfl, Or.inr ⟨rfl, rfl⟩⟩
    let U : Set (Shao.Path n) := {a | x * Real.sqrt (Shao.energy a) ≤ Shao.upperMax (s • a) hn}
    have hUm : MeasurableSet U := measurableSet_le (Shao.measurable_energyWall x)
      ((Shao.measurable_upperMax hn).comp (Measurable.of_eval fun i => measurable_const.mul (measurable_pi_apply i)))
    have hComp : S J = Uᶜ := by
      ext a
      rcases hJs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [S, U, Set.mem_setOf_eq, Set.mem_compl_iff, not_le, one_smul, neg_one_smul, actualWall]
    have hCross := (hC1Data.2.2.2 s hsign).2
    change |P.real U - 2 * Shao.standardNormalTail x| ≤ K1 * delta at hCross
    have hSurv : |P.real (S J) - (1 - 2 * Shao.standardNormalTail x)| ≤ K1 * delta := by
      rw [hComp, measureReal_compl hUm, probReal_univ]
      have he : (1 - P.real U) - (1 - 2 * Shao.standardNormalTail x) =
          -(P.real U - 2 * Shao.standardNormalTail x) := by ring
      rw [he, abs_neg]
      exact hCross
    have hVGap := (hHalf.1 J hJ).2
    rw [hAIntegral J, hInitialIntegral J]
    calc
      _ ≤ |P.real (S J) - (1 - 2 * Shao.standardNormalTail x)| +
          |(1 - 2 * Shao.standardNormalTail x) - (∫ a, V0 J a ∂P)| := abs_sub_le _ _ _
      _ ≤ K1 * delta + CS * delta := by
        apply add_le_add hSurv
        simpa only [abs_sub_comm] using hVGap
      _ = KG * delta := by dsimp [KG]; ring
  have hTransfer := source_three_domain_overshoot_transfer P Q (actualDerivativeFamily Q)
    (fun J => (hKernel J).1) 4 (by norm_num)
    (fun J => (hKernel J).2.1.derivative_bound) (fun J => (hKernel J).2.2)
    x hxpos H hH nu hnum hnustop (fun _ _ => le_rfl) (CB * delta) (CE * delta) (KG * delta) hB hE hG
  have ht := hTransfer.2.2 (fun _ => 1) measurable_const (fun _ => by norm_num) (fun _ _ => rfl)
  simp only [one_mul] at ht
  change |(∫ p, A .interval p - Vinitial .interval p ∂revealLaw P)| ≤
    3 * (CB * delta) + 3 * (CE * delta) + 2 * (KG * delta) at ht
  rw [integral_sub (hAI .interval) (hInitialI .interval), hAIntegral .interval, hInitialIntegral .interval] at ht
  let SB : Set ΩB := {omegaB | ∀ t : BridgeTime, |Bm ⟨(t : ℝ), t.property.1⟩ omegaB| < x}
  have hInitB : |(∫ a, V0 .interval a ∂P) - PB.real SB| ≤ CI * delta :=
    (hInit.2 (Equiv.refl (Fin n))).2.2.1
  have hStrict : |P.real (S .interval) - PB.real SB| ≤ CA * delta := by
    calc
      _ ≤ |P.real (S .interval) - ∫ a, V0 .interval a ∂P| + |(∫ a, V0 .interval a ∂P) - PB.real SB| := abs_sub_le _ _ _
      _ ≤ (3 * (CB * delta) + 3 * (CE * delta) + 2 * (KG * delta)) + CI * delta := add_le_add ht hInitB
      _ ≤ CA * delta := by dsimp [CA]; nlinarith only [hdelta]
  have hBPair : AEMeasurable (fun omegaB : ΩB => (bridgeNoise Bm omegaB, Bm 1 omegaB)) PB :=
    (aemeasurable_bridgeNoise Bm PB hBm).prodMk (hBm.toIsPreBrownianReal.aemeasurable 1)
  have hBAE : (fun omegaB : ΩB => (bridgeNoise Bm omegaB, Bm 1 omegaB)) ⁻¹' initialSurvival x =ᵐ[PB] SB := by
    filter_upwards [ae_bridgeNoise_eq Bm PB hBm] with omegaB homegaB
    apply propext
    rw [Set.mem_preimage, mem_initialSurvival_iff]
    have he (t : BridgeTime) : bridgePath 0 1 (Bm 1 omegaB) (bridgeNoise Bm omegaB) t =
        Bm ⟨(t : ℝ), t.property.1⟩ omegaB := by
      simp only [bridgePath, ContinuousMap.coe_mk, mul_zero, zero_add, Real.sqrt_one, one_mul]
      rw [homegaB t]
      ring
    simp only [he, SB, Set.mem_setOf_eq]
  have hSBnull : NullMeasurableSet SB PB :=
    (hBPair.nullMeasurableSet_preimage (measurableSet_initialSurvival x)).congr hBAE
  have hWeak : {a : Shao.Path n | x * Real.sqrt (Shao.energy a) ≤ Shao.absMax a hn} = (S .interval)ᶜ := by
    ext a
    simp only [S, Set.mem_setOf_eq, Set.mem_compl_iff, not_lt, actualWall]
  have hBWeak : {omegaB | ∃ t : BridgeTime, x ≤ |Bm ⟨(t : ℝ), t.property.1⟩ omegaB|} = SBᶜ := by
    ext omegaB
    simp only [SB, Set.mem_setOf_eq, Set.mem_compl_iff, not_forall, not_lt]
  rw [hWeak, hBWeak, measureReal_compl (hSm .interval), measureReal_compl₀ hSBnull, probReal_univ]
  simp only [probReal_univ]
  have he : (1 - P.real (S .interval)) - (1 - PB.real SB) = -(P.real (S .interval) - PB.real SB) := by ring
  rw [he, abs_neg]
  exact hStrict

theorem iid_actual_bounded_centered_fixed_comparison :
    ∃ epsilonF CF CA : ℝ, 0 < epsilonF ∧ epsilonF ≤ 1 / 8 ∧ 0 < CF ∧ 0 < CA ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (bound : ℝ), 0 < bound → (∀ᵐ z : ℝ ∂rho, |z| ≤ bound) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        ∀ (n : ℕ) (hn : 0 < n) (x : ℝ), (1 / 2 : ℝ) ≤ x → x ≤ 16 →
          bound ≤ Real.sqrt (n : ℝ) / (100 * x) →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          let delta : ℝ := beta / Real.sqrt (n : ℝ)
          delta * x ^ 3 ≤ epsilonF →
          ∀ {ΩB : Type*} [MeasurableSpace ΩB]
            (Bm : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
            IsBrownianReal Bm PB →
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
            let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) rho
            let brownianDouble : Set ΩB := {omegaB |
              (∃ t : BridgeTime, x ≤ Bm ⟨(t : ℝ), t.property.1⟩ omegaB) ∧
              (∃ t : BridgeTime, Bm ⟨(t : ℝ), t.property.1⟩ omegaB ≤ -x)}
            Shao.truncationBudget normalizedLaw n 0 = delta ∧
              Shao.truncationBudget normalizedLaw n x = delta * (1 + x) ^ 3 ∧
              |P.real (doubleCrossingEvent x) - PB.real brownianDouble| ≤
                CF * delta * (1 + x) ^ 3 * Shao.standardNormalTail x ∧
              |P.real {a | x * Real.sqrt (Shao.energy a) ≤ Shao.absMax a hn} -
                PB.real {omegaB | ∃ t : BridgeTime,
                  x ≤ |Bm ⟨(t : ℝ), t.property.1⟩ omegaB|}| ≤ CA * delta := by
  classical
  obtain ⟨epsA, CA, hEpsA, hEpsA8, hCA, hAbsolute⟩ := abcf_fixed_absolute_comparison
  obtain ⟨rhoStar, eps1, C1, K1, hrho, hrho16, hEps1Eq, hEps1, hC1, hK1, hSegment⟩ :=
    abcf_legal_c1_fixed_segment
  obtain ⟨CS, hCS, hHalfInitial⟩ := abcf_halfline_initial_all_positive
  let epsilonF : ℝ := min epsA eps1
  let KD : ℝ := 2 * K1 + CA
  let CF : ℝ := 1 + KD / Shao.standardNormalTail 16
  have hKD : 0 < KD := by dsimp [KD]; positivity
  have ht16 : 0 < Shao.standardNormalTail 16 := (Shao.standardNormalTail_basic.2.2.1 16).1
  have hCF : 0 < CF := by dsimp [CF]; positivity
  refine ⟨epsilonF, CF, CA, lt_min hEpsA hEps1, (min_le_left _ _).trans hEpsA8, hCF, hCA, ?_⟩
  intro rho hProb bound hb hsupport hmean hsecond n hn x hx hx16 hscale beta delta hsmall
    ΩB hΩB Bm PB hPB hBm P normalizedLaw brownianDouble
  letI : IsProbabilityMeasure rho := hProb
  letI : IsProbabilityMeasure PB := hPB
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  rcases abcf_bounded_own_budget_identities rho bound hb hsupport hmean hsecond n hn x hx hscale with
    ⟨h1, h2, h3, hbound1, hbeta, hdelta, hH, hnlarge, hR0, hRx, hcut, hPrefixBudget⟩
  have hxpos : 0 < x := by linarith only [hx]
  have hsmallA : delta * x ^ 3 ≤ epsA := hsmall.trans (min_le_left _ _)
  have hsmall1 : delta * x ^ 3 ≤ eps1 := hsmall.trans (min_le_right _ _)
  have hC1Data := hSegment rho bound hb hsupport hmean hsecond n hn x hx hx16 hscale hsmall1
  have hAbs := hAbsolute rho bound hb hsupport hmean hsecond n hn x hx hx16 hscale hsmallA Bm PB hBm
  have hBoundRoot : bound ≤ Real.sqrt (n : ℝ) := by
    have hh : (100 * x) * bound ≤ Real.sqrt (n : ℝ) := by
      simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < 100 * x)).mp hscale
    exact (le_mul_of_one_le_left hb.le (by linarith only [hx] : 1 ≤ 100 * x)).trans hh
  have hHalf := hHalfInitial rho bound hb hsupport hmean hsecond n hn hBoundRoot Bm PB hBm x hxpos
  let U : Set (Shao.Path n) := {a | actualWall a x ≤ Shao.upperMax a hn}
  let L : Set (Shao.Path n) := {a | actualWall a x ≤ Shao.upperMax (-a) hn}
  let W : Set (Shao.Path n) := {a | actualWall a x ≤ Shao.absMax a hn}
  let UB : Set ΩB := {omegaB | ∃ t : BridgeTime, x ≤ Bm ⟨(t : ℝ), t.property.1⟩ omegaB}
  let LB : Set ΩB := {omegaB | ∃ t : BridgeTime, Bm ⟨(t : ℝ), t.property.1⟩ omegaB ≤ -x}
  let WB : Set ΩB := {omegaB | ∃ t : BridgeTime, x ≤ |Bm ⟨(t : ℝ), t.property.1⟩ omegaB|}
  have hUm : MeasurableSet U := measurableSet_le (Shao.measurable_energyWall x) (Shao.measurable_upperMax hn)
  have hLm : MeasurableSet L := measurableSet_le (Shao.measurable_energyWall x)
    ((Shao.measurable_upperMax hn).comp (by fun_prop))
  have hHit (s : ℝ) (hsign : s = 1 ∨ s = -1) (a : Shao.Path n) :
      (∃ r : ℕ, r ≤ n ∧ actualWall a x ≤ s * Shao.prefixSum a r) ↔
        actualWall a x ≤ Shao.upperMax (s • a) hn := by
    constructor
    · rintro ⟨r, hr, hc⟩
      by_cases hr0 : r = 0
      · have hw0 : actualWall a x ≤ 0 := by simpa only [hr0, Shao.prefixSum_zero, mul_zero] using hc
        have hE0 : Shao.energy a = 0 := by
          by_contra hne
          have hp : 0 < Shao.energy a := lt_of_le_of_ne (Shao.energy_nonneg a) (Ne.symm hne)
          exact (not_lt_of_ge hw0) (mul_pos hxpos (Real.sqrt_pos.mpr hp))
        have hSigned0 : Shao.energy (s • a) = 0 := by
          rcases hsign with rfl | rfl <;> simpa using hE0
        rw [Shao.upperMax_eq_zero_of_energy_eq_zero _ hn hSigned0]
        exact hw0
      · have hp := Shao.le_upperMax (s • a) hn r (Nat.one_le_iff_ne_zero.mpr hr0) hr
        rw [Shao.prefixSum_smul] at hp
        exact hc.trans hp
    · intro hc
      obtain ⟨r, hr, hrn, hEq⟩ := Shao.upperMax_attained (s • a) hn
      refine ⟨r, hrn, ?_⟩
      rw [hEq, Shao.prefixSum_smul] at hc
      exact hc
  have hDouble : doubleCrossingEvent x = U ∩ L := by
    ext a
    change ((∃ r : ℕ, r ≤ n ∧ actualWall a x ≤ Shao.prefixSum a r) ∧
      (∃ r : ℕ, r ≤ n ∧ Shao.prefixSum a r ≤ -actualWall a x)) ↔
      (actualWall a x ≤ Shao.upperMax a hn ∧ actualWall a x ≤ Shao.upperMax (-a) hn)
    constructor
    · rintro ⟨⟨r, hr, hc⟩, ⟨t, ht, hd⟩⟩
      constructor
      · simpa only [one_smul] using (hHit 1 (Or.inl rfl) a).mp ⟨r, hr, by simpa only [one_mul] using hc⟩
      · simpa only [neg_one_smul] using
          (hHit (-1) (Or.inr rfl) a).mp ⟨t, ht, by simp only [neg_one_mul]; linarith only [hd]⟩
    · rintro ⟨hu, hl⟩
      obtain ⟨r, hr, hc⟩ := (hHit 1 (Or.inl rfl) a).mpr (by simpa only [one_smul] using hu)
      obtain ⟨t, ht, hd⟩ := (hHit (-1) (Or.inr rfl) a).mpr (by simpa only [neg_one_smul] using hl)
      refine ⟨⟨r, hr, by simpa only [one_mul] using hc⟩, ⟨t, ht, ?_⟩⟩
      simp only [neg_one_mul] at hd
      linarith only [hd]
  have hUnion : U ∪ L = W := by
    ext a
    simp only [U, L, W, Set.mem_union, Set.mem_setOf_eq, Shao.absMax, Shao.lowerMax, le_max_iff]
  have hBUnion : UB ∪ LB = WB := by
    ext omegaB
    constructor
    · rintro (⟨t, ht⟩ | ⟨t, ht⟩)
      · exact ⟨t, ht.trans (le_abs_self _)⟩
      · exact ⟨t, (by linarith only [ht] : x ≤ -Bm ⟨(t : ℝ), t.property.1⟩ omegaB).trans (neg_le_abs _)⟩
    · rintro ⟨t, ht⟩
      by_cases hz : 0 ≤ Bm ⟨(t : ℝ), t.property.1⟩ omegaB
      · rw [abs_of_nonneg hz] at ht
        exact Or.inl ⟨t, ht⟩
      · rw [abs_of_neg (lt_of_not_ge hz)] at ht
        exact Or.inr ⟨t, by linarith only [ht]⟩
  have hBDouble : brownianDouble = UB ∩ LB := by
    ext omegaB
    rfl
  have hUpperNull (Y : ℝ≥0 → ΩB → ℝ) (hY : IsBrownianReal Y PB) :
      NullMeasurableSet {omegaB | ∃ t : BridgeTime, x ≤ Y ⟨(t : ℝ), t.property.1⟩ omegaB} PB := by
    let K : Set (ContinuousMap BridgeTime ℝ) := {f | ∃ t : BridgeTime, x ≤ f t}
    have ho : IsOpen {f : ContinuousMap BridgeTime ℝ | ∀ t : BridgeTime, f t < x} := by
      simpa [Set.MapsTo] using
        (ContinuousMap.isOpen_setOfPred_mapsTo (X := BridgeTime) isCompact_univ (isOpen_Iio (a := x)))
    have hK : MeasurableSet K := by
      have he : K = {f : ContinuousMap BridgeTime ℝ | ∀ t : BridgeTime, f t < x}ᶜ := by
        ext f
        simp only [K, Set.mem_setOf_eq, Set.mem_compl_iff, not_forall, not_lt]
      rw [he]
      exact ho.measurableSet.compl
    have hm := (Shao.OQ4.PolygonalBrownianWeakLimit.aemeasurable_brownianUnitPath Y 1 PB hY).nullMeasurableSet_preimage hK
    apply hm.congr
    filter_upwards [Shao.OQ4.PolygonalBrownianWeakLimit.ae_brownianUnitPath_eq Y 1 PB hY] with omegaB homegaB
    apply propext
    change (∃ t : BridgeTime, x ≤ Shao.OQ4.PolygonalBrownianWeakLimit.brownianUnitPath Y 1 omegaB t) ↔ _
    have ht (t : BridgeTime) : Shao.OQ4.PolygonalBrownianWeakLimit.brownianUnitPath Y 1 omegaB t =
        Y ⟨(t : ℝ), t.property.1⟩ omegaB := by
      have hh := homegaB t
      change Shao.OQ4.PolygonalBrownianWeakLimit.brownianUnitPath Y 1 omegaB t =
        Y (1 * ⟨(t : ℝ), t.property.1⟩) omegaB at hh
      exact hh.trans (congrArg (fun q : ℝ≥0 => Y q omegaB) (_root_.one_mul _))
    simp only [ht]
  have hUBnull : NullMeasurableSet UB PB := hUpperNull Bm hBm
  have hLBnull : NullMeasurableSet LB PB := by
    have he : LB = {omegaB | ∃ t : BridgeTime, x ≤ (-Bm) ⟨(t : ℝ), t.property.1⟩ omegaB} := by
      ext omegaB
      change (∃ t : BridgeTime, Bm ⟨(t : ℝ), t.property.1⟩ omegaB ≤ -x) ↔
        (∃ t : BridgeTime, x ≤ (-Bm) ⟨(t : ℝ), t.property.1⟩ omegaB)
      constructor
      · rintro ⟨t, ht⟩
        refine ⟨t, ?_⟩
        change x ≤ -(Bm ⟨(t : ℝ), t.property.1⟩ omegaB)
        linarith only [ht]
      · rintro ⟨t, ht⟩
        change x ≤ -(Bm ⟨(t : ℝ), t.property.1⟩ omegaB) at ht
        exact ⟨t, by linarith only [ht]⟩
    rw [he]
    exact hUpperNull (-Bm) hBm.neg
  have hUB : PB.real UB = 2 * Shao.standardNormalTail x := by simpa only [one_mul] using hHalf.2 1 (Or.inl rfl)
  have hLB : PB.real LB = 2 * Shao.standardNormalTail x := by
    have he : LB = {omegaB | ∃ t : BridgeTime, x ≤ (-1 : ℝ) * Bm ⟨(t : ℝ), t.property.1⟩ omegaB} := by
      ext omegaB
      simp only [LB, Set.mem_setOf_eq, neg_one_mul]
      constructor <;> rintro ⟨t, ht⟩ <;> exact ⟨t, by linarith only [ht]⟩
    rw [he]
    exact hHalf.2 (-1) (Or.inr rfl)
  have hUError : |P.real U - 2 * Shao.standardNormalTail x| ≤ K1 * delta := by
    simpa only [one_smul, U, actualWall] using (hC1Data.2.2.2 1 (Or.inl rfl)).2
  have hLError : |P.real L - 2 * Shao.standardNormalTail x| ≤ K1 * delta := by
    simpa only [neg_one_smul, L, actualWall] using (hC1Data.2.2.2 (-1) (Or.inr rfl)).2
  have hWError : |P.real W - PB.real WB| ≤ CA * delta := hAbs
  have hFiniteIE := measureReal_union_add_inter₀ (μ := P) (s := U) hLm.nullMeasurableSet
  rw [hUnion, ← hDouble] at hFiniteIE
  have hBrownianIE := measureReal_union_add_inter₀ (μ := PB) (s := UB) hLBnull
  rw [hBUnion, ← hBDouble, hUB, hLB] at hBrownianIE
  have hDoubleError : |P.real (doubleCrossingEvent x) - PB.real brownianDouble| ≤ KD * delta := by
    have he : P.real (doubleCrossingEvent x) - PB.real brownianDouble =
        (P.real U - 2 * Shao.standardNormalTail x) + (P.real L - 2 * Shao.standardNormalTail x) -
        (P.real W - PB.real WB) := by linarith only [hFiniteIE, hBrownianIE]
    rw [he]
    calc
      _ ≤ |(P.real U - 2 * Shao.standardNormalTail x) + (P.real L - 2 * Shao.standardNormalTail x)| +
          |P.real W - PB.real WB| := abs_sub _ _
      _ ≤ (|P.real U - 2 * Shao.standardNormalTail x| + |P.real L - 2 * Shao.standardNormalTail x|) +
          |P.real W - PB.real WB| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ (K1 * delta + K1 * delta) + CA * delta := add_le_add (add_le_add hUError hLError) hWError
      _ = KD * delta := by dsimp [KD]; ring
  have hWeight : Shao.standardNormalTail 16 ≤ (1 + x) ^ 3 * Shao.standardNormalTail x := by
    have ht : Shao.standardNormalTail 16 ≤ Shao.standardNormalTail x := Shao.standardNormalTail_basic.1 hx16
    have hc : (1 : ℝ) ≤ (1 + x) ^ 3 := by
      calc
        (1 : ℝ) = 1 ^ 3 := by norm_num
        _ ≤ (1 + x) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith only [hx]) 3
    exact ht.trans (le_mul_of_one_le_left (Shao.standardNormalTail_basic.2.2.1 x).1.le hc)
  have hCFPay : KD ≤ CF * Shao.standardNormalTail 16 := by
    have he : CF * Shao.standardNormalTail 16 = Shao.standardNormalTail 16 + KD := by
      dsimp only [CF]
      field_simp [ht16.ne']
      <;> ring
    rw [he]
    linarith only [ht16]
  refine ⟨hR0, hRx, hDoubleError.trans ?_, hAbs⟩
  calc
    KD * delta ≤ (CF * Shao.standardNormalTail 16) * delta := mul_le_mul_of_nonneg_right hCFPay hdelta.le
    _ ≤ (CF * ((1 + x) ^ 3 * Shao.standardNormalTail x)) * delta :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWeight hCF.le) hdelta.le
    _ = CF * delta * (1 + x) ^ 3 * Shao.standardNormalTail x := by ring

theorem iid_actual_bounded_own_budget_identities
    (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (bound : ℝ) (hb : 0 < bound) (hsupport : ∀ᵐ z : ℝ ∂rho, |z| ≤ bound)
    (hmean : (∫ z : ℝ, z ∂rho) = 0)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂rho) = 1)
    (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : (1 / 2 : ℝ) ≤ x)
    (hscale : bound ≤ Real.sqrt (n : ℝ) / (100 * x)) :
    let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
    let delta : ℝ := beta / Real.sqrt (n : ℝ)
    let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) rho
    Integrable (fun z : ℝ => z) rho ∧
      Integrable (fun z : ℝ => z ^ 2) rho ∧ Integrable (fun z : ℝ => |z| ^ 3) rho ∧
      1 ≤ bound ∧ 1 ≤ beta ∧ 0 < delta ∧ 0 < 4 * beta ^ 2 ∧ 2500 ≤ n ∧
      Shao.truncationBudget normalizedLaw n 0 = delta ∧
      Shao.truncationBudget normalizedLaw n x = delta * (1 + x) ^ 3 ∧
      4 * (n : ℝ) * (Shao.truncationBudget normalizedLaw n 0) ^ 2 = 4 * beta ^ 2 ∧
      ∀ t ∈ Finset.Icc 1 (n / 2),
        Shao.truncationBudget
          (Measure.map (fun z : ℝ => z / Real.sqrt ((n - t : ℕ) : ℝ)) rho)
          (n - t) 0 = beta / Real.sqrt ((n - t : ℕ) : ℝ) := by
  exact abcf_bounded_own_budget_identities rho bound hb hsupport hmean hsecond n hn x hx hscale

theorem iid_actual_halfline_initial_all_positive :
    ∃ C : ℝ, 0 < C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (bound : ℝ), 0 < bound → (∀ᵐ z : ℝ ∂rho, |z| ≤ bound) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        ∀ (n : ℕ), 0 < n → bound ≤ Real.sqrt (n : ℝ) →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          let delta : ℝ := beta / Real.sqrt (n : ℝ)
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
          ∀ {ΩB : Type*} [MeasurableSpace ΩB]
            (Bm : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
            IsBrownianReal Bm PB → ∀ (x : ℝ), 0 < x →
              let Q : Measure BridgeNoise := bridgeLaw Bm PB
              (∀ J : MonitoredDomain, (J = .upper ∨ J = .lower) →
                let V0 : Shao.Path n → ℝ := fun a =>
                  sourceValue J (eventCompletionKernel J Q) a x 0 (Equiv.refl (Fin n))
                Integrable V0 P ∧ |(∫ a, V0 a ∂P) - (1 - 2 * Shao.standardNormalTail x)| ≤ C * delta) ∧
              ∀ s : ℝ, (s = 1 ∨ s = -1) →
                PB.real {omegaB | ∃ t : BridgeTime,
                  x ≤ s * Bm ⟨(t : ℝ), t.property.1⟩ omegaB} = 2 * Shao.standardNormalTail x := by
  exact abcf_halfline_initial_all_positive

end Shao.C2.ActualBoundedCenteredFixed
