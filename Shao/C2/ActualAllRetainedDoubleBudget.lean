import Shao.C2.ActualPostwallRetainedBudgets
import Shao.C2.ActualRetainedResidualBudgets
import Shao.Probability.SourceRegularRetainedProbability

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
noncomputable section
namespace Shao.C2.ActualAllRetainedDoubleBudget
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.ActualSignedDoubleTelescope
open Shao.C2.ActualPostwallRetainedBudgets
open Shao.C2.ActualRetainedResidualBudgets
open Shao.Probability.SourcePermutationReveal
open Shao.Probability.SourceSeparatedOvershoot

local instance allRetainedLabelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

-- FROZEN_PUBLIC_HEAD_1
theorem iid_actual_all_retained_double_absolute_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ΩB : Type*} [MeasurableSpace ΩB]
        (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (Bm : ℝ≥0 → ΩB → ℝ), IsBrownianReal Bm PB →
        let Q : Measure BridgeNoise := bridgeLaw Bm PB
        ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
          (Bcap : ℝ), 0 < Bcap → (∀ᵐ z : ℝ ∂rho, |z| ≤ Bcap) →
          (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
          ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), 16 ≤ x →
            Bcap ≤ Real.sqrt (n : ℝ) / (200 * x) →
            let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
            let delta : ℝ := beta / Real.sqrt (n : ℝ)
            delta * (1 + x) ^ 3 ≤ Real.exp (-3 * x ^ 2) →
            let h0 : ℝ := 4 * beta ^ 2
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
            ∀ (nu : Shao.Path n → LabelPerm n → ℕ),
              (∀ sigma, Measurable (fun a => nu a sigma)) →
              (∀ a sigma, nu a sigma ≤ energyCutoff a h0 sigma) →
              let bill : Shao.Path n × LabelPerm n → ℝ := fun p =>
                ∑ r : Fin n, |actualDoubleRetained Q x p.1 (nu p.1) r.val p.2|
              let signedBill : Shao.Path n × LabelPerm n → ℝ := fun p =>
                ∑ r : Fin n, actualDoubleRetained Q x p.1 (nu p.1) r.val p.2
              Measurable bill ∧ Integrable bill (revealLaw P) ∧
                (∀ p, 0 ≤ bill p) ∧
                Measurable signedBill ∧ Integrable signedBill (revealLaw P) ∧
                (∫ p, bill p ∂revealLaw P) ≤ C * delta * Shao.standardNormalTail x ∧
                |∫ p, signedBill p ∂revealLaw P| ≤ C * delta * Shao.standardNormalTail x
    := by
  classical
  obtain ⟨CP, hCP, hPreBudget⟩ :=
    Shao.Probability.SourceRegularRetainedProbability.iid_actual_regular_retained_probability_budget
  obtain ⟨CB, hCB, hBadBudget⟩ := iid_actual_bad_retained_allranks_budget
  obtain ⟨CE, hCE, hEarlyBudget⟩ := iid_actual_early_postwall_retained_budget
  obtain ⟨CL, hCL, hLateBudget⟩ := iid_actual_late_regular_postwall_retained_budget
  let KT : ℝ := (8 / 3) * 2 ^ 11 * 720 / (3 / 10 : ℝ) ^ 6
  have hKT : 0 < KT := by norm_num [KT]
  let C : ℝ := 1 + CP + CB + 2 * KT * (CE + CL)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro ΩB hΩB PB hPB Bm hBm Q rho hProb Bcap hB hsupport hmean hsecond
    n hn x hx hscale beta delta hres h0 P nu hnum hcap bill signedBill
  letI : IsProbabilityMeasure rho := hProb
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  letI : IsProbabilityMeasure (revealLaw P) := by unfold revealLaw; infer_instance
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw Bm PB hBm
  have hx0 : 0 < x := by linarith only [hx]
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hPow (k : ℕ) : Integrable (fun z : ℝ => |z| ^ k) rho := by
    apply (integrable_const (Bcap ^ k)).mono'
      ((continuous_abs.measurable.pow_const k).aestronglyMeasurable)
    filter_upwards [hsupport] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg z) k)]
    exact pow_le_pow_left₀ (abs_nonneg z) hz k
  have h2 : Integrable (fun z : ℝ => z ^ 2) rho := by simpa only [sq_abs] using hPow 2
  have h3 : Integrable (fun z : ℝ => |z| ^ 3) rho := hPow 3
  have hbeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one rho h2 h3 hsecond
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact div_pos (lt_of_lt_of_le zero_lt_one hbeta)
      (Real.sqrt_pos.2 (by exact_mod_cast hn))
  have htail : 0 ≤ Shao.standardNormalTail x :=
    (Shao.standardNormalTail_basic.2.2.1 x).1.le
  have hthree : (3 / 2 : ℝ) * x = 3 * x / 2 := by ring
  have hscale100 : Bcap ≤ Real.sqrt (n : ℝ) / (100 * x) := by
    apply hscale.trans
    apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity)
    linarith only [hx0]
  let Fx : ℝ := (1 + x) ^ 10 * Real.exp (-(4 / 5 : ℝ) * x ^ 2)
  have hFx : 0 < Fx := by dsimp only [Fx]; positivity
  -- Literal Gaussian tail payment, with a universal numerical constant.
  have hTailF : Fx ≤ KT * Shao.standardNormalTail x := by
    have hrev : (1 / 2 : ℝ) ≤ (4 / 3 : ℝ) * (1 + x) *
        Real.exp (x ^ 2 / 2) * Shao.standardNormalTail x := by
      simpa only [Shao.standardNormalTail_basic.2.1,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, div_one, sub_zero] using
        Shao.standardNormalTail_ratio_bound x 0 hx0.le (by norm_num)
    have hGaussian : Real.exp (-x ^ 2 / 2) ≤
        (8 / 3 : ℝ) * (1 + x) * Shao.standardNormalTail x := by
      have hh := mul_le_mul_of_nonneg_left hrev (Real.exp_nonneg (-x ^ 2 / 2))
      have he : Real.exp (-x ^ 2 / 2) * Real.exp (x ^ 2 / 2) = 1 := by
        rw [← Real.exp_add]
        convert Real.exp_zero using 1 <;> ring
      have hh' : Real.exp (-x ^ 2 / 2) * (1 / 2 : ℝ) ≤
          (4 / 3 : ℝ) * (1 + x) * Shao.standardNormalTail x := by
        calc
          _ ≤ Real.exp (-x ^ 2 / 2) *
              ((4 / 3 : ℝ) * (1 + x) * Real.exp (x ^ 2 / 2) * Shao.standardNormalTail x) := hh
          _ = (4 / 3 : ℝ) * (1 + x) *
              (Real.exp (-x ^ 2 / 2) * Real.exp (x ^ 2 / 2)) * Shao.standardNormalTail x := by ring
          _ = _ := by rw [he]; ring
      linarith only [hh']
    let u : ℝ := (3 / 10 : ℝ) * x ^ 2
    have hu : 0 < u := by dsimp only [u]; positivity
    have he6 : u ^ 6 / 720 ≤ Real.exp u := by
      simpa only [show (6 : ℕ).factorial = 720 by norm_num, Nat.cast_ofNat] using
        Real.pow_div_factorial_le_exp u hu.le 6
    have heCancel : Real.exp u * Real.exp (-u) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hPay : x ^ 12 * Real.exp (-u) ≤ 720 / (3 / 10 : ℝ) ^ 6 := by
      have hh := mul_le_mul_of_nonneg_right he6 (Real.exp_nonneg (-u))
      rw [heCancel] at hh
      have hnorm : (u ^ 6 / 720 * Real.exp (-u)) *
          (720 / (3 / 10 : ℝ) ^ 6) = x ^ 12 * Real.exp (-u) := by
        dsimp only [u]
        ring
      calc
        _ = (u ^ 6 / 720 * Real.exp (-u)) * (720 / (3 / 10 : ℝ) ^ 6) := hnorm.symm
        _ ≤ 1 * (720 / (3 / 10 : ℝ) ^ 6) := mul_le_mul_of_nonneg_right hh (by norm_num)
        _ = _ := one_mul _
    have hpoly : (1 + x) ^ 11 ≤ 2 ^ 11 * x ^ 12 := by
      have hh : (1 + x) ^ 11 ≤ (2 * x) ^ 11 :=
        pow_le_pow_left₀ (by linarith only [hx0]) (by linarith only [hx1]) 11
      have hxpow : x ^ 11 ≤ x ^ 12 := by
        calc
          _ ≤ x ^ 11 * x := le_mul_of_one_le_right (pow_nonneg hx0.le 11) hx1
          _ = _ := by ring
      calc
        _ ≤ (2 * x) ^ 11 := hh
        _ = 2 ^ 11 * x ^ 11 := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hxpow (by norm_num)
    have hpolyPay : (1 + x) ^ 11 * Real.exp (-u) ≤
        2 ^ 11 * (720 / (3 / 10 : ℝ) ^ 6) := by
      calc
        _ ≤ (2 ^ 11 * x ^ 12) * Real.exp (-u) :=
          mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg _)
        _ = 2 ^ 11 * (x ^ 12 * Real.exp (-u)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hPay (by norm_num)
    have hsplit : Real.exp (-(4 / 5 : ℝ) * x ^ 2) =
        Real.exp (-u) * Real.exp (-x ^ 2 / 2) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [u]
      ring
    calc
      Fx = ((1 + x) ^ 10 * Real.exp (-u)) * Real.exp (-x ^ 2 / 2) := by
        dsimp only [Fx]
        rw [hsplit]
        ring
      _ ≤ ((1 + x) ^ 10 * Real.exp (-u)) *
          ((8 / 3 : ℝ) * (1 + x) * Shao.standardNormalTail x) :=
        mul_le_mul_of_nonneg_left hGaussian (by positivity)
      _ = (8 / 3 : ℝ) * ((1 + x) ^ 11 * Real.exp (-u)) * Shao.standardNormalTail x := by ring
      _ ≤ (8 / 3 : ℝ) * (2 ^ 11 * (720 / (3 / 10 : ℝ) ^ 6)) * Shao.standardNormalTail x := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpolyPay (by norm_num)) htail
      _ = KT * Shao.standardNormalTail x := by dsimp only [KT]; ring
  have hEarlyTail : Real.exp (-(89 / 100 : ℝ) * x ^ 2) ≤ KT * Shao.standardNormalTail x := by
    apply le_trans _ hTailF
    have hExp := Real.exp_le_exp.mpr
      (by nlinarith only [sq_nonneg x] : -(89 / 100 : ℝ) * x ^ 2 ≤ -(4 / 5 : ℝ) * x ^ 2)
    have hpoly : 1 ≤ (1 + x) ^ 10 := one_le_pow₀ (by linarith only [hx0])
    calc
      _ ≤ Real.exp (-(4 / 5 : ℝ) * x ^ 2) := hExp
      _ ≤ Fx := by
        dsimp only [Fx]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg _)
  let cap : Shao.Path n → LabelPerm n → ℕ := fun a sigma => energyCutoff a h0 sigma
  let RR : (Shao.Path n → LabelPerm n → ℕ) →
      Shao.Path n × LabelPerm n → Fin n → ℝ :=
    fun tau p r => actualDoubleRetained Q x p.1 (tau p.1) r.val p.2
  let A : Shao.Path n × LabelPerm n → Fin n → Prop := fun p r =>
    ∀ k : ℕ, k ≤ r.val →
      |Shao.prefixSum (Shao.Probability.Spitzer.reorder p.1 p.2) k| < actualWall p.1 x
  let Reg : Shao.Path n × LabelPerm n → Fin n → Prop := fun p r =>
    |remainingSum p.1 r.val p.2| ≤ (3 * x / 2) * Real.sqrt (remainingEnergy p.1 r.val p.2)
  let PT : Shao.Path n × LabelPerm n → Fin n → ℝ := fun p r =>
    if r.val < cap p.1 p.2 ∧ A p r ∧ Reg p r then |RR cap p r| else 0
  let BT : Shao.Path n × LabelPerm n → Fin n → ℝ := fun p r =>
    if (3 * x / 2) * Real.sqrt (remainingEnergy p.1 r.val p.2) ≤ |remainingSum p.1 r.val p.2| then
      actualRetainedAbsoluteRank Q p.1 x (nu p.1) r p.2 else 0
  let ET : ℝ → Shao.Path n × LabelPerm n → Fin n → ℝ := fun sign p r =>
    if 2 * r.val < n ∧ actualOppositePrefixHit sign p.1 x r.val p.2 then
      actualPostwallRetainedRank Q sign p.1 x (nu p.1) r p.2 else 0
  let LT : ℝ → Shao.Path n × LabelPerm n → Fin n → ℝ := fun sign p r =>
    if n ≤ 2 * r.val ∧ Reg p r ∧ actualOppositePrefixHit sign p.1 x r.val p.2 then
      actualPostwallRetainedRank Q sign p.1 x (nu p.1) r p.2 else 0
  let Pre : Shao.Path n × LabelPerm n → ℝ := fun p => ∑ r : Fin n, PT p r
  let Bad : Shao.Path n × LabelPerm n → ℝ := fun p => ∑ r : Fin n, BT p r
  let Early : ℝ → Shao.Path n × LabelPerm n → ℝ := fun sign p => ∑ r : Fin n, ET sign p r
  let Late : ℝ → Shao.Path n × LabelPerm n → ℝ := fun sign p => ∑ r : Fin n, LT sign p r
  have hPreData : Measurable Pre ∧ Integrable Pre (revealLaw P) ∧
      (∫ p, Pre p ∂revealLaw P) ≤ CP * delta * Real.exp (-x ^ 2) ∧
      (∫ p, Pre p ∂revealLaw P) ≤ CP * delta * Shao.standardNormalTail x := by
    simpa only [Pre, PT, RR, cap, A, Reg, actualDoubleRetained, actualDerivativeFamily, hthree] using
      hPreBudget PB Bm hBm rho h2 h3 hmean hsecond n hn x hx
  have hBadData : Measurable Bad ∧ Integrable Bad (revealLaw P) ∧
      (∀ p, 0 ≤ Bad p) ∧ (∫ p, Bad p ∂revealLaw P) ≤ CB * delta * Shao.standardNormalTail x := by
    exact hBadBudget PB Bm hBm rho Bcap hB hsupport hmean hsecond n hn x hx
      hscale100 hres nu hnum hcap
  have hEarlyData (sign : ℝ) (hSign : sign = 1 ∨ sign = -1) :
      Measurable (Early sign) ∧ Integrable (Early sign) (revealLaw P) ∧
        (∀ p, 0 ≤ Early sign p) ∧
        (∫ p, Early sign p ∂revealLaw P) ≤ CE * delta * Real.exp (-(89 / 100 : ℝ) * x ^ 2) :=
    hEarlyBudget PB Bm hBm rho Bcap hB hsupport hmean hsecond n hn x hx
      hscale hres nu hnum hcap sign hSign
  have hLateData (sign : ℝ) (hSign : sign = 1 ∨ sign = -1) :
      Measurable (Late sign) ∧ Integrable (Late sign) (revealLaw P) ∧
        (∀ p, 0 ≤ Late sign p) ∧
        (∫ p, Late sign p ∂revealLaw P) ≤ CL * delta * Fx := by
    have h := hLateBudget PB Bm hBm rho Bcap hB hsupport hmean hsecond n hn x hx
      hscale hres nu hnum hcap sign hSign
    have hEq : Late sign = actualLateRegularPostwallRetainedBill Q x sign nu := by
      funext p
      rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hEq]
      exact h.1
    · rw [hEq]
      exact h.2.1
    · intro p
      rw [hEq]
      exact h.2.2.1 p
    · rw [hEq]
      simpa only [Fx, mul_assoc, P, Q, delta, beta] using h.2.2.2
  have heP := hEarlyData 1 (Or.inl rfl)
  have heM := hEarlyData (-1) (Or.inr rfl)
  have hlP := hLateData 1 (Or.inl rfl)
  have hlM := hLateData (-1) (Or.inr rfl)
  -- All literal source terms have genuine L1 before comparison and signed summation.
  have hReflection : Shao.Probability.SourceActualLocalProfileBudget.HalflineReflectionIdentities Q := by
    constructor
    · intro w y T z _hw hT hy hz
      simpa only [Shao.C2.HalfLineReflectionFormula.upperReflection] using
        Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula Bm PB hBm w y T z hT hy hz
    · intro w y T z _hw hT hy hz
      simpa only [Shao.C2.HalfLineReflectionFormula.lowerReflection] using
        Shao.C2.BridgeLowerIdentification.bridge_lower_formula Bm PB hBm w y T z hT hy hz
  have hRegKernel (w y T z : ℝ) (hw : 0 < w) (hT : 0 < T) (hy : |y| < w) (hz : |z| < w) :
      DifferentiableAt ℝ
        (fun Y => Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w Y T z) y :=
    (Shao.C2.BridgeIntervalImageResolved.sourceIntervalCompletion_spatial_hasDerivAt
      Bm PB hBm w y T z hw hy hz hT).differentiableAt
  have hk (J : MonitoredDomain) : Measurable (actualDerivativeFamily Q J) ∧
      KernelBounds J (eventCompletionKernel J Q) (actualDerivativeFamily Q J) 4 := by
    cases J with
    | upper =>
        have hd := Shao.Probability.SourceActualLocalProfileBudget.actual_halfline_kernel_data
          Q hReflection .upper (Or.inl rfl)
        exact ⟨by simpa only [actualDerivativeFamily] using hd.1,
          by simpa only [actualDerivativeFamily] using hd.2.1⟩
    | lower =>
        have hd := Shao.Probability.SourceActualLocalProfileBudget.actual_halfline_kernel_data
          Q hReflection .lower (Or.inr rfl)
        exact ⟨by simpa only [actualDerivativeFamily] using hd.1,
          by simpa only [actualDerivativeFamily] using hd.2.1⟩
    | interval =>
        have hd := Shao.Probability.SourceActualIntervalProfileBudget.actual_interval_kernel_data Q hReflection hRegKernel
        exact ⟨by simpa only [actualDerivativeFamily] using hd.1,
          by simpa only [actualDerivativeFamily] using hd.2.1⟩
  let LJ : (Shao.Path n → LabelPerm n → ℕ) → MonitoredDomain →
      Shao.Path n × LabelPerm n → Fin n → ℝ := fun tau J p r =>
    sourceRetainedRemainder J (eventCompletionKernel J Q) (actualDerivativeFamily Q J)
      p.1 x (tau p.1) r.val p.2
  have hParts (J : MonitoredDomain) := source_parts_measurable_integrable J
    (eventCompletionKernel J Q) (actualDerivativeFamily Q J)
    (eventCompletionKernel_data J Q).1 (hk J).1 4 (hk J).2 P x hx0 nu hnum
  have hLm (J : MonitoredDomain) (r : Fin n) : Measurable (fun p => LJ nu J p r) := by
    apply measurable_from_prod_countable_left
    intro sigma
    exact ((hParts J).1 sigma r.val).1
  have hLi (J : MonitoredDomain) (r : Fin n) : Integrable (fun p => LJ nu J p r) (revealLaw P) :=
    ((hParts J).2.1 r.val).1
  have hRRm (r : Fin n) : Measurable (fun p => RR nu p r) :=
    ((hLm .interval r).sub (hLm .upper r)).sub (hLm .lower r)
  have hRRi (r : Fin n) : Integrable (fun p => RR nu p r) (revealLaw P) :=
    ((hLi .interval r).sub (hLi .upper r)).sub (hLi .lower r)
  have hBillM : Measurable bill := Finset.measurable_sum _ fun r _ => (continuous_abs.measurable.comp (hRRm r))
  have hBillI : Integrable bill (revealLaw P) := integrable_finsetSum _ fun r _ => (hRRi r).abs
  have hBillNN (p : Shao.Path n × LabelPerm n) : 0 ≤ bill p :=
    Finset.sum_nonneg fun r _ => abs_nonneg _
  have hSignedM : Measurable signedBill := Finset.measurable_sum _ fun r _ => hRRm r
  have hSignedI : Integrable signedBill (revealLaw P) := integrable_finsetSum _ fun r _ => hRRi r
  -- The same cap factor multiplies all three signed source terms.
  have hCapFactor (J : MonitoredDomain) (p : Shao.Path n × LabelPerm n) (r : Fin n) :
      LJ nu J p r = if r.val < nu p.1 p.2 then LJ cap J p r else 0 := by
    dsimp only [LJ, sourceRetainedRemainder]
    simp only [dif_pos r.is_lt]
    by_cases hr : r.val < nu p.1 p.2
    · have hrk : r.val < cap p.1 p.2 := lt_of_lt_of_le hr (hcap p.1 p.2)
      simp only [hr, hrk, true_and, if_true]
    · simp only [hr, false_and, if_false]
  have hDoubleCapFactor (p : Shao.Path n × LabelPerm n) (r : Fin n) :
      RR nu p r = if r.val < nu p.1 p.2 then RR cap p r else 0 := by
    change LJ nu .interval p r - LJ nu .upper p r - LJ nu .lower p r = _
    rw [hCapFactor .interval p r, hCapFactor .upper p r, hCapFactor .lower p r]
    by_cases hr : r.val < nu p.1 p.2
    · simp only [if_pos hr]
      rfl
    · simp only [if_neg hr, sub_self]
  have hLive (J : MonitoredDomain) (p : Shao.Path n × LabelPerm n) (r : Fin n)
      (hL : LJ nu J p r ≠ 0) : sourceAlive J p.1 x r.val p.2 := by
    by_contra hd
    apply hL
    dsimp only [LJ, sourceRetainedRemainder]
    rw [dif_pos r.is_lt, if_neg (by tauto)]
  have hDeadInterval (p : Shao.Path n × LabelPerm n) (r : Fin n)
      (hA : ¬A p r) : LJ nu .interval p r = 0 := by
    by_contra hL
    have ha := hLive .interval p r hL
    apply hA
    intro k hk
    exact abs_lt.2 (ha.2.2 k hk)
  have hUpperOpp (p : Shao.Path n × LabelPerm n) (r : Fin n)
      (hA : ¬A p r) (hL : LJ nu .upper p r ≠ 0) :
      actualOppositePrefixHit 1 p.1 x r.val p.2 := by
    have ha := hLive .upper p r hL
    have hw : 0 < actualWall p.1 x := by
      dsimp only [actualWall]
      exact mul_pos hx0 (Real.sqrt_pos.2 ha.1)
    have hex : ∃ k : ℕ, k ≤ r.val ∧
        actualWall p.1 x ≤ |Shao.prefixSum (Shao.Probability.Spitzer.reorder p.1 p.2) k| := by
      by_contra hnone
      apply hA
      intro k hk
      apply lt_of_not_ge
      intro hge
      exact hnone ⟨k, hk, hge⟩
    rcases hex with ⟨k, hkr, hge⟩
    have hk0 : 0 < k := by
      by_contra hk
      have hkz : k = 0 := by omega
      rw [hkz, Shao.prefixSum_zero, abs_zero] at hge
      exact (not_le_of_gt hw) hge
    have hu : Shao.prefixSum (Shao.Probability.Spitzer.reorder p.1 p.2) k < actualWall p.1 x :=
      ha.2.2 k hkr
    have hl : Shao.prefixSum (Shao.Probability.Spitzer.reorder p.1 p.2) k ≤ -actualWall p.1 x := by
      by_contra hh
      have habs : |Shao.prefixSum (Shao.Probability.Spitzer.reorder p.1 p.2) k| < actualWall p.1 x :=
        abs_lt.2 ⟨lt_of_not_ge hh, hu⟩
      exact (not_lt_of_ge hge) habs
    exact ⟨⟨k, by omega⟩, hk0, by simpa only [one_mul] using hl⟩
  have hLowerOpp (p : Shao.Path n × LabelPerm n) (r : Fin n)
      (hA : ¬A p r) (hL : LJ nu .lower p r ≠ 0) :
      actualOppositePrefixHit (-1) p.1 x r.val p.2 := by
    have ha := hLive .lower p r hL
    have hw : 0 < actualWall p.1 x := by
      dsimp only [actualWall]
      exact mul_pos hx0 (Real.sqrt_pos.2 ha.1)
    have hex : ∃ k : ℕ, k ≤ r.val ∧
        actualWall p.1 x ≤ |Shao.prefixSum (Shao.Probability.Spitzer.reorder p.1 p.2) k| := by
      by_contra hnone
      apply hA
      intro k hk
      apply lt_of_not_ge
      intro hge
      exact hnone ⟨k, hk, hge⟩
    rcases hex with ⟨k, hkr, hge⟩
    have hk0 : 0 < k := by
      by_contra hk
      have hkz : k = 0 := by omega
      rw [hkz, Shao.prefixSum_zero, abs_zero] at hge
      exact (not_le_of_gt hw) hge
    have hl : -actualWall p.1 x < Shao.prefixSum (Shao.Probability.Spitzer.reorder p.1 p.2) k :=
      ha.2.2 k hkr
    have hu : actualWall p.1 x ≤ Shao.prefixSum (Shao.Probability.Spitzer.reorder p.1 p.2) k := by
      by_contra hh
      have habs : |Shao.prefixSum (Shao.Probability.Spitzer.reorder p.1 p.2) k| < actualWall p.1 x :=
        abs_lt.2 ⟨hl, lt_of_not_ge hh⟩
      exact (not_lt_of_ge hge) habs
    refine ⟨⟨k, by omega⟩, hk0, ?_⟩
    simpa only [neg_one_mul] using neg_le_neg hu
  have hUpperRank (p : Shao.Path n × LabelPerm n) (r : Fin n) :
      actualPostwallRetainedRank Q 1 p.1 x (nu p.1) r p.2 = |LJ nu .upper p r| := by
    simp [actualPostwallRetainedRank, actualPostwallHalfline, LJ]
  have hLowerRank (p : Shao.Path n × LabelPerm n) (r : Fin n) :
      actualPostwallRetainedRank Q (-1) p.1 x (nu p.1) r p.2 = |LJ nu .lower p r| := by
    simp only [actualPostwallRetainedRank, actualPostwallHalfline,
      if_neg (by norm_num : ¬(-1 : ℝ) = 1), LJ]
  have hPostMasks (p : Shao.Path n × LabelPerm n) (r : Fin n) (hA : ¬A p r) :
      |RR nu p r| ≤
        (if actualOppositePrefixHit 1 p.1 x r.val p.2 then
          actualPostwallRetainedRank Q 1 p.1 x (nu p.1) r p.2 else 0) +
        (if actualOppositePrefixHit (-1) p.1 x r.val p.2 then
          actualPostwallRetainedRank Q (-1) p.1 x (nu p.1) r p.2 else 0) := by
    have hU : |LJ nu .upper p r| =
        if actualOppositePrefixHit 1 p.1 x r.val p.2 then
          actualPostwallRetainedRank Q 1 p.1 x (nu p.1) r p.2 else 0 := by
      rw [hUpperRank p r]
      by_cases ho : actualOppositePrefixHit 1 p.1 x r.val p.2
      · rw [if_pos ho]
      · have hz : LJ nu .upper p r = 0 := by
          by_contra hh
          exact ho (hUpperOpp p r hA hh)
        rw [if_neg ho, hz, abs_zero]
    have hD : |LJ nu .lower p r| =
        if actualOppositePrefixHit (-1) p.1 x r.val p.2 then
          actualPostwallRetainedRank Q (-1) p.1 x (nu p.1) r p.2 else 0 := by
      rw [hLowerRank p r]
      by_cases ho : actualOppositePrefixHit (-1) p.1 x r.val p.2
      · rw [if_pos ho]
      · have hz : LJ nu .lower p r = 0 := by
          by_contra hh
          exact ho (hLowerOpp p r hA hh)
        rw [if_neg ho, hz, abs_zero]
    calc
      |RR nu p r| = |-(LJ nu .upper p r + LJ nu .lower p r)| := by
        change |LJ nu .interval p r - LJ nu .upper p r - LJ nu .lower p r| = _
        rw [hDeadInterval p r hA]
        congr 1
        ring
      _ = |LJ nu .upper p r + LJ nu .lower p r| := abs_neg _
      _ ≤ |LJ nu .upper p r| + |LJ nu .lower p r| := abs_add_le _ _
      _ = _ := by rw [hU, hD]
  have hPT0 (p : Shao.Path n × LabelPerm n) (r : Fin n) : 0 ≤ PT p r := by
    dsimp only [PT]
    split_ifs <;> positivity
  have hBT0 (p : Shao.Path n × LabelPerm n) (r : Fin n) : 0 ≤ BT p r := by
    dsimp only [BT, actualRetainedAbsoluteRank]
    split_ifs <;> positivity
  have hET0 (sign : ℝ) (p : Shao.Path n × LabelPerm n) (r : Fin n) : 0 ≤ ET sign p r := by
    dsimp only [ET, actualPostwallRetainedRank]
    split_ifs <;> positivity
  have hLT0 (sign : ℝ) (p : Shao.Path n × LabelPerm n) (r : Fin n) : 0 ≤ LT sign p r := by
    dsimp only [LT, actualPostwallRetainedRank]
    split_ifs <;> positivity
  have hPreTerm (p : Shao.Path n × LabelPerm n) (r : Fin n)
      (ha : A p r) (hrg : Reg p r) : |RR nu p r| ≤ PT p r := by
    rw [hDoubleCapFactor p r]
    by_cases hr : r.val < nu p.1 p.2
    · have hrk : r.val < cap p.1 p.2 := lt_of_lt_of_le hr (hcap p.1 p.2)
      rw [if_pos hr]
      change |RR cap p r| ≤
        if r.val < cap p.1 p.2 ∧ A p r ∧ Reg p r then |RR cap p r| else 0
      rw [if_pos (show r.val < cap p.1 p.2 ∧ A p r ∧ Reg p r from ⟨hrk, ha, hrg⟩)]
    · rw [if_neg hr, abs_zero]
      exact hPT0 p r
  have hMaskSplit (sign : ℝ) (p : Shao.Path n × LabelPerm n) (r : Fin n) (hrg : Reg p r) :
      ET sign p r + LT sign p r =
        if actualOppositePrefixHit sign p.1 x r.val p.2 then
          actualPostwallRetainedRank Q sign p.1 x (nu p.1) r p.2 else 0 := by
    by_cases he : 2 * r.val < n
    · have hl : ¬n ≤ 2 * r.val := by omega
      by_cases ho : actualOppositePrefixHit sign p.1 x r.val p.2 <;>
        simp only [ET, LT, he, hl, ho, hrg, true_and, false_and, if_true, if_false, add_zero]
    · have hl : n ≤ 2 * r.val := by omega
      by_cases ho : actualOppositePrefixHit sign p.1 x r.val p.2 <;>
        simp only [ET, LT, he, hl, ho, hrg, true_and, false_and, if_true, if_false, zero_add]
  have hRankDom (p : Shao.Path n × LabelPerm n) (r : Fin n) :
      |RR nu p r| ≤ PT p r + BT p r + ET 1 p r + ET (-1) p r + LT 1 p r + LT (-1) p r := by
    by_cases hrg : Reg p r
    · by_cases ha : A p r
      · have hh := hPreTerm p r ha hrg
        linarith only [hh, hBT0 p r, hET0 1 p r, hET0 (-1) p r, hLT0 1 p r, hLT0 (-1) p r]
      · have hh : |RR nu p r| ≤ ET 1 p r + ET (-1) p r + LT 1 p r + LT (-1) p r := by
          calc
            _ ≤ (if actualOppositePrefixHit 1 p.1 x r.val p.2 then
                  actualPostwallRetainedRank Q 1 p.1 x (nu p.1) r p.2 else 0) +
                (if actualOppositePrefixHit (-1) p.1 x r.val p.2 then
                  actualPostwallRetainedRank Q (-1) p.1 x (nu p.1) r p.2 else 0) := hPostMasks p r ha
            _ = _ := by rw [← hMaskSplit 1 p r hrg, ← hMaskSplit (-1) p r hrg]; ring
        linarith only [hh, hPT0 p r, hBT0 p r]
    · have hb : (3 * x / 2) * Real.sqrt (remainingEnergy p.1 r.val p.2) ≤
          |remainingSum p.1 r.val p.2| := (lt_of_not_ge hrg).le
      have hh : |RR nu p r| ≤ BT p r := by
        rw [show BT p r = actualRetainedAbsoluteRank Q p.1 x (nu p.1) r p.2 from if_pos hb]
        have htri : |RR nu p r| ≤ |LJ nu .interval p r| + |LJ nu .upper p r| + |LJ nu .lower p r| := by
          change |LJ nu .interval p r - LJ nu .upper p r - LJ nu .lower p r| ≤ _
          exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) (le_refl _))
        have hNeg : 0 ≤ max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
            p.1 x (nu p.1) r.val p.2) 0 := le_max_right _ _
        exact htri.trans (by
          dsimp only [actualRetainedAbsoluteRank, LJ]
          linarith only [hNeg])
      linarith only [hh, hPT0 p r, hET0 1 p r, hET0 (-1) p r, hLT0 1 p r, hLT0 (-1) p r]
  have hBillDom (p : Shao.Path n × LabelPerm n) : bill p ≤
      Pre p + Bad p + Early 1 p + Early (-1) p + Late 1 p + Late (-1) p := by
    change (∑ r : Fin n, |RR nu p r|) ≤ _
    dsimp only [Pre, Bad, Early, Late]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun r _ => hRankDom p r
  have hiPB : Integrable (fun p => Pre p + Bad p) (revealLaw P) := by
    convert hPreData.2.1.add hBadData.2.1 using 1
  have hiE1 : Integrable (fun p => Pre p + Bad p + Early 1 p) (revealLaw P) := by
    convert hiPB.add heP.2.1 using 1
  have hiE2 : Integrable (fun p => Pre p + Bad p + Early 1 p + Early (-1) p) (revealLaw P) := by
    convert hiE1.add heM.2.1 using 1
  have hiL1 : Integrable (fun p => Pre p + Bad p + Early 1 p + Early (-1) p + Late 1 p)
      (revealLaw P) := by
    convert hiE2.add hlP.2.1 using 1
  have hiAll : Integrable (fun p => Pre p + Bad p + Early 1 p + Early (-1) p + Late 1 p + Late (-1) p)
      (revealLaw P) := by
    convert hiL1.add hlM.2.1 using 1
  have hBillPay : (∫ p, bill p ∂revealLaw P) ≤ C * delta * Shao.standardNormalTail x := by
    calc
      _ ≤ ∫ p, Pre p + Bad p + Early 1 p + Early (-1) p + Late 1 p + Late (-1) p ∂revealLaw P :=
        integral_mono hBillI hiAll hBillDom
      _ = (∫ p, Pre p ∂revealLaw P) + (∫ p, Bad p ∂revealLaw P) +
          (∫ p, Early 1 p ∂revealLaw P) + (∫ p, Early (-1) p ∂revealLaw P) +
          (∫ p, Late 1 p ∂revealLaw P) + (∫ p, Late (-1) p ∂revealLaw P) := by
        rw [integral_add hiL1 hlM.2.1, integral_add hiE2 hlP.2.1,
          integral_add hiE1 heM.2.1, integral_add hiPB heP.2.1,
          integral_add hPreData.2.1 hBadData.2.1]
      _ ≤ CP * delta * Shao.standardNormalTail x + CB * delta * Shao.standardNormalTail x +
          2 * CE * delta * Real.exp (-(89 / 100 : ℝ) * x ^ 2) + 2 * CL * delta * Fx := by
        linarith only [hPreData.2.2.2, hBadData.2.2.2,
          heP.2.2.2, heM.2.2.2, hlP.2.2.2, hlM.2.2.2]
      _ ≤ CP * delta * Shao.standardNormalTail x + CB * delta * Shao.standardNormalTail x +
          2 * CE * delta * (KT * Shao.standardNormalTail x) +
            2 * CL * delta * (KT * Shao.standardNormalTail x) := by
        have he := mul_le_mul_of_nonneg_left hEarlyTail (show 0 ≤ 2 * CE * delta by positivity)
        have hl := mul_le_mul_of_nonneg_left hTailF (show 0 ≤ 2 * CL * delta by positivity)
        exact add_le_add (add_le_add (le_refl _) he) hl
      _ = (CP + CB + 2 * KT * (CE + CL)) * delta * Shao.standardNormalTail x := by ring
      _ ≤ C * delta * Shao.standardNormalTail x := by
        have hh := mul_le_mul_of_nonneg_right
          (show CP + CB + 2 * KT * (CE + CL) ≤ C by dsimp only [C]; linarith)
          (mul_nonneg hdelta.le htail)
        convert hh using 1 <;> ring
  refine ⟨hBillM, hBillI, hBillNN, hSignedM, hSignedI, hBillPay, ?_⟩
  calc
    |∫ p, signedBill p ∂revealLaw P| ≤ ∫ p, |signedBill p| ∂revealLaw P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm signedBill
    _ ≤ ∫ p, bill p ∂revealLaw P := integral_mono hSignedI.abs hBillI
      (fun p => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ C * delta * Shao.standardNormalTail x := hBillPay

end Shao.C2.ActualAllRetainedDoubleBudget
