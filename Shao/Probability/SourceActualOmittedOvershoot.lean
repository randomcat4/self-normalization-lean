/-
Proposal v1: declarations only, no proof bodies and no production source.
Sole prospective module: Shao.Probability.SourceActualOmittedOvershoot.
The late actual retained/negative producer is an explicitly pending-qualified
dependency; this proposal does not treat it as an accepted theorem.
The sole public head pays actual omitted nonnegative wall overshoots,
the interval positive part, and the full absolute interval source remainder.
-/
import Shao.Probability.SourceActualAdaptiveTerminal
import Shao.Probability.SourceEarlyRetainedProbability
import Shao.Probability.SourceActualLateOmittedBudget
import Shao.Probability.SourceSeparatedOvershoot
import Shao.Probability.SourceActualIntervalProfileBudget
import Shao.C2.BridgeIntervalImageResolved
import Shao.C2.AdaptiveRevealCutoff
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
noncomputable section
namespace Shao.Probability.SourceActualOmittedOvershoot
open MeasureTheory ProbabilityTheory
open SourcePermutationReveal SourceSeparatedOvershoot
open SourceActualLocalProfileBudget SourceActualIntervalProfileBudget
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open scoped BigOperators Classical NNReal

local instance labelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

/- Sole new declaration. Necessary stopping-window identities, actual kernel
data, source measurability and finite-sum calculations are local haves inside
this proof; no generic B/E/telescope wrapper or auxiliary public head is proposed.

All displayed lets are part of the proposed frozen statement. The nonnegative
totalCost pays four concrete costs simultaneously, so its three bounds also
bound each actual upper/lower omitted overshoot, the interval positive part,
and the full absolute interval remainder separately.
-/
theorem iid_actual_omitted_overshoot_and_interval_budget :
    let K : ℝ := (2 : ℝ) ^ 64
    ∃ C : ℝ, 0 < C ∧
      ∀ {ΩB : Type*} [MeasurableSpace ΩB]
        (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : ℝ≥0 → ΩB → ℝ), IsBrownianReal B PB →
        let Q : Measure BridgeNoise := bridgeLaw B PB
        ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
          (Bcap : ℝ), 0 < Bcap → (∀ᵐ z : ℝ ∂rho, |z| ≤ Bcap) →
          (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
          ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), 16 ≤ x →
            Bcap ≤ Real.sqrt (n : ℝ) / (200 * x) →
            let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
            let delta : ℝ := beta / Real.sqrt (n : ℝ)
            let u : ℝ := delta * (1 + x) ^ 3
            u ≤ Real.exp (-3 * x ^ 2) →
            let h0 : ℝ := 4 * beta ^ 2
            let H : ℝ := K * beta ^ 2 * (1 + x) ^ 6
            let m : ℕ := ⌈H⌉₊
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
            let nu : Shao.Path n → LabelPerm n → ℕ :=
              fun a sigma => energyCutoff a h0 sigma
            let tau : Shao.Path n → LabelPerm n → ℕ := fun a sigma =>
              min (energyCutoff a H sigma) (n - m)
            let F : MonitoredDomain → BridgeKernel := fun J => eventCompletionKernel J Q
            let FY : MonitoredDomain → BridgeKernel := fun J =>
              match J with
              | .upper => halflineDerivative .upper
              | .lower => halflineDerivative .lower
              | .interval => intervalDerivative Q
            let O : MonitoredDomain → (Shao.Path n × LabelPerm n) → Fin n → ℝ :=
              fun J p r => sourceSeparatedOvershoot J (FY J)
                p.1 x (nu p.1) r.val p.2
            let omittedOvershoot : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ :=
              fun J p => ∑ r : Fin n,
                if tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then O J p r else 0
            let intervalPositive : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
              ∑ r : Fin n,
                if tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then
                  max (O .interval p r) 0 else 0
            let intervalAbsolute : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
              ∑ r : Fin n,
                if tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then
                  |sourceRemainder .interval (F .interval) (FY .interval)
                    p.1 x r.val p.2| else 0
            let totalCost : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
              omittedOvershoot .upper p + omittedOvershoot .lower p +
                intervalPositive p + intervalAbsolute p
            (∀ J : MonitoredDomain,
              Measurable (omittedOvershoot J) ∧
                Integrable (omittedOvershoot J) (revealLaw P)) ∧
              Measurable intervalPositive ∧ Integrable intervalPositive (revealLaw P) ∧
              Measurable intervalAbsolute ∧ Integrable intervalAbsolute (revealLaw P) ∧
              Measurable totalCost ∧ Integrable totalCost (revealLaw P) ∧
              (∀ p : Shao.Path n × LabelPerm n,
                0 ≤ omittedOvershoot .upper p ∧ 0 ≤ omittedOvershoot .lower p ∧
                  0 ≤ intervalPositive p ∧
                  intervalPositive p ≤ omittedOvershoot .upper p + omittedOvershoot .lower p ∧
                  0 ≤ intervalAbsolute p ∧ 0 ≤ totalCost p) ∧
              (∫ p, totalCost p ∂revealLaw P) ≤
                C * beta * Real.sqrt H / (n : ℝ) + C * H / (n : ℝ) ∧
              (∫ p, totalCost p ∂revealLaw P) ≤ C * H / (n : ℝ) ∧
              (∫ p, totalCost p ∂revealLaw P) ≤
                C * delta * Shao.standardNormalTail x := by
  classical
  intro K
  obtain ⟨CE,hCE,hEarly⟩ :=
    SourceEarlyRetainedProbability.iid_actual_early_rare_and_omitted_retained_budget
  obtain ⟨CL,hCL,hLate⟩ :=
    SourceActualLateOmittedBudget.iid_actual_late_omitted_retained_negative_budget
  obtain ⟨CT,hCT,hTerminal⟩ :=
    SourceActualAdaptiveTerminal.iid_actual_adaptive_terminal_budget
  let CB : ℝ := CE + CL
  let C : ℝ := 3 * CB + 12 * CT + 1
  have hCB : 0 < CB := by dsimp [CB]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ΩB mΩB PB hPB B hB Q rho hRho Bcap hBcap hBound hmean hsecond
    n hn x hx hsmall beta delta u hu h0 H m P nu tau F FY O
    omittedOvershoot intervalPositive intervalAbsolute totalCost
  letI : IsProbabilityMeasure rho := hRho
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw B PB hB
  let μ : Measure (Shao.Path n × LabelPerm n) := revealLaw P
  letI : IsProbabilityMeasure P := by dsimp only [P]; infer_instance
  letI : IsProbabilityMeasure μ := by dsimp only [μ,revealLaw]; infer_instance
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hx0 : 0 < x := by linarith only [hx]
  have h2 : Integrable (fun z : ℝ => z^2) rho := by
    refine (integrable_const (Bcap^2)).mono' (by fun_prop) ?_
    filter_upwards [hBound] with z hz
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg z)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z) hz 2
  have h3 : Integrable (fun z : ℝ => |z|^3) rho := by
    refine (integrable_const (Bcap^3)).mono' (by fun_prop) ?_
    filter_upwards [hBound] with z hz
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤|z|^3)]
    exact pow_le_pow_left₀ (abs_nonneg z) hz 3
  have hBeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one rho h2 h3 hsecond
  have hBeta0 : 0 < beta := by linarith only [hBeta]
  have hh0 : 0 < h0 := by dsimp only [h0]; positivity
  have hH : 0 < H := by dsimp only [H,K]; positivity
  have hh0H : h0 ≤ H := by
    have hK4 : (4:ℝ) ≤ K := by norm_num [K]
    have hp : (1:ℝ) ≤ (1+x)^6 := one_le_pow₀ (by linarith only [hx])
    have hK0 : 0 ≤ K := le_trans (by norm_num : (0:ℝ) ≤ 4) hK4
    have hscale : (4:ℝ) ≤ K*(1+x)^6 :=
      hK4.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hK0)
    dsimp only [h0,H]
    nlinarith only [mul_le_mul_of_nonneg_right hscale (sq_nonneg beta)]
  have hnuStop (a : Shao.Path n) : IsRevealStoppingRank (nu a) :=
    (energy_cutoff_data a h0 hh0).1
  have htauData (a : Shao.Path n) :=
    Shao.C2.AdaptiveRevealCutoff.adaptive_cutoff_stopping_and_le a h0 H hh0 hH hh0H m
  have htauStop (a : Shao.Path n) : IsRevealStoppingRank (tau a) := (htauData a).1
  have htauNu (a : Shao.Path n) (sigma : LabelPerm n) : tau a sigma ≤ nu a sigma :=
    (htauData a).2 sigma
  have hnuBound (a : Shao.Path n) (sigma : LabelPerm n) : nu a sigma ≤ n :=
    (hnuStop a).1 sigma
  have htauBound (a : Shao.Path n) (sigma : LabelPerm n) : tau a sigma ≤ n :=
    (htauNu a sigma).trans (hnuBound a sigma)
  have hnuM (sigma : LabelPerm n) : Measurable (fun a : Shao.Path n => nu a sigma) :=
    actual_energy_cutoff_measurable h0 hh0 sigma
  have htauM (sigma : LabelPerm n) : Measurable (fun a : Shao.Path n => tau a sigma) :=
    (actual_energy_cutoff_measurable H hH sigma).min measurable_const
  have hReflection : HalflineReflectionIdentities Q := by
    constructor
    · intro w y T z hw hT hy hz
      exact Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula B PB hB w y T z hT hy hz
    · intro w y T z hw hT hy hz
      exact Shao.C2.BridgeLowerIdentification.bridge_lower_formula B PB hB w y T z hT hy hz
  have hRegular (w y T z : ℝ) (hw : 0<w) (hT : 0<T) (hy : |y|<w) (hz : |z|<w) :
      DifferentiableAt ℝ (fun Y =>
        Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w Y T z) y :=
    (Shao.C2.BridgeIntervalImageResolved.sourceIntervalCompletion_spatial_hasDerivAt
      B PB hB w y T z hw hy hz hT).differentiableAt
  have hFm (J : MonitoredDomain) : Measurable (F J) := (eventCompletionKernel_data J Q).1
  have hData (J : MonitoredDomain) : Measurable (FY J) ∧ KernelBounds J (F J) (FY J) 4 := by
    cases J with
    | upper => exact ⟨(actual_halfline_kernel_data Q hReflection .upper (Or.inl rfl)).1,
        (actual_halfline_kernel_data Q hReflection .upper (Or.inl rfl)).2.1⟩
    | lower => exact ⟨(actual_halfline_kernel_data Q hReflection .lower (Or.inr rfl)).1,
        (actual_halfline_kernel_data Q hReflection .lower (Or.inr rfl)).2.1⟩
    | interval => exact ⟨(actual_interval_kernel_data Q hReflection hRegular).1,
        (actual_interval_kernel_data Q hReflection hRegular).2.1⟩
  have hDeriv (J : MonitoredDomain) (w y T z : ℝ)
      (hw : 0<w) (hT : 0<T) (hy : Interior J w y) (hz : Interior J w z) :
      HasDerivAt (fun s : ℝ => eventCompletionKernel J Q (w,s,T,z))
        (FY J (w,y,T,z)) y := by
    cases J with
    | upper =>
      exact (actual_halfline_kernel_data Q hReflection .upper (Or.inl rfl)).2.2 w y T z hw hT hy hz
    | lower =>
      exact (actual_halfline_kernel_data Q hReflection .lower (Or.inr rfl)).2.2 w y T z hw hT hy hz
    | interval =>
      exact (actual_interval_kernel_data Q hReflection hRegular).2.2
        w y T z hw hT (abs_lt.mpr hy) (abs_lt.mpr hz)
  let L : MonitoredDomain → (Shao.Path n × LabelPerm n) → Fin n → ℝ :=
    fun J p r => sourceRetainedRemainder J (F J) (FY J) p.1 x (nu p.1) r.val p.2
  have hParts (J : MonitoredDomain) := source_parts_measurable_integrable J (F J) (FY J)
    (hFm J) (hData J).1 4 (hData J).2 P x hx0 nu hnuM
  have hLM (J : MonitoredDomain) (r : Fin n) : Measurable (fun p => L J p r) := by
    apply measurable_from_prod_countable_left
    intro sigma
    exact ((hParts J).1 sigma r.val).1
  have hOM (J : MonitoredDomain) (r : Fin n) : Measurable (fun p => O J p r) := by
    apply measurable_from_prod_countable_left
    intro sigma
    exact ((hParts J).1 sigma r.val).2
  have hLI (J : MonitoredDomain) (r : Fin n) : Integrable (fun p => L J p r) μ :=
    ((hParts J).2.1 r.val).1
  have hOI (J : MonitoredDomain) (r : Fin n) : Integrable (fun p => O J p r) μ :=
    ((hParts J).2.1 r.val).2
  have hGuard (r : Fin n) : MeasurableSet {p : Shao.Path n × LabelPerm n |
      tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2} := by
    have hm : Measurable (fun p : Shao.Path n × LabelPerm n =>
        if tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then (1:ℝ) else 0) := by
      apply measurable_from_prod_countable_left
      intro sigma
      exact Measurable.ite ((measurableSet_le (htauM sigma) measurable_const).inter
        (measurableSet_lt measurable_const (hnuM sigma))) measurable_const measurable_const
    simpa only [Set.preimage,Set.mem_singleton_iff,ite_eq_left_iff,zero_ne_one,imp_false,not_not]
      using hm (measurableSet_singleton (1:ℝ))
  have hSelM (r : Fin n) (f : (Shao.Path n × LabelPerm n) → ℝ) (hf : Measurable f) :
      Measurable (fun p => if tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then f p else 0) :=
    hf.ite (hGuard r) measurable_const
  have hSelI (r : Fin n) (f : (Shao.Path n × LabelPerm n) → ℝ) (hf : Integrable f μ) :
      Integrable (fun p => if tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then f p else 0) μ := by
    convert hf.indicator (hGuard r) using 1
    funext p
    simp only [Set.indicator_apply,Set.mem_setOf_eq]
  have hSplit (J : MonitoredDomain) (p : Shao.Path n × LabelPerm n) (r : Fin n)
      (hr : r.val < nu p.1 p.2) :
      sourceRemainder J (F J) (FY J) p.1 x r.val p.2 = L J p r + O J p r := by
    simpa only [if_pos hr] using source_selected_remainder_decomposition J (F J) (FY J)
      p.1 x hx0 (nu p.1) r.val p.2
  have hOSI (J : MonitoredDomain) : Integrable (omittedOvershoot J) μ :=
    integrable_finsetSum _ (fun r _ => hSelI r _ (hOI J r))
  have hOSM (J : MonitoredDomain) : Measurable (omittedOvershoot J) :=
    Finset.measurable_sum _ (fun r _ => hSelM r _ (hOM J r))
  have hPosM : Measurable intervalPositive :=
    Finset.measurable_sum _ (fun r _ => hSelM r _ ((hOM .interval r).max measurable_const))
  have hPosRankI (r : Fin n) : Integrable (fun p => max (O .interval p r) 0) μ := by
    refine (hOI .interval r).abs.mono'
      (((hOM .interval r).max measurable_const).aestronglyMeasurable) ?_
    exact ae_of_all _ fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _)
  have hPosI : Integrable intervalPositive μ :=
    integrable_finsetSum _ (fun r _ => hSelI r _ (hPosRankI r))
  let LS : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ := fun J p =>
    ∑ r : Fin n, if tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then L J p r else 0
  let A : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ := fun J p =>
    ∑ r : Fin n, if tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then |L J p r| else 0
  let N : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
    ∑ r : Fin n, if tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then
      max (-O .interval p r) 0 else 0
  have hLSI (J : MonitoredDomain) : Integrable (LS J) μ :=
    integrable_finsetSum _ (fun r _ => hSelI r _ (hLI J r))
  have hAM (J : MonitoredDomain) : Measurable (A J) :=
    Finset.measurable_sum _ (fun r _ => hSelM r _ (continuous_abs.measurable.comp (hLM J r)))
  have hAI (J : MonitoredDomain) : Integrable (A J) μ :=
    integrable_finsetSum _ (fun r _ => hSelI r _ (hLI J r).abs)
  have hNegRankI (r : Fin n) : Integrable (fun p => max (-O .interval p r) 0) μ := by
    refine (hOI .interval r).abs.mono'
      (((hOM .interval r).neg.max measurable_const).aestronglyMeasurable) ?_
    exact ae_of_all _ fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
      exact max_le (neg_le_abs _) (abs_nonneg _)
  have hNM : Measurable N := Finset.measurable_sum _ fun r _ =>
    hSelM r _ ((hOM .interval r).neg.max measurable_const)
  have hNI : Integrable N μ := integrable_finsetSum _ fun r _ => hSelI r _ (hNegRankI r)
  have hRSelected (r : Fin n) :
      (fun p : Shao.Path n × LabelPerm n =>
        if tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then
          |sourceRemainder .interval (F .interval) (FY .interval) p.1 x r.val p.2| else 0) =
      (fun p => if tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then
        |L .interval p r + O .interval p r| else 0) := by
    funext p
    split_ifs with h
    · rw [hSplit .interval p r h.2]
    · rfl
  have hAbsM : Measurable intervalAbsolute := by
    apply Finset.measurable_sum
    intro r _
    rw [hRSelected r]
    exact hSelM r _ (continuous_abs.measurable.comp ((hLM .interval r).add (hOM .interval r)))
  have hAbsI : Integrable intervalAbsolute μ := by
    apply integrable_finsetSum
    intro r _
    rw [hRSelected r]
    exact hSelI r _ ((hLI .interval r).add (hOI .interval r)).abs
  have hTotalM : Measurable totalCost :=
    (((hOSM .upper).add (hOSM .lower)).add hPosM).add hAbsM
  have hTotalI : Integrable totalCost μ :=
    (((hOSI .upper).add (hOSI .lower)).add hPosI).add hAbsI
  have hSign (p : Shao.Path n × LabelPerm n) (r : Fin n) :=
    source_separated_overshoot_sign_domination Q FY hDeriv p.1 x hx0 (nu p.1) r.val p.2
  have hOS0 (J : MonitoredDomain) (hJ : J=.upper ∨ J=.lower)
      (p : Shao.Path n × LabelPerm n) : 0 ≤ omittedOvershoot J p := by
    apply Finset.sum_nonneg
    intro r _
    split_ifs
    · rcases hJ with rfl | rfl
      · exact (hSign p r).1
      · exact (hSign p r).2.1
    · exact le_rfl
  have hPos0 (p : Shao.Path n × LabelPerm n) : 0 ≤ intervalPositive p := by
    apply Finset.sum_nonneg
    intro r _
    split_ifs
    · exact le_max_right _ _
    · exact le_rfl
  have hAbs0 (p : Shao.Path n × LabelPerm n) : 0 ≤ intervalAbsolute p := by
    apply Finset.sum_nonneg
    intro r _
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl
  have hPosDom (p : Shao.Path n × LabelPerm n) :
      intervalPositive p ≤ omittedOvershoot .upper p + omittedOvershoot .lower p := by
    simp only [intervalPositive,omittedOvershoot,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro r _
    split_ifs
    · exact (hSign p r).2.2.2.1
    · norm_num
  have hA0 (J : MonitoredDomain) (p : Shao.Path n × LabelPerm n) : 0 ≤ A J p := by
    apply Finset.sum_nonneg
    intro r _
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl
  have hN0 (p : Shao.Path n × LabelPerm n) : 0 ≤ N p := by
    apply Finset.sum_nonneg
    intro r _
    split_ifs
    · exact le_max_right _ _
    · exact le_rfl
  have hTotal0 (p : Shao.Path n × LabelPerm n) : 0 ≤ totalCost p :=
    add_nonneg (add_nonneg (add_nonneg (hOS0 .upper (Or.inl rfl) p)
      (hOS0 .lower (Or.inr rfl) p)) (hPos0 p)) (hAbs0 p)
  let Vnu : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ := fun J p =>
    sourceValue J (F J) p.1 x (nu p.1 p.2) p.2
  let Vtau : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ := fun J p =>
    sourceValue J (F J) p.1 x (tau p.1 p.2) p.2
  let Rnu : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ := fun J p =>
    stoppedRemainderSum J (F J) (FY J) p.1 x (nu p.1) p.2
  let Rtau : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ := fun J p =>
    stoppedRemainderSum J (F J) (FY J) p.1 x (tau p.1) p.2
  have hVnuData (J : MonitoredDomain) := source_stopped_integrability J (F J) (FY J)
    (hFm J) (hData J).1 4 (hData J).2 P x hx0 nu hnuM hnuBound
    (fun _ => 1) measurable_const (fun _ => by norm_num)
  have hVtauData (J : MonitoredDomain) := source_stopped_integrability J (F J) (FY J)
    (hFm J) (hData J).1 4 (hData J).2 P x hx0 tau htauM htauBound
    (fun _ => 1) measurable_const (fun _ => by norm_num)
  have hVnuI (J : MonitoredDomain) : Integrable (Vnu J) μ := by
    simpa only [one_mul] using (hVnuData J).1
  have hVtauI (J : MonitoredDomain) : Integrable (Vtau J) μ := by
    simpa only [one_mul] using (hVtauData J).1
  have hRnuI (J : MonitoredDomain) : Integrable (Rnu J) μ := by
    simpa only [one_mul] using (hVnuData J).2.2
  have hRtauI (J : MonitoredDomain) : Integrable (Rtau J) μ := by
    simpa only [one_mul] using (hVtauData J).2.2
  have hRemDiff (J : MonitoredDomain) (p : Shao.Path n × LabelPerm n) :
      Rnu J p - Rtau J p = LS J p + omittedOvershoot J p := by
    dsimp only [Rnu,Rtau,stoppedRemainderSum]
    rw [←Finset.sum_sub_distrib,
      ←Fin.sum_univ_eq_sum_range (fun r : ℕ =>
        (if r < nu p.1 p.2 then sourceRemainder J (F J) (FY J) p.1 x r p.2 else 0) -
          (if r < tau p.1 p.2 then sourceRemainder J (F J) (FY J) p.1 x r p.2 else 0)) n]
    simp only [LS,omittedOvershoot,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    by_cases ht : r.val < tau p.1 p.2
    · have hv : r.val < nu p.1 p.2 := ht.trans_le (htauNu p.1 p.2)
      have hw : ¬(tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2) := by omega
      simp only [if_pos ht,if_pos hv,if_neg hw,sub_self,zero_add]
    · by_cases hv : r.val < nu p.1 p.2
      · have hw : tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 := ⟨by omega,hv⟩
        simp only [if_neg ht,if_pos hv,if_pos hw,sub_zero]
        exact hSplit J p r hv
      · have hw : ¬(tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2) := by tauto
        simp only [if_neg ht,if_neg hv,if_neg hw,sub_self,zero_add]
  have hTel (J : MonitoredDomain) :
      (∫ p, Vnu J p ∂μ) - (∫ p, Vtau J p ∂μ) =
        (∫ p, LS J p ∂μ) + (∫ p, omittedOvershoot J p ∂μ) := by
    have hnTel := source_masked_stopped_telescope_integral J (F J) (FY J)
      (hFm J) (hData J).1 4 (hData J).2 P x hx0 h0 hh0 nu hnuM hnuStop
      (fun _ _ => le_rfl) (fun _ => 1) measurable_const (fun _ => by norm_num)
    have htTel := source_masked_stopped_telescope_integral J (F J) (FY J)
      (hFm J) (hData J).1 4 (hData J).2 P x hx0 h0 hh0 tau htauM htauStop
      htauNu (fun _ => 1) measurable_const (fun _ => by norm_num)
    simp only [one_mul] at hnTel htTel
    have hri : (∫ p, Rnu J p ∂μ) - (∫ p, Rtau J p ∂μ) =
        (∫ p, LS J p ∂μ) + (∫ p, omittedOvershoot J p ∂μ) := by
      calc
        _ = ∫ p, Rnu J p - Rtau J p ∂μ :=
          (integral_sub (hRnuI J) (hRtauI J)).symm
        _ = ∫ p, LS J p + omittedOvershoot J p ∂μ :=
          integral_congr_ae (ae_of_all _ (hRemDiff J))
        _ = _ := integral_add (hLSI J) (hOSI J)
    change (∫ p, Vnu J p ∂μ) -
      (∫ p : Shao.Path n × LabelPerm n, sourceValue J (F J) p.1 x 0 p.2 ∂μ) =
        (∫ p, Rnu J p ∂μ) at hnTel
    change (∫ p, Vtau J p ∂μ) -
      (∫ p : Shao.Path n × LabelPerm n, sourceValue J (F J) p.1 x 0 p.2 ∂μ) =
        (∫ p, Rtau J p ∂μ) at htTel
    linarith only [hnTel,htTel,hri]
  let terminal : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ := fun J p =>
    if sourceAlive J p.1 x n p.2 then 1 else 0
  let discrepancy : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ := fun J p =>
    (Finset.Icc (tau p.1 p.2) n).sup'
      (by exact ⟨n,Finset.mem_Icc.mpr ⟨htauBound p.1 p.2,le_rfl⟩⟩)
      (fun j => |sourceValue J (F J) p.1 x j p.2 - terminal J p|)
  have hTerm (J : MonitoredDomain) := hTerminal PB B hB rho Bcap hBcap hBound hmean hsecond
    n hn x hx hsmall hu J
  have hTermData (J : MonitoredDomain) :
      Measurable (discrepancy J) ∧ Integrable (discrepancy J) μ ∧
        (∫ p, discrepancy J p ∂μ) ≤ CT*H/(n : ℝ) ∧
        (∫ p, discrepancy J p ∂μ) ≤ CT*delta*Shao.standardNormalTail x := hTerm J
  have hDiscLe (J : MonitoredDomain) (p : Shao.Path n × LabelPerm n) (j : ℕ)
      (htj : tau p.1 p.2 ≤ j) (hjn : j ≤ n) :
      |sourceValue J (F J) p.1 x j p.2 - terminal J p| ≤ discrepancy J p :=
    Finset.le_sup' (fun k => |sourceValue J (F J) p.1 x k p.2 - terminal J p|)
      (Finset.mem_Icc.mpr ⟨htj,hjn⟩)
  have hVdiff (J : MonitoredDomain) (p : Shao.Path n × LabelPerm n) :
      Vnu J p - Vtau J p ≤ 2*discrepancy J p := by
    have hv := hDiscLe J p (nu p.1 p.2) (htauNu p.1 p.2) (hnuBound p.1 p.2)
    have ht := hDiscLe J p (tau p.1 p.2) le_rfl (htauBound p.1 p.2)
    have hv' := le_abs_self (Vnu J p - terminal J p)
    have ht' := neg_le_abs (Vtau J p - terminal J p)
    change |Vnu J p - terminal J p| ≤ discrepancy J p at hv
    change |Vtau J p - terminal J p| ≤ discrepancy J p at ht
    linarith only [hv,ht,hv',ht']
  have hVdiffInt (J : MonitoredDomain) :
      (∫ p, Vnu J p ∂μ) - (∫ p, Vtau J p ∂μ) ≤
        2*(∫ p, discrepancy J p ∂μ) := by
    calc
      _ = ∫ p, Vnu J p - Vtau J p ∂μ :=
        (integral_sub (hVnuI J) (hVtauI J)).symm
      _ ≤ ∫ p, 2*discrepancy J p ∂μ :=
        integral_mono ((hVnuI J).sub (hVtauI J)) ((hTermData J).2.1.const_mul 2) (hVdiff J)
      _ = _ := integral_const_mul _ _
  have hNegLS (J : MonitoredDomain) :
      -(∫ p, LS J p ∂μ) ≤ ∫ p, A J p ∂μ := by
    calc
      _ = ∫ p, -LS J p ∂μ := (integral_neg _).symm
      _ ≤ ∫ p, A J p ∂μ := by
        apply integral_mono (hLSI J).neg (hAI J)
        intro p
        simp only [Pi.neg_apply,LS,A,←Finset.sum_neg_distrib]
        apply Finset.sum_le_sum
        intro r _
        split_ifs
        · exact neg_le_abs _
        · simp
  have hWall (J : MonitoredDomain) :
      (∫ p, omittedOvershoot J p ∂μ) ≤
        (∫ p, A J p ∂μ) + 2*(∫ p, discrepancy J p ∂μ) := by
    linarith only [hTel J,hVdiffInt J,hNegLS J]
  let bill : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
    A .interval p + A .upper p + A .lower p + N p
  let rankBill : (Shao.Path n × LabelPerm n) → Fin n → ℝ := fun p r =>
    |L .interval p r| + |L .upper p r| + |L .lower p r| + max (-O .interval p r) 0
  let early : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
    ∑ r : Fin n, if r.val ≤ n/2 ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then
      rankBill p r else 0
  let late : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
    ∑ r : Fin n, if n/2 < r.val ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then
      rankBill p r else 0
  have hEarlyApplied := hEarly PB B hB rho Bcap hBcap hBound hmean hsecond n hn x hx hu
  rcases hEarlyApplied with ⟨_,_,hEM,hEI,_,hEB,hED⟩
  change Measurable early at hEM
  change Integrable early μ at hEI
  change (∫ p, early p ∂μ) ≤ CE*beta*Real.sqrt H/(n : ℝ) at hEB
  change (∫ p, early p ∂μ) ≤ CE*delta*Shao.standardNormalTail x at hED
  have hLateApplied := hLate PB B hB rho Bcap hBcap hBound hmean hsecond n hn x hx hsmall hu
  rcases hLateApplied with ⟨hLateM,hLateI,hLB,hLD⟩
  change Measurable late at hLateM
  change Integrable late μ at hLateI
  change (∫ p, late p ∂μ) ≤ CL*beta*Real.sqrt H/(n : ℝ) at hLB
  change (∫ p, late p ∂μ) ≤ CL*delta*Shao.standardNormalTail x at hLD
  have hBillI : Integrable bill μ :=
    (((hAI .interval).add (hAI .upper)).add (hAI .lower)).add hNI
  have hBillSplit (p : Shao.Path n × LabelPerm n) : bill p = early p + late p := by
    simp only [bill,A,N,early,late,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : r.val ≤ n/2
    · have hr' : ¬n/2 < r.val := by omega
      by_cases hw : tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2
      · simp only [hr,hr',true_and,false_and,if_pos hw,if_false,rankBill,add_zero]
      · simp only [hr,hr',true_and,false_and,if_neg hw,if_false,zero_add]
    · have hr' : n/2 < r.val := by omega
      by_cases hw : tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2
      · simp only [hr,hr',true_and,false_and,if_pos hw,if_false,rankBill,zero_add]
      · simp only [hr,hr',true_and,false_and,if_neg hw,if_false,zero_add]
  have hBillIntSplit : (∫ p, bill p ∂μ) = (∫ p, early p ∂μ) + (∫ p, late p ∂μ) := by
    calc
      _ = ∫ p, early p + late p ∂μ := integral_congr_ae (ae_of_all _ hBillSplit)
      _ = _ := integral_add hEI hLateI
  have hBillB : (∫ p, bill p ∂μ) ≤ CB*beta*Real.sqrt H/(n : ℝ) := by
    rw [hBillIntSplit]
    calc
      _ ≤ CE*beta*Real.sqrt H/(n : ℝ) + CL*beta*Real.sqrt H/(n : ℝ) := add_le_add hEB hLB
      _ = _ := by dsimp only [CB]; ring
  have hBillD : (∫ p, bill p ∂μ) ≤ CB*delta*Shao.standardNormalTail x := by
    rw [hBillIntSplit]
    dsimp only [CB]
    linarith only [hED,hLD]
  have hAbsDom (p : Shao.Path n × LabelPerm n) :
      intervalAbsolute p ≤ A .interval p + N p + intervalPositive p := by
    simp only [intervalAbsolute,A,N,intervalPositive,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro r _
    split_ifs with hw
    · rw [hSplit .interval p r hw.2]
      have hparts : |O .interval p r| = max (-O .interval p r) 0 + max (O .interval p r) 0 := by
        by_cases ho : 0 ≤ O .interval p r
        · rw [abs_of_nonneg ho,max_eq_left ho,max_eq_right (neg_nonpos.mpr ho),zero_add]
        · have ho' : O .interval p r ≤ 0 := (lt_of_not_ge ho).le
          rw [abs_of_nonpos ho',max_eq_right ho',max_eq_left (neg_nonneg.mpr ho'),add_zero]
      have ha := abs_add_le (L .interval p r) (O .interval p r)
      rw [hparts] at ha
      linarith only [ha]
    · norm_num
  have hAbsInt : (∫ p, intervalAbsolute p ∂μ) ≤
      (∫ p, A .interval p ∂μ) + (∫ p, N p ∂μ) + (∫ p, intervalPositive p ∂μ) := by
    calc
      _ ≤ ∫ p, A .interval p + N p + intervalPositive p ∂μ :=
        integral_mono hAbsI (((hAI .interval).add hNI).add hPosI) hAbsDom
      _ = _ := by
        have h1 := integral_add ((hAI .interval).add hNI) hPosI
        have h2 := integral_add (hAI .interval) hNI
        simp only [Pi.add_apply] at h1 h2
        rw [h2] at h1
        exact h1
  have hPosInt : (∫ p, intervalPositive p ∂μ) ≤
      (∫ p, omittedOvershoot .upper p ∂μ) + (∫ p, omittedOvershoot .lower p ∂μ) := by
    calc
      _ ≤ ∫ p, omittedOvershoot .upper p + omittedOvershoot .lower p ∂μ :=
        integral_mono hPosI ((hOSI .upper).add (hOSI .lower)) hPosDom
      _ = _ := integral_add (hOSI .upper) (hOSI .lower)
  have hBillInt : (∫ p, bill p ∂μ) =
      (∫ p, A .interval p ∂μ) + (∫ p, A .upper p ∂μ) +
        (∫ p, A .lower p ∂μ) + (∫ p, N p ∂μ) := by
    change (∫ p, A .interval p + A .upper p + A .lower p + N p ∂μ) = _
    have h1 := integral_add (((hAI .interval).add (hAI .upper)).add (hAI .lower)) hNI
    have h2 := integral_add ((hAI .interval).add (hAI .upper)) (hAI .lower)
    have h3 := integral_add (hAI .interval) (hAI .upper)
    simp only [Pi.add_apply] at h1 h2 h3
    rw [h2,h3] at h1
    exact h1
  have hTotalInt : (∫ p, totalCost p ∂μ) =
      (∫ p, omittedOvershoot .upper p ∂μ) + (∫ p, omittedOvershoot .lower p ∂μ) +
        (∫ p, intervalPositive p ∂μ) + (∫ p, intervalAbsolute p ∂μ) := by
    change (∫ p, omittedOvershoot .upper p + omittedOvershoot .lower p +
      intervalPositive p + intervalAbsolute p ∂μ) = _
    have h1 := integral_add (((hOSI .upper).add (hOSI .lower)).add hPosI) hAbsI
    have h2 := integral_add ((hOSI .upper).add (hOSI .lower)) hPosI
    have h3 := integral_add (hOSI .upper) (hOSI .lower)
    simp only [Pi.add_apply] at h1 h2 h3
    rw [h2,h3] at h1
    exact h1
  have hTotalPaid : (∫ p, totalCost p ∂μ) ≤ 3*(∫ p, bill p ∂μ) +
      6*(∫ p, discrepancy .upper p ∂μ) + 6*(∫ p, discrepancy .lower p ∂μ) := by
    have hAint0 : 0 ≤ ∫ p, A .interval p ∂μ := integral_nonneg (hA0 .interval)
    have hNint0 : 0 ≤ ∫ p, N p ∂μ := integral_nonneg hN0
    linarith only [hTotalInt,hBillInt,hAbsInt,hPosInt,hWall .upper,hWall .lower,hAint0,hNint0]
  have hMixed : (∫ p, totalCost p ∂μ) ≤
      C*beta*Real.sqrt H/(n : ℝ) + C*H/(n : ℝ) := by
    have hs : 0 ≤ beta*Real.sqrt H/(n : ℝ) := by positivity
    have ht : 0 ≤ H/(n : ℝ) := by positivity
    have hb := hBillB
    have hu := (hTermData .upper).2.2.1
    have hl := (hTermData .lower).2.2.1
    have hbase : (∫ p, totalCost p ∂μ) ≤
        3*CB*(beta*Real.sqrt H/(n : ℝ)) + 12*CT*(H/(n : ℝ)) := by
      calc
        _ ≤ 3*(∫ p, bill p ∂μ) + 6*(∫ p, discrepancy .upper p ∂μ) +
            6*(∫ p, discrepancy .lower p ∂μ) := hTotalPaid
        _ ≤ 3*(CB*beta*Real.sqrt H/(n : ℝ)) + 6*(CT*H/(n : ℝ)) + 6*(CT*H/(n : ℝ)) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left hb (by norm_num))
            (mul_le_mul_of_nonneg_left hu (by norm_num)))
            (mul_le_mul_of_nonneg_left hl (by norm_num))
        _ = _ := by ring
    have hc1 : 3*CB ≤ C := by dsimp only [C]; linarith only [hCT]
    have hc2 : 12*CT ≤ C := by dsimp only [C]; linarith only [hCB]
    calc
      _ ≤ 3*CB*(beta*Real.sqrt H/(n : ℝ)) + 12*CT*(H/(n : ℝ)) := hbase
      _ ≤ C*(beta*Real.sqrt H/(n : ℝ)) + C*(H/(n : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_right hc1 hs) (mul_le_mul_of_nonneg_right hc2 ht)
      _ = _ := by ring
  have hHBound : (∫ p, totalCost p ∂μ) ≤ C*H/(n : ℝ) := by
    have hsqrt : 0 ≤ Real.sqrt H := Real.sqrt_nonneg H
    have hsq : (Real.sqrt H)^2 = H := Real.sq_sqrt hH.le
    have hbH : beta*Real.sqrt H ≤ H/2 := by
      change 4*beta^2 ≤ H at hh0H
      have hs2 : 2*beta ≤ Real.sqrt H := by nlinarith only [hh0H,hsq,hBeta0,hsqrt]
      nlinarith only [mul_le_mul_of_nonneg_right hs2 hsqrt,hsq]
    have hbRate : beta*Real.sqrt H/(n : ℝ) ≤ (H/(n : ℝ))/2 := by
      have hh := div_le_div_of_nonneg_right hbH hnR.le
      convert hh using 1 <;> ring
    have hB : (∫ p, bill p ∂μ) ≤ CB*(H/(n : ℝ))/2 := by
      calc
        _ ≤ CB*beta*Real.sqrt H/(n : ℝ) := hBillB
        _ = CB*(beta*Real.sqrt H/(n : ℝ)) := by ring
        _ ≤ CB*((H/(n : ℝ))/2) := mul_le_mul_of_nonneg_left hbRate hCB.le
        _ = _ := by ring
    have ht : 0 ≤ H/(n : ℝ) := by positivity
    have hbase : (∫ p, totalCost p ∂μ) ≤
        (3*CB/2+12*CT)*(H/(n : ℝ)) := by
      calc
        _ ≤ 3*(∫ p, bill p ∂μ) + 6*(∫ p, discrepancy .upper p ∂μ) +
            6*(∫ p, discrepancy .lower p ∂μ) := hTotalPaid
        _ ≤ 3*(CB*(H/(n : ℝ))/2) + 6*(CT*H/(n : ℝ)) + 6*(CT*H/(n : ℝ)) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left hB (by norm_num))
            (mul_le_mul_of_nonneg_left (hTermData .upper).2.2.1 (by norm_num)))
            (mul_le_mul_of_nonneg_left (hTermData .lower).2.2.1 (by norm_num))
        _ = _ := by ring
    have hc : 3*CB/2+12*CT ≤ C := by dsimp only [C]; linarith only [hCB]
    calc
      _ ≤ (3*CB/2+12*CT)*(H/(n : ℝ)) := hbase
      _ ≤ C*(H/(n : ℝ)) := mul_le_mul_of_nonneg_right hc ht
      _ = _ := by ring
  have hDeltaBound : (∫ p, totalCost p ∂μ) ≤ C*delta*Shao.standardNormalTail x := by
    have hdelta0 : 0 ≤ delta := by dsimp only [delta]; positivity
    have htail0 : 0 ≤ Shao.standardNormalTail x := by
      dsimp only [Shao.standardNormalTail]
      exact ENNReal.toReal_nonneg
    have hrate0 : 0 ≤ delta*Shao.standardNormalTail x := mul_nonneg hdelta0 htail0
    have hbase : (∫ p, totalCost p ∂μ) ≤ (3*CB+12*CT)*(delta*Shao.standardNormalTail x) := by
      nlinarith only [hTotalPaid,hBillD,(hTermData .upper).2.2.2,(hTermData .lower).2.2.2]
    have hc : 3*CB+12*CT ≤ C := by dsimp only [C]; linarith
    calc
      _ ≤ (3*CB+12*CT)*(delta*Shao.standardNormalTail x) := hbase
      _ ≤ C*(delta*Shao.standardNormalTail x) := mul_le_mul_of_nonneg_right hc hrate0
      _ = _ := by ring
  refine ⟨(fun J => ⟨hOSM J,hOSI J⟩),hPosM,hPosI,hAbsM,hAbsI,hTotalM,hTotalI,?_,
    hMixed,hHBound,hDeltaBound⟩
  intro p
  exact ⟨hOS0 .upper (Or.inl rfl) p,hOS0 .lower (Or.inr rfl) p,hPos0 p,hPosDom p,hAbs0 p,hTotal0 p⟩
end Shao.Probability.SourceActualOmittedOvershoot
