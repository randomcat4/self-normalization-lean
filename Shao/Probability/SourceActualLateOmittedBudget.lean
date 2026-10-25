/-
Implementation attempt v1, 2026-10-25, exact Root-frozen declarations.
Proof bodies are uncompiled; this is NOT an accepted theorem.
Intended sole new production module:
  Shao.Probability.SourceActualLateOmittedBudget
Root freeze: coordination/actual-late-omitted-budget-root-freeze-v1.json.

Scope: genuine late omitted three-domain sourceRetainedRemainder absolute
bills and interval sourceSeparatedOvershoot negative bill, under the original
bounded auxiliary iid law, actual Brownian bridge, same sigma/tau/nu and
strict/closed source boundaries. No target Taylor or target probability premise.
-/
import Shao.Probability.SourceLateOmittedSuffixBudget
import Shao.Probability.SourceWeightedPrefixWall
import Shao.Probability.SourceActualIntervalProfileBudget
import Shao.Probability.SourceIIDGaussianProfileBudget
import Shao.Probability.QuadraticEnergyLowerTail
import Shao.C2.BridgeIntervalImageResolved
import Shao.C2.BridgeHalfLineRetainedBound
import Shao.C2.AdaptiveRevealCutoff
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
noncomputable section
namespace Shao.Probability.SourceActualLateOmittedBudget
open MeasureTheory ProbabilityTheory
open SourcePermutationReveal SourceSeparatedOvershoot
open SourceActualLocalProfileBudget SourceActualIntervalProfileBudget
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open scoped BigOperators Classical NNReal

local instance labelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

/- Necessary private declaration 1.
The interval counterpart of accepted actual_halfline_retained_rank_domination.
The only analytic input is the actual Brownian/C2 bound, not Csmall as a premise.
-/
private theorem alo_actual_interval_rank_domination
    {ΩB : Type*} [MeasurableSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → ℝ) (hB : IsBrownianReal B PB)
    {n : ℕ} (a : Shao.Path n) (h0 x : ℝ) (hh0 : 0 < h0) (hx : 0 < x)
    (nu : LabelPerm n → ℕ) (sigma : LabelPerm n)
    (hcap : nu sigma ≤ energyCutoff a h0 sigma) (r : Fin n) :
    let Q : Measure BridgeNoise := bridgeLaw B PB
    let F : BridgeKernel := eventCompletionKernel .interval Q
    let FY : BridgeKernel := intervalDerivative Q
    |sourceRetainedRemainder .interval F FY a x nu r.val sigma| +
        max (-sourceSeparatedOvershoot .interval FY a x nu r.val sigma) 0 ≤
      (2 * Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant + 40) *
        SourceIIDGaussianProfileBudget.rankGaussianWeight h0 x
          (wallSigns .interval) false (Spitzer.reorder a sigma) r
 := by
  classical
  intro Q F FY
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw B PB hB
  have hReflection : HalflineReflectionIdentities Q := by
    constructor
    · intro w y T z hw hT hy hz
      exact Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula B PB hB w y T z hT hy hz
    · intro w y T z hw hT hy hz
      exact Shao.C2.BridgeLowerIdentification.bridge_lower_formula B PB hB w y T z hT hy hz
  have hRegular (w y T z : ℝ) (hw : 0 < w) (hT : 0 < T)
      (hy : |y| < w) (hz : |z| < w) :
      DifferentiableAt ℝ (fun Y =>
        Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w Y T z) y :=
    (Shao.C2.BridgeIntervalImageResolved.sourceIntervalCompletion_spatial_hasDerivAt
      B PB hB w y T z hw hy hz hT).differentiableAt
  have hKernel := actual_interval_kernel_data Q hReflection hRegular
  let w : ℝ := actualWall a x
  let y : ℝ := Shao.prefixSum (Spitzer.reorder a sigma) r.val
  let T : ℝ := remainingEnergy a r.val sigma
  let z : ℝ := Shao.prefixSum a n
  let b : ℝ := a (sigma r)
  have hNN : 0 ≤ SourceIIDGaussianProfileBudget.rankGaussianWeight h0 x
      (wallSigns .interval) false (Spitzer.reorder a sigma) r :=
    ((SourceIIDGaussianProfileBudget.fixed_gaussian_weight_measurable_bound
      r.val (n-r.val) h0 x (wallSigns .interval) false).2.1 _ _).1
  have hCI : 0 ≤ 2 * Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant + 40 := by
    have hh := Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant_nonneg
    linarith
  by_cases hact : r.val < nu sigma ∧ sourceAlive .interval a x r.val sigma ∧ 0 < T
  · have hw : 0 < w := mul_pos hx (Real.sqrt_pos.2 hact.2.1.1)
    have hy : |y| < w := abs_lt.mpr (hact.2.1.2.2 r.val le_rfl)
    have hz : |z| < w := abs_lt.mpr hact.2.1.2.1
    have hT : 0 < T := hact.2.2
    have hcut : h0 ≤ T := ((energy_cutoff_data a h0 hh0).2.2 sigma r.val
      (hact.1.trans_le hcap)).2
    have hb : b ^ 2 ≤ T :=
      (remaining_population_geometry a r.val r.is_lt.le sigma).2.2.1 r le_rfl
    have hzero : T - b ^ 2 = 0 → y + b = z := actual_reveal_zero_future_reachable a r sigma
    have hExt (Y S : ℝ) : completionExt .interval F w Y S z =
        Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w Y S z := by
      by_cases hY : |Y| < w
      · have hYi := abs_lt.mp hY
        have hzi := abs_lt.mp hz
        simp [completionExt, Interior, hw, hYi.1, hYi.2, hzi.1, hzi.2,
          Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion, F, eventCompletionKernel, hY]
      · rw [Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion_exterior Q w Y S z (by tauto)]
        have hYi : ¬(-w < Y ∧ Y < w) := fun hh => hY (abs_lt.mpr hh)
        simp only [completionExt, Interior, hYi, false_and, and_false, if_false]
    have hDer : deriv (fun Y : ℝ =>
        Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w Y T z) y =
        FY (w,y,T,z) := by
      have hf : (fun Y : ℝ => Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w Y T z) =
          (fun Y : ℝ => eventCompletionKernel .interval Q (w,Y,T,z)) := by
        funext Y
        exact Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion_pos Q w Y T z hT
      rw [hf]
      exact (hKernel.2.2 w y T z hw hT hy hz).deriv
    have hRem (c : ℝ) : localRemainder .interval F FY w y T z c =
        Shao.C2.ActualIntervalProjection.sourceRemainder Q w y T z c := by
      unfold localRemainder Shao.C2.ActualIntervalProjection.sourceRemainder
      rw [hExt, hDer]
      simp only [Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion, if_pos hT,
        F, eventCompletionKernel, compensationCoefficient]
    have hRet : localRetainedRemainder .interval F FY w y T z b =
        Shao.C2.IntervalGaussianLocal.retainedRemainder Q w y T z b := by
      by_cases hs : b^2 ≤ T/2 <;> by_cases hu : w ≤ y+b <;> by_cases hl : y+b ≤ -w
      all_goals
        have hh : ¬ |y+b| < w ↔ w ≤ y+b ∨ y+b ≤ -w := by
          constructor
          · intro hh
            by_contra hc
            push_neg at hc
            exact hh (abs_lt.mpr ⟨by linarith only [hc.2], hc.1⟩)
          · rintro (hu | hl) hh
            · exact not_lt_of_ge hu (abs_lt.mp hh).2
            · exact not_lt_of_ge hl (abs_lt.mp hh).1
        simp only [localRetainedRemainder, projectionIncrement,
          Shao.C2.IntervalGaussianLocal.retainedRemainder, hT, hs, hu, hl, hh, hRem,
          true_and, and_true, and_false, false_and, true_or, or_true, false_or, or_false,
          if_true, if_false]
    have hNeg : max (-localSeparatedOvershoot .interval FY w y T z b) 0 =
        Shao.C2.IntervalGaussianLocal.negativeOvershoot Q w y T z b := by
      have huEq : -(b-(w-y))*(1-(b+(w-y))*(z-y)/T)*FY (w,y,T,z) =
          Shao.C2.ActualIntervalProjection.upperOvershoot Q w y T z b := by
        simp only [Shao.C2.ActualIntervalProjection.upperOvershoot,
          Shao.C2.ProjectionOvershoot.projectionOvershoot,
          Shao.C2.ProjectionOvershoot.projectionFactor, hDer]
      have hlEq : -(b-(-w-y))*(1-(b+(-w-y))*(z-y)/T)*FY (w,y,T,z) =
          Shao.C2.ActualIntervalProjection.lowerOvershoot Q w y T z b := by
        simp only [Shao.C2.ActualIntervalProjection.lowerOvershoot,
          Shao.C2.ProjectionOvershoot.projectionOvershoot,
          Shao.C2.ProjectionOvershoot.projectionFactor, hDer]
        ring
      by_cases hs : b^2 ≤ T/2 <;> by_cases hu : w ≤ y+b <;> by_cases hl : y+b ≤ -w
      all_goals
        have hh : ¬ |y+b| < w ↔ w ≤ y+b ∨ y+b ≤ -w := by
          constructor
          · intro hh
            by_contra hc
            push_neg at hc
            exact hh (abs_lt.mpr ⟨by linarith only [hc.2], hc.1⟩)
          · rintro (hu | hl) hh
            · exact not_lt_of_ge hu (abs_lt.mp hh).2
            · exact not_lt_of_ge hl (abs_lt.mp hh).1
        simp only [localSeparatedOvershoot, projectionIncrement,
          Shao.C2.IntervalGaussianLocal.negativeOvershoot, hT, hs, hu, hl, hh,
          true_and, and_true, and_false, false_and, true_or, or_true, false_or, or_false,
          if_true, if_false, huEq, hlEq, sub_self, neg_zero, zero_mul, max_self]
    have hbound := Shao.C2.BridgeIntervalImageResolved.actual_interval_retained_bound
      B PB hB w y T z b hw hy hz hT hb hzero
    have hqperm : Shao.energy (Spitzer.reorder a sigma) = Shao.energy a := by
      simpa only [Shao.energy, Spitzer.reorder] using Equiv.sum_comp sigma (fun i => (a i)^2)
    have hsperm : Shao.prefixSum (Spitzer.reorder a sigma) n = Shao.prefixSum a n := by
      simpa only [Shao.prefixSum_length, Spitzer.reorder] using Equiv.sum_comp sigma a
    have hA : ∀ s ∈ wallSigns .interval,
        Shao.maxWithZero (s • Spitzer.head (Spitzer.reorder a sigma) r.val r.is_lt.le) < w := by
      intro s hs
      have he : s = 1 ∨ s = -1 := by simpa [wallSigns] using hs
      rcases he with rfl | rfl
      all_goals
        unfold Shao.maxWithZero
        rw [Finset.sup'_lt_iff]
        intro k hk
        rw [Shao.prefixSum_smul, Spitzer.head_prefixSum _ _ _ k (Finset.mem_Icc.1 hk).2]
        have hkLive := hact.2.1.2.2 k (Finset.mem_Icc.1 hk).2
      · simpa only [one_mul] using hkLive.2
      · simp only [neg_one_mul]
        linarith only [hkLive.1]
    have hRank : SourceIIDGaussianProfileBudget.rankGaussianWeight h0 x
        (wallSigns .interval) false (Spitzer.reorder a sigma) r =
        (|b|/Real.sqrt T)^3 * (1+|z-y|/Real.sqrt T)^3 *
          Shao.C2.IntervalGaussianLargeStep.intervalEnvelope w y T z b := by
      have he := (SourceIIDGaussianProfileBudget.gaussian_weight_source_state
        (Spitzer.reorder a sigma) r h0 x (wallSigns .interval) false).2.2.2.2
      rw [hqperm, hsperm] at he
      have hsel : 0 < Shao.energy a - Shao.prefixSquares (Spitzer.reorder a sigma) r.val ∧
          h0 ≤ Shao.energy a - Shao.prefixSquares (Spitzer.reorder a sigma) r.val ∧
          (∀ s ∈ wallSigns .interval,
            if false = true then Shao.maxWithZero
              (s • Spitzer.head (Spitzer.reorder a sigma) r.val r.is_lt.le) ≤ x*Real.sqrt (Shao.energy a)
            else Shao.maxWithZero
              (s • Spitzer.head (Spitzer.reorder a sigma) r.val r.is_lt.le) < x*Real.sqrt (Shao.energy a)) :=
        ⟨hT,hcut,by simpa only [Bool.false_eq_true, ite_false, w, actualWall] using hA⟩
      rw [if_pos hsel, if_pos (show 0 < Shao.energy a -
        Shao.prefixSquares (Spitzer.reorder a sigma) r.val from hT)] at he
      convert he using 1
      simp only [wallSigns, Finset.sum_insert (by norm_num : (1:ℝ) ∉ ({-1}:Finset ℝ)),
        Finset.sum_singleton, one_mul, neg_one_mul, sub_neg_eq_add,
        Shao.C2.IntervalGaussianLargeStep.intervalEnvelope, Shao.C2.GaussianWallEnvelope.wallEnvelope]
      dsimp only [w, y, z, b, T, actualWall, remainingEnergy, Spitzer.reorder]
      congr 2 <;> ring
    simp only [sourceRetainedRemainder, sourceSeparatedOvershoot, dif_pos r.is_lt,
      if_pos (show r.val < nu sigma ∧ sourceAlive .interval a x r.val sigma ∧
        0 < remainingEnergy a r.val sigma from hact)]
    change |localRetainedRemainder .interval F FY w y T z b| +
      max (-localSeparatedOvershoot .interval FY w y T z b) 0 ≤ _
    rw [hRet, hNeg, hRank]
    simpa only [Q,mul_assoc] using hbound
  · have hi : ¬(r.val < nu sigma ∧ sourceAlive .interval a x r.val sigma ∧
        0 < remainingEnergy a r.val sigma) := hact
    simp only [sourceRetainedRemainder, sourceSeparatedOvershoot, dif_pos r.is_lt,
      if_neg hi, abs_zero, neg_zero, max_self, add_zero]
    exact mul_nonneg hCI hNN

/- Necessary private declaration 2.
No mask is discarded: the source terms keep nu and the same actual path.
The envelope enlarges the interval strict survival event to its two one-wall
strict survival events after the actual interval theorem is applied.
-/
private theorem alo_actual_three_domain_rank_domination
    {ΩB : Type*} [MeasurableSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → ℝ) (hB : IsBrownianReal B PB)
    {n : ℕ} (a : Shao.Path n) (h0 x : ℝ) (hh0 : 0 < h0) (hx : 0 < x)
    (nu : LabelPerm n → ℕ) (sigma : LabelPerm n)
    (hcap : nu sigma ≤ energyCutoff a h0 sigma) (r : Fin n) :
    let C0 : ℝ :=
      2 * (2 * Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant + 40) +
        2 * 8000100
    let Q : Measure BridgeNoise := bridgeLaw B PB
    let F : MonitoredDomain → BridgeKernel := fun J => eventCompletionKernel J Q
    let FY : MonitoredDomain → BridgeKernel := fun J =>
      match J with
      | .upper => halflineDerivative .upper
      | .lower => halflineDerivative .lower
      | .interval => intervalDerivative Q
    let L : MonitoredDomain → ℝ := fun J =>
      sourceRetainedRemainder J (F J) (FY J) a x nu r.val sigma
    |L .interval| + |L .upper| + |L .lower| +
        max (-sourceSeparatedOvershoot .interval (FY .interval)
          a x nu r.val sigma) 0 ≤
      C0 *
        (SourceIIDGaussianProfileBudget.rankGaussianWeight h0 x {1} false
            (Spitzer.reorder a sigma) r +
          SourceIIDGaussianProfileBudget.rankGaussianWeight h0 x {-1} false
            (Spitzer.reorder a sigma) r)
 := by
  classical
  intro C0 Q F FY L
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw B PB hB
  have hReflection : HalflineReflectionIdentities Q := by
    constructor
    · intro w y T z hw hT hy hz
      exact Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula B PB hB w y T z hT hy hz
    · intro w y T z hw hT hy hz
      exact Shao.C2.BridgeLowerIdentification.bridge_lower_formula B PB hB w y T z hT hy hz
  let CI : ℝ := 2 * Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant + 40
  let GU : ℝ := SourceIIDGaussianProfileBudget.rankGaussianWeight h0 x {1} false
    (Spitzer.reorder a sigma) r
  let GLo : ℝ := SourceIIDGaussianProfileBudget.rankGaussianWeight h0 x {-1} false
    (Spitzer.reorder a sigma) r
  let GI : ℝ := SourceIIDGaussianProfileBudget.rankGaussianWeight h0 x
    (wallSigns .interval) false (Spitzer.reorder a sigma) r
  have hCI : 0 ≤ CI := by
    dsimp [CI]
    linarith [Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant_nonneg]
  have hGUnn : 0 ≤ GU :=
    ((SourceIIDGaussianProfileBudget.fixed_gaussian_weight_measurable_bound
      r.val (n-r.val) h0 x {1} false).2.1 _ _).1
  have hGLnn : 0 ≤ GLo :=
    ((SourceIIDGaussianProfileBudget.fixed_gaussian_weight_measurable_bound
      r.val (n-r.val) h0 x {-1} false).2.1 _ _).1
  have hG : GI ≤ GU + GLo := by
    let v := Spitzer.head (Spitzer.reorder a sigma) r.val r.is_lt.le
    let u := Spitzer.tail (Spitzer.reorder a sigma) r.val r.is_lt.le
    change SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x (wallSigns .interval) false v u ≤
      SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {1} false v u +
        SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {-1} false v u
    by_cases hA : 0 < Shao.energy u ∧ h0 ≤ Shao.energy u ∧
        SourceIIDGaussianProfileBudget.prefixSurvival x (wallSigns .interval) false v u
    · have hAU : SourceIIDGaussianProfileBudget.prefixSurvival x {1} false v u := by
        intro s hs
        have hmem : s ∈ wallSigns .interval := by
          simpa [wallSigns] using (Or.inl (Finset.mem_singleton.mp hs) : s=1 ∨ s=-1)
        exact hA.2.2 s hmem
      have hAL : SourceIIDGaussianProfileBudget.prefixSurvival x {-1} false v u := by
        intro s hs
        have hmem : s ∈ wallSigns .interval := by
          simpa [wallSigns] using (Or.inr (Finset.mem_singleton.mp hs) : s=1 ∨ s=-1)
        exact hA.2.2 s hmem
      have hAUact : 0<Shao.energy u ∧ h0≤Shao.energy u ∧
          SourceIIDGaussianProfileBudget.prefixSurvival x {1} false v u := ⟨hA.1,hA.2.1,hAU⟩
      have hALact : 0<Shao.energy u ∧ h0≤Shao.energy u ∧
          SourceIIDGaussianProfileBudget.prefixSurvival x {-1} false v u := ⟨hA.1,hA.2.1,hAL⟩
      simp only [SourceIIDGaussianProfileBudget.fixedGaussianWeight, if_pos hA,
        if_pos hAUact, if_pos hALact,
        SourceIIDGaussianProfileBudget.gaussianProfiles, if_pos hA.1, wallSigns,
        Finset.sum_insert (by norm_num : (1:ℝ) ∉ ({-1}:Finset ℝ)), Finset.sum_singleton]
      simp only [if_pos (show 0<Shao.energy u ∧ h0≤Shao.energy u ∧
        SourceIIDGaussianProfileBudget.prefixSurvival x {1,-1} false v u from hA)]
      ring_nf
      exact le_rfl
    · rw [SourceIIDGaussianProfileBudget.fixedGaussianWeight, if_neg hA]
      exact add_nonneg hGUnn hGLnn
  have hI := alo_actual_interval_rank_domination PB B hB a h0 x hh0 hx nu sigma hcap r
  change |L .interval| + max (-sourceSeparatedOvershoot .interval (FY .interval)
    a x nu r.val sigma) 0 ≤ CI * GI at hI
  have hU := actual_halfline_retained_rank_domination Q hReflection .upper (Or.inl rfl)
    a h0 x hh0 hx nu sigma hcap r
  have hD := actual_halfline_retained_rank_domination Q hReflection .lower (Or.inr rfl)
    a h0 x hh0 hx nu sigma hcap r
  change |L .upper| ≤ 8000100 * GU at hU
  change |L .lower| ≤ 8000100 * GLo at hD
  have hI' := hI.trans (mul_le_mul_of_nonneg_left hG hCI)
  change _ ≤ C0 * (GU + GLo)
  have hC : CI + 8000100 ≤ C0 := by dsimp [C0, CI]; linarith
  have hfin := mul_le_mul_of_nonneg_right hC (add_nonneg hGUnn hGLnn)
  nlinarith only [hI', hU, hD, hfin]

/- Necessary private declaration 3.
Actual full-prefix profile, one actual sign, fixed arbitrary complete-suffix
state T,d,b. Both 0<w and the closed CDF upper endpoint are retained by the
proof. The public B CDF is used with theta=0 on G; Gc is paid rather than
dropped. Constant precedes all law/data/sign/suffix parameters.
-/
private theorem alo_iid_fixed_state_wall_profile :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (Bcap : ℝ), 0 < Bcap → (∀ᵐ z : ℝ ∂rho, |z| ≤ Bcap) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), 1 ≤ x →
          Bcap ≤ Real.sqrt (n : ℝ) / (200 * x) →
          ∀ (r : ℕ), r ≤ n → (n : ℝ) / 2 ≤ (r : ℝ) →
            ∀ (T d b eta : ℝ), 0 < T → 4 * beta ^ 2 ≤ T → b ^ 2 ≤ T →
              (eta = 1 ∨ eta = -1) →
              let P : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => rho)
              let D : ℝ := 1 + |d| / Real.sqrt T
              let M : ℝ := |b| + max (eta * d) 0
              let wall : Shao.Path r → ℝ := fun v =>
                x * Real.sqrt (Shao.energy v + T)
              let A : Set (Shao.Path r) := {v | ∀ k : Fin (r + 1),
                0 < k.val → eta * Shao.prefixSum v k.val < wall v}
              let profile : Shao.Path r → ℝ := fun v =>
                Real.exp (-((max (wall v - eta * Shao.prefixSum v r - M) 0) ^ 2) / T)
              Measurable (A.indicator profile) ∧ Integrable (A.indicator profile) P ∧
                (∫ v, A.indicator profile v ∂P) ≤ C * T * D ^ 2 / (r : ℝ)
 := by
  classical
  obtain ⟨CW, hCW, hWall⟩ :=
    SourceWeightedPrefixWall.actual_circular_weighted_true_wall_closed_cdf
  refine ⟨9 * CW + 16, by linarith, ?_⟩
  intro rho hRho Bcap hBcap hBound hmean hsecond beta n hn x hx hsmall
    r hrn hhalf T d b eta hT hh0 hb heta P D M wall A profile
  letI : IsProbabilityMeasure rho := hRho
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hCW0 : 0 < CW := by linarith
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.2 hn
  have hrR : 0 < (r : ℝ) := by linarith only [hnR, hhalf]
  have hr : 0 < r := Nat.cast_pos.1 hrR
  have hrS : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 hrR
  have h2 : Integrable (fun z : ℝ => z ^ 2) rho := by
    refine (integrable_const (Bcap^2)).mono' (by fun_prop) ?_
    filter_upwards [hBound] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z) hz 2
  have h3 : Integrable (fun z : ℝ => |z| ^ 3) rho := by
    refine (integrable_const (Bcap^3)).mono' (by fun_prop) ?_
    filter_upwards [hBound] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ |z|^3)]
    exact pow_le_pow_left₀ (abs_nonneg z) hz 3
  have hBeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one rho h2 h3 hsecond
  have hBeta0 : 0 < beta := by linarith
  let gap : ℝ → Shao.Path r → ℝ := fun eta v => wall v - eta * Shao.prefixSum v r
  let AA : ℝ → Set (Shao.Path r) := fun eta => {v | ∀ k : Fin (r+1),
    0 < k.val → eta * Shao.prefixSum v k.val < wall v}
  let G : Set (Shao.Path r) := {v | (r : ℝ)/2 ≤ Shao.energy v}
  have hwallM : Measurable wall :=
    measurable_const.mul ((Shao.measurable_energy.add_const T).sqrt)
  have hgapM (eta : ℝ) : Measurable (gap eta) :=
    hwallM.sub (measurable_const.mul (Shao.measurable_prefixSum r))
  have hAM (eta : ℝ) : MeasurableSet (AA eta) := by
    change MeasurableSet {v : Shao.Path r | ∀ k : Fin (r+1),
      0 < k.val → eta * Shao.prefixSum v k.val < wall v}
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro k
    by_cases hk : 0 < k.val
    · simpa only [hk, true_implies, Pi.mul_apply] using
        measurableSet_lt (measurable_const.mul (Shao.measurable_prefixSum k.val)) hwallM
    · simp only [hk, false_implies, Set.setOf_true, MeasurableSet.univ]
  have hGM : MeasurableSet G := measurableSet_le measurable_const Shao.measurable_energy
  have hgapPos (eta : ℝ) (v : Shao.Path r) (hv : v ∈ AA eta) : 0 < gap eta v := by
    have hh := hv ⟨r, by omega⟩ hr
    dsimp [gap]
    linarith
  have hCDF (eta : ℝ) (heta : eta = 1 ∨ eta = -1) (s : ℝ) (hs : 0 ≤ s) :
      P.real {v | v ∈ AA eta ∩ G ∧ gap eta v ≤ s} ≤
        CW * (s + beta)^2 / (r : ℝ) := by
    let rhoS : Measure ℝ := Measure.map (fun z : ℝ => eta * z) rho
    let PS : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => rhoS)
    let S : Shao.Path r → Shao.Path r := fun v => eta • v
    have hm : Measurable (fun z : ℝ => eta*z) := measurable_const.mul measurable_id
    letI : IsProbabilityMeasure rhoS := by dsimp [rhoS]; infer_instance
    have habs (z : ℝ) : |eta*z|=|z| := by
      rcases heta with rfl | rfl <;> simp
    have hsq (z : ℝ) : (eta*z)^2=z^2 := by
      rcases heta with rfl | rfl <;> ring
    have hcaps : ∀ᵐ z : ℝ ∂rhoS, |z| ≤ Bcap := by
      apply (ae_map_iff hm.aemeasurable
        (measurableSet_le continuous_abs.measurable measurable_const)).2
      simpa only [habs] using hBound
    have hmeans : (∫ z : ℝ, z ∂rhoS)=0 := by
      rw [show rhoS=Measure.map (fun z : ℝ => eta*z) rho from rfl,
        integral_map hm.aemeasurable (f := fun z : ℝ => z) (by fun_prop),
        integral_const_mul, hmean, mul_zero]
    have hseconds : (∫ z : ℝ, z^2 ∂rhoS)=1 := by
      rw [show rhoS=Measure.map (fun z : ℝ => eta*z) rho from rfl,
        integral_map hm.aemeasurable (f := fun z : ℝ => z^2) (by fun_prop)]
      simpa only [hsq] using hsecond
    have hbetas : (∫ z : ℝ, |z|^3 ∂rhoS)=beta := by
      rw [show rhoS=Measure.map (fun z : ℝ => eta*z) rho from rfl,
        integral_map hm.aemeasurable (f := fun z : ℝ => |z|^3) (by fun_prop)]
      simp only [habs]
      rfl
    let wallS : Shao.Path r → ℝ := fun v => x*Real.sqrt (Shao.energy v+T)
    let gapS : Shao.Path r → ℝ := fun v => wallS v-Shao.prefixSum v r
    let AS : Set (Shao.Path r) := {v | ∀ k : Fin (r+1),
      0 < k.val → Shao.prefixSum v k.val < wallS v}
    let ES : Set (Shao.Path r) := AS ∩ G ∩ {v | 0<gapS v ∧ gapS v≤s}
    have hASM : MeasurableSet AS := by simpa only [AA, one_mul] using hAM 1
    have hgapSM : Measurable gapS := hwallM.sub (Shao.measurable_prefixSum r)
    have hESM : MeasurableSet ES :=
      (hASM.inter hGM).inter
        ((measurableSet_lt measurable_const hgapSM).inter
          (measurableSet_le hgapSM measurable_const))
    have hb := hWall rhoS Bcap hBcap hcaps hmeans hseconds n hn x hx hsmall
      r hrn hhalf T hT.le 0 s (by norm_num) (by positivity) hs
    have hprob : PS.real ES ≤ CW*(s+beta)^2/(r : ℝ) := by
      have hb0 : (∫ v,ES.indicator (fun _ => (1:ℝ)) v ∂PS)≤CW*(s+beta)^2/(r : ℝ) := by
        simpa only [hbetas,zero_pow (by decide : (2:ℕ)≠0),
          zero_pow (by decide : (3:ℕ)≠0),zero_mul,mul_zero,zero_add,add_zero,
          one_pow,Real.exp_zero,mul_one,ES,AS,gapS,wallS,G] using hb.2
      have hone : (∫ v,ES.indicator (fun _ => (1:ℝ)) v ∂PS)=PS.real ES := by
        change (∫ v,ES.indicator 1 v ∂PS)=PS.real ES
        exact integral_indicator_one hESM
      rwa [hone] at hb0
    have hSM : Measurable S :=
      Measurable.of_eval fun i => measurable_const.mul (measurable_pi_apply i)
    have hmap : Measure.map S P=PS :=
      Measure.pi_map_pi (fun _ : Fin r => hm.aemeasurable)
    have henergyS (v : Shao.Path r) : Shao.energy (S v)=Shao.energy v := by
      rw [Shao.energy_smul]
      rcases heta with rfl | rfl <;> norm_num
    have hevent : S ⁻¹' ES={v | v∈AA eta∩G ∧ gap eta v≤s} := by
      ext v
      simp only [Set.mem_preimage, ES, Set.mem_inter_iff, Set.mem_setOf_eq,
        AS, wallS, gapS, henergyS, S, Shao.prefixSum_smul, AA, G, wall, gap]
      constructor
      · rintro ⟨⟨ha,hg⟩,hw⟩
        exact ⟨⟨ha,hg⟩,hw.2⟩
      · rintro ⟨⟨ha,hg⟩,hw⟩
        exact ⟨⟨ha,hg⟩,hgapPos eta v ha,hw⟩
    rw [←hmap, Measure.real_def, Measure.map_apply hSM hESM, hevent] at hprob
    exact hprob
  have hLow : P.real Gᶜ ≤ 64*beta^2/(r : ℝ) := by
    let scale : ℝ := Real.sqrt (r : ℝ)
    let rhoR : Measure ℝ := Measure.map (fun z : ℝ => z/scale) rho
    let PR : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => rhoR)
    let S : Shao.Path r → Shao.Path r := fun v i => v i/scale
    have hs : 0<scale := hrS
    have hs2 : scale^2=(r : ℝ) := Real.sq_sqrt hrR.le
    have hm : Measurable (fun z : ℝ => z/scale) := measurable_id.div_const _
    letI : IsProbabilityMeasure rhoR := by dsimp [rhoR]; infer_instance
    have h2R : Integrable (fun z : ℝ => z^2) rhoR := by
      apply (integrable_map_measure (by fun_prop) hm.aemeasurable).2
      simpa only [Function.comp_def,div_pow] using h2.div_const (scale^2)
    have h3R : Integrable (fun z : ℝ => |z|^3) rhoR := by
      apply (integrable_map_measure (by fun_prop) hm.aemeasurable).2
      simpa only [Function.comp_def,abs_div,abs_of_pos hs,div_pow] using
        h3.div_const (scale^3)
    have hNorm : (r : ℝ)*(∫ z : ℝ,z^2 ∂rhoR)=1 := by
      rw [show rhoR=Measure.map (fun z : ℝ => z/scale) rho from rfl,
        integral_map hm.aemeasurable (f := fun z : ℝ => z^2) (by fun_prop)]
      simp_rw [div_pow]
      rw [integral_div,hsecond,hs2]
      exact mul_one_div_cancel hrR.ne'
    have hBetaR : (r : ℝ)*(∫ z : ℝ,|z|^3 ∂rhoR)=beta/scale := by
      rw [show rhoR=Measure.map (fun z : ℝ => z/scale) rho from rfl,
        integral_map hm.aemeasurable (f := fun z : ℝ => |z|^3) (by fun_prop)]
      simp only [abs_div,abs_of_pos hs,div_pow]
      rw [integral_div]
      change (r : ℝ)*(beta/scale^3)=beta/scale
      field_simp
      nlinarith [hs2]
    have hTail := (finite_iid_energy_lower_tail rhoR r hr h2R h3R hNorm
      (1/2) (by norm_num) (by norm_num)).2
    rw [hBetaR] at hTail
    have hSM : Measurable S :=
      Measurable.of_eval fun i => by
        simpa only [S] using (measurable_pi_apply i : Measurable (fun v : Shao.Path r => v i)).div_const scale
    have hmap : Measure.map S P=PR :=
      Measure.pi_map_pi (fun _ : Fin r => hm.aemeasurable)
    have hES : MeasurableSet {v : Shao.Path r | Shao.energy v≤1-(1/2 : ℝ)} :=
      measurableSet_le Shao.measurable_energy measurable_const
    have he (v : Shao.Path r) : Shao.energy (S v)=Shao.energy v/(r : ℝ) := by
      simp only [S,Shao.energy,div_pow,hs2,Finset.sum_div]
    have hSet : S ⁻¹' {v : Shao.Path r | Shao.energy v≤1-(1/2 : ℝ)}=
        {v : Shao.Path r | Shao.energy v≤(r : ℝ)/2} := by
      ext v
      simp only [Set.mem_preimage,Set.mem_setOf_eq,he,div_le_iff₀ hrR]
      constructor <;> intro hh <;> linarith
    change PR.real {v : Shao.Path r | Shao.energy v≤1-(1/2 : ℝ)}≤_ at hTail
    rw [←hmap,Measure.real_def,Measure.map_apply hSM hES,hSet] at hTail
    have hexp : -((1/2 : ℝ)^3/(8*(beta/scale)^2))=-(r : ℝ)/(64*beta^2) := by
      simp only [div_pow]
      rw [hs2]
      field_simp [hrR.ne',hBeta0.ne']
      <;> ring
    rw [hexp] at hTail
    have hsub : Gᶜ ⊆ {v : Shao.Path r | Shao.energy v≤(r : ℝ)/2} := by
      intro v hv
      change ¬(r : ℝ)/2≤Shao.energy v at hv
      exact (lt_of_not_ge hv).le
    have hle : P.real Gᶜ≤Real.exp (-(r : ℝ)/(64*beta^2)) :=
      (measureReal_mono hsub).trans hTail
    have ha : 0<(r : ℝ)/(64*beta^2) := by positivity
    have heq : Real.exp (-(r : ℝ)/(64*beta^2))≤64*beta^2/(r : ℝ) := by
      have he : (r : ℝ)/(64*beta^2)≤Real.exp ((r : ℝ)/(64*beta^2)) :=
        (le_add_of_nonneg_right (by norm_num : (0:ℝ)≤1)).trans
          (Real.add_one_le_exp _)
      rw [show -(r : ℝ)/(64*beta^2)=-((r : ℝ)/(64*beta^2)) by ring,
        Real.exp_neg,←one_div]
      calc
        1/Real.exp ((r : ℝ)/(64*beta^2))≤1/((r : ℝ)/(64*beta^2)) :=
          one_div_le_one_div_of_le ha he
        _ = _ := by field_simp
    exact hle.trans heq
  have hTs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hTs2 : (Real.sqrt T)^2 = T := Real.sq_sqrt hT.le
  have hD : 1 ≤ D := by
    have hh : 0 ≤ |d|/Real.sqrt T := div_nonneg (abs_nonneg d) hTs.le
    dsimp [D]
    linarith
  have hD0 : 0 ≤ D := by linarith
  have hM0 : 0 ≤ M := add_nonneg (abs_nonneg b) (le_max_right _ _)
  have hab : |b| ≤ Real.sqrt T := by nlinarith only [hb, sq_abs b, hTs2, abs_nonneg b, hTs.le]
  have hds : |eta*d|=|d| := by rcases heta with rfl | rfl <;> simp
  have hmax : max (eta*d) 0 ≤ |d| :=
    max_le ((le_abs_self _).trans_eq hds) (abs_nonneg d)
  have hMD : M ≤ Real.sqrt T * D := by
    have he : Real.sqrt T * D = Real.sqrt T + |d| := by dsimp [D]; field_simp <;> ring
    rw [he]
    exact add_le_add hab hmax
  have hM2 : M^2 ≤ T*D^2 := by
    have hh := pow_le_pow_left₀ hM0 hMD 2
    nlinarith only [hh, hTs2]
  have hTD : T ≤ T*D^2 := le_mul_of_one_le_right hT.le (one_le_pow₀ hD)
  have hPM : Measurable profile :=
    (((((hgapM eta).sub_const M).max measurable_const).pow_const 2).neg.div_const T).exp
  have hP0 (v : Shao.Path r) : 0 ≤ profile v := (Real.exp_pos _).le
  have hP1 (v : Shao.Path r) : profile v ≤ 1 :=
    Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.2 (sq_nonneg _)) hT.le)
  have hPi : Integrable profile P := by
    refine (integrable_const (1:ℝ)).mono' hPM.aestronglyMeasurable ?_
    exact ae_of_all _ fun v => by rw [Real.norm_eq_abs,abs_of_nonneg (hP0 v)]; exact hP1 v
  have hAeq : AA eta = A := rfl
  have hAi : Integrable (A.indicator profile) P := hPi.indicator (hAeq ▸ hAM eta)
  have hQuad (v : ℝ) (hv : 0 ≤ v) :
      P.real {a | a ∈ AA eta ∩ G ∧ gap eta a ≤ v} ≤
        (2*CW)*(v^2/(r : ℝ)+(beta/Real.sqrt (r : ℝ))^2) := by
    have hh := hCDF eta heta v hv
    have hrat : (v+beta)^2/(r : ℝ) ≤
        2*(v^2/(r : ℝ)+(beta/Real.sqrt (r : ℝ))^2) := by
      rw [div_pow, Real.sq_sqrt hrR.le]
      have hnum : (v+beta)^2≤2*(v^2+beta^2) := by nlinarith [sq_nonneg (v-beta)]
      have hz := div_le_div_of_nonneg_right hnum hrR.le
      convert hz using 1 <;> ring
    calc
      _ ≤ CW*((v+beta)^2/(r : ℝ)) := by convert hh using 1 <;> ring
      _ ≤ CW*(2*(v^2/(r : ℝ)+(beta/Real.sqrt (r : ℝ))^2)) :=
        mul_le_mul_of_nonneg_left hrat hCW0.le
      _ = _ := by ring
  have hHigh := gaussian_wall_profile_of_quadratic_closed_cdf
    P (AA eta ∩ G) ((hAM eta).inter hGM) (gap eta) (hgapM eta)
    (2*CW) (beta/Real.sqrt (r : ℝ)) (r : ℝ) T M
    (by positivity) hrR hT hM0 hQuad
  change (∫ v,(AA eta ∩ G).indicator profile v ∂P) ≤ _ at hHigh
  have hHigh' : (∫ v,(AA eta ∩ G).indicator profile v ∂P) ≤
      9*CW*T*D^2/(r : ℝ) := by
    apply hHigh.trans
    rw [div_pow, Real.sq_sqrt hrR.le]
    have hnum : 2*CW*(2*(M^2+T)+beta^2) ≤ 9*CW*T*D^2 := by
      nlinarith [mul_nonneg hCW0.le (sub_nonneg.2 hM2),
        mul_nonneg hCW0.le (sub_nonneg.2 hTD),
        mul_nonneg hCW0.le (sub_nonneg.2 hh0)]
    have hz := div_le_div_of_nonneg_right hnum hrR.le
    convert hz using 1 <;> ring
  have hHighI : Integrable ((AA eta ∩ G).indicator profile) P :=
    hPi.indicator ((hAM eta).inter hGM)
  have hLowI : Integrable (Gᶜ.indicator (fun _ : Shao.Path r => (1:ℝ))) P :=
    (integrable_const _).indicator hGM.compl
  have hLowEq : (∫ v,Gᶜ.indicator (fun _ : Shao.Path r => (1:ℝ)) v ∂P)=P.real Gᶜ :=
    integral_indicator_one hGM.compl
  have hdom (v : Shao.Path r) : A.indicator profile v ≤
      (AA eta ∩ G).indicator profile v + Gᶜ.indicator (fun _ => (1:ℝ)) v := by
    by_cases hA : v∈A <;> by_cases hG : v∈G
    · have hAG : v∈AA eta ∩ G := ⟨hA,hG⟩
      simp [Set.indicator_of_mem,Set.indicator_of_notMem,hA,hG,hAG]
    · have hAG : v∉AA eta ∩ G := fun hh => hG hh.2
      have hc : v∈Gᶜ := hG
      simp only [Set.indicator_of_mem hA,Set.indicator_of_notMem hAG,
        Set.indicator_of_mem hc,zero_add]
      exact hP1 v
    · have hAG : v∉AA eta ∩ G := fun hh => hA hh.1
      simp [Set.indicator_of_mem,Set.indicator_of_notMem,hA,hG,hAG]
    · have hAG : v∉AA eta ∩ G := fun hh => hA hh.1
      simp [Set.indicator_of_mem,Set.indicator_of_notMem,hA,hG,hAG]
  refine ⟨hPM.indicator (hAeq ▸ hAM eta),hAi,?_⟩
  have hInt := integral_mono hAi (hHighI.add hLowI) hdom
  simp only [Pi.add_apply] at hInt
  rw [integral_add hHighI hLowI,hLowEq] at hInt
  have hLow' : P.real Gᶜ ≤ 16*T*D^2/(r : ℝ) := by
    apply hLow.trans
    apply div_le_div_of_nonneg_right _ hrR.le
    nlinarith only [hh0, hTD]
  have hz := hInt.trans (add_le_add hHigh' hLow')
  convert hz using 1 <;> ring

/- Necessary private declaration 4.
This is the exact analytic payment for a fixed complete iid suffix. No
conditioning on a dprime-dependent event and no redraw of the marked first
suffix increment occurs. Empty/zero-energy suffixes are explicitly totalized.
-/
private theorem alo_iid_fixed_suffix_weighted_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (Bcap : ℝ), 0 < Bcap → (∀ᵐ z : ℝ ∂rho, |z| ≤ Bcap) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), 1 ≤ x →
          Bcap ≤ Real.sqrt (n : ℝ) / (200 * x) →
          ∀ (r : ℕ), r ≤ n → (n : ℝ) / 2 ≤ (r : ℝ) →
            ∀ (t : ℕ) (u : Shao.Path t),
              let h0 : ℝ := 4 * beta ^ 2
              let Pprefix : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => rho)
              let T : ℝ := Shao.energy u
              let d : ℝ := Shao.prefixSum u t
              let b : ℝ := SourceIIDGaussianProfileBudget.firstValue u
              let D : ℝ := 1 + |d| / Real.sqrt T
              let G : Shao.Path r → ℝ := fun v =>
                SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {1} false v u +
                  SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {-1} false v u
              let W : ℝ := if 0 < T ∧ h0 ≤ T then |b| ^ 3 / Real.sqrt T * D ^ 5 else 0
              Measurable G ∧ Integrable G Pprefix ∧
                (∫ v, G v ∂Pprefix) ≤ C * W / (r : ℝ)
 := by
  classical
  obtain ⟨CP, hCP, hProfile⟩ := alo_iid_fixed_state_wall_profile
  refine ⟨2*CP, by positivity, ?_⟩
  intro rho hRho Bcap hBcap hBound hmean hsecond beta n hn x hx hsmall
    r hrn hhalf t u h0 Pprefix T d b D G W
  letI : IsProbabilityMeasure rho := hRho
  letI : IsProbabilityMeasure Pprefix := by dsimp [Pprefix]; infer_instance
  have hData (eta : ℝ) := SourceIIDGaussianProfileBudget.fixed_gaussian_weight_measurable_bound
    r t h0 x {eta} false
  have hMeas (eta : ℝ) : Measurable (fun v : Shao.Path r =>
      SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {eta} false v u) :=
    (hData eta).1.comp (measurable_id.prodMk measurable_const)
  have hInt (eta : ℝ) : Integrable (fun v : Shao.Path r =>
      SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {eta} false v u) Pprefix := by
    refine (integrable_const ((1+Real.sqrt (t : ℝ))^3)).mono'
      (hMeas eta).aestronglyMeasurable ?_
    exact ae_of_all _ fun v => by
      simpa only [Finset.card_singleton, Nat.cast_one, one_mul, Real.norm_eq_abs]
        using ((hData eta).2.1 v u).2
  have hGM : Measurable G := (hMeas 1).add (hMeas (-1))
  have hGI : Integrable G Pprefix := (hInt 1).add (hInt (-1))
  refine ⟨hGM,hGI,?_⟩
  by_cases hsel : 0 < T ∧ h0 ≤ T
  · have ht : 0 < t := by
      by_contra hh
      have ht0 : t=0 := Nat.eq_zero_of_not_pos hh
      subst t
      simpa [T,Shao.energy] using hsel.1
    have hb : b^2 ≤ T := by
      change (SourceIIDGaussianProfileBudget.firstValue u)^2 ≤ Shao.energy u
      rw [SourceIIDGaussianProfileBudget.firstValue,dif_pos ht]
      exact Finset.single_le_sum (fun i _ => sq_nonneg (u i))
        (Finset.mem_univ (⟨0,ht⟩ : Fin t))
    have hD : SourceMarkedSuffixAveraging.suffixD u=D := by
      simp only [SourceMarkedSuffixAveraging.suffixD, if_pos hsel.1, D, T, d]
    let c : ℝ := |b|^3/(T*Real.sqrt T)*D^3
    have hc : 0 ≤ c := by
      have hD0 : 0≤D := add_nonneg zero_le_one
        (div_nonneg (abs_nonneg d) (Real.sqrt_nonneg T))
      exact mul_nonneg (div_nonneg (pow_nonneg (abs_nonneg b) 3)
        (mul_nonneg hsel.1.le (Real.sqrt_nonneg T))) (pow_nonneg hD0 3)
    have hOne (eta : ℝ) (heta : eta=1 ∨ eta= -1) :
        (∫ v, SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {eta} false v u
          ∂Pprefix) ≤ c*(CP*T*D^2/(r : ℝ)) := by
      let wall : Shao.Path r → ℝ := fun v => x*Real.sqrt (Shao.energy v+T)
      let A : Set (Shao.Path r) := {v | ∀ k : Fin (r+1),
        0<k.val → eta*Shao.prefixSum v k.val<wall v}
      let profile : Shao.Path r → ℝ := fun v => Real.exp
        (-((max (wall v-eta*Shao.prefixSum v r-(|b|+max (eta*d) 0)) 0)^2)/T)
      have hP := hProfile rho Bcap hBcap hBound hmean hsecond n hn x hx hsmall r hrn hhalf
        T d b eta hsel.1 hsel.2 hb heta
      change Measurable (A.indicator profile) ∧ Integrable (A.indicator profile) Pprefix ∧
        (∫ v,A.indicator profile v ∂Pprefix) ≤ CP*T*D^2/(r : ℝ) at hP
      have hAlive (v : Shao.Path r) :
          SourceIIDGaussianProfileBudget.prefixSurvival x {eta} false v u ↔ v∈A := by
        simp only [SourceIIDGaussianProfileBudget.prefixSurvival, Finset.mem_singleton,
          forall_eq, Bool.false_eq_true, ite_false]
        unfold Shao.maxWithZero
        rw [Finset.sup'_lt_iff]
        constructor
        · intro h k hk
          have hh := h k.val (Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩)
          simpa only [Shao.prefixSum_smul,wall,T,add_comm] using hh
        · intro h k hk
          rw [Shao.prefixSum_smul]
          by_cases hk0 : 0<k
          · have hkr : k≤r := (Finset.mem_Icc.1 hk).2
            simpa only [wall,T,add_comm] using h ⟨k,Nat.lt_succ_of_le hkr⟩ hk0
          · have hkz : k=0 := Nat.eq_zero_of_not_pos hk0
            subst k
            simp only [Shao.prefixSum_zero,mul_zero]
            exact mul_pos (by linarith only [hx])
              (Real.sqrt_pos.2 (by linarith [Shao.energy_nonneg v]))
      have hEq : (fun v : Shao.Path r =>
          SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {eta} false v u) =
          fun v => c*(A.indicator profile v) := by
        funext v
        by_cases hv : v∈A
        · have ha := (hAlive v).2 hv
          have hTU : 0<Shao.energy u := hsel.1
          have hAct : 0<Shao.energy u ∧ h0≤Shao.energy u ∧
              SourceIIDGaussianProfileBudget.prefixSurvival x {eta} false v u :=
            ⟨hTU,hsel.2,ha⟩
          simp only [SourceIIDGaussianProfileBudget.fixedGaussianWeight,
            if_pos hAct,SourceIIDGaussianProfileBudget.gaussianProfiles,
            if_pos hTU,Finset.sum_singleton,hD,Set.indicator_of_mem hv]
          dsimp only [c,profile,wall,T,d,b]
          congr 1 <;> congr 2 <;> ring
        · have ha := (not_congr (hAlive v)).mpr hv
          have hs : ¬(0<Shao.energy u ∧ h0≤Shao.energy u ∧
              SourceIIDGaussianProfileBudget.prefixSurvival x {eta} false v u) := fun hh => ha hh.2.2
          simp only [SourceIIDGaussianProfileBudget.fixedGaussianWeight,if_neg hs,
            Set.indicator_of_notMem hv,mul_zero]
      rw [hEq,integral_const_mul]
      exact mul_le_mul_of_nonneg_left hP.2.2 hc
    have hp := hOne 1 (Or.inl rfl)
    have hm := hOne (-1) (Or.inr rfl)
    change (∫ v, (SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {1} false v u +
      SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {-1} false v u) ∂Pprefix) ≤ _
    rw [integral_add (hInt 1) (hInt (-1))]
    have hz := add_le_add hp hm
    have he : c*(CP*T*D^2/(r : ℝ))+c*(CP*T*D^2/(r : ℝ)) = 2*CP*W/(r : ℝ) := by
      dsimp only [W]
      rw [if_pos hsel]
      dsimp [c]
      field_simp [ne_of_gt hsel.1,ne_of_gt (Real.sqrt_pos.2 hsel.1)]
      <;> ring
    exact hz.trans_eq he
  · have hz (v : Shao.Path r) : G v=0 := by
      have hs (eta : ℝ) : ¬(0<Shao.energy u ∧ h0≤Shao.energy u ∧
          SourceIIDGaussianProfileBudget.prefixSurvival x {eta} false v u) :=
        fun hh => hsel ⟨hh.1,hh.2.1⟩
      simp only [G,SourceIIDGaussianProfileBudget.fixedGaussianWeight,
        if_neg (hs 1),if_neg (hs (-1)),zero_add]
    have hGzero : G=fun _ => (0:ℝ) := funext hz
    rw [hGzero,integral_zero]
    simp only [W,if_neg hsel,mul_zero,zero_div,le_rfl]

/- Necessary private declaration 5.
Exact fixed split/Fubini statement including the omitted mask. It is specific
to the existing actual Gaussian envelopes; no arbitrary B/E/telescope slots.
Its two sides use the same actual head, full suffix, first mark and energy wall.
-/
private theorem alo_iid_masked_rank_fubini
    {n : ℕ} (rho : Measure ℝ) [IsProbabilityMeasure rho] (r : Fin n)
    (h0 H x : ℝ) (hh0 : 0 < h0) (hH : 0 < H) (m : ℕ) :
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
    let Pprefix : Measure (Shao.Path r.val) := Measure.pi (fun _ : Fin r.val => rho)
    let Psuffix : Measure (Shao.Path (n - r.val)) :=
      Measure.pi (fun _ : Fin (n - r.val) => rho)
    let nu : Shao.Path n → LabelPerm n → ℕ :=
      fun a sigma => energyCutoff a h0 sigma
    let tau : Shao.Path n → LabelPerm n → ℕ := fun a sigma =>
      min (energyCutoff a H sigma) (n - m)
    let g : Shao.Path n → ℝ := fun a =>
      if tau a (Equiv.refl (Fin n)) ≤ r.val ∧ r.val < nu a (Equiv.refl (Fin n)) then
        SourceIIDGaussianProfileBudget.rankGaussianWeight h0 x {1} false a r +
          SourceIIDGaussianProfileBudget.rankGaussianWeight h0 x {-1} false a r
      else 0
    let f : Shao.Path r.val × Shao.Path (n - r.val) → ℝ := fun p =>
      if h0 ≤ Shao.energy p.2 ∧ (Shao.energy p.2 < H ∨ n - r.val ≤ m) then
        SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {1} false p.1 p.2 +
          SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {-1} false p.1 p.2
      else 0
    Measurable g ∧ Integrable g P ∧ Measurable f ∧ Integrable f (Pprefix.prod Psuffix) ∧
      Integrable (fun u => ∫ v, f (v, u) ∂Pprefix) Psuffix ∧
      (∫ a, g a ∂P) = ∫ u, (∫ v, f (v, u) ∂Pprefix) ∂Psuffix
 := by
  classical
  intro P Pprefix Psuffix nu tau g f
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  letI : IsProbabilityMeasure Pprefix := by dsimp [Pprefix]; infer_instance
  letI : IsProbabilityMeasure Psuffix := by dsimp [Psuffix]; infer_instance
  let split : Shao.Path n → Shao.Path r.val × Shao.Path (n-r.val) := fun a =>
    (Spitzer.head a r.val r.is_lt.le,Spitzer.tail a r.val r.is_lt.le)
  have hSplit : MeasurePreserving split P (Pprefix.prod Psuffix) := by
    let e : Fin r.val ⊕ Fin (n-r.val) ≃ Fin n :=
      finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le r.is_lt.le))
    have h1 := (measurePreserving_piCongrLeft (fun _ : Fin n => rho) e).symm
    have h2 := measurePreserving_sumPiEquivProdPi (fun _ : Fin r.val ⊕ Fin (n-r.val) => rho)
    convert h2.comp h1 using 1
    ext a i <;> change a _ = a _ <;> congr 1
  have hData (eta : ℝ) := SourceIIDGaussianProfileBudget.fixed_gaussian_weight_measurable_bound
    r.val (n-r.val) h0 x {eta} false
  have hMaskM : MeasurableSet {p : Shao.Path r.val × Shao.Path (n-r.val) |
      h0≤Shao.energy p.2 ∧ (Shao.energy p.2<H ∨ n-r.val≤m)} := by
    have he : Measurable (fun p : Shao.Path r.val × Shao.Path (n-r.val) => Shao.energy p.2) :=
      Shao.measurable_energy.comp measurable_snd
    have hm : MeasurableSet {p : Shao.Path r.val × Shao.Path (n-r.val) | n-r.val≤m} := by
      by_cases hc : n-r.val≤m <;> simp [hc]
    exact (measurableSet_le measurable_const he).inter
      ((measurableSet_lt he measurable_const).union hm)
  have hfM : Measurable f :=
    Measurable.ite hMaskM ((hData 1).1.add (hData (-1)).1) measurable_const
  have hfBound (p : Shao.Path r.val × Shao.Path (n-r.val)) :
      |f p| ≤ 2*(1+Real.sqrt ((n-r.val : ℕ) : ℝ))^3 := by
    dsimp only [f]
    split_ifs
    · calc
        _ ≤ |SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {1} false p.1 p.2|+
            |SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {-1} false p.1 p.2| :=
          abs_add_le _ _
        _ ≤ (1+Real.sqrt ((n-r.val : ℕ) : ℝ))^3+
            (1+Real.sqrt ((n-r.val : ℕ) : ℝ))^3 := by
          exact add_le_add (by simpa using ((hData 1).2.1 p.1 p.2).2)
            (by simpa using ((hData (-1)).2.1 p.1 p.2).2)
        _ = _ := by ring
    · rw [abs_zero]
      positivity
  have hfI : Integrable f (Pprefix.prod Psuffix) := by
    refine (integrable_const (2*(1+Real.sqrt ((n-r.val : ℕ) : ℝ))^3)).mono'
      hfM.aestronglyMeasurable ?_
    exact ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hfBound p
  have hEq (a : Shao.Path n) : g a = f (split a) := by
    have hEnergy : Shao.energy (Spitzer.tail a r.val r.is_lt.le) =
        remainingEnergy a r.val (Equiv.refl (Fin n)) := by
      have hid : Spitzer.reorder a (Equiv.refl (Fin n))=a := by funext i; rfl
      rw [remainingEnergy,hid]
      exact (SourceIIDGaussianProfileBudget.gaussian_weight_source_state a r h0 x {1} false).1
    have hMask := Shao.C2.AdaptiveRevealCutoff.omitted_adaptive_cutoff_iff
      a h0 H hh0 hH m r.val r.is_lt.le (Equiv.refl (Fin n))
    rw [←hEnergy] at hMask
    dsimp only [g,f,split,tau,nu]
    simp only [hMask,SourceIIDGaussianProfileBudget.rankGaussianWeight]
  have hgM : Measurable g := by
    have he : g=fun a => f (split a) := funext hEq
    rw [he]
    exact hfM.comp hSplit.measurable
  have hgI : Integrable g P := by
    have he : g=fun a => f (split a) := funext hEq
    rw [he]
    exact hSplit.integrable_comp_of_integrable hfI
  refine ⟨hgM,hgI,hfM,hfI,hfI.integral_prod_right,?_⟩
  have he := integral_map (μ:=P) (φ:=split) (f:=f)
    hSplit.measurable.aemeasurable hfM.aestronglyMeasurable
  rw [hSplit.map_eq] at he
  calc
    (∫ a,g a ∂P)=(∫ a,f (split a) ∂P) := integral_congr_ae (ae_of_all _ hEq)
    _=(∫ p,f p ∂Pprefix.prod Psuffix) := he.symm
    _=_ := integral_prod_symm _ hfI

/- Necessary private declaration 6.
The genuine three-domain source bill is compared in expectation, not
pointwise, to precisely PR376's W/n sum. Arbitrary H and m here do not change
their values in the public theorem. No integrability of a target is assumed.
-/
private theorem alo_iid_actual_late_comparison :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ΩB : Type*} [MeasurableSpace ΩB]
        (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : ℝ≥0 → ΩB → ℝ), IsBrownianReal B PB →
        let Q : Measure BridgeNoise := bridgeLaw B PB
        ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
          (Bcap : ℝ), 0 < Bcap → (∀ᵐ z : ℝ ∂rho, |z| ≤ Bcap) →
          (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
          ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), 1 ≤ x →
            Bcap ≤ Real.sqrt (n : ℝ) / (200 * x) →
            let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
            let h0 : ℝ := 4 * beta ^ 2
            ∀ (H : ℝ), 0 < H → ∀ (m : ℕ),
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
              let L : MonitoredDomain → (Shao.Path n × LabelPerm n) → Fin n → ℝ :=
                fun J p r => sourceRetainedRemainder J (F J) (FY J)
                  p.1 x (nu p.1) r.val p.2
              let W : (Shao.Path n × LabelPerm n) → Fin n → ℝ := fun p r =>
                |p.1 (p.2 r)| ^ 3 / Real.sqrt (remainingEnergy p.1 r.val p.2) *
                  (1 + |remainingSum p.1 r.val p.2| /
                    Real.sqrt (remainingEnergy p.1 r.val p.2)) ^ 5
              let lateSuffix : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
                (1 / (n : ℝ)) * ∑ r : Fin n,
                  if n / 2 < r.val ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2
                  then W p r else 0
              let lateActual : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
                ∑ r : Fin n,
                  if n / 2 < r.val ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then
                    |L .interval p r| + |L .upper p r| + |L .lower p r| +
                      max (-sourceSeparatedOvershoot .interval (FY .interval)
                        p.1 x (nu p.1) r.val p.2) 0
                  else 0
              Measurable lateActual ∧ Integrable lateActual (revealLaw P) ∧
                Measurable lateSuffix ∧ Integrable lateSuffix (revealLaw P) ∧
                (∫ p, lateActual p ∂revealLaw P) ≤
                  C * (∫ p, lateSuffix p ∂revealLaw P)
 := by
  classical
  obtain ⟨CF,hCF,hFixed⟩ := alo_iid_fixed_suffix_weighted_bound
  let C0 : ℝ :=
    2*(2*Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant+40)+2*8000100
  have hC0 : 0<C0 := by
    dsimp [C0]
    linarith [Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant_nonneg]
  refine ⟨2*C0*CF,by positivity,?_⟩
  intro ΩB mΩB PB hPB B hB Q rho hRho Bcap hBcap hBound hmean hsecond
    n hn x hx hsmall beta h0 H hH m P nu tau F FY L W lateSuffix lateActual
  letI : IsProbabilityMeasure rho := hRho
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw B PB hB
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  letI : IsProbabilityMeasure (revealLaw P) := by unfold revealLaw; infer_instance
  have hx0 : 0<x := by linarith only [hx]
  have hnR : 0<(n : ℝ) := Nat.cast_pos.2 hn
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
  have hBeta : 1≤beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one rho h2 h3 hsecond
  have hh0 : 0<h0 := by dsimp [h0]; nlinarith
  have hh04 : 4≤h0 := by dsimp [h0]; nlinarith
  let Pt : (t : ℕ) → Measure (Shao.Path t) := fun t => Measure.pi (fun _ : Fin t => rho)
  let R : (Shao.Path n × LabelPerm n) → Shao.Path n := fun p => Spitzer.reorder p.1 p.2
  have hRm : Measurable R := by
    apply measurable_from_prod_countable_left
    intro sigma
    exact Measurable.of_eval fun i => measurable_pi_apply (sigma i)
  let X : Fin n → Shao.Path n → ℝ := fun i a => a i
  have hXm (i : Fin n) : Measurable (X i) := measurable_pi_apply i
  have hIndep : iIndepFun X P :=
    iIndepFun_pi (X:=fun _ : Fin n => (id : ℝ→ℝ)) (fun _ => measurable_id.aemeasurable)
  have hLaw (i : Fin n) : IdentDistrib (X i) (id : ℝ→ℝ) P rho := by
    refine ⟨(hXm i).aemeasurable,measurable_id.aemeasurable,?_⟩
    simpa only [Measure.map_id] using (measurePreserving_eval (μ:=fun _ : Fin n => rho) i).map_eq
  have hMap : Measure.map R (revealLaw P)=P :=
    iid_randomPermutation_map_eq_pi P rho X hXm hIndep hLaw
  have hPath : IdentDistrib R (id : Shao.Path n → Shao.Path n) (revealLaw P) P := by
    refine ⟨hRm.aemeasurable,measurable_id.aemeasurable,?_⟩
    simpa only [Measure.map_id] using hMap
  let tail : (r : Fin n) → Shao.Path n → Shao.Path (n-r.val) := fun r a =>
    Spitzer.tail a r.val r.is_lt.le
  have hTail (r : Fin n) : MeasurePreserving (tail r) P (Pt (n-r.val)) := by
    let split : Shao.Path n → Shao.Path r.val × Shao.Path (n-r.val) := fun a =>
      (Spitzer.head a r.val r.is_lt.le,tail r a)
    have hSplit : MeasurePreserving split P ((Pt r.val).prod (Pt (n-r.val))) := by
      let e : Fin r.val ⊕ Fin (n-r.val) ≃ Fin n :=
        finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le r.is_lt.le))
      have h1 := (measurePreserving_piCongrLeft (fun _ : Fin n => rho) e).symm
      have h2 := measurePreserving_sumPiEquivProdPi (fun _ : Fin r.val ⊕ Fin (n-r.val) => rho)
      convert h2.comp h1 using 1
      ext a i <;> change a _ = a _ <;> congr 1
    letI : IsProbabilityMeasure (Pt r.val) := by dsimp [Pt]; infer_instance
    exact (measurePreserving_snd (μ:=Pt r.val) (ν:=Pt (n-r.val))).comp hSplit
  let S : (r : Fin n) → (Shao.Path n × LabelPerm n) → Shao.Path (n-r.val) :=
    fun r p => tail r (R p)
  have hSeed (r : Fin n) : IdentDistrib (S r) (id : Shao.Path (n-r.val) → Shao.Path (n-r.val))
      (revealLaw P) (Pt (n-r.val)) := by
    have hId : IdentDistrib (tail r) (id : Shao.Path (n-r.val) → Shao.Path (n-r.val))
        P (Pt (n-r.val)) := by
      refine ⟨(hTail r).measurable.aemeasurable,measurable_id.aemeasurable,?_⟩
      simpa only [Measure.map_id] using (hTail r).map_eq
    exact (hPath.comp (hTail r).measurable).trans hId
  have hState (r : Fin n) (p : Shao.Path n × LabelPerm n) :
      Shao.energy (S r p)=remainingEnergy p.1 r.val p.2 ∧
      Shao.prefixSum (S r p) (n-r.val)=remainingSum p.1 r.val p.2 ∧
      SourceIIDGaussianProfileBudget.firstValue (S r p)=p.1 (p.2 r) := by
    have hh := SourceIIDGaussianProfileBudget.gaussian_weight_source_state (R p) r h0 x ∅ false
    have hE : Shao.energy (R p)=Shao.energy p.1 := by
      simpa only [R,Shao.energy,Spitzer.reorder] using Equiv.sum_comp p.2 (fun i => (p.1 i)^2)
    have hSum : Shao.prefixSum (R p) n=Shao.prefixSum p.1 n := by
      simpa only [R,Shao.prefixSum_length,Spitzer.reorder] using Equiv.sum_comp p.2 p.1
    exact ⟨by simpa only [remainingEnergy,hE] using hh.1,
      by simpa only [remainingSum,hSum] using hh.2.1,hh.2.2.2.1⟩
  let Z : (r : Fin n) → Shao.Path (n-r.val) → ℝ := fun r u =>
    if h0≤Shao.energy u ∧ (Shao.energy u<H ∨ n-r.val≤m) then
      |SourceIIDGaussianProfileBudget.firstValue u|^3/Real.sqrt (Shao.energy u)*
        (1+|Shao.prefixSum u (n-r.val)|/Real.sqrt (Shao.energy u))^5
    else 0
  have hZM (r : Fin n) : Measurable (Z r) := by
    have ht : 0<n-r.val := Nat.sub_pos_of_lt r.is_lt
    have hFirst : Measurable (SourceIIDGaussianProfileBudget.firstValue : Shao.Path (n-r.val)→ℝ) := by
      change Measurable (fun u : Shao.Path (n-r.val) => SourceIIDGaussianProfileBudget.firstValue u)
      simpa only [SourceIIDGaussianProfileBudget.firstValue,dif_pos ht] using
        (show Measurable (fun u : Shao.Path (n-r.val) => u (⟨0,ht⟩ : Fin (n-r.val))) from
          measurable_pi_apply _)
    have hmask : MeasurableSet {u : Shao.Path (n-r.val) |
        h0≤Shao.energy u ∧ (Shao.energy u<H ∨ n-r.val≤m)} := by
      by_cases hc : n-r.val≤m
      · simpa only [hc,or_true,and_true] using measurableSet_le measurable_const Shao.measurable_energy
      · simpa only [hc,or_false,Set.setOf_and] using
          (measurableSet_le measurable_const Shao.measurable_energy).inter
            (measurableSet_lt Shao.measurable_energy measurable_const)
    apply Measurable.ite hmask _ measurable_const
    exact (((continuous_abs.measurable.comp hFirst).pow_const 3).div Shao.measurable_energy.sqrt).mul
      ((measurable_const.add ((continuous_abs.measurable.comp (Shao.measurable_prefixSum (n-r.val))).div
        Shao.measurable_energy.sqrt)).pow_const 5)
  have hZ0 (r : Fin n) (u : Shao.Path (n-r.val)) : 0≤Z r u := by dsimp [Z]; split_ifs <;> positivity
  have hZI (r : Fin n) : Integrable (Z r) (Pt (n-r.val)) := by
    letI : IsProbabilityMeasure (Pt (n-r.val)) := by dsimp [Pt]; infer_instance
    have ht : 0<n-r.val := Nat.sub_pos_of_lt r.is_lt
    let i0 : Fin (n-r.val) := ⟨0,ht⟩
    have hEval : Measure.map (fun u : Shao.Path (n-r.val) => u i0) (Pt (n-r.val))=rho :=
      (measurePreserving_eval (μ:=fun _ : Fin (n-r.val) => rho) i0).map_eq
    have hAE : ∀ᵐ u : Shao.Path (n-r.val) ∂Pt (n-r.val),
        |SourceIIDGaussianProfileBudget.firstValue u|≤Bcap := by
      have hh : ∀ᵐ z : ℝ ∂Measure.map (fun u : Shao.Path (n-r.val) => u i0) (Pt (n-r.val)),
          |z|≤Bcap := by rw [hEval]; exact hBound
      have hh' := (ae_map_iff (measurable_pi_apply i0).aemeasurable
        (measurableSet_le continuous_abs.measurable measurable_const)).1 hh
      simpa only [SourceIIDGaussianProfileBudget.firstValue,dif_pos ht,i0] using hh'
    refine (integrable_const (Bcap^3*(1+Real.sqrt (n : ℝ))^5)).mono'
      (hZM r).aestronglyMeasurable ?_
    filter_upwards [hAE] with u hu
    rw [Real.norm_eq_abs,abs_of_nonneg (hZ0 r u)]
    dsimp only [Z]
    split_ifs with hs
    · have hT4 : (4:ℝ)≤Shao.energy u := hh04.trans hs.1
      have hT : 0<Shao.energy u := by linarith
      have hS : 1≤Real.sqrt (Shao.energy u) := by
        have hh := Real.sqrt_le_sqrt (show (1:ℝ)≤Shao.energy u by linarith)
        simpa only [Real.sqrt_one] using hh
      have hmark : |SourceIIDGaussianProfileBudget.firstValue u|^3/Real.sqrt (Shao.energy u)≤Bcap^3 := by
        apply (div_le_iff₀ (by positivity)).2
        exact (pow_le_pow_left₀ (abs_nonneg _) hu 3).trans
          (le_mul_of_one_le_right (by positivity) hS)
      have hD := (SourceMarkedSuffixAveraging.suffix_normalized_geometry u).2.2.2.2.2.1.2
      have hD' : 1+|Shao.prefixSum u (n-r.val)|/Real.sqrt (Shao.energy u)≤1+Real.sqrt (n : ℝ) := by
        have htN : ((n-r.val : ℕ):ℝ)≤(n:ℝ) := Nat.cast_le.2 (Nat.sub_le _ _)
        have hsz := Real.sqrt_le_sqrt htN
        have hdEq : SourceMarkedSuffixAveraging.suffixD u=
            1+|Shao.prefixSum u (n-r.val)|/Real.sqrt (Shao.energy u) := by
          simp only [SourceMarkedSuffixAveraging.suffixD,if_pos hT]
        rw [hdEq] at hD
        linarith
      exact mul_le_mul hmark (pow_le_pow_left₀ (by positivity) hD' 5)
        (by positivity) (by positivity)
    · positivity
  let selectedW : Fin n → (Shao.Path n × LabelPerm n) → ℝ := fun r p =>
    if n/2<r.val ∧ tau p.1 p.2≤r.val ∧ r.val<nu p.1 p.2 then W p r else 0
  have hCut (r : Fin n) (p : Shao.Path n × LabelPerm n) :
      (tau p.1 p.2≤r.val ∧ r.val<nu p.1 p.2) ↔
        h0≤remainingEnergy p.1 r.val p.2 ∧
          (remainingEnergy p.1 r.val p.2<H ∨ n-r.val≤m) :=
    Shao.C2.AdaptiveRevealCutoff.omitted_adaptive_cutoff_iff p.1 h0 H hh0 hH m r.val r.is_lt.le p.2
  have hWval (r : Fin n) (p : Shao.Path n × LabelPerm n) :
      selectedW r p = if n/2<r.val then Z r (S r p) else 0 := by
    dsimp only [selectedW,Z,W]
    rw [(hState r p).1,(hState r p).2.1,(hState r p).2.2]
    by_cases hr : n/2<r.val
    · simp only [hr,true_and,if_true]
      simp only [hCut r p]
    · simp only [hr,false_and,if_false]
  have hWM (r : Fin n) : Measurable (selectedW r) := by
    have he : selectedW r=fun p => if n/2<r.val then Z r (S r p) else 0 := funext (hWval r)
    rw [he]
    by_cases hr : n/2<r.val
    · simp only [if_pos hr]
      exact (hZM r).comp ((hTail r).measurable.comp hRm)
    · simp only [if_neg hr]
      exact measurable_const
  have hWI (r : Fin n) : Integrable (selectedW r) (revealLaw P) := by
    have he : selectedW r=fun p => if n/2<r.val then Z r (S r p) else 0 := funext (hWval r)
    rw [he]
    by_cases hr : n/2<r.val
    · simp only [if_pos hr]
      exact ((hSeed r).comp (hZM r)).integrable_iff.2 (hZI r)
    · simp only [if_neg hr]
      exact integrable_zero _ _ _
  have hWnn (r : Fin n) (p : Shao.Path n × LabelPerm n) : 0≤selectedW r p := by
    rw [hWval]; split_ifs <;> positivity
  have hSuffixM : Measurable lateSuffix :=
    (Finset.measurable_sum _ fun r _ => hWM r).const_mul (1/(n : ℝ))
  have hSuffixI : Integrable lateSuffix (revealLaw P) :=
    (integrable_finsetSum _ fun r _ => hWI r).const_mul (1/(n : ℝ))
  have hReflection : HalflineReflectionIdentities Q := by
    constructor
    · intro w y T z hw hT hy hz
      exact Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula B PB hB w y T z hT hy hz
    · intro w y T z hw hT hy hz
      exact Shao.C2.BridgeLowerIdentification.bridge_lower_formula B PB hB w y T z hT hy hz
  have hRegular (w y T z : ℝ) (hw : 0<w) (hT : 0<T) (hy : |y|<w) (hz : |z|<w) :
      DifferentiableAt ℝ (fun Y => Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w Y T z) y :=
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
  have hnu (sigma : LabelPerm n) : Measurable (fun a : Shao.Path n => nu a sigma) :=
    actual_energy_cutoff_measurable h0 hh0 sigma
  have htau (sigma : LabelPerm n) : Measurable (fun a : Shao.Path n => tau a sigma) :=
    (actual_energy_cutoff_measurable H hH sigma).min measurable_const
  have hParts (J : MonitoredDomain) := source_parts_measurable_integrable J (F J) (FY J)
    (hFm J) (hData J).1 4 (hData J).2 P x hx0 nu hnu
  let bill : Fin n → (Shao.Path n × LabelPerm n) → ℝ := fun r p =>
    |L .interval p r|+|L .upper p r|+|L .lower p r|+
      max (-sourceSeparatedOvershoot .interval (FY .interval) p.1 x (nu p.1) r.val p.2) 0
  have hLM (J : MonitoredDomain) (r : Fin n) : Measurable (fun p => L J p r) := by
    apply measurable_from_prod_countable_left
    intro sigma
    exact ((hParts J).1 sigma r.val).1
  have hOM (r : Fin n) : Measurable (fun p : Shao.Path n × LabelPerm n =>
      sourceSeparatedOvershoot .interval (FY .interval) p.1 x (nu p.1) r.val p.2) := by
    apply measurable_from_prod_countable_left
    intro sigma
    exact ((hParts .interval).1 sigma r.val).2
  have hBillM (r : Fin n) : Measurable (bill r) :=
    (((continuous_abs.measurable.comp (hLM .interval r)).add
      (continuous_abs.measurable.comp (hLM .upper r))).add
      (continuous_abs.measurable.comp (hLM .lower r))).add
      ((hOM r).neg.max measurable_const)
  have hLI (J : MonitoredDomain) (r : Fin n) : Integrable (fun p => L J p r) (revealLaw P) :=
    ((hParts J).2.1 r.val).1
  have hOI (r : Fin n) : Integrable (fun p : Shao.Path n × LabelPerm n =>
      sourceSeparatedOvershoot .interval (FY .interval) p.1 x (nu p.1) r.val p.2) (revealLaw P) :=
    ((hParts .interval).2.1 r.val).2
  have hNegI (r : Fin n) : Integrable (fun p : Shao.Path n × LabelPerm n =>
      max (-sourceSeparatedOvershoot .interval (FY .interval) p.1 x (nu p.1) r.val p.2) 0)
      (revealLaw P) := by
    refine (hOI r).abs.mono' (((hOM r).neg.max measurable_const).aestronglyMeasurable) ?_
    exact ae_of_all _ fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
      exact max_le (neg_le_abs _) (abs_nonneg _)
  have hBillI (r : Fin n) : Integrable (bill r) (revealLaw P) :=
    ((((hLI .interval r).abs.add (hLI .upper r).abs).add (hLI .lower r).abs).add (hNegI r))
  let selectedA : Fin n → (Shao.Path n × LabelPerm n) → ℝ := fun r p =>
    if n/2<r.val ∧ tau p.1 p.2≤r.val ∧ r.val<nu p.1 p.2 then bill r p else 0
  have hGuard (r : Fin n) : MeasurableSet {p : Shao.Path n × LabelPerm n |
      n/2<r.val ∧ tau p.1 p.2≤r.val ∧ r.val<nu p.1 p.2} := by
    have hm : Measurable (fun p : Shao.Path n × LabelPerm n =>
        if n/2<r.val ∧ tau p.1 p.2≤r.val ∧ r.val<nu p.1 p.2 then (1:ℝ) else 0) := by
      apply measurable_from_prod_countable_left
      intro sigma
      by_cases hr : n/2<r.val
      · simp only [hr,true_and]
        exact Measurable.ite ((measurableSet_le (htau sigma) measurable_const).inter
          (measurableSet_lt measurable_const (hnu sigma))) measurable_const measurable_const
      · simp only [hr,false_and,ite_false]
        exact measurable_const
    simpa only [Set.preimage,Set.mem_singleton_iff,ite_eq_left_iff,zero_ne_one,imp_false,not_not]
      using hm (measurableSet_singleton (1:ℝ))
  have hAM (r : Fin n) : Measurable (selectedA r) := (hBillM r).ite (hGuard r) measurable_const
  have hAI (r : Fin n) : Integrable (selectedA r) (revealLaw P) := by
    convert (hBillI r).indicator (hGuard r) using 1
    funext p
    simp only [selectedA,Set.indicator_apply,Set.mem_setOf_eq]
  have hActualM : Measurable lateActual := Finset.measurable_sum _ fun r _ => hAM r
  have hActualI : Integrable lateActual (revealLaw P) := integrable_finsetSum _ fun r _ => hAI r
  let g : Fin n → Shao.Path n → ℝ := fun r a =>
    if tau a (Equiv.refl (Fin n))≤r.val ∧ r.val<nu a (Equiv.refl (Fin n)) then
      SourceIIDGaussianProfileBudget.rankGaussianWeight h0 x {1} false a r+
        SourceIIDGaussianProfileBudget.rankGaussianWeight h0 x {-1} false a r else 0
  let f : (r : Fin n) → Shao.Path r.val × Shao.Path (n-r.val) → ℝ := fun r p =>
    if h0≤Shao.energy p.2 ∧ (Shao.energy p.2<H ∨ n-r.val≤m) then
      SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {1} false p.1 p.2+
        SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {-1} false p.1 p.2 else 0
  have hFub (r : Fin n) := alo_iid_masked_rank_fubini rho r h0 H x hh0 hH m
  have hgM (r : Fin n) : Measurable (g r) := (hFub r).1
  have hgI (r : Fin n) : Integrable (g r) P := (hFub r).2.1
  have hgRI (r : Fin n) : Integrable (fun p => g r (R p)) (revealLaw P) :=
    ((hPath.comp (hgM r)).integrable_iff.2 (hgI r))
  let eg : Fin n → (Shao.Path n × LabelPerm n) → ℝ := fun r p =>
    if n/2<r.val then g r (R p) else 0
  have hegI (r : Fin n) : Integrable (eg r) (revealLaw P) := by
    by_cases hr : n/2<r.val
    · simpa only [eg,if_pos hr] using hgRI r
    · simp only [eg,if_neg hr]
      exact integrable_zero _ _ _
  have hMaskR (r : Fin n) (p : Shao.Path n × LabelPerm n) :
      (tau (R p) (Equiv.refl (Fin n))≤r.val ∧ r.val<nu (R p) (Equiv.refl (Fin n))) ↔
        (tau p.1 p.2≤r.val ∧ r.val<nu p.1 p.2) := by
    have hE : remainingEnergy (R p) r.val (Equiv.refl (Fin n))=remainingEnergy p.1 r.val p.2 := by
      unfold remainingEnergy
      have he : Shao.energy (R p)=Shao.energy p.1 := by
        simpa only [R,Shao.energy,Spitzer.reorder] using Equiv.sum_comp p.2 (fun i => (p.1 i)^2)
      rw [he]
      rfl
    rw [hCut r (R p,Equiv.refl (Fin n)),hCut r p,hE]
  have hDom (r : Fin n) (p : Shao.Path n × LabelPerm n) : selectedA r p≤C0*eg r p := by
    by_cases hr : n/2<r.val
    · by_cases hs : tau p.1 p.2≤r.val ∧ r.val<nu p.1 p.2
      · have hsR := (hMaskR r p).2 hs
        simp only [selectedA,eg,g,hr,true_and,if_pos hs,if_pos hsR,if_true]
        exact alo_actual_three_domain_rank_domination PB B hB p.1 h0 x hh0 hx0
          (nu p.1) p.2 le_rfl r
      · have hsR := (not_congr (hMaskR r p)).2 hs
        simp only [selectedA,eg,g,hr,true_and,if_neg hs,if_neg hsR,if_true,mul_zero,le_rfl]
    · simp only [selectedA,eg,hr,false_and,if_false,mul_zero,le_rfl]
  have hRank (r : Fin n) : (∫ p,eg r p ∂revealLaw P) ≤
      (2*CF/(n : ℝ))*(∫ p,selectedW r p ∂revealLaw P) := by
    by_cases hr : n/2<r.val
    · have hhalf : (n : ℝ)/2≤(r.val : ℝ) := by
        have hnat : n≤2*r.val := by omega
        have hcast : (n : ℝ)≤2*(r.val : ℝ) := by exact_mod_cast hnat
        linarith only [hcast]
      have hrR : 0<(r.val : ℝ) := by linarith only [hnR,hhalf]
      have hInner (u : Shao.Path (n-r.val)) :
          (∫ v,f r (v,u) ∂Pt r.val) ≤ CF*Z r u/(r.val : ℝ) := by
        by_cases hs : h0≤Shao.energy u ∧ (Shao.energy u<H ∨ n-r.val≤m)
        · have hT : 0<Shao.energy u := hh0.trans_le hs.1
          have hFix := hFixed rho Bcap hBcap hBound hmean hsecond n hn x hx hsmall
            r.val r.is_lt.le hhalf (n-r.val) u
          dsimp only [f,Z]
          simp only [if_pos hs]
          have hAct : 0<Shao.energy u ∧ h0≤Shao.energy u := ⟨hT,hs.1⟩
          have hFixB := hFix.2.2
          change (∫ v, (SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {1} false v u+
            SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {-1} false v u) ∂Pt r.val) ≤
              CF*(if 0<Shao.energy u ∧ h0≤Shao.energy u then
                |SourceIIDGaussianProfileBudget.firstValue u|^3/Real.sqrt (Shao.energy u)*
                  (1+|Shao.prefixSum u (n-r.val)|/Real.sqrt (Shao.energy u))^5 else 0)/(r.val : ℝ)
            at hFixB
          simpa only [if_pos hAct] using hFixB
        · have hfzero : (fun v => f r (v,u))=fun _ => (0:ℝ) := by
            funext v; simp only [f,if_neg hs]
          rw [hfzero,integral_zero]
          simp only [Z,if_neg hs,mul_zero,zero_div,le_rfl]
      have hOuter := integral_mono ((hFub r).2.2.2.2.1)
        ((hZI r).const_mul CF |>.div_const (r.val : ℝ)) hInner
      rw [integral_div,integral_const_mul] at hOuter
      have heW : (∫ p,selectedW r p ∂revealLaw P)=(∫ u,Z r u ∂Pt (n-r.val)) := by
        calc
          _=(∫ p,Z r (S r p) ∂revealLaw P) :=
            integral_congr_ae (ae_of_all _ fun p => by rw [hWval,if_pos hr])
          _=_ := ((hSeed r).comp (hZM r)).integral_eq
      have heG : (∫ p,eg r p ∂revealLaw P)=(∫ a,g r a ∂P) := by
        calc
          _=(∫ p,g r (R p) ∂revealLaw P) := by simp only [eg,if_pos hr]
          _=_ := (hPath.comp (hgM r)).integral_eq
      rw [heG,heW]
      have heF := (hFub r).2.2.2.2.2
      change (∫ a,g r a ∂P)=(∫ u,(∫ v,f r (v,u) ∂Pt r.val) ∂Pt (n-r.val)) at heF
      rw [heF]
      apply hOuter.trans
      have hZint : 0≤(∫ u,Z r u ∂Pt (n-r.val)) := integral_nonneg (hZ0 r)
      have hrecip : 1/(r.val : ℝ)≤2/(n : ℝ) := by
        apply (div_le_div_iff₀ hrR hnR).2
        linarith only [hhalf]
      have hz := mul_le_mul_of_nonneg_left hrecip (mul_nonneg hCF.le hZint)
      convert hz using 1 <;> ring
    · have heg0 : eg r=fun _ => (0:ℝ) := by funext p; simp only [eg,if_neg hr]
      have hW0 : selectedW r=fun _ => (0:ℝ) := by
        funext p; rw [hWval,if_neg hr]
      simp only [heg0,hW0,integral_zero,mul_zero,le_rfl]
  refine ⟨hActualM,hActualI,hSuffixM,hSuffixI,?_⟩
  have hIntDom := integral_mono hActualI
    ((integrable_finsetSum _ fun r _ => hegI r).const_mul C0)
    (fun p => by
      change (∑ r : Fin n,selectedA r p)≤C0*∑ r : Fin n,eg r p
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun r _ => hDom r p)
  rw [integral_const_mul,integral_finsetSum Finset.univ (fun r _ => hegI r)] at hIntDom
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun r _ => hRank r)
  rw [←Finset.mul_sum,←integral_finsetSum Finset.univ (fun r _ => hWI r)] at hsum
  have hh := hIntDom.trans (mul_le_mul_of_nonneg_left hsum hC0.le)
  have he : (∫ p,lateSuffix p ∂revealLaw P)=
      (1/(n : ℝ))*(∫ p,∑ r : Fin n,selectedW r p ∂revealLaw P) := integral_const_mul _ _
  rw [he]
  convert hh using 1 <;> ring

/- Sole new public declaration.
This is the requested original late omitted L + interval O_- statement itself.
K, beta, delta, u, h0, H, m, P, nu, tau, Q, F, FY and L have exact full values.
-/
theorem iid_actual_late_omitted_retained_negative_budget :
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
            let L : MonitoredDomain → (Shao.Path n × LabelPerm n) → Fin n → ℝ :=
              fun J p r => sourceRetainedRemainder J (F J) (FY J)
                p.1 x (nu p.1) r.val p.2
            let lateOmitted : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
              ∑ r : Fin n,
                if n / 2 < r.val ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then
                  |L .interval p r| + |L .upper p r| + |L .lower p r| +
                    max (-sourceSeparatedOvershoot .interval (FY .interval)
                      p.1 x (nu p.1) r.val p.2) 0
                else 0
            Measurable lateOmitted ∧ Integrable lateOmitted (revealLaw P) ∧
              (∫ p, lateOmitted p ∂revealLaw P) ≤
                C * beta * Real.sqrt H / (n : ℝ) ∧
              (∫ p, lateOmitted p ∂revealLaw P) ≤
                C * delta * Shao.standardNormalTail x
 := by
  classical
  intro K
  obtain ⟨CA,hCA,hActual⟩ := alo_iid_actual_late_comparison
  obtain ⟨CS,hCS,hSuffix⟩ := SourceLateOmittedSuffixBudget.iid_actual_late_omitted_suffix_budget
  refine ⟨CA*CS,by positivity,?_⟩
  intro ΩB mΩB PB hPB B hB Q rho hRho Bcap hBcap hBound hmean hsecond
    n hn x hx hsmall beta delta u hu h0 H m P nu tau F FY L lateOmitted
  letI : IsProbabilityMeasure rho := hRho
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
  have hBeta : 1≤beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one rho h2 h3 hsecond
  have hBeta0 : 0<beta := by linarith
  have hx0 : 0<1+x := by linarith
  have hH : 0<H := by dsimp [H,K]; positivity
  let W : (Shao.Path n × LabelPerm n) → Fin n → ℝ := fun p r =>
    |p.1 (p.2 r)|^3/Real.sqrt (remainingEnergy p.1 r.val p.2)*
      (1+|remainingSum p.1 r.val p.2|/Real.sqrt (remainingEnergy p.1 r.val p.2))^5
  let lateS : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
    (1/(n : ℝ))*∑ r : Fin n,
      if n/2<r.val ∧ tau p.1 p.2≤r.val ∧ r.val<nu p.1 p.2 then W p r else 0
  have hOld := hSuffix rho h2 h3 hmean hsecond n hn x hx hu
  change Measurable lateS ∧ Integrable lateS (revealLaw P) ∧
    (∫ p,lateS p ∂revealLaw P)≤CS*beta*Real.sqrt H/(n : ℝ) ∧
    (∫ p,lateS p ∂revealLaw P)≤CS*delta*Shao.standardNormalTail x at hOld
  have hNew := hActual PB B hB rho Bcap hBcap hBound hmean hsecond
    n hn x (by linarith only [hx]) hsmall H hH m
  change Measurable lateOmitted ∧ Integrable lateOmitted (revealLaw P) ∧
    Measurable lateS ∧ Integrable lateS (revealLaw P) ∧
    (∫ p,lateOmitted p ∂revealLaw P)≤CA*(∫ p,lateS p ∂revealLaw P) at hNew
  refine ⟨hNew.1,hNew.2.1,?_,?_⟩
  · calc
      _≤CA*(∫ p,lateS p ∂revealLaw P) := hNew.2.2.2.2
      _≤CA*(CS*beta*Real.sqrt H/(n : ℝ)) := mul_le_mul_of_nonneg_left hOld.2.2.1 hCA.le
      _=_ := by ring
  · calc
      _≤CA*(∫ p,lateS p ∂revealLaw P) := hNew.2.2.2.2
      _≤CA*(CS*delta*Shao.standardNormalTail x) := mul_le_mul_of_nonneg_left hOld.2.2.2 hCA.le
      _=_ := by ring

end Shao.Probability.SourceActualLateOmittedBudget
