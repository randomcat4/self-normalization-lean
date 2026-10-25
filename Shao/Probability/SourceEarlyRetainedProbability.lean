/- Mathematics-only candidate. No formal body or Lean/AX authority.
   Actual early rare branch and independent early omitted branch only.
   Regular all-rank payment is already PR363; late strip/record belongs to B. -/
import Shao.Probability.SourceResidualRareSuffix
import Shao.Probability.SourceActualIntervalProfileBudget
import Shao.Probability.SourceIIDGaussianProfileBudget
import Shao.C2.BridgeIntervalImageResolved
import Shao.C2.BridgeHalfLineRetainedBound
import Shao.C2.AuxiliaryRealMarkedFiniteCutoffBudget
import Shao.C2.AdaptiveRevealCutoff
import Shao.C2.AuxiliaryLowEnergyGaussian
import Shao.Probability.GaussianTail

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
noncomputable section
namespace Shao.Probability.SourceEarlyRetainedProbability
open MeasureTheory ProbabilityTheory
open SourcePermutationReveal SourceSeparatedOvershoot
open SourceActualLocalProfileBudget SourceActualIntervalProfileBudget
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open scoped BigOperators Classical NNReal

local instance labelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

private theorem erp_actual_cubic_domination
    {ΩB : Type*} [MeasurableSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → ℝ) (hB : IsBrownianReal B PB)
    {n : ℕ} (a : Shao.Path n) (H x : ℝ) (hH : 0 < H) (hx : 0 < x)
    (nu : LabelPerm n → ℕ) (sigma : LabelPerm n)
    (hcap : nu sigma ≤ energyCutoff a H sigma)
    (r : Fin n) (hr : r.val < nu sigma) :
    let C0 : ℝ :=
      2 * (2 * Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant + 40) + 2 * 8000100
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
        max (-sourceSeparatedOvershoot .interval (FY .interval) a x nu r.val sigma) 0 ≤
      C0 * (|a (sigma r)| / Real.sqrt (remainingEnergy a r.val sigma)) ^ 3 *
        (1 + |remainingSum a r.val sigma| / Real.sqrt (remainingEnergy a r.val sigma)) ^ 3 := by
  classical
  dsimp only
  let C0 : ℝ := 2 * (2 * Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant + 40) + 2 * 8000100
  let Q : Measure BridgeNoise := bridgeLaw B PB
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw B PB hB
  let F : MonitoredDomain → BridgeKernel := fun J => eventCompletionKernel J Q
  let FY : MonitoredDomain → BridgeKernel := fun J =>
    match J with
    | .upper => halflineDerivative .upper
    | .lower => halflineDerivative .lower
    | .interval => intervalDerivative Q
  let L : MonitoredDomain → ℝ := fun J => sourceRetainedRemainder J (F J) (FY J) a x nu r.val sigma
  let w : ℝ := actualWall a x
  let y : ℝ := Shao.prefixSum (Spitzer.reorder a sigma) r.val
  let T : ℝ := remainingEnergy a r.val sigma
  let z : ℝ := Shao.prefixSum a n
  let b : ℝ := a (sigma r)
  let cube : ℝ := (|b| / Real.sqrt T)^3 * (1 + |z-y| / Real.sqrt T)^3
  change |L .interval| + |L .upper| + |L .lower| +
    max (-sourceSeparatedOvershoot .interval (FY .interval) a x nu r.val sigma) 0 ≤
      C0 * (|b| / Real.sqrt T)^3 * (1 + |remainingSum a r.val sigma| / Real.sqrt T)^3
  have hd : remainingSum a r.val sigma = z-y := rfl
  rw [hd]
  conv_rhs => rw [mul_assoc]
  change _ ≤ C0 * cube
  have hT : 0 < T := lt_of_lt_of_le hH
    ((energy_cutoff_data a H hH).2.2 sigma r.val (lt_of_lt_of_le hr hcap)).2
  have hb : b^2 ≤ T := (remaining_population_geometry a r.val r.is_lt.le sigma).2.2.1 r le_rfl
  have hzero : T-b^2=0 → y+b=z := actual_reveal_zero_future_reachable a r sigma
  have hCube : 0 ≤ cube := by dsimp [cube]; positivity
  have hReflection : HalflineReflectionIdentities Q := by
    constructor
    · intro w y T z hw hT hy hz
      simpa only [Shao.C2.HalfLineReflectionFormula.upperReflection] using
        Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula B PB hB w y T z hT hy hz
    · intro w y T z hw hT hy hz
      simpa only [Shao.C2.HalfLineReflectionFormula.lowerReflection] using
        Shao.C2.BridgeLowerIdentification.bridge_lower_formula B PB hB w y T z hT hy hz
  have hRegular (w y T z : ℝ) (hw : 0<w) (hT : 0<T) (hy : |y|<w) (hz : |z|<w) :
      DifferentiableAt ℝ (fun Y => Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w Y T z) y :=
    (Shao.C2.BridgeIntervalImageResolved.sourceIntervalCompletion_spatial_hasDerivAt
      B PB hB w y T z hw hy hz hT).differentiableAt
  have hupper : |L .upper| ≤ 8000100 * cube := by
    by_cases ha : sourceAlive .upper a x r.val sigma
    · have hw : 0 < w := mul_pos hx (Real.sqrt_pos.2 ha.1)
      have hy : Interior .upper w y := ha.2.2 r.val le_rfl
      have hz : Interior .upper w z := ha.2.1
      change y < w at hy
      change z < w at hz
      have hKernel := actual_halfline_kernel_data Q hReflection .upper (by simp)
      have hExt (Y S : ℝ) :
          completionExt .upper (eventCompletionKernel .upper Q) w Y S z =
            Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion Q w Y S z := by
        by_cases hY : Y < w
        · simp [completionExt, Interior,
            Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion,
            hw, hY, hz, eventCompletionKernel]
        · rw [Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion_exterior Q w Y S z
            (by tauto)]
          simp [completionExt, Interior, hY]
      have hDer : deriv (fun Y : ℝ =>
          Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion Q w Y T z) y =
          halflineDerivative .upper (w,y,T,z) := by
        have hf : (fun Y : ℝ =>
            Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion Q w Y T z) =
            (fun Y : ℝ => eventCompletionKernel .upper Q (w,Y,T,z)) := by
          funext Y
          simp only [Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion,
            if_pos hw, if_pos hT, eventCompletionKernel]
        rw [hf]
        exact (hKernel.2.2 w y T z hw hT hy hz).deriv
      have hRem (β : ℝ) :
          localRemainder .upper (eventCompletionKernel .upper Q) (halflineDerivative .upper)
            w y T z β =
          Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion Q w (y+β) (T-β^2) z -
            Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion Q w y T z -
            (β-β^2*(z-y)/T) * deriv (fun Y : ℝ =>
              Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion Q w Y T z) y := by
        unfold localRemainder
        rw [hExt, hDer]
        simp only [Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion,
          if_pos hw, if_pos hT, eventCompletionKernel, compensationCoefficient]
      have hRet :
          localRetainedRemainder .upper (eventCompletionKernel .upper Q) (halflineDerivative .upper)
            w y T z b =
          (if b^2 ≤ T/2 ∧ w ≤ y+b then
            localRemainder .upper (eventCompletionKernel .upper Q) (halflineDerivative .upper)
              w y T z (w-y)
            else localRemainder .upper (eventCompletionKernel .upper Q) (halflineDerivative .upper)
              w y T z b) := by
        by_cases hs : b^2 ≤ T/2 <;> by_cases hc : w ≤ y+b <;>
          simp only [localRetainedRemainder, projectionIncrement, hT, hs, hc,
            true_and, and_self, and_false, and_true, if_true, if_false]
      have hbound := Shao.C2.BridgeHalfLineRetainedBound.actual_upper_retained_bound
        B PB hB w y T z b hw hy hz hT hb hzero
      dsimp only at hbound
      have he : Real.exp (-((max (w-y - (|b| + max (z-y) 0)) 0)^2)/T) ≤ 1 :=
        Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) hT.le)
      have hle := hbound.trans (mul_le_of_le_one_right (by positivity) he)
      have hsource : L .upper = localRetainedRemainder .upper (eventCompletionKernel .upper Q)
          (halflineDerivative .upper) w y T z b := by
        simp only [L, F, FY, sourceRetainedRemainder, dif_pos r.is_lt, hr, ha,
          show 0 < remainingEnergy a r.val sigma from hT, true_and, if_true]
        rfl
      rw [hsource, hRet]
      simpa only [hRem, cube, mul_assoc] using hle
    · simp only [L, F, FY, sourceRetainedRemainder, dif_pos r.is_lt, ha, and_false,
        false_and, if_false, abs_zero]
      exact mul_nonneg (by norm_num) hCube
  have hlower : |L .lower| ≤ 8000100 * cube := by
    by_cases ha : sourceAlive .lower a x r.val sigma
    · have hw : 0 < w := mul_pos hx (Real.sqrt_pos.2 ha.1)
      have hy : Interior .lower w y := ha.2.2 r.val le_rfl
      have hz : Interior .lower w z := ha.2.1
      change -w < y at hy
      change -w < z at hz
      have hKernel := actual_halfline_kernel_data Q hReflection .lower (by simp)
      have hExt (Y S : ℝ) :
          completionExt .lower (eventCompletionKernel .lower Q) w Y S z =
            Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion Q w Y S z := by
        by_cases hY : -w < Y
        · simp [completionExt, Interior,
            Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion,
            hw, hY, hz, eventCompletionKernel]
        · rw [Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion_exterior Q w Y S z
            (by tauto)]
          simp [completionExt, Interior, hY]
      have hDer : deriv (fun Y : ℝ =>
          Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion Q w Y T z) y =
          halflineDerivative .lower (w,y,T,z) := by
        have hf : (fun Y : ℝ =>
            Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion Q w Y T z) =
            (fun Y : ℝ => eventCompletionKernel .lower Q (w,Y,T,z)) := by
          funext Y
          simp only [Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion,
            if_pos hw, if_pos hT, eventCompletionKernel]
        rw [hf]
        exact (hKernel.2.2 w y T z hw hT hy hz).deriv
      have hRem (β : ℝ) :
          localRemainder .lower (eventCompletionKernel .lower Q) (halflineDerivative .lower)
            w y T z β =
          Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion Q w (y+β) (T-β^2) z -
            Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion Q w y T z -
            (β-β^2*(z-y)/T) * deriv (fun Y : ℝ =>
              Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion Q w Y T z) y := by
        unfold localRemainder
        rw [hExt, hDer]
        simp only [Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion,
          if_pos hw, if_pos hT, eventCompletionKernel, compensationCoefficient]
      have hRet :
          localRetainedRemainder .lower (eventCompletionKernel .lower Q) (halflineDerivative .lower)
            w y T z b =
          (if b^2 ≤ T/2 ∧ y+b ≤ -w then
            localRemainder .lower (eventCompletionKernel .lower Q) (halflineDerivative .lower)
              w y T z (-w-y)
            else localRemainder .lower (eventCompletionKernel .lower Q) (halflineDerivative .lower)
              w y T z b) := by
        by_cases hs : b^2 ≤ T/2 <;> by_cases hc : y+b ≤ -w <;>
          simp only [localRetainedRemainder, projectionIncrement, hT, hs, hc,
            true_and, and_self, and_false, and_true, if_true, if_false]
      have hbound := Shao.C2.BridgeHalfLineRetainedBound.actual_lower_retained_bound
        B PB hB w y T z b hw hy hz hT hb hzero
      dsimp only at hbound
      have he : Real.exp (-((max (w+y - (|b| + max (y-z) 0)) 0)^2)/T) ≤ 1 :=
        Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) hT.le)
      have hle := hbound.trans (mul_le_of_le_one_right (by positivity) he)
      have hsource : L .lower = localRetainedRemainder .lower (eventCompletionKernel .lower Q)
          (halflineDerivative .lower) w y T z b := by
        simp only [L, F, FY, sourceRetainedRemainder, dif_pos r.is_lt, hr, ha,
          show 0 < remainingEnergy a r.val sigma from hT, true_and, if_true]
        rfl
      rw [hsource, hRet]
      simpa only [hRem, cube, mul_assoc] using hle
    · simp only [L, F, FY, sourceRetainedRemainder, dif_pos r.is_lt, ha, and_false,
        false_and, if_false, abs_zero]
      exact mul_nonneg (by norm_num) hCube
  have hinterval : |L .interval| +
      max (-sourceSeparatedOvershoot .interval (FY .interval) a x nu r.val sigma) 0 ≤
      2 * (2 * Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant + 40) * cube := by
    by_cases ha : sourceAlive .interval a x r.val sigma
    · have hw : 0 < w := mul_pos hx (Real.sqrt_pos.2 ha.1)
      have hy : |y| < w := abs_lt.mpr (ha.2.2 r.val le_rfl)
      have hz : |z| < w := abs_lt.mpr ha.2.1
      have hKernel := actual_interval_kernel_data Q hReflection hRegular
      have hExt (Y S : ℝ) : completionExt .interval (eventCompletionKernel .interval Q) w Y S z =
          Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w Y S z := by
        by_cases hY : |Y| < w
        · have hYi := abs_lt.mp hY
          have hzi := abs_lt.mp hz
          simp [completionExt, Interior, hw, hYi.1, hYi.2, hzi.1, hzi.2,
            Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion, eventCompletionKernel, hY]
        · rw [Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion_exterior Q w Y S z (by tauto)]
          have hYi : ¬(-w < Y ∧ Y < w) := fun hh => hY (abs_lt.mpr hh)
          simp only [completionExt, Interior, hYi, false_and, and_false, if_false]
      have hDer : deriv (fun Y : ℝ =>
          Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w Y T z) y =
          intervalDerivative Q (w,y,T,z) := by
        have hf : (fun Y : ℝ => Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w Y T z) =
            (fun Y : ℝ => eventCompletionKernel .interval Q (w,Y,T,z)) := by
          funext Y
          exact Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion_pos Q w Y T z hT
        rw [hf]
        exact (hKernel.2.2 w y T z hw hT hy hz).deriv
      have hRem (beta : ℝ) :
          localRemainder .interval (eventCompletionKernel .interval Q) (intervalDerivative Q) w y T z beta =
            Shao.C2.ActualIntervalProjection.sourceRemainder Q w y T z beta := by
        unfold localRemainder Shao.C2.ActualIntervalProjection.sourceRemainder
        rw [hExt, hDer]
        simp only [Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion, if_pos hT,
          eventCompletionKernel, compensationCoefficient]
      have hRet : localRetainedRemainder .interval (eventCompletionKernel .interval Q)
          (intervalDerivative Q) w y T z b = Shao.C2.IntervalGaussianLocal.retainedRemainder Q w y T z b := by
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
          simp only [localRetainedRemainder, projectionIncrement, Shao.C2.IntervalGaussianLocal.retainedRemainder,
            hT, hs, hu, hl, hh, hRem, true_and, and_true, and_false, false_and,
            true_or, or_true, false_or, or_false, if_true, if_false]
      have hNeg : max (-localSeparatedOvershoot .interval (intervalDerivative Q) w y T z b) 0 =
          Shao.C2.IntervalGaussianLocal.negativeOvershoot Q w y T z b := by
        have huEq : -(b-(w-y))*(1-(b+(w-y))*(z-y)/T)*intervalDerivative Q (w,y,T,z) =
            Shao.C2.ActualIntervalProjection.upperOvershoot Q w y T z b := by
          simp only [Shao.C2.ActualIntervalProjection.upperOvershoot,
            Shao.C2.ProjectionOvershoot.projectionOvershoot, Shao.C2.ProjectionOvershoot.projectionFactor, hDer]
        have hlEq : -(b-(-w-y))*(1-(b+(-w-y))*(z-y)/T)*intervalDerivative Q (w,y,T,z) =
            Shao.C2.ActualIntervalProjection.lowerOvershoot Q w y T z b := by
          simp only [Shao.C2.ActualIntervalProjection.lowerOvershoot,
            Shao.C2.ProjectionOvershoot.projectionOvershoot, Shao.C2.ProjectionOvershoot.projectionFactor, hDer]
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
          simp only [localSeparatedOvershoot, projectionIncrement, Shao.C2.IntervalGaussianLocal.negativeOvershoot,
            hT, hs, hu, hl, hh, true_and, and_true, and_false, false_and,
            true_or, or_true, false_or, or_false, if_true, if_false, huEq, hlEq,
            sub_self, neg_zero, zero_mul, max_self]
      have hbound := Shao.C2.BridgeIntervalImageResolved.actual_interval_retained_bound
        B PB hB w y T z b hw hy hz hT hb hzero
      have henv : Shao.C2.IntervalGaussianLargeStep.intervalEnvelope w y T z b ≤ 2 := by
        have hu := (Shao.C2.GaussianWallEnvelope.wallEnvelope_bounds (w-y) |b| (z-y) T hT).2
        have hl := (Shao.C2.GaussianWallEnvelope.wallEnvelope_bounds (w+y) |b| (y-z) T hT).2
        dsimp only [Shao.C2.IntervalGaussianLargeStep.intervalEnvelope]
        linarith only [hu,hl]
      have hCP := Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant_nonneg
      have hle := hbound.trans (mul_le_mul_of_nonneg_left henv (by positivity))
      have hsource : L .interval = localRetainedRemainder .interval (eventCompletionKernel .interval Q)
          (intervalDerivative Q) w y T z b := by
        simp only [L, F, FY, sourceRetainedRemainder, dif_pos r.is_lt, hr, ha,
          show 0 < remainingEnergy a r.val sigma from hT, true_and, if_true]
        rfl
      have hO : sourceSeparatedOvershoot .interval (FY .interval) a x nu r.val sigma =
          localSeparatedOvershoot .interval (intervalDerivative Q) w y T z b := by
        simp only [FY, sourceSeparatedOvershoot, dif_pos r.is_lt, hr, ha,
          show 0 < remainingEnergy a r.val sigma from hT, true_and, if_true]
        rfl
      rw [hsource,hO,hRet,hNeg]
      simpa only [cube, mul_assoc, mul_left_comm, mul_comm] using hle
    · simp only [L, F, FY, sourceRetainedRemainder, sourceSeparatedOvershoot,
        dif_pos r.is_lt, ha, and_false, false_and, if_false, abs_zero, neg_zero,
        max_self, zero_add]
      have hCP := Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant_nonneg
      positivity
  dsimp only [C0]
  nlinarith only [hupper, hlower, hinterval]


private theorem erp_iid_early_low_energy_grid
    (hc : 0 < (1 - Real.exp (-2)) / 8) :
    let c : ℝ := (1 - Real.exp (-2)) / 8
    let CF : ℝ := Classical.choose
      (Shao.C2.AuxiliaryRealMarkedFiniteCutoffBudget.auxiliary_actual_real_marked_finite_cutoff_budget
        (3 : ℝ) (3 : ℝ) (by norm_num) (by norm_num))
    let CS : ℝ := Classical.choose
      (Shao.Probability.raw_gaussian_scalar_budget_integrals (c / 4)
        (div_pos hc (by norm_num)))
    ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho],
        Integrable (fun z : ℝ => z ^ 2) rho →
        Integrable (fun z : ℝ => |z| ^ 3) rho →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        let h0 : ℝ := 4 * beta ^ 2
        ∀ (n : ℕ), 4 ≤ n → ∀ H : ℝ, h0 ≤ H →
          let Pt : (t : ℕ) → Measure (Shao.Path t) :=
            fun t => Measure.pi (fun _ : Fin t => rho)
          let firstCube : (t : ℕ) → Shao.Path t → ℝ := fun t v =>
            if ht : 0 < t then |v ⟨0, ht⟩| ^ 3 else 0
          let low : (t : ℕ) → Shao.Path t → ℝ := fun t v =>
            if 0 < Shao.energy v ∧ h0 ≤ Shao.energy v ∧ Shao.energy v < H then
              firstCube t v / (Real.sqrt (Shao.energy v)) ^ 3 *
                (1 + |Shao.prefixSum v t| / Real.sqrt (Shao.energy v)) ^ 3
            else 0
          (∀ t ∈ Finset.Icc ((n + 1) / 2) n,
            Measurable (low t) ∧ Integrable (low t) (Pt t)) ∧
            (∑ t ∈ Finset.Icc ((n + 1) / 2) n, ∫ v, low t v ∂Pt t) ≤
              (CF * CS * (1 + 4 / c)) * beta * Real.sqrt H / (n : ℝ) := by
  classical
  intro c CF CS rho hrho h2 h3 hmean hsecond beta h0 n hn H hh0H Pt firstCube low
  letI : IsProbabilityMeasure rho := hrho
  have hcpos : 0 < c := hc
  have ha : 0 < c/4 := div_pos hcpos (by norm_num)
  have hCF := Classical.choose_spec
    (Shao.C2.AuxiliaryRealMarkedFiniteCutoffBudget.auxiliary_actual_real_marked_finite_cutoff_budget
      (3 : ℝ) (3 : ℝ) (by norm_num) (by norm_num))
  have hCS := Classical.choose_spec
    (Shao.Probability.raw_gaussian_scalar_budget_integrals (c/4) ha)
  have hCFpos : 0 < CF := hCF.1
  have hCSpos : 0 < CS := hCS.1
  have hn0 : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hnS : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hBeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one rho h2 h3 hsecond
  have hBeta0 : 0 < beta := by linarith
  have hRet := Shao.C2.AuxiliaryThirdMomentTruncation.auxiliary_actual_third_moment_retains_half
    rho h2 h3 hsecond
  have hh0 : 0 < h0 := hRet.1
  have hH : 0 < H := hh0.trans_le hh0H
  let a3 : ℝ → ℝ := fun s => ∫ z : ℝ, |z|^3 * Real.exp (-s*z^2) ∂rho
  let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) rho
  let R0 : ℝ := Shao.truncationBudget normalizedLaw n 0
  let earlyKernel : ℝ → ℝ := fun s => Real.rpow s (1/2 : ℝ) * a3 (s/2) *
    Real.exp (-(c/4)*(n : ℝ)*s)
  let eH : ℝ := Real.exp (-c*(n : ℝ)/(4*H))
  have hScalar := hCS.2 rho n hn0 h2 hsecond
  have hKi : IntegrableOn earlyKernel (Set.Ioi 0) := hScalar.2.2.2.1
  have hKb : (n : ℝ) * (∫ s : ℝ in Set.Ioi 0, earlyKernel s) ≤ CS * R0 :=
    hScalar.2.2.2.2
  have hA3 (s : ℝ) : 0 ≤ a3 s := integral_nonneg (fun z => by positivity)
  have hKn (s : ℝ) (hs : 0 < s) : 0 ≤ earlyKernel s := by
    dsimp only [earlyKernel]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _) (hA3 _)) (Real.exp_pos _).le
  have hKint0 : 0 ≤ ∫ s : ℝ in Set.Ioi 0, earlyKernel s :=
    setIntegral_nonneg measurableSet_Ioi (fun s hs => hKn s hs)
  have hRle : R0 ≤ beta / Real.sqrt (n : ℝ) := by
    have hFi : Integrable (fun z : ℝ => Shao.truncationF (z / Real.sqrt (n : ℝ))) rho := by
      simpa only [div_eq_mul_inv, one_div, mul_comm] using
        Shao.integrable_truncationF_mul rho h2 ((Real.sqrt (n : ℝ))⁻¹)
    have hCi : Integrable (fun z : ℝ => |z / Real.sqrt (n : ℝ)|^3) rho := by
      simpa only [abs_div, abs_of_pos hnS, div_pow] using h3.div_const ((Real.sqrt (n : ℝ))^3)
    have hPoint (z : ℝ) : Shao.truncationF (z / Real.sqrt (n : ℝ)) ≤ |z / Real.sqrt (n : ℝ)|^3 := by
      unfold Shao.truncationF
      have hh := mul_le_mul_of_nonneg_left (min_le_left |z / Real.sqrt (n : ℝ)| (1 : ℝ))
        (sq_nonneg (z / Real.sqrt (n : ℝ)))
      calc
        _ ≤ (z / Real.sqrt (n : ℝ))^2 * |z / Real.sqrt (n : ℝ)| := hh
        _ = _ := by rw [← sq_abs (z / Real.sqrt (n : ℝ))]; ring
    calc
      R0 = (n : ℝ) * ∫ z : ℝ, Shao.truncationF (z / Real.sqrt (n : ℝ)) ∂rho := by
        dsimp [R0, normalizedLaw, Shao.truncationBudget]
        simp only [add_zero, one_mul]
        rw [integral_map (μ := rho) (φ := fun z : ℝ => z / Real.sqrt (n : ℝ))
          (f := Shao.truncationF) (measurable_id.div_const _).aemeasurable
          Shao.continuous_truncationF.aestronglyMeasurable]
      _ ≤ (n : ℝ) * ∫ z : ℝ, |z / Real.sqrt (n : ℝ)|^3 ∂rho :=
        mul_le_mul_of_nonneg_left (integral_mono hFi hCi hPoint) hnR.le
      _ = beta / Real.sqrt (n : ℝ) := by
        simp only [abs_div, abs_of_pos hnS, div_pow]
        rw [integral_div]
        change (n : ℝ) * (beta / Real.sqrt (n : ℝ)^3) = beta / Real.sqrt (n : ℝ)
        have hs := Real.sq_sqrt hnR.le
        field_simp <;> nlinarith
  have hper (t : ℕ) (htmem : t ∈ Finset.Icc ((n+1)/2) n) :
      Measurable (low t) ∧ Integrable (low t) (Pt t) ∧
        (∫ v, low t v ∂Pt t) ≤ CF * eH * (∫ s : ℝ in Set.Ioi 0, earlyKernel s) := by
    have ht : 0 < t := by have := (Finset.mem_Icc.1 htmem).1; omega
    have htmNat : n ≤ 4*(t-1) := by have := (Finset.mem_Icc.1 htmem).1; omega
    have htm : (n : ℝ)/4 ≤ ((t-1 : ℕ) : ℝ) := by
      have h : (n : ℝ) ≤ 4*((t-1 : ℕ) : ℝ) := by exact_mod_cast htmNat
      linarith
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
    have hFinite := hCF.2 rho h2 hmean hsecond m h0 H hh0 hh0H
    have hlow (v : Shao.Path (m+1)) : low (m+1) v =
        if 0 < Shao.energy v ∧ h0 ≤ Shao.energy v ∧ Shao.energy v < H then
          |v 0|^3 * Real.rpow (Shao.energy v) (-(3 : ℝ)/2) *
            Real.rpow (1+|Shao.prefixSum v (m+1)|/Real.sqrt (Shao.energy v)) (3 : ℝ)
        else 0 := by
      dsimp only [low,firstCube]
      simp only [show 0 < m+1 by omega, dite_true]
      split_ifs with hv
      · have hInv : 1 / Real.sqrt (Shao.energy v)^3 = Real.rpow (Shao.energy v) (-(3 : ℝ)/2) := by
          rw [Real.rpow_eq_pow,Real.sqrt_eq_rpow,← Real.rpow_mul_natCast hv.1.le,one_div]
          rw [show -(3 : ℝ)/2 = -((1/2 : ℝ)*(3 : ℕ)) by norm_num,
            Real.rpow_neg hv.1.le]
        have hNat (z : ℝ) : Real.rpow z (3 : ℝ) = z^3 := Real.rpow_natCast z 3
        rw [← hInv,hNat]
        simp only [div_eq_mul_inv,one_div,one_mul]
        rfl
      · rfl
    have hEq : low (m+1) = _ := funext hlow
    have hLowM : Measurable (low (m+1)) := by
      dsimp only [low]
      apply Measurable.ite
        ((measurableSet_lt measurable_const Shao.measurable_energy).inter
          ((measurableSet_le measurable_const Shao.measurable_energy).inter
          (measurableSet_lt Shao.measurable_energy measurable_const)))
      · dsimp only [firstCube]
        simp only [show 0 < m+1 by omega, dite_true]
        exact (((continuous_abs.measurable.comp (measurable_pi_apply (X := fun _ : Fin (m+1) => ℝ) _)).pow_const 3).div
          (Shao.measurable_energy.sqrt.pow_const 3)).mul
          ((measurable_const.add ((continuous_abs.measurable.comp (Shao.measurable_prefixSum (m+1))).div
            Shao.measurable_energy.sqrt)).pow_const 3)
      · exact measurable_const
    have hLowI : Integrable (low (m+1)) (Pt (m+1)) := by
      rw [hEq]
      exact hFinite.1
    have hGamma : (if (1/2 : ℝ) ≤ ∫ z : ℝ, if z^2 ≤ h0 then z^2 else 0 ∂rho then -c else 1) = -c :=
      if_pos hRet.2
    dsimp only [c] at hGamma
    let kernel : ℝ → ℝ := fun s => Real.rpow s (1/2 : ℝ) * a3 (s/2) *
      Real.exp (-c*(s+1/H)*(m : ℝ))
    have hFint : IntegrableOn kernel (Set.Ioo 0 (1/h0)) := by
      simpa only [hGamma,show (3 : ℝ)/2-1=1/2 by norm_num] using hFinite.2.1
    have hFb : (∫ v, low (m+1) v ∂Pt (m+1)) ≤ CF * ∫ s : ℝ in Set.Ioo 0 (1/h0), kernel s := by
      rw [hEq]
      let fk : ℝ → ℝ := fun s => Real.rpow s ((3 : ℝ)/2-1) * a3 (s/2) *
        Real.exp ((if (1/2 : ℝ) ≤ ∫ z : ℝ, if z^2 ≤ h0 then z^2 else 0 ∂rho then -c else 1)*(s+1/H)*(m : ℝ))
      have hfk : fk = kernel := by
        funext s
        dsimp only [fk,kernel,c]
        rw [hGamma]
        norm_num
      have hraw : (∫ v : Shao.Path (m+1),
          (if 0 < Shao.energy v ∧ h0 ≤ Shao.energy v ∧ Shao.energy v < H then
            |v 0|^3 * Real.rpow (Shao.energy v) (-(3 : ℝ)/2) *
              Real.rpow (1+|Shao.prefixSum v (m+1)|/Real.sqrt (Shao.energy v)) (3 : ℝ)
          else 0) ∂Pt (m+1)) ≤ CF * ∫ s : ℝ in Set.Ioo 0 (1/h0), fk s := hFinite.2.2
      rwa [hfk] at hraw
    have hKsmall : IntegrableOn earlyKernel (Set.Ioo 0 (1/h0)) := hKi.mono_set (fun s hs => hs.1)
    have hdom : kernel ≤ᵐ[volume.restrict (Set.Ioo 0 (1/h0))] fun s => eH*earlyKernel s := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      have hExp : Real.exp (-c*(s+1/H)*(m : ℝ)) ≤
          eH * Real.exp (-(c/4)*(n : ℝ)*s) := by
        rw [show eH * Real.exp (-(c/4)*(n : ℝ)*s) =
            Real.exp (-c*(n : ℝ)/(4*H) + -(c/4)*(n : ℝ)*s) by
          dsimp only [eH]; rw [Real.exp_add]]
        apply Real.exp_le_exp.2
        have hm : (n : ℝ)/4 ≤ (m : ℝ) := by simpa only [Nat.succ_sub_one] using htm
        have hp := mul_nonneg (mul_nonneg hcpos.le (add_nonneg hs.1.le (one_div_pos.mpr hH).le)) (sub_nonneg.2 hm)
        have hfield : c*(s+1/H)*(n : ℝ)/4 = c*(n : ℝ)/(4*H)+(c/4)*(n : ℝ)*s := by ring
        calc
          -c*(s+1/H)*(m : ℝ) ≤ -(c*(s+1/H)*(n : ℝ)/4) := by nlinarith only [hp]
          _ = _ := by rw [hfield]; ring
      have hd := mul_le_mul_of_nonneg_left hExp
        (mul_nonneg (Real.rpow_nonneg hs.1.le (1/2 : ℝ)) (hA3 (s/2)))
      convert hd using 1 <;> simp only [kernel,earlyKernel,Real.rpow_eq_pow] <;> ring
    refine ⟨hLowM,hLowI,?_⟩
    calc
      _ ≤ CF * ∫ s : ℝ in Set.Ioo 0 (1/h0), kernel s := hFb
      _ ≤ CF * ∫ s : ℝ in Set.Ioo 0 (1/h0), eH*earlyKernel s :=
        mul_le_mul_of_nonneg_left (integral_mono_ae hFint (hKsmall.const_mul eH) hdom) hCFpos.le
      _ = CF*eH*(∫ s : ℝ in Set.Ioo 0 (1/h0), earlyKernel s) := by rw [integral_const_mul];ring
      _ ≤ CF*eH*(∫ s : ℝ in Set.Ioi 0, earlyKernel s) := by
        apply mul_le_mul_of_nonneg_left _ (by dsimp[eH];positivity)
        apply setIntegral_mono_set hKi
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
          exact hKn s hs
        · exact ae_of_all _ (fun s hs => hs.1)
  refine ⟨fun t ht => ⟨(hper t ht).1,(hper t ht).2.1⟩,?_⟩
  have hsum : (∑ t ∈ Finset.Icc ((n+1)/2) n, ∫ v, low t v ∂Pt t) ≤
      CF*CS*(beta/Real.sqrt (n : ℝ))*eH := by
    calc
      _ ≤ ∑ t ∈ Finset.Icc ((n+1)/2) n, CF*eH*(∫ s : ℝ in Set.Ioi 0, earlyKernel s) :=
        Finset.sum_le_sum (fun t ht => (hper t ht).2.2)
      _ = ((Finset.Icc ((n+1)/2) n).card : ℝ) *
          (CF*eH*(∫ s : ℝ in Set.Ioi 0, earlyKernel s)) := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ (n : ℝ) * (CF*eH*(∫ s : ℝ in Set.Ioi 0, earlyKernel s)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (show (Finset.Icc ((n+1)/2) n).card ≤ n by rw [Nat.card_Icc]; omega)
      _ = CF*eH*((n : ℝ)*(∫ s : ℝ in Set.Ioi 0, earlyKernel s)) := by ring
      _ ≤ CF*eH*(CS*R0) := mul_le_mul_of_nonneg_left hKb (by dsimp[eH];positivity)
      _ ≤ CF*eH*(CS*(beta/Real.sqrt (n : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRle hCSpos.le) (by dsimp[eH];positivity)
      _ = _ := by ring
  let v : ℝ := (n : ℝ)/H
  have hv : 0 < v := div_pos hnR hH
  have he : eH = Real.exp (-(c/4)*v) := by dsimp only [eH,v]; congr 1; ring
  have hExp1 : Real.exp (-(c/4)*v) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hExpV : v*Real.exp (-(c/4)*v) ≤ 1/(c/4) := by
    apply (le_div_iff₀ ha).2
    have haV : (c/4)*v ≤ Real.exp ((c/4)*v) := by
      linarith only [Real.add_one_le_exp ((c/4)*v)]
    have hh := mul_le_mul_of_nonneg_right haV (Real.exp_pos (-(c/4)*v)).le
    have heq : Real.exp ((c/4)*v) * Real.exp (-(c/4)*v) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
    rw [heq] at hh
    nlinarith only [hh]
  have hsV : Real.sqrt v ≤ 1+v := by
    have hs := Real.sq_sqrt hv.le
    have hnn := Real.sqrt_nonneg v
    nlinarith only [hs,hnn,sq_nonneg (Real.sqrt v-1)]
  have hDamp : Real.sqrt v*eH ≤ 1+4/c := by
    rw [he]
    have hh := mul_le_mul_of_nonneg_right hsV (Real.exp_pos (-(c/4)*v)).le
    have hi : 1/(c/4)=4/c := by field_simp
    rw [hi] at hExpV
    nlinarith only [hh,hExp1,hExpV]
  have hfactor : (beta/Real.sqrt (n : ℝ))*eH =
      (beta*Real.sqrt H/(n : ℝ))*(Real.sqrt v*eH) := by
    rw [show Real.sqrt v = Real.sqrt (n : ℝ)/Real.sqrt H from Real.sqrt_div hnR.le H]
    have hHS := Real.sqrt_pos.2 hH
    have hnSq := Real.sq_sqrt hnR.le
    field_simp
    rw [hnSq]
    ring
  calc
    _ ≤ CF*CS*(beta/Real.sqrt (n : ℝ))*eH := hsum
    _ = CF*CS*((beta*Real.sqrt H/(n : ℝ))*(Real.sqrt v*eH)) := by rw [← hfactor];ring
    _ ≤ CF*CS*((beta*Real.sqrt H/(n : ℝ))*(1+4/c)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDamp (by positivity)) (by positivity)
    _ = _ := by ring


theorem iid_actual_early_rare_and_omitted_retained_budget :
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
            let LD : (Shao.Path n × LabelPerm n) → Fin n → ℝ := fun p r =>
              L .interval p r - L .upper p r - L .lower p r
            let earlyRare : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
              ∑ r : Fin n,
                if r.val ≤ n / 2 ∧ r.val < nu p.1 p.2 ∧
                    (∀ k : ℕ, k ≤ r.val →
                      |Shao.prefixSum (Spitzer.reorder p.1 p.2) k| < actualWall p.1 x) ∧
                    (3 / 2 : ℝ) * x * Real.sqrt (remainingEnergy p.1 r.val p.2) <
                      |remainingSum p.1 r.val p.2|
                then |LD p r| else 0
            let earlyOmitted : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
              ∑ r : Fin n,
                if r.val ≤ n / 2 ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then
                  |L .interval p r| + |L .upper p r| + |L .lower p r| +
                    max (-sourceSeparatedOvershoot .interval (FY .interval)
                      p.1 x (nu p.1) r.val p.2) 0
                else 0
            Measurable earlyRare ∧ Integrable earlyRare (revealLaw P) ∧
              Measurable earlyOmitted ∧ Integrable earlyOmitted (revealLaw P) ∧
              (∫ p, earlyRare p ∂revealLaw P) ≤ C * delta * Shao.standardNormalTail x ∧
              (∫ p, earlyOmitted p ∂revealLaw P) ≤
                C * beta * Real.sqrt H / (n : ℝ) ∧
              (∫ p, earlyOmitted p ∂revealLaw P) ≤ C * delta * Shao.standardNormalTail x := by
  classical
  intro K
  let c : ℝ := (1-Real.exp (-2))/8
  have hc : 0 < c := div_pos (sub_pos.2 (Real.exp_lt_one_iff.2 (by norm_num))) (by norm_num)
  let CP : ℝ := Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant
  let C0 : ℝ := 2*(2*CP+40)+2*8000100
  let CQ : ℝ := Classical.choose (SourceResidualRareSuffix.iid_marked_and_unmarked_rare_real_suffix_budgets 3)
  let CF : ℝ := Classical.choose
    (Shao.C2.AuxiliaryRealMarkedFiniteCutoffBudget.auxiliary_actual_real_marked_finite_cutoff_budget
      (3 : ℝ) (3 : ℝ) (by norm_num) (by norm_num))
  let CS : ℝ := Classical.choose (raw_gaussian_scalar_budget_integrals (c/4) (by positivity))
  let Cearly : ℝ := (16/3 : ℝ)*C0*CQ
  let Clow : ℝ := C0*CF*CS*(1+4/c)
  let C : ℝ := 1+Cearly+Clow*(1+(8/3 : ℝ)*Real.sqrt K)
  have hQ := Classical.choose_spec (SourceResidualRareSuffix.iid_marked_and_unmarked_rare_real_suffix_budgets 3)
  have hF := Classical.choose_spec
    (Shao.C2.AuxiliaryRealMarkedFiniteCutoffBudget.auxiliary_actual_real_marked_finite_cutoff_budget
      (3 : ℝ) (3 : ℝ) (by norm_num) (by norm_num))
  have hS := Classical.choose_spec (raw_gaussian_scalar_budget_integrals (c/4) (by positivity))
  have hCP : 0 ≤ CP := Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant_nonneg
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  have hCQ : 0 < CQ := hQ.1
  have hCF : 0 < CF := hF.1
  have hCS : 0 < CS := hS.1
  have hClow : 0 < Clow := by dsimp [Clow]; positivity
  have hCearly : 0 < Cearly := by dsimp [Cearly]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ΩB mΩB PB hPB B hB Q rho hrho Bcap hBcap hBound hmean hsecond n hn x hx
    beta delta u hu h0 H m P nu tau F FY L LD earlyRare earlyOmitted
  letI : IsProbabilityMeasure rho := hrho
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw B PB hB
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  letI : IsProbabilityMeasure (revealLaw P) := by unfold revealLaw; infer_instance
  have hxpos : 0 < x := by linarith
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.2 hn
  have hnS : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have h2 : Integrable (fun z : ℝ => z^2) rho := by
    refine (integrable_const (Bcap^2)).mono' (by fun_prop) ?_
    filter_upwards [hBound] with z hz
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg z)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z) hz 2
  have h3 : Integrable (fun z : ℝ => |z|^3) rho := by
    refine (integrable_const (Bcap^3)).mono' (by fun_prop) ?_
    filter_upwards [hBound] with z hz
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ |z|^3)]
    exact pow_le_pow_left₀ (abs_nonneg z) hz 3
  have hRare := hQ.2 rho Bcap hBcap hBound hmean hsecond n hn x hx hu
  rcases hRare with ⟨hBeta,hh0,hHhalf,hm4,hh0m,hmn,hMom,hLong,hEarly,hLate,hFutureI,hFutureB⟩
  clear hLong hLate hFutureI hFutureB
  have hm4 : 4 ≤ m := hm4
  have hmn : (m : ℝ) ≤ (n : ℝ)/4 := hmn
  have hBetaPos : 0 < beta := by linarith only [hBeta]
  have hdelta : 0 < delta := div_pos hBetaPos hnS
  have hH : 0 < H := by linarith only [hh0,hHhalf]
  have hn16 : 16 ≤ n := by
    have hmcast : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4
    have hncast : (16 : ℝ) ≤ n := by linarith only [hmcast,hmn]
    exact_mod_cast hncast
  let Pt : (t : ℕ) → Measure (Shao.Path t) := fun t => Measure.pi (fun _ : Fin t => rho)
  let firstCube : (t : ℕ) → Shao.Path t → ℝ := fun t v => if ht : 0<t then |v ⟨0,ht⟩|^3 else 0
  let rareW : (t : ℕ) → Shao.Path t → ℝ := fun t v =>
    if 0<Shao.energy v ∧ h0≤Shao.energy v ∧ (3/2 : ℝ)*x*Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v t| then
      firstCube t v/(Real.sqrt (Shao.energy v))^3*(1+|Shao.prefixSum v t|/Real.sqrt (Shao.energy v))^3 else 0
  let lowW : (t : ℕ) → Shao.Path t → ℝ := fun t v =>
    if 0<Shao.energy v ∧ h0≤Shao.energy v ∧ Shao.energy v<H then
      firstCube t v/(Real.sqrt (Shao.energy v))^3*(1+|Shao.prefixSum v t|/Real.sqrt (Shao.energy v))^3 else 0
  have hRareEq (t : ℕ) : rareW t =
      (fun v : Shao.Path t =>
        if 0<Shao.energy v ∧ h0≤Shao.energy v ∧ (3*x/2)*Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v t| then
          firstCube t v/(Real.sqrt (Shao.energy v))^3 *
            (if 0<Shao.energy v then 1+|Shao.prefixSum v t|/Real.sqrt (Shao.energy v) else 1)^3
        else 0) := by
    funext v
    have hScale : (3/2 : ℝ)*x=3*x/2 := by ring
    dsimp only [rareW]
    rw [hScale]
    by_cases hv : 0 < Shao.energy v ∧ h0 ≤ Shao.energy v ∧ (3*x/2)*Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v t|
    · rw [if_pos hv,if_pos hv,if_pos hv.1]
    · rw [if_neg hv,if_neg hv]
  have hRareI (t : ℕ) : Integrable (rareW t) (Pt t) := by
    rw [hRareEq t]
    exact (hMom t 3 (Or.inr rfl)).1
  have hEarlyR : (∑ t ∈ Finset.Icc ((n+1)/2) n, ∫ v, rareW t v ∂Pt t) ≤ CQ*delta*
      (Real.sqrt (Shao.standardNormalTail (3*x/2))+Real.exp (-x^2)) := by
    simp_rw [hRareEq]
    exact hEarly
  have hLow := erp_iid_early_low_energy_grid hc rho h2 h3 hmean hsecond n (by omega) H (by linarith)
  change (∀ t ∈ Finset.Icc ((n+1)/2) n, Measurable (lowW t) ∧ Integrable (lowW t) (Pt t)) ∧
    (∑ t ∈ Finset.Icc ((n+1)/2) n, ∫ v, lowW t v ∂Pt t) ≤
      (CF*CS*(1+4/c))*beta*Real.sqrt H/(n : ℝ) at hLow
  have hRareM (t : ℕ) : Measurable (rareW t) := by
    have hCm : Measurable (firstCube t) := by
      dsimp only [firstCube]
      split_ifs
      · fun_prop
      · exact measurable_const
    dsimp only [rareW]
    apply Measurable.ite
      ((measurableSet_lt measurable_const Shao.measurable_energy).inter
        ((measurableSet_le measurable_const Shao.measurable_energy).inter
        (measurableSet_le (measurable_const.mul Shao.measurable_energy.sqrt)
          (continuous_abs.measurable.comp (Shao.measurable_prefixSum t)))))
    · exact (hCm.div (Shao.measurable_energy.sqrt.pow_const 3)).mul
        ((measurable_const.add ((continuous_abs.measurable.comp (Shao.measurable_prefixSum t)).div
          Shao.measurable_energy.sqrt)).pow_const 3)
    · exact measurable_const
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
    (hFm J) (hData J).1 4 (hData J).2 P x hxpos nu hnu
  have hLm (J : MonitoredDomain) (r : Fin n) : Measurable (fun p => L J p r) := by
    apply measurable_from_prod_countable_left
    intro sigma
    exact ((hParts J).1 sigma r.val).1
  have hLi (J : MonitoredDomain) (r : Fin n) : Integrable (fun p => L J p r) (revealLaw P) :=
    ((hParts J).2.1 r.val).1
  have hLDm (r : Fin n) : Measurable (fun p => LD p r) :=
    ((hLm .interval r).sub (hLm .upper r)).sub (hLm .lower r)
  have hLDi (r : Fin n) : Integrable (fun p => LD p r) (revealLaw P) :=
    ((hLi .interval r).sub (hLi .upper r)).sub (hLi .lower r)
  let O : (Shao.Path n × LabelPerm n) → Fin n → ℝ := fun p r =>
    sourceSeparatedOvershoot .interval (FY .interval) p.1 x (nu p.1) r.val p.2
  have hOm (r : Fin n) : Measurable (fun p => O p r) := by
    apply measurable_from_prod_countable_left
    intro sigma
    exact ((hParts .interval).1 sigma r.val).2
  have hOi (r : Fin n) : Integrable (fun p => O p r) (revealLaw P) :=
    ((hParts .interval).2.1 r.val).2
  have hGuardR (r : Fin n) : MeasurableSet {p : Shao.Path n × LabelPerm n |
      r.val ≤ n/2 ∧ r.val < nu p.1 p.2 ∧
      (∀ k : ℕ, k ≤ r.val → |Shao.prefixSum (Spitzer.reorder p.1 p.2) k| < actualWall p.1 x) ∧
      (3/2 : ℝ)*x*Real.sqrt (remainingEnergy p.1 r.val p.2) < |remainingSum p.1 r.val p.2|} := by
    have hSection (sigma : LabelPerm n) : MeasurableSet {a : Shao.Path n |
        r.val ≤ n/2 ∧ r.val < nu a sigma ∧
        (∀ k : ℕ, k ≤ r.val → |Shao.prefixSum (Spitzer.reorder a sigma) k| < actualWall a x) ∧
        (3/2 : ℝ)*x*Real.sqrt (remainingEnergy a r.val sigma) < |remainingSum a r.val sigma|} := by
      by_cases he : r.val ≤ n/2
      · simp only [he,true_and]
        have hRm : Measurable (fun a : Shao.Path n => Spitzer.reorder a sigma) :=
          Measurable.of_eval (fun i => measurable_pi_apply (sigma i))
        have hW : Measurable (fun a : Shao.Path n => actualWall a x) :=
          measurable_const.mul Shao.measurable_energy.sqrt
        have hS (s : Finset ℕ) : MeasurableSet {a : Shao.Path n |
            ∀ k ∈ s, |Shao.prefixSum (Spitzer.reorder a sigma) k| < actualWall a x} := by
          induction s using Finset.induction_on with
          | empty => simp
          | @insert k s hk ih =>
            simpa only [Finset.forall_mem_insert,Set.setOf_and,Function.comp_def] using
              (measurableSet_lt (continuous_abs.measurable.comp ((Shao.measurable_prefixSum k).comp hRm)) hW).inter ih
        have hPref : MeasurableSet {a : Shao.Path n | ∀ k : ℕ, k ≤ r.val →
            |Shao.prefixSum (Spitzer.reorder a sigma) k| < actualWall a x} := by
          simpa only [Finset.mem_range,Nat.lt_succ_iff] using hS (Finset.range (r.val+1))
        have hD : Measurable (fun a : Shao.Path n => remainingSum a r.val sigma) :=
          (Shao.measurable_prefixSum n).sub ((Shao.measurable_prefixSum r.val).comp hRm)
        have hT : Measurable (fun a : Shao.Path n => remainingEnergy a r.val sigma) :=
          Shao.measurable_energy.sub ((Shao.measurable_prefixSquares r.val).comp hRm)
        exact (measurableSet_lt measurable_const (hnu sigma)).inter
          (hPref.inter (measurableSet_lt (measurable_const.mul hT.sqrt) (continuous_abs.measurable.comp hD)))
      · simp only [he,false_and,Set.setOf_false,MeasurableSet.empty]
    have hm : Measurable (fun p : Shao.Path n × LabelPerm n =>
        if r.val ≤ n/2 ∧ r.val < nu p.1 p.2 ∧
          (∀ k : ℕ, k ≤ r.val → |Shao.prefixSum (Spitzer.reorder p.1 p.2) k| < actualWall p.1 x) ∧
          (3/2 : ℝ)*x*Real.sqrt (remainingEnergy p.1 r.val p.2) < |remainingSum p.1 r.val p.2|
        then (1 : ℝ) else 0) := by
      apply measurable_from_prod_countable_left
      intro sigma
      exact Measurable.ite (hSection sigma) measurable_const measurable_const
    simpa only [Set.preimage,Set.mem_singleton_iff,ite_eq_left_iff,zero_ne_one,imp_false,not_not]
      using hm (measurableSet_singleton (1 : ℝ))
  have hGuardO (r : Fin n) : MeasurableSet {p : Shao.Path n × LabelPerm n |
      r.val ≤ n/2 ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2} := by
    have hm : Measurable (fun p : Shao.Path n × LabelPerm n =>
        if r.val ≤ n/2 ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then (1 : ℝ) else 0) := by
      apply measurable_from_prod_countable_left
      intro sigma
      by_cases he : r.val ≤ n/2
      · simp only [he,true_and]
        exact Measurable.ite ((measurableSet_le (htau sigma) measurable_const).inter
          (measurableSet_lt measurable_const (hnu sigma))) measurable_const measurable_const
      · simp only [he,false_and,ite_false]
        exact measurable_const
    simpa only [Set.preimage,Set.mem_singleton_iff,ite_eq_left_iff,zero_ne_one,imp_false,not_not]
      using hm (measurableSet_singleton (1 : ℝ))
  have hRareBillM : Measurable earlyRare := by
    apply Finset.measurable_sum
    intro r hr
    exact Measurable.ite (hGuardR r) (continuous_abs.measurable.comp (hLDm r)) measurable_const
  have hRareBillI : Integrable earlyRare (revealLaw P) := by
    apply integrable_finsetSum
    intro r hr
    exact (hLDi r).abs.mono'
      ((Measurable.ite (hGuardR r) (continuous_abs.measurable.comp (hLDm r)) measurable_const).aestronglyMeasurable)
      (ae_of_all _ fun p => by split_ifs <;> simp [Real.norm_eq_abs])
  have hCombinedM (r : Fin n) : Measurable (fun p => |L .interval p r|+|L .upper p r|+|L .lower p r|+max (-O p r) 0) :=
    (((continuous_abs.measurable.comp (hLm .interval r)).add (continuous_abs.measurable.comp (hLm .upper r))).add
      (continuous_abs.measurable.comp (hLm .lower r))).add ((hOm r).neg.max measurable_const)
  have hNegI (r : Fin n) : Integrable (fun p => max (-O p r) 0) (revealLaw P) := by
    refine (hOi r).abs.mono' (((hOm r).neg.max measurable_const).aestronglyMeasurable) ?_
    exact ae_of_all _ (fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
      exact max_le (neg_le_abs (O p r)) (abs_nonneg _))
  have hCombinedI (r : Fin n) : Integrable (fun p => |L .interval p r|+|L .upper p r|+|L .lower p r|+max (-O p r) 0) (revealLaw P) :=
    (((hLi .interval r).abs.add (hLi .upper r).abs).add (hLi .lower r).abs).add (hNegI r)
  have hOmittedM : Measurable earlyOmitted := by
    apply Finset.measurable_sum
    intro r hr
    exact Measurable.ite (hGuardO r) (hCombinedM r) measurable_const
  have hOmittedI : Integrable earlyOmitted (revealLaw P) := by
    apply integrable_finsetSum
    intro r hr
    exact (hCombinedI r).mono'
      ((Measurable.ite (hGuardO r) (hCombinedM r) measurable_const).aestronglyMeasurable)
      (ae_of_all _ fun p => by
        split_ifs
        · rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
        · simp only [norm_zero]; positivity)
  have hPt (t : ℕ) : IsProbabilityMeasure (Pt t) := by dsimp [Pt]; infer_instance
  let split : (r : Fin n) → Shao.Path n → Shao.Path r.val × Shao.Path (n-r.val) := fun r a =>
    (Spitzer.head a r.val r.is_lt.le,Spitzer.tail a r.val r.is_lt.le)
  have hSplit (r : Fin n) : MeasurePreserving (split r) P ((Pt r.val).prod (Pt (n-r.val))) := by
    let e : Fin r.val ⊕ Fin (n-r.val) ≃ Fin n :=
      finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le r.is_lt.le))
    have h1 := (measurePreserving_piCongrLeft (fun _ : Fin n => rho) e).symm
    have h2 := measurePreserving_sumPiEquivProdPi (fun _ : Fin r.val ⊕ Fin (n-r.val) => rho)
    convert h2.comp h1 using 1
    ext a i <;> change a _ = a _ <;> congr 1
  have hTail (r : Fin n) : MeasurePreserving (fun a : Shao.Path n => (split r a).2) P (Pt (n-r.val)) := by
    letI := hPt r.val
    exact (measurePreserving_snd (μ := Pt r.val) (ν := Pt (n-r.val))).comp (hSplit r)
  have hTailId (r : Fin n) : IdentDistrib (fun a : Shao.Path n => (split r a).2)
      (id : Shao.Path (n-r.val) → Shao.Path (n-r.val)) P (Pt (n-r.val)) :=
    ⟨(hTail r).measurable.aemeasurable,measurable_id.aemeasurable,by rw [Measure.map_id];exact (hTail r).map_eq⟩
  have hRm : Measurable (fun p : Shao.Path n × LabelPerm n => Spitzer.reorder p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro sigma
    exact Measurable.of_eval (fun i => measurable_pi_apply (sigma i))
  let X : Fin n → Shao.Path n → ℝ := fun i a => a i
  have hX (i : Fin n) : Measurable (X i) := measurable_pi_apply i
  have hLaw (i : Fin n) : IdentDistrib (X i) (id : ℝ → ℝ) P rho := by
    refine ⟨(hX i).aemeasurable,measurable_id.aemeasurable,?_⟩
    simpa only [Measure.map_id] using (measurePreserving_eval (μ := fun _ : Fin n => rho) i).map_eq
  have hIndep : iIndepFun X P := iIndepFun_pi (X := fun _ : Fin n => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)
  have hMap : Measure.map (fun p : Shao.Path n × LabelPerm n => Spitzer.reorder p.1 p.2) (revealLaw P) = P :=
    iid_randomPermutation_map_eq_pi P rho X hX hIndep hLaw
  have hPath : IdentDistrib (fun p : Shao.Path n × LabelPerm n => Spitzer.reorder p.1 p.2)
      (id : Shao.Path n → Shao.Path n) (revealLaw P) P :=
    ⟨hRm.aemeasurable,measurable_id.aemeasurable,by simpa only [Measure.map_id] using hMap⟩
  have hTailSeed (r : Fin n) : IdentDistrib
      (fun p : Shao.Path n × LabelPerm n => (split r (Spitzer.reorder p.1 p.2)).2)
      (id : Shao.Path (n-r.val) → Shao.Path (n-r.val)) (revealLaw P) (Pt (n-r.val)) :=
    (hPath.comp (hTail r).measurable).trans (hTailId r)
  have hState (r : Fin n) (p : Shao.Path n × LabelPerm n) :
      Shao.energy (split r (Spitzer.reorder p.1 p.2)).2 = remainingEnergy p.1 r.val p.2 ∧
      Shao.prefixSum (split r (Spitzer.reorder p.1 p.2)).2 (n-r.val) = remainingSum p.1 r.val p.2 ∧
      firstCube (n-r.val) (split r (Spitzer.reorder p.1 p.2)).2 = |p.1 (p.2 r)|^3 := by
    have hh := SourceIIDGaussianProfileBudget.gaussian_weight_source_state (Spitzer.reorder p.1 p.2) r h0 x ∅ false
    have hEnergy : Shao.energy (Spitzer.reorder p.1 p.2) = Shao.energy p.1 := by
      simpa only [Shao.energy,Spitzer.reorder] using Equiv.sum_comp p.2 (fun i => (p.1 i)^2)
    have hSum : Shao.prefixSum (Spitzer.reorder p.1 p.2) n = Shao.prefixSum p.1 n := by
      simpa only [Shao.prefixSum_length,Spitzer.reorder] using Equiv.sum_comp p.2 p.1
    refine ⟨?_,?_,?_⟩
    · simpa only [remainingEnergy,hEnergy] using hh.1
    · simpa only [remainingSum,hSum] using hh.2.1
    · have ht : 0 < n-r.val := Nat.sub_pos_of_lt r.is_lt
      simpa only [firstCube,SourceIIDGaussianProfileBudget.firstValue,dif_pos ht,Spitzer.reorder]
        using congrArg (fun b : ℝ => |b|^3) hh.2.2.2.1
  let er : Finset (Fin n) := Finset.univ.filter (fun r => r.val ≤ n/2)
  have hReindex (f : ℕ → ℝ) : (∑ r ∈ er, f (n-r.val)) = ∑ t ∈ Finset.Icc ((n+1)/2) n, f t := by
    apply Finset.sum_bij (fun r _ => n-r.val)
    · intro r hr
      have hh := (Finset.mem_filter.mp hr).2
      simp only [Finset.mem_Icc];omega
    · intro r hr s hs he
      apply Fin.ext
      omega
    · intro t ht
      have hh := Finset.mem_Icc.mp ht
      refine ⟨⟨n-t,by omega⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by change n-t≤n/2;omega⟩,?_⟩
      dsimp;omega
    · intro r hr;rfl
  have hEarlyMem (r : Fin n) (hr : r∈er) : n-r.val ∈ Finset.Icc ((n+1)/2) n := by
    have hh := (Finset.mem_filter.mp hr).2
    simp only [Finset.mem_Icc];omega
  let cube : (Shao.Path n × LabelPerm n) → Fin n → ℝ := fun p r =>
    |p.1 (p.2 r)|^3/(Real.sqrt (remainingEnergy p.1 r.val p.2))^3 *
      (1+|remainingSum p.1 r.val p.2|/Real.sqrt (remainingEnergy p.1 r.val p.2))^3
  have hCoarse (p : Shao.Path n × LabelPerm n) (r : Fin n) (hr : r.val < nu p.1 p.2) :
      |L .interval p r|+|L .upper p r|+|L .lower p r|+max (-O p r) 0 ≤ C0*cube p r := by
    have hh := erp_actual_cubic_domination PB B hB p.1 h0 x hh0 hxpos (nu p.1) p.2 le_rfl r hr
    dsimp only at hh
    convert hh using 1 <;> dsimp only [cube] <;> rw [div_pow] <;> ring
  have hRareNN (t : ℕ) (v : Shao.Path t) : 0 ≤ rareW t v := by
    dsimp [rareW,firstCube];split_ifs <;> positivity
  have hLowNN (t : ℕ) (v : Shao.Path t) : 0 ≤ lowW t v := by
    dsimp [lowW,firstCube];split_ifs <;> positivity
  let SR : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
    ∑ r ∈ er, rareW (n-r.val) (split r (Spitzer.reorder p.1 p.2)).2
  let SL : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
    ∑ r ∈ er, lowW (n-r.val) (split r (Spitzer.reorder p.1 p.2)).2
  have hSRI : Integrable SR (revealLaw P) := by
    dsimp only [SR]
    apply integrable_finsetSum
    intro r hr
    exact ((hTailSeed r).comp (hRareM (n-r.val))).integrable_iff.mpr (hRareI (n-r.val))
  have hSLI : Integrable SL (revealLaw P) := by
    dsimp only [SL]
    apply integrable_finsetSum
    intro r hr
    exact ((hTailSeed r).comp (hLow.1 _ (hEarlyMem r hr)).1).integrable_iff.mpr
      (hLow.1 _ (hEarlyMem r hr)).2
  have hSRB : (∫ p, SR p ∂revealLaw P) ≤ CQ*delta*
      (Real.sqrt (Shao.standardNormalTail (3*x/2))+Real.exp (-x^2)) := by
    dsimp only [SR]
    have hi (r : Fin n) (hr : r∈er) : Integrable
        (fun p : Shao.Path n × LabelPerm n => rareW (n-r.val) (split r (Spitzer.reorder p.1 p.2)).2) (revealLaw P) := by
      simpa only [Function.comp_def] using
        ((hTailSeed r).comp (hRareM (n-r.val))).integrable_iff.mpr (hRareI (n-r.val))
    rw [integral_finsetSum er hi]
    have he (r : Fin n) : (∫ p, rareW (n-r.val) (split r (Spitzer.reorder p.1 p.2)).2 ∂revealLaw P) =
        ∫ v, rareW (n-r.val) v ∂Pt (n-r.val) := ((hTailSeed r).comp (hRareM (n-r.val))).integral_eq
    simp_rw [he]
    rw [hReindex (fun t : ℕ => ∫ v, rareW t v ∂Pt t)]
    exact hEarlyR
  have hSLB : (∫ p, SL p ∂revealLaw P) ≤ (CF*CS*(1+4/c))*beta*Real.sqrt H/(n : ℝ) := by
    dsimp only [SL]
    have hi (r : Fin n) (hr : r∈er) : Integrable
        (fun p : Shao.Path n × LabelPerm n => lowW (n-r.val) (split r (Spitzer.reorder p.1 p.2)).2) (revealLaw P) := by
      simpa only [Function.comp_def] using
        ((hTailSeed r).comp (hLow.1 _ (hEarlyMem r hr)).1).integrable_iff.mpr (hLow.1 _ (hEarlyMem r hr)).2
    rw [integral_finsetSum er hi]
    have he (r : Fin n) (hr : r∈er) :
        (∫ p, lowW (n-r.val) (split r (Spitzer.reorder p.1 p.2)).2 ∂revealLaw P) =
        ∫ v, lowW (n-r.val) v ∂Pt (n-r.val) :=
      ((hTailSeed r).comp (hLow.1 _ (hEarlyMem r hr)).1).integral_eq
    have hsumEq := Finset.sum_congr rfl (fun r hr => he r hr)
    rw [hsumEq,hReindex (fun t : ℕ => ∫ v, lowW t v ∂Pt t)]
    exact hLow.2
  have hPointR (p : Shao.Path n × LabelPerm n) : earlyRare p ≤ C0*SR p := by
    dsimp only [earlyRare,SR,er]
    rw [Finset.sum_filter,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    by_cases hg : r.val ≤ n/2 ∧ r.val < nu p.1 p.2 ∧
        (∀ k : ℕ, k ≤ r.val → |Shao.prefixSum (Spitzer.reorder p.1 p.2) k| < actualWall p.1 x) ∧
        (3/2 : ℝ)*x*Real.sqrt (remainingEnergy p.1 r.val p.2) < |remainingSum p.1 r.val p.2|
    · rw [if_pos hg,if_pos hg.1]
      have hCut : h0 ≤ remainingEnergy p.1 r.val p.2 :=
        ((energy_cutoff_data p.1 h0 hh0).2.2 p.2 r.val hg.2.1).2
      have hT : 0 < remainingEnergy p.1 r.val p.2 := hh0.trans_le hCut
      have he : rareW (n-r.val) (split r (Spitzer.reorder p.1 p.2)).2 = cube p r := by
        dsimp only [rareW]
        rw [(hState r p).1,(hState r p).2.1,if_pos ⟨hT,hCut,hg.2.2.2.le⟩,(hState r p).2.2]
      rw [he]
      have htri : |LD p r| ≤ |L .interval p r|+|L .upper p r|+|L .lower p r| := by
        have ht (a b : ℝ) : |a-b| ≤ |a|+|b| := by
          simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le a 0 b
        have h1 := ht (L .interval p r) (L .upper p r)
        have h2 := ht (L .interval p r-L .upper p r) (L .lower p r)
        exact h2.trans (by linarith only [h1])
      have hc := hCoarse p r hg.2.1
      exact htri.trans ((le_add_of_nonneg_right (le_max_right _ _)).trans hc)
    · rw [if_neg hg]
      split_ifs
      · exact mul_nonneg hC0.le (hRareNN _ _)
      · simp only [mul_zero,le_refl]
  have hPointO (p : Shao.Path n × LabelPerm n) : earlyOmitted p ≤ C0*SL p := by
    dsimp only [earlyOmitted,SL,er]
    rw [Finset.sum_filter,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    by_cases hg : r.val ≤ n/2 ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2
    · rw [if_pos hg,if_pos hg.1]
      have hc := (Shao.C2.AdaptiveRevealCutoff.omitted_adaptive_cutoff_iff
        p.1 h0 H hh0 hH m r.val r.is_lt.le p.2).1 hg.2
      have htm : m < n-r.val := by
        have h4mR : (4 : ℝ)*(m : ℝ) ≤ n := by linarith only [hmn]
        have h4mN : 4*m ≤ n := by exact_mod_cast h4mR
        omega
      have hTH : remainingEnergy p.1 r.val p.2 < H := hc.2.resolve_right (by omega)
      have hT : 0 < remainingEnergy p.1 r.val p.2 := hh0.trans_le hc.1
      have he : lowW (n-r.val) (split r (Spitzer.reorder p.1 p.2)).2 = cube p r := by
        dsimp only [lowW]
        rw [(hState r p).1,(hState r p).2.1,if_pos ⟨hT,hc.1,hTH⟩,(hState r p).2.2]
      rw [he]
      exact hCoarse p r hg.2.2
    · rw [if_neg hg]
      split_ifs
      · exact mul_nonneg hC0.le (hLowNN _ _)
      · simp only [mul_zero,le_refl]
  have hRareStrong : (∫ p, earlyRare p ∂revealLaw P) ≤ C0*CQ*delta*
      (Real.sqrt (Shao.standardNormalTail (3*x/2))+Real.exp (-x^2)) := by
    calc
      _ ≤ ∫ p, C0*SR p ∂revealLaw P := integral_mono hRareBillI (hSRI.const_mul _) hPointR
      _ = C0*(∫ p, SR p ∂revealLaw P) := integral_const_mul _ _
      _ ≤ C0*(CQ*delta*(Real.sqrt (Shao.standardNormalTail (3*x/2))+Real.exp (-x^2))) :=
        mul_le_mul_of_nonneg_left hSRB hC0.le
      _ = _ := by ring
  have hOmittedStrong : (∫ p, earlyOmitted p ∂revealLaw P) ≤ Clow*beta*Real.sqrt H/(n : ℝ) := by
    calc
      _ ≤ ∫ p, C0*SL p ∂revealLaw P := integral_mono hOmittedI (hSLI.const_mul _) hPointO
      _ = C0*(∫ p, SL p ∂revealLaw P) := integral_const_mul _ _
      _ ≤ C0*((CF*CS*(1+4/c))*beta*Real.sqrt H/(n : ℝ)) :=
        mul_le_mul_of_nonneg_left hSLB hC0.le
      _ = _ := by dsimp only [Clow];ring
  let Ax : ℝ := Real.sqrt (Shao.standardNormalTail (3*x/2))+Real.exp (-x^2)
  have hAx : Ax ≤ (16/3 : ℝ)*Shao.standardNormalTail x := by
    have hden : 1 ≤ Real.sqrt (2*Real.pi) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [Real.pi_gt_three]
    have hDens (z : ℝ) : Shao.standardNormalDensity z ≤ Real.exp (-z^2/2) := by
      have he : Shao.standardNormalDensity z = (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-z^2/2) := by
        simp [Shao.standardNormalDensity,ProbabilityTheory.gaussianPDFReal]
      rw [he]
      exact mul_le_of_le_one_left (Real.exp_nonneg _) ((inv_le_one₀ (by positivity)).2 hden)
    have hPsi : Shao.standardNormalTail (3*x/2) ≤ Real.exp (-9*x^2/8) := by
      have hm := (Shao.standardNormal_mills_bounds (3*x/2) (by positivity)).2.1
      calc
        _ ≤ (4/3 : ℝ)*Shao.standardNormalDensity (3*x/2)/(1+3*x/2) := hm
        _ ≤ (4/3 : ℝ)*Real.exp (-(3*x/2)^2/2)/(1+3*x/2) := by gcongr;exact hDens _
        _ ≤ Real.exp (-(3*x/2)^2/2) := by
          apply (div_le_iff₀ (by positivity : 0<1+3*x/2)).2
          nlinarith only [Real.exp_pos (-(3*x/2)^2/2),hx]
        _ = _ := by congr 1;ring
    have hs : Real.sqrt (Shao.standardNormalTail (3*x/2)) ≤ Real.exp (-9*x^2/16) := by
      apply Real.sqrt_le_iff.2
      refine ⟨Real.exp_nonneg _,?_⟩
      have he : (Real.exp (-9*x^2/16))^2 = Real.exp (-9*x^2/8) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      rw [he]
      exact hPsi
    have hA := Shao.C2.AuxiliaryLowEnergyGaussian.auxiliary_exponential_le_gaussian_tail
      x (9*x^2/16) hxpos.le (by nlinarith)
    have hB := Shao.C2.AuxiliaryLowEnergyGaussian.auxiliary_exponential_le_gaussian_tail
      x (x^2) hxpos.le (by nlinarith)
    have hA' : Real.exp (-9*x^2/16) ≤ (8/3 : ℝ)*Shao.standardNormalTail x := by
      convert hA using 1 <;> congr 1 <;> ring
    dsimp only [Ax]
    linarith only [hs,hA',hB]
  have hTailNN : 0 ≤ Shao.standardNormalTail x := ((Shao.standardNormalTail_basic).2.2.1 x).1.le
  have hKpos : 0<K := by norm_num [K]
  have hHsqrt : Real.sqrt H = Real.sqrt K*beta*(1+x)^3 := by
    have hbase : H = (Real.sqrt K*beta*(1+x)^3)^2 := by
      dsimp only [H]
      simp only [mul_pow,Real.sq_sqrt hKpos.le]
      ring
    rw [hbase,Real.sqrt_sq (by positivity)]
  have hDeltaU : delta*u = beta^2*(1+x)^3/(n : ℝ) := by
    dsimp only [delta,u]
    calc
      _ = beta^2*(1+x)^3/(Real.sqrt (n : ℝ))^2 := by
        field_simp [hnS.ne'] <;> ring
      _ = _ := by rw [Real.sq_sqrt hnR.le]
  have hScale : beta*Real.sqrt H/(n : ℝ) = Real.sqrt K*delta*u := by
    calc
      _ = Real.sqrt K*(beta^2*(1+x)^3/(n : ℝ)) := by rw [hHsqrt];ring
      _ = Real.sqrt K*(delta*u) := by rw [hDeltaU]
      _ = _ := by ring
  have hExpTail : Real.exp (-3*x^2) ≤ (8/3 : ℝ)*Shao.standardNormalTail x := by
    have hh := Shao.C2.AuxiliaryLowEnergyGaussian.auxiliary_exponential_le_gaussian_tail
      x (3*x^2) hxpos.le (by nlinarith)
    convert hh using 1 <;> congr 1 <;> ring
  have hScaleTail : beta*Real.sqrt H/(n : ℝ) ≤
      (8/3 : ℝ)*Real.sqrt K*delta*Shao.standardNormalTail x := by
    rw [hScale]
    calc
      _ ≤ Real.sqrt K*delta*Real.exp (-3*x^2) := mul_le_mul_of_nonneg_left hu (by positivity)
      _ ≤ Real.sqrt K*delta*((8/3 : ℝ)*Shao.standardNormalTail x) :=
        mul_le_mul_of_nonneg_left hExpTail (by positivity)
      _ = _ := by ring
  have hEC : Cearly ≤ C := by
    have hh : 0 ≤ Clow*(1+(8/3 : ℝ)*Real.sqrt K) := by positivity
    dsimp only [C]
    linarith only [hh]
  have hLC : Clow ≤ C := by
    dsimp only [C]
    have hh : 0 ≤ Clow*((8/3 : ℝ)*Real.sqrt K) := by positivity
    nlinarith only [hh,hCearly.le]
  have hLTC : (8/3 : ℝ)*Real.sqrt K*Clow ≤ C := by
    dsimp only [C]
    nlinarith only [hClow.le,hCearly.le]
  refine ⟨hRareBillM,hRareBillI,hOmittedM,hOmittedI,?_,?_,?_⟩
  · calc
      _ ≤ C0*CQ*delta*Ax := hRareStrong
      _ ≤ C0*CQ*delta*((16/3 : ℝ)*Shao.standardNormalTail x) :=
        mul_le_mul_of_nonneg_left hAx (by positivity)
      _ = Cearly*delta*Shao.standardNormalTail x := by dsimp only [Cearly];ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hEC hdelta.le) hTailNN
  · exact hOmittedStrong.trans (by gcongr)
  · calc
      _ ≤ Clow*(beta*Real.sqrt H/(n : ℝ)) := by convert hOmittedStrong using 1 <;> ring
      _ ≤ Clow*((8/3 : ℝ)*Real.sqrt K*delta*Shao.standardNormalTail x) :=
        mul_le_mul_of_nonneg_left hScaleTail hClow.le
      _ = ((8/3 : ℝ)*Real.sqrt K*Clow)*delta*Shao.standardNormalTail x := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLTC hdelta.le) hTailNN

end Shao.Probability.SourceEarlyRetainedProbability
