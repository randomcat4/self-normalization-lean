import Shao.C2.ActualBadIntervalNegativeBudget
import Shao.C2.BridgeIntervalImageResolved
import Shao.Probability.SourceEarlyRetainedProbability
import Shao.Probability.SourceLateOmittedSuffixBudget
import Shao.Probability.SourceTrueWallProfile

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
noncomputable section
namespace Shao.C2.ActualRetainedResidualBudgets
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.ActualSignedDoubleTelescope
open Shao.Probability.SourcePermutationReveal
open Shao.Probability.SourceSeparatedOvershoot

local instance labelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

def actualRetainedAbsoluteRank {n : ℕ} (Q : Measure BridgeNoise)
    (a : Shao.Path n) (x : ℝ) (nu : LabelPerm n → ℕ)
    (r : Fin n) (sigma : LabelPerm n) : ℝ :=
  |sourceRetainedRemainder .interval (eventCompletionKernel .interval Q)
      (actualDerivativeFamily Q .interval) a x nu r.val sigma| +
  |sourceRetainedRemainder .upper (eventCompletionKernel .upper Q)
      (actualDerivativeFamily Q .upper) a x nu r.val sigma| +
  |sourceRetainedRemainder .lower (eventCompletionKernel .lower Q)
      (actualDerivativeFamily Q .lower) a x nu r.val sigma| +
  max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
      a x nu r.val sigma) 0

def actualOmittedRetainedBill {n : ℕ} (Q : Measure BridgeNoise) (x : ℝ)
    (nu tau : Shao.Path n → LabelPerm n → ℕ)
    (p : Shao.Path n × LabelPerm n) : ℝ :=
  ∑ r : Fin n, if tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then
    actualRetainedAbsoluteRank Q p.1 x (nu p.1) r p.2 else 0

def actualBadRetainedBill {n : ℕ} (Q : Measure BridgeNoise) (x : ℝ)
    (nu : Shao.Path n → LabelPerm n → ℕ)
    (p : Shao.Path n × LabelPerm n) : ℝ :=
  ∑ r : Fin n, if (3 * x / 2) * Real.sqrt (remainingEnergy p.1 r.val p.2) ≤
      |remainingSum p.1 r.val p.2| then
    actualRetainedAbsoluteRank Q p.1 x (nu p.1) r p.2 else 0

private theorem arr_interval_rank_gaussian_domination
    {ΩB : Type*} [MeasurableSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (Bm : ℝ≥0 → ΩB → ℝ) (hBm : IsBrownianReal Bm PB)
    {n : ℕ} (a : Shao.Path n) (H x : ℝ) (hH : 0 < H) (hx : 0 < x)
    (nu : LabelPerm n → ℕ) (sigma : LabelPerm n)
    (hcap : nu sigma ≤ energyCutoff a H sigma) (r : Fin n) :
    let Q : Measure BridgeNoise := bridgeLaw Bm PB
    |sourceRetainedRemainder .interval (eventCompletionKernel .interval Q)
        (actualDerivativeFamily Q .interval) a x nu r.val sigma| +
      max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
        a x nu r.val sigma) 0 ≤
      (2 * Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant + 40) *
        Shao.Probability.SourceIIDGaussianProfileBudget.rankGaussianWeight H x {1, -1} false
          (Shao.Probability.Spitzer.reorder a sigma) r := by
  classical
  dsimp only
  let Q : Measure BridgeNoise := bridgeLaw Bm PB
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw Bm PB hBm
  let K : ℝ := 2 * Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant + 40
  let L : ℝ := sourceRetainedRemainder .interval (eventCompletionKernel .interval Q)
    (Shao.Probability.SourceActualIntervalProfileBudget.intervalDerivative Q) a x nu r.val sigma
  let O : ℝ := sourceSeparatedOvershoot .interval
    (Shao.Probability.SourceActualIntervalProfileBudget.intervalDerivative Q) a x nu r.val sigma
  change |L| + max (-O) 0 ≤ K *
    Shao.Probability.SourceIIDGaussianProfileBudget.rankGaussianWeight H x
      (Shao.Probability.SourceActualLocalProfileBudget.wallSigns .interval) false
      (Shao.Probability.Spitzer.reorder a sigma) r
  have hCP := Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant_nonneg
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hReflection : Shao.Probability.SourceActualLocalProfileBudget.HalflineReflectionIdentities Q := by
    constructor
    · intro w y T z hw hT hy hz
      simpa only [Shao.C2.HalfLineReflectionFormula.upperReflection] using
        Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula Bm PB hBm w y T z hT hy hz
    · intro w y T z hw hT hy hz
      simpa only [Shao.C2.HalfLineReflectionFormula.lowerReflection] using
        Shao.C2.BridgeLowerIdentification.bridge_lower_formula Bm PB hBm w y T z hT hy hz
  have hRegular (w y T z : ℝ) (hw : 0 < w) (hT : 0 < T) (hy : |y| < w) (hz : |z| < w) :
      DifferentiableAt ℝ
        (fun Y => Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w Y T z) y :=
    (Shao.C2.BridgeIntervalImageResolved.sourceIntervalCompletion_spatial_hasDerivAt
      Bm PB hBm w y T z hw hy hz hT).differentiableAt
  have hKernel := Shao.Probability.SourceActualIntervalProfileBudget.actual_interval_kernel_data
    Q hReflection hRegular
  have hsigns : ∀ s ∈ Shao.Probability.SourceActualLocalProfileBudget.wallSigns .interval,
      s = 1 ∨ s = -1 := by
    simp only [Shao.Probability.SourceActualLocalProfileBudget.wallSigns,
      Finset.mem_insert, Finset.mem_singleton]
    exact fun s hs => hs
  let w : ℝ := actualWall a x
  let y : ℝ := Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) r.val
  let T : ℝ := remainingEnergy a r.val sigma
  let z : ℝ := Shao.prefixSum a n
  let b : ℝ := a (sigma r)
  have hNN : 0 ≤ Shao.Probability.SourceIIDGaussianProfileBudget.rankGaussianWeight H x (Shao.Probability.SourceActualLocalProfileBudget.wallSigns .interval) false
      (Shao.Probability.Spitzer.reorder a sigma) r :=
    ((Shao.Probability.SourceIIDGaussianProfileBudget.fixed_gaussian_weight_measurable_bound
      r.val (n-r.val) H x (Shao.Probability.SourceActualLocalProfileBudget.wallSigns .interval) false).2.1 _ _).1
  by_cases hact : r.val < nu sigma ∧ sourceAlive .interval a x r.val sigma ∧ 0 < T
  · have hw : 0 < w := mul_pos hx (Real.sqrt_pos.2 hact.2.1.1)
    have hy : |y| < w := abs_lt.mpr (hact.2.1.2.2 r.val le_rfl)
    have hz : |z| < w := abs_lt.mpr hact.2.1.2.1
    have hT : 0 < T := hact.2.2
    have hcut : H ≤ T := ((energy_cutoff_data a H hH).2.2 sigma r.val (hact.1.trans_le hcap)).2
    have hb : b ^ 2 ≤ T := (remaining_population_geometry a r.val r.is_lt.le sigma).2.2.1 r le_rfl
    have hzero : T - b ^ 2 = 0 → y + b = z := Shao.Probability.SourceActualLocalProfileBudget.actual_reveal_zero_future_reachable a r sigma
    have hExt (Y S : ℝ) : completionExt .interval (eventCompletionKernel .interval Q) w Y S z =
        Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w Y S z := by
      by_cases hY : |Y| < w
      · have hYi := abs_lt.mp hY
        have hzi := abs_lt.mp hz
        simp [completionExt, Interior, hw, hYi.1, hYi.2, hzi.1, hzi.2,
          Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion, eventCompletionKernel, hY]
      · rw [Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion_exterior Q w Y S z (by tauto)]
        have hYi : ¬(-w < Y ∧ Y < w) := fun hH => hY (abs_lt.mpr hH)
        simp only [completionExt, Interior, hYi, false_and, and_false, if_false]
    have hDer : deriv (fun Y : ℝ =>
        Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w Y T z) y =
        Shao.Probability.SourceActualIntervalProfileBudget.intervalDerivative Q (w,y,T,z) := by
      have hf : (fun Y : ℝ => Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w Y T z) =
          (fun Y : ℝ => eventCompletionKernel .interval Q (w,Y,T,z)) := by
        funext Y
        exact Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion_pos Q w Y T z hT
      rw [hf]
      exact (hKernel.2.2 w y T z hw hT hy hz).deriv
    have hRem (beta : ℝ) :
        localRemainder .interval (eventCompletionKernel .interval Q) (Shao.Probability.SourceActualIntervalProfileBudget.intervalDerivative Q) w y T z beta =
          Shao.C2.ActualIntervalProjection.sourceRemainder Q w y T z beta := by
      unfold localRemainder Shao.C2.ActualIntervalProjection.sourceRemainder
      rw [hExt, hDer]
      simp only [Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion, if_pos hT,
        eventCompletionKernel, compensationCoefficient]
    have hRet : localRetainedRemainder .interval (eventCompletionKernel .interval Q)
        (Shao.Probability.SourceActualIntervalProfileBudget.intervalDerivative Q) w y T z b = Shao.C2.IntervalGaussianLocal.retainedRemainder Q w y T z b := by
      by_cases hs : b^2 ≤ T/2 <;> by_cases hu : w ≤ y+b <;> by_cases hl : y+b ≤ -w
      all_goals
        have hH : ¬ |y+b| < w ↔ w ≤ y+b ∨ y+b ≤ -w := by
          constructor
          · intro hH
            by_contra hc
            push_neg at hc
            exact hH (abs_lt.mpr ⟨by linarith only [hc.2], hc.1⟩)
          · rintro (hu | hl) hH
            · exact not_lt_of_ge hu (abs_lt.mp hH).2
            · exact not_lt_of_ge hl (abs_lt.mp hH).1
        simp only [localRetainedRemainder, projectionIncrement, Shao.C2.IntervalGaussianLocal.retainedRemainder,
          hT, hs, hu, hl, hH, hRem, true_and, and_true, and_false, false_and,
          true_or, or_true, false_or, or_false, if_true, if_false]
    have hNeg : max (-localSeparatedOvershoot .interval (Shao.Probability.SourceActualIntervalProfileBudget.intervalDerivative Q) w y T z b) 0 =
        Shao.C2.IntervalGaussianLocal.negativeOvershoot Q w y T z b := by
      have huEq : -(b-(w-y))*(1-(b+(w-y))*(z-y)/T)*Shao.Probability.SourceActualIntervalProfileBudget.intervalDerivative Q (w,y,T,z) =
          Shao.C2.ActualIntervalProjection.upperOvershoot Q w y T z b := by
        simp only [Shao.C2.ActualIntervalProjection.upperOvershoot,
          Shao.C2.ProjectionOvershoot.projectionOvershoot, Shao.C2.ProjectionOvershoot.projectionFactor, hDer]
      have hlEq : -(b-(-w-y))*(1-(b+(-w-y))*(z-y)/T)*Shao.Probability.SourceActualIntervalProfileBudget.intervalDerivative Q (w,y,T,z) =
          Shao.C2.ActualIntervalProjection.lowerOvershoot Q w y T z b := by
        simp only [Shao.C2.ActualIntervalProjection.lowerOvershoot,
          Shao.C2.ProjectionOvershoot.projectionOvershoot, Shao.C2.ProjectionOvershoot.projectionFactor, hDer]
        ring
      by_cases hs : b^2 ≤ T/2 <;> by_cases hu : w ≤ y+b <;> by_cases hl : y+b ≤ -w
      all_goals
        have hH : ¬ |y+b| < w ↔ w ≤ y+b ∨ y+b ≤ -w := by
          constructor
          · intro hH
            by_contra hc
            push_neg at hc
            exact hH (abs_lt.mpr ⟨by linarith only [hc.2], hc.1⟩)
          · rintro (hu | hl) hH
            · exact not_lt_of_ge hu (abs_lt.mp hH).2
            · exact not_lt_of_ge hl (abs_lt.mp hH).1
        simp only [localSeparatedOvershoot, projectionIncrement, Shao.C2.IntervalGaussianLocal.negativeOvershoot,
          hT, hs, hu, hl, hH, true_and, and_true, and_false, false_and,
          true_or, or_true, false_or, or_false, if_true, if_false, huEq, hlEq,
          sub_self, neg_zero, zero_mul, max_self]
    have hbound := Shao.C2.BridgeIntervalImageResolved.actual_interval_retained_bound
      Bm PB hBm w y T z b hw hy hz hT hb hzero
    have hqperm : Shao.energy (Shao.Probability.Spitzer.reorder a sigma) = Shao.energy a := by
      simpa only [Shao.energy, Shao.Probability.Spitzer.reorder] using Equiv.sum_comp sigma (fun i => (a i)^2)
    have hsperm : Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) n = Shao.prefixSum a n := by
      simpa only [Shao.prefixSum_length, Shao.Probability.Spitzer.reorder] using Equiv.sum_comp sigma a
    have hA : ∀ s ∈ Shao.Probability.SourceActualLocalProfileBudget.wallSigns .interval,
        Shao.maxWithZero (s • Shao.Probability.Spitzer.head (Shao.Probability.Spitzer.reorder a sigma) r.val r.is_lt.le) < w := by
      intro s hs
      rcases hsigns s hs with rfl | rfl
      all_goals
        unfold Shao.maxWithZero
        rw [Finset.sup'_lt_iff]
        intro k hk
        rw [Shao.prefixSum_smul, Shao.Probability.Spitzer.head_prefixSum _ _ _ k (Finset.mem_Icc.1 hk).2]
        have hkLive := hact.2.1.2.2 k (Finset.mem_Icc.1 hk).2
      · simpa only [one_mul] using hkLive.2
      · simp only [neg_one_mul]
        linarith only [hkLive.1]
    have hRank : Shao.Probability.SourceIIDGaussianProfileBudget.rankGaussianWeight H x (Shao.Probability.SourceActualLocalProfileBudget.wallSigns .interval) false
        (Shao.Probability.Spitzer.reorder a sigma) r =
        (|b|/Real.sqrt T)^3 * (1+|z-y|/Real.sqrt T)^3 *
          Shao.C2.IntervalGaussianLargeStep.intervalEnvelope w y T z b := by
      have he := (Shao.Probability.SourceIIDGaussianProfileBudget.gaussian_weight_source_state
        (Shao.Probability.Spitzer.reorder a sigma) r H x (Shao.Probability.SourceActualLocalProfileBudget.wallSigns .interval) false).2.2.2.2
      rw [hqperm, hsperm] at he
      have hsel : 0 < Shao.energy a - Shao.prefixSquares (Shao.Probability.Spitzer.reorder a sigma) r.val ∧
          H ≤ Shao.energy a - Shao.prefixSquares (Shao.Probability.Spitzer.reorder a sigma) r.val ∧
          (∀ s ∈ Shao.Probability.SourceActualLocalProfileBudget.wallSigns .interval,
            if false = true then Shao.maxWithZero
              (s • Shao.Probability.Spitzer.head (Shao.Probability.Spitzer.reorder a sigma) r.val r.is_lt.le) ≤ x*Real.sqrt (Shao.energy a)
            else Shao.maxWithZero
              (s • Shao.Probability.Spitzer.head (Shao.Probability.Spitzer.reorder a sigma) r.val r.is_lt.le) < x*Real.sqrt (Shao.energy a)) :=
        ⟨hT,hcut,by simpa only [Bool.false_eq_true, ite_false, w, actualWall] using hA⟩
      rw [if_pos hsel, if_pos (show 0 < Shao.energy a -
        Shao.prefixSquares (Shao.Probability.Spitzer.reorder a sigma) r.val from hT)] at he
      convert he using 1
      simp only [Shao.Probability.SourceActualLocalProfileBudget.wallSigns,
        Finset.sum_insert (by norm_num : (1:ℝ) ∉ ({-1}:Finset ℝ)),
        Finset.sum_singleton, one_mul, neg_one_mul, sub_neg_eq_add,
        Shao.C2.IntervalGaussianLargeStep.intervalEnvelope, Shao.C2.GaussianWallEnvelope.wallEnvelope]
      dsimp only [w, y, z, b, T, actualWall, remainingEnergy, Shao.Probability.Spitzer.reorder]
      congr 2 <;> ring
    dsimp only [L, O]
    simp only [sourceRetainedRemainder, sourceSeparatedOvershoot, dif_pos r.is_lt,
      if_pos (show r.val < nu sigma ∧ sourceAlive .interval a x r.val sigma ∧
        0 < remainingEnergy a r.val sigma from hact)]
    change |localRetainedRemainder .interval (eventCompletionKernel .interval Q) (Shao.Probability.SourceActualIntervalProfileBudget.intervalDerivative Q) w y T z b| +
      max (-localSeparatedOvershoot .interval (Shao.Probability.SourceActualIntervalProfileBudget.intervalDerivative Q) w y T z b) 0 ≤ _
    rw [hRet, hNeg, hRank]
    simpa only [K, mul_assoc] using hbound
  · dsimp only [L, O]
    have hinactive : ¬ (r.val < nu sigma ∧ sourceAlive .interval a x r.val sigma ∧
        0 < remainingEnergy a r.val sigma) := hact
    simp only [sourceRetainedRemainder, sourceSeparatedOvershoot, dif_pos r.is_lt,
      if_neg hinactive, abs_zero, neg_zero, max_self, add_zero]
    exact mul_nonneg hKpos.le hNN

private theorem arr_two_sign_rank_gaussian_le
    {n : ℕ} (a : Shao.Path n) (r : Fin n) (H x : ℝ) :
    Shao.Probability.SourceIIDGaussianProfileBudget.rankGaussianWeight H x {1, -1} false a r ≤
      Shao.Probability.SourceIIDGaussianProfileBudget.rankGaussianWeight H x {1} false a r +
      Shao.Probability.SourceIIDGaussianProfileBudget.rankGaussianWeight H x {-1} false a r := by
  classical
  let v := Shao.Probability.Spitzer.head a r.val r.is_lt.le
  let u := Shao.Probability.Spitzer.tail a r.val r.is_lt.le
  change Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight H x {1, -1} false v u ≤
    Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight H x {1} false v u +
    Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight H x {-1} false v u
  have hplusNN : 0 ≤ Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight H x {1} false v u :=
    ((Shao.Probability.SourceIIDGaussianProfileBudget.fixed_gaussian_weight_measurable_bound
      r.val (n-r.val) H x {1} false).2.1 v u).1
  have hminusNN : 0 ≤ Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight H x {-1} false v u :=
    ((Shao.Probability.SourceIIDGaussianProfileBudget.fixed_gaussian_weight_measurable_bound
      r.val (n-r.val) H x {-1} false).2.1 v u).1
  by_cases hact : 0 < Shao.energy u ∧ H ≤ Shao.energy u ∧
      Shao.Probability.SourceIIDGaussianProfileBudget.prefixSurvival x {1, -1} false v u
  · have hplus : Shao.Probability.SourceIIDGaussianProfileBudget.prefixSurvival x {1} false v u := by
      intro s hs
      have hs1 : s = 1 := Finset.mem_singleton.mp hs
      subst s
      exact hact.2.2 1 (by simp)
    have hminus : Shao.Probability.SourceIIDGaussianProfileBudget.prefixSurvival x {-1} false v u := by
      intro s hs
      have hs1 : s = -1 := Finset.mem_singleton.mp hs
      subst s
      exact hact.2.2 (-1) (by simp)
    have hplusAct : 0 < Shao.energy u ∧ H ≤ Shao.energy u ∧
        Shao.Probability.SourceIIDGaussianProfileBudget.prefixSurvival x {1} false v u :=
      ⟨hact.1, hact.2.1, hplus⟩
    have hminusAct : 0 < Shao.energy u ∧ H ≤ Shao.energy u ∧
        Shao.Probability.SourceIIDGaussianProfileBudget.prefixSurvival x {-1} false v u :=
      ⟨hact.1, hact.2.1, hminus⟩
    simp only [Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight,
      if_pos hact, if_pos hplusAct, if_pos hminusAct,
      Shao.Probability.SourceIIDGaussianProfileBudget.gaussianProfiles, if_pos hact.1,
      Finset.sum_insert (by norm_num : (1 : ℝ) ∉ ({-1} : Finset ℝ)), Finset.sum_singleton]
    exact le_of_eq (by ring)
  · rw [Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight, if_neg hact]
    exact add_nonneg hplusNN hminusNN

theorem actual_retained_absolute_rank_gaussian_domination
    {ΩB : Type*} [MeasurableSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (Bm : ℝ≥0 → ΩB → ℝ) (hBm : IsBrownianReal Bm PB)
    {n : ℕ} (a : Shao.Path n) (H x : ℝ) (hH : 0 < H) (hx : 0 < x)
    (nu : LabelPerm n → ℕ) (sigma : LabelPerm n)
    (hcap : nu sigma ≤ energyCutoff a H sigma) (r : Fin n) :
    let Q : Measure BridgeNoise := bridgeLaw Bm PB
    0 ≤ actualRetainedAbsoluteRank Q a x nu r sigma ∧
    actualRetainedAbsoluteRank Q a x nu r sigma ≤
      (8000100 + (2 * Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant + 40)) *
        (Shao.Probability.SourceIIDGaussianProfileBudget.rankGaussianWeight H x {1} false
            (Shao.Probability.Spitzer.reorder a sigma) r +
         Shao.Probability.SourceIIDGaussianProfileBudget.rankGaussianWeight H x {-1} false
            (Shao.Probability.Spitzer.reorder a sigma) r) := by
  classical
  dsimp only
  let Q : Measure BridgeNoise := bridgeLaw Bm PB
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw Bm PB hBm
  have hReflection : Shao.Probability.SourceActualLocalProfileBudget.HalflineReflectionIdentities Q := by
    constructor
    · intro w y T z hw hT hy hz
      simpa only [Shao.C2.HalfLineReflectionFormula.upperReflection] using
        Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula Bm PB hBm w y T z hT hy hz
    · intro w y T z hw hT hy hz
      simpa only [Shao.C2.HalfLineReflectionFormula.lowerReflection] using
        Shao.C2.BridgeLowerIdentification.bridge_lower_formula Bm PB hBm w y T z hT hy hz
  have hI := arr_interval_rank_gaussian_domination PB Bm hBm a H x hH hx nu sigma hcap r
  have hU := Shao.Probability.SourceActualLocalProfileBudget.actual_halfline_retained_rank_domination
    Q hReflection .upper (Or.inl rfl) a H x hH hx nu sigma hcap r
  have hL := Shao.Probability.SourceActualLocalProfileBudget.actual_halfline_retained_rank_domination
    Q hReflection .lower (Or.inr rfl) a H x hH hx nu sigma hcap r
  have hS := arr_two_sign_rank_gaussian_le (Shao.Probability.Spitzer.reorder a sigma) r H x
  have hCP := Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant_nonneg
  have hCI : 0 ≤ 2 * Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant + 40 := by positivity
  have hItwo := hI.trans (mul_le_mul_of_nonneg_left hS hCI)
  change 0 ≤ actualRetainedAbsoluteRank Q a x nu r sigma ∧ _
  refine ⟨?_, ?_⟩
  · unfold actualRetainedAbsoluteRank
    positivity
  · dsimp only [actualRetainedAbsoluteRank]
    change |sourceRetainedRemainder .interval (eventCompletionKernel .interval Q)
        (actualDerivativeFamily Q .interval) a x nu r.val sigma| +
      |sourceRetainedRemainder .upper (eventCompletionKernel .upper Q)
        (actualDerivativeFamily Q .upper) a x nu r.val sigma| +
      |sourceRetainedRemainder .lower (eventCompletionKernel .lower Q)
        (actualDerivativeFamily Q .lower) a x nu r.val sigma| +
      max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
        a x nu r.val sigma) 0 ≤ _
    simp only [actualDerivativeFamily] at ⊢
    simp only [Shao.Probability.SourceActualLocalProfileBudget.wallSigns] at hU hL
    simp only [actualDerivativeFamily] at hItwo
    nlinarith only [hItwo, hU, hL]

private theorem arr_late_fixed_suffix_gaussian_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (Bcap : ℝ), 0 < Bcap → (∀ᵐ z : ℝ ∂rho, |z| ≤ Bcap) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), 16 ≤ x →
          Bcap ≤ Real.sqrt (n : ℝ) / (100 * x) →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          ∀ (r t : ℕ), n = r + t → 0 < r → n ≤ 2 * r →
            ∀ (u : Shao.Path t) (H : ℝ), 0 < H → 4 * beta ^ 2 ≤ H →
              ∀ (s : ℝ), (s = 1 ∨ s = -1) →
                let Pr : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => rho)
                let T : ℝ := Shao.energy u
                let F : Shao.Path r → ℝ := fun v =>
                  Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight
                    H x {s} false v u
                let W : ℝ := if 0 < T ∧ H ≤ T then
                    |Shao.Probability.SourceIIDGaussianProfileBudget.firstValue u| ^ 3 /
                      Real.sqrt T *
                        (Shao.Probability.SourceMarkedSuffixAveraging.suffixD u) ^ 5
                  else 0
                Integrable F Pr ∧ (∫ v, F v ∂Pr) ≤ C / (r : ℝ) * W := by
  classical
  obtain ⟨Cs, hCs, hstrip⟩ :=
    Shao.C2.ActualBadIntervalNegativeBudget.actual_large_x_true_energy_closed_strip
  refine ⟨9 * Cs, by positivity, ?_⟩
  intro rho hProb Bcap hBcap hsupport hmean hsecond n hn x hx hsupportN
    beta r t hsplit hr hlate u H hH hHbeta s hs Pr T F W
  letI : IsProbabilityMeasure rho := hProb
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hsqrtr : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 hrR
  have hBr : (beta / Real.sqrt (r : ℝ)) ^ 2 = beta ^ 2 / (r : ℝ) := by
    rw [div_pow, Real.sq_sqrt hrR.le]
  have hdata :=
    Shao.Probability.SourceIIDGaussianProfileBudget.fixed_gaussian_weight_measurable_bound
      r t H x {s} false
  have hFm : Measurable F :=
    hdata.1.comp (measurable_id.prodMk measurable_const)
  have hFi : Integrable F Pr :=
    (integrable_const ((({s} : Finset ℝ).card : ℝ) *
      (1 + Real.sqrt (t : ℝ)) ^ 3)).mono' hFm.aestronglyMeasurable
      (ae_of_all _ fun v => by
        simpa only [Real.norm_eq_abs] using (hdata.2.1 v u).2)
  refine ⟨hFi, ?_⟩
  by_cases hcut : 0 < T ∧ H ≤ T
  · let b : ℝ := Shao.Probability.SourceIIDGaussianProfileBudget.firstValue u
    let d : ℝ := Shao.prefixSum u t
    let D : ℝ := Shao.Probability.SourceMarkedSuffixAveraging.suffixD u
    let M : ℝ := |b| + max (s * d) 0
    let wall : Shao.Path r → ℝ := fun v => x * Real.sqrt (T + Shao.energy v)
    let A : Set (Shao.Path r) := {v | Shao.maxWithZero (s • v) < wall v}
    let w : Shao.Path r → ℝ := fun v => wall v - s * Shao.prefixSum v r
    let profile : Shao.Path r → ℝ := fun v =>
      Real.exp (-((max (w v - M) 0) ^ 2) / T)
    have hT : 0 < T := hcut.1
    have hsqrtT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
    have hsqrtT2 : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hT.le
    have hwm : Measurable wall :=
      measurable_const.mul ((measurable_const.add Shao.measurable_energy).sqrt)
    have hw : Measurable w :=
      hwm.sub (measurable_const.mul (Shao.measurable_prefixSum r))
    have hmaxm : Measurable (fun v : Shao.Path r => Shao.maxWithZero (s • v)) :=
      Shao.measurable_maxWithZero.comp (Measurable.of_eval fun i =>
        measurable_const.mul (measurable_pi_apply i))
    have hA : MeasurableSet A := measurableSet_lt hmaxm hwm
    have hM0 : 0 ≤ M := add_nonneg (abs_nonneg b) (le_max_right _ _)
    have hDeq : D = 1 + |d| / Real.sqrt T := by
      change (if 0 < T then 1 + |d| / Real.sqrt T else 1) = _
      exact if_pos hT
    have hD : 1 ≤ D := by
      rw [hDeq]
      linarith only [div_nonneg (abs_nonneg d) hsqrtT.le]
    have hD0 : 0 ≤ D := (by norm_num : (0 : ℝ) ≤ 1).trans hD
    have hD2 : 1 ≤ D ^ 2 := by nlinarith only [hD]
    have hb : b ^ 2 ≤ T := by
      dsimp only [b, Shao.Probability.SourceIIDGaussianProfileBudget.firstValue]
      split_ifs with ht
      · change (u ⟨0, ht⟩) ^ 2 ≤ ∑ i : Fin t, (u i) ^ 2
        exact Finset.single_le_sum (fun i _ => sq_nonneg (u i))
          (Finset.mem_univ (⟨0, ht⟩ : Fin t))
      · simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using Shao.energy_nonneg u
    have hbabs : |b| ≤ Real.sqrt T :=
      (sq_le_sq₀ (abs_nonneg b) hsqrtT.le).1
        (by simpa only [sq_abs, hsqrtT2] using hb)
    have hsd : s * d ≤ |d| := by
      rcases hs with rfl | rfl
      · simpa only [one_mul] using le_abs_self d
      · simpa only [neg_one_mul] using neg_le_abs d
    have hMle : M ≤ Real.sqrt T * D := by
      calc
        M ≤ |b| + |d| := add_le_add le_rfl (max_le hsd (abs_nonneg d))
        _ ≤ Real.sqrt T + |d| := add_le_add hbabs le_rfl
        _ = Real.sqrt T * D := by
          rw [hDeq, mul_add, mul_one, mul_div_cancel₀ _ hsqrtT.ne']
    have hM2 : M ^ 2 ≤ T * D ^ 2 := by
      have hh := (sq_le_sq₀ hM0 (mul_nonneg hsqrtT.le hD0)).2 hMle
      simpa only [mul_pow, hsqrtT2] using hh
    have hsurv (v : Shao.Path r) :
        Shao.Probability.SourceIIDGaussianProfileBudget.prefixSurvival x {s} false v u ↔
          v ∈ A := by
      simp [Shao.Probability.SourceIIDGaussianProfileBudget.prefixSurvival, A, wall, T]
    have he (v : Shao.Path r) :
        F v = (|b| ^ 3 / (T * Real.sqrt T) * D ^ 3) * A.indicator profile v := by
      by_cases hv : v ∈ A
      · have hcond : 0 < Shao.energy u ∧ H ≤ Shao.energy u ∧
            Shao.Probability.SourceIIDGaussianProfileBudget.prefixSurvival x {s} false v u :=
          ⟨hcut.1, hcut.2, (hsurv v).2 hv⟩
        change Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight
          H x {s} false v u = _
        rw [Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight,
          if_pos hcond, Set.indicator_of_mem hv]
        simp only [Shao.Probability.SourceIIDGaussianProfileBudget.gaussianProfiles,
          Finset.sum_singleton, if_pos hcut.1]
        rfl
      · have hnot : ¬Shao.Probability.SourceIIDGaussianProfileBudget.prefixSurvival
            x {s} false v u := fun hh => hv ((hsurv v).1 hh)
        change Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight
          H x {s} false v u = _
        rw [Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight,
          if_neg (by tauto), Set.indicator_of_notMem hv, mul_zero]
    have hCDF (a : ℝ) (ha : 0 ≤ a) :
        Pr.real {v | v ∈ A ∧ w v ≤ a} ≤
          (2 * Cs) * (a ^ 2 / (r : ℝ) + (beta / Real.sqrt (r : ℝ)) ^ 2) := by
      have hbnd := hstrip rho Bcap hBcap hsupport hmean hsecond n hn x hx hsupportN
        r hr (by omega) hlate T a s hT.le ha hs
      change Pr.real {v : Shao.Path r |
          Shao.maxWithZero (s • v) ≤ wall v ∧
          wall v - a ≤ s * Shao.prefixSum v r ∧
          s * Shao.prefixSum v r ≤ wall v} ≤ Cs * (a + beta) ^ 2 / (r : ℝ) at hbnd
      have hsub : {v | v ∈ A ∧ w v ≤ a} ⊆ {v : Shao.Path r |
          Shao.maxWithZero (s • v) ≤ wall v ∧
          wall v - a ≤ s * Shao.prefixSum v r ∧
          s * Shao.prefixSum v r ≤ wall v} := by
        intro v hv
        have hvmax : Shao.maxWithZero (s • v) ≤ wall v :=
          (show Shao.maxWithZero (s • v) < wall v from hv.1).le
        have hvsum := (Shao.maxWithZero_le_iff (s • v) (wall v)).1 hvmax r le_rfl
        rw [Shao.prefixSum_smul] at hvsum
        have hvw : wall v - s * Shao.prefixSum v r ≤ a := hv.2
        exact ⟨hvmax, by linarith only [hvw], hvsum⟩
      have hsq : (a + beta) ^ 2 ≤ 2 * (a ^ 2 + beta ^ 2) := by
        nlinarith only [sq_nonneg (a - beta)]
      calc
        _ ≤ Pr.real {v : Shao.Path r |
            Shao.maxWithZero (s • v) ≤ wall v ∧
            wall v - a ≤ s * Shao.prefixSum v r ∧
            s * Shao.prefixSum v r ≤ wall v} := measureReal_mono hsub
        _ ≤ Cs * (a + beta) ^ 2 / (r : ℝ) := hbnd
        _ ≤ Cs * (2 * (a ^ 2 + beta ^ 2)) / (r : ℝ) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hCs.le) hrR.le
        _ = _ := by rw [hBr]; ring
    have hg := Shao.Probability.gaussian_wall_profile_of_quadratic_closed_cdf
      Pr A hA w hw (2 * Cs) (beta / Real.sqrt (r : ℝ)) (r : ℝ) T M
      (by positivity) hrR hT hM0 hCDF
    change (∫ v, A.indicator profile v ∂Pr) ≤
      (2 * Cs) * (2 * (M ^ 2 + T) / (r : ℝ) +
        (beta / Real.sqrt (r : ℝ)) ^ 2) at hg
    have hbetaT : 4 * beta ^ 2 ≤ T := hHbeta.trans hcut.2
    have hTD : T ≤ T * D ^ 2 := by
      nlinarith only [mul_le_mul_of_nonneg_left hD2 hT.le]
    have hgeom : 4 * M ^ 2 + 4 * T + 2 * beta ^ 2 ≤ 9 * T * D ^ 2 := by
      have hTD0 : 0 ≤ T * D ^ 2 := mul_nonneg hT.le (sq_nonneg D)
      nlinarith only [hM2, hTD, hbetaT, hTD0]
    have hprofile : (∫ v, A.indicator profile v ∂Pr) ≤
        9 * Cs * T * D ^ 2 / (r : ℝ) := by
      calc
        _ ≤ (2 * Cs) * (2 * (M ^ 2 + T) / (r : ℝ) +
            (beta / Real.sqrt (r : ℝ)) ^ 2) := hg
        _ = (Cs / (r : ℝ)) * (4 * M ^ 2 + 4 * T + 2 * beta ^ 2) := by
          rw [hBr]
          ring
        _ ≤ (Cs / (r : ℝ)) * (9 * T * D ^ 2) :=
          mul_le_mul_of_nonneg_left hgeom (div_nonneg hCs.le hrR.le)
        _ = _ := by ring
    have hWeq : W = |b| ^ 3 / Real.sqrt T * D ^ 5 := if_pos hcut
    rw [hWeq]
    calc
      (∫ v, F v ∂Pr) =
          (|b| ^ 3 / (T * Real.sqrt T) * D ^ 3) *
            (∫ v, A.indicator profile v ∂Pr) := by
        simp_rw [he]
        exact integral_const_mul _ _
      _ ≤ (|b| ^ 3 / (T * Real.sqrt T) * D ^ 3) *
          (9 * Cs * T * D ^ 2 / (r : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hprofile
        exact mul_nonneg (div_nonneg (pow_nonneg (abs_nonneg b) 3)
          (mul_nonneg hT.le hsqrtT.le)) (pow_nonneg hD0 3)
      _ = (9 * Cs) / (r : ℝ) * (|b| ^ 3 / Real.sqrt T * D ^ 5) := by
        field_simp [hT.ne', hsqrtT.ne', hrR.ne']
        <;> ring
  · have hFzero : F = fun _ => 0 := by
      funext v
      change Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight
        H x {s} false v u = 0
      unfold Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight
      exact if_neg (by tauto)
    rw [hFzero, integral_zero]
    simp only [W, if_neg hcut, mul_zero, le_refl]

private theorem arr_omitted_mask_iff
    {n : ℕ} (a : Shao.Path n) (h0 H : ℝ) (hh0 : 0 < h0) (hH : 0 < H)
    (sigma : LabelPerm n) (r : Fin n) (m : ℕ) :
    (min (energyCutoff a H sigma) (n - m) ≤ r.val ∧
        r.val < energyCutoff a h0 sigma) ↔
      h0 ≤ remainingEnergy a r.val sigma ∧
        (remainingEnergy a r.val sigma < H ∨ n - r.val ≤ m) := by
  classical
  have hHcut : energyCutoff a H sigma ≤ r.val ↔ remainingEnergy a r.val sigma < H :=
    (energy_cutoff_data a H hH).2.1 sigma r.val r.is_lt.le
  have hh0cut : energyCutoff a h0 sigma ≤ r.val ↔ remainingEnergy a r.val sigma < h0 :=
    (energy_cutoff_data a h0 hh0).2.1 sigma r.val r.is_lt.le
  have hnu : r.val < energyCutoff a h0 sigma ↔ h0 ≤ remainingEnergy a r.val sigma := by
    constructor
    · intro hr
      exact ((energy_cutoff_data a h0 hh0).2.2 sigma r.val hr).2
    · intro hT
      by_contra hr
      have hcut : energyCutoff a h0 sigma ≤ r.val := Nat.le_of_not_gt hr
      exact (not_lt.mpr hT) (hh0cut.mp hcut)
  have hm : n - m ≤ r.val ↔ n - r.val ≤ m := by omega
  rw [min_le_iff, hHcut, hnu, hm]
  tauto

private theorem arr_absolute_rank_measurable_integrable
    {ΩB : Type*} [MeasurableSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (Bm : ℝ≥0 → ΩB → ℝ) (hBm : IsBrownianReal Bm PB)
    {n : ℕ} (P : Measure (Shao.Path n)) [IsProbabilityMeasure P]
    (x : ℝ) (hx : 0 < x) (nu : Shao.Path n → LabelPerm n → ℕ)
    (hnu : ∀ sigma, Measurable (fun a => nu a sigma)) (r : Fin n) :
    let Q : Measure BridgeNoise := bridgeLaw Bm PB
    let F : Shao.Path n × LabelPerm n → ℝ := fun p =>
      actualRetainedAbsoluteRank Q p.1 x (nu p.1) r p.2
    Measurable F ∧ Integrable F (revealLaw P) ∧
      (∀ p, 0 ≤ F p) ∧ (∀ p, F p ≤ 3 + 88 * (1 + (n : ℝ))) := by
  classical
  intro Q F
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw Bm PB hBm
  letI : IsProbabilityMeasure (revealLaw P) := by unfold revealLaw; infer_instance
  have hReflection : Shao.Probability.SourceActualLocalProfileBudget.HalflineReflectionIdentities Q := by
    constructor
    · intro w y T z _hw hT hy hz
      simpa only [Shao.C2.HalfLineReflectionFormula.upperReflection] using
        Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula Bm PB hBm w y T z hT hy hz
    · intro w y T z _hw hT hy hz
      simpa only [Shao.C2.HalfLineReflectionFormula.lowerReflection] using
        Shao.C2.BridgeLowerIdentification.bridge_lower_formula Bm PB hBm w y T z hT hy hz
  have hReg (w y T z : ℝ) (hw : 0 < w) (hT : 0 < T) (hy : |y| < w) (hz : |z| < w) :
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
        have hd := Shao.Probability.SourceActualIntervalProfileBudget.actual_interval_kernel_data
          Q hReflection hReg
        exact ⟨by simpa only [actualDerivativeFamily] using hd.1,
          by simpa only [actualDerivativeFamily] using hd.2.1⟩
  have hp (J : MonitoredDomain) := source_parts_measurable_integrable J
    (eventCompletionKernel J Q) (actualDerivativeFamily Q J)
    (eventCompletionKernel_data J Q).1 (hk J).1 4 (hk J).2 P x hx nu hnu
  have hLm (J : MonitoredDomain) : Measurable (fun p : Shao.Path n × LabelPerm n =>
      sourceRetainedRemainder J (eventCompletionKernel J Q)
        (actualDerivativeFamily Q J) p.1 x (nu p.1) r.val p.2) := by
    apply measurable_from_prod_countable_left
    intro sigma
    exact ((hp J).1 sigma r.val).1
  have hOm : Measurable (fun p : Shao.Path n × LabelPerm n =>
      sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
        p.1 x (nu p.1) r.val p.2) := by
    apply measurable_from_prod_countable_left
    intro sigma
    exact ((hp .interval).1 sigma r.val).2
  have hFm : Measurable F := by
    dsimp only [F, actualRetainedAbsoluteRank]
    exact ((((continuous_abs.measurable.comp (hLm .interval)).add
      (continuous_abs.measurable.comp (hLm .upper))).add
      (continuous_abs.measurable.comp (hLm .lower))).add (hOm.neg.max measurable_const))
  have hNN (p : Shao.Path n × LabelPerm n) : 0 ≤ F p := by
    dsimp only [F, actualRetainedAbsoluteRank]
    positivity
  have hB (p : Shao.Path n × LabelPerm n) : F p ≤ 3 + 88 * (1 + (n : ℝ)) := by
    have hd (J : MonitoredDomain) := source_parts_uniform_bound J
      (eventCompletionKernel J Q) (actualDerivativeFamily Q J) 4 (hk J).2
      p.1 x hx (nu p.1) r.val p.2
    have hNeg : max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
        p.1 x (nu p.1) r.val p.2) 0 ≤ 4 * 4 * (1 + (n : ℝ)) :=
      max_le ((neg_le_abs _).trans (hd .interval).1) (by positivity)
    dsimp only [F, actualRetainedAbsoluteRank]
    nlinarith only [(hd .interval).2, (hd .upper).2, (hd .lower).2, hNeg]
  refine ⟨hFm, ?_, hNN, hB⟩
  exact (integrable_const (3 + 88 * (1 + (n : ℝ)))).mono'
    hFm.aestronglyMeasurable (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hNN p)]
      exact hB p)

private theorem arr_iid_late_omitted_gaussian_bill :
    let K : ℝ := (2 : ℝ) ^ 64
    ∃ C : ℝ, 0 < C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (Bcap : ℝ), 0 < Bcap → (∀ᵐ z : ℝ ∂rho, |z| ≤ Bcap) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), 16 ≤ x →
          Bcap ≤ Real.sqrt (n : ℝ) / (100 * x) →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          let delta : ℝ := beta / Real.sqrt (n : ℝ)
          delta * (1 + x) ^ 3 ≤ Real.exp (-3 * x ^ 2) →
          let h0 : ℝ := 4 * beta ^ 2
          let H : ℝ := K * beta ^ 2 * (1 + x) ^ 6
          let m : ℕ := ⌈H⌉₊
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
          let nu : Shao.Path n → LabelPerm n → ℕ :=
            fun a sigma => energyCutoff a h0 sigma
          let tau : Shao.Path n → LabelPerm n → ℕ := fun a sigma =>
            min (energyCutoff a H sigma) (n - m)
          ∀ (s : ℝ), (s = 1 ∨ s = -1) →
            let bill : Shao.Path n × LabelPerm n → ℝ := fun p =>
              ∑ r : Fin n, if n / 2 < r.val ∧ tau p.1 p.2 ≤ r.val ∧
                  r.val < nu p.1 p.2 then
                Shao.Probability.SourceIIDGaussianProfileBudget.rankGaussianWeight
                  h0 x {s} false (Shao.Probability.Spitzer.reorder p.1 p.2) r
              else 0
            Measurable bill ∧ Integrable bill (revealLaw P) ∧
              (∀ p, 0 ≤ bill p) ∧
              (∫ p, bill p ∂revealLaw P) ≤ C * beta * Real.sqrt H / (n : ℝ) ∧
              (∫ p, bill p ∂revealLaw P) ≤ C * delta * Shao.standardNormalTail x := by
  classical
  intro K
  obtain ⟨CL, hCL, hLateFixed⟩ := arr_late_fixed_suffix_gaussian_bound
  obtain ⟨CW, hCW, hPay⟩ :=
    Shao.Probability.SourceLateOmittedSuffixBudget.iid_actual_late_omitted_suffix_budget
  let C : ℝ := 2 * CL * CW
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro rho hProb Bcap hBcap hsupport hmean hsecond n hn x hx hscale
    beta delta hres h0 H m P nu tau s hs bill
  letI : IsProbabilityMeasure rho := hProb
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  letI : IsProbabilityMeasure (revealLaw P) := by unfold revealLaw; infer_instance
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have h2 : Integrable (fun z : ℝ => z ^ 2) rho := by
    refine (integrable_const (Bcap ^ 2)).mono' (by fun_prop) ?_
    filter_upwards [hsupport] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z) hz 2
  have h3 : Integrable (fun z : ℝ => |z| ^ 3) rho := by
    refine (integrable_const (Bcap ^ 3)).mono' (by fun_prop) ?_
    filter_upwards [hsupport] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ |z| ^ 3)]
    exact pow_le_pow_left₀ (abs_nonneg z) hz 3
  have hbeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one
      rho h2 h3 hsecond
  have hbeta0 : 0 < beta := lt_of_lt_of_le zero_lt_one hbeta
  have hh0 : 0 < h0 := by dsimp [h0]; positivity
  have hK4 : 4 ≤ K := by norm_num [K]
  have hx6 : 1 ≤ (1 + x) ^ 6 :=
    one_le_pow₀ (by linarith only [hx] : 1 ≤ 1 + x)
  have hh0H : h0 ≤ H := by
    have h1 := mul_le_mul_of_nonneg_right hK4 (sq_nonneg beta)
    have h2' := mul_le_mul_of_nonneg_left hx6
      (mul_nonneg (by norm_num [K] : 0 ≤ K) (sq_nonneg beta))
    dsimp only [h0, H]
    nlinarith only [h1, h2']
  have hH : 0 < H := hh0.trans_le hh0H
  let Pt : (t : ℕ) → Measure (Shao.Path t) :=
    fun t => Measure.pi (fun _ : Fin t => rho)
  have hPt (t : ℕ) : IsProbabilityMeasure (Pt t) := by dsimp [Pt]; infer_instance
  -- The future weight uses the complete suffix, including its first label.
  let W : (t : ℕ) → Shao.Path t → ℝ := fun t u =>
    if h0 ≤ Shao.energy u ∧ (Shao.energy u < H ∨ t ≤ m) then
      |Shao.Probability.SourceIIDGaussianProfileBudget.firstValue u| ^ 3 /
        Real.sqrt (Shao.energy u) *
          (1 + |Shao.prefixSum u t| / Real.sqrt (Shao.energy u)) ^ 5
    else 0
  have hWm (t : ℕ) : Measurable (W t) := by
    have hb : Measurable
        (Shao.Probability.SourceIIDGaussianProfileBudget.firstValue : Shao.Path t → ℝ) := by
      change Measurable (fun u : Shao.Path t => if ht : 0 < t then u ⟨0, ht⟩ else 0)
      by_cases ht : 0 < t
      · simpa only [dif_pos ht] using
          (measurable_pi_apply (X := fun _ : Fin t => ℝ) (⟨0, ht⟩ : Fin t))
      · simpa only [dif_neg ht] using
          (measurable_const : Measurable (fun _ : Shao.Path t => (0 : ℝ)))
    have hguard : MeasurableSet {u : Shao.Path t |
        h0 ≤ Shao.energy u ∧ (Shao.energy u < H ∨ t ≤ m)} := by
      by_cases ht : t ≤ m
      · simpa only [ht, or_true, and_true] using
          measurableSet_le measurable_const Shao.measurable_energy
      · simpa only [ht, or_false, Set.setOf_and] using
          (measurableSet_le measurable_const Shao.measurable_energy).inter
            (measurableSet_lt Shao.measurable_energy measurable_const)
    exact Measurable.ite hguard
      ((((continuous_abs.measurable.comp hb).pow_const 3).div Shao.measurable_energy.sqrt).mul
        ((measurable_const.add
          ((continuous_abs.measurable.comp (Shao.measurable_prefixSum t)).div Shao.measurable_energy.sqrt)).pow_const 5))
      measurable_const
  have hW0 (t : ℕ) (u : Shao.Path t) : 0 ≤ W t u := by
    dsimp only [W]
    split_ifs <;> positivity
  -- This energy majorant supplies genuine L1 independently of the numerical bill.
  have hWbound (t : ℕ) (u : Shao.Path t) :
      W t u ≤ (1 + Real.sqrt (t : ℝ)) ^ 5 * Shao.energy u := by
    by_cases hsel : h0 ≤ Shao.energy u ∧ (Shao.energy u < H ∨ t ≤ m)
    · have hT : 0 < Shao.energy u := hh0.trans_le hsel.1
      have hsqrt : 0 < Real.sqrt (Shao.energy u) := Real.sqrt_pos.2 hT
      have hcub :
          |Shao.Probability.SourceIIDGaussianProfileBudget.firstValue u| ^ 3 ≤
            Shao.energy u * Real.sqrt (Shao.energy u) := by
        apply le_trans _
          (Shao.Probability.SourceMarkedSuffixAveraging.suffix_normalized_geometry u).2.2.1
        by_cases ht : 0 < t
        · simpa only [Shao.Probability.SourceIIDGaussianProfileBudget.firstValue,
            dif_pos ht, Shao.Probability.SourceMarkedSuffixAveraging.cubicMass] using
            (Finset.single_le_sum (fun i _ => pow_nonneg (abs_nonneg (u i)) 3)
              (Finset.mem_univ (⟨0, ht⟩ : Fin t)))
        · simp only [Shao.Probability.SourceIIDGaussianProfileBudget.firstValue,
            dif_neg ht, abs_zero, zero_pow (by norm_num : (3 : ℕ) ≠ 0)]
          exact Finset.sum_nonneg fun i _ => pow_nonneg (abs_nonneg (u i)) 3
      have hratio :
          |Shao.Probability.SourceIIDGaussianProfileBudget.firstValue u| ^ 3 /
              Real.sqrt (Shao.energy u) ≤ Shao.energy u :=
        (div_le_iff₀ hsqrt).2 hcub
      have hD :=
        (Shao.Probability.SourceMarkedSuffixAveraging.suffix_normalized_geometry u).2.2.2.2.2.1
      have hDle : 1 + |Shao.prefixSum u t| / Real.sqrt (Shao.energy u) ≤
          1 + Real.sqrt (t : ℝ) := by
        simpa only [Shao.Probability.SourceMarkedSuffixAveraging.suffixD, if_pos hT]
          using hD.2
      dsimp only [W]
      rw [if_pos hsel]
      calc
        _ ≤ Shao.energy u * (1 + Real.sqrt (t : ℝ)) ^ 5 :=
          mul_le_mul hratio (pow_le_pow_left₀ (by positivity) hDle 5)
            (by positivity) (Shao.energy_nonneg u)
        _ = _ := mul_comm _ _
    · dsimp only [W]
      rw [if_neg hsel]
      positivity
  have hEnergyI (t : ℕ) : Integrable (Shao.energy : Shao.Path t → ℝ) (Pt t) := by
    change Integrable (fun u : Shao.Path t => ∑ i : Fin t, (u i) ^ 2) (Pt t)
    exact integrable_finsetSum _ fun i _ =>
      (measurePreserving_eval (μ := fun _ : Fin t => rho) i).integrable_comp_of_integrable h2
  have hWi (t : ℕ) : Integrable (W t) (Pt t) :=
    ((hEnergyI t).const_mul ((1 + Real.sqrt (t : ℝ)) ^ 5)).mono'
      (hWm t).aestronglyMeasurable (ae_of_all _ fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hW0 t u)]
        exact hWbound t u)
  let split : (r : Fin n) → Shao.Path n →
      Shao.Path r.val × Shao.Path (n - r.val) := fun r a =>
    (Shao.Probability.Spitzer.head a r.val r.is_lt.le,
     Shao.Probability.Spitzer.tail a r.val r.is_lt.le)
  have hSplit (r : Fin n) :
      MeasurePreserving (split r) P ((Pt r.val).prod (Pt (n - r.val))) := by
    let e : Fin r.val ⊕ Fin (n - r.val) ≃ Fin n :=
      finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le r.is_lt.le))
    have h1 := (measurePreserving_piCongrLeft (fun _ : Fin n => rho) e).symm
    have h2' := measurePreserving_sumPiEquivProdPi
      (fun _ : Fin r.val ⊕ Fin (n - r.val) => rho)
    convert h2'.comp h1 using 1
    ext a i <;> change a _ = a _ <;> congr 1
  let S : (r : Fin n) → Shao.Path n → Shao.Path (n - r.val) :=
    fun r a => (split r a).2
  have hTail (r : Fin n) : MeasurePreserving (S r) P (Pt (n - r.val)) := by
    letI := hPt r.val
    exact (measurePreserving_snd (μ := Pt r.val) (ν := Pt (n - r.val))).comp (hSplit r)
  let L : Fin n → Shao.Path n → ℝ := fun r a =>
    if n / 2 < r.val then W (n - r.val) (S r a) else 0
  have hLm (r : Fin n) : Measurable (L r) := by
    by_cases hr : n / 2 < r.val
    · simpa only [L, if_pos hr, Function.comp_def] using
        (hWm (n - r.val)).comp (hTail r).measurable
    · simpa only [L, if_neg hr] using
        (measurable_const : Measurable (fun _ : Shao.Path n => (0 : ℝ)))
  have hLi (r : Fin n) : Integrable (L r) P := by
    by_cases hr : n / 2 < r.val
    · simpa only [L, if_pos hr, Function.comp_def] using
        (hTail r).integrable_comp_of_integrable (hWi (n - r.val))
    · simpa only [L, if_neg hr] using
        (integrable_const (0 : ℝ) : Integrable (fun _ : Shao.Path n => (0 : ℝ)) P)
  have hLtail (r : Fin n) : (∫ a, L r a ∂P) =
      if n / 2 < r.val then ∫ u, W (n - r.val) u ∂Pt (n - r.val) else 0 := by
    by_cases hr : n / 2 < r.val
    · simp only [L, if_pos hr]
      have he := integral_map (μ := P) (φ := S r) (f := W (n - r.val))
        (hTail r).measurable.aemeasurable (hWm _).aestronglyMeasurable
      rw [(hTail r).map_eq] at he
      exact he.symm
    · simp only [L, if_neg hr, integral_zero]
  let R : Fin n → Shao.Path n → ℝ := fun r a =>
    if n / 2 < r.val ∧ h0 ≤ Shao.energy (S r a) ∧
        (Shao.energy (S r a) < H ∨ n - r.val ≤ m) then
      Shao.Probability.SourceIIDGaussianProfileBudget.rankGaussianWeight h0 x {s} false a r
    else 0
  have hRank (r : Fin n) : Measurable (R r) ∧ Integrable (R r) P ∧
      (∀ a, 0 ≤ R r a) ∧
      (∫ a, R r a ∂P) ≤ (2 * CL / (n : ℝ)) * ∫ a, L r a ∂P := by
    let Pr : Measure (Shao.Path r.val) := Pt r.val
    let Ps : Measure (Shao.Path (n - r.val)) := Pt (n - r.val)
    let F : Shao.Path r.val × Shao.Path (n - r.val) → ℝ := fun p =>
      if n / 2 < r.val ∧ h0 ≤ Shao.energy p.2 ∧
          (Shao.energy p.2 < H ∨ n - r.val ≤ m) then
        Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight
          h0 x {s} false p.1 p.2
      else 0
    have hdata :=
      Shao.Probability.SourceIIDGaussianProfileBudget.fixed_gaussian_weight_measurable_bound
        r.val (n - r.val) h0 x {s} false
    have hguard : MeasurableSet {p : Shao.Path r.val × Shao.Path (n - r.val) |
        n / 2 < r.val ∧ h0 ≤ Shao.energy p.2 ∧
          (Shao.energy p.2 < H ∨ n - r.val ≤ m)} := by
      have hE := Shao.measurable_energy.comp
        (measurable_snd : Measurable (Prod.snd : Shao.Path r.val × Shao.Path (n - r.val) → _))
      by_cases hr : n / 2 < r.val
      · by_cases ht : n - r.val ≤ m
        · simpa only [hr, ht, or_true, and_true, true_and, Function.comp_def] using
            measurableSet_le measurable_const hE
        · simpa only [hr, ht, or_false, true_and, Set.setOf_and, Function.comp_def] using
            (measurableSet_le measurable_const hE).inter (measurableSet_lt hE measurable_const)
      · simp only [hr, false_and, Set.setOf_false]
        exact MeasurableSet.empty
    have hFm : Measurable F := Measurable.ite hguard hdata.1 measurable_const
    have hF0 (p : Shao.Path r.val × Shao.Path (n - r.val)) : 0 ≤ F p := by
      dsimp only [F]
      split_ifs
      · exact (hdata.2.1 p.1 p.2).1
      · exact le_rfl
    have hFb (p : Shao.Path r.val × Shao.Path (n - r.val)) :
        |F p| ≤ (1 + Real.sqrt ((n - r.val : ℕ) : ℝ)) ^ 3 := by
      dsimp only [F]
      split_ifs
      · simpa only [Finset.card_singleton, Nat.cast_one, one_mul] using
          (hdata.2.1 p.1 p.2).2
      · simp only [abs_zero]
        positivity
    have hFi : Integrable F (Pr.prod Ps) :=
      (integrable_const ((1 + Real.sqrt ((n - r.val : ℕ) : ℝ)) ^ 3)).mono'
        hFm.aestronglyMeasurable
        (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hFb p)
    have hRsplit : R r = fun a => F (split r a) := by rfl
    have hRm : Measurable (R r) := by
      rw [hRsplit]
      exact hFm.comp (hSplit r).measurable
    have hRi : Integrable (R r) P := by
      rw [hRsplit]
      exact (hSplit r).integrable_comp_of_integrable hFi
    have hEq : (∫ a, R r a ∂P) = ∫ u, (∫ v, F (v, u) ∂Pr) ∂Ps := by
      rw [hRsplit]
      have he := integral_map (μ := P) (φ := split r) (f := F)
        (hSplit r).measurable.aemeasurable hFm.aestronglyMeasurable
      rw [(hSplit r).map_eq] at he
      exact he.symm.trans (integral_prod_symm _ hFi)
    refine ⟨hRm, hRi, (fun a => hF0 (split r a)), ?_⟩
    rw [hEq, hLtail]
    by_cases hr : n / 2 < r.val
    · rw [if_pos hr]
      have hr0 : 0 < r.val := by omega
      have hrR : 0 < (r.val : ℝ) := by exact_mod_cast hr0
      have hn2r : n ≤ 2 * r.val := by omega
      have hn2rR : (n : ℝ) ≤ 2 * (r.val : ℝ) := by exact_mod_cast hn2r
      have hcoeff : CL / (r.val : ℝ) ≤ 2 * CL / (n : ℝ) := by
        apply (div_le_div_iff₀ hrR hnR).2
        calc
          CL * (n : ℝ) ≤ CL * (2 * (r.val : ℝ)) :=
            mul_le_mul_of_nonneg_left hn2rR hCL.le
          _ = (2 * CL) * (r.val : ℝ) := by ring
      have hinner (u : Shao.Path (n - r.val)) :
          (∫ v, F (v, u) ∂Pr) ≤ (2 * CL / (n : ℝ)) * W (n - r.val) u := by
        by_cases hsel : h0 ≤ Shao.energy u ∧
            (Shao.energy u < H ∨ n - r.val ≤ m)
        · have hT : 0 < Shao.energy u := hh0.trans_le hsel.1
          have hcut : 0 < Shao.energy u ∧ h0 ≤ Shao.energy u := ⟨hT, hsel.1⟩
          have hf := hLateFixed rho Bcap hBcap hsupport hmean hsecond n hn x hx hscale
            r.val (n - r.val) (Nat.add_sub_of_le r.is_lt.le).symm hr0 hn2r
            u h0 hh0 (le_refl _) s hs
          have hFval : (fun v : Shao.Path r.val => F (v, u)) = fun v =>
              Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight
                h0 x {s} false v u := by
            funext v
            exact if_pos ⟨hr, hsel⟩
          have hWval : W (n - r.val) u =
              if 0 < Shao.energy u ∧ h0 ≤ Shao.energy u then
                |Shao.Probability.SourceIIDGaussianProfileBudget.firstValue u| ^ 3 /
                  Real.sqrt (Shao.energy u) *
                    Shao.Probability.SourceMarkedSuffixAveraging.suffixD u ^ 5
              else 0 := by
            simp only [W, if_pos hsel, if_pos hcut,
              Shao.Probability.SourceMarkedSuffixAveraging.suffixD, if_pos hT]
          rw [hFval]
          calc
            _ ≤ (CL / (r.val : ℝ)) * W (n - r.val) u := by
              rw [hWval]
              exact hf.2
            _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (hW0 _ u)
        · have hFzero : (fun v : Shao.Path r.val => F (v, u)) = fun _ => 0 := by
            funext v
            exact if_neg (by tauto)
          rw [hFzero, integral_zero]
          exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hCL.le) hnR.le) (hW0 _ u)
      have hi := integral_mono hFi.integral_prod_right
        ((hWi (n - r.val)).const_mul (2 * CL / (n : ℝ))) hinner
      simpa only [integral_const_mul, Ps] using hi
    · have hFzero : F = fun _ => 0 := by
        funext p
        exact if_neg (by tauto)
      simp only [hFzero, integral_zero, if_neg hr, mul_zero, le_refl]
  let G : Shao.Path n → ℝ := fun a => ∑ r : Fin n, R r a
  let J : Shao.Path n → ℝ := fun a => ∑ r : Fin n, L r a
  have hGm : Measurable G := Finset.measurable_sum _ fun r _ => (hRank r).1
  have hGi : Integrable G P := integrable_finsetSum _ fun r _ => (hRank r).2.1
  have hJm : Measurable J := Finset.measurable_sum _ fun r _ => hLm r
  have hJi : Integrable J P := integrable_finsetSum _ fun r _ => hLi r
  -- The entire reordered path and the exact mask are transported jointly.
  let reorder : Shao.Path n × LabelPerm n → Shao.Path n :=
    fun p => Shao.Probability.Spitzer.reorder p.1 p.2
  have hReorderM : Measurable reorder := by
    apply measurable_from_prod_countable_left
    intro sigma
    exact Measurable.of_eval fun i => measurable_pi_apply (sigma i)
  have hMap : Measure.map reorder (revealLaw P) = P := by
    have hInd : iIndepFun (fun i : Fin n => Function.eval i) P :=
      iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)
    have hLaw (i : Fin n) : IdentDistrib (Function.eval i) (id : ℝ → ℝ) P rho :=
      ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable,
        by simp only [Measure.map_id]
           exact (measurePreserving_eval (μ := fun _ : Fin n => rho) i).map_eq⟩
    exact iid_randomPermutation_map_eq_pi P rho (fun i : Fin n => Function.eval i)
      (fun i => measurable_pi_apply i) hInd hLaw
  have hMP : MeasurePreserving reorder (revealLaw P) P := ⟨hReorderM, hMap⟩
  have hState (r : Fin n) (p : Shao.Path n × LabelPerm n) :
      Shao.energy (S r (reorder p)) = remainingEnergy p.1 r.val p.2 ∧
      Shao.prefixSum (S r (reorder p)) (n - r.val) = remainingSum p.1 r.val p.2 ∧
      Shao.Probability.SourceIIDGaussianProfileBudget.firstValue (S r (reorder p)) =
        p.1 (p.2 r) := by
    have hh := Shao.Probability.SourceIIDGaussianProfileBudget.gaussian_weight_source_state
      (reorder p) r h0 x {s} false
    have hEnergy : Shao.energy (reorder p) = Shao.energy p.1 := by
      exact Equiv.sum_comp p.2 (fun i => p.1 i ^ 2)
    have hSum : Shao.prefixSum (reorder p) n = Shao.prefixSum p.1 n := by
      simpa only [Shao.prefixSum_length, reorder, Shao.Probability.Spitzer.reorder]
        using Equiv.sum_comp p.2 p.1
    exact ⟨by simpa only [S, split, remainingEnergy, hEnergy] using hh.1,
      by simpa only [S, split, remainingSum, hSum] using hh.2.1,
      hh.2.2.2.1⟩
  have hMask (r : Fin n) (p : Shao.Path n × LabelPerm n) :
      (n / 2 < r.val ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2) ↔
        n / 2 < r.val ∧ h0 ≤ Shao.energy (S r (reorder p)) ∧
          (Shao.energy (S r (reorder p)) < H ∨ n - r.val ≤ m) := by
    rw [(hState r p).1]
    exact and_congr_right fun _ => arr_omitted_mask_iff p.1 h0 H hh0 hH p.2 r m
  have hBillEq : bill = fun p => G (reorder p) := by
    funext p
    change (∑ r : Fin n, if n / 2 < r.val ∧ tau p.1 p.2 ≤ r.val ∧
        r.val < nu p.1 p.2 then
      Shao.Probability.SourceIIDGaussianProfileBudget.rankGaussianWeight
        h0 x {s} false (reorder p) r else 0) = ∑ r : Fin n, R r (reorder p)
    apply Finset.sum_congr rfl
    intro r _
    dsimp only [R]
    simp only [hMask r p]
  have hBillM : Measurable bill := by
    rw [hBillEq]
    exact hGm.comp hReorderM
  have hBillI : Integrable bill (revealLaw P) := by
    rw [hBillEq]
    exact hMP.integrable_comp_of_integrable hGi
  have hBill0 (p : Shao.Path n × LabelPerm n) : 0 ≤ bill p := by
    rw [hBillEq]
    exact Finset.sum_nonneg fun r _ => (hRank r).2.2.1 (reorder p)
  let actualW : (Shao.Path n × LabelPerm n) → Fin n → ℝ := fun p r =>
    |p.1 (p.2 r)| ^ 3 / Real.sqrt (remainingEnergy p.1 r.val p.2) *
      (1 + |remainingSum p.1 r.val p.2| /
        Real.sqrt (remainingEnergy p.1 r.val p.2)) ^ 5
  let lateW : Shao.Path n × LabelPerm n → ℝ := fun p =>
    (1 / (n : ℝ)) * ∑ r : Fin n,
      if n / 2 < r.val ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2
      then actualW p r else 0
  have hWeight (r : Fin n) (p : Shao.Path n × LabelPerm n) :
      |Shao.Probability.SourceIIDGaussianProfileBudget.firstValue (S r (reorder p))| ^ 3 /
          Real.sqrt (Shao.energy (S r (reorder p))) *
        (1 + |Shao.prefixSum (S r (reorder p)) (n - r.val)| /
          Real.sqrt (Shao.energy (S r (reorder p)))) ^ 5 = actualW p r := by
    rw [(hState r p).1, (hState r p).2.1, (hState r p).2.2]
  have hLateEq (p : Shao.Path n × LabelPerm n) :
      lateW p = (1 / (n : ℝ)) * J (reorder p) := by
    apply congrArg (fun z : ℝ => (1 / (n : ℝ)) * z)
    apply Finset.sum_congr rfl
    intro r _
    change (if n / 2 < r.val ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then
        actualW p r else 0) =
      (if n / 2 < r.val then W (n - r.val) (S r (reorder p)) else 0)
    simp only [hMask r p]
    dsimp only [W]
    rw [hWeight]
    by_cases hr : n / 2 < r.val <;>
      by_cases hsel : h0 ≤ Shao.energy (S r (reorder p)) ∧
          (Shao.energy (S r (reorder p)) < H ∨ n - r.val ≤ m) <;>
      simp only [hr, hsel, true_and, false_and, if_true, if_false]
  have hOld := hPay rho h2 h3 hmean hsecond n hn x hx hres
  change Measurable lateW ∧ Integrable lateW (revealLaw P) ∧
    (∫ p, lateW p ∂revealLaw P) ≤ CW * beta * Real.sqrt H / (n : ℝ) ∧
    (∫ p, lateW p ∂revealLaw P) ≤ CW * delta * Shao.standardNormalTail x at hOld
  have hPaid : (∫ p, lateW p ∂revealLaw P) =
      (1 / (n : ℝ)) * ∑ r : Fin n, ∫ a, L r a ∂P := by
    calc
      _ = ∫ p, (1 / (n : ℝ)) * J (reorder p) ∂revealLaw P :=
        integral_congr_ae (ae_of_all _ hLateEq)
      _ = (1 / (n : ℝ)) * ∫ p, J (reorder p) ∂revealLaw P := integral_const_mul _ _
      _ = (1 / (n : ℝ)) * ∫ a, J a ∂P := by
        have he := integral_map (μ := revealLaw P) (φ := reorder) (f := J)
          hReorderM.aemeasurable hJm.aestronglyMeasurable
        rw [hMap] at he
        exact congrArg (fun z : ℝ => (1 / (n : ℝ)) * z) he.symm
      _ = _ := by
        dsimp only [J]
        rw [integral_finsetSum _ (fun r _ => hLi r)]
  have hBound : (∫ p, bill p ∂revealLaw P) ≤
      (2 * CL) * ∫ p, lateW p ∂revealLaw P := by
    calc
      _ = ∫ a, G a ∂P := by
        rw [hBillEq]
        have he := integral_map (μ := revealLaw P) (φ := reorder) (f := G)
          hReorderM.aemeasurable hGm.aestronglyMeasurable
        rw [hMap] at he
        exact he.symm
      _ = ∑ r : Fin n, ∫ a, R r a ∂P :=
        integral_finsetSum _ (fun r _ => (hRank r).2.1)
      _ ≤ ∑ r : Fin n, (2 * CL / (n : ℝ)) * ∫ a, L r a ∂P :=
        Finset.sum_le_sum fun r _ => (hRank r).2.2.2
      _ = (2 * CL) * ((1 / (n : ℝ)) * ∑ r : Fin n, ∫ a, L r a ∂P) := by
        rw [← Finset.mul_sum]
        ring
      _ = _ := by rw [hPaid]
  refine ⟨hBillM, hBillI, hBill0, ?_, ?_⟩
  · calc
      _ ≤ (2 * CL) * ∫ p, lateW p ∂revealLaw P := hBound
      _ ≤ (2 * CL) * (CW * beta * Real.sqrt H / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hOld.2.2.1 (by positivity)
      _ = C * beta * Real.sqrt H / (n : ℝ) := by dsimp only [C]; ring
  · calc
      _ ≤ (2 * CL) * ∫ p, lateW p ∂revealLaw P := hBound
      _ ≤ (2 * CL) * (CW * delta * Shao.standardNormalTail x) :=
        mul_le_mul_of_nonneg_left hOld.2.2.2 (by positivity)
      _ = C * delta * Shao.standardNormalTail x := by dsimp only [C]; ring

theorem iid_actual_entire_omitted_retained_budget :
    let K : ℝ := (2 : ℝ) ^ 64
    ∃ C : ℝ, 0 < C ∧
      ∀ {ΩB : Type*} [MeasurableSpace ΩB]
        (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (Bm : ℝ≥0 → ΩB → ℝ), IsBrownianReal Bm PB →
        let Q : Measure BridgeNoise := bridgeLaw Bm PB
        ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
          (Bcap : ℝ), 0 < Bcap → (∀ᵐ z : ℝ ∂rho, |z| ≤ Bcap) →
          (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
          ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), 16 ≤ x →
            Bcap ≤ Real.sqrt (n : ℝ) / (100 * x) →
            let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
            let delta : ℝ := beta / Real.sqrt (n : ℝ)
            delta * (1 + x) ^ 3 ≤ Real.exp (-3 * x ^ 2) →
            let h0 : ℝ := 4 * beta ^ 2
            let H : ℝ := K * beta ^ 2 * (1 + x) ^ 6
            let m : ℕ := ⌈H⌉₊
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
            let nu : Shao.Path n → LabelPerm n → ℕ :=
              fun a sigma => energyCutoff a h0 sigma
            let tau : Shao.Path n → LabelPerm n → ℕ := fun a sigma =>
              min (energyCutoff a H sigma) (n - m)
            let bill := actualOmittedRetainedBill Q x nu tau
            Measurable bill ∧ Integrable bill (revealLaw P) ∧
              (∀ p, 0 ≤ bill p) ∧
              (∫ p, bill p ∂revealLaw P) ≤ C * beta * Real.sqrt H / (n : ℝ) ∧
              (∫ p, bill p ∂revealLaw P) ≤ C * delta * Shao.standardNormalTail x := by
  classical
  intro K
  obtain ⟨Ce, hCe, hEarly⟩ :=
    Shao.Probability.SourceEarlyRetainedProbability.iid_actual_early_rare_and_omitted_retained_budget
  obtain ⟨Cg, hCg, hLate⟩ := arr_iid_late_omitted_gaussian_bill
  let Cphys : ℝ := 8000100 + (2 * Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant + 40)
  let C : ℝ := 1 + Ce + 2 * Cphys * Cg
  have hCP := Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant_nonneg
  have hCphys : 0 < Cphys := by dsimp [Cphys]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro ΩB mΩB PB hPB Bm hBm Q rho hrho Bcap hBcap hBound hmean hsecond
    n hn x hx hSupport beta delta hsmall h0 H m P nu tau bill
  letI : IsProbabilityMeasure rho := hrho
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw Bm PB hBm
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  letI : IsProbabilityMeasure (revealLaw P) := by unfold revealLaw; infer_instance
  have hxpos : 0 < x := by linarith only [hx]
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.2 hn
  have h2 : Integrable (fun z : ℝ => z ^ 2) rho := by
    refine (integrable_const (Bcap ^ 2)).mono' (by fun_prop) ?_
    filter_upwards [hBound] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z) hz 2
  have h3 : Integrable (fun z : ℝ => |z| ^ 3) rho := by
    refine (integrable_const (Bcap ^ 3)).mono' (by fun_prop) ?_
    filter_upwards [hBound] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ |z| ^ 3)]
    exact pow_le_pow_left₀ (abs_nonneg z) hz 3
  have hbeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one rho h2 h3 hsecond
  have hbetaPos : 0 < beta := lt_of_lt_of_le zero_lt_one hbeta
  have hh0 : 0 < h0 := by dsimp [h0]; positivity
  have hK4 : 4 ≤ K := by norm_num [K]
  have hx6 : 1 ≤ (1 + x) ^ 6 := one_le_pow₀ (by linarith only [hx] : 1 ≤ 1 + x)
  have hh0H : h0 ≤ H := by
    have h1 := mul_le_mul_of_nonneg_right hK4 (sq_nonneg beta)
    have h2 := mul_le_mul_of_nonneg_left hx6
      (mul_nonneg (by norm_num [K] : 0 ≤ K) (sq_nonneg beta))
    dsimp only [h0, H]
    nlinarith only [h1, h2]
  have hH : 0 < H := hh0.trans_le hh0H
  have hnu (sigma : LabelPerm n) : Measurable (fun a => nu a sigma) :=
    Shao.Probability.SourceActualLocalProfileBudget.actual_energy_cutoff_measurable h0 hh0 sigma
  have htau (sigma : LabelPerm n) : Measurable (fun a => tau a sigma) :=
    (Shao.Probability.SourceActualLocalProfileBudget.actual_energy_cutoff_measurable H hH sigma).min
      measurable_const
  have hnum : Measurable (fun p : Shao.Path n × LabelPerm n => nu p.1 p.2) := by
    apply measurable_from_prod_countable_left
    exact hnu
  have htaum : Measurable (fun p : Shao.Path n × LabelPerm n => tau p.1 p.2) := by
    apply measurable_from_prod_countable_left
    exact htau
  have hRank (r : Fin n) := arr_absolute_rank_measurable_integrable
    PB Bm hBm P x hxpos nu hnu r
  have hMask (r : Fin n) : MeasurableSet {p : Shao.Path n × LabelPerm n |
      tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2} :=
    (measurableSet_le htaum measurable_const).inter
      (measurableSet_lt measurable_const hnum)
  have hRm (r : Fin n) : Measurable (fun p : Shao.Path n × LabelPerm n =>
      if tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then
        actualRetainedAbsoluteRank Q p.1 x (nu p.1) r p.2 else 0) :=
    Measurable.ite (hMask r) (hRank r).1 measurable_const
  have hRi (r : Fin n) : Integrable (fun p : Shao.Path n × LabelPerm n =>
      if tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then
        actualRetainedAbsoluteRank Q p.1 x (nu p.1) r p.2 else 0) (revealLaw P) := by
    refine (hRank r).2.1.mono' (hRm r).aestronglyMeasurable (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs]
    split_ifs
    · exact (abs_of_nonneg ((hRank r).2.2.1 p)).le
    · rw [abs_zero]
      exact (hRank r).2.2.1 p
  have hBillM : Measurable bill := by
    exact Finset.measurable_sum _ (fun r _ => hRm r)
  have hBillI : Integrable bill (revealLaw P) := by
    exact integrable_finsetSum _ (fun r _ => hRi r)
  have hBillNN (p : Shao.Path n × LabelPerm n) : 0 ≤ bill p := by
    apply Finset.sum_nonneg
    intro r _
    split_ifs
    · exact (hRank r).2.2.1 p
    · exact le_rfl
  let early : Shao.Path n × LabelPerm n → ℝ := fun p =>
    ∑ r : Fin n, if r.val ≤ n / 2 ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then
      actualRetainedAbsoluteRank Q p.1 x (nu p.1) r p.2 else 0
  let lateProfile : ℝ → Shao.Path n × LabelPerm n → ℝ := fun s p =>
    ∑ r : Fin n, if n / 2 < r.val ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then
      Shao.Probability.SourceIIDGaussianProfileBudget.rankGaussianWeight h0 x {s} false
        (Shao.Probability.Spitzer.reorder p.1 p.2) r else 0
  have hE := hEarly PB Bm hBm rho Bcap hBcap hBound hmean hsecond n hn x hx hsmall
  rcases hE with ⟨_hRareM, _hRareI, hEm0, hEi0, _hRareB, hEB0, hET0⟩
  have hEm : Measurable early := by
    simpa only [early, actualRetainedAbsoluteRank, actualDerivativeFamily] using hEm0
  have hEi : Integrable early (revealLaw P) := by
    simpa only [early, actualRetainedAbsoluteRank, actualDerivativeFamily] using hEi0
  have hEB : (∫ p, early p ∂revealLaw P) ≤ Ce * beta * Real.sqrt H / (n : ℝ) := by
    simpa only [early, actualRetainedAbsoluteRank, actualDerivativeFamily] using hEB0
  have hET : (∫ p, early p ∂revealLaw P) ≤ Ce * delta * Shao.standardNormalTail x := by
    simpa only [early, actualRetainedAbsoluteRank, actualDerivativeFamily] using hET0
  have hG (s : ℝ) (hs : s = 1 ∨ s = -1) :
      Measurable (lateProfile s) ∧ Integrable (lateProfile s) (revealLaw P) ∧
      (∀ p, 0 ≤ lateProfile s p) ∧
      (∫ p, lateProfile s p ∂revealLaw P) ≤ Cg * beta * Real.sqrt H / (n : ℝ) ∧
      (∫ p, lateProfile s p ∂revealLaw P) ≤ Cg * delta * Shao.standardNormalTail x := by
    simpa only [lateProfile] using
      hLate rho Bcap hBcap hBound hmean hsecond n hn x hx hSupport hsmall s hs
  have hGp := hG 1 (Or.inl rfl)
  have hGm := hG (-1) (Or.inr rfl)
  have hDom (p : Shao.Path n × LabelPerm n) :
      bill p ≤ early p + Cphys * (lateProfile 1 p + lateProfile (-1) p) := by
    calc
      bill p ≤ ∑ r : Fin n,
          ((if r.val ≤ n / 2 ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then
            actualRetainedAbsoluteRank Q p.1 x (nu p.1) r p.2 else 0) +
          Cphys * ((if n / 2 < r.val ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then
            Shao.Probability.SourceIIDGaussianProfileBudget.rankGaussianWeight h0 x {1} false
              (Shao.Probability.Spitzer.reorder p.1 p.2) r else 0) +
            (if n / 2 < r.val ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 then
            Shao.Probability.SourceIIDGaussianProfileBudget.rankGaussianWeight h0 x {-1} false
              (Shao.Probability.Spitzer.reorder p.1 p.2) r else 0))) := by
        apply Finset.sum_le_sum
        intro r _
        by_cases hsel : tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2
        · by_cases he : r.val ≤ n / 2
          · have hl : ¬(n / 2 < r.val ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2) :=
              fun hh => (not_lt.mpr he) hh.1
            simp only [if_pos hsel, if_pos (show r.val ≤ n / 2 ∧ tau p.1 p.2 ≤ r.val ∧
              r.val < nu p.1 p.2 from ⟨he, hsel⟩), if_neg hl, add_zero, mul_zero, le_refl]
          · have hl : n / 2 < r.val := Nat.lt_of_not_ge he
            have hne : ¬(r.val ≤ n / 2 ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2) :=
              fun hh => he hh.1
            have hd := (actual_retained_absolute_rank_gaussian_domination PB Bm hBm
              p.1 h0 x hh0 hxpos (nu p.1) p.2 le_rfl r).2
            simpa only [if_pos hsel, if_neg hne,
              if_pos (show n / 2 < r.val ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2 from
                ⟨hl, hsel⟩), zero_add, Cphys] using hd
        · have he : ¬(r.val ≤ n / 2 ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2) :=
            fun hh => hsel hh.2
          have hl : ¬(n / 2 < r.val ∧ tau p.1 p.2 ≤ r.val ∧ r.val < nu p.1 p.2) :=
            fun hh => hsel hh.2
          simp only [if_neg hsel, if_neg he, if_neg hl, add_zero, mul_zero, le_refl]
      _ = early p + Cphys * (lateProfile 1 p + lateProfile (-1) p) := by
        simp only [early, lateProfile, Finset.sum_add_distrib, Finset.mul_sum, mul_add]
  have hGPi := hGp.2.1
  have hGMi := hGm.2.1
  have hi : (∫ p, bill p ∂revealLaw P) ≤ (∫ p, early p ∂revealLaw P) +
      Cphys * ((∫ p, lateProfile 1 p ∂revealLaw P) +
        (∫ p, lateProfile (-1) p ∂revealLaw P)) := by
    calc
      _ ≤ ∫ p, early p + Cphys * (lateProfile 1 p + lateProfile (-1) p) ∂revealLaw P :=
        integral_mono hBillI (hEi.add ((hGPi.add hGMi).const_mul Cphys)) hDom
      _ = _ := by
        have hsumI : Integrable
            (fun p => lateProfile 1 p + lateProfile (-1) p) (revealLaw P) := by
          simpa only [Pi.add_apply] using hGPi.add hGMi
        have hmulI : Integrable
            (fun p => Cphys * (lateProfile 1 p + lateProfile (-1) p)) (revealLaw P) :=
          hsumI.const_mul Cphys
        rw [integral_add (f := early)
          (g := fun p => Cphys * (lateProfile 1 p + lateProfile (-1) p)) hEi hmulI,
          integral_const_mul]
        exact congrArg (fun z : ℝ => (∫ p, early p ∂revealLaw P) + Cphys * z)
          (integral_add hGPi hGMi)
  have hCoeff : Ce + 2 * Cphys * Cg ≤ C := by dsimp [C]; linarith
  have hdelta : 0 ≤ delta := div_nonneg hbetaPos.le (Real.sqrt_nonneg _)
  have hTail : 0 ≤ Shao.standardNormalTail x := ((Shao.standardNormalTail_basic).2.2.1 x).1.le
  refine ⟨hBillM, hBillI, hBillNN, ?_, ?_⟩
  · calc
      _ ≤ Ce * beta * Real.sqrt H / (n : ℝ) + Cphys *
          (Cg * beta * Real.sqrt H / (n : ℝ) + Cg * beta * Real.sqrt H / (n : ℝ)) :=
        hi.trans (add_le_add hEB (mul_le_mul_of_nonneg_left
          (add_le_add hGp.2.2.2.1 hGm.2.2.2.1) hCphys.le))
      _ = (Ce + 2 * Cphys * Cg) * beta * Real.sqrt H / (n : ℝ) := by ring
      _ ≤ C * beta * Real.sqrt H / (n : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCoeff hbetaPos.le) (Real.sqrt_nonneg H)) hnR.le
  · calc
      _ ≤ Ce * delta * Shao.standardNormalTail x + Cphys *
          (Cg * delta * Shao.standardNormalTail x + Cg * delta * Shao.standardNormalTail x) :=
        hi.trans (add_le_add hET (mul_le_mul_of_nonneg_left
          (add_le_add hGp.2.2.2.2 hGm.2.2.2.2) hCphys.le))
      _ = (Ce + 2 * Cphys * Cg) * delta * Shao.standardNormalTail x := by ring
      _ ≤ C * delta * Shao.standardNormalTail x :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCoeff hdelta) hTail

theorem iid_actual_bad_retained_allranks_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ΩB : Type*} [MeasurableSpace ΩB]
        (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (Bm : ℝ≥0 → ΩB → ℝ), IsBrownianReal Bm PB →
        let Q : Measure BridgeNoise := bridgeLaw Bm PB
        ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
          (Bcap : ℝ), 0 < Bcap → (∀ᵐ z : ℝ ∂rho, |z| ≤ Bcap) →
          (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
          ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), 16 ≤ x →
            Bcap ≤ Real.sqrt (n : ℝ) / (100 * x) →
            let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
            let delta : ℝ := beta / Real.sqrt (n : ℝ)
            delta * (1 + x) ^ 3 ≤ Real.exp (-3 * x ^ 2) →
            let h0 : ℝ := 4 * beta ^ 2
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
            ∀ (nu : Shao.Path n → LabelPerm n → ℕ),
              (∀ sigma, Measurable (fun a => nu a sigma)) →
              (∀ a sigma, nu a sigma ≤ energyCutoff a h0 sigma) →
              let bill := actualBadRetainedBill Q x nu
              Measurable bill ∧ Integrable bill (revealLaw P) ∧
                (∀ p, 0 ≤ bill p) ∧
                (∫ p, bill p ∂revealLaw P) ≤ C * delta * Shao.standardNormalTail x := by
  classical
  obtain ⟨CL, hCL, hLateFixed⟩ := arr_late_fixed_suffix_gaussian_bound
  obtain ⟨CR, hCR, hRare⟩ :=
    Shao.Probability.SourceResidualRareSuffix.iid_marked_and_unmarked_rare_real_suffix_budgets 5
  let Cphys : ℝ := 8000100 +
    (2 * Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant + 40)
  have hCphys : 0 < Cphys := by
    have hh := Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant_nonneg
    dsimp [Cphys]
    positivity
  let C : ℝ := (16 + 4 * CL) * Cphys * CR + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro ΩB hΩB PB hPB Bm hBm Q rho hProb Bcap hBcap hsupport hmean hsecond
    n hn x hx hscale beta delta hres h0 P nu hnum hnu bill
  letI : IsProbabilityMeasure rho := hProb
  letI : IsProbabilityMeasure PB := hPB
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  letI : IsProbabilityMeasure (revealLaw P) := by unfold revealLaw; infer_instance
  have hx0 : 0 < x := by linarith only [hx]
  let Ax : ℝ := Real.sqrt (Shao.standardNormalTail (3 * x / 2)) + Real.exp (-x ^ 2)
  let Pt : (t : ℕ) → Measure (Shao.Path t) :=
    fun t => Measure.pi (fun _ : Fin t => rho)
  let Tt : (t : ℕ) → Shao.Path t → ℝ := fun _ => Shao.energy
  let dt : (t : ℕ) → Shao.Path t → ℝ := fun t a => Shao.prefixSum a t
  let M : (t : ℕ) → Shao.Path t → ℝ := fun t a =>
    if ht : 0 < t then |a ⟨0, ht⟩| ^ 3 else 0
  let Dt : (t : ℕ) → Shao.Path t → ℝ := fun t a =>
    if 0 < Tt t a then 1 + |dt t a| / Real.sqrt (Tt t a) else 1
  let marked : ℕ → (t : ℕ) → Shao.Path t → ℝ := fun q t a =>
    if 0 < Tt t a ∧ h0 ≤ Tt t a ∧
        (3 * x / 2) * Real.sqrt (Tt t a) ≤ |dt t a| then
      M t a / (Real.sqrt (Tt t a)) ^ q * Dt t a ^ 5 else 0
  have hrare := hRare rho Bcap hBcap hsupport hmean hsecond n hn x hx hres
  rcases hrare with ⟨hBetaR, hh0R, hhH, hm4, hmh, hmn, hInt, hPoint,
    hEarlyGrid, hLateGrid, hFutureInt, hFutureBound⟩
  have hbeta : 1 ≤ beta := hBetaR
  have hh0 : 0 < h0 := hh0R
  have hdelta : 0 ≤ delta := by dsimp [delta]; positivity
  have htail : 0 ≤ Shao.standardNormalTail x :=
    (Shao.standardNormalTail_basic.2.2.1 x).1.le
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmarkedInt (t q : ℕ) (hq : q = 1 ∨ q = 3) :
      Integrable (marked q t) (Pt t) := by
    simpa only [marked, M, Dt, Tt, dt, Pt, h0] using (hInt t q hq).1
  have hmarked0 (q t : ℕ) (a : Shao.Path t) : 0 ≤ marked q t a := by
    dsimp [marked, M, Dt]
    split_ifs <;> positivity
  have hmarkValue (q t : ℕ) (u : Shao.Path t) :
      marked q t u =
        if 0 < Shao.energy u ∧ h0 ≤ Shao.energy u ∧
            (3 * x / 2) * Real.sqrt (Shao.energy u) ≤ |Shao.prefixSum u t| then
          |Shao.Probability.SourceIIDGaussianProfileBudget.firstValue u| ^ 3 /
            (Real.sqrt (Shao.energy u)) ^ q *
              Shao.Probability.SourceMarkedSuffixAveraging.suffixD u ^ 5
        else 0 := by
    have hM : M t u =
        |Shao.Probability.SourceIIDGaussianProfileBudget.firstValue u| ^ 3 := by
      by_cases ht : 0 < t
      · simp only [M, Shao.Probability.SourceIIDGaussianProfileBudget.firstValue,
          dif_pos ht]
      · simp only [M, Shao.Probability.SourceIIDGaussianProfileBudget.firstValue,
          dif_neg ht, abs_zero, zero_pow (by norm_num : (3 : ℕ) ≠ 0)]
    dsimp only [marked, Tt, dt]
    rw [hM]
    rfl
  let E : ℕ → ℝ := fun t => ∫ u, marked 3 t u ∂Pt t
  let L : ℕ → ℝ := fun t => ∫ u, marked 1 t u ∂Pt t
  have hE0 (t : ℕ) : 0 ≤ E t := integral_nonneg (hmarked0 3 t)
  have hL0 (t : ℕ) : 0 ≤ L t := integral_nonneg (hmarked0 1 t)
  have hEarlyPay : (∑ t ∈ Finset.Icc ((n + 1) / 2) n, E t) ≤ CR * delta * Ax := by
    simpa only [E, marked, M, Dt, Tt, dt, Pt, h0, Ax] using hEarlyGrid
  have hLatePay : (1 / (n : ℝ)) * (∑ t ∈ Finset.Icc 1 (n / 2), L t) ≤
      CR * delta * Shao.standardNormalTail x := by
    simpa only [L, marked, M, Dt, Tt, dt, Pt, h0] using hLateGrid
  -- Genuine integrability of the literal source bill is established before transport.
  let term : Fin n → (Shao.Path n × LabelPerm n) → ℝ := fun r p =>
    if (3 * x / 2) * Real.sqrt (remainingEnergy p.1 r.val p.2) ≤
        |remainingSum p.1 r.val p.2| then
      actualRetainedAbsoluteRank Q p.1 x (nu p.1) r p.2 else 0
  have htermData (r : Fin n) : Measurable (term r) ∧
      Integrable (term r) (revealLaw P) ∧ ∀ p, 0 ≤ term r p := by
    have habs := arr_absolute_rank_measurable_integrable PB Bm hBm P x hx0 nu hnum r
    have hT : Measurable (fun p : Shao.Path n × LabelPerm n =>
        remainingEnergy p.1 r.val p.2) := by
      apply measurable_from_prod_countable_left
      intro sigma
      exact Shao.measurable_energy.sub ((Shao.measurable_prefixSquares r.val).comp
        (Measurable.of_eval fun i =>
          measurable_pi_apply (X := fun _ : Fin n => ℝ) (sigma i)))
    have hd : Measurable (fun p : Shao.Path n × LabelPerm n =>
        remainingSum p.1 r.val p.2) := by
      apply measurable_from_prod_countable_left
      intro sigma
      exact (Shao.measurable_prefixSum n).sub ((Shao.measurable_prefixSum r.val).comp
        (Measurable.of_eval fun i =>
          measurable_pi_apply (X := fun _ : Fin n => ℝ) (sigma i)))
    have hm : Measurable (term r) :=
      Measurable.ite (measurableSet_le (measurable_const.mul hT.sqrt)
        (continuous_abs.measurable.comp hd)) habs.1 measurable_const
    have hnn (p : Shao.Path n × LabelPerm n) : 0 ≤ term r p := by
      dsimp only [term]
      split_ifs
      · exact habs.2.2.1 p
      · exact le_rfl
    have hb (p : Shao.Path n × LabelPerm n) :
        term r p ≤ 3 + 88 * (1 + (n : ℝ)) := by
      dsimp only [term]
      split_ifs
      · exact habs.2.2.2 p
      · positivity
    refine ⟨hm, ?_, hnn⟩
    exact (integrable_const (3 + 88 * (1 + (n : ℝ)))).mono'
      hm.aestronglyMeasurable (ae_of_all _ fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hnn p)]
        exact hb p)
  have hbill : Measurable bill ∧ Integrable bill (revealLaw P) ∧ ∀ p, 0 ≤ bill p := by
    refine ⟨?_, ?_, ?_⟩
    · change Measurable (fun p => ∑ r : Fin n, term r p)
      exact Finset.measurable_sum _ fun r _ => (htermData r).1
    · change Integrable (fun p => ∑ r : Fin n, term r p) (revealLaw P)
      exact integrable_finsetSum _ fun r _ => (htermData r).2.1
    · intro p
      exact Finset.sum_nonneg fun r _ => (htermData r).2.2 p
  -- One singleton Gaussian carrier costs the exact marked q=3, p=5 weight.
  have hEarlyFixed {r t : ℕ} (v : Shao.Path r) (u : Shao.Path t) (s : ℝ) :
      (if (3 * x / 2) * Real.sqrt (Shao.energy u) ≤ |Shao.prefixSum u t| then
        Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight
          h0 x {s} false v u else 0) ≤ marked 3 t u := by
    rw [hmarkValue]
    by_cases hbad : (3 * x / 2) * Real.sqrt (Shao.energy u) ≤ |Shao.prefixSum u t|
    · rw [if_pos hbad]
      by_cases hcut : 0 < Shao.energy u ∧ h0 ≤ Shao.energy u
      · rw [if_pos ⟨hcut.1, hcut.2, hbad⟩]
        let D : ℝ := Shao.Probability.SourceMarkedSuffixAveraging.suffixD u
        have hD : 1 ≤ D :=
          (Shao.Probability.SourceMarkedSuffixAveraging.suffix_normalized_geometry u).2.2.2.2.2.1.1
        have hD0 : 0 ≤ D := (by norm_num : (0 : ℝ) ≤ 1).trans hD
        have hD2 : 1 ≤ D ^ 2 := by nlinarith only [hD]
        have hD35 : D ^ 3 ≤ D ^ 5 := by
          calc
            _ = D ^ 3 * 1 := by ring
            _ ≤ D ^ 3 * D ^ 2 :=
              mul_le_mul_of_nonneg_left hD2 (pow_nonneg hD0 3)
            _ = _ := by ring
        have hden : (Real.sqrt (Shao.energy u)) ^ 3 =
            Shao.energy u * Real.sqrt (Shao.energy u) := by
          calc
            _ = (Real.sqrt (Shao.energy u)) ^ 2 * Real.sqrt (Shao.energy u) := by ring
            _ = _ := by rw [Real.sq_sqrt hcut.1.le]
        have hA0 : 0 ≤
            |Shao.Probability.SourceIIDGaussianProfileBudget.firstValue u| ^ 3 /
              (Shao.energy u * Real.sqrt (Shao.energy u)) := by
          exact div_nonneg (pow_nonneg (abs_nonneg _) 3)
            (mul_nonneg hcut.1.le (Real.sqrt_nonneg _))
        have hPi : Shao.Probability.SourceIIDGaussianProfileBudget.gaussianProfiles
            x {s} v u ≤ 1 := by
          simp only [Shao.Probability.SourceIIDGaussianProfileBudget.gaussianProfiles,
            if_pos hcut.1, Finset.sum_singleton]
          exact Real.exp_le_one_iff.2
            (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) hcut.1.le)
        unfold Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight
        split_ifs with hactive
        · calc
            _ ≤ (|Shao.Probability.SourceIIDGaussianProfileBudget.firstValue u| ^ 3 /
                (Shao.energy u * Real.sqrt (Shao.energy u)) * D ^ 3) * 1 :=
              mul_le_mul_of_nonneg_left hPi (mul_nonneg hA0 (pow_nonneg hD0 3))
            _ ≤ |Shao.Probability.SourceIIDGaussianProfileBudget.firstValue u| ^ 3 /
                (Shao.energy u * Real.sqrt (Shao.energy u)) * D ^ 5 := by
              simpa only [mul_one] using mul_le_mul_of_nonneg_left hD35 hA0
            _ = _ := by rw [hden]
        · positivity
      · have hncut : ¬(0 < Shao.energy u ∧ h0 ≤ Shao.energy u ∧
            (3 * x / 2) * Real.sqrt (Shao.energy u) ≤ |Shao.prefixSum u t|) := by tauto
        rw [if_neg hncut]
        unfold Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight
        rw [if_neg (by tauto)]
    · have hnmark : ¬(0 < Shao.energy u ∧ h0 ≤ Shao.energy u ∧
          (3 * x / 2) * Real.sqrt (Shao.energy u) ≤ |Shao.prefixSum u t|) := by
        tauto
      simp only [if_neg hbad, if_neg hnmark, le_refl]
  -- The cap-free carrier retains the complete pre-label tail and weak Bad event.
  let R : Fin n → Shao.Path n → ℝ := fun r a =>
    if (3 * x / 2) * Real.sqrt (remainingEnergy a r.val (Equiv.refl (Fin n))) ≤
        |remainingSum a r.val (Equiv.refl (Fin n))| then
      Shao.Probability.SourceIIDGaussianProfileBudget.rankGaussianWeight h0 x {1} false a r +
      Shao.Probability.SourceIIDGaussianProfileBudget.rankGaussianWeight h0 x {-1} false a r
    else 0
  have hRank (r : Fin n) : Measurable (R r) ∧ Integrable (R r) P ∧
      (∫ a, R r a ∂P) ≤
        if r.val ≤ n / 2 then 2 * E (n - r.val)
        else (4 * CL / (n : ℝ)) * L (n - r.val) := by
    let Pr : Measure (Shao.Path r.val) := Pt r.val
    let Ps : Measure (Shao.Path (n - r.val)) := Pt (n - r.val)
    let split : Shao.Path n → Shao.Path r.val × Shao.Path (n - r.val) := fun a =>
      (Shao.Probability.Spitzer.head a r.val r.is_lt.le,
       Shao.Probability.Spitzer.tail a r.val r.is_lt.le)
    have hsplit : MeasurePreserving split P (Pr.prod Ps) := by
      let e : Fin r.val ⊕ Fin (n - r.val) ≃ Fin n :=
        finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le r.is_lt.le))
      have h1 := (measurePreserving_piCongrLeft (fun _ : Fin n => rho) e).symm
      have h2 := measurePreserving_sumPiEquivProdPi
        (fun _ : Fin r.val ⊕ Fin (n - r.val) => rho)
      convert h2.comp h1 using 1
      ext a i <;> change a _ = a _ <;> congr 1
    let F : Shao.Path r.val × Shao.Path (n - r.val) → ℝ := fun p =>
      if (3 * x / 2) * Real.sqrt (Shao.energy p.2) ≤
          |Shao.prefixSum p.2 (n - r.val)| then
        Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight
          h0 x {1} false p.1 p.2 +
        Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight
          h0 x {-1} false p.1 p.2
      else 0
    have hplus := Shao.Probability.SourceIIDGaussianProfileBudget.fixed_gaussian_weight_measurable_bound
      r.val (n - r.val) h0 x {1} false
    have hminus := Shao.Probability.SourceIIDGaussianProfileBudget.fixed_gaussian_weight_measurable_bound
      r.val (n - r.val) h0 x {-1} false
    have hFm : Measurable F :=
      Measurable.ite (measurableSet_le
        (measurable_const.mul (Shao.measurable_energy.comp measurable_snd).sqrt)
        (continuous_abs.measurable.comp
          ((Shao.measurable_prefixSum (n - r.val)).comp measurable_snd)))
        (hplus.1.add hminus.1) measurable_const
    have hF0 (p : Shao.Path r.val × Shao.Path (n - r.val)) : 0 ≤ F p := by
      dsimp only [F]
      split_ifs
      · exact add_nonneg (hplus.2.1 p.1 p.2).1 (hminus.2.1 p.1 p.2).1
      · exact le_rfl
    have hFb (p : Shao.Path r.val × Shao.Path (n - r.val)) :
        |F p| ≤ 2 * (1 + Real.sqrt ((n - r.val : ℕ) : ℝ)) ^ 3 := by
      dsimp only [F]
      split_ifs
      · have hp := (hplus.2.1 p.1 p.2).2
        have hm := (hminus.2.1 p.1 p.2).2
        have hh := (abs_add_le
          (Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {1} false p.1 p.2)
          (Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {-1} false p.1 p.2)).trans
          (add_le_add hp hm)
        simpa only [Finset.card_singleton, Nat.cast_one, one_mul, ← two_mul] using hh
      · simp only [abs_zero]
        positivity
    have hFi : Integrable F (Pr.prod Ps) :=
      (integrable_const (2 * (1 + Real.sqrt ((n - r.val : ℕ) : ℝ)) ^ 3)).mono'
        hFm.aestronglyMeasurable
        (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hFb p)
    have hFsectioni (u : Shao.Path (n - r.val)) :
        Integrable (fun v => F (v, u)) Pr :=
      (integrable_const (2 * (1 + Real.sqrt ((n - r.val : ℕ) : ℝ)) ^ 3)).mono'
        (hFm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        (ae_of_all _ fun v => by simpa only [Real.norm_eq_abs] using hFb (v, u))
    have hRsplit : R r = fun a => F (split a) := by
      funext a
      have hs := Shao.Probability.SourceIIDGaussianProfileBudget.gaussian_weight_source_state
        a r h0 x {1} false
      have hT : remainingEnergy a r.val (Equiv.refl (Fin n)) =
          Shao.energy (Shao.Probability.Spitzer.tail a r.val r.is_lt.le) := hs.1.symm
      have hd : remainingSum a r.val (Equiv.refl (Fin n)) =
          Shao.prefixSum (Shao.Probability.Spitzer.tail a r.val r.is_lt.le) (n - r.val) := hs.2.1.symm
      dsimp only [R, F, split, Shao.Probability.SourceIIDGaussianProfileBudget.rankGaussianWeight]
      rw [hT, hd]
    have hRm : Measurable (R r) := by
      rw [hRsplit]
      exact hFm.comp hsplit.measurable
    have hRi : Integrable (R r) P := by
      rw [hRsplit]
      exact hsplit.integrable_comp_of_integrable hFi
    have hEq : (∫ a, R r a ∂P) =
        ∫ u, (∫ v, F (v, u) ∂Pr) ∂Ps := by
      rw [hRsplit]
      have he := integral_map (μ := P) (φ := split) (f := F)
        hsplit.measurable.aemeasurable hFm.aestronglyMeasurable
      rw [hsplit.map_eq] at he
      exact he.symm.trans (integral_prod_symm _ hFi)
    have hinnerInt : Integrable (fun u => ∫ v, F (v, u) ∂Pr) Ps :=
      hFi.integral_prod_right
    refine ⟨hRm, hRi, ?_⟩
    rw [hEq]
    by_cases hearly : r.val ≤ n / 2
    · rw [if_pos hearly]
      have hp (u : Shao.Path (n - r.val)) :
          (∫ v, F (v, u) ∂Pr) ≤ 2 * marked 3 (n - r.val) u := by
        have hpoint (v : Shao.Path r.val) : F (v, u) ≤ 2 * marked 3 (n - r.val) u := by
          have hp := hEarlyFixed v u 1
          have hm := hEarlyFixed v u (-1)
          have hh := add_le_add hp hm
          dsimp only [F]
          split_ifs with hbad
          · simpa only [if_pos hbad, ← two_mul] using hh
          · exact mul_nonneg (by norm_num) (hmarked0 _ _ _)
        calc
          _ ≤ ∫ _v : Shao.Path r.val, 2 * marked 3 (n - r.val) u ∂Pr :=
            integral_mono (hFsectioni u) (integrable_const _) hpoint
          _ = _ := by simp [Pr, Pt]
      have hi := integral_mono hinnerInt
        ((hmarkedInt (n - r.val) 3 (Or.inr rfl)).const_mul 2) hp
      simpa only [integral_const_mul, Ps, E] using hi
    · rw [if_neg hearly]
      have hr0 : 0 < r.val := by omega
      have hrR : 0 < (r.val : ℝ) := by exact_mod_cast hr0
      have hn2r : n ≤ 2 * r.val := by omega
      have hn2rR : (n : ℝ) ≤ 2 * (r.val : ℝ) := by exact_mod_cast hn2r
      have hcoeff : 2 * (CL / (r.val : ℝ)) ≤ 4 * CL / (n : ℝ) := by
        have hh : CL / (r.val : ℝ) ≤ (2 * CL) / (n : ℝ) := by
          apply (div_le_div_iff₀ hrR hnR).2
          calc
            CL * (n : ℝ) ≤ CL * (2 * (r.val : ℝ)) :=
              mul_le_mul_of_nonneg_left hn2rR hCL.le
            _ = (2 * CL) * (r.val : ℝ) := by ring
        calc
          _ ≤ 2 * ((2 * CL) / (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2)
          _ = _ := by ring
      have hp (u : Shao.Path (n - r.val)) :
          (∫ v, F (v, u) ∂Pr) ≤
            (4 * CL / (n : ℝ)) * marked 1 (n - r.val) u := by
        have hlp := hLateFixed rho Bcap hBcap hsupport hmean hsecond n hn x hx hscale
          r.val (n - r.val) (Nat.add_sub_of_le r.is_lt.le).symm hr0 hn2r
          u h0 hh0 (le_refl _) 1 (Or.inl rfl)
        have hlm := hLateFixed rho Bcap hBcap hsupport hmean hsecond n hn x hx hscale
          r.val (n - r.val) (Nat.add_sub_of_le r.is_lt.le).symm hr0 hn2r
          u h0 hh0 (le_refl _) (-1) (Or.inr rfl)
        by_cases hbad : (3 * x / 2) * Real.sqrt (Shao.energy u) ≤
            |Shao.prefixSum u (n - r.val)|
        · have hmark : marked 1 (n - r.val) u =
              if 0 < Shao.energy u ∧ h0 ≤ Shao.energy u then
                |Shao.Probability.SourceIIDGaussianProfileBudget.firstValue u| ^ 3 /
                  Real.sqrt (Shao.energy u) *
                    Shao.Probability.SourceMarkedSuffixAveraging.suffixD u ^ 5
              else 0 := by
            rw [hmarkValue]
            simp only [hbad, and_true, pow_one]
          have hFadd : (fun v : Shao.Path r.val => F (v, u)) = fun v =>
              Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {1} false v u +
              Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {-1} false v u := by
            funext v
            exact if_pos hbad
          rw [hFadd, integral_add hlp.1 hlm.1]
          calc
            _ ≤ 2 * (CL / (r.val : ℝ)) * marked 1 (n - r.val) u := by
              have hh := add_le_add hlp.2 hlm.2
              rw [hmark] at ⊢
              convert hh using 1 <;> ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (hmarked0 _ _ _)
        · have hzero : (fun v : Shao.Path r.val => F (v, u)) = fun _ => 0 := by
            funext v
            exact if_neg hbad
          rw [hzero, integral_zero]
          exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hCL.le) hnR.le)
            (hmarked0 _ _ _)
      have hi := integral_mono hinnerInt
        ((hmarkedInt (n - r.val) 1 (Or.inl rfl)).const_mul (4 * CL / (n : ℝ))) hp
      simpa only [integral_const_mul, Ps, L] using hi
  let G : Shao.Path n → ℝ := fun a => ∑ r : Fin n, R r a
  have hGm : Measurable G := Finset.measurable_sum _ fun r _ => (hRank r).1
  have hGi : Integrable G P := integrable_finsetSum _ fun r _ => (hRank r).2.1
  -- Remove arbitrary cap dependence pointwise, before the iid whole-path map.
  have hperm (a : Shao.Path n) (sigma : LabelPerm n) :
      Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) n = Shao.prefixSum a n ∧
      Shao.energy (Shao.Probability.Spitzer.reorder a sigma) = Shao.energy a := by
    constructor
    · simpa only [Shao.prefixSum_length, Shao.Probability.Spitzer.reorder]
        using Equiv.sum_comp sigma a
    · exact Equiv.sum_comp sigma (fun i => a i ^ 2)
  have hdom (p : Shao.Path n × LabelPerm n) : bill p ≤ Cphys * G (randomReorder p) := by
    change (∑ r : Fin n, term r p) ≤ Cphys * ∑ r : Fin n, R r (randomReorder p)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    have hT : remainingEnergy (randomReorder p) r.val (Equiv.refl (Fin n)) =
        remainingEnergy p.1 r.val p.2 := by
      change Shao.energy (randomReorder p) -
          Shao.prefixSquares (randomReorder p) r.val =
        Shao.energy p.1 - Shao.prefixSquares (randomReorder p) r.val
      exact congrArg
        (fun z : ℝ => z - Shao.prefixSquares (randomReorder p) r.val)
        (hperm p.1 p.2).2
    have hd : remainingSum (randomReorder p) r.val (Equiv.refl (Fin n)) =
        remainingSum p.1 r.val p.2 := by
      change Shao.prefixSum (randomReorder p) n -
          Shao.prefixSum (randomReorder p) r.val =
        Shao.prefixSum p.1 n - Shao.prefixSum (randomReorder p) r.val
      exact congrArg
        (fun z : ℝ => z - Shao.prefixSum (randomReorder p) r.val)
        (hperm p.1 p.2).1
    dsimp only [term, R]
    rw [hT, hd]
    by_cases hbad : (3 * x / 2) * Real.sqrt (remainingEnergy p.1 r.val p.2) ≤
        |remainingSum p.1 r.val p.2|
    · rw [if_pos hbad, if_pos hbad]
      exact (actual_retained_absolute_rank_gaussian_domination
        PB Bm hBm p.1 h0 x hh0 hx0 (nu p.1) p.2 (hnu p.1 p.2) r).2
    · simp only [if_neg hbad, mul_zero, le_refl]
  have hRm : Measurable (randomReorder : Shao.Path n × LabelPerm n → Shao.Path n) :=
    measurable_from_prod_countable_left (fun sigma => by
      apply Measurable.of_eval
      intro i
      exact measurable_pi_apply (sigma i))
  have hmap : Measure.map randomReorder (revealLaw P) = P := by
    have hInd : iIndepFun (fun i : Fin n => Function.eval i) P :=
      iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)
    have hLaw (i : Fin n) : IdentDistrib (Function.eval i) (id : ℝ → ℝ) P rho :=
      ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable,
        by simp only [Measure.map_id]
           exact (measurePreserving_eval (μ := fun _ : Fin n => rho) i).map_eq⟩
    exact iid_randomPermutation_map_eq_pi P rho (fun i : Fin n => Function.eval i)
      (fun i => measurable_pi_apply i) hInd hLaw
  have hmp : MeasurePreserving randomReorder (revealLaw P) P := ⟨hRm, hmap⟩
  have hreduce : (∫ p, bill p ∂revealLaw P) ≤ Cphys * ∫ a, G a ∂P := by
    calc
      _ ≤ ∫ p, Cphys * G (randomReorder p) ∂revealLaw P :=
        integral_mono hbill.2.1
          ((hmp.integrable_comp_of_integrable hGi).const_mul Cphys) hdom
      _ = Cphys * ∫ p, G (randomReorder p) ∂revealLaw P := integral_const_mul _ _
      _ = _ := by
        have hi := integral_map (μ := revealLaw P) hRm.aemeasurable hGm.aestronglyMeasurable
        rw [hmap] at hi
        exact congrArg (fun z : ℝ => Cphys * z) hi.symm
  -- The two rank sets inject into the inclusive rare-producer grids, for both parities.
  have hgrid :
      (∑ r : Fin n, if r.val ≤ n / 2 then E (n - r.val) else 0) ≤
          (∑ t ∈ Finset.Icc ((n + 1) / 2) n, E t) ∧
      (∑ r : Fin n, if n / 2 < r.val then L (n - r.val) else 0) ≤
          (∑ t ∈ Finset.Icc 1 (n / 2), L t) := by
    have hinj : Function.Injective (fun r : Fin n => n - r.val) := by
      intro a b he
      change n - a.val = n - b.val at he
      apply Fin.ext
      have ha := a.is_lt
      have hb := b.is_lt
      omega
    have hEarly : ((Finset.univ.filter (fun r : Fin n => r.val ≤ n / 2)).image
        (fun r => n - r.val)) ⊆ Finset.Icc ((n + 1) / 2) n := by
      intro t ht
      rcases Finset.mem_image.mp ht with ⟨r, hr, rfl⟩
      have hh := (Finset.mem_filter.mp hr).2
      have hrn := r.is_lt
      simp only [Finset.mem_Icc]
      omega
    have hLate : ((Finset.univ.filter (fun r : Fin n => n / 2 < r.val)).image
        (fun r => n - r.val)) ⊆ Finset.Icc 1 (n / 2) := by
      intro t ht
      rcases Finset.mem_image.mp ht with ⟨r, hr, rfl⟩
      have hh := (Finset.mem_filter.mp hr).2
      have hrn := r.is_lt
      simp only [Finset.mem_Icc]
      omega
    constructor
    · rw [← Finset.sum_filter]
      calc
        _ = ∑ t ∈ (Finset.univ.filter (fun r : Fin n => r.val ≤ n / 2)).image
            (fun r => n - r.val), E t := by
          rw [Finset.sum_image]
          exact fun a _ b _ he => hinj he
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hEarly (fun t _ _ => hE0 t)
    · rw [← Finset.sum_filter]
      calc
        _ = ∑ t ∈ (Finset.univ.filter (fun r : Fin n => n / 2 < r.val)).image
            (fun r => n - r.val), L t := by
          rw [Finset.sum_image]
          exact fun a _ b _ he => hinj he
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hLate (fun t _ _ => hL0 t)
  have hsumBound : (∫ a, G a ∂P) ≤
      2 * (∑ t ∈ Finset.Icc ((n + 1) / 2) n, E t) +
        (4 * CL) * ((1 / (n : ℝ)) * ∑ t ∈ Finset.Icc 1 (n / 2), L t) := by
    change (∫ a, ∑ r : Fin n, R r a ∂P) ≤ _
    rw [integral_finsetSum _ (fun r _ => (hRank r).2.1)]
    calc
      _ ≤ ∑ r : Fin n, if r.val ≤ n / 2 then 2 * E (n - r.val)
          else (4 * CL / (n : ℝ)) * L (n - r.val) :=
        Finset.sum_le_sum fun r _ => (hRank r).2.2
      _ = 2 * (∑ r : Fin n, if r.val ≤ n / 2 then E (n - r.val) else 0) +
          (4 * CL / (n : ℝ)) *
            (∑ r : Fin n, if n / 2 < r.val then L (n - r.val) else 0) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r _
        by_cases hh : r.val ≤ n / 2
        · simp only [if_pos hh, if_neg (by omega : ¬n / 2 < r.val), mul_zero, add_zero]
        · simp only [if_neg hh, if_pos (by omega : n / 2 < r.val), mul_zero, zero_add]
      _ ≤ _ := by
        have he := mul_le_mul_of_nonneg_left hgrid.1 (by norm_num : (0 : ℝ) ≤ 2)
        have hl := mul_le_mul_of_nonneg_left hgrid.2
          (show 0 ≤ 4 * CL / (n : ℝ) from
            div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hCL.le) hnR.le)
        calc
          _ ≤ 2 * (∑ t ∈ Finset.Icc ((n + 1) / 2) n, E t) +
              (4 * CL / (n : ℝ)) * (∑ t ∈ Finset.Icc 1 (n / 2), L t) :=
            add_le_add he hl
          _ = _ := by ring
  -- This is the qualified H18 numerical proof, copied locally rather than using a private name.
  have hGaussian : Ax ≤ 8 * Shao.standardNormalTail x := by
    have hx0' : 0 ≤ x := hx0.le
    have hpoly : 1 + x ≤ Real.exp (x ^ 2 / 8) := by
      calc
        1 + x ≤ 1 + x ^ 2 / 8 := by
          nlinarith [mul_nonneg hx0' (show 0 ≤ x - 8 by linarith)]
        _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (x ^ 2 / 8)
    have hrev : (1 / 2 : ℝ) ≤
        (4 / 3 : ℝ) * (1 + x) * Real.exp (x ^ 2 / 2) * Shao.standardNormalTail x := by
      simpa only [Shao.standardNormalTail_basic.2.1,
        zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, div_one, sub_zero] using
          Shao.standardNormalTail_ratio_bound x 0 hx0' (by norm_num)
    have hrevB : (1 / 2 : ℝ) ≤
        (4 / 3 : ℝ) * Real.exp (5 * x ^ 2 / 8) * Shao.standardNormalTail x := by
      apply hrev.trans
      calc
        _ ≤ (4 / 3 : ℝ) * Real.exp (x ^ 2 / 8) * Real.exp (x ^ 2 / 2) *
            Shao.standardNormalTail x := by gcongr
        _ = _ := by rw [mul_assoc (4 / 3 : ℝ), ← Real.exp_add]; congr 2; ring
    have hNeg : Real.exp (-5 * x ^ 2 / 8) ≤ (8 / 3 : ℝ) * Shao.standardNormalTail x := by
      have hh := mul_le_mul_of_nonneg_left hrevB (Real.exp_nonneg (-5 * x ^ 2 / 8))
      have he : Real.exp (-5 * x ^ 2 / 8) * Real.exp (5 * x ^ 2 / 8) = 1 := by
        rw [← Real.exp_add]
        convert Real.exp_zero using 1 <;> ring
      have hh' : Real.exp (-5 * x ^ 2 / 8) * (1 / 2 : ℝ) ≤
          (4 / 3 : ℝ) * Shao.standardNormalTail x := by
        calc
          _ ≤ Real.exp (-5 * x ^ 2 / 8) *
              ((4 / 3 : ℝ) * Real.exp (5 * x ^ 2 / 8) * Shao.standardNormalTail x) := hh
          _ = (4 / 3 : ℝ) *
              (Real.exp (-5 * x ^ 2 / 8) * Real.exp (5 * x ^ 2 / 8)) *
                Shao.standardNormalTail x := by ring
          _ = _ := by rw [he]; ring
      linarith only [hh']
    have hratio : (1 + x) / (1 + 3 * x / 2) ≤ (1 : ℝ) := by
      apply (div_le_one (by positivity)).2
      linarith only [hx0']
    have hforward : Shao.standardNormalTail (3 * x / 2) ≤
        (4 / 3 : ℝ) * Real.exp (-5 * x ^ 2 / 8) * Shao.standardNormalTail x := by
      have hh := Shao.standardNormalTail_ratio_bound x (3 * x / 2) hx0' (by positivity)
      have he : (x ^ 2 - (3 * x / 2) ^ 2) / 2 = -5 * x ^ 2 / 8 := by ring
      rw [he] at hh
      apply hh.trans
      calc
        _ ≤ (4 / 3 : ℝ) * 1 * Real.exp (-5 * x ^ 2 / 8) * Shao.standardNormalTail x := by gcongr
        _ = _ := by ring
    have hsquare : Shao.standardNormalTail (3 * x / 2) ≤
        (2 * Shao.standardNormalTail x) ^ 2 := by
      have hh := mul_le_mul_of_nonneg_right hNeg htail
      nlinarith [sq_nonneg (Shao.standardNormalTail x)]
    have hsqrt : Real.sqrt (Shao.standardNormalTail (3 * x / 2)) ≤
        2 * Shao.standardNormalTail x := (Real.sqrt_le_iff).2 ⟨by positivity, hsquare⟩
    have hsmall : Real.exp (-x ^ 2) ≤ (8 / 3 : ℝ) * Shao.standardNormalTail x :=
      (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x] :
        -x ^ 2 ≤ -5 * x ^ 2 / 8)).trans hNeg
    dsimp only [Ax]
    nlinarith only [hsqrt, hsmall, htail]
  refine ⟨hbill.1, hbill.2.1, hbill.2.2, ?_⟩
  calc
    _ ≤ Cphys * ∫ a, G a ∂P := hreduce
    _ ≤ Cphys *
        (2 * (∑ t ∈ Finset.Icc ((n + 1) / 2) n, E t) +
          (4 * CL) * ((1 / (n : ℝ)) * ∑ t ∈ Finset.Icc 1 (n / 2), L t)) :=
      mul_le_mul_of_nonneg_left hsumBound hCphys.le
    _ ≤ Cphys * (2 * (CR * delta * Ax) +
        (4 * CL) * (CR * delta * Shao.standardNormalTail x)) := by
      apply mul_le_mul_of_nonneg_left _ hCphys.le
      exact add_le_add (mul_le_mul_of_nonneg_left hEarlyPay (by norm_num))
        (mul_le_mul_of_nonneg_left hLatePay (mul_nonneg (by norm_num) hCL.le))
    _ ≤ Cphys * (2 * (CR * delta * (8 * Shao.standardNormalTail x)) +
        (4 * CL) * (CR * delta * Shao.standardNormalTail x)) := by
      apply mul_le_mul_of_nonneg_left _ hCphys.le
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hGaussian (mul_nonneg hCR.le hdelta))
          (by norm_num : (0 : ℝ) ≤ 2)) _
    _ = ((16 + 4 * CL) * Cphys * CR) * delta * Shao.standardNormalTail x := by ring
    _ ≤ C * delta * Shao.standardNormalTail x := by
      have hh := mul_le_mul_of_nonneg_right
        (show (16 + 4 * CL) * Cphys * CR ≤ C by dsimp [C]; linarith)
        (mul_nonneg hdelta htail)
      convert hh using 1 <;> ring

end Shao.C2.ActualRetainedResidualBudgets
