import Shao.Probability.SourceActualRecordEndstrip
import Shao.Probability.SourceActualRecordLowFullEnergy
import Shao.Probability.SourceActualOrdinarySuffixWeight
import Shao.Probability.SourceWeightedRecordStrip
import Shao.Probability.SourceResidualRareSuffix
import Shao.Probability.SourceActualOmittedOvershoot
import Shao.C2.ActualOneWallRecordEnvelope
import Shao.C2.ActualDoubleSeparatedClassification
import Shao.C2.ActualBadIntervalNegativeBudget
import Shao.C2.BridgeIntervalImageResolved
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
noncomputable section
namespace Shao.Probability.SourceActualFullPositiveOvershoot
open MeasureTheory ProbabilityTheory
open SourcePermutationReveal SourceSeparatedOvershoot
open SourceActualLocalProfileBudget
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.ActualSignedDoubleTelescope
open scoped BigOperators Classical NNReal

local instance labelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

theorem iid_actual_full_signed_separated_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ΩB : Type*} [MeasurableSpace ΩB]
        (Bm : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
        IsBrownianReal Bm PB →
        let Q : Measure BridgeNoise := bridgeLaw Bm PB
        ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
          (Bcap : ℝ), 0 < Bcap → (∀ᵐ z : ℝ ∂rho, |z| ≤ Bcap) →
          (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), 16 ≤ x →
            Bcap ≤ Real.sqrt (n : ℝ) / (200 * x) →
            let delta : ℝ := beta / Real.sqrt (n : ℝ)
            delta * (1 + x) ^ 3 ≤ Real.exp (-3 * x ^ 2) →
            let h0 : ℝ := 4 * beta ^ 2
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
            ∀ (nu : Shao.Path n → LabelPerm n → ℕ),
              (∀ sigma : LabelPerm n, Measurable (fun a => nu a sigma)) →
              (∀ a sigma, nu a sigma ≤ energyCutoff a h0 sigma) →
              let bill : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
                ∑ r ∈ Finset.range n,
                  actualDoubleSeparated Q x p.1 (nu p.1) r p.2
              Measurable bill ∧ Integrable bill (revealLaw P) ∧
                (∀ p : Shao.Path n × LabelPerm n, 0 ≤ bill p) ∧
                (∫ p, bill p ∂revealLaw P) ≤
                  C * delta * Shao.standardNormalTail x
 := by
  classical
  have hIntegralAdd {A : Type} [MeasurableSpace A] {mu : Measure A}
      (f g : A → ℝ) (hf : Integrable f mu) (hg : Integrable g mu) :
      (∫ a, f a + g a ∂mu) = (∫ a, f a ∂mu) + (∫ a, g a ∂mu) :=
    integral_add hf hg
  obtain ⟨CK, hCK, hClass⟩ :=
    Shao.C2.ActualDoubleSeparatedClassification.actual_double_separated_three_bill
  obtain ⟨CN, hCN, hNegative⟩ :=
    Shao.C2.ActualBadIntervalNegativeBudget.actual_bad_interval_negative_budget
  -- Assemble the actual signed source from three positive budgets, all proved below.
  suffices hPositive :
      ∃ CO CP CB : ℝ, 0 < CO ∧ 0 < CP ∧ 0 < CB ∧
        ∀ {ΩB : Type _} [MeasurableSpace ΩB]
          (Bm : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
          IsBrownianReal Bm PB →
        ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
          (Bcap : ℝ), 0 < Bcap → (∀ᵐ z : ℝ ∂rho, |z| ≤ Bcap) →
          (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), 16 ≤ x →
            Bcap ≤ Real.sqrt (n : ℝ) / (200 * x) →
            let delta : ℝ := beta / Real.sqrt (n : ℝ)
            delta * (1 + x) ^ 3 ≤ Real.exp (-3 * x ^ 2) →
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
            ∀ (nu : Shao.Path n → LabelPerm n → ℕ),
              (∀ sigma : LabelPerm n, Measurable (fun a => nu a sigma)) →
              (∀ a sigma, nu a sigma ≤ energyCutoff a (4 * beta ^ 2) sigma) →
              let O : MonitoredDomain → ℕ → (Shao.Path n × LabelPerm n) → ℝ :=
                fun J r p => sourceSeparatedOvershoot J (halflineDerivative J)
                  p.1 x (nu p.1) r p.2
              let ordinary : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
                ∑ r ∈ Finset.range n, (O .upper r p + O .lower r p)
              let prior : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
                ∑ r : Fin n,
                  ((if Shao.C2.ActualOneWallRecordEnvelope.oppositePrefixHit
                    .upper p.1 x r p.2 then O .upper r.val p else 0) +
                  (if Shao.C2.ActualOneWallRecordEnvelope.oppositePrefixHit
                    .lower p.1 x r p.2 then O .lower r.val p else 0))
              let bad : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
                ∑ r ∈ Finset.range n,
                  if 3 * x * Real.sqrt (remainingEnergy p.1 r p.2) / 2 ≤
                      |remainingSum p.1 r p.2| then O .upper r p + O .lower r p else 0
              (∫ p, ordinary p ∂revealLaw P) ≤ CO * delta ∧
                (∫ p, prior p ∂revealLaw P) ≤ CP * delta * Shao.standardNormalTail x ∧
                (∫ p, bad p ∂revealLaw P) ≤ CB * delta * Shao.standardNormalTail x by
    rcases hPositive with ⟨CO, CP, CB, hCO, hCP, hCB, hPay⟩
    refine ⟨3 * CK * CO + CP + CB + CN, by positivity, ?_⟩
    intro ΩB instΩB Bm PB instPB hBm Q rho instRho Bcap hBcap hsupport
      hmean hsecond beta n hn x hx hBscale delta hres h0 P nu hnum hcap bill
    letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw Bm PB hBm
    letI : IsProbabilityMeasure (revealLaw P) := by unfold revealLaw; infer_instance
    have hx0 : 0 < x := by linarith only [hx]
    have hPower (r : ℕ) : Integrable (fun z : ℝ => |z| ^ r) rho := by
      apply (integrable_const (Bcap ^ r)).mono' (by fun_prop)
      filter_upwards [hsupport] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg z) r)]
      exact pow_le_pow_left₀ (abs_nonneg z) hz r
    have h2 : Integrable (fun z : ℝ => z ^ 2) rho := by
      simpa only [sq_abs] using hPower 2
    have hbeta1 : 1 ≤ beta :=
      Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one
        rho h2 (hPower 3) hsecond
    have hbeta : 0 < beta := lt_of_lt_of_le zero_lt_one hbeta1
    have hdelta : 0 ≤ delta := by dsimp only [delta]; positivity
    have hReflection : HalflineReflectionIdentities Q := by
      constructor
      · intro w y T z _hw hT hy hz
        simpa only [Shao.C2.HalfLineReflectionFormula.upperReflection] using
          Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula Bm PB hBm w y T z hT hy hz
      · intro w y T z _hw hT hy hz
        simpa only [Shao.C2.HalfLineReflectionFormula.lowerReflection] using
          Shao.C2.BridgeLowerIdentification.bridge_lower_formula Bm PB hBm w y T z hT hy hz
    have hRegular (w y T z : ℝ) (hw : 0 < w) (hT : 0 < T)
        (hy : |y| < w) (hz : |z| < w) :
        DifferentiableAt ℝ (fun s : ℝ =>
          Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w s T z) y :=
      (Shao.C2.BridgeIntervalImageResolved.sourceIntervalCompletion_spatial_hasDerivAt
        Bm PB hBm w y T z hw hy hz hT).differentiableAt
    have hData (J : MonitoredDomain) :
        Measurable (actualDerivativeFamily Q J) ∧
        KernelBounds J (eventCompletionKernel J Q) (actualDerivativeFamily Q J) 4 := by
      cases J with
      | upper => exact ⟨(actual_halfline_kernel_data Q hReflection .upper (Or.inl rfl)).1,
          (actual_halfline_kernel_data Q hReflection .upper (Or.inl rfl)).2.1⟩
      | lower => exact ⟨(actual_halfline_kernel_data Q hReflection .lower (Or.inr rfl)).1,
          (actual_halfline_kernel_data Q hReflection .lower (Or.inr rfl)).2.1⟩
      | interval => exact ⟨(SourceActualIntervalProfileBudget.actual_interval_kernel_data
          Q hReflection hRegular).1,
          (SourceActualIntervalProfileBudget.actual_interval_kernel_data
            Q hReflection hRegular).2.1⟩
    have hParts (J : MonitoredDomain) := source_parts_measurable_integrable J
      (eventCompletionKernel J Q) (actualDerivativeFamily Q J)
      (eventCompletionKernel_data J Q).1 (hData J).1 4 (hData J).2 P x hx0 nu hnum
    have hSepM (J : MonitoredDomain) (r : ℕ) :
        Measurable (fun p : Shao.Path n × LabelPerm n => sourceSeparatedOvershoot J
          (actualDerivativeFamily Q J) p.1 x (nu p.1) r p.2) := by
      apply measurable_from_prod_countable_left
      intro sigma
      exact ((hParts J).1 sigma r).2
    have hBillM : Measurable bill := by
      apply Finset.measurable_sum
      intro r _
      exact ((hSepM .upper r).add (hSepM .lower r)).sub (hSepM .interval r)
    have hBillI : Integrable bill (revealLaw P) := by
      apply integrable_finsetSum
      intro r _
      exact (((hParts .upper).2.1 r).2.add ((hParts .lower).2.1 r).2).sub
        ((hParts .interval).2.1 r).2
    have hReorderM : Measurable
        (randomReorder : Shao.Path n × LabelPerm n → Shao.Path n) := by
      apply measurable_from_prod_countable_left
      intro sigma
      exact Measurable.of_eval fun i => measurable_pi_apply (sigma i)
    have hRemainEM (r : ℕ) : Measurable (fun p : Shao.Path n × LabelPerm n =>
        remainingEnergy p.1 r p.2) :=
      (Shao.measurable_energy.comp measurable_fst).sub
        ((Shao.measurable_prefixSquares r).comp hReorderM)
    have hRemainSM (r : ℕ) : Measurable (fun p : Shao.Path n × LabelPerm n =>
        remainingSum p.1 r p.2) :=
      ((Shao.measurable_prefixSum n).comp measurable_fst).sub
        ((Shao.measurable_prefixSum r).comp hReorderM)
    have hBadM (r : ℕ) : MeasurableSet {p : Shao.Path n × LabelPerm n |
        3 * x * Real.sqrt (remainingEnergy p.1 r p.2) / 2 ≤
          |remainingSum p.1 r p.2|} :=
      measurableSet_le ((measurable_const.mul (hRemainEM r).sqrt).div_const 2)
        (continuous_abs.measurable.comp (hRemainSM r))
    have hOppM (J : MonitoredDomain) (r : Fin n) :
        MeasurableSet {p : Shao.Path n × LabelPerm n |
          Shao.C2.ActualOneWallRecordEnvelope.oppositePrefixHit J p.1 x r p.2} := by
      simp only [Shao.C2.ActualOneWallRecordEnvelope.oppositePrefixHit, Set.setOf_exists]
      apply MeasurableSet.iUnion
      intro k
      by_cases hk : k ≤ r.val
      · simp only [hk, true_and]
        exact measurableSet_le
          (measurable_const.mul ((Shao.measurable_prefixSum k).comp hReorderM))
          ((measurable_const.mul (Shao.measurable_energy.comp measurable_fst).sqrt).neg)
      · simp only [hk, false_and, Set.setOf_false, MeasurableSet.empty]
    let O : MonitoredDomain → ℕ → (Shao.Path n × LabelPerm n) → ℝ :=
      fun J r p => sourceSeparatedOvershoot J (halflineDerivative J) p.1 x (nu p.1) r p.2
    let ordinary : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
      ∑ r ∈ Finset.range n, (O .upper r p + O .lower r p)
    let prior : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
      ∑ r : Fin n,
        ((if Shao.C2.ActualOneWallRecordEnvelope.oppositePrefixHit .upper p.1 x r p.2
          then O .upper r.val p else 0) +
        (if Shao.C2.ActualOneWallRecordEnvelope.oppositePrefixHit .lower p.1 x r p.2
          then O .lower r.val p else 0))
    let bad : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
      ∑ r ∈ Finset.range n,
        if 3 * x * Real.sqrt (remainingEnergy p.1 r p.2) / 2 ≤
            |remainingSum p.1 r p.2| then O .upper r p + O .lower r p else 0
    let negative : (Shao.Path n × LabelPerm n) → ℝ :=
      Shao.C2.ActualBadIntervalNegativeBudget.actualBadIntervalNegativeBill Q x nu
    have hOI : Integrable ordinary (revealLaw P) := by
      apply integrable_finsetSum
      intro r _
      exact ((hParts .upper).2.1 r).2.add ((hParts .lower).2.1 r).2
    have hPI : Integrable prior (revealLaw P) := by
      apply integrable_finsetSum
      intro r _
      exact (((hParts .upper).2.1 r.val).2.indicator (hOppM .upper r)).add
        (((hParts .lower).2.1 r.val).2.indicator (hOppM .lower r))
    have hBI : Integrable bad (revealLaw P) := by
      apply integrable_finsetSum
      intro r _
      exact ((((hParts .upper).2.1 r).2.add ((hParts .lower).2.1 r).2).indicator (hBadM r))
    have hB100 : Bcap ≤ Real.sqrt (n : ℝ) / (100 * x) := by
      apply hBscale.trans
      apply (div_le_div_iff₀ (by positivity : 0 < 200 * x)
        (by positivity : 0 < 100 * x)).2
      have hh := mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hx0.le
      nlinarith only [hh]
    have hNeg := hNegative rho Bcap hBcap hsupport hmean hsecond n hn x hx hB100
      hres Bm PB hBm nu hnum hcap
    change Measurable negative ∧ Integrable negative (revealLaw P) ∧
      0 ≤ (∫ p, negative p ∂revealLaw P) ∧
      (∫ p, negative p ∂revealLaw P) ≤ CN * delta * Shao.standardNormalTail x at hNeg
    have hPos := hPay Bm PB hBm rho Bcap hBcap hsupport hmean hsecond n hn x hx hBscale
      hres nu hnum hcap
    change (∫ p, ordinary p ∂revealLaw P) ≤ CO * delta ∧
      (∫ p, prior p ∂revealLaw P) ≤ CP * delta * Shao.standardNormalTail x ∧
      (∫ p, bad p ∂revealLaw P) ≤ CB * delta * Shao.standardNormalTail x at hPos
    have hNonneg (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower)
        (r : Fin n) (p : Shao.Path n × LabelPerm n) : 0 ≤ O J r.val p :=
      (Shao.C2.ActualOneWallRecordEnvelope.actual_onewall_record_envelope
        J hJ p.1 x beta hx0 hbeta (nu p.1) r p.2 (hcap p.1 p.2)).1
    have hNotLower (p : Shao.Path n × LabelPerm n) (r : Fin n) :
        (¬Shao.C2.ActualDoubleSeparatedClassification.prefixAlive .lower p.1 x r.val p.2) ↔
          Shao.C2.ActualOneWallRecordEnvelope.oppositePrefixHit .upper p.1 x r p.2 := by
      simp only [Shao.C2.ActualDoubleSeparatedClassification.prefixAlive,
        Interior, Shao.C2.ActualOneWallRecordEnvelope.oppositePrefixHit,
        Shao.C2.ActualOneWallRecordEnvelope.oneWallSign, one_mul,
        not_forall, not_imp, not_lt]
      constructor <;> rintro ⟨k, hk, hv⟩ <;> exact ⟨k, hk, hv⟩
    have hNotUpper (p : Shao.Path n × LabelPerm n) (r : Fin n) :
        (¬Shao.C2.ActualDoubleSeparatedClassification.prefixAlive .upper p.1 x r.val p.2) ↔
          Shao.C2.ActualOneWallRecordEnvelope.oppositePrefixHit .lower p.1 x r p.2 := by
      simp only [Shao.C2.ActualDoubleSeparatedClassification.prefixAlive,
        Interior, Shao.C2.ActualOneWallRecordEnvelope.oppositePrefixHit,
        Shao.C2.ActualOneWallRecordEnvelope.oneWallSign, neg_one_mul,
        not_forall, not_imp, not_lt, neg_le_neg_iff]
      constructor <;> rintro ⟨k, hk, hv⟩ <;> exact ⟨k, hk, hv⟩
    have hRank (p : Shao.Path n × LabelPerm n) (r : Fin n) :
        0 ≤ actualDoubleSeparated Q x p.1 (nu p.1) r.val p.2 ∧
          actualDoubleSeparated Q x p.1 (nu p.1) r.val p.2 ≤
            CK * Real.exp (-x ^ 2) * (O .upper r.val p + O .lower r.val p) +
            (if 3 * x * Real.sqrt (remainingEnergy p.1 r.val p.2) / 2 ≤
                |remainingSum p.1 r.val p.2| then
              O .upper r.val p + O .lower r.val p else 0) +
            (if 3 * x * Real.sqrt (remainingEnergy p.1 r.val p.2) / 2 ≤
                |remainingSum p.1 r.val p.2| then
              max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
                p.1 x (nu p.1) r.val p.2) 0 else 0) +
            (if Shao.C2.ActualOneWallRecordEnvelope.oppositePrefixHit .upper p.1 x r p.2
              then O .upper r.val p else 0) +
            (if Shao.C2.ActualOneWallRecordEnvelope.oppositePrefixHit .lower p.1 x r p.2
              then O .lower r.val p else 0) := by
      have hh := hClass Bm PB hBm p.1 x hx (nu p.1) r.val p.2
      have hU := hNonneg .upper (Or.inl rfl) r p
      have hL := hNonneg .lower (Or.inr rfl) r p
      change 0 ≤ actualDoubleSeparated Q x p.1 (nu p.1) r.val p.2 ∧ _ at hh
      refine ⟨hh.1, ?_⟩
      have hhBound := hh.2
      have hPreviousL :
          (if Shao.C2.ActualDoubleSeparatedClassification.prefixAlive .lower p.1 x r.val p.2
            then 0 else O .upper r.val p) =
          (if Shao.C2.ActualOneWallRecordEnvelope.oppositePrefixHit .upper p.1 x r p.2
            then O .upper r.val p else 0) := by
        by_cases hp : Shao.C2.ActualDoubleSeparatedClassification.prefixAlive .lower p.1 x r.val p.2
        · simp only [if_pos hp, if_neg (fun ho => (hNotLower p r).mpr ho hp)]
        · simp only [if_neg hp, if_pos ((hNotLower p r).mp hp)]
      have hPreviousU :
          (if Shao.C2.ActualDoubleSeparatedClassification.prefixAlive .upper p.1 x r.val p.2
            then 0 else O .lower r.val p) =
          (if Shao.C2.ActualOneWallRecordEnvelope.oppositePrefixHit .lower p.1 x r p.2
            then O .lower r.val p else 0) := by
        by_cases hp : Shao.C2.ActualDoubleSeparatedClassification.prefixAlive .upper p.1 x r.val p.2
        · simp only [if_pos hp, if_neg (fun ho => (hNotUpper p r).mpr ho hp)]
        · simp only [if_neg hp, if_pos ((hNotUpper p r).mp hp)]
      change _ ≤ CK * Real.exp (-x ^ 2) * (O .upper r.val p + O .lower r.val p) +
        (if 3 * x * Real.sqrt (remainingEnergy p.1 r.val p.2) / 2 <
            |remainingSum p.1 r.val p.2| then
          O .upper r.val p + O .lower r.val p +
            max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
               p.1 x (nu p.1) r.val p.2) 0 else 0) +
          (if Shao.C2.ActualDoubleSeparatedClassification.prefixAlive .lower p.1 x r.val p.2
            then 0 else O .upper r.val p) +
          (if Shao.C2.ActualDoubleSeparatedClassification.prefixAlive .upper p.1 x r.val p.2
            then 0 else O .lower r.val p) at hhBound
      rw [hPreviousL, hPreviousU] at hhBound
      apply hhBound.trans
      by_cases hs : 3 * x * Real.sqrt (remainingEnergy p.1 r.val p.2) / 2 <
          |remainingSum p.1 r.val p.2|
      · simp only [if_pos hs, if_pos hs.le]
        exact le_of_eq (by ring)
      · rw [if_neg hs]
        split_ifs <;> nlinarith only [hU, hL, le_max_right
          (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
            p.1 x (nu p.1) r.val p.2) 0]
    have hBill0 (p : Shao.Path n × LabelPerm n) : 0 ≤ bill p := by
      apply Finset.sum_nonneg
      intro r hr
      exact (hRank p ⟨r, Finset.mem_range.mp hr⟩).1
    have hDom (p : Shao.Path n × LabelPerm n) :
        bill p ≤ CK * Real.exp (-x ^ 2) * ordinary p + bad p + negative p + prior p := by
      have hh := Finset.sum_le_sum (s := Finset.univ) (fun r _ => (hRank p r).2)
      convert hh using 1
      · exact (Fin.sum_univ_eq_sum_range
          (fun r => actualDoubleSeparated Q x p.1 (nu p.1) r p.2) n).symm
      · dsimp only [ordinary, bad, negative,
          Shao.C2.ActualBadIntervalNegativeBudget.actualBadIntervalNegativeBill, prior]
        rw [← Fin.sum_univ_eq_sum_range (fun r => O .upper r p + O .lower r p) n,
          ← Fin.sum_univ_eq_sum_range (fun r =>
            if 3 * x * Real.sqrt (remainingEnergy p.1 r p.2) / 2 ≤
                |remainingSum p.1 r p.2| then O .upper r p + O .lower r p else 0) n,
          ← Fin.sum_univ_eq_sum_range (fun r =>
            if 3 * x * Real.sqrt (remainingEnergy p.1 r p.2) / 2 ≤
                |remainingSum p.1 r p.2| then
              max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
                p.1 x (nu p.1) r p.2) 0 else 0) n]
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
    run_tac
      let formulaName := Lean.mkPrivateNameCore "Shao.Probability.GaussianTail".toName
        "Shao.density_formula".toName
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        have $(Lean.mkIdent "hDensityFormula".toName) := $(Lean.mkIdent formulaName)))
    have hExpTail : Real.exp (-x ^ 2) ≤ 3 * Shao.standardNormalTail x := by
      have hplus : 0 < 1 + x := by linarith only [hx]
      have hpiroot : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
      have hpi3 : Real.sqrt (2 * Real.pi) ≤ 3 := by
        nlinarith only [Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity),
          Real.pi_lt_four, Real.sqrt_nonneg (2 * Real.pi)]
      have hphi : Real.exp (-x ^ 2 / 2) ≤ 3 * Shao.standardNormalDensity x := by
        have hh : 1 ≤ 3 / Real.sqrt (2 * Real.pi) :=
          (le_div_iff₀ hpiroot).2 (by simpa only [one_mul] using hpi3)
        have hh' := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-x ^ 2 / 2)).le
        rw [hDensityFormula x]
        convert hh' using 1 <;> ring
      have hratio : (1 + x) * Real.exp (-x ^ 2 / 2) ≤ 1 := by
        calc
          _ ≤ Real.exp x * Real.exp (-x ^ 2 / 2) :=
            mul_le_mul_of_nonneg_right
              (by simpa only [add_comm] using Real.add_one_le_exp x) (Real.exp_pos _).le
          _ = Real.exp (x - x ^ 2 / 2) := by rw [← Real.exp_add]; congr 1 <;> ring
          _ ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [hx, sq_nonneg (x - 1)])
      have hcompare : (1 + x) * Real.exp (-x ^ 2) ≤ Real.exp (-x ^ 2 / 2) := by
        have he : Real.exp (-x ^ 2) = Real.exp (-x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [he]
        nlinarith only [mul_le_mul_of_nonneg_left hratio (Real.exp_pos (-x ^ 2 / 2)).le]
      have hh : Real.exp (-x ^ 2) ≤ 3 * Shao.standardNormalDensity x / (1 + x) := by
        apply (le_div_iff₀ hplus).2
        nlinarith only [hcompare, hphi]
      apply hh.trans
      have hm := mul_le_mul_of_nonneg_left (Shao.standardNormal_mills_bounds x hx0.le).1
        (by norm_num : (0 : ℝ) ≤ 3)
      convert hm using 1 <;> ring
    refine ⟨hBillM, hBillI, hBill0, ?_⟩
    calc
      (∫ p, bill p ∂revealLaw P) ≤
          ∫ p, CK * Real.exp (-x ^ 2) * ordinary p + bad p + negative p + prior p ∂revealLaw P :=
        integral_mono hBillI
          ((((hOI.const_mul (CK * Real.exp (-x ^ 2))).add hBI).add hNeg.2.1).add hPI) hDom
      _ = CK * Real.exp (-x ^ 2) * (∫ p, ordinary p ∂revealLaw P) +
          (∫ p, bad p ∂revealLaw P) + (∫ p, negative p ∂revealLaw P) +
          (∫ p, prior p ∂revealLaw P) := by
        rw [hIntegralAdd
            (fun p => CK * Real.exp (-x ^ 2) * ordinary p + bad p + negative p) prior
            (((hOI.const_mul (CK * Real.exp (-x ^ 2))).add hBI).add hNeg.2.1) hPI,
          hIntegralAdd (fun p => CK * Real.exp (-x ^ 2) * ordinary p + bad p) negative
            ((hOI.const_mul (CK * Real.exp (-x ^ 2))).add hBI) hNeg.2.1,
          hIntegralAdd (fun p => CK * Real.exp (-x ^ 2) * ordinary p) bad
            (hOI.const_mul (CK * Real.exp (-x ^ 2))) hBI, integral_const_mul]
      _ ≤ CK * Real.exp (-x ^ 2) * (CO * delta) +
          CB * delta * Shao.standardNormalTail x + CN * delta * Shao.standardNormalTail x +
          CP * delta * Shao.standardNormalTail x :=
        add_le_add (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hPos.1 (by positivity)) hPos.2.2) hNeg.2.2.2) hPos.2.1
      _ ≤ CK * (3 * Shao.standardNormalTail x) * (CO * delta) +
          CB * delta * Shao.standardNormalTail x + CN * delta * Shao.standardNormalTail x +
          CP * delta * Shao.standardNormalTail x := by
        have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hExpTail hCK.le)
          (mul_nonneg hCO.le hdelta)
        linarith only [hh]
      _ = (3 * CK * CO + CP + CB + CN) * delta * Shao.standardNormalTail x := by ring
  -- Proof of the internal quantitative obligation starts here.
  have hLogRatio (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) :
      Real.log (1 + v) / v ≤ Real.log (1 + u) / u := by
    have hv : 0 < v := hu.trans_le huv
    have hu1 : 0 < 1 + u := by linarith only [hu]
    have hv1 : 0 < 1 + v := by linarith only [hv]
    have hTangent := Real.log_le_sub_one_of_pos (div_pos hv1 hu1)
    rw [Real.log_div hv1.ne' hu1.ne'] at hTangent
    have hDiff : Real.log (1 + v) - Real.log (1 + u) ≤ (v - u) / (1 + u) := by
      convert hTangent using 1 <;> field_simp [ne_of_gt hu1] <;> ring
    have hLower : u / (1 + u) ≤ Real.log (1 + u) := by
      have hh := Real.one_sub_inv_le_log_of_pos hu1
      convert hh using 1 <;> field_simp [ne_of_gt hu1] <;> ring
    have hOne := mul_le_mul_of_nonneg_left hDiff hu.le
    have hTwo := mul_le_mul_of_nonneg_left hLower (sub_nonneg.mpr huv)
    have hMiddle : u * ((v - u) / (1 + u)) = (v - u) * (u / (1 + u)) := by ring
    rw [hMiddle] at hOne
    apply (div_le_div_iff₀ hv hu).2
    calc
      Real.log (1 + v) * u =
          u * (Real.log (1 + v) - Real.log (1 + u)) + u * Real.log (1 + u) := by ring
      _ ≤ (v - u) * (u / (1 + u)) + u * Real.log (1 + u) :=
        by linarith only [hOne]
      _ ≤ (v - u) * Real.log (1 + u) + u * Real.log (1 + u) :=
        by linarith only [hTwo]
      _ = Real.log (1 + u) * v := by ring
  have hEarlyEndpoint (N j x Bcap : ℝ) (hj : 0 < j)
      (hearly : 160000 * j ≤ N) (hx : 16 ≤ x) (hB : 0 < Bcap)
      (hscale : Bcap ≤ Real.sqrt N / (200 * x)) :
      let A : ℝ := x * Real.sqrt N / 2
      max (24 * Bcap) (3 * Real.sqrt j) ≤ A ∧
        Real.exp (-(A / (72 * Bcap)) * Real.log (1 + A * Bcap / j)) ≤
          (j / N) * Real.exp (-2 * x ^ 2) := by
    intro A
    have hN : 0 < N := by nlinarith only [hearly, hj]
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
    have hx0 : 0 < x := by linarith only [hx]
    have hx2 : 256 ≤ x ^ 2 := by nlinarith only [hx, sq_nonneg (x - 16)]
    have hA : 0 < A := by dsimp only [A]; positivity
    let B0 : ℝ := Real.sqrt N / (200 * x)
    let y : ℝ := N / j
    have hB0 : 0 < B0 := by dsimp only [B0]; positivity
    have hB0le : Bcap ≤ B0 := hscale
    have hy : 0 < y := by dsimp only [y]; positivity
    have hymin : 160000 ≤ y := by
      dsimp only [y]
      exact (le_div_iff₀ hj).2 (by nlinarith only [hearly])
    have hA24 : 24 * Bcap ≤ A := by
      have hb := (le_div_iff₀ (by positivity : 0 < 200 * x)).mp hscale
      have hh := mul_le_mul_of_nonneg_left hb hx0.le
      have hg := mul_nonneg hB.le (show 0 ≤ 200 * x ^ 2 - 48 by nlinarith only [hx2])
      dsimp only [A]
      nlinarith only [hh, hg]
    have hA3 : 3 * Real.sqrt j ≤ A := by
      have hjN : j ≤ N := by nlinarith only [hearly, hj]
      have hh := mul_le_mul_of_nonneg_right hx2 hN.le
      have hA2 : A ^ 2 = x ^ 2 * N / 4 := by
        dsimp only [A]
        rw [div_pow, mul_pow, Real.sq_sqrt hN.le]
        ring
      apply (sq_le_sq₀ (by positivity : 0 ≤ 3 * Real.sqrt j) hA.le).1
      rw [mul_pow, Real.sq_sqrt hj.le]
      nlinarith only [hA2, hh, hjN, hj]
    have hAB0 : A * B0 / j = y / 400 := by
      dsimp only [A, B0, y]
      field_simp [ne_of_gt hx0, ne_of_gt hj]
      nlinarith only [Real.sq_sqrt hN.le]
    have hAdivB0 : A / (72 * B0) = (25 / 18 : ℝ) * x ^ 2 := by
      dsimp only [A, B0]
      field_simp [ne_of_gt hx0, ne_of_gt hs]
      <;> ring
    have hMono : A / (72 * B0) * Real.log (1 + A * B0 / j) ≤
        A / (72 * Bcap) * Real.log (1 + A * Bcap / j) := by
      have hu : 0 < A * Bcap / j := by positivity
      have huv : A * Bcap / j ≤ A * B0 / j :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hB0le hA.le) hj.le
      have hh := mul_le_mul_of_nonneg_left
        (hLogRatio (A * Bcap / j) (A * B0 / j) hu huv)
        (show 0 ≤ A ^ 2 / (72 * j) by positivity)
      convert hh using 1 <;>
        field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hB0, ne_of_gt hj] <;> ring
    have hSqrtLower : 400 ≤ Real.sqrt y := by
      nlinarith only [Real.sq_sqrt hy.le, hymin, Real.sqrt_nonneg y]
    have hSqrtUpper : Real.sqrt y ≤ y / 400 := by
      have hh := mul_le_mul_of_nonneg_right hSqrtLower (Real.sqrt_nonneg y)
      rw [Real.mul_self_sqrt hy.le] at hh
      nlinarith only [hh]
    have hLogLower : Real.log y / 2 ≤ Real.log (1 + y / 400) := by
      have hh := Real.log_le_log (Real.sqrt_pos.2 hy)
        (show Real.sqrt y ≤ 1 + y / 400 by linarith only [hSqrtUpper])
      simpa only [Real.log_sqrt hy.le] using hh
    have hExp8 : Real.exp (8 : ℝ) ≤ 6561 := by
      have hh := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 8
      have he : Real.exp (8 : ℝ) = Real.exp 1 ^ 8 := by
        rw [← Real.exp_nat_mul]
        norm_num
      rw [he]
      norm_num at hh ⊢
      exact hh
    have hLog8 : 8 ≤ Real.log y := by
      have hh := Real.log_le_log (Real.exp_pos 8)
        (show Real.exp 8 ≤ y by linarith only [hExp8, hymin])
      simpa only [Real.log_exp] using hh
    have hExponent : 2 * x ^ 2 + Real.log y ≤
        A / (72 * Bcap) * Real.log (1 + A * Bcap / j) := by
      have hlog0 : 0 ≤ Real.log y := by linarith only [hLog8]
      have hh := mul_le_mul_of_nonneg_left hLogLower
        (show 0 ≤ (25 / 18 : ℝ) * x ^ 2 by positivity)
      have hlogpay := mul_le_mul_of_nonneg_left hLog8
        (show 0 ≤ x ^ 2 / 2 - 1 by nlinarith only [hx2])
      have hextra := mul_nonneg (sq_nonneg x) hlog0
      rw [hAdivB0, hAB0] at hMono
      nlinarith only [hMono, hh, hlogpay, hextra, hx2]
    refine ⟨max_le hA24 hA3, ?_⟩
    calc
      _ ≤ Real.exp (-(2 * x ^ 2 + Real.log y)) :=
        Real.exp_le_exp.2 (by nlinarith only [hExponent])
      _ = (j / N) * Real.exp (-2 * x ^ 2) := by
        have hInvLog : Real.exp (-Real.log y) = y⁻¹ := by
          rw [Real.exp_neg, Real.exp_log hy]
        rw [neg_add, Real.exp_add, hInvLog,
          show -(2 * x ^ 2) = -2 * x ^ 2 by ring]
        dsimp only [y]
        field_simp [ne_of_gt hN, ne_of_gt hj]
        <;> ring
  obtain ⟨CE, hCE, hEndpoint⟩ :=
    SourceActualRecordEndstrip.actual_true_energy_record_strip_endpoint_tail
  obtain ⟨CU, hCU, hUnweighted⟩ :=
    SourceActualRecordEndstrip.actual_unweighted_true_energy_record_strip
  obtain ⟨CW, hCW, hOrdinaryWeight⟩ := iid_actual_ordinary_suffix_weight_first_moment_and_sum
  obtain ⟨CWRS, hCWRS, hWeighted⟩ :=
    SourceWeightedRecordStrip.actual_circular_weighted_true_energy_record_strip
  obtain ⟨CL, hCL, hLowFull⟩ :=
    SourceActualRecordLowFullEnergy.iid_actual_low_full_energy_two_halfline_budget
  obtain ⟨CR, hCR, hRare⟩ :=
    SourceResidualRareSuffix.iid_marked_and_unmarked_rare_real_suffix_budgets 2
  obtain ⟨CT, hCT, hOmitted⟩ :=
    SourceActualOmittedOvershoot.iid_actual_omitted_overshoot_and_interval_budget
  let CEarly : ℝ := 24 * CE * CW
  let CO : ℝ := CL + CEarly + 1920000 * CU * CW + 1
  let CP : ℝ := CO / Shao.standardNormalTail 400 + 3 * (CL + CEarly) +
    5760000 * CWRS * CW * Real.exp (8 * CWRS + CWRS / 100) + 1
  let CB : ℝ := 3 * (CL + CEarly) + 3840000 * CU * CR + CT + 1
  have hPsi400 : 0 < Shao.standardNormalTail 400 :=
    (Shao.standardNormalTail_basic.2.2.1 400).1
  have hCE0 : 0 < CE := lt_of_lt_of_le zero_lt_one hCE
  have hCU0 : 0 < CU := lt_of_lt_of_le zero_lt_one hCU
  have hCWRS0 : 0 < CWRS := lt_of_lt_of_le zero_lt_one hCWRS
  have hCL0 : 0 < CL := lt_of_lt_of_le zero_lt_one hCL
  have hCO : 0 < CO := by dsimp only [CO, CEarly]; positivity
  have hCP : 0 < CP := by dsimp only [CP, CEarly]; positivity
  have hCB : 0 < CB := by dsimp only [CB, CEarly]; positivity
  refine ⟨CO, CP, CB, hCO, hCP, hCB, ?_⟩
  intro ΩB instΩB Bm PB instPB hBm rho instRho Bcap hBcap hsupport
    hmean hsecond beta n hn x hx hBscale delta hres P nu hnum hcap O ordinary prior bad
  let Q : Measure BridgeNoise := bridgeLaw Bm PB
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw Bm PB hBm
  letI : IsProbabilityMeasure P := by dsimp only [P]; infer_instance
  letI : IsProbabilityMeasure (revealLaw P) := by unfold revealLaw; infer_instance
  let law : (j : ℕ) → Measure (Shao.Path j) := fun j => Measure.pi (fun _ : Fin j => rho)
  have hLawProb (j : ℕ) : IsProbabilityMeasure (law j) := by
    dsimp only [law]
    infer_instance
  have hx0 : 0 < x := by linarith only [hx]
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrootn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnr
  have hPower (r : ℕ) : Integrable (fun z : ℝ => |z| ^ r) rho := by
    apply (integrable_const (Bcap ^ r)).mono' (by fun_prop)
    filter_upwards [hsupport] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg z) r)]
    exact pow_le_pow_left₀ (abs_nonneg z) hz r
  have h2 : Integrable (fun z : ℝ => z ^ 2) rho := by simpa only [sq_abs] using hPower 2
  have hbeta1 : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one
      rho h2 (hPower 3) hsecond
  have hbeta : 0 < beta := lt_of_lt_of_le zero_lt_one hbeta1
  have hdelta : 0 ≤ delta := by dsimp only [delta]; positivity
  let h0 : ℝ := 4 * beta ^ 2
  let H : ℝ := (2 : ℝ) ^ 64 * beta ^ 2 * (1 + x) ^ 6
  let m : ℕ := ⌈H⌉₊
  let kappa : Shao.Path n → LabelPerm n → ℕ := fun a sigma => energyCutoff a h0 sigma
  let tau : Shao.Path n → LabelPerm n → ℕ := fun a sigma =>
    min (energyCutoff a H sigma) (n - m)
  let lam : Shao.Path n → LabelPerm n → ℕ := fun a sigma => min (nu a sigma) (tau a sigma)
  have hRareData := hRare rho Bcap hBcap hsupport hmean hsecond n hn x hx hres
  rcases hRareData with ⟨hBetaR, hh0, hhH, hm4, hmh, hmn, hMarkedI, hMarkedPay,
    hMarkedEarly, hMarkedLate, hFutureI, hFuturePay⟩
  have hH : 0 < H := by dsimp only [H]; positivity
  have hh0H : h0 ≤ H := hhH.trans (by linarith only [hH])
  have hmnNat : m ≤ n := by
    have hmnLocal : (m : ℝ) ≤ (n : ℝ) / 4 := hmn
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by linarith only [hmnLocal, hnr]
    exact_mod_cast hmn'
  have hkm (sigma : LabelPerm n) : Measurable (fun a : Shao.Path n => kappa a sigma) :=
    actual_energy_cutoff_measurable h0 hh0 sigma
  have htm (sigma : LabelPerm n) : Measurable (fun a : Shao.Path n => tau a sigma) :=
    (actual_energy_cutoff_measurable H hH sigma).min measurable_const
  have hlm (sigma : LabelPerm n) : Measurable (fun a : Shao.Path n => lam a sigma) :=
    (hnum sigma).min (htm sigma)
  have htcap (a : Shao.Path n) (sigma : LabelPerm n) : tau a sigma ≤ kappa a sigma :=
    (Shao.C2.AdaptiveRevealCutoff.adaptive_cutoff_stopping_and_le
      a h0 H hh0 hH hh0H m).2 sigma
  have hlcap (a : Shao.Path n) (sigma : LabelPerm n) : lam a sigma ≤ kappa a sigma :=
    (min_le_left _ _).trans (hcap a sigma)
  have hCapRestriction (J : MonitoredDomain) (G : BridgeKernel)
      (a : Shao.Path n) (small large : LabelPerm n → ℕ) (r : ℕ) (sigma : LabelPerm n)
      (hsl : small sigma ≤ large sigma) :
      sourceSeparatedOvershoot J G a x small r sigma =
        if r < small sigma then sourceSeparatedOvershoot J G a x large r sigma else 0 := by
    by_cases hr : r < n
    · by_cases hs : r < small sigma
      · have hl : r < large sigma := hs.trans_le hsl
        simp only [sourceSeparatedOvershoot, dif_pos hr, hs, hl, true_and, if_pos]
      · simp only [sourceSeparatedOvershoot, dif_pos hr, hs, false_and, if_false]
    · simp only [sourceSeparatedOvershoot, dif_neg hr, ite_self]
  have hHalf0 (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower)
      (a : Shao.Path n) (cap : LabelPerm n → ℕ) (hCap : ∀ sigma, cap sigma ≤ kappa a sigma)
      (r : ℕ) (sigma : LabelPerm n) :
      0 ≤ sourceSeparatedOvershoot J (halflineDerivative J) a x cap r sigma := by
    by_cases hr : r < n
    · exact (Shao.C2.ActualOneWallRecordEnvelope.actual_onewall_record_envelope J hJ
        a x beta hx0 hbeta cap ⟨r, hr⟩ sigma (hCap sigma)).1
    · simp only [sourceSeparatedOvershoot, dif_neg hr, le_refl]
  have hCapMono (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower)
      (a : Shao.Path n) (small large : LabelPerm n → ℕ)
      (hsl : ∀ sigma, small sigma ≤ large sigma)
      (hlarge : ∀ sigma, large sigma ≤ kappa a sigma) (r : ℕ) (sigma : LabelPerm n) :
      sourceSeparatedOvershoot J (halflineDerivative J) a x small r sigma ≤
        sourceSeparatedOvershoot J (halflineDerivative J) a x large r sigma := by
    rw [hCapRestriction J (halflineDerivative J) a small large r sigma (hsl sigma)]
    split_ifs
    · exact le_rfl
    · exact hHalf0 J hJ a large hlarge r sigma
  have hReflection : HalflineReflectionIdentities Q := by
    constructor
    · intro w y T z _hw hT hy hz
      exact Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula Bm PB hBm w y T z hT hy hz
    · intro w y T z _hw hT hy hz
      exact Shao.C2.BridgeLowerIdentification.bridge_lower_formula Bm PB hBm w y T z hT hy hz
  have hParts (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower)
      (cap : Shao.Path n → LabelPerm n → ℕ)
      (hCapM : ∀ sigma, Measurable (fun a => cap a sigma)) :=
    source_parts_measurable_integrable J (eventCompletionKernel J Q) (halflineDerivative J)
      (eventCompletionKernel_data J Q).1 (actual_halfline_kernel_data Q hReflection J hJ).1
      4 (actual_halfline_kernel_data Q hReflection J hJ).2.1 P x hx0 cap hCapM
  have hOrdI : Integrable ordinary (revealLaw P) := by
    apply integrable_finsetSum
    intro r _
    exact ((hParts .upper (Or.inl rfl) nu hnum).2.1 r).2.add
      ((hParts .lower (Or.inr rfl) nu hnum).2.1 r).2
  let low : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
    if Shao.energy p.1 < (n : ℝ) / 2 then ordinary p else 0
  let lowKappa : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
    if Shao.energy p.1 < (n : ℝ) / 2 then
      separatedSum .upper (halflineDerivative .upper) p.1 x (kappa p.1) p.2 +
        separatedSum .lower (halflineDerivative .lower) p.1 x (kappa p.1) p.2 else 0
  have hLowM : MeasurableSet {p : Shao.Path n × LabelPerm n |
      Shao.energy p.1 < (n : ℝ) / 2} :=
    measurableSet_lt (Shao.measurable_energy.comp measurable_fst) measurable_const
  have hLowI : Integrable low (revealLaw P) := hOrdI.indicator hLowM
  have hLowData := hLowFull rho Bcap hBcap hsupport hmean hsecond n hn x hx hBscale hres
  change Measurable lowKappa ∧ Integrable lowKappa (revealLaw P) ∧
    (∀ p, 0 ≤ lowKappa p) ∧ _ ∧
    (∫ p, lowKappa p ∂revealLaw P) ≤ CL * delta * Real.exp (-2 * x ^ 2) ∧ _ at hLowData
  have hLowDom (p : Shao.Path n × LabelPerm n) : low p ≤ lowKappa p := by
    by_cases hp : Shao.energy p.1 < (n : ℝ) / 2
    · simp only [low, lowKappa, if_pos hp, ordinary, separatedSum]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun r _ => add_le_add
        (hCapMono .upper (Or.inl rfl) p.1 (nu p.1) (kappa p.1) (hcap p.1)
          (fun _ => le_rfl) r p.2)
        (hCapMono .lower (Or.inr rfl) p.1 (nu p.1) (kappa p.1) (hcap p.1)
          (fun _ => le_rfl) r p.2)
    · simp only [low, lowKappa, if_neg hp, le_refl]
  have hLowPay : (∫ p, low p ∂revealLaw P) ≤ CL * delta * Real.exp (-2 * x ^ 2) :=
    (integral_mono hLowI hLowData.2.1 hLowDom).trans hLowData.2.2.2.2.1
  have hBeforeTau (J : MonitoredDomain) (a : Shao.Path n) (r : ℕ) (sigma : LabelPerm n) :
      (if r < tau a sigma then sourceSeparatedOvershoot J (halflineDerivative J)
        a x (nu a) r sigma else 0) =
      sourceSeparatedOvershoot J (halflineDerivative J) a x (lam a) r sigma := by
    rw [hCapRestriction J (halflineDerivative J) a (lam a) (nu a) r sigma
      (min_le_left _ _)]
    by_cases ht : r < tau a sigma
    · by_cases hnu : r < nu a sigma
      · simp only [lam, lt_min_iff, ht, hnu, and_self, if_pos]
      · have hz : sourceSeparatedOvershoot J (halflineDerivative J) a x (nu a) r sigma = 0 := by
          rw [hCapRestriction J (halflineDerivative J) a (nu a) (kappa a) r sigma (hcap a sigma)]
          simp only [hnu, if_false]
        simp only [lam, lt_min_iff, hnu, false_and, if_false, if_pos ht, hz]
    · simp only [lam, lt_min_iff, ht, and_false, if_false]
  have hBeforeBadEnvelope (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower)
      (p : Shao.Path n × LabelPerm n) (r : Fin n) :
      (if r.val < tau p.1 p.2 then
        if 3 * x * Real.sqrt (remainingEnergy p.1 r.val p.2) / 2 ≤
            |remainingSum p.1 r.val p.2| then O J r.val p else 0 else 0) ≤
        if Shao.C2.ActualOneWallRecordEnvelope.recordStrip J p.1 x r p.2 then
          6 * Shao.C2.ActualOneWallRecordEnvelope.recordIncrement J p.1 r p.2 *
            Shao.C2.ActualOneWallRecordEnvelope.badFutureWeight
              p.1 H m x (r.val + 1) p.2 else 0 := by
    have hh := (Shao.C2.ActualOneWallRecordEnvelope.actual_onewall_bad_future_record_envelope
      J hJ p.1 x beta H (by linarith only [hx]) hbeta hh0H m hmnNat
        (lam p.1) r p.2 (min_le_right _ _)).2
    have he :
        (if r.val < tau p.1 p.2 then
          if 3 * x * Real.sqrt (remainingEnergy p.1 r.val p.2) / 2 ≤
              |remainingSum p.1 r.val p.2| then O J r.val p else 0 else 0) =
        (if 3 * x * Real.sqrt (remainingEnergy p.1 r.val p.2) / 2 ≤
            |remainingSum p.1 r.val p.2| then
          sourceSeparatedOvershoot J (halflineDerivative J) p.1 x (lam p.1) r.val p.2 else 0) := by
      rw [← hBeforeTau J p.1 r.val p.2]
      dsimp only [O]
      split_ifs <;> rfl
    rw [he]
    exact hh
  run_tac
    let modName : Lean.Name := "Shao.Probability.SourceTrueEnergyStrip".toName
    let splitName := Lean.mkPrivateNameCore modName
      "Shao.Probability.tes_head_tail_measurePreserving".toName
    let sumName := Lean.mkPrivateNameCore modName "Shao.Probability.tes_head_tail_sum".toName
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent "hSplit".toName) := $(Lean.mkIdent splitName)))
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent "hSplitSum".toName) := @$(Lean.mkIdent sumName)))
  have hReorderSum (a : Shao.Path n) (sigma : LabelPerm n) :
      Shao.prefixSum (Spitzer.reorder a sigma) n = Shao.prefixSum a n := by
    simp only [Shao.prefixSum_length, Spitzer.reorder]
    exact Equiv.sum_comp sigma a
  have hReorderEnergy (a : Shao.Path n) (sigma : LabelPerm n) :
      Shao.energy (Spitzer.reorder a sigma) = Shao.energy a :=
    Equiv.sum_comp sigma (fun i : Fin n => a i ^ 2)
  have hHeadEnergy (v : Shao.Path n) (j : ℕ) (hjn : j ≤ n) :
      Shao.energy (Spitzer.head v j hjn) = Shao.prefixSquares v j := by
    have hh := Spitzer.head_prefixSum (fun i : Fin n => v i ^ 2) j hjn j le_rfl
    rw [Shao.prefixSum_length] at hh
    exact hh
  have hSuffix (a : Shao.Path n) (sigma : LabelPerm n) (j : ℕ) (hjn : j ≤ n) :
      remainingEnergy a j sigma = Shao.energy (Spitzer.tail (Spitzer.reorder a sigma) j hjn) ∧
      remainingSum a j sigma =
        Shao.prefixSum (Spitzer.tail (Spitzer.reorder a sigma) j hjn) (n - j) := by
    have hq := hSplitSum (Spitzer.reorder a sigma) j hjn (fun z : ℝ => z ^ 2)
    have hs : Shao.prefixSum (Spitzer.reorder a sigma) n =
        Shao.prefixSum (Spitzer.head (Spitzer.reorder a sigma) j hjn) j +
          Shao.prefixSum (Spitzer.tail (Spitzer.reorder a sigma) j hjn) (n - j) := by
      simpa only [Shao.prefixSum_length] using
        hSplitSum (Spitzer.reorder a sigma) j hjn (fun z : ℝ => z)
    change Shao.energy (Spitzer.reorder a sigma) =
      Shao.energy (Spitzer.head (Spitzer.reorder a sigma) j hjn) +
        Shao.energy (Spitzer.tail (Spitzer.reorder a sigma) j hjn) at hq
    rw [hReorderEnergy, hHeadEnergy] at hq
    rw [Spitzer.head_prefixSum (Spitzer.reorder a sigma) j hjn j le_rfl, hReorderSum] at hs
    constructor
    · dsimp only [remainingEnergy]; linarith only [hq]
    · dsimp only [remainingSum]; linarith only [hs]
  have hReorderM : Measurable
      (randomReorder : Shao.Path n × LabelPerm n → Shao.Path n) :=
    measurable_from_prod_countable_left (fun sigma =>
      Measurable.of_eval fun i => measurable_pi_apply (sigma i))
  have hReorderMap : (revealLaw P).map randomReorder = P := by
    have hInd : iIndepFun (fun i : Fin n => Function.eval i) P :=
      iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)
    have hLaw (i : Fin n) : IdentDistrib (Function.eval i) (id : ℝ → ℝ) P rho :=
      ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable,
        by simp only [Measure.map_id]; exact
          (measurePreserving_eval (fun _ : Fin n => rho) i).map_eq⟩
    exact iid_randomPermutation_map_eq_pi P rho (fun i : Fin n => Function.eval i)
      (fun i => measurable_pi_apply i) hInd hLaw
  have hReorderMP : MeasurePreserving randomReorder (revealLaw P) P :=
    ⟨hReorderM, hReorderMap⟩
  let W : (t : ℕ) → Shao.Path t → ℝ := fun t u =>
    if 0 < Shao.energy u ∧ 2 * beta ^ 2 ≤ Shao.energy u then
      1 / Real.sqrt (Shao.energy u) *
        (1 + |Shao.prefixSum u t| / Real.sqrt (Shao.energy u)) ^ 2 else 0
  let future : (t : ℕ) → Shao.Path t → ℝ := fun t u =>
    if 0 < Shao.energy u ∧ H / 2 ≤ Shao.energy u ∧
        Real.sqrt (9 * x ^ 2 / 4 - 1) * Real.sqrt (Shao.energy u) ≤
          |Shao.prefixSum u t| then
      1 / Real.sqrt (Shao.energy u) *
        (1 + |Shao.prefixSum u t| / Real.sqrt (Shao.energy u)) ^ 2 else 0
  have hW := hOrdinaryWeight rho (hPower 3) hmean hsecond
  change (∀ t : ℕ, Measurable (W t) ∧ Integrable (W t) (law t) ∧
    (∀ u : Shao.Path t, 0 ≤ W t u) ∧
    (∫ u : Shao.Path t, W t u ∂law t) ≤ CW / Real.sqrt ((t : ℝ) + beta ^ 2)) ∧
      (∀ u : Shao.Path 0, W 0 u = 0) ∧
      (∀ N : ℕ, (∑ t ∈ Finset.Icc 0 N, ∫ u : Shao.Path t, W t u ∂law t) ≤
        CW * Real.sqrt (N : ℝ)) at hW
  have hFutureInt (t : ℕ) : Integrable (future t) (law t) := hFutureI t
  have hFutureBound (t : ℕ) (ht : m ≤ t) :
      (∫ u : Shao.Path t, future t u ∂law t) ≤
        CR * Real.rpow (t : ℝ) (-1 / 2 : ℝ) * Shao.standardNormalTail x :=
    hFuturePay t ht
  have hFuture0 (t : ℕ) (u : Shao.Path t) : 0 ≤ future t u := by
    dsimp only [future]
    split_ifs <;> positivity
  have hOrdinaryFuture (a : Shao.Path n) (sigma : LabelPerm n) (j : ℕ) (hjn : j ≤ n) :
      Shao.C2.ActualOneWallRecordEnvelope.ordinaryFutureWeight a beta j sigma =
        W (n - j) (Spitzer.tail (Spitzer.reorder a sigma) j hjn) := by
    dsimp only [Shao.C2.ActualOneWallRecordEnvelope.ordinaryFutureWeight,
      Shao.C2.ActualOneWallRecordEnvelope.futureProfile, W]
    rw [(hSuffix a sigma j hjn).1, (hSuffix a sigma j hjn).2]
  have hBadFuture (a : Shao.Path n) (sigma : LabelPerm n) (j : ℕ) (hjn : j ≤ n) :
      Shao.C2.ActualOneWallRecordEnvelope.badFutureWeight a H m x j sigma =
        if m ≤ n - j then future (n - j) (Spitzer.tail (Spitzer.reorder a sigma) j hjn) else 0 := by
    dsimp only [Shao.C2.ActualOneWallRecordEnvelope.badFutureWeight,
      Shao.C2.ActualOneWallRecordEnvelope.futureProfile, future]
    rw [(hSuffix a sigma j hjn).1, (hSuffix a sigma j hjn).2,
      show (9 / 4 : ℝ) * x ^ 2 - 1 = 9 * x ^ 2 / 4 - 1 by ring]
    by_cases hm : m ≤ n - j <;> simp only [hm, true_and, false_and, if_true, if_false]
  let D : (j : ℕ) → Shao.Path j → ℝ := fun j v =>
    max (Shao.prefixSum v j - Shao.maxWithZero (Spitzer.head v (j - 1) (Nat.sub_le j 1))) 0
  let F : (j : ℕ) → ℝ → Shao.Path j → ℝ := fun j q v =>
    Shao.prefixSum v j - x * Real.sqrt (max (Shao.energy v + q) ((n : ℝ) / 2))
  let E : (j : ℕ) → ℝ → Set (Shao.Path j) := fun j q => {v | 0 ≤ F j q v ∧ F j q v ≤ D j v}
  have hD0 (j : ℕ) (v : Shao.Path j) : 0 ≤ D j v := le_max_right _ _
  have hDm (j : ℕ) : Measurable (D j) := by
    have hHeadM : Measurable (fun v : Shao.Path j => Spitzer.head v (j - 1) (Nat.sub_le j 1)) :=
      Measurable.of_eval fun i => measurable_pi_apply _
    exact ((Shao.measurable_prefixSum j).sub
      (Shao.measurable_maxWithZero.comp hHeadM)).max measurable_const
  have hFm (j : ℕ) (q : ℝ) : Measurable (F j q) :=
    (Shao.measurable_prefixSum j).sub
      (measurable_const.mul ((Shao.measurable_energy.add_const q).max measurable_const).sqrt)
  have hEm (j : ℕ) (q : ℝ) : MeasurableSet (E j q) :=
    (measurableSet_le measurable_const (hFm j q)).inter (measurableSet_le (hFm j q) (hDm j))
  have hStripLength (j : ℕ) (q : ℝ) (hq : 0 ≤ q) (v : Shao.Path j) (hv : v ∈ E j q) :
      x ^ 2 ≤ (j : ℝ) := by
    let M : ℝ := max (Shao.energy v + q) ((n : ℝ) / 2)
    have hM : 0 < M := lt_of_lt_of_le (by positivity) (le_max_right _ _)
    have hEnergy : Shao.energy v ≤ M :=
      (show Shao.energy v ≤ Shao.energy v + q by linarith only [hq]).trans (le_max_left _ _)
    have hS : x * Real.sqrt M ≤ Shao.prefixSum v j := by
      have hh := hv.1
      change 0 ≤ Shao.prefixSum v j - x * Real.sqrt M at hh
      linarith only [hh]
    have hS2 := pow_le_pow_left₀ (mul_nonneg hx0.le (Real.sqrt_nonneg M)) hS 2
    rw [mul_pow, Real.sq_sqrt hM.le] at hS2
    have hCauchy : Shao.prefixSum v j ^ 2 ≤ (j : ℝ) * Shao.energy v := by
      have hh := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := v)
      simpa only [Shao.prefixSum_length, Shao.energy, Finset.card_univ, Fintype.card_fin] using hh
    have hEM := mul_le_mul_of_nonneg_left hEnergy (Nat.cast_nonneg j)
    by_contra hh
    have hpos := mul_pos (sub_pos.mpr (lt_of_not_ge hh)) hM
    nlinarith only [hpos, hS2, hCauchy, hEM]
  have hStripSmallEmpty (j : ℕ) (hj : j < 12) (q : ℝ) (hq : 0 ≤ q) : E j q = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro v hv
    have hh := hStripLength j q hq v hv
    have hjr : (j : ℝ) < 12 := by exact_mod_cast hj
    nlinarith only [hh, hjr, hx, sq_nonneg (x - 16)]
  have hSupport (j : ℕ) : ∀ᵐ v : Shao.Path j ∂law j, ∀ i : Fin j, |v i| ≤ Bcap := by
    apply ae_all_iff.2
    intro i
    exact (measurePreserving_eval (fun _ : Fin j => rho) i).quasiMeasurePreserving.ae hsupport
  have hSignM (j : ℕ) (s : ℝ) : Measurable (fun v : Shao.Path j => s • v) :=
    Measurable.of_eval fun i => measurable_const.mul (measurable_pi_apply i)
  have hSignedDI (j : ℕ) (s : ℝ) (hs : s = 1 ∨ s = -1) :
      Integrable (fun v : Shao.Path j => D j (s • v)) (law j) := by
    letI : IsProbabilityMeasure (law j) := hLawProb j
    have hsabs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
    apply (integrable_const ((j : ℝ) * Bcap)).mono'
      ((hDm j).comp (hSignM j s)).aestronglyMeasurable
    filter_upwards [hSupport j] with v hv
    change ‖D j (s • v)‖ ≤ (j : ℝ) * Bcap
    rw [Real.norm_eq_abs, abs_of_nonneg (hD0 j (s • v))]
    apply max_le
    · have hsum : |Shao.prefixSum (s • v) j| ≤ (j : ℝ) * Bcap := by
        rw [Shao.prefixSum_length]
        exact (Finset.abs_sum_le_sum_abs _ _).trans (by
          calc
            _ ≤ ∑ i : Fin j, Bcap := Finset.sum_le_sum fun i _ => by
              simpa only [Pi.smul_apply, smul_eq_mul, abs_mul, hsabs, one_mul] using hv i
            _ = _ := by simp)
      have hM0 := Shao.maxWithZero_nonneg
        (Spitzer.head (s • v) (j - 1) (Nat.sub_le j 1))
      have hsum' := (le_abs_self (Shao.prefixSum (s • v) j)).trans hsum
      linarith only [hsum', hM0]
    · positivity
  -- Genuine product integration, with the complete true suffix fixed.
  -- A may depend on the suffix energy; the original product law is never masked.
  have hBlock (j : ℕ) (hjn : j ≤ n) (s : ℝ) (hs : s = 1 ∨ s = -1)
      (A : ℝ → Shao.Path j → ℝ)
      (hAm : Measurable (fun p : Shao.Path j × Shao.Path (n - j) => A (Shao.energy p.2) p.1))
      (hA0 : ∀ q v, 0 ≤ A q v)
      (hAD : ∀ q v, A q v ≤ D j (s • v))
      (V : Shao.Path (n - j) → ℝ) (hVm : Measurable V)
      (hVI : Integrable V (law (n - j))) (hV0 : ∀ u, 0 ≤ V u)
      (K : ℝ) (hPrefix : ∀ q : ℝ, 0 ≤ q → (∫ v, A q v ∂law j) ≤ K) :
      let Env : Shao.Path n → ℝ := fun v =>
        A (Shao.energy (Spitzer.tail v j hjn)) (Spitzer.head v j hjn) * V (Spitzer.tail v j hjn)
      Measurable Env ∧ Integrable Env P ∧ (∀ v, 0 ≤ Env v) ∧
        (∫ v, Env v ∂P) ≤ K * (∫ u, V u ∂law (n - j)) := by
    intro Env
    let mu : Measure (Shao.Path j × Shao.Path (n - j)) := (law j).prod (law (n - j))
    let G : Shao.Path j × Shao.Path (n - j) → ℝ := fun p => A (Shao.energy p.2) p.1 * V p.2
    have hGm : Measurable G := hAm.mul (hVm.comp measurable_snd)
    have hGI : Integrable G mu := by
      apply ((hSignedDI j s hs).mul_prod hVI).mono' hGm.aestronglyMeasurable
      exact ae_of_all _ fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hA0 _ _) (hV0 _))]
        exact mul_le_mul_of_nonneg_right (hAD _ _) (hV0 _)
    have hsplit : MeasurePreserving
        (fun v : Shao.Path n => (Spitzer.head v j hjn, Spitzer.tail v j hjn)) P mu :=
      hSplit rho n j hjn
    have hEnvM : Measurable Env := hGm.comp hsplit.measurable
    have hEnvI : Integrable Env P := hsplit.integrable_comp_of_integrable hGI
    have hIntegral : (∫ v, Env v ∂P) =
        ∫ u, (∫ v, A (Shao.energy u) v ∂law j) * V u ∂law (n - j) := by
      have hm := integral_map hsplit.aemeasurable hGm.aestronglyMeasurable
      rw [hsplit.map_eq] at hm
      calc
        _ = ∫ p, G p ∂mu := hm.symm
        _ = ∫ u, (∫ v, A (Shao.energy u) v * V u ∂law j) ∂law (n - j) :=
          integral_prod_symm _ hGI
        _ = _ := by simp only [integral_mul_const]
    have hInnerI : Integrable
        (fun u => (∫ v, A (Shao.energy u) v ∂law j) * V u) (law (n - j)) := by
      simpa only [G, integral_mul_const] using hGI.integral_prod_right
    refine ⟨hEnvM, hEnvI, fun v => mul_nonneg (hA0 _ _) (hV0 _), ?_⟩
    rw [hIntegral]
    have hh := integral_mono hInnerI (hVI.const_mul K) fun u =>
      mul_le_mul_of_nonneg_right (hPrefix (Shao.energy u) (Shao.energy_nonneg u)) (hV0 u)
    simpa only [integral_const_mul] using hh
  -- Reflection is a pushforward of the law, rather than a symmetry assumption.
  let eta : ℝ → Measure ℝ := fun s => rho.map (fun z : ℝ => s * z)
  let signLaw : ℝ → (j : ℕ) → Measure (Shao.Path j) := fun s j =>
    Measure.pi (fun _ : Fin j => eta s)
  have hSignProb (s : ℝ) : IsProbabilityMeasure (eta s) := by
    dsimp only [eta]
    infer_instance
  have hSignSupport (s : ℝ) (hs : s = 1 ∨ s = -1) :
      ∀ᵐ z : ℝ ∂eta s, |z| ≤ Bcap := by
    have hsabs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
    apply (ae_map_iff (by fun_prop)
      (measurableSet_le continuous_abs.measurable measurable_const)).2
    simpa only [abs_mul, hsabs, one_mul] using hsupport
  have hSignMean (s : ℝ) : (∫ z : ℝ, z ∂eta s) = 0 := by
    dsimp only [eta]
    rw [integral_map (by fun_prop) (by fun_prop), integral_const_mul, hmean, mul_zero]
  have hSignSecond (s : ℝ) (hs : s = 1 ∨ s = -1) :
      (∫ z : ℝ, z ^ 2 ∂eta s) = 1 := by
    dsimp only [eta]
    rw [integral_map (by fun_prop) (by fun_prop)]
    rcases hs with rfl | rfl
    · simpa only [one_mul] using hsecond
    · simpa only [neg_one_mul, neg_sq] using hsecond
  have hSignBeta (s : ℝ) (hs : s = 1 ∨ s = -1) :
      (∫ z : ℝ, |z| ^ 3 ∂eta s) = beta := by
    have hsabs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
    dsimp only [eta]
    rw [integral_map (by fun_prop) (by fun_prop)]
    simp only [abs_mul, hsabs, one_mul]
    rfl
  have hSignMap (s : ℝ) (j : ℕ) : Measure.map (fun v : Shao.Path j => s • v) (law j) =
      signLaw s j := Measure.pi_map_pi (fun _ : Fin j =>
        (show Measurable (fun z : ℝ => s * z) from measurable_const.mul measurable_id).aemeasurable)
  have hSignIntegral (s : ℝ) (j : ℕ) (G : Shao.Path j → ℝ) (hGm : Measurable G) :
      (∫ v, G (s • v) ∂law j) = ∫ v, G v ∂signLaw s j := by
    have hh := integral_map (μ := law j) (hSignM j s).aemeasurable hGm.aestronglyMeasurable
    rw [hSignMap] at hh
    exact hh.symm
  have hSignEnergy (j : ℕ) (s : ℝ) (hs : s = 1 ∨ s = -1) (v : Shao.Path j) :
      Shao.energy (s • v) = Shao.energy v := by
    rcases hs with rfl | rfl
    · simp only [one_smul]
    · simp only [Shao.energy, Pi.smul_apply, smul_eq_mul, neg_one_mul, neg_sq]
  have hPrefixOrdinary (j : ℕ) (hj : 0 < j) (hjn : j ≤ n)
      (s : ℝ) (hs : s = 1 ∨ s = -1) (q : ℝ) (hq : 0 ≤ q) :
      (∫ v : Shao.Path j, (E j q).indicator (D j) (s • v) ∂law j) ≤ CU * beta / (j : ℝ) := by
    letI : IsProbabilityMeasure (eta s) := hSignProb s
    rw [hSignIntegral s j _ ((hDm j).indicator (hEm j q))]
    by_cases hj12 : j < 12
    · rw [hStripSmallEmpty j hj12 q hq]
      simp only [Set.indicator_empty, integral_zero]
      positivity
    · have hd := hUnweighted (eta s) Bcap hBcap (hSignSupport s hs) (hSignMean s)
        (hSignSecond s hs) n hn x (by linarith only [hx]) hBscale j (by omega) hjn q hq
      rw [hSignBeta s hs] at hd
      exact hd.2.2.2
  have hPrefixEarly (j : ℕ) (hj : 0 < j) (hjn : j ≤ n)
      (hearly : 160000 * (j : ℝ) ≤ (n : ℝ))
      (s : ℝ) (hs : s = 1 ∨ s = -1) (q : ℝ) (hq : 0 ≤ q) :
      (∫ v : Shao.Path j, (E j q).indicator (D j) (s • v) ∂law j) ≤
        CE * beta / (n : ℝ) * Real.exp (-2 * x ^ 2) := by
    letI : IsProbabilityMeasure (eta s) := hSignProb s
    rw [hSignIntegral s j _ ((hDm j).indicator (hEm j q))]
    by_cases hj12 : j < 12
    · rw [hStripSmallEmpty j hj12 q hq]
      simp only [Set.indicator_empty, integral_zero]
      positivity
    · let A : ℝ := x * Real.sqrt (n : ℝ) / 2
      have hjr : 0 < (j : ℝ) := by exact_mod_cast hj
      have hEarly := hEarlyEndpoint (n : ℝ) (j : ℝ) x Bcap hjr hearly hx hBcap hBscale
      change max (24 * Bcap) (3 * Real.sqrt (j : ℝ)) ≤ A ∧
        Real.exp (-(A / (72 * Bcap)) * Real.log (1 + A * Bcap / (j : ℝ))) ≤
          ((j : ℝ) / (n : ℝ)) * Real.exp (-2 * x ^ 2) at hEarly
      have hRootFloor : Real.sqrt (n : ℝ) / 2 ≤ Real.sqrt ((n : ℝ) / 2) := by
        nlinarith only [Real.sq_sqrt hnr.le,
          Real.sq_sqrt (show 0 ≤ (n : ℝ) / 2 by positivity),
          Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg ((n : ℝ) / 2)]
      have hEndpointOnStrip (v : Shao.Path j) (hv : v ∈ E j q) :
          A ≤ Shao.prefixSum v j := by
        have hroot := Real.sqrt_le_sqrt (le_max_right (Shao.energy v + q) ((n : ℝ) / 2))
        have hlow := mul_le_mul_of_nonneg_left (hRootFloor.trans hroot) hx0.le
        have hh := hv.1
        change 0 ≤ Shao.prefixSum v j -
          x * Real.sqrt (max (Shao.energy v + q) ((n : ℝ) / 2)) at hh
        dsimp only [A]
        nlinarith only [hlow, hh]
      have hSet : {v : Shao.Path j | 0 ≤ F j q v ∧ F j q v ≤ D j v ∧
          A ≤ Shao.prefixSum v j} = E j q := by
        ext v
        exact ⟨fun h => ⟨h.1, h.2.1⟩,
          fun h => ⟨h.1, h.2, hEndpointOnStrip v h⟩⟩
      have hd := hEndpoint (eta s) Bcap hBcap (hSignSupport s hs) (hSignMean s)
        (hSignSecond s hs) n hn x (by linarith only [hx]) hBscale j (by omega) hjn
        q hq A hEarly.1
      rw [hSignBeta s hs] at hd
      change Measurable (F j q) ∧ MeasurableSet {v : Shao.Path j |
        0 ≤ F j q v ∧ F j q v ≤ D j v ∧ A ≤ Shao.prefixSum v j} ∧
        Integrable ({v : Shao.Path j | 0 ≤ F j q v ∧ F j q v ≤ D j v ∧
          A ≤ Shao.prefixSum v j}.indicator (D j)) (signLaw s j) ∧ _ at hd
      rw [hSet] at hd
      calc
        _ ≤ CE * beta / (j : ℝ) *
            Real.exp (-(A / (72 * Bcap)) * Real.log (1 + A * Bcap / (j : ℝ))) := hd.2.2.2
        _ ≤ CE * beta / (j : ℝ) * (((j : ℝ) / (n : ℝ)) * Real.exp (-2 * x ^ 2)) :=
          mul_le_mul_of_nonneg_left hEarly.2 (by positivity)
        _ = CE * beta / (n : ℝ) * Real.exp (-2 * x ^ 2) := by
          field_simp [ne_of_gt hjr, ne_of_gt hnr]
          <;> ring
  let AOrd : (j : ℕ) → ℝ → ℝ → Shao.Path j → ℝ := fun j s q v =>
    (E j q).indicator (D j) (s • v)
  have hAOrdM (j : ℕ) (s : ℝ) : Measurable
      (fun p : Shao.Path j × Shao.Path (n - j) => AOrd j s (Shao.energy p.2) p.1) := by
    have hsm : Measurable (fun p : Shao.Path j × Shao.Path (n - j) => s • p.1) :=
      (hSignM j s).comp measurable_fst
    have hdm := (hDm j).comp hsm
    have hfm : Measurable (fun p : Shao.Path j × Shao.Path (n - j) =>
        F j (Shao.energy p.2) (s • p.1)) :=
      ((Shao.measurable_prefixSum j).comp hsm).sub
        (measurable_const.mul ((((Shao.measurable_energy.comp hsm).add
          (Shao.measurable_energy.comp measurable_snd)).max measurable_const).sqrt))
    exact Measurable.ite
      ((measurableSet_le measurable_const hfm).inter (measurableSet_le hfm hdm)) hdm measurable_const
  have hAOrd0 (j : ℕ) (s q : ℝ) (v : Shao.Path j) : 0 ≤ AOrd j s q v :=
    Set.indicator_nonneg (fun u _ => hD0 j u) _
  have hAOrdD (j : ℕ) (s q : ℝ) (v : Shao.Path j) : AOrd j s q v ≤ D j (s • v) := by
    dsimp only [AOrd]
    by_cases hv : s • v ∈ E j q
    · simp only [Set.indicator_of_mem hv, le_refl]
    · simp only [Set.indicator_of_notMem hv]
      exact hD0 j (s • v)
  let EnvOrd : MonitoredDomain → Fin n → Shao.Path n → ℝ := fun J r v =>
    AOrd (r.val + 1) (Shao.C2.ActualOneWallRecordEnvelope.oneWallSign J)
      (Shao.energy (Spitzer.tail v (r.val + 1) (by omega)))
      (Spitzer.head v (r.val + 1) (by omega)) *
        W (n - (r.val + 1)) (Spitzer.tail v (r.val + 1) (by omega))
  have hSignWall (J : MonitoredDomain) :
      Shao.C2.ActualOneWallRecordEnvelope.oneWallSign J = 1 ∨
        Shao.C2.ActualOneWallRecordEnvelope.oneWallSign J = -1 := by
    cases J <;> simp [Shao.C2.ActualOneWallRecordEnvelope.oneWallSign]
  have hEnvOrd (J : MonitoredDomain) (r : Fin n) :
      Measurable (EnvOrd J r) ∧ Integrable (EnvOrd J r) P ∧
      (∀ v, 0 ≤ EnvOrd J r v) ∧
      (∫ v, EnvOrd J r v ∂P) ≤
        CU * beta / (r.val + 1 : ℝ) * (∫ u, W (n - (r.val + 1)) u ∂law (n - (r.val + 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      hBlock (r.val + 1) (by omega) _ (hSignWall J) (AOrd (r.val + 1) _)
        (hAOrdM _ _) (hAOrd0 _ _) (hAOrdD _ _) _
        (hW.1 (n - (r.val + 1))).1 (hW.1 (n - (r.val + 1))).2.1
        (hW.1 (n - (r.val + 1))).2.2.1 _
        (hPrefixOrdinary (r.val + 1) (by omega) (by omega) _ (hSignWall J))
  have hEnvOrdEarly (J : MonitoredDomain) (r : Fin n)
      (hearly : 160000 * (r.val + 1 : ℝ) ≤ (n : ℝ)) :
      (∫ v, EnvOrd J r v ∂P) ≤
        CE * beta / (n : ℝ) * Real.exp (-2 * x ^ 2) *
          (∫ u, W (n - (r.val + 1)) u ∂law (n - (r.val + 1))) := by
    have hh := hBlock (r.val + 1) (by omega) _ (hSignWall J) (AOrd (r.val + 1) _)
      (hAOrdM _ _) (hAOrd0 _ _) (hAOrdD _ _) _
      (hW.1 (n - (r.val + 1))).1 (hW.1 (n - (r.val + 1))).2.1
      (hW.1 (n - (r.val + 1))).2.2.1 _
      (hPrefixEarly (r.val + 1) (by omega) (by omega)
        (by simpa only [Nat.cast_add, Nat.cast_one] using hearly) _ (hSignWall J))
    exact hh.2.2.2
  have hDRecord (J : MonitoredDomain) (a : Shao.Path n) (sigma : LabelPerm n) (r : Fin n) :
      D (r.val + 1) (Shao.C2.ActualOneWallRecordEnvelope.oneWallSign J •
        Spitzer.head (Spitzer.reorder a sigma) (r.val + 1) (by omega)) =
        Shao.C2.ActualOneWallRecordEnvelope.recordIncrement J a r sigma := by
    have he : Spitzer.head (Shao.C2.ActualOneWallRecordEnvelope.oneWallSign J •
        Spitzer.head (Spitzer.reorder a sigma) (r.val + 1) (by omega))
          (r.val + 1 - 1) (by omega) =
        Shao.C2.ActualOneWallRecordEnvelope.oneWallSign J •
          Spitzer.head (Spitzer.reorder a sigma) r.val r.isLt.le := by
      funext i
      rfl
    dsimp only [D, Shao.C2.ActualOneWallRecordEnvelope.recordIncrement]
    rw [Shao.prefixSum_smul,
      Spitzer.head_prefixSum (Spitzer.reorder a sigma) (r.val + 1) (by omega) (r.val + 1) le_rfl, he]
  have hActualStrip (J : MonitoredDomain) (a : Shao.Path n) (sigma : LabelPerm n)
      (r : Fin n) (hhigh : (n : ℝ) / 2 ≤ Shao.energy a) :
      Shao.C2.ActualOneWallRecordEnvelope.recordStrip J a x r sigma ↔
        Shao.C2.ActualOneWallRecordEnvelope.oneWallSign J •
          Spitzer.head (Spitzer.reorder a sigma) (r.val + 1) (by omega) ∈
            E (r.val + 1) (Shao.energy
              (Spitzer.tail (Spitzer.reorder a sigma) (r.val + 1) (by omega))) := by
    have he := hSplitSum (Spitzer.reorder a sigma) (r.val + 1) (by omega) (fun z : ℝ => z ^ 2)
    change Shao.energy (Spitzer.reorder a sigma) =
      Shao.energy (Spitzer.head (Spitzer.reorder a sigma) (r.val + 1) (by omega)) +
        Shao.energy (Spitzer.tail (Spitzer.reorder a sigma) (r.val + 1) (by omega)) at he
    rw [hReorderEnergy] at he
    simp only [E, Set.mem_setOf_eq]
    dsimp only [F, Shao.C2.ActualOneWallRecordEnvelope.recordStrip]
    rw [hDRecord, Shao.prefixSum_smul,
      Spitzer.head_prefixSum (Spitzer.reorder a sigma) (r.val + 1) (by omega) (r.val + 1) le_rfl,
      hSignEnergy _ _ (hSignWall J), ← he, max_eq_left hhigh] <;> rfl
  have hActualEnvDom (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower)
      (p : Shao.Path n × LabelPerm n) (r : Fin n) :
      (if (n : ℝ) / 2 ≤ Shao.energy p.1 then O J r.val p else 0) ≤
        6 * EnvOrd J r (randomReorder p) := by
    have hEnv0 := (hEnvOrd J r).2.2.1 (randomReorder p)
    by_cases hhigh : (n : ℝ) / 2 ≤ Shao.energy p.1
    · rw [if_pos hhigh]
      have hh := (Shao.C2.ActualOneWallRecordEnvelope.actual_onewall_record_envelope
        J hJ p.1 x beta hx0 hbeta (nu p.1) r p.2 (hcap p.1 p.2)).2
      by_cases hr : Shao.C2.ActualOneWallRecordEnvelope.recordStrip J p.1 x r p.2
      · rw [if_pos hr] at hh
        have he : EnvOrd J r (randomReorder p) =
            Shao.C2.ActualOneWallRecordEnvelope.recordIncrement J p.1 r p.2 *
              Shao.C2.ActualOneWallRecordEnvelope.ordinaryFutureWeight p.1 beta (r.val + 1) p.2 := by
          dsimp only [EnvOrd, AOrd, randomReorder]
          rw [Set.indicator_of_mem ((hActualStrip J p.1 p.2 r hhigh).mp hr), hDRecord,
            ← hOrdinaryFuture]
        rw [he]
        nlinarith only [hh]
      · rw [if_neg hr] at hh
        nlinarith only [hh, hEnv0]
    · rw [if_neg hhigh]
      positivity
  have hW0Int (t : ℕ) : 0 ≤ ∫ u, W t u ∂law t :=
    integral_nonneg (hW.1 t).2.2.1
  have hWEarly (r : Fin n) (hearly : 160000 * (r.val + 1 : ℝ) ≤ (n : ℝ)) :
      (∫ u, W (n - (r.val + 1)) u ∂law (n - (r.val + 1))) ≤
        2 * CW / Real.sqrt (n : ℝ) := by
    have hcast : ((n - (r.val + 1) : ℕ) : ℝ) = (n : ℝ) - (r.val + 1 : ℝ) := by
      rw [Nat.cast_sub (by omega : r.val + 1 ≤ n), Nat.cast_add, Nat.cast_one]
    have ht : (n : ℝ) / 2 ≤ ((n - (r.val + 1) : ℕ) : ℝ) + beta ^ 2 := by
      rw [hcast]
      nlinarith only [hearly, sq_nonneg beta]
    have hden : 0 < Real.sqrt (((n - (r.val + 1) : ℕ) : ℝ) + beta ^ 2) :=
      Real.sqrt_pos.2 (by linarith only [ht, hnr])
    have hdenLo : Real.sqrt (n : ℝ) / 2 ≤
        Real.sqrt (((n - (r.val + 1) : ℕ) : ℝ) + beta ^ 2) := by
      nlinarith only [Real.sq_sqrt hnr.le, Real.sq_sqrt (le_of_lt (Real.sqrt_pos.mp hden)),
        Real.sqrt_nonneg (n : ℝ), hden, ht]
    apply (hW.1 (n - (r.val + 1))).2.2.2.trans
    apply (div_le_div_iff₀ hden hrootn).2
    nlinarith only [mul_le_mul_of_nonneg_left hdenLo hCW.le]
  have hWReindex :
      (∑ r : Fin n, ∫ u, W (n - (r.val + 1)) u ∂law (n - (r.val + 1))) ≤
        CW * Real.sqrt (n : ℝ) := by
    have he : (∑ r : Fin n, ∫ u, W (n - (r.val + 1)) u ∂law (n - (r.val + 1))) =
        ∑ t ∈ Finset.range n, ∫ u, W t u ∂law t := by
      have hh := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n))
        (fun t : Fin n => ∫ u, W t.val u ∂law t.val)
      change (∑ r : Fin n, ∫ u : Shao.Path (n - (r.val + 1)),
          W (n - (r.val + 1)) u ∂law (n - (r.val + 1))) =
        ∑ r : Fin n, ∫ u : Shao.Path r.val, W r.val u ∂law r.val at hh
      exact hh.trans (Fin.sum_univ_eq_sum_range (fun t => ∫ u, W t u ∂law t) n)
    rw [he]
    apply (Finset.sum_le_sum_of_subset_of_nonneg (show Finset.range n ⊆ Finset.Icc 0 n from by
      intro t ht
      exact Finset.mem_Icc.2 ⟨Nat.zero_le t, (Finset.mem_range.mp ht).le⟩)
      (fun t _ _ => hW0Int t)).trans
    exact hW.2.2 n
  have hBetaRate : beta / (n : ℝ) * Real.sqrt (n : ℝ) = delta := by
    dsimp only [delta]
    apply (eq_div_iff (ne_of_gt hrootn)).2
    rw [mul_assoc, Real.mul_self_sqrt hnr.le]
    exact div_mul_cancel₀ _ (ne_of_gt hnr)
  have hEnvRankBound (J : MonitoredDomain) (r : Fin n) :
      (∫ v, EnvOrd J r v ∂P) ≤
        (2 * CE * CW * beta / ((n : ℝ) * Real.sqrt (n : ℝ)) * Real.exp (-2 * x ^ 2)) +
        (160000 * CU * beta / (n : ℝ)) *
          (∫ u, W (n - (r.val + 1)) u ∂law (n - (r.val + 1))) := by
    by_cases hearly : 160000 * (r.val + 1 : ℝ) ≤ (n : ℝ)
    · calc
        _ ≤ CE * beta / (n : ℝ) * Real.exp (-2 * x ^ 2) *
            (∫ u, W (n - (r.val + 1)) u ∂law (n - (r.val + 1))) :=
          hEnvOrdEarly J r hearly
        _ ≤ CE * beta / (n : ℝ) * Real.exp (-2 * x ^ 2) * (2 * CW / Real.sqrt (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (hWEarly r hearly) (by positivity)
        _ ≤ _ := by
          have hh : 0 ≤ (160000 * CU * beta / (n : ℝ)) *
              (∫ u, W (n - (r.val + 1)) u ∂law (n - (r.val + 1))) :=
            mul_nonneg (by positivity) (hW0Int _)
          have heq : CE * beta / (n : ℝ) * Real.exp (-2 * x ^ 2) * (2 * CW / Real.sqrt (n : ℝ)) =
              2 * CE * CW * beta / ((n : ℝ) * Real.sqrt (n : ℝ)) * Real.exp (-2 * x ^ 2) := by ring
          rw [heq]
          exact le_add_of_nonneg_right hh
    · have hjr : 0 < (r.val + 1 : ℝ) := by positivity
      have hlate : (n : ℝ) ≤ 160000 * (r.val + 1 : ℝ) := le_of_lt (lt_of_not_ge hearly)
      have hcoeff : CU * beta / (r.val + 1 : ℝ) ≤ 160000 * CU * beta / (n : ℝ) := by
        apply (div_le_div_iff₀ hjr hnr).2
        have hh := mul_le_mul_of_nonneg_left hlate (show 0 ≤ CU * beta by positivity)
        nlinarith only [hh]
      calc
        _ ≤ CU * beta / (r.val + 1 : ℝ) *
            (∫ u, W (n - (r.val + 1)) u ∂law (n - (r.val + 1))) := (hEnvOrd J r).2.2.2
        _ ≤ (160000 * CU * beta / (n : ℝ)) *
            (∫ u, W (n - (r.val + 1)) u ∂law (n - (r.val + 1))) :=
          mul_le_mul_of_nonneg_right hcoeff (hW0Int _)
        _ ≤ _ := le_add_of_nonneg_left (by positivity)
  have hEnvSum (J : MonitoredDomain) :
      (∑ r : Fin n, ∫ v, EnvOrd J r v ∂P) ≤
        2 * CE * CW * delta * Real.exp (-2 * x ^ 2) + 160000 * CU * CW * delta := by
    calc
      _ ≤ ∑ r : Fin n,
          ((2 * CE * CW * beta / ((n : ℝ) * Real.sqrt (n : ℝ)) * Real.exp (-2 * x ^ 2)) +
          (160000 * CU * beta / (n : ℝ)) *
            (∫ u, W (n - (r.val + 1)) u ∂law (n - (r.val + 1)))) :=
        Finset.sum_le_sum fun r _ => hEnvRankBound J r
      _ = (n : ℝ) *
          (2 * CE * CW * beta / ((n : ℝ) * Real.sqrt (n : ℝ)) * Real.exp (-2 * x ^ 2)) +
          (160000 * CU * beta / (n : ℝ)) *
            (∑ r : Fin n, ∫ u, W (n - (r.val + 1)) u ∂law (n - (r.val + 1))) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← Finset.mul_sum]
      _ ≤ (n : ℝ) *
          (2 * CE * CW * beta / ((n : ℝ) * Real.sqrt (n : ℝ)) * Real.exp (-2 * x ^ 2)) +
          (160000 * CU * beta / (n : ℝ)) * (CW * Real.sqrt (n : ℝ)) := by
        have hh := mul_le_mul_of_nonneg_left hWReindex
          (show 0 ≤ 160000 * CU * beta / (n : ℝ) by positivity)
        linarith only [hh]
      _ = _ := by
        have hFirst : (n : ℝ) *
            (2 * CE * CW * beta / ((n : ℝ) * Real.sqrt (n : ℝ)) * Real.exp (-2 * x ^ 2)) =
            2 * CE * CW * delta * Real.exp (-2 * x ^ 2) := by
          dsimp only [delta]
          field_simp [ne_of_gt hnr, ne_of_gt hrootn]
          <;> ring
        have hSecond : (160000 * CU * beta / (n : ℝ)) * (CW * Real.sqrt (n : ℝ)) =
            160000 * CU * CW * delta := by
          calc
            _ = 160000 * CU * CW * (beta / (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
            _ = _ := by rw [hBetaRate]
        rw [hFirst, hSecond]
  have hPairedIntegral (s : Finset (Fin n)) (f g : Fin n → Shao.Path n → ℝ)
      (hf : ∀ r ∈ s, Integrable (f r) P) (hg : ∀ r ∈ s, Integrable (g r) P) :
      (∫ v, ∑ r ∈ s, (f r v + g r v) ∂P) =
        (∑ r ∈ s, ∫ v, f r v ∂P) + (∑ r ∈ s, ∫ v, g r v ∂P) := by
    have hi (r : Fin n) (hr : r ∈ s) : Integrable (fun v => f r v + g r v) P :=
      (hf r hr).add (hg r hr)
    have hSum : (∫ v, ∑ r ∈ s, (f r v + g r v) ∂P) =
        ∑ r ∈ s, ∫ v, f r v + g r v ∂P := integral_finsetSum s hi
    rw [hSum]
    calc
      _ = ∑ r ∈ s, ((∫ v, f r v ∂P) + (∫ v, g r v ∂P)) :=
        Finset.sum_congr rfl (fun r hr => hIntegralAdd (f r) (g r) (hf r hr) (hg r hr))
      _ = _ := Finset.sum_add_distrib
  let high : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
    if (n : ℝ) / 2 ≤ Shao.energy p.1 then ordinary p else 0
  have hHighM : MeasurableSet {p : Shao.Path n × LabelPerm n |
      (n : ℝ) / 2 ≤ Shao.energy p.1} :=
    measurableSet_le measurable_const (Shao.measurable_energy.comp measurable_fst)
  have hHighI : Integrable high (revealLaw P) := hOrdI.indicator hHighM
  let GOrd : Shao.Path n → ℝ := fun v => ∑ r : Fin n, (EnvOrd .upper r v + EnvOrd .lower r v)
  have hGOrdM : Measurable GOrd := by
    apply Finset.measurable_sum
    intro r _
    exact ((hEnvOrd .upper r).1).add (hEnvOrd .lower r).1
  have hGOrdI : Integrable GOrd P := by
    apply integrable_finsetSum
    intro r _
    exact ((hEnvOrd .upper r).2.1).add (hEnvOrd .lower r).2.1
  have hGOrdInt : (∫ p, GOrd (randomReorder p) ∂revealLaw P) = ∫ v, GOrd v ∂P := by
    have hh := integral_map hReorderMP.aemeasurable hGOrdM.aestronglyMeasurable
    rw [hReorderMP.map_eq] at hh
    exact hh.symm
  have hHighDom (p : Shao.Path n × LabelPerm n) : high p ≤ 6 * GOrd (randomReorder p) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) fun r _ =>
      add_le_add (hActualEnvDom .upper (Or.inl rfl) p r) (hActualEnvDom .lower (Or.inr rfl) p r)
    by_cases hhigh : (n : ℝ) / 2 ≤ Shao.energy p.1
    · simp only [if_pos hhigh] at hh
      dsimp only [high, ordinary, GOrd]
      rw [if_pos hhigh, ← Fin.sum_univ_eq_sum_range]
      convert hh using 1
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    · dsimp only [high]
      rw [if_neg hhigh]
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun r _ =>
        add_nonneg ((hEnvOrd .upper r).2.2.1 _) ((hEnvOrd .lower r).2.2.1 _))
  have hHighPay : (∫ p, high p ∂revealLaw P) ≤
      CEarly * delta * Real.exp (-2 * x ^ 2) + 1920000 * CU * CW * delta := by
    calc
      _ ≤ ∫ p, 6 * GOrd (randomReorder p) ∂revealLaw P :=
        integral_mono hHighI ((hReorderMP.integrable_comp_of_integrable hGOrdI).const_mul 6) hHighDom
      _ = 6 * (∫ v, GOrd v ∂P) := by rw [integral_const_mul, hGOrdInt]
      _ = 6 * ((∑ r : Fin n, ∫ v, EnvOrd .upper r v ∂P) +
          (∑ r : Fin n, ∫ v, EnvOrd .lower r v ∂P)) := by
        dsimp only [GOrd]
        rw [hPairedIntegral Finset.univ (EnvOrd .upper) (EnvOrd .lower)
          (fun r _ => (hEnvOrd .upper r).2.1) (fun r _ => (hEnvOrd .lower r).2.1)]
      _ ≤ 6 * ((2 * CE * CW * delta * Real.exp (-2 * x ^ 2) + 160000 * CU * CW * delta) +
          (2 * CE * CW * delta * Real.exp (-2 * x ^ 2) + 160000 * CU * CW * delta)) :=
        mul_le_mul_of_nonneg_left (add_le_add (hEnvSum .upper) (hEnvSum .lower)) (by norm_num)
      _ = _ := by dsimp only [CEarly]; ring
  have hOrdinaryPay : (∫ p, ordinary p ∂revealLaw P) ≤ CO * delta := by
    have he : ordinary = fun p => low p + high p := by
      funext p
      dsimp only [low, high]
      by_cases hp : Shao.energy p.1 < (n : ℝ) / 2
      · rw [if_pos hp, if_neg (not_le_of_gt hp), add_zero]
      · rw [if_neg hp, if_pos (le_of_not_gt hp), zero_add]
    have hexp : Real.exp (-2 * x ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith only [sq_nonneg x])
    rw [he, integral_add hLowI hHighI]
    calc
      _ ≤ CL * delta * Real.exp (-2 * x ^ 2) +
          (CEarly * delta * Real.exp (-2 * x ^ 2) + 1920000 * CU * CW * delta) :=
        add_le_add hLowPay hHighPay
      _ ≤ CL * delta + CEarly * delta + 1920000 * CU * CW * delta := by
        have h1 := mul_le_mul_of_nonneg_left hexp (show 0 ≤ CL * delta by positivity)
        have h2 := mul_le_mul_of_nonneg_left hexp (show 0 ≤ CEarly * delta by dsimp only [CEarly]; positivity)
        nlinarith only [h1, h2]
      _ ≤ CO * delta := by
        dsimp only [CO]
        nlinarith only [hdelta]
  let omitted : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ := fun J p =>
    ∑ r : Fin n, if tau p.1 p.2 ≤ r.val ∧ r.val < kappa p.1 p.2 then
      sourceSeparatedOvershoot J (actualDerivativeFamily Q J) p.1 x (kappa p.1) r.val p.2 else 0
  let intervalPositive : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
    ∑ r : Fin n, if tau p.1 p.2 ≤ r.val ∧ r.val < kappa p.1 p.2 then
      max (sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
        p.1 x (kappa p.1) r.val p.2) 0 else 0
  let intervalAbsolute : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
    ∑ r : Fin n, if tau p.1 p.2 ≤ r.val ∧ r.val < kappa p.1 p.2 then
      |sourceRemainder .interval (eventCompletionKernel .interval Q)
        (actualDerivativeFamily Q .interval) p.1 x r.val p.2| else 0
  let tailCost : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
    omitted .upper p + omitted .lower p + intervalPositive p + intervalAbsolute p
  have hOmittedData := hOmitted PB Bm hBm rho Bcap hBcap hsupport hmean hsecond
    n hn x hx hBscale hres
  rcases hOmittedData with ⟨hOmittedI, hIPM, hIPI, hIAM, hIAI, hTCM, hTCI,
    hTCPositive, hTCRough, hTCMiddle, hTCPay⟩
  have hTailCostM : Measurable tailCost := hTCM
  have hTailCostI : Integrable tailCost (revealLaw P) := hTCI
  have hTailCostPay : (∫ p, tailCost p ∂revealLaw P) ≤
      CT * delta * Shao.standardNormalTail x := hTCPay
  have hTailCost0 (p : Shao.Path n × LabelPerm n) : 0 ≤ tailCost p :=
    (hTCPositive p).2.2.2.2.2
  let tailNu : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
    ∑ r : Fin n, if tau p.1 p.2 ≤ r.val then O .upper r.val p + O .lower r.val p else 0
  have hTailRank (p : Shao.Path n × LabelPerm n) (r : Fin n) :
      (if tau p.1 p.2 ≤ r.val then O .upper r.val p + O .lower r.val p else 0) ≤
      (if tau p.1 p.2 ≤ r.val ∧ r.val < kappa p.1 p.2 then
        sourceSeparatedOvershoot .upper (halflineDerivative .upper)
          p.1 x (kappa p.1) r.val p.2 +
        sourceSeparatedOvershoot .lower (halflineDerivative .lower)
          p.1 x (kappa p.1) r.val p.2 else 0) := by
    by_cases ht : tau p.1 p.2 ≤ r.val
    · rw [if_pos ht]
      by_cases hk : r.val < kappa p.1 p.2
      · rw [if_pos ⟨ht, hk⟩]
        exact add_le_add
          (hCapMono .upper (Or.inl rfl) p.1 (nu p.1) (kappa p.1) (hcap p.1)
            (fun _ => le_rfl) r.val p.2)
          (hCapMono .lower (Or.inr rfl) p.1 (nu p.1) (kappa p.1) (hcap p.1)
            (fun _ => le_rfl) r.val p.2)
      · have hnu : ¬r.val < nu p.1 p.2 := fun hh => hk (hh.trans_le (hcap p.1 p.2))
        have hInactive : ¬(tau p.1 p.2 ≤ r.val ∧ r.val < kappa p.1 p.2) := fun hh => hk hh.2
        simp only [if_neg hInactive, O, sourceSeparatedOvershoot,
          dif_pos r.isLt, hnu, false_and, if_false, zero_add, le_refl]
    · have hInactive : ¬(tau p.1 p.2 ≤ r.val ∧ r.val < kappa p.1 p.2) := fun hh => ht hh.1
      simp only [if_neg ht, if_neg hInactive, le_refl]
  have hTailSourceDom (p : Shao.Path n × LabelPerm n) : tailNu p ≤ tailCost p := by
    have hh := Finset.sum_le_sum (s := Finset.univ) fun r _ => hTailRank p r
    have he : tailNu p ≤ omitted .upper p + omitted .lower p := by
      convert hh using 1
      dsimp only [omitted]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      split_ifs
      · rfl
      · exact zero_add 0
    have hIP0 : 0 ≤ intervalPositive p := (hTCPositive p).2.2.1
    have hIA0 : 0 ≤ intervalAbsolute p := (hTCPositive p).2.2.2.2.1
    dsimp only [tailCost]
    linarith only [he, hIP0, hIA0]
  let earlySet : Finset (Fin n) := Finset.univ.filter (fun r =>
    160000 * (r.val + 1 : ℝ) ≤ (n : ℝ))
  let earlyOrdinary : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
    ∑ r ∈ earlySet, (O .upper r.val p + O .lower r.val p)
  let earlyHigh : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
    if (n : ℝ) / 2 ≤ Shao.energy p.1 then earlyOrdinary p else 0
  let GEarly : Shao.Path n → ℝ := fun v => ∑ r ∈ earlySet, (EnvOrd .upper r v + EnvOrd .lower r v)
  have hEarlyMember (r : Fin n) (hr : r ∈ earlySet) :
      160000 * (r.val + 1 : ℝ) ≤ (n : ℝ) := (Finset.mem_filter.mp hr).2
  have hEarlyOrdI : Integrable earlyOrdinary (revealLaw P) := by
    apply integrable_finsetSum
    intro r _
    exact ((hParts .upper (Or.inl rfl) nu hnum).2.1 r.val).2.add
      ((hParts .lower (Or.inr rfl) nu hnum).2.1 r.val).2
  have hEarlyHighI : Integrable earlyHigh (revealLaw P) := hEarlyOrdI.indicator hHighM
  have hGEarlyM : Measurable GEarly := by
    apply Finset.measurable_sum
    intro r _
    exact ((hEnvOrd .upper r).1).add (hEnvOrd .lower r).1
  have hGEarlyI : Integrable GEarly P := by
    apply integrable_finsetSum
    intro r _
    exact ((hEnvOrd .upper r).2.1).add (hEnvOrd .lower r).2.1
  have hEarlyEnvSum (J : MonitoredDomain) :
      (∑ r ∈ earlySet, ∫ v, EnvOrd J r v ∂P) ≤
        2 * CE * CW * delta * Real.exp (-2 * x ^ 2) := by
    have hEach (r : Fin n) (hr : r ∈ earlySet) :
        (∫ v, EnvOrd J r v ∂P) ≤
          2 * CE * CW * beta / ((n : ℝ) * Real.sqrt (n : ℝ)) * Real.exp (-2 * x ^ 2) := by
      have hh := mul_le_mul_of_nonneg_left (hWEarly r (hEarlyMember r hr))
        (show 0 ≤ CE * beta / (n : ℝ) * Real.exp (-2 * x ^ 2) by positivity)
      apply (hEnvOrdEarly J r (hEarlyMember r hr)).trans
      convert hh using 1 <;> ring
    have hCard : (earlySet.card : ℝ) ≤ (n : ℝ) := by
      have hh : earlySet.card ≤ n := by
        apply (Finset.card_le_card (Finset.filter_subset _ _)).trans
        simp
      exact_mod_cast hh
    calc
      _ ≤ ∑ _r ∈ earlySet,
          2 * CE * CW * beta / ((n : ℝ) * Real.sqrt (n : ℝ)) * Real.exp (-2 * x ^ 2) :=
        Finset.sum_le_sum hEach
      _ = (earlySet.card : ℝ) *
          (2 * CE * CW * beta / ((n : ℝ) * Real.sqrt (n : ℝ)) * Real.exp (-2 * x ^ 2)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℝ) *
          (2 * CE * CW * beta / ((n : ℝ) * Real.sqrt (n : ℝ)) * Real.exp (-2 * x ^ 2)) :=
        mul_le_mul_of_nonneg_right hCard (by positivity)
      _ = _ := by
        dsimp only [delta]
        field_simp [ne_of_gt hnr, ne_of_gt hrootn]
        <;> ring
  have hEarlyHighDom (p : Shao.Path n × LabelPerm n) :
      earlyHigh p ≤ 6 * GEarly (randomReorder p) := by
    have hh := Finset.sum_le_sum (s := earlySet) fun r _ =>
      add_le_add (hActualEnvDom .upper (Or.inl rfl) p r) (hActualEnvDom .lower (Or.inr rfl) p r)
    by_cases hhigh : (n : ℝ) / 2 ≤ Shao.energy p.1
    · simp only [if_pos hhigh] at hh
      dsimp only [earlyHigh, earlyOrdinary, GEarly]
      rw [if_pos hhigh]
      convert hh using 1
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    · dsimp only [earlyHigh]
      rw [if_neg hhigh]
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun r _ =>
        add_nonneg ((hEnvOrd .upper r).2.2.1 _) ((hEnvOrd .lower r).2.2.1 _))
  have hEarlyHighPay : (∫ p, earlyHigh p ∂revealLaw P) ≤
      CEarly * delta * Real.exp (-2 * x ^ 2) := by
    have hTransfer : (∫ p, GEarly (randomReorder p) ∂revealLaw P) = ∫ v, GEarly v ∂P := by
      have hh := integral_map hReorderMP.aemeasurable hGEarlyM.aestronglyMeasurable
      rw [hReorderMP.map_eq] at hh
      exact hh.symm
    calc
      _ ≤ ∫ p, 6 * GEarly (randomReorder p) ∂revealLaw P :=
        integral_mono hEarlyHighI
          ((hReorderMP.integrable_comp_of_integrable hGEarlyI).const_mul 6) hEarlyHighDom
      _ = 6 * (∫ v, GEarly v ∂P) := by rw [integral_const_mul, hTransfer]
      _ = 6 * ((∑ r ∈ earlySet, ∫ v, EnvOrd .upper r v ∂P) +
          (∑ r ∈ earlySet, ∫ v, EnvOrd .lower r v ∂P)) := by
        dsimp only [GEarly]
        rw [hPairedIntegral earlySet (EnvOrd .upper) (EnvOrd .lower)
          (fun r _ => (hEnvOrd .upper r).2.1) (fun r _ => (hEnvOrd .lower r).2.1)]
      _ ≤ 6 * (2 * CE * CW * delta * Real.exp (-2 * x ^ 2) +
          2 * CE * CW * delta * Real.exp (-2 * x ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add (hEarlyEnvSum .upper) (hEarlyEnvSum .lower)) (by norm_num)
      _ = _ := by dsimp only [CEarly]; ring
  let base : (Shao.Path n × LabelPerm n) → ℝ := fun p => low p + earlyHigh p
  have hBaseI : Integrable base (revealLaw P) := hLowI.add hEarlyHighI
  have hBasePay : (∫ p, base p ∂revealLaw P) ≤
      (CL + CEarly) * delta * Real.exp (-2 * x ^ 2) := by
    rw [show base = fun p => low p + earlyHigh p from rfl, integral_add hLowI hEarlyHighI]
    convert add_le_add hLowPay hEarlyHighPay using 1 <;> ring
  let theta : ℝ := 2 * x / Real.sqrt (n : ℝ)
  let witnessLevel : ℝ := 3 * x * Real.sqrt ((n : ℝ) / 2)
  let priorFactor : ℝ := (1 + 2 * x) ^ 5 *
    Real.exp (8 * CWRS + CWRS / 100) * Real.exp (-(11 / 5 : ℝ) * x ^ 2)
  have htheta : 0 ≤ theta := by dsimp only [theta]; positivity
  have hthetaB : theta * Bcap ≤ 1 / 100 := by
    have hb := (le_div_iff₀ (by positivity : 0 < 200 * x)).mp hBscale
    dsimp only [theta]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hrootn).2
    nlinarith only [hb]
  have htheta2 : (n : ℝ) * theta ^ 2 = 4 * x ^ 2 := by
    dsimp only [theta]
    rw [div_pow, mul_pow, Real.sq_sqrt hnr.le]
    field_simp [ne_of_gt hnr]
    <;> ring
  have htheta3 : (n : ℝ) * theta ^ 3 * beta = 8 * delta * x ^ 3 := by
    have he : theta ^ 3 = theta ^ 2 * theta := by ring
    rw [he, ← mul_assoc, htheta2]
    dsimp only [theta, delta]
    ring
  have hResidualX : delta * x ^ 3 ≤ 1 := by
    have hExp : Real.exp (-3 * x ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith only [sq_nonneg x])
    have hCube := pow_le_pow_left₀ hx0.le (show x ≤ 1 + x by linarith) 3
    exact (mul_le_mul_of_nonneg_left hCube hdelta).trans (hres.trans hExp)
  have hthetaPoly (j : ℕ) (hjn : j ≤ n) : 1 + theta * Real.sqrt (j : ℝ) ≤ 1 + 2 * x := by
    have hh := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (show (j : ℝ) ≤ (n : ℝ) by exact_mod_cast hjn)) htheta
    have he : theta * Real.sqrt (n : ℝ) = 2 * x := by
      dsimp only [theta]
      exact div_mul_cancel₀ _ (ne_of_gt hrootn)
    rw [he] at hh
    linarith only [hh]
  have hthetaLarge (j : ℕ) (hLate : (n : ℝ) < 160000 * (j : ℝ)) (hx400 : 400 ≤ x) :
      1 ≤ theta * Real.sqrt ((j : ℝ) / 4) := by
    have hx2 : 160000 ≤ x ^ 2 := by nlinarith only [hx400, sq_nonneg (x - 400)]
    have he : (theta * Real.sqrt ((j : ℝ) / 4)) ^ 2 = x ^ 2 * (j : ℝ) / (n : ℝ) := by
      dsimp only [theta]
      rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hnr.le,
        Real.sq_sqrt (show 0 ≤ (j : ℝ) / 4 by positivity)]
      ring
    apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (by positivity)).1
    rw [he, one_pow]
    apply (le_div_iff₀ hnr).2
    have hh := mul_le_mul_of_nonneg_right hx2 (Nat.cast_nonneg j)
    nlinarith only [hLate, hh]
  have hthetaExponent (j : ℕ) (hjn : j ≤ n) :
      (253 / 500 : ℝ) * (j : ℝ) * theta ^ 2 +
          CWRS * (j : ℝ) * theta ^ 3 * beta + CWRS * theta * Bcap - theta * witnessLevel ≤
        -(11 / 5 : ℝ) * x ^ 2 + (8 * CWRS + CWRS / 100) := by
    have hjr : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjn
    have hQuad : (253 / 500 : ℝ) * (j : ℝ) * theta ^ 2 ≤ (253 / 125 : ℝ) * x ^ 2 := by
      have hh := mul_le_mul_of_nonneg_right hjr (show 0 ≤ (253 / 500 : ℝ) * theta ^ 2 by positivity)
      nlinarith only [hh, htheta2]
    have hCube : CWRS * (j : ℝ) * theta ^ 3 * beta ≤ 8 * CWRS := by
      have hh := mul_le_mul_of_nonneg_right hjr (show 0 ≤ CWRS * theta ^ 3 * beta by positivity)
      have hp := mul_le_mul_of_nonneg_left hResidualX hCWRS0.le
      have he := congrArg (fun z : ℝ => CWRS * z) htheta3
      nlinarith only [hh, he, hp]
    have hSupportPay : CWRS * theta * Bcap ≤ CWRS / 100 := by
      nlinarith only [mul_le_mul_of_nonneg_left hthetaB hCWRS0.le]
    have hFloor : (88 / 125 : ℝ) * Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) / 2) := by
      apply (sq_le_sq₀ (by positivity) (by positivity)).1
      rw [mul_pow, Real.sq_sqrt hnr.le, Real.sq_sqrt (show 0 ≤ (n : ℝ) / 2 by positivity)]
      nlinarith only [hnr]
    have hWitnessPay : (528 / 125 : ℝ) * x ^ 2 ≤ theta * witnessLevel := by
      have hh := mul_le_mul_of_nonneg_left hFloor (show 0 ≤ theta * (3 * x) by positivity)
      convert hh using 1
      · dsimp only [theta]
        field_simp [ne_of_gt hrootn]
        <;> ring
      · dsimp only [witnessLevel]
        ring
    linarith only [hQuad, hCube, hSupportPay, hWitnessPay]
  obtain ⟨CMoment, hCMoment, hWitnessMoment⟩ :=
    Shao.Probability.SourceCircularWitnessMoment.actual_circular_witness_small_parameter_moment
  have hWitnessM (j : ℕ) : Measurable
      (Shao.C2.ActualOneWallRecordEnvelope.circularWitness : Shao.Path j → ℝ) :=
    (hWitnessMoment rho Bcap hBcap hsupport hmean hsecond j).1
  let APrior : (j : ℕ) → ℝ → ℝ → Shao.Path j → ℝ := fun j s q v =>
    if s • v ∈ E j q ∧ witnessLevel ≤
        Shao.C2.ActualOneWallRecordEnvelope.circularWitness (s • v) then D j (s • v) else 0
  have hPriorPrefix (j : ℕ) (hj : 0 < j) (hjn : j ≤ n)
      (hLate : (n : ℝ) < 160000 * (j : ℝ)) (hx400 : 400 ≤ x)
      (s : ℝ) (hs : s = 1 ∨ s = -1) (q : ℝ) (hq : 0 ≤ q) :
      (∫ v, APrior j s q v ∂law j) ≤ CWRS * beta / (j : ℝ) * priorFactor := by
    letI : IsProbabilityMeasure (eta s) := hSignProb s
    let G : Shao.Path j → ℝ := fun v =>
      if v ∈ E j q ∧ witnessLevel ≤ Shao.C2.ActualOneWallRecordEnvelope.circularWitness v then D j v else 0
    let Z : Shao.Path j → ℝ := (E j q).indicator (fun v =>
      D j v * Real.exp (theta * Shao.C2.ActualOneWallRecordEnvelope.circularWitness v))
    have hGm : Measurable G := Measurable.ite
      ((hEm j q).inter (measurableSet_le measurable_const (hWitnessM j))) (hDm j) measurable_const
    change (∫ v, G (s • v) ∂law j) ≤ _
    rw [hSignIntegral s j G hGm]
    by_cases hj12 : j < 12
    · have hGzero : G = 0 := by
        funext v
        simp only [G, hStripSmallEmpty j hj12 q hq, Set.notMem_empty, false_and, if_false, Pi.zero_apply]
      simp only [hGzero, Pi.zero_apply, integral_zero]
      dsimp only [priorFactor]
      positivity
    · have hd := hWeighted (eta s) Bcap hBcap (hSignSupport s hs) (hSignMean s)
        (hSignSecond s hs) n hn x (by linarith only [hx]) hBscale j (by omega) hjn q hq
        theta htheta hthetaB (hthetaLarge j hLate hx400)
      rw [hSignBeta s hs] at hd
      change Measurable (F j q) ∧ MeasurableSet (E j q) ∧
        Integrable Z (signLaw s j) ∧ _ at hd
      have hZ0 (v : Shao.Path j) : 0 ≤ Z v :=
        Set.indicator_nonneg (fun v _ => mul_nonneg (hD0 j v) (Real.exp_pos _).le) v
      have hG0 (v : Shao.Path j) : 0 ≤ G v := by dsimp only [G]; split_ifs <;> positivity
      have hDom (v : Shao.Path j) : G v ≤ Real.exp (-theta * witnessLevel) * Z v := by
        by_cases hv : v ∈ E j q ∧ witnessLevel ≤ Shao.C2.ActualOneWallRecordEnvelope.circularWitness v
        · simp only [G, if_pos hv, Z, Set.indicator_of_mem hv.1]
          have he : 1 ≤ Real.exp (-theta * witnessLevel) *
              Real.exp (theta * Shao.C2.ActualOneWallRecordEnvelope.circularWitness v) := by
            rw [← Real.exp_add]
            apply Real.one_le_exp_iff.2
            nlinarith only [mul_le_mul_of_nonneg_left hv.2 htheta]
          have hh := mul_le_mul_of_nonneg_left he (hD0 j v)
          nlinarith only [hh]
        · rw [show G v = 0 by simp only [G, if_neg hv]]
          exact mul_nonneg (Real.exp_pos _).le (hZ0 v)
      have hBoundI := hd.2.2.1.const_mul (Real.exp (-theta * witnessLevel))
      have hGI : Integrable G (signLaw s j) := hBoundI.mono' hGm.aestronglyMeasurable
        (ae_of_all _ fun v => by rw [Real.norm_eq_abs, abs_of_nonneg (hG0 v)]; exact hDom v)
      have hi := integral_mono hGI hBoundI hDom
      rw [integral_const_mul] at hi
      have hCoef : 0 ≤ CWRS * beta / (j : ℝ) := by positivity
      have hPoly := pow_le_pow_left₀ (show 0 ≤ 1 + theta * Real.sqrt (j : ℝ) by positivity)
        (hthetaPoly j hjn) 5
      calc
        _ ≤ Real.exp (-theta * witnessLevel) * (∫ v, Z v ∂signLaw s j) := hi
        _ ≤ Real.exp (-theta * witnessLevel) *
            (CWRS * beta / (j : ℝ) * (1 + theta * Real.sqrt (j : ℝ)) ^ 5 *
              Real.exp ((253 / 500 : ℝ) * (j : ℝ) * theta ^ 2 +
                CWRS * (j : ℝ) * theta ^ 3 * beta + CWRS * theta * Bcap)) :=
          mul_le_mul_of_nonneg_left hd.2.2.2 (Real.exp_pos _).le
        _ = CWRS * beta / (j : ℝ) * (1 + theta * Real.sqrt (j : ℝ)) ^ 5 *
            Real.exp ((253 / 500 : ℝ) * (j : ℝ) * theta ^ 2 +
              CWRS * (j : ℝ) * theta ^ 3 * beta + CWRS * theta * Bcap - theta * witnessLevel) := by
          have he : Real.exp ((253 / 500 : ℝ) * (j : ℝ) * theta ^ 2 +
                CWRS * (j : ℝ) * theta ^ 3 * beta + CWRS * theta * Bcap - theta * witnessLevel) =
              Real.exp ((253 / 500 : ℝ) * (j : ℝ) * theta ^ 2 +
                CWRS * (j : ℝ) * theta ^ 3 * beta + CWRS * theta * Bcap) *
                Real.exp (-theta * witnessLevel) := by
            rw [sub_eq_add_neg, Real.exp_add,
              show -(theta * witnessLevel) = -theta * witnessLevel by ring]
          rw [he]
          ring
        _ ≤ CWRS * beta / (j : ℝ) * (1 + 2 * x) ^ 5 *
            Real.exp (-(11 / 5 : ℝ) * x ^ 2 + (8 * CWRS + CWRS / 100)) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hPoly hCoef)
            (Real.exp_le_exp.2 (hthetaExponent j hjn)) (Real.exp_pos _).le (by positivity)
        _ = CWRS * beta / (j : ℝ) * priorFactor := by
          dsimp only [priorFactor]
          rw [Real.exp_add]
          ring
  let lateSet : Finset (Fin n) := Finset.univ.filter (fun r =>
    ¬160000 * (r.val + 1 : ℝ) ≤ (n : ℝ))
  have hLateMember (r : Fin n) (hr : r ∈ lateSet) :
      (n : ℝ) < 160000 * (r.val + 1 : ℝ) := lt_of_not_ge (Finset.mem_filter.mp hr).2
  have hO0 (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower)
      (p : Shao.Path n × LabelPerm n) (r : Fin n) : 0 ≤ O J r.val p :=
    hHalf0 J hJ p.1 (nu p.1) (hcap p.1) r.val p.2
  have hBaseDom (M Hrank : (Shao.Path n × LabelPerm n) → Fin n → ℝ)
      (hM : ∀ p r, M p r ≤ O .upper r.val p + O .lower r.val p)
      (hH0 : ∀ p r, 0 ≤ Hrank p r)
      (hLate : ∀ p r, (n : ℝ) / 2 ≤ Shao.energy p.1 → r ∈ lateSet → M p r ≤ Hrank p r)
      (p : Shao.Path n × LabelPerm n) :
      (∑ r : Fin n, M p r) ≤ base p + ∑ r ∈ lateSet, Hrank p r := by
    by_cases hhigh : (n : ℝ) / 2 ≤ Shao.energy p.1
    · have hLowFalse : ¬Shao.energy p.1 < (n : ℝ) / 2 := not_lt_of_ge hhigh
      have hh := Finset.sum_le_sum (s := Finset.univ) fun r _ =>
        show M p r ≤
          (if 160000 * (r.val + 1 : ℝ) ≤ (n : ℝ) then O .upper r.val p + O .lower r.val p else 0) +
          (if ¬160000 * (r.val + 1 : ℝ) ≤ (n : ℝ) then Hrank p r else 0) from by
          by_cases he : 160000 * (r.val + 1 : ℝ) ≤ (n : ℝ)
          · simpa only [he, not_true_eq_false, if_pos, if_false, add_zero] using hM p r
          · simpa only [he, not_false_eq_true, if_false, if_true, zero_add] using
              hLate p r hhigh (Finset.mem_filter.2 ⟨Finset.mem_univ r, he⟩)
      rw [Finset.sum_add_distrib] at hh
      simpa only [base, low, earlyHigh, if_neg hLowFalse, if_pos hhigh, zero_add,
        earlyOrdinary, earlySet, lateSet, Finset.sum_filter] using hh
    · have hlow : Shao.energy p.1 < (n : ℝ) / 2 := lt_of_not_ge hhigh
      have hh := Finset.sum_le_sum (s := Finset.univ) fun r _ => hM p r
      have hMOrd : (∑ r : Fin n, M p r) ≤ ordinary p := by
        dsimp only [ordinary]
        rw [← Fin.sum_univ_eq_sum_range (fun r => O .upper r p + O .lower r p) n]
        exact hh
      have hRest0 : 0 ≤ ∑ r ∈ lateSet, Hrank p r := Finset.sum_nonneg fun r _ => hH0 p r
      simpa only [base, low, earlyHigh, if_pos hlow, if_neg hhigh, add_zero] using
        hMOrd.trans (le_add_of_nonneg_right hRest0)
  have hAPrior0 (j : ℕ) (s q : ℝ) (v : Shao.Path j) : 0 ≤ APrior j s q v := by
    dsimp only [APrior]
    split_ifs
    · exact hD0 j (s • v)
    · exact le_rfl
  have hAPriorD (j : ℕ) (s q : ℝ) (v : Shao.Path j) : APrior j s q v ≤ D j (s • v) := by
    dsimp only [APrior]
    split_ifs
    · exact le_rfl
    · exact hD0 j (s • v)
  have hAPriorM (j : ℕ) (s : ℝ) : Measurable
      (fun p : Shao.Path j × Shao.Path (n - j) => APrior j s (Shao.energy p.2) p.1) := by
    have hsm : Measurable (fun p : Shao.Path j × Shao.Path (n - j) => s • p.1) :=
      (hSignM j s).comp measurable_fst
    have hdm := (hDm j).comp hsm
    have hfm : Measurable (fun p : Shao.Path j × Shao.Path (n - j) =>
        F j (Shao.energy p.2) (s • p.1)) :=
      ((Shao.measurable_prefixSum j).comp hsm).sub
        (measurable_const.mul ((((Shao.measurable_energy.comp hsm).add
          (Shao.measurable_energy.comp measurable_snd)).max measurable_const).sqrt))
    exact Measurable.ite (((measurableSet_le measurable_const hfm).inter
      (measurableSet_le hfm hdm)).inter
        (measurableSet_le measurable_const ((hWitnessM j).comp hsm))) hdm measurable_const
  let EnvPrior : MonitoredDomain → Fin n → Shao.Path n → ℝ := fun J r v =>
    APrior (r.val + 1) (Shao.C2.ActualOneWallRecordEnvelope.oneWallSign J)
      (Shao.energy (Spitzer.tail v (r.val + 1) (by omega)))
      (Spitzer.head v (r.val + 1) (by omega)) *
        W (n - (r.val + 1)) (Spitzer.tail v (r.val + 1) (by omega))
  have hEnvPrior (J : MonitoredDomain) (r : Fin n) (hr : r ∈ lateSet) (hx400 : 400 ≤ x) :
      Measurable (EnvPrior J r) ∧ Integrable (EnvPrior J r) P ∧
      (∀ v, 0 ≤ EnvPrior J r v) ∧
      (∫ v, EnvPrior J r v ∂P) ≤ CWRS * beta / (r.val + 1 : ℝ) * priorFactor *
        (∫ u, W (n - (r.val + 1)) u ∂law (n - (r.val + 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      hBlock (r.val + 1) (by omega) _ (hSignWall J) (APrior (r.val + 1) _)
        (hAPriorM _ _) (hAPrior0 _ _) (hAPriorD _ _) _
        (hW.1 (n - (r.val + 1))).1 (hW.1 (n - (r.val + 1))).2.1
        (hW.1 (n - (r.val + 1))).2.2.1 _
        (hPriorPrefix (r.val + 1) (by omega) (by omega)
          (by simpa only [Nat.cast_add, Nat.cast_one] using hLateMember r hr)
            hx400 _ (hSignWall J))
  have hEnvPrior0 (J : MonitoredDomain) (r : Fin n) (v : Shao.Path n) : 0 ≤ EnvPrior J r v :=
    mul_nonneg (hAPrior0 _ _ _ _) ((hW.1 _).2.2.1 _)
  have hActualPriorDom (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower)
      (p : Shao.Path n × LabelPerm n) (r : Fin n) (hhigh : (n : ℝ) / 2 ≤ Shao.energy p.1) :
      (if Shao.C2.ActualOneWallRecordEnvelope.oppositePrefixHit J p.1 x r p.2
        then O J r.val p else 0) ≤ 6 * EnvPrior J r (randomReorder p) := by
    have hh := Shao.C2.ActualOneWallRecordEnvelope.actual_onewall_prior_hit_record_envelope
      J hJ p.1 x beta hx0 hbeta (nu p.1) r p.2 (hcap p.1 p.2)
    dsimp only at hh
    by_cases hactive : Shao.C2.ActualOneWallRecordEnvelope.recordStrip J p.1 x r p.2 ∧
        3 * actualWall p.1 x ≤ Shao.C2.ActualOneWallRecordEnvelope.circularWitness
          (Shao.C2.ActualOneWallRecordEnvelope.oneWallSign J •
            Spitzer.head (Spitzer.reorder p.1 p.2) (r.val + 1) (by omega))
    · rw [if_pos hactive] at hh
      have hWall : witnessLevel ≤ 3 * actualWall p.1 x := by
        dsimp only [witnessLevel, actualWall]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt hhigh) (show 0 ≤ 3 * x by positivity)
      have hOurMark := And.intro ((hActualStrip J p.1 p.2 r hhigh).mp hactive.1)
        (hWall.trans hactive.2)
      have he : EnvPrior J r (randomReorder p) =
          Shao.C2.ActualOneWallRecordEnvelope.recordIncrement J p.1 r p.2 *
            Shao.C2.ActualOneWallRecordEnvelope.ordinaryFutureWeight p.1 beta (r.val + 1) p.2 := by
        dsimp only [EnvPrior, APrior, randomReorder]
        rw [if_pos hOurMark, hDRecord, ← hOrdinaryFuture]
      rw [he]
      nlinarith only [hh]
    · rw [if_neg hactive] at hh
      nlinarith only [hh, hEnvPrior0 J r (randomReorder p)]
  have hLateSum (f : Fin n → ℝ) (g : ℕ → ℝ) (Cg factor CV : ℝ)
      (hCg : 0 ≤ Cg) (hfactor : 0 ≤ factor) (hg0 : ∀ t, 0 ≤ g t)
      (hEach : ∀ r, r ∈ lateSet →
        f r ≤ Cg * beta / (r.val + 1 : ℝ) * factor * g (n - (r.val + 1)))
      (hGrid : (∑ r : Fin n, g (n - (r.val + 1))) ≤ CV * Real.sqrt (n : ℝ)) :
      (∑ r ∈ lateSet, f r) ≤ 160000 * Cg * CV * delta * factor := by
    have hCoeff (r : Fin n) (hr : r ∈ lateSet) :
        Cg * beta / (r.val + 1 : ℝ) ≤ 160000 * Cg * beta / (n : ℝ) := by
      apply (div_le_div_iff₀ (by positivity : 0 < (r.val + 1 : ℝ)) hnr).2
      have hh := mul_le_mul_of_nonneg_left (hLateMember r hr).le
        (mul_nonneg hCg hbeta.le)
      nlinarith only [hh]
    calc
      _ ≤ ∑ r ∈ lateSet,
          (160000 * Cg * beta / (n : ℝ) * factor) * g (n - (r.val + 1)) := by
        apply Finset.sum_le_sum
        intro r hr
        exact (hEach r hr).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hCoeff r hr) hfactor) (hg0 _))
      _ = (160000 * Cg * beta / (n : ℝ) * factor) *
          (∑ r ∈ lateSet, g (n - (r.val + 1))) := by rw [Finset.mul_sum]
      _ ≤ (160000 * Cg * beta / (n : ℝ) * factor) *
          (∑ r : Fin n, g (n - (r.val + 1))) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun r _ _ => hg0 _)) (by positivity)
      _ ≤ (160000 * Cg * beta / (n : ℝ) * factor) * (CV * Real.sqrt (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hGrid (by positivity)
      _ = 160000 * Cg * CV * (beta / (n : ℝ) * Real.sqrt (n : ℝ)) * factor := by ring
      _ = _ := by rw [hBetaRate]
  have hPriorEnvSum (J : MonitoredDomain) (hx400 : 400 ≤ x) :
      (∑ r ∈ lateSet, ∫ v, EnvPrior J r v ∂P) ≤ 160000 * CWRS * CW * delta * priorFactor :=
    hLateSum _ (fun t => ∫ u, W t u ∂law t) CWRS priorFactor CW hCWRS0.le
      (by dsimp only [priorFactor]; positivity) hW0Int
      (fun r hr => (hEnvPrior J r hr hx400).2.2.2) hWReindex
  let GPrior : Shao.Path n → ℝ := fun v =>
    ∑ r ∈ lateSet, (EnvPrior .upper r v + EnvPrior .lower r v)
  have hGPriorM (hx400 : 400 ≤ x) : Measurable GPrior := by
    apply Finset.measurable_sum
    intro r hr
    exact ((hEnvPrior .upper r hr hx400).1).add (hEnvPrior .lower r hr hx400).1
  have hGPriorI (hx400 : 400 ≤ x) : Integrable GPrior P := by
    apply integrable_finsetSum
    intro r hr
    exact ((hEnvPrior .upper r hr hx400).2.1).add (hEnvPrior .lower r hr hx400).2.1
  have hGPriorPay (hx400 : 400 ≤ x) : (∫ v, GPrior v ∂P) ≤
      320000 * CWRS * CW * delta * priorFactor := by
    dsimp only [GPrior]
    rw [hPairedIntegral lateSet (EnvPrior .upper) (EnvPrior .lower)
      (fun r hr => (hEnvPrior .upper r hr hx400).2.1)
      (fun r hr => (hEnvPrior .lower r hr hx400).2.1)]
    convert add_le_add (hPriorEnvSum .upper hx400) (hPriorEnvSum .lower hx400) using 1 <;> ring
  have hPriorDom (p : Shao.Path n × LabelPerm n) :
      prior p ≤ base p + 6 * GPrior (randomReorder p) := by
    let M : (Shao.Path n × LabelPerm n) → Fin n → ℝ := fun p r =>
      (if Shao.C2.ActualOneWallRecordEnvelope.oppositePrefixHit .upper p.1 x r p.2
        then O .upper r.val p else 0) +
      (if Shao.C2.ActualOneWallRecordEnvelope.oppositePrefixHit .lower p.1 x r p.2
        then O .lower r.val p else 0)
    have hM (p : Shao.Path n × LabelPerm n) (r : Fin n) : M p r ≤ O .upper r.val p + O .lower r.val p := by
      dsimp only [M]
      split_ifs <;> linarith only [hO0 .upper (Or.inl rfl) p r, hO0 .lower (Or.inr rfl) p r]
    have hh := hBaseDom M (fun p r => 6 * (EnvPrior .upper r (randomReorder p) +
        EnvPrior .lower r (randomReorder p))) hM
      (fun p r => mul_nonneg (by norm_num)
        (add_nonneg (hEnvPrior0 .upper r (randomReorder p)) (hEnvPrior0 .lower r (randomReorder p))))
      (fun p r hhigh _ => by
        have hu := hActualPriorDom .upper (Or.inl rfl) p r hhigh
        have hl := hActualPriorDom .lower (Or.inr rfl) p r hhigh
        dsimp only [M]
        nlinarith only [hu, hl]) p
    convert hh using 1
    dsimp only [GPrior]
    rw [Finset.mul_sum]
  let VFuture : (t : ℕ) → Shao.Path t → ℝ := fun t u => if m ≤ t then future t u else 0
  have hFutureM (t : ℕ) : Measurable (future t) := by
    exact Measurable.ite
      ((measurableSet_lt measurable_const Shao.measurable_energy).inter
        ((measurableSet_le measurable_const Shao.measurable_energy).inter
          (measurableSet_le (measurable_const.mul Shao.measurable_energy.sqrt)
            (continuous_abs.measurable.comp (Shao.measurable_prefixSum t)))))
      ((measurable_const.div Shao.measurable_energy.sqrt).mul
        ((measurable_const.add ((continuous_abs.measurable.comp (Shao.measurable_prefixSum t)).div
          Shao.measurable_energy.sqrt)).pow_const 2)) measurable_const
  have hVFutureM (t : ℕ) : Measurable (VFuture t) := by
    dsimp only [VFuture]
    by_cases ht : m ≤ t <;> simp only [ht, if_true, if_false]
    · exact hFutureM t
    · exact measurable_const
  have hVFutureI (t : ℕ) : Integrable (VFuture t) (law t) := by
    dsimp only [VFuture]
    by_cases ht : m ≤ t <;> simp only [ht, if_true, if_false]
    · exact hFutureInt t
    · exact integrable_zero _ _ _
  have hVFuture0 (t : ℕ) (u : Shao.Path t) : 0 ≤ VFuture t u := by
    dsimp only [VFuture]
    split_ifs
    · exact hFuture0 t u
    · exact le_rfl
  have hVFuturePoint (t : ℕ) :
      (∫ u, VFuture t u ∂law t) ≤ CR * Shao.standardNormalTail x * (1 / Real.sqrt (t : ℝ)) := by
    by_cases ht : m ≤ t
    · have hh := hFutureBound t ht
      have he : Real.rpow (t : ℝ) (-1 / 2 : ℝ) = 1 / Real.sqrt (t : ℝ) := by
        simp only [Real.rpow_eq_pow]
        rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
          Real.rpow_neg (Nat.cast_nonneg t), ← Real.sqrt_eq_rpow, one_div]
      rw [he] at hh
      simpa only [VFuture, if_pos ht, mul_assoc, mul_left_comm, mul_comm] using hh
    · simp only [VFuture, if_neg ht, integral_zero]
      exact mul_nonneg (mul_nonneg hCR.le (Shao.standardNormalTail_basic.2.2.1 x).1.le) (by positivity)
  have hHarmonic (N : ℕ) :
      (∑ t ∈ Finset.range N, 1 / Real.sqrt ((t + 1 : ℕ) : ℝ)) ≤ 2 * Real.sqrt (N : ℝ) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hr : 0 < Real.sqrt ((N + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
      have hstep : 1 / Real.sqrt ((N + 1 : ℕ) : ℝ) ≤
          2 * (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) := by
        norm_num only [Nat.cast_add, Nat.cast_one] at hr ⊢
        apply (div_le_iff₀ hr).2
        have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ (N : ℝ) + 1 by positivity)
        have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ (N : ℝ) by positivity)
        nlinarith only [h1, h2,
          sq_nonneg (Real.sqrt ((N : ℝ) + 1) - Real.sqrt (N : ℝ))]
      linarith only [ih, hstep]
  have hHarmonicZero (N : ℕ) :
      (∑ t ∈ Finset.range N, 1 / Real.sqrt (t : ℝ)) ≤ 2 * Real.sqrt (N : ℝ) := by
    cases N with
    | zero => simp
    | succ N =>
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, Real.sqrt_zero, div_zero, zero_add, add_zero]
      apply (hHarmonic N).trans
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by push_cast; linarith)) (by norm_num)
  have hReverseSum (g : ℕ → ℝ) :
      (∑ r : Fin n, g (n - (r.val + 1))) = ∑ t ∈ Finset.range n, g t := by
    have hh := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n)) (fun t : Fin n => g t.val)
    change (∑ r : Fin n, g (Fin.revPerm r).val) = ∑ r : Fin n, g r.val at hh
    have hv (r : Fin n) : (Fin.revPerm r).val = n - (r.val + 1) := by
      change (Fin.rev r).val = n - (r.val + 1)
      rfl
    simp only [hv] at hh
    exact hh.trans (Fin.sum_univ_eq_sum_range g n)
  have hVFutureGrid :
      (∑ r : Fin n, ∫ u, VFuture (n - (r.val + 1)) u ∂law (n - (r.val + 1))) ≤
        (2 * CR * Shao.standardNormalTail x) * Real.sqrt (n : ℝ) := by
    rw [hReverseSum (fun t => ∫ u : Shao.Path t, VFuture t u ∂law t)]
    calc
      _ ≤ ∑ t ∈ Finset.range n, CR * Shao.standardNormalTail x * (1 / Real.sqrt (t : ℝ)) :=
        Finset.sum_le_sum fun t _ => hVFuturePoint t
      _ = (CR * Shao.standardNormalTail x) * (∑ t ∈ Finset.range n, 1 / Real.sqrt (t : ℝ)) := by
        rw [Finset.mul_sum]
      _ ≤ (CR * Shao.standardNormalTail x) * (2 * Real.sqrt (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (hHarmonicZero n)
          (mul_nonneg hCR.le (Shao.standardNormalTail_basic.2.2.1 x).1.le)
      _ = _ := by ring
  let EnvRare : MonitoredDomain → Fin n → Shao.Path n → ℝ := fun J r v =>
    AOrd (r.val + 1) (Shao.C2.ActualOneWallRecordEnvelope.oneWallSign J)
      (Shao.energy (Spitzer.tail v (r.val + 1) (by omega)))
      (Spitzer.head v (r.val + 1) (by omega)) *
        VFuture (n - (r.val + 1)) (Spitzer.tail v (r.val + 1) (by omega))
  have hEnvRare (J : MonitoredDomain) (r : Fin n) :
      Measurable (EnvRare J r) ∧ Integrable (EnvRare J r) P ∧
      (∀ v, 0 ≤ EnvRare J r v) ∧
      (∫ v, EnvRare J r v ∂P) ≤ CU * beta / (r.val + 1 : ℝ) *
        (∫ u, VFuture (n - (r.val + 1)) u ∂law (n - (r.val + 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      hBlock (r.val + 1) (by omega) _ (hSignWall J) (AOrd (r.val + 1) _)
        (hAOrdM _ _) (hAOrd0 _ _) (hAOrdD _ _) _ (hVFutureM _) (hVFutureI _)
        (hVFuture0 _) _ (hPrefixOrdinary (r.val + 1) (by omega) (by omega) _ (hSignWall J))
  have hActualRareDom (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower)
      (p : Shao.Path n × LabelPerm n) (r : Fin n) (hhigh : (n : ℝ) / 2 ≤ Shao.energy p.1) :
      (if r.val < tau p.1 p.2 then
        if 3 * x * Real.sqrt (remainingEnergy p.1 r.val p.2) / 2 ≤
            |remainingSum p.1 r.val p.2| then O J r.val p else 0 else 0) ≤
        6 * EnvRare J r (randomReorder p) := by
    have hh := hBeforeBadEnvelope J hJ p r
    by_cases hr : Shao.C2.ActualOneWallRecordEnvelope.recordStrip J p.1 x r p.2
    · rw [if_pos hr] at hh
      have he : EnvRare J r (randomReorder p) =
          Shao.C2.ActualOneWallRecordEnvelope.recordIncrement J p.1 r p.2 *
            Shao.C2.ActualOneWallRecordEnvelope.badFutureWeight p.1 H m x (r.val + 1) p.2 := by
        dsimp only [EnvRare, AOrd, randomReorder]
        rw [Set.indicator_of_mem ((hActualStrip J p.1 p.2 r hhigh).mp hr), hDRecord, hBadFuture]
      rw [he]
      nlinarith only [hh]
    · rw [if_neg hr] at hh
      nlinarith only [hh, (hEnvRare J r).2.2.1 (randomReorder p)]
  have hRareEnvSum (J : MonitoredDomain) :
      (∑ r ∈ lateSet, ∫ v, EnvRare J r v ∂P) ≤
        320000 * CU * CR * delta * Shao.standardNormalTail x := by
    have hh := hLateSum _ (fun t => ∫ u, VFuture t u ∂law t) CU 1
      (2 * CR * Shao.standardNormalTail x) hCU0.le (by norm_num)
      (fun t => integral_nonneg (hVFuture0 t))
      (fun r _ => by simpa only [mul_one] using (hEnvRare J r).2.2.2) hVFutureGrid
    convert hh using 1 <;> ring
  let GRare : Shao.Path n → ℝ := fun v =>
    ∑ r ∈ lateSet, (EnvRare .upper r v + EnvRare .lower r v)
  have hGRareM : Measurable GRare := by
    apply Finset.measurable_sum
    intro r _
    exact ((hEnvRare .upper r).1).add (hEnvRare .lower r).1
  have hGRareI : Integrable GRare P := by
    apply integrable_finsetSum
    intro r _
    exact ((hEnvRare .upper r).2.1).add (hEnvRare .lower r).2.1
  have hGRarePay : (∫ v, GRare v ∂P) ≤
      640000 * CU * CR * delta * Shao.standardNormalTail x := by
    dsimp only [GRare]
    rw [hPairedIntegral lateSet (EnvRare .upper) (EnvRare .lower)
      (fun r _ => (hEnvRare .upper r).2.1) (fun r _ => (hEnvRare .lower r).2.1)]
    convert add_le_add (hRareEnvSum .upper) (hRareEnvSum .lower) using 1 <;> ring
  run_tac
    let formulaName := Lean.mkPrivateNameCore "Shao.Probability.GaussianTail".toName
      "Shao.density_formula".toName
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent "hDensityFormula".toName) := $(Lean.mkIdent formulaName)))
  have hGaussianLower (R : ℝ) (hR : (1 + x) * R ≤ Real.exp (-x ^ 2 / 2)) :
      R ≤ 3 * Shao.standardNormalTail x := by
    have hplus : 0 < 1 + x := by linarith only [hx]
    have hpiroot : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    have hpi3 : Real.sqrt (2 * Real.pi) ≤ 3 := by
      nlinarith only [Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity),
        Real.pi_lt_four, Real.sqrt_nonneg (2 * Real.pi)]
    have hphi : Real.exp (-x ^ 2 / 2) ≤ 3 * Shao.standardNormalDensity x := by
      have hh : 1 ≤ 3 / Real.sqrt (2 * Real.pi) :=
        (le_div_iff₀ hpiroot).2 (by simpa only [one_mul] using hpi3)
      have hh' := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-x ^ 2 / 2)).le
      rw [hDensityFormula x]
      convert hh' using 1 <;> ring
    have hh : R ≤ 3 * Shao.standardNormalDensity x / (1 + x) := by
      apply (le_div_iff₀ hplus).2
      nlinarith only [hR, hphi]
    apply hh.trans
    have hm := mul_le_mul_of_nonneg_left (Shao.standardNormal_mills_bounds x hx0.le).1
      (by norm_num : (0 : ℝ) ≤ 3)
    convert hm using 1 <;> ring
  have hExp2Tail : Real.exp (-2 * x ^ 2) ≤ 3 * Shao.standardNormalTail x := by
    apply hGaussianLower
    have hratio : (1 + x) * Real.exp (-3 * x ^ 2 / 2) ≤ 1 := by
      calc
        _ ≤ Real.exp x * Real.exp (-3 * x ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right
            (by simpa only [add_comm] using Real.add_one_le_exp x) (Real.exp_pos _).le
        _ = Real.exp (x - 3 * x ^ 2 / 2) := by rw [← Real.exp_add]; congr 1 <;> ring
        _ ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith only [hx, sq_nonneg (x - 1)])
    have he : Real.exp (-2 * x ^ 2) =
        Real.exp (-x ^ 2 / 2) * Real.exp (-3 * x ^ 2 / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    nlinarith only [mul_le_mul_of_nonneg_left hratio (Real.exp_pos (-x ^ 2 / 2)).le]
  have hPolyTail : (1 + 2 * x) ^ 5 * Real.exp (-(11 / 5 : ℝ) * x ^ 2) ≤
      3 * Shao.standardNormalTail x := by
    apply hGaussianLower
    have hPoly : (1 + x) * (1 + 2 * x) ^ 5 ≤ 32 * (1 + x) ^ 6 := by
      have hp := pow_le_pow_left₀ (show 0 ≤ 1 + 2 * x by positivity)
        (show 1 + 2 * x ≤ 2 * (1 + x) by linarith) 5
      have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1 + x by positivity)
      convert hh using 1 <;> ring
    have hPolyExp : (1 + x) ^ 6 ≤ Real.exp (6 * x) := by
      have hh := pow_le_pow_left₀ (show 0 ≤ 1 + x by positivity)
        (show 1 + x ≤ Real.exp x by simpa only [add_comm] using Real.add_one_le_exp x) 6
      rw [← Real.exp_nat_mul] at hh
      simpa only [Nat.cast_ofNat] using hh
    have h32 : (32 : ℝ) ≤ Real.exp 32 := by
      have hh := Real.add_one_le_exp (32 : ℝ)
      linarith only [hh]
    have hratio : (1 + x) * (1 + 2 * x) ^ 5 * Real.exp (-(17 / 10 : ℝ) * x ^ 2) ≤ 1 := by
      calc
        _ ≤ 32 * (1 + x) ^ 6 * Real.exp (-(17 / 10 : ℝ) * x ^ 2) :=
          mul_le_mul_of_nonneg_right hPoly (Real.exp_pos _).le
        _ ≤ Real.exp 32 * Real.exp (6 * x) * Real.exp (-(17 / 10 : ℝ) * x ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul h32 hPolyExp (by positivity) (Real.exp_pos _).le)
            (Real.exp_pos _).le
        _ = Real.exp (32 + 6 * x - (17 / 10 : ℝ) * x ^ 2) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        _ ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith only [hx, sq_nonneg (x - 16)])
    have he : Real.exp (-(11 / 5 : ℝ) * x ^ 2) =
        Real.exp (-x ^ 2 / 2) * Real.exp (-(17 / 10 : ℝ) * x ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    nlinarith only [mul_le_mul_of_nonneg_left hratio (Real.exp_pos (-x ^ 2 / 2)).le]
  have hPriorFactorTail : priorFactor ≤
      3 * Real.exp (8 * CWRS + CWRS / 100) * Shao.standardNormalTail x := by
    have hh := mul_le_mul_of_nonneg_left hPolyTail (Real.exp_pos (8 * CWRS + CWRS / 100)).le
    dsimp only [priorFactor]
    nlinarith only [hh]
  have hOppM (J : MonitoredDomain) (r : Fin n) : MeasurableSet
      {p : Shao.Path n × LabelPerm n |
        Shao.C2.ActualOneWallRecordEnvelope.oppositePrefixHit J p.1 x r p.2} := by
    simp only [Shao.C2.ActualOneWallRecordEnvelope.oppositePrefixHit, Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro k
    by_cases hk : k ≤ r.val
    · simp only [hk, true_and]
      exact measurableSet_le
        (measurable_const.mul ((Shao.measurable_prefixSum k).comp hReorderM))
        ((measurable_const.mul (Shao.measurable_energy.comp measurable_fst).sqrt).neg)
    · simp only [hk, false_and, Set.setOf_false, MeasurableSet.empty]
  have hBadM (r : ℕ) : MeasurableSet {p : Shao.Path n × LabelPerm n |
      3 * x * Real.sqrt (remainingEnergy p.1 r p.2) / 2 ≤ |remainingSum p.1 r p.2|} := by
    have hEM : Measurable (fun p : Shao.Path n × LabelPerm n => remainingEnergy p.1 r p.2) :=
      (Shao.measurable_energy.comp measurable_fst).sub ((Shao.measurable_prefixSquares r).comp hReorderM)
    have hSM : Measurable (fun p : Shao.Path n × LabelPerm n => remainingSum p.1 r p.2) :=
      ((Shao.measurable_prefixSum n).comp measurable_fst).sub ((Shao.measurable_prefixSum r).comp hReorderM)
    exact measurableSet_le ((measurable_const.mul hEM.sqrt).div_const 2)
      (continuous_abs.measurable.comp hSM)
  have hPriorI : Integrable prior (revealLaw P) := by
    apply integrable_finsetSum
    intro r _
    exact (((hParts .upper (Or.inl rfl) nu hnum).2.1 r.val).2.indicator (hOppM .upper r)).add
      (((hParts .lower (Or.inr rfl) nu hnum).2.1 r.val).2.indicator (hOppM .lower r))
  have hBadI : Integrable bad (revealLaw P) := by
    apply integrable_finsetSum
    intro r _
    exact ((((hParts .upper (Or.inl rfl) nu hnum).2.1 r).2.add
      ((hParts .lower (Or.inr rfl) nu hnum).2.1 r).2).indicator (hBadM r))
  have hPriorOrdDom (p : Shao.Path n × LabelPerm n) : prior p ≤ ordinary p := by
    have hh := Finset.sum_le_sum (s := Finset.univ) fun r _ =>
      show (if Shao.C2.ActualOneWallRecordEnvelope.oppositePrefixHit .upper p.1 x r p.2
          then O .upper r.val p else 0) +
          (if Shao.C2.ActualOneWallRecordEnvelope.oppositePrefixHit .lower p.1 x r p.2
          then O .lower r.val p else 0) ≤ O .upper r.val p + O .lower r.val p from by
        split_ifs <;> linarith only [hO0 .upper (Or.inl rfl) p r, hO0 .lower (Or.inr rfl) p r]
    dsimp only [ordinary]
    rw [← Fin.sum_univ_eq_sum_range (fun r => O .upper r p + O .lower r p) n]
    exact hh
  have hPriorPay : (∫ p, prior p ∂revealLaw P) ≤ CP * delta * Shao.standardNormalTail x := by
    by_cases hsmall : x ≤ 400
    · have hPsi : Shao.standardNormalTail 400 ≤ Shao.standardNormalTail x :=
        Shao.standardNormalTail_basic.1 hsmall
      have hCPCompare : CO / Shao.standardNormalTail 400 ≤ CP := by
        have hrest : 0 ≤ 3 * (CL + CEarly) +
            5760000 * CWRS * CW * Real.exp (8 * CWRS + CWRS / 100) + 1 := by
          dsimp only [CEarly]
          positivity
        dsimp only [CP]
        linarith only [hrest]
      calc
        _ ≤ ∫ p, ordinary p ∂revealLaw P := integral_mono hPriorI hOrdI hPriorOrdDom
        _ ≤ CO * delta := hOrdinaryPay
        _ = CO / Shao.standardNormalTail 400 * delta * Shao.standardNormalTail 400 := by
          field_simp [ne_of_gt hPsi400]
        _ ≤ CO / Shao.standardNormalTail 400 * delta * Shao.standardNormalTail x :=
          mul_le_mul_of_nonneg_left hPsi (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCPCompare hdelta) (Shao.standardNormalTail_basic.2.2.1 x).1.le
    · have hx400 : 400 ≤ x := le_of_lt (lt_of_not_ge hsmall)
      have hTransfer : (∫ p, GPrior (randomReorder p) ∂revealLaw P) = ∫ v, GPrior v ∂P := by
        have hh := integral_map hReorderMP.aemeasurable (hGPriorM hx400).aestronglyMeasurable
        rw [hReorderMP.map_eq] at hh
        exact hh.symm
      calc
        _ ≤ ∫ p, base p + 6 * GPrior (randomReorder p) ∂revealLaw P :=
          integral_mono hPriorI (hBaseI.add
            ((hReorderMP.integrable_comp_of_integrable (hGPriorI hx400)).const_mul 6)) hPriorDom
        _ = (∫ p, base p ∂revealLaw P) + 6 * (∫ v, GPrior v ∂P) := by
          rw [hIntegralAdd base (fun p => 6 * GPrior (randomReorder p))
              hBaseI ((hReorderMP.integrable_comp_of_integrable (hGPriorI hx400)).const_mul 6),
            integral_const_mul, hTransfer]
        _ ≤ (CL + CEarly) * delta * Real.exp (-2 * x ^ 2) +
            6 * (320000 * CWRS * CW * delta * priorFactor) :=
          add_le_add hBasePay (mul_le_mul_of_nonneg_left (hGPriorPay hx400) (by norm_num))
        _ ≤ (CL + CEarly) * delta * (3 * Shao.standardNormalTail x) +
            6 * (320000 * CWRS * CW * delta *
              (3 * Real.exp (8 * CWRS + CWRS / 100) * Shao.standardNormalTail x)) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hExp2Tail (by dsimp only [CEarly]; positivity)
          · exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hPriorFactorTail (by positivity)) (by norm_num)
        _ = (3 * (CL + CEarly) + 5760000 * CWRS * CW * Real.exp (8 * CWRS + CWRS / 100)) *
            delta * Shao.standardNormalTail x := by ring
        _ ≤ _ := by
          have hh : 0 ≤ CO / Shao.standardNormalTail 400 + 1 := by positivity
          have hcoeff : 3 * (CL + CEarly) + 5760000 * CWRS * CW * Real.exp (8 * CWRS + CWRS / 100) ≤ CP := by
            dsimp only [CP]
            linarith only [hh]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff hdelta)
            (Shao.standardNormalTail_basic.2.2.1 x).1.le
  have hBadDom (p : Shao.Path n × LabelPerm n) :
      bad p ≤ base p + 6 * GRare (randomReorder p) + tailCost p := by
    let M : (Shao.Path n × LabelPerm n) → Fin n → ℝ := fun p r =>
      if 3 * x * Real.sqrt (remainingEnergy p.1 r.val p.2) / 2 ≤
          |remainingSum p.1 r.val p.2| then O .upper r.val p + O .lower r.val p else 0
    let T : (Shao.Path n × LabelPerm n) → Fin n → ℝ := fun p r =>
      if tau p.1 p.2 ≤ r.val then O .upper r.val p + O .lower r.val p else 0
    let Hrank : (Shao.Path n × LabelPerm n) → Fin n → ℝ := fun p r =>
      6 * (EnvRare .upper r (randomReorder p) + EnvRare .lower r (randomReorder p)) + T p r
    have hM (q : Shao.Path n × LabelPerm n) (r : Fin n) : M q r ≤ O .upper r.val q + O .lower r.val q := by
      dsimp only [M]
      split_ifs
      · exact le_rfl
      · exact add_nonneg (hO0 .upper (Or.inl rfl) q r) (hO0 .lower (Or.inr rfl) q r)
    have hT0 (q : Shao.Path n × LabelPerm n) (r : Fin n) : 0 ≤ T q r := by
      dsimp only [T]
      split_ifs
      · exact add_nonneg (hO0 .upper (Or.inl rfl) q r) (hO0 .lower (Or.inr rfl) q r)
      · exact le_rfl
    have hH0 (q : Shao.Path n × LabelPerm n) (r : Fin n) : 0 ≤ Hrank q r :=
      add_nonneg (mul_nonneg (by norm_num) (add_nonneg
        ((hEnvRare .upper r).2.2.1 _) ((hEnvRare .lower r).2.2.1 _))) (hT0 q r)
    have hLate (q : Shao.Path n × LabelPerm n) (r : Fin n)
        (hhigh : (n : ℝ) / 2 ≤ Shao.energy q.1) (_hr : r ∈ lateSet) : M q r ≤ Hrank q r := by
      by_cases ht : r.val < tau q.1 q.2
      · have hu := hActualRareDom .upper (Or.inl rfl) q r hhigh
        have hl := hActualRareDom .lower (Or.inr rfl) q r hhigh
        rw [if_pos ht] at hu hl
        dsimp only [M, Hrank, T]
        rw [if_neg (not_le_of_gt ht), add_zero]
        by_cases hbad : 3 * x * Real.sqrt (remainingEnergy q.1 r.val q.2) / 2 ≤
            |remainingSum q.1 r.val q.2|
        · rw [if_pos hbad] at hu hl ⊢
          nlinarith only [hu, hl]
        · rw [if_neg hbad]
          exact mul_nonneg (by norm_num) (add_nonneg
            ((hEnvRare .upper r).2.2.1 _) ((hEnvRare .lower r).2.2.1 _))
      · have hafter : tau q.1 q.2 ≤ r.val := le_of_not_gt ht
        have hh := hM q r
        have he := mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) (add_nonneg
          ((hEnvRare .upper r).2.2.1 (randomReorder q))
          ((hEnvRare .lower r).2.2.1 (randomReorder q)))
        dsimp only [Hrank, T]
        rw [if_pos hafter]
        linarith only [hh, he]
    have hh := hBaseDom M Hrank hM hH0 hLate p
    have hmEq : (∑ r : Fin n, M p r) = bad p := by
      dsimp only [M, bad]
      exact Fin.sum_univ_eq_sum_range (fun r =>
        if 3 * x * Real.sqrt (remainingEnergy p.1 r p.2) / 2 ≤
            |remainingSum p.1 r p.2| then O .upper r p + O .lower r p else 0) n
    have hRewrite : (∑ r ∈ lateSet, Hrank p r) =
        6 * GRare (randomReorder p) + (∑ r ∈ lateSet, T p r) := by
      dsimp only [Hrank, GRare]
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    have hTailSubset : (∑ r ∈ lateSet, T p r) ≤ tailNu p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun r _ _ => hT0 p r)
    have hTail := hTailSubset.trans (hTailSourceDom p)
    rw [hmEq, hRewrite] at hh
    linarith only [hh, hTail]
  have hBadPay : (∫ p, bad p ∂revealLaw P) ≤ CB * delta * Shao.standardNormalTail x := by
    have hTransfer : (∫ p, GRare (randomReorder p) ∂revealLaw P) = ∫ v, GRare v ∂P := by
      have hh := integral_map hReorderMP.aemeasurable hGRareM.aestronglyMeasurable
      rw [hReorderMP.map_eq] at hh
      exact hh.symm
    calc
      _ ≤ ∫ p, base p + 6 * GRare (randomReorder p) + tailCost p ∂revealLaw P :=
        integral_mono hBadI ((hBaseI.add
          ((hReorderMP.integrable_comp_of_integrable hGRareI).const_mul 6)).add hTailCostI) hBadDom
      _ = (∫ p, base p ∂revealLaw P) + 6 * (∫ v, GRare v ∂P) + (∫ p, tailCost p ∂revealLaw P) := by
        rw [hIntegralAdd (fun p => base p + 6 * GRare (randomReorder p)) tailCost
            (hBaseI.add ((hReorderMP.integrable_comp_of_integrable hGRareI).const_mul 6)) hTailCostI,
          hIntegralAdd base (fun p => 6 * GRare (randomReorder p))
            hBaseI ((hReorderMP.integrable_comp_of_integrable hGRareI).const_mul 6),
          integral_const_mul, hTransfer]
      _ ≤ (CL + CEarly) * delta * Real.exp (-2 * x ^ 2) +
          6 * (640000 * CU * CR * delta * Shao.standardNormalTail x) +
          CT * delta * Shao.standardNormalTail x :=
        add_le_add (add_le_add hBasePay (mul_le_mul_of_nonneg_left hGRarePay (by norm_num))) hTailCostPay
      _ ≤ (CL + CEarly) * delta * (3 * Shao.standardNormalTail x) +
          6 * (640000 * CU * CR * delta * Shao.standardNormalTail x) +
          CT * delta * Shao.standardNormalTail x := by
        have hh := mul_le_mul_of_nonneg_left hExp2Tail
          (show 0 ≤ (CL + CEarly) * delta by dsimp only [CEarly]; positivity)
        linarith only [hh]
      _ = (3 * (CL + CEarly) + 3840000 * CU * CR + CT) * delta * Shao.standardNormalTail x := by ring
      _ ≤ _ := by
        have hcoeff : 3 * (CL + CEarly) + 3840000 * CU * CR + CT ≤ CB := by
          dsimp only [CB]
          linarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff hdelta)
          (Shao.standardNormalTail_basic.2.2.1 x).1.le
  exact ⟨hOrdinaryPay, hPriorPay, hBadPay⟩

end Shao.Probability.SourceActualFullPositiveOvershoot
