import Shao.Probability.SourceActualFullPositiveOvershoot
import Shao.Probability.SourceActualAdaptiveTerminal
import Shao.C2.ActualAllRetainedDoubleBudget
import Shao.C2.ActualSignedDoubleTelescope
import Shao.C2.AdaptiveRevealCutoff
import Shao.C2.InitialDoubleCompletionBudget
import Shao.Probability.SourceNonresidualBrownian
import Shao.Probability.MeasurablePath
import Shao.Probability.TruncationIntegrals
import Shao.C2.TwoSided
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
noncomputable section
namespace Shao.Probability.SourceActualBoundedRelativeConsumer
open MeasureTheory ProbabilityTheory
open SourcePermutationReveal
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open scoped BigOperators Classical NNReal

local instance labelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

theorem iid_actual_bounded_centered_high_threshold_relative_comparison :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ΩB : Type*} [MeasurableSpace ΩB]
        (Bm : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
        IsBrownianReal Bm PB →
        ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
          (Bcap : ℝ), 0 < Bcap → (∀ᵐ z : ℝ ∂rho, |z| ≤ Bcap) →
          (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
          ∀ (n : ℕ) (hn : 0 < n) (x : ℝ), 16 ≤ x →
            Bcap ≤ Real.sqrt (n : ℝ) / (200 * x) →
            let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
            let delta : ℝ := beta / Real.sqrt (n : ℝ)
            let u : ℝ := delta * (1 + x) ^ 3
            u ≤ 1 / 20000 →
            let normalizedLaw : Measure ℝ :=
              Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) rho
            let R : ℝ := Shao.truncationBudget normalizedLaw n x
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
            let D : Set (Shao.Path n) := Shao.C2.doubleCrossing hn x
            let DB : Set ΩB := {omega |
              (∃ t : BridgeTime, x ≤ Bm ⟨(t : ℝ), t.property.1⟩ omega) ∧
              ∃ t : BridgeTime, Bm ⟨(t : ℝ), t.property.1⟩ omega ≤ -x}
            let Z0 : Shao.Path n → ℝ :=
              Shao.C2.InitialDoubleCompletionBudget.initialDoubleObservable
                (bridgeLaw Bm PB) x
            Integrable (fun z : ℝ => z ^ 2) rho ∧
              Integrable (fun z : ℝ => |z| ^ 3) rho ∧
              0 < delta ∧ R = u ∧
              MeasurableSet D ∧
              Integrable (D.indicator (fun _ : Shao.Path n => (1 : ℝ))) P ∧
              NullMeasurableSet DB PB ∧
              Measurable Z0 ∧ Integrable Z0 P ∧
              (u ≤ Real.exp (-3 * x ^ 2) →
                |P.real D - ∫ a : Shao.Path n, Z0 a ∂P| ≤
                  C * delta * Shao.standardNormalTail x) ∧
              |P.real D - PB.real DB| ≤ C * R * Shao.standardNormalTail x := by
  classical
  obtain ⟨CL, hCL, hRetained⟩ :=
    Shao.C2.ActualAllRetainedDoubleBudget.iid_actual_all_retained_double_absolute_budget
  obtain ⟨CO, hCO, hSeparated⟩ :=
    SourceActualFullPositiveOvershoot.iid_actual_full_signed_separated_budget
  obtain ⟨CT, hCT, hTerminal⟩ :=
    SourceActualAdaptiveTerminal.iid_actual_adaptive_terminal_budget
  obtain ⟨CI, hCI, hInitial⟩ :=
    Shao.C2.InitialDoubleCompletionBudget.original_finite_second_initial_double_completion_budget
  have hNonresidual :=
    SourceNonresidualBrownian.source_centered_bounded_nonresidual_brownian_comparison
      1 (by norm_num)
  dsimp only at hNonresidual
  rcases hNonresidual with ⟨hCabs, hCN, hNonresidual⟩
  simp only [div_one] at hCN hNonresidual
  let CN : ℝ := Real.sqrt (2 * Real.pi) * (2 + 4 * Real.exp 1) +
    4 * Real.sqrt (2 * Real.pi)
  let CS : ℝ := 3 * CT + CL + CO
  have hCNpos : 0 < CN := hCN
  have hCS : 0 < CS := by dsimp only [CS]; positivity
  refine ⟨1 + CS + CI + CN, by positivity, ?_⟩
  intro ΩB _ Bm PB _ hBm rho _ Bcap hBcap hsupport hmean hsecond
    n hn x hx hcap beta delta u hu normalizedLaw R P D DB Z0
  letI : IsProbabilityMeasure P := by dsimp only [P]; infer_instance
  let Q : Measure BridgeNoise := bridgeLaw Bm PB
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw Bm PB hBm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have h2 : Integrable (fun z : ℝ => z ^ 2) rho := by
    apply Integrable.of_bound (by fun_prop) (Bcap ^ 2)
    filter_upwards [hsupport] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z), ← sq_abs z]
    exact pow_le_pow_left₀ (abs_nonneg z) hz 2
  have h3 : Integrable (fun z : ℝ => |z| ^ 3) rho := by
    apply Integrable.of_bound (by fun_prop) (Bcap ^ 3)
    filter_upwards [hsupport] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg z) 3)]
    exact pow_le_pow_left₀ (abs_nonneg z) hz 3
  have hbeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one
      rho h2 h3 hsecond
  have hbeta0 : 0 < beta := by linarith
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hu0 : 0 < u := by dsimp only [u]; positivity
  have hdeltaU : delta ≤ u := by
    have hp : 1 ≤ (1 + x) ^ 3 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + x)
    have hh := mul_le_mul_of_nonneg_left hp hdelta.le
    simpa only [mul_one] using hh
  have hPsi : 0 < Shao.standardNormalTail x := (Shao.standardNormalTail_basic.2.2.1 x).1
  have hScaleM : Measurable (fun z : ℝ => z / Real.sqrt (n : ℝ)) :=
    measurable_id.div_const _
  letI : IsProbabilityMeasure normalizedLaw := by
    dsimp only [normalizedLaw]
    exact (Measure.isProbabilityMeasure_map_iff hScaleM.aemeasurable).mpr inferInstance
  have hNmean : (∫ z : ℝ, z ∂normalizedLaw) = 0 := by
    dsimp only [normalizedLaw]
    rw [integral_map (μ := rho) (φ := fun z : ℝ => z / Real.sqrt (n : ℝ))
        (f := fun z : ℝ => z) hScaleM.aemeasurable (by fun_prop),
      integral_div, hmean, zero_div]
  have hNsecond : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂normalizedLaw) = 1 := by
    dsimp only [normalizedLaw]
    rw [integral_map (μ := rho) (φ := fun z : ℝ => z / Real.sqrt (n : ℝ))
      (f := fun z : ℝ => z ^ 2) hScaleM.aemeasurable (by fun_prop)]
    simp only [div_pow]
    rw [integral_div, hsecond, Real.sq_sqrt hnR.le]
    exact mul_one_div_cancel hnR.ne'
  have hNthird : (n : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂normalizedLaw) = delta := by
    dsimp only [normalizedLaw]
    rw [integral_map (μ := rho) (φ := fun z : ℝ => z / Real.sqrt (n : ℝ))
      (f := fun z : ℝ => |z| ^ 3) hScaleM.aemeasurable (by fun_prop)]
    simp only [abs_div, abs_of_pos hsn, div_pow]
    rw [integral_div]
    change (n : ℝ) * (beta / Real.sqrt (n : ℝ) ^ 3) = beta / Real.sqrt (n : ℝ)
    rw [show Real.sqrt (n : ℝ) ^ 3 = (n : ℝ) * Real.sqrt (n : ℝ) by
      rw [pow_succ, Real.sq_sqrt hnR.le]]
    field_simp [hnR.ne', hsn.ne'] <;> ring
  have hNsupport200 : ∀ᵐ z : ℝ ∂normalizedLaw, |z| ≤ 1 / (200 * x) := by
    apply (ae_map_iff hScaleM.aemeasurable
      (measurableSet_le continuous_abs.measurable measurable_const)).mpr
    filter_upwards [hsupport] with z hz
    rw [abs_div, abs_of_pos hsn]
    calc
      |z| / Real.sqrt (n : ℝ) ≤ Bcap / Real.sqrt (n : ℝ) :=
        div_le_div_of_nonneg_right hz hsn.le
      _ ≤ 1 / (200 * x) := by
        apply (div_le_iff₀ hsn).mpr
        simpa only [div_eq_mul_inv, mul_comm, one_mul] using hcap
  have hNsupport4 : ∀ᵐ z : ℝ ∂normalizedLaw, |z| ≤ 1 / (4 * x) := by
    filter_upwards [hNsupport200] with z hz
    exact hz.trans (one_div_le_one_div_of_le (by positivity) (by nlinarith))
  have hNdata := hNonresidual Bm PB hBm normalizedLaw n hn x hx1
    hNsupport4 hNmean hNsecond
  rcases hNdata with ⟨hN2, hN3, hNbeta, hNsize, hNDM, hNDB, hNbudget, hNpaid⟩
  have hR : R = u := by
    change Shao.truncationBudget normalizedLaw n x = u
    simpa only [hNthird] using hNbudget
  have hDM : MeasurableSet D := Shao.C2.measurableSet_doubleCrossing hn x
  have hDI : Integrable (D.indicator (fun _ : Shao.Path n => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hDM
  have hDB : NullMeasurableSet DB PB := hNDB
  have hZ0M : Measurable Z0 := by
    dsimp only [Z0, Shao.C2.InitialDoubleCompletionBudget.initialDoubleObservable]
    exact Measurable.ite Shao.measurableSet_zeroEnergy measurable_const
      ((Shao.C2.InitialDoubleCompletionKernel.actual_initial_double_completion_kernel
        Bm PB hBm x hx1).1.measurable.comp Shao.C1.measurable_normalizedEndpoint)
  have hRhalf : R ≤ 1 / 2 := hR.le.trans (hu.trans (by norm_num))
  have hInitialData := hInitial rho n hn h2 hmean hsecond ΩB Bm PB hBm x hx1 hRhalf
  rcases hInitialData with ⟨hZ0I, hInitialPaid, hMaskedUnused⟩
  change Integrable Z0 P at hZ0I
  change |(∫ a : Shao.Path n, Z0 a ∂P) - PB.real DB| ≤
    CI * R * Shao.standardNormalTail x at hInitialPaid
  let PN : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => normalizedLaw)
  let A : Shao.Path n → Shao.Path n := fun a i => a i / Real.sqrt (n : ℝ)
  have hAM : Measurable A :=
    Measurable.of_eval (fun i => (measurable_pi_apply i).div_const _)
  have hAmap : Measure.map A P = PN :=
    Measure.pi_map_pi (fun _ : Fin n => hScaleM.aemeasurable)
  have hAscale (a : Shao.Path n) : A a = (Real.sqrt (n : ℝ))⁻¹ • a := by
    funext i
    change a i / Real.sqrt (n : ℝ) = (Real.sqrt (n : ℝ))⁻¹ * a i
    rw [div_eq_mul_inv, mul_comm]
  have hAevent (a : Shao.Path n) : A a ∈ D ↔ a ∈ D := by
    have hc : 0 < (Real.sqrt (n : ℝ))⁻¹ := inv_pos.mpr hsn
    change (x * Real.sqrt (Shao.energy (A a)) ≤ Shao.upperMax (A a) hn ∧
      x * Real.sqrt (Shao.energy (A a)) ≤ Shao.lowerMax (A a) hn) ↔ _
    rw [hAscale, Shao.energy_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc.le,
      Shao.upperMax_smul_of_nonneg _ hc.le, Shao.lowerMax_smul_of_nonneg _ hc.le]
    rw [show x * ((Real.sqrt (n : ℝ))⁻¹ * Real.sqrt (Shao.energy a)) =
      (Real.sqrt (n : ℝ))⁻¹ * (x * Real.sqrt (Shao.energy a)) by ring]
    simp only [mul_le_mul_iff_right₀ hc]
    rfl
  have hPNevent : PN.real D = P.real D := by
    have hpre : A ⁻¹' D = D := Set.ext hAevent
    have hh : PN D = P D := by rw [← hAmap, Measure.map_apply hAM hDM, hpre]
    exact congrArg ENNReal.toReal hh
  have hAbsAdd (a b : ℝ) : |a + b| ≤ |a| + |b| := by
    calc
      |a + b| = |a - (-b)| := by congr 1 <;> ring
      _ ≤ |a| + |-b| := abs_sub a (-b)
      _ = |a| + |b| := by rw [abs_neg]
  have hResidualSource (hres : u ≤ Real.exp (-3 * x ^ 2)) :
      |P.real D - ∫ a : Shao.Path n, Z0 a ∂P| ≤
        CS * delta * Shao.standardNormalTail x := by
    let h0 : ℝ := 4 * beta ^ 2
    let K : ℝ := (2 : ℝ) ^ 64
    let H : ℝ := K * beta ^ 2 * (1 + x) ^ 6
    let m : ℕ := ⌈H⌉₊
    let tau : Shao.Path n → LabelPerm n → ℕ := fun a sigma =>
      min (energyCutoff a H sigma) (n - m)
    have hh0 : 0 < h0 := by dsimp only [h0]; positivity
    have hH : 0 < H := by dsimp only [H, K]; positivity
    have hh0H : h0 ≤ H := by
      have hp : 1 ≤ (1 + x) ^ 6 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + x)
      have hK4 : (4 : ℝ) ≤ K := by norm_num [K]
      have hK0 : 0 ≤ K := by dsimp only [K]; positivity
      have hh : 4 ≤ K * (1 + x) ^ 6 := by
        have hh := mul_le_mul_of_nonneg_left hp hK0
        linarith
      have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg beta)
      dsimp only [h0, H]
      nlinarith only [hh']
    have hTauM (sigma : LabelPerm n) : Measurable (fun a => tau a sigma) :=
      (SourceActualLocalProfileBudget.actual_energy_cutoff_measurable H hH sigma).min
        measurable_const
    have hTauStop (a : Shao.Path n) : IsRevealStoppingRank (tau a) :=
      (Shao.C2.AdaptiveRevealCutoff.adaptive_cutoff_stopping_and_le
        a h0 H hh0 hH hh0H m).1
    have hTauCap (a : Shao.Path n) (sigma : LabelPerm n) :
        tau a sigma ≤ energyCutoff a h0 sigma :=
      (Shao.C2.AdaptiveRevealCutoff.adaptive_cutoff_stopping_and_le
        a h0 H hh0 hH hh0H m).2 sigma
    have hTauLe (p : Shao.Path n × LabelPerm n) : tau p.1 p.2 ≤ n :=
      (Nat.min_le_right _ _).trans (Nat.sub_le n m)
    let pairLaw : Measure (Shao.Path n × LabelPerm n) := revealLaw P
    let Z : ℕ → (Shao.Path n × LabelPerm n) → ℝ := fun r p =>
      Shao.C2.ActualSignedDoubleTelescope.actualDoubleValue Q x p.1 r p.2
    let W : (Shao.Path n × LabelPerm n) → ℝ := fun p => Z (tau p.1 p.2) p
    let L : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
      ∑ r ∈ Finset.range n,
        Shao.C2.ActualSignedDoubleTelescope.actualDoubleRetained Q x p.1 (tau p.1) r p.2
    let O : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
      ∑ r ∈ Finset.range n,
        Shao.C2.ActualSignedDoubleTelescope.actualDoubleSeparated Q x p.1 (tau p.1) r p.2
    have hRetainedData := hRetained PB Bm hBm rho Bcap hBcap hsupport hmean hsecond
      n hn x hx hcap hres tau hTauM hTauCap
    dsimp only at hRetainedData
    have hLPaid : |∫ p, L p ∂pairLaw| ≤ CL * delta * Shao.standardNormalTail x := by
      have hFinReindex :
          (fun p : Shao.Path n × LabelPerm n =>
            ∑ r : Fin n,
              Shao.C2.ActualSignedDoubleTelescope.actualDoubleRetained
                Q x p.1 (tau p.1) r.val p.2) = L := by
        funext p
        exact Fin.sum_univ_eq_sum_range
          (fun r : ℕ => Shao.C2.ActualSignedDoubleTelescope.actualDoubleRetained
            Q x p.1 (tau p.1) r p.2) n
      have hh := hRetainedData.2.2.2.2.2.2
      change |∫ p : Shao.Path n × LabelPerm n,
        (∑ r : Fin n, Shao.C2.ActualSignedDoubleTelescope.actualDoubleRetained
          Q x p.1 (tau p.1) r.val p.2) ∂pairLaw| ≤
            CL * delta * Shao.standardNormalTail x at hh
      rw [hFinReindex] at hh
      exact hh
    have hSeparatedData := hSeparated Bm PB hBm rho Bcap hBcap hsupport hmean hsecond
      n hn x hx hcap hres tau hTauM hTauCap
    dsimp only at hSeparatedData
    have hOPoint : ∀ p, 0 ≤ O p := hSeparatedData.2.2.1
    have hOPaid : (∫ p, O p ∂pairLaw) ≤ CO * delta * Shao.standardNormalTail x :=
      hSeparatedData.2.2.2
    have hOMean : 0 ≤ ∫ p, O p ∂pairLaw := integral_nonneg hOPoint
    have hTelescope := Shao.C2.ActualSignedDoubleTelescope.actual_double_stopped_telescope
      Bm PB hBm n P x hx0 h0 hh0 tau hTauM hTauStop hTauCap
      (fun _ => (1 : ℝ)) measurable_const (by intro a; norm_num)
      (by intro a sigma; rfl)
    dsimp only at hTelescope
    have hWI0 : Integrable (fun p => W p - Z0 p.1) pairLaw := by
      simpa only [one_mul] using hTelescope.2.1
    have hMeanEq : (∫ p, W p - Z0 p.1 ∂pairLaw) =
        (∫ p, L p ∂pairLaw) - (∫ p, O p ∂pairLaw) := by
      simpa only [one_mul] using hTelescope.2.2.2.2.1
    have hStoppedPaid : |∫ p, W p - Z0 p.1 ∂pairLaw| ≤
        (CL + CO) * delta * Shao.standardNormalTail x := by
      rw [hMeanEq]
      calc
        |(∫ p, L p ∂pairLaw) - (∫ p, O p ∂pairLaw)| ≤
            |∫ p, L p ∂pairLaw| + |∫ p, O p ∂pairLaw| := abs_sub _ _
        _ ≤ CL * delta * Shao.standardNormalTail x + CO * delta * Shao.standardNormalTail x :=
          add_le_add hLPaid (by rw [abs_of_nonneg hOMean]; exact hOPaid)
        _ = (CL + CO) * delta * Shao.standardNormalTail x := by ring
    have hEvent (a : Shao.Path n) :
        a ∈ Shao.C2.ActualSignedDoubleTelescope.doubleCrossingEvent x ↔ a ∈ D := by
      by_cases he : Shao.energy a = 0
      · have huMax := Shao.upperMax_eq_zero_of_energy_eq_zero a hn he
        have hlMax := Shao.lowerMax_eq_zero_of_energy_eq_zero a hn he
        constructor
        · intro h
          change x * Real.sqrt (Shao.energy a) ≤ Shao.upperMax a hn ∧
            x * Real.sqrt (Shao.energy a) ≤ Shao.lowerMax a hn
          simp only [he, Real.sqrt_zero, mul_zero, huMax, hlMax, le_refl, and_self]
        · intro h
          change (∃ r : ℕ, r ≤ n ∧ actualWall a x ≤ Shao.prefixSum a r) ∧
            (∃ r : ℕ, r ≤ n ∧ Shao.prefixSum a r ≤ -actualWall a x)
          constructor <;> refine ⟨0, Nat.zero_le n, ?_⟩ <;>
            simp only [actualWall, he, Real.sqrt_zero, mul_zero, Shao.prefixSum_zero, neg_zero, le_refl]
      · have he0 : 0 < Shao.energy a := lt_of_le_of_ne (Shao.energy_nonneg a) (Ne.symm he)
        have hw : 0 < actualWall a x := mul_pos hx0 (Real.sqrt_pos.mpr he0)
        change ((∃ r : ℕ, r ≤ n ∧ actualWall a x ≤ Shao.prefixSum a r) ∧
          (∃ r : ℕ, r ≤ n ∧ Shao.prefixSum a r ≤ -actualWall a x)) ↔
          (actualWall a x ≤ Shao.upperMax a hn ∧ actualWall a x ≤ Shao.lowerMax a hn)
        rw [Shao.lowerMax, Shao.upperMax_ge_iff, Shao.upperMax_ge_iff]
        simp only [Shao.prefixSum_neg]
        constructor
        · rintro ⟨⟨ru, hru, hu⟩, ⟨rl, hrl, hl⟩⟩
          have hru0 : ru ≠ 0 := by
            intro hr; rw [hr, Shao.prefixSum_zero] at hu; linarith
          have hrl0 : rl ≠ 0 := by
            intro hr; rw [hr, Shao.prefixSum_zero] at hl; linarith
          exact ⟨⟨ru, Nat.one_le_iff_ne_zero.mpr hru0, hru, hu⟩,
            ⟨rl, Nat.one_le_iff_ne_zero.mpr hrl0, hrl, by linarith⟩⟩
        · rintro ⟨⟨ru, _, hru, hu⟩, ⟨rl, _, hrl, hl⟩⟩
          exact ⟨⟨ru, hru, hu⟩, ⟨rl, hrl, by linarith⟩⟩
    have hReorderM : Measurable (randomReorder : (Shao.Path n × LabelPerm n) → Shao.Path n) := by
      apply measurable_from_prod_countable_left
      intro sigma
      exact Measurable.of_eval (fun i => measurable_pi_apply (sigma i))
    have hCoordLaw (i : Fin n) : IdentDistrib (Function.eval i) (id : ℝ → ℝ) P rho := by
      refine ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, ?_⟩
      exact (measurePreserving_eval (fun _ : Fin n => rho) i).map_eq.trans Measure.map_id.symm
    have hReorderLaw : Measure.map randomReorder pairLaw = P := by
      exact iid_randomPermutation_map_eq_pi P rho (fun i => Function.eval i)
        (fun i => measurable_pi_apply i)
        (iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)) hCoordLaw
    have hReorderMP : MeasurePreserving randomReorder pairLaw P := ⟨hReorderM, hReorderLaw⟩
    have hZnEq : Z n = fun p => D.indicator (fun _ : Shao.Path n => (1 : ℝ)) (randomReorder p) := by
      funext p
      have hb := (Shao.C2.ActualSignedDoubleTelescope.actual_double_value_boundary
        Q x hx0 p.1 p.2).2.2
      change Z n p = _
      change Shao.C2.ActualSignedDoubleTelescope.actualDoubleValue Q x p.1 n p.2 = _
      rw [hb, hEvent]
      rfl
    have hZnI : Integrable (Z n) pairLaw := by
      rw [hZnEq]
      exact hReorderMP.integrable_comp_of_integrable hDI
    have hZnMean : (∫ p, Z n p ∂pairLaw) = P.real D := by
      rw [hZnEq]
      have hh := integral_map (μ := pairLaw) (φ := randomReorder)
        (f := D.indicator (fun _ : Shao.Path n => (1 : ℝ)))
        hReorderM.aemeasurable
        (measurable_const.indicator hDM).aestronglyMeasurable
      rw [hReorderLaw] at hh
      exact hh.symm.trans (integral_indicator_one hDM)
    have hZ0PairI : Integrable (fun p : Shao.Path n × LabelPerm n => Z0 p.1) pairLaw :=
      measurePreserving_fst.integrable_comp_of_integrable hZ0I
    have hZ0PairMean : (∫ p : Shao.Path n × LabelPerm n, Z0 p.1 ∂pairLaw) =
        ∫ a : Shao.Path n, Z0 a ∂P := by
      simpa only [pairLaw, revealLaw, probReal_univ, one_smul] using
        (integral_fun_fst (μ := P) (ν := uniformPermutationLaw n) Z0)
    have hWI : Integrable W pairLaw := by
      have hh := hWI0.add hZ0PairI
      have hSumEq :
          ((fun p : Shao.Path n × LabelPerm n => W p - Z0 p.1) +
            (fun p : Shao.Path n × LabelPerm n => Z0 p.1)) = W := by
        funext p
        change (W p - Z0 p.1) + Z0 p.1 = W p
        exact sub_add_cancel _ _
      rw [hSumEq] at hh
      exact hh
    have hDifferenceI : Integrable (fun p => Z n p - W p) pairLaw := hZnI.sub hWI
    let terminal : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ := fun J p =>
      if sourceAlive J p.1 x n p.2 then 1 else 0
    let disc : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ := fun J p =>
      (Finset.Icc (tau p.1 p.2) n).sup'
        (by exact ⟨n, Finset.mem_Icc.mpr ⟨hTauLe p, le_rfl⟩⟩)
        (fun j => |sourceValue J (eventCompletionKernel J Q) p.1 x j p.2 - terminal J p|)
    have hDisc (J : MonitoredDomain) : Measurable (disc J) ∧ Integrable (disc J) pairLaw ∧
        (∫ p, disc J p ∂pairLaw) ≤ CT * delta * Shao.standardNormalTail x := by
      have hh := hTerminal PB Bm hBm rho Bcap hBcap hsupport hmean hsecond
        n hn x hx hcap hres J
      dsimp only at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.2⟩
    have hFinal (J : MonitoredDomain) (a : Shao.Path n) (sigma : LabelPerm n) :
        sourceValue J (eventCompletionKernel J Q) a x n sigma = terminal J (a, sigma) := by
      have hs : Shao.prefixSum (Spitzer.reorder a sigma) n = Shao.prefixSum a n := by
        simpa only [Shao.prefixSum_length, Spitzer.reorder] using Equiv.sum_comp sigma a
      have he : Shao.energy (Spitzer.reorder a sigma) = Shao.energy a := by
        simpa only [Shao.energy, Spitzer.reorder] using
          Equiv.sum_comp sigma (fun i => (a i) ^ 2)
      have ht : remainingEnergy a n sigma = 0 := by
        rw [remainingEnergy, Shao.prefixSquares_length, he, sub_self]
      by_cases ha : sourceAlive J a x n sigma
      · have hw : 0 < actualWall a x := mul_pos hx0 (Real.sqrt_pos.mpr ha.1)
        simp only [sourceValue, if_pos ha, terminal]
        rw [hs, ht, completionExt, if_pos ⟨hw, ha.2.1, ha.2.1⟩]
        norm_num [ha]
      · simp only [sourceValue, terminal, if_neg ha]
    have hOneDisc (J : MonitoredDomain) (p : Shao.Path n × LabelPerm n) :
        |sourceValue J (eventCompletionKernel J Q) p.1 x n p.2 -
          sourceValue J (eventCompletionKernel J Q) p.1 x (tau p.1 p.2) p.2| ≤ disc J p := by
      rw [hFinal, abs_sub_comm]
      exact Finset.le_sup' (fun j =>
        |sourceValue J (eventCompletionKernel J Q) p.1 x j p.2 - terminal J p|)
        (Finset.mem_Icc.mpr ⟨le_rfl, hTauLe p⟩)
    have hThree (a b c : ℝ) : |-a - b + c| ≤ |a| + |b| + |c| := by
      calc
        |-a - b + c| ≤ |-a - b| + |c| := hAbsAdd _ _
        _ ≤ (|-a| + |b|) + |c| :=
          add_le_add (abs_sub (-a) b) (show |c| ≤ |c| from le_rfl)
        _ = |a| + |b| + |c| := by rw [abs_neg]
    have hDom (p : Shao.Path n × LabelPerm n) :
        |Z n p - W p| ≤ disc .upper p + disc .lower p + disc .interval p := by
      have hh := hThree
        (sourceValue .upper (eventCompletionKernel .upper Q) p.1 x n p.2 -
          sourceValue .upper (eventCompletionKernel .upper Q) p.1 x (tau p.1 p.2) p.2)
        (sourceValue .lower (eventCompletionKernel .lower Q) p.1 x n p.2 -
          sourceValue .lower (eventCompletionKernel .lower Q) p.1 x (tau p.1 p.2) p.2)
        (sourceValue .interval (eventCompletionKernel .interval Q) p.1 x n p.2 -
          sourceValue .interval (eventCompletionKernel .interval Q) p.1 x (tau p.1 p.2) p.2)
      have heq : Z n p - W p =
          -(sourceValue .upper (eventCompletionKernel .upper Q) p.1 x n p.2 -
            sourceValue .upper (eventCompletionKernel .upper Q) p.1 x (tau p.1 p.2) p.2) -
          (sourceValue .lower (eventCompletionKernel .lower Q) p.1 x n p.2 -
            sourceValue .lower (eventCompletionKernel .lower Q) p.1 x (tau p.1 p.2) p.2) +
          (sourceValue .interval (eventCompletionKernel .interval Q) p.1 x n p.2 -
            sourceValue .interval (eventCompletionKernel .interval Q) p.1 x (tau p.1 p.2) p.2) := by
        dsimp only [Z, W, Shao.C2.ActualSignedDoubleTelescope.actualDoubleValue]
        ring
      rw [heq]
      exact hh.trans (add_le_add (add_le_add (hOneDisc .upper p) (hOneDisc .lower p))
        (hOneDisc .interval p))
    have hDiscSumI : Integrable
        (fun p => disc .upper p + disc .lower p + disc .interval p) pairLaw :=
      ((hDisc .upper).2.1.add (hDisc .lower).2.1).add (hDisc .interval).2.1
    have hTerminalPaid : |∫ p, Z n p - W p ∂pairLaw| ≤
        3 * CT * delta * Shao.standardNormalTail x := by
      calc
        |∫ p, Z n p - W p ∂pairLaw| ≤ ∫ p, |Z n p - W p| ∂pairLaw := by
          simpa only [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (μ := pairLaw) (fun p => Z n p - W p)
        _ ≤ ∫ p, disc .upper p + disc .lower p + disc .interval p ∂pairLaw :=
          integral_mono hDifferenceI.abs hDiscSumI hDom
        _ = (∫ p, disc .upper p ∂pairLaw) + (∫ p, disc .lower p ∂pairLaw) +
            (∫ p, disc .interval p ∂pairLaw) := by
          calc
            (∫ p, disc .upper p + disc .lower p + disc .interval p ∂pairLaw) =
                (∫ p, disc .upper p + disc .lower p ∂pairLaw) +
                  (∫ p, disc .interval p ∂pairLaw) :=
              integral_add (μ := pairLaw)
                (f := fun p => disc .upper p + disc .lower p)
                (g := fun p => disc .interval p)
                ((hDisc .upper).2.1.add (hDisc .lower).2.1) (hDisc .interval).2.1
            _ = (∫ p, disc .upper p ∂pairLaw) + (∫ p, disc .lower p ∂pairLaw) +
                (∫ p, disc .interval p ∂pairLaw) :=
              congrArg (fun t : ℝ => t + (∫ p, disc .interval p ∂pairLaw))
                (integral_add (μ := pairLaw) (f := fun p => disc .upper p)
                  (g := fun p => disc .lower p) (hDisc .upper).2.1 (hDisc .lower).2.1)
        _ ≤ 3 * CT * delta * Shao.standardNormalTail x := by
          linarith only [(hDisc .upper).2.2, (hDisc .lower).2.2, (hDisc .interval).2.2]
    have hDecomposition : P.real D - (∫ a : Shao.Path n, Z0 a ∂P) =
        (∫ p, Z n p - W p ∂pairLaw) + (∫ p, W p - Z0 p.1 ∂pairLaw) := by
      rw [integral_sub hZnI hWI, integral_sub hWI hZ0PairI, hZnMean, hZ0PairMean]
      ring
    rw [hDecomposition]
    calc
      |(∫ p, Z n p - W p ∂pairLaw) + (∫ p, W p - Z0 p.1 ∂pairLaw)| ≤
          |∫ p, Z n p - W p ∂pairLaw| + |∫ p, W p - Z0 p.1 ∂pairLaw| := hAbsAdd _ _
      _ ≤ 3 * CT * delta * Shao.standardNormalTail x +
          (CL + CO) * delta * Shao.standardNormalTail x := add_le_add hTerminalPaid hStoppedPaid
      _ = CS * delta * Shao.standardNormalTail x := by dsimp only [CS]; ring
  refine ⟨h2, h3, hdelta, hR, hDM, hDI, hDB, hZ0M, hZ0I, ?_, ?_⟩
  · intro hres
    exact (hResidualSource hres).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : CS ≤ 1 + CS + CI + CN) hdelta.le) hPsi.le)
  · by_cases hres : u ≤ Real.exp (-3 * x ^ 2)
    · have hSourceScaled : CS * delta * Shao.standardNormalTail x ≤
          CS * R * Shao.standardNormalTail x := by
        rw [hR]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdeltaU hCS.le) hPsi.le
      calc
        |P.real D - PB.real DB| =
            |(P.real D - ∫ a : Shao.Path n, Z0 a ∂P) +
              ((∫ a : Shao.Path n, Z0 a ∂P) - PB.real DB)| := by congr 1 <;> ring
        _ ≤ |P.real D - ∫ a : Shao.Path n, Z0 a ∂P| +
            |(∫ a : Shao.Path n, Z0 a ∂P) - PB.real DB| := hAbsAdd _ _
        _ ≤ CS * delta * Shao.standardNormalTail x + CI * R * Shao.standardNormalTail x :=
          add_le_add (hResidualSource hres) hInitialPaid
        _ ≤ CS * R * Shao.standardNormalTail x + CI * R * Shao.standardNormalTail x :=
          add_le_add hSourceScaled (le_refl (CI * R * Shao.standardNormalTail x))
        _ = (CS + CI) * R * Shao.standardNormalTail x := by ring
        _ ≤ (1 + CS + CI + CN) * R * Shao.standardNormalTail x :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith : CS + CI ≤ 1 + CS + CI + CN)
              (by rw [hR]; exact hu0.le)) hPsi.le
    · have hguard : Real.exp (-3 * x ^ 2) ≤ u := (lt_of_not_ge hres).le
      have hpaid := hNpaid
      rw [hNthird] at hpaid
      have hNR := (hpaid hu).2 (by simpa only [one_mul] using hguard)
      change |PN.real D - PB.real DB| ≤ CN * u * Shao.standardNormalTail x at hNR
      rw [hPNevent] at hNR
      rw [hR]
      exact hNR.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : CN ≤ 1 + CS + CI + CN) hu0.le) hPsi.le)

end Shao.Probability.SourceActualBoundedRelativeConsumer
