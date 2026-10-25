import Shao.Probability.SourceWeightedRecordStrip
import Shao.Probability.QuadraticEnergyLowerTail
import Shao.C2.ActualOneWallRecordEnvelope
import Shao.C2.ActualDoubleSeparatedClassification
import Shao.C2.ActualBadIntervalNegativeBudget
import Shao.C2.BridgeIntervalImageResolved
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
noncomputable section
namespace Shao.Probability.SourceActualRecordLowFullEnergy
open MeasureTheory ProbabilityTheory
open SourcePermutationReveal SourceSeparatedOvershoot
open SourceActualLocalProfileBudget
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.ActualOneWallRecordEnvelope
open Shao.C2.ActualSignedDoubleTelescope
open scoped BigOperators Classical NNReal

local instance labelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

theorem iid_actual_low_full_energy_two_halfline_budget :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (Bcap : ℝ), 0 < Bcap → (∀ᵐ z : ℝ ∂rho, |z| ≤ Bcap) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), 16 ≤ x →
          Bcap ≤ Real.sqrt (n : ℝ) / (200 * x) →
          let delta : ℝ := beta / Real.sqrt (n : ℝ)
          delta * (1 + x) ^ 3 ≤ Real.exp (-3 * x ^ 2) →
          let t : ℝ := (n : ℝ) / beta ^ 2
          let h0 : ℝ := 4 * beta ^ 2
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
          let kappa : Shao.Path n → LabelPerm n → ℕ :=
            fun a sigma => energyCutoff a h0 sigma
          let bill : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
            if Shao.energy p.1 < (n : ℝ) / 2 then
              separatedSum .upper (halflineDerivative .upper) p.1 x (kappa p.1) p.2 +
                separatedSum .lower (halflineDerivative .lower) p.1 x (kappa p.1) p.2
            else 0
          Measurable bill ∧ Integrable bill (revealLaw P) ∧
            (∀ p : Shao.Path n × LabelPerm n, 0 ≤ bill p) ∧
            (∫ p, bill p ∂revealLaw P) ≤
              72 * Real.sqrt t * (1 + t) * Real.exp (-t / 128) ∧
            (∫ p, bill p ∂revealLaw P) ≤
              C * delta * Real.exp (-2 * x ^ 2) ∧
            (∫ p, bill p ∂revealLaw P) ≤
              C * delta * Shao.standardNormalTail x
 := by
  classical
  refine ⟨56623104, by norm_num, ?_⟩
  intro rho instRho Bcap hBcap hsupport hmean hsecond beta n hn x hx hBscale
    delta hres t h0 P kappa bill
  let law : (m : ℕ) → Measure (Shao.Path m) := fun m =>
    Measure.pi (fun _ : Fin m => rho)
  have hLawProb (m : ℕ) : IsProbabilityMeasure (law m) := by
    dsimp only [law]
    infer_instance
  have hx0 : 0 < x := by linarith only [hx]
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrootn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnr
  have hPower (r : ℕ) : Integrable (fun z : ℝ => z ^ r) rho ∧
      Integrable (fun z : ℝ => |z| ^ r) rho := by
    have hb : ∀ᵐ z : ℝ ∂rho, |z| ^ r ≤ Bcap ^ r :=
      hsupport.mono fun z hz => pow_le_pow_left₀ (abs_nonneg z) hz r
    constructor
    · exact (integrable_const (Bcap ^ r)).mono' (by fun_prop)
        (by simpa only [Real.norm_eq_abs, abs_pow] using hb)
    · exact (integrable_const (Bcap ^ r)).mono' (by fun_prop) (by
        filter_upwards [hb] with z hz
        simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg z) r)] using hz)
  have hbeta1 : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one
      rho (hPower 2).1 (hPower 3).2 hsecond
  have hbeta : 0 < beta := lt_of_lt_of_le zero_lt_one hbeta1
  have hbetaB : beta ≤ Bcap := by
    have hi := integral_mono_ae (hPower 3).2 ((hPower 2).1.const_mul Bcap)
      (hsupport.mono fun z hz => by
        have hh := mul_le_mul_of_nonneg_right hz (sq_nonneg z)
        calc
          |z| ^ 3 = |z| * z ^ 2 := by rw [← sq_abs z]; ring
          _ ≤ Bcap * z ^ 2 := hh)
    simpa only [integral_const_mul, hsecond, mul_one] using hi
  have hBroot : Bcap ≤ Real.sqrt (n : ℝ) := by
    apply hBscale.trans
    apply (div_le_iff₀ (by positivity : 0 < 200 * x)).2
    have hh := mul_nonneg (Real.sqrt_nonneg (n : ℝ))
      (show 0 ≤ 200 * x - 1 by linarith only [hx])
    nlinarith only [hh]
  have hBsq : Bcap ^ 2 ≤ (n : ℝ) := by
    nlinarith only [hBroot, hBcap, Real.sq_sqrt hnr.le]
  have hfourth : (∫ z : ℝ, z ^ 4 ∂rho) ≤ Bcap * beta := by
    have hi := integral_mono_ae (hPower 4).1 ((hPower 3).2.const_mul Bcap)
      (hsupport.mono fun z hz => by
        have hh := mul_le_mul_of_nonneg_right hz (pow_nonneg (abs_nonneg z) 3)
        calc
          z ^ 4 = |z| * |z| ^ 3 := by
            calc
              z ^ 4 = (z ^ 2) ^ 2 := by ring
              _ = (|z| ^ 2) ^ 2 := by rw [sq_abs z]
              _ = _ := by ring
          _ ≤ Bcap * |z| ^ 3 := hh)
    simpa only [integral_const_mul] using hi
  have hfourthN : (∫ z : ℝ, z ^ 4 ∂rho) ≤ (n : ℝ) :=
    hfourth.trans ((mul_le_mul_of_nonneg_left hbetaB hBcap.le).trans
      (by simpa only [pow_two] using hBsq))
  have hScale : beta ^ 2 * t = (n : ℝ) := by
    dsimp only [t]
    field_simp
  have ht0 : 0 < t := by dsimp only [t]; positivity
  have hdelta0 : 0 < delta := by dsimp only [delta]; positivity
  have hdeltaScale : delta * Real.sqrt t = 1 := by
    have hsq : (beta * Real.sqrt t) ^ 2 = (n : ℝ) := by
      rw [mul_pow, Real.sq_sqrt ht0.le, hScale]
    have hroot : beta * Real.sqrt t = Real.sqrt (n : ℝ) := by
      apply (sq_eq_sq₀ (mul_nonneg hbeta.le (Real.sqrt_nonneg t))
        (Real.sqrt_nonneg (n : ℝ))).mp
      exact hsq.trans (Real.sq_sqrt hnr.le).symm
    dsimp only [delta]
    rw [div_mul_eq_mul_div, hroot, div_self (ne_of_gt hrootn)]
  have hSupport (m : ℕ) : ∀ᵐ v : Shao.Path m ∂law m, ∀ i : Fin m, |v i| ≤ Bcap := by
    apply ae_all_iff.2
    intro i
    exact (measurePreserving_eval (fun _ : Fin m => rho) i).quasiMeasurePreserving.ae hsupport
  have hSumBound (m : ℕ) (v : Shao.Path m) (hv : ∀ i : Fin m, |v i| ≤ Bcap) :
      |Shao.prefixSum v m| ≤ (m : ℝ) * Bcap := by
    rw [Shao.prefixSum_length]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (by simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hv i))
  have hSumPower (m r : ℕ) : Integrable
      (fun v : Shao.Path m => Shao.prefixSum v m ^ r) (law m) := by
    letI : IsProbabilityMeasure (law m) := hLawProb m
    apply (integrable_const (((m : ℝ) * Bcap) ^ r)).mono'
      ((Shao.measurable_prefixSum m).pow_const r).aestronglyMeasurable
    filter_upwards [hSupport m] with v hv
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hSumBound m v hv) r
  have hMoments (m : ℕ) :
      (∫ v : Shao.Path m, Shao.prefixSum v m ∂law m) = 0 ∧
      (∫ v : Shao.Path m, Shao.prefixSum v m ^ 2 ∂law m) = (m : ℝ) ∧
      (∫ v : Shao.Path m, Shao.prefixSum v m ^ 4 ∂law m) =
        (m : ℝ) * (∫ z : ℝ, z ^ 4 ∂rho) + 3 * (m : ℝ) * ((m : ℝ) - 1) := by
    induction m with
    | zero => simp [Shao.prefixSum]
    | succ m ih =>
      let J : ℝ × Shao.Path m → Shao.Path (m + 1) := fun p => Fin.snoc p.2 p.1
      have hJ : MeasurePreserving J (rho.prod (law m)) (law (m + 1)) := by
        have heq : J = (fun p : ℝ × Shao.Path m =>
            (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm p) := by
          funext p
          simp only [J, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv_apply, Fin.insertNth_last']
        rw [heq]
        exact (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => rho)
          (Fin.last m)).symm
      have hJS (p : ℝ × Shao.Path m) :
          Shao.prefixSum (J p) (m + 1) = p.1 + Shao.prefixSum p.2 m := by
        simp only [Shao.prefixSum_length, Fin.sum_univ_castSucc, J,
          Fin.snoc_castSucc, Fin.snoc_last]
        ring
      have hTransfer (r : ℕ) :
          (∫ v : Shao.Path (m + 1), Shao.prefixSum v (m + 1) ^ r ∂law (m + 1)) =
          ∫ p : ℝ × Shao.Path m, (p.1 + Shao.prefixSum p.2 m) ^ r ∂rho.prod (law m) := by
        have hh := integral_map hJ.aemeasurable
          (((Shao.measurable_prefixSum (m + 1)).pow_const r).aestronglyMeasurable)
        rw [hJ.map_eq] at hh
        simpa only [hJS] using hh
      have hMixed (a b : ℕ) : Integrable
          (fun p : ℝ × Shao.Path m => p.1 ^ a * Shao.prefixSum p.2 m ^ b)
          (rho.prod (law m)) := (hPower a).1.mul_prod (hSumPower m b)
      have hMixedValue (a b : ℕ) :
          (∫ p : ℝ × Shao.Path m, p.1 ^ a * Shao.prefixSum p.2 m ^ b ∂rho.prod (law m)) =
          (∫ z : ℝ, z ^ a ∂rho) * (∫ v : Shao.Path m, Shao.prefixSum v m ^ b ∂law m) :=
        integral_prod_mul (μ := rho) (ν := law m)
          (fun z : ℝ => z ^ a) (fun v : Shao.Path m => Shao.prefixSum v m ^ b)
      have hExpand1 : (∫ p : ℝ × Shao.Path m,
          p.1 + Shao.prefixSum p.2 m ∂rho.prod (law m)) = 0 := by
        have heq : (fun p : ℝ × Shao.Path m => p.1 + Shao.prefixSum p.2 m) =
            (fun p => p.1 ^ 1 * Shao.prefixSum p.2 m ^ 0 +
              p.1 ^ 0 * Shao.prefixSum p.2 m ^ 1) := by funext p; ring
        rw [heq, integral_add (hMixed 1 0) (hMixed 0 1), hMixedValue, hMixedValue]
        simp only [pow_zero, pow_one, integral_const, probReal_univ, one_smul,
          hmean, ih.1, zero_mul, mul_zero, add_zero]
      have hExpand2 : (∫ p : ℝ × Shao.Path m,
          (p.1 + Shao.prefixSum p.2 m) ^ 2 ∂rho.prod (law m)) = (m : ℝ) + 1 := by
        have heq : (fun p : ℝ × Shao.Path m => (p.1 + Shao.prefixSum p.2 m) ^ 2) =
            (fun p => p.1 ^ 2 * Shao.prefixSum p.2 m ^ 0 +
              2 * (p.1 ^ 1 * Shao.prefixSum p.2 m ^ 1) +
              p.1 ^ 0 * Shao.prefixSum p.2 m ^ 2) := by funext p; ring
        have hSumI : Integrable (fun p : ℝ × Shao.Path m =>
            p.1 ^ 2 * Shao.prefixSum p.2 m ^ 0 +
              2 * (p.1 ^ 1 * Shao.prefixSum p.2 m ^ 1)) (rho.prod (law m)) :=
          (hMixed 2 0).add ((hMixed 1 1).const_mul 2)
        rw [heq, integral_add hSumI (hMixed 0 2),
          integral_add (hMixed 2 0) ((hMixed 1 1).const_mul 2), integral_const_mul]
        rw [hMixedValue, hMixedValue, hMixedValue]
        simp only [pow_zero, pow_one, integral_const, probReal_univ, one_smul,
          hmean, hsecond, ih.1, ih.2.1, zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_one]
        ring
      have hExpand4 : (∫ p : ℝ × Shao.Path m,
          (p.1 + Shao.prefixSum p.2 m) ^ 4 ∂rho.prod (law m)) =
          ((m : ℝ) + 1) * (∫ z : ℝ, z ^ 4 ∂rho) + 3 * ((m : ℝ) + 1) * (m : ℝ) := by
        have heq : (fun p : ℝ × Shao.Path m => (p.1 + Shao.prefixSum p.2 m) ^ 4) =
            (fun p => p.1 ^ 4 * Shao.prefixSum p.2 m ^ 0 +
              4 * (p.1 ^ 3 * Shao.prefixSum p.2 m ^ 1) +
              6 * (p.1 ^ 2 * Shao.prefixSum p.2 m ^ 2) +
              4 * (p.1 ^ 1 * Shao.prefixSum p.2 m ^ 3) +
              p.1 ^ 0 * Shao.prefixSum p.2 m ^ 4) := by funext p; ring
        have hSumI2 : Integrable (fun p : ℝ × Shao.Path m =>
            p.1 ^ 4 * Shao.prefixSum p.2 m ^ 0 +
              4 * (p.1 ^ 3 * Shao.prefixSum p.2 m ^ 1)) (rho.prod (law m)) :=
          (hMixed 4 0).add ((hMixed 3 1).const_mul 4)
        have hSumI3 : Integrable (fun p : ℝ × Shao.Path m =>
            p.1 ^ 4 * Shao.prefixSum p.2 m ^ 0 +
              4 * (p.1 ^ 3 * Shao.prefixSum p.2 m ^ 1) +
              6 * (p.1 ^ 2 * Shao.prefixSum p.2 m ^ 2)) (rho.prod (law m)) :=
          hSumI2.add ((hMixed 2 2).const_mul 6)
        have hSumI4 : Integrable (fun p : ℝ × Shao.Path m =>
            p.1 ^ 4 * Shao.prefixSum p.2 m ^ 0 +
              4 * (p.1 ^ 3 * Shao.prefixSum p.2 m ^ 1) +
              6 * (p.1 ^ 2 * Shao.prefixSum p.2 m ^ 2) +
              4 * (p.1 ^ 1 * Shao.prefixSum p.2 m ^ 3)) (rho.prod (law m)) :=
          hSumI3.add ((hMixed 1 3).const_mul 4)
        rw [heq,
          integral_add hSumI4 (hMixed 0 4),
          integral_add hSumI3 ((hMixed 1 3).const_mul 4),
          integral_add hSumI2 ((hMixed 2 2).const_mul 6),
          integral_add (hMixed 4 0) ((hMixed 3 1).const_mul 4)]
        simp only [integral_const_mul]
        rw [hMixedValue 4 0, hMixedValue 3 1, hMixedValue 2 2, hMixedValue 1 3,
          hMixedValue 0 4]
        simp only [pow_zero, pow_one, integral_const,
          probReal_univ, one_smul, hmean, hsecond, ih.1, ih.2.1, ih.2.2,
          zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_one]
        ring
      refine ⟨?_, ?_, ?_⟩
      · simpa only [pow_one] using (hTransfer 1).trans (by simpa only [pow_one] using hExpand1)
      · simpa only [Nat.cast_add, Nat.cast_one] using (hTransfer 2).trans hExpand2
      · simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using
          (hTransfer 4).trans hExpand4
  have hLow : P.real {v : Shao.Path n | Shao.energy v < (n : ℝ) / 2} ≤
      Real.exp (-t / 64) := by
    let scale : ℝ := Real.sqrt (n : ℝ)
    let eta : Measure ℝ := rho.map (fun z : ℝ => z / scale)
    letI : IsProbabilityMeasure eta := by dsimp only [eta]; infer_instance
    have hm : Measurable (fun z : ℝ => z / scale) := measurable_id.div_const scale
    have hs : 0 < scale := hrootn
    have hs2 : scale ^ 2 = (n : ℝ) := Real.sq_sqrt hnr.le
    have he2 : Integrable (fun z : ℝ => z ^ 2) eta := by
      apply (integrable_map_measure (by fun_prop) hm.aemeasurable).2
      simpa only [Function.comp_def, div_pow] using (hPower 2).1.div_const (scale ^ 2)
    have he3 : Integrable (fun z : ℝ => |z| ^ 3) eta := by
      apply (integrable_map_measure (by fun_prop) hm.aemeasurable).2
      simpa only [Function.comp_def, abs_div, abs_of_pos hs, div_pow] using
        (hPower 3).2.div_const (scale ^ 3)
    have hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta) = 1 := by
      rw [show eta = rho.map (fun z : ℝ => z / scale) from rfl,
        integral_map hm.aemeasurable (by fun_prop)]
      simp_rw [div_pow]
      rw [integral_div, hsecond, ← hs2]
      field_simp
    have hebeta : (n : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂eta) = delta := by
      rw [show eta = rho.map (fun z : ℝ => z / scale) from rfl,
        integral_map hm.aemeasurable (by fun_prop)]
      simp_rw [abs_div, abs_of_pos hs, div_pow]
      rw [integral_div, ← hs2]
      change scale ^ 2 * (beta / scale ^ 3) = beta / scale
      field_simp
    have hh := (finite_iid_energy_lower_tail eta n hn he2 he3 hnorm
      (1 / 2) (by norm_num) (by norm_num)).2
    rw [hebeta] at hh
    let normPath : Shao.Path n → Shao.Path n := fun v i => v i / scale
    have hnm : Measurable normPath := by
      dsimp only [normPath]
      exact Measurable.of_eval fun i =>
        (measurable_pi_apply (X := fun _ : Fin n => ℝ) i).div_const scale
    have hmap : P.map normPath = Measure.pi (fun _ : Fin n => eta) :=
      Measure.pi_map_pi (fun _ : Fin n => hm.aemeasurable)
    have hpre : normPath ⁻¹' {v : Shao.Path n | Shao.energy v ≤ 1 - (1 / 2 : ℝ)} =
        {v : Shao.Path n | Shao.energy v ≤ (n : ℝ) / 2} := by
      ext v
      have henergy : Shao.energy (normPath v) = Shao.energy v / (n : ℝ) := by
        simp only [Shao.energy, normPath, div_pow, ← Finset.sum_div, hs2]
      change Shao.energy (normPath v) ≤ 1 - (1 / 2 : ℝ) ↔ _
      rw [henergy, div_le_iff₀ hnr]
      norm_num
      constructor <;> intro hv <;> linarith only [hv]
    have hclosed : MeasurableSet {v : Shao.Path n | Shao.energy v ≤ 1 - (1 / 2 : ℝ)} :=
      measurableSet_le Shao.measurable_energy measurable_const
    rw [← hmap, Measure.real_def, Measure.map_apply hnm hclosed, hpre] at hh
    have he : -((1 / 2 : ℝ) ^ 3 / (8 * delta ^ 2)) = -t / 64 := by
      dsimp only [delta, t]
      simp only [div_pow, Real.sq_sqrt hnr.le]
      field_simp [ne_of_gt hbeta, ne_of_gt hnr]
      <;> ring
    rw [he] at hh
    have hsub : {v : Shao.Path n | Shao.energy v < (n : ℝ) / 2} ⊆
        {v : Shao.Path n | Shao.energy v ≤ (n : ℝ) / 2} := by
      intro v hv
      exact (show Shao.energy v < (n : ℝ) / 2 from hv).le
    exact (measureReal_mono hsub).trans hh
  let W : (m : ℕ) → Shao.Path m → ℝ := fun m v =>
    if 0 < Shao.energy v ∧ 2 * beta ^ 2 ≤ Shao.energy v then
      1 / Real.sqrt (Shao.energy v) *
        (1 + |Shao.prefixSum v m| / Real.sqrt (Shao.energy v)) ^ 2
    else 0
  have hW0 (m : ℕ) (v : Shao.Path m) : 0 ≤ W m v := by
    dsimp only [W]
    split_ifs <;> positivity
  have hWm (m : ℕ) : Measurable (W m) := by
    apply Measurable.ite ((measurableSet_lt measurable_const Shao.measurable_energy).inter
      (measurableSet_le measurable_const Shao.measurable_energy))
    · exact (measurable_const.div Shao.measurable_energy.sqrt).mul
        ((measurable_const.add ((continuous_abs.measurable.comp
          (Shao.measurable_prefixSum m)).div Shao.measurable_energy.sqrt)).pow_const 2)
    · exact measurable_const
  have hWBound (m : ℕ) (v : Shao.Path m) (hv : ∀ i : Fin m, |v i| ≤ Bcap) :
      W m v ≤ 1 / beta * (1 + (m : ℝ) * Bcap / beta) ^ 2 := by
    dsimp only [W]
    split_ifs with hq
    · have hr : 0 < Real.sqrt (Shao.energy v) := Real.sqrt_pos.2 hq.1
      have hbr : beta ≤ Real.sqrt (Shao.energy v) := by
        nlinarith only [Real.sq_sqrt hq.1.le, hq.2, hbeta, Real.sqrt_nonneg (Shao.energy v)]
      have hi : 1 / Real.sqrt (Shao.energy v) ≤ 1 / beta :=
        one_div_le_one_div_of_le hbeta hbr
      have hquot : |Shao.prefixSum v m| / Real.sqrt (Shao.energy v) ≤
          (m : ℝ) * Bcap / beta := by
        exact (div_le_div_of_nonneg_right (hSumBound m v hv) hr.le).trans
          (by
            apply (div_le_div_iff₀ hr hbeta).2
            exact mul_le_mul_of_nonneg_left hbr (by positivity))
      exact mul_le_mul hi (pow_le_pow_left₀ (by positivity)
        (show 1 + |Shao.prefixSum v m| / Real.sqrt (Shao.energy v) ≤
          1 + (m : ℝ) * Bcap / beta by linarith only [hquot]) 2)
        (by positivity) (by positivity)
    · positivity
  have hWPower (m r : ℕ) : Integrable (fun v : Shao.Path m => W m v ^ r) (law m) := by
    letI : IsProbabilityMeasure (law m) := hLawProb m
    apply (integrable_const ((1 / beta * (1 + (m : ℝ) * Bcap / beta) ^ 2) ^ r)).mono'
      ((hWm m).pow_const r).aestronglyMeasurable
    filter_upwards [hSupport m] with v hv
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hW0 m v) r)]
    exact pow_le_pow_left₀ (hW0 m v) (hWBound m v hv) r
  have hWPoint (m : ℕ) (v : Shao.Path m) :
      W m v ^ 2 ≤ 4 / beta ^ 2 + Shao.prefixSum v m ^ 4 / beta ^ 6 := by
    dsimp only [W]
    split_ifs with hq
    · let r : ℝ := Real.sqrt (Shao.energy v)
      let a : ℝ := |Shao.prefixSum v m|
      have hr : 0 < r := Real.sqrt_pos.2 hq.1
      have hr2 : r ^ 2 = Shao.energy v := Real.sq_sqrt hq.1.le
      have hv0 : 0 ≤ a / r := by positivity
      have hpoly : (1 + a / r) ^ 4 ≤ 8 * (1 + (a / r) ^ 4) := by
        have hh := mul_nonneg (sq_nonneg (a / r - 1))
          (show 0 ≤ 7 * (a / r) ^ 2 + 10 * (a / r) + 7 by positivity)
        nlinarith only [hh]
      have hfirst : 8 / r ^ 2 ≤ 4 / beta ^ 2 := by
        apply (div_le_div_iff₀ (by positivity : 0 < r ^ 2) (by positivity : 0 < beta ^ 2)).2
        nlinarith only [hr2, hq.2]
      have hq3 : 8 * beta ^ 6 ≤ r ^ 6 := by
        have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * beta ^ 2) hq.2 3
        rw [← hr2] at hh
        nlinarith only [hh]
      have hsecond : 8 * a ^ 4 / r ^ 6 ≤ a ^ 4 / beta ^ 6 := by
        apply (div_le_div_iff₀ (by positivity : 0 < r ^ 6) (by positivity : 0 < beta ^ 6)).2
        nlinarith only [mul_le_mul_of_nonneg_left hq3 (show 0 ≤ a ^ 4 by positivity)]
      calc
        (1 / r * (1 + a / r) ^ 2) ^ 2 ≤
            8 / r ^ 2 + 8 * a ^ 4 / r ^ 6 := by
          have hh := mul_le_mul_of_nonneg_left hpoly (show 0 ≤ 1 / r ^ 2 by positivity)
          convert hh using 1 <;> field_simp <;> ring
        _ ≤ 4 / beta ^ 2 + a ^ 4 / beta ^ 6 := add_le_add hfirst hsecond
        _ = _ := by
          have ha : a ^ 4 = Shao.prefixSum v m ^ 4 := by
            dsimp only [a]
            calc
              |Shao.prefixSum v m| ^ 4 = (|Shao.prefixSum v m| ^ 2) ^ 2 := by ring
              _ = (Shao.prefixSum v m ^ 2) ^ 2 := by rw [sq_abs]
              _ = Shao.prefixSum v m ^ 4 := by ring
          rw [ha]
    · simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using
        (show 0 ≤ 4 / beta ^ 2 + Shao.prefixSum v m ^ 4 / beta ^ 6 by positivity)
  have hWSecond (m : ℕ) (hm : m ≤ n) :
      (∫ v : Shao.Path m, W m v ^ 2 ∂law m) ≤ 8 * (1 + t) ^ 2 / beta ^ 2 := by
    have hmr : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm
    have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hfourthM : (∫ v : Shao.Path m, Shao.prefixSum v m ^ 4 ∂law m) ≤ 4 * (n : ℝ) ^ 2 := by
      rw [(hMoments m).2.2]
      have hi := mul_le_mul_of_nonneg_left hfourthN hm0
      have hmn := mul_le_mul_of_nonneg_right hmr hnr.le
      have hm2 := pow_le_pow_left₀ hm0 hmr 2
      nlinarith only [hi, hmn, hm2, hm0]
    have hi := integral_mono (hWPower m 2)
      ((integrable_const (4 / beta ^ 2)).add ((hSumPower m 4).div_const (beta ^ 6)))
      (hWPoint m)
    change (∫ v : Shao.Path m, W m v ^ 2 ∂law m) ≤
      ∫ v : Shao.Path m, 4 / beta ^ 2 + Shao.prefixSum v m ^ 4 / beta ^ 6 ∂law m at hi
    rw [integral_add (integrable_const _) ((hSumPower m 4).div_const (beta ^ 6))] at hi
    simp only [integral_div, integral_const, probReal_univ, one_smul] at hi
    calc
      _ ≤ 4 / beta ^ 2 + (4 * (n : ℝ) ^ 2) / beta ^ 6 := hi.trans (by
        have hdiv : (∫ v : Shao.Path m, Shao.prefixSum v m ^ 4 ∂law m) / beta ^ 6 ≤
            (4 * (n : ℝ) ^ 2) / beta ^ 6 :=
          div_le_div_of_nonneg_right hfourthM (by positivity : 0 ≤ beta ^ 6)
        linarith only [hdiv])
      _ = (4 + 4 * t ^ 2) / beta ^ 2 := by
        have hs : (n : ℝ) = beta ^ 2 * t := hScale.symm
        rw [hs]
        field_simp [ne_of_gt hbeta]
        <;> ring
      _ ≤ 8 * (1 + t) ^ 2 / beta ^ 2 :=
        div_le_div_of_nonneg_right (by nlinarith only [ht0.le, sq_nonneg t]) (sq_nonneg beta)
  run_tac
    let modName : Lean.Name := "Shao.Probability.SourceTrueEnergyStrip".toName
    let splitName := Lean.mkPrivateNameCore modName
      "Shao.Probability.tes_head_tail_measurePreserving".toName
    let sumName := Lean.mkPrivateNameCore modName "Shao.Probability.tes_head_tail_sum".toName
    let cyclicName := Lean.mkPrivateNameCore "Shao.Probability.SourceWeightedRecordStrip".toName
      "Shao.Probability.SourceWeightedRecordStrip.wrs_cyclic_record_identity".toName
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent "hSplit".toName) := $(Lean.mkIdent splitName)))
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent "hSplitSum".toName) := @$(Lean.mkIdent sumName)))
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent "hCyclic".toName) := $(Lean.mkIdent cyclicName)))
  let D : (m : ℕ) → ℝ → Shao.Path m → ℝ := fun m s v =>
    max (Shao.prefixSum (s • v) m - Shao.maxWithZero
      (Spitzer.head (s • v) (m - 1) (Nat.sub_le m 1))) 0
  have hCore (j : ℕ) (hj : 0 < j) (hjn : j ≤ n) (s : ℝ) (hs : s = 1 ∨ s = -1) :
      let R : Shao.Path n → ℝ := fun v =>
        if Shao.energy v < (n : ℝ) / 2 then
          D j s (Spitzer.head v j hjn) * W (n - j) (Spitzer.tail v j hjn)
        else 0
      Measurable R ∧ Integrable R P ∧ (∀ v, 0 ≤ R v) ∧
        (∫ v, R v ∂P) ≤ 3 * (1 + t) / (beta * Real.sqrt (j : ℝ)) * Real.exp (-t / 128) := by
    intro R
    letI : NeZero j := ⟨Nat.ne_of_gt hj⟩
    letI : IsProbabilityMeasure (law j) := hLawProb j
    letI : IsProbabilityMeasure (law (n - j)) := hLawProb (n - j)
    let μ : Measure (Shao.Path j × Shao.Path (n - j)) := (law j).prod (law (n - j))
    let A : Set (Shao.Path j × Shao.Path (n - j)) :=
      {p | Shao.energy p.1 + Shao.energy p.2 < (n : ℝ) / 2}
    let H : (Shao.Path j × Shao.Path (n - j)) → ℝ := fun p =>
      D j s p.1 * W (n - j) p.2
    let F : (Shao.Path j × Shao.Path (n - j)) → ℝ := fun p =>
      max (s * Shao.prefixSum p.1 j) 0 * W (n - j) p.2
    let G : (Shao.Path j × Shao.Path (n - j)) → ℝ := A.indicator (fun _ => 1)
    have hjr : 0 < (j : ℝ) := by exact_mod_cast hj
    have hjroot : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.2 hjr
    have hsabs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
    have hD0 (v : Shao.Path j) : 0 ≤ D j s v := le_max_right _ _
    have hDm : Measurable (D j s) := by
      have hsm : Measurable (fun v : Shao.Path j => s • v) :=
        Measurable.of_eval fun i => measurable_const.mul (measurable_pi_apply i)
      have hhm : Measurable (fun v : Shao.Path j =>
          Spitzer.head (s • v) (j - 1) (Nat.sub_le j 1)) :=
        Measurable.of_eval fun i => measurable_const.mul (measurable_pi_apply _)
      exact (((Shao.measurable_prefixSum j).comp hsm).sub
        (Shao.measurable_maxWithZero.comp hhm)).max measurable_const
    have hDcap (v : Shao.Path j) (hv : ∀ i : Fin j, |v i| ≤ Bcap) :
        D j s v ≤ (j : ℝ) * Bcap := by
      apply max_le
      · have hh : Shao.prefixSum (s • v) j ≤ (j : ℝ) * Bcap := by
          rw [Shao.prefixSum_smul]
          exact (le_abs_self _).trans (by simpa only [abs_mul, hsabs, one_mul] using hSumBound j v hv)
        linarith only [hh, Shao.maxWithZero_nonneg
          (Spitzer.head (s • v) (j - 1) (Nat.sub_le j 1))]
      · positivity
    have hDI : Integrable (D j s) (law j) := by
      apply (integrable_const ((j : ℝ) * Bcap)).mono' hDm.aestronglyMeasurable
      filter_upwards [hSupport j] with v hv
      rw [Real.norm_eq_abs, abs_of_nonneg (hD0 v)]
      exact hDcap v hv
    have hFm : Measurable F :=
      (((measurable_const.mul ((Shao.measurable_prefixSum j).comp measurable_fst)).max
        measurable_const).mul ((hWm (n - j)).comp measurable_snd))
    have hHm : Measurable H := (hDm.comp measurable_fst).mul
      ((hWm (n - j)).comp measurable_snd)
    have hAm : MeasurableSet A :=
      measurableSet_lt ((Shao.measurable_energy.comp measurable_fst).add
        (Shao.measurable_energy.comp measurable_snd)) measurable_const
    have hHI : Integrable H μ := by
      simpa only [pow_one] using hDI.mul_prod (hWPower (n - j) 1)
    have hAI : Integrable (A.indicator H) μ := hHI.indicator hAm
    have hF0 (p : Shao.Path j × Shao.Path (n - j)) : 0 ≤ F p := by
      exact mul_nonneg (le_max_right _ _) (hW0 _ _)
    have hFSq (p : Shao.Path j × Shao.Path (n - j)) :
        F p ^ 2 ≤ Shao.prefixSum p.1 j ^ 2 * W (n - j) p.2 ^ 2 := by
      have hh : max (s * Shao.prefixSum p.1 j) 0 ^ 2 ≤ Shao.prefixSum p.1 j ^ 2 := by
        have hmax : max (s * Shao.prefixSum p.1 j) 0 ≤ |Shao.prefixSum p.1 j| := by
          apply max_le
          · exact (le_abs_self _).trans_eq (by rw [abs_mul, hsabs, one_mul])
          · exact abs_nonneg _
        have hp := pow_le_pow_left₀ (le_max_right (s * Shao.prefixSum p.1 j) 0) hmax 2
        simpa only [sq_abs] using hp
      simpa only [F, mul_pow] using mul_le_mul_of_nonneg_right hh (sq_nonneg _)
    have hSqI : Integrable (fun p : Shao.Path j × Shao.Path (n - j) =>
        Shao.prefixSum p.1 j ^ 2 * W (n - j) p.2 ^ 2) μ :=
      (hSumPower j 2).mul_prod (hWPower (n - j) 2)
    have hFSqI : Integrable (fun p => F p ^ 2) μ :=
      hSqI.mono' (hFm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hFSq p)
    have hJBound : (∫ p, F p ^ 2 ∂μ) ≤
        (3 * Real.sqrt (j : ℝ) * (1 + t) / beta) ^ 2 := by
      have hh := integral_mono hFSqI hSqI hFSq
      have hfactor : (∫ p : Shao.Path j × Shao.Path (n - j),
          Shao.prefixSum p.1 j ^ 2 * W (n - j) p.2 ^ 2 ∂μ) =
          (∫ v : Shao.Path j, Shao.prefixSum v j ^ 2 ∂law j) *
            (∫ v : Shao.Path (n - j), W (n - j) v ^ 2 ∂law (n - j)) :=
        integral_prod_mul (μ := law j) (ν := law (n - j))
          (fun v : Shao.Path j => Shao.prefixSum v j ^ 2)
          (fun v : Shao.Path (n - j) => W (n - j) v ^ 2)
      rw [hfactor, (hMoments j).2.1] at hh
      have hh' := mul_le_mul_of_nonneg_left (hWSecond (n - j) (Nat.sub_le n j)) hjr.le
      calc
        _ ≤ (j : ℝ) * (8 * (1 + t) ^ 2 / beta ^ 2) := hh.trans hh'
        _ = 8 * ((j : ℝ) * (1 + t) ^ 2 / beta ^ 2) := by ring
        _ ≤ 9 * ((j : ℝ) * (1 + t) ^ 2 / beta ^ 2) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ = _ := by
          rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hjr.le]
          ring
    have hJ0 : 0 ≤ ∫ p, F p ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
    have hJRoot : Real.sqrt (∫ p, F p ^ 2 ∂μ) ≤
        3 * Real.sqrt (j : ℝ) * (1 + t) / beta := by
      have hbound0 : 0 ≤ 3 * Real.sqrt (j : ℝ) * (1 + t) / beta := by positivity
      nlinarith only [hJBound, Real.sq_sqrt hJ0,
        Real.sqrt_nonneg (∫ p, F p ^ 2 ∂μ), hbound0]
    have hsplit : MeasurePreserving
        (fun v : Shao.Path n => (Spitzer.head v j hjn, Spitzer.tail v j hjn)) P μ :=
      hSplit rho n j hjn
    have hEnergy (v : Shao.Path n) :
        Shao.energy v = Shao.energy (Spitzer.head v j hjn) +
          Shao.energy (Spitzer.tail v j hjn) := hSplitSum v j hjn (fun z : ℝ => z ^ 2)
    have hALow : μ.real A ≤ Real.exp (-t / 64) := by
      have hpre : (fun v : Shao.Path n => (Spitzer.head v j hjn, Spitzer.tail v j hjn)) ⁻¹' A =
          {v | Shao.energy v < (n : ℝ) / 2} := by
        ext v
        change Shao.energy (Spitzer.head v j hjn) + Shao.energy (Spitzer.tail v j hjn) < _ ↔ _
        rw [← hEnergy v]
        rfl
      have he : μ.real A = P.real {v : Shao.Path n | Shao.energy v < (n : ℝ) / 2} := by
        rw [← hsplit.map_eq, Measure.real_def, Measure.map_apply hsplit.measurable hAm, hpre]
        rfl
      exact he.trans_le hLow
    have hARoot : Real.sqrt (μ.real A) ≤ Real.exp (-t / 128) := by
      have he : Real.exp (-t / 128) ^ 2 = Real.exp (-t / 64) := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
      nlinarith only [hALow, Real.sq_sqrt (measureReal_nonneg : 0 ≤ μ.real A), he,
        Real.sqrt_nonneg (μ.real A), Real.exp_pos (-t / 128)]
    have hFMem : MemLp F 2 μ :=
      (memLp_two_iff_integrable_sq hFm.aestronglyMeasurable).2 hFSqI
    have hGMem : MemLp G 2 μ := by
      exact (memLp_const (1 : ℝ)).indicator hAm.nullMeasurableSet
    have hG0 (p : Shao.Path j × Shao.Path (n - j)) : 0 ≤ G p := by
      by_cases hp : p ∈ A <;> simp [G, hp]
    have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (ae_of_all _ hF0) (ae_of_all _ hG0) (by simpa using hFMem) (by simpa using hGMem)
    have hFG : (fun p => F p * G p) = A.indicator F := by
      funext p
      by_cases hp : p ∈ A
      · simp only [G, Set.indicator_of_mem hp, mul_one]
      · simp only [G, Set.indicator_of_notMem hp, mul_zero]
    have hGSq : (fun p => G p ^ 2) = A.indicator (fun _ => (1 : ℝ)) := by
      funext p
      by_cases hp : p ∈ A
      · simp only [G, Set.indicator_of_mem hp, one_pow]
      · simp only [G, Set.indicator_of_notMem hp, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    have hfRpow (p : Shao.Path j × Shao.Path (n - j)) :
        F p ^ (2 : ℝ) = F p ^ (2 : ℕ) := Real.rpow_natCast (F p) 2
    have hgRpow (p : Shao.Path j × Shao.Path (n - j)) :
        G p ^ (2 : ℝ) = G p ^ (2 : ℕ) := Real.rpow_natCast (G p) 2
    simp_rw [hfRpow, hgRpow] at hHolder
    have hOneIntegral :
        (∫ p : Shao.Path j × Shao.Path (n - j), A.indicator (fun _ => (1 : ℝ)) p ∂μ) =
          μ.real A := integral_indicator_one hAm
    rw [hFG, hGSq, hOneIntegral] at hHolder
    have hCauchy : (∫ p, A.indicator F p ∂μ) ≤
        (3 * Real.sqrt (j : ℝ) * (1 + t) / beta) * Real.exp (-t / 128) := by
      have hh : (∫ p, A.indicator F p ∂μ) ≤
          Real.sqrt (∫ p, F p ^ 2 ∂μ) * Real.sqrt (μ.real A) := by
        simpa only [Real.sqrt_eq_rpow] using hHolder
      exact hh.trans (mul_le_mul hJRoot hARoot (Real.sqrt_nonneg _) (by positivity))
    let rot : Fin j → Shao.Path j → Shao.Path j := fun q v i => v (i + q)
    let rotPair : Fin j → (Shao.Path j × Shao.Path (n - j)) →
        (Shao.Path j × Shao.Path (n - j)) := fun q p => (rot q p.1, p.2)
    have hRotMP (q : Fin j) : MeasurePreserving (rotPair q) μ μ :=
      ((measurePreserving_piCongrLeft (fun _ : Fin j => rho) (Equiv.addRight q)).symm).prod
        (MeasurePreserving.id (law (n - j)))
    have hRotEnergy (q : Fin j) (v : Shao.Path j) : Shao.energy (rot q v) = Shao.energy v :=
      Equiv.sum_comp (Equiv.addRight q) (fun i : Fin j => v i ^ 2)
    have hRotMark (q : Fin j) (p : Shao.Path j × Shao.Path (n - j)) :
        rotPair q p ∈ A ↔ p ∈ A := by
      change Shao.energy (rot q p.1) + Shao.energy p.2 < (n : ℝ) / 2 ↔
        Shao.energy p.1 + Shao.energy p.2 < (n : ℝ) / 2
      rw [hRotEnergy]
    have hCycle (p : Shao.Path j × Shao.Path (n - j)) :
        (∑ q : Fin j, (A.indicator H) (rotPair q p)) = A.indicator F p := by
      by_cases hp : p ∈ A
      · have hrec := (hCyclic j hj (s • p.1)).1
        change (∑ q : Fin j, D j s (rot q p.1)) = max (Shao.prefixSum (s • p.1) j) 0 at hrec
        rw [Shao.prefixSum_smul] at hrec
        simp_rw [Set.indicator_of_mem ((hRotMark _ p).mpr hp)]
        rw [Set.indicator_of_mem hp]
        change (∑ q : Fin j, D j s (rot q p.1) * W (n - j) p.2) = _
        rw [← Finset.sum_mul, hrec]
      · have hnq (q : Fin j) : rotPair q p ∉ A := fun hq => hp ((hRotMark q p).mp hq)
        simp only [Set.indicator_of_notMem hp, Set.indicator_of_notMem (hnq _), Finset.sum_const_zero]
    have hRotI (q : Fin j) : Integrable (fun p => A.indicator H (rotPair q p)) μ :=
      (hRotMP q).integrable_comp_of_integrable hAI
    have hRotIntegral (q : Fin j) :
        (∫ p, A.indicator H (rotPair q p) ∂μ) = ∫ p, A.indicator H p ∂μ := by
      have hh := integral_map (hRotMP q).aemeasurable (hHm.indicator hAm).aestronglyMeasurable
      rw [(hRotMP q).map_eq] at hh
      exact hh.symm
    have hCycleIntegral : (j : ℝ) * (∫ p, A.indicator H p ∂μ) =
        ∫ p, A.indicator F p ∂μ := by
      calc
        _ = ∑ q : Fin j, ∫ p, A.indicator H (rotPair q p) ∂μ := by simp only [hRotIntegral,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = ∫ p, ∑ q : Fin j, A.indicator H (rotPair q p) ∂μ :=
          (integral_finsetSum _ fun q _ => hRotI q).symm
        _ = _ := integral_congr_ae (ae_of_all _ hCycle)
    have hCoreBound : (∫ p, A.indicator H p ∂μ) ≤
        3 * (1 + t) / (beta * Real.sqrt (j : ℝ)) * Real.exp (-t / 128) := by
      rw [← hCycleIntegral] at hCauchy
      have hh : (∫ p, A.indicator H p ∂μ) ≤
          ((3 * Real.sqrt (j : ℝ) * (1 + t) / beta) * Real.exp (-t / 128)) / (j : ℝ) :=
        (le_div_iff₀ hjr).2 (by simpa only [mul_comm] using hCauchy)
      calc
        _ ≤ ((3 * Real.sqrt (j : ℝ) * (1 + t) / beta) * Real.exp (-t / 128)) / (j : ℝ) := hh
        _ = ((3 * Real.sqrt (j : ℝ) * (1 + t) / beta) * Real.exp (-t / 128)) /
            Real.sqrt (j : ℝ) ^ 2 := by rw [Real.sq_sqrt hjr.le]
        _ = _ := by
          field_simp [ne_of_gt hbeta, ne_of_gt hjroot]
          <;> ring
    have hR (v : Shao.Path n) :
        R v = A.indicator H (Spitzer.head v j hjn, Spitzer.tail v j hjn) := by
      dsimp only [R]
      rw [Set.indicator_apply]
      change (if Shao.energy v < (n : ℝ) / 2 then
          D j s (Spitzer.head v j hjn) * W (n - j) (Spitzer.tail v j hjn) else 0) =
        (if Shao.energy (Spitzer.head v j hjn) + Shao.energy (Spitzer.tail v j hjn) < (n : ℝ) / 2 then
          D j s (Spitzer.head v j hjn) * W (n - j) (Spitzer.tail v j hjn) else 0)
      rw [hEnergy v]
    have hRM : Measurable R := by
      simpa only [Function.comp_def, ← hR] using (hHm.indicator hAm).comp hsplit.measurable
    have hRI : Integrable R P := by
      simpa only [Function.comp_def, ← hR] using hsplit.integrable_comp_of_integrable hAI
    refine ⟨hRM, hRI, ?_, ?_⟩
    · intro v
      dsimp only [R]
      split_ifs
      · exact mul_nonneg (hD0 _) (hW0 _ _)
      · exact le_rfl
    · have hh := integral_map hsplit.aemeasurable (hHm.indicator hAm).aestronglyMeasurable
      rw [hsplit.map_eq] at hh
      have he : (∫ v, R v ∂P) = ∫ p, A.indicator H p ∂μ := by
        simpa only [← hR] using hh.symm
      exact he.trans_le hCoreBound
  have hGData (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower) :
      Measurable (halflineDerivative J) ∧
      KernelBounds J (fun _ => 0) (halflineDerivative J) 4 := by
    rcases hJ with rfl | rfl
    · refine ⟨by
        change Measurable (fun p : ℝ × ℝ × ℝ × ℝ =>
          -Shao.C2.HalfLineMixedProfiles.slopeTime (p.1 - p.2.1) (p.1 - p.2.2.2) p.2.2.1)
        unfold Shao.C2.HalfLineMixedProfiles.slopeTime
        fun_prop,
        ⟨by norm_num, by intros; norm_num, ?_⟩⟩
      intro w y T z hw hT hy hz
      have hu : 0 < w - y := sub_pos.mpr hy
      have hv : 0 < w - z := sub_pos.mpr hz
      have hh := Shao.C2.HalfLineReflectionFormula.positive_reflection_slope_bound
        (w - y) (w - z) T hu hv hT
      have hnn : 0 ≤ Shao.C2.HalfLineMixedProfiles.slopeTime (w - y) (w - z) T := by
        unfold Shao.C2.HalfLineMixedProfiles.slopeTime
        positivity
      change |-Shao.C2.HalfLineMixedProfiles.slopeTime (w - y) (w - z) T| ≤ _
      rw [abs_neg, abs_of_nonneg hnn]
      simpa only [Shao.C2.HalfLineMixedProfiles.slopeTime,
        show (w - y) - (w - z) = z - y by ring] using hh
    · refine ⟨by
        change Measurable (fun p : ℝ × ℝ × ℝ × ℝ =>
          Shao.C2.HalfLineMixedProfiles.slopeTime (p.1 + p.2.1) (p.1 + p.2.2.2) p.2.2.1)
        unfold Shao.C2.HalfLineMixedProfiles.slopeTime
        fun_prop,
        ⟨by norm_num, by intros; norm_num, ?_⟩⟩
      intro w y T z hw hT hy hz
      have hu : 0 < w + y := by change -w < y at hy; linarith only [hy]
      have hv : 0 < w + z := by change -w < z at hz; linarith only [hz]
      have hh := Shao.C2.HalfLineReflectionFormula.positive_reflection_slope_bound
        (w + y) (w + z) T hu hv hT
      have hnn : 0 ≤ Shao.C2.HalfLineMixedProfiles.slopeTime (w + y) (w + z) T := by
        unfold Shao.C2.HalfLineMixedProfiles.slopeTime
        positivity
      change |Shao.C2.HalfLineMixedProfiles.slopeTime (w + y) (w + z) T| ≤ _
      rw [abs_of_nonneg hnn]
      simpa only [Shao.C2.HalfLineMixedProfiles.slopeTime,
        show (w + y) - (w + z) = y - z by ring, abs_sub_comm y z] using hh
  have hh0 : 0 < h0 := by dsimp only [h0]; positivity
  have hkm (sigma : LabelPerm n) : Measurable (fun a : Shao.Path n => kappa a sigma) :=
    actual_energy_cutoff_measurable h0 hh0 sigma
  have hParts (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower) :=
    source_parts_measurable_integrable J (fun _ => 0) (halflineDerivative J)
      measurable_const (hGData J hJ).1 4 (hGData J hJ).2 P x hx0 kappa hkm
  let wallBill : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ := fun J p =>
    if Shao.energy p.1 < (n : ℝ) / 2 then
      separatedSum J (halflineDerivative J) p.1 x (kappa p.1) p.2 else 0
  have hLowM : MeasurableSet {p : Shao.Path n × LabelPerm n |
      Shao.energy p.1 < (n : ℝ) / 2} :=
    measurableSet_lt (Shao.measurable_energy.comp measurable_fst) measurable_const
  have hWallM (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower) : Measurable (wallBill J) := by
    apply Measurable.ite hLowM
    · apply measurable_from_prod_countable_left
      intro sigma
      apply Finset.measurable_sum
      intro r _
      exact ((hParts J hJ).1 sigma r).2
    · exact measurable_const
  have hWallI (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower) :
      Integrable (wallBill J) (revealLaw P) := by
    apply ((hParts J hJ).2.2.2.indicator hLowM).congr
    filter_upwards [] with p
    by_cases hp : Shao.energy p.1 < (n : ℝ) / 2
    · simp only [Set.indicator_of_mem (show p ∈ {q : Shao.Path n × LabelPerm n |
        Shao.energy q.1 < (n : ℝ) / 2} from hp), wallBill, if_pos hp]
    · simp only [Set.indicator_of_notMem (show p ∉ {q : Shao.Path n × LabelPerm n |
        Shao.energy q.1 < (n : ℝ) / 2} from hp), wallBill, if_neg hp]
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
      remainingSum a j sigma = Shao.prefixSum (Spitzer.tail (Spitzer.reorder a sigma) j hjn) (n - j) := by
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
  have hDRecord (J : MonitoredDomain) (a : Shao.Path n) (sigma : LabelPerm n) (r : Fin n) :
      D (r.val + 1) (oneWallSign J)
        (Spitzer.head (Spitzer.reorder a sigma) (r.val + 1) (by omega)) =
        recordIncrement J a r sigma := by
    have he : Spitzer.head (oneWallSign J •
        Spitzer.head (Spitzer.reorder a sigma) (r.val + 1) (by omega))
          (r.val + 1 - 1) (by omega) =
        oneWallSign J • Spitzer.head (Spitzer.reorder a sigma) r.val r.isLt.le := by
      funext i
      rfl
    dsimp only [D, recordIncrement]
    rw [Shao.prefixSum_smul, Spitzer.head_prefixSum]
    rw [he]
    exact le_rfl
  have hRm : Measurable (randomReorder : Shao.Path n × LabelPerm n → Shao.Path n) :=
    measurable_from_prod_countable_left (fun sigma =>
      Measurable.of_eval fun i => measurable_pi_apply (sigma i))
  have hmap : (revealLaw P).map randomReorder = P := by
    have hInd : iIndepFun (fun i : Fin n => Function.eval i) P :=
      iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)
    have hLaw (i : Fin n) : IdentDistrib (Function.eval i) (id : ℝ → ℝ) P rho :=
      ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable,
        by simp only [Measure.map_id]; exact (measurePreserving_eval (fun _ : Fin n => rho) i).map_eq⟩
    exact iid_randomPermutation_map_eq_pi P rho (fun i : Fin n => Function.eval i)
      (fun i => measurable_pi_apply i) hInd hLaw
  have hmp : MeasurePreserving randomReorder (revealLaw P) P := ⟨hRm, hmap⟩
  let Env : MonitoredDomain → Fin n → Shao.Path n → ℝ := fun J r v =>
    if Shao.energy v < (n : ℝ) / 2 then
      D (r.val + 1) (oneWallSign J) (Spitzer.head v (r.val + 1) (by omega)) *
        W (n - (r.val + 1)) (Spitzer.tail v (r.val + 1) (by omega))
    else 0
  have hEnv (J : MonitoredDomain) (r : Fin n) :
      Measurable (Env J r) ∧ Integrable (Env J r) P ∧ (∀ v, 0 ≤ Env J r v) ∧
      (∫ v, Env J r v ∂P) ≤ 3 * (1 + t) / (beta * Real.sqrt (r.val + 1 : ℝ)) *
        Real.exp (-t / 128) := by
    have hs : oneWallSign J = 1 ∨ oneWallSign J = -1 := by
      cases J <;> simp [oneWallSign]
    simpa only [Nat.cast_add, Nat.cast_one] using
      hCore (r.val + 1) (by omega) (by omega) (oneWallSign J) hs
  have hEnvActual (J : MonitoredDomain) (r : Fin n) (p : Shao.Path n × LabelPerm n) :
      Env J r (randomReorder p) =
        if Shao.energy p.1 < (n : ℝ) / 2 then
          recordIncrement J p.1 r p.2 * ordinaryFutureWeight p.1 beta (r.val + 1) p.2
        else 0 := by
    dsimp only [Env, randomReorder]
    rw [hReorderEnergy, hDRecord]
    by_cases hp : Shao.energy p.1 < (n : ℝ) / 2
    · rw [if_pos hp, if_pos hp]
      congr 1
      dsimp only [W, ordinaryFutureWeight, futureProfile]
      rw [(hSuffix p.1 p.2 (r.val + 1) (by omega)).1,
        (hSuffix p.1 p.2 (r.val + 1) (by omega)).2]
    · rw [if_neg hp, if_neg hp]
  have hWall0 (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower)
      (p : Shao.Path n × LabelPerm n) : 0 ≤ wallBill J p := by
    dsimp only [wallBill]
    split_ifs
    · apply Finset.sum_nonneg
      intro r hr
      exact (actual_onewall_record_envelope J hJ p.1 x beta hx0 hbeta
        (kappa p.1) ⟨r, Finset.mem_range.mp hr⟩ p.2 le_rfl).1
    · exact le_rfl
  have hWallDom (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower)
      (p : Shao.Path n × LabelPerm n) :
      wallBill J p ≤ 6 * ∑ r : Fin n, Env J r (randomReorder p) := by
    by_cases hp : Shao.energy p.1 < (n : ℝ) / 2
    · dsimp only [wallBill]
      rw [if_pos hp, separatedSum,
        ← Fin.sum_univ_eq_sum_range (fun r => sourceSeparatedOvershoot J
          (halflineDerivative J) p.1 x (kappa p.1) r p.2) n, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r _
      rw [hEnvActual, if_pos hp]
      have hh := (actual_onewall_record_envelope J hJ p.1 x beta hx0 hbeta
        (kappa p.1) r p.2 le_rfl).2
      have hProd : 0 ≤ recordIncrement J p.1 r p.2 * ordinaryFutureWeight p.1 beta (r.val + 1) p.2 := by
        have hz := (hEnv J r).2.2.1 (randomReorder p)
        rwa [hEnvActual, if_pos hp] at hz
      split_ifs at hh <;> nlinarith only [hh, hProd]
    · have hz (r : Fin n) : Env J r (randomReorder p) = 0 := by rw [hEnvActual, if_neg hp]
      simp only [wallBill, if_neg hp, hz, Finset.sum_const_zero, mul_zero, le_refl]
  have hHarmonic (m : ℕ) :
      (∑ r ∈ Finset.range m, 1 / Real.sqrt ((r + 1 : ℕ) : ℝ)) ≤ 2 * Real.sqrt (m : ℝ) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hr : 0 < Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
      have hstep : 1 / Real.sqrt ((m + 1 : ℕ) : ℝ) ≤
          2 * (Real.sqrt ((m + 1 : ℕ) : ℝ) - Real.sqrt (m : ℝ)) := by
        norm_num only [Nat.cast_add, Nat.cast_one] at hr ⊢
        apply (div_le_iff₀ hr).2
        have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ (m : ℝ) + 1 by positivity)
        have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ (m : ℝ) by positivity)
        nlinarith only [h1, h2,
          sq_nonneg (Real.sqrt ((m : ℝ) + 1) - Real.sqrt (m : ℝ))]
      linarith only [ih, hstep]
  have hRootRatio : Real.sqrt (n : ℝ) / beta = Real.sqrt t := by
    have hh := hdeltaScale
    dsimp only [delta] at hh
    field_simp at hh
    apply (div_eq_iff (ne_of_gt hbeta)).2
    simpa only [mul_comm] using hh.symm
  have hWallBound (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower) :
      (∫ p, wallBill J p ∂revealLaw P) ≤
        36 * Real.sqrt t * (1 + t) * Real.exp (-t / 128) := by
    have hEI : Integrable (fun v => ∑ r : Fin n, Env J r v) P :=
      integrable_finsetSum _ fun r _ => (hEnv J r).2.1
    have hEM : Measurable (fun v => ∑ r : Fin n, Env J r v) :=
      Finset.measurable_sum _ fun r _ => (hEnv J r).1
    have hSum : (∑ r : Fin n, 1 / Real.sqrt (r.val + 1 : ℝ)) ≤ 2 * Real.sqrt (n : ℝ) := by
      have he := Fin.sum_univ_eq_sum_range (fun r => 1 / Real.sqrt ((r + 1 : ℕ) : ℝ)) n
      simpa only [Nat.cast_add, Nat.cast_one] using he.trans_le (hHarmonic n)
    calc
      _ ≤ ∫ p, 6 * ∑ r : Fin n, Env J r (randomReorder p) ∂revealLaw P :=
        integral_mono (hWallI J hJ) ((hmp.integrable_comp_of_integrable hEI).const_mul 6)
          (hWallDom J hJ)
      _ = 6 * (∫ v, ∑ r : Fin n, Env J r v ∂P) := by
        have hTransferIntegral :
            (∫ p, ∑ r : Fin n, Env J r (randomReorder p) ∂revealLaw P) =
              ∫ v, ∑ r : Fin n, Env J r v ∂P := by
          have hh := integral_map (μ := revealLaw P) hRm.aemeasurable hEM.aestronglyMeasurable
          rw [hmap] at hh
          exact hh.symm
        rw [integral_const_mul, hTransferIntegral]
      _ = 6 * ∑ r : Fin n, ∫ v, Env J r v ∂P := by
        rw [integral_finsetSum _ fun r _ => (hEnv J r).2.1]
      _ ≤ 6 * ∑ r : Fin n, 3 * (1 + t) / (beta * Real.sqrt (r.val + 1 : ℝ)) *
          Real.exp (-t / 128) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum fun r _ => (hEnv J r).2.2.2
      _ = (18 * (1 + t) / beta * Real.exp (-t / 128)) *
          ∑ r : Fin n, 1 / Real.sqrt (r.val + 1 : ℝ) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ ≤ (18 * (1 + t) / beta * Real.exp (-t / 128)) * (2 * Real.sqrt (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hSum (by positivity)
      _ = _ := by rw [← hRootRatio]; ring
  have hBillEq : bill = fun p => wallBill .upper p + wallBill .lower p := by
    funext p
    dsimp only [bill, wallBill]
    split_ifs <;> ring
  have hBillM : Measurable bill := by
    rw [hBillEq]
    exact (hWallM .upper (Or.inl rfl)).add (hWallM .lower (Or.inr rfl))
  have hBillI : Integrable bill (revealLaw P) := by
    rw [hBillEq]
    exact (hWallI .upper (Or.inl rfl)).add (hWallI .lower (Or.inr rfl))
  have hBill0 (p : Shao.Path n × LabelPerm n) : 0 ≤ bill p := by
    rw [hBillEq]
    exact add_nonneg (hWall0 .upper (Or.inl rfl) p) (hWall0 .lower (Or.inr rfl) p)
  have hMain : (∫ p, bill p ∂revealLaw P) ≤
      72 * Real.sqrt t * (1 + t) * Real.exp (-t / 128) := by
    rw [hBillEq, integral_add (hWallI .upper (Or.inl rfl)) (hWallI .lower (Or.inr rfl))]
    linarith only [hWallBound .upper (Or.inl rfl), hWallBound .lower (Or.inr rfl)]
  have hres1 : delta * (1 + x) ^ 3 ≤ 1 :=
    hres.trans (Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg x]))
  have hCube : (1 + x) ^ 3 ≤ Real.sqrt t := by
    calc
      (1 + x) ^ 3 = (delta * (1 + x) ^ 3) * Real.sqrt t := by
        calc
          _ = (delta * Real.sqrt t) * (1 + x) ^ 3 := by rw [hdeltaScale, one_mul]
          _ = _ := by ring
      _ ≤ 1 * Real.sqrt t := mul_le_mul_of_nonneg_right hres1 (Real.sqrt_nonneg t)
      _ = _ := one_mul _
  have htPower : (1 + x) ^ 6 ≤ t := by
    have hh := pow_le_pow_left₀ (show 0 ≤ (1 + x) ^ 3 by positivity) hCube 2
    rw [Real.sq_sqrt ht0.le] at hh
    nlinarith only [hh]
  have ht1 : 1 ≤ t := by
    have hh : (1 : ℝ) ≤ (1 + x) ^ 6 := one_le_pow₀ (by linarith only [hx])
    exact hh.trans htPower
  have ht512 : 512 * x ^ 2 ≤ t := by
    have hx4 : (512 : ℝ) ≤ x ^ 4 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16) hx 4
      norm_num at hh
      linarith only [hh]
    have hxp := mul_le_mul_of_nonneg_right hx4 (sq_nonneg x)
    have hxx := pow_le_pow_left₀ hx0.le (show x ≤ 1 + x by linarith) 6
    nlinarith only [hxp, hxx, htPower]
  have hQuadraticExp (y : ℝ) (hy : 0 ≤ y) : y ^ 2 ≤ 2 * Real.exp y := by
    have hbase : 1 + y / 3 ≤ Real.exp (y / 3) := by
      simpa only [add_comm] using Real.add_one_le_exp (y / 3)
    have hcube := pow_le_pow_left₀ (show 0 ≤ 1 + y / 3 by positivity) hbase 3
    have he : Real.exp (y / 3) ^ 3 = Real.exp y := by
      rw [pow_succ, pow_two, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [he] at hcube
    have hh := mul_nonneg hy (sq_nonneg (y - 3))
    nlinarith only [hcube, hh, sq_nonneg y, hy]
  have hPolyExp : t ^ 2 * Real.exp (-t / 256) ≤ 2 * 256 ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right (hQuadraticExp (t / 256) (by positivity))
      (Real.exp_pos (-t / 256)).le
    have he : Real.exp (t / 256) * Real.exp (-t / 256) = 1 := by
      rw [← Real.exp_add, show t / 256 + -t / 256 = 0 by ring, Real.exp_zero]
    nlinarith only [hh, he]
  have hAbsorb : 72 * Real.sqrt t * (1 + t) * Real.exp (-t / 128) ≤
      18874368 * delta * Real.exp (-2 * x ^ 2) := by
    have hsqrt : Real.sqrt t = delta * t := by
      have hh := congrArg (fun z : ℝ => z * Real.sqrt t) hdeltaScale
      rw [mul_assoc, Real.mul_self_sqrt ht0.le, one_mul] at hh
      exact hh.symm
    have hsplitExp : Real.exp (-t / 128) = Real.exp (-t / 256) * Real.exp (-t / 256) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = 72 * delta * t * (1 + t) * Real.exp (-t / 128) := by rw [hsqrt]; ring
      _ ≤ 144 * delta * t ^ 2 * Real.exp (-t / 128) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        have hh := mul_le_mul_of_nonneg_left (show 1 + t ≤ 2 * t by linarith only [ht1])
          (show 0 ≤ 72 * delta * t by positivity)
        nlinarith only [hh]
      _ = 144 * delta * (t ^ 2 * Real.exp (-t / 256)) * Real.exp (-t / 256) := by
        rw [hsplitExp]
        ring
      _ ≤ 144 * delta * (2 * 256 ^ 2) * Real.exp (-t / 256) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPolyExp (by positivity))
          (Real.exp_pos _).le
      _ = 18874368 * delta * Real.exp (-t / 256) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith only [ht512]))
        (by positivity)
  run_tac
    let formulaName := Lean.mkPrivateNameCore "Shao.Probability.GaussianTail".toName
      "Shao.density_formula".toName
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent "hDensityFormula".toName) := $(Lean.mkIdent formulaName)))
  have hExpTail : Real.exp (-2 * x ^ 2) ≤ 3 * Shao.standardNormalTail x := by
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
    have hratio : (1 + x) * Real.exp (-3 * x ^ 2 / 2) ≤ 1 := by
      calc
        _ ≤ Real.exp x * Real.exp (-3 * x ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right (by simpa only [add_comm] using Real.add_one_le_exp x)
            (Real.exp_pos _).le
        _ = Real.exp (x - 3 * x ^ 2 / 2) := by rw [← Real.exp_add]; congr 1 <;> ring
        _ ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [hx, sq_nonneg (x - 1)])
    have hcompare : (1 + x) * Real.exp (-2 * x ^ 2) ≤ Real.exp (-x ^ 2 / 2) := by
      have he : Real.exp (-2 * x ^ 2) = Real.exp (-x ^ 2 / 2) * Real.exp (-3 * x ^ 2 / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      nlinarith only [mul_le_mul_of_nonneg_left hratio (Real.exp_pos (-x ^ 2 / 2)).le]
    have hh : Real.exp (-2 * x ^ 2) ≤ 3 * Shao.standardNormalDensity x / (1 + x) := by
      apply (le_div_iff₀ hplus).2
      nlinarith only [hcompare, hphi]
    apply hh.trans
    have hm := mul_le_mul_of_nonneg_left (Shao.standardNormal_mills_bounds x hx0.le).1
      (by norm_num : (0 : ℝ) ≤ 3)
    convert hm using 1 <;> ring
  refine ⟨hBillM, hBillI, hBill0, hMain, ?_, ?_⟩
  · apply (hMain.trans hAbsorb).trans
    nlinarith only [mul_nonneg hdelta0.le (Real.exp_pos (-2 * x ^ 2)).le]
  · apply (hMain.trans hAbsorb).trans
    have hh := mul_le_mul_of_nonneg_left hExpTail
      (show 0 ≤ 18874368 * delta by positivity)
    nlinarith only [hh]

theorem iid_actual_low_full_energy_signed_separated_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ΩB : Type*} [MeasurableSpace ΩB]
        (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
        IsBrownianReal B PB →
        let Q : Measure BridgeNoise := bridgeLaw B PB
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
            let kappa : Shao.Path n → LabelPerm n → ℕ :=
              fun a sigma => energyCutoff a h0 sigma
            let bill : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
              if Shao.energy p.1 < (n : ℝ) / 2 then
                ∑ r ∈ Finset.range n,
                  actualDoubleSeparated Q x p.1 (kappa p.1) r p.2
              else 0
            Measurable bill ∧ Integrable bill (revealLaw P) ∧
              (∀ p : Shao.Path n × LabelPerm n, 0 ≤ bill p) ∧
              (∫ p, bill p ∂revealLaw P) ≤
                C * delta * Shao.standardNormalTail x
 := by
  classical
  obtain ⟨CP, hCP, hPair⟩ := iid_actual_low_full_energy_two_halfline_budget
  obtain ⟨CK, hCK, hClass⟩ :=
    Shao.C2.ActualDoubleSeparatedClassification.actual_double_separated_three_bill
  obtain ⟨CN, hCN, hNegative⟩ :=
    Shao.C2.ActualBadIntervalNegativeBudget.actual_bad_interval_negative_budget
  refine ⟨(CK + 2) * CP + CN, by positivity, ?_⟩
  intro ΩB instΩB B PB instPB hB Q rho instRho Bcap hBcap hsupport hmean hsecond
    beta n hn x hx hBscale delta hres h0 P kappa bill
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
  have hh0 : 0 < h0 := by dsimp only [h0]; positivity
  have hkm (sigma : LabelPerm n) : Measurable (fun a : Shao.Path n => kappa a sigma) :=
    actual_energy_cutoff_measurable h0 hh0 sigma
  have hkcap (a : Shao.Path n) (sigma : LabelPerm n) :
      kappa a sigma ≤ energyCutoff a (4 * beta ^ 2) sigma := le_rfl
  have hB100 : Bcap ≤ Real.sqrt (n : ℝ) / (100 * x) := by
    apply hBscale.trans
    apply (div_le_div_iff₀ (by positivity : 0 < 200 * x)
      (by positivity : 0 < 100 * x)).2
    have hh := mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hx0.le
    nlinarith only [hh]
  let pairBill : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
    if Shao.energy p.1 < (n : ℝ) / 2 then
      separatedSum .upper (halflineDerivative .upper) p.1 x (kappa p.1) p.2 +
        separatedSum .lower (halflineDerivative .lower) p.1 x (kappa p.1) p.2
    else 0
  let negativeBill : (Shao.Path n × LabelPerm n) → ℝ :=
    Shao.C2.ActualBadIntervalNegativeBudget.actualBadIntervalNegativeBill Q x kappa
  have hp := hPair rho Bcap hBcap hsupport hmean hsecond n hn x hx hBscale hres
  change Measurable pairBill ∧ Integrable pairBill (revealLaw P) ∧
    (∀ p, 0 ≤ pairBill p) ∧ _ ∧ _ ∧
    (∫ p, pairBill p ∂revealLaw P) ≤ CP * delta * Shao.standardNormalTail x at hp
  have hneg := hNegative rho Bcap hBcap hsupport hmean hsecond n hn x hx hB100 hres
    B PB hB kappa hkm hkcap
  change Measurable negativeBill ∧ Integrable negativeBill (revealLaw P) ∧
    0 ≤ (∫ p, negativeBill p ∂revealLaw P) ∧
    (∫ p, negativeBill p ∂revealLaw P) ≤ CN * delta * Shao.standardNormalTail x at hneg
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw B PB hB
  have hReflection : HalflineReflectionIdentities Q := by
    constructor
    · intro w y T z _hw hT hy hz
      simpa only [Shao.C2.HalfLineReflectionFormula.upperReflection] using
        Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula B PB hB w y T z hT hy hz
    · intro w y T z _hw hT hy hz
      simpa only [Shao.C2.HalfLineReflectionFormula.lowerReflection] using
        Shao.C2.BridgeLowerIdentification.bridge_lower_formula B PB hB w y T z hT hy hz
  have hRegular (w y T z : ℝ) (hw : 0 < w) (hT : 0 < T)
      (hy : |y| < w) (hz : |z| < w) :
      DifferentiableAt ℝ (fun s : ℝ =>
        Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w s T z) y :=
    (Shao.C2.BridgeIntervalImageResolved.sourceIntervalCompletion_spatial_hasDerivAt
      B PB hB w y T z hw hy hz hT).differentiableAt
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
    (eventCompletionKernel_data J Q).1 (hData J).1 4 (hData J).2 P x hx0 kappa hkm
  have hSepM (J : MonitoredDomain) (r : ℕ) :
      Measurable (fun p : Shao.Path n × LabelPerm n => sourceSeparatedOvershoot J
        (actualDerivativeFamily Q J) p.1 x (kappa p.1) r p.2) := by
    apply measurable_from_prod_countable_left
    intro sigma
    exact ((hParts J).1 sigma r).2
  have hFullM : Measurable (fun p : Shao.Path n × LabelPerm n =>
      ∑ r ∈ Finset.range n, actualDoubleSeparated Q x p.1 (kappa p.1) r p.2) := by
    apply Finset.measurable_sum
    intro r _
    exact ((hSepM .upper r).add (hSepM .lower r)).sub (hSepM .interval r)
  have hFullI : Integrable (fun p : Shao.Path n × LabelPerm n =>
      ∑ r ∈ Finset.range n, actualDoubleSeparated Q x p.1 (kappa p.1) r p.2)
      (revealLaw P) := by
    apply integrable_finsetSum
    intro r _
    exact (((hParts .upper).2.1 r).2.add ((hParts .lower).2.1 r).2).sub
      ((hParts .interval).2.1 r).2
  have hLowM : MeasurableSet {p : Shao.Path n × LabelPerm n |
      Shao.energy p.1 < (n : ℝ) / 2} :=
    measurableSet_lt (Shao.measurable_energy.comp measurable_fst) measurable_const
  have hBillM : Measurable bill := Measurable.ite hLowM hFullM measurable_const
  have hBillI : Integrable bill (revealLaw P) := by
    apply (hFullI.indicator hLowM).congr
    filter_upwards [] with p
    by_cases hp : Shao.energy p.1 < (n : ℝ) / 2
    · simp only [Set.indicator_of_mem (show p ∈ {q : Shao.Path n × LabelPerm n |
        Shao.energy q.1 < (n : ℝ) / 2} from hp), bill, if_pos hp]
    · simp only [Set.indicator_of_notMem (show p ∉ {q : Shao.Path n × LabelPerm n |
        Shao.energy q.1 < (n : ℝ) / 2} from hp), bill, if_neg hp]
  have hNeg0 (p : Shao.Path n × LabelPerm n) : 0 ≤ negativeBill p := by
    apply Finset.sum_nonneg
    intro r _
    split_ifs <;> positivity
  have hRank (p : Shao.Path n × LabelPerm n) (r : ℕ) (hr : r < n) :
      0 ≤ actualDoubleSeparated Q x p.1 (kappa p.1) r p.2 ∧
      actualDoubleSeparated Q x p.1 (kappa p.1) r p.2 ≤
        (CK + 2) * (sourceSeparatedOvershoot .upper (halflineDerivative .upper)
          p.1 x (kappa p.1) r p.2 +
          sourceSeparatedOvershoot .lower (halflineDerivative .lower)
            p.1 x (kappa p.1) r p.2) +
        (if 3 * x * Real.sqrt (remainingEnergy p.1 r p.2) / 2 ≤
            |remainingSum p.1 r p.2| then
          max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
            p.1 x (kappa p.1) r p.2) 0 else 0) := by
    let U : ℝ := sourceSeparatedOvershoot .upper (halflineDerivative .upper)
      p.1 x (kappa p.1) r p.2
    let L : ℝ := sourceSeparatedOvershoot .lower (halflineDerivative .lower)
      p.1 x (kappa p.1) r p.2
    let I : ℝ := sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
      p.1 x (kappa p.1) r p.2
    have hu : 0 ≤ U := (actual_onewall_record_envelope .upper (Or.inl rfl)
      p.1 x beta hx0 hbeta (kappa p.1) ⟨r, hr⟩ p.2 le_rfl).1
    have hl : 0 ≤ L := (actual_onewall_record_envelope .lower (Or.inr rfl)
      p.1 x beta hx0 hbeta (kappa p.1) ⟨r, hr⟩ p.2 le_rfl).1
    have hh := hClass B PB hB p.1 x hx (kappa p.1) r p.2
    change 0 ≤ U + L - I ∧ U + L - I ≤
      CK * Real.exp (-x ^ 2) * (U + L) +
      (if 3 * x * Real.sqrt (remainingEnergy p.1 r p.2) / 2 <
        |remainingSum p.1 r p.2| then U + L + max (-I) 0 else 0) +
      (if Shao.C2.ActualDoubleSeparatedClassification.prefixAlive .lower p.1 x r p.2
        then 0 else U) +
      (if Shao.C2.ActualDoubleSeparatedClassification.prefixAlive .upper p.1 x r p.2
        then 0 else L) at hh
    have he : CK * Real.exp (-x ^ 2) * (U + L) ≤ CK * (U + L) := by
      have hex : Real.exp (-x ^ 2) ≤ 1 :=
        (Real.exp_le_exp.2 (by nlinarith only [sq_nonneg x])).trans_eq Real.exp_zero
      nlinarith only [mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hex hCK.le) (add_nonneg hu hl)]
    have hbad :
        (if 3 * x * Real.sqrt (remainingEnergy p.1 r p.2) / 2 <
          |remainingSum p.1 r p.2| then U + L + max (-I) 0 else 0) ≤
        U + L + (if 3 * x * Real.sqrt (remainingEnergy p.1 r p.2) / 2 ≤
          |remainingSum p.1 r p.2| then max (-I) 0 else 0) := by
      by_cases hs : 3 * x * Real.sqrt (remainingEnergy p.1 r p.2) / 2 <
          |remainingSum p.1 r p.2|
      · rw [if_pos hs, if_pos (le_of_lt hs)]
      · rw [if_neg hs]
        split_ifs <;> positivity
    have hprevL :
        (if Shao.C2.ActualDoubleSeparatedClassification.prefixAlive .lower p.1 x r p.2
          then 0 else U) ≤ U := by split_ifs <;> linarith only [hu]
    have hprevU :
        (if Shao.C2.ActualDoubleSeparatedClassification.prefixAlive .upper p.1 x r p.2
          then 0 else L) ≤ L := by split_ifs <;> linarith only [hl]
    exact ⟨hh.1, by change U + L - I ≤ _; nlinarith only [hh.2, he, hbad, hprevL, hprevU]⟩
  have hBill0 (p : Shao.Path n × LabelPerm n) : 0 ≤ bill p := by
    dsimp only [bill]
    split_ifs
    · exact Finset.sum_nonneg fun r hr => (hRank p r (Finset.mem_range.mp hr)).1
    · exact le_rfl
  have hDom (p : Shao.Path n × LabelPerm n) :
      bill p ≤ (CK + 2) * pairBill p + negativeBill p := by
    by_cases hpLow : Shao.energy p.1 < (n : ℝ) / 2
    · have hh := Finset.sum_le_sum (s := Finset.range n)
        (fun r hr => (hRank p r (Finset.mem_range.mp hr)).2)
      dsimp only [bill, pairBill]
      rw [if_pos hpLow, if_pos hpLow]
      convert hh using 1
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, separatedSum,
        negativeBill, Shao.C2.ActualBadIntervalNegativeBudget.actualBadIntervalNegativeBill]
    · simpa only [bill, pairBill, if_neg hpLow, mul_zero, zero_add] using hNeg0 p
  refine ⟨hBillM, hBillI, hBill0, ?_⟩
  calc
    (∫ p, bill p ∂revealLaw P) ≤
        ∫ p, (CK + 2) * pairBill p + negativeBill p ∂revealLaw P :=
      integral_mono hBillI ((hp.2.1.const_mul (CK + 2)).add hneg.2.1) hDom
    _ = (CK + 2) * (∫ p, pairBill p ∂revealLaw P) +
        (∫ p, negativeBill p ∂revealLaw P) := by
      rw [integral_add (hp.2.1.const_mul (CK + 2)) hneg.2.1, integral_const_mul]
    _ ≤ (CK + 2) * (CP * delta * Shao.standardNormalTail x) +
        CN * delta * Shao.standardNormalTail x :=
      add_le_add (mul_le_mul_of_nonneg_left hp.2.2.2.2.2 (by positivity)) hneg.2.2.2
    _ = ((CK + 2) * CP + CN) * delta * Shao.standardNormalTail x := by ring

end Shao.Probability.SourceActualRecordLowFullEnergy
