/- Mathematics-only candidate. No formal source or Lean checks authorized.
   PR355 exact source is a qualification-pending dependency at read time. -/
import Shao.Probability.SourceActualRegularLocal
import Shao.Probability.SourceSuffixMomentBudgets
import Shao.C2.AuxiliaryTiltedProductEnergy
import Shao.C2.BridgeUpperAffineIdentification
import Shao.C2.BridgeLowerIdentification
import Shao.Probability.GaussianTail
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Tilted

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
noncomputable section
namespace Shao.Probability.SourceRegularRetainedProbability
open MeasureTheory ProbabilityTheory
open SourcePermutationReveal SourceSeparatedOvershoot
open SourceActualLocalProfileBudget SourceActualIntervalProfileBudget
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open scoped BigOperators Classical NNReal

local instance labelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

private theorem rrp_unsummed_cubic_grid :
    ∃ K : ℝ, 0 < K ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho],
        Integrable (fun z : ℝ => z ^ 2) rho →
        Integrable (fun z : ℝ => |z| ^ 3) rho →
        (∫ z : ℝ, z ∂rho) = 0 →
        (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        let H : ℝ := 4 * beta ^ 2
        let P : (m : ℕ) → Measure (Shao.Path (m + 1)) :=
          fun m => Measure.pi (fun _ : Fin (m + 1) => rho)
        let selected : (m : ℕ) → Shao.Path (m + 1) → ℝ := fun m v =>
          if 0 < Shao.energy v ∧ H ≤ Shao.energy v then
            |v 0| ^ 3 / (Real.sqrt (Shao.energy v)) ^ 3 *
              (1 + |Shao.prefixSum v (m + 1)| / Real.sqrt (Shao.energy v)) ^ 3
          else 0
        (∀ m : ℕ, Measurable (selected m) ∧ Integrable (selected m) (P m)) ∧
          ∀ N : ℕ, (∑ m ∈ Finset.range N, ∫ v, selected m v ∂P m) ≤ K := by
  classical
  obtain ⟨CI, hCI, hInverse⟩ := iid_marked_cutoff_inverse_moments 3 3 (Or.inr rfl)
  let c : ℝ := (1 - Real.exp (-2)) / 8
  have hc : 0 < c := by
    have : Real.exp (-2 : ℝ) < 1 := by simpa using Real.exp_lt_exp.mpr (show (-2 : ℝ) < 0 by norm_num)
    dsimp [c]; linarith
  have hc1 : c < 1 := by dsimp [c]; nlinarith [Real.exp_pos (-2)]
  let K : ℝ := 2 * CI / c
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro rho hRho h2 h3 hmean hsecond beta H P selected
  have hBeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one rho h2 h3 hsecond
  have hb : 0 < beta := by linarith
  have hH : 0 < H := by dsimp [H]; positivity
  have hH4 : 4 ≤ H := by dsimp [H]; nlinarith
  have hRetm : Measurable (fun z : ℝ => if z ^ 2 ≤ H then z ^ 2 else 0) :=
    Measurable.ite (measurableSet_le (measurable_id.pow_const 2) measurable_const)
      (measurable_id.pow_const 2) measurable_const
  have hReti : Integrable (fun z : ℝ => if z ^ 2 ≤ H then z ^ 2 else 0) rho :=
    h2.mono' hRetm.aestronglyMeasurable (ae_of_all _ fun z => by
      split_ifs
      · simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z), le_refl]
      · simpa only [Real.norm_eq_abs, abs_zero] using sq_nonneg z)
  have hCut (z : ℝ) : z ^ 2 ≤ (if z ^ 2 ≤ H then z ^ 2 else 0) + |z| ^ 3 / (2 * beta) := by
    by_cases hz : z ^ 2 ≤ H
    · simp only [if_pos hz]; exact le_add_of_nonneg_right (by positivity)
    · have hz' : 2 * beta ≤ |z| := by
        have hh : 4 * beta ^ 2 < z ^ 2 := lt_of_not_ge hz
        nlinarith [sq_abs z, abs_nonneg z]
      simp only [if_neg hz, zero_add]
      apply (le_div_iff₀ (by positivity : 0 < 2 * beta)).mpr
      have hh := mul_le_mul_of_nonneg_right hz' (sq_nonneg z)
      nlinarith [sq_abs z]
  have hRetiLower : (1 / 2 : ℝ) ≤ ∫ z : ℝ, if z ^ 2 ≤ H then z ^ 2 else 0 ∂rho := by
    have hh := integral_mono h2 (hReti.add (h3.div_const (2 * beta))) hCut
    dsimp only [Pi.add_apply] at hh
    rw [integral_add hReti (h3.div_const (2 * beta)), integral_div, hsecond] at hh
    change (1 : ℝ) ≤ (∫ z : ℝ, if z ^ 2 ≤ H then z ^ 2 else 0 ∂rho) + beta / (2 * beta) at hh
    have he : beta / (2 * beta) = (1 / 2 : ℝ) := by field_simp
    rw [he] at hh
    linarith
  let A : ℝ → ℝ := fun u => ∫ z : ℝ, |z| ^ 3 * Real.exp (-u * z ^ 2) ∂rho
  let kernel : ℕ → ℝ → ℝ := fun m s =>
    Real.rpow s (1 / 2 : ℝ) * A (s / 2) * Real.exp (-c * s * (m : ℝ))
  have hMaster (m : ℕ) :
      Integrable (selected m) (P m) ∧
      IntegrableOn (kernel m) (Set.Ioo 0 (1 / H)) ∧
      (∫ v, selected m v ∂P m) ≤ CI * ∫ s : ℝ in Set.Ioo 0 (1 / H), kernel m s := by
    simpa only [selected, P, kernel, A, c, if_pos hRetiLower, Nat.cast_ofNat, show (3 : ℝ) / 2 - 1 = 1 / 2 by norm_num]
      using hInverse rho h2 hmean hsecond m H hH
  have hSm (m : ℕ) : Measurable (selected m) := by
    dsimp [selected]
    apply Measurable.ite ((measurableSet_lt measurable_const Shao.measurable_energy).inter
      (measurableSet_le measurable_const Shao.measurable_energy))
    · exact (((continuous_abs.measurable.comp (measurable_pi_apply (X := fun _ : Fin (m + 1) => ℝ) 0)).pow_const 3).div
        (Shao.measurable_energy.sqrt.pow_const 3)).mul
        ((measurable_const.add ((continuous_abs.measurable.comp (Shao.measurable_prefixSum (m + 1))).div
          Shao.measurable_energy.sqrt)).pow_const 3)
    · exact measurable_const
  refine ⟨fun m => ⟨hSm m, (hMaster m).1⟩, ?_⟩
  intro N
  have hA (s : ℝ) (hs : 0 < s) : 0 ≤ A (s / 2) ∧ A (s / 2) ≤ beta := by
    have hpoint (z : ℝ) : 0 ≤ |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2) ∧
        |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2) ≤ |z| ^ 3 := by
      refine ⟨by positivity, ?_⟩
      exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg z]))
    have hi : Integrable (fun z : ℝ => |z| ^ 3 * Real.exp (-(s / 2) * z ^ 2)) rho :=
      h3.mono' (by fun_prop) (ae_of_all _ fun z => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hpoint z).1] using (hpoint z).2)
    exact ⟨integral_nonneg (fun z => (hpoint z).1), integral_mono hi h3 (fun z => (hpoint z).2)⟩
  have hGeo (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) (1 / H)) :
      (∑ m ∈ Finset.range N, Real.exp (-c * s * (m : ℝ))) ≤ 2 / (c * s) := by
    have hcs : 0 < c * s := mul_pos hc hs.1
    have hs1 : s < 1 := hs.2.trans_le (by simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (show (1 : ℝ) ≤ H by linarith))
    have hcs1 : c * s < 1 := (mul_lt_mul_of_pos_right hc1 hs.1).trans (by simpa using hs1)
    let z : ℝ := Real.exp (-c * s)
    have hz : 0 < z := Real.exp_pos _
    have hz1 : z < 1 := by dsimp [z]; exact Real.exp_lt_one_iff.mpr (by nlinarith)
    have hden : c * s / 2 ≤ 1 - z := by
      have he := Real.add_one_le_exp (c * s)
      have hmul : z * Real.exp (c * s) = 1 := by
        dsimp [z]; rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      have he' : z * (1 + c * s) ≤ 1 := by nlinarith
      nlinarith
    have htel (M : ℕ) : (1 - z) * (∑ m ∈ Finset.range M, z ^ m) = 1 - z ^ M := by
      induction M with
      | zero => simp
      | succ M ih => rw [Finset.sum_range_succ, pow_succ, mul_add, ih]; ring
    have hsum : (∑ m ∈ Finset.range N, z ^ m) ≤ 2 / (c * s) := by
      apply (le_div_iff₀ hcs).mpr
      have hh := htel N
      have hnonneg : 0 ≤ ∑ m ∈ Finset.range N, z ^ m := Finset.sum_nonneg (fun _ _ => pow_nonneg hz.le _)
      have hmul := mul_le_mul_of_nonneg_right hden hnonneg
      nlinarith [pow_nonneg hz.le N]
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro m _
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hHalfInt : IntegrableOn (fun s : ℝ => Real.rpow s (-1 / 2 : ℝ)) (Set.Ioo 0 (1 / H)) ∧
      (∫ s : ℝ in Set.Ioo 0 (1 / H), Real.rpow s (-1 / 2 : ℝ)) = 1 / beta := by
    simp only [Real.rpow_eq_pow]
    have hi : IntervalIntegrable (fun s : ℝ => s ^ (-1 / 2 : ℝ)) volume 0 (1 / H) :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have hio : IntegrableOn (fun s : ℝ => s ^ (-1 / 2 : ℝ)) (Set.Ioc 0 (1 / H)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ 1 / H)).1 hi
    refine ⟨hio.mono_set Set.Ioo_subset_Ioc_self, ?_⟩
    have he := integral_rpow (a := (0 : ℝ)) (b := 1 / H) (r := (-1 / 2 : ℝ)) (Or.inl (by norm_num))
    rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 1 / H), integral_Ioc_eq_integral_Ioo] at he
    have hsqrt : Real.sqrt H = 2 * beta := by
      rw [show H = (2 * beta) ^ 2 by dsimp [H]; ring, Real.sqrt_sq (by positivity)]
    have heval : (1 / H) ^ (1 / 2 : ℝ) = 1 / (2 * beta) := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one, hsqrt]
    norm_num only [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num,
      Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), sub_zero] at he
    rw [heval] at he
    convert he using 1 <;> field_simp
  have hSumInt : IntegrableOn (fun s : ℝ => ∑ m ∈ Finset.range N, kernel m s) (Set.Ioo 0 (1 / H)) :=
    integrable_finsetSum _ (fun m _ => (hMaster m).2.1)
  have hMajor : (∫ s : ℝ in Set.Ioo 0 (1 / H), ∑ m ∈ Finset.range N, kernel m s) ≤
      (2 * beta / c) * (1 / beta) := by
    have hi := hHalfInt.1.const_mul (2 * beta / c)
    have hbnd := integral_mono_ae hSumInt hi
      ((ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun s hs => by
        have hh := hGeo s hs
        have ha := hA s hs.1
        have he : Real.rpow s (1 / 2 : ℝ) = s * Real.rpow s (-1 / 2 : ℝ) := by
          change s ^ (1 / 2 : ℝ) = s * s ^ (-1 / 2 : ℝ)
          rw [show (1 / 2 : ℝ) = 1 + (-1 / 2 : ℝ) by norm_num,
            Real.rpow_add hs.1, Real.rpow_one]
        calc
          (∑ m ∈ Finset.range N, kernel m s) =
              (Real.rpow s (1 / 2 : ℝ) * A (s / 2)) *
                (∑ m ∈ Finset.range N, Real.exp (-c * s * (m : ℝ))) := by
            simp only [kernel, Finset.mul_sum]
          _ ≤ (Real.rpow s (1 / 2 : ℝ) * beta) * (2 / (c * s)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left ha.2 (Real.rpow_nonneg hs.1.le _)) hh
              (Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))
              (mul_nonneg (Real.rpow_nonneg hs.1.le _) hb.le)
          _ = (2 * beta / c) * Real.rpow s (-1 / 2 : ℝ) := by
            rw [he]; field_simp [hc.ne', hs.1.ne'] <;> ring))
    simpa only [integral_const_mul, hHalfInt.2] using hbnd
  calc
    (∑ m ∈ Finset.range N, ∫ v, selected m v ∂P m) ≤
        ∑ m ∈ Finset.range N, CI * ∫ s : ℝ in Set.Ioo 0 (1 / H), kernel m s :=
      Finset.sum_le_sum (fun m _ => (hMaster m).2.2)
    _ = CI * (∫ s : ℝ in Set.Ioo 0 (1 / H), ∑ m ∈ Finset.range N, kernel m s) := by
      rw [← Finset.mul_sum, integral_finsetSum _ (fun m _ => (hMaster m).2.1)]
    _ ≤ CI * ((2 * beta / c) * (1 / beta)) := mul_le_mul_of_nonneg_left hMajor hCI.le
    _ = K := by dsimp [K]; field_simp

private theorem rrp_damped_energy_grid :
    ∃ K : ℝ, 0 < K ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho],
        Integrable (fun z : ℝ => z ^ 2) rho →
        Integrable (fun z : ℝ => |z| ^ 3) rho →
        (∫ z : ℝ, z ∂rho) = 0 →
        (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), 16 ≤ x →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          let delta : ℝ := beta / Real.sqrt (n : ℝ)
          let H : ℝ := 4 * beta ^ 2
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
          let T : Shao.Path n → Fin n → ℝ := fun a r =>
            Shao.energy a - Shao.prefixSquares a r.val
          let d : Shao.Path n → Fin n → ℝ := fun a r =>
            Shao.prefixSum a n - Shao.prefixSum a r.val
          let G : Shao.Path n → Fin n → ℝ := fun a r =>
            if 0 < T a r ∧ H ≤ T a r then
              |a r| ^ 3 / (Real.sqrt (T a r)) ^ 3 *
                (1 + |d a r| / Real.sqrt (T a r)) ^ 3 *
                Real.exp (-x ^ 2 * Shao.energy a / T a r)
            else 0
          Measurable (fun a => ∑ r : Fin n, G a r) ∧
            Integrable (fun a => ∑ r : Fin n, G a r) P ∧
            (∫ a, ∑ r : Fin n, G a r ∂P) ≤ K * delta * Real.exp (-x ^ 2) := by
  classical
  obtain ⟨CE, hCE, hEarlyRaw⟩ := iid_early_cubic_suffix_budget
  obtain ⟨CT, hCT, hLateRaw⟩ := iid_late_fifth_and_cubic_suffix_budgets
  obtain ⟨KU, hKU, hUniformRaw⟩ := rrp_unsummed_cubic_grid
  refine ⟨4 * CE + 4 * CT + 32 * KU, by positivity, ?_⟩
  intro rho hRho h2 h3 hmean hsecond n hn x hx beta delta H P T d G
  let Pm : (t : ℕ) → Measure (Shao.Path t) := fun t => Measure.pi (fun _ : Fin t => rho)
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hPm (t : ℕ) : IsProbabilityMeasure (Pm t) := by dsimp [Pm]; infer_instance
  have hBeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one rho h2 h3 hsecond
  have hb : 0 < beta := by linarith
  have hH : 0 < H := by dsimp [H]; positivity
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnS : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hdelta : 0 < delta := div_pos hb hnS
  have hsecondPos : 0 < ∫ z : ℝ, z ^ 2 ∂rho := by rw [hsecond]; norm_num
  let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / Real.sqrt (n : ℝ)) rho
  let R0 : ℝ := Shao.truncationBudget normalizedLaw n 0
  let h : ℝ := 4 * (n : ℝ) * R0 ^ 2
  have hRaw := raw_truncation_budget_suffix_geometry rho n hn h2 hsecondPos
  simp only [hsecond, mul_one] at hRaw
  have hRpos : 0 < R0 := hRaw.1
  have hhpos : 0 < h := hRaw.2.2.2.1
  have hRle : R0 ≤ delta := by
    have hFi : Integrable (fun z : ℝ => Shao.truncationF (z / Real.sqrt (n : ℝ))) rho := by
      simpa only [div_eq_mul_inv, one_div, mul_comm] using
        Shao.integrable_truncationF_mul rho h2 ((Real.sqrt (n : ℝ))⁻¹)
    have hCi : Integrable (fun z : ℝ => |z / Real.sqrt (n : ℝ)| ^ 3) rho := by
      simpa only [abs_div, abs_of_pos hnS, div_pow] using h3.div_const ((Real.sqrt (n : ℝ)) ^ 3)
    have hPoint (z : ℝ) : Shao.truncationF (z / Real.sqrt (n : ℝ)) ≤ |z / Real.sqrt (n : ℝ)| ^ 3 := by
      unfold Shao.truncationF
      have hm := min_le_left |z / Real.sqrt (n : ℝ)| (1 : ℝ)
      have hh := mul_le_mul_of_nonneg_left hm (sq_nonneg (z / Real.sqrt (n : ℝ)))
      calc
        _ ≤ (z / Real.sqrt (n : ℝ)) ^ 2 * |z / Real.sqrt (n : ℝ)| := hh
        _ = _ := by rw [← sq_abs (z / Real.sqrt (n : ℝ))]; ring
    calc
      R0 = (n : ℝ) * ∫ z : ℝ, Shao.truncationF (z / Real.sqrt (n : ℝ)) ∂rho := by
        dsimp [R0, normalizedLaw, Shao.truncationBudget]
        simp only [add_zero, one_mul]
        rw [integral_map (μ := rho) (φ := fun z : ℝ => z / Real.sqrt (n : ℝ))
          (f := Shao.truncationF) (measurable_id.div_const _).aemeasurable
          Shao.continuous_truncationF.aestronglyMeasurable]
      _ ≤ (n : ℝ) * ∫ z : ℝ, |z / Real.sqrt (n : ℝ)| ^ 3 ∂rho :=
        mul_le_mul_of_nonneg_left (integral_mono hFi hCi hPoint) hnR.le
      _ = delta := by
        simp only [abs_div, abs_of_pos hnS, div_pow]
        rw [integral_div]
        change (n : ℝ) * (beta / Real.sqrt (n : ℝ) ^ 3) = beta / Real.sqrt (n : ℝ)
        have hs := Real.sq_sqrt hnR.le
        field_simp <;> nlinarith
  have hhH : h ≤ H := by
    have hh : R0 ^ 2 ≤ delta ^ 2 := sq_le_sq₀ hRpos.le hdelta.le |>.mpr hRle
    have hs : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
    have he : (n : ℝ) * delta ^ 2 = beta ^ 2 := by
      dsimp [delta]; rw [div_pow, hs]; field_simp
    dsimp [h, H]
    nlinarith [mul_le_mul_of_nonneg_left hh hnR.le]
  let firstCube : (t : ℕ) → Shao.Path t → ℝ := fun t v =>
    if ht : 0 < t then |v ⟨0, ht⟩| ^ 3 else 0
  let W : (t : ℕ) → Shao.Path t → ℝ := fun t v =>
    if 0 < Shao.energy v ∧ H ≤ Shao.energy v then
      firstCube t v / (Real.sqrt (Shao.energy v)) ^ 3 *
        (1 + |Shao.prefixSum v t| / Real.sqrt (Shao.energy v)) ^ 3
    else 0
  let E : (t : ℕ) → Shao.Path t → ℝ := fun t v =>
    if 0 < Shao.energy v ∧ h ≤ Shao.energy v then
      firstCube t v / (Shao.energy v * Real.sqrt (Shao.energy v)) *
        (1 + |Shao.prefixSum v t| ^ 3 / (Shao.energy v * Real.sqrt (Shao.energy v)))
    else 0
  let Rp : ℕ → ℝ := fun t => Shao.truncationBudget
    (Measure.map (fun z : ℝ => z / Real.sqrt ((n - t : ℕ) : ℝ)) rho) (n - t) 0
  have hUniform := hUniformRaw rho h2 h3 hmean hsecond
  have hzero (m : ℕ) (hm : 0 < m+1) : (⟨0, hm⟩ : Fin (m+1)) = 0 := by
    apply Fin.ext
    simp
  have hWdata (t : ℕ) (ht : 0 < t) : Measurable (W t) ∧ Integrable (W t) (Pm t) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
    simpa only [W, firstCube, dif_pos (Nat.succ_pos m), Nat.succ_eq_add_one, Pm, H, beta, hzero] using hUniform.1 m
  have hWnn (t : ℕ) (v : Shao.Path t) : 0 ≤ W t v := by
    dsimp [W, firstCube]; split_ifs <;> positivity
  have hEarly := hEarlyRaw rho n hn h2 hmean hsecondPos
  simp only [hsecond, mul_one] at hEarly
  change (∀ t ∈ Finset.Icc ((n + 1) / 2) n, Integrable (E t) (Pm t)) ∧
    (∑ t ∈ Finset.Icc ((n + 1) / 2) n, ∫ v, E t v ∂Pm t) ≤ CE * R0 at hEarly
  have hEW (t : ℕ) (ht : 0 < t) (v : Shao.Path t) : W t v ≤ 4 * E t v := by
    have hEnergy : 0 ≤ Shao.energy v := Shao.energy_nonneg v
    by_cases hv : 0 < Shao.energy v ∧ H ≤ Shao.energy v
    · have hcut : 0 < Shao.energy v ∧ h ≤ Shao.energy v := ⟨hv.1, hhH.trans hv.2⟩
      have hs : 0 < Real.sqrt (Shao.energy v) := Real.sqrt_pos.mpr hv.1
      have hden : Real.sqrt (Shao.energy v) ^ 3 = Shao.energy v * Real.sqrt (Shao.energy v) := by
        rw [pow_succ, Real.sq_sqrt hv.1.le]
      have hpoly : (1 + |Shao.prefixSum v t| / Real.sqrt (Shao.energy v)) ^ 3 ≤
          4 * (1 + |Shao.prefixSum v t| ^ 3 / (Shao.energy v * Real.sqrt (Shao.energy v))) := by
        have hq : 0 ≤ |Shao.prefixSum v t| / Real.sqrt (Shao.energy v) := by positivity
        have hh := mul_nonneg (sq_nonneg (|Shao.prefixSum v t| / Real.sqrt (Shao.energy v) - 1))
          (show 0 ≤ |Shao.prefixSum v t| / Real.sqrt (Shao.energy v) + 1 by positivity)
        rw [← hden, ← div_pow]
        nlinarith
      dsimp only [W, E]
      rw [if_pos hv, if_pos hcut, hden]
      have hM : 0 ≤ firstCube t v / (Shao.energy v * Real.sqrt (Shao.energy v)) := by
        dsimp [firstCube]; rw [dif_pos ht]; positivity
      nlinarith [mul_le_mul_of_nonneg_left hpoly hM]
    · have hEnn : 0 ≤ E t v := by dsimp [E, firstCube]; split_ifs <;> positivity
      simp only [W, if_neg hv]; positivity
  let split : (r : Fin n) → Shao.Path n → Shao.Path r.val × Shao.Path (n - r.val) := fun r a =>
    (Spitzer.head a r.val r.is_lt.le, Spitzer.tail a r.val r.is_lt.le)
  have hSplit (r : Fin n) : MeasurePreserving (split r) P ((Pm r.val).prod (Pm (n-r.val))) := by
    let e : Fin r.val ⊕ Fin (n-r.val) ≃ Fin n :=
      finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le r.is_lt.le))
    have h1 := (measurePreserving_piCongrLeft (fun _ : Fin n => rho) e).symm
    have h2 := measurePreserving_sumPiEquivProdPi (fun _ : Fin r.val ⊕ Fin (n-r.val) => rho)
    convert h2.comp h1 using 1
    ext a i <;> change a _ = a _ <;> congr 1
  have hTail (r : Fin n) : MeasurePreserving (fun a : Shao.Path n => (split r a).2) P (Pm (n-r.val)) := by
    letI := hPm r.val
    exact (measurePreserving_snd (μ := Pm r.val) (ν := Pm (n-r.val))).comp (hSplit r)
  have hTailId (r : Fin n) : IdentDistrib (fun a : Shao.Path n => (split r a).2)
      (id : Shao.Path (n-r.val) → Shao.Path (n-r.val)) P (Pm (n-r.val)) :=
    ⟨(hTail r).measurable.aemeasurable, measurable_id.aemeasurable, by rw [Measure.map_id]; exact (hTail r).map_eq⟩
  have hState (r : Fin n) (a : Shao.Path n) :
      Shao.energy (split r a).2 = T a r ∧
      Shao.prefixSum (split r a).2 (n-r.val) = d a r ∧
      Shao.energy (split r a).2 + Shao.energy (split r a).1 = Shao.energy a ∧
      SourceIIDGaussianProfileBudget.firstValue (split r a).2 = a r := by
    exact ⟨(SourceIIDGaussianProfileBudget.gaussian_weight_source_state a r H x ∅ false).1,
      (SourceIIDGaussianProfileBudget.gaussian_weight_source_state a r H x ∅ false).2.1,
      (SourceIIDGaussianProfileBudget.gaussian_weight_source_state a r H x ∅ false).2.2.1,
      (SourceIIDGaussianProfileBudget.gaussian_weight_source_state a r H x ∅ false).2.2.2.1⟩
  have hGform (a : Shao.Path n) (r : Fin n) :
      G a r = W (n-r.val) (split r a).2 * Real.exp (-x ^ 2 * Shao.energy a / T a r) := by
    have ht : 0 < n-r.val := Nat.sub_pos_of_lt r.is_lt
    have hs := hState r a
    dsimp only [G, W, firstCube]
    rw [dif_pos ht, hs.1, hs.2.1]
    have he : (split r a).2 ⟨0, ht⟩ = a r := by
      simpa only [SourceIIDGaussianProfileBudget.firstValue, dif_pos ht] using hs.2.2.2
    rw [he]
    split_ifs <;> simp
  have hTm (r : Fin n) : Measurable (fun a : Shao.Path n => T a r) :=
    Shao.measurable_energy.sub (Shao.measurable_prefixSquares r.val)
  have hdm (r : Fin n) : Measurable (fun a : Shao.Path n => d a r) :=
    (Shao.measurable_prefixSum n).sub (Shao.measurable_prefixSum r.val)
  have hGm (r : Fin n) : Measurable (fun a : Shao.Path n => G a r) := by
    dsimp only [G]
    apply Measurable.ite ((measurableSet_lt measurable_const (hTm r)).inter
      (measurableSet_le measurable_const (hTm r)))
    · exact ((((continuous_abs.measurable.comp (measurable_pi_apply (X := fun _ : Fin n => ℝ) r)).pow_const 3).div
        ((hTm r).sqrt.pow_const 3)).mul
        ((measurable_const.add ((continuous_abs.measurable.comp (hdm r)).div (hTm r).sqrt)).pow_const 3)).mul
        ((measurable_const.mul Shao.measurable_energy).div (hTm r)).exp
    · exact measurable_const
  have hGnn (a : Shao.Path n) (r : Fin n) : 0 ≤ G a r := by
    dsimp [G]; split_ifs <;> positivity
  have hGbase (a : Shao.Path n) (r : Fin n) :
      G a r ≤ W (n-r.val) (split r a).2 * Real.exp (-x ^ 2) := by
    rw [hGform]
    by_cases ht : 0 < T a r
    · have he : T a r ≤ Shao.energy a := by
        dsimp [T]
        exact sub_le_self _ (Finset.sum_nonneg (fun i _ => sq_nonneg (a i)))
      have hh : -x ^ 2 * Shao.energy a / T a r ≤ -x ^ 2 := by
        apply (div_le_iff₀ ht).mpr
        nlinarith [sq_nonneg x]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hh) (hWnn _ _)
    · have hw : W (n-r.val) (split r a).2 = 0 := by
        dsimp only [W]; rw [(hState r a).1]; exact if_neg (fun h => ht h.1)
      simp only [hw, zero_mul, le_refl]
  have hGi (r : Fin n) : Integrable (fun a : Shao.Path n => G a r) P := by
    have hi := (hTail r).integrable_comp_of_integrable (hWdata _ (Nat.sub_pos_of_lt r.is_lt)).2
    exact (hi.mul_const (Real.exp (-x ^ 2))).mono' (hGm r).aestronglyMeasurable
      (ae_of_all _ fun a => by simpa only [Function.comp_def, Real.norm_eq_abs, abs_of_nonneg (hGnn a r)] using hGbase a r)
  let suffix : (t : ℕ) → Shao.Path n → Shao.Path (n - (n - t)) := fun t a =>
    Spitzer.tail a (n-t) (Nat.sub_le n t)
  let TL : ℕ → Shao.Path n → ℝ := fun t a => Shao.energy (suffix t a)
  let dL : ℕ → Shao.Path n → ℝ := fun t a => Shao.prefixSum (suffix t a) (n-(n-t))
  let betaL : ℕ → Shao.Path n → ℝ := fun t a =>
    if 0 < TL t a then (∑ i : Fin (n-(n-t)), |suffix t a i| ^ 3) /
      (TL t a * Real.sqrt (TL t a)) else 0
  let DL : ℕ → Shao.Path n → ℝ := fun t a =>
    if 0 < TL t a then 1 + |dL t a| / Real.sqrt (TL t a) else 1
  let A : ℕ → Shao.Path n → ℝ := fun t a =>
    if 0 < TL t a ∧ h ≤ TL t a then
      (betaL t a / (t : ℝ)) * DL t a ^ 5 *
        (TL t a / ((n-t : ℕ) : ℝ) + Rp t ^ 2)
    else 0
  have hLate := hLateRaw rho n hn h2 hmean hsecondPos
  simp only [hsecond, mul_one] at hLate
  have hLate5 : (∀ t ∈ Finset.Icc 1 (n/2), Integrable (A t) P) ∧
      (∑ t ∈ Finset.Icc 1 (n/2), ∫ a, A t a ∂P) ≤ CT * R0 := hLate 5 (Or.inr rfl)
  have hAForm (r : Fin n) (a : Shao.Path n) :
      A (n-r.val) a = SourceMarkedSuffixAveraging.lateAveragedWeight h (r.val : ℝ)
        (Rp (n-r.val)) (split r a).2 := by
    let q : Fin n := ⟨n-(n-r.val), by omega⟩
    have hq : q = r := by apply Fin.ext; dsimp [q]; omega
    have he : Shao.energy (suffix (n-r.val) a) = Shao.energy (split r a).2 := by
      change Shao.energy (Spitzer.tail a q.val q.is_lt.le) =
        Shao.energy (Spitzer.tail a r.val r.is_lt.le)
      rw [hq]
    have hcubes : (∑ i : Fin (n-(n-(n-r.val))), |suffix (n-r.val) a i| ^ 3) =
        ∑ i : Fin (n-r.val), |(split r a).2 i| ^ 3 := by
      change (∑ i : Fin (n-q.val), |Spitzer.tail a q.val q.is_lt.le i| ^ 3) =
        ∑ i : Fin (n-r.val), |Spitzer.tail a r.val r.is_lt.le i| ^ 3
      rw [hq]
    have hd : Shao.prefixSum (suffix (n-r.val) a) (n-(n-(n-r.val))) =
        Shao.prefixSum (split r a).2 (n-r.val) := by
      change Shao.prefixSum (Spitzer.tail a q.val q.is_lt.le) (n-q.val) =
        Shao.prefixSum (Spitzer.tail a r.val r.is_lt.le) (n-r.val)
      rw [hq]
    simp only [A, TL, betaL, DL, dL]
    rw [he, hcubes, hd, Nat.sub_sub_self r.is_lt.le]
    by_cases hc : h ≤ Shao.energy (split r a).2
    · have ht : 0 < Shao.energy (split r a).2 := hhpos.trans_le hc
      simp only [ht, hc, true_and, ite_true, SourceMarkedSuffixAveraging.lateAveragedWeight,
        SourceMarkedSuffixAveraging.suffixBeta, SourceMarkedSuffixAveraging.cubicMass,
        SourceMarkedSuffixAveraging.suffixD]
    · simp only [hc, and_false, ite_false, SourceMarkedSuffixAveraging.lateAveragedWeight]
  have hLateMarked (r : Fin n) (hr : n/2 < r.val) :
      Integrable (fun a : Shao.Path n => SourceMarkedSuffixAveraging.lateMarkedWeight
        h (r.val : ℝ) (Rp (n-r.val)) (split r a).2 ⟨0, Nat.sub_pos_of_lt r.is_lt⟩) P ∧
      (∫ a, SourceMarkedSuffixAveraging.lateMarkedWeight h (r.val : ℝ) (Rp (n-r.val))
        (split r a).2 ⟨0, Nat.sub_pos_of_lt r.is_lt⟩ ∂P) = ∫ a, A (n-r.val) a ∂P := by
    have hrp : 0 < (r.val : ℝ) := Nat.cast_pos.mpr (by omega)
    have hMark := SourceMarkedSuffixAveraging.iid_product_late_marked_integral_eq_average
      (Nat.sub_pos_of_lt r.is_lt) rho h2 h (r.val : ℝ) (Rp (n-r.val)) hhpos hrp
      ⟨0, Nat.sub_pos_of_lt r.is_lt⟩
    have hMm := (SourceMarkedSuffixAveraging.late_weights_measurable_and_covariant
      (t := n-r.val) h (r.val : ℝ) (Rp (n-r.val))).1 ⟨0, Nat.sub_pos_of_lt r.is_lt⟩
    have hAm := (SourceMarkedSuffixAveraging.late_weights_measurable_and_covariant
      (t := n-r.val) h (r.val : ℝ) (Rp (n-r.val))).2.1
    have hMid := (hTailId r).comp hMm
    have hAid := (hTailId r).comp hAm
    refine ⟨hMid.integrable_iff.mpr hMark.1, ?_⟩
    calc
      _ = ∫ u : Shao.Path (n-r.val), SourceMarkedSuffixAveraging.lateMarkedWeight
          h (r.val : ℝ) (Rp (n-r.val)) u ⟨0, Nat.sub_pos_of_lt r.is_lt⟩ ∂Pm (n-r.val) := hMid.integral_eq
      _ = ∫ u : Shao.Path (n-r.val), SourceMarkedSuffixAveraging.lateAveragedWeight
          h (r.val : ℝ) (Rp (n-r.val)) u ∂Pm (n-r.val) := hMark.2.2
      _ = _ := hAid.integral_eq.symm.trans (integral_congr_ae (ae_of_all _ (fun a => (hAForm r a).symm)))
  have hLatePoint (r : Fin n) (hr : n/2 < r.val) (a : Shao.Path n) :
      (T a r / (n : ℝ)) * W (n-r.val) (split r a).2 ≤
        SourceMarkedSuffixAveraging.lateMarkedWeight h (r.val : ℝ) (Rp (n-r.val))
          (split r a).2 ⟨0, Nat.sub_pos_of_lt r.is_lt⟩ := by
    let u := (split r a).2
    have ht : 0 < n-r.val := Nat.sub_pos_of_lt r.is_lt
    have hg := SourceMarkedSuffixAveraging.suffix_normalized_geometry u
    have hMnn := (hg.2.2.2.1 ⟨0, ht⟩).1
    have hD : 1 ≤ SourceMarkedSuffixAveraging.suffixD u := hg.2.2.2.2.2.1.1
    have hDnn : 0 ≤ SourceMarkedSuffixAveraging.suffixD u := by linarith only [hD]
    have hEnergy : 0 ≤ Shao.energy u := Shao.energy_nonneg u
    have hTnn : 0 ≤ T a r := by rw [← (hState r a).1]; exact hEnergy
    have hnn : 0 ≤ SourceMarkedSuffixAveraging.lateMarkedWeight h (r.val : ℝ) (Rp (n-r.val)) u ⟨0, ht⟩ := by
      dsimp [SourceMarkedSuffixAveraging.lateMarkedWeight]
      split_ifs
      · exact mul_nonneg (mul_nonneg hMnn (by positivity)) (by positivity)
      · rfl
    by_cases hc : 0 < T a r ∧ H ≤ T a r
    · have hct : h ≤ Shao.energy u := by rw [(hState r a).1]; exact hhH.trans hc.2
      have hu : 0 < Shao.energy u := by rw [(hState r a).1]; exact hc.1
      have hden : Real.sqrt (Shao.energy u) ^ 3 = Shao.energy u * Real.sqrt (Shao.energy u) := by
        rw [pow_succ, Real.sq_sqrt hu.le]
      have hW : W (n-r.val) u = SourceMarkedSuffixAveraging.normalizedCubicMark u ⟨0, ht⟩ *
          SourceMarkedSuffixAveraging.suffixD u ^ 3 := by
        have hcu : 0 < Shao.energy u ∧ H ≤ Shao.energy u := ⟨hu, by rw [(hState r a).1]; exact hc.2⟩
        simp only [W, firstCube, dif_pos ht, if_pos hcu,
          SourceMarkedSuffixAveraging.normalizedCubicMark, SourceMarkedSuffixAveraging.suffixD, if_pos hu, hden]
      have hratio : T a r / (n : ℝ) ≤ Shao.energy u / (r.val : ℝ) + Rp (n-r.val) ^ 2 := by
        rw [← (hState r a).1]
        have hrl : (r.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast r.is_lt.le
        have hrp : 0 < (r.val : ℝ) := Nat.cast_pos.mpr (by omega)
        exact (div_le_div_of_nonneg_left (Shao.energy_nonneg u) hrp hrl).trans
          (le_add_of_nonneg_right (sq_nonneg _))
      rw [hW]
      change _ ≤ (if h ≤ Shao.energy u then _ else 0)
      rw [if_pos hct]
      have hpow := pow_le_pow_right₀ hD (show (3 : ℕ) ≤ 5 by omega)
      have hprod := mul_le_mul_of_nonneg_left hpow hMnn
      have hbnd := mul_le_mul hprod hratio (div_nonneg hTnn hnR.le)
        (mul_nonneg hMnn (pow_nonneg hDnn _))
      convert hbnd using 1 <;> ring
    · have hw : W (n-r.val) u = 0 := by
        dsimp only [W]; rw [(hState r a).1]; exact if_neg hc
      rw [hw, mul_zero]
      exact hnn
  let q : ℝ := 1 / (128 * beta ^ 2)
  have hq : 0 < q := by dsimp [q]; positivity
  have hSmall : ((0 : ℝ) + q) * beta ^ 2 ≤ 1 / 64 := by
    dsimp [q]; field_simp; nlinarith [sq_pos_of_pos hb]
  have hLow (r : ℕ) : Integrable (fun v : Shao.Path r => Real.exp (-q * Shao.energy v)) (Pm r) ∧
      (∫ v, Real.exp (-q * Shao.energy v) ∂Pm r) ≤ Real.exp (-(3 / 4) * q * (r : ℝ)) := by
    have hh := Shao.C2.AuxiliaryTiltedProductEnergy.auxiliary_tilted_product_low_energy rho h2 h3 hmean hsecond
      0 q (by norm_num) hq.le hq.le hSmall r
    simpa only [neg_zero, zero_mul, MeasureTheory.tilted_const] using And.intro hh.2.1 hh.2.2.1
  let I : (r : ℕ) → Shao.Path r → ℝ := fun r v => if Shao.energy v < (r : ℝ) / 2 then 1 else 0
  have hIm (r : ℕ) : Measurable (I r) :=
    Measurable.ite (measurableSet_lt Shao.measurable_energy measurable_const) measurable_const measurable_const
  have hIi (r : ℕ) : Integrable (I r) (Pm r) := by
    letI := hPm r
    exact (integrable_const (1 : ℝ)).mono' (hIm r).aestronglyMeasurable (ae_of_all _ fun v => by
      dsimp [I]; split_ifs <;> norm_num)
  have hInn (r : ℕ) (v : Shao.Path r) : 0 ≤ I r v := by dsimp [I]; split_ifs <;> norm_num
  have hIBound (r : ℕ) : (∫ v, I r v ∂Pm r) ≤ Real.exp (-q * (r : ℝ) / 4) := by
    have hp (v : Shao.Path r) : I r v ≤ Real.exp (q * (r : ℝ) / 2) * Real.exp (-q * Shao.energy v) := by
      dsimp only [I]
      split_ifs with hv
      · rw [← Real.exp_add]
        exact Real.one_le_exp_iff.mpr (by nlinarith)
      · positivity
    calc
      _ ≤ ∫ v : Shao.Path r, Real.exp (q * (r : ℝ) / 2) * Real.exp (-q * Shao.energy v) ∂Pm r :=
        integral_mono (hIi r) ((hLow r).1.const_mul _) hp
      _ = Real.exp (q * (r : ℝ) / 2) * ∫ v : Shao.Path r, Real.exp (-q * Shao.energy v) ∂Pm r := integral_const_mul _ _
      _ ≤ Real.exp (q * (r : ℝ) / 2) * Real.exp (-(3 / 4) * q * (r : ℝ)) :=
        mul_le_mul_of_nonneg_left (hLow r).2 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1 <;> ring
  have hSmallExp : Real.exp (-1 / (1024 * delta ^ 2)) ≤ 32 * delta := by
    have hE := Real.add_one_le_exp ((1 / (32 * delta)) ^ 2)
    have hS := sq_nonneg (1 / (32 * delta) - 1 / 2)
    have hW : 1 / (32 * delta) ≤ Real.exp ((1 / (32 * delta)) ^ 2) := by nlinarith
    have he : Real.exp (-1 / (1024 * delta ^ 2)) * Real.exp ((1 / (32 * delta)) ^ 2) = 1 := by
      rw [← Real.exp_add]
      have hz : -1 / (1024 * delta ^ 2) + (1 / (32 * delta)) ^ 2 = 0 := by ring
      rw [hz, Real.exp_zero]
    have hm := mul_le_mul_of_nonneg_left hW (Real.exp_pos (-1 / (1024 * delta ^ 2))).le
    rw [he] at hm
    apply (div_le_one (by positivity : 0 < 32 * delta)).mp
    simpa only [div_eq_mul_inv, one_mul] using hm
  have hBadExp (r : Fin n) (hr : n/2 < r.val) : Real.exp (-q * (r.val : ℝ) / 4) ≤
      Real.exp (-1 / (1024 * delta ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have hrn : (n : ℝ) ≤ 2 * (r.val : ℝ) := by exact_mod_cast (show n ≤ 2 * r.val by omega)
    have hs : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
    dsimp [q, delta]
    rw [div_pow, hs]
    field_simp <;> nlinarith
  have hBadIntegral (r : Fin n) (hr : n/2 < r.val) :
      (∫ a : Shao.Path n, I r.val (split r a).1 * W (n-r.val) (split r a).2 ∂P) ≤
        Real.exp (-1 / (1024 * delta ^ 2)) * ∫ u, W (n-r.val) u ∂Pm (n-r.val) := by
    have hm : Measurable (fun p : Shao.Path r.val × Shao.Path (n-r.val) => I r.val p.1 * W (n-r.val) p.2) :=
      ((hIm _).comp measurable_fst).mul ((hWdata _ (Nat.sub_pos_of_lt r.is_lt)).1.comp measurable_snd)
    have he := integral_map (μ := P) (φ := split r)
      (f := fun p : Shao.Path r.val × Shao.Path (n-r.val) => I r.val p.1 * W (n-r.val) p.2)
      (hSplit r).measurable.aemeasurable hm.aestronglyMeasurable
    rw [(hSplit r).map_eq, integral_prod_mul] at he
    rw [← he]
    exact mul_le_mul_of_nonneg_right ((hIBound _).trans (hBadExp r hr))
      (integral_nonneg (hWnn _))
  have hEm (t : ℕ) : Measurable (E t) := by
    have hCm : Measurable (firstCube t) := by
      dsimp only [firstCube]; split_ifs
      · exact (continuous_abs.measurable.comp (measurable_pi_apply (X := fun _ : Fin t => ℝ) _)).pow_const 3
      · exact measurable_const
    dsimp only [E]
    apply Measurable.ite ((measurableSet_lt measurable_const Shao.measurable_energy).inter
      (measurableSet_le measurable_const Shao.measurable_energy))
    · exact (hCm.div (Shao.measurable_energy.mul Shao.measurable_energy.sqrt)).mul
        (measurable_const.add (((continuous_abs.measurable.comp (Shao.measurable_prefixSum t)).pow_const 3).div
          (Shao.measurable_energy.mul Shao.measurable_energy.sqrt)))
    · exact measurable_const
  have hEarlyRank (r : Fin n) (hr : r.val ≤ n/2) :
      (∫ a, G a r ∂P) ≤ 4 * Real.exp (-x ^ 2) * ∫ u, E (n-r.val) u ∂Pm (n-r.val) := by
    have ht : n-r.val ∈ Finset.Icc ((n+1)/2) n := by simp only [Finset.mem_Icc]; omega
    have hiE := (hTail r).integrable_comp_of_integrable (hEarly.1 _ ht)
    have hId := (hTailId r).comp (hEm (n-r.val))
    calc
      _ ≤ ∫ a, 4 * Real.exp (-x ^ 2) * E (n-r.val) (split r a).2 ∂P :=
        integral_mono (hGi r) (hiE.const_mul _) (fun a => (hGbase a r).trans (by
          calc
            _ ≤ (4 * E (n-r.val) (split r a).2) * Real.exp (-x^2) :=
              mul_le_mul_of_nonneg_right (hEW _ (Nat.sub_pos_of_lt r.is_lt) (split r a).2) (Real.exp_pos _).le
            _ = _ := by ring))
      _ = _ := by
        rw [integral_const_mul]
        congr 1
        exact hId.integral_eq
  have hLateRank (r : Fin n) (hr : n/2 < r.val) :
      (∫ a, G a r ∂P) ≤ 4 * Real.exp (-x ^ 2) * (∫ a, A (n-r.val) a ∂P) +
        Real.exp (-x ^ 2) * Real.exp (-1 / (1024 * delta ^ 2)) *
          (∫ u, W (n-r.val) u ∂Pm (n-r.val)) := by
    let Mark : Shao.Path n → ℝ := fun a => SourceMarkedSuffixAveraging.lateMarkedWeight
      h (r.val : ℝ) (Rp (n-r.val)) (split r a).2 ⟨0, Nat.sub_pos_of_lt r.is_lt⟩
    have hMi : Integrable Mark P := (hLateMarked r hr).1
    have hMnn (a : Shao.Path n) : 0 ≤ Mark a := by
      have hh := hLatePoint r hr a
      have ht : 0 ≤ T a r := by rw [← (hState r a).1]; exact Shao.energy_nonneg _
      exact (mul_nonneg (div_nonneg ht hnR.le) (hWnn _ _)).trans hh
    have hBMi : Integrable (fun a : Shao.Path n => I r.val (split r a).1 * W (n-r.val) (split r a).2) P :=
      (hSplit r).integrable_comp_of_integrable ((hIi r.val).mul_prod
        (hWdata _ (Nat.sub_pos_of_lt r.is_lt)).2)
    have hPoint (a : Shao.Path n) : G a r ≤
        4 * Real.exp (-x ^ 2) * Mark a +
        Real.exp (-x ^ 2) * (I r.val (split r a).1 * W (n-r.val) (split r a).2) := by
      by_cases hbad : Shao.energy (split r a).1 < (r.val : ℝ) / 2
      · have he : I r.val (split r a).1 = 1 := by simp only [I, if_pos hbad]
        rw [he, one_mul]
        exact (hGbase a r).trans (by nlinarith [mul_nonneg (Real.exp_pos (-x^2)).le (hMnn a)])
      · have hGood : (r.val : ℝ) / 2 ≤ Shao.energy (split r a).1 := le_of_not_gt hbad
        have heI : I r.val (split r a).1 = 0 := by simp only [I, if_neg hbad]
        rw [heI, zero_mul, mul_zero, add_zero]
        by_cases ht : 0 < T a r
        · have hnPrefix : (n : ℝ) / 4 ≤ Shao.energy (split r a).1 := by
            have hrn : (n : ℝ) ≤ 2 * (r.val : ℝ) := by exact_mod_cast (show n ≤ 2*r.val by omega)
            linarith
          have hTotal : T a r + (n : ℝ) / 4 ≤ Shao.energy a := by
            have hh := (hState r a).2.2.1
            rw [(hState r a).1] at hh
            linarith
          let w : ℝ := (n : ℝ) / (4 * T a r)
          have hw : 0 < w := by dsimp [w]; positivity
          have hExpW : Real.exp (-w) ≤ 4 * T a r / (n : ℝ) := by
            have he := Real.add_one_le_exp w
            have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (-w)).le
            have hInv : Real.exp (-w) * Real.exp w = 1 := by rw [← Real.exp_add]; simp
            rw [hInv] at hm
            have hh : Real.exp (-w) * w ≤ 1 := by nlinarith [Real.exp_pos (-w)]
            apply (le_div_iff₀ hnR).mpr
            dsimp [w] at hh
            have hh' : Real.exp (-w) * (n : ℝ) / (4 * T a r) ≤ 1 := by convert hh using 1 <;> ring
            have hh'' := (div_le_one (by positivity : 0 < 4 * T a r)).mp hh'
            exact hh''
          have hExponent : -x ^ 2 * Shao.energy a / T a r ≤ -x ^ 2 - w := by
            apply (div_le_iff₀ ht).mpr
            have hx1 : 1 ≤ x ^ 2 := by nlinarith
            have hTotalMul := mul_le_mul_of_nonneg_left hTotal (sq_nonneg x)
            have hnn := mul_nonneg (show 0 ≤ x^2 - 1 by linarith) (show 0 ≤ (n:ℝ)/4 by positivity)
            dsimp [w]
            field_simp
            nlinarith
          have hExp : Real.exp (-x ^ 2 * Shao.energy a / T a r) ≤
              Real.exp (-x ^ 2) * (4 * T a r / (n : ℝ)) := by
            calc
              _ ≤ Real.exp (-x ^ 2 - w) := Real.exp_le_exp.mpr hExponent
              _ = Real.exp (-x ^ 2) * Real.exp (-w) := by rw [← Real.exp_add]; congr 1 <;> ring
              _ ≤ _ := mul_le_mul_of_nonneg_left hExpW (Real.exp_pos _).le
          rw [hGform]
          have hh := mul_le_mul_of_nonneg_left hExp (hWnn _ (split r a).2)
          have hm := mul_le_mul_of_nonneg_left (hLatePoint r hr a)
            (show 0 ≤ 4 * Real.exp (-x ^ 2) by positivity)
          exact hh.trans (by convert hm using 1 <;> ring)
        · have hh : G a r = 0 := by dsimp [G]; exact if_neg (fun hh => ht hh.1)
          rw [hh]
          exact mul_nonneg (by positivity) (hMnn a)
    calc
      _ ≤ ∫ a, 4 * Real.exp (-x ^ 2) * Mark a +
          Real.exp (-x ^ 2) * (I r.val (split r a).1 * W (n-r.val) (split r a).2) ∂P :=
        integral_mono (hGi r) ((hMi.const_mul _).add (hBMi.const_mul _)) hPoint
      _ = 4 * Real.exp (-x ^ 2) * (∫ a, Mark a ∂P) +
          Real.exp (-x ^ 2) * (∫ a, I r.val (split r a).1 * W (n-r.val) (split r a).2 ∂P) := by
        rw [integral_add (hMi.const_mul _) (hBMi.const_mul _), integral_const_mul, integral_const_mul]
      _ ≤ _ := by
        rw [(hLateMarked r hr).2]
        have hh := mul_le_mul_of_nonneg_left (hBadIntegral r hr) (Real.exp_pos (-x^2)).le
        nlinarith
  let er : Finset (Fin n) := Finset.univ.filter (fun r => r.val ≤ n/2)
  let lr : Finset (Fin n) := Finset.univ.filter (fun r => ¬ r.val ≤ n/2)
  have hReindexE (f : ℕ → ℝ) : (∑ r ∈ er, f (n-r.val)) = ∑ t ∈ Finset.Icc ((n+1)/2) n, f t := by
    apply Finset.sum_bij (fun r _ => n-r.val)
    · intro r hr
      have hh := (Finset.mem_filter.mp hr).2
      simp only [Finset.mem_Icc]; omega
    · intro r hr s hs he
      apply Fin.ext
      omega
    · intro t ht
      have hh := Finset.mem_Icc.mp ht
      refine ⟨⟨n-t, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change n-t ≤ n/2; omega⟩, ?_⟩
      dsimp; omega
    · intro r hr; rfl
  have hReindexL (f : ℕ → ℝ) : (∑ r ∈ lr, f (n-r.val)) = ∑ t ∈ Finset.Icc 1 ((n-1)/2), f t := by
    apply Finset.sum_bij (fun r _ => n-r.val)
    · intro r hr
      have hh := (Finset.mem_filter.mp hr).2
      simp only [Finset.mem_Icc]; omega
    · intro r hr s hs he
      apply Fin.ext
      omega
    · intro t ht
      have hh := Finset.mem_Icc.mp ht
      refine ⟨⟨n-t, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change ¬ n-t ≤ n/2; omega⟩, ?_⟩
      dsimp; omega
    · intro r hr; rfl
  have hSumE : (∑ r ∈ er, ∫ u, E (n-r.val) u ∂Pm (n-r.val)) ≤ CE * delta := by
    rw [hReindexE (fun t : ℕ => ∫ u, E t u ∂Pm t)]
    exact hEarly.2.trans (mul_le_mul_of_nonneg_left hRle hCE.le)
  have hAnn (t : ℕ) (a : Shao.Path n) : 0 ≤ A t a := by
    have ht : 0 ≤ TL t a := Shao.energy_nonneg _
    dsimp [A, betaL, DL]
    split_ifs <;> positivity
  have hSumA : (∑ r ∈ lr, ∫ a, A (n-r.val) a ∂P) ≤ CT * delta := by
    rw [hReindexL (fun t : ℕ => ∫ a, A t a ∂P)]
    have hsub : Finset.Icc 1 ((n-1)/2) ⊆ Finset.Icc 1 (n/2) := by
      intro t ht
      simp only [Finset.mem_Icc] at ht ⊢
      omega
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun t _ _ => integral_nonneg (hAnn t))).trans
      (hLate5.2.trans (mul_le_mul_of_nonneg_left hRle hCT.le))
  have hSumWAll : (∑ r : Fin n, ∫ u, W (n-r.val) u ∂Pm (n-r.val)) ≤ KU := by
    have he : (∑ r : Fin n, ∫ u, W (n-r.val) u ∂Pm (n-r.val)) =
        ∑ m ∈ Finset.range n, ∫ u, W (m+1) u ∂Pm (m+1) := by
      apply Finset.sum_bij (fun r _ => n-1-r.val)
      · intro r hr; simp only [Finset.mem_range]; omega
      · intro r hr s hs he; apply Fin.ext; omega
      · intro m hm
        have hh := Finset.mem_range.mp hm
        refine ⟨⟨n-1-m, by omega⟩, Finset.mem_univ _, ?_⟩
        dsimp; omega
      · intro r hr
        have hh : n-r.val = n-1-r.val+1 := by omega
        rw [hh]
    rw [he]
    simpa only [W, firstCube, dif_pos (Nat.zero_lt_succ _), Nat.succ_eq_add_one, Pm, H, beta, hzero] using hUniform.2 n
  have hSumW : (∑ r ∈ lr, ∫ u, W (n-r.val) u ∂Pm (n-r.val)) ≤ KU :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun r _ _ => integral_nonneg (hWnn _))).trans hSumWAll
  have hSumi : Integrable (fun a => ∑ r : Fin n, G a r) P :=
    integrable_finsetSum _ (fun r _ => hGi r)
  refine ⟨Finset.measurable_sum _ (fun r _ => hGm r), hSumi, ?_⟩
  rw [integral_finsetSum _ (fun r _ => hGi r)]
  calc
    (∑ r : Fin n, ∫ a, G a r ∂P) ≤ ∑ r : Fin n,
        if r.val ≤ n/2 then 4 * Real.exp (-x^2) * ∫ u, E (n-r.val) u ∂Pm (n-r.val)
        else 4 * Real.exp (-x^2) * (∫ a, A (n-r.val) a ∂P) +
          Real.exp (-x^2) * Real.exp (-1/(1024*delta^2)) * (∫ u, W (n-r.val) u ∂Pm (n-r.val)) := by
      apply Finset.sum_le_sum
      intro r _
      split_ifs with hr
      · exact hEarlyRank r hr
      · exact hLateRank r (by omega)
    _ = 4 * Real.exp (-x^2) * (∑ r ∈ er, ∫ u, E (n-r.val) u ∂Pm (n-r.val)) +
        4 * Real.exp (-x^2) * (∑ r ∈ lr, ∫ a, A (n-r.val) a ∂P) +
        Real.exp (-x^2) * Real.exp (-1/(1024*delta^2)) * (∑ r ∈ lr, ∫ u, W (n-r.val) u ∂Pm (n-r.val)) := by
      rw [Finset.sum_ite]
      dsimp only [er, lr]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    _ ≤ 4 * Real.exp (-x^2) * (CE * delta) +
        4 * Real.exp (-x^2) * (CT * delta) +
        Real.exp (-x^2) * Real.exp (-1/(1024*delta^2)) * KU := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hSumE (by positivity))
        (mul_le_mul_of_nonneg_left hSumA (by positivity)))
        (mul_le_mul_of_nonneg_left hSumW (by positivity))
    _ ≤ (4*CE+4*CT+32*KU) * delta * Real.exp (-x^2) := by
      have hh := mul_le_mul_of_nonneg_left hSmallExp
        (show 0 ≤ Real.exp (-x^2) * KU by positivity)
      nlinarith

theorem iid_actual_regular_retained_probability_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ΩB : Type*} [MeasurableSpace ΩB]
        (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : ℝ≥0 → ΩB → ℝ), IsBrownianReal B PB →
        let Q : Measure BridgeNoise := bridgeLaw B PB
        ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho],
          Integrable (fun z : ℝ => z ^ 2) rho →
          Integrable (fun z : ℝ => |z| ^ 3) rho →
          (∫ z : ℝ, z ∂rho) = 0 →
          (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
          ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), 16 ≤ x →
            let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
            let delta : ℝ := beta / Real.sqrt (n : ℝ)
            let h0 : ℝ := 4 * beta ^ 2
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
            let nu : Shao.Path n → LabelPerm n → ℕ :=
              fun a sigma => energyCutoff a h0 sigma
            let F : MonitoredDomain → BridgeKernel := fun J => eventCompletionKernel J Q
            let FY : MonitoredDomain → BridgeKernel := fun J =>
              match J with
              | .upper => halflineDerivative .upper
              | .lower => halflineDerivative .lower
              | .interval => intervalDerivative Q
            let L : (Shao.Path n × LabelPerm n) → Fin n → ℝ := fun p r =>
              sourceRetainedRemainder .interval (F .interval) (FY .interval)
                  p.1 x (nu p.1) r.val p.2 -
                sourceRetainedRemainder .upper (F .upper) (FY .upper)
                  p.1 x (nu p.1) r.val p.2 -
                sourceRetainedRemainder .lower (F .lower) (FY .lower)
                  p.1 x (nu p.1) r.val p.2
            let bill : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
              ∑ r : Fin n,
                if r.val < nu p.1 p.2 ∧
                    (∀ k : ℕ, k ≤ r.val →
                      |Shao.prefixSum (Spitzer.reorder p.1 p.2) k| < actualWall p.1 x) ∧
                    |remainingSum p.1 r.val p.2| ≤
                      (3 / 2 : ℝ) * x * Real.sqrt (remainingEnergy p.1 r.val p.2)
                then |L p r| else 0
            Measurable bill ∧ Integrable bill (revealLaw P) ∧
              (∫ p, bill p ∂revealLaw P) ≤
                C * delta * Real.exp (-x ^ 2) ∧
              (∫ p, bill p ∂revealLaw P) ≤ C * delta * Shao.standardNormalTail x := by
  classical
  obtain ⟨KG, hKG, hGrid⟩ := rrp_damped_energy_grid
  obtain ⟨CL, hCL, hLocal⟩ :=
    SourceActualRegularLocal.actual_regular_retained_local_cubic_bound
  let C : ℝ := CL * KG * (1 + 2 * Real.sqrt (2 * Real.pi))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ΩB mΩB PB hPB B hB Q rho hRho h2 h3 hmean hsecond n hn x hx
    beta delta h0 P nu F FY L bill
  have hxpos : 0 < x := by linarith
  have hBeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one rho h2 h3 hsecond
  have hBetaPos : 0 < beta := by linarith
  have hh0 : 0 < h0 := by dsimp [h0]; positivity
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hdelta : 0 < delta := div_pos hBetaPos (Real.sqrt_pos.mpr hnR)
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw B PB hB
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  letI : IsProbabilityMeasure (revealLaw P) := by unfold revealLaw; infer_instance
  have hReflection : HalflineReflectionIdentities Q := by
    constructor
    · intro w y T z _ hT hy hz
      exact Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula B PB hB w y T z hT hy hz
    · intro w y T z _ hT hy hz
      exact Shao.C2.BridgeLowerIdentification.bridge_lower_formula B PB hB w y T z hT hy hz
  have hRegular (w y T z : ℝ) (hw : 0 < w) (hT : 0 < T)
      (hy : |y| < w) (hz : |z| < w) :
      DifferentiableAt ℝ
        (fun s : ℝ => Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w s T z) y :=
    (Shao.C2.BridgeIntervalImageResolved.sourceIntervalCompletion_spatial_hasDerivAt
      B PB hB w y T z hw hy hz hT).differentiableAt
  have hFm (J : MonitoredDomain) : Measurable (F J) :=
    (eventCompletionKernel_data J Q).1
  have hData (J : MonitoredDomain) :
      Measurable (FY J) ∧ KernelBounds J (F J) (FY J) 4 := by
    cases J with
    | upper => exact ⟨(actual_halfline_kernel_data Q hReflection .upper (Or.inl rfl)).1,
        (actual_halfline_kernel_data Q hReflection .upper (Or.inl rfl)).2.1⟩
    | lower => exact ⟨(actual_halfline_kernel_data Q hReflection .lower (Or.inr rfl)).1,
        (actual_halfline_kernel_data Q hReflection .lower (Or.inr rfl)).2.1⟩
    | interval => exact ⟨(actual_interval_kernel_data Q hReflection hRegular).1,
        (actual_interval_kernel_data Q hReflection hRegular).2.1⟩
  have hnu (sigma : LabelPerm n) : Measurable (fun a : Shao.Path n => nu a sigma) :=
    actual_energy_cutoff_measurable h0 hh0 sigma
  have hParts (J : MonitoredDomain) := source_parts_measurable_integrable J (F J) (FY J)
    (hFm J) (hData J).1 4 (hData J).2 P x hxpos nu hnu
  have hLm (r : Fin n) : Measurable (fun p => L p r) := by
    apply measurable_from_prod_countable_left
    intro sigma
    exact (((hParts .interval).1 sigma r.val).1.sub
      ((hParts .upper).1 sigma r.val).1).sub ((hParts .lower).1 sigma r.val).1
  have hLi (r : Fin n) : Integrable (fun p => L p r) (revealLaw P) :=
    (((hParts .interval).2.1 r.val).1.sub ((hParts .upper).2.1 r.val).1).sub
      ((hParts .lower).2.1 r.val).1
  have hGuard (r : Fin n) : MeasurableSet {p : Shao.Path n × LabelPerm n |
      r.val < nu p.1 p.2 ∧
      (∀ k : ℕ, k ≤ r.val →
        |Shao.prefixSum (Spitzer.reorder p.1 p.2) k| < actualWall p.1 x) ∧
      |remainingSum p.1 r.val p.2| ≤
        (3 / 2 : ℝ) * x * Real.sqrt (remainingEnergy p.1 r.val p.2)} := by
    have hSection (sigma : LabelPerm n) : MeasurableSet {a : Shao.Path n |
        r.val < nu a sigma ∧
        (∀ k : ℕ, k ≤ r.val →
          |Shao.prefixSum (Spitzer.reorder a sigma) k| < actualWall a x) ∧
        |remainingSum a r.val sigma| ≤
          (3 / 2 : ℝ) * x * Real.sqrt (remainingEnergy a r.val sigma)} := by
      have hRm : Measurable (fun a : Shao.Path n => Spitzer.reorder a sigma) :=
        Measurable.of_eval (fun i => measurable_pi_apply (sigma i))
      have hW : Measurable (fun a : Shao.Path n => actualWall a x) :=
        measurable_const.mul Shao.measurable_energy.sqrt
      have hS (s : Finset ℕ) : MeasurableSet {a : Shao.Path n |
          ∀ k ∈ s, |Shao.prefixSum (Spitzer.reorder a sigma) k| < actualWall a x} := by
        induction s using Finset.induction_on with
        | empty => simp
        | @insert k s hk ih =>
          simpa only [Finset.forall_mem_insert, Set.setOf_and, Function.comp_def] using
            (measurableSet_lt (continuous_abs.measurable.comp ((Shao.measurable_prefixSum k).comp hRm)) hW).inter ih
      have hPref : MeasurableSet {a : Shao.Path n | ∀ k : ℕ, k ≤ r.val →
          |Shao.prefixSum (Spitzer.reorder a sigma) k| < actualWall a x} := by
        simpa only [Finset.mem_range, Nat.lt_succ_iff] using hS (Finset.range (r.val + 1))
      have hD : Measurable (fun a : Shao.Path n => remainingSum a r.val sigma) :=
        (Shao.measurable_prefixSum n).sub ((Shao.measurable_prefixSum r.val).comp hRm)
      have hT : Measurable (fun a : Shao.Path n => remainingEnergy a r.val sigma) :=
        Shao.measurable_energy.sub ((Shao.measurable_prefixSquares r.val).comp hRm)
      exact (measurableSet_lt measurable_const (hnu sigma)).inter
        (hPref.inter (measurableSet_le (continuous_abs.measurable.comp hD) ((measurable_const.mul hT.sqrt))))
    have hm : Measurable (fun p : Shao.Path n × LabelPerm n =>
        if r.val < nu p.1 p.2 ∧
          (∀ k : ℕ, k ≤ r.val →
            |Shao.prefixSum (Spitzer.reorder p.1 p.2) k| < actualWall p.1 x) ∧
          |remainingSum p.1 r.val p.2| ≤
            (3 / 2 : ℝ) * x * Real.sqrt (remainingEnergy p.1 r.val p.2)
        then (1 : ℝ) else 0) := by
      apply measurable_from_prod_countable_left
      intro sigma
      exact Measurable.ite (hSection sigma) measurable_const measurable_const
    simpa only [Set.preimage, Set.mem_singleton_iff, ite_eq_left_iff, zero_ne_one,
      imp_false, not_not] using hm (measurableSet_singleton (1 : ℝ))
  have hBillm : Measurable bill := by
    apply Finset.measurable_sum
    intro r _
    exact Measurable.ite (hGuard r) (continuous_abs.measurable.comp (hLm r)) measurable_const
  have hBilli : Integrable bill (revealLaw P) := by
    apply integrable_finsetSum
    intro r _
    have hi := (hLi r).abs
    exact hi.mono' ((Measurable.ite (hGuard r) (continuous_abs.measurable.comp (hLm r)) measurable_const).aestronglyMeasurable)
      (ae_of_all _ fun p => by split_ifs <;> simp [Real.norm_eq_abs])
  let TT : Shao.Path n → Fin n → ℝ := fun a r => Shao.energy a - Shao.prefixSquares a r.val
  let dd : Shao.Path n → Fin n → ℝ := fun a r => Shao.prefixSum a n - Shao.prefixSum a r.val
  let G0 : Shao.Path n → Fin n → ℝ := fun a r =>
    if 0 < TT a r ∧ h0 ≤ TT a r then
      |a r| ^ 3 / (Real.sqrt (TT a r)) ^ 3 *
        (1 + |dd a r| / Real.sqrt (TT a r)) ^ 3 *
        Real.exp (-x ^ 2 * Shao.energy a / TT a r)
    else 0
  let S : Shao.Path n → ℝ := fun a => ∑ r : Fin n, G0 a r
  have hGridData : Measurable S ∧ Integrable S P ∧
      (∫ a, S a ∂P) ≤ KG * delta * Real.exp (-x ^ 2) :=
    hGrid rho h2 h3 hmean hsecond n hn x hx
  have hGnn (a : Shao.Path n) (r : Fin n) : 0 ≤ G0 a r := by dsimp [G0]; split_ifs <;> positivity
  have hRm : Measurable (fun p : Shao.Path n × LabelPerm n => Spitzer.reorder p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro sigma
    exact Measurable.of_eval (fun i => measurable_pi_apply (sigma i))
  let X : Fin n → Shao.Path n → ℝ := fun i a => a i
  have hX (i : Fin n) : Measurable (X i) := measurable_pi_apply i
  have hLaw (i : Fin n) : IdentDistrib (X i) (id : ℝ → ℝ) P rho := by
    refine ⟨(hX i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [Measure.map_id] using
      (measurePreserving_eval (μ := fun _ : Fin n => rho) i).map_eq
  have hIndep : iIndepFun X P :=
    iIndepFun_pi (X := fun _ : Fin n => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)
  have hMap : Measure.map (fun p : Shao.Path n × LabelPerm n => Spitzer.reorder p.1 p.2)
      (revealLaw P) = P := iid_randomPermutation_map_eq_pi P rho X hX hIndep hLaw
  have hPath : IdentDistrib (fun p : Shao.Path n × LabelPerm n => Spitzer.reorder p.1 p.2)
      (id : Shao.Path n → Shao.Path n) (revealLaw P) P :=
    ⟨hRm.aemeasurable, measurable_id.aemeasurable, by simpa only [Measure.map_id] using hMap⟩
  have hSid := hPath.comp hGridData.1
  have hSi : Integrable (fun p : Shao.Path n × LabelPerm n => S (Spitzer.reorder p.1 p.2))
      (revealLaw P) := hSid.integrable_iff.mpr hGridData.2.1
  have hPoint (p : Shao.Path n × LabelPerm n) : bill p ≤ CL * S (Spitzer.reorder p.1 p.2) := by
    dsimp only [bill, S]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    by_cases hg : r.val < nu p.1 p.2 ∧
        (∀ k : ℕ, k ≤ r.val →
          |Shao.prefixSum (Spitzer.reorder p.1 p.2) k| < actualWall p.1 x) ∧
        |remainingSum p.1 r.val p.2| ≤
          (3 / 2 : ℝ) * x * Real.sqrt (remainingEnergy p.1 r.val p.2)
    · rw [if_pos hg]
      have hCut : h0 ≤ remainingEnergy p.1 r.val p.2 :=
        ((energy_cutoff_data p.1 h0 hh0).2.2 p.2 r.val hg.1).2
      have hT : 0 < remainingEnergy p.1 r.val p.2 := hh0.trans_le hCut
      have hRet (J : MonitoredDomain) :
          sourceRetainedRemainder J (F J) (FY J) p.1 x (nu p.1) r.val p.2 =
          sourceRetainedRemainder J (F J) (FY J) p.1 x (fun _ => n) r.val p.2 := by
        simp only [sourceRetainedRemainder, dif_pos r.is_lt, hg.1, r.is_lt, true_and]
      have hPhysical := hLocal PB B hB p.1 x p.2 r hx hg.2.1 hT hg.2.2
      have hEnergy : Shao.energy (Spitzer.reorder p.1 p.2) = Shao.energy p.1 := by
        simpa only [Shao.energy, Spitzer.reorder] using
          Equiv.sum_comp p.2 (fun i => (p.1 i) ^ 2)
      have hSum : Shao.prefixSum (Spitzer.reorder p.1 p.2) n = Shao.prefixSum p.1 n := by
        simpa only [Shao.prefixSum_length, Spitzer.reorder] using Equiv.sum_comp p.2 p.1
      have hWallSq : (actualWall p.1 x) ^ 2 = x ^ 2 * Shao.energy p.1 := by
        rw [actualWall, mul_pow, Real.sq_sqrt (Shao.energy_nonneg p.1)]
      dsimp only at hPhysical
      change |sourceRetainedRemainder .interval (F .interval) (FY .interval) p.1 x
          (fun _ => n) r.val p.2 -
        sourceRetainedRemainder .upper (F .upper) (FY .upper) p.1 x (fun _ => n) r.val p.2 -
        sourceRetainedRemainder .lower (F .lower) (FY .lower) p.1 x (fun _ => n) r.val p.2| ≤ _ at hPhysical
      dsimp only [L]
      rw [hRet .interval, hRet .upper, hRet .lower]
      convert hPhysical using 1
      have hTT : TT (Spitzer.reorder p.1 p.2) r = remainingEnergy p.1 r.val p.2 := by
        dsimp only [TT, remainingEnergy]
        rw [hEnergy]
      have hAct : 0 < TT (Spitzer.reorder p.1 p.2) r ∧ h0 ≤ TT (Spitzer.reorder p.1 p.2) r := by
        rw [hTT]
        exact ⟨hT, hCut⟩
      dsimp only [G0]
      rw [if_pos hAct, hTT]
      dsimp only [dd]
      rw [hEnergy, hSum, hWallSq, div_pow]
      simp only [Spitzer.reorder, neg_mul]
      ring
    · rw [if_neg hg]
      exact mul_nonneg hCL.le (hGnn _ _)
  have hStrong : (∫ p, bill p ∂revealLaw P) ≤ CL * KG * delta * Real.exp (-x ^ 2) := by
    calc
      (∫ p, bill p ∂revealLaw P) ≤
          ∫ p, CL * S (Spitzer.reorder p.1 p.2) ∂revealLaw P :=
        integral_mono hBilli (hSi.const_mul CL) hPoint
      _ = CL * (∫ a, S a ∂P) := by
        rw [integral_const_mul]
        congr 1
        exact hSid.integral_eq
      _ ≤ CL * (KG * delta * Real.exp (-x ^ 2)) := mul_le_mul_of_nonneg_left hGridData.2.2 hCL.le
      _ = CL * KG * delta * Real.exp (-x ^ 2) := by ring
  have hExpTail : Real.exp (-x ^ 2) ≤ 2 * Real.sqrt (2 * Real.pi) * Shao.standardNormalTail x := by
    have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    have hM := (Shao.standardNormal_mills_bounds x hxpos.le).1
    have hDensity : Shao.standardNormalDensity x =
        (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x^2/2) := by
      simp [Shao.standardNormalDensity, ProbabilityTheory.gaussianPDFReal]
    rw [hDensity] at hM
    have hx1 : 1 ≤ x := by linarith
    have he : x ≤ Real.exp (x ^ 2 / 2) := by
      have hh := Real.add_one_le_exp (x ^ 2 / 2)
      nlinarith [sq_nonneg (x - 1)]
    have hh : (1 + x) * Real.exp (-x ^ 2 / 2) ≤ 2 := by
      have heInv : Real.exp (-x ^ 2 / 2) * Real.exp (x ^ 2 / 2) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      have hz := Real.exp_pos (-x ^ 2 / 2)
      nlinarith
    have hFactor : Real.exp (-x ^ 2) =
        (Real.exp (-x ^ 2 / 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have hM' : Real.exp (-x ^ 2 / 2) ≤
        Shao.standardNormalTail x * (Real.sqrt (2 * Real.pi) * (1 + x)) := by
      apply (div_le_iff₀ (mul_pos hs (by linarith : 0 < 1 + x))).mp
      convert hM using 1 <;> field_simp <;> ring
    rw [hFactor]
    have hm := mul_le_mul_of_nonneg_left hM' (Real.exp_pos (-x ^ 2 / 2)).le
    have ht : 0 ≤ Shao.standardNormalTail x := ((Shao.standardNormalTail_basic).2.2.1 x).1.le
    nlinarith [mul_le_mul_of_nonneg_right hh (mul_nonneg ht hs.le)]
  refine ⟨hBillm, hBilli, hStrong.trans ?_, hStrong.trans ?_⟩
  · dsimp [C]
    have hfac : 1 ≤ 1 + 2 * Real.sqrt (2 * Real.pi) := by nlinarith [Real.sqrt_nonneg (2 * Real.pi)]
    have hcoef : CL * KG ≤ CL * KG * (1 + 2 * Real.sqrt (2 * Real.pi)) :=
      le_mul_of_one_le_right (mul_nonneg hCL.le hKG.le) hfac
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hdelta.le) (Real.exp_pos _).le
  · calc
      CL * KG * delta * Real.exp (-x ^ 2) ≤
          CL * KG * delta * (2 * Real.sqrt (2 * Real.pi) * Shao.standardNormalTail x) :=
        mul_le_mul_of_nonneg_left hExpTail (by positivity)
      _ ≤ C * delta * Shao.standardNormalTail x := by
        dsimp [C]
        have hnn : 0 ≤ CL * KG * delta * Shao.standardNormalTail x := by
          exact mul_nonneg (by positivity) (((Shao.standardNormalTail_basic).2.2.1 x).1.le)
        nlinarith

end Shao.Probability.SourceRegularRetainedProbability
