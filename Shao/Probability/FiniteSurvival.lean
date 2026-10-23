import Shao.Probability.BerryEsseen
import Shao.Probability.SpitzerLaplace
import Mathlib.Analysis.SumIntegralComparisons

/-!
Finite closed survival from the actual finite CDF and Spitzer producers.
The nonzero actual mean remains explicit in the generating-series correction.
-/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped Topology

private theorem fs_centered_third_moment_ge_variance
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu) :
    let mu : ℝ := ∫ z : ℝ, z ∂nu
    let V : ℝ := variance (id : ℝ → ℝ) nu
    (Real.sqrt V) ^ 3 ≤ ∫ z : ℝ, |z - mu| ^ 3 ∂nu := by
  let mu : ℝ := ∫ z : ℝ, z ∂nu
  let V : ℝ := variance (id : ℝ → ℝ) nu
  let tau : ℝ := Real.sqrt V
  have htau : 0 < tau := Real.sqrt_pos.2 hV
  have htau2 : tau ^ 2 = V := Real.sq_sqrt hV.le
  have hLp : MemLp id 3 nu := by
    apply (integrable_norm_rpow_iff (p := (3 : ENNReal))
      measurable_id.aestronglyMeasurable (by norm_num) (by norm_num)).1
    have hh := h3
    simp_rw [← Real.rpow_natCast] at hh
    simpa only [ENNReal.toReal_ofNat, Real.norm_eq_abs, id_eq, Nat.cast_ofNat] using hh
  have hLpc : MemLp (fun z : ℝ => z - mu) 3 nu := hLp.sub (memLp_const mu)
  have hc3 : Integrable (fun z : ℝ => |z - mu| ^ 3) nu := by
    simpa only [Real.norm_eq_abs] using hLpc.integrable_norm_pow'
  have hc2 : Integrable (fun z : ℝ => (z - mu) ^ 2) nu := by
    have hh := (hLpc.mono_exponent (show (2 : ENNReal) ≤ 3 by norm_num)).integrable_norm_pow'
    simpa only [Real.norm_eq_abs, sq_abs] using hh
  have hVeq : (∫ z : ℝ, (z - mu) ^ 2 ∂nu) = V :=
    (variance_eq_integral measurable_id.aemeasurable).symm
  have hpoint (z : ℝ) : 3 * tau * (z - mu) ^ 2 ≤
      2 * |z - mu| ^ 3 + tau ^ 3 := by
    have hh := mul_nonneg (sq_nonneg (|z - mu| - tau))
      (show 0 ≤ 2 * |z - mu| + tau by positivity)
    rw [← sq_abs (z - mu)]
    nlinarith only [hh]
  have hi := integral_mono (hc2.const_mul (3 * tau))
    ((hc3.const_mul 2).add (integrable_const (tau ^ 3))) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul, integral_add (hc3.const_mul 2) (integrable_const (tau ^ 3)),
    integral_const_mul, hVeq] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  rw [← htau2] at hi
  change tau ^ 3 ≤ ∫ z : ℝ, |z - mu| ^ 3 ∂nu
  nlinarith only [hi]

private theorem fs_positiveLaplace_scale
    (sigma L s : ℝ) (hsigma : 0 < sigma) :
    Shao.OQ4.positiveLaplace L (s / sigma) =
      Shao.OQ4.positiveLaplace (sigma * L) s := by
  unfold Shao.OQ4.positiveLaplace
  by_cases hs : 0 ≤ s
  · rw [max_eq_left (div_nonneg hs hsigma.le), max_eq_left hs]
    congr 1
    congr 1
    field_simp
  · rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hs) hsigma.le),
      max_eq_right (le_of_not_ge hs)]
    simp

private theorem fs_actual_payment_lower_bound
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (L : ℝ) (hL : 1 ≤ L)
    (hbetaL : (∫ z : ℝ, |z - ∫ w : ℝ, w ∂nu| ^ 3 ∂nu) /
      (Real.sqrt (variance (id : ℝ → ℝ) nu)) ^ 3 ≤ L)
    (k : ℕ) (hk : 1 ≤ k) :
    let mu : ℝ := ∫ z : ℝ, z ∂nu
    let sigma : ℝ := Real.sqrt (variance (id : ℝ → ℝ) nu)
    let delta : ℝ := |mu| / sigma
    1 / 2 - (1025 : ℝ) * L / Real.sqrt (k : ℝ) - delta * Real.sqrt (k : ℝ) ≤
      Shao.OQ4.finiteSumLaplacePayment nu k (sigma * L) := by
  let mu : ℝ := ∫ z : ℝ, z ∂nu
  let sigma : ℝ := Real.sqrt (variance (id : ℝ → ℝ) nu)
  let beta : ℝ := (∫ z : ℝ, |z - mu| ^ 3 ∂nu) / sigma ^ 3
  let delta : ℝ := |mu| / sigma
  let v : ℝ := Real.sqrt (k : ℝ)
  let P : Measure (Shao.Path k) := Measure.pi (fun _ : Fin k => nu)
  let X : Shao.Path k → ℝ := fun a => Shao.prefixSum a k / sigma
  let law : Measure ℝ := P.map X
  let epsilon : ℝ := 1024 * beta / v + delta * v
  let C : ℝ := epsilon * v / L
  have hsigma : 0 < sigma := Real.sqrt_pos.2 hV
  have hv : 0 < v := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < k by omega))
  have hLp : 0 < L := by linarith
  have hbeta : 0 ≤ beta := by dsimp [beta]; positivity
  have hdelta : 0 ≤ delta := div_nonneg (abs_nonneg mu) hsigma.le
  have hepsilon : 0 ≤ epsilon := by dsimp [epsilon]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCL : C * L / v = epsilon := by dsimp [C]; field_simp
  have hX : Measurable X := (Shao.measurable_prefixSum k).div_const sigma
  have hlaw : IsProbabilityMeasure law := by
    constructor
    change P.map X Set.univ = 1
    rw [Measure.map_apply hX MeasurableSet.univ]
    simp
  letI : IsProbabilityMeasure law := hlaw
  have hCDF (x : ℝ) :
      |law.real {y : ℝ | y / v ≤ x} - Shao.OQ4.standardNormalCDF x| ≤ C * L / v := by
    have hB : MeasurableSet {y : ℝ | y / v ≤ x} :=
      measurableSet_le (measurable_id.div_const v) measurable_const
    have hs : X ⁻¹' {y : ℝ | y / v ≤ x} =
        {a : Shao.Path k | Shao.prefixSum a k / (sigma * v) ≤ x} := by
      ext a
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, X, div_div]
    change |((P.map X) {y : ℝ | y / v ≤ x}).toReal - _| ≤ _
    rw [Measure.map_apply hX hB, hs, hCL]
    have hc := iid_uncentered_berryEsseen nu h3 hV k hk x
    change |P.real {a : Shao.Path k | Shao.prefixSum a k / (sigma * v) ≤ x} -
      Shao.OQ4.standardNormalCDF x| ≤
      1024 * (∫ z : ℝ, |z - mu| ^ 3 ∂nu) / (sigma ^ 3 * v) + |mu| * v / sigma at hc
    change |P.real {a : Shao.Path k | Shao.prefixSum a k / (sigma * v) ≤ x} -
      Shao.OQ4.standardNormalCDF x| ≤ epsilon
    calc
      _ ≤ 1024 * (∫ z : ℝ, |z - mu| ^ 3 ∂nu) / (sigma ^ 3 * v) +
          |mu| * v / sigma := hc
      _ = epsilon := by dsimp [epsilon, beta, delta]; ring
  have hpay := Shao.OQ4.laplacePayment_lower_bound_of_cdf law k hk C L L hC hL le_rfl hCDF
  have hpayEq : Shao.OQ4.laplacePayment law L =
      Shao.OQ4.finiteSumLaplacePayment nu k (sigma * L) := by
    unfold Shao.OQ4.laplacePayment Shao.OQ4.finiteSumLaplacePayment
    rw [integral_map (μ := P) (φ := X) (f := Shao.OQ4.positiveLaplace L)
      hX.aemeasurable (Shao.OQ4.integrable_positiveLaplace law hLp).aestronglyMeasurable]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun a =>
      fs_positiveLaplace_scale sigma L (Shao.prefixSum a k) hsigma
  rw [hpayEq] at hpay
  have heq : (1 + C) * L / v = L / v + epsilon := by
    rw [add_mul, add_div, hCL, one_mul]
  have hcompare : L / v + epsilon ≤ 1025 * L / v + delta * v := by
    change beta ≤ L at hbetaL
    calc
      _ = (L + 1024 * beta) / v + delta * v := by dsimp [epsilon]; ring
      _ ≤ (L + 1024 * L) / v + delta * v := by
        have hh := div_le_div_of_nonneg_right
          (show L + 1024 * beta ≤ L + 1024 * L by linarith) hv.le
        linarith only [hh]
      _ = _ := by ring
  rw [heq] at hpay
  change 1 / 2 - 1025 * L / v - delta * v ≤ _
  linarith

private theorem fs_drift_sqrt_series (m : ℕ) (hm : 1 ≤ m) :
    let s : ℝ := Real.exp (-1 / (m : ℝ))
    Summable (fun n : ℕ => s ^ (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ)) ∧
      (∑' n : ℕ, s ^ (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ)) ≤
        4 * Real.sqrt (m : ℝ) := by
  let s : ℝ := Real.exp (-1 / (m : ℝ))
  let f : ℝ → ℝ := fun x => x ^ (-(1 / 2 : ℝ)) * Real.exp (-((m : ℝ)⁻¹ * x))
  have hmp : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hr : 0 < (m : ℝ)⁻¹ := inv_pos.2 hmp
  have hfi0 : IntegrableOn f (Set.Ioi 0) := by
    have hi := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := -(1 / 2 : ℝ)) (p := 1) (b := (m : ℝ)⁻¹)
      (by norm_num) (by norm_num) hr
    simpa only [Real.rpow_one, neg_mul] using hi
  have hfi1 : IntegrableOn f (Set.Ioi 1) :=
    hfi0.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  have hfpos (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f x :=
    mul_nonneg (Real.rpow_nonneg hx _) (Real.exp_pos _).le
  have hanti : AntitoneOn f (Set.Ici 1) := by
    intro x hx y hy hxy
    have hxp : 0 < x := by linarith [show 1 ≤ x from hx]
    have hyp : 0 < y := hxp.trans_le hxy
    exact mul_le_mul
      (Real.rpow_le_rpow_of_nonpos hxp hxy (by norm_num : -(1 / 2 : ℝ) ≤ 0))
      (Real.exp_le_exp.mpr (by nlinarith))
      (Real.exp_pos _).le (Real.rpow_nonneg hxp.le _)
  have hsumf : Summable (fun n : ℕ => f (n : ℝ)) :=
    (show AntitoneOn f (Set.Ici ((1 : ℕ) : ℝ)) by simpa only [Nat.cast_one] using hanti)
      |>.summable_of_integrableOn_Ioi (N := 1)
        (by simpa only [Nat.cast_one] using hfi1)
        (fun x hx => hfpos x (by
          have hh : (1 : ℝ) < x := by simpa only [Set.mem_Ioi, Nat.cast_one] using hx
          linarith))
  have hsum : Summable (fun n : ℕ => f ((n + 1 : ℕ) : ℝ)) :=
    (summable_nat_add_iff 1).2 hsumf
  have htail : (∑' n : ℕ, f ((n + 1 + 1 : ℕ) : ℝ)) ≤
      ∫ x : ℝ in Set.Ioi 0, f x := by
    calc
      _ ≤ ∫ x : ℝ in Set.Ioi (1 : ℝ), f x := by
        simpa only [Nat.cast_one] using
          ((show AntitoneOn f (Set.Ici ((1 : ℕ) : ℝ)) by simpa only [Nat.cast_one] using hanti)
          |>.tsum_comp_add_le_integral 1 (by simpa only [Nat.cast_one] using hfi1)
            (fun x hx => hfpos x (by
              have hh : (1 : ℝ) < x := by simpa only [Set.mem_Ioi, Nat.cast_one] using hx
              linarith)))
      _ ≤ _ := setIntegral_mono_set hfi0
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          exact hfpos x hx.le)
        (Filter.Eventually.of_forall fun x hx => by
          exact lt_trans (by norm_num : (0 : ℝ) < 1) hx)
  have hval : (∫ x : ℝ in Set.Ioi 0, f x) =
      Real.sqrt (m : ℝ) * Real.sqrt Real.pi := by
    have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (1 / 2 : ℝ)) (r := (m : ℝ)⁻¹) (by norm_num) hr
    norm_num only [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num,
      one_div, inv_inv] at hi
    rw [Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow] at hi
    exact hi
  have hfirst : f 1 ≤ 1 := by
    simp only [f, Real.one_rpow, one_mul, mul_one]
    exact Real.exp_le_one_iff.2 (by linarith)
  have hroot : 1 ≤ Real.sqrt (m : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hmr
  have hpi : Real.sqrt Real.pi ≤ 2 :=
    (Real.sqrt_le_iff).2 ⟨by norm_num, by linarith [Real.pi_lt_four]⟩
  have hterm (n : ℕ) : f ((n + 1 : ℕ) : ℝ) =
      s ^ (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    dsimp [f, s]
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, ← Real.exp_nat_mul]
    have he : -((m : ℝ)⁻¹ * ((n + 1 : ℕ) : ℝ)) =
        ((n + 1 : ℕ) : ℝ) * (-1 / (m : ℝ)) := by ring
    rw [he]
    ring
  refine ⟨by simpa only [hterm] using hsum, ?_⟩
  change (∑' n : ℕ, s ^ (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ)) ≤ _
  rw [← show (fun n : ℕ => f ((n + 1 : ℕ) : ℝ)) =
    (fun n : ℕ => s ^ (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ)) from funext hterm]
  rw [hsum.tsum_eq_zero_add]
  have htail' : (∑' n : ℕ, f ((n + 1 + 1 : ℕ) : ℝ)) ≤
      2 * Real.sqrt (m : ℝ) := by
    rw [hval] at htail
    exact htail.trans (by nlinarith [Real.sqrt_nonneg (m : ℝ)])
  simpa only [zero_add, Nat.cast_one] using
    (show f 1 + (∑' n : ℕ, f ((n + 1 + 1 : ℕ) : ℝ)) ≤
      4 * Real.sqrt (m : ℝ) by linarith)

private theorem fs_corrected_laplaceW_lower
    (A : ℕ → ℝ) (L C delta : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C) (hd : 0 ≤ delta)
    (hA : ∀ k : ℕ, 1 ≤ k → 0 ≤ A k ∧ A k ≤ 1)
    (hS1 : ∀ k : ℕ, 1 ≤ k →
      1 / 2 - C * L / Real.sqrt (k : ℝ) - delta * Real.sqrt (k : ℝ) ≤ A k)
    (m : ℕ) (hm : 1 ≤ m) :
    let s : ℝ := Real.exp (-1 / (m : ℝ));
    -(1 / 2) * Real.log (1 - s) - Real.log L - (1 + 3 * C) -
        4 * delta * Real.sqrt (m : ℝ) ≤ Shao.OQ4.laplaceW A s := by
  let s : ℝ := Real.exp (-1 / (m : ℝ))
  let B : ℕ → ℝ := fun k => min 1 (A k + delta * Real.sqrt (k : ℝ))
  obtain ⟨hs0, hs1, hgap⟩ := Shao.OQ4.exp_neg_reciprocal_gap m hm
  change 0 < s at hs0
  change s < 1 at hs1
  have hLp : 0 < L := by linarith
  have hB (k : ℕ) (hk : 1 ≤ k) : 0 ≤ B k ∧ B k ≤ 1 := by
    constructor
    · exact le_min (by norm_num) (add_nonneg (hA k hk).1
        (mul_nonneg hd (Real.sqrt_nonneg _)))
    · exact min_le_left _ _
  have hSB (k : ℕ) (hk : 1 ≤ k) :
      1 / 2 - C * L / Real.sqrt (k : ℝ) ≤ B k := by
    apply le_min
    · have hh : 0 ≤ C * L / Real.sqrt (k : ℝ) := by positivity
      linarith
    · linarith [hS1 k hk]
  have hW := Shao.OQ4.laplaceW_lower_bound B L C hL hC hB hSB hs0 hs1
  have hAs := Shao.OQ4.summable_laplaceW A hs0 hs1 hA
  have hBs := Shao.OQ4.summable_laplaceW B hs0 hs1 hB
  have hDs := hBs.sub hAs
  obtain ⟨hRs, hRb⟩ := fs_drift_sqrt_series m hm
  change Summable (fun n : ℕ => s ^ (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ)) at hRs
  change (∑' n : ℕ, s ^ (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ)) ≤
    4 * Real.sqrt (m : ℝ) at hRb
  have hpoint (n : ℕ) :
      s ^ (n + 1) * B (n + 1) / (n + 1) -
        s ^ (n + 1) * A (n + 1) / (n + 1) ≤
      delta * (s ^ (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
    have hnp : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hrp : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 hnp
    have hrsq := Real.sq_sqrt hnp.le
    have hcancel : Real.sqrt ((n + 1 : ℕ) : ℝ) / ((n : ℝ) + 1) =
        (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ := by
      apply mul_right_cancel₀ hrp.ne'
      rw [div_mul_eq_mul_div, Real.mul_self_sqrt hnp.le, inv_mul_cancel₀ hrp.ne']
      simp [Nat.cast_add, Nat.cast_one, show (n : ℝ) + 1 ≠ 0 by positivity]
    have hBdiff : B (n + 1) - A (n + 1) ≤
        delta * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
      have hh := min_le_right (1 : ℝ) (A (n + 1) + delta * Real.sqrt ((n + 1 : ℕ) : ℝ))
      change B (n + 1) ≤ A (n + 1) + delta * Real.sqrt ((n + 1 : ℕ) : ℝ) at hh
      linarith
    calc
      _ = s ^ (n + 1) * (B (n + 1) - A (n + 1)) / (n + 1) := by ring
      _ ≤ s ^ (n + 1) * (delta * Real.sqrt ((n + 1 : ℕ) : ℝ)) / (n + 1) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hBdiff (pow_nonneg hs0.le _))
          (by simpa only [Nat.cast_add, Nat.cast_one] using hnp.le)
      _ = delta * s ^ (n + 1) * (Real.sqrt ((n + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) := by ring
      _ = _ := by rw [hcancel]; ring
  have hDsum : (∑' n : ℕ, (s ^ (n + 1) * B (n + 1) / (n + 1) -
      s ^ (n + 1) * A (n + 1) / (n + 1))) =
      Shao.OQ4.laplaceW B s - Shao.OQ4.laplaceW A s :=
    (hBs.hasSum.sub hAs.hasSum).tsum_eq
  have hdiff : Shao.OQ4.laplaceW B s - Shao.OQ4.laplaceW A s ≤
      4 * delta * Real.sqrt (m : ℝ) := by
    rw [← hDsum]
    calc
      _ ≤ ∑' n : ℕ, delta * (s ^ (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ)) :=
        Summable.tsum_le_tsum hpoint hDs (hRs.mul_left delta)
      _ = delta * (∑' n : ℕ, s ^ (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ)) :=
        (hRs.hasSum.mul_left delta).tsum_eq
      _ ≤ delta * (4 * Real.sqrt (m : ℝ)) := mul_le_mul_of_nonneg_left hRb hd
      _ = _ := by ring
  change -(1 / 2) * Real.log (1 - s) - Real.log L - (1 + 3 * C) -
    4 * delta * Real.sqrt (m : ℝ) ≤ Shao.OQ4.laplaceW A s
  linarith

private theorem fs_coefficient_bound_at_exp
    (a : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ 1) (hanti : Antitone a)
    (m : ℕ) (hm : 1 ≤ m)
    (hG : Shao.OQ4.laplaceG a (Real.exp (-1 / (m : ℝ))) ≤
      B / Real.sqrt (1 - Real.exp (-1 / (m : ℝ)))) :
    a m ≤ Real.sqrt 2 * Real.exp 1 * B / Real.sqrt (m : ℝ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmroot : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmpos
  let s : ℝ := Real.exp (-1 / (m : ℝ))
  obtain ⟨hs0, hs1, hgap⟩ := Shao.OQ4.exp_neg_reciprocal_gap m hm
  change 0 < s at hs0
  change s < 1 at hs1
  change 1 / (2 * (m : ℝ)) ≤ 1 - s at hgap
  have hspow : s ^ m = Real.exp (-1) := by
    dsimp [s]
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have hsum := Shao.OQ4.summable_laplaceG a hs0 hs1 ha
  have hprefix : (m : ℝ) * s ^ m * a m ≤ Shao.OQ4.laplaceG a s := by
    calc
      _ = ∑ j ∈ Finset.range m, s ^ m * a m := by simp; ring
      _ ≤ ∑ j ∈ Finset.range m, s ^ j * a j := by
        apply Finset.sum_le_sum
        intro j hj
        have hjm : j ≤ m := (Finset.mem_range.mp hj).le
        exact mul_le_mul (pow_le_pow_of_le_one hs0.le hs1.le hjm) (hanti hjm)
          (ha m).1 (pow_nonneg hs0.le j)
      _ ≤ _ := Summable.sum_le_tsum (Finset.range m)
        (fun j _ => mul_nonneg (pow_nonneg hs0.le j) (ha j).1) hsum
  rw [hspow] at hprefix
  have hcancel : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
  have haG : a m ≤ Real.exp 1 * Shao.OQ4.laplaceG a s / (m : ℝ) := by
    apply (le_div_iff₀ hmpos).2
    calc
      _ = (Real.exp 1 * Real.exp (-1)) * ((m : ℝ) * a m) := by rw [hcancel]; ring
      _ = Real.exp 1 * ((m : ℝ) * Real.exp (-1) * a m) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hprefix (Real.exp_pos 1).le
  have hroot2 : 0 < Real.sqrt (2 * (m : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hgroot := Real.sqrt_le_sqrt hgap
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one] at hgroot
  have hinv : 1 / Real.sqrt (1 - s) ≤ Real.sqrt (2 * (m : ℝ)) := by
    have hi := one_div_le_one_div_of_le (div_pos (by norm_num : (0 : ℝ) < 1) hroot2) hgroot
    simpa using hi
  have hG' : Shao.OQ4.laplaceG a s ≤ B * Real.sqrt (2 * (m : ℝ)) := by
    calc
      _ ≤ B / Real.sqrt (1 - s) := hG
      _ = B * (1 / Real.sqrt (1 - s)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hinv hB
  have hid : Real.sqrt (m : ℝ) / (m : ℝ) = (Real.sqrt (m : ℝ))⁻¹ := by
    apply mul_right_cancel₀ hmroot.ne'
    rw [div_mul_eq_mul_div, Real.mul_self_sqrt hmpos.le, div_self hmpos.ne',
      inv_mul_cancel₀ hmroot.ne']
  calc
    _ ≤ Real.exp 1 * Shao.OQ4.laplaceG a s / (m : ℝ) := haG
    _ ≤ Real.exp 1 * (B * Real.sqrt (2 * (m : ℝ))) / (m : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hG' (Real.exp_pos 1).le) hmpos.le
    _ = (Real.sqrt 2 * Real.exp 1 * B) * (Real.sqrt (m : ℝ) / (m : ℝ)) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    _ = _ := by rw [hid]; rfl

private theorem fs_actual_maxLaplaceMean_bound
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (L : ℝ) (hL : 1 ≤ L)
    (hbetaL : (∫ z : ℝ, |z - ∫ w : ℝ, w ∂nu| ^ 3 ∂nu) /
      (Real.sqrt (variance (id : ℝ → ℝ) nu)) ^ 3 ≤ L)
    (m : ℕ) (hm : 1 ≤ m) :
    let sigma : ℝ := Real.sqrt (variance (id : ℝ → ℝ) nu)
    let delta : ℝ := |∫ z : ℝ, z ∂nu| / sigma
    Shao.OQ4.maxLaplaceMean nu (sigma * L) m ≤
      Real.sqrt 2 * Real.exp (5 + 3 * (1024 : ℝ)) * L / Real.sqrt (m : ℝ) *
        Real.exp (4 * delta * Real.sqrt (m : ℝ)) := by
  let sigma : ℝ := Real.sqrt (variance (id : ℝ → ℝ) nu)
  let delta : ℝ := |∫ z : ℝ, z ∂nu| / sigma
  let A : ℕ → ℝ := fun k => Shao.OQ4.finiteSumLaplacePayment nu k (sigma * L)
  let a : ℕ → ℝ := Shao.OQ4.maxLaplaceMean nu (sigma * L)
  let s : ℝ := Real.exp (-1 / (m : ℝ))
  let D : ℝ := 4 * delta * Real.sqrt (m : ℝ)
  let B : ℝ := Real.exp (1 + 3 * (1025 : ℝ)) * L * Real.exp D
  have hsigma : 0 < sigma := Real.sqrt_pos.2 hV
  have hLp : 0 < L := by linarith
  have hH : 0 < sigma * L := mul_pos hsigma hLp
  have hd : 0 ≤ delta := div_nonneg (abs_nonneg _) hsigma.le
  obtain ⟨hs0, hs1, _⟩ := Shao.OQ4.exp_neg_reciprocal_gap m hm
  change 0 < s at hs0
  change s < 1 at hs1
  have hA (k : ℕ) (_hk : 1 ≤ k) : 0 ≤ A k ∧ A k ≤ 1 :=
    Shao.OQ4.finiteSumLaplacePayment_bounds nu k hH
  have hS (k : ℕ) (hk : 1 ≤ k) :
      1 / 2 - 1025 * L / Real.sqrt (k : ℝ) - delta * Real.sqrt (k : ℝ) ≤ A k :=
    fs_actual_payment_lower_bound nu h3 hV L hL hbetaL k hk
  have hW := fs_corrected_laplaceW_lower A L 1025 delta hL (by norm_num) hd hA hS m hm
  change -(1 / 2) * Real.log (1 - s) - Real.log L - (1 + 3 * 1025) - D ≤
    Shao.OQ4.laplaceW A s at hW
  have hWshift : -(1 / 2) * Real.log (1 - s) - Real.log L - (1 + 3 * 1025) ≤
      Shao.OQ4.laplaceW A s + D := by linarith
  have hSP : Shao.OQ4.laplaceG a s = (1 - s)⁻¹ * Real.exp (-Shao.OQ4.laplaceW A s) :=
    Shao.OQ4.maxLaplace_original_sp_to_normalized nu hH hs0 hs1
      (actual_maximum_spitzer_laplace nu hH hs0 hs1)
  have hSPshift : Shao.OQ4.laplaceG a s * Real.exp (-D) =
      (1 - s)⁻¹ * Real.exp (-(Shao.OQ4.laplaceW A s + D)) := by
    rw [hSP]
    calc
      _ = (1 - s)⁻¹ * (Real.exp (-Shao.OQ4.laplaceW A s) * Real.exp (-D)) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 1; congr 1; ring
  have hGU := Shao.OQ4.generating_upper_of_W_lower
    (Shao.OQ4.laplaceG a s * Real.exp (-D)) (Shao.OQ4.laplaceW A s + D)
    L 1025 s hLp hs0 hs1 hWshift hSPshift
  have hGbound : Shao.OQ4.laplaceG a s ≤ B / Real.sqrt (1 - s) := by
    calc
      _ = (Shao.OQ4.laplaceG a s * Real.exp (-D)) * Real.exp D := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      _ ≤ (Real.exp (1 + 3 * (1025 : ℝ)) * L / Real.sqrt (1 - s)) * Real.exp D :=
        mul_le_mul_of_nonneg_right hGU (Real.exp_pos D).le
      _ = _ := by dsimp [B]; ring
  have hcoef := fs_coefficient_bound_at_exp a B (by dsimp [B]; positivity)
    (fun j => Shao.OQ4.maxLaplaceMean_bounds nu j hH)
    (Shao.OQ4.maxLaplaceMean_antitone nu hH) m hm hGbound
  have he : Real.exp 1 * Real.exp (1 + 3 * (1025 : ℝ)) =
      Real.exp (5 + 3 * (1024 : ℝ)) := by
    rw [← Real.exp_add]
    norm_num
  change a m ≤ Real.sqrt 2 * Real.exp (5 + 3 * (1024 : ℝ)) * L / Real.sqrt (m : ℝ) * Real.exp D
  calc
    _ ≤ Real.sqrt 2 * Real.exp 1 * B / Real.sqrt (m : ℝ) := hcoef
    _ = Real.sqrt 2 * (Real.exp 1 * Real.exp (1 + 3 * (1025 : ℝ))) * L /
        Real.sqrt (m : ℝ) * Real.exp D := by dsimp [B]; ring
    _ = _ := by rw [he]

theorem iid_closed_survival_nonzero_drift
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    let mu : ℝ := ∫ z : ℝ, z ∂nu
    let V : ℝ := variance (id : ℝ → ℝ) nu
    let m3c : ℝ := ∫ z : ℝ, |z - mu| ^ 3 ∂nu
    (Measure.pi (fun _ : Fin m => nu)).real
        {a : Shao.Path m | Shao.maxWithZero a ≤ r} ≤
      (2 * Real.exp (6 + 3 * (1024 : ℝ))) *
        min 1 ((r + m3c / V) /
          (Real.sqrt V * Real.sqrt ((m + 1 : ℕ) : ℝ))) *
        Real.exp (4 * (|mu| * Real.sqrt (m : ℝ) / Real.sqrt V)) := by
  let mu : ℝ := ∫ z : ℝ, z ∂nu
  let V : ℝ := variance (id : ℝ → ℝ) nu
  let sigma : ℝ := Real.sqrt V
  let m3c : ℝ := ∫ z : ℝ, |z - mu| ^ 3 ∂nu
  let beta : ℝ := m3c / sigma ^ 3
  let delta : ℝ := |mu| / sigma
  let d : ℝ := r / sigma
  let L : ℝ := d + beta
  let K : ℝ := 2 * Real.exp (6 + 3 * (1024 : ℝ))
  have hsigma : 0 < sigma := Real.sqrt_pos.2 hV
  have hsigma2 : sigma ^ 2 = V := Real.sq_sqrt hV.le
  have hbeta : 1 ≤ beta := by
    apply (le_div_iff₀ (pow_pos hsigma 3)).2
    simpa only [one_mul] using fs_centered_third_moment_ge_variance nu h3 hV
  have hd : 0 ≤ d := div_nonneg hr hsigma.le
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hbetaL : beta ≤ L := by dsimp [L]; linarith
  have hLp : 0 < L := by linarith
  have hH : 0 < sigma * L := mul_pos hsigma hLp
  have hdelta : 0 ≤ delta := div_nonneg (abs_nonneg mu) hsigma.le
  have hK : 1 ≤ K := by
    have hh : 1 ≤ Real.exp (6 + 3 * (1024 : ℝ)) :=
      Real.one_le_exp_iff.2 (by norm_num)
    dsimp [K]
    linarith
  have hP : (Measure.pi (fun _ : Fin m => nu)).real
      {a : Shao.Path m | Shao.maxWithZero a ≤ r} ≤ 1 := by
    simpa only [probReal_univ] using
      (measureReal_mono (μ := Measure.pi (fun _ : Fin m => nu))
        (Set.subset_univ {a : Shao.Path m | Shao.maxWithZero a ≤ r}))
  have hratio : (r + m3c / V) / (sigma * Real.sqrt ((m + 1 : ℕ) : ℝ)) =
      L / Real.sqrt ((m + 1 : ℕ) : ℝ) := by
    dsimp [L, d, beta]
    rw [← hsigma2]
    field_simp
    <;> ring
  have hDrift : Real.exp (4 * (|mu| * Real.sqrt (m : ℝ) / sigma)) =
      Real.exp (4 * delta * Real.sqrt (m : ℝ)) := by
    congr 1
    dsimp [delta]
    ring
  change (Measure.pi (fun _ : Fin m => nu)).real
    {a : Shao.Path m | Shao.maxWithZero a ≤ r} ≤
    K * min 1 ((r + m3c / V) / (sigma * Real.sqrt ((m + 1 : ℕ) : ℝ))) *
      Real.exp (4 * (|mu| * Real.sqrt (m : ℝ) / sigma))
  rw [hratio, hDrift]
  by_cases hm0 : m = 0
  · subst m
    simp only [Nat.zero_add, Nat.cast_one, Real.sqrt_one, div_one, Nat.cast_zero,
      Real.sqrt_zero, mul_zero, Real.exp_zero, mul_one]
    rw [min_eq_left hL]
    simpa only [mul_one] using hP.trans hK
  · have hm : 1 ≤ m := by omega
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have hvm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmpos
    have hvm1 : 0 < Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hLscale : sigma * L = r + sigma * beta := by
      dsimp [L, d]
      field_simp
      <;> ring
    have hrH : r / (sigma * L) ≤ 1 := by
      apply (div_le_one hH).2
      rw [hLscale]
      have hh : 0 ≤ sigma * beta := mul_nonneg hsigma.le (by linarith)
      linarith
    have hEvent : (Shao.closedUpper r : Set (Shao.Path m)) =
        {a : Shao.Path m | Shao.maxWithZero a ≤ r} := by
      ext a
      exact Shao.mem_closedUpper_iff_maxWithZero_le a r
    have hMarkov := Shao.OQ4.closedUpper_probability_le_laplace nu m r hr hH
    rw [hEvent] at hMarkov
    have hcoef := fs_actual_maxLaplaceMean_bound nu h3 hV L hL hbetaL m hm
    change Shao.OQ4.maxLaplaceMean nu (sigma * L) m ≤
      Real.sqrt 2 * Real.exp (5 + 3 * (1024 : ℝ)) * L / Real.sqrt (m : ℝ) *
        Real.exp (4 * delta * Real.sqrt (m : ℝ)) at hcoef
    have he : Real.exp 1 * Real.exp (5 + 3 * (1024 : ℝ)) =
        Real.exp (6 + 3 * (1024 : ℝ)) := by rw [← Real.exp_add]; norm_num
    have hroots : Real.sqrt 2 / Real.sqrt (m : ℝ) ≤
        2 / Real.sqrt ((m + 1 : ℕ) : ℝ) := by
      apply (div_le_div_iff₀ hvm hvm1).2
      apply (sq_le_sq₀ (by positivity) (by positivity)).1
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        Real.sq_sqrt (by positivity : 0 ≤ ((m + 1 : ℕ) : ℝ)), Real.sq_sqrt hmpos.le]
      have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
      norm_num only [Nat.cast_add, Nat.cast_one]
      nlinarith
    have hlinear : (Measure.pi (fun _ : Fin m => nu)).real
        {a : Shao.Path m | Shao.maxWithZero a ≤ r} ≤
        K * (L / Real.sqrt ((m + 1 : ℕ) : ℝ)) *
          Real.exp (4 * delta * Real.sqrt (m : ℝ)) := by
      calc
        _ ≤ Real.exp (r / (sigma * L)) * Shao.OQ4.maxLaplaceMean nu (sigma * L) m := hMarkov
        _ ≤ Real.exp 1 * Shao.OQ4.maxLaplaceMean nu (sigma * L) m :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hrH)
            (Shao.OQ4.maxLaplaceMean_bounds nu m hH).1
        _ ≤ Real.exp 1 * (Real.sqrt 2 * Real.exp (5 + 3 * (1024 : ℝ)) * L /
            Real.sqrt (m : ℝ) * Real.exp (4 * delta * Real.sqrt (m : ℝ))) :=
          mul_le_mul_of_nonneg_left hcoef (Real.exp_pos 1).le
        _ = (Real.sqrt 2 / Real.sqrt (m : ℝ)) *
            (Real.exp (6 + 3 * (1024 : ℝ)) * L *
              Real.exp (4 * delta * Real.sqrt (m : ℝ))) := by
          rw [← he]
          ring
        _ ≤ (2 / Real.sqrt ((m + 1 : ℕ) : ℝ)) *
            (Real.exp (6 + 3 * (1024 : ℝ)) * L *
              Real.exp (4 * delta * Real.sqrt (m : ℝ))) :=
          mul_le_mul_of_nonneg_right hroots (by positivity)
        _ = _ := by dsimp [K]; ring
    by_cases hR : L / Real.sqrt ((m + 1 : ℕ) : ℝ) ≤ 1
    · rw [min_eq_right hR]
      exact hlinear
    · rw [min_eq_left (le_of_not_ge hR), mul_one]
      have hE : 1 ≤ Real.exp (4 * delta * Real.sqrt (m : ℝ)) :=
        Real.one_le_exp_iff.2 (by positivity)
      exact hP.trans (by nlinarith [mul_le_mul hK hE (by norm_num) (by linarith : 0 ≤ K)])

end Shao.Probability
