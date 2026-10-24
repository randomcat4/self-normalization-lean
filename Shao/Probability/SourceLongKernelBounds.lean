import Shao.Probability.SourceFutureNoiseOddEven
import Shao.Probability.QuadraticCharacteristicOddPower
import Shao.Probability.QuadraticFullNoiseHighFrequency
import Shao.Probability.SourceKernelMarkedOutside
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Full-space early and long-time estimates for the actual conditional-law
future/noise kernel. The absolute smallness threshold pays both outside-v
nonstationarity and the early remaining-clock guard. -/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped Topology ContDiff

private lemma gaussian_moment_integrable (k : ℕ) (T : ℝ) (hT : 0 < T) :
    Integrable (fun u : ℝ => |u| ^ k * Real.exp (-T * u ^ 2 / 256)) := by
  have hi := (integrable_rpow_mul_exp_neg_mul_sq
    (b := T / 256) (by positivity) (s := (k : ℝ))
    (by linarith [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k])).norm
  convert hi using 1
  funext u
  rw [Real.rpow_natCast, Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_pos (Real.exp_pos _)]
  congr 2
  ring

private lemma gaussian_moment_scale (k : ℕ) (T : ℝ) (hT : 0 < T) :
    (∫ u : ℝ, |u| ^ k * Real.exp (-T * u ^ 2 / 256)) =
      (∫ u : ℝ, |u| ^ k * Real.exp (-u ^ 2 / 256)) /
        (Real.sqrt T) ^ (k + 1) := by
  let t := Real.sqrt T
  have ht : 0 < t := Real.sqrt_pos.mpr hT
  have ht2 : t ^ 2 = T := Real.sq_sqrt hT.le
  let g : ℝ → ℝ := fun u => |u| ^ k * Real.exp (-u ^ 2 / 256)
  have he (u : ℝ) : |u| ^ k * Real.exp (-T * u ^ 2 / 256) =
      (t ^ k)⁻¹ * g (t * u) := by
    dsimp [g]
    rw [abs_mul, abs_of_pos ht, mul_pow,
      show -(t * u) ^ 2 / 256 = -T * u ^ 2 / 256 by rw [mul_pow, ht2]; ring]
    field_simp
  simp_rw [he]
  rw [integral_const_mul, Measure.integral_comp_mul_left]
  rw [abs_of_pos (inv_pos.mpr ht), smul_eq_mul]
  change _ = (∫ u : ℝ, g u) / t ^ (k + 1)
  rw [pow_succ]
  field_simp

private lemma gaussian_moments_budget :
    ∃ G : ℝ, 0 < G ∧ ∀ (T : ℝ), 0 < T → ∀ k : ℕ, 2 ≤ k → k ≤ 4 →
      (∫ u : ℝ, |u| ^ k * Real.exp (-T * u ^ 2 / 256)) ≤
        G / (Real.sqrt T) ^ (k + 1) := by
  let J : ℕ → ℝ := fun k => ∫ u : ℝ, |u| ^ k * Real.exp (-u ^ 2 / 256)
  have hJ (k : ℕ) : 0 ≤ J k := integral_nonneg fun u => by dsimp; positivity
  let G := J 2 + J 3 + J 4 + 1
  refine ⟨G, by dsimp [G]; linarith [hJ 2, hJ 3, hJ 4], ?_⟩
  intro T hT k hk hk4
  rw [gaussian_moment_scale k T hT]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases this with rfl | rfl | rfl <;> dsimp [G] <;>
    linarith [hJ 2, hJ 3, hJ 4]

private noncomputable def tailProfile (p : ℕ) (a u : ℝ) : ℝ :=
  1 / (1 + |u| / a) ^ p

private lemma tailProfile_nonneg (p : ℕ) (a u : ℝ) (ha : 0 < a) :
    0 ≤ tailProfile p a u := by unfold tailProfile; positivity

private lemma tailProfile_two_integrable : Integrable (tailProfile 2 1) := by
  have hi := (integrable_one_add_norm (E := ℝ) (μ := (volume : Measure ℝ))
    (r := 2) (by norm_num))
  convert hi using 1
  funext u
  simp only [tailProfile, div_one, Real.norm_eq_abs]
  rw [Real.rpow_neg (by positivity), Real.rpow_two, one_div]

private lemma tailProfile_compare (p : ℕ) (hp : 2 ≤ p) (a u : ℝ) (ha : 0 < a) :
    tailProfile p a u ≤ tailProfile 2 a u := by
  have hbase : 1 ≤ 1 + |u| / a := le_add_of_nonneg_right (by positivity)
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ hbase hp)

private lemma tailProfile_budget :
    ∃ P : ℝ, 0 < P ∧ ∀ (a : ℝ), 0 < a → ∀ p : ℕ, 2 ≤ p →
      Integrable (tailProfile p a) ∧ (∫ u : ℝ, tailProfile p a u) ≤ P * a := by
  let J : ℝ := ∫ u : ℝ, tailProfile 2 1 u
  have hJ : 0 ≤ J := integral_nonneg fun u => tailProfile_nonneg 2 1 u (by norm_num)
  refine ⟨J + 1, by linarith, ?_⟩
  intro a ha p hp
  have he (u : ℝ) : tailProfile 2 a u = tailProfile 2 1 (u / a) := by
    simp only [tailProfile, abs_div, abs_of_pos ha, div_one]
  have hi : Integrable (tailProfile 2 a) := by
    convert tailProfile_two_integrable.comp_div ha.ne' using 1
    funext u
    exact he u
  have hip : Integrable (tailProfile p a) := hi.mono'
    (show Measurable (tailProfile p a) by unfold tailProfile; fun_prop).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (tailProfile_nonneg p a u ha)]
      exact tailProfile_compare p hp a u ha)
  refine ⟨hip, ?_⟩
  calc
    _ ≤ ∫ u : ℝ, tailProfile 2 a u := integral_mono hip hi
      (fun u => tailProfile_compare p hp a u ha)
    _ = a * J := by
      simp_rw [he, div_eq_mul_inv]
      rw [Measure.integral_comp_inv_mul_right, abs_of_pos ha, smul_eq_mul]
    _ ≤ (J + 1) * a := by nlinarith

private lemma inverse_power_tail_majorant (p : ℕ) (a u : ℝ) (ha : 0 < a)
    (hu : a ≤ |u|) :
    1 / |u| ^ p ≤ (2 : ℝ) ^ p / a ^ p * tailProfile p a u := by
  have hu0 : 0 < |u| := ha.trans_le hu
  have hb : a * (1 + |u| / a) ≤ 2 * |u| := by
    rw [mul_add, mul_one, mul_div_cancel₀ _ ha.ne']
    linarith
  have hpow := pow_le_pow_left₀ (by positivity) hb p
  rw [mul_pow, mul_pow] at hpow
  calc
    _ ≤ (2 : ℝ) ^ p / (a ^ p * (1 + |u| / a) ^ p) :=
      (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hpow)
    _ = _ := by unfold tailProfile; ring

private lemma actual_mark_linear_budget :
    ∃ A : ℝ, 0 < A ∧ ∀ y u : ℝ, 0 ≤ y →
      Integrable (fun v : ℝ => ‖sourceMarkSine sourceKernelCutoff y u 0 v‖) ∧
      Integrable (fun v : ℝ => |v| * ‖sourceMarkSine sourceKernelCutoff y u 0 v‖) ∧
      (∫ v : ℝ, ‖sourceMarkSine sourceKernelCutoff y u 0 v‖) ≤ A * y * |u| ∧
      (∫ v : ℝ, |v| * ‖sourceMarkSine sourceKernelCutoff y u 0 v‖) ≤
        A * (1 + y * |u|) * y * |u| := by
  obtain ⟨C, hC, hb⟩ := sourceMarkSine_norms (1 / 16) 4 (by norm_num) (by norm_num)
  obtain ⟨M, hM, hf⟩ := sourceKernel_marked_amplitude_family
  have hc := hf 0 (Or.inl rfl) 0 (by norm_num)
  simp only [pow_zero, div_one] at hc
  have hB (r : ℝ) : |sourceKernelCutoff r| ≤ M ∧
      |deriv sourceKernelCutoff r| ≤ M ∧
      |deriv (deriv sourceKernelCutoff) r| ≤ M := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [iteratedDeriv_zero] using hc.2.2 0 (by norm_num) r
    · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hc.2.2 1 (by norm_num) r
    · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hc.2.2 2 (by norm_num) r
  refine ⟨C * M, mul_pos hC hM, ?_⟩
  intro y u hy
  obtain ⟨hi, hvi, h0, h1⟩ := hb M hM.le sourceKernelCutoff hc.1 hc.2.1 hB
    y u 0 hy (by simpa using div_nonneg hy (by norm_num : (0 : ℝ) ≤ 16))
  refine ⟨hi, hvi, ?_, ?_⟩
  · calc
      _ ≤ C * M * (y * |u|) := h0.trans
        (mul_le_mul_of_nonneg_left (min_le_left _ _) (mul_pos hC hM).le)
      _ = _ := by ring
  · calc
      _ ≤ C * M * (1 + y * |u|) * (y * |u|) := h1.trans
        (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity))
      _ = _ := by ring

private lemma actual_mark_outside_budget :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ (1 / 16 : ℝ) ∧
      ∀ a y u : ℝ, 0 < a → 0 ≤ y → y ≤ 2 → a * y ≤ δ →
        (∫ v in {v : ℝ | |u| / a < |v|},
          ‖sourceMarkSine sourceKernelCutoff y u 0 v‖) ≤
            C * y * |u| * tailProfile 31 a u := by
  obtain ⟨C, δ, hC, hδ, hδ16, hb⟩ := sourceKernel_marked_outside_norms
  refine ⟨C, δ, hC, hδ, hδ16, ?_⟩
  intro a y u ha hy hy2 hay
  have h := (hb 0 (Or.inl rfl) 0 (by norm_num) a y u 0 ha hy hy2 hay
    (by simpa using div_nonneg hy (by norm_num : (0 : ℝ) ≤ 16))).2.2.2.2.2.2.1
  simp only [pow_zero, div_one] at h
  change (∫ v in {v : ℝ | |u| / a < |v|},
    ‖sourceMarkSine sourceKernelCutoff y u 0 v‖) ≤
      C * min (y * |u|) 1 / (1 + |u| / a) ^ 31 at h
  calc
    _ ≤ C * (y * |u|) / (1 + |u| / a) ^ 31 := h.trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (min_le_left _ _) hC.le) (by positivity))
    _ = _ := by unfold tailProfile; ring

private noncomputable def oddSpectrum (ν : Measure ℝ) (m : ℕ) (u v : ℝ) : ℂ :=
  ((quadraticChar ν u v) ^ m - (quadraticChar ν (-u) v) ^ m) / 2 *
    quadraticFullNoiseChar ν u v

private noncomputable def evenSpectrum (ν : Measure ℝ) (m : ℕ) (u v : ℝ) : ℂ :=
  ((quadraticChar ν u v) ^ m + (quadraticChar ν (-u) v) ^ m) / 2 *
    quadraticFullNoiseChar ν u v

private lemma half_spectra_bound (z z' X : ℂ) (B : ℝ)
    (hz : ‖z * X‖ ≤ B) (hz' : ‖z' * X‖ ≤ B) :
    ‖(z - z') / 2 * X‖ ≤ B ∧ ‖(z + z') / 2 * X‖ ≤ B := by
  have he : (z - z') / 2 * X = (z * X - z' * X) / 2 := by ring
  have he' : (z + z') / 2 * X = (z * X + z' * X) / 2 := by ring
  rw [he, he', norm_div, norm_div]
  norm_num only [Complex.norm_ofNat]
  constructor
  · have h := norm_sub_le (z * X) (z' * X)
    linarith
  · have h := norm_add_le (z * X) (z' * X)
    linarith

private lemma actual_spectra_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν) (h : ℝ) (hh : 0 < h)
    (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) (m : ℕ) (u v : ℝ) :
    ‖oddSpectrum ν m u v‖ ≤ 1 ∧ ‖evenSpectrum ν m u v‖ ≤ 1 := by
  apply half_spectra_bound
  all_goals
    rw [norm_mul, norm_pow]
    calc
      _ ≤ 1 * ‖quadraticFullNoiseChar ν u v‖ := mul_le_mul_of_nonneg_right
        (pow_le_one₀ (norm_nonneg _) (norm_quadraticChar_le_one _ _ _)) (norm_nonneg _)
      _ ≤ 1 := by simpa only [one_mul] using
        (quadraticFullNoiseChar_product ν h3 hV h hh hs u v).2.2.2

private lemma actual_spectra_low_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν) (h : ℝ) (hh : 0 < h)
    (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) (n m : ℕ) (hmn : m ≤ n) (hm6 : 6 ≤ m)
    (hscale : (3 / 4 : ℝ) ≤ (n : ℝ) * ∫ a : ℝ, a ^ 2 ∂ν)
    (hbias : (n : ℝ) * |∫ a : ℝ, a ∂ν| ≤ 1)
    (hcomp : (∫ a : ℝ, a ^ 2 ∂ν) ≤ 4 * variance (id : ℝ → ℝ) ν)
    (u v : ℝ)
    (hu : |u| ≤ (1 / 128 : ℝ) /
      ((∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν))
    (hv : |v| ≤ (1 / 128 : ℝ) * |u| /
      ((∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν)) :
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    let T : ℝ := (m : ℝ) * m2
    let E : ℝ := Real.exp (-T * u ^ 2 / 256)
    ‖oddSpectrum ν m u v‖ ≤ E *
      ((m : ℝ) * |μ| * |u| + (m : ℝ) * m3 * (|u| ^ 3 + |u| * |v|)) ∧
      ‖evenSpectrum ν m u v‖ ≤ E := by
  dsimp only
  have hX := (quadraticFullNoiseChar_product ν h3 hV h hh hs u v).2.2.2
  constructor
  · have hodd := (quadraticChar_odd_power_lowFrequency_normalized ν h3 hV n m hmn hm6
      hscale hbias hcomp u v hu hv).1
    dsimp only at hodd
    rw [oddSpectrum, norm_mul, norm_div, Complex.norm_ofNat]
    calc
      _ ≤ ‖(quadraticChar ν u v) ^ m - (quadraticChar ν (-u) v) ^ m‖ / 2 :=
        mul_le_of_le_one_right (by positivity) hX
      _ ≤ _ := by linarith only [hodd]
  · obtain ⟨hplus, hminus⟩ := quadraticChar_lowFrequency_damping ν h3 hV u v hu hv
    have hraw (z : ℂ)
        (hz : ‖z‖ ≤ Real.exp (-(variance (id : ℝ → ℝ) ν) * u ^ 2 / 32)) :
        ‖z ^ m * quadraticFullNoiseChar ν u v‖ ≤
          Real.exp (-((m : ℝ) * ∫ a : ℝ, a ^ 2 ∂ν) * u ^ 2 / 256) := by
      rw [norm_mul, norm_pow]
      calc
        _ ≤ ‖z‖ ^ m := mul_le_of_le_one_right (by positivity) hX
        _ ≤ (Real.exp (-(variance (id : ℝ → ℝ) ν) * u ^ 2 / 32)) ^ m :=
          pow_le_pow_left₀ (norm_nonneg _) hz m
        _ = Real.exp ((m : ℝ) * (-(variance (id : ℝ → ℝ) ν) * u ^ 2 / 32)) :=
          (Real.exp_nat_mul _ _).symm
        _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          have hc := mul_le_mul_of_nonneg_left hcomp
            (mul_nonneg (Nat.cast_nonneg m) (sq_nonneg u))
          nlinarith only [hc, mul_nonneg (Nat.cast_nonneg m) hV.le,
            mul_nonneg (mul_nonneg (Nat.cast_nonneg m) hV.le) (sq_nonneg u)]
    exact (half_spectra_bound _ _ _ _ (hraw _ hplus) (hraw _ hminus)).2

private lemma weighted_profile (p k : ℕ) (hk : k ≤ p) (a u : ℝ) (ha : 0 < a) :
    |u| ^ k * tailProfile p a u ≤ a ^ k * tailProfile (p - k) a u := by
  have hd : 0 < 1 + |u| / a := by positivity
  have he : a * (1 + |u| / a) = a + |u| := by
    rw [mul_add, mul_one, mul_div_cancel₀ _ ha.ne']
  have hpow : |u| ^ k ≤ a ^ k * (1 + |u| / a) ^ k := by
    rw [← mul_pow, he]
    exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) k
  unfold tailProfile
  calc
    _ ≤ (a ^ k * (1 + |u| / a) ^ k) * (1 / (1 + |u| / a) ^ p) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = _ := by
      rw [show (1 + |u| / a) ^ p =
        (1 + |u| / a) ^ k * (1 + |u| / a) ^ (p - k) by
          rw [← pow_add, Nat.add_sub_of_le hk]]
      field_simp

private lemma weighted_profile_high (p k : ℕ) (hk : k ≤ p)
    (a u : ℝ) (ha : 0 < a) (hu : u ≠ 0) :
    |u| ^ k * tailProfile p a u ≤ a ^ p / |u| ^ (p - k) := by
  have hu0 : 0 < |u| := abs_pos.mpr hu
  have hd : 0 < 1 + |u| / a := by positivity
  have hb : |u| ≤ a * (1 + |u| / a) := by
    rw [mul_add, mul_one, mul_div_cancel₀ _ ha.ne']
    linarith
  have hpow := pow_le_pow_left₀ hu0.le hb p
  rw [mul_pow] at hpow
  have he : tailProfile p a u ≤ a ^ p / |u| ^ p := by
    unfold tailProfile
    exact (div_le_div_iff₀ (pow_pos hd _) (pow_pos hu0 _)).mpr (by simpa using hpow)
  calc
    _ ≤ |u| ^ k * (a ^ p / |u| ^ p) :=
      mul_le_mul_of_nonneg_left he (pow_nonneg hu0.le _)
    _ = _ := by
      rw [show |u| ^ p = |u| ^ k * |u| ^ (p - k) by
        rw [← pow_add, Nat.add_sub_of_le hk]]
      field_simp

private lemma mark_slice_comparison (G : ℝ → ℂ) (hG : Integrable G)
    (y u R A0 A1 L : ℝ) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hL : 0 ≤ L)
    (hmark : Integrable (fun v : ℝ => ‖sourceMarkSine sourceKernelCutoff y u 0 v‖))
    (hvmark : Integrable (fun v : ℝ => |v| * ‖sourceMarkSine sourceKernelCutoff y u 0 v‖))
    (hglob : ∀ v, ‖G v‖ ≤ L * ‖sourceMarkSine sourceKernelCutoff y u 0 v‖)
    (hlow : ∀ v, |v| ≤ R → ‖G v‖ ≤
      ‖sourceMarkSine sourceKernelCutoff y u 0 v‖ * (A0 + A1 * |v|)) :
    (∫ v : ℝ, ‖G v‖) ≤
      A0 * (∫ v : ℝ, ‖sourceMarkSine sourceKernelCutoff y u 0 v‖) +
      A1 * (∫ v : ℝ, |v| * ‖sourceMarkSine sourceKernelCutoff y u 0 v‖) +
      L * (∫ v in {v : ℝ | R < |v|}, ‖sourceMarkSine sourceKernelCutoff y u 0 v‖) := by
  let b : ℝ → ℝ := fun v => ‖sourceMarkSine sourceKernelCutoff y u 0 v‖
  let S : Set ℝ := {v : ℝ | R < |v|}
  have hS : MeasurableSet S := (isOpen_lt continuous_const continuous_abs).measurableSet
  have henv : Integrable (fun v => A0 * b v + A1 * (|v| * b v) + L * S.indicator b v) :=
    ((hmark.const_mul A0).add (hvmark.const_mul A1)).add
      ((hmark.indicator hS).const_mul L)
  calc
    _ ≤ ∫ v : ℝ, A0 * b v + A1 * (|v| * b v) + L * S.indicator b v :=
      integral_mono hG.norm henv (fun v => by
        by_cases hv : v ∈ S
        · rw [Set.indicator_of_mem hv]
          have hb : 0 ≤ b v := norm_nonneg _
          have h0 := mul_nonneg hA0 hb
          have h1 := mul_nonneg hA1 (mul_nonneg (abs_nonneg v) hb)
          linarith [hglob v]
        · rw [Set.indicator_of_notMem hv]
          have hvl : |v| ≤ R := le_of_not_gt hv
          have he := hlow v hvl
          dsimp only [b] at *
          nlinarith only [he])
    _ = _ := by
      calc
        _ = (∫ v : ℝ, A0 * b v + A1 * (|v| * b v)) +
            (∫ v : ℝ, L * S.indicator b v) :=
          integral_add ((hmark.const_mul A0).add (hvmark.const_mul A1))
            ((hmark.indicator hS).const_mul L)
        _ = (∫ v : ℝ, A0 * b v) + (∫ v : ℝ, A1 * (|v| * b v)) +
            (∫ v : ℝ, L * S.indicator b v) := by
          rw [integral_add (hmark.const_mul A0) (hvmark.const_mul A1)]
        _ = _ := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_indicator hS]

private lemma four_region_slice_bound (G : ℝ → ℂ) (hG : Integrable G)
    (j : ℕ) (hj : 1 ≤ j) (hj2 : j ≤ 2)
    (A D a b c y u L0 L1 H0 : ℝ)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hy : 0 ≤ y) (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hH0 : 0 ≤ H0)
    (hm : Integrable (fun v : ℝ => ‖sourceMarkSine sourceKernelCutoff y u 0 v‖))
    (hvm : Integrable (fun v : ℝ => |v| * ‖sourceMarkSine sourceKernelCutoff y u 0 v‖))
    (hm0 : (∫ v : ℝ, ‖sourceMarkSine sourceKernelCutoff y u 0 v‖) ≤ A * y * |u|)
    (hm1 : (∫ v : ℝ, |v| * ‖sourceMarkSine sourceKernelCutoff y u 0 v‖) ≤
      A * (1 + y * |u|) * y * |u|)
    (hoa : (∫ v in {v : ℝ | |u| / a < |v|},
      ‖sourceMarkSine sourceKernelCutoff y u 0 v‖) ≤ D * y * |u| * tailProfile 31 a u)
    (hoc : (∫ v in {v : ℝ | |u| / c < |v|},
      ‖sourceMarkSine sourceKernelCutoff y u 0 v‖) ≤ D * y * |u| * tailProfile 31 c u)
    (hglob : ∀ v, ‖G v‖ ≤ |u| ^ (j - 1) * ‖sourceMarkSine sourceKernelCutoff y u 0 v‖)
    (hlow : |u| ≤ b → ∀ v, |v| ≤ |u| / a →
      ‖G v‖ ≤ ‖sourceMarkSine sourceKernelCutoff y u 0 v‖ *
        (|u| ^ (j - 1) * L0 + |u| ^ (j - 1) * L1 * |v|))
    (hhigh : b ≤ |u| → ∀ v, |v| ≤ |u| / c →
      ‖G v‖ ≤ ‖sourceMarkSine sourceKernelCutoff y u 0 v‖ *
        (|u| ^ (j - 1) * H0 / |u| ^ 12)) :
    (∫ v : ℝ, ‖G v‖) ≤
      A * y * |u| ^ j * (L0 + L1 * (1 + y * |u|)) +
      A * y * H0 * ((2 : ℝ) ^ (12 - j) / b ^ (12 - j)) * tailProfile (12 - j) b u +
      D * y * a ^ j * tailProfile (31 - j) a u +
      D * y * c ^ 31 * ((2 : ℝ) ^ (31 - j) / b ^ (31 - j)) * tailProfile (31 - j) b u := by
  have hup : |u| ^ (j - 1) * |u| = |u| ^ j := by
    rw [← pow_succ, Nat.sub_add_cancel hj]
  have hp31 : j ≤ 31 := by omega
  have hp12 : j ≤ 12 := by omega
  have n0 : 0 ≤ A * y * |u| ^ j * (L0 + L1 * (1 + y * |u|)) := by positivity
  have n1 : 0 ≤ A * y * H0 * ((2 : ℝ) ^ (12 - j) / b ^ (12 - j)) *
      tailProfile (12 - j) b u := by
    exact mul_nonneg (by positivity) (tailProfile_nonneg _ _ _ hb)
  have n2 : 0 ≤ D * y * a ^ j * tailProfile (31 - j) a u :=
    mul_nonneg (by positivity) (tailProfile_nonneg _ _ _ ha)
  have n3 : 0 ≤ D * y * c ^ 31 * ((2 : ℝ) ^ (31 - j) / b ^ (31 - j)) *
      tailProfile (31 - j) b u :=
    mul_nonneg (by positivity) (tailProfile_nonneg _ _ _ hb)
  by_cases hu : |u| ≤ b
  · have hslice := mark_slice_comparison G hG y u (|u| / a)
      (|u| ^ (j - 1) * L0) (|u| ^ (j - 1) * L1) (|u| ^ (j - 1))
      (by positivity) (by positivity) (by positivity) hm hvm hglob (hlow hu)
    have hbnd : (∫ v : ℝ, ‖G v‖) ≤
        A * y * |u| ^ j * (L0 + L1 * (1 + y * |u|)) +
          D * y * (|u| ^ j * tailProfile 31 a u) := by
      calc
        _ ≤ (|u| ^ (j - 1) * L0) * (A * y * |u|) +
            (|u| ^ (j - 1) * L1) * (A * (1 + y * |u|) * y * |u|) +
            |u| ^ (j - 1) * (D * y * |u| * tailProfile 31 a u) := by
          apply hslice.trans
          gcongr
        _ = _ := by rw [← hup]; ring
    have ho := mul_le_mul_of_nonneg_left (weighted_profile 31 j hp31 a u ha)
      (mul_nonneg hD hy)
    nlinarith only [hbnd, ho, n1, n3]
  · have hub : b ≤ |u| := (lt_of_not_ge hu).le
    have hu0 : u ≠ 0 := by intro hz; simpa [hz] using (hb.trans_le hub).ne'
    have hua : 0 < |u| := abs_pos.mpr hu0
    have hslice := mark_slice_comparison G hG y u (|u| / c)
      (|u| ^ (j - 1) * H0 / |u| ^ 12) 0 (|u| ^ (j - 1))
      (by positivity) le_rfl (by positivity) hm hvm hglob
      (fun v hv => by simpa only [zero_mul, add_zero] using hhigh hub v hv)
    have hbnd : (∫ v : ℝ, ‖G v‖) ≤
        A * y * H0 * (1 / |u| ^ (12 - j)) +
          D * y * (|u| ^ j * tailProfile 31 c u) := by
      calc
        _ ≤ (|u| ^ (j - 1) * H0 / |u| ^ 12) * (A * y * |u|) +
            0 * (∫ v : ℝ, |v| * ‖sourceMarkSine sourceKernelCutoff y u 0 v‖) +
            |u| ^ (j - 1) * (D * y * |u| * tailProfile 31 c u) := by
          apply hslice.trans
          gcongr
        _ = _ := by
          have hpow : |u| ^ 12 = |u| ^ j * |u| ^ (12 - j) := by
            rw [← pow_add, Nat.add_sub_of_le hp12]
          rw [hpow, ← hup]
          field_simp
          ring
    have hmain := mul_le_mul_of_nonneg_left (inverse_power_tail_majorant (12 - j) b u hb hub)
      (by positivity : 0 ≤ A * y * H0)
    have hout1 := weighted_profile_high 31 j hp31 c u hc hu0
    have hout2 := mul_le_mul_of_nonneg_left (inverse_power_tail_majorant (31 - j) b u hb hub)
      (by positivity : 0 ≤ c ^ 31)
    have hout := mul_le_mul_of_nonneg_left (hout1.trans (by simpa only [div_eq_mul_inv,
      one_mul, mul_assoc] using hout2)) (mul_nonneg hD hy)
    calc
      _ ≤ A * y * H0 * ((2 : ℝ) ^ (12 - j) / b ^ (12 - j)) *
          tailProfile (12 - j) b u +
          D * y * c ^ 31 * ((2 : ℝ) ^ (31 - j) / b ^ (31 - j)) *
            tailProfile (31 - j) b u := hbnd.trans (add_le_add
              (by simpa only [mul_assoc] using hmain)
              (by convert hout using 1 <;> ring))
      _ ≤ _ := by linarith only [n0, n2]

private lemma four_region_integral_bound
    (H : (ℝ × ℝ) → ℂ) (hH : Integrable H)
    (j : ℕ) (hj : 1 ≤ j) (hj2 : j ≤ 2)
    (A D P a b c y H0 : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hy : 0 ≤ y) (hH0 : 0 ≤ H0)
    (hprof : ∀ d : ℝ, 0 < d → ∀ p : ℕ, 2 ≤ p →
      Integrable (tailProfile p d) ∧ (∫ u : ℝ, tailProfile p d u) ≤ P * d)
    (L : ℝ → ℝ) (hL : Integrable L)
    (hslice : ∀ᵐ u : ℝ, (∫ v : ℝ, ‖H (u, v)‖) ≤ L u +
      A * y * H0 * ((2 : ℝ) ^ (12 - j) / b ^ (12 - j)) * tailProfile (12 - j) b u +
      D * y * a ^ j * tailProfile (31 - j) a u +
      D * y * c ^ 31 * ((2 : ℝ) ^ (31 - j) / b ^ (31 - j)) * tailProfile (31 - j) b u) :
    ‖∫ ξ : ℝ × ℝ, H ξ‖ ≤ (∫ u : ℝ, L u) +
      A * y * H0 * ((2 : ℝ) ^ (12 - j) / b ^ (12 - j)) * (P * b) +
      D * y * a ^ j * (P * a) +
      D * y * c ^ 31 * ((2 : ℝ) ^ (31 - j) / b ^ (31 - j)) * (P * b) := by
  have hp12 : 2 ≤ 12 - j := by omega
  have hp31 : 2 ≤ 31 - j := by omega
  obtain ⟨h1, hb1⟩ := hprof b hb (12 - j) hp12
  obtain ⟨h2, hb2⟩ := hprof a ha (31 - j) hp31
  obtain ⟨h3, hb3⟩ := hprof b hb (31 - j) hp31
  let K1 := A * y * H0 * ((2 : ℝ) ^ (12 - j) / b ^ (12 - j))
  let K2 := D * y * a ^ j
  let K3 := D * y * c ^ 31 * ((2 : ℝ) ^ (31 - j) / b ^ (31 - j))
  have hE := ((hL.add (h1.const_mul K1)).add (h2.const_mul K2)).add (h3.const_mul K3)
  rw [Measure.volume_eq_prod ℝ ℝ] at hH ⊢
  calc
    _ ≤ ∫ ξ : ℝ × ℝ, ‖H ξ‖ ∂(volume.prod volume) := norm_integral_le_integral_norm _
    _ = ∫ u : ℝ, ∫ v : ℝ, ‖H (u, v)‖ := integral_prod _ hH.norm
    _ ≤ ∫ u : ℝ, L u + K1 * tailProfile (12 - j) b u +
        K2 * tailProfile (31 - j) a u + K3 * tailProfile (31 - j) b u :=
      integral_mono_ae hH.norm.integral_prod_left hE hslice
    _ = (∫ u : ℝ, L u) + K1 * (∫ u : ℝ, tailProfile (12 - j) b u) +
        K2 * (∫ u : ℝ, tailProfile (31 - j) a u) +
        K3 * (∫ u : ℝ, tailProfile (31 - j) b u) := by
      have e3 := integral_add ((hL.add (h1.const_mul K1)).add (h2.const_mul K2))
        (h3.const_mul K3)
      have e2 := integral_add (hL.add (h1.const_mul K1)) (h2.const_mul K2)
      have e1 := integral_add hL (h1.const_mul K1)
      simp only [Pi.add_apply] at e1 e2 e3
      rw [e3, e2, e1]
      simp only [integral_const_mul]
    _ ≤ _ := by
      dsimp only [K1, K2, K3]
      gcongr

private lemma gaussian_low_envelopes (G A y M0 M3 T : ℝ)
    (hG : ∀ k : ℕ, 2 ≤ k → k ≤ 4 →
      (∫ u : ℝ, |u| ^ k * Real.exp (-T * u ^ 2 / 256)) ≤
        G / (Real.sqrt T) ^ (k + 1))
    (hA : 0 ≤ A) (hy : 0 ≤ y) (hM0 : 0 ≤ M0) (hM3 : 0 ≤ M3) (hT : 0 < T) :
    let E : ℝ → ℝ := fun u => Real.exp (-T * u ^ 2 / 256)
    let Lo : ℝ → ℝ := fun u => A * y * |u| *
      (E u * (M0 * |u| + M3 * |u| ^ 3) + E u * M3 * |u| * (1 + y * |u|))
    let Le : ℝ → ℝ := fun u => A * y * |u| ^ 2 * E u
    Integrable Lo ∧ Integrable Le ∧
      (∫ u : ℝ, Lo u) ≤ A * y * G *
        (M0 / (Real.sqrt T) ^ 3 + M3 * (1 / (Real.sqrt T) ^ 5 +
          1 / (Real.sqrt T) ^ 3 + y / (Real.sqrt T) ^ 4)) ∧
      (∫ u : ℝ, Le u) ≤ A * y * G / (Real.sqrt T) ^ 3 := by
  let J : ℕ → ℝ → ℝ := fun k u => |u| ^ k * Real.exp (-T * u ^ 2 / 256)
  have hi (k : ℕ) : Integrable (J k) := gaussian_moment_integrable k T hT
  have h2 := hG 2 (by norm_num) (by norm_num)
  have h3 := hG 3 (by norm_num) (by norm_num)
  have h4 := hG 4 (by norm_num) (by norm_num)
  norm_num only at h2 h3 h4
  dsimp only
  have he (u : ℝ) : A * y * |u| *
      (Real.exp (-T * u ^ 2 / 256) * (M0 * |u| + M3 * |u| ^ 3) +
        Real.exp (-T * u ^ 2 / 256) * M3 * |u| * (1 + y * |u|)) =
      A * y * M0 * J 2 u + A * y * M3 * J 4 u +
        A * y * M3 * J 2 u + A * y * M3 * y * J 3 u := by dsimp [J]; ring
  have hLo := (((hi 2).const_mul (A * y * M0)).add
    ((hi 4).const_mul (A * y * M3))).add ((hi 2).const_mul (A * y * M3))
  have hLo' := hLo.add ((hi 3).const_mul (A * y * M3 * y))
  have hLei : Integrable (fun u => A * y * |u| ^ 2 * Real.exp (-T * u ^ 2 / 256)) := by
    convert (hi 2).const_mul (A * y) using 1
    funext u
    dsimp [J]
    ring
  have hLoi : Integrable (fun u => A * y * |u| *
      (Real.exp (-T * u ^ 2 / 256) * (M0 * |u| + M3 * |u| ^ 3) +
        Real.exp (-T * u ^ 2 / 256) * M3 * |u| * (1 + y * |u|))) := by
    convert hLo' using 1
    funext u
    exact he u
  refine ⟨hLoi, hLei, ?_, ?_⟩
  · have e1 := integral_add ((hi 2).const_mul (A * y * M0)) ((hi 4).const_mul (A * y * M3))
    have e2 := integral_add (((hi 2).const_mul (A * y * M0)).add
      ((hi 4).const_mul (A * y * M3))) ((hi 2).const_mul (A * y * M3))
    have e3 := integral_add hLo ((hi 3).const_mul (A * y * M3 * y))
    simp only [Pi.add_apply] at e1 e2 e3
    calc
      _ = A * y * M0 * (∫ u : ℝ, J 2 u) + A * y * M3 * (∫ u : ℝ, J 4 u) +
          A * y * M3 * (∫ u : ℝ, J 2 u) + A * y * M3 * y * (∫ u : ℝ, J 3 u) := by
        simp_rw [he]
        rw [e3, e2, e1]
        simp only [integral_const_mul]
      _ ≤ A * y * M0 * (G / (Real.sqrt T) ^ 3) +
          A * y * M3 * (G / (Real.sqrt T) ^ 5) +
          A * y * M3 * (G / (Real.sqrt T) ^ 3) +
          A * y * M3 * y * (G / (Real.sqrt T) ^ 4) := by gcongr
      _ = _ := by ring
  · calc
      _ = A * y * (∫ u : ℝ, J 2 u) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun u => by dsimp [J]; ring
      _ ≤ A * y * (G / (Real.sqrt T) ^ 3) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hA hy)
      _ = _ := by ring

private noncomputable def kernelMarkIntegrand (k : ℕ) (F : (ℝ × ℝ) → ℂ)
    (y w q : ℝ) (ξ : ℝ × ℝ) : ℂ :=
  Complex.exp (((ξ.2 * q : ℝ) : ℂ) * Complex.I) *
    (Real.cos (ξ.1 * w) : ℂ) * sourceMarkSine sourceKernelCutoff y ξ.1 0 ξ.2 *
      (ξ.1 : ℂ) ^ k * F ξ

private lemma kernelMarkIntegrand_norm (k : ℕ) (F : (ℝ × ℝ) → ℂ)
    (y w q u v : ℝ) :
    ‖kernelMarkIntegrand k F y w q (u, v)‖ ≤
      |u| ^ k * ‖sourceMarkSine sourceKernelCutoff y u 0 v‖ * ‖F (u, v)‖ := by
  have he : ‖Complex.exp (((v * q : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  dsimp only [kernelMarkIntegrand]
  rw [norm_mul, norm_mul, norm_mul, norm_mul, he, one_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ 1 * ‖sourceMarkSine sourceKernelCutoff y u 0 v‖ * |u| ^ k * ‖F (u, v)‖ := by
      gcongr
      exact Real.abs_cos_le_one _
    _ = _ := by ring

private lemma kernelMarkIntegrand_bound (k : ℕ) (F : (ℝ × ℝ) → ℂ)
    (y w q u v B : ℝ) (hF : ‖F (u, v)‖ ≤ B) :
    ‖kernelMarkIntegrand k F y w q (u, v)‖ ≤
      ‖sourceMarkSine sourceKernelCutoff y u 0 v‖ * (|u| ^ k * B) := by
  calc
    _ ≤ |u| ^ k * ‖sourceMarkSine sourceKernelCutoff y u 0 v‖ * B :=
      (kernelMarkIntegrand_norm k F y w q u v).trans
        (mul_le_mul_of_nonneg_left hF (by positivity))
    _ = _ := by ring

private lemma actual_kernel_mark_formulas (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν) (h : ℝ) (hh : 0 < h)
    (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) (m : ℕ) (y : ℝ) (hy : 0 ≤ y) (w q : ℝ) :
    let f : ℝ → ℝ := fun r => sourceFutureNoiseKernel ν m y (r, q)
    let o : ℝ → ℝ := fun r => (f r - f (-r)) / 2
    let e : ℝ → ℝ := fun r => (f r + f (-r)) / 2
    let Go : (ℝ × ℝ) → ℂ := kernelMarkIntegrand 0 (fun ξ => oddSpectrum ν m ξ.1 ξ.2) y w q
    let Ge : (ℝ × ℝ) → ℂ := kernelMarkIntegrand 1 (fun ξ => evenSpectrum ν m ξ.1 ξ.2) y w q
    (DifferentiableAt ℝ o w ∧ DifferentiableAt ℝ e w ∧
      DifferentiableAt ℝ (fun r => deriv e r) w) ∧
      Integrable Go ∧ Integrable Ge ∧
      ((deriv o w : ℝ) : ℂ) = (2 * Complex.I / (((2 * Real.pi) ^ 2 : ℝ) : ℂ)) * ∫ ξ, Go ξ ∧
      ((deriv (fun r => deriv e r) w : ℝ) : ℂ) =
        (-2 / (((2 * Real.pi) ^ 2 : ℝ) : ℂ)) * ∫ ξ, Ge ξ := by
  obtain ⟨ho, hGo, heqo⟩ := sourceFutureNoiseKernel_odd_derivative_inverse ν h3 hV h hh hs m y hy w q
  obtain ⟨he, hee, hGe, heqe⟩ := sourceFutureNoiseKernel_even_second_inverse ν h3 hV h hh hs m y hy w q
  exact ⟨⟨ho, he, hee⟩,
    by
      convert hGo using 1
      funext ξ
      simp only [kernelMarkIntegrand, oddSpectrum, pow_zero, mul_one],
    by
      convert hGe using 1
      funext ξ
      simp only [kernelMarkIntegrand, evenSpectrum, pow_one],
    by simpa only [kernelMarkIntegrand, oddSpectrum, pow_zero, mul_one] using heqo,
    by simpa only [kernelMarkIntegrand, evenSpectrum, pow_one] using heqe⟩

private lemma actual_frequency_pair_budgets (Cfull : ℝ) (hCfull : 0 ≤ Cfull) :
    ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧ δ ≤ (1 / 16 : ℝ) ∧
      ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun a : ℝ => |a| ^ 3) ν →
        0 < variance (id : ℝ → ℝ) ν →
        ∀ h : ℝ, 0 < h → (∀ᵐ a : ℝ ∂ν, |a| ≤ h) →
        ∀ n m : ℕ, m ≤ n → 6 ≤ m →
        (3 / 4 : ℝ) ≤ (n : ℝ) * ∫ a : ℝ, a ^ 2 ∂ν →
        (n : ℝ) * |∫ a : ℝ, a ∂ν| ≤ 1 →
        (∫ a : ℝ, a ^ 2 ∂ν) ≤ 4 * variance (id : ℝ → ℝ) ν →
        let μ : ℝ := ∫ a : ℝ, a ∂ν
        let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
        let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
        let γ : ℝ := m3 / variance (id : ℝ → ℝ) ν
        let T : ℝ := (m : ℝ) * m2
        0 < T → 0 < γ → ∀ y : ℝ, 0 ≤ y → y ≤ 2 →
        (128 * γ) * y ≤ δ → (4 * h) * y ≤ δ →
        (∀ u v : ℝ, 1 / (128 * γ) ≤ |u| → |v| ≤ |u| / (4 * h) →
          ‖oddSpectrum ν m u v‖ ≤ Cfull / (T ^ 6 * |u| ^ 12) ∧
          ‖evenSpectrum ν m u v‖ ≤ Cfull / (T ^ 6 * |u| ^ 12)) →
        ∀ w q : ℝ,
          ‖∫ ξ : ℝ × ℝ,
            kernelMarkIntegrand 0 (fun ξ => oddSpectrum ν m ξ.1 ξ.2) y w q ξ‖ ≤
            K * y * ((m : ℝ) * |μ| / (Real.sqrt T) ^ 3 +
              (m : ℝ) * m3 * (1 / (Real.sqrt T) ^ 5 +
                1 / (Real.sqrt T) ^ 3 + y / (Real.sqrt T) ^ 4) +
              γ ^ 2 + γ ^ 10 / T ^ 6 + h ^ 31 * γ ^ 29) ∧
          ‖∫ ξ : ℝ × ℝ,
            kernelMarkIntegrand 1 (fun ξ => evenSpectrum ν m ξ.1 ξ.2) y w q ξ‖ ≤
            K * y * (1 / (Real.sqrt T) ^ 3 + γ ^ 3 +
              γ ^ 9 / T ^ 6 + h ^ 31 * γ ^ 28) := by
  obtain ⟨A, hA, hmark⟩ := actual_mark_linear_budget
  obtain ⟨D, δ, hD, hδ, hδ16, hout⟩ := actual_mark_outside_budget
  obtain ⟨P, hP, hprof⟩ := tailProfile_budget
  obtain ⟨G, hG, hgauss⟩ := gaussian_moments_budget
  let R : ℝ := 2 ^ 31 * 128 ^ 31 * 4 ^ 31
  let S : ℝ := A * G + A * Cfull * P + D * P + 1
  let K : ℝ := R * S
  have hR : 0 < R := by norm_num [R]
  have hAG : 0 ≤ A * G := by positivity
  have hAC : 0 ≤ A * Cfull * P := by positivity
  have hDP : 0 ≤ D * P := by positivity
  have hS : 0 < S := by dsimp [S]; linarith
  have hcoef (z c : ℝ) (hz0 : 0 ≤ z) (hz : z ≤ S) (hc0 : 0 ≤ c) (hc : c ≤ R) :
      z * c ≤ K := by
    calc
      _ ≤ S * R := mul_le_mul hz hc hc0 hS.le
      _ = K := by dsimp [K]; ring
  have c0 : A * G ≤ K := by
    simpa using hcoef (A * G) 1 hAG (by dsimp [S]; linarith) (by norm_num) (by norm_num [R])
  have c1 : A * Cfull * P * 2 ^ 11 * 128 ^ 10 ≤ K := by
    convert hcoef (A * Cfull * P) (2 ^ 11 * 128 ^ 10) hAC
      (by dsimp [S]; linarith) (by positivity) (by norm_num [R]) using 1 <;> ring
  have c2 : D * P * 128 ^ 2 ≤ K := hcoef (D * P) (128 ^ 2) hDP
    (by dsimp [S]; linarith) (by positivity) (by norm_num [R])
  have c3 : D * P * 4 ^ 31 * 2 ^ 30 * 128 ^ 29 ≤ K := by
    convert hcoef (D * P) (4 ^ 31 * 2 ^ 30 * 128 ^ 29) hDP
      (by dsimp [S]; linarith) (by positivity) (by norm_num [R]) using 1 <;> ring
  have c4 : A * Cfull * P * 2 ^ 10 * 128 ^ 9 ≤ K := by
    convert hcoef (A * Cfull * P) (2 ^ 10 * 128 ^ 9) hAC
      (by dsimp [S]; linarith) (by positivity) (by norm_num [R]) using 1 <;> ring
  have c5 : D * P * 128 ^ 3 ≤ K := hcoef (D * P) (128 ^ 3) hDP
    (by dsimp [S]; linarith) (by positivity) (by norm_num [R])
  have c6 : D * P * 4 ^ 31 * 2 ^ 29 * 128 ^ 28 ≤ K := by
    convert hcoef (D * P) (4 ^ 31 * 2 ^ 29 * 128 ^ 28) hDP
      (by dsimp [S]; linarith) (by positivity) (by norm_num [R]) using 1 <;> ring
  refine ⟨K, δ, mul_pos hR hS, hδ, hδ16, ?_⟩
  intro ν hp h3 hV h hh hs n m hmn hm6 hscale hbias hcomp
  dsimp only
  intro hT hγ y hy hy2 hsmallA hsmallC hcone w q
  letI := hp
  let μ : ℝ := ∫ a : ℝ, a ∂ν
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
  let γ : ℝ := m3 / variance (id : ℝ → ℝ) ν
  let T : ℝ := (m : ℝ) * ∫ a : ℝ, a ^ 2 ∂ν
  let b : ℝ := 1 / (128 * γ)
  have hb : 0 < b := by dsimp [b]; positivity
  have hγ0 : 0 < γ := hγ
  have hT0 : 0 < T := hT
  have hm3 : 0 ≤ m3 := integral_nonneg fun a => by positivity
  have hM0 : 0 ≤ (m : ℝ) * |μ| := by positivity
  have hM3 : 0 ≤ (m : ℝ) * m3 := by positivity
  let E : ℝ → ℝ := fun u => Real.exp (-T * u ^ 2 / 256)
  let Lo : ℝ → ℝ := fun u => A * y * |u| *
    (E u * ((m : ℝ) * |μ| * |u| + (m : ℝ) * m3 * |u| ^ 3) +
      E u * ((m : ℝ) * m3) * |u| * (1 + y * |u|))
  let Le : ℝ → ℝ := fun u => A * y * |u| ^ 2 * E u
  have hLoLe := gaussian_low_envelopes G A y ((m : ℝ) * |μ|) ((m : ℝ) * m3) T
    (hgauss T hT0) hA.le hy hM0 hM3 hT0
  let Go : (ℝ × ℝ) → ℂ :=
    kernelMarkIntegrand 0 (fun ξ => oddSpectrum ν m ξ.1 ξ.2) y w q
  let Ge : (ℝ × ℝ) → ℂ :=
    kernelMarkIntegrand 1 (fun ξ => evenSpectrum ν m ξ.1 ξ.2) y w q
  have hf := actual_kernel_mark_formulas ν h3 hV h hh hs m y hy w q
  have hGoi : Integrable Go := hf.2.1
  have hGei : Integrable Ge := hf.2.2.1
  have hGop : Integrable Go (volume.prod volume) := by
    simpa only [← Measure.volume_eq_prod ℝ ℝ] using hGoi
  have hGep : Integrable Ge (volume.prod volume) := by
    simpa only [← Measure.volume_eq_prod ℝ ℝ] using hGei
  have hao : 0 < 128 * γ := by positivity
  have hco : 0 < 4 * h := by positivity
  have hfreq (u : ℝ) : |u| / (128 * γ) = (1 / 128 : ℝ) * |u| / γ := by ring
  have hbdef : b = (1 / 128 : ℝ) / γ := by dsimp [b]; ring
  have hsliceO : ∀ᵐ u : ℝ, (∫ v : ℝ, ‖Go (u, v)‖) ≤ Lo u +
      A * y * (Cfull / T ^ 6) * ((2 : ℝ) ^ 11 / b ^ 11) * tailProfile 11 b u +
      D * y * (128 * γ) * tailProfile 30 (128 * γ) u +
      D * y * (4 * h) ^ 31 * ((2 : ℝ) ^ 30 / b ^ 30) * tailProfile 30 b u := by
    filter_upwards [(integrable_prod_iff hGop.aestronglyMeasurable).mp hGop |>.1] with u hi
    obtain ⟨hmi, hvmi, hm0, hm1⟩ := hmark y u hy
    have hs0 := actual_spectra_le_one ν h3 hV h hh hs m u
    have ht := four_region_slice_bound (fun v => Go (u, v)) hi 1 (by norm_num) (by norm_num)
      A D (128 * γ) b (4 * h) y u
      (E u * ((m : ℝ) * |μ| * |u| + (m : ℝ) * m3 * |u| ^ 3))
      (E u * ((m : ℝ) * m3) * |u|) (Cfull / T ^ 6)
      hA.le hD.le hao hb hco hy (by dsimp [E]; positivity) (by dsimp [E]; positivity)
      (by positivity) hmi hvmi hm0 hm1
      (hout _ _ _ hao hy hy2 hsmallA) (hout _ _ _ hco hy hy2 hsmallC)
      (fun v => by
        simpa only [Go, Nat.reduceSub, pow_zero, one_mul, mul_one, mul_comm] using
          kernelMarkIntegrand_bound 0 (fun ξ => oddSpectrum ν m ξ.1 ξ.2) y w q u v 1 (hs0 v).1)
      (fun hu v hv => by
        have hl := (actual_spectra_low_bounds ν h3 hV h hh hs n m hmn hm6 hscale hbias hcomp u v
          (by simpa only [hbdef] using hu) (by simpa only [hfreq] using hv)).1
        convert kernelMarkIntegrand_bound 0 (fun ξ => oddSpectrum ν m ξ.1 ξ.2) y w q u v _ hl using 1 <;>
          dsimp [Go, E, μ, m3, T] <;> ring)
      (fun hu v hv => by
        convert kernelMarkIntegrand_bound 0 (fun ξ => oddSpectrum ν m ξ.1 ξ.2) y w q u v _
          (hcone u v hu hv).1 using 1 <;> dsimp [Go] <;> ring)
    simpa only [Nat.reduceSub, pow_zero, pow_one, Lo] using ht
  have hsliceE : ∀ᵐ u : ℝ, (∫ v : ℝ, ‖Ge (u, v)‖) ≤ Le u +
      A * y * (Cfull / T ^ 6) * ((2 : ℝ) ^ 10 / b ^ 10) * tailProfile 10 b u +
      D * y * (128 * γ) ^ 2 * tailProfile 29 (128 * γ) u +
      D * y * (4 * h) ^ 31 * ((2 : ℝ) ^ 29 / b ^ 29) * tailProfile 29 b u := by
    filter_upwards [(integrable_prod_iff hGep.aestronglyMeasurable).mp hGep |>.1] with u hi
    obtain ⟨hmi, hvmi, hm0, hm1⟩ := hmark y u hy
    have hs0 := actual_spectra_le_one ν h3 hV h hh hs m u
    have ht := four_region_slice_bound (fun v => Ge (u, v)) hi 2 (by norm_num) (by norm_num)
      A D (128 * γ) b (4 * h) y u (E u) 0 (Cfull / T ^ 6)
      hA.le hD.le hao hb hco hy (Real.exp_pos _).le le_rfl
      (by positivity) hmi hvmi hm0 hm1
      (hout _ _ _ hao hy hy2 hsmallA) (hout _ _ _ hco hy hy2 hsmallC)
      (fun v => by
        simpa only [Ge, Nat.reduceSub, pow_one, mul_one, mul_comm] using
          kernelMarkIntegrand_bound 1 (fun ξ => evenSpectrum ν m ξ.1 ξ.2) y w q u v 1 (hs0 v).2)
      (fun hu v hv => by
        have hl := (actual_spectra_low_bounds ν h3 hV h hh hs n m hmn hm6 hscale hbias hcomp u v
          (by simpa only [hbdef] using hu) (by simpa only [hfreq] using hv)).2
        convert kernelMarkIntegrand_bound 1 (fun ξ => evenSpectrum ν m ξ.1 ξ.2) y w q u v _ hl using 1 <;>
          dsimp [Ge, E, T] <;> ring)
      (fun hu v hv => by
        convert kernelMarkIntegrand_bound 1 (fun ξ => evenSpectrum ν m ξ.1 ξ.2) y w q u v _ (hcone u v hu hv).2 using 1 <;>
          dsimp [Ge] <;> ring)
    simpa only [Nat.reduceSub, pow_zero, pow_one, zero_mul, add_zero, Le] using ht
  have hIntO := four_region_integral_bound Go hGoi 1 (by norm_num) (by norm_num)
    A D P (128 * γ) b (4 * h) y (Cfull / T ^ 6) hA.le hD.le hao hb hco hy
    (by positivity) hprof Lo hLoLe.1 (by simpa only [Nat.reduceSub, pow_one] using hsliceO)
  have hIntE := four_region_integral_bound Ge hGei 2 (by norm_num) (by norm_num)
    A D P (128 * γ) b (4 * h) y (Cfull / T ^ 6) hA.le hD.le hao hb hco hy
    (by positivity) hprof Le hLoLe.2.1 hsliceE
  simp only [Nat.reduceSub, pow_one] at hIntO hIntE
  constructor
  · calc
      _ ≤ A * y * G * ((m : ℝ) * |μ| / (Real.sqrt T) ^ 3 +
          (m : ℝ) * m3 * (1 / (Real.sqrt T) ^ 5 +
            1 / (Real.sqrt T) ^ 3 + y / (Real.sqrt T) ^ 4)) +
          A * y * (Cfull / T ^ 6) * ((2 : ℝ) ^ 11 / b ^ 11) * (P * b) +
          D * y * (128 * γ) * (P * (128 * γ)) +
          D * y * (4 * h) ^ 31 * ((2 : ℝ) ^ 30 / b ^ 30) * (P * b) := by
        apply hIntO.trans
        gcongr
        exact hLoLe.2.2.1
      _ = (A * G) * y * ((m : ℝ) * |μ| / (Real.sqrt T) ^ 3 +
          (m : ℝ) * m3 * (1 / (Real.sqrt T) ^ 5 +
            1 / (Real.sqrt T) ^ 3 + y / (Real.sqrt T) ^ 4)) +
          (A * Cfull * P * 2 ^ 11 * 128 ^ 10) * y * (γ ^ 10 / T ^ 6) +
          (D * P * 128 ^ 2) * y * γ ^ 2 +
          (D * P * 4 ^ 31 * 2 ^ 30 * 128 ^ 29) * y * (h ^ 31 * γ ^ 29) := by
        dsimp only [b]
        field_simp <;> ring
      _ ≤ _ := by
        have hc := add_le_add (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right c0 (by positivity : 0 ≤ y *
            ((m : ℝ) * |μ| / (Real.sqrt T) ^ 3 + (m : ℝ) * m3 *
              (1 / (Real.sqrt T) ^ 5 + 1 / (Real.sqrt T) ^ 3 + y / (Real.sqrt T) ^ 4))))
          (mul_le_mul_of_nonneg_right c1 (by positivity : 0 ≤ y * (γ ^ 10 / T ^ 6))))
          (mul_le_mul_of_nonneg_right c2 (by positivity : 0 ≤ y * γ ^ 2)))
          (mul_le_mul_of_nonneg_right c3 (by positivity : 0 ≤ y * (h ^ 31 * γ ^ 29)))
        convert hc using 1 <;> ring
  · calc
      _ ≤ A * y * G / (Real.sqrt T) ^ 3 +
          A * y * (Cfull / T ^ 6) * ((2 : ℝ) ^ 10 / b ^ 10) * (P * b) +
          D * y * (128 * γ) ^ 2 * (P * (128 * γ)) +
          D * y * (4 * h) ^ 31 * ((2 : ℝ) ^ 29 / b ^ 29) * (P * b) := by
        apply hIntE.trans
        gcongr
        exact hLoLe.2.2.2
      _ = (A * G) * y * (1 / (Real.sqrt T) ^ 3) +
          (A * Cfull * P * 2 ^ 10 * 128 ^ 9) * y * (γ ^ 9 / T ^ 6) +
          (D * P * 128 ^ 3) * y * γ ^ 3 +
          (D * P * 4 ^ 31 * 2 ^ 29 * 128 ^ 28) * y * (h ^ 31 * γ ^ 28) := by
        dsimp only [b]
        field_simp <;> ring
      _ ≤ _ := by
        have hc := add_le_add (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right c0 (by positivity : 0 ≤ y * (1 / (Real.sqrt T) ^ 3)))
          (mul_le_mul_of_nonneg_right c4 (by positivity : 0 ≤ y * (γ ^ 9 / T ^ 6))))
          (mul_le_mul_of_nonneg_right c5 (by positivity : 0 ≤ y * γ ^ 3)))
          (mul_le_mul_of_nonneg_right c6 (by positivity : 0 ≤ y * (h ^ 31 * γ ^ 28)))
        convert hc using 1 <;> ring

private noncomputable def oddFrequencyBudget (M0 M3 γ h T y : ℝ) : ℝ :=
  M0 / (Real.sqrt T) ^ 3 + M3 * (1 / (Real.sqrt T) ^ 5 +
    1 / (Real.sqrt T) ^ 3 + y / (Real.sqrt T) ^ 4) +
      γ ^ 2 + γ ^ 10 / T ^ 6 + h ^ 31 * γ ^ 29

private noncomputable def evenFrequencyBudget (γ h T : ℝ) : ℝ :=
  1 / (Real.sqrt T) ^ 3 + γ ^ 3 + γ ^ 9 / T ^ 6 + h ^ 31 * γ ^ 28

private lemma frequency_budget_scale_reduction (N0 N3 M0 M3 γ h T y : ℝ)
    (hN0 : 0 ≤ N0) (hN3 : 0 ≤ N3) (hM0 : 0 ≤ M0) (hM3 : 0 ≤ M3)
    (hM0N : M0 ≤ N0) (hM3N : M3 ≤ N3)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hγN : γ ≤ 2 * N3) (hT : 0 < T) (hT4 : T ≤ 4 / 3)
    (hγT : γ ^ 2 ≤ T) (hγy : γ ≤ y) (hy2 : y ≤ 2) :
    (3 / 8 ≤ T →
      y * oddFrequencyBudget M0 M3 γ h T y ≤ 512 * (N0 + N3) ∧
      y * evenFrequencyBudget γ h T ≤ 512) ∧
    (M0 ≤ (4 / 3 : ℝ) * T * N0 → M3 ≤ (4 / 3 : ℝ) * T * N3 → y ^ 2 ≤ T →
      oddFrequencyBudget M0 M3 γ h T y ≤
        512 * (N0 / Real.sqrt T + N3 / (Real.sqrt T) ^ 3) ∧
      evenFrequencyBudget γ h T ≤ 512 / (Real.sqrt T) ^ 3) := by
  let t := Real.sqrt T
  have ht : 0 < t := Real.sqrt_pos.mpr hT
  have ht2 : t ^ 2 = T := Real.sq_sqrt hT.le
  have htmax : t ≤ 2 := by nlinarith only [ht2, hT4, ht.le]
  have ht3 : t ^ 3 ≤ 8 := by
    have hp := pow_le_pow_left₀ ht.le htmax 3
    norm_num at hp
    exact hp
  have hy : 0 ≤ y := hγ.le.trans hγy
  have hγt : γ ≤ t := by nlinarith only [hγT, ht2, hγ.le, ht.le]
  have hγ2 : γ ^ 2 ≤ 2 * N3 := by
    have hp := mul_le_mul_of_nonneg_left hγ1 hγ.le
    nlinarith only [hγ1, hγN, hγ.le, hp]
  have hh31 : h ^ 31 ≤ 1 := pow_le_one₀ hh hh1
  have hγ28 : γ ^ 28 ≤ 1 := pow_le_one₀ hγ.le hγ1
  have hγ29 : γ ^ 29 ≤ γ := by
    calc
      _ = γ ^ 28 * γ := by ring
      _ ≤ 1 * γ := mul_le_mul_of_nonneg_right hγ28 hγ.le
      _ = _ := one_mul _
  have htailO : h ^ 31 * γ ^ 29 ≤ 2 * N3 := by
    calc
      _ ≤ 1 * γ ^ 29 := mul_le_mul_of_nonneg_right hh31 (by positivity)
      _ ≤ _ := by simpa only [one_mul] using hγ29.trans hγN
  have htailE : h ^ 31 * γ ^ 28 ≤ 1 := by
    calc
      _ ≤ 1 * γ ^ 28 := mul_le_mul_of_nonneg_right hh31 (by positivity)
      _ ≤ 1 := by simpa only [one_mul] using hγ28
  have hhighE : γ ^ 9 / T ^ 6 ≤ 1 / t ^ 3 := by
    apply (div_le_div_iff₀ (pow_pos hT 6) (pow_pos ht 3)).mpr
    calc
      _ ≤ t ^ 9 * t ^ 3 := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hγ.le hγt 9) (by positivity)
      _ = _ := by rw [← ht2]; ring
  have hhighO : γ ^ 10 / T ^ 6 ≤ 2 * N3 / t ^ 3 := by
    calc
      _ = γ * (γ ^ 9 / T ^ 6) := by ring
      _ ≤ γ * (1 / t ^ 3) := mul_le_mul_of_nonneg_left hhighE hγ.le
      _ ≤ (2 * N3) * (1 / t ^ 3) := mul_le_mul_of_nonneg_right hγN (by positivity)
      _ = _ := by ring
  have hconst : 1 ≤ 8 / t ^ 3 := (le_div_iff₀ (pow_pos ht 3)).mpr (by simpa using ht3)
  have hEven : evenFrequencyBudget γ h T ≤ 32 / t ^ 3 := by
    have hγ3 : γ ^ 3 ≤ 1 := pow_le_one₀ hγ.le hγ1
    dsimp only [evenFrequencyBudget]
    change 1 / t ^ 3 + γ ^ 3 + γ ^ 9 / T ^ 6 + h ^ 31 * γ ^ 28 ≤ _
    calc
      _ ≤ 1 / t ^ 3 + 1 + 1 / t ^ 3 + 1 := by gcongr
      _ = (2 + 2 * t ^ 3) / t ^ 3 := by field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith only [ht3]) (by positivity)
  have hOddTail : γ ^ 2 + γ ^ 10 / T ^ 6 + h ^ 31 * γ ^ 29 ≤ 36 * N3 / t ^ 3 := by
    have hNconst : 2 * N3 ≤ 16 * N3 / t ^ 3 := by
      convert mul_le_mul_of_nonneg_left hconst (by positivity : 0 ≤ 2 * N3) using 1 <;> ring
    calc
      _ ≤ 16 * N3 / t ^ 3 + 2 * N3 / t ^ 3 + 16 * N3 / t ^ 3 :=
        add_le_add (add_le_add (hγ2.trans hNconst) hhighO) (htailO.trans hNconst)
      _ = 34 * N3 / t ^ 3 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith only [hN3]) (by positivity)
  constructor
  · intro hTearly
    have htmin : (1 / 2 : ℝ) ≤ t := by nlinarith only [hTearly, ht2, ht.le]
    have hI3 : 1 / t ^ 3 ≤ 8 := by
      calc
        _ ≤ 1 / (1 / 2 : ℝ) ^ 3 := one_div_le_one_div_of_le (by norm_num)
          (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) htmin 3)
        _ = _ := by norm_num
    have hI4 : 1 / t ^ 4 ≤ 16 := by
      calc
        _ ≤ 1 / (1 / 2 : ℝ) ^ 4 := one_div_le_one_div_of_le (by norm_num)
          (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) htmin 4)
        _ = _ := by norm_num
    have hI5 : 1 / t ^ 5 ≤ 32 := by
      calc
        _ ≤ 1 / (1 / 2 : ℝ) ^ 5 := one_div_le_one_div_of_le (by norm_num)
          (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) htmin 5)
        _ = _ := by norm_num
    have h0 : M0 / t ^ 3 ≤ 8 * N0 := by
      have hm := mul_le_mul hM0N hI3 (by positivity) hN0
      convert hm using 1 <;> ring
    have h3 : M3 / t ^ 3 ≤ 8 * N3 := by
      have hm := mul_le_mul hM3N hI3 (by positivity) hN3
      convert hm using 1 <;> ring
    have h5 : M3 / t ^ 5 ≤ 32 * N3 := by
      have hm := mul_le_mul hM3N hI5 (by positivity) hN3
      convert hm using 1 <;> ring
    have h4 : M3 * y / t ^ 4 ≤ 32 * N3 := by
      have hm := mul_le_mul (mul_le_mul hM3N hy2 hy hN3) hI4 (by positivity) (by positivity)
      convert hm using 1 <;> ring
    have htail : γ ^ 2 + γ ^ 10 / T ^ 6 + h ^ 31 * γ ^ 29 ≤ 20 * N3 := by
      have hhi := hhighO.trans (by
        convert mul_le_mul_of_nonneg_left hI3 (by positivity : 0 ≤ 2 * N3) using 1 <;> ring)
      linarith only [hγ2, hhi, htailO]
    have hOdd : oddFrequencyBudget M0 M3 γ h T y ≤ 8 * N0 + 92 * N3 := by
      dsimp only [oddFrequencyBudget]
      change M0 / t ^ 3 + M3 * (1 / t ^ 5 + 1 / t ^ 3 + y / t ^ 4) +
        γ ^ 2 + γ ^ 10 / T ^ 6 + h ^ 31 * γ ^ 29 ≤ _
      calc
        _ = M0 / t ^ 3 + M3 / t ^ 5 + M3 / t ^ 3 + M3 * y / t ^ 4 +
            (γ ^ 2 + γ ^ 10 / T ^ 6 + h ^ 31 * γ ^ 29) := by ring
        _ ≤ 8 * N0 + 32 * N3 + 8 * N3 + 32 * N3 + 20 * N3 :=
          add_le_add (add_le_add (add_le_add (add_le_add h0 h5) h3) h4) htail
        _ = _ := by ring
    constructor
    · calc
        _ ≤ 2 * (8 * N0 + 92 * N3) := mul_le_mul hy2 hOdd
          (by unfold oddFrequencyBudget; positivity) (by positivity)
        _ ≤ _ := by nlinarith only [hN0, hN3]
    · have he : evenFrequencyBudget γ h T ≤ 256 := hEven.trans (by
        convert mul_le_mul_of_nonneg_left hI3 (by norm_num : (0 : ℝ) ≤ 32) using 1 <;> ring)
      exact (mul_le_mul hy2 he (by unfold evenFrequencyBudget; positivity) (by norm_num)).trans
        (by norm_num)
  · intro hM0T hM3T hyT
    have hyt : y ≤ t := by nlinarith only [hyT, ht2, hy, ht.le]
    have h0 : M0 / t ^ 3 ≤ 2 * N0 / t := by
      apply (div_le_div_iff₀ (pow_pos ht 3) ht).mpr
      have hm := mul_le_mul_of_nonneg_right hM0T ht.le
      rw [← ht2] at hm
      nlinarith only [hm, mul_nonneg hN0 (pow_pos ht 3).le]
    have h5 : M3 / t ^ 5 ≤ 2 * N3 / t ^ 3 := by
      apply (div_le_div_iff₀ (pow_pos ht 5) (pow_pos ht 3)).mpr
      have hm := mul_le_mul_of_nonneg_right hM3T (pow_pos ht 3).le
      rw [← ht2] at hm
      nlinarith only [hm, mul_nonneg hN3 (pow_pos ht 5).le]
    have h3 : M3 / t ^ 3 ≤ N3 / t ^ 3 := div_le_div_of_nonneg_right hM3N (by positivity)
    have h4 : M3 * y / t ^ 4 ≤ N3 / t ^ 3 := by
      calc
        _ ≤ N3 * t / t ^ 4 := div_le_div_of_nonneg_right
          (mul_le_mul hM3N hyt hy hN3) (by positivity)
        _ = _ := by field_simp
    constructor
    · dsimp only [oddFrequencyBudget]
      change M0 / t ^ 3 + M3 * (1 / t ^ 5 + 1 / t ^ 3 + y / t ^ 4) +
        γ ^ 2 + γ ^ 10 / T ^ 6 + h ^ 31 * γ ^ 29 ≤ _
      calc
        _ = M0 / t ^ 3 + M3 / t ^ 5 + M3 / t ^ 3 + M3 * y / t ^ 4 +
            (γ ^ 2 + γ ^ 10 / T ^ 6 + h ^ 31 * γ ^ 29) := by ring
        _ ≤ 2 * N0 / t + 2 * N3 / t ^ 3 + N3 / t ^ 3 + N3 / t ^ 3 + 36 * N3 / t ^ 3 :=
          add_le_add (add_le_add (add_le_add (add_le_add h0 h5) h3) h4) hOddTail
        _ = 2 * (N0 / t) + 40 * (N3 / t ^ 3) := by ring
        _ ≤ 512 * (N0 / t) + 512 * (N3 / t ^ 3) := add_le_add
          (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
          (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
        _ = _ := by ring
    · exact hEven.trans (div_le_div_of_nonneg_right (by norm_num) (by positivity))

theorem sourceTruncation_futureNoise_early_long_kernel_bounds :
    ∃ C epsilon0 L2 : ℝ, 0 < C ∧ 0 < epsilon0 ∧ epsilon0 ≤ 1 / 2 ∧
      (16384 : ℝ) ≤ L2 ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
          (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 →
          (∫ a : ℝ, a ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ epsilon0 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            let ρ : Measure ℝ :=
              ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
            let mu : ℝ := ∫ a : ℝ, a ∂ρ
            let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
            let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
            let gamma : ℝ := m3 / variance (id : ℝ → ℝ) ρ
            ∀ y : ℝ, gamma ≤ y → y ≤ 2 →
              ∀ i : ℕ, 1 ≤ i → i ≤ n →
                let m : ℕ := n - i
                let T : ℝ := (m : ℝ) * m2
                let f : ℝ → ℝ → ℝ := fun q w => sourceFutureNoiseKernel ρ m y (w, q)
                let o : ℝ → ℝ → ℝ := fun q w => (f q w - f q (-w)) / 2
                let e : ℝ → ℝ → ℝ := fun q w => (f q w + f q (-w)) / 2
                (∀ w q : ℝ,
                  DifferentiableAt ℝ (o q) w ∧
                  DifferentiableAt ℝ (e q) w ∧
                  DifferentiableAt ℝ (fun r : ℝ => deriv (e q) r) w) ∧
                (i ≤ n / 2 → ∀ w q : ℝ,
                  |deriv (o q) w| ≤ C * ((n : ℝ) * |mu| + (n : ℝ) * m3) ∧
                  |deriv (fun r : ℝ => deriv (e q) r) w| ≤ C) ∧
                (n / 2 < i → max (L2 * gamma ^ 2) (y ^ 2) ≤ T →
                  ∀ w q : ℝ,
                    |deriv (o q) w| ≤ C * y *
                      ((n : ℝ) * |mu| / Real.sqrt T +
                        (n : ℝ) * m3 / (Real.sqrt T) ^ 3) ∧
                    |deriv (fun r : ℝ => deriv (e q) r) w| ≤
                      C * y / (Real.sqrt T) ^ 3) := by
  obtain ⟨Cfull, hCfull, hfull⟩ := sourceTruncation_fullNoise_highFrequency_derivatives
  obtain ⟨K, δ, hK, hδ, hδ16, hfrequency⟩ := actual_frequency_pair_budgets Cfull hCfull.le
  let epsilon0 : ℝ := min (δ / 1024) (1 / 1024)
  let B : ℝ := ‖(2 * Complex.I / (((2 * Real.pi) ^ 2 : ℝ) : ℂ))‖ +
    ‖(-2 / (((2 * Real.pi) ^ 2 : ℝ) : ℂ))‖ + 1
  let C : ℝ := 512 * B * K
  have hB : 0 < B := by dsimp [B]; positivity
  have hBo : ‖(2 * Complex.I / (((2 * Real.pi) ^ 2 : ℝ) : ℂ))‖ ≤ B := by
    dsimp [B]
    linarith [norm_nonneg (-2 / (((2 * Real.pi) ^ 2 : ℝ) : ℂ))]
  have hBe : ‖(-2 / (((2 * Real.pi) ^ 2 : ℝ) : ℂ))‖ ≤ B := by
    dsimp [B]
    linarith [norm_nonneg (2 * Complex.I / (((2 * Real.pi) ^ 2 : ℝ) : ℂ))]
  have he0 : 0 < epsilon0 := lt_min (by positivity) (by norm_num)
  have he01 : epsilon0 ≤ 1 / 1024 := min_le_right _ _
  have he0δ : epsilon0 ≤ δ / 1024 := min_le_left _ _
  refine ⟨C, epsilon0, 16384, by dsimp [C]; positivity, he0,
    by linarith, le_rfl, ?_⟩
  intro ν0 hp0 n h2 hnorm hmean x epsilon hx he he0bound hbudget
  dsimp only
  intro y hγy hy2 i _hi1 hin
  letI := hp0
  let h : ℝ := epsilon / (1 + x)
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ h}
  let μ : ℝ := ∫ a : ℝ, a ∂ρ
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
  let γ : ℝ := m3 / variance (id : ℝ → ℝ) ρ
  let m : ℕ := n - i
  let T : ℝ := (m : ℝ) * m2
  let N0 : ℝ := (n : ℝ) * |μ|
  let N3 : ℝ := (n : ℝ) * m3
  let M0 : ℝ := (m : ℝ) * |μ|
  let M3 : ℝ := (m : ℝ) * m3
  let f : ℝ → ℝ → ℝ := fun q w => sourceFutureNoiseKernel ρ m y (w, q)
  let o : ℝ → ℝ → ℝ := fun q w => (f q w - f q (-w)) / 2
  let e : ℝ → ℝ → ℝ := fun q w => (f q w + f q (-w)) / 2
  have hehalf : epsilon ≤ 1 / 2 := by linarith
  have hh : 0 < h := div_pos he (by linarith)
  have hhε : h ≤ epsilon := by
    apply (div_le_iff₀ (by linarith : 0 < 1 + x)).mpr
    nlinarith only [mul_nonneg he.le hx]
  obtain ⟨_, _, hp, hs, _, h2r, h3r, _⟩ :=
    Shao.sourceTruncation_law_data ν0 n h2 hnorm x epsilon hx he hehalf hbudget
  have hprob : IsProbabilityMeasure ρ := hp
  letI := hprob
  have hsupport : ∀ᵐ a : ℝ ∂ρ, |a| ≤ h := hs
  have hcube : Integrable (fun a : ℝ => |a| ^ 3) ρ := h3r
  obtain ⟨hscale, hscaleHi, _, hVeq, _, hV, _, _⟩ :=
    Shao.sourceTruncation_variance_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget
  change (3 / 4 : ℝ) ≤ (n : ℝ) * m2 at hscale
  change (n : ℝ) * m2 ≤ (4 / 3 : ℝ) at hscaleHi
  change variance (id : ℝ → ℝ) ρ = m2 - μ ^ 2 at hVeq
  change 0 < variance (id : ℝ → ℝ) ρ at hV
  have hm2 : 0 < m2 := by nlinarith only [hV, hVeq, sq_nonneg μ]
  obtain ⟨hm3pos, hγ, _, _, hγh, _, hγN, _, _⟩ :=
    Shao.sourceTruncation_gamma_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget
  change 0 < m3 at hm3pos
  change 0 < γ at hγ
  change γ ≤ 2 * h at hγh
  replace hγN : γ ≤ 2 * N3 := by
    dsimp only [N3]
    nlinarith only [hγN]
  have hy : 0 ≤ y := hγ.le.trans hγy
  have hh1 : h ≤ 1 := by linarith
  have hγ1 : γ ≤ 1 := by linarith
  have hγsmall : γ ≤ 1 / 512 := by linarith
  have hsmallA : (128 * γ) * y ≤ δ := by
    have hp := mul_le_mul (hγh.trans (by linarith : 2 * h ≤ 2 * epsilon)) hy2 hy
      (by positivity : 0 ≤ 2 * epsilon)
    nlinarith only [hp, he0bound, he0δ, he.le]
  have hsmallC : (4 * h) * y ≤ δ := by
    have hp := mul_le_mul hhε hy2 hy he.le
    nlinarith only [hp, he0bound, he0δ, he.le]
  have hmn : m ≤ n := Nat.sub_le n i
  have hmnR : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
  have hThi : T ≤ 4 / 3 :=
    (mul_le_mul_of_nonneg_right hmnR hm2.le).trans hscaleHi
  have hN0 : 0 ≤ N0 := by dsimp [N0]; positivity
  have hN3 : 0 ≤ N3 := by dsimp [N3]; positivity
  have hM0 : 0 ≤ M0 := by dsimp [M0]; positivity
  have hM3 : 0 ≤ M3 := by dsimp [M3]; positivity
  have hM0N : M0 ≤ N0 := mul_le_mul_of_nonneg_right hmnR (abs_nonneg μ)
  have hM3N : M3 ≤ N3 := mul_le_mul_of_nonneg_right hmnR hm3pos.le
  have hratio : (m : ℝ) ≤ (4 / 3 : ℝ) * T * (n : ℝ) := by
    have hp := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg m)
    dsimp [T]
    nlinarith only [hp]
  have hM0T : M0 ≤ (4 / 3 : ℝ) * T * N0 := by
    convert mul_le_mul_of_nonneg_right hratio (abs_nonneg μ) using 1 <;> dsimp [M0, N0] <;> ring
  have hM3T : M3 ≤ (4 / 3 : ℝ) * T * N3 := by
    convert mul_le_mul_of_nonneg_right hratio hm3pos.le using 1 <;> dsimp [M3, N3] <;> ring
  have hQuant (hguard : (16384 : ℝ) * γ ^ 2 ≤ T) (w q : ℝ) :
      |deriv (o q) w| ≤ B * K * y * oddFrequencyBudget M0 M3 γ h T y ∧
      |deriv (fun r : ℝ => deriv (e q) r) w| ≤ B * K * y * evenFrequencyBudget γ h T := by
    have hTp : 0 < T := (mul_pos (by norm_num : (0 : ℝ) < 16384)
      (sq_pos_of_pos hγ)).trans_le hguard
    obtain ⟨_, hm6, _, hbias, hcomp⟩ :=
      Shao.sourceTruncation_oddPower_scale_inputs ν0 n h2 hnorm hmean x epsilon hx he hehalf
        hbudget i hin 16384 (by norm_num) hguard
    have hcone (u v : ℝ) (hu : 1 / (128 * γ) ≤ |u|) (hv : |v| ≤ |u| / (4 * h)) :
        ‖oddSpectrum ρ m u v‖ ≤ Cfull / (T ^ 6 * |u| ^ 12) ∧
        ‖evenSpectrum ρ m u v‖ ≤ Cfull / (T ^ 6 * |u| ^ 12) := by
      have hu0 : u ≠ 0 := by
        have hp : 0 < |u| := (by positivity : 0 < 1 / (128 * γ)).trans_le hu
        exact abs_pos.mp hp
      have huf : (1 / 128 : ℝ) / γ ≤ |u| := by convert hu using 1 <;> ring
      have hkL : 1 ≤ (1 / 128 : ℝ) * Real.sqrt 16384 := by
        rw [show (16384 : ℝ) = 128 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
        norm_num
      have hp := hfull ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hin
        h (1 / 128) 16384 le_rfl (by norm_num) (by norm_num) hkL hguard
        1 u v (by norm_num) hu0 huf hv
      have hn := hfull ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hin
        h (1 / 128) 16384 le_rfl (by norm_num) (by norm_num) hkL hguard
        (-1) u v (by norm_num) hu0 huf hv
      apply half_spectra_bound
      · simpa only [one_mul] using hp.2.2.1
      · simpa only [neg_one_mul] using hn.2.2.1
    obtain ⟨ho, he⟩ := hfrequency ρ hprob hcube hV h hh hsupport n m hmn hm6 hscale hbias hcomp
      hTp hγ y hy hy2 hsmallA hsmallC hcone w q
    change ‖∫ ξ, kernelMarkIntegrand 0 (fun ξ => oddSpectrum ρ m ξ.1 ξ.2) y w q ξ‖ ≤
      K * y * oddFrequencyBudget M0 M3 γ h T y at ho
    change ‖∫ ξ, kernelMarkIntegrand 1 (fun ξ => evenSpectrum ρ m ξ.1 ξ.2) y w q ξ‖ ≤
      K * y * evenFrequencyBudget γ h T at he
    have hf := actual_kernel_mark_formulas ρ hcube hV h hh hsupport m y hy w q
    constructor
    · calc
        _ = ‖((deriv (o q) w : ℝ) : ℂ)‖ := by simp only [Complex.norm_real, Real.norm_eq_abs]
        _ = ‖(2 * Complex.I / (((2 * Real.pi) ^ 2 : ℝ) : ℂ))‖ *
            ‖∫ ξ, kernelMarkIntegrand 0 (fun ξ => oddSpectrum ρ m ξ.1 ξ.2) y w q ξ‖ := by
          rw [hf.2.2.2.1, norm_mul]
        _ ≤ B * (K * y * oddFrequencyBudget M0 M3 γ h T y) :=
          mul_le_mul hBo ho (norm_nonneg _) hB.le
        _ = _ := by ring
    · calc
        _ = ‖((deriv (fun r : ℝ => deriv (e q) r) w : ℝ) : ℂ)‖ := by
          simp only [Complex.norm_real, Real.norm_eq_abs]
        _ = ‖(-2 / (((2 * Real.pi) ^ 2 : ℝ) : ℂ))‖ *
            ‖∫ ξ, kernelMarkIntegrand 1 (fun ξ => evenSpectrum ρ m ξ.1 ξ.2) y w q ξ‖ := by
          rw [hf.2.2.2.2, norm_mul]
        _ ≤ B * (K * y * evenFrequencyBudget γ h T) := mul_le_mul hBe he (norm_nonneg _) hB.le
        _ = _ := by ring
  refine ⟨fun w q => (actual_kernel_mark_formulas ρ hcube hV h hh hsupport m y hy w q).1, ?_, ?_⟩
  · intro hiearly w q
    have hne : n ≤ 2 * m := by dsimp [m]; omega
    have hneR : (n : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hne
    have hTearly : (3 / 8 : ℝ) ≤ T := by
      have hp := mul_le_mul_of_nonneg_right hneR hm2.le
      dsimp [T]
      nlinarith only [hp, hscale]
    have hγsquare := pow_le_pow_left₀ hγ.le hγsmall 2
    have hguard : (16384 : ℝ) * γ ^ 2 ≤ T := by nlinarith only [hγsquare, hTearly]
    have hTp : 0 < T := by linarith
    have hγT : γ ^ 2 ≤ T := by nlinarith only [hguard, sq_nonneg γ]
    have hr := (frequency_budget_scale_reduction N0 N3 M0 M3 γ h T y hN0 hN3 hM0 hM3 hM0N hM3N
      hγ hγ1 hh.le hh1 hγN hTp hThi hγT hγy hy2).1 hTearly
    have hq := hQuant hguard w q
    constructor
    · calc
        _ ≤ B * K * (y * oddFrequencyBudget M0 M3 γ h T y) := by convert hq.1 using 1 <;> ring
        _ ≤ B * K * (512 * (N0 + N3)) := mul_le_mul_of_nonneg_left hr.1 (by positivity)
        _ = _ := by dsimp [C, N0, N3]; ring
    · calc
        _ ≤ B * K * (y * evenFrequencyBudget γ h T) := by convert hq.2 using 1 <;> ring
        _ ≤ B * K * 512 := mul_le_mul_of_nonneg_left hr.2 (by positivity)
        _ = _ := by dsimp [C]; ring
  · intro _hilate hlong w q
    have hguard : (16384 : ℝ) * γ ^ 2 ≤ T := (le_max_left _ _).trans hlong
    have hyT : y ^ 2 ≤ T := (le_max_right _ _).trans hlong
    have hTp : 0 < T := (mul_pos (by norm_num : (0 : ℝ) < 16384)
      (sq_pos_of_pos hγ)).trans_le hguard
    have hγT : γ ^ 2 ≤ T := by nlinarith only [hguard, sq_nonneg γ]
    have hr := (frequency_budget_scale_reduction N0 N3 M0 M3 γ h T y hN0 hN3 hM0 hM3 hM0N hM3N
      hγ hγ1 hh.le hh1 hγN hTp hThi hγT hγy hy2).2 hM0T hM3T hyT
    have hq := hQuant hguard w q
    constructor
    · calc
        _ ≤ B * K * y * (512 * (N0 / Real.sqrt T + N3 / (Real.sqrt T) ^ 3)) :=
          hq.1.trans (mul_le_mul_of_nonneg_left hr.1 (by positivity))
        _ = _ := by dsimp [C, N0, N3]; ring
    · calc
        _ ≤ B * K * y * (512 / (Real.sqrt T) ^ 3) :=
          hq.2.trans (mul_le_mul_of_nonneg_left hr.2 (by positivity))
        _ = _ := by dsimp [C]; ring

/- BEGIN FIXED CUTOFF PUBLIC COMPANIONS.
Additive export of the fixed one-sixteenth cutoff from the existing proof.
The original source is recovered exactly by deleting this marked block.
-/

private lemma fixedCutoff_actual_mark_outside_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ a y u : ℝ, 0 < a → 0 ≤ y → y ≤ 2 → a * y ≤ (1 / 16 : ℝ) →
        (∫ v in {v : ℝ | |u| / a < |v|},
          ‖sourceMarkSine sourceKernelCutoff y u 0 v‖) ≤
            C * y * |u| * tailProfile 31 a u := by
  obtain ⟨C, hC, hb⟩ := sourceKernel_marked_outside_norms_fixed_sixteenth
  refine ⟨C, hC, ?_⟩
  intro a y u ha hy hy2 hay
  have h := (hb 0 (Or.inl rfl) 0 (by norm_num) a y u 0 ha hy hy2 hay
    (by simpa using div_nonneg hy (by norm_num : (0 : ℝ) ≤ 16))).2.2.2.2.2.2.1
  simp only [pow_zero, div_one] at h
  change (∫ v in {v : ℝ | |u| / a < |v|},
    ‖sourceMarkSine sourceKernelCutoff y u 0 v‖) ≤
      C * min (y * |u|) 1 / (1 + |u| / a) ^ 31 at h
  calc
    _ ≤ C * (y * |u|) / (1 + |u| / a) ^ 31 := h.trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (min_le_left _ _) hC.le) (by positivity))
    _ = _ := by unfold tailProfile; ring

private lemma fixedCutoff_actual_frequency_pair_budgets (Cfull : ℝ) (hCfull : 0 ≤ Cfull) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun a : ℝ => |a| ^ 3) ν →
        0 < variance (id : ℝ → ℝ) ν →
        ∀ h : ℝ, 0 < h → (∀ᵐ a : ℝ ∂ν, |a| ≤ h) →
        ∀ n m : ℕ, m ≤ n → 6 ≤ m →
        (3 / 4 : ℝ) ≤ (n : ℝ) * ∫ a : ℝ, a ^ 2 ∂ν →
        (n : ℝ) * |∫ a : ℝ, a ∂ν| ≤ 1 →
        (∫ a : ℝ, a ^ 2 ∂ν) ≤ 4 * variance (id : ℝ → ℝ) ν →
        let μ : ℝ := ∫ a : ℝ, a ∂ν
        let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
        let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
        let γ : ℝ := m3 / variance (id : ℝ → ℝ) ν
        let T : ℝ := (m : ℝ) * m2
        0 < T → 0 < γ → ∀ y : ℝ, 0 ≤ y → y ≤ 2 →
        (128 * γ) * y ≤ (1 / 16 : ℝ) → (4 * h) * y ≤ (1 / 16 : ℝ) →
        (∀ u v : ℝ, 1 / (128 * γ) ≤ |u| → |v| ≤ |u| / (4 * h) →
          ‖oddSpectrum ν m u v‖ ≤ Cfull / (T ^ 6 * |u| ^ 12) ∧
          ‖evenSpectrum ν m u v‖ ≤ Cfull / (T ^ 6 * |u| ^ 12)) →
        ∀ w q : ℝ,
          ‖∫ ξ : ℝ × ℝ,
            kernelMarkIntegrand 0 (fun ξ => oddSpectrum ν m ξ.1 ξ.2) y w q ξ‖ ≤
            K * y * ((m : ℝ) * |μ| / (Real.sqrt T) ^ 3 +
              (m : ℝ) * m3 * (1 / (Real.sqrt T) ^ 5 +
                1 / (Real.sqrt T) ^ 3 + y / (Real.sqrt T) ^ 4) +
              γ ^ 2 + γ ^ 10 / T ^ 6 + h ^ 31 * γ ^ 29) ∧
          ‖∫ ξ : ℝ × ℝ,
            kernelMarkIntegrand 1 (fun ξ => evenSpectrum ν m ξ.1 ξ.2) y w q ξ‖ ≤
            K * y * (1 / (Real.sqrt T) ^ 3 + γ ^ 3 +
              γ ^ 9 / T ^ 6 + h ^ 31 * γ ^ 28) := by
  obtain ⟨A, hA, hmark⟩ := actual_mark_linear_budget
  obtain ⟨D, hD, hout⟩ := fixedCutoff_actual_mark_outside_budget
  obtain ⟨P, hP, hprof⟩ := tailProfile_budget
  obtain ⟨G, hG, hgauss⟩ := gaussian_moments_budget
  let R : ℝ := 2 ^ 31 * 128 ^ 31 * 4 ^ 31
  let S : ℝ := A * G + A * Cfull * P + D * P + 1
  let K : ℝ := R * S
  have hR : 0 < R := by norm_num [R]
  have hAG : 0 ≤ A * G := by positivity
  have hAC : 0 ≤ A * Cfull * P := by positivity
  have hDP : 0 ≤ D * P := by positivity
  have hS : 0 < S := by dsimp [S]; linarith
  have hcoef (z c : ℝ) (hz0 : 0 ≤ z) (hz : z ≤ S) (hc0 : 0 ≤ c) (hc : c ≤ R) :
      z * c ≤ K := by
    calc
      _ ≤ S * R := mul_le_mul hz hc hc0 hS.le
      _ = K := by dsimp [K]; ring
  have c0 : A * G ≤ K := by
    simpa using hcoef (A * G) 1 hAG (by dsimp [S]; linarith) (by norm_num) (by norm_num [R])
  have c1 : A * Cfull * P * 2 ^ 11 * 128 ^ 10 ≤ K := by
    convert hcoef (A * Cfull * P) (2 ^ 11 * 128 ^ 10) hAC
      (by dsimp [S]; linarith) (by positivity) (by norm_num [R]) using 1 <;> ring
  have c2 : D * P * 128 ^ 2 ≤ K := hcoef (D * P) (128 ^ 2) hDP
    (by dsimp [S]; linarith) (by positivity) (by norm_num [R])
  have c3 : D * P * 4 ^ 31 * 2 ^ 30 * 128 ^ 29 ≤ K := by
    convert hcoef (D * P) (4 ^ 31 * 2 ^ 30 * 128 ^ 29) hDP
      (by dsimp [S]; linarith) (by positivity) (by norm_num [R]) using 1 <;> ring
  have c4 : A * Cfull * P * 2 ^ 10 * 128 ^ 9 ≤ K := by
    convert hcoef (A * Cfull * P) (2 ^ 10 * 128 ^ 9) hAC
      (by dsimp [S]; linarith) (by positivity) (by norm_num [R]) using 1 <;> ring
  have c5 : D * P * 128 ^ 3 ≤ K := hcoef (D * P) (128 ^ 3) hDP
    (by dsimp [S]; linarith) (by positivity) (by norm_num [R])
  have c6 : D * P * 4 ^ 31 * 2 ^ 29 * 128 ^ 28 ≤ K := by
    convert hcoef (D * P) (4 ^ 31 * 2 ^ 29 * 128 ^ 28) hDP
      (by dsimp [S]; linarith) (by positivity) (by norm_num [R]) using 1 <;> ring
  refine ⟨K, mul_pos hR hS, ?_⟩
  intro ν hp h3 hV h hh hs n m hmn hm6 hscale hbias hcomp
  dsimp only
  intro hT hγ y hy hy2 hsmallA hsmallC hcone w q
  letI := hp
  let μ : ℝ := ∫ a : ℝ, a ∂ν
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
  let γ : ℝ := m3 / variance (id : ℝ → ℝ) ν
  let T : ℝ := (m : ℝ) * ∫ a : ℝ, a ^ 2 ∂ν
  let b : ℝ := 1 / (128 * γ)
  have hb : 0 < b := by dsimp [b]; positivity
  have hγ0 : 0 < γ := hγ
  have hT0 : 0 < T := hT
  have hm3 : 0 ≤ m3 := integral_nonneg fun a => by positivity
  have hM0 : 0 ≤ (m : ℝ) * |μ| := by positivity
  have hM3 : 0 ≤ (m : ℝ) * m3 := by positivity
  let E : ℝ → ℝ := fun u => Real.exp (-T * u ^ 2 / 256)
  let Lo : ℝ → ℝ := fun u => A * y * |u| *
    (E u * ((m : ℝ) * |μ| * |u| + (m : ℝ) * m3 * |u| ^ 3) +
      E u * ((m : ℝ) * m3) * |u| * (1 + y * |u|))
  let Le : ℝ → ℝ := fun u => A * y * |u| ^ 2 * E u
  have hLoLe := gaussian_low_envelopes G A y ((m : ℝ) * |μ|) ((m : ℝ) * m3) T
    (hgauss T hT0) hA.le hy hM0 hM3 hT0
  let Go : (ℝ × ℝ) → ℂ :=
    kernelMarkIntegrand 0 (fun ξ => oddSpectrum ν m ξ.1 ξ.2) y w q
  let Ge : (ℝ × ℝ) → ℂ :=
    kernelMarkIntegrand 1 (fun ξ => evenSpectrum ν m ξ.1 ξ.2) y w q
  have hf := actual_kernel_mark_formulas ν h3 hV h hh hs m y hy w q
  have hGoi : Integrable Go := hf.2.1
  have hGei : Integrable Ge := hf.2.2.1
  have hGop : Integrable Go (volume.prod volume) := by
    simpa only [← Measure.volume_eq_prod ℝ ℝ] using hGoi
  have hGep : Integrable Ge (volume.prod volume) := by
    simpa only [← Measure.volume_eq_prod ℝ ℝ] using hGei
  have hao : 0 < 128 * γ := by positivity
  have hco : 0 < 4 * h := by positivity
  have hfreq (u : ℝ) : |u| / (128 * γ) = (1 / 128 : ℝ) * |u| / γ := by ring
  have hbdef : b = (1 / 128 : ℝ) / γ := by dsimp [b]; ring
  have hsliceO : ∀ᵐ u : ℝ, (∫ v : ℝ, ‖Go (u, v)‖) ≤ Lo u +
      A * y * (Cfull / T ^ 6) * ((2 : ℝ) ^ 11 / b ^ 11) * tailProfile 11 b u +
      D * y * (128 * γ) * tailProfile 30 (128 * γ) u +
      D * y * (4 * h) ^ 31 * ((2 : ℝ) ^ 30 / b ^ 30) * tailProfile 30 b u := by
    filter_upwards [(integrable_prod_iff hGop.aestronglyMeasurable).mp hGop |>.1] with u hi
    obtain ⟨hmi, hvmi, hm0, hm1⟩ := hmark y u hy
    have hs0 := actual_spectra_le_one ν h3 hV h hh hs m u
    have ht := four_region_slice_bound (fun v => Go (u, v)) hi 1 (by norm_num) (by norm_num)
      A D (128 * γ) b (4 * h) y u
      (E u * ((m : ℝ) * |μ| * |u| + (m : ℝ) * m3 * |u| ^ 3))
      (E u * ((m : ℝ) * m3) * |u|) (Cfull / T ^ 6)
      hA.le hD.le hao hb hco hy (by dsimp [E]; positivity) (by dsimp [E]; positivity)
      (by positivity) hmi hvmi hm0 hm1
      (hout _ _ _ hao hy hy2 hsmallA) (hout _ _ _ hco hy hy2 hsmallC)
      (fun v => by
        simpa only [Go, Nat.reduceSub, pow_zero, one_mul, mul_one, mul_comm] using
          kernelMarkIntegrand_bound 0 (fun ξ => oddSpectrum ν m ξ.1 ξ.2) y w q u v 1 (hs0 v).1)
      (fun hu v hv => by
        have hl := (actual_spectra_low_bounds ν h3 hV h hh hs n m hmn hm6 hscale hbias hcomp u v
          (by simpa only [hbdef] using hu) (by simpa only [hfreq] using hv)).1
        convert kernelMarkIntegrand_bound 0 (fun ξ => oddSpectrum ν m ξ.1 ξ.2) y w q u v _ hl using 1 <;>
          dsimp [Go, E, μ, m3, T] <;> ring)
      (fun hu v hv => by
        convert kernelMarkIntegrand_bound 0 (fun ξ => oddSpectrum ν m ξ.1 ξ.2) y w q u v _
          (hcone u v hu hv).1 using 1 <;> dsimp [Go] <;> ring)
    simpa only [Nat.reduceSub, pow_zero, pow_one, Lo] using ht
  have hsliceE : ∀ᵐ u : ℝ, (∫ v : ℝ, ‖Ge (u, v)‖) ≤ Le u +
      A * y * (Cfull / T ^ 6) * ((2 : ℝ) ^ 10 / b ^ 10) * tailProfile 10 b u +
      D * y * (128 * γ) ^ 2 * tailProfile 29 (128 * γ) u +
      D * y * (4 * h) ^ 31 * ((2 : ℝ) ^ 29 / b ^ 29) * tailProfile 29 b u := by
    filter_upwards [(integrable_prod_iff hGep.aestronglyMeasurable).mp hGep |>.1] with u hi
    obtain ⟨hmi, hvmi, hm0, hm1⟩ := hmark y u hy
    have hs0 := actual_spectra_le_one ν h3 hV h hh hs m u
    have ht := four_region_slice_bound (fun v => Ge (u, v)) hi 2 (by norm_num) (by norm_num)
      A D (128 * γ) b (4 * h) y u (E u) 0 (Cfull / T ^ 6)
      hA.le hD.le hao hb hco hy (Real.exp_pos _).le le_rfl
      (by positivity) hmi hvmi hm0 hm1
      (hout _ _ _ hao hy hy2 hsmallA) (hout _ _ _ hco hy hy2 hsmallC)
      (fun v => by
        simpa only [Ge, Nat.reduceSub, pow_one, mul_one, mul_comm] using
          kernelMarkIntegrand_bound 1 (fun ξ => evenSpectrum ν m ξ.1 ξ.2) y w q u v 1 (hs0 v).2)
      (fun hu v hv => by
        have hl := (actual_spectra_low_bounds ν h3 hV h hh hs n m hmn hm6 hscale hbias hcomp u v
          (by simpa only [hbdef] using hu) (by simpa only [hfreq] using hv)).2
        convert kernelMarkIntegrand_bound 1 (fun ξ => evenSpectrum ν m ξ.1 ξ.2) y w q u v _ hl using 1 <;>
          dsimp [Ge, E, T] <;> ring)
      (fun hu v hv => by
        convert kernelMarkIntegrand_bound 1 (fun ξ => evenSpectrum ν m ξ.1 ξ.2) y w q u v _ (hcone u v hu hv).2 using 1 <;>
          dsimp [Ge] <;> ring)
    simpa only [Nat.reduceSub, pow_zero, pow_one, zero_mul, add_zero, Le] using ht
  have hIntO := four_region_integral_bound Go hGoi 1 (by norm_num) (by norm_num)
    A D P (128 * γ) b (4 * h) y (Cfull / T ^ 6) hA.le hD.le hao hb hco hy
    (by positivity) hprof Lo hLoLe.1 (by simpa only [Nat.reduceSub, pow_one] using hsliceO)
  have hIntE := four_region_integral_bound Ge hGei 2 (by norm_num) (by norm_num)
    A D P (128 * γ) b (4 * h) y (Cfull / T ^ 6) hA.le hD.le hao hb hco hy
    (by positivity) hprof Le hLoLe.2.1 hsliceE
  simp only [Nat.reduceSub, pow_one] at hIntO hIntE
  constructor
  · calc
      _ ≤ A * y * G * ((m : ℝ) * |μ| / (Real.sqrt T) ^ 3 +
          (m : ℝ) * m3 * (1 / (Real.sqrt T) ^ 5 +
            1 / (Real.sqrt T) ^ 3 + y / (Real.sqrt T) ^ 4)) +
          A * y * (Cfull / T ^ 6) * ((2 : ℝ) ^ 11 / b ^ 11) * (P * b) +
          D * y * (128 * γ) * (P * (128 * γ)) +
          D * y * (4 * h) ^ 31 * ((2 : ℝ) ^ 30 / b ^ 30) * (P * b) := by
        apply hIntO.trans
        gcongr
        exact hLoLe.2.2.1
      _ = (A * G) * y * ((m : ℝ) * |μ| / (Real.sqrt T) ^ 3 +
          (m : ℝ) * m3 * (1 / (Real.sqrt T) ^ 5 +
            1 / (Real.sqrt T) ^ 3 + y / (Real.sqrt T) ^ 4)) +
          (A * Cfull * P * 2 ^ 11 * 128 ^ 10) * y * (γ ^ 10 / T ^ 6) +
          (D * P * 128 ^ 2) * y * γ ^ 2 +
          (D * P * 4 ^ 31 * 2 ^ 30 * 128 ^ 29) * y * (h ^ 31 * γ ^ 29) := by
        dsimp only [b]
        field_simp <;> ring
      _ ≤ _ := by
        have hc := add_le_add (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right c0 (by positivity : 0 ≤ y *
            ((m : ℝ) * |μ| / (Real.sqrt T) ^ 3 + (m : ℝ) * m3 *
              (1 / (Real.sqrt T) ^ 5 + 1 / (Real.sqrt T) ^ 3 + y / (Real.sqrt T) ^ 4))))
          (mul_le_mul_of_nonneg_right c1 (by positivity : 0 ≤ y * (γ ^ 10 / T ^ 6))))
          (mul_le_mul_of_nonneg_right c2 (by positivity : 0 ≤ y * γ ^ 2)))
          (mul_le_mul_of_nonneg_right c3 (by positivity : 0 ≤ y * (h ^ 31 * γ ^ 29)))
        convert hc using 1 <;> ring
  · calc
      _ ≤ A * y * G / (Real.sqrt T) ^ 3 +
          A * y * (Cfull / T ^ 6) * ((2 : ℝ) ^ 10 / b ^ 10) * (P * b) +
          D * y * (128 * γ) ^ 2 * (P * (128 * γ)) +
          D * y * (4 * h) ^ 31 * ((2 : ℝ) ^ 29 / b ^ 29) * (P * b) := by
        apply hIntE.trans
        gcongr
        exact hLoLe.2.2.2
      _ = (A * G) * y * (1 / (Real.sqrt T) ^ 3) +
          (A * Cfull * P * 2 ^ 10 * 128 ^ 9) * y * (γ ^ 9 / T ^ 6) +
          (D * P * 128 ^ 3) * y * γ ^ 3 +
          (D * P * 4 ^ 31 * 2 ^ 29 * 128 ^ 28) * y * (h ^ 31 * γ ^ 28) := by
        dsimp only [b]
        field_simp <;> ring
      _ ≤ _ := by
        have hc := add_le_add (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right c0 (by positivity : 0 ≤ y * (1 / (Real.sqrt T) ^ 3)))
          (mul_le_mul_of_nonneg_right c4 (by positivity : 0 ≤ y * (γ ^ 9 / T ^ 6))))
          (mul_le_mul_of_nonneg_right c5 (by positivity : 0 ≤ y * γ ^ 3)))
          (mul_le_mul_of_nonneg_right c6 (by positivity : 0 ≤ y * (h ^ 31 * γ ^ 28)))
        convert hc using 1 <;> ring

theorem sourceTruncation_futureNoise_early_long_kernel_bounds_fixed_cutoff :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
          (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 →
          (∫ a : ℝ, a ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ (1 / 16384 : ℝ) →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            let ρ : Measure ℝ :=
              ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
            let mu : ℝ := ∫ a : ℝ, a ∂ρ
            let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
            let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
            let gamma : ℝ := m3 / variance (id : ℝ → ℝ) ρ
            ∀ y : ℝ, gamma ≤ y → y ≤ 2 →
              ∀ i : ℕ, 1 ≤ i → i ≤ n →
                let m : ℕ := n - i
                let T : ℝ := (m : ℝ) * m2
                let f : ℝ → ℝ → ℝ := fun q w => sourceFutureNoiseKernel ρ m y (w, q)
                let o : ℝ → ℝ → ℝ := fun q w => (f q w - f q (-w)) / 2
                let e : ℝ → ℝ → ℝ := fun q w => (f q w + f q (-w)) / 2
                (∀ w q : ℝ,
                  DifferentiableAt ℝ (o q) w ∧
                  DifferentiableAt ℝ (e q) w ∧
                  DifferentiableAt ℝ (fun r : ℝ => deriv (e q) r) w) ∧
                (i ≤ n / 2 → ∀ w q : ℝ,
                  |deriv (o q) w| ≤ C * ((n : ℝ) * |mu| + (n : ℝ) * m3) ∧
                  |deriv (fun r : ℝ => deriv (e q) r) w| ≤ C) ∧
                (n / 2 < i → max ((16384 : ℝ) * gamma ^ 2) (y ^ 2) ≤ T →
                  ∀ w q : ℝ,
                    |deriv (o q) w| ≤ C * y *
                      ((n : ℝ) * |mu| / Real.sqrt T +
                        (n : ℝ) * m3 / (Real.sqrt T) ^ 3) ∧
                    |deriv (fun r : ℝ => deriv (e q) r) w| ≤
                      C * y / (Real.sqrt T) ^ 3) := by
  obtain ⟨Cfull, hCfull, hfull⟩ := sourceTruncation_fullNoise_highFrequency_derivatives
  obtain ⟨K, hK, hfrequency⟩ := fixedCutoff_actual_frequency_pair_budgets Cfull hCfull.le
  let δ : ℝ := 1 / 16
  have hδ : 0 < δ := by norm_num [δ]
  have hδ16 : δ ≤ (1 / 16 : ℝ) := le_rfl
  let epsilon0 : ℝ := min (δ / 1024) (1 / 1024)
  let B : ℝ := ‖(2 * Complex.I / (((2 * Real.pi) ^ 2 : ℝ) : ℂ))‖ +
    ‖(-2 / (((2 * Real.pi) ^ 2 : ℝ) : ℂ))‖ + 1
  let C : ℝ := 512 * B * K
  have hB : 0 < B := by dsimp [B]; positivity
  have hBo : ‖(2 * Complex.I / (((2 * Real.pi) ^ 2 : ℝ) : ℂ))‖ ≤ B := by
    dsimp [B]
    linarith [norm_nonneg (-2 / (((2 * Real.pi) ^ 2 : ℝ) : ℂ))]
  have hBe : ‖(-2 / (((2 * Real.pi) ^ 2 : ℝ) : ℂ))‖ ≤ B := by
    dsimp [B]
    linarith [norm_nonneg (2 * Complex.I / (((2 * Real.pi) ^ 2 : ℝ) : ℂ))]
  have he0 : 0 < epsilon0 := lt_min (by positivity) (by norm_num)
  have he01 : epsilon0 ≤ 1 / 1024 := min_le_right _ _
  have he0δ : epsilon0 ≤ δ / 1024 := min_le_left _ _
  have he0fixed : epsilon0 = (1 / 16384 : ℝ) := by norm_num [epsilon0, δ]
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro ν0 hp0 n h2 hnorm hmean x epsilon hx he heFixed hbudget
  have he0bound : epsilon ≤ epsilon0 := by rw [he0fixed]; exact heFixed
  dsimp only
  intro y hγy hy2 i _hi1 hin
  letI := hp0
  let h : ℝ := epsilon / (1 + x)
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ h}
  let μ : ℝ := ∫ a : ℝ, a ∂ρ
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
  let γ : ℝ := m3 / variance (id : ℝ → ℝ) ρ
  let m : ℕ := n - i
  let T : ℝ := (m : ℝ) * m2
  let N0 : ℝ := (n : ℝ) * |μ|
  let N3 : ℝ := (n : ℝ) * m3
  let M0 : ℝ := (m : ℝ) * |μ|
  let M3 : ℝ := (m : ℝ) * m3
  let f : ℝ → ℝ → ℝ := fun q w => sourceFutureNoiseKernel ρ m y (w, q)
  let o : ℝ → ℝ → ℝ := fun q w => (f q w - f q (-w)) / 2
  let e : ℝ → ℝ → ℝ := fun q w => (f q w + f q (-w)) / 2
  have hehalf : epsilon ≤ 1 / 2 := by linarith
  have hh : 0 < h := div_pos he (by linarith)
  have hhε : h ≤ epsilon := by
    apply (div_le_iff₀ (by linarith : 0 < 1 + x)).mpr
    nlinarith only [mul_nonneg he.le hx]
  obtain ⟨_, _, hp, hs, _, h2r, h3r, _⟩ :=
    Shao.sourceTruncation_law_data ν0 n h2 hnorm x epsilon hx he hehalf hbudget
  have hprob : IsProbabilityMeasure ρ := hp
  letI := hprob
  have hsupport : ∀ᵐ a : ℝ ∂ρ, |a| ≤ h := hs
  have hcube : Integrable (fun a : ℝ => |a| ^ 3) ρ := h3r
  obtain ⟨hscale, hscaleHi, _, hVeq, _, hV, _, _⟩ :=
    Shao.sourceTruncation_variance_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget
  change (3 / 4 : ℝ) ≤ (n : ℝ) * m2 at hscale
  change (n : ℝ) * m2 ≤ (4 / 3 : ℝ) at hscaleHi
  change variance (id : ℝ → ℝ) ρ = m2 - μ ^ 2 at hVeq
  change 0 < variance (id : ℝ → ℝ) ρ at hV
  have hm2 : 0 < m2 := by nlinarith only [hV, hVeq, sq_nonneg μ]
  obtain ⟨hm3pos, hγ, _, _, hγh, _, hγN, _, _⟩ :=
    Shao.sourceTruncation_gamma_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget
  change 0 < m3 at hm3pos
  change 0 < γ at hγ
  change γ ≤ 2 * h at hγh
  replace hγN : γ ≤ 2 * N3 := by
    dsimp only [N3]
    nlinarith only [hγN]
  have hy : 0 ≤ y := hγ.le.trans hγy
  have hh1 : h ≤ 1 := by linarith
  have hγ1 : γ ≤ 1 := by linarith
  have hγsmall : γ ≤ 1 / 512 := by linarith
  have hsmallA : (128 * γ) * y ≤ δ := by
    have hp := mul_le_mul (hγh.trans (by linarith : 2 * h ≤ 2 * epsilon)) hy2 hy
      (by positivity : 0 ≤ 2 * epsilon)
    dsimp only [δ]
    nlinarith only [hp, heFixed]
  have hsmallC : (4 * h) * y ≤ δ := by
    have hp := mul_le_mul hhε hy2 hy he.le
    dsimp only [δ]
    nlinarith only [hp, heFixed]
  have hmn : m ≤ n := Nat.sub_le n i
  have hmnR : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
  have hThi : T ≤ 4 / 3 :=
    (mul_le_mul_of_nonneg_right hmnR hm2.le).trans hscaleHi
  have hN0 : 0 ≤ N0 := by dsimp [N0]; positivity
  have hN3 : 0 ≤ N3 := by dsimp [N3]; positivity
  have hM0 : 0 ≤ M0 := by dsimp [M0]; positivity
  have hM3 : 0 ≤ M3 := by dsimp [M3]; positivity
  have hM0N : M0 ≤ N0 := mul_le_mul_of_nonneg_right hmnR (abs_nonneg μ)
  have hM3N : M3 ≤ N3 := mul_le_mul_of_nonneg_right hmnR hm3pos.le
  have hratio : (m : ℝ) ≤ (4 / 3 : ℝ) * T * (n : ℝ) := by
    have hp := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg m)
    dsimp [T]
    nlinarith only [hp]
  have hM0T : M0 ≤ (4 / 3 : ℝ) * T * N0 := by
    convert mul_le_mul_of_nonneg_right hratio (abs_nonneg μ) using 1 <;> dsimp [M0, N0] <;> ring
  have hM3T : M3 ≤ (4 / 3 : ℝ) * T * N3 := by
    convert mul_le_mul_of_nonneg_right hratio hm3pos.le using 1 <;> dsimp [M3, N3] <;> ring
  have hQuant (hguard : (16384 : ℝ) * γ ^ 2 ≤ T) (w q : ℝ) :
      |deriv (o q) w| ≤ B * K * y * oddFrequencyBudget M0 M3 γ h T y ∧
      |deriv (fun r : ℝ => deriv (e q) r) w| ≤ B * K * y * evenFrequencyBudget γ h T := by
    have hTp : 0 < T := (mul_pos (by norm_num : (0 : ℝ) < 16384)
      (sq_pos_of_pos hγ)).trans_le hguard
    obtain ⟨_, hm6, _, hbias, hcomp⟩ :=
      Shao.sourceTruncation_oddPower_scale_inputs ν0 n h2 hnorm hmean x epsilon hx he hehalf
        hbudget i hin 16384 (by norm_num) hguard
    have hcone (u v : ℝ) (hu : 1 / (128 * γ) ≤ |u|) (hv : |v| ≤ |u| / (4 * h)) :
        ‖oddSpectrum ρ m u v‖ ≤ Cfull / (T ^ 6 * |u| ^ 12) ∧
        ‖evenSpectrum ρ m u v‖ ≤ Cfull / (T ^ 6 * |u| ^ 12) := by
      have hu0 : u ≠ 0 := by
        have hp : 0 < |u| := (by positivity : 0 < 1 / (128 * γ)).trans_le hu
        exact abs_pos.mp hp
      have huf : (1 / 128 : ℝ) / γ ≤ |u| := by convert hu using 1 <;> ring
      have hkL : 1 ≤ (1 / 128 : ℝ) * Real.sqrt 16384 := by
        rw [show (16384 : ℝ) = 128 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
        norm_num
      have hp := hfull ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hin
        h (1 / 128) 16384 le_rfl (by norm_num) (by norm_num) hkL hguard
        1 u v (by norm_num) hu0 huf hv
      have hn := hfull ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hin
        h (1 / 128) 16384 le_rfl (by norm_num) (by norm_num) hkL hguard
        (-1) u v (by norm_num) hu0 huf hv
      apply half_spectra_bound
      · simpa only [one_mul] using hp.2.2.1
      · simpa only [neg_one_mul] using hn.2.2.1
    obtain ⟨ho, he⟩ := hfrequency ρ hprob hcube hV h hh hsupport n m hmn hm6 hscale hbias hcomp
      hTp hγ y hy hy2 hsmallA hsmallC hcone w q
    change ‖∫ ξ, kernelMarkIntegrand 0 (fun ξ => oddSpectrum ρ m ξ.1 ξ.2) y w q ξ‖ ≤
      K * y * oddFrequencyBudget M0 M3 γ h T y at ho
    change ‖∫ ξ, kernelMarkIntegrand 1 (fun ξ => evenSpectrum ρ m ξ.1 ξ.2) y w q ξ‖ ≤
      K * y * evenFrequencyBudget γ h T at he
    have hf := actual_kernel_mark_formulas ρ hcube hV h hh hsupport m y hy w q
    constructor
    · calc
        _ = ‖((deriv (o q) w : ℝ) : ℂ)‖ := by simp only [Complex.norm_real, Real.norm_eq_abs]
        _ = ‖(2 * Complex.I / (((2 * Real.pi) ^ 2 : ℝ) : ℂ))‖ *
            ‖∫ ξ, kernelMarkIntegrand 0 (fun ξ => oddSpectrum ρ m ξ.1 ξ.2) y w q ξ‖ := by
          rw [hf.2.2.2.1, norm_mul]
        _ ≤ B * (K * y * oddFrequencyBudget M0 M3 γ h T y) :=
          mul_le_mul hBo ho (norm_nonneg _) hB.le
        _ = _ := by ring
    · calc
        _ = ‖((deriv (fun r : ℝ => deriv (e q) r) w : ℝ) : ℂ)‖ := by
          simp only [Complex.norm_real, Real.norm_eq_abs]
        _ = ‖(-2 / (((2 * Real.pi) ^ 2 : ℝ) : ℂ))‖ *
            ‖∫ ξ, kernelMarkIntegrand 1 (fun ξ => evenSpectrum ρ m ξ.1 ξ.2) y w q ξ‖ := by
          rw [hf.2.2.2.2, norm_mul]
        _ ≤ B * (K * y * evenFrequencyBudget γ h T) := mul_le_mul hBe he (norm_nonneg _) hB.le
        _ = _ := by ring
  refine ⟨fun w q => (actual_kernel_mark_formulas ρ hcube hV h hh hsupport m y hy w q).1, ?_, ?_⟩
  · intro hiearly w q
    have hne : n ≤ 2 * m := by dsimp [m]; omega
    have hneR : (n : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hne
    have hTearly : (3 / 8 : ℝ) ≤ T := by
      have hp := mul_le_mul_of_nonneg_right hneR hm2.le
      dsimp [T]
      nlinarith only [hp, hscale]
    have hγsquare := pow_le_pow_left₀ hγ.le hγsmall 2
    have hguard : (16384 : ℝ) * γ ^ 2 ≤ T := by nlinarith only [hγsquare, hTearly]
    have hTp : 0 < T := by linarith
    have hγT : γ ^ 2 ≤ T := by nlinarith only [hguard, sq_nonneg γ]
    have hr := (frequency_budget_scale_reduction N0 N3 M0 M3 γ h T y hN0 hN3 hM0 hM3 hM0N hM3N
      hγ hγ1 hh.le hh1 hγN hTp hThi hγT hγy hy2).1 hTearly
    have hq := hQuant hguard w q
    constructor
    · calc
        _ ≤ B * K * (y * oddFrequencyBudget M0 M3 γ h T y) := by convert hq.1 using 1 <;> ring
        _ ≤ B * K * (512 * (N0 + N3)) := mul_le_mul_of_nonneg_left hr.1 (by positivity)
        _ = _ := by dsimp [C, N0, N3]; ring
    · calc
        _ ≤ B * K * (y * evenFrequencyBudget γ h T) := by convert hq.2 using 1 <;> ring
        _ ≤ B * K * 512 := mul_le_mul_of_nonneg_left hr.2 (by positivity)
        _ = _ := by dsimp [C]; ring
  · intro _hilate hlong w q
    have hguard : (16384 : ℝ) * γ ^ 2 ≤ T := (le_max_left _ _).trans hlong
    have hyT : y ^ 2 ≤ T := (le_max_right _ _).trans hlong
    have hTp : 0 < T := (mul_pos (by norm_num : (0 : ℝ) < 16384)
      (sq_pos_of_pos hγ)).trans_le hguard
    have hγT : γ ^ 2 ≤ T := by nlinarith only [hguard, sq_nonneg γ]
    have hr := (frequency_budget_scale_reduction N0 N3 M0 M3 γ h T y hN0 hN3 hM0 hM3 hM0N hM3N
      hγ hγ1 hh.le hh1 hγN hTp hThi hγT hγy hy2).2 hM0T hM3T hyT
    have hq := hQuant hguard w q
    constructor
    · calc
        _ ≤ B * K * y * (512 * (N0 / Real.sqrt T + N3 / (Real.sqrt T) ^ 3)) :=
          hq.1.trans (mul_le_mul_of_nonneg_left hr.1 (by positivity))
        _ = _ := by dsimp [C, N0, N3]; ring
    · calc
        _ ≤ B * K * y * (512 / (Real.sqrt T) ^ 3) :=
          hq.2.trans (mul_le_mul_of_nonneg_left hr.2 (by positivity))
        _ = _ := by dsimp [C]; ring

/- END FIXED CUTOFF PUBLIC COMPANIONS. -/

end Shao.Probability
