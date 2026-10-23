import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory
open scoped ContDiff FourierTransform Topology

noncomputable def sourceMarkExponential (a : ℝ → ℝ) (y u v : ℝ) : ℂ :=
  ∫ r : ℝ, (a r : ℂ) *
    Complex.exp ((((u * y * Real.sqrt r - v * r : ℝ) : ℂ)) * Complex.I)

noncomputable def sourceMarkSine (a : ℝ → ℝ) (y u w v : ℝ) : ℂ :=
  ∫ r : ℝ, ((a r * Real.sin (u * (y * Real.sqrt r + w)) : ℝ) : ℂ) *
    Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I))

private lemma schwartz_sq_integrable (b : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => ‖b x‖ ^ 2) :=
  (memLp_two_iff_integrable_sq_norm b.continuous.aestronglyMeasurable).mp
    (b.memLp 2 volume)

private lemma fourier_deriv_norm (b : SchwartzMap ℝ ℂ) (v : ℝ) :
    ‖𝓕 (SchwartzMap.derivCLM ℂ ℂ b) v‖ =
      (2 * Real.pi) * (|v| * ‖𝓕 b v‖) := by
  have hd := congrFun (Real.fourier_deriv b.integrable b.differentiable
    (SchwartzMap.derivCLM ℂ ℂ b).integrable) v
  change ‖𝓕 (deriv (b : ℝ → ℂ)) v‖ =
    (2 * Real.pi) * (|v| * ‖𝓕 (b : ℝ → ℂ) v‖)
  rw [hd, norm_smul]
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
  ring

private lemma fourier_frequency_sq_integrable (b : SchwartzMap ℝ ℂ) :
    Integrable (fun v : ℝ => v ^ 2 * ‖𝓕 b v‖ ^ 2) ∧
      (∫ v : ℝ, v ^ 2 * ‖𝓕 b v‖ ^ 2) ≤
        ∫ r : ℝ, ‖SchwartzMap.derivCLM ℂ ℂ b r‖ ^ 2 := by
  let db := SchwartzMap.derivCLM ℂ ℂ b
  have hpi : 1 ≤ 2 * Real.pi := by nlinarith [Real.two_le_pi]
  have hp (v : ℝ) : v ^ 2 * ‖𝓕 b v‖ ^ 2 ≤ ‖𝓕 db v‖ ^ 2 := by
    have hn : 0 ≤ |v| * ‖𝓕 b v‖ := by positivity
    have hle : |v| * ‖𝓕 b v‖ ≤ ‖𝓕 db v‖ := by
      rw [fourier_deriv_norm]
      nlinarith
    have hh := pow_le_pow_left₀ hn hle 2
    simpa only [mul_pow, sq_abs] using hh
  have hi := schwartz_sq_integrable (𝓕 db)
  have hit : Integrable (fun v : ℝ => v ^ 2 * ‖𝓕 b v‖ ^ 2) := by
    refine hi.mono' (by fun_prop) (Filter.Eventually.of_forall fun v => ?_)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ v ^ 2 * ‖𝓕 b v‖ ^ 2)] using hp v
  refine ⟨hit, (integral_mono hit hi hp).trans_eq ?_⟩
  exact SchwartzMap.integral_norm_sq_fourier db

private lemma schwartz_fourier_L1_bound (b : SchwartzMap ℝ ℂ) (A R : ℝ)
    (hA : 0 ≤ A) (hR : 1 ≤ R)
    (h0 : (∫ r : ℝ, ‖b r‖ ^ 2) ≤ A ^ 2)
    (h1 : (∫ r : ℝ, ‖SchwartzMap.derivCLM ℂ ℂ b r‖ ^ 2) ≤ (A * R) ^ 2) :
    (∫ v : ℝ, ‖𝓕 b v‖) ≤ 4 * A * Real.sqrt R := by
  have hRp : 0 < R := by linarith
  have hRn : R ≠ 0 := ne_of_gt hRp
  let W : ℝ → ℝ := fun v => Real.sqrt ((1 + (v / R) ^ 2)⁻¹)
  let G : ℝ → ℝ := fun v => Real.sqrt (1 + (v / R) ^ 2) * ‖𝓕 b v‖
  have hbase (v : ℝ) : 0 < 1 + (v / R) ^ 2 := by positivity
  have hWsq (v : ℝ) : W v ^ 2 = (1 + (R⁻¹ * v) ^ 2)⁻¹ := by
    dsimp [W]
    rw [Real.sq_sqrt (by positivity)]
    congr 2
    ring
  have hiWsq : Integrable (fun v : ℝ => W v ^ 2) := by
    exact (integrable_inv_one_add_mul_sq (inv_ne_zero hRn)).congr
      (Filter.Eventually.of_forall fun v => (hWsq v).symm)
  have hW : MemLp W 2 volume :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr hiWsq
  have hWi : (∫ v : ℝ, W v ^ 2) = Real.pi * R := by
    simp_rw [hWsq]
    rw [integral_univ_inv_one_add_mul_sq, abs_of_pos (inv_pos.mpr hRp)]
    field_simp
  obtain ⟨hiT, hT⟩ := fourier_frequency_sq_integrable b
  have hiF := schwartz_sq_integrable (𝓕 b)
  have hGsq (v : ℝ) : G v ^ 2 =
      ‖𝓕 b v‖ ^ 2 + R⁻¹ ^ 2 * (v ^ 2 * ‖𝓕 b v‖ ^ 2) := by
    dsimp [G]
    rw [mul_pow, Real.sq_sqrt (hbase v).le]
    field_simp
    <;> ring
  have hiGsq : Integrable (fun v : ℝ => G v ^ 2) := by
    exact (hiF.add (hiT.const_mul (R⁻¹ ^ 2))).congr
      (Filter.Eventually.of_forall fun v => (hGsq v).symm)
  have hG : MemLp G 2 volume :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr hiGsq
  have hGi : (∫ v : ℝ, G v ^ 2) ≤ 2 * A ^ 2 := by
    simp_rw [hGsq]
    rw [integral_add hiF (hiT.const_mul _), integral_const_mul]
    have hf := (SchwartzMap.integral_norm_sq_fourier b).le.trans h0
    calc
      _ ≤ A ^ 2 + R⁻¹ ^ 2 * (A * R) ^ 2 :=
        add_le_add hf (mul_le_mul_of_nonneg_left (hT.trans h1) (sq_nonneg _))
      _ = 2 * A ^ 2 := by field_simp; ring
  have hprod (v : ℝ) : ‖W v‖ * ‖G v‖ = ‖𝓕 b v‖ := by
    have hs : Real.sqrt (1 + (v / R) ^ 2) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (hbase v))
    dsimp [W, G]
    rw [abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)),
      Real.sqrt_inv, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  have hh := integral_mul_norm_le_Lp_mul_Lq
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
      (2 : ℝ).HolderConjugate 2)
    (by simpa using hW) (by simpa using hG)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs] at hh
  simp_rw [← Real.norm_eq_abs, hprod] at hh
  rw [hWi] at hh
  have hwbound : Real.sqrt (Real.pi * R) ≤ 2 * Real.sqrt R := by
    calc
      _ ≤ Real.sqrt (4 * R) := Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_right Real.pi_le_four hRp.le)
      _ = 2 * Real.sqrt R := by
        have hs4 : Real.sqrt (4 : ℝ) = 2 := by
          simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
            using Real.sqrt_sq_eq_abs (2 : ℝ)
        rw [Real.sqrt_mul (by norm_num), hs4]
  have hgbound : Real.sqrt (∫ v : ℝ, G v ^ 2) ≤ 2 * A := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity, by nlinarith [sq_nonneg A]⟩
  calc
    _ ≤ Real.sqrt (Real.pi * R) * Real.sqrt (∫ v : ℝ, G v ^ 2) := hh
    _ ≤ (2 * Real.sqrt R) * (2 * A) :=
      mul_le_mul hwbound hgbound (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring

private lemma schwartz_fourier_norms (b : SchwartzMap ℝ ℂ) (A R : ℝ)
    (hA : 0 ≤ A) (hR : 1 ≤ R)
    (h0 : (∫ r : ℝ, ‖b r‖ ^ 2) ≤ A ^ 2)
    (h1 : (∫ r : ℝ, ‖SchwartzMap.derivCLM ℂ ℂ b r‖ ^ 2) ≤ (A * R) ^ 2)
    (h2 : (∫ r : ℝ, ‖SchwartzMap.derivCLM ℂ ℂ
      (SchwartzMap.derivCLM ℂ ℂ b) r‖ ^ 2) ≤ (A * R ^ 2) ^ 2) :
    Integrable (fun v : ℝ => ‖𝓕 b v‖) ∧
      Integrable (fun v : ℝ => |v| * ‖𝓕 b v‖) ∧
      (∫ v : ℝ, ‖𝓕 b v‖) ≤ 4 * A * Real.sqrt R ∧
      (∫ v : ℝ, |v| * ‖𝓕 b v‖) ≤ 4 * A * R * Real.sqrt R := by
  let db := SchwartzMap.derivCLM ℂ ℂ b
  have hi : Integrable (fun v : ℝ => |v| * ‖𝓕 b v‖) := by
    convert SchwartzMap.integrable_pow_mul volume (𝓕 b) 1 using 1
    congr 1
    funext v
    simp only [Real.norm_eq_abs, pow_one]
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
  have hp (v : ℝ) : |v| * ‖𝓕 b v‖ ≤ ‖𝓕 db v‖ := by
    rw [fourier_deriv_norm]
    nlinarith [mul_nonneg (abs_nonneg v) (norm_nonneg (𝓕 b v))]
  refine ⟨(𝓕 b).integrable.norm, hi, schwartz_fourier_L1_bound b A R hA hR h0 h1, ?_⟩
  have hh := schwartz_fourier_L1_bound db (A * R) R (by positivity) hR h1
    (by simpa only [mul_assoc, pow_two] using h2)
  exact (integral_mono hi (𝓕 db).integrable.norm hp).trans (by simpa only [mul_assoc] using hh)

private noncomputable def unitFourier (b : ℝ → ℂ) (v : ℝ) : ℂ :=
  ∫ r : ℝ, b r * Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I))

private lemma unitFourier_eq (b : ℝ → ℂ) (v : ℝ) :
    unitFourier b v = 𝓕 b (v / (2 * Real.pi)) := by
  unfold unitFourier
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with r
  simp only [smul_eq_mul]
  rw [mul_comm (b r)]
  congr 1
  congr 1
  push_cast
  field_simp
  <;> ring

private lemma unitFourier_schwartz_norms (b : SchwartzMap ℝ ℂ) (A R : ℝ)
    (hA : 0 ≤ A) (hR : 1 ≤ R)
    (h0 : (∫ r : ℝ, ‖b r‖ ^ 2) ≤ A ^ 2)
    (h1 : (∫ r : ℝ, ‖SchwartzMap.derivCLM ℂ ℂ b r‖ ^ 2) ≤ (A * R) ^ 2)
    (h2 : (∫ r : ℝ, ‖SchwartzMap.derivCLM ℂ ℂ
      (SchwartzMap.derivCLM ℂ ℂ b) r‖ ^ 2) ≤ (A * R ^ 2) ^ 2) :
    Integrable (fun v : ℝ => ‖unitFourier b v‖) ∧
      Integrable (fun v : ℝ => |v| * ‖unitFourier b v‖) ∧
      (∫ v : ℝ, ‖unitFourier b v‖) ≤ 256 * A * Real.sqrt R ∧
      (∫ v : ℝ, |v| * ‖unitFourier b v‖) ≤ 256 * A * R * Real.sqrt R := by
  obtain ⟨hi0, hi1, hb0, hb1⟩ := schwartz_fourier_norms b A R hA hR h0 h1 h2
  let c := 2 * Real.pi
  have hcp : 0 < c := by dsimp [c]; positivity
  have hcn : c ≠ 0 := ne_of_gt hcp
  have hc8 : c ≤ 8 := by dsimp [c]; linarith [Real.pi_le_four]
  have he (v : ℝ) : unitFourier b v = 𝓕 b (c⁻¹ * v) := by
    rw [unitFourier_eq, div_eq_mul_inv, mul_comm]
    rfl
  have hiu0 : Integrable (fun v : ℝ => ‖unitFourier b v‖) := by
    simpa only [he, SchwartzMap.fourier_coe] using
      hi0.comp_mul_left' (inv_ne_zero hcn)
  have he1 (v : ℝ) : |v| * ‖unitFourier b v‖ =
      c * (|c⁻¹ * v| * ‖𝓕 b (c⁻¹ * v)‖) := by
    rw [he, abs_mul, abs_of_pos (inv_pos.mpr hcp)]
    field_simp
  have hiu1 : Integrable (fun v : ℝ => |v| * ‖unitFourier b v‖) := by
    exact ((hi1.comp_mul_left' (inv_ne_zero hcn)).const_mul c).congr
      (Filter.Eventually.of_forall fun v => (he1 v).symm)
  have hs0 : (∫ v : ℝ, ‖unitFourier b v‖) = c * ∫ v : ℝ, ‖𝓕 b v‖ := by
    simp_rw [he]
    rw [Measure.integral_comp_mul_left (fun v : ℝ => ‖𝓕 b v‖) (c⁻¹)]
    simp only [abs_of_pos (inv_pos.mpr hcp), inv_inv, smul_eq_mul, abs_of_pos hcp]
  have hs1 : (∫ v : ℝ, |v| * ‖unitFourier b v‖) =
      c ^ 2 * ∫ v : ℝ, |v| * ‖𝓕 b v‖ := by
    simp_rw [he1]
    rw [integral_const_mul,
      Measure.integral_comp_mul_left (fun v : ℝ => |v| * ‖𝓕 b v‖) (c⁻¹)]
    simp only [abs_of_pos (inv_pos.mpr hcp), inv_inv, smul_eq_mul, abs_of_pos hcp]
    ring
  refine ⟨hiu0, hiu1, ?_, ?_⟩
  · rw [hs0]
    calc
      _ ≤ c * (4 * A * Real.sqrt R) := mul_le_mul_of_nonneg_left hb0 hcp.le
      _ ≤ 256 * A * Real.sqrt R := by nlinarith [mul_nonneg hA (Real.sqrt_nonneg R)]
  · rw [hs1]
    calc
      _ ≤ c ^ 2 * (4 * A * R * Real.sqrt R) :=
        mul_le_mul_of_nonneg_left hb1 (sq_nonneg _)
      _ ≤ 256 * A * R * Real.sqrt R := by
        have hc64 : c ^ 2 ≤ 64 := by nlinarith
        nlinarith [mul_nonneg (mul_nonneg hA (by linarith : 0 ≤ R)) (Real.sqrt_nonneg R)]

private lemma supported_mul_smooth (a0 a1 : ℝ) (ha0 : 0 < a0)
    (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ Set.Icc a0 a1)
    (g : ℝ → ℂ) (hg : ∀ r : ℝ, 0 < r → ContDiffAt ℝ ∞ g r) :
    ContDiff ℝ ∞ (fun r : ℝ => (a r : ℂ) * g r) ∧
      tsupport (fun r : ℝ => (a r : ℂ) * g r) ⊆ Set.Icc a0 a1 := by
  have haC : ContDiff ℝ ∞ (fun r : ℝ => (a r : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ha
  constructor
  · apply contDiff_iff_contDiffAt.mpr
    intro r
    by_cases hr : 0 < r
    · exact haC.contDiffAt.mul (hg r hr)
    · have hn : r ∉ tsupport a := by
        intro hh
        exact hr (lt_of_lt_of_le ha0 (hs hh).1)
      have hz := notMem_tsupport_iff_eventuallyEq.mp hn
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℂ)) r).congr_of_eventuallyEq
      filter_upwards [hz] with x hx
      simp [hx]
  · apply closure_minimal ?_ isClosed_Icc
    intro r hr
    have hn : a r ≠ 0 := by
      intro hz
      exact hr (by simp [hz])
    exact hs (subset_closure hn)

private lemma product_derivatives (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
    (g : ℝ → ℂ) (hg : ∀ r : ℝ, 0 < r → ContDiffAt ℝ ∞ g r)
    (r : ℝ) (hr : 0 < r) :
    deriv (fun x : ℝ => (a x : ℂ) * g x) r =
        ((deriv a r : ℝ) : ℂ) * g r + (a r : ℂ) * deriv g r ∧
      deriv (deriv (fun x : ℝ => (a x : ℂ) * g x)) r =
        ((deriv (deriv a) r : ℝ) : ℂ) * g r +
          2 * ((deriv a r : ℝ) : ℂ) * deriv g r + (a r : ℂ) * deriv (deriv g) r := by
  have hda : ContDiff ℝ ∞ (deriv a) := (contDiff_infty_iff_deriv.mp ha).2
  have hf (x : ℝ) := ((ha.differentiable (by simp)).differentiableAt (x := x)).hasDerivAt.ofReal_comp
  have hdf := ((hda.differentiable (by simp)).differentiableAt (x := r)).hasDerivAt.ofReal_comp
  have hgg (x : ℝ) (hx : 0 < x) := (hg x hx).differentiableAt (by simp)
  have hgd := ((hg r hr).derivWithin (m := ∞) (by simp)).differentiableAt (by simp)
  have he : deriv (fun x : ℝ => (a x : ℂ) * g x) =ᶠ[𝓝 r]
      (fun x : ℝ => ((deriv a x : ℝ) : ℂ) * g x + (a x : ℂ) * deriv g x) := by
    filter_upwards [lt_mem_nhds hr] with x hx
    exact ((hf x).mul (hgg x hx).hasDerivAt).deriv
  refine ⟨((hf r).mul (hgg r hr).hasDerivAt).deriv, ?_⟩
  rw [he.deriv_eq]
  have hd := ((hdf.mul (hgg r hr).hasDerivAt).add ((hf r).mul hgd.hasDerivAt)).deriv
  change deriv (fun x : ℝ => ((deriv a x : ℝ) : ℂ) * g x + (a x : ℂ) * deriv g x) r = _ at hd
  rw [hd]
  ring

private lemma supported_sq_bound (a0 a1 : ℝ) (ha1 : a0 ≤ a1)
    (b : SchwartzMap ℝ ℂ) (hs : tsupport b ⊆ Set.Icc a0 a1)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ r ∈ Set.Icc a0 a1, ‖b r‖ ≤ B) :
    (∫ r : ℝ, ‖b r‖ ^ 2) ≤ (B * Real.sqrt (1 + (a1 - a0))) ^ 2 := by
  have hi : Integrable ((Set.Icc a0 a1).indicator (fun _ : ℝ => B ^ 2)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const isCompact_Icc.measure_ne_top)
  have hp (r : ℝ) : ‖b r‖ ^ 2 ≤ (Set.Icc a0 a1).indicator (fun _ => B ^ 2) r := by
    by_cases hr : r ∈ Set.Icc a0 a1
    · rw [Set.indicator_of_mem hr]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb r hr) 2
    · have hz : b r = 0 := by
        by_contra hn
        exact hr (hs (subset_closure hn))
      simp [Set.indicator_of_notMem hr, hz]
  have hbound := integral_mono (schwartz_sq_integrable b) hi hp
  have hint : (∫ r : ℝ, (Set.Icc a0 a1).indicator (fun _ => B ^ 2) r) =
      (a1 - a0) * B ^ 2 := by
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ha1, intervalIntegral.integral_const]
    rfl
  rw [hint] at hbound
  rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 + (a1 - a0))]
  nlinarith [sq_nonneg B]

private lemma product_norm_bounds (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
    (g : ℝ → ℂ) (hg : ∀ r : ℝ, 0 < r → ContDiffAt ℝ ∞ g r)
    (M G0 G1 G2 : ℝ) (hM : 0 ≤ M)
    (r : ℝ) (hr : 0 < r)
    (haB : |a r| ≤ M ∧ |deriv a r| ≤ M ∧ |deriv (deriv a) r| ≤ M)
    (hgB : ‖g r‖ ≤ G0 ∧ ‖deriv g r‖ ≤ G1 ∧ ‖deriv (deriv g) r‖ ≤ G2) :
    ‖(a r : ℂ) * g r‖ ≤ M * G0 ∧
      ‖deriv (fun x : ℝ => (a x : ℂ) * g x) r‖ ≤ M * (G0 + G1) ∧
      ‖deriv (deriv (fun x : ℝ => (a x : ℂ) * g x)) r‖ ≤ M * (G0 + 2 * G1 + G2) := by
  have hh0 := mul_le_mul haB.1 hgB.1 (norm_nonneg _) hM
  have hh1 := mul_le_mul haB.2.1 hgB.2.1 (norm_nonneg _) hM
  have hh2 := mul_le_mul haB.2.2 hgB.2.2 (norm_nonneg _) hM
  have h10 := mul_le_mul haB.2.1 hgB.1 (norm_nonneg _) hM
  have h01 := mul_le_mul haB.1 hgB.2.1 (norm_nonneg _) hM
  have h20 := mul_le_mul haB.2.2 hgB.1 (norm_nonneg _) hM
  have h02 := mul_le_mul haB.1 hgB.2.2 (norm_nonneg _) hM
  obtain ⟨hd1, hd2⟩ := product_derivatives a ha g hg r hr
  refine ⟨by simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using hh0, ?_, ?_⟩
  · rw [hd1]
    have htri := norm_add_le (((deriv a r : ℝ) : ℂ) * g r) ((a r : ℂ) * deriv g r)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs] at htri
    nlinarith
  · rw [hd2]
    have htri := (norm_add_le
      (((deriv (deriv a) r : ℝ) : ℂ) * g r + 2 * ((deriv a r : ℝ) : ℂ) * deriv g r)
      ((a r : ℂ) * deriv (deriv g) r)).trans
      (add_le_add (norm_add_le
        (((deriv (deriv a) r : ℝ) : ℂ) * g r)
        (2 * ((deriv a r : ℝ) : ℂ) * deriv g r)) (le_refl _))
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs] at htri
    nlinarith

private noncomputable def phaseSlope (t r : ℝ) : ℝ := t / (2 * Real.sqrt r)
private noncomputable def phaseCurvature (t r : ℝ) : ℝ := -t / (4 * Real.sqrt r ^ 3)
private noncomputable def markExpPhase (t s r : ℝ) : ℂ :=
  Complex.exp (((t * Real.sqrt r + s : ℝ) : ℂ) * Complex.I)
private noncomputable def markSinPhase (t s r : ℝ) : ℂ :=
  (Real.sin (t * Real.sqrt r + s) : ℂ)

private lemma argument_hasDerivAt (t s r : ℝ) (hr : 0 < r) :
    HasDerivAt (fun x : ℝ => t * Real.sqrt x + s) (phaseSlope t r) r := by
  convert ((Real.hasDerivAt_sqrt (ne_of_gt hr)).const_mul t).add_const s using 1 <;>
    dsimp [phaseSlope] <;> ring

private lemma slope_hasDerivAt (t r : ℝ) (hr : 0 < r) :
    HasDerivAt (phaseSlope t) (phaseCurvature t r) r := by
  have hs : Real.sqrt r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hr)
  convert (hasDerivAt_const r t).div
    ((Real.hasDerivAt_sqrt (ne_of_gt hr)).const_mul 2) (mul_ne_zero (by norm_num) hs) using 1
  · rfl
  · dsimp [phaseCurvature]
    field_simp
    <;> ring

private lemma markExpPhase_smooth (t s r : ℝ) (hr : 0 < r) :
    ContDiffAt ℝ ∞ (markExpPhase t s) r := by
  have hp : ContDiffAt ℝ ∞ (fun x : ℝ => t * Real.sqrt x + s) r :=
    (contDiffAt_const.mul (Real.contDiffAt_sqrt (n := ∞) (ne_of_gt hr))).add contDiffAt_const
  have hpC := Complex.ofRealCLM.contDiff.contDiffAt.comp r hp
  exact (hpC.mul contDiffAt_const).cexp

private lemma markSinPhase_smooth (t s r : ℝ) (hr : 0 < r) :
    ContDiffAt ℝ ∞ (markSinPhase t s) r := by
  have hp : ContDiffAt ℝ ∞ (fun x : ℝ => t * Real.sqrt x + s) r :=
    (contDiffAt_const.mul (Real.contDiffAt_sqrt (n := ∞) (ne_of_gt hr))).add contDiffAt_const
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp r hp.sin

private lemma markExpPhase_hasDerivAt (t s r : ℝ) (hr : 0 < r) :
    HasDerivAt (markExpPhase t s)
      (((phaseSlope t r : ℝ) : ℂ) * Complex.I * markExpPhase t s r) r := by
  convert ((argument_hasDerivAt t s r hr).ofReal_comp.mul_const Complex.I).cexp using 1
  all_goals try rfl
  all_goals try dsimp [markExpPhase]
  all_goals ring

private lemma markSinPhase_hasDerivAt (t s r : ℝ) (hr : 0 < r) :
    HasDerivAt (markSinPhase t s)
      ((Real.cos (t * Real.sqrt r + s) * phaseSlope t r : ℝ) : ℂ) r := by
  exact (argument_hasDerivAt t s r hr).sin.ofReal_comp

private lemma markExpPhase_second (t s r : ℝ) (hr : 0 < r) :
    deriv (deriv (markExpPhase t s)) r =
      (((phaseCurvature t r : ℝ) : ℂ) * Complex.I -
        ((phaseSlope t r : ℝ) : ℂ) ^ 2) * markExpPhase t s r := by
  have he : deriv (markExpPhase t s) =ᶠ[𝓝 r]
      (fun x : ℝ => ((phaseSlope t x : ℝ) : ℂ) * Complex.I * markExpPhase t s x) := by
    filter_upwards [lt_mem_nhds hr] with x hx
    exact (markExpPhase_hasDerivAt t s x hx).deriv
  rw [he.deriv_eq]
  have hd := (((slope_hasDerivAt t r hr).ofReal_comp.mul_const Complex.I).mul
    (markExpPhase_hasDerivAt t s r hr)).deriv
  change deriv (fun x : ℝ => ((phaseSlope t x : ℝ) : ℂ) * Complex.I * markExpPhase t s x) r = _ at hd
  rw [hd]
  ring_nf
  simp only [Complex.I_sq]
  ring

private lemma markSinPhase_second (t s r : ℝ) (hr : 0 < r) :
    deriv (deriv (markSinPhase t s)) r =
      ((Real.cos (t * Real.sqrt r + s) * phaseCurvature t r -
        Real.sin (t * Real.sqrt r + s) * phaseSlope t r ^ 2 : ℝ) : ℂ) := by
  have he : deriv (markSinPhase t s) =ᶠ[𝓝 r]
      (fun x : ℝ => ((Real.cos (t * Real.sqrt x + s) * phaseSlope t x : ℝ) : ℂ)) := by
    filter_upwards [lt_mem_nhds hr] with x hx
    exact (markSinPhase_hasDerivAt t s x hx).deriv
  rw [he.deriv_eq]
  have hd := (((argument_hasDerivAt t s r hr).cos.mul (slope_hasDerivAt t r hr)).ofReal_comp).deriv
  change deriv (fun x : ℝ => ((Real.cos (t * Real.sqrt x + s) * phaseSlope t x : ℝ) : ℂ)) r = _ at hd
  rw [hd]
  push_cast
  ring

private noncomputable def slopeBound (a0 : ℝ) : ℝ := 1 / (2 * Real.sqrt a0)
private noncomputable def curvatureBound (a0 : ℝ) : ℝ := 1 / (4 * Real.sqrt a0 ^ 3)

private lemma phase_coefficient_bounds (a0 : ℝ) (ha0 : 0 < a0)
    (t r : ℝ) (hr : a0 ≤ r) :
    |phaseSlope t r| ≤ slopeBound a0 * |t| ∧
      |phaseCurvature t r| ≤ curvatureBound a0 * |t| := by
  have hrp : 0 < r := lt_of_lt_of_le ha0 hr
  have hs0 : 0 < Real.sqrt a0 := Real.sqrt_pos.mpr ha0
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hrp
  have hs : Real.sqrt a0 ≤ Real.sqrt r := Real.sqrt_le_sqrt hr
  constructor
  · dsimp [phaseSlope, slopeBound]
    rw [abs_div, abs_of_pos (mul_pos (by norm_num) hsr)]
    calc
      _ ≤ |t| / (2 * Real.sqrt a0) :=
        div_le_div_of_nonneg_left (abs_nonneg t) (by positivity) (by linarith)
      _ = _ := by ring
  · dsimp [phaseCurvature, curvatureBound]
    rw [abs_div, abs_neg, abs_of_pos (by positivity : 0 < 4 * Real.sqrt r ^ 3)]
    calc
      _ ≤ |t| / (4 * Real.sqrt a0 ^ 3) :=
        div_le_div_of_nonneg_left (abs_nonneg t) (by positivity) (by gcongr)
      _ = _ := by ring

private lemma markExpPhase_norm (t s r : ℝ) : ‖markExpPhase t s r‖ = 1 := by
  simp [markExpPhase, Complex.norm_exp, Complex.mul_re]

private lemma markExpPhase_norm_bounds (a0 : ℝ) (ha0 : 0 < a0)
    (t s r : ℝ) (hr : a0 ≤ r) :
    ‖markExpPhase t s r‖ ≤ 1 ∧
      ‖deriv (markExpPhase t s) r‖ ≤ slopeBound a0 * |t| ∧
      ‖deriv (deriv (markExpPhase t s)) r‖ ≤
        curvatureBound a0 * |t| + slopeBound a0 ^ 2 * |t| ^ 2 := by
  have hrp := lt_of_lt_of_le ha0 hr
  obtain ⟨hb1, hb2⟩ := phase_coefficient_bounds a0 ha0 t r hr
  refine ⟨(markExpPhase_norm t s r).le, ?_, ?_⟩
  · rw [(markExpPhase_hasDerivAt t s r hrp).deriv]
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      markExpPhase_norm, mul_one] using hb1
  · rw [markExpPhase_second t s r hrp, norm_mul, markExpPhase_norm, mul_one]
    have ht := norm_sub_le (((phaseCurvature t r : ℝ) : ℂ) * Complex.I)
      (((phaseSlope t r : ℝ) : ℂ) ^ 2)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one, norm_pow] at ht
    have hb1sq := pow_le_pow_left₀ (abs_nonneg (phaseSlope t r)) hb1 2
    nlinarith

private lemma markSinPhase_norm_bounds (a0 a1 : ℝ) (ha0 : 0 < a0)
    (t s r : ℝ) (hr : r ∈ Set.Icc a0 a1) :
    ‖markSinPhase t s r‖ ≤ 1 ∧
      ‖markSinPhase t s r‖ ≤ |t| * Real.sqrt a1 + |s| ∧
      ‖deriv (markSinPhase t s) r‖ ≤ slopeBound a0 * |t| ∧
      ‖deriv (deriv (markSinPhase t s)) r‖ ≤
        curvatureBound a0 * |t| + slopeBound a0 ^ 2 * |t| ^ 2 := by
  have hrp := lt_of_lt_of_le ha0 hr.1
  obtain ⟨hb1, hb2⟩ := phase_coefficient_bounds a0 ha0 t r hr.1
  have hsin := Real.abs_sin_le_one (t * Real.sqrt r + s)
  have hcos := Real.abs_cos_le_one (t * Real.sqrt r + s)
  have harg : |t * Real.sqrt r + s| ≤ |t| * Real.sqrt a1 + |s| := by
    calc
      _ ≤ |t * Real.sqrt r| + |s| := abs_add_le _ _
      _ = |t| * Real.sqrt r + |s| := by rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ _ := by gcongr; exact hr.2
  refine ⟨by simpa only [markSinPhase, Complex.norm_real, Real.norm_eq_abs] using hsin,
    ?_, ?_, ?_⟩
  · simpa only [markSinPhase, Complex.norm_real, Real.norm_eq_abs] using
      Real.abs_sin_le_abs.trans harg
  · rw [(markSinPhase_hasDerivAt t s r hrp).deriv, Complex.norm_real,
      Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_right hcos (abs_nonneg _)).trans (by simpa using hb1)
  · rw [markSinPhase_second t s r hrp, Complex.norm_real, Real.norm_eq_abs]
    have ht := norm_sub_le (Real.cos (t * Real.sqrt r + s) * phaseCurvature t r)
      (Real.sin (t * Real.sqrt r + s) * phaseSlope t r ^ 2)
    simp only [Real.norm_eq_abs, abs_mul, abs_pow] at ht
    have hc := mul_le_mul_of_nonneg_right hcos (abs_nonneg (phaseCurvature t r))
    have hs := mul_le_mul_of_nonneg_right hsin (sq_nonneg |phaseSlope t r|)
    have hb1sq := pow_le_pow_left₀ (abs_nonneg (phaseSlope t r)) hb1 2
    nlinarith

private lemma supported_unit_budget (a0 a1 : ℝ) (ha0 : 0 < a0) (ha1 : a0 ≤ a1)
    (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ Set.Icc a0 a1)
    (g : ℝ → ℂ) (hg : ∀ r : ℝ, 0 < r → ContDiffAt ℝ ∞ g r)
    (A R : ℝ) (hA : 0 ≤ A) (hR : 1 ≤ R)
    (hb : ∀ r ∈ Set.Icc a0 a1,
      ‖(a r : ℂ) * g r‖ ≤ A ∧
        ‖deriv (fun x : ℝ => (a x : ℂ) * g x) r‖ ≤ A * R ∧
        ‖deriv (deriv (fun x : ℝ => (a x : ℂ) * g x)) r‖ ≤ A * R ^ 2) :
    Integrable (fun v : ℝ => ‖unitFourier (fun x => (a x : ℂ) * g x) v‖) ∧
      Integrable (fun v : ℝ => |v| * ‖unitFourier (fun x => (a x : ℂ) * g x) v‖) ∧
      (∫ v : ℝ, ‖unitFourier (fun x => (a x : ℂ) * g x) v‖) ≤
        256 * A * Real.sqrt (1 + (a1 - a0)) * Real.sqrt R ∧
      (∫ v : ℝ, |v| * ‖unitFourier (fun x => (a x : ℂ) * g x) v‖) ≤
        256 * A * Real.sqrt (1 + (a1 - a0)) * R * Real.sqrt R := by
  obtain ⟨hc, hsup⟩ := supported_mul_smooth a0 a1 ha0 a ha hs g hg
  have hcompact : HasCompactSupport (fun x : ℝ => (a x : ℂ) * g x) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsup
  let b : SchwartzMap ℝ ℂ := hcompact.toSchwartzMap hc
  let db := SchwartzMap.derivCLM ℂ ℂ b
  let ddb := SchwartzMap.derivCLM ℂ ℂ db
  have hsupb : tsupport b ⊆ Set.Icc a0 a1 := hsup
  have hsupdb : tsupport db ⊆ Set.Icc a0 a1 :=
    (SchwartzMap.tsupport_derivCLM_subset ℂ b).trans hsupb
  have hsupddb : tsupport ddb ⊆ Set.Icc a0 a1 :=
    (SchwartzMap.tsupport_derivCLM_subset ℂ db).trans hsupdb
  have h0 := supported_sq_bound a0 a1 ha1 b hsupb A hA (fun r hr => (hb r hr).1)
  have h1 := supported_sq_bound a0 a1 ha1 db hsupdb (A * R) (by positivity)
    (fun r hr => (hb r hr).2.1)
  have h2 := supported_sq_bound a0 a1 ha1 ddb hsupddb (A * R ^ 2) (by positivity)
    (fun r hr => (hb r hr).2.2)
  have he1 : (A * R * Real.sqrt (1 + (a1 - a0))) ^ 2 =
      (A * Real.sqrt (1 + (a1 - a0)) * R) ^ 2 := by ring
  have he2 : (A * R ^ 2 * Real.sqrt (1 + (a1 - a0))) ^ 2 =
      (A * Real.sqrt (1 + (a1 - a0)) * R ^ 2) ^ 2 := by ring
  rw [he1] at h1
  rw [he2] at h2
  have hbudget := unitFourier_schwartz_norms b (A * Real.sqrt (1 + (a1 - a0))) R
    (by positivity) hR h0 h1 h2
  have hbcoe : (b : ℝ → ℂ) = (fun x : ℝ => (a x : ℂ) * g x) := rfl
  rw [hbcoe] at hbudget
  simpa only [mul_assoc] using hbudget

private noncomputable def largeBudget (a0 : ℝ) : ℝ :=
  1 + 2 * slopeBound a0 + curvatureBound a0 + slopeBound a0 ^ 2

private noncomputable def smallBudget (a0 a1 : ℝ) : ℝ :=
  Real.sqrt a1 + 1 / 16 + 2 * slopeBound a0 + curvatureBound a0 + slopeBound a0 ^ 2

private lemma largeBudget_pos (a0 : ℝ) : 0 < largeBudget a0 := by
  dsimp [largeBudget, slopeBound, curvatureBound]
  positivity

private lemma smallBudget_pos (a0 a1 : ℝ) : 0 < smallBudget a0 a1 := by
  dsimp [smallBudget, slopeBound, curvatureBound]
  positivity

private lemma large_product_bounds (a0 a1 : ℝ) (ha0 : 0 < a0)
    (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
    (g : ℝ → ℂ) (hg : ∀ r : ℝ, 0 < r → ContDiffAt ℝ ∞ g r)
    (M T : ℝ) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (haB : ∀ r : ℝ, |a r| ≤ M ∧ |deriv a r| ≤ M ∧ |deriv (deriv a) r| ≤ M)
    (hgB : ∀ r ∈ Set.Icc a0 a1,
      ‖g r‖ ≤ 1 ∧ ‖deriv g r‖ ≤ slopeBound a0 * T ∧
        ‖deriv (deriv g) r‖ ≤ curvatureBound a0 * T + slopeBound a0 ^ 2 * T ^ 2) :
    ∀ r ∈ Set.Icc a0 a1,
      ‖(a r : ℂ) * g r‖ ≤ M * largeBudget a0 ∧
        ‖deriv (fun x : ℝ => (a x : ℂ) * g x) r‖ ≤ M * largeBudget a0 * (1 + T) ∧
        ‖deriv (deriv (fun x : ℝ => (a x : ℂ) * g x)) r‖ ≤
          M * largeBudget a0 * (1 + T) ^ 2 := by
  have hc1 : 0 ≤ slopeBound a0 := by dsimp [slopeBound]; positivity
  have hc2 : 0 ≤ curvatureBound a0 := by dsimp [curvatureBound]; positivity
  have hD1 : 1 ≤ largeBudget a0 := by
    dsimp [largeBudget]
    nlinarith [sq_nonneg (slopeBound a0)]
  have hD2 : 1 + slopeBound a0 ≤ largeBudget a0 := by
    dsimp [largeBudget]
    nlinarith [sq_nonneg (slopeBound a0)]
  have h11 : (1 : ℝ) ≤ (1 + T) ^ 2 := by nlinarith [sq_nonneg T]
  have hT1 : T ≤ 1 + T := by linarith
  have hT2 : T ≤ (1 + T) ^ 2 := by nlinarith [sq_nonneg T]
  have hTT : T ^ 2 ≤ (1 + T) ^ 2 := by nlinarith
  have hp1 : 1 + slopeBound a0 * T ≤ largeBudget a0 * (1 + T) := by
    calc
      _ ≤ (1 + T) + slopeBound a0 * (1 + T) :=
        add_le_add (by linarith) (mul_le_mul_of_nonneg_left hT1 hc1)
      _ = (1 + slopeBound a0) * (1 + T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD2 (by positivity)
  have hp2 : 1 + 2 * (slopeBound a0 * T) +
      (curvatureBound a0 * T + slopeBound a0 ^ 2 * T ^ 2) ≤
      largeBudget a0 * (1 + T) ^ 2 := by
    calc
      _ ≤ (1 + T) ^ 2 + 2 * (slopeBound a0 * (1 + T) ^ 2) +
          (curvatureBound a0 * (1 + T) ^ 2 + slopeBound a0 ^ 2 * (1 + T) ^ 2) := by
        gcongr <;> assumption
      _ = _ := by dsimp [largeBudget]; ring
  intro r hr
  obtain ⟨hb0, hb1, hb2⟩ := product_norm_bounds a ha g hg M 1
    (slopeBound a0 * T) (curvatureBound a0 * T + slopeBound a0 ^ 2 * T ^ 2)
    hM r (lt_of_lt_of_le ha0 hr.1) (haB r) (hgB r hr)
  refine ⟨hb0.trans ?_, hb1.trans ?_, hb2.trans ?_⟩
  · exact mul_le_mul_of_nonneg_left hD1 hM
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp1 hM
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp2 hM

private lemma small_product_bounds (a0 a1 : ℝ) (ha0 : 0 < a0)
    (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
    (g : ℝ → ℂ) (hg : ∀ r : ℝ, 0 < r → ContDiffAt ℝ ∞ g r)
    (M T : ℝ) (hM : 0 ≤ M) (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (haB : ∀ r : ℝ, |a r| ≤ M ∧ |deriv a r| ≤ M ∧ |deriv (deriv a) r| ≤ M)
    (hgB : ∀ r ∈ Set.Icc a0 a1,
      ‖g r‖ ≤ (Real.sqrt a1 + 1 / 16) * T ∧
        ‖deriv g r‖ ≤ slopeBound a0 * T ∧
        ‖deriv (deriv g) r‖ ≤ curvatureBound a0 * T + slopeBound a0 ^ 2 * T ^ 2) :
    ∀ r ∈ Set.Icc a0 a1,
      ‖(a r : ℂ) * g r‖ ≤ M * T * smallBudget a0 a1 ∧
        ‖deriv (fun x : ℝ => (a x : ℂ) * g x) r‖ ≤ M * T * smallBudget a0 a1 ∧
        ‖deriv (deriv (fun x : ℝ => (a x : ℂ) * g x)) r‖ ≤ M * T * smallBudget a0 a1 := by
  have hc1 : 0 ≤ slopeBound a0 := by dsimp [slopeBound]; positivity
  have hc2 : 0 ≤ curvatureBound a0 := by dsimp [curvatureBound]; positivity
  have hTT : T ^ 2 ≤ T := by nlinarith
  have hp0 : (Real.sqrt a1 + 1 / 16) * T ≤ T * smallBudget a0 a1 := by
    dsimp [smallBudget]
    nlinarith [mul_nonneg hc1 hT, mul_nonneg hc2 hT,
      mul_nonneg (sq_nonneg (slopeBound a0)) hT]
  have hp1 : (Real.sqrt a1 + 1 / 16) * T + slopeBound a0 * T ≤
      T * smallBudget a0 a1 := by
    dsimp [smallBudget]
    nlinarith [mul_nonneg hc1 hT, mul_nonneg hc2 hT,
      mul_nonneg (sq_nonneg (slopeBound a0)) hT]
  have hp2 : (Real.sqrt a1 + 1 / 16) * T + 2 * (slopeBound a0 * T) +
      (curvatureBound a0 * T + slopeBound a0 ^ 2 * T ^ 2) ≤ T * smallBudget a0 a1 := by
    have hh := mul_le_mul_of_nonneg_left hTT (sq_nonneg (slopeBound a0))
    dsimp [smallBudget]
    nlinarith
  intro r hr
  obtain ⟨hb0, hb1, hb2⟩ := product_norm_bounds a ha g hg M
    ((Real.sqrt a1 + 1 / 16) * T) (slopeBound a0 * T)
    (curvatureBound a0 * T + slopeBound a0 ^ 2 * T ^ 2)
    hM r (lt_of_lt_of_le ha0 hr.1) (haB r) (hgB r hr)
  refine ⟨hb0.trans ?_, hb1.trans ?_, hb2.trans ?_⟩
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp0 hM
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp1 hM
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp2 hM

private lemma exponential_eq_unit (a : ℝ → ℝ) (y u v : ℝ) :
    sourceMarkExponential a y u v =
      unitFourier (fun r : ℝ => (a r : ℂ) * markExpPhase (u * y) 0 r) v := by
  unfold sourceMarkExponential unitFourier markExpPhase
  apply integral_congr_ae
  filter_upwards [] with r
  rw [mul_assoc (a r : ℂ), ← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

private lemma sine_eq_unit (a : ℝ → ℝ) (y u w v : ℝ) :
    sourceMarkSine a y u w v =
      unitFourier (fun r : ℝ => (a r : ℂ) * markSinPhase (u * y) (u * w) r) v := by
  unfold sourceMarkSine unitFourier markSinPhase
  apply integral_congr_ae
  filter_upwards [] with r
  have he : u * (y * Real.sqrt r + w) = (u * y) * Real.sqrt r + u * w := by ring
  rw [he, Complex.ofReal_mul]

private lemma sqrt_one_add_le (T : ℝ) (hT : 0 ≤ T) :
    Real.sqrt (1 + T) ≤ 1 + Real.sqrt T := by
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by positivity, by nlinarith [Real.sq_sqrt hT, Real.sqrt_nonneg T]⟩

theorem sourceMarkExponential_norms (a0 a1 : ℝ)
    (ha0 : 0 < a0) (ha1 : a0 ≤ a1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ℝ), 0 ≤ M → ∀ (a : ℝ → ℝ),
        ContDiff ℝ ∞ a → tsupport a ⊆ Set.Icc a0 a1 →
        (∀ r : ℝ, |a r| ≤ M ∧ |deriv a r| ≤ M ∧
          |deriv (deriv a) r| ≤ M) →
        ∀ (y u : ℝ), 0 ≤ y →
          Integrable (fun v : ℝ => ‖sourceMarkExponential a y u v‖) ∧
          Integrable (fun v : ℝ => |v| * ‖sourceMarkExponential a y u v‖) ∧
          (∫ v : ℝ, ‖sourceMarkExponential a y u v‖) ≤
            C * M * (1 + Real.sqrt (y * |u|)) ∧
          (∫ v : ℝ, |v| * ‖sourceMarkExponential a y u v‖) ≤
            C * M * (1 + y * |u|) * (1 + Real.sqrt (y * |u|)) := by
  let L := Real.sqrt (1 + (a1 - a0))
  have hL : 0 < L := Real.sqrt_pos.mpr (by linarith)
  let C := 256 * largeBudget a0 * L
  have hD : 0 < largeBudget a0 := largeBudget_pos a0
  refine ⟨C, mul_pos (mul_pos (by norm_num) (largeBudget_pos a0)) hL, ?_⟩
  intro M hM a ha hs haB y u hy
  let T := y * |u|
  have hT : 0 ≤ T := mul_nonneg hy (abs_nonneg _)
  have ht : |u * y| = T := by rw [abs_mul, abs_of_nonneg hy]; dsimp [T]; ring
  have hg : ∀ r : ℝ, 0 < r → ContDiffAt ℝ ∞ (markExpPhase (u * y) 0) r :=
    markExpPhase_smooth (u * y) 0
  have hgB : ∀ r ∈ Set.Icc a0 a1,
      ‖markExpPhase (u * y) 0 r‖ ≤ 1 ∧
        ‖deriv (markExpPhase (u * y) 0) r‖ ≤ slopeBound a0 * T ∧
        ‖deriv (deriv (markExpPhase (u * y) 0)) r‖ ≤
          curvatureBound a0 * T + slopeBound a0 ^ 2 * T ^ 2 := by
    intro r hr
    simpa only [ht] using markExpPhase_norm_bounds a0 ha0 (u * y) 0 r hr.1
  have hb := large_product_bounds a0 a1 ha0 a ha (markExpPhase (u * y) 0) hg
    M T hM hT haB hgB
  have hbudget := supported_unit_budget a0 a1 ha0 ha1 a ha hs
    (markExpPhase (u * y) 0) hg (M * largeBudget a0) (1 + T)
    (mul_nonneg hM (largeBudget_pos a0).le) (by linarith) hb
  simp_rw [← exponential_eq_unit a y u] at hbudget
  obtain ⟨hi0, hi1, hb0, hb1⟩ := hbudget
  refine ⟨hi0, hi1, ?_, ?_⟩
  · calc
      _ ≤ 256 * (M * largeBudget a0) * L * Real.sqrt (1 + T) := hb0
      _ ≤ 256 * (M * largeBudget a0) * L * (1 + Real.sqrt T) :=
        mul_le_mul_of_nonneg_left (sqrt_one_add_le T hT) (by positivity)
      _ = _ := by dsimp [C, T]; ring
  · calc
      _ ≤ 256 * (M * largeBudget a0) * L * (1 + T) * Real.sqrt (1 + T) := hb1
      _ ≤ 256 * (M * largeBudget a0) * L * (1 + T) * (1 + Real.sqrt T) :=
        mul_le_mul_of_nonneg_left (sqrt_one_add_le T hT) (by positivity)
      _ = _ := by dsimp [C, T]; ring

theorem sourceMarkSine_norms (a0 a1 : ℝ)
    (ha0 : 0 < a0) (ha1 : a0 ≤ a1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ℝ), 0 ≤ M → ∀ (a : ℝ → ℝ),
        ContDiff ℝ ∞ a → tsupport a ⊆ Set.Icc a0 a1 →
        (∀ r : ℝ, |a r| ≤ M ∧ |deriv a r| ≤ M ∧
          |deriv (deriv a) r| ≤ M) →
        ∀ (y u w : ℝ), 0 ≤ y → |w| ≤ y / 16 →
          Integrable (fun v : ℝ => ‖sourceMarkSine a y u w v‖) ∧
          Integrable (fun v : ℝ => |v| * ‖sourceMarkSine a y u w v‖) ∧
          (∫ v : ℝ, ‖sourceMarkSine a y u w v‖) ≤
            C * M * min (y * |u|) (1 + Real.sqrt (y * |u|)) ∧
          (∫ v : ℝ, |v| * ‖sourceMarkSine a y u w v‖) ≤
            C * M * (1 + y * |u|) *
              min (y * |u|) (1 + Real.sqrt (y * |u|)) := by
  let L := Real.sqrt (1 + (a1 - a0))
  have hL : 0 < L := Real.sqrt_pos.mpr (by linarith)
  have hDL : 0 < largeBudget a0 := largeBudget_pos a0
  have hDS : 0 < smallBudget a0 a1 := smallBudget_pos a0 a1
  let CL := 256 * largeBudget a0 * L
  let CS := 256 * smallBudget a0 a1 * L
  have hCL : 0 < CL := by dsimp [CL]; positivity
  have hCS : 0 < CS := by dsimp [CS]; positivity
  let C := 2 * CL + CS
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro M hM a ha hs haB y u w hy hw
  let T := y * |u|
  have hT : 0 ≤ T := mul_nonneg hy (abs_nonneg _)
  have ht : |u * y| = T := by rw [abs_mul, abs_of_nonneg hy]; dsimp [T]; ring
  have hsw : |u * w| ≤ T / 16 := by
    rw [abs_mul]
    calc
      _ ≤ |u| * (y / 16) := mul_le_mul_of_nonneg_left hw (abs_nonneg _)
      _ = _ := by dsimp [T]; ring
  have hg : ∀ r : ℝ, 0 < r → ContDiffAt ℝ ∞ (markSinPhase (u * y) (u * w)) r :=
    markSinPhase_smooth (u * y) (u * w)
  have hgLarge : ∀ r ∈ Set.Icc a0 a1,
      ‖markSinPhase (u * y) (u * w) r‖ ≤ 1 ∧
        ‖deriv (markSinPhase (u * y) (u * w)) r‖ ≤ slopeBound a0 * T ∧
        ‖deriv (deriv (markSinPhase (u * y) (u * w))) r‖ ≤
          curvatureBound a0 * T + slopeBound a0 ^ 2 * T ^ 2 := by
    intro r hr
    obtain ⟨h0, _, h1, h2⟩ := markSinPhase_norm_bounds a0 a1 ha0 (u * y) (u * w) r hr
    exact ⟨h0, by simpa only [ht] using h1, by simpa only [ht] using h2⟩
  have hbL := large_product_bounds a0 a1 ha0 a ha (markSinPhase (u * y) (u * w)) hg
    M T hM hT haB hgLarge
  have hbudgetL := supported_unit_budget a0 a1 ha0 ha1 a ha hs
    (markSinPhase (u * y) (u * w)) hg (M * largeBudget a0) (1 + T)
    (mul_nonneg hM hDL.le) (by linarith) hbL
  simp_rw [← sine_eq_unit a y u w] at hbudgetL
  obtain ⟨hi0, hi1, hb0, hb1⟩ := hbudgetL
  have hlarge0 : (∫ v : ℝ, ‖sourceMarkSine a y u w v‖) ≤
      CL * M * (1 + Real.sqrt T) := by
    calc
      _ ≤ 256 * (M * largeBudget a0) * L * Real.sqrt (1 + T) := hb0
      _ ≤ 256 * (M * largeBudget a0) * L * (1 + Real.sqrt T) :=
        mul_le_mul_of_nonneg_left (sqrt_one_add_le T hT) (by positivity)
      _ = _ := by dsimp [CL]; ring
  have hlarge1 : (∫ v : ℝ, |v| * ‖sourceMarkSine a y u w v‖) ≤
      CL * M * (1 + T) * (1 + Real.sqrt T) := by
    calc
      _ ≤ 256 * (M * largeBudget a0) * L * (1 + T) * Real.sqrt (1 + T) := hb1
      _ ≤ 256 * (M * largeBudget a0) * L * (1 + T) * (1 + Real.sqrt T) :=
        mul_le_mul_of_nonneg_left (sqrt_one_add_le T hT) (by positivity)
      _ = _ := by dsimp [CL]; ring
  refine ⟨hi0, hi1, ?_⟩
  by_cases hT1 : T ≤ 1
  · have hgSmall : ∀ r ∈ Set.Icc a0 a1,
        ‖markSinPhase (u * y) (u * w) r‖ ≤ (Real.sqrt a1 + 1 / 16) * T ∧
          ‖deriv (markSinPhase (u * y) (u * w)) r‖ ≤ slopeBound a0 * T ∧
          ‖deriv (deriv (markSinPhase (u * y) (u * w))) r‖ ≤
            curvatureBound a0 * T + slopeBound a0 ^ 2 * T ^ 2 := by
      intro r hr
      obtain ⟨_, h0, h1, h2⟩ := markSinPhase_norm_bounds a0 a1 ha0 (u * y) (u * w) r hr
      rw [ht] at h0 h1 h2
      refine ⟨h0.trans ?_, h1, h2⟩
      nlinarith
    have hbS := small_product_bounds a0 a1 ha0 a ha (markSinPhase (u * y) (u * w)) hg
      M T hM hT hT1 haB hgSmall
    have hbudgetS := supported_unit_budget a0 a1 ha0 ha1 a ha hs
      (markSinPhase (u * y) (u * w)) hg (M * T * smallBudget a0 a1) 1
      (by positivity) le_rfl (by simpa only [mul_one, one_pow] using hbS)
    simp_rw [← sine_eq_unit a y u w, Real.sqrt_one, mul_one] at hbudgetS
    obtain ⟨_, _, hs0, hs1⟩ := hbudgetS
    have hs0' : (∫ v : ℝ, ‖sourceMarkSine a y u w v‖) ≤ CS * M * T := by
      convert hs0 using 1 <;> dsimp [CS, L] <;> ring
    have hs1' : (∫ v : ℝ, |v| * ‖sourceMarkSine a y u w v‖) ≤ CS * M * T := by
      convert hs1 using 1 <;> dsimp [CS, L] <;> ring
    have hmin : min T (1 + Real.sqrt T) = T :=
      min_eq_left (by nlinarith [Real.sqrt_nonneg T])
    have hSC : CS ≤ C := by dsimp [C]; linarith
    constructor
    · change _ ≤ C * M * min T (1 + Real.sqrt T)
      rw [hmin]
      exact hs0'.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hSC hM) hT)
    · change _ ≤ C * M * (1 + T) * min T (1 + Real.sqrt T)
      rw [hmin]
      refine (hs1'.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hSC hM) hT)).trans ?_
      have hh := mul_le_mul_of_nonneg_left
        (show T ≤ (1 + T) * T by nlinarith [sq_nonneg T]) (mul_nonneg hC.le hM)
      simpa only [mul_assoc] using hh
  · have hTge : 1 ≤ T := by linarith
    have hsT : Real.sqrt T ≤ T := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨hT, by nlinarith⟩
    have hmin : 1 + Real.sqrt T ≤ 2 * min T (1 + Real.sqrt T) := by
      by_cases hcmp : T ≤ 1 + Real.sqrt T
      · rw [min_eq_left hcmp]
        linarith
      · rw [min_eq_right (le_of_not_ge hcmp)]
        linarith [Real.sqrt_nonneg T]
    have hLC : 2 * CL ≤ C := by dsimp [C]; linarith
    constructor
    · change _ ≤ C * M * min T (1 + Real.sqrt T)
      calc
        _ ≤ CL * M * (1 + Real.sqrt T) := hlarge0
        _ ≤ CL * M * (2 * min T (1 + Real.sqrt T)) :=
          mul_le_mul_of_nonneg_left hmin (mul_nonneg hCL.le hM)
        _ = (2 * CL) * M * min T (1 + Real.sqrt T) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hLC hM) (le_min hT (by positivity))
    · change _ ≤ C * M * (1 + T) * min T (1 + Real.sqrt T)
      calc
        _ ≤ CL * M * (1 + T) * (1 + Real.sqrt T) := hlarge1
        _ ≤ CL * M * (1 + T) * (2 * min T (1 + Real.sqrt T)) :=
          mul_le_mul_of_nonneg_left hmin (by positivity)
        _ = (2 * CL) * M * (1 + T) * min T (1 + Real.sqrt T) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLC hM) (by positivity))
          (le_min hT (by positivity))

end Shao.Probability

