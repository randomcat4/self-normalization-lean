import Shao.Probability.RetainedSample

/-!
# Actual retained centered moments and variance

All moments use the existing genuine retained cutoff law. The centered cube
comparison is proved by an integrated polynomial inequality. The source size
assumptions then separate the actual variance from zero and bound its actual
Berry--Esseen Lyapunov parameter.
-/

set_option autoImplicit false

namespace Shao

open MeasureTheory

private theorem abs_integral_cube_le_integral_abs_cube
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (h1 : Integrable (fun z : ℝ => z) η)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) η) :
    |∫ z : ℝ, z ∂η| ^ 3 ≤ ∫ z : ℝ, |z| ^ 3 ∂η := by
  let b : ℝ := |∫ z : ℝ, z ∂η|
  have hb : 0 ≤ b := abs_nonneg _
  have habs : Integrable (fun z : ℝ => |z|) η := by
    simpa only [Real.norm_eq_abs] using h1.norm
  have hbmean : b ≤ ∫ z : ℝ, |z| ∂η := by
    simpa only [b, Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (μ := η) (fun z : ℝ => z))
  have hpoint (z : ℝ) : (3 * b ^ 2) * |z| ≤ |z| ^ 3 + 2 * b ^ 3 := by
    have hfactor := mul_nonneg (sq_nonneg (|z| - b))
      (show 0 ≤ |z| + 2 * b by positivity)
    nlinarith only [hfactor]
  have hI := integral_mono (habs.const_mul (3 * b ^ 2))
    (h3.add (integrable_const (2 * b ^ 3))) hpoint
  have hmoment : (3 * b ^ 2) * (∫ z : ℝ, |z| ∂η) ≤
      (∫ z : ℝ, |z| ^ 3 ∂η) + 2 * b ^ 3 := by
    simpa [integral_add h3 (integrable_const (2 * b ^ 3)), integral_const_mul] using hI
  have hmul := mul_le_mul_of_nonneg_left hbmean
    (show 0 ≤ 3 * b ^ 2 by positivity)
  change b ^ 3 ≤ _
  nlinarith only [hmoment, hmul]

theorem retainedCutoffLaw_centered_moments
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (x : ℝ) (hx : 0 < x) (hq : 0 < retainedCutoffMass ν x)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) :
    let μx : ℝ := ∫ z : ℝ, z ∂retainedCutoffLaw ν x
    Integrable (fun z : ℝ => z - μx) (retainedCutoffLaw ν x) ∧
      Integrable (fun z : ℝ => (z - μx) ^ 2) (retainedCutoffLaw ν x) ∧
      Integrable (fun z : ℝ => |z - μx| ^ 3) (retainedCutoffLaw ν x) ∧
      (∫ z : ℝ, z - μx ∂retainedCutoffLaw ν x) = 0 ∧
      (∫ z : ℝ, (z - μx) ^ 2 ∂retainedCutoffLaw ν x) =
        (∫ z : ℝ, z ^ 2 ∂retainedCutoffLaw ν x) - μx ^ 2 ∧
      (∫ z : ℝ, |z - μx| ^ 3 ∂retainedCutoffLaw ν x) ≤
        8 * (∫ z : ℝ, |z| ^ 3 ∂retainedCutoffLaw ν x) := by
  let η : Measure ℝ := retainedCutoffLaw ν x
  let μx : ℝ := ∫ z : ℝ, z ∂η
  have : IsProbabilityMeasure η := retainedCutoffLaw_isProbabilityMeasure ν x hq
  obtain ⟨h1, h2x⟩ := integrable_retainedCutoffLaw_id_sq ν x hq h2
  have h3 := integrable_retainedCutoffLaw_abs_cube ν x hx hq h2
  change Integrable (fun z : ℝ => z) η at h1
  change Integrable (fun z : ℝ => z ^ 2) η at h2x
  change Integrable (fun z : ℝ => |z| ^ 3) η at h3
  have hc1 : Integrable (fun z : ℝ => z - μx) η := h1.sub (integrable_const μx)
  have hpolynomial (z : ℝ) : (z - μx) ^ 2 = z ^ 2 - (2 * μx) * z + μx ^ 2 := by
    ring
  have hc2 : Integrable (fun z : ℝ => (z - μx) ^ 2) η := by
    apply ((h2x.sub (h1.const_mul (2 * μx))).add (integrable_const (μx ^ 2))).congr
    exact ae_of_all η (fun z => (hpolynomial z).symm)
  have hcenter : (∫ z : ℝ, z - μx ∂η) = 0 := by
    rw [integral_sub h1 (integrable_const μx)]
    simp [μx]
  have hvariance : (∫ z : ℝ, (z - μx) ^ 2 ∂η) =
      (∫ z : ℝ, z ^ 2 ∂η) - μx ^ 2 := by
    calc
      _ = ∫ z : ℝ, z ^ 2 - (2 * μx) * z + μx ^ 2 ∂η := by
        apply integral_congr_ae
        exact ae_of_all η hpolynomial
      _ = (∫ z : ℝ, z ^ 2 ∂η) - (2 * μx) * (∫ z : ℝ, z ∂η) + μx ^ 2 := by
        rw [integral_add (f := fun z : ℝ => z ^ 2 - (2 * μx) * z)
            (g := fun _z : ℝ => μx ^ 2)
            (h2x.sub (h1.const_mul (2 * μx))) (integrable_const (μx ^ 2)),
          integral_sub (f := fun z : ℝ => z ^ 2) (g := fun z : ℝ => (2 * μx) * z)
            h2x (h1.const_mul (2 * μx)), integral_const_mul]
        simp
      _ = _ := by change _ = _ - (∫ z : ℝ, z ∂η) ^ 2; dsimp only [μx]; ring
  have hcubepoint (z : ℝ) : |z - μx| ^ 3 ≤ 4 * (|z| ^ 3 + |μx| ^ 3) := by
    have htriangle : |z - μx| ≤ |z| + |μx| := by simpa using abs_sub_le z 0 μx
    apply (pow_le_pow_left₀ (abs_nonneg _) htriangle 3).trans
    have hfactor := mul_nonneg (show 0 ≤ 3 * (|z| + |μx|) by positivity)
      (sq_nonneg (|z| - |μx|))
    nlinarith only [hfactor]
  have hdom : Integrable (fun z : ℝ => 4 * (|z| ^ 3 + |μx| ^ 3)) η :=
    (h3.add (integrable_const (|μx| ^ 3))).const_mul 4
  have hc3 : Integrable (fun z : ℝ => |z - μx| ^ 3) η := by
    apply hdom.mono' ((continuous_id.sub continuous_const).abs.pow 3).aestronglyMeasurable
    exact ae_of_all η (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
      exact hcubepoint z)
  have hcubeI := integral_mono hc3 hdom hcubepoint
  have hcubefour : (∫ z : ℝ, |z - μx| ^ 3 ∂η) ≤
      4 * ((∫ z : ℝ, |z| ^ 3 ∂η) + |μx| ^ 3) := by
    simpa [integral_const_mul, integral_add h3 (integrable_const (|μx| ^ 3))] using hcubeI
  have hjensen : |μx| ^ 3 ≤ ∫ z : ℝ, |z| ^ 3 ∂η :=
    abs_integral_cube_le_integral_abs_cube η h1 h3
  exact ⟨hc1, hc2, hc3, hcenter, hvariance, by nlinarith only [hcubefour, hjensen]⟩

theorem retainedSample_variance_third_moment_bounds
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n j : ℕ) (x : ℝ)
    (hx : 2 ≤ x) (hsize : x ^ 6 ≤ (n : ℝ))
    (hj : (j : ℝ) ≤ x ^ 2 / 2)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (hcut : (n : ℝ) * (∫ z : ℝ, truncationF (x * z) ∂ν) ≤ 1) :
    let μx : ℝ := ∫ z : ℝ, z ∂retainedCutoffLaw ν x
    let Vx : ℝ := ∫ z : ℝ, (z - μx) ^ 2 ∂retainedCutoffLaw ν x
    let M : ℝ := (n - j : ℕ)
    let y : ℝ := Real.sqrt (x ^ 2 - (j : ℝ))
    (∀ᵐ z : ℝ ∂retainedCutoffLaw ν x, |z - μx| ≤ 2 / x) ∧
      0 < Vx ∧
      ((1 / 2 : ℝ) ≤ M * Vx ∧ M * Vx ≤ 2) ∧
      M * (∫ z : ℝ, |z - μx| ^ 3 ∂retainedCutoffLaw ν x) ≤ 16 / y ^ 3 := by
  let η : Measure ℝ := retainedCutoffLaw ν x
  let μx : ℝ := ∫ z : ℝ, z ∂η
  let Vx : ℝ := ∫ z : ℝ, (z - μx) ^ 2 ∂η
  let E2 : ℝ := ∫ z : ℝ, z ^ 2 ∂η
  let N : ℝ := n
  let M : ℝ := (n - j : ℕ)
  let y : ℝ := Real.sqrt (x ^ 2 - (j : ℝ))
  obtain ⟨hn64, _, hm1, hfrac, h31⟩ := retainedSample_size_bounds n j x hx hsize hj
  have hn2 : 2 ≤ n := by omega
  have hN64 : (64 : ℝ) ≤ N := by dsimp only [N]; exact_mod_cast hn64
  have hNpos : 0 < N := by linarith
  have hM1 : (1 : ℝ) ≤ M := by dsimp only [M]; exact_mod_cast hm1
  have hMpos : 0 < M := by linarith
  have hMN : M ≤ N := by dsimp only [M, N]; exact_mod_cast Nat.sub_le n j
  have hxpos : 0 < x := by linarith
  obtain ⟨_, hqhalf, _⟩ := retainedCutoffMass_bounds ν n hn2 x hxpos h2 hcut
  have hq : 0 < retainedCutoffMass ν x := by linarith
  obtain ⟨_, _, _, _, hV, hCc⟩ := retainedCutoffLaw_centered_moments ν x hxpos hq h2
  change Vx = E2 - μx ^ 2 at hV
  have hMV : M * Vx = M * E2 - M * μx ^ 2 := by rw [hV]; ring
  have hsecond := retainedCutoffLaw_second_moment_bounds ν n hn2 x hxpos h2 hnorm hcut
  have hx2 : (4 : ℝ) ≤ x ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx 2
    norm_num at h
    exact h
  have hxinv : 1 / x ^ 2 ≤ (1 / 4 : ℝ) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hxpos) (by norm_num : (0 : ℝ) < 4)).mpr
    nlinarith only [hx2]
  have hNlo : (3 / 4 : ℝ) ≤ N * E2 := by
    have hlo := hsecond.1
    change 1 - 1 / x ^ 2 ≤ N * E2 at hlo
    linarith only [hxinv, hlo]
  have hratio : (31 / 32 : ℝ) ≤ M / N := h31.trans hfrac
  have hprod := mul_le_mul hratio hNlo (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (div_nonneg hMpos.le hNpos.le)
  have hcancel : (M / N) * (N * E2) = M * E2 := by field_simp [hNpos.ne']
  rw [hcancel] at hprod
  norm_num at hprod
  have hmeanN := retainedCutoffLaw_mean_bound ν n hn2 x hxpos h2 hmean hcut
  change N * |μx| ≤ 2 / x at hmeanN
  have htwoDiv : 2 / x ≤ (1 : ℝ) := (div_le_iff₀ hxpos).mpr (by linarith only [hx])
  have hNmu : N * |μx| ≤ 1 := hmeanN.trans htwoDiv
  have hmu64 : |μx| ≤ (1 / 64 : ℝ) := by
    nlinarith only [hNmu, hN64, abs_nonneg μx]
  have hNm2 : N * μx ^ 2 ≤ (1 / 64 : ℝ) := by
    calc
      N * μx ^ 2 = (N * |μx|) * |μx| := by rw [← sq_abs μx]; ring
      _ ≤ 1 * |μx| := mul_le_mul_of_nonneg_right hNmu (abs_nonneg μx)
      _ ≤ 1 / 64 := by simpa only [one_mul] using hmu64
  have hMm2 : M * μx ^ 2 ≤ (1 / 64 : ℝ) :=
    (mul_le_mul_of_nonneg_right hMN (sq_nonneg μx)).trans hNm2
  have hlo : (1 / 2 : ℝ) ≤ M * Vx := by nlinarith only [hMV, hprod, hMm2]
  have hVpos : 0 < Vx :=
    (mul_pos_iff_of_pos_left hMpos).mp (lt_of_lt_of_le (by norm_num) hlo)
  obtain ⟨_, ⟨_, hrawupper⟩, _, hrawthird⟩ :=
    retainedSample_raw_moment_bounds ν n j x hx hsize hj h2 hmean hnorm hcut
  have hupp : M * Vx ≤ 2 := by
    have hm2nonneg := mul_nonneg hMpos.le (sq_nonneg μx)
    change M * E2 ≤ 2 at hrawupper
    nlinarith only [hMV, hm2nonneg, hrawupper]
  have hmuBound : |μx| ≤ 1 / x := by
    have h := (mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ N by linarith)
      (abs_nonneg μx)).trans hmeanN
    simp only [div_eq_mul_inv, one_mul] at h ⊢
    nlinarith only [h]
  refine ⟨?_, hVpos, ⟨hlo, hupp⟩, ?_⟩
  · filter_upwards [ae_abs_le_retainedCutoffLaw ν x hq] with z hz
    have htriangle : |z - μx| ≤ |z| + |μx| := by simpa using abs_sub_le z 0 μx
    apply htriangle.trans
    calc
      |z| + |μx| ≤ 1 / x + 1 / x := add_le_add hz hmuBound
      _ = 2 / x := by ring
  · have h := mul_le_mul_of_nonneg_left hCc hMpos.le
    calc
      _ ≤ 8 * (M * (∫ z : ℝ, |z| ^ 3 ∂η)) := by nlinarith only [h]
      _ ≤ 8 * (2 / y ^ 3) := mul_le_mul_of_nonneg_left hrawthird (by norm_num)
      _ = 16 / y ^ 3 := by ring

theorem retainedSample_lyapunov_bound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n j : ℕ) (x : ℝ)
    (hx : 2 ≤ x) (hsize : x ^ 6 ≤ (n : ℝ))
    (hj : (j : ℝ) ≤ x ^ 2 / 2)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (hcut : (n : ℝ) * (∫ z : ℝ, truncationF (x * z) ∂ν) ≤ 1) :
    let μx : ℝ := ∫ z : ℝ, z ∂retainedCutoffLaw ν x
    let Vx : ℝ := ∫ z : ℝ, (z - μx) ^ 2 ∂retainedCutoffLaw ν x
    let M : ℝ := (n - j : ℕ)
    let y : ℝ := Real.sqrt (x ^ 2 - (j : ℝ))
    (∫ z : ℝ, |z - μx| ^ 3 ∂retainedCutoffLaw ν x) /
        (Real.sqrt M * (Real.sqrt Vx) ^ 3) ≤ 64 / y ^ 3 := by
  let μx : ℝ := ∫ z : ℝ, z ∂retainedCutoffLaw ν x
  let Vx : ℝ := ∫ z : ℝ, (z - μx) ^ 2 ∂retainedCutoffLaw ν x
  let M : ℝ := (n - j : ℕ)
  let y : ℝ := Real.sqrt (x ^ 2 - (j : ℝ))
  let C : ℝ := ∫ z : ℝ, |z - μx| ^ 3 ∂retainedCutoffLaw ν x
  let s : ℝ := Real.sqrt (M * Vx)
  obtain ⟨_, hVpos, ⟨hlo, _⟩, hC⟩ :=
    retainedSample_variance_third_moment_bounds ν n j x hx hsize hj h2 hmean hnorm hcut
  change 0 < Vx at hVpos
  change (1 / 2 : ℝ) ≤ M * Vx at hlo
  change M * C ≤ 16 / y ^ 3 at hC
  obtain ⟨_, _, hm1, _, _⟩ := retainedSample_size_bounds n j x hx hsize hj
  obtain ⟨_, _, hy1⟩ := retainedSample_threshold_bounds j x hx hj
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hy1
  have hM1 : (1 : ℝ) ≤ M := by dsimp only [M]; exact_mod_cast hm1
  have hMpos : 0 < M := by linarith
  have hMVpos : 0 < M * Vx := mul_pos hMpos hVpos
  have hspos : 0 < s := Real.sqrt_pos.mpr hMVpos
  have hs2 : s ^ 2 = M * Vx := Real.sq_sqrt hMVpos.le
  have hshalf : (1 / 2 : ℝ) ≤ s := by
    apply Real.le_sqrt_of_sq_le
    linarith only [hlo]
  have hscube : (1 / 4 : ℝ) ≤ s ^ 3 := by
    calc
      (1 / 4 : ℝ) = (1 / 2) * (1 / 2) := by norm_num
      _ ≤ s * (M * Vx) := mul_le_mul hshalf hlo (by norm_num) hspos.le
      _ = s ^ 3 := by rw [← hs2]; ring
  have hsqrt : s = Real.sqrt M * Real.sqrt Vx := Real.sqrt_mul hMpos.le Vx
  have hMsqrt : (Real.sqrt M) ^ 2 = M := Real.sq_sqrt hMpos.le
  have hden : s ^ 3 = M * (Real.sqrt M * (Real.sqrt Vx) ^ 3) := by
    calc
      s ^ 3 = (Real.sqrt M) ^ 2 * (Real.sqrt M * (Real.sqrt Vx) ^ 3) := by
        rw [hsqrt]
        ring
      _ = M * (Real.sqrt M * (Real.sqrt Vx) ^ 3) := by rw [hMsqrt]
  have hdenpos : 0 < Real.sqrt M * (Real.sqrt Vx) ^ 3 :=
    mul_pos (Real.sqrt_pos.mpr hMpos) (pow_pos (Real.sqrt_pos.mpr hVpos) 3)
  have hratio : C / (Real.sqrt M * (Real.sqrt Vx) ^ 3) = (M * C) / s ^ 3 := by
    apply (div_eq_div_iff hdenpos.ne' (pow_pos hspos 3).ne').mpr
    rw [hden]
    ring
  change C / (Real.sqrt M * (Real.sqrt Vx) ^ 3) ≤ 64 / y ^ 3
  rw [hratio]
  apply (div_le_iff₀ (pow_pos hspos 3)).mpr
  have hquarter : 1 ≤ 4 * s ^ 3 := by linarith only [hscube]
  have hmul := mul_le_mul_of_nonneg_left hquarter
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 16) (pow_pos hypos 3).le)
  calc
    M * C ≤ 16 / y ^ 3 := hC
    _ ≤ (16 / y ^ 3) * (4 * s ^ 3) := by simpa only [mul_one] using hmul
    _ = (64 / y ^ 3) * s ^ 3 := by ring

end Shao
