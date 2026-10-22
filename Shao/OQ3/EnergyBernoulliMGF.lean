import Shao.OQ3.SourceBinaryEntropyGap
import Shao.OQ3.InverseTilt
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace Shao.OQ3
open MeasureTheory
noncomputable section

private theorem binary_test_normalizer_pos (z theta : ℝ) (hz0 : 0 < z) (hz1 : z < 1) :
    0 < 1 - z + z * Real.exp theta :=
  add_pos (sub_pos.mpr hz1) (mul_pos hz0 (Real.exp_pos theta))

theorem exists_binary_exponential_test (p z L : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z < 1)
    (hL : L < binaryRelativeEntropy p z) :
    ∃ theta : ℝ, 0 < 1 - z + z * Real.exp theta ∧
      L < theta * p - Real.log (1 - z + z * Real.exp theta) := by
  have hcz : 0 < 1 - z := sub_pos.mpr hz1
  by_cases hpzero : p = 0
  · subst p
    have hD : binaryRelativeEntropy 0 z = -Real.log (1 - z) := by
      simp [binaryRelativeEntropy, one_div]
    rw [hD] at hL
    have hE : 1 - z < Real.exp (-L) :=
      (Real.log_lt_iff_lt_exp hcz).mp (by linarith)
    let d : ℝ := Real.exp (-L) - (1 - z)
    have hd : 0 < d := sub_pos.mpr hE
    let u : ℝ := d / (2 * z)
    have hu : 0 < u := div_pos hd (mul_pos (by norm_num) hz0)
    have hzu : z * u = d / 2 := by
      dsimp [u]
      field_simp
    have hN : 0 < 1 - z + z * Real.exp (Real.log u) :=
      binary_test_normalizer_pos z _ hz0 hz1
    have hNE : 1 - z + z * Real.exp (Real.log u) < Real.exp (-L) := by
      rw [Real.exp_log hu, hzu]
      dsimp [d] at *
      linarith
    have hlog := Real.log_lt_log hN hNE
    rw [Real.log_exp] at hlog
    refine ⟨Real.log u, hN, ?_⟩
    simpa only [mul_zero, zero_sub] using (show L < -Real.log
      (1 - z + z * Real.exp (Real.log u)) by linarith)
  by_cases hpone : p = 1
  · subst p
    have hD : binaryRelativeEntropy 1 z = -Real.log z := by
      simp [binaryRelativeEntropy, one_div]
    rw [hD] at hL
    have hE : z < Real.exp (-L) :=
      (Real.log_lt_iff_lt_exp hz0).mp (by linarith)
    let d : ℝ := Real.exp (-L) - z
    have hd : 0 < d := sub_pos.mpr hE
    let u : ℝ := d / (2 * (1 - z))
    have hu : 0 < u := div_pos hd (mul_pos (by norm_num) hcz)
    have hcu : (1 - z) * u = d / 2 := by
      dsimp [u]
      field_simp
    let B : ℝ := 1 - z + z * Real.exp (-Real.log u)
    have hB : 0 < B := binary_test_normalizer_pos z _ hz0 hz1
    have hBu : B * u = z + d / 2 := by
      dsimp [B]
      rw [Real.exp_neg, Real.exp_log hu]
      calc
        (1 - z + z * u⁻¹) * u = (1 - z) * u + z := by
          field_simp
        _ = z + d / 2 := by rw [hcu]; ring
    have hBE : B * u < Real.exp (-L) := by
      rw [hBu]
      dsimp [d] at *
      linarith
    have hlog := Real.log_lt_log (mul_pos hB hu) hBE
    rw [Real.log_mul hB.ne' hu.ne', Real.log_exp] at hlog
    refine ⟨-Real.log u, hB, ?_⟩
    change L < (-Real.log u) * 1 - Real.log B
    linarith
  have hp : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpzero)
  have hcp : 0 < 1 - p := sub_pos.mpr (lt_of_le_of_ne hp1 hpone)
  let A : ℝ := p / z
  let B : ℝ := (1 - p) / (1 - z)
  have hA : 0 < A := div_pos hp hz0
  have hB : 0 < B := div_pos hcp hcz
  let theta : ℝ := Real.log A - Real.log B
  have hexp : Real.exp theta = A / B := by
    dsimp [theta]
    rw [Real.exp_sub, Real.exp_log hA, Real.exp_log hB]
  have hnormal : 1 - z + z * Real.exp theta = B⁻¹ := by
    rw [hexp]
    dsimp [A, B]
    field_simp
    ring
  refine ⟨theta, binary_test_normalizer_pos z theta hz0 hz1, ?_⟩
  rw [hnormal, Real.log_inv]
  calc
    L < binaryRelativeEntropy p z := hL
    _ = theta * p - -Real.log B := by
      dsimp [binaryRelativeEntropy, theta, A, B]
      ring

theorem bounded_energy_logMGF_le_bernoulli (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q H t : ℝ) (hH : 0 < H)
    (henergy : ∀ᵐ x ∂mu, 1 ≤ x ^ 2 ∧ x ^ 2 ≤ 1 + H)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂mu) = q) :
    Integrable (fun x : ℝ => Real.exp (t * (x ^ 2 - q))) mu ∧
      0 < (∫ x : ℝ, Real.exp (t * (x ^ 2 - q)) ∂mu) ∧
      Real.log (∫ x : ℝ, Real.exp (t * (x ^ 2 - q)) ∂mu) ≤
        -t * (q - 1) + Real.log
          (1 - (q - 1) / H + ((q - 1) / H) * Real.exp (t * H)) := by
  let u : ℝ → ℝ := fun x => (x ^ 2 - 1) / H
  let g : ℝ → ℝ := fun x => Real.exp (t * (x ^ 2 - 1))
  let f : ℝ → ℝ := fun x => Real.exp (t * (x ^ 2 - q))
  let v : ℝ → ℝ := fun x => 1 - u x + u x * Real.exp (t * H)
  let B : ℝ := 1 - (q - 1) / H + ((q - 1) / H) * Real.exp (t * H)
  let A : ℝ := Real.exp (-t * (q - 1))
  have hf : Integrable f mu := by
    apply integrable_continuous_of_fixed_bounds mu hb
    dsimp [f]
    fun_prop
  have hg : Integrable g mu := by
    apply integrable_continuous_of_fixed_bounds mu hb
    dsimp [g]
    fun_prop
  have hu : Integrable u mu := by
    apply integrable_continuous_of_fixed_bounds mu hb
    dsimp [u]
    fun_prop
  have hv : Integrable v mu := by
    exact (integrable_const 1 |>.sub hu).add (hu.mul_const _)
  have hx2 : Integrable (fun x : ℝ => x ^ 2) mu := by
    apply integrable_continuous_of_fixed_bounds mu hb
    fun_prop
  have hintu : (∫ x : ℝ, u x ∂mu) = (q - 1) / H := by
    dsimp [u]
    rw [integral_div, integral_sub hx2 (integrable_const 1), hsecond]
    simp
  have hleft : Integrable (fun x : ℝ => 1 - u x) mu := (integrable_const 1).sub hu
  have hintv : (∫ x : ℝ, v x ∂mu) = B := by
    dsimp [v]
    rw [integral_add hleft (hu.mul_const _),
      integral_sub (integrable_const 1) hu, integral_mul_const, hintu]
    simp [B]
  have hle : g ≤ᵐ[mu] v := by
    filter_upwards [henergy] with x hx
    have hu0 : 0 ≤ u x := div_nonneg (sub_nonneg.mpr hx.1) hH.le
    have hu1 : u x ≤ 1 := (div_le_one hH).mpr (by linarith)
    have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (t * H))
      (sub_nonneg.mpr hu1) hu0 (by ring : 1 - u x + u x = 1)
    have harg : (1 - u x) * 0 + u x * (t * H) = t * (x ^ 2 - 1) := by
      dsimp [u]
      field_simp
      ring
    simpa only [smul_eq_mul, harg, Real.exp_zero, mul_one] using hc
  have hZ : 0 < ∫ x : ℝ, f x ∂mu := integral_exp_pos hf
  have hA : 0 < A := Real.exp_pos _
  have hfg (x : ℝ) : f x = A * g x := by
    dsimp [f, A, g]
    rw [← Real.exp_add]
    congr 1
    ring
  have hbound : (∫ x : ℝ, f x ∂mu) ≤ A * B := by
    calc
      (∫ x : ℝ, f x ∂mu) = A * ∫ x : ℝ, g x ∂mu := by
        simp_rw [hfg]
        rw [integral_const_mul]
      _ ≤ A * ∫ x : ℝ, v x ∂mu :=
        mul_le_mul_of_nonneg_left (integral_mono_ae hg hv hle) hA.le
      _ = A * B := by rw [hintv]
  have hB : 0 < B := (mul_pos_iff_of_pos_left hA).mp (hZ.trans_le hbound)
  refine ⟨hf, hZ, ?_⟩
  have hlog := Real.log_le_log hZ hbound
  rw [Real.log_mul hA.ne' hB.ne'] at hlog
  dsimp [A] at hlog
  rw [Real.log_exp] at hlog
  exact hlog

end
end Shao.OQ3
