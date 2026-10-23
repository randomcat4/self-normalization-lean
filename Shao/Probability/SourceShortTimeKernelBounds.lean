import Shao.Probability.SourceOddEvenMarkedIBP
import Shao.Probability.QuadraticFullNoiseMarkedLowRegions
import Shao.Probability.QuadraticFullNoiseMarkedOutside
import Shao.Probability.QuadraticFullNoiseMarkedRegionFour
import Shao.Probability.SourceShortTimeGrid

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

private noncomputable def shortD (ν : Measure ℝ) (m : ℕ) (u v : ℝ) : ℂ :=
  (quadraticChar ν u v ^ m - quadraticChar ν (-u) v ^ m) / 2 *
    quadraticFullNoiseChar ν u v

private noncomputable def shortW (ν : Measure ℝ) (m : ℕ) (u v : ℝ) : ℂ :=
  (u : ℂ) * ((quadraticChar ν u v ^ m + quadraticChar ν (-u) v ^ m) / 2 *
    quadraticFullNoiseChar ν u v)

private noncomputable def shortB (y w sigma u v : ℝ) : ℂ :=
  sourceMarkSine (fun r => sourceKernelCutoff r /
    (Real.sqrt r + sigma * w / y) ^ 2) y u (sigma * w) v

private noncomputable def shortOddNorm (ν : Measure ℝ) (m : ℕ)
    (y w sigma : ℝ) (p : ℝ × ℝ) : ℝ :=
  ‖deriv (fun r : ℝ => deriv (fun t : ℝ => shortD ν m t p.2) r) p.1‖ *
    ‖shortB y w sigma p.1 p.2‖ / y ^ 2

private noncomputable def shortEvenNorm (ν : Measure ℝ) (m : ℕ)
    (y w sigma : ℝ) (p : ℝ × ℝ) : ℝ :=
  ‖deriv (fun r : ℝ => deriv (fun t : ℝ => shortW ν m t p.2) r) p.1‖ *
    ‖shortB y w sigma p.1 p.2‖ / y ^ 2

private noncomputable def shortR (y T : ℝ) : ℝ :=
  1 + Real.sqrt y * T ^ (-(1 / 4 : ℝ))

private theorem shortR_one_le (y T : ℝ) (hT : 0 ≤ T) : 1 ≤ shortR y T := by
  dsimp [shortR]
  have hn : 0 ≤ Real.sqrt y * T ^ (-(1 / 4 : ℝ)) := by positivity
  linarith

private theorem short_high_profile (b T y : ℝ) (hb : 0 < b) (hT : 0 < T)
    (hbT : b ^ 2 ≤ T) :
    (b ^ 10 + Real.sqrt y * b ^ 9 * Real.sqrt b) / T ^ 5 ≤ shortR y T ∧
      (b ^ 11 + Real.sqrt y * b ^ 10 * Real.sqrt b) / T ^ 5 ≤ b * shortR y T := by
  have h10 : b ^ 10 ≤ T ^ 5 := by
    convert pow_le_pow_left₀ (sq_nonneg b) hbT 5 using 1 <;> ring
  have h19 : b ^ 9 * Real.sqrt b ≤ T ^ (19 / 4 : ℝ) := by
    calc
      b ^ 9 * Real.sqrt b = b ^ (19 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast b 9, ← Real.rpow_add hb]
        norm_num
      _ = (b ^ 2) ^ (19 / 4 : ℝ) := by
        rw [← Real.rpow_natCast b 2, ← Real.rpow_mul hb.le]
        norm_num
      _ ≤ T ^ (19 / 4 : ℝ) :=
        Real.rpow_le_rpow (sq_nonneg b) hbT (by norm_num)
  have hscale : T ^ (-(1 / 4 : ℝ)) * T ^ 5 = T ^ (19 / 4 : ℝ) := by
    rw [← Real.rpow_natCast T 5, ← Real.rpow_add hT]
    norm_num
  have he : (b ^ 10 + Real.sqrt y * b ^ 9 * Real.sqrt b) / T ^ 5 ≤ shortR y T := by
    apply (div_le_iff₀ (pow_pos hT 5)).mpr
    dsimp [shortR]
    calc
      b ^ 10 + Real.sqrt y * b ^ 9 * Real.sqrt b ≤
          T ^ 5 + Real.sqrt y * T ^ (19 / 4 : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left h19 (Real.sqrt_nonneg y)]
      _ = (1 + Real.sqrt y * T ^ (-(1 / 4 : ℝ))) * T ^ 5 := by
        rw [← hscale]
        ring
  refine ⟨he, ?_⟩
  convert mul_le_mul_of_nonneg_left he hb.le using 1 <;> ring

private theorem short_five_integral (F : ℝ × ℝ → ℝ)
    (U L C : Set (ℝ × ℝ)) (hU : MeasurableSet U) (hL : MeasurableSet L)
    (hC : MeasurableSet C) (hLU : L ⊆ U)
    (h1 : IntegrableOn F (L ∩ C)) (h2 : IntegrableOn F (L \ C))
    (h3 : IntegrableOn F (U \ L)) (h4 : IntegrableOn F (Uᶜ ∩ C))
    (h5 : IntegrableOn F (Uᶜ \ C)) :
    Integrable F ∧ (∫ p, F p) =
      (∫ p in L ∩ C, F p) + (∫ p in L \ C, F p) +
        (∫ p in U \ L, F p) + (∫ p in Uᶜ ∩ C, F p) + (∫ p in Uᶜ \ C, F p) := by
  have hcover : (((L ∩ C) ∪ (L \ C)) ∪ (U \ L)) ∪ (Uᶜ ∩ C) ∪ (Uᶜ \ C) =
      Set.univ := by
    ext p
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff,
      Set.mem_compl_iff, Set.mem_univ, iff_true]
    by_cases hu : p ∈ U <;> by_cases hl : p ∈ L <;> by_cases hc : p ∈ C <;>
      simp_all
  have hi : Integrable F := by
    have hh := (((h1.union h2).union h3).union h4).union h5
    rwa [hcover, integrableOn_univ] at hh
  have hUL : U ∩ L = L := Set.inter_eq_right.mpr hLU
  have hsplitU := integral_inter_add_sdiff (f := F) hL hi.integrableOn
    (s := U)
  rw [hUL] at hsplitU
  have hsplitL := integral_inter_add_sdiff (f := F) hC hi.integrableOn
    (s := L)
  have hsplitUc := integral_inter_add_sdiff (f := F) hC hi.integrableOn
    (s := Uᶜ)
  have hsplit := integral_add_compl hU hi
  exact ⟨hi, by linarith⟩

private theorem short_scalar_profiles (A B gamma h y T : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hgB : gamma ≤ 2 * B) (hh : 0 < h) (hh1 : h ≤ 1)
    (hy : 0 < y) (hy2 : y ≤ 2) (hT : 0 < T) (hTy : T < y ^ 2)
    (hbT : (128 * gamma) ^ 2 ≤ T) :
    let b : ℝ := gamma / (1 / 128 : ℝ)
    let R : ℝ := shortR y T
    ((B + T * A) * R ≤ 4 * ((A + B) * R)) ∧
      (T * (A + B) ≤ 4 * ((A + B) * R)) ∧
      (Real.sqrt T + gamma ≤ 4 * R) ∧
      (b * (T + h * gamma) ≤ 82304 * ((A + B) * R)) ∧
      (b * (Real.sqrt T + gamma) + b ^ 2 * (T + h * gamma) ≤ 82304 * R) ∧
      ((b ^ 11 + Real.sqrt y * b ^ 10 * Real.sqrt b) / T ^ 5 ≤
        256 * ((A + B) * R)) ∧
      ((b ^ 10 + Real.sqrt y * b ^ 9 * Real.sqrt b) / T ^ 5 ≤ 256 * R) ∧
      ((4 * h) ^ 31 * b ^ 30 * (T + h * gamma) ≤
        (10 * 4 ^ 31 * 128 ^ 30 : ℝ) * ((A + B) * R)) ∧
      ((4 * h) ^ 31 * (b ^ 30 * (Real.sqrt T + gamma) +
        b ^ 29 * (T + h * gamma)) ≤ (10 * 4 ^ 31 * 128 ^ 30 : ℝ) * R) := by
  dsimp only
  let b : ℝ := gamma / (1 / 128 : ℝ)
  let R : ℝ := shortR y T
  have hb : b = 128 * gamma := by dsimp [b]; ring
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hb128 : b ≤ 128 := by rw [hb]; linarith
  have hR : 1 ≤ R := shortR_one_le y T hT.le
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hAB : 0 ≤ A + B := add_nonneg hA hB
  have hABR : A + B ≤ (A + B) * R := by nlinarith
  have hT4 : T ≤ 4 := by nlinarith
  have hsT : Real.sqrt T ≤ 2 := (Real.sqrt_le_iff).2 ⟨by norm_num, by linarith⟩
  have hhg : h * gamma ≤ 1 := by nlinarith
  have hTg : T + h * gamma ≤ 5 := by linarith
  have hsg : Real.sqrt T + gamma ≤ 3 := by linarith
  have hb2 : b ^ 2 ≤ 128 ^ 2 := pow_le_pow_left₀ hb0 hb128 2
  have hbound := short_high_profile b T y (by rw [hb]; positivity) hT
    (by simpa only [hb] using hbT)
  have hbR : b * R ≤ 256 * ((A + B) * R) := by
    rw [hb]
    nlinarith [mul_le_mul_of_nonneg_right hgB hR0,
      mul_nonneg hA hR0]
  have hg30 : gamma ^ 30 ≤ gamma := by
    calc
      gamma ^ 30 = gamma ^ 29 * gamma := by ring
      _ ≤ 1 * gamma := mul_le_mul_of_nonneg_right (pow_le_one₀ hg.le hg1) hg.le
      _ = gamma := one_mul _
  have hb30g : b ^ 30 ≤ 128 ^ 30 * gamma := by
    rw [hb, mul_pow]
    exact mul_le_mul_of_nonneg_left hg30 (by positivity)
  have hb30 : b ^ 30 ≤ 128 ^ 30 := pow_le_pow_left₀ hb0 hb128 30
  have hb29 : b ^ 29 ≤ 128 ^ 29 := pow_le_pow_left₀ hb0 hb128 29
  have hh31 : (4 * h) ^ 31 ≤ 4 ^ 31 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 31
  refine ⟨?_, ?_, ?_, ?_, ?_, hbound.2.trans hbR, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg hA (show 0 ≤ 4 - T by linarith),
      mul_nonneg hA hR0, mul_nonneg hB hR0]
  · nlinarith [mul_le_mul_of_nonneg_right hT4 hAB]
  · nlinarith
  · have hmul := mul_le_mul_of_nonneg_left hTg hb0
    rw [hb] at hmul
    nlinarith
  · have hmul1 := mul_le_mul_of_nonneg_left hsg hb0
    have hmul2 := mul_le_mul_of_nonneg_left hTg (sq_nonneg b)
    nlinarith
  · change (b ^ 10 + Real.sqrt y * b ^ 9 * Real.sqrt b) / T ^ 5 ≤ 256 * R
    exact hbound.1.trans (by nlinarith)
  · change (4 * h) ^ 31 * b ^ 30 * (T + h * gamma) ≤
      (10 * 4 ^ 31 * 128 ^ 30 : ℝ) * ((A + B) * R)
    have hp1 := mul_le_mul hh31 hb30g (by positivity) (by positivity)
    have hp2 := mul_le_mul hp1 hTg (by positivity) (by positivity)
    have hp3 := mul_le_mul_of_nonneg_left hgB (show 0 ≤ (5 * 4 ^ 31 * 128 ^ 30 : ℝ) by positivity)
    calc
      _ ≤ 4 ^ 31 * (128 ^ 30 * gamma) * 5 := hp2
      _ = (5 * 4 ^ 31 * 128 ^ 30 : ℝ) * gamma := by ring
      _ ≤ (5 * 4 ^ 31 * 128 ^ 30 : ℝ) * (2 * B) := hp3
      _ = (10 * 4 ^ 31 * 128 ^ 30 : ℝ) * B := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ((show B ≤ A + B by linarith).trans hABR)
        (by positivity)
  · change (4 * h) ^ 31 * (b ^ 30 * (Real.sqrt T + gamma) +
      b ^ 29 * (T + h * gamma)) ≤ (10 * 4 ^ 31 * 128 ^ 30 : ℝ) * R
    have hp1 := mul_le_mul hb30 hsg (by positivity) (by positivity)
    have hp2 := mul_le_mul hb29 hTg (by positivity) (by positivity)
    have hp3 := mul_le_mul hh31 (add_le_add hp1 hp2) (by positivity) (by positivity)
    have hc : (4 ^ 31 * (128 ^ 30 * 3 + 128 ^ 29 * 5) : ℝ) ≤
        10 * 4 ^ 31 * 128 ^ 30 := by norm_num
    exact hp3.trans (hc.trans (by nlinarith only [hR]))

private theorem short_profile_bound (I C y P M F : ℝ) (hC : 0 ≤ C)
    (hi : I ≤ C / y ^ 2 * P) (hp : P ≤ M * F) :
    I ≤ M * C / y ^ 2 * F := by
  calc
    I ≤ C / y ^ 2 * P := hi
    _ ≤ C / y ^ 2 * (M * F) :=
      mul_le_mul_of_nonneg_left hp (div_nonneg hC (sq_nonneg y))
    _ = M * C / y ^ 2 * F := by ring

set_option maxHeartbeats 800000 in
private theorem short_actual_norm_bounds :
    ∃ K epsilon0 : ℝ, 0 < K ∧ 0 < epsilon0 ∧ epsilon0 ≤ 1 / 2 ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
          (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 →
          (∫ a : ℝ, a ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ epsilon0 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ i : ℕ, i ≤ n → ∀ y w sigma : ℝ, 0 < y → y ≤ 2 →
              |w| ≤ y / 16 → |sigma| = 1 →
              let ρ : Measure ℝ :=
                ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
              let mu : ℝ := ∫ a : ℝ, a ∂ρ
              let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
              let gamma : ℝ := m3 / variance (id : ℝ → ℝ) ρ
              let T : ℝ := ((n - i : ℕ) : ℝ) * (∫ a : ℝ, a ^ 2 ∂ρ)
              (16384 : ℝ) * gamma ^ 2 ≤ T → T < y ^ 2 →
              Integrable (shortOddNorm ρ (n - i) y w sigma) ∧
                Integrable (shortEvenNorm ρ (n - i) y w sigma) ∧
                (∫ p, shortOddNorm ρ (n - i) y w sigma p) ≤
                  K / y ^ 2 * (((n : ℝ) * |mu| + (n : ℝ) * m3) * shortR y T) ∧
                (∫ p, shortEvenNorm ρ (n - i) y w sigma p) ≤ K / y ^ 2 * shortR y T := by
  obtain ⟨C1, hC1, reg1⟩ := sourceTruncation_odd_even_fullNoise_region1_actual_marked_postIBP
  obtain ⟨C2, delta2, hC2, hd2, _, reg2⟩ :=
    sourceTruncation_odd_even_fullNoise_region2_actual_marked_postIBP
  obtain ⟨C3, delta3, hC3, hd3, _, reg3⟩ :=
    sourceTruncation_odd_even_fullNoise_region3_actual_marked_postIBP
  obtain ⟨C4, hC4, reg4⟩ := sourceTruncation_odd_even_fullNoise_region4_actual_marked_postIBP
  obtain ⟨C5, delta5, hC5, hd5, _, reg5⟩ :=
    sourceTruncation_odd_even_fullNoise_region5_actual_marked_postIBP
  let epsilon0 : ℝ := min (1 / 2) (min (delta2 / 8) (min (delta3 / 512) (delta5 / 8)))
  let M : ℝ := 10 * 4 ^ 31 * 128 ^ 30
  let K : ℝ := 4 * C1 + 4 * C2 + 82304 * C3 + 256 * C4 + M * C5
  have he0 : 0 < epsilon0 := by dsimp [epsilon0]; positivity
  have he02 : epsilon0 ≤ 1 / 2 := min_le_left _ _
  have he0d2 : epsilon0 ≤ delta2 / 8 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have he0d3 : epsilon0 ≤ delta3 / 512 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have he0d5 : epsilon0 ≤ delta5 / 8 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨K, epsilon0, by dsimp [K, M]; positivity, he0, he02, ?_⟩
  intro ν0 hp n h2 hn hm x epsilon hx he he0le hbudget i hi y w sigma hy hy2 hw hsigma
  letI : IsProbabilityMeasure ν0 := hp
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
  let m : ℕ := n - i
  let h : ℝ := epsilon / (1 + x)
  let mu : ℝ := ∫ a : ℝ, a ∂ρ
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
  let gamma : ℝ := m3 / variance (id : ℝ → ℝ) ρ
  let T : ℝ := (m : ℝ) * (∫ a : ℝ, a ^ 2 ∂ρ)
  let A : ℝ := (n : ℝ) * |mu|
  let B : ℝ := (n : ℝ) * m3
  let b : ℝ := gamma / (1 / 128 : ℝ)
  let R : ℝ := shortR y T
  change (16384 : ℝ) * gamma ^ 2 ≤ T → T < y ^ 2 → _
  intro hlow hTy
  have heHalf : epsilon ≤ 1 / 2 := he0le.trans he02
  have hden : 0 < 1 + x := by linarith
  have hh : 0 < h := div_pos he hden
  have hhe : h ≤ epsilon := by
    dsimp [h]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hh1 : h ≤ 1 := by linarith
  rcases sourceTruncation_gamma_bounds ν0 n h2 hn hm x epsilon hx he heHalf hbudget with
    ⟨hm3, hg, _, _, hgh, _, hgB, _, _⟩
  change 0 < m3 at hm3
  change 0 < gamma at hg
  change gamma ≤ 2 * h at hgh
  have hgB' : gamma ≤ 2 * B := by simpa only [B, mul_assoc] using hgB
  have hg1 : gamma ≤ 1 := by linarith only [hgh, hhe, heHalf]
  have hT : 0 < T := lt_of_lt_of_le (by positivity) hlow
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hR : 1 ≤ R := shortR_one_le y T hT.le
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hpays := short_scalar_profiles A B gamma h y T hA hB hg hg1 hgB' hh hh1
    hy hy2 hT hTy (by nlinarith only [hlow])
  change _ at hpays
  rcases hpays with ⟨p1, p2o, p2e, p3o, p3e, p4o, p4e, p5o, p5e⟩
  have hsmall2 : (4 * h) * y ≤ delta2 := by
    have hhy : h * y ≤ 2 * epsilon :=
      (mul_le_mul_of_nonneg_left hy2 hh.le).trans (by nlinarith only [hhe])
    have hδ := he0le.trans he0d2
    nlinarith only [hhy, hδ]
  have hsmall3 : b * y ≤ delta3 := by
    have hhy : h * y ≤ 2 * epsilon :=
      (mul_le_mul_of_nonneg_left hy2 hh.le).trans (by nlinarith only [hhe])
    have hgy : gamma * y ≤ 4 * epsilon := by
      have hgym := mul_le_mul_of_nonneg_right hgh hy.le
      nlinarith only [hgym, hhy]
    have hδ := he0le.trans he0d3
    dsimp [b]
    nlinarith only [hgy, hδ]
  have hsmall5 : (4 * h) * y ≤ delta5 := by
    have hhy : h * y ≤ 2 * epsilon :=
      (mul_le_mul_of_nonneg_left hy2 hh.le).trans (by nlinarith only [hhe])
    have hδ := he0le.trans he0d5
    nlinarith only [hhy, hδ]
  have hkL : 1 ≤ (1 / 128 : ℝ) * Real.sqrt 16384 := by
    have hsqrt : Real.sqrt (16384 : ℝ) = 128 := by
      convert Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 128) using 1 <;> norm_num
    norm_num [hsqrt]
  have d1 := reg1 ν0 hp n h2 hn hm x epsilon hx he heHalf hbudget i hi
    h (1 / 128) 16384 y w sigma le_rfl (by norm_num) (by norm_num) (by norm_num)
      hkL hy hy2 hw hsigma hlow hTy
  have d2 := reg2 ν0 hp n h2 hn hm x epsilon hx he heHalf hbudget i hi
    h (1 / 128) 16384 y w sigma le_rfl hh1 (by norm_num) (by norm_num) (by norm_num)
      hkL hy hy2 hw hsigma hlow hTy hsmall2
  have d3 := reg3 ν0 hp n h2 hn hm x epsilon hx he heHalf hbudget i hi
    h (1 / 128) y w sigma le_rfl (by norm_num) hy hy2 hw hsigma hsmall3
  have d4 := reg4 ν0 hp n h2 hn hm x epsilon hx he heHalf hbudget i hi
    h (1 / 128) 16384 y w sigma le_rfl (by norm_num) (by norm_num)
      hkL hy hy2 hw hsigma hlow hTy
  have d5 := reg5 ν0 hp n h2 hn hm x epsilon hx he heHalf hbudget i hi
    h (1 / 128) y w sigma le_rfl (by norm_num) hy hy2 hw hsigma hsmall5
  let U : Set (ℝ × ℝ) := {p | |p.1| ≤ (1 / 128 : ℝ) / gamma}
  let L : Set (ℝ × ℝ) := {p | |p.1| ≤ (1 / 128 : ℝ) / gamma ∧
    |p.2| ≤ (1 / 128 : ℝ) * |p.1| / gamma}
  let C : Set (ℝ × ℝ) := {p | p.1 ≠ 0 ∧ |p.2| ≤ |p.1| / (4 * h)}
  let R1 : Set (ℝ × ℝ) := {p | |p.1| ≤ (1 / 128 : ℝ) / gamma ∧
    |p.2| ≤ (1 / 128 : ℝ) * |p.1| / gamma ∧ p.1 ≠ 0 ∧ |p.2| ≤ |p.1| / (4 * h)}
  let R2 : Set (ℝ × ℝ) := {p | |p.1| ≤ (1 / 128 : ℝ) / gamma ∧
    |p.2| ≤ (1 / 128 : ℝ) * |p.1| / gamma ∧ ¬(p.1 ≠ 0 ∧ |p.2| ≤ |p.1| / (4 * h))}
  let R3 : Set (ℝ × ℝ) := {p | |p.1| ≤ (1 / 128 : ℝ) / gamma ∧
    (1 / 128 : ℝ) * |p.1| / gamma < |p.2|}
  let R4 : Set (ℝ × ℝ) := {p | (1 / 128 : ℝ) / gamma < |p.1| ∧
    |p.2| ≤ |p.1| / (4 * h)}
  let R4bar : Set (ℝ × ℝ) := {p | (1 / 128 : ℝ) / gamma ≤ |p.1| ∧
    |p.2| ≤ |p.1| / (4 * h)}
  let R5 : Set (ℝ × ℝ) := {p | (1 / 128 : ℝ) / gamma < |p.1| ∧
    |p.1| / (4 * h) < |p.2|}
  let No : ℝ × ℝ → ℝ := shortOddNorm ρ m y w sigma
  let Ne : ℝ × ℝ → ℝ := shortEvenNorm ρ m y w sigma
  change IntegrableOn No R1 ∧ IntegrableOn Ne R1 ∧
    (∫ p in R1, No p) ≤ C1 / y ^ 2 * (B + T * A) * R ∧
    (∫ p in R1, Ne p) ≤ C1 / y ^ 2 * R at d1
  change IntegrableOn No R2 ∧ IntegrableOn Ne R2 ∧
    (∫ p in R2, No p) ≤ C2 / y ^ 2 * T * (A + B) ∧
    (∫ p in R2, Ne p) ≤ C2 / y ^ 2 * (Real.sqrt T + gamma) at d2
  change IntegrableOn No R3 ∧ IntegrableOn Ne R3 ∧
    (∫ p in R3, No p) ≤ C3 / y ^ 2 * b * (T + h * gamma) ∧
    (∫ p in R3, Ne p) ≤ C3 / y ^ 2 *
      (b * (Real.sqrt T + gamma) + b ^ 2 * (T + h * gamma)) at d3
  change IntegrableOn No R4bar ∧ IntegrableOn Ne R4bar ∧
    (∫ p in R4bar, No p) ≤ C4 / y ^ 2 / T ^ 5 *
      (b ^ 11 + Real.sqrt y * b ^ 10 * Real.sqrt b) ∧
    (∫ p in R4bar, Ne p) ≤ C4 / y ^ 2 / T ^ 5 *
      (b ^ 10 + Real.sqrt y * b ^ 9 * Real.sqrt b) at d4
  change IntegrableOn No R5 ∧ IntegrableOn Ne R5 ∧
    (∫ p in R5, No p) ≤ C5 / y ^ 2 * (4 * h) ^ 31 * b ^ 30 * (T + h * gamma) ∧
    (∫ p in R5, Ne p) ≤ C5 / y ^ 2 * (4 * h) ^ 31 *
      (b ^ 30 * (Real.sqrt T + gamma) + b ^ 29 * (T + h * gamma)) at d5
  have hmf : Measurable (fun p : ℝ × ℝ => |p.1|) := by fun_prop
  have hms : Measurable (fun p : ℝ × ℝ => |p.2|) := by fun_prop
  have hU : MeasurableSet U := measurableSet_le hmf measurable_const
  have hL : MeasurableSet L := hU.inter
    (measurableSet_le hms (by fun_prop))
  have hz : MeasurableSet {p : ℝ × ℝ | p.1 = 0} :=
    measurableSet_eq_fun measurable_fst measurable_const
  have hC : MeasurableSet C := hz.compl.inter
    (measurableSet_le hms (by fun_prop))
  have hLU : L ⊆ U := fun _ hp => hp.1
  have e1 : R1 = L ∩ C := by ext p; simp [R1, L, C, and_assoc]
  have e2 : R2 = L \ C := by ext p; simp [R2, L, C, and_assoc]
  have e3 : R3 = U \ L := by
    ext p
    by_cases hu : |p.1| ≤ (1 / 128 : ℝ) / gamma <;>
      simp [R3, U, L, hu, not_le] <;> tauto
  have hcut : 0 < (1 / 128 : ℝ) / gamma := div_pos (by norm_num) hg
  have hne (p : ℝ × ℝ) (hu : (1 / 128 : ℝ) / gamma < |p.1|) : p.1 ≠ 0 := by
    intro heq
    simp only [heq, abs_zero] at hu
    linarith
  have e4 : R4 = Uᶜ ∩ C := by
    ext p
    simp only [R4, U, C, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_le]
    exact ⟨fun hp => ⟨hp.1, hne p hp.1, hp.2⟩, fun hp => ⟨hp.1, hp.2.2⟩⟩
  have e5 : R5 = Uᶜ \ C := by
    ext p
    simp only [R5, U, C, Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_compl_iff, not_le]
    constructor
    · rintro ⟨hu, hv⟩
      exact ⟨hu, fun hp => (not_le.mpr hv) hp.2⟩
    · rintro ⟨hu, hv⟩
      exact ⟨hu, lt_of_not_ge (fun hh => hv ⟨hne p hu, hh⟩)⟩
  have h4sub : R4 ⊆ R4bar := fun _ hp => ⟨hp.1.le, hp.2⟩
  have hNo (p : ℝ × ℝ) : 0 ≤ No p := by dsimp [No, shortOddNorm]; positivity
  have hNe (p : ℝ × ℝ) : 0 ≤ Ne p := by dsimp [Ne, shortEvenNorm]; positivity
  have d4o : (∫ p in R4, No p) ≤ C4 / y ^ 2 *
      ((b ^ 11 + Real.sqrt y * b ^ 10 * Real.sqrt b) / T ^ 5) := by
    have hh := setIntegral_mono_set d4.1 (Filter.Eventually.of_forall hNo)
      (Filter.Eventually.of_forall h4sub)
    exact hh.trans (by convert d4.2.2.1 using 1 <;> ring)
  have d4e : (∫ p in R4, Ne p) ≤ C4 / y ^ 2 *
      ((b ^ 10 + Real.sqrt y * b ^ 9 * Real.sqrt b) / T ^ 5) := by
    have hh := setIntegral_mono_set d4.2.1 (Filter.Eventually.of_forall hNe)
      (Filter.Eventually.of_forall h4sub)
    exact hh.trans (by convert d4.2.2.2 using 1 <;> ring)
  have hfo := short_five_integral No U L C hU hL hC hLU
    (by simpa only [← e1] using d1.1) (by simpa only [← e2] using d2.1)
    (by simpa only [← e3] using d3.1)
    (by simpa only [← e4] using d4.1.mono_set h4sub)
    (by simpa only [← e5] using d5.1)
  have hfe := short_five_integral Ne U L C hU hL hC hLU
    (by simpa only [← e1] using d1.2.1) (by simpa only [← e2] using d2.2.1)
    (by simpa only [← e3] using d3.2.1)
    (by simpa only [← e4] using d4.2.1.mono_set h4sub)
    (by simpa only [← e5] using d5.2.1)
  rw [← e1, ← e2, ← e3, ← e4, ← e5] at hfo hfe
  have o1 := short_profile_bound _ C1 y _ 4 _ hC1.le
    (by simpa only [mul_assoc] using d1.2.2.1) p1
  have o2 := short_profile_bound _ C2 y _ 4 _ hC2.le
    (by simpa only [mul_assoc] using d2.2.2.1) p2o
  have o3 := short_profile_bound _ C3 y _ 82304 _ hC3.le
    (by simpa only [mul_assoc] using d3.2.2.1) p3o
  have o4 := short_profile_bound _ C4 y _ 256 _ hC4.le d4o p4o
  have o5 := short_profile_bound _ C5 y _ M _ hC5.le
    (by simpa only [mul_assoc] using d5.2.2.1) p5o
  have e1b := short_profile_bound _ C1 y _ 4 R hC1.le d1.2.2.2 (by nlinarith only [hR0])
  have e2b := short_profile_bound _ C2 y _ 4 R hC2.le d2.2.2.2 p2e
  have e3b := short_profile_bound _ C3 y _ 82304 R hC3.le d3.2.2.2 p3e
  have e4b := short_profile_bound _ C4 y _ 256 R hC4.le d4e p4e
  have e5b := short_profile_bound _ C5 y _ M R hC5.le
    (by simpa only [mul_assoc] using d5.2.2.2) p5e
  refine ⟨hfo.1, hfe.1, ?_, ?_⟩
  · rw [hfo.2]
    convert add_le_add (add_le_add (add_le_add (add_le_add o1 o2) o3) o4) o5 using 1 <;>
      dsimp [K] <;> ring
  · rw [hfe.2]
    convert add_le_add (add_le_add (add_le_add (add_le_add e1b e2b) e3b) e4b) e5b using 1 <;>
      dsimp [K] <;> ring

private theorem short_marked_norm_integral (F : ℝ × ℝ → ℂ) (y w sigma q : ℝ) :
    (∫ p : ℝ × ℝ, ‖Complex.exp ((((p.2 * q : ℝ) : ℂ)) * Complex.I) *
      shortB y w sigma p.1 p.2 * F p‖) / y ^ 2 =
      ∫ p : ℝ × ℝ, ‖F p‖ * ‖shortB y w sigma p.1 p.2‖ / y ^ 2 := by
  rw [integral_div]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
      Real.exp_zero, one_mul]
    ring

private theorem short_inverse_abs (z y : ℝ) (c : ℂ) (G H : ℝ × ℝ → ℂ)
    (hc : ‖c‖ ≤ 1 / y ^ 2)
    (hz : (z : ℂ) = c * ((∫ p, G p) + ∫ p, H p)) :
    |z| ≤ (∫ p, ‖G p‖) / y ^ 2 + (∫ p, ‖H p‖) / y ^ 2 := by
  calc
    |z| = ‖(z : ℂ)‖ := by simp
    _ = ‖c‖ * ‖(∫ p, G p) + ∫ p, H p‖ := by rw [hz, norm_mul]
    _ ≤ (1 / y ^ 2) * ((∫ p, ‖G p‖) + ∫ p, ‖H p‖) := by
      apply mul_le_mul hc
        ((norm_add_le _ _).trans (add_le_add (norm_integral_le_integral_norm G)
          (norm_integral_le_integral_norm H))) (norm_nonneg _)
        (div_nonneg zero_le_one (sq_nonneg y))
    _ = (∫ p, ‖G p‖) / y ^ 2 + (∫ p, ‖H p‖) / y ^ 2 := by ring

private theorem short_coefficient_norms (y : ℝ) (hy : 0 < y) :
    ‖-Complex.I / (((2 * Real.pi) ^ 2 * y ^ 2 : ℝ) : ℂ)‖ ≤ 1 / y ^ 2 ∧
      ‖((((2 * Real.pi) ^ 2 * y ^ 2 : ℝ) : ℂ)⁻¹)‖ ≤ 1 / y ^ 2 := by
  have hpi : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.two_le_pi]
  have hden : 0 < (2 * Real.pi) ^ 2 * y ^ 2 := by positivity
  have hle : 1 / ((2 * Real.pi) ^ 2 * y ^ 2) ≤ 1 / y ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hy) (by nlinarith [sq_nonneg y])
  constructor
  · simpa only [norm_div, norm_neg, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hden] using hle
  · simpa only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden,
      one_div] using hle

theorem sourceTruncation_futureNoise_short_kernel_sums :
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
              let T : ℕ → ℝ := fun i => ((n - i : ℕ) : ℝ) * m2
              let J : Finset ℕ := (Finset.range (n + 1)).filter
                (fun i => n / 2 < i ∧ L2 * gamma ^ 2 ≤ T i ∧
                  T i < max (L2 * gamma ^ 2) (y ^ 2))
              let f : ℕ → ℝ → ℝ → ℝ := fun i q w =>
                sourceFutureNoiseKernel ρ (n - i) y (w, q)
              let o : ℕ → ℝ → ℝ → ℝ := fun i q w =>
                (f i q w - f i q (-w)) / 2
              let e : ℕ → ℝ → ℝ → ℝ := fun i q w =>
                (f i q w + f i q (-w)) / 2
              (∀ i ∈ J, ∀ w q : ℝ, |w| ≤ y / 16 →
                DifferentiableAt ℝ (o i q) w ∧
                  DifferentiableAt ℝ (e i q) w ∧
                  DifferentiableAt ℝ (fun r : ℝ => deriv (e i q) r) w) ∧
              (∀ q w : ℕ → ℝ, (∀ i ∈ J, |w i| ≤ y / 16) →
                m2 * (∑ i ∈ J, |deriv (o i (q i)) (w i)|) ≤
                    C * ((n : ℝ) * |mu| + (n : ℝ) * m3) ∧
                  m2 * (∑ i ∈ J,
                    |deriv (fun r : ℝ => deriv (e i (q i)) r) (w i)|) ≤ C) := by
  obtain ⟨K, epsilon0, hK, he0, he02, hnorm⟩ := short_actual_norm_bounds
  obtain ⟨Cg, hCg, hgrid⟩ := sourceTruncation_shortClock_R_sums
  let C : ℝ := 2 * K * Cg
  refine ⟨C, epsilon0, 16384, by dsimp [C]; positivity, he0, he02, le_rfl, ?_⟩
  intro ν0 hp n h2 hn hm x epsilon hx he he0le hbudget
  letI : IsProbabilityMeasure ν0 := hp
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
  let mu : ℝ := ∫ a : ℝ, a ∂ρ
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
  let gamma : ℝ := m3 / variance (id : ℝ → ℝ) ρ
  change ∀ y : ℝ, gamma ≤ y → y ≤ 2 → _
  intro y hgy hy2
  let h : ℝ := epsilon / (1 + x)
  let T : ℕ → ℝ := fun i => ((n - i : ℕ) : ℝ) * m2
  let J : Finset ℕ := (Finset.range (n + 1)).filter
    (fun i => n / 2 < i ∧ (16384 : ℝ) * gamma ^ 2 ≤ T i ∧
      T i < max ((16384 : ℝ) * gamma ^ 2) (y ^ 2))
  let f : ℕ → ℝ → ℝ → ℝ := fun i q w => sourceFutureNoiseKernel ρ (n - i) y (w, q)
  let o : ℕ → ℝ → ℝ → ℝ := fun i q w => (f i q w - f i q (-w)) / 2
  let e : ℕ → ℝ → ℝ → ℝ := fun i q w => (f i q w + f i q (-w)) / 2
  let A : ℝ := (n : ℝ) * |mu| + (n : ℝ) * m3
  change (∀ i ∈ J, ∀ w q : ℝ, |w| ≤ y / 16 → _) ∧ _
  have heHalf : epsilon ≤ 1 / 2 := he0le.trans he02
  rcases sourceTruncation_law_data ν0 n h2 hn x epsilon hx he heHalf hbudget with
    ⟨_, _, hpρ, hs, _, _, h3, _⟩
  change IsProbabilityMeasure ρ at hpρ
  letI : IsProbabilityMeasure ρ := hpρ
  change (∀ᵐ a : ℝ ∂ρ, |a| ≤ h) at hs
  change Integrable (fun a : ℝ => |a| ^ 3) ρ at h3
  rcases sourceTruncation_variance_bounds ν0 n h2 hn hm x epsilon hx he heHalf hbudget with
    ⟨_, _, _, hVm, _, hV, _, _⟩
  change 0 < variance (id : ℝ → ℝ) ρ at hV
  change variance (id : ℝ → ℝ) ρ = m2 - mu ^ 2 at hVm
  have hm2 : 0 < m2 := by nlinarith [sq_nonneg mu]
  have hg : 0 < gamma := (sourceTruncation_gamma_bounds ν0 n h2 hn hm x epsilon
    hx he heHalf hbudget).2.1
  have hy : 0 < y := hg.trans_le hgy
  have hh : 0 < h := div_pos he (by linarith)
  have hA : 0 ≤ A := by
    have hm3 : 0 < m3 := (sourceTruncation_gamma_bounds ν0 n h2 hn hm x epsilon
      hx he heHalf hbudget).1
    dsimp [A]
    positivity
  have hJ : J = (Finset.range (n + 1)).filter
      (fun i => n / 2 < i ∧ (16384 : ℝ) * gamma ^ 2 ≤ T i ∧ T i < y ^ 2) := by
    apply Finset.filter_congr
    intro i hi
    constructor
    · rintro ⟨hlate, hlo, hu⟩
      exact ⟨hlate, hlo, (lt_max_iff.mp hu).resolve_left (not_lt_of_ge hlo)⟩
    · rintro ⟨hlate, hlo, hu⟩
      exact ⟨hlate, hlo, hu.trans_le (le_max_right _ _)⟩
  have hRsum : m2 / y ^ 2 * (∑ i ∈ J, shortR y (T i)) ≤ Cg := by
    have hh := (hgrid ν0 hp n h2 hn hm x epsilon hx he heHalf hbudget
      16384 y (by norm_num) hy).1
    simpa only [hJ, shortR] using hh
  have hpoint (i : ℕ) (hi : i ∈ J) (w q : ℝ) (hw : |w| ≤ y / 16) :
      DifferentiableAt ℝ (o i q) w ∧ DifferentiableAt ℝ (e i q) w ∧
        DifferentiableAt ℝ (fun r : ℝ => deriv (e i q) r) w ∧
        |deriv (o i q) w| ≤ 2 * K / y ^ 2 * (A * shortR y (T i)) ∧
        |deriv (fun r : ℝ => deriv (e i q) r) w| ≤ 2 * K / y ^ 2 * shortR y (T i) := by
    have himem := Finset.mem_filter.mp hi
    have hiN : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp himem.1)
    have hlo := himem.2.2.1
    have hTy : T i < y ^ 2 :=
      (lt_max_iff.mp himem.2.2.2).resolve_left (not_lt_of_ge hlo)
    have nplus := hnorm ν0 hp n h2 hn hm x epsilon hx he he0le hbudget i hiN
      y w 1 hy hy2 hw (by norm_num) hlo hTy
    have nminus := hnorm ν0 hp n h2 hn hm x epsilon hx he he0le hbudget i hiN
      y w (-1) hy hy2 hw (by norm_num) hlo hTy
    have odd := sourceFutureNoiseKernel_odd_derivative_markedIBP ρ h3 hV h hh hs
      (n - i) y hy w q hw
    have even := sourceFutureNoiseKernel_even_second_markedIBP ρ h3 hV h hh hs
      (n - i) y hy w q hw
    let Go : ℝ → ℝ × ℝ → ℂ := fun sigma p =>
      Complex.exp ((((p.2 * q : ℝ) : ℂ)) * Complex.I) *
        shortB y w sigma p.1 p.2 *
          deriv (fun r : ℝ => deriv (fun t : ℝ => shortD ρ (n - i) t p.2) r) p.1
    let Ge : ℝ → ℝ × ℝ → ℂ := fun sigma p =>
      Complex.exp ((((p.2 * q : ℝ) : ℂ)) * Complex.I) *
        shortB y w sigma p.1 p.2 *
          deriv (fun r : ℝ => deriv (fun t : ℝ => shortW ρ (n - i) t p.2) r) p.1
    have hoident : ((deriv (o i q) w : ℝ) : ℂ) =
        (-Complex.I / (((2 * Real.pi) ^ 2 * y ^ 2 : ℝ) : ℂ)) *
          ((∫ p, Go 1 p) + ∫ p, Go (-1) p) := by
      simpa only [o, f, Go, shortB, shortD, one_mul, neg_one_mul, neg_div,
        sub_eq_add_neg] using odd.2.2.2
    have heident : ((deriv (fun r : ℝ => deriv (e i q) r) w : ℝ) : ℂ) =
        ((((2 * Real.pi) ^ 2 * y ^ 2 : ℝ) : ℂ)⁻¹) *
          ((∫ p, Ge 1 p) + ∫ p, Ge (-1) p) := by
      simpa only [e, f, Ge, shortB, shortW, one_mul, neg_one_mul, neg_div,
        sub_eq_add_neg] using even.2.2.2.2
    have hco := (short_coefficient_norms y hy).1
    have hce := (short_coefficient_norms y hy).2
    have hno (sigma : ℝ) : (∫ p, ‖Go sigma p‖) / y ^ 2 =
        ∫ p, shortOddNorm ρ (n - i) y w sigma p :=
      short_marked_norm_integral _ y w sigma q
    have hne (sigma : ℝ) : (∫ p, ‖Ge sigma p‖) / y ^ 2 =
        ∫ p, shortEvenNorm ρ (n - i) y w sigma p :=
      short_marked_norm_integral _ y w sigma q
    have ho : |deriv (o i q) w| ≤ 2 * K / y ^ 2 * (A * shortR y (T i)) := by
      have hz := short_inverse_abs _ y _ (Go 1) (Go (-1)) hco hoident
      rw [hno 1, hno (-1)] at hz
      calc
        _ ≤ _ := hz
        _ ≤ K / y ^ 2 * (A * shortR y (T i)) +
            K / y ^ 2 * (A * shortR y (T i)) := add_le_add nplus.2.2.1 nminus.2.2.1
        _ = _ := by ring
    have heven : |deriv (fun r : ℝ => deriv (e i q) r) w| ≤
        2 * K / y ^ 2 * shortR y (T i) := by
      have hz := short_inverse_abs _ y _ (Ge 1) (Ge (-1)) hce heident
      rw [hne 1, hne (-1)] at hz
      calc
        _ ≤ _ := hz
        _ ≤ K / y ^ 2 * shortR y (T i) +
            K / y ^ 2 * shortR y (T i) := add_le_add nplus.2.2.2 nminus.2.2.2
        _ = _ := by ring
    exact ⟨odd.1, even.1, even.2.1, ho, heven⟩
  refine ⟨fun i hi w q hw => ⟨(hpoint i hi w q hw).1,
    (hpoint i hi w q hw).2.1, (hpoint i hi w q hw).2.2.1⟩, ?_⟩
  intro q w hw
  constructor
  · have hsum := Finset.sum_le_sum (fun i hi => (hpoint i hi (w i) (q i) (hw i hi)).2.2.2.1)
    calc
      m2 * (∑ i ∈ J, |deriv (o i (q i)) (w i)|) ≤
          m2 * (∑ i ∈ J, 2 * K / y ^ 2 * (A * shortR y (T i))) :=
        mul_le_mul_of_nonneg_left hsum hm2.le
      _ = (2 * K * A) * (m2 / y ^ 2 * (∑ i ∈ J, shortR y (T i))) := by
        simp_rw [← mul_assoc, ← Finset.mul_sum]
        ring
      _ ≤ (2 * K * A) * Cg := mul_le_mul_of_nonneg_left hRsum (by positivity)
      _ = C * A := by dsimp [C]; ring
  · have hsum := Finset.sum_le_sum (fun i hi => (hpoint i hi (w i) (q i) (hw i hi)).2.2.2.2)
    calc
      m2 * (∑ i ∈ J, |deriv (fun r : ℝ => deriv (e i (q i)) r) (w i)|) ≤
          m2 * (∑ i ∈ J, 2 * K / y ^ 2 * shortR y (T i)) :=
        mul_le_mul_of_nonneg_left hsum hm2.le
      _ = (2 * K) * (m2 / y ^ 2 * (∑ i ∈ J, shortR y (T i))) := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ (2 * K) * Cg := mul_le_mul_of_nonneg_left hRsum (by positivity)
      _ = C := rfl

end Shao.Probability
