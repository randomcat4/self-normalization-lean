import Shao.Probability.SourceTruncationBridge

/-!
The actual fixed-cutoff conditional law supplies the raw Fourier gamma and
the remaining-length inputs. The source normalization is n times its original
second moment equal to one; its conditional mean need not vanish.
-/

set_option autoImplicit false

namespace Shao

open MeasureTheory ProbabilityTheory

private theorem sf_raw_lyapunov (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (h2 : Integrable (fun z : ℝ => z ^ 2) rho)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) rho) :
    Real.sqrt (∫ z : ℝ, z ^ 2 ∂rho) * (∫ z : ℝ, z ^ 2 ∂rho) ≤
      ∫ z : ℝ, |z| ^ 3 ∂rho := by
  let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
  let b : ℝ := Real.sqrt m2
  have hm2 : 0 ≤ m2 := integral_nonneg (fun z => sq_nonneg z)
  have hb : 0 ≤ b := Real.sqrt_nonneg m2
  have hb2 : b ^ 2 = m2 := Real.sq_sqrt hm2
  have hpoint (z : ℝ) : (3 * b) * z ^ 2 ≤ 2 * |z| ^ 3 + b ^ 3 := by
    have hfactor := mul_nonneg (sq_nonneg (|z| - b))
      (show 0 ≤ 2 * |z| + b by positivity)
    rw [← sq_abs z]
    nlinarith only [hfactor]
  have hint := integral_mono (h2.const_mul (3 * b))
    ((h3.const_mul 2).add (integrable_const (b ^ 3))) hpoint
  change (∫ z : ℝ, (3 * b) * z ^ 2 ∂rho) ≤
    ∫ z : ℝ, 2 * |z| ^ 3 + b ^ 3 ∂rho at hint
  rw [integral_const_mul, integral_add (h3.const_mul 2) (integrable_const (b ^ 3)),
    integral_const_mul] at hint
  simp only [integral_const, probReal_univ, one_smul] at hint
  change (3 * b) * m2 ≤ 2 * (∫ z : ℝ, |z| ^ 3 ∂rho) + b ^ 3 at hint
  have hb3 : b ^ 3 = b * m2 := by rw [pow_succ, hb2]; ring
  change b * m2 ≤ _
  linarith only [hint, hb3]

private theorem sf_variance_ratio (N mu m2 V : ℝ) (hN : 0 < N)
    (hmu : N * mu ^ 2 ≤ 1 / 4) (hVlo : (1 / 2 : ℝ) ≤ N * V)
    (hVeq : V = m2 - mu ^ 2) : V ≤ m2 ∧ m2 ≤ 2 * V := by
  have hscaled : N * V = N * m2 - N * mu ^ 2 := by rw [hVeq]; ring
  constructor
  · nlinarith only [hVeq, sq_nonneg mu]
  · by_contra hbad
    have hpos := mul_pos hN (sub_pos.mpr (lt_of_not_ge hbad))
    nlinarith only [hscaled, hmu, hVlo, hpos]

theorem sourceTruncation_gamma_bounds
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : truncationBudget nu n x ≤ epsilon ^ 3 / 8) :
    let h : ℝ := epsilon / (1 + x)
    let rho : Measure ℝ := ProbabilityTheory.cond nu {z | |z| ≤ h}
    let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
    let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
    let V : ℝ := ProbabilityTheory.variance (id : ℝ → ℝ) rho
    let gamma : ℝ := m3 / V
    let r : ℝ := truncationBudget nu n 0
    0 < m3 ∧ 0 < gamma ∧
      Real.sqrt m2 * m2 ≤ m3 ∧
      m2 ≤ gamma ^ 2 ∧ gamma ≤ 2 * h ∧
      (3 / 4 : ℝ) * (n : ℝ) * m3 ≤ gamma ∧
      gamma ≤ 2 * (n : ℝ) * m3 ∧
      (n : ℝ) * m3 ≤ 2 * r ∧ gamma ≤ 4 * r := by
  let a : ℝ := 1 + x
  let h : ℝ := epsilon / a
  let rho : Measure ℝ := ProbabilityTheory.cond nu {z | |z| ≤ h}
  let mu : ℝ := ∫ z : ℝ, z ∂rho
  let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
  let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
  let V : ℝ := ProbabilityTheory.variance (id : ℝ → ℝ) rho
  let gamma : ℝ := m3 / V
  let r : ℝ := truncationBudget nu n 0
  have ha1 : 1 ≤ a := by dsimp [a]; linarith
  have ha : 0 < a := by linarith
  have hh : 0 ≤ h := div_nonneg hepsilon.le ha.le
  obtain ⟨_, _, hn64, _⟩ := sourceTruncation_sample_size nu n h2 hnorm x epsilon hx
    hepsilon hepsilonHalf hR
  have hN : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨_, _, hp, hs, _, h2r, h3r, _⟩ :=
    sourceTruncation_law_data nu n h2 hnorm x epsilon hx hepsilon hepsilonHalf hR
  have instProb : IsProbabilityMeasure rho := hp
  obtain ⟨_, _, hmu, hVeq, _, hVp, hVlo, hVhi⟩ :=
    sourceTruncation_variance_bounds nu n h2 hnorm hmean x epsilon hx
      hepsilon hepsilonHalf hR
  change (n : ℝ) * mu ^ 2 ≤ 1 / 4 at hmu
  change V = m2 - mu ^ 2 at hVeq
  change 0 < V at hVp
  change (1 / 2 : ℝ) ≤ (n : ℝ) * V at hVlo
  change (n : ℝ) * V ≤ (4 / 3 : ℝ) at hVhi
  obtain ⟨hVm2, hm2V⟩ := sf_variance_ratio (n : ℝ) mu m2 V hN hmu hVlo hVeq
  have hm2 : 0 < m2 := hVp.trans_le hVm2
  have hlyap : Real.sqrt m2 * m2 ≤ m3 := sf_raw_lyapunov rho h2r h3r
  have hm3 : 0 < m3 := (mul_pos (Real.sqrt_pos.2 hm2) hm2).trans_le hlyap
  have hgamma : 0 < gamma := div_pos hm3 hVp
  have hroot : Real.sqrt m2 ≤ gamma := by
    apply (le_div_iff₀ hVp).2
    exact (mul_le_mul_of_nonneg_left hVm2 (Real.sqrt_nonneg m2)).trans hlyap
  have hm2gamma : m2 ≤ gamma ^ 2 := by
    have hsquare := pow_le_pow_left₀ (Real.sqrt_nonneg m2) hroot 2
    rwa [Real.sq_sqrt hm2.le] at hsquare
  have hcube : m3 ≤ h * m2 := by
    have hi := integral_mono_ae h3r (h2r.const_mul h) (by
      filter_upwards [hs] with z hz
      calc
        |z| ^ 3 = |z| * z ^ 2 := by rw [← sq_abs z]; ring
        _ ≤ h * z ^ 2 := mul_le_mul_of_nonneg_right hz (sq_nonneg z))
    simpa only [integral_const_mul] using hi
  have hgammaCutoff : gamma ≤ 2 * h := by
    apply (div_le_iff₀ hVp).2
    calc
      m3 ≤ h * m2 := hcube
      _ ≤ h * (2 * V) := mul_le_mul_of_nonneg_left hm2V hh
      _ = (2 * h) * V := by ring
  have hgammaV : gamma * V = m3 := div_mul_cancel₀ m3 hVp.ne'
  have hid : gamma * ((n : ℝ) * V) = (n : ℝ) * m3 := by
    calc
      _ = (n : ℝ) * (gamma * V) := by ring
      _ = _ := by rw [hgammaV]
  have hgammaLo : (3 / 4 : ℝ) * (n : ℝ) * m3 ≤ gamma := by
    have hi := mul_le_mul_of_nonneg_left hVhi hgamma.le
    nlinarith only [hi, hid]
  have hgammaHi : gamma ≤ 2 * (n : ℝ) * m3 := by
    have hi := mul_le_mul_of_nonneg_left hVlo hgamma.le
    nlinarith only [hi, hid]
  have hpaid := (sourceTruncation_paid_moments nu n h2 hnorm hmean x epsilon hx
    hepsilon hepsilonHalf hR).2.1
  change (n : ℝ) * m3 ≤ 2 * truncationBudget nu n x / a ^ 3 at hpaid
  have hscale : truncationBudget nu n x ≤ a ^ 3 * r := by
    have hi := (truncationBudget_scale_one_le nu n h2 0 a ha1).2
    have harg : a * (1 + 0) - 1 = x := by dsimp [a]; ring
    simpa only [harg] using hi
  have hraw : (n : ℝ) * m3 ≤ 2 * r := by
    apply hpaid.trans
    apply (div_le_iff₀ (pow_pos ha 3)).2
    nlinarith only [hscale]
  change 0 < m3 ∧ 0 < gamma ∧ Real.sqrt m2 * m2 ≤ m3 ∧
    m2 ≤ gamma ^ 2 ∧ gamma ≤ 2 * h ∧
    (3 / 4 : ℝ) * (n : ℝ) * m3 ≤ gamma ∧
    gamma ≤ 2 * (n : ℝ) * m3 ∧ (n : ℝ) * m3 ≤ 2 * r ∧ gamma ≤ 4 * r
  exact ⟨hm3, hgamma, hlyap, hm2gamma, hgammaCutoff, hgammaLo, hgammaHi, hraw,
    by nlinarith only [hgammaHi, hraw]⟩

theorem sourceTruncation_oddPower_scale_inputs
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : truncationBudget nu n x ≤ epsilon ^ 3 / 8)
    (i : ℕ) (hi : i ≤ n) (L2 : ℝ) (hL2 : 20 ≤ L2)
    (hT :
      let rho : Measure ℝ :=
        ProbabilityTheory.cond nu {z | |z| ≤ epsilon / (1 + x)}
      let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
      let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂rho) /
        ProbabilityTheory.variance (id : ℝ → ℝ) rho
      L2 * gamma ^ 2 ≤ ((n - i : ℕ) : ℝ) * m2) :
    let rho : Measure ℝ :=
      ProbabilityTheory.cond nu {z | |z| ≤ epsilon / (1 + x)}
    let mu : ℝ := ∫ z : ℝ, z ∂rho
    let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
    let V : ℝ := ProbabilityTheory.variance (id : ℝ → ℝ) rho
    let ell : ℕ := n - i
    L2 ≤ (ell : ℝ) ∧ 6 ≤ ell ∧ ell ≤ n ∧
      (n : ℝ) * |mu| ≤ 1 ∧ m2 ≤ 4 * V := by
  let a : ℝ := 1 + x
  let rho : Measure ℝ := ProbabilityTheory.cond nu {z | |z| ≤ epsilon / a}
  let mu : ℝ := ∫ z : ℝ, z ∂rho
  let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
  let V : ℝ := ProbabilityTheory.variance (id : ℝ → ℝ) rho
  let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂rho) / V
  let ell : ℕ := n - i
  have ha1 : 1 ≤ a := by dsimp [a]; linarith
  have ha : 0 < a := by linarith
  obtain ⟨_, hgamma, _, hm2gamma, _, _, _, _, _⟩ :=
    sourceTruncation_gamma_bounds nu n h2 hnorm hmean x epsilon hx
      hepsilon hepsilonHalf hR
  change 0 < gamma at hgamma
  change m2 ≤ gamma ^ 2 at hm2gamma
  have hregion : L2 * gamma ^ 2 ≤ (ell : ℝ) * m2 := hT
  have hlength : L2 ≤ (ell : ℝ) := by
    have hbound := hregion.trans
      (mul_le_mul_of_nonneg_left hm2gamma (Nat.cast_nonneg ell))
    by_contra hbad
    have hpos := mul_pos (sub_pos.mpr (lt_of_not_ge hbad)) (pow_pos hgamma 2)
    nlinarith only [hbound, hpos]
  have hell6 : 6 ≤ ell := by
    have hreal : (6 : ℝ) ≤ (ell : ℝ) := by linarith
    exact_mod_cast hreal
  have helln : ell ≤ n := by dsimp [ell]; omega
  obtain ⟨_, _, hn64, _⟩ := sourceTruncation_sample_size nu n h2 hnorm x epsilon hx
    hepsilon hepsilonHalf hR
  have hN : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨_, _, hmu, hVeq, _, hVp, hVlo, _⟩ :=
    sourceTruncation_variance_bounds nu n h2 hnorm hmean x epsilon hx
      hepsilon hepsilonHalf hR
  have hm2V : m2 ≤ 2 * V :=
    (sf_variance_ratio (n : ℝ) mu m2 V hN hmu hVlo hVeq).2
  have hpaid := (sourceTruncation_paid_moments nu n h2 hnorm hmean x epsilon hx
    hepsilon hepsilonHalf hR).1
  change (n : ℝ) * |mu| ≤ 2 * truncationBudget nu n x / (epsilon ^ 2 * a) at hpaid
  have hbias : (n : ℝ) * |mu| ≤ (1 / 8 : ℝ) := by
    apply hpaid.trans
    apply (div_le_iff₀ (mul_pos (pow_pos hepsilon 2) ha)).2
    have hh := mul_le_mul_of_nonneg_left
      (show 2 * epsilon ≤ a by linarith) (sq_nonneg epsilon)
    nlinarith only [hR, hh]
  change L2 ≤ (ell : ℝ) ∧ 6 ≤ ell ∧ ell ≤ n ∧ (n : ℝ) * |mu| ≤ 1 ∧ m2 ≤ 4 * V
  exact ⟨hlength, hell6, helln, hbias.trans (by norm_num), by linarith only [hm2V, hVp]⟩

end Shao
