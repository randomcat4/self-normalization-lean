import Shao.Probability.BoundedQuadraticTilt
import Shao.Probability.LowFrequencyDamping
import Shao.Probability.SourceFourierScale

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

private theorem tlf_power_integrable (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h : ℝ) (hs : ∀ᵐ a : ℝ ∂nu, |a| ≤ h) (k : ℕ) :
    Integrable (fun a : ℝ => a ^ k) nu ∧
      Integrable (fun a : ℝ => |a| ^ k) nu := by
  have hp : ∀ᵐ a : ℝ ∂nu, |a| ^ k ≤ h ^ k :=
    hs.mono fun a ha => pow_le_pow_left₀ (abs_nonneg a) ha k
  constructor
  · exact (integrable_const (h ^ k)).mono' (by fun_prop) (by
      simpa only [Real.norm_eq_abs, abs_pow] using hp)
  · refine (integrable_const (h ^ k)).mono' (by fun_prop) ?_
    filter_upwards [hp] with a ha
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg a) k)] using ha

private theorem tlf_raw_root (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun a : ℝ => a ^ 2) nu)
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu) :
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
    let V : ℝ := variance (id : ℝ → ℝ) nu
    let gamma : ℝ := m3 / V
    0 < m3 ∧ 0 < gamma ∧ Real.sqrt m2 ≤ gamma ∧ m2 ≤ gamma ^ 2 := by
  dsimp only
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
  let V : ℝ := variance (id : ℝ → ℝ) nu
  let gamma : ℝ := m3 / V
  let t : ℝ := Real.sqrt m2
  have hformula : V = m2 - (∫ a : ℝ, a ∂nu) ^ 2 := by
    simpa only [V, m2, Pi.pow_apply, id_eq] using
      variance_eq_sub ((memLp_two_iff_integrable_sq
        measurable_id.aestronglyMeasurable).2 h2)
  have hVm2 : V ≤ m2 := by nlinarith only [hformula, sq_nonneg (∫ a : ℝ, a ∂nu)]
  have hm2 : 0 < m2 := hV.trans_le hVm2
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = m2 := Real.sq_sqrt hm2.le
  have hpoint (z : ℝ) : (3 * t) * z ^ 2 ≤ 2 * |z| ^ 3 + t ^ 3 := by
    have hfactor := mul_nonneg (sq_nonneg (|z| - t))
      (show 0 ≤ 2 * |z| + t by positivity)
    rw [← sq_abs z]
    nlinarith only [hfactor]
  have hint := integral_mono (h2.const_mul (3 * t))
    ((h3.const_mul 2).add (integrable_const (t ^ 3))) hpoint
  change (∫ a : ℝ, (3 * t) * a ^ 2 ∂nu) ≤
    ∫ a : ℝ, 2 * |a| ^ 3 + t ^ 3 ∂nu at hint
  rw [integral_const_mul, integral_add (h3.const_mul 2) (integrable_const (t ^ 3)),
    integral_const_mul, integral_const, probReal_univ, one_smul] at hint
  have ht3 : t ^ 3 = t * m2 := by rw [pow_succ, ht2]; ring
  have hlyap : t * m2 ≤ m3 := by change (3 * t) * m2 ≤ 2 * m3 + t ^ 3 at hint; linarith
  have hm3 : 0 < m3 := (mul_pos (Real.sqrt_pos.2 hm2) hm2).trans_le hlyap
  have hgamma : 0 < gamma := div_pos hm3 hV
  have hroot : Real.sqrt m2 ≤ gamma := by
    apply (le_div_iff₀ hV).2
    exact (mul_le_mul_of_nonneg_left hVm2 (Real.sqrt_nonneg _)).trans hlyap
  have hsquare := pow_le_pow_left₀ (Real.sqrt_nonneg m2) hroot 2
  rw [Real.sq_sqrt hm2.le] at hsquare
  exact ⟨hm3, hgamma, hroot, hsquare⟩

private theorem tlf_mean_comparison
    (mu m2 m3 V murho Vrho h lam s y : ℝ)
    (hh : 0 < h) (hlam : 0 ≤ lam) (hs : 0 ≤ s) (hsquare : s ≤ lam ^ 2)
    (hy : 2 ≤ y) (hV : 0 < V) (hVrho : 0 < Vrho)
    (hmu : |mu| ≤ V) (hm2V : m2 ≤ (8 / 3 : ℝ) * V)
    (hgamma : 0 < m3 / V) (hroot : Real.sqrt V ≤ m3 / V)
    (hvar : Real.exp (-(4 * lam * h)) * V ≤ Vrho)
    (hmean : |murho| ≤ Real.exp (4 * lam * h) * (|mu| + lam * m2 + s * m3))
    (hsmall : (y + lam) * (8 * Real.exp (8 * lam * h) * (m3 / V)) ≤ (1 / 8 : ℝ)) :
    |murho| ≤ Real.sqrt Vrho ∧ murho ^ 2 ≤ Vrho := by
  let a : ℝ := lam * h
  let gamma : ℝ := m3 / V
  let Gamma : ℝ := 8 * Real.exp (8 * a) * gamma
  let t : ℝ := Real.sqrt V
  let tr : ℝ := Real.sqrt Vrho
  let B : ℝ := gamma + (8 / 3 : ℝ) * lam * gamma + s * gamma ^ 2
  let k : ℝ := (y + lam) * Gamma
  have ha : 0 ≤ a := mul_nonneg hlam hh.le
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have htr : 0 ≤ tr := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = V := Real.sq_sqrt hV.le
  have htr2 : tr ^ 2 = Vrho := Real.sq_sqrt hVrho.le
  have htg : t ≤ gamma := hroot
  have hG : 0 < Gamma := by dsimp [Gamma]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmut : |mu| ≤ gamma * t := by
    have h := mul_le_mul_of_nonneg_right htg ht
    nlinarith only [hmu, ht2, h]
  have hm2t : m2 ≤ (8 / 3 : ℝ) * gamma * t := by
    have h := mul_le_mul_of_nonneg_right htg ht
    nlinarith only [hm2V, ht2, h]
  have hgammaV : gamma * V = m3 := div_mul_cancel₀ _ hV.ne'
  have hm3t : m3 ≤ gamma ^ 2 * t := by
    have h := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right htg ht) hgamma.le
    calc
      m3 = gamma * (t * t) := by rw [← pow_two, ht2, hgammaV]
      _ ≤ gamma * (gamma * t) := h
      _ = gamma ^ 2 * t := by ring
  have hbase : |mu| + lam * m2 + s * m3 ≤ B * t := by
    have hl := mul_le_mul_of_nonneg_left hm2t hlam
    have hs' := mul_le_mul_of_nonneg_left hm3t hs
    dsimp only [B]
    nlinarith only [hmut, hl, hs']
  have hvar' : Real.exp (-(4 * a)) * V ≤ Vrho := by simpa [a, mul_assoc] using hvar
  have hvarmul := mul_le_mul_of_nonneg_left hvar' (Real.exp_pos (4 * a)).le
  have hcancel : Real.exp (4 * a) * Real.exp (-(4 * a)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hVmul : V ≤ Real.exp (4 * a) * Vrho := by
    simpa only [← mul_assoc, hcancel, one_mul] using hvarmul
  have htime : t ≤ Real.exp (2 * a) * tr := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [mul_pow, htr2]
      have he : Real.exp (2 * a) ^ 2 = Real.exp (4 * a) := by
        rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
      rw [he]
      exact hVmul
  have hmean' : |murho| ≤ Real.exp (4 * a) * (|mu| + lam * m2 + s * m3) := by
    simpa [a, mul_assoc] using hmean
  have hmeanB : |murho| ≤ Real.exp (6 * a) * B * tr := by
    calc
      |murho| ≤ Real.exp (4 * a) * (|mu| + lam * m2 + s * m3) := hmean'
      _ ≤ Real.exp (4 * a) * (B * t) :=
        mul_le_mul_of_nonneg_left hbase (Real.exp_pos _).le
      _ ≤ Real.exp (4 * a) * (B * (Real.exp (2 * a) * tr)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htime hB)
          (Real.exp_pos _).le
      _ = Real.exp (6 * a) * B * tr := by
        rw [show 6 * a = 4 * a + 2 * a by ring, Real.exp_add]
        ring
  have he68 : Real.exp (6 * a) ≤ Real.exp (8 * a) :=
    Real.exp_le_exp.mpr (by nlinarith only [ha])
  have he616 : Real.exp (6 * a) ≤ Real.exp (16 * a) :=
    Real.exp_le_exp.mpr (by nlinarith only [ha])
  have hg6 : Real.exp (6 * a) * gamma ≤ Gamma / 8 := by
    have hh := mul_le_mul_of_nonneg_right he68 hgamma.le
    dsimp only [Gamma]
    nlinarith only [hh]
  have hg26 : Real.exp (6 * a) * gamma ^ 2 ≤ Gamma ^ 2 / 64 := by
    calc
      _ ≤ Real.exp (16 * a) * gamma ^ 2 :=
        mul_le_mul_of_nonneg_right he616 (sq_nonneg gamma)
      _ = Gamma ^ 2 / 64 := by
        dsimp only [Gamma]
        rw [show 16 * a = 8 * a + 8 * a by ring, Real.exp_add]
        ring
  have hterm2 : Real.exp (6 * a) * ((8 / 3 : ℝ) * lam * gamma) ≤ lam * Gamma / 3 := by
    have hh := mul_le_mul_of_nonneg_left hg6 (show 0 ≤ (8 / 3 : ℝ) * lam by positivity)
    nlinarith only [hh]
  have hterm3 : Real.exp (6 * a) * (s * gamma ^ 2) ≤ (lam * Gamma) ^ 2 / 64 := by
    have hh := mul_le_mul_of_nonneg_left hg26 hs
    have hh' := mul_le_mul_of_nonneg_right hsquare (div_nonneg (sq_nonneg Gamma) (by norm_num : (0 : ℝ) ≤ 64))
    nlinarith only [hh, hh']
  have hsum : Real.exp (6 * a) * B ≤ Gamma / 8 + lam * Gamma / 3 + (lam * Gamma) ^ 2 / 64 := by
    dsimp only [B]
    nlinarith only [hg6, hterm2, hterm3]
  have hk0 : 0 ≤ k := by dsimp [k]; positivity
  have hk : k ≤ (1 / 8 : ℝ) := by simpa [k, Gamma, a, gamma, mul_assoc] using hsmall
  have hGk : Gamma ≤ k / 2 := by
    have hh := mul_le_mul_of_nonneg_right hy hG.le
    dsimp only [k]
    nlinarith only [hh, mul_nonneg hlam hG.le]
  have hlk : lam * Gamma ≤ k := by
    dsimp only [k]
    nlinarith only [mul_nonneg (show 0 ≤ y by linarith only [hy]) hG.le]
  have hl0 : 0 ≤ lam * Gamma := mul_nonneg hlam hG.le
  have hl2 : (lam * Gamma) ^ 2 ≤ k ^ 2 := pow_le_pow_left₀ hl0 hlk 2
  have hk2 : k ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := pow_le_pow_left₀ hk0 hk 2
  have hsmallB : Real.exp (6 * a) * B ≤ 1 := by
    nlinarith only [hsum, hGk, hlk, hl2, hk2, hk]
  have hfinal : |murho| ≤ tr :=
    hmeanB.trans (by nlinarith only [mul_le_mul_of_nonneg_right hsmallB htr])
  refine ⟨hfinal, ?_⟩
  have hh := pow_le_pow_left₀ (abs_nonneg murho) hfinal 2
  simpa only [sq_abs, htr2] using hh


theorem boundedQuadraticTilt_joint_second_moments_lowFrequency
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (n : ℕ) (h lam b s y : ℝ)
    (hh : 0 < h) (hlam : 0 ≤ lam)
    (hb : b = lam ∨ b = -lam)
    (hs : 0 ≤ s) (hsquare : s ≤ lam ^ 2)
    (hslope : s * h ≤ lam)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (hy : 2 ≤ y)
    (hnV : (1 / 2 : ℝ) ≤
      (n : ℝ) * variance (id : ℝ → ℝ) nu)
    (hnm2 : (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu) ≤ (4 / 3 : ℝ))
    (hnmu : (n : ℝ) * |∫ a : ℝ, a ∂nu| ≤ (1 / 2 : ℝ)) :
    let rho : Measure ℝ := nu.tilted (fun a => b * a - s * a ^ 2)
    let mu : ℝ := ∫ a : ℝ, a ∂nu
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
    let V : ℝ := variance (id : ℝ → ℝ) nu
    let gamma : ℝ := m3 / V
    let murho : ℝ := ∫ a : ℝ, a ∂rho
    let m2rho : ℝ := ∫ a : ℝ, a ^ 2 ∂rho
    let m3rho : ℝ := ∫ a : ℝ, |a| ^ 3 ∂rho
    let Vrho : ℝ := variance (id : ℝ → ℝ) rho
    let Gamma : ℝ := 8 * Real.exp (8 * lam * h) * gamma
    IsProbabilityMeasure rho ∧
      (∀ᵐ a : ℝ ∂rho, |a| ≤ h) ∧
      Integrable (fun a : ℝ => a) rho ∧
      Integrable (fun a : ℝ => a ^ 2) rho ∧
      Integrable (fun a : ℝ => |a| ^ 3) rho ∧
      0 < V ∧ 0 < Vrho ∧ 0 < Gamma ∧
      Real.exp (-(4 * lam * h)) * V ≤ Vrho ∧
      Vrho ≤ Real.exp (4 * lam * h) * V ∧
      m3rho / Vrho ≤ Gamma ∧
      Real.sqrt m2rho ≤ Gamma ∧ m2rho ≤ Gamma ^ 2 ∧
      ((y + lam) * Gamma ≤ (1 / 8 : ℝ) →
        |murho| ≤ Real.sqrt Vrho ∧ murho ^ 2 ≤ Vrho ∧
          Vrho ≤ m2rho ∧ m2rho ≤ 2 * Vrho) ∧
      (∀ (ell : ℕ) (u v : ℝ),
        |u| ≤ (1 / 128 : ℝ) / Gamma →
        |v| ≤ (1 / 128 : ℝ) * |u| / Gamma →
        ‖(quadraticChar rho u v) ^ ell‖ ≤
            Real.exp (-Real.exp (-(4 * lam * h)) *
              ((ell : ℝ) * m2) * u ^ 2 / 128) ∧
          ‖(quadraticChar rho (-u) v) ^ ell‖ ≤
            Real.exp (-Real.exp (-(4 * lam * h)) *
              ((ell : ℝ) * m2) * u ^ 2 / 128)) := by
  dsimp only
  let rho : Measure ℝ := nu.tilted (fun a => b * a - s * a ^ 2)
  let mu : ℝ := ∫ a : ℝ, a ∂nu
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
  let V : ℝ := variance (id : ℝ → ℝ) nu
  let gamma : ℝ := m3 / V
  let murho : ℝ := ∫ a : ℝ, a ∂rho
  let m2rho : ℝ := ∫ a : ℝ, a ^ 2 ∂rho
  let m3rho : ℝ := ∫ a : ℝ, |a| ^ 3 ∂rho
  let Vrho : ℝ := variance (id : ℝ → ℝ) rho
  let Gamma : ℝ := 8 * Real.exp (8 * lam * h) * gamma
  have hn : (0 : ℝ) < n := by
    by_contra hn
    have hn0 : (n : ℝ) = 0 := le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg n)
    simp only [hn0, zero_mul] at hnV
    norm_num at hnV
  have hV : 0 < V := by
    by_contra hV
    have h := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (le_of_not_gt hV)
    change (n : ℝ) * V ≤ 0 at h
    linarith only [hnV, h]
  have hm2V : m2 ≤ (8 / 3 : ℝ) * V := by
    by_contra hbad
    have hh := mul_pos hn (sub_pos.mpr (lt_of_not_ge hbad))
    nlinarith only [hh, hnm2, hnV]
  have hmuV : |mu| ≤ V := by
    by_contra hbad
    have hh := mul_pos hn (sub_pos.mpr (lt_of_not_ge hbad))
    nlinarith only [hh, hnmu, hnV]
  have h2 := (tlf_power_integrable nu h hsupport 2).1
  have h3 := (tlf_power_integrable nu h hsupport 3).2
  have hformula : V = m2 - mu ^ 2 := by
    simpa only [V, m2, mu, Pi.pow_apply, id_eq] using
      variance_eq_sub ((memLp_two_iff_integrable_sq
        measurable_id.aestronglyMeasurable).2 h2)
  have hVm2 : V ≤ m2 := by nlinarith only [hformula, sq_nonneg mu]
  obtain ⟨hm3, hg, hroot, _⟩ := tlf_raw_root nu h2 h3 hV
  have hrootV : Real.sqrt V ≤ gamma := (Real.sqrt_le_sqrt hVm2).trans hroot
  have hG : 0 < Gamma := by dsimp [Gamma]; positivity
  obtain ⟨_, hp, hsr, h1r, h2r, h3r, _, _, _, _, _, hvl, hvu,
    _, _, _, hVeq, hmean, _, _, hpos, _, _, _⟩ :=
    boundedQuadraticTilt_joint_moments_normalizer nu h lam b s hh hlam hb hs hsquare hslope hsupport
  have hprob : IsProbabilityMeasure rho := hp
  letI : IsProbabilityMeasure rho := hprob
  obtain ⟨hVr, hgr⟩ := hpos hV
  obtain ⟨_, hgrpos, hrootr, hrawr⟩ := tlf_raw_root rho h2r h3r hVr
  have hrootG : Real.sqrt m2rho ≤ Gamma := hrootr.trans hgr
  have hrawG : m2rho ≤ Gamma ^ 2 := hrawr.trans (pow_le_pow_left₀ hgrpos.le hgr 2)
  refine ⟨hp, hsr, h1r, h2r, h3r, hV, hVr, hG, hvl, hvu, hgr, hrootG, hrawG, ?_, ?_⟩
  · intro hsmall
    obtain ⟨hmeanroot, hmeansq⟩ := tlf_mean_comparison mu m2 m3 V murho Vrho h lam s y
      hh hlam hs hsquare hy hV hVr hmuV hm2V hg hrootV hvl hmean hsmall
    refine ⟨hmeanroot, hmeansq, ?_, ?_⟩ <;>
      nlinarith only [hVeq, hmeansq, sq_nonneg murho]
  · intro ell u v hu hv
    let gr : ℝ := m3rho / Vrho
    have hgrpos' : 0 < gr := hgrpos
    have hu' : |u| ≤ (1 / 128 : ℝ) / gr := hu.trans
      (div_le_div₀ (by norm_num : (0 : ℝ) ≤ 1 / 128) le_rfl hgrpos' hgr)
    have hv' : |v| ≤ (1 / 128 : ℝ) * |u| / gr := hv.trans
      (div_le_div₀ (by positivity) le_rfl hgrpos' hgr)
    obtain ⟨hplus, hminus⟩ := quadraticChar_lowFrequency_damping rho h3r hVr u v hu' hv'
    have hvarm2 : Real.exp (-(4 * lam * h)) * m2 ≤ (8 / 3 : ℝ) * Vrho := by
      have h1 := mul_le_mul_of_nonneg_left hm2V (Real.exp_pos (-(4 * lam * h))).le
      have h2 := mul_le_mul_of_nonneg_left hvl (by norm_num : (0 : ℝ) ≤ 8 / 3)
      nlinarith only [h1, h2]
    have hcoef : Real.exp (-(4 * lam * h)) * m2 / 128 ≤ Vrho / 32 := by
      nlinarith only [hvarm2, hVr.le]
    have hexponent : (ell : ℝ) * (-Vrho * u ^ 2 / 32) ≤
        -Real.exp (-(4 * lam * h)) * ((ell : ℝ) * m2) * u ^ 2 / 128 := by
      have hmul := mul_le_mul_of_nonneg_right hcoef
        (mul_nonneg (Nat.cast_nonneg ell) (sq_nonneg u))
      nlinarith only [hmul]
    have hpower (z : ℂ) (hz : ‖z‖ ≤ Real.exp (-Vrho * u ^ 2 / 32)) :
        ‖z ^ ell‖ ≤ Real.exp (-Real.exp (-(4 * lam * h)) * ((ell : ℝ) * m2) * u ^ 2 / 128) := by
      calc
        ‖z ^ ell‖ = ‖z‖ ^ ell := norm_pow z ell
        _ ≤ (Real.exp (-Vrho * u ^ 2 / 32)) ^ ell := pow_le_pow_left₀ (norm_nonneg z) hz ell
        _ = Real.exp ((ell : ℝ) * (-Vrho * u ^ 2 / 32)) := by rw [Real.exp_nat_mul]
        _ ≤ _ := Real.exp_le_exp.mpr hexponent
    exact ⟨hpower _ hplus, hpower _ hminus⟩


theorem sourceTruncation_jointTilt_second_moments_lowFrequency
    (nu0 : Measure ℝ) [IsProbabilityMeasure nu0] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu0) = 1)
    (hmean : (∫ z : ℝ, z ∂nu0) = 0)
    (x epsilon epsilon0 : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilon0 : 0 < epsilon0)
    (hepsilon0One : epsilon0 ≤ 1)
    (hepsilonSmall : epsilon ≤ epsilon0 / 2)
    (hR : Shao.truncationBudget nu0 n x ≤ epsilon ^ 3 / 8)
    (y : ℝ) (hy : 2 ≤ y)
    (hwindow : |y - x| ≤ 1 / (2 * (1 + x)))
    (hyh : y * (epsilon0 / (1 + y)) ≤ (1 / 4 : ℝ))
    (i : ℕ) (hi : i ≤ n) (q : ℝ) (hq : 0 ≤ q)
    (hNlo : (1 / 16 : ℝ) ≤ q + ((n - i : ℕ) : ℝ) *
      (∫ z : ℝ, z ^ 2 ∂ProbabilityTheory.cond nu0
        {z : ℝ | |z| ≤ epsilon / (1 + x)}))
    (hNhi : q + ((n - i : ℕ) : ℝ) *
      (∫ z : ℝ, z ^ 2 ∂ProbabilityTheory.cond nu0
        {z : ℝ | |z| ≤ epsilon / (1 + x)}) ≤ 7)
    (lam b s : ℝ)
    (hlam : y / Real.sqrt (q + ((n - i : ℕ) : ℝ) *
      (∫ z : ℝ, z ^ 2 ∂ProbabilityTheory.cond nu0
        {z : ℝ | |z| ≤ epsilon / (1 + x)})) ≤ lam)
    (hb : b = lam ∨ b = -lam)
    (hschoice : s = 0 ∨ s = lam * y / Real.sqrt
      (q + ((n - i : ℕ) : ℝ) *
        (∫ z : ℝ, z ^ 2 ∂ProbabilityTheory.cond nu0
          {z : ℝ | |z| ≤ epsilon / (1 + x)}))) :
    let nu : Measure ℝ := ProbabilityTheory.cond nu0
      {z : ℝ | |z| ≤ epsilon / (1 + x)}
    let h : ℝ := epsilon0 / (1 + y)
    let mu : ℝ := ∫ a : ℝ, a ∂nu
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
    let V : ℝ := variance (id : ℝ → ℝ) nu
    let gamma : ℝ := m3 / V
    let T : ℝ := ((n - i : ℕ) : ℝ) * m2
    let N : ℝ := q + T
    let rho : Measure ℝ := nu.tilted (fun a => b * a - s * a ^ 2)
    let murho : ℝ := ∫ a : ℝ, a ∂rho
    let m2rho : ℝ := ∫ a : ℝ, a ^ 2 ∂rho
    let m3rho : ℝ := ∫ a : ℝ, |a| ^ 3 ∂rho
    let Vrho : ℝ := variance (id : ℝ → ℝ) rho
    let Gamma : ℝ := 8 * Real.exp (8 * lam * h) * gamma
    IsProbabilityMeasure nu ∧ IsProbabilityMeasure rho ∧
      0 < h ∧ epsilon / (1 + x) ≤ h ∧
      (∀ᵐ a : ℝ ∂nu, |a| ≤ h) ∧
      (∀ᵐ a : ℝ ∂rho, |a| ≤ h) ∧
      0 ≤ lam ∧ 0 ≤ s ∧ s ≤ lam ^ 2 ∧ s * h ≤ lam ∧
      0 ≤ T ∧ T ≤ (4 / 3 : ℝ) ∧ (1 / 16 : ℝ) ≤ N ∧ N ≤ 7 ∧
      (3 / 4 : ℝ) ≤ (n : ℝ) * m2 ∧
      (n : ℝ) * m2 ≤ (4 / 3 : ℝ) ∧
      (1 / 2 : ℝ) ≤ (n : ℝ) * V ∧
      (n : ℝ) * |mu| ≤ epsilon / (4 * (1 + x)) ∧
      (n : ℝ) * |mu| ≤ (1 / 2 : ℝ) ∧
      0 < V ∧ 0 < Vrho ∧ 0 < gamma ∧ 0 < Gamma ∧
      gamma ≤ y ∧
      Integrable (fun a : ℝ => a) rho ∧
      Integrable (fun a : ℝ => a ^ 2) rho ∧
      Integrable (fun a : ℝ => |a| ^ 3) rho ∧
      Real.exp (-(4 * lam * h)) * V ≤ Vrho ∧
      Vrho ≤ Real.exp (4 * lam * h) * V ∧
      m3rho / Vrho ≤ Gamma ∧
      Real.sqrt m2rho ≤ Gamma ∧ m2rho ≤ Gamma ^ 2 ∧
      ((y + lam) * Gamma ≤ (1 / 8 : ℝ) →
        |murho| ≤ Real.sqrt Vrho ∧ murho ^ 2 ≤ Vrho ∧
          Vrho ≤ m2rho ∧ m2rho ≤ 2 * Vrho) ∧
      (∀ u v : ℝ,
        |u| ≤ (1 / 128 : ℝ) / Gamma →
        |v| ≤ (1 / 128 : ℝ) * |u| / Gamma →
        ‖(quadraticChar rho u v) ^ (n - i)‖ ≤
            Real.exp (-Real.exp (-(4 * lam * h)) * T * u ^ 2 / 128) ∧
          ‖(quadraticChar rho (-u) v) ^ (n - i)‖ ≤
            Real.exp (-Real.exp (-(4 * lam * h)) * T * u ^ 2 / 128)) := by
  dsimp only
  let nu : Measure ℝ := ProbabilityTheory.cond nu0 {z : ℝ | |z| ≤ epsilon / (1 + x)}
  let h : ℝ := epsilon0 / (1 + y)
  let mu : ℝ := ∫ a : ℝ, a ∂nu
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
  let V : ℝ := variance (id : ℝ → ℝ) nu
  let gamma : ℝ := m3 / V
  let T : ℝ := ((n - i : ℕ) : ℝ) * m2
  let N : ℝ := q + T
  let rho : Measure ℝ := nu.tilted (fun a => b * a - s * a ^ 2)
  let murho : ℝ := ∫ a : ℝ, a ∂rho
  let m2rho : ℝ := ∫ a : ℝ, a ^ 2 ∂rho
  let m3rho : ℝ := ∫ a : ℝ, |a| ^ 3 ∂rho
  let Vrho : ℝ := variance (id : ℝ → ℝ) rho
  let Gamma : ℝ := 8 * Real.exp (8 * lam * h) * gamma
  have hehalf : epsilon ≤ (1 / 2 : ℝ) := by linarith only [hepsilonSmall, hepsilon0One]
  have hxp : 0 < 1 + x := by linarith only [hx]
  have hyp : 0 < 1 + y := by linarith only [hy]
  have hh : 0 < h := div_pos hepsilon0 hyp
  obtain ⟨_, _, hp, hscut, _, _, _, _⟩ :=
    Shao.sourceTruncation_law_data nu0 n h2 hnorm x epsilon hx hepsilon hehalf hR
  have hpnu : IsProbabilityMeasure nu := hp
  letI : IsProbabilityMeasure nu := hpnu
  have hwindowhalf : 1 / (2 * (1 + x)) ≤ (1 : ℝ) :=
    (div_le_iff₀ (show 0 < 2 * (1 + x) by positivity)).2 (by nlinarith only [hx])
  have hscale : 1 + y ≤ 2 * (1 + x) := by
    have hw := (abs_le.mp hwindow).2
    linarith only [hw, hwindowhalf, hx]
  have hcut : epsilon / (1 + x) ≤ h := by
    apply (div_le_div_iff₀ hxp hyp).2
    calc
      epsilon * (1 + y) ≤ (epsilon0 / 2) * (1 + y) :=
        mul_le_mul_of_nonneg_right hepsilonSmall hyp.le
      _ ≤ (epsilon0 / 2) * (2 * (1 + x)) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = epsilon0 * (1 + x) := by ring
  have hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h := hscut.mono fun a ha => ha.trans hcut
  obtain ⟨hnm2lo, hnm2, _, _, _, hVp, hnV, _⟩ :=
    Shao.sourceTruncation_variance_bounds nu0 n h2 hnorm hmean x epsilon hx hepsilon hehalf hR
  have hpaid := (Shao.sourceTruncation_paid_moments nu0 n h2 hnorm hmean
    x epsilon hx hepsilon hehalf hR).1
  have hmeanpaid : (n : ℝ) * |mu| ≤ epsilon / (4 * (1 + x)) := by
    apply hpaid.trans
    apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hepsilon) hxp)
      (show 0 < 4 * (1 + x) by positivity)).2
    have hbound := mul_le_mul_of_nonneg_right hR (show 0 ≤ 8 * (1 + x) by positivity)
    nlinarith only [hbound]
  have hmeanhalf : (n : ℝ) * |mu| ≤ (1 / 2 : ℝ) := hmeanpaid.trans (by
    apply (div_le_iff₀ (show 0 < 4 * (1 + x) by positivity)).2
    nlinarith only [hx, hehalf])
  obtain ⟨_, hg, _, _, hgc, _, _, _, _⟩ := Shao.sourceTruncation_gamma_bounds
    nu0 n h2 hnorm hmean x epsilon hx hepsilon hehalf hR
  have hgy : gamma ≤ y := by
    have hhthird : h ≤ (1 / 3 : ℝ) := by
      apply (div_le_iff₀ hyp).2
      linarith only [hepsilon0One, hy]
    linarith only [hgc, hcut, hhthird, hy]
  have hm2nonneg : 0 ≤ m2 := integral_nonneg fun a => sq_nonneg a
  have hT : 0 ≤ T := mul_nonneg (Nat.cast_nonneg (n - i)) hm2nonneg
  have hTupper : T ≤ (4 / 3 : ℝ) := by
    have hsub : ((n - i : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n i
    exact (mul_le_mul_of_nonneg_right hsub hm2nonneg).trans hnm2
  have hN : 0 < N := lt_of_lt_of_le (by norm_num) hNlo
  have hNsqrt : (1 / 4 : ℝ) ≤ Real.sqrt N := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact hNlo
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hr : 0 ≤ y / Real.sqrt N := div_nonneg (by linarith only [hy]) hsqrt.le
  have hl : 0 ≤ lam := hr.trans hlam
  have hr4 : y / Real.sqrt N ≤ 4 * y := by
    apply (div_le_iff₀ hsqrt).2
    have hmul := mul_le_mul_of_nonneg_left hNsqrt (show 0 ≤ 4 * y by linarith only [hy])
    nlinarith only [hmul]
  have hsparams : 0 ≤ s ∧ s ≤ lam ^ 2 ∧ s * h ≤ lam := by
    rcases hschoice with hs0 | hs0
    · rw [hs0]
      exact ⟨le_rfl, sq_nonneg lam, by simpa only [zero_mul] using hl⟩
    · have hseq : s = lam * (y / Real.sqrt N) := by simpa only [mul_div_assoc] using hs0
      rw [hseq]
      refine ⟨mul_nonneg hl hr, ?_, ?_⟩
      · have hh := mul_le_mul_of_nonneg_left hlam hl
        nlinarith only [hh]
      · have hh' := mul_le_mul_of_nonneg_left hr4 (mul_nonneg hl hh.le)
        have hh'' := mul_le_mul_of_nonneg_left hyh hl
        nlinarith only [hh', hh'']
  obtain ⟨hpr, hsr, h1r, h2r, h3r, hV, hVr, hG, hvl, hvu, hgr, hrootr, hrawr,
    hcomparison, hfreq⟩ := boundedQuadraticTilt_joint_second_moments_lowFrequency
      nu n h lam b s y hh hl hb hsparams.1 hsparams.2.1 hsparams.2.2 hsupport hy hnV hnm2 hmeanhalf
  refine ⟨hpnu, hpr, hh, hcut, hsupport, hsr, hl, hsparams.1, hsparams.2.1, hsparams.2.2,
    hT, hTupper, hNlo, hNhi, hnm2lo, hnm2, hnV, hmeanpaid, hmeanhalf,
    hV, hVr, hg, hG, hgy, h1r, h2r, h3r, hvl, hvu, hgr, hrootr, hrawr, hcomparison, ?_⟩
  intro u v hu hv
  exact hfreq (n - i) u v hu hv

end Shao.Probability
