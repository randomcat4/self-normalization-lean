import Shao.OQ6.ConditionalVarianceMean
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Data.Nat.Find

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Shao.OQ6.ConditionalStandardizedPMoment

noncomputable section

open MeasureTheory ProbabilityTheory

theorem actual_conditional_standardized_pmoment
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun z : Ω × Ω => h z.1 z.2))
    (hh2 : MemLp (fun z : Ω × Ω => h z.1 z.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ z : Ω × Ω, h z.1 z.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (w : Ω → ℝ)
    (hw : Measurable w)
    (hwone : ∀ᵐ o ∂μ, 1 ≤ w o)
    (α τ : ℝ) (hα : 0 < α) (hτ : 0 < τ)
    (hwexp : Integrable (fun o => Real.exp (τ * Real.rpow (w o) α)) μ)
    (henvelope : ∀ᵐ z : Ω × Ω ∂(μ.prod μ),
      |h z.1 z.2 - (∫ y, h z.1 y ∂μ) - (∫ y, h z.2 y ∂μ)| ≤
        w z.1 * w z.2)
    (p : ℝ) (hp : 2 < p ∧ p ≤ 3)
    (hgp : Integrable
      (fun o => Real.rpow |∫ y, h o y ∂μ| p) μ) :
    let Np : ℕ := Nat.ceil (p / α)
    let Aexpp : ℝ := (Np.factorial : ℝ) / τ ^ Np
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
    let B : ℝ := Real.rpow β (1 / p)
    let Wp : ℝ := Real.rpow (∫ o, Real.rpow |w o| p ∂μ) (1 / p)
    0 < Aexpp ∧
      (∀ s : ℝ, 1 ≤ s →
        Real.rpow s p ≤ Aexpp * Real.exp (τ * Real.rpow s α)) ∧
      Integrable (fun o => Real.rpow |w o| p) μ ∧
      MemLp w (ENNReal.ofReal p) μ ∧
      MemLp g (ENNReal.ofReal p) μ ∧ 1 ≤ β ∧
      ∀ eps : ℝ, 0 < eps →
      ∃ N0 : ℕ, 1 ≤ N0 ∧
      ∀ R : ℝ, (N0 : ℝ) ≤ R →
      let C : Set Ω := {o : Ω | w o ≤ R}
      let π : ℝ := μ.real Cᶜ
      let d : ℝ := μ.real C
      let ν : Measure Ω := (μ C)⁻¹ • μ.restrict C
      let b : ℝ := ∫ o in Cᶜ, w o ∂μ
      let c : ℝ := b / d
      let u : ℝ := ∫ o, g o ∂ν
      let a : Ω → ℝ := fun o => ∫ y, r o y ∂ν
      let θ : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ∂(ν.prod ν)
      let Tp : ℝ := ∫ o in Cᶜ, Real.rpow |g o| p ∂μ
      let Mp : ℝ := ∫ o, Real.rpow |g o| p ∂ν
      (1 / 2 : ℝ) ≤ d ∧ d = 1 - π ∧
        IsProbabilityMeasure ν ∧ ν ≪ μ ∧ ν C = 1 ∧
        MemLp w (ENNReal.ofReal p) ν ∧
        MemLp g (ENNReal.ofReal p) ν ∧
        MemLp a (ENNReal.ofReal p) ν ∧
        Integrable (fun o => Real.rpow |g o| p) ν ∧
        Mp = (β - Tp) / d ∧ 0 ≤ Tp ∧ Tp ≤ eps ∧ |Mp - β| ≤ eps ∧
        ∀ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 →
        let H : Ω → Ω → ℝ := fun o y => g o + g y + lam * r o y
        let q : ℝ := ∫ z : Ω × Ω, H z.1 z.2 ∂(ν.prod ν)
        let G : Ω → ℝ := fun o => (∫ y, H o y ∂ν) - q
        let σ2 : ℝ := ∫ o, G o ^ 2 ∂ν
        let σ : ℝ := Real.sqrt σ2
        let βR : ℝ := ∫ o, Real.rpow |G o / σ| p ∂ν
        let Δp : ℝ :=
          Real.rpow (∫ o, Real.rpow |G o - g o| p ∂ν) (1 / p)
        Measurable G ∧ MemLp G (ENNReal.ofReal p) ν ∧
          Integrable (fun o => Real.rpow |G o - g o| p) ν ∧
          Δp ≤ |u| + c * (Wp / Real.rpow d (1 / p)) + c ^ 2 ∧
          Δp ≤ eps ∧
          (1 / 2 : ℝ) ≤ σ2 ∧ σ2 ≤ (3 / 2 : ℝ) ∧
          |σ2 - 1| ≤ eps ∧ 0 < σ ∧
          MemLp (fun o => G o / σ) (ENNReal.ofReal p) ν ∧
          Integrable (fun o => Real.rpow |G o / σ| p) ν ∧
          |βR - β| ≤ eps ∧ βR ≤ 2 * β := by
  classical
  dsimp only
  let Np : ℕ := Nat.ceil (p / α)
  let Aexpp : ℝ := (Np.factorial : ℝ) / τ ^ Np
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
  let B : ℝ := Real.rpow β (1 / p)
  let Wp : ℝ := Real.rpow (∫ o, Real.rpow |w o| p ∂μ) (1 / p)
  change Integrable (fun o => Real.rpow |g o| p) μ at hgp
  have hsource :=
    Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
      μ h hh hh2 hhsymm hcenter hprojectionsecond
      3 (by norm_num) 0 (by norm_num) (by positivity)
  dsimp only at hsource
  rcases hsource with
    ⟨hgm, hg2, hgmean, hgsecond, hrm, hr2, hrsymm, hrcan, hsourceRest⟩
  clear hsourceRest
  change Measurable g at hgm
  change MemLp g 2 μ at hg2
  change (∫ o, g o ∂μ) = 0 at hgmean
  change (∫ o, g o ^ 2 ∂μ) = 1 at hgsecond
  have hp0 : 0 < p := by linarith only [hp.1]
  have hp1 : 1 < p := by linarith only [hp.1]
  have hpne : p ≠ 0 := hp0.ne'
  have hinvp0 : 0 < 1 / p := div_pos zero_lt_one hp0
  have hinvp1 : 1 / p ≤ 1 := (div_le_one hp0).2 hp1.le
  have hpENN0 : ENNReal.ofReal p ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hp0
  have hpENN1 : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    exact ENNReal.one_le_ofReal.mpr hp1.le
  have hpowMeas : ∀ f : Ω → ℝ, Measurable f →
      Measurable (fun o => Real.rpow |f o| p) := by
    intro f hf
    simpa only [Real.rpow_eq_pow, Real.norm_eq_abs, Function.comp_def] using
      (Real.continuous_rpow_const hp0.le).measurable.comp hf.norm
  have hfactorial : 0 < (Np.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos Np
  have htauNp : 0 < τ ^ Np := pow_pos hτ Np
  have hAexpp : 0 < Aexpp := div_pos hfactorial htauNp
  have halphaNp : p ≤ α * (Np : ℝ) := by
    have hc : p / α ≤ (Np : ℝ) := Nat.le_ceil (p / α)
    have hm := (div_le_iff₀ hα).1 hc
    nlinarith only [hm]
  have hdom : ∀ s : ℝ, 1 ≤ s →
      Real.rpow s p ≤ Aexpp * Real.exp (τ * Real.rpow s α) := by
    intro s hs
    have hs0 : 0 ≤ s := by linarith only [hs]
    have hterm := Real.pow_div_factorial_le_exp
      (τ * Real.rpow s α)
      (mul_nonneg hτ.le (Real.rpow_nonneg hs0 α)) Np
    have hpow : Real.rpow s p ≤ (Real.rpow s α) ^ Np := by
      calc
        Real.rpow s p ≤ Real.rpow s (α * (Np : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hs halphaNp
        _ = (Real.rpow s α) ^ Np := by
          exact (Real.rpow_mul hs0 α (Np : ℝ)).trans
            (Real.rpow_natCast (Real.rpow s α) Np)
    have hterm' : τ ^ Np * (Real.rpow s α) ^ Np ≤
        Real.exp (τ * Real.rpow s α) * (Np.factorial : ℝ) := by
      apply (div_le_iff₀ hfactorial).1
      simpa only [mul_pow] using hterm
    calc
      Real.rpow s p ≤ (Real.rpow s α) ^ Np := hpow
      _ ≤ Real.exp (τ * Real.rpow s α) * (Np.factorial : ℝ) / τ ^ Np := by
        apply (le_div_iff₀ htauNp).2
        simpa only [mul_comm] using hterm'
      _ = Aexpp * Real.exp (τ * Real.rpow s α) := by
        dsimp only [Aexpp]
        ring
  have hWpIntegral : Integrable (fun o => Real.rpow |w o| p) μ := by
    apply (hwexp.const_mul Aexpp).mono' (hpowMeas w hw).aestronglyMeasurable
    filter_upwards [hwone] with o ho
    have hw0 : 0 ≤ w o := by linarith only [ho]
    have hpower0 : 0 ≤ Real.rpow |w o| p := Real.rpow_nonneg (abs_nonneg _) _
    rw [Real.norm_eq_abs, abs_of_nonneg hpower0,
      abs_of_nonneg hw0]
    exact hdom (w o) ho
  have hwp : MemLp w (ENNReal.ofReal p) μ := by
    apply (integrable_norm_rpow_iff hw.aestronglyMeasurable hpENN0
      ENNReal.ofReal_ne_top).1
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le,
      Real.rpow_eq_pow] using hWpIntegral
  have hgpLp : MemLp g (ENNReal.ofReal p) μ := by
    apply (integrable_norm_rpow_iff hgm.aestronglyMeasurable hpENN0
      ENNReal.ofReal_ne_top).1
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le,
      Real.rpow_eq_pow] using hgp
  have hβ0 : 0 ≤ β :=
    integral_nonneg (fun o => Real.rpow_nonneg (abs_nonneg (g o)) p)
  have hB0 : 0 ≤ B := Real.rpow_nonneg hβ0 (1 / p)
  have hWp0 : 0 ≤ Wp := Real.rpow_nonneg
    (integral_nonneg (fun o => Real.rpow_nonneg (abs_nonneg (w o)) p)) _
  have hRootPower : ∀ x : ℝ, 0 ≤ x →
      Real.rpow (Real.rpow x (1 / p)) p = x := by
    intro x hx
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul hx]
    have heq : (1 / p) * p = 1 := by field_simp [hpne]
    rw [heq, Real.rpow_one]
  have hPowerRoot : ∀ x : ℝ, 0 ≤ x →
      Real.rpow (Real.rpow x p) (1 / p) = x := by
    intro x hx
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul hx]
    have heq : p * (1 / p) = 1 := by field_simp [hpne]
    rw [heq, Real.rpow_one]
  have hBeta : 1 ≤ β := by
    have hp20 : 0 < p / 2 := by linarith only [hp.1]
    have hp21 : 1 < p / 2 := by linarith only [hp.1]
    have hp2q : (p / 2).HolderConjugate (p / (p - 2)) := by
      apply (Real.holderConjugate_iff_eq_conjExponent hp21).2
      have hpm2ne : p - 2 ≠ 0 := by linarith only [hp.1]
      have hp2m1ne : p / 2 - 1 ≠ 0 := by linarith only [hp21]
      field_simp [hpm2ne, hp2m1ne] <;> ring
    have hgSqLp : MemLp (fun o => g o ^ 2) (ENNReal.ofReal (p / 2)) μ := by
      apply (integrable_norm_rpow_iff (hgm.pow_const 2).aestronglyMeasurable
        (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp20)
        ENNReal.ofReal_ne_top).1
      have hsame : (fun o => Real.rpow |g o ^ 2| (p / 2)) =
          (fun o => Real.rpow |g o| p) := by
        funext o
        rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
        calc
          Real.rpow (|g o| ^ 2) (p / 2) =
              Real.rpow |g o| ((2 : ℝ) * (p / 2)) := by
            simpa only [Real.rpow_eq_pow, Real.rpow_ofNat] using
              (Real.rpow_mul (abs_nonneg (g o)) (2 : ℝ) (p / 2)).symm
          _ = Real.rpow |g o| p := by congr 1; ring
      have hsquareInt : Integrable (fun o => Real.rpow |g o ^ 2| (p / 2)) μ := by
        rw [hsame]
        exact hgp
      simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp20.le,
        Real.rpow_eq_pow] using hsquareInt
    have honeLp : MemLp (fun _ : Ω => (1 : ℝ))
        (ENNReal.ofReal (p / (p - 2))) μ := by
      apply (integrable_norm_rpow_iff measurable_const.aestronglyMeasurable
        (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp2q.symm.pos)
        ENNReal.ofReal_ne_top).1
      simpa only [norm_one, Real.one_rpow] using
        (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ)
    have hpower : (∫ o, (g o ^ 2) ^ (p / 2) ∂μ) = β := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun o => by
        calc
          (g o ^ 2) ^ (p / 2) = (|g o| ^ 2) ^ (p / 2) := by rw [sq_abs]
          _ = |g o| ^ ((2 : ℝ) * (p / 2)) := by
            simpa only [Real.rpow_eq_pow, Real.rpow_ofNat] using
              (Real.rpow_mul (abs_nonneg (g o)) (2 : ℝ) (p / 2)).symm
          _ = Real.rpow |g o| p := by
            have heq : (2 : ℝ) * (p / 2) = p := by ring
            rw [heq, Real.rpow_eq_pow])
    have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hp2q
      (Filter.Eventually.of_forall (fun o => sq_nonneg (g o)))
      (Filter.Eventually.of_forall (fun _ : Ω => zero_le_one)) hgSqLp honeLp
    have hinv : 1 / (p / 2) = 2 / p := by field_simp [hpne]
    have hholder : 1 ≤ Real.rpow β (2 / p) := by
      simpa only [mul_one, hpower, hgsecond, integral_const, probReal_univ,
        smul_eq_mul, Real.one_rpow, one_mul, hinv, Real.rpow_eq_pow] using hh
    by_contra hβ
    have hlt := Real.rpow_lt_one hβ0 (lt_of_not_ge hβ)
      (div_pos (by norm_num : (0 : ℝ) < 2) hp0)
    exact (not_lt_of_ge hholder) hlt
  have hβpos : 0 < β := lt_of_lt_of_le zero_lt_one hBeta
  have hBpos : 0 < B := Real.rpow_pos_of_pos hβpos _
  have hBpow : Real.rpow B p = β := hRootPower β hβ0
  have hw1 : Integrable w μ := hwp.integrable hpENN1
  have hw0 : ∀ᵐ o ∂μ, 0 ≤ w o :=
    hwone.mono (fun _ ho => by linarith only [ho])
  let W2 : ℝ := Real.sqrt (∫ o, w o ^ 2 ∂μ)
  let Cvar : ℝ := 32 * (1 + B ^ 2 + W2 ^ 2)
  let t : ℝ := 1 - 1 / p
  let e : ℝ := 1 - 2 / p
  let Mpow : ℝ := 2 * (B + 1)
  let Lpow : ℝ := p * Real.rpow Mpow (p - 1)
  let piTail : ℝ → ℝ := fun s => μ.real {o : Ω | s < w o}
  let bTail : ℝ → ℝ := fun s => ∫ o in {o : Ω | s < w o}, w o ∂μ
  let pTail : ℝ → ℝ := fun s => ∫ o in {o : Ω | s < w o}, Real.rpow |g o| p ∂μ
  let errG : ℝ → ℝ := fun s => 2 * B * Real.rpow (piTail s) t + Real.rpow 2 (1 + 1 / p) * Wp * bTail s + 4 * (bTail s) ^ 2
  let errRoot : ℝ → ℝ := fun s => Real.rpow (2 * (β * piTail s + pTail s)) (1 / p)
  let errVar : ℝ → ℝ := fun s => Cvar * (Real.rpow (piTail s) e + bTail s + (bTail s) ^ 2)
  let errStd : ℝ → ℝ := fun s => 2 * (errG s + errRoot s + B * errVar s)
  have ht0 : 0 < t := by
    dsimp only [t]
    have hh : 1 / p < 1 := (div_lt_one hp0).2 hp1
    linarith only [hh]
  have he0 : 0 < e := by
    dsimp only [e]
    have hh : 2 / p < 1 := (div_lt_one hp0).2 hp.1
    linarith only [hh]
  have hCvar0 : 0 ≤ Cvar := by dsimp only [Cvar]; positivity
  have hMpow0 : 0 < Mpow := by dsimp only [Mpow]; linarith only [hB0]
  have hLpow0 : 0 < Lpow :=
    mul_pos hp0 (Real.rpow_pos_of_pos hMpow0 _)
  have hTwoRootCoefficient : Real.rpow (2 : ℝ) (1 + 1 / p) =
      2 * Real.rpow (2 : ℝ) (1 / p) := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using
      (Real.rpow_add (by norm_num : (0 : ℝ) < 2) 1 (1 / p))
  have hRootDifference : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      |Real.rpow x (1 / p) - Real.rpow y (1 / p)| ≤
        Real.rpow |x - y| (1 / p) := by
    have hordered : ∀ x y : ℝ, 0 ≤ y → y ≤ x →
        Real.rpow x (1 / p) - Real.rpow y (1 / p) ≤
          Real.rpow (x - y) (1 / p) := by
      intro x y hy hyx
      have hh := Real.rpow_add_le_add_rpow hy (sub_nonneg.mpr hyx)
        hinvp0.le hinvp1
      have heq : y + (x - y) = x := by ring
      rw [heq] at hh
      simpa only [Real.rpow_eq_pow] using (sub_le_iff_le_add'.2 hh)
    intro x y hx hy
    simp only [Real.rpow_eq_pow] at hordered ⊢
    rcases le_total y x with hyx | hxy
    · rw [abs_of_nonneg (sub_nonneg.mpr
        (Real.rpow_le_rpow hy hyx hinvp0.le)), abs_of_nonneg (sub_nonneg.mpr hyx)]
      exact hordered x y hy hyx
    · rw [abs_sub_comm (x ^ (1 / p)) (y ^ (1 / p)), abs_sub_comm x y,
        abs_of_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow hx hxy hinvp0.le)),
        abs_of_nonneg (sub_nonneg.mpr hxy)]
      exact hordered y x hx hxy
  have hPowerDifference : ∀ x y : ℝ, 0 ≤ x → x ≤ Mpow →
      0 ≤ y → y ≤ Mpow →
      |Real.rpow x p - Real.rpow y p| ≤ Lpow * |x - y| := by
    have hordered : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ Mpow →
        |Real.rpow y p - Real.rpow x p| ≤ Lpow * (y - x) := by
      intro x y hx hxy hy
      have hh := norm_image_sub_le_of_norm_deriv_le_segment'
        (f := fun z : ℝ => Real.rpow z p)
        (f' := fun z : ℝ => p * Real.rpow z (p - 1))
        (a := x) (b := y) (C := Lpow)
        (fun z hz => by
          simpa only [Real.rpow_eq_pow] using
            (Real.hasDerivAt_rpow_const (x := z) (p := p) (Or.inr hp1.le)).hasDerivWithinAt)
        (fun z hz => by
          have hz0 : 0 ≤ z := hx.trans hz.1
          have hzm : z ≤ Mpow := hz.2.le.trans hy
          change |p * z ^ (p - 1)| ≤ Lpow
          rw [abs_of_nonneg (mul_nonneg hp0.le (Real.rpow_nonneg hz0 _))]
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hz0 hzm (by linarith only [hp1])) hp0.le)
        y ⟨hxy, le_rfl⟩
      simpa only [Real.norm_eq_abs] using hh
    intro x y hx hxm hy hym
    rcases le_total x y with hxy | hyx
    · rw [abs_sub_comm (Real.rpow x _) (Real.rpow y _),
        abs_of_nonpos (sub_nonpos.mpr hxy)]
      simpa only [neg_sub] using hordered x y hx hxy hym
    · rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
      exact hordered y x hy hyx hxm
  -- Closed cutoffs have strict complements, including at atoms.
  have hTailNonneg : ∀ s : ℝ,
      0 ≤ piTail s ∧ 0 ≤ bTail s ∧ 0 ≤ pTail s := by
    intro s
    exact ⟨measureReal_nonneg,
      integral_nonneg_of_ae (ae_restrict_of_ae hw0),
      integral_nonneg (fun o => Real.rpow_nonneg (abs_nonneg (g o)) p)⟩
  have hTailMono : ∀ s z : ℝ, s ≤ z →
      piTail z ≤ piTail s ∧ bTail z ≤ bTail s ∧ pTail z ≤ pTail s := by
    intro s z hsz
    have hsets : {o : Ω | z < w o} ⊆ {o : Ω | s < w o} :=
      fun o ho => lt_of_le_of_lt hsz ho
    exact ⟨measureReal_mono hsets,
      setIntegral_mono_set hw1.restrict (ae_restrict_of_ae hw0)
        (Filter.Eventually.of_forall hsets),
      setIntegral_mono_set hgp.restrict
        (Filter.Eventually.of_forall (fun o => Real.rpow_nonneg (abs_nonneg (g o)) p))
        (Filter.Eventually.of_forall hsets)⟩
  have hMaskLimit : ∀ f : Ω → ℝ, Integrable f μ →
      Filter.Tendsto
        (fun k : ℕ => ∫ o, ({o : Ω | (k : ℝ) < w o}).indicator f o ∂μ)
        Filter.atTop (nhds 0) := by
    intro f hf
    have hlim := tendsto_integral_of_dominated_convergence
      (F := fun k : ℕ => ({o : Ω | (k : ℝ) < w o}).indicator f)
      (f := fun _ : Ω => (0 : ℝ))
      (fun o => ‖f o‖)
      (fun k => (hf.indicator (measurableSet_lt measurable_const hw)).aestronglyMeasurable)
      hf.norm
      (fun k => Filter.Eventually.of_forall (fun o => by
        by_cases ho : o ∈ {o : Ω | (k : ℝ) < w o}
        · simpa only [Set.indicator_of_mem ho] using (le_refl ‖f o‖)
        · simpa only [Set.indicator_of_notMem ho, norm_zero] using (norm_nonneg (f o))))
      (Filter.Eventually.of_forall (fun o => by
        have hzero : (fun _ : ℕ => (0 : ℝ)) =ᶠ[Filter.atTop]
            (fun k : ℕ => ({o : Ω | (k : ℝ) < w o}).indicator f o) := by
          filter_upwards
            [(tendsto_natCast_atTop_atTop :
              Filter.Tendsto (fun k : ℕ => (k : ℝ)) Filter.atTop Filter.atTop).eventually
                (Filter.eventually_ge_atTop (w o))] with k hk
          have hnot : o ∉ {o : Ω | (k : ℝ) < w o} := by
            exact not_lt_of_ge hk
          simp only [Set.indicator_of_notMem hnot]
        exact Filter.Tendsto.congr' hzero tendsto_const_nhds))
    simpa only [integral_zero] using hlim
  have hPiLimit : Filter.Tendsto (fun k : ℕ => piTail (k : ℝ))
      Filter.atTop (nhds 0) := by
    have heq : ∀ k : ℕ,
        (∫ o, ({o : Ω | (k : ℝ) < w o}).indicator (fun _ => (1 : ℝ)) o ∂μ) =
          piTail (k : ℝ) := by
      intro k
      rw [integral_indicator (measurableSet_lt measurable_const hw)]
      simp only [integral_const, smul_eq_mul, mul_one, piTail, Measure.real,
        Measure.restrict_apply_univ]
    simpa only [heq] using hMaskLimit (fun _ => (1 : ℝ)) (integrable_const 1)
  have hBtailLimit : Filter.Tendsto (fun k : ℕ => bTail (k : ℝ))
      Filter.atTop (nhds 0) := by
    simpa only [integral_indicator (measurableSet_lt measurable_const hw), bTail]
      using hMaskLimit w hw1
  have hPtailLimit : Filter.Tendsto (fun k : ℕ => pTail (k : ℝ))
      Filter.atTop (nhds 0) := by
    simpa only [integral_indicator (measurableSet_lt measurable_const hw), pTail]
      using hMaskLimit (fun o => Real.rpow |g o| p) hgp
  have hPiPowerLimit : Filter.Tendsto
      (fun k : ℕ => Real.rpow (piTail (k : ℝ)) t) Filter.atTop (nhds 0) := by
    simpa only [Real.rpow_eq_pow, Real.zero_rpow ht0.ne', Function.comp_def] using
      (Real.continuous_rpow_const ht0.le).continuousAt.tendsto.comp hPiLimit
  have hPiPower2Limit : Filter.Tendsto
      (fun k : ℕ => Real.rpow (piTail (k : ℝ)) e) Filter.atTop (nhds 0) := by
    simpa only [Real.rpow_eq_pow, Real.zero_rpow he0.ne', Function.comp_def] using
      (Real.continuous_rpow_const he0.le).continuousAt.tendsto.comp hPiLimit
  have hMassErrorLimit : Filter.Tendsto
      (fun k : ℕ => 2 * (β * piTail (k : ℝ) + pTail (k : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero, zero_add] using
      (hPiLimit.const_mul β |>.add hPtailLimit).const_mul 2
  have hErrGLimit : Filter.Tendsto (fun k : ℕ => errG (k : ℝ))
      Filter.atTop (nhds 0) := by
    simpa only [errG, mul_zero, zero_add, add_zero, zero_pow (by norm_num : 2 ≠ 0)]
      using ((hPiPowerLimit.const_mul (2 * B)).add
        (hBtailLimit.const_mul (Real.rpow 2 (1 + 1 / p) * Wp))).add
          ((hBtailLimit.pow 2).const_mul 4)
  have hErrRootLimit : Filter.Tendsto (fun k : ℕ => errRoot (k : ℝ))
      Filter.atTop (nhds 0) := by
    simpa only [errRoot, Real.rpow_eq_pow, Real.zero_rpow hinvp0.ne', Function.comp_def] using
      (Real.continuous_rpow_const hinvp0.le).continuousAt.tendsto.comp hMassErrorLimit
  have hErrVarLimit : Filter.Tendsto (fun k : ℕ => errVar (k : ℝ))
      Filter.atTop (nhds 0) := by
    simpa only [errVar, mul_zero, zero_add, add_zero, zero_pow (by norm_num : 2 ≠ 0)]
      using ((hPiPower2Limit.add hBtailLimit).add (hBtailLimit.pow 2)).const_mul Cvar
  have hErrStdLimit : Filter.Tendsto (fun k : ℕ => Lpow * errStd (k : ℝ))
      Filter.atTop (nhds 0) := by
    simpa only [errStd, mul_zero, zero_add, add_zero] using
      (((hErrGLimit.add hErrRootLimit).add (hErrVarLimit.const_mul B)).const_mul 2).const_mul Lpow
  have hErrorsMono : ∀ s z : ℝ, s ≤ z →
      errG z ≤ errG s ∧ errRoot z ≤ errRoot s ∧
        errVar z ≤ errVar s ∧ errStd z ≤ errStd s := by
    intro s z hsz
    rcases hTailMono s z hsz with ⟨hpi, hb, hpg⟩
    have hb2 : (bTail z) ^ 2 ≤ (bTail s) ^ 2 := by
      nlinarith only [hb, (hTailNonneg s).2.1, (hTailNonneg z).2.1,
        mul_nonneg (sub_nonneg.mpr hb)
          (add_nonneg (hTailNonneg s).2.1 (hTailNonneg z).2.1)]
    have hG : errG z ≤ errG s := by
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (hTailNonneg z).1 hpi ht0.le) (mul_nonneg (by norm_num) hB0))
          (mul_le_mul_of_nonneg_left hb
            (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hWp0)))
        (mul_le_mul_of_nonneg_left hb2 (by norm_num))
    have hRoot : errRoot z ≤ errRoot s := by
      exact Real.rpow_le_rpow
        (mul_nonneg (by norm_num) (add_nonneg
          (mul_nonneg hβ0 (hTailNonneg z).1) (hTailNonneg z).2.2))
        (mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left hpi hβ0) hpg) (by norm_num)) hinvp0.le
    have hVar : errVar z ≤ errVar s := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add
          (Real.rpow_le_rpow (hTailNonneg z).1 hpi he0.le) hb) hb2) hCvar0
    exact ⟨hG, hRoot, hVar, mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add hG hRoot) (mul_le_mul_of_nonneg_left hVar hB0)) (by norm_num)⟩
  refine ⟨hAexpp, hdom, hWpIntegral, hwp, hgpLp, hBeta, ?_⟩
  intro eps heps
  have hTailSmall : ∃ k : ℕ, 1 ≤ k ∧ piTail (k : ℝ) ≤ (1 / 2 : ℝ) ∧ pTail (k : ℝ) ≤ eps ∧ 2 * (β * piTail (k : ℝ) + pTail (k : ℝ)) ≤ eps ∧ errG (k : ℝ) ≤ eps ∧ errVar (k : ℝ) ≤ min (1 / 2 : ℝ) eps ∧ errG (k : ℝ) + errRoot (k : ℝ) ≤ 1 ∧ Lpow * errStd (k : ℝ) ≤ min eps (β / 2) := by
    have hposVar : 0 < min (1 / 2 : ℝ) eps := lt_min (by norm_num) heps
    have hposMoment : 0 < min eps (β / 2) := lt_min heps (div_pos hβpos (by norm_num))
    have hAll : ∀ᶠ k : ℕ in Filter.atTop,
        1 ≤ k ∧ piTail (k : ℝ) ≤ (1 / 2 : ℝ) ∧ pTail (k : ℝ) ≤ eps ∧
        2 * (β * piTail (k : ℝ) + pTail (k : ℝ)) ≤ eps ∧
        errG (k : ℝ) ≤ eps ∧ errVar (k : ℝ) ≤ min (1 / 2 : ℝ) eps ∧
        errG (k : ℝ) + errRoot (k : ℝ) ≤ 1 ∧
        Lpow * errStd (k : ℝ) ≤ min eps (β / 2) := by
      filter_upwards [Filter.eventually_ge_atTop (1 : ℕ),
        (tendsto_order.1 hPiLimit).2 (1 / 2) (by norm_num),
        (tendsto_order.1 hPtailLimit).2 eps heps,
        (tendsto_order.1 hMassErrorLimit).2 eps heps,
        (tendsto_order.1 hErrGLimit).2 eps heps,
        (tendsto_order.1 hErrVarLimit).2 (min (1 / 2 : ℝ) eps) hposVar,
        (tendsto_order.1 (hErrGLimit.add hErrRootLimit)).2 1 (by norm_num),
        (tendsto_order.1 hErrStdLimit).2 (min eps (β / 2)) hposMoment]
        with k hk hpi hpg hm hG hV hGR hS
      exact ⟨hk, hpi.le, hpg.le, hm.le, hG.le, hV.le, hGR.le, hS.le⟩
    exact hAll.exists
  let N0 : ℕ := Nat.find hTailSmall
  have hN0 : 1 ≤ N0 ∧ piTail (N0 : ℝ) ≤ (1 / 2 : ℝ) ∧ pTail (N0 : ℝ) ≤ eps ∧ 2 * (β * piTail (N0 : ℝ) + pTail (N0 : ℝ)) ≤ eps ∧ errG (N0 : ℝ) ≤ eps ∧ errVar (N0 : ℝ) ≤ min (1 / 2 : ℝ) eps ∧ errG (N0 : ℝ) + errRoot (N0 : ℝ) ≤ 1 ∧ Lpow * errStd (N0 : ℝ) ≤ min eps (β / 2) := Nat.find_spec hTailSmall
  refine ⟨N0, hN0.1, ?_⟩
  intro R hR
  let C : Set Ω := {o : Ω | w o ≤ R}
  let π : ℝ := μ.real Cᶜ
  let d : ℝ := μ.real C
  let ν : Measure Ω := (μ C)⁻¹ • μ.restrict C
  let b : ℝ := ∫ o in Cᶜ, w o ∂μ
  let c : ℝ := b / d
  let u : ℝ := ∫ o, g o ∂ν
  let a : Ω → ℝ := fun o => ∫ y, r o y ∂ν
  let θ : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ∂(ν.prod ν)
  let Tp : ℝ := ∫ o in Cᶜ, Real.rpow |g o| p ∂μ
  let Mp : ℝ := ∫ o, Real.rpow |g o| p ∂ν
  have hC : MeasurableSet C := measurableSet_le hw measurable_const
  have hComp : Cᶜ = {o : Ω | R < w o} := by
    ext o
    simp only [C, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  have hπTail : π = piTail R := by
    dsimp only [π, piTail]
    rw [hComp]
  have hbTail : b = bTail R := by
    dsimp only [b, bTail]
    rw [hComp]
  have hTpTail : Tp = pTail R := by
    dsimp only [Tp, pTail]
    rw [hComp]
  have hπ0 : 0 ≤ π := measureReal_nonneg
  have hb0 : 0 ≤ b := integral_nonneg_of_ae (ae_restrict_of_ae hw0)
  have hTp0 : 0 ≤ Tp := integral_nonneg (fun o => Real.rpow_nonneg (abs_nonneg (g o)) p)
  have hdpi : d = 1 - π := by
    have hc := measureReal_compl (μ := μ) hC
    simp only [probReal_univ] at hc
    change π = 1 - d at hc
    linarith only [hc]
  have hπhalf : π ≤ (1 / 2 : ℝ) := by
    rw [hπTail]
    exact ((hTailMono _ _ hR).1).trans hN0.2.1
  have hdhalf : (1 / 2 : ℝ) ≤ d := by linarith only [hdpi, hπhalf]
  have hd : 0 < d := by linarith only [hdhalf]
  have hdle1 : d ≤ 1 := by linarith only [hdpi, hπ0]
  have hc0 : 0 ≤ c := div_nonneg hb0 hd.le
  have hErrGSmall : errG R ≤ eps :=
    (hErrorsMono _ _ hR).1.trans hN0.2.2.2.2.1
  have hErrVarSmall : errVar R ≤ min (1 / 2 : ℝ) eps :=
    (hErrorsMono _ _ hR).2.2.1.trans hN0.2.2.2.2.2.1
  have hErrNormSmall : errG R + errRoot R ≤ 1 :=
    (add_le_add (hErrorsMono _ _ hR).1 (hErrorsMono _ _ hR).2.1).trans
      hN0.2.2.2.2.2.2.1
  have hErrMomentSmall : Lpow * errStd R ≤ min eps (β / 2) :=
    (mul_le_mul_of_nonneg_left (hErrorsMono _ _ hR).2.2.2 hLpow0.le).trans
      hN0.2.2.2.2.2.2.2
  have hcarrier :=
    Shao.OQ6.ConditionalTrueProjectionCarrier.actual_conditional_true_projection_carrier
      μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone
      α τ hα hτ hwexp henvelope R hd 0 (by norm_num)
  dsimp only at hcarrier
  rcases hcarrier with
    ⟨hOldA, hOldDom, hOldC, hOlddpi, hOldd, hOldpi, hOldpilt,
      hνprob, hνac, hνprodac, hνC, hνmass, hνint,
      hw2, hwν2, hwνSecond, ham, ha2, haν2, hrows,
      hθmean, hθtail, hθbound, hOldRest⟩
  clear hOldA hOldDom hOldC hOlddpi hOldd hOldpi hOldpilt
    hνprodac hνmass hw2 hwν2 hwνSecond ha2 haν2 hθmean hθtail hOldRest
  change IsProbabilityMeasure ν at hνprob
  change ν ≪ μ at hνac
  change ν C = 1 at hνC
  change (∀ f : Ω → ℝ, Integrable f μ →
    Integrable f ν ∧ (∫ o, f o ∂ν) = (∫ o in C, f o ∂μ) / d) at hνint
  change Measurable a at ham
  change (∀ᵐ o ∂μ, Integrable (r o) μ ∧ Integrable (r o) ν ∧
    a o = -(∫ y in Cᶜ, r o y ∂μ) / d ∧ |a o| ≤ c * w o) at hrows
  change |θ| ≤ b ^ 2 / d ^ 2 at hθbound
  haveI : IsProbabilityMeasure ν := hνprob
  have hθc : |θ| ≤ c ^ 2 := by simpa only [c, div_pow] using hθbound
  have hwpνInt : Integrable (fun o => Real.rpow |w o| p) ν :=
    (hνint _ hWpIntegral).1
  have hgpνInt : Integrable (fun o => Real.rpow |g o| p) ν := (hνint _ hgp).1
  have hwpν : MemLp w (ENNReal.ofReal p) ν := by
    apply (integrable_norm_rpow_iff hw.aestronglyMeasurable hpENN0
      ENNReal.ofReal_ne_top).1
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le,
      Real.rpow_eq_pow] using hwpνInt
  have hgpν : MemLp g (ENNReal.ofReal p) ν := by
    apply (integrable_norm_rpow_iff hgm.aestronglyMeasurable hpENN0
      ENNReal.ofReal_ne_top).1
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le,
      Real.rpow_eq_pow] using hgpνInt
  have haPoint : ∀ᵐ o ∂ν, |a o| ≤ c * w o :=
    Filter.Eventually.mono (hνac.ae_le hrows) (fun _ ho => ho.2.2.2)
  have haIntegral : Integrable (fun o => Real.rpow |a o| p) ν := by
    apply (hwpνInt.const_mul (Real.rpow c p)).mono' (hpowMeas a ham).aestronglyMeasurable
    filter_upwards [haPoint, hνac.ae_le hw0] with o ho hw0o
    have hpower0 : 0 ≤ Real.rpow |a o| p := Real.rpow_nonneg (abs_nonneg _) _
    rw [Real.norm_eq_abs, abs_of_nonneg hpower0]
    calc
      Real.rpow |a o| p ≤ Real.rpow (c * w o) p :=
        Real.rpow_le_rpow (abs_nonneg _) ho hp0.le
      _ = Real.rpow c p * Real.rpow |w o| p := by
        rw [abs_of_nonneg hw0o]
        simpa only [Real.rpow_eq_pow] using Real.mul_rpow hc0 hw0o
  have hapν : MemLp a (ENNReal.ofReal p) ν := by
    apply (integrable_norm_rpow_iff ham.aestronglyMeasurable hpENN0
      ENNReal.ofReal_ne_top).1
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le,
      Real.rpow_eq_pow] using haIntegral
  have hLpNormIntegral : ∀ f : Ω → ℝ, AEStronglyMeasurable f ν →
      lpNorm f (ENNReal.ofReal p) ν =
        Real.rpow (∫ o, Real.rpow |f o| p ∂ν) (1 / p) := by
    intro f hf
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le,
      Real.rpow_eq_pow, one_div] using
      lpNorm_eq_integral_norm_rpow_toReal hpENN0 ENNReal.ofReal_ne_top hf
  have hNormAE : ∀ f k : Ω → ℝ, AEStronglyMeasurable f ν →
      AEStronglyMeasurable k ν → f =ᵐ[ν] k →
        lpNorm f (ENNReal.ofReal p) ν = lpNorm k (ENNReal.ofReal p) ν := by
    intro f k hf hk hfk
    rw [hLpNormIntegral f hf, hLpNormIntegral k hk]
    congr 1
    apply integral_congr_ae
    filter_upwards [hfk] with o ho
    change Real.rpow |f o| p = Real.rpow |k o| p
    rw [ho]
  have hConstLp : ∀ v : ℝ, MemLp (fun _ : Ω => v) (ENNReal.ofReal p) ν := by
    intro v
    apply (integrable_norm_rpow_iff measurable_const.aestronglyMeasurable
      hpENN0 ENNReal.ofReal_ne_top).1
    exact integrable_const _
  have hNormConst : ∀ v : ℝ,
      lpNorm (fun _ : Ω => v) (ENNReal.ofReal p) ν = |v| := by
    intro v
    simpa only [Real.norm_eq_abs, probReal_univ, Real.one_rpow, mul_one] using
      lpNorm_const' (μ := ν) hpENN0 ENNReal.ofReal_ne_top v
  have hNormScale : ∀ v : ℝ, ∀ f : Ω → ℝ,
      lpNorm (fun o => v * f o) (ENNReal.ofReal p) ν =
        |v| * lpNorm f (ENNReal.ofReal p) ν := by
    intro v f
    have hh := lpNorm_const_smul (p := ENNReal.ofReal p) v f ν
    change lpNorm (fun o => v * f o) (ENNReal.ofReal p) ν =
      ‖v‖ * lpNorm f (ENNReal.ofReal p) ν at hh
    simpa only [Real.norm_eq_abs] using hh
  have hwNormBound : lpNorm w (ENNReal.ofReal p) ν ≤ Wp / Real.rpow d (1 / p) := by
    rw [hLpNormIntegral w hw.aestronglyMeasurable]
    have hint : (∫ o, Real.rpow |w o| p ∂ν) ≤
        (∫ o, Real.rpow |w o| p ∂μ) / d := by
      rw [(hνint _ hWpIntegral).2]
      exact div_le_div_of_nonneg_right
        (setIntegral_le_integral hWpIntegral
          (Filter.Eventually.of_forall (fun o => Real.rpow_nonneg (abs_nonneg (w o)) p))) hd.le
    calc
      Real.rpow (∫ o, Real.rpow |w o| p ∂ν) (1 / p) ≤
          Real.rpow ((∫ o, Real.rpow |w o| p ∂μ) / d) (1 / p) :=
        Real.rpow_le_rpow
          (integral_nonneg (fun o => Real.rpow_nonneg (abs_nonneg (w o)) p)) hint hinvp0.le
      _ = Wp / Real.rpow d (1 / p) := by
        simpa only [Wp, Real.rpow_eq_pow] using
          Real.div_rpow
            (integral_nonneg (fun o => Real.rpow_nonneg (abs_nonneg (w o)) p)) hd.le (1 / p)
  have haNormBound : lpNorm a (ENNReal.ofReal p) ν ≤
      c * lpNorm w (ENNReal.ofReal p) ν := by
    rw [hLpNormIntegral a ham.aestronglyMeasurable,
      hLpNormIntegral w hw.aestronglyMeasurable]
    have hint : (∫ o, Real.rpow |a o| p ∂ν) ≤
        Real.rpow c p * (∫ o, Real.rpow |w o| p ∂ν) := by
      calc
        _ ≤ ∫ o, Real.rpow c p * Real.rpow |w o| p ∂ν := by
          apply integral_mono_ae haIntegral (hwpνInt.const_mul _)
          filter_upwards [haPoint, hνac.ae_le hw0] with o ho hw0o
          calc
            Real.rpow |a o| p ≤ Real.rpow (c * w o) p :=
              Real.rpow_le_rpow (abs_nonneg _) ho hp0.le
            _ = Real.rpow c p * Real.rpow |w o| p := by
              rw [abs_of_nonneg hw0o]
              simpa only [Real.rpow_eq_pow] using Real.mul_rpow hc0 hw0o
        _ = _ := integral_const_mul _ _
    calc
      Real.rpow (∫ o, Real.rpow |a o| p ∂ν) (1 / p) ≤
          Real.rpow (Real.rpow c p * (∫ o, Real.rpow |w o| p ∂ν)) (1 / p) :=
        Real.rpow_le_rpow
          (integral_nonneg (fun o => Real.rpow_nonneg (abs_nonneg (a o)) p)) hint hinvp0.le
      _ = Real.rpow (Real.rpow c p) (1 / p) *
          Real.rpow (∫ o, Real.rpow |w o| p ∂ν) (1 / p) := by
        simpa only [Real.rpow_eq_pow] using
          Real.mul_rpow (Real.rpow_nonneg hc0 p)
            (integral_nonneg (fun o => Real.rpow_nonneg (abs_nonneg (w o)) p))
      _ = c * Real.rpow (∫ o, Real.rpow |w o| p ∂ν) (1 / p) := by rw [hPowerRoot c hc0]
  have hMpIdentity : Mp = (β - Tp) / d := by
    have hsplit := integral_add_compl hC hgp
    change (∫ o in C, Real.rpow |g o| p ∂μ) + Tp = β at hsplit
    change (∫ o, Real.rpow |g o| p ∂ν) = _
    rw [(hνint _ hgp).2]
    congr 1
    linarith only [hsplit]
  have hTpSmall : Tp ≤ eps := by
    rw [hTpTail]
    exact (hTailMono _ _ hR).2.2.trans hN0.2.2.1
  have hMassErrorSmall : 2 * (β * π + Tp) ≤ eps := by
    rw [hπTail, hTpTail]
    exact (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left (hTailMono _ _ hR).1 hβ0)
        (hTailMono _ _ hR).2.2) (by norm_num)).trans hN0.2.2.2.1
  have hMpError : |Mp - β| ≤ 2 * (β * π + Tp) := by
    have hEq : Mp - β = (β * π - Tp) / d := by
      apply (eq_div_iff hd.ne').2
      have hm := (eq_div_iff hd.ne').1 hMpIdentity
      calc
        (Mp - β) * d = Mp * d - β * d := by ring
        _ = (β - Tp) - β * d := by rw [hm]
        _ = β * π - Tp := by rw [hdpi]; ring
    have hinvd : 1 / d ≤ 2 := (div_le_iff₀ hd).2 (by linarith only [hdhalf])
    rw [hEq, abs_div, abs_of_pos hd]
    calc
      |β * π - Tp| / d ≤ (β * π + Tp) / d := by
        apply div_le_div_of_nonneg_right _ hd.le
        simpa only [abs_of_nonneg (mul_nonneg hβ0 hπ0), abs_of_nonneg hTp0]
          using abs_sub (β * π) Tp
      _ = (β * π + Tp) * (1 / d) := by ring
      _ ≤ (β * π + Tp) * 2 := mul_le_mul_of_nonneg_left hinvd
        (add_nonneg (mul_nonneg hβ0 hπ0) hTp0)
      _ = 2 * (β * π + Tp) := by ring
  have hMp0 : 0 ≤ Mp := integral_nonneg (fun o => Real.rpow_nonneg (abs_nonneg (g o)) p)
  have hgRootError : |lpNorm g (ENNReal.ofReal p) ν - B| ≤ errRoot R := by
    rw [hLpNormIntegral g hgm.aestronglyMeasurable]
    change |Real.rpow Mp (1 / p) - Real.rpow β (1 / p)| ≤ errRoot R
    calc
      _ ≤ Real.rpow |Mp - β| (1 / p) := hRootDifference Mp β hMp0 hβ0
      _ ≤ Real.rpow (2 * (β * π + Tp)) (1 / p) :=
        Real.rpow_le_rpow (abs_nonneg _) hMpError hinvp0.le
      _ = errRoot R := by simp only [errRoot, ← hπTail, ← hTpTail]
  refine ⟨hdhalf, hdpi, hνprob, hνac, hνC, hwpν, hgpν, hapν, hgpνInt,
    hMpIdentity, hTp0, hTpSmall, hMpError.trans hMassErrorSmall, ?_⟩
  intro lam hLam
  let H : Ω → Ω → ℝ := fun o y => g o + g y + lam * r o y
  let q : ℝ := ∫ z : Ω × Ω, H z.1 z.2 ∂(ν.prod ν)
  let G : Ω → ℝ := fun o => (∫ y, H o y ∂ν) - q
  let σ2 : ℝ := ∫ o, G o ^ 2 ∂ν
  let σ : ℝ := Real.sqrt σ2
  let βR : ℝ := ∫ o, Real.rpow |G o / σ| p ∂ν
  let Δp : ℝ := Real.rpow (∫ o, Real.rpow |G o - g o| p ∂ν) (1 / p)
  have hfinite :=
    Shao.OQ6.ConditionalVarianceMean.actual_conditional_variance_mean
      μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone
      α τ hα hτ hwexp henvelope p hp hgp
  dsimp only at hfinite
  rcases hfinite with ⟨hfβ, hfB, hfW, hfCvar, hfCmean, hfinite⟩
  specialize hfinite R hdhalf lam hLam
  rcases hfinite with
    ⟨hfC, hfdpi, hfd, hfpi, hfpilt, hfb, hfνprob, hfνac, hfνprodac,
      hfgm, hfg2, hfgν2, hfgmean, hfgsecond, hfw2, hfwν2, hfwνsecond,
      hfam, hfaν2, hfrows, hfθmean, hfθsecond, hfθbound,
      hfHm, hfH2, hfq, hGm, hG2, hGrows, hfGmean,
      hfga, hfF2, hfσInt, hfσ0, huBound, hfTail2, hfgνerror, hfgνsecond,
      hfu2, hfa2, hfgaBound, hfσIdentity, hF2Consumed, hfMean⟩
  clear hfβ hfB hfW hfCvar hfCmean hfC hfdpi hfd hfpi hfpilt hfb
    hfνprob hfνac hfνprodac hfgm hfg2 hfgν2 hfgmean hfgsecond
    hfw2 hfwν2 hfwνsecond hfam hfaν2 hfrows hfθmean hfθsecond hfθbound
    hfHm hfH2 hfq hfGmean hfga hfF2 hfσInt hfσ0 hfTail2 hfgνerror hfgνsecond
    hfu2 hfa2 hfgaBound hfσIdentity hfMean
  change Measurable G at hGm
  change MemLp G 2 ν at hG2
  change (∀ᵐ o ∂μ, Integrable (H o) ν ∧
    G o = g o - u + lam * (a o - θ)) at hGrows
  change |u| ≤ B * Real.rpow π t / d at huBound
  change |σ2 - 1| ≤ Cvar * (Real.rpow π e + b + b ^ 2) at hF2Consumed
  have hGagree : G =ᵐ[ν] (fun o => g o - u + lam * (a o - θ)) :=
    Filter.Eventually.mono (hνac.ae_le hGrows) (fun _ ho => ho.2)
  have hGp : MemLp G (ENNReal.ofReal p) ν := by
    apply (memLp_congr_ae hGagree).2
    exact (hgpν.sub (hConstLp u)).add
      ((hapν.sub (hConstLp θ)).const_mul lam)
  have hDiffp : MemLp (fun o => G o - g o) (ENNReal.ofReal p) ν := hGp.sub hgpν
  have hDiffInt : Integrable (fun o => Real.rpow |G o - g o| p) ν := by
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le,
      Real.rpow_eq_pow] using hDiffp.integrable_norm_rpow hpENN0 ENNReal.ofReal_ne_top
  have hDiffNorm : Δp = lpNorm (fun o => -u + lam * (a o - θ)) (ENNReal.ofReal p) ν := by
    change Real.rpow (∫ o, Real.rpow |G o - g o| p ∂ν) (1 / p) = _
    rw [← hLpNormIntegral _ hDiffp.aestronglyMeasurable]
    apply hNormAE _ _ hDiffp.aestronglyMeasurable
      (measurable_const.add ((ham.sub measurable_const).const_mul lam)).aestronglyMeasurable
    filter_upwards [hGagree] with o ho
    change G o - g o = -u + lam * (a o - θ)
    rw [ho]
    ring
  have hDeltaFinite : Δp ≤ |u| + c * (Wp / Real.rpow d (1 / p)) + c ^ 2 := by
    have hsub : lpNorm (fun o => a o - θ) (ENNReal.ofReal p) ν ≤
        lpNorm a (ENNReal.ofReal p) ν + |θ| := by
      have hh := lpNorm_sub_le (g := fun _ : Ω => θ) hapν hpENN1
      change lpNorm (fun o => a o - θ) (ENNReal.ofReal p) ν ≤
        lpNorm a (ENNReal.ofReal p) ν + lpNorm (fun _ : Ω => θ) (ENNReal.ofReal p) ν at hh
      rw [hNormConst θ] at hh
      exact hh
    have hlamabs : |lam| ≤ 1 := by rw [abs_of_nonneg hLam.1]; exact hLam.2
    have hadd : lpNorm (fun o => -u + lam * (a o - θ)) (ENNReal.ofReal p) ν ≤
        |u| + |lam| * lpNorm (fun o => a o - θ) (ENNReal.ofReal p) ν := by
      have hh := lpNorm_add_le (g := fun o => lam * (a o - θ)) (hConstLp (-u)) hpENN1
      change lpNorm (fun o => -u + lam * (a o - θ)) (ENNReal.ofReal p) ν ≤
        lpNorm (fun _ : Ω => -u) (ENNReal.ofReal p) ν +
          lpNorm (fun o => lam * (a o - θ)) (ENNReal.ofReal p) ν at hh
      rw [hNormConst (-u), abs_neg, hNormScale lam] at hh
      exact hh
    have hlamSub : |lam| * lpNorm (fun o => a o - θ) (ENNReal.ofReal p) ν ≤
        lpNorm a (ENNReal.ofReal p) ν + |θ| := by
      calc
        _ ≤ |lam| * (lpNorm a (ENNReal.ofReal p) ν + |θ|) :=
          mul_le_mul_of_nonneg_left hsub (abs_nonneg _)
        _ ≤ 1 * (lpNorm a (ENNReal.ofReal p) ν + |θ|) :=
          mul_le_mul_of_nonneg_right hlamabs (add_nonneg lpNorm_nonneg (abs_nonneg θ))
        _ = _ := one_mul _
    rw [hDiffNorm]
    calc
      _ ≤ |u| + |lam| * lpNorm (fun o => a o - θ) (ENNReal.ofReal p) ν := hadd
      _ ≤ |u| + (lpNorm a (ENNReal.ofReal p) ν + |θ|) := by
        exact add_le_add (le_refl _) hlamSub
      _ ≤ |u| + (c * (Wp / Real.rpow d (1 / p)) + c ^ 2) := by
        exact add_le_add (le_refl _) (add_le_add
          (haNormBound.trans (mul_le_mul_of_nonneg_left hwNormBound hc0)) hθc)
      _ = _ := by ring
  have hinvd : 1 / d ≤ 2 :=
    (div_le_iff₀ hd).2 (by linarith only [hdhalf])
  have hcTwo : c ≤ 2 * b := by
    change b / d ≤ 2 * b
    calc
      b / d = b * (1 / d) := by ring
      _ ≤ b * 2 := mul_le_mul_of_nonneg_left hinvd hb0
      _ = 2 * b := by ring
  have hcSquare : c ^ 2 ≤ 4 * b ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hcTwo)
      (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb0) hc0)
    nlinarith only [hprod]
  have huTwo : |u| ≤ 2 * B * Real.rpow π t := by
    calc
      |u| ≤ B * Real.rpow π t / d := huBound
      _ = (B * Real.rpow π t) * (1 / d) := by ring
      _ ≤ (B * Real.rpow π t) * 2 :=
        mul_le_mul_of_nonneg_left hinvd (mul_nonneg hB0 (Real.rpow_nonneg hπ0 t))
      _ = 2 * B * Real.rpow π t := by ring
  have hRootInverse : 1 / Real.rpow d (1 / p) ≤ Real.rpow (2 : ℝ) (1 / p) := by
    have hh := Real.rpow_le_rpow (div_nonneg zero_le_one hd.le) hinvd hinvp0.le
    change Real.rpow (1 / d) (1 / p) ≤ Real.rpow (2 : ℝ) (1 / p) at hh
    have heq : Real.rpow (1 / d) (1 / p) = 1 / Real.rpow d (1 / p) := by
      simpa only [Real.rpow_eq_pow, Real.one_rpow] using
        Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) hd.le (1 / p)
    rw [heq] at hh
    exact hh
  have hWpScale : Wp / Real.rpow d (1 / p) ≤ Wp * Real.rpow (2 : ℝ) (1 / p) := by
    calc
      Wp / Real.rpow d (1 / p) = Wp * (1 / Real.rpow d (1 / p)) := by ring
      _ ≤ Wp * Real.rpow (2 : ℝ) (1 / p) :=
        mul_le_mul_of_nonneg_left hRootInverse hWp0
  have hCwScale : c * (Wp / Real.rpow d (1 / p)) ≤
      Real.rpow (2 : ℝ) (1 + 1 / p) * Wp * b := by
    calc
      c * (Wp / Real.rpow d (1 / p)) ≤
          (2 * b) * (Wp * Real.rpow (2 : ℝ) (1 / p)) :=
        mul_le_mul hcTwo hWpScale
          (div_nonneg hWp0 (Real.rpow_nonneg hd.le _))
          (mul_nonneg (by norm_num) hb0)
      _ = Real.rpow (2 : ℝ) (1 + 1 / p) * Wp * b := by
        rw [hTwoRootCoefficient]
        ring
  have hDeltaError : Δp ≤ errG R := by
    calc
      Δp ≤ |u| + c * (Wp / Real.rpow d (1 / p)) + c ^ 2 := hDeltaFinite
      _ ≤ 2 * B * Real.rpow π t +
          Real.rpow (2 : ℝ) (1 + 1 / p) * Wp * b + 4 * b ^ 2 :=
        add_le_add (add_le_add huTwo hCwScale) hcSquare
      _ = errG R := by simp only [errG, ← hπTail, ← hbTail]
  have hDeltaSmall : Δp ≤ eps := hDeltaError.trans hErrGSmall
  have hVariance : |σ2 - 1| ≤ errVar R := by
    simpa only [errVar, ← hπTail, ← hbTail] using hF2Consumed
  have hVarianceHalf : |σ2 - 1| ≤ (1 / 2 : ℝ) :=
    hVariance.trans (hErrVarSmall.trans (min_le_left _ _))
  have hVarianceSmall : |σ2 - 1| ≤ eps :=
    hVariance.trans (hErrVarSmall.trans (min_le_right _ _))
  have hσ2Lower : (1 / 2 : ℝ) ≤ σ2 := by
    have hh := (abs_le.1 hVarianceHalf).1
    linarith only [hh]
  have hσ2Upper : σ2 ≤ (3 / 2 : ℝ) := by
    have hh := (abs_le.1 hVarianceHalf).2
    linarith only [hh]
  have hσ2Positive : 0 < σ2 := by linarith only [hσ2Lower]
  have hσPositive : 0 < σ := Real.sqrt_pos.2 hσ2Positive
  have hσNonneg : 0 ≤ σ := hσPositive.le
  have hσSquare : σ ^ 2 = σ2 := Real.sq_sqrt hσ2Positive.le
  have hσHalf : (1 / 2 : ℝ) ≤ σ := by
    by_contra hh
    have hσlt : σ < (1 / 2 : ℝ) := lt_of_not_ge hh
    have hprod := mul_nonneg (sub_nonneg.mpr hσlt.le)
      (add_nonneg hσNonneg (by norm_num : (0 : ℝ) ≤ 1 / 2))
    nlinarith only [hprod, hσSquare, hσ2Lower]
  have hσInverse : 1 / σ ≤ 2 :=
    (div_le_iff₀ hσPositive).2 (by linarith only [hσHalf])
  have hσError : |σ - 1| ≤ errVar R := by
    have hfactor : |σ2 - 1| = |σ - 1| * (σ + 1) := by
      have heq : σ2 - 1 = (σ - 1) * (σ + 1) := by
        nlinarith only [hσSquare]
      rw [heq, abs_mul,
        abs_of_nonneg (show 0 ≤ σ + 1 by linarith only [hσNonneg])]
    calc
      |σ - 1| ≤ |σ - 1| * (σ + 1) := by
        nlinarith only [mul_nonneg (abs_nonneg (σ - 1)) hσNonneg]
      _ = |σ2 - 1| := hfactor.symm
      _ ≤ errVar R := hVariance
  have hσInverseError : |1 / σ - 1| ≤ 2 * errVar R := by
    have heq : 1 / σ - 1 = (1 - σ) / σ := by field_simp [hσPositive.ne']
    rw [heq, abs_div, abs_of_pos hσPositive, abs_sub_comm 1 σ]
    calc
      |σ - 1| / σ = |σ - 1| * (1 / σ) := by ring
      _ ≤ |σ - 1| * 2 := mul_le_mul_of_nonneg_left hσInverse (abs_nonneg _)
      _ ≤ errVar R * 2 := mul_le_mul_of_nonneg_right hσError (by norm_num)
      _ = 2 * errVar R := by ring
  have hDeltaNorm : lpNorm (fun o => G o - g o) (ENNReal.ofReal p) ν = Δp :=
    hLpNormIntegral _ hDiffp.aestronglyMeasurable
  have hNormReverse : |lpNorm G (ENNReal.ofReal p) ν - lpNorm g (ENNReal.ofReal p) ν| ≤ Δp := by
    have hforward := lpNorm_le_lpNorm_add_lpNorm_sub'
      (f := G) hgpν hpENN1
    have hbackward := lpNorm_le_lpNorm_add_lpNorm_sub'
      (f := g) hGp hpENN1
    have hcomm : lpNorm (g - G) (ENNReal.ofReal p) ν =
        lpNorm (G - g) (ENNReal.ofReal p) ν := lpNorm_sub_comm g G _ ν
    rw [hcomm] at hbackward
    change lpNorm G (ENNReal.ofReal p) ν ≤
      lpNorm g (ENNReal.ofReal p) ν + lpNorm (fun o => G o - g o) (ENNReal.ofReal p) ν at hforward
    change lpNorm g (ENNReal.ofReal p) ν ≤
      lpNorm G (ENNReal.ofReal p) ν + lpNorm (fun o => G o - g o) (ENNReal.ofReal p) ν at hbackward
    rw [hDeltaNorm] at hforward hbackward
    exact abs_le.2 ⟨by linarith only [hbackward], by linarith only [hforward]⟩
  have hGNormError : |lpNorm G (ENNReal.ofReal p) ν - B| ≤ errG R + errRoot R := by
    calc
      |lpNorm G (ENNReal.ofReal p) ν - B| ≤
          |lpNorm G (ENNReal.ofReal p) ν - lpNorm g (ENNReal.ofReal p) ν| +
            |lpNorm g (ENNReal.ofReal p) ν - B| := abs_sub_le _ _ _
      _ ≤ Δp + errRoot R := add_le_add hNormReverse hgRootError
      _ ≤ errG R + errRoot R := add_le_add hDeltaError (le_refl _)
  have hGNormBound : lpNorm G (ENNReal.ofReal p) ν ≤ B + 1 := by
    have hh := (abs_le.1 (hGNormError.trans hErrNormSmall)).2
    linarith only [hh]
  have hStandardizedLp : MemLp (fun o => G o / σ) (ENNReal.ofReal p) ν := by
    have hh := hGp.const_mul (1 / σ)
    have heq : (fun o => (1 / σ) * G o) = (fun o => G o / σ) := by
      funext o
      ring
    rw [heq] at hh
    exact hh
  have hStandardizedIntegral : Integrable (fun o => Real.rpow |G o / σ| p) ν := by
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le, Real.rpow_eq_pow] using
      hStandardizedLp.integrable_norm_rpow hpENN0 ENNReal.ofReal_ne_top
  have hStandardizedNorm : lpNorm (fun o => G o / σ) (ENNReal.ofReal p) ν =
      lpNorm G (ENNReal.ofReal p) ν / σ := by
    have heq : (fun o => G o / σ) = (fun o => (1 / σ) * G o) := by
      funext o
      ring
    rw [heq, hNormScale (1 / σ) G,
      abs_of_pos (div_pos zero_lt_one hσPositive)]
    ring
  have hStandardizedBound : lpNorm (fun o => G o / σ) (ENNReal.ofReal p) ν ≤ Mpow := by
    rw [hStandardizedNorm]
    calc
      lpNorm G (ENNReal.ofReal p) ν / σ =
          lpNorm G (ENNReal.ofReal p) ν * (1 / σ) := by ring
      _ ≤ (B + 1) * 2 :=
        mul_le_mul hGNormBound hσInverse (div_nonneg zero_le_one hσNonneg)
          (by linarith only [hB0])
      _ = Mpow := by dsimp only [Mpow]; ring
  have hStandardizedError : |lpNorm (fun o => G o / σ) (ENNReal.ofReal p) ν - B| ≤ errStd R := by
    rw [hStandardizedNorm]
    have heq : lpNorm G (ENNReal.ofReal p) ν / σ - B =
        (lpNorm G (ENNReal.ofReal p) ν - B) / σ + B * (1 / σ - 1) := by ring
    rw [heq]
    calc
      _ ≤ |(lpNorm G (ENNReal.ofReal p) ν - B) / σ| + |B * (1 / σ - 1)| := abs_add_le _ _
      _ = |lpNorm G (ENNReal.ofReal p) ν - B| * (1 / σ) + B * |1 / σ - 1| := by
        rw [abs_div, abs_of_pos hσPositive, abs_mul, abs_of_nonneg hB0]
        ring
      _ ≤ |lpNorm G (ENNReal.ofReal p) ν - B| * 2 + B * (2 * errVar R) :=
        add_le_add (mul_le_mul_of_nonneg_left hσInverse (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hσInverseError hB0)
      _ ≤ (errG R + errRoot R) * 2 + B * (2 * errVar R) :=
        add_le_add (mul_le_mul_of_nonneg_right hGNormError (by norm_num)) (le_refl _)
      _ = errStd R := by dsimp only [errStd]; ring
  have hβRNonneg : 0 ≤ βR :=
    integral_nonneg (fun o => Real.rpow_nonneg (abs_nonneg (G o / σ)) p)
  have hStandardizedPower : Real.rpow
      (lpNorm (fun o => G o / σ) (ENNReal.ofReal p) ν) p = βR := by
    rw [hLpNormIntegral _ hStandardizedLp.aestronglyMeasurable]
    exact hRootPower βR hβRNonneg
  have hBFixedBound : B ≤ Mpow := by dsimp only [Mpow]; linarith only [hB0]
  have hMomentError : |βR - β| ≤ Lpow * errStd R := by
    calc
      |βR - β| = |Real.rpow (lpNorm (fun o => G o / σ) (ENNReal.ofReal p) ν) p -
          Real.rpow B p| := by rw [hStandardizedPower, hBpow]
      _ ≤ Lpow * |lpNorm (fun o => G o / σ) (ENNReal.ofReal p) ν - B| :=
        hPowerDifference _ _ lpNorm_nonneg hStandardizedBound hB0 hBFixedBound
      _ ≤ Lpow * errStd R := mul_le_mul_of_nonneg_left hStandardizedError hLpow0.le
  have hMomentSmall : |βR - β| ≤ eps :=
    hMomentError.trans (hErrMomentSmall.trans (min_le_left _ _))
  have hMomentHalf : |βR - β| ≤ β / 2 :=
    hMomentError.trans (hErrMomentSmall.trans (min_le_right _ _))
  have hMomentBound : βR ≤ 2 * β := by
    have hh := (abs_le.1 hMomentHalf).2
    linarith only [hh, hβ0]
  exact ⟨hGm, hGp, hDiffInt, hDeltaFinite, hDeltaSmall,
    hσ2Lower, hσ2Upper, hVarianceSmall, hσPositive,
    hStandardizedLp, hStandardizedIntegral, hMomentSmall, hMomentBound⟩

end

end Shao.OQ6.ConditionalStandardizedPMoment
