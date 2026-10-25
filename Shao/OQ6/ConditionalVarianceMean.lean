import Shao.OQ6.ConditionalTrueProjectionCarrier
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Shao.OQ6.ConditionalVarianceMean

noncomputable section

open MeasureTheory ProbabilityTheory

theorem actual_conditional_variance_mean
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
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
    let B : ℝ := Real.rpow β (1 / p)
    let W2 : ℝ := Real.sqrt (∫ o, w o ^ 2 ∂μ)
    let Cvar : ℝ := 32 * (1 + B ^ 2 + W2 ^ 2)
    let Cmean : ℝ := 4 * (1 + B)
    0 ≤ β ∧ 0 ≤ B ∧ 0 ≤ W2 ∧ 0 < Cvar ∧ 0 < Cmean ∧
      ∀ R : ℝ, (1 / 2 : ℝ) ≤ μ.real {o : Ω | w o ≤ R} →
      ∀ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 →
      let C : Set Ω := {o : Ω | w o ≤ R}
      let π : ℝ := μ.real Cᶜ
      let d : ℝ := μ.real C
      let ν : Measure Ω := (μ C)⁻¹ • μ.restrict C
      let b : ℝ := ∫ o in Cᶜ, w o ∂μ
      let c : ℝ := b / d
      let u : ℝ := ∫ o, g o ∂ν
      let a : Ω → ℝ := fun o => ∫ y, r o y ∂ν
      let θ : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ∂(ν.prod ν)
      let H : Ω → Ω → ℝ := fun o y => g o + g y + lam * r o y
      let q : ℝ := ∫ z : Ω × Ω, H z.1 z.2 ∂(ν.prod ν)
      let G : Ω → ℝ := fun o => (∫ y, H o y ∂ν) - q
      let σ2 : ℝ := ∫ o, G o ^ 2 ∂ν
      MeasurableSet C ∧ d = 1 - π ∧ 0 < d ∧ 0 ≤ π ∧ π < 1 ∧ 0 ≤ b ∧
        IsProbabilityMeasure ν ∧ ν ≪ μ ∧ (ν.prod ν) ≪ (μ.prod μ) ∧
        Measurable g ∧ MemLp g 2 μ ∧ MemLp g 2 ν ∧
        (∫ o, g o ∂μ) = 0 ∧ (∫ o, g o ^ 2 ∂μ) = 1 ∧
        MemLp w 2 μ ∧ MemLp w 2 ν ∧
        (∫ o, w o ^ 2 ∂ν) ≤ W2 ^ 2 / d ∧
        Measurable a ∧ MemLp a 2 ν ∧
        (∀ᵐ o ∂μ, Integrable (r o) μ ∧ Integrable (r o) ν ∧
          a o = -(∫ y in Cᶜ, r o y ∂μ) / d ∧ |a o| ≤ c * w o) ∧
        θ = (∫ o, a o ∂ν) ∧
        θ ^ 2 ≤ (∫ o, a o ^ 2 ∂ν) ∧ |θ| ≤ b ^ 2 / d ^ 2 ∧
        Measurable (fun z : Ω × Ω => H z.1 z.2) ∧
        MemLp (fun z : Ω × Ω => H z.1 z.2) 2 (ν.prod ν) ∧
        q = 2 * u + lam * θ ∧
        Measurable G ∧ MemLp G 2 ν ∧
        (∀ᵐ o ∂μ, Integrable (H o) ν ∧
          G o = g o - u + lam * (a o - θ)) ∧
        (∫ o, G o ∂ν) = 0 ∧
        Integrable (fun o => g o * a o) ν ∧
        MemLp (fun o => g o + lam * a o) 2 ν ∧
        Integrable (fun o => G o ^ 2) ν ∧ 0 ≤ σ2 ∧
        |u| ≤ B * Real.rpow π (1 - 1 / p) / d ∧
        (∫ o in Cᶜ, g o ^ 2 ∂μ) ≤ B ^ 2 * Real.rpow π (1 - 2 / p) ∧
        |(∫ o, g o ^ 2 ∂ν) - 1| ≤
          2 * (1 + B ^ 2) * Real.rpow π (1 - 2 / p) ∧
        (∫ o, g o ^ 2 ∂ν) ≤ 2 ∧
        u ^ 2 ≤ 4 * B ^ 2 * Real.rpow π (1 - 2 / p) ∧
        (∫ o, a o ^ 2 ∂ν) ≤ 8 * W2 ^ 2 * b ^ 2 ∧
        |∫ o, g o * a o ∂ν| ≤ 4 * W2 * b ∧
        σ2 = (∫ o, (g o + lam * a o) ^ 2 ∂ν) - (u + lam * θ) ^ 2 ∧
        |σ2 - 1| ≤ Cvar * (Real.rpow π (1 - 2 / p) + b + b ^ 2) ∧
        (∀ m n : ℕ, m ≤ n →
          Real.sqrt (m : ℝ) * |q| ≤ Cmean * Real.sqrt (n : ℝ) *
            (Real.rpow π (1 - 1 / p) + b ^ 2)) := by
  classical
  dsimp only
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
  let B : ℝ := Real.rpow β (1 / p)
  let W2 : ℝ := Real.sqrt (∫ o, w o ^ 2 ∂μ)
  let Cvar : ℝ := 32 * (1 + B ^ 2 + W2 ^ 2)
  let Cmean : ℝ := 4 * (1 + B)
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
  have hg1 : Integrable g μ := hg2.integrable (by norm_num)
  have hgSqμ : Integrable (fun o => g o ^ 2) μ := hg2.integrable_sq
  have hp0 : 0 < p := by linarith only [hp.1]
  have hp1 : 1 < p := by linarith only [hp.1]
  have hinvp0 : 0 < 1 / p := div_pos zero_lt_one hp0
  have hβ0 : 0 ≤ β :=
    integral_nonneg (fun o => Real.rpow_nonneg (abs_nonneg (g o)) p)
  have hB0 : 0 ≤ B := Real.rpow_nonneg hβ0 (1 / p)
  have hW20 : 0 ≤ W2 := Real.sqrt_nonneg _
  have hCvar : 0 < Cvar := by
    dsimp only [Cvar]
    nlinarith only [sq_nonneg B, sq_nonneg W2]
  have hCmean : 0 < Cmean := by
    dsimp only [Cmean]
    linarith only [hB0]
  have hBsq : B ^ 2 = Real.rpow β (2 / p) := by
    calc
      B ^ 2 = Real.rpow (Real.rpow β (1 / p)) (2 : ℝ) :=
        (Real.rpow_natCast (Real.rpow β (1 / p)) 2).symm
      _ = Real.rpow β ((1 / p) * 2) := (Real.rpow_mul hβ0 _ _).symm
      _ = Real.rpow β (2 / p) := by congr 1; ring
  refine ⟨hβ0, hB0, hW20, hCvar, hCmean, ?_⟩
  intro R hcutoff lam hLam
  let C : Set Ω := {o : Ω | w o ≤ R}
  let π : ℝ := μ.real Cᶜ
  let d : ℝ := μ.real C
  let ν : Measure Ω := (μ C)⁻¹ • μ.restrict C
  let b : ℝ := ∫ o in Cᶜ, w o ∂μ
  let c : ℝ := b / d
  let u : ℝ := ∫ o, g o ∂ν
  let a : Ω → ℝ := fun o => ∫ y, r o y ∂ν
  let θ : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ∂(ν.prod ν)
  let H : Ω → Ω → ℝ := fun o y => g o + g y + lam * r o y
  let q : ℝ := ∫ z : Ω × Ω, H z.1 z.2 ∂(ν.prod ν)
  let G : Ω → ℝ := fun o => (∫ y, H o y ∂ν) - q
  let σ2 : ℝ := ∫ o, G o ^ 2 ∂ν
  have hdhalf : (1 / 2 : ℝ) ≤ d := hcutoff
  have hdpos : 0 < μ.real {o : Ω | w o ≤ R} := by
    linarith only [hcutoff]
  have hcarrier :=
    Shao.OQ6.ConditionalTrueProjectionCarrier.actual_conditional_true_projection_carrier
      μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone
      α τ hα hτ hwexp henvelope R hdpos lam hLam
  dsimp only at hcarrier
  rcases hcarrier with
    ⟨hAexp, hdom, hC, hdpi, hd, hπ0, hπlt, hνprob,
      hνac, hνprodac, hνC, hνmass, hνint, hw2, hwν2, hwνSecond,
      ham, ha2, haν2, hrows, hθmean, hθtail, hθbound,
      hHm, hH2, hq, hGm, hG2, hHrows, hGmean, hcarrierRest⟩
  clear hAexp hdom hνC hνmass ha2 hθtail hcarrierRest
  change MeasurableSet C at hC
  change d = 1 - π at hdpi
  change 0 < d at hd
  change 0 ≤ π at hπ0
  change π < 1 at hπlt
  change IsProbabilityMeasure ν at hνprob
  change ν ≪ μ at hνac
  change (ν.prod ν) ≪ (μ.prod μ) at hνprodac
  change (∀ f : Ω → ℝ, Integrable f μ →
    Integrable f ν ∧ (∫ o, f o ∂ν) = (∫ o in C, f o ∂μ) / d) at hνint
  change MemLp w 2 μ at hw2
  change MemLp w 2 ν at hwν2
  change (∫ o, w o ^ 2 ∂ν) ≤ (∫ o, w o ^ 2 ∂μ) / d at hwνSecond
  change Measurable a at ham
  change MemLp a 2 ν at haν2
  change (∀ᵐ o ∂μ, Integrable (r o) μ ∧ Integrable (r o) ν ∧
    a o = -(∫ y in Cᶜ, r o y ∂μ) / d ∧ |a o| ≤ c * w o) at hrows
  change θ = (∫ o, a o ∂ν) at hθmean
  change |θ| ≤ b ^ 2 / d ^ 2 at hθbound
  change Measurable (fun z : Ω × Ω => H z.1 z.2) at hHm
  change MemLp (fun z : Ω × Ω => H z.1 z.2) 2 (ν.prod ν) at hH2
  change q = 2 * u + lam * θ at hq
  change Measurable G at hGm
  change MemLp G 2 ν at hG2
  change (∀ᵐ o ∂μ, Integrable (H o) ν ∧
    G o = g o - u + lam * (a o - θ)) at hHrows
  change (∫ o, G o ∂ν) = 0 at hGmean
  haveI : IsProbabilityMeasure ν := hνprob
  have hgνSq : Integrable (fun o => g o ^ 2) ν :=
    (hνint (fun o => g o ^ 2) hgSqμ).1
  have hgν2 : MemLp g 2 ν :=
    (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2 hgνSq
  have hgν1 : Integrable g ν := hgν2.integrable (by norm_num)
  have haν1 : Integrable a ν := haν2.integrable (by norm_num)
  have haνSq : Integrable (fun o => a o ^ 2) ν := haν2.integrable_sq
  have hw0 : ∀ᵐ o ∂μ, 0 ≤ w o := hwone.mono (fun _ ho => by linarith only [ho])
  have hb0 : 0 ≤ b := integral_nonneg_of_ae (ae_restrict_of_ae hw0)
  have hc0 : 0 ≤ c := div_nonneg hb0 hd.le
  have hdle1 : d ≤ 1 := by linarith only [hdpi, hπ0]
  have hπle1 : π ≤ 1 := hπlt.le
  let t : ℝ := 1 - 1 / p
  let e : ℝ := 1 - 2 / p
  let p2 : ℝ := p / 2
  let pconj : ℝ := p / (p - 1)
  let p2conj : ℝ := p2 / (p2 - 1)
  let μD : Measure Ω := μ.restrict Cᶜ
  let gAbs : Ω → ℝ := fun o => |g o|
  let gSq : Ω → ℝ := fun o => g o ^ 2
  let one : Ω → ℝ := fun _ : Ω => (1 : ℝ)
  let F : Ω → ℝ := fun o => g o + lam * a o
  let M : ℝ := u + lam * θ
  let T1 : ℝ := ∫ o in Cᶜ, |g o| ∂μ
  let T2 : ℝ := ∫ o in Cᶜ, g o ^ 2 ∂μ
  let PgTail : ℝ := ∫ o in Cᶜ, Real.rpow |g o| p ∂μ
  let Sg2 : ℝ := ∫ o, g o ^ 2 ∂ν
  let Wμ2 : ℝ := ∫ o, w o ^ 2 ∂μ
  let A2 : ℝ := ∫ o, a o ^ 2 ∂ν
  let Iga : ℝ := ∫ o, g o * a o ∂ν
  have ht0 : 0 < t := by
    dsimp only [t]
    have hi : 1 / p < 1 := (div_lt_one hp0).2 hp1
    linarith only [hi]
  have he0 : 0 < e := by
    dsimp only [e]
    have hi : 2 / p < 1 := (div_lt_one hp0).2 hp.1
    linarith only [hi]
  have hele1 : e ≤ 1 := by
    dsimp only [e]
    have hi : 0 ≤ 2 / p := div_nonneg (by norm_num) hp0.le
    linarith only [hi]
  have htwoT : e ≤ 2 * t := by
    dsimp only [e, t]
    simp only [div_eq_mul_inv, one_mul]
    linarith only []
  have hp20 : 0 < p2 := div_pos hp0 (by norm_num)
  have hp21 : 1 < p2 := by dsimp only [p2]; linarith only [hp.1]
  have hpq : p.HolderConjugate pconj :=
    (Real.holderConjugate_iff_eq_conjExponent hp1).2 rfl
  have hp2q : p2.HolderConjugate p2conj :=
    (Real.holderConjugate_iff_eq_conjExponent hp21).2 rfl
  have hpconj0 : 0 < pconj := hpq.symm.pos
  have hp2conj0 : 0 < p2conj := hp2q.symm.pos
  have hinvpconj : 1 / pconj = t := by
    dsimp only [t]
    simpa only [one_div] using hpq.one_sub_inv.symm
  have hinvp2 : 1 / p2 = 2 / p := by
    dsimp only [p2]
    simp only [one_div, div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul]
  have hinvp2conj : 1 / p2conj = e := by
    have hhq : 1 / p2conj = 1 - 1 / p2 := by
      simpa only [one_div] using hp2q.one_sub_inv.symm
    rw [hhq, hinvp2]
  have hPg0 : 0 ≤ PgTail :=
    integral_nonneg (fun o => Real.rpow_nonneg (abs_nonneg (g o)) p)
  have hPgβ : PgTail ≤ β := by
    have hsplit := integral_add_compl hC hgp
    have hgGood0 : 0 ≤ ∫ o in C, Real.rpow |g o| p ∂μ :=
      integral_nonneg (fun o => Real.rpow_nonneg (abs_nonneg (g o)) p)
    change (∫ o in C, Real.rpow |g o| p ∂μ) + PgTail = β at hsplit
    linarith only [hsplit, hgGood0]
  have hDmass : μD.real Set.univ = π := by
    change ((μ.restrict Cᶜ) Set.univ).toReal = (μ Cᶜ).toReal
    rw [Measure.restrict_apply_univ]
  have hgAbsLp : MemLp gAbs (ENNReal.ofReal p) μD := by
    have hgAbsMeas : Measurable (fun o => |g o|) := by
      simpa only [Real.norm_eq_abs] using hgm.norm
    apply (integrable_norm_rpow_iff hgAbsMeas.aestronglyMeasurable
      (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp0)
      (by exact ENNReal.ofReal_ne_top)).1
    simpa only [gAbs, μD, Real.norm_eq_abs, abs_abs,
      ENNReal.toReal_ofReal hp0.le, Real.rpow_eq_pow] using hgp.restrict
  have hgSqPow : (fun o => Real.rpow (g o ^ 2) p2) =
      (fun o => Real.rpow |g o| p) := by
    funext o
    calc
      Real.rpow (g o ^ 2) p2 = Real.rpow (|g o| ^ 2) p2 := by rw [sq_abs]
      _ = Real.rpow |g o| ((2 : ℝ) * p2) := by
        simpa only [Real.rpow_eq_pow, Real.rpow_ofNat] using
          (Real.rpow_mul (abs_nonneg (g o)) (2 : ℝ) p2).symm
      _ = Real.rpow |g o| p := by congr 1; dsimp only [p2]; ring
  have hgSqLp : MemLp gSq (ENNReal.ofReal p2) μD := by
    apply (integrable_norm_rpow_iff (hgm.pow_const 2).aestronglyMeasurable
      (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp20)
      (by exact ENNReal.ofReal_ne_top)).1
    have hsame : (fun o => Real.rpow |g o ^ 2| p2) =
        (fun o => Real.rpow |g o| p) := by
      funext o
      rw [abs_of_nonneg (sq_nonneg (g o))]
      exact congrFun hgSqPow o
    have hpowerInt : Integrable (fun o => Real.rpow |g o ^ 2| p2) μD := by
      rw [hsame]
      exact hgp.restrict
    simpa only [gSq, Real.norm_eq_abs, ENNReal.toReal_ofReal hp20.le,
      Real.rpow_eq_pow] using hpowerInt
  have honeLp1 : MemLp one (ENNReal.ofReal pconj) μD := by
    apply (integrable_norm_rpow_iff measurable_const.aestronglyMeasurable
      (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hpconj0)
      (by exact ENNReal.ofReal_ne_top)).1
    simpa only [one, norm_one, Real.one_rpow] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μD)
  have honeLp2 : MemLp one (ENNReal.ofReal p2conj) μD := by
    apply (integrable_norm_rpow_iff measurable_const.aestronglyMeasurable
      (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp2conj0)
      (by exact ENNReal.ofReal_ne_top)).1
    simpa only [one, norm_one, Real.one_rpow] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μD)
  have hT1holder : T1 ≤ Real.rpow PgTail (1 / p) * Real.rpow π t := by
    change (∫ o, |g o| ∂μD) ≤
      Real.rpow (∫ o, Real.rpow |g o| p ∂μD) (1 / p) * Real.rpow π t
    have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
      (Filter.Eventually.of_forall (fun o => abs_nonneg (g o)))
      (Filter.Eventually.of_forall (fun _ : Ω => zero_le_one)) hgAbsLp honeLp1
    simpa only [gAbs, one, Real.rpow_eq_pow, mul_one, Real.one_rpow, integral_const,
      smul_eq_mul, mul_one, hDmass, hinvpconj] using hh
  have hT2holder : T2 ≤ Real.rpow PgTail (2 / p) * Real.rpow π e := by
    change (∫ o, g o ^ 2 ∂μD) ≤ Real.rpow PgTail (2 / p) * Real.rpow π e
    have hpower : (∫ o, (g o ^ 2) ^ p2 ∂μD) = PgTail := by
      calc
        _ = ∫ o, Real.rpow |g o| p ∂μD := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun o => by
            simpa only [Real.rpow_eq_pow] using congrFun hgSqPow o)
        _ = PgTail := rfl
    have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hp2q
      (Filter.Eventually.of_forall (fun o => sq_nonneg (g o)))
      (Filter.Eventually.of_forall (fun _ : Ω => zero_le_one)) hgSqLp honeLp2
    change (∫ o, gSq o * one o ∂μD) ≤ _ at hh
    rw [hpower] at hh
    simpa only [gSq, one, Real.rpow_eq_pow, mul_one, Real.one_rpow, integral_const,
      smul_eq_mul, mul_one, hDmass, hinvp2, hinvp2conj] using hh
  have hπt0 : 0 ≤ Real.rpow π t := Real.rpow_nonneg hπ0 t
  have hπe0 : 0 ≤ Real.rpow π e := Real.rpow_nonneg hπ0 e
  have hT1 : T1 ≤ B * Real.rpow π t := by
    apply hT1holder.trans
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hPg0 hPgβ hinvp0.le) hπt0
  have hT2 : T2 ≤ B ^ 2 * Real.rpow π e := by
    apply hT2holder.trans
    rw [hBsq]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hPg0 hPgβ (div_nonneg (by norm_num) hp0.le)) hπe0
  have hinvd : 1 / d ≤ 2 := (div_le_iff₀ hd).2 (by linarith only [hdhalf])
  have huTail : u = -(∫ o in Cᶜ, g o ∂μ) / d := by
    have hsplit := integral_add_compl hC hg1
    rw [hgmean] at hsplit
    change (∫ o, g o ∂ν) = _
    rw [(hνint g hg1).2]
    congr 1
    linarith only [hsplit]
  have huBound : |u| ≤ B * Real.rpow π t / d := by
    have habs : |∫ o in Cᶜ, g o ∂μ| ≤ T1 := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := μ.restrict Cᶜ) g)
    rw [huTail, abs_div, abs_neg, abs_of_pos hd]
    exact div_le_div_of_nonneg_right (habs.trans hT1) hd.le
  have huTwo : |u| ≤ 2 * B * Real.rpow π t := by
    calc
      |u| ≤ B * Real.rpow π t / d := huBound
      _ = (B * Real.rpow π t) * (1 / d) := by ring
      _ ≤ (B * Real.rpow π t) * 2 :=
        mul_le_mul_of_nonneg_left hinvd (mul_nonneg hB0 hπt0)
      _ = 2 * B * Real.rpow π t := by ring
  have hT20 : 0 ≤ T2 := integral_nonneg (fun o => sq_nonneg (g o))
  have hSg20 : 0 ≤ Sg2 := integral_nonneg (fun o => sq_nonneg (g o))
  have hSplitG2 : (∫ o in C, g o ^ 2 ∂μ) + T2 = 1 := by
    have hh := integral_add_compl hC hgSqμ
    rw [hgsecond] at hh
    exact hh
  have hSg2 : Sg2 = (1 - T2) / d := by
    change (∫ o, g o ^ 2 ∂ν) = _
    rw [(hνint (fun o => g o ^ 2) hgSqμ).2]
    congr 1
    linarith only [hSplitG2]
  have hSg2le : Sg2 ≤ 2 := by
    calc
      Sg2 = (1 - T2) / d := hSg2
      _ ≤ 1 / d := div_le_div_of_nonneg_right (by linarith only [hT20]) hd.le
      _ ≤ 2 := hinvd
  have hLoss : Sg2 - 1 = (π - T2) / d := by
    apply (eq_div_iff hd.ne').2
    have hh : Sg2 * d = 1 - T2 := (eq_div_iff hd.ne').1 hSg2
    nlinarith only [hh, hdpi]
  have hπPower : π ≤ Real.rpow π e := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge' hπ0 hπle1 he0.le hele1)
  have hSg2error : |Sg2 - 1| ≤ 2 * (1 + B ^ 2) * Real.rpow π e := by
    have hnum : |π - T2| ≤ (1 + B ^ 2) * Real.rpow π e := by
      calc
        |π - T2| ≤ |π| + |T2| := abs_sub _ _
        _ = π + T2 := by rw [abs_of_nonneg hπ0, abs_of_nonneg hT20]
        _ ≤ Real.rpow π e + B ^ 2 * Real.rpow π e := add_le_add hπPower hT2
        _ = (1 + B ^ 2) * Real.rpow π e := by ring
    rw [hLoss, abs_div, abs_of_pos hd]
    calc
      |π - T2| / d ≤ ((1 + B ^ 2) * Real.rpow π e) / d :=
        div_le_div_of_nonneg_right hnum hd.le
      _ = ((1 + B ^ 2) * Real.rpow π e) * (1 / d) := by ring
      _ ≤ ((1 + B ^ 2) * Real.rpow π e) * 2 :=
        mul_le_mul_of_nonneg_left hinvd
          (mul_nonneg (by nlinarith only [sq_nonneg B]) hπe0)
      _ = 2 * (1 + B ^ 2) * Real.rpow π e := by ring
  have hπtSq : (Real.rpow π t) ^ 2 = Real.rpow π (2 * t) := by
    calc
      (Real.rpow π t) ^ 2 = Real.rpow (Real.rpow π t) (2 : ℝ) :=
        (Real.rpow_natCast (Real.rpow π t) 2).symm
      _ = Real.rpow π (t * 2) := (Real.rpow_mul hπ0 t 2).symm
      _ = Real.rpow π (2 * t) := by congr 1; ring
  have huSq : u ^ 2 ≤ 4 * B ^ 2 * Real.rpow π e := by
    calc
      u ^ 2 = |u| ^ 2 := (sq_abs u).symm
      _ ≤ (2 * B * Real.rpow π t) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg u)
          (mul_nonneg (mul_nonneg (by norm_num) hB0) hπt0)).2 huTwo
      _ = 4 * B ^ 2 * Real.rpow π (2 * t) := by rw [mul_pow, mul_pow, hπtSq]; ring
      _ ≤ 4 * B ^ 2 * Real.rpow π e :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge' hπ0 hπle1 he0.le htwoT)
          (mul_nonneg (by norm_num) (sq_nonneg B))
  have hWμ20 : 0 ≤ Wμ2 := integral_nonneg (fun o => sq_nonneg (w o))
  have hW2sq : W2 ^ 2 = Wμ2 := Real.sq_sqrt hWμ20
  have hwSecond : (∫ o, w o ^ 2 ∂ν) ≤ W2 ^ 2 / d := by
    rw [hW2sq]
    exact hwνSecond
  have hwSecondTwo : (∫ o, w o ^ 2 ∂ν) ≤ 2 * W2 ^ 2 := by
    calc
      _ ≤ W2 ^ 2 / d := hwSecond
      _ = W2 ^ 2 * (1 / d) := by ring
      _ ≤ W2 ^ 2 * 2 := mul_le_mul_of_nonneg_left hinvd (sq_nonneg W2)
      _ = 2 * W2 ^ 2 := by ring
  have hcTwo : c ≤ 2 * b := by
    change b / d ≤ 2 * b
    apply (div_le_iff₀ hd).2
    have hh := mul_le_mul_of_nonneg_left
      (show (1 : ℝ) ≤ 2 * d by linarith only [hdhalf]) hb0
    nlinarith only [hh]
  have hcSq : c ^ 2 ≤ 4 * b ^ 2 := by
    have hh := (sq_le_sq₀ hc0 (mul_nonneg (by norm_num) hb0)).2 hcTwo
    nlinarith only [hh]
  have hA20 : 0 ≤ A2 := integral_nonneg (fun o => sq_nonneg (a o))
  have hA2scale : A2 ≤ c ^ 2 * (∫ o, w o ^ 2 ∂ν) := by
    calc
      A2 ≤ ∫ o, c ^ 2 * w o ^ 2 ∂ν := by
        apply integral_mono_ae haνSq (hwν2.integrable_sq.const_mul (c ^ 2))
        filter_upwards [hνac.ae_le hrows, hνac.ae_le hw0] with o ho hwo
        have hh := (sq_le_sq₀ (abs_nonneg (a o)) (mul_nonneg hc0 hwo)).2 ho.2.2.2
        simpa only [sq_abs, mul_pow] using hh
      _ = c ^ 2 * (∫ o, w o ^ 2 ∂ν) := integral_const_mul _ _
  have hA2bound : A2 ≤ 8 * W2 ^ 2 * b ^ 2 := by
    calc
      A2 ≤ c ^ 2 * (∫ o, w o ^ 2 ∂ν) := hA2scale
      _ ≤ c ^ 2 * (2 * W2 ^ 2) :=
        mul_le_mul_of_nonneg_left hwSecondTwo (sq_nonneg c)
      _ ≤ (4 * b ^ 2) * (2 * W2 ^ 2) :=
        mul_le_mul_of_nonneg_right hcSq (mul_nonneg (by norm_num) (sq_nonneg W2))
      _ = 8 * W2 ^ 2 * b ^ 2 := by ring
  have hθSq : θ ^ 2 ≤ A2 := by
    have hcenter : (∫ o, (a o - θ) ^ 2 ∂ν) = A2 - θ ^ 2 := by
      calc
        _ = ∫ o, a o ^ 2 - (2 * θ) * a o + θ ^ 2 ∂ν :=
          integral_congr_ae (Filter.Eventually.of_forall (fun o => by ring))
        _ = A2 - (2 * θ) * (∫ o, a o ∂ν) + θ ^ 2 := by
          rw [integral_add (f := fun o => a o ^ 2 - (2 * θ) * a o)
              (g := fun _ : Ω => θ ^ 2) (haνSq.sub (haν1.const_mul (2 * θ)))
              (integrable_const (θ ^ 2)),
            integral_sub (f := fun o => a o ^ 2) (g := fun o => (2 * θ) * a o)
              haνSq (haν1.const_mul (2 * θ)), integral_const_mul,
            integral_const, probReal_univ, one_smul]
        _ = A2 - θ ^ 2 := by rw [← hθmean]; ring
    have hh : 0 ≤ ∫ o, (a o - θ) ^ 2 ∂ν :=
      integral_nonneg (fun o => sq_nonneg (a o - θ))
    rw [hcenter] at hh
    linarith only [hh]
  have hgaInt : Integrable (fun o => g o * a o) ν := by
    apply (hgνSq.add haνSq).mono' (hgm.mul ham).aestronglyMeasurable
    filter_upwards with o
    change ‖g o * a o‖ ≤ g o ^ 2 + a o ^ 2
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith only [sq_nonneg (|g o| - |a o|), sq_abs (g o), sq_abs (a o),
      sq_nonneg (g o), sq_nonneg (a o)]
  have hIholder : |Iga| ≤ Real.rpow Sg2 (1 / 2) * Real.rpow A2 (1 / 2) := by
    have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
      (show MemLp g (ENNReal.ofReal (2 : ℝ)) ν by norm_num; exact hgν2)
      (show MemLp a (ENNReal.ofReal (2 : ℝ)) ν by norm_num; exact haν2)
    have hgNormSquare : (∫ o, ‖g o‖ ^ (2 : ℝ) ∂ν) = Sg2 := by
      calc
        _ = ∫ o, g o ^ 2 ∂ν := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun o => by
            change ‖g o‖ ^ (2 : ℝ) = g o ^ 2
            rw [Real.rpow_ofNat ‖g o‖ 2, Real.norm_eq_abs, sq_abs])
        _ = Sg2 := rfl
    have haNormSquare : (∫ o, ‖a o‖ ^ (2 : ℝ) ∂ν) = A2 := by
      calc
        _ = ∫ o, a o ^ 2 ∂ν := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun o => by
            change ‖a o‖ ^ (2 : ℝ) = a o ^ 2
            rw [Real.rpow_ofNat ‖a o‖ 2, Real.norm_eq_abs, sq_abs])
        _ = A2 := rfl
    rw [hgNormSquare, haNormSquare] at hh
    calc
      |Iga| ≤ ∫ o, |g o * a o| ∂ν := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (μ := ν) (fun o => g o * a o))
      _ = ∫ o, |g o| * |a o| ∂ν := by simp only [abs_mul]
      _ ≤ Real.rpow Sg2 (1 / 2) * Real.rpow A2 (1 / 2) := by
        simpa only [Real.norm_eq_abs, Real.rpow_eq_pow] using hh
  have hSroot : (Real.rpow Sg2 (1 / 2)) ^ 2 = Sg2 := by
    calc
      (Real.rpow Sg2 (1 / 2)) ^ 2 =
          Real.rpow (Real.rpow Sg2 (1 / 2)) (2 : ℝ) := by
        simpa only [Real.rpow_eq_pow] using
          (Real.rpow_ofNat (Real.rpow Sg2 (1 / 2)) 2).symm
      _ = Real.rpow Sg2 ((1 / 2) * 2) := by
        simpa only [Real.rpow_eq_pow] using (Real.rpow_mul hSg20 (1 / 2) 2).symm
      _ = Sg2 := by norm_num [Real.rpow_eq_pow]
  have hAroot : (Real.rpow A2 (1 / 2)) ^ 2 = A2 := by
    calc
      (Real.rpow A2 (1 / 2)) ^ 2 =
          Real.rpow (Real.rpow A2 (1 / 2)) (2 : ℝ) := by
        simpa only [Real.rpow_eq_pow] using
          (Real.rpow_ofNat (Real.rpow A2 (1 / 2)) 2).symm
      _ = Real.rpow A2 ((1 / 2) * 2) := by
        simpa only [Real.rpow_eq_pow] using (Real.rpow_mul hA20 (1 / 2) 2).symm
      _ = A2 := by norm_num [Real.rpow_eq_pow]
  have hIsq : Iga ^ 2 ≤ Sg2 * A2 := by
    have hh := (sq_le_sq₀ (abs_nonneg Iga)
      (mul_nonneg (Real.rpow_nonneg hSg20 _) (Real.rpow_nonneg hA20 _))).2 hIholder
    have hh' : Iga ^ 2 ≤ (Real.rpow Sg2 (1 / 2)) ^ 2 *
        (Real.rpow A2 (1 / 2)) ^ 2 := by
      simpa only [Real.rpow_eq_pow, sq_abs, mul_pow] using hh
    rw [hSroot, hAroot] at hh'
    exact hh'
  have hI16 : Iga ^ 2 ≤ 16 * W2 ^ 2 * b ^ 2 := by
    calc
      Iga ^ 2 ≤ Sg2 * A2 := hIsq
      _ ≤ 2 * A2 := mul_le_mul_of_nonneg_right hSg2le hA20
      _ ≤ 2 * (8 * W2 ^ 2 * b ^ 2) :=
        mul_le_mul_of_nonneg_left hA2bound (by norm_num)
      _ = 16 * W2 ^ 2 * b ^ 2 := by ring
  have hIbound : |Iga| ≤ 4 * W2 * b := by
    apply (sq_le_sq₀ (abs_nonneg Iga)
      (mul_nonneg (mul_nonneg (by norm_num) hW20) hb0)).1
    rw [sq_abs]
    nlinarith only [hI16]
  have hF2 : MemLp F 2 ν := hgν2.add (haν2.const_mul lam)
  have hF1 : Integrable F ν := hF2.integrable (by norm_num)
  have hFmean : (∫ o, F o ∂ν) = M := by
    calc
      (∫ o, F o ∂ν) = (∫ o, g o ∂ν) + (∫ o, lam * a o ∂ν) :=
        integral_add (f := g) (g := fun o => lam * a o)
          hgν1 (haν1.const_mul lam)
      _ = u + lam * θ := by rw [integral_const_mul, ← hθmean]
      _ = M := rfl
  have hGagree : G =ᵐ[ν] (fun o => F o - M) := by
    filter_upwards [hνac.ae_le hHrows] with o ho
    rw [ho.2]
    dsimp only [F, M]
    ring
  have hσInt : Integrable (fun o => G o ^ 2) ν := hG2.integrable_sq
  have hσ0 : 0 ≤ σ2 := integral_nonneg (fun o => sq_nonneg (G o))
  have hσIdentity : σ2 = (∫ o, F o ^ 2 ∂ν) - M ^ 2 := by
    calc
      σ2 = ∫ o, (F o - M) ^ 2 ∂ν := by
        apply integral_congr_ae
        exact hGagree.mono (fun _ ho => congrArg (fun s : ℝ => s ^ 2) ho)
      _ = ∫ o, F o ^ 2 - (2 * M) * F o + M ^ 2 ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall (fun o => by ring))
      _ = (∫ o, F o ^ 2 ∂ν) - (2 * M) * (∫ o, F o ∂ν) + M ^ 2 := by
        rw [integral_add (f := fun o => F o ^ 2 - (2 * M) * F o)
            (g := fun _ : Ω => M ^ 2)
            (hF2.integrable_sq.sub (hF1.const_mul (2 * M))) (integrable_const (M ^ 2)),
          integral_sub (f := fun o => F o ^ 2) (g := fun o => (2 * M) * F o)
            hF2.integrable_sq (hF1.const_mul (2 * M)),
          integral_const_mul, integral_const, probReal_univ, one_smul]
      _ = (∫ o, F o ^ 2 ∂ν) - M ^ 2 := by rw [hFmean]; ring
  have hFenergy : (∫ o, F o ^ 2 ∂ν) = Sg2 + (2 * lam) * Iga + lam ^ 2 * A2 := by
    calc
      _ = ∫ o, g o ^ 2 + (2 * lam) * (g o * a o) + lam ^ 2 * a o ^ 2 ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun o => by dsimp only [F]; ring)
      _ = Sg2 + (2 * lam) * Iga + lam ^ 2 * A2 := by
        rw [integral_add (f := fun o => g o ^ 2 + (2 * lam) * (g o * a o))
            (g := fun o => lam ^ 2 * a o ^ 2)
            (hgνSq.add (hgaInt.const_mul (2 * lam))) (haνSq.const_mul (lam ^ 2)),
          integral_add (f := fun o => g o ^ 2) (g := fun o => (2 * lam) * (g o * a o))
            hgνSq (hgaInt.const_mul (2 * lam)), integral_const_mul, integral_const_mul]
  have hLamSq : lam ^ 2 ≤ 1 := by
    have hh := mul_nonneg hLam.1 (sub_nonneg.mpr hLam.2)
    nlinarith only [hh, hLam.2]
  have hMsq : M ^ 2 ≤ 2 * u ^ 2 + 2 * θ ^ 2 := by
    have hh : lam ^ 2 * θ ^ 2 ≤ θ ^ 2 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hLamSq (sq_nonneg θ)
    dsimp only [M]
    nlinarith only [sq_nonneg (u - lam * θ), hh]
  have hσExpanded : σ2 - 1 = (Sg2 - 1) + (2 * lam) * Iga + lam ^ 2 * A2 - M ^ 2 := by
    rw [hσIdentity, hFenergy]
    ring
  have hCross : |(2 * lam) * Iga| ≤ 2 * |Iga| := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) hLam.1)]
    have hh := mul_le_mul_of_nonneg_right hLam.2 (abs_nonneg Iga)
    nlinarith only [hh]
  have hATerm : |lam ^ 2 * A2| ≤ A2 := by
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg lam) hA20)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hLamSq hA20
  have hσTriangle : |σ2 - 1| ≤ |Sg2 - 1| + 2 * |Iga| + A2 + M ^ 2 := by
    rw [hσExpanded]
    calc
      |(Sg2 - 1) + (2 * lam) * Iga + lam ^ 2 * A2 - M ^ 2| ≤
          |(Sg2 - 1) + (2 * lam) * Iga + lam ^ 2 * A2| + |M ^ 2| := abs_sub _ _
      _ ≤ (|(Sg2 - 1) + (2 * lam) * Iga| + |lam ^ 2 * A2|) + |M ^ 2| :=
        add_le_add (abs_add_le _ _) (le_refl |M ^ 2|)
      _ ≤ ((|Sg2 - 1| + |(2 * lam) * Iga|) + |lam ^ 2 * A2|) + |M ^ 2| :=
        add_le_add (add_le_add (abs_add_le _ _) (le_refl |lam ^ 2 * A2|))
          (le_refl |M ^ 2|)
      _ ≤ |Sg2 - 1| + 2 * |Iga| + A2 + M ^ 2 := by
        rw [abs_of_nonneg (sq_nonneg M)]
        exact add_le_add (add_le_add (add_le_add (le_refl |Sg2 - 1|) hCross) hATerm)
          (le_refl (M ^ 2))
  have hθSqBound : θ ^ 2 ≤ 8 * W2 ^ 2 * b ^ 2 := hθSq.trans hA2bound
  have hVarStrong : |σ2 - 1| ≤
      (2 + 10 * B ^ 2) * Real.rpow π e + 8 * W2 * b + 24 * W2 ^ 2 * b ^ 2 := by
    nlinarith only [hσTriangle, hSg2error, hIbound, hA2bound, hMsq, huSq, hθSqBound]
  have hCvar1 : 2 + 10 * B ^ 2 ≤ Cvar := by
    dsimp only [Cvar]
    nlinarith only [sq_nonneg B, sq_nonneg W2]
  have hCvar2 : 8 * W2 ≤ Cvar := by
    dsimp only [Cvar]
    nlinarith only [sq_nonneg (W2 - 1), sq_nonneg B, sq_nonneg W2]
  have hCvar3 : 24 * W2 ^ 2 ≤ Cvar := by
    dsimp only [Cvar]
    nlinarith only [sq_nonneg B, sq_nonneg W2]
  have hVariance : |σ2 - 1| ≤ Cvar * (Real.rpow π e + b + b ^ 2) := by
    calc
      |σ2 - 1| ≤ (2 + 10 * B ^ 2) * Real.rpow π e +
          8 * W2 * b + 24 * W2 ^ 2 * b ^ 2 := hVarStrong
      _ ≤ Cvar * Real.rpow π e + Cvar * b + Cvar * b ^ 2 :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_right hCvar1 hπe0)
          (mul_le_mul_of_nonneg_right hCvar2 hb0))
          (mul_le_mul_of_nonneg_right hCvar3 (sq_nonneg b))
      _ = Cvar * (Real.rpow π e + b + b ^ 2) := by ring
  have hθFour : |θ| ≤ 4 * b ^ 2 := by
    calc
      |θ| ≤ b ^ 2 / d ^ 2 := hθbound
      _ = c ^ 2 := by dsimp only [c]; rw [div_pow]
      _ ≤ 4 * b ^ 2 := hcSq
  have hQFour : |q| ≤ 4 * (B * Real.rpow π t + b ^ 2) := by
    rw [hq]
    calc
      |2 * u + lam * θ| ≤ |2 * u| + |lam * θ| := abs_add_le _ _
      _ = 2 * |u| + lam * |θ| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hLam.1]
        norm_num
      _ ≤ 2 * (2 * B * Real.rpow π t) + 4 * b ^ 2 := by
        have hh : lam * |θ| ≤ |θ| := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hLam.2 (abs_nonneg θ)
        linarith only [huTwo, hθFour, hh]
      _ = 4 * (B * Real.rpow π t + b ^ 2) := by ring
  have hMean : ∀ m n : ℕ, m ≤ n →
      Real.sqrt (m : ℝ) * |q| ≤ Cmean * Real.sqrt (n : ℝ) *
        (Real.rpow π t + b ^ 2) := by
    intro m n hmn
    have hsqrt : Real.sqrt (m : ℝ) ≤ Real.sqrt (n : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hmn)
    have hconst : 4 * (B * Real.rpow π t + b ^ 2) ≤
        Cmean * (Real.rpow π t + b ^ 2) := by
      dsimp only [Cmean]
      nlinarith only [hπt0, mul_nonneg hB0 (sq_nonneg b)]
    calc
      Real.sqrt (m : ℝ) * |q| ≤ Real.sqrt (n : ℝ) * |q| :=
        mul_le_mul_of_nonneg_right hsqrt (abs_nonneg q)
      _ ≤ Real.sqrt (n : ℝ) * (4 * (B * Real.rpow π t + b ^ 2)) :=
        mul_le_mul_of_nonneg_left hQFour (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt (n : ℝ) * (Cmean * (Real.rpow π t + b ^ 2)) :=
        mul_le_mul_of_nonneg_left hconst (Real.sqrt_nonneg _)
      _ = Cmean * Real.sqrt (n : ℝ) * (Real.rpow π t + b ^ 2) := by ring
  exact ⟨hC, hdpi, hd, hπ0, hπlt, hb0, hνprob, hνac, hνprodac,
    hgm, hg2, hgν2, hgmean, hgsecond, hw2, hwν2, hwSecond,
    ham, haν2, hrows, hθmean, hθSq, hθbound, hHm, hH2, hq,
    hGm, hG2, hHrows, hGmean, hgaInt, hF2, hσInt, hσ0,
    huBound, hT2, hSg2error, hSg2le, huSq, hA2bound, hIbound,
    hσIdentity, hVariance, hMean⟩

end

end Shao.OQ6.ConditionalVarianceMean
