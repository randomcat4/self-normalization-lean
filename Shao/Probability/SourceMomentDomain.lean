import Shao.Probability.TruncationSampleSize
import Shao.Probability.TruncationIntegrals
import Shao.Probability.FiniteIID
import Shao.Probability.MeasurablePath
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
Original moment-domain guards and exact normalization of the actual raw law.
These are auxiliary producers for C1; endpoint, small-boundary and root
assembly obligations are separate. No centering is needed for the guards.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Shao.Probability
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem original_moment_domain_coarse_guards
    (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hp : Integrable (fun z : ℝ => Real.rpow |z| p) nu) :
    let beta : ℝ := (n : ℝ) * (∫ z : ℝ, Real.rpow |z| p ∂nu)
    let H : ℝ := Real.rpow beta (-1 / p)
    0 < beta ∧ Real.rpow (n : ℝ) (-(p - 2) / 2) ≤ beta ∧
      0 < H ∧ H ≤ Real.rpow (n : ℝ) (1 / 6) ∧
      (∀ x : ℝ, 0 ≤ x → x ≤ H →
        x ^ 6 ≤ (n : ℝ) ∧
          (n : ℝ) * (∫ z : ℝ, Shao.truncationF (x * z) ∂nu) ≤ 1) := by
  simp only [Real.rpow_eq_pow] at hp ⊢
  let beta : ℝ := (n : ℝ) * (∫ z : ℝ, (|z| ^ (p : ℝ)) ∂nu)
  let H : ℝ := (beta ^ ((-1 / p) : ℝ))
  change 0 < beta ∧ _ ≤ beta ∧ 0 < H ∧ H ≤ _ ∧ _
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : 0 < p := by linarith
  have hscale (z : ℝ) : (((n : ℝ) * z ^ 2) ^ ((p / 2) : ℝ)) =
      ((n : ℝ) ^ ((p / 2) : ℝ)) * (|z| ^ (p : ℝ)) := by
    rw [Real.mul_rpow hN.le (sq_nonneg z), ← sq_abs z,
      ← Real.rpow_natCast_mul (abs_nonneg z) 2 (p / 2)]
    congr 2
    ring
  have hU : Integrable (fun z : ℝ => (((n : ℝ) * z ^ 2) ^ ((p / 2) : ℝ))) nu :=
    (hp.const_mul (((n : ℝ) ^ ((p / 2) : ℝ)))).congr
      (ae_of_all nu (fun z => (hscale z).symm))
  have htan (z : ℝ) : 1 + (p / 2) * ((n : ℝ) * z ^ 2 - 1) ≤
      (((n : ℝ) * z ^ 2) ^ ((p / 2) : ℝ)) := by
    have h := one_add_mul_self_le_rpow_one_add
      (s := (n : ℝ) * z ^ 2 - 1) (by nlinarith [sq_nonneg z])
      (p := p / 2) (by linarith)
    simpa only [add_sub_cancel] using h
  have hItan := integral_mono
    ((integrable_const (1 : ℝ)).add
      (((h2.const_mul (n : ℝ)).sub (integrable_const (1 : ℝ))).const_mul (p / 2)))
    hU htan
  have hmoment : 1 ≤ ((n : ℝ) ^ ((p / 2) : ℝ)) *
      (∫ z : ℝ, (|z| ^ (p : ℝ)) ∂nu) := by
    have hright : (∫ z : ℝ, (((n : ℝ) * z ^ 2) ^ ((p / 2) : ℝ)) ∂nu) =
        ((n : ℝ) ^ ((p / 2) : ℝ)) * (∫ z : ℝ, (|z| ^ (p : ℝ)) ∂nu) := by
      simp_rw [hscale]
      exact integral_const_mul _ _
    rw [hright] at hItan
    change (∫ z : ℝ, 1 + (p / 2) * ((n : ℝ) * z ^ 2 - 1) ∂nu) ≤ _ at hItan
    rw [integral_add (f := fun _ : ℝ => (1 : ℝ))
      (g := fun z : ℝ => (p / 2) * ((n : ℝ) * z ^ 2 - 1)) (integrable_const (1 : ℝ))
      (((h2.const_mul (n : ℝ)).sub (integrable_const (1 : ℝ))).const_mul (p / 2)),
      integral_const_mul,
      integral_sub (f := fun z : ℝ => (n : ℝ) * z ^ 2) (g := fun _ : ℝ => (1 : ℝ))
        (h2.const_mul (n : ℝ)) (integrable_const (1 : ℝ)),
      integral_const_mul] at hItan
    simpa [hnorm] using hItan
  have hlower : ((n : ℝ) ^ ((-(p - 2) / 2) : ℝ)) ≤ beta := by
    have hpow : ((n : ℝ) ^ ((p / 2) : ℝ)) *
        ((n : ℝ) ^ ((-(p - 2) / 2) : ℝ)) = (n : ℝ) := by
      rw [← Real.rpow_add hN]
      convert Real.rpow_one (n : ℝ) using 2 <;> ring
    apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hN (p / 2))).mp
    calc
      _ = (n : ℝ) := hpow
      _ ≤ (n : ℝ) * (((n : ℝ) ^ ((p / 2) : ℝ)) *
          (∫ z : ℝ, (|z| ^ (p : ℝ)) ∂nu)) := by nlinarith
      _ = _ := by dsimp [beta]; ring
  have hb : 0 < beta := (Real.rpow_pos_of_pos hN _).trans_le hlower
  have hH : 0 < H := Real.rpow_pos_of_pos hb _
  have hHbound : H ≤ ((n : ℝ) ^ ((1 / 6) : ℝ)) := by
    calc
      H ≤ ((((n : ℝ) ^ ((-(p - 2) / 2) : ℝ))) ^ ((-1 / p) : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN _) hlower (by exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hp0.le)
      _ = ((n : ℝ) ^ (((p - 2) / (2 * p)) : ℝ)) := by
        rw [← Real.rpow_mul hN.le]
        congr 1
        field_simp
        <;> ring
      _ ≤ ((n : ℝ) ^ ((1 / 6) : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hN1
        apply (div_le_iff₀ (by positivity : 0 < 2 * p)).2
        nlinarith
  have hHpow : (H ^ (p : ℝ)) * beta = 1 := by
    dsimp [H]
    rw [← Real.rpow_mul hb.le]
    have he : (-1 / p) * p = (-1 : ℝ) := by field_simp
    rw [he, Real.rpow_neg_one]
    exact inv_mul_cancel₀ hb.ne'
  refine ⟨hb, hlower, hH, hHbound, ?_⟩
  intro x hx hxH
  constructor
  · calc
      x ^ 6 ≤ (((n : ℝ) ^ ((1 / 6) : ℝ))) ^ 6 :=
        pow_le_pow_left₀ hx (hxH.trans hHbound) 6
      _ = (n : ℝ) := by
        rw [← Real.rpow_mul_natCast hN.le]
        norm_num
  · have hpoint (z : ℝ) : (|x * z| ^ (p : ℝ)) =
        (x ^ (p : ℝ)) * (|z| ^ (p : ℝ)) := by
      rw [abs_mul, abs_of_nonneg hx, Real.mul_rpow hx (abs_nonneg z)]
    have hxp : Integrable (fun z : ℝ => (|x * z| ^ (p : ℝ))) nu :=
      (hp.const_mul ((x ^ (p : ℝ)))).congr (ae_of_all nu (fun z => (hpoint z).symm))
    have hi := integral_mono (Shao.integrable_truncationF_mul nu h2 x) hxp
      (fun z => Shao.truncationF_le_rpow (x * z) p hp2.le hp3)
    have hi' : (∫ z : ℝ, Shao.truncationF (x * z) ∂nu) ≤
        (x ^ (p : ℝ)) * (∫ z : ℝ, (|z| ^ (p : ℝ)) ∂nu) := by
      simpa only [hpoint, integral_const_mul] using hi
    calc
      _ ≤ (x ^ (p : ℝ)) * beta := by dsimp [beta]; nlinarith
      _ ≤ (H ^ (p : ℝ)) * beta :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx hxH hp0.le) hb.le
      _ = 1 := hHpow

theorem original_raw_normalization_data
    (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) mu)
    (hmean : (∫ z : ℝ, z ∂mu) = 0)
    (hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂mu)
    (hp : Integrable (fun z : ℝ => Real.rpow |z| p) mu) :
    let sigma : ℝ := Real.sqrt (∫ z : ℝ, z ^ 2 ∂mu)
    let nu : Measure ℝ := Measure.map
      (fun z : ℝ => z / (sigma * Real.sqrt (n : ℝ))) mu
    let beta : ℝ := (∫ z : ℝ, Real.rpow |z| p ∂mu) /
      (Real.rpow sigma p * Real.rpow (n : ℝ) ((p - 2) / 2))
    let Praw : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
    let Pnorm : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    0 < sigma ∧ IsProbabilityMeasure nu ∧
      Integrable (fun z : ℝ => z ^ 2) nu ∧
      (∫ z : ℝ, z ∂nu) = 0 ∧
      (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 ∧
      Integrable (fun z : ℝ => Real.rpow |z| p) nu ∧
      (∫ z : ℝ, Real.rpow |z| p ∂nu) =
        (∫ z : ℝ, Real.rpow |z| p ∂mu) /
          (Real.rpow sigma p * Real.rpow (n : ℝ) (p / 2)) ∧
      0 < beta ∧ beta = (n : ℝ) * (∫ z : ℝ, Real.rpow |z| p ∂nu) ∧
      Measure.map (fun a : Shao.Path n =>
        (fun i : Fin n => a i / (sigma * Real.sqrt (n : ℝ)))) Praw = Pnorm ∧
      (∀ x s : ℝ, (s = 1 ∨ s = -1) →
        Pnorm.real {v : Shao.Path n |
          x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn} =
        Praw.real {v : Shao.Path n |
          x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn}) := by
  simp only [Real.rpow_eq_pow] at hp ⊢
  let sigma : ℝ := Real.sqrt (∫ z : ℝ, z ^ 2 ∂mu)
  let nu : Measure ℝ := Measure.map
    (fun z : ℝ => z / (sigma * Real.sqrt (n : ℝ))) mu
  let beta : ℝ := (∫ z : ℝ, (|z| ^ (p : ℝ)) ∂mu) /
    ((sigma ^ (p : ℝ)) * ((n : ℝ) ^ (((p - 2) / 2) : ℝ)))
  let Praw : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
  let Pnorm : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  change 0 < sigma ∧ IsProbabilityMeasure nu ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧
    0 < beta ∧ beta = _ ∧ Measure.map _ Praw = Pnorm ∧ _
  let b : ℝ := sigma * Real.sqrt (n : ℝ)
  let c : ℝ := b⁻¹
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hsigma : 0 < sigma := Real.sqrt_pos.2 hsecond
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hN
  have hb : 0 < b := mul_pos hsigma hsn
  have hc : 0 < c := inv_pos.2 hb
  have hsigma2 : sigma ^ 2 = ∫ z : ℝ, z ^ 2 ∂mu := Real.sq_sqrt hsecond.le
  have hsn2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hN.le
  have hscale : Measurable (fun z : ℝ => z / b) := by fun_prop
  have heq (z : ℝ) : z / b = c * z := by dsimp [c]; rw [div_eq_mul_inv]; ring
  have hprob : IsProbabilityMeasure nu := by dsimp [nu]; infer_instance
  let : IsProbabilityMeasure nu := hprob
  have h1 : Integrable (fun z : ℝ => z) mu := by
    apply ((integrable_const (1 : ℝ)).add h2).mono' measurable_id.aestronglyMeasurable
    filter_upwards [] with z
    change |z| ≤ 1 + z ^ 2
    nlinarith [sq_nonneg (|z| - 1), sq_abs z]
  have hi1 : Integrable (fun z : ℝ => z) nu := by
    apply (integrable_map_measure measurable_id.aestronglyMeasurable hscale.aemeasurable).2
    exact (h1.const_mul c).congr (ae_of_all mu (fun z => (heq z).symm))
  have hi2 : Integrable (fun z : ℝ => z ^ 2) nu := by
    apply (integrable_map_measure (by fun_prop) hscale.aemeasurable).2
    apply (h2.const_mul (c ^ 2)).congr
    exact ae_of_all mu (fun z => by change c ^ 2 * z ^ 2 = (z / b) ^ 2; rw [heq, mul_pow])
  have hnuMean : (∫ z : ℝ, z ∂nu) = 0 := by
    change (∫ z : ℝ, z ∂Measure.map (fun z : ℝ => z / b) mu) = 0
    rw [integral_map hscale.aemeasurable (f := fun z : ℝ => z) (by fun_prop)]
    simp_rw [heq]
    rw [integral_const_mul, hmean, mul_zero]
  have hnuSecond : (∫ z : ℝ, z ^ 2 ∂nu) =
      c ^ 2 * (∫ z : ℝ, z ^ 2 ∂mu) := by
    change (∫ z : ℝ, z ^ 2 ∂Measure.map (fun z : ℝ => z / b) mu) = _
    rw [integral_map hscale.aemeasurable (by fun_prop)]
    simp_rw [heq, mul_pow]
    exact integral_const_mul _ _
  have hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 := by
    rw [hnuSecond]
    dsimp [c, b]
    rw [inv_pow, mul_pow, hsigma2, hsn2]
    field_simp
  have hbpow : (b ^ (p : ℝ)) =
      (sigma ^ (p : ℝ)) * ((n : ℝ) ^ ((p / 2) : ℝ)) := by
    dsimp [b]
    rw [Real.mul_rpow hsigma.le hsn.le, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hN.le]
    congr 2
    ring
  have hpm : Measurable (fun z : ℝ => (|z| ^ (p : ℝ))) := by fun_prop
  have hppoint (z : ℝ) : (|z / b| ^ (p : ℝ)) =
      (|z| ^ (p : ℝ)) / ((sigma ^ (p : ℝ)) * ((n : ℝ) ^ ((p / 2) : ℝ))) := by
    rw [abs_div, abs_of_pos hb, Real.div_rpow (abs_nonneg z) hb.le, hbpow]
  have hip : Integrable (fun z : ℝ => (|z| ^ (p : ℝ))) nu := by
    apply (integrable_map_measure hpm.aestronglyMeasurable hscale.aemeasurable).2
    exact (hp.div_const _).congr (ae_of_all mu (fun z => (hppoint z).symm))
  have hnuP : (∫ z : ℝ, (|z| ^ (p : ℝ)) ∂nu) =
      (∫ z : ℝ, (|z| ^ (p : ℝ)) ∂mu) /
        ((sigma ^ (p : ℝ)) * ((n : ℝ) ^ ((p / 2) : ℝ))) := by
    change (∫ z : ℝ, (|z| ^ (p : ℝ)) ∂Measure.map (fun z : ℝ => z / b) mu) = _
    rw [integral_map hscale.aemeasurable hpm.aestronglyMeasurable]
    simp_rw [hppoint]
    exact integral_div _ _
  have hNpow : ((n : ℝ) ^ ((p / 2) : ℝ)) =
      ((n : ℝ) ^ (((p - 2) / 2) : ℝ)) * (n : ℝ) := by
    calc
      _ = (n : ℝ) ^ (((p - 2) / 2) + (1 : ℝ)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hN, Real.rpow_one]
  have hbeta : beta = (n : ℝ) * (∫ z : ℝ, (|z| ^ (p : ℝ)) ∂nu) := by
    rw [hnuP, hNpow]
    dsimp [beta]
    field_simp
  have hbetaPos : 0 < beta := by
    rw [hbeta]
    exact (original_moment_domain_coarse_guards p hp2 hp3 nu n hn hi2 hnorm hip).1
  have hmap : Measure.map (fun a : Shao.Path n =>
      (fun i : Fin n => a i / (sigma * Real.sqrt (n : ℝ)))) Praw = Pnorm :=
    Measure.pi_map_pi (fun _ : Fin n => hscale.aemeasurable)
  refine ⟨hsigma, hprob, hi2, hnuMean, hnorm, hip, hnuP, hbetaPos, hbeta, hmap, ?_⟩
  intro x s _hs
  have hT : Measurable (fun a : Shao.Path n => (fun i : Fin n => a i / b)) :=
    Measurable.of_eval (fun i => (measurable_pi_apply (X := fun _ : Fin n => ℝ) i).div_const b)
  have hsm : Measurable (fun a : Shao.Path n => s • a) :=
    Measurable.of_eval (fun i => measurable_const.mul (measurable_pi_apply i))
  have hE : MeasurableSet {v : Shao.Path n |
      x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn} :=
    measurableSet_le (Shao.measurable_energyWall x) ((Shao.measurable_upperMax hn).comp hsm)
  have hpre : (fun a : Shao.Path n => (fun i : Fin n => a i / b)) ⁻¹'
      {v : Shao.Path n | x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn} =
      {v : Shao.Path n | x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn} := by
    ext a
    have hTa : (fun i : Fin n => a i / b) = c • a := by
      funext i
      exact heq (a i)
    have hcomm : s • (c • a) = c • (s • a) := by
      funext i
      change s * (c * a i) = c * (s * a i)
      ring
    change (x * Real.sqrt (Shao.energy (fun i : Fin n => a i / b)) ≤
      Shao.upperMax (s • (fun i : Fin n => a i / b)) hn) ↔ _
    rw [hTa, hcomm, Shao.energy_smul, Real.sqrt_mul (sq_nonneg c),
      Real.sqrt_sq hc.le, Shao.upperMax_smul_of_nonneg c hc.le]
    rw [show x * (c * Real.sqrt (Shao.energy a)) =
      c * (x * Real.sqrt (Shao.energy a)) by ring]
    exact mul_le_mul_iff_right₀ hc
  change Pnorm.real {v : Shao.Path n |
    x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn} =
    Praw.real {v : Shao.Path n |
      x * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn}
  rw [← hmap]
  simp only [Measure.real_def]
  rw [Measure.map_apply hT hE, hpre]

end Shao.Probability
