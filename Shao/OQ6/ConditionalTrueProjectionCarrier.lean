import Shao.OQ6.ActualQuadraticTiltMoments
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Shao.OQ6.ConditionalTrueProjectionCarrier

noncomputable section

open MeasureTheory ProbabilityTheory

theorem actual_conditional_true_projection_carrier
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
    (R : ℝ) (hcutoff : 0 < μ.real {o : Ω | w o ≤ R})
    (lam : ℝ) (hLam : 0 ≤ lam ∧ lam ≤ 1) :
    let N : ℕ := Nat.ceil (2 / α)
    let Aexp : ℝ := (N.factorial : ℝ) / τ ^ N
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
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
    let rC : Ω → Ω → ℝ := fun o y => r o y - a o - a y + θ
    let K : Ω → Ω → ℝ := fun o y => H o y - q - G o - G y
    0 < Aexp ∧
      (∀ t : ℝ, 1 ≤ t → t ^ 2 ≤ Aexp * Real.exp (τ * Real.rpow t α)) ∧
      MeasurableSet C ∧
      d = 1 - π ∧ 0 < d ∧ 0 ≤ π ∧ π < 1 ∧
      IsProbabilityMeasure ν ∧
      ν ≪ μ ∧ (ν.prod ν) ≪ (μ.prod μ) ∧ ν C = 1 ∧
      (∀ A : Set Ω, MeasurableSet A → ν.real A = μ.real (A ∩ C) / d) ∧
      (∀ f : Ω → ℝ, Integrable f μ →
        Integrable f ν ∧ (∫ o, f o ∂ν) = (∫ o in C, f o ∂μ) / d) ∧
      MemLp w 2 μ ∧ MemLp w 2 ν ∧
      (∫ o, w o ^ 2 ∂ν) ≤ (∫ o, w o ^ 2 ∂μ) / d ∧
      Measurable a ∧ MemLp a 2 μ ∧ MemLp a 2 ν ∧
      (∀ᵐ o ∂μ, Integrable (r o) μ ∧ Integrable (r o) ν ∧
        a o = -(∫ y in Cᶜ, r o y ∂μ) / d ∧ |a o| ≤ c * w o) ∧
      θ = (∫ o, a o ∂ν) ∧
      θ = (∫ z in Cᶜ ×ˢ Cᶜ, r z.1 z.2 ∂(μ.prod μ)) / d ^ 2 ∧
      |θ| ≤ b ^ 2 / d ^ 2 ∧
      Measurable (fun z : Ω × Ω => H z.1 z.2) ∧
      MemLp (fun z : Ω × Ω => H z.1 z.2) 2 (ν.prod ν) ∧
      q = 2 * u + lam * θ ∧
      Measurable G ∧ MemLp G 2 ν ∧
      (∀ᵐ o ∂μ, Integrable (H o) ν ∧
        G o = g o - u + lam * (a o - θ)) ∧
      (∫ o, G o ∂ν) = 0 ∧
      Measurable (fun z : Ω × Ω => rC z.1 z.2) ∧
      MemLp (fun z : Ω × Ω => rC z.1 z.2) 2 (ν.prod ν) ∧
      (∀ o y, rC o y = rC y o) ∧
      (∀ᵐ o ∂ν, (∫ y, rC o y ∂ν) = 0) ∧
      MemLp (fun z : Ω × Ω => K z.1 z.2) 2 (ν.prod ν) ∧
      (∀ᵐ z : Ω × Ω ∂(ν.prod ν), K z.1 z.2 = lam * rC z.1 z.2) ∧
      (∀ᵐ o ∂ν, (∫ y, K o y ∂ν) = 0) ∧
      (∀ᵐ z : Ω × Ω ∂(μ.prod μ),
        |rC z.1 z.2| ≤ (w z.1 + c) * (w z.2 + c) ∧
        |lam * rC z.1 z.2| ≤ (1 + c) ^ 2 * w z.1 * w z.2) ∧
      (∀ᵐ z : Ω × Ω ∂(ν.prod ν), |K z.1 z.2| ≤ (R + c) ^ 2) := by
  classical
  dsimp only
  let N : ℕ := Nat.ceil (2 / α)
  let Aexp : ℝ := (N.factorial : ℝ) / τ ^ N
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
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
  let rC : Ω → Ω → ℝ := fun o y => r o y - a o - a y + θ
  let K : Ω → Ω → ℝ := fun o y => H o y - q - G o - G y

  -- Only the first eight public facts of qualified unit140 are consumed.
  have hsource :=
    Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
      μ h hh hh2 hhsymm hcenter hprojectionsecond
      3 (by norm_num) 0 (by norm_num) (by positivity)
  dsimp only at hsource
  rcases hsource with ⟨hgm, hg2, hgmean, hgsecond, hrm, hr2, hrsymm, hrcan, hsourceRest⟩
  clear hsourceRest
  change Measurable g at hgm
  change MemLp g 2 μ at hg2
  change (∫ o, g o ∂μ) = 0 at hgmean
  change (∫ o, g o ^ 2 ∂μ) = 1 at hgsecond
  change Measurable (fun z : Ω × Ω => r z.1 z.2) at hrm
  change MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ) at hr2
  change (∀ o y, r o y = r y o) at hrsymm
  change (∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0) at hrcan
  have hg1 : Integrable g μ := hg2.integrable (by norm_num)
  have hr1 : Integrable (fun z : Ω × Ω => r z.1 z.2) (μ.prod μ) :=
    hr2.integrable (by norm_num)

  -- The original stretched exponential assumption actually pays for L2(w).
  have hfactorial : 0 < (N.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos N
  have htauN : 0 < τ ^ N := pow_pos hτ N
  have hAexp : 0 < Aexp := div_pos hfactorial htauN
  have halphaN : 2 ≤ α * (N : ℝ) := by
    have hceil : 2 / α ≤ (N : ℝ) := Nat.le_ceil (2 / α)
    have hmul := (div_le_iff₀ hα).1 hceil
    nlinarith
  have hdom : ∀ t : ℝ, 1 ≤ t →
      t ^ 2 ≤ Aexp * Real.exp (τ * Real.rpow t α) := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith
    have hrpow0 : 0 ≤ Real.rpow t α := Real.rpow_nonneg ht0 α
    have hterm := Real.pow_div_factorial_le_exp
      (τ * Real.rpow t α) (mul_nonneg hτ.le hrpow0) N
    have hpow : t ^ 2 ≤ (Real.rpow t α) ^ N := by
      calc
        t ^ 2 = Real.rpow t (2 : ℝ) := (Real.rpow_natCast t 2).symm
        _ ≤ Real.rpow t (α * (N : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le ht halphaN
        _ = (Real.rpow t α) ^ N := by
          exact (Real.rpow_mul ht0 α (N : ℝ)).trans (Real.rpow_natCast (Real.rpow t α) N)
    have hterm' : τ ^ N * (Real.rpow t α) ^ N ≤
        Real.exp (τ * Real.rpow t α) * (N.factorial : ℝ) := by
      apply (div_le_iff₀ hfactorial).1
      simpa only [mul_pow] using hterm
    calc
      t ^ 2 ≤ (Real.rpow t α) ^ N := hpow
      _ ≤ Real.exp (τ * Real.rpow t α) * (N.factorial : ℝ) / τ ^ N := by
        apply (le_div_iff₀ htauN).2
        simpa only [mul_comm] using hterm'
      _ = Aexp * Real.exp (τ * Real.rpow t α) := by
        dsimp only [Aexp]
        ring
  have hwSq : Integrable (fun o => w o ^ 2) μ := by
    apply (hwexp.const_mul Aexp).mono' (hw.pow_const 2).aestronglyMeasurable
    filter_upwards [hwone] with o ho
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hdom (w o) ho
  have hw2 : MemLp w 2 μ :=
    (memLp_two_iff_integrable_sq hw.aestronglyMeasurable).2 hwSq
  have hw1 : Integrable w μ := hw2.integrable (by norm_num)
  have hw0 : ∀ᵐ o ∂μ, 0 ≤ w o := hwone.mono (fun _ ho => by linarith)

  -- The genuine conditional measure is a normalized restriction of this μ.
  have hC : MeasurableSet C := measurableSet_le hw measurable_const
  have hd : 0 < d := hcutoff
  have hCzero : μ C ≠ 0 := by
    intro hz
    have hd' := hd
    simp only [d, Measure.real, hz, ENNReal.toReal_zero] at hd'
    exact (lt_irrefl 0) hd'
  have hCfinite : μ C ≠ ⊤ := measure_ne_top μ C
  have hinvfinite : (μ C)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hCzero
  have hνprob : IsProbabilityMeasure ν := by
    change IsProbabilityMeasure (ProbabilityTheory.cond μ C)
    exact ProbabilityTheory.cond_isProbabilityMeasure hCzero
  haveI : IsProbabilityMeasure ν := hνprob
  have hνac : ν ≪ μ := by
    change ProbabilityTheory.cond μ C ≪ μ
    exact ProbabilityTheory.cond_absolutelyContinuous
  have hνprodac : (ν.prod ν) ≪ (μ.prod μ) := hνac.prod hνac
  have hνC : ν C = 1 := by
    change ((μ C)⁻¹ • μ.restrict C) C = 1
    rw [Measure.smul_apply, Measure.restrict_apply_self, smul_eq_mul,
      ENNReal.inv_mul_cancel hCzero hCfinite]
  have hdpi : d = 1 - π := by
    have hcompl := measureReal_compl (μ := μ) hC
    simp only [probReal_univ] at hcompl
    change π = 1 - d at hcompl
    linarith
  have hπ0 : 0 ≤ π := measureReal_nonneg
  have hπlt : π < 1 := by linarith
  have hνmass : ∀ A : Set Ω, MeasurableSet A →
      ν.real A = μ.real (A ∩ C) / d := by
    intro A hA
    change (((μ C)⁻¹ • μ.restrict C) A).toReal =
      (μ (A ∩ C)).toReal / (μ C).toReal
    rw [Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul,
      ENNReal.toReal_mul, ENNReal.toReal_inv]
    ring
  have hνint : ∀ f : Ω → ℝ, Integrable f μ →
      Integrable f ν ∧ (∫ o, f o ∂ν) = (∫ o in C, f o ∂μ) / d := by
    intro f hf
    refine ⟨hf.restrict.smul_measure hinvfinite, ?_⟩
    change (∫ o, f o ∂((μ C)⁻¹ • μ.restrict C)) = _
    rw [integral_smul_measure, ENNReal.toReal_inv]
    change (μ C).toReal⁻¹ * (∫ o in C, f o ∂μ) =
      (∫ o in C, f o ∂μ) / (μ C).toReal
    ring
  have hνL2 : ∀ f : Ω → ℝ, Measurable f → MemLp f 2 μ → MemLp f 2 ν := by
    intro f hf hf2
    exact (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2
      (hνint (fun o => f o ^ 2) hf2.integrable_sq).1
  have hwν2 : MemLp w 2 ν := hνL2 w hw hw2
  have hwνSecond : (∫ o, w o ^ 2 ∂ν) ≤ (∫ o, w o ^ 2 ∂μ) / d := by
    rw [(hνint (fun o => w o ^ 2) hwSq).2]
    have hsplit := integral_add_compl hC hwSq
    have hnonneg : 0 ≤ ∫ o in Cᶜ, w o ^ 2 ∂μ :=
      integral_nonneg (fun o => sq_nonneg (w o))
    exact div_le_div_of_nonneg_right (by linarith) hd.le
  have hgν2 : MemLp g 2 ν := hνL2 g hgm hg2
  have hgν1 : Integrable g ν := hgν2.integrable (by norm_num)
  have hνprod : ν.prod ν =
      ((μ C)⁻¹ * (μ C)⁻¹) • (μ.prod μ).restrict (C ×ˢ C) := by
    dsimp only [ν]
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      Measure.prod_restrict]
  have hrν2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (ν.prod ν) := by
    apply (memLp_two_iff_integrable_sq hrm.aestronglyMeasurable).2
    rw [hνprod]
    exact hr2.integrable_sq.restrict.smul_measure
      (ENNReal.mul_ne_top hinvfinite hinvfinite)
  have hrν1 : Integrable (fun z : Ω × Ω => r z.1 z.2) (ν.prod ν) :=
    hrν2.integrable (by norm_num)
  have hrνIntegral : (∫ z : Ω × Ω, r z.1 z.2 ∂(ν.prod ν)) =
      (∫ z in C ×ˢ C, r z.1 z.2 ∂(μ.prod μ)) / d ^ 2 := by
    rw [hνprod, integral_smul_measure]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, smul_eq_mul]
    change ((μ C).toReal⁻¹ * (μ C).toReal⁻¹) *
      (∫ z in C ×ˢ C, r z.1 z.2 ∂(μ.prod μ)) =
      (∫ z in C ×ˢ C, r z.1 z.2 ∂(μ.prod μ)) / (μ C).toReal ^ 2
    simp only [div_eq_mul_inv, inv_pow, pow_two]
    ring
  have hb0 : 0 ≤ b := integral_nonneg_of_ae (ae_restrict_of_ae hw0)
  have hc0 : 0 ≤ c := div_nonneg hb0 hd.le

  -- Source degeneracy and envelope supply AE rows, never every observation.
  have henv : ∀ᵐ z : Ω × Ω ∂(μ.prod μ), |r z.1 z.2| ≤ w z.1 * w z.2 :=
    henvelope
  have henvRows := Measure.ae_ae_of_ae_prod henv
  have hrows : ∀ᵐ o ∂μ, Integrable (r o) μ ∧ Integrable (r o) ν ∧
      a o = -(∫ y in Cᶜ, r o y ∂μ) / d ∧ |a o| ≤ c * w o := by
    filter_upwards [hr1.prod_right_ae, hrcan, henvRows, hw0]
      with o hrow hcan hrowenv hwo
    have hrowν : Integrable (r o) ν := (hνint (r o) hrow).1
    have hsplit := integral_add_compl hC hrow
    have hgoodtail : (∫ y in C, r o y ∂μ) = -(∫ y in Cᶜ, r o y ∂μ) := by
      rw [hcan] at hsplit
      linarith
    have hat : a o = -(∫ y in Cᶜ, r o y ∂μ) / d := by
      change (∫ y, r o y ∂ν) = _
      rw [(hνint (r o) hrow).2, hgoodtail]
    have htailBound : |∫ y in Cᶜ, r o y ∂μ| ≤ w o * b := by
      calc
        |∫ y in Cᶜ, r o y ∂μ| ≤ ∫ y in Cᶜ, |r o y| ∂μ := by
          simpa only [Real.norm_eq_abs] using
            (norm_integral_le_integral_norm (μ := μ.restrict Cᶜ) (r o))
        _ ≤ ∫ y in Cᶜ, w o * w y ∂μ := by
          apply integral_mono_ae
            (by simpa only [Real.norm_eq_abs] using hrow.norm.restrict)
            (hw1.const_mul (w o)).restrict
          exact ae_restrict_of_ae hrowenv
        _ = w o * b := by rw [integral_const_mul]
    refine ⟨hrow, hrowν, hat, ?_⟩
    rw [hat, abs_div, abs_neg, abs_of_pos hd]
    calc
      |∫ y in Cᶜ, r o y ∂μ| / d ≤ (w o * b) / d :=
        div_le_div_of_nonneg_right htailBound hd.le
      _ = c * w o := by dsimp only [c]; ring
  have ham : Measurable a := hrm.stronglyMeasurable.integral_prod_right'.measurable
  have haSq : Integrable (fun o => a o ^ 2) μ := by
    apply (hwSq.const_mul (c ^ 2)).mono' (ham.pow_const 2).aestronglyMeasurable
    filter_upwards [hrows, hw0] with o ho hwo
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hs := (sq_le_sq₀ (abs_nonneg (a o)) (mul_nonneg hc0 hwo)).2 ho.2.2.2
    simpa only [sq_abs, mul_pow] using hs
  have ha2 : MemLp a 2 μ :=
    (memLp_two_iff_integrable_sq ham.aestronglyMeasurable).2 haSq
  have haν2 : MemLp a 2 ν := hνL2 a ham ha2
  have haν1 : Integrable a ν := haν2.integrable (by norm_num)
  have hθmean : θ = (∫ o, a o ∂ν) := integral_prod _ hrν1

  -- Exact rectangle cancellations pay the double-tail identity.
  have hrectInt : ∀ A B : Set Ω,
      Integrable (fun z : Ω × Ω => r z.1 z.2)
        ((μ.restrict A).prod (μ.restrict B)) := by
    intro A B
    rw [Measure.prod_restrict]
    exact hr1.restrict
  have hrect : ∀ A B : Set Ω,
      (∫ z in A ×ˢ B, r z.1 z.2 ∂(μ.prod μ)) =
        ∫ o in A, ∫ y in B, r o y ∂μ ∂μ := by
    intro A B
    exact setIntegral_prod _ hr1.restrict
  have hrectSymm : ∀ A B : Set Ω,
      (∫ z in A ×ˢ B, r z.1 z.2 ∂(μ.prod μ)) =
        ∫ z in B ×ˢ A, r z.1 z.2 ∂(μ.prod μ) := by
    intro A B
    calc
      _ = ∫ z : Ω × Ω, r z.1 z.2 ∂((μ.restrict A).prod (μ.restrict B)) := by
        rw [Measure.prod_restrict]
      _ = ∫ y in B, ∫ o in A, r o y ∂μ ∂μ := integral_prod_symm _ (hrectInt A B)
      _ = ∫ y in B, ∫ o in A, r y o ∂μ ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => integral_congr_ae
          (Filter.Eventually.of_forall fun o => hrsymm o y)
      _ = _ := (hrect B A).symm
  have hrectSum : ∀ A B : Set Ω, MeasurableSet B →
      (∫ z in A ×ˢ B, r z.1 z.2 ∂(μ.prod μ)) +
        (∫ z in A ×ˢ Bᶜ, r z.1 z.2 ∂(μ.prod μ)) = 0 := by
    intro A B hB
    rw [hrect A B, hrect A Bᶜ,
      ← integral_add (hrectInt A B).integral_prod_left
        (hrectInt A Bᶜ).integral_prod_left]
    calc
      _ = ∫ o in A, ∫ y, r o y ∂μ ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hr1.prod_right_ae] with o ho
        exact integral_add_compl hB ho
      _ = 0 := integral_eq_zero_of_ae (ae_restrict_of_ae hrcan)
  have hCCDD : (∫ z in C ×ˢ C, r z.1 z.2 ∂(μ.prod μ)) =
      ∫ z in Cᶜ ×ˢ Cᶜ, r z.1 z.2 ∂(μ.prod μ) := by
    have h1 := hrectSum C C hC
    have h2 := hrectSum Cᶜ C hC
    have h3 := hrectSymm C Cᶜ
    linarith
  have hθtail : θ =
      (∫ z in Cᶜ ×ˢ Cᶜ, r z.1 z.2 ∂(μ.prod μ)) / d ^ 2 := by
    change (∫ z : Ω × Ω, r z.1 z.2 ∂(ν.prod ν)) = _
    rw [hrνIntegral, hCCDD]
  have hθbound : |θ| ≤ b ^ 2 / d ^ 2 := by
    have hww : Integrable (fun z : Ω × Ω => w z.1 * w z.2)
        ((μ.prod μ).restrict (Cᶜ ×ˢ Cᶜ)) := by
      rw [← Measure.prod_restrict]
      exact hw1.restrict.mul_prod hw1.restrict
    have htail : |∫ z in Cᶜ ×ˢ Cᶜ, r z.1 z.2 ∂(μ.prod μ)| ≤ b ^ 2 := by
      calc
        _ ≤ ∫ z in Cᶜ ×ˢ Cᶜ, |r z.1 z.2| ∂(μ.prod μ) := by
          simpa only [Real.norm_eq_abs] using
            (norm_integral_le_integral_norm
              (μ := (μ.prod μ).restrict (Cᶜ ×ˢ Cᶜ))
              (fun z : Ω × Ω => r z.1 z.2))
        _ ≤ ∫ z in Cᶜ ×ˢ Cᶜ, w z.1 * w z.2 ∂(μ.prod μ) := by
          apply integral_mono_ae
            (by simpa only [Real.norm_eq_abs] using hr1.norm.restrict) hww
          exact ae_restrict_of_ae henv
        _ = b ^ 2 := by
          rw [← Measure.prod_restrict, integral_prod_mul]
          change b * b = b ^ 2
          ring
    rw [hθtail, abs_div, abs_of_nonneg (sq_nonneg d)]
    exact div_le_div_of_nonneg_right htail (sq_nonneg d)
  have hθc : |θ| ≤ c ^ 2 := by
    simpa only [c, div_pow] using hθbound

  -- H, q and G are actual integrals under ν, not agreeing input data.
  have hHm : Measurable (fun z : Ω × Ω => H z.1 z.2) :=
    ((hgm.comp measurable_fst).add (hgm.comp measurable_snd)).add
      (measurable_const.mul hrm)
  have hH2 : MemLp (fun z : Ω × Ω => H z.1 z.2) 2 (ν.prod ν) :=
    ((hgν2.comp_fst ν).add (hgν2.comp_snd ν)).add (hrν2.const_mul lam)
  have hH1 : Integrable (fun z : Ω × Ω => H z.1 z.2) (ν.prod ν) :=
    hH2.integrable (by norm_num)
  have hgf : Integrable (fun z : Ω × Ω => g z.1) (ν.prod ν) :=
    (hgν2.comp_fst ν).integrable (by norm_num)
  have hgs : Integrable (fun z : Ω × Ω => g z.2) (ν.prod ν) :=
    (hgν2.comp_snd ν).integrable (by norm_num)
  have hgfmean : (∫ z : Ω × Ω, g z.1 ∂(ν.prod ν)) = u := by
    rw [integral_prod _ hgf]
    simpa only [integral_const, probReal_univ, one_smul] using
      (show (∫ o, g o ∂ν) = u from rfl)
  have hgsmean : (∫ z : Ω × Ω, g z.2 ∂(ν.prod ν)) = u := by
    rw [integral_prod _ hgs]
    change (∫ _ : Ω, u ∂ν) = u
    rw [integral_const, probReal_univ, one_smul]
  have hq : q = 2 * u + lam * θ := by
    change (∫ z : Ω × Ω, g z.1 + g z.2 + lam * r z.1 z.2 ∂(ν.prod ν)) = _
    have hpair : (∫ z : Ω × Ω, g z.1 + g z.2 ∂(ν.prod ν)) = 2 * u := by
      calc
        _ = (∫ z : Ω × Ω, g z.1 ∂(ν.prod ν)) +
            (∫ z : Ω × Ω, g z.2 ∂(ν.prod ν)) :=
          integral_add (f := fun z : Ω × Ω => g z.1)
            (g := fun z : Ω × Ω => g z.2) hgf hgs
        _ = 2 * u := by rw [hgfmean, hgsmean]; ring
    have hscale : (∫ z : Ω × Ω, lam * r z.1 z.2 ∂(ν.prod ν)) = lam * θ :=
      integral_const_mul lam (fun z : Ω × Ω => r z.1 z.2)
    calc
      _ = (∫ z : Ω × Ω, g z.1 + g z.2 ∂(ν.prod ν)) +
          (∫ z : Ω × Ω, lam * r z.1 z.2 ∂(ν.prod ν)) :=
        integral_add (f := fun z : Ω × Ω => g z.1 + g z.2)
          (g := fun z : Ω × Ω => lam * r z.1 z.2)
          (hgf.add hgs) (hrν1.const_mul lam)
      _ = 2 * u + lam * θ := by rw [hpair, hscale]
  have hGm : Measurable G :=
    (hHm.stronglyMeasurable.integral_prod_right'.measurable).sub measurable_const
  have hHrows : ∀ᵐ o ∂μ, Integrable (H o) ν ∧
      G o = g o - u + lam * (a o - θ) := by
    filter_upwards [hrows] with o ho
    have hrow : Integrable (H o) ν :=
      ((integrable_const (g o)).add hgν1).add (ho.2.1.const_mul lam)
    refine ⟨hrow, ?_⟩
    have hconst : (∫ _ : Ω, g o ∂ν) = g o := by
      rw [integral_const, probReal_univ, one_smul]
    have hpair : (∫ y, g o + g y ∂ν) = g o + u := by
      calc
        _ = (∫ _ : Ω, g o ∂ν) + (∫ y, g y ∂ν) :=
          integral_add (f := fun _ : Ω => g o) (g := g)
            (integrable_const (g o)) hgν1
        _ = g o + u := by rw [hconst]
    have hscale : (∫ y, lam * r o y ∂ν) = lam * a o :=
      integral_const_mul lam (r o)
    have hsum : (∫ y, g o + g y + lam * r o y ∂ν) = g o + u + lam * a o := by
      calc
        _ = (∫ y, g o + g y ∂ν) + (∫ y, lam * r o y ∂ν) :=
          integral_add (f := fun y => g o + g y) (g := fun y => lam * r o y)
            ((integrable_const (g o)).add hgν1) (ho.2.1.const_mul lam)
        _ = g o + u + lam * a o := by rw [hpair, hscale]
    change (∫ y, g o + g y + lam * r o y ∂ν) - q = _
    rw [hsum, hq]
    ring
  have hGformula : G =ᵐ[ν] (fun o => g o - u + lam * (a o - θ)) :=
    Filter.Eventually.mono (hνac.ae_le hHrows) (fun _ ho => ho.2)
  have hG2 : MemLp G 2 ν := by
    have hformula2 : MemLp (fun o => g o - u + lam * (a o - θ)) 2 ν :=
      (hgν2.sub (memLp_const u)).add ((haν2.sub (memLp_const θ)).const_mul lam)
    exact (MeasureTheory.memLp_congr_ae hGformula).2 hformula2
  have hGmean : (∫ o, G o ∂ν) = 0 := by
    change (∫ o, (∫ y, H o y ∂ν) - q ∂ν) = 0
    rw [integral_sub hH1.integral_prod_left (integrable_const q),
      ← integral_prod _ hH1, integral_const, probReal_univ, one_smul]
    change q - q = 0
    ring

  -- The actual centered residual and the source formula agree only AE.
  have hrCm : Measurable (fun z : Ω × Ω => rC z.1 z.2) :=
    ((hrm.sub (ham.comp measurable_fst)).sub (ham.comp measurable_snd)).add
      measurable_const
  have hrC2 : MemLp (fun z : Ω × Ω => rC z.1 z.2) 2 (ν.prod ν) :=
    ((hrν2.sub (haν2.comp_fst ν)).sub (haν2.comp_snd ν)).add (memLp_const θ)
  have hrCsymm : ∀ o y, rC o y = rC y o := by
    intro o y
    dsimp only [rC]
    rw [hrsymm o y]
    ring
  have hrCcan : ∀ᵐ o ∂ν, (∫ y, rC o y ∂ν) = 0 := by
    filter_upwards [hνac.ae_le hrows] with o ho
    have hconsta : (∫ _ : Ω, a o ∂ν) = a o := by
      rw [integral_const, probReal_univ, one_smul]
    have hconstθ : (∫ _ : Ω, θ ∂ν) = θ := by
      rw [integral_const, probReal_univ, one_smul]
    have hsub1 : (∫ y, r o y - a o ∂ν) = a o - a o := by
      calc
        _ = (∫ y, r o y ∂ν) - (∫ _ : Ω, a o ∂ν) :=
          integral_sub (f := r o) (g := fun _ : Ω => a o)
            ho.2.1 (integrable_const (a o))
        _ = a o - a o := by rw [hconsta]
    have hsub2 : (∫ y, r o y - a o - a y ∂ν) = a o - a o - θ := by
      calc
        _ = (∫ y, r o y - a o ∂ν) - (∫ y, a y ∂ν) :=
          integral_sub (f := fun y => r o y - a o) (g := a)
            (ho.2.1.sub (integrable_const (a o))) haν1
        _ = a o - a o - θ := by rw [hsub1, ← hθmean]
    change (∫ y, r o y - a o - a y + θ ∂ν) = 0
    calc
      _ = (∫ y, r o y - a o - a y ∂ν) + (∫ _ : Ω, θ ∂ν) :=
        integral_add (f := fun y => r o y - a o - a y) (g := fun _ : Ω => θ)
          ((ho.2.1.sub (integrable_const (a o))).sub haν1) (integrable_const θ)
      _ = (a o - a o - θ) + θ := by rw [hsub2, hconstθ]
      _ = 0 := by ring
  have hK2 : MemLp (fun z : Ω × Ω => K z.1 z.2) 2 (ν.prod ν) :=
    ((hH2.sub (memLp_const q)).sub (hG2.comp_fst ν)).sub (hG2.comp_snd ν)
  have hKagree : ∀ᵐ z : Ω × Ω ∂(ν.prod ν), K z.1 z.2 = lam * rC z.1 z.2 := by
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hGformula,
      measurePreserving_snd.quasiMeasurePreserving.ae hGformula] with z hz1 hz2
    change H z.1 z.2 - q - G z.1 - G z.2 = lam * rC z.1 z.2
    rw [hz1, hz2, hq]
    dsimp only [H, rC]
    ring
  have hKcan : ∀ᵐ o ∂ν, (∫ y, K o y ∂ν) = 0 := by
    filter_upwards [Measure.ae_ae_of_ae_prod hKagree, hrCcan] with o ho hcan
    calc
      (∫ y, K o y ∂ν) = ∫ y, lam * rC o y ∂ν := integral_congr_ae ho
      _ = lam * ∫ y, rC o y ∂ν := integral_const_mul _ _
      _ = 0 := by rw [hcan, mul_zero]

  have hcanonicalEnvelope : ∀ᵐ z : Ω × Ω ∂(μ.prod μ),
      |rC z.1 z.2| ≤ (w z.1 + c) * (w z.2 + c) ∧
        |lam * rC z.1 z.2| ≤ (1 + c) ^ 2 * w z.1 * w z.2 := by
    filter_upwards [henv,
      measurePreserving_fst.quasiMeasurePreserving.ae hrows,
      measurePreserving_snd.quasiMeasurePreserving.ae hrows,
      measurePreserving_fst.quasiMeasurePreserving.ae hwone,
      measurePreserving_snd.quasiMeasurePreserving.ae hwone]
      with z hz hz1 hz2 hwz1 hwz2
    have hwz10 : 0 ≤ w z.1 := by linarith
    have hwz20 : 0 ≤ w z.2 := by linarith
    have hrc : |rC z.1 z.2| ≤ (w z.1 + c) * (w z.2 + c) := by
      calc
        |rC z.1 z.2| ≤ |r z.1 z.2 - a z.1 - a z.2| + |θ| := abs_add_le _ _
        _ ≤ (|r z.1 z.2 - a z.1| + |a z.2|) + |θ| :=
          add_le_add (abs_sub (r z.1 z.2 - a z.1) (a z.2)) (le_refl |θ|)
        _ ≤ ((|r z.1 z.2| + |a z.1|) + |a z.2|) + |θ| :=
          add_le_add (add_le_add (abs_sub (r z.1 z.2) (a z.1))
            (le_refl |a z.2|)) (le_refl |θ|)
        _ ≤ ((w z.1 * w z.2 + c * w z.1) + c * w z.2) + c ^ 2 :=
          add_le_add (add_le_add (add_le_add hz hz1.2.2.2) hz2.2.2.2) hθc
        _ = (w z.1 + c) * (w z.2 + c) := by ring
    have hLamabs : |lam| ≤ 1 := by rw [abs_of_nonneg hLam.1]; exact hLam.2
    have hp0 : 0 ≤ (w z.1 + c) * (w z.2 + c) :=
      mul_nonneg (add_nonneg hwz10 hc0) (add_nonneg hwz20 hc0)
    have hwc1 : w z.1 + c ≤ (1 + c) * w z.1 := by
      nlinarith only [mul_nonneg hc0 (sub_nonneg.mpr hwz1)]
    have hwc2 : w z.2 + c ≤ (1 + c) * w z.2 := by
      nlinarith only [mul_nonneg hc0 (sub_nonneg.mpr hwz2)]
    refine ⟨hrc, ?_⟩
    calc
      |lam * rC z.1 z.2| = |lam| * |rC z.1 z.2| := abs_mul _ _
      _ ≤ |lam| * ((w z.1 + c) * (w z.2 + c)) :=
        mul_le_mul_of_nonneg_left hrc (abs_nonneg lam)
      _ ≤ 1 * ((w z.1 + c) * (w z.2 + c)) :=
        mul_le_mul_of_nonneg_right hLamabs hp0
      _ ≤ ((1 + c) * w z.1) * ((1 + c) * w z.2) := by
        rw [one_mul]
        exact mul_le_mul hwc1 hwc2 (add_nonneg hwz20 hc0)
          (mul_nonneg (by linarith only [hc0]) hwz10)
      _ = (1 + c) ^ 2 * w z.1 * w z.2 := by ring
  have hνsupport : ∀ᵐ o ∂ν, w o ≤ R := by
    change ∀ᵐ o ∂ProbabilityTheory.cond μ C, o ∈ C
    exact ProbabilityTheory.ae_cond_mem hC
  have hwν0 : ∀ᵐ o ∂ν, 0 ≤ w o := hνac.ae_le hw0
  have hKbound : ∀ᵐ z : Ω × Ω ∂(ν.prod ν), |K z.1 z.2| ≤ (R + c) ^ 2 := by
    filter_upwards [hKagree, hνprodac.ae_le hcanonicalEnvelope,
      measurePreserving_fst.quasiMeasurePreserving.ae hνsupport,
      measurePreserving_snd.quasiMeasurePreserving.ae hνsupport,
      measurePreserving_fst.quasiMeasurePreserving.ae hwν0,
      measurePreserving_snd.quasiMeasurePreserving.ae hwν0]
      with z hz henvz hs1 hs2 hwz1 hwz2
    have hLamabs : |lam| ≤ 1 := by rw [abs_of_nonneg hLam.1]; exact hLam.2
    have hp0 : 0 ≤ (w z.1 + c) * (w z.2 + c) :=
      mul_nonneg (add_nonneg hwz1 hc0) (add_nonneg hwz2 hc0)
    calc
      |K z.1 z.2| = |lam| * |rC z.1 z.2| := by rw [hz, abs_mul]
      _ ≤ |lam| * ((w z.1 + c) * (w z.2 + c)) :=
        mul_le_mul_of_nonneg_left henvz.1 (abs_nonneg lam)
      _ ≤ 1 * ((w z.1 + c) * (w z.2 + c)) :=
        mul_le_mul_of_nonneg_right hLamabs hp0
      _ ≤ (R + c) * (R + c) := by
        rw [one_mul]
        exact mul_le_mul (add_le_add hs1 (le_refl c)) (add_le_add hs2 (le_refl c))
          (add_nonneg hwz2 hc0) (by linarith only [hwz1, hs1, hc0])
      _ = (R + c) ^ 2 := by ring

  exact ⟨hAexp, hdom, hC, hdpi, hd, hπ0, hπlt, hνprob,
    hνac, hνprodac, hνC, hνmass, hνint, hw2, hwν2, hwνSecond,
    ham, ha2, haν2, hrows, hθmean, hθtail, hθbound,
    hHm, hH2, hq, hGm, hG2, hHrows, hGmean,
    hrCm, hrC2, hrCsymm, hrCcan, hK2, hKagree, hKcan,
    hcanonicalEnvelope, hKbound⟩
end

end Shao.OQ6.ConditionalTrueProjectionCarrier
