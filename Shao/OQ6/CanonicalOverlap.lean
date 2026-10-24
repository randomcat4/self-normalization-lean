import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact moments for overlapping complete observations

The source is p39, lines117–135: the bridge from (9) to the edge-pair
classification preceding (10).  The shared law is literally
`ρ.prod (ρ.prod ρ)`; the disjoint law is literally
`(ρ.prod ρ).prod (ρ.prod ρ)`.  Genuine integrability is paid before
signed Fubini is used.  This module does not implement finite-sample
coordinate transport, edge counts, deletion, or the Shao–Zhou probability
engine, and preserves the p54 repairs.  The original roots remain open.
-/

set_option autoImplicit false

namespace Shao.OQ6.CanonicalOverlap

noncomputable section

open MeasureTheory

theorem shared_observation_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun p : Ω × Ω => r p.1 p.2))
    (hr2 : MemLp (fun p : Ω × Ω => r p.1 p.2) 2 (ρ.prod ρ)) :
    Measurable (fun x : Ω => ∫ y : Ω, r x y ∂ρ) ∧
      MemLp (fun x : Ω => ∫ y : Ω, r x y ∂ρ) 2 ρ ∧
      Integrable
        (fun t : Ω × (Ω × Ω) => r t.1 t.2.1 * r t.1 t.2.2)
        (ρ.prod (ρ.prod ρ)) ∧
      (∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
        ∂(ρ.prod (ρ.prod ρ))) =
        ∫ x : Ω, (∫ y : Ω, r x y ∂ρ) ^ 2 ∂ρ := by
  have hri : Integrable (fun p : Ω × Ω => r p.1 p.2) (ρ.prod ρ) :=
    hr2.integrable (by norm_num)
  have hsqi : Integrable (fun p : Ω × Ω => r p.1 p.2 ^ 2) (ρ.prod ρ) :=
    hr2.integrable_sq
  have hfm : Measurable (fun x : Ω => ∫ y : Ω, r x y ∂ρ) :=
    hr.stronglyMeasurable.integral_prod_right'.measurable
  have hQi : Integrable (fun x : Ω => ∫ y : Ω, r x y ^ 2 ∂ρ) ρ :=
    hsqi.integral_prod_left
  have hrows : ∀ᵐ x ∂ρ,
      Integrable (fun y : Ω => r x y) ρ ∧
        Integrable (fun y : Ω => r x y ^ 2) ρ :=
    hri.prod_right_ae.and hsqi.prod_right_ae

  -- Quadratic Jensen against the probability-space constant 1: expand
  -- the nonnegative centered square, only on the a.e. integrable rows.
  have hJensen : ∀ᵐ x ∂ρ,
      (∫ y : Ω, r x y ∂ρ) ^ 2 ≤ ∫ y : Ω, r x y ^ 2 ∂ρ := by
    filter_upwards [hrows] with x hx
    let c : ℝ := ∫ y : Ω, r x y ∂ρ
    have hc : (∫ _ : Ω, c ^ 2 ∂ρ) = c ^ 2 := by simp
    have hcenter : 0 ≤ ∫ y : Ω, (r x y - c) ^ 2 ∂ρ :=
      integral_nonneg (fun y : Ω => sq_nonneg (r x y - c))
    have hexpand :
        (∫ y : Ω, (r x y - c) ^ 2 ∂ρ) =
          (∫ y : Ω, r x y ^ 2 ∂ρ) - c ^ 2 := by
      calc
        _ = ∫ y : Ω, (r x y ^ 2 - (2 * c) * r x y) + c ^ 2 ∂ρ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun y : Ω => by ring)
        _ = ((∫ y : Ω, r x y ^ 2 ∂ρ) -
              (2 * c) * (∫ y : Ω, r x y ∂ρ)) + c ^ 2 := by
          rw [integral_add
            (f := fun y : Ω => r x y ^ 2 - (2 * c) * r x y)
            (g := fun _ : Ω => c ^ 2)
            (hx.2.sub (hx.1.const_mul (2 * c))) (integrable_const (c ^ 2)),
            integral_sub
              (f := fun y : Ω => r x y ^ 2)
              (g := fun y : Ω => (2 * c) * r x y)
              hx.2 (hx.1.const_mul (2 * c)),
            integral_const_mul, hc]
        _ = _ := by dsimp only [c]; ring
    change c ^ 2 ≤ ∫ y : Ω, r x y ^ 2 ∂ρ
    linarith [hexpand, hcenter]
  have hfSq : Integrable (fun x : Ω => (∫ y : Ω, r x y ∂ρ) ^ 2) ρ := by
    apply hQi.mono' (hfm.pow_const 2).aestronglyMeasurable
    filter_upwards [hJensen] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (∫ y : Ω, r x y ∂ρ))] using hx
  have hf2 : MemLp (fun x : Ω => ∫ y : Ω, r x y ∂ρ) 2 ρ :=
    (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mpr hfSq

  -- First lift the two genuine square-L1 budgets.  The unused coordinate
  -- has mass 1; no product of row energies or fourth moment is required.
  have hUm : Measurable (fun t : Ω × (Ω × Ω) => r t.1 t.2.1 ^ 2) :=
    (hr.comp (measurable_fst.prodMk measurable_snd.fst)).pow_const 2
  have hVm : Measurable (fun t : Ω × (Ω × Ω) => r t.1 t.2.2 ^ 2) :=
    (hr.comp (measurable_fst.prodMk measurable_snd.snd)).pow_const 2
  have hnormsq (a : ℝ) : ‖a ^ 2‖ = a ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a)]
  have hUnorm (x : Ω) :
      (∫ yz : Ω × Ω, ‖r x yz.1 ^ 2‖ ∂(ρ.prod ρ)) =
        ∫ y : Ω, r x y ^ 2 ∂ρ := by
    simp only [hnormsq]
    rw [integral_fun_fst (μ := ρ) (ν := ρ) (fun y : Ω => r x y ^ 2)]
    simp
  have hVnorm (x : Ω) :
      (∫ yz : Ω × Ω, ‖r x yz.2 ^ 2‖ ∂(ρ.prod ρ)) =
        ∫ z : Ω, r x z ^ 2 ∂ρ := by
    simp only [hnormsq]
    rw [integral_fun_snd (μ := ρ) (ν := ρ) (fun z : Ω => r x z ^ 2)]
    simp
  have hUi : Integrable
      (fun t : Ω × (Ω × Ω) => r t.1 t.2.1 ^ 2) (ρ.prod (ρ.prod ρ)) := by
    apply (integrable_prod_iff hUm.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [hsqi.prod_right_ae] with x hx
      exact hx.comp_fst ρ
    · simpa only [hUnorm] using hQi
  have hVi : Integrable
      (fun t : Ω × (Ω × Ω) => r t.1 t.2.2 ^ 2) (ρ.prod (ρ.prod ρ)) := by
    apply (integrable_prod_iff hVm.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [hsqi.prod_right_ae] with x hx
      exact hx.comp_snd ρ
    · simpa only [hVnorm] using hQi
  have hHm : Measurable
      (fun t : Ω × (Ω × Ω) => r t.1 t.2.1 * r t.1 t.2.2) :=
    (hr.comp (measurable_fst.prodMk measurable_snd.fst)).mul
      (hr.comp (measurable_fst.prodMk measurable_snd.snd))
  have hHi : Integrable
      (fun t : Ω × (Ω × Ω) => r t.1 t.2.1 * r t.1 t.2.2)
      (ρ.prod (ρ.prod ρ)) := by
    apply ((hUi.add hVi).div_const 2).mono' hHm.aestronglyMeasurable
    refine Filter.Eventually.of_forall (fun t : Ω × (Ω × Ω) => ?_)
    change ‖r t.1 t.2.1 * r t.1 t.2.2‖ ≤
      (r t.1 t.2.1 ^ 2 + r t.1 t.2.2 ^ 2) / 2
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|r t.1 t.2.1| - |r t.1 t.2.2|),
      sq_abs (r t.1 t.2.1), sq_abs (r t.1 t.2.2)]

  -- Factor only on the a.e. good rows, after paying their tensor L1.
  have hinner : ∀ᵐ x ∂ρ,
      (∫ yz : Ω × Ω, r x yz.1 * r x yz.2 ∂(ρ.prod ρ)) =
        (∫ y : Ω, r x y ∂ρ) ^ 2 := by
    filter_upwards [hri.prod_right_ae] with x hx
    have hrowProduct : Integrable
        (fun yz : Ω × Ω => r x yz.1 * r x yz.2) (ρ.prod ρ) :=
      hx.mul_prod hx
    rw [integral_prod (fun yz : Ω × Ω => r x yz.1 * r x yz.2) hrowProduct]
    simp only [integral_const_mul, integral_mul_const, pow_two]
  refine ⟨hfm, hf2, hHi, ?_⟩
  calc
    _ = ∫ x : Ω, (∫ yz : Ω × Ω, r x yz.1 * r x yz.2 ∂(ρ.prod ρ)) ∂ρ :=
      integral_prod
        (fun t : Ω × (Ω × Ω) => r t.1 t.2.1 * r t.1 t.2.2) hHi
    _ = _ := integral_congr_ae hinner

theorem disjoint_observation_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (r : Ω → Ω → ℝ)
    (hr1 : Integrable (fun p : Ω × Ω => r p.1 p.2) (ρ.prod ρ)) :
    Integrable
        (fun d : (Ω × Ω) × (Ω × Ω) =>
          r d.1.1 d.1.2 * r d.2.1 d.2.2)
        ((ρ.prod ρ).prod (ρ.prod ρ)) ∧
      (∫ d : (Ω × Ω) × (Ω × Ω),
          r d.1.1 d.1.2 * r d.2.1 d.2.2
        ∂((ρ.prod ρ).prod (ρ.prod ρ))) =
        (∫ p : Ω × Ω, r p.1 p.2 ∂(ρ.prod ρ)) ^ 2 := by
  have hJi : Integrable
      (fun d : (Ω × Ω) × (Ω × Ω) =>
        r d.1.1 d.1.2 * r d.2.1 d.2.2)
      ((ρ.prod ρ).prod (ρ.prod ρ)) :=
    hr1.mul_prod hr1
  refine ⟨hJi, ?_⟩
  calc
    _ = ∫ p : Ω × Ω, (∫ q : Ω × Ω,
          r p.1 p.2 * r q.1 q.2 ∂(ρ.prod ρ)) ∂(ρ.prod ρ) :=
      integral_prod
        (fun d : (Ω × Ω) × (Ω × Ω) =>
          r d.1.1 d.1.2 * r d.2.1 d.2.2) hJi
    _ = _ := by
      simp only [integral_const_mul, integral_mul_const, pow_two]

end

end Shao.OQ6.CanonicalOverlap
