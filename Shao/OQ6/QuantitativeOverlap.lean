import Shao.OQ6.CanonicalTilt
import Shao.OQ6.CanonicalOverlap
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quantitative moments for tilted overlapping observations

The source is p39(9) to the edge-pair classification preceding (10).
The shared law is literally `ρ.prod (ρ.prod ρ)`; the disjoint law is
literally `(ρ.prod ρ).prod (ρ.prod ρ)`.  The original-law good rows are
transported only almost everywhere by genuine absolute continuity.
The nonsymmetric pair-L2 lift below pays the shared theorem's product
integrability without a symmetry premise.  Finite-sample transport,
orientation, counts, deletion and source probability costs remain separate.
Shao–Zhou attribution, the p54 repairs and the partial-tilt inverse
normalizer are retained.  The original roots remain open.
-/

set_option autoImplicit false

namespace Shao.OQ6.QuantitativeOverlap

noncomputable section

open MeasureTheory

private theorem qo_tilted_pair_l2
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun z : Ω × Ω => r z.1 z.2))
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ))
    (L : Ω → ℝ) (hL : Measurable L) (K : ℝ)
    (hLnonneg : ∀ o, 0 ≤ L o)
    (hLle : ∀ o, L o ≤ K)
    (hLmass : (∫ o, L o ∂μ) = 1) :
    let ρ : Measure Ω :=
      μ.withDensity (fun o => ENNReal.ofReal (L o))
    IsProbabilityMeasure ρ ∧
      MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (ρ.prod ρ) := by
  dsimp only
  let ρ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
  have hLi : Integrable L μ :=
    Integrable.of_bound hL.aestronglyMeasurable K
      (Filter.Eventually.of_forall fun o => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hLnonneg o)] using hLle o)
  have hK : 1 ≤ K := by
    have h := integral_mono hLi (integrable_const K) hLle
    simpa only [hLmass, integral_const, probReal_univ, one_smul] using h
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hρprob : IsProbabilityMeasure ρ := by
    constructor
    change (μ.withDensity (fun o => ENNReal.ofReal (L o))) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hLi
        (Filter.Eventually.of_forall hLnonneg), hLmass]
    exact ENNReal.ofReal_one
  let W : Ω × Ω → ℝ := fun z => L z.1 * L z.2
  have hWm : Measurable W :=
    (hL.comp measurable_fst).mul (hL.comp measurable_snd)
  have hWnonneg (z : Ω × Ω) : 0 ≤ W z :=
    mul_nonneg (hLnonneg z.1) (hLnonneg z.2)
  have hWbound (z : Ω × Ω) : W z ≤ K ^ 2 := by
    simpa only [W, pow_two] using
      mul_le_mul (hLle z.1) (hLle z.2) (hLnonneg z.2) hK0
  have hρpair : ρ.prod ρ = (μ.prod μ).withDensity
      (fun z : Ω × Ω => ENNReal.ofReal (W z)) := by
    dsimp only [ρ]
    rw [prod_withDensity hL.ennreal_ofReal hL.ennreal_ofReal]
    congr 1
    funext z
    change ENNReal.ofReal (L z.1) * ENNReal.ofReal (L z.2) =
      ENNReal.ofReal (L z.1 * L z.2)
    rw [ENNReal.ofReal_mul (hLnonneg z.1)]
  have hpairSquare : Integrable
      (fun z : Ω × Ω => r z.1 z.2 ^ 2) (ρ.prod ρ) := by
    rw [hρpair]
    apply (integrable_withDensity_iff hWm.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).2
    have hweighted : Integrable
        (fun z : Ω × Ω => r z.1 z.2 ^ 2 * W z) (μ.prod μ) :=
      hr2.integrable_sq.mul_bdd (g := W) hWm.aestronglyMeasurable
        (c := K ^ 2) (Filter.Eventually.of_forall fun z => by
          simpa only [Real.norm_eq_abs, abs_of_nonneg (hWnonneg z)]
            using hWbound z)
    simpa only [ENNReal.toReal_ofReal (hWnonneg _)] using hweighted
  have hpair2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (ρ.prod ρ) :=
    (memLp_two_iff_integrable_sq hr.aestronglyMeasurable).2 hpairSquare
  exact ⟨hρprob, hpair2⟩

theorem shared_tilted_moment_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun z : Ω × Ω => r z.1 z.2))
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ))
    (hrcan : ∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0)
    (s : ℝ) (hs : 0 ≤ s)
    (hrsecond :
      (∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)) ≤ s ^ 2)
    (L : Ω → ℝ) (hL : Measurable L) (K : ℝ)
    (hLnonneg : ∀ o, 0 ≤ L o)
    (hLle : ∀ o, L o ≤ K)
    (hLmass : (∫ o, L o ∂μ) = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hδsecond : (∫ o, (L o - 1) ^ 2 ∂μ) ≤ ε ^ 2) :
    let ρ : Measure Ω :=
      μ.withDensity (fun o => ENNReal.ofReal (L o))
    let f : Ω → ℝ := fun o => ∫ y, r o y * L y ∂μ
    ρ ≪ μ ∧
      MemLp f 2 ρ ∧
      (∀ᵐ o ∂ρ,
        Integrable (r o) ρ ∧ (∫ y, r o y ∂ρ) = f o) ∧
      Integrable
        (fun t : Ω × (Ω × Ω) => r t.1 t.2.1 * r t.1 t.2.2)
        (ρ.prod (ρ.prod ρ)) ∧
      (∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
        ∂(ρ.prod (ρ.prod ρ))) = (∫ o, f o ^ 2 ∂ρ) ∧
      0 ≤ (∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
        ∂(ρ.prod (ρ.prod ρ))) ∧
      (∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
        ∂(ρ.prod (ρ.prod ρ))) ≤ K * ε ^ 2 * s ^ 2 := by
  dsimp only
  let ρ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
  let f : Ω → ℝ := fun o => ∫ y, r o y * L y ∂μ
  obtain ⟨hρprob, hpairρ2⟩ :=
    qo_tilted_pair_l2 μ r hr hr2 L hL K hLnonneg hLle hLmass
  haveI : IsProbabilityMeasure ρ := hρprob
  have hρμ : ρ ≪ μ :=
    withDensity_absolutelyContinuous μ (fun o => ENNReal.ofReal (L o))
  obtain ⟨_, _, _, _, _, _, hfρ2, _, _, hfbound, hrowsμ⟩ :=
    Shao.OQ6.CanonicalTilt.section_contraction μ r hr hr2 hrcan s hs hrsecond
      L hL K hLnonneg hLle hLmass ε hε hδsecond
  -- Transfer the entire original-law good-row event before projecting it.
  have hrowsρ := hρμ.ae_le hrowsμ
  have hrowmatch : ∀ᵐ o ∂ρ,
      Integrable (r o) ρ ∧ (∫ y, r o y ∂ρ) = f o := by
    filter_upwards [hrowsρ] with o ho
    rcases ho with ⟨_, _, _, hrowρi, _, _, _, _, hmatch, _, _, _⟩
    exact ⟨hrowρi, hmatch⟩
  obtain ⟨_, _, hHi, hHq⟩ :=
    Shao.OQ6.CanonicalOverlap.shared_observation_moment ρ r hr hpairρ2
  have hHf :
      (∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
        ∂(ρ.prod (ρ.prod ρ))) = (∫ o, f o ^ 2 ∂ρ) := by
    calc
      _ = ∫ o, (∫ y, r o y ∂ρ) ^ 2 ∂ρ := hHq
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hrowmatch] with o ho
        rw [ho.2]
  refine ⟨hρμ, hfρ2, hrowmatch, hHi, hHf, ?_, ?_⟩
  · rw [hHf]
    exact integral_nonneg fun o => sq_nonneg (f o)
  · rw [hHf]
    exact hfbound

theorem disjoint_tilted_moment_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun z : Ω × Ω => r z.1 z.2))
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ))
    (hrsymm : ∀ o y, r o y = r y o)
    (hrcan : ∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0)
    (s : ℝ) (hs : 0 ≤ s)
    (hrsecond :
      (∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)) ≤ s ^ 2)
    (L : Ω → ℝ) (hL : Measurable L) (K : ℝ)
    (hLnonneg : ∀ o, 0 ≤ L o)
    (hLle : ∀ o, L o ≤ K)
    (hLmass : (∫ o, L o ∂μ) = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hδsecond : (∫ o, (L o - 1) ^ 2 ∂μ) ≤ ε ^ 2) :
    let ρ : Measure Ω :=
      μ.withDensity (fun o => ENNReal.ofReal (L o))
    Integrable
        (fun d : (Ω × Ω) × (Ω × Ω) =>
          r d.1.1 d.1.2 * r d.2.1 d.2.2)
        ((ρ.prod ρ).prod (ρ.prod ρ)) ∧
      (∫ d : (Ω × Ω) × (Ω × Ω),
        r d.1.1 d.1.2 * r d.2.1 d.2.2
        ∂((ρ.prod ρ).prod (ρ.prod ρ))) =
        (∫ z : Ω × Ω, r z.1 z.2 ∂(ρ.prod ρ)) ^ 2 ∧
      0 ≤ (∫ d : (Ω × Ω) × (Ω × Ω),
        r d.1.1 d.1.2 * r d.2.1 d.2.2
        ∂((ρ.prod ρ).prod (ρ.prod ρ))) ∧
      (∫ d : (Ω × Ω) × (Ω × Ω),
        r d.1.1 d.1.2 * r d.2.1 d.2.2
        ∂((ρ.prod ρ).prod (ρ.prod ρ))) ≤ s ^ 2 * ε ^ 4 := by
  dsimp only
  let ρ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
  obtain ⟨hρprob, _, _, _, _, hrρi, _, _, _, _, _, hmeanbound⟩ :=
    Shao.OQ6.CanonicalTilt.pair_contraction μ r hr hr2 hrsymm hrcan s hs
      hrsecond L hL K hLnonneg hLle hLmass ε hε hδsecond
  haveI : IsProbabilityMeasure ρ := hρprob
  obtain ⟨hJi, hJmean⟩ :=
    Shao.OQ6.CanonicalOverlap.disjoint_observation_moment ρ r hrρi
  refine ⟨hJi, hJmean, ?_, ?_⟩
  · rw [hJmean]
    exact sq_nonneg _
  · rw [hJmean]
    calc
      (∫ z : Ω × Ω, r z.1 z.2 ∂(ρ.prod ρ)) ^ 2 =
          |∫ z : Ω × Ω, r z.1 z.2 ∂(ρ.prod ρ)| ^ 2 := (sq_abs _).symm
      _ ≤ (s * ε ^ 2) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hmeanbound 2
      _ = s ^ 2 * ε ^ 4 := by ring

end

end Shao.OQ6.QuantitativeOverlap
