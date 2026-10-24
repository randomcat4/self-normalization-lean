import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Shao.OQ6.CanonicalTilt

noncomputable section

open MeasureTheory

/- The bounded density is on the whole observation space.  Every use of
Fubini below is accompanied by genuine integrability.  The two public
contractions are the analytic step in source p39(9), with Shao--Zhou
attribution; they do not assert the subsequent counts or probability bound. -/

private theorem ct_density_data
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (L : α → ℝ) (hL : Measurable L) (K : ℝ)
    (hn : ∀ x, 0 ≤ L x) (hb : ∀ x, L x ≤ K)
    (hm : (∫ x, L x ∂μ) = 1) :
    IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (L x))) ∧
      1 ≤ K ∧ MemLp L 2 μ ∧ MemLp (fun x => L x - 1) 2 μ := by
  have hnorm : ∀ᵐ x ∂μ, ‖L x‖ ≤ K :=
    Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hn x)] using hb x
  have hi : Integrable L μ := Integrable.of_bound hL.aestronglyMeasurable K hnorm
  have h2 : MemLp L 2 μ := MemLp.of_bound hL.aestronglyMeasurable K hnorm
  have hK : 1 ≤ K := by
    have h := integral_mono hi (integrable_const K) hb
    simpa only [hm, integral_const, probReal_univ, one_smul] using h
  refine ⟨?_, hK, h2, ?_⟩
  · constructor
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn), hm]
    exact ENNReal.ofReal_one
  · exact h2.sub (memLp_const (1 : ℝ))

private theorem ct_density_integrable
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (L : α → ℝ) (hL : Measurable L) (K : ℝ)
    (hn : ∀ x, 0 ≤ L x) (hb : ∀ x, L x ≤ K)
    {g : α → ℝ} (hg : Integrable g μ) :
    Integrable g (μ.withDensity (fun x => ENNReal.ofReal (L x))) := by
  apply (integrable_withDensity_iff hL.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).2
  have hp : Integrable (fun x => g x * L x) μ :=
    hg.mul_bdd hL.aestronglyMeasurable (c := K)
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hn x)] using hb x)
  simpa only [ENNReal.toReal_ofReal (hn _)] using hp

private theorem ct_density_integral
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (L : α → ℝ) (hL : Measurable L) (hn : ∀ x, 0 ≤ L x)
    (g : α → ℝ) :
    (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (L x))) =
      ∫ x, g x * L x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul hL.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hn _), smul_eq_mul, mul_comm]

private theorem ct_density_memLp_two
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (L : α → ℝ) (hL : Measurable L) (K : ℝ)
    (hn : ∀ x, 0 ≤ L x) (hb : ∀ x, L x ≤ K)
    {g : α → ℝ} (hgm : Measurable g) (hg : MemLp g 2 μ) :
    MemLp g 2 (μ.withDensity (fun x => ENNReal.ofReal (L x))) := by
  apply (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2
  exact ct_density_integrable μ L hL K hn hb hg.integrable_sq

private theorem ct_density_nonneg_moment
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (L : α → ℝ) (hL : Measurable L) (K : ℝ)
    (hn : ∀ x, 0 ≤ L x) (hb : ∀ x, L x ≤ K)
    {g : α → ℝ} (hg : Integrable g μ) (hgn : ∀ x, 0 ≤ g x) :
    (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (L x))) ≤
      K * ∫ x, g x ∂μ := by
  have hprod : Integrable (fun x => g x * L x) μ :=
    hg.mul_bdd hL.aestronglyMeasurable (c := K)
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hn x)] using hb x)
  rw [ct_density_integral μ L hL hn]
  calc
    _ ≤ ∫ x, K * g x ∂μ := integral_mono hprod (hg.const_mul K)
      (fun x => by simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (hb x) (hgn x))
    _ = _ := by rw [integral_const_mul]

private theorem ct_cauchy_square
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {u v : α → ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    |∫ x, u x * v x ∂μ| ^ 2 ≤
      (∫ x, u x ^ 2 ∂μ) * (∫ x, v x ^ 2 ∂μ) := by
  have hh := integral_mul_norm_le_Lp_mul_Lq
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
      (2 : ℝ).HolderConjugate 2)
    (by simpa using hu) (by simpa using hv)
  have hnorm : |∫ x, u x * v x ∂μ| ≤
      Real.sqrt (∫ x, u x ^ 2 ∂μ) * Real.sqrt (∫ x, v x ^ 2 ∂μ) := by
    refine (norm_integral_le_integral_norm (μ := μ)
      (fun x : α => u x * v x)).trans ?_
    simpa only [norm_mul, Real.norm_eq_abs, Real.rpow_two,
      ← Real.sqrt_eq_rpow, sq_abs] using hh
  calc
    _ ≤ (Real.sqrt (∫ x, u x ^ 2 ∂μ) *
        Real.sqrt (∫ x, v x ^ 2 ∂μ)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hnorm 2
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (u x)),
        Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (v x))]

private theorem ct_pair_density
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (L : α → ℝ) (hL : Measurable L) (hn : ∀ x, 0 ≤ L x) :
    (μ.withDensity (fun x => ENNReal.ofReal (L x))).prod
        (μ.withDensity (fun x => ENNReal.ofReal (L x))) =
      (μ.prod μ).withDensity (fun z : α × α =>
        ENNReal.ofReal (L z.1 * L z.2)) := by
  rw [prod_withDensity hL.ennreal_ofReal hL.ennreal_ofReal]
  congr 1
  funext z
  rw [ENNReal.ofReal_mul (hn z.1)]

theorem pair_contraction
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun z : Ω × Ω => r z.1 z.2))
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ))
    (hrsymm : ∀ o y, r o y = r y o)
    (hrcan : ∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0)
    (s : ℝ) (hs : 0 ≤ s)
    (hrsecond : (∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)) ≤ s ^ 2)
    (L : Ω → ℝ) (hL : Measurable L) (K : ℝ)
    (hLnonneg : ∀ o, 0 ≤ L o) (hLle : ∀ o, L o ≤ K)
    (hLmass : (∫ o, L o ∂μ) = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hδsecond : (∫ o, (L o - 1) ^ 2 ∂μ) ≤ ε ^ 2) :
    let δ : Ω → ℝ := fun o => L o - 1
    let ρ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
    IsProbabilityMeasure ρ ∧
      1 ≤ K ∧
      MemLp L 2 μ ∧ MemLp δ 2 μ ∧
      MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (ρ.prod ρ) ∧
      Integrable (fun z : Ω × Ω => r z.1 z.2) (ρ.prod ρ) ∧
      Integrable (fun z : Ω × Ω => r z.1 z.2 ^ 2) (ρ.prod ρ) ∧
      (∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(ρ.prod ρ)) ≤ K ^ 2 * s ^ 2 ∧
      Integrable (fun z : Ω × Ω => r z.1 z.2 * L z.1 * L z.2) (μ.prod μ) ∧
      Integrable (fun z : Ω × Ω => r z.1 z.2 * δ z.1 * δ z.2) (μ.prod μ) ∧
      (∫ z : Ω × Ω, r z.1 z.2 ∂(ρ.prod ρ)) =
        (∫ z : Ω × Ω, r z.1 z.2 * δ z.1 * δ z.2 ∂(μ.prod μ)) ∧
      |∫ z : Ω × Ω, r z.1 z.2 ∂(ρ.prod ρ)| ≤ s * ε ^ 2 := by
  dsimp only
  let δ : Ω → ℝ := fun o => L o - 1
  let ρ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
  obtain ⟨hρ, hK, hL2, hδ2⟩ := ct_density_data μ L hL K hLnonneg hLle hLmass
  letI : IsProbabilityMeasure ρ := hρ
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hδm : Measurable δ := hL.sub measurable_const
  have hδb (o : Ω) : ‖δ o‖ ≤ K + 1 := by
    change |L o - 1| ≤ K + 1
    have h := abs_sub (L o) 1
    rw [abs_of_nonneg (hLnonneg o), abs_one] at h
    exact h.trans (by linarith [hLle o])
  let W : Ω × Ω → ℝ := fun z => L z.1 * L z.2
  have hWm : Measurable W := (hL.comp measurable_fst).mul (hL.comp measurable_snd)
  have hWn (z : Ω × Ω) : 0 ≤ W z := mul_nonneg (hLnonneg _) (hLnonneg _)
  have hWb (z : Ω × Ω) : W z ≤ K ^ 2 := by
    simpa only [W, pow_two] using
      mul_le_mul (hLle z.1) (hLle z.2) (hLnonneg z.2) hK0
  have hρpair : ρ.prod ρ = (μ.prod μ).withDensity
      (fun z => ENNReal.ofReal (W z)) := ct_pair_density μ L hL hLnonneg
  have hrρ2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (ρ.prod ρ) := by
    rw [hρpair]
    exact ct_density_memLp_two (μ.prod μ) W hWm (K ^ 2) hWn hWb hr hr2
  have hrρi := hrρ2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hrρsq := hrρ2.integrable_sq
  have hrρbound : (∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂ρ.prod ρ) ≤ K ^ 2 * s ^ 2 := by
    rw [hρpair]
    exact (ct_density_nonneg_moment (μ.prod μ) W hWm (K ^ 2) hWn hWb
      hr2.integrable_sq (fun z => sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hrsecond (sq_nonneg K))
  have hri : Integrable (fun z : Ω × Ω => r z.1 z.2) (μ.prod μ) :=
    hr2.integrable (by norm_num)
  have hrL1 : Integrable (fun z : Ω × Ω => r z.1 z.2 * L z.1) (μ.prod μ) :=
    hri.mul_bdd (g := fun z : Ω × Ω => L z.1)
    (hL.comp measurable_fst).aestronglyMeasurable
    (c := K) (Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hLnonneg z.1)] using hLle z.1)
  have hrLL : Integrable (fun z : Ω × Ω => r z.1 z.2 * L z.1 * L z.2) (μ.prod μ) :=
    hrL1.mul_bdd (g := fun z : Ω × Ω => L z.2)
    (hL.comp measurable_snd).aestronglyMeasurable
    (c := K) (Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hLnonneg z.2)] using hLle z.2)
  have hrδ1 : Integrable (fun z : Ω × Ω => r z.1 z.2 * δ z.1) (μ.prod μ) :=
    hri.mul_bdd (g := fun z : Ω × Ω => δ z.1)
    (hδm.comp measurable_fst).aestronglyMeasurable
    (c := K + 1) (Filter.Eventually.of_forall fun z => hδb z.1)
  have hrδ2 : Integrable (fun z : Ω × Ω => r z.1 z.2 * δ z.2) (μ.prod μ) :=
    hri.mul_bdd (g := fun z : Ω × Ω => δ z.2)
    (hδm.comp measurable_snd).aestronglyMeasurable
    (c := K + 1) (Filter.Eventually.of_forall fun z => hδb z.2)
  have hrδδ : Integrable (fun z : Ω × Ω => r z.1 z.2 * δ z.1 * δ z.2) (μ.prod μ) :=
    hrδ1.mul_bdd (g := fun z : Ω × Ω => δ z.2)
    (hδm.comp measurable_snd).aestronglyMeasurable
    (c := K + 1) (Filter.Eventually.of_forall fun z => hδb z.2)
  have hzero : (∫ z : Ω × Ω, r z.1 z.2 ∂μ.prod μ) = 0 := by
    rw [integral_prod _ hri]
    exact integral_eq_zero_of_ae hrcan
  have hzero1 : (∫ z : Ω × Ω, r z.1 z.2 * δ z.1 ∂μ.prod μ) = 0 := by
    rw [integral_prod (fun z : Ω × Ω => r z.1 z.2 * δ z.1) hrδ1]
    apply integral_eq_zero_of_ae
    filter_upwards [hrcan] with o ho
    rw [integral_mul_const, ho, zero_mul]
    rfl
  have hcol : ∀ᵐ y ∂μ, (∫ o, r o y ∂μ) = 0 := by
    filter_upwards [hrcan] with y hy
    calc
      _ = ∫ o, r y o ∂μ := integral_congr_ae
        (Filter.Eventually.of_forall fun o => hrsymm o y)
      _ = 0 := hy
  have hzero2 : (∫ z : Ω × Ω, r z.1 z.2 * δ z.2 ∂μ.prod μ) = 0 := by
    rw [integral_prod_symm (fun z : Ω × Ω => r z.1 z.2 * δ z.2) hrδ2]
    apply integral_eq_zero_of_ae
    filter_upwards [hcol] with y hy
    rw [integral_mul_const, hy, zero_mul]
    rfl
  have hchange : (∫ z : Ω × Ω, r z.1 z.2 ∂ρ.prod ρ) =
      ∫ z : Ω × Ω, r z.1 z.2 * L z.1 * L z.2 ∂μ.prod μ := by
    rw [hρpair, ct_density_integral (μ.prod μ) W hWm hWn]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by dsimp [W]; ring
  have hcancel : (∫ z : Ω × Ω, r z.1 z.2 ∂ρ.prod ρ) =
      ∫ z : Ω × Ω, r z.1 z.2 * δ z.1 * δ z.2 ∂μ.prod μ := by
    rw [hchange]
    calc
      _ = ∫ z : Ω × Ω, ((r z.1 z.2 + r z.1 z.2 * δ z.1) +
          r z.1 z.2 * δ z.2) + r z.1 z.2 * δ z.1 * δ z.2 ∂μ.prod μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by dsimp [δ]; ring
      _ = _ := by
        rw [integral_add
            (f := fun z : Ω × Ω => (r z.1 z.2 + r z.1 z.2 * δ z.1) +
              r z.1 z.2 * δ z.2)
            (g := fun z : Ω × Ω => r z.1 z.2 * δ z.1 * δ z.2)
            ((hri.add hrδ1).add hrδ2) hrδδ,
          integral_add
            (f := fun z : Ω × Ω => r z.1 z.2 + r z.1 z.2 * δ z.1)
            (g := fun z : Ω × Ω => r z.1 z.2 * δ z.2)
            (hri.add hrδ1) hrδ2,
          integral_add
            (f := fun z : Ω × Ω => r z.1 z.2)
            (g := fun z : Ω × Ω => r z.1 z.2 * δ z.1) hri hrδ1,
          hzero, hzero1, hzero2]
        ring
  let B : Ω × Ω → ℝ := fun z => δ z.1 * δ z.2
  have hBm : Measurable B := (hδm.comp measurable_fst).mul (hδm.comp measurable_snd)
  have hBsq : Integrable (fun z => B z ^ 2) (μ.prod μ) := by
    simpa only [B, mul_pow] using hδ2.integrable_sq.mul_prod hδ2.integrable_sq
  have hB2 : MemLp B 2 (μ.prod μ) :=
    (memLp_two_iff_integrable_sq hBm.aestronglyMeasurable).2 hBsq
  have hBmoment : (∫ z, B z ^ 2 ∂μ.prod μ) = (∫ o, δ o ^ 2 ∂μ) ^ 2 := by
    simp only [B, mul_pow]
    rw [integral_prod_mul (fun o => δ o ^ 2) (fun o => δ o ^ 2), pow_two]
  have hd0 : 0 ≤ ∫ o, δ o ^ 2 ∂μ := integral_nonneg fun o => sq_nonneg _
  have hcs := ct_cauchy_square (μ.prod μ) hr2 hB2
  have hsharp : |∫ z : Ω × Ω, r z.1 z.2 * δ z.1 * δ z.2 ∂μ.prod μ| ≤
      s * ε ^ 2 := by
    have hT : |∫ z : Ω × Ω, r z.1 z.2 * δ z.1 * δ z.2 ∂μ.prod μ| ^ 2 ≤
        s ^ 2 * (ε ^ 2) ^ 2 := by
      have he : (fun z : Ω × Ω => r z.1 z.2 * B z) =
          (fun z => r z.1 z.2 * δ z.1 * δ z.2) := by
        funext z; dsimp [B]; ring
      rw [he, hBmoment] at hcs
      exact hcs.trans (mul_le_mul hrsecond
        (pow_le_pow_left₀ hd0 hδsecond 2) (sq_nonneg _)
        (sq_nonneg s))
    have hn : 0 ≤ s * ε ^ 2 := mul_nonneg hs (sq_nonneg ε)
    have hp : (s * ε ^ 2) ^ 2 = s ^ 2 * (ε ^ 2) ^ 2 := mul_pow _ _ _
    nlinarith [abs_nonneg (∫ z : Ω × Ω,
      r z.1 z.2 * δ z.1 * δ z.2 ∂μ.prod μ)]
  refine ⟨hρ, hK, hL2, hδ2, hrρ2, hrρi, hrρsq, hrρbound,
    hrLL, hrδδ, hcancel, ?_⟩
  rw [hcancel]
  exact hsharp

theorem section_contraction
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun z : Ω × Ω => r z.1 z.2))
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ))
    (hrcan : ∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0)
    (s : ℝ) (hs : 0 ≤ s)
    (hrsecond : (∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)) ≤ s ^ 2)
    (L : Ω → ℝ) (hL : Measurable L)
    (K : ℝ)
    (hLnonneg : ∀ o, 0 ≤ L o) (hLle : ∀ o, L o ≤ K)
    (hLmass : (∫ o, L o ∂μ) = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hδsecond : (∫ o, (L o - 1) ^ 2 ∂μ) ≤ ε ^ 2) :
    let δ : Ω → ℝ := fun o => L o - 1
    let ρ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
    let R : Ω → ℝ := fun o => ∫ y, r o y ^ 2 ∂μ
    let f : Ω → ℝ := fun o => ∫ y, r o y * L y ∂μ
    Measurable R ∧ Integrable R μ ∧
      (∫ o, R o ∂μ) = (∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)) ∧
      (∫ o, R o ∂μ) ≤ s ^ 2 ∧
      Measurable f ∧ MemLp f 2 μ ∧ MemLp f 2 ρ ∧
      Integrable (fun o => f o ^ 2) μ ∧
      Integrable (fun o => f o ^ 2) ρ ∧
      (∫ o, f o ^ 2 ∂ρ) ≤ K * ε ^ 2 * s ^ 2 ∧
      (∀ᵐ o ∂μ,
        MemLp (r o) 2 μ ∧ MemLp (r o) 2 ρ ∧
        Integrable (r o) μ ∧ Integrable (r o) ρ ∧
        Integrable (fun y => r o y ^ 2) μ ∧
        Integrable (fun y => r o y ^ 2) ρ ∧
        Integrable (fun y => r o y * L y) μ ∧
        Integrable (fun y => r o y * δ y) μ ∧
        (∫ y, r o y ∂ρ) = f o ∧
        f o = (∫ y, r o y * δ y ∂μ) ∧
        |f o| ^ 2 ≤ ε ^ 2 * R o ∧
        (∫ y, r o y ^ 2 ∂ρ) ≤ K * R o) := by
  dsimp only
  let δ : Ω → ℝ := fun o => L o - 1
  let ρ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
  let R : Ω → ℝ := fun o => ∫ y, r o y ^ 2 ∂μ
  let f : Ω → ℝ := fun o => ∫ y, r o y * L y ∂μ
  obtain ⟨hρ, hK, hL2, hδ2⟩ := ct_density_data μ L hL K hLnonneg hLle hLmass
  letI : IsProbabilityMeasure ρ := hρ
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hRm : Measurable R :=
    (hr.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  have hRi : Integrable R μ := hr2.integrable_sq.integral_prod_left
  have hRint : (∫ o, R o ∂μ) =
      ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂μ.prod μ :=
    (integral_prod _ hr2.integrable_sq).symm
  have hRbound : (∫ o, R o ∂μ) ≤ s ^ 2 := hRint.symm ▸ hrsecond
  have hRn (o : Ω) : 0 ≤ R o := integral_nonneg fun y => sq_nonneg _
  have hfm : Measurable f :=
    (hr.mul (hL.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
  have hrows : ∀ᵐ o ∂μ,
      MemLp (r o) 2 μ ∧ MemLp (r o) 2 ρ ∧
      Integrable (r o) μ ∧ Integrable (r o) ρ ∧
      Integrable (fun y => r o y ^ 2) μ ∧
      Integrable (fun y => r o y ^ 2) ρ ∧
      Integrable (fun y => r o y * L y) μ ∧
      Integrable (fun y => r o y * δ y) μ ∧
      (∫ y, r o y ∂ρ) = f o ∧
      f o = (∫ y, r o y * δ y ∂μ) ∧
      |f o| ^ 2 ≤ ε ^ 2 * R o ∧
      (∫ y, r o y ^ 2 ∂ρ) ≤ K * R o := by
    filter_upwards [hr2.integrable_sq.prod_right_ae, hrcan] with o hsq hcan
    have hrowm : Measurable (r o) := hr.comp (measurable_const.prodMk measurable_id)
    have hrow2 : MemLp (r o) 2 μ :=
      (memLp_two_iff_integrable_sq hrowm.aestronglyMeasurable).2 hsq
    have hrowρ2 : MemLp (r o) 2 ρ :=
      ct_density_memLp_two μ L hL K hLnonneg hLle hrowm hrow2
    have hrowi := hrow2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
    have hrowρi := hrowρ2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
    have hrowL : Integrable (fun y => r o y * L y) μ := hrow2.integrable_mul hL2
    have hrowδ : Integrable (fun y => r o y * δ y) μ := hrow2.integrable_mul hδ2
    have hchange : (∫ y, r o y ∂ρ) = f o :=
      ct_density_integral μ L hL hLnonneg (r o)
    have hcancel : f o = ∫ y, r o y * δ y ∂μ := by
      calc
        _ = ∫ y, r o y * δ y + r o y ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun y => by dsimp [δ]; ring
        _ = (∫ y, r o y * δ y ∂μ) + ∫ y, r o y ∂μ :=
          integral_add (f := fun y => r o y * δ y) (g := fun y => r o y) hrowδ hrowi
        _ = _ := by rw [hcan, add_zero]
    have hcs : |f o| ^ 2 ≤ ε ^ 2 * R o := by
      rw [hcancel]
      have h := ct_cauchy_square μ hrow2 hδ2
      exact h.trans (by simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left hδsecond (hRn o))
    have hrowbound : (∫ y, r o y ^ 2 ∂ρ) ≤ K * R o :=
      ct_density_nonneg_moment μ L hL K hLnonneg hLle hsq (fun y => sq_nonneg _)
    exact ⟨hrow2, hrowρ2, hrowi, hrowρi, hsq, hrowρ2.integrable_sq,
      hrowL, hrowδ, hchange, hcancel, hcs, hrowbound⟩
  have hpoint : ∀ᵐ o ∂μ, f o ^ 2 ≤ ε ^ 2 * R o := by
    filter_upwards [hrows] with o ho
    rcases ho with ⟨_, _, _, _, _, _, _, _, _, _, hb, _⟩
    simpa only [sq_abs] using hb
  have hfsq : Integrable (fun o => f o ^ 2) μ := by
    refine (hRi.const_mul (ε ^ 2)).mono' (hfm.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hpoint] with o ho
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f o))] using ho
  have hf2 : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).2 hfsq
  have hfρ2 : MemLp f 2 ρ := ct_density_memLp_two μ L hL K hLnonneg hLle hfm hf2
  have hfsqbound : (∫ o, f o ^ 2 ∂μ) ≤ ε ^ 2 * ∫ o, R o ∂μ := by
    simpa only [integral_const_mul] using
      integral_mono_ae hfsq (hRi.const_mul (ε ^ 2)) hpoint
  have hconsumer : (∫ o, f o ^ 2 ∂ρ) ≤ K * ε ^ 2 * s ^ 2 := by
    calc
      _ ≤ K * ∫ o, f o ^ 2 ∂μ := ct_density_nonneg_moment μ L hL K hLnonneg
        hLle hfsq (fun o => sq_nonneg _)
      _ ≤ K * (ε ^ 2 * ∫ o, R o ∂μ) := mul_le_mul_of_nonneg_left hfsqbound hK0
      _ ≤ K * (ε ^ 2 * s ^ 2) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hRbound (sq_nonneg ε)) hK0
      _ = _ := by ring
  exact ⟨hRm, hRi, hRint, hRbound, hfm, hf2, hfρ2, hfsq, hfρ2.integrable_sq,
    hconsumer, hrows⟩

end

end Shao.OQ6.CanonicalTilt
