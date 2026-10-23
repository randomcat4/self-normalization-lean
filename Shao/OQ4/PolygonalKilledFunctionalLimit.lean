-- Exact lane-lead formal freeze: all42 heads and16 transparent values (14defs+2abbrevs).
-- Full mathematical proof, every proposed head/value, and pinned API evidence read.
-- Producer declarations frozen; consumer may be locally implemented but not checked against unqualified objects.
-- Full implementation of the exact frozen heads/transparent values.
-- Unchecked source: no import check or object emission is authorized yet.
-- Producer binding follows author142's exact declaration proposal b8056e19.
-- Producer qualification is pending; these imports are not accepted evidence.
import Shao.OQ4.PolygonalPathTightness
import Shao.OQ4.PolygonalBrownianWeakLimit
import Shao.OQ4.BrownianSurvivalBoundary
import Shao.Probability.MeasurablePath
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

noncomputable section
namespace Shao.OQ4.PolygonalKilledFunctionalLimit
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Ω : Type*} [MeasurableSpace Ω]

-- Four PUBLIC definition values. Time zero is explicitly monitored.
def floorHorizon (T : ℝ≥0) (h : ℝ) : ℕ :=
  ⌊(T : ℝ) * h ^ 2⌋₊

def discreteClosedSurvival (n l : ℕ) (h u : ℝ) (b : ℝ≥0) : Set (Shao.Path n) :=
  {a | ∀ k : ℕ, k ≤ l → |u + Shao.prefixSum a k / h| ≤ (b : ℝ)}

def discreteKilledCosine (n l : ℕ) (h u : ℝ) (b : ℝ≥0) : Shao.Path n → ℝ :=
  (discreteClosedSurvival n l h u b).indicator
    (fun a => Real.cos ((Real.pi / 2) * (u + Shao.prefixSum a l / h)))

def brownianKilledCosine (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (u : ℝ) : Ω → ℝ :=
  (BrownianSurvivalBoundary.closedSurvival B T u).indicator
    (fun ω => Real.cos ((Real.pi / 2) * (u + B T ω)))

-- PUBLIC deterministic/measurability/integrability heads.
theorem floorHorizon_le (T : ℝ≥0) (h : ℝ) (n : ℕ)
    (horizon : (T : ℝ) * h ^ 2 ≤ (n : ℝ)) :
    floorHorizon T h ≤ n := by
  exact Nat.floor_le_of_le horizon

theorem discreteClosedSurvival_iff_polygonal
    (n l : ℕ) (h : ℝ) (hh : 0 < h) (hl : l ≤ n)
    (u : ℝ) (b : ℝ≥0) (a : Shao.Path n) :
    a ∈ discreteClosedSurvival n l h u b ↔
      ∀ t : ℝ, t ∈ Icc 0 ((l : ℝ) / h ^ 2) →
        |u + PolygonalThirdMoment.polygonalPath n h a t| ≤ (b : ℝ) := by
  have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
  constructor
  · intro ha t ht
    by_cases he : t = (l : ℝ) / h ^ 2
    · rw [he, PolygonalThirdMoment.polygonalPath_at_grid n h hh a l hl]
      exact ha l le_rfl
    have htl : t < (l : ℝ) / h ^ 2 := lt_of_le_of_ne ht.2 he
    let k : ℕ := ⌊t * h ^ 2⌋₊
    have hx : 0 ≤ t * h ^ 2 := mul_nonneg ht.1 hh2.le
    have hk0 : (k : ℝ) ≤ t * h ^ 2 := Nat.floor_le hx
    have hk1 : t * h ^ 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hkl : k < l := by
      have hreal : (k : ℝ) < (l : ℝ) :=
        hk0.trans_lt ((lt_div_iff₀ hh2).mp htl)
      exact_mod_cast hreal
    have hkn : k < n := lt_of_lt_of_le hkl hl
    let v : ℝ := t * h ^ 2 - (k : ℝ)
    have hv0 : 0 ≤ v := sub_nonneg.mpr hk0
    have hv1 : v ≤ 1 := by dsimp [v]; linarith
    have htform : t = ((k : ℝ) + v) / h ^ 2 := by
      apply (eq_div_iff (ne_of_gt hh2)).mpr
      dsimp [v]
      ring
    rw [htform, PolygonalThirdMoment.polygonalPath_on_grid_interval
      n h hh a k hkn v hv0 hv1]
    have hkbound := ha k hkl.le
    have hnext := ha (k + 1) (Nat.succ_le_iff.mpr hkl)
    calc
      |u + ((1 - v) * (Shao.prefixSum a k / h) +
          v * (Shao.prefixSum a (k + 1) / h))| =
        |(1 - v) * (u + Shao.prefixSum a k / h) +
          v * (u + Shao.prefixSum a (k + 1) / h)| := by congr 1; ring
      _ ≤ |(1 - v) * (u + Shao.prefixSum a k / h)| +
          |v * (u + Shao.prefixSum a (k + 1) / h)| := abs_add_le _ _
      _ = (1 - v) * |u + Shao.prefixSum a k / h| +
          v * |u + Shao.prefixSum a (k + 1) / h| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hv1), abs_of_nonneg hv0]
      _ ≤ (1 - v) * (b : ℝ) + v * (b : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hkbound (sub_nonneg.mpr hv1))
          (mul_le_mul_of_nonneg_left hnext hv0)
      _ = (b : ℝ) := by ring
  · intro ha k hk
    have htime : (k : ℝ) / h ^ 2 ∈ Icc (0 : ℝ) ((l : ℝ) / h ^ 2) := by
      constructor
      · exact div_nonneg (Nat.cast_nonneg _) hh2.le
      · exact div_le_div_of_nonneg_right (by exact_mod_cast hk) hh2.le
    simpa only [PolygonalThirdMoment.polygonalPath_at_grid n h hh a k (hk.trans hl)]
      using ha ((k : ℝ) / h ^ 2) htime

theorem measurableSet_discreteClosedSurvival
    (n l : ℕ) (h u : ℝ) (b : ℝ≥0) :
    MeasurableSet (discreteClosedSurvival n l h u b) := by
  simp only [discreteClosedSurvival, Set.ofPred_forall]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    measurableSet_le (continuous_abs.measurable.comp
      (measurable_const.add ((Shao.measurable_prefixSum k).div_const h)))
      measurable_const

theorem integrable_discreteKilledCosine
    (n l : ℕ) (h u : ℝ) (b : ℝ≥0)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Integrable (discreteKilledCosine n l h u b)
      (Measure.pi (fun _ : Fin n => ν)) := by
  have hc : Measurable (fun a : Shao.Path n =>
      Real.cos ((Real.pi / 2) * (u + Shao.prefixSum a l / h))) :=
    Real.continuous_cos.measurable.comp
      (measurable_const.mul (measurable_const.add ((Shao.measurable_prefixSum l).div_const h)))
  have hi : Integrable (fun a : Shao.Path n =>
      Real.cos ((Real.pi / 2) * (u + Shao.prefixSum a l / h)))
      (Measure.pi (fun _ : Fin n => ν)) :=
    (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => by simpa [Real.norm_eq_abs] using Real.abs_cos_le_one _)
  exact hi.indicator (measurableSet_discreteClosedSurvival n l h u b)

theorem integrable_brownianKilledCosine
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (u : ℝ) :
    Integrable (brownianKilledCosine B T u) P := by
  have hc : AEMeasurable (fun ω => Real.cos ((Real.pi / 2) * (u + B T ω))) P :=
    Real.continuous_cos.measurable.comp_aemeasurable
      (((hB.toIsPreBrownianReal.aemeasurable T).const_add u).const_mul (Real.pi / 2))
  have hi : Integrable (fun ω => Real.cos ((Real.pi / 2) * (u + B T ω))) P :=
    (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using Real.abs_cos_le_one _)
  exact hi.indicator₀ (BrownianSurvivalBoundary.closedSurvival_nullMeasurable B P hB T u)

-- PRIVATE domain aliases, each with its full transparent value.
private abbrev PathSpace := C(unitInterval, ℝ)
private abbrev Parameters := unitInterval × (ℝ × ℝ)

private theorem scaleUnit_mem (θ s : unitInterval) :
    (θ : ℝ) * (s : ℝ) ∈ Icc (0 : ℝ) 1 := by
  exact ⟨mul_nonneg θ.2.1 s.2.1,
    (mul_le_mul_of_nonneg_left s.2.2 θ.2.1).trans (by simpa using θ.2.2)⟩

private theorem continuous_scaleUnit_value (θ : unitInterval) :
    Continuous (fun s : unitInterval =>
      (⟨(θ : ℝ) * (s : ℝ), scaleUnit_mem θ s⟩ : unitInterval)) := by
  exact (continuous_const.mul continuous_subtype_val).subtype_mk _

private def scaleUnit (θ : unitInterval) : C(unitInterval, unitInterval) :=
  ⟨fun s => ⟨(θ : ℝ) * (s : ℝ), scaleUnit_mem θ s⟩,
    continuous_scaleUnit_value θ⟩

private def reparam (θ : unitInterval) (f : PathSpace) : PathSpace :=
  f.comp (scaleUnit θ)

private theorem continuous_reparam :
    Continuous (fun q : unitInterval × PathSpace => reparam q.1 q.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hs : Continuous (fun q : (unitInterval × PathSpace) × unitInterval =>
      scaleUnit q.1.1 q.2) := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul
      (continuous_subtype_val.comp continuous_snd)
  exact continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk hs)

private def stripGap (p : Parameters) (f : PathSpace) : ℝ :=
  ‖ContinuousMap.const unitInterval p.2.1 + reparam p.1 f‖ - p.2.2

private def terminalCos (p : Parameters) (f : PathSpace) : ℝ :=
  Real.cos ((Real.pi / 2) * (p.2.1 + f p.1))

private theorem continuous_stripGap :
    Continuous (fun q : Parameters × PathSpace => stripGap q.1 q.2) := by
  have hc : Continuous (fun q : Parameters × PathSpace =>
      ContinuousMap.const unitInterval q.1.2.1) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_fst.comp (continuous_snd.comp (continuous_fst.comp continuous_fst))
  exact (hc.add (continuous_reparam.comp
    ((continuous_fst.comp continuous_fst).prodMk continuous_snd))).norm.sub
      (continuous_snd.comp (continuous_snd.comp continuous_fst))

private theorem continuous_terminalCos :
    Continuous (fun q : Parameters × PathSpace => terminalCos q.1 q.2) := by
  exact Real.continuous_cos.comp (continuous_const.mul
    ((continuous_fst.comp (continuous_snd.comp continuous_fst)).add
      (continuous_eval.comp (continuous_snd.prodMk (continuous_fst.comp continuous_fst)))))

private theorem stripGap_nonpos_iff (p : Parameters) (f : PathSpace) :
    stripGap p f ≤ 0 ↔
      ∀ s : unitInterval, |p.2.1 + f (scaleUnit p.1 s)| ≤ p.2.2 := by
  rw [stripGap, sub_nonpos, ContinuousMap.norm_le_of_nonempty]
  rfl

private theorem floorRatio_mem (T : ℝ≥0) (h : ℝ)
    (hT : 0 < T) (hh : 0 < h) :
    ((floorHorizon T h : ℝ) / h ^ 2) / (T : ℝ) ∈ Icc (0 : ℝ) 1 := by
  have hTr : 0 < (T : ℝ) := hT
  have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
  have hfloor : (floorHorizon T h : ℝ) ≤ (T : ℝ) * h ^ 2 :=
    Nat.floor_le (mul_nonneg T.2 (sq_nonneg h))
  constructor
  · exact div_nonneg (div_nonneg (Nat.cast_nonneg _) hh2.le) hTr.le
  · apply (div_le_one hTr).mpr
    exact (div_le_iff₀ hh2).mpr hfloor

private def floorRatio (T : ℝ≥0) (h : ℝ) (hT : 0 < T) (hh : 0 < h) :
    unitInterval :=
  ⟨((floorHorizon T h : ℝ) / h ^ 2) / (T : ℝ), floorRatio_mem T h hT hh⟩

private theorem floorRatio_error (T : ℝ≥0) (h : ℝ)
    (hT : 0 < T) (hh : 0 < h) :
    0 ≤ 1 - (floorRatio T h hT hh : ℝ) ∧
      1 - (floorRatio T h hT hh : ℝ) < 1 / ((T : ℝ) * h ^ 2) := by
  have hTr : 0 < (T : ℝ) := hT
  have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
  constructor
  · exact sub_nonneg.mpr (floorRatio_mem T h hT hh).2
  · have hf : (T : ℝ) * h ^ 2 < (floorHorizon T h : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    change 1 - ((floorHorizon T h : ℝ) / h ^ 2) / (T : ℝ) < _
    apply (lt_div_iff₀ (mul_pos hTr hh2)).mpr
    have heq : (1 - ((floorHorizon T h : ℝ) / h ^ 2) / (T : ℝ)) *
        ((T : ℝ) * h ^ 2) = (T : ℝ) * h ^ 2 - (floorHorizon T h : ℝ) := by
      field_simp [ne_of_gt hTr, ne_of_gt hh2]
    rw [heq]
    linarith

private theorem floorRatio_tendsto (T : ℝ≥0) (hT : 0 < T)
    (hSeq : ℕ → ℝ) (hpos : ∀ j, 0 < hSeq j)
    (hinfty : Tendsto hSeq atTop atTop) :
    Tendsto (fun j => floorRatio T (hSeq j) hT (hpos j)) atTop
      (𝓝 (1 : unitInterval)) := by
  have hi : Tendsto (fun j => (hSeq j)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hinfty
  have hb : Tendsto (fun j => 1 / ((T : ℝ) * hSeq j ^ 2)) atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_nhds.mul (hi.pow 2) :
      Tendsto (fun j => (T : ℝ)⁻¹ * ((hSeq j)⁻¹) ^ 2) atTop (𝓝 ((T : ℝ)⁻¹ * 0 ^ 2))) using 1
    · ext j
      simp [div_eq_mul_inv, mul_inv_rev, inv_pow, mul_comm]
    · simp
  have hz : Tendsto (fun j => 1 - (floorRatio T (hSeq j) hT (hpos j) : ℝ))
      atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun j => (floorRatio_error T (hSeq j) hT (hpos j)).1)
      (fun j => (floorRatio_error T (hSeq j) hT (hpos j)).2.le) hb
  apply tendsto_subtype_rng.mpr
  have ht : Tendsto (fun j => (1 : ℝ) -
      (1 - (floorRatio T (hSeq j) hT (hpos j) : ℝ))) atTop (𝓝 ((1 : ℝ) - 0)) :=
    tendsto_const_nhds.sub hz
  simpa only [sub_sub_cancel, sub_zero, Set.Icc.coe_one] using ht

private theorem row_event_terminal_adapter
    (T : ℝ≥0) (hT : 0 < T) (n : ℕ) (h : ℝ) (hh : 0 < h)
    (horizon : (T : ℝ) * h ^ 2 ≤ (n : ℝ)) (v : ℝ) (b : ℝ≥0)
    (a : Shao.Path n) :
    (a ∈ discreteClosedSurvival n (floorHorizon T h) h v b ↔
      stripGap (floorRatio T h hT hh, (v, (b : ℝ)))
        (PolygonalPathTightness.unitPolygonalPath T n h a) ≤ 0) ∧
    terminalCos (floorRatio T h hT hh, (v, (b : ℝ)))
      (PolygonalPathTightness.unitPolygonalPath T n h a) =
        Real.cos ((Real.pi / 2) * (v + Shao.prefixSum a (floorHorizon T h) / h)) := by
  let θ := floorRatio T h hT hh
  let t₀ : ℝ := (floorHorizon T h : ℝ) / h ^ 2
  let X := PolygonalPathTightness.unitPolygonalPath T n h a
  have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
  have hTr : 0 < (T : ℝ) := hT
  have ht₀ : 0 ≤ t₀ := div_nonneg (Nat.cast_nonneg _) hh2.le
  have hθ : (T : ℝ) * (θ : ℝ) = t₀ := by
    dsimp [θ, floorRatio, t₀]
    field_simp [ne_of_gt hTr]
  have hX (s : unitInterval) :
      X (scaleUnit θ s) = PolygonalThirdMoment.polygonalPath n h a (t₀ * (s : ℝ)) := by
    change PolygonalThirdMoment.polygonalPath n h a
      ((T : ℝ) * ((θ : ℝ) * (s : ℝ))) = _
    rw [← mul_assoc, hθ]
  constructor
  · rw [stripGap_nonpos_iff]
    constructor
    · intro he s
      have hp := (discreteClosedSurvival_iff_polygonal n (floorHorizon T h) h hh
        (floorHorizon_le T h n horizon) v b a).mp he
      rw [hX s]
      exact hp _ ⟨mul_nonneg ht₀ s.2.1,
        (mul_le_mul_of_nonneg_left s.2.2 ht₀).trans_eq (mul_one _)⟩
    · intro hg
      apply (discreteClosedSurvival_iff_polygonal n (floorHorizon T h) h hh
        (floorHorizon_le T h n horizon) v b a).mpr
      intro t ht
      by_cases hz : t₀ = 0
      · have ht0 : t = 0 := le_antisymm (by simpa [t₀, hz] using ht.2) ht.1
        have hg0 := hg (0 : unitInterval)
        rw [hX] at hg0
        simpa [ht0] using hg0
      · have htpos : 0 < t₀ := lt_of_le_of_ne ht₀ (Ne.symm hz)
        let s : unitInterval := ⟨t / t₀,
          ⟨div_nonneg ht.1 ht₀, (div_le_one htpos).mpr ht.2⟩⟩
        have hgs := hg s
        rw [hX] at hgs
        have hmul : t₀ * (s : ℝ) = t := by
          dsimp [s]
          field_simp [hz]
        simpa only [hmul] using hgs
  · have hxθ : X θ = PolygonalThirdMoment.polygonalPath n h a t₀ := by
      change PolygonalThirdMoment.polygonalPath n h a ((T : ℝ) * (θ : ℝ)) = _
      rw [hθ]
    change Real.cos ((Real.pi / 2) * (v + X θ)) = _
    rw [hxθ, PolygonalThirdMoment.polygonalPath_at_grid n h hh a
      (floorHorizon T h) (floorHorizon_le T h n horizon)]

private theorem uniform_parameter_on_compact
    (H : Parameters × PathSpace → ℝ) (hH : Continuous H)
    (pSeq : ℕ → Parameters) (p : Parameters)
    (hp : Tendsto pSeq atTop (𝓝 p)) (K : Set PathSpace) (hK : IsCompact K)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ f ∈ K, |H (pSeq j, f) - H (p, f)| < ε := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let HK (q : Parameters) : C(K, ℝ) :=
    ⟨fun f => H (q, f.1), hH.comp (continuous_const.prodMk continuous_subtype_val)⟩
  have hc : Continuous HK := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hH.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hconv : Tendsto (fun j => HK (pSeq j)) atTop (𝓝 (HK p)) :=
    (hc.tendsto p).comp hp
  filter_upwards [(Metric.tendsto_nhds.mp hconv) ε hε] with j hj f hf
  have hd : dist (HK (pSeq j) ⟨f, hf⟩) (HK p ⟨f, hf⟩) ≤
      dist (HK (pSeq j)) (HK p) := ContinuousMap.dist_apply_le_dist (⟨f, hf⟩ : K)
  exact lt_of_le_of_lt (by simpa [HK, Real.dist_eq] using hd) hj

private theorem tendsto_integral_varying_test
    (μSeq : ℕ → ProbabilityMeasure PathSpace) (μ : ProbabilityMeasure PathSpace)
    (hμ : Tendsto μSeq atTop (𝓝 μ))
    (htight : IsTightMeasureSet (Set.range (fun j => (μSeq j : Measure PathSpace))))
    (pSeq : ℕ → Parameters) (p : Parameters) (hp : Tendsto pSeq atTop (𝓝 p))
    (H : Parameters × PathSpace → ℝ) (hH : Continuous H)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ p f, |H (p, f)| ≤ C) :
    Tendsto (fun j => ∫ f, H (pSeq j, f) ∂(μSeq j : Measure PathSpace)) atTop
      (𝓝 (∫ f, H (p, f) ∂(μ : Measure PathSpace))) := by
  have hcont (q : Parameters) : Continuous (fun f => H (q, f)) :=
    hH.comp (continuous_const.prodMk continuous_id)
  have hint (q : Parameters) (ρ : ProbabilityMeasure PathSpace) :
      Integrable (fun f => H (q, f)) (ρ : Measure PathSpace) :=
    (integrable_const C).mono' (hcont q).aestronglyMeasurable
      (Filter.Eventually.of_forall fun f => by simpa [Real.norm_eq_abs] using hbound q f)
  let F : BoundedContinuousFunction PathSpace ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨fun f => H (p, f), hcont p⟩ (2 * C)
      (fun f g => by
        change |H (p, f) - H (p, g)| ≤ 2 * C
        exact (abs_sub (H (p, f)) (H (p, g))).trans
          (by linarith [hbound p f, hbound p g]))
  have hfixed : Tendsto (fun j => ∫ f, H (p, f) ∂(μSeq j : Measure PathSpace))
      atTop (𝓝 (∫ f, H (p, f) ∂(μ : Measure PathSpace))) := by
    simpa only [F, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk]
      using (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) F
  have hdiff : Tendsto (fun j => (∫ f, H (pSeq j, f) ∂(μSeq j : Measure PathSpace)) -
      ∫ f, H (p, f) ∂(μSeq j : Measure PathSpace)) atTop (𝓝 (0 : ℝ)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let δ : ℝ := ε / (4 * (C + 1))
    have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) (by linarith))
    obtain ⟨K, hK, htail⟩ :=
      isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight
        (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ)
    have hmK : MeasurableSet K := hK.isClosed.measurableSet
    filter_upwards [uniform_parameter_on_compact H hH pSeq p hp K hK (ε / 2)
      (half_pos hε)] with j hj
    have htailReal : (μSeq j : Measure PathSpace).real Kᶜ ≤ δ := by
      have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (htail (μSeq j : Measure PathSpace) ⟨j, rfl⟩)
      simpa only [MeasureTheory.measureReal_def, ENNReal.toReal_ofReal hδ.le] using hr
    let G : PathSpace → ℝ := fun f => ε / 2 + 2 * C * Kᶜ.indicator (fun _ => (1 : ℝ)) f
    have hGI : Integrable G (μSeq j : Measure PathSpace) :=
      (integrable_const (ε / 2)).add
        (((integrable_const (1 : ℝ)).indicator hmK.compl).const_mul (2 * C))
    have hpoint : ∀ f, ‖H (pSeq j, f) - H (p, f)‖ ≤ G f := by
      intro f
      by_cases hf : f ∈ K
      · simp only [G, Set.indicator_of_notMem (show f ∉ Kᶜ from by simpa), mul_zero, add_zero]
        simpa only [Real.norm_eq_abs] using (hj f hf).le
      · simp only [G, Set.indicator_of_mem (show f ∈ Kᶜ from hf), mul_one]
        have hd := abs_sub (H (pSeq j, f)) (H (p, f))
        rw [Real.norm_eq_abs]
        linarith [hbound (pSeq j) f, hbound p f]
    have hi := norm_integral_le_of_norm_le hGI (Filter.Eventually.of_forall hpoint)
    rw [integral_sub (hint (pSeq j) (μSeq j)) (hint p (μSeq j))] at hi
    have hGeq : (∫ f, G f ∂(μSeq j : Measure PathSpace)) =
        ε / 2 + 2 * C * (μSeq j : Measure PathSpace).real Kᶜ := by
      rw [show G = (fun f => ε / 2 +
        2 * C * Kᶜ.indicator (fun _ => (1 : ℝ)) f) from rfl,
        integral_add (integrable_const _)
          (((integrable_const (1 : ℝ)).indicator hmK.compl).const_mul _),
        integral_const_mul, integral_indicator hmK.compl, setIntegral_const]
      simp
    rw [hGeq] at hi
    have hnum : ε / 2 + 2 * C * δ < ε := by
      have heq : δ * (4 * (C + 1)) = ε := by
        dsimp [δ]
        exact div_mul_cancel₀ ε (by positivity : 4 * (C + 1) ≠ 0)
      nlinarith
    have htailBound : ε / 2 + 2 * C * (μSeq j : Measure PathSpace).real Kᶜ ≤
        ε / 2 + 2 * C * δ := by
      nlinarith [mul_le_mul_of_nonneg_left htailReal (by positivity : 0 ≤ 2 * C)]
    have hfinal := hi.trans_lt (htailBound.trans_lt hnum)
    simpa only [dist_zero_right, Real.norm_eq_abs] using hfinal
  convert hdiff.add hfixed using 1 <;> simp

private def cutoffWidth (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)
private def lowerCutoff (m : ℕ) (d : ℝ) : ℝ :=
  max 0 (min 1 (-d / cutoffWidth m))
private def upperCutoff (m : ℕ) (d : ℝ) : ℝ :=
  max 0 (min 1 (1 - d / cutoffWidth m))

private theorem continuous_lowerCutoff (m : ℕ) : Continuous (lowerCutoff m) := by
  unfold lowerCutoff
  fun_prop
private theorem continuous_upperCutoff (m : ℕ) : Continuous (upperCutoff m) := by
  unfold upperCutoff
  fun_prop

private theorem cutoff_bounds (m : ℕ) (d : ℝ) :
    0 ≤ lowerCutoff m d ∧
      lowerCutoff m d ≤ (if d ≤ 0 then (1 : ℝ) else 0) ∧
      (if d ≤ 0 then (1 : ℝ) else 0) ≤ upperCutoff m d ∧
      upperCutoff m d ≤ 1 ∧
      0 ≤ upperCutoff m d - lowerCutoff m d ∧
      upperCutoff m d - lowerCutoff m d ≤ 1 := by
  have hw : 0 < cutoffWidth m := by unfold cutoffWidth; positivity
  have hl0 : 0 ≤ lowerCutoff m d := le_max_left _ _
  have hu1 : upperCutoff m d ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have hlu : lowerCutoff m d ≤ upperCutoff m d := by
    apply max_le_max le_rfl
    apply min_le_min le_rfl
    simp only [neg_div]
    linarith
  have hli : lowerCutoff m d ≤ (if d ≤ 0 then (1 : ℝ) else 0) := by
    split_ifs with hd
    · exact max_le (by norm_num) (min_le_left _ _)
    · have hz : -d / cutoffWidth m ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le
      exact max_le le_rfl ((min_le_right _ _).trans hz)
  have hiu : (if d ≤ 0 then (1 : ℝ) else 0) ≤ upperCutoff m d := by
    split_ifs with hd
    · have hz : 0 ≤ -d / cutoffWidth m := div_nonneg (neg_nonneg.mpr hd) hw.le
      change 1 ≤ max 0 (min 1 (1 - d / cutoffWidth m))
      have hs : 1 ≤ 1 - d / cutoffWidth m := by
        have ht : d / cutoffWidth m ≤ 0 := div_nonpos_of_nonpos_of_nonneg hd hw.le
        linarith
      rw [min_eq_left hs, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
    · exact le_max_left _ _
  exact ⟨hl0, hli, hiu, hu1, sub_nonneg.mpr hlu, by linarith⟩

private theorem cutoff_limits (d : ℝ) :
    Tendsto (fun m => lowerCutoff m d) atTop (𝓝 (if d < 0 then (1 : ℝ) else 0)) ∧
      Tendsto (fun m => upperCutoff m d) atTop (𝓝 (if d ≤ 0 then (1 : ℝ) else 0)) ∧
      Tendsto (fun m => upperCutoff m d - lowerCutoff m d) atTop
        (𝓝 (if d = 0 then (1 : ℝ) else 0)) := by
  have hw : Tendsto cutoffWidth atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hwpos (m : ℕ) : 0 < cutoffWidth m := by unfold cutoffWidth; positivity
  have hlo : Tendsto (fun m => lowerCutoff m d) atTop
      (𝓝 (if d < 0 then (1 : ℝ) else 0)) := by
    by_cases hd : d < 0
    · have he : ∀ᶠ m in atTop, lowerCutoff m d = 1 := by
        filter_upwards [hw.eventually (eventually_lt_nhds (show (0 : ℝ) < -d by linarith))] with m hm
        have hb : 1 ≤ -d / cutoffWidth m := (le_div_iff₀ (hwpos m)).mpr (by linarith)
        simp [lowerCutoff, min_eq_left hb]
      simpa only [if_pos hd] using
        (tendsto_const_nhds.congr' (he.mono fun m hm => hm.symm))
    · have he : ∀ m, lowerCutoff m d = 0 := by
        intro m
        have hb : -d / cutoffWidth m ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) (hwpos m).le
        simp [lowerCutoff, max_eq_left ((min_le_right _ _).trans hb)]
      simpa only [if_neg hd, he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hup : Tendsto (fun m => upperCutoff m d) atTop
      (𝓝 (if d ≤ 0 then (1 : ℝ) else 0)) := by
    by_cases hd : d ≤ 0
    · have he (m : ℕ) : upperCutoff m d = 1 := by
        have hb : 1 ≤ 1 - d / cutoffWidth m := by
          have hz := div_nonpos_of_nonpos_of_nonneg hd (hwpos m).le
          linarith
        simp [upperCutoff, min_eq_left hb]
      simp only [if_pos hd, he]
      exact tendsto_const_nhds
    · have he : ∀ᶠ m in atTop, upperCutoff m d = 0 := by
        filter_upwards [hw.eventually (eventually_lt_nhds (show (0 : ℝ) < d by linarith))] with m hm
        have hb : 1 ≤ d / cutoffWidth m := (le_div_iff₀ (hwpos m)).mpr (by simpa using hm.le)
        have hz : 1 - d / cutoffWidth m ≤ 0 := by linarith
        simp [upperCutoff, max_eq_left ((min_le_right _ _).trans hz)]
      simpa only [if_neg hd] using
        (tendsto_const_nhds.congr' (he.mono fun m hm => hm.symm))
  refine ⟨hlo, hup, ?_⟩
  have heq : (if d ≤ 0 then (1 : ℝ) else 0) -
      (if d < 0 then (1 : ℝ) else 0) = (if d = 0 then (1 : ℝ) else 0) := by
    by_cases h0 : d = 0
    · subst d; norm_num
    · rcases lt_or_gt_of_ne h0 with hn | hp
      · simp [hn, hn.le, h0]
      · simp [not_le.mpr hp, not_lt.mpr hp.le, h0]
  simpa only [heq] using hup.sub hlo

set_option maxHeartbeats 2000000 in
private theorem tendsto_closed_functionals
    (μSeq : ℕ → ProbabilityMeasure PathSpace) (μ : ProbabilityMeasure PathSpace)
    (hμ : Tendsto μSeq atTop (𝓝 μ))
    (htight : IsTightMeasureSet (Set.range (fun j => (μSeq j : Measure PathSpace))))
    (pSeq : ℕ → Parameters) (p : Parameters) (hp : Tendsto pSeq atTop (𝓝 p))
    (hboundary : (μ : Measure PathSpace) {f | stripGap p f = 0} = 0) :
    Tendsto (fun j => (μSeq j : Measure PathSpace).real {f | stripGap (pSeq j) f ≤ 0})
      atTop (𝓝 ((μ : Measure PathSpace).real {f | stripGap p f ≤ 0})) ∧
    Tendsto (fun j => ∫ f,
      ({g | stripGap (pSeq j) g ≤ 0} : Set PathSpace).indicator
        (terminalCos (pSeq j)) f ∂(μSeq j : Measure PathSpace)) atTop
      (𝓝 (∫ f, ({g | stripGap p g ≤ 0} : Set PathSpace).indicator
        (terminalCos p) f ∂(μ : Measure PathSpace))) := by
  let S (q : Parameters) : Set PathSpace := {f | stripGap q f ≤ 0}
  let L (m : ℕ) (z : Parameters × PathSpace) := lowerCutoff m (stripGap z.1 z.2)
  let U (m : ℕ) (z : Parameters × PathSpace) := upperCutoff m (stripGap z.1 z.2)
  let A (m : ℕ) (z : Parameters × PathSpace) := L m z * terminalCos z.1 z.2
  let D (m : ℕ) (z : Parameters × PathSpace) := U m z - L m z
  have hSm (q : Parameters) : MeasurableSet (S q) :=
    measurableSet_le (continuous_stripGap.comp
      (continuous_const.prodMk continuous_id)).measurable measurable_const
  have hC (q : Parameters) : Continuous (terminalCos q) :=
    continuous_terminalCos.comp (continuous_const.prodMk continuous_id)
  have hcb (q : Parameters) (f : PathSpace) : |terminalCos q f| ≤ 1 :=
    Real.abs_cos_le_one _
  have hLC (m : ℕ) : Continuous (L m) :=
    (continuous_lowerCutoff m).comp continuous_stripGap
  have hUC (m : ℕ) : Continuous (U m) :=
    (continuous_upperCutoff m).comp continuous_stripGap
  have hAC (m : ℕ) : Continuous (A m) := (hLC m).mul continuous_terminalCos
  have hDC (m : ℕ) : Continuous (D m) := (hUC m).sub (hLC m)
  have hLB (m : ℕ) (q : Parameters) (f : PathSpace) : |L m (q, f)| ≤ 1 := by
    have hb := cutoff_bounds m (stripGap q f)
    rw [abs_of_nonneg hb.1]
    exact hb.2.1.trans (hb.2.2.1.trans hb.2.2.2.1)
  have hUB (m : ℕ) (q : Parameters) (f : PathSpace) : |U m (q, f)| ≤ 1 := by
    have hb := cutoff_bounds m (stripGap q f)
    rw [abs_of_nonneg (hb.1.trans (hb.2.1.trans hb.2.2.1))]
    exact hb.2.2.2.1
  have hAB (m : ℕ) (q : Parameters) (f : PathSpace) : |A m (q, f)| ≤ 1 := by
    calc
      |A m (q, f)| = |L m (q, f)| * |terminalCos q f| := abs_mul _ _
      _ ≤ 1 * 1 := mul_le_mul (hLB m q f) (hcb q f) (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hDB (m : ℕ) (q : Parameters) (f : PathSpace) : |D m (q, f)| ≤ 1 := by
    have hb := cutoff_bounds m (stripGap q f)
    rw [abs_of_nonneg hb.2.2.2.2.1]
    exact hb.2.2.2.2.2
  have hTI (F : Parameters × PathSpace → ℝ) (hF : Continuous F)
      (hb : ∀ q f, |F (q, f)| ≤ 1) (q : Parameters) (ρ : ProbabilityMeasure PathSpace) :
      Integrable (fun f => F (q, f)) (ρ : Measure PathSpace) :=
    (integrable_const (1 : ℝ)).mono'
      (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun f => by simpa [Real.norm_eq_abs] using hb q f)
  have hCI (q : Parameters) (ρ : ProbabilityMeasure PathSpace) :
      Integrable ((S q).indicator (terminalCos q)) (ρ : Measure PathSpace) := by
    have hi : Integrable (terminalCos q) (ρ : Measure PathSpace) :=
      (integrable_const (1 : ℝ)).mono' (hC q).aestronglyMeasurable
        (Filter.Eventually.of_forall fun f => by simpa [Real.norm_eq_abs] using hcb q f)
    exact hi.indicator (hSm q)
  have hne : ∀ᵐ f ∂(μ : Measure PathSpace), stripGap p f ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using hboundary
  have hlo (f : PathSpace) (hf : stripGap p f ≠ 0) :
      Tendsto (fun m => L m (p, f)) atTop
        (𝓝 ((S p).indicator (fun _ => (1 : ℝ)) f)) := by
    have heq : (if stripGap p f < 0 then (1 : ℝ) else 0) =
        (S p).indicator (fun _ => (1 : ℝ)) f := by
      have hiff : stripGap p f < 0 ↔ stripGap p f ≤ 0 :=
        ⟨le_of_lt, fun h => lt_of_le_of_ne h hf⟩
      simp only [S, Set.indicator, Set.mem_setOf_eq, hiff]
    simpa only [L, heq] using (cutoff_limits (stripGap p f)).1
  have hup (f : PathSpace) : Tendsto (fun m => U m (p, f)) atTop
      (𝓝 ((S p).indicator (fun _ => (1 : ℝ)) f)) := by
    simpa only [U, S, Set.indicator, Set.mem_setOf_eq] using
      (cutoff_limits (stripGap p f)).2.1
  have hd (f : PathSpace) (hf : stripGap p f ≠ 0) :
      Tendsto (fun m => D m (p, f)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [D, U, L, if_neg hf] using (cutoff_limits (stripGap p f)).2.2
  have hla : Tendsto (fun m => ∫ f, L m (p, f) ∂(μ : Measure PathSpace)) atTop
      (𝓝 ((μ : Measure PathSpace).real (S p))) := by
    have hh := tendsto_integral_of_dominated_convergence (μ := (μ : Measure PathSpace))
      (fun _ : PathSpace => (1 : ℝ))
      (fun m => (hLC m).comp (continuous_const.prodMk continuous_id) |>.aestronglyMeasurable)
      (integrable_const _) (fun m => Filter.Eventually.of_forall fun f => by
        simpa [Real.norm_eq_abs] using hLB m p f)
      (hne.mono fun f hf => hlo f hf)
    simpa only [Function.comp_apply, id_eq,
      integral_indicator_const (1 : ℝ) (hSm p), smul_eq_mul, mul_one] using hh
  have hua : Tendsto (fun m => ∫ f, U m (p, f) ∂(μ : Measure PathSpace)) atTop
      (𝓝 ((μ : Measure PathSpace).real (S p))) := by
    have hh := tendsto_integral_of_dominated_convergence (μ := (μ : Measure PathSpace))
      (fun _ : PathSpace => (1 : ℝ))
      (fun m => (hUC m).comp (continuous_const.prodMk continuous_id) |>.aestronglyMeasurable)
      (integrable_const _) (fun m => Filter.Eventually.of_forall fun f => by
        simpa [Real.norm_eq_abs] using hUB m p f)
      (Filter.Eventually.of_forall hup)
    simpa only [Function.comp_apply, id_eq,
      integral_indicator_const (1 : ℝ) (hSm p), smul_eq_mul, mul_one] using hh
  have hda : Tendsto (fun m => ∫ f, D m (p, f) ∂(μ : Measure PathSpace)) atTop
      (𝓝 (0 : ℝ)) := by
    have hh := tendsto_integral_of_dominated_convergence (μ := (μ : Measure PathSpace))
      (fun _ : PathSpace => (1 : ℝ))
      (fun m => (hDC m).comp (continuous_const.prodMk continuous_id) |>.aestronglyMeasurable)
      (integrable_const _) (fun m => Filter.Eventually.of_forall fun f => by
        simpa [Real.norm_eq_abs] using hDB m p f)
      (hne.mono fun f hf => hd f hf)
    simpa only [Function.comp_apply, id_eq, integral_zero] using hh
  have haa : Tendsto (fun m => ∫ f, A m (p, f) ∂(μ : Measure PathSpace)) atTop
      (𝓝 (∫ f, (S p).indicator (terminalCos p) f ∂(μ : Measure PathSpace))) := by
    apply tendsto_integral_of_dominated_convergence (μ := (μ : Measure PathSpace))
      (fun _ : PathSpace => (1 : ℝ))
      (fun m => (hAC m).comp (continuous_const.prodMk continuous_id) |>.aestronglyMeasurable)
      (integrable_const _) (fun m => Filter.Eventually.of_forall fun f => by
        simpa [Real.norm_eq_abs] using hAB m p f)
    filter_upwards [hne] with f hf
    have hx := (hlo f hf).mul (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => terminalCos p f) atTop (𝓝 (terminalCos p f)))
    by_cases hs : f ∈ S p
    · simpa only [A, Function.comp_apply, id_eq, Set.indicator_of_mem hs, one_mul] using hx
    · simpa only [A, Function.comp_apply, id_eq, Set.indicator_of_notMem hs, zero_mul] using hx
  have hmoveL (m : ℕ) := tendsto_integral_varying_test μSeq μ hμ htight pSeq p hp
    (L m) (hLC m) 1 (by norm_num) (hLB m)
  have hmoveU (m : ℕ) := tendsto_integral_varying_test μSeq μ hμ htight pSeq p hp
    (U m) (hUC m) 1 (by norm_num) (hUB m)
  have hmoveD (m : ℕ) := tendsto_integral_varying_test μSeq μ hμ htight pSeq p hp
    (D m) (hDC m) 1 (by norm_num) (hDB m)
  have hmoveA (m : ℕ) := tendsto_integral_varying_test μSeq μ hμ htight pSeq p hp
    (A m) (hAC m) 1 (by norm_num) (hAB m)
  have hbracket (m : ℕ) (q : Parameters) (ρ : ProbabilityMeasure PathSpace) :
      (∫ f, L m (q, f) ∂(ρ : Measure PathSpace)) ≤ (ρ : Measure PathSpace).real (S q) ∧
      (ρ : Measure PathSpace).real (S q) ≤ ∫ f, U m (q, f) ∂(ρ : Measure PathSpace) := by
    rw [← integral_indicator_one (hSm q)]
    constructor
    · apply integral_mono (hTI (L m) (hLC m) (hLB m) q ρ)
        ((integrable_const (1 : ℝ)).indicator (hSm q))
      intro f
      simpa only [L, S, Set.indicator, Set.mem_setOf_eq] using (cutoff_bounds m (stripGap q f)).2.1
    · apply integral_mono ((integrable_const (1 : ℝ)).indicator (hSm q))
        (hTI (U m) (hUC m) (hUB m) q ρ)
      intro f
      simpa only [U, S, Set.indicator, Set.mem_setOf_eq] using (cutoff_bounds m (stripGap q f)).2.2.1
  have herror (m : ℕ) (q : Parameters) (ρ : ProbabilityMeasure PathSpace) :
      |(∫ f, (S q).indicator (terminalCos q) f ∂(ρ : Measure PathSpace)) -
        ∫ f, A m (q, f) ∂(ρ : Measure PathSpace)| ≤
          ∫ f, D m (q, f) ∂(ρ : Measure PathSpace) := by
    rw [← integral_sub (hCI q ρ) (hTI (A m) (hAC m) (hAB m) q ρ)]
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le (hTI (D m) (hDC m) (hDB m) q ρ)
    apply Filter.Eventually.of_forall
    intro f
    have hb := cutoff_bounds m (stripGap q f)
    by_cases hs : f ∈ S q
    · have hg : stripGap q f ≤ 0 := hs
      have hu : U m (q, f) = 1 := le_antisymm hb.2.2.2.1 (by simpa [hg] using hb.2.2.1)
      have hl1 : L m (q, f) ≤ 1 := by simpa [hg] using hb.2.1
      simp only [Set.indicator_of_mem hs, A, D, hu, Real.norm_eq_abs]
      calc
        |terminalCos q f - L m (q, f) * terminalCos q f| =
          |1 - L m (q, f)| * |terminalCos q f| := by rw [← abs_mul]; congr 1; ring
        _ ≤ (1 - L m (q, f)) * 1 := by
          rw [abs_of_nonneg (sub_nonneg.mpr hl1)]
          exact mul_le_mul_of_nonneg_left (hcb q f) (sub_nonneg.mpr hl1)
        _ = 1 - L m (q, f) := mul_one _
    · have hg : ¬stripGap q f ≤ 0 := hs
      have hl : L m (q, f) = 0 := le_antisymm (by simpa [hg] using hb.2.1) hb.1
      simp only [Set.indicator_of_notMem hs, A, hl, zero_mul, sub_zero, norm_zero]
      exact hb.2.2.2.2.1
  constructor
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hthird : 0 < ε / 3 := div_pos hε (by norm_num)
    obtain ⟨m, hml, hmu⟩ := (((Metric.tendsto_nhds.mp hla) (ε / 3) hthird).and
      ((Metric.tendsto_nhds.mp hua) (ε / 3) hthird)).exists
    filter_upwards [(Metric.tendsto_nhds.mp (hmoveL m)) (ε / 3) hthird,
      (Metric.tendsto_nhds.mp (hmoveU m)) (ε / 3) hthird] with j hjl hju
    have hbj := hbracket m (pSeq j) (μSeq j)
    rw [Real.dist_eq] at hml hmu hjl hju ⊢
    apply abs_lt.mpr
    constructor
    · linarith [(abs_lt.mp hml).1, (abs_lt.mp hjl).1]
    · linarith [(abs_lt.mp hmu).2, (abs_lt.mp hju).2]
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hfourth : 0 < ε / 4 := div_pos hε (by norm_num)
    obtain ⟨m, hmd, hma⟩ := (((Metric.tendsto_nhds.mp hda) (ε / 4) hfourth).and
      ((Metric.tendsto_nhds.mp haa) (ε / 4) hfourth)).exists
    filter_upwards [(Metric.tendsto_nhds.mp (hmoveD m)) (ε / 4) hfourth,
      (Metric.tendsto_nhds.mp (hmoveA m)) (ε / 4) hfourth] with j hjd hja
    have he := herror m (pSeq j) (μSeq j)
    rw [Real.dist_eq] at hmd hma hjd hja ⊢
    have htri := abs_add_le
      ((∫ f, (S (pSeq j)).indicator (terminalCos (pSeq j)) f ∂(μSeq j : Measure PathSpace)) -
        ∫ f, A m (pSeq j, f) ∂(μSeq j : Measure PathSpace))
      ((∫ f, A m (pSeq j, f) ∂(μSeq j : Measure PathSpace)) -
        ∫ f, (S p).indicator (terminalCos p) f ∂(μ : Measure PathSpace))
    have htri2 := abs_add_le
      ((∫ f, A m (pSeq j, f) ∂(μSeq j : Measure PathSpace)) -
        ∫ f, A m (p, f) ∂(μ : Measure PathSpace))
      ((∫ f, A m (p, f) ∂(μ : Measure PathSpace)) -
        ∫ f, (S p).indicator (terminalCos p) f ∂(μ : Measure PathSpace))
    simp only [sub_add_sub_cancel] at htri htri2
    linarith [(abs_lt.mp hmd).2, (abs_lt.mp hma).2,
      (abs_lt.mp hjd).2, (abs_lt.mp hja).2]

-- Repackage the producer's actual law; do not copy/replace its literal path.
private def brownianPathLaw
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) : ProbabilityMeasure PathSpace :=
  ⟨PolygonalBrownianWeakLimit.brownianUnitPathLaw B T P,
    PolygonalBrownianWeakLimit.isProbabilityMeasure_brownianUnitPathLaw B T P hB⟩

private def rowPathLaw (T : ℝ≥0) (n : ℕ) (h : ℝ) (ν : Measure ℝ)
    (hprob : IsProbabilityMeasure ν) : ProbabilityMeasure PathSpace :=
  ⟨PolygonalPathTightness.polygonalPathLaw T n h ν,
    @PolygonalPathTightness.isProbabilityMeasure_polygonalPathLaw T n h ν hprob⟩

-- Concrete producer adapter, not an added hypothesis of either public theorem.
private theorem rowPathLaw_tendsto
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0)
    (nSeq : ℕ → ℕ) (hSeq : ℕ → ℝ) (νSeq : ℕ → Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (hpos : ∀ j, 0 < hSeq j)
    (horizon : ∀ j, (T : ℝ) * hSeq j ^ 2 ≤ (nSeq j : ℝ))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hinfty : Tendsto hSeq atTop atTop) :
    Tendsto (fun j => rowPathLaw T (nSeq j) (hSeq j) (νSeq j) (hprob j)) atTop
      (𝓝 (brownianPathLaw B P hB T)) := by
  letI : ∀ j, IsProbabilityMeasure (νSeq j) := hprob
  exact PolygonalBrownianWeakLimit.tendsto_polygonalPathLaw_brownianUnitPathLaw
    B T P hB νSeq h3 hmean hsecond M hM hSeq hpos hinfty nSeq horizon

private theorem brownian_identifications
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (hT : 0 < T)
    (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    ((brownianPathLaw B P hB T : Measure PathSpace)
      {f | stripGap ((1 : unitInterval), (u, (1 : ℝ))) f = 0} = 0) ∧
    ((brownianPathLaw B P hB T : Measure PathSpace).real
      {f | stripGap ((1 : unitInterval), (u, (1 : ℝ))) f ≤ 0} =
        P.real (BrownianSurvivalBoundary.closedSurvival B T u)) ∧
    ((∫ f,
      ({g | stripGap ((1 : unitInterval), (u, (1 : ℝ))) g ≤ 0} : Set PathSpace).indicator
        (terminalCos ((1 : unitInterval), (u, (1 : ℝ)))) f
          ∂(brownianPathLaw B P hB T : Measure PathSpace)) =
      ∫ ω, brownianKilledCosine B T u ω ∂P) := by
  let β := PolygonalBrownianWeakLimit.brownianUnitPath B T
  let p₀ : Parameters := ((1 : unitInterval), (u, (1 : ℝ)))
  let S : Set PathSpace := {f | stripGap p₀ f ≤ 0}
  have hTr : 0 < (T : ℝ) := hT
  have hβ : AEMeasurable β P :=
    PolygonalBrownianWeakLimit.aemeasurable_brownianUnitPath B T P hB
  have heq : ∀ᵐ ω ∂P, ∀ s : unitInterval,
      β ω s = B (T * ⟨(s : ℝ), s.2.1⟩) ω :=
    PolygonalBrownianWeakLimit.ae_brownianUnitPath_eq B T P hB
  have htime (t : ℝ≥0) (ht : t ≤ T) :
      ∃ s : unitInterval, T * ⟨(s : ℝ), s.2.1⟩ = t := by
    let s : unitInterval := ⟨(t : ℝ) / (T : ℝ),
      ⟨div_nonneg t.2 T.2, (div_le_one hTr).mpr (by exact_mod_cast ht)⟩⟩
    refine ⟨s, ?_⟩
    apply NNReal.coe_injective
    change (T : ℝ) * ((t : ℝ) / (T : ℝ)) = (t : ℝ)
    field_simp [ne_of_gt hTr]
  have htime_le (s : unitInterval) : (T * NNReal.mk (s : ℝ) s.2.1 : ℝ≥0) ≤ T := by
    have hs : (NNReal.mk (s : ℝ) s.2.1 : ℝ≥0) ≤ (1 : ℝ≥0) := s.2.2
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hs (show (0 : ℝ≥0) ≤ T from bot_le))
  have hscale (s : unitInterval) : scaleUnit (1 : unitInterval) s = s := by
    apply Subtype.ext
    simp [scaleUnit]
  have hreparam (f : PathSpace) : reparam (1 : unitInterval) f = f := by
    ext s
    change f (scaleUnit (1 : unitInterval) s) = f s
    rw [hscale]
  have hpath : ∀ᵐ ω ∂P,
      ‖ContinuousMap.const unitInterval u + β ω‖ = BrownianSurvivalBoundary.pathSup B T u ω ∧
      (β ω ∈ S ↔ ω ∈ BrownianSurvivalBoundary.closedSurvival B T u) ∧
      β ω (1 : unitInterval) = B T ω := by
    filter_upwards [heq] with ω hω
    have hrange : ((fun t : ℝ≥0 => |u + B t ω|) '' Icc (0 : ℝ≥0) T) =
        Set.range (fun s : unitInterval => |u + β ω s|) := by
      ext y
      constructor
      · rintro ⟨t, ht, rfl⟩
        obtain ⟨s, hs⟩ := htime t ht.2
        refine ⟨s, ?_⟩
        change |u + β ω s| = |u + B t ω|
        rw [hω s, hs]
      · rintro ⟨s, rfl⟩
        refine ⟨T * ⟨(s : ℝ), s.2.1⟩, ⟨bot_le, htime_le s⟩, ?_⟩
        change |u + B (T * ⟨(s : ℝ), s.2.1⟩) ω| = |u + β ω s|
        rw [hω s]
    have hnorm : ‖ContinuousMap.const unitInterval u + β ω‖ =
        BrownianSurvivalBoundary.pathSup B T u ω := by
      unfold BrownianSurvivalBoundary.pathSup
      rw [hrange, ContinuousMap.norm_eq_iSup_norm]
      change (⨆ s : unitInterval, |u + β ω s|) =
        sSup (Set.range (fun s : unitInterval => |u + β ω s|))
      rfl
    refine ⟨hnorm, ?_, ?_⟩
    · change stripGap p₀ (β ω) ≤ 0 ↔
        ∀ t : ℝ≥0, t ≤ T → |u + B t ω| ≤ 1
      rw [stripGap_nonpos_iff]
      change (∀ s : unitInterval, |u + β ω (scaleUnit (1 : unitInterval) s)| ≤ 1) ↔ _
      simp_rw [hscale, hω]
      constructor
      · intro hs t ht
        obtain ⟨s, hst⟩ := htime t ht
        simpa only [hst] using hs s
      · intro hs s
        exact hs _ (htime_le s)
    · have h1 : (T * NNReal.mk ((1 : unitInterval) : ℝ) (1 : unitInterval).2.1 : ℝ≥0) = T := by
        apply NNReal.coe_injective
        simp
      exact (hω (1 : unitInterval)).trans (congrArg (fun t : ℝ≥0 => B t ω) h1)
  have hS : MeasurableSet S := measurableSet_le
    (continuous_stripGap.comp (continuous_const.prodMk continuous_id)).measurable measurable_const
  have hZ : MeasurableSet {f : PathSpace | stripGap p₀ f = 0} :=
    (isClosed_eq (continuous_stripGap.comp (continuous_const.prodMk continuous_id))
      continuous_const).measurableSet
  have hpre : β ⁻¹' {f : PathSpace | stripGap p₀ f = 0} =ᵐ[P]
      {ω | BrownianSurvivalBoundary.pathSup B T u ω = 1} := by
    filter_upwards [hpath] with ω hω
    apply propext
    change (stripGap p₀ (β ω) = 0) ↔ _
    change (‖ContinuousMap.const unitInterval u + reparam (1 : unitInterval) (β ω)‖ - 1 = 0) ↔ _
    rw [hreparam, hω.1]
    exact sub_eq_zero
  have hnull : (brownianPathLaw B P hB T : Measure PathSpace)
      {f | stripGap p₀ f = 0} = 0 := by
    change (P.map β) {f | stripGap p₀ f = 0} = 0
    rw [Measure.map_apply_of_aemeasurable hβ hZ]
    exact (measure_congr hpre).trans
      (BrownianSurvivalBoundary.measure_pathSup_eq_one_eq_zero B P hB T hT u hu)
  have hprob : (brownianPathLaw B P hB T : Measure PathSpace).real S =
      P.real (BrownianSurvivalBoundary.closedSurvival B T u) := by
    change (P.map β).real S = _
    rw [map_measureReal_apply_of_aemeasurable hβ hS]
    apply measureReal_congr
    filter_upwards [hpath] with ω hω
    exact propext hω.2.1
  have hweight : (∫ f, S.indicator (terminalCos p₀) f
      ∂(brownianPathLaw B P hB T : Measure PathSpace)) =
        ∫ ω, brownianKilledCosine B T u ω ∂P := by
    have hF : AEStronglyMeasurable (S.indicator (terminalCos p₀)) (P.map β) :=
      ((continuous_terminalCos.comp (continuous_const.prodMk continuous_id)).measurable.indicator hS).aestronglyMeasurable
    change (∫ f, S.indicator (terminalCos p₀) f ∂P.map β) = _
    rw [integral_map hβ hF]
    apply integral_congr_ae
    filter_upwards [hpath] with ω hω
    have hc : terminalCos p₀ (β ω) = Real.cos ((Real.pi / 2) * (u + B T ω)) := by
      change Real.cos ((Real.pi / 2) * (u + β ω (1 : unitInterval))) = _
      rw [hω.2.2]
    by_cases hs : ω ∈ BrownianSurvivalBoundary.closedSurvival B T u
    · have hβs : β ω ∈ S := hω.2.1.mpr hs
      simp only [Set.indicator_of_mem hβs, brownianKilledCosine, Set.indicator_of_mem hs, hc]
    · have hβs : β ω ∉ S := (not_congr hω.2.1).mpr hs
      simp only [Set.indicator_of_notMem hβs, brownianKilledCosine, Set.indicator_of_notMem hs]
  exact ⟨hnull, hprob, hweight⟩

-- PUBLIC mandatory actual probability and weighted-integral limits.
-- No public weak-limit, tightness, boundary-null or desired-identity premise.
theorem discrete_survival_tendsto_brownian
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (hT : 0 < T)
    (nSeq : ℕ → ℕ) (hSeq : ℕ → ℝ) (νSeq : ℕ → Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (hpos : ∀ j, 0 < hSeq j)
    (horizon : ∀ j, (T : ℝ) * hSeq j ^ 2 ≤ (nSeq j : ℝ))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hinfty : Tendsto hSeq atTop atTop)
    (bSeq : ℕ → ℝ≥0) (hb : Tendsto bSeq atTop (𝓝 (1 : ℝ≥0)))
    (uSeq : ℕ → ℝ) (u : ℝ) (huSeq : Tendsto uSeq atTop (𝓝 u))
    (hu : u ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun j => (Measure.pi (fun _ : Fin (nSeq j) => νSeq j)).real
      (discreteClosedSurvival (nSeq j) (floorHorizon T (hSeq j))
        (hSeq j) (uSeq j) (bSeq j))) atTop
      (𝓝 (P.real (BrownianSurvivalBoundary.closedSurvival B T u))) := by
  let μSeq (j : ℕ) := rowPathLaw T (nSeq j) (hSeq j) (νSeq j) (hprob j)
  let μ := brownianPathLaw B P hB T
  let pSeq (j : ℕ) : Parameters :=
    (floorRatio T (hSeq j) hT (hpos j), (uSeq j, (bSeq j : ℝ)))
  let p : Parameters := ((1 : unitInterval), (u, (1 : ℝ)))
  have hμ : Tendsto μSeq atTop (𝓝 μ) :=
    rowPathLaw_tendsto B P hB T nSeq hSeq νSeq hprob hpos horizon h3 hmean hsecond M hM hinfty
  have htight : IsTightMeasureSet (Set.range (fun j => (μSeq j : Measure PathSpace))) :=
    PolygonalPathTightness.isTightMeasureSet_polygonalPathLaw
      T nSeq hSeq νSeq hprob hpos horizon h3 hmean M hM
  have hbR : Tendsto (fun j => (bSeq j : ℝ)) atTop (𝓝 (1 : ℝ)) :=
    (NNReal.continuous_coe.tendsto (1 : ℝ≥0)).comp hb
  have hp : Tendsto pSeq atTop (𝓝 p) :=
    (floorRatio_tendsto T hT hSeq hpos hinfty).prodMk_nhds (huSeq.prodMk_nhds hbR)
  have hi := brownian_identifications B P hB T hT u hu
  have hc := (tendsto_closed_functionals μSeq μ hμ htight pSeq p hp hi.1).1
  have hrow (j : ℕ) : (μSeq j : Measure PathSpace).real {f | stripGap (pSeq j) f ≤ 0} =
      (Measure.pi (fun _ : Fin (nSeq j) => νSeq j)).real
        (discreteClosedSurvival (nSeq j) (floorHorizon T (hSeq j))
          (hSeq j) (uSeq j) (bSeq j)) := by
    change ((Measure.pi (fun _ : Fin (nSeq j) => νSeq j)).map
      (PolygonalPathTightness.unitPolygonalPath T (nSeq j) (hSeq j))).real _ = _
    have hS : MeasurableSet {f : PathSpace | stripGap (pSeq j) f ≤ 0} :=
      measurableSet_le (continuous_stripGap.comp
        (continuous_const.prodMk continuous_id)).measurable measurable_const
    rw [map_measureReal_apply
      (PolygonalPathTightness.measurable_unitPolygonalPath T (nSeq j) (hSeq j)) hS]
    congr 1
    ext a
    exact (row_event_terminal_adapter T hT (nSeq j) (hSeq j) (hpos j)
      (horizon j) (uSeq j) (bSeq j) a).1.symm
  have hlimit : (μ : Measure PathSpace).real {f | stripGap p f ≤ 0} =
      P.real (BrownianSurvivalBoundary.closedSurvival B T u) := hi.2.1
  simpa only [hrow, hlimit] using hc

theorem discrete_killed_cosine_tendsto_brownian
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (hT : 0 < T)
    (nSeq : ℕ → ℕ) (hSeq : ℕ → ℝ) (νSeq : ℕ → Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (hpos : ∀ j, 0 < hSeq j)
    (horizon : ∀ j, (T : ℝ) * hSeq j ^ 2 ≤ (nSeq j : ℝ))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hinfty : Tendsto hSeq atTop atTop)
    (bSeq : ℕ → ℝ≥0) (hb : Tendsto bSeq atTop (𝓝 (1 : ℝ≥0)))
    (uSeq : ℕ → ℝ) (u : ℝ) (huSeq : Tendsto uSeq atTop (𝓝 u))
    (hu : u ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun j => ∫ a : Shao.Path (nSeq j),
      discreteKilledCosine (nSeq j) (floorHorizon T (hSeq j))
        (hSeq j) (uSeq j) (bSeq j) a
          ∂Measure.pi (fun _ : Fin (nSeq j) => νSeq j)) atTop
      (𝓝 (∫ ω, brownianKilledCosine B T u ω ∂P)) := by
  let μSeq (j : ℕ) := rowPathLaw T (nSeq j) (hSeq j) (νSeq j) (hprob j)
  let μ := brownianPathLaw B P hB T
  let pSeq (j : ℕ) : Parameters :=
    (floorRatio T (hSeq j) hT (hpos j), (uSeq j, (bSeq j : ℝ)))
  let p : Parameters := ((1 : unitInterval), (u, (1 : ℝ)))
  have hμ : Tendsto μSeq atTop (𝓝 μ) :=
    rowPathLaw_tendsto B P hB T nSeq hSeq νSeq hprob hpos horizon h3 hmean hsecond M hM hinfty
  have htight : IsTightMeasureSet (Set.range (fun j => (μSeq j : Measure PathSpace))) :=
    PolygonalPathTightness.isTightMeasureSet_polygonalPathLaw
      T nSeq hSeq νSeq hprob hpos horizon h3 hmean M hM
  have hbR : Tendsto (fun j => (bSeq j : ℝ)) atTop (𝓝 (1 : ℝ)) :=
    (NNReal.continuous_coe.tendsto (1 : ℝ≥0)).comp hb
  have hp : Tendsto pSeq atTop (𝓝 p) :=
    (floorRatio_tendsto T hT hSeq hpos hinfty).prodMk_nhds (huSeq.prodMk_nhds hbR)
  have hi := brownian_identifications B P hB T hT u hu
  have hc := (tendsto_closed_functionals μSeq μ hμ htight pSeq p hp hi.1).2
  have hrow (j : ℕ) :
      (∫ f, ({g | stripGap (pSeq j) g ≤ 0} : Set PathSpace).indicator
        (terminalCos (pSeq j)) f ∂(μSeq j : Measure PathSpace)) =
      ∫ a : Shao.Path (nSeq j),
        discreteKilledCosine (nSeq j) (floorHorizon T (hSeq j))
          (hSeq j) (uSeq j) (bSeq j) a
            ∂Measure.pi (fun _ : Fin (nSeq j) => νSeq j) := by
    let S : Set PathSpace := {f | stripGap (pSeq j) f ≤ 0}
    have hS : MeasurableSet S := measurableSet_le
      (continuous_stripGap.comp (continuous_const.prodMk continuous_id)).measurable measurable_const
    have hF : AEStronglyMeasurable (S.indicator (terminalCos (pSeq j)))
        (μSeq j : Measure PathSpace) :=
      ((continuous_terminalCos.comp (continuous_const.prodMk continuous_id)).measurable.indicator hS).aestronglyMeasurable
    change (∫ f, S.indicator (terminalCos (pSeq j)) f
      ∂(Measure.pi (fun _ : Fin (nSeq j) => νSeq j)).map
        (PolygonalPathTightness.unitPolygonalPath T (nSeq j) (hSeq j))) = _
    rw [integral_map
      (PolygonalPathTightness.measurable_unitPolygonalPath T (nSeq j) (hSeq j)).aemeasurable hF]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro a
    have ha := row_event_terminal_adapter T hT (nSeq j) (hSeq j) (hpos j)
      (horizon j) (uSeq j) (bSeq j) a
    by_cases he : a ∈ discreteClosedSurvival (nSeq j) (floorHorizon T (hSeq j))
        (hSeq j) (uSeq j) (bSeq j)
    · have hs : PolygonalPathTightness.unitPolygonalPath T (nSeq j) (hSeq j) a ∈ S := ha.1.mp he
      simp only [Set.indicator_of_mem hs, discreteKilledCosine, Set.indicator_of_mem he]
      exact ha.2
    · have hs : PolygonalPathTightness.unitPolygonalPath T (nSeq j) (hSeq j) a ∉ S :=
        fun hs => he (ha.1.mpr hs)
      simp only [Set.indicator_of_notMem hs, discreteKilledCosine, Set.indicator_of_notMem he]
  have hlimit : (∫ f, ({g | stripGap p g ≤ 0} : Set PathSpace).indicator
      (terminalCos p) f ∂(μ : Measure PathSpace)) =
      ∫ ω, brownianKilledCosine B T u ω ∂P := hi.2.2
  simpa only [hrow, hlimit] using hc

end Shao.OQ4.PolygonalKilledFunctionalLimit

end
