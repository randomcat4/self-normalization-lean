-- Exact lane-lead formal freeze: all46 declaration heads and10 literal definition values.
-- Mathematical proof and pinned APIs fully read before this freeze; no premise delta.
import Shao.OQ4.RowPolygonalFDD
import Shao.OQ4.PolygonalPathTightness
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UnitInterval
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

namespace Shao.OQ4.PolygonalBrownianWeakLimit

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators NNReal Classical BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

-- Private deterministic definitions/heads (10 definitions total in the whole inventory,
-- including the public definitions below; no new structures/instances are proposed).

private def unitTime (T : ℝ≥0) (u : unitInterval) : ℝ≥0 :=
  T * ⟨(u : ℝ), u.property.1⟩

private theorem continuous_unitTime (T : ℝ≥0) : Continuous (unitTime T) := by
  unfold unitTime
  exact continuous_const.mul (continuous_subtype_val.subtype_mk _)

private theorem gridPoint_mem (n : ℕ) (i : Fin (n + 2)) :
    (i.val : ℝ) / ((n + 1 : ℕ) : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  refine ⟨div_nonneg (Nat.cast_nonneg _) hn.le, (div_le_one hn).mpr ?_⟩
  exact_mod_cast (show i.val ≤ n + 1 by omega)

private def gridPoint (n : ℕ) (i : Fin (n + 2)) : unitInterval :=
  ⟨(i.val : ℝ) / ((n + 1 : ℕ) : ℝ), gridPoint_mem n i⟩

private def gridRamp (n : ℕ) (i : Fin (n + 1)) (u : unitInterval) : ℝ :=
  max 0 (min 1 (((n + 1 : ℕ) : ℝ) * (u : ℝ) - (i.val : ℝ)))

private theorem continuous_gridInterpolate_value
    (n : ℕ) (v : Fin (n + 2) → ℝ) :
    Continuous (fun u : unitInterval =>
      v 0 + ∑ i : Fin (n + 1), (v i.succ - v i.castSucc) * gridRamp n i u) := by
  unfold gridRamp
  fun_prop

private def gridInterpolate (n : ℕ) (v : Fin (n + 2) → ℝ) :
    C(unitInterval, ℝ) :=
  ⟨fun u => v 0 + ∑ i : Fin (n + 1),
      (v i.succ - v i.castSucc) * gridRamp n i u,
    continuous_gridInterpolate_value n v⟩

private def gridEval (n : ℕ) (f : C(unitInterval, ℝ)) : Fin (n + 2) → ℝ :=
  fun i => f (gridPoint n i)

private def gridReconstruct (n : ℕ) (f : C(unitInterval, ℝ)) :
    C(unitInterval, ℝ) :=
  gridInterpolate n (gridEval n f)

private theorem exists_gridSegment (n : ℕ) (u : unitInterval) :
    ∃ i : Fin (n + 1),
      (i.val : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * (u : ℝ) ∧
      ((n + 1 : ℕ) : ℝ) * (u : ℝ) ≤ (i.val : ℝ) + 1 := by
  let x : ℝ := ((n + 1 : ℕ) : ℝ) * (u : ℝ)
  have hx0 : 0 ≤ x := mul_nonneg (Nat.cast_nonneg _) u.property.1
  have hxr : x ≤ ((n + 1 : ℕ) : ℝ) := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left u.property.2 (Nat.cast_nonneg (n + 1) : (0 : ℝ) ≤ _)
  by_cases hlt : x < ((n + 1 : ℕ) : ℝ)
  · let i : Fin (n + 1) := ⟨Nat.floor x, (Nat.floor_lt hx0).mpr hlt⟩
    exact ⟨i, Nat.floor_le hx0, (Nat.lt_floor_add_one x).le⟩
  · refine ⟨⟨n, by omega⟩, ?_, ?_⟩
    · dsimp [x] at *
      have hn : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
      exact hn.trans (le_of_not_gt hlt)
    · simpa only [x, Nat.cast_add, Nat.cast_one] using hxr

private theorem gridInterpolate_segment
    (n : ℕ) (v : Fin (n + 2) → ℝ) (u : unitInterval) (i : Fin (n + 1))
    (hleft : (i.val : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * (u : ℝ))
    (hright : ((n + 1 : ℕ) : ℝ) * (u : ℝ) ≤ (i.val : ℝ) + 1) :
    gridInterpolate n v u =
      (1 - (((n + 1 : ℕ) : ℝ) * (u : ℝ) - (i.val : ℝ))) * v i.castSucc +
      (((n + 1 : ℕ) : ℝ) * (u : ℝ) - (i.val : ℝ)) * v i.succ := by
  classical
  let x : ℝ := ((n + 1 : ℕ) : ℝ) * (u : ℝ)
  let θ : ℝ := x - (i.val : ℝ)
  have hθ0 : 0 ≤ θ := sub_nonneg.mpr hleft
  have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith
  have hterm (k : Fin (n + 1)) :
      (v k.succ - v k.castSucc) * gridRamp n k u =
        (if k.val < i.val then v k.succ - v k.castSucc else 0) +
        (if k = i then (v i.succ - v i.castSucc) * θ else 0) := by
    by_cases hki : k.val < i.val
    · have hne : k ≠ i := by intro h; subst h; omega
      have hcast : (k.val : ℝ) + 1 ≤ (i.val : ℝ) := by
        exact_mod_cast (show k.val + 1 ≤ i.val by omega)
      have hone : 1 ≤ x - (k.val : ℝ) := by linarith
      have hramp : gridRamp n k u = 1 := by
        change max 0 (min 1 (x - (k.val : ℝ))) = 1
        rw [min_eq_left hone, max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)]
      simp only [hramp, if_pos hki, if_neg hne, mul_one, add_zero]
    · by_cases heq : k = i
      · subst k
        have hramp : gridRamp n i u = θ := by
          change max 0 (min 1 θ) = θ
          rw [min_eq_right hθ1, max_eq_right hθ0]
        simp only [hramp, lt_self_iff_false, ite_false, ite_true, zero_add]
      · have hlt : i.val < k.val := by
          have hval : k.val ≠ i.val := by intro h; exact heq (Fin.ext h)
          omega
        have hcast : (i.val : ℝ) + 1 ≤ (k.val : ℝ) := by
          exact_mod_cast (show i.val + 1 ≤ k.val by omega)
        have hzero : x - (k.val : ℝ) ≤ 0 := by linarith
        have hramp : gridRamp n k u = 0 := by
          change max 0 (min 1 (x - (k.val : ℝ))) = 0
          exact max_eq_left ((min_le_right _ _).trans hzero)
        simp [hramp, hki, heq]
  have htel (q : ℕ) (hq : q ≤ n + 1) :
      (∑ k ∈ Finset.univ.filter (fun k : Fin (n + 1) => k.val < q),
        (v k.succ - v k.castSucc)) =
        v ⟨q, by omega⟩ - v 0 := by
    induction q with
    | zero => simp
    | succ q ih =>
      let k : Fin (n + 1) := ⟨q, by omega⟩
      have heq : Finset.univ.filter (fun j : Fin (n + 1) => j.val < q + 1) =
          insert k (Finset.univ.filter (fun j : Fin (n + 1) => j.val < q)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hj
          by_cases h : j.val = q
          · exact Or.inl (Fin.ext h)
          · exact Or.inr (by omega)
        · rintro (rfl | hj)
          · simp [k]
          · omega
      rw [heq, Finset.sum_insert (by simp [k]), ih (by omega)]
      change (v k.succ - v k.castSucc) + (v k.castSucc - v 0) = v k.succ - v 0
      ring
  have hs : (∑ k : Fin (n + 1),
      if k.val < i.val then v k.succ - v k.castSucc else 0) =
      v i.castSucc - v 0 := by
    have hi : (⟨i.val, by omega⟩ : Fin (n + 2)) = i.castSucc := Fin.ext rfl
    simpa only [Finset.sum_filter, hi] using htel i.val (by omega)
  change v 0 + ∑ k : Fin (n + 1),
    (v k.succ - v k.castSucc) * gridRamp n k u = _
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_add_distrib, hs]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  dsimp [θ, x]
  ring

private theorem lipschitzWith_gridInterpolate (n : ℕ) :
    LipschitzWith 1 (gridInterpolate n) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul]
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro u
  obtain ⟨i, hleft, hright⟩ := exists_gridSegment n u
  rw [gridInterpolate_segment n v u i hleft hright,
    gridInterpolate_segment n w u i hleft hright]
  let θ : ℝ := ((n + 1 : ℕ) : ℝ) * (u : ℝ) - (i.val : ℝ)
  have hθ0 : 0 ≤ θ := sub_nonneg.mpr hleft
  have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith
  have hv0 : |v i.castSucc - w i.castSucc| ≤ dist v w := by
    simpa only [Real.dist_eq] using
      (dist_pi_le_iff (f := v) (g := w) dist_nonneg).mp le_rfl i.castSucc
  have hv1 : |v i.succ - w i.succ| ≤ dist v w := by
    simpa only [Real.dist_eq] using
      (dist_pi_le_iff (f := v) (g := w) dist_nonneg).mp le_rfl i.succ
  change |(1 - θ) * v i.castSucc + θ * v i.succ -
    ((1 - θ) * w i.castSucc + θ * w i.succ)| ≤ dist v w
  calc
    _ = |(1 - θ) * (v i.castSucc - w i.castSucc) +
        θ * (v i.succ - w i.succ)| := by congr 1; ring
    _ ≤ |(1 - θ) * (v i.castSucc - w i.castSucc)| +
        |θ * (v i.succ - w i.succ)| := abs_add_le _ _
    _ = (1 - θ) * |v i.castSucc - w i.castSucc| +
        θ * |v i.succ - w i.succ| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hθ1), abs_of_nonneg hθ0]
    _ ≤ (1 - θ) * dist v w + θ * dist v w :=
      add_le_add (mul_le_mul_of_nonneg_left hv0 (sub_nonneg.mpr hθ1))
        (mul_le_mul_of_nonneg_left hv1 hθ0)
    _ = dist v w := by ring

private theorem continuous_gridInterpolate (n : ℕ) :
    Continuous (gridInterpolate n) := (lipschitzWith_gridInterpolate n).continuous

private theorem continuous_gridEval (n : ℕ) : Continuous (gridEval n) := by
  exact continuous_pi (fun i => continuous_eval_const (gridPoint n i))

private theorem lipschitzWith_gridReconstruct (n : ℕ) :
    LipschitzWith 1 (gridReconstruct n) := by
  have he : LipschitzWith 1 (gridEval n) := by
    apply LipschitzWith.of_dist_le_mul
    intro f g
    simp only [NNReal.coe_one, one_mul]
    exact (dist_pi_le_iff dist_nonneg).mpr fun i =>
      ContinuousMap.dist_apply_le_dist (gridPoint n i)
  unfold gridReconstruct
  simpa only [one_mul, Function.comp_def] using
    (lipschitzWith_gridInterpolate n).comp he

private theorem continuous_gridReconstruct (n : ℕ) :
    Continuous (gridReconstruct n) := (lipschitzWith_gridReconstruct n).continuous

private theorem gridReconstruct_tendsto (f : C(unitInterval, ℝ)) :
    Tendsto (fun n : ℕ => gridReconstruct n f) atTop (𝓝 f) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have huc := CompactSpace.uniformContinuous_of_continuous f.continuous
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.mp huc (ε / 2) (half_pos hε)
  have hmeshlim : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hmeshlim δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have hr : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hm : 1 / ((n + 1 : ℕ) : ℝ) < δ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ 1 / ((n + 1 : ℕ) : ℝ))] using hN n hn
  apply lt_of_le_of_lt ((ContinuousMap.dist_le (half_pos hε).le).mpr ?_) (half_lt_self hε)
  intro u
  obtain ⟨i, hleft, hright⟩ := exists_gridSegment n u
  let a : unitInterval := gridPoint n i.castSucc
  let b : unitInterval := gridPoint n i.succ
  have ha : (a : ℝ) ≤ (u : ℝ) := by
    change (i.val : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ (u : ℝ)
    exact (div_le_iff₀ hr).mpr (by simpa only [mul_comm] using hleft)
  have hb : (u : ℝ) ≤ (b : ℝ) := by
    change (u : ℝ) ≤ ((i.val + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)
    apply (le_div_iff₀ hr).mpr
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using hright
  have har : (a : ℝ) * ((n + 1 : ℕ) : ℝ) = (i.val : ℝ) := by
    dsimp [a, gridPoint]
    exact div_mul_cancel₀ _ (ne_of_gt hr)
  have hbr : (b : ℝ) * ((n + 1 : ℕ) : ℝ) = (i.val : ℝ) + 1 := by
    dsimp [b, gridPoint]
    rw [div_mul_cancel₀ _ (ne_of_gt hr)]
    simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
  have hda : dist a u ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ha)]
    apply (le_div_iff₀ hr).mpr
    nlinarith
  have hdb : dist b u ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hb)]
    apply (le_div_iff₀ hr).mpr
    nlinarith
  have hva : |f a - f u| ≤ ε / 2 :=
    (show dist (f a) (f u) < ε / 2 from hfδ (hda.trans_lt hm)).le
  have hvb : |f b - f u| ≤ ε / 2 :=
    (show dist (f b) (f u) < ε / 2 from hfδ (hdb.trans_lt hm)).le
  let θ : ℝ := ((n + 1 : ℕ) : ℝ) * (u : ℝ) - (i.val : ℝ)
  have hθ0 : 0 ≤ θ := sub_nonneg.mpr hleft
  have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith
  change |gridInterpolate n (gridEval n f) u - f u| ≤ ε / 2
  rw [gridInterpolate_segment n (gridEval n f) u i hleft hright]
  change |(1 - θ) * f a + θ * f b - f u| ≤ ε / 2
  calc
    _ = |(1 - θ) * (f a - f u) + θ * (f b - f u)| := by congr 1; ring
    _ ≤ |(1 - θ) * (f a - f u)| + |θ * (f b - f u)| := abs_add_le _ _
    _ = (1 - θ) * |f a - f u| + θ * |f b - f u| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hθ1), abs_of_nonneg hθ0]
    _ ≤ (1 - θ) * (ε / 2) + θ * (ε / 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hva (sub_nonneg.mpr hθ1))
        (mul_le_mul_of_nonneg_left hvb hθ0)
    _ = ε / 2 := by ring

private theorem gridReconstruct_uniform_compact
    (K : Set C(unitInterval, ℝ)) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ f ∈ K, dist (gridReconstruct n f) f < ε := by
  classical
  obtain ⟨s, hsK, hcover⟩ := hK.elim_nhds_subcover
    (fun f => Metric.ball f (ε / 4))
    (fun f _ => Metric.ball_mem_nhds f (by positivity))
  have hs : ∀ᶠ n : ℕ in atTop, ∀ g ∈ s, dist (gridReconstruct n g) g < ε / 4 := by
    apply (Filter.eventually_all_finset s).mpr
    intro g _
    exact Metric.tendsto_nhds.mp (gridReconstruct_tendsto g) (ε / 4) (by positivity)
  filter_upwards [hs] with n hn f hf
  obtain ⟨g, hgs, hfg⟩ := Set.mem_iUnion₂.mp (hcover hf)
  have hfg' : dist f g < ε / 4 := hfg
  have hR : dist (gridReconstruct n f) (gridReconstruct n g) ≤ dist f g := by
    simpa only [NNReal.coe_one, one_mul] using
      (lipschitzWith_gridReconstruct n).dist_le_mul f g
  have ht := dist_triangle (gridReconstruct n f) (gridReconstruct n g) f
  have ht' := dist_triangle (gridReconstruct n g) g f
  rw [dist_comm g f] at ht'
  have hg := hn g hgs
  linarith

private theorem boundedContinuous_gridReconstruct_uniform_compact
    (F : C(unitInterval, ℝ) →ᵇ ℝ)
    (K : Set C(unitInterval, ℝ)) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ f ∈ K, |F (gridReconstruct n f) - F f| < ε := by
  have hnear := hK.uniformContinuousAt_of_continuousAt F
    (fun f _ => F.continuous.continuousAt) (Metric.dist_mem_uniformity hε)
  obtain ⟨δ, hδ, hδF⟩ := Metric.mem_uniformity_dist.mp hnear
  filter_upwards [gridReconstruct_uniform_compact K hK δ hδ] with n hn f hf
  have hclose : dist f (gridReconstruct n f) < δ := by simpa only [dist_comm] using hn f hf
  have h := hδF hclose hf
  change dist (F f) (F (gridReconstruct n f)) < ε at h
  simpa only [Real.dist_eq, abs_sub_comm] using h

-- Public actual observable and its law. These are the only public definitions.
-- The value of brownianUnitPath is the literal conditional required by the freeze.

def brownianUnitPath {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    C(unitInterval, ℝ) :=
  if hc : Continuous (fun u : unitInterval => B (unitTime T u) ω) then
    ⟨fun u => B (unitTime T u) ω, hc⟩
  else 0

def brownianUnitPathLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (P : Measure Ω) :
    Measure C(unitInterval, ℝ) :=
  P.map (brownianUnitPath B T)

private def brownianGridApprox {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    C(unitInterval, ℝ) :=
  gridInterpolate n (fun i => B (unitTime T (gridPoint n i)) ω)

private theorem brownianUnitPath_apply_of_continuous {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω)
    (hc : Continuous (fun u : unitInterval => B (unitTime T u) ω))
    (u : unitInterval) :
    brownianUnitPath B T ω u = B (unitTime T u) ω := by
  simp only [brownianUnitPath, dif_pos hc, ContinuousMap.coe_mk]

theorem ae_brownianUnitPath_eq {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (P : Measure Ω)
    [IsProbabilityMeasure P] (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ u : unitInterval,
      brownianUnitPath B T ω u = B (unitTime T u) ω := by
  filter_upwards [hB.cont] with ω hω
  intro u
  exact brownianUnitPath_apply_of_continuous B T ω
    (hω.comp (continuous_unitTime T)) u

private theorem aemeasurable_brownianGridApprox {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (P : Measure Ω)
    [IsProbabilityMeasure P] (hB : IsBrownianReal B P) (n : ℕ) :
    AEMeasurable (brownianGridApprox B T n) P := by
  exact (continuous_gridInterpolate n).measurable.comp_aemeasurable
    (AEMeasurable.of_eval fun i => hB.toIsPreBrownianReal.aemeasurable
      (unitTime T (gridPoint n i)))

private theorem ae_tendsto_brownianGridApprox {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (P : Measure Ω)
    [IsProbabilityMeasure P] (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => brownianGridApprox B T n ω) atTop
      (𝓝 (brownianUnitPath B T ω)) := by
  filter_upwards [ae_brownianUnitPath_eq B T P hB] with ω hω
  have heq (n : ℕ) : brownianGridApprox B T n ω =
      gridReconstruct n (brownianUnitPath B T ω) := by
    unfold brownianGridApprox gridReconstruct gridEval
    congr 1
    funext i
    exact (hω (gridPoint n i)).symm
  simpa only [heq] using gridReconstruct_tendsto (brownianUnitPath B T ω)

theorem aemeasurable_brownianUnitPath {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (P : Measure Ω)
    [IsProbabilityMeasure P] (hB : IsBrownianReal B P) :
    AEMeasurable (brownianUnitPath B T) P := by
  exact aemeasurable_of_tendsto_metrizable_ae'
    (aemeasurable_brownianGridApprox B T P hB) (ae_tendsto_brownianGridApprox B T P hB)

theorem isProbabilityMeasure_brownianUnitPathLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (P : Measure Ω)
    [IsProbabilityMeasure P] (hB : IsBrownianReal B P) :
    IsProbabilityMeasure (brownianUnitPathLaw B T P) := by
  exact (Measure.isProbabilityMeasure_map_iff (aemeasurable_brownianUnitPath B T P hB)).mpr
    inferInstance

-- Actual cumulative-time Brownian Gaussian law. These helpers reprove only
-- elementary prefix identities, not accepted producer proofs.

private theorem durationPrefix_zero {m : ℕ} (D : Fin m → ℝ≥0) :
    RowPolygonalFDD.durationPrefix D 0 = 0 := by
  simp [RowPolygonalFDD.durationPrefix]

private theorem durationPrefix_succ {m : ℕ} (D : Fin m → ℝ≥0) (k : Fin m) :
    RowPolygonalFDD.durationPrefix D (k.val + 1) =
      RowPolygonalFDD.durationPrefix D k.val + D k := by
  classical
  have heq : Finset.univ.filter (fun i : Fin m => i.val < k.val + 1) =
      insert k (Finset.univ.filter (fun i : Fin m => i.val < k.val)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hi
      by_cases hik : i.val = k.val
      · exact Or.inl (Fin.ext hik)
      · exact Or.inr (by omega)
    · rintro (rfl | hi) <;> omega
  unfold RowPolygonalFDD.durationPrefix
  rw [heq, Finset.sum_insert (by simp), add_comm]

private theorem durationPrefix_mono {m : ℕ} (D : Fin m → ℝ≥0) :
    Monotone (RowPolygonalFDD.durationPrefix D) := by
  intro q r hqr
  unfold RowPolygonalFDD.durationPrefix
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by intro k hk; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *; omega)
    (fun _ _ _ => bot_le)

private theorem cumulative_brownian_increments {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (m : ℕ) (D : Fin m → ℝ≥0) (ω : Ω) (k : Fin m) :
    RowPolygonalFDD.cumulativeMap m
      (fun i => B (RowPolygonalFDD.durationPrefix D (i.val + 1)) ω -
        B (RowPolygonalFDD.durationPrefix D i.val) ω) k =
      B (RowPolygonalFDD.observationTime D k) ω - B 0 ω := by
  classical
  have htel (q : ℕ) (hq : q ≤ m) :
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < q),
        (B (RowPolygonalFDD.durationPrefix D (i.val + 1)) ω -
          B (RowPolygonalFDD.durationPrefix D i.val) ω)) =
        B (RowPolygonalFDD.durationPrefix D q) ω - B 0 ω := by
    induction q with
    | zero => simp [durationPrefix_zero]
    | succ q ih =>
      let j : Fin m := ⟨q, by omega⟩
      have heq : Finset.univ.filter (fun i : Fin m => i.val < q + 1) =
          insert j (Finset.univ.filter (fun i : Fin m => i.val < q)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hi
          by_cases h : i.val = q
          · exact Or.inl (Fin.ext h)
          · exact Or.inr (by omega)
        · rintro (rfl | hi)
          · simp [j]
          · omega
      rw [heq, Finset.sum_insert (by simp [j]), ih (by omega)]
      simp only [j]
      ring
  exact htel (k.val + 1) (by omega)

private theorem brownian_increment_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (m : ℕ) (D : Fin m → ℝ≥0) (k : Fin m) :
    HasLaw (fun ω => B (RowPolygonalFDD.durationPrefix D (k.val + 1)) ω -
      B (RowPolygonalFDD.durationPrefix D k.val) ω)
      (gaussianReal 0 (D k)) P := by
  have h := hB.toIsPreBrownianReal.hasLaw_sub
    (RowPolygonalFDD.durationPrefix D (k.val + 1))
    (RowPolygonalFDD.durationPrefix D k.val)
  have hdist : nndist
      ((RowPolygonalFDD.durationPrefix D (k.val + 1) : ℝ≥0) : ℝ)
      ((RowPolygonalFDD.durationPrefix D k.val : ℝ≥0) : ℝ) = D k := by
    apply NNReal.coe_injective
    simp only [coe_nndist, Real.dist_eq, durationPrefix_succ, NNReal.coe_add,
      add_sub_cancel_left]
    exact abs_of_nonneg (NNReal.coe_nonneg _)
  convert h using 1 <;>
    first | rfl | exact hdist.symm | exact congrArg (gaussianReal 0) hdist.symm

private theorem brownian_increment_vector_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (m : ℕ) (D : Fin m → ℝ≥0) :
    HasLaw (fun ω (k : Fin m) =>
      B (RowPolygonalFDD.durationPrefix D (k.val + 1)) ω -
        B (RowPolygonalFDD.durationPrefix D k.val) ω)
      (RowPolygonalFDD.gaussianIncrementLaw D) P := by
  let t : Fin (m + 1) → ℝ≥0 := fun i => RowPolygonalFDD.durationPrefix D i.val
  have ht : Monotone t := fun i j hij => durationPrefix_mono D (by exact_mod_cast hij)
  have hind := hB.toIsPreBrownianReal.hasIndepIncrements m t ht
  have hmeas (k : Fin m) := (brownian_increment_hasLaw B P hB m D k).aemeasurable
  refine ⟨AEMeasurable.of_eval hmeas, ?_⟩
  rw [iIndepFun.map_fun_eq_pi_map hmeas hind]
  unfold RowPolygonalFDD.gaussianIncrementLaw
  congr 1
  funext k
  exact (brownian_increment_hasLaw B P hB m D k).map_eq

theorem brownian_vector_hasLaw_cumulativeGaussian {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (m : ℕ) (D : Fin m → ℝ≥0) :
    HasLaw (fun ω (k : Fin m) => B (RowPolygonalFDD.observationTime D k) ω)
      (RowPolygonalFDD.cumulativeGaussianLaw D) P := by
  have hcont : Continuous (RowPolygonalFDD.cumulativeMap m) := by
    unfold RowPolygonalFDD.cumulativeMap Shao.prefixSum
    fun_prop
  have hinc := brownian_increment_vector_hasLaw B P hB m D
  have hmap : HasLaw (RowPolygonalFDD.cumulativeMap m)
      (RowPolygonalFDD.cumulativeGaussianLaw D)
      (RowPolygonalFDD.gaussianIncrementLaw D) :=
    ⟨hcont.measurable.aemeasurable, rfl⟩
  apply (hmap.comp hinc).congr
  filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω
  funext k
  simpa only [Function.comp_apply, hω, sub_zero] using
    (cumulative_brownian_increments B m D ω k).symm

-- Fully proved tightness + specified finite-grid convergence helper.
-- Its abstract hypotheses are discharged in the actual final theorems below.

private theorem uniform_tight_integral_gridReconstruct_error
    (μSeq : ℕ → Measure C(unitInterval, ℝ))
    [∀ j, IsProbabilityMeasure (μSeq j)]
    (htight : IsTightMeasureSet (Set.range μSeq))
    (F : C(unitInterval, ℝ) →ᵇ ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
      |(∫ f, F (gridReconstruct n f) ∂(μSeq j)) -
        (∫ f, F f ∂(μSeq j))| < ε := by
  classical
  let η : ℝ := ε / (8 * (‖F‖ + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨K, hK, htail⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight
      (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη)
  filter_upwards [boundedContinuous_gridReconstruct_uniform_compact
    F K hK (ε / 2) (half_pos hε)] with n hn j
  let R : C(unitInterval, ℝ) →ᵇ ℝ :=
    F.compContinuous ⟨gridReconstruct n, continuous_gridReconstruct n⟩
  have hR : Integrable (fun f => F (gridReconstruct n f)) (μSeq j) := R.integrable _
  have hF : Integrable F (μSeq j) := F.integrable _
  have hG : Integrable (fun f => F (gridReconstruct n f) - F f) (μSeq j) := hR.sub hF
  let H : C(unitInterval, ℝ) → ℝ := fun f =>
    ε / 2 + Kᶜ.indicator (fun _ => 2 * ‖F‖) f
  have hH : Integrable H (μSeq j) :=
    (integrable_const _).add ((integrable_const _).indicator hK.isClosed.measurableSet.compl)
  have hpoint (f : C(unitInterval, ℝ)) :
      ‖F (gridReconstruct n f) - F f‖ ≤ H f := by
    by_cases hf : f ∈ K
    · simpa [H, hf, Real.norm_eq_abs] using (hn f hf).le
    · have hbound : |F (gridReconstruct n f) - F f| ≤ 2 * ‖F‖ := by
        simpa only [Real.dist_eq] using F.dist_le_two_norm (gridReconstruct n f) f
      dsimp [H]
      rw [Set.indicator_of_mem (Set.mem_compl hf)]
      linarith
  have hreal : (μSeq j).real Kᶜ ≤ η := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (htail _ ⟨j, rfl⟩)
    simpa only [ENNReal.toReal_ofReal hη.le, Measure.real] using h
  have herr : η * (2 * ‖F‖) < ε / 2 := by
    dsimp [η]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (show 0 < 8 * (‖F‖ + 1) by positivity)).mpr
    have hprod : 0 ≤ ε * ‖F‖ := mul_nonneg hε.le (norm_nonneg F)
    nlinarith
  calc
    _ = ‖∫ f, F (gridReconstruct n f) - F f ∂(μSeq j)‖ := by
      rw [integral_sub hR hF, Real.norm_eq_abs]
    _ ≤ ∫ f, ‖F (gridReconstruct n f) - F f‖ ∂(μSeq j) :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ f, H f ∂(μSeq j) := integral_mono hG.norm hH hpoint
    _ = ε / 2 + (μSeq j).real Kᶜ * (2 * ‖F‖) := by
      dsimp [H]
      rw [integral_add (integrable_const _) ((integrable_const _).indicator
        hK.isClosed.measurableSet.compl), integral_const,
        integral_indicator_const _ hK.isClosed.measurableSet.compl]
      simp only [probReal_univ, one_smul, smul_eq_mul, one_mul]
    _ ≤ ε / 2 + η * (2 * ‖F‖) := by
      have hb := mul_le_mul_of_nonneg_right hreal (show 0 ≤ 2 * ‖F‖ by positivity)
      linarith
    _ < ε := by linarith

private theorem tendsto_integral_gridReconstruct
    (μ : Measure C(unitInterval, ℝ)) [IsProbabilityMeasure μ]
    (F : C(unitInterval, ℝ) →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ f, F (gridReconstruct n f) ∂μ) atTop
      (𝓝 (∫ f, F f ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
  · intro n
    exact (F.continuous.comp (continuous_gridReconstruct n)).measurable.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ fun f => F.norm_coe_le_norm (gridReconstruct n f)
  · exact ae_of_all _ fun f =>
      (F.continuous.tendsto f).comp (gridReconstruct_tendsto f)

private theorem tendsto_laws_of_tight_gridEval
    (μSeq : ℕ → Measure C(unitInterval, ℝ))
    [∀ j, IsProbabilityMeasure (μSeq j)]
    (μ : Measure C(unitInterval, ℝ)) [IsProbabilityMeasure μ]
    (htight : IsTightMeasureSet (Set.range μSeq))
    (hgrid : ∀ n : ℕ, TendstoInDistribution
      (fun _ : ℕ => gridEval n) atTop (gridEval n) μSeq μ) :
    Tendsto (β := ProbabilityMeasure C(unitInterval, ℝ))
      (fun j => (⟨μSeq j, inferInstance⟩ : ProbabilityMeasure C(unitInterval, ℝ)))
      atTop (𝓝 (⟨μ, inferInstance⟩ : ProbabilityMeasure C(unitInterval, ℝ))) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  change Tendsto (fun j => ∫ f, F f ∂(μSeq j)) atTop (𝓝 (∫ f, F f ∂μ))
  have hfinite (n : ℕ) :
      Tendsto (fun j => ∫ f, F (gridReconstruct n f) ∂(μSeq j)) atTop
        (𝓝 (∫ f, F (gridReconstruct n f) ∂μ)) := by
    let G : (Fin (n + 2) → ℝ) →ᵇ ℝ :=
      F.compContinuous ⟨gridInterpolate n, continuous_gridInterpolate n⟩
    have h := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
      (fun _ => (continuous_gridEval n).measurable.aemeasurable)
      (continuous_gridEval n).measurable.aemeasurable).mp (hgrid n) G
    simpa only [G, BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
      gridReconstruct] using h
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he : 0 < ε / 3 := by positivity
  have hrow := uniform_tight_integral_gridReconstruct_error μSeq htight F (ε / 3) he
  have htarget := Metric.tendsto_nhds.mp (tendsto_integral_gridReconstruct μ F) (ε / 3) he
  obtain ⟨n, hnrow, hntarget⟩ := (hrow.and htarget).exists
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp (hfinite n) (ε / 3) he
  refine ⟨J, fun j hj => ?_⟩
  have h1 : |(∫ f, F f ∂(μSeq j)) -
      (∫ f, F (gridReconstruct n f) ∂(μSeq j))| < ε / 3 := by
    simpa only [abs_sub_comm] using hnrow j
  have h2 : |(∫ f, F (gridReconstruct n f) ∂(μSeq j)) -
      (∫ f, F (gridReconstruct n f) ∂μ)| < ε / 3 := by
    simpa only [Real.dist_eq] using hJ j hj
  have h3 : |(∫ f, F (gridReconstruct n f) ∂μ) - (∫ f, F f ∂μ)| < ε / 3 := by
    simpa only [Real.dist_eq] using hntarget
  have ht := abs_sub_le (∫ f, F f ∂(μSeq j))
    (∫ f, F (gridReconstruct n f) ∂(μSeq j)) (∫ f, F f ∂μ)
  have ht' := abs_sub_le (∫ f, F (gridReconstruct n f) ∂(μSeq j))
    (∫ f, F (gridReconstruct n f) ∂μ) (∫ f, F f ∂μ)
  rw [Real.dist_eq]
  linarith

-- Exact durations for all grid nodes, including the observation at time zero.

private def gridDurations (T : ℝ≥0) (n : ℕ) : Fin (n + 2) → ℝ≥0 :=
  fun i => if i.val = 0 then 0 else T / ((n + 1 : ℕ) : ℝ≥0)

private theorem gridDurations_totalDuration (T : ℝ≥0) (n : ℕ) :
    RowPolygonalFDD.totalDuration (gridDurations T n) = T := by
  have hn : ((n + 1 : ℕ) : ℝ≥0) ≠ 0 := by positivity
  unfold RowPolygonalFDD.totalDuration gridDurations
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, ite_true, Fin.val_succ, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, if_false, zero_add, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_div_assoc, mul_comm _ T, mul_div_cancel_right₀ _ hn]

private theorem gridDurations_observationTime
    (T : ℝ≥0) (n : ℕ) (i : Fin (n + 2)) :
    RowPolygonalFDD.observationTime (gridDurations T n) i =
      unitTime T (gridPoint n i) := by
  have hp (k : Fin (n + 2)) :
      RowPolygonalFDD.observationTime (gridDurations T n) k =
        (k.val : ℝ≥0) * (T / ((n + 1 : ℕ) : ℝ≥0)) := by
    refine Fin.induction ?_ (fun j ih => ?_) k
    · rw [RowPolygonalFDD.observationTime, durationPrefix_succ]
      simp [durationPrefix_zero, gridDurations]
    · change RowPolygonalFDD.durationPrefix (gridDurations T n) (j.succ.val + 1) = _
      rw [durationPrefix_succ (gridDurations T n) j.succ]
      change RowPolygonalFDD.observationTime (gridDurations T n) j.castSucc +
        gridDurations T n j.succ = _
      rw [ih]
      simp only [gridDurations, Fin.val_succ, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, if_false, Fin.val_castSucc, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  rw [hp]
  apply NNReal.coe_injective
  change (i.val : ℝ) * ((T : ℝ) / ((n + 1 : ℕ) : ℝ)) =
    (T : ℝ) * ((i.val : ℝ) / ((n + 1 : ℕ) : ℝ))
  ring

private theorem gridEval_unitPolygonalPath
    (T : ℝ≥0) (n : ℕ) (N : ℕ) (h : ℝ) (a : Shao.Path N) :
    gridEval n (PolygonalPathTightness.unitPolygonalPath T N h a) =
      RowPolygonalFDD.polygonalVector N h (gridDurations T n) a := by
  funext i
  rw [gridEval, PolygonalPathTightness.unitPolygonalPath_apply]
  unfold RowPolygonalFDD.polygonalVector
  rw [gridDurations_observationTime]
  rfl

private theorem brownian_gridEval_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (P : Measure Ω)
    [IsProbabilityMeasure P] (hB : IsBrownianReal B P) (n : ℕ) :
    HasLaw (fun ω => gridEval n (brownianUnitPath B T ω))
      (RowPolygonalFDD.cumulativeGaussianLaw (gridDurations T n)) P := by
  apply (brownian_vector_hasLaw_cumulativeGaussian B P hB (n + 2)
    (gridDurations T n)).congr
  filter_upwards [ae_brownianUnitPath_eq B T P hB] with ω hω
  funext i
  simp only [gridEval, hω, gridDurations_observationTime]

private theorem row_gridObservations_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (P : Measure Ω)
    [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (νSeq : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (νSeq j)]
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hbound : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hSeq : ℕ → ℝ) (hpos : ∀ j, 0 < hSeq j)
    (hh : Tendsto hSeq atTop atTop) (NSeq : ℕ → ℕ)
    (hN : ∀ j, (T : ℝ) * (hSeq j) ^ 2 ≤ (NSeq j : ℝ)) (n : ℕ) :
    TendstoInDistribution
      (fun j a => gridEval n (PolygonalPathTightness.unitPolygonalPath
        T (NSeq j) (hSeq j) a)) atTop
      (fun ω => gridEval n (brownianUnitPath B T ω))
      (fun j => Measure.pi (fun _ : Fin (NSeq j) => νSeq j)) P := by
  have hFDD := RowPolygonalFDD.row_polygonal_tendsto_cumulative_gaussian
    (n + 2) (gridDurations T n) νSeq h3 hmean hsecond M hbound hSeq hh NSeq
    (by intro j; simpa only [gridDurations_totalDuration] using hN j)
  have hG := brownian_gridEval_hasLaw B T P hB n
  have hm (j : ℕ) : AEMeasurable
      (fun a => gridEval n (PolygonalPathTightness.unitPolygonalPath
        T (NSeq j) (hSeq j) a))
      (Measure.pi (fun _ : Fin (NSeq j) => νSeq j)) :=
    ((continuous_gridEval n).comp
      (PolygonalPathTightness.continuous_unitPolygonalPath T (NSeq j) (hSeq j))).measurable.aemeasurable
  apply (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hm hG.aemeasurable).mpr
  intro F
  have ht := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    hFDD.forall_aemeasurable hFDD.aemeasurable_limit).mp hFDD F
  have hlimit : (∫ v, F v ∂(RowPolygonalFDD.cumulativeGaussianLaw (gridDurations T n))) =
      ∫ ω, F (gridEval n (brownianUnitPath B T ω)) ∂P := by
    simpa only [Function.comp_def] using
      (hG.integral_comp F.continuous.measurable.aestronglyMeasurable).symm
  simpa only [id_eq, gridEval_unitPolygonalPath, hlimit] using ht

-- Public actual path convergence and the equivalent weak-law statement.

theorem row_unitPolygonalPath_tendsto_brownian {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (P : Measure Ω)
    [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (νSeq : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (νSeq j)]
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hbound : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hSeq : ℕ → ℝ) (hpos : ∀ j, 0 < hSeq j)
    (hh : Tendsto hSeq atTop atTop) (NSeq : ℕ → ℕ)
    (hN : ∀ j, (T : ℝ) * (hSeq j) ^ 2 ≤ (NSeq j : ℝ)) :
    TendstoInDistribution
      (fun j => PolygonalPathTightness.unitPolygonalPath T (NSeq j) (hSeq j)) atTop
      (brownianUnitPath B T)
      (fun j => Measure.pi (fun _ : Fin (NSeq j) => νSeq j)) P := by
  let μSeq : ℕ → Measure C(unitInterval, ℝ) := fun j =>
    PolygonalPathTightness.polygonalPathLaw T (NSeq j) (hSeq j) (νSeq j)
  let μ : Measure C(unitInterval, ℝ) := brownianUnitPathLaw B T P
  letI : ∀ j, IsProbabilityMeasure (μSeq j) := fun j =>
    PolygonalPathTightness.isProbabilityMeasure_polygonalPathLaw T (NSeq j) (hSeq j) (νSeq j)
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_brownianUnitPathLaw B T P hB
  have hm (j : ℕ) : AEMeasurable
      (PolygonalPathTightness.unitPolygonalPath T (NSeq j) (hSeq j))
      (Measure.pi (fun _ : Fin (NSeq j) => νSeq j)) :=
    (PolygonalPathTightness.measurable_unitPolygonalPath T (NSeq j) (hSeq j)).aemeasurable
  have hβ := aemeasurable_brownianUnitPath B T P hB
  have htight : IsTightMeasureSet (Set.range μSeq) :=
    PolygonalPathTightness.isTightMeasureSet_polygonalPathLaw T NSeq hSeq νSeq
      (fun _ => inferInstance) hpos hN h3 hmean M hbound
  have hgrid (n : ℕ) : TendstoInDistribution
      (fun _ : ℕ => gridEval n) atTop (gridEval n) μSeq μ := by
    have hg := row_gridObservations_tendsto B T P hB νSeq h3 hmean hsecond M hbound
      hSeq hpos hh NSeq hN n
    apply (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
      (fun _ => (continuous_gridEval n).measurable.aemeasurable)
      (continuous_gridEval n).measurable.aemeasurable).mpr
    intro F
    have htest := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
      hg.forall_aemeasurable hg.aemeasurable_limit).mp hg F
    have hleft (j : ℕ) : (∫ f, F (gridEval n f) ∂(μSeq j)) =
        ∫ a, F (gridEval n (PolygonalPathTightness.unitPolygonalPath
          T (NSeq j) (hSeq j) a)) ∂(Measure.pi (fun _ : Fin (NSeq j) => νSeq j)) := by
      exact integral_map (hm j)
        (F.continuous.comp (continuous_gridEval n)).measurable.aestronglyMeasurable
    have hright : (∫ f, F (gridEval n f) ∂μ) =
        ∫ ω, F (gridEval n (brownianUnitPath B T ω)) ∂P := by
      exact integral_map hβ
        (F.continuous.comp (continuous_gridEval n)).measurable.aestronglyMeasurable
    simpa only [hleft, hright] using htest
  exact ⟨hm, hβ, tendsto_laws_of_tight_gridEval μSeq μ htight hgrid⟩

theorem tendsto_polygonalPathLaw_brownianUnitPathLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (P : Measure Ω)
    [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (νSeq : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (νSeq j)]
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (hsecond : ∀ j, (∫ x : ℝ, x ^ 2 ∂(νSeq j)) = 1)
    (M : ℝ) (hbound : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M)
    (hSeq : ℕ → ℝ) (hpos : ∀ j, 0 < hSeq j)
    (hh : Tendsto hSeq atTop atTop) (NSeq : ℕ → ℕ)
    (hN : ∀ j, (T : ℝ) * (hSeq j) ^ 2 ≤ (NSeq j : ℝ)) :
    Tendsto (β := ProbabilityMeasure C(unitInterval, ℝ))
      (fun j => (⟨PolygonalPathTightness.polygonalPathLaw
        T (NSeq j) (hSeq j) (νSeq j),
        PolygonalPathTightness.isProbabilityMeasure_polygonalPathLaw
          T (NSeq j) (hSeq j) (νSeq j)⟩ : ProbabilityMeasure C(unitInterval, ℝ)))
      atTop
      (𝓝 (⟨brownianUnitPathLaw B T P,
        isProbabilityMeasure_brownianUnitPathLaw B T P hB⟩ :
        ProbabilityMeasure C(unitInterval, ℝ))) := by
  exact (row_unitPolygonalPath_tendsto_brownian B T P hB νSeq h3 hmean hsecond
    M hbound hSeq hpos hh NSeq hN).tendsto

-- No opaque computational/choice-bearing definitions beyond the literal ones listed.
-- No auxiliary measurable-version path is exposed or substituted for brownianUnitPath.
-- No new FDD/tightness/uniqueness/convergence premise appears in either final theorem.

end

end Shao.OQ4.PolygonalBrownianWeakLimit
