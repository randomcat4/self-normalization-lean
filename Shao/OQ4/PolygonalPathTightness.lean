import Shao.OQ4.PolygonalThirdMomentB3
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tightness of the actual finite-row polygonal path laws

The exact declarations and definition values are frozen in
`frozen-polygonal-path-tightness-formal-v1.lean.txt`. The continuous
observable below is the actual finite sum from PolygonalThirdMomentB3.
The dyadic compact sets and all probability bounds are derived here.
-/

open MeasureTheory
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

namespace Shao.OQ4.PolygonalPathTightness

private theorem continuous_polygonalPath_joint (n : ℕ) (h : ℝ) :
    Continuous (fun p : Shao.Path n × ℝ =>
      PolygonalThirdMoment.polygonalPath n h p.1 p.2) := by
  unfold PolygonalThirdMoment.polygonalPath
  fun_prop

private theorem continuous_unitPolygonalPath_value
    (T : ℝ≥0) (n : ℕ) (h : ℝ) (a : Shao.Path n) :
    Continuous (fun u : unitInterval =>
      PolygonalThirdMoment.polygonalPath n h a ((T : ℝ) * (u : ℝ))) := by
  exact (continuous_polygonalPath_joint n h).comp
    (continuous_const.prodMk (continuous_const.mul continuous_subtype_val))

/-- The particular finite-row polygonal path on the actual unit interval. -/
def unitPolygonalPath (T : ℝ≥0) (n : ℕ) (h : ℝ) (a : Shao.Path n) :
    C(unitInterval, ℝ) :=
  ⟨fun u => PolygonalThirdMoment.polygonalPath n h a ((T : ℝ) * (u : ℝ)),
    continuous_unitPolygonalPath_value T n h a⟩

@[simp] theorem unitPolygonalPath_apply
    (T : ℝ≥0) (n : ℕ) (h : ℝ) (a : Shao.Path n) (u : unitInterval) :
    unitPolygonalPath T n h a u =
      PolygonalThirdMoment.polygonalPath n h a ((T : ℝ) * (u : ℝ)) := rfl

theorem continuous_unitPolygonalPath (T : ℝ≥0) (n : ℕ) (h : ℝ) :
    Continuous (unitPolygonalPath T n h) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_polygonalPath_joint n h).comp
    (continuous_fst.prodMk (continuous_const.mul
      (continuous_subtype_val.comp continuous_snd)))

theorem measurable_unitPolygonalPath (T : ℝ≥0) (n : ℕ) (h : ℝ) :
    Measurable (unitPolygonalPath T n h) :=
  (continuous_unitPolygonalPath T n h).measurable

@[simp] theorem unitPolygonalPath_at_zero
    (T : ℝ≥0) (n : ℕ) (h : ℝ) (a : Shao.Path n) :
    unitPolygonalPath T n h a (0 : unitInterval) = 0 := by
  simp only [unitPolygonalPath_apply, Set.Icc.coe_zero, mul_zero,
    PolygonalThirdMoment.polygonalPath, zero_mul, zero_sub]
  apply Finset.sum_eq_zero
  intro i _
  have hi : -(i.val : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg _)
  have hr : max 0 (min 1 (-(i.val : ℝ))) = 0 :=
    max_eq_left (le_trans (min_le_right _ _) hi)
  simp [hr]

@[simp] theorem unitPolygonalPath_of_T_zero
    (n : ℕ) (h : ℝ) (a : Shao.Path n) :
    unitPolygonalPath 0 n h a = 0 := by
  ext u
  change PolygonalThirdMoment.polygonalPath n h a (0 * (u : ℝ)) = 0
  simpa only [zero_mul, unitPolygonalPath_apply, Set.Icc.coe_zero,
    mul_zero] using unitPolygonalPath_at_zero 0 n h a

@[simp] theorem unitPolygonalPath_of_n_zero
    (T : ℝ≥0) (h : ℝ) (a : Shao.Path 0) :
    unitPolygonalPath T 0 h a = 0 := by
  ext u
  simp [unitPolygonalPath_apply, PolygonalThirdMoment.polygonalPath]

/-- Pushforward of the actual finite pi law by the particular observable. -/
def polygonalPathLaw (T : ℝ≥0) (n : ℕ) (h : ℝ) (ν : Measure ℝ) :
    Measure C(unitInterval, ℝ) :=
  (Measure.pi (fun _ : Fin n => ν)).map (unitPolygonalPath T n h)

theorem isProbabilityMeasure_polygonalPathLaw
    (T : ℝ≥0) (n : ℕ) (h : ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (polygonalPathLaw T n h ν) := by
  unfold polygonalPathLaw
  infer_instance

private def dyadicDecay : ℝ := 15 / 16

private def dyadicEdgeRatio : ℝ := 512 / 1125

private def dyadicLayerRatio : ℝ := 1024 / 1125

private theorem dyadicPoint_mem (k : ℕ) (i : Fin (2 ^ k + 1)) :
    (i.val : ℝ) / (2 : ℝ) ^ k ∈ unitInterval := by
  have hp : 0 < (2 : ℝ) ^ k := by positivity
  have hi : i.val ≤ 2 ^ k := Nat.le_of_lt_succ i.isLt
  have hi' : (i.val : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast hi
  exact ⟨div_nonneg (Nat.cast_nonneg _) hp.le,
    (div_le_iff₀ hp).mpr (by simpa only [one_mul] using hi')⟩

private def dyadicPoint (k : ℕ) (i : Fin (2 ^ k + 1)) : unitInterval :=
  ⟨(i.val : ℝ) / (2 : ℝ) ^ k, dyadicPoint_mem k i⟩

private theorem dyadicFloorIndex_lt (k : ℕ) (u : unitInterval) :
    ⌊(2 : ℝ) ^ k * (u : ℝ)⌋₊ < 2 ^ k + 1 := by
  apply Nat.lt_succ_of_le
  apply Nat.floor_le_of_le
  simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_one] using
    mul_le_mul_of_nonneg_left u.property.2
      (show 0 ≤ (2 : ℝ) ^ k by positivity)

private def dyadicFloorIndex (k : ℕ) (u : unitInterval) : Fin (2 ^ k + 1) :=
  ⟨⌊(2 : ℝ) ^ k * (u : ℝ)⌋₊, dyadicFloorIndex_lt k u⟩

private def dyadicApprox (k : ℕ) (u : unitInterval) : unitInterval :=
  dyadicPoint k (dyadicFloorIndex k u)

private theorem dyadicApprox_distance (k : ℕ) (u : unitInterval) :
    0 ≤ (u : ℝ) - (dyadicApprox k u : ℝ) ∧
      (u : ℝ) - (dyadicApprox k u : ℝ) < (1 / 2 : ℝ) ^ k := by
  have hp : 0 < (2 : ℝ) ^ k := by positivity
  have hx : 0 ≤ (2 : ℝ) ^ k * (u : ℝ) := mul_nonneg hp.le u.property.1
  have hlo := Nat.floor_le hx
  have hhi := Nat.lt_floor_add_one ((2 : ℝ) ^ k * (u : ℝ))
  change 0 ≤ (u : ℝ) - (⌊(2 : ℝ) ^ k * (u : ℝ)⌋₊ : ℝ) / (2 : ℝ) ^ k ∧
    (u : ℝ) - (⌊(2 : ℝ) ^ k * (u : ℝ)⌋₊ : ℝ) / (2 : ℝ) ^ k <
      (1 / 2 : ℝ) ^ k
  constructor
  · exact sub_nonneg.mpr ((div_le_iff₀ hp).mpr (by nlinarith [hlo]))
  · rw [div_pow, one_pow]
    have hu : (u : ℝ) <
        (⌊(2 : ℝ) ^ k * (u : ℝ)⌋₊ : ℝ) / (2 : ℝ) ^ k + 1 / (2 : ℝ) ^ k := by
      calc
        (u : ℝ) < ((⌊(2 : ℝ) ^ k * (u : ℝ)⌋₊ : ℝ) + 1) / (2 : ℝ) ^ k :=
          (lt_div_iff₀ hp).mpr (by nlinarith [hhi])
        _ = _ := by ring
    linarith

private theorem tendsto_dyadicApprox (u : unitInterval) :
    Filter.Tendsto (fun k : ℕ => dyadicApprox k u) Filter.atTop (𝓝 u) := by
  have hpow : Filter.Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k)
      Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hd : Filter.Tendsto (fun k : ℕ =>
      (u : ℝ) - (dyadicApprox k u : ℝ)) Filter.atTop (𝓝 0) :=
    squeeze_zero (fun k => (dyadicApprox_distance k u).1)
      (fun k => (dyadicApprox_distance k u).2.le) hpow
  apply tendsto_subtype_rng.mpr
  convert (tendsto_const_nhds : Filter.Tendsto
    (fun _ : ℕ => (u : ℝ)) Filter.atTop (𝓝 (u : ℝ))).sub hd using 1 <;> simp

private theorem dyadicApprox_step_cases (k : ℕ) (u : unitInterval) :
    dyadicApprox (k + 1) u = dyadicApprox k u ∨
      ∃ i : Fin (2 ^ (k + 1)),
        dyadicApprox k u = dyadicPoint (k + 1) i.castSucc ∧
        dyadicApprox (k + 1) u = dyadicPoint (k + 1) i.succ := by
  let m : ℕ := ⌊(2 : ℝ) ^ k * (u : ℝ)⌋₊
  let m' : ℕ := ⌊(2 : ℝ) ^ (k + 1) * (u : ℝ)⌋₊
  have hx : 0 ≤ (2 : ℝ) ^ k * (u : ℝ) :=
    mul_nonneg (pow_nonneg (by norm_num) _) u.property.1
  have hlo : (m : ℝ) ≤ (2 : ℝ) ^ k * (u : ℝ) := Nat.floor_le hx
  have hhi : (2 : ℝ) ^ k * (u : ℝ) < (m : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hmlo : 2 * m ≤ m' := by
    apply Nat.le_floor
    change ((2 * m : ℕ) : ℝ) ≤ (2 : ℝ) ^ (k + 1) * (u : ℝ)
    push_cast
    rw [pow_succ]
    nlinarith
  have hmhi : m' < 2 * m + 2 := by
    apply (Nat.floor_lt (mul_nonneg
      (show 0 ≤ (2 : ℝ) ^ (k + 1) by positivity) u.property.1)).mpr
    push_cast
    rw [pow_succ]
    nlinarith
  have hcases : m' = 2 * m ∨ m' = 2 * m + 1 := by omega
  rcases hcases with heq | heq
  · left
    apply Subtype.ext
    change (m' : ℝ) / (2 : ℝ) ^ (k + 1) = (m : ℝ) / (2 : ℝ) ^ k
    rw [heq, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
    field_simp <;> ring
  · right
    have hmtop : m' ≤ 2 ^ (k + 1) :=
      Nat.le_of_lt_succ (dyadicFloorIndex_lt (k + 1) u)
    have hleft : 2 * m < 2 ^ (k + 1) := by omega
    let i : Fin (2 ^ (k + 1)) := ⟨2 * m, hleft⟩
    refine ⟨i, ?_, ?_⟩
    · apply Subtype.ext
      change (m : ℝ) / (2 : ℝ) ^ k = ((2 * m : ℕ) : ℝ) /
        (2 : ℝ) ^ (k + 1)
      push_cast
      rw [pow_succ]
      field_simp <;> ring
    · apply Subtype.ext
      change (m' : ℝ) / (2 : ℝ) ^ (k + 1) =
        ((2 * m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1)
      rw [heq]

private theorem dyadicApprox_close_cases (k : ℕ) (u v : unitInterval)
    (huv : (u : ℝ) ≤ (v : ℝ))
    (hclose : (v : ℝ) - (u : ℝ) ≤ (1 / 2 : ℝ) ^ k) :
    dyadicApprox k u = dyadicApprox k v ∨
      ∃ i : Fin (2 ^ k),
        dyadicApprox k u = dyadicPoint k i.castSucc ∧
        dyadicApprox k v = dyadicPoint k i.succ := by
  let m : ℕ := ⌊(2 : ℝ) ^ k * (u : ℝ)⌋₊
  let m' : ℕ := ⌊(2 : ℝ) ^ k * (v : ℝ)⌋₊
  have hp : 0 < (2 : ℝ) ^ k := by positivity
  have hmult : (2 : ℝ) ^ k * (v : ℝ) ≤
      (2 : ℝ) ^ k * (u : ℝ) + 1 := by
    have hc := mul_le_mul_of_nonneg_left hclose hp.le
    have hrecip : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by
      rw [div_pow, one_pow]
      field_simp
    rw [hrecip] at hc
    nlinarith
  have hmlo : m ≤ m' := Nat.floor_mono (mul_le_mul_of_nonneg_left huv hp.le)
  have hmhi : m' ≤ m + 1 := by
    calc
      m' ≤ ⌊(2 : ℝ) ^ k * (u : ℝ) + 1⌋₊ := Nat.floor_mono hmult
      _ = m + 1 := Nat.floor_add_one (mul_nonneg hp.le u.property.1)
  have hcases : m' = m ∨ m' = m + 1 := by omega
  rcases hcases with heq | heq
  · left
    apply Subtype.ext
    change (m : ℝ) / (2 : ℝ) ^ k = (m' : ℝ) / (2 : ℝ) ^ k
    rw [heq]
  · right
    have htop : m' ≤ 2 ^ k := Nat.le_of_lt_succ (dyadicFloorIndex_lt k v)
    have hm : m < 2 ^ k := by omega
    let i : Fin (2 ^ k) := ⟨m, hm⟩
    refine ⟨i, ?_, ?_⟩
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      change (m' : ℝ) / (2 : ℝ) ^ k = ((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k
      rw [heq]

private def dyadicGood (A : ℝ) : Set C(unitInterval, ℝ) :=
  {f | f (0 : unitInterval) = 0 ∧
    ∀ (k : ℕ) (i : Fin (2 ^ k)),
      |f (dyadicPoint k i.succ) - f (dyadicPoint k i.castSucc)| ≤
        A * dyadicDecay ^ k}

private theorem dyadicGood_step_bound (A : ℝ) (hA : 0 ≤ A)
    (f : C(unitInterval, ℝ)) (hf : f ∈ dyadicGood A)
    (k : ℕ) (u : unitInterval) :
    |f (dyadicApprox (k + 1) u) - f (dyadicApprox k u)| ≤
      A * dyadicDecay ^ (k + 1) := by
  rcases dyadicApprox_step_cases k u with heq | ⟨i, hleft, hright⟩
  · rw [heq, sub_self, abs_zero]
    exact mul_nonneg hA (pow_nonneg (by norm_num [dyadicDecay]) _)
  · rw [hleft, hright]
    exact hf.2 (k + 1) i

private theorem dyadicGood_chain_bound (A : ℝ) (hA : 0 ≤ A)
    (f : C(unitInterval, ℝ)) (hf : f ∈ dyadicGood A)
    (k ℓ : ℕ) (u : unitInterval) :
    |f (dyadicApprox (k + ℓ) u) - f (dyadicApprox k u)| ≤
      A * ∑ v ∈ Finset.range ℓ, dyadicDecay ^ (k + v + 1) := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    have hs := dyadicGood_step_bound A hA f hf (k + ℓ) u
    calc
      |f (dyadicApprox (k + (ℓ + 1)) u) - f (dyadicApprox k u)| ≤
          |f (dyadicApprox (k + ℓ + 1) u) - f (dyadicApprox (k + ℓ) u)| +
            |f (dyadicApprox (k + ℓ) u) - f (dyadicApprox k u)| := by
        simpa only [Nat.add_assoc] using abs_sub_le
          (f (dyadicApprox (k + ℓ + 1) u)) (f (dyadicApprox (k + ℓ) u))
          (f (dyadicApprox k u))
      _ ≤ A * dyadicDecay ^ (k + ℓ + 1) +
          A * ∑ v ∈ Finset.range ℓ, dyadicDecay ^ (k + v + 1) :=
        add_le_add hs ih
      _ = _ := by rw [Finset.sum_range_succ]; ring

private theorem dyadicGood_tail_bound (A : ℝ) (hA : 0 ≤ A)
    (f : C(unitInterval, ℝ)) (hf : f ∈ dyadicGood A)
    (k : ℕ) (u : unitInterval) :
    |f u - f (dyadicApprox k u)| ≤
      A * dyadicDecay ^ (k + 1) / (1 - dyadicDecay) := by
  have hq : 0 ≤ dyadicDecay := by norm_num [dyadicDecay]
  have hden : 0 < 1 - dyadicDecay := by norm_num [dyadicDecay]
  have hgeom : ∀ ℓ : ℕ,
      (1 - dyadicDecay) * (∑ v ∈ Finset.range ℓ,
        dyadicDecay ^ (k + v + 1)) =
      dyadicDecay ^ (k + 1) * (1 - dyadicDecay ^ ℓ) := by
    intro ℓ
    induction ℓ with
    | zero => simp
    | succ ℓ ih =>
      have hterm : dyadicDecay ^ (k + ℓ + 1) =
          dyadicDecay ^ (k + 1) * dyadicDecay ^ ℓ := by
        rw [← pow_add]
        congr 1
        omega
      rw [Finset.sum_range_succ, mul_add, ih, hterm, pow_succ dyadicDecay ℓ]
      ring
  have hfin : ∀ ℓ : ℕ,
      |f (dyadicApprox (k + ℓ) u) - f (dyadicApprox k u)| ≤
        A * dyadicDecay ^ (k + 1) / (1 - dyadicDecay) := by
    intro ℓ
    have hsum : (∑ v ∈ Finset.range ℓ, dyadicDecay ^ (k + v + 1)) ≤
        dyadicDecay ^ (k + 1) / (1 - dyadicDecay) := by
      apply (le_div_iff₀ hden).mpr
      have heq := hgeom ℓ
      have hprod := mul_nonneg (pow_nonneg hq (k + 1)) (pow_nonneg hq ℓ)
      nlinarith
    calc
      _ ≤ A * ∑ v ∈ Finset.range ℓ, dyadicDecay ^ (k + v + 1) :=
        dyadicGood_chain_bound A hA f hf k ℓ u
      _ ≤ A * (dyadicDecay ^ (k + 1) / (1 - dyadicDecay)) :=
        mul_le_mul_of_nonneg_left hsum hA
      _ = _ := by ring
  have hlim : Filter.Tendsto (fun m : ℕ =>
      |f (dyadicApprox m u) - f (dyadicApprox k u)|)
      Filter.atTop (𝓝 |f u - f (dyadicApprox k u)|) :=
    (((f.continuous.tendsto u).comp (tendsto_dyadicApprox u)).sub_const _).abs
  apply le_of_tendsto hlim
  filter_upwards [Filter.eventually_ge_atTop k] with m hm
  have heq : k + (m - k) = m := by omega
  simpa only [heq] using hfin (m - k)

private theorem dyadicGood_modulus (A : ℝ) (hA : 0 ≤ A)
    (f : C(unitInterval, ℝ)) (hf : f ∈ dyadicGood A)
    (k : ℕ) (u v : unitInterval)
    (hclose : |(v : ℝ) - (u : ℝ)| ≤ (1 / 2 : ℝ) ^ k) :
    |f v - f u| ≤ 31 * A * dyadicDecay ^ k := by
  have hord : ∀ u v : unitInterval,
      (u : ℝ) ≤ (v : ℝ) →
      |(v : ℝ) - (u : ℝ)| ≤ (1 / 2 : ℝ) ^ k →
      |f v - f u| ≤ 31 * A * dyadicDecay ^ k := by
    intro u v huv hc
    have hu := dyadicGood_tail_bound A hA f hf k u
    have hv := dyadicGood_tail_bound A hA f hf k v
    have hmid : |f (dyadicApprox k v) - f (dyadicApprox k u)| ≤
        A * dyadicDecay ^ k := by
      rcases dyadicApprox_close_cases k u v huv
        ((le_abs_self _).trans hc) with heq | ⟨i, hleft, hright⟩
      · rw [heq, sub_self, abs_zero]
        exact mul_nonneg hA (pow_nonneg (by norm_num [dyadicDecay]) _)
      · rw [hleft, hright]
        exact hf.2 k i
    have htri : |f v - f u| ≤ |f v - f (dyadicApprox k v)| +
        |f (dyadicApprox k v) - f (dyadicApprox k u)| +
        |f u - f (dyadicApprox k u)| := by
      have h1 := abs_sub_le (f v) (f (dyadicApprox k v)) (f u)
      have h2 := abs_sub_le (f (dyadicApprox k v)) (f (dyadicApprox k u)) (f u)
      rw [abs_sub_comm (f (dyadicApprox k u)) (f u)] at h2
      linarith
    calc
      _ ≤ A * dyadicDecay ^ (k + 1) / (1 - dyadicDecay) +
          A * dyadicDecay ^ k +
          A * dyadicDecay ^ (k + 1) / (1 - dyadicDecay) := by linarith
      _ = _ := by rw [pow_succ]; norm_num [dyadicDecay] <;> ring
  rcases le_total (u : ℝ) (v : ℝ) with huv | hvu
  · exact hord u v huv hclose
  · have hc : |(u : ℝ) - (v : ℝ)| ≤ (1 / 2 : ℝ) ^ k := by
      simpa only [abs_sub_comm] using hclose
    simpa only [abs_sub_comm] using hord v u hvu hc

private theorem dyadicGood_range_bound (A : ℝ) (hA : 0 ≤ A)
    (f : C(unitInterval, ℝ)) (hf : f ∈ dyadicGood A) (u : unitInterval) :
    |f u| ≤ 31 * A := by
  have hc : |(u : ℝ) - ((0 : unitInterval) : ℝ)| ≤ (1 / 2 : ℝ) ^ 0 := by
    simpa only [Set.Icc.coe_zero, sub_zero, abs_of_nonneg u.property.1,
      pow_zero] using u.property.2
  simpa only [hf.1, sub_zero, pow_zero, mul_one] using
    dyadicGood_modulus A hA f hf 0 0 u hc

private theorem isClosed_dyadicGood (A : ℝ) :
    IsClosed (dyadicGood A) := by
  unfold dyadicGood
  simp only [Set.setOf_and, Set.setOf_forall]
  refine (isClosed_eq (continuous_eval_const _) continuous_const).inter ?_
  apply isClosed_iInter
  intro k
  apply isClosed_iInter
  intro i
  exact isClosed_le
    (((continuous_eval_const _).sub (continuous_eval_const _)).abs) continuous_const

private theorem equicontinuous_dyadicGood (A : ℝ) (hA : 0 ≤ A) :
    Equicontinuous (fun f : dyadicGood A => fun u : unitInterval => f.1 u) := by
  apply UniformEquicontinuous.equicontinuous
  rw [Metric.uniformEquicontinuous_iff]
  intro ε hε
  have hlim : Filter.Tendsto (fun k : ℕ => 31 * A * dyadicDecay ^ k)
      Filter.atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (show 0 ≤ dyadicDecay by norm_num [dyadicDecay])
        (show dyadicDecay < 1 by norm_num [dyadicDecay])).const_mul (31 * A)
  obtain ⟨k, hk⟩ := (hlim.eventually (Iio_mem_nhds hε)).exists
  refine ⟨(1 / 2 : ℝ) ^ k, by positivity, ?_⟩
  intro u v huv f
  have hc : |(v : ℝ) - (u : ℝ)| ≤ (1 / 2 : ℝ) ^ k := by
    simpa only [Subtype.dist_eq, Real.dist_eq, abs_sub_comm] using huv.le
  have hf := (dyadicGood_modulus A hA f.1 f.2 k u v hc).trans_lt hk
  simpa only [Real.dist_eq, abs_sub_comm] using hf

private theorem isCompact_dyadicGood (A : ℝ) (hA : 0 ≤ A) :
    IsCompact (dyadicGood A) := by
  let e := ContinuousMap.isometryEquivBoundedOfCompact unitInterval ℝ
  let B : Set (BoundedContinuousFunction unitInterval ℝ) := e '' dyadicGood A
  have hBclosed : IsClosed B := e.toHomeomorph.isClosedMap _ (isClosed_dyadicGood A)
  have hBmem : ∀ g ∈ B, e.symm g ∈ dyadicGood A := by
    intro g hg
    rcases hg with ⟨f, hf, rfl⟩
    simpa only [e.symm_apply_apply] using hf
  have hBequi : Equicontinuous
      (fun g : B => fun u : unitInterval => g.1 u) := by
    convert (equicontinuous_dyadicGood A hA).comp
      (fun g : B => (⟨e.symm g.1, hBmem g.1 g.2⟩ : dyadicGood A)) using 1 <;> rfl
  have hBcompact : IsCompact B :=
    BoundedContinuousFunction.arzela_ascoli₂
      (Set.Icc (-31 * A) (31 * A)) isCompact_Icc B hBclosed
      (fun g u hg => by
        have h := dyadicGood_range_bound A hA (e.symm g) (hBmem g hg) u
        change |g u| ≤ 31 * A at h
        rcases abs_le.mp h with ⟨hl, hr⟩
        exact ⟨by linarith, hr⟩) hBequi
  simpa only [B, Set.image_image, Function.comp_def, e.symm_apply_apply,
    Set.image_id'] using hBcompact.image e.symm.continuous

private theorem unit_increment_abs_cube_integrable
    (T : ℝ≥0) (n : ℕ) (h : ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hh : 0 < h) (hn : (T : ℝ) * h ^ 2 ≤ (n : ℝ))
    (u v : unitInterval) :
    Integrable (fun a : Shao.Path n =>
      |unitPolygonalPath T n h a v - unitPolygonalPath T n h a u| ^ 3)
      (Measure.pi (fun _ : Fin n => ν)) := by
  have ht : ∀ v : unitInterval, ((T : ℝ) * (v : ℝ)) * h ^ 2 ≤ (n : ℝ) := by
    intro v
    calc
      ((T : ℝ) * (v : ℝ)) * h ^ 2 = ((T : ℝ) * h ^ 2) * (v : ℝ) := by ring
      _ ≤ ((T : ℝ) * h ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left v.property.2 (mul_nonneg T.coe_nonneg (sq_nonneg h))
      _ = (T : ℝ) * h ^ 2 := mul_one _
      _ ≤ _ := hn
  have hord : ∀ u v : unitInterval, (u : ℝ) ≤ (v : ℝ) →
      Integrable (fun a : Shao.Path n =>
        |unitPolygonalPath T n h a v - unitPolygonalPath T n h a u| ^ 3)
        (Measure.pi (fun _ : Fin n => ν)) := by
    intro u v huv
    simpa only [unitPolygonalPath_apply] using
      PolygonalThirdMoment.polygonal_increment_abs_cube_integrable
        n ν h3 h ((T : ℝ) * (u : ℝ)) ((T : ℝ) * (v : ℝ)) hh
        (mul_nonneg T.coe_nonneg u.property.1)
        (mul_le_mul_of_nonneg_left huv T.coe_nonneg) (ht v)
  rcases le_total (u : ℝ) (v : ℝ) with huv | hvu
  · exact hord u v huv
  · simpa only [abs_sub_comm] using hord v u hvu

private theorem unit_increment_abs_cube_le
    (T : ℝ≥0) (n : ℕ) (h : ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hh : 0 < h) (hn : (T : ℝ) * h ^ 2 ≤ (n : ℝ))
    (M : ℝ) (hM : (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M)
    (u v : unitInterval) :
    (∫ a : Shao.Path n,
      |unitPolygonalPath T n h a v - unitPolygonalPath T n h a u| ^ 3
      ∂(Measure.pi (fun _ : Fin n => ν))) ≤
      24 * M * (Real.sqrt (T : ℝ)) ^ 3 *
        (Real.sqrt |(v : ℝ) - (u : ℝ)|) ^ 3 := by
  have ht : ∀ v : unitInterval, ((T : ℝ) * (v : ℝ)) * h ^ 2 ≤ (n : ℝ) := by
    intro v
    calc
      ((T : ℝ) * (v : ℝ)) * h ^ 2 = ((T : ℝ) * h ^ 2) * (v : ℝ) := by ring
      _ ≤ ((T : ℝ) * h ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left v.property.2 (mul_nonneg T.coe_nonneg (sq_nonneg h))
      _ = (T : ℝ) * h ^ 2 := mul_one _
      _ ≤ _ := hn
  have hord : ∀ u v : unitInterval, (u : ℝ) ≤ (v : ℝ) →
      (∫ a : Shao.Path n,
        |unitPolygonalPath T n h a v - unitPolygonalPath T n h a u| ^ 3
        ∂(Measure.pi (fun _ : Fin n => ν))) ≤
        24 * M * (Real.sqrt (T : ℝ)) ^ 3 *
          (Real.sqrt |(v : ℝ) - (u : ℝ)|) ^ 3 := by
    intro u v huv
    have hb := PolygonalThirdMoment.polygonal_increment_abs_cube_le
      n ν h3 hmean h ((T : ℝ) * (u : ℝ)) ((T : ℝ) * (v : ℝ)) hh
      (mul_nonneg T.coe_nonneg u.property.1)
      (mul_le_mul_of_nonneg_left huv T.coe_nonneg) (ht v)
    have hroot : Real.sqrt ((T : ℝ) * (v : ℝ) - (T : ℝ) * (u : ℝ)) =
        Real.sqrt (T : ℝ) * Real.sqrt |(v : ℝ) - (u : ℝ)| := by
      rw [show (T : ℝ) * (v : ℝ) - (T : ℝ) * (u : ℝ) =
        (T : ℝ) * ((v : ℝ) - (u : ℝ)) by ring]
      rw [Real.sqrt_mul T.coe_nonneg, abs_of_nonneg (sub_nonneg.mpr huv)]
    calc
      _ ≤ 24 * (∫ x : ℝ, |x| ^ 3 ∂ν) *
          (Real.sqrt ((T : ℝ) * (v : ℝ) - (T : ℝ) * (u : ℝ))) ^ 3 := by
        simpa only [unitPolygonalPath_apply] using hb
      _ ≤ 24 * M *
          (Real.sqrt ((T : ℝ) * (v : ℝ) - (T : ℝ) * (u : ℝ))) ^ 3 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM (by norm_num))
          (pow_nonneg (Real.sqrt_nonneg _) _)
      _ = _ := by rw [hroot, mul_pow]; ring
  rcases le_total (u : ℝ) (v : ℝ) with huv | hvu
  · exact hord u v huv
  · simpa only [abs_sub_comm] using hord v u hvu

private theorem dyadic_sqrt_cube_le (k : ℕ) :
    (Real.sqrt ((1 / 2 : ℝ) ^ k)) ^ 3 ≤ (3 / 8 : ℝ) ^ k := by
  have hs : Real.sqrt (1 / 2 : ℝ) ≤ 3 / 4 := by
    have hsq := Real.sq_sqrt (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    have hnonneg := Real.sqrt_nonneg (1 / 2 : ℝ)
    nlinarith
  have hc : (Real.sqrt (1 / 2 : ℝ)) ^ 3 ≤ 3 / 8 := by
    rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ,
      Real.sq_sqrt (show 0 ≤ (1 / 2 : ℝ) by norm_num)]
    nlinarith
  induction k with
  | zero => norm_num
  | succ k ih =>
    calc
      (Real.sqrt ((1 / 2 : ℝ) ^ (k + 1))) ^ 3 =
          (Real.sqrt ((1 / 2 : ℝ) ^ k)) ^ 3 * (Real.sqrt (1 / 2 : ℝ)) ^ 3 := by
        rw [pow_succ (1 / 2 : ℝ) k, Real.sqrt_mul (by positivity), mul_pow]
      _ ≤ (3 / 8 : ℝ) ^ k * (3 / 8 : ℝ) :=
        mul_le_mul ih hc (by positivity) (by positivity)
      _ = _ := (pow_succ _ _).symm

private def dyadicIncrement {Ω : Type*}
    (X : Ω → C(unitInterval, ℝ)) (k : ℕ) (i : Fin (2 ^ k)) : Ω → ℝ :=
  fun ω => X ω (dyadicPoint k i.succ) - X ω (dyadicPoint k i.castSucc)

private def dyadicViolation {Ω : Type*}
    (X : Ω → C(unitInterval, ℝ)) (A : ℝ) (k : ℕ) (i : Fin (2 ^ k)) :
    Set Ω :=
  {ω | A * dyadicDecay ^ k < |dyadicIncrement X k i ω|}

private def dyadicLevelViolation {Ω : Type*}
    (X : Ω → C(unitInterval, ℝ)) (A : ℝ) (k : ℕ) : Set Ω :=
  ⋃ i : Fin (2 ^ k), dyadicViolation X A k i

private theorem measurable_dyadicIncrement
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → C(unitInterval, ℝ)) (hX : Measurable X)
    (k : ℕ) (i : Fin (2 ^ k)) :
    Measurable (dyadicIncrement X k i) := by
  exact ((ContinuousMap.measurable_eval _).comp hX).sub
    ((ContinuousMap.measurable_eval _).comp hX)

private theorem measurableSet_dyadicViolation
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → C(unitInterval, ℝ)) (hX : Measurable X)
    (A : ℝ) (k : ℕ) (i : Fin (2 ^ k)) :
    MeasurableSet (dyadicViolation X A k i) := by
  exact measurableSet_lt measurable_const
    ((continuous_abs : Continuous (fun x : ℝ => |x|)).measurable.comp
      (measurable_dyadicIncrement X hX k i))

private theorem dyadicGood_preimage_compl
    {Ω : Type*} (X : Ω → C(unitInterval, ℝ))
    (hzero : ∀ ω, X ω (0 : unitInterval) = 0) (A : ℝ) :
    X ⁻¹' (dyadicGood A)ᶜ = ⋃ k : ℕ, dyadicLevelViolation X A k := by
  classical
  ext ω
  simp [dyadicGood, dyadicLevelViolation, dyadicViolation, dyadicIncrement, hzero]

private theorem measure_dyadicViolation_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → C(unitInterval, ℝ)) (hX : Measurable X)
    (C A : ℝ) (hC : 0 ≤ C) (hA : 0 < A)
    (k : ℕ) (i : Fin (2 ^ k))
    (hint : Integrable (fun ω => |dyadicIncrement X k i ω| ^ 3) μ)
    (hbound : (∫ ω, |dyadicIncrement X k i ω| ^ 3 ∂μ) ≤
      C * (3 / 8 : ℝ) ^ k) :
    μ (dyadicViolation X A k i) ≤
      ENNReal.ofReal (C / A ^ 3 * dyadicEdgeRatio ^ k) := by
  have hq : 0 < dyadicDecay := by norm_num [dyadicDecay]
  have hθ : 0 < A * dyadicDecay ^ k := mul_pos hA (pow_pos hq _)
  let F : Set Ω := {ω | (A * dyadicDecay ^ k) ^ 3 ≤
    |dyadicIncrement X k i ω| ^ 3}
  have hsubset : dyadicViolation X A k i ⊆ F := by
    intro ω hω
    change (A * dyadicDecay ^ k) ^ 3 ≤ |dyadicIncrement X k i ω| ^ 3
    change A * dyadicDecay ^ k < |dyadicIncrement X k i ω| at hω
    gcongr <;> first | exact hω.le | positivity
  have hmono : μ.real (dyadicViolation X A k i) ≤ μ.real F :=
    ENNReal.toReal_mono (measure_ne_top μ F) (measure_mono hsubset)
  have hmark : (A * dyadicDecay ^ k) ^ 3 * μ.real F ≤
      ∫ ω, |dyadicIncrement X k i ω| ^ 3 ∂μ :=
    mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall (fun ω => pow_nonneg (abs_nonneg _) _))
      hint ((A * dyadicDecay ^ k) ^ 3)
  have hreal : μ.real (dyadicViolation X A k i) ≤
      C * (3 / 8 : ℝ) ^ k / (A * dyadicDecay ^ k) ^ 3 := by
    apply (le_div_iff₀ (pow_pos hθ 3)).mpr
    calc
      _ = (A * dyadicDecay ^ k) ^ 3 * μ.real (dyadicViolation X A k i) :=
        mul_comm _ _
      _ ≤ (A * dyadicDecay ^ k) ^ 3 * μ.real F :=
        mul_le_mul_of_nonneg_left hmono (pow_nonneg hθ.le _)
      _ ≤ _ := hmark.trans hbound
  have hratio : C * (3 / 8 : ℝ) ^ k / (A * dyadicDecay ^ k) ^ 3 =
      C / A ^ 3 * dyadicEdgeRatio ^ k := by
    have hp : (A * dyadicDecay ^ k) ^ 3 = A ^ 3 * (dyadicDecay ^ 3) ^ k := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
      rw [Nat.mul_comm k 3]
    rw [hp]
    calc
      _ = C / A ^ 3 * ((3 / 8 : ℝ) ^ k / (dyadicDecay ^ 3) ^ k) := by
        field_simp [ne_of_gt hA, ne_of_gt hq]
        <;> ring
      _ = C / A ^ 3 * ((3 / 8 : ℝ) / dyadicDecay ^ 3) ^ k :=
        congrArg (fun t : ℝ => C / A ^ 3 * t)
          (div_pow (3 / 8 : ℝ) (dyadicDecay ^ 3) k).symm
      _ = _ := by norm_num [dyadicDecay, dyadicEdgeRatio]
  rw [hratio] at hreal
  have hlift := ENNReal.ofReal_le_ofReal hreal
  change ENNReal.ofReal (μ (dyadicViolation X A k i)).toReal ≤ _ at hlift
  rwa [ENNReal.ofReal_toReal (measure_ne_top μ _)] at hlift

private theorem measure_dyadicLevelViolation_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → C(unitInterval, ℝ)) (hX : Measurable X)
    (C A : ℝ) (hC : 0 ≤ C) (hA : 0 < A) (k : ℕ)
    (hint : ∀ i : Fin (2 ^ k),
      Integrable (fun ω => |dyadicIncrement X k i ω| ^ 3) μ)
    (hbound : ∀ i : Fin (2 ^ k),
      (∫ ω, |dyadicIncrement X k i ω| ^ 3 ∂μ) ≤ C * (3 / 8 : ℝ) ^ k) :
    μ (dyadicLevelViolation X A k) ≤
      ENNReal.ofReal (C / A ^ 3 * dyadicLayerRatio ^ k) := by
  classical
  have hnonneg : 0 ≤ C / A ^ 3 * dyadicEdgeRatio ^ k := by
    exact mul_nonneg (div_nonneg hC (pow_nonneg hA.le _))
      (pow_nonneg (by norm_num [dyadicEdgeRatio]) _)
  calc
    _ ≤ ∑ i : Fin (2 ^ k), μ (dyadicViolation X A k i) :=
      measure_iUnion_fintype_le μ _
    _ ≤ ∑ _i : Fin (2 ^ k), ENNReal.ofReal (C / A ^ 3 * dyadicEdgeRatio ^ k) :=
      Finset.sum_le_sum (fun i _ =>
        measure_dyadicViolation_le μ X hX C A hC hA k i (hint i) (hbound i))
    _ = ENNReal.ofReal (∑ _i : Fin (2 ^ k), C / A ^ 3 * dyadicEdgeRatio ^ k) :=
      (ENNReal.ofReal_sum_of_nonneg (fun _ _ => hnonneg)).symm
    _ = ENNReal.ofReal (C / A ^ 3 * dyadicLayerRatio ^ k) := by
      congr 1
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat]
      rw [show dyadicLayerRatio = 2 * dyadicEdgeRatio by
        norm_num [dyadicLayerRatio, dyadicEdgeRatio], mul_pow]
      ring

private theorem measure_preimage_dyadicGood_compl_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → C(unitInterval, ℝ)) (hX : Measurable X)
    (hzero : ∀ ω, X ω (0 : unitInterval) = 0)
    (C A : ℝ) (hC : 0 ≤ C) (hA : 0 < A)
    (hint : ∀ (k : ℕ) (i : Fin (2 ^ k)),
      Integrable (fun ω => |dyadicIncrement X k i ω| ^ 3) μ)
    (hbound : ∀ (k : ℕ) (i : Fin (2 ^ k)),
      (∫ ω, |dyadicIncrement X k i ω| ^ 3 ∂μ) ≤ C * (3 / 8 : ℝ) ^ k) :
    μ (X ⁻¹' (dyadicGood A)ᶜ) ≤
      ENNReal.ofReal ((C / A ^ 3) / (1 - dyadicLayerRatio)) := by
  have hr : |dyadicLayerRatio| < 1 := by norm_num [dyadicLayerRatio]
  have hs : Summable (fun k : ℕ => C / A ^ 3 * dyadicLayerRatio ^ k) :=
    (summable_geometric_of_abs_lt_one hr).mul_left _
  have hn : ∀ k : ℕ, 0 ≤ C / A ^ 3 * dyadicLayerRatio ^ k := by
    intro k
    exact mul_nonneg (div_nonneg hC (pow_nonneg hA.le _))
      (pow_nonneg (by norm_num [dyadicLayerRatio]) _)
  rw [dyadicGood_preimage_compl X hzero A]
  calc
    _ ≤ ∑' k : ℕ, μ (dyadicLevelViolation X A k) := measure_iUnion_le _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (C / A ^ 3 * dyadicLayerRatio ^ k) :=
      ENNReal.tsum_le_tsum (fun k =>
        measure_dyadicLevelViolation_le μ X hX C A hC hA k (hint k) (hbound k))
    _ = ENNReal.ofReal (∑' k : ℕ, C / A ^ 3 * dyadicLayerRatio ^ k) :=
      (ENNReal.ofReal_tsum_of_nonneg hn hs).symm
    _ = _ := by
      simp only [tsum_mul_left, tsum_geometric_of_abs_lt_one hr, div_eq_mul_inv]

private theorem exists_pos_amplitude
    (C : ℝ) (hC : 0 ≤ C) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧
      ENNReal.ofReal ((C / A ^ 3) / (1 - dyadicLayerRatio)) ≤ ε := by
  by_cases htop : ε = ∞
  · exact ⟨1, by norm_num, by simp only [htop, le_top]⟩
  have he : 0 < ε.toReal := ENNReal.toReal_pos (ne_of_gt hε) htop
  have hd : 0 < 1 - dyadicLayerRatio := by norm_num [dyadicLayerRatio]
  let D : ℝ := (1 - dyadicLayerRatio) * ε.toReal
  have hD : 0 < D := mul_pos hd he
  let A : ℝ := 1 + C / D
  have hCD : 0 ≤ C / D := div_nonneg hC hD.le
  have hA1 : 1 ≤ A := by dsimp [A]; linarith
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) hA1
  have hcube : A ≤ A ^ 3 := by
    have hp := mul_nonneg (sub_nonneg.mpr hA1)
      (show 0 ≤ A * (A + 1) by positivity)
    nlinarith
  have hbound : C ≤ A ^ 3 * D := by
    apply (div_le_iff₀ hD).mp
    have hId : C / D = A - 1 := by dsimp [A]; ring
    rw [hId]
    linarith
  refine ⟨A, hA, (ENNReal.ofReal_le_iff_le_toReal htop).mpr ?_⟩
  apply (div_le_iff₀ hd).mpr
  apply (div_le_iff₀ (pow_pos hA 3)).mpr
  calc
    C ≤ A ^ 3 * D := hbound
    _ = ε.toReal * (1 - dyadicLayerRatio) * A ^ 3 := by dsimp [D]; ring

theorem isTightMeasureSet_polygonalPathLaw
    (T : ℝ≥0) (nSeq : ℕ → ℕ) (hSeq : ℕ → ℝ)
    (νSeq : ℕ → Measure ℝ)
    (hprob : ∀ j, IsProbabilityMeasure (νSeq j))
    (hpos : ∀ j, 0 < hSeq j)
    (horizon : ∀ j, (T : ℝ) * hSeq j ^ 2 ≤ (nSeq j : ℝ))
    (h3 : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (νSeq j))
    (hmean : ∀ j, (∫ x : ℝ, x ∂(νSeq j)) = 0)
    (M : ℝ) (hM : ∀ j, (∫ x : ℝ, |x| ^ 3 ∂(νSeq j)) ≤ M) :
    IsTightMeasureSet (Set.range (fun j =>
      polygonalPathLaw T (nSeq j) (hSeq j) (νSeq j))) := by
  have hM0 : 0 ≤ M :=
    (integral_nonneg (fun x : ℝ => pow_nonneg (abs_nonneg x) 3)).trans (hM 0)
  let C : ℝ := 24 * M * (Real.sqrt (T : ℝ)) ^ 3
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (by norm_num) hM0)
    (pow_nonneg (Real.sqrt_nonneg _) _)
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨A, hA, hεA⟩ := exists_pos_amplitude C hC ε hε
  refine ⟨dyadicGood A, isCompact_dyadicGood A hA.le, ?_⟩
  rintro ρ ⟨j, rfl⟩
  letI : IsProbabilityMeasure (νSeq j) := hprob j
  have hint : ∀ (k : ℕ) (i : Fin (2 ^ k)),
      Integrable (fun a : Shao.Path (nSeq j) =>
        |dyadicIncrement (unitPolygonalPath T (nSeq j) (hSeq j)) k i a| ^ 3)
        (Measure.pi (fun _ : Fin (nSeq j) => νSeq j)) := by
    intro k i
    exact unit_increment_abs_cube_integrable T (nSeq j) (hSeq j) (νSeq j)
      (h3 j) (hpos j) (horizon j) (dyadicPoint k i.castSucc) (dyadicPoint k i.succ)
  have hbound : ∀ (k : ℕ) (i : Fin (2 ^ k)),
      (∫ a : Shao.Path (nSeq j),
        |dyadicIncrement (unitPolygonalPath T (nSeq j) (hSeq j)) k i a| ^ 3
        ∂(Measure.pi (fun _ : Fin (nSeq j) => νSeq j))) ≤ C * (3 / 8 : ℝ) ^ k := by
    intro k i
    have hdist : |(dyadicPoint k i.succ : ℝ) -
        (dyadicPoint k i.castSucc : ℝ)| = (1 / 2 : ℝ) ^ k := by
      change |((i.val + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k -
        (i.val : ℝ) / (2 : ℝ) ^ k| = (1 / 2 : ℝ) ^ k
      rw [Nat.cast_add, Nat.cast_one,
        show ((i.val : ℝ) + 1) / (2 : ℝ) ^ k -
          (i.val : ℝ) / (2 : ℝ) ^ k = 1 / (2 : ℝ) ^ k by ring,
        abs_of_pos (by positivity), div_pow, one_pow]
    have hi := unit_increment_abs_cube_le T (nSeq j) (hSeq j) (νSeq j)
      (h3 j) (hmean j) (hpos j) (horizon j) M (hM j)
      (dyadicPoint k i.castSucc) (dyadicPoint k i.succ)
    rw [hdist] at hi
    calc
      _ ≤ C * (Real.sqrt ((1 / 2 : ℝ) ^ k)) ^ 3 := by
        simpa only [dyadicIncrement, C] using hi
      _ ≤ _ := mul_le_mul_of_nonneg_left (dyadic_sqrt_cube_le k) hC
  change (Measure.pi (fun _ : Fin (nSeq j) => νSeq j)).map
    (unitPolygonalPath T (nSeq j) (hSeq j)) (dyadicGood A)ᶜ ≤ ε
  rw [Measure.map_apply (measurable_unitPolygonalPath T (nSeq j) (hSeq j))
    (isClosed_dyadicGood A).measurableSet.compl]
  exact (measure_preimage_dyadicGood_compl_le
    (Measure.pi (fun _ : Fin (nSeq j) => νSeq j))
    (unitPolygonalPath T (nSeq j) (hSeq j))
    (measurable_unitPolygonalPath T (nSeq j) (hSeq j))
    (unitPolygonalPath_at_zero T (nSeq j) (hSeq j))
    C A hC hA hint hbound).trans hεA

end Shao.OQ4.PolygonalPathTightness

