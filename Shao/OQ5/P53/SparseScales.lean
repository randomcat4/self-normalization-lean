import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Deterministic slow scales for the P53 sparse construction

The data are one fixed exponent and one entire possibly nonmonotone input
sequence. All divisions and real powers retain their total definitions;
positivity, cancellations and scale identities are used only on a common
eventual tail. This module constructs no sparse labels or probability law.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace Shao.OQ5.P53

noncomputable section

def sparseDelta (α : ℝ) : ℝ := 3 * α / (8 - 2 * α)

def sparseBeta (α : ℝ) : ℝ := (4 - α) / 2

def sparseRatio (x : ℕ → ℝ) (n : ℕ) : ℝ := x n / Real.sqrt (n : ℝ)

def sparseCost (α : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) ^ sparseDelta α / x n) ^ sparseBeta α

def sparseSlow (α : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  min ((sparseCost α x n) ^ (-1 / α : ℝ))
    ((sparseRatio x n) ^ (-1 / 2 : ℝ))

def sparseAmplitude (α : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (sparseSlow α x n * x n)

def sparseShift (α : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  sparseAmplitude α x n ^ 2 / ((n : ℝ) - 2)

private theorem cost_eq_neg_rpow (α : ℝ) (x : ℕ → ℝ) (n : ℕ)
    (hn : 0 < (n : ℝ)) (hx : 0 < x n) :
    sparseCost α x n = (x n / (n : ℝ) ^ sparseDelta α) ^ (-sparseBeta α) := by
  have hp : 0 < (n : ℝ) ^ sparseDelta α := Real.rpow_pos_of_pos hn _
  change ((n : ℝ) ^ sparseDelta α / x n) ^ sparseBeta α = _
  rw [Real.rpow_neg (div_nonneg hx.le hp.le), Real.div_rpow hx.le hp.le,
    inv_div, Real.div_rpow hp.le hx.le]

private theorem mul_neg_half_eq_sqrt (u : ℝ) (hu : 0 < u) :
    u * u ^ (-1 / 2 : ℝ) = Real.sqrt u := by
  calc
    u * u ^ (-1 / 2 : ℝ) = u ^ (1 + (-1 / 2 : ℝ)) := by
      rw [Real.rpow_add hu, Real.rpow_one]
    _ = u ^ (1 / 2 : ℝ) := by congr 1; norm_num
    _ = Real.sqrt u := (Real.sqrt_eq_rpow u).symm

private theorem cost_slow_bound (u s a : ℝ) (hu : 0 < u) (hs : 0 ≤ s)
    (ha : 0 < a) (h : s ≤ u ^ (-1 / a : ℝ)) :
    u * s ^ (a / 2) ≤ Real.sqrt u := by
  have he : (-1 / a : ℝ) * (a / 2) = -1 / 2 := by
    field_simp [ne_of_gt ha]
  calc
    u * s ^ (a / 2) ≤ u * (u ^ (-1 / a : ℝ)) ^ (a / 2) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs h (by positivity)) hu.le
    _ = u * u ^ (-1 / 2 : ℝ) := by rw [← Real.rpow_mul hu.le, he]
    _ = Real.sqrt u := mul_neg_half_eq_sqrt u hu

private theorem amplitude_sq_identity (N s x : ℝ)
    (hN : 0 < N) (hs : 0 < s) (hx : 0 < x) :
    (N ^ (3 / 4 : ℝ) * Real.sqrt (s * x)) ^ 2 / N ^ 2 =
      s * (x / Real.sqrt N) := by
  have hp : (N ^ (3 / 4 : ℝ)) ^ 2 = N ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast (N ^ (3 / 4 : ℝ)) 2, ← Real.rpow_mul hN.le]
    congr 1; norm_num
  have hq : N ^ (3 / 2 : ℝ) / N ^ 2 = 1 / Real.sqrt N := by
    rw [← Real.rpow_natCast N 2, ← Real.rpow_sub hN]
    rw [show (3 / 2 : ℝ) - ((2 : ℕ) : ℝ) = -(1 / 2 : ℝ) by norm_num,
      Real.rpow_neg hN.le, ← Real.sqrt_eq_rpow]
    simp only [one_div]
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hs.le hx.le)]
  calc
    (N ^ (3 / 4 : ℝ)) ^ 2 * (s * x) / N ^ 2 =
        ((N ^ (3 / 4 : ℝ)) ^ 2 / N ^ 2) * (s * x) := by ring
    _ = (1 / Real.sqrt N) * (s * x) := by rw [hp, hq]
    _ = s * (x / Real.sqrt N) := by ring

private theorem amplitude_rpow_identity (α N s x : ℝ)
    (hN : 0 < N) (hs : 0 < s) (hx : 0 < x) :
    (N ^ (3 / 4 : ℝ) * Real.sqrt (s * x)) ^ α / x ^ 2 =
      (N ^ (3 * α / 4) * x ^ (α / 2 - 2)) * s ^ (α / 2) := by
  have hp : (N ^ (3 / 4 : ℝ)) ^ α = N ^ (3 * α / 4) := by
    rw [← Real.rpow_mul hN.le]
    congr 1; ring
  have hq : (Real.sqrt (s * x)) ^ α = s ^ (α / 2) * x ^ (α / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (mul_nonneg hs.le hx.le)]
    rw [show (1 / 2 : ℝ) * α = α / 2 by ring, Real.mul_rpow hs.le hx.le]
  rw [Real.mul_rpow (Real.rpow_nonneg hN.le _) (Real.sqrt_nonneg _), hp, hq]
  rw [Real.rpow_sub hx, Real.rpow_two]
  ring

private theorem nat_rpow_exp_tendsto (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-((n : ℝ) ^ c)))
      atTop (nhds 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / c) 1
    (by norm_num)).comp hn
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn1
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have he : c * (1 / c) = 1 := by field_simp [ne_of_gt hc]
  simp only [Function.comp_apply]
  rw [← Real.rpow_mul hn0.le, he, Real.rpow_one]
  simp only [neg_mul, one_mul]

theorem sparse_exponent_bounds (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    0 < sparseDelta α ∧ sparseDelta α < 1 / 2 ∧ 0 < sparseBeta α ∧
      sparseDelta α * sparseBeta α = 3 * α / 4 := by
  have hd : 0 < 8 - 2 * α := by linarith
  dsimp only [sparseDelta, sparseBeta]
  refine ⟨div_pos (mul_pos (by norm_num) hα0) hd, ?_, ?_, ?_⟩
  · rw [div_lt_iff₀ hd]
    nlinarith
  · exact div_pos (by linarith) (by norm_num)
  · calc
      3 * α / (8 - 2 * α) * ((4 - α) / 2) =
          (3 * α * ((4 - α) / 2)) / (8 - 2 * α) := by ring
      _ = 3 * α / 4 := by
        apply (div_eq_iff (ne_of_gt hd)).mpr
        ring

theorem sparse_input_tendsto (α : ℝ) (x : ℕ → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hSuper : Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop)
    (hSmall : Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0)) :
    Tendsto x atTop atTop := by
  have _hSmall := hSmall
  have hd := (sparse_exponent_bounds α hα0 hα1).1
  have hp : Tendsto (fun n : ℕ => (n : ℝ) ^ sparseDelta α) atTop atTop :=
    (tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop_mono' atTop _ hp
  filter_upwards [hSuper.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℕ)] with n hq hn1
  have hn : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hb : 0 < (n : ℝ) ^ sparseDelta α := Real.rpow_pos_of_pos hn _
  simpa only [one_mul] using (le_div_iff₀ hb).mp hq

theorem sparse_eventually_pos (α : ℝ) (x : ℕ → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hSuper : Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop)
    (hSmall : Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0)) :
    ∀ᶠ n : ℕ in atTop, 4 ≤ n ∧ 0 < x n ∧ 0 < sparseRatio x n ∧
      0 < sparseCost α x n ∧ 0 < sparseSlow α x n ∧
      0 < sparseAmplitude α x n ∧ 0 < sparseShift α x n := by
  have hx := (sparse_input_tendsto α x hα0 hα1 hSuper hSmall).eventually_gt_atTop 0
  filter_upwards [eventually_ge_atTop (4 : ℕ), hx] with n hn4 hx0
  have hn4r : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
  have hn : 0 < (n : ℝ) := by linarith
  have hr : 0 < sparseRatio x n := div_pos hx0 (Real.sqrt_pos.mpr hn)
  have he : 0 < sparseCost α x n :=
    Real.rpow_pos_of_pos (div_pos (Real.rpow_pos_of_pos hn _) hx0) _
  have hs : 0 < sparseSlow α x n :=
    lt_min (Real.rpow_pos_of_pos he _) (Real.rpow_pos_of_pos hr _)
  have ht : 0 < sparseAmplitude α x n :=
    mul_pos (Real.rpow_pos_of_pos hn _) (Real.sqrt_pos.mpr (mul_pos hs hx0))
  have hd : 0 < sparseShift α x n := div_pos (pow_pos ht 2) (by linarith)
  exact ⟨hn4, hx0, hr, he, hs, ht, hd⟩

theorem sparseCost_tendsto_zero (α : ℝ) (x : ℕ → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hSuper : Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop)
    (hSmall : Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0)) :
    Tendsto (sparseCost α x) atTop (nhds 0) := by
  have hb := (sparse_exponent_bounds α hα0 hα1).2.2.1
  apply ((tendsto_rpow_neg_atTop hb).comp hSuper).congr'
  filter_upwards [sparse_eventually_pos α x hα0 hα1 hSuper hSmall] with n hp
  rcases hp with ⟨hn4, hx, hr, he, hs, ht, hd⟩
  have hn4r : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
  exact (cost_eq_neg_rpow α x n (by linarith) hx).symm

theorem sparseSlow_tendsto (α : ℝ) (x : ℕ → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hSuper : Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop)
    (hSmall : Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0)) :
    Tendsto (sparseSlow α x) atTop atTop := by
  have hp := sparse_eventually_pos α x hα0 hα1 hSuper hSmall
  have he : Tendsto (sparseCost α x) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨sparseCost_tendsto_zero α x hα0 hα1 hSuper hSmall,
      hp.mono (fun _ h => h.2.2.2.1)⟩
  have hr : Tendsto (sparseRatio x) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hSmall, hp.mono (fun _ h => h.2.2.1)⟩
  have hl := (tendsto_rpow_neg_nhdsGT_zero
    (show (-1 / α : ℝ) < 0 from div_neg_of_neg_of_pos (by norm_num) hα0)).comp he
  have hu := (tendsto_rpow_neg_nhdsGT_zero (show (-1 / 2 : ℝ) < 0 by norm_num)).comp hr
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [tendsto_atTop.mp hl b, tendsto_atTop.mp hu b] with n hn hn'
  exact le_min hn hn'

theorem sparseSlow_eventual_estimates (α : ℝ) (x : ℕ → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hSuper : Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop)
    (hSmall : Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0)) :
    ∀ᶠ n : ℕ in atTop,
      sparseCost α x n * (sparseSlow α x n) ^ (α / 2) ≤
        Real.sqrt (sparseCost α x n) ∧
      sparseSlow α x n * sparseRatio x n ≤ Real.sqrt (sparseRatio x n) := by
  filter_upwards [sparse_eventually_pos α x hα0 hα1 hSuper hSmall] with n hp
  rcases hp with ⟨hn4, hx, hr, he, hs, ht, hd⟩
  refine ⟨cost_slow_bound _ _ _ he hs.le hα0 (min_le_left _ _), ?_⟩
  calc
    sparseSlow α x n * sparseRatio x n ≤
        (sparseRatio x n) ^ (-1 / 2 : ℝ) * sparseRatio x n :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hr.le
    _ = sparseRatio x n * (sparseRatio x n) ^ (-1 / 2 : ℝ) := mul_comm _ _
    _ = Real.sqrt (sparseRatio x n) := mul_neg_half_eq_sqrt _ hr

theorem sparse_cost_slow_tendsto_zero (α : ℝ) (x : ℕ → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hSuper : Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop)
    (hSmall : Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0)) :
    Tendsto (fun n : ℕ => sparseCost α x n * (sparseSlow α x n) ^ (α / 2))
      atTop (nhds 0) := by
  have hnonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ sparseCost α x n * (sparseSlow α x n) ^ (α / 2) := by
    filter_upwards [sparse_eventually_pos α x hα0 hα1 hSuper hSmall] with n hp
    rcases hp with ⟨hn4, hx, hr, he, hs, ht, hd⟩
    exact mul_nonneg he.le (Real.rpow_nonneg hs.le _)
  have hbound := (sparseSlow_eventual_estimates α x hα0 hα1 hSuper hSmall).mono
    (fun _ h => h.1)
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (sparseCost α x n)) atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp
      (sparseCost_tendsto_zero α x hα0 hα1 hSuper hSmall)
  exact squeeze_zero' hnonneg hbound hsqrt

theorem sparse_slow_ratio_tendsto_zero (α : ℝ) (x : ℕ → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hSuper : Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop)
    (hSmall : Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0)) :
    Tendsto (fun n : ℕ => sparseSlow α x n * sparseRatio x n) atTop (nhds 0) := by
  have hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ sparseSlow α x n * sparseRatio x n := by
    filter_upwards [sparse_eventually_pos α x hα0 hα1 hSuper hSmall] with n hp
    rcases hp with ⟨hn4, hx, hr, he, hs, ht, hd⟩
    exact mul_nonneg hs.le hr.le
  have hbound := (sparseSlow_eventual_estimates α x hα0 hα1 hSuper hSmall).mono
    (fun _ h => h.2)
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (sparseRatio x n)) atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hSmall
  exact squeeze_zero' hnonneg hbound hsqrt

theorem sparse_eventual_scale_identities (α : ℝ) (x : ℕ → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hSuper : Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop)
    (hSmall : Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0)) :
    ∀ᶠ n : ℕ in atTop,
      sparseCost α x n = (n : ℝ) ^ (3 * α / 4) * (x n) ^ (α / 2 - 2) ∧
      sparseAmplitude α x n ^ 2 / (n : ℝ) ^ 2 = sparseSlow α x n * sparseRatio x n ∧
      (sparseAmplitude α x n) ^ α / (x n) ^ 2 =
        sparseCost α x n * (sparseSlow α x n) ^ (α / 2) := by
  have hdb := (sparse_exponent_bounds α hα0 hα1).2.2.2
  filter_upwards [sparse_eventually_pos α x hα0 hα1 hSuper hSmall] with n hp
  rcases hp with ⟨hn4, hx, hr, he, hs, ht, hd⟩
  have hn4r : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
  have hn : 0 < (n : ℝ) := by linarith
  have hcost : sparseCost α x n =
      (n : ℝ) ^ (3 * α / 4) * (x n) ^ (α / 2 - 2) := by
    change (((n : ℝ) ^ sparseDelta α / x n) ^ sparseBeta α) = _
    rw [Real.div_rpow (Real.rpow_nonneg hn.le _) hx.le, ← Real.rpow_mul hn.le, hdb]
    rw [show α / 2 - 2 = -sparseBeta α by dsimp only [sparseBeta]; ring,
      Real.rpow_neg hx.le]
    simp only [div_eq_mul_inv]
  refine ⟨hcost, ?_, ?_⟩
  · exact amplitude_sq_identity _ _ _ hn hs hx
  · change (((n : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (sparseSlow α x n * x n)) ^ α /
      (x n) ^ 2) = _
    rw [amplitude_rpow_identity α _ _ _ hn hs hx, ← hcost]

theorem sparseAmplitude_cost_tendsto_zero (α : ℝ) (x : ℕ → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hSuper : Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop)
    (hSmall : Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0)) :
    Tendsto (fun n : ℕ => (sparseAmplitude α x n) ^ α / (x n) ^ 2)
      atTop (nhds 0) := by
  apply (sparse_cost_slow_tendsto_zero α x hα0 hα1 hSuper hSmall).congr'
  exact (sparse_eventual_scale_identities α x hα0 hα1 hSuper hSmall).mono
    (fun _ h => h.2.2.symm)

theorem sparseAmplitude_div_nat_tendsto_zero (α : ℝ) (x : ℕ → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hSuper : Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop)
    (hSmall : Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0)) :
    Tendsto (fun n : ℕ => sparseAmplitude α x n / (n : ℝ)) atTop (nhds 0) := by
  have heq : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (sparseSlow α x n * sparseRatio x n) = sparseAmplitude α x n / (n : ℝ) := by
    filter_upwards [sparse_eventually_pos α x hα0 hα1 hSuper hSmall,
      sparse_eventual_scale_identities α x hα0 hα1 hSuper hSmall] with n hp hi
    rcases hp with ⟨hn4, hx, hr, he, hs, ht, hd⟩
    have hn4r : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    have hn : 0 ≤ (n : ℝ) := by linarith
    calc
      Real.sqrt (sparseSlow α x n * sparseRatio x n) =
          Real.sqrt (sparseAmplitude α x n ^ 2 / (n : ℝ) ^ 2) := congrArg Real.sqrt hi.2.1.symm
      _ = Real.sqrt ((sparseAmplitude α x n / (n : ℝ)) ^ 2) := by rw [div_pow]
      _ = sparseAmplitude α x n / (n : ℝ) := Real.sqrt_sq (div_nonneg ht.le hn)
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (sparseSlow α x n * sparseRatio x n))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp
      (sparse_slow_ratio_tendsto_zero α x hα0 hα1 hSuper hSmall)
  exact hlim.congr' heq

theorem sparseShift_div_nat_tendsto_zero (α : ℝ) (x : ℕ → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hSuper : Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop)
    (hSmall : Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0)) :
    Tendsto (fun n : ℕ => sparseShift α x n / (n : ℝ)) atTop (nhds 0) := by
  have hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ sparseShift α x n / (n : ℝ) := by
    filter_upwards [sparse_eventually_pos α x hα0 hα1 hSuper hSmall] with n hp
    rcases hp with ⟨hn4, hx, hr, he, hs, ht, hd⟩
    exact div_nonneg hd.le (Nat.cast_nonneg n)
  have hbound : ∀ᶠ n : ℕ in atTop,
      sparseShift α x n / (n : ℝ) ≤ 2 * (sparseSlow α x n * sparseRatio x n) := by
    filter_upwards [sparse_eventually_pos α x hα0 hα1 hSuper hSmall,
      sparse_eventual_scale_identities α x hα0 hα1 hSuper hSmall] with n hp hi
    rcases hp with ⟨hn4, hx, hr, he, hs, ht, hd⟩
    have hn4r : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    have hn : 0 < (n : ℝ) := by linarith
    have hden : 0 < (n : ℝ) - 2 := by linarith
    have hfactor : (n : ℝ) / ((n : ℝ) - 2) ≤ 2 := by
      apply (div_le_iff₀ hden).mpr
      linarith
    calc
      sparseShift α x n / (n : ℝ) =
          (sparseAmplitude α x n ^ 2 / (n : ℝ) ^ 2) *
            ((n : ℝ) / ((n : ℝ) - 2)) := by
        unfold sparseShift
        field_simp [ne_of_gt hn, ne_of_gt hden]
      _ = (sparseSlow α x n * sparseRatio x n) *
          ((n : ℝ) / ((n : ℝ) - 2)) := by rw [hi.2.1]
      _ ≤ (sparseSlow α x n * sparseRatio x n) * 2 :=
        mul_le_mul_of_nonneg_left hfactor (mul_nonneg hs.le hr.le)
      _ = 2 * (sparseSlow α x n * sparseRatio x n) := mul_comm _ _
  have hupper : Tendsto (fun n : ℕ => 2 * (sparseSlow α x n * sparseRatio x n))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2)).mul
        (sparse_slow_ratio_tendsto_zero α x hα0 hα1 hSuper hSmall)
  exact squeeze_zero' hnonneg hbound hupper

theorem sparse_eventual_bounds (α : ℝ) (x : ℕ → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hSuper : Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop)
    (hSmall : Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0)) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (3 / 4 : ℝ) ≤ sparseAmplitude α x n ∧
      sparseAmplitude α x n ≤ (n : ℝ) ∧ sparseShift α x n ≤ 2 * (n : ℝ) := by
  have hs := (sparseSlow_tendsto α x hα0 hα1 hSuper hSmall).eventually_ge_atTop 1
  have hx := (sparse_input_tendsto α x hα0 hα1 hSuper hSmall).eventually_ge_atTop 1
  have ht : ∀ᶠ n : ℕ in atTop, sparseAmplitude α x n / (n : ℝ) < 1 :=
    (sparseAmplitude_div_nat_tendsto_zero α x hα0 hα1 hSuper hSmall).eventually_lt
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)) (by norm_num)
  have hd : ∀ᶠ n : ℕ in atTop, sparseShift α x n / (n : ℝ) < 2 :=
    (sparseShift_div_nat_tendsto_zero α x hα0 hα1 hSuper hSmall).eventually_lt
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2)) (by norm_num)
  filter_upwards [sparse_eventually_pos α x hα0 hα1 hSuper hSmall, hs, hx, ht, hd]
    with n hp hs1 hx1 ht1 hd2
  rcases hp with ⟨hn4, hx0, hr, he, hs0, ht0, hd0⟩
  have hn4r : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
  have hn : 0 < (n : ℝ) := by linarith
  have hsx : 1 ≤ sparseSlow α x n * x n := by
    simpa only [one_mul] using mul_le_mul hs1 hx1 (by norm_num : (0 : ℝ) ≤ 1) hs0.le
  have hroot : 1 ≤ Real.sqrt (sparseSlow α x n * x n) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hsx
  have hlower : (n : ℝ) ^ (3 / 4 : ℝ) ≤ sparseAmplitude α x n := by
    simpa only [sparseAmplitude, mul_one] using
      mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg hn.le (3 / 4 : ℝ))
  have htlt : sparseAmplitude α x n / (n : ℝ) < 1 := ht1
  have hdlt : sparseShift α x n / (n : ℝ) < 2 := hd2
  have htupper : sparseAmplitude α x n < (n : ℝ) := by
    simpa only [one_mul] using (div_lt_iff₀ hn).mp htlt
  have hdupper : sparseShift α x n < 2 * (n : ℝ) := (div_lt_iff₀ hn).mp hdlt
  exact ⟨hlower, htupper.le, hdupper.le⟩

theorem sparse_exp_cost_tendsto_zero (α : ℝ) (x : ℕ → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hSuper : Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop)
    (hSmall : Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0)) :
    Tendsto (fun n : ℕ => Real.exp (-((sparseAmplitude α x n) ^ α)))
      atTop (nhds 0) := by
  have hc : 0 < 3 * α / 4 := by positivity
  have hn : Tendsto (fun n : ℕ => (n : ℝ) ^ (3 * α / 4)) atTop atTop :=
    (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  have hbound : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (3 * α / 4) ≤ (sparseAmplitude α x n) ^ α := by
    filter_upwards [sparse_eventual_bounds α x hα0 hα1 hSuper hSmall] with n h
    calc
      (n : ℝ) ^ (3 * α / 4) = ((n : ℝ) ^ (3 / 4 : ℝ)) ^ α := by
        rw [← Real.rpow_mul (Nat.cast_nonneg n)]
        congr 1; ring
      _ ≤ (sparseAmplitude α x n) ^ α :=
        Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg n) _) h.1 hα0.le
  have ht : Tendsto (fun n : ℕ => (sparseAmplitude α x n) ^ α) atTop atTop :=
    tendsto_atTop_mono' atTop hbound hn
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 1 (by norm_num)).comp ht
  simpa only [Function.comp_def, Real.rpow_zero, one_mul, neg_mul] using h

theorem sparse_nat_mul_exp_cost_tendsto_zero (α : ℝ) (x : ℕ → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hSuper : Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop)
    (hSmall : Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-((sparseAmplitude α x n) ^ α)))
      atTop (nhds 0) := by
  have hc : 0 < 3 * α / 4 := by positivity
  have hnonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ (n : ℝ) * Real.exp (-((sparseAmplitude α x n) ^ α)) :=
    Filter.Eventually.of_forall (fun n => mul_nonneg (Nat.cast_nonneg n) (Real.exp_pos _).le)
  have hbound : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * Real.exp (-((sparseAmplitude α x n) ^ α)) ≤
        (n : ℝ) * Real.exp (-((n : ℝ) ^ (3 * α / 4))) := by
    filter_upwards [sparse_eventual_bounds α x hα0 hα1 hSuper hSmall] with n h
    have hp : (n : ℝ) ^ (3 * α / 4) ≤ (sparseAmplitude α x n) ^ α := by
      calc
        (n : ℝ) ^ (3 * α / 4) = ((n : ℝ) ^ (3 / 4 : ℝ)) ^ α := by
          rw [← Real.rpow_mul (Nat.cast_nonneg n)]
          congr 1; ring
        _ ≤ (sparseAmplitude α x n) ^ α :=
          Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg n) _) h.1 hα0.le
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hp)) (Nat.cast_nonneg n)
  exact squeeze_zero' hnonneg hbound (nat_rpow_exp_tendsto _ hc)

end

end Shao.OQ5.P53
