import Shao.C2.IntervalImageSpatialProfiles
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.FunctionSeries

noncomputable section
namespace Shao.C2.IntervalImageSpatialConvergence
open Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageExponents Shao.C2.IntervalImageSpatialProfiles

def StripPoint (a H U : ℝ) := {p : ℝ × ℝ // |p.1| ≤ a ∧ H ≤ p.2 ∧ p.2 ≤ U}

def spatialPrefactor (j : ℕ) (a H : ℝ) : ℝ :=
  (4 / Real.sqrt H * (1 + 2 * a / Real.sqrt H)) ^ j *
    (1 + (2 : ℝ) ^ j * (Nat.factorial j : ℝ))

def gaussianMajorant (a U : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(4 * a ^ 2 / U) * (n : ℝ) ^ 2)

def spatialTailBlock (j : ℕ) (a z T y : ℝ) (n : ℕ) : ℝ :=
  iteratedDeriv j (fun w => Real.exp (-imageA a w z ((n : ℤ) + 2 : ℤ) / T)) y +
    iteratedDeriv j (fun w => Real.exp (-imageA a w z (-((n : ℤ) + 2) : ℤ) / T)) y -
    iteratedDeriv j (fun w => Real.exp (-imageB a w z ((n : ℤ) + 1 : ℤ) / T)) y -
    iteratedDeriv j (fun w => Real.exp (-imageB a w z (-((n : ℤ) + 2) : ℤ) / T)) y

theorem summable_exp_neg_nat_sq (c : ℝ) (hc : 0 < c) :
    Summable (fun n : ℕ => Real.exp (-c * (n : ℝ) ^ 2)) := by
  have hr : ‖Real.exp (-c)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-c))]
    exact Real.exp_lt_one_iff.2 (by linarith only [hc])
  apply (summable_geometric_of_norm_lt_one hr).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst n
      norm_num
    · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt h)
      nlinarith only [h1]
  calc
    _ ≤ Real.exp (-c * (n : ℝ)) := Real.exp_le_exp.2
      (mul_le_mul_of_nonpos_left hn (by linarith only [hc] : -c ≤ 0))
    _ = Real.exp (-c) ^ n := by rw [← Real.exp_nat_mul]; congr 1 <;> ring

theorem gaussianMajorant_summable (a U : ℝ) (ha : 0 < a) (hU : 0 < U) :
    Summable (gaussianMajorant a U) := by
  exact summable_exp_neg_nat_sq (4 * a ^ 2 / U) (by positivity)

theorem tail_exponent_lower_bounds (a y z : ℝ) (n : ℕ) (ha : 0 < a)
    (hy : |y| ≤ a) (hz : |z| ≤ a) :
    8 * (n : ℝ) ^ 2 * a ^ 2 ≤ imageA a y z ((n : ℤ) + 2 : ℤ) ∧
      8 * (n : ℝ) ^ 2 * a ^ 2 ≤ imageA a y z (-((n : ℤ) + 2) : ℤ) ∧
      8 * (n : ℝ) ^ 2 * a ^ 2 ≤ imageB a y z ((n : ℤ) + 1 : ℤ) ∧
      8 * (n : ℝ) ^ 2 * a ^ 2 ≤ imageB a y z (-((n : ℤ) + 2) : ℤ) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h0 : 0 ≤ imageB a y z 0 := by
    simpa only [Int.cast_zero] using imageB_nonneg a y z 0 ha hy hz
  have hneg : 0 ≤ imageB a y z (-1) := by
    simpa using imageB_nonneg a y z (-1) ha hy hz
  have hAp := imageA_positive_tail a y z ((n : ℝ) + 2) ha hy hz (by linarith only [hn])
  have hAn := imageA_negative_tail a y z ((n : ℝ) + 2) ha hy hz (by linarith only [hn])
  have hBp := imageB_positive_tail a y z ((n : ℝ) + 1) ha hy hz (by linarith only [hn])
  have hBn := imageB_negative_tail a y z ((n : ℝ) + 1) ha hy hz (by linarith only [hn])
  have hAextra : 0 ≤ 8 * a ^ 2 * (3 * (n : ℝ) + 2) := by positivity
  have hBextra : 0 ≤ 8 * a ^ 2 * (2 * (n : ℝ) + 1) := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · push_cast
    nlinarith only [hAp, h0, hAextra]
  · push_cast
    nlinarith only [hAn, hneg, hAextra]
  · push_cast
    nlinarith only [hBp, h0, hBextra]
  · push_cast
    rw [show -((n : ℝ) + 2) = -((n : ℝ) + 1) - 1 by ring]
    nlinarith only [hBn, hneg, hBextra]

theorem exponent_half_le_majorant (a C T U : ℝ) (n : ℕ) (hT : 0 < T) (hTU : T ≤ U)
    (hC : 8 * (n : ℝ) ^ 2 * a ^ 2 ≤ C) :
    Real.exp (-C / (2 * T)) ≤ gaussianMajorant a U n := by
  have hU : 0 < U := hT.trans_le hTU
  have hn0 : 0 ≤ 8 * (n : ℝ) ^ 2 * a ^ 2 := by positivity
  have h1 : (8 * (n : ℝ) ^ 2 * a ^ 2) / (2 * T) ≤ C / (2 * T) :=
    (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * T)).2 hC
  have h2 := div_le_div_of_nonneg_left hn0 (by positivity : 0 < 2 * T)
    (by linarith only [hTU] : 2 * T ≤ 2 * U)
  dsimp only [gaussianMajorant]
  apply Real.exp_le_exp.2
  convert neg_le_neg (h2.trans h1) using 1 <;>
    field_simp [ne_of_gt hT, ne_of_gt hU] <;> ring

theorem spatial_prefactor_bound (j : ℕ) (a H T y z : ℝ) (ha : 0 < a) (hH : 0 < H)
    (hHT : H ≤ T) (hy : |y| ≤ a) (hz : |z| ≤ a) :
    (4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j *
        (1 + (2 : ℝ) ^ j * (Nat.factorial j : ℝ)) ≤ spatialPrefactor j a H := by
  have hT : 0 < T := hH.trans_le hHT
  have hsH : 0 < Real.sqrt H := Real.sqrt_pos.2 hH
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hs : Real.sqrt H ≤ Real.sqrt T := Real.sqrt_le_sqrt hHT
  have hd : |z - y| ≤ 2 * a := by
    apply abs_le.mpr
    constructor <;> linarith only [(abs_le.mp hy).1, (abs_le.mp hy).2,
      (abs_le.mp hz).1, (abs_le.mp hz).2]
  have h4 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4) hsH hs
  have hdist : |z - y| / Real.sqrt T ≤ 2 * a / Real.sqrt H :=
    (div_le_div_of_nonneg_left (abs_nonneg (z - y)) hsH hs).trans
      ((div_le_div_iff_of_pos_right hsH).2 hd)
  have hbase : 4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T) ≤
      4 / Real.sqrt H * (1 + 2 * a / Real.sqrt H) :=
    mul_le_mul h4 (add_le_add (le_refl 1) hdist) (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) hbase j) (by positivity)

theorem spatialTailBlock_bound (j : ℕ) (a z H U : ℝ) (n : ℕ) (p : StripPoint a H U)
    (ha : 0 < a) (hz : |z| ≤ a) (hH : 0 < H) (hHU : H ≤ U) :
    ‖spatialTailBlock j a z p.val.2 p.val.1 n‖ ≤
      4 * spatialPrefactor j a H * gaussianMajorant a U n := by
  have hT : 0 < p.val.2 := hH.trans_le p.property.2.1
  have hK : 0 ≤ spatialPrefactor j a H := by dsimp only [spatialPrefactor]; positivity
  have hcoef := spatial_prefactor_bound j a H p.val.2 p.val.1 z ha hH p.property.2.1 p.property.1 hz
  have hCs := tail_exponent_lower_bounds a p.val.1 z n ha p.property.1 hz
  have hterm (f : ℝ → ℝ) (C : ℝ)
      (hp : |iteratedDeriv j f p.val.1| ≤
        (4 / Real.sqrt p.val.2 * (1 + |z - p.val.1| / Real.sqrt p.val.2)) ^ j *
          (1 + (2 : ℝ) ^ j * (Nat.factorial j : ℝ)) * Real.exp (-C / (2 * p.val.2)))
      (hC : 8 * (n : ℝ) ^ 2 * a ^ 2 ≤ C) :
      |iteratedDeriv j f p.val.1| ≤ spatialPrefactor j a H * gaussianMajorant a U n := by
    have he := exponent_half_le_majorant a C p.val.2 U n hT p.property.2.2 hC
    exact hp.trans (mul_le_mul hcoef he (Real.exp_pos _).le hK)
  have hAp := hterm _ _ (imageA_spatial_profile j a p.val.1 z p.val.2
    ((n : ℤ) + 2) ha p.property.1 hz hT) hCs.1
  have hAn := hterm _ _ (imageA_spatial_profile j a p.val.1 z p.val.2
    (-((n : ℤ) + 2)) ha p.property.1 hz hT) hCs.2.1
  have hBp := hterm _ _ (imageB_spatial_profile j a p.val.1 z p.val.2
    ((n : ℤ) + 1) ha p.property.1 hz hT) hCs.2.2.1
  have hBn := hterm _ _ (imageB_spatial_profile j a p.val.1 z p.val.2
    (-((n : ℤ) + 2)) ha p.property.1 hz hT) hCs.2.2.2
  have htri (x1 x2 x3 x4 : ℝ) :
      |x1 + x2 - x3 - x4| ≤ |x1| + |x2| + |x3| + |x4| := by
    have h1 := abs_add_le (x1 + x2 - x3) (-x4)
    have h2 := abs_add_le (x1 + x2) (-x3)
    have h3 := abs_add_le x1 x2
    simp only [← sub_eq_add_neg, abs_neg] at h1 h2
    linarith only [h1, h2, h3]
  rw [Real.norm_eq_abs]
  dsimp only [spatialTailBlock]
  have hh := htri
    (iteratedDeriv j (fun w => Real.exp (-imageA a w z ((n : ℤ) + 2 : ℤ) / p.val.2)) p.val.1)
    (iteratedDeriv j (fun w => Real.exp (-imageA a w z (-((n : ℤ) + 2) : ℤ) / p.val.2)) p.val.1)
    (iteratedDeriv j (fun w => Real.exp (-imageB a w z ((n : ℤ) + 1 : ℤ) / p.val.2)) p.val.1)
    (iteratedDeriv j (fun w => Real.exp (-imageB a w z (-((n : ℤ) + 2) : ℤ) / p.val.2)) p.val.1)
  linarith only [hh, hAp, hAn, hBp, hBn]

theorem spatialTailBlock_summable (j : ℕ) (a z H U : ℝ) (p : StripPoint a H U)
    (ha : 0 < a) (hz : |z| ≤ a) (hH : 0 < H) (hHU : H ≤ U) :
    Summable (fun n : ℕ => spatialTailBlock j a z p.val.2 p.val.1 n) := by
  have hs := (gaussianMajorant_summable a U ha (hH.trans_le hHU)).mul_left (4 * spatialPrefactor j a H)
  exact hs.of_norm_bounded (fun n => spatialTailBlock_bound j a z H U n p ha hz hH hHU)

theorem spatialTailBlock_uniformly_convergent (j : ℕ) (a z H U : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hH : 0 < H) (hHU : H ≤ U) :
    TendstoUniformly
      (fun N : ℕ => fun p : StripPoint a H U =>
        ∑ n ∈ Finset.range N, spatialTailBlock j a z p.val.2 p.val.1 n)
      (fun p : StripPoint a H U => ∑' n : ℕ, spatialTailBlock j a z p.val.2 p.val.1 n) atTop := by
  have hs := (gaussianMajorant_summable a U ha (hH.trans_le hHU)).mul_left (4 * spatialPrefactor j a H)
  apply tendstoUniformly_tsum_nat hs
  intro n p
  exact spatialTailBlock_bound j a z H U n p ha hz hH hHU

end Shao.C2.IntervalImageSpatialConvergence
