import Shao.C2.IntervalReciprocalDerivatives

noncomputable section
namespace Shao.C2.IntervalReciprocalHighTime
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalReciprocalDerivatives Shao.C2.IntervalHighTimeProfiles

def reciprocalHighTimeConstant : ℝ := 32 * Real.sqrt (2 * Real.pi) * Real.exp 2

theorem reciprocalCoefficient_scaling (j l : ℕ) (d T : ℝ)
    (hjl : j + l ≤ 3) (hT : 0 < T) :
    reciprocalCoefficient j l d T =
      reciprocalCoefficient j l (d / Real.sqrt T) 1 *
        (1 / Real.sqrt T) ^ (j + 2 * l) := by
  generalize hRdef : Real.sqrt T = R
  have hR : 0 < R := hRdef ▸ Real.sqrt_pos.mpr hT
  have hRsq : R ^ 2 = T := by rw [← hRdef]; exact Real.sq_sqrt hT.le
  rw [← hRsq]
  have cases : (j = 0 ∧ l = 0) ∨ (j = 1 ∧ l = 0) ∨ (j = 2 ∧ l = 0) ∨
      (j = 3 ∧ l = 0) ∨ (j = 0 ∧ l = 1) ∨ (j = 1 ∧ l = 1) ∨ (j = 2 ∧ l = 1) ∨
      (j = 0 ∧ l = 2) ∨ (j = 1 ∧ l = 2) ∨ (j = 0 ∧ l = 3) := by omega
  rcases cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [reciprocalCoefficient.eq_1, reciprocalCoefficient.eq_2, reciprocalCoefficient.eq_3, reciprocalCoefficient.eq_4, reciprocalCoefficient.eq_5, reciprocalCoefficient.eq_6, reciprocalCoefficient.eq_7, reciprocalCoefficient.eq_8, reciprocalCoefficient.eq_9, reciprocalCoefficient.eq_10]
    ring_nf <;> field_simp [ne_of_gt hR] <;> ring

theorem reciprocalCoefficient_unit_bound (j l : ℕ) (d : ℝ)
    (hjl : j + l ≤ 3) (hd : |d| ≤ 2) :
    |reciprocalCoefficient j l d 1| ≤ 32 := by
  have hp (n : ℕ) : -(2 : ℝ) ^ n ≤ d ^ n ∧ d ^ n ≤ (2 : ℝ) ^ n := by
    apply abs_le.mp
    simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg d) hd n
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  have h4 := hp 4
  have h5 := hp 5
  have h6 := hp 6
  norm_num at h1 h2 h3 h4 h5 h6
  have cases : (j = 0 ∧ l = 0) ∨ (j = 1 ∧ l = 0) ∨ (j = 2 ∧ l = 0) ∨
      (j = 3 ∧ l = 0) ∨ (j = 0 ∧ l = 1) ∨ (j = 1 ∧ l = 1) ∨ (j = 2 ∧ l = 1) ∨
      (j = 0 ∧ l = 2) ∨ (j = 1 ∧ l = 2) ∨ (j = 0 ∧ l = 3) := by omega
  rcases cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [reciprocalCoefficient.eq_1, reciprocalCoefficient.eq_2, reciprocalCoefficient.eq_3, reciprocalCoefficient.eq_4, reciprocalCoefficient.eq_5, reciprocalCoefficient.eq_6, reciprocalCoefficient.eq_7, reciprocalCoefficient.eq_8, reciprocalCoefficient.eq_9, reciprocalCoefficient.eq_10]
    apply abs_le.mpr
    constructor <;> nlinarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2,
      h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]

theorem reciprocalFreeDensity_drift_bound (z T y : ℝ)
    (hT : 0 < T) (hd : |z - y| ≤ 2 * Real.sqrt T) :
    ‖reciprocalFreeDensity z T y‖ ≤
      Real.sqrt (2 * Real.pi) * Real.exp 2 * Real.sqrt T := by
  have hR : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hp := pow_le_pow_left₀ (abs_nonneg (z - y)) hd 2
  rw [sq_abs] at hp
  have hsq : (z - y) ^ 2 ≤ 4 * T := by nlinarith only [hp, Real.sq_sqrt hT.le]
  have hq : (z - y) ^ 2 / (2 * T) ≤ 2 :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * T)).mpr (by nlinarith only [hsq])
  have hg : 0 ≤ reciprocalFreeDensity z T y := by dsimp only [reciprocalFreeDensity]; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hg]
  calc
    _ ≤ Real.sqrt (2 * Real.pi) * Real.sqrt T * Real.exp 2 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hq) (by positivity)
    _ = _ := by ring

theorem reciprocalMixedFamily_drift_bound (j l : ℕ) (z T y : ℝ)
    (hjl : j + l ≤ 3) (hT : 0 < T) (hd : |z - y| ≤ 2 * Real.sqrt T) :
    ‖reciprocalMixedFamily j l z T y‖ ≤
      reciprocalHighTimeConstant * Real.sqrt T *
        (1 / Real.sqrt T) ^ (j + 2 * l) := by
  have hR : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hd' : |(z - y) / Real.sqrt T| ≤ 2 := by
    rw [abs_div, abs_of_pos hR]
    exact (div_le_iff₀ hR).mpr hd
  have hcoef : |reciprocalCoefficient j l (z - y) T| ≤
      32 * (1 / Real.sqrt T) ^ (j + 2 * l) := by
    rw [reciprocalCoefficient_scaling j l (z - y) T hjl hT, abs_mul, abs_pow,
      abs_of_pos (one_div_pos.mpr hR)]
    exact mul_le_mul_of_nonneg_right (reciprocalCoefficient_unit_bound j l _ hjl hd')
      (by positivity)
  rw [reciprocalMixedFamily, norm_mul]
  change |reciprocalCoefficient j l (z - y) T| * ‖reciprocalFreeDensity z T y‖ ≤ _
  calc
    _ ≤ (32 * (1 / Real.sqrt T) ^ (j + 2 * l)) *
        (Real.sqrt (2 * Real.pi) * Real.exp 2 * Real.sqrt T) :=
      mul_le_mul hcoef (reciprocalFreeDensity_drift_bound z T y hT hd) (norm_nonneg _) (by positivity)
    _ = _ := by dsimp only [reciprocalHighTimeConstant]; ring

theorem reciprocalFreeDensity_mixed_drift_bound (j l : ℕ) (z T y : ℝ)
    (hjl : j + l ≤ 3) (hT : 0 < T) (hd : |z - y| ≤ 2 * Real.sqrt T) :
    ‖iteratedDeriv l (fun S => iteratedDeriv j (reciprocalFreeDensity z S) y) T‖ ≤
      reciprocalHighTimeConstant * Real.sqrt T *
        (1 / Real.sqrt T) ^ (j + 2 * l) := by
  rw [reciprocalFreeDensity_mixed_iteratedDeriv j l z T y hjl hT]
  exact reciprocalMixedFamily_drift_bound j l z T y hjl hT hd

theorem reciprocalFreeDensity_mixed_highTime_bound (j l : ℕ) (a z T y : ℝ)
    (hjl : j + l ≤ 3) (ha : 0 < a) (hT : 0 < T) (hlarge : a ^ 2 ≤ T)
    (hy : |y| ≤ a) (hz : |z| ≤ a) :
    ‖iteratedDeriv l (fun S => iteratedDeriv j (reciprocalFreeDensity z S) y) T‖ ≤
      reciprocalHighTimeConstant * Real.sqrt T *
        (1 / Real.sqrt T) ^ (j + 2 * l) := by
  have hd : |z - y| ≤ 2 * Real.sqrt T :=
    (div_le_iff₀ (Real.sqrt_pos.mpr hT)).mp (highTime_drift_bound a y z T ha hy hz hT hlarge).1
  exact reciprocalFreeDensity_mixed_drift_bound j l z T y hjl hT hd

end Shao.C2.IntervalReciprocalHighTime
