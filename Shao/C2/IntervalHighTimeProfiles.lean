import Shao.C2.IntervalSpectralGaussian

noncomputable section
namespace Shao.C2.IntervalHighTimeProfiles
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.CompletionFirstProfile Shao.C2.HalfLineTaylorSegment Shao.C2.IntervalGaussianLocal

theorem highTime_drift_bound (a y z T : ℝ) (ha : 0 < a) (hy : |y| ≤ a) (hz : |z| ≤ a)
    (hT : 0 < T) (hHigh : a ^ 2 ≤ T) :
    |z - y| / Real.sqrt T ≤ 2 ∧ 1 + |z - y| / Real.sqrt T ≤ 3 := by
  have hroot : a ≤ Real.sqrt T := by
    nlinarith only [Real.sq_sqrt hT.le, Real.sqrt_nonneg T, hHigh, ha]
  have hd : |z - y| ≤ 2 * a := abs_le.2 ⟨by linarith only [(abs_le.mp hz).1, (abs_le.mp hy).2],
    by linarith only [(abs_le.mp hz).2, (abs_le.mp hy).1]⟩
  have hdiv : |z - y| / Real.sqrt T ≤ 2 :=
    (div_le_iff₀ (Real.sqrt_pos.mpr hT)).2 (by linarith only [hd, hroot])
  exact ⟨hdiv, by linarith only [hdiv]⟩

theorem highTime_wall_products (a y z T : ℝ) (ha : 0 < a) (hy : |y| ≤ a) (hz : |z| ≤ a)
    (hHigh : a ^ 2 ≤ T) :
    (0 ≤ (a - y) * (a - z) ∧ (a - y) * (a - z) ≤ 4 * T) ∧
      (0 ≤ (a + y) * (a + z) ∧ (a + y) * (a + z) ≤ 4 * T) := by
  have hu0 : 0 ≤ a - y := by linarith only [(abs_le.mp hy).2]
  have hv0 : 0 ≤ a - z := by linarith only [(abs_le.mp hz).2]
  have hl0 : 0 ≤ a + y := by linarith only [(abs_le.mp hy).1]
  have hw0 : 0 ≤ a + z := by linarith only [(abs_le.mp hz).1]
  have hu : a - y ≤ 2 * a := by linarith only [(abs_le.mp hy).1]
  have hv : a - z ≤ 2 * a := by linarith only [(abs_le.mp hz).1]
  have hl : a + y ≤ 2 * a := by linarith only [(abs_le.mp hy).2]
  have hw : a + z ≤ 2 * a := by linarith only [(abs_le.mp hz).2]
  have h1 := mul_le_mul hu hv hv0 (by positivity : 0 ≤ 2 * a)
  have h2 := mul_le_mul hl hw hw0 (by positivity : 0 ≤ 2 * a)
  exact ⟨⟨mul_nonneg hu0 hv0, by nlinarith only [h1, hHigh]⟩,
    ⟨mul_nonneg hl0 hw0, by nlinarith only [h2, hHigh]⟩⟩

theorem intervalProfile_le_increment (a y z T b : ℝ) (hy : |y| ≤ a) (hz : |z| ≤ a)
    (hT : 0 < T) :
    intervalProfile a y T z ≤ intervalIncrementProfile a y T z b := by
  have hm (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
      Real.exp (-u * v / T) ≤ incrementProfile u v T b := by
    have hmax : max (u - |b|) 0 ≤ u := max_le (by linarith only [abs_nonneg b]) hu
    have hnum := mul_le_mul_of_nonneg_right hmax hv
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (by linarith only [hnum]) hT.le
  have hU := hm (a - y) (a - z) (by linarith only [(abs_le.mp hy).2])
    (by linarith only [(abs_le.mp hz).2])
  have hL := hm (a + y) (a + z) (by linarith only [(abs_le.mp hy).1])
    (by linarith only [(abs_le.mp hz).1])
  exact add_le_add hU hL

theorem intervalProfile_highTime_lower (a y z T : ℝ) (ha : 0 < a) (hy : |y| ≤ a)
    (hz : |z| ≤ a) (hT : 0 < T) (hHigh : a ^ 2 ≤ T) :
    2 * Real.exp (-4) ≤ intervalProfile a y T z := by
  have hprod := highTime_wall_products a y z T ha hy hz hHigh
  have hU : Real.exp (-4) ≤ upperProfile a y T z := by
    apply Real.exp_le_exp.mpr
    exact (le_div_iff₀ hT).2 (by linarith only [hprod.1.2])
  have hL : Real.exp (-4) ≤ lowerProfile a y T z := by
    apply Real.exp_le_exp.mpr
    exact (le_div_iff₀ hT).2 (by linarith only [hprod.2.2])
  simpa only [two_mul, intervalProfile] using add_le_add hU hL

theorem intervalIncrementProfile_highTime_lower (a y z T b : ℝ) (ha : 0 < a) (hy : |y| ≤ a)
    (hz : |z| ≤ a) (hT : 0 < T) (hHigh : a ^ 2 ≤ T) :
    2 * Real.exp (-4) ≤ intervalIncrementProfile a y T z b := by
  exact (intervalProfile_highTime_lower a y z T ha hy hz hT hHigh).trans
    (intervalProfile_le_increment a y z T b hy hz hT)

theorem highTime_bound_to_profile (a y z T R B : ℝ) (ha : 0 < a) (hy : |y| ≤ a)
    (hz : |z| ≤ a) (hT : 0 < T) (hHigh : a ^ 2 ≤ T) (hB : 0 ≤ B) (hR : |R| ≤ B) :
    |R| ≤ (Real.exp 4 / 2 * B) * intervalProfile a y T z := by
  have hP := intervalProfile_highTime_lower a y z T ha hy hz hT hHigh
  have hE : Real.exp 4 * Real.exp (-4) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hfactor : 1 ≤ Real.exp 4 / 2 * intervalProfile a y T z := by
    calc
      _ = Real.exp 4 / 2 * (2 * Real.exp (-4)) := by rw [← hE]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hP (by positivity)
  calc
    _ ≤ B := hR
    _ = B * 1 := by ring
    _ ≤ B * (Real.exp 4 / 2 * intervalProfile a y T z) := mul_le_mul_of_nonneg_left hfactor hB
    _ = _ := by ring

end Shao.C2.IntervalHighTimeProfiles

