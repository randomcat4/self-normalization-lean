import Shao.C2.ProjectionOvershoot

noncomputable section
namespace Shao.C2.GaussianWallEnvelope
open Shao.C2.HalfLineTaylorSegment

def wallEnvelope (w B e T : ℝ) : ℝ :=
  Real.exp (-((max (w - (B + max e 0)) 0) ^ 2) / T)

theorem wall_product_lower_bound (w B e : ℝ) (hw : 0 < w) (hB : 0 ≤ B) (he : e < w) :
    (max (w - (B + max e 0)) 0) ^ 2 ≤ max (w - B) 0 * (w - e) := by
  have hMB : B ≤ B + max e 0 := by linarith only [le_max_right e 0]
  have hMe : e ≤ B + max e 0 := by linarith only [hB, le_max_left e 0]
  have h1 : max (w - (B + max e 0)) 0 ≤ max (w - B) 0 :=
    max_le_max (by linarith only [hMB]) (le_refl 0)
  have h2 : max (w - (B + max e 0)) 0 ≤ w - e :=
    max_le (by linarith only [hMe]) (sub_pos.mpr he).le
  have h := mul_le_mul h1 h2 (le_max_right (w - (B + max e 0)) 0)
    (le_max_right (w - B) 0)
  simpa only [pow_two] using h

theorem increment_profile_le_wallEnvelope (w e T b : ℝ) (hw : 0 < w)
    (he : e < w) (hT : 0 < T) :
    incrementProfile w (w - e) T b ≤ wallEnvelope w |b| e T := by
  have h := wall_product_lower_bound w |b| e hw (abs_nonneg b) he
  dsimp only [incrementProfile, wallEnvelope]
  apply Real.exp_le_exp.2
  have hh := (div_le_div_iff_of_pos_right hT).2 (neg_le_neg h)
  convert hh using 1 <;> ring

theorem initial_profile_le_wallEnvelope (w e T b : ℝ) (hw : 0 < w)
    (he : e < w) (hT : 0 < T) :
    Real.exp (-w * (w - e) / T) ≤ wallEnvelope w |b| e T := by
  have h := wall_product_lower_bound w |b| e hw (abs_nonneg b) he
  have hA : max (w - |b|) 0 ≤ w := max_le (by linarith only [abs_nonneg b]) hw.le
  have hp := mul_le_mul_of_nonneg_right hA (sub_pos.mpr he).le
  have hR := h.trans hp
  dsimp only [wallEnvelope]
  apply Real.exp_le_exp.2
  have hh := (div_le_div_iff_of_pos_right hT).2 (neg_le_neg hR)
  convert hh using 1 <;> ring

theorem future_reflection_deficit_le_wallEnvelope (w e T b : ℝ) (hw : 0 < w)
    (he : e < w) (hT : 0 < T) (hnew : 0 ≤ w - b) (hfuture : 0 < T - b ^ 2) :
    Real.exp (-2 * (w - b) * (w - e) / (T - b ^ 2)) ≤ wallEnvelope w |b| e T := by
  let M := |b| + max e 0
  let r := max (w - M) 0
  have hMb : b ≤ M := by dsimp only [M]; linarith only [le_abs_self b, le_max_right e 0]
  have hMe : e ≤ M := by dsimp only [M]; linarith only [abs_nonneg b, le_max_left e 0]
  have hRu : r ≤ w - b := max_le (by linarith only [hMb]) hnew
  have hRv : r ≤ w - e := max_le (by linarith only [hMe]) (sub_pos.mpr he).le
  have hR0 : 0 ≤ r := le_max_right (w - M) 0
  have hprod : r ^ 2 ≤ (w - b) * (w - e) := by
    simpa only [pow_two] using mul_le_mul hRu hRv hR0 hnew
  have hp0 : 0 ≤ (w - b) * (w - e) := mul_nonneg hnew (sub_pos.mpr he).le
  have hE : T - b ^ 2 ≤ T := by linarith only [sq_nonneg b]
  have hr1 : r ^ 2 / T ≤ (w - b) * (w - e) / T := (div_le_div_iff_of_pos_right hT).2 hprod
  have hr2 := div_le_div_of_nonneg_left hp0 hfuture hE
  have hr3 : (w - b) * (w - e) / (T - b ^ 2) ≤ 2 * (w - b) * (w - e) / (T - b ^ 2) := by
    have hp := div_nonneg hp0 hfuture.le
    calc
      _ = 1 * ((w - b) * (w - e) / (T - b ^ 2)) := by ring
      _ ≤ 2 * ((w - b) * (w - e) / (T - b ^ 2)) := mul_le_mul_of_nonneg_right (by norm_num) hp
      _ = _ := by ring
  dsimp only [wallEnvelope]
  apply Real.exp_le_exp.2
  change -2 * (w - b) * (w - e) / (T - b ^ 2) ≤ -(r ^ 2) / T
  convert neg_le_neg (hr1.trans (hr2.trans hr3)) using 1 <;> ring

theorem crossing_wallEnvelope_eq_one (w b e T : ℝ) (hw : 0 < w) (hcross : w ≤ |b|) :
    wallEnvelope w |b| e T = 1 := by
  have hM : w ≤ |b| + max e 0 := by linarith only [hcross, le_max_right e 0]
  have hr : max (w - (|b| + max e 0)) 0 = 0 := max_eq_right (sub_nonpos.mpr hM)
  dsimp only [wallEnvelope]
  rw [hr]
  norm_num

theorem wallEnvelope_bounds (w B e T : ℝ) (hT : 0 < T) :
    0 < wallEnvelope w B e T ∧ wallEnvelope w B e T ≤ 1 := by
  dsimp only [wallEnvelope]
  constructor
  · exact Real.exp_pos _
  · calc
      _ ≤ Real.exp 0 := Real.exp_le_exp.2
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) hT.le)
      _ = 1 := Real.exp_zero

end Shao.C2.GaussianWallEnvelope
