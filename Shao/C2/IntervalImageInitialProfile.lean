import Shao.C2.BrownianSineStoppedLimit
import Shao.C2.IntervalImageSmallTimeSum

noncomputable section
namespace Shao.C2.IntervalImageInitialProfile
open MeasureTheory Set Filter
open scoped NNReal Topology
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageSmallTimeSum
open Shao.C2.CompletionFirstProfile

theorem intervalImageCandidate_small_time_bounded (a z U x : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hU : 0 < U) (hx : |x| ≤ a) (hsmall : U ≤ a ^ 2) :
    |intervalImageCandidate a z U x| ≤ 17 := by
  have hxl := abs_le.mp hx
  have hzl := abs_le.mp hz
  have hup : upperProfile a x U z ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg
    · have hh := mul_nonneg (sub_nonneg.mpr hxl.2) (sub_nonneg.mpr hzl.2)
      nlinarith
    · exact hU.le
  have hlo : lowerProfile a x U z ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg
    · have hh := mul_nonneg (show 0 ≤ a + x by linarith) (show 0 ≤ a + z by linarith)
      nlinarith
    · exact hU.le
  have hp : intervalProfile a x U z ≤ 2 := by
    dsimp only [intervalProfile]
    linarith
  have hh := intervalImageCandidate_sub_one_smallTime_profile a z U x ha hz hU hx hsmall
  have ht : |intervalImageCandidate a z U x| ≤ |intervalImageCandidate a z U x - 1| + 1 := by
    simpa only [sub_add_cancel, abs_one] using abs_add_le (intervalImageCandidate a z U x - 1) (1 : ℝ)
  linarith

private theorem exp_neg_div_initial_limit (F : ℝ≥0 → ℝ) (c : ℝ) (hc : 0 < c)
    (hF : Tendsto F (𝓝 0) (𝓝 c)) :
    Tendsto (fun T : ℝ≥0 => Real.exp (-F T / (T : ℝ))) (𝓝[>] 0) (𝓝 0) := by
  have ht : Tendsto (fun T : ℝ≥0 => (T : ℝ)) (𝓝[>] 0) (𝓝[>] (0 : ℝ)) :=
    (NNReal.map_coe_nhdsGT 0).le
  have hi : Tendsto (fun T : ℝ≥0 => (T : ℝ)⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.comp ht
  have hr := Filter.Tendsto.pos_mul_atTop hc (hF.mono_left nhdsWithin_le_nhds) hi
  simpa only [Function.comp_def, neg_mul, div_eq_mul_inv] using
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hr

theorem intervalImageCandidate_initial_diagonal (a z w : ℝ)
    (ha : 0 < a) (hz : |z| < a) :
    Tendsto (fun T : ℝ≥0 => intervalImageCandidate a z (T : ℝ)
      (z + Real.sqrt (T : ℝ) * w)) (𝓝[>] 0) (𝓝 1) := by
  let x (T : ℝ≥0) : ℝ := z + Real.sqrt (T : ℝ) * w
  have hx : Tendsto x (𝓝 0) (𝓝 z) := by
    have hc : Continuous x := continuous_const.add
      ((Real.continuous_sqrt.comp NNReal.continuous_coe).mul continuous_const)
    simpa only [x, NNReal.coe_zero, Real.sqrt_zero, zero_mul, add_zero] using hc.tendsto (0 : ℝ≥0)
  have hu : Tendsto (fun T : ℝ≥0 => (a - x T) * (a - z)) (𝓝 0) (𝓝 ((a - z) * (a - z))) :=
    (tendsto_const_nhds.sub hx).mul tendsto_const_nhds
  have hl : Tendsto (fun T : ℝ≥0 => (a + x T) * (a + z)) (𝓝 0) (𝓝 ((a + z) * (a + z))) :=
    (tendsto_const_nhds.add hx).mul tendsto_const_nhds
  have hz' := abs_lt.mp hz
  have heU : Tendsto (fun T : ℝ≥0 => upperProfile a (x T) (T : ℝ) z) (𝓝[>] 0) (𝓝 0) := by
    simpa only [upperProfile, neg_mul] using exp_neg_div_initial_limit _ _
      (mul_pos (sub_pos.mpr hz'.2) (sub_pos.mpr hz'.2)) hu
  have heL : Tendsto (fun T : ℝ≥0 => lowerProfile a (x T) (T : ℝ) z) (𝓝[>] 0) (𝓝 0) := by
    simpa only [lowerProfile, neg_mul] using exp_neg_div_initial_limit _ _
      (mul_pos (show 0 < a + z by linarith) (show 0 < a + z by linarith)) hl
  have hp : Tendsto (fun T : ℝ≥0 => intervalProfile a (x T) (T : ℝ) z) (𝓝[>] 0) (𝓝 0) := by
    simpa only [intervalProfile, add_zero] using heU.add heL
  have h8 : Tendsto (fun T : ℝ≥0 => 8 * intervalProfile a (x T) (T : ℝ) z) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using hp.const_mul 8
  have hinside : ∀ᶠ T in 𝓝[>] (0 : ℝ≥0), |x T| < a :=
    (hx.abs.eventually (gt_mem_nhds hz)).filter_mono nhdsWithin_le_nhds
  have hsmall : ∀ᶠ (T : ℝ≥0) in 𝓝[>] (0 : ℝ≥0), (T : ℝ) < a ^ 2 :=
    ((NNReal.continuous_coe.tendsto 0).eventually
      (gt_mem_nhds (sq_pos_of_pos ha))).filter_mono nhdsWithin_le_nhds
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h8.eventually (gt_mem_nhds hε), hinside, hsmall,
    self_mem_nhdsWithin] with T hbound hi hs hT
  have hT' : 0 < (T : ℝ) := hT
  have hh := intervalImageCandidate_sub_one_smallTime_profile a z (T : ℝ) (x T)
    ha hz.le hT' hi.le hs.le
  change |intervalImageCandidate a z (T : ℝ) (x T) - 1| < ε
  exact hh.trans_lt hbound

end Shao.C2.IntervalImageInitialProfile
