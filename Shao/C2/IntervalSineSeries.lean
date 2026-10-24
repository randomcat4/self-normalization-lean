import Shao.C2.IntervalSineTerms

noncomputable section
namespace Shao.C2.IntervalSineSeries
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalSineTerms Shao.C2.IntervalSpectralGaussian

def mixedSineSeries (j l : ℕ) (a z T y : ℝ) : ℝ :=
  ∑' n : ℕ, mixedSineTerm j l a z T y n

theorem mixedSineTerm_strip_bound (j l : ℕ) (a z H T y : ℝ) (n : ℕ)
    (ha : 0 < a) (hHT : H ≤ T) :
    ‖mixedSineTerm j l a z T y n‖ ≤
      ((1 / a) * (Real.pi / (2 * a)) ^ j * (Real.pi ^ 2 / (8 * a ^ 2)) ^ l) *
        weightedGaussian (Real.pi ^ 2 / 8) (j + 2 * l) (H / a ^ 2) n := by
  apply (mixedSineTerm_weighted_bound j l a z T y n ha).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  dsimp only [weightedGaussian]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hdiv : H / a ^ 2 ≤ T / a ^ 2 := div_le_div_of_nonneg_right hHT (sq_nonneg a)
  exact mul_le_mul_of_nonpos_left hdiv
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg _))

theorem mixedSineSeries_spatial_hasDerivAt (j l : ℕ) (a z T y : ℝ)
    (ha : 0 < a) (hT : 0 < T) :
    HasDerivAt (mixedSineSeries j l a z T) (mixedSineSeries (j + 1) l a z T y) y := by
  have hu := (weightedGaussian_summable (Real.pi ^ 2 / 8) (T / a ^ 2) ((j + 1) + 2 * l)
    (by positivity) (by positivity)).mul_left
      ((1 / a) * (Real.pi / (2 * a)) ^ (j + 1) * (Real.pi ^ 2 / (8 * a ^ 2)) ^ l)
  have hg : ∀ n w, w ∈ Ioo (y - 1) (y + 1) →
      HasDerivAt (fun v => mixedSineTerm j l a z T v n)
        (mixedSineTerm (j + 1) l a z T w n) w := by
    intro n w _
    exact mixedSineTerm_spatial_hasDerivAt j l a z T w n
  have hg' : ∀ n w, w ∈ Ioo (y - 1) (y + 1) →
      ‖mixedSineTerm (j + 1) l a z T w n‖ ≤
        ((1 / a) * (Real.pi / (2 * a)) ^ (j + 1) * (Real.pi ^ 2 / (8 * a ^ 2)) ^ l) *
          weightedGaussian (Real.pi ^ 2 / 8) ((j + 1) + 2 * l) (T / a ^ 2) n := by
    intro n w _
    exact mixedSineTerm_weighted_bound (j + 1) l a z T w n ha
  have hyI : y ∈ Ioo (y - 1) (y + 1) := by constructor <;> linarith
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    hg hg' hyI (mixedSineTerm_summable j l a z T y ha hT) hyI

theorem mixedSineSeries_time_hasDerivAt (j l : ℕ) (a z T y : ℝ)
    (ha : 0 < a) (hT : 0 < T) :
    HasDerivAt (fun S => mixedSineSeries j l a z S y)
      (mixedSineSeries j (l + 1) a z T y) T := by
  have hH : 0 < T / 2 := by linarith only [hT]
  have hTI : T ∈ Ioo (T / 2) (2 * T) := by constructor <;> linarith only [hT]
  have hu := (weightedGaussian_summable (Real.pi ^ 2 / 8) ((T / 2) / a ^ 2) (j + 2 * (l + 1))
    (by positivity) (by positivity)).mul_left
      ((1 / a) * (Real.pi / (2 * a)) ^ j * (Real.pi ^ 2 / (8 * a ^ 2)) ^ (l + 1))
  have hg : ∀ n S, S ∈ Ioo (T / 2) (2 * T) →
      HasDerivAt (fun V => mixedSineTerm j l a z V y n)
        (mixedSineTerm j (l + 1) a z S y n) S := by
    intro n S _
    exact mixedSineTerm_time_hasDerivAt j l a z S y n
  have hg' : ∀ n S, S ∈ Ioo (T / 2) (2 * T) →
      ‖mixedSineTerm j (l + 1) a z S y n‖ ≤
        ((1 / a) * (Real.pi / (2 * a)) ^ j * (Real.pi ^ 2 / (8 * a ^ 2)) ^ (l + 1)) *
          weightedGaussian (Real.pi ^ 2 / 8) (j + 2 * (l + 1)) ((T / 2) / a ^ 2) n := by
    intro n S hS
    exact mixedSineTerm_strip_bound j (l + 1) a z (T / 2) S y n ha hS.1.le
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    hg hg' hTI (mixedSineTerm_summable j l a z T y ha hT) hTI

theorem mixedSineSeries_spatial_iteratedDeriv (j l : ℕ) (a z T y : ℝ)
    (ha : 0 < a) (hT : 0 < T) :
    iteratedDeriv j (mixedSineSeries 0 l a z T) y = mixedSineSeries j l a z T y := by
  induction j generalizing y with
  | zero => rfl
  | succ j ih =>
    have heq : iteratedDeriv j (mixedSineSeries 0 l a z T) = mixedSineSeries j l a z T := by
      funext w
      exact ih w
    rw [iteratedDeriv_succ, heq]
    exact (mixedSineSeries_spatial_hasDerivAt j l a z T y ha hT).deriv

theorem mixedSineSeries_time_iteratedDeriv (j l : ℕ) (a z T y : ℝ)
    (ha : 0 < a) (hT : 0 < T) :
    iteratedDeriv l (fun S => mixedSineSeries j 0 a z S y) T =
      mixedSineSeries j l a z T y := by
  induction l generalizing T with
  | zero => rfl
  | succ l ih =>
    have heq : iteratedDeriv l (fun S => mixedSineSeries j 0 a z S y) =ᶠ[𝓝 T]
        (fun S => mixedSineSeries j l a z S y) := by
      filter_upwards [isOpen_Ioi.mem_nhds hT] with S hS
      exact ih S hS
    rw [iteratedDeriv_succ]
    exact heq.deriv_eq.trans (mixedSineSeries_time_hasDerivAt j l a z T y ha hT).deriv

theorem sineSeries_mixed_iteratedDeriv (j l : ℕ) (a z T y : ℝ)
    (ha : 0 < a) (hT : 0 < T) :
    iteratedDeriv l (fun S => iteratedDeriv j (mixedSineSeries 0 0 a z S) y) T =
      mixedSineSeries j l a z T y := by
  have heq : (fun S => iteratedDeriv j (mixedSineSeries 0 0 a z S) y) =ᶠ[𝓝 T]
      (fun S => mixedSineSeries j 0 a z S y) := by
    filter_upwards [isOpen_Ioi.mem_nhds hT] with S hS
    exact mixedSineSeries_spatial_iteratedDeriv j 0 a z S y ha hS
  exact (Filter.EventuallyEq.iteratedDeriv_eq l heq).trans
    (mixedSineSeries_time_iteratedDeriv j l a z T y ha hT)

theorem sineSeries_mixed_commutation (j l : ℕ) (a z T y : ℝ)
    (ha : 0 < a) (hT : 0 < T) :
    iteratedDeriv j (fun w => iteratedDeriv l (fun S => mixedSineSeries 0 0 a z S w) T) y =
      iteratedDeriv l (fun S => iteratedDeriv j (mixedSineSeries 0 0 a z S) y) T := by
  have heq : (fun w => iteratedDeriv l (fun S => mixedSineSeries 0 0 a z S w) T) =
      mixedSineSeries 0 l a z T := by
    funext w
    exact mixedSineSeries_time_iteratedDeriv 0 l a z T w ha hT
  rw [heq, mixedSineSeries_spatial_iteratedDeriv j l a z T y ha hT,
    sineSeries_mixed_iteratedDeriv j l a z T y ha hT]

theorem mixedSineSeries_weighted_bound (j l : ℕ) (a z T y : ℝ)
    (ha : 0 < a) (hT : 0 < T) :
    ‖mixedSineSeries j l a z T y‖ ≤
      ((1 / a) * (Real.pi / (2 * a)) ^ j * (Real.pi ^ 2 / (8 * a ^ 2)) ^ l) *
        (∑' n : ℕ, weightedGaussian (Real.pi ^ 2 / 8) (j + 2 * l) (T / a ^ 2) n) := by
  have hs := mixedSineTerm_summable j l a z T y ha hT
  have hu := (weightedGaussian_summable (Real.pi ^ 2 / 8) (T / a ^ 2) (j + 2 * l)
    (by positivity) (by positivity)).hasSum.mul_left
      ((1 / a) * (Real.pi / (2 * a)) ^ j * (Real.pi ^ 2 / (8 * a ^ 2)) ^ l)
  exact hs.hasSum.norm_le_of_bounded hu
    (fun n => mixedSineTerm_weighted_bound j l a z T y n ha)

end Shao.C2.IntervalSineSeries
