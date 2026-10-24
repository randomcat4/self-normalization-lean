import Shao.OQ6.NormalizedRemainderEnvelope
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Tilted

set_option autoImplicit false

namespace Shao.OQ6.NormalizedAnalyticCostLimits

noncomputable section

open MeasureTheory
open scoped BigOperators Classical Topology

theorem actual_normalization_sequence_limits
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (hξ2 : ∀ i : Fin n, MemLp (ξ i) 2 ν)
    (hξmean : ∀ i : Fin n, (∫ ω, ξ i ω ∂ν) = 0)
    (hξenergy : (∑ i : Fin n, ∫ ω, (ξ i ω) ^ 2 ∂ν) = 1)
    (Y : ℕ → Fin n → Ω → ℝ)
    (hY : ∀ (k : ℕ) (i : Fin n), Measurable (Y k i))
    (ε : ℕ → ℝ) (hε : ∀ k : ℕ, 0 < ε k)
    (hεsmall : ∀ k : ℕ, ε k < 1 / (4 * Real.sqrt (n : ℝ)))
    (hεlim : Filter.Tendsto ε Filter.atTop (nhds (0 : ℝ)))
    (herr : ∀ (k : ℕ) (i : Fin n) (ω : Ω), |Y k i ω - ξ i ω| ≤ ε k) :
    let μ : ℕ → Fin n → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν (Y k)
    let s : ℕ → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν (Y k)
    let η : ℕ → Fin n → Ω → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
    let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
    let Wη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, η k i ω
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
    let Vη : ℕ → Ω → ℝ := fun k ω => Real.sqrt (∑ i : Fin n, (η k i ω) ^ 2)
    let ρ : ℕ → ℝ := fun k => 4 * ε k * Real.sqrt (n : ℝ)
    (∀ (k : ℕ) (i : Fin n), |μ k i| ≤ ε k) ∧
    (∀ k : ℕ, |s k - 1| ≤ 2 * ε k * Real.sqrt (n : ℝ) ∧ (1 / 2 : ℝ) < s k) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => μ k i) Filter.atTop (nhds (0 : ℝ))) ∧
    Filter.Tendsto s Filter.atTop (nhds (1 : ℝ)) ∧
    Filter.Tendsto ρ Filter.atTop (nhds (0 : ℝ)) ∧
    (∀ (k : ℕ) (i : Fin n), Measurable (η k i) ∧ MemLp (η k i) 2 ν) ∧
    (∀ (k : ℕ) (i : Fin n) (ω : Ω), |η k i ω| ≤ 2 * |ξ i ω| + 1) ∧
    (∀ (i : Fin n) (ω : Ω), Filter.Tendsto (fun k : ℕ => η k i ω) Filter.atTop (nhds (ξ i ω))) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => Wη k ω) Filter.atTop (nhds (W ω))) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => Vη k ω) Filter.atTop (nhds (V ω))) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => ∫ ω, |η k i ω - ξ i ω| ∂ν)
      Filter.atTop (nhds (0 : ℝ))) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => ∫ ω, (η k i ω - ξ i ω) ^ 2 ∂ν)
      Filter.atTop (nhds (0 : ℝ))) := by
  classical
  dsimp only
  let μ : ℕ → Fin n → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν (Y k)
  let s : ℕ → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν (Y k)
  let η : ℕ → Fin n → Ω → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
  let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
  let Wη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, η k i ω
  let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
  let Vη : ℕ → Ω → ℝ := fun k ω => Real.sqrt (∑ i : Fin n, (η k i ω) ^ 2)
  let ρ : ℕ → ℝ := fun k => 4 * ε k * Real.sqrt (n : ℝ)
  have hcs (k : ℕ) :
      (∀ i : Fin n, |μ k i| ≤ ε k) ∧
      |s k - 1| ≤ 2 * ε k * Real.sqrt (n : ℝ) := by
    rcases Shao.OQ6.ActualMomentNormalization.actual_centering_and_scale_spec
      ν n hn ξ (Y k) hξ hξ2 hξmean hξenergy (hY k) (ε k) (hε k).le (herr k) with
      ⟨_, _, _, _, _, _, _, hm, _, _, _, hs⟩
    exact ⟨hm, hs⟩
  have hspec (k : ℕ) :
      (1 / 2 : ℝ) < s k ∧
      (∀ i : Fin n, Measurable (η k i) ∧ MemLp (η k i) 2 ν) ∧
      (∀ ω : Ω, |Vη k ω - V ω| ≤ ρ k * (1 + V ω)) ∧
      (∀ ω : Ω, |Wη k ω - W ω| ≤ Real.sqrt (n : ℝ) * ρ k * (1 + V ω)) ∧
      (∀ (i : Fin n) (ω : Ω), |η k i ω| ≤ 2 * |ξ i ω| + 4 * ε k) ∧
      (∀ (i : Fin n) (ω : Ω), |η k i ω - ξ i ω| ≤ 4 * ε k + ρ k * |ξ i ω|) := by
    rcases Shao.OQ6.ActualMomentNormalization.actual_moment_normalization_spec
      ν n hn ξ (Y k) hξ hξ2 hξmean hξenergy (hY k) (ε k) (hε k) (hεsmall k) (herr k) with
      ⟨hs, hm, h2, _, _, _, _, _, _, hV, hW, hb, he⟩
    exact ⟨hs, (fun i => ⟨hm i, h2 i⟩), hV, hW, hb, he⟩
  have hρlim : Filter.Tendsto ρ Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [ρ, mul_zero, zero_mul] using
      (hεlim.const_mul (4 : ℝ)).mul_const (Real.sqrt (n : ℝ))
  have hlimabs (f g : ℕ → ℝ) (a : ℝ)
      (hg : Filter.Tendsto g Filter.atTop (nhds (0 : ℝ)))
      (hb : ∀ k : ℕ, |f k - a| ≤ g k) :
      Filter.Tendsto f Filter.atTop (nhds a) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [Real.norm_eq_abs]
    exact squeeze_zero' (Filter.Eventually.of_forall fun k => abs_nonneg (f k - a))
      (Filter.Eventually.of_forall hb) hg
  have hμlim (i : Fin n) : Filter.Tendsto (fun k : ℕ => μ k i)
      Filter.atTop (nhds (0 : ℝ)) := by
    apply hlimabs _ ε 0 hεlim
    intro k
    simpa only [sub_zero] using (hcs k).1 i
  have hslim : Filter.Tendsto s Filter.atTop (nhds (1 : ℝ)) := by
    apply hlimabs _ (fun k => 2 * ε k * Real.sqrt (n : ℝ)) 1
    · simpa only [mul_zero, zero_mul] using
        (hεlim.const_mul (2 : ℝ)).mul_const (Real.sqrt (n : ℝ))
    · exact fun k => (hcs k).2
  have hηpoint (i : Fin n) (ω : Ω) :
      Filter.Tendsto (fun k : ℕ => η k i ω) Filter.atTop (nhds (ξ i ω)) := by
    apply hlimabs _ (fun k => 4 * ε k + ρ k * |ξ i ω|) (ξ i ω)
    · simpa only [mul_zero, zero_mul, add_zero] using
        (hεlim.const_mul (4 : ℝ)).add (hρlim.mul_const |ξ i ω|)
    · exact fun k => (hspec k).2.2.2.2.2 i ω
  have hWpoint (ω : Ω) :
      Filter.Tendsto (fun k : ℕ => Wη k ω) Filter.atTop (nhds (W ω)) := by
    apply hlimabs _ (fun k => Real.sqrt (n : ℝ) * ρ k * (1 + V ω)) (W ω)
    · simpa only [mul_zero, zero_mul] using
        (hρlim.const_mul (Real.sqrt (n : ℝ))).mul_const (1 + V ω)
    · exact fun k => (hspec k).2.2.2.1 ω
  have hVpoint (ω : Ω) :
      Filter.Tendsto (fun k : ℕ => Vη k ω) Filter.atTop (nhds (V ω)) := by
    apply hlimabs _ (fun k => ρ k * (1 + V ω)) (V ω)
    · simpa only [zero_mul] using hρlim.mul_const (1 + V ω)
    · exact fun k => (hspec k).2.2.1 ω
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hroot : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hnR
  have hrootpos : 0 < Real.sqrt (n : ℝ) := by linarith
  have hεone (k : ℕ) : 4 * ε k ≤ 1 := by
    have hprod : ε k * (4 * Real.sqrt (n : ℝ)) < 1 :=
      (lt_div_iff₀ (by positivity : 0 < 4 * Real.sqrt (n : ℝ))).1 (hεsmall k)
    nlinarith [mul_nonneg (hε k).le (sub_nonneg.mpr hroot)]
  have hηbound (k : ℕ) (i : Fin n) (ω : Ω) :
      |η k i ω| ≤ 2 * |ξ i ω| + 1 := by
    linarith [(hspec k).2.2.2.2.1 i ω, hεone k]
  have hdiffbound (k : ℕ) (i : Fin n) (ω : Ω) :
      |η k i ω - ξ i ω| ≤ 3 * |ξ i ω| + 1 := by
    have ht := abs_sub (η k i ω) (ξ i ω)
    linarith [hηbound k i ω]
  have hL1 (i : Fin n) : Filter.Tendsto
      (fun k : ℕ => ∫ ω, |η k i ω - ξ i ω| ∂ν) Filter.atTop (nhds (0 : ℝ)) := by
    have hdom : Integrable (fun ω => 3 * |ξ i ω| + 1) ν :=
      (((hξ2 i).integrable (by norm_num)).abs.const_mul 3).add (integrable_const 1)
    have hconv := tendsto_integral_of_dominated_convergence
      (μ := ν) (F := fun k ω => |η k i ω - ξ i ω|) (f := fun _ : Ω => (0 : ℝ))
      (fun ω => 3 * |ξ i ω| + 1)
      (fun k => (continuous_abs.measurable.comp
        (((hspec k).2.1 i).1.sub (hξ i))).aestronglyMeasurable)
      hdom
      (fun k => Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs, abs_abs] using hdiffbound k i ω)
      (Filter.Eventually.of_forall fun ω => by
        simpa only [sub_self, abs_zero] using
          ((hηpoint i ω).sub (tendsto_const_nhds (x := ξ i ω))).abs)
    simpa only [integral_zero] using hconv
  have hL2 (i : Fin n) : Filter.Tendsto
      (fun k : ℕ => ∫ ω, (η k i ω - ξ i ω) ^ 2 ∂ν) Filter.atTop (nhds (0 : ℝ)) := by
    have hdom : Integrable (fun ω => 18 * (ξ i ω) ^ 2 + 2) ν :=
      ((hξ2 i).integrable_sq.const_mul 18).add (integrable_const 2)
    have hsq (k : ℕ) (ω : Ω) :
        (η k i ω - ξ i ω) ^ 2 ≤ 18 * (ξ i ω) ^ 2 + 2 := by
      have hb := pow_le_pow_left₀ (abs_nonneg (η k i ω - ξ i ω))
        (hdiffbound k i ω) 2
      rw [sq_abs] at hb
      nlinarith [sq_nonneg (3 * |ξ i ω| - 1), sq_abs (ξ i ω)]
    have hconv := tendsto_integral_of_dominated_convergence
      (μ := ν) (F := fun k ω => (η k i ω - ξ i ω) ^ 2)
      (f := fun _ : Ω => (0 : ℝ)) (fun ω => 18 * (ξ i ω) ^ 2 + 2)
      (fun k => ((((hspec k).2.1 i).1.sub (hξ i)).pow_const 2).aestronglyMeasurable)
      hdom
      (fun k => Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs,
          abs_of_nonneg (sq_nonneg (η k i ω - ξ i ω))] using hsq k ω)
      (Filter.Eventually.of_forall fun ω => by
        simpa only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
          ((hηpoint i ω).sub (tendsto_const_nhds (x := ξ i ω))).pow 2)
    simpa only [integral_zero] using hconv
  exact ⟨(fun k => (hcs k).1), (fun k => ⟨(hcs k).2, (hspec k).1⟩),
    hμlim, hslim, hρlim, (fun k => (hspec k).2.1), hηbound, hηpoint,
    hWpoint, hVpoint, hL1, hL2⟩

theorem actual_projection_tilt_and_truncated_cost_limits
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (hξ2 : ∀ i : Fin n, MemLp (ξ i) 2 ν)
    (hξmean : ∀ i : Fin n, (∫ ω, ξ i ω ∂ν) = 0)
    (hξenergy : (∑ i : Fin n, ∫ ω, (ξ i ω) ^ 2 ∂ν) = 1)
    (Y : ℕ → Fin n → Ω → ℝ)
    (hY : ∀ (k : ℕ) (i : Fin n), Measurable (Y k i))
    (ε : ℕ → ℝ) (hε : ∀ k : ℕ, 0 < ε k)
    (hεsmall : ∀ k : ℕ, ε k < 1 / (4 * Real.sqrt (n : ℝ)))
    (hεlim : Filter.Tendsto ε Filter.atTop (nhds (0 : ℝ)))
    (herr : ∀ (k : ℕ) (i : Fin n) (ω : Ω), |Y k i ω - ξ i ω| ≤ ε k)
    (x : ℝ) :
    let η : ℕ → Fin n → Ω → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
    let ℓ : Fin n → Ω → ℝ := fun i ω => x * ξ i ω - (x * ξ i ω) ^ 2 / 2
    let ℓη : ℕ → Fin n → Ω → ℝ := fun k i ω => x * η k i ω - (x * η k i ω) ^ 2 / 2
    let S : Ω → ℝ := fun ω => ∑ i : Fin n, ℓ i ω
    let Sη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, ℓη k i ω
    let Sminus : Fin n → Ω → ℝ := fun i ω => ∑ j ∈ Finset.univ.erase i, ℓ j ω
    let Sηminus : ℕ → Fin n → Ω → ℝ := fun k i ω => ∑ j ∈ Finset.univ.erase i, ℓη k j ω
    let m : Fin n → ℝ := fun i => ∫ ω, Real.exp (ℓ i ω) ∂ν
    let mη : ℕ → Fin n → ℝ := fun k i => ∫ ω, Real.exp (ℓη k i ω) ∂ν
    let I : ℝ := ∫ ω, Real.exp (S ω) ∂ν
    let Iη : ℕ → ℝ := fun k => ∫ ω, Real.exp (Sη k ω) ∂ν
    let J : Fin n → ℝ := fun i => ∫ ω, Real.exp (Sminus i ω) ∂ν
    let Jη : ℕ → Fin n → ℝ := fun k i => ∫ ω, Real.exp (Sηminus k i ω) ∂ν
    let δ : Fin n → ℝ := fun i => ∫ ω, (x * ξ i ω) ^ 2 * min |x * ξ i ω| 1 ∂ν
    let δη : ℕ → Fin n → ℝ := fun k i => ∫ ω, (x * η k i ω) ^ 2 * min |x * η k i ω| 1 ∂ν
    let L : ℝ := ∑ i : Fin n, δ i
    let Lη : ℕ → ℝ := fun k => ∑ i : Fin n, δη k i
    let q : Ω → ℝ := fun ω => Real.exp (S ω) / I
    let qη : ℕ → Ω → ℝ := fun k ω => Real.exp (Sη k ω) / Iη k
    let qminus : Fin n → Ω → ℝ := fun i ω => Real.exp (Sminus i ω) / I
    let qηminus : ℕ → Fin n → Ω → ℝ := fun k i ω => Real.exp (Sηminus k i ω) / Iη k
    let pminus : Fin n → Ω → ℝ := fun i ω => Real.exp (Sminus i ω) / J i
    let pηminus : ℕ → Fin n → Ω → ℝ := fun k i ω => Real.exp (Sηminus k i ω) / Jη k i
    (∀ i : Fin n, Integrable (fun ω => Real.exp (ℓ i ω)) ν ∧ 0 < m i) ∧
    (∀ (k : ℕ) (i : Fin n), Integrable (fun ω => Real.exp (ℓη k i ω)) ν ∧ 0 < mη k i) ∧
    Integrable (fun ω => Real.exp (S ω)) ν ∧ 0 < I ∧
    (∀ k : ℕ, Integrable (fun ω => Real.exp (Sη k ω)) ν ∧ 0 < Iη k) ∧
    (∀ i : Fin n, Integrable (fun ω => Real.exp (Sminus i ω)) ν ∧ 0 < J i) ∧
    (∀ (k : ℕ) (i : Fin n), Integrable (fun ω => Real.exp (Sηminus k i ω)) ν ∧ 0 < Jη k i) ∧
    (∀ ω : Ω, Real.exp (S ω) ≤ Real.exp ((n : ℝ) / 2)) ∧
    (∀ (k : ℕ) (ω : Ω), Real.exp (Sη k ω) ≤ Real.exp ((n : ℝ) / 2)) ∧
    (∀ (i : Fin n) (ω : Ω), Real.exp (Sminus i ω) ≤ Real.exp (((n - 1 : ℕ) : ℝ) / 2)) ∧
    (∀ (k : ℕ) (i : Fin n) (ω : Ω), Real.exp (Sηminus k i ω) ≤ Real.exp (((n - 1 : ℕ) : ℝ) / 2)) ∧
    (∀ i : Fin n, Integrable (fun ω => (x * ξ i ω) ^ 2 * min |x * ξ i ω| 1) ν) ∧
    (∀ (k : ℕ) (i : Fin n), Integrable (fun ω => (x * η k i ω) ^ 2 * min |x * η k i ω| 1) ν) ∧
    (∀ (k : ℕ) (i : Fin n) (ω : Ω),
      |(x * η k i ω) ^ 2 * min |x * η k i ω| 1| ≤ x ^ 2 * (8 * (ξ i ω) ^ 2 + 2)) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => mη k i) Filter.atTop (nhds (m i))) ∧
    Filter.Tendsto Iη Filter.atTop (nhds I) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => Jη k i) Filter.atTop (nhds (J i))) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => δη k i) Filter.atTop (nhds (δ i))) ∧
    Filter.Tendsto Lη Filter.atTop (nhds L) ∧
    Integrable q ν ∧ (∫ ω, q ω ∂ν) = 1 ∧
    (∀ k : ℕ, Integrable (qη k) ν ∧ (∫ ω, qη k ω ∂ν) = 1) ∧
    (∀ i : Fin n, Integrable (qminus i) ν ∧ (∫ ω, qminus i ω ∂ν) = J i / I) ∧
    (∀ (k : ℕ) (i : Fin n), Integrable (qηminus k i) ν ∧ (∫ ω, qηminus k i ω ∂ν) = Jη k i / Iη k) ∧
    (∀ i : Fin n, Integrable (pminus i) ν ∧ (∫ ω, pminus i ω ∂ν) = 1) ∧
    (∀ (k : ℕ) (i : Fin n), Integrable (pηminus k i) ν ∧ (∫ ω, pηminus k i ω ∂ν) = 1) ∧
    (∀ (i : Fin n) (ω : Ω), qminus i ω = (J i / I) * pminus i ω) ∧
    (∀ (k : ℕ) (i : Fin n) (ω : Ω), qηminus k i ω = (Jη k i / Iη k) * pηminus k i ω) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => qη k ω) Filter.atTop (nhds (q ω))) ∧
    (∀ (i : Fin n) (ω : Ω), Filter.Tendsto (fun k : ℕ => qηminus k i ω) Filter.atTop (nhds (qminus i ω))) ∧
    (∀ (i : Fin n) (ω : Ω), Filter.Tendsto (fun k : ℕ => pηminus k i ω) Filter.atTop (nhds (pminus i ω))) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => Jη k i / Iη k) Filter.atTop (nhds (J i / I))) := by
  classical
  dsimp only
  let η : ℕ → Fin n → Ω → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
  let ℓ : Fin n → Ω → ℝ := fun i ω => x * ξ i ω - (x * ξ i ω) ^ 2 / 2
  let ℓη : ℕ → Fin n → Ω → ℝ := fun k i ω => x * η k i ω - (x * η k i ω) ^ 2 / 2
  let S : Ω → ℝ := fun ω => ∑ i : Fin n, ℓ i ω
  let Sη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, ℓη k i ω
  let Sminus : Fin n → Ω → ℝ := fun i ω => ∑ j ∈ Finset.univ.erase i, ℓ j ω
  let Sηminus : ℕ → Fin n → Ω → ℝ := fun k i ω => ∑ j ∈ Finset.univ.erase i, ℓη k j ω
  let m : Fin n → ℝ := fun i => ∫ ω, Real.exp (ℓ i ω) ∂ν
  let mη : ℕ → Fin n → ℝ := fun k i => ∫ ω, Real.exp (ℓη k i ω) ∂ν
  let I : ℝ := ∫ ω, Real.exp (S ω) ∂ν
  let Iη : ℕ → ℝ := fun k => ∫ ω, Real.exp (Sη k ω) ∂ν
  let J : Fin n → ℝ := fun i => ∫ ω, Real.exp (Sminus i ω) ∂ν
  let Jη : ℕ → Fin n → ℝ := fun k i => ∫ ω, Real.exp (Sηminus k i ω) ∂ν
  let δ : Fin n → ℝ := fun i => ∫ ω, (x * ξ i ω) ^ 2 * min |x * ξ i ω| 1 ∂ν
  let δη : ℕ → Fin n → ℝ := fun k i => ∫ ω, (x * η k i ω) ^ 2 * min |x * η k i ω| 1 ∂ν
  let L : ℝ := ∑ i : Fin n, δ i
  let Lη : ℕ → ℝ := fun k => ∑ i : Fin n, δη k i
  let q : Ω → ℝ := fun ω => Real.exp (S ω) / I
  let qη : ℕ → Ω → ℝ := fun k ω => Real.exp (Sη k ω) / Iη k
  let qminus : Fin n → Ω → ℝ := fun i ω => Real.exp (Sminus i ω) / I
  let qηminus : ℕ → Fin n → Ω → ℝ := fun k i ω => Real.exp (Sηminus k i ω) / Iη k
  let pminus : Fin n → Ω → ℝ := fun i ω => Real.exp (Sminus i ω) / J i
  let pηminus : ℕ → Fin n → Ω → ℝ := fun k i ω => Real.exp (Sηminus k i ω) / Jη k i
  have hnorm := actual_normalization_sequence_limits ν n hn ξ hξ hξ2 hξmean
    hξenergy Y hY ε hε hεsmall hεlim herr
  rcases hnorm with ⟨_, _, _, _, _, hηspec, hηbound, hηpoint, _, _, _, _⟩
  have hηm (k : ℕ) (i : Fin n) : Measurable (η k i) := (hηspec k i).1
  let T : (Fin n → Ω → ℝ) → Finset (Fin n) → Ω → ℝ :=
    fun f t ω => ∑ i ∈ t, (x * f i ω - (x * f i ω) ^ 2 / 2)
  have hTm (f : Fin n → Ω → ℝ) (hf : ∀ i : Fin n, Measurable (f i))
      (t : Finset (Fin n)) : Measurable (T f t) := by
    exact Finset.measurable_sum t (fun i _ =>
      (measurable_const.mul (hf i)).sub
        (((measurable_const.mul (hf i)).pow_const 2).div_const 2))
  have hTbound (f : Fin n → Ω → ℝ) (t : Finset (Fin n)) (ω : Ω) :
      Real.exp (T f t ω) ≤ Real.exp ((t.card : ℝ) / 2) := by
    apply Real.exp_le_exp.mpr
    calc
      T f t ω ≤ ∑ _i ∈ t, (1 / 2 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [sq_nonneg (x * f i ω - 1)]
      _ = (t.card : ℝ) / 2 := by simp [div_eq_mul_inv]
  have hTint (f : Fin n → Ω → ℝ) (hf : ∀ i : Fin n, Measurable (f i))
      (t : Finset (Fin n)) : Integrable (fun ω => Real.exp (T f t ω)) ν := by
    apply (integrable_const (Real.exp ((t.card : ℝ) / 2))).mono'
      (hTm f hf t).exp.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hTbound f t ω
  have hℓpoint (i : Fin n) (ω : Ω) : Filter.Tendsto
      (fun k : ℕ => ℓη k i ω) Filter.atTop (nhds (ℓ i ω)) := by
    have hu := (hηpoint i ω).const_mul x
    exact hu.sub ((hu.pow 2).div_const 2)
  have hTpoint (t : Finset (Fin n)) (ω : Ω) : Filter.Tendsto
      (fun k : ℕ => T (η k) t ω) Filter.atTop (nhds (T ξ t ω)) := by
    exact tendsto_finsetSum t (fun i _ => hℓpoint i ω)
  have hTlim (t : Finset (Fin n)) : Filter.Tendsto
      (fun k : ℕ => ∫ ω, Real.exp (T (η k) t ω) ∂ν)
      Filter.atTop (nhds (∫ ω, Real.exp (T ξ t ω) ∂ν)) := by
    exact tendsto_integral_of_dominated_convergence
      (μ := ν) (F := fun k ω => Real.exp (T (η k) t ω))
      (f := fun ω => Real.exp (T ξ t ω))
      (fun _ : Ω => Real.exp ((t.card : ℝ) / 2))
      (fun k => (hTm (η k) (hηm k) t).exp.aestronglyMeasurable)
      (integrable_const _)
      (fun k => Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hTbound (η k) t ω)
      (Filter.Eventually.of_forall fun ω =>
        Real.continuous_exp.continuousAt.tendsto.comp (hTpoint t ω))
  have hm (i : Fin n) : Integrable (fun ω => Real.exp (ℓ i ω)) ν ∧ 0 < m i := by
    have hi : Integrable (fun ω => Real.exp (ℓ i ω)) ν := by
      simpa only [T, Finset.sum_singleton] using hTint ξ hξ {i}
    exact ⟨hi, integral_exp_pos hi⟩
  have hmη (k : ℕ) (i : Fin n) :
      Integrable (fun ω => Real.exp (ℓη k i ω)) ν ∧ 0 < mη k i := by
    have hi : Integrable (fun ω => Real.exp (ℓη k i ω)) ν := by
      simpa only [T, Finset.sum_singleton] using hTint (η k) (hηm k) {i}
    exact ⟨hi, integral_exp_pos hi⟩
  have hSI : Integrable (fun ω => Real.exp (S ω)) ν := hTint ξ hξ Finset.univ
  have hIpos : 0 < I := integral_exp_pos hSI
  have hSIη (k : ℕ) : Integrable (fun ω => Real.exp (Sη k ω)) ν ∧ 0 < Iη k := by
    have hi : Integrable (fun ω => Real.exp (Sη k ω)) ν := hTint (η k) (hηm k) Finset.univ
    exact ⟨hi, integral_exp_pos hi⟩
  have hJI (i : Fin n) : Integrable (fun ω => Real.exp (Sminus i ω)) ν ∧ 0 < J i := by
    have hi : Integrable (fun ω => Real.exp (Sminus i ω)) ν :=
      hTint ξ hξ (Finset.univ.erase i)
    exact ⟨hi, integral_exp_pos hi⟩
  have hJIη (k : ℕ) (i : Fin n) :
      Integrable (fun ω => Real.exp (Sηminus k i ω)) ν ∧ 0 < Jη k i := by
    have hi : Integrable (fun ω => Real.exp (Sηminus k i ω)) ν :=
      hTint (η k) (hηm k) (Finset.univ.erase i)
    exact ⟨hi, integral_exp_pos hi⟩
  have hSB (ω : Ω) : Real.exp (S ω) ≤ Real.exp ((n : ℝ) / 2) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hTbound ξ Finset.univ ω
  have hSBη (k : ℕ) (ω : Ω) : Real.exp (Sη k ω) ≤ Real.exp ((n : ℝ) / 2) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hTbound (η k) Finset.univ ω
  have hJB (i : Fin n) (ω : Ω) :
      Real.exp (Sminus i ω) ≤ Real.exp (((n - 1 : ℕ) : ℝ) / 2) := by
    simpa using hTbound ξ (Finset.univ.erase i) ω
  have hJBη (k : ℕ) (i : Fin n) (ω : Ω) :
      Real.exp (Sηminus k i ω) ≤ Real.exp (((n - 1 : ℕ) : ℝ) / 2) := by
    simpa using hTbound (η k) (Finset.univ.erase i) ω
  have hmlim (i : Fin n) : Filter.Tendsto (fun k : ℕ => mη k i)
      Filter.atTop (nhds (m i)) := by
    simpa only [T, Finset.sum_singleton] using hTlim {i}
  have hIlim : Filter.Tendsto Iη Filter.atTop (nhds I) := hTlim Finset.univ
  have hJlim (i : Fin n) : Filter.Tendsto (fun k : ℕ => Jη k i)
      Filter.atTop (nhds (J i)) := hTlim (Finset.univ.erase i)
  let τ : ℝ → ℝ := fun u => u ^ 2 * min |u| 1
  have hτnonneg (u : ℝ) : 0 ≤ τ u :=
    mul_nonneg (sq_nonneg u) (le_min (abs_nonneg u) (by norm_num))
  have hτle (u : ℝ) : τ u ≤ u ^ 2 := by
    exact (mul_le_mul_of_nonneg_left (min_le_right |u| 1) (sq_nonneg u)).trans_eq (mul_one _)
  have hτm (f : Ω → ℝ) (hf : Measurable f) : Measurable (fun ω => τ (x * f ω)) := by
    have hu : Measurable (fun ω : Ω => x * f ω) := measurable_const.mul hf
    exact (hu.pow_const 2).mul
      ((continuous_abs.measurable.comp hu).min measurable_const)
  have hδdom (k : ℕ) (i : Fin n) (ω : Ω) :
      |τ (x * η k i ω)| ≤ x ^ 2 * (8 * (ξ i ω) ^ 2 + 2) := by
    rw [abs_of_nonneg (hτnonneg _)]
    have hb := pow_le_pow_left₀ (abs_nonneg (η k i ω)) (hηbound k i ω) 2
    rw [sq_abs] at hb
    have hs : (η k i ω) ^ 2 ≤ 8 * (ξ i ω) ^ 2 + 2 := by
      nlinarith [sq_nonneg (2 * |ξ i ω| - 1), sq_abs (ξ i ω)]
    calc
      τ (x * η k i ω) ≤ (x * η k i ω) ^ 2 := hτle _
      _ = x ^ 2 * (η k i ω) ^ 2 := mul_pow _ _ _
      _ ≤ x ^ 2 * (8 * (ξ i ω) ^ 2 + 2) := mul_le_mul_of_nonneg_left hs (sq_nonneg x)
  have hδdomI (i : Fin n) : Integrable (fun ω => x ^ 2 * (8 * (ξ i ω) ^ 2 + 2)) ν :=
    (((hξ2 i).integrable_sq.const_mul 8).add (integrable_const 2)).const_mul (x ^ 2)
  have hδI (i : Fin n) : Integrable (fun ω => τ (x * ξ i ω)) ν := by
    apply ((hξ2 i).integrable_sq.const_mul (x ^ 2)).mono' (hτm (ξ i) (hξ i)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hτnonneg _)]
      simpa only [mul_pow] using hτle (x * ξ i ω)
  have hδIη (k : ℕ) (i : Fin n) : Integrable (fun ω => τ (x * η k i ω)) ν := by
    apply (hδdomI i).mono' (hτm (η k i) (hηm k i)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using hδdom k i ω
  have hτcont : Continuous τ :=
    (continuous_id.pow 2).mul (continuous_abs.min continuous_const)
  have hδlim (i : Fin n) : Filter.Tendsto (fun k : ℕ => δη k i)
      Filter.atTop (nhds (δ i)) := by
    exact tendsto_integral_of_dominated_convergence
      (μ := ν) (F := fun k ω => τ (x * η k i ω)) (f := fun ω => τ (x * ξ i ω))
      (fun ω => x ^ 2 * (8 * (ξ i ω) ^ 2 + 2))
      (fun k => (hτm (η k i) (hηm k i)).aestronglyMeasurable)
      (hδdomI i)
      (fun k => Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs] using hδdom k i ω)
      (Filter.Eventually.of_forall fun ω =>
        hτcont.continuousAt.tendsto.comp ((hηpoint i ω).const_mul x))
  have hLlim : Filter.Tendsto Lη Filter.atTop (nhds L) :=
    tendsto_finsetSum Finset.univ (fun i _ => hδlim i)
  have hquot (f : Ω → ℝ) (hf : Integrable f ν) (a : ℝ) :
      Integrable (fun ω => f ω / a) ν ∧
      (∫ ω, f ω / a ∂ν) = (∫ ω, f ω ∂ν) / a := by
    refine ⟨hf.div_const a, ?_⟩
    simp only [div_eq_mul_inv, integral_mul_const]
  have hqI : Integrable q ν ∧ (∫ ω, q ω ∂ν) = 1 := by
    refine ⟨(hquot _ hSI I).1, ?_⟩
    exact (hquot _ hSI I).2.trans (div_self hIpos.ne')
  have hqIη (k : ℕ) : Integrable (qη k) ν ∧ (∫ ω, qη k ω ∂ν) = 1 := by
    refine ⟨(hquot _ (hSIη k).1 (Iη k)).1, ?_⟩
    exact (hquot _ (hSIη k).1 (Iη k)).2.trans (div_self (hSIη k).2.ne')
  have hqJI (i : Fin n) : Integrable (qminus i) ν ∧
      (∫ ω, qminus i ω ∂ν) = J i / I := hquot _ (hJI i).1 I
  have hqJIη (k : ℕ) (i : Fin n) : Integrable (qηminus k i) ν ∧
      (∫ ω, qηminus k i ω ∂ν) = Jη k i / Iη k := hquot _ (hJIη k i).1 (Iη k)
  have hpJI (i : Fin n) : Integrable (pminus i) ν ∧ (∫ ω, pminus i ω ∂ν) = 1 := by
    refine ⟨(hquot _ (hJI i).1 (J i)).1, ?_⟩
    exact (hquot _ (hJI i).1 (J i)).2.trans (div_self (hJI i).2.ne')
  have hpJIη (k : ℕ) (i : Fin n) :
      Integrable (pηminus k i) ν ∧ (∫ ω, pηminus k i ω ∂ν) = 1 := by
    refine ⟨(hquot _ (hJIη k i).1 (Jη k i)).1, ?_⟩
    exact (hquot _ (hJIη k i).1 (Jη k i)).2.trans (div_self (hJIη k i).2.ne')
  have hqfactor (i : Fin n) (ω : Ω) : qminus i ω = (J i / I) * pminus i ω := by
    dsimp only [qminus, pminus]
    field_simp [(hJI i).2.ne', hIpos.ne']
  have hqfactorη (k : ℕ) (i : Fin n) (ω : Ω) :
      qηminus k i ω = (Jη k i / Iη k) * pηminus k i ω := by
    dsimp only [qηminus, pηminus]
    field_simp [(hJIη k i).2.ne', (hSIη k).2.ne']
  have hqpoint (ω : Ω) : Filter.Tendsto (fun k : ℕ => qη k ω)
      Filter.atTop (nhds (q ω)) :=
    (Real.continuous_exp.continuousAt.tendsto.comp (hTpoint Finset.univ ω)).div hIlim hIpos.ne'
  have hqminuspoint (i : Fin n) (ω : Ω) : Filter.Tendsto (fun k : ℕ => qηminus k i ω)
      Filter.atTop (nhds (qminus i ω)) :=
    (Real.continuous_exp.continuousAt.tendsto.comp
      (hTpoint (Finset.univ.erase i) ω)).div hIlim hIpos.ne'
  have hpminuspoint (i : Fin n) (ω : Ω) : Filter.Tendsto (fun k : ℕ => pηminus k i ω)
      Filter.atTop (nhds (pminus i ω)) :=
    (Real.continuous_exp.continuousAt.tendsto.comp
      (hTpoint (Finset.univ.erase i) ω)).div (hJlim i) (hJI i).2.ne'
  have hratio (i : Fin n) : Filter.Tendsto (fun k : ℕ => Jη k i / Iη k)
      Filter.atTop (nhds (J i / I)) := (hJlim i).div hIlim hIpos.ne'
  exact ⟨hm, hmη, hSI, hIpos, hSIη, hJI, hJIη, hSB, hSBη, hJB, hJBη,
    hδI, hδIη, hδdom, hmlim, hIlim, hJlim, hδlim, hLlim,
    hqI.1, hqI.2, hqIη, hqJI, hqJIη, hpJI, hpJIη, hqfactor, hqfactorη,
    hqpoint, hqminuspoint, hpminuspoint, hratio⟩

theorem actual_normalized_remainder_analytic_cost_limits
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (hξ2 : ∀ i : Fin n, MemLp (ξ i) 2 ν)
    (hξmean : ∀ i : Fin n, (∫ ω, ξ i ω ∂ν) = 0)
    (hξenergy : (∑ i : Fin n, ∫ ω, (ξ i ω) ^ 2 ∂ν) = 1)
    (Y : ℕ → Fin n → Ω → ℝ)
    (hY : ∀ (k : ℕ) (i : Fin n), Measurable (Y k i))
    (ε : ℕ → ℝ) (hε : ∀ k : ℕ, 0 < ε k)
    (hεsmall : ∀ k : ℕ, ε k < 1 / (4 * Real.sqrt (n : ℝ)))
    (hεlim : Filter.Tendsto ε Filter.atTop (nhds (0 : ℝ)))
    (herr : ∀ (k : ℕ) (i : Fin n) (ω : Ω), |Y k i ω - ξ i ω| ≤ ε k)
    (A B : Ω → ℝ) (Adelete Bdelete : Fin n → Ω → ℝ)
    (hA : Measurable A) (hB : Measurable B)
    (hAdelete : ∀ i : Fin n, Measurable (Adelete i))
    (hBdelete : ∀ i : Fin n, Measurable (Bdelete i))
    (hAnonneg : ∀ ω : Ω, 0 ≤ A ω)
    (hBnonneg : ∀ ω : Ω, 0 ≤ B ω)
    (hAdeletenonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ Adelete i ω)
    (hBdeletenonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ Bdelete i ω)
    (hAint : Integrable A ν) (hBint : Integrable B ν)
    (hAdeleteint : ∀ i : Fin n, Integrable (Adelete i) ν)
    (hBdeleteint : ∀ i : Fin n, Integrable (Bdelete i) ν)
    (x : ℝ) (hx : 0 ≤ x) :
    let η : ℕ → Fin n → Ω → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
    let H : Ω → ℝ := fun ω => (1 + V ω) * (Real.sqrt (n : ℝ) + x * Real.sqrt (1 + B ω))
    let ρ : ℕ → ℝ := fun k => 4 * ε k * Real.sqrt (n : ℝ)
    let Aε : ℕ → Ω → ℝ := fun k ω => A ω + ρ k * H ω
    let ℓ : Fin n → Ω → ℝ := fun i ω => x * ξ i ω - (x * ξ i ω) ^ 2 / 2
    let ℓη : ℕ → Fin n → Ω → ℝ := fun k i ω => x * η k i ω - (x * η k i ω) ^ 2 / 2
    let S : Ω → ℝ := fun ω => ∑ i : Fin n, ℓ i ω
    let Sη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, ℓη k i ω
    let Sminus : Fin n → Ω → ℝ := fun i ω => ∑ j ∈ Finset.univ.erase i, ℓ j ω
    let Sηminus : ℕ → Fin n → Ω → ℝ := fun k i ω => ∑ j ∈ Finset.univ.erase i, ℓη k j ω
    let I : ℝ := ∫ ω, Real.exp (S ω) ∂ν
    let Iη : ℕ → ℝ := fun k => ∫ ω, Real.exp (Sη k ω) ∂ν
    let cap : Fin n → Ω → ℝ := fun i ω => min |x * ξ i ω| 1
    let capη : ℕ → Fin n → Ω → ℝ := fun k i ω => min |x * η k i ω| 1
    let compactCap : Fin n → Ω → ℝ := fun i ω => min |ξ i ω| (1 + x)⁻¹
    let compactCapη : ℕ → Fin n → Ω → ℝ := fun k i ω => min |η k i ω| (1 + x)⁻¹
    let fullTest : Ω → ℝ := fun ω => x * A ω + x ^ 2 * B ω
    let fullTestη : ℕ → Ω → ℝ := fun k ω => x * Aε k ω + x ^ 2 * B ω
    let deletedTest : Fin n → Ω → ℝ := fun i ω => cap i ω * (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)
    let deletedTestη : ℕ → Fin n → Ω → ℝ := fun k i ω => capη k i ω * (|Aε k ω - Adelete i ω| + x * |B ω - Bdelete i ω|)
    let compactDeletedTest : Fin n → Ω → ℝ := fun i ω => compactCap i ω * (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)
    let compactDeletedTestη : ℕ → Fin n → Ω → ℝ := fun k i ω => compactCapη k i ω * (|Aε k ω - Adelete i ω| + x * |B ω - Bdelete i ω|)
    let δcompact : Fin n → ℝ := fun i => ∫ ω, ((1 + x) * ξ i ω) ^ 2 * min |(1 + x) * ξ i ω| 1 ∂ν
    let δcompactη : ℕ → Fin n → ℝ := fun k i => ∫ ω, ((1 + x) * η k i ω) ^ 2 * min |(1 + x) * η k i ω| 1 ∂ν
    let Lcompact : ℝ := ∑ i : Fin n, δcompact i
    let Lcompactη : ℕ → ℝ := fun k => ∑ i : Fin n, δcompactη k i
    let sourceCost : ℝ := ((∫ ω, fullTest ω * Real.exp (S ω) ∂ν) + ∑ i : Fin n, ∫ ω, deletedTest i ω * Real.exp (Sminus i ω) ∂ν) / I
    let sourceCostη : ℕ → ℝ := fun k => ((∫ ω, fullTestη k ω * Real.exp (Sη k ω) ∂ν) + ∑ i : Fin n, ∫ ω, deletedTestη k i ω * Real.exp (Sηminus k i ω) ∂ν) / Iη k
    let compactCost : ℝ := Lcompact + (∫ ω, A ω ∂ν) + x * (∫ ω, B ω ∂ν) + ∑ i : Fin n, ∫ ω, compactDeletedTest i ω ∂ν
    let compactCostη : ℕ → ℝ := fun k => Lcompactη k + (∫ ω, Aε k ω ∂ν) + x * (∫ ω, B ω ∂ν) + ∑ i : Fin n, ∫ ω, compactDeletedTestη k i ω ∂ν
    Integrable H ν ∧
    (∀ k : ℕ, Integrable (Aε k) ν ∧ ∀ ω : Ω, 0 ≤ Aε k ω ∧ Aε k ω ≤ A ω + H ω) ∧
    Filter.Tendsto (fun k : ℕ => ∫ ω, |Aε k ω - A ω| ∂ν) Filter.atTop (nhds (0 : ℝ)) ∧
    Integrable (fun ω => fullTest ω * Real.exp (S ω)) ν ∧
    (∀ k : ℕ, Integrable (fun ω => fullTestη k ω * Real.exp (Sη k ω)) ν) ∧
    (∀ i : Fin n, Integrable (fun ω => deletedTest i ω * Real.exp (Sminus i ω)) ν) ∧
    (∀ (k : ℕ) (i : Fin n), Integrable (fun ω => deletedTestη k i ω * Real.exp (Sηminus k i ω)) ν) ∧
    (∀ i : Fin n, Integrable (compactDeletedTest i) ν) ∧
    (∀ (k : ℕ) (i : Fin n), Integrable (compactDeletedTestη k i) ν) ∧
    (∀ (k : ℕ) (ω : Ω),
      |fullTestη k ω * Real.exp (Sη k ω)| ≤
        Real.exp ((n : ℝ) / 2) * (x * (A ω + H ω) + x ^ 2 * B ω)) ∧
    (∀ (k : ℕ) (i : Fin n) (ω : Ω),
      |deletedTestη k i ω * Real.exp (Sηminus k i ω)| ≤
        Real.exp (((n - 1 : ℕ) : ℝ) / 2) * (|A ω - Adelete i ω| + H ω + x * |B ω - Bdelete i ω|)) ∧
    (∀ (k : ℕ) (i : Fin n) (ω : Ω),
      |compactDeletedTestη k i ω| ≤
        (1 + x)⁻¹ * (|A ω - Adelete i ω| + H ω + x * |B ω - Bdelete i ω|)) ∧
    Filter.Tendsto (fun k : ℕ => ∫ ω, fullTestη k ω * Real.exp (Sη k ω) ∂ν)
      Filter.atTop (nhds (∫ ω, fullTest ω * Real.exp (S ω) ∂ν)) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => ∫ ω, deletedTestη k i ω * Real.exp (Sηminus k i ω) ∂ν)
      Filter.atTop (nhds (∫ ω, deletedTest i ω * Real.exp (Sminus i ω) ∂ν))) ∧
    Filter.Tendsto (fun k : ℕ => (∫ ω, fullTestη k ω * Real.exp (Sη k ω) ∂ν) / Iη k)
      Filter.atTop (nhds ((∫ ω, fullTest ω * Real.exp (S ω) ∂ν) / I)) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => (∫ ω, deletedTestη k i ω * Real.exp (Sηminus k i ω) ∂ν) / Iη k)
      Filter.atTop (nhds ((∫ ω, deletedTest i ω * Real.exp (Sminus i ω) ∂ν) / I))) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => ∫ ω, compactDeletedTestη k i ω ∂ν)
      Filter.atTop (nhds (∫ ω, compactDeletedTest i ω ∂ν))) ∧
    Filter.Tendsto sourceCostη Filter.atTop (nhds sourceCost) ∧
    Filter.Tendsto compactCostη Filter.atTop (nhds compactCost) := by
  classical
  dsimp only
  let η : ℕ → Fin n → Ω → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
  let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
  let H : Ω → ℝ := fun ω => (1 + V ω) * (Real.sqrt (n : ℝ) + x * Real.sqrt (1 + B ω))
  let ρ : ℕ → ℝ := fun k => 4 * ε k * Real.sqrt (n : ℝ)
  let Aε : ℕ → Ω → ℝ := fun k ω => A ω + ρ k * H ω
  let ℓ : Fin n → Ω → ℝ := fun i ω => x * ξ i ω - (x * ξ i ω) ^ 2 / 2
  let ℓη : ℕ → Fin n → Ω → ℝ := fun k i ω => x * η k i ω - (x * η k i ω) ^ 2 / 2
  let S : Ω → ℝ := fun ω => ∑ i : Fin n, ℓ i ω
  let Sη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, ℓη k i ω
  let Sminus : Fin n → Ω → ℝ := fun i ω => ∑ j ∈ Finset.univ.erase i, ℓ j ω
  let Sηminus : ℕ → Fin n → Ω → ℝ := fun k i ω => ∑ j ∈ Finset.univ.erase i, ℓη k j ω
  let I : ℝ := ∫ ω, Real.exp (S ω) ∂ν
  let Iη : ℕ → ℝ := fun k => ∫ ω, Real.exp (Sη k ω) ∂ν
  let cap : Fin n → Ω → ℝ := fun i ω => min |x * ξ i ω| 1
  let capη : ℕ → Fin n → Ω → ℝ := fun k i ω => min |x * η k i ω| 1
  let compactCap : Fin n → Ω → ℝ := fun i ω => min |ξ i ω| (1 + x)⁻¹
  let compactCapη : ℕ → Fin n → Ω → ℝ := fun k i ω => min |η k i ω| (1 + x)⁻¹
  let fullTest : Ω → ℝ := fun ω => x * A ω + x ^ 2 * B ω
  let fullTestη : ℕ → Ω → ℝ := fun k ω => x * Aε k ω + x ^ 2 * B ω
  let deletedTest : Fin n → Ω → ℝ := fun i ω => cap i ω * (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)
  let deletedTestη : ℕ → Fin n → Ω → ℝ := fun k i ω => capη k i ω * (|Aε k ω - Adelete i ω| + x * |B ω - Bdelete i ω|)
  let compactDeletedTest : Fin n → Ω → ℝ := fun i ω => compactCap i ω * (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)
  let compactDeletedTestη : ℕ → Fin n → Ω → ℝ := fun k i ω => compactCapη k i ω * (|Aε k ω - Adelete i ω| + x * |B ω - Bdelete i ω|)
  let δcompact : Fin n → ℝ := fun i => ∫ ω, ((1 + x) * ξ i ω) ^ 2 * min |(1 + x) * ξ i ω| 1 ∂ν
  let δcompactη : ℕ → Fin n → ℝ := fun k i => ∫ ω, ((1 + x) * η k i ω) ^ 2 * min |(1 + x) * η k i ω| 1 ∂ν
  let Lcompact : ℝ := ∑ i : Fin n, δcompact i
  let Lcompactη : ℕ → ℝ := fun k => ∑ i : Fin n, δcompactη k i
  let sourceCost : ℝ := ((∫ ω, fullTest ω * Real.exp (S ω) ∂ν) + ∑ i : Fin n, ∫ ω, deletedTest i ω * Real.exp (Sminus i ω) ∂ν) / I
  let sourceCostη : ℕ → ℝ := fun k => ((∫ ω, fullTestη k ω * Real.exp (Sη k ω) ∂ν) + ∑ i : Fin n, ∫ ω, deletedTestη k i ω * Real.exp (Sηminus k i ω) ∂ν) / Iη k
  let compactCost : ℝ := Lcompact + (∫ ω, A ω ∂ν) + x * (∫ ω, B ω ∂ν) + ∑ i : Fin n, ∫ ω, compactDeletedTest i ω ∂ν
  let compactCostη : ℕ → ℝ := fun k => Lcompactη k + (∫ ω, Aε k ω ∂ν) + x * (∫ ω, B ω ∂ν) + ∑ i : Fin n, ∫ ω, compactDeletedTestη k i ω ∂ν
  have hnorm := actual_normalization_sequence_limits ν n hn ξ hξ hξ2 hξmean
    hξenergy Y hY ε hε hεsmall hεlim herr
  rcases hnorm with ⟨_, _, _, _, hρlim, hηspec, _, hηpoint, _, _, _, _⟩
  have hηm (k : ℕ) (i : Fin n) : Measurable (η k i) := (hηspec k i).1
  have hproj := actual_projection_tilt_and_truncated_cost_limits ν n hn ξ hξ hξ2
    hξmean hξenergy Y hY ε hε hεsmall hεlim herr x
  rcases hproj with
    ⟨_, _, _, hIpos, _, _, _, hSB, hSBη, hJB, hJBη, _, _, _, _, hIlim,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have henergy := Shao.OQ6.NormalizedRemainderEnvelope.actual_energy_envelope_integrability
    ν n hn ξ hξ hξ2 hξenergy B hB hBnonneg hBint
  rcases henergy with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hHspec, hHpos, _, _, _⟩
  have hHm : Measurable H := (hHspec x).1
  have hHint : Integrable H ν := (hHspec x).2
  have hHnonneg (ω : Ω) : 0 ≤ H ω := (hHpos x hx ω).le
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hrootpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hρbounds (k : ℕ) : 0 ≤ ρ k ∧ ρ k ≤ 1 := by
    have hprod : ε k * (4 * Real.sqrt (n : ℝ)) < 1 :=
      (lt_div_iff₀ (by positivity : 0 < 4 * Real.sqrt (n : ℝ))).1 (hεsmall k)
    dsimp only [ρ]
    constructor
    · exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (hε k).le)
        (Real.sqrt_nonneg (n : ℝ))
    · nlinarith
  have hAεm (k : ℕ) : Measurable (Aε k) := hA.add (measurable_const.mul hHm)
  have hAεI (k : ℕ) : Integrable (Aε k) ν := hAint.add (hHint.const_mul (ρ k))
  have hAεbounds (k : ℕ) (ω : Ω) : 0 ≤ Aε k ω ∧ Aε k ω ≤ A ω + H ω := by
    have hρH : 0 ≤ ρ k * H ω := mul_nonneg (hρbounds k).1 (hHnonneg ω)
    have hρle : ρ k * H ω ≤ H ω := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hρbounds k).2 (hHnonneg ω)
    change 0 ≤ A ω + ρ k * H ω ∧ A ω + ρ k * H ω ≤ A ω + H ω
    exact ⟨add_nonneg (hAnonneg ω) hρH, add_le_add (le_refl (A ω)) hρle⟩
  have hAεpoint (ω : Ω) : Filter.Tendsto (fun k : ℕ => Aε k ω)
      Filter.atTop (nhds (A ω)) := by
    simpa only [zero_mul, add_zero] using
      (tendsto_const_nhds (x := A ω)).add (hρlim.mul_const (H ω))
  have hAεerror (k : ℕ) :
      (∫ ω, |Aε k ω - A ω| ∂ν) = ρ k * (∫ ω, H ω ∂ν) := by
    calc
      (∫ ω, |Aε k ω - A ω| ∂ν) = ∫ ω, ρ k * H ω ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => by
          change |A ω + ρ k * H ω - A ω| = ρ k * H ω
          rw [add_sub_cancel_left, abs_of_nonneg (mul_nonneg (hρbounds k).1 (hHnonneg ω))]
      _ = ρ k * (∫ ω, H ω ∂ν) := integral_const_mul (ρ k) H
  have hAεL1 : Filter.Tendsto (fun k : ℕ => ∫ ω, |Aε k ω - A ω| ∂ν)
      Filter.atTop (nhds (0 : ℝ)) := by
    simp_rw [hAεerror]
    simpa only [zero_mul] using hρlim.mul_const (∫ ω, H ω ∂ν)
  have hAεElim : Filter.Tendsto (fun k : ℕ => ∫ ω, Aε k ω ∂ν)
      Filter.atTop (nhds (∫ ω, A ω ∂ν)) := by
    have he (k : ℕ) : (∫ ω, Aε k ω ∂ν) =
        (∫ ω, A ω ∂ν) + ρ k * (∫ ω, H ω ∂ν) := by
      rw [show Aε k = (fun ω => A ω + ρ k * H ω) from rfl,
        integral_add hAint (hHint.const_mul (ρ k)), integral_const_mul]
    simp_rw [he]
    simpa only [zero_mul, add_zero] using
      (tendsto_const_nhds (x := ∫ ω, A ω ∂ν)).add (hρlim.mul_const (∫ ω, H ω ∂ν))
  have hℓm (i : Fin n) : Measurable (ℓ i) :=
    (measurable_const.mul (hξ i)).sub
      (((measurable_const.mul (hξ i)).pow_const 2).div_const 2)
  have hℓηm (k : ℕ) (i : Fin n) : Measurable (ℓη k i) :=
    (measurable_const.mul (hηm k i)).sub
      (((measurable_const.mul (hηm k i)).pow_const 2).div_const 2)
  have hSm : Measurable S := Finset.measurable_sum Finset.univ (fun i _ => hℓm i)
  have hSηm (k : ℕ) : Measurable (Sη k) :=
    Finset.measurable_sum Finset.univ (fun i _ => hℓηm k i)
  have hJm (i : Fin n) : Measurable (Sminus i) :=
    Finset.measurable_sum (Finset.univ.erase i) (fun j _ => hℓm j)
  have hJηm (k : ℕ) (i : Fin n) : Measurable (Sηminus k i) :=
    Finset.measurable_sum (Finset.univ.erase i) (fun j _ => hℓηm k j)
  have hℓpoint (i : Fin n) (ω : Ω) : Filter.Tendsto
      (fun k : ℕ => ℓη k i ω) Filter.atTop (nhds (ℓ i ω)) := by
    have hu := (hηpoint i ω).const_mul x
    exact hu.sub ((hu.pow 2).div_const 2)
  have hSpoint (ω : Ω) : Filter.Tendsto (fun k : ℕ => Sη k ω)
      Filter.atTop (nhds (S ω)) := tendsto_finsetSum Finset.univ (fun i _ => hℓpoint i ω)
  have hJpoint (i : Fin n) (ω : Ω) : Filter.Tendsto (fun k : ℕ => Sηminus k i ω)
      Filter.atTop (nhds (Sminus i ω)) :=
    tendsto_finsetSum (Finset.univ.erase i) (fun j _ => hℓpoint j ω)
  have hcm (i : Fin n) : Measurable (cap i) :=
    (continuous_abs.measurable.comp
      (show Measurable (fun ω : Ω => x * ξ i ω) from measurable_const.mul (hξ i))).min measurable_const
  have hcηm (k : ℕ) (i : Fin n) : Measurable (capη k i) :=
    (continuous_abs.measurable.comp
      (show Measurable (fun ω : Ω => x * η k i ω) from measurable_const.mul (hηm k i))).min measurable_const
  have hccm (i : Fin n) : Measurable (compactCap i) :=
    (continuous_abs.measurable.comp (hξ i)).min measurable_const
  have hccηm (k : ℕ) (i : Fin n) : Measurable (compactCapη k i) :=
    (continuous_abs.measurable.comp (hηm k i)).min measurable_const
  have hcpoint (i : Fin n) (ω : Ω) : Filter.Tendsto (fun k : ℕ => capη k i ω)
      Filter.atTop (nhds (cap i ω)) := by
    have hc : Continuous (fun u : ℝ => min |u| 1) := continuous_abs.min continuous_const
    exact hc.continuousAt.tendsto.comp ((hηpoint i ω).const_mul x)
  have hccpoint (i : Fin n) (ω : Ω) : Filter.Tendsto (fun k : ℕ => compactCapη k i ω)
      Filter.atTop (nhds (compactCap i ω)) := by
    have hc : Continuous (fun u : ℝ => min |u| (1 + x)⁻¹) :=
      continuous_abs.min continuous_const
    exact hc.continuousAt.tendsto.comp (hηpoint i ω)
  let E : Fin n → Ω → ℝ := fun i ω => |A ω - Adelete i ω| + H ω + x * |B ω - Bdelete i ω|
  let G : Fin n → Ω → ℝ := fun i ω => |A ω - Adelete i ω| + x * |B ω - Bdelete i ω|
  let Gη : ℕ → Fin n → Ω → ℝ := fun k i ω => |Aε k ω - Adelete i ω| + x * |B ω - Bdelete i ω|
  let F : Ω → ℝ := fun ω => x * (A ω + H ω) + x ^ 2 * B ω
  have hEI (i : Fin n) : Integrable (E i) ν :=
    (((hAint.sub (hAdeleteint i)).abs.add hHint).add
      ((hBint.sub (hBdeleteint i)).abs.const_mul x))
  have hFI : Integrable F ν :=
    ((hAint.add hHint).const_mul x).add (hBint.const_mul (x ^ 2))
  have hGm (i : Fin n) : Measurable (G i) :=
    (continuous_abs.measurable.comp (hA.sub (hAdelete i))).add
      (measurable_const.mul (continuous_abs.measurable.comp (hB.sub (hBdelete i))))
  have hGηm (k : ℕ) (i : Fin n) : Measurable (Gη k i) :=
    (continuous_abs.measurable.comp ((hAεm k).sub (hAdelete i))).add
      (measurable_const.mul (continuous_abs.measurable.comp (hB.sub (hBdelete i))))
  have hGnonneg (i : Fin n) (ω : Ω) : 0 ≤ G i ω :=
    add_nonneg (abs_nonneg _) (mul_nonneg hx (abs_nonneg _))
  have hGηnonneg (k : ℕ) (i : Fin n) (ω : Ω) : 0 ≤ Gη k i ω :=
    add_nonneg (abs_nonneg _) (mul_nonneg hx (abs_nonneg _))
  have hEbound (i : Fin n) (ω : Ω) : G i ω ≤ E i ω := by
    dsimp only [G, E]
    linarith [hHnonneg ω]
  have hEηbound (k : ℕ) (i : Fin n) (ω : Ω) : Gη k i ω ≤ E i ω := by
    have hdiff : |Aε k ω - Adelete i ω| ≤ |A ω - Adelete i ω| + H ω := by
      calc
        |Aε k ω - Adelete i ω| = |(A ω - Adelete i ω) + ρ k * H ω| := by
          congr 1
          dsimp only [Aε]
          ring
        _ ≤ |A ω - Adelete i ω| + |ρ k * H ω| := abs_add_le _ _
        _ = |A ω - Adelete i ω| + ρ k * H ω := by
          rw [abs_of_nonneg (mul_nonneg (hρbounds k).1 (hHnonneg ω))]
        _ ≤ |A ω - Adelete i ω| + H ω := by
          exact add_le_add (le_refl |A ω - Adelete i ω|)
            (by simpa only [one_mul] using
              mul_le_mul_of_nonneg_right (hρbounds k).2 (hHnonneg ω))
    dsimp only [Gη, E]
    linarith
  have hGpoint (i : Fin n) (ω : Ω) : Filter.Tendsto (fun k : ℕ => Gη k i ω)
      Filter.atTop (nhds (G i ω)) :=
    ((hAεpoint ω).sub (tendsto_const_nhds (x := Adelete i ω))).abs.add
      (tendsto_const_nhds (x := x * |B ω - Bdelete i ω|))
  have hfullm : Measurable fullTest :=
    (measurable_const.mul hA).add (measurable_const.mul hB)
  have hfullηm (k : ℕ) : Measurable (fullTestη k) :=
    (measurable_const.mul (hAεm k)).add (measurable_const.mul hB)
  have hdm (i : Fin n) : Measurable (deletedTest i) := (hcm i).mul (hGm i)
  have hdηm (k : ℕ) (i : Fin n) : Measurable (deletedTestη k i) :=
    (hcηm k i).mul (hGηm k i)
  have hcdm (i : Fin n) : Measurable (compactDeletedTest i) := (hccm i).mul (hGm i)
  have hcdηm (k : ℕ) (i : Fin n) : Measurable (compactDeletedTestη k i) :=
    (hccηm k i).mul (hGηm k i)
  have hcapbounds (u c : ℝ) (hc : 0 ≤ c) : 0 ≤ min |u| c ∧ min |u| c ≤ c :=
    ⟨le_min (abs_nonneg u) hc, min_le_right _ _⟩
  have hweight (w g e c : ℝ) (hc : 0 ≤ c) (hw : 0 ≤ w ∧ w ≤ c)
      (hg : 0 ≤ g ∧ g ≤ e) : 0 ≤ w * g ∧ w * g ≤ c * e :=
    ⟨mul_nonneg hw.1 hg.1, mul_le_mul hw.2 hg.2 hg.1 hc⟩
  have hfullbounds (ω : Ω) : 0 ≤ fullTest ω ∧ fullTest ω ≤ F ω := by
    refine ⟨add_nonneg (mul_nonneg hx (hAnonneg ω))
      (mul_nonneg (sq_nonneg x) (hBnonneg ω)), ?_⟩
    change x * A ω + x ^ 2 * B ω ≤ x * (A ω + H ω) + x ^ 2 * B ω
    have hAle : A ω ≤ A ω + H ω := by linarith [hHnonneg ω]
    exact add_le_add (mul_le_mul_of_nonneg_left hAle hx) (le_refl (x ^ 2 * B ω))
  have hfullηbounds (k : ℕ) (ω : Ω) : 0 ≤ fullTestη k ω ∧ fullTestη k ω ≤ F ω := by
    refine ⟨add_nonneg (mul_nonneg hx (hAεbounds k ω).1)
      (mul_nonneg (sq_nonneg x) (hBnonneg ω)), ?_⟩
    change x * Aε k ω + x ^ 2 * B ω ≤ x * (A ω + H ω) + x ^ 2 * B ω
    exact add_le_add (mul_le_mul_of_nonneg_left (hAεbounds k ω).2 hx)
      (le_refl (x ^ 2 * B ω))
  have hdbounds (i : Fin n) (ω : Ω) : 0 ≤ deletedTest i ω ∧ deletedTest i ω ≤ E i ω := by
    simpa only [one_mul] using hweight (cap i ω) (G i ω) (E i ω) 1 (by norm_num)
      (hcapbounds _ _ (by norm_num)) ⟨hGnonneg i ω, hEbound i ω⟩
  have hdηbounds (k : ℕ) (i : Fin n) (ω : Ω) :
      0 ≤ deletedTestη k i ω ∧ deletedTestη k i ω ≤ E i ω := by
    simpa only [one_mul] using hweight (capη k i ω) (Gη k i ω) (E i ω) 1 (by norm_num)
      (hcapbounds _ _ (by norm_num)) ⟨hGηnonneg k i ω, hEηbound k i ω⟩
  have hcpos : 0 ≤ (1 + x)⁻¹ := inv_nonneg.mpr (by linarith)
  have hcdbounds (i : Fin n) (ω : Ω) :
      0 ≤ compactDeletedTest i ω ∧ compactDeletedTest i ω ≤ (1 + x)⁻¹ * E i ω :=
    hweight (compactCap i ω) (G i ω) (E i ω) (1 + x)⁻¹ hcpos
      (hcapbounds _ _ hcpos) ⟨hGnonneg i ω, hEbound i ω⟩
  have hcdηbounds (k : ℕ) (i : Fin n) (ω : Ω) :
      0 ≤ compactDeletedTestη k i ω ∧ compactDeletedTestη k i ω ≤ (1 + x)⁻¹ * E i ω :=
    hweight (compactCapη k i ω) (Gη k i ω) (E i ω) (1 + x)⁻¹ hcpos
      (hcapbounds _ _ hcpos) ⟨hGηnonneg k i ω, hEηbound k i ω⟩
  have hexpbound (f e d : Ω → ℝ) (C : ℝ)
      (hf : ∀ ω : Ω, 0 ≤ f ω ∧ f ω ≤ d ω)
      (he : ∀ ω : Ω, Real.exp (e ω) ≤ C) (ω : Ω) :
      |f ω * Real.exp (e ω)| ≤ C * d ω := by
    rw [abs_of_nonneg (mul_nonneg (hf ω).1 (Real.exp_pos _).le)]
    calc
      f ω * Real.exp (e ω) ≤ d ω * Real.exp (e ω) :=
        mul_le_mul_of_nonneg_right (hf ω).2 (Real.exp_pos _).le
      _ ≤ d ω * C := mul_le_mul_of_nonneg_left (he ω) ((hf ω).1.trans (hf ω).2)
      _ = C * d ω := mul_comm _ _
  have hfullbound := hexpbound fullTest S F (Real.exp ((n : ℝ) / 2)) hfullbounds hSB
  have hfullηbound (k : ℕ) :=
    hexpbound (fullTestη k) (Sη k) F (Real.exp ((n : ℝ) / 2)) (hfullηbounds k) (hSBη k)
  have hdbound (i : Fin n) := hexpbound (deletedTest i) (Sminus i) (E i)
    (Real.exp (((n - 1 : ℕ) : ℝ) / 2)) (hdbounds i) (hJB i)
  have hdηbound (k : ℕ) (i : Fin n) := hexpbound (deletedTestη k i) (Sηminus k i) (E i)
    (Real.exp (((n - 1 : ℕ) : ℝ) / 2)) (hdηbounds k i) (hJBη k i)
  have hcdηbound (k : ℕ) (i : Fin n) (ω : Ω) :
      |compactDeletedTestη k i ω| ≤ (1 + x)⁻¹ * E i ω := by
    rw [abs_of_nonneg (hcdηbounds k i ω).1]
    exact (hcdηbounds k i ω).2
  have hboundedI (f d : Ω → ℝ) (hf : Measurable f) (hd : Integrable d ν)
      (hb : ∀ ω : Ω, |f ω| ≤ d ω) : Integrable f ν := by
    apply hd.mono' hf.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using hb ω
  have hfullI : Integrable (fun ω => fullTest ω * Real.exp (S ω)) ν :=
    hboundedI _ _ (hfullm.mul hSm.exp) (hFI.const_mul _) hfullbound
  have hfullηI (k : ℕ) : Integrable (fun ω => fullTestη k ω * Real.exp (Sη k ω)) ν :=
    hboundedI _ _ ((hfullηm k).mul (hSηm k).exp) (hFI.const_mul _) (hfullηbound k)
  have hdI (i : Fin n) : Integrable (fun ω => deletedTest i ω * Real.exp (Sminus i ω)) ν :=
    hboundedI _ _ ((hdm i).mul (hJm i).exp) ((hEI i).const_mul _) (hdbound i)
  have hdηI (k : ℕ) (i : Fin n) :
      Integrable (fun ω => deletedTestη k i ω * Real.exp (Sηminus k i ω)) ν :=
    hboundedI _ _ ((hdηm k i).mul (hJηm k i).exp) ((hEI i).const_mul _) (hdηbound k i)
  have hcdI (i : Fin n) : Integrable (compactDeletedTest i) ν := by
    apply hboundedI _ _ (hcdm i) ((hEI i).const_mul ((1 + x)⁻¹))
    intro ω
    rw [abs_of_nonneg (hcdbounds i ω).1]
    exact (hcdbounds i ω).2
  have hcdηI (k : ℕ) (i : Fin n) : Integrable (compactDeletedTestη k i) ν :=
    hboundedI _ _ (hcdηm k i) ((hEI i).const_mul ((1 + x)⁻¹)) (hcdηbound k i)
  have hfullpoint (ω : Ω) : Filter.Tendsto
      (fun k : ℕ => fullTestη k ω * Real.exp (Sη k ω))
      Filter.atTop (nhds (fullTest ω * Real.exp (S ω))) :=
    (((hAεpoint ω).const_mul x).add (tendsto_const_nhds (x := x ^ 2 * B ω))).mul
      (Real.continuous_exp.continuousAt.tendsto.comp (hSpoint ω))
  have hdpoint (i : Fin n) (ω : Ω) : Filter.Tendsto
      (fun k : ℕ => deletedTestη k i ω * Real.exp (Sηminus k i ω))
      Filter.atTop (nhds (deletedTest i ω * Real.exp (Sminus i ω))) :=
    ((hcpoint i ω).mul (hGpoint i ω)).mul
      (Real.continuous_exp.continuousAt.tendsto.comp (hJpoint i ω))
  have hcdpoint (i : Fin n) (ω : Ω) : Filter.Tendsto
      (fun k : ℕ => compactDeletedTestη k i ω)
      Filter.atTop (nhds (compactDeletedTest i ω)) :=
    (hccpoint i ω).mul (hGpoint i ω)
  have hfullLim : Filter.Tendsto
      (fun k : ℕ => ∫ ω, fullTestη k ω * Real.exp (Sη k ω) ∂ν)
      Filter.atTop (nhds (∫ ω, fullTest ω * Real.exp (S ω) ∂ν)) :=
    tendsto_integral_of_dominated_convergence
      (μ := ν) (F := fun k ω => fullTestη k ω * Real.exp (Sη k ω))
      (f := fun ω => fullTest ω * Real.exp (S ω))
      (fun ω => Real.exp ((n : ℝ) / 2) * F ω)
      (fun k => ((hfullηm k).mul (hSηm k).exp).aestronglyMeasurable)
      (hFI.const_mul _)
      (fun k => Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs] using hfullηbound k ω)
      (Filter.Eventually.of_forall hfullpoint)
  have hdLim (i : Fin n) : Filter.Tendsto
      (fun k : ℕ => ∫ ω, deletedTestη k i ω * Real.exp (Sηminus k i ω) ∂ν)
      Filter.atTop (nhds (∫ ω, deletedTest i ω * Real.exp (Sminus i ω) ∂ν)) :=
    tendsto_integral_of_dominated_convergence
      (μ := ν) (F := fun k ω => deletedTestη k i ω * Real.exp (Sηminus k i ω))
      (f := fun ω => deletedTest i ω * Real.exp (Sminus i ω))
      (fun ω => Real.exp (((n - 1 : ℕ) : ℝ) / 2) * E i ω)
      (fun k => ((hdηm k i).mul (hJηm k i).exp).aestronglyMeasurable)
      ((hEI i).const_mul _)
      (fun k => Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs] using hdηbound k i ω)
      (Filter.Eventually.of_forall (hdpoint i))
  have hcdLim (i : Fin n) : Filter.Tendsto
      (fun k : ℕ => ∫ ω, compactDeletedTestη k i ω ∂ν)
      Filter.atTop (nhds (∫ ω, compactDeletedTest i ω ∂ν)) :=
    tendsto_integral_of_dominated_convergence
      (μ := ν) (F := fun k ω => compactDeletedTestη k i ω)
      (f := fun ω => compactDeletedTest i ω) (fun ω => (1 + x)⁻¹ * E i ω)
      (fun k => (hcdηm k i).aestronglyMeasurable)
      ((hEI i).const_mul _)
      (fun k => Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs] using hcdηbound k i ω)
      (Filter.Eventually.of_forall (hcdpoint i))
  have hfullRatio := hfullLim.div hIlim hIpos.ne'
  have hdRatio (i : Fin n) := (hdLim i).div hIlim hIpos.ne'
  have hsourceLim : Filter.Tendsto sourceCostη Filter.atTop (nhds sourceCost) :=
    (hfullLim.add (tendsto_finsetSum Finset.univ (fun i _ => hdLim i))).div hIlim hIpos.ne'
  have hcompactProj := actual_projection_tilt_and_truncated_cost_limits ν n hn ξ hξ hξ2
    hξmean hξenergy Y hY ε hε hεsmall hεlim herr (1 + x)
  rcases hcompactProj with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hLcompactLim,
      _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have hcompactLim : Filter.Tendsto compactCostη Filter.atTop (nhds compactCost) :=
    ((hLcompactLim.add hAεElim).add (tendsto_const_nhds (x := x * (∫ ω, B ω ∂ν)))).add
      (tendsto_finsetSum Finset.univ (fun i _ => hcdLim i))
  exact ⟨hHint, (fun k => ⟨hAεI k, hAεbounds k⟩), hAεL1,
    hfullI, hfullηI, hdI, hdηI, hcdI, hcdηI, hfullηbound, hdηbound,
    hcdηbound, hfullLim, hdLim, hfullRatio, hdRatio, hcdLim, hsourceLim, hcompactLim⟩

end

end Shao.OQ6.NormalizedAnalyticCostLimits
