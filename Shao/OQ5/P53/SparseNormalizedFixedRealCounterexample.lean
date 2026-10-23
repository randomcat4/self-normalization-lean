import Shao.OQ5.P53.SparseNormalizedRealOperator
import Shao.OQ5.P53.SparseNormalizedRealStatistics
import Shao.OQ5.P53.SparseSourceWindows

/-!
# One fixed normalized real iid counterexample and both source windows

Source p53 sections 1–5 and the scope01 variance-one convention. The actual
real law and iid coordinate process stay unchanged under the fixed positive
kernel scaling. All population, residual-operator, original centered-row
jackknife and actual-tail conclusions are exposed as literal conjuncts.
The feature exponential parameter is explicitly adjusted. No source moment,
independence, denominator or tail conclusion is assumed by the existence proof.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace Shao.OQ5.P53

def SparseNormalizedFixedRealPopulation (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : Prop :=
  let μ := sparseRealMeasure α x N
  let G := sparseNormalizedRealG α x N
  let Z := sparseNormalizedRealZ α x N
  let h := sparseNormalizedRealKernel α x N
  IsProbabilityMeasure μ ∧
  Measurable G ∧ Measurable Z ∧
  ProbabilityTheory.IndepFun G Z μ ∧
  μ.map (fun z => -G z) = μ.map G ∧
  μ.map (fun z => -Z z) = μ.map Z ∧
  (∫ z, G z ∂μ) = 0 ∧ (∫ z, Z z ∂μ) = 0 ∧
  (∫ z, (G z) ^ 2 ∂μ) = 1 ∧
  0 < (∫ z, (Z z) ^ 2 ∂μ) ∧
  (∀ q : ℝ, 0 < q →
    Integrable (fun z => |G z| ^ q) μ ∧
    Integrable (fun z => |Z z| ^ q) μ ∧
    Integrable (fun w : ℝ × ℝ => |h w.1 w.2| ^ q) (μ.prod μ)) ∧
  0 < sparseNormalizedRealExpParameter α x N ∧
  (∀ τ : ℝ, 0 < τ → τ ≤ sparseNormalizedRealExpParameter α x N →
    Integrable (fun z => Real.exp (τ * |Z z| ^ α)) μ ∧
    (∫ z, Real.exp (τ * |Z z| ^ α) ∂μ) ≤ (5 / 4 : ℝ)) ∧
  Measurable (fun w : ℝ × ℝ => h w.1 w.2) ∧
  (∀ u v : ℝ, h u v = h v u) ∧
  (∀ u v : ℝ, h u v = G u + G v + Z u * Z v) ∧
  (∀ u : ℝ, Integrable (h u) μ ∧ (∫ v, h u v ∂μ) = G u) ∧
  Integrable (fun w : ℝ × ℝ => h w.1 w.2) (μ.prod μ) ∧
  (∫ w : ℝ × ℝ, h w.1 w.2 ∂(μ.prod μ)) = 0

def SparseNormalizedFixedRealRankOne (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α) : Prop :=
  let μ := sparseRealMeasure α x N
  let G := sparseNormalizedRealG α x N
  let Z := sparseNormalizedRealZ α x N
  let h := sparseNormalizedRealKernel α x N
  let H := sparseNormalizedRealResidual α x N
  let A := sparseNormalizedRealResidualOperator α x N hα
  (∀ u v : ℝ, h u v - G u - G v = H u v ∧ H u v = Z u * Z v) ∧
  (∀ u : ℝ, Integrable (H u) μ ∧ (∫ v, H u v ∂μ) = 0) ∧
  (∀ f : Lp ℝ 2 μ,
    (A f : ℝ → ℝ) =ᵐ[μ] (fun u => ∫ v, H u v * f v ∂μ)) ∧
  IsSelfAdjoint A ∧
  (∀ f : Lp ℝ 2 μ, 0 ≤ inner ℝ f (A f)) ∧
  A.toLinearMap.rank = 1 ∧ A ≠ 0

def SparseNormalizedFixedRealIIDStatistic (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : Prop :=
  let μ := sparseRealMeasure α x N
  let ν := sparseRealSampleMeasure α x N
  let X := sparseRealSampleCoordinate
  IsProbabilityMeasure ν ∧
  (∀ i : ℕ, Measurable (X i)) ∧
  ProbabilityTheory.iIndepFun X ν ∧
  (∀ i : ℕ, ν.map (X i) = μ) ∧
  (∀ n : ℕ, ν.map (fun ξ (i : Fin n) => X i.val ξ) =
    Measure.pi (fun _ : Fin n => μ)) ∧
  (∀ (n : ℕ) (ξ : Fin n → ℝ), sparseNormalizedRealSampleU α x N ξ =
    Shao.OQ6.FiniteRows.uStatistic (fun i k => sparseNormalizedRealKernel α x N (ξ i) (ξ k))) ∧
  (∀ (n : ℕ) (ξ : Fin n → ℝ), sparseNormalizedRealSampleStudentizerSq α x N ξ =
    Shao.OQ6.FiniteRows.jackknifeSq (fun i k => sparseNormalizedRealKernel α x N (ξ i) (ξ k))) ∧
  (∀ (n : ℕ) (ξ : Fin n → ℝ), sparseNormalizedRealSampleStudentizer α x N ξ =
    Real.sqrt (sparseNormalizedRealSampleStudentizerSq α x N ξ)) ∧
  (∀ (n : ℕ) (ξ : Fin n → ℝ), sparseNormalizedRealSampleStudentized α x N ξ =
    Real.sqrt (n : ℝ) *
      (sparseNormalizedRealSampleU α x N ξ -
        ∫ w : ℝ × ℝ, sparseNormalizedRealKernel α x N w.1 w.2 ∂(μ.prod μ)) /
      sparseNormalizedRealSampleStudentizer α x N ξ) ∧
  (∀ n : ℕ, 3 ≤ n → ∀ᵐ ξ : ℕ → ℝ ∂ν,
    0 < sparseNormalizedRealSampleStudentizer α x N (fun i : Fin n => X i.val ξ))

def SparseNormalizedFixedRealCounterexample (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α) : Prop :=
  SparseSelectionCore α x N ∧
  N 0 = 1 ∧ StrictMono N ∧ Tendsto N atTop atTop ∧
  (∀ j : ℕ, 2 ^ j ≤ N j) ∧
  SparseNormalizedFixedRealPopulation α x N ∧
  SparseNormalizedFixedRealRankOne α x N hα ∧
  SparseNormalizedFixedRealIIDStatistic α x N ∧
  (∀ᶠ j : ℕ in atTop,
    0 < sparseNormalizedRealSampleStudentizedTailProbability α x N (N j) (x (N j))) ∧
  Tendsto (fun j : ℕ => Real.log (sparseNormalizedRealSampleStudentizedTailProbability α x N (N j) (x (N j))) /
    (-(x (N j) ^ 2) / 2)) atTop (nhds 0) ∧
  Tendsto (fun j : ℕ => sparseNormalizedRealSampleStudentizedTailProbability α x N (N j) (x (N j)) /
    Shao.OQ5.P35.standardNormalUpperTail (x (N j))) atTop atTop

theorem sparseNormalizedFixedRealPopulation_of_core :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → SparseSelectionCore α x N → SparseNormalizedFixedRealPopulation α x N := by
  intro α x N hα hN
  dsimp only [SparseNormalizedFixedRealPopulation]
  refine ⟨sparseRealMeasure_probability α x N,
    measurable_sparseNormalizedRealG α x N, measurable_sparseNormalizedRealZ α x N,
    sparseNormalizedRealG_indep_Z α x N,
    sparseNormalizedRealG_symmetric α x N, sparseNormalizedRealZ_symmetric α x N,
    integral_sparseNormalizedRealG_zero α x N hα hN,
    integral_sparseNormalizedRealZ_zero α x N hα hN,
    integral_sparseNormalizedRealG_sq_one α x N hα hN,
    integral_sparseNormalizedRealZ_sq_pos α x N hα hN,
    ?_, sparseNormalizedRealExpParameter_pos α x N hα hN, ?_,
    measurable_sparseNormalizedRealKernel α x N,
    sparseNormalizedRealKernel_symmetric α x N, ?_, ?_,
    integrable_sparseNormalizedRealKernel α x N hα hN,
    integral_sparseNormalizedRealKernel_zero α x N hα hN⟩
  · intro q hq
    exact ⟨integrable_sparseNormalizedRealG_rpow α x N hα hN q hq,
      integrable_sparseNormalizedRealZ_rpow α x N hα hN q hq,
      integrable_sparseNormalizedRealKernel_rpow α x N hα hN q hq⟩
  · intro τ hτ hτ0
    exact sparseNormalizedRealZ_exp_bound α x N hα hN τ hτ hτ0
  · intro u v
    exact sparseNormalizedRealKernel_decomposition α x N hα hN u v
  · intro u
    exact sparseNormalizedRealKernel_right_projection α x N hα hN u

theorem sparseNormalizedFixedRealRankOne_of_core :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α),
  SparseSelectionCore α x N → SparseNormalizedFixedRealRankOne α x N hα := by
  intro α x N hα hN
  dsimp only [SparseNormalizedFixedRealRankOne]
  refine ⟨?_, ?_, sparseNormalizedRealResidualOperator_apply_ae α x N hα,
    sparseNormalizedRealResidualOperator_isSelfAdjoint α x N hα,
    sparseNormalizedRealResidualOperator_positive α x N hα,
    sparseNormalizedRealResidualOperator_rank α x N hα hN,
    sparseNormalizedRealResidualOperator_ne_zero α x N hα hN⟩
  · intro u v
    exact sparseNormalizedRealResidual_decomposition α x N hα hN u v
  · intro u
    exact sparseNormalizedRealResidual_right_zero α x N hα hN u

theorem sparseNormalizedFixedRealIIDStatistic :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  SparseNormalizedFixedRealIIDStatistic α x N := by
  intro α x N hα hN
  dsimp only [SparseNormalizedFixedRealIIDStatistic]
  refine ⟨sparseRealSampleMeasure_probability α x N,
    measurable_sparseRealSampleCoordinate,
    iIndepFun_sparseRealSampleCoordinate α x N,
    sparseRealSampleCoordinate_law α x N,
    sparseRealSample_prefix_law α x N, ?_, ?_, ?_, ?_, ?_⟩
  · intro n ξ
    rfl
  · intro n ξ
    rfl
  · intro n ξ
    rfl
  · intro n ξ
    rfl
  · intro n hn
    exact sparseNormalizedRealSampleStudentizer_prefix_pos_ae α x N hα hN n hn

theorem sparseNormalizedFixedRealCounterexample_of_core :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α),
  α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  SparseNormalizedFixedRealCounterexample α x N hα := by
  intro α x N hα hα1 hN hSuper hSmall
  refine ⟨hN, hN.1, sparseSelectionCore_strictMono α x N hN,
    sparseSelectionCore_tendsto α x N hN, hN.2.1,
    sparseNormalizedFixedRealPopulation_of_core α x N hα hN,
    sparseNormalizedFixedRealRankOne_of_core α x N hα hN,
    sparseNormalizedFixedRealIIDStatistic α x N hα hN, ?_,
    tendsto_sparseNormalizedRealSampleStudentized_logTail_normalized_zero α x N hα hα1 hN hSuper hSmall,
    tendsto_sparseNormalizedRealSampleStudentized_gaussianTail_ratio_atTop α x N hα hα1 hN hSuper hSmall⟩
  simpa only [sparseNormalizedRealSampleStudentizedTailProbability_eq α x N hα hN] using
    eventually_sparseRealSampleStudentizedTailProbability_pos α x N hα hα1 hN hSuper hSmall

theorem exists_sparseNormalizedFixedRealCounterexample :
  ∀ (α : ℝ) (x : ℕ → ℝ) (hα : 0 < α), α < 1 →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  ∃ N : ℕ → ℕ, SparseNormalizedFixedRealCounterexample α x N hα := by
  intro α x hα hα1 hSuper hSmall
  obtain ⟨N, hN⟩ := exists_sparseSelectionCore α x hα hα1 hSuper hSmall
  exact ⟨N, sparseNormalizedFixedRealCounterexample_of_core α x N hα hα1 hN hSuper hSmall⟩

theorem exists_sparseNormalizedFixedRealCounterexample_relativeWindow :
  ∀ (p α : ℝ) (hα : 0 < α), 2 < p → p ≤ 3 → α < 2 * (p - 2) / (2 * p - 1) →
  ∃ N : ℕ → ℕ, SparseNormalizedFixedRealCounterexample α (sparseRelativeWindow p) N hα := by
  intro p α hα hp hp3 hcut
  obtain ⟨hα1, _hdelta⟩ := sparseDelta_lt_relativeWindowExponent p α hp hα hcut
  obtain ⟨hSuper, hSmall⟩ := sparseRelativeWindow_input_limits p α hp hp3 hα hcut
  exact exists_sparseNormalizedFixedRealCounterexample α (sparseRelativeWindow p) hα hα1 hSuper hSmall

theorem exists_sparseNormalizedFixedRealCounterexample_twoFifths :
  ∃ N : ℕ → ℕ, SparseNormalizedFixedRealCounterexample (2 / 5 : ℝ) sparseFifthPowerWindow N (by norm_num) := by
  obtain ⟨hSuper, hSmall⟩ := sparseFifthPowerWindow_input_limits
  exact exists_sparseNormalizedFixedRealCounterexample (2 / 5 : ℝ) sparseFifthPowerWindow
    (by norm_num) (by norm_num) hSuper hSmall

end Shao.OQ5.P53
