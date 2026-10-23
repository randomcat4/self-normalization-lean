import Shao.OQ5.P53.SparseBalancedTailLimits
import Shao.OQ5.P53.SparseRealOperator

/-!
# One fixed real iid counterexample for a given supercritical sequence

Source: current/oq56/inputs02/p53.md sections 1–4 and the two tail limits
in section 5. All population data use the same alpha, given sequence and
one recursively chosen subsequence. The data have no sample-size parameter.
The predicates expose the real law, moments, projection, residual integral
operator, iid process, original centered-row jackknife and actual tails.
Window examples and optional variance normalization remain separate.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace Shao.OQ5.P53

def SparseFixedRealPopulation (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : Prop :=
  let μ := sparseRealMeasure α x N
  let G := sparseRealG α x N
  let Z := sparseRealZ α x N
  let h := sparseRealKernel α x N
  IsProbabilityMeasure μ ∧
  Measurable G ∧ Measurable Z ∧
  ProbabilityTheory.IndepFun G Z μ ∧
  μ.map (fun z => -G z) = μ.map G ∧
  μ.map (fun z => -Z z) = μ.map Z ∧
  (∫ z, G z ∂μ) = 0 ∧ (∫ z, Z z ∂μ) = 0 ∧
  (1 / 3 : ℝ) ≤ (∫ z, (G z) ^ 2 ∂μ) ∧
  0 < (∫ z, (Z z) ^ 2 ∂μ) ∧
  (∀ q : ℝ, 0 < q →
    Integrable (fun z => |G z| ^ q) μ ∧
    Integrable (fun z => |Z z| ^ q) μ ∧
    Integrable (fun w : ℝ × ℝ => |h w.1 w.2| ^ q) (μ.prod μ)) ∧
  (∀ τ : ℝ, 0 < τ → τ ≤ 1 →
    Integrable (fun z => Real.exp (τ * |Z z| ^ α)) μ ∧
    (∫ z, Real.exp (τ * |Z z| ^ α) ∂μ) ≤ (5 / 4 : ℝ)) ∧
  Measurable (fun w : ℝ × ℝ => h w.1 w.2) ∧
  (∀ u v : ℝ, h u v = h v u) ∧
  (∀ u v : ℝ, h u v = G u + G v + Z u * Z v) ∧
  (∀ u : ℝ, Integrable (h u) μ ∧ (∫ v, h u v ∂μ) = G u) ∧
  Integrable (fun w : ℝ × ℝ => h w.1 w.2) (μ.prod μ) ∧
  (∫ w : ℝ × ℝ, h w.1 w.2 ∂(μ.prod μ)) = 0

def SparseFixedRealRankOne (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α) : Prop :=
  let μ := sparseRealMeasure α x N
  let G := sparseRealG α x N
  let Z := sparseRealZ α x N
  let h := sparseRealKernel α x N
  let H := sparseRealResidual α x N
  let A := sparseRealResidualOperator α x N hα
  (∀ u v : ℝ, h u v - G u - G v = H u v ∧ H u v = Z u * Z v) ∧
  (∀ u : ℝ, Integrable (H u) μ ∧ (∫ v, H u v ∂μ) = 0) ∧
  (∀ f : Lp ℝ 2 μ,
    (A f : ℝ → ℝ) =ᵐ[μ] (fun u => ∫ v, H u v * f v ∂μ)) ∧
  IsSelfAdjoint A ∧
  (∀ f : Lp ℝ 2 μ, 0 ≤ inner ℝ f (A f)) ∧
  A.toLinearMap.rank = 1 ∧ A ≠ 0

def SparseFixedRealIIDStatistic (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : Prop :=
  let μ := sparseRealMeasure α x N
  let ν := sparseRealSampleMeasure α x N
  let X := sparseRealSampleCoordinate
  IsProbabilityMeasure ν ∧
  (∀ i : ℕ, Measurable (X i)) ∧
  ProbabilityTheory.iIndepFun X ν ∧
  (∀ i : ℕ, ν.map (X i) = μ) ∧
  (∀ n : ℕ, ν.map (fun ξ (i : Fin n) => X i.val ξ) =
    Measure.pi (fun _ : Fin n => μ)) ∧
  (∀ (n : ℕ) (ξ : Fin n → ℝ), sparseRealSampleU α x N ξ =
    Shao.OQ6.FiniteRows.uStatistic (fun i k => sparseRealKernel α x N (ξ i) (ξ k))) ∧
  (∀ (n : ℕ) (ξ : Fin n → ℝ), sparseRealSampleStudentizerSq α x N ξ =
    Shao.OQ6.FiniteRows.jackknifeSq (fun i k => sparseRealKernel α x N (ξ i) (ξ k))) ∧
  (∀ (n : ℕ) (ξ : Fin n → ℝ), sparseRealSampleStudentizer α x N ξ =
    Real.sqrt (sparseRealSampleStudentizerSq α x N ξ)) ∧
  (∀ (n : ℕ) (ξ : Fin n → ℝ), sparseRealSampleStudentized α x N ξ =
    Real.sqrt (n : ℝ) * sparseRealSampleU α x N ξ / sparseRealSampleStudentizer α x N ξ) ∧
  (∀ n : ℕ, 3 ≤ n → ∀ᵐ ξ : ℕ → ℝ ∂ν,
    0 < sparseRealSampleStudentizer α x N (fun i : Fin n => X i.val ξ))

def SparseFixedRealCounterexample (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α) : Prop :=
  SparseSelectionCore α x N ∧
  N 0 = 1 ∧ StrictMono N ∧ Tendsto N atTop atTop ∧
  (∀ j : ℕ, 2 ^ j ≤ N j) ∧
  SparseFixedRealPopulation α x N ∧
  SparseFixedRealRankOne α x N hα ∧
  SparseFixedRealIIDStatistic α x N ∧
  (∀ᶠ j : ℕ in atTop,
    0 < sparseRealSampleStudentizedTailProbability α x N (N j) (x (N j))) ∧
  Tendsto (fun j : ℕ => Real.log (sparseRealSampleStudentizedTailProbability α x N (N j) (x (N j))) /
    (-(x (N j) ^ 2) / 2)) atTop (nhds 0) ∧
  Tendsto (fun j : ℕ => sparseRealSampleStudentizedTailProbability α x N (N j) (x (N j)) /
    Shao.OQ5.P35.standardNormalUpperTail (x (N j))) atTop atTop

theorem sparseFixedRealPopulation_of_core :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → SparseSelectionCore α x N → SparseFixedRealPopulation α x N := by
  intro α x N hα hN
  dsimp only [SparseFixedRealPopulation]
  refine ⟨sparseRealMeasure_probability α x N,
    measurable_sparseRealG α x N, measurable_sparseRealZ α x N,
    sparseRealG_indep_Z α x N,
    sparseRealG_symmetric α x N, sparseRealZ_symmetric α x N,
    integral_sparseRealG_zero α x N hα hN,
    integral_sparseRealZ_zero α x N hα,
    integral_sparseRealG_sq_ge α x N hα hN,
    integral_sparseRealZ_sq_pos α x N hα hN,
    ?_, ?_, measurable_sparseRealKernel α x N,
    sparseRealKernel_symmetric α x N, ?_, ?_,
    integrable_sparseRealKernel α x N hα hN,
    integral_sparseRealKernel_zero α x N hα hN⟩
  · intro q hq
    exact ⟨integrable_sparseRealG_rpow α x N hα hN q hq,
      integrable_sparseRealZ_rpow α x N hα q hq,
      integrable_sparseRealKernel_rpow α x N hα hN q hq⟩
  · intro τ hτ hτ1
    exact ⟨integrable_sparseRealZ_exp α x N hα τ hτ hτ1,
      integral_sparseRealZ_exp_le α x N hα τ hτ hτ1⟩
  · intro u v
    rfl
  · intro u
    exact ⟨integrable_sparseRealKernel_right α x N hα hN u,
      integral_sparseRealKernel_right α x N hα hN u⟩

theorem sparseFixedRealRankOne_of_core :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α),
  SparseSelectionCore α x N → SparseFixedRealRankOne α x N hα := by
  intro α x N hα hN
  dsimp only [SparseFixedRealRankOne]
  refine ⟨?_, ?_, sparseRealResidualOperator_apply_ae α x N hα,
    sparseRealResidualOperator_isSelfAdjoint α x N hα,
    sparseRealResidualOperator_positive α x N hα,
    sparseRealResidualOperator_rank α x N hα hN,
    sparseRealResidualOperator_ne_zero α x N hα hN⟩
  · intro u v
    exact ⟨sparseRealResidual_decomposition α x N u v, rfl⟩
  · intro u
    exact ⟨integrable_sparseRealResidual_right α x N hα u,
      integral_sparseRealResidual_right_zero α x N hα u⟩

theorem sparseFixedRealIIDStatistic :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), SparseFixedRealIIDStatistic α x N := by
  intro α x N
  dsimp only [SparseFixedRealIIDStatistic]
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
    exact sparseRealSampleStudentizer_prefix_pos_ae α x N n hn

theorem sparseFixedRealCounterexample_of_core :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α),
  α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  SparseFixedRealCounterexample α x N hα := by
  intro α x N hα hα1 hN hSuper hSmall
  exact ⟨hN, hN.1, sparseSelectionCore_strictMono α x N hN,
    sparseSelectionCore_tendsto α x N hN, hN.2.1,
    sparseFixedRealPopulation_of_core α x N hα hN,
    sparseFixedRealRankOne_of_core α x N hα hN,
    sparseFixedRealIIDStatistic α x N,
    eventually_sparseRealSampleStudentizedTailProbability_pos α x N hα hα1 hN hSuper hSmall,
    tendsto_sparseRealSampleStudentized_logTail_normalized_zero α x N hα hα1 hN hSuper hSmall,
    tendsto_sparseRealSampleStudentized_gaussianTail_ratio_atTop α x N hα hα1 hN hSuper hSmall⟩

theorem exists_sparseFixedRealCounterexample :
  ∀ (α : ℝ) (x : ℕ → ℝ) (hα : 0 < α), α < 1 →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  ∃ N : ℕ → ℕ, SparseFixedRealCounterexample α x N hα := by
  intro α x hα hα1 hSuper hSmall
  obtain ⟨N, hN⟩ := exists_sparseSelectionCore α x hα hα1 hSuper hSmall
  exact ⟨N, sparseFixedRealCounterexample_of_core α x N hα hα1 hN hSuper hSmall⟩

end Shao.OQ5.P53
