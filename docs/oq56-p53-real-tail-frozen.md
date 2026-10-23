# Exact P53 actual fixed-real-tail declarations

The three-module milestone has 18 public theorem types and 7 public definitions. These mathematical values and types were frozen before implementation. Unit126 adds one explicit cached Mathlib import in its preserved import-only repair; its mathematical declarations are unchanged. Verification receipts and independent reports are listed separately.

## Unit 124 — Shao.OQ5.P53.SparseBalancedTailLimits

Imports: `Shao.OQ5.P53.SparseBalancedConcentration`, `Shao.OQ5.P53.SparseBalancedEventCost`, `Shao.OQ5.P53.SparseRealStatistics`, `Shao.OQ5.P35.GaussianTail`.

```lean


theorem sparseSampleStudentizedTailProbability_eq_finite :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n : ℕ) (y : ℝ),
  sparseSampleStudentizedTailProbability α x N n y =
    (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N)).real
      {ω : Fin n → SparseObs | y ≤ sparseSampleStudentized α x N ω}

theorem eventually_sparseSampleStudentizedTailProbability_ge_balanced_half :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  ∀ᶠ j : ℕ in atTop,
    (sparsePopulationSampleMeasure α x N).real (sparseBalancedPrefixEvent (N j) j) / 2 ≤
      sparseSampleStudentizedTailProbability α x N (N j) (x (N j))

theorem eventually_sparseRealSampleStudentizedTailProbability_ge_balanced_half :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  ∀ᶠ j : ℕ in atTop,
    (sparsePopulationSampleMeasure α x N).real (sparseBalancedPrefixEvent (N j) j) / 2 ≤
      sparseRealSampleStudentizedTailProbability α x N (N j) (x (N j))

theorem eventually_sparseRealSampleStudentizedTailProbability_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  ∀ᶠ j : ℕ in atTop,
    0 < sparseRealSampleStudentizedTailProbability α x N (N j) (x (N j))

theorem tendsto_sparseRealSampleStudentized_logTail_cost_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  Tendsto (fun j : ℕ => Real.log (sparseRealSampleStudentizedTailProbability α x N (N j) (x (N j))) / x (N j) ^ 2)
    atTop (nhds 0)

theorem tendsto_sparseRealSampleStudentized_logTail_normalized_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  Tendsto (fun j : ℕ => Real.log (sparseRealSampleStudentizedTailProbability α x N (N j) (x (N j))) / (-(x (N j) ^ 2) / 2))
    atTop (nhds 0)

theorem tendsto_sparseRealSampleStudentized_gaussianTail_ratio_atTop :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  Tendsto (fun j : ℕ => sparseRealSampleStudentizedTailProbability α x N (N j) (x (N j)) /
    Shao.OQ5.P35.standardNormalUpperTail (x (N j))) atTop atTop
```

## Unit 125 — Shao.OQ5.P53.SparseFixedRealCounterexample

Imports: `Shao.OQ5.P53.SparseBalancedTailLimits`, `Shao.OQ5.P53.SparseRealOperator`.

```lean
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
  0 < α → SparseSelectionCore α x N → SparseFixedRealPopulation α x N

theorem sparseFixedRealRankOne_of_core :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α),
  SparseSelectionCore α x N → SparseFixedRealRankOne α x N hα

theorem sparseFixedRealIIDStatistic :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), SparseFixedRealIIDStatistic α x N

theorem sparseFixedRealCounterexample_of_core :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α),
  α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  SparseFixedRealCounterexample α x N hα

theorem exists_sparseFixedRealCounterexample :
  ∀ (α : ℝ) (x : ℕ → ℝ) (hα : 0 < α), α < 1 →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  ∃ N : ℕ → ℕ, SparseFixedRealCounterexample α x N hα
```

## Unit 126 — Shao.OQ5.P53.SparseSourceWindows

Imports: `Shao.OQ5.P53.SparseFixedRealCounterexample`, `Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics`.

```lean
def sparseRelativeWindowExponent (p : ℝ) : ℝ := (p - 2) / (2 * p)

def sparseRelativeWindow (p : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ sparseRelativeWindowExponent p / Real.log (n : ℝ)

def sparseFifthPowerWindow (n : ℕ) : ℝ := (n : ℝ) ^ (1 / 5 : ℝ)

theorem sparseRelativeWindowExponent_bounds :
  ∀ p : ℝ, 2 < p → 0 < sparseRelativeWindowExponent p ∧ sparseRelativeWindowExponent p < (1 / 2 : ℝ)

theorem sparseDelta_lt_relativeWindowExponent :
  ∀ (p α : ℝ), 2 < p → 0 < α → α < 2 * (p - 2) / (2 * p - 1) →
  α < 1 ∧ sparseDelta α < sparseRelativeWindowExponent p

theorem sparseRelativeWindow_input_limits :
  ∀ (p α : ℝ), 2 < p → p ≤ 3 → 0 < α → α < 2 * (p - 2) / (2 * p - 1) →
  Tendsto (fun n : ℕ => sparseRelativeWindow p n / (n : ℝ) ^ sparseDelta α) atTop atTop ∧
  Tendsto (fun n : ℕ => sparseRatio (sparseRelativeWindow p) n) atTop (nhds 0)

theorem exists_sparseFixedRealCounterexample_relativeWindow :
  ∀ (p α : ℝ) (hα : 0 < α), 2 < p → p ≤ 3 → α < 2 * (p - 2) / (2 * p - 1) →
  ∃ N : ℕ → ℕ, SparseFixedRealCounterexample α (sparseRelativeWindow p) N hα

theorem sparseFifthPowerWindow_input_limits :
  Tendsto (fun n : ℕ => sparseFifthPowerWindow n / (n : ℝ) ^ sparseDelta (2 / 5 : ℝ)) atTop atTop ∧
  Tendsto (fun n : ℕ => sparseRatio sparseFifthPowerWindow n) atTop (nhds 0)

theorem exists_sparseFixedRealCounterexample_twoFifths :
  ∃ N : ℕ → ℕ, SparseFixedRealCounterexample (2 / 5 : ℝ) sparseFifthPowerWindow N (by norm_num)
```
