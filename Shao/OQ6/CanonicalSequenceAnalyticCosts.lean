import Shao.OQ6.AmbientCanonicalCodingTransport
import Shao.OQ6.NormalizedAnalyticCostLimits
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Shao.OQ6.CanonicalSequenceAnalyticCosts

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology

theorem ambient_canonical_sequence_cost_limits_and_strict_budgets
    {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n) {X : Fin n → Type*}
    [mX : ∀ i : Fin n, MeasurableSpace (X i)]
    [∀ i : Fin n, MeasurableSpace.CountablyGenerated (X i)]
    (O : ∀ i : Fin n, A → X i)
    (hO : ∀ i : Fin n, Measurable (O i))
    (hOindep : iIndepFun O P)
    (g : ∀ i : Fin n, X i → ℝ)
    (hg : ∀ i : Fin n, Measurable (g i))
    (hg2 : ∀ i : Fin n, MemLp (fun ω : A => g i (O i ω)) 2 P)
    (hgmean : ∀ i : Fin n, (∫ ω, g i (O i ω) ∂P) = 0)
    (hgenergy : (∑ i : Fin n, ∫ ω, (g i (O i ω)) ^ 2 ∂P) = 1)
    (Aenv Benv : (∀ i : Fin n, X i) → ℝ)
    (Adeleted Bdeleted : ∀ i : Fin n, (∀ j : {j : Fin n // j ≠ i}, X j.1) → ℝ)
    (hAenv : Measurable Aenv) (hBenv : Measurable Benv)
    (hAdeleted : ∀ i : Fin n, Measurable (Adeleted i))
    (hBdeleted : ∀ i : Fin n, Measurable (Bdeleted i))
    (hAnonneg : ∀ o : (∀ i : Fin n, X i), 0 ≤ Aenv o)
    (hBnonneg : ∀ o : (∀ i : Fin n, X i), 0 ≤ Benv o)
    (hAdeletenonneg : ∀ (i : Fin n) (o : ∀ j : {j : Fin n // j ≠ i}, X j.1), 0 ≤ Adeleted i o)
    (hBdeletenonneg : ∀ (i : Fin n) (o : ∀ j : {j : Fin n // j ≠ i}, X j.1), 0 ≤ Bdeleted i o)
    (hAint : Integrable (fun ω : A => Aenv (fun i => O i ω)) P)
    (hBint : Integrable (fun ω : A => Benv (fun i => O i ω)) P)
    (hAdeleteint : ∀ i : Fin n, Integrable (fun ω : A => Adeleted i (fun j => O j.1 ω)) P)
    (hBdeleteint : ∀ i : Fin n, Integrable (fun ω : A => Bdeleted i (fun j => O j.1 ω)) P)
    (x : ℝ) (hx : 0 ≤ x) :
    let μ : ∀ i : Fin n, Measure (X i) := fun i => P.map (O i)
    let μ0 : Measure (∀ i : Fin n, X i) := Measure.pi μ
    let Q : A → (∀ i : Fin n, X i) := fun ω i => O i ω
    let lambda01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
    let νlocal : ∀ i : Fin n, Measure (X i × ℝ) := fun i => (μ i).prod lambda01
    let ν : Measure (∀ i : Fin n, X i × ℝ) := Measure.pi νlocal
    let q : (∀ i : Fin n, X i × ℝ) → (∀ i : Fin n, X i) := fun y i => (y i).1
    let ε : ℕ → ℝ := fun k => 1 / (8 * Real.sqrt (n : ℝ) * ((k : ℝ) + 1))
    let c : ∀ i : Fin n, (X i × ℝ) → ℝ := fun i => Shao.OQ6.ScalarObservationCoding.baseFourIndicatorCode (MeasurableSpace.natGeneratingSequence (X i × ℝ))
    let ξlocal : ∀ i : Fin n, (X i × ℝ) → ℝ := fun i z => g i z.1
    let Ylocal : ℕ → ∀ i : Fin n, (X i × ℝ) → ℝ := fun k i => Shao.OQ6.QuantizedObservationCoding.quantizedObservation (ε k) (ξlocal i) (c i)
    let ξ0 : Fin n → A → ℝ := fun i ω => g i (O i ω)
    let ξ : Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun i y => g i (y i).1
    let Y : ℕ → Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun k i y => Ylocal k i (y i)
    let a : ℕ → Fin n → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν (Y k)
    let s : ℕ → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν (Y k)
    let ηlocal : ℕ → ∀ i : Fin n, (X i × ℝ) → ℝ := fun k i => Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation (a k i) (s k) (Ylocal k i)
    let η : ℕ → Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
    let C : ℕ → (∀ i : Fin n, X i × ℝ) → (Fin n → ℝ) := fun k y i => η k i y
    let V0 : A → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ0 i ω) ^ 2)
    let V : (∀ i : Fin n, X i × ℝ) → ℝ := fun y => Real.sqrt (∑ i : Fin n, (ξ i y) ^ 2)
    let Vη : ℕ → (∀ i : Fin n, X i × ℝ) → ℝ := fun k y => Real.sqrt (∑ i : Fin n, (η k i y) ^ 2)
    let Z0 : Set A := {ω : A | V0 ω = 0}
    let Z : Set (∀ i : Fin n, X i × ℝ) := {y : (∀ i : Fin n, X i × ℝ) | V y = 0}
    let p0 : ℝ := P.real Z0
    let Aν : (∀ i : Fin n, X i × ℝ) → ℝ := fun y => Aenv (q y)
    let Bν : (∀ i : Fin n, X i × ℝ) → ℝ := fun y => Benv (q y)
    let Aνdelete : Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun i y => Adeleted i (fun j => (y j.1).1)
    let Bνdelete : Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun i y => Bdeleted i (fun j => (y j.1).1)
    let H : (∀ i : Fin n, X i × ℝ) → ℝ := fun y => (1 + V y) * (Real.sqrt (n : ℝ) + x * Real.sqrt (1 + Bν y))
    let ρ : ℕ → ℝ := fun k => 4 * ε k * Real.sqrt (n : ℝ)
    let Aε : ℕ → (∀ i : Fin n, X i × ℝ) → ℝ := fun k y => Aν y + ρ k * H y
    let ℓ0 : Fin n → A → ℝ := fun i ω => x * ξ0 i ω - (x * ξ0 i ω) ^ 2 / 2
    let ℓη : ℕ → Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun k i y => x * η k i y - (x * η k i y) ^ 2 / 2
    let S0 : A → ℝ := fun ω => ∑ i : Fin n, ℓ0 i ω
    let Sη : ℕ → (∀ i : Fin n, X i × ℝ) → ℝ := fun k y => ∑ i : Fin n, ℓη k i y
    let S0minus : Fin n → A → ℝ := fun i ω => ∑ j ∈ Finset.univ.erase i, ℓ0 j ω
    let Sηminus : ℕ → Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun k i y => ∑ j ∈ Finset.univ.erase i, ℓη k j y
    let I0 : ℝ := ∫ ω, Real.exp (S0 ω) ∂P
    let Iη : ℕ → ℝ := fun k => ∫ y, Real.exp (Sη k y) ∂ν
    let J0 : Fin n → ℝ := fun i => ∫ ω, Real.exp (S0minus i ω) ∂P
    let Jη : ℕ → Fin n → ℝ := fun k i => ∫ y, Real.exp (Sηminus k i y) ∂ν
    let δ0 : Fin n → ℝ := fun i => ∫ ω, (x * ξ0 i ω) ^ 2 * min |x * ξ0 i ω| 1 ∂P
    let δη : ℕ → Fin n → ℝ := fun k i => ∫ y, (x * η k i y) ^ 2 * min |x * η k i y| 1 ∂ν
    let L0 : ℝ := ∑ i : Fin n, δ0 i
    let Lη : ℕ → ℝ := fun k => ∑ i : Fin n, δη k i
    let fullTest0 : A → ℝ := fun ω => x * Aenv (Q ω) + x ^ 2 * Benv (Q ω)
    let fullTestη : ℕ → (∀ i : Fin n, X i × ℝ) → ℝ := fun k y => x * Aε k y + x ^ 2 * Bν y
    let deletedTest0 : Fin n → A → ℝ := fun i ω => min |x * ξ0 i ω| 1 * (|Aenv (Q ω) - Adeleted i (fun j => O j.1 ω)| + x * |Benv (Q ω) - Bdeleted i (fun j => O j.1 ω)|)
    let deletedTestη : ℕ → Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun k i y => min |x * η k i y| 1 * (|Aε k y - Aνdelete i y| + x * |Bν y - Bνdelete i y|)
    let compactDeletedTest0 : Fin n → A → ℝ := fun i ω => min |ξ0 i ω| (1 + x)⁻¹ * (|Aenv (Q ω) - Adeleted i (fun j => O j.1 ω)| + x * |Benv (Q ω) - Bdeleted i (fun j => O j.1 ω)|)
    let compactDeletedTestη : ℕ → Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun k i y => min |η k i y| (1 + x)⁻¹ * (|Aε k y - Aνdelete i y| + x * |Bν y - Bνdelete i y|)
    let Lcompact0 : ℝ := ∑ i : Fin n, ∫ ω, ((1 + x) * ξ0 i ω) ^ 2 * min |(1 + x) * ξ0 i ω| 1 ∂P
    let Lcompactη : ℕ → ℝ := fun k => ∑ i : Fin n, ∫ y, ((1 + x) * η k i y) ^ 2 * min |(1 + x) * η k i y| 1 ∂ν
    let sourceCost0 : ℝ := ((∫ ω, fullTest0 ω * Real.exp (S0 ω) ∂P) + ∑ i : Fin n, ∫ ω, deletedTest0 i ω * Real.exp (S0minus i ω) ∂P) / I0
    let sourceCostη : ℕ → ℝ := fun k => ((∫ y, fullTestη k y * Real.exp (Sη k y) ∂ν) + ∑ i : Fin n, ∫ y, deletedTestη k i y * Real.exp (Sηminus k i y) ∂ν) / Iη k
    let compactCost0 : ℝ := Lcompact0 + (∫ ω, Aenv (Q ω) ∂P) + x * (∫ ω, Benv (Q ω) ∂P) + ∑ i : Fin n, ∫ ω, compactDeletedTest0 i ω ∂P
    let compactCostη : ℕ → ℝ := fun k => Lcompactη k + (∫ y, Aε k y ∂ν) + x * (∫ y, Bν y ∂ν) + ∑ i : Fin n, ∫ y, compactDeletedTestη k i y ∂ν
    (∀ k : ℕ, 0 < ε k ∧ ε k < 1 / (4 * Real.sqrt (n : ℝ))) ∧
    Filter.Tendsto ε Filter.atTop (nhds (0 : ℝ)) ∧
    IsProbabilityMeasure ν ∧ MeasurePreserving Q P μ0 ∧ MeasurePreserving q ν μ0 ∧
    MeasurableSet Z0 ∧ MeasurableSet Z ∧ ν Z = P Z0 ∧ ν.real Z = p0 ∧
    (∀ (k : ℕ) (i : Fin n), Measurable (Y k i) ∧ MemLp (Y k i) 2 ν) ∧
    (∀ (k : ℕ) (i : Fin n) (y : ∀ j : Fin n, X j × ℝ), |Y k i y - ξ i y| ≤ ε k) ∧
    (∀ (k : ℕ) (i : Fin n), |a k i| ≤ ε k) ∧
    (∀ k : ℕ, |s k - 1| ≤ 2 * ε k * Real.sqrt (n : ℝ) ∧ (1 / 2 : ℝ) < s k) ∧
    (∀ (k : ℕ) (i : Fin n) (y : ∀ j : Fin n, X j × ℝ), η k i y = ηlocal k i (y i)) ∧
    (∀ (k : ℕ) (i : Fin n), Measurable (η k i) ∧ MemLp (η k i) 2 ν) ∧
    (∀ k : ℕ, iIndepFun (η k) ν ∧ (∀ i : Fin n, (∫ y, η k i y ∂ν) = 0) ∧ (∑ i : Fin n, ∫ y, (η k i y) ^ 2 ∂ν) = 1) ∧
    (∀ (k : ℕ) (i : Fin n) (t : ℝ), ν ({y : (∀ j : Fin n, X j × ℝ) | η k i y = t}) = 0) ∧
    (∀ k : ℕ, ν ({y : (∀ i : Fin n, X i × ℝ) | Vη k y = 0}) = 0) ∧
    (∀ k : ℕ, Measurable[(inferInstance : MeasurableSpace (∀ i : Fin n, X i × ℝ)), borel (Fin n → ℝ)] (C k) ∧ MeasurableSpace.comap (C k) (borel (Fin n → ℝ)) = (inferInstance : MeasurableSpace (∀ i : Fin n, X i × ℝ))) ∧
    (∀ (k : ℕ) (h : (∀ i : Fin n, X i × ℝ) → ℝ), Measurable h →
      ∃ F : (Fin n → ℝ) → ℝ, Measurable[borel (Fin n → ℝ), borel ℝ] F ∧ ∀ y : (∀ i : Fin n, X i × ℝ), h y = F (C k y)) ∧
    (∀ (k : ℕ) (i : Fin n) (d : (∀ j : {j : Fin n // j ≠ i}, X j.1 × ℝ) → ℝ), Measurable d →
      ∃ F : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] F ∧
        (∀ u : (∀ j : {j : Fin n // j ≠ i}, X j.1 × ℝ), d u = F (fun j => ηlocal k j.1 (u j))) ∧
        Measurable[borel (Fin n → ℝ), borel ℝ] (fun v : Fin n → ℝ => F (fun j => v j.1)) ∧
        ∀ y : (∀ j : Fin n, X j × ℝ), d (fun j => y j.1) = F (fun j => η k j.1 y)) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => a k i) Filter.atTop (nhds (0 : ℝ))) ∧
    Filter.Tendsto s Filter.atTop (nhds (1 : ℝ)) ∧
    Filter.Tendsto ρ Filter.atTop (nhds (0 : ℝ)) ∧
    (∀ (i : Fin n) (y : ∀ j : Fin n, X j × ℝ), Filter.Tendsto (fun k : ℕ => η k i y) Filter.atTop (nhds (ξ i y))) ∧
    (∀ y : (∀ i : Fin n, X i × ℝ), Filter.Tendsto (fun k : ℕ => Vη k y) Filter.atTop (nhds (V y))) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => ∫ y, |η k i y - ξ i y| ∂ν) Filter.atTop (nhds (0 : ℝ))) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => ∫ y, (η k i y - ξ i y) ^ 2 ∂ν) Filter.atTop (nhds (0 : ℝ))) ∧
    Measurable H ∧ Integrable H ν ∧
    (∀ k : ℕ, Measurable (Aε k) ∧ Integrable (Aε k) ν ∧ ∀ y : (∀ i : Fin n, X i × ℝ), 0 ≤ Aε k y ∧ Aε k y ≤ Aν y + H y) ∧
    Filter.Tendsto (fun k : ℕ => ∫ y, |Aε k y - Aν y| ∂ν) Filter.atTop (nhds (0 : ℝ)) ∧
    Integrable (fun ω => Real.exp (S0 ω)) P ∧ 0 < I0 ∧
    (∀ k : ℕ, Integrable (fun y => Real.exp (Sη k y)) ν ∧ 0 < Iη k) ∧
    (∀ i : Fin n, Integrable (fun ω => Real.exp (S0minus i ω)) P ∧ 0 < J0 i) ∧
    (∀ (k : ℕ) (i : Fin n), Integrable (fun y => Real.exp (Sηminus k i y)) ν ∧ 0 < Jη k i) ∧
    (∀ (k : ℕ) (i : Fin n), (∫ y, Real.exp (Sηminus k i y) / Iη k ∂ν) = Jη k i / Iη k) ∧
    Integrable (fun ω => fullTest0 ω * Real.exp (S0 ω)) P ∧
    (∀ i : Fin n, Integrable (fun ω => deletedTest0 i ω * Real.exp (S0minus i ω)) P ∧ Integrable (compactDeletedTest0 i) P) ∧
    (∀ k : ℕ, Integrable (fun y => fullTestη k y * Real.exp (Sη k y)) ν) ∧
    (∀ (k : ℕ) (i : Fin n), Integrable (fun y => deletedTestη k i y * Real.exp (Sηminus k i y)) ν ∧ Integrable (compactDeletedTestη k i) ν) ∧
    Filter.Tendsto Iη Filter.atTop (nhds I0) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => Jη k i) Filter.atTop (nhds (J0 i))) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => δη k i) Filter.atTop (nhds (δ0 i))) ∧
    Filter.Tendsto Lη Filter.atTop (nhds L0) ∧
    Filter.Tendsto Lcompactη Filter.atTop (nhds Lcompact0) ∧
    Filter.Tendsto sourceCostη Filter.atTop (nhds sourceCost0) ∧
    Filter.Tendsto compactCostη Filter.atTop (nhds compactCost0) ∧
    (∀ (d l r b : ℝ), (∀ i : Fin n, δ0 i < d) → L0 < l → sourceCost0 < r → compactCost0 < b →
      ∀ᶠ k : ℕ in Filter.atTop, (∀ i : Fin n, δη k i < d) ∧ Lη k < l ∧ sourceCostη k < r ∧ compactCostη k < b) ∧
    (∀ cSZ : ℝ, 0 < cSZ → 1 ≤ x → (∀ i : Fin n, δ0 i ≤ (1 / 2 : ℝ)) → L0 ≤ (cSZ / 2) * x ^ 2 →
      ∀ᶠ k : ℕ in Filter.atTop, (∀ i : Fin n, δη k i ≤ 1) ∧ Lη k ≤ cSZ * x ^ 2)
 := by
  classical
  dsimp only
  let μ : ∀ i : Fin n, Measure (X i) := fun i => P.map (O i)
  let μ0 : Measure (∀ i : Fin n, X i) := Measure.pi μ
  let Q : A → (∀ i : Fin n, X i) := fun ω i => O i ω
  let lambda01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
  let νlocal : ∀ i : Fin n, Measure (X i × ℝ) := fun i => (μ i).prod lambda01
  let ν : Measure (∀ i : Fin n, X i × ℝ) := Measure.pi νlocal
  let q : (∀ i : Fin n, X i × ℝ) → (∀ i : Fin n, X i) := fun y i => (y i).1
  let ε : ℕ → ℝ := fun k => 1 / (8 * Real.sqrt (n : ℝ) * ((k : ℝ) + 1))
  let c : ∀ i : Fin n, (X i × ℝ) → ℝ := fun i => Shao.OQ6.ScalarObservationCoding.baseFourIndicatorCode (MeasurableSpace.natGeneratingSequence (X i × ℝ))
  let ξlocal : ∀ i : Fin n, (X i × ℝ) → ℝ := fun i z => g i z.1
  let Ylocal : ℕ → ∀ i : Fin n, (X i × ℝ) → ℝ := fun k i => Shao.OQ6.QuantizedObservationCoding.quantizedObservation (ε k) (ξlocal i) (c i)
  let ξ0 : Fin n → A → ℝ := fun i ω => g i (O i ω)
  let ξ : Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun i y => g i (y i).1
  let Y : ℕ → Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun k i y => Ylocal k i (y i)
  let a : ℕ → Fin n → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν (Y k)
  let s : ℕ → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν (Y k)
  let ηlocal : ℕ → ∀ i : Fin n, (X i × ℝ) → ℝ := fun k i => Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation (a k i) (s k) (Ylocal k i)
  let η : ℕ → Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
  let C : ℕ → (∀ i : Fin n, X i × ℝ) → (Fin n → ℝ) := fun k y i => η k i y
  let V0 : A → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ0 i ω) ^ 2)
  let V : (∀ i : Fin n, X i × ℝ) → ℝ := fun y => Real.sqrt (∑ i : Fin n, (ξ i y) ^ 2)
  let Vη : ℕ → (∀ i : Fin n, X i × ℝ) → ℝ := fun k y => Real.sqrt (∑ i : Fin n, (η k i y) ^ 2)
  let Z0 : Set A := {ω : A | V0 ω = 0}
  let Z : Set (∀ i : Fin n, X i × ℝ) := {y : (∀ i : Fin n, X i × ℝ) | V y = 0}
  let p0 : ℝ := P.real Z0
  let Aν : (∀ i : Fin n, X i × ℝ) → ℝ := fun y => Aenv (q y)
  let Bν : (∀ i : Fin n, X i × ℝ) → ℝ := fun y => Benv (q y)
  let Aνdelete : Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun i y => Adeleted i (fun j => (y j.1).1)
  let Bνdelete : Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun i y => Bdeleted i (fun j => (y j.1).1)
  let H : (∀ i : Fin n, X i × ℝ) → ℝ := fun y => (1 + V y) * (Real.sqrt (n : ℝ) + x * Real.sqrt (1 + Bν y))
  let ρ : ℕ → ℝ := fun k => 4 * ε k * Real.sqrt (n : ℝ)
  let Aε : ℕ → (∀ i : Fin n, X i × ℝ) → ℝ := fun k y => Aν y + ρ k * H y
  let ℓ0 : Fin n → A → ℝ := fun i ω => x * ξ0 i ω - (x * ξ0 i ω) ^ 2 / 2
  let ℓη : ℕ → Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun k i y => x * η k i y - (x * η k i y) ^ 2 / 2
  let S0 : A → ℝ := fun ω => ∑ i : Fin n, ℓ0 i ω
  let Sη : ℕ → (∀ i : Fin n, X i × ℝ) → ℝ := fun k y => ∑ i : Fin n, ℓη k i y
  let S0minus : Fin n → A → ℝ := fun i ω => ∑ j ∈ Finset.univ.erase i, ℓ0 j ω
  let Sηminus : ℕ → Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun k i y => ∑ j ∈ Finset.univ.erase i, ℓη k j y
  let I0 : ℝ := ∫ ω, Real.exp (S0 ω) ∂P
  let Iη : ℕ → ℝ := fun k => ∫ y, Real.exp (Sη k y) ∂ν
  let J0 : Fin n → ℝ := fun i => ∫ ω, Real.exp (S0minus i ω) ∂P
  let Jη : ℕ → Fin n → ℝ := fun k i => ∫ y, Real.exp (Sηminus k i y) ∂ν
  let δ0 : Fin n → ℝ := fun i => ∫ ω, (x * ξ0 i ω) ^ 2 * min |x * ξ0 i ω| 1 ∂P
  let δη : ℕ → Fin n → ℝ := fun k i => ∫ y, (x * η k i y) ^ 2 * min |x * η k i y| 1 ∂ν
  let L0 : ℝ := ∑ i : Fin n, δ0 i
  let Lη : ℕ → ℝ := fun k => ∑ i : Fin n, δη k i
  let fullTest0 : A → ℝ := fun ω => x * Aenv (Q ω) + x ^ 2 * Benv (Q ω)
  let fullTestη : ℕ → (∀ i : Fin n, X i × ℝ) → ℝ := fun k y => x * Aε k y + x ^ 2 * Bν y
  let deletedTest0 : Fin n → A → ℝ := fun i ω => min |x * ξ0 i ω| 1 * (|Aenv (Q ω) - Adeleted i (fun j => O j.1 ω)| + x * |Benv (Q ω) - Bdeleted i (fun j => O j.1 ω)|)
  let deletedTestη : ℕ → Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun k i y => min |x * η k i y| 1 * (|Aε k y - Aνdelete i y| + x * |Bν y - Bνdelete i y|)
  let compactDeletedTest0 : Fin n → A → ℝ := fun i ω => min |ξ0 i ω| (1 + x)⁻¹ * (|Aenv (Q ω) - Adeleted i (fun j => O j.1 ω)| + x * |Benv (Q ω) - Bdeleted i (fun j => O j.1 ω)|)
  let compactDeletedTestη : ℕ → Fin n → (∀ i : Fin n, X i × ℝ) → ℝ := fun k i y => min |η k i y| (1 + x)⁻¹ * (|Aε k y - Aνdelete i y| + x * |Bν y - Bνdelete i y|)
  let Lcompact0 : ℝ := ∑ i : Fin n, ∫ ω, ((1 + x) * ξ0 i ω) ^ 2 * min |(1 + x) * ξ0 i ω| 1 ∂P
  let Lcompactη : ℕ → ℝ := fun k => ∑ i : Fin n, ∫ y, ((1 + x) * η k i y) ^ 2 * min |(1 + x) * η k i y| 1 ∂ν
  let sourceCost0 : ℝ := ((∫ ω, fullTest0 ω * Real.exp (S0 ω) ∂P) + ∑ i : Fin n, ∫ ω, deletedTest0 i ω * Real.exp (S0minus i ω) ∂P) / I0
  let sourceCostη : ℕ → ℝ := fun k => ((∫ y, fullTestη k y * Real.exp (Sη k y) ∂ν) + ∑ i : Fin n, ∫ y, deletedTestη k i y * Real.exp (Sηminus k i y) ∂ν) / Iη k
  let compactCost0 : ℝ := Lcompact0 + (∫ ω, Aenv (Q ω) ∂P) + x * (∫ ω, Benv (Q ω) ∂P) + ∑ i : Fin n, ∫ ω, compactDeletedTest0 i ω ∂P
  let compactCostη : ℕ → ℝ := fun k => Lcompactη k + (∫ y, Aε k y ∂ν) + x * (∫ y, Bν y ∂ν) + ∑ i : Fin n, ∫ y, compactDeletedTestη k i y ∂ν
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hεpos (k : ℕ) : 0 < ε k := by dsimp only [ε]; positivity
  have hεsmall (k : ℕ) : ε k < 1 / (4 * Real.sqrt (n : ℝ)) := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    dsimp only [ε]
    apply (div_lt_div_iff₀ (by positivity : 0 < 8 * Real.sqrt (n : ℝ) * ((k : ℝ) + 1))
      (by positivity : 0 < 4 * Real.sqrt (n : ℝ))).2
    nlinarith [mul_nonneg hr.le hk]
  have hεeq : ε = fun k : ℕ => (1 / (8 * Real.sqrt (n : ℝ))) * (1 / ((k : ℝ) + 1)) := by
    funext k
    simp only [ε, div_eq_mul_inv, one_mul, mul_inv_rev]
    ring
  have hεlim : Filter.Tendsto ε Filter.atTop (nhds (0 : ℝ)) := by
    rw [hεeq]
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto
        (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhds (0 : ℝ))).const_mul
        (1 / (8 * Real.sqrt (n : ℝ)))
  rcases Shao.OQ6.AmbientCanonicalCodingTransport.ambient_independent_uniform_observation_transport
      P O hO hOindep with
    ⟨hμprob, hμ0prob, hprob, hQ, hq, _, _, _, _, hIntegral, _, _, hEvents⟩
  letI : ∀ i : Fin n, IsProbabilityMeasure (μ i) := hμprob
  letI : IsProbabilityMeasure μ0 := hμ0prob
  letI : IsProbabilityMeasure ν := hprob
  have hgLocal2 (i : Fin n) : MemLp (g i) 2 (μ i) :=
    (memLp_map_measure_iff (hg i).aestronglyMeasurable (hO i).aemeasurable).2 (hg2 i)
  have hgLocalFirst (i : Fin n) : (∫ o, g i o ∂(μ i)) = 0 := by
    have hi := integral_map (hO i).aemeasurable
      ((hgLocal2 i).integrable (by norm_num)).aestronglyMeasurable
    exact hi.trans (hgmean i)
  have hgLocalSecond (i : Fin n) : (∫ o, (g i o) ^ 2 ∂(μ i)) = ∫ ω, (g i (O i ω)) ^ 2 ∂P :=
    integral_map (hO i).aemeasurable (hgLocal2 i).integrable_sq.aestronglyMeasurable
  have hgLocalEnergy : (∑ i : Fin n, ∫ o, (g i o) ^ 2 ∂(μ i)) = 1 := by
    simpa only [hgLocalSecond] using hgenergy
  have hcode (k : ℕ) := Shao.OQ6.FiniteUniformCodingAssembly.actual_finite_normalized_coding_spec
    n hn μ g hg hgLocal2 hgLocalFirst hgLocalEnergy (ε k) (hεpos k) (hεsmall k)
  have hξm (i : Fin n) : Measurable (ξ i) := (hcode 0).2.2.1 i
  have hξ2 (i : Fin n) : MemLp (ξ i) 2 ν := (hcode 0).2.2.2.1 i
  have hξmean (i : Fin n) : (∫ y, ξ i y ∂ν) = 0 := (hcode 0).2.2.2.2.2.2.1 i
  have hξenergy : (∑ i : Fin n, ∫ y, (ξ i y) ^ 2 ∂ν) = 1 := (hcode 0).2.2.2.2.2.2.2.1
  have hYm (k : ℕ) (i : Fin n) : Measurable (Y k i) := (hcode k).2.2.2.2.2.2.2.2.2.1 i
  have herr (k : ℕ) (i : Fin n) (y : ∀ j : Fin n, X j × ℝ) : |Y k i y - ξ i y| ≤ ε k :=
    (hcode k).2.2.2.2.2.2.2.2.2.2.1 i y
  have hY2 (k : ℕ) (i : Fin n) : MemLp (Y k i) 2 ν :=
    (Shao.OQ6.ActualMomentNormalization.actual_centering_and_scale_spec ν n hn ξ (Y k)
      hξm hξ2 hξmean hξenergy (hYm k) (ε k) (hεpos k).le (herr k)).1 i
  have hlocalComap (k : ℕ) (i : Fin n) :
      MeasurableSpace.comap (ηlocal k i) (borel ℝ) = (inferInstance : MeasurableSpace (X i × ℝ)) :=
    (hcode k).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i
  have hηeval (k : ℕ) (i : Fin n) (y : ∀ j : Fin n, X j × ℝ) : η k i y = ηlocal k i (y i) :=
    (hcode k).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i y
  have hηind (k : ℕ) : iIndepFun (η k) ν :=
    (hcode k).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hηmean (k : ℕ) (i : Fin n) : (∫ y, η k i y ∂ν) = 0 :=
    (hcode k).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i
  have hηenergy (k : ℕ) : (∑ i : Fin n, ∫ y, (η k i y) ^ 2 ∂ν) = 1 :=
    (hcode k).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hηnull (k : ℕ) (i : Fin n) (t : ℝ) : ν ({y : (∀ j : Fin n, X j × ℝ) | η k i y = t}) = 0 :=
    (hcode k).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i t
  have hVηnull (k : ℕ) : ν ({y : (∀ j : Fin n, X j × ℝ) | Vη k y = 0}) = 0 :=
    (hcode k).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCeq (k : ℕ) : C k = Shao.OQ6.CoordinateBorelFactorization.coordinateCodeTuple (ηlocal k) := by
    funext y i
    exact hηeval k i y
  have hfull (k : ℕ) := Shao.OQ6.CoordinateBorelFactorization.finite_coordinate_code_tuple_spec
    (I := Fin n) (X := fun i : Fin n => X i × ℝ) (ηlocal k) (hlocalComap k)
  have hCspec (k : ℕ) :
      Measurable[(inferInstance : MeasurableSpace (∀ i : Fin n, X i × ℝ)), borel (Fin n → ℝ)] (C k) ∧
      MeasurableSpace.comap (C k) (borel (Fin n → ℝ)) = (inferInstance : MeasurableSpace (∀ i : Fin n, X i × ℝ)) := by
    rw [hCeq k]
    exact ⟨(hfull k).1, (hfull k).2.1⟩
  have hfactor (k : ℕ) (h : (∀ i : Fin n, X i × ℝ) → ℝ) (hh : Measurable h) :
      ∃ F : (Fin n → ℝ) → ℝ, Measurable[borel (Fin n → ℝ), borel ℝ] F ∧ ∀ y : (∀ i : Fin n, X i × ℝ), h y = F (C k y) := by
    rw [hCeq k]
    exact (hfull k).2.2 h hh
  have hdelete (k : ℕ) (i : Fin n) (d : (∀ j : {j : Fin n // j ≠ i}, X j.1 × ℝ) → ℝ) (hd : Measurable d) :
      ∃ F : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] F ∧
        (∀ u : (∀ j : {j : Fin n // j ≠ i}, X j.1 × ℝ), d u = F (fun j => ηlocal k j.1 (u j))) ∧
        Measurable[borel (Fin n → ℝ), borel ℝ] (fun v : Fin n → ℝ => F (fun j => v j.1)) ∧
        ∀ y : (∀ j : Fin n, X j × ℝ), d (fun j => y j.1) = F (fun j => η k j.1 y) := by
    rcases Shao.OQ6.CoordinateBorelFactorization.finite_deleted_code_factorization
      (X := fun j : Fin n => X j × ℝ) (ηlocal k) (hlocalComap k) i with
      ⟨_, _, _, _, _, _, hf⟩
    obtain ⟨F, hF, hEq, hFlift, hEqLift⟩ := hf d hd
    refine ⟨F, hF, hEq, hFlift, ?_⟩
    intro y
    exact hEqLift y
  rcases Shao.OQ6.NormalizedAnalyticCostLimits.actual_normalization_sequence_limits
      ν n hn ξ hξm hξ2 hξmean hξenergy Y hYm ε hεpos hεsmall hεlim herr with
    ⟨haBound, hsBound, haLim, hsLim, hρLim, hηspec, _, hηpoint, _, hVpoint, hL1, hL2⟩
  let gt : Fin n → (∀ i : Fin n, X i) → ℝ := fun i o => g i (o i)
  let Ad : Fin n → (∀ i : Fin n, X i) → ℝ := fun i o => Adeleted i (fun j => o j.1)
  let Bd : Fin n → (∀ i : Fin n, X i) → ℝ := fun i o => Bdeleted i (fun j => o j.1)
  have hgt (i : Fin n) : Measurable (gt i) := (hg i).comp (measurable_pi_apply i)
  have hAd (i : Fin n) : Measurable (Ad i) :=
    (hAdeleted i).comp (measurable_pi_iff.2 (fun j => measurable_pi_apply j.1))
  have hBd (i : Fin n) : Measurable (Bd i) :=
    (hBdeleted i).comp (measurable_pi_iff.2 (fun j => measurable_pi_apply j.1))
  have hAνm : Measurable Aν := hAenv.comp hq.measurable
  have hBνm : Measurable Bν := hBenv.comp hq.measurable
  have hAdνm (i : Fin n) : Measurable (Aνdelete i) := (hAd i).comp hq.measurable
  have hBdνm (i : Fin n) : Measurable (Bνdelete i) := (hBd i).comp hq.measurable
  have hAνI : Integrable Aν ν := (hIntegral Aenv hAenv hAint).2.2.1
  have hBνI : Integrable Bν ν := (hIntegral Benv hBenv hBint).2.2.1
  have hAdνI (i : Fin n) : Integrable (Aνdelete i) ν := (hIntegral (Ad i) (hAd i) (hAdeleteint i)).2.2.1
  have hBdνI (i : Fin n) : Integrable (Bνdelete i) ν := (hIntegral (Bd i) (hBd i) (hBdeleteint i)).2.2.1
  have hIntFromν (f : (∀ i : Fin n, X i) → ℝ) (hf : Measurable f)
      (hi : Integrable (fun y : (∀ i : Fin n, X i × ℝ) => f (q y)) ν) :
      Integrable (fun ω : A => f (Q ω)) P := by
    exact hQ.integrable_comp_of_integrable ((hq.integrable_comp hf.aestronglyMeasurable).1 hi)
  have hIntEq (f : (∀ i : Fin n, X i) → ℝ) (hf : Measurable f) :
      (∫ y, f (q y) ∂ν) = ∫ ω, f (Q ω) ∂P := by
    have h1 := integral_map hq.aemeasurable (hf.aestronglyMeasurable : AEStronglyMeasurable f (ν.map q))
    have h2 := integral_map hQ.aemeasurable (hf.aestronglyMeasurable : AEStronglyMeasurable f (P.map Q))
    rw [hq.map_eq] at h1
    rw [hQ.map_eq] at h2
    exact h1.symm.trans h2
  let Vt : (∀ i : Fin n, X i) → ℝ := fun o => Real.sqrt (∑ i : Fin n, (gt i o) ^ 2)
  have hVt : Measurable Vt := Real.continuous_sqrt.measurable.comp
    (Finset.measurable_sum Finset.univ (fun i _ => (hgt i).pow_const 2))
  have hZt : MeasurableSet {o : (∀ i : Fin n, X i) | Vt o = 0} := measurableSet_eq_fun hVt measurable_const
  have hZ0m : MeasurableSet Z0 := hZt.preimage hQ.measurable
  have hZm : MeasurableSet Z := hZt.preimage hq.measurable
  have hZero : ν Z = P Z0 ∧ ν.real Z = p0 := hEvents _ hZt
  have hHm : Measurable H := ((measurable_const.add (hVt.comp hq.measurable)).mul
    (measurable_const.add (measurable_const.mul
      (Real.continuous_sqrt.measurable.comp (measurable_const.add hBνm)))))
  have hAεm (k : ℕ) : Measurable (Aε k) := hAνm.add (measurable_const.mul hHm)
  rcases Shao.OQ6.NormalizedAnalyticCostLimits.actual_normalized_remainder_analytic_cost_limits
      ν n hn ξ hξm hξ2 hξmean hξenergy Y hYm ε hεpos hεsmall hεlim herr
      Aν Bν Aνdelete Bνdelete hAνm hBνm hAdνm hBdνm
      (fun y => hAnonneg (q y)) (fun y => hBnonneg (q y))
      (fun i y => hAdeletenonneg i _) (fun i y => hBdeletenonneg i _)
      hAνI hBνI hAdνI hBdνI x hx with
    ⟨hHI, hAεspec, hAεL1, hFullI, hFullηI, hDelI, hDelηI, hCompactDelI,
      hCompactDelηI, _, _, _, _, _, _, _, _, hSourceLimν, hCompactLimν⟩
  rcases Shao.OQ6.NormalizedAnalyticCostLimits.actual_projection_tilt_and_truncated_cost_limits
      ν n hn ξ hξm hξ2 hξmean hξenergy Y hYm ε hεpos hεsmall hεlim herr x with
    ⟨_, _, hExpI, hIpos, hExpηI, hMinusI, hMinusηI, _, _, _, _, _, _, _, _,
      hILimν, hJLimν, hδLimν, hLLimν, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  rcases Shao.OQ6.NormalizedAnalyticCostLimits.actual_projection_tilt_and_truncated_cost_limits
      ν n hn ξ hξm hξ2 hξmean hξenergy Y hYm ε hεpos hεsmall hεlim herr (1 + x) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hLcompactLimν,
      _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  let St : (∀ i : Fin n, X i) → ℝ := fun o => ∑ i : Fin n, (x * gt i o - (x * gt i o) ^ 2 / 2)
  let Stminus : Fin n → (∀ i : Fin n, X i) → ℝ := fun i o => ∑ j ∈ Finset.univ.erase i, (x * gt j o - (x * gt j o) ^ 2 / 2)
  have hSt : Measurable St := Finset.measurable_sum Finset.univ (fun i _ =>
    (measurable_const.mul (hgt i)).sub (((measurable_const.mul (hgt i)).pow_const 2).div_const 2))
  have hStminus (i : Fin n) : Measurable (Stminus i) := Finset.measurable_sum (Finset.univ.erase i) (fun j _ =>
    (measurable_const.mul (hgt j)).sub (((measurable_const.mul (hgt j)).pow_const 2).div_const 2))
  have hIeq : (∫ y, Real.exp (St (q y)) ∂ν) = I0 := hIntEq (fun o => Real.exp (St o)) hSt.exp
  have hJeq (i : Fin n) : (∫ y, Real.exp (Stminus i (q y)) ∂ν) = J0 i :=
    hIntEq (fun o => Real.exp (Stminus i o)) (hStminus i).exp
  have hI0I : Integrable (fun ω => Real.exp (S0 ω)) P :=
    hIntFromν (fun o => Real.exp (St o)) hSt.exp hExpI
  have hI0pos : 0 < I0 := by rw [← hIeq]; exact hIpos
  have hJ0I (i : Fin n) : Integrable (fun ω => Real.exp (S0minus i ω)) P ∧ 0 < J0 i := by
    refine ⟨hIntFromν (fun o => Real.exp (Stminus i o)) (hStminus i).exp (hMinusI i).1, ?_⟩
    rw [← hJeq i]
    exact (hMinusI i).2
  have hILim : Filter.Tendsto Iη Filter.atTop (nhds I0) := by
    change Filter.Tendsto Iη Filter.atTop (nhds (∫ y, Real.exp (St (q y)) ∂ν)) at hILimν
    simpa only [hIeq] using hILimν
  have hJLim (i : Fin n) : Filter.Tendsto (fun k : ℕ => Jη k i) Filter.atTop (nhds (J0 i)) := by
    have ht := hJLimν i
    change Filter.Tendsto (fun k : ℕ => Jη k i) Filter.atTop (nhds (∫ y, Real.exp (Stminus i (q y)) ∂ν)) at ht
    simpa only [hJeq] using ht
  have hδeq (t : ℝ) (i : Fin n) :
      (∫ y, (t * ξ i y) ^ 2 * min |t * ξ i y| 1 ∂ν) =
        ∫ ω, (t * ξ0 i ω) ^ 2 * min |t * ξ0 i ω| 1 ∂P := by
    apply hIntEq (fun o => (t * gt i o) ^ 2 * min |t * gt i o| 1)
    exact ((measurable_const.mul (hgt i)).pow_const 2).mul
      ((continuous_abs.measurable.comp (measurable_const.mul (hgt i))).min measurable_const)
  have hLeq (t : ℝ) :
      (∑ i : Fin n, ∫ y, (t * ξ i y) ^ 2 * min |t * ξ i y| 1 ∂ν) =
        ∑ i : Fin n, ∫ ω, (t * ξ0 i ω) ^ 2 * min |t * ξ0 i ω| 1 ∂P :=
    Finset.sum_congr rfl (fun i _ => hδeq t i)
  have hδLim (i : Fin n) : Filter.Tendsto (fun k : ℕ => δη k i) Filter.atTop (nhds (δ0 i)) := by
    have ht := hδLimν i
    change Filter.Tendsto (fun k : ℕ => δη k i) Filter.atTop
      (nhds (∫ y, (x * ξ i y) ^ 2 * min |x * ξ i y| 1 ∂ν)) at ht
    simpa only [hδeq] using ht
  have hLLim : Filter.Tendsto Lη Filter.atTop (nhds L0) := by
    change Filter.Tendsto Lη Filter.atTop
      (nhds (∑ i : Fin n, ∫ y, (x * ξ i y) ^ 2 * min |x * ξ i y| 1 ∂ν)) at hLLimν
    simpa only [hLeq] using hLLimν
  have hLcompactLim : Filter.Tendsto Lcompactη Filter.atTop (nhds Lcompact0) := by
    change Filter.Tendsto Lcompactη Filter.atTop
      (nhds (∑ i : Fin n, ∫ y, ((1 + x) * ξ i y) ^ 2 * min |(1 + x) * ξ i y| 1 ∂ν)) at hLcompactLimν
    simpa only [hLeq] using hLcompactLimν
  let Fraw : (∀ i : Fin n, X i) → ℝ := fun o => (x * Aenv o + x ^ 2 * Benv o) * Real.exp (St o)
  let Draw : Fin n → (∀ i : Fin n, X i) → ℝ := fun i o =>
    min |x * gt i o| 1 * (|Aenv o - Ad i o| + x * |Benv o - Bd i o|) * Real.exp (Stminus i o)
  let Craw : Fin n → (∀ i : Fin n, X i) → ℝ := fun i o =>
    min |gt i o| (1 + x)⁻¹ * (|Aenv o - Ad i o| + x * |Benv o - Bd i o|)
  have hFraw : Measurable Fraw := ((measurable_const.mul hAenv).add
    (measurable_const.mul hBenv)).mul hSt.exp
  have hGap (i : Fin n) : Measurable (fun o => |Aenv o - Ad i o| + x * |Benv o - Bd i o|) :=
    (continuous_abs.measurable.comp (hAenv.sub (hAd i))).add
      (measurable_const.mul (continuous_abs.measurable.comp (hBenv.sub (hBd i))))
  have hDraw (i : Fin n) : Measurable (Draw i) :=
    (((continuous_abs.measurable.comp (measurable_const.mul (hgt i))).min measurable_const).mul
      (hGap i)).mul (hStminus i).exp
  have hCraw (i : Fin n) : Measurable (Craw i) :=
    ((continuous_abs.measurable.comp (hgt i)).min measurable_const).mul (hGap i)
  have hFrawEq := hIntEq Fraw hFraw
  have hDrawEq (i : Fin n) := hIntEq (Draw i) (hDraw i)
  have hCrawEq (i : Fin n) := hIntEq (Craw i) (hCraw i)
  have hAeq := hIntEq Aenv hAenv
  have hBeq := hIntEq Benv hBenv
  have hFull0I : Integrable (fun ω => fullTest0 ω * Real.exp (S0 ω)) P :=
    hIntFromν Fraw hFraw hFullI
  have hDel0I (i : Fin n) : Integrable (fun ω => deletedTest0 i ω * Real.exp (S0minus i ω)) P ∧
      Integrable (compactDeletedTest0 i) P :=
    ⟨hIntFromν (Draw i) (hDraw i) (hDelI i), hIntFromν (Craw i) (hCraw i) (hCompactDelI i)⟩
  have hSourceLim : Filter.Tendsto sourceCostη Filter.atTop (nhds sourceCost0) := by
    change Filter.Tendsto sourceCostη Filter.atTop
      (nhds (((∫ y, Fraw (q y) ∂ν) + ∑ i : Fin n, ∫ y, Draw i (q y) ∂ν) /
        (∫ y, Real.exp (St (q y)) ∂ν))) at hSourceLimν
    rw [hFrawEq, hIeq] at hSourceLimν
    simp_rw [hDrawEq] at hSourceLimν
    exact hSourceLimν
  have hCompactLim : Filter.Tendsto compactCostη Filter.atTop (nhds compactCost0) := by
    change Filter.Tendsto compactCostη Filter.atTop
      (nhds ((∑ i : Fin n, ∫ y, ((1 + x) * ξ i y) ^ 2 * min |(1 + x) * ξ i y| 1 ∂ν) +
        (∫ y, Aenv (q y) ∂ν) + x * (∫ y, Benv (q y) ∂ν) + ∑ i : Fin n, ∫ y, Craw i (q y) ∂ν)) at hCompactLimν
    rw [hLeq, hAeq, hBeq] at hCompactLimν
    simp_rw [hCrawEq] at hCompactLimν
    exact hCompactLimν
  have hMass (k : ℕ) (i : Fin n) : (∫ y, Real.exp (Sηminus k i y) / Iη k ∂ν) = Jη k i / Iη k := by
    rw [integral_div]
  have hStrict (d l r b : ℝ) (hd : ∀ i : Fin n, δ0 i < d) (hl : L0 < l)
      (hR : sourceCost0 < r) (hB : compactCost0 < b) :
      ∀ᶠ k : ℕ in Filter.atTop, (∀ i : Fin n, δη k i < d) ∧ Lη k < l ∧ sourceCostη k < r ∧ compactCostη k < b := by
    have hAll : ∀ᶠ k : ℕ in Filter.atTop, ∀ i : Fin n, δη k i < d := by
      rw [Filter.eventually_all]
      intro i
      exact (hδLim i).eventually (eventually_lt_nhds (hd i))
    filter_upwards [hAll, hLLim.eventually (eventually_lt_nhds hl),
      hSourceLim.eventually (eventually_lt_nhds hR), hCompactLim.eventually (eventually_lt_nhds hB)] with k hk hkl hkr hkb
    exact ⟨hk, hkl, hkr, hkb⟩
  have hHalf (cSZ : ℝ) (hcSZ : 0 < cSZ) (hx1 : 1 ≤ x)
      (hd : ∀ i : Fin n, δ0 i ≤ (1 / 2 : ℝ)) (hl : L0 ≤ (cSZ / 2) * x ^ 2) :
      ∀ᶠ k : ℕ in Filter.atTop, (∀ i : Fin n, δη k i ≤ 1) ∧ Lη k ≤ cSZ * x ^ 2 := by
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx1
    have hgap : L0 < cSZ * x ^ 2 := by
      have hp := mul_pos hcSZ (sq_pos_of_pos hxpos)
      nlinarith
    have hAll : ∀ᶠ k : ℕ in Filter.atTop, ∀ i : Fin n, δη k i < (1 : ℝ) := by
      rw [Filter.eventually_all]
      intro i
      exact (hδLim i).eventually (eventually_lt_nhds (by linarith [hd i]))
    filter_upwards [hAll, hLLim.eventually (eventually_lt_nhds hgap)] with k hk hlk
    exact ⟨fun i => (hk i).le, hlk.le⟩
  exact ⟨(fun k => ⟨hεpos k, hεsmall k⟩), hεlim, hprob, hQ, hq,
    hZ0m, hZm, hZero.1, hZero.2, (fun k i => ⟨hYm k i, hY2 k i⟩), herr,
    haBound, hsBound, hηeval, hηspec,
    (fun k => ⟨hηind k, hηmean k, hηenergy k⟩), hηnull, hVηnull,
    hCspec, hfactor, hdelete, haLim, hsLim, hρLim, hηpoint, hVpoint, hL1, hL2,
    hHm, hHI, (fun k => ⟨hAεm k, (hAεspec k).1, (hAεspec k).2⟩), hAεL1,
    hI0I, hI0pos, hExpηI, hJ0I, hMinusηI, hMass, hFull0I, hDel0I,
    hFullηI, (fun k i => ⟨hDelηI k i, hCompactDelηI k i⟩),
    hILim, hJLim, hδLim, hLLim, hLcompactLim, hSourceLim, hCompactLim, hStrict, hHalf⟩

end

end Shao.OQ6.CanonicalSequenceAnalyticCosts
