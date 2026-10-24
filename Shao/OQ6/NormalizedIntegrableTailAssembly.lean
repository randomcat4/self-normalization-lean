import Shao.OQ6.NormalizedRawNumeratorBuffer
import Shao.OQ6.NormalizedEventTransport
import Shao.Probability.GaussianTail
import Mathlib.Probability.Independence.Basic

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Shao.OQ6.NormalizedIntegrableTailAssembly

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology

universe u

def ScalarShaoZhouFiniteCostTailInput
    (cSZ C1 C2 C3 C4 : ℝ) : Prop :=
  0 < cSZ ∧ 0 < C1 ∧ 0 < C2 ∧ 0 < C3 ∧ 0 < C4 ∧
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (ζ : Fin n → Ω → ℝ)
    (F1 F2 FA FB : (Fin n → ℝ) → ℝ)
    (FAdelete FBdelete : ∀ i : Fin n, ({j : Fin n // j ≠ i} → ℝ) → ℝ)
    (hζ : ∀ i : Fin n, Measurable (ζ i))
    (hζindep : iIndepFun ζ ν)
    (hζ2 : ∀ i : Fin n, MemLp (ζ i) 2 ν)
    (hζmean : ∀ i : Fin n, (∫ ω, ζ i ω ∂ν) = 0)
    (hζenergy : (∑ i : Fin n, ∫ ω, (ζ i ω) ^ 2 ∂ν) = 1)
    (hF1 : Measurable[borel (Fin n → ℝ), borel ℝ] F1)
    (hF2 : Measurable[borel (Fin n → ℝ), borel ℝ] F2)
    (hFA : Measurable[borel (Fin n → ℝ), borel ℝ] FA)
    (hFB : Measurable[borel (Fin n → ℝ), borel ℝ] FB)
    (hFAdelete : ∀ i : Fin n,
      Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] (FAdelete i))
    (hFBdelete : ∀ i : Fin n,
      Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] (FBdelete i))
    (x : ℝ),
    let C : Ω → (Fin n → ℝ) := fun ω i => ζ i ω
    let D1 : Ω → ℝ := fun ω => F1 (C ω)
    let D2 : Ω → ℝ := fun ω => F2 (C ω)
    let A : Ω → ℝ := fun ω => FA (C ω)
    let B : Ω → ℝ := fun ω => FB (C ω)
    let Adelete : Fin n → Ω → ℝ := fun i ω => FAdelete i (fun j => ζ j.1 ω)
    let Bdelete : Fin n → Ω → ℝ := fun i ω => FBdelete i (fun j => ζ j.1 ω)
    let W : Ω → ℝ := fun ω => ∑ i : Fin n, ζ i ω
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ζ i ω) ^ 2)
    let S : Ω → ℝ := fun ω => ∑ i : Fin n, (x * ζ i ω - (x * ζ i ω) ^ 2 / 2)
    let Sminus : Fin n → Ω → ℝ := fun i ω => ∑ j ∈ Finset.univ.erase i, (x * ζ j ω - (x * ζ j ω) ^ 2 / 2)
    let I : ℝ := ∫ ω, Real.exp (S ω) ∂ν
    let δ : Fin n → ℝ := fun i => ∫ ω, (x * ζ i ω) ^ 2 * min |x * ζ i ω| 1 ∂ν
    let L : ℝ := ∑ i : Fin n, δ i
    let full : Ω → ℝ := fun ω => (x * A ω + x ^ 2 * B ω) * Real.exp (S ω)
    let deleted : Fin n → Ω → ℝ := fun i ω => (min |x * ζ i ω| 1 * (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)) * Real.exp (Sminus i ω)
    let R : ℝ := ((∫ ω, full ω ∂ν) + ∑ i : Fin n, ∫ ω, deleted i ω ∂ν) / I
    let T : Ω → ℝ := fun ω => (W ω + D1 ω) / (V ω * Real.sqrt (1 + D2 ω))
    (∀ ω : Ω, 0 ≤ A ω ∧ 0 ≤ B ω) →
    (∀ (i : Fin n) (ω : Ω), 0 ≤ Adelete i ω ∧ 0 ≤ Bdelete i ω) →
    (∀ᵐ ω ∂ν, |D1 ω| ≤ A ω ∧ |D2 ω| ≤ B ω) →
    (∀ᵐ ω ∂ν, 0 < 1 + D2 ω) →
    (∀ᵐ ω ∂ν, 0 < V ω) →
    Integrable (fun ω => Real.exp (S ω)) ν →
    0 < I → Integrable full ν →
    (∀ i : Fin n, Integrable (deleted i) ν) →
    1 ≤ x → (∀ i : Fin n, δ i ≤ 1) → L ≤ cSZ * x ^ 2 →
    Shao.standardNormalTail x * Real.exp (-C1 * L) * (1 - C2 * R) ≤
      ν.real {ω : Ω | x ≤ T ω} ∧
    ν.real {ω : Ω | x ≤ T ω} ≤
      Shao.standardNormalTail x * Real.exp (C3 * L) * (1 + C4 * R) +
        ν.real {ω : Ω | x * |D1 ω| > V ω / 4} +
        ν.real {ω : Ω | x ^ 2 * |D2 ω| > (1 / 4 : ℝ)}

theorem actual_normalized_integrable_tail_assembly
    {Ω : Type u} [MeasurableSpace Ω]
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
    (hηindep : ∀ k : ℕ, iIndepFun
      (Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)) ν)
    (hηpos : ∀ k : ℕ, ∀ᵐ ω ∂ν, 0 < Real.sqrt (∑ i : Fin n,
      (Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k) i ω) ^ 2))
    (hFullFactor : ∀ (k : ℕ) (h : Ω → ℝ), Measurable h →
      ∃ F : (Fin n → ℝ) → ℝ,
        Measurable[borel (Fin n → ℝ), borel ℝ] F ∧
        ∀ ω : Ω, h ω = F (fun i =>
          Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k) i ω))
    (D1 D2 κ A B : Ω → ℝ) (Adelete Bdelete : Fin n → Ω → ℝ)
    (hD1 : Measurable D1) (hD2 : Measurable D2) (hκ : Measurable κ)
    (hA : Measurable A) (hB : Measurable B)
    (hAdelete : ∀ i : Fin n, Measurable (Adelete i))
    (hBdelete : ∀ i : Fin n, Measurable (Bdelete i))
    (hAnonneg : ∀ ω : Ω, 0 ≤ A ω)
    (hBnonneg : ∀ ω : Ω, 0 ≤ B ω)
    (hAdeletenonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ Adelete i ω)
    (hBdeletenonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ Bdelete i ω)
    (hD1A : ∀ ω : Ω, |D1 ω| ≤ A ω)
    (hD2B : ∀ ω : Ω, |D2 ω| ≤ B ω)
    (hD2pos : ∀ᵐ ω ∂ν, 0 < 1 + D2 ω)
    (hAint : Integrable A ν) (hBint : Integrable B ν)
    (hAdeleteint : ∀ i : Fin n, Integrable (Adelete i) ν)
    (hBdeleteint : ∀ i : Fin n, Integrable (Bdelete i) ν)
    (hAdeleteFactor : ∀ (k : ℕ) (i : Fin n),
      ∃ F : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] F ∧
        ∀ ω : Ω, Adelete i ω = F (fun j =>
          Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k) j.1 ω))
    (hBdeleteFactor : ∀ (k : ℕ) (i : Fin n),
      ∃ F : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] F ∧
        ∀ ω : Ω, Bdelete i ω = F (fun j =>
          Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k) j.1 ω))
    (cSZ C1 C2 C3 C4 : ℝ)
    (hSZ : ScalarShaoZhouFiniteCostTailInput.{u} cSZ C1 C2 C3 C4)
    (x : ℝ) (hx : 1 ≤ x)
    (hδ : ∀ i : Fin n,
      (∫ ω, (x * ξ i ω) ^ 2 * min |x * ξ i ω| 1 ∂ν) ≤ (1 / 2 : ℝ))
    (hL : (∑ i : Fin n, ∫ ω, (x * ξ i ω) ^ 2 * min |x * ξ i ω| 1 ∂ν) ≤
      (cSZ / 2) * x ^ 2) :
    let η : ℕ → Fin n → Ω → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
    let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
    let Wη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, η k i ω
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
    let Vη : ℕ → Ω → ℝ := fun k ω => Real.sqrt (∑ i : Fin n, (η k i ω) ^ 2)
    let b : Ω → ℝ := fun ω => Real.sqrt (1 + D2 ω)
    let Dη : ℕ → Ω → ℝ := fun k ω => D1 ω + W ω - Wη k ω + x * b ω * (Vη k ω - V ω)
    let H : Ω → ℝ := fun ω => (1 + V ω) * (Real.sqrt (n : ℝ) + x * Real.sqrt (1 + B ω))
    let ρ : ℕ → ℝ := fun k => 4 * ε k * Real.sqrt (n : ℝ)
    let Aε : ℕ → Ω → ℝ := fun k ω => A ω + ρ k * H ω
    let T : Ω → ℝ := fun ω => if V ω = 0 then κ ω else (W ω + D1 ω) / (V ω * b ω)
    let Tη : ℕ → Ω → ℝ := fun k ω => (Wη k ω + Dη k ω) / (Vη k ω * b ω)
    let F : Set Ω := {ω : Ω | x * V ω * b ω ≤ W ω + D1 ω}
    let Z : Set Ω := {ω : Ω | V ω = 0}
    let p0 : ℝ := ν.real Z
    let δ : Fin n → ℝ := fun i => ∫ ω, (x * ξ i ω) ^ 2 * min |x * ξ i ω| 1 ∂ν
    let δη : ℕ → Fin n → ℝ := fun k i => ∫ ω, (x * η k i ω) ^ 2 * min |x * η k i ω| 1 ∂ν
    let L : ℝ := ∑ i : Fin n, δ i
    let Lη : ℕ → ℝ := fun k => ∑ i : Fin n, δη k i
    let S : Ω → ℝ := fun ω => ∑ i : Fin n, (x * ξ i ω - (x * ξ i ω) ^ 2 / 2)
    let Sη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, (x * η k i ω - (x * η k i ω) ^ 2 / 2)
    let Sminus : Fin n → Ω → ℝ := fun i ω => ∑ j ∈ Finset.univ.erase i, (x * ξ j ω - (x * ξ j ω) ^ 2 / 2)
    let Sηminus : ℕ → Fin n → Ω → ℝ := fun k i ω => ∑ j ∈ Finset.univ.erase i, (x * η k j ω - (x * η k j ω) ^ 2 / 2)
    let I : ℝ := ∫ ω, Real.exp (S ω) ∂ν
    let Iη : ℕ → ℝ := fun k => ∫ ω, Real.exp (Sη k ω) ∂ν
    let full : Ω → ℝ := fun ω => (x * A ω + x ^ 2 * B ω) * Real.exp (S ω)
    let fullη : ℕ → Ω → ℝ := fun k ω => (x * Aε k ω + x ^ 2 * B ω) * Real.exp (Sη k ω)
    let deleted : Fin n → Ω → ℝ := fun i ω => (min |x * ξ i ω| 1 * (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)) * Real.exp (Sminus i ω)
    let deletedη : ℕ → Fin n → Ω → ℝ := fun k i ω => (min |x * η k i ω| 1 * (|Aε k ω - Adelete i ω| + x * |B ω - Bdelete i ω|)) * Real.exp (Sηminus k i ω)
    let R : ℝ := ((∫ ω, full ω ∂ν) + ∑ i : Fin n, ∫ ω, deleted i ω ∂ν) / I
    let Rη : ℕ → ℝ := fun k => ((∫ ω, fullη k ω ∂ν) + ∑ i : Fin n, ∫ ω, deletedη k i ω ∂ν) / Iη k
    let lower : ℝ := Shao.standardNormalTail x * Real.exp (-C1 * L) * (1 - C2 * R)
    let lowerη : ℕ → ℝ := fun k => Shao.standardNormalTail x * Real.exp (-C1 * Lη k) * (1 - C2 * Rη k)
    let upper : ℝ := Shao.standardNormalTail x * Real.exp (C3 * L) * (1 + C4 * R)
    let upperη : ℕ → ℝ := fun k => Shao.standardNormalTail x * Real.exp (C3 * Lη k) * (1 + C4 * Rη k)
    let numeratorBad : Set Ω := {ω : Ω | x * |D1 ω| > V ω / 8}
    let numeratorBadη : ℕ → Set Ω := fun k => {ω : Ω | x * |Dη k ω| > Vη k ω / 4}
    let denominatorBad : Set Ω := {ω : Ω | x ^ 2 * |D2 ω| > (1 / 4 : ℝ)}
    (∀ᶠ k : ℕ in Filter.atTop, (∀ i : Fin n, δη k i ≤ 1) ∧ Lη k ≤ cSZ * x ^ 2) ∧
    Filter.Tendsto lowerη Filter.atTop (nhds lower) ∧
    Filter.Tendsto upperη Filter.atTop (nhds upper) ∧
    (∀ k : ℕ, ν.real {ω : Ω | x ≤ Tη k ω} = ν.real F) ∧
    lower ≤ ν.real F ∧
    ν.real F ≤ upper + ν.real numeratorBad + ν.real denominatorBad + p0 ∧
    lower - p0 ≤ ν.real {ω : Ω | x ≤ T ω} ∧
    ν.real {ω : Ω | x ≤ T ω} ≤
      upper + ν.real numeratorBad + ν.real denominatorBad + 2 * p0
 := by
  classical
  let η : ℕ → Fin n → Ω → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
  let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
  let Wη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, η k i ω
  let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
  let Vη : ℕ → Ω → ℝ := fun k ω => Real.sqrt (∑ i : Fin n, (η k i ω) ^ 2)
  let b : Ω → ℝ := fun ω => Real.sqrt (1 + D2 ω)
  let Dη : ℕ → Ω → ℝ := fun k ω => D1 ω + W ω - Wη k ω + x * b ω * (Vη k ω - V ω)
  let H : Ω → ℝ := fun ω => (1 + V ω) * (Real.sqrt (n : ℝ) + x * Real.sqrt (1 + B ω))
  let ρ : ℕ → ℝ := fun k => 4 * ε k * Real.sqrt (n : ℝ)
  let Aε : ℕ → Ω → ℝ := fun k ω => A ω + ρ k * H ω
  let T : Ω → ℝ := fun ω => if V ω = 0 then κ ω else (W ω + D1 ω) / (V ω * b ω)
  let Tη : ℕ → Ω → ℝ := fun k ω => (Wη k ω + Dη k ω) / (Vη k ω * b ω)
  let F : Set Ω := {ω : Ω | x * V ω * b ω ≤ W ω + D1 ω}
  let Z : Set Ω := {ω : Ω | V ω = 0}
  let p0 : ℝ := ν.real Z
  let δ : Fin n → ℝ := fun i => ∫ ω, (x * ξ i ω) ^ 2 * min |x * ξ i ω| 1 ∂ν
  let δη : ℕ → Fin n → ℝ := fun k i => ∫ ω, (x * η k i ω) ^ 2 * min |x * η k i ω| 1 ∂ν
  let L : ℝ := ∑ i : Fin n, δ i
  let Lη : ℕ → ℝ := fun k => ∑ i : Fin n, δη k i
  let S : Ω → ℝ := fun ω => ∑ i : Fin n, (x * ξ i ω - (x * ξ i ω) ^ 2 / 2)
  let Sη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, (x * η k i ω - (x * η k i ω) ^ 2 / 2)
  let Sminus : Fin n → Ω → ℝ := fun i ω => ∑ j ∈ Finset.univ.erase i, (x * ξ j ω - (x * ξ j ω) ^ 2 / 2)
  let Sηminus : ℕ → Fin n → Ω → ℝ := fun k i ω => ∑ j ∈ Finset.univ.erase i, (x * η k j ω - (x * η k j ω) ^ 2 / 2)
  let I : ℝ := ∫ ω, Real.exp (S ω) ∂ν
  let Iη : ℕ → ℝ := fun k => ∫ ω, Real.exp (Sη k ω) ∂ν
  let full : Ω → ℝ := fun ω => (x * A ω + x ^ 2 * B ω) * Real.exp (S ω)
  let fullη : ℕ → Ω → ℝ := fun k ω => (x * Aε k ω + x ^ 2 * B ω) * Real.exp (Sη k ω)
  let deleted : Fin n → Ω → ℝ := fun i ω => (min |x * ξ i ω| 1 * (|A ω - Adelete i ω| + x * |B ω - Bdelete i ω|)) * Real.exp (Sminus i ω)
  let deletedη : ℕ → Fin n → Ω → ℝ := fun k i ω => (min |x * η k i ω| 1 * (|Aε k ω - Adelete i ω| + x * |B ω - Bdelete i ω|)) * Real.exp (Sηminus k i ω)
  let R : ℝ := ((∫ ω, full ω ∂ν) + ∑ i : Fin n, ∫ ω, deleted i ω ∂ν) / I
  let Rη : ℕ → ℝ := fun k => ((∫ ω, fullη k ω ∂ν) + ∑ i : Fin n, ∫ ω, deletedη k i ω ∂ν) / Iη k
  let lower : ℝ := Shao.standardNormalTail x * Real.exp (-C1 * L) * (1 - C2 * R)
  let lowerη : ℕ → ℝ := fun k => Shao.standardNormalTail x * Real.exp (-C1 * Lη k) * (1 - C2 * Rη k)
  let upper : ℝ := Shao.standardNormalTail x * Real.exp (C3 * L) * (1 + C4 * R)
  let upperη : ℕ → ℝ := fun k => Shao.standardNormalTail x * Real.exp (C3 * Lη k) * (1 + C4 * Rη k)
  let numeratorBad : Set Ω := {ω : Ω | x * |D1 ω| > V ω / 8}
  let numeratorBadη : ℕ → Set Ω := fun k => {ω : Ω | x * |Dη k ω| > Vη k ω / 4}
  let denominatorBad : Set Ω := {ω : Ω | x ^ 2 * |D2 ω| > (1 / 4 : ℝ)}
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  rcases hSZ with ⟨hcSZ, hC1, hC2, hC3, hC4, hSource⟩
  have hMom (k : ℕ) :
      (∀ i : Fin n, Measurable (η k i) ∧ MemLp (η k i) 2 ν) ∧
      (∀ i : Fin n, (∫ ω, η k i ω ∂ν) = 0) ∧
      (∑ i : Fin n, ∫ ω, (η k i ω) ^ 2 ∂ν) = 1 := by
    have hh := Shao.OQ6.ActualMomentNormalization.actual_moment_normalization_spec
      ν n hn ξ (Y k) hξ hξ2 hξmean hξenergy (hY k)
      (ε k) (hε k) (hεsmall k) (herr k)
    rcases hh with ⟨_, hm, h2, _, _, hz, he, _⟩
    exact ⟨fun i => ⟨hm i, h2 i⟩, hz, he⟩
  have hEnvelope (k : ℕ) : Measurable (Dη k) ∧ Measurable (Aε k) ∧
      (∀ ω : Ω, |Dη k ω| ≤ Aε k ω) ∧ (∀ ω : Ω, 0 ≤ Aε k ω) := by
    have hh := Shao.OQ6.NormalizedRemainderEnvelope.actual_normalized_remainder_envelope_spec
      ν n hn ξ (Y k) hξ hξ2 hξmean hξenergy (hY k)
      D1 D2 A B Adelete Bdelete hD1 hD2 hA hB hAnonneg hBnonneg
      hD1A hD2B hAint hBint (ε k) (hε k) (hεsmall k) (herr k) x hx0
    rcases hh with ⟨_, _, _, _, _, _, _, _, hmD, hmA, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, hdom, hnon, _⟩
    exact ⟨hmD, hmA, hdom, hnon⟩
  have hProjection :=
    Shao.OQ6.NormalizedAnalyticCostLimits.actual_projection_tilt_and_truncated_cost_limits
      ν n hn ξ hξ hξ2 hξmean hξenergy Y hY ε hε hεsmall hεlim herr x
  rcases hProjection with ⟨_, _, hSInt, hIpos, hSηspec, _, _, _, _, _, _, _, _, _,
    _, _, _, hδlim0, hLlim0, _⟩
  have hδlim : ∀ i : Fin n,
      Filter.Tendsto (fun k : ℕ => δη k i) Filter.atTop (nhds (δ i)) := hδlim0
  have hLlim : Filter.Tendsto Lη Filter.atTop (nhds L) := hLlim0
  have hCosts :=
    Shao.OQ6.NormalizedAnalyticCostLimits.actual_normalized_remainder_analytic_cost_limits
      ν n hn ξ hξ hξ2 hξmean hξenergy Y hY ε hε hεsmall hεlim herr
      A B Adelete Bdelete hA hB hAdelete hBdelete hAnonneg hBnonneg
      hAdeletenonneg hBdeletenonneg hAint hBint hAdeleteint hBdeleteint x hx0
  rcases hCosts with ⟨_, _, _, hFullInt, hFullηInt, hDeletedInt, hDeletedηInt,
    _, _, _, _, _, _, _, _, _, _, hRlim0, _⟩
  have hRlim : Filter.Tendsto Rη Filter.atTop (nhds R) := hRlim0
  have hBudget : ∀ᶠ k : ℕ in Filter.atTop,
      (∀ i : Fin n, δη k i ≤ 1) ∧ Lη k ≤ cSZ * x ^ 2 := by
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
    have hgap : L < cSZ * x ^ 2 := by
      have hp := mul_pos hcSZ (sq_pos_of_pos hxpos)
      change L ≤ (cSZ / 2) * x ^ 2 at hL
      nlinarith
    have hAll : ∀ᶠ k : ℕ in Filter.atTop, ∀ i : Fin n, δη k i < (1 : ℝ) := by
      rw [Filter.eventually_all]
      intro i
      have hi : δ i < (1 : ℝ) := lt_of_le_of_lt (hδ i) (by norm_num)
      exact (hδlim i).eventually (eventually_lt_nhds hi)
    filter_upwards [hAll, hLlim.eventually (eventually_lt_nhds hgap)] with k hk hlk
    exact ⟨fun i => (hk i).le, hlk.le⟩
  have hLowerExp : Filter.Tendsto (fun k : ℕ => Real.exp (-C1 * Lη k))
      Filter.atTop (nhds (Real.exp (-C1 * L))) :=
    Real.continuous_exp.continuousAt.tendsto.comp (hLlim.const_mul (-C1))
  have hLowerFactor : Filter.Tendsto (fun k : ℕ => 1 - C2 * Rη k)
      Filter.atTop (nhds (1 - C2 * R)) :=
    tendsto_const_nhds.sub (hRlim.const_mul C2)
  have hLowerLim : Filter.Tendsto lowerη Filter.atTop (nhds lower) :=
    (tendsto_const_nhds.mul hLowerExp).mul hLowerFactor
  have hUpperExp : Filter.Tendsto (fun k : ℕ => Real.exp (C3 * Lη k))
      Filter.atTop (nhds (Real.exp (C3 * L))) :=
    Real.continuous_exp.continuousAt.tendsto.comp (hLlim.const_mul C3)
  have hUpperFactor : Filter.Tendsto (fun k : ℕ => 1 + C4 * Rη k)
      Filter.atTop (nhds (1 + C4 * R)) :=
    tendsto_const_nhds.add (hRlim.const_mul C4)
  have hUpperLim : Filter.Tendsto upperη Filter.atTop (nhds upper) :=
    (tendsto_const_nhds.mul hUpperExp).mul hUpperFactor
  have hTransport (k : ℕ) :
      ν.real {ω : Ω | x ≤ Tη k ω} = ν.real F ∧
      |ν.real {ω : Ω | x ≤ T ω} - ν.real F| ≤ p0 := by
    have hh := Shao.OQ6.NormalizedEventTransport.actual_normalized_quotient_projection_zero_transport
      ν ξ (Y k) hξ (hY k) D1 D2 κ hD1 hD2 hκ hD2pos (hηpos k)
    rcases hh with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hEvents⟩
    have hCmp : (fun a b : ℝ => b ≤ a) ∈
        ({R | R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨
          R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨
          R = (fun a b : ℝ => a = b)} : Set (ℝ → ℝ → Prop)) :=
      Or.inr (Or.inr (Or.inl rfl))
    rcases hEvents x (fun a b : ℝ => b ≤ a) hCmp with
      ⟨_, _, _, hMass, _, _, hPhysical, _, _⟩
    constructor
    · change (ν {ω : Ω | x ≤ Tη k ω}).toReal = (ν F).toReal
      exact congrArg ENNReal.toReal hMass
    · exact hPhysical
  have hBad :=
    Shao.OQ6.NormalizedRawNumeratorBuffer.actual_normalized_raw_numerator_bad_event_limsup
      ν n hn ξ hξ hξ2 hξmean hξenergy Y hY ε hε hεsmall hεlim herr
      D1 D2 hD1 hD2 x hx0
  rcases hBad with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, hBadEventually0, _⟩
  have hBadEventually : ∀ t : ℝ, 0 < t → ∀ᶠ k : ℕ in Filter.atTop,
      ν.real (numeratorBadη k) ≤ ν.real numeratorBad + p0 + t := hBadEventually0
  have hScalar (k : ℕ) (hd : ∀ i : Fin n, δη k i ≤ 1)
      (hl : Lη k ≤ cSZ * x ^ 2) :
      lowerη k ≤ ν.real {ω : Ω | x ≤ Tη k ω} ∧
      ν.real {ω : Ω | x ≤ Tη k ω} ≤
        upperη k + ν.real (numeratorBadη k) + ν.real denominatorBad := by
    obtain ⟨F1, hF1, hF1eq⟩ := hFullFactor k (Dη k) (hEnvelope k).1
    obtain ⟨F2, hF2, hF2eq⟩ := hFullFactor k D2 hD2
    obtain ⟨FA, hFA, hFAeq⟩ := hFullFactor k (Aε k) (hEnvelope k).2.1
    obtain ⟨FB, hFB, hFBeq⟩ := hFullFactor k B hB
    change ∀ ω : Ω, Dη k ω = F1 (fun i => η k i ω) at hF1eq
    change ∀ ω : Ω, D2 ω = F2 (fun i => η k i ω) at hF2eq
    change ∀ ω : Ω, Aε k ω = FA (fun i => η k i ω) at hFAeq
    change ∀ ω : Ω, B ω = FB (fun i => η k i ω) at hFBeq
    let FAdelete (i : Fin n) : ({j : Fin n // j ≠ i} → ℝ) → ℝ :=
      Classical.choose (hAdeleteFactor k i)
    let FBdelete (i : Fin n) : ({j : Fin n // j ≠ i} → ℝ) → ℝ :=
      Classical.choose (hBdeleteFactor k i)
    have hFAdelete (i : Fin n) :
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] (FAdelete i) :=
      (Classical.choose_spec (hAdeleteFactor k i)).1
    have hFBdelete (i : Fin n) :
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] (FBdelete i) :=
      (Classical.choose_spec (hBdeleteFactor k i)).1
    have hFAdeleteEq (i : Fin n) (ω : Ω) :
        Adelete i ω = FAdelete i (fun j => η k j.1 ω) :=
      (Classical.choose_spec (hAdeleteFactor k i)).2 ω
    have hFBdeleteEq (i : Fin n) (ω : Ω) :
        Bdelete i ω = FBdelete i (fun j => η k j.1 ω) :=
      (Classical.choose_spec (hBdeleteFactor k i)).2 ω
    have hs := hSource ν n hn (η k) F1 F2 FA FB FAdelete FBdelete
      (fun i => ((hMom k).1 i).1) (hηindep k)
      (fun i => ((hMom k).1 i).2) (hMom k).2.1 (hMom k).2.2
      hF1 hF2 hFA hFB hFAdelete hFBdelete x
    dsimp only at hs
    simp only [← hF1eq, ← hF2eq, ← hFAeq, ← hFBeq,
      ← hFAdeleteEq, ← hFBdeleteEq] at hs
    have hNon : ∀ ω : Ω, 0 ≤ Aε k ω ∧ 0 ≤ B ω :=
      fun ω => ⟨(hEnvelope k).2.2.2 ω, hBnonneg ω⟩
    have hDelNon : ∀ (i : Fin n) (ω : Ω), 0 ≤ Adelete i ω ∧ 0 ≤ Bdelete i ω :=
      fun i ω => ⟨hAdeletenonneg i ω, hBdeletenonneg i ω⟩
    have hDom : ∀ᵐ ω ∂ν, |Dη k ω| ≤ Aε k ω ∧ |D2 ω| ≤ B ω :=
      Filter.Eventually.of_forall fun ω => ⟨(hEnvelope k).2.2.1 ω, hD2B ω⟩
    exact hs hNon hDelNon hDom hD2pos (hηpos k) (hSηspec k).1
      (hSηspec k).2 (hFullηInt k) (hDeletedηInt k) hx hd hl
  have hLowerEvent : lower ≤ ν.real F := by
    apply le_of_tendsto hLowerLim
    filter_upwards [hBudget] with k hk
    simpa only [(hTransport k).1] using (hScalar k hk.1 hk.2).1
  have hUpperError (t : ℝ) (ht : 0 < t) :
      ν.real F ≤ upper + ν.real numeratorBad + ν.real denominatorBad + p0 + t := by
    have hEv : ∀ᶠ k : ℕ in Filter.atTop,
        ν.real F ≤ upperη k + ν.real numeratorBad + ν.real denominatorBad + p0 + t := by
      filter_upwards [hBudget, hBadEventually t ht] with k hk hbad
      have hs := (hScalar k hk.1 hk.2).2
      rw [(hTransport k).1] at hs
      linarith
    have hLimit : Filter.Tendsto
        (fun k : ℕ => upperη k + ν.real numeratorBad + ν.real denominatorBad + p0 + t)
        Filter.atTop (nhds (upper + ν.real numeratorBad + ν.real denominatorBad + p0 + t)) :=
      (((hUpperLim.add tendsto_const_nhds).add tendsto_const_nhds).add
        tendsto_const_nhds).add tendsto_const_nhds
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hLimit hEv
  have hUpperEvent :
      ν.real F ≤ upper + ν.real numeratorBad + ν.real denominatorBad + p0 := by
    by_contra hnot
    have hpos : 0 < ν.real F - (upper + ν.real numeratorBad + ν.real denominatorBad + p0) :=
      sub_pos.mpr (lt_of_not_ge hnot)
    have hh := hUpperError
      ((ν.real F - (upper + ν.real numeratorBad + ν.real denominatorBad + p0)) / 2)
      (by linarith)
    linarith
  have hPhysical := (hTransport 0).2
  have hPhysicalLower : lower - p0 ≤ ν.real {ω : Ω | x ≤ T ω} := by
    have hd := (abs_le.mp hPhysical).1
    linarith
  have hPhysicalUpper : ν.real {ω : Ω | x ≤ T ω} ≤
      upper + ν.real numeratorBad + ν.real denominatorBad + 2 * p0 := by
    have hd := (abs_le.mp hPhysical).2
    linarith
  exact ⟨hBudget, hLowerLim, hUpperLim, (fun k => (hTransport k).1),
    hLowerEvent, hUpperEvent, hPhysicalLower, hPhysicalUpper⟩

end

end Shao.OQ6.NormalizedIntegrableTailAssembly
