# Unit141 frozen contracts v1

Frozen 2026-10-24T02:20:15.056Z. Two exact public theorem types; zero public definitions. Full JSON is authoritative for exact UTF-8 header bytes.

The original six imports gain only Shao.OQ6.ActualQuadraticTiltMoments. Both reviewed raw headers and all mathematical premises/conclusions are unchanged. Complete LOCAL implementation may proceed under the exact frozen140 interface. **Every141 server and acceptance gate must wait for140 exact-source qualification with complete independent source/proof/type/value coverage and kernel/all-owned transitive-axiom evidence.** No141 elaboration or acceptance is asserted.

Q is the finite measure m_i^-1 H, with actual mass m_i^-1. H leaves coordinate i original. Genuine weighted absolute integrability precedes signed transport. Actual deletion keeps original n coefficients, including n=3; no n>=4 repair or higher mixed moment. Uniform quantitative rates, weighted11–14/cost/HG/p54 and all original roots remain OPEN; external Shao-Zhou attribution remains.

~~~lean
import Shao.OQ6.QuadraticTilt
import Shao.OQ6.ObservationProductTilt
import Shao.OQ6.ActualQuadraticTiltMoments
import Shao.OQ6.ResidualDeletion
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false

namespace Shao.OQ6.PartialObservationTilt

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem finite_observation_partial_tilt_transport
    {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (mu : Fin n → Measure Ω)
    [∀ j : Fin n, IsProbabilityMeasure (mu j)]
    (phi : Fin n → Ω → ℝ)
    (hExp : ∀ j : Fin n,
      Integrable (fun o : Ω => Real.exp (phi j o)) (mu j))
    (i : Fin n) :
    let m : Fin n → ℝ := fun j =>
      ∫ o : Ω, Real.exp (phi j o) ∂(mu j)
    let I : ℝ := ∏ j : Fin n, m j
    let P : Measure (Fin n → Ω) := Measure.pi mu
    let S : (Fin n → Ω) → ℝ := fun xi =>
      ∑ j : Fin n, phi j (xi j)
    let Sminus : (Fin n → Ω) → ℝ := fun xi =>
      ∑ j ∈ Finset.univ.erase i, phi j (xi j)
    let H : Measure (Fin n → Ω) := Measure.pi
      (fun j : Fin n => if j = i then mu j else (mu j).tilted (phi j))
    let R : (Fin n → Ω) → ℝ := fun xi => Real.exp (Sminus xi) / I
    let Q : Measure (Fin n → Ω) :=
      P.withDensity (fun xi => ENNReal.ofReal (R xi))
    (∀ j : Fin n, 0 < m j) ∧ 0 < I ∧
      Integrable (fun xi => Real.exp (S xi)) P ∧
      (∫ xi, Real.exp (S xi) ∂P) = I ∧
      Integrable (fun xi => Real.exp (Sminus xi)) P ∧
      (∫ xi, Real.exp (Sminus xi) ∂P) =
        (∏ j ∈ Finset.univ.erase i, m j) ∧
      I = m i * (∏ j ∈ Finset.univ.erase i, m j) ∧
      (∀ xi, R xi = (m i)⁻¹ *
        (∏ j ∈ Finset.univ.erase i, Real.exp (phi j (xi j)) / m j)) ∧
      P.tilted Sminus = H ∧ IsProbabilityMeasure H ∧
      Q = ENNReal.ofReal ((m i)⁻¹) • H ∧
      IsFiniteMeasure Q ∧ Q Set.univ = ENNReal.ofReal ((m i)⁻¹) ∧
      Integrable R P ∧ (∫ xi, R xi ∂P) = (m i)⁻¹ ∧
      (∀ f : (Fin n → Ω) → ℝ, Integrable f H →
        Integrable (fun xi => R xi * |f xi|) P ∧
        (∫ xi, R xi * |f xi| ∂P) =
          (m i)⁻¹ * (∫ xi, |f xi| ∂H) ∧
        Integrable (fun xi => R xi * f xi) P ∧
        Integrable f Q ∧
        (∫ xi, R xi * f xi ∂P) =
          (m i)⁻¹ * (∫ xi, f xi ∂H) ∧
        (∫ xi, f xi ∂Q) = (m i)⁻¹ * (∫ xi, f xi ∂H))

theorem actual_quadratic_partial_source_transport
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun z : Ω × Ω => h z.1 z.2))
    (hh2 : MemLp (fun z : Ω × Ω => h z.1 z.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ z : Ω × Ω, h z.1 z.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (n : ℕ) (hn : 3 ≤ n) (i : Fin n)
    (x : ℝ) (hx : 0 ≤ x)
    (hwindow : x ≤ Real.sqrt (n : ℝ) /
      (2 * Real.exp (1 / 2 : ℝ))) :
    let C : ℝ := Real.exp (1 / 2 : ℝ)
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let a : ℝ := x / Real.sqrt (n : ℝ)
    let φ : Ω → ℝ := fun o => a * g o - (a * g o) ^ 2 / 2
    let w : Ω → ℝ := fun o => Real.exp (φ o)
    let m : ℝ := ∫ o, w o ∂μ
    let L : Ω → ℝ := fun o => w o / m
    let ρ : Measure Ω :=
      μ.withDensity (fun o => ENNReal.ofReal (L o))
    let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let Sminus : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ j ∈ Finset.univ.erase i, φ (ξ j)
    let I : ℝ := m ^ n
    let R : (Fin n → Ω) → ℝ := fun ξ => Real.exp (Sminus ξ) / I
    let H : Measure (Fin n → Ω) := Measure.pi
      (fun j : Fin n => if j = i then μ else ρ)
    let Q : Measure (Fin n → Ω) :=
      P₀.withDensity (fun ξ => ENNReal.ofReal (R ξ))
    let cap : (Fin n → Ω) → ℝ := fun ξ => min |a * g (ξ i)| 1
    let e : (Fin n → Ω) → Fin n → Fin n → ℝ :=
      fun ξ j k => r (ξ j) (ξ k)
    let F : (Fin n → Ω) → ℝ := fun ξ =>
      Shao.OQ5.P35.unorderedPairSum (e ξ)
    let Fdel : (Fin n → Ω) → ℝ := fun ξ =>
      Shao.OQ5.P35.unorderedPairSum
        (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i)
    let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
      Shao.OQ6.ResidualDeletion.rowSum (e ξ) j
    let ψdel : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
      Shao.OQ6.ResidualDeletion.rowSum
        (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i) j
    let Λsq : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ j : Fin n, ψ ξ j ^ 2
    let Λdelsq : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ j : Fin n, ψdel ξ j ^ 2
    let D₁ : (Fin n → Ω) → ℝ := fun ξ =>
      F ξ / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
    let D₁del : (Fin n → Ω) → ℝ := fun ξ =>
      Fdel ξ / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
    let cross : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ j ∈ Finset.univ.erase i,
        2 * r (ξ i) (ξ j) * (ψ ξ j - r (ξ i) (ξ j))
    Integrable w μ ∧ (1 / 2 : ℝ) ≤ m ∧ m ≤ (3 / 2 : ℝ) ∧
      0 < m ∧ 0 < I ∧ 0 < m⁻¹ ∧ m⁻¹ ≤ 2 ∧
      μ.tilted φ = ρ ∧ IsProbabilityMeasure ρ ∧
      (∫ ξ, Real.exp (∑ j : Fin n, φ (ξ j)) ∂P₀) = I ∧
      Integrable (fun ξ => Real.exp (Sminus ξ)) P₀ ∧
      (∫ ξ, Real.exp (Sminus ξ) ∂P₀) = m ^ (n - 1) ∧
      (∀ ξ, R ξ = m⁻¹ *
        (∏ j ∈ Finset.univ.erase i, L (ξ j))) ∧
      P₀.tilted Sminus = H ∧ IsProbabilityMeasure H ∧
      H = P₀.withDensity
        (fun ξ => ENNReal.ofReal
          (∏ j ∈ Finset.univ.erase i, L (ξ j))) ∧
      Q = ENNReal.ofReal (m⁻¹) • H ∧
      IsFiniteMeasure Q ∧ Q Set.univ = ENNReal.ofReal (m⁻¹) ∧
      (∀ ξ, 0 < R ξ ∧ R ξ ≤ 2 * (2 * C) ^ (n - 1)) ∧
      (∀ j k : Fin n, j ≠ k →
        MemLp (fun ξ => r (ξ j) (ξ k)) 2 H) ∧
      Integrable (fun ξ => D₁ ξ - D₁del ξ) H ∧
      Integrable (fun ξ => Λsq ξ - Λdelsq ξ) H ∧
      Integrable cross H ∧
      (∀ f : (Fin n → Ω) → ℝ, Integrable f H →
        Integrable (fun ξ => R ξ * cap ξ * |f ξ|) P₀ ∧
        (∫ ξ, R ξ * cap ξ * |f ξ| ∂P₀) =
          m⁻¹ * (∫ ξ, cap ξ * |f ξ| ∂H) ∧
        (∫ ξ, R ξ * cap ξ * |f ξ| ∂P₀) ≤
          2 * (∫ ξ, |f ξ| ∂H) ∧
        Integrable (fun ξ => R ξ * cap ξ * f ξ) P₀ ∧
        Integrable (fun ξ => cap ξ * f ξ) Q ∧
        (∫ ξ, R ξ * cap ξ * f ξ ∂P₀) =
          m⁻¹ * (∫ ξ, cap ξ * f ξ ∂H) ∧
        (∫ ξ, cap ξ * f ξ ∂Q) =
          m⁻¹ * (∫ ξ, cap ξ * f ξ ∂H))

end

end Shao.OQ6.PartialObservationTilt
~~~
