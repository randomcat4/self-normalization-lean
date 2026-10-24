# OQ6 exact frozen row/deletion and observation-tilt contracts

Five source-bound modules, ten public theorem types and two public definitions. These contracts were frozen before implementation. This document records exact statement scope; individual qualification is bound separately in server-checks.json and proof-review.md. All original p53/OQ6/RS2 roots remain OPEN. Shao–Zhou attribution and the later partial m_i^-1 factor remain explicit obligations.

<!-- unit131 frozen JSON SHA256 eabfff97d7575f664c8e8a8554fb8c87b8e66d648c2487420c85361622407964; frozen MD SHA256 7bf371e2f88fc0c707a860a1988d7efb23fcb71761310f48ba9ef81e78374753 -->

# Unit131 frozen source declaration

Frozen beforeimplementation. Module `Shao.OQ6.ResidualRowExpansion`, namespace `Shao.OQ6.FiniteRows`; soleimport `Shao.OQ6.FiniteRows`. No public definition; exactly one public theorem.

The actual uncentered row square for H_ij=g_i+g_j+r_ij satisfies the full originalp39(4) expansion afterclearing the projectionenergy division. n≥3; g arbitraryreal vector; r symmetric with arbitrary diagonal. S andQ are actualfullsample sums; psi excludesdiagonal; F countsunorderedpairs once. Bothmixedterms are retained. No samplecentering, canonicaldegeneracy, iid/moment/tail/RS conclusion is assumed. The identity holds at Q=0/R=0; quotientD2requiresseparateV>0.

```lean
theorem uncenteredSq_sub_projectionSq_expansion
    {n : ℕ} (g : Fin n → ℝ) (r : Fin n → Fin n → ℝ)
    (hr : ∀ i j, r i j = r j i) (hn : 3 ≤ n) :
    let psi : Fin n → ℝ := fun i =>
      ∑ j ∈ Finset.univ.erase i, r i j
    let S : ℝ := ∑ i : Fin n, g i
    let Q : ℝ := ∑ i : Fin n, g i ^ 2
    let F : ℝ := Shao.OQ5.P35.unorderedPairSum r
    ((n : ℝ) - 1) *
        (Shao.OQ6.FiniteRows.uncenteredSq
          (fun i j => g i + g j + r i j) - Q / (n : ℝ)) =
      Q / (n : ℝ) +
        ((3 * (n : ℝ) - 4) / ((n : ℝ) - 2) ^ 2) * S ^ 2 +
        (2 / ((n : ℝ) - 2)) * (∑ i : Fin n, g i * psi i) +
        (4 / ((n : ℝ) - 2) ^ 2) * S * F +
        (∑ i : Fin n, psi i ^ 2) / ((n : ℝ) - 2) ^ 2
```

Author mayuseprivateproofhelpers; all public header/assumptions fixed. No sorry/admit/newaxiom/unsafe/native_decide; no extra publicdeclarations or imports withoutleadreview. Existingaccepted FiniteRows is read-only andisnotrecompiledforthisunit.

Directconsumer: p39equation4 then actualG-envelope, deletedrow/costchain. Thisfinitealgebra doesnotcloseOQ6/RS2 oranyoriginalroot. No probability/normal-tail/zero-denominator eventconversion is paidhere.

Localimplementation only; nextsource-bound fullindependentreview then exactserversource/object/actualowned&transitiveaxiomgates arerequired. Rootaloneintegrates.


---

<!-- unit132 frozen JSON SHA256 7fa0394497c4f415ace4559add8425891829766c6b6791d29b9451bbfdcd5f76; frozen MD SHA256 edb74e16dc475ba88cda951d5584b7d5a6ce87b42165a142839c6d47b6cdea77 -->

# Unit132 frozen declarations

FROZEN_BEFORE_IMPLEMENTATION. Two concrete definitions and three theorem types form one source-bound deletion unit. Server Lean is not yet authorized. The author must never be final reviewer.

Source p39:129–151 and p38:68 retains original n and all cross terms; no positivity or diagonal-zero premise is added.

```lean
import Shao.OQ5.P35.RowIdentity

set_option autoImplicit false

namespace Shao.OQ6.ResidualDeletion

noncomputable section

open scoped BigOperators

variable {n : ℕ}

def eraseIncident (r : Fin n → Fin n → ℝ) (i : Fin n) :
    Fin n → Fin n → ℝ :=
  fun j k => if j = i ∨ k = i then 0 else r j k

def rowSum (r : Fin n → Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ k ∈ Finset.univ.erase j, r j k

theorem rowSum_eraseIncident
    (r : Fin n → Fin n → ℝ) (i j : Fin n) :
    rowSum (eraseIncident r i) j =
      if j = i then 0 else rowSum r j - r j i

theorem unorderedPairSum_sub_eraseIncident
    (r : Fin n → Fin n → ℝ)
    (hr : ∀ j k, r j k = r k j) (i : Fin n) :
    Shao.OQ5.P35.unorderedPairSum r -
        Shao.OQ5.P35.unorderedPairSum (eraseIncident r i) =
      rowSum r i

theorem rowSqSum_sub_eraseIncident
    (r : Fin n → Fin n → ℝ)
    (hr : ∀ j k, r j k = r k j) (i : Fin n) :
    (∑ j : Fin n, rowSum r j ^ 2) -
        (∑ j : Fin n, rowSum (eraseIncident r i) j ^ 2) =
      rowSum r i ^ 2 +
        ∑ j ∈ Finset.univ.erase i,
          (2 * r i j * (rowSum r j - r i j) + r i j ^ 2)

end

end Shao.OQ6.ResidualDeletion
```

OQ6/RS2 remain OPEN.


---

<!-- unit133 frozen JSON SHA256 33c4b2ea7f31704fc8e2679520782f9a0bd2414cee8dea12c696c8159899de64; frozen MD SHA256 24547e7fc216eb4af56db8fd36134008bfe473e2cfcc3984f572646b738cbe10 -->

# Unit133 frozen declarations

FROZEN_BEFORE_IMPLEMENTATION; three public theorem types, zero public definitions. Sourcep38:68/p39:129–134; retain complete Ω-valued observations and originalFin n. Parent132 remains unqualified and must pass its own server/kernel/AX gates before any133servercheck.

```lean
import Shao.OQ6.ResidualDeletion
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

set_option autoImplicit false

universe u

namespace Shao.OQ6.ResidualDeletion

noncomputable section

open scoped BigOperators

variable {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}

theorem erasedSampleMatrix_measurable_factorization
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun p : Ω × Ω => r p.1 p.2)) (i : Fin n) :
    ∃ Φ : ({j : Fin n // j ≠ i} → Ω) → (Fin n → Fin n → ℝ),
      Measurable Φ ∧
        ∀ ξ : Fin n → Ω,
          eraseIncident (fun j k => r (ξ j) (ξ k)) i =
            Φ (fun j => ξ j.val)

theorem erasedSamplePairSum_measurable_factorization
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun p : Ω × Ω => r p.1 p.2)) (i : Fin n) :
    ∃ F : ({j : Fin n // j ≠ i} → Ω) → ℝ,
      Measurable F ∧
        ∀ ξ : Fin n → Ω,
          Shao.OQ5.P35.unorderedPairSum
            (eraseIncident (fun j k => r (ξ j) (ξ k)) i) =
              F (fun j => ξ j.val)

theorem erasedSampleRowSqSum_measurable_factorization
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun p : Ω × Ω => r p.1 p.2)) (i : Fin n) :
    ∃ Λ : ({j : Fin n // j ≠ i} → Ω) → ℝ,
      Measurable Λ ∧
        ∀ ξ : Fin n → Ω,
          (∑ j : Fin n,
            rowSum (eraseIncident (fun j k => r (ξ j) (ξ k)) i) j ^ 2) =
              Λ (fun j => ξ j.val)

end

end Shao.OQ6.ResidualDeletion
```

No probability/integrability or root closure is claimed.


---

<!-- unit134 frozen JSON SHA256 c63d7cd6c9a7bb03212d3619575b7744dcb4b0a99fbaf4616934fe0c1425f9e7; frozen MD SHA256 49b839ac411a3d32e36a80fb5de7402fa438e0f53b5641a530063b5dd1133792 -->

# Unit134 frozen exact interface

Frozen before implementation. Zero public definitions and two public theorem types. Source: original p39 lines109–127 equation(8), Shao–Zhou context retained. The actual observation space/probability, genuine MemLp g2, actual secondmoment1, actual normalization integral and literal Mathlib tilted law are preserved. No boundedness or exponential-moment condition on g is added. All full/partial product laws (including extra m^-1), residual overlap/cross costs and original roots remain OPEN.

```lean
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

universe u

namespace Shao.OQ6.QuadraticTilt

noncomputable section

open MeasureTheory ProbabilityTheory

theorem weight_bounds (u v : ℝ) :
    0 < Real.exp (u - u ^ 2 / 2) ∧
      Real.exp (u - u ^ 2 / 2) ≤ Real.exp (1 / 2 : ℝ) ∧
        |Real.exp (u - u ^ 2 / 2) - Real.exp (v - v ^ 2 / 2)| ≤
          Real.exp (1 / 2 : ℝ) * |u - v|

theorem normalizer_density_L2
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgsecond : (∫ ω, g ω ^ 2 ∂μ) = 1)
    (a : ℝ) (ha : |a| ≤ (2 * Real.exp (1 / 2 : ℝ))⁻¹) :
    let w : Ω → ℝ := fun ω => Real.exp (a * g ω - (a * g ω) ^ 2 / 2)
    let m : ℝ := ∫ ω, w ω ∂μ
    let L : Ω → ℝ := fun ω => w ω / m
    Integrable w μ ∧
      (1 / 2 : ℝ) ≤ m ∧ m ≤ (3 / 2 : ℝ) ∧
        Measurable L ∧ Integrable L μ ∧
          (∀ ω, 0 < L ω ∧ L ω ≤ 2 * Real.exp (1 / 2 : ℝ)) ∧
            (∫ ω, L ω ∂μ) = 1 ∧
              IsProbabilityMeasure (μ.tilted
                (fun ω => a * g ω - (a * g ω) ^ 2 / 2)) ∧
                Integrable (fun ω => (L ω - 1) ^ 2) μ ∧
                  (∫ ω, (L ω - 1) ^ 2 ∂μ) ≤
                    4 * (Real.exp (1 / 2 : ℝ)) ^ 2 * a ^ 2

end

end Shao.OQ6.QuadraticTilt
```

Candidate proof and exact source binding: f9df6cf684fac966a3c0769fc1f767e933f8e8ed8aea75d43186d682a8e7ec78. Pinned MeanValue source SHA 0f10e5afeb80809192b023486b09e98939d0a6bd0920ab3882bddb41a715d947. No source implementation or Lean check has occurred. Authors cannot be final reviewers.


---

<!-- unit135 frozen JSON SHA256 f0b9fdac4b2667410efeb4d2c9d1d05df312ad5c4208f9182b2fc57046478c1c; frozen MD SHA256 41754c4124d19d4dbf9656026673877314fcc0ee85f232ff55380111f93283b2 -->

# Unit135 exact frozen product-law contract

Frozen before implementation: zero public definitions, one full public theorem type. Source p37 section6/equation17 and p39 actual full/partial observation law. Full observations on arbitrary common Ω are retained; actual normalizers and genuine exp-integrability are explicit. No MGF-domain, bounded-g, measurable-φ or desiredlawidentity premise is added. The partial expectation m_i^-1 factor and actual cost/integrability estimates remain separate later consumers. Allroots OPEN.

```lean
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false

namespace Shao.OQ6

noncomputable section

open MeasureTheory
open scoped BigOperators

theorem finite_observation_product_tilt
    {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (mu : Fin n → Measure Ω)
    [∀ j : Fin n, IsProbabilityMeasure (mu j)]
    (phi : Fin n → Ω → ℝ)
    (hExp : ∀ j : Fin n,
      Integrable (fun o : Ω => Real.exp (phi j o)) (mu j)) :
    let S : (Fin n → Ω) → ℝ := fun xi =>
      ∑ j : Fin n, phi j (xi j)
    let m : Fin n → ℝ := fun j =>
      ∫ o : Ω, Real.exp (phi j o) ∂(mu j)
    let P : Measure (Fin n → Ω) := Measure.pi mu
    Integrable (fun xi => Real.exp (S xi)) P ∧
      (∫ xi : Fin n → Ω, Real.exp (S xi) ∂P) =
        (∏ j : Fin n, m j) ∧
      0 < (∫ xi : Fin n → Ω, Real.exp (S xi) ∂P) ∧
      P.tilted S =
        Measure.pi (fun j : Fin n => (mu j).tilted (phi j))

end

end Shao.OQ6
```

No implementation/kernel/axiom acceptance exists at this freeze. Generic API instantiations remain explicit server obligations; no silent premise change is permitted.
