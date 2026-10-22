# Frozen public declarations: layer laws and fixed p52 growth

Original source p50.md SHA de553dc827eeadbc1e863c1778caa9bdeb00bca84110b4666b06cab053d7b768 and p52.md SHA 615209f8501e14a6bfaee220899c30891510fef5987c9abf7f74ac52b6538b45. Exact unit freezes:37 SHA1d811ab9ceee29788af2463752060d2be027a3ff9e58f3a8f7651b89fbff8455;38 SHA2124fe1714baec8054992d8d4567ebe992de79f48f8293354c4b4a4b5f579d9a;39 SHA142158a815ecd7924ae52932977baf1b95a9d2c3077adc15bbef834c35319e6a;40 SHA34212c96d86ae7a69f0f05e5647107fab2f4289eeb3a44d31a57145f86597ebc. The following exact catalogs omit proofs and retain every definition/type/premise. They do not imply acceptance before the independent gates summarized by the review document.
## Unit37

```lean
import Shao.OQ5.P50.ThreeStateLayer
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped BigOperators

namespace Shao.OQ5.P50

noncomputable section

/-- The actual three-state atomic law with the existing source weights. -/
def layerMeasure (p q : ℝ) : Measure (Fin 3) :=
  Measure.sum fun a : Fin 3 => ENNReal.ofReal (layerWeight p q a) • Measure.dirac a

theorem layerMeasure_isProbabilityMeasure (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q ≤ 1) :
    IsProbabilityMeasure (layerMeasure p q)

theorem layerMeasure_singleton (p q : ℝ) (a : Fin 3) :
    layerMeasure p q {a} = ENNReal.ofReal (layerWeight p q a)

theorem integrable_layerMeasure (p q : ℝ) (f : Fin 3 → ℝ) :
    Integrable f (layerMeasure p q)

theorem integral_layerMeasure (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q ≤ 1) (f : Fin 3 → ℝ) :
    (∫ a, f a ∂layerMeasure p q) = ∑ a : Fin 3, layerWeight p q a * f a

theorem integrable_layerMeasure_prod (p q : ℝ) (F : Fin 3 × Fin 3 → ℝ) :
    Integrable F ((layerMeasure p q).prod (layerMeasure p q))

theorem integral_layerMeasure_prod (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q ≤ 1) (F : Fin 3 × Fin 3 → ℝ) :
    (∫ z, F z ∂(layerMeasure p q).prod (layerMeasure p q)) =
      ∑ a : Fin 3, ∑ b : Fin 3,
        layerWeight p q a * layerWeight p q b * F (a, b)

theorem integral_layerKernel_row_zero (N : ℕ) (t p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q ≤ 1) (hqnz : q ≠ 0) (a : Fin 3) :
    (∫ b, layerKernel N t p q a b ∂layerMeasure p q) = 0

theorem layerKernel_memLp_two (N : ℕ) (t p q : ℝ) :
    MemLp (fun z : Fin 3 × Fin 3 => layerKernel N t p q z.1 z.2) 2
      ((layerMeasure p q).prod (layerMeasure p q))

end
end Shao.OQ5.P50
```

## Unit38

```lean
import Shao.OQ5.P50.ThreeStateLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory

namespace Shao.OQ5.P50

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

/-- Actual uniform law on the interval [-1,1]. -/
def layerNoiseLaw : Measure ℝ :=
  ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)

/-- The full countable product of the actual three-state source marginals. -/
def layerCategoryProductLaw (p q : ℕ → ℝ) : Measure (ℕ → Fin 3) :=
  Measure.infinitePi (fun j : ℕ => layerMeasure (p j) (q j))

/-- The entire observation law, with independent G and all categorical layers. -/
def layerObservationLaw (p q : ℕ → ℝ) : Measure LayerObs :=
  layerNoiseLaw.prod (layerCategoryProductLaw p q)

theorem layerNoiseLaw_isProbabilityMeasure : IsProbabilityMeasure layerNoiseLaw

theorem layerNoiseLaw_ae_mem :
    ∀ᵐ g ∂layerNoiseLaw, g ∈ Set.Icc (-1 : ℝ) 1

theorem layerCategoryProductLaw_isProbabilityMeasure (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1) :
    IsProbabilityMeasure (layerCategoryProductLaw p q)

theorem layerObservationLaw_isProbabilityMeasure (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1) :
    IsProbabilityMeasure (layerObservationLaw p q)

theorem map_layerObservation_first (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1) :
    (layerObservationLaw p q).map Prod.fst = layerNoiseLaw

theorem map_layerObservation_categories (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1) :
    (layerObservationLaw p q).map Prod.snd = layerCategoryProductLaw p q

theorem map_layerObservation_category (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1) (j : ℕ) :
    (layerObservationLaw p q).map (fun o => o.2 j) = layerMeasure (p j) (q j)

theorem layerObservation_first_ae_mem (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1) :
    ∀ᵐ o ∂layerObservationLaw p q, o.1 ∈ Set.Icc (-1 : ℝ) 1

theorem layerObservation_first_indep_categories (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1) :
    ProbabilityTheory.IndepFun Prod.fst Prod.snd (layerObservationLaw p q)

theorem iIndepFun_layerObservation_categories (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1) :
    ProbabilityTheory.iIndepFun (fun j (o : LayerObs) => o.2 j) (layerObservationLaw p q)

theorem map_layerObservation_category_pair (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1)
    (i j : ℕ) (hij : i ≠ j) :
    (layerObservationLaw p q).map (fun o => (o.2 i, o.2 j)) =
      (layerMeasure (p i) (q i)).prod (layerMeasure (p j) (q j))

theorem map_layerObservation_category_restrict (p q : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hpq : ∀ j, p j + q j ≤ 1)
    (J : Finset ℕ) :
    (layerObservationLaw p q).map (fun o (j : J) => o.2 j) =
      Measure.pi (fun j : J => layerMeasure (p j) (q j))

end
end Shao.OQ5.P50
```

## Unit39

```lean
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Shao.OQ5.P52

noncomputable section

/-- Source N_J with J=j+6, fixed independently of exponents and sample sizes. -/
def fixedLayerN (j : ℕ) : ℕ := 2 ^ (3 * (j + 6) ^ 3)

/-- The exact dyadic source amplitude. -/
def fixedLayerT (j : ℕ) : ℝ := (2 : ℝ) ^ (2 * (j + 6) ^ 3)

def fixedLayerC (j : ℕ) : ℝ := 1 + 1 / ((j + 6 : ℕ) : ℝ)

def fixedLayerTau (j : ℕ) : ℝ := 1 / 3 - 1 / ((j + 6 : ℕ) : ℝ)

def fixedLayerP (j : ℕ) : ℝ :=
  Real.exp (-((fixedLayerN j : ℝ) ^ fixedLayerTau j))

def fixedLayerQ (j : ℕ) : ℝ := (fixedLayerN j : ℝ) ^ (-fixedLayerC j)

theorem fixedLayerN_ge_eight (j : ℕ) : 8 ≤ fixedLayerN j

theorem fixedLayerT_pos (j : ℕ) : 0 < fixedLayerT j

theorem fixedLayerC_bounds (j : ℕ) :
    1 < fixedLayerC j ∧ fixedLayerC j ≤ 7 / 6

theorem fixedLayerTau_bounds (j : ℕ) :
    1 / 6 ≤ fixedLayerTau j ∧ fixedLayerTau j < 1 / 3

theorem fixedLayerP_bounds (j : ℕ) :
    0 < fixedLayerP j ∧ fixedLayerP j < 1 / 2

theorem fixedLayerQ_bounds (j : ℕ) :
    0 < fixedLayerQ j ∧ fixedLayerQ j < 1 / 8

theorem fixedLayerP_add_Q_lt_one (j : ℕ) :
    fixedLayerP j + fixedLayerQ j < 1

theorem fixedLayerT_eq_rpow_N (j : ℕ) :
    fixedLayerT j = (fixedLayerN j : ℝ) ^ (2 / 3 : ℝ)

end
end Shao.OQ5.P52
```

## Unit40

```lean
import Shao.OQ5.P52.FixedLayerCoefficients

open Filter
open scoped Topology

namespace Shao.OQ5.P52

noncomputable section

theorem strictMono_fixedLayerN : StrictMono fixedLayerN

theorem fixedLayerN_tendsto : Tendsto fixedLayerN atTop atTop

theorem fixedLayerC_tendsto : Tendsto fixedLayerC atTop (nhds 1)

theorem fixedLayerTau_tendsto : Tendsto fixedLayerTau atTop (nhds (1 / 3))

theorem fixedLayer_log_N (j : ℕ) :
    Real.log (fixedLayerN j : ℝ) =
      3 * (((j + 6 : ℕ) : ℝ) ^ 3) * Real.log 2

theorem fixedLayerN_rpow_tau (j : ℕ) :
    (fixedLayerN j : ℝ) ^ fixedLayerTau j =
      (2 : ℝ) ^ ((j + 6) ^ 2 * (j + 3))

theorem fixedLayerN_rpow_neg_inv (j : ℕ) :
    (fixedLayerN j : ℝ) ^ (-1 / ((j + 6 : ℕ) : ℝ)) =
      (2 : ℝ) ^ (-3 * (((j + 6 : ℕ) : ℝ) ^ 2))

theorem fixedLayer_exponent_gap (η : ℝ) (hη0 : 0 < η) (hη : η < 1 / 5) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ j in atTop,
      δ ≤ fixedLayerTau j - η * (fixedLayerC j + 2 / 3) ∧
      δ ≤ fixedLayerTau j - 5 * η / 3 ∧
      δ ≤ fixedLayerTau j - 2 * η / 3

theorem fixedLayer_log_cost_tendsto_zero :
    Tendsto (fun j : ℕ =>
      (fixedLayerN j : ℝ) ^ (-1 / ((j + 6 : ℕ) : ℝ)) *
        (Real.log (fixedLayerN j : ℝ)) ^ 2) atTop (nhds 0)

end
end Shao.OQ5.P52
```
