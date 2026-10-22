# Frozen catalogs — actual iid/event/conditional law

ACCEPTED FROZEN CATALOGS. Authoritative original freezes immutable; exactcatalog copies, not proof-gate claims.

## Unit56

Freeze SHA256 8874ca2628c7e39fa56c9326fa4957f6e1fafdb35d332ff74e2e880611d9ecbe.

```lean
import Shao.OQ5.P52.FixedLayerModel
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

def fixedSampleLaw : Measure (ℕ → LayerObs) :=
  Measure.infinitePi (fun _ : ℕ => fixedObservationLaw)

def fixedSampleCoordinate (i : ℕ) (ω : ℕ → LayerObs) : LayerObs := ω i

theorem fixedSampleLaw_isProbabilityMeasure :
    IsProbabilityMeasure fixedSampleLaw

theorem measurable_fixedSampleCoordinate (i : ℕ) :
    Measurable (fixedSampleCoordinate i)

theorem map_fixedSampleCoordinate (i : ℕ) :
    fixedSampleLaw.map (fixedSampleCoordinate i) = fixedObservationLaw

theorem iIndepFun_fixedSampleCoordinate :
    ProbabilityTheory.iIndepFun fixedSampleCoordinate fixedSampleLaw

theorem map_fixedSampleCoordinate_pair (i j : ℕ) (hij : i ≠ j) :
    fixedSampleLaw.map (fun ω => (fixedSampleCoordinate i ω, fixedSampleCoordinate j ω)) =
      fixedObservationLaw.prod fixedObservationLaw

theorem map_fixedSamplePrefix (n : ℕ) :
    fixedSampleLaw.map (fun ω (i : Fin n) => fixedSampleCoordinate i.val ω) =
      Measure.pi (fun _ : Fin n => fixedObservationLaw)

end
end Shao.OQ5.P52
```

## Unit57

Freeze SHA256 60cfa68d062d3e6f41c59f2d50c9f959a57b73755695ba17863dba253fafc12f.

```lean
import Shao.OQ5.P52.FixedLayerSample
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

open MeasureTheory ProbabilityTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

def fixedSampleCategory (j i : ℕ) (ω : ℕ → LayerObs) : Fin 3 :=
  (fixedSampleCoordinate i ω).2 j

def fixedLayerPositionEvent (j n : ℕ) (J : Finset (Fin n)) : Set (ℕ → LayerObs) :=
  {ω | ∀ i : Fin n, if i ∈ J then fixedSampleCategory j i.val ω = 1
    else fixedSampleCategory j i.val ω = 0}

def fixedLayerExactEvent (j n K : ℕ) : Set (ℕ → LayerObs) :=
  {ω | (Finset.univ.filter (fun i : Fin n => fixedSampleCategory j i.val ω = 1)).card = K ∧
    ∀ i : Fin n, fixedSampleCategory j i.val ω = 0 ∨ fixedSampleCategory j i.val ω = 1}

def fixedLayerRareEvent (j : ℕ) : Set (ℕ → LayerObs) :=
  fixedLayerExactEvent j (fixedLayerN j) 2

theorem measurable_fixedSampleCategory (j i : ℕ) :
    Measurable (fixedSampleCategory j i)

theorem map_fixedSampleCategory (j i : ℕ) :
    fixedSampleLaw.map (fixedSampleCategory j i) =
      Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j)

theorem iIndepFun_fixedSampleCategory (j : ℕ) :
    iIndepFun (fixedSampleCategory j) fixedSampleLaw

theorem measurableSet_fixedLayerPositionEvent (j n : ℕ) (J : Finset (Fin n)) :
    MeasurableSet (fixedLayerPositionEvent j n J)

theorem fixedLayerPositionEvent_probability (j n : ℕ) (J : Finset (Fin n)) :
    fixedSampleLaw.real (fixedLayerPositionEvent j n J) =
      (fixedLayerP j) ^ J.card * (1 - fixedLayerP j - fixedLayerQ j) ^ (n - J.card)

theorem fixedLayerExactEvent_eq_biUnion (j n K : ℕ) :
    fixedLayerExactEvent j n K =
      ⋃ J ∈ (Finset.univ : Finset (Fin n)).powersetCard K, fixedLayerPositionEvent j n J

theorem measurableSet_fixedLayerExactEvent (j n K : ℕ) :
    MeasurableSet (fixedLayerExactEvent j n K)

theorem fixedLayerPositionEvent_disjoint (j n : ℕ) (J J' : Finset (Fin n))
    (hJJ : J ≠ J') :
    Disjoint (fixedLayerPositionEvent j n J) (fixedLayerPositionEvent j n J')

theorem fixedLayerExactEvent_probability (j n K : ℕ) (hK : K ≤ n) :
    fixedSampleLaw.real (fixedLayerExactEvent j n K) =
      (n.choose K : ℝ) * (fixedLayerP j) ^ K *
        (1 - fixedLayerP j - fixedLayerQ j) ^ (n - K)

theorem fixedLayerRareEvent_probability (j : ℕ) :
    fixedSampleLaw.real (fixedLayerRareEvent j) =
      ((fixedLayerN j).choose 2 : ℝ) * (fixedLayerP j) ^ 2 *
        (1 - fixedLayerP j - fixedLayerQ j) ^ (fixedLayerN j - 2)

theorem fixedLayerRareEvent_probability_pos (j : ℕ) :
    0 < fixedSampleLaw.real (fixedLayerRareEvent j)

end
end Shao.OQ5.P52
```

## Unit58

Freeze SHA256 c7a8cc33145287ecfb6e22f1838a4e3cc606572fbbe2ecf078b34d9425bd11dc.

```lean
import Shao.OQ5.P52.FixedLayerRareEvents
import Shao.Probability.ConditionalIID

open MeasureTheory ProbabilityTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

theorem fixedLayerPositionEvent_probability_pos (j n : ℕ) (J : Finset (Fin n)) :
    0 < fixedSampleLaw.real (fixedLayerPositionEvent j n J)

theorem fixedLayerPositionEvent_cond_isProbabilityMeasure
    (j n : ℕ) (J : Finset (Fin n)) :
    IsProbabilityMeasure (ProbabilityTheory.cond fixedSampleLaw (fixedLayerPositionEvent j n J))

theorem map_fixedLayerPositionEvent_cond_prefix
    (j n : ℕ) (J : Finset (Fin n)) :
    (ProbabilityTheory.cond fixedSampleLaw (fixedLayerPositionEvent j n J)).map
      (fun ω (i : Fin n) => fixedSampleCoordinate i.val ω) =
      Measure.pi (fun i : Fin n =>
        if i ∈ J then ProbabilityTheory.cond fixedObservationLaw {o : LayerObs | o.2 j = 1}
        else ProbabilityTheory.cond fixedObservationLaw {o : LayerObs | o.2 j = 0})

end
end Shao.OQ5.P52
```
