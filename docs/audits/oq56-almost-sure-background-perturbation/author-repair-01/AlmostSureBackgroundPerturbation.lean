import Shao.OQ5.P41.FiniteBackgroundPerturbation
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

set_option autoImplicit false

universe u

namespace Shao.OQ5.P41.AlmostSureBackgroundPerturbation

noncomputable section

open MeasureTheory ProbabilityTheory
open Shao.OQ5.P41.FiniteBackgroundPerturbation
open scoped BigOperators

def sampleEnvelopeEvent (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (w : Ω → ℝ) : Set (Fin n → Ω) :=
  {x | (∀ i : Fin n, 0 ≤ w (x i)) ∧
    (∀ i j : Fin n, i ≠ j → |r (x i) (x j)| ≤ w (x i) * w (x j))}

def sampleBackgroundBounds (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (w : Ω → ℝ) (x : Fin n → Ω) : Prop :=
  ∀ (v : Fin n → ℝ) (B : Finset (Fin n)),
    |blockPairSum (anomaly B) (fun i j : Fin n => r (x i) (x j))| ≤
        (anomalyWeight B (fun i : Fin n => w (x i))) ^ (2 : ℕ) / 2 ∧
    (4 ≤ n →
      (∀ i : Fin n, i ∈ B →
        |adjustedRow v (fun a b : Fin n => r (x a) (x b)) i -
          backgroundRow B v (fun a b : Fin n => r (x a) (x b)) i| ≤
          anomalyWeight B (fun a : Fin n => w (x a)) * w (x i) /
            ((n : ℝ) - 2)) ∧
      (3 ≤ B.card →
        |Real.sqrt (blockCenteredEnergy B
            (adjustedRow v (fun a b : Fin n => r (x a) (x b)))) -
          Real.sqrt ((B.card : ℝ) - 1) *
            backgroundStudentizer B v (fun a b : Fin n => r (x a) (x b))| ≤
          anomalyWeight B (fun a : Fin n => w (x a)) *
            Real.sqrt (backgroundWeightEnergy B (fun a : Fin n => w (x a))) /
              ((n : ℝ) - 2)))

private theorem coordinatePair_measurePreserving (n : ℕ) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (i j : Fin n) (hij : i ≠ j) :
    MeasurePreserving (fun x : Fin n → Ω => (x i, x j))
      (Measure.pi (fun _ : Fin n => μ)) (μ.prod μ)
:= by
  have hind : iIndepFun
      (fun (k : Fin n) (x : Fin n → Ω) => x k)
      (Measure.pi (fun _ : Fin n => μ)) :=
    iIndepFun_pi (μ := fun _ : Fin n => μ)
      (X := fun _ (o : Ω) => o) (fun _ => measurable_id.aemeasurable)
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
  have hmap := (hind.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  rw [(measurePreserving_eval (fun _ : Fin n => μ) i).map_eq,
    (measurePreserving_eval (fun _ : Fin n => μ) j).map_eq] at hmap
  exact hmap

theorem ae_sampleEnvelopeEvent (n : ℕ) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (r : Ω → Ω → ℝ) (w : Ω → ℝ)
    (hw : ∀ᵐ o : Ω ∂μ, 0 ≤ w o)
    (hr : ∀ᵐ p : Ω × Ω ∂μ.prod μ, |r p.1 p.2| ≤ w p.1 * w p.2) :
    ∀ᵐ x : Fin n → Ω ∂Measure.pi (fun _ : Fin n => μ),
      x ∈ sampleEnvelopeEvent n r w
:= by
  have hW (i : Fin n) :
      ∀ᵐ x : Fin n → Ω ∂Measure.pi (fun _ : Fin n => μ), 0 ≤ w (x i) :=
    (measurePreserving_eval (fun _ : Fin n => μ) i).quasiMeasurePreserving.ae hw
  have hR (i j : Fin n) :
      ∀ᵐ x : Fin n → Ω ∂Measure.pi (fun _ : Fin n => μ),
        i ≠ j → |r (x i) (x j)| ≤ w (x i) * w (x j) := by
    by_cases hij : i ≠ j
    · exact ((coordinatePair_measurePreserving n μ i j hij).quasiMeasurePreserving.ae hr).mono
        (fun x hx _ => hx)
    · exact Filter.Eventually.of_forall (fun x hne => False.elim (hij hne))
  have hWAll : ∀ᵐ x : Fin n → Ω ∂Measure.pi (fun _ : Fin n => μ),
      ∀ i : Fin n, 0 ≤ w (x i) :=
    Filter.eventually_all.2 hW
  have hRAll : ∀ᵐ x : Fin n → Ω ∂Measure.pi (fun _ : Fin n => μ),
      ∀ i j : Fin n, i ≠ j → |r (x i) (x j)| ≤ w (x i) * w (x j) :=
    Filter.eventually_all.2 (fun i => Filter.eventually_all.2 (fun j => hR i j))
  filter_upwards [hWAll, hRAll] with x hxW hxR
  exact ⟨hxW, hxR⟩

theorem measurableSet_sampleEnvelopeEvent (n : ℕ) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] (r : Ω → Ω → ℝ) (w : Ω → ℝ)
    (hr : Measurable (Function.uncurry r)) (hw : Measurable w) :
    MeasurableSet (sampleEnvelopeEvent n r w)
:= by
  classical
  have hpair (i j : Fin n) :
      Measurable (fun x : Fin n → Ω => (x i, x j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hrx (i j : Fin n) :
      Measurable (fun x : Fin n → Ω => r (x i) (x j)) := by
    exact Measurable.comp (g := Function.uncurry r)
      (f := fun x : Fin n → Ω => (x i, x j)) hr (hpair i j)
  have hwx (i : Fin n) :
      Measurable (fun x : Fin n → Ω => w (x i)) :=
    hw.comp (measurable_pi_apply i)
  change MeasurableSet
    ({x : Fin n → Ω | ∀ i : Fin n, 0 ≤ w (x i)} ∩
      {x : Fin n → Ω | ∀ i j : Fin n,
        i ≠ j → |r (x i) (x j)| ≤ w (x i) * w (x j)})
  apply MeasurableSet.inter
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_le measurable_const (hwx i)
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ =>
        measurableSet_le (hrx i j).abs ((hwx i).mul (hwx j))

theorem sampleEnvelopeEvent_probability_one (n : ℕ) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (r : Ω → Ω → ℝ) (w : Ω → ℝ)
    (hmr : Measurable (Function.uncurry r)) (hmw : Measurable w)
    (hw : ∀ᵐ o : Ω ∂μ, 0 ≤ w o)
    (hr : ∀ᵐ p : Ω × Ω ∂μ.prod μ, |r p.1 p.2| ≤ w p.1 * w p.2) :
    (Measure.pi (fun _ : Fin n => μ)) (sampleEnvelopeEvent n r w) = 1 ∧
      (Measure.pi (fun _ : Fin n => μ)).real (sampleEnvelopeEvent n r w) = 1
:= by
  have hE : (Measure.pi (fun _ : Fin n => μ)) (sampleEnvelopeEvent n r w) = 1 :=
    (mem_ae_iff_prob_eq_one
      (measurableSet_sampleEnvelopeEvent n r w hmr hmw)).mp
        (ae_sampleEnvelopeEvent n μ r w hw hr)
  refine ⟨hE, ?_⟩
  simp only [Measure.real, hE, ENNReal.toReal_one]

theorem backgroundBounds_of_mem_sampleEnvelopeEvent (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (w : Ω → ℝ) (x : Fin n → Ω)
    (hx : x ∈ sampleEnvelopeEvent n r w) :
    sampleBackgroundBounds n r w x
:= by
  change (∀ i : Fin n, 0 ≤ w (x i)) ∧
    (∀ i j : Fin n, i ≠ j → |r (x i) (x j)| ≤ w (x i) * w (x j)) at hx
  rcases hx with ⟨hxW, hxR⟩
  unfold sampleBackgroundBounds
  intro v B
  constructor
  · exact anomaly_pair_envelope_bound B
      (fun i j : Fin n => r (x i) (x j)) (fun i : Fin n => w (x i)) hxW hxR
  · intro hn
    constructor
    · intro i hi
      exact adjustedRow_sub_backgroundRow_bound B v
        (fun a b : Fin n => r (x a) (x b)) (fun a : Fin n => w (x a))
        hn hxW hxR i hi
    · intro hm
      exact background_centered_norm_perturbation B v
        (fun a b : Fin n => r (x a) (x b)) (fun a : Fin n => w (x a))
        hn hm hxW hxR

theorem ae_sampleBackgroundBounds (n : ℕ) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (r : Ω → Ω → ℝ) (w : Ω → ℝ)
    (hw : ∀ᵐ o : Ω ∂μ, 0 ≤ w o)
    (hr : ∀ᵐ p : Ω × Ω ∂μ.prod μ, |r p.1 p.2| ≤ w p.1 * w p.2) :
    ∀ᵐ x : Fin n → Ω ∂Measure.pi (fun _ : Fin n => μ),
      x ∈ sampleEnvelopeEvent n r w ∧ sampleBackgroundBounds n r w x
:= by
  filter_upwards [ae_sampleEnvelopeEvent n μ r w hw hr] with x hx
  exact ⟨hx, backgroundBounds_of_mem_sampleEnvelopeEvent n r w x hx⟩

end

end Shao.OQ5.P41.AlmostSureBackgroundPerturbation
