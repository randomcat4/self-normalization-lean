import Shao.C2.CompletedIntervalDerivative
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

noncomputable section
namespace Shao.C2.InteriorDerivativeMeasurability
open MeasureTheory Set Filter
open scoped Topology Classical
open Shao.C2.BridgeDomination Shao.C2.CompletionMeasurability
open Shao.C2.CompletedIntervalProcess Shao.C2.CompletedIntervalDerivative

def interiorSpatialDerivative (ν : Measure BridgeNoise) (a y T z : ℝ) : ℝ := by
  classical
  exact if 0 < T ∧ |y| < a ∧ |z| < a then spatialDerivative ν a y T z else 0

theorem measurable_interiorSpatialDerivative (ν : Measure BridgeNoise) [SFinite ν]
    (hRegular : ∀ a y T z : ℝ, 0 < a → 0 < T → |y| < a → |z| < a →
      HasDerivAt (fun u : ℝ => intervalCompletion ν a u T z) (spatialDerivative ν a y T z) y) :
    Measurable (fun p : CompletionParameters =>
      interiorSpatialDerivative ν p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let G : CompletionParameters → Prop := fun p =>
    0 < p.2.2.1 ∧ |p.2.1| < p.1 ∧ |p.2.2.2| < p.1
  have hG : MeasurableSet {p | G p} :=
    (measurableSet_lt measurable_const measurable_snd.snd.fst).inter
      ((measurableSet_lt (continuous_abs.measurable.comp measurable_snd.fst) measurable_fst).inter
        (measurableSet_lt (continuous_abs.measurable.comp measurable_snd.snd.snd) measurable_fst))
  let step : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  let f : ℕ → CompletionParameters → ℝ := fun k p =>
    if G p then (step k)⁻¹ *
      (intervalCompletion ν p.1 (p.2.1 + step k) p.2.2.1 p.2.2.2 -
        intervalCompletion ν p.1 p.2.1 p.2.2.1 p.2.2.2) else 0
  have hc := measurable_intervalCompletion_parameters ν
  have hf : ∀ k, Measurable (f k) := by
    intro k
    have hp : Measurable (fun p : CompletionParameters =>
        ((p.1, (p.2.1 + step k, (p.2.2.1, p.2.2.2))) : CompletionParameters)) :=
      measurable_fst.prodMk ((measurable_snd.fst.add measurable_const).prodMk
        (measurable_snd.snd.fst.prodMk measurable_snd.snd.snd))
    exact Measurable.ite hG (measurable_const.mul ((hc.comp hp).sub hc)) measurable_const
  have hstep : Tendsto step atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Eventually.of_forall (fun k => by
      change 0 < 1 / ((k : ℝ) + 1)
      positivity)
  have hlim : ∀ p : CompletionParameters,
      Tendsto (fun k => f k p) atTop
        (𝓝 (interiorSpatialDerivative ν p.1 p.2.1 p.2.2.1 p.2.2.2)) := by
    intro p
    by_cases hg : 0 < p.2.2.1 ∧ |p.2.1| < p.1 ∧ |p.2.2.2| < p.1
    · have ha : 0 < p.1 := (abs_nonneg p.2.1).trans_lt hg.2.1
      have hh := (hRegular _ _ _ _ ha hg.1 hg.2.1 hg.2.2).tendsto_slope_zero_right.comp hstep
      simpa only [f, G, interiorSpatialDerivative, _root_.if_pos hg, smul_eq_mul, Function.comp_def] using hh
    · simpa only [f, G, interiorSpatialDerivative, _root_.if_neg hg] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.2 hlim)

theorem completedDerivative_eq_interior (n : ℕ) (ν : Measure BridgeNoise)
    (x : ℝ) (z : Shao.Path n) (σ : Equiv.Perm (Fin n)) (r : Fin n) :
    completedDerivative ν x z σ r =
      if 0 < Shao.energy z ∧ strictLive x z σ r.val ∧
          |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z) then
        interiorSpatialDerivative ν (x * Real.sqrt (Shao.energy z))
          (Shao.prefixSum (fun i => z (σ i)) r.val)
          (Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) r.val)
          (Shao.prefixSum z n)
      else 0 := by
  by_cases hg : 0 < Shao.energy z ∧ strictLive x z σ r.val ∧
      |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z)
  · by_cases ht : 0 < Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) r.val
    · have hfull := And.intro hg.1 (And.intro hg.2.1 (And.intro hg.2.2 ht))
      have hi := And.intro ht (And.intro (hg.2.1 r.val le_rfl) hg.2.2)
      simp only [completedDerivative, interiorSpatialDerivative, if_pos hfull, if_pos hg, if_pos hi]
    · have hfull : ¬ (0 < Shao.energy z ∧ strictLive x z σ r.val ∧
          |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z) ∧
          0 < Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) r.val) :=
        fun h => ht h.2.2.2
      have hi : ¬ (0 < Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) r.val ∧
          |Shao.prefixSum (fun i => z (σ i)) r.val| < x * Real.sqrt (Shao.energy z) ∧
          |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z)) := fun h => ht h.1
      simp only [completedDerivative, interiorSpatialDerivative, if_neg hfull, if_pos hg, if_neg hi]
  · have hfull : ¬ (0 < Shao.energy z ∧ strictLive x z σ r.val ∧
        |Shao.prefixSum z n| < x * Real.sqrt (Shao.energy z) ∧
        0 < Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) r.val) :=
      fun h => hg ⟨h.1, h.2.1, h.2.2.1⟩
    simp only [completedDerivative, if_neg hfull, if_neg hg]

theorem measurable_completedDerivative_of_regular (n : ℕ)
    (ν : Measure BridgeNoise) [SFinite ν]
    (hRegular : ∀ a y T z : ℝ, 0 < a → 0 < T → |y| < a → |z| < a →
      HasDerivAt (fun u : ℝ => intervalCompletion ν a u T z) (spatialDerivative ν a y T z) y)
    (x : ℝ) (σ : Equiv.Perm (Fin n)) (r : Fin n) :
    Measurable (fun z : Shao.Path n => completedDerivative ν x z σ r) := by
  have hσ : Measurable (fun z : Shao.Path n => fun i => z (σ i)) :=
    Measurable.of_eval (fun i => measurable_pi_apply (σ i))
  have hy := (Shao.measurable_prefixSum r.val).comp hσ
  have hT := Shao.measurable_energy.sub ((Shao.measurable_prefixSquares r.val).comp hσ)
  have hz := Shao.measurable_prefixSum (n := n) n
  have hp : Measurable (fun z : Shao.Path n =>
      ((x * Real.sqrt (Shao.energy z),
        (Shao.prefixSum (fun i => z (σ i)) r.val,
          (Shao.energy z - Shao.prefixSquares (fun i => z (σ i)) r.val, Shao.prefixSum z n))) :
        CompletionParameters)) :=
    (Shao.measurable_energyWall x).prodMk (hy.prodMk (hT.prodMk hz))
  have hm := (measurable_interiorSpatialDerivative ν hRegular).comp hp
  dsimp only [Function.comp_def] at hm
  simp_rw [completedDerivative_eq_interior n ν x]
  exact Measurable.ite
    ((measurableSet_lt measurable_const Shao.measurable_energy).inter
      ((measurableSet_strictLive n x σ r.val).inter
        (measurableSet_lt (continuous_abs.measurable.comp hz) (Shao.measurable_energyWall x))))
    hm measurable_const

end Shao.C2.InteriorDerivativeMeasurability
