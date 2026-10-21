import Shao.OQ5.P52.FixedLayerModel

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

/-- The actual finite-state excess moment, with both coefficient arguments explicit. -/
def fixedLayerExcessCost (j : ℕ) (η «λ» : ℝ) : ℝ :=
  ∫ s : Fin 3 × Fin 3,
    Real.exp («λ» * |Shao.OQ5.P50.layerKernel (fixedLayerN j) (fixedLayerT j)
      (fixedLayerP j) (fixedLayerQ j) s.1 s.2| ^ η) - 1
    ∂(Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j)).prod
      (Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j))

private theorem fixedPairCategory_measurable (j : ℕ) :
    Measurable (fun z : LayerObs × LayerObs => (z.1.2 j, z.2.2 j)) :=
  ((measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)).prodMk
    ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))

private theorem map_fixedPairCategory (j : ℕ) :
    (fixedObservationLaw.prod fixedObservationLaw).map
      (fun z : LayerObs × LayerObs => (z.1.2 j, z.2.2 j)) =
      (Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j)).prod
        (Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j)) := by
  exact Shao.OQ5.P50.map_layerObservation_pair_category fixedLayerP fixedLayerQ
    (fun i => (fixedLayerP_bounds i).1.le) (fun i => (fixedLayerQ_bounds i).1.le)
    (fun i => (fixedLayerP_add_Q_lt_one i).le) j

private theorem finite_excess_five_atoms (n : ℕ) (t p q η «λ» : ℝ)
    (hn : 4 ≤ n) (ht : 0 < t) (hp : 0 < p) (hq : 0 < q)
    (hpq : p + q ≤ 1) (hη : 0 < η) :
    (∫ s : Fin 3 × Fin 3,
      Real.exp («λ» * |Shao.OQ5.P50.layerKernel n t p q s.1 s.2| ^ η) - 1
      ∂(Shao.OQ5.P50.layerMeasure p q).prod (Shao.OQ5.P50.layerMeasure p q)) =
      2 * (1 - p - q) * p * (Real.exp («λ» * t ^ η) - 1) +
      p ^ 2 * (Real.exp («λ» * (((n : ℝ) - 4) * t) ^ η) - 1) +
      2 * p * q * (Real.exp («λ» * (t * |1 - p - q - p * ((n : ℝ) - 4)| / q) ^ η) - 1) +
      2 * (1 - p - q) * q * (Real.exp («λ» * (p * t / q) ^ η) - 1) +
      q ^ 2 * (Real.exp («λ» *
        (p * t * |2 - 2 * q - p * ((n : ℝ) - 2)| / q ^ 2) ^ η) - 1) := by
  rw [Shao.OQ5.P50.integral_layerMeasure_prod p q hp.le hq.le hpq]
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  have hn' : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (4 : ℝ) - (n : ℝ) ≤ 0 := by linarith
  simp [huniv, Shao.OQ5.P50.layerWeight, Shao.OQ5.P50.layerKernel,
    abs_mul, abs_div, abs_of_pos ht, abs_of_pos hp, abs_of_pos hq,
    abs_of_nonpos hn0, Real.zero_rpow (ne_of_gt hη)]
  ring

theorem integrable_fixedLayerAtomExcess (j : ℕ) (η «λ» : ℝ) :
    Integrable (fun s : Fin 3 × Fin 3 =>
      Real.exp («λ» * |Shao.OQ5.P50.layerKernel (fixedLayerN j) (fixedLayerT j)
        (fixedLayerP j) (fixedLayerQ j) s.1 s.2| ^ η) - 1)
      ((Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j)).prod
        (Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j))) := by
  exact Shao.OQ5.P50.integrable_layerMeasure_prod _ _ _

theorem integrable_fixedLayerTermExcess (j : ℕ) (η «λ» : ℝ) :
    Integrable (fun z : LayerObs × LayerObs =>
      Real.exp («λ» * |fixedLayerTerm j z| ^ η) - 1)
      (fixedObservationLaw.prod fixedObservationLaw) := by
  let F := fun s : Fin 3 × Fin 3 => Real.exp («λ» * |Shao.OQ5.P50.layerKernel
    (fixedLayerN j) (fixedLayerT j) (fixedLayerP j) (fixedLayerQ j) s.1 s.2| ^ η) - 1
  have hI : Integrable F ((fixedObservationLaw.prod fixedObservationLaw).map
      (fun z : LayerObs × LayerObs => (z.1.2 j, z.2.2 j))) := by
    rw [map_fixedPairCategory]
    exact integrable_fixedLayerAtomExcess j η «λ»
  exact hI.comp_measurable (fixedPairCategory_measurable j)

theorem fixedLayerExcessCost_eq_pair_integral (j : ℕ) (η «λ» : ℝ) :
    fixedLayerExcessCost j η «λ» =
      ∫ z : LayerObs × LayerObs, Real.exp («λ» * |fixedLayerTerm j z| ^ η) - 1
        ∂fixedObservationLaw.prod fixedObservationLaw := by
  let F := fun s : Fin 3 × Fin 3 => Real.exp («λ» * |Shao.OQ5.P50.layerKernel
    (fixedLayerN j) (fixedLayerT j) (fixedLayerP j) (fixedLayerQ j) s.1 s.2| ^ η) - 1
  have hI : Integrable F ((fixedObservationLaw.prod fixedObservationLaw).map
      (fun z : LayerObs × LayerObs => (z.1.2 j, z.2.2 j))) := by
    rw [map_fixedPairCategory]
    exact integrable_fixedLayerAtomExcess j η «λ»
  calc
    _ = ∫ s, F s ∂(fixedObservationLaw.prod fixedObservationLaw).map
        (fun z : LayerObs × LayerObs => (z.1.2 j, z.2.2 j)) := by
      rw [map_fixedPairCategory]
      rfl
    _ = _ := integral_map (fixedPairCategory_measurable j).aemeasurable
      hI.aestronglyMeasurable

theorem fixedLayerExcessCost_nonneg (j : ℕ) (η «λ» : ℝ) («hλ» : 0 ≤ «λ») :
    0 ≤ fixedLayerExcessCost j η «λ» := by
  unfold fixedLayerExcessCost
  apply integral_nonneg
  intro s
  change 0 ≤ Real.exp («λ» * |Shao.OQ5.P50.layerKernel (fixedLayerN j) (fixedLayerT j)
    (fixedLayerP j) (fixedLayerQ j) s.1 s.2| ^ η) - 1
  have h0 : 0 ≤ «λ» * |Shao.OQ5.P50.layerKernel (fixedLayerN j) (fixedLayerT j)
      (fixedLayerP j) (fixedLayerQ j) s.1 s.2| ^ η :=
    mul_nonneg «hλ» (Real.rpow_nonneg (abs_nonneg _) _)
  linarith [Real.add_one_le_exp («λ» * |Shao.OQ5.P50.layerKernel (fixedLayerN j)
    (fixedLayerT j) (fixedLayerP j) (fixedLayerQ j) s.1 s.2| ^ η)]

theorem integral_fixedLayerAtomExp (j : ℕ) (η «λ» : ℝ) :
    (∫ s : Fin 3 × Fin 3,
      Real.exp («λ» * |Shao.OQ5.P50.layerKernel (fixedLayerN j) (fixedLayerT j)
        (fixedLayerP j) (fixedLayerQ j) s.1 s.2| ^ η)
      ∂(Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j)).prod
        (Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j))) =
      1 + fixedLayerExcessCost j η «λ» := by
  let _ := Shao.OQ5.P50.layerMeasure_isProbabilityMeasure (fixedLayerP j) (fixedLayerQ j)
    (fixedLayerP_bounds j).1.le (fixedLayerQ_bounds j).1.le
    (fixedLayerP_add_Q_lt_one j).le
  let F : Fin 3 × Fin 3 → ℝ := fun s => Real.exp («λ» * |Shao.OQ5.P50.layerKernel
    (fixedLayerN j) (fixedLayerT j) (fixedLayerP j) (fixedLayerQ j) s.1 s.2| ^ η)
  have hI : Integrable F ((Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j)).prod
      (Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j))) :=
    Shao.OQ5.P50.integrable_layerMeasure_prod _ _ F
  change (∫ s, F s ∂(Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j)).prod
      (Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j))) = 1 + fixedLayerExcessCost j η «λ»
  have hc : fixedLayerExcessCost j η «λ» = (∫ s, F s ∂(Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j)).prod
      (Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j))) - 1 := by
    change (∫ s, F s - 1 ∂(Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j)).prod
      (Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j))) = _
    rw [integral_sub hI (integrable_const (1 : ℝ))]
    simp
  linarith

theorem fixedLayerExcessCost_eq_five_atoms (j : ℕ) (η «λ» : ℝ) (hη : 0 < η) :
    let N := (fixedLayerN j : ℝ)
    let t := fixedLayerT j
    let p := fixedLayerP j
    let q := fixedLayerQ j
    fixedLayerExcessCost j η «λ» =
      2 * (1 - p - q) * p * (Real.exp («λ» * t ^ η) - 1) +
      p ^ 2 * (Real.exp («λ» * ((N - 4) * t) ^ η) - 1) +
      2 * p * q * (Real.exp («λ» * (t * |1 - p - q - p * (N - 4)| / q) ^ η) - 1) +
      2 * (1 - p - q) * q * (Real.exp («λ» * (p * t / q) ^ η) - 1) +
      q ^ 2 * (Real.exp («λ» *
        (p * t * |2 - 2 * q - p * (N - 2)| / q ^ 2) ^ η) - 1) := by
  dsimp only
  exact finite_excess_five_atoms (fixedLayerN j) (fixedLayerT j)
    (fixedLayerP j) (fixedLayerQ j) η «λ»
    (le_trans (by norm_num : (4 : ℕ) ≤ 8) (fixedLayerN_ge_eight j))
    (fixedLayerT_pos j) (fixedLayerP_bounds j).1 (fixedLayerQ_bounds j).1
    (fixedLayerP_add_Q_lt_one j).le hη

end
end Shao.OQ5.P52
