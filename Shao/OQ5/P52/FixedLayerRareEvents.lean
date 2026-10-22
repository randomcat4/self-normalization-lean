import Shao.OQ5.P52.FixedLayerSample
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Exact probabilities for the actual fixed-layer rare events

At the actual layer sample size, the event is literally two target states
and zero in every other sampled position of that layer. Noise and all other
layers are unrestricted. No conditional law or asymptotic assertion is used.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

attribute [local instance] fixedSampleLaw_isProbabilityMeasure

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
    Measurable (fixedSampleCategory j i) :=
  ((measurable_pi_apply j).comp measurable_snd).comp (measurable_fixedSampleCoordinate i)

theorem map_fixedSampleCategory (j i : ℕ) :
    fixedSampleLaw.map (fixedSampleCategory j i) =
      Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j) := by
  have hm : Measurable (fun o : LayerObs => o.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  calc
    fixedSampleLaw.map (fixedSampleCategory j i) =
        (fixedSampleLaw.map (fixedSampleCoordinate i)).map (fun o : LayerObs => o.2 j) := by
      rw [Measure.map_map hm (measurable_fixedSampleCoordinate i)]
      rfl
    _ = _ := by rw [map_fixedSampleCoordinate, map_fixedObservation_category]

theorem iIndepFun_fixedSampleCategory (j : ℕ) :
    iIndepFun (fixedSampleCategory j) fixedSampleLaw := by
  exact iIndepFun_fixedSampleCoordinate.comp (fun _ (o : LayerObs) => o.2 j)
    (fun _ => (measurable_pi_apply j).comp measurable_snd)

private theorem fixedLayerPositionEvent_eq_inter (j n : ℕ) (J : Finset (Fin n)) :
    fixedLayerPositionEvent j n J =
      ⋂ i : Fin n, fixedSampleCategory j i.val ⁻¹' (if i ∈ J then {1} else {0}) := by
  ext ω
  simp only [fixedLayerPositionEvent, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
  apply forall_congr'
  intro i
  by_cases hi : i ∈ J <;> simp [hi]

theorem measurableSet_fixedLayerPositionEvent (j n : ℕ) (J : Finset (Fin n)) :
    MeasurableSet (fixedLayerPositionEvent j n J) := by
  rw [fixedLayerPositionEvent_eq_inter]
  apply MeasurableSet.iInter
  intro i
  apply measurable_fixedSampleCategory j i.val
  by_cases hi : i ∈ J <;> simp [hi]

private theorem fixedSampleCategory_preimage_real (j i : ℕ) (s : Set (Fin 3))
    (hs : MeasurableSet s) :
    fixedSampleLaw.real (fixedSampleCategory j i ⁻¹' s) =
      (Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j)).real s := by
  change (fixedSampleLaw (fixedSampleCategory j i ⁻¹' s)).toReal = _
  rw [← Measure.map_apply (measurable_fixedSampleCategory j i) hs, map_fixedSampleCategory]
  rfl

private theorem fixedLayerMeasure_real_singleton (j : ℕ) (a : Fin 3) :
    (Shao.OQ5.P50.layerMeasure (fixedLayerP j) (fixedLayerQ j)).real {a} =
      Shao.OQ5.P50.layerWeight (fixedLayerP j) (fixedLayerQ j) a := by
  rw [measureReal_def, Shao.OQ5.P50.layerMeasure_singleton, ENNReal.toReal_ofReal]
  unfold Shao.OQ5.P50.layerWeight
  split_ifs
  · linarith [fixedLayerP_add_Q_lt_one j]
  · exact (fixedLayerP_bounds j).1.le
  · exact (fixedLayerQ_bounds j).1.le

theorem fixedLayerPositionEvent_probability (j n : ℕ) (J : Finset (Fin n)) :
    fixedSampleLaw.real (fixedLayerPositionEvent j n J) =
      (fixedLayerP j) ^ J.card * (1 - fixedLayerP j - fixedLayerQ j) ^ (n - J.card) := by
  classical
  have hi : iIndepFun (fun i : Fin n => fixedSampleCategory j i.val) fixedSampleLaw :=
    iIndepFun.precomp Fin.val_injective (iIndepFun_fixedSampleCategory j)
  have hp := hi.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun i : Fin n => if i ∈ J then {1} else {0})
    (by intro i _; by_cases hiJ : i ∈ J <;> simp [hiJ])
  have hreal := congrArg ENNReal.toReal hp
  have hfilter : (Finset.univ : Finset (Fin n)).filter (fun i => i ∈ J) = J := by
    ext i
    simp
  have hnot : (Finset.univ : Finset (Fin n)).filter (fun i => i ∉ J) =
      Finset.univ \ J := by
    ext i
    simp
  calc
    fixedSampleLaw.real (fixedLayerPositionEvent j n J) =
        ∏ i : Fin n, fixedSampleLaw.real
          (fixedSampleCategory j i.val ⁻¹' (if i ∈ J then {1} else {0})) := by
      simpa only [fixedLayerPositionEvent_eq_inter, measureReal_def,
        Finset.mem_univ, Set.iInter_true, ENNReal.toReal_prod] using hreal
    _ = ∏ i : Fin n, if i ∈ J then fixedLayerP j else 1 - fixedLayerP j - fixedLayerQ j := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hiJ : i ∈ J
      · simp only [hiJ, ite_true]
        rw [fixedSampleCategory_preimage_real _ _ _ (measurableSet_singleton 1),
          fixedLayerMeasure_real_singleton]
        norm_num [Shao.OQ5.P50.layerWeight]
      · simp only [hiJ, ite_false]
        rw [fixedSampleCategory_preimage_real _ _ _ (measurableSet_singleton 0),
          fixedLayerMeasure_real_singleton]
        simp only [Shao.OQ5.P50.layerWeight, ite_true]
    _ = (fixedLayerP j) ^ J.card *
        (1 - fixedLayerP j - fixedLayerQ j) ^ (n - J.card) := by
      rw [Finset.prod_ite, hfilter, hnot, Finset.prod_const, Finset.prod_const,
        Finset.card_sdiff]
      simp

private theorem fixedLayerPositionEvent_filter_eq (j n : ℕ) (J : Finset (Fin n))
    (ω : ℕ → LayerObs) (hω : ω ∈ fixedLayerPositionEvent j n J) :
    Finset.univ.filter (fun i : Fin n => fixedSampleCategory j i.val ω = 1) = J := by
  classical
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro heq
    by_contra hi
    have hzero : fixedSampleCategory j i.val ω = 0 := by
      simpa only [fixedLayerPositionEvent, Set.mem_ofPred_eq, hi, ite_false] using hω i
    have hbad : (0 : Fin 3) = 1 := hzero.symm.trans heq
    exact (by decide : (0 : Fin 3) ≠ 1) hbad
  · intro hi
    simpa only [fixedLayerPositionEvent, Set.mem_ofPred_eq, hi, ite_true] using hω i

theorem fixedLayerExactEvent_eq_biUnion (j n K : ℕ) :
    fixedLayerExactEvent j n K =
      ⋃ J ∈ (Finset.univ : Finset (Fin n)).powersetCard K, fixedLayerPositionEvent j n J := by
  classical
  ext ω
  constructor
  · intro hω
    rcases hω with ⟨hcard, hstates⟩
    let J := Finset.univ.filter (fun i : Fin n => fixedSampleCategory j i.val ω = 1)
    refine Set.mem_iUnion.mpr ⟨J, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
    · intro i
      by_cases hi : fixedSampleCategory j i.val ω = 1
      · simp [J, hi]
      · have hzero : fixedSampleCategory j i.val ω = 0 := (hstates i).resolve_right hi
        simp [J, hzero]
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨J, hω⟩
    rcases Set.mem_iUnion.mp hω with ⟨hJ, hω⟩
    have hcard := (Finset.mem_powersetCard.mp hJ).2
    constructor
    · rw [fixedLayerPositionEvent_filter_eq j n J ω hω, hcard]
    · intro i
      by_cases hi : i ∈ J
      · right
        simpa only [fixedLayerPositionEvent, Set.mem_ofPred_eq, hi, ite_true] using hω i
      · left
        simpa only [fixedLayerPositionEvent, Set.mem_ofPred_eq, hi, ite_false] using hω i

theorem measurableSet_fixedLayerExactEvent (j n K : ℕ) :
    MeasurableSet (fixedLayerExactEvent j n K) := by
  rw [fixedLayerExactEvent_eq_biUnion]
  apply MeasurableSet.biUnion (Finset.finite_toSet _).countable
  intro J _
  exact measurableSet_fixedLayerPositionEvent j n J

theorem fixedLayerPositionEvent_disjoint (j n : ℕ) (J J' : Finset (Fin n))
    (hJJ : J ≠ J') :
    Disjoint (fixedLayerPositionEvent j n J) (fixedLayerPositionEvent j n J') := by
  apply Set.disjoint_left.mpr
  intro ω hω hω'
  exact hJJ ((fixedLayerPositionEvent_filter_eq j n J ω hω).symm.trans
    (fixedLayerPositionEvent_filter_eq j n J' ω hω'))

theorem fixedLayerExactEvent_probability (j n K : ℕ) (hK : K ≤ n) :
    fixedSampleLaw.real (fixedLayerExactEvent j n K) =
      (n.choose K : ℝ) * (fixedLayerP j) ^ K *
        (1 - fixedLayerP j - fixedLayerQ j) ^ (n - K) := by
  classical
  have _ := hK
  rw [fixedLayerExactEvent_eq_biUnion]
  rw [measureReal_biUnion_finset
    (fun J _ J' _ hJJ => fixedLayerPositionEvent_disjoint j n J J' hJJ)
    (fun J _ => measurableSet_fixedLayerPositionEvent j n J)]
  calc
    (∑ J ∈ (Finset.univ : Finset (Fin n)).powersetCard K,
        fixedSampleLaw.real (fixedLayerPositionEvent j n J)) =
        ∑ _J ∈ (Finset.univ : Finset (Fin n)).powersetCard K,
          (fixedLayerP j) ^ K * (1 - fixedLayerP j - fixedLayerQ j) ^ (n - K) := by
      apply Finset.sum_congr rfl
      intro J hJ
      rw [fixedLayerPositionEvent_probability, (Finset.mem_powersetCard.mp hJ).2]
    _ = (n.choose K : ℝ) * (fixedLayerP j) ^ K *
        (1 - fixedLayerP j - fixedLayerQ j) ^ (n - K) := by
      simp only [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring

theorem fixedLayerRareEvent_probability (j : ℕ) :
    fixedSampleLaw.real (fixedLayerRareEvent j) =
      ((fixedLayerN j).choose 2 : ℝ) * (fixedLayerP j) ^ 2 *
        (1 - fixedLayerP j - fixedLayerQ j) ^ (fixedLayerN j - 2) := by
  exact fixedLayerExactEvent_probability j (fixedLayerN j) 2
    (le_trans (by norm_num : 2 ≤ 8) (fixedLayerN_ge_eight j))

theorem fixedLayerRareEvent_probability_pos (j : ℕ) :
    0 < fixedSampleLaw.real (fixedLayerRareEvent j) := by
  rw [fixedLayerRareEvent_probability]
  apply mul_pos
  · apply mul_pos
    · exact_mod_cast Nat.choose_pos (le_trans (by norm_num : 2 ≤ 8) (fixedLayerN_ge_eight j))
    · exact pow_pos (fixedLayerP_bounds j).1 _
  · apply pow_pos
    linarith [fixedLayerP_add_Q_lt_one j]

end
end Shao.OQ5.P52
