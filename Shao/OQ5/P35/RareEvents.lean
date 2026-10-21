import Shao.OQ5.P35.CategoryTails
import Shao.OQ5.P35.InfiniteSample
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Exact p35 rare-category event probabilities

Source: `current/oq56/inputs02/p35.md`, §4, formula (9).
The literal count/no-larger event and all fixed-position events live on the
same infinite sample law. This file proves exact probabilities and positivity;
it contains no conditional-law theorem or eventual lower-bound assertion.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Categories decoded from the actual fixed infinite observation sequence. -/
def sampleCategory (i : ℕ) (ω : ℕ → ℝ) : ℕ :=
  decodeCategory (sampleCoordinate i ω)

/-- Target positions equal j and every remaining coordinate is strictly below j. -/
def fixedCategoryEvent (n j : ℕ) (J : Finset (Fin n)) : Set (ℕ → ℝ) :=
  {ω | ∀ i : Fin n, if i ∈ J then sampleCategory i.val ω = j
    else sampleCategory i.val ω < j}

/-- The source event: exactly K target categories and no category larger than j. -/
def exactCategoryEvent (n K j : ℕ) : Set (ℕ → ℝ) :=
  {ω | (Finset.univ.filter (fun i : Fin n => sampleCategory i.val ω = j)).card = K ∧
    ∀ i : Fin n, sampleCategory i.val ω ≤ j}

/-- A fixed deterministic category-index sequence, not a changing sampling law. -/
def targetCategoryCount (j : ℕ) : ℕ := 4 ^ j

def rareSampleSize (j : ℕ) : ℕ := targetCategoryCount j ^ 4

def rareCategoryEvent (j : ℕ) : Set (ℕ → ℝ) :=
  exactCategoryEvent (rareSampleSize j) (targetCategoryCount j) j

theorem measurable_sampleCategory (i : ℕ) : Measurable (sampleCategory i) :=
  measurable_decodeCategory.comp (measurable_sampleCoordinate i)

theorem map_sampleCategory (i : ℕ) :
    Measure.map (sampleCategory i) sampleLaw = categoryMeasure := by
  calc
    Measure.map (sampleCategory i) sampleLaw =
        Measure.map decodeCategory (Measure.map (sampleCoordinate i) sampleLaw) := by
      rw [Measure.map_map measurable_decodeCategory (measurable_sampleCoordinate i)]
      rfl
    _ = categoryMeasure := by rw [map_sampleCoordinate, map_category_realLaw]

theorem iIndepFun_sampleCategory : iIndepFun sampleCategory sampleLaw := by
  exact iIndepFun_sampleCoordinate.comp (fun _ => decodeCategory)
    (fun _ => measurable_decodeCategory)

private theorem fixedCategoryEvent_eq_inter (n j : ℕ) (J : Finset (Fin n)) :
    fixedCategoryEvent n j J =
      ⋂ i : Fin n, sampleCategory i.val ⁻¹' (if i ∈ J then {j} else Set.Iio j) := by
  ext ω
  simp only [fixedCategoryEvent, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
  apply forall_congr'
  intro i
  by_cases hi : i ∈ J <;> simp [hi]

theorem measurableSet_fixedCategoryEvent (n j : ℕ) (J : Finset (Fin n)) :
    MeasurableSet (fixedCategoryEvent n j J) := by
  rw [fixedCategoryEvent_eq_inter]
  apply MeasurableSet.iInter
  intro i
  apply measurable_sampleCategory i.val
  by_cases hi : i ∈ J <;> simp [hi]

private theorem sampleCategory_preimage_real (i : ℕ) (s : Set ℕ)
    (hs : MeasurableSet s) :
    sampleLaw.real (sampleCategory i ⁻¹' s) = categoryMeasure.real s := by
  change (sampleLaw (sampleCategory i ⁻¹' s)).toReal = (categoryMeasure s).toReal
  rw [← Measure.map_apply (measurable_sampleCategory i) hs, map_sampleCategory]

theorem fixedCategoryEvent_probability (n j : ℕ) (J : Finset (Fin n)) :
    sampleLaw.real (fixedCategoryEvent n j J) =
      categoryMass j ^ J.card * categoryBelowMass j ^ (n - J.card) := by
  classical
  have hi : iIndepFun (fun i : Fin n => sampleCategory i.val) sampleLaw :=
    iIndepFun.precomp Fin.val_injective iIndepFun_sampleCategory
  have hp := hi.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun i : Fin n => if i ∈ J then {j} else Set.Iio j)
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
    sampleLaw.real (fixedCategoryEvent n j J) =
        ∏ i : Fin n, sampleLaw.real
          (sampleCategory i.val ⁻¹' (if i ∈ J then {j} else Set.Iio j)) := by
      simpa only [fixedCategoryEvent_eq_inter, measureReal_def,
        Finset.mem_univ, Set.iInter_true, ENNReal.toReal_prod] using hreal
    _ = ∏ i : Fin n, if i ∈ J then categoryMass j else categoryBelowMass j := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hiJ : i ∈ J
      · simp only [hiJ, ite_true]
        rw [sampleCategory_preimage_real _ _ (measurableSet_singleton j)]
        exact categoryMeasure_real_singleton j
      · simp only [hiJ, ite_false]
        exact sampleCategory_preimage_real _ _ measurableSet_Iio
    _ = categoryMass j ^ J.card * categoryBelowMass j ^ (n - J.card) := by
      rw [Finset.prod_ite, hfilter, hnot, Finset.prod_const, Finset.prod_const,
        Finset.card_sdiff]
      simp

private theorem fixedCategoryEvent_filter_eq (n j : ℕ) (J : Finset (Fin n))
    (ω : ℕ → ℝ) (hω : ω ∈ fixedCategoryEvent n j J) :
    Finset.univ.filter (fun i : Fin n => sampleCategory i.val ω = j) = J := by
  classical
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro heq
    by_contra hi
    have hlt : sampleCategory i.val ω < j := by simpa [fixedCategoryEvent, hi] using hω i
    exact (ne_of_lt hlt) heq
  · intro hi
    simpa [fixedCategoryEvent, hi] using hω i

theorem exactCategoryEvent_eq_biUnion (n K j : ℕ) :
    exactCategoryEvent n K j =
      ⋃ J ∈ (Finset.univ : Finset (Fin n)).powersetCard K, fixedCategoryEvent n j J := by
  classical
  ext ω
  constructor
  · intro hω
    rcases hω with ⟨hcard, hle⟩
    let J := Finset.univ.filter (fun i : Fin n => sampleCategory i.val ω = j)
    refine Set.mem_iUnion.mpr ⟨J, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
    · intro i
      by_cases hi : sampleCategory i.val ω = j
      · simp [J, hi]
      · have hlt : sampleCategory i.val ω < j := lt_of_le_of_ne (hle i) hi
        simp [J, hi, hlt]
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨J, hω⟩
    rcases Set.mem_iUnion.mp hω with ⟨hJ, hω⟩
    have hcard := (Finset.mem_powersetCard.mp hJ).2
    constructor
    · rw [fixedCategoryEvent_filter_eq n j J ω hω, hcard]
    · intro i
      by_cases hi : i ∈ J
      · have heq : sampleCategory i.val ω = j := by simpa [fixedCategoryEvent, hi] using hω i
        exact heq.le
      · have hlt : sampleCategory i.val ω < j := by simpa [fixedCategoryEvent, hi] using hω i
        exact hlt.le

theorem measurableSet_exactCategoryEvent (n K j : ℕ) :
    MeasurableSet (exactCategoryEvent n K j) := by
  rw [exactCategoryEvent_eq_biUnion]
  apply MeasurableSet.biUnion (Finset.finite_toSet _).countable
  intro J _
  exact measurableSet_fixedCategoryEvent n j J

theorem fixedCategoryEvent_disjoint (n j : ℕ) (J J' : Finset (Fin n)) (hJJ : J ≠ J') :
    Disjoint (fixedCategoryEvent n j J) (fixedCategoryEvent n j J') := by
  apply Set.disjoint_left.mpr
  intro ω hω hω'
  exact hJJ ((fixedCategoryEvent_filter_eq n j J ω hω).symm.trans
    (fixedCategoryEvent_filter_eq n j J' ω hω'))

theorem exactCategoryEvent_probability (n K j : ℕ) (hK : K ≤ n) :
    sampleLaw.real (exactCategoryEvent n K j) =
      (n.choose K : ℝ) * categoryMass j ^ K * categoryBelowMass j ^ (n - K) := by
  classical
  have _ := hK
  rw [exactCategoryEvent_eq_biUnion]
  rw [measureReal_biUnion_finset
    (fun J _ J' _ hJJ => fixedCategoryEvent_disjoint n j J J' hJJ)
    (fun J _ => measurableSet_fixedCategoryEvent n j J)]
  calc
    (∑ J ∈ (Finset.univ : Finset (Fin n)).powersetCard K,
        sampleLaw.real (fixedCategoryEvent n j J)) =
        ∑ _J ∈ (Finset.univ : Finset (Fin n)).powersetCard K,
          categoryMass j ^ K * categoryBelowMass j ^ (n - K) := by
      apply Finset.sum_congr rfl
      intro J hJ
      rw [fixedCategoryEvent_probability, (Finset.mem_powersetCard.mp hJ).2]
    _ = (n.choose K : ℝ) * categoryMass j ^ K * categoryBelowMass j ^ (n - K) := by
      simp only [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring

theorem targetCategoryCount_le_rareSampleSize (j : ℕ) :
    targetCategoryCount j ≤ rareSampleSize j := by
  have hk : 0 < targetCategoryCount j := by unfold targetCategoryCount; positivity
  have hprod : 1 ≤ targetCategoryCount j * targetCategoryCount j * targetCategoryCount j := by
    exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos hk hk) hk)
  unfold rareSampleSize
  calc
    targetCategoryCount j = targetCategoryCount j * 1 := by simp
    _ ≤ targetCategoryCount j * (targetCategoryCount j * targetCategoryCount j * targetCategoryCount j) :=
      Nat.mul_le_mul_left _ hprod
    _ = targetCategoryCount j ^ 4 := by ring

theorem rareCategoryEvent_probability (j : ℕ) (hj : 1 ≤ j) :
    sampleLaw.real (rareCategoryEvent j) =
      ((rareSampleSize j).choose (targetCategoryCount j) : ℝ) *
        categoryMass j ^ targetCategoryCount j *
        categoryBelowMass j ^ (rareSampleSize j - targetCategoryCount j) := by
  have _ := hj
  exact exactCategoryEvent_probability _ _ _ (targetCategoryCount_le_rareSampleSize j)

theorem rareCategoryEvent_probability_pos (j : ℕ) (hj : 1 ≤ j) :
    0 < sampleLaw.real (rareCategoryEvent j) := by
  rw [rareCategoryEvent_probability j hj]
  apply mul_pos
  · apply mul_pos
    · exact_mod_cast Nat.choose_pos (targetCategoryCount_le_rareSampleSize j)
    · exact pow_pos (categoryMass_pos j) _
  · apply pow_pos
    have hq := (categoryBelowMass_bounds j hj).1
    linarith

end

end Shao.OQ5.P35
