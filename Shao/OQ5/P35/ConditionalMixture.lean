import Shao.OQ5.P35.ConditionalSample
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Mixing actual fixed-position conditional laws

The exact count event is a disjoint union of equal-probability fixed-position
events. Its conditional law is their uniform finite mixture. No independence
assertion is made under the mixed count event.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

theorem exactCategoryEvent_ne_zero (n K j : ℕ) (hj : 1 ≤ j) (hK : K ≤ n) :
    sampleLaw (exactCategoryEvent n K j) ≠ 0 := by
  have hq : 0 < categoryBelowMass j :=
    lt_of_lt_of_le (by norm_num) (categoryBelowMass_bounds j hj).1
  have hp : 0 < sampleLaw.real (exactCategoryEvent n K j) := by
    rw [exactCategoryEvent_probability n K j hK]
    exact mul_pos
      (mul_pos (by exact_mod_cast Nat.choose_pos hK) (pow_pos (categoryMass_pos j) K))
      (pow_pos hq (n - K))
  intro hz
  simp [measureReal_def, hz] at hp

theorem exactCategoryEvent_cond_isProbability (n K j : ℕ) (hj : 1 ≤ j) (hK : K ≤ n) :
    IsProbabilityMeasure (cond sampleLaw (exactCategoryEvent n K j)) :=
  cond_isProbabilityMeasure (exactCategoryEvent_ne_zero n K j hj hK)

theorem cond_exactCategoryEvent_eq_uniform_sum
    (n K j : ℕ) (hj : 1 ≤ j) (hK : K ≤ n) :
    cond sampleLaw (exactCategoryEvent n K j) =
      ((n.choose K : ℝ≥0∞)⁻¹) •
        ∑ J ∈ (Finset.univ : Finset (Fin n)).powersetCard K,
          cond sampleLaw (fixedCategoryEvent n j J) := by
  classical
  let F := (Finset.univ : Finset (Fin n)).powersetCard K
  have hcard : F.card = n.choose K := by simp [F, Finset.card_powersetCard]
  have hF : F.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact Nat.choose_pos hK)
  obtain ⟨J0, hJ0⟩ := hF
  let a := sampleLaw (fixedCategoryEvent n j J0)
  have ha0 : a ≠ 0 := fixedCategoryEvent_ne_zero n j hj J0
  have hat : a ≠ ∞ := measure_ne_top _ _
  have hc0 : (n.choose K : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hK).ne'
  have hct : (n.choose K : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hp (J : Finset (Fin n)) (hJ : J ∈ F) :
      sampleLaw (fixedCategoryEvent n j J) = a := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) hat).mp
    change sampleLaw.real (fixedCategoryEvent n j J) =
      sampleLaw.real (fixedCategoryEvent n j J0)
    rw [fixedCategoryEvent_probability, fixedCategoryEvent_probability,
      (Finset.mem_powersetCard.mp hJ).2, (Finset.mem_powersetCard.mp hJ0).2]
  have hd : Set.PairwiseDisjoint (↑F) (fixedCategoryEvent n j) := by
    intro J _ J' _ hne
    exact fixedCategoryEvent_disjoint n j J J' hne
  have hm (J : Finset (Fin n)) : MeasurableSet (fixedCategoryEvent n j J) :=
    measurableSet_fixedCategoryEvent n j J
  have hre : sampleLaw.restrict (exactCategoryEvent n K j) =
      ∑ J ∈ F, sampleLaw.restrict (fixedCategoryEvent n j J) := by
    rw [exactCategoryEvent_eq_biUnion, Measure.restrict_biUnion_finset hd hm]
    exact Measure.sum_coe_finset F (fun J => sampleLaw.restrict (fixedCategoryEvent n j J))
  have he : sampleLaw (exactCategoryEvent n K j) = (n.choose K : ℝ≥0∞) * a := by
    rw [exactCategoryEvent_eq_biUnion, measure_biUnion_finset hd (fun J _ => hm J)]
    calc
      _ = ∑ _J ∈ F, a := Finset.sum_congr rfl (fun J hJ => hp J hJ)
      _ = _ := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hs :
      (∑ J ∈ F, cond sampleLaw (fixedCategoryEvent n j J)) =
        a⁻¹ • ∑ J ∈ F, sampleLaw.restrict (fixedCategoryEvent n j J) := by
    unfold ProbabilityTheory.cond
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun J hJ => by rw [hp J hJ])
  calc
    cond sampleLaw (exactCategoryEvent n K j) =
        ((n.choose K : ℝ≥0∞) * a)⁻¹ •
          ∑ J ∈ F, sampleLaw.restrict (fixedCategoryEvent n j J) := by
      unfold ProbabilityTheory.cond
      rw [he, hre]
    _ = (n.choose K : ℝ≥0∞)⁻¹ •
        (a⁻¹ • ∑ J ∈ F, sampleLaw.restrict (fixedCategoryEvent n j J)) := by
      rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hct), smul_smul]
    _ = _ := by rw [← hs]

theorem integrable_cond_exactCategoryEvent
    (n K j : ℕ) (hj : 1 ≤ j) (hK : K ≤ n)
    (f : (ℕ → ℝ) → ℝ)
    (hf : ∀ J ∈ (Finset.univ : Finset (Fin n)).powersetCard K,
      Integrable f (cond sampleLaw (fixedCategoryEvent n j J))) :
    Integrable f (cond sampleLaw (exactCategoryEvent n K j)) := by
  rw [cond_exactCategoryEvent_eq_uniform_sum n K j hj hK]
  apply (integrable_finsetSum_measure.mpr hf).smul_measure
  exact ENNReal.inv_ne_top.mpr (by exact_mod_cast (Nat.choose_pos hK).ne')

theorem integral_cond_exactCategoryEvent
    (n K j : ℕ) (hj : 1 ≤ j) (hK : K ≤ n)
    (f : (ℕ → ℝ) → ℝ)
    (hf : ∀ J ∈ (Finset.univ : Finset (Fin n)).powersetCard K,
      Integrable f (cond sampleLaw (fixedCategoryEvent n j J))) :
    (∫ ω, f ω ∂cond sampleLaw (exactCategoryEvent n K j)) =
      (n.choose K : ℝ)⁻¹ *
        ∑ J ∈ (Finset.univ : Finset (Fin n)).powersetCard K,
          (∫ ω, f ω ∂cond sampleLaw (fixedCategoryEvent n j J)) := by
  rw [cond_exactCategoryEvent_eq_uniform_sum n K j hj hK,
    integral_smul_measure, integral_finsetSum_measure hf,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

theorem integral_cond_exactCategoryEvent_le
    (n K j : ℕ) (hj : 1 ≤ j) (hK : K ≤ n)
    (f : (ℕ → ℝ) → ℝ) (C : ℝ)
    (hf : ∀ J ∈ (Finset.univ : Finset (Fin n)).powersetCard K,
      Integrable f (cond sampleLaw (fixedCategoryEvent n j J)))
    (hbound : ∀ J ∈ (Finset.univ : Finset (Fin n)).powersetCard K,
      (∫ ω, f ω ∂cond sampleLaw (fixedCategoryEvent n j J)) ≤ C) :
    (∫ ω, f ω ∂cond sampleLaw (exactCategoryEvent n K j)) ≤ C := by
  have hc : 0 < (n.choose K : ℝ) := by exact_mod_cast Nat.choose_pos hK
  rw [integral_cond_exactCategoryEvent n K j hj hK f hf]
  calc
    _ ≤ (n.choose K : ℝ)⁻¹ *
        ∑ _J ∈ (Finset.univ : Finset (Fin n)).powersetCard K, C :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hbound) (inv_nonneg.mpr hc.le)
    _ = C := by
      rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp

theorem measureReal_cond_exactCategoryEvent_le
    (n K j : ℕ) (hj : 1 ≤ j) (hK : K ≤ n)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) (C : ℝ)
    (hbound : ∀ J ∈ (Finset.univ : Finset (Fin n)).powersetCard K,
      (cond sampleLaw (fixedCategoryEvent n j J)).real B ≤ C) :
    (cond sampleLaw (exactCategoryEvent n K j)).real B ≤ C := by
  classical
  let f : (ℕ → ℝ) → ℝ := B.indicator (fun _ => 1)
  have hf (J : Finset (Fin n))
      (_hJ : J ∈ (Finset.univ : Finset (Fin n)).powersetCard K) :
      Integrable f (cond sampleLaw (fixedCategoryEvent n j J)) := by
    have := fixedCategoryEvent_cond_isProbability n j hj J
    exact (integrable_const (1 : ℝ)).indicator hB
  have hb (J : Finset (Fin n))
      (hJ : J ∈ (Finset.univ : Finset (Fin n)).powersetCard K) :
      (∫ ω, f ω ∂cond sampleLaw (fixedCategoryEvent n j J)) ≤ C := by
    simpa only [f, integral_indicator_const (1 : ℝ) hB, smul_eq_mul, mul_one] using hbound J hJ
  have := exactCategoryEvent_cond_isProbability n K j hj hK
  have h := integral_cond_exactCategoryEvent_le n K j hj hK f C hf hb
  simpa only [f, integral_indicator_const (1 : ℝ) hB, smul_eq_mul, mul_one] using h

end

end Shao.OQ5.P35
