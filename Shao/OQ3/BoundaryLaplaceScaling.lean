import Shao.OQ3.BoundaryLaplaceCoordinates
import Shao.OQ3.BoundaryLaplaceIntegral

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem boundary_anisotropic_halfspace_scaling (t : ℝ) (ht : 0 < t) :
    let m : Measure (ℝ × ℝ) :=
      (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0))
    let T : (ℝ × ℝ) → (ℝ × ℝ) := fun p => (t * p.1, t ^ 2 * p.2)
    Measure.map T m = ENNReal.ofReal ((t ^ 3)⁻¹) • m ∧ MeasurableEmbedding T ∧
      ∀ f : (ℝ × ℝ) → ℝ,
        (Integrable (fun p => f (T p)) m ↔ Integrable f m) ∧
        (∫ p : ℝ × ℝ, f (T p) ∂m) = (t ^ 3)⁻¹ * ∫ p : ℝ × ℝ, f p ∂m
 := by
  let m : Measure (ℝ × ℝ) :=
    (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0))
  let T : (ℝ × ℝ) → (ℝ × ℝ) := fun p => (t * p.1, t ^ 2 * p.2)
  have ht2 : 0 < t ^ 2 := pow_pos ht 2
  let e1 : ℝ ≃ₜ ℝ := Homeomorph.mulLeft₀ t ht.ne'
  let e2 : ℝ ≃ₜ ℝ := Homeomorph.mulLeft₀ (t ^ 2) ht2.ne'
  have he2 : MeasurableEmbedding (fun x : ℝ => t ^ 2 * x) := e2.isClosedEmbedding.measurableEmbedding
  have hEmb : MeasurableEmbedding T := (e1.prodCongr e2).isClosedEmbedding.measurableEmbedding
  have hpre : (fun x : ℝ => t ^ 2 * x) ⁻¹' Set.Ici 0 = Set.Ici 0 := by
    ext x
    exact mul_nonneg_iff_of_pos_left ht2
  have hmap1 : Measure.map (fun x : ℝ => t * x) volume =
      ENNReal.ofReal (t⁻¹) • (volume : Measure ℝ) := by
    simpa only [abs_of_pos (inv_pos.mpr ht)] using Real.map_volume_mul_left ht.ne'
  have hmap2 : Measure.map (fun x : ℝ => t ^ 2 * x)
      ((volume : Measure ℝ).restrict (Set.Ici 0)) =
      ENNReal.ofReal ((t ^ 2)⁻¹) • ((volume : Measure ℝ).restrict (Set.Ici 0)) := by
    calc
      _ = (Measure.map (fun x : ℝ => t ^ 2 * x) volume).restrict (Set.Ici 0) := by
        rw [he2.restrict_map, hpre]
      _ = _ := by rw [Real.map_volume_mul_left ht2.ne', Measure.restrict_smul,
        abs_of_pos (inv_pos.mpr ht2)]
  have hcoef : ENNReal.ofReal (t⁻¹) * ENNReal.ofReal ((t ^ 2)⁻¹) =
      ENNReal.ofReal ((t ^ 3)⁻¹) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le)]
    congr 1
    simp only [← inv_pow]
    ring
  have hmap : Measure.map T m = ENNReal.ofReal ((t ^ 3)⁻¹) • m := by
    change Measure.map (Prod.map (fun x : ℝ => t * x) (fun x : ℝ => t ^ 2 * x))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0))) = _
    rw [← Measure.map_prod_map (volume : Measure ℝ)
      ((volume : Measure ℝ).restrict (Set.Ici 0)) (by fun_prop) (by fun_prop),
      hmap1, hmap2, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, hcoef]
  refine ⟨hmap, hEmb, ?_⟩
  intro f
  have hc0 : ENNReal.ofReal ((t ^ 3)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos ht 3))).ne'
  have hcfin : ENNReal.ofReal ((t ^ 3)⁻¹) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hi : Integrable f (Measure.map T m) ↔ Integrable (fun p => f (T p)) m :=
    hEmb.integrable_map_iff
  rw [hmap, integrable_smul_measure hc0 hcfin] at hi
  refine ⟨hi.symm, ?_⟩
  rw [← hEmb.integral_map f, hmap, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg ht.le 3)), smul_eq_mul]

theorem boundary_cutoff_rectangle_integral_scaling
    (f : (ℝ × ℝ) → ℝ) (rho t : ℝ) (ht : 0 < t) :
    let m : Measure (ℝ × ℝ) :=
      (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0))
    let m0 : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)
    let R : Set (ℝ × ℝ) := {w | |w.1| ≤ rho ∧ 0 ≤ w.2 ∧ w.2 ≤ rho}
    let H : (ℝ × ℝ) → ℝ := fun p =>
      if |t * p.1| ≤ rho ∧ t ^ 2 * p.2 ≤ rho then f (t * p.1, t ^ 2 * p.2) else 0
    (Integrable H m ↔ IntegrableOn f R m0) ∧
      (∫ w : ℝ × ℝ in R, f w ∂m0) = t ^ 3 * ∫ p : ℝ × ℝ, H p ∂m := by
  let m : Measure (ℝ × ℝ) :=
    (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0))
  let m0 : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)
  let R : Set (ℝ × ℝ) := {w | |w.1| ≤ rho ∧ 0 ≤ w.2 ∧ w.2 ≤ rho}
  let H : (ℝ × ℝ) → ℝ := fun p =>
    if |t * p.1| ≤ rho ∧ t ^ 2 * p.2 ≤ rho then f (t * p.1, t ^ 2 * p.2) else 0
  let S : Set (ℝ × ℝ) := {w | |w.1| ≤ rho ∧ w.2 ≤ rho}
  let cut : (ℝ × ℝ) → ℝ := fun w => if |w.1| ≤ rho ∧ w.2 ≤ rho then f w else 0
  have hS : MeasurableSet S :=
    (measurableSet_le (show Measurable (fun w : ℝ × ℝ => |w.1|) from
      (show Continuous (fun w : ℝ × ℝ => |w.1|) from by fun_prop).measurable) measurable_const).inter
      (measurableSet_le measurable_snd measurable_const)
  have hhalf : m = m0.restrict {p : ℝ × ℝ | 0 ≤ p.2} := by
    have hh := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (Set.univ : Set ℝ) (Set.Ici (0 : ℝ))
    have heq : (Set.univ : Set ℝ) ×ˢ Set.Ici 0 = {p : ℝ × ℝ | 0 ≤ p.2} := by
      ext p
      simp
    rw [Measure.restrict_univ, heq] at hh
    exact hh
  have hrestr : m.restrict S = m0.restrict R := by
    rw [hhalf, Measure.restrict_restrict hS]
    congr 1
    ext w
    change ((|w.1| ≤ rho ∧ w.2 ≤ rho) ∧ 0 ≤ w.2) ↔ (|w.1| ≤ rho ∧ 0 ≤ w.2 ∧ w.2 ≤ rho)
    tauto
  have hcut : cut = S.indicator f := by
    funext w
    simp only [cut, S, Set.indicator, Set.mem_setOf_eq]
  have hint : Integrable cut m ↔ IntegrableOn f R m0 := by
    rw [hcut, integrable_indicator_iff hS]
    change Integrable f (m.restrict S) ↔ Integrable f (m0.restrict R)
    rw [hrestr]
  have hIeq : (∫ w : ℝ × ℝ, cut w ∂m) = ∫ w : ℝ × ℝ in R, f w ∂m0 := by
    rw [hcut, integral_indicator hS]
    change (∫ w : ℝ × ℝ, f w ∂m.restrict S) = ∫ w : ℝ × ℝ, f w ∂m0.restrict R
    rw [hrestr]
  obtain ⟨hcomp, hscale⟩ := (boundary_anisotropic_halfspace_scaling t ht).2.2 cut
  have hK : Integrable H m ↔ Integrable cut m := hcomp
  have hKI : (∫ p : ℝ × ℝ, H p ∂m) = (t ^ 3)⁻¹ * ∫ w : ℝ × ℝ, cut w ∂m := hscale
  refine ⟨hK.trans hint, ?_⟩
  rw [hIeq] at hKI
  rw [hKI, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 3 ht.ne'), one_mul]

end
end Shao.OQ3
