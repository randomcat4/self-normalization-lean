import Shao.OQ5.P52.FixedLayerErasedVariance
import Shao.OQ5.P52.FixedLayerErasedNoise

/-!
# Full-kernel population projection under the actual erased law

Honest noise L2 and residual L2 give the full-kernel L2. Canonical rows
identify the actual first projection. All square and cross terms are
integrable before Fubini and the exact second-moment expansion.
-/

set_option autoImplicit false

open MeasureTheory Filter

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

attribute [local instance] fixedErasedLaw_isProbabilityMeasure

private theorem erased_first_memLp_two (j : ℕ) :
    MemLp (fun o : LayerObs => o.1) 2 (fixedErasedLaw j) :=
  (memLp_two_iff_integrable_sq measurable_fst.aestronglyMeasurable).mpr
    (integrable_fixedErasedLaw_first_sq j)

theorem fixedKernel_memLp_two_fixedErasedLaw (j : ℕ) :
    MemLp fixedKernel 2 ((fixedErasedLaw j).prod (fixedErasedLaw j)) := by
  have hg := erased_first_memLp_two j
  change MemLp (fun z : LayerObs × LayerObs =>
    z.1.1 + z.2.1 + fixedResidualKernel z) 2 _
  exact ((hg.comp_fst (fixedErasedLaw j)).add
    (hg.comp_snd (fixedErasedLaw j))).add (fixedResidualKernel_memLp_two_fixedErasedLaw j)

private theorem integrable_erased_kernel_pair (j : ℕ) :
    Integrable fixedKernel ((fixedErasedLaw j).prod (fixedErasedLaw j)) :=
  (fixedKernel_memLp_two_fixedErasedLaw j).integrable (by norm_num)

theorem integrable_fixedKernel_row_fixedErasedLaw_ae (j : ℕ) :
    ∀ᵐ o : LayerObs ∂fixedErasedLaw j,
      Integrable (fun o' : LayerObs => fixedKernel (o, o')) (fixedErasedLaw j) :=
  (integrable_erased_kernel_pair j).prod_right_ae

theorem integral_fixedKernel_row_fixedErasedLaw_eq_first_ae (j : ℕ) :
    ∀ᵐ o : LayerObs ∂fixedErasedLaw j,
      (∫ o' : LayerObs, fixedKernel (o, o') ∂fixedErasedLaw j) = o.1 := by
  filter_upwards [integrable_fixedResidualKernel_row_fixedErasedLaw_ae j,
    integral_fixedResidualKernel_row_fixedErasedLaw_eq_zero_ae j] with o hr hz
  change (∫ o' : LayerObs, o.1 + o'.1 + fixedResidualKernel (o, o')
    ∂fixedErasedLaw j) = o.1
  have hs : Integrable (fun o' : LayerObs => o.1 + o'.1) (fixedErasedLaw j) :=
    (integrable_const o.1).add (integrable_fixedErasedLaw_first j)
  rw [integral_add hs hr,
    integral_add (integrable_const o.1) (integrable_fixedErasedLaw_first j),
    integral_fixedErasedLaw_first_eq_zero, hz]
  simp

theorem integral_fixedKernel_fixedErasedLaw_eq_zero (j : ℕ) :
    (∫ z : LayerObs × LayerObs, fixedKernel z
      ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) = 0 := by
  rw [integral_prod fixedKernel (integrable_erased_kernel_pair j)]
  exact (integral_congr_ae (integral_fixedKernel_row_fixedErasedLaw_eq_first_ae j)).trans
    (integral_fixedErasedLaw_first_eq_zero j)

theorem integral_fixedKernel_sq_fixedErasedLaw (j : ℕ) :
    (∫ z : LayerObs × LayerObs, (fixedKernel z) ^ 2
      ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) =
      2 / 3 + ∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
        ∂(fixedErasedLaw j).prod (fixedErasedLaw j) := by
  let β := fixedErasedLaw j
  let Q := β.prod β
  have hg : MemLp (fun o : LayerObs => o.1) 2 β := erased_first_memLp_two j
  have ha : MemLp (fun z : LayerObs × LayerObs => z.1.1) 2 Q := hg.comp_fst β
  have hb : MemLp (fun z : LayerObs × LayerObs => z.2.1) 2 Q := hg.comp_snd β
  have hr : MemLp fixedResidualKernel 2 Q := fixedResidualKernel_memLp_two_fixedErasedLaw j
  have hab : Integrable (fun z : LayerObs × LayerObs => z.1.1 * z.2.1) Q :=
    ha.integrable_mul hb
  have har : Integrable (fun z : LayerObs × LayerObs => z.1.1 * fixedResidualKernel z) Q :=
    ha.integrable_mul hr
  have hbr : Integrable (fun z : LayerObs × LayerObs => z.2.1 * fixedResidualKernel z) Q :=
    hb.integrable_mul hr
  have haa : (∫ z : LayerObs × LayerObs, z.1.1 ^ 2 ∂Q) = 1 / 3 := by
    calc
      _ = ∫ o : LayerObs, o.1 ^ 2 ∂β := by
        simpa only [probReal_univ, one_smul] using
          (integral_fun_fst (μ := β) (ν := β) (fun o : LayerObs => o.1 ^ 2))
      _ = 1 / 3 := integral_fixedErasedLaw_first_sq j
  have hbb : (∫ z : LayerObs × LayerObs, z.2.1 ^ 2 ∂Q) = 1 / 3 := by
    calc
      _ = ∫ o : LayerObs, o.1 ^ 2 ∂β := by
        simpa only [probReal_univ, one_smul] using
          (integral_fun_snd (μ := β) (ν := β) (fun o : LayerObs => o.1 ^ 2))
      _ = 1 / 3 := integral_fixedErasedLaw_first_sq j
  have hab0 : (∫ z : LayerObs × LayerObs, z.1.1 * z.2.1 ∂Q) = 0 := by
    change (∫ z : LayerObs × LayerObs,
      (fun o : LayerObs => o.1) z.1 * (fun o : LayerObs => o.1) z.2 ∂β.prod β) = _
    rw [integral_prod_mul, integral_fixedErasedLaw_first_eq_zero]
    exact zero_mul _
  have har0 : (∫ z : LayerObs × LayerObs, z.1.1 * fixedResidualKernel z ∂Q) = 0 := by
    rw [integral_prod _ har]
    calc
      _ = ∫ _o : LayerObs, (0 : ℝ) ∂β := by
        apply integral_congr_ae
        filter_upwards [integrable_fixedResidualKernel_row_fixedErasedLaw_ae j,
          integral_fixedResidualKernel_row_fixedErasedLaw_eq_zero_ae j] with o hi hz
        have _hrow : Integrable (fun o' : LayerObs =>
            o.1 * fixedResidualKernel (o, o')) β := hi.const_mul o.1
        rw [integral_const_mul, hz, mul_zero]
      _ = 0 := integral_zero _ _
  have hbr0 : (∫ z : LayerObs × LayerObs, z.2.1 * fixedResidualKernel z ∂Q) = 0 := by
    rw [integral_prod_symm _ hbr]
    calc
      _ = ∫ _o : LayerObs, (0 : ℝ) ∂β := by
        apply integral_congr_ae
        filter_upwards [integrable_fixedResidualKernel_row_fixedErasedLaw_ae j,
          integral_fixedResidualKernel_row_fixedErasedLaw_eq_zero_ae j] with o hi hz
        have he : (fun o' : LayerObs => o.1 * fixedResidualKernel (o', o)) =
            (fun o' : LayerObs => o.1 * fixedResidualKernel (o, o')) := by
          funext o'
          rw [fixedResidualKernel_symmetric o' o]
        have _hrow : Integrable (fun o' : LayerObs =>
            o.1 * fixedResidualKernel (o', o)) β := by
          rw [he]
          exact hi.const_mul o.1
        rw [he, integral_const_mul, hz, mul_zero]
      _ = 0 := integral_zero _ _
  have he : (fun z : LayerObs × LayerObs => (fixedKernel z) ^ 2) =
      (fun z => (((z.1.1 ^ 2 + z.2.1 ^ 2) + (fixedResidualKernel z) ^ 2) +
        2 * (z.1.1 * z.2.1)) + 2 * (z.1.1 * fixedResidualKernel z) +
        2 * (z.2.1 * fixedResidualKernel z)) := by
    funext z
    change (z.1.1 + z.2.1 + fixedResidualKernel z) ^ 2 = _
    ring
  have hs0 : Integrable (fun z : LayerObs × LayerObs => z.1.1 ^ 2 + z.2.1 ^ 2) Q :=
    ha.integrable_sq.add hb.integrable_sq
  have hs1 : Integrable (fun z : LayerObs × LayerObs =>
      (z.1.1 ^ 2 + z.2.1 ^ 2) + (fixedResidualKernel z) ^ 2) Q :=
    hs0.add hr.integrable_sq
  have hs2 : Integrable (fun z : LayerObs × LayerObs =>
      ((z.1.1 ^ 2 + z.2.1 ^ 2) + (fixedResidualKernel z) ^ 2) + 2 * (z.1.1 * z.2.1)) Q :=
    hs1.add (hab.const_mul 2)
  have hs3 : Integrable (fun z : LayerObs × LayerObs =>
      (((z.1.1 ^ 2 + z.2.1 ^ 2) + (fixedResidualKernel z) ^ 2) +
        2 * (z.1.1 * z.2.1)) + 2 * (z.1.1 * fixedResidualKernel z)) Q :=
    hs2.add (har.const_mul 2)
  change (∫ z : LayerObs × LayerObs, (fixedKernel z) ^ 2 ∂Q) =
    2 / 3 + ∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2 ∂Q
  rw [he, integral_add hs3 (hbr.const_mul 2), integral_add hs2 (har.const_mul 2),
    integral_add hs1 (hab.const_mul 2), integral_add hs0 hr.integrable_sq,
    integral_add ha.integrable_sq hb.integrable_sq,
    integral_const_mul, integral_const_mul, integral_const_mul, haa, hbb, hab0, har0, hbr0]
  ring

theorem integral_fixedKernel_sq_fixedErasedLaw_le (j : ℕ) :
    (∫ z : LayerObs × LayerObs, (fixedKernel z) ^ 2
      ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) ≤
      2 / 3 + ∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw := by
  rw [integral_fixedKernel_sq_fixedErasedLaw]
  linarith [integral_fixedResidualKernel_sq_fixedErasedLaw_le j]

end
end Shao.OQ5.P52
