import Shao.C1.PermutationEnergyEnvelope
import Shao.Probability.MeasurablePath
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

noncomputable section
namespace Shao.C1.GuardedPermutationIntegrability
open MeasureTheory
open Shao.C1.PermutationEnergyEnvelope

def guardedRemainder {n : ℕ} (σ : Equiv.Perm (Fin n)) (r : Fin n) (H : ℝ)
    (FY Vnext Vnow : Shao.Path n → ℝ) (a : Shao.Path n) : ℝ :=
  if H ≤ revealRemainingEnergy a σ r then
    Vnext a - Vnow a -
      (a (σ r) - (a (σ r)) ^ 2 * revealRemainingSum a σ r / revealRemainingEnergy a σ r) * FY a
  else 0

theorem measurable_guarded_remainder {n : ℕ} (σ : Equiv.Perm (Fin n))
    (r : Fin n) (H : ℝ) (FY Vnext Vnow : Shao.Path n → ℝ)
    (hFY : Measurable FY) (hVnext : Measurable Vnext) (hVnow : Measurable Vnow) :
    Measurable (guardedRemainder σ r H FY Vnext Vnow) := by
  classical
  have hS : Measurable (fun a : Shao.Path n => revealRemainingSum a σ r) := by
    unfold revealRemainingSum
    fun_prop
  have hT : Measurable (fun a : Shao.Path n => revealRemainingEnergy a σ r) := by
    unfold revealRemainingEnergy
    fun_prop
  unfold guardedRemainder
  exact Measurable.ite (measurableSet_le measurable_const hT)
    ((hVnext.sub hVnow).sub
      (((measurable_pi_apply (σ r)).sub
        (((measurable_pi_apply (σ r)).pow_const 2).mul hS |>.div hT)).mul hFY))
    measurable_const

theorem guarded_remainder_bound {n : ℕ} (σ : Equiv.Perm (Fin n))
    (r : Fin n) (H C : ℝ) (hH : 0 < H) (hC : 0 ≤ C)
    (FY Vnext Vnow : Shao.Path n → ℝ)
    (hvNext : ∀ a, 0 ≤ Vnext a ∧ Vnext a ≤ 1)
    (hvNow : ∀ a, 0 ≤ Vnow a ∧ Vnow a ≤ 1)
    (hfy : ∀ a, H ≤ revealRemainingEnergy a σ r →
      |FY a| ≤ C / Real.sqrt (revealRemainingEnergy a σ r) *
        (1 + |revealRemainingSum a σ r| / Real.sqrt (revealRemainingEnergy a σ r))) :
    ∀ a, |guardedRemainder σ r H FY Vnext Vnow a| ≤ 1 + 2 * C * (1 + (n : ℝ)) := by
  intro a
  by_cases ht : H ≤ revealRemainingEnergy a σ r
  · rw [guardedRemainder, if_pos ht]
    have hb := actual_remainder_bound a σ r C (FY a) (Vnext a) (Vnow a) hC
      (hH.trans_le ht) (hfy a ht) (hvNext a) (hvNow a)
    have hcount : ((n - r.val : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n r.val
    exact hb.trans (by nlinarith)
  · rw [guardedRemainder, if_neg ht, abs_zero]
    positivity

theorem guarded_remainder_integrable {n : ℕ}
    (P : Measure (Shao.Path n)) [IsProbabilityMeasure P]
    (σ : Equiv.Perm (Fin n)) (r : Fin n) (H C : ℝ) (hH : 0 < H) (hC : 0 ≤ C)
    (FY Vnext Vnow : Shao.Path n → ℝ)
    (hFY : Measurable FY) (hVnext : Measurable Vnext) (hVnow : Measurable Vnow)
    (hvNext : ∀ a, 0 ≤ Vnext a ∧ Vnext a ≤ 1)
    (hvNow : ∀ a, 0 ≤ Vnow a ∧ Vnow a ≤ 1)
    (hfy : ∀ a, H ≤ revealRemainingEnergy a σ r →
      |FY a| ≤ C / Real.sqrt (revealRemainingEnergy a σ r) *
        (1 + |revealRemainingSum a σ r| / Real.sqrt (revealRemainingEnergy a σ r))) :
    Integrable (guardedRemainder σ r H FY Vnext Vnow) P := by
  refine (integrable_const (1 + 2 * C * (1 + (n : ℝ)))).mono'
    (measurable_guarded_remainder σ r H FY Vnext Vnow hFY hVnext hVnow).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun a => by
    rw [Real.norm_eq_abs]
    exact guarded_remainder_bound σ r H C hH hC FY Vnext Vnow hvNext hvNow hfy a

end Shao.C1.GuardedPermutationIntegrability
