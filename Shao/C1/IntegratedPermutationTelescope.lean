import Shao.C1.StoppedPermutationTelescope
import Shao.C1.GuardedPermutationIntegrability
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Count

noncomputable section
namespace Shao.C1.IntegratedPermutationTelescope
open MeasureTheory
open scoped BigOperators ENNReal
open Shao.C1.PermutationEnergyEnvelope Shao.C1.GuardedPermutationIntegrability

def uniformPermutationLaw (n : ℕ) [MeasurableSpace (Equiv.Perm (Fin n))] :
    Measure (Equiv.Perm (Fin n)) :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞)⁻¹ • Measure.count

def stoppedGuardedRemainder {n : ℕ}
    (ν : Shao.Path n → Equiv.Perm (Fin n) → ℕ)
    (V : Shao.Path n → Equiv.Perm (Fin n) → ℕ → ℝ)
    (FY : Shao.Path n → Equiv.Perm (Fin n) → Fin n → ℝ)
    (H : ℝ) (a : Shao.Path n) (σ : Equiv.Perm (Fin n)) (r : Fin n) : ℝ :=
  if r.val < ν a σ then
    guardedRemainder σ r H (fun b => FY b σ r)
      (fun b => V b σ (r.val + 1)) (fun b => V b σ r.val) a
  else 0

theorem uniformPermutationLaw_isProbability (n : ℕ)
    [MeasurableSpace (Equiv.Perm (Fin n))] :
    IsProbabilityMeasure (uniformPermutationLaw n) := by
  constructor
  have hc : (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simpa [uniformPermutationLaw, Measure.smul_apply, Measure.count_univ,
    ENat.card_eq_coe_fintype_card] using (ENNReal.inv_mul_cancel hc (by simp))

theorem integral_uniformPermutationLaw (n : ℕ)
    [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))]
    (f : Equiv.Perm (Fin n) → ℝ) :
    (∫ σ, f σ ∂(uniformPermutationLaw n)) =
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ * ∑ σ, f σ := by
  rw [uniformPermutationLaw, integral_smul_measure, integral_count]
  simp

theorem integrated_stopped_compensation (n : ℕ)
    [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))]
    (P : Measure (Shao.Path n)) [IsProbabilityMeasure P]
    (ν : Shao.Path n → Equiv.Perm (Fin n) → ℕ)
    (hν : ∀ a σ, ν a σ ≤ n)
    (hνmeas : ∀ σ, Measurable (fun a => ν a σ))
    (hνobs : ∀ (a : Shao.Path n) (r : Fin n) (σ τ : Equiv.Perm (Fin n)),
      (∀ i : Fin n, i.val < r.val → σ i = τ i) →
        (r.val < ν a σ ↔ r.val < ν a τ))
    (V : Shao.Path n → Equiv.Perm (Fin n) → ℕ → ℝ)
    (hVmeas : ∀ σ k, Measurable (fun a => V a σ k))
    (hVbounds : ∀ a σ k, 0 ≤ V a σ k ∧ V a σ k ≤ 1)
    (FY : Shao.Path n → Equiv.Perm (Fin n) → Fin n → ℝ)
    (hFYmeas : ∀ σ r, Measurable (fun a => FY a σ r))
    (hFYobs : ∀ (a : Shao.Path n) (r : Fin n) (σ τ : Equiv.Perm (Fin n)),
      (∀ i : Fin n, i.val < r.val → σ i = τ i) → FY a σ r = FY a τ r)
    (H C : ℝ) (hH : 0 < H) (hC : 0 ≤ C)
    (hcutoff : ∀ (a : Shao.Path n) (σ : Equiv.Perm (Fin n)) (r : Fin n),
      r.val < ν a σ → H ≤ revealRemainingEnergy a σ r)
    (hfy : ∀ (a : Shao.Path n) (σ : Equiv.Perm (Fin n)) (r : Fin n),
      H ≤ revealRemainingEnergy a σ r →
        |FY a σ r| ≤ C / Real.sqrt (revealRemainingEnergy a σ r) *
          (1 + |revealRemainingSum a σ r| / Real.sqrt (revealRemainingEnergy a σ r)))
    (m : Shao.Path n → ℝ) (hmmeas : Measurable m) (hmabs : ∀ a, |m a| ≤ 1)
    (hminvariant : ∀ (a : Shao.Path n) (τ : Equiv.Perm (Fin n)),
      m (fun i => a (τ i)) = m a) :
    Integrable (fun a => ∫ σ, m a * (V a σ (ν a σ) - V a σ 0)
      ∂(uniformPermutationLaw n)) P ∧
    Integrable (fun a => ∫ σ, m a * (∑ r : Fin n, stoppedGuardedRemainder ν V FY H a σ r)
      ∂(uniformPermutationLaw n)) P ∧
    (∫ a, ∫ σ, m a * (V a σ (ν a σ) - V a σ 0) ∂(uniformPermutationLaw n) ∂P) =
      ∫ a, ∫ σ, m a * (∑ r : Fin n, stoppedGuardedRemainder ν V FY H a σ r)
        ∂(uniformPermutationLaw n) ∂P
 := by
  classical
  -- The bounded stopping rank has a finite measurable selection of the V sections.
  have hstopmeas (σ : Equiv.Perm (Fin n)) :
      Measurable (fun a => V a σ (ν a σ)) := by
    have hrepr (a : Shao.Path n) :
        (∑ k ∈ Finset.range (n + 1), if ν a σ = k then V a σ k else 0) =
          V a σ (ν a σ) := by
      rw [Finset.sum_eq_single (ν a σ)]
      · simp
      · intro k _ hk
        exact ite_eq_right (Ne.symm hk)
      · intro hk
        exact False.elim (hk (Finset.mem_range.mpr (Nat.lt_succ_of_le (hν a σ))))
    have hsum : Measurable (fun a : Shao.Path n =>
        ∑ k ∈ Finset.range (n + 1), if ν a σ = k then V a σ k else 0) := by
      exact (Finset.range (n + 1)).measurable_fun_sum fun k _ =>
        Measurable.ite (measurableSet_eq_fun (hνmeas σ) measurable_const)
          (hVmeas σ k) measurable_const
    simpa only [hrepr] using hsum
  have hmask : ∀ᵐ a ∂P, ‖m a‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun a => by simpa only [Real.norm_eq_abs] using hmabs a
  have hleftsection (σ : Equiv.Perm (Fin n)) :
      Integrable (fun a => m a * (V a σ (ν a σ) - V a σ 0)) P := by
    have hd : Integrable (fun a => V a σ (ν a σ) - V a σ 0) P := by
      refine (integrable_const (1 : ℝ)).mono'
        ((hstopmeas σ).sub (hVmeas σ 0)).aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [(hVbounds a σ (ν a σ)).1, (hVbounds a σ 0).2],
          by linarith [(hVbounds a σ (ν a σ)).2, (hVbounds a σ 0).1]⟩
    exact hd.bdd_mul hmmeas.aestronglyMeasurable hmask
  -- Each original guarded summand is integrable before finite averaging.
  have hrightsummand (σ : Equiv.Perm (Fin n)) (r : Fin n) :
      Integrable (fun a => stoppedGuardedRemainder ν V FY H a σ r) P := by
    have hg := guarded_remainder_integrable P σ r H C hH hC
      (fun a => FY a σ r) (fun a => V a σ (r.val + 1)) (fun a => V a σ r.val)
      (hFYmeas σ r) (hVmeas σ (r.val + 1)) (hVmeas σ r.val)
      (fun a => hVbounds a σ (r.val + 1)) (fun a => hVbounds a σ r.val)
      (fun a ht => hfy a σ r ht)
    have hi := hg.indicator (s := {a : Shao.Path n | r.val < ν a σ})
      (measurableSet_lt measurable_const (hνmeas σ))
    convert hi using 1
    ext a
    simp only [stoppedGuardedRemainder, Set.indicator_apply, Set.mem_setOf_eq]
  have hrightsection (σ : Equiv.Perm (Fin n)) :
      Integrable (fun a => m a * (∑ r : Fin n, stoppedGuardedRemainder ν V FY H a σ r)) P :=
    (integrable_finsetSum Finset.univ (fun r _ => hrightsummand σ r)).bdd_mul
      hmmeas.aestronglyMeasurable hmask
  have hleft : Integrable (fun a => ∫ σ, m a * (V a σ (ν a σ) - V a σ 0)
      ∂(uniformPermutationLaw n)) P := by
    simpa only [integral_uniformPermutationLaw] using
      (integrable_finsetSum Finset.univ (fun σ _ => hleftsection σ)).const_mul
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹
  have hright : Integrable (fun a => ∫ σ, m a *
      (∑ r : Fin n, stoppedGuardedRemainder ν V FY H a σ r)
      ∂(uniformPermutationLaw n)) P := by
    simpa only [integral_uniformPermutationLaw] using
      (integrable_finsetSum Finset.univ (fun σ _ => hrightsection σ)).const_mul
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹
  have hpoint (a : Shao.Path n) :
      (∫ σ, m a * (V a σ (ν a σ) - V a σ 0) ∂(uniformPermutationLaw n)) =
        ∫ σ, m a * (∑ r : Fin n, stoppedGuardedRemainder ν V FY H a σ r)
          ∂(uniformPermutationLaw n) := by
    have hf := PermutationCompensation.finite_stopped_compensation n a (ν a) (hν a)
      (hνobs a) (FY a) (hFYobs a) H hH (hcutoff a) (V a)
    have hguard : (∑ σ : Equiv.Perm (Fin n), (V a σ (ν a σ) - V a σ 0)) =
        ∑ σ : Equiv.Perm (Fin n), ∑ r : Fin n,
          stoppedGuardedRemainder ν V FY H a σ r := by
      rw [hf]
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro r _
      by_cases hs : r.val < ν a σ
      · simp only [stoppedGuardedRemainder, ite_eq_left hs, guardedRemainder,
          ite_eq_left (hcutoff a σ r hs)]
        dsimp only [revealRemainingSum, revealRemainingEnergy]
        ring
      · simp only [stoppedGuardedRemainder, ite_eq_right hs]
    rw [integral_uniformPermutationLaw, integral_uniformPermutationLaw]
    simpa only [Finset.mul_sum] using congrArg
      (fun z : ℝ => (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ * (m a * z)) hguard
  exact ⟨hleft, hright, integral_congr_ae (Filter.Eventually.of_forall hpoint)⟩

end Shao.C1.IntegratedPermutationTelescope
