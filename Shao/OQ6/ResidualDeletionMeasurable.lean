import Shao.OQ6.ResidualDeletion
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Deleted residual statistics on the complete retained observations

Original p38, line 68, and p39, lines 129–134. The matrix retains its original
Fin n index type. The witnesses use retained observations directly, without
choosing a value for the deleted observation. This file asserts no integrability
or tilted probability estimate.
-/

set_option autoImplicit false

universe u

namespace Shao.OQ6.ResidualDeletion

noncomputable section

open scoped BigOperators

variable {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}

theorem erasedSampleMatrix_measurable_factorization
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun p : Ω × Ω => r p.1 p.2)) (i : Fin n) :
    ∃ Φ : ({j : Fin n // j ≠ i} → Ω) → (Fin n → Fin n → ℝ),
      Measurable Φ ∧
        ∀ ξ : Fin n → Ω,
          eraseIncident (fun j k => r (ξ j) (ξ k)) i =
            Φ (fun j => ξ j.val) := by
  classical
  let Φ : ({j : Fin n // j ≠ i} → Ω) → (Fin n → Fin n → ℝ) :=
    fun η j k =>
      if hj : j = i then 0 else
      if hk : k = i then 0 else
        r (η ⟨j, hj⟩) (η ⟨k, hk⟩)
  have hΦ : Measurable Φ := by
    apply Measurable.of_eval
    intro j
    apply Measurable.of_eval
    intro k
    by_cases hj : j = i
    · simpa only [Φ, dif_pos hj] using
        (measurable_const :
          Measurable (fun _ : ({j : Fin n // j ≠ i} → Ω) => (0 : ℝ)))
    · by_cases hk : k = i
      · simpa only [Φ, dif_neg hj, dif_pos hk] using
          (measurable_const :
            Measurable (fun _ : ({j : Fin n // j ≠ i} → Ω) => (0 : ℝ)))
      · have hjm :
            Measurable (fun η : ({j : Fin n // j ≠ i} → Ω) => η ⟨j, hj⟩) :=
          measurable_pi_apply _
        have hkm :
            Measurable (fun η : ({j : Fin n // j ≠ i} → Ω) => η ⟨k, hk⟩) :=
          measurable_pi_apply _
        simpa only [Φ, dif_neg hj, dif_neg hk, Function.comp_def] using hr.comp (hjm.prodMk hkm)
  refine ⟨Φ, hΦ, ?_⟩
  intro ξ
  funext j k
  by_cases hj : j = i
  · simp [eraseIncident, Φ, hj]
  · by_cases hk : k = i
    · simp [eraseIncident, Φ, hj, hk]
    · simp [eraseIncident, Φ, hj, hk]

theorem erasedSamplePairSum_measurable_factorization
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun p : Ω × Ω => r p.1 p.2)) (i : Fin n) :
    ∃ F : ({j : Fin n // j ≠ i} → Ω) → ℝ,
      Measurable F ∧
        ∀ ξ : Fin n → Ω,
          Shao.OQ5.P35.unorderedPairSum
            (eraseIncident (fun j k => r (ξ j) (ξ k)) i) =
              F (fun j => ξ j.val) := by
  classical
  obtain ⟨Φ, hΦ, hfactor⟩ := erasedSampleMatrix_measurable_factorization r hr i
  have hentry (j k : Fin n) :
      Measurable (fun η : ({j : Fin n // j ≠ i} → Ω) => Φ η j k) :=
    (measurable_pi_apply k).comp ((measurable_pi_apply j).comp hΦ)
  let F : ({j : Fin n // j ≠ i} → Ω) → ℝ :=
    fun η => Shao.OQ5.P35.unorderedPairSum (Φ η)
  refine ⟨F, ?_, ?_⟩
  · unfold F Shao.OQ5.P35.unorderedPairSum
    apply Finset.measurable_sum
    intro j _
    apply Finset.measurable_sum
    intro k _
    by_cases hjk : j < k
    · simpa only [hjk, ite_true] using hentry j k
    · simp only [hjk, ite_false]
      exact measurable_const
  · intro ξ
    dsimp only [F]
    rw [hfactor ξ]

theorem erasedSampleRowSqSum_measurable_factorization
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun p : Ω × Ω => r p.1 p.2)) (i : Fin n) :
    ∃ Λ : ({j : Fin n // j ≠ i} → Ω) → ℝ,
      Measurable Λ ∧
        ∀ ξ : Fin n → Ω,
          (∑ j : Fin n,
            rowSum (eraseIncident (fun j k => r (ξ j) (ξ k)) i) j ^ 2) =
              Λ (fun j => ξ j.val) := by
  classical
  obtain ⟨Φ, hΦ, hfactor⟩ := erasedSampleMatrix_measurable_factorization r hr i
  have hentry (j k : Fin n) :
      Measurable (fun η : ({j : Fin n // j ≠ i} → Ω) => Φ η j k) :=
    (measurable_pi_apply k).comp ((measurable_pi_apply j).comp hΦ)
  have hrow (j : Fin n) :
      Measurable (fun η : ({j : Fin n // j ≠ i} → Ω) => rowSum (Φ η) j) := by
    unfold rowSum
    exact Finset.measurable_sum _ (fun k _ => hentry j k)
  let E : ({j : Fin n // j ≠ i} → Ω) → ℝ :=
    fun η => ∑ j : Fin n, rowSum (Φ η) j ^ 2
  refine ⟨E, ?_, ?_⟩
  · dsimp only [E]
    exact Finset.measurable_sum _ (fun j _ => (hrow j).pow_const 2)
  · intro ξ
    dsimp only [E]
    rw [hfactor ξ]

end

end Shao.OQ6.ResidualDeletion
