import Shao.C2.AuxiliaryOwnC1Budget
import Shao.Probability.SourceOriginalFullRelative

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Shao.C2.AuxiliaryProductC1Endpoint
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem actual_product_absolute_endpoint_c1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ rhoStar : ℝ, 0 < rhoStar → rhoStar ≤ 1 / 16 →
        ∀ (chi : Measure ℝ) [IsProbabilityMeasure chi],
          Integrable (fun z : ℝ => z ^ 2) chi →
          (∫ z : ℝ, z ∂chi) = 0 →
          (0 < ∫ z : ℝ, z ^ 2 ∂chi) →
          Integrable (fun z : ℝ => |z| ^ 3) chi →
          ∀ (n : ℕ) (hn : 0 < n) (y : ℝ), 0 ≤ y →
            let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂chi
            let eta : Measure ℝ := Measure.map
              (fun z : ℝ => z / (Real.sqrt sigmaSq * Real.sqrt (n : ℝ))) chi
            Shao.truncationBudget eta n y ≤ rhoStar →
            (Measure.pi (fun _ : Fin n => chi)).real
              {v : Shao.Path n | y * Real.sqrt (Shao.energy v) ≤
                |Shao.prefixSum v n|} ≤ C * Shao.standardNormalTail y := by
  classical
  obtain ⟨C0, hC0, hC1⟩ :=
    Shao.Probability.SourceOriginalFullRelative.original_iid_signed_halfline_full_relative_comparison
  refine ⟨4 + 2 * C0, by linarith, ?_⟩
  intro rhoStar hRho0 hRho16 chi _ h2 hMean hSecond h3 n hn y hy sigmaSq eta hBudget
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => chi)
  let X : Fin n → Shao.Path n → ℝ := fun i v => v i
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hX (i : Fin n) : AEMeasurable (X i) P := (measurable_pi_apply i).aemeasurable
  have hLaw (i : Fin n) : IdentDistrib (X i) (id : ℝ → ℝ) P chi := by
    refine ⟨hX i, measurable_id.aemeasurable, ?_⟩
    simpa only [Measure.map_id] using
      (measurePreserving_eval (fun _ : Fin n => chi) i).map_eq
  have hIndep : iIndepFun X P :=
    iIndepFun_pi (X := fun _ : Fin n => (id : ℝ → ℝ))
      (fun _ => measurable_id.aemeasurable)
  have h3p : Integrable (fun z : ℝ => Real.rpow |z| (3 : ℝ)) chi := by
    have hPow : (fun z : ℝ => Real.rpow |z| (3 : ℝ)) =
        (fun z : ℝ => |z| ^ (3 : ℕ)) := by
      funext z
      exact Real.rpow_natCast |z| 3
    rw [hPow]
    exact h3
  let A : ℝ → Set (Shao.Path n) := fun s =>
    {v | y * Real.sqrt (Shao.energy v) ≤ Shao.upperMax (s • v) hn}
  have hTail0 : 0 ≤ Shao.standardNormalTail y :=
    (Shao.standardNormalTail_basic.2.2.1 y).1.le
  have hBudget1 : Shao.truncationBudget eta n y ≤ 1 := by linarith
  have hSigned (s : ℝ) (hs : s = 1 ∨ s = -1) :
      P.real (A s) ≤ (2 + C0) * Shao.standardNormalTail y := by
    have hApply := hC1 rhoStar hRho0 hRho16 (3 : ℝ) (by norm_num) (by norm_num)
      P chi n hn X hX hIndep hLaw h2 hMean hSecond h3p s y hs hy
      ⟨hy, Or.inr hBudget⟩
    have hError := hApply.2.2.2.1
    change |P.real (A s) - 2 * Shao.standardNormalTail y| ≤
      C0 * Shao.truncationBudget eta n y * Shao.standardNormalTail y at hError
    have hPay : C0 * Shao.truncationBudget eta n y * Shao.standardNormalTail y ≤
        C0 * Shao.standardNormalTail y := by
      calc
        _ ≤ C0 * 1 * Shao.standardNormalTail y :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hBudget1 hC0.le) hTail0
        _ = _ := by ring
    have hh := (le_abs_self (P.real (A s) - 2 * Shao.standardNormalTail y)).trans
      (hError.trans hPay)
    nlinarith
  have hSub : {v : Shao.Path n | y * Real.sqrt (Shao.energy v) ≤
      |Shao.prefixSum v n|} ⊆ A 1 ∪ A (-1) := by
    intro v hv
    change y * Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v n| at hv
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn)
    by_cases hS : 0 ≤ Shao.prefixSum v n
    · left
      rw [abs_of_nonneg hS] at hv
      change y * Real.sqrt (Shao.energy v) ≤ Shao.upperMax ((1 : ℝ) • v) hn
      simpa only [one_smul] using hv.trans (Shao.le_upperMax v hn n hn1 le_rfl)
    · right
      rw [abs_of_neg (lt_of_not_ge hS)] at hv
      have hPrefix : Shao.prefixSum ((-1 : ℝ) • v) n = -Shao.prefixSum v n := by
        rw [Shao.prefixSum_smul]
        ring
      have hEndpoint : y * Real.sqrt (Shao.energy v) ≤
          Shao.prefixSum ((-1 : ℝ) • v) n := by rw [hPrefix]; exact hv
      exact hEndpoint.trans (Shao.le_upperMax ((-1 : ℝ) • v) hn n hn1 le_rfl)
  calc
    P.real {v : Shao.Path n | y * Real.sqrt (Shao.energy v) ≤
        |Shao.prefixSum v n|} ≤ P.real (A 1 ∪ A (-1)) := measureReal_mono hSub
    _ ≤ P.real (A 1) + P.real (A (-1)) := measureReal_union_le (A 1) (A (-1))
    _ ≤ (2 + C0) * Shao.standardNormalTail y +
        (2 + C0) * Shao.standardNormalTail y :=
      add_le_add (hSigned 1 (Or.inl rfl)) (hSigned (-1) (Or.inr rfl))
    _ = (4 + 2 * C0) * Shao.standardNormalTail y := by ring

end Shao.C2.AuxiliaryProductC1Endpoint
