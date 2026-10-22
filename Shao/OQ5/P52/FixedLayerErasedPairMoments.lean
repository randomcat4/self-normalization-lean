import Shao.OQ5.P52.FixedLayerErasedEdgeMoments

/-!
# Actual erased unordered residual pair-sum moments

Genuine finite-sum L2 and edge-product L1 precede every finite integral
expansion. Increasing endpoint pairs count each unordered edge once.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped BigOperators

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

attribute [local instance] fixedErasedLaw_isProbabilityMeasure

def fixedErasedResidualPairSum {n : ℕ} (x : Fin n → LayerObs) : ℝ :=
  Shao.OQ5.P35.unorderedPairSum
    (fun i k => fixedResidualKernel (x i, x k))

private def guardedEdge {n : ℕ} (a b : Fin n) (x : Fin n → LayerObs) : ℝ :=
  if a < b then fixedResidualKernel (x a, x b) else 0

private theorem guarded_memLp (j n : ℕ) (a b : Fin n) :
    MemLp (guardedEdge a b) 2 (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) := by
  change MemLp (fun x : Fin n → LayerObs =>
    if a < b then fixedResidualKernel (x a, x b) else 0) 2
    (Measure.pi (fun _ : Fin n => fixedErasedLaw j))
  by_cases hab : a < b
  · simpa only [guardedEdge, hab, ite_true] using
      fixedErasedResidualEdge_memLp_two j n a b hab.ne
  · simpa only [guardedEdge, hab, ite_false] using
      (memLp_const (0 : ℝ) : MemLp (fun _ : Fin n → LayerObs => (0 : ℝ)) 2
        (Measure.pi (fun _ : Fin n => fixedErasedLaw j)))

private theorem guarded_integral (j n : ℕ) (a b : Fin n) :
    (∫ x : Fin n → LayerObs, guardedEdge a b x
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = 0 := by
  have _hI := (guarded_memLp j n a b).integrable (by norm_num)
  by_cases hab : a < b
  · simpa only [guardedEdge, hab, ite_true] using
      integral_fixedErasedResidualEdge_eq_zero j n a b hab.ne
  · simp only [guardedEdge, hab, ite_false, integral_zero]

theorem fixedErasedResidualPairSum_memLp_two (j n : ℕ) :
    MemLp (fixedErasedResidualPairSum (n := n)) 2
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) := by
  change MemLp (fun x : Fin n → LayerObs =>
    ∑ a : Fin n, ∑ b : Fin n, guardedEdge a b x) 2
    (Measure.pi (fun _ : Fin n => fixedErasedLaw j))
  exact memLp_finsetSum Finset.univ (fun a _ =>
    memLp_finsetSum Finset.univ (fun b _ => guarded_memLp j n a b))

theorem integral_fixedErasedResidualPairSum_eq_zero (j n : ℕ) :
    (∫ x : Fin n → LayerObs, fixedErasedResidualPairSum x
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = 0 := by
  have hI (a b : Fin n) := (guarded_memLp j n a b).integrable (by norm_num)
  change (∫ x : Fin n → LayerObs, ∑ a : Fin n, ∑ b : Fin n, guardedEdge a b x
    ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = 0
  rw [integral_finsetSum Finset.univ
    (fun a _ => integrable_finsetSum Finset.univ (fun b _ => hI a b))]
  calc
    _ = ∑ a : Fin n, ∑ b : Fin n,
        ∫ x : Fin n → LayerObs, guardedEdge a b x
          ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j) := by
      apply Finset.sum_congr rfl
      intro a _
      exact integral_finsetSum Finset.univ (fun b _ => hI a b)
    _ = 0 := by simp only [guarded_integral, Finset.sum_const_zero]

private theorem increasing_pair_unique {n : ℕ} (a b c d : Fin n)
    (hab : a < b) (hcd : c < d)
    (hsets : ({a, b} : Finset (Fin n)) = {c, d}) : a = c ∧ b = d := by
  have ha : a = c ∨ a = d := by
    have hm : a ∈ ({c, d} : Finset (Fin n)) := by rw [← hsets]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  rcases ha with hac | had
  · subst c
    have hb : b = a ∨ b = d := by
      have hm : b ∈ ({a, d} : Finset (Fin n)) := by rw [← hsets]; simp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    rcases hb with hba | hbd
    · exact False.elim (hab.ne hba.symm)
    · exact ⟨rfl, hbd⟩
  · subst d
    have hb : b = c := by
      have hm : b ∈ ({c, a} : Finset (Fin n)) := by rw [← hsets]; simp
      rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hm :
        b = c ∨ b = a) with hbc | hba
      · exact hbc
      · exact False.elim (hab.ne hba.symm)
    have hba : b < a := by simpa only [hb] using hcd
    exact False.elim (lt_asymm hab hba)

private theorem edge_guarded_moment (j n : ℕ) (a b c d : Fin n) (hab : a < b) :
    (∫ x : Fin n → LayerObs, fixedResidualKernel (x a, x b) * guardedEdge c d x
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) =
      if a = c ∧ b = d then
        ∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂(fixedErasedLaw j).prod (fixedErasedLaw j)
      else 0 := by
  have _hI := (fixedErasedResidualEdge_memLp_two j n a b hab.ne).integrable_mul
    (guarded_memLp j n c d)
  by_cases hcd : c < d
  · have heq : (({a, b} : Finset (Fin n)) = {c, d}) ↔ a = c ∧ b = d := by
      refine ⟨increasing_pair_unique a b c d hab hcd, ?_⟩
      rintro ⟨rfl, rfl⟩
      rfl
    simpa only [guardedEdge, hcd, ite_true, heq] using
      integral_fixedErasedResidualEdge_mul j n a b c d hab.ne hcd.ne
  · have hne : ¬ (a = c ∧ b = d) := by
      rintro ⟨rfl, rfl⟩
      exact hcd hab
    simp only [guardedEdge, hcd, ite_false, mul_zero, integral_zero, hne]

private theorem edge_mul_pair_sum (j n : ℕ) (a b : Fin n) (hab : a < b) :
    (∫ x : Fin n → LayerObs,
      fixedResidualKernel (x a, x b) * fixedErasedResidualPairSum x
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) =
      ∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
        ∂(fixedErasedLaw j).prod (fixedErasedLaw j) := by
  have hI (c d : Fin n) : Integrable (fun x : Fin n → LayerObs =>
      fixedResidualKernel (x a, x b) * guardedEdge c d x)
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) :=
    (fixedErasedResidualEdge_memLp_two j n a b hab.ne).integrable_mul
      (guarded_memLp j n c d)
  change (∫ x : Fin n → LayerObs,
    fixedResidualKernel (x a, x b) * (∑ c : Fin n, ∑ d : Fin n, guardedEdge c d x)
    ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = _
  simp only [Finset.mul_sum]
  rw [integral_finsetSum Finset.univ
    (fun c _ => integrable_finsetSum Finset.univ (fun d _ => hI c d))]
  calc
    _ = ∑ c : Fin n, ∑ d : Fin n,
        ∫ x : Fin n → LayerObs, fixedResidualKernel (x a, x b) * guardedEdge c d x
          ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j) := by
      apply Finset.sum_congr rfl
      intro c _
      exact integral_finsetSum Finset.univ (fun d _ => hI c d)
    _ = _ := by
      simp_rw [edge_guarded_moment j n a b _ _ hab]
      simp [ite_and]

private theorem unordered_constant (n : ℕ) (v : ℝ) :
    Shao.OQ5.P35.unorderedPairSum (fun _ _ : Fin n => v) = (n.choose 2 : ℝ) * v := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [Shao.OQ5.P35.unorderedPairSum]
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hrows (i : Fin n) : (∑ k ∈ Finset.univ.erase i, v) = ((n - 1 : ℕ) : ℝ) * v := by
    simp
  have hc : (n : ℝ) * (((n - 1 : ℕ) : ℝ) * v) =
      2 * Shao.OQ5.P35.unorderedPairSum (fun _ _ : Fin n => v) := by
    simpa only [hrows, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      using Shao.OQ5.P35.offDiagonalSum_eq_two_unordered
        (fun _ _ : Fin n => v) (fun _ _ => rfl)
  have hncast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    simpa only [Nat.cast_one] using (Nat.cast_sub hn1 : ((n - 1 : ℕ) : ℝ) = _)
  rw [hncast] at hc
  rw [← Shao.OQ5.P35.pairCount_eq_choose]
  unfold Shao.OQ5.P35.pairCount
  apply mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0)
  calc
    _ = (n : ℝ) * (((n : ℝ) - 1) * v) := hc.symm
    _ = _ := by ring

theorem integral_fixedErasedResidualPairSum_sq (j n : ℕ) :
    (∫ x : Fin n → LayerObs, (fixedErasedResidualPairSum x) ^ 2
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) =
      (n.choose 2 : ℝ) *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) := by
  have hI (a b : Fin n) : Integrable (fun x : Fin n → LayerObs =>
      guardedEdge a b x * fixedErasedResidualPairSum x)
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) :=
    (guarded_memLp j n a b).integrable_mul (fixedErasedResidualPairSum_memLp_two j n)
  have _hSq := (fixedErasedResidualPairSum_memLp_two j n).integrable_sq
  calc
    _ = ∫ x : Fin n → LayerObs,
        ∑ a : Fin n, ∑ b : Fin n, guardedEdge a b x * fixedErasedResidualPairSum x
        ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        dsimp only
        rw [pow_two]
        change (∑ a : Fin n, ∑ b : Fin n, guardedEdge a b x) *
          fixedErasedResidualPairSum x = _
        simp only [Finset.sum_mul])
    _ = ∑ a : Fin n, ∑ b : Fin n,
        ∫ x : Fin n → LayerObs, guardedEdge a b x * fixedErasedResidualPairSum x
          ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j) := by
      rw [integral_finsetSum Finset.univ
        (fun a _ => integrable_finsetSum Finset.univ (fun b _ => hI a b))]
      apply Finset.sum_congr rfl
      intro a _
      exact integral_finsetSum Finset.univ (fun b _ => hI a b)
    _ = Shao.OQ5.P35.unorderedPairSum (fun _ _ : Fin n =>
        ∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) := by
      unfold Shao.OQ5.P35.unorderedPairSum
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases hab : a < b
      · simpa only [guardedEdge, hab, ite_true] using edge_mul_pair_sum j n a b hab
      · simp only [guardedEdge, hab, ite_false, zero_mul, integral_zero]
    _ = _ := unordered_constant n _

end
end Shao.OQ5.P52
