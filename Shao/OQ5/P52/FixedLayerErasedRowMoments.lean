import Shao.OQ5.P52.FixedLayerErasedEdgeMoments

/-!
# Actual erased residual rows and their centered energy

Finite sums retain only off-diagonal edges. The unordered-edge moment
identity counts equal neighbors on one row and the single reversed edge
between distinct rows. All integral interchanges have genuine L1 inputs.
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

attribute [local instance] fixedErasedLaw_isProbabilityMeasure

def fixedErasedResidualRow {n : ℕ} (i : Fin n) (x : Fin n → LayerObs) : ℝ :=
  ∑ k ∈ Finset.univ.erase i, fixedResidualKernel (x i, x k)

theorem fixedErasedResidualRow_memLp_two (j n : ℕ) (i : Fin n) :
    MemLp (fixedErasedResidualRow i) 2
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) := by
  classical
  unfold fixedErasedResidualRow
  exact memLp_finsetSum _ fun k hk =>
    fixedErasedResidualEdge_memLp_two j n i k (Finset.mem_erase.mp hk).1.symm

theorem integral_fixedErasedResidualRow_eq_zero (j n : ℕ) (i : Fin n) :
    (∫ x : Fin n → LayerObs, fixedErasedResidualRow i x
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = 0 := by
  classical
  unfold fixedErasedResidualRow
  rw [integral_finsetSum _ (fun k hk =>
    (fixedErasedResidualEdge_memLp_two j n i k
      (Finset.mem_erase.mp hk).1.symm).integrable (by norm_num))]
  exact Finset.sum_eq_zero fun k hk =>
    integral_fixedErasedResidualEdge_eq_zero j n i k (Finset.mem_erase.mp hk).1.symm

theorem integrable_fixedErasedResidualRow_mul
    (j n : ℕ) (i k : Fin n) :
    Integrable (fun x : Fin n → LayerObs =>
      fixedErasedResidualRow i x * fixedErasedResidualRow k x)
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) :=
  (fixedErasedResidualRow_memLp_two j n i).integrable_mul
    (fixedErasedResidualRow_memLp_two j n k)

private theorem pair_same_center (n : ℕ) (i a b : Fin n) (hai : a ≠ i) :
    (({i, a} : Finset (Fin n)) = {i, b}) ↔ a = b := by
  classical
  constructor
  · intro hs
    have hm : a ∈ ({i, b} : Finset (Fin n)) := by rw [← hs]; simp
    exact (show a = i ∨ a = b by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm).resolve_left hai
  · intro h
    rw [h]

private theorem pair_different_centers (n : ℕ) (i k a b : Fin n) (hik : i ≠ k) :
    (({i, a} : Finset (Fin n)) = {k, b}) ↔ a = k ∧ b = i := by
  classical
  constructor
  · intro hs
    have hi : i = k ∨ i = b := by
      have hm : i ∈ ({k, b} : Finset (Fin n)) := by rw [← hs]; simp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    have hk : k = i ∨ k = a := by
      have hm : k ∈ ({i, a} : Finset (Fin n)) := by rw [hs]; simp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    exact ⟨(hk.resolve_left hik.symm).symm, (hi.resolve_left hik).symm⟩
  · rintro ⟨rfl, rfl⟩
    exact Finset.pair_comm _ _

private theorem row_edge_count (n : ℕ) (i k : Fin n) (V : ℝ) :
    (∑ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase k,
      if ({i, a} : Finset (Fin n)) = {k, b} then V else 0) =
      (if i = k then ((n - 1 : ℕ) : ℝ) else 1) * V := by
  classical
  by_cases hik : i = k
  · subst k
    rw [ite_eq_left rfl]
    calc
      _ = ∑ a ∈ Finset.univ.erase i, V := by
        apply Finset.sum_congr rfl
        intro a ha
        simp_rw [pair_same_center n i a _ (Finset.mem_erase.mp ha).1]
        exact Finset.sum_ite_eq_of_mem _ a (fun _ => V) ha
      _ = _ := by simp [nsmul_eq_mul]
  · rw [ite_eq_right hik]
    calc
      _ = ∑ a ∈ Finset.univ.erase i, if a = k then V else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        simp_rw [pair_different_centers n i k a _ hik]
        by_cases hak : a = k
        · simp only [hak, true_and, ite_true]
          exact Finset.sum_ite_eq_of_mem' _ i (fun _ => V)
            (Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩)
        · simp [hak]
      _ = V := Finset.sum_ite_eq_of_mem' _ k (fun _ => V)
        (Finset.mem_erase.mpr ⟨Ne.symm hik, Finset.mem_univ k⟩)
      _ = _ := (one_mul V).symm

theorem integral_fixedErasedResidualRow_mul (j n : ℕ) (i k : Fin n) :
    (∫ x : Fin n → LayerObs,
      fixedErasedResidualRow i x * fixedErasedResidualRow k x
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) =
      (if i = k then ((n - 1 : ℕ) : ℝ) else 1) *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) := by
  classical
  have hprod (a : Fin n) (ha : a ∈ Finset.univ.erase i)
      (b : Fin n) (hb : b ∈ Finset.univ.erase k) :
      Integrable (fun x : Fin n → LayerObs =>
        fixedResidualKernel (x i, x a) * fixedResidualKernel (x k, x b))
        (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) :=
    integrable_fixedErasedResidualEdge_mul j n i a k b
      (Finset.mem_erase.mp ha).1.symm (Finset.mem_erase.mp hb).1.symm
  calc
    _ = ∫ x : Fin n → LayerObs,
        ∑ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase k,
          fixedResidualKernel (x i, x a) * fixedResidualKernel (x k, x b)
        ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        Finset.sum_mul_sum _ _ _ _
    _ = ∑ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase k,
        ∫ x : Fin n → LayerObs,
          fixedResidualKernel (x i, x a) * fixedResidualKernel (x k, x b)
        ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j) := by
      rw [integral_finsetSum _ (fun a ha =>
        integrable_finsetSum _ (fun b hb => hprod a ha b hb))]
      apply Finset.sum_congr rfl
      intro a ha
      exact integral_finsetSum _ (fun b hb => hprod a ha b hb)
    _ = ∑ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase k,
        if ({i, a} : Finset (Fin n)) = {k, b} then
          ∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
            ∂(fixedErasedLaw j).prod (fixedErasedLaw j)
        else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact integral_fixedErasedResidualEdge_mul j n i a k b
        (Finset.mem_erase.mp ha).1.symm (Finset.mem_erase.mp hb).1.symm
    _ = _ := row_edge_count n i k _

private theorem total_rows_memLp_two (j n : ℕ) :
    MemLp (fun x : Fin n → LayerObs => ∑ i : Fin n, fixedErasedResidualRow i x) 2
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) :=
  memLp_finsetSum Finset.univ (fun i _ => fixedErasedResidualRow_memLp_two j n i)

theorem integrable_fixedErasedResidualCenteredRows_sq (j n : ℕ) :
    Integrable (fun x : Fin n → LayerObs =>
      ∑ i : Fin n,
        (fixedErasedResidualRow i x -
          (n : ℝ)⁻¹ * ∑ k : Fin n, fixedErasedResidualRow k x) ^ 2)
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) := by
  exact integrable_finsetSum Finset.univ (fun i _ =>
    ((fixedErasedResidualRow_memLp_two j n i).sub
      ((total_rows_memLp_two j n).const_mul (n : ℝ)⁻¹)).integrable_sq)

private theorem centered_finite_sum (n : ℕ) (hn : 0 < n) (v : Fin n → ℝ) :
    (∑ i : Fin n, (v i - (n : ℝ)⁻¹ * ∑ k : Fin n, v k) ^ 2) =
      (∑ i : Fin n, (v i) ^ 2) - (n : ℝ)⁻¹ * (∑ k : Fin n, v k) ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  let S : ℝ := ∑ k : Fin n, v k
  calc
    _ = ∑ i : Fin n,
        ((v i) ^ 2 - (2 * ((n : ℝ)⁻¹ * S)) * v i + ((n : ℝ)⁻¹ * S) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [S]
      ring
    _ = (∑ i : Fin n, (v i) ^ 2) - (2 * ((n : ℝ)⁻¹ * S)) * S +
        (n : ℝ) * ((n : ℝ)⁻¹ * S) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rfl
    _ = _ := by
      dsimp only [S]
      field_simp [hn0]
      ring

private theorem row_covariance_sum (n : ℕ) (i : Fin n) (V : ℝ) :
    (∑ k : Fin n, (if i = k then ((n - 1 : ℕ) : ℝ) else 1) * V) =
      2 * ((n - 1 : ℕ) : ℝ) * V := by
  classical
  rw [← Finset.sum_erase_add Finset.univ
    (fun k : Fin n => (if i = k then ((n - 1 : ℕ) : ℝ) else 1) * V)
    (Finset.mem_univ i)]
  have he : (∑ k ∈ Finset.univ.erase i,
      (if i = k then ((n - 1 : ℕ) : ℝ) else 1) * V) =
      ((n - 1 : ℕ) : ℝ) * V := by
    calc
      _ = ∑ k ∈ Finset.univ.erase i, V := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [ite_eq_right (Finset.mem_erase.mp hk).1.symm, one_mul]
      _ = _ := by simp [nsmul_eq_mul]
  rw [he, ite_eq_left rfl]
  ring

private theorem integral_row_square_sum (j n : ℕ) :
    (∫ x : Fin n → LayerObs, ∑ i : Fin n, (fixedErasedResidualRow i x) ^ 2
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) =
      (n : ℝ) * ((n - 1 : ℕ) : ℝ) *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) := by
  classical
  rw [integral_finsetSum Finset.univ (fun i _ =>
    (fixedErasedResidualRow_memLp_two j n i).integrable_sq)]
  calc
    _ = ∑ i : Fin n,
        ((n - 1 : ℕ) : ℝ) *
          (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
            ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) := by
      apply Finset.sum_congr rfl
      intro i _
      have h := integral_fixedErasedResidualRow_mul j n i i
      rw [ite_eq_left rfl] at h
      simpa only [pow_two] using h
    _ = _ := by simp [nsmul_eq_mul, mul_assoc]

private theorem integral_total_rows_square (j n : ℕ) :
    (∫ x : Fin n → LayerObs, (∑ i : Fin n, fixedErasedResidualRow i x) ^ 2
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) =
      2 * (n : ℝ) * ((n - 1 : ℕ) : ℝ) *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) := by
  classical
  calc
    _ = ∫ x : Fin n → LayerObs,
        ∑ i : Fin n, ∑ k : Fin n, fixedErasedResidualRow i x * fixedErasedResidualRow k x
        ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [pow_two]
        exact Fintype.sum_mul_sum _ _
    _ = ∑ i : Fin n, ∑ k : Fin n,
        ∫ x : Fin n → LayerObs, fixedErasedResidualRow i x * fixedErasedResidualRow k x
        ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j) := by
      rw [integral_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum Finset.univ (fun k _ => integrable_fixedErasedResidualRow_mul j n i k))]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum Finset.univ (fun k _ => integrable_fixedErasedResidualRow_mul j n i k)
    _ = ∑ i : Fin n, ∑ k : Fin n,
        (if i = k then ((n - 1 : ℕ) : ℝ) else 1) *
          (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
            ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      exact integral_fixedErasedResidualRow_mul j n i k
    _ = ∑ _i : Fin n, 2 * ((n - 1 : ℕ) : ℝ) *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact row_covariance_sum n i _
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem integral_fixedErasedResidualCenteredRows_sq
    (j n : ℕ) (hn : 3 ≤ n) :
    (∫ x : Fin n → LayerObs,
      ∑ i : Fin n,
        (fixedErasedResidualRow i x -
          (n : ℝ)⁻¹ * ∑ k : Fin n, fixedErasedResidualRow k x) ^ 2
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) =
      ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ) *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) := by
  have hnpos : 0 < n := by omega
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos)
  have hsq : Integrable (fun x : Fin n → LayerObs =>
      ∑ i : Fin n, (fixedErasedResidualRow i x) ^ 2)
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) :=
    integrable_finsetSum Finset.univ (fun i _ =>
      (fixedErasedResidualRow_memLp_two j n i).integrable_sq)
  have htotal := (total_rows_memLp_two j n).integrable_sq
  calc
    _ = ∫ x : Fin n → LayerObs,
        (∑ i : Fin n, (fixedErasedResidualRow i x) ^ 2) -
          (n : ℝ)⁻¹ * (∑ k : Fin n, fixedErasedResidualRow k x) ^ 2
        ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        centered_finite_sum n hnpos (fun i => fixedErasedResidualRow i x)
    _ = (n : ℝ) * ((n - 1 : ℕ) : ℝ) *
        (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) -
        (n : ℝ)⁻¹ * (2 * (n : ℝ) * ((n - 1 : ℕ) : ℝ) *
          (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
            ∂(fixedErasedLaw j).prod (fixedErasedLaw j))) := by
      rw [integral_sub hsq (htotal.const_mul (n : ℝ)⁻¹), integral_const_mul,
        integral_row_square_sum, integral_total_rows_square]
    _ = _ := by
      rw [Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_ofNat]
      field_simp [hn0]

end
end Shao.OQ5.P52