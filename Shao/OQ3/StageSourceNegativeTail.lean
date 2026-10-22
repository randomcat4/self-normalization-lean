import Shao.OQ3.NegativeLayerGeometricTail

namespace Shao.OQ3
open MeasureTheory Filter
open scoped BigOperators
noncomputable section

private theorem stage_abs_bounds_ae (mu : Measure ℝ) (J : ℕ)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i)) :
    ∀ᵐ x ∂mu, 1 ≤ |x| ∧ |x| ≤ 4 + Real.sqrt 10 := by
  filter_upwards [hrange] with x hx
  obtain ⟨i, rfl⟩ := hx
  cases i with
  | inl i => exact fixedAtom_bounds (Sum.inl i)
  | inr j => exact fixedAtom_bounds (Sum.inr j.val)

theorem exists_stage_source_negative_layer_geometric_tail (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q : ℝ)
    (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = q / 4)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ∃ gamma C : ℝ, 0 < gamma ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop, ∀ theta ∈ Set.Icc (0 : ℝ) 1,
        Summable (fun k : ℕ =>
          negativeNormalLayerTerm mu q sourceEll (dyadicMesh J) theta n k) ∧
        ∀ K : ℕ, (∑' k : ℕ,
          negativeNormalLayerTerm mu q sourceEll (dyadicMesh J) theta n (K + k)) ≤
            C * Real.exp (-gamma * dyadicMesh J) ^ K /
              (1 - Real.exp (-gamma * dyadicMesh J)) := by
  have hbounds := stage_abs_bounds_ae mu J hrange
  have hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10 := hbounds.mono fun _ hx => hx.2
  let H : ℝ := 25 + 8 * Real.sqrt 10
  have hslo : (25 / 8 : ℝ) < Real.sqrt 10 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hshi : Real.sqrt 10 < (13 / 4 : ℝ) :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hHlo : 50 < H := by dsimp only [H]; linarith only [hslo]
  have hHhi : H < 51 := by dsimp only [H]; linarith only [hshi]
  have hB : 0 ≤ 4 + Real.sqrt 10 := by positivity
  have hBsq : (4 + Real.sqrt 10) ^ 2 = 1 + H := by
    dsimp only [H]
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
  have henergy : ∀ᵐ x ∂mu, 1 ≤ x ^ 2 ∧ x ^ 2 ≤ 1 + H := by
    filter_upwards [hbounds] with x hx
    have hlo := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg x)).mpr hx.1
    have hhi := (sq_le_sq₀ (abs_nonneg x) hB).mpr hx.2
    simp only [one_pow, sq_abs] at hlo
    rw [sq_abs, hBsq] at hhi
    exact ⟨hlo, hhi⟩
  have hbase : ∀ i : Fin 4, 0 < mu.real {baseAtom i} := by
    intro i
    exact hpos (Sum.inl i)
  have hS := normalVariance_pos mu hb hbase
  have hD := parabolaCovariance_det_pos mu hb hbase
  have hT := transverseVariance_pos mu hb hbase
  have hX : Integrable (fun x : ℝ => x) mu :=
    integrable_continuous_of_fixed_bounds mu hb _ continuous_id
  have hX2 : Integrable (fun x : ℝ => x ^ 2) mu :=
    integrable_continuous_of_fixed_bounds mu hb _ (by fun_prop)
  have hmoment : (∫ x : ℝ, normalValue x ∂mu) =
      8 * (∫ x : ℝ, x ∂mu) - (∫ x : ℝ, x ^ 2 ∂mu) := by
    change (∫ x : ℝ, 8 * x - x ^ 2 ∂mu) = _
    rw [integral_sub (hX.const_mul 8) hX2, integral_const_mul]
  have hsecond : (∫ x : ℝ, x ^ 2 ∂mu) = q := by
    rw [hmeanY, hmeanX] at hmoment
    linarith only [hmoment]
  have hLp : MemLp (fun x : ℝ => x) 2 mu :=
    MemLp.of_bound continuous_id.aestronglyMeasurable (4 + Real.sqrt 10)
      (by simpa only [Real.norm_eq_abs] using hb)
  have hVar : ProbabilityTheory.variance (fun x : ℝ => x) mu = q - q ^ 2 / 16 := by
    rw [ProbabilityTheory.variance_eq_sub hLp]
    change (∫ x : ℝ, x ^ 2 ∂mu) - (∫ x : ℝ, x ∂mu) ^ 2 = _
    rw [hsecond, hmeanX]
    ring
  have hle := transverseVariance_le_variance_id mu hb hbase
  rw [hVar] at hle
  have hfrac : (1 : ℝ) / 30 < q / (32 * transverseVariance mu) := by
    apply (lt_div_iff₀ (mul_pos (by norm_num) hT)).mpr
    nlinarith only [hle, sq_nonneg (q - 1), hq0]
  have hgap : sourceEll < q / (32 * transverseVariance mu) :=
    sourceEll_lt_one_div_thirty.trans hfrac
  have hellq : sourceEll * q < 7 / 200 := by
    have hproduct := mul_lt_mul_of_pos_right sourceEll_lt_one_div_thirty
      (lt_trans zero_lt_one hq0)
    nlinarith only [hproduct, hq1]
  exact exists_source_negative_layer_geometric_tail mu J q H sourceEll hb hq0 hq1 hHlo hHhi
    sourceEll_pos.le hellq henergy hmeanY hmeanX hS hD hgap hrange hpos

end
end Shao.OQ3
