import Shao.OQ3.StandardizedCellChangeOfMeasure

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology BigOperators
noncomputable section

theorem iid_parabola_affine_standardized_law
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 1 ≤ n)
    (y : ℝ × ℝ) (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
    let Y : ℝ → (ℝ × ℝ) := fun x => E ((x, x ^ 2) - y)
    let law : Measure (ℝ × ℝ) := nu.map Y
    let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let QY : Measure (Fin n → (ℝ × ℝ)) := Measure.pi (fun _ : Fin n => law)
    let M : Shao.Path n → (ℝ × ℝ) := fun z =>
      ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
    let T : Shao.Path n → (ℝ × ℝ) := fun z =>
      Real.sqrt (n : ℝ) • E (M z - y)
    let S : (Fin n → (ℝ × ℝ)) → (ℝ × ℝ) := fun v =>
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, v i
    IsProbabilityMeasure law ∧ IsProbabilityMeasure (Q.map T) ∧
      (∀ z : Shao.Path n, T z = S (fun i => Y (z i))) ∧
      Q.map T = QY.map S
 := by
  classical
  dsimp only
  let Y : ℝ → (ℝ × ℝ) := fun x => E ((x, x ^ 2) - y)
  let law : Measure (ℝ × ℝ) := nu.map Y
  let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let QY : Measure (Fin n → (ℝ × ℝ)) := Measure.pi (fun _ : Fin n => law)
  let M : Shao.Path n → (ℝ × ℝ) := fun z =>
    ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
  let T : Shao.Path n → (ℝ × ℝ) := fun z =>
    Real.sqrt (n : ℝ) • E (M z - y)
  let S : (Fin n → (ℝ × ℝ)) → (ℝ × ℝ) := fun v =>
    (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, v i
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hroot : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  have hsquare : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hmul : (Real.sqrt (n : ℝ))⁻¹ * (n : ℝ) = Real.sqrt (n : ℝ) := by
    calc
      _ = (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt (n : ℝ) ^ 2) :=
        congrArg (fun r : ℝ => (Real.sqrt (n : ℝ))⁻¹ * r) hsquare.symm
      _ = _ := by field_simp [hroot]
  have hratio : Real.sqrt (n : ℝ) / (n : ℝ) = (Real.sqrt (n : ℝ))⁻¹ :=
    (div_eq_iff hn0).2 hmul.symm
  have hscalar (b c : ℝ) :
      Real.sqrt (n : ℝ) * (b / (n : ℝ) - c) =
        (Real.sqrt (n : ℝ))⁻¹ * (b - (n : ℝ) * c) := by
    calc
      _ = (Real.sqrt (n : ℝ) / (n : ℝ)) * b - Real.sqrt (n : ℝ) * c := by ring
      _ = (Real.sqrt (n : ℝ))⁻¹ * b -
          ((Real.sqrt (n : ℝ))⁻¹ * (n : ℝ)) * c := by rw [hratio, hmul]
      _ = _ := by ring
  have hpoint (z : Shao.Path n) : T z = S (fun i => Y (z i)) := by
    have hsum (t : Finset (Fin n)) :
        (∑ i ∈ t, (z i, z i ^ 2)) = (∑ i ∈ t, z i, ∑ i ∈ t, z i ^ 2) := by
      induction t using Finset.induction_on with
      | empty => simp only [Finset.sum_empty]; rfl
      | @insert i t hi ih => simp [Finset.sum_insert, hi, ih]
    have hvec : Real.sqrt (n : ℝ) • (M z - y) =
        (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, ((z i, z i ^ 2) - y) := by
      ext
      · simpa [M, Shao.energy, Finset.sum_sub_distrib, hsum, smul_eq_mul] using
          hscalar (∑ i : Fin n, z i) y.1
      · simpa [M, Shao.energy, Finset.sum_sub_distrib, hsum, smul_eq_mul] using
          hscalar (∑ i : Fin n, z i ^ 2) y.2
    change Real.sqrt (n : ℝ) • E (M z - y) =
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, E ((z i, z i ^ 2) - y)
    calc
      _ = E (Real.sqrt (n : ℝ) • (M z - y)) := (E.map_smul _ _).symm
      _ = E ((Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, ((z i, z i ^ 2) - y)) :=
        congrArg E hvec
      _ = _ := by rw [E.map_smul, map_sum]
  have hY : Measurable Y := by dsimp [Y]; fun_prop
  have hlaw : IsProbabilityMeasure law :=
    (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).mpr inferInstance
  letI : IsProbabilityMeasure law := hlaw
  have hYX : Measurable (fun z : Shao.Path n => fun i => Y (z i)) := by fun_prop
  have hS : Measurable S := by dsimp [S]; fun_prop
  have hfun : T = S ∘ (fun z : Shao.Path n => fun i => Y (z i)) := funext hpoint
  have hT : Measurable T := by rw [hfun]; exact hS.comp hYX
  have hprob : IsProbabilityMeasure (Q.map T) :=
    (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).mpr inferInstance
  have hpi : Q.map (fun z : Shao.Path n => fun i => Y (z i)) = QY :=
    Measure.pi_map_pi (fun _ => hY.aemeasurable)
  refine ⟨hlaw, hprob, hpoint, ?_⟩
  change Q.map T = QY.map S
  rw [← hpi, Measure.map_map hS hYX]
  exact congrArg (fun f => Q.map f) hfun

theorem parabola_affine_law_eq_coordinate_map
    (nu : Measure ℝ) (y : ℝ × ℝ) (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (Y : ℝ → (Fin 2 → ℝ)) (hY : Measurable Y)
    (hpoint : ∀ x : ℝ, E ((x, x ^ 2) - y) = (Y x 0, Y x 1)) :
    nu.map (fun x => E ((x, x ^ 2) - y)) =
      (nu.map Y).map (fun v : Fin 2 → ℝ => (v 0, v 1)) := by
  rw [Measure.map_map (by fun_prop) hY]
  congr 1
  funext x
  exact hpoint x

end
end Shao.OQ3
