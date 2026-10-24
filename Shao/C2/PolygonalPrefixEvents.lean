import Shao.C2.BrownianUpperJointLimit

noncomputable section
namespace Shao.C2.PolygonalPrefixEvents
open MeasureTheory ProbabilityTheory Set
open Shao.C2.BridgeDomination Shao.C2.BrownianUpperJointLimit
open Shao.OQ4.PolygonalPathTightness Shao.OQ4.PolygonalThirdMoment

private theorem exists_segment (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx : 0 ≤ x) (hxn : x ≤ (n : ℝ)) :
    ∃ k : ℕ, k < n ∧ (k : ℝ) ≤ x ∧ x ≤ (k : ℝ) + 1 := by
  by_cases hlt : x < (n : ℝ)
  · exact ⟨Nat.floor x, (Nat.floor_lt hx).mpr hlt, Nat.floor_le hx,
      (Nat.lt_floor_add_one x).le⟩
  · have he : x = (n : ℝ) := le_antisymm hxn (le_of_not_gt hlt)
    refine ⟨n - 1, by omega, ?_, ?_⟩
    · rw [he]
      exact_mod_cast Nat.sub_le n 1
    · rw [he]
      exact_mod_cast (show n ≤ n - 1 + 1 by omega)

theorem unitPolygonalPath_one (n : ℕ) (h : ℝ) (hh : 0 < h)
    (hsq : h ^ 2 = (n : ℝ)) (p : Shao.Path n) :
    unitPolygonalPath 1 n h p 1 = Shao.prefixSum p n / h := by
  have he := polygonalPath_at_grid n h hh p n le_rfl
  rw [← hsq, div_self (ne_of_gt (sq_pos_of_pos hh))] at he
  simpa only [unitPolygonalPath_apply, Set.Icc.coe_one, NNReal.coe_one, one_mul] using he

theorem unitPolygonalPath_segment (n : ℕ) (h : ℝ) (hh : 0 < h)
    (hsq : h ^ 2 = (n : ℝ)) (p : Shao.Path n) (t : BridgeTime) :
    ∃ k : ℕ, k < n ∧ ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      unitPolygonalPath 1 n h p t =
        (1 - θ) * (Shao.prefixSum p k / h) + θ * (Shao.prefixSum p (k + 1) / h) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    rw [← hsq]
    exact sq_pos_of_pos hh
  have hn : 0 < n := by exact_mod_cast hnR
  let x : ℝ := (t : ℝ) * h ^ 2
  have hx : 0 ≤ x := mul_nonneg t.property.1 (sq_nonneg h)
  have hxn : x ≤ (n : ℝ) := by
    have he := mul_le_mul_of_nonneg_right t.property.2 (sq_nonneg h)
    simpa only [x, one_mul, hsq] using he
  obtain ⟨k, hk, hlo, hhi⟩ := exists_segment n hn x hx hxn
  let θ : ℝ := x - (k : ℝ)
  have hθ0 : 0 ≤ θ := sub_nonneg.mpr hlo
  have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith
  have ht : ((k : ℝ) + θ) / h ^ 2 = (t : ℝ) := by
    dsimp [θ, x]
    field_simp [ne_of_gt hh]
    <;> ring
  have he := polygonalPath_on_grid_interval n h hh p k hk θ hθ0 hθ1
  refine ⟨k, hk, θ, hθ0, hθ1, ?_⟩
  simpa only [unitPolygonalPath_apply, NNReal.coe_one, one_mul, ht] using he

theorem unitPolygonalPath_le_iff (n : ℕ) (h : ℝ) (hh : 0 < h)
    (hsq : h ^ 2 = (n : ℝ)) (p : Shao.Path n) (a : ℝ) :
    (∀ t : BridgeTime, unitPolygonalPath 1 n h p t ≤ a) ↔
      ∀ k : ℕ, k ≤ n → Shao.prefixSum p k ≤ a * h := by
  constructor
  · intro hall k hk
    have hs : 0 < h ^ 2 := sq_pos_of_pos hh
    let t : BridgeTime := ⟨(k : ℝ) / h ^ 2,
      div_nonneg (Nat.cast_nonneg _) hs.le,
      (div_le_one hs).mpr (by rw [hsq]; exact_mod_cast hk)⟩
    have he : unitPolygonalPath 1 n h p t = Shao.prefixSum p k / h := by
      simpa only [unitPolygonalPath_apply, NNReal.coe_one, one_mul, t] using polygonalPath_at_grid n h hh p k hk
    have hi := hall t
    rw [he] at hi
    exact (div_le_iff₀ hh).mp hi
  · intro hprefix t
    obtain ⟨k, hk, θ, hθ0, hθ1, he⟩ := unitPolygonalPath_segment n h hh hsq p t
    have hlo : Shao.prefixSum p k / h ≤ a := (div_le_iff₀ hh).mpr (hprefix k hk.le)
    have hhi : Shao.prefixSum p (k + 1) / h ≤ a :=
      (div_le_iff₀ hh).mpr (hprefix (k + 1) (by omega))
    rw [he]
    have hleft := mul_le_mul_of_nonneg_left hlo (sub_nonneg.mpr hθ1)
    have hright := mul_le_mul_of_nonneg_left hhi hθ0
    nlinarith

theorem unitPolygonalPath_lt_iff (n : ℕ) (h : ℝ) (hh : 0 < h)
    (hsq : h ^ 2 = (n : ℝ)) (p : Shao.Path n) (a : ℝ) :
    (∀ t : BridgeTime, unitPolygonalPath 1 n h p t < a) ↔
      ∀ k : ℕ, k ≤ n → Shao.prefixSum p k < a * h := by
  constructor
  · intro hall k hk
    have hs : 0 < h ^ 2 := sq_pos_of_pos hh
    let t : BridgeTime := ⟨(k : ℝ) / h ^ 2,
      div_nonneg (Nat.cast_nonneg _) hs.le,
      (div_le_one hs).mpr (by rw [hsq]; exact_mod_cast hk)⟩
    have he : unitPolygonalPath 1 n h p t = Shao.prefixSum p k / h := by
      simpa only [unitPolygonalPath_apply, NNReal.coe_one, one_mul, t] using polygonalPath_at_grid n h hh p k hk
    have hi := hall t
    rw [he] at hi
    exact (div_lt_iff₀ hh).mp hi
  · intro hprefix t
    obtain ⟨k, hk, θ, hθ0, hθ1, he⟩ := unitPolygonalPath_segment n h hh hsq p t
    have hlo : Shao.prefixSum p k / h < a := (div_lt_iff₀ hh).mpr (hprefix k hk.le)
    have hhi : Shao.prefixSum p (k + 1) / h < a :=
      (div_lt_iff₀ hh).mpr (hprefix (k + 1) (by omega))
    rw [he]
    by_cases hθ : θ = 1
    · simpa [hθ] using hhi
    · have hleft := mul_lt_mul_of_pos_left hlo (sub_pos.mpr (lt_of_le_of_ne hθ1 hθ))
      have hright := mul_le_mul_of_nonneg_left hhi.le hθ0
      nlinarith

theorem upperJoint_real_prefix (n : ℕ) (h : ℝ) (hh : 0 < h)
    (hsq : h ^ 2 = (n : ℝ)) (ν : Measure ℝ) (a v : ℝ) :
    (polygonalPathLaw 1 n h ν).real (upperJointSet a v) =
      (Measure.pi (fun _ : Fin n => ν)).real
        {p : Shao.Path n | (∀ k : ℕ, k ≤ n → Shao.prefixSum p k ≤ a * h) ∧
          Shao.prefixSum p n ≤ v * h} := by
  simp only [measureReal_def, polygonalPathLaw]
  rw [Measure.map_apply (measurable_unitPolygonalPath 1 n h)
    (isClosed_upperJointSet a v).measurableSet]
  apply congrArg ENNReal.toReal
  apply congrArg (Measure.pi (fun _ : Fin n => ν))
  ext p
  change ((∀ t : BridgeTime, unitPolygonalPath 1 n h p t ≤ a) ∧
    unitPolygonalPath 1 n h p 1 ≤ v) ↔ _
  rw [unitPolygonalPath_le_iff n h hh hsq p a, unitPolygonalPath_one n h hh hsq p]
  exact and_congr_right (fun _ => div_le_iff₀ hh)

end Shao.C2.PolygonalPrefixEvents
