import Shao.C2.FiniteWalkReflection
import Mathlib.SetTheory.Cardinal.Finite

noncomputable section
namespace Shao.C2.FiniteWalkReflectionCount
open Shao.C2.FiniteWalkReflection

theorem reflectAtHit_hasHit {n : ℕ} (h : ℤ) (w : Fin n → Bool)
    (hex : ∃ k : ℕ, k ≤ n ∧ walkPrefix w k = h) :
    ∃ k : ℕ, k ≤ n ∧ walkPrefix (reflectAtHit h w) k = h := by
  have hs := firstHit_spec h w hex
  refine ⟨firstHit h w, hs.1, ?_⟩
  rw [reflectAtHit, walkPrefix_reflectAfter_of_le w (firstHit h w) (firstHit h w) le_rfl]
  exact hs.2

theorem strictBelow_iff_noHit {n : ℕ} (h : ℤ) (hh : 0 < h) (w : Fin n → Bool) :
    (∀ k : ℕ, k ≤ n → walkPrefix w k < h) ↔
      ¬∃ k : ℕ, k ≤ n ∧ walkPrefix w k = h := by
  constructor
  · intro hall ⟨k, hk, he⟩
    have hs := hall k hk
    omega
  · intro hmiss k hk
    by_contra hnot
    have hge : h ≤ walkPrefix w k := by omega
    obtain ⟨j, hj, he⟩ := walkPrefix_reaches_level w h hh k hk hge
    exact hmiss ⟨j, le_trans hj hk, he⟩

theorem hit_endpoint_cdf_card (n : ℕ) (h x : ℤ) (hh : 0 < h) (hx : x < h) :
    Nat.card {w : Fin n → Bool //
      (∃ k : ℕ, k ≤ n ∧ walkPrefix w k = h) ∧ walkPrefix w n ≤ x} =
      Nat.card {w : Fin n → Bool // 2 * h - x ≤ walkPrefix w n} := by
  classical
  refine Nat.card_congr {
    toFun := fun w => ⟨reflectAtHit h w.val, ?_⟩
    invFun := fun w => ⟨reflectAtHit h w.val, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have he := reflectAtHit_endpoint h w.val w.property.1
    have hxw := w.property.2
    omega
  · have hew := w.property
    have hex := walkPrefix_reaches_level w.val h hh n le_rfl (by omega)
    refine ⟨reflectAtHit_hasHit h w.val hex, ?_⟩
    have he := reflectAtHit_endpoint h w.val hex
    omega
  · intro w
    apply Subtype.ext
    exact reflectAtHit_involutive h w.val
  · intro w
    apply Subtype.ext
    exact reflectAtHit_involutive h w.val

theorem killed_endpoint_cdf_card (n : ℕ) (h x : ℤ) (hh : 0 < h) (hx : x < h) :
    Nat.card {w : Fin n → Bool //
        (∀ k : ℕ, k ≤ n → walkPrefix w k < h) ∧ walkPrefix w n ≤ x} +
      Nat.card {w : Fin n → Bool // 2 * h - x ≤ walkPrefix w n} =
        Nat.card {w : Fin n → Bool // walkPrefix w n ≤ x} := by
  classical
  let E := {w : Fin n → Bool // walkPrefix w n ≤ x}
  let H : E → Prop := fun e => ∃ k : ℕ, k ≤ n ∧ walkPrefix e.val k = h
  have hp := Nat.card_congr (Equiv.sumCompl H)
  rw [Nat.card_sum] at hp
  have hH : Nat.card {e : E // H e} =
      Nat.card {w : Fin n → Bool //
        (∃ k : ℕ, k ≤ n ∧ walkPrefix w k = h) ∧ walkPrefix w n ≤ x} := by
    exact Nat.card_congr {
      toFun := fun e => ⟨e.val.val, e.property, e.val.property⟩
      invFun := fun w => ⟨⟨w.val, w.property.2⟩, w.property.1⟩
      left_inv := fun e => Subtype.ext (Subtype.ext rfl)
      right_inv := fun w => Subtype.ext rfl }
  have hS : Nat.card {e : E // ¬H e} =
      Nat.card {w : Fin n → Bool //
        (∀ k : ℕ, k ≤ n → walkPrefix w k < h) ∧ walkPrefix w n ≤ x} := by
    exact Nat.card_congr {
      toFun := fun e => ⟨e.val.val, (strictBelow_iff_noHit h hh e.val.val).mpr e.property, e.val.property⟩
      invFun := fun w => ⟨⟨w.val, w.property.2⟩, (strictBelow_iff_noHit h hh w.val).mp w.property.1⟩
      left_inv := fun e => Subtype.ext (Subtype.ext rfl)
      right_inv := fun w => Subtype.ext rfl }
  rw [hH, hS, hit_endpoint_cdf_card n h x hh hx] at hp
  exact (Nat.add_comm _ _).trans hp

end Shao.C2.FiniteWalkReflectionCount
