import Shao.Probability.SourcePermutationReveal

set_option autoImplicit false
noncomputable section
namespace Shao.C2.AdaptiveRevealCutoff
open Shao.Probability.SourcePermutationReveal

theorem before_adaptive_cutoff_iff
    {n : ℕ} (a : Shao.Path n) (H : ℝ) (hH : 0 < H)
    (m r : ℕ) (hr : r ≤ n) (sigma : LabelPerm n) :
    r < min (energyCutoff a H sigma) (n - m) ↔
      r < n - m ∧ H ≤ remainingEnergy a r sigma := by
  have hc := (energy_cutoff_data a H hH).2.1 sigma r hr
  rw [lt_min_iff]
  have he : r < energyCutoff a H sigma ↔ H ≤ remainingEnergy a r sigma := by
    simpa only [not_le, not_lt] using not_congr hc
  rw [he]
  exact and_comm

theorem omitted_adaptive_cutoff_iff
    {n : ℕ} (a : Shao.Path n) (h0 H : ℝ) (hh0 : 0 < h0) (hH : 0 < H)
    (m r : ℕ) (hr : r ≤ n) (sigma : LabelPerm n) :
    (min (energyCutoff a H sigma) (n - m) ≤ r ∧ r < energyCutoff a h0 sigma) ↔
      h0 ≤ remainingEnergy a r sigma ∧
        (remainingEnergy a r sigma < H ∨ n - r ≤ m) := by
  have hcH := (energy_cutoff_data a H hH).2.1 sigma r hr
  have hc0 := (energy_cutoff_data a h0 hh0).2.1 sigma r hr
  have he0 : r < energyCutoff a h0 sigma ↔ h0 ≤ remainingEnergy a r sigma := by
    simpa only [not_le, not_lt] using not_congr hc0
  rw [min_le_iff, hcH, he0]
  have hNat : n - m ≤ r ↔ n - r ≤ m := by omega
  rw [hNat]
  exact and_comm

theorem adaptive_cutoff_stopping_and_le
    {n : ℕ} (a : Shao.Path n) (h0 H : ℝ) (hh0 : 0 < h0) (hH : 0 < H)
    (hh0H : h0 ≤ H) (m : ℕ) :
    IsRevealStoppingRank (fun sigma => min (energyCutoff a H sigma) (n - m)) ∧
      ∀ sigma : LabelPerm n,
        min (energyCutoff a H sigma) (n - m) ≤ energyCutoff a h0 sigma := by
  have hDataH := energy_cutoff_data a H hH
  have hData0 := energy_cutoff_data a h0 hh0
  constructor
  · constructor
    · intro sigma
      exact (min_le_left _ _).trans (hDataH.1.1 sigma)
    · intro r sigma tau hprefix
      simp only [min_le_iff]
      exact or_congr (hDataH.1.2 r sigma tau hprefix) Iff.rfl
  · intro sigma
    have hAt0 : remainingEnergy a (energyCutoff a h0 sigma) sigma < h0 :=
      ((hData0.2.1 sigma (energyCutoff a h0 sigma) (hData0.1.1 sigma))).mp le_rfl
    have hLe : energyCutoff a H sigma ≤ energyCutoff a h0 sigma :=
      ((hDataH.2.1 sigma (energyCutoff a h0 sigma) (hData0.1.1 sigma))).mpr
        (hAt0.trans_le hh0H)
    exact (min_le_left _ _).trans hLe

end Shao.C2.AdaptiveRevealCutoff
