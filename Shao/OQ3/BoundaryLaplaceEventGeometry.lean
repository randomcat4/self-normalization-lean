import Shao.OQ3.BoundaryLaplacePhysicalDomain

namespace Shao.OQ3
open scoped Topology
noncomputable section

theorem positive_parabola_window_event_geometry
    (level a0 rho : ℝ) (hlevel : 0 < level) (hrho : 0 < rho)
    (hphysical : ∀ r z : ℝ, |r| ≤ rho → |z| ≤ rho →
      0 < a0 + r ∧ 0 < (a0 + r) ^ 2 / level ^ 2 - z) :
    let U : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
      |w.1 ^ 2 / level ^ 2 - w.2| ≤ rho}
    let V : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
      w.1 ^ 2 / level ^ 2 - rho ≤ w.2 ∧ w.2 ≤ w.1 ^ 2 / level ^ 2}
    let D : Set (ℝ × ℝ) := {w | 0 < w.2 ∧ level * Real.sqrt w.2 ≤ w.1}
    IsClosed U ∧ (a0, a0 ^ 2 / level ^ 2) ∈ interior U ∧
      (∀ w ∈ U, 0 < w.1 ∧ 0 < w.2) ∧ V = U ∩ D := by
  let U : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
    |w.1 ^ 2 / level ^ 2 - w.2| ≤ rho}
  let V : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
    w.1 ^ 2 / level ^ 2 - rho ≤ w.2 ∧ w.2 ≤ w.1 ^ 2 / level ^ 2}
  let D : Set (ℝ × ℝ) := {w | 0 < w.2 ∧ level * Real.sqrt w.2 ≤ w.1}
  have hc1 : Continuous (fun w : ℝ × ℝ => |w.1 - a0|) := by fun_prop
  have hc2 : Continuous (fun w : ℝ × ℝ => |w.1 ^ 2 / level ^ 2 - w.2|) := by fun_prop
  have hclosed : IsClosed U :=
    (isClosed_le hc1 continuous_const).inter (isClosed_le hc2 continuous_const)
  have hcenter1 : |(a0, a0 ^ 2 / level ^ 2).1 - a0| < rho := by simpa using hrho
  have hcenter2 :
      |(a0, a0 ^ 2 / level ^ 2).1 ^ 2 / level ^ 2 - (a0, a0 ^ 2 / level ^ 2).2| < rho := by
    simpa using hrho
  have hnear1 : ∀ᶠ w in 𝓝 (a0, a0 ^ 2 / level ^ 2), |w.1 - a0| < rho :=
    hc1.continuousAt.eventually (gt_mem_nhds hcenter1)
  have hnear2 : ∀ᶠ w in 𝓝 (a0, a0 ^ 2 / level ^ 2),
      |w.1 ^ 2 / level ^ 2 - w.2| < rho :=
    hc2.continuousAt.eventually (gt_mem_nhds hcenter2)
  have hinterior : (a0, a0 ^ 2 / level ^ 2) ∈ interior U := by
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hnear1, hnear2] with w h1 h2
    exact ⟨h1.le, h2.le⟩
  have hpositive : ∀ w ∈ U, 0 < w.1 ∧ 0 < w.2 := by
    intro w hw
    have hcoords := hphysical (w.1 - a0) (w.1 ^ 2 / level ^ 2 - w.2) hw.1 hw.2
    have hfirst : a0 + (w.1 - a0) = w.1 := by ring
    rw [hfirst] at hcoords
    have hsecond : w.1 ^ 2 / level ^ 2 - (w.1 ^ 2 / level ^ 2 - w.2) = w.2 := by ring
    rw [hsecond] at hcoords
    exact hcoords
  refine ⟨hclosed, hinterior, hpositive, ?_⟩
  apply Set.ext
  intro w
  constructor
  · intro hw
    have hz : 0 ≤ w.1 ^ 2 / level ^ 2 - w.2 := sub_nonneg.mpr hw.2.2
    have hzrho : w.1 ^ 2 / level ^ 2 - w.2 ≤ rho := by linarith [hw.2.1]
    have hwU : w ∈ U := ⟨hw.1, by rw [abs_of_nonneg hz]; exact hzrho⟩
    have hp := hpositive w hwU
    have hevent : level * Real.sqrt w.2 ≤ w.1 :=
      (self_normalized_boundary_event_iff level w.1 w.2 hlevel hp.2).mpr ⟨hp.1, hw.2.2⟩
    exact ⟨hwU, hp.2, hevent⟩
  · rintro ⟨hwU, hwD⟩
    have hupper : w.2 ≤ w.1 ^ 2 / level ^ 2 :=
      ((self_normalized_boundary_event_iff level w.1 w.2 hlevel hwD.1).mp hwD.2).2
    have hbound : w.1 ^ 2 / level ^ 2 - w.2 ≤ rho :=
      (le_abs_self _).trans hwU.2
    exact ⟨hwU.1, by linarith, hupper⟩

end
end Shao.OQ3
