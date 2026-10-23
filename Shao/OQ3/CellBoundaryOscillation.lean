import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Connected.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Shao.OQ3
open Classical
open scoped Topology
noncomputable section

theorem closed_ball_membership_iff_of_frontier_disjoint
    (A : Set (ℝ × ℝ)) (z : ℝ × ℝ) (h : ℝ)
    (havoid : Disjoint (Metric.closedBall z h) (frontier A)) :
    ∀ u ∈ Metric.closedBall z h, ∀ v ∈ Metric.closedBall z h, (u ∈ A ↔ v ∈ A) := by
  have hcover : Metric.closedBall z h ⊆ interior A ∪ interior Aᶜ := by
    intro x hx
    by_cases hi : x ∈ interior A
    · exact Or.inl hi
    · right
      rw [interior_compl]
      intro hcl
      exact Set.disjoint_left.mp havoid hx ⟨hcl, hi⟩
  have hdisjoint : Disjoint (interior A) (interior Aᶜ) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (interior_subset hy) (interior_subset hx)
  have hconnected : IsPreconnected (Metric.closedBall z h) :=
    (convex_closedBall z h).isPreconnected
  rcases hconnected.subset_or_subset isOpen_interior isOpen_interior hdisjoint hcover with hin | hout
  · intro u hu v hv
    exact iff_of_true (interior_subset (hin hu)) (interior_subset (hin hv))
  · intro u hu v hv
    exact iff_of_false (interior_subset (hout hu)) (interior_subset (hout hv))

theorem indicator_cell_pair_oscillation_bound
    (A : Set (ℝ × ℝ)) (g : (ℝ × ℝ) → ℝ)
    (C L h : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hbound : ∀ u ∈ A, |g u| ≤ C)
    (hLip : ∀ u ∈ A, ∀ v ∈ A, |g u - g v| ≤ L * dist u v)
    (z : ℝ × ℝ) :
    let Near : Prop := (Metric.closedBall z h ∩ A).Nonempty
    let Edge : Prop := (Metric.closedBall z h ∩ frontier A).Nonempty
    ∀ u ∈ Metric.closedBall z h, ∀ v ∈ Metric.closedBall z h,
      |A.indicator g u - A.indicator g v| ≤
        (if Near then 2 * L * h else 0) + (if Edge then 2 * C else 0) := by
  classical
  let Near : Prop := (Metric.closedBall z h ∩ A).Nonempty
  let Edge : Prop := (Metric.closedBall z h ∩ frontier A).Nonempty
  have hind (x : ℝ × ℝ) : |A.indicator g x| ≤ C := by
    by_cases hx : x ∈ A
    · simpa only [Set.indicator_of_mem hx] using hbound x hx
    · rw [Set.indicator_of_notMem hx, abs_zero]
      exact hC
  have hNearNonneg : 0 ≤ (if Near then 2 * L * h else 0) := by
    split_ifs <;> positivity
  dsimp only
  intro u hu v hv
  by_cases hedge : Edge
  · have hrough : |A.indicator g u - A.indicator g v| ≤ 2 * C := by
      calc
        _ ≤ |A.indicator g u| + |-(A.indicator g v)| := abs_add_le _ _
        _ ≤ C + C := by rw [abs_neg]; exact add_le_add (hind u) (hind v)
        _ = _ := by ring
    change _ ≤ (if Near then 2 * L * h else 0) + (if Edge then 2 * C else 0)
    rw [if_pos hedge]
    linarith
  · have havoid : Disjoint (Metric.closedBall z h) (frontier A) := by
      apply Set.disjoint_left.mpr
      intro x hx hfront
      exact hedge ⟨x, hx, hfront⟩
    have hiff := closed_ball_membership_iff_of_frontier_disjoint A z h havoid u hu v hv
    by_cases huA : u ∈ A
    · have hvA : v ∈ A := hiff.mp huA
      have hnear : Near := ⟨u, hu, huA⟩
      have hdist : dist u v ≤ 2 * h := by
        have htri := dist_triangle u z v
        have hu0 : dist u z ≤ h := hu
        have hv0 : dist v z ≤ h := hv
        rw [dist_comm z v] at htri
        linarith
      change _ ≤ (if Near then 2 * L * h else 0) + (if Edge then 2 * C else 0)
      rw [if_pos hnear, if_neg hedge, add_zero,
        Set.indicator_of_mem huA, Set.indicator_of_mem hvA]
      calc
        _ ≤ L * dist u v := hLip u huA v hvA
        _ ≤ L * (2 * h) := mul_le_mul_of_nonneg_left hdist hL
        _ = _ := by ring
    · have hvA : v ∉ A := fun hvA => huA (hiff.mpr hvA)
      change _ ≤ (if Near then 2 * L * h else 0) + (if Edge then 2 * C else 0)
      rw [Set.indicator_of_notMem huA, Set.indicator_of_notMem hvA,
        sub_self, abs_zero, if_neg hedge, add_zero]
      exact hNearNonneg

end
end Shao.OQ3
