import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Sequences

namespace Shao.OQ3
open Filter
open scoped Topology
noncomputable section

theorem exists_large_torus_return (m : ℕ) (x : Fin m → UnitAddCircle)
    (eps : ℝ) (heps : 0 < eps) (B : ℕ) :
    ∃ n : ℕ, B < n ∧ ‖n • x‖ < eps := by
  classical
  let z : Fin m → UnitAddCircle := (B + 1) • x
  obtain ⟨y, _, f, hf, hlim⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (Fin m → UnitAddCircle))).tendsto_subseq
      (fun k : ℕ => Set.mem_univ (k • z))
  have hlim' : Tendsto (fun k : ℕ => f k • z) atTop (𝓝 y) := hlim
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim' (eps / 2) (by linarith)
  let q : ℕ := f (N + 1) - f N
  have hfn : f N < f (N + 1) := hf (Nat.lt_succ_self N)
  have hq : 0 < q := Nat.sub_pos_of_lt hfn
  have hind : q + f N = f (N + 1) := Nat.sub_add_cancel hfn.le
  have heq : q • z = f (N + 1) • z - f N • z := by
    apply (eq_sub_iff_add_eq).mpr
    rw [← add_nsmul, hind]
  have hsmall : ‖q • z‖ < eps := by
    calc
      ‖q • z‖ = dist (f (N + 1) • z) (f N • z) := by rw [heq, dist_eq_norm]
      _ ≤ dist (f (N + 1) • z) y + dist y (f N • z) :=
        dist_triangle _ _ _
      _ = dist (f (N + 1) • z) y + dist (f N • z) y := by rw [dist_comm y]
      _ < eps := by
        have h1 := hN (N + 1) (by omega)
        have h0 := hN N le_rfl
        linarith
  refine ⟨(B + 1) * q, ?_, ?_⟩
  · have hq1 : 1 ≤ q := hq
    have hlarge : B + 1 ≤ (B + 1) * q := by
      simpa only [mul_one] using Nat.mul_le_mul_left (B + 1) hq1
    omega
  · rw [Nat.mul_comm (B + 1) q, mul_smul]
    exact hsmall

end
end Shao.OQ3
