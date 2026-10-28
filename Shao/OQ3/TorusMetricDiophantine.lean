import Shao.OQ3.TorusSimultaneousBadSet
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem torus_metric_diophantine_eventually (m : ℕ) (hm : 6 ≤ m) :
    (∑' n : ℕ, volume {x : Fin m → UnitAddCircle | ∀ j,
      ‖((n + 1 : ℕ) : ℤ) • x j‖ ≤ Real.rpow ((n : ℝ) + 1) (-(3 : ℝ) / 16)}) ≠ ⊤ ∧
      ∀ᵐ x ∂(volume : Measure (Fin m → UnitAddCircle)),
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ j : Fin m,
          Real.rpow ((n : ℝ) + 1) (-(3 : ℝ) / 16) <
            ‖((n + 1 : ℕ) : ℤ) • x j‖ := by
  classical
  simp only [Real.rpow_eq_pow]
  let g : ℝ := -(3 : ℝ) / 16
  let p : ℝ := g * (m : ℝ)
  let eps : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ g
  let Bad : ℕ → Set (Fin m → UnitAddCircle) := fun n =>
    {x | ∀ j, ‖((n + 1 : ℕ) : ℤ) • x j‖ ≤ eps n}
  have hmR : (6 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hp : p < -1 := by dsimp [p, g]; nlinarith
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ p) := Real.summable_nat_rpow.mpr hp
  have hshift : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ p) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ p) 1).2 hbase)
  have hRealBound (n : ℕ) : (2 * eps n) ^ m =
      (2 : ℝ) ^ m * ((n : ℝ) + 1) ^ p := by
    rw [mul_pow]
    congr 1
    exact (Real.rpow_mul_natCast (show 0 ≤ (n : ℝ) + 1 by positivity) g m).symm
  have hSeries : Summable (fun n : ℕ => (2 * eps n) ^ m) := by
    simp_rw [hRealBound]
    exact hshift.mul_left ((2 : ℝ) ^ m)
  have hBound (n : ℕ) : volume (Bad n) ≤ ENNReal.ofReal ((2 * eps n) ^ m) := by
    have heps : 0 ≤ eps n := Real.rpow_nonneg (by positivity) g
    have h := (torus_simultaneous_bad_set_volume m ((n + 1 : ℕ) : ℤ)
      (by omega) (eps n)).2
    rw [← ENNReal.ofReal_pow (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) heps) m] at h
    exact h
  have hFinite : (∑' n : ℕ, volume (Bad n)) ≠ ⊤ :=
    ne_top_of_le_ne_top hSeries.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum hBound)
  refine ⟨hFinite, ?_⟩
  filter_upwards [ae_eventually_notMem hFinite] with x hx
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hx
  refine ⟨N, ?_⟩
  intro n hn
  simpa only [Bad, eps, g, Set.mem_setOf_eq, not_forall, not_le] using hN n hn

end
end Shao.OQ3
