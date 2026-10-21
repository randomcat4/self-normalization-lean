import Shao.OQ3.SummableAtoms

/-!
# Accumulating atoms exclude a nonzero lattice projection

Source: current/oq3/proofs/r1/report.md, lines 113-119 and 259-277.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U6a scope: 0d269910fcdbe5edbff649ef20053a9362b22c811eb5603da0973445086bc919.
These are atom-location statements; the probability characteristic-function
equality bridge is separate.
-/

namespace Shao.OQ3

open Filter

noncomputable section

theorem dyadicMesh_tendsto_zero :
    Filter.Tendsto dyadicMesh Filter.atTop (nhds (0 : ℝ)) := by
  change Tendsto (fun j : ℕ => ((2 : ℝ) ^ j)⁻¹) atTop (nhds 0)
  simpa only [one_div, inv_pow] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1))

theorem addedAtom_tendsto :
    Filter.Tendsto addedAtom Filter.atTop (nhds (4 + Real.sqrt 10)) := by
  have hmesh : Tendsto (fun j => dyadicMesh (j + 1)) atTop (nhds (0 : ℝ)) :=
    dyadicMesh_tendsto_zero.comp (tendsto_add_atTop_nat 1)
  have hrad : Tendsto (fun j => 10 - dyadicMesh (j + 1)) atTop (nhds (10 : ℝ)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hmesh (a := (10 : ℝ))
  change Tendsto (fun j => 4 + Real.sqrt (10 - dyadicMesh (j + 1)))
    atTop (nhds (4 + Real.sqrt 10))
  exact tendsto_const_nhds.add hrad.sqrt

theorem eventually_zero_of_lattice_tendsto_zero (c : ℝ) (hc : 0 < c) (f : ℕ → ℝ)
    (hf : Filter.Tendsto f Filter.atTop (nhds 0))
    (hmem : ∀ j, ∃ m : ℤ, f j = c * (m : ℝ)) :
    ∀ᶠ j in Filter.atTop, f j = 0 := by
  have hsmall : ∀ᶠ j in atTop, |f j| < c := by
    have habs : Tendsto (fun j => |f j|) atTop (nhds (0 : ℝ)) := by
      simpa only [abs_zero] using hf.abs
    exact habs.eventually (gt_mem_nhds hc)
  filter_upwards [hsmall] with j hj
  obtain ⟨m, hm⟩ := hmem j
  by_cases hz : m = 0
  · simp [hm, hz]
  · have hlarge : (1 : ℝ) ≤ |(m : ℝ)| := by
      exact_mod_cast Int.one_le_abs hz
    rw [hm, abs_mul, abs_of_pos hc] at hj
    nlinarith

theorem fixedAtom_no_projection_lattice (c : ℝ) (hc : 0 < c) (xi eta : ℝ)
    (hmem : ∀ i : AtomicIndex, ∃ m : ℤ,
      xi * (fixedAtom i - (4 + Real.sqrt 10)) +
        eta * ((fixedAtom i) ^ 2 - (4 + Real.sqrt 10) ^ 2) = c * (m : ℝ)) :
    xi = 0 ∧ eta = 0 := by
  let beta := 4 + Real.sqrt 10
  let f : ℕ → ℝ := fun j => xi * (addedAtom j - beta) +
    eta * (addedAtom j ^ 2 - beta ^ 2)
  have hf : Tendsto f atTop (nhds 0) := by
    have ha : Tendsto addedAtom atTop (nhds beta) := addedAtom_tendsto
    have hd : Tendsto (fun j => addedAtom j - beta) atTop (nhds (0 : ℝ)) := by
      simpa only [sub_self] using ha.sub (tendsto_const_nhds (x := beta))
    have hd2 : Tendsto (fun j => addedAtom j ^ 2 - beta ^ 2) atTop (nhds (0 : ℝ)) := by
      have hh : Tendsto (fun j => addedAtom j ^ 2 - beta ^ 2) atTop
          (nhds (beta ^ 2 - beta ^ 2)) :=
        (ha.pow 2).sub tendsto_const_nhds
      simpa only [sub_self] using hh
    have h1 := tendsto_const_nhds.mul hd (a := xi)
    have h2 := tendsto_const_nhds.mul hd2 (a := eta)
    change Tendsto (fun j => xi * (addedAtom j - beta) +
      eta * (addedAtom j ^ 2 - beta ^ 2)) atTop (nhds 0)
    simpa only [mul_zero, add_zero] using h1.add h2
  have hzero : ∀ᶠ j in atTop, f j = 0 :=
    eventually_zero_of_lattice_tendsto_zero c hc f hf (fun j => hmem (Sum.inr j))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hzero
  have hlinear (j : ℕ) (hj : N ≤ j) : xi + eta * (addedAtom j + beta) = 0 := by
    have hfac : (addedAtom j - beta) * (xi + eta * (addedAtom j + beta)) = 0 := by
      have hz := hN j hj
      dsimp [f] at hz
      nlinarith [hz]
    exact (mul_eq_zero.mp hfac).resolve_left
      (sub_ne_zero.mpr (ne_of_lt (addedAtom_lt_limit j)))
  have h0 := hlinear N le_rfl
  have h1 := hlinear (N + 1) (by omega)
  have hdiff : addedAtom N ≠ addedAtom (N + 1) := by
    intro h
    have hbad := addedAtom_injective h
    omega
  have heta : eta = 0 := by
    have hprod : eta * (addedAtom N - addedAtom (N + 1)) = 0 := by nlinarith [h0, h1]
    exact (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hdiff)
  exact ⟨by simpa [heta] using h0, heta⟩

end
end Shao.OQ3
