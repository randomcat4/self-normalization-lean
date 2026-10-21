import Shao.OQ3.AtomProjection
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Positive accumulating atoms imply genuine joint nonlattice

Source: current/oq3/proofs/r1/report.md, lines 259-277.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U6b scope: 8de2c7bea7ed69f3d27419dc5ed60acca09e9e427f421fa4b312a13302ae7696.
-/

namespace Shao.OQ3

open MeasureTheory

noncomputable section

def jointPhase (xi eta x : ℝ) : ℂ :=
  Complex.exp (((xi * x + eta * x ^ 2 : ℝ) : ℂ) * Complex.I)

def jointCharacteristic (mu : Measure ℝ) (xi eta : ℝ) : ℂ :=
  ∫ x, jointPhase xi eta x ∂mu

theorem jointPhase_norm (xi eta x : ℝ) : ‖jointPhase xi eta x‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

theorem integrable_jointPhase (mu : Measure ℝ) [IsProbabilityMeasure mu] (xi eta : ℝ) :
    Integrable (jointPhase xi eta) mu := by
  have hf : Continuous (jointPhase xi eta) := by
    unfold jointPhase
    fun_prop
  apply Integrable.of_bound hf.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun x => (jointPhase_norm xi eta x).le

theorem jointCharacteristic_norm_le_one (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (xi eta : ℝ) :
    ‖jointCharacteristic mu xi eta‖ ≤ 1 := by
  calc
    ‖jointCharacteristic mu xi eta‖ ≤ ∫ x, ‖jointPhase xi eta x‖ ∂mu :=
      norm_integral_le_integral_norm _
    _ = 1 := by simp [jointPhase_norm, measureReal_def]

private theorem complex_strictConvexSpace : StrictConvexSpace ℝ ℂ := by
  apply StrictConvexSpace.of_norm_add_ne_two
  intro x y hx hy hne hsum
  have hpar := parallelogram_law_with_norm ℝ x y
  rw [hx, hy, hsum] at hpar
  have hzero : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact hne (sub_eq_zero.mp (norm_eq_zero.mp hzero))

theorem jointPhase_eq_of_modulus_one (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (xi eta : ℝ) (hmod : ‖jointCharacteristic mu xi eta‖ = 1)
    (x y : ℝ) (hx : 0 < mu.real {x}) (hy : 0 < mu.real {y}) :
    jointPhase xi eta x = jointPhase xi eta y := by
  let := complex_strictConvexSpace
  have hbound : ∀ᵐ a ∂mu, ‖jointPhase xi eta a‖ ≤ 1 :=
    Filter.Eventually.of_forall fun a => (jointPhase_norm xi eta a).le
  rcases ae_eq_const_or_norm_integral_lt_of_norm_le_const hbound with hconst | hstrict
  · let z : ℂ := ⨍ a, jointPhase xi eta a ∂mu
    have hae : ∀ᵐ a ∂mu, jointPhase xi eta a = z := hconst
    have hpoint (a : ℝ) (ha : 0 < mu.real {a}) : jointPhase xi eta a = z := by
      by_contra hbad
      have hsub : ({a} : Set ℝ) ⊆ {b | jointPhase xi eta b ≠ z} := by
        intro b hb
        obtain rfl := Set.mem_singleton_iff.mp hb
        exact hbad
      have hnull : mu {b | jointPhase xi eta b ≠ z} = 0 := ae_iff.mp hae
      have hzero : mu {a} = 0 := le_antisymm
        ((measure_mono hsub).trans_eq hnull) (by positivity)
      have hreal : mu.real {a} = 0 := by simp only [measureReal_def, hzero, ENNReal.toReal_zero]
      linarith
    exact (hpoint x hx).trans (hpoint y hy).symm
  · have hlt : ‖jointCharacteristic mu xi eta‖ < 1 := by
      simpa [jointCharacteristic, measureReal_def] using hstrict
    exact False.elim ((ne_of_lt hlt) hmod)

theorem jointPhase_eq_iff_lattice (xi eta x y : ℝ) :
    jointPhase xi eta x = jointPhase xi eta y ↔
      ∃ m : ℤ, xi * (x - y) + eta * (x ^ 2 - y ^ 2) = (2 * Real.pi) * (m : ℝ) := by
  unfold jointPhase
  rw [Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have him := congrArg Complex.im hm
    norm_num [pow_two] at him
    nlinarith [him]
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    apply Complex.ext
    · simp [pow_two]
    · norm_num [pow_two]
      nlinarith [hm]

theorem jointCharacteristic_norm_lt_one_of_positive_atoms (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hpos : ∀ i, 0 < mu.real {fixedAtom i})
    (xi eta : ℝ) (hne : xi ≠ 0 ∨ eta ≠ 0) :
    ‖jointCharacteristic mu xi eta‖ < 1 := by
  have hle := jointCharacteristic_norm_le_one mu xi eta
  by_contra hnlt
  have hmod : ‖jointCharacteristic mu xi eta‖ = 1 := le_antisymm hle (not_lt.mp hnlt)
  have hb : 0 < mu.real {4 + Real.sqrt 10} := by
    simpa [fixedAtom, baseAtom] using hpos (Sum.inl 2)
  have hmem (i : AtomicIndex) : ∃ m : ℤ,
      xi * (fixedAtom i - (4 + Real.sqrt 10)) +
        eta * ((fixedAtom i) ^ 2 - (4 + Real.sqrt 10) ^ 2) = (2 * Real.pi) * (m : ℝ) :=
    (jointPhase_eq_iff_lattice xi eta (fixedAtom i) (4 + Real.sqrt 10)).mp
      (jointPhase_eq_of_modulus_one mu xi eta hmod _ _ (hpos i) hb)
  obtain ⟨hxi, heta⟩ := fixedAtom_no_projection_lattice (2 * Real.pi)
    (mul_pos (by norm_num) Real.pi_pos) xi eta hmem
  rcases hne with hne | hne
  · exact hne hxi
  · exact hne heta

end
end Shao.OQ3
