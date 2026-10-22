import Shao.OQ3.FiniteStageMeasure
import Shao.OQ3.ResonanceArithmetic

/-!
# Maximal normal lattice spans of the actual finite laws

Source: current/oq3/proofs/r1/report.md, lines 113-119 and 396-406.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U8 scope: fb35d6d762e70ee479b05d636bca2a2f7b22d70f605fed611e3cff81a378b2d6.
-/

namespace Shao.OQ3

open MeasureTheory
open scoped Matrix

noncomputable section

def HasNormalLattice (mu : Measure ℝ) (h : ℝ) : Prop :=
  0 < h ∧ ∃ offset : ℝ, ∀ᵐ x ∂mu, ∃ k : ℤ,
    normalValue x = offset + h * (k : ℝ)

def IsMaximalNormalLattice (mu : Measure ℝ) (h : ℝ) : Prop :=
  HasNormalLattice mu h ∧ ∀ h' : ℝ, HasNormalLattice mu h' → h' ≤ h

theorem stageAtom_normalValue_lattice (J : ℕ) (i : Fin 4 ⊕ Fin J) :
  ∃ k : ℤ, normalValue (stageAtom (fun j : Fin J => addedAtom j.val) i) =
    dyadicMesh J * (k : ℝ) := by
  obtain ⟨k, hk⟩ := stageAtom_normalValue_scaled_integer J i
  refine ⟨k, ?_⟩
  change normalValue (stageAtom (fun j : Fin J => addedAtom j.val) i) =
    ((2 : ℝ) ^ J)⁻¹ * (k : ℝ)
  rw [← hk]
  field_simp

theorem addedAtom_normal_difference (J : ℕ) :
  normalValue (addedAtom J) - normalValue (baseAtom 2) = dyadicMesh (J + 1) := by
  rw [addedAtom_normalValue, congrFun normalValue_baseAtom 2]
  norm_num

theorem normal_lattice_of_stage_range (mu : Measure ℝ) (J : ℕ)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i)) :
  HasNormalLattice mu (dyadicMesh J) := by
  refine ⟨by unfold dyadicMesh; positivity, 0, ?_⟩
  filter_upwards [hrange] with x hx
  obtain ⟨i, rfl⟩ := hx
  simpa only [zero_add] using stageAtom_normalValue_lattice J i

private theorem holds_at_positive_atom (mu : Measure ℝ) (A : ℝ → Prop)
    (hae : ∀ᵐ x ∂mu, A x) (x : ℝ) (hx : 0 < mu.real {x}) : A x := by
  by_contra hbad
  have hsub : ({x} : Set ℝ) ⊆ {y | ¬ A y} := by
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact hbad
  have hnull : mu {y | ¬ A y} = 0 := ae_iff.mp hae
  have hzero : mu {x} = 0 := le_antisymm ((measure_mono hsub).trans_eq hnull) (by positivity)
  have hreal : mu.real {x} = 0 := by simp only [measureReal_def, hzero, ENNReal.toReal_zero]
  exact (ne_of_gt hx) hreal

theorem normal_lattice_span_le_of_positive_atoms (mu : Measure ℝ) (h : ℝ)
    (hspan : HasNormalLattice mu h) (x y : ℝ)
    (hx : 0 < mu.real {x}) (hy : 0 < mu.real {y})
    (hdiff : 0 < normalValue x - normalValue y) :
  h ≤ normalValue x - normalValue y := by
  obtain ⟨hh, offset, hae⟩ := hspan
  obtain ⟨kx, hkx⟩ := holds_at_positive_atom mu _ hae x hx
  obtain ⟨ky, hky⟩ := holds_at_positive_atom mu _ hae y hy
  have heq : normalValue x - normalValue y = h * ((kx - ky : ℤ) : ℝ) := by
    push_cast
    linarith [hkx, hky]
  have hne : kx - ky ≠ 0 := by
    intro hz
    rw [hz, Int.cast_zero, mul_zero] at heq
    linarith
  have hlarge : (1 : ℝ) ≤ |((kx - ky : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hne
  calc
    h = h * 1 := by ring
    _ ≤ h * |((kx - ky : ℤ) : ℝ)| := mul_le_mul_of_nonneg_left hlarge hh.le
    _ = |normalValue x - normalValue y| := by rw [heq, abs_mul, abs_of_pos hh]
    _ = normalValue x - normalValue y := abs_of_pos hdiff

theorem stage_normal_span_maximal (mu : Measure ℝ) (J : ℕ)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
  IsMaximalNormalLattice mu (dyadicMesh J) := by
  refine ⟨normal_lattice_of_stage_range mu J hrange, ?_⟩
  intro h hspan
  cases J with
  | zero =>
    have hx : 0 < mu.real {baseAtom 1} := hpos (Sum.inl 1)
    have hy : 0 < mu.real {baseAtom 2} := hpos (Sum.inl 2)
    have hd : normalValue (baseAtom 1) - normalValue (baseAtom 2) = (1 : ℝ) := by
      rw [congrFun normalValue_baseAtom 1, congrFun normalValue_baseAtom 2]
      norm_num
    have hle := normal_lattice_span_le_of_positive_atoms mu h hspan
      (baseAtom 1) (baseAtom 2) hx hy (by rw [hd]; norm_num)
    simpa only [hd, dyadicMesh, pow_zero, inv_one] using hle
  | succ J =>
    have hx : 0 < mu.real {addedAtom J} := hpos (Sum.inr ⟨J, Nat.lt_succ_self J⟩)
    have hy : 0 < mu.real {baseAtom 2} := hpos (Sum.inl 2)
    have hdiff : 0 < normalValue (addedAtom J) - normalValue (baseAtom 2) := by
      rw [addedAtom_normal_difference]
      unfold dyadicMesh
      positivity
    have hle := normal_lattice_span_le_of_positive_atoms mu h hspan
      (addedAtom J) (baseAtom 2) hx hy hdiff
    simpa only [addedAtom_normal_difference] using hle

theorem finite_atomic_normal_span_maximal (ell : ℝ) (p : Fin 4 → ℝ)
    (r : ℕ → ℝ) (J : ℕ)
    (hp : ∀ i, 0 < finiteBase ell p r J i) (hr : ∀ j, 0 < r j) :
  IsMaximalNormalLattice (atomicMeasure (finiteMass ell p r J)) (dyadicMesh J) := by
  have hw := finiteMass_nonneg ell p r J (fun i => (hp i).le) (fun j => (hr j).le)
  apply stage_normal_span_maximal _ J (atomicMeasure_finiteMass_ae_range ell p r J)
  intro i
  cases i with
  | inl i =>
    change 0 < (atomicMeasure (finiteMass ell p r J)).real {fixedAtom (Sum.inl i)}
    rw [atomicMeasure_real_singleton _ hw]
    exact hp i
  | inr j =>
    change 0 < (atomicMeasure (finiteMass ell p r J)).real {fixedAtom (Sum.inr j.val)}
    rw [atomicMeasure_real_singleton _ hw]
    simpa [finiteMass, j.isLt] using hr j.val

theorem finite_original_normal_span_maximal (ell q : ℝ) (p : Fin 4 → ℝ)
    (r : ℕ → ℝ) (J : ℕ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hp : ∀ i, 0 < finiteBase ell p r J i) (hr : ∀ j, 0 < r j) :
  IsMaximalNormalLattice (originalMeasure ell (finiteMass ell p r J)) (dyadicMesh J) := by
  apply stage_normal_span_maximal _ J (originalMeasure_finiteMass_ae_range ell p r J)
  exact finite_original_atom_pos ell q p r J hM hc hp hr

theorem exists_source_finite_maximal_normal_family :
  ∃ (p : Fin 4 → ℝ) (q eps : ℝ), (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧
    0 < eps ∧ (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
    ∀ (r : ℕ → ℝ), (∀ j, 0 < r j) → Summable r → (∑' j, r j) < eps →
      ∀ J : ℕ,
        IsMaximalNormalLattice (atomicMeasure (finiteMass sourceEll p r J)) (dyadicMesh J) ∧
        IsMaximalNormalLattice (originalMeasure sourceEll (finiteMass sourceEll p r J))
          (dyadicMesh J) := by
  obtain ⟨p, q, eps, hp, hlo, hhi, heps, hc, hfamily⟩ := exists_source_finite_and_limit_family
  refine ⟨p, q, eps, hp, hlo, hhi, heps, hc, ?_⟩
  intro r hr hs ht J
  obtain ⟨_, _, hstages⟩ := hfamily r hr hs ht
  obtain ⟨hpJ, _, _, _, _⟩ := hstages J
  exact ⟨finite_atomic_normal_span_maximal sourceEll p r J hpJ hr,
    finite_original_normal_span_maximal sourceEll q p r J
      source_constraintMatrix_nonsingular hc hpJ hr⟩

end
end Shao.OQ3
