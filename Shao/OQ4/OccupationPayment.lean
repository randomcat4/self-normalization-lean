import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite occupation-layer integral payment

This is the frozen finite deterministic bridge from the layer-mass input O0/OC
to the boundary-defect payment in R5.  The layer-mass estimate is an explicit
independent hypothesis, not a theorem about a killed random walk.
-/

namespace Shao.OQ4

open MeasureTheory
open scoped BigOperators

/-- A left-closed, right-open layer of the measurable depth variable. -/
def boundaryLayer {Ω : Type*} (d : Ω → ℝ) (j : ℕ) : Set Ω :=
  {ω | (j : ℝ) ≤ d ω ∧ d ω < (j : ℝ) + 1}

theorem measurableSet_boundaryLayer {Ω : Type*} [MeasurableSpace Ω]
    {d : Ω → ℝ} (hd : Measurable d) (j : ℕ) : MeasurableSet (boundaryLayer d j) :=
  (measurableSet_le measurable_const hd).inter (measurableSet_lt hd measurable_const)

/-- Finite layer-mass payment with only almost-everywhere depth and layer bounds. -/
theorem finite_occupation_payment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (d F : Ω → ℝ) (L : ℕ) (C : ℝ) (a : ℕ → ℝ)
    (hdmeas : Measurable d) (hF : Integrable F μ) (_hC : 0 ≤ C)
    (ha : ∀ j, j < L → 0 ≤ a j)
    (hd : ∀ᵐ ω ∂μ, 0 ≤ d ω ∧ d ω < (L : ℝ))
    (hcap : ∀ᵐ ω ∂μ, ∀ j, j < L → ω ∈ boundaryLayer d j → F ω ≤ a j)
    (hmass : ∀ j, j < L → μ.real (boundaryLayer d j) ≤ C * ((j : ℝ) + 1)) :
    (∫ ω, F ω ∂μ) ≤ C * ∑ j ∈ Finset.range L, ((j : ℝ) + 1) * a j := by
  let G : Ω → ℝ := fun ω =>
    ∑ j ∈ Finset.range L, (boundaryLayer d j).indicator (fun _ => a j) ω
  have htermI : ∀ j ∈ Finset.range L,
      Integrable ((boundaryLayer d j).indicator (fun _ => a j)) μ := by
    intro j _
    exact (integrable_const (a j)).indicator (measurableSet_boundaryLayer hdmeas j)
  have hGI : Integrable G μ := by
    exact integrable_finsetSum (Finset.range L) htermI
  have hupper : ∀ᵐ ω ∂μ, F ω ≤ G ω := by
    apply (hd.and hcap).mono
    intro ω hgood
    let j : ℕ := ⌊d ω⌋₊
    have hjlower : (j : ℝ) ≤ d ω := Nat.floor_le hgood.1.1
    have hjL : j < L := by
      exact_mod_cast (lt_of_le_of_lt hjlower hgood.1.2)
    have hjlayer : ω ∈ boundaryLayer d j :=
      ⟨hjlower, Nat.lt_floor_add_one (d ω)⟩
    have hnonneg : ∀ r ∈ Finset.range L,
        0 ≤ (boundaryLayer d r).indicator (fun _ => a r) ω := by
      intro r hr
      by_cases hωr : ω ∈ boundaryLayer d r
      · simp only [Set.indicator, hωr, ite_true]
        exact ha r (Finset.mem_range.mp hr)
      · simp only [Set.indicator, hωr, ite_false]
        exact le_rfl
    have hsingle : (boundaryLayer d j).indicator (fun _ => a j) ω ≤ G ω :=
      Finset.single_le_sum hnonneg (Finset.mem_range.mpr hjL)
    have hselected : (boundaryLayer d j).indicator (fun _ => a j) ω = a j := by
      simp only [Set.indicator, hjlayer, ite_true]
    rw [hselected] at hsingle
    exact (hgood.2 j hjL hjlayer).trans hsingle
  calc
    (∫ ω, F ω ∂μ) ≤ ∫ ω, G ω ∂μ := integral_mono_ae hF hGI hupper
    _ = ∑ j ∈ Finset.range L, μ.real (boundaryLayer d j) * a j := by
      dsimp only [G]
      rw [integral_finsetSum (Finset.range L) htermI]
      apply Finset.sum_congr rfl
      intro j _
      simpa only [smul_eq_mul] using
        (integral_indicator_const (a j) (measurableSet_boundaryLayer hdmeas j))
    _ ≤ ∑ j ∈ Finset.range L, (C * ((j : ℝ) + 1)) * a j := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (hmass j (Finset.mem_range.mp hj))
        (ha j (Finset.mem_range.mp hj))
    _ = C * ∑ j ∈ Finset.range L, ((j : ℝ) + 1) * a j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- A closed upper depth h is covered by floor(h)+1 layers, including integer h. -/
theorem finite_occupation_payment_of_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (d F : Ω → ℝ) (h C : ℝ) (a : ℕ → ℝ)
    (hdmeas : Measurable d) (hF : Integrable F μ) (_hh : 0 ≤ h) (hC : 0 ≤ C)
    (ha : ∀ j, j < ⌊h⌋₊ + 1 → 0 ≤ a j)
    (hd : ∀ᵐ ω ∂μ, 0 ≤ d ω ∧ d ω ≤ h)
    (hcap : ∀ᵐ ω ∂μ, ∀ j, j < ⌊h⌋₊ + 1 → ω ∈ boundaryLayer d j → F ω ≤ a j)
    (hmass : ∀ j, j < ⌊h⌋₊ + 1 → μ.real (boundaryLayer d j) ≤ C * ((j : ℝ) + 1)) :
    (∫ ω, F ω ∂μ) ≤ C * ∑ j ∈ Finset.range (⌊h⌋₊ + 1), ((j : ℝ) + 1) * a j := by
  have htop : h < ((⌊h⌋₊ + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one h
  apply finite_occupation_payment μ d F (⌊h⌋₊ + 1) C a hdmeas hF hC ha _ hcap hmass
  exact hd.mono fun _ hω => ⟨hω.1, hω.2.trans_lt htop⟩

end Shao.OQ4
