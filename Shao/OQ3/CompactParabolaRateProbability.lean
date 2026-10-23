import Shao.OQ3.QuadraticSampleExponentialBound
import Mathlib.Topology.Compactness.Compact

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators Topology
noncomputable section

theorem compact_parabola_rate_probability_upper_bound
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (F : Set (ℝ × ℝ)) (hF : IsCompact F) (c : ℝ)
    (hRate : ∀ w ∈ F, (c : EReal) <
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w) :
    let Domain : Set (ℝ × ℝ) :=
      Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))
    let K : (ℝ × ℝ) → ℝ := fun theta =>
      Real.log (∫ x : ℝ, Real.exp (theta.1 * x + theta.2 * x ^ 2) ∂mu)
    let Test : (ℝ × ℝ) → (ℝ × ℝ) → ℝ := fun theta w =>
      theta.1 * w.1 + theta.2 * w.2 - K theta
    ∃ S : Finset Domain, 0 < (S.card : ℝ) + 1 ∧
      (∀ w ∈ F, ∃ theta ∈ S, c < Test (theta : ℝ × ℝ) w) ∧
      ∀ n : ℕ, 1 ≤ n →
        let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
        let M : Shao.Path n → (ℝ × ℝ) := fun z =>
          ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
        P.real (M ⁻¹' F) ≤ ((S.card : ℝ) + 1) * Real.exp (-(n : ℝ) * c) := by
  classical
  let Domain : Set (ℝ × ℝ) :=
    Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))
  let K : (ℝ × ℝ) → ℝ := fun theta =>
    Real.log (∫ x : ℝ, Real.exp (theta.1 * x + theta.2 * x ^ 2) ∂mu)
  let Test : (ℝ × ℝ) → (ℝ × ℝ) → ℝ := fun theta w =>
    theta.1 * w.1 + theta.2 * w.2 - K theta
  have hpoint : ∀ w ∈ F, ∃ theta : Domain, c < Test (theta : ℝ × ℝ) w := by
    intro w hw
    have hr := hRate w hw
    change (c : EReal) < ⨆ theta : Domain, (Test (theta : ℝ × ℝ) w : EReal) at hr
    obtain ⟨theta, htheta⟩ := lt_iSup_iff.mp hr
    refine ⟨theta, ?_⟩
    exact_mod_cast htheta
  let U : Domain → Set (ℝ × ℝ) := fun theta => {w | c < Test (theta : ℝ × ℝ) w}
  have hU (theta : Domain) : IsOpen (U theta) := by
    apply isOpen_lt continuous_const
    dsimp only [Test]
    fun_prop
  have hcover : F ⊆ ⋃ theta : Domain, U theta := by
    intro w hw
    obtain ⟨theta, htheta⟩ := hpoint w hw
    exact Set.mem_iUnion.mpr ⟨theta, htheta⟩
  obtain ⟨S, hS⟩ := hF.elim_finite_subcover U hU hcover
  refine ⟨S, by positivity, ?_, ?_⟩
  · intro w hw
    obtain ⟨theta, htheta⟩ := Set.mem_iUnion.mp (hS hw)
    obtain ⟨hmem, hvalue⟩ := Set.mem_iUnion.mp htheta
    exact ⟨theta, hmem, hvalue⟩
  · intro n hn
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
    letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
    let M : Shao.Path n → (ℝ × ℝ) := fun z =>
      ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
    have hsubset : M ⁻¹' F ⊆ ⋃ theta ∈ S, M ⁻¹' U theta := by
      intro z hz
      obtain ⟨theta, htheta⟩ := Set.mem_iUnion.mp (hS hz)
      obtain ⟨hmem, hvalue⟩ := Set.mem_iUnion.mp htheta
      exact Set.mem_iUnion.mpr ⟨theta, Set.mem_iUnion.mpr ⟨hmem, hvalue⟩⟩
    have hsingle (theta : Domain) :
        P.real (M ⁻¹' U theta) ≤ Real.exp (-(n : ℝ) * c) := by
      apply iid_quadratic_exponential_separator_bound mu (theta : ℝ × ℝ) theta.property
        n hn (U theta) (hU theta).measurableSet c
      intro w hw
      exact le_of_lt hw
    change P.real (M ⁻¹' F) ≤ ((S.card : ℝ) + 1) * Real.exp (-(n : ℝ) * c)
    calc
      _ ≤ P.real (⋃ theta ∈ S, M ⁻¹' U theta) :=
        measureReal_mono hsubset (measure_ne_top P _)
      _ ≤ ∑ theta ∈ S, P.real (M ⁻¹' U theta) :=
        measureReal_biUnion_finset_le S (fun theta => M ⁻¹' U theta)
      _ ≤ ∑ _theta ∈ S, Real.exp (-(n : ℝ) * c) :=
        Finset.sum_le_sum (fun theta _ => hsingle theta)
      _ = (S.card : ℝ) * Real.exp (-(n : ℝ) * c) := by simp
      _ ≤ ((S.card : ℝ) + 1) * Real.exp (-(n : ℝ) * c) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

end
end Shao.OQ3
