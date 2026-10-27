import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.Normed.Group.Constructions

namespace Shao.OQ3
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

theorem centered_gaussian_subgaussian_mgf
    (v : ℝ≥0) :
    ProbabilityTheory.HasSubgaussianMGF (fun x : ℝ => x) v (ProbabilityTheory.gaussianReal 0 v) := by
  constructor
  · intro t
    exact ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := v) t
  · intro t
    rw [ProbabilityTheory.mgf_fun_id_gaussianReal]
    simp

theorem centered_gaussian_abs_tail_le
    (v : ℝ≥0) (eps : ℝ) (heps : 0 ≤ eps) :
    (ProbabilityTheory.gaussianReal 0 v).real {x : ℝ | eps < |x|} ≤
      2 * Real.exp (-eps ^ 2 / (2 * (v : ℝ))) := by
  let mu := ProbabilityTheory.gaussianReal 0 v
  have hX := centered_gaussian_subgaussian_mgf v
  have hp : mu.real {x : ℝ | eps ≤ x} ≤ Real.exp (-eps ^ 2 / (2 * (v : ℝ))) :=
    hX.measure_ge_le heps
  have hn : mu.real {x : ℝ | eps ≤ -x} ≤ Real.exp (-eps ^ 2 / (2 * (v : ℝ))) :=
    hX.neg.measure_ge_le heps
  have hsub : {x : ℝ | eps < |x|} ⊆
      {x : ℝ | eps ≤ x} ∪ {x : ℝ | eps ≤ -x} := by
    intro x hx
    rcases le_total 0 x with hx0 | hx0
    · exact Or.inl (by simpa only [abs_of_nonneg hx0] using hx.le)
    · exact Or.inr (by simpa only [abs_of_nonpos hx0] using hx.le)
  calc
    _ ≤ mu.real ({x : ℝ | eps ≤ x} ∪ {x : ℝ | eps ≤ -x}) := measureReal_mono hsub
    _ ≤ mu.real {x : ℝ | eps ≤ x} + mu.real {x : ℝ | eps ≤ -x} := measureReal_union_le _ _
    _ ≤ Real.exp (-eps ^ 2 / (2 * (v : ℝ))) +
        Real.exp (-eps ^ 2 / (2 * (v : ℝ))) := add_le_add hp hn
    _ = _ := by ring

theorem pair_gaussian_noise_tail_le
    (b : ℝ) (hb : 0 < b) (eps : ℝ) (heps : 0 ≤ eps) :
    let v : ℝ≥0 := Real.toNNReal (2 * b)
    let gamma : Measure (ℝ × ℝ) :=
      (ProbabilityTheory.gaussianReal 0 v).prod (ProbabilityTheory.gaussianReal 0 v)
    gamma.real {y : ℝ × ℝ | eps < ‖y‖} ≤
      4 * Real.exp (-eps ^ 2 / (4 * b)) := by
  intro v gamma
  let A : Set ℝ := {x : ℝ | eps < |x|}
  have hset : {y : ℝ × ℝ | eps < ‖y‖} =
      (A ×ˢ (Set.univ : Set ℝ)) ∪ (Set.univ ×ˢ A) := by
    ext y
    simp only [Set.mem_setOf_eq, Prod.norm_def, Real.norm_eq_abs, lt_max_iff,
      Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, true_and, A]
  have htail := centered_gaussian_abs_tail_le v eps heps
  have hprod :
      gamma.real (A ×ˢ (Set.univ : Set ℝ)) + gamma.real (Set.univ ×ˢ A) =
        2 * (ProbabilityTheory.gaussianReal 0 v).real A := by
    dsimp only [gamma]
    simp only [Measure.real, Measure.prod_prod, measure_univ, mul_one, one_mul]
    ring
  have hv : (v : ℝ) = 2 * b := by
    dsimp only [v]
    rw [Real.toNNReal_of_nonneg (by positivity : 0 ≤ 2 * b)]
    rfl
  have hd : 2 * (v : ℝ) = 4 * b := by rw [hv]; ring
  calc
    _ = gamma.real ((A ×ˢ (Set.univ : Set ℝ)) ∪ (Set.univ ×ˢ A)) := by rw [hset]
    _ ≤ gamma.real (A ×ˢ (Set.univ : Set ℝ)) + gamma.real (Set.univ ×ˢ A) :=
      measureReal_union_le _ _
    _ = 2 * (ProbabilityTheory.gaussianReal 0 v).real A := hprod
    _ ≤ 4 * Real.exp (-eps ^ 2 / (2 * (v : ℝ))) := by
      change 2 * (ProbabilityTheory.gaussianReal 0 v).real {x : ℝ | eps < |x|} ≤ _
      linarith
    _ = _ := by rw [hd]

end
end Shao.OQ3
