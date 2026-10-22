import Shao.OQ3.NormalLayerMassBound
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

namespace Shao.OQ3
open MeasureTheory Filter
open scoped BigOperators Matrix
noncomputable section

def positiveNormalLayerTerm (mu : Measure ℝ) (q ell h theta : ℝ) (n k : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) * Real.exp (-ell * (h * ((k : ℝ) + 1 - theta))) *
    (Measure.pi (fun _ : Fin n => mu)).real
      {z : Shao.Path n | normalDeviation q z = h * ((k : ℝ) + 1 - theta)}

theorem exists_stage_positive_layer_tail_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a ell : ℝ) (hell : 0 < ell)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ theta ∈ Set.Icc (0 : ℝ) 1,
      Summable (fun k : ℕ => positiveNormalLayerTerm mu q ell (dyadicMesh J) theta n k) ∧
      ∀ K : ℕ, (∑' k : ℕ,
        positiveNormalLayerTerm mu q ell (dyadicMesh J) theta n (K + k)) ≤
          C * Real.exp (-ell * dyadicMesh J) ^ K /
            (1 - Real.exp (-ell * dyadicMesh J)) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_stage_normal_layer_mass_bound mu J q a hb hq ha hS hD hrange hpos
  have hmesh : 0 < dyadicMesh J := by unfold dyadicMesh; positivity
  let rho := Real.exp (-ell * dyadicMesh J)
  have hrho : 0 < rho := Real.exp_pos _
  have hrho1 : rho < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hell hmesh])
  have habs : |rho| < 1 := by rw [abs_of_pos hrho]; exact hrho1
  have hden : 0 < 1 - rho := sub_pos.mpr hrho1
  have hsumrho : Summable (fun k : ℕ => rho ^ k) := summable_geometric_of_abs_lt_one habs
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with n hn
  intro theta htheta
  have hnonneg (k : ℕ) :
      0 ≤ positiveNormalLayerTerm mu q ell (dyadicMesh J) theta n k := by
    unfold positiveNormalLayerTerm
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le) ENNReal.toReal_nonneg
  have hmajor (k : ℕ) :
      positiveNormalLayerTerm mu q ell (dyadicMesh J) theta n k ≤ C * rho ^ k := by
    have hexp : Real.exp (-ell * (dyadicMesh J * ((k : ℝ) + 1 - theta))) ≤ rho ^ k := by
      dsimp [rho]
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hh := mul_nonneg (mul_pos hell hmesh).le (sub_nonneg.mpr htheta.2)
      nlinarith
    unfold positiveNormalLayerTerm
    calc
      _ = Real.exp (-ell * (dyadicMesh J * ((k : ℝ) + 1 - theta))) *
          (Real.sqrt (n : ℝ) * (Measure.pi (fun _ : Fin n => mu)).real
            {z : Shao.Path n | normalDeviation q z = dyadicMesh J * ((k : ℝ) + 1 - theta)}) := by ring
      _ ≤ Real.exp (-ell * (dyadicMesh J * ((k : ℝ) + 1 - theta))) * C :=
        mul_le_mul_of_nonneg_left (hn _) (Real.exp_pos _).le
      _ ≤ rho ^ k * C := mul_le_mul_of_nonneg_right hexp hC.le
      _ = C * rho ^ k := mul_comm _ _
  have hsumMajor : Summable (fun k : ℕ => C * rho ^ k) := hsumrho.mul_left C
  have hsumTerm : Summable (fun k : ℕ =>
      positiveNormalLayerTerm mu q ell (dyadicMesh J) theta n k) :=
    Summable.of_nonneg_of_le hnonneg hmajor hsumMajor
  refine ⟨hsumTerm, ?_⟩
  intro K
  have hmajorShift (k : ℕ) :
      positiveNormalLayerTerm mu q ell (dyadicMesh J) theta n (K + k) ≤
        (C * rho ^ K) * rho ^ k := by
    calc
      _ ≤ C * rho ^ (K + k) := hmajor (K + k)
      _ = _ := by rw [pow_add]; ring
  have hsumMajorShift : Summable (fun k : ℕ => (C * rho ^ K) * rho ^ k) :=
    hsumrho.mul_left _
  have hsumShift : Summable (fun k : ℕ =>
      positiveNormalLayerTerm mu q ell (dyadicMesh J) theta n (K + k)) :=
    Summable.of_nonneg_of_le (fun k => hnonneg (K + k)) hmajorShift hsumMajorShift
  calc
    _ ≤ ∑' k : ℕ, (C * rho ^ K) * rho ^ k :=
      hsumShift.tsum_le_tsum hmajorShift hsumMajorShift
    _ = (C * rho ^ K) * ∑' k : ℕ, rho ^ k := hsumrho.tsum_mul_left _
    _ = C * Real.exp (-ell * dyadicMesh J) ^ K /
        (1 - Real.exp (-ell * dyadicMesh J)) := by
      rw [tsum_geometric_of_abs_lt_one habs]
      rfl

end
end Shao.OQ3
