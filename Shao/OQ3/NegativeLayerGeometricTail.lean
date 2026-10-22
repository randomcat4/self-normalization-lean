import Shao.OQ3.GlobalNegativeLayerBound

namespace Shao.OQ3
open MeasureTheory Filter
open scoped BigOperators
noncomputable section

def negativeNormalLayerTerm (mu : Measure ℝ) (q ell h theta : ℝ)
    (n k : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) * Real.exp (ell * (h * ((k : ℝ) + theta))) *
    (Measure.pi (fun _ : Fin n => mu)).real
      {z : Shao.Path n | normalDeviation q z = -(h * ((k : ℝ) + theta)) ∧
        z ∈ sourceTail q n}

theorem exists_source_negative_layer_geometric_tail (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q H ell : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq0 : 1 < q) (hq1 : q < 103 / 100) (hH0 : 50 < H) (hH1 : H < 51)
    (hell : 0 ≤ ell) (hellq : ell * q < 7 / 200)
    (henergy : ∀ᵐ x ∂mu, 1 ≤ x ^ 2 ∧ x ^ 2 ≤ 1 + H)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = q / 4)
    (hS : 0 < normalVariance mu) (hD : 0 < (parabolaCovariance mu).det)
    (hgap : ell < q / (32 * transverseVariance mu))
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ∃ gamma C : ℝ, 0 < gamma ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop, ∀ theta ∈ Set.Icc (0 : ℝ) 1,
        Summable (fun k : ℕ =>
          negativeNormalLayerTerm mu q ell (dyadicMesh J) theta n k) ∧
        ∀ K : ℕ, (∑' k : ℕ,
          negativeNormalLayerTerm mu q ell (dyadicMesh J) theta n (K + k)) ≤
            C * Real.exp (-gamma * dyadicMesh J) ^ K /
              (1 - Real.exp (-gamma * dyadicMesh J)) := by
  obtain ⟨gamma, C, hgamma, hC, hbound⟩ :=
    exists_global_source_negative_layer_bound mu J q H ell hb hq0 hq1 hH0 hH1 hell hellq
      henergy hmeanY hmeanX hS hD hgap hrange hpos
  have hmesh : 0 < dyadicMesh J := by unfold dyadicMesh; positivity
  let rho : ℝ := Real.exp (-gamma * dyadicMesh J)
  have hrho : 0 < rho := Real.exp_pos _
  have hrho1 : rho < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hgamma hmesh])
  have habs : |rho| < 1 := by rw [abs_of_pos hrho]; exact hrho1
  have hden : 0 < 1 - rho := sub_pos.mpr hrho1
  have hsumrho : Summable (fun k : ℕ => rho ^ k) := summable_geometric_of_abs_lt_one habs
  refine ⟨gamma, C, hgamma, hC, ?_⟩
  filter_upwards [hbound] with n hn
  intro theta htheta
  have hnonneg (k : ℕ) :
      0 ≤ negativeNormalLayerTerm mu q ell (dyadicMesh J) theta n k := by
    unfold negativeNormalLayerTerm
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le) ENNReal.toReal_nonneg
  have hmajor (k : ℕ) :
      negativeNormalLayerTerm mu q ell (dyadicMesh J) theta n k ≤ C * rho ^ k := by
    have ht : 0 ≤ dyadicMesh J * ((k : ℝ) + theta) :=
      mul_nonneg hmesh.le (add_nonneg (Nat.cast_nonneg k) htheta.1)
    have hexp : Real.exp (-gamma * (dyadicMesh J * ((k : ℝ) + theta))) ≤ rho ^ k := by
      dsimp only [rho]
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hh := mul_nonneg (mul_pos hgamma hmesh).le htheta.1
      nlinarith only [hh]
    exact (hn _ ht).trans (mul_le_mul_of_nonneg_left hexp hC.le)
  have hsumMajor : Summable (fun k : ℕ => C * rho ^ k) := hsumrho.mul_left C
  have hsumTerm : Summable (fun k : ℕ =>
      negativeNormalLayerTerm mu q ell (dyadicMesh J) theta n k) :=
    Summable.of_nonneg_of_le hnonneg hmajor hsumMajor
  refine ⟨hsumTerm, ?_⟩
  intro K
  have hmajorShift (k : ℕ) :
      negativeNormalLayerTerm mu q ell (dyadicMesh J) theta n (K + k) ≤
        (C * rho ^ K) * rho ^ k := by
    calc
      _ ≤ C * rho ^ (K + k) := hmajor (K + k)
      _ = _ := by rw [pow_add]; ring
  have hsumMajorShift : Summable (fun k : ℕ => (C * rho ^ K) * rho ^ k) :=
    hsumrho.mul_left _
  have hsumShift : Summable (fun k : ℕ =>
      negativeNormalLayerTerm mu q ell (dyadicMesh J) theta n (K + k)) :=
    Summable.of_nonneg_of_le (fun k => hnonneg (K + k)) hmajorShift hsumMajorShift
  calc
    _ ≤ ∑' k : ℕ, (C * rho ^ K) * rho ^ k :=
      hsumShift.tsum_le_tsum hmajorShift hsumMajorShift
    _ = (C * rho ^ K) * ∑' k : ℕ, rho ^ k := hsumrho.tsum_mul_left _
    _ = C * Real.exp (-gamma * dyadicMesh J) ^ K /
        (1 - Real.exp (-gamma * dyadicMesh J)) := by
      rw [tsum_geometric_of_abs_lt_one habs]
      rfl

end
end Shao.OQ3
