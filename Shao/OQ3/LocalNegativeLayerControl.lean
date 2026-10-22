import Shao.OQ3.LocalNegativeLayerTail
import Shao.OQ3.SampleBoundary
import Mathlib.Analysis.SpecificLimits.Normed

namespace Shao.OQ3
open MeasureTheory Filter
open scoped BigOperators
noncomputable section

def localNegativeNormalLayerTerm (mu : Measure ℝ) (q ell h theta delta : ℝ)
    (n k : ℕ) : ℝ :=
  if h * ((k : ℝ) + theta) / (n : ℝ) ≤ delta then
    Real.sqrt (n : ℝ) * Real.exp (ell * (h * ((k : ℝ) + theta))) *
      (Measure.pi (fun _ : Fin n => mu)).real
        {z : Shao.Path n | normalDeviation q z = -(h * ((k : ℝ) + theta)) ∧
          z ∈ sourceTail q n}
  else 0

theorem exists_local_source_negative_layer_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q ell : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : 0 < q) (hell : 0 ≤ ell)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = q / 4)
    (hS : 0 < normalVariance mu) (hD : 0 < (parabolaCovariance mu).det)
    (hgap : ell < q / (32 * transverseVariance mu))
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ∃ delta gamma C : ℝ, 0 < delta ∧ 0 < gamma ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop, ∀ k : ℝ, 0 ≤ k → k / (n : ℝ) ≤ delta →
        Real.sqrt (n : ℝ) * Real.exp (ell * k) *
          (Measure.pi (fun _ : Fin n => mu)).real
            {z : Shao.Path n | normalDeviation q z = -k ∧ z ∈ sourceTail q n} ≤
          C * Real.exp (-gamma * k) := by
  obtain ⟨delta0, gamma, c, C, hdelta0, hgamma, hc, hC, hbound⟩ :=
    exists_local_negative_layer_tail_bound mu J q (q / 4) ell hb hq hell hmeanY hmeanX hS hD hgap hrange hpos
  let delta : ℝ := min delta0 (16 * delta0 ^ 2 / q)
  have hdelta : 0 < delta := lt_min hdelta0 (div_pos (by positivity) hq)
  have hd0 : delta ≤ delta0 := min_le_left _ _
  have hdq : delta ≤ 16 * delta0 ^ 2 / q := min_le_right _ _
  refine ⟨delta, gamma, C, hdelta, hgamma, hC, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  intro k hk hsmall
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hrad : 0 ≤ (n : ℝ) * q * k / 16 := by positivity
  let r : ℝ := Real.sqrt ((n : ℝ) * q * k / 16)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = (n : ℝ) * q * k / 16 := Real.sq_sqrt hrad
  have hcross : k * q ≤ (16 * delta0 ^ 2) * (n : ℝ) :=
    (div_le_div_iff₀ hnpos hq).mp (hsmall.trans hdq)
  have hmul := mul_le_mul_of_nonneg_right hcross hnpos.le
  have hrsmall : r / (n : ℝ) ≤ delta0 := by
    apply (div_le_iff₀ hnpos).mpr
    dsimp only [r]
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith only [hmul]⟩
  have hsubset : {path : Shao.Path n | normalDeviation q path = -k ∧ path ∈ sourceTail q n} ⊆
      {path : Shao.Path n | normalDeviation q path = -k ∧
        r ≤ |(∑ i : Fin n, path i) - (n : ℝ) * (q / 4)|} := by
    intro path hpath
    have hcurved := ((sourceTail_on_normal_layer q hq n
      (lt_of_lt_of_le Nat.zero_lt_one hn1) path (-k) hpath.1).mp hpath.2).2.2
    have hsquare : r ^ 2 ≤ tangentDeviation q path ^ 2 := by
      rw [hrsq]
      nlinarith only [hcurved]
    have habs : r ≤ |tangentDeviation q path| :=
      (sq_le_sq₀ hr (abs_nonneg _)).mp (by simpa only [sq_abs] using hsquare)
    have hcenter : (∑ i : Fin n, path i) - (n : ℝ) * (q / 4) = tangentDeviation q path := by
      unfold tangentDeviation
      ring
    exact ⟨hpath.1, by rw [hcenter]; exact habs⟩
  have hmass := measureReal_mono (μ := Measure.pi (fun _ : Fin n => mu)) hsubset
  have hI := hn k r hk hr (hsmall.trans hd0) hrsmall (by rw [hrsq])
  have he : Real.exp (-gamma * k - c * r ^ 2 / (n : ℝ)) ≤ Real.exp (-gamma * k) := by
    apply Real.exp_le_exp.mpr
    have hnonneg : 0 ≤ c * r ^ 2 / (n : ℝ) :=
      div_nonneg (mul_nonneg hc.le (sq_nonneg _)) hnpos.le
    linarith only [hnonneg]
  calc
    _ ≤ Real.sqrt (n : ℝ) * Real.exp (ell * k) *
        (Measure.pi (fun _ : Fin n => mu)).real
          {path : Shao.Path n | normalDeviation q path = -k ∧
            r ≤ |(∑ i : Fin n, path i) - (n : ℝ) * (q / 4)|} :=
      mul_le_mul_of_nonneg_left hmass (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)
    _ ≤ C * Real.exp (-gamma * k - c * r ^ 2 / (n : ℝ)) := hI
    _ ≤ _ := mul_le_mul_of_nonneg_left he hC.le

theorem exists_local_negative_layer_geometric_tail (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q ell : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : 0 < q) (hell : 0 ≤ ell)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = q / 4)
    (hS : 0 < normalVariance mu) (hD : 0 < (parabolaCovariance mu).det)
    (hgap : ell < q / (32 * transverseVariance mu))
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ∃ delta gamma C : ℝ, 0 < delta ∧ 0 < gamma ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop, ∀ theta ∈ Set.Icc (0 : ℝ) 1,
        Summable (fun k : ℕ =>
          localNegativeNormalLayerTerm mu q ell (dyadicMesh J) theta delta n k) ∧
        ∀ K : ℕ, (∑' k : ℕ,
          localNegativeNormalLayerTerm mu q ell (dyadicMesh J) theta delta n (K + k)) ≤
            C * Real.exp (-gamma * dyadicMesh J) ^ K /
              (1 - Real.exp (-gamma * dyadicMesh J)) := by
  obtain ⟨delta, gamma, C, hdelta, hgamma, hC, hbound⟩ :=
    exists_local_source_negative_layer_bound mu J q ell hb hq hell hmeanY hmeanX hS hD hgap hrange hpos
  have hmesh : 0 < dyadicMesh J := by unfold dyadicMesh; positivity
  let rho : ℝ := Real.exp (-gamma * dyadicMesh J)
  have hrho : 0 < rho := Real.exp_pos _
  have hrho1 : rho < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hgamma hmesh])
  have habs : |rho| < 1 := by rw [abs_of_pos hrho]; exact hrho1
  have hden : 0 < 1 - rho := sub_pos.mpr hrho1
  have hsumrho : Summable (fun k : ℕ => rho ^ k) := summable_geometric_of_abs_lt_one habs
  refine ⟨delta, gamma, C, hdelta, hgamma, hC, ?_⟩
  filter_upwards [hbound] with n hn
  intro theta htheta
  have hnonneg (k : ℕ) :
      0 ≤ localNegativeNormalLayerTerm mu q ell (dyadicMesh J) theta delta n k := by
    unfold localNegativeNormalLayerTerm
    split_ifs
    · exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le) ENNReal.toReal_nonneg
    · exact le_refl _
  have hmajor (k : ℕ) :
      localNegativeNormalLayerTerm mu q ell (dyadicMesh J) theta delta n k ≤ C * rho ^ k := by
    have ht : 0 ≤ dyadicMesh J * ((k : ℝ) + theta) :=
      mul_nonneg hmesh.le (add_nonneg (Nat.cast_nonneg k) htheta.1)
    have hexp : Real.exp (-gamma * (dyadicMesh J * ((k : ℝ) + theta))) ≤ rho ^ k := by
      dsimp only [rho]
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hh := mul_nonneg (mul_pos hgamma hmesh).le htheta.1
      nlinarith only [hh]
    unfold localNegativeNormalLayerTerm
    split_ifs with hlocal
    · exact (hn _ ht hlocal).trans (mul_le_mul_of_nonneg_left hexp hC.le)
    · exact mul_nonneg hC.le (pow_nonneg hrho.le k)
  have hsumMajor : Summable (fun k : ℕ => C * rho ^ k) := hsumrho.mul_left C
  have hsumTerm : Summable (fun k : ℕ =>
      localNegativeNormalLayerTerm mu q ell (dyadicMesh J) theta delta n k) :=
    Summable.of_nonneg_of_le hnonneg hmajor hsumMajor
  refine ⟨hsumTerm, ?_⟩
  intro K
  have hmajorShift (k : ℕ) :
      localNegativeNormalLayerTerm mu q ell (dyadicMesh J) theta delta n (K + k) ≤
        (C * rho ^ K) * rho ^ k := by
    calc
      _ ≤ C * rho ^ (K + k) := hmajor (K + k)
      _ = _ := by rw [pow_add]; ring
  have hsumMajorShift : Summable (fun k : ℕ => (C * rho ^ K) * rho ^ k) :=
    hsumrho.mul_left _
  have hsumShift : Summable (fun k : ℕ =>
      localNegativeNormalLayerTerm mu q ell (dyadicMesh J) theta delta n (K + k)) :=
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
