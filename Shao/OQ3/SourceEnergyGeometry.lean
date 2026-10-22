import Shao.OQ3.SampleBoundary
import Mathlib.Topology.Order.Compact

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

def sourceEnergyRatio (q : ℝ) (n : ℕ) (z : Shao.Path n) : ℝ :=
  Real.sqrt (Shao.energy z / ((n : ℝ) * q))

def sourceFarEnergySet (q H delta : ℝ) : Set ℝ :=
  {R | 0 ≤ R ∧ 1 ≤ q * R ^ 2 ∧ q * R ^ 2 ≤ 1 + H ∧
    delta ≤ q * (R - 1) ^ 2}

private theorem energy_ratio_sq (q : ℝ) (hq : 0 < q) (n : ℕ) (hn : 0 < n)
    (z : Shao.Path n) :
    (n : ℝ) * q * sourceEnergyRatio q n z ^ 2 = Shao.energy z := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnq : 0 < (n : ℝ) * q := mul_pos hnR hq
  dsimp [sourceEnergyRatio]
  rw [Real.sq_sqrt (div_nonneg (Shao.energy_nonneg z) hnq.le)]
  field_simp

theorem sourceFarEnergySet_isCompact (q H delta : ℝ) (hq : 0 < q) (hH : 0 < H) :
    IsCompact (sourceFarEnergySet q H delta) := by
  have hc0 : IsClosed {R : ℝ | 0 ≤ R} := isClosed_le continuous_const continuous_id
  have hc1 : IsClosed {R : ℝ | 1 ≤ q * R ^ 2} := by
    apply isClosed_le continuous_const
    fun_prop
  have hc2 : IsClosed {R : ℝ | q * R ^ 2 ≤ 1 + H} := by
    apply isClosed_le _ continuous_const
    fun_prop
  have hc3 : IsClosed {R : ℝ | delta ≤ q * (R - 1) ^ 2} := by
    apply isClosed_le continuous_const
    fun_prop
  have hc : IsClosed (sourceFarEnergySet q H delta) :=
    hc0.inter (hc1.inter (hc2.inter hc3))
  have hU : 0 < (1 + H) / q := div_pos (by linarith) hq
  apply (isCompact_Icc (a := (0 : ℝ)) (b := Real.sqrt ((1 + H) / q))).of_isClosed_subset hc
  intro R hR
  refine ⟨hR.1, ?_⟩
  have hsq : R ^ 2 ≤ (1 + H) / q := (le_div_iff₀ hq).mpr (by
    simpa only [mul_comm] using hR.2.2.1)
  apply (sq_le_sq₀ hR.1 (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hU.le]
  exact hsq

theorem sourceTail_normalDeviation_energy_lower (q : ℝ) (hq : 0 < q)
    (n : ℕ) (hn : 0 < n) (z : Shao.Path n) (htail : z ∈ sourceTail q n) :
    -((n : ℝ) * q * (sourceEnergyRatio q n z - 1) ^ 2) ≤ normalDeviation q z := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have he := energy_ratio_sq q hq n hn z
  have hE := Shao.energy_nonneg z
  have hR : 0 ≤ sourceEnergyRatio q n z := Real.sqrt_nonneg _
  let T : ℝ := Real.sqrt q / 4 * Real.sqrt ((n : ℝ) * Shao.energy z)
  let U : ℝ := (n : ℝ) * q * sourceEnergyRatio q n z / 4
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hTsq : T ^ 2 = (n : ℝ) * q * Shao.energy z / 16 := by
    dsimp [T]
    rw [mul_pow, div_pow, Real.sq_sqrt hq.le,
      Real.sq_sqrt (mul_nonneg hnR.le hE)]
    ring
  have hUsq : U ^ 2 = (n : ℝ) * q * Shao.energy z / 16 := by
    calc
      U ^ 2 = ((n : ℝ) * q) / 16 *
          ((n : ℝ) * q * sourceEnergyRatio q n z ^ 2) := by dsimp [U]; ring
      _ = (n : ℝ) * q * Shao.energy z / 16 := by rw [he]; ring
  have hTU : T = U := (sq_eq_sq₀ hT hU).mp (hTsq.trans hUsq.symm)
  have hsum : U ≤ ∑ i, z i := hTU ▸ htail.2
  rw [normalDeviation_eq_sum_energy]
  calc
    -((n : ℝ) * q * (sourceEnergyRatio q n z - 1) ^ 2) =
        8 * U - Shao.energy z - (n : ℝ) * q := by
      rw [← he]
      dsimp [U]
      ring
    _ ≤ 8 * (∑ i, z i) - Shao.energy z - (n : ℝ) * q := by linarith

theorem sourceTail_far_energy_mem (q H delta : ℝ) (hq : 0 < q)
    (hH : 0 < H) (hdelta : 0 < delta) (n : ℕ) (hn : 0 < n)
    (z : Shao.Path n) (henergy : ∀ i : Fin n, 1 ≤ (z i) ^ 2 ∧ (z i) ^ 2 ≤ 1 + H)
    (htail : z ∈ sourceTail q n) (hfar : normalDeviation q z ≤ -delta * (n : ℝ)) :
    sourceEnergyRatio q n z ∈ sourceFarEnergySet q H delta ∧
      0 < sourceEnergyRatio q n z ∧ sourceEnergyRatio q n z ≠ 1 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnq : 0 < (n : ℝ) * q := mul_pos hnR hq
  have hupper : 0 < (n : ℝ) * (1 + H) := mul_pos hnR (add_pos zero_lt_one hH)
  have he := energy_ratio_sq q hq n hn z
  have hElow : (n : ℝ) ≤ Shao.energy z := by
    calc
      (n : ℝ) = ∑ _ : Fin n, (1 : ℝ) := by simp
      _ ≤ Shao.energy z := Finset.sum_le_sum (fun i _ => (henergy i).1)
  have hEhigh : Shao.energy z ≤ (n : ℝ) * (1 + H) := by
    calc
      Shao.energy z ≤ ∑ _ : Fin n, (1 + H) :=
        Finset.sum_le_sum (fun i _ => (henergy i).2)
      _ = (n : ℝ) * (1 + H) := by simp; ring
  have hlow : 1 ≤ q * sourceEnergyRatio q n z ^ 2 := by
    apply (mul_le_mul_iff_right₀ hnR).mp
    nlinarith only [he, hElow]
  have hhigh : q * sourceEnergyRatio q n z ^ 2 ≤ 1 + H := by
    apply (mul_le_mul_iff_right₀ hnR).mp
    nlinarith only [he, hEhigh, hupper]
  have hgeom := sourceTail_normalDeviation_energy_lower q hq n hn z htail
  have hdeltaR : delta ≤ q * (sourceEnergyRatio q n z - 1) ^ 2 := by
    apply (mul_le_mul_iff_right₀ hnR).mp
    nlinarith only [hgeom, hfar]
  have hR : 0 < sourceEnergyRatio q n z := by
    exact Real.sqrt_pos_of_pos (div_pos (hnR.trans_le hElow) hnq)
  refine ⟨⟨hR.le, hlow, hhigh, hdeltaR⟩, hR, ?_⟩
  intro hReq
  rw [hReq] at hdeltaR
  norm_num at hdeltaR
  linarith

end
end Shao.OQ3
