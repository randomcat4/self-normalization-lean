import Shao.OQ3.EnergyBernoulliMGF
import Shao.OQ3.SourceEnergyGeometry

namespace Shao.OQ3
open MeasureTheory
noncomputable section

theorem exists_source_far_energy_exponential_cover (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q H ell delta : ℝ)
    (hq0 : 1 < q) (hq1 : q < 103 / 100) (hH0 : 50 < H) (hH1 : H < 51)
    (hell : 0 ≤ ell) (hgap : ell * q < 7 / 200) (hdelta : 0 < delta)
    (henergy : ∀ᵐ x ∂mu, 1 ≤ x ^ 2 ∧ x ^ 2 ≤ 1 + H)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂mu) = q) :
    ∃ c : ℝ, 0 < c ∧ ∃ T : Finset ℝ,
      (∀ t ∈ T, Integrable (fun x : ℝ => Real.exp (t * (x ^ 2 - q))) mu ∧
        0 < (∫ x : ℝ, Real.exp (t * (x ^ 2 - q)) ∂mu)) ∧
      ∀ R ∈ sourceFarEnergySet q H delta, ∃ t ∈ T,
        ell * q * (R - 1) ^ 2 + c < t * (q * R ^ 2 - q) -
          Real.log (∫ x : ℝ, Real.exp (t * (x ^ 2 - q)) ∂mu) := by
  classical
  have hq : 0 < q := lt_trans zero_lt_one hq0
  have hH : 0 < H := by linarith
  let g : ℝ := 7 / 200 - ell * q
  have hg : 0 < g := sub_pos.mpr hgap
  let c : ℝ := delta * g / (4 * q)
  have hc : 0 < c := div_pos (mul_pos hdelta hg) (mul_pos (by norm_num) hq)
  let Z : ℝ → ℝ := fun t => ∫ x : ℝ, Real.exp (t * (x ^ 2 - q)) ∂mu
  have hactual (t : ℝ) :
      Integrable (fun x : ℝ => Real.exp (t * (x ^ 2 - q))) mu ∧ 0 < Z t := by
    have h := bounded_energy_logMGF_le_bernoulli mu hb q H t hH henergy hsecond
    exact ⟨h.1, h.2.1⟩
  have hpoint : ∀ R ∈ sourceFarEnergySet q H delta, ∃ t : ℝ,
      ell * q * (R - 1) ^ 2 + 2 * c < t * (q * R ^ 2 - q) - Real.log (Z t) := by
    intro R hR
    have hRpos : 0 < R := by
      by_contra hn
      have hRzero : R = 0 := le_antisymm (le_of_not_gt hn) hR.1
      have he := hR.2.1
      rw [hRzero] at he
      norm_num at he
    have hRne : R ≠ 1 := by
      intro heq
      have hd := hR.2.2.2
      rw [heq] at hd
      norm_num at hd
      linarith
    let p : ℝ := (q * R ^ 2 - 1) / H
    let z : ℝ := (q - 1) / H
    have hp0 : 0 ≤ p := div_nonneg (sub_nonneg.mpr hR.2.1) hH.le
    have hp1 : p ≤ 1 := (div_le_one hH).mpr (by linarith [hR.2.2.1])
    have hz0 : 0 < z := div_pos (sub_pos.mpr hq0) hH
    have hz1 : z < 1 := (div_lt_one hH).mpr (by linarith)
    have hmargin : 4 * c ≤ g * (R - 1) ^ 2 := by
      have hm := mul_le_mul_of_nonneg_right hR.2.2.2 hg.le
      have hceq : 4 * c * q = delta * g := by
        dsimp [c]
        field_simp
      apply (mul_le_mul_iff_right₀ hq).mp
      nlinarith only [hm, hceq]
    have hD := binaryRelativeEntropy_source_gap q H R hq0 hq1 hH0 hH1
      hRpos hRne hp0 hp1
    have hweight : 0 ≤ ell * q * (R - 1) ^ 2 :=
      mul_nonneg (mul_nonneg hell hq.le) (sq_nonneg _)
    have hL : ell * q * (R - 1) ^ 2 + 2 * c < binaryRelativeEntropy p z := by
      dsimp [g] at hmargin
      change (7 / 200) * (R - 1) ^ 2 < binaryRelativeEntropy p z at hD
      nlinarith only [hmargin, hD, hc, hweight]
    obtain ⟨theta, htheta, htest⟩ :=
      exists_binary_exponential_test p z _ hp0 hp1 hz0 hz1 hL
    let t : ℝ := theta / H
    have htH : t * H = theta := by dsimp [t]; field_simp
    have htp : theta * p = t * (q * R ^ 2 - 1) := by
      dsimp [p, t]
      ring
    have hmgf := (bounded_energy_logMGF_le_bernoulli mu hb q H t hH henergy hsecond).2.2
    change Real.log (Z t) ≤ -t * (q - 1) +
      Real.log (1 - z + z * Real.exp (t * H)) at hmgf
    rw [htH] at hmgf
    refine ⟨t, ?_⟩
    rw [htp] at htest
    nlinarith only [htest, hmgf]
  let U : ℝ → Set ℝ := fun t =>
    {R | c < t * (q * R ^ 2 - q) - Real.log (Z t) - ell * q * (R - 1) ^ 2}
  have hU (t : ℝ) : IsOpen (U t) := by
    apply isOpen_lt continuous_const
    fun_prop
  have hcover : sourceFarEnergySet q H delta ⊆ ⋃ t : ℝ, U t := by
    intro R hR
    obtain ⟨t, ht⟩ := hpoint R hR
    apply Set.mem_iUnion.mpr
    refine ⟨t, ?_⟩
    change c < t * (q * R ^ 2 - q) - Real.log (Z t) - ell * q * (R - 1) ^ 2
    linarith
  obtain ⟨T, hT⟩ := (sourceFarEnergySet_isCompact q H delta hq hH).elim_finite_subcover
    U hU hcover
  refine ⟨c, hc, T, ?_, ?_⟩
  · intro t ht
    exact hactual t
  · intro R hR
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp (hT hR)
    obtain ⟨htT, htR⟩ := Set.mem_iUnion.mp ht
    refine ⟨t, htT, ?_⟩
    change c < t * (q * R ^ 2 - q) - Real.log (Z t) - ell * q * (R - 1) ^ 2 at htR
    change ell * q * (R - 1) ^ 2 + c < t * (q * R ^ 2 - q) - Real.log (Z t)
    linarith

end
end Shao.OQ3
