import Shao.Probability.BrownianSpectralEnvelope
import Shao.Probability.BrownianGridBridge

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Shao.Probability.BrownianSup

private def spectralError (x : ℝ) : ℝ :=
  Shao.OQ4.RademacherSpectralTail.absoluteC * Real.exp (-Real.pi ^ 2 / x ^ 2)

private def upperEnvelope (x : ℝ) : ℝ := firstTerm x * (1 + spectralError x)

private theorem firstTerm_positive (x : ℝ) : 0 < firstTerm x := by
  exact mul_pos (div_pos (by norm_num) Real.pi_pos) (Real.exp_pos _)

private theorem upperEnvelope_continuousAt (x : ℝ) (hx : 0 < x) :
    ContinuousAt upperEnvelope x := by
  unfold upperEnvelope firstTerm spectralError
  fun_prop (disch := positivity)

private theorem multiples_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun m : ℕ => d * m) atTop atTop :=
  tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m hd) tendsto_id

variable {Ω : Type*} [MeasurableSpace Ω]
variable (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
variable (hB : IsBrownianReal B P)

include hB in
private theorem coarse_lower_envelope
    (d : ℕ) (hd : 0 < d) (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    firstTerm x - firstTerm x * spectralError x ≤ brownianGridProbability B P d x := by
  apply le_of_forall_pos_le_add
  intro η hη
  have hq := rademacher_coarse_tendsto_brownian_grid B P hB d hd x hx
  apply le_of_tendsto_of_tendsto (tendsto_const_nhds (x :=
    firstTerm x - firstTerm x * spectralError x)) (hq.add_const η)
  have henv := (multiples_tendsto d hd).eventually
    (rademacher_eventual_firstTerm_envelope x hx hx1 η hη)
  filter_upwards [henv, eventually_ge_atTop 1] with m hm hmp
  have hc := (rademacher_coarse_comparison d m hd (by omega) x 1 hx.le (by norm_num)).1
  have he := (abs_le.mp hm).1
  change -(firstTerm x * spectralError x + η) ≤ radSurvival (d * m) x - firstTerm x at he
  linarith

include hB in
private theorem coarse_upper_envelope
    (d : ℕ) (hd : 0 < d) (x ε : ℝ) (hx : 0 < x) (hε : 0 < ε)
    (hxε : x + ε < 1) :
    brownianGridProbability B P d x ≤ upperEnvelope (x + ε) + 6 / ((d : ℝ) * ε ^ 4) := by
  apply le_of_forall_pos_le_add
  intro η hη
  have hq := rademacher_coarse_tendsto_brownian_grid B P hB d hd x hx
  apply le_of_tendsto hq
  have henv := (multiples_tendsto d hd).eventually
    (rademacher_eventual_firstTerm_envelope (x + ε) (by linarith) hxε η hη)
  filter_upwards [henv, eventually_ge_atTop 1] with m hm hmp
  have hc := (rademacher_coarse_comparison d m hd (by omega) x ε hx.le hε).2
  have he := (abs_le.mp hm).2
  change radSurvival (d * m) (x + ε) - firstTerm (x + ε) ≤
    firstTerm (x + ε) * spectralError (x + ε) + η at he
  dsimp only [upperEnvelope]
  nlinarith

private theorem actual_lower_envelope (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    firstTerm x - firstTerm x * spectralError x ≤ probability B P hB x := by
  exact ge_of_tendsto (brownian_dyadic_grid_tendsto_probability B P hB x)
    (Eventually.of_forall (fun r => coarse_lower_envelope B P hB (2 ^ r)
      (pow_pos (by norm_num) r) x hx hx1))

private theorem actual_upper_shifted_envelope (x ε : ℝ) (hx : 0 < x) (hε : 0 < ε)
    (hxε : x + ε < 1) : probability B P hB x ≤ upperEnvelope (x + ε) := by
  have hpow : Tendsto (fun r : ℕ => ((2 ^ r : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have herr : Tendsto (fun r : ℕ => 6 / (((2 ^ r : ℕ) : ℝ) * ε ^ 4)) atTop (𝓝 (0 : ℝ)) := by
    have hi : Tendsto (fun r : ℕ => (((2 ^ r : ℕ) : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp hpow
    convert hi.mul_const (6 / ε ^ 4) using 1
    · funext r
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · simp
  have hup : Tendsto (fun r : ℕ => upperEnvelope (x + ε) +
      6 / (((2 ^ r : ℕ) : ℝ) * ε ^ 4)) atTop (𝓝 (upperEnvelope (x + ε))) := by
    simpa using herr.const_add (upperEnvelope (x + ε))
  exact le_of_tendsto_of_tendsto' (brownian_dyadic_grid_tendsto_probability B P hB x) hup
    (fun r => coarse_upper_envelope B P hB (2 ^ r) (pow_pos (by norm_num) r) x ε hx hε hxε)

private theorem actual_upper_envelope (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    probability B P hB x ≤ upperEnvelope x := by
  let ε : ℕ → ℝ := fun k => (1 - x) / ((k : ℝ) + 2)
  have hden : Tendsto (fun k : ℕ => (k : ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono (fun k : ℕ => by linarith) tendsto_natCast_atTop_atTop
  have hε : Tendsto ε atTop (𝓝 (0 : ℝ)) := by
    simpa [ε, div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hden).const_mul (1 - x)
  have hlim : Tendsto (fun k => upperEnvelope (x + ε k)) atTop (𝓝 (upperEnvelope x)) := by
    apply (upperEnvelope_continuousAt x hx).tendsto.comp
    simpa using hε.const_add x
  apply le_of_tendsto_of_tendsto' (tendsto_const_nhds (x := probability B P hB x)) hlim
  intro k
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hεpos : 0 < ε k := div_pos (by linarith) (by linarith)
  have hεlt : ε k < 1 - x := by
    apply (div_lt_iff₀ (show (0 : ℝ) < (k : ℝ) + 2 by linarith)).2
    nlinarith
  exact actual_upper_shifted_envelope B P hB x (ε k) hx hεpos (by linarith)

theorem actual_brownian_firstTerm_envelope (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    |probability B P hB x / firstTerm x - 1| ≤
      Shao.OQ4.RademacherSpectralTail.absoluteC * Real.exp (-Real.pi ^ 2 / x ^ 2) := by
  have hlo := actual_lower_envelope B P hB x hx hx1
  have hup := actual_upper_envelope B P hB x hx hx1
  have hpos := firstTerm_positive x
  have hraw : |probability B P hB x - firstTerm x| ≤ firstTerm x * spectralError x := by
    apply abs_le.mpr
    dsimp only [upperEnvelope] at hup
    constructor <;> nlinarith
  have heq : probability B P hB x / firstTerm x - 1 =
      (probability B P hB x - firstTerm x) / firstTerm x := by
    field_simp
  rw [heq, abs_div, abs_of_pos hpos]
  apply (div_le_iff₀ hpos).2
  change |probability B P hB x - firstTerm x| ≤ spectralError x * firstTerm x
  simpa only [mul_comm] using hraw

private theorem spectralError_tendsto_zero :
    Tendsto spectralError (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  change Tendsto (fun x : ℝ => Shao.OQ4.RademacherSpectralTail.absoluteC *
    Real.exp (-Real.pi ^ 2 / x ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))
  have hinv : Tendsto (fun x : ℝ => x⁻¹) (𝓝[>] (0 : ℝ)) atTop := tendsto_inv_nhdsGT_zero
  have hp : Tendsto (fun x : ℝ => (x⁻¹) ^ 2) (𝓝[>] (0 : ℝ)) atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hinv
  have hn : Tendsto (fun x : ℝ => -Real.pi ^ 2 / x ^ 2) (𝓝[>] (0 : ℝ)) atBot := by
    simpa only [Function.comp_def, div_eq_mul_inv, inv_pow, neg_mul] using
      tendsto_neg_atTop_atBot.comp (hp.const_mul_atTop (sq_pos_of_pos Real.pi_pos))
  simpa only [spectralError, Function.comp_def, mul_zero] using
    (Real.tendsto_exp_atBot.comp hn).const_mul Shao.OQ4.RademacherSpectralTail.absoluteC

theorem actual_brownian_firstTerm :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x : ℝ, 0 < x → x < δ → |probability B P hB x / firstTerm x - 1| < ε := by
  intro ε hε
  have hev := spectralError_tendsto_zero.eventually (eventually_lt_nhds hε)
  obtain ⟨δ, hδ, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨min δ 1, lt_min hδ (by norm_num), ?_⟩
  intro x hx hxδ
  have henv := actual_brownian_firstTerm_envelope B P hB x hx (lt_of_lt_of_le hxδ (min_le_right _ _))
  exact lt_of_le_of_lt henv (hbound ⟨hx, lt_of_lt_of_le hxδ (min_le_left _ _)⟩)

theorem actual_brownian_eventually_positive :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 < x → x < δ →
      0 < probability B P hB x ∧ 0 < probability B P hB x / firstTerm x := by
  obtain ⟨δ, hδ, hbound⟩ := actual_brownian_firstTerm B P hB (1 / 2) (by norm_num)
  refine ⟨δ, hδ, ?_⟩
  intro x hx hxδ
  have hratio : 0 < probability B P hB x / firstTerm x := by
    have hh := (abs_lt.mp (hbound x hx hxδ)).1
    linarith
  exact ⟨(div_pos_iff_of_pos_right (firstTerm_positive x)).mp hratio, hratio⟩

end Shao.Probability.BrownianSup
