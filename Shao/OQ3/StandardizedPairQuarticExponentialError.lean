import Shao.OQ3.StandardizedPairNormalizedLogExponent
import Shao.OQ3.UniformPairCharacteristicLocalGaussian
import Shao.OQ3.ComplexExpAddError
import Shao.OQ3.PairDirectionalMomentScaling

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

theorem uniform_standardized_pair_quartic_exponential_error
    {ι : Type*} (law : ι → Measure (Fin 2 → ℝ))
    (hprob : ∀ i, IsProbabilityMeasure (law i))
    (hL2 : ∀ i, ∀ j : Fin 2, MemLp (fun y : Fin 2 → ℝ => y j) 2 (law i))
    (hmean : ∀ i, ∀ j : Fin 2, (∫ y : Fin 2 → ℝ, y j ∂law i) = 0)
    (hcov : ∀ i, ∀ j k : Fin 2, ProbabilityTheory.covariance
      (fun y : Fin 2 → ℝ => y j) (fun y : Fin 2 → ℝ => y k) (law i) =
        if j = k then 1 else 0)
    (M3 M4 M5 : ℝ)
    (hI3 : ∀ i, Integrable
      (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3) (law i))
    (hM3 : ∀ i, (∫ y : Fin 2 → ℝ,
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3 ∂law i) ≤ M3)
    (hI4 : ∀ i, Integrable
      (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 4) (law i))
    (hM4 : ∀ i, (∫ y : Fin 2 → ℝ,
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 4 ∂law i) ≤ M4)
    (hI5 : ∀ i, Integrable
      (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 5) (law i))
    (hM5 : ∀ i, (∫ y : Fin 2 → ℝ,
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 5 ∂law i) ≤ M5) :
    let Phi : ι → ℝ → ℝ → ℂ := fun i u v =>
      ∫ y : Fin 2 → ℝ,
        Complex.exp (((u * y 0 + v * y 1 : ℝ) : ℂ) * Complex.I) ∂law i
    let Qn : ι → ℕ → ℝ → ℝ → ℂ := fun i n u v =>
      -((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2 -
        Complex.I * ((∫ y : Fin 2 → ℝ,
          (u * y 0 + v * y 1) ^ 3 ∂law i : ℝ) : ℂ) /
          (6 * (Real.sqrt (n : ℝ) : ℂ)) +
        (((∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ 4 ∂law i : ℝ) -
          3 * (u ^ 2 + v ^ 2) ^ 2 : ℝ) : ℂ) / (24 * (n : ℂ))
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ i, ∀ u v : ℝ,
        Real.sqrt (u ^ 2 + v ^ 2) ≤ delta * Real.sqrt (n : ℝ) →
        ‖Phi i (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ^ n‖ ≤
            Real.exp (-(u ^ 2 + v ^ 2) / 4) ∧
          ‖Phi i (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ^ n -
              Complex.exp (Qn i n u v)‖ ≤
            C * Real.sqrt (u ^ 2 + v ^ 2) ^ 5 /
              ((n : ℝ) * Real.sqrt (n : ℝ)) * Real.exp (-(u ^ 2 + v ^ 2) / 8) := by
  intro Phi Qn
  obtain ⟨C, dV, hC, hdV, hdV1, hV⟩ :=
    uniform_standardized_pair_normalized_log_exponent law hprob hL2 hmean hcov
      M3 M4 M5 hI3 hM3 hI4 hM4 hI5 hM5
  have hthird : ∃ K : ℝ, 0 < K ∧ ∀ i ∈ (Set.univ : Set ι),
      Integrable (fun y : Fin 2 → ℝ =>
        Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3) (law i) ∧
      (∫ y : Fin 2 → ℝ, Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3 ∂law i) ≤ K := by
    refine ⟨1 + |M3|, by positivity, ?_⟩
    intro i hi
    exact ⟨hI3 i, (hM3 i).trans (by linarith [le_abs_self M3])⟩
  obtain ⟨dG, hdG, hdG1, hG⟩ :=
    uniform_isotropic_pair_characteristic_local_gaussian_bound
      (Set.univ : Set ι) law (fun i _ => hprob i) (fun i _ j => hL2 i j)
      (fun i _ j => hmean i j) (fun i _ j k => hcov i j k) hthird
  let delta : ℝ := min dV (min dG (1 / (8 * (C + 1))))
  have hden : 0 < 8 * (C + 1) := by positivity
  have hdsmall : 0 < 1 / (8 * (C + 1)) := by positivity
  have hdelta : 0 < delta := lt_min hdV (lt_min hdG hdsmall)
  have hdeltaV : delta ≤ dV := min_le_left _ _
  have hdeltaG : delta ≤ dG :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hdeltaS : delta ≤ 1 / (8 * (C + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hdelta1 : delta ≤ 1 := hdeltaV.trans hdV1
  have hCdelta : C * delta ≤ 1 / 8 := by
    have hmul : delta * (8 * (C + 1)) ≤ 1 := (le_div_iff₀ hden).mp hdeltaS
    nlinarith [hdelta.le]
  refine ⟨C, delta, hC, hdelta, hdelta1, ?_⟩
  intro n hn i u v hrad
  let s : ℝ := Real.sqrt (n : ℝ)
  let r : ℝ := Real.sqrt (u ^ 2 + v ^ 2)
  let t : ℝ := r / s
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hn)
  have hs : 0 < s := Real.sqrt_pos.mpr hnpos
  have hsne : s ≠ 0 := ne_of_gt hs
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = u ^ 2 + v ^ 2 := Real.sq_sqrt (by positivity)
  have ht : 0 ≤ t := div_nonneg hr hs.le
  have htdelta : t ≤ delta := (div_le_iff₀ hs).mpr hrad
  have ht1 : t ≤ 1 := htdelta.trans hdelta1
  have hscale : Real.sqrt ((u / s) ^ 2 + (v / s) ^ 2) = r / s := by
    simpa [div_eq_mul_inv, abs_of_pos (inv_pos.mpr hs), mul_comm, r] using
      euclidean_frequency_radius_scalar_mul s⁻¹ u v
  have hradV : Real.sqrt (u ^ 2 + v ^ 2) ≤ dV * Real.sqrt (n : ℝ) :=
    hrad.trans (mul_le_mul_of_nonneg_right hdeltaV hs.le)
  rcases hV n hn i u v hradV with ⟨hne, hlog, hexp⟩
  have hradG : Real.sqrt ((u / s) ^ 2 + (v / s) ^ 2) ≤ dG := by
    rw [hscale]
    exact htdelta.trans hdeltaG
  have hGauss : ‖Phi i (u / s) (v / s)‖ ≤
      Real.exp (-((u / s) ^ 2 + (v / s) ^ 2) / 4) :=
    hG i (Set.mem_univ _) (u / s) (v / s) hradG
  have hfreq : (u / s) ^ 2 + (v / s) ^ 2 = (u ^ 2 + v ^ 2) / s ^ 2 := by
    field_simp [hsne] <;> ring
  have hexponent : (n : ℝ) * (-((u / s) ^ 2 + (v / s) ^ 2) / 4) =
      -(u ^ 2 + v ^ 2) / 4 := by
    rw [hfreq, ← hs2]
    field_simp [hsne] <;> ring
  have hpow : ‖Phi i (u / s) (v / s) ^ n‖ ≤ Real.exp (-(u ^ 2 + v ^ 2) / 4) := by
    calc
      ‖Phi i (u / s) (v / s) ^ n‖ = ‖Phi i (u / s) (v / s)‖ ^ n :=
        Complex.norm_pow _ _
      _ ≤ (Real.exp (-((u / s) ^ 2 + (v / s) ^ 2) / 4)) ^ n :=
        pow_le_pow_left₀ (norm_nonneg _) hGauss n
      _ = Real.exp ((n : ℝ) * (-((u / s) ^ 2 + (v / s) ^ 2) / 4)) :=
        (Real.exp_nat_mul _ n).symm
      _ = Real.exp (-(u ^ 2 + v ^ 2) / 4) := congrArg Real.exp hexponent
  let Z : ℂ := (n : ℂ) * Complex.log (Phi i (u / s) (v / s))
  let e : ℂ := Qn i n u v - Z
  have hexpZ : Complex.exp Z = Phi i (u / s) (v / s) ^ n := hexp
  have hre : Z.re ≤ -(u ^ 2 + v ^ 2) / 4 := by
    apply Real.exp_le_exp.mp
    rw [← Complex.norm_exp, hexpZ]
    exact hpow
  have hEnorm : ‖e‖ ≤ C * r ^ 5 / ((n : ℝ) * s) := by
    dsimp only [e, Z]
    rw [norm_sub_rev]
    exact hlog
  have ht2 : t ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg ht (sub_nonneg.mpr ht1)]
  have ht3 : t ^ 3 ≤ t := by
    nlinarith [mul_nonneg ht (sub_nonneg.mpr ht2)]
  have herror_id : C * r ^ 5 / ((n : ℝ) * s) = C * r ^ 2 * t ^ 3 := by
    dsimp only [t]
    rw [← hs2]
    field_simp [hsne] <;> ring
  have hsmall : ‖e‖ ≤ (u ^ 2 + v ^ 2) / 8 := by
    calc
      ‖e‖ ≤ C * r ^ 5 / ((n : ℝ) * s) := hEnorm
      _ = C * r ^ 2 * t ^ 3 := herror_id
      _ ≤ C * r ^ 2 * delta :=
        mul_le_mul_of_nonneg_left (ht3.trans htdelta) (by positivity)
      _ ≤ r ^ 2 / 8 := by
        nlinarith [mul_le_mul_of_nonneg_right hCdelta (sq_nonneg r)]
      _ = (u ^ 2 + v ^ 2) / 8 := by rw [hr2]
  have hgap : (u ^ 2 + v ^ 2) / 8 ≤ ((u ^ 2 + v ^ 2) / 4) / 2 :=
    le_of_eq (by ring)
  have hpert := norm_complex_exp_add_error_of_re_le Z e
    ((u ^ 2 + v ^ 2) / 4) ((u ^ 2 + v ^ 2) / 8)
    (by simpa only [neg_div] using hre) hsmall hgap
  have hadd : Z + e = Qn i n u v := by dsimp only [e]; ring
  have hdenexp : -((u ^ 2 + v ^ 2) / 4) / 2 = -(u ^ 2 + v ^ 2) / 8 := by ring
  rw [hadd, hexpZ, hdenexp] at hpert
  refine ⟨hpow, ?_⟩
  calc
    ‖Phi i (u / s) (v / s) ^ n - Complex.exp (Qn i n u v)‖ =
        ‖Complex.exp (Qn i n u v) - Phi i (u / s) (v / s) ^ n‖ := norm_sub_rev _ _
    _ ≤ ‖e‖ * Real.exp (-(u ^ 2 + v ^ 2) / 8) := hpert
    _ ≤ C * r ^ 5 / ((n : ℝ) * s) * Real.exp (-(u ^ 2 + v ^ 2) / 8) :=
      mul_le_mul_of_nonneg_right hEnorm (Real.exp_pos _).le

end
end Shao.OQ3
