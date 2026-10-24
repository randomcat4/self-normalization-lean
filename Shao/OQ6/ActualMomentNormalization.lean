import Shao.OQ6.QuantizedObservationCoding
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace Shao.OQ6.ActualMomentNormalization

noncomputable section

open MeasureTheory
open scoped BigOperators

noncomputable def actualCoordinateMean
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) {n : ℕ} (Y : Fin n → Ω → ℝ) (i : Fin n) : ℝ :=
  ∫ ω, Y i ω ∂ν

noncomputable def actualCenteredFamily
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) {n : ℕ} (Y : Fin n → Ω → ℝ)
    (i : Fin n) (ω : Ω) : ℝ :=
  Y i ω - actualCoordinateMean ν Y i

noncomputable def actualNormalizationScale
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) {n : ℕ} (Y : Fin n → Ω → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, ∫ ω, (actualCenteredFamily ν Y i ω) ^ 2 ∂ν)

noncomputable def actualNormalizedFamily
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) {n : ℕ} (Y : Fin n → Ω → ℝ)
    (i : Fin n) (ω : Ω) : ℝ :=
  Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation
    (actualCoordinateMean ν Y i) (actualNormalizationScale ν Y) (Y i) ω

theorem actual_centering_and_scale_spec
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (ξ Y : Fin n → Ω → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (hξ2 : ∀ i : Fin n, MemLp (ξ i) 2 ν)
    (hξmean : ∀ i : Fin n, (∫ ω, ξ i ω ∂ν) = 0)
    (hξenergy : (∑ i : Fin n, ∫ ω, (ξ i ω) ^ 2 ∂ν) = 1)
    (hY : ∀ i : Fin n, Measurable (Y i))
    (ε : ℝ) (hε : 0 ≤ ε)
    (herr : ∀ (i : Fin n) (ω : Ω), |Y i ω - ξ i ω| ≤ ε) :
    let μ : Fin n → ℝ := actualCoordinateMean ν Y
    let Z : Fin n → Ω → ℝ := actualCenteredFamily ν Y
    let s : ℝ := actualNormalizationScale ν Y
    (∀ i : Fin n, MemLp (Y i) 2 ν) ∧
    (∀ i : Fin n, Integrable (Y i) ν) ∧
    (∀ i : Fin n, Integrable (fun ω => (Y i ω) ^ 2) ν) ∧
    (∀ i : Fin n, Measurable (Z i)) ∧
    (∀ i : Fin n, MemLp (Z i) 2 ν) ∧
    (∀ i : Fin n, Integrable (Z i) ν) ∧
    (∀ i : Fin n, Integrable (fun ω => (Z i ω) ^ 2) ν) ∧
    (∀ i : Fin n, |μ i| ≤ ε) ∧
    (∀ (i : Fin n) (ω : Ω), |Z i ω - ξ i ω| ≤ 2 * ε) ∧
    (∀ i : Fin n, (∫ ω, Z i ω ∂ν) = 0) ∧
    s ^ 2 = (∑ i : Fin n, ∫ ω, (Z i ω) ^ 2 ∂ν) ∧
    |s - 1| ≤ 2 * ε * Real.sqrt (n : ℝ) := by
  classical
  dsimp only
  let μ : Fin n → ℝ := actualCoordinateMean ν Y
  let Z : Fin n → Ω → ℝ := actualCenteredFamily ν Y
  let s : ℝ := actualNormalizationScale ν Y
  have he2 (i : Fin n) : MemLp (fun ω => Y i ω - ξ i ω) 2 ν :=
    MemLp.of_bound ((hY i).sub (hξ i)).aestronglyMeasurable ε
      (Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs] using herr i ω)
  have hY2 (i : Fin n) : MemLp (Y i) 2 ν := by
    have heq : (fun ω => Y i ω - ξ i ω) + ξ i = Y i := by
      funext ω
      simp
    rw [← heq]
    exact (he2 i).add (hξ2 i)
  have hYI (i : Fin n) : Integrable (Y i) ν := (hY2 i).integrable (by norm_num)
  have hYsq (i : Fin n) : Integrable (fun ω => (Y i ω) ^ 2) ν :=
    (hY2 i).integrable_sq
  have hZm (i : Fin n) : Measurable (Z i) := by
    change Measurable (fun ω => Y i ω - μ i)
    exact (hY i).sub measurable_const
  have hZ2 (i : Fin n) : MemLp (Z i) 2 ν := by
    change MemLp (Y i - fun _ : Ω => μ i) 2 ν
    exact (hY2 i).sub (memLp_const (μ i))
  have hZI (i : Fin n) : Integrable (Z i) ν := (hZ2 i).integrable (by norm_num)
  have hZsq (i : Fin n) : Integrable (fun ω => (Z i ω) ^ 2) ν :=
    (hZ2 i).integrable_sq
  have hμ (i : Fin n) : |μ i| ≤ ε := by
    have heq : (∫ ω, Y i ω ∂ν) = ∫ ω, Y i ω - ξ i ω ∂ν := by
      rw [integral_sub (hYI i) ((hξ2 i).integrable (by norm_num)),
        hξmean i, sub_zero]
    change |∫ ω, Y i ω ∂ν| ≤ ε
    rw [heq]
    calc
      |∫ ω, Y i ω - ξ i ω ∂ν| ≤ ∫ ω, |Y i ω - ξ i ω| ∂ν := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := ν) (fun ω => Y i ω - ξ i ω)
      _ ≤ ∫ _ : Ω, ε ∂ν :=
        integral_mono ((he2 i).integrable (by norm_num)).abs
          (integrable_const ε) (herr i)
      _ = ε := by simp
  have hZerr (i : Fin n) (ω : Ω) : |Z i ω - ξ i ω| ≤ 2 * ε := by
    calc
      |Z i ω - ξ i ω| = |(Y i ω - ξ i ω) - μ i| := by
        congr 1
        change (Y i ω - μ i) - ξ i ω = _
        ring
      _ ≤ |Y i ω - ξ i ω| + |μ i| := abs_sub _ _
      _ ≤ 2 * ε := by linarith [herr i ω, hμ i]
  have hZmean (i : Fin n) : (∫ ω, Z i ω ∂ν) = 0 := by
    change (∫ ω, Y i ω - μ i ∂ν) = 0
    rw [integral_sub (hYI i) (integrable_const (μ i))]
    simp only [integral_const, probReal_univ, one_smul]
    change μ i - μ i = 0
    ring
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ 2 = ∑ i : Fin n, ∫ ω, (Z i ω) ^ 2 ∂ν := by
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
      integral_nonneg fun ω => sq_nonneg (Z i ω))
  let A : ℝ := ∑ i : Fin n, ∫ ω, (Z i ω) ^ 2 ∂ν
  let C : ℝ := ∑ i : Fin n, ∫ ω, Z i ω * ξ i ω ∂ν
  have hZX (i : Fin n) : Integrable (fun ω => Z i ω * ξ i ω) ν := by
    simpa only [Pi.mul_def] using (hZ2 i).integrable_mul (hξ2 i)
  have hquad (t : ℝ) :
      (∑ i : Fin n, ∫ ω, (Z i ω - t * ξ i ω) ^ 2 ∂ν) =
        A - 2 * t * C + t ^ 2 := by
    have hi (i : Fin n) :
        (∫ ω, (Z i ω - t * ξ i ω) ^ 2 ∂ν) =
          (∫ ω, (Z i ω) ^ 2 ∂ν) -
            (2 * t) * (∫ ω, Z i ω * ξ i ω ∂ν) +
            t ^ 2 * (∫ ω, (ξ i ω) ^ 2 ∂ν) := by
      have heq : (fun ω => (Z i ω - t * ξ i ω) ^ 2) =
          (fun ω => (Z i ω) ^ 2 - (2 * t) * (Z i ω * ξ i ω) +
            t ^ 2 * (ξ i ω) ^ 2) := by
        funext ω
        ring
      have hsub : Integrable
          (fun ω => (Z i ω) ^ 2 - (2 * t) * (Z i ω * ξ i ω)) ν := by
        simpa only [Pi.sub_def] using (hZsq i).sub ((hZX i).const_mul (2 * t))
      rw [heq,
        integral_add
          (f := fun ω => (Z i ω) ^ 2 - (2 * t) * (Z i ω * ξ i ω))
          (g := fun ω => t ^ 2 * (ξ i ω) ^ 2) hsub
          ((hξ2 i).integrable_sq.const_mul (t ^ 2)),
        integral_sub (f := fun ω => (Z i ω) ^ 2)
          (g := fun ω => (2 * t) * (Z i ω * ξ i ω))
          (hZsq i) ((hZX i).const_mul (2 * t)),
        integral_const_mul, integral_const_mul]
    calc
      _ = ∑ i : Fin n,
          ((∫ ω, (Z i ω) ^ 2 ∂ν) -
            (2 * t) * (∫ ω, Z i ω * ξ i ω ∂ν) +
            t ^ 2 * (∫ ω, (ξ i ω) ^ 2 ∂ν)) :=
        Finset.sum_congr rfl fun i _ => hi i
      _ = A - 2 * t * C + t ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, hξenergy]
        dsimp only [A, C]
        ring
  have hC2 : C ^ 2 ≤ A := by
    have hp : 0 ≤ ∑ i : Fin n, ∫ ω, (Z i ω - C * ξ i ω) ^ 2 ∂ν :=
      Finset.sum_nonneg fun i _ => integral_nonneg fun ω => sq_nonneg _
    rw [hquad C] at hp
    nlinarith
  have hCs : C ≤ s := by
    by_contra hc
    have hlt : s < C := lt_of_not_ge hc
    have hp : 0 < (C - s) * (C + s) :=
      mul_pos (sub_pos.mpr hlt) (by linarith)
    change s ^ 2 = A at hsq
    nlinarith
  have hD : (∑ i : Fin n, ∫ ω, (Z i ω - ξ i ω) ^ 2 ∂ν) ≤
      4 * ε ^ 2 * (n : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin n, ∫ _ω : Ω, (2 * ε) ^ 2 ∂ν := by
        apply Finset.sum_le_sum
        intro i _
        have hd2 : MemLp (fun ω => Z i ω - ξ i ω) 2 ν := by
          simpa only [Pi.sub_def] using (hZ2 i).sub (hξ2 i)
        apply integral_mono (f := fun ω => (Z i ω - ξ i ω) ^ 2)
          (g := fun _ω : Ω => (2 * ε) ^ 2) hd2.integrable_sq
          (integrable_const ((2 * ε) ^ 2))
        intro ω
        simpa only [sq_abs] using
          pow_le_pow_left₀ (abs_nonneg (Z i ω - ξ i ω)) (hZerr i ω) 2
      _ = (n : ℝ) * (2 * ε) ^ 2 := by simp
      _ = 4 * ε ^ 2 * (n : ℝ) := by ring
  have hDformula : (∑ i : Fin n, ∫ ω, (Z i ω - ξ i ω) ^ 2 ∂ν) =
      A - 2 * C + 1 := by
    simpa only [one_mul, one_pow, mul_one] using hquad 1
  have hdistSq : (s - 1) ^ 2 ≤ 4 * ε ^ 2 * (n : ℝ) := by
    rw [hDformula] at hD
    change s ^ 2 = A at hsq
    nlinarith
  let δ : ℝ := 2 * ε * Real.sqrt (n : ℝ)
  have hδ0 : 0 ≤ δ := by dsimp only [δ]; positivity
  have hδsq : δ ^ 2 = 4 * ε ^ 2 * (n : ℝ) := by
    dsimp only [δ]
    rw [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)]
    ring
  have hscale : |s - 1| ≤ δ := by
    by_contra hh
    have hlt : δ < |s - 1| := lt_of_not_ge hh
    have hp : 0 < (|s - 1| - δ) * (|s - 1| + δ) :=
      mul_pos (sub_pos.mpr hlt) (by linarith [abs_nonneg (s - 1)])
    nlinarith [sq_abs (s - 1)]
  exact ⟨hY2, hYI, hYsq, hZm, hZ2, hZI, hZsq, hμ, hZerr, hZmean, hsq, hscale⟩

theorem actual_moment_normalization_spec
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (ξ Y : Fin n → Ω → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (hξ2 : ∀ i : Fin n, MemLp (ξ i) 2 ν)
    (hξmean : ∀ i : Fin n, (∫ ω, ξ i ω ∂ν) = 0)
    (hξenergy : (∑ i : Fin n, ∫ ω, (ξ i ω) ^ 2 ∂ν) = 1)
    (hY : ∀ i : Fin n, Measurable (Y i))
    (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε < 1 / (4 * Real.sqrt (n : ℝ)))
    (herr : ∀ (i : Fin n) (ω : Ω), |Y i ω - ξ i ω| ≤ ε) :
    let μ : Fin n → ℝ := actualCoordinateMean ν Y
    let Z : Fin n → Ω → ℝ := actualCenteredFamily ν Y
    let s : ℝ := actualNormalizationScale ν Y
    let η : Fin n → Ω → ℝ := actualNormalizedFamily ν Y
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
    let Vη : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (η i ω) ^ 2)
    let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
    let Wη : Ω → ℝ := fun ω => ∑ i : Fin n, η i ω
    let ρ : ℝ := 4 * ε * Real.sqrt (n : ℝ)
    (1 / 2 : ℝ) < s ∧
    (∀ i : Fin n, Measurable (η i)) ∧
    (∀ i : Fin n, MemLp (η i) 2 ν) ∧
    (∀ i : Fin n, Integrable (η i) ν) ∧
    (∀ i : Fin n, Integrable (fun ω => (η i ω) ^ 2) ν) ∧
    (∀ i : Fin n, (∫ ω, η i ω ∂ν) = 0) ∧
    (∑ i : Fin n, ∫ ω, (η i ω) ^ 2 ∂ν) = 1 ∧
    (∀ (i : Fin n) (ω : Ω), s * η i ω + μ i = Y i ω) ∧
    (∀ ω : Ω,
      Real.sqrt (∑ i : Fin n, (η i ω - ξ i ω) ^ 2) ≤ ρ * (1 + V ω)) ∧
    (∀ ω : Ω, |Vη ω - V ω| ≤ ρ * (1 + V ω)) ∧
    (∀ ω : Ω, |Wη ω - W ω| ≤ Real.sqrt (n : ℝ) * ρ * (1 + V ω)) ∧
    (∀ (i : Fin n) (ω : Ω), |η i ω| ≤ 2 * |ξ i ω| + 4 * ε) ∧
    (∀ (i : Fin n) (ω : Ω), |η i ω - ξ i ω| ≤ 4 * ε + ρ * |ξ i ω|) := by
  classical
  dsimp only
  let μ : Fin n → ℝ := actualCoordinateMean ν Y
  let Z : Fin n → Ω → ℝ := actualCenteredFamily ν Y
  let s : ℝ := actualNormalizationScale ν Y
  let η : Fin n → Ω → ℝ := actualNormalizedFamily ν Y
  let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
  let Vη : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (η i ω) ^ 2)
  let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
  let Wη : Ω → ℝ := fun ω => ∑ i : Fin n, η i ω
  let ρ : ℝ := 4 * ε * Real.sqrt (n : ℝ)
  rcases actual_centering_and_scale_spec ν n hn ξ Y hξ hξ2 hξmean hξenergy
      hY ε hε.le herr with
    ⟨hY2, hYI, hYsq, hZm, hZ2, hZI, hZsq, hμ, hZerr, hZmean, hsq, hscale⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hrootpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hεprod : ε * (4 * Real.sqrt (n : ℝ)) < 1 :=
    (lt_div_iff₀ (by positivity : 0 < 4 * Real.sqrt (n : ℝ))).mp hεsmall
  have hs : (1 / 2 : ℝ) < s := by
    have hh := (abs_le.mp hscale).1
    change -(2 * ε * Real.sqrt (n : ℝ)) ≤ s - 1 at hh
    nlinarith
  have hspos : 0 < s := by linarith
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hsinvpos : 0 < (1 : ℝ) / s := one_div_pos.mpr hspos
  have hsinv0 : 0 ≤ (1 : ℝ) / s := hsinvpos.le
  have hsinv : (1 : ℝ) / s ≤ 2 := (div_le_iff₀ hspos).2 (by linarith)
  have hη (i : Fin n) (ω : Ω) : η i ω = Z i ω / s := rfl
  have hηm (i : Fin n) : Measurable (η i) := by
    change Measurable (fun ω => Z i ω / s)
    exact (hZm i).div_const s
  have hηsq (i : Fin n) : Integrable (fun ω => (η i ω) ^ 2) ν := by
    change Integrable (fun ω => (Z i ω / s) ^ 2) ν
    simpa only [div_pow] using (hZsq i).div_const (s ^ 2)
  have hη2 (i : Fin n) : MemLp (η i) 2 ν :=
    (memLp_two_iff_integrable_sq (hηm i).aestronglyMeasurable).2 (hηsq i)
  have hηI (i : Fin n) : Integrable (η i) ν := (hη2 i).integrable (by norm_num)
  have hηmean (i : Fin n) : (∫ ω, η i ω ∂ν) = 0 := by
    simp_rw [hη, div_eq_mul_inv, integral_mul_const]
    rw [hZmean i]
    simp
  have hηenergy : (∑ i : Fin n, ∫ ω, (η i ω) ^ 2 ∂ν) = 1 := by
    calc
      _ = ∑ i : Fin n, (∫ ω, (Z i ω) ^ 2 ∂ν) / s ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        simp_rw [hη, div_pow, div_eq_mul_inv, integral_mul_const]
      _ = (∑ i : Fin n, ∫ ω, (Z i ω) ^ 2 ∂ν) * (s ^ 2)⁻¹ := by
        simp_rw [div_eq_mul_inv]
        rw [Finset.sum_mul]
      _ = 1 := by
        rw [← hsq]
        exact mul_inv_cancel₀ (pow_ne_zero 2 hsne)
  have hrec (i : Fin n) (ω : Ω) : s * η i ω + μ i = Y i ω := by
    rw [hη]
    change s * ((Y i ω - μ i) / s) + μ i = Y i ω
    field_simp [hsne] <;> ring
  have hle_of_sq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (hab : a ^ 2 ≤ b ^ 2) : a ≤ b := by
    by_contra hh
    have hlt : b < a := lt_of_not_ge hh
    have hp : 0 < (a - b) * (a + b) :=
      mul_pos (sub_pos.mpr hlt) (by linarith)
    nlinarith
  have hnorm0 (u : Fin n → ℝ) : 0 ≤ ∑ i : Fin n, (u i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (u i)
  have hnormSq (u : Fin n → ℝ) :
      (Real.sqrt (∑ i : Fin n, (u i) ^ 2)) ^ 2 = ∑ i : Fin n, (u i) ^ 2 :=
    Real.sq_sqrt (hnorm0 u)
  have htri (u v : Fin n → ℝ) :
      Real.sqrt (∑ i : Fin n, (u i + v i) ^ 2) ≤
        Real.sqrt (∑ i : Fin n, (u i) ^ 2) +
          Real.sqrt (∑ i : Fin n, (v i) ^ 2) := by
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ u v
    have hexp : (∑ i : Fin n, (u i + v i) ^ 2) =
        (∑ i : Fin n, (u i) ^ 2) + 2 * (∑ i : Fin n, u i * v i) +
          (∑ i : Fin n, (v i) ^ 2) := by
      calc
        _ = ∑ i : Fin n, ((u i) ^ 2 + 2 * (u i * v i) + (v i) ^ 2) :=
          Finset.sum_congr rfl fun i _ => by ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    apply hle_of_sq _ _ (Real.sqrt_nonneg _)
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    rw [hnormSq (fun i => u i + v i)]
    nlinarith [hnormSq u, hnormSq v]
  have hsmul (a : ℝ) (u : Fin n → ℝ) :
      Real.sqrt (∑ i : Fin n, (a * u i) ^ 2) =
        |a| * Real.sqrt (∑ i : Fin n, (u i) ^ 2) := by
    have heq : (∑ i : Fin n, (a * u i) ^ 2) = a ^ 2 * (∑ i : Fin n, (u i) ^ 2) := by
      simp_rw [mul_pow]
      rw [Finset.mul_sum]
    rw [heq, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]
  have hsum (u : Fin n → ℝ) :
      |∑ i : Fin n, u i| ≤
        Real.sqrt (n : ℝ) * Real.sqrt (∑ i : Fin n, (u i) ^ 2) := by
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun i : Fin n => |u i|) (fun _ : Fin n => (1 : ℝ))
    have hh : (∑ i : Fin n, |u i|) ≤
        Real.sqrt (∑ i : Fin n, (u i) ^ 2) * Real.sqrt (n : ℝ) := by
      simpa [sq_abs] using hcs
    calc
      _ ≤ ∑ i : Fin n, |u i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ Real.sqrt (∑ i : Fin n, (u i) ^ 2) * Real.sqrt (n : ℝ) := hh
      _ = _ := mul_comm _ _
  let δ : ℝ := 2 * ε * Real.sqrt (n : ℝ)
  have hδ0 : 0 ≤ δ := by dsimp only [δ]; positivity
  have hδsq : δ ^ 2 = (n : ℝ) * (2 * ε) ^ 2 := by
    dsimp only [δ]
    rw [mul_pow, Real.sq_sqrt hnpos.le]
    ring
  have hsc : |1 - s| ≤ δ := by
    simpa only [abs_sub_comm] using hscale
  have hd (ω : Ω) :
      Real.sqrt (∑ i : Fin n, (Z i ω - ξ i ω) ^ 2) ≤ δ := by
    have hb : (∑ i : Fin n, (Z i ω - ξ i ω) ^ 2) ≤ (n : ℝ) * (2 * ε) ^ 2 := by
      calc
        _ ≤ ∑ _i : Fin n, (2 * ε) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          simpa only [sq_abs] using
            pow_le_pow_left₀ (abs_nonneg (Z i ω - ξ i ω)) (hZerr i ω) 2
        _ = _ := by simp
    apply hle_of_sq _ _ (Real.sqrt_nonneg _) hδ0
    rw [hnormSq, hδsq]
    exact hb
  have hvec (ω : Ω) :
      Real.sqrt (∑ i : Fin n, (η i ω - ξ i ω) ^ 2) ≤ ρ * (1 + V ω) := by
    have hpoint (i : Fin n) : η i ω - ξ i ω =
        (1 / s) * ((Z i ω - ξ i ω) + (1 - s) * ξ i ω) := by
      rw [hη]
      field_simp [hsne] <;> ring
    calc
      _ = Real.sqrt (∑ i : Fin n,
          ((1 / s) * ((Z i ω - ξ i ω) + (1 - s) * ξ i ω)) ^ 2) := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => congrArg (fun a : ℝ => a ^ 2) (hpoint i)
      _ = |1 / s| * Real.sqrt (∑ i : Fin n,
          ((Z i ω - ξ i ω) + (1 - s) * ξ i ω) ^ 2) :=
        hsmul (1 / s) (fun i => (Z i ω - ξ i ω) + (1 - s) * ξ i ω)
      _ = (1 / s) * Real.sqrt (∑ i : Fin n,
          ((Z i ω - ξ i ω) + (1 - s) * ξ i ω) ^ 2) := by
        rw [abs_of_pos hsinvpos]
      _ ≤ (1 / s) *
          (Real.sqrt (∑ i : Fin n, (Z i ω - ξ i ω) ^ 2) +
            Real.sqrt (∑ i : Fin n, ((1 - s) * ξ i ω) ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (htri (fun i => Z i ω - ξ i ω) (fun i => (1 - s) * ξ i ω)) hsinv0
      _ = (1 / s) *
          (Real.sqrt (∑ i : Fin n, (Z i ω - ξ i ω) ^ 2) + |1 - s| * V ω) := by
        rw [hsmul]
      _ ≤ (1 / s) * (δ + δ * V ω) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (hd ω)
            (mul_le_mul_of_nonneg_right hsc (Real.sqrt_nonneg _))) hsinv0
      _ ≤ 2 * (δ + δ * V ω) :=
        mul_le_mul_of_nonneg_right hsinv (by positivity)
      _ = ρ * (1 + V ω) := by dsimp only [δ, ρ]; ring
  have hV (ω : Ω) : |Vη ω - V ω| ≤ ρ * (1 + V ω) := by
    let E : ℝ := Real.sqrt (∑ i : Fin n, (η i ω - ξ i ω) ^ 2)
    have hforward : Vη ω ≤ E + V ω := by
      have hh := htri (fun i => η i ω - ξ i ω) (fun i => ξ i ω)
      simpa only [sub_add_cancel] using hh
    have heq : (∑ i : Fin n, (ξ i ω - η i ω) ^ 2) =
        ∑ i : Fin n, (η i ω - ξ i ω) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by ring
    have hbackward : V ω ≤ E + Vη ω := by
      calc
        V ω = Real.sqrt (∑ i : Fin n, ((ξ i ω - η i ω) + η i ω) ^ 2) := by
          change Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2) = _
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ ≤ Real.sqrt (∑ i : Fin n, (ξ i ω - η i ω) ^ 2) + Vη ω :=
          htri (fun i => ξ i ω - η i ω) (fun i => η i ω)
        _ = E + Vη ω := by rw [heq]
    have hh : |Vη ω - V ω| ≤ E := abs_le.mpr ⟨by linarith, by linarith⟩
    exact hh.trans (hvec ω)
  have hW (ω : Ω) :
      |Wη ω - W ω| ≤ Real.sqrt (n : ℝ) * ρ * (1 + V ω) := by
    calc
      _ = |∑ i : Fin n, (η i ω - ξ i ω)| := by
        congr 1
        change (∑ i : Fin n, η i ω) - (∑ i : Fin n, ξ i ω) = _
        rw [Finset.sum_sub_distrib]
      _ ≤ Real.sqrt (n : ℝ) * Real.sqrt (∑ i : Fin n, (η i ω - ξ i ω) ^ 2) :=
        hsum (fun i => η i ω - ξ i ω)
      _ ≤ Real.sqrt (n : ℝ) * (ρ * (1 + V ω)) :=
        mul_le_mul_of_nonneg_left (hvec ω) (Real.sqrt_nonneg _)
      _ = _ := by ring
  have hcoord (i : Fin n) (ω : Ω) : |η i ω| ≤ 2 * |ξ i ω| + 4 * ε := by
    have hz : |Z i ω| ≤ |ξ i ω| + 2 * ε := by
      calc
        |Z i ω| = |(Z i ω - ξ i ω) + ξ i ω| := by rw [sub_add_cancel]
        _ ≤ |Z i ω - ξ i ω| + |ξ i ω| := abs_add_le _ _
        _ ≤ |ξ i ω| + 2 * ε := by linarith [hZerr i ω]
    calc
      |η i ω| = |Z i ω| * (1 / s) := by
        rw [hη, abs_div, abs_of_pos hspos]
        ring
      _ ≤ (|ξ i ω| + 2 * ε) * 2 :=
        mul_le_mul hz hsinv hsinv0 (by positivity)
      _ = _ := by ring
  have hcoorddiff (i : Fin n) (ω : Ω) :
      |η i ω - ξ i ω| ≤ 4 * ε + ρ * |ξ i ω| := by
    have ha : |Z i ω - ξ i ω| / s ≤ 4 * ε := by
      calc
        _ = |Z i ω - ξ i ω| * (1 / s) := by ring
        _ ≤ (2 * ε) * 2 := mul_le_mul (hZerr i ω) hsinv hsinv0 (by positivity)
        _ = _ := by ring
    have hb : |1 - s| / s ≤ ρ := by
      calc
        _ = |1 - s| * (1 / s) := by ring
        _ ≤ δ * 2 := mul_le_mul hsc hsinv hsinv0 hδ0
        _ = ρ := by dsimp only [δ, ρ]; ring
    have hpoint : η i ω - ξ i ω =
        (Z i ω - ξ i ω) / s + ((1 - s) / s) * ξ i ω := by
      rw [hη]
      field_simp [hsne] <;> ring
    calc
      _ = |(Z i ω - ξ i ω) / s + ((1 - s) / s) * ξ i ω| := congrArg abs hpoint
      _ ≤ |(Z i ω - ξ i ω) / s| + |((1 - s) / s) * ξ i ω| := abs_add_le _ _
      _ = |Z i ω - ξ i ω| / s + (|1 - s| / s) * |ξ i ω| := by
        simp only [abs_div, abs_mul, abs_of_pos hspos]
      _ ≤ 4 * ε + ρ * |ξ i ω| :=
        add_le_add ha (mul_le_mul_of_nonneg_right hb (abs_nonneg _))
  exact ⟨hs, hηm, hη2, hηI, hηsq, hηmean, hηenergy, hrec,
    hvec, hV, hW, hcoord, hcoorddiff⟩

end

end Shao.OQ6.ActualMomentNormalization
