import Shao.OQ3.CenteredLogMGF
import Shao.OQ3.LocalRateMargin

namespace Shao.OQ3

open MeasureTheory

noncomputable section

def normalTrialTilt (mu : Measure ℝ) (y z : ℝ) : ℝ × ℝ :=
  let S := normalVariance mu
  let T := transverseVariance mu
  let b := ProbabilityTheory.covariance normalValue (fun x : ℝ => x) mu / S
  (y / S - b * ((z - b * y) / T), (z - b * y) / T)

def normalTrialCost (mu : Measure ℝ) (q a y z : ℝ) : ℝ :=
  (normalTrialTilt mu y z).1 * y + (normalTrialTilt mu y z).2 * z -
    centeredNormalLogMGF mu q a (normalTrialTilt mu y z).1 (normalTrialTilt mu y z).2

private theorem trial_parameter_bound (S T b y z : ℝ) (hS : 0 < S) (hT : 0 < T) :
    |y / S - b * ((z - b * y) / T)| + |(z - b * y) / T| ≤
      (1 / S + (|b| + 1) ^ 2 / T + 1) * (|y| + |z|) := by
  let u : ℝ := (z - b * y) / T
  let R : ℝ := |y| + |z|
  have hR : 0 ≤ R := add_nonneg (abs_nonneg y) (abs_nonneg z)
  have hyR : |y| ≤ R := by dsimp only [R]; linarith only [abs_nonneg z]
  have hznum : |z - b * y| ≤ (|b| + 1) * R := by
    calc
      |z - b * y| ≤ |z| + |b| * |y| := by
        simpa only [sub_eq_add_neg, abs_neg, abs_mul] using abs_add_le z (-(b * y))
      _ ≤ (|b| + 1) * R := by
        dsimp only [R]
        nlinarith only [abs_nonneg y, mul_nonneg (abs_nonneg b) (abs_nonneg z)]
  have hu : |u| ≤ ((|b| + 1) / T) * R := by
    dsimp only [u]
    rw [abs_div, abs_of_pos hT]
    calc
      |z - b * y| / T ≤ ((|b| + 1) * R) / T :=
        div_le_div_of_nonneg_right hznum hT.le
      _ = ((|b| + 1) / T) * R := by ring
  have hv : |y / S - b * u| ≤ |y| / S + |b| * |u| := by
    simpa only [sub_eq_add_neg, abs_neg, abs_mul, abs_div, abs_of_pos hS] using
      abs_add_le (y / S) (-(b * u))
  calc
    |y / S - b * u| + |u| ≤ (|y| / S + |b| * |u|) + |u| :=
      add_le_add hv (le_refl _)
    _ = |y| / S + (|b| + 1) * |u| := by ring
    _ ≤ R / S + (|b| + 1) * (((|b| + 1) / T) * R) :=
      add_le_add (div_le_div_of_nonneg_right hyR hS.le)
        (mul_le_mul_of_nonneg_left hu (by positivity))
    _ = (1 / S + (|b| + 1) ^ 2 / T) * R := by ring
    _ ≤ (1 / S + (|b| + 1) ^ 2 / T + 1) * R := by nlinarith only [hR]

private theorem trial_quadratic_duality (S T b y z : ℝ) (hS : 0 < S) (hT : 0 < T) :
    (y / S - b * ((z - b * y) / T)) * y + ((z - b * y) / T) * z -
      (S * ((y / S - b * ((z - b * y) / T)) + b * ((z - b * y) / T)) ^ 2 +
        T * ((z - b * y) / T) ^ 2) / 2 = gaussianRateProfile S T b y z := by
  unfold gaussianRateProfile
  field_simp [hS.ne', hT.ne']
  ring

theorem exists_normalTrialCost_cubic_lower (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a : ℝ)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a)
    (hS : 0 < normalVariance mu) (hD : 0 < (parabolaCovariance mu).det) :
    ∃ D radius : ℝ, 0 < D ∧ 0 < radius ∧ ∀ y z : ℝ, |y| + |z| ≤ radius →
      Integrable (fun x : ℝ => Real.exp (centeredNormalProjection q a
        (normalTrialTilt mu y z).1 (normalTrialTilt mu y z).2 x)) mu ∧
        0 < (∫ x : ℝ, Real.exp (centeredNormalProjection q a
          (normalTrialTilt mu y z).1 (normalTrialTilt mu y z).2 x) ∂mu) ∧
        gaussianRateProfile (normalVariance mu) (transverseVariance mu)
          (ProbabilityTheory.covariance normalValue (fun x : ℝ => x) mu / normalVariance mu)
          y z - D * (|y| + |z|) ^ 3 ≤ normalTrialCost mu q a y z := by
  let S : ℝ := normalVariance mu
  let T : ℝ := transverseVariance mu
  let b : ℝ := ProbabilityTheory.covariance normalValue (fun x : ℝ => x) mu / S
  have hT : 0 < T := div_pos hD hS
  let L : ℝ := 1 / S + (|b| + 1) ^ 2 / T + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  obtain ⟨C, delta, hC, hdelta, hmgf⟩ := exists_centeredNormalLogMGF_cubic_upper mu hb q a hq ha
  let D : ℝ := C * L ^ 3
  let radius : ℝ := min 1 (delta / L)
  have hDpos : 0 < D := mul_pos hC (pow_pos hL _)
  have hradius : 0 < radius := lt_min (by norm_num) (div_pos hdelta hL)
  refine ⟨D, radius, hDpos, hradius, ?_⟩
  intro y z hyz
  let v : ℝ := (normalTrialTilt mu y z).1
  let s : ℝ := (normalTrialTilt mu y z).2
  let R : ℝ := |y| + |z|
  have htilt : |v| + |s| ≤ L * R := by
    simpa only [v, s, normalTrialTilt, S, T, b, L, R] using
      trial_parameter_bound S T b y z hS hT
  have hdomain : |v| + |s| ≤ delta := by
    have hh : radius * L ≤ delta := (le_div_iff₀ hL).mp (min_le_right _ _)
    calc
      |v| + |s| ≤ L * R := htilt
      _ ≤ L * radius := mul_le_mul_of_nonneg_left hyz hL.le
      _ ≤ delta := by nlinarith only [hh]
  obtain ⟨hE, hZ, hupper⟩ := hmgf v s hdomain
  have herr : C * (|v| + |s|) ^ 3 ≤ D * R ^ 3 := by
    calc
      C * (|v| + |s|) ^ 3 ≤ C * (L * R) ^ 3 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (add_nonneg (abs_nonneg v) (abs_nonneg s)) htilt 3) hC.le
      _ = D * R ^ 3 := by dsimp only [D]; ring
  have hdual : v * y + s * z - normalTangentQuadratic mu v s / 2 =
      gaussianRateProfile S T b y z := by
    rw [normalTangentQuadratic_complete_square mu hb hS v s]
    simpa only [v, s, normalTrialTilt, S, T, b] using
      trial_quadratic_duality S T b y z hS hT
  refine ⟨hE, hZ, ?_⟩
  change gaussianRateProfile S T b y z - D * R ^ 3 ≤
    v * y + s * z - centeredNormalLogMGF mu q a v s
  calc
    gaussianRateProfile S T b y z - D * R ^ 3 =
        (v * y + s * z - normalTangentQuadratic mu v s / 2) - D * R ^ 3 := by rw [hdual]
    _ ≤ (v * y + s * z - normalTangentQuadratic mu v s / 2) - C * (|v| + |s|) ^ 3 :=
      sub_le_sub_left herr _
    _ = v * y + s * z - (normalTangentQuadratic mu v s / 2 + C * (|v| + |s|) ^ 3) := by ring
    _ ≤ v * y + s * z - centeredNormalLogMGF mu q a v s := sub_le_sub_left hupper _

theorem exists_normalTrialCost_weight_margin (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a ell : ℝ)
    (hq : 0 < q) (hell : 0 ≤ ell)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = a)
    (hS : 0 < normalVariance mu) (hD : 0 < (parabolaCovariance mu).det)
    (hgap : ell < q / (32 * transverseVariance mu)) :
    ∃ delta gamma c : ℝ, 0 < delta ∧ 0 < gamma ∧ 0 < c ∧
      ∀ n : ℕ, 1 ≤ n → ∀ k r : ℝ, 0 ≤ k →
        k / (n : ℝ) ≤ delta → |r| / (n : ℝ) ≤ delta →
          (n : ℝ) * q * k / 16 ≤ r ^ 2 →
            gamma * k + c * r ^ 2 / (n : ℝ) ≤
              (n : ℝ) * normalTrialCost mu q a (-k / (n : ℝ)) (r / (n : ℝ)) - ell * k := by
  have hT : 0 < transverseVariance mu := div_pos hD hS
  obtain ⟨D, radius, hDpos, hradius, hlower⟩ :=
    exists_normalTrialCost_cubic_lower mu hb q a hmeanY hmeanX hS hD
  exact exists_cubic_rate_weight_margin q ell (normalVariance mu) (transverseVariance mu)
    (ProbabilityTheory.covariance normalValue (fun x : ℝ => x) mu / normalVariance mu)
    D radius hq hell hS hT hDpos.le hradius hgap (normalTrialCost mu q a)
    (fun y z hyz => (hlower y z hyz).2.2)

end
end Shao.OQ3
