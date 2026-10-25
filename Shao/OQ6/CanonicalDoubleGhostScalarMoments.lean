import Shao.OQ6.CanonicalDoubleGhostRowMoments
import Shao.OQ6.FiniteQuadraticSignChaos
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

set_option autoImplicit false

namespace Shao.OQ6.CanonicalDoubleGhostScalarMoments

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal
open Shao.OQ6.FiniteHilbertSignMoments
open Shao.OQ6.FiniteMatrixSignEnergy
open Shao.OQ6.DoubleGhostSignInvariance
open Shao.OQ6.FiniteQuadraticSignChaos
open Shao.OQ6.CanonicalDoubleGhostRowMoments

def halfSumCLM (n : ℕ) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • ∑ i : Fin n,
    (PiLp.proj (𝕜 := ℝ) (2 : ℝ≥0∞) (fun _ : Fin n => ℝ) i)

def originalHalf (n : ℕ) {Ω : Type*} (r : Ω → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  (∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else r (x i) (x j)) / 2

def ghostHalf (n : ℕ) {Ω : Type*} (r : Ω → Ω → ℝ) (z : Fin n → Ω × Ω) : ℝ :=
  quadratic n (ghostMatrix n r z) (fun _ : Fin n => (1 : ℝ)) / 2

def originalUpper (n : ℕ) {Ω : Type*} (r : Ω → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then r (x i) (x j) else 0

theorem halfSumCLM_apply (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
  halfSumCLM n v = (∑ i : Fin n, v i) / 2 := by
  simp [halfSumCLM, PiLp.proj, PiLp.projₗ, smul_eq_mul, div_eq_mul_inv, mul_comm]

private theorem originalHalf_eq_halfSumCLM (n : ℕ) {Ω : Type*}
    (r : Ω → Ω → ℝ) (x : Fin n → Ω) :
  originalHalf n r x = halfSumCLM n (originalRows n r x) := by
  rw [halfSumCLM_apply]
  simp only [originalHalf, originalRows, PiLp.toLp_apply]

private theorem ghostHalf_eq_halfSumCLM (n : ℕ) {Ω : Type*}
    (r : Ω → Ω → ℝ) (z : Fin n → Ω × Ω) :
  ghostHalf n r z = halfSumCLM n (ghostRows n r z) := by
  rw [halfSumCLM_apply]
  simp only [ghostHalf, ghostRows, quadratic, rowAction_apply, one_mul, mul_one]

theorem canonical_scalar_ghost_mean (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω) [hν : IsProbabilityMeasure ν] (r : Ω → Ω → ℝ)
    (hr : Measurable (Function.uncurry r))
    (hr1 : Integrable (Function.uncurry r) (ν.prod ν))
    (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0)
    (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0) :
  Integrable (originalHalf n r) (sampleLaw n ν) ∧
  Integrable (ghostHalf n r) (pairedLaw n ν) ∧
  (∀ᵐ x : Fin n → Ω ∂sampleLaw n ν,
    Integrable (fun y : Fin n → Ω => ghostHalf n r (pairSamples n (x, y))) (sampleLaw n ν) ∧
    (∫ y : Fin n → Ω, ghostHalf n r (pairSamples n (x, y)) ∂sampleLaw n ν) = originalHalf n r x) := by
  have hVectorMean := canonical_ghost_mean n ν r hr hr1 hcR hcL
  refine ⟨?_, ?_, ?_⟩
  · apply ((halfSumCLM n).integrable_comp hVectorMean.1).congr
    filter_upwards with x
    exact (originalHalf_eq_halfSumCLM n r x).symm
  · apply ((halfSumCLM n).integrable_comp hVectorMean.2.1).congr
    filter_upwards with z
    exact (ghostHalf_eq_halfSumCLM n r z).symm
  · filter_upwards [hVectorMean.2.2] with x hx
    let vectorSection : (Fin n → Ω) → EuclideanSpace ℝ (Fin n) :=
      fun y : Fin n → Ω => ghostRows n r (pairSamples n (x, y))
    refine ⟨?_, ?_⟩
    · apply ((halfSumCLM n).integrable_comp hx.1).congr
      filter_upwards with y
      exact (ghostHalf_eq_halfSumCLM n r (pairSamples n (x, y))).symm
    · calc
        (∫ y : Fin n → Ω, ghostHalf n r (pairSamples n (x, y)) ∂sampleLaw n ν) =
            ∫ y : Fin n → Ω, halfSumCLM n (vectorSection y) ∂sampleLaw n ν := by
          apply integral_congr_ae
          filter_upwards with y
          exact ghostHalf_eq_halfSumCLM n r (pairSamples n (x, y))
        _ = halfSumCLM n (∫ y : Fin n → Ω, vectorSection y ∂sampleLaw n ν) :=
          (halfSumCLM n).integral_comp_comm hx.1
        _ = halfSumCLM n (originalRows n r x) := congrArg (halfSumCLM n) hx.2
        _ = originalHalf n r x := (originalHalf_eq_halfSumCLM n r x).symm

theorem ghost_scalar_sign_law (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω) [hν : IsProbabilityMeasure ν] (r : Ω → Ω → ℝ)
    (s : Fin n → Bool) (hr : Measurable (Function.uncurry r)) :
  Measurable (fun z : Fin n → Ω × Ω => |ghostHalf n r z|) ∧
  Measurable (fun z : Fin n → Ω × Ω =>
    |quadratic n (ghostMatrix n r z) (signPath n s) / 2|) ∧
  Measure.map (fun z : Fin n → Ω × Ω => |ghostHalf n r z|) (pairedLaw n ν) =
    Measure.map (fun z : Fin n → Ω × Ω =>
      |quadratic n (ghostMatrix n r z) (signPath n s) / 2|) (pairedLaw n ν) := by
  let corner11 : Fin n → Fin n → (Fin n → Ω × Ω) → Ω × Ω :=
    fun (i j : Fin n) (z : Fin n → Ω × Ω) => ((z i).1, (z j).1)
  let corner21 : Fin n → Fin n → (Fin n → Ω × Ω) → Ω × Ω :=
    fun (i j : Fin n) (z : Fin n → Ω × Ω) => ((z i).2, (z j).1)
  let corner12 : Fin n → Fin n → (Fin n → Ω × Ω) → Ω × Ω :=
    fun (i j : Fin n) (z : Fin n → Ω × Ω) => ((z i).1, (z j).2)
  let corner22 : Fin n → Fin n → (Fin n → Ω × Ω) → Ω × Ω :=
    fun (i j : Fin n) (z : Fin n → Ω × Ω) => ((z i).2, (z j).2)
  let ghostEntry : Fin n → Fin n → (Fin n → Ω × Ω) → ℝ :=
    fun (i j : Fin n) (z : Fin n → Ω × Ω) => ghostMatrix n r z i j
  let leftAbs : (Fin n → Ω × Ω) → ℝ :=
    fun z : Fin n → Ω × Ω => |ghostHalf n r z|
  let signedHalf : (Fin n → Ω × Ω) → ℝ :=
    fun z : Fin n → Ω × Ω => quadratic n (ghostMatrix n r z) (signPath n s) / 2
  let rightAbs : (Fin n → Ω × Ω) → ℝ := fun z : Fin n → Ω × Ω => |signedHalf z|
  have hEntry (i j : Fin n) : Measurable (ghostEntry i j) := by
    by_cases hij : i = j
    · subst j
      simpa only [ghostEntry, ghostMatrix, ite_true] using
        (measurable_const : Measurable (fun _ : Fin n → Ω × Ω => (0 : ℝ)))
    · have h11 : Measurable (Function.uncurry r ∘ corner11 i j) := by
        apply hr.comp
        exact ((measurable_pi_apply i).fst).prodMk ((measurable_pi_apply j).fst)
      have h21 : Measurable (Function.uncurry r ∘ corner21 i j) := by
        apply hr.comp
        exact ((measurable_pi_apply i).snd).prodMk ((measurable_pi_apply j).fst)
      have h12 : Measurable (Function.uncurry r ∘ corner12 i j) := by
        apply hr.comp
        exact ((measurable_pi_apply i).fst).prodMk ((measurable_pi_apply j).snd)
      have h22 : Measurable (Function.uncurry r ∘ corner22 i j) := by
        apply hr.comp
        exact ((measurable_pi_apply i).snd).prodMk ((measurable_pi_apply j).snd)
      change Measurable (fun z : Fin n → Ω × Ω => ghostMatrix n r z i j)
      simp only [ghostMatrix, ite_eq_right hij]
      convert ((h11.sub h21).sub h12).add h22 using 1
      funext z
      simp only [Function.comp_def, Function.uncurry, corner11, corner21, corner12,
        corner22, Pi.sub_apply, Pi.add_apply]
  have hG : Measurable (ghostHalf n r) := by
    change Measurable (fun z : Fin n → Ω × Ω => ghostHalf n r z)
    simp only [ghostHalf, quadratic, mul_one]
    change Measurable (fun z : Fin n → Ω × Ω =>
      (∑ i : Fin n, ∑ j : Fin n, ghostEntry i j z) / 2)
    fun_prop
  have hLeft : Measurable leftAbs := by
    change Measurable (fun z : Fin n → Ω × Ω => |ghostHalf n r z|)
    simpa only [Real.norm_eq_abs] using
      (show Measurable (fun z : Fin n → Ω × Ω => ‖ghostHalf n r z‖) from
        continuous_norm.measurable.comp hG)
  have hSwap (z : Fin n → Ω × Ω) :
      ghostHalf n r (swapSample n s z) = signedHalf z := by
    dsimp only [ghostHalf, signedHalf, quadratic]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [ghostMatrix_swap]
    simp only [signPath, mul_one]
    ring
  have hRight (z : Fin n → Ω × Ω) :
      rightAbs z = leftAbs (swapSample n s z) := (congrArg abs (hSwap z)).symm
  have hMP := swapSample_measurePreserving n ν s
  have hRightMeas : Measurable rightAbs := by
    convert hLeft.comp hMP.measurable using 1
    funext z
    exact hRight z
  refine ⟨hLeft, hRightMeas, ?_⟩
  change Measure.map leftAbs (pairedLaw n ν) = Measure.map rightAbs (pairedLaw n ν)
  calc
    Measure.map leftAbs (pairedLaw n ν) =
        Measure.map leftAbs (Measure.map (swapSample n s) (pairedLaw n ν)) := by
      rw [hMP.map_eq]
    _ = Measure.map (leftAbs ∘ swapSample n s) (pairedLaw n ν) :=
      Measure.map_map hLeft hMP.measurable
    _ = Measure.map rightAbs (pairedLaw n ν) := by
      congr 1
      funext z
      exact (hRight z).symm

private theorem abs_integral_rpow_le_integral {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [hμ : IsProbabilityMeasure μ] (f : Ω → ℝ) (q : ℝ)
    (hq : 2 ≤ q) (hf : Integrable f μ)
    (hfq : Integrable (fun a : Ω => Real.rpow |f a| q) μ) :
  Real.rpow |∫ a : Ω, f a ∂μ| q ≤ ∫ a : Ω, Real.rpow |f a| q ∂μ := by
  let powerF : Ω → ℝ := fun a : Ω => Real.rpow |f a| q
  let rootPower : ℝ → ℝ := fun t : ℝ => Real.rpow t (1 / q)
  let absF : Ω → ℝ := fun a : Ω => |f a|
  let momentF : ℝ := ∫ a : Ω, powerF a ∂μ
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hinvpos : 0 < 1 / q := one_div_pos.mpr hqpos
  have hinvle : 1 / q ≤ 1 := by
    apply (div_le_iff₀ hqpos).2
    linarith
  have hRoot (a : Ω) : rootPower (powerF a) = absF a := by
    simp only [rootPower, powerF, absF, Real.rpow_eq_pow]
    rw [← Real.rpow_mul (abs_nonneg (f a)), mul_one_div_cancel hqpos.ne', Real.rpow_one]
  have hRootInt : Integrable (rootPower ∘ powerF) μ := by
    apply hf.norm.congr
    filter_upwards with a
    change |f a| = rootPower (powerF a)
    exact (hRoot a).symm
  have hConcave : ConcaveOn ℝ (Set.Ici 0) rootPower := by
    simpa only [rootPower, Real.rpow_eq_pow] using Real.concaveOn_rpow hinvpos.le hinvle
  have hContinuous : ContinuousOn rootPower (Set.Ici 0) := by
    apply Continuous.continuousOn
    simpa only [rootPower, Real.rpow_eq_pow] using Real.continuous_rpow_const hinvpos.le
  have hNonneg (a : Ω) : 0 ≤ powerF a := Real.rpow_nonneg (abs_nonneg (f a)) q
  have hJensen := hConcave.le_map_integral (μ := μ) (f := powerF)
    hContinuous isClosed_Ici (Filter.Eventually.of_forall hNonneg) hfq hRootInt
  have hRootIntegral : (∫ a : Ω, rootPower (powerF a) ∂μ) = ∫ a : Ω, |f a| ∂μ := by
    apply integral_congr_ae
    filter_upwards with a
    exact hRoot a
  have hJ : (∫ a : Ω, |f a| ∂μ) ≤ Real.rpow momentF (1 / q) := by
    rw [hRootIntegral] at hJensen
    exact hJensen
  have hNorm : |∫ a : Ω, f a ∂μ| ≤ ∫ a : Ω, |f a| ∂μ := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm f
  have hMomentNonneg : 0 ≤ momentF := integral_nonneg hNonneg
  calc
    Real.rpow |∫ a : Ω, f a ∂μ| q ≤ Real.rpow (Real.rpow momentF (1 / q)) q :=
      Real.rpow_le_rpow (abs_nonneg _) (hNorm.trans hJ) hqpos.le
    _ = momentF := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_mul hMomentNonneg, one_div_mul_cancel hqpos.ne', Real.rpow_one]

private theorem half_quadratic_envelope (n : ℕ) (D : Fin n → Fin n → ℝ)
    (W : Fin n → ℝ) (u : Shao.Path n)
    (hW : ∀ i : Fin n, 0 ≤ W i)
    (hD : ∀ i j : Fin n, |D i j| ≤ W i * W j)
    (hu : ∀ i : Fin n, |u i| ≤ 1) :
  |quadratic n D u / 2| ≤ ((n : ℝ) / 2) * weightEnergy n W := by
  let productEntry : Fin n → Fin n → ℝ := fun i j : Fin n => W i * W j
  let squareEntry : Fin n → Fin n → ℝ := fun i j : Fin n => (W i ^ 2 + W j ^ 2) / 2
  have hProduct (i j : Fin n) : productEntry i j ≤ squareEntry i j := by
    dsimp only [productEntry, squareEntry]
    nlinarith [sq_nonneg (W i - W j)]
  have hEntry (i j : Fin n) : |D i j * u i * u j| ≤ productEntry i j := by
    simp only [abs_mul]
    calc
      |D i j| * |u i| * |u j| ≤ |D i j| * 1 * 1 := by
        gcongr
        · exact hu i
        · exact hu j
      _ = |D i j| := by ring
      _ ≤ productEntry i j := hD i j
  have hSum : (∑ i : Fin n, ∑ j : Fin n, productEntry i j) ≤
      (n : ℝ) * weightEnergy n W := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, productEntry i j) ≤
          ∑ i : Fin n, ∑ j : Fin n, squareEntry i j := by
        exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hProduct i j))
      _ = (n : ℝ) * weightEnergy n W := by
        dsimp only [squareEntry, weightEnergy]
        simp_rw [div_eq_mul_inv, add_mul, Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← Finset.mul_sum, ← Finset.sum_mul]
        ring
  have hTriangle : |quadratic n D u| ≤
      ∑ i : Fin n, ∑ j : Fin n, |D i j * u i * u j| := by
    unfold quadratic
    calc
      |∑ i : Fin n, ∑ j : Fin n, D i j * u i * u j| ≤
          ∑ i : Fin n, |∑ j : Fin n, D i j * u i * u j| := by
        simpa only [Real.norm_eq_abs] using
          norm_sum_le Finset.univ (fun i : Fin n => ∑ j : Fin n, D i j * u i * u j)
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, |D i j * u i * u j| := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [Real.norm_eq_abs] using
          norm_sum_le Finset.univ (fun j : Fin n => D i j * u i * u j)
  calc
    |quadratic n D u / 2| = |quadratic n D u| / 2 := by norm_num [abs_div]
    _ ≤ (∑ i : Fin n, ∑ j : Fin n, |D i j * u i * u j|) / 2 :=
      div_le_div_of_nonneg_right hTriangle (by norm_num)
    _ ≤ (∑ i : Fin n, ∑ j : Fin n, productEntry i j) / 2 :=
      div_le_div_of_nonneg_right
        (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hEntry i j)))
        (by norm_num)
    _ ≤ ((n : ℝ) * weightEnergy n W) / 2 :=
      div_le_div_of_nonneg_right hSum (by norm_num)
    _ = ((n : ℝ) / 2) * weightEnergy n W := by ring

theorem ghost_scalar_qmoment_bound (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω) [hν : IsProbabilityMeasure ν] (r : Ω → Ω → ℝ)
    (w : Ω → ℝ) (q : ℝ) (hr : Measurable (Function.uncurry r))
    (hq : 2 ≤ q) (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hR : ∀ᵐ p : Ω × Ω ∂ν.prod ν, |r p.1 p.2| ≤ w p.1 * w p.2)
    (hS : Integrable (fun z : Fin n → Ω × Ω => Real.rpow (pairedEnergy n w z) q) (pairedLaw n ν)) :
  Integrable (fun z : Fin n → Ω × Ω => Real.rpow |ghostHalf n r z| q) (pairedLaw n ν) ∧
  (∫ z : Fin n → Ω × Ω, Real.rpow |ghostHalf n r z| q ∂pairedLaw n ν) ≤
    Real.rpow ((8 : ℝ) * q) q *
      (∫ z : Fin n → Ω × Ω, Real.rpow (pairedEnergy n w z) q ∂pairedLaw n ν) := by
  letI instP : IsProbabilityMeasure (pairedLaw n ν) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => ν.prod ν)))
  let K : ℝ := (8 : ℝ) * q
  let S : (Fin n → Ω × Ω) → ℝ := pairedEnergy n w
  let recoverPower : ℝ → ℝ := fun t : ℝ => Real.rpow (max t 0) (1 / q)
  let onePlusPower : (Fin n → Ω × Ω) → ℝ :=
    fun z : Fin n → Ω × Ω => 1 + Real.rpow (S z) q
  let f1 : (Fin n → Ω × Ω) → ℝ :=
    fun z : Fin n → Ω × Ω => Real.rpow |ghostHalf n r z| q
  let signedPower : (Fin n → Bool) → (Fin n → Ω × Ω) → ℝ :=
    fun (s : Fin n → Bool) (z : Fin n → Ω × Ω) =>
      Real.rpow |quadratic n (ghostMatrix n r z) (signPath n s) / 2| q
  let cubePower : (Fin n → Ω × Ω) → ℝ :=
    fun z : Fin n → Ω × Ω => cubeMean n (fun s : Fin n → Bool => signedPower s z)
  let dimensionBound : ℝ := (n : ℝ) / 2
  let dominatingPower : (Fin n → Ω × Ω) → ℝ :=
    fun z : Fin n → Ω × Ω => Real.rpow dimensionBound q * Real.rpow (S z) q
  let scalarPower : ℝ → ℝ := fun t : ℝ => Real.rpow t q
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hq1 : 1 ≤ q := by linarith
  have hinvpos : 0 < 1 / q := one_div_pos.mpr hqpos
  have hKNonneg : 0 ≤ K := by dsimp only [K]; positivity
  have hDimNonneg : 0 ≤ dimensionBound := by dsimp only [dimensionBound]; positivity
  have hSnonneg (z : Fin n → Ω × Ω) : 0 ≤ S z := by
    dsimp only [S, pairedEnergy, weightEnergy]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hRecoverCont : Continuous recoverPower :=
    (Real.continuous_rpow_const hinvpos.le).comp (continuous_id.max continuous_const)
  have hRecover (z : Fin n → Ω × Ω) : recoverPower (Real.rpow (S z) q) = S z := by
    dsimp only [recoverPower]
    simp only [Real.rpow_eq_pow]
    rw [max_eq_left (Real.rpow_nonneg (hSnonneg z) q),
      ← Real.rpow_mul (hSnonneg z), mul_one_div_cancel hqpos.ne', Real.rpow_one]
  have hSmeas : AEStronglyMeasurable S (pairedLaw n ν) := by
    apply (hRecoverCont.comp_aestronglyMeasurable hS.aestronglyMeasurable).congr
    exact Filter.Eventually.of_forall hRecover
  have hOnePlus : Integrable onePlusPower (pairedLaw n ν) :=
    (integrable_const (1 : ℝ)).add hS
  have hSle (z : Fin n → Ω × Ω) : S z ≤ onePlusPower z := by
    change S z ≤ 1 + Real.rpow (S z) q
    simp only [Real.rpow_eq_pow]
    by_cases hz : S z ≤ 1
    · have hp := Real.rpow_nonneg (hSnonneg z) q
      linarith
    · have hp := Real.self_le_rpow_of_one_le (le_of_lt (lt_of_not_ge hz)) hq1
      linarith
  have hSInt : Integrable S (pairedLaw n ν) := by
    apply hOnePlus.mono' hSmeas
    filter_upwards with z
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hSnonneg z)] using hSle z
  have hDomInt : Integrable dominatingPower (pairedLaw n ν) :=
    hS.const_mul (Real.rpow dimensionBound q)
  have hEnvelope := ghostMatrix_ae_envelope n ν r w hW hR
  have hLaw (s : Fin n → Bool) := ghost_scalar_sign_law n ν r s hr
  have hF1Meas : Measurable f1 := by
    have hforall : ∀ s : Fin n → Bool, Measurable f1 := by
      intro s
      exact (Real.continuous_rpow_const hqpos.le).measurable.comp (hLaw s).1
    simpa only [forall_const] using hforall
  have hSignedMeas (s : Fin n → Bool) : Measurable (signedPower s) :=
    (Real.continuous_rpow_const hqpos.le).measurable.comp (hLaw s).2.1
  have hF1Int : Integrable f1 (pairedLaw n ν) := by
    apply hDomInt.mono' hF1Meas.aestronglyMeasurable
    filter_upwards [hEnvelope] with z hz
    change |Real.rpow |ghostHalf n r z| q| ≤
      Real.rpow dimensionBound q * Real.rpow (S z) q
    simp only [Real.rpow_eq_pow]
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) q)]
    have hb : |ghostHalf n r z| ≤ dimensionBound * S z :=
      half_quadratic_envelope n (ghostMatrix n r z) (ghostWeight n w z)
        (fun _ : Fin n => (1 : ℝ)) hz.1 hz.2 (by intro i; norm_num)
    calc
      |ghostHalf n r z| ^ q ≤ (dimensionBound * S z) ^ q :=
        Real.rpow_le_rpow (abs_nonneg _) hb hqpos.le
      _ = dimensionBound ^ q * S z ^ q := Real.mul_rpow hDimNonneg (hSnonneg z)
  have hSignedInt (s : Fin n → Bool) : Integrable (signedPower s) (pairedLaw n ν) := by
    apply hDomInt.mono' (hSignedMeas s).aestronglyMeasurable
    filter_upwards [hEnvelope] with z hz
    change |Real.rpow |quadratic n (ghostMatrix n r z) (signPath n s) / 2| q| ≤
      Real.rpow dimensionBound q * Real.rpow (S z) q
    simp only [Real.rpow_eq_pow]
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) q)]
    have hsign (i : Fin n) : |signPath n s i| ≤ 1 := by
      cases hs : s i <;> simp [signPath, signValue, hs]
    have hb := half_quadratic_envelope n (ghostMatrix n r z) (ghostWeight n w z)
      (signPath n s) hz.1 hz.2 hsign
    calc
      |quadratic n (ghostMatrix n r z) (signPath n s) / 2| ^ q ≤
          (dimensionBound * S z) ^ q := Real.rpow_le_rpow (abs_nonneg _) hb hqpos.le
      _ = dimensionBound ^ q * S z ^ q := Real.mul_rpow hDimNonneg (hSnonneg z)
  have hScalarMeas : StronglyMeasurable scalarPower :=
    (Real.continuous_rpow_const hqpos.le).stronglyMeasurable
  have hLawIntegral (s : Fin n → Bool) :
      (∫ z : Fin n → Ω × Ω, f1 z ∂pairedLaw n ν) =
        ∫ z : Fin n → Ω × Ω, signedPower s z ∂pairedLaw n ν := by
    calc
      (∫ z : Fin n → Ω × Ω, f1 z ∂pairedLaw n ν) =
          ∫ t : ℝ, scalarPower t ∂Measure.map
            (fun z : Fin n → Ω × Ω => |ghostHalf n r z|) (pairedLaw n ν) :=
        (integral_map_of_stronglyMeasurable (hLaw s).1 hScalarMeas).symm
      _ = ∫ t : ℝ, scalarPower t ∂Measure.map
            (fun z : Fin n → Ω × Ω =>
              |quadratic n (ghostMatrix n r z) (signPath n s) / 2|)
            (pairedLaw n ν) := by rw [(hLaw s).2.2]
      _ = ∫ z : Fin n → Ω × Ω, signedPower s z ∂pairedLaw n ν :=
        integral_map_of_stronglyMeasurable (hLaw s).2.1 hScalarMeas
  have hCubeInt : Integrable cubePower (pairedLaw n ν) :=
    (integrable_finsetSum Finset.univ (fun s _ => hSignedInt s)).const_mul ((2 : ℝ) ^ n)⁻¹
  have hCubeNonneg (z : Fin n → Ω × Ω) : 0 ≤ cubePower z := by
    apply mul_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n))
    exact Finset.sum_nonneg (fun s _ => Real.rpow_nonneg (abs_nonneg _) q)
  have hCubeIntegral : (∫ z : Fin n → Ω × Ω, cubePower z ∂pairedLaw n ν) =
      ∫ z : Fin n → Ω × Ω, f1 z ∂pairedLaw n ν := by
    change (∫ z : Fin n → Ω × Ω, ((2 : ℝ) ^ n)⁻¹ *
      (∑ s : Fin n → Bool, signedPower s z) ∂pairedLaw n ν) = _
    rw [integral_const_mul, integral_finsetSum Finset.univ (fun s _ => hSignedInt s)]
    simp_rw [← hLawIntegral]
    simp [Fintype.card_fun, Fintype.card_fin, pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)]
  have hCubeBound : ∀ᵐ z : Fin n → Ω × Ω ∂pairedLaw n ν,
      cubePower z ≤ Real.rpow K q * Real.rpow (S z) q := by
    filter_upwards [hEnvelope] with z hz
    have hdiag (i : Fin n) : ghostMatrix n r z i i = 0 := by
      simp only [ghostMatrix, ite_true]
    have hEnergy : Real.sqrt (entryEnergy n (ghostMatrix n r z)) ≤ S z := by
      simpa only [entryEnergy, matrixEnergy, S, pairedEnergy] using
        (matrix_energy_bound n (ghostMatrix n r z) (ghostWeight n w z) hz.1 hz.2).2
    have hbase : Real.rpow (cubePower z) (1 / q) ≤ K * S z := by
      calc
        Real.rpow (cubePower z) (1 / q) ≤
            (8 : ℝ) * q * Real.sqrt (entryEnergy n (ghostMatrix n r z)) :=
          finite_half_quadratic_sign_moment_bound n (ghostMatrix n r z) q hdiag hq
        _ ≤ K * S z := mul_le_mul_of_nonneg_left hEnergy hKNonneg
    calc
      cubePower z = Real.rpow (Real.rpow (cubePower z) (1 / q)) q := by
        simp only [Real.rpow_eq_pow]
        rw [← Real.rpow_mul (hCubeNonneg z), one_div_mul_cancel hqpos.ne', Real.rpow_one]
      _ ≤ Real.rpow (K * S z) q :=
        Real.rpow_le_rpow (Real.rpow_nonneg (hCubeNonneg z) (1 / q)) hbase hqpos.le
      _ = Real.rpow K q * Real.rpow (S z) q := Real.mul_rpow hKNonneg (hSnonneg z)
  refine ⟨hF1Int, ?_⟩
  calc
    (∫ z : Fin n → Ω × Ω, f1 z ∂pairedLaw n ν) =
        ∫ z : Fin n → Ω × Ω, cubePower z ∂pairedLaw n ν := hCubeIntegral.symm
    _ ≤ ∫ z : Fin n → Ω × Ω, Real.rpow K q * Real.rpow (S z) q ∂pairedLaw n ν :=
      integral_mono_ae hCubeInt (hS.const_mul (Real.rpow K q)) hCubeBound
    _ = Real.rpow K q * (∫ z : Fin n → Ω × Ω, Real.rpow (S z) q ∂pairedLaw n ν) :=
      integral_const_mul _ _

theorem canonical_half_qmoment_bound (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω) [hν : IsProbabilityMeasure ν] (r : Ω → Ω → ℝ)
    (w : Ω → ℝ) (q : ℝ) (hr : Measurable (Function.uncurry r))
    (hr1 : Integrable (Function.uncurry r) (ν.prod ν))
    (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0)
    (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0)
    (hq : 2 ≤ q) (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hR : ∀ᵐ p : Ω × Ω ∂ν.prod ν, |r p.1 p.2| ≤ w p.1 * w p.2)
    (hS : Integrable (fun z : Fin n → Ω × Ω => Real.rpow (pairedEnergy n w z) q) (pairedLaw n ν)) :
  Integrable (fun x : Fin n → Ω => Real.rpow |originalHalf n r x| q) (sampleLaw n ν) ∧
  Real.rpow (∫ x : Fin n → Ω, Real.rpow |originalHalf n r x| q ∂sampleLaw n ν) (1 / q) ≤
    (8 : ℝ) * q *
      Real.rpow (∫ z : Fin n → Ω × Ω, Real.rpow (pairedEnergy n w z) q ∂pairedLaw n ν) (1 / q) := by
  letI instM : IsProbabilityMeasure (sampleLaw n ν) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => ν)))
  letI instMM : IsProbabilityMeasure ((sampleLaw n ν).prod (sampleLaw n ν)) :=
    inferInstanceAs (IsProbabilityMeasure ((Measure.pi (fun _ : Fin n => ν)).prod (Measure.pi (fun _ : Fin n => ν))))
  let pairedGhost : ((Fin n → Ω) × (Fin n → Ω)) → ℝ :=
    fun p : (Fin n → Ω) × (Fin n → Ω) => ghostHalf n r (pairSamples n p)
  let innerQ : (Fin n → Ω) → ℝ :=
    fun x : Fin n → Ω => ∫ y : Fin n → Ω, Real.rpow |pairedGhost (x, y)| q ∂sampleLaw n ν
  let rowQ : (Fin n → Ω) → ℝ := fun x : Fin n → Ω => Real.rpow |originalHalf n r x| q
  let K : ℝ := (8 : ℝ) * q
  let weightQIntegral : ℝ :=
    ∫ z : Fin n → Ω × Ω, Real.rpow (pairedEnergy n w z) q ∂pairedLaw n ν
  let rowQIntegral : ℝ := ∫ x : Fin n → Ω, rowQ x ∂sampleLaw n ν
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hinvpos : 0 < 1 / q := one_div_pos.mpr hqpos
  have hScalarMean := canonical_scalar_ghost_mean n ν r hr hr1 hcR hcL
  have hghost := ghost_scalar_qmoment_bound n ν r w q hr hq hW hR hS
  have hpair := pairSamples_measurePreserving n ν
  have hPairedQ : Integrable
      (fun p : (Fin n → Ω) × (Fin n → Ω) => Real.rpow |pairedGhost p| q)
      ((sampleLaw n ν).prod (sampleLaw n ν)) :=
    hpair.integrable_comp_of_integrable hghost.1
  have hInnerInt : Integrable innerQ (sampleLaw n ν) := hPairedQ.integral_prod_left
  have hRowMeas : AEStronglyMeasurable rowQ (sampleLaw n ν) := by
    apply (Real.continuous_rpow_const hqpos.le).comp_aestronglyMeasurable
    simpa only [Real.norm_eq_abs] using hScalarMean.1.norm.aestronglyMeasurable
  have hRowNonneg (x : Fin n → Ω) : 0 ≤ rowQ x :=
    Real.rpow_nonneg (abs_nonneg (originalHalf n r x)) q
  have hRowDom : ∀ᵐ x : Fin n → Ω ∂sampleLaw n ν, rowQ x ≤ innerQ x := by
    filter_upwards [hScalarMean.2.2, hPairedQ.prod_right_ae] with x hx hxq
    let sectionGhost : (Fin n → Ω) → ℝ := fun y : Fin n → Ω => pairedGhost (x, y)
    have hSection : Integrable sectionGhost (sampleLaw n ν) := hx.1
    have hSectionQ : Integrable
        (fun y : Fin n → Ω => Real.rpow |sectionGhost y| q) (sampleLaw n ν) := hxq
    have hjensen := abs_integral_rpow_le_integral (sampleLaw n ν)
      sectionGhost q hq hSection hSectionQ
    change Real.rpow |∫ y : Fin n → Ω, sectionGhost y ∂sampleLaw n ν| q ≤ innerQ x at hjensen
    rw [show (∫ y : Fin n → Ω, sectionGhost y ∂sampleLaw n ν) = originalHalf n r x from hx.2] at hjensen
    exact hjensen
  have hRowInt : Integrable rowQ (sampleLaw n ν) := by
    apply hInnerInt.mono' hRowMeas
    filter_upwards [hRowDom] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hRowNonneg x)] using hx
  have hPairIntegral :
      (∫ p : (Fin n → Ω) × (Fin n → Ω), Real.rpow |pairedGhost p| q
        ∂(sampleLaw n ν).prod (sampleLaw n ν)) =
      ∫ z : Fin n → Ω × Ω, Real.rpow |ghostHalf n r z| q ∂pairedLaw n ν := by
    calc
      (∫ p : (Fin n → Ω) × (Fin n → Ω), Real.rpow |pairedGhost p| q
          ∂(sampleLaw n ν).prod (sampleLaw n ν)) =
          ∫ z : Fin n → Ω × Ω, Real.rpow |ghostHalf n r z| q
            ∂Measure.map (pairSamples n) ((sampleLaw n ν).prod (sampleLaw n ν)) := by
        symm
        apply integral_map hpair.measurable.aemeasurable
        rw [hpair.map_eq]
        exact hghost.1.aestronglyMeasurable
      _ = ∫ z : Fin n → Ω × Ω, Real.rpow |ghostHalf n r z| q ∂pairedLaw n ν := by
        rw [hpair.map_eq]
  have hMoment : rowQIntegral ≤ Real.rpow K q * weightQIntegral := by
    calc
      rowQIntegral ≤ ∫ x : Fin n → Ω, innerQ x ∂sampleLaw n ν :=
        integral_mono_ae hRowInt hInnerInt hRowDom
      _ = ∫ p : (Fin n → Ω) × (Fin n → Ω), Real.rpow |pairedGhost p| q
          ∂(sampleLaw n ν).prod (sampleLaw n ν) := (integral_prod _ hPairedQ).symm
      _ = ∫ z : Fin n → Ω × Ω, Real.rpow |ghostHalf n r z| q ∂pairedLaw n ν := hPairIntegral
      _ ≤ Real.rpow K q * weightQIntegral := hghost.2
  have hRowIntegralNonneg : 0 ≤ rowQIntegral := integral_nonneg hRowNonneg
  have hWeightIntegralNonneg : 0 ≤ weightQIntegral := by
    apply integral_nonneg
    intro z
    apply Real.rpow_nonneg
    dsimp only [pairedEnergy, weightEnergy]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hKNonneg : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨hRowInt, ?_⟩
  calc
    Real.rpow rowQIntegral (1 / q) ≤
        Real.rpow (Real.rpow K q * weightQIntegral) (1 / q) :=
      Real.rpow_le_rpow hRowIntegralNonneg hMoment hinvpos.le
    _ = Real.rpow (Real.rpow K q) (1 / q) * Real.rpow weightQIntegral (1 / q) :=
      Real.mul_rpow (Real.rpow_nonneg hKNonneg q) hWeightIntegralNonneg
    _ = K * Real.rpow weightQIntegral (1 / q) := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_mul hKNonneg, mul_one_div_cancel hqpos.ne', Real.rpow_one]

theorem original_half_eq_upper (n : ℕ) {Ω : Type*} (r : Ω → Ω → ℝ)
    (hsym : ∀ a b : Ω, r a b = r b a) (x : Fin n → Ω) :
  originalHalf n r x = originalUpper n r x := by
  let originalMatrix : Fin n → Fin n → ℝ :=
    fun i j : Fin n => if i = j then 0 else r (x i) (x j)
  have hdiag (i : Fin n) : originalMatrix i i = 0 := by
    simp only [originalMatrix, ite_true]
  have hsymMatrix (i j : Fin n) : originalMatrix i j = originalMatrix j i := by
    by_cases hij : i = j
    · subst j
      rfl
    · have hji : j ≠ i := by
        intro h
        exact hij h.symm
      simpa only [originalMatrix, ite_eq_right hij, ite_eq_right hji] using hsym (x i) (x j)
  have hBridge := quadratic_eq_two_upper n originalMatrix (fun _ : Fin n => (1 : ℝ))
    hdiag hsymMatrix
  have hUpper : (∑ i : Fin n, ∑ j : Fin n,
      if i < j then originalMatrix i j * (1 : ℝ) * (1 : ℝ) else 0) = originalUpper n r x := by
    unfold originalUpper
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i < j
    · simp only [hij, ite_true, originalMatrix, ite_eq_right (ne_of_lt hij), mul_one]
    · simp only [hij, ite_false]
  rw [hUpper] at hBridge
  change (∑ i : Fin n, ∑ j : Fin n, originalMatrix i j * (1 : ℝ) * (1 : ℝ)) =
    (2 : ℝ) * originalUpper n r x at hBridge
  simp only [mul_one] at hBridge
  change (∑ i : Fin n, ∑ j : Fin n, originalMatrix i j) / 2 = originalUpper n r x
  rw [hBridge]
  ring

theorem canonical_scalar_qmoment_bound (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω) [hν : IsProbabilityMeasure ν] (r : Ω → Ω → ℝ)
    (w : Ω → ℝ) (q : ℝ) (hr : Measurable (Function.uncurry r))
    (hr1 : Integrable (Function.uncurry r) (ν.prod ν))
    (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0)
    (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0)
    (hsym : ∀ a b : Ω, r a b = r b a)
    (hq : 2 ≤ q) (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a)
    (hR : ∀ᵐ p : Ω × Ω ∂ν.prod ν, |r p.1 p.2| ≤ w p.1 * w p.2)
    (hS : Integrable (fun z : Fin n → Ω × Ω => Real.rpow (pairedEnergy n w z) q) (pairedLaw n ν)) :
  Integrable (fun x : Fin n → Ω => Real.rpow |originalUpper n r x| q) (sampleLaw n ν) ∧
  Real.rpow (∫ x : Fin n → Ω, Real.rpow |originalUpper n r x| q ∂sampleLaw n ν) (1 / q) ≤
    (8 : ℝ) * q *
      Real.rpow (∫ z : Fin n → Ω × Ω, Real.rpow (pairedEnergy n w z) q ∂pairedLaw n ν) (1 / q) := by
  have hHalf := canonical_half_qmoment_bound n ν r w q hr hr1 hcR hcL hq hW hR hS
  simpa only [original_half_eq_upper n r hsym] using hHalf

end
end Shao.OQ6.CanonicalDoubleGhostScalarMoments
