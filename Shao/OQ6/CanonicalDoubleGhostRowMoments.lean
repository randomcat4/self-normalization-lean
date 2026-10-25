import Shao.OQ6.DoubleGhostSignInvariance
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

set_option autoImplicit false

namespace Shao.OQ6.CanonicalDoubleGhostRowMoments

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal
open Shao.OQ6.FiniteHilbertSignMoments
open Shao.OQ6.FiniteMatrixSignEnergy
open Shao.OQ6.DoubleGhostSignInvariance

def sampleLaw (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (ν : Measure Ω) : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => ν)

def pairSamples (n : ℕ) {Ω : Type*} (p : (Fin n → Ω) × (Fin n → Ω)) : Fin n → Ω × Ω := fun i : Fin n => (p.1 i, p.2 i)

def originalRows (n : ℕ) {Ω : Type*} (r : Ω → Ω → ℝ) (x : Fin n → Ω) : EuclideanSpace ℝ (Fin n) := WithLp.toLp (2 : ℝ≥0∞) (V := Fin n → ℝ) (fun i : Fin n => ∑ j : Fin n, if i = j then 0 else r (x i) (x j))

def ghostRows (n : ℕ) {Ω : Type*} (r : Ω → Ω → ℝ) (z : Fin n → Ω × Ω) : EuclideanSpace ℝ (Fin n) := rowAction n (ghostMatrix n r z) (fun _ : Fin n => (1 : ℝ))

def pairedEnergy (n : ℕ) {Ω : Type*} (w : Ω → ℝ) (z : Fin n → Ω × Ω) : ℝ := weightEnergy n (ghostWeight n w z)

theorem pairSamples_measurePreserving (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (ν : Measure Ω) [hν : IsProbabilityMeasure ν] : MeasurePreserving (pairSamples n (Ω := Ω)) ((sampleLaw n ν).prod (sampleLaw n ν)) (pairedLaw n ν) := by
  let splitEquiv : (Fin n → Ω × Ω) ≃ᵐ ((Fin n → Ω) × (Fin n → Ω)) := MeasurableEquiv.arrowProdEquivProdArrow Ω Ω (Fin n)
  let constantMarginal : Fin n → Measure Ω := fun _ : Fin n => ν
  have hsplit : MeasurePreserving splitEquiv (pairedLaw n ν)
      ((sampleLaw n ν).prod (sampleLaw n ν)) := by
    simpa only [splitEquiv, constantMarginal, sampleLaw, pairedLaw] using
      measurePreserving_arrowProdEquivProdArrow Ω Ω (Fin n) constantMarginal constantMarginal
  change MeasurePreserving splitEquiv.symm
    ((sampleLaw n ν).prod (sampleLaw n ν)) (pairedLaw n ν)
  exact MeasureTheory.MeasurePreserving.symm splitEquiv hsplit

theorem canonical_ghost_mean (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (ν : Measure Ω) [hν : IsProbabilityMeasure ν] (r : Ω → Ω → ℝ) (hr : Measurable (Function.uncurry r)) (hr1 : Integrable (Function.uncurry r) (ν.prod ν)) (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0) (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0) : Integrable (originalRows n r) (sampleLaw n ν) ∧ Integrable (ghostRows n r) (pairedLaw n ν) ∧ (∀ᵐ x : Fin n → Ω ∂sampleLaw n ν, Integrable (fun y : Fin n → Ω => ghostRows n r (pairSamples n (x, y))) (sampleLaw n ν) ∧ (∫ y : Fin n → Ω, ghostRows n r (pairSamples n (x, y)) ∂sampleLaw n ν) = originalRows n r x) := by
  classical
  letI instM : IsProbabilityMeasure (sampleLaw n ν) := inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => ν)))
  letI instP : IsProbabilityMeasure (pairedLaw n ν) := inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => ν.prod ν)))
  letI instMM : IsProbabilityMeasure ((sampleLaw n ν).prod (sampleLaw n ν)) := inferInstanceAs (IsProbabilityMeasure ((Measure.pi (fun _ : Fin n => ν)).prod (Measure.pi (fun _ : Fin n => ν))))
  let good : Set Ω := {a : Ω | Integrable (fun b : Ω => r a b) ν ∧ Integrable (fun b : Ω => r b a) ν ∧ (∫ b : Ω, r a b ∂ν) = 0 ∧ (∫ b : Ω, r b a ∂ν) = 0}
  let basisVector : Fin n → EuclideanSpace ℝ (Fin n) := fun i : Fin n => WithLp.toLp (2 : ℝ≥0∞) (V := Fin n → ℝ) (fun k : Fin n => if k = i then (1 : ℝ) else 0)
  let sampleEval : Fin n → (Fin n → Ω) → Ω := fun (i : Fin n) (x : Fin n → Ω) => x i
  let samplePairEval : Fin n → Fin n → (Fin n → Ω) → Ω × Ω := fun (i j : Fin n) (x : Fin n → Ω) => (x i, x j)
  let corner11 : Fin n → Fin n → (Fin n → Ω × Ω) → Ω × Ω := fun (i j : Fin n) (z : Fin n → Ω × Ω) => ((z i).1, (z j).1)
  let corner21 : Fin n → Fin n → (Fin n → Ω × Ω) → Ω × Ω := fun (i j : Fin n) (z : Fin n → Ω × Ω) => ((z i).2, (z j).1)
  let corner12 : Fin n → Fin n → (Fin n → Ω × Ω) → Ω × Ω := fun (i j : Fin n) (z : Fin n → Ω × Ω) => ((z i).1, (z j).2)
  let corner22 : Fin n → Fin n → (Fin n → Ω × Ω) → Ω × Ω := fun (i j : Fin n) (z : Fin n → Ω × Ω) => ((z i).2, (z j).2)
  let sampleIdentity : Fin n → Ω → Ω := fun (_ : Fin n) (a : Ω) => a
  let pairedIdentity : Fin n → (Ω × Ω) → Ω × Ω := fun (_ : Fin n) (p : Ω × Ω) => p
  let pairedEval : Fin n → (Fin n → Ω × Ω) → Ω × Ω := fun (i : Fin n) (z : Fin n → Ω × Ω) => z i
  let firstProjection : (Ω × Ω) → Ω := Prod.fst
  let secondProjection : (Ω × Ω) → Ω := Prod.snd
  let originalEntry : Fin n → Fin n → (Fin n → Ω) → ℝ := fun (i j : Fin n) (x : Fin n → Ω) => if i = j then 0 else r (x i) (x j)
  let ghostEntry : Fin n → Fin n → (Fin n → Ω × Ω) → ℝ := fun (i j : Fin n) (z : Fin n → Ω × Ω) => ghostMatrix n r z i j
  let sectionEntry : Fin n → Fin n → (Fin n → Ω) → (Fin n → Ω) → ℝ := fun (i j : Fin n) (x y : Fin n → Ω) => ghostMatrix n r (pairSamples n (x, y)) i j
  let originalCoefficient : Fin n → (Fin n → Ω) → ℝ := fun (i : Fin n) (x : Fin n → Ω) => originalRows n r x i
  let ghostCoefficient : Fin n → (Fin n → Ω × Ω) → ℝ := fun (i : Fin n) (z : Fin n → Ω × Ω) => ghostRows n r z i
  let sectionCoefficient : Fin n → (Fin n → Ω) → (Fin n → Ω) → ℝ := fun (i : Fin n) (x y : Fin n → Ω) => ghostRows n r (pairSamples n (x, y)) i
  have hEval (i : Fin n) : MeasurePreserving (sampleEval i) (sampleLaw n ν) ν := by
    simpa only [sampleEval, sampleLaw] using measurePreserving_eval (fun _ : Fin n => ν) i
  have hPEval (i : Fin n) :
      MeasurePreserving (pairedEval i) (pairedLaw n ν) (ν.prod ν) := by
    simpa only [pairedEval, pairedLaw] using
      measurePreserving_eval (fun _ : Fin n => ν.prod ν) i
  have hInd : ProbabilityTheory.iIndepFun sampleEval (sampleLaw n ν) := by
    simpa only [sampleEval, sampleIdentity, sampleLaw] using
      (ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin n => ν)
        (X := sampleIdentity) (fun _ => measurable_id.aemeasurable))
  have hPInd : ProbabilityTheory.iIndepFun pairedEval (pairedLaw n ν) := by
    simpa only [pairedEval, pairedIdentity, pairedLaw] using
      (ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin n => ν.prod ν)
        (X := pairedIdentity) (fun _ => measurable_id.aemeasurable))
  have hPair (i j : Fin n) (hij : i ≠ j) :
      MeasurePreserving (samplePairEval i j) (sampleLaw n ν) (ν.prod ν) := by
    refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
    have hjoint := (hInd.indepFun hij).map_prod_eq_prod_map_map
      (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
    rw [(hEval i).map_eq, (hEval j).map_eq] at hjoint
    exact hjoint
  have hfst (i : Fin n) :
      MeasurePreserving (Prod.fst ∘ pairedEval i) (pairedLaw n ν) ν :=
    (measurePreserving_fst (μ := ν) (ν := ν)).comp (hPEval i)
  have hsnd (i : Fin n) :
      MeasurePreserving (Prod.snd ∘ pairedEval i) (pairedLaw n ν) ν :=
    (measurePreserving_snd (μ := ν) (ν := ν)).comp (hPEval i)
  have h11 (i j : Fin n) (hij : i ≠ j) :
      MeasurePreserving (corner11 i j) (pairedLaw n ν) (ν.prod ν) := by
    refine ⟨((measurable_pi_apply i).fst).prodMk ((measurable_pi_apply j).fst), ?_⟩
    have hjoint := ((hPInd.indepFun hij).comp measurable_fst measurable_fst).map_prod_eq_prod_map_map
      ((measurable_pi_apply i).fst.aemeasurable) ((measurable_pi_apply j).fst.aemeasurable)
    have hfi := (hfst i).map_eq
    have hfj := (hfst j).map_eq
    simp only [Function.comp_def, pairedEval] at hfi hfj hjoint
    rw [hfi, hfj] at hjoint
    simpa only [corner11] using hjoint
  have h21 (i j : Fin n) (hij : i ≠ j) :
      MeasurePreserving (corner21 i j) (pairedLaw n ν) (ν.prod ν) := by
    refine ⟨((measurable_pi_apply i).snd).prodMk ((measurable_pi_apply j).fst), ?_⟩
    have hjoint := ((hPInd.indepFun hij).comp measurable_snd measurable_fst).map_prod_eq_prod_map_map
      ((measurable_pi_apply i).snd.aemeasurable) ((measurable_pi_apply j).fst.aemeasurable)
    have hfi := (hsnd i).map_eq
    have hfj := (hfst j).map_eq
    simp only [Function.comp_def, pairedEval] at hfi hfj hjoint
    rw [hfi, hfj] at hjoint
    simpa only [corner21] using hjoint
  have h12 (i j : Fin n) (hij : i ≠ j) :
      MeasurePreserving (corner12 i j) (pairedLaw n ν) (ν.prod ν) := by
    refine ⟨((measurable_pi_apply i).fst).prodMk ((measurable_pi_apply j).snd), ?_⟩
    have hjoint := ((hPInd.indepFun hij).comp measurable_fst measurable_snd).map_prod_eq_prod_map_map
      ((measurable_pi_apply i).fst.aemeasurable) ((measurable_pi_apply j).snd.aemeasurable)
    have hfi := (hfst i).map_eq
    have hfj := (hsnd j).map_eq
    simp only [Function.comp_def, pairedEval] at hfi hfj hjoint
    rw [hfi, hfj] at hjoint
    simpa only [corner12] using hjoint
  have h22 (i j : Fin n) (hij : i ≠ j) :
      MeasurePreserving (corner22 i j) (pairedLaw n ν) (ν.prod ν) := by
    refine ⟨((measurable_pi_apply i).snd).prodMk ((measurable_pi_apply j).snd), ?_⟩
    have hjoint := ((hPInd.indepFun hij).comp measurable_snd measurable_snd).map_prod_eq_prod_map_map
      ((measurable_pi_apply i).snd.aemeasurable) ((measurable_pi_apply j).snd.aemeasurable)
    have hfi := (hsnd i).map_eq
    have hfj := (hsnd j).map_eq
    simp only [Function.comp_def, pairedEval] at hfi hfj hjoint
    rw [hfi, hfj] at hjoint
    simpa only [corner22] using hjoint
  have hOriginalEntry (i j : Fin n) : Integrable (originalEntry i j) (sampleLaw n ν) := by
    by_cases hij : i = j
    · subst j
      simpa only [originalEntry, ite_true] using
        (integrable_const (0 : ℝ) : Integrable (fun _ : Fin n → Ω => (0 : ℝ)) (sampleLaw n ν))
    · simpa only [originalEntry, ite_eq_right hij, Function.comp_def,
        Function.uncurry, samplePairEval] using (hPair i j hij).integrable_comp_of_integrable hr1
  have hGhostEntry (i j : Fin n) : Integrable (ghostEntry i j) (pairedLaw n ν) := by
    by_cases hij : i = j
    · subst j
      simpa only [ghostEntry, ghostMatrix, ite_true] using
        (integrable_const (0 : ℝ) : Integrable (fun _ : Fin n → Ω × Ω => (0 : ℝ)) (pairedLaw n ν))
    · apply (((((h11 i j hij).integrable_comp_of_integrable hr1).sub
        ((h21 i j hij).integrable_comp_of_integrable hr1)).sub
        ((h12 i j hij).integrable_comp_of_integrable hr1)).add
        ((h22 i j hij).integrable_comp_of_integrable hr1)).congr
      filter_upwards with z
      simp only [ghostEntry, ghostMatrix, ite_eq_right hij, Function.comp_def,
        Function.uncurry, corner11, corner21, corner12, corner22,
        Pi.sub_apply, Pi.add_apply]
  have hOriginalCoefficient (i : Fin n) : Integrable (originalCoefficient i) (sampleLaw n ν) := by
    simpa only [originalCoefficient, originalRows, PiLp.toLp_apply, originalEntry] using
      integrable_finsetSum Finset.univ (fun j _ => hOriginalEntry i j)
  have hGhostCoefficient (i : Fin n) : Integrable (ghostCoefficient i) (pairedLaw n ν) := by
    simpa only [ghostCoefficient, ghostRows, rowAction_apply, one_mul, ghostEntry] using
      integrable_finsetSum Finset.univ (fun j _ => hGhostEntry i j)
  have hBasisRepr (v : EuclideanSpace ℝ (Fin n)) :
      v = ∑ i : Fin n, v i • basisVector i := by
    apply PiLp.ext
    intro k
    change WithLp.ofLp v k = WithLp.ofLp (∑ i : Fin n, v i • basisVector i) k
    rw [WithLp.ofLp_sum]
    simp only [Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, basisVector,
      WithLp.ofLp_toLp, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp [eq_comm]
  have hOriginal : Integrable (originalRows n r) (sampleLaw n ν) := by
    apply (integrable_finsetSum Finset.univ
      (fun i _ => (hOriginalCoefficient i).smul_const (basisVector i))).congr
    filter_upwards with x
    exact (hBasisRepr (originalRows n r x)).symm
  have hGhost : Integrable (ghostRows n r) (pairedLaw n ν) := by
    apply (integrable_finsetSum Finset.univ
      (fun i _ => (hGhostCoefficient i).smul_const (basisVector i))).congr
    filter_upwards with z
    exact (hBasisRepr (ghostRows n r z)).symm
  have hGood : ∀ᵐ a : Ω ∂ν, a ∈ good := by
    filter_upwards [hr1.prod_right_ae, hr1.prod_left_ae, hcR, hcL] with a hright hleft hzeroR hzeroL
    exact ⟨hright, hleft, hzeroR, hzeroL⟩
  have hGoodSample : ∀ᵐ x : Fin n → Ω ∂sampleLaw n ν, ∀ i : Fin n, x i ∈ good := by
    rw [ae_all_iff]
    intro i
    exact (hEval i).quasiMeasurePreserving.ae hGood
  have hIntegralKernel : (∫ p : Ω × Ω, Function.uncurry r p ∂ν.prod ν) = 0 := by
    rw [integral_prod _ hr1]
    simpa only [Function.uncurry, integral_zero] using integral_congr_ae hcR
  have hEvalIntegral (f : Ω → ℝ) (hf : Integrable f ν) (i : Fin n) :
      (∫ y : Fin n → Ω, f (sampleEval i y) ∂sampleLaw n ν) = ∫ a : Ω, f a ∂ν := by
    calc
      (∫ y : Fin n → Ω, f (sampleEval i y) ∂sampleLaw n ν) =
          ∫ a : Ω, f a ∂Measure.map (sampleEval i) (sampleLaw n ν) := by
            symm
            apply integral_map (hEval i).measurable.aemeasurable
            rw [(hEval i).map_eq]
            exact hf.aestronglyMeasurable
      _ = ∫ a : Ω, f a ∂ν := by rw [(hEval i).map_eq]
  have hPairIntegral (i j : Fin n) (hij : i ≠ j) :
      (∫ y : Fin n → Ω, r (y i) (y j) ∂sampleLaw n ν) = 0 := by
    calc
      (∫ y : Fin n → Ω, r (y i) (y j) ∂sampleLaw n ν) =
          ∫ p : Ω × Ω, Function.uncurry r p ∂Measure.map (samplePairEval i j) (sampleLaw n ν) :=
        (integral_map_of_stronglyMeasurable (hPair i j hij).measurable hr.stronglyMeasurable).symm
      _ = 0 := by rw [(hPair i j hij).map_eq]; exact hIntegralKernel
  refine ⟨hOriginal, hGhost, ?_⟩
  filter_upwards [hGoodSample] with x hx
  let sectionGhost : (Fin n → Ω) → EuclideanSpace ℝ (Fin n) := fun y : Fin n → Ω => ghostRows n r (pairSamples n (x, y))
  have hSectionEntry (i j : Fin n) : Integrable (sectionEntry i j x) (sampleLaw n ν) := by
    by_cases hij : i = j
    · subst j
      simpa only [sectionEntry, ghostMatrix, ite_true] using
        (integrable_const (0 : ℝ) : Integrable (fun _ : Fin n → Ω => (0 : ℝ)) (sampleLaw n ν))
    · have hconst : Integrable (fun _ : Fin n → Ω => r (x i) (x j)) (sampleLaw n ν) :=
        integrable_const _
      have h10 := (hEval i).integrable_comp_of_integrable (hx j).2.1
      have h01 := (hEval j).integrable_comp_of_integrable (hx i).1
      have h00 := (hPair i j hij).integrable_comp_of_integrable hr1
      apply (((hconst.sub h10).sub h01).add h00).congr
      filter_upwards with y
      simp only [sectionEntry, ghostMatrix, ite_eq_right hij, pairSamples,
        Function.comp_def, Function.uncurry, sampleEval, samplePairEval,
        Pi.sub_apply, Pi.add_apply]
  have hSectionMean (i j : Fin n) :
      (∫ y : Fin n → Ω, sectionEntry i j x y ∂sampleLaw n ν) = originalEntry i j x := by
    by_cases hij : i = j
    · subst j
      simp only [sectionEntry, ghostMatrix, originalEntry, ite_true, integral_zero]
    · have hconst : Integrable (fun _ : Fin n → Ω => r (x i) (x j)) (sampleLaw n ν) :=
        integrable_const _
      have h10 := (hEval i).integrable_comp_of_integrable (hx j).2.1
      have h01 := (hEval j).integrable_comp_of_integrable (hx i).1
      have h00 := (hPair i j hij).integrable_comp_of_integrable hr1
      simp only [Function.comp_def, Function.uncurry, sampleEval, samplePairEval] at h10 h01 h00
      simp only [sectionEntry, ghostMatrix, originalEntry, ite_eq_right hij, pairSamples]
      have hAddIntegral := integral_add ((hconst.sub h10).sub h01) h00
      have hSubIntegral := integral_sub (hconst.sub h10) h01
      have hFirstSubIntegral := integral_sub hconst h10
      simp only [Pi.sub_apply, Pi.add_apply] at hAddIntegral hSubIntegral hFirstSubIntegral
      rw [hAddIntegral, hSubIntegral, hFirstSubIntegral]
      have h10Integral := hEvalIntegral _ (hx j).2.1 i
      have h01Integral := hEvalIntegral _ (hx i).1 j
      simp only [sampleEval] at h10Integral h01Integral
      rw [h10Integral, h01Integral,
        hPairIntegral i j hij, (hx j).2.2.2, (hx i).2.2.1]
      simp
  have hSectionCoefficient (i : Fin n) :
      Integrable (sectionCoefficient i x) (sampleLaw n ν) := by
    simpa only [sectionCoefficient, ghostRows, rowAction_apply, one_mul, sectionEntry] using
      integrable_finsetSum Finset.univ (fun j _ => hSectionEntry i j)
  have hSectionCoefficientMean (i : Fin n) :
      (∫ y : Fin n → Ω, sectionCoefficient i x y ∂sampleLaw n ν) = originalCoefficient i x := by
    simp only [sectionCoefficient, ghostRows, rowAction_apply, one_mul,
      originalCoefficient, originalRows, PiLp.toLp_apply]
    change (∫ y : Fin n → Ω, ∑ j : Fin n, sectionEntry i j x y ∂sampleLaw n ν) =
      ∑ j : Fin n, originalEntry i j x
    rw [integral_finsetSum Finset.univ (fun j _ => hSectionEntry i j)]
    exact Finset.sum_congr rfl (fun j _ => hSectionMean i j)
  have hSection : Integrable sectionGhost (sampleLaw n ν) := by
    apply (integrable_finsetSum Finset.univ
      (fun i _ => (hSectionCoefficient i).smul_const (basisVector i))).congr
    filter_upwards with y
    exact (hBasisRepr (sectionGhost y)).symm
  have hVectorMean : (∫ y : Fin n → Ω, sectionGhost y ∂sampleLaw n ν) = originalRows n r x := by
    calc
      (∫ y : Fin n → Ω, sectionGhost y ∂sampleLaw n ν) =
          ∫ y : Fin n → Ω, ∑ i : Fin n, sectionCoefficient i x y • basisVector i ∂sampleLaw n ν :=
        integral_congr_ae (Filter.Eventually.of_forall (fun y => hBasisRepr (sectionGhost y)))
      _ = ∑ i : Fin n, (∫ y : Fin n → Ω, sectionCoefficient i x y ∂sampleLaw n ν) • basisVector i := by
        rw [integral_finsetSum Finset.univ
          (fun i _ => (hSectionCoefficient i).smul_const (basisVector i))]
        exact Finset.sum_congr rfl (fun i _ => integral_smul_const (sectionCoefficient i x) (basisVector i))
      _ = ∑ i : Fin n, originalCoefficient i x • basisVector i := by
        simp only [hSectionCoefficientMean]
      _ = originalRows n r x := (hBasisRepr (originalRows n r x)).symm
  exact ⟨hSection, hVectorMean⟩

theorem norm_integral_rpow_le_integral (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [hμ : IsProbabilityMeasure μ] (G : Ω → EuclideanSpace ℝ (Fin n)) (q : ℝ) (hq : 2 ≤ q) (hG : Integrable G μ) (hGq : Integrable (fun a : Ω => Real.rpow ‖G a‖ q) μ) : Real.rpow ‖∫ a : Ω, G a ∂μ‖ q ≤ ∫ a : Ω, Real.rpow ‖G a‖ q ∂μ := by
  let b : ℝ := 1 / q
  let powerNorm : Ω → ℝ := fun a : Ω => Real.rpow ‖G a‖ q
  let inversePower : ℝ → ℝ := fun t : ℝ => Real.rpow t b
  let nonnegativeHalfLine : Set ℝ := Set.Ici (0 : ℝ)
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hbpos : 0 < b := one_div_pos.mpr hqpos
  have hble : b ≤ 1 := by dsimp [b]; exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) ≤ q)).trans_eq (by norm_num)
  have hcancel : q * b = 1 := by dsimp [b]; exact mul_one_div_cancel hqpos.ne'
  have hInverse (a : Ω) : inversePower (powerNorm a) = ‖G a‖ := by
    dsimp only [inversePower, powerNorm]
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul (norm_nonneg (G a)), hcancel, Real.rpow_one]
  have hconcave : ConcaveOn ℝ nonnegativeHalfLine inversePower := by
    simpa only [nonnegativeHalfLine, inversePower, Real.rpow_eq_pow] using Real.concaveOn_rpow hbpos.le hble
  have hcontinuous : ContinuousOn inversePower nonnegativeHalfLine :=
    (Real.continuous_rpow_const hbpos.le).continuousOn
  have hpowerInt : Integrable powerNorm μ := hGq
  have hcompInt : Integrable (inversePower ∘ powerNorm) μ := by
    apply hG.norm.congr
    exact Filter.Eventually.of_forall (fun a => (hInverse a).symm)
  have hpowerNonneg (a : Ω) : powerNorm a ∈ nonnegativeHalfLine := by
    change 0 ≤ Real.rpow ‖G a‖ q
    simpa only [Real.rpow_eq_pow] using Real.rpow_nonneg (norm_nonneg (G a)) q
  have hmean : (∫ a : Ω, ‖G a‖ ∂μ) ≤ inversePower (∫ a : Ω, powerNorm a ∂μ) := by
    have hjensen : (∫ a : Ω, inversePower (powerNorm a) ∂μ) ≤
        inversePower (∫ a : Ω, powerNorm a ∂μ) :=
      hconcave.le_map_integral (f := powerNorm) hcontinuous isClosed_Ici
        (Filter.Eventually.of_forall hpowerNonneg) hpowerInt hcompInt
    simpa only [Function.comp_def, hInverse] using hjensen
  have hnorm : ‖∫ a : Ω, G a ∂μ‖ ≤ inversePower (∫ a : Ω, powerNorm a ∂μ) :=
    (norm_integral_le_integral_norm G).trans hmean
  have hmeanNonneg : 0 ≤ ∫ a : Ω, powerNorm a ∂μ :=
    integral_nonneg (fun a => Real.rpow_nonneg (norm_nonneg (G a)) q)
  calc
    Real.rpow ‖∫ a : Ω, G a ∂μ‖ q ≤
        Real.rpow (inversePower (∫ a : Ω, powerNorm a ∂μ)) q :=
      Real.rpow_le_rpow (norm_nonneg _) hnorm hqpos.le
    _ = ∫ a : Ω, Real.rpow ‖G a‖ q ∂μ := by
      change Real.rpow (Real.rpow (∫ a : Ω, powerNorm a ∂μ) b) q =
        ∫ a : Ω, powerNorm a ∂μ
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_mul hmeanNonneg, mul_comm b q, hcancel, Real.rpow_one]

theorem ghost_row_qmoment_bound (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (ν : Measure Ω) [hν : IsProbabilityMeasure ν] (r : Ω → Ω → ℝ) (w : Ω → ℝ) (q : ℝ) (hr : Measurable (Function.uncurry r)) (hq : 2 ≤ q) (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a) (hR : ∀ᵐ p : Ω × Ω ∂ν.prod ν, |r p.1 p.2| ≤ w p.1 * w p.2) (hS : Integrable (fun z : Fin n → Ω × Ω => Real.rpow (pairedEnergy n w z) q) (pairedLaw n ν)) : Integrable (fun z : Fin n → Ω × Ω => Real.rpow ‖ghostRows n r z‖ q) (pairedLaw n ν) ∧ (∫ z : Fin n → Ω × Ω, Real.rpow ‖ghostRows n r z‖ q ∂pairedLaw n ν) ≤ Real.rpow ((2 : ℝ) * Real.sqrt q) q * (∫ z : Fin n → Ω × Ω, Real.rpow (pairedEnergy n w z) q ∂pairedLaw n ν) := by
  classical
  have hDeterministic : ∀ (D : Fin n → Fin n → ℝ) (W : Fin n → ℝ) (u : Shao.Path n)
      (hW0 : ∀ i : Fin n, 0 ≤ W i)
      (hD0 : ∀ i j : Fin n, |D i j| ≤ W i * W j)
      (hu : ∀ j : Fin n, |u j| ≤ 1),
      ‖rowAction n D u‖ ≤ Real.sqrt (n : ℝ) * weightEnergy n W := by
    intro D W u hW0 hD0 hu
    let columnNorms : Fin n → ℝ := fun j : Fin n => ‖column n D j‖
    have hColumnEnergy : (∑ j : Fin n, columnNorms j ^ 2) = matrixEnergy n D := by
      simpa only [columnNorms, Shao.OQ6.FiniteHilbertSignMoments.energy] using column_energy_eq n D
    calc
      ‖rowAction n D u‖ ≤ ∑ j : Fin n, ‖u j • column n D j‖ := by
        unfold rowAction
        exact norm_sum_le _ _
      _ = ∑ j : Fin n, |u j| * columnNorms j := by
        simp only [norm_smul, Real.norm_eq_abs, columnNorms]
      _ ≤ ∑ j : Fin n, columnNorms j := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_of_le_one_left (norm_nonneg (column n D j)) (hu j)
      _ = ∑ j : Fin n, (1 : ℝ) * columnNorms j := by simp
      _ ≤ Real.sqrt (∑ j : Fin n, (1 : ℝ) ^ 2) *
          Real.sqrt (∑ j : Fin n, columnNorms j ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : Fin n => (1 : ℝ)) columnNorms
      _ = Real.sqrt (n : ℝ) * Real.sqrt (matrixEnergy n D) := by
        rw [hColumnEnergy]
        simp
      _ ≤ Real.sqrt (n : ℝ) * weightEnergy n W :=
        mul_le_mul_of_nonneg_left (matrix_energy_bound n D W hW0 hD0).2 (Real.sqrt_nonneg _)
  letI instM : IsProbabilityMeasure (sampleLaw n ν) := inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => ν)))
  letI instP : IsProbabilityMeasure (pairedLaw n ν) := inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => ν.prod ν)))
  letI instMM : IsProbabilityMeasure ((sampleLaw n ν).prod (sampleLaw n ν)) := inferInstanceAs (IsProbabilityMeasure ((Measure.pi (fun _ : Fin n => ν)).prod (Measure.pi (fun _ : Fin n => ν))))
  let K : ℝ := (2 : ℝ) * Real.sqrt q
  let S : (Fin n → Ω × Ω) → ℝ := pairedEnergy n w
  let recoverPower : ℝ → ℝ := fun t : ℝ => Real.rpow (max t 0) (1 / q)
  let onePlusPower : (Fin n → Ω × Ω) → ℝ := fun z : Fin n → Ω × Ω => 1 + Real.rpow (pairedEnergy n w z) q
  let f1 : (Fin n → Ω × Ω) → ℝ := fun z : Fin n → Ω × Ω => Real.rpow ‖ghostRows n r z‖ q
  let signedPower : (Fin n → Bool) → (Fin n → Ω × Ω) → ℝ := fun (s : Fin n → Bool) (z : Fin n → Ω × Ω) => Real.rpow ‖rowAction n (ghostMatrix n r z) (signPath n s)‖ q
  let cubePower : (Fin n → Ω × Ω) → ℝ := fun z : Fin n → Ω × Ω => cubeMean n (fun s : Fin n → Bool => signedPower s z)
  let dimensionBound : ℝ := Real.sqrt (n : ℝ)
  let dominatingPower : (Fin n → Ω × Ω) → ℝ := fun z : Fin n → Ω × Ω => Real.rpow dimensionBound q * Real.rpow (pairedEnergy n w z) q
  let scalarPower : ℝ → ℝ := fun t : ℝ => Real.rpow t q
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hq1 : 1 ≤ q := by linarith
  have hinvpos : 0 < 1 / q := one_div_pos.mpr hqpos
  have hSnonneg (z : Fin n → Ω × Ω) : 0 ≤ S z := by
    dsimp only [S, pairedEnergy, weightEnergy]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hRecoverCont : Continuous recoverPower :=
    (Real.continuous_rpow_const hinvpos.le).comp (continuous_id.max continuous_const)
  have hRecover (z : Fin n → Ω × Ω) :
      recoverPower (Real.rpow (S z) q) = S z := by
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
  have hLaw (s : Fin n → Bool) := ghost_row_norm_law n ν r s hr
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
    change |Real.rpow ‖ghostRows n r z‖ q| ≤
      Real.rpow dimensionBound q * Real.rpow (S z) q
    simp only [Real.rpow_eq_pow]
    rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) q)]
    have hb : ‖ghostRows n r z‖ ≤ dimensionBound * S z :=
      hDeterministic (ghostMatrix n r z) (ghostWeight n w z)
        (fun _ : Fin n => (1 : ℝ)) hz.1 hz.2 (by intro j; norm_num)
    calc
      ‖ghostRows n r z‖ ^ q ≤ (dimensionBound * S z) ^ q :=
        Real.rpow_le_rpow (norm_nonneg _) hb hqpos.le
      _ = dimensionBound ^ q * S z ^ q :=
        Real.mul_rpow (Real.sqrt_nonneg (n : ℝ)) (hSnonneg z)
  have hSignedInt (s : Fin n → Bool) : Integrable (signedPower s) (pairedLaw n ν) := by
    apply hDomInt.mono' (hSignedMeas s).aestronglyMeasurable
    filter_upwards [hEnvelope] with z hz
    change |Real.rpow ‖rowAction n (ghostMatrix n r z) (signPath n s)‖ q| ≤
      Real.rpow dimensionBound q * Real.rpow (S z) q
    simp only [Real.rpow_eq_pow]
    rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) q)]
    have hsign (j : Fin n) : |signPath n s j| ≤ 1 := by
      cases hs : s j <;> simp [signPath, signValue, hs]
    have hb := hDeterministic (ghostMatrix n r z) (ghostWeight n w z)
      (signPath n s) hz.1 hz.2 hsign
    calc
      ‖rowAction n (ghostMatrix n r z) (signPath n s)‖ ^ q ≤
          (dimensionBound * S z) ^ q := Real.rpow_le_rpow (norm_nonneg _) hb hqpos.le
      _ = dimensionBound ^ q * S z ^ q :=
        Real.mul_rpow (Real.sqrt_nonneg (n : ℝ)) (hSnonneg z)
  have hScalarMeas : StronglyMeasurable scalarPower :=
    (Real.continuous_rpow_const hqpos.le).stronglyMeasurable
  have hLawIntegral (s : Fin n → Bool) :
      (∫ z : Fin n → Ω × Ω, f1 z ∂pairedLaw n ν) =
        ∫ z : Fin n → Ω × Ω, signedPower s z ∂pairedLaw n ν := by
    calc
      (∫ z : Fin n → Ω × Ω, f1 z ∂pairedLaw n ν) =
          ∫ t : ℝ, scalarPower t ∂Measure.map
            (fun z : Fin n → Ω × Ω => ‖rowAction n (ghostMatrix n r z)
              (fun _ : Fin n => (1 : ℝ))‖) (pairedLaw n ν) :=
        (integral_map_of_stronglyMeasurable (hLaw s).1 hScalarMeas).symm
      _ = ∫ t : ℝ, scalarPower t ∂Measure.map
            (fun z : Fin n → Ω × Ω => ‖rowAction n (ghostMatrix n r z) (signPath n s)‖)
              (pairedLaw n ν) := by rw [(hLaw s).2.2]
      _ = ∫ z : Fin n → Ω × Ω, signedPower s z ∂pairedLaw n ν :=
        integral_map_of_stronglyMeasurable (hLaw s).2.1 hScalarMeas
  have hCubeInt : Integrable cubePower (pairedLaw n ν) := by
    exact (integrable_finsetSum Finset.univ (fun s _ => hSignedInt s)).const_mul ((2 : ℝ) ^ n)⁻¹
  have hCubeNonneg (z : Fin n → Ω × Ω) : 0 ≤ cubePower z := by
    apply mul_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n))
    exact Finset.sum_nonneg (fun s _ => Real.rpow_nonneg (norm_nonneg _) q)
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
    have hbase : Real.rpow (cubePower z) (1 / q) ≤ K * S z := by
      exact finite_matrix_sign_moment_bound n (ghostMatrix n r z) (ghostWeight n w z) q hz.1 hz.2 hq
    calc
      cubePower z = Real.rpow (Real.rpow (cubePower z) (1 / q)) q := by
        simp only [Real.rpow_eq_pow]
        rw [← Real.rpow_mul (hCubeNonneg z), one_div_mul_cancel hqpos.ne', Real.rpow_one]
      _ ≤ Real.rpow (K * S z) q :=
        Real.rpow_le_rpow (Real.rpow_nonneg (hCubeNonneg z) (1 / q)) hbase hqpos.le
      _ = Real.rpow K q * Real.rpow (S z) q :=
        Real.mul_rpow (mul_nonneg (by norm_num) (Real.sqrt_nonneg q)) (hSnonneg z)
  refine ⟨hF1Int, ?_⟩
  calc
    (∫ z : Fin n → Ω × Ω, f1 z ∂pairedLaw n ν) =
        ∫ z : Fin n → Ω × Ω, cubePower z ∂pairedLaw n ν := hCubeIntegral.symm
    _ ≤ ∫ z : Fin n → Ω × Ω, Real.rpow K q * Real.rpow (S z) q ∂pairedLaw n ν :=
      integral_mono_ae hCubeInt (hS.const_mul (Real.rpow K q)) hCubeBound
    _ = Real.rpow K q * (∫ z : Fin n → Ω × Ω, Real.rpow (S z) q ∂pairedLaw n ν) :=
      integral_const_mul _ _

theorem canonical_row_qmoment_bound (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (ν : Measure Ω) [hν : IsProbabilityMeasure ν] (r : Ω → Ω → ℝ) (w : Ω → ℝ) (q : ℝ) (hr : Measurable (Function.uncurry r)) (hr1 : Integrable (Function.uncurry r) (ν.prod ν)) (hcR : ∀ᵐ a : Ω ∂ν, (∫ b : Ω, r a b ∂ν) = 0) (hcL : ∀ᵐ b : Ω ∂ν, (∫ a : Ω, r a b ∂ν) = 0) (hq : 2 ≤ q) (hW : ∀ᵐ a : Ω ∂ν, 0 ≤ w a) (hR : ∀ᵐ p : Ω × Ω ∂ν.prod ν, |r p.1 p.2| ≤ w p.1 * w p.2) (hS : Integrable (fun z : Fin n → Ω × Ω => Real.rpow (pairedEnergy n w z) q) (pairedLaw n ν)) : Integrable (fun x : Fin n → Ω => Real.rpow ‖originalRows n r x‖ q) (sampleLaw n ν) ∧ Real.rpow (∫ x : Fin n → Ω, Real.rpow ‖originalRows n r x‖ q ∂sampleLaw n ν) (1 / q) ≤ (2 : ℝ) * Real.sqrt q * Real.rpow (∫ z : Fin n → Ω × Ω, Real.rpow (pairedEnergy n w z) q ∂pairedLaw n ν) (1 / q) := by
  letI instM : IsProbabilityMeasure (sampleLaw n ν) := inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => ν)))
  letI instP : IsProbabilityMeasure (pairedLaw n ν) := inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => ν.prod ν)))
  letI instMM : IsProbabilityMeasure ((sampleLaw n ν).prod (sampleLaw n ν)) := inferInstanceAs (IsProbabilityMeasure ((Measure.pi (fun _ : Fin n => ν)).prod (Measure.pi (fun _ : Fin n => ν))))
  let pairedGhost : ((Fin n → Ω) × (Fin n → Ω)) → EuclideanSpace ℝ (Fin n) := fun p : (Fin n → Ω) × (Fin n → Ω) => ghostRows n r (pairSamples n p)
  let innerQ : (Fin n → Ω) → ℝ := fun x : Fin n → Ω => ∫ y : Fin n → Ω, Real.rpow ‖pairedGhost (x, y)‖ q ∂sampleLaw n ν
  let rowQ : (Fin n → Ω) → ℝ := fun x : Fin n → Ω => Real.rpow ‖originalRows n r x‖ q
  let K : ℝ := (2 : ℝ) * Real.sqrt q
  let weightQIntegral : ℝ := ∫ z : Fin n → Ω × Ω, Real.rpow (pairedEnergy n w z) q ∂pairedLaw n ν
  let rowQIntegral : ℝ := ∫ x : Fin n → Ω, rowQ x ∂sampleLaw n ν
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hinvpos : 0 < 1 / q := one_div_pos.mpr hqpos
  have hmean := canonical_ghost_mean n ν r hr hr1 hcR hcL
  have hghost := ghost_row_qmoment_bound n ν r w q hr hq hW hR hS
  have hpair := pairSamples_measurePreserving n ν
  have hPairedQ : Integrable
      (fun p : (Fin n → Ω) × (Fin n → Ω) => Real.rpow ‖pairedGhost p‖ q)
      ((sampleLaw n ν).prod (sampleLaw n ν)) :=
    hpair.integrable_comp_of_integrable hghost.1
  have hInnerInt : Integrable innerQ (sampleLaw n ν) := hPairedQ.integral_prod_left
  have hRowMeas : AEStronglyMeasurable rowQ (sampleLaw n ν) :=
    (Real.continuous_rpow_const hqpos.le).comp_aestronglyMeasurable
      hmean.1.norm.aestronglyMeasurable
  have hRowNonneg (x : Fin n → Ω) : 0 ≤ rowQ x :=
    Real.rpow_nonneg (norm_nonneg (originalRows n r x)) q
  have hRowDom : ∀ᵐ x : Fin n → Ω ∂sampleLaw n ν, rowQ x ≤ innerQ x := by
    filter_upwards [hmean.2.2, hPairedQ.prod_right_ae] with x hx hxq
    let sectionGhost : (Fin n → Ω) → EuclideanSpace ℝ (Fin n) := fun y : Fin n → Ω => pairedGhost (x, y)
    have hSection : Integrable sectionGhost (sampleLaw n ν) := hx.1
    have hSectionQ : Integrable
        (fun y : Fin n → Ω => Real.rpow ‖sectionGhost y‖ q) (sampleLaw n ν) := hxq
    have hjensen := norm_integral_rpow_le_integral n (sampleLaw n ν)
      sectionGhost q hq hSection hSectionQ
    change Real.rpow ‖∫ y : Fin n → Ω, sectionGhost y ∂sampleLaw n ν‖ q ≤ innerQ x at hjensen
    rw [show (∫ y : Fin n → Ω, sectionGhost y ∂sampleLaw n ν) = originalRows n r x from hx.2] at hjensen
    exact hjensen
  have hRowInt : Integrable rowQ (sampleLaw n ν) := by
    apply hInnerInt.mono' hRowMeas
    filter_upwards [hRowDom] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hRowNonneg x)] using hx
  have hPairIntegral :
      (∫ p : (Fin n → Ω) × (Fin n → Ω), Real.rpow ‖pairedGhost p‖ q
        ∂(sampleLaw n ν).prod (sampleLaw n ν)) =
      ∫ z : Fin n → Ω × Ω, Real.rpow ‖ghostRows n r z‖ q ∂pairedLaw n ν := by
    calc
      (∫ p : (Fin n → Ω) × (Fin n → Ω), Real.rpow ‖pairedGhost p‖ q
          ∂(sampleLaw n ν).prod (sampleLaw n ν)) =
          ∫ z : Fin n → Ω × Ω, Real.rpow ‖ghostRows n r z‖ q
            ∂Measure.map (pairSamples n) ((sampleLaw n ν).prod (sampleLaw n ν)) := by
        symm
        apply integral_map hpair.measurable.aemeasurable
        rw [hpair.map_eq]
        exact hghost.1.aestronglyMeasurable
      _ = ∫ z : Fin n → Ω × Ω, Real.rpow ‖ghostRows n r z‖ q ∂pairedLaw n ν := by
        rw [hpair.map_eq]
  have hMoment : rowQIntegral ≤ Real.rpow K q * weightQIntegral := by
    calc
      rowQIntegral ≤ ∫ x : Fin n → Ω, innerQ x ∂sampleLaw n ν :=
        integral_mono_ae hRowInt hInnerInt hRowDom
      _ = ∫ p : (Fin n → Ω) × (Fin n → Ω), Real.rpow ‖pairedGhost p‖ q
          ∂(sampleLaw n ν).prod (sampleLaw n ν) := (integral_prod _ hPairedQ).symm
      _ = ∫ z : Fin n → Ω × Ω, Real.rpow ‖ghostRows n r z‖ q ∂pairedLaw n ν := hPairIntegral
      _ ≤ Real.rpow K q * weightQIntegral := hghost.2
  have hRowIntegralNonneg : 0 ≤ rowQIntegral := integral_nonneg hRowNonneg
  have hWeightIntegralNonneg : 0 ≤ weightQIntegral := by
    apply integral_nonneg
    intro z
    apply Real.rpow_nonneg
    dsimp only [pairedEnergy, weightEnergy]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hKNonneg : 0 ≤ K := mul_nonneg (by norm_num) (Real.sqrt_nonneg q)
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

end

end Shao.OQ6.CanonicalDoubleGhostRowMoments
