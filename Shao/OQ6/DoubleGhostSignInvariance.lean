import Shao.OQ6.FiniteMatrixSignEnergy
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.Basic

set_option autoImplicit false

namespace Shao.OQ6.DoubleGhostSignInvariance

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal
open Shao.OQ6.FiniteHilbertSignMoments
open Shao.OQ6.FiniteMatrixSignEnergy

def pairSwap {Ω : Type*} (b : Bool) (p : Ω × Ω) : Ω × Ω := if b then p else (p.2, p.1)

def swapSample (n : ℕ) {Ω : Type*} (s : Fin n → Bool) (z : Fin n → Ω × Ω) : Fin n → Ω × Ω := fun i : Fin n => pairSwap (s i) (z i)

def ghostMatrix (n : ℕ) {Ω : Type*} (r : Ω → Ω → ℝ) (z : Fin n → Ω × Ω) : Fin n → Fin n → ℝ := fun i j : Fin n => if i = j then 0 else r (z i).1 (z j).1 - r (z i).2 (z j).1 - r (z i).1 (z j).2 + r (z i).2 (z j).2

def ghostWeight (n : ℕ) {Ω : Type*} (w : Ω → ℝ) (z : Fin n → Ω × Ω) : Fin n → ℝ := fun i : Fin n => w (z i).1 + w (z i).2

def signLeft (n : ℕ) (s : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) := WithLp.toLp (2 : ℝ≥0∞) (V := Fin n → ℝ) (fun i : Fin n => signValue (s i) * x i)

def pairedLaw (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (ν : Measure Ω) : Measure (Fin n → Ω × Ω) := Measure.pi (fun _ : Fin n => ν.prod ν)

theorem swapSample_involutive (n : ℕ) {Ω : Type*} (s : Fin n → Bool) : Function.Involutive (swapSample n (Ω := Ω) s) := by
  intro z
  funext i
  cases hsi : s i <;> simp [swapSample, pairSwap, hsi]

theorem ghostMatrix_swap (n : ℕ) {Ω : Type*} (r : Ω → Ω → ℝ) (s : Fin n → Bool) (z : Fin n → Ω × Ω) (i : Fin n) (j : Fin n) : ghostMatrix n r (swapSample n s z) i j = signValue (s i) * ghostMatrix n r z i j * signValue (s j) := by
  by_cases hij : i = j
  · subst j
    simp [ghostMatrix]
  · cases hsi : s i <;> cases hsj : s j <;>
      simp [ghostMatrix, hij, swapSample, pairSwap, signValue, hsi, hsj] <;> ring

theorem signLeft_isometry (n : ℕ) (s : Fin n → Bool) : Isometry (signLeft n s) ∧ (∀ x : EuclideanSpace ℝ (Fin n), ‖signLeft n s x‖ = ‖x‖) := by
  have hnorm (x : EuclideanSpace ℝ (Fin n)) : ‖signLeft n s x‖ = ‖x‖ := by
    have hsquare : ‖signLeft n s x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      apply Finset.sum_congr rfl
      intro i hi
      change (signValue (s i) * x i) ^ 2 = (x i) ^ 2
      cases s i <;> simp [signValue]
    nlinarith [norm_nonneg (signLeft n s x), norm_nonneg x]
  refine ⟨?_, hnorm⟩
  apply isometry_iff_dist_eq.2
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  have hsub : signLeft n s x - signLeft n s y = signLeft n s (x - y) := by
    apply PiLp.ext
    intro i
    change signValue (s i) * x i - signValue (s i) * y i =
      signValue (s i) * (x i - y i)
    ring
  rw [hsub, hnorm]

theorem rowAction_swap_spec (n : ℕ) {Ω : Type*} (r : Ω → Ω → ℝ) (s : Fin n → Bool) (z : Fin n → Ω × Ω) : rowAction n (ghostMatrix n r (swapSample n s z)) (fun _ : Fin n => (1 : ℝ)) = signLeft n s (rowAction n (ghostMatrix n r z) (signPath n s)) ∧ ‖rowAction n (ghostMatrix n r (swapSample n s z)) (fun _ : Fin n => (1 : ℝ))‖ = ‖rowAction n (ghostMatrix n r z) (signPath n s)‖ := by
  have hvector :
      rowAction n (ghostMatrix n r (swapSample n s z)) (fun _ : Fin n => (1 : ℝ)) =
        signLeft n s (rowAction n (ghostMatrix n r z) (signPath n s)) := by
    apply PiLp.ext
    intro i
    change (rowAction n (ghostMatrix n r (swapSample n s z))
      (fun _ : Fin n => (1 : ℝ))) i =
        signValue (s i) * (rowAction n (ghostMatrix n r z) (signPath n s)) i
    rw [rowAction_apply, rowAction_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ghostMatrix_swap]
    dsimp only [signPath]
    ring
  refine ⟨hvector, ?_⟩
  rw [hvector]
  exact (signLeft_isometry n s).2 _

theorem ghostMatrix_envelope (n : ℕ) {Ω : Type*} (r : Ω → Ω → ℝ) (w : Ω → ℝ) (z : Fin n → Ω × Ω) (hW : ∀ i : Fin n, 0 ≤ w (z i).1 ∧ 0 ≤ w (z i).2) (hR : ∀ i j : Fin n, i ≠ j → (|r (z i).1 (z j).1| ≤ w (z i).1 * w (z j).1) ∧ (|r (z i).2 (z j).1| ≤ w (z i).2 * w (z j).1) ∧ (|r (z i).1 (z j).2| ≤ w (z i).1 * w (z j).2) ∧ (|r (z i).2 (z j).2| ≤ w (z i).2 * w (z j).2)) : (∀ i : Fin n, 0 ≤ ghostWeight n w z i) ∧ (∀ i j : Fin n, |ghostMatrix n r z i j| ≤ ghostWeight n w z i * ghostWeight n w z j) := by
  refine ⟨?_, ?_⟩
  · intro i
    exact add_nonneg (hW i).1 (hW i).2
  · intro i j
    by_cases hij : i = j
    · subst j
      simpa [ghostMatrix] using (mul_self_nonneg (ghostWeight n w z i))
    · simp only [ghostMatrix, ite_eq_right hij, ghostWeight]
      rcases hR i j hij with ⟨h11, h21, h12, h22⟩
      have hab : |r (z i).1 (z j).1 - r (z i).2 (z j).1| ≤
          |r (z i).1 (z j).1| + |r (z i).2 (z j).1| := abs_sub _ _
      have habc : |r (z i).1 (z j).1 - r (z i).2 (z j).1 - r (z i).1 (z j).2| ≤
          |r (z i).1 (z j).1 - r (z i).2 (z j).1| + |r (z i).1 (z j).2| :=
        abs_sub _ _
      have habcd :
          |r (z i).1 (z j).1 - r (z i).2 (z j).1 - r (z i).1 (z j).2 +
            r (z i).2 (z j).2| ≤
          |r (z i).1 (z j).1 - r (z i).2 (z j).1 - r (z i).1 (z j).2| +
            |r (z i).2 (z j).2| := abs_add_le _ _
      nlinarith

theorem swapSample_measurePreserving (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (ν : Measure Ω) [hν : IsProbabilityMeasure ν] (s : Fin n → Bool) : MeasurePreserving (swapSample n (Ω := Ω) s) (pairedLaw n ν) (pairedLaw n ν) := by
  have hfactor (i : Fin n) :
      MeasurePreserving (pairSwap (s i) : Ω × Ω → Ω × Ω) (ν.prod ν) (ν.prod ν) := by
    cases s i with
    | false =>
      change MeasurePreserving Prod.swap (ν.prod ν) (ν.prod ν)
      exact Measure.measurePreserving_swap (μ := ν) (ν := ν)
    | true =>
      change MeasurePreserving id (ν.prod ν) (ν.prod ν)
      exact MeasurePreserving.id (ν.prod ν)
  have hmap (i : Fin n) : (ν.prod ν).map (pairSwap (s i)) = ν.prod ν :=
    (hfactor i).map_eq
  refine ⟨?_, ?_⟩
  · exact measurable_pi_iff.2 (fun i =>
      (hfactor i).measurable.comp (measurable_pi_apply i))
  · have hpi := Measure.pi_map_pi
      (μ := fun _ : Fin n => ν.prod ν)
      (f := fun i : Fin n => pairSwap (s i))
      (hμ := fun i => by rw [hmap i]; infer_instance)
      (fun i => (hfactor i).aemeasurable)
    change (Measure.pi (fun _ : Fin n => ν.prod ν)).map
      (fun x i => pairSwap (s i) (x i)) = Measure.pi (fun _ : Fin n => ν.prod ν)
    simpa only [hmap] using hpi

theorem ghostMatrix_ae_envelope (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (ν : Measure Ω) [hν : IsProbabilityMeasure ν] (r : Ω → Ω → ℝ) (w : Ω → ℝ) (hW : ∀ᵐ x : Ω ∂ν, 0 ≤ w x) (hR : ∀ᵐ p : Ω × Ω ∂ν.prod ν, |r p.1 p.2| ≤ w p.1 * w p.2) : ∀ᵐ z : Fin n → Ω × Ω ∂pairedLaw n ν, (∀ i : Fin n, 0 ≤ ghostWeight n w z i) ∧ (∀ i j : Fin n, |ghostMatrix n r z i j| ≤ ghostWeight n w z i * ghostWeight n w z j) := by
  unfold pairedLaw
  have hfst (i : Fin n) :
      MeasurePreserving (fun z : Fin n → Ω × Ω => (z i).1) (Measure.pi (fun _ : Fin n => ν.prod ν)) ν :=
    (measurePreserving_fst (μ := ν) (ν := ν)).comp
      (measurePreserving_eval (fun _ : Fin n => ν.prod ν) i)
  have hsnd (i : Fin n) :
      MeasurePreserving (fun z : Fin n → Ω × Ω => (z i).2) (Measure.pi (fun _ : Fin n => ν.prod ν)) ν :=
    (measurePreserving_snd (μ := ν) (ν := ν)).comp
      (measurePreserving_eval (fun _ : Fin n => ν.prod ν) i)
  have hind : ProbabilityTheory.iIndepFun
      (fun (i : Fin n) (z : Fin n → Ω × Ω) => z i) (Measure.pi (fun _ : Fin n => ν.prod ν)) := by
    exact ProbabilityTheory.iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have h11 (i j : Fin n) (hij : i ≠ j) :
      MeasurePreserving (fun z : Fin n → Ω × Ω => ((z i).1, (z j).1))
        (Measure.pi (fun _ : Fin n => ν.prod ν)) (ν.prod ν) := by
    refine ⟨((measurable_pi_apply i).fst).prodMk ((measurable_pi_apply j).fst), ?_⟩
    have hjoint := ((hind.indepFun hij).comp measurable_fst measurable_fst).map_prod_eq_prod_map_map
      ((measurable_pi_apply i).fst.aemeasurable)
      ((measurable_pi_apply j).fst.aemeasurable)
    simpa only [Function.comp_def, (hfst i).map_eq, (hfst j).map_eq] using hjoint
  have h21 (i j : Fin n) (hij : i ≠ j) :
      MeasurePreserving (fun z : Fin n → Ω × Ω => ((z i).2, (z j).1))
        (Measure.pi (fun _ : Fin n => ν.prod ν)) (ν.prod ν) := by
    refine ⟨((measurable_pi_apply i).snd).prodMk ((measurable_pi_apply j).fst), ?_⟩
    have hjoint := ((hind.indepFun hij).comp measurable_snd measurable_fst).map_prod_eq_prod_map_map
      ((measurable_pi_apply i).snd.aemeasurable)
      ((measurable_pi_apply j).fst.aemeasurable)
    simpa only [Function.comp_def, (hsnd i).map_eq, (hfst j).map_eq] using hjoint
  have h12 (i j : Fin n) (hij : i ≠ j) :
      MeasurePreserving (fun z : Fin n → Ω × Ω => ((z i).1, (z j).2))
        (Measure.pi (fun _ : Fin n => ν.prod ν)) (ν.prod ν) := by
    refine ⟨((measurable_pi_apply i).fst).prodMk ((measurable_pi_apply j).snd), ?_⟩
    have hjoint := ((hind.indepFun hij).comp measurable_fst measurable_snd).map_prod_eq_prod_map_map
      ((measurable_pi_apply i).fst.aemeasurable)
      ((measurable_pi_apply j).snd.aemeasurable)
    simpa only [Function.comp_def, (hfst i).map_eq, (hsnd j).map_eq] using hjoint
  have h22 (i j : Fin n) (hij : i ≠ j) :
      MeasurePreserving (fun z : Fin n → Ω × Ω => ((z i).2, (z j).2))
        (Measure.pi (fun _ : Fin n => ν.prod ν)) (ν.prod ν) := by
    refine ⟨((measurable_pi_apply i).snd).prodMk ((measurable_pi_apply j).snd), ?_⟩
    have hjoint := ((hind.indepFun hij).comp measurable_snd measurable_snd).map_prod_eq_prod_map_map
      ((measurable_pi_apply i).snd.aemeasurable)
      ((measurable_pi_apply j).snd.aemeasurable)
    simpa only [Function.comp_def, (hsnd i).map_eq, (hsnd j).map_eq] using hjoint
  have hwAll : ∀ᵐ z : Fin n → Ω × Ω ∂Measure.pi (fun _ : Fin n => ν.prod ν),
      ∀ i : Fin n, 0 ≤ w (z i).1 ∧ 0 ≤ w (z i).2 := by
    rw [ae_all_iff]
    intro i
    exact ((hfst i).quasiMeasurePreserving.ae hW).and
      ((hsnd i).quasiMeasurePreserving.ae hW)
  have hrAll : ∀ᵐ z : Fin n → Ω × Ω ∂Measure.pi (fun _ : Fin n => ν.prod ν),
      ∀ i j : Fin n, i ≠ j →
        (|r (z i).1 (z j).1| ≤ w (z i).1 * w (z j).1) ∧
        (|r (z i).2 (z j).1| ≤ w (z i).2 * w (z j).1) ∧
        (|r (z i).1 (z j).2| ≤ w (z i).1 * w (z j).2) ∧
        (|r (z i).2 (z j).2| ≤ w (z i).2 * w (z j).2) := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ hne => (hne hij).elim)
    · filter_upwards [(h11 i j hij).quasiMeasurePreserving.ae hR,
        (h21 i j hij).quasiMeasurePreserving.ae hR,
        (h12 i j hij).quasiMeasurePreserving.ae hR,
        (h22 i j hij).quasiMeasurePreserving.ae hR] with z hz11 hz21 hz12 hz22
      exact fun _ => ⟨hz11, hz21, hz12, hz22⟩
  filter_upwards [hwAll, hrAll] with z hwz hrz
  exact ghostMatrix_envelope n r w z hwz hrz

theorem ghost_row_norm_law (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (ν : Measure Ω) [hν : IsProbabilityMeasure ν] (r : Ω → Ω → ℝ) (s : Fin n → Bool) (hr : Measurable (Function.uncurry r)) : Measurable (fun z : Fin n → Ω × Ω => ‖rowAction n (ghostMatrix n r z) (fun _ : Fin n => (1 : ℝ))‖) ∧ Measurable (fun z : Fin n → Ω × Ω => ‖rowAction n (ghostMatrix n r z) (signPath n s)‖) ∧ Measure.map (fun z : Fin n → Ω × Ω => ‖rowAction n (ghostMatrix n r z) (fun _ : Fin n => (1 : ℝ))‖) (pairedLaw n ν) = Measure.map (fun z : Fin n → Ω × Ω => ‖rowAction n (ghostMatrix n r z) (signPath n s)‖) (pairedLaw n ν) := by
  have hentry (i j : Fin n) :
      Measurable (fun z : Fin n → Ω × Ω => ghostMatrix n r z i j) := by
    by_cases hij : i = j
    · simp only [ghostMatrix, ite_eq_left hij]
      exact measurable_const
    · simp only [ghostMatrix, ite_eq_right hij]
      exact (((hr.comp (((measurable_pi_apply i).fst).prodMk
        ((measurable_pi_apply j).fst))).sub
          (hr.comp (((measurable_pi_apply i).snd).prodMk
            ((measurable_pi_apply j).fst)))).sub
          (hr.comp (((measurable_pi_apply i).fst).prodMk
            ((measurable_pi_apply j).snd)))).add
          (hr.comp
            ((show Measurable (fun z : Fin n → Ω × Ω => (z i).2) from
                (measurable_pi_apply i).snd).prodMk
              (show Measurable (fun z : Fin n → Ω × Ω => (z j).2) from
                (measurable_pi_apply j).snd)))
  have hrow (u : Shao.Path n) (i : Fin n) :
      Measurable (fun z : Fin n → Ω × Ω =>
        ∑ j : Fin n, u j * ghostMatrix n r z i j) :=
    Finset.measurable_sum Finset.univ (fun j _ => (hentry i j).const_mul (u j))
  have hnorm (u : Shao.Path n) :
      Measurable (fun z : Fin n → Ω × Ω => ‖rowAction n (ghostMatrix n r z) u‖) := by
    have hsquare : Measurable (fun z : Fin n → Ω × Ω =>
        ∑ i : Fin n, (∑ j : Fin n, u j * ghostMatrix n r z i j) ^ 2) :=
      Finset.measurable_sum Finset.univ (fun i _ => (hrow u i).pow_const 2)
    have hcoordinates :
        (fun z : Fin n → Ω × Ω => ‖rowAction n (ghostMatrix n r z) u‖) =
          (fun z : Fin n → Ω × Ω => Real.sqrt
            (∑ i : Fin n, (∑ j : Fin n, u j * ghostMatrix n r z i j) ^ 2)) := by
      funext z
      rw [EuclideanSpace.norm_eq]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [rowAction_apply]
      simpa only [Real.norm_eq_abs] using
        (sq_abs (∑ j : Fin n, u j * ghostMatrix n r z i j))
    rw [hcoordinates]
    exact Real.continuous_sqrt.measurable.comp hsquare
  refine ⟨hnorm (fun _ : Fin n => (1 : ℝ)), hnorm (signPath n s), ?_⟩
  calc
    Measure.map (fun z : Fin n → Ω × Ω =>
        ‖rowAction n (ghostMatrix n r z) (fun _ : Fin n => (1 : ℝ))‖) (pairedLaw n ν) =
      Measure.map (fun z : Fin n → Ω × Ω =>
        ‖rowAction n (ghostMatrix n r z) (fun _ : Fin n => (1 : ℝ))‖)
          (Measure.map (swapSample n (Ω := Ω) s) (pairedLaw n ν)) := by
            rw [(swapSample_measurePreserving n ν s).map_eq]
    _ = Measure.map
        ((fun z : Fin n → Ω × Ω =>
          ‖rowAction n (ghostMatrix n r z) (fun _ : Fin n => (1 : ℝ))‖) ∘
            swapSample n (Ω := Ω) s) (pairedLaw n ν) :=
      Measure.map_map (hnorm (fun _ : Fin n => (1 : ℝ)))
        (swapSample_measurePreserving n ν s).measurable
    _ = Measure.map (fun z : Fin n → Ω × Ω =>
        ‖rowAction n (ghostMatrix n r z) (signPath n s)‖) (pairedLaw n ν) :=
      Measure.map_congr (Filter.Eventually.of_forall
        (fun z => (rowAction_swap_spec n r s z).2))

end

end Shao.OQ6.DoubleGhostSignInvariance
