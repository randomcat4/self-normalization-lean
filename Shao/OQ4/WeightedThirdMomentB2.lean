import Shao.Basic.FinitePath
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FunProp

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators

namespace Shao.OQ4.WeightedThirdMoment

private def signValue (b : Bool) : ℝ :=
  cond b 1 (-1)

private noncomputable def signAverage (m : ℕ)
    (F : (Fin m → Bool) → ℝ) : ℝ :=
  ((2 : ℝ) ^ m)⁻¹ * ∑ ε : Fin m → Bool, F ε

private def swapCopies (m : ℕ) (ε : Fin m → Bool)
    (p : Shao.Path m × Shao.Path m) : Shao.Path m × Shao.Path m :=
  ((fun i => cond (ε i) (p.1 i) (p.2 i)),
   (fun i => cond (ε i) (p.2 i) (p.1 i)))

private theorem finite_sum_abs_cube_le (m : ℕ) (u : Fin m → ℝ) :
    |∑ i : Fin m, u i| ^ 3 ≤
      (m : ℝ) ^ 2 * ∑ i : Fin m, |u i| ^ 3 := by
  classical
  let R : ℝ := ∑ i : Fin m, |u i|
  let Q : ℝ := ∑ i : Fin m, |u i| ^ 2
  let T : ℝ := ∑ i : Fin m, |u i| ^ 3
  have hR : 0 ≤ R := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => pow_nonneg (abs_nonneg _) _
  have hN : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have h1 : R ^ 2 ≤ (m : ℝ) * Q := by
    simpa [R, Q] using
      (Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
        (r := fun i : Fin m => |u i|)
        (f := fun _ : Fin m => (1 : ℝ))
        (g := fun i : Fin m => |u i| ^ 2)
        (fun _ _ => by positivity) (fun _ _ => sq_nonneg _)
        (fun _ _ => by simp))
  have h2 : Q ^ 2 ≤ R * T := by
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun _ _ => abs_nonneg _) (fun _ _ => pow_nonneg (abs_nonneg _) _)
      (fun i _ => (show (|u i| ^ 2) ^ 2 ≤ |u i| * |u i| ^ 3 by nlinarith))
  have h3 : R ^ 3 ≤ (m : ℝ) ^ 2 * T := by
    by_cases hz : R = 0
    · simp [hz, mul_nonneg (sq_nonneg (m : ℝ)) hT]
    have hp : 0 < R := lt_of_le_of_ne hR (Ne.symm hz)
    have hh1 := mul_le_mul h1 h1 (sq_nonneg R) (mul_nonneg hN hQ)
    have hh2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (m : ℝ))
    by_contra hn
    have hn' := mul_pos hp (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith [hh1, hh2]
  calc
    |∑ i : Fin m, u i| ^ 3 ≤ R ^ 3 := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := h3

private theorem integrable_fin_sum_abs_cube
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (m : ℕ) (f : Fin m → α → ℝ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (h3 : ∀ i, Integrable (fun a => |f i a| ^ 3) μ) :
    Integrable (fun a => |∑ i : Fin m, f i a| ^ 3) μ := by
  classical
  have hg : Integrable (fun a => (m : ℝ) ^ 2 * ∑ i : Fin m, |f i a| ^ 3) μ :=
    (integrable_finsetSum Finset.univ (fun i _ => h3 i)).const_mul _
  apply hg.mono_nonneg
  · exact (continuous_abs.pow 3).comp_aestronglyMeasurable
      (by simpa only [← Finset.sum_apply] using
        Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => hf i))
  · exact Filter.Eventually.of_forall fun _ => pow_nonneg (abs_nonneg _) _
  · exact Filter.Eventually.of_forall fun a => finite_sum_abs_cube_le m (fun i => f i a)

private theorem integrable_of_abs_cube
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : AEStronglyMeasurable f μ)
    (h3 : Integrable (fun a => |f a| ^ 3) μ) :
    Integrable f μ := by
  have hn : Integrable (fun a => ‖f a‖ ^ 1) μ :=
    integrable_norm_pow_of_le hf (by norm_num : (1 : ℕ) ≤ 3) (by simpa using h3)
  apply (integrable_norm_iff hf).mp
  simpa using hn

private theorem abs_cube_sub_le (x y : ℝ) :
    |x - y| ^ 3 ≤ 4 * (|x| ^ 3 + |y| ^ 3) := by
  have htri : |x - y| ≤ |x| + |y| := abs_sub x y
  have hc : |x - y| ^ 3 ≤ (|x| + |y|) ^ 3 := by gcongr
  have hs := mul_nonneg (add_nonneg (abs_nonneg x) (abs_nonneg y))
    (sq_nonneg (|x| - |y|))
  nlinarith

private theorem abs_cube_tangent (t y : ℝ) :
    |t| ^ 3 + 3 * t * |t| * (y - t) ≤ |y| ^ 3 := by
  have hp (a b : ℝ) (ha : 0 ≤ a) :
      |a| ^ 3 + 3 * a * |a| * (b - a) ≤ |b| ^ 3 := by
    rw [abs_of_nonneg ha]
    by_cases hb : 0 ≤ b
    · rw [abs_of_nonneg hb]
      have hs := mul_nonneg (sq_nonneg (b - a)) (by linarith : 0 ≤ b + 2 * a)
      nlinarith
    · rw [abs_of_neg (lt_of_not_ge hb)]
      have hba : 0 ≤ -b := le_of_lt (neg_pos.mpr (lt_of_not_ge hb))
      nlinarith [mul_nonneg (sq_nonneg a) hba, pow_nonneg ha 3, pow_nonneg hba 3]
  by_cases ht : 0 ≤ t
  · exact hp t y ht
  · have hh := hp (-t) (-y) (by linarith)
    simp only [abs_neg] at hh
    nlinarith [hh]

private theorem abs_cube_integral_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (hf : Integrable f μ)
    (h3 : Integrable (fun a => |f a| ^ 3) μ) :
    |∫ a, f a ∂μ| ^ 3 ≤ ∫ a, |f a| ^ 3 ∂μ := by
  let t : ℝ := ∫ a, f a ∂μ
  have hl : Integrable (fun a => |t| ^ 3 + 3 * t * |t| * (f a - t)) μ :=
    (integrable_const _).add ((hf.sub (integrable_const _)).const_mul _)
  have hi := integral_mono hl h3 (fun a => abs_cube_tangent t (f a))
  have heq : (∫ a, |t| ^ 3 + 3 * t * |t| * (f a - t) ∂μ) = |t| ^ 3 := by
    have hr : Integrable (fun a => 3 * t * |t| * (f a - t)) μ :=
      (hf.sub (integrable_const t)).const_mul _
    calc
      _ = (∫ a, |t| ^ 3 ∂μ) + ∫ a, 3 * t * |t| * (f a - t) ∂μ :=
        integral_add (integrable_const _) hr
      _ = _ := by
        rw [integral_const_mul, integral_sub hf (integrable_const t)]
        simp [t]
  rw [heq] at hi
  exact hi

private theorem signAverage_succ
    (m : ℕ) (F : (Fin (m + 1) → Bool) → ℝ) :
    signAverage (m + 1) F =
      (signAverage m (fun ε => F (Fin.cons false ε)) +
        signAverage m (fun ε => F (Fin.cons true ε))) / 2 := by
  classical
  have hs : (∑ ε : Fin (m + 1) → Bool, F ε) =
      (∑ ε : Fin m → Bool, F (Fin.cons true ε)) +
        ∑ ε : Fin m → Bool, F (Fin.cons false ε) := by
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Bool)).sum_comp]
    simp only [Fintype.sum_prod_type, Fin.consEquiv_apply, Fintype.sum_bool]
  simp only [signAverage, hs, pow_succ]
  ring

private theorem signAverage_second_moment (m : ℕ) (u : Fin m → ℝ) :
    signAverage m (fun ε => (∑ i : Fin m, u i * signValue (ε i)) ^ 2) =
      ∑ i : Fin m, u i ^ 2 := by
  classical
  induction m with
  | zero => simp [signAverage]
  | succ m ih =>
    let V : (Fin m → Bool) → ℝ := fun ε => ∑ i : Fin m, u i.succ * signValue (ε i)
    have avc (k : ℝ) : signAverage m (fun _ => k) = k := by
      simp [signAverage, Nat.cast_pow]
    have ava (f g : (Fin m → Bool) → ℝ) :
        signAverage m (fun ε => f ε + g ε) = signAverage m f + signAverage m g := by
      simp [signAverage, Finset.sum_add_distrib, mul_add]
    have hs (b : Bool) (ε : Fin m → Bool) :
        (∑ i : Fin (m + 1), u i * signValue ((Fin.cons b ε : Fin (m + 1) → Bool) i)) =
          u 0 * signValue b + V ε := by simp [Fin.sum_univ_succ, V]
    rw [signAverage_succ]
    simp_rw [hs]
    simp only [signValue, Bool.cond_false, Bool.cond_true, mul_neg, mul_one]
    calc
      _ = signAverage m (fun ε => u 0 ^ 2 + (V ε) ^ 2) := by
        unfold signAverage
        rw [← mul_add, ← Finset.sum_add_distrib]
        simp_rw [show ∀ ε, (-u 0 + V ε) ^ 2 + (u 0 + V ε) ^ 2 =
          2 * (u 0 ^ 2 + (V ε) ^ 2) from fun ε => by ring]
        rw [← Finset.mul_sum]
        ring
      _ = u 0 ^ 2 + signAverage m (fun ε => (V ε) ^ 2) := by rw [ava, avc]
      _ = _ := by rw [ih (fun i => u i.succ), Fin.sum_univ_succ]

private theorem signAverage_fourth_moment (m : ℕ) (u : Fin m → ℝ) :
    signAverage m (fun ε => (∑ i : Fin m, u i * signValue (ε i)) ^ 4) =
      3 * (∑ i : Fin m, u i ^ 2) ^ 2 - 2 * ∑ i : Fin m, u i ^ 4 := by
  classical
  induction m with
  | zero => simp [signAverage]
  | succ m ih =>
    let V : (Fin m → Bool) → ℝ := fun ε => ∑ i : Fin m, u i.succ * signValue (ε i)
    have avc (k : ℝ) : signAverage m (fun _ => k) = k := by
      simp [signAverage, Nat.cast_pow]
    have ava (f g : (Fin m → Bool) → ℝ) :
        signAverage m (fun ε => f ε + g ε) = signAverage m f + signAverage m g := by
      simp [signAverage, Finset.sum_add_distrib, mul_add]
    have avm (k : ℝ) (f : (Fin m → Bool) → ℝ) :
        signAverage m (fun ε => k * f ε) = k * signAverage m f := by
      simp [signAverage, Finset.mul_sum, mul_left_comm]
    have hs (b : Bool) (ε : Fin m → Bool) :
        (∑ i : Fin (m + 1), u i * signValue ((Fin.cons b ε : Fin (m + 1) → Bool) i)) =
          u 0 * signValue b + V ε := by simp [Fin.sum_univ_succ, V]
    rw [signAverage_succ]
    simp_rw [hs]
    simp only [signValue, Bool.cond_false, Bool.cond_true, mul_neg, mul_one]
    calc
      _ = signAverage m (fun ε => u 0 ^ 4 + 6 * u 0 ^ 2 * (V ε) ^ 2 + (V ε) ^ 4) := by
        unfold signAverage
        rw [← mul_add, ← Finset.sum_add_distrib]
        simp_rw [show ∀ ε, (-u 0 + V ε) ^ 4 + (u 0 + V ε) ^ 4 =
          2 * (u 0 ^ 4 + 6 * u 0 ^ 2 * (V ε) ^ 2 + (V ε) ^ 4) from fun ε => by ring]
        rw [← Finset.mul_sum]
        ring
      _ = u 0 ^ 4 + 6 * u 0 ^ 2 * signAverage m (fun ε => (V ε) ^ 2) +
          signAverage m (fun ε => (V ε) ^ 4) := by rw [ava, ava, avc, avm]
      _ = _ := by
        rw [signAverage_second_moment m (fun i => u i.succ), ih (fun i => u i.succ)]
        simp only [Fin.sum_univ_succ]
        ring

private theorem signAverage_abs_cube_le (m : ℕ) (u : Fin m → ℝ) :
    signAverage m (fun ε => |∑ i : Fin m, u i * signValue (ε i)| ^ 3) ≤
      2 * (Real.sqrt (∑ i : Fin m, u i ^ 2)) ^ 3 := by
  classical
  let q : ℝ := ∑ i : Fin m, u i ^ 2
  let t : ℝ := Real.sqrt q
  let V : (Fin m → Bool) → ℝ := fun ε => ∑ i : Fin m, u i * signValue (ε i)
  have hq : 0 ≤ q := Finset.sum_nonneg fun i _ => sq_nonneg _
  have ht : t ^ 2 = q := Real.sq_sqrt hq
  by_cases hz : q = 0
  · have hu (i : Fin m) : u i = 0 := by
      have hi : u i ^ 2 ≤ q := Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
      nlinarith [sq_nonneg (u i)]
    simp [hu, signAverage]
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
  have htp : 0 < t := Real.sqrt_pos.mpr hqp
  have hy (ε : Fin m → Bool) :
      2 * t * |V ε| ^ 3 ≤ (V ε) ^ 4 + q * (V ε) ^ 2 := by
    have h4 : |V ε| ^ 4 = (V ε) ^ 4 := by
      calc
        _ = (|V ε| ^ 2) ^ 2 := by ring
        _ = ((V ε) ^ 2) ^ 2 := by rw [sq_abs]
        _ = _ := by ring
    have hs := mul_nonneg (sq_nonneg |V ε|) (sq_nonneg (|V ε| - t))
    nlinarith [sq_abs (V ε), h4]
  have hi : 0 ≤ ((2 : ℝ) ^ m)⁻¹ := by positivity
  have hav :
      2 * t * signAverage m (fun ε => |V ε| ^ 3) ≤
        signAverage m (fun ε => (V ε) ^ 4) + q * signAverage m (fun ε => (V ε) ^ 2) := by
    have hh := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (s := Finset.univ) (fun ε _ => hy ε)) hi
    convert hh using 1 <;>
      simp only [signAverage, Finset.sum_add_distrib, ← Finset.mul_sum] <;> ring
  have h2 : signAverage m (fun ε => (V ε) ^ 2) = q := signAverage_second_moment m u
  have h4 : signAverage m (fun ε => (V ε) ^ 4) ≤ 3 * q ^ 2 := by
    rw [show signAverage m (fun ε => (V ε) ^ 4) =
        3 * q ^ 2 - 2 * ∑ i : Fin m, u i ^ 4 from signAverage_fourth_moment m u]
    have hp : 0 ≤ ∑ i : Fin m, u i ^ 4 := Finset.sum_nonneg fun i _ => by positivity
    linarith
  change signAverage m (fun ε => |V ε| ^ 3) ≤ 2 * t ^ 3
  rw [h2] at hav
  have hscale : 4 * q ^ 2 = (2 * t) * (2 * t ^ 3) := by rw [← ht]; ring
  have hbound : 2 * t * signAverage m (fun ε => |V ε| ^ 3) ≤ (2 * t) * (2 * t ^ 3) := by
    rw [← hscale]
    nlinarith [hav, h4]
  by_contra hn
  have hn' := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) htp)
    (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith [hbound]

private theorem weighted_square_cube_le (m : ℕ) (c z : Fin m → ℝ) :
    (Real.sqrt (∑ i : Fin m, c i ^ 2 * z i ^ 2)) ^ 3 ≤
      Real.sqrt (∑ i : Fin m, c i ^ 2) *
        ∑ i : Fin m, c i ^ 2 * |z i| ^ 3 := by
  classical
  let A : ℝ := ∑ i : Fin m, c i ^ 2
  let Q : ℝ := ∑ i : Fin m, c i ^ 2 * z i ^ 2
  let L : ℝ := ∑ i : Fin m, c i ^ 2 * |z i|
  let R : ℝ := ∑ i : Fin m, c i ^ 2 * |z i| ^ 3
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hL : 0 ≤ L := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (abs_nonneg _)
  have hR : 0 ≤ R := Finset.sum_nonneg fun i _ => by positivity
  have h1 : L ^ 2 ≤ A * Q := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun i _ => sq_nonneg (c i))
      (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    intro i _
    rw [mul_pow, sq_abs]
    nlinarith
  have h2 : Q ^ 2 ≤ L * R := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun i _ => mul_nonneg (sq_nonneg _) (abs_nonneg _))
      (fun i _ => by positivity)
    intro i _
    have hz : |z i| ^ 2 = z i ^ 2 := sq_abs _
    calc
      _ = (c i ^ 2) ^ 2 * (z i ^ 2) ^ 2 := by ring
      _ = (c i ^ 2) ^ 2 * (|z i| ^ 2) ^ 2 := by rw [hz]
      _ ≤ _ := by nlinarith
  change (Real.sqrt Q) ^ 3 ≤ Real.sqrt A * R
  by_cases hz : Q = 0
  · rw [hz, Real.sqrt_zero]
    simpa using mul_nonneg (Real.sqrt_nonneg A) hR
  have hQp : 0 < Q := lt_of_le_of_ne hQ (Ne.symm hz)
  have hQQ : Q ^ 3 ≤ A * R ^ 2 := by
    have hh2 := mul_le_mul h2 h2 (sq_nonneg Q) (mul_nonneg hL hR)
    have hh1 := mul_le_mul_of_nonneg_right h1 (sq_nonneg R)
    by_contra hn
    have hn' := mul_pos hQp (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith [hh1, hh2]
  have hsQ : (Real.sqrt Q) ^ 2 = Q := Real.sq_sqrt hQ
  have hsA : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA
  have hsq : ((Real.sqrt Q) ^ 3) ^ 2 ≤ (Real.sqrt A * R) ^ 2 := by
    calc
      _ = Q ^ 3 := by rw [← pow_mul, Nat.mul_comm 3 2, pow_mul, hsQ]
      _ ≤ A * R ^ 2 := hQQ
      _ = _ := by rw [mul_pow, hsA]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq

private theorem measurePreserving_swapCopies
    (m : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (ε : Fin m → Bool) :
    MeasurePreserving (swapCopies m ε)
      ((Measure.pi (fun _ : Fin m => ν)).prod
        (Measure.pi (fun _ : Fin m => ν)))
      ((Measure.pi (fun _ : Fin m => ν)).prod
        (Measure.pi (fun _ : Fin m => ν))) := by
  have he := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin m)
    (fun _ => ν) (fun _ => ν)
  let f : Fin m → (ℝ × ℝ) → (ℝ × ℝ) :=
    fun i p => cond (ε i) p p.swap
  have hf (i : Fin m) : MeasurePreserving (f i) (ν.prod ν) (ν.prod ν) := by
    cases h : ε i
    · simpa [f, h] using (measurePreserving_swap : MeasurePreserving Prod.swap (ν.prod ν) (ν.prod ν))
    · have hi : f i = id := by funext p; simp [f, h]
      rw [hi]
      exact MeasurePreserving.id _
  have hpi := measurePreserving_pi (fun _ : Fin m => ν.prod ν) (fun _ : Fin m => ν.prod ν) hf
  have h := he.comp (hpi.comp he.symm)
  convert h using 1
  funext p
  apply Prod.ext <;> funext i <;> cases hε : ε i <;>
    simp [swapCopies, MeasurableEquiv.arrowProdEquivProdArrow, f, hε]

private theorem difference_coordinate_third_moment
    (m : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν) (i : Fin m) :
    Integrable (fun p : Shao.Path m × Shao.Path m => |p.1 i - p.2 i| ^ 3)
      ((Measure.pi (fun _ : Fin m => ν)).prod
        (Measure.pi (fun _ : Fin m => ν))) ∧
      (∫ p : Shao.Path m × Shao.Path m, |p.1 i - p.2 i| ^ 3
        ∂((Measure.pi (fun _ : Fin m => ν)).prod
          (Measure.pi (fun _ : Fin m => ν)))) ≤
        8 * (∫ x : ℝ, |x| ^ 3 ∂ν) := by
  let μ := Measure.pi (fun _ : Fin m => ν)
  let ρ := μ.prod μ
  have he : MeasurePreserving (fun a : Shao.Path m => a i) μ ν := measurePreserving_eval _ _
  have hf : MeasurePreserving (fun p : Shao.Path m × Shao.Path m => p.1 i) ρ ν :=
    he.comp measurePreserving_fst
  have hs : MeasurePreserving (fun p : Shao.Path m × Shao.Path m => p.2 i) ρ ν :=
    he.comp measurePreserving_snd
  have hfi := hf.integrable_comp_of_integrable h3
  have hsi := hs.integrable_comp_of_integrable h3
  change Integrable (fun p : Shao.Path m × Shao.Path m => |p.1 i| ^ 3) ρ at hfi
  change Integrable (fun p : Shao.Path m × Shao.Path m => |p.2 i| ^ 3) ρ at hsi
  have hd : Integrable (fun p : Shao.Path m × Shao.Path m => |p.1 i - p.2 i| ^ 3) ρ := by
    apply ((hfi.add hsi).const_mul (4 : ℝ)).mono_nonneg
    · fun_prop
    · exact Filter.Eventually.of_forall fun p => by positivity
    · exact Filter.Eventually.of_forall fun p => abs_cube_sub_le _ _
  refine ⟨hd, ?_⟩
  have hh := integral_mono hd ((hfi.add hsi).const_mul (4 : ℝ)) (fun p => abs_cube_sub_le (p.1 i) (p.2 i))
  have ifi : (∫ p : Shao.Path m × Shao.Path m, |p.1 i| ^ 3 ∂ρ) = ∫ x : ℝ, |x| ^ 3 ∂ν := by
    have hi := integral_map_of_stronglyMeasurable (μ := ρ) hf.measurable
      (f := fun x : ℝ => |x| ^ 3) (continuous_abs.pow 3).stronglyMeasurable
    rw [hf.map_eq] at hi
    exact hi.symm
  have isi : (∫ p : Shao.Path m × Shao.Path m, |p.2 i| ^ 3 ∂ρ) = ∫ x : ℝ, |x| ^ 3 ∂ν := by
    have hi := integral_map_of_stronglyMeasurable (μ := ρ) hs.measurable
      (f := fun x : ℝ => |x| ^ 3) (continuous_abs.pow 3).stronglyMeasurable
    rw [hs.map_eq] at hi
    exact hi.symm
  calc
    _ ≤ ∫ p : Shao.Path m × Shao.Path m, 4 * (|p.1 i| ^ 3 + |p.2 i| ^ 3) ∂ρ := hh
    _ = _ := by rw [integral_const_mul, integral_add hfi hsi, ifi, isi]; ring

theorem weighted_sum_abs_cube_integrable
    (m : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (c : Fin m → ℝ) :
    Integrable (fun a : Shao.Path m => |∑ i : Fin m, c i * a i| ^ 3)
      (Measure.pi (fun _ : Fin m => ν)) := by
  apply integrable_fin_sum_abs_cube _ m (fun i (a : Shao.Path m) => c i * a i)
  · intro i
    exact (show Continuous (fun a : Shao.Path m => c i * a i) by fun_prop).aestronglyMeasurable
  · intro i
    have hi := (measurePreserving_eval (fun _ : Fin m => ν) i).integrable_comp_of_integrable h3
    simpa only [abs_mul, mul_pow, Function.comp_def] using hi.const_mul (|c i| ^ 3)

private theorem symmetrization_le
    (m : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0) (c : Fin m → ℝ) :
    (∫ a : Shao.Path m, |∑ i : Fin m, c i * a i| ^ 3
      ∂(Measure.pi (fun _ : Fin m => ν))) ≤
      ∫ p : Shao.Path m × Shao.Path m,
        |∑ i : Fin m, c i * (p.1 i - p.2 i)| ^ 3
        ∂((Measure.pi (fun _ : Fin m => ν)).prod
          (Measure.pi (fun _ : Fin m => ν))) := by
  classical
  let μ := Measure.pi (fun _ : Fin m => ν)
  let S : Shao.Path m → ℝ := fun a => ∑ i : Fin m, c i * a i
  let D : Shao.Path m × Shao.Path m → ℝ := fun p => ∑ i : Fin m, c i * (p.1 i - p.2 i)
  have hid : Integrable (fun x : ℝ => x) ν := integrable_of_abs_cube ν _ (by fun_prop) h3
  have hcoord (i : Fin m) : Integrable (fun a : Shao.Path m => c i * a i) μ :=
    ((measurePreserving_eval (fun _ : Fin m => ν) i).integrable_comp_of_integrable hid).const_mul _
  have hS : Integrable S μ := integrable_finsetSum Finset.univ (fun i _ => hcoord i)
  have hS3 : Integrable (fun a => |S a| ^ 3) μ := weighted_sum_abs_cube_integrable m ν h3 c
  have hSmean : (∫ a, S a ∂μ) = 0 := by
    rw [integral_finsetSum Finset.univ (fun i _ => hcoord i)]
    apply Finset.sum_eq_zero
    intro i _
    rw [integral_const_mul]
    have he := measurePreserving_eval (fun _ : Fin m => ν) i
    have hi : (∫ a : Shao.Path m, a i ∂μ) = ∫ x : ℝ, x ∂ν := by
      have hi := integral_map_of_stronglyMeasurable (μ := μ) he.measurable
        (f := fun x : ℝ => x) (by fun_prop)
      rw [he.map_eq] at hi
      exact hi.symm
    rw [hi, hmean, mul_zero]
  have hD3 : Integrable (fun p => |D p| ^ 3) (μ.prod μ) := by
    apply integrable_fin_sum_abs_cube _ m (fun i (p : Shao.Path m × Shao.Path m) => c i * (p.1 i - p.2 i))
    · intro i
      fun_prop
    · intro i
      simpa only [abs_mul, mul_pow] using
        (difference_coordinate_third_moment m ν h3 i).1.const_mul (|c i| ^ 3)
  have hsection (a : Shao.Path m) : Integrable (fun b => |D (a, b)| ^ 3) μ := by
    have h : Integrable (fun b => 4 * (|S a| ^ 3 + |S b| ^ 3)) μ :=
      ((integrable_const _).add hS3).const_mul _
    apply h.mono_nonneg (by fun_prop) (Filter.Eventually.of_forall fun b => by positivity)
    exact Filter.Eventually.of_forall fun b => by
      simpa [D, S, Finset.sum_sub_distrib, mul_sub] using abs_cube_sub_le (S a) (S b)
  have hpoint (a : Shao.Path m) : |S a| ^ 3 ≤ ∫ b, |D (a, b)| ^ 3 ∂μ := by
    have heq : (fun b => D (a, b)) = (fun b => S a - S b) := by
      funext b
      simp [D, S, mul_sub, Finset.sum_sub_distrib]
    have hdi : Integrable (fun b => D (a, b)) μ := by rw [heq]; exact (integrable_const _).sub hS
    have hdm : (∫ b, D (a, b) ∂μ) = S a := by
      rw [heq, integral_sub (integrable_const _) hS, hSmean]
      simp
    simpa [hdm] using abs_cube_integral_le μ (fun b => D (a, b)) hdi (hsection a)
  have hh := integral_mono hS3 hD3.integral_prod_left hpoint
  rw [← integral_prod _ hD3] at hh
  exact hh

private theorem integral_difference_abs_cube_eq_signAverage
    (m : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν) (c : Fin m → ℝ) :
    (∫ p : Shao.Path m × Shao.Path m,
      |∑ i : Fin m, c i * (p.1 i - p.2 i)| ^ 3
      ∂((Measure.pi (fun _ : Fin m => ν)).prod
        (Measure.pi (fun _ : Fin m => ν)))) =
      ∫ p : Shao.Path m × Shao.Path m,
        signAverage m (fun ε =>
          |∑ i : Fin m, (c i * (p.1 i - p.2 i)) * signValue (ε i)| ^ 3)
        ∂((Measure.pi (fun _ : Fin m => ν)).prod
          (Measure.pi (fun _ : Fin m => ν))) := by
  classical
  let μ := Measure.pi (fun _ : Fin m => ν)
  let ρ := μ.prod μ
  let F : Shao.Path m × Shao.Path m → ℝ := fun p => |∑ i : Fin m, c i * (p.1 i - p.2 i)| ^ 3
  let G : (Fin m → Bool) → Shao.Path m × Shao.Path m → ℝ :=
    fun ε p => |∑ i : Fin m, (c i * (p.1 i - p.2 i)) * signValue (ε i)| ^ 3
  have hF : Integrable F ρ := by
    apply integrable_fin_sum_abs_cube _ m (fun i (p : Shao.Path m × Shao.Path m) => c i * (p.1 i - p.2 i))
    · intro i
      fun_prop
    · intro i
      simpa only [abs_mul, mul_pow] using
        (difference_coordinate_third_moment m ν h3 i).1.const_mul (|c i| ^ 3)
  have hcomp (ε : Fin m → Bool) : G ε = F ∘ swapCopies m ε := by
    funext p
    dsimp only [G, F, Function.comp_def]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    cases hi : ε i <;> simp [swapCopies, signValue, hi] <;> ring
  have hG (ε : Fin m → Bool) : Integrable (G ε) ρ := by
    rw [hcomp]
    exact (measurePreserving_swapCopies m ν ε).integrable_comp_of_integrable hF
  have heq (ε : Fin m → Bool) : (∫ p, G ε p ∂ρ) = ∫ p, F p ∂ρ := by
    rw [hcomp]
    have he := measurePreserving_swapCopies m ν ε
    have hcont : Continuous F := by dsimp [F]; fun_prop
    have hi := integral_map_of_stronglyMeasurable (μ := ρ) he.measurable (f := F) hcont.stronglyMeasurable
    rw [he.map_eq] at hi
    exact hi.symm
  change (∫ p, F p ∂ρ) = ∫ p, signAverage m (fun ε => G ε p) ∂ρ
  simp only [signAverage, integral_const_mul, integral_finsetSum Finset.univ (fun ε _ => hG ε), heq]
  simp [Nat.cast_pow]

theorem weighted_sum_abs_cube_le
    (m : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (c : Fin m → ℝ) :
    (∫ a : Shao.Path m, |∑ i : Fin m, c i * a i| ^ 3
      ∂(Measure.pi (fun _ : Fin m => ν))) ≤
      24 * (∫ x : ℝ, |x| ^ 3 ∂ν) * (Real.sqrt (∑ i : Fin m, c i ^ 2)) ^ 3 := by
  classical
  let μ := Measure.pi (fun _ : Fin m => ν)
  let ρ := μ.prod μ
  let A : ℝ := ∑ i : Fin m, c i ^ 2
  let β : ℝ := ∫ x : ℝ, |x| ^ 3 ∂ν
  let H : Shao.Path m × Shao.Path m → ℝ := fun p => signAverage m (fun ε =>
    |∑ i : Fin m, (c i * (p.1 i - p.2 i)) * signValue (ε i)| ^ 3)
  let B : Shao.Path m × Shao.Path m → ℝ := fun p =>
    2 * Real.sqrt A * ∑ i : Fin m, c i ^ 2 * |p.1 i - p.2 i| ^ 3
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hβ : 0 ≤ β := integral_nonneg fun x => by positivity
  have hcoord (i : Fin m) : Integrable (fun p : Shao.Path m × Shao.Path m =>
      c i ^ 2 * |p.1 i - p.2 i| ^ 3) ρ :=
    (difference_coordinate_third_moment m ν h3 i).1.const_mul _
  have hB : Integrable B ρ :=
    (integrable_finsetSum Finset.univ (fun i _ => hcoord i)).const_mul _
  have hH : Integrable H ρ := by
    unfold H signAverage
    apply Integrable.const_mul
    apply integrable_finsetSum Finset.univ
    intro ε _
    apply integrable_fin_sum_abs_cube _ m (fun i (p : Shao.Path m × Shao.Path m) => (c i * (p.1 i - p.2 i)) * signValue (ε i))
    · intro i
      fun_prop
    · intro i
      convert
        (difference_coordinate_third_moment m ν h3 i).1.const_mul
          (|c i| ^ 3 * |signValue (ε i)| ^ 3) using 1
      funext p
      simp only [abs_mul, mul_pow]
      ring
  have hpoint (p : Shao.Path m × Shao.Path m) : H p ≤ B p := by
    have hsign := signAverage_abs_cube_le m (fun i => c i * (p.1 i - p.2 i))
    have hw := weighted_square_cube_le m c (fun i => p.1 i - p.2 i)
    dsimp [H, B]
    calc
      _ ≤ 2 * (Real.sqrt (∑ i : Fin m, (c i * (p.1 i - p.2 i)) ^ 2)) ^ 3 := hsign
      _ = 2 * (Real.sqrt (∑ i : Fin m, c i ^ 2 * (p.1 i - p.2 i) ^ 2)) ^ 3 := by simp_rw [mul_pow]
      _ ≤ _ := by dsimp [A] at *; nlinarith
  have hI : (∫ p, B p ∂ρ) ≤ 16 * β * (Real.sqrt A) ^ 3 := by
    have hsum : (∑ i : Fin m, ∫ p : Shao.Path m × Shao.Path m,
        c i ^ 2 * |p.1 i - p.2 i| ^ 3 ∂ρ) ≤ A * (8 * β) := by
      calc
        _ = ∑ i : Fin m, c i ^ 2 * (∫ p : Shao.Path m × Shao.Path m,
            |p.1 i - p.2 i| ^ 3 ∂ρ) := by simp only [integral_const_mul]
        _ ≤ ∑ i : Fin m, c i ^ 2 * (8 * β) := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (difference_coordinate_third_moment m ν h3 i).2 (sq_nonneg _)
        _ = _ := by rw [← Finset.sum_mul]
    dsimp [B]
    rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hcoord i)]
    calc
      _ ≤ 2 * Real.sqrt A * (A * (8 * β)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 2 * Real.sqrt A * ((Real.sqrt A) ^ 2 * (8 * β)) := by rw [Real.sq_sqrt hA]
      _ = _ := by ring
  calc
    _ ≤ ∫ p : Shao.Path m × Shao.Path m,
        |∑ i : Fin m, c i * (p.1 i - p.2 i)| ^ 3 ∂ρ := symmetrization_le m ν h3 hmean c
    _ = ∫ p, H p ∂ρ := integral_difference_abs_cube_eq_signAverage m ν h3 c
    _ ≤ ∫ p, B p ∂ρ := integral_mono hH hB hpoint
    _ ≤ 16 * β * (Real.sqrt A) ^ 3 := hI
    _ ≤ _ := by
      change 16 * β * (Real.sqrt A) ^ 3 ≤ 24 * β * (Real.sqrt A) ^ 3
      nlinarith [mul_nonneg hβ (pow_nonneg (Real.sqrt_nonneg A) 3)]

end Shao.OQ4.WeightedThirdMoment
