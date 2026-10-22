import Shao.OQ3.GaussianBoundaryLaplaceMixture
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace Shao.OQ3

open MeasureTheory Filter
open scoped Topology BigOperators Interval

noncomputable section

private def quadratureR (s h : ℝ) : ℝ :=
  h / (Real.exp (s * h) - 1) + h / 2 - 1 / s

private theorem quadratureR_nonneg (s h : ℝ) (hs : 0 < s) (hh : 0 < h) :
    0 ≤ quadratureR s h := by
  let phi : ℝ → ℝ := fun u => (u - 2) * Real.exp u + u + 2
  have hderiv : ∀ u, HasDerivAt phi ((u - 1) * Real.exp u + 1) u := by
    intro u
    convert! (((hasDerivAt_id u).sub_const 2).mul (Real.hasDerivAt_exp u)).add
      ((hasDerivAt_id u).add_const 2) using 1 <;> first
      | (funext v; simp only [phi, Pi.add_apply, Pi.mul_apply, id_eq]; ring)
      | (simp only [id_eq]; ring)
  have hnonneg : ∀ u : ℝ, 0 ≤ (u - 1) * Real.exp u + 1 := by
    intro u
    have H := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-u))
      (Real.exp_pos u).le
    have he : Real.exp (-u) * Real.exp u = 1 := by
      rw [← Real.exp_add]; simp
    rw [he] at H
    nlinarith only [H]
  have hmono : Monotone phi := monotone_of_hasDerivAt_nonneg hderiv hnonneg
  have hp := hmono (le_of_lt (mul_pos hs hh))
  have hp0 : phi 0 = 0 := by simp [phi]
  rw [hp0] at hp
  have he : 0 < Real.exp (s * h) - 1 := sub_pos.mpr
    ((Real.one_lt_exp_iff).mpr (mul_pos hs hh))
  have heq : quadratureR s h =
      phi (s * h) / (2 * s * (Real.exp (s * h) - 1)) := by
    unfold quadratureR phi
    have he' : -1 + Real.exp (h * s) ≠ 0 := by
      simpa [mul_comm, sub_eq_add_neg, add_comm] using he.ne'
    field_simp [hs.ne', he.ne', he']
    ring_nf
    field_simp [he']
    <;> ring
  rw [heq]
  exact div_nonneg hp (by positivity)

private theorem quadratureR_le_half (s h : ℝ) (hs : 0 < s) (hh : 0 < h) :
    quadratureR s h ≤ h / 2 := by
  have he : 0 < Real.exp (s * h) - 1 := sub_pos.mpr
    ((Real.one_lt_exp_iff).mpr (mul_pos hs hh))
  have H := Real.add_one_le_exp (s * h)
  have hfrac : h / (Real.exp (s * h) - 1) ≤ 1 / s := by
    apply (div_le_div_iff₀ he hs).mpr
    nlinarith only [H]
  unfold quadratureR
  linarith only [hfrac]

private theorem quadratureR_ge_quarter (s h : ℝ) (hs : 0 < s) (hh : 0 < h)
    (hlarge : 4 ≤ s * h) : h / 4 ≤ quadratureR s h := by
  have he : 0 < Real.exp (s * h) - 1 := sub_pos.mpr
    ((Real.one_lt_exp_iff).mpr (mul_pos hs hh))
  have hfrac : 1 / s ≤ h / 4 := by
    apply (div_le_iff₀ hs).mpr
    nlinarith only [hlarge]
  have hgeom : 0 ≤ h / (Real.exp (s * h) - 1) := div_nonneg hh.le he.le
  unfold quadratureR
  linarith only [hfrac, hgeom]

private def cauchyWeight (t : ℝ) : ℝ :=
  (2 / Real.pi) * (1 + t ^ 2)⁻¹

private theorem cauchyWeight_nonneg (t : ℝ) : 0 ≤ cauchyWeight t := by
  unfold cauchyWeight
  positivity

private theorem cauchyWeight_continuous : Continuous cauchyWeight := by
  unfold cauchyWeight
  apply Continuous.mul continuous_const
  apply Continuous.inv₀
  · fun_prop
  · intro t; positivity

private theorem cauchyWeight_integrable : IntegrableOn cauchyWeight (Set.Ioi 0) :=
  integrable_inv_one_add_sq.integrableOn.const_mul _

private theorem integral_cauchyWeight : (∫ t : ℝ in Set.Ioi 0, cauchyWeight t) = 1 := by
  unfold cauchyWeight
  rw [integral_const_mul, integral_Ioi_inv_one_add_sq]
  norm_num

private def decayRate (ell a t : ℝ) : ℝ := a * (1 + t ^ 2) - ell

private theorem decayRate_lower (ell a t : ℝ) (ha : 0 ≤ a) :
    a - ell ≤ decayRate ell a t := by
  unfold decayRate
  nlinarith only [mul_nonneg ha (sq_nonneg t)]

private def mixedKernel (ell a x t : ℝ) : ℝ :=
  cauchyWeight t * Real.exp (-decayRate ell a t * x)

private theorem mixedKernel_nonneg (ell a x t : ℝ) : 0 ≤ mixedKernel ell a x t :=
  mul_nonneg (cauchyWeight_nonneg t) (Real.exp_pos _).le

private theorem mixedKernel_continuous (ell a x : ℝ) :
    Continuous (mixedKernel ell a x) := by
  unfold mixedKernel decayRate
  exact cauchyWeight_continuous.mul (by fun_prop)

private theorem mixedKernel_le (ell a x t : ℝ) (ha : 0 ≤ a) (hgap : ell < a)
    (hx : 0 ≤ x) : mixedKernel ell a x t ≤
      cauchyWeight t * Real.exp (-(a - ell) * x) := by
  unfold mixedKernel
  apply mul_le_mul_of_nonneg_left _ (cauchyWeight_nonneg t)
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_right (decayRate_lower ell a t ha) hx]

private theorem mixedKernel_integrable (ell a x : ℝ) (ha : 0 ≤ a) (hgap : ell < a)
    (hx : 0 ≤ x) : IntegrableOn (mixedKernel ell a x) (Set.Ioi 0) := by
  apply (cauchyWeight_integrable.mul_const (Real.exp (-(a - ell) * x))).mono'
    (mixedKernel_continuous ell a x).aestronglyMeasurable
  exact ae_of_all _ (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mixedKernel_nonneg ell a x t)]
    exact mixedKernel_le ell a x t ha hgap hx)

private theorem integral_mixedKernel_le (ell a x : ℝ) (ha : 0 ≤ a) (hgap : ell < a)
    (hx : 0 ≤ x) : (∫ t : ℝ in Set.Ioi 0, mixedKernel ell a x t) ≤
      Real.exp (-(a - ell) * x) := by
  calc
    _ ≤ ∫ t : ℝ in Set.Ioi 0, cauchyWeight t * Real.exp (-(a - ell) * x) :=
      integral_mono (mixedKernel_integrable ell a x ha hgap hx)
        (cauchyWeight_integrable.mul_const _) (fun t => mixedKernel_le ell a x t ha hgap hx)
    _ = _ := by rw [integral_mul_const, integral_cauchyWeight, one_mul]

private theorem profile_pos (ell kappa x : ℝ) (hk : 0 < kappa) (hx : 0 ≤ x) :
    gaussianBoundaryProfile ell kappa x = Real.exp (-ell * x) := by
  rw [gaussianBoundaryProfile, gaussianBoundaryWeight_eq_piecewise kappa hk,
    if_pos hx, mul_one]

private theorem profile_neg_mixture (ell kappa x : ℝ) (hk : 0 < kappa)
    (hx : 0 ≤ x) : gaussianBoundaryProfile ell kappa (-x) =
      ∫ t : ℝ in Set.Ioi 0, mixedKernel ell (kappa ^ 2 / 2) x t := by
  have hm := gaussianBoundaryWeight_neg_laplace_mixture kappa x hk hx
  unfold gaussianBoundaryProfile
  rw [hm.2, ← mul_assoc, ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  unfold mixedKernel cauchyWeight decayRate
  dsimp only []
  have he : -ell * -x + -((kappa ^ 2 / 2) * (1 + t ^ 2)) * x =
      -(kappa ^ 2 / 2 * (1 + t ^ 2) - ell) * x := by ring
  calc
    _ = (2 / Real.pi) * (1 + t ^ 2)⁻¹ *
        (Real.exp (-ell * -x) * Real.exp (-((kappa ^ 2 / 2) * (1 + t ^ 2)) * x)) := by ring
    _ = _ := by rw [← Real.exp_add, he]

private theorem exp_nat_summable (r : ℝ) (hr : 0 < r) :
    Summable (fun n : ℕ => Real.exp (-r * (n : ℝ))) := by
  have hratio : |Real.exp (-r)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hr)
  convert! summable_geometric_of_abs_lt_one hratio using 1
  funext n
  rw [← Real.exp_nat_mul]
  congr 1
  ring

private theorem exp_nat_tsum (r : ℝ) (hr : 0 < r) :
    (∑' n : ℕ, Real.exp (-r * (n : ℝ))) = 1 / (1 - Real.exp (-r)) := by
  have hratio : |Real.exp (-r)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hr)
  convert! tsum_geometric_of_abs_lt_one hratio using 1
  · apply tsum_congr
    intro n
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  · exact one_div _

private theorem exp_succ_summable (r : ℝ) (hr : 0 < r) :
    Summable (fun n : ℕ => Real.exp (-r * ((n : ℝ) + 1))) := by
  convert! (exp_nat_summable r hr).comp_injective Nat.succ_injective using 1
  funext n
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one]

private theorem exp_succ_tsum (r : ℝ) (hr : 0 < r) :
    (∑' n : ℕ, Real.exp (-r * ((n : ℝ) + 1))) = 1 / (Real.exp r - 1) := by
  have hsum := (exp_nat_summable r hr).tsum_eq_zero_add
  have hcast : (fun n : ℕ => Real.exp (-r * ↑(n + 1))) =
      (fun n : ℕ => Real.exp (-r * ((n : ℝ) + 1))) := by
    funext n; simp only [Nat.cast_add, Nat.cast_one]
  rw [hcast, exp_nat_tsum r hr] at hsum
  simp only [Nat.cast_zero, mul_zero, Real.exp_zero] at hsum
  have hd : 0 < 1 - Real.exp (-r) := sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hr))
  have hE : 0 < Real.exp r - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hr)
  have he : Real.exp (-r) * Real.exp r = 1 := by rw [← Real.exp_add]; simp
  have hid : 1 / (1 - Real.exp (-r)) - 1 = 1 / (Real.exp r - 1) := by
    field_simp [hd.ne', hE.ne']
    nlinarith only [he]
  linarith only [hsum, hid]

private theorem profile_nat_summable (ell kappa h : ℝ) (hell : 0 < ell)
    (hk : 0 < kappa) (hh : 0 < h) :
    Summable (fun n : ℕ => gaussianBoundaryProfile ell kappa ((n : ℝ) * h)) := by
  convert! exp_nat_summable (ell * h) (mul_pos hell hh) using 1
  funext n
  rw [profile_pos ell kappa _ hk (by positivity)]
  congr 1
  ring

private theorem profile_neg_summable (ell kappa h : ℝ) (hk : 0 < kappa)
    (hgap : ell < kappa ^ 2 / 2) (hh : 0 < h) :
    Summable (fun n : ℕ =>
      gaussianBoundaryProfile ell kappa (-(((n : ℝ) + 1) * h))) := by
  have ha : 0 ≤ kappa ^ 2 / 2 := by positivity
  apply Summable.of_nonneg_of_le
    (fun n => ?_) (fun n => ?_)
    (exp_succ_summable ((kappa ^ 2 / 2 - ell) * h) (by positivity))
  · rw [profile_neg_mixture ell kappa _ hk (by positivity)]
    exact integral_nonneg (mixedKernel_nonneg _ _ _)
  · rw [profile_neg_mixture ell kappa _ hk (by positivity)]
    convert! integral_mixedKernel_le ell (kappa ^ 2 / 2) (((n : ℝ) + 1) * h)
      ha hgap (by positivity) using 1 <;> congr 1 <;> ring

private theorem profile_integer_summable (ell kappa h : ℝ) (hell : 0 < ell)
    (hk : 0 < kappa) (hgap : ell < kappa ^ 2 / 2) (hh : 0 < h) :
    Summable (fun k : ℤ => gaussianBoundaryProfile ell kappa ((k : ℝ) * h)) := by
  apply Summable.of_nat_of_neg_add_one
    (by simpa only [Int.cast_natCast] using profile_nat_summable ell kappa h hell hk hh)
  simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, neg_mul] using
    profile_neg_summable ell kappa h hk hgap hh

private theorem decayRate_pos (ell a t : ℝ) (ha : 0 ≤ a) (hgap : ell < a) :
    0 < decayRate ell a t :=
  (sub_pos.mpr hgap).trans_le (decayRate_lower ell a t ha)

private theorem weighted_inv_integrable (ell a : ℝ) (ha : 0 ≤ a) (hgap : ell < a) :
    IntegrableOn (fun t : ℝ => cauchyWeight t / decayRate ell a t) (Set.Ioi 0) := by
  have hc : Continuous (fun t : ℝ => cauchyWeight t / decayRate ell a t) := by
    apply cauchyWeight_continuous.div
    · unfold decayRate; fun_prop
    · intro t; exact (decayRate_pos ell a t ha hgap).ne'
  apply (cauchyWeight_integrable.div_const (a - ell)).mono' hc.aestronglyMeasurable
  exact ae_of_all _ (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (cauchyWeight_nonneg t) (decayRate_pos ell a t ha hgap).le)]
    exact div_le_div_of_nonneg_left (cauchyWeight_nonneg t) (sub_pos.mpr hgap)
      (decayRate_lower ell a t ha))

private theorem integral_mixedKernel_x (ell a t : ℝ) (ha : 0 ≤ a) (hgap : ell < a) :
    (∫ x : ℝ in Set.Ioi 0, mixedKernel ell a x t) =
      cauchyWeight t / decayRate ell a t := by
  unfold mixedKernel
  rw [integral_const_mul, integral_exp_mul_Ioi
    (neg_neg_of_pos (decayRate_pos ell a t ha hgap)) 0]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]
  ring

private theorem mixedKernel_joint_integrable (ell a : ℝ) (ha : 0 ≤ a) (hgap : ell < a) :
    Integrable (fun p : ℝ × ℝ => mixedKernel ell a p.2 p.1)
      (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((volume : Measure ℝ).restrict (Set.Ioi 0))) := by
  have hc : Continuous (fun p : ℝ × ℝ => mixedKernel ell a p.2 p.1) := by
    unfold mixedKernel decayRate
    exact (cauchyWeight_continuous.comp continuous_fst).mul (by fun_prop)
  apply (integrable_prod_iff hc.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun t => ?_), ?_⟩
  · exact (integrableOn_exp_mul_Ioi
      (neg_neg_of_pos (decayRate_pos ell a t ha hgap)) 0).const_mul (cauchyWeight t)
  · have heq : (fun t : ℝ => ∫ x : ℝ in Set.Ioi 0, ‖mixedKernel ell a x t‖) =
        (fun t : ℝ => cauchyWeight t / decayRate ell a t) := by
      funext t
      calc
        _ = ∫ x : ℝ in Set.Ioi 0, mixedKernel ell a x t := by
          apply integral_congr_ae
          exact ae_of_all _ (fun x => Real.norm_of_nonneg (mixedKernel_nonneg ell a x t))
        _ = _ := integral_mixedKernel_x ell a t ha hgap
    rw [heq]
    exact weighted_inv_integrable ell a ha hgap

private theorem integral_profile_negative (ell kappa : ℝ) (hk : 0 < kappa)
    (hgap : ell < kappa ^ 2 / 2) :
    (∫ x : ℝ in Set.Ioi 0, gaussianBoundaryProfile ell kappa (-x)) =
      ∫ t : ℝ in Set.Ioi 0, cauchyWeight t / decayRate ell (kappa ^ 2 / 2) t := by
  have ha : 0 ≤ kappa ^ 2 / 2 := by positivity
  calc
    _ = ∫ x : ℝ in Set.Ioi 0, ∫ t : ℝ in Set.Ioi 0,
        mixedKernel ell (kappa ^ 2 / 2) x t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact profile_neg_mixture ell kappa x hk hx.le
    _ = ∫ t : ℝ in Set.Ioi 0, ∫ x : ℝ in Set.Ioi 0,
        mixedKernel ell (kappa ^ 2 / 2) x t :=
      (integral_integral_swap (mixedKernel_joint_integrable ell (kappa ^ 2 / 2) ha hgap)).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun t => integral_mixedKernel_x ell (kappa ^ 2 / 2) t ha hgap)

private theorem tsum_profile_negative (ell kappa h : ℝ) (hk : 0 < kappa)
    (hgap : ell < kappa ^ 2 / 2) (hh : 0 < h) :
    (∑' n : ℕ, gaussianBoundaryProfile ell kappa (-(((n : ℝ) + 1) * h))) =
      ∫ t : ℝ in Set.Ioi 0,
        cauchyWeight t / (Real.exp (decayRate ell (kappa ^ 2 / 2) t * h) - 1) := by
  let a : ℝ := kappa ^ 2 / 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hnorm (n : ℕ) :
      (∫ t : ℝ in Set.Ioi 0, ‖mixedKernel ell a (((n : ℝ) + 1) * h) t‖) =
        ∫ t : ℝ in Set.Ioi 0, mixedKernel ell a (((n : ℝ) + 1) * h) t := by
    apply integral_congr_ae
    exact ae_of_all _ (fun t => Real.norm_of_nonneg (mixedKernel_nonneg _ _ _ t))
  have hs : Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0, ‖mixedKernel ell a (((n : ℝ) + 1) * h) t‖) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun t => norm_nonneg _))
      (fun n => ?_) (exp_succ_summable ((a - ell) * h) (by positivity))
    rw [hnorm]
    convert! integral_mixedKernel_le ell a (((n : ℝ) + 1) * h) ha hgap
      (by positivity) using 1 <;> congr 1 <;> ring
  calc
    _ = ∑' n : ℕ, ∫ t : ℝ in Set.Ioi 0,
        mixedKernel ell a (((n : ℝ) + 1) * h) t := by
      apply tsum_congr
      intro n
      exact profile_neg_mixture ell kappa _ hk (by positivity)
    _ = ∫ t : ℝ in Set.Ioi 0, ∑' n : ℕ,
        mixedKernel ell a (((n : ℝ) + 1) * h) t :=
      integral_tsum_of_summable_integral_norm
        (fun n => mixedKernel_integrable ell a _ ha hgap (by positivity)) hs
    _ = _ := by
      apply integral_congr_ae
      apply ae_of_all
      intro t
      have hfun : (fun n : ℕ => mixedKernel ell a (((n : ℝ) + 1) * h) t) =
          (fun n : ℕ => cauchyWeight t *
            Real.exp (-(decayRate ell a t * h) * ((n : ℝ) + 1))) := by
        funext n
        unfold mixedKernel
        congr 2
        ring
      dsimp only []
      rw [hfun, tsum_mul_left, exp_succ_tsum _
        (mul_pos (decayRate_pos ell a t ha hgap) hh)]
      simp only [a, mul_one_div]

private theorem weighted_geom_integrable (ell a h : ℝ) (ha : 0 ≤ a)
    (hgap : ell < a) (hh : 0 < h) :
    IntegrableOn (fun t : ℝ =>
      cauchyWeight t / (Real.exp (decayRate ell a t * h) - 1)) (Set.Ioi 0) := by
  have hd (t : ℝ) : 0 < Real.exp (decayRate ell a t * h) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos (decayRate_pos ell a t ha hgap) hh))
  have hc : Continuous (fun t : ℝ =>
      cauchyWeight t / (Real.exp (decayRate ell a t * h) - 1)) := by
    apply cauchyWeight_continuous.div
    · unfold decayRate; fun_prop
    · intro t; exact (hd t).ne'
  apply ((weighted_inv_integrable ell a ha hgap).div_const h).mono'
    hc.aestronglyMeasurable
  exact ae_of_all _ (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (cauchyWeight_nonneg t) (hd t).le)]
    calc
      _ ≤ cauchyWeight t / (decayRate ell a t * h) :=
        div_le_div_of_nonneg_left (cauchyWeight_nonneg t)
          (mul_pos (decayRate_pos ell a t ha hgap) hh)
          (by linarith only [Real.add_one_le_exp (decayRate ell a t * h)])
      _ = _ := by ring)

private theorem weightedR_continuous (ell a h : ℝ) (ha : 0 ≤ a)
    (hgap : ell < a) (hh : 0 < h) :
    Continuous (fun t : ℝ => cauchyWeight t * quadratureR (decayRate ell a t) h) := by
  have hc : Continuous (decayRate ell a) := by unfold decayRate; fun_prop
  have he : Continuous (fun t : ℝ => h / (Real.exp (decayRate ell a t * h) - 1)) :=
    continuous_const.div (by unfold decayRate; fun_prop) (fun t =>
      (sub_pos.mpr (Real.one_lt_exp_iff.mpr
        (mul_pos (decayRate_pos ell a t ha hgap) hh))).ne')
  exact cauchyWeight_continuous.mul ((he.add continuous_const).sub
    (continuous_const.div hc (fun t => (decayRate_pos ell a t ha hgap).ne')))

private theorem weightedR_integrable (ell a h : ℝ) (ha : 0 ≤ a)
    (hgap : ell < a) (hh : 0 < h) :
    IntegrableOn (fun t : ℝ => cauchyWeight t * quadratureR (decayRate ell a t) h)
      (Set.Ioi 0) := by
  apply (cauchyWeight_integrable.mul_const (h / 2)).mono'
    (weightedR_continuous ell a h ha hgap hh).aestronglyMeasurable
  exact ae_of_all _ (fun t => by
    have h0 := quadratureR_nonneg (decayRate ell a t) h (decayRate_pos ell a t ha hgap) hh
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (cauchyWeight_nonneg t) h0)]
    exact mul_le_mul_of_nonneg_left
      (quadratureR_le_half (decayRate ell a t) h (decayRate_pos ell a t ha hgap) hh)
      (cauchyWeight_nonneg t))

private theorem integral_weightedR (ell a h : ℝ) (ha : 0 ≤ a)
    (hgap : ell < a) (hh : 0 < h) :
    (∫ t : ℝ in Set.Ioi 0, cauchyWeight t * quadratureR (decayRate ell a t) h) =
      h * (∫ t : ℝ in Set.Ioi 0,
        cauchyWeight t / (Real.exp (decayRate ell a t * h) - 1)) + h / 2 -
      ∫ t : ℝ in Set.Ioi 0, cauchyWeight t / decayRate ell a t := by
  have hg := weighted_geom_integrable ell a h ha hgap hh
  have hi := weighted_inv_integrable ell a ha hgap
  have heq : (fun t : ℝ => cauchyWeight t * quadratureR (decayRate ell a t) h) =
      (fun t : ℝ => h * (cauchyWeight t / (Real.exp (decayRate ell a t * h) - 1)) +
        (h / 2) * cauchyWeight t - cauchyWeight t / decayRate ell a t) := by
    funext t; unfold quadratureR; ring
  have hsub := integral_sub ((hg.const_mul h).add (cauchyWeight_integrable.const_mul (h / 2))) hi
  have hadd := integral_add (hg.const_mul h) (cauchyWeight_integrable.const_mul (h / 2))
  simp only [Pi.add_apply, Pi.sub_apply] at hsub hadd
  rw [heq, hsub, hadd, integral_const_mul, integral_const_mul, integral_cauchyWeight, mul_one]

private theorem integral_profile_split (ell kappa : ℝ) (hell : 0 < ell)
    (hk : 0 < kappa) (hgap : ell < kappa ^ 2 / 2) :
    (∫ d : ℝ, gaussianBoundaryProfile ell kappa d) = 1 / ell +
      ∫ t : ℝ in Set.Ioi 0, cauchyWeight t / decayRate ell (kappa ^ 2 / 2) t := by
  have hi := gaussianBoundaryProfile_integrable ell kappa hell hk (by linarith only [hgap])
  have hp : (∫ x : ℝ in Set.Ioi 0, gaussianBoundaryProfile ell kappa x) = 1 / ell := by
    calc
      _ = ∫ x : ℝ in Set.Ioi 0, Real.exp (-ell * x) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        exact profile_pos ell kappa x hk hx.le
      _ = _ := by rw [integral_exp_mul_Ioi (neg_neg_of_pos hell) 0]; simp
  have hn : (∫ x : ℝ in Set.Iic 0, gaussianBoundaryProfile ell kappa x) =
      ∫ t : ℝ in Set.Ioi 0, cauchyWeight t / decayRate ell (kappa ^ 2 / 2) t := by
    have hr := integral_comp_neg_Ioi 0 (gaussianBoundaryProfile ell kappa)
    simp only [neg_zero] at hr
    rw [← hr]
    exact integral_profile_negative ell kappa hk hgap
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hi.integrableOn hi.integrableOn,
    hp, hn, add_comm]

private theorem profile_positive_tsum (ell kappa h : ℝ) (hell : 0 < ell)
    (hk : 0 < kappa) (hh : 0 < h) :
    (∑' n : ℕ, gaussianBoundaryProfile ell kappa ((n : ℝ) * h)) =
      1 + 1 / (Real.exp (ell * h) - 1) := by
  have heq : (fun n : ℕ => gaussianBoundaryProfile ell kappa ((n : ℝ) * h)) =
      (fun n : ℕ => Real.exp (-(ell * h) * (n : ℝ))) := by
    funext n
    rw [profile_pos ell kappa _ hk (by positivity)]
    congr 1
    ring
  rw [heq, (exp_nat_summable (ell * h) (mul_pos hell hh)).tsum_eq_zero_add]
  simp only [Nat.cast_zero, mul_zero, Real.exp_zero, Nat.cast_add, Nat.cast_one]
  rw [exp_succ_tsum _ (mul_pos hell hh)]

private theorem profile_quadrature_identity (ell kappa h : ℝ) (hell : 0 < ell)
    (hk : 0 < kappa) (hgap : ell < kappa ^ 2 / 2) (hh : 0 < h) :
    h * (∑' k : ℤ, gaussianBoundaryProfile ell kappa ((k : ℝ) * h)) -
      (∫ d : ℝ, gaussianBoundaryProfile ell kappa d) = quadratureR ell h +
      ∫ t : ℝ in Set.Ioi 0, cauchyWeight t * quadratureR (decayRate ell (kappa ^ 2 / 2) t) h := by
  have hpos : Summable (fun n : ℕ => gaussianBoundaryProfile ell kappa (((n : ℤ) : ℝ) * h)) := by
    simpa only [Int.cast_natCast] using profile_nat_summable ell kappa h hell hk hh
  have hneg : Summable (fun n : ℕ =>
      gaussianBoundaryProfile ell kappa (((-((n : ℤ) + 1) : ℤ) : ℝ) * h)) := by
    simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, neg_mul] using
      profile_neg_summable ell kappa h hk hgap hh
  have hz := tsum_of_nat_of_neg_add_one
    (f := fun k : ℤ => gaussianBoundaryProfile ell kappa ((k : ℝ) * h)) hpos hneg
  simp only [Int.cast_natCast, Int.cast_neg, Int.cast_add, Int.cast_one, neg_mul] at hz
  rw [hz, profile_positive_tsum ell kappa h hell hk hh,
    tsum_profile_negative ell kappa h hk hgap hh, integral_profile_split ell kappa hell hk hgap,
    integral_weightedR ell (kappa ^ 2 / 2) h (by positivity) hgap hh]
  unfold quadratureR
  ring

private theorem integral_weightedR_lower (ell a h : ℝ) (ha : 1 / 30 < a)
    (hell : ell < 1 / 30) (hh : 0 < h) (hh1 : h ≤ 1) :
    (6 * h * Real.sqrt h) / (577 * Real.pi) ≤
      ∫ t : ℝ in Set.Ioi 0, cauchyWeight t * quadratureR (decayRate ell a t) h := by
  have ha0 : 0 ≤ a := by linarith only [ha]
  have hgap : ell < a := hell.trans ha
  let u : ℝ := Real.sqrt h
  let r : ℝ := 12 / u
  have hu : 0 < u := Real.sqrt_pos.mpr hh
  have hu2 : u ^ 2 = h := Real.sq_sqrt hh.le
  have hr : 0 < r := div_pos (by norm_num) hu
  have hbounds (t : ℝ) (ht : t ∈ Set.Icc r (2 * r)) :
      144 ≤ h * t ^ 2 ∧ h * t ^ 2 ≤ 576 := by
    have ht0 : 0 < t := hr.trans_le ht.1
    have hlo : 12 ≤ t * u := (div_le_iff₀ hu).mp ht.1
    have hhi : t * u ≤ 24 := by
      have H : t ≤ 24 / u := by convert! ht.2 using 1 <;> dsimp [r] <;> ring
      exact (le_div_iff₀ hu).mp H
    have hsqlo : 144 ≤ (t * u) ^ 2 := by nlinarith only [sq_nonneg (t * u - 12), hlo]
    have hsqhi : (t * u) ^ 2 ≤ 576 := by
      nlinarith only [mul_self_le_mul_self (mul_nonneg ht0.le hu.le) hhi]
    rw [mul_pow, hu2] at hsqlo hsqhi
    constructor <;> nlinarith only [hsqlo, hsqhi]
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc r (2 * r)) :
      (2 * h / (577 * Real.pi)) * (h / 4) ≤
        cauchyWeight t * quadratureR (decayRate ell a t) h := by
    have ht := hbounds t ht
    have hs : 4 ≤ decayRate ell a t * h := by
      have H := mul_le_mul_of_nonneg_left ht.1 ha0
      have H' := mul_nonneg (sub_pos.mpr hgap).le hh.le
      unfold decayRate
      nlinarith only [H, H', ha]
    have hw : 2 * h / (577 * Real.pi) ≤ cauchyWeight t := by
      have hd : 0 < 1 + t ^ 2 := by positivity
      have heq : cauchyWeight t = 2 / (Real.pi * (1 + t ^ 2)) := by
        unfold cauchyWeight
        simp only [mul_inv_rev, div_eq_mul_inv]
        ring
      rw [heq]
      apply (div_le_div_iff₀ (by positivity : 0 < 577 * Real.pi)
        (mul_pos Real.pi_pos hd)).mpr
      have H : h * (1 + t ^ 2) ≤ 577 := by nlinarith only [ht.2, hh1]
      nlinarith only [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr H)]
    exact mul_le_mul hw
      (quadratureR_ge_quarter (decayRate ell a t) h (decayRate_pos ell a t ha0 hgap) hh hs)
      (by positivity) (cauchyWeight_nonneg t)
  have hfinite : IntegrableOn
      (fun t : ℝ => cauchyWeight t * quadratureR (decayRate ell a t) h) (Set.Icc r (2 * r)) :=
    (weightedR_continuous ell a h ha0 hgap hh).integrableOn_Icc
  have hint := setIntegral_ge_of_const_le_real (μ := (volume : Measure ℝ))
    measurableSet_Icc (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) hpoint hfinite
  have hlength : volume.real (Set.Icc r (2 * r)) = r := by
    rw [Real.volume_real_Icc_of_le (by linarith only [hr])]
    ring
  rw [hlength] at hint
  have hsub : (∫ t : ℝ in Set.Icc r (2 * r),
      cauchyWeight t * quadratureR (decayRate ell a t) h) ≤
        ∫ t : ℝ in Set.Ioi 0, cauchyWeight t * quadratureR (decayRate ell a t) h := by
    apply setIntegral_mono_set (weightedR_integrable ell a h ha0 hgap hh)
      (ae_of_all _ (fun t => mul_nonneg (cauchyWeight_nonneg t)
        (quadratureR_nonneg _ h (decayRate_pos ell a t ha0 hgap) hh)))
    exact ae_of_all _ (fun t ht => hr.trans_le ht.1)
  have heq : (2 * h / (577 * Real.pi)) * (h / 4) * r =
      (6 * h * Real.sqrt h) / (577 * Real.pi) := by
    dsimp [r, u]
    have hsqrt : Real.sqrt h ≠ 0 := (Real.sqrt_pos.mpr hh).ne'
    field_simp
    nlinarith only [Real.sq_sqrt hh.le]
  rw [heq] at hint
  exact hint.trans hsub

private theorem profile_lattice_gap (ell kappa h : ℝ) (hell : 0 < ell)
    (hell1 : ell < 1 / 30) (hk : 0 < kappa) (ha : 1 / 30 < kappa ^ 2 / 2)
    (hh : 0 < h) (hh1 : h ≤ 1) :
    (∫ d : ℝ, gaussianBoundaryProfile ell kappa d) +
      (6 * h * Real.sqrt h) / (577 * Real.pi) ≤
        h * ∑' k : ℤ, gaussianBoundaryProfile ell kappa ((k : ℝ) * h) := by
  have hid := profile_quadrature_identity ell kappa h hell hk (hell1.trans ha) hh
  have hlower := integral_weightedR_lower ell (kappa ^ 2 / 2) h ha hell1 hh hh1
  have h0 := quadratureR_nonneg ell h hell hh
  linarith only [hid, hlower, h0]

theorem stage_sourceGaussianLayerWeight_lattice_gap
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (J : ℕ) (q : ℝ)
    (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = q / 4)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    Summable (fun k : ℤ => sourceGaussianLayerWeight mu q sourceEll
      ((k : ℝ) * dyadicMesh J)) ∧
    correctedInverseScale sourceEll q mu +
      (dyadicMesh J * Real.sqrt (dyadicMesh J)) / (4096 * Real.pi) ≤
      (dyadicMesh J / Real.sqrt (normalVariance mu)) *
        ∑' k : ℤ, sourceGaussianLayerWeight mu q sourceEll
          ((k : ℝ) * dyadicMesh J) := by
  have hq : 0 < q := lt_trans zero_lt_one hq0
  have hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10 := by
    filter_upwards [hrange] with x hx
    obtain ⟨i, rfl⟩ := hx
    cases i with
    | inl i => exact (fixedAtom_bounds (Sum.inl i)).2
    | inr j => exact (fixedAtom_bounds (Sum.inr j.val)).2
  have hbase : ∀ i : Fin 4, 0 < mu.real {baseAtom i} := fun i => hpos (Sum.inl i)
  have hS := normalVariance_pos mu hb hbase
  have hT := transverseVariance_pos mu hb hbase
  have hX : Integrable (fun x : ℝ => x) mu :=
    integrable_continuous_of_fixed_bounds mu hb _ continuous_id
  have hX2 : Integrable (fun x : ℝ => x ^ 2) mu :=
    integrable_continuous_of_fixed_bounds mu hb _ (by fun_prop)
  have hmoment : (∫ x : ℝ, normalValue x ∂mu) =
      8 * (∫ x : ℝ, x ∂mu) - (∫ x : ℝ, x ^ 2 ∂mu) := by
    change (∫ x : ℝ, 8 * x - x ^ 2 ∂mu) = _
    rw [integral_sub (hX.const_mul 8) hX2, integral_const_mul]
  have hsecond : (∫ x : ℝ, x ^ 2 ∂mu) = q := by
    rw [hmeanY, hmeanX] at hmoment
    linarith only [hmoment]
  have hLp : MemLp (fun x : ℝ => x) 2 mu :=
    MemLp.of_bound continuous_id.aestronglyMeasurable (4 + Real.sqrt 10)
      (by simpa only [Real.norm_eq_abs] using hb)
  have hVar : ProbabilityTheory.variance (fun x : ℝ => x) mu = q - q ^ 2 / 16 := by
    rw [ProbabilityTheory.variance_eq_sub hLp]
    change (∫ x : ℝ, x ^ 2 ∂mu) - (∫ x : ℝ, x ∂mu) ^ 2 = _
    rw [hsecond, hmeanX]
    ring
  have hle := transverseVariance_le_variance_id mu hb hbase
  rw [hVar] at hle
  have hfrac : (1 : ℝ) / 30 < q / (32 * transverseVariance mu) := by
    apply (lt_div_iff₀ (mul_pos (by norm_num) hT)).mpr
    nlinarith only [hle, sq_nonneg (q - 1), hq0, hq1]
  have hk : 0 < boundaryKappa q mu :=
    div_pos (Real.sqrt_pos.mpr hq)
      (mul_pos (by norm_num) (Real.sqrt_pos.mpr hT))
  have hksq : boundaryKappa q mu ^ 2 / 2 = q / (32 * transverseVariance mu) := by
    unfold boundaryKappa
    rw [div_pow, mul_pow, Real.sq_sqrt hq.le, Real.sq_sqrt hT.le]
    ring
  have ha : 1 / 30 < boundaryKappa q mu ^ 2 / 2 := by rw [hksq]; exact hfrac
  have hY : ∀ᵐ x ∂mu, |normalValue x| ≤ 16 := by
    filter_upwards [hrange] with x hx
    obtain ⟨i, rfl⟩ := hx
    have hlo : -9 ≤ normalValue (stageAtom (fun j : Fin J => addedAtom j.val) i) := by
      cases i with
      | inl i => exact fixedAtom_normalValue_lower (Sum.inl i)
      | inr j => exact fixedAtom_normalValue_lower (Sum.inr j.val)
    have hhi : normalValue (stageAtom (fun j : Fin J => addedAtom j.val) i) ≤ 16 := by
      unfold normalValue
      nlinarith only [sq_nonneg (stageAtom (fun j : Fin J => addedAtom j.val) i - 4)]
    exact abs_le.mpr ⟨by linarith only [hlo], hhi⟩
  have hYc : Continuous normalValue := by unfold normalValue; fun_prop
  have hYlp : MemLp normalValue 2 mu :=
    MemLp.of_bound hYc.aestronglyMeasurable 16 (by simpa only [Real.norm_eq_abs] using hY)
  have hY2 : Integrable (fun x : ℝ => normalValue x ^ 2) mu :=
    integrable_continuous_of_fixed_bounds mu hb _ (hYc.pow 2)
  have hYsq : (∫ x : ℝ, normalValue x ^ 2 ∂mu) ≤ 256 := by
    have hbound : ∀ᵐ x ∂mu, normalValue x ^ 2 ≤ 256 := by
      filter_upwards [hY] with x hx
      have H := abs_le.mp hx
      nlinarith only [H.1, H.2, sq_nonneg (normalValue x)]
    simpa using integral_mono_ae hY2 (integrable_const (256 : ℝ)) hbound
  have hSupper : normalVariance mu ≤ 256 := by
    change ProbabilityTheory.variance normalValue mu ≤ 256
    rw [ProbabilityTheory.variance_eq_sub hYlp]
    change (∫ x : ℝ, normalValue x ^ 2 ∂mu) - (∫ x : ℝ, normalValue x ∂mu) ^ 2 ≤ 256
    nlinarith only [hYsq, sq_nonneg (∫ x : ℝ, normalValue x ∂mu)]
  have hsigma : 0 < Real.sqrt (normalVariance mu) := Real.sqrt_pos.mpr hS
  have hsigma16 : Real.sqrt (normalVariance mu) ≤ 16 := by
    nlinarith only [Real.sq_sqrt hS.le, hsigma.le, hSupper]
  have hh : 0 < dyadicMesh J := by unfold dyadicMesh; positivity
  have hh1 : dyadicMesh J ≤ 1 := by
    unfold dyadicMesh
    exact (inv_le_one₀ (by positivity)).mpr (one_le_pow₀ (by norm_num))
  obtain ⟨hfun, _, hcontinuous⟩ := stage_sourceGaussianLayerWeight_profile_and_integral
    mu J q hq0 hq1 hmeanY hmeanX hrange hpos
  have hfunext : sourceGaussianLayerWeight mu q sourceEll =
      gaussianBoundaryProfile sourceEll (boundaryKappa q mu) := funext hfun
  refine ⟨?_, ?_⟩
  · rw [hfunext]
    exact profile_integer_summable sourceEll (boundaryKappa q mu) (dyadicMesh J)
      sourceEll_pos hk (sourceEll_lt_one_div_thirty.trans ha) hh
  · have hgap := profile_lattice_gap sourceEll (boundaryKappa q mu) (dyadicMesh J)
      sourceEll_pos sourceEll_lt_one_div_thirty hk ha hh hh1
    rw [← hfunext] at hgap
    have hscaled := mul_le_mul_of_nonneg_left hgap (one_div_pos.mpr hsigma).le
    have hmargin : Real.sqrt (normalVariance mu) *
        ((dyadicMesh J * Real.sqrt (dyadicMesh J)) / (4096 * Real.pi)) ≤
        (6 * dyadicMesh J * Real.sqrt (dyadicMesh J)) / (577 * Real.pi) := by
      calc
        _ ≤ 16 * ((dyadicMesh J * Real.sqrt (dyadicMesh J)) / (4096 * Real.pi)) :=
          mul_le_mul_of_nonneg_right hsigma16 (by positivity)
        _ ≤ _ := by
          rw [← mul_div_assoc]
          apply (div_le_div_iff₀ (by positivity : 0 < 4096 * Real.pi)
            (by positivity : 0 < 577 * Real.pi)).mpr
          nlinarith only [mul_nonneg (mul_nonneg hh.le
            (Real.sqrt_nonneg (dyadicMesh J))) Real.pi_pos.le]
    have hnormalized :
        (dyadicMesh J * Real.sqrt (dyadicMesh J)) / (4096 * Real.pi) ≤
          ((6 * dyadicMesh J * Real.sqrt (dyadicMesh J)) / (577 * Real.pi)) /
            Real.sqrt (normalVariance mu) :=
      (le_div_iff₀ hsigma).mpr (by simpa only [mul_comm] using hmargin)
    rw [mul_add, hcontinuous] at hscaled
    have heq : (1 / Real.sqrt (normalVariance mu)) *
        ((6 * dyadicMesh J * Real.sqrt (dyadicMesh J)) / (577 * Real.pi)) =
        ((6 * dyadicMesh J * Real.sqrt (dyadicMesh J)) / (577 * Real.pi)) /
          Real.sqrt (normalVariance mu) := by ring
    rw [heq] at hscaled
    have hfinal : correctedInverseScale sourceEll q mu +
        (dyadicMesh J * Real.sqrt (dyadicMesh J)) / (4096 * Real.pi) ≤
          (1 / Real.sqrt (normalVariance mu)) * (dyadicMesh J *
            ∑' k : ℤ, sourceGaussianLayerWeight mu q sourceEll ((k : ℝ) * dyadicMesh J)) := by
      linarith only [hnormalized, hscaled]
    convert! hfinal using 1 <;> ring

end
end Shao.OQ3
