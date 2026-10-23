import Shao.Probability.SourceFourierScale
import Shao.Probability.FiniteIID
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.Complex.Exponential

/-!
The actual fixed-x conditional law supplies the noncentered finite-product
Chernoff estimate in supplement.tex 908--920.  The clock is the expectation
of the actual squared coordinates.  This does not supply the localized
scalar-noise derivative or close the original C1/C2 comparison.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Shao.Probability

private theorem smt_power_integrable
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h : ℝ) (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h) (p : ℕ) :
    Integrable (fun a : ℝ => a ^ p) nu := by
  apply Integrable.of_bound (by fun_prop) (h ^ p)
  filter_upwards [hsupport] with a ha
  simpa only [Real.norm_eq_abs, abs_pow] using
    pow_le_pow_left₀ (abs_nonneg a) ha p

private theorem smt_one_step_exp
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h : ℝ) (hh : 0 ≤ h)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (theta : ℝ) (htheta : |theta| * h ≤ 1) :
    let mu : ℝ := ∫ a : ℝ, a ∂nu
    let raw2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
    Integrable (fun a : ℝ => Real.exp (theta * a)) nu ∧
      (∫ a : ℝ, Real.exp (theta * a) ∂nu) ≤
        Real.exp (|theta| * |mu| + 2 * theta ^ 2 * raw2) := by
  have _ := hh
  dsimp only
  have h1 : Integrable (fun a : ℝ => a) nu := by
    simpa only [pow_one] using smt_power_integrable nu h hsupport 1
  have h2 := smt_power_integrable nu h hsupport 2
  have hsmall : ∀ᵐ a : ℝ ∂nu, |theta * a| ≤ 1 := by
    filter_upwards [hsupport] with a ha
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left ha (abs_nonneg theta)).trans htheta
  have hi : Integrable (fun a : ℝ => Real.exp (theta * a)) nu := by
    apply Integrable.of_bound (by fun_prop) (Real.exp 1)
    filter_upwards [hsmall] with a ha
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans ha)
  have hpoint : ∀ᵐ a : ℝ ∂nu,
      Real.exp (theta * a) ≤ 1 + theta * a + 2 * theta ^ 2 * a ^ 2 := by
    filter_upwards [hsmall] with a ha
    have hp := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le ha)).2
    nlinarith [sq_nonneg (theta * a)]
  have hb := integral_mono_ae hi
    (((integrable_const 1).add (h1.const_mul theta)).add
      (h2.const_mul (2 * theta ^ 2))) hpoint
  change (∫ a : ℝ, Real.exp (theta * a) ∂nu) ≤
    ∫ a : ℝ, 1 + theta * a + 2 * theta ^ 2 * a ^ 2 ∂nu at hb
  rw [integral_add (f := fun a : ℝ => 1 + theta * a)
      (g := fun a : ℝ => 2 * theta ^ 2 * a ^ 2)
      ((integrable_const 1).add (h1.const_mul theta))
      (h2.const_mul (2 * theta ^ 2)),
    integral_add (f := fun _a : ℝ => (1 : ℝ)) (g := fun a : ℝ => theta * a)
      (integrable_const 1) (h1.const_mul theta), integral_const_mul,
    integral_const_mul] at hb
  simp only [integral_const, probReal_univ, one_smul] at hb
  refine ⟨hi, hb.trans ?_⟩
  calc
    _ ≤ 1 + |theta| * |∫ a : ℝ, a ∂nu| +
        2 * theta ^ 2 * (∫ a : ℝ, a ^ 2 ∂nu) := by
      have hab := le_abs_self (theta * (∫ a : ℝ, a ∂nu))
      rw [abs_mul] at hab
      linarith
    _ ≤ Real.exp (|theta| * |∫ a : ℝ, a ∂nu| +
        2 * theta ^ 2 * (∫ a : ℝ, a ^ 2 ∂nu)) := by
      simpa only [add_assoc, add_comm, add_left_comm] using
        Real.add_one_le_exp (|theta| * |∫ a : ℝ, a ∂nu| +
          2 * theta ^ 2 * (∫ a : ℝ, a ^ 2 ∂nu))

private theorem smt_product_exp_energy
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h : ℝ) (hh : 0 ≤ h)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (m : ℕ) (theta : ℝ) (htheta : |theta| * h ≤ 1) :
    let mu : ℝ := ∫ a : ℝ, a ∂nu
    let raw2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
    let pi : Measure (Shao.Path m) := Measure.pi (fun _ : Fin m => nu)
    let S : Shao.Path m → ℝ := fun a => Shao.prefixSum a m
    let Q : Shao.Path m → ℝ := fun a => Shao.prefixSquares a m
    Integrable Q pi ∧
      (∫ a : Shao.Path m, Q a ∂pi) = (m : ℝ) * raw2 ∧
      Integrable (fun a : Shao.Path m => Real.exp (theta * S a)) pi ∧
      (∫ a : Shao.Path m, Real.exp (theta * S a) ∂pi) ≤
        Real.exp ((m : ℝ) * |theta| * |mu| +
          2 * theta ^ 2 * ((m : ℝ) * raw2)) := by
  classical
  let mu : ℝ := ∫ a : ℝ, a ∂nu
  let raw2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
  let pi : Measure (Shao.Path m) := Measure.pi (fun _ : Fin m => nu)
  let S : Shao.Path m → ℝ := fun a => Shao.prefixSum a m
  let Q : Shao.Path m → ℝ := fun a => Shao.prefixSquares a m
  let X : Fin m → Shao.Path m → ℝ := fun j a => a j
  have hXm (j : Fin m) : Measurable (X j) := measurable_pi_apply j
  have hLaw (j : Fin m) : IdentDistrib (X j) (id : ℝ → ℝ) pi nu := by
    refine ⟨(hXm j).aemeasurable, measurable_id.aemeasurable, ?_⟩
    exact (measurePreserving_eval (fun _ : Fin m => nu) j).map_eq.trans Measure.map_id.symm
  have hsq := smt_power_integrable nu h hsupport 2
  have hQi (j : Fin m) : Integrable (fun a : Shao.Path m => (a j) ^ 2) pi :=
    (measurePreserving_eval (fun _ : Fin m => nu) j).integrable_comp_of_integrable hsq
  have hQsum : Q = fun a : Shao.Path m => ∑ j : Fin m, (a j) ^ 2 := by
    funext a
    exact Shao.prefixSquares_length a
  have hSQ : Integrable Q pi := by
    rw [hQsum]
    exact integrable_finsetSum _ (fun j _ => hQi j)
  have hQeq : (∫ a : Shao.Path m, Q a ∂pi) = (m : ℝ) * raw2 := by
    rw [hQsum, integral_finsetSum _ (fun j _ => hQi j)]
    have he (j : Fin m) : (∫ a : Shao.Path m, (a j) ^ 2 ∂pi) = raw2 := by
      exact (hLaw j).comp (by fun_prop : Measurable (fun a : ℝ => a ^ 2)) |>.integral_eq
    simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hSsum : S = fun a : Shao.Path m => ∑ j : Fin m, X j a := by
    funext a
    exact Shao.prefixSum_length a
  have hcoord (j : Fin m) : ∀ᵐ a : Shao.Path m ∂pi, |X j a| ≤ h :=
    (measurePreserving_eval (fun _ : Fin m => nu) j).quasiMeasurePreserving.ae hsupport
  have hSi : Integrable (fun a : Shao.Path m => Real.exp (theta * S a)) pi := by
    apply Integrable.of_bound (by rw [hSsum]; fun_prop)
      (Real.exp (|theta| * ((m : ℝ) * h)))
    filter_upwards [ae_all_iff.2 hcoord] with a ha
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hsum : |S a| ≤ (m : ℝ) * h := by
      rw [hSsum]
      apply abs_le.mpr
      constructor
      · have hb := Finset.sum_le_sum (s := Finset.univ)
          (fun j _ => (abs_le.mp (ha j)).1)
        simpa using hb
      · have hb := Finset.sum_le_sum (s := Finset.univ)
          (fun j _ => (abs_le.mp (ha j)).2)
        simpa using hb
    calc
      theta * S a ≤ |theta * S a| := le_abs_self _
      _ = |theta| * |S a| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (abs_nonneg theta)
  have hind : iIndepFun X pi := iIndepFun_pi (fun _ : Fin m => measurable_id.aemeasurable)
  have hf : Measurable (fun a : ℝ => Real.exp (theta * a)) := by fun_prop
  have hfac := hind.integral_fun_prod_comp (fun j => (hXm j).aemeasurable)
    (f := fun _ a => Real.exp (theta * a)) (fun _ => hf.aestronglyMeasurable)
  have hme (j : Fin m) : (∫ a : Shao.Path m, Real.exp (theta * X j a) ∂pi) =
      ∫ a : ℝ, Real.exp (theta * a) ∂nu := (hLaw j).comp hf |>.integral_eq
  have hex : (fun a : Shao.Path m => Real.exp (theta * S a)) =
      (fun a : Shao.Path m => ∏ j : Fin m, Real.exp (theta * X j a)) := by
    funext a
    rw [hSsum, Finset.mul_sum, Real.exp_sum]
  have heq : (∫ a : Shao.Path m, Real.exp (theta * S a) ∂pi) =
      (∫ a : ℝ, Real.exp (theta * a) ∂nu) ^ m := by
    rw [hex, hfac]
    simp only [hme, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  obtain ⟨_, hb⟩ := smt_one_step_exp nu h hh hsupport theta htheta
  refine ⟨hSQ, hQeq, hSi, ?_⟩
  rw [heq]
  calc
    _ ≤ (Real.exp (|theta| * |mu| + 2 * theta ^ 2 * raw2)) ^ m :=
      pow_le_pow_left₀ (integral_nonneg fun a => (Real.exp_pos _).le) hb m
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

private theorem smt_exp_markov
    {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (S : Ω → ℝ) (theta r : ℝ) (htheta : 0 < theta)
    (hi : Integrable (fun a : Ω => Real.exp (theta * S a)) mu) :
    mu.real {a : Ω | r ≤ S a} ≤
      Real.exp (-theta * r) * (∫ a : Ω, Real.exp (theta * S a) ∂mu) := by
  have hsub : {a : Ω | r ≤ S a} ⊆
      {a : Ω | Real.exp (theta * r) ≤ Real.exp (theta * S a)} := by
    intro a ha
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ha htheta.le)
  have hm : mu.real {a : Ω | r ≤ S a} ≤
      mu.real {a : Ω | Real.exp (theta * r) ≤ Real.exp (theta * S a)} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all mu (fun a => (Real.exp_pos (theta * S a)).le)) hi (Real.exp (theta * r))
  have hb : mu.real {a : Ω | r ≤ S a} * Real.exp (theta * r) ≤
      ∫ a : Ω, Real.exp (theta * S a) ∂mu := by
    exact (mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le).trans (by
      simpa only [mul_comm] using hmark)
  calc
    _ ≤ (∫ a : Ω, Real.exp (theta * S a) ∂mu) / Real.exp (theta * r) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr hb
    _ = _ := by rw [show -theta * r = -(theta * r) by ring, Real.exp_neg]; ring

private theorem smt_product_abs_tail
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h : ℝ) (hh : 0 ≤ h)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (m : ℕ) (theta r : ℝ)
    (hthetaPos : 0 < theta) (hr : 0 < r)
    (htheta : theta * h ≤ 1) :
    let mu : ℝ := ∫ a : ℝ, a ∂nu
    let raw2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
    let pi : Measure (Shao.Path m) := Measure.pi (fun _ : Fin m => nu)
    let S : Shao.Path m → ℝ := fun a => Shao.prefixSum a m
    pi.real {a : Shao.Path m | r ≤ |S a|} ≤
      2 * Real.exp ((m : ℝ) * theta * |mu| +
        2 * theta ^ 2 * ((m : ℝ) * raw2) - theta * r) := by
  have _ := hr
  let mu : ℝ := ∫ a : ℝ, a ∂nu
  let raw2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
  let pi : Measure (Shao.Path m) := Measure.pi (fun _ : Fin m => nu)
  let S : Shao.Path m → ℝ := fun a => Shao.prefixSum a m
  have hp := smt_product_exp_energy nu h hh hsupport m theta (by
    simpa only [abs_of_pos hthetaPos] using htheta)
  have hn := smt_product_exp_energy nu h hh hsupport m (-theta) (by
    simpa only [abs_neg, abs_of_pos hthetaPos] using htheta)
  obtain ⟨_, _, hpi, hpb⟩ := hp
  obtain ⟨_, _, hni, hnb⟩ := hn
  change Integrable (fun a : Shao.Path m => Real.exp (theta * S a)) pi at hpi
  change (∫ a : Shao.Path m, Real.exp (theta * S a) ∂pi) ≤
    Real.exp ((m : ℝ) * |theta| * |mu| + 2 * theta ^ 2 * ((m : ℝ) * raw2)) at hpb
  change Integrable (fun a : Shao.Path m => Real.exp ((-theta) * S a)) pi at hni
  change (∫ a : Shao.Path m, Real.exp ((-theta) * S a) ∂pi) ≤
    Real.exp ((m : ℝ) * |-theta| * |mu| + 2 * (-theta) ^ 2 * ((m : ℝ) * raw2)) at hnb
  simp only [abs_neg, abs_of_pos hthetaPos, neg_sq] at hpb hnb
  have hpmark := smt_exp_markov pi S theta r hthetaPos hpi
  have hnmark := smt_exp_markov pi (fun a => -S a) theta r hthetaPos (by
    simpa only [mul_neg, neg_mul] using hni)
  have hneg : (∫ a : Shao.Path m, Real.exp (theta * (-S a)) ∂pi) =
      ∫ a : Shao.Path m, Real.exp ((-theta) * S a) ∂pi := by
    congr 1
    funext a
    congr 1
    ring
  rw [hneg] at hnmark
  have hpbound := hpmark.trans (mul_le_mul_of_nonneg_left hpb (Real.exp_pos _).le)
  have hnbound := hnmark.trans (mul_le_mul_of_nonneg_left hnb (Real.exp_pos _).le)
  have hevent : {a : Shao.Path m | r ≤ |S a|} =
      {a : Shao.Path m | r ≤ S a} ∪ {a : Shao.Path m | r ≤ -S a} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_union, le_abs]
  change pi.real {a : Shao.Path m | r ≤ |S a|} ≤ _
  rw [hevent]
  calc
    _ ≤ pi.real {a : Shao.Path m | r ≤ S a} +
        pi.real {a : Shao.Path m | r ≤ -S a} := measureReal_union_le _ _
    _ ≤ 2 * (Real.exp (-theta * r) *
        Real.exp ((m : ℝ) * theta * |mu| + 2 * theta ^ 2 * ((m : ℝ) * raw2))) := by
      linarith only [hpbound, hnbound]
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

private theorem smt_constant_guards
    (L2 epsilon0 : ℝ) (hL2 : 0 < L2) (hepsilon0 : 0 < epsilon0)
    (hbound : epsilon0 ≤ 1 / (192 * Real.sqrt (L2 + 1))) :
    epsilon0 ≤ 1 / 192 ∧ 8192 * L2 * epsilon0 ^ 2 ≤ 1 / 2 := by
  have hLp : 0 < L2 + 1 := by linarith
  have hs := Real.sq_sqrt hLp.le
  have hsn := Real.sqrt_nonneg (L2 + 1)
  have hs1 : 1 ≤ Real.sqrt (L2 + 1) := by nlinarith
  have hden : 0 < 192 * Real.sqrt (L2 + 1) := by positivity
  have he : epsilon0 ≤ (1 / 192 : ℝ) := hbound.trans (by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith only [hs1])
  have hb := (le_div_iff₀ hden).mp hbound
  have hb2 := pow_le_pow_left₀ (mul_nonneg hepsilon0.le hden.le) hb 2
  rw [mul_pow, mul_pow, hs] at hb2
  norm_num at hb2
  refine ⟨he, ?_⟩
  nlinarith only [hb2, sq_nonneg epsilon0]

theorem sourceTruncation_growing_microtime_abs_tail
    (L2 epsilon0 : ℝ) (hL2 : 0 < L2)
    (hepsilon0 : 0 < epsilon0)
    (hepsilon0Bound : epsilon0 ≤ 1 / (192 * Real.sqrt (L2 + 1)))
    (nu0 : Measure ℝ) [IsProbabilityMeasure nu0] (n : ℕ)
    (h2 : Integrable (fun a : ℝ => a ^ 2) nu0)
    (hnorm : (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu0) = 1)
    (hmean : (∫ a : ℝ, a ∂nu0) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ epsilon0 / 2)
    (hR : Shao.truncationBudget nu0 n x ≤ epsilon ^ 3 / 8)
    (y : ℝ) (hy : 2 ≤ y)
    (hwindow : |y - x| ≤ 1 / (2 * (1 + x)))
    (m : ℕ) (hm : m ≤ n) :
    let nu : Measure ℝ := ProbabilityTheory.cond nu0
      {a : ℝ | |a| ≤ epsilon / (1 + x)}
    let raw2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
    let V : ℝ := ProbabilityTheory.variance (id : ℝ → ℝ) nu
    let gamma : ℝ := m3 / V
    let T : ℝ := (m : ℝ) * raw2
    let pi : Measure (Shao.Path m) := Measure.pi (fun _ : Fin m => nu)
    let C : ℝ := 2 * Real.exp 17
    T ≤ L2 * gamma ^ 2 →
      Integrable (fun a : Shao.Path m => Shao.prefixSquares a m) pi ∧
      (∫ a : Shao.Path m, Shao.prefixSquares a m ∂pi) = T ∧
      pi.real {a : Shao.Path m | y / 8 ≤ |Shao.prefixSum a m|} ≤
        C * Real.exp (-4 * y ^ 2) := by
  let nu : Measure ℝ := ProbabilityTheory.cond nu0
    {a : ℝ | |a| ≤ epsilon / (1 + x)}
  let raw2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
  let V : ℝ := ProbabilityTheory.variance (id : ℝ → ℝ) nu
  let gamma : ℝ := m3 / V
  let T : ℝ := (m : ℝ) * raw2
  let pi : Measure (Shao.Path m) := Measure.pi (fun _ : Fin m => nu)
  let C : ℝ := 2 * Real.exp 17
  let hcut : ℝ := epsilon / (1 + x)
  let h : ℝ := epsilon0 / (1 + y)
  let mu : ℝ := ∫ a : ℝ, a ∂nu
  let R : ℝ := Shao.truncationBudget nu0 n x
  let Lambda : ℝ := (1 + y) * (n : ℝ) * |mu| +
    (1 + y) ^ 3 * (n : ℝ) * m3
  let lambda0 : ℝ := 32 * (1 + y)
  change T ≤ L2 * gamma ^ 2 → _
  intro hclock
  obtain ⟨he0, hquadratic⟩ := smt_constant_guards L2 epsilon0 hL2 hepsilon0 hepsilon0Bound
  have heHalf : epsilon ≤ (1 / 2 : ℝ) := by linarith
  have hxp : 0 < 1 + x := by linarith
  have hyp : 0 < 1 + y := by linarith
  have hh : 0 < h := div_pos hepsilon0 hyp
  have hhalf : 1 / (2 * (1 + x)) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (show 0 < 2 * (1 + x) by positivity)).mpr
    linarith
  have hratio : 1 + y ≤ 2 * (1 + x) := by
    have hu := (abs_le.mp hwindow).2
    linarith
  have hcutH : hcut ≤ h := by
    apply (div_le_div_iff₀ hxp hyp).mpr
    calc
      epsilon * (1 + y) ≤ (epsilon0 / 2) * (1 + y) :=
        mul_le_mul_of_nonneg_right hepsilonSmall hyp.le
      _ ≤ (epsilon0 / 2) * (2 * (1 + x)) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = epsilon0 * (1 + x) := by ring
  have hwindowFull : |y - x| ≤ 1 / (1 + x) := hwindow.trans (by
    apply one_div_le_one_div_of_le hxp
    linarith)
  obtain ⟨_, _, hprob, hsx, _, _, _, _⟩ :=
    Shao.sourceTruncation_law_data nu0 n h2 hnorm x epsilon hx hepsilon heHalf hR
  change IsProbabilityMeasure nu at hprob
  letI : IsProbabilityMeasure nu := hprob
  change ∀ᵐ a : ℝ ∂nu, |a| ≤ hcut at hsx
  have hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h := hsx.mono fun a ha => ha.trans hcutH
  obtain ⟨hm3p, hgp, _, _, hgcut, _, _, _, _⟩ :=
    Shao.sourceTruncation_gamma_bounds nu0 n h2 hnorm hmean x epsilon hx hepsilon heHalf hR
  change 0 < m3 at hm3p
  change 0 < gamma at hgp
  change gamma ≤ 2 * hcut at hgcut
  have hgamma : gamma ≤ 2 * h := hgcut.trans (mul_le_mul_of_nonneg_left hcutH (by norm_num))
  obtain ⟨_, _, hLambda, _⟩ := Shao.sourceTruncation_nearby_payment
    nu0 n h2 hnorm hmean x epsilon hx hepsilon heHalf hR y (by linarith) hwindowFull
  change Lambda ≤ 20 * R / epsilon ^ 2 at hLambda
  have hRdiv : 20 * R / epsilon ^ 2 ≤ (5 / 2 : ℝ) * epsilon := by
    apply (div_le_iff₀ (sq_pos_of_pos hepsilon)).mpr
    change Shao.truncationBudget nu0 n x ≤ epsilon ^ 3 / 8 at hR
    dsimp [R]
    nlinarith only [hR]
  have hLambdaHalf : Lambda ≤ (1 / 2 : ℝ) := by
    have hb := hLambda.trans hRdiv
    linarith
  have hlambdaPos : 0 < lambda0 := by dsimp [lambda0]; positivity
  have hlambdaSmall : lambda0 * h ≤ 1 := by
    have heq : lambda0 * h = 32 * epsilon0 := by
      dsimp [lambda0, h]
      field_simp
    rw [heq]
    linarith
  have htheta : |lambda0| * h ≤ 1 := by
    simpa only [abs_of_pos hlambdaPos] using hlambdaSmall
  obtain ⟨hQi, hQeq, _, _⟩ := smt_product_exp_energy nu h hh.le hsupport m lambda0 htheta
  change Integrable (fun a : Shao.Path m => Shao.prefixSquares a m) pi at hQi
  change (∫ a : Shao.Path m, Shao.prefixSquares a m ∂pi) = T at hQeq
  refine ⟨hQi, hQeq, ?_⟩
  change pi.real {a : Shao.Path m | y / 8 ≤ |Shao.prefixSum a m|} ≤ C * Real.exp (-4 * y ^ 2)
  by_cases hm0 : m = 0
  · subst m
    have hempty : {a : Shao.Path 0 | y / 8 ≤ |Shao.prefixSum a 0|} = ∅ := by
      ext a
      simp only [Shao.prefixSum_zero, abs_zero, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false]
      linarith
    rw [hempty]
    simp only [measureReal_empty]
    dsimp [C]
    positivity
  · have hmcast : (m : ℝ) ≤ n := by exact_mod_cast hm
    have hmuMono := mul_le_mul_of_nonneg_right hmcast (abs_nonneg mu)
    have hLambdaLower : (1 + y) * (n : ℝ) * |mu| ≤ Lambda := by
      dsimp [Lambda]
      have hterm : 0 ≤ (1 + y) ^ 3 * (n : ℝ) * m3 := by positivity
      linarith only [hterm]
    have hdrift : (m : ℝ) * lambda0 * |mu| ≤ 16 := by
      calc
        _ = 32 * ((1 + y) * ((m : ℝ) * |mu|)) := by dsimp [lambda0]; ring
        _ ≤ 32 * ((1 + y) * ((n : ℝ) * |mu|)) := by
          gcongr
        _ ≤ 32 * Lambda := by
          gcongr
          simpa only [mul_assoc] using hLambdaLower
        _ ≤ 16 := by linarith only [hLambdaHalf]
    have hgammaSq : gamma ^ 2 ≤ (2 * h) ^ 2 :=
      pow_le_pow_left₀ hgp.le hgamma 2
    have hquad : 2 * lambda0 ^ 2 * T ≤ (1 / 2 : ℝ) := by
      calc
        _ ≤ 2 * lambda0 ^ 2 * (L2 * gamma ^ 2) :=
          mul_le_mul_of_nonneg_left hclock (by positivity)
        _ ≤ 2 * lambda0 ^ 2 * (L2 * (2 * h) ^ 2) := by
          gcongr
        _ = 8192 * L2 * epsilon0 ^ 2 := by
          dsimp [lambda0, h]
          field_simp
          ring
        _ ≤ (1 / 2 : ℝ) := hquadratic
    have htail := smt_product_abs_tail nu h hh.le hsupport m lambda0 (y / 8)
      hlambdaPos (by positivity) hlambdaSmall
    change pi.real {a : Shao.Path m | y / 8 ≤ |Shao.prefixSum a m|} ≤
      2 * Real.exp ((m : ℝ) * lambda0 * |mu| + 2 * lambda0 ^ 2 * T - lambda0 * (y / 8)) at htail
    calc
      _ ≤ 2 * Real.exp ((m : ℝ) * lambda0 * |mu| +
          2 * lambda0 ^ 2 * T - lambda0 * (y / 8)) := htail
      _ ≤ 2 * Real.exp (17 - 4 * y ^ 2) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        dsimp only [lambda0] at hdrift hquad ⊢
        nlinarith only [hdrift, hquad, hy]
      _ = C * Real.exp (-4 * y ^ 2) := by
        dsimp [C]
        rw [show 17 - 4 * y ^ 2 = 17 + (-4 * y ^ 2) by ring, Real.exp_add]
        ring

end Shao.Probability
