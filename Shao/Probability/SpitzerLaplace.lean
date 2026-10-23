import Shao.Probability.SpitzerFinite
import Shao.OQ4.FiniteSurvivalLaplace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Spitzer's identity for the actual finite iid product laws

The finite labelled identity is integrated before fixed-coordinate invariance is
used. No sample-dependent permutation is claimed to preserve a probability law.
-/

noncomputable section

namespace Shao.Probability

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Topology

private theorem spitzer_integral_reorder (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (F : Shao.Path n → ℝ) :
    (∫ a : Shao.Path n, F (Spitzer.reorder a σ)
      ∂Measure.pi (fun _ : Fin n => ν)) =
        ∫ a : Shao.Path n, F a ∂Measure.pi (fun _ : Fin n => ν) := by
  have h := (measurePreserving_piCongrLeft (fun _ : Fin n => ν) σ).symm
  exact h.integral_comp' F

theorem spitzer_reordered_maximum_integral (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (n : ℕ) {L : ℝ} (hL : 0 < L)
    (σ : Equiv.Perm (Fin n)) :
    (∫ a : Shao.Path n,
      Real.exp (-Shao.maxWithZero (Spitzer.reorder a σ) / L)
      ∂Measure.pi (fun _ : Fin n => ν)) =
        Shao.OQ4.maxLaplaceMean ν L n := by
  exact spitzer_integral_reorder ν n σ (Shao.OQ4.maxLaplaceIntegrand L)

private theorem spitzer_head_tail_measurePreserving (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (n k : ℕ) (hk : k ≤ n) :
    MeasurePreserving (fun a : Shao.Path n => (Spitzer.head a k hk, Spitzer.tail a k hk))
      (Measure.pi (fun _ : Fin n => ν))
      ((Measure.pi (fun _ : Fin k => ν)).prod
        (Measure.pi (fun _ : Fin (n-k) => ν))) := by
  let e : Fin k ⊕ Fin (n-k) ≃ Fin n :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hk))
  have h₁ := (measurePreserving_piCongrLeft (fun _ : Fin n => ν) e).symm
  have h₂ := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin k ⊕ Fin (n-k) => ν)
  convert h₂.comp h₁ using 1
  ext a i <;> change a _ = a _ <;> congr 1

theorem spitzer_head_tail_integral (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (n k : ℕ) (hk : k ≤ n)
    {L : ℝ} (hL : 0 < L) :
    (∫ a : Shao.Path n,
      Real.exp (-max (Shao.prefixSum a k) 0 / L) *
        Real.exp (-Shao.maxWithZero (Spitzer.tail a k hk) / L)
      ∂Measure.pi (fun _ : Fin n => ν)) =
        Shao.OQ4.endpointLaplaceMean ν L k *
          Shao.OQ4.maxLaplaceMean ν L (n - k) := by
  have hm := spitzer_head_tail_measurePreserving ν n k hk
  have hmeas : Measurable (fun a : Shao.Path n =>
      (Spitzer.head a k hk, Spitzer.tail a k hk)) := hm.measurable
  have hf : Measurable (fun z : Shao.Path k × Shao.Path (n-k) =>
      Shao.OQ4.endpointLaplaceIntegrand L z.1 * Shao.OQ4.maxLaplaceIntegrand L z.2) :=
    ((Shao.OQ4.measurable_endpointLaplaceIntegrand k L).comp measurable_fst).mul
      ((Shao.OQ4.measurable_maxLaplaceIntegrand (n-k) L).comp measurable_snd)
  have hi := integral_map (μ := Measure.pi (fun _ : Fin n => ν))
    hmeas.aemeasurable hf.aestronglyMeasurable
  rw [hm.map_eq] at hi
  calc
    _ = ∫ a : Shao.Path n,
        Shao.OQ4.endpointLaplaceIntegrand L (Spitzer.head a k hk) *
          Shao.OQ4.maxLaplaceIntegrand L (Spitzer.tail a k hk)
        ∂Measure.pi (fun _ : Fin n => ν) := by
      apply integral_congr_ae
      exact ae_of_all _ fun a => by
        simp only [Shao.OQ4.endpointLaplaceIntegrand, Shao.OQ4.maxLaplaceIntegrand,
          Spitzer.head_prefixSum a k hk k le_rfl]
    _ = _ := hi.symm.trans (integral_prod_mul _ _)

private theorem spitzer_integrable_cut (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n k : ℕ) (hk : k ≤ n) {L : ℝ} (hL : 0 < L) :
    Integrable (fun a : Shao.Path n =>
      Real.exp (-max (Shao.prefixSum a k) 0 / L) *
        Real.exp (-Shao.maxWithZero (Spitzer.tail a k hk) / L))
      (Measure.pi (fun _ : Fin n => ν)) := by
  have ht : Measurable (fun a : Shao.Path n => Spitzer.tail a k hk) :=
    Measurable.of_eval (fun i => measurable_pi_apply _)
  have hm : Measurable (fun a : Shao.Path n =>
      Real.exp (-max (Shao.prefixSum a k) 0 / L) *
        Real.exp (-Shao.maxWithZero (Spitzer.tail a k hk) / L)) :=
    (Real.measurable_exp.comp (((Shao.measurable_prefixSum k).max
      measurable_const).neg.div_const L)).mul
        ((Shao.OQ4.measurable_maxLaplaceIntegrand (n-k) L).comp ht)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  apply ae_of_all
  intro a
  have hh := Shao.OQ4.endpointLaplaceIntegrand_bounds hL (Spitzer.head a k hk)
  have htail := Shao.OQ4.maxLaplaceIntegrand_bounds hL (Spitzer.tail a k hk)
  simp only [Shao.OQ4.endpointLaplaceIntegrand,
    Spitzer.head_prefixSum a k hk k le_rfl] at hh
  change ‖_ * Shao.OQ4.maxLaplaceIntegrand L (Spitzer.tail a k hk)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hh.1 htail.1)]
  exact (mul_le_mul hh.2 htail.2 htail.1 (by norm_num)).trans_eq (one_mul 1)

theorem actual_maximum_laplace_recurrence (ν : Measure ℝ)
    [IsProbabilityMeasure ν] {L : ℝ} (hL : 0 < L) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * Shao.OQ4.maxLaplaceMean ν L (n + 1) =
      ∑ j ∈ Finset.range (n + 1),
        Shao.OQ4.endpointLaplaceMean ν L (j + 1) *
          Shao.OQ4.maxLaplaceMean ν L (n - j) := by
  classical
  let P := Equiv.Perm (Fin (n+1))
  let μ := Measure.pi (fun _ : Fin (n+1) => ν)
  have hr (σ : P) : MeasurePreserving (Spitzer.reorder · σ) μ μ :=
    (measurePreserving_piCongrLeft (fun _ : Fin (n+1) => ν) σ).symm
  have hmi (σ : P) : Integrable (fun a : Shao.Path (n+1) =>
      Real.exp (-Shao.maxWithZero (Spitzer.reorder a σ) / L)) μ :=
    (hr σ).integrable_comp_of_integrable (Shao.OQ4.integrable_maxLaplaceIntegrand ν (n+1) hL)
  have hci (k : Fin (n+1)) (σ : P) : Integrable (fun a : Shao.Path (n+1) =>
      Real.exp (-max (Shao.prefixSum (Spitzer.reorder a σ) (k.val+1)) 0 / L) *
        Real.exp (-Shao.maxWithZero
          (Spitzer.tail (Spitzer.reorder a σ) (k.val+1) (Nat.succ_le_of_lt k.is_lt)) / L)) μ :=
    (hr σ).integrable_comp_of_integrable
      (spitzer_integrable_cut ν (n+1) (k.val+1) (Nat.succ_le_of_lt k.is_lt) hL)
  have he := integral_congr_ae (μ := μ) (ae_of_all μ
    (fun a => Spitzer.finite_spitzer_cut_identity (n+1) a L))
  rw [integral_const_mul, integral_finsetSum _ (fun σ _ => hmi σ),
    integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun σ _ => hci k σ))] at he
  simp_rw [integral_finsetSum _ (fun σ _ => hci _ σ)] at he
  have hint (k : Fin (n+1)) (σ : P) :
      (∫ a : Shao.Path (n+1),
        Real.exp (-max (Shao.prefixSum (Spitzer.reorder a σ) (k.val+1)) 0 / L) *
          Real.exp (-Shao.maxWithZero
            (Spitzer.tail (Spitzer.reorder a σ) (k.val+1) (Nat.succ_le_of_lt k.is_lt)) / L) ∂μ) =
        Shao.OQ4.endpointLaplaceMean ν L (k.val+1) *
          Shao.OQ4.maxLaplaceMean ν L (n-k.val) := by
    have hinv := spitzer_integral_reorder ν (n+1) σ (fun a =>
      Real.exp (-max (Shao.prefixSum a (k.val+1)) 0 / L) *
        Real.exp (-Shao.maxWithZero (Spitzer.tail a (k.val+1) (Nat.succ_le_of_lt k.is_lt)) / L))
    apply hinv.trans
    have hsub : n+1-(k.val+1) = n-k.val := by omega
    simpa only [hsub] using spitzer_head_tail_integral ν (n+1) (k.val+1)
      (Nat.succ_le_of_lt k.is_lt) hL
  have hmax (σ : P) : (∫ a : Shao.Path (n+1),
      Real.exp (-Shao.maxWithZero (Spitzer.reorder a σ) / L) ∂μ) =
      Shao.OQ4.maxLaplaceMean ν L (n+1) :=
    spitzer_reordered_maximum_integral ν (n+1) hL σ
  simp only [hmax, hint,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at he
  have hcard : (Fintype.card P : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (show Nonempty P from inferInstance)).ne'
  have he' : ((n+1 : ℕ) : ℝ) * Shao.OQ4.maxLaplaceMean ν L (n+1) =
      ∑ k : Fin (n+1), Shao.OQ4.endpointLaplaceMean ν L (k.val+1) *
        Shao.OQ4.maxLaplaceMean ν L (n-k.val) := by
    apply (mul_left_cancel₀ hcard)
    rw [Finset.mul_sum]
    nlinarith [he]
  exact he'.trans (Fin.sum_univ_eq_sum_range
    (fun j => Shao.OQ4.endpointLaplaceMean ν L (j+1) *
      Shao.OQ4.maxLaplaceMean ν L (n-j)) (n+1))

private theorem spitzer_summable_norm_coeff (c : ℕ → ℝ)
    (hc : ∀ n, ‖c n‖ ≤ 1) {x : ℝ} (hx : |x| < 1) :
    Summable (fun n : ℕ => ‖x^n * c n‖) := by
  apply (summable_geometric_of_lt_one (abs_nonneg x) hx).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro n
  rw [norm_mul, norm_pow, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (pow_nonneg (abs_nonneg x) n) (hc n)

private theorem spitzer_hasDerivAt_shiftSeries (c : ℕ → ℝ)
    (hc : ∀ n, ‖c n‖ ≤ 1) {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (fun y : ℝ => ∑' n : ℕ, y^(n+1) * c n)
      (∑' n : ℕ, (n+1 : ℝ) * x^n * c n) x := by
  let r : ℝ := (|x|+1)/2
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hxr : |x| < r := by dsimp [r]; linarith
  have hr1 : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hr0]; dsimp [r]; linarith
  have hu : Summable (fun n : ℕ => (n+1 : ℝ)*r^n) := by
    convert (summable_pow_mul_geometric_of_norm_lt_one 1 hr1).add
      (summable_geometric_of_norm_lt_one hr1) using 1
    ext n
    simp [pow_one, add_mul]
  apply hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo (convex_Ioo (-r) r).isPreconnected
    (g' := fun (n : ℕ) (y : ℝ) => (n+1 : ℝ)*y^n*c n) (y₀ := 0)
  · intro n y hy
    convert (hasDerivAt_pow (n+1) y).mul_const (c n) using 1 <;> simp
  · intro n y hy
    have hyr : |y| ≤ r := (abs_lt.mpr hy).le
    rw [norm_mul, norm_mul, norm_pow, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n+1)]
    calc
      ((n+1 : ℝ)*|y|^n)*‖c n‖ ≤ ((n+1 : ℝ)*r^n)*1 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg y) hyr n) (by positivity)
        · exact hc n
        · exact norm_nonneg _
        · positivity
      _ = _ := mul_one _
  · exact ⟨by linarith, hr0⟩
  · simp
  · exact abs_lt.mp hxr

private theorem spitzer_hasDerivAt_logSeries (c : ℕ → ℝ)
    (hc : ∀ n, ‖c n‖ ≤ 1) {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (fun y : ℝ => ∑' n : ℕ, y^(n+1)*c n/(n+1))
      (∑' n : ℕ, x^n*c n) x := by
  let r : ℝ := (|x|+1)/2
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hxr : |x| < r := by dsimp [r]; linarith
  have hr1 : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hr0]; dsimp [r]; linarith
  apply hasDerivAt_tsum_of_isPreconnected (summable_geometric_of_norm_lt_one hr1)
    isOpen_Ioo (convex_Ioo (-r) r).isPreconnected
    (g' := fun n y => y^n*c n) (y₀ := 0)
  · intro n y hy
    convert ((hasDerivAt_pow (n+1) y).mul_const (c n)).div_const (n+1 : ℝ) using 1
    simp only [Nat.add_sub_cancel]
    field_simp
    simp
  · intro n y hy
    rw [norm_mul, norm_pow, Real.norm_eq_abs]
    calc
      |y|^n * ‖c n‖ ≤ r^n*1 :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg y) (abs_lt.mpr hy).le n)
          (hc n) (norm_nonneg _) (pow_nonneg hr0.le n)
      _ = _ := mul_one _
  · exact ⟨by linarith, hr0⟩
  · simp
  · exact abs_lt.mp hxr

theorem laplace_identity_of_bounded_recurrence (a b : ℕ → ℝ)
    (ha0 : a 0 = 1)
    (ha : ∀ n : ℕ, 0 ≤ a n ∧ a n ≤ 1)
    (hb : ∀ n : ℕ, 1 ≤ n → 0 ≤ b n ∧ b n ≤ 1)
    (hrec : ∀ n : ℕ,
      ((n + 1 : ℕ) : ℝ) * a (n + 1) =
        ∑ j ∈ Finset.range (n + 1), b (j + 1) * a (n - j))
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Shao.OQ4.laplaceG a s = Real.exp (Shao.OQ4.laplaceW b s) := by
  let A : ℝ → ℝ := fun x => a 0 + ∑' n : ℕ, x^(n+1)*a (n+1)
  let W : ℝ → ℝ := fun x => ∑' n : ℕ, x^(n+1)*b (n+1)/(n+1)
  let DA : ℝ → ℝ := fun x => ∑' n : ℕ, (n+1 : ℝ)*x^n*a (n+1)
  let DW : ℝ → ℝ := fun x => ∑' n : ℕ, x^n*b (n+1)
  have hna (n : ℕ) : ‖a n‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (ha n).1]
    exact (ha n).2
  have hnb (n : ℕ) : ‖b (n+1)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hb (n+1) (by omega)).1]
    exact (hb (n+1) (by omega)).2
  have hAeq (x : ℝ) (hx : |x| < 1) :
      A x = ∑' n : ℕ, x^n*a n := by
    have h := (spitzer_summable_norm_coeff a hna hx).of_norm.tsum_eq_zero_add
    simpa only [pow_zero, one_mul] using h.symm
  have hA (x : ℝ) (hx : |x| < 1) : HasDerivAt A (DA x) x :=
    (spitzer_hasDerivAt_shiftSeries (fun n => a (n+1)) (fun n => hna (n+1)) hx).const_add (a 0)
  have hW (x : ℝ) (hx : |x| < 1) : HasDerivAt W (DW x) x :=
    spitzer_hasDerivAt_logSeries (fun n => b (n+1)) hnb hx
  have hprod (x : ℝ) (hx : |x| < 1) : DW x * A x = DA x := by
    rw [hAeq x hx]
    have h := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
      (spitzer_summable_norm_coeff (fun n => b (n+1)) hnb hx)
      (spitzer_summable_norm_coeff a hna hx)
    change (∑' n, x^n*b (n+1)) * (∑' n, x^n*a n) = _
    rw [h]
    apply tsum_congr
    intro n
    calc
      (∑ j ∈ Finset.range (n+1), (x^j*b (j+1))*(x^(n-j)*a (n-j))) =
          x^n * ∑ j ∈ Finset.range (n+1), b (j+1)*a (n-j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        rw [show (x^j*b (j+1))*(x^(n-j)*a (n-j)) =
          (x^j*x^(n-j))*(b (j+1)*a (n-j)) by ring,
          ← pow_add, Nat.add_sub_of_le hjn]
      _ = (n+1 : ℝ)*x^n*a (n+1) := by rw [← hrec n]; push_cast; ring
  let F : ℝ → ℝ := fun x => A x * Real.exp (-W x)
  have hF (x : ℝ) (hx : |x| < 1) : HasDerivAt F 0 x := by
    convert (hA x hx).mul ((hW x hx).neg.exp) using 1
    rw [← hprod x hx]
    ring
  have hconst : F s = F 0 := by
    apply isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-1 : ℝ) 1).isPreconnected
      (fun x hx => (hF x (abs_lt.mpr hx)).differentiableAt.differentiableWithinAt)
      (fun x hx => (hF x (abs_lt.mpr hx)).deriv)
    · exact ⟨by linarith, hs1⟩
    · norm_num
  have hzero : F 0 = 1 := by simp [F, A, W, ha0]
  have he : A s * Real.exp (-W s) = 1 := hconst.trans hzero
  have htarget : A s = Real.exp (W s) := by
    have he' := congrArg (fun z : ℝ => z*Real.exp (W s)) he
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one, one_mul] at he'
    exact he'
  change Shao.OQ4.laplaceG a s = Real.exp (W s)
  rw [← htarget, hAeq s (by rwa [abs_of_pos hs0])]
  rfl

theorem actual_maximum_spitzer_laplace (ν : Measure ℝ)
    [IsProbabilityMeasure ν] {L s : ℝ}
    (hL : 0 < L) (hs0 : 0 < s) (hs1 : s < 1) :
    Shao.OQ4.laplaceG (Shao.OQ4.maxLaplaceMean ν L) s =
      Real.exp (Shao.OQ4.laplaceW (Shao.OQ4.endpointLaplaceMean ν L) s) := by
  apply laplace_identity_of_bounded_recurrence
    (Shao.OQ4.maxLaplaceMean ν L) (Shao.OQ4.endpointLaplaceMean ν L)
    (Shao.OQ4.maxLaplaceMean_zero ν L)
    (fun n => Shao.OQ4.maxLaplaceMean_bounds ν n hL)
    (fun n _ => Shao.OQ4.endpointLaplaceMean_bounds ν n hL)
    (actual_maximum_laplace_recurrence ν hL) hs0 hs1

end Shao.Probability
