/- Actual iid finite-variance closed survival and true-energy concentration. -/
import Shao.Probability.FiniteSurvival
import Shao.Probability.SourceSmallBoundary
import Shao.Probability.TruncationRegularity
import Shao.Probability.FiniteIID

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Shao.Probability
open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem tes_drift_bound
    (N : ℕ) (mu V : ℝ) (hN : 0 < (N : ℝ)) (hV : 0 < V)
    (hmu : (N : ℝ) * |mu| ≤ 1 / 8)
    (hNV : (1 / 2 : ℝ) ≤ (N : ℝ) * V) :
    |mu| * Real.sqrt (N : ℝ) / Real.sqrt V ≤ 1 / 4 := by
  have hmusq := pow_le_pow_left₀ (mul_nonneg hN.le (abs_nonneg mu)) hmu 2
  rw [mul_pow, sq_abs] at hmusq
  have hsmall : 16 * mu ^ 2 * (N : ℝ) ≤ V := by
    by_contra hh
    have hpos := mul_pos hN (sub_pos.mpr (lt_of_not_ge hh))
    nlinarith only [hmusq, hNV, hpos]
  have hroot : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  apply (div_le_iff₀ hroot).2
  apply (sq_le_sq₀ (by positivity) (by positivity)).1
  rw [mul_pow, sq_abs, Real.sq_sqrt (Nat.cast_nonneg N), mul_pow,
    Real.sq_sqrt hV.le]
  nlinarith only [hsmall]

private theorem tes_small_closed_upper
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hR : Shao.truncationBudget nu n 0 ≤ (1 / 800 : ℝ) ^ 3 / 8) :
    ∀ u : ℝ, 0 ≤ u →
      (Measure.pi (fun _ : Fin n => nu)).real
        {v : Shao.Path n | Shao.maxWithZero v ≤ u} ≤
        (128 * Real.exp (7 + 3 * (1024 : ℝ)) + 1 / (1 / 800 : ℝ) ^ 3) *
          (u + Shao.truncationBudget nu n 0) := by
  classical
  let e : ℝ := 1 / 800
  let R : ℝ := Shao.truncationBudget nu n 0
  let S : ℝ := 128 * Real.exp (7 + 3 * (1024 : ℝ))
  let rho : Measure ℝ := cond nu {z : ℝ | |z| ≤ e}
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
  let P0 : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let mu : ℝ := ∫ z : ℝ, z ∂rho
  let V : ℝ := variance (id : ℝ → ℝ) rho
  let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
  let m3c : ℝ := ∫ z : ℝ, |z - mu| ^ 3 ∂rho
  have he : 0 < e := by norm_num [e]
  have heHalf : e ≤ 1 / 2 := by norm_num [e]
  have hR' : R ≤ e ^ 3 / 8 := hR
  have hR0 : 0 ≤ R := Shao.truncationBudget_nonneg nu n h2 0
  have hNp : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlaw := Shao.sourceTruncation_law_data nu n h2 hnorm 0 e (by norm_num)
    he heHalf hR'
  simp only [add_zero, div_one] at hlaw
  have hp : IsProbabilityMeasure rho := hlaw.2.2.1
  letI : IsProbabilityMeasure rho := hp
  have h3r : Integrable (fun z : ℝ => |z| ^ 3) rho := hlaw.2.2.2.2.2.2.1
  have hpaid := Shao.sourceTruncation_paid_moments nu n h2 hnorm hmean 0 e
    (by norm_num) he heHalf hR'
  simp only [add_zero, div_one, mul_one, one_pow] at hpaid
  have hmu : (n : ℝ) * |mu| ≤ 2 * R / e ^ 2 := hpaid.1
  have hcentered : m3c ≤ 8 * m3 := hpaid.2.2.2.2
  have hvdata := Shao.sourceTruncation_variance_bounds nu n h2 hnorm hmean 0 e
    (by norm_num) he heHalf hR'
  simp only [add_zero, div_one] at hvdata
  have hV : 0 < V := hvdata.2.2.2.2.2.1
  have hNV : (1 / 2 : ℝ) ≤ (n : ℝ) * V := hvdata.2.2.2.2.2.2.1
  have hgdata := Shao.sourceTruncation_gamma_bounds nu n h2 hnorm hmean 0 e
    (by norm_num) he heHalf hR'
  simp only [add_zero, div_one] at hgdata
  have hgamma : m3 / V ≤ 4 * R := hgdata.2.2.2.2.2.2.2.2
  have hmuN : (n : ℝ) * |mu| ≤ 1 / 8 := by
    apply hmu.trans
    apply (div_le_iff₀ (pow_pos he 2)).2
    norm_num [e, R] at hR' ⊢
    linarith only [hR']
  have hdrift := tes_drift_bound n mu V hNp hV hmuN hNV
  have hden : 0 < Real.sqrt V * Real.sqrt ((n + 1 : ℕ) : ℝ) := by positivity
  have hdenLo : (1 / 2 : ℝ) ≤ Real.sqrt V * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    apply (sq_le_sq₀ (by norm_num) (by positivity)).1
    rw [mul_pow, Real.sq_sqrt hV.le, Real.sq_sqrt (by positivity)]
    push_cast
    nlinarith only [hNV, hV]
  have hc : m3c / V ≤ 32 * R := by
    have hh := div_le_div_of_nonneg_right hcentered hV.le
    calc
      _ ≤ 8 * (m3 / V) := by convert hh using 1 <;> ring
      _ ≤ 32 * R := by linarith only [hgamma]
  obtain ⟨_, _, hPB⟩ := sourceTruncation_original_max_cdf_pullback
  have hpb := hPB nu n hn h2 hmean hnorm 0 e (by norm_num) he (le_refl e) hR'
  simp only [add_zero, div_one] at hpb
  let N : Set (Shao.Path n) := {v | ∀ j : Fin n, |v j| ≤ e}
  let p : ℝ := P0.real N
  have hp1 : p ≤ 1 := hpb.2.1
  have hcomp : 1 - p ≤ R / e ^ 3 := hpb.2.2.1
  have hcond : cond P0 N = P := hpb.2.2.2.2.2.1
  have hNm : MeasurableSet N := by
    have hset : N = ⋂ i : Fin n, {v : Shao.Path n | |v i| ≤ e} := by
      ext v; simp only [N, Set.mem_setOf_eq, Set.mem_iInter]
    rw [hset]
    exact MeasurableSet.iInter (fun i : Fin n => measurableSet_le
      (continuous_abs.measurable.comp (measurable_pi_apply i)) measurable_const)
  intro u hu
  have hsurv := iid_closed_survival_nonzero_drift rho h3r hV n u hu
  change P.real {v : Shao.Path n | Shao.maxWithZero v ≤ u} ≤
    (2 * Real.exp (6 + 3 * (1024 : ℝ))) *
      min 1 ((u + m3c / V) / (Real.sqrt V * Real.sqrt ((n + 1 : ℕ) : ℝ))) *
      Real.exp (4 * (|mu| * Real.sqrt (n : ℝ) / Real.sqrt V)) at hsurv
  have hratio : (u + m3c / V) / (Real.sqrt V * Real.sqrt ((n + 1 : ℕ) : ℝ)) ≤
      2 * u + 64 * R := by
    apply (div_le_iff₀ hden).2
    have hh := mul_le_mul_of_nonneg_left hdenLo (show 0 ≤ 2 * u + 64 * R by positivity)
    nlinarith only [hc, hh]
  have hmin := (min_le_right 1 _).trans hratio
  have hexp : Real.exp (4 * (|mu| * Real.sqrt (n : ℝ) / Real.sqrt V)) ≤ Real.exp 1 :=
    Real.exp_le_exp.2 (by linarith only [hdrift])
  have heq : Real.exp (6 + 3 * (1024 : ℝ)) * Real.exp 1 =
      Real.exp (7 + 3 * (1024 : ℝ)) := by rw [← Real.exp_add]; norm_num
  let A : Set (Shao.Path n) := {v | Shao.maxWithZero v ≤ u}
  have hF : P.real A ≤ S * (u + R) := by
    apply hsurv.trans
    calc
      _ ≤ (2 * Real.exp (6 + 3 * (1024 : ℝ))) * (2 * u + 64 * R) * Real.exp 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hmin (by positivity)) hexp
          (Real.exp_pos _).le (by positivity)
      _ = Real.exp (7 + 3 * (1024 : ℝ)) * (4 * u + 128 * R) := by
        calc
          _ = (Real.exp (6 + 3 * (1024 : ℝ)) * Real.exp 1) * (4 * u + 128 * R) := by ring
          _ = _ := by rw [heq]
      _ ≤ S * (u + R) := by
        dsimp [S]
        nlinarith only [mul_nonneg (Real.exp_pos (7 + 3 * (1024 : ℝ))).le hu]
  have hmul : P.real A * p = P0.real (N ∩ A) := by
    simpa only [hcond, p, Measure.real_def, ENNReal.toReal_mul] using
      congrArg ENNReal.toReal (cond_mul_eq_inter hNm A P0)
  have hsplit := measureReal_inter_add_sdiff (μ := P0) (s := A) hNm
  have hrem : P0.real (A \ N) ≤ 1 - p := by
    have hh := measureReal_mono (μ := P0) (show A \ N ⊆ Nᶜ from fun _ hv => hv.2)
    rwa [measureReal_compl hNm, probReal_univ] at hh
  rw [Set.inter_comm A N, ← hmul] at hsplit
  have hpF : P.real A * p ≤ P.real A := by
    nlinarith only [hp1, measureReal_nonneg (μ := P) (s := A)]
  change P0.real A ≤ (S + 1 / e ^ 3) * (u + R)
  calc
    _ ≤ P.real A + (1 - p) := by linarith only [hsplit, hpF, hrem]
    _ ≤ S * (u + R) + R / e ^ 3 := add_le_add hF hcomp
    _ ≤ (S + 1 / e ^ 3) * (u + R) := by
      have hh : 0 ≤ u / e ^ 3 := div_nonneg hu (pow_pos he 3).le
      calc
        _ = (S + 1 / e ^ 3) * (u + R) - u / e ^ 3 := by ring
        _ ≤ _ := sub_le_self _ hh

private theorem tes_closed_upper_uniform :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu]
        (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 →
        (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ u : ℝ, 0 ≤ u →
          (Measure.pi (fun _ : Fin n => nu)).real
            {v : Shao.Path n | Shao.maxWithZero v ≤ u} ≤
            C * (u + Shao.truncationBudget nu n 0) := by
  let S : ℝ := 128 * Real.exp (7 + 3 * (1024 : ℝ))
  let C : ℝ := S + 9 / (1 / 800 : ℝ) ^ 3
  have hS : 0 < S := by dsimp [S]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro nu hnu n hn h2 hmean hnorm u hu
  letI : IsProbabilityMeasure nu := hnu
  have hR0 := Shao.truncationBudget_nonneg nu n h2 0
  by_cases hbig : (1 / 800 : ℝ) ^ 3 / 8 ≤ Shao.truncationBudget nu n 0
  · have hpay : 1 ≤ C * Shao.truncationBudget nu n 0 := by
      have hh : 1 ≤ (8 / (1 / 800 : ℝ) ^ 3) * Shao.truncationBudget nu n 0 := by
        norm_num at hbig ⊢
        linarith only [hbig]
      exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith only [hS]) hR0)
    exact measureReal_le_one.trans (hpay.trans (by nlinarith only [mul_nonneg hC.le hu]))
  · have hh := tes_small_closed_upper nu n hn h2 hmean hnorm (le_of_lt (lt_of_not_ge hbig)) u hu
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [C, S]; norm_num)
      (add_nonneg hu hR0))

theorem original_closed_survival_uniform :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu]
        (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 →
        (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
        ∀ (s u : ℝ), (s = 1 ∨ s = -1) → 0 ≤ u →
          (Measure.pi (fun _ : Fin n => nu)).real
            {v : Shao.Path n | Shao.maxWithZero (s • v) ≤ u} ≤
            C * (u + Shao.truncationBudget nu n 0) := by
  classical
  obtain ⟨C, hC, hbound⟩ := tes_closed_upper_uniform
  refine ⟨C, hC, ?_⟩
  intro nu hnu n hn h2 hmean hnorm s u hs hu
  letI : IsProbabilityMeasure nu := hnu
  let nus : Measure ℝ := Measure.map (fun z : ℝ => s * z) nu
  have hm : Measurable (fun z : ℝ => s * z) := measurable_const.mul measurable_id
  have hsq (z : ℝ) : (s * z) ^ 2 = z ^ 2 := by
    rcases hs with rfl | rfl <;> ring
  have hprob : IsProbabilityMeasure nus := by dsimp [nus]; infer_instance
  letI : IsProbabilityMeasure nus := hprob
  have h2s : Integrable (fun z : ℝ => z ^ 2) nus := by
    apply (integrable_map_measure (by fun_prop) hm.aemeasurable).2
    simpa only [Function.comp_def, hsq] using h2
  have hmeans : (∫ z : ℝ, z ∂nus) = 0 := by
    rw [show nus = Measure.map (fun z : ℝ => s * z) nu from rfl,
      integral_map hm.aemeasurable (f := fun z : ℝ => z) (by fun_prop),
      integral_const_mul, hmean, mul_zero]
  have hsecond : (∫ z : ℝ, z ^ 2 ∂nus) = ∫ z : ℝ, z ^ 2 ∂nu := by
    rw [show nus = Measure.map (fun z : ℝ => s * z) nu from rfl,
      integral_map hm.aemeasurable (by fun_prop)]
    simp only [hsq]
  have hbudget : Shao.truncationBudget nus n 0 = Shao.truncationBudget nu n 0 := by
    unfold Shao.truncationBudget
    congr 1
    rw [show nus = Measure.map (fun z : ℝ => s * z) nu from rfl,
      integral_map hm.aemeasurable (f := fun z : ℝ => Shao.truncationF ((1 + 0) * z))
        ((Shao.continuous_truncationF.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)]
    apply integral_congr_ae
    filter_upwards [] with z
    rcases hs with rfl | rfl
    · simp
    · simpa only [add_zero, one_mul, neg_one_mul] using Shao.truncationF_neg z
  have hnorms : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nus) = 1 := by rw [hsecond]; exact hnorm
  have hb := hbound nus n hn h2s hmeans hnorms u hu
  rw [hbudget] at hb
  let T : Shao.Path n → Shao.Path n := fun v => s • v
  have hTm : Measurable T :=
    Measurable.of_eval (fun i => measurable_const.mul (measurable_pi_apply i))
  have hmap : Measure.map T (Measure.pi (fun _ : Fin n => nu)) =
      Measure.pi (fun _ : Fin n => nus) :=
    Measure.pi_map_pi (fun _ : Fin n => hm.aemeasurable)
  have hA : MeasurableSet {v : Shao.Path n | Shao.maxWithZero v ≤ u} :=
    measurableSet_le Shao.measurable_maxWithZero measurable_const
  rw [← hmap] at hb
  simpa only [Measure.real_def, Measure.map_apply hTm hA, Set.preimage_setOf_eq, T] using hb


private theorem tes_iid_clipped_square_moments
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1) :
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let U : Shao.Path n → ℝ := fun v => ∑ i : Fin n, if |v i| ≤ d then v i ^ 2 else 0
    Measurable U ∧ MemLp U 2 P ∧
      1 - Shao.truncationBudget nu n 0 / d ≤ (∫ v, U v ∂P) ∧
      variance U P ≤ d ^ 2 ∧ variance U P ≤ d * Shao.truncationBudget nu n 0 := by
  classical
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let A : ℝ → ℝ := fun z => if |z| ≤ d then z ^ 2 else 0
  let U : Shao.Path n → ℝ := fun v => ∑ i : Fin n, A (v i)
  have hAm : Measurable A := Measurable.ite
    (measurableSet_le continuous_abs.measurable measurable_const)
    (measurable_id.pow_const 2) measurable_const
  have hAb (z : ℝ) : 0 ≤ A z ∧ A z ≤ d ^ 2 := by
    dsimp [A]
    split_ifs with hz
    · exact ⟨sq_nonneg _, by nlinarith [sq_abs z, abs_nonneg z]⟩
    · constructor <;> positivity
  have hALp : MemLp A 2 nu := MemLp.of_bound hAm.aestronglyMeasurable (d ^ 2)
    (ae_of_all nu fun z => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hAb z).1] using (hAb z).2)
  have hAi : Integrable A nu := hALp.integrable (by norm_num)
  have hcoord (i : Fin n) : MemLp (fun v : Shao.Path n => A (v i)) 2 P :=
    hALp.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => nu) i)
  have hUm : Measurable U := by dsimp [U]; fun_prop
  have hULp : MemLp U 2 P := memLp_finsetSum Finset.univ (fun i _ => hcoord i)
  have hUint : (∫ v, U v ∂P) = (n : ℝ) * (∫ z, A z ∂nu) := by
    rw [show U = (fun v => ∑ i : Fin n, A (v i)) from rfl,
      integral_finsetSum _ (fun i _ => (hcoord i).integrable (by norm_num))]
    have hi (i : Fin n) : (∫ v : Shao.Path n, A (v i) ∂P) = ∫ z, A z ∂nu := by
      have hi := integral_map (μ := P) (measurable_pi_apply i).aemeasurable hAm.aestronglyMeasurable
      rw [(measurePreserving_eval (fun _ : Fin n => nu) i).map_eq] at hi
      exact hi.symm
    simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hFi : Integrable Shao.truncationF nu := by
    simpa only [one_mul] using Shao.integrable_truncationF_mul nu h2 1
  have hmean : 1 - Shao.truncationBudget nu n 0 / d ≤ ∫ v, U v ∂P := by
    have hi := integral_mono h2 (hAi.add (hFi.div_const d)) (fun z => by
      change z ^ 2 ≤ A z + Shao.truncationF z / d
      dsimp [A]
      split_ifs with hz
      · have hh : 0 ≤ Shao.truncationF z / d := div_nonneg (Shao.truncationF_nonneg _) hd.le
        linarith
      · have hmin : d ≤ min |z| 1 := le_min (le_of_not_ge hz) hd1
        have hh := mul_le_mul_of_nonneg_left hmin (sq_nonneg z)
        rw [zero_add]
        apply (le_div_iff₀ hd).2
        simpa only [Shao.truncationF, mul_comm] using hh)
    change (∫ z, z ^ 2 ∂nu) ≤ ∫ z, A z + Shao.truncationF z / d ∂nu at hi
    rw [integral_add hAi (hFi.div_const d), integral_div] at hi
    have hh := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    rw [mul_add, hnorm, ← hUint] at hh
    have hR : Shao.truncationBudget nu n 0 = (n : ℝ) * (∫ z, Shao.truncationF z ∂nu) := by
      simp only [Shao.truncationBudget, add_zero, one_mul]
    rw [hR]
    rw [← mul_div_assoc] at hh
    linarith only [hh]
  have hvar : variance U P = (n : ℝ) * variance A nu := by
    have hv := variance_sum_pi (μ := fun _ : Fin n => nu) (X := fun _ => A) (fun _ => hALp)
    have he : (∑ i : Fin n, fun v : Shao.Path n => A (v i)) = U := by
      funext v; simp only [Finset.sum_apply]; rfl
    rw [he] at hv
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hv
  have hvarle : variance A nu ≤ ∫ z, A z ^ 2 ∂nu := by
    rw [variance_eq_sub hALp]
    simp only [Pi.pow_apply]
    exact sub_le_self _ (sq_nonneg _)
  have hsq2 : (∫ z, A z ^ 2 ∂nu) ≤ d ^ 2 * (∫ z, z ^ 2 ∂nu) := by
    rw [← integral_const_mul]
    exact integral_mono hALp.integrable_sq (h2.const_mul (d ^ 2)) (fun z => by
      change A z ^ 2 ≤ d ^ 2 * z ^ 2
      dsimp [A]
      split_ifs with hz
      · have hh : z ^ 2 ≤ d ^ 2 := by nlinarith [sq_abs z, abs_nonneg z]
        nlinarith only [mul_le_mul_of_nonneg_right hh (sq_nonneg z)]
      · simp; positivity)
  have hsqF : (∫ z, A z ^ 2 ∂nu) ≤ d * (∫ z, Shao.truncationF z ∂nu) := by
    rw [← integral_const_mul]
    exact integral_mono hALp.integrable_sq (hFi.const_mul d) (fun z => by
      change A z ^ 2 ≤ d * Shao.truncationF z
      dsimp [A]
      split_ifs with hz
      · rw [Shao.truncationF, min_eq_left (hz.trans hd1)]
        have hh := mul_le_mul_of_nonneg_right hz (pow_nonneg (abs_nonneg z) 3)
        calc
          (z ^ 2) ^ 2 = |z| * |z| ^ 3 := by rw [← sq_abs z]; ring
          _ ≤ d * |z| ^ 3 := hh
          _ = d * (z ^ 2 * |z|) := by rw [show |z| ^ 3 = z ^ 2 * |z| by rw [pow_succ, sq_abs]]
      · simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
        exact mul_nonneg hd.le (Shao.truncationF_nonneg z))
  refine ⟨hUm, hULp, hmean, ?_, ?_⟩
  · rw [hvar]
    calc
      _ ≤ (n : ℝ) * (d ^ 2 * ∫ z, z ^ 2 ∂nu) :=
        mul_le_mul_of_nonneg_left (hvarle.trans hsq2) (Nat.cast_nonneg n)
      _ = d ^ 2 := by nlinarith only [hnorm]
  · rw [hvar]
    calc
      _ ≤ (n : ℝ) * (d * ∫ z, Shao.truncationF z ∂nu) :=
        mul_le_mul_of_nonneg_left (hvarle.trans hsqF) (Nat.cast_nonneg n)
      _ = d * Shao.truncationBudget nu n 0 := by
        simp only [Shao.truncationBudget, add_zero, one_mul]; ring

private theorem tes_zero_update_indep
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (H : Shao.Path n → ℝ) (hH : Measurable H) (i : Fin n) :
    IndepFun (fun v : Shao.Path n => v i)
      (fun v : Shao.Path n => H (Function.update v i 0))
      (Measure.pi (fun _ : Fin n => nu)) := by
  classical
  have hind : iIndepFun (fun j : Fin n => fun v : Shao.Path n => v j)
      (Measure.pi (fun _ : Fin n => nu)) := iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hdis : Disjoint ({i} : Set (Fin n)) {j : Fin n | j ≠ i} := by
    exact Set.disjoint_left.2 fun j hj hk => hk (Set.mem_singleton_iff.1 hj)
  have hi := hind.indepFun_set ({i} : Set (Fin n)) {j : Fin n | j ≠ i} hdis
    (fun j => measurable_pi_apply j)
  let rec0 : ({j : Fin n | j ≠ i} → ℝ) → Shao.Path n :=
    fun w j => if hj : j = i then 0 else w ⟨j, hj⟩
  have hrec : Measurable rec0 := by
    apply Measurable.of_eval
    intro j
    by_cases hj : j = i
    · simpa only [rec0, dif_pos hj] using (measurable_const : Measurable (fun _ : ({j : Fin n | j ≠ i} → ℝ) => (0 : ℝ)))
    · simpa only [rec0, dif_neg hj] using (measurable_pi_apply (⟨j, hj⟩ : {j : Fin n | j ≠ i}))
  have hh := hi.comp (measurable_pi_apply (⟨i, by simp⟩ : ({i} : Set (Fin n)))) (hH.comp hrec)
  have hfun : (fun v : Shao.Path n => H (Function.update v i 0)) =
      (H ∘ rec0) ∘ (fun v : Shao.Path n => fun j : {j : Fin n | j ≠ i} => v j) := by
    funext v
    apply congrArg H
    funext j
    by_cases hj : j = i <;> simp [rec0, Function.update_apply, hj]
  rw [hfun]
  exact hh

private theorem tes_unit_sum_abs
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1) :
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let S : Shao.Path n → ℝ := fun v => ∑ i : Fin n, v i
    MemLp S 2 P ∧ (∫ v, S v ^ 2 ∂P) = 1 ∧ (∫ v, |S v| ∂P) ≤ 1 := by
  classical
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let S : Shao.Path n → ℝ := fun v => ∑ i : Fin n, v i
  have hLp : MemLp (id : ℝ → ℝ) 2 nu :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 h2
  have hcoord (i : Fin n) : MemLp (fun v : Shao.Path n => v i) 2 P :=
    hLp.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => nu) i)
  have hSLp : MemLp S 2 P := memLp_finsetSum Finset.univ (fun i _ => hcoord i)
  have hSmean : (∫ v, S v ∂P) = 0 := by
    rw [show S = (fun v => ∑ i : Fin n, v i) from rfl,
      integral_finsetSum _ (fun i _ => (hcoord i).integrable (by norm_num))]
    have hi (i : Fin n) : (∫ v : Shao.Path n, v i ∂P) = 0 := by
      have hi := integral_map (μ := P) (measurable_pi_apply i).aemeasurable
        measurable_id.aestronglyMeasurable
      rw [(measurePreserving_eval (fun _ : Fin n => nu) i).map_eq] at hi
      exact hi.symm.trans hmean
    simp only [hi, Finset.sum_const_zero]
  have hSsq : (∫ v, S v ^ 2 ∂P) = 1 := by
    have hv := variance_sum_pi (μ := fun _ : Fin n => nu) (X := fun _ => (id : ℝ → ℝ)) (fun _ => hLp)
    have he : (∑ i : Fin n, fun v : Shao.Path n => v i) = S := by
      funext v; simp only [Finset.sum_apply]; rfl
    change variance (∑ i : Fin n, fun v : Shao.Path n => v i) P = _ at hv
    rw [he, variance_eq_sub hSLp, hSmean, variance_eq_sub hLp] at hv
    simpa only [Pi.pow_apply, id_eq, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero,
      hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hnorm] using hv
  have habs : Integrable (fun v => |S v|) P := by
    simpa only [Real.norm_eq_abs] using (hSLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)).norm
  refine ⟨hSLp, hSsq, ?_⟩
  have hi := integral_mono habs ((hSLp.integrable_sq.add (integrable_const 1)).div_const 2)
    (fun v => by change |S v| ≤ (S v ^ 2 + 1) / 2; nlinarith [sq_nonneg (|S v| - 1), sq_abs (S v)])
  change (∫ v, |S v| ∂P) ≤ ∫ v, (S v ^ 2 + 1) / 2 ∂P at hi
  rw [integral_div, integral_add hSLp.integrable_sq (integrable_const 1), hSsq] at hi
  norm_num only [integral_const, probReal_univ, one_smul] at hi
  exact hi

private theorem tes_clip_step
    (a b d h h0 z : ℝ) (hab : a ≤ b) (hd : 0 ≤ d)
    (hpos : 0 ≤ z → h0 ≤ h - z) (hneg : z ≤ 0 → h - z ≤ h0) :
    let f : ℝ → ℝ := fun t => min (max (t - a + d) 0) (b - a + 2 * d)
    0 ≤ z * (f h - f h0) ∧
      (a ≤ h → h ≤ b → |z| ≤ d → z ^ 2 ≤ z * (f h - f h0)) := by
  let f : ℝ → ℝ := fun t => min (max (t - a + d) 0) (b - a + 2 * d)
  have hmono : Monotone f := by
    intro x y hxy
    exact min_le_min (max_le_max (by linarith) le_rfl) le_rfl
  have hlinear (t : ℝ) (ht0 : a - d ≤ t) (ht1 : t ≤ b + d) : f t = t - a + d := by
    dsimp [f]
    rw [max_eq_left (by linarith), min_eq_left (by linarith)]
  constructor
  · by_cases hz : 0 ≤ z
    · exact mul_nonneg hz (sub_nonneg.2 (hmono (by linarith [hpos hz])))
    · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hz)
        (sub_nonpos.2 (hmono (by linarith [hneg (le_of_not_ge hz)])))
  · intro ha hb hz
    have hzl := abs_le.1 hz
    have hfh := hlinear h (by linarith) (by linarith)
    have hfz := hlinear (h - z) (by linarith) (by linarith)
    by_cases hzp : 0 ≤ z
    · have hh := hmono (hpos hzp)
      rw [hfz] at hh
      change z ^ 2 ≤ z * (f h - f h0)
      rw [hfh]
      nlinarith only [mul_le_mul_of_nonneg_left hh hzp]
    · have hh := hmono (hneg (le_of_not_ge hzp))
      rw [hfz] at hh
      change z ^ 2 ≤ z * (f h - f h0)
      rw [hfh]
      nlinarith only [mul_le_mul_of_nonpos_left hh (le_of_not_ge hzp)]

theorem iid_strong_monotonicity_concentration
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (H : Shao.Path n → ℝ) (hH : Measurable H)
    (hstrong : ∀ (v : Shao.Path n) (i : Fin n),
      Monotone (fun t : ℝ => H (Function.update v i t) - t))
    (a b : ℝ) (hab : a ≤ b) :
    (Measure.pi (fun _ : Fin n => nu)).real
      {v : Shao.Path n | a ≤ H v ∧ H v ≤ b} ≤
      2 * (b - a) + 80 * Shao.truncationBudget nu n 0 := by
  classical
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let R : ℝ := Shao.truncationBudget nu n 0
  let E : Set (Shao.Path n) := {v | a ≤ H v ∧ H v ≤ b}
  have hR0 : 0 ≤ R := Shao.truncationBudget_nonneg nu n h2 0
  by_cases hbig : 1 / 16 ≤ R
  · exact measureReal_le_one.trans (by linarith only [hbig, hab])
  have hsmall : R < 1 / 16 := lt_of_not_ge hbig
  have hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂nu := by
    by_contra hh
    have hm := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (le_of_not_gt hh)
    rw [hnorm] at hm
    norm_num at hm
  have hRp : 0 < R := Shao.truncationBudget_pos nu n h2 hn hsecond 0 (by norm_num)
  let d : ℝ := 4 * R
  let M : ℝ := b - a + 2 * d
  let f : ℝ → ℝ := fun t => min (max (t - a + d) 0) M
  let U : Shao.Path n → ℝ := fun v => ∑ i : Fin n, if |v i| ≤ d then v i ^ 2 else 0
  let S : Shao.Path n → ℝ := fun v => ∑ i : Fin n, v i
  let I : Shao.Path n → ℝ := E.indicator (fun _ => 1)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1 := by dsimp [d]; linarith only [hsmall]
  have hM : 0 ≤ M := by dsimp [M]; linarith only [hab, hd]
  have hfm : Measurable f := by dsimp [f]; fun_prop
  have hfb (t : ℝ) : 0 ≤ f t ∧ f t ≤ M :=
    ⟨le_min (le_max_right _ _) hM, min_le_right _ _⟩
  have hFbound : ∀ᵐ v ∂P, ‖f (H v)‖ ≤ M := ae_of_all P fun v => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hfb _).1]
    exact (hfb _).2
  have hUdata := tes_iid_clipped_square_moments nu n h2 hnorm d hd hd1
  have hUm : Measurable U := hUdata.1
  have hULp : MemLp U 2 P := hUdata.2.1
  have hUi : Integrable U P := hULp.integrable (by norm_num)
  have hUmean : 3 / 4 ≤ ∫ v, U v ∂P := by
    have hr : R / d = 1 / 4 := by dsimp [d]; field_simp
    have hh : 1 - R / d ≤ ∫ v, U v ∂P := hUdata.2.2.1
    rw [hr] at hh
    linarith only [hh]
  have hvarU : variance U P ≤ d ^ 2 := hUdata.2.2.2.1
  have hSdata := tes_unit_sum_abs nu n h2 hmean hnorm
  have hSLp : MemLp S 2 P := hSdata.1
  have hSi : Integrable S P := hSLp.integrable (by norm_num)
  have hSabs : Integrable (fun v => |S v|) P := by simpa only [Real.norm_eq_abs] using hSi.norm
  have hSabs_le : (∫ v, |S v| ∂P) ≤ 1 := hSdata.2.2
  have hLp : MemLp (id : ℝ → ℝ) 2 nu :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 h2
  have hXi (i : Fin n) : Integrable (fun v : Shao.Path n => v i) P :=
    (hLp.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => nu) i)).integrable (by norm_num)
  have hXmean (i : Fin n) : (∫ v : Shao.Path n, v i ∂P) = 0 := by
    have hi := integral_map (μ := P) (measurable_pi_apply i).aemeasurable measurable_id.aestronglyMeasurable
    rw [(measurePreserving_eval (fun _ : Fin n => nu) i).map_eq] at hi
    exact hi.symm.trans hmean
  have hH0m (i : Fin n) : Measurable (fun v : Shao.Path n => H (Function.update v i 0)) := by
    apply hH.comp
    apply Measurable.of_eval
    intro j
    by_cases hj : j = i
    · simpa [hj] using (measurable_const : Measurable (fun _ : Shao.Path n => (0 : ℝ)))
    · simpa [Function.update_apply, hj] using (measurable_pi_apply (X := fun _ : Fin n => ℝ) j)
  have hXF (i : Fin n) : Integrable (fun v : Shao.Path n => v i * f (H v)) P :=
    (hXi i).mul_bdd (hfm.comp hH).aestronglyMeasurable hFbound
  have hXF0 (i : Fin n) : Integrable (fun v : Shao.Path n => v i * f (H (Function.update v i 0))) P :=
    (hXi i).mul_bdd (hfm.comp (hH0m i)).aestronglyMeasurable (ae_of_all P fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hfb _).1]; exact (hfb _).2)
  have hzero (i : Fin n) : (∫ v : Shao.Path n, v i * f (H (Function.update v i 0)) ∂P) = 0 := by
    have hi := (tes_zero_update_indep nu n H hH i).comp measurable_id hfm
    have he := hi.integral_fun_mul_eq_mul_integral
      (measurable_pi_apply i).aestronglyMeasurable (hfm.comp (hH0m i)).aestronglyMeasurable
    change (∫ v : Shao.Path n, v i * f (H (Function.update v i 0)) ∂P) =
      (∫ v : Shao.Path n, v i ∂P) * (∫ v : Shao.Path n, f (H (Function.update v i 0)) ∂P) at he
    rw [hXmean, zero_mul] at he
    exact he
  have hpart (i : Fin n) : Integrable (fun v : Shao.Path n =>
      v i * (f (H v) - f (H (Function.update v i 0)))) P := by
    exact ((hXF i).sub (hXF0 i)).congr (ae_of_all P fun v => by simp only [Pi.sub_apply]; ring)
  have hstep (v : Shao.Path n) (i : Fin n) :
      0 ≤ v i * (f (H v) - f (H (Function.update v i 0))) ∧
        (a ≤ H v → H v ≤ b → |v i| ≤ d →
          v i ^ 2 ≤ v i * (f (H v) - f (H (Function.update v i 0)))) := by
    apply tes_clip_step a b d (H v) (H (Function.update v i 0)) (v i) hab hd.le
    · intro hv
      simpa only [Function.update_eq_self, sub_zero] using hstrong v i hv
    · intro hv
      simpa only [Function.update_eq_self, sub_zero] using hstrong v i hv
  have hEm : MeasurableSet E := (measurableSet_le measurable_const hH).inter
    (measurableSet_le hH measurable_const)
  have hIm : Measurable I := measurable_const.indicator hEm
  have hIi : Integrable I P := (integrable_const (1 : ℝ)).indicator hEm
  have hIval : (∫ v, I v ∂P) = P.real E := integral_indicator_one hEm
  have hIU : Integrable (fun v => I v * U v) P := hUi.bdd_mul hIm.aestronglyMeasurable
    (c := 1) (ae_of_all P fun v => by by_cases hv : v ∈ E <;> simp [I, hv])
  have hIU_le : (∫ v, I v * U v ∂P) ≤ M := by
    have hi := integral_mono hIU (integrable_finsetSum Finset.univ (fun i _ => hpart i)) (fun v => by
      change I v * U v ≤ ∑ i : Fin n, v i * (f (H v) - f (H (Function.update v i 0)))
      by_cases hv : v ∈ E
      · simp only [I, Set.indicator_of_mem hv, one_mul]
        apply Finset.sum_le_sum
        intro i _
        split_ifs with hs
        · exact (hstep v i).2 hv.1 hv.2 hs
        · exact (hstep v i).1
      · simp only [I, Set.indicator_of_notMem hv, zero_mul]
        exact Finset.sum_nonneg fun i _ => (hstep v i).1)
    rw [integral_finsetSum _ (fun i _ => hpart i)] at hi
    have hpi (i : Fin n) : (∫ v : Shao.Path n,
        v i * (f (H v) - f (H (Function.update v i 0))) ∂P) =
        ∫ v : Shao.Path n, v i * f (H v) ∂P := by
      simp_rw [mul_sub]
      rw [integral_sub (hXF i) (hXF0 i), hzero, sub_zero]
    simp_rw [hpi] at hi
    have hsum : (∑ i : Fin n, ∫ v : Shao.Path n, v i * f (H v) ∂P) =
        ∫ v, S v * f (H v) ∂P := by
      rw [← integral_finsetSum _ (fun i _ => hXF i)]
      apply integral_congr_ae
      exact ae_of_all P fun v => by dsimp [S]; rw [Finset.sum_mul]
    rw [hsum] at hi
    have hSF : Integrable (fun v => S v * f (H v)) P :=
      hSi.mul_bdd (hfm.comp hH).aestronglyMeasurable hFbound
    have hup := integral_mono hSF (hSabs.mul_const M) (fun v => by
      change S v * f (H v) ≤ |S v| * M
      exact (mul_le_mul_of_nonneg_right (le_abs_self (S v)) (hfb _).1).trans
        (mul_le_mul_of_nonneg_left (hfb _).2 (abs_nonneg (S v))))
    rw [integral_mul_const] at hup
    exact hi.trans (hup.trans (by nlinarith only [mul_le_mul_of_nonneg_right hSabs_le hM]))
  have hlower : P.real E / 2 - variance U P ≤ ∫ v, I v * U v ∂P := by
    let mU : ℝ := ∫ v, U v ∂P
    have hcen : Integrable (fun v => (U v - mU) ^ 2) P :=
      (hULp.sub (memLp_const mU)).integrable_sq
    have hi := integral_mono ((hIi.mul_const (mU - 1 / 4)).sub hcen) hIU (fun v => by
      change I v * (mU - 1 / 4) - (U v - mU) ^ 2 ≤ I v * U v
      by_cases hv : v ∈ E
      · simp only [I, Set.indicator_of_mem hv, one_mul]
        nlinarith only [sq_nonneg (U v - mU + 1 / 2)]
      · simp only [I, Set.indicator_of_notMem hv, zero_mul]
        nlinarith only [sq_nonneg (U v - mU)])
    change (∫ v, I v * (mU - 1 / 4) - (U v - mU) ^ 2 ∂P) ≤ ∫ v, I v * U v ∂P at hi
    rw [integral_sub (hIi.mul_const (mU - 1 / 4)) hcen, integral_mul_const, hIval] at hi
    rw [(variance_eq_integral hUm.aemeasurable).symm] at hi
    have hm : P.real E / 2 ≤ P.real E * (mU - 1 / 4) := by
      have hh := mul_le_mul_of_nonneg_left (show 1 / 2 ≤ mU - 1 / 4 by dsimp [mU]; linarith only [hUmean])
        (measureReal_nonneg (μ := P) (s := E))
      linarith only [hh]
    linarith only [hi, hm]
  change P.real E ≤ 2 * (b - a) + 80 * R
  dsimp [M, d] at hIU_le hvarU
  nlinarith only [hlower, hIU_le, hvarU, hRp, hsmall]


private theorem tes_clamped_square_lipschitz (s t : ℝ) :
    let chi : ℝ → ℝ := fun z => max (-(1 / 4 : ℝ)) (min z (1 / 4))
    |chi t ^ 2 - chi s ^ 2| ≤ |t - s| / 2 := by
  let chi : ℝ → ℝ := fun z => max (-(1 / 4 : ℝ)) (min z (1 / 4))
  have hbound (z : ℝ) : |chi z| ≤ 1 / 4 := by
    apply abs_le.2
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
  have hlip : |chi t - chi s| ≤ |t - s| := by
    have h1 := abs_min_sub_min_le_max t (1 / 4 : ℝ) s (1 / 4)
    have h2 := abs_max_sub_max_le_max (-(1 / 4 : ℝ)) (min t (1 / 4))
      (-(1 / 4 : ℝ)) (min s (1 / 4))
    simp only [sub_self, abs_zero, max_eq_left (abs_nonneg (t - s))] at h1
    simp only [sub_self, abs_zero, max_eq_right (abs_nonneg (min t (1 / 4 : ℝ) - min s (1 / 4)))] at h2
    exact h2.trans h1
  have hsum : |chi t + chi s| ≤ 1 / 2 :=
    (abs_add_le _ _).trans (by linarith only [hbound t, hbound s])
  calc
    _ = |chi t - chi s| * |chi t + chi s| := by rw [← abs_mul]; congr 1; ring
    _ ≤ |t - s| * (1 / 2) := mul_le_mul hlip hsum (abs_nonneg _) (abs_nonneg _)
    _ = _ := by ring

private theorem tes_floored_sqrt_lipschitz (r s t : ℝ) :
    let chi : ℝ → ℝ := fun z => max (-(1 / 4 : ℝ)) (min z (1 / 4))
    |Real.sqrt (max (r + chi t ^ 2) (1 / 2)) -
      Real.sqrt (max (r + chi s ^ 2) (1 / 2))| ≤ |t - s| / 2 := by
  let chi : ℝ → ℝ := fun z => max (-(1 / 4 : ℝ)) (min z (1 / 4))
  let A : ℝ := max (r + chi t ^ 2) (1 / 2)
  let B : ℝ := max (r + chi s ^ 2) (1 / 2)
  have hA : (1 / 2 : ℝ) ≤ A := le_max_right _ _
  have hB : (1 / 2 : ℝ) ≤ B := le_max_right _ _
  have hAp : 0 ≤ A := by linarith
  have hBp : 0 ≤ B := by linarith
  have hrootA : (1 / 2 : ℝ) ≤ Real.sqrt A := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).1
    rw [Real.sq_sqrt hAp]; linarith only [hA]
  have hrootB : (1 / 2 : ℝ) ≤ Real.sqrt B := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).1
    rw [Real.sq_sqrt hBp]; linarith only [hB]
  have hab : |A - B| ≤ |chi t ^ 2 - chi s ^ 2| := by
    have hh := abs_max_sub_max_le_max (r + chi t ^ 2) (1 / 2 : ℝ)
      (r + chi s ^ 2) (1 / 2)
    have he : (r + chi t ^ 2) - (r + chi s ^ 2) = chi t ^ 2 - chi s ^ 2 := by ring
    simpa only [sub_self, abs_zero, he, max_eq_left (abs_nonneg (chi t ^ 2 - chi s ^ 2))] using hh
  have hprod : |Real.sqrt A - Real.sqrt B| * (Real.sqrt A + Real.sqrt B) = |A - B| := by
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)), ← abs_mul]
    congr 1
    nlinarith only [Real.sq_sqrt hAp, Real.sq_sqrt hBp]
  have hh := tes_clamped_square_lipschitz s t
  change |chi t ^ 2 - chi s ^ 2| ≤ |t - s| / 2 at hh
  change |Real.sqrt A - Real.sqrt B| ≤ |t - s| / 2
  calc
    _ ≤ |Real.sqrt A - Real.sqrt B| * (Real.sqrt A + Real.sqrt B) := by
      nlinarith only [hrootA, hrootB, abs_nonneg (Real.sqrt A - Real.sqrt B)]
    _ = |A - B| := hprod
    _ ≤ |chi t ^ 2 - chi s ^ 2| := hab
    _ ≤ _ := hh

private theorem tes_iid_large_coordinate
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1) :
    (Measure.pi (fun _ : Fin n => nu)).real
      {v : Shao.Path n | ∃ i : Fin n, d < |v i|} ≤
      Shao.truncationBudget nu n 0 / d ^ 3 := by
  classical
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let B : Set ℝ := {z | d < |z|}
  have hBm : MeasurableSet B := measurableSet_lt measurable_const continuous_abs.measurable
  have hFi : Integrable Shao.truncationF nu := by
    simpa only [one_mul] using Shao.integrable_truncationF_mul nu h2 1
  have hB : nu.real B ≤ (∫ z, Shao.truncationF z ∂nu) / d ^ 3 := by
    have hi := integral_mono ((integrable_const (1 : ℝ)).indicator hBm) (hFi.div_const (d ^ 3)) (fun z => by
      by_cases hz : z ∈ B
      · rw [Set.indicator_of_mem hz]
        apply (le_div_iff₀ (pow_pos hd 3)).2
        have hz' : d ≤ |z| := le_of_lt hz
        have hsq : d ^ 2 ≤ z ^ 2 := by nlinarith only [sq_abs z, hz', hd, sq_nonneg (|z| - d)]
        change 1 * d ^ 3 ≤ z ^ 2 * min |z| 1
        calc
          _ = d ^ 2 * d := by ring
          _ ≤ _ := mul_le_mul hsq (le_min hz' hd1) hd.le (sq_nonneg z)
      · rw [Set.indicator_of_notMem hz]
        exact div_nonneg (Shao.truncationF_nonneg _) (pow_pos hd 3).le)
    change (∫ z, B.indicator (fun _ => (1 : ℝ)) z ∂nu) ≤ ∫ z, Shao.truncationF z / d ^ 3 ∂nu at hi
    have hI : (∫ z, B.indicator (fun _ => (1 : ℝ)) z ∂nu) = nu.real B := integral_indicator_one hBm
    rw [hI, integral_div] at hi
    exact hi
  have hcoord (i : Fin n) : P.real {v : Shao.Path n | d < |v i|} = nu.real B := by
    have hm := (measurePreserving_eval (fun _ : Fin n => nu) i).map_eq
    have hh := congrArg (fun m : Measure ℝ => m B) hm
    rw [Measure.map_apply (measurable_pi_apply i) hBm] at hh
    exact congrArg ENNReal.toReal hh
  have hset : {v : Shao.Path n | ∃ i : Fin n, d < |v i|} =
      ⋃ i : Fin n, {v : Shao.Path n | d < |v i|} := by ext v; simp
  rw [hset]
  calc
    _ ≤ ∑ i : Fin n, P.real {v : Shao.Path n | d < |v i|} := measureReal_iUnion_fintype_le _
    _ = (n : ℝ) * nu.real B := by simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ (n : ℝ) * ((∫ z, Shao.truncationF z ∂nu) / d ^ 3) :=
      mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg n)
    _ = Shao.truncationBudget nu n 0 / d ^ 3 := by
      simp only [Shao.truncationBudget, add_zero, one_mul]; ring

private theorem tes_iid_low_energy
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1) :
    (Measure.pi (fun _ : Fin n => nu)).real
      {v : Shao.Path n | Shao.energy v < 1 / 2} ≤
      16 * Shao.truncationBudget nu n 0 := by
  classical
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let R : ℝ := Shao.truncationBudget nu n 0
  have hR0 : 0 ≤ R := Shao.truncationBudget_nonneg nu n h2 0
  by_cases hbig : 1 / 16 ≤ R
  · exact measureReal_le_one.trans (by linarith only [hbig])
  have hsmall : R ≤ 1 / 16 := le_of_lt (lt_of_not_ge hbig)
  let U : Shao.Path n → ℝ := fun v => ∑ i : Fin n, if |v i| ≤ (1 / 4 : ℝ) then v i ^ 2 else 0
  have hdata := tes_iid_clipped_square_moments nu n h2 hnorm (1 / 4) (by norm_num) (by norm_num)
  have hUm : Measurable U := hdata.1
  have hULp : MemLp U 2 P := hdata.2.1
  let m : ℝ := ∫ v, U v ∂P
  have hm : 3 / 4 ≤ m := by
    have hh : 1 - R / (1 / 4) ≤ m := hdata.2.2.1
    linarith only [hh, hsmall]
  have hvar : variance U P ≤ R / 4 := by
    have hh : variance U P ≤ (1 / 4) * R := hdata.2.2.2.2
    linarith only [hh]
  let B : Set (Shao.Path n) := {v | Shao.energy v < 1 / 2}
  have hBm : MeasurableSet B := measurableSet_lt Shao.measurable_energy measurable_const
  have hcen : Integrable (fun v => (U v - m) ^ 2) P :=
    (hULp.sub (memLp_const m)).integrable_sq
  have hi := integral_mono (((integrable_const (1 : ℝ)).indicator hBm).div_const 16) hcen (fun v => by
    change B.indicator (fun _ => (1 : ℝ)) v / 16 ≤ (U v - m) ^ 2
    by_cases hv : v ∈ B
    · rw [Set.indicator_of_mem hv]
      have hUQ : U v ≤ Shao.energy v := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs <;> nlinarith only [sq_nonneg (v i)]
      have hdiff : 1 / 4 ≤ m - U v := by
        change Shao.energy v < 1 / 2 at hv
        linarith only [hUQ, hm, hv]
      nlinarith only [hdiff, sq_nonneg (m - U v - 1 / 4)]
    · rw [Set.indicator_of_notMem hv]
      exact by simpa only [zero_div] using sq_nonneg (U v - m))
  change (∫ v, B.indicator (fun _ => (1 : ℝ)) v / 16 ∂P) ≤ ∫ v, (U v - m) ^ 2 ∂P at hi
  have hI : (∫ v, B.indicator (fun _ => (1 : ℝ)) v ∂P) = P.real B := integral_indicator_one hBm
  rw [integral_div, hI, (variance_eq_integral hUm.aemeasurable).symm] at hi
  change P.real B ≤ 16 * R
  nlinarith only [hi, hvar, hR0]

private theorem tes_normalization_data
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂nu) :
    let scale : ℝ := Real.sqrt ((n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu))
    let eta : Measure ℝ := Measure.map (fun z : ℝ => z / scale) nu
    0 < scale ∧ IsProbabilityMeasure eta ∧
      Integrable (fun z : ℝ => z ^ 2) eta ∧
      (∫ z : ℝ, z ∂eta) = 0 ∧
      (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta) = 1 ∧
      Measure.map (fun v : Shao.Path n => (fun i : Fin n => v i / scale))
        (Measure.pi (fun _ : Fin n => nu)) = Measure.pi (fun _ : Fin n => eta) := by
  let scale : ℝ := Real.sqrt ((n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu))
  let eta : Measure ℝ := Measure.map (fun z : ℝ => z / scale) nu
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < scale := Real.sqrt_pos.2 (mul_pos hnp hsecond)
  have hs2 : scale ^ 2 = (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) :=
    Real.sq_sqrt (mul_nonneg hnp.le hsecond.le)
  have hmapm : Measurable (fun z : ℝ => z / scale) := measurable_id.div_const scale
  have hp : IsProbabilityMeasure eta := by dsimp [eta]; infer_instance
  letI : IsProbabilityMeasure eta := hp
  have hi2 : Integrable (fun z : ℝ => z ^ 2) eta := by
    apply (integrable_map_measure (by fun_prop) hmapm.aemeasurable).2
    simpa only [Function.comp_def, div_pow] using h2.div_const (scale ^ 2)
  have hm : (∫ z : ℝ, z ∂eta) = 0 := by
    rw [show eta = Measure.map (fun z : ℝ => z / scale) nu from rfl,
      integral_map hmapm.aemeasurable (f := fun z : ℝ => z) (by fun_prop), integral_div, hmean, zero_div]
  have hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta) = 1 := by
    rw [show eta = Measure.map (fun z : ℝ => z / scale) nu from rfl,
      integral_map hmapm.aemeasurable (by fun_prop)]
    simp_rw [div_pow]
    rw [integral_div, ← mul_div_assoc]
    apply (div_eq_one_iff_eq (pow_ne_zero 2 hs.ne')).2
    exact hs2.symm
  exact ⟨hs, hp, hi2, hm, hnorm, Measure.pi_map_pi (fun _ : Fin n => hmapm.aemeasurable)⟩

private theorem tes_external_energy_normalized
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (q x a b : ℝ) (hq : 0 ≤ q) (hx : 0 ≤ x) (hx1 : x ≤ 1) (hab : a ≤ b) :
    (Measure.pi (fun _ : Fin n => nu)).real
      {v : Shao.Path n |
        a ≤ Shao.prefixSum v n - x * Real.sqrt (q + Shao.energy v) ∧
        Shao.prefixSum v n - x * Real.sqrt (q + Shao.energy v) ≤ b} ≤
      160 * ((b - a) + Shao.truncationBudget nu n 0) := by
  classical
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let chi : ℝ → ℝ := fun z => max (-(1 / 4 : ℝ)) (min z (1 / 4))
  let K : Shao.Path n → ℝ := fun v => ∑ i : Fin n, chi (v i) ^ 2
  let H : Shao.Path n → ℝ := fun v => Shao.prefixSum v n - x * Real.sqrt (max (q + K v) (1 / 2))
  let T : Shao.Path n → ℝ := fun v => 2 * H v
  have hTm : Measurable T := by simp only [T, H, K, chi, Shao.prefixSum_length]; fun_prop
  have hstrong : ∀ (v : Shao.Path n) (i : Fin n),
      Monotone (fun t : ℝ => T (Function.update v i t) - t) := by
    intro v i s t hst
    have hsum (g : ℝ → ℝ) (w : ℝ) :
        (∑ j : Fin n, g (Function.update v i w j)) =
          (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, g (v j)) + g w := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      · simp
    have hS (w : ℝ) : Shao.prefixSum (Function.update v i w) n =
        (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, v j) + w := by
      simpa only [id_eq, Shao.prefixSum_length] using hsum id w
    have hK (w : ℝ) : K (Function.update v i w) =
        (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, chi (v j) ^ 2) + chi w ^ 2 :=
      hsum (fun z => chi z ^ 2) w
    have hh := tes_floored_sqrt_lipschitz
      (q + ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, chi (v j) ^ 2) s t
    have hsqrt : |Real.sqrt (max (q + K (Function.update v i t)) (1 / 2)) -
        Real.sqrt (max (q + K (Function.update v i s)) (1 / 2))| ≤ (t - s) / 2 := by
      simpa only [hK, ← add_assoc, abs_of_nonneg (sub_nonneg.2 hst)] using hh
    have hup : x * (Real.sqrt (max (q + K (Function.update v i t)) (1 / 2)) -
        Real.sqrt (max (q + K (Function.update v i s)) (1 / 2))) ≤ (t - s) / 2 := by
      calc
        _ ≤ x * ((t - s) / 2) := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hsqrt) hx
        _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hx1 (sub_nonneg.2 hst)]
    change 2 * (Shao.prefixSum (Function.update v i s) n -
      x * Real.sqrt (max (q + K (Function.update v i s)) (1 / 2))) - s ≤
      2 * (Shao.prefixSum (Function.update v i t) n -
      x * Real.sqrt (max (q + K (Function.update v i t)) (1 / 2))) - t
    rw [hS s, hS t]
    nlinarith only [hup]
  have hconc := iid_strong_monotonicity_concentration nu n hn h2 hmean hnorm T hTm hstrong
    (2 * a) (2 * b) (by linarith only [hab])
  have hE : {v : Shao.Path n | 2 * a ≤ T v ∧ T v ≤ 2 * b} =
      {v : Shao.Path n | a ≤ H v ∧ H v ≤ b} := by
    ext v
    change (2 * a ≤ 2 * H v ∧ 2 * H v ≤ 2 * b) ↔ _
    constructor <;> intro hv <;> constructor <;> linarith only [hv.1, hv.2]
  rw [hE] at hconc
  let A : Set (Shao.Path n) := {v | a ≤ Shao.prefixSum v n - x * Real.sqrt (q + Shao.energy v) ∧
    Shao.prefixSum v n - x * Real.sqrt (q + Shao.energy v) ≤ b}
  let B : Set (Shao.Path n) := {v | ∃ i : Fin n, (1 / 4 : ℝ) < |v i|}
  let D : Set (Shao.Path n) := {v | Shao.energy v < 1 / 2}
  have hsub : A ⊆ {v : Shao.Path n | a ≤ H v ∧ H v ≤ b} ∪ (B ∪ D) := by
    intro v hv
    by_cases hB : v ∈ B
    · exact Or.inr (Or.inl hB)
    by_cases hD : v ∈ D
    · exact Or.inr (Or.inr hD)
    left
    have hKv : K v = Shao.energy v := by
      apply Finset.sum_congr rfl
      intro i _
      have hz : |v i| ≤ (1 / 4 : ℝ) := le_of_not_gt fun hi => hB ⟨i, hi⟩
      have hh := abs_le.1 hz
      dsimp [chi]
      rw [min_eq_left hh.2, max_eq_right hh.1]
    have hfloor : (1 / 2 : ℝ) ≤ q + K v := by
      rw [hKv]
      have hh : 1 / 2 ≤ Shao.energy v := le_of_not_gt hD
      linarith only [hq, hh]
    change a ≤ Shao.prefixSum v n - x * Real.sqrt (max (q + K v) (1 / 2)) ∧
      Shao.prefixSum v n - x * Real.sqrt (max (q + K v) (1 / 2)) ≤ b
    rw [max_eq_left hfloor, hKv]
    exact hv
  have hB : P.real B ≤ 64 * Shao.truncationBudget nu n 0 := by
    have hh := tes_iid_large_coordinate nu n h2 (1 / 4) (by norm_num) (by norm_num)
    norm_num only [one_div, inv_pow, inv_inv, Nat.cast_ofNat] at hh
    convert hh using 1 <;> ring
  have hD : P.real D ≤ 16 * Shao.truncationBudget nu n 0 := tes_iid_low_energy nu n h2 hnorm
  change P.real A ≤ 160 * ((b - a) + Shao.truncationBudget nu n 0)
  calc
    _ ≤ P.real {v : Shao.Path n | a ≤ H v ∧ H v ≤ b} + (P.real B + P.real D) :=
      (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
        (add_le_add le_rfl (measureReal_union_le B D)))
    _ ≤ (2 * (2 * b - 2 * a) + 80 * Shao.truncationBudget nu n 0) +
        (64 * Shao.truncationBudget nu n 0 + 16 * Shao.truncationBudget nu n 0) :=
      add_le_add hconc (add_le_add hB hD)
    _ ≤ _ := by linarith only [hab]

theorem iid_external_energy_concentration :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu]
        (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 →
        0 < (∫ z : ℝ, z ^ 2 ∂nu) →
        let scale : ℝ := Real.sqrt ((n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu))
        let eta : Measure ℝ := Measure.map (fun z : ℝ => z / scale) nu
        let R : ℝ := Shao.truncationBudget eta n 0
        ∀ (q x a b : ℝ), 0 ≤ q → 0 ≤ x → x ≤ 1 → a ≤ b →
          (Measure.pi (fun _ : Fin n => nu)).real
            {v : Shao.Path n |
              a ≤ Shao.prefixSum v n - x * Real.sqrt (q + Shao.energy v) ∧
              Shao.prefixSum v n - x * Real.sqrt (q + Shao.energy v) ≤ b} ≤
            C * ((b - a) / scale + R) := by
  refine ⟨160, by norm_num, ?_⟩
  intro nu hnu n hn h2 hmean hsecond scale eta R q x a b hq hx hx1 hab
  letI : IsProbabilityMeasure nu := hnu
  have hdata := tes_normalization_data nu n hn h2 hmean hsecond
  have hs : 0 < scale := hdata.1
  letI : IsProbabilityMeasure eta := hdata.2.1
  have h2e : Integrable (fun z : ℝ => z ^ 2) eta := hdata.2.2.1
  have hme : (∫ z : ℝ, z ∂eta) = 0 := hdata.2.2.2.1
  have hne : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta) = 1 := hdata.2.2.2.2.1
  let T : Shao.Path n → Shao.Path n := fun v i => v i / scale
  have hTm : Measurable T := by
    dsimp [T]
    exact Measurable.of_eval fun i => (measurable_pi_apply (X := fun _ : Fin n => ℝ) i).div_const scale
  have hmap : Measure.map T (Measure.pi (fun _ : Fin n => nu)) =
      Measure.pi (fun _ : Fin n => eta) := hdata.2.2.2.2.2
  have hstat (v : Shao.Path n) : Shao.prefixSum (T v) n -
      x * Real.sqrt (q / scale ^ 2 + Shao.energy (T v)) =
      (Shao.prefixSum v n - x * Real.sqrt (q + Shao.energy v)) / scale := by
    have hTv : T v = scale⁻¹ • v := by funext i; change v i / scale = scale⁻¹ * v i; ring
    rw [hTv, Shao.prefixSum_smul, Shao.energy_smul]
    have he : q / scale ^ 2 + scale⁻¹ ^ 2 * Shao.energy v = (q + Shao.energy v) / scale ^ 2 := by ring
    rw [he, Real.sqrt_div (add_nonneg hq (Shao.energy_nonneg v)), Real.sqrt_sq hs.le]
    ring
  let A : Set (Shao.Path n) := {v | a / scale ≤ Shao.prefixSum v n -
    x * Real.sqrt (q / scale ^ 2 + Shao.energy v) ∧
    Shao.prefixSum v n - x * Real.sqrt (q / scale ^ 2 + Shao.energy v) ≤ b / scale}
  have hAm : MeasurableSet A := by
    have hm : Measurable (fun v : Shao.Path n => Shao.prefixSum v n -
        x * Real.sqrt (q / scale ^ 2 + Shao.energy v)) :=
      (Shao.measurable_prefixSum n).sub (measurable_const.mul
        ((measurable_const.add Shao.measurable_energy).sqrt))
    exact (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)
  have hpre : T ⁻¹' A = {v : Shao.Path n |
      a ≤ Shao.prefixSum v n - x * Real.sqrt (q + Shao.energy v) ∧
      Shao.prefixSum v n - x * Real.sqrt (q + Shao.energy v) ≤ b} := by
    ext v
    change (a / scale ≤ _ ∧ _ ≤ b / scale) ↔ _
    rw [hstat]
    exact and_congr (div_le_div_iff_of_pos_right hs) (div_le_div_iff_of_pos_right hs)
  have hb := tes_external_energy_normalized eta n hn h2e hme hne (q / scale ^ 2) x
    (a / scale) (b / scale) (div_nonneg hq (sq_nonneg scale)) hx hx1
    ((div_le_div_iff_of_pos_right hs).2 hab)
  change (Measure.pi (fun _ : Fin n => eta)).real A ≤ _ at hb
  rw [← hmap, Measure.real_def, Measure.map_apply hTm hAm, hpre] at hb
  convert hb using 1 <;> first | rfl | ring


private theorem tes_raw_reverse_lower_survival :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 → 0 < (∫ z : ℝ, z ^ 2 ∂nu) →
        let scale : ℝ := Real.sqrt ((n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu))
        let eta : Measure ℝ := Measure.map (fun z : ℝ => z / scale) nu
        let R : ℝ := Shao.truncationBudget eta n 0
        ∀ u : ℝ, 0 ≤ u →
          (Measure.pi (fun _ : Fin n => nu)).real
            {v : Shao.Path n | Shao.maxWithZero (fun i => -v (Fin.rev i)) ≤ u} ≤
            C * (u / scale + R) := by
  classical
  obtain ⟨C, hC, hbound⟩ := original_closed_survival_uniform
  refine ⟨C, hC, ?_⟩
  intro nu hnu n hn h2 hmean hsecond scale eta R u hu
  letI : IsProbabilityMeasure nu := hnu
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  have hdata := tes_normalization_data nu n hn h2 hmean hsecond
  have hs : 0 < scale := hdata.1
  letI : IsProbabilityMeasure eta := hdata.2.1
  have h2e : Integrable (fun z : ℝ => z ^ 2) eta := hdata.2.2.1
  have hme : (∫ z : ℝ, z ∂eta) = 0 := hdata.2.2.2.1
  have hne : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta) = 1 := hdata.2.2.2.2.1
  let T : Shao.Path n → Shao.Path n := fun v i => v i / scale
  have hTm : Measurable T := by
    dsimp [T]
    exact Measurable.of_eval fun i => (measurable_pi_apply (X := fun _ : Fin n => ℝ) i).div_const scale
  have hmap : Measure.map T P = Measure.pi (fun _ : Fin n => eta) := hdata.2.2.2.2.2
  have hmax (v : Shao.Path n) : Shao.maxWithZero ((-1 : ℝ) • T v) =
      Shao.maxWithZero ((-1 : ℝ) • v) / scale := by
    have he : (-1 : ℝ) • T v = scale⁻¹ • ((-1 : ℝ) • v) := by
      funext i; change -1 * (v i / scale) = scale⁻¹ * (-1 * v i); ring
    rw [he, Shao.maxWithZero_eq _ hn, Shao.upperMax_smul_of_nonneg _ (inv_nonneg.2 hs.le),
      Shao.maxWithZero_eq _ hn]
    by_cases hv : 0 ≤ Shao.upperMax ((-1 : ℝ) • v) hn
    · rw [max_eq_right hv, max_eq_right (mul_nonneg (inv_nonneg.2 hs.le) hv)]
      ring
    · rw [max_eq_left (le_of_not_ge hv), max_eq_left (mul_nonpos_of_nonneg_of_nonpos
        (inv_nonneg.2 hs.le) (le_of_not_ge hv))]
      simp
  have hsm : Measurable (fun v : Shao.Path n => (-1 : ℝ) • v) :=
    Measurable.of_eval fun i => measurable_const.mul (measurable_pi_apply i)
  have hA : MeasurableSet {v : Shao.Path n | Shao.maxWithZero ((-1 : ℝ) • v) ≤ u / scale} :=
    measurableSet_le (Shao.measurable_maxWithZero.comp hsm) measurable_const
  have hb := hbound eta n hn h2e hme hne (-1) (u / scale) (Or.inr rfl) (div_nonneg hu hs.le)
  have hpre : T ⁻¹' {v : Shao.Path n | Shao.maxWithZero ((-1 : ℝ) • v) ≤ u / scale} =
      {v : Shao.Path n | Shao.maxWithZero ((-1 : ℝ) • v) ≤ u} := by
    ext v
    change Shao.maxWithZero ((-1 : ℝ) • T v) ≤ u / scale ↔ _
    rw [hmax]
    exact div_le_div_iff_of_pos_right hs
  rw [← hmap, Measure.real_def, Measure.map_apply hTm hA, hpre] at hb
  have hrev : MeasurePreserving (fun v : Shao.Path n => fun i => v (Fin.rev i)) P P :=
    (measurePreserving_piCongrLeft (fun _ : Fin n => nu) Fin.revPerm).symm
  have hE : MeasurableSet {v : Shao.Path n | Shao.maxWithZero ((-1 : ℝ) • v) ≤ u} :=
    measurableSet_le (Shao.measurable_maxWithZero.comp hsm) measurable_const
  have he := congrArg (fun m : Measure (Shao.Path n) => m {v | Shao.maxWithZero ((-1 : ℝ) • v) ≤ u}) hrev.map_eq
  rw [Measure.map_apply hrev.measurable hE] at he
  have hsigned (v : Shao.Path n) : (-1 : ℝ) • (fun i => v (Fin.rev i)) = (fun i => -v (Fin.rev i)) := by
    funext i; simp
  have hrevpre : (fun v : Shao.Path n => fun i => v (Fin.rev i)) ⁻¹'
      {v : Shao.Path n | Shao.maxWithZero ((-1 : ℝ) • v) ≤ u} =
      {v : Shao.Path n | Shao.maxWithZero (fun i => -v (Fin.rev i)) ≤ u} := by
    ext v
    change Shao.maxWithZero ((-1 : ℝ) • (fun i => v (Fin.rev i))) ≤ u ↔ _
    rw [hsigned]
    rfl
  rw [hrevpre] at he
  change P.real {v : Shao.Path n | Shao.maxWithZero (fun i => -v (Fin.rev i)) ≤ u} ≤ _
  exact (congrArg ENNReal.toReal he).le.trans hb

private theorem tes_head_tail_measurePreserving
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n k : ℕ) (hk : k ≤ n) :
    MeasurePreserving (fun v : Shao.Path n => (Spitzer.head v k hk, Spitzer.tail v k hk))
      (Measure.pi (fun _ : Fin n => nu))
      ((Measure.pi (fun _ : Fin k => nu)).prod (Measure.pi (fun _ : Fin (n - k) => nu))) := by
  let e : Fin k ⊕ Fin (n - k) ≃ Fin n :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hk))
  have h1 := (measurePreserving_piCongrLeft (fun _ : Fin n => nu) e).symm
  have h2 := measurePreserving_sumPiEquivProdPi (fun _ : Fin k ⊕ Fin (n - k) => nu)
  convert h2.comp h1 using 1
  ext v i <;> change v _ = v _ <;> congr 1

private theorem tes_head_tail_sum
    {n : ℕ} (v : Shao.Path n) (k : ℕ) (hk : k ≤ n) (g : ℝ → ℝ) :
    (∑ i : Fin n, g (v i)) =
      (∑ i : Fin k, g (Spitzer.head v k hk i)) +
        (∑ i : Fin (n - k), g (Spitzer.tail v k hk i)) := by
  let e : Fin k ⊕ Fin (n - k) ≃ Fin n :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hk))
  have hh := e.sum_comp (fun i : Fin n => g (v i))
  rw [Fintype.sum_sum_type] at hh
  exact hh.symm

private theorem tes_reverse_prefixSum
    {n : ℕ} (v : Shao.Path n) (j : ℕ) (hj : j ≤ n) :
    Shao.prefixSum (fun i : Fin n => v (Fin.rev i)) j =
      Shao.prefixSum v n - Shao.prefixSum v (n - j) := by
  classical
  have he : (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < j), v (Fin.rev i)) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => n - j ≤ i.val), v i := by
    apply Finset.sum_equiv Fin.revPerm
    · intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (i.val < j ↔ n - j ≤ (Fin.rev i).val)
      rw [Fin.val_rev]
      have hi := i.is_lt
      omega
    · intro i _; rfl
  have hh := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => i.val < n - j) v
  simp only [not_lt] at hh
  rw [Shao.prefixSum_length]
  change (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < j), v (Fin.rev i)) =
    (∑ i : Fin n, v i) - ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < n - j), v i
  rw [he]
  linarith only [hh]

private theorem tes_reverse_tail_prefixSum
    {n : ℕ} (v : Shao.Path n) (k : ℕ) (hk : k ≤ n)
    (j : ℕ) (hj : j ≤ n - k) :
    Shao.prefixSum (fun i : Fin (n - k) => Spitzer.tail v k hk (Fin.rev i)) j =
      Shao.prefixSum v n - Shao.prefixSum v (n - j) := by
  have hl : n - k ≤ n := Nat.sub_le _ _
  have he : (fun i : Fin (n - k) => Spitzer.tail v k hk (Fin.rev i)) =
      Spitzer.head (fun i : Fin n => v (Fin.rev i)) (n - k) hl := by
    funext i
    dsimp [Spitzer.tail, Spitzer.head]
    congr 1
    apply Fin.ext
    simp only [Fin.val_rev]
    have hi := i.is_lt
    omega
  rw [he, Spitzer.head_prefixSum _ _ _ _ hj, tes_reverse_prefixSum _ _ (hj.trans hl)]

private theorem tes_product_section_bound
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu : Measure A) (nu : Measure B) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (E : Set (A × B)) (hE : MeasurableSet E) (L : Set B) (hL : MeasurableSet L)
    (C : ℝ) (hC : 0 ≤ C)
    (houtside : ∀ a b, (a, b) ∈ E → b ∈ L)
    (hsection : ∀ b ∈ L, mu.real {a | (a, b) ∈ E} ≤ C) :
    (mu.prod nu).real E ≤ C * nu.real L := by
  classical
  let f : A × B → ℝ := E.indicator (fun _ => 1)
  have hfi : Integrable f (mu.prod nu) := (integrable_const (1 : ℝ)).indicator hE
  have hval : (∫ p, f p ∂mu.prod nu) = (mu.prod nu).real E := integral_indicator_one hE
  have hLval : (∫ b, L.indicator (fun _ => C) b ∂nu) = C * nu.real L := by
    rw [integral_indicator_const C hL]
    simp only [smul_eq_mul, mul_comm]
  rw [← hval, integral_prod_symm f hfi, ← hLval]
  apply integral_mono hfi.integral_prod_right ((integrable_const C).indicator hL)
  intro b
  let S : Set A := {a | (a, b) ∈ E}
  have hS : MeasurableSet S := hE.preimage (measurable_id.prodMk measurable_const)
  have hinner : (∫ a, f (a, b) ∂mu) = mu.real S := integral_indicator_one hS
  change (∫ a, f (a, b) ∂mu) ≤ L.indicator (fun _ => C) b
  rw [hinner]
  by_cases hb : b ∈ L
  · rw [Set.indicator_of_mem hb]
    exact hsection b hb
  · rw [Set.indicator_of_notMem hb]
    have hempty : S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      exact fun a ha => hb (houtside a b ha)
    simp only [hempty, measureReal_empty, le_refl]

private theorem tes_block_budget_comparison
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n j : ℕ)
    (hj : 0 < j) (hjn : j ≤ n) (hnj : n ≤ 4 * j)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂nu) :
    let sn : ℝ := Real.sqrt ((n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu))
    let sj : ℝ := Real.sqrt ((j : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu))
    let etan : Measure ℝ := Measure.map (fun z : ℝ => z / sn) nu
    let etaj : Measure ℝ := Measure.map (fun z : ℝ => z / sj) nu
    ∀ u : ℝ, 0 ≤ u →
      u / sj + Shao.truncationBudget etaj j 0 ≤
        8 * (u / sn + Shao.truncationBudget etan n 0) := by
  let sn : ℝ := Real.sqrt ((n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu))
  let sj : ℝ := Real.sqrt ((j : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu))
  let etan : Measure ℝ := Measure.map (fun z : ℝ => z / sn) nu
  let etaj : Measure ℝ := Measure.map (fun z : ℝ => z / sj) nu
  have hjr : 0 < (j : ℝ) := by exact_mod_cast hj
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le hj hjn)
  have hsj : 0 < sj := Real.sqrt_pos.2 (mul_pos hjr hsecond)
  have hsn : 0 < sn := Real.sqrt_pos.2 (mul_pos hnr hsecond)
  have hsj2 : sj ^ 2 = (j : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) := Real.sq_sqrt (by positivity)
  have hsn2 : sn ^ 2 = (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) := Real.sq_sqrt (by positivity)
  have hscale : sn ≤ 2 * sj := by
    apply (sq_le_sq₀ hsn.le (by positivity)).1
    rw [hsn2, mul_pow, hsj2]
    have hn4 : (n : ℝ) ≤ 4 * (j : ℝ) := by exact_mod_cast hnj
    nlinarith only [mul_le_mul_of_nonneg_right hn4 hsecond.le]
  have hcoeff : sj⁻¹ ≤ 2 * sn⁻¹ := by
    have hh : 1 / sj ≤ 2 / sn := (div_le_div_iff₀ hsj hsn).2 (by simpa only [one_mul] using hscale)
    simpa only [one_div, div_eq_mul_inv, one_mul] using hh
  have hInt (s : ℝ) : Integrable (fun z : ℝ => Shao.truncationF (z / s)) nu := by
    simpa only [div_eq_mul_inv, mul_comm] using Shao.integrable_truncationF_mul nu h2 s⁻¹
  have hi : (∫ z, Shao.truncationF (z / sj) ∂nu) ≤
      8 * (∫ z, Shao.truncationF (z / sn) ∂nu) := by
    rw [← integral_const_mul]
    apply integral_mono (hInt sj) ((hInt sn).const_mul 8)
    intro z
    have hm := Shao.truncationF_mono_scale sj⁻¹ (2 * sn⁻¹) z (inv_nonneg.2 hsj.le) hcoeff
    have hu := (Shao.truncationF_scale_one_le 2 (z / sn) (by norm_num)).2
    calc
      _ ≤ Shao.truncationF (2 * (z / sn)) := by convert hm using 1 <;> congr 1 <;> ring
      _ ≤ 8 * Shao.truncationF (z / sn) := by norm_num only [show (2 : ℝ) ^ 3 = 8 by norm_num] at hu; exact hu
  have hRn : Shao.truncationBudget etan n 0 = (n : ℝ) * (∫ z, Shao.truncationF (z / sn) ∂nu) := by
    simp only [Shao.truncationBudget, add_zero, one_mul]
    rw [show etan = Measure.map (fun z : ℝ => z / sn) nu from rfl]
    congr 1
    exact integral_map (μ := nu) (φ := fun z : ℝ => z / sn) (by fun_prop)
      Shao.continuous_truncationF.aestronglyMeasurable
  have hRj : Shao.truncationBudget etaj j 0 = (j : ℝ) * (∫ z, Shao.truncationF (z / sj) ∂nu) := by
    simp only [Shao.truncationBudget, add_zero, one_mul]
    rw [show etaj = Measure.map (fun z : ℝ => z / sj) nu from rfl]
    congr 1
    exact integral_map (μ := nu) (φ := fun z : ℝ => z / sj) (by fun_prop)
      Shao.continuous_truncationF.aestronglyMeasurable
  have hR : Shao.truncationBudget etaj j 0 ≤ 8 * Shao.truncationBudget etan n 0 := by
    rw [hRj, hRn]
    have hjn' : (j : ℝ) ≤ n := by exact_mod_cast hjn
    have hI0 : 0 ≤ ∫ z, Shao.truncationF (z / sn) ∂nu := integral_nonneg fun z => Shao.truncationF_nonneg _
    calc
      _ ≤ (j : ℝ) * (8 * ∫ z, Shao.truncationF (z / sn) ∂nu) :=
        mul_le_mul_of_nonneg_left hi hjr.le
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hjn' hI0]
  change ∀ u : ℝ, 0 ≤ u → u / sj + Shao.truncationBudget etaj j 0 ≤
    8 * (u / sn + Shao.truncationBudget etan n 0)
  intro u hu
  have hwidth : u / sj ≤ 2 * (u / sn) := by
    have hh := mul_le_mul_of_nonneg_left hcoeff hu
    convert hh using 1 <;> ring
  have hu0 : 0 ≤ u / sn := div_nonneg hu hsn.le
  linarith only [hwidth, hR, hu0]

private theorem tes_one_step_budget
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1) :
    3 / 8 ≤ Shao.truncationBudget nu 1 0 := by
  have hFi : Integrable Shao.truncationF nu := by
    simpa only [one_mul] using Shao.integrable_truncationF_mul nu h2 1
  have hi := integral_mono h2 ((integrable_const (1 / 4 : ℝ)).add (hFi.const_mul 2)) (fun z => by
    change z ^ 2 ≤ 1 / 4 + 2 * Shao.truncationF z
    by_cases hz : |z| ≤ 1 / 2
    · have hh : z ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs z, abs_nonneg z]
      linarith only [hh, Shao.truncationF_nonneg z]
    · have hh : (1 / 2 : ℝ) ≤ min |z| 1 := le_min (le_of_not_ge hz) (by norm_num)
      have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg z)
      change z ^ 2 ≤ 1 / 4 + 2 * (z ^ 2 * min |z| 1)
      nlinarith only [hm])
  change (∫ z, z ^ 2 ∂nu) ≤ ∫ z, 1 / 4 + 2 * Shao.truncationF z ∂nu at hi
  rw [integral_add (integrable_const (1 / 4 : ℝ)) (hFi.const_mul 2), integral_const_mul, hnorm] at hi
  norm_num only [integral_const, probReal_univ, one_smul] at hi
  simp only [Shao.truncationBudget, Nat.cast_one, add_zero, one_mul]
  linarith only [hi]

theorem iid_true_energy_closed_strip :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu]
        (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) nu →
        (∫ z : ℝ, z ∂nu) = 0 →
        0 < (∫ z : ℝ, z ^ 2 ∂nu) →
        let scale : ℝ := Real.sqrt ((n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu))
        let eta : Measure ℝ := Measure.map (fun z : ℝ => z / scale) nu
        let R : ℝ := Shao.truncationBudget eta n 0
        ∀ (q x u : ℝ), 0 ≤ q → 0 ≤ x → x ≤ 1 → 0 ≤ u →
          let wall : Shao.Path n → ℝ := fun v =>
            x * Real.sqrt (q + Shao.energy v)
          (Measure.pi (fun _ : Fin n => nu)).real
            {v : Shao.Path n |
              Shao.maxWithZero v ≤ wall v ∧
              wall v - u ≤ Shao.prefixSum v n ∧ Shao.prefixSum v n ≤ wall v} ≤
            C * min 1 ((u / scale + R) ^ 2) := by
  classical
  obtain ⟨Cac, hCac, hAC⟩ := iid_external_energy_concentration
  obtain ⟨Cs, hCs, hSurv⟩ := tes_raw_reverse_lower_survival
  let C : ℝ := 64 * Cac * Cs + 9
  have hprod : 0 ≤ Cac * Cs := mul_nonneg hCac.le hCs.le
  have hC : 0 < C := by dsimp [C]; nlinarith only [hprod]
  have hC8 : 8 ≤ C := by dsimp [C]; nlinarith only [hprod]
  have hC1 : 1 ≤ C := by linarith only [hC8]
  refine ⟨C, hC, ?_⟩
  intro nu hnu n hn h2 hmean hsecond scale eta R q x u hq hx hx1 hu wall
  letI : IsProbabilityMeasure nu := hnu
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let A : ℝ := u / scale + R
  let E : Set (Shao.Path n) := {v | Shao.maxWithZero v ≤ wall v ∧
    wall v - u ≤ Shao.prefixSum v n ∧ Shao.prefixSum v n ≤ wall v}
  have hdata := tes_normalization_data nu n hn h2 hmean hsecond
  have hs : 0 < scale := hdata.1
  letI : IsProbabilityMeasure eta := hdata.2.1
  have h2e : Integrable (fun z : ℝ => z ^ 2) eta := hdata.2.2.1
  have hne : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta) = 1 := hdata.2.2.2.2.1
  have hR0 : 0 ≤ R := Shao.truncationBudget_nonneg eta n h2e 0
  have hA0 : 0 ≤ A := add_nonneg (div_nonneg hu hs.le) hR0
  change P.real E ≤ C * min 1 (A ^ 2)
  by_cases hn1 : n = 1
  · subst n
    have hnorme : (∫ z : ℝ, z ^ 2 ∂eta) = 1 := by
      simpa only [Nat.cast_one, one_mul] using hne
    have hR : 3 / 8 ≤ R := tes_one_step_budget eta h2e hnorme
    have hA : 3 / 8 ≤ A := by dsimp [A]; linarith only [hR, div_nonneg hu hs.le]
    have hmin : 1 / 8 ≤ min 1 (A ^ 2) := le_min (by norm_num) (by nlinarith only [hA, sq_nonneg (A - 3 / 8)])
    have hpay : 1 ≤ C * min 1 (A ^ 2) := by
      have hh := mul_le_mul_of_nonneg_left hmin hC.le
      nlinarith only [hh, hC8]
    exact measureReal_le_one.trans hpay
  have hn2 : 2 ≤ n := by omega
  let b : ℕ := n / 2
  let l : ℕ := n - b
  have hb : b ≤ n := by dsimp [b]; omega
  have hbp : 0 < b := by dsimp [b]; omega
  have hlp : 0 < l := by dsimp [l, b]; omega
  have hl : l ≤ n := by dsimp [l]; omega
  have hnb : n ≤ 4 * b := by dsimp [b]; omega
  have hnl : n ≤ 4 * l := by dsimp [l, b]; omega
  let sb : ℝ := Real.sqrt ((b : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu))
  let sl : ℝ := Real.sqrt ((l : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu))
  let etab : Measure ℝ := Measure.map (fun z : ℝ => z / sb) nu
  let etal : Measure ℝ := Measure.map (fun z : ℝ => z / sl) nu
  let Rb : ℝ := Shao.truncationBudget etab b 0
  let Rl : ℝ := Shao.truncationBudget etal l 0
  let Fb : ℝ := u / sb + Rb
  let Fl : ℝ := u / sl + Rl
  let Pb : Measure (Shao.Path b) := Measure.pi (fun _ : Fin b => nu)
  let Pl : Measure (Shao.Path l) := Measure.pi (fun _ : Fin l => nu)
  have hsb : 0 < sb := Real.sqrt_pos.2 (mul_pos (by exact_mod_cast hbp) hsecond)
  have hsl : 0 < sl := Real.sqrt_pos.2 (mul_pos (by exact_mod_cast hlp) hsecond)
  have hRb0 : 0 ≤ Rb := by
    change 0 ≤ (b : ℝ) * (∫ z, Shao.truncationF ((1 + 0) * z) ∂etab)
    exact mul_nonneg (Nat.cast_nonneg b) (integral_nonneg fun z => Shao.truncationF_nonneg _)
  have hRl0 : 0 ≤ Rl := by
    change 0 ≤ (l : ℝ) * (∫ z, Shao.truncationF ((1 + 0) * z) ∂etal)
    exact mul_nonneg (Nat.cast_nonneg l) (integral_nonneg fun z => Shao.truncationF_nonneg _)
  have hFb0 : 0 ≤ Fb := add_nonneg (div_nonneg hu hsb.le) hRb0
  have hFl0 : 0 ≤ Fl := add_nonneg (div_nonneg hu hsl.le) hRl0
  have hFb : Fb ≤ 8 * A := tes_block_budget_comparison nu n b hbp hb hnb h2 hsecond u hu
  have hFl : Fl ≤ 8 * A := tes_block_budget_comparison nu n l hlp hl hnl h2 hsecond u hu
  let L : Set (Shao.Path l) := {c | Shao.maxWithZero (fun i => -c (Fin.rev i)) ≤ u}
  have hLm : MeasurableSet L := by
    apply measurableSet_le _ measurable_const
    apply Shao.measurable_maxWithZero.comp
    exact Measurable.of_eval fun i => (measurable_pi_apply (Fin.rev i)).neg
  let Z : Shao.Path b × Shao.Path l → ℝ := fun p =>
    Shao.prefixSum p.1 b - x * Real.sqrt (q + Shao.energy p.2 + Shao.energy p.1)
  let G : Set (Shao.Path b × Shao.Path l) := {p | p.2 ∈ L ∧
    -Shao.prefixSum p.2 l - u ≤ Z p ∧ Z p ≤ -Shao.prefixSum p.2 l}
  have hZm : Measurable Z := (Shao.measurable_prefixSum b |>.comp measurable_fst).sub
    (measurable_const.mul (((measurable_const.add (Shao.measurable_energy.comp measurable_snd)).add
      (Shao.measurable_energy.comp measurable_fst)).sqrt))
  have hGm : MeasurableSet G := (hLm.preimage measurable_snd).inter
    ((measurableSet_le (((Shao.measurable_prefixSum l).comp measurable_snd).neg.sub_const u) hZm).inter
      (measurableSet_le hZm (((Shao.measurable_prefixSum l).comp measurable_snd).neg)))
  have hsplit := tes_head_tail_measurePreserving nu n b hb
  have hsub : E ⊆ (fun v : Shao.Path n => (Spitzer.head v b hb, Spitzer.tail v b hb)) ⁻¹' G := by
    intro v hv
    have hvL : Spitzer.tail v b hb ∈ L := by
      change Shao.maxWithZero (-(fun i : Fin l => Spitzer.tail v b hb (Fin.rev i))) ≤ u
      apply (Shao.maxWithZero_le_iff _ u).2
      intro j hj
      rw [Shao.prefixSum_neg, tes_reverse_tail_prefixSum v b hb j hj]
      have hm := (Shao.maxWithZero_le_iff v (wall v)).1 hv.1 (n - j) (Nat.sub_le _ _)
      linarith only [hm, hv.2.1]
    refine ⟨hvL, ?_, ?_⟩
    all_goals
      have hS : Shao.prefixSum v n = Shao.prefixSum (Spitzer.head v b hb) b +
          Shao.prefixSum (Spitzer.tail v b hb) l := by
        change Shao.prefixSum v n = Shao.prefixSum (Spitzer.head v b hb) b +
          Shao.prefixSum (Spitzer.tail v b hb) (n - b)
        simpa only [Shao.prefixSum_length, id_eq] using tes_head_tail_sum v b hb id
      have hQ : Shao.energy v = Shao.energy (Spitzer.head v b hb) + Shao.energy (Spitzer.tail v b hb) :=
        tes_head_tail_sum v b hb (fun z => z ^ 2)
      have hqe : q + Shao.energy (Spitzer.tail v b hb) + Shao.energy (Spitzer.head v b hb) =
          q + Shao.energy v := by linarith only [hQ]
      dsimp only [Z, Prod.fst, Prod.snd]
      rw [hqe]
      change _ ≤ _
      rw [← show wall v = x * Real.sqrt (q + Shao.energy v) from rfl]
      linarith only [hS, hv.2.1, hv.2.2]
  have hsections (c : Shao.Path l) (_hc : c ∈ L) : Pb.real {a | (a, c) ∈ G} ≤ Cac * Fb := by
    have hsec := hAC nu b hbp h2 hmean hsecond (q + Shao.energy c) x
      (-Shao.prefixSum c l - u) (-Shao.prefixSum c l) (add_nonneg hq (Shao.energy_nonneg c))
      hx hx1 (by linarith only [hu])
    have hwidth : -Shao.prefixSum c l - (-Shao.prefixSum c l - u) = u := by ring
    rw [hwidth] at hsec
    apply (measureReal_mono (μ := Pb) (show {a | (a, c) ∈ G} ⊆
      {a : Shao.Path b | -Shao.prefixSum c l - u ≤ Shao.prefixSum a b - x * Real.sqrt (q + Shao.energy c + Shao.energy a) ∧
        Shao.prefixSum a b - x * Real.sqrt (q + Shao.energy c + Shao.energy a) ≤ -Shao.prefixSum c l}
      from fun _ ha => ha.2)).trans
    exact hsec
  have hG : (Pb.prod Pl).real G ≤ (Cac * Fb) * Pl.real L := tes_product_section_bound
    Pb Pl G hGm L hLm (Cac * Fb) (mul_nonneg hCac.le hFb0) (fun _ _ hp => hp.1) hsections
  have hL : Pl.real L ≤ Cs * Fl := hSurv nu l hlp h2 hmean hsecond u hu
  have hbound : P.real E ≤ (64 * Cac * Cs) * A ^ 2 := by
    calc
      _ ≤ P.real ((fun v : Shao.Path n => (Spitzer.head v b hb, Spitzer.tail v b hb)) ⁻¹' G) :=
        measureReal_mono hsub
      _ = (Pb.prod Pl).real G := by
        have he := congrArg (fun m : Measure (Shao.Path b × Shao.Path l) => m G) hsplit.map_eq
        rw [Measure.map_apply hsplit.measurable hGm] at he
        exact congrArg ENNReal.toReal he
      _ ≤ (Cac * Fb) * Pl.real L := hG
      _ ≤ (Cac * Fb) * (Cs * Fl) := mul_le_mul_of_nonneg_left hL (mul_nonneg hCac.le hFb0)
      _ = (Cac * Cs) * (Fb * Fl) := by ring
      _ ≤ (Cac * Cs) * ((8 * A) * (8 * A)) := mul_le_mul_of_nonneg_left
        (mul_le_mul hFb hFl hFl0 (by positivity)) hprod
      _ = _ := by ring
  by_cases hsmall : A ^ 2 ≤ 1
  · rw [min_eq_right hsmall]
    exact hbound.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (sq_nonneg A))
  · rw [min_eq_left (le_of_not_ge hsmall)]
    simpa only [mul_one] using (measureReal_le_one (μ := P) (s := E)).trans hC1

end Shao.Probability
