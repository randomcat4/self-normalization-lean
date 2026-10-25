/- Actual signed opposite-hit regular suffix Gaussian profile. -/
import Shao.Probability.MeasurablePath
import Shao.Probability.SourceWeightedPrefixWall

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
noncomputable section
namespace Shao.Probability.SourceRegularOppositeWall
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem actual_signed_opposite_hit_regular_suffix_profile :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (B : ℝ), 0 < B → (∀ᵐ z : ℝ ∂rho, |z| ≤ B) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ (n : ℕ), 0 < n →
          let delta : ℝ := beta / Real.sqrt (n : ℝ)
          ∀ x : ℝ, 16 ≤ x → B ≤ Real.sqrt (n : ℝ) / (200 * x) →
            delta * (1 + x) ^ 3 ≤ 1 →
            ∀ (r : ℕ), r ≤ n → (n : ℝ) / 2 ≤ (r : ℝ) →
              let P : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => rho)
              ∀ (T b d : ℝ), 0 < T → b ^ 2 ≤ T →
                |d| ≤ (3 / 2 : ℝ) * x * Real.sqrt T →
                ∀ s : ℝ, (s = 1 ∨ s = -1) →
                  let wall : Shao.Path r → ℝ := fun a =>
                    x * Real.sqrt (Shao.energy a + T)
                  let w : Shao.Path r → ℝ := fun a =>
                    wall a - s * Shao.prefixSum a r
                  let A : Set (Shao.Path r) := {a | ∀ k : Fin (r + 1),
                    0 < k.val → s * Shao.prefixSum a k.val < wall a}
                  let G : Set (Shao.Path r) := {a | (r : ℝ) / 2 ≤ Shao.energy a}
                  let Popp : Set (Shao.Path r) := {a | ∃ k : Fin (r + 1),
                    0 < k.val ∧ s * Shao.prefixSum a k.val ≤ -wall a}
                  let M : ℝ := |b| + max (s * d) 0
                  let profile : Shao.Path r → ℝ := fun a =>
                    Real.exp (-((max (w a - M) 0) ^ 2) / T)
                  Integrable ((A ∩ G ∩ Popp).indicator profile) P ∧
                    (∫ a : Shao.Path r, (A ∩ G ∩ Popp).indicator profile a ∂P) ≤
                      C * (T + beta ^ 2) / (r : ℝ) * (1 + x) ^ 10 *
                        Real.exp (-(4 / 5 : ℝ) * x ^ 2) := by
  classical
  obtain ⟨C0, hC0, hKernel⟩ :=
    SourceWeightedPrefixWall.actual_prior_opposite_hit_gaussian_wall_profile
  let C : ℝ := 4 * C0 * Real.exp (3 * C0) + 1
  have hC0nonneg : 0 ≤ C0 := le_trans zero_le_one hC0
  have hC : 1 ≤ C := by
    have hh : 0 ≤ 4 * C0 * Real.exp (3 * C0) := by positivity
    dsimp only [C]
    linarith only [hh]
  refine ⟨C, hC, ?_⟩
  intro rho hprob B hB hs hmean hvar beta n hn delta x hx hBsmall hsmall
    r hrn hhalf P T b d hT hb hd s hsign wall w A G Popp M profile
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrp : 0 < (r : ℝ) := by linarith only [hhalf, hnp]
  have hxpos : 0 < x := by linarith only [hx]
  have hx0 : 0 ≤ x := hxpos.le
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hBeta : 0 ≤ beta := integral_nonneg (fun z => pow_nonneg (abs_nonneg z) 3)
  let q : ℝ := Real.sqrt ((r : ℝ) + T)
  let t : ℝ := Real.sqrt T
  let z : ℝ := Real.sqrt ((r : ℝ) / 2 + T)
  let sn : ℝ := Real.sqrt (n : ℝ)
  let sr : ℝ := Real.sqrt (r : ℝ)
  let theta : ℝ := x / q
  let a0 : ℝ := x * z
  have hq : 0 < q := Real.sqrt_pos.2 (by linarith only [hrp, hT])
  have ht : 0 < t := Real.sqrt_pos.2 hT
  have hz : 0 < z := Real.sqrt_pos.2 (by linarith only [hrp, hT])
  have hsn : 0 < sn := Real.sqrt_pos.2 hnp
  have hsr : 0 < sr := Real.sqrt_pos.2 hrp
  have hq2 : q ^ 2 = (r : ℝ) + T := Real.sq_sqrt (by linarith only [hrp, hT])
  have ht2 : t ^ 2 = T := Real.sq_sqrt hT.le
  have hz2 : z ^ 2 = (r : ℝ) / 2 + T :=
    Real.sq_sqrt (by linarith only [hrp, hT])
  have hsn2 : sn ^ 2 = (n : ℝ) := Real.sq_sqrt hnp.le
  have hsr2 : sr ^ 2 = (r : ℝ) := Real.sq_sqrt hrp.le
  have hsrq : sr ≤ q := Real.sqrt_le_sqrt (by linarith only [hT])
  have htq : t ≤ q := Real.sqrt_le_sqrt (by linarith only [hrp])
  have htheta : 0 ≤ theta := div_nonneg hx0 hq.le
  have hthetaMax : theta ≤ x / Real.sqrt (r : ℝ) := by
    exact (div_le_div_iff₀ hq hsr).2 (mul_le_mul_of_nonneg_left hsrq hx0)
  have hthetaq : theta * q = x := by
    exact div_mul_cancel₀ x hq.ne'
  have hthetaT : theta * t ≤ x := by
    calc
      _ ≤ theta * q := mul_le_mul_of_nonneg_left htq htheta
      _ = x := hthetaq
  have hthetaR : theta * sr ≤ x := by
    calc
      _ ≤ theta * q := mul_le_mul_of_nonneg_left hsrq htheta
      _ = x := hthetaq
  have hsnq : sn ≤ 2 * q := by
    apply (sq_le_sq₀ hsn.le (by positivity)).1
    nlinarith only [hsn2, hq2, hhalf, hrp.le, hT.le]
  have hbroot : |b| ≤ t := by
    apply (sq_le_sq₀ (abs_nonneg b) ht.le).1
    simpa only [sq_abs, ht2] using hb
  have habsS : |s| = 1 := by
    rcases hsign with rfl | rfl <;> norm_num
  have hsd : s * d ≤ |d| := by
    calc
      _ ≤ |s * d| := le_abs_self _
      _ = |d| := by rw [abs_mul, habsS, one_mul]
  have hmax : max (s * d) 0 ≤ (3 / 2 : ℝ) * x * t := by
    exact max_le (hsd.trans hd) (by positivity)
  have hM : 0 ≤ M := add_nonneg (abs_nonneg b) (le_max_right _ _)
  have hMbound : M ≤ (1 + (3 / 2 : ℝ) * x) * t := by
    dsimp only [M]
    nlinarith only [hbroot, hmax]
  have hMratio : M / t ≤ 1 + (3 / 2 : ℝ) * x :=
    (div_le_iff₀ ht).2 hMbound
  have hPoly5 : (1 + theta * sr) ^ 5 ≤ (1 + x) ^ 5 :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hthetaR]) 5
  have hPoly3 : (1 + theta * t) ^ 3 ≤ (1 + x) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hthetaT]) 3
  have hPoly2 : (1 + M / t) ^ 2 ≤ 4 * (1 + x) ^ 2 := by
    have hh : 1 + M / t ≤ 2 * (1 + x) := by
      linarith only [hMratio, hx0]
    have hp := pow_le_pow_left₀
      (by positivity : 0 ≤ 1 + M / t) hh 2
    simpa only [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hp
  have hPolynomial :
      (1 + theta * sr) ^ 5 * (1 + M / t) ^ 2 * (1 + theta * t) ^ 3 ≤
        4 * (1 + x) ^ 10 := by
    have h12 := mul_le_mul hPoly5 hPoly2 (by positivity) (by positivity)
    have h123 := mul_le_mul h12 hPoly3 (by positivity) (by positivity)
    convert h123 using 1 <;> ring
  have hBudget : beta * (1 + x) ^ 3 ≤ sn := by
    have hh : (beta * (1 + x) ^ 3) / sn ≤ 1 := by
      simpa only [delta, sn, div_mul_eq_mul_div] using hsmall
    simpa only [one_mul] using (div_le_iff₀ hsn).1 hh
  have hBudgetX : beta * x ^ 3 ≤ sn := by
    calc
      _ ≤ beta * (1 + x) ^ 3 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hx0 (by linarith only [hx0]) 3) hBeta
      _ ≤ sn := hBudget
  have hCubic : (r : ℝ) * theta ^ 3 * beta ≤ 2 := by
    have hmul : ((r : ℝ) * theta ^ 3 * beta) * q ^ 3 ≤ 2 * q ^ 3 := by
      calc
        _ = (r : ℝ) * (beta * (theta * q) ^ 3) := by ring
        _ = (r : ℝ) * (beta * x ^ 3) := by rw [hthetaq]
        _ ≤ (r : ℝ) * sn := mul_le_mul_of_nonneg_left hBudgetX hrp.le
        _ ≤ (r : ℝ) * (2 * q) := mul_le_mul_of_nonneg_left hsnq hrp.le
        _ ≤ q ^ 2 * (2 * q) := mul_le_mul_of_nonneg_right
          (by linarith only [hq2, hT.le]) (by positivity)
        _ = 2 * q ^ 3 := by ring
    by_contra hnot
    have hbad := mul_lt_mul_of_pos_right (lt_of_not_ge hnot) (pow_pos hq 3)
    exact (not_lt_of_ge hmul) hbad
  have hSupport : theta * B ≤ 1 := by
    have hraw : 200 * x * B ≤ sn := by
      have hh := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 200) hxpos)).1 hBsmall
      change B * (200 * x) ≤ sn at hh
      nlinarith only [hh]
    have hxb : x * B ≤ q := by linarith only [hraw, hsnq, hq.le]
    calc
      _ = (x * B) / q := by dsimp only [theta]; ring
      _ ≤ 1 := (div_le_iff₀ hq).2 (by simpa only [one_mul] using hxb)
  have hRootGeometry : q + t ≤ 2 * z := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).1
    nlinarith only [hq2, ht2, hz2, sq_nonneg (q - t)]
  have hJointDrift :
      (3 / 2 : ℝ) * x ^ 2 + (3 / 2 : ℝ) * x * theta * t ≤
        3 * theta * a0 := by
    have hh := mul_le_mul_of_nonneg_left hRootGeometry
      (by positivity : 0 ≤ (3 / 2 : ℝ) * theta * x)
    have hqterm : ((3 / 2 : ℝ) * theta * x) * q = (3 / 2 : ℝ) * x ^ 2 := by
      calc
        _ = (3 / 2 : ℝ) * x * (theta * q) := by ring
        _ = (3 / 2 : ℝ) * x ^ 2 := by rw [hthetaq]; ring
    dsimp only [a0]
    nlinarith only [hh, hqterm]
  have hThetaSquare : ((r : ℝ) + T) * theta ^ 2 = x ^ 2 := by
    calc
      _ = q ^ 2 * theta ^ 2 := by rw [hq2]
      _ = (theta * q) ^ 2 := by ring
      _ = x ^ 2 := by rw [hthetaq]
  have hQuadratic :
      (53 / 100 : ℝ) * (r : ℝ) * theta ^ 2 + theta ^ 2 * T / 4 ≤
        (53 / 100 : ℝ) * x ^ 2 := by
    have hnonneg : 0 ≤ theta ^ 2 * T := mul_nonneg (sq_nonneg _) hT.le
    nlinarith only [hThetaSquare, hnonneg]
  have hThetaM : theta * M ≤ x + (3 / 2 : ℝ) * x * theta * t := by
    have hh := mul_le_mul_of_nonneg_left hMbound htheta
    nlinarith only [hh, hthetaT]
  have hMargin97 :
      (53 / 100 : ℝ) * (r : ℝ) * theta ^ 2 - 3 * theta * a0 +
        theta * M + theta ^ 2 * T / 4 ≤ -(97 / 100 : ℝ) * x ^ 2 + x := by
    nlinarith only [hJointDrift, hQuadratic, hThetaM]
  have hCoordinatePayment : x ≤ x ^ 2 / 16 := by
    nlinarith only [mul_nonneg hx0 (sub_nonneg.mpr hx)]
  have hMargin9075 :
      (53 / 100 : ℝ) * (r : ℝ) * theta ^ 2 - 3 * theta * a0 +
        theta * M + theta ^ 2 * T / 4 ≤ -(363 / 400 : ℝ) * x ^ 2 := by
    nlinarith only [hMargin97, hCoordinatePayment]
  let E : ℝ := (53 / 100 : ℝ) * (r : ℝ) * theta ^ 2 +
    C0 * (r : ℝ) * theta ^ 3 * beta + C0 * theta * B -
    3 * theta * a0 + theta * M + theta ^ 2 * T / 4
  have hExponent : E ≤ 3 * C0 + -(4 / 5 : ℝ) * x ^ 2 := by
    have hc := mul_le_mul_of_nonneg_left hCubic hC0nonneg
    have hb' := mul_le_mul_of_nonneg_left hSupport hC0nonneg
    dsimp only [E]
    nlinarith only [hMargin9075, hc, hb', sq_nonneg x]
  have hExp : Real.exp E ≤ Real.exp (3 * C0) * Real.exp (-(4 / 5 : ℝ) * x ^ 2) := by
    calc
      _ ≤ Real.exp (3 * C0 + -(4 / 5 : ℝ) * x ^ 2) := Real.exp_le_exp.mpr hExponent
      _ = _ := Real.exp_add _ _
  have hActual :
      Integrable ((A ∩ G ∩ Popp).indicator profile) P ∧
        (∫ a : Shao.Path r, (A ∩ G ∩ Popp).indicator profile a ∂P) ≤
          C0 * (T + beta ^ 2) / (r : ℝ) *
            (1 + theta * sr) ^ 5 * (1 + M / t) ^ 2 *
            (1 + theta * t) ^ 3 * Real.exp E := by
    rcases hsign with rfl | rfl
    · have hh := hKernel rho B hB hs hmean hvar n hn x hx1 hBsmall
        r hrn hhalf T M hT hM theta htheta hthetaMax
      simpa only [wall, w, A, G, Popp, profile, P, beta, E, a0, z, sr, t, one_mul]
        using hh
    · let rhoNeg : Measure ℝ := rho.map (fun y : ℝ => -y)
      have hm : Measurable (fun y : ℝ => -y) := measurable_neg
      letI : IsProbabilityMeasure rhoNeg :=
        (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
      have hsNeg : ∀ᵐ y : ℝ ∂rhoNeg, |y| ≤ B := by
        apply (ae_map_iff hm.aemeasurable
          (measurableSet_le continuous_abs.measurable measurable_const)).2
        simpa only [abs_neg] using hs
      have hmeanNeg : (∫ y : ℝ, y ∂rhoNeg) = 0 := by
        change (∫ y : ℝ, y ∂rho.map (fun y : ℝ => -y)) = 0
        rw [integral_map hm.aemeasurable (by fun_prop), integral_neg, hmean, neg_zero]
      have hvarNeg : (∫ y : ℝ, y ^ 2 ∂rhoNeg) = 1 := by
        change (∫ y : ℝ, y ^ 2 ∂rho.map (fun y : ℝ => -y)) = 1
        rw [integral_map hm.aemeasurable (by fun_prop)]
        simpa only [neg_sq] using hvar
      have hbetaNeg : (∫ y : ℝ, |y| ^ 3 ∂rhoNeg) = beta := by
        change (∫ y : ℝ, |y| ^ 3 ∂rho.map (fun y : ℝ => -y)) = beta
        rw [integral_map hm.aemeasurable (by fun_prop)]
        simp only [abs_neg]
        rfl
      let PN : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => rhoNeg)
      let wallPlus : Shao.Path r → ℝ := fun a => x * Real.sqrt (Shao.energy a + T)
      let wPlus : Shao.Path r → ℝ := fun a => wallPlus a - Shao.prefixSum a r
      let APlus : Set (Shao.Path r) := {a | ∀ k : Fin (r + 1),
        0 < k.val → Shao.prefixSum a k.val < wallPlus a}
      let GPlus : Set (Shao.Path r) := {a | (r : ℝ) / 2 ≤ Shao.energy a}
      let OppPlus : Set (Shao.Path r) := {a | ∃ k : Fin (r + 1),
        0 < k.val ∧ Shao.prefixSum a k.val ≤ -wallPlus a}
      let profilePlus : Shao.Path r → ℝ := fun a =>
        Real.exp (-((max (wPlus a - M) 0) ^ 2) / T)
      let FPlus : Shao.Path r → ℝ := (APlus ∩ GPlus ∩ OppPlus).indicator profilePlus
      have hWallM : Measurable wallPlus :=
        (Shao.measurable_energy.add measurable_const).sqrt.const_mul x
      have hwM : Measurable wPlus := hWallM.sub (Shao.measurable_prefixSum r)
      have hAM : MeasurableSet APlus := by
        simp only [APlus, Set.setOf_forall]
        exact MeasurableSet.iInter fun k : Fin (r + 1) =>
          MeasurableSet.iInter fun _ : 0 < k.val =>
            measurableSet_lt (Shao.measurable_prefixSum k.val) hWallM
      have hGM : MeasurableSet GPlus :=
        measurableSet_le measurable_const Shao.measurable_energy
      have hOM : MeasurableSet OppPlus := by
        simp only [OppPlus, Set.setOf_exists]
        exact MeasurableSet.iUnion fun k : Fin (r + 1) => by
          by_cases hk : 0 < k.val
          · simpa only [hk, true_and, Pi.neg_apply] using
              (measurableSet_le (Shao.measurable_prefixSum k.val) hWallM.neg)
          · simp [hk]
      have hProfileM : Measurable profilePlus := by
        dsimp only [profilePlus]
        exact ((((hwM.sub measurable_const).max measurable_const).pow_const 2).neg.div_const T).exp
      have hFM : Measurable FPlus :=
        hProfileM.indicator ((hAM.inter hGM).inter hOM)
      have hMap : P.map (fun a : Shao.Path r => -a) = PN :=
        Measure.pi_map_pi (fun _ : Fin r => hm.aemeasurable)
      have hPathM : Measurable (fun a : Shao.Path r => -a) := by fun_prop
      have hPull (a : Shao.Path r) :
          FPlus (-a) = (A ∩ G ∩ Popp).indicator profile a := by
        simp only [FPlus, Set.indicator_apply, Set.mem_inter_iff, Set.mem_setOf_eq,
          APlus, GPlus, OppPlus, profilePlus, wPlus, wallPlus,
          A, G, Popp, profile, w, wall, Shao.energy_neg, Shao.prefixSum_neg,
          neg_one_mul]
      have hh := hKernel rhoNeg B hB hsNeg hmeanNeg hvarNeg n hn x hx1 hBsmall
        r hrn hhalf T M hT hM theta htheta hthetaMax
      dsimp only at hh
      rw [hbetaNeg] at hh
      have hI : Integrable FPlus PN := hh.1
      have hBound : (∫ a : Shao.Path r, FPlus a ∂PN) ≤
          C0 * (T + beta ^ 2) / (r : ℝ) *
            (1 + theta * sr) ^ 5 * (1 + M / t) ^ 2 *
            (1 + theta * t) ^ 3 * Real.exp E := by
        simpa only [FPlus, APlus, GPlus, OppPlus, profilePlus, wPlus, wallPlus,
          PN, E, a0, z, sr, t] using hh.2
      constructor
      · have hI' : Integrable FPlus (P.map (fun a : Shao.Path r => -a)) := by
          rw [hMap]
          exact hI
        have hp := (integrable_map_measure hFM.aestronglyMeasurable hPathM.aemeasurable).1 hI'
        exact hp.congr (ae_of_all _ hPull)
      · calc
          _ = ∫ a : Shao.Path r, FPlus (-a) ∂P :=
            integral_congr_ae (ae_of_all _ fun a => (hPull a).symm)
          _ = ∫ a : Shao.Path r, FPlus a ∂PN := by
            rw [← hMap, integral_map hPathM.aemeasurable hFM.aestronglyMeasurable]
          _ ≤ _ := hBound
  refine ⟨hActual.1, hActual.2.trans ?_⟩
  have hBase : 0 ≤ (T + beta ^ 2) / (r : ℝ) := by positivity
  calc
    _ = (C0 * ((T + beta ^ 2) / (r : ℝ))) *
        ((1 + theta * sr) ^ 5 * (1 + M / t) ^ 2 * (1 + theta * t) ^ 3) *
        Real.exp E := by ring
    _ ≤ (C0 * ((T + beta ^ 2) / (r : ℝ))) * (4 * (1 + x) ^ 10) *
        (Real.exp (3 * C0) * Real.exp (-(4 / 5 : ℝ) * x ^ 2)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hPolynomial (mul_nonneg hC0nonneg hBase)
      · exact hExp
      · positivity
      · positivity
    _ = (4 * C0 * Real.exp (3 * C0)) * ((T + beta ^ 2) / (r : ℝ)) *
        (1 + x) ^ 10 * Real.exp (-(4 / 5 : ℝ) * x ^ 2) := by ring
    _ ≤ C * ((T + beta ^ 2) / (r : ℝ)) * (1 + x) ^ 10 *
        Real.exp (-(4 / 5 : ℝ) * x ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hBase
      dsimp only [C]
      linarith
    _ = _ := by ring

end Shao.Probability.SourceRegularOppositeWall
