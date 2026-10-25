import Shao.OQ6.ConditionalVarianceMean

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Shao.OQ6.LogarithmicConditionalRates

noncomputable section

open MeasureTheory ProbabilityTheory

theorem actual_logarithmic_conditional_rates
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun z : Ω × Ω => h z.1 z.2))
    (hh2 : MemLp (fun z : Ω × Ω => h z.1 z.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ z : Ω × Ω, h z.1 z.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (w : Ω → ℝ)
    (hw : Measurable w)
    (hwone : ∀ᵐ o ∂μ, 1 ≤ w o)
    (α τ : ℝ) (hα : 0 < α) (hτ : 0 < τ)
    (hwexp : Integrable (fun o => Real.exp (τ * Real.rpow (w o) α)) μ)
    (henvelope : ∀ᵐ z : Ω × Ω ∂(μ.prod μ),
      |h z.1 z.2 - (∫ y, h z.1 y ∂μ) - (∫ y, h z.2 y ∂μ)| ≤
        w z.1 * w z.2)
    (p : ℝ) (hp : 2 < p ∧ p ≤ 3)
    (hgp : Integrable
      (fun o => Real.rpow |∫ y, h o y ∂μ| p) μ)
    (J : ℝ) (hJ : 0 ≤ J) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
    let B : ℝ := Real.rpow β (1 / p)
    let W2 : ℝ := Real.sqrt (∫ o, w o ^ 2 ∂μ)
    let Cvar : ℝ := 32 * (1 + B ^ 2 + W2 ^ 2)
    let Cmean : ℝ := 4 * (1 + B)
    let e : ℝ := 1 - 2 / p
    let t : ℝ := 1 - 1 / p
    let A : ℝ := 2 * (J + 1) / e
    let M : ℝ := ∫ o, Real.exp (τ * Real.rpow (w o) α) ∂μ
    let Kvar : ℝ := Cvar *
      (Real.rpow M e + W2 * Real.sqrt M + W2 ^ 2 * M)
    let Kmean : ℝ := Cmean * (Real.rpow M t + W2 ^ 2 * M)
    let N0 : ℕ := Nat.ceil (max (3 : ℝ) (Real.rpow (2 * M) (1 / A)))
    0 < e ∧ e ≤ (1 / 3 : ℝ) ∧ t = (1 + e) / 2 ∧ 0 < A ∧
      Real.exp τ ≤ M ∧ 1 < M ∧
      J ≤ A * e ∧ J ≤ A / 2 ∧ J ≤ A ∧
      J ≤ A * t - 1 / 2 ∧ J ≤ A - 1 / 2 ∧
      ∀ n : ℕ, N0 ≤ n →
      let Rn : ℝ := Real.rpow (A * Real.log (n : ℝ) / τ) (1 / α)
      let Cn : Set Ω := {o : Ω | w o ≤ Rn}
      let πn : ℝ := μ.real Cnᶜ
      let dn : ℝ := μ.real Cn
      let νn : Measure Ω := (μ Cn)⁻¹ • μ.restrict Cn
      let bn : ℝ := ∫ o in Cnᶜ, w o ∂μ
      3 ≤ n ∧ 0 < Rn ∧ MeasurableSet Cn ∧
        (∀ᵐ o ∂μ,
          (w o ≤ Rn ↔ τ * Real.rpow (w o) α ≤ A * Real.log (n : ℝ))) ∧
        0 ≤ πn ∧ πn ≤ M * Real.rpow (n : ℝ) (-A) ∧
        M * Real.rpow (n : ℝ) (-A) ≤ (1 / 2 : ℝ) ∧
        dn = 1 - πn ∧ (1 / 2 : ℝ) ≤ dn ∧
        IsProbabilityMeasure νn ∧ νn ≪ μ ∧
        0 ≤ bn ∧ bn ^ 2 ≤ W2 ^ 2 * πn ∧
        bn ≤ W2 * Real.sqrt M * Real.rpow (n : ℝ) (-A / 2) ∧
        ∀ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 →
        let Hn : Ω → Ω → ℝ := fun o y => g o + g y + lam * r o y
        let qn : ℝ := ∫ z : Ω × Ω, Hn z.1 z.2 ∂(νn.prod νn)
        let Gn : Ω → ℝ := fun o => (∫ y, Hn o y ∂νn) - qn
        let σ2n : ℝ := ∫ o, Gn o ^ 2 ∂νn
        MemLp Gn 2 νn ∧ (∫ o, Gn o ∂νn) = 0 ∧ 0 ≤ σ2n ∧
          |σ2n - 1| ≤ Kvar * Real.rpow (n : ℝ) (-J) ∧
          (∀ m : ℕ, m ≤ n →
            Real.sqrt (m : ℝ) * |qn| ≤ Kmean * Real.rpow (n : ℝ) (-J)) := by
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
  let B : ℝ := Real.rpow β (1 / p)
  let W2 : ℝ := Real.sqrt (∫ o, w o ^ 2 ∂μ)
  let Cvar : ℝ := 32 * (1 + B ^ 2 + W2 ^ 2)
  let Cmean : ℝ := 4 * (1 + B)
  let e : ℝ := 1 - 2 / p
  let t : ℝ := 1 - 1 / p
  let A : ℝ := 2 * (J + 1) / e
  let M : ℝ := ∫ o, Real.exp (τ * Real.rpow (w o) α) ∂μ
  let Kvar : ℝ := Cvar * (Real.rpow M e + W2 * Real.sqrt M + W2 ^ 2 * M)
  let Kmean : ℝ := Cmean * (Real.rpow M t + W2 ^ 2 * M)
  let N0 : ℕ := Nat.ceil (max (3 : ℝ) (Real.rpow (2 * M) (1 / A)))
  rcases Shao.OQ6.ConditionalVarianceMean.actual_conditional_variance_mean
      μ h hh hh2 hhsymm hcenter hprojectionsecond w hw hwone α τ hα hτ
      hwexp henvelope p hp hgp with
    ⟨hβ0, hB0, hW20, hCvar, hCmean, hfinite⟩
  have hp0 : 0 < p := by linarith [hp.1]
  have he : 0 < e := by
    have hdiv : 2 / p < (1 : ℝ) := (div_lt_one hp0).2 hp.1
    dsimp only [e]
    linarith
  have he1 : e < 1 := by
    have hdiv : 0 < (2 : ℝ) / p := div_pos (by norm_num) hp0
    dsimp only [e]
    linarith
  have hep : e * p = p - 2 := by
    dsimp only [e]
    field_simp [ne_of_gt hp0] <;> ring
  have he33 : e ≤ (1 / 3 : ℝ) := by
    have hprod : 0 ≤ (1 - e) * (3 - p) :=
      mul_nonneg (by linarith) (by linarith [hp.2])
    nlinarith [hep]
  have hteq : t = (1 + e) / 2 := by
    dsimp only [t, e]
    ring
  have ht : 0 < t := by linarith [hteq]
  have hA : 0 < A := by
    dsimp only [A]
    exact div_pos (by linarith) he
  have hAe : A * e = 2 * (J + 1) := by
    dsimp only [A]
    field_simp [ne_of_gt he] <;> ring
  have hAhalf : J + 1 ≤ A / 2 := by
    have hprod : 0 ≤ A * (1 - e) :=
      mul_nonneg hA.le (by linarith)
    nlinarith [hAe]
  have hJae : J ≤ A * e := by linarith [hAe]
  have hJhalf : J ≤ A / 2 := by linarith
  have hJa : J ≤ A := by linarith
  have hJat : J ≤ A * t - 1 / 2 := by
    have hprod : 0 ≤ A * (t - 1 / 2) :=
      mul_nonneg hA.le (by linarith [hteq])
    nlinarith
  have hJaone : J ≤ A - 1 / 2 := by linarith
  have hExpTau : 1 < Real.exp τ := Real.one_lt_exp_iff.2 hτ
  have hExpLower : ∀ᵐ o ∂μ,
      Real.exp τ ≤ Real.exp (τ * Real.rpow (w o) α) := by
    filter_upwards [hwone] with o ho
    have hpower : 1 ≤ Real.rpow (w o) α := by
      have hhpower := Real.rpow_le_rpow (show (0 : ℝ) ≤ 1 by norm_num) ho hα.le
      simpa only [Real.one_rpow, Real.rpow_eq_pow] using hhpower
    exact Real.exp_le_exp_of_le (by nlinarith)
  have hExpNonneg : ∀ᵐ o ∂μ,
      0 ≤ Real.exp (τ * Real.rpow (w o) α) := by
    exact hExpLower.mono fun _ ho => le_trans (by linarith [hExpTau]) ho
  have hMlower : Real.exp τ ≤ M := by
    have hhM := integral_mono_ae (integrable_const (Real.exp τ)) hwexp hExpLower
    simpa only [integral_const, probReal_univ, one_smul] using hhM
  have hM1 : 1 < M := lt_of_lt_of_le hExpTau hMlower
  have hM0 : 0 < M := by linarith
  have h2M0 : 0 < 2 * M := by linarith
  refine ⟨he, he33, hteq, hA, hMlower, hM1, hJae, hJhalf, hJa, hJat, hJaone, ?_⟩
  intro n hn
  let Rn : ℝ := Real.rpow (A * Real.log (n : ℝ) / τ) (1 / α)
  let Cn : Set Ω := {o : Ω | w o ≤ Rn}
  let πn : ℝ := μ.real Cnᶜ
  let dn : ℝ := μ.real Cn
  let νn : Measure Ω := (μ Cn)⁻¹ • μ.restrict Cn
  let bn : ℝ := ∫ o in Cnᶜ, w o ∂μ
  have hceil : max (3 : ℝ) (Real.rpow (2 * M) (1 / A)) ≤ (N0 : ℝ) :=
    Nat.le_ceil _
  have hNn : (N0 : ℝ) ≤ (n : ℝ) := (Nat.cast_le (α := ℝ)).2 hn
  have hn3real : (3 : ℝ) ≤ (n : ℝ) :=
    (le_max_left _ _).trans (hceil.trans hNn)
  have hn3 : 3 ≤ n := (Nat.cast_le (α := ℝ)).1 (by simpa using hn3real)
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hthreshold : Real.rpow (2 * M) (1 / A) ≤ (n : ℝ) :=
    (le_max_right _ _).trans (hceil.trans hNn)
  have hthreshold0 : 0 < Real.rpow (2 * M) (1 / A) :=
    Real.rpow_pos_of_pos h2M0 _
  have hthresholdPow : Real.rpow (Real.rpow (2 * M) (1 / A)) A = 2 * M := by
    change ((2 * M) ^ (1 / A)) ^ A = 2 * M
    rw [← Real.rpow_mul h2M0.le]
    have hinv : (1 / A) * A = 1 := by field_simp [ne_of_gt hA]
    rw [hinv, Real.rpow_one]
  have hnPowLower : 2 * M ≤ Real.rpow (n : ℝ) A := by
    have hhpow := Real.rpow_le_rpow hthreshold0.le hthreshold hA.le
    change Real.rpow (Real.rpow (2 * M) (1 / A)) A ≤
      Real.rpow (n : ℝ) A at hhpow
    rw [hthresholdPow] at hhpow
    exact hhpow
  have hnPowPos : 0 < Real.rpow (n : ℝ) A := Real.rpow_pos_of_pos hn0 _
  have hnNegPow : Real.rpow (n : ℝ) (-A) = (Real.rpow (n : ℝ) A)⁻¹ := by
    change (n : ℝ) ^ (-A) = ((n : ℝ) ^ A)⁻¹
    exact Real.rpow_neg hn0.le A
  have hhalf : M * Real.rpow (n : ℝ) (-A) ≤ (1 / 2 : ℝ) := by
    rw [hnNegPow, ← div_eq_mul_inv]
    apply (div_le_iff₀ hnPowPos).2
    nlinarith [hnPowLower]
  have hbase0 : 0 < A * Real.log (n : ℝ) / τ :=
    div_pos (mul_pos hA hnlog) hτ
  have hRn0 : 0 < Rn := Real.rpow_pos_of_pos hbase0 _
  have hRnPow : Real.rpow Rn α = A * Real.log (n : ℝ) / τ := by
    change ((A * Real.log (n : ℝ) / τ) ^ (1 / α)) ^ α =
      A * Real.log (n : ℝ) / τ
    rw [← Real.rpow_mul hbase0.le]
    have hinv : (1 / α) * α = 1 := by field_simp [ne_of_gt hα]
    rw [hinv, Real.rpow_one]
  have hCn : MeasurableSet Cn := measurableSet_le hw measurable_const
  have hEvent : ∀ᵐ o ∂μ,
      (w o ≤ Rn ↔ τ * Real.rpow (w o) α ≤ A * Real.log (n : ℝ)) := by
    filter_upwards [hwone] with o ho
    have hwo : 0 ≤ w o := le_trans zero_le_one ho
    have hreflect := Real.rpow_le_rpow_iff hwo hRn0.le hα
    change (Real.rpow (w o) α ≤ Real.rpow Rn α ↔ w o ≤ Rn) at hreflect
    rw [hRnPow] at hreflect
    calc
      w o ≤ Rn ↔ Real.rpow (w o) α ≤ A * Real.log (n : ℝ) / τ := hreflect.symm
      _ ↔ τ * Real.rpow (w o) α ≤ A * Real.log (n : ℝ) := by
        rw [le_div_iff₀ hτ, mul_comm (Real.rpow (w o) α) τ]
  have hnPowExp : Real.rpow (n : ℝ) A = Real.exp (A * Real.log (n : ℝ)) := by
    change (n : ℝ) ^ A = Real.exp (A * Real.log (n : ℝ))
    rw [Real.rpow_def_of_pos hn0, mul_comm (Real.log (n : ℝ)) A]
  have hBadMem : ∀ᵐ o ∂μ.restrict Cnᶜ, o ∈ Cnᶜ :=
    ae_restrict_of_forall_mem hCn.compl (fun _ ho => ho)
  have hEventBad : ∀ᵐ o ∂μ.restrict Cnᶜ,
      (w o ≤ Rn ↔ τ * Real.rpow (w o) α ≤ A * Real.log (n : ℝ)) :=
    ae_restrict_of_ae hEvent
  have hTailPoint : ∀ᵐ o ∂μ.restrict Cnᶜ,
      Real.rpow (n : ℝ) A ≤ Real.exp (τ * Real.rpow (w o) α) := by
    filter_upwards [hBadMem, hEventBad] with o ho heo
    change ¬ w o ≤ Rn at ho
    have hY : A * Real.log (n : ℝ) < τ * Real.rpow (w o) α :=
      lt_of_not_ge (mt heo.2 ho)
    rw [hnPowExp]
    exact Real.exp_le_exp_of_le hY.le
  have hTailIntegral : Real.rpow (n : ℝ) A * πn ≤ M := by
    calc
      Real.rpow (n : ℝ) A * πn = ∫ o in Cnᶜ, Real.rpow (n : ℝ) A ∂μ := by
        rw [setIntegral_const]
        simp only [smul_eq_mul]
        change Real.rpow (n : ℝ) A * πn = πn * Real.rpow (n : ℝ) A
        ring
      _ ≤ ∫ o in Cnᶜ, Real.exp (τ * Real.rpow (w o) α) ∂μ :=
        integral_mono_ae (integrable_const _) hwexp.restrict hTailPoint
      _ ≤ M := setIntegral_le_integral hwexp hExpNonneg
  have hπ0 : 0 ≤ πn := measureReal_nonneg
  have hπtail : πn ≤ M * Real.rpow (n : ℝ) (-A) := by
    rw [hnNegPow, ← div_eq_mul_inv]
    apply (le_div_iff₀ hnPowPos).2
    nlinarith [hTailIntegral]
  have hdn : dn = 1 - πn := by
    have hc := probReal_compl_eq_one_sub (μ := μ) hCn
    change πn = 1 - dn at hc
    linarith
  have hdhalf : (1 / 2 : ℝ) ≤ dn := by linarith [hπtail, hhalf]
  have hseed := hfinite Rn hdhalf (0 : ℝ) ⟨le_rfl, zero_le_one⟩
  rcases hseed with
    ⟨_, _, _, _, _, hb0, hνprob, hνac, _, _, _, _, _, _, hw2, _⟩
  have hwSqInt : Integrable (fun o => w o ^ 2) μ := hw2.integrable_sq
  have hw2bad : MemLp w 2 (μ.restrict Cnᶜ) := MemLp.restrict Cnᶜ hw2
  have hOne2 : MemLp (fun _ : Ω => (1 : ℝ)) 2 (μ.restrict Cnᶜ) :=
    memLp_const (1 : ℝ)
  have hwNonnegBad : ∀ᵐ o ∂μ.restrict Cnᶜ, 0 ≤ w o := by
    exact (ae_restrict_of_ae hwone).mono fun _ ho => le_trans zero_le_one ho
  have hCauchy : bn ≤ Real.sqrt (∫ o in Cnᶜ, w o ^ 2 ∂μ) * Real.sqrt πn := by
    have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := μ.restrict Cnᶜ) Real.HolderConjugate.two_two
      (f := w) (g := fun _ : Ω => (1 : ℝ)) hwNonnegBad
      (Filter.Eventually.of_forall (fun _ => zero_le_one))
      (by simpa using hw2bad) (by simpa using hOne2)
    change (∫ o in Cnᶜ, w o * (1 : ℝ) ∂μ) ≤
      (∫ o in Cnᶜ, (w o) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
      (∫ o in Cnᶜ, (1 : ℝ) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) at hHolder
    simp only [mul_one, Real.rpow_ofNat, Real.one_rpow, one_pow] at hHolder
    have hOneIntegral : (∫ _ in Cnᶜ, (1 : ℝ) ∂μ) = πn := by
      rw [setIntegral_const]
      simp only [smul_eq_mul]
      change πn * 1 = πn
      ring
    rw [hOneIntegral] at hHolder
    change bn ≤ (∫ o in Cnᶜ, w o ^ 2 ∂μ) ^ (1 / 2 : ℝ) *
      πn ^ (1 / 2 : ℝ) at hHolder
    simpa only [← Real.sqrt_eq_rpow] using hHolder
  have hwSq0 : 0 ≤ ∫ o, w o ^ 2 ∂μ :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall (fun o => sq_nonneg (w o)))
  have hwSqBad0 : 0 ≤ ∫ o in Cnᶜ, w o ^ 2 ∂μ :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall (fun o => sq_nonneg (w o)))
  have hW2sq : W2 ^ 2 = ∫ o, w o ^ 2 ∂μ := by
    dsimp only [W2]
    exact Real.sq_sqrt hwSq0
  have hbSqBad : bn ^ 2 ≤ πn * (∫ o in Cnᶜ, w o ^ 2 ∂μ) := by
    have hroot0 : 0 ≤ Real.sqrt (∫ o in Cnᶜ, w o ^ 2 ∂μ) * Real.sqrt πn :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hprod : 0 ≤
        (Real.sqrt (∫ o in Cnᶜ, w o ^ 2 ∂μ) * Real.sqrt πn - bn) *
        (Real.sqrt (∫ o in Cnᶜ, w o ^ 2 ∂μ) * Real.sqrt πn + bn) :=
      mul_nonneg (sub_nonneg.2 hCauchy) (add_nonneg hroot0 hb0)
    have hsquare :
        (Real.sqrt (∫ o in Cnᶜ, w o ^ 2 ∂μ) * Real.sqrt πn) ^ 2 =
          πn * (∫ o in Cnᶜ, w o ^ 2 ∂μ) := by
      rw [mul_pow, Real.sq_sqrt hwSqBad0, Real.sq_sqrt hπ0]
      ring
    nlinarith only [hprod, hsquare]
  have hBadSqLe : (∫ o in Cnᶜ, w o ^ 2 ∂μ) ≤ W2 ^ 2 := by
    calc
      (∫ o in Cnᶜ, w o ^ 2 ∂μ) ≤ ∫ o, w o ^ 2 ∂μ :=
        setIntegral_le_integral hwSqInt
          (Filter.Eventually.of_forall (fun o => sq_nonneg (w o)))
      _ = W2 ^ 2 := hW2sq.symm
  have hbSq : bn ^ 2 ≤ W2 ^ 2 * πn := by
    calc
      bn ^ 2 ≤ πn * (∫ o in Cnᶜ, w o ^ 2 ∂μ) := hbSqBad
      _ ≤ πn * W2 ^ 2 := mul_le_mul_of_nonneg_left hBadSqLe hπ0
      _ = W2 ^ 2 * πn := mul_comm _ _
  have hbSqrt : bn ≤ W2 * Real.sqrt πn := by
    have hright0 : 0 ≤ W2 * Real.sqrt πn :=
      mul_nonneg hW20 (Real.sqrt_nonneg _)
    have hrightSq : (W2 * Real.sqrt πn) ^ 2 = W2 ^ 2 * πn := by
      rw [mul_pow, Real.sq_sqrt hπ0]
    by_contra hnot
    have hlt : W2 * Real.sqrt πn < bn := lt_of_not_ge hnot
    have hprod : 0 < (bn - W2 * Real.sqrt πn) * (bn + W2 * Real.sqrt πn) :=
      mul_pos (sub_pos.2 hlt) (by linarith)
    nlinarith only [hprod, hrightSq, hbSq]
  have hsqrtPower : Real.sqrt (Real.rpow (n : ℝ) (-A)) =
      Real.rpow (n : ℝ) (-A / 2) := by
    rw [Real.sqrt_eq_rpow]
    change ((n : ℝ) ^ (-A)) ^ (1 / 2 : ℝ) = (n : ℝ) ^ (-A / 2)
    rw [← Real.rpow_mul hn0.le]
    have hexp : (-A) * (1 / 2 : ℝ) = -A / 2 := by ring
    rw [hexp]
  have hbTail : bn ≤ W2 * Real.sqrt M * Real.rpow (n : ℝ) (-A / 2) := by
    calc
      bn ≤ W2 * Real.sqrt πn := hbSqrt
      _ ≤ W2 * Real.sqrt (M * Real.rpow (n : ℝ) (-A)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hπtail) hW20
      _ = W2 * Real.sqrt M * Real.rpow (n : ℝ) (-A / 2) := by
        rw [Real.sqrt_mul hM0.le, hsqrtPower]
        ring
  have hbSqTail : bn ^ 2 ≤ W2 ^ 2 * M * Real.rpow (n : ℝ) (-A) := by
    calc
      bn ^ 2 ≤ W2 ^ 2 * πn := hbSq
      _ ≤ W2 ^ 2 * (M * Real.rpow (n : ℝ) (-A)) :=
        mul_le_mul_of_nonneg_left hπtail (sq_nonneg W2)
      _ = W2 ^ 2 * M * Real.rpow (n : ℝ) (-A) := by ring
  have hPiPower : ∀ s : ℝ, 0 ≤ s →
      Real.rpow πn s ≤ Real.rpow M s * Real.rpow (n : ℝ) (-(A * s)) := by
    intro s hs
    calc
      Real.rpow πn s ≤ Real.rpow (M * Real.rpow (n : ℝ) (-A)) s := by
        exact Real.rpow_le_rpow hπ0 hπtail hs
      _ = Real.rpow M s * Real.rpow (Real.rpow (n : ℝ) (-A)) s := by
        change (M * (n : ℝ) ^ (-A)) ^ s = M ^ s * ((n : ℝ) ^ (-A)) ^ s
        exact Real.mul_rpow hM0.le (Real.rpow_pos_of_pos hn0 (-A)).le
      _ = Real.rpow M s * Real.rpow (n : ℝ) (-(A * s)) := by
        change M ^ s * ((n : ℝ) ^ (-A)) ^ s = M ^ s * (n : ℝ) ^ (-(A * s))
        rw [← Real.rpow_mul hn0.le, neg_mul]
  have hRatePower : ∀ a : ℝ, J ≤ a →
      Real.rpow (n : ℝ) (-a) ≤ Real.rpow (n : ℝ) (-J) := by
    intro a ha
    exact Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg ha)
  have heRate : Real.rpow (n : ℝ) (-(A * e)) ≤ Real.rpow (n : ℝ) (-J) :=
    hRatePower (A * e) hJae
  have hhalfRate : Real.rpow (n : ℝ) (-A / 2) ≤ Real.rpow (n : ℝ) (-J) := by
    have hh := hRatePower (A / 2) hJhalf
    have hexp : -(A / 2) = -A / 2 := by ring
    rw [hexp] at hh
    exact hh
  have haRate : Real.rpow (n : ℝ) (-A) ≤ Real.rpow (n : ℝ) (-J) :=
    hRatePower A hJa
  have hPiRate : Real.rpow πn e ≤ Real.rpow M e * Real.rpow (n : ℝ) (-J) :=
    (hPiPower e he.le).trans
      (mul_le_mul_of_nonneg_left heRate (Real.rpow_nonneg hM0.le e))
  have hbRate : bn ≤ W2 * Real.sqrt M * Real.rpow (n : ℝ) (-J) :=
    hbTail.trans (mul_le_mul_of_nonneg_left hhalfRate
      (mul_nonneg hW20 (Real.sqrt_nonneg M)))
  have hbSqRate : bn ^ 2 ≤ W2 ^ 2 * M * Real.rpow (n : ℝ) (-J) :=
    hbSqTail.trans (mul_le_mul_of_nonneg_left haRate (mul_nonneg (sq_nonneg W2) hM0.le))
  have hSqrtMul : ∀ a : ℝ,
      Real.sqrt (n : ℝ) * Real.rpow (n : ℝ) (-a) =
        Real.rpow (n : ℝ) (-(a - 1 / 2)) := by
    intro a
    rw [Real.sqrt_eq_rpow]
    change (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-a) =
      (n : ℝ) ^ (-(a - 1 / 2))
    rw [← Real.rpow_add hn0]
    have hexp : (1 / 2 : ℝ) + -a = -(a - 1 / 2) := by ring
    rw [hexp]
  have hPiScaled : Real.sqrt (n : ℝ) * Real.rpow πn t ≤
      Real.rpow M t * Real.rpow (n : ℝ) (-J) := by
    calc
      Real.sqrt (n : ℝ) * Real.rpow πn t ≤
          Real.sqrt (n : ℝ) * (Real.rpow M t * Real.rpow (n : ℝ) (-(A * t))) :=
        mul_le_mul_of_nonneg_left (hPiPower t ht.le) (Real.sqrt_nonneg _)
      _ = Real.rpow M t * (Real.sqrt (n : ℝ) * Real.rpow (n : ℝ) (-(A * t))) := by
        ring
      _ = Real.rpow M t * Real.rpow (n : ℝ) (-(A * t - 1 / 2)) := by
        rw [hSqrtMul (A * t)]
      _ ≤ Real.rpow M t * Real.rpow (n : ℝ) (-J) :=
        mul_le_mul_of_nonneg_left (hRatePower (A * t - 1 / 2) hJat)
          (Real.rpow_nonneg hM0.le t)
  have hbSqScaled : Real.sqrt (n : ℝ) * bn ^ 2 ≤
      W2 ^ 2 * M * Real.rpow (n : ℝ) (-J) := by
    calc
      Real.sqrt (n : ℝ) * bn ^ 2 ≤
          Real.sqrt (n : ℝ) * (W2 ^ 2 * M * Real.rpow (n : ℝ) (-A)) :=
        mul_le_mul_of_nonneg_left hbSqTail (Real.sqrt_nonneg _)
      _ = W2 ^ 2 * M * (Real.sqrt (n : ℝ) * Real.rpow (n : ℝ) (-A)) := by ring
      _ = W2 ^ 2 * M * Real.rpow (n : ℝ) (-(A - 1 / 2)) := by rw [hSqrtMul A]
      _ ≤ W2 ^ 2 * M * Real.rpow (n : ℝ) (-J) :=
        mul_le_mul_of_nonneg_left (hRatePower (A - 1 / 2) hJaone)
          (mul_nonneg (sq_nonneg W2) hM0.le)
  refine ⟨hn3, hRn0, hCn, hEvent, hπ0, hπtail, hhalf, hdn, hdhalf,
    hνprob, hνac, hb0, hbSq, hbTail, ?_⟩
  intro lam hLam
  let Hn : Ω → Ω → ℝ := fun o y => g o + g y + lam * r o y
  let qn : ℝ := ∫ z : Ω × Ω, Hn z.1 z.2 ∂(νn.prod νn)
  let Gn : Ω → ℝ := fun o => (∫ y, Hn o y ∂νn) - qn
  let σ2n : ℝ := ∫ o, Gn o ^ 2 ∂νn
  have hAll := hfinite Rn hdhalf lam hLam
  rcases hAll with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, hG2, _, hGcenter, _, _, _, hσnonneg, _, _, _, _, _, _, _, _,
      hVarFinite, hMeanFinite⟩
  change MemLp Gn 2 νn ∧ (∫ o, Gn o ∂νn) = 0 ∧ 0 ≤ σ2n ∧
    |σ2n - 1| ≤ Kvar * Real.rpow (n : ℝ) (-J) ∧
    (∀ m : ℕ, m ≤ n →
      Real.sqrt (m : ℝ) * |qn| ≤ Kmean * Real.rpow (n : ℝ) (-J))
  refine ⟨hG2, hGcenter, hσnonneg, ?_, ?_⟩
  · have hinside : Real.rpow πn e + bn + bn ^ 2 ≤
        (Real.rpow M e + W2 * Real.sqrt M + W2 ^ 2 * M) *
          Real.rpow (n : ℝ) (-J) := by
      nlinarith only [hPiRate, hbRate, hbSqRate]
    calc
      |σ2n - 1| ≤ Cvar * (Real.rpow πn e + bn + bn ^ 2) := hVarFinite
      _ ≤ Cvar * ((Real.rpow M e + W2 * Real.sqrt M + W2 ^ 2 * M) *
          Real.rpow (n : ℝ) (-J)) := mul_le_mul_of_nonneg_left hinside hCvar.le
      _ = Kvar * Real.rpow (n : ℝ) (-J) := by
        dsimp only [Kvar]
        ring
  · intro m hmn
    have hinside : Real.sqrt (n : ℝ) * Real.rpow πn t +
        Real.sqrt (n : ℝ) * bn ^ 2 ≤
        (Real.rpow M t + W2 ^ 2 * M) * Real.rpow (n : ℝ) (-J) := by
      nlinarith only [hPiScaled, hbSqScaled]
    calc
      Real.sqrt (m : ℝ) * |qn| ≤
          Cmean * Real.sqrt (n : ℝ) * (Real.rpow πn t + bn ^ 2) :=
        hMeanFinite m n hmn
      _ = Cmean * (Real.sqrt (n : ℝ) * Real.rpow πn t +
          Real.sqrt (n : ℝ) * bn ^ 2) := by ring
      _ ≤ Cmean * ((Real.rpow M t + W2 ^ 2 * M) * Real.rpow (n : ℝ) (-J)) :=
        mul_le_mul_of_nonneg_left hinside hCmean.le
      _ = Kmean * Real.rpow (n : ℝ) (-J) := by
        dsimp only [Kmean]
        ring


end

end Shao.OQ6.LogarithmicConditionalRates
