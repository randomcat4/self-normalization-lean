import Shao.Probability.TiltedLowFrequency

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

private theorem sgp_exp_square_bound (x : ℝ) (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-x) ≤ 4 := by
  have he : x / 2 ≤ Real.exp (x / 2) := by linarith [Real.add_one_le_exp (x / 2)]
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-(x / 2))).le
  have hid : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [hid] at hm
  have hp := pow_le_pow_left₀ (mul_nonneg (by positivity) (Real.exp_pos _).le) hm 2
  have hid2 : (Real.exp (-(x / 2))) ^ 2 = Real.exp (-x) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [mul_pow, hid2] at hp
  nlinarith only [hp]

private theorem sgp_schedule_guards (y h N lam : ℝ)
    (hy : 2 ≤ y) (hh : 0 < h) (hN : (1 / 16 : ℝ) ≤ N)
    (hyh : y * h ≤ (1 / 64 : ℝ))
    (hlam : y / Real.sqrt N ≤ lam) :
    let s : ℝ := lam * y / Real.sqrt N
    0 ≤ lam ∧ 0 ≤ s ∧ s ≤ lam ^ 2 ∧ s * h ≤ lam := by
  have hNp : 0 < N := by linarith
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
  have hs4 : (1 / 4 : ℝ) ≤ Real.sqrt N := by
    nlinarith [Real.sq_sqrt hNp.le, Real.sqrt_nonneg N]
  have hl0 : 0 ≤ lam := (by positivity : 0 ≤ y / Real.sqrt N).trans hlam
  have hsq := mul_le_mul_of_nonneg_left hlam hl0
  have hratio : y * h / Real.sqrt N ≤ 1 := by
    apply (div_le_one hs).2
    linarith only [hyh, hs4]
  have hslope := mul_le_mul_of_nonneg_left hratio hl0
  dsimp only
  refine ⟨hl0, by positivity, ?_, ?_⟩
  · convert hsq using 1 <;> ring
  · convert hslope using 1 <;> ring

private theorem sgp_log_clock_mono (T t0 : ℝ)
    (hT : 0 < T) (ht : 0 < t0) (hTt : T ≤ t0)
    (hte : t0 ≤ Real.exp (-1)) :
    T * Real.log (1 / T) ≤ t0 * Real.log (1 / t0) := by
  let ell : ℝ := Real.log (1 / T)
  let ell0 : ℝ := Real.log (1 / t0)
  have he0 : 1 ≤ ell0 := by
    have hb := Real.log_le_log ht hte
    rw [Real.log_exp] at hb
    dsimp [ell0]; simp only [one_div, Real.log_inv]; linarith
  have he : ell0 ≤ ell := by
    have hb := Real.log_le_log hT hTt
    dsimp [ell0, ell]; simp only [one_div, Real.log_inv]; linarith
  have hid : t0 * Real.exp (-(ell - ell0)) = T := by
    have h1 : Real.exp (-ell) = T := by
      dsimp [ell]; simp only [one_div, Real.log_inv, neg_neg]; exact Real.exp_log hT
    have h0 : Real.exp ell0 = 1 / t0 := Real.exp_log (by positivity)
    rw [show -(ell - ell0) = -ell + ell0 by ring, Real.exp_add, h1, h0]
    field_simp
  have hb : ell ≤ ell0 * Real.exp (ell - ell0) := by
    have hm := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (ell - ell0)) (by linarith : 0 ≤ ell0)
    have hp := mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr he0)
    nlinarith only [hm, hp]
  have hm := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-(ell - ell0))).le
  have hcancel : Real.exp (ell - ell0) * Real.exp (-(ell - ell0)) = 1 := by
    rw [← Real.exp_add]; simp
  have hm2 : ell * Real.exp (-(ell - ell0)) ≤ ell0 := by
    rw [mul_assoc, hcancel, mul_one] at hm
    exact hm
  have hfinal := mul_le_mul_of_nonneg_left hm2 ht.le
  change T * ell ≤ t0 * ell0
  rw [← hid]
  nlinarith only [hfinal]

private theorem sgp_short_log_clock_bound
    (epsilon0 alpha eta0 y gamma T : ℝ)
    (hepsilon0 : 0 < epsilon0) (hepsilon0One : epsilon0 ≤ 1)
    (halpha : 0 ≤ alpha) (halphaSmall : alpha ≤ (1 / 48 : ℝ))
    (heta0 : 0 < eta0) (heta0One : eta0 ≤ 1)
    (hy : 0 ≤ y) (hgamma : 0 < gamma)
    (hgammaBudget : gamma * (1 + y) ^ 3 ≤ eta0)
    (hclock : gamma ^ 2 ≤ T) (hT : T < 1) :
    let h : ℝ := epsilon0 / (1 + y)
    let ell : ℝ := Real.log (1 / T)
    let r : ℝ := Real.log (1 / gamma)
    let lam : ℝ := (alpha / h) * ell
    let Gamma : ℝ := 8 * Real.exp (8 * lam * h) * gamma
    0 < T ∧ 0 ≤ r ∧ 0 < ell ∧ ell ≤ 2 * r ∧
      lam * h = alpha * ell ∧ 0 ≤ lam ∧ 0 < Gamma ∧
      (y + lam) * Gamma ≤ (10 / epsilon0) * Real.sqrt eta0 := by
  dsimp only
  let a : ℝ := 1 + y
  let h : ℝ := epsilon0 / (1 + y)
  let ell : ℝ := Real.log (1 / T)
  let r : ℝ := Real.log (1 / gamma)
  let lam : ℝ := (alpha / h) * ell
  let Gamma : ℝ := 8 * Real.exp (8 * lam * h) * gamma
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have hap : 0 < a := by linarith
  have hh : 0 < h := div_pos hepsilon0 hap
  have hg1 : gamma ≤ 1 := by
    have hpow : 1 ≤ a ^ 3 := one_le_pow₀ ha
    have hm := mul_le_mul_of_nonneg_left hpow hgamma.le
    change gamma * a ^ 3 ≤ eta0 at hgammaBudget
    nlinarith only [hm, hgammaBudget, heta0One]
  have hTp : 0 < T := (sq_pos_of_pos hgamma).trans_le hclock
  have hr : 0 ≤ r := by
    dsimp [r]
    exact Real.log_nonneg ((one_le_div hgamma).mpr hg1)
  have hell : 0 < ell := by
    dsimp [ell]
    exact Real.log_pos ((one_lt_div hTp).mpr hT)
  have hlog := Real.log_le_log (sq_pos_of_pos hgamma) hclock
  rw [Real.log_pow] at hlog
  norm_num at hlog
  have hrel : ell ≤ 2 * r := by
    dsimp [ell, r]
    simp only [one_div, Real.log_inv]
    linarith
  have hge : Real.exp (-r) = gamma := by
    dsimp [r]; simp only [one_div, Real.log_inv, neg_neg]
    exact Real.exp_log hgamma
  have hlh : lam * h = alpha * ell := by dsimp [lam]; field_simp <;> ring
  have hlval : lam = (alpha / epsilon0) * a * ell := by
    dsimp [lam, h, a]; field_simp <;> ring
  have hl0 : 0 ≤ lam := by dsimp [lam]; positivity
  have hG : 0 < Gamma := by dsimp [Gamma]; positivity
  have hsmall : 8 * alpha * ell ≤ r / 3 := by
    have hm := mul_le_mul_of_nonneg_left hrel (show 0 ≤ 8 * alpha by positivity)
    have hn := mul_le_mul_of_nonneg_right halphaSmall hr
    nlinarith only [hm, hn]
  have hlin : y + lam ≤ a * (1 + (2 * alpha / epsilon0) * r) := by
    rw [hlval]
    have hm := mul_le_mul_of_nonneg_left hrel
      (show 0 ≤ (alpha / epsilon0) * a by positivity)
    dsimp [a] at *
    ring_nf at hm ⊢
    linarith only [hm]
  have hex : Real.exp (8 * lam * h) * gamma ≤ Real.exp (-(2 * r / 3)) := by
    rw [← hge, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hv : 8 * lam * h = 8 * alpha * ell := by nlinarith only [hlh]
    rw [hv]
    linarith only [hsmall]
  have hw : r * Real.exp (-(r / 6)) ≤ 6 := by
    have he : r / 6 ≤ Real.exp (r / 6) := by linarith [Real.add_one_le_exp (r / 6)]
    have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-(r / 6))).le
    have hid : Real.exp (r / 6) * Real.exp (-(r / 6)) = 1 := by
      rw [← Real.exp_add]; simp
    rw [hid] at hm
    nlinarith only [hm]
  have hneg : Real.exp (-(r / 6)) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hb : (1 + (2 * alpha / epsilon0) * r) * Real.exp (-(r / 6)) ≤
      1 + 12 * alpha / epsilon0 := by
    have hm := mul_le_mul_of_nonneg_left hw (show 0 ≤ 2 * alpha / epsilon0 by positivity)
    ring_nf at hm hneg ⊢
    linarith only [hm, hneg]
  have hc : 1 + 12 * alpha / epsilon0 ≤ 5 / (4 * epsilon0) := by
    apply (le_div_iff₀ (show 0 < 4 * epsilon0 by positivity)).2
    have hid : (12 * alpha / epsilon0) * (4 * epsilon0) = 48 * alpha := by field_simp; ring
    rw [add_mul, hid]
    nlinarith only [hepsilon0One, halphaSmall]
  have hehalf : Real.exp (-(r / 2)) = Real.sqrt gamma := by
    have he2 : Real.exp (-(r / 2)) ^ 2 = gamma := by
      rw [← Real.exp_nat_mul]; convert hge using 1 <;> ring
    have hs := Real.sq_sqrt hgamma.le
    nlinarith [Real.sqrt_nonneg gamma, (Real.exp_pos (-(r / 2))).le]
  have hsqrt : a * Real.sqrt gamma ≤ Real.sqrt eta0 := by
    have hpow : a ^ 2 ≤ a ^ 3 := by nlinarith only [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr ha)]
    have hm := mul_le_mul_of_nonneg_right hpow hgamma.le
    have hg2 : (a * Real.sqrt gamma) ^ 2 ≤ eta0 := by
      rw [mul_pow, Real.sq_sqrt hgamma.le]
      nlinarith only [hm, hgammaBudget]
    nlinarith [Real.sq_sqrt heta0.le, Real.sqrt_nonneg eta0,
      mul_nonneg hap.le (Real.sqrt_nonneg gamma)]
  have hsplit : Real.exp (-(2 * r / 3)) =
      Real.exp (-(r / 2)) * Real.exp (-(r / 6)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hmain : (y + lam) * Gamma ≤ (10 / epsilon0) * Real.sqrt eta0 := by
    calc
      (y + lam) * Gamma = 8 * (y + lam) * (Real.exp (8 * lam * h) * gamma) := by dsimp [Gamma]; ring
      _ ≤ 8 * (a * (1 + (2 * alpha / epsilon0) * r)) * Real.exp (-(2 * r / 3)) := by gcongr
      _ = 8 * (a * Real.sqrt gamma) *
          ((1 + (2 * alpha / epsilon0) * r) * Real.exp (-(r / 6))) := by rw [hsplit, hehalf]; ring
      _ ≤ 8 * (a * Real.sqrt gamma) * (5 / (4 * epsilon0)) := by
        exact mul_le_mul_of_nonneg_left (hb.trans hc) (by positivity)
      _ ≤ 8 * Real.sqrt eta0 * (5 / (4 * epsilon0)) := by gcongr
      _ = _ := by field_simp; ring
  exact ⟨hTp, hr, hell, hrel, hlh, hl0, hG, hmain⟩

private theorem sgp_macroscopic_clock_bound
    (epsilon0 t0 eta0 y gamma T N : ℝ)
    (hepsilon0 : 0 < epsilon0) (ht0 : 0 < t0)
    (heta0 : 0 ≤ eta0) (hy : 0 ≤ y) (hgamma : 0 < gamma)
    (hgammaBudget : gamma * (1 + y) ^ 3 ≤ eta0)
    (hT : t0 ≤ T) (hTN : T ≤ N)
    (hNlo : (1 / 16 : ℝ) ≤ N) (hNhi : N ≤ 7) :
    let h : ℝ := epsilon0 / (1 + y)
    let lam : ℝ := y * Real.sqrt N / T
    let Gamma : ℝ := 8 * Real.exp (8 * lam * h) * gamma
    y / Real.sqrt N ≤ lam ∧ 0 ≤ lam ∧ 0 < Gamma ∧
      lam ≤ 3 * y / t0 ∧ lam * h ≤ 3 * epsilon0 / t0 ∧
      Gamma ≤ 8 * Real.exp (24 * epsilon0 / t0) * gamma ∧
      (y + lam) * Gamma ≤
        8 * (1 + 3 / t0) * Real.exp (24 * epsilon0 / t0) * eta0 := by
  dsimp only
  let a : ℝ := 1 + y
  let h : ℝ := epsilon0 / (1 + y)
  let lam : ℝ := y * Real.sqrt N / T
  let Gamma : ℝ := 8 * Real.exp (8 * lam * h) * gamma
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have hap : 0 < a := by linarith
  have hTp : 0 < T := ht0.trans_le hT
  have hNp : 0 < N := by linarith
  have hsq := Real.sq_sqrt hNp.le
  have hroot : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
  have hroot3 : Real.sqrt N ≤ 3 := by nlinarith [Real.sqrt_nonneg N]
  have hl0 : 0 ≤ lam := by dsimp [lam]; positivity
  have hG : 0 < Gamma := by dsimp [Gamma]; positivity
  have hlo : y / Real.sqrt N ≤ lam := by
    dsimp [lam]
    apply (div_le_div_iff₀ hroot hTp).2
    rw [mul_assoc, ← pow_two, hsq]
    exact mul_le_mul_of_nonneg_left hTN hy
  have hlu : lam ≤ 3 * y / t0 := by
    dsimp [lam]
    exact div_le_div₀ (by positivity) (by nlinarith only [mul_le_mul_of_nonneg_left hroot3 hy]) ht0 hT
  have hlh : lam * h ≤ 3 * epsilon0 / t0 := by
    calc
      lam * h ≤ (3 * y / t0) * (epsilon0 / a) := by dsimp [h, a] at *; gcongr
      _ = (3 * epsilon0 / t0) * (y / a) := by ring
      _ ≤ (3 * epsilon0 / t0) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (div_le_one hap).mpr (by dsimp [a]; linarith)
      _ = _ := by ring
  have hGb : Gamma ≤ 8 * Real.exp (24 * epsilon0 / t0) * gamma := by
    dsimp [Gamma]
    gcongr
    calc
      8 * lam * h = 8 * (lam * h) := by ring
      _ ≤ 8 * (3 * epsilon0 / t0) := mul_le_mul_of_nonneg_left hlh (by norm_num)
      _ = _ := by ring
  have hlin : y + lam ≤ a * (1 + 3 / t0) := by
    have hcoef : 0 ≤ 3 / t0 := by positivity
    dsimp [a]
    ring_nf at hlu hcoef ⊢
    linarith only [hlu, hcoef]
  have hag : a * gamma ≤ eta0 := by
    have hp : a ≤ a ^ 3 := by nlinarith only [mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ a * (a + 1) by positivity)]
    have hm := mul_le_mul_of_nonneg_right hp hgamma.le
    change gamma * a ^ 3 ≤ eta0 at hgammaBudget
    nlinarith only [hm, hgammaBudget]
  have hpay : (y + lam) * Gamma ≤
      8 * (1 + 3 / t0) * Real.exp (24 * epsilon0 / t0) * eta0 := by
    calc
      _ ≤ (a * (1 + 3 / t0)) * (8 * Real.exp (24 * epsilon0 / t0) * gamma) := by gcongr
      _ = (8 * (1 + 3 / t0) * Real.exp (24 * epsilon0 / t0)) * (a * gamma) := by ring
      _ ≤ _ := by gcongr
  exact ⟨hlo, hl0, hG, hlu, hlh, hGb, hpay⟩

theorem sourceGrowingTilt_explicit_constant_payment
    (L L2 : ℝ) (hL : 1600 ≤ L) (hL2 : 20 ≤ L2) :
    let alpha : ℝ := 1 / 1024
    let epsilon0 : ℝ := min (1 / (64 * Real.sqrt L2)) (alpha / (8 * L))
    let u : ℝ := 48 * alpha / epsilon0
    let t0 : ℝ := Real.exp (-u)
    let eta0 : ℝ := min (1 / 16)
      (min (Real.sqrt t0 / (2 * Real.sqrt L2))
        (min ((epsilon0 / 20480) ^ 2)
          (1 / (16384 * (1 + 3 / t0) *
            Real.exp (24 * epsilon0 / t0)))))
    0 < epsilon0 ∧ epsilon0 ≤ (1 / 64 : ℝ) ∧
      epsilon0 ≤ 1 / (64 * Real.sqrt L2) ∧
      epsilon0 ≤ alpha / (8 * L) ∧
      0 < t0 ∧ t0 < (3 / 8 : ℝ) ∧ t0 ≤ Real.exp (-1) ∧
      (3 * alpha / epsilon0) * t0 * Real.log (1 / t0) ≤ (1 / 4 : ℝ) ∧
      0 < eta0 ∧ eta0 ≤ (1 / 16 : ℝ) ∧
      eta0 ≤ Real.sqrt t0 / (2 * Real.sqrt L2) ∧
      eta0 ≤ (epsilon0 / 20480) ^ 2 ∧
      eta0 ≤ 1 / (16384 * (1 + 3 / t0) *
        Real.exp (24 * epsilon0 / t0)) := by
  dsimp only
  let alpha : ℝ := 1 / 1024
  let epsilon0 : ℝ := min (1 / (64 * Real.sqrt L2)) (alpha / (8 * L))
  let u : ℝ := 48 * alpha / epsilon0
  let t0 : ℝ := Real.exp (-u)
  let eta0 : ℝ := min (1 / 16)
    (min (Real.sqrt t0 / (2 * Real.sqrt L2))
      (min ((epsilon0 / 20480) ^ 2)
        (1 / (16384 * (1 + 3 / t0) * Real.exp (24 * epsilon0 / t0)))))
  have hLp : 0 < L := by linarith
  have hL2p : 0 < L2 := by linarith
  have hs : 0 < Real.sqrt L2 := Real.sqrt_pos.2 hL2p
  have hs1 : 1 ≤ Real.sqrt L2 := by nlinarith [Real.sq_sqrt hL2p.le, Real.sqrt_nonneg L2]
  have he : 0 < epsilon0 := by dsimp [epsilon0, alpha]; positivity
  have he1 : epsilon0 ≤ 1 / (64 * Real.sqrt L2) := min_le_left _ _
  have he2 : epsilon0 ≤ alpha / (8 * L) := min_le_right _ _
  have he64 : epsilon0 ≤ (1 / 64 : ℝ) := he1.trans (by apply one_div_le_one_div_of_le (by norm_num); nlinarith)
  have hup : 0 < u := by dsimp [u, alpha]; positivity
  have hu2 : 2 ≤ u := by
    have hm := (le_div_iff₀ (show 0 < 8 * L by positivity)).mp he2
    apply (le_div_iff₀ he).2
    dsimp [alpha] at *
    nlinarith only [hm, hL, he64]
  have ht : 0 < t0 := Real.exp_pos _
  have htExp : t0 ≤ Real.exp (-1) := by dsimp [t0]; exact Real.exp_le_exp.mpr (by linarith)
  have htThree : t0 < (3 / 8 : ℝ) := by
    have he2v : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    have hv : Real.exp (-2 : ℝ) ≤ (1 / 3 : ℝ) := by
      rw [Real.exp_neg]
      simpa only [one_div] using (one_div_le_one_div_of_le (by norm_num) he2v)
    have ht2 : t0 ≤ Real.exp (-2) := by dsimp [t0]; exact Real.exp_le_exp.mpr (by linarith)
    linarith
  have hlog : Real.log (1 / t0) = u := by
    dsimp [t0]; rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hclock : (3 * alpha / epsilon0) * t0 * Real.log (1 / t0) ≤ (1 / 4 : ℝ) := by
    rw [hlog]
    have hb := sgp_exp_square_bound u hup.le
    have hval : 3 * alpha / epsilon0 = u / 16 := by dsimp [u]; ring
    rw [hval]
    dsimp [t0]
    nlinarith only [hb]
  have heta : 0 < eta0 := by dsimp [eta0]; positivity
  have he16 : eta0 ≤ (1 / 16 : ℝ) := min_le_left _ _
  have her := (min_le_right (1 / 16 : ℝ) _ : eta0 ≤ _)
  have hc := her.trans (min_le_left _ _)
  have hr := her.trans (min_le_right _ _)
  have hshort := hr.trans (min_le_left _ _)
  have hmacro := hr.trans (min_le_right _ _)
  exact ⟨he, he64, he1, he2, ht, htThree, htExp, hclock, heta, he16, hc, hshort, hmacro⟩

theorem sourceTruncation_growingTilt_parameter_payment
    (nu0 : Measure ℝ) [IsProbabilityMeasure nu0] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu0) = 1)
    (hmean : (∫ z : ℝ, z ∂nu0) = 0)
    (L L2 epsilon0 t0 eta0 : ℝ)
    (hL : 1600 ≤ L) (hL2 : 20 ≤ L2)
    (hepsilon0 : 0 < epsilon0)
    (hepsilon0Clock : epsilon0 ≤ 1 / (64 * Real.sqrt L2))
    (hepsilon0Tilt : epsilon0 ≤ (1 / 1024 : ℝ) / (8 * L))
    (ht0 : 0 < t0) (ht0ThreeEighths : t0 < (3 / 8 : ℝ))
    (ht0Exp : t0 ≤ Real.exp (-1))
    (ht0Log : (3 * (1 / 1024 : ℝ) / epsilon0) * t0 *
      Real.log (1 / t0) ≤ (1 / 4 : ℝ))
    (heta0 : 0 < eta0) (heta0Sixteenth : eta0 ≤ (1 / 16 : ℝ))
    (heta0Clock : eta0 ≤ Real.sqrt t0 / (2 * Real.sqrt L2))
    (heta0Short : eta0 ≤ (epsilon0 / 20480) ^ 2)
    (heta0Macro : eta0 ≤ 1 / (16384 * (1 + 3 / t0) *
      Real.exp (24 * epsilon0 / t0)))
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilonDef : epsilon = min (epsilon0 / 2)
      (1 / (4 * (8 * (1 + L) + 1) * L)))
    (hRcube : Shao.truncationBudget nu0 n x ≤ epsilon ^ 3 / 8)
    (hReta : Shao.truncationBudget nu0 n x ≤ epsilon ^ 2 * eta0 / 40)
    (y : ℝ) (hy : 2 ≤ y)
    (hwindow : |y - x| ≤ 1 / (2 * (1 + x))) :
    let nu : Measure ℝ := ProbabilityTheory.cond nu0
      {z : ℝ | |z| ≤ epsilon / (1 + x)}
    let hxcut : ℝ := epsilon / (1 + x)
    let h : ℝ := epsilon0 / (1 + y)
    let alpha : ℝ := 1 / 1024
    let mu : ℝ := ∫ a : ℝ, a ∂nu
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
    let V : ℝ := variance (id : ℝ → ℝ) nu
    let gamma : ℝ := m3 / V
    let Lambda : ℝ := (1 + y) * (n : ℝ) * |mu| +
      (1 + y) ^ 3 * (n : ℝ) * m3
    0 < epsilon ∧ epsilon ≤ epsilon0 / 2 ∧
      IsProbabilityMeasure nu ∧
      Integrable (fun a : ℝ => a) nu ∧
      Integrable (fun a : ℝ => a ^ 2) nu ∧
      Integrable (fun a : ℝ => |a| ^ 3) nu ∧
      0 < hxcut ∧ 0 < h ∧ hxcut ≤ h ∧
      (∀ᵐ a : ℝ ∂nu, |a| ≤ hxcut) ∧
      (∀ᵐ a : ℝ ∂nu, |a| ≤ h) ∧
      y ≤ 1 + x ∧ 1 + y ≤ 2 * (1 + x) ∧
      (4 * h) * y ≤ (1 / 16 : ℝ) ∧
      (3 / 4 : ℝ) ≤ (n : ℝ) * m2 ∧
      (n : ℝ) * m2 ≤ (4 / 3 : ℝ) ∧
      (1 / 2 : ℝ) ≤ (n : ℝ) * V ∧
      (n : ℝ) * |mu| ≤ (1 / 2 : ℝ) ∧
      0 < V ∧ 0 < m3 ∧ 0 < gamma ∧
      m2 ≤ 2 * V ∧ m2 ≤ gamma ^ 2 ∧
      gamma ≤ 2 * hxcut ∧ gamma ≤ 2 * (n : ℝ) * m3 ∧
      0 ≤ Lambda ∧ Lambda ≤ eta0 / 2 ∧
      gamma * (1 + y) ^ 3 ≤ eta0 ∧
      L2 * gamma ^ 2 ≤ t0 ∧
      (∀ u v : ℝ, u ≠ 0 → |v| ≤ |u| / (4 * h) →
        |v| ≤ |u| / (4 * hxcut)) ∧
      (∀ (i : ℕ) (q : ℝ), i ≤ n → 0 ≤ q →
        let m : ℕ := n - i
        let T : ℝ := (m : ℝ) * m2
        let N : ℝ := q + T
        (i ≤ n / 2 ∨ (n / 2 < i ∧ t0 ≤ T ∧ (1 / 16 : ℝ) ≤ q)) →
        5 < q ∨
          (let lam : ℝ := y * Real.sqrt N / T
           let s : ℝ := lam * y / Real.sqrt N
           let Gamma : ℝ := 8 * Real.exp (8 * lam * h) * gamma
           t0 ≤ T ∧ L2 * gamma ^ 2 ≤ T ∧
             (1 / 16 : ℝ) ≤ N ∧ N ≤ 7 ∧
             y / Real.sqrt N ≤ lam ∧ 0 ≤ lam ∧
             0 ≤ s ∧ s ≤ lam ^ 2 ∧ s * h ≤ lam ∧
             s = y ^ 2 / T ∧ 0 < Gamma ∧
             lam ≤ 3 * y / t0 ∧ lam * h ≤ 3 * epsilon0 / t0 ∧
             (y + lam) * Gamma ≤ (1 / 2048 : ℝ) ∧
             (y + lam) * Gamma ≤ (1 / 8 : ℝ) ∧
             (128 * Gamma) * y ≤ (1 / 16 : ℝ) ∧
             -lam * y * Real.sqrt N + T * lam ^ 2 / 2 =
               -(y ^ 2 * N / (2 * T)))) ∧
      (∀ (i : ℕ) (q : ℝ), i ≤ n → n / 2 < i → (1 / 16 : ℝ) ≤ q →
        let m : ℕ := n - i
        let T : ℝ := (m : ℝ) * m2
        let N : ℝ := q + T
        L2 * gamma ^ 2 ≤ T → T < t0 →
        5 < q ∨
          (let ell : ℝ := Real.log (1 / T)
           let lam : ℝ := (alpha / h) * ell
           let s : ℝ := lam * y / Real.sqrt N
           let Gamma : ℝ := 8 * Real.exp (8 * lam * h) * gamma
           let E : ℝ := Real.exp
             (-lam * y * Real.sqrt N + T * lam ^ 2 / 2 +
               (m : ℝ) * lam * |mu| +
               512 * (m : ℝ) * lam ^ 3 * m3 * Real.exp (512 * lam * h) +
               512 * lam * h)
           0 < T ∧ 1 ≤ ell ∧
             (1 / 16 : ℝ) ≤ N ∧ N ≤ 7 ∧
             4 * y ≤ lam ∧ y / Real.sqrt N ≤ lam ∧
             0 ≤ s ∧ s ≤ lam ^ 2 ∧ s * h ≤ lam ∧
             lam * h = alpha * ell ∧ 0 < Gamma ∧
             (y + lam) * Gamma ≤ (10 / epsilon0) * Real.sqrt eta0 ∧
             (y + lam) * Gamma ≤ (1 / 2048 : ℝ) ∧
             (y + lam) * Gamma ≤ (1 / 8 : ℝ) ∧
             (128 * Gamma) * y ≤ (1 / 16 : ℝ) ∧
             T * lam ^ 2 / 2 ≤ (lam * y * Real.sqrt N) / 4 ∧
             (m : ℝ) * lam * |mu| ≤ (lam * y * Real.sqrt N) / 8 ∧
             512 * (m : ℝ) * lam ^ 3 * m3 * Real.exp (512 * lam * h) ≤
               (lam * y * Real.sqrt N) / 8 ∧
             L * y * (1 + y) * ell ≤ (lam * y * Real.sqrt N) / 2 ∧
             E ≤ Real.exp (512 * lam * h) *
               Real.exp (-L * y * (1 + y) * ell))) := by
  dsimp only
  let nu : Measure ℝ := ProbabilityTheory.cond nu0 {z : ℝ | |z| ≤ epsilon / (1 + x)}
  let hxcut : ℝ := epsilon / (1 + x)
  let h : ℝ := epsilon0 / (1 + y)
  let alpha : ℝ := 1 / 1024
  let mu : ℝ := ∫ a : ℝ, a ∂nu
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
  let V : ℝ := variance (id : ℝ → ℝ) nu
  let gamma : ℝ := m3 / V
  let Lambda : ℝ := (1 + y) * (n : ℝ) * |mu| + (1 + y) ^ 3 * (n : ℝ) * m3
  let a : ℝ := 1 + y
  let b : ℝ := 1 + x
  have ha : 3 ≤ a := by dsimp [a]; linarith
  have hap : 0 < a := by linarith
  have hb : 1 ≤ b := by dsimp [b]; linarith
  have hbp : 0 < b := by linarith
  have hLp : 0 < L := by linarith
  have hL2p : 0 < L2 := by linarith
  have hsL2 : 1 ≤ Real.sqrt L2 := by nlinarith only [hL2, Real.sq_sqrt hL2p.le, Real.sqrt_nonneg L2]
  have he064 : epsilon0 ≤ (1 / 64 : ℝ) := hepsilon0Clock.trans (by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith)
  have he0One : epsilon0 ≤ 1 := by linarith
  have heps : 0 < epsilon := by rw [hepsilonDef]; positivity
  have hepsSmall : epsilon ≤ epsilon0 / 2 := by rw [hepsilonDef]; exact min_le_left _ _
  have hepsHalf : epsilon ≤ (1 / 2 : ℝ) := by linarith
  have hhalf : 1 / (2 * (1 + x)) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (show 0 < 2 * (1 + x) by positivity)).2
    linarith
  have hupper := (abs_le.mp hwindow).2
  have hyx : y ≤ 1 + x := by linarith
  have hab : a ≤ 2 * b := by dsimp [a, b]; linarith
  have hxc : 0 < hxcut := div_pos heps hbp
  have hh : 0 < h := div_pos hepsilon0 hap
  have hxch : hxcut ≤ h := by
    apply (div_le_div_iff₀ hbp hap).2
    calc
      epsilon * a ≤ (epsilon0 / 2) * a := mul_le_mul_of_nonneg_right hepsSmall hap.le
      _ ≤ (epsilon0 / 2) * (2 * b) := mul_le_mul_of_nonneg_left hab (by positivity)
      _ = epsilon0 * b := by ring
  have hwindowFull : |y - x| ≤ 1 / (1 + x) := hwindow.trans (by
    apply one_div_le_one_div_of_le hbp
    dsimp [b] at *; linarith)
  obtain ⟨_, _, hprob, hsx, h1, h2nu, h3nu, _⟩ :=
    Shao.sourceTruncation_law_data nu0 n h2 hnorm x epsilon hx heps hepsHalf hRcube
  change IsProbabilityMeasure nu at hprob
  letI : IsProbabilityMeasure nu := hprob
  change ∀ᵐ z : ℝ ∂nu, |z| ≤ hxcut at hsx
  change Integrable (fun z : ℝ => z) nu at h1
  change Integrable (fun z : ℝ => z ^ 2) nu at h2nu
  change Integrable (fun z : ℝ => |z| ^ 3) nu at h3nu
  have hsh : ∀ᵐ z : ℝ ∂nu, |z| ≤ h := hsx.mono fun z hz => hz.trans hxch
  obtain ⟨hnm2lo, hnm2hi, hnmu2, hVeq, _, hVp, hnVlo, _⟩ :=
    Shao.sourceTruncation_variance_bounds nu0 n h2 hnorm hmean x epsilon hx heps hepsHalf hRcube
  change (3 / 4 : ℝ) ≤ (n : ℝ) * m2 at hnm2lo
  change (n : ℝ) * m2 ≤ (4 / 3 : ℝ) at hnm2hi
  change (n : ℝ) * mu ^ 2 ≤ (1 / 4 : ℝ) at hnmu2
  change V = m2 - mu ^ 2 at hVeq
  change 0 < V at hVp
  change (1 / 2 : ℝ) ≤ (n : ℝ) * V at hnVlo
  obtain ⟨hm3p, hgp, _, hm2g, hgcut, _, hgnm3, _, _⟩ :=
    Shao.sourceTruncation_gamma_bounds nu0 n h2 hnorm hmean x epsilon hx heps hepsHalf hRcube
  change 0 < m3 at hm3p
  change 0 < gamma at hgp
  change m2 ≤ gamma ^ 2 at hm2g
  change gamma ≤ 2 * hxcut at hgcut
  change gamma ≤ 2 * (n : ℝ) * m3 at hgnm3
  have hnNat : 0 < n := by
    by_contra hnot
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hnot
    simp only [hn0, Nat.cast_zero, zero_mul] at hnorm
    norm_num at hnorm
  have hn : 0 < (n : ℝ) := by exact_mod_cast hnNat
  have hm20 : 0 ≤ m2 := integral_nonneg fun z => sq_nonneg z
  have hm2V : m2 ≤ 2 * V := by
    have hmu2 : mu ^ 2 ≤ m2 / 3 := by
      apply (mul_le_mul_iff_right₀ hn).mp
      nlinarith only [hnmu2, hnm2lo]
    rw [hVeq]
    nlinarith only [hmu2, hm20]
  obtain ⟨_, _, hLambdaOld, _⟩ :=
    Shao.sourceTruncation_nearby_payment nu0 n h2 hnorm hmean x epsilon hx heps hepsHalf
      hRcube y (by linarith) hwindowFull
  change Lambda ≤ 20 * Shao.truncationBudget nu0 n x / epsilon ^ 2 at hLambdaOld
  have hLambda : Lambda ≤ eta0 / 2 := by
    calc
      Lambda ≤ 20 * Shao.truncationBudget nu0 n x / epsilon ^ 2 := hLambdaOld
      _ ≤ 20 * (epsilon ^ 2 * eta0 / 40) / epsilon ^ 2 := by gcongr
      _ = eta0 / 2 := by field_simp <;> ring
  have hLambda0 : 0 ≤ Lambda := by dsimp [Lambda]; positivity
  have hmuBudget : (n : ℝ) * |mu| ≤ Lambda := by
    have hm := mul_nonneg (show 0 ≤ a - 1 by linarith)
      (mul_nonneg (Nat.cast_nonneg n) (abs_nonneg mu))
    dsimp [Lambda, a] at *
    nlinarith only [hm, mul_nonneg (pow_nonneg (show 0 ≤ 1 + y by linarith) 3)
      (mul_nonneg (Nat.cast_nonneg n) hm3p.le)]
  have hmuSmall : (n : ℝ) * |mu| ≤ (1 / 2 : ℝ) := by linarith
  have hm3Budget : a ^ 3 * (n : ℝ) * m3 ≤ Lambda := by
    dsimp [Lambda, a]
    nlinarith only [mul_nonneg (show 0 ≤ 1 + y by linarith)
      (mul_nonneg (Nat.cast_nonneg n) (abs_nonneg mu))]
  have hgBudget : gamma * a ^ 3 ≤ eta0 := by
    have hm := mul_le_mul_of_nonneg_right hgnm3 (pow_nonneg hap.le 3)
    nlinarith only [hm, hm3Budget, hLambda]
  have hgEta : gamma ≤ eta0 := by
    have hp : 1 ≤ a ^ 3 := one_le_pow₀ (by linarith)
    have hm := mul_le_mul_of_nonneg_left hp hgp.le
    nlinarith only [hm, hgBudget]
  have hgClock : L2 * gamma ^ 2 ≤ t0 := by
    have hsmp := (le_div_iff₀ (show 0 < 2 * Real.sqrt L2 by positivity)).mp heta0Clock
    have hsqs := pow_le_pow_left₀ (by positivity : 0 ≤ eta0 * (2 * Real.sqrt L2)) hsmp 2
    rw [mul_pow, mul_pow, Real.sq_sqrt ht0.le, Real.sq_sqrt hL2p.le] at hsqs
    have hgg := pow_le_pow_left₀ hgp.le hgEta 2
    have hggL := mul_le_mul_of_nonneg_left hgg hL2p.le
    nlinarith only [hsqs, hggL, ht0.le]
  have hyh : y * h ≤ (1 / 64 : ℝ) := by
    have hid : a * h = epsilon0 := by dsimp [h, a]; field_simp
    have hm := mul_nonneg hh.le (show 0 ≤ a - y by dsimp [a]; linarith)
    nlinarith only [hid, hm, he064]
  have hfour : (4 * h) * y ≤ (1 / 16 : ℝ) := by nlinarith only [hyh]
  refine ⟨heps, hepsSmall, hprob, h1, h2nu, h3nu, hxc, hh, hxch, hsx, hsh,
    hyx, hab, hfour, hnm2lo, hnm2hi, hnVlo, hmuSmall, hVp, hm3p, hgp,
    hm2V, hm2g, hgcut, hgnm3, hLambda0, hLambda, hgBudget, hgClock, ?_, ?_, ?_⟩
  · intro u v _ hv
    apply hv.trans
    apply (div_le_div_iff₀ (show 0 < 4 * h by positivity) (show 0 < 4 * hxcut by positivity)).2
    exact mul_le_mul_of_nonneg_left (by linarith only [hxch]) (abs_nonneg u)
  · intro i q hi hq
    intro hrange
    by_cases hqbig : 5 < q
    · exact Or.inl hqbig
    apply Or.inr
    let m : ℕ := n - i
    let T : ℝ := (m : ℝ) * m2
    let N : ℝ := q + T
    let lam : ℝ := y * Real.sqrt N / T
    let s : ℝ := lam * y / Real.sqrt N
    let Gamma : ℝ := 8 * Real.exp (8 * lam * h) * gamma
    have hq5 : q ≤ 5 := le_of_not_gt hqbig
    have hT0 : 0 ≤ T := by dsimp [T]; positivity
    have hTmax : T ≤ (4 / 3 : ℝ) := by
      have hmle : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n i
      exact (mul_le_mul_of_nonneg_right hmle hm20).trans hnm2hi
    have hTl : t0 ≤ T := by
      rcases hrange with hearly | hlate
      · have hhalfN : (n : ℝ) / 2 ≤ (m : ℝ) := by
          have hi2 : 2 * i ≤ n := by omega
          have hcast : (2 : ℝ) * (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi2
          dsimp [m]; rw [Nat.cast_sub hi]; linarith
        have hm := mul_le_mul_of_nonneg_right hhalfN hm20
        change _ ≤ T at hm
        nlinarith only [hm, hnm2lo, ht0ThreeEighths]
      · exact hlate.2.1
    have hNl : (1 / 16 : ℝ) ≤ N := by
      rcases hrange with hearly | hlate
      · have hhalfN : (n : ℝ) / 2 ≤ (m : ℝ) := by
          have hi2 : 2 * i ≤ n := by omega
          have hcast : (2 : ℝ) * (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi2
          dsimp [m]; rw [Nat.cast_sub hi]; linarith
        have hm := mul_le_mul_of_nonneg_right hhalfN hm20
        dsimp [N, T] at *
        nlinarith only [hm, hnm2lo, hq]
      · dsimp [N]; linarith only [hlate.2.2, hT0]
    have hNu : N ≤ 7 := by dsimp [N]; linarith only [hq5, hTmax]
    have hTN : T ≤ N := by dsimp [N]; linarith only [hq]
    obtain ⟨hlam, hl0, hG, hlu, hlh, _, hpay⟩ :=
      sgp_macroscopic_clock_bound epsilon0 t0 eta0 y gamma T N hepsilon0 ht0 heta0.le
        (by linarith) hgp hgBudget hTl hTN hNl hNu
    change y / Real.sqrt N ≤ lam at hlam
    change 0 ≤ lam at hl0
    change 0 < Gamma at hG
    change lam ≤ 3 * y / t0 at hlu
    change lam * h ≤ 3 * epsilon0 / t0 at hlh
    change (y + lam) * Gamma ≤ 8 * (1 + 3 / t0) * Real.exp (24 * epsilon0 / t0) * eta0 at hpay
    obtain ⟨_, hs0, hsquare, hslope⟩ := sgp_schedule_guards y h N lam hy hh hNl hyh hlam
    change 0 ≤ s at hs0
    change s ≤ lam ^ 2 at hsquare
    change s * h ≤ lam at hslope
    have hpay2048 : (y + lam) * Gamma ≤ (1 / 2048 : ℝ) := by
      apply hpay.trans
      calc
        _ ≤ 8 * (1 + 3 / t0) * Real.exp (24 * epsilon0 / t0) *
            (1 / (16384 * (1 + 3 / t0) * Real.exp (24 * epsilon0 / t0))) := by gcongr
        _ = _ := by field_simp <;> ring
    have hout : (128 * Gamma) * y ≤ (1 / 16 : ℝ) := by
      have hm := mul_nonneg hl0 hG.le
      nlinarith only [hpay2048, hm]
    have hTp : 0 < T := ht0.trans_le hTl
    have hNp : 0 < N := by linarith only [hNl]
    have hsp : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
    have hsval : s = y ^ 2 / T := by dsimp [s, lam]; field_simp <;> ring
    have hex : -lam * y * Real.sqrt N + T * lam ^ 2 / 2 = -(y ^ 2 * N / (2 * T)) := by
      dsimp [lam]
      field_simp
      ring_nf
      rw [Real.sq_sqrt hNp.le]
    exact ⟨hTl, hgClock.trans hTl, hNl, hNu, hlam, hl0, hs0, hsquare, hslope,
      hsval, hG, hlu, hlh, hpay2048, hpay2048.trans (by norm_num), hout, hex⟩
  · intro i q hi _ hq
    intro hclock hTsmall
    by_cases hqbig : 5 < q
    · exact Or.inl hqbig
    apply Or.inr
    let m : ℕ := n - i
    let T : ℝ := (m : ℝ) * m2
    let N : ℝ := q + T
    let ell : ℝ := Real.log (1 / T)
    let lam : ℝ := (alpha / h) * ell
    let s : ℝ := lam * y / Real.sqrt N
    let Gamma : ℝ := 8 * Real.exp (8 * lam * h) * gamma
    let E : ℝ := Real.exp (-lam * y * Real.sqrt N + T * lam ^ 2 / 2 +
      (m : ℝ) * lam * |mu| + 512 * (m : ℝ) * lam ^ 3 * m3 * Real.exp (512 * lam * h) + 512 * lam * h)
    change L2 * gamma ^ 2 ≤ T at hclock
    change T < t0 at hTsmall
    have hgammaClock : gamma ^ 2 ≤ T := by
      have hm := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ L2 by linarith) (sq_nonneg gamma)
      nlinarith only [hm, hclock]
    have hT1 : T < 1 := hTsmall.trans (ht0ThreeEighths.trans (by norm_num))
    obtain ⟨hTp, _, _, _, hlh, hl0, hG, hpay⟩ :=
      sgp_short_log_clock_bound epsilon0 alpha eta0 y gamma T hepsilon0 he0One
        (by dsimp [alpha]; norm_num) (by dsimp [alpha]; norm_num) heta0
        (by linarith) (by linarith) hgp hgBudget hgammaClock hT1
    change lam * h = alpha * ell at hlh
    change 0 ≤ lam at hl0
    change 0 < Gamma at hG
    change (y + lam) * Gamma ≤ (10 / epsilon0) * Real.sqrt eta0 at hpay
    have hell : 1 ≤ ell := by
      have hb := Real.log_le_log hTp (hTsmall.le.trans ht0Exp)
      rw [Real.log_exp] at hb
      dsimp [ell]; simp only [one_div, Real.log_inv]; linarith
    have hNl : (1 / 16 : ℝ) ≤ N := by dsimp [N]; linarith only [hq, hTp.le]
    have hNu : N ≤ 7 := by
      have hq5 := le_of_not_gt hqbig
      dsimp [N]
      linarith only [hq5, hTsmall, ht0ThreeEighths]
    have hNp : 0 < N := by linarith only [hNl]
    have hsp : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
    have hs4 : (1 / 4 : ℝ) ≤ Real.sqrt N := by nlinarith only [hNl, Real.sq_sqrt hNp.le, Real.sqrt_nonneg N]
    have hlval : lam = (alpha / epsilon0) * a * ell := by
      dsimp [lam, h, a]; field_simp <;> ring
    have hac : 4 ≤ alpha / epsilon0 := by
      have hb := (le_div_iff₀ (show 0 < 8 * L by positivity)).mp hepsilon0Tilt
      apply (le_div_iff₀ hepsilon0).2
      change epsilon0 * (8 * L) ≤ alpha at hb
      calc
        4 * epsilon0 ≤ (8 * L) * epsilon0 :=
          mul_le_mul_of_nonneg_right (by linarith only [hL]) hepsilon0.le
        _ ≤ alpha := by nlinarith only [hb]
    have hlam4 : 4 * y ≤ lam := by
      rw [hlval]
      have hm := mul_le_mul_of_nonneg_right hac hap.le
      have hn := mul_le_mul_of_nonneg_left hell (show 0 ≤ (alpha / epsilon0) * a by positivity)
      dsimp [a] at *
      nlinarith only [hm, hn]
    have hlam : y / Real.sqrt N ≤ lam := by
      have hb : y / Real.sqrt N ≤ 4 * y := by
        apply (div_le_iff₀ hsp).2
        nlinarith only [mul_le_mul_of_nonneg_left hs4 (show 0 ≤ 4 * y by linarith)]
      exact hb.trans hlam4
    obtain ⟨_, hs0, hsquare, hslope⟩ := sgp_schedule_guards y h N lam hy hh hNl hyh hlam
    change 0 ≤ s at hs0
    change s ≤ lam ^ 2 at hsquare
    change s * h ≤ lam at hslope
    have hsqrtEta : Real.sqrt eta0 ≤ epsilon0 / 20480 := by
      nlinarith only [heta0Short, Real.sq_sqrt heta0.le, Real.sqrt_nonneg eta0, hepsilon0.le]
    have hpay2048 : (y + lam) * Gamma ≤ (1 / 2048 : ℝ) := by
      calc
        _ ≤ (10 / epsilon0) * Real.sqrt eta0 := hpay
        _ ≤ (10 / epsilon0) * (epsilon0 / 20480) := by gcongr
        _ = _ := by field_simp <;> ring
    have hout : (128 * Gamma) * y ≤ (1 / 16 : ℝ) := by
      nlinarith only [hpay2048, mul_nonneg hl0 hG.le]
    have hTle : T ≤ 1 := hT1.le
    have hmN : (m : ℝ) ≤ (4 / 3 : ℝ) * T * (n : ℝ) := by
      have hb := mul_le_mul_of_nonneg_left hnm2lo (Nat.cast_nonneg m)
      dsimp [T] at *
      nlinarith only [hb]
    have htime := sgp_log_clock_mono T t0 hTp ht0 hTsmall.le ht0Exp
    have hsmalltime : (3 * alpha / epsilon0) * T * ell ≤ (1 / 4 : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left htime (show 0 ≤ 3 * alpha / epsilon0 by positivity)
      change (3 * alpha / epsilon0) * t0 * Real.log (1 / t0) ≤ (1 / 4 : ℝ) at ht0Log
      change T * ell ≤ _ at htime
      nlinarith only [hm, ht0Log]
    have hTlam : T * lam ≤ a / 12 := by
      have hm := mul_le_mul_of_nonneg_left hsmalltime (show 0 ≤ a / 3 by positivity)
      rw [hlval]
      ring_nf at hm ⊢
      linarith only [hm]
    have hays : a ≤ 6 * y * Real.sqrt N := by
      have hm := mul_le_mul_of_nonneg_left hs4 (show 0 ≤ 6 * y by linarith)
      dsimp [a] at *
      nlinarith only [hm, hy]
    have hquad : T * lam ^ 2 / 2 ≤ (lam * y * Real.sqrt N) / 4 := by
      have hb : T * lam ≤ y * Real.sqrt N / 2 := by nlinarith only [hTlam, hays]
      have hm := mul_le_mul_of_nonneg_right hb (show 0 ≤ lam / 2 by positivity)
      nlinarith only [hm]
    have hmeanBase : (m : ℝ) * |mu| ≤ (4 / 3 : ℝ) * Lambda := by
      calc
        _ ≤ ((4 / 3 : ℝ) * T * (n : ℝ)) * |mu| := mul_le_mul_of_nonneg_right hmN (abs_nonneg mu)
        _ = (4 / 3 : ℝ) * T * ((n : ℝ) * |mu|) := by ring
        _ ≤ (4 / 3 : ℝ) * 1 * Lambda := by gcongr
        _ = _ := by ring
    have hmean : (m : ℝ) * lam * |mu| ≤ (lam * y * Real.sqrt N) / 8 := by
      have hys : (1 / 2 : ℝ) ≤ y * Real.sqrt N := by
        have hm := mul_le_mul_of_nonneg_left hs4 (show 0 ≤ y by linarith)
        nlinarith only [hm, hy]
      have hb : (m : ℝ) * |mu| ≤ y * Real.sqrt N / 8 := by
        nlinarith only [hmeanBase, hLambda, heta0Sixteenth, hys]
      have hm := mul_le_mul_of_nonneg_left hb hl0
      nlinarith only [hm]
    have hTexpId : T = Real.exp (-ell) := by
      dsimp [ell]; simp only [one_div, Real.log_inv, neg_neg]
      exact (Real.exp_log hTp).symm
    have he512 : 512 * lam * h = ell / 2 := by dsimp [alpha] at hlh; nlinarith only [hlh]
    have hclock16 : T * ell ^ 2 * Real.exp (512 * lam * h) ≤ 16 := by
      rw [he512, hTexpId]
      have hb := sgp_exp_square_bound (ell / 2) (by linarith)
      have hid : Real.exp (-ell) * ell ^ 2 * Real.exp (ell / 2) =
          ell ^ 2 * Real.exp (-(ell / 2)) := by
        rw [mul_comm (Real.exp (-ell)) (ell ^ 2), mul_assoc, ← Real.exp_add]
        congr 2; ring
      rw [hid]
      nlinarith only [hb]
    have hm3a2 : a ^ 2 * (n : ℝ) * m3 ≤ Lambda := by
      have hp : a ^ 2 ≤ a ^ 3 := by nlinarith only [mul_nonneg (sq_nonneg a) (show 0 ≤ a - 1 by linarith)]
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg n)) hm3p.le).trans hm3Budget
    have hbase3 : (m : ℝ) * m3 * a ^ 2 ≤ (4 / 3 : ℝ) * T * Lambda := by
      have hb := mul_le_mul_of_nonneg_right hmN (show 0 ≤ m3 * a ^ 2 by positivity)
      have hc := mul_le_mul_of_nonneg_left hm3a2 (show 0 ≤ (4 / 3 : ℝ) * T by positivity)
      nlinarith only [hb, hc]
    have hcubicBase : 512 * (m : ℝ) * lam ^ 2 * m3 * Real.exp (512 * lam * h) ≤
        Lambda / (96 * epsilon0 ^ 2) := by
      calc
        _ = (512 * (alpha / epsilon0) ^ 2 * ell ^ 2 * Real.exp (512 * lam * h)) *
            ((m : ℝ) * m3 * a ^ 2) := by rw [hlval]; ring
        _ ≤ (512 * (alpha / epsilon0) ^ 2 * ell ^ 2 * Real.exp (512 * lam * h)) *
            ((4 / 3 : ℝ) * T * Lambda) := by gcongr
        _ = ((2048 / 3 : ℝ) * (alpha / epsilon0) ^ 2 * Lambda) *
            (T * ell ^ 2 * Real.exp (512 * lam * h)) := by ring
        _ ≤ ((2048 / 3 : ℝ) * (alpha / epsilon0) ^ 2 * Lambda) * 16 := by gcongr
        _ = Lambda / (96 * epsilon0 ^ 2) := by dsimp [alpha]; field_simp <;> ring
    have hetaEps : eta0 ≤ epsilon0 ^ 2 := by
      have hb : (epsilon0 / 20480) ^ 2 ≤ epsilon0 ^ 2 := by nlinarith only [sq_nonneg epsilon0]
      exact heta0Short.trans hb
    have hcubic : 512 * (m : ℝ) * lam ^ 3 * m3 * Real.exp (512 * lam * h) ≤
        (lam * y * Real.sqrt N) / 8 := by
      have hrat : Lambda / (96 * epsilon0 ^ 2) ≤ (1 / 192 : ℝ) := by
        apply (div_le_iff₀ (show 0 < 96 * epsilon0 ^ 2 by positivity)).2
        nlinarith only [hLambda, hetaEps]
      have hys : (1 / 2 : ℝ) ≤ y * Real.sqrt N := by
        nlinarith only [mul_le_mul_of_nonneg_left hs4 (show 0 ≤ y by linarith), hy]
      have hb : 512 * (m : ℝ) * lam ^ 2 * m3 * Real.exp (512 * lam * h) ≤ y * Real.sqrt N / 8 := by
        linarith only [hcubicBase, hrat, hys]
      have hm := mul_le_mul_of_nonneg_right hb hl0
      nlinarith only [hm]
    have hLalpha : L ≤ alpha / (8 * epsilon0) := by
      have hb := (le_div_iff₀ (show 0 < 8 * L by positivity)).mp hepsilon0Tilt
      apply (le_div_iff₀ (show 0 < 8 * epsilon0 by positivity)).2
      change epsilon0 * (8 * L) ≤ alpha at hb
      nlinarith only [hb]
    have hdecay : L * y * a * ell ≤ (lam * y * Real.sqrt N) / 2 := by
      have hm := mul_le_mul_of_nonneg_right hLalpha (show 0 ≤ y * a * ell by positivity)
      have hc := mul_le_mul_of_nonneg_left hs4 (show 0 ≤ lam * y / 2 by positivity)
      rw [hlval] at hc
      rw [hlval]
      ring_nf at hm hc ⊢
      linarith only [hm, hc]
    have hE : E ≤ Real.exp (512 * lam * h) * Real.exp (-L * y * a * ell) := by
      rw [← Real.exp_add]
      dsimp [E]
      apply Real.exp_le_exp.mpr
      nlinarith only [hquad, hmean, hcubic, hdecay]
    exact ⟨hTp, hell, hNl, hNu, hlam4, hlam, hs0, hsquare, hslope, hlh,
      hG, hpay, hpay2048, hpay2048.trans (by norm_num), hout, hquad, hmean,
      hcubic, hdecay, hE⟩

theorem sourceGrowingTilt_log_polynomial_payment
    (L y T : ℝ) (hL : 1600 ≤ L) (hy : 2 ≤ y)
    (hT : 0 < T) (hTexp : T ≤ Real.exp (-1)) :
    let ell : ℝ := Real.log (1 / T)
    (1 + y) ^ 128 * Real.exp (512 * ell) *
        Real.exp (-L * y * (1 + y) * ell) ≤
      Real.exp (-y ^ 2 / 2) / (1 + y) * T ^ 2 ∧
      (1 + y) ^ 128 * Real.exp (512 * ell) *
          Real.exp (-L * y * (1 + y) * ell) ≤
        Real.sqrt (2 * Real.pi) * Shao.standardNormalTail y * T ^ 2 := by
  dsimp only
  let a : ℝ := 1 + y
  let ell : ℝ := Real.log (1 / T)
  have ha : 3 ≤ a := by dsimp [a]; linarith
  have hap : 0 < a := by linarith
  have hlogT := Real.log_le_log hT hTexp
  rw [Real.log_exp] at hlogT
  have hell : 1 ≤ ell := by dsimp [ell]; simp only [one_div, Real.log_inv]; linarith
  have hla : Real.log a ≤ y := by
    have ht := Real.log_le_sub_one_of_pos hap
    dsimp [a] at *; linarith
  have hya : 6 ≤ y * a := by nlinarith
  have hcoef : L * y * a - 514 ≥ (L / 2) * y * a := by nlinarith
  have hneed : 129 * Real.log a + y ^ 2 / 2 ≤ (L / 2) * y * a := by
    have h1 : 129 * y ≤ 43 * y * a := by nlinarith
    have h2 : y ^ 2 / 2 ≤ y * a / 2 := by dsimp [a]; nlinarith
    have h3 : (87 / 2 : ℝ) * y * a ≤ (L / 2) * y * a := by nlinarith
    nlinarith only [h1, h2, h3, hla]
  have hmore := mul_le_mul_of_nonneg_left hell (show 0 ≤ L * y * a - 514 by nlinarith)
  have hexponent : 128 * Real.log a + 512 * ell - L * y * a * ell ≤
      -y ^ 2 / 2 - Real.log a - 2 * ell := by nlinarith only [hneed, hcoef, hmore]
  have haexp : Real.exp (128 * Real.log a) = a ^ 128 := by
    change Real.exp ((↑(128 : ℕ) : ℝ) * Real.log a) = _
    rw [Real.exp_nat_mul, Real.exp_log hap]
  have hTexpid : Real.exp (-ell) = T := by
    dsimp [ell]; simp only [one_div, Real.log_inv, neg_neg]; exact Real.exp_log hT
  have hTtwo : Real.exp ((2 : ℝ) * (-ell)) = T ^ 2 := by
    change Real.exp ((↑(2 : ℕ) : ℝ) * (-ell)) = _
    rw [Real.exp_nat_mul, hTexpid]
  have hpay : a ^ 128 * Real.exp (512 * ell) * Real.exp (-L * y * a * ell) ≤
      Real.exp (-y ^ 2 / 2) / a * T ^ 2 := by
    have he := Real.exp_le_exp.mpr hexponent
    have hl : Real.exp (128 * Real.log a + 512 * ell - L * y * a * ell) =
        a ^ 128 * Real.exp (512 * ell) * Real.exp (-L * y * a * ell) := by
      rw [show 128 * Real.log a + 512 * ell - L * y * a * ell =
        (128 * Real.log a + 512 * ell) + (-L * y * a * ell) by ring,
        Real.exp_add, Real.exp_add, haexp]
    have hr : Real.exp (-y ^ 2 / 2 - Real.log a - 2 * ell) =
        Real.exp (-y ^ 2 / 2) / a * T ^ 2 := by
      rw [show -y ^ 2 / 2 - Real.log a - 2 * ell =
        (-y ^ 2 / 2 + -Real.log a) + (2 : ℝ) * (-ell) by ring,
        Real.exp_add, Real.exp_add, hTtwo, Real.exp_neg,
        Real.exp_log hap]
      ring
    rwa [hl, hr] at he
  have hd : Shao.standardNormalDensity y =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) := by
    unfold Shao.standardNormalDensity
    rw [ProbabilityTheory.gaussianPDFReal_def]
    norm_num
  have hpi : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have htail := (Shao.standardNormal_mills_bounds y (by linarith)).1
  have htail2 : Real.exp (-y ^ 2 / 2) / a ≤ Real.sqrt (2 * Real.pi) * Shao.standardNormalTail y := by
    rw [hd] at htail
    have hm := mul_le_mul_of_nonneg_left htail hpi.le
    dsimp [a] at *
    field_simp at hm ⊢
    nlinarith only [hm]
  exact ⟨hpay, hpay.trans (mul_le_mul_of_nonneg_right htail2 (sq_nonneg T))⟩

end Shao.Probability
