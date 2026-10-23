import Shao.Probability.CenteredQuadraticCharacteristicPower
import Shao.Probability.QuadraticFullNoiseConeDerivatives
import Shao.Probability.QuadraticFullNoiseDerivatives
import Shao.Probability.SourceFourierScale

/-!
Actual high-frequency product estimates from supplement 2607–2612, 3369–3401.
The six retained chord factors pay the signed centered-power gap weight. The
original conditional mean is then restored as its true complex exponential.
The final adapter pays all numerical guards from the original truncation law
and returns the original clock T = (n-i) * Eρ[A²].
-/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

private lemma second_mul (f g : ℝ → ℂ)
    (hf : ∀ r, HasDerivAt f (deriv f r) r)
    (hg : ∀ r, HasDerivAt g (deriv g r) r) (u : ℝ)
    (hff : DifferentiableAt ℝ (fun r => deriv f r) u)
    (hgg : DifferentiableAt ℝ (fun r => deriv g r) u) :
    HasDerivAt (fun r => deriv (fun s => f s * g s) r)
      (deriv (fun r => deriv f r) u * g u +
        2 * deriv f u * deriv g u + f u * deriv (fun r => deriv g r) u) u := by
  have hd := ((hff.hasDerivAt.mul (hg u)).add ((hf u).mul hgg.hasDerivAt)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => ((hf r).mul (hg r)).deriv)
  convert hd using 1
  ring

-- Retained-factor multiplication uses no division by the retained weight.
private lemma weighted_mul (f g : ℝ → ℂ)
    (hf : ∀ r, HasDerivAt f (deriv f r) r)
    (hg : ∀ r, HasDerivAt g (deriv g r) r) (u R d0 d1 d2 q1 q2 : ℝ)
    (_hR : 0 ≤ R) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2)
    (hff : DifferentiableAt ℝ (fun r => deriv f r) u)
    (hgg : DifferentiableAt ℝ (fun r => deriv g r) u)
    (hf0 : ‖f u‖ * R ≤ d0) (hf1 : ‖deriv f u‖ * R ≤ d1)
    (hf2 : ‖deriv (fun r => deriv f r) u‖ * R ≤ d2)
    (hg0 : ‖g u‖ ≤ R) (hg1 : ‖deriv g u‖ ≤ q1 * R)
    (hg2 : ‖deriv (fun r => deriv g r) u‖ ≤ q2 * R) :
    DifferentiableAt ℝ (fun r => f r * g r) u ∧
      DifferentiableAt ℝ (fun r => deriv (fun s => f s * g s) r) u ∧
      ‖f u * g u‖ ≤ d0 ∧
      ‖deriv (fun r => f r * g r) u‖ ≤ d1 + q1 * d0 ∧
      ‖deriv (fun r => deriv (fun s => f s * g s) r) u‖ ≤
        d2 + 2 * q1 * d1 + q2 * d0 := by
  have hd := second_mul f g hf hg u hff hgg
  refine ⟨((hf u).mul (hg u)).differentiableAt, hd.differentiableAt, ?_, ?_, ?_⟩
  · rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hg0 (norm_nonneg _)).trans hf0
  · have hfirst : deriv (fun r => f r * g r) u = deriv f u * g u + f u * deriv g u :=
      ((hf u).mul (hg u)).deriv
    rw [hfirst]
    calc
      _ ≤ ‖deriv f u‖ * ‖g u‖ + ‖f u‖ * ‖deriv g u‖ := by
        simpa only [norm_mul] using norm_add_le (deriv f u * g u) (f u * deriv g u)
      _ ≤ ‖deriv f u‖ * R + q1 * (‖f u‖ * R) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hg0 (norm_nonneg _)
        · nlinarith only [mul_le_mul_of_nonneg_left hg1 (norm_nonneg (f u))]
      _ ≤ _ := add_le_add hf1 (mul_le_mul_of_nonneg_left hf0 hq1)
  · rw [hd.deriv]
    calc
      _ ≤ ‖deriv (fun r => deriv f r) u‖ * ‖g u‖ +
          2 * ‖deriv f u‖ * ‖deriv g u‖ +
          ‖f u‖ * ‖deriv (fun r => deriv g r) u‖ := by
        calc
          _ ≤ ‖deriv (fun r => deriv f r) u * g u + 2 * deriv f u * deriv g u‖ +
              ‖f u * deriv (fun r => deriv g r) u‖ := norm_add_le _ _
          _ ≤ (‖deriv (fun r => deriv f r) u * g u‖ + ‖2 * deriv f u * deriv g u‖) +
              ‖f u * deriv (fun r => deriv g r) u‖ := add_le_add (norm_add_le _ _) le_rfl
          _ = _ := by simp
      _ ≤ ‖deriv (fun r => deriv f r) u‖ * R +
          2 * q1 * (‖deriv f u‖ * R) + q2 * (‖f u‖ * R) := by
        apply add_le_add
        · apply add_le_add
          · exact mul_le_mul_of_nonneg_left hg0 (norm_nonneg _)
          · nlinarith only [mul_le_mul_of_nonneg_left hg1 (by positivity : 0 ≤ 2 * ‖deriv f u‖)]
        · nlinarith only [mul_le_mul_of_nonneg_left hg2 (norm_nonneg (f u))]
      _ ≤ _ := add_le_add (add_le_add hf2
        (mul_le_mul_of_nonneg_left hf1 (by positivity)))
        (mul_le_mul_of_nonneg_left hf0 hq2)

private noncomputable def linearPhase (b r : ℝ) : ℂ :=
  Complex.exp (((b * r : ℝ) : ℂ) * Complex.I)

private lemma phase_first (b r : ℝ) : HasDerivAt (linearPhase b)
    (((b : ℂ) * Complex.I) * linearPhase b r) r := by
  unfold linearPhase
  convert ((((hasDerivAt_id r).const_mul b).ofReal_comp).mul_const Complex.I).cexp using 1
  all_goals try funext t
  all_goals dsimp
  all_goals push_cast
  all_goals ring

private lemma phase_second (b r : ℝ) : HasDerivAt (fun s => deriv (linearPhase b) s)
    (((b : ℂ) * Complex.I) ^ 2 * linearPhase b r) r := by
  have hd := ((phase_first b r).const_mul ((b : ℂ) * Complex.I)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => (phase_first b s).deriv)
  convert hd using 1
  ring

private lemma phase_bounds (b r : ℝ) : ‖linearPhase b r‖ = 1 ∧
    ‖deriv (linearPhase b) r‖ = |b| ∧
    ‖deriv (fun s => deriv (linearPhase b) s) r‖ = b ^ 2 := by
  have hn (s : ℝ) : ‖linearPhase b s‖ = 1 := by
    simp [linearPhase, Complex.norm_exp, Complex.mul_re]
  refine ⟨hn r, ?_, ?_⟩
  · rw [(phase_first b r).deriv]
    simp [hn]
  · rw [(phase_second b r).deriv]
    simp [norm_pow, hn, sq_abs]

private lemma restore_mean (ν : Measure ℝ) (m : ℕ) (σ r v : ℝ) :
    linearPhase ((m : ℝ) * σ * (∫ a : ℝ, a ∂ν)) r *
        (centeredQuadraticChar ν (σ * r) v) ^ m =
      (quadraticChar ν (σ * r) v) ^ m := by
  let z : ℂ := (((σ * r * ∫ a : ℝ, a ∂ν : ℝ) : ℂ) * Complex.I)
  have he : linearPhase ((m : ℝ) * σ * (∫ a : ℝ, a ∂ν)) r =
      Complex.exp ((m : ℂ) * z) := by
    unfold linearPhase
    congr 1
    dsimp [z]
    push_cast
    ring
  rw [he]
  simp only [centeredQuadraticChar, mul_pow]
  change Complex.exp ((m : ℂ) * z) * (Complex.exp (-z) ^ m * _) = _
  rw [← Complex.exp_nat_mul]
  rw [← mul_assoc, ← Complex.exp_add]
  simp

-- The source-payable mean guard also supplies the global noise moment bridge.
private lemma gamma_payment (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) (hm : 16 ≤ m)
    (hmean : (m : ℝ) * |∫ a : ℝ, a ∂ν| ≤
      4 * Real.sqrt ((m : ℝ) * variance (id : ℝ → ℝ) ν)) :
    Integrable (fun a : ℝ => a ^ 2) ν ∧
      (∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν ≤ 2 * h := by
  have h2 : Integrable (fun a : ℝ => a ^ 2) ν := by
    refine (integrable_const (h ^ 2)).mono' (by fun_prop) ?_
    filter_upwards [hs] with a ha
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a), sq_abs] using
      pow_le_pow_left₀ (abs_nonneg a) ha 2
  let μ : ℝ := ∫ a : ℝ, a ∂ν
  let V : ℝ := variance (id : ℝ → ℝ) ν
  have hmR : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hS : 0 ≤ (m : ℝ) * V := mul_nonneg hmpos.le hV.le
  have hmu : μ ^ 2 ≤ V := by
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (m : ℝ) * |μ|) hmean 2
    rw [mul_pow, sq_abs, mul_pow, Real.sq_sqrt hS] at hsq
    have hcancel : (m : ℝ) * μ ^ 2 ≤ 16 * V := by
      by_contra hc
      have hp := mul_pos hmpos (sub_pos.mpr (lt_of_not_ge hc))
      nlinarith only [hsq, hp]
    nlinarith only [hcancel, mul_le_mul_of_nonneg_right hmR (sq_nonneg μ)]
  have hveq : V = (∫ a : ℝ, a ^ 2 ∂ν) - μ ^ 2 :=
    variance_eq_sub ((memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 h2)
  have hm2 : (∫ a : ℝ, a ^ 2 ∂ν) ≤ 2 * V := by linarith
  have hcube : (∫ a : ℝ, |a| ^ 3 ∂ν) ≤ h * (∫ a : ℝ, a ^ 2 ∂ν) := by
    have hi := integral_mono_ae h3 (h2.const_mul h) (by
      filter_upwards [hs] with a ha
      calc
        |a| ^ 3 = |a| * a ^ 2 := by rw [← sq_abs a]; ring
        _ ≤ h * a ^ 2 := mul_le_mul_of_nonneg_right ha (sq_nonneg a))
    simpa only [integral_const_mul] using hi
  refine ⟨h2, (div_le_iff₀ hV).2 ?_⟩
  nlinarith only [hcube, mul_le_mul_of_nonneg_left hm2 hh.le]

private lemma retained_gap (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (σ u v : ℝ) (hσ : |σ| = 1) (hu : u ≠ 0) (hv : |v| ≤ |u| / (4 * h)) :
    (quadraticChordChar ν u v).re ^ 6 * (quadraticChordChar ν (-u) v).re ^ 6 ≤
      (4 ^ 6 / (variance (id : ℝ → ℝ) ν ^ 6 * |u| ^ 12)) *
        (1 - ‖quadraticChar ν (σ * u) v‖ ^ 2) ^ 6 := by
  have hk := quadraticChordChar_exact ν h3 hV u v
  have hl := quadraticChordChar_exact ν h3 hV (-u) v
  have hp : (σ * u) ^ 2 = u ^ 2 := by
    have hs2 : σ ^ 2 = 1 := by nlinarith [sq_abs σ]
    rw [mul_pow, hs2, one_mul]
  have habs : |σ * u| = |u| := by rw [abs_mul, hσ, one_mul]
  have hgap := (quadraticChordChar_cone_gap ν h3 hV h hh hs (σ * u) v
    (by intro he; have := congrArg abs he; simp [habs, hu] at this)
    (by simpa only [habs] using hv)).2
  have hpow := pow_le_pow_left₀
    (quadraticChordChar_exact ν h3 hV (σ * u) v).2.2.2.1 hgap 6
  rw [hp] at hpow
  have hsign : σ = 1 ∨ σ = -1 := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).1 hσ
  have hR : (quadraticChordChar ν u v).re ^ 6 * (quadraticChordChar ν (-u) v).re ^ 6 ≤
      (quadraticChordChar ν (σ * u) v).re ^ 6 := by
    rcases hsign with rfl | rfl
    · simp only [one_mul]
      exact (mul_le_mul_of_nonneg_left
        (pow_le_one₀ hl.2.2.2.1 hl.2.2.2.2) (by positivity)).trans_eq (mul_one _)
    · simp only [neg_one_mul]
      exact (mul_le_mul_of_nonneg_right
        (pow_le_one₀ hk.2.2.2.1 hk.2.2.2.2) (by positivity)).trans_eq (one_mul _)
  refine hR.trans (hpow.trans_eq ?_)
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu
  have ha12 : |u| ^ 12 = u ^ 12 := by
    calc
      _ = (|u| ^ 2) ^ 6 := by ring
      _ = (u ^ 2) ^ 6 := by rw [sq_abs]
      _ = _ := by ring
  rw [ha12]
  field_simp

theorem quadraticChar_power_fullNoise_cone_scale_bounds :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun a : ℝ => |a| ^ 3) ν →
        0 < variance (id : ℝ → ℝ) ν →
        ∀ h : ℝ, 0 < h → (∀ᵐ a : ℝ ∂ν, |a| ≤ h) →
          ∀ m : ℕ, 16 ≤ m →
            ∀ σ u v : ℝ, |σ| = 1 → u ≠ 0 → |v| ≤ |u| / (4 * h) →
              let μ : ℝ := ∫ a : ℝ, a ∂ν
              let S : ℝ := (m : ℝ) * variance (id : ℝ → ℝ) ν
              (m : ℝ) * |μ| ≤ 4 * Real.sqrt S →
              1 ≤ 2 * |u| * Real.sqrt S →
              let f : ℝ → ℂ := fun r =>
                (quadraticChar ν (σ * r) v) ^ m * quadraticFullNoiseChar ν r v
              DifferentiableAt ℝ f u ∧
                DifferentiableAt ℝ (fun r : ℝ => deriv f r) u ∧
                ‖f u‖ ≤ C / (S ^ 6 * |u| ^ 12) ∧
                ‖deriv f u‖ ≤ C * Real.sqrt S / (S ^ 6 * |u| ^ 12) ∧
                ‖deriv (fun r : ℝ => deriv f r) u‖ ≤
                  C * S / (S ^ 6 * |u| ^ 12) := by
  obtain ⟨P, hPpos, hpower⟩ := centeredQuadraticChar_signed_power_gap_bounds
  obtain ⟨A, B, hA, hB, hnoise⟩ := quadraticFullNoiseChar_cone_retained_derivatives
  refine ⟨4 ^ 6 * P * (25 + 20 * A + 4 * B), by positivity, ?_⟩
  intro ν hprob h3 hV h hh hs m hm σ u v hσ hu hv
  dsimp only
  intro hmean hfreq
  let := hprob
  let V : ℝ := variance (id : ℝ → ℝ) ν
  let S : ℝ := (m : ℝ) * V
  let a : ℝ := |u|
  let s : ℝ := Real.sqrt S
  let gap : ℝ := 1 - ‖quadraticChar ν (σ * u) v‖ ^ 2
  let R : ℝ := (quadraticChordChar ν u v).re ^ 6 * (quadraticChordChar ν (-u) v).re ^ 6
  let E : ℝ := 4 ^ 6 / (V ^ 6 * a ^ 12)
  let D : ℝ := 4 ^ 6 * P / (S ^ 6 * a ^ 12)
  let p : ℝ → ℂ := fun r => centeredQuadraticChar ν (σ * r) v ^ m
  let q : ℝ → ℂ := fun r => quadraticFullNoiseChar ν r v
  let G : ℝ → ℂ := fun r => p r * q r
  let b : ℝ := (m : ℝ) * σ * (∫ a : ℝ, a ∂ν)
  have ha : 0 < a := abs_pos.mpr hu
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hS : 0 < S := mul_pos hmpos hV
  have hs0 : 0 ≤ s := Real.sqrt_nonneg S
  have hs2 : s ^ 2 = S := Real.sq_sqrt hS.le
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hinv : 1 / a ≤ 2 * s := (div_le_iff₀ ha).2 (by nlinarith only [hfreq])
  obtain ⟨h2, hgamma⟩ := gamma_payment ν h3 hV h hh hs m hm hmean
  have hp (r : ℝ) : HasDerivAt p (deriv p r) r :=
    (hpower ν hprob h2 m hm σ hσ r v).1.hasDerivAt
  have hq (r : ℝ) : HasDerivAt q (deriv q r) r :=
    (quadraticFullNoiseChar_derivatives ν h3 hV h hh hs hgamma r v).1.differentiableAt.hasDerivAt
  obtain ⟨_, hpp, hp0, hp1, hp2⟩ := hpower ν hprob h2 m hm σ hσ u v
  obtain ⟨_, hqq, hq0, hq1, hq2⟩ := hnoise ν hprob h3 hV h hh hs u v hu hv
  have hrGap : R ≤ E * gap ^ 6 := retained_gap ν h3 hV h hh hs σ u v hσ hu hv
  have transfer (X : ℂ) (c : ℝ) (hc : ‖X‖ * gap ^ 6 ≤ c) : ‖X‖ * R ≤ E * c := by
    calc
      _ ≤ ‖X‖ * (E * gap ^ 6) := mul_le_mul_of_nonneg_left hrGap (norm_nonneg X)
      _ = E * (‖X‖ * gap ^ 6) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc hE
  have hED : E * (P / (m : ℝ) ^ 6) = D := by
    dsimp [E, D, S]
    field_simp
  have hpR0 : ‖p u‖ * R ≤ D := (transfer _ _ hp0).trans_eq hED
  have hpR1 : ‖deriv p u‖ * R ≤ D * s := by
    refine (transfer _ _ hp1).trans_eq ?_
    calc
      E * (P * s / (m : ℝ) ^ 6) = (E * (P / (m : ℝ) ^ 6)) * s := by ring
      _ = _ := by rw [hED]
  have hpR2 : ‖deriv (fun r => deriv p r) u‖ * R ≤ D * S := by
    refine (transfer _ _ hp2).trans_eq ?_
    calc
      E * (P * S / (m : ℝ) ^ 6) = (E * (P / (m : ℝ) ^ 6)) * S := by ring
      _ = _ := by rw [hED]
  have hq1' : ‖deriv q u‖ ≤ (2 * A * s) * R := by
    calc
      _ ≤ A * R / a := hq1
      _ = A * R * (1 / a) := by ring
      _ ≤ A * R * (2 * s) := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring
  have hq2' : ‖deriv (fun r => deriv q r) u‖ ≤ (4 * B * S) * R := by
    calc
      _ ≤ B * R / a ^ 2 := by simpa only [a, sq_abs] using hq2
      _ = B * R * (1 / a) ^ 2 := by ring
      _ ≤ B * R * (2 * s) ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hinv 2) (by positivity)
      _ = _ := by rw [mul_pow, hs2]; ring
  obtain ⟨hG, hGG, hG0, hG1, hG2⟩ := weighted_mul p q hp hq u R D (D * s) (D * S)
    (2 * A * s) (4 * B * S) hR (by positivity) (by positivity)
    hpp hqq hpR0 hpR1 hpR2 hq0 hq1' hq2'
  have hG1' : ‖deriv G u‖ ≤ D * (1 + 2 * A) * s := by
    convert hG1 using 1
    ring
  have hG2' : ‖deriv (fun r => deriv G r) u‖ ≤ D * (1 + 4 * A + 4 * B) * S := by
    refine hG2.trans_eq ?_
    calc
      _ = D * S + 4 * A * D * s ^ 2 + 4 * B * S * D := by ring
      _ = _ := by rw [hs2]; ring
  have hGglobal (r : ℝ) : HasDerivAt G (deriv G r) r :=
    ((hp r).mul (hq r)).differentiableAt.hasDerivAt
  have hb : |b| ≤ 4 * s := by
    simpa only [b, abs_mul, hσ,
      abs_of_nonneg (show (0 : ℝ) ≤ m from Nat.cast_nonneg m), mul_one] using hmean
  have hb2 : b ^ 2 ≤ 16 * S := by
    calc
      _ = |b| ^ 2 := (sq_abs b).symm
      _ ≤ (4 * s) ^ 2 := pow_le_pow_left₀ (abs_nonneg b) hb 2
      _ = _ := by rw [mul_pow, hs2]; norm_num
  have ht (r : ℝ) : HasDerivAt (linearPhase b) (deriv (linearPhase b) r) r :=
    (phase_first b r).differentiableAt.hasDerivAt
  have ht0 : ‖linearPhase b u‖ ≤ 1 := (phase_bounds b u).1.le
  have ht1 : ‖deriv (linearPhase b) u‖ ≤ (4 * s) * 1 := by
    simpa only [(phase_bounds b u).2.1, mul_one] using hb
  have ht2 : ‖deriv (fun r => deriv (linearPhase b) r) u‖ ≤ (16 * S) * 1 := by
    simpa only [(phase_bounds b u).2.2, mul_one] using hb2
  obtain ⟨hF, hFF, hF0, hF1, hF2⟩ := weighted_mul G (linearPhase b) hGglobal ht u 1
    D (D * (1 + 2 * A) * s) (D * (1 + 4 * A + 4 * B) * S) (4 * s) (16 * S)
    (by norm_num) (by positivity) (by positivity) hGG (phase_second b u).differentiableAt
    (by simpa only [mul_one] using hG0) (by simpa only [mul_one] using hG1')
    (by simpa only [mul_one] using hG2') ht0 ht1 ht2
  have hFeq : (fun r => G r * linearPhase b r) = (fun r =>
      (quadraticChar ν (σ * r) v) ^ m * quadraticFullNoiseChar ν r v) := by
    funext r
    calc
      _ = (linearPhase b r * p r) * q r := by dsimp [G]; ring
      _ = _ := by rw [restore_mean]
  change ‖(fun r => G r * linearPhase b r) u‖ ≤ D at hF0
  rw [hFeq] at hF hFF hF0 hF1 hF2
  refine ⟨hF, hFF, hF0.trans ?_, hF1.trans ?_, hF2.trans ?_⟩
  · have hc : 1 ≤ 25 + 20 * A + 4 * B := by nlinarith only [hA, hB]
    have hd := mul_le_mul_of_nonneg_left hc hD
    simpa only [D, mul_one, div_mul_eq_mul_div] using hd
  · have hc : 5 + 2 * A ≤ 25 + 20 * A + 4 * B := by nlinarith only [hA, hB]
    have hd := mul_le_mul_of_nonneg_left hc (mul_nonneg hD hs0)
    calc
      _ = D * s * (5 + 2 * A) := by ring
      _ ≤ D * s * (25 + 20 * A + 4 * B) := hd
      _ = _ := by dsimp [D, s]; ring
  · apply le_of_eq
    calc
      _ = D * (1 + 4 * A + 4 * B) * S + 8 * D * (1 + 2 * A) * s ^ 2 +
          16 * S * D := by ring
      _ = D * S * (25 + 20 * A + 4 * B) := by rw [hs2]; ring
      _ = 4 ^ 6 * P * (25 + 20 * A + 4 * B) *
          ((m : ℝ) * variance (id : ℝ → ℝ) ν) /
          (((m : ℝ) * variance (id : ℝ → ℝ) ν) ^ 6 * |u| ^ 12) := by
        dsimp [D, S, V, a]
        ring

private lemma change_clock (c S T a : ℝ) (hc : 0 ≤ c) (hS : 0 < S)
    (hT : 0 < T) (ha : 0 < a) (hTS : T ≤ 4 * S) :
    c / (S ^ 6 * a ^ 12) ≤ 4 ^ 6 * c / (T ^ 6 * a ^ 12) := by
  have hp := pow_le_pow_left₀ hT.le hTS 6
  have hden : T ^ 6 * a ^ 12 ≤ 4 ^ 6 * (S ^ 6 * a ^ 12) := by
    calc
      _ ≤ (4 * S) ^ 6 * a ^ 12 := mul_le_mul_of_nonneg_right hp (by positivity)
      _ = _ := by ring
  apply (div_le_div_iff₀ (by positivity : 0 < S ^ 6 * a ^ 12)
    (by positivity : 0 < T ^ 6 * a ^ 12)).2
  nlinarith only [mul_le_mul_of_nonneg_left hden hc]

theorem sourceTruncation_fullNoise_highFrequency_derivatives :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
          (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 →
          (∫ a : ℝ, a ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ i : ℕ, i ≤ n → ∀ h kappa L2 : ℝ,
              epsilon / (1 + x) ≤ h → 0 < kappa → 20 ≤ L2 →
              1 ≤ kappa * Real.sqrt L2 →
              let ρ : Measure ℝ :=
                ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
              let m : ℕ := n - i
              let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
              let V : ℝ := variance (id : ℝ → ℝ) ρ
              let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂ρ) / V
              let T : ℝ := (m : ℝ) * m2
              L2 * gamma ^ 2 ≤ T →
              ∀ σ u v : ℝ, |σ| = 1 → u ≠ 0 →
                kappa / gamma ≤ |u| → |v| ≤ |u| / (4 * h) →
                let f : ℝ → ℂ := fun r =>
                  (quadraticChar ρ (σ * r) v) ^ m * quadraticFullNoiseChar ρ r v
                DifferentiableAt ℝ f u ∧
                  DifferentiableAt ℝ (fun r : ℝ => deriv f r) u ∧
                  ‖f u‖ ≤ C / (T ^ 6 * |u| ^ 12) ∧
                  ‖deriv f u‖ ≤ C * Real.sqrt T / (T ^ 6 * |u| ^ 12) ∧
                  ‖deriv (fun r : ℝ => deriv f r) u‖ ≤
                    C * T / (T ^ 6 * |u| ^ 12) := by
  obtain ⟨C, hC, hfull⟩ := quadraticChar_power_fullNoise_cone_scale_bounds
  refine ⟨4 ^ 6 * C, by positivity, ?_⟩
  intro ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h kappa L2
    hh hkappa hL2 hkL2
  dsimp only
  intro hT σ u v hσ hu hufreq hv
  let := hp0
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
  let μ : ℝ := ∫ a : ℝ, a ∂ρ
  let m : ℕ := n - i
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
  let V : ℝ := variance (id : ℝ → ℝ) ρ
  let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂ρ) / V
  let T : ℝ := (m : ℝ) * m2
  let S : ℝ := (m : ℝ) * V
  obtain ⟨_, _, hp, hsupport, _, h2r, h3r, _⟩ :=
    Shao.sourceTruncation_law_data ν0 n h2 hnorm x epsilon hx he hehalf hbudget
  have hprob : IsProbabilityMeasure ρ := hp
  let := hprob
  obtain ⟨hscale, _, _, hVeq, _, hVp, _, _⟩ :=
    Shao.sourceTruncation_variance_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget
  change V = m2 - μ ^ 2 at hVeq
  change 0 < V at hVp
  change (3 / 4 : ℝ) ≤ (n : ℝ) * m2 at hscale
  obtain ⟨_, hgammapos, _, _, _, _, _, _, _⟩ :=
    Shao.sourceTruncation_gamma_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget
  change 0 < gamma at hgammapos
  obtain ⟨hLm, _, hmn, hbias, hm2V⟩ :=
    Shao.sourceTruncation_oddPower_scale_inputs ν0 n h2 hnorm hmean x epsilon hx he hehalf
      hbudget i hi L2 hL2 hT
  change L2 ≤ (m : ℝ) at hLm
  change m ≤ n at hmn
  change (n : ℝ) * |μ| ≤ 1 at hbias
  change m2 ≤ 4 * V at hm2V
  have hm : 16 ≤ m := by
    have : (16 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hS : 0 < S := mul_pos hmpos hVp
  have hVm2 : V ≤ m2 := by nlinarith only [hVeq, sq_nonneg μ]
  have hm2pos : 0 < m2 := hVp.trans_le hVm2
  have hTpos : 0 < T := mul_pos hmpos hm2pos
  have hST : S ≤ T := mul_le_mul_of_nonneg_left hVm2 hmpos.le
  have hTS : T ≤ 4 * S := by
    have hh' := mul_le_mul_of_nonneg_left hm2V hmpos.le
    dsimp [T, S]
    nlinarith only [hh']
  have hcutoff : 0 < epsilon / (1 + x) := div_pos he (by linarith)
  have hhpos : 0 < h := hcutoff.trans_le hh
  have hs : ∀ᵐ a : ℝ ∂ρ, |a| ≤ h := hsupport.mono fun _ ha => ha.trans hh
  have hrootS := Real.sq_sqrt hS.le
  have hrootS0 := Real.sqrt_nonneg S
  -- The retained conditional mean is paid from the original mean-zero normalization.
  have hmeanpaid : (m : ℝ) * |μ| ≤ 4 * Real.sqrt S := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hmnR : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
    have hsq : ((n : ℝ) * |μ|) ^ 2 ≤ 1 := by
      nlinarith only [hbias, mul_nonneg hn (abs_nonneg μ),
        mul_nonneg (sub_nonneg.mpr hbias) (by positivity : 0 ≤ 1 + (n : ℝ) * |μ|)]
    rw [mul_pow, sq_abs] at hsq
    have hc : (n : ℝ) * μ ^ 2 ≤ (4 / 3 : ℝ) * m2 := by
      have hleft := mul_le_mul_of_nonneg_right hscale (mul_nonneg hn (sq_nonneg μ))
      have hright := mul_le_mul_of_nonneg_left hsq hm2pos.le
      nlinarith only [hleft, hright]
    have hmsq : ((m : ℝ) * |μ|) ^ 2 ≤ (4 / 3 : ℝ) * T := by
      calc
        _ = (m : ℝ) * ((m : ℝ) * μ ^ 2) := by rw [mul_pow, sq_abs]; ring
        _ ≤ (m : ℝ) * ((n : ℝ) * μ ^ 2) := by gcongr
        _ ≤ (m : ℝ) * ((4 / 3 : ℝ) * m2) := mul_le_mul_of_nonneg_left hc hmpos.le
        _ = _ := by dsimp [T]; ring
    nlinarith only [hmsq, hTS, hrootS, hrootS0, hS,
      mul_nonneg hmpos.le (abs_nonneg μ)]
  have hfreqpaid : 1 ≤ 2 * |u| * Real.sqrt S := by
    have ha : 0 ≤ |u| := abs_nonneg u
    have hL : 0 ≤ L2 := by linarith
    have hkg : kappa ≤ |u| * gamma := (div_le_iff₀ hgammapos).1 hufreq
    have hk2 := pow_le_pow_left₀ hkappa.le hkg 2
    have hkLsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hkL2 2
    rw [mul_pow, Real.sq_sqrt hL] at hkLsq
    norm_num only [one_pow] at hkLsq
    have hp : 1 ≤ |u| ^ 2 * T := by
      calc
        _ ≤ kappa ^ 2 * L2 := hkLsq
        _ ≤ (|u| * gamma) ^ 2 * L2 := mul_le_mul_of_nonneg_right hk2 hL
        _ = |u| ^ 2 * (L2 * gamma ^ 2) := by ring
        _ ≤ |u| ^ 2 * T := mul_le_mul_of_nonneg_left hT (sq_nonneg |u|)
    have hp2 : 1 ≤ (2 * |u| * Real.sqrt S) ^ 2 := by
      calc
        _ ≤ |u| ^ 2 * T := hp
        _ ≤ |u| ^ 2 * (4 * S) := mul_le_mul_of_nonneg_left hTS (sq_nonneg |u|)
        _ = _ := by rw [mul_pow, mul_pow, hrootS]; ring
    nlinarith only [hp2, mul_nonneg (by positivity : 0 ≤ 2 * |u|) hrootS0]
  obtain ⟨hf, hff, hf0, hf1, hf2⟩ :=
    hfull ρ hprob h3r hVp h hhpos hs m hm σ u v hσ hu hv hmeanpaid hfreqpaid
  refine ⟨hf, hff, hf0.trans ?_, hf1.trans ?_, hf2.trans ?_⟩
  · exact change_clock C S T |u| hC.le hS hTpos (abs_pos.mpr hu) hTS
  · calc
      _ ≤ C * Real.sqrt T / (S ^ 6 * |u| ^ 12) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hST) hC.le)
          (by positivity)
      _ ≤ 4 ^ 6 * (C * Real.sqrt T) / (T ^ 6 * |u| ^ 12) :=
        change_clock (C * Real.sqrt T) S T |u| (by positivity) hS hTpos (abs_pos.mpr hu) hTS
      _ = _ := by ring
  · calc
      _ ≤ C * T / (S ^ 6 * |u| ^ 12) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hST hC.le) (by positivity)
      _ ≤ 4 ^ 6 * (C * T) / (T ^ 6 * |u| ^ 12) :=
        change_clock (C * T) S T |u| (by positivity) hS hTpos (abs_pos.mpr hu) hTS
      _ = _ := by ring

end Shao.Probability
