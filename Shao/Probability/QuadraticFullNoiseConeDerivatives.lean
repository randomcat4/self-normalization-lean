import Shao.Probability.QuadraticFullNoise
import Shao.Probability.QuadraticChordConeDerivatives
import Shao.Probability.SourceScalarFourierDerivatives

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

private noncomputable def chordPhase (u v : ℝ) (z : ℝ × ℝ) : ℂ :=
  Complex.exp (((u * z.1 + v * z.2 : ℝ) : ℂ) * Complex.I)

private lemma chordPhase_norm (u v : ℝ) (z : ℝ × ℝ) : ‖chordPhase u v z‖ = 1 := by
  simp [chordPhase, Complex.norm_exp, Complex.mul_re]

private lemma chordPhase_first_norm (u v : ℝ) (z : ℝ × ℝ) :
    ‖Complex.I * (z.1 : ℂ) * chordPhase u v z‖ = |z.1| := by
  simp [chordPhase_norm]

private lemma chordPhase_hasDerivAt (u v : ℝ) (z : ℝ × ℝ) :
    HasDerivAt (fun r : ℝ => chordPhase r v z)
      (Complex.I * (z.1 : ℂ) * chordPhase u v z) u := by
  unfold chordPhase
  convert (((((hasDerivAt_id u).mul_const z.1).add_const (v * z.2)).ofReal_comp).mul_const
    Complex.I).cexp using 1
  all_goals try funext r
  all_goals try dsimp
  all_goals push_cast
  all_goals ring

private lemma chord_hasDerivAt (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) (u v : ℝ) :
    HasDerivAt (fun r : ℝ => quadraticChordChar ν r v)
      (deriv (fun r : ℝ => quadraticChordChar ν r v) u) u := by
  obtain ⟨_, hc, _, _⟩ := quadraticChord_law_data ν h3 hV h hh hs
  let := hc
  have h1 := (quadraticChord_moments ν h3 hV h hh hs).2.1
  have hphase (r : ℝ) : Integrable (chordPhase r v) (quadraticChordLaw ν) := by
    refine (integrable_const (μ := quadraticChordLaw ν) (1 : ℝ)).mono' ?_
      (Filter.Eventually.of_forall fun z => (chordPhase_norm r v z).le)
    unfold chordPhase
    fun_prop
  have hfirst (r : ℝ) : Integrable
      (fun z => Complex.I * (z.1 : ℂ) * chordPhase r v z) (quadraticChordLaw ν) := by
    refine h1.mono' ?_ (Filter.Eventually.of_forall fun z => (chordPhase_first_norm r v z).le)
    unfold chordPhase
    fun_prop
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ)
    (F' := fun r z => Complex.I * (z.1 : ℂ) * chordPhase r v z)
    (bound := fun z : ℝ × ℝ => |z.1|) (by simp)
    (Filter.Eventually.of_forall fun r => (hphase r).aestronglyMeasurable)
    (hphase u) (hfirst u).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z r _ => (chordPhase_first_norm r v z).le)
    h1 (Filter.Eventually.of_forall fun z r _ => chordPhase_hasDerivAt r v z)).2
      |>.differentiableAt.hasDerivAt

private lemma second_power_hasDerivAt (f : ℝ → ℂ)
    (hf : ∀ r, HasDerivAt f (deriv f r) r)
    (u : ℝ) (hff : HasDerivAt (fun r => deriv f r)
      (deriv (fun r => deriv f r) u) u) (k : ℕ) :
    HasDerivAt (fun r => deriv (fun s => f s ^ k) r)
      ((k : ℂ) * f u ^ (k - 1) * deriv (fun r => deriv f r) u +
      (k : ℂ) * ((k - 1 : ℕ) : ℂ) * f u ^ (k - 2) * (deriv f u) ^ 2) u := by
  have hfirst (r : ℝ) : deriv (fun s => f s ^ k) r =
      (k : ℂ) * f r ^ (k - 1) * deriv f r := (hf r |>.pow k).deriv
  have hd := (((hf u).pow (k - 1)).mul hff).const_mul (k : ℂ)
  have he : HasDerivAt (fun r => deriv (fun s => f s ^ k) r)
      ((k : ℂ) * (((k - 1 : ℕ) : ℂ) * f u ^ (k - 1 - 1) * deriv f u *
        deriv f u + f u ^ (k - 1) * deriv (fun r => deriv f r) u)) u := by
    convert hd using 1
    funext r
    dsimp
    rw [hfirst]
    ring
  convert he using 1
  simp only [Nat.sub_sub]
  ring

private lemma second_mul_hasDerivAt (f g : ℝ → ℂ)
    (hf : ∀ r, HasDerivAt f (deriv f r) r)
    (hg : ∀ r, HasDerivAt g (deriv g r) r) (u : ℝ)
    (hff : HasDerivAt (fun r => deriv f r) (deriv (fun r => deriv f r) u) u)
    (hgg : HasDerivAt (fun r => deriv g r) (deriv (fun r => deriv g r) u) u) :
    HasDerivAt (fun r => deriv (fun s => f s * g s) r)
      (deriv (fun r => deriv f r) u * g u +
        2 * deriv f u * deriv g u + f u * deriv (fun r => deriv g r) u) u := by
  have hd := ((hff.mul (hg u)).add ((hf u).mul hgg)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => ((hf r).mul (hg r)).deriv)
  convert hd using 1
  ring

private lemma power8_bounds (f : ℝ → ℂ)
    (hf : ∀ r, HasDerivAt f (deriv f r) r) (u a : ℝ) (ha : 0 < a)
    (hff : HasDerivAt (fun r => deriv f r) (deriv (fun r => deriv f r) u) u)
    (h0 : ‖f u‖ ≤ 1) (h1 : ‖deriv f u‖ ≤ 8 / a)
    (h2 : ‖deriv (fun r => deriv f r) u‖ ≤ 64 / a ^ 2) :
    HasDerivAt (fun r => deriv (fun s => f s ^ 8) r)
      (deriv (fun r => deriv (fun s => f s ^ 8) r) u) u ∧
    ‖f u ^ 8‖ ≤ ‖f u‖ ^ 6 ∧
    ‖deriv (fun r => f r ^ 8) u‖ ≤ 64 * ‖f u‖ ^ 6 / a ∧
    ‖deriv (fun r => deriv (fun s => f s ^ 8) r) u‖ ≤ 4096 * ‖f u‖ ^ 6 / a ^ 2 := by
  have hp7 : ‖f u‖ ^ 7 ≤ ‖f u‖ ^ 6 := by
    calc
      _ = ‖f u‖ ^ 6 * ‖f u‖ := by ring
      _ ≤ ‖f u‖ ^ 6 * 1 := mul_le_mul_of_nonneg_left h0 (by positivity)
      _ = _ := mul_one _
  have hp8 : ‖f u‖ ^ 8 ≤ ‖f u‖ ^ 6 := by
    calc
      _ = ‖f u‖ ^ 6 * ‖f u‖ ^ 2 := by ring
      _ ≤ ‖f u‖ ^ 6 * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ (norm_nonneg _) h0) (by positivity)
      _ = _ := mul_one _
  have hsecond := second_power_hasDerivAt f hf u hff 8
  refine ⟨hsecond.differentiableAt.hasDerivAt, by simpa only [norm_pow] using hp8, ?_, ?_⟩
  · have hfirst : deriv (fun r => f r ^ 8) u = (8 : ℂ) * f u ^ 7 * deriv f u :=
      (hf u |>.pow 8).deriv
    rw [hfirst]
    calc
      _ = 8 * ‖f u‖ ^ 7 * ‖deriv f u‖ := by simp [norm_pow]
      _ ≤ 8 * ‖f u‖ ^ 7 * (8 / a) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 8 * ‖f u‖ ^ 6 * (8 / a) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp7 (by norm_num)) (by positivity)
      _ = _ := by ring
  · rw [hsecond.deriv]
    norm_num only [Nat.reduceSub, Nat.cast_ofNat]
    calc
      _ ≤ 8 * ‖f u‖ ^ 7 * ‖deriv (fun r => deriv f r) u‖ +
          56 * ‖f u‖ ^ 6 * ‖deriv f u‖ ^ 2 := by
        exact (norm_add_le _ _).trans_eq (by simp [norm_pow])
      _ ≤ 8 * ‖f u‖ ^ 6 * (64 / a ^ 2) + 56 * ‖f u‖ ^ 6 * (8 / a) ^ 2 := by
        apply add_le_add
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hp7 (by norm_num)) h2
            (norm_nonneg _) (by positivity)
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h1 2) (by positivity)
      _ = _ := by field_simp; ring

private lemma mul_bounds (f g : ℝ → ℂ)
    (hf : ∀ r, HasDerivAt f (deriv f r) r)
    (hg : ∀ r, HasDerivAt g (deriv g r) r) (u a p q A1 A2 B1 B2 : ℝ)
    (ha : 0 < a) (hp : 0 ≤ p) (_hq : 0 ≤ q)
    (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (_hB1 : 0 ≤ B1) (_hB2 : 0 ≤ B2)
    (hff : HasDerivAt (fun r => deriv f r) (deriv (fun r => deriv f r) u) u)
    (hgg : HasDerivAt (fun r => deriv g r) (deriv (fun r => deriv g r) u) u)
    (hf0 : ‖f u‖ ≤ p) (hf1 : ‖deriv f u‖ ≤ A1 * p / a)
    (hf2 : ‖deriv (fun r => deriv f r) u‖ ≤ A2 * p / a ^ 2)
    (hg0 : ‖g u‖ ≤ q) (hg1 : ‖deriv g u‖ ≤ B1 * q / a)
    (hg2 : ‖deriv (fun r => deriv g r) u‖ ≤ B2 * q / a ^ 2) :
    HasDerivAt (fun r => deriv (fun s => f s * g s) r)
      (deriv (fun r => deriv (fun s => f s * g s) r) u) u ∧
    ‖f u * g u‖ ≤ p * q ∧
    ‖deriv (fun r => f r * g r) u‖ ≤ (A1 + B1) * (p * q) / a ∧
    ‖deriv (fun r => deriv (fun s => f s * g s) r) u‖ ≤
      (A2 + 2 * A1 * B1 + B2) * (p * q) / a ^ 2 := by
  have hsecond := second_mul_hasDerivAt f g hf hg u hff hgg
  refine ⟨hsecond.differentiableAt.hasDerivAt, ?_, ?_, ?_⟩
  · rw [norm_mul]
    exact mul_le_mul hf0 hg0 (norm_nonneg _) hp
  · have hfirst : deriv (fun r => f r * g r) u = deriv f u * g u + f u * deriv g u :=
      ((hf u).mul (hg u)).deriv
    rw [hfirst]
    calc
      _ ≤ ‖deriv f u‖ * ‖g u‖ + ‖f u‖ * ‖deriv g u‖ := by
        simpa only [norm_mul] using norm_add_le (deriv f u * g u) (f u * deriv g u)
      _ ≤ (A1 * p / a) * q + p * (B1 * q / a) := add_le_add
        (mul_le_mul hf1 hg0 (norm_nonneg _) (by positivity))
        (mul_le_mul hf0 hg1 (norm_nonneg _) hp)
      _ = _ := by ring
  · rw [hsecond.deriv]
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
      _ ≤ (A2 * p / a ^ 2) * q + 2 * (A1 * p / a) * (B1 * q / a) +
          p * (B2 * q / a ^ 2) := add_le_add
        (add_le_add (mul_le_mul hf2 hg0 (norm_nonneg _) (by positivity))
          (mul_le_mul (mul_le_mul_of_nonneg_left hf1 (by norm_num)) hg1
            (norm_nonneg _) (by positivity)))
        (mul_le_mul hf0 hg2 (norm_nonneg _) hp)
      _ = _ := by field_simp

private lemma chord_norm_re (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν) (u v : ℝ) :
    ‖quadraticChordChar ν u v‖ = (quadraticChordChar ν u v).re ∧
      ‖quadraticChordChar ν u v‖ ≤ 1 := by
  obtain ⟨_, _, him, hn, hb⟩ := quadraticChordChar_exact ν h3 hV u v
  have he : quadraticChordChar ν u v = ((quadraticChordChar ν u v).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hnorm : ‖quadraticChordChar ν u v‖ = (quadraticChordChar ν u v).re := by
    conv_lhs => rw [he]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
  exact ⟨hnorm, hnorm.trans_le hb⟩

theorem quadraticFullNoiseChar_cone_retained_derivatives :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun a : ℝ => |a| ^ 3) ν →
        0 < variance (id : ℝ → ℝ) ν →
        ∀ h : ℝ, 0 < h → (∀ᵐ a : ℝ ∂ν, |a| ≤ h) →
          ∀ u v : ℝ, u ≠ 0 → |v| ≤ |u| / (4 * h) →
            let R : ℝ :=
              (quadraticChordChar ν u v).re ^ 6 *
                (quadraticChordChar ν (-u) v).re ^ 6
            DifferentiableAt ℝ (fun t : ℝ => quadraticFullNoiseChar ν t v) u ∧
            DifferentiableAt ℝ
              (fun t : ℝ => deriv (fun r : ℝ => quadraticFullNoiseChar ν r v) t) u ∧
            ‖quadraticFullNoiseChar ν u v‖ ≤ R ∧
            ‖deriv (fun t : ℝ => quadraticFullNoiseChar ν t v) u‖ ≤ C1 * R / |u| ∧
            ‖deriv
              (fun t : ℝ => deriv (fun r : ℝ => quadraticFullNoiseChar ν r v) t) u‖ ≤
                C2 * R / u ^ 2 := by
  obtain ⟨A, B, hA, hB, hscalar⟩ := sourceScalarChar_scaled_derivative_bounds
  refine ⟨128 + A, 16384 + 256 * A + B, by positivity, by positivity, ?_⟩
  intro ν hprob h3 hV h hh hs u v hu hv
  let := hprob
  let K : ℝ → ℂ := fun r => quadraticChordChar ν r v
  let L : ℝ → ℂ := fun r => quadraticChordChar ν (-r) v
  let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν
  let Q : ℝ → ℂ := fun r => sourceScalarChar (gamma * r)
  let P : ℝ → ℂ := fun r => K r ^ 8
  let N : ℝ → ℂ := fun r => L r ^ 8
  have hK (r : ℝ) : HasDerivAt K (deriv K r) r := chord_hasDerivAt ν h3 hV h hh hs r v
  have hL (r : ℝ) : HasDerivAt L (deriv L r) r :=
    ((hK (-r)).scomp r (hasDerivAt_neg r)).differentiableAt.hasDerivAt
  have hQ (r : ℝ) : HasDerivAt Q (deriv Q r) r :=
    (sourceScalarChar_scaled_derivatives gamma r).1.differentiableAt.hasDerivAt
  obtain ⟨_, _, _, hKsecond, _, _⟩ := quadraticChordChar_cone_derivatives ν h3 hV h hh hs u v hu hv
  obtain ⟨_, _, _, hKsecondNeg, _, hdKsecondNeg⟩ :=
    quadraticChordChar_cone_derivatives ν h3 hV h hh hs (-u) v (neg_ne_zero.mpr hu)
      (by simpa only [abs_neg] using hv)
  have hLderiv (r : ℝ) : deriv L r = -deriv K (-r) := by
    simpa only [Function.comp_def, K, L, neg_one_smul] using
      ((hK (-r)).scomp r (hasDerivAt_neg r)).deriv
  have hLsecond := ((hKsecondNeg.scomp u (hasDerivAt_neg u)).neg).congr_of_eventuallyEq
    (Filter.Eventually.of_forall hLderiv)
  have hQsecond := (sourceScalarChar_scaled_derivatives gamma u).2.1.differentiableAt.hasDerivAt
  have hk0 := (chord_norm_re ν h3 hV u v).2
  have hl0 := (chord_norm_re ν h3 hV (-u) v).2
  obtain ⟨hk1, hk2⟩ := quadraticChordChar_cone_derivative_bounds ν h3 hV h hh hs u v hu hv
  obtain ⟨hl1, hl2⟩ := quadraticChordChar_cone_derivative_bounds ν h3 hV h hh hs (-u) v
    (neg_ne_zero.mpr hu) (by simpa only [abs_neg] using hv)
  have hl1' : ‖deriv L u‖ ≤ 8 / |u| := by
    rw [hLderiv, norm_neg]
    simpa only [abs_neg] using hl1
  have hl2' : ‖deriv (fun r => deriv L r) u‖ ≤ 64 / |u| ^ 2 := by
    rw [hLsecond.deriv]
    simp only [neg_one_smul, neg_neg]
    rw [hdKsecondNeg] at hl2
    simpa only [neg_sq, sq_abs] using hl2
  have hk2' : ‖deriv (fun r => deriv K r) u‖ ≤ 64 / |u| ^ 2 := by
    simpa only [sq_abs] using hk2
  obtain ⟨hPsecond, hp0, hp1, hp2⟩ := power8_bounds K hK u |u| (abs_pos.mpr hu)
    hKsecond.differentiableAt.hasDerivAt hk0 hk1 hk2'
  obtain ⟨hNsecond, hn0, hn1, hn2⟩ := power8_bounds L hL u |u| (abs_pos.mpr hu)
    hLsecond.differentiableAt.hasDerivAt hl0 hl1' hl2'
  have hP (r : ℝ) : HasDerivAt P (deriv P r) r := (hK r |>.pow 8).differentiableAt.hasDerivAt
  have hN (r : ℝ) : HasDerivAt N (deriv N r) r := (hL r |>.pow 8).differentiableAt.hasDerivAt
  obtain ⟨hPNsecond, hpn0, hpn1, hpn2⟩ := mul_bounds P N hP hN u |u|
    (‖K u‖ ^ 6) (‖L u‖ ^ 6) 64 4096 64 4096
    (abs_pos.mpr hu) (by positivity) (by positivity)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hPsecond hNsecond hp0 hp1 hp2 hn0 hn1 hn2
  norm_num only [Nat.reduceAdd, Nat.reduceMul] at hpn1 hpn2
  have hPN (r : ℝ) : HasDerivAt (fun s => P s * N s) (deriv (fun s => P s * N s) r) r :=
    ((hP r).mul (hN r)).differentiableAt.hasDerivAt
  obtain ⟨hq1, hq2⟩ := hscalar gamma u hu
  have hq0 : ‖Q u‖ ≤ 1 := (sourceScalarChar_even_bound (gamma * u)).2.2
  obtain ⟨hFsecond, hf0, hf1, hf2⟩ := mul_bounds (fun r => P r * N r) Q hPN hQ u |u|
    (‖K u‖ ^ 6 * ‖L u‖ ^ 6) 1 128 16384 A B
    (abs_pos.mpr hu) (by positivity) (by norm_num) (by norm_num) (by norm_num) hA.le hB.le
    hPNsecond hQsecond hpn0 hpn1 hpn2 hq0 (by simpa only [mul_one] using hq1)
    (by simpa only [mul_one, sq_abs] using hq2)
  have hF (r : ℝ) : HasDerivAt (fun s => P s * N s * Q s)
      (deriv (fun s => P s * N s * Q s) r) r :=
    ((hPN r).mul (hQ r)).differentiableAt.hasDerivAt
  have hE (r : ℝ) : quadraticFullNoiseChar ν r v = P r * N r * Q r :=
    (quadraticFullNoiseChar_product ν h3 hV h hh hs r v).1
  have hEF : (fun r => quadraticFullNoiseChar ν r v) = (fun r => P r * N r * Q r) := funext hE
  dsimp only
  rw [hEF, hE u]
  refine ⟨(hF u).differentiableAt, hFsecond.differentiableAt, ?_, ?_, ?_⟩
  all_goals
    simp only [mul_one] at hf0 hf1 hf2
    rw [(chord_norm_re ν h3 hV u v).1, (chord_norm_re ν h3 hV (-u) v).1] at hf0 hf1 hf2
  · exact hf0
  · exact hf1
  · convert hf2 using 1
    rw [sq_abs]
    ring

theorem quadraticFullNoiseChar_cone_derivative_bounds :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun a : ℝ => |a| ^ 3) ν →
        0 < variance (id : ℝ → ℝ) ν →
        ∀ h : ℝ, 0 < h → (∀ᵐ a : ℝ ∂ν, |a| ≤ h) →
          ∀ u v : ℝ, u ≠ 0 → |v| ≤ |u| / (4 * h) →
            ‖deriv (fun t : ℝ => quadraticFullNoiseChar ν t v) u‖ ≤ C1 / |u| ∧
            ‖deriv
              (fun t : ℝ => deriv (fun r : ℝ => quadraticFullNoiseChar ν r v) t) u‖ ≤
                C2 / u ^ 2 := by
  obtain ⟨C1, C2, hC1, hC2, hbound⟩ := quadraticFullNoiseChar_cone_retained_derivatives
  refine ⟨C1, C2, hC1, hC2, ?_⟩
  intro ν hprob h3 hV h hh hs u v hu hv
  let := hprob
  obtain ⟨_, _, _, h1, h2⟩ := hbound ν hprob h3 hV h hh hs u v hu hv
  have hk := (chord_norm_re ν h3 hV u v).2
  have hl := (chord_norm_re ν h3 hV (-u) v).2
  have hr : (quadraticChordChar ν u v).re ^ 6 * (quadraticChordChar ν (-u) v).re ^ 6 ≤ 1 := by
    rw [← (chord_norm_re ν h3 hV u v).1, ← (chord_norm_re ν h3 hV (-u) v).1]
    exact (mul_le_mul (pow_le_one₀ (norm_nonneg _) hk) (pow_le_one₀ (norm_nonneg _) hl)
      (by positivity) (by norm_num)).trans_eq (by norm_num)
  constructor
  · exact h1.trans (div_le_div_of_nonneg_right
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hr hC1.le) (abs_nonneg u))
  · exact h2.trans (div_le_div_of_nonneg_right
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hr hC2.le) (sq_nonneg u))

end Shao.Probability
