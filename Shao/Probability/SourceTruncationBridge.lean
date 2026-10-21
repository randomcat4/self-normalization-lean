import Shao.Probability.TruncationSampleSize
import Shao.Probability.RetainedVariance
import Shao.Probability.GaussianTail
import Mathlib.Probability.Moments.Variance

/-!
The original cutoff epsilon/(1+x), its actual conditional probability law,
and the moment payments retaining the original truncation budget.
-/

set_option autoImplicit false

namespace Shao

open MeasureTheory ProbabilityTheory

theorem sourceTruncation_reparameterization
    (nu : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    let a : ℝ := 1 + x
    let b : ℝ := a / epsilon
    let B : Set ℝ := {z | |z| ≤ epsilon / a}
    let H : ℝ := (n : ℝ) * ∫ z : ℝ, truncationF (b * z) ∂nu
    1 / b = epsilon / a ∧
      retainedCutoffSet b = B ∧
      retainedCutoffLaw nu b = ProbabilityTheory.cond nu B ∧
      H = truncationBudget nu n (b - 1) ∧
      truncationBudget nu n x / epsilon ^ 2 ≤ H ∧
      H ≤ truncationBudget nu n x / epsilon ^ 3 := by
  let a : ℝ := 1 + x
  let b : ℝ := a / epsilon
  let H : ℝ := (n : ℝ) * ∫ z : ℝ, truncationF (b * z) ∂nu
  have ha : 0 < a := by dsimp [a]; linarith
  have hi : 1 / b = epsilon / a := by dsimp [b]; field_simp
  have hB : retainedCutoffSet b = {z : ℝ | |z| ≤ epsilon / a} := by
    ext z
    simp only [retainedCutoffSet, Set.mem_ofPred_eq, hi]
  have hH : H = truncationBudget nu n (b - 1) := by
    have hh : 1 + (b - 1) = b := by ring
    simp only [H, truncationBudget, hh]
  have hc : (1 : ℝ) ≤ 1 / epsilon := (le_div_iff₀ hepsilon).2 (by linarith)
  have harg : (1 / epsilon) * (1 + x) - 1 = b - 1 := by dsimp [b, a]; ring
  have hs := truncationBudget_scale_one_le nu n h2 x (1 / epsilon) hc
  rw [harg, ← hH] at hs
  refine ⟨hi, hB, ?_, hH, ?_, ?_⟩
  · change ProbabilityTheory.cond nu (retainedCutoffSet b) = _
    rw [hB]
  · simpa only [div_pow, one_pow, one_div_mul_eq_div] using hs.1
  · simpa only [div_pow, one_pow, one_div_mul_eq_div] using hs.2

private theorem st_positive_data
    (nu : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (x : ℝ) (hx : 0 ≤ x) :
    0 < n ∧ (1 : ℝ) ≤ n ∧ 0 < truncationBudget nu n x := by
  have hn : 0 < n := by
    by_contra h
    have hz := Nat.eq_zero_of_not_pos h
    simp [hz] at hnorm
  have hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂nu := by
    by_contra h
    have hh := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (le_of_not_gt h)
    rw [hnorm] at hh
    norm_num at hh
  exact ⟨hn, by exact_mod_cast hn, truncationBudget_pos nu n h2 hn hsecond x hx⟩

theorem sourceTruncation_sample_size
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : truncationBudget nu n x ≤ epsilon ^ 3 / 8) :
    let b : ℝ := (1 + x) / epsilon
    2 ≤ b ∧ b ^ 6 ≤ (n : ℝ) ∧ 64 ≤ n ∧
      (n : ℝ) * (∫ z : ℝ, truncationF (b * z) ∂nu) ≤ 1 / 8 := by
  let a : ℝ := 1 + x
  let b : ℝ := a / epsilon
  let R : ℝ := truncationBudget nu n x
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  have hb : 2 ≤ b := (le_div_iff₀ hepsilon).2 (by nlinarith)
  have hb0 : 0 < b := by linarith
  have he1 : epsilon ≤ 1 := by linarith
  obtain ⟨_, _, hRp⟩ := st_positive_data nu n h2 hnorm x hx
  change 0 < R at hRp
  have he3 : epsilon ^ 3 ≤ (1 / 2 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hepsilon.le hepsilonHalf 3
  have hR64 : R ≤ 1 / 64 := by dsimp only [R]; nlinarith [hR]
  have hs := (truncationBudget_sample_size_lower nu n h2 hnorm x R hx
    (le_refl R) (by linarith)).2
  change (1 - R) ^ 3 * a ^ 6 / R ^ 2 ≤ (n : ℝ) at hs
  have hR2 : R ^ 2 ≤ epsilon ^ 6 / 64 := by
    have hh := pow_le_pow_left₀ hRp.le hR 2
    nlinarith only [hh]
  have hone : (1 / 64 : ℝ) ≤ (1 - R) ^ 3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 63 / 64)
      (show (63 / 64 : ℝ) ≤ 1 - R by linarith) 3
    norm_num at hh ⊢
    linarith
  have hb6 : b ^ 6 ≤ (n : ℝ) := by
    apply le_trans _ hs
    apply (le_div_iff₀ (sq_pos_of_pos hRp)).2
    have hpoly : R ^ 2 ≤ epsilon ^ 6 * (1 - R) ^ 3 := by
      calc
        R ^ 2 ≤ epsilon ^ 6 / 64 := hR2
        _ ≤ epsilon ^ 6 * (1 - R) ^ 3 := by
          have hh := mul_le_mul_of_nonneg_left hone (pow_nonneg hepsilon.le 6)
          nlinarith only [hh]
    dsimp only [b]
    rw [div_pow]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (pow_pos hepsilon 6)).2
    have hh := mul_le_mul_of_nonneg_left hpoly (pow_nonneg ha0.le 6)
    nlinarith only [hh]
  have hn64 : 64 ≤ n := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hb 6
    norm_num at hh
    have hN : (64 : ℝ) ≤ n := hh.trans hb6
    exact_mod_cast hN
  have hscale := (sourceTruncation_reparameterization nu n h2 x epsilon hx hepsilon he1).2.2.2.2.2
  have hH : (n : ℝ) * (∫ z : ℝ, truncationF (b * z) ∂nu) ≤ 1 / 8 := by
    apply hscale.trans
    apply (div_le_iff₀ (pow_pos hepsilon 3)).2
    nlinarith only [hR]
  exact ⟨hb, hb6, hn64, hH⟩

theorem sourceTruncation_tail_budget
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    let a : ℝ := 1 + x
    let h : ℝ := epsilon / a
    let R : ℝ := truncationBudget nu n x
    (n : ℝ) * nu.real {z | h < |z|} ≤ R / epsilon ^ 3 ∧
      (n : ℝ) * (∫ z : ℝ, if h < |z| then |z| else 0 ∂nu) ≤
        R / (epsilon ^ 2 * a) ∧
      (n : ℝ) * (∫ z : ℝ, if h < |z| then z ^ 2 else 0 ∂nu) ≤
        R / (epsilon * a ^ 2) := by
  let a : ℝ := 1 + x
  let b : ℝ := a / epsilon
  let R : ℝ := truncationBudget nu n x
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := div_pos ha hepsilon
  have hp := sourceTruncation_reparameterization nu n h2 x epsilon hx hepsilon hepsilon1
  have hi : 1 / b = epsilon / a := hp.1
  have hscale : (n : ℝ) * (∫ z : ℝ, truncationF (b * z) ∂nu) ≤ R / epsilon ^ 3 :=
    hp.2.2.2.2.2
  have hB := measurableSet_retainedCutoffSet b
  have hmass : nu.real {z : ℝ | epsilon / a < |z|} =
      ∫ z : ℝ, (retainedCutoffSet b)ᶜ.indicator (fun _z => (1 : ℝ)) z ∂nu := by
    have ht := integral_indicator_one (μ := nu) hB.compl
    change (∫ z : ℝ, (retainedCutoffSet b)ᶜ.indicator (fun _z => (1 : ℝ)) z ∂nu) =
      nu.real (retainedCutoffSet b)ᶜ at ht
    rw [ht]
    congr 1
    ext z
    simp only [Set.mem_compl_iff, retainedCutoffSet, Set.mem_ofPred_eq, not_le, hi]
  have hpoint (z : ℝ) :
      (retainedCutoffSet b)ᶜ.indicator (fun _z => (1 : ℝ)) z ≤ truncationF (b * z) := by
    simp only [Set.indicator, Set.mem_compl_iff, retainedCutoffSet,
      Set.mem_ofPred_eq, not_le]
    split_ifs with hl
    · have hh : 1 ≤ |b * z| := by
        rw [abs_mul, abs_of_pos hb]
        have hh := (div_lt_iff₀ hb).mp hl
        nlinarith
      rw [truncationF_of_one_le_abs _ hh, ← sq_abs]
      nlinarith
    · exact truncationF_nonneg _
  have hmassI := integral_mono ((integrable_const (1 : ℝ)).indicator hB.compl)
    (integrable_truncationF_mul nu h2 b) hpoint
  have hm : (n : ℝ) * nu.real {z : ℝ | epsilon / a < |z|} ≤ R / epsilon ^ 3 := by
    rw [hmass]
    exact (mul_le_mul_of_nonneg_left hmassI (Nat.cast_nonneg n)).trans hscale
  have h1 := mul_le_mul_of_nonneg_left (integral_truncation_tail_one_le nu h2 b hb)
    (Nat.cast_nonneg n)
  have h2t := mul_le_mul_of_nonneg_left (integral_truncation_tail_two_le nu h2 b hb)
    (Nat.cast_nonneg n)
  rw [hi] at h1 h2t
  have h1' : b * ((n : ℝ) * ∫ z : ℝ, if epsilon / a < |z| then |z| else 0 ∂nu) ≤
      R / epsilon ^ 3 := by
    apply le_trans _ hscale
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h1
  have h2' : b ^ 2 * ((n : ℝ) * ∫ z : ℝ, if epsilon / a < |z| then z ^ 2 else 0 ∂nu) ≤
      R / epsilon ^ 3 := by
    apply le_trans _ hscale
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2t
  refine ⟨hm, ?_, ?_⟩
  · apply (le_div_iff₀ (mul_pos (pow_pos hepsilon 2) ha)).2
    have hh := (le_div_iff₀ (pow_pos hepsilon 3)).mp h1'
    calc
      _ = (b * ((n : ℝ) * ∫ z : ℝ, if epsilon / a < |z| then |z| else 0 ∂nu)) *
          epsilon ^ 3 := by dsimp [b]; field_simp; ring
      _ ≤ R := hh
  · apply (le_div_iff₀ (mul_pos hepsilon (pow_pos ha 2))).2
    have hh := (le_div_iff₀ (pow_pos hepsilon 3)).mp h2'
    calc
      _ = (b ^ 2 * ((n : ℝ) * ∫ z : ℝ, if epsilon / a < |z| then z ^ 2 else 0 ∂nu)) *
          epsilon ^ 3 := by dsimp [b]; field_simp; ring
      _ ≤ R := hh

theorem sourceTruncation_law_data
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : truncationBudget nu n x ≤ epsilon ^ 3 / 8) :
    let B : Set ℝ := {z | |z| ≤ epsilon / (1 + x)}
    let rho : Measure ℝ := ProbabilityTheory.cond nu B
    (3 / 4 : ℝ) ≤ nu.real B ∧ nu.real B ≤ 1 ∧
      IsProbabilityMeasure rho ∧
      (∀ᵐ z : ℝ ∂rho, |z| ≤ epsilon / (1 + x)) ∧
      Integrable (fun z : ℝ => z) rho ∧
      Integrable (fun z : ℝ => z ^ 2) rho ∧
      Integrable (fun z : ℝ => |z| ^ 3) rho ∧
      Integrable (fun z : ℝ => z ^ 4) rho := by
  let b : ℝ := (1 + x) / epsilon
  have he1 : epsilon ≤ 1 := by linarith
  obtain ⟨hb2, _, hn64, hH⟩ := sourceTruncation_sample_size nu n h2 hnorm x epsilon hx
    hepsilon hepsilonHalf hR
  have hb : 0 < b := by change 0 < (1 + x) / epsilon; positivity
  have hn : 2 ≤ n := by omega
  have hN : (64 : ℝ) ≤ n := by exact_mod_cast hn64
  have hNp : (0 : ℝ) < n := by linarith
  have hp := sourceTruncation_reparameterization nu n h2 x epsilon hx hepsilon he1
  have hi : 1 / b = epsilon / (1 + x) := hp.1
  have hlaw := hp.2.2.1
  obtain ⟨hqlo, _, hqhi⟩ := retainedCutoffMass_bounds nu n hn b hb h2
    (hH.trans (by norm_num))
  have hq34 : (3 / 4 : ℝ) ≤ retainedCutoffMass nu b := by
    have hh : 1 / (n : ℝ) ≤ (1 / 4 : ℝ) := (div_le_iff₀ hNp).2 (by linarith)
    linarith
  have hq : 0 < retainedCutoffMass nu b := by linarith
  have hmass : retainedCutoffMass nu b =
      nu.real {z : ℝ | |z| ≤ epsilon / (1 + x)} := by
    change (nu (retainedCutoffSet b)).toReal = _
    rw [hp.2.1]
    rfl
  have instProb : IsProbabilityMeasure (retainedCutoffLaw nu b) :=
    retainedCutoffLaw_isProbabilityMeasure nu b hq
  have hsp := ae_abs_le_retainedCutoffLaw nu b hq
  obtain ⟨h1, hsq⟩ := integrable_retainedCutoffLaw_id_sq nu b hq h2
  have h3 := integrable_retainedCutoffLaw_abs_cube nu b hb hq h2
  have h4 : Integrable (fun z : ℝ => z ^ 4) (retainedCutoffLaw nu b) := by
    apply (integrable_const ((1 / b) ^ 4)).mono'
      (continuous_id.pow 4).aestronglyMeasurable
    filter_upwards [hsp] with z hz
    change ‖z ^ 4‖ ≤ (1 / b) ^ 4
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg z) hz 4
  dsimp only
  rw [← hlaw]
  exact ⟨hmass ▸ hq34, hmass ▸ hqhi, inferInstance,
    by simpa only [hi] using hsp, h1, hsq, h3, h4⟩

private theorem st_raw_paid
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : truncationBudget nu n x ≤ epsilon ^ 3 / 8) :
    let a : ℝ := 1 + x
    let rho : Measure ℝ := ProbabilityTheory.cond nu {z | |z| ≤ epsilon / a}
    (n : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂rho) ≤ 2 * truncationBudget nu n x / a ^ 3 ∧
      (n : ℝ) * (∫ z : ℝ, z ^ 4 ∂rho) ≤
        (epsilon / a) * ((n : ℝ) * ∫ z : ℝ, |z| ^ 3 ∂rho) := by
  let a : ℝ := 1 + x
  let b : ℝ := a / epsilon
  let rho : Measure ℝ := ProbabilityTheory.cond nu {z | |z| ≤ epsilon / a}
  let R : ℝ := truncationBudget nu n x
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := div_pos ha hepsilon
  have he1 : epsilon ≤ 1 := by linarith
  have hp := sourceTruncation_reparameterization nu n h2 x epsilon hx hepsilon he1
  have hi : 1 / b = epsilon / a := hp.1
  have hlaw : retainedCutoffLaw nu b = rho := hp.2.2.1
  obtain ⟨hq34, _, _, hsp, _, _, h3, h4⟩ :=
    sourceTruncation_law_data nu n h2 hnorm x epsilon hx hepsilon hepsilonHalf hR
  have hmass : retainedCutoffMass nu b = nu.real {z : ℝ | |z| ≤ epsilon / a} := by
    change (nu (retainedCutoffSet b)).toReal = _
    rw [hp.2.1]
    rfl
  have hq34' : (3 / 4 : ℝ) ≤ retainedCutoffMass nu b := by rw [hmass]; exact hq34
  have hq : 0 < retainedCutoffMass nu b := by linarith
  have hba : 1 / b ≤ 1 / a := by
    rw [hi]
    exact div_le_div_of_nonneg_right he1 ha.le
  have hsmall := integrable_truncation_small_three nu h2 a ha
  have hnumInt := integrable_truncation_small_three nu h2 b hb
  have hsub : (∫ z : ℝ, if |z| ≤ 1 / b then |z| ^ 3 else 0 ∂nu) ≤
      ∫ z : ℝ, if |z| ≤ 1 / a then |z| ^ 3 else 0 ∂nu := by
    apply integral_mono hnumInt hsmall
    intro z
    change (if |z| ≤ 1 / b then |z| ^ 3 else 0) ≤
      if |z| ≤ 1 / a then |z| ^ 3 else 0
    by_cases hz : |z| ≤ 1 / b
    · simp only [ite_eq_left hz, ite_eq_left (hz.trans hba), le_refl]
    · rw [ite_eq_right hz]
      split_ifs <;> positivity
  have hnumEq : (∫ z : ℝ in retainedCutoffSet b, |z| ^ 3 ∂nu) =
      ∫ z : ℝ, if |z| ≤ 1 / b then |z| ^ 3 else 0 ∂nu := by
    rw [← integral_indicator (measurableSet_retainedCutoffSet b)]
    rfl
  have hscaled : a ^ 3 * (∫ z : ℝ in retainedCutoffSet b, |z| ^ 3 ∂nu) ≤
      ∫ z : ℝ, truncationF (a * z) ∂nu := by
    rw [hnumEq]
    exact (mul_le_mul_of_nonneg_left hsub (pow_nonneg ha.le 3)).trans
      (integral_truncation_small_three_le nu h2 a ha)
  have hnum : (n : ℝ) * (∫ z : ℝ in retainedCutoffSet b, |z| ^ 3 ∂nu) ≤ R / a ^ 3 := by
    apply (le_div_iff₀ (pow_pos ha 3)).2
    have hh := mul_le_mul_of_nonneg_left hscaled (Nat.cast_nonneg n)
    simpa only [R, a, truncationBudget, mul_assoc, mul_comm, mul_left_comm] using hh
  have hrestricted : Integrable (fun z : ℝ => |z| ^ 3) (nu.restrict (retainedCutoffSet b)) := by
    apply hnumInt.restrict.congr
    filter_upwards [ae_restrict_mem (measurableSet_retainedCutoffSet b)] with z hz
    exact ite_eq_left hz
  have hR0 : 0 ≤ R := truncationBudget_nonneg nu n h2 x
  have hcub : (n : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂retainedCutoffLaw nu b) ≤ 2 * R / a ^ 3 := by
    calc
      _ = ((n : ℝ) * (∫ z : ℝ in retainedCutoffSet b, |z| ^ 3 ∂nu)) /
          retainedCutoffMass nu b := by
        rw [integral_retainedCutoffLaw nu b hq _ hrestricted]
        ring
      _ ≤ (R / a ^ 3) / retainedCutoffMass nu b :=
        div_le_div_of_nonneg_right hnum hq.le
      _ ≤ 2 * R / a ^ 3 := by
        apply (div_le_iff₀ hq).2
        have hh := mul_le_mul_of_nonneg_left
          (show 1 ≤ 2 * retainedCutoffMass nu b by linarith)
          (div_nonneg hR0 (pow_nonneg ha.le 3))
        simpa only [div_eq_mul_inv, one_mul, mul_assoc, mul_comm, mul_left_comm] using hh
  have hf : (∫ z : ℝ, z ^ 4 ∂rho) ≤ (epsilon / a) * (∫ z : ℝ, |z| ^ 3 ∂rho) := by
    have hh := integral_mono_ae h4 (h3.const_mul (epsilon / a)) (by
      filter_upwards [hsp] with z hz
      calc
        z ^ 4 = (z ^ 2) ^ 2 := by ring
        _ = (|z| ^ 2) ^ 2 := by rw [sq_abs]
        _ = |z| * |z| ^ 3 := by ring
        _ ≤ (epsilon / a) * |z| ^ 3 :=
          mul_le_mul_of_nonneg_right hz (pow_nonneg (abs_nonneg z) 3))
    simpa only [integral_const_mul] using hh
  dsimp only
  exact ⟨by simpa only [hlaw] using hcub,
    by simpa only [mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg n)⟩

private theorem st_integrable_id (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu) : Integrable (fun z : ℝ => z) nu := by
  apply ((integrable_const (1 : ℝ)).add h2).mono' continuous_id.aestronglyMeasurable
  exact ae_of_all nu (fun z => by
    change ‖z‖ ≤ 1 + z ^ 2
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|z| - 1), sq_abs z, abs_nonneg z])

private theorem st_compl_integral (nu : Measure ℝ) (b : ℝ) (f : ℝ → ℝ) :
    (∫ z : ℝ in (retainedCutoffSet b)ᶜ, f z ∂nu) =
      ∫ z : ℝ, if 1 / b < |z| then f z else 0 ∂nu := by
  rw [← integral_indicator (measurableSet_retainedCutoffSet b).compl]
  apply integral_congr_ae
  exact ae_of_all nu (fun z => by
    simp only [Set.indicator, Set.mem_compl_iff, retainedCutoffSet, Set.mem_ofPred_eq, not_le])

theorem sourceTruncation_paid_moments
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : truncationBudget nu n x ≤ epsilon ^ 3 / 8) :
    let a : ℝ := 1 + x
    let rho : Measure ℝ := ProbabilityTheory.cond nu {z | |z| ≤ epsilon / a}
    let mu : ℝ := ∫ z : ℝ, z ∂rho
    let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
    let m4 : ℝ := ∫ z : ℝ, z ^ 4 ∂rho
    let R : ℝ := truncationBudget nu n x
    (n : ℝ) * |mu| ≤ 2 * R / (epsilon ^ 2 * a) ∧
      (n : ℝ) * m3 ≤ 2 * R / a ^ 3 ∧
      (n : ℝ) * m4 ≤ (epsilon / a) * ((n : ℝ) * m3) ∧
      Integrable (fun z : ℝ => |z - mu| ^ 3) rho ∧
      (∫ z : ℝ, |z - mu| ^ 3 ∂rho) ≤ 8 * m3 := by
  let a : ℝ := 1 + x
  let b : ℝ := a / epsilon
  let R : ℝ := truncationBudget nu n x
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := div_pos ha hepsilon
  have he1 : epsilon ≤ 1 := by linarith
  have hp := sourceTruncation_reparameterization nu n h2 x epsilon hx hepsilon he1
  have hi : 1 / b = epsilon / a := hp.1
  have hlaw : retainedCutoffLaw nu b =
      ProbabilityTheory.cond nu {z : ℝ | |z| ≤ epsilon / a} := hp.2.2.1
  have hd := sourceTruncation_law_data nu n h2 hnorm x epsilon hx hepsilon hepsilonHalf hR
  have hq34 : (3 / 4 : ℝ) ≤ retainedCutoffMass nu b := by
    change (3 / 4 : ℝ) ≤ (nu (retainedCutoffSet b)).toReal
    rw [hp.2.1]
    exact hd.1
  have hq : 0 < retainedCutoffMass nu b := by linarith
  have h1 := st_integrable_id nu h2
  have hsplit := integral_add_compl (measurableSet_retainedCutoffSet b) h1
  rw [hmean] at hsplit
  have hnum : (∫ z : ℝ in retainedCutoffSet b, z ∂nu) =
      -(∫ z : ℝ in (retainedCutoffSet b)ᶜ, z ∂nu) := by linarith only [hsplit]
  have hnumabs : |∫ z : ℝ in retainedCutoffSet b, z ∂nu| ≤
      ∫ z : ℝ, if epsilon / a < |z| then |z| else 0 ∂nu := by
    calc
      _ = |∫ z : ℝ in (retainedCutoffSet b)ᶜ, z ∂nu| := by rw [hnum, abs_neg]
      _ ≤ ∫ z : ℝ in (retainedCutoffSet b)ᶜ, |z| ∂nu := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := nu.restrict (retainedCutoffSet b)ᶜ)
            (fun z : ℝ => z)
      _ = _ := by rw [st_compl_integral, hi]
  have ht := (sourceTruncation_tail_budget nu n h2 x epsilon hx hepsilon he1).2.1
  have hnumB : (n : ℝ) * |∫ z : ℝ in retainedCutoffSet b, z ∂nu| ≤
      R / (epsilon ^ 2 * a) :=
    (mul_le_mul_of_nonneg_left hnumabs (Nat.cast_nonneg n)).trans ht
  have hR0 : 0 ≤ R := truncationBudget_nonneg nu n h2 x
  have hmu : (n : ℝ) * |∫ z : ℝ, z ∂retainedCutoffLaw nu b| ≤
      2 * R / (epsilon ^ 2 * a) := by
    calc
      _ = ((n : ℝ) * |∫ z : ℝ in retainedCutoffSet b, z ∂nu|) / retainedCutoffMass nu b := by
        rw [integral_retainedCutoffLaw nu b hq _ h1.restrict,
          abs_div, abs_of_pos hq]
        ring
      _ ≤ (R / (epsilon ^ 2 * a)) / retainedCutoffMass nu b :=
        div_le_div_of_nonneg_right hnumB hq.le
      _ ≤ 2 * R / (epsilon ^ 2 * a) := by
        apply (div_le_iff₀ hq).2
        have hh := mul_le_mul_of_nonneg_left
          (show 1 ≤ 2 * retainedCutoffMass nu b by linarith)
          (div_nonneg hR0 (mul_nonneg (sq_nonneg epsilon) ha.le))
        simpa only [div_eq_mul_inv, one_mul, mul_assoc, mul_comm, mul_left_comm] using hh
  have hr := st_raw_paid nu n h2 hnorm x epsilon hx hepsilon hepsilonHalf hR
  have hc := retainedCutoffLaw_centered_moments nu b hb hq h2
  dsimp only
  refine ⟨?_, hr.1, hr.2, ?_, ?_⟩
  · simpa only [hlaw] using hmu
  · simpa only [hlaw] using hc.2.2.1
  · simpa only [hlaw] using hc.2.2.2.2.2

theorem sourceTruncation_variance_bounds
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : truncationBudget nu n x ≤ epsilon ^ 3 / 8) :
    let rho : Measure ℝ :=
      ProbabilityTheory.cond nu {z | |z| ≤ epsilon / (1 + x)}
    let mu : ℝ := ∫ z : ℝ, z ∂rho
    let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
    let V : ℝ := ProbabilityTheory.variance (id : ℝ → ℝ) rho
    (3 / 4 : ℝ) ≤ (n : ℝ) * m2 ∧
      (n : ℝ) * m2 ≤ (4 / 3 : ℝ) ∧
      (n : ℝ) * mu ^ 2 ≤ (1 / 4 : ℝ) ∧
      V = m2 - mu ^ 2 ∧
      V = (∫ z : ℝ, (z - mu) ^ 2 ∂rho) ∧
      0 < V ∧ (1 / 2 : ℝ) ≤ (n : ℝ) * V ∧
      (n : ℝ) * V ≤ (4 / 3 : ℝ) := by
  let a : ℝ := 1 + x
  let b : ℝ := a / epsilon
  let rho : Measure ℝ := ProbabilityTheory.cond nu {z | |z| ≤ epsilon / a}
  let mu : ℝ := ∫ z : ℝ, z ∂rho
  let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
  let V : ℝ := ProbabilityTheory.variance (id : ℝ → ℝ) rho
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  have hb : 0 < b := div_pos ha0 hepsilon
  have he1 : epsilon ≤ 1 := by linarith
  have hp := sourceTruncation_reparameterization nu n h2 x epsilon hx hepsilon he1
  have hlaw : retainedCutoffLaw nu b = rho := hp.2.2.1
  obtain ⟨hb2, _, hn64, hH⟩ := sourceTruncation_sample_size nu n h2 hnorm x epsilon hx
    hepsilon hepsilonHalf hR
  have hn2 : 2 ≤ n := by omega
  have hN64 : (64 : ℝ) ≤ n := by exact_mod_cast hn64
  have hN0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hNp : (0 : ℝ) < n := by linarith
  obtain ⟨hlo, hhi⟩ := retainedCutoffLaw_second_moment_bounds nu n hn2 b hb h2 hnorm
    (hH.trans (by norm_num))
  rw [hlaw] at hlo hhi
  have hrawlo : (3 / 4 : ℝ) ≤ (n : ℝ) * m2 := by
    have hbSq : (4 : ℝ) ≤ b ^ 2 := by nlinarith only [hb2]
    have hh : 1 / b ^ 2 ≤ (1 / 4 : ℝ) := (div_le_iff₀ (pow_pos hb 2)).2 (by linarith)
    linarith only [hlo, hh]
  have hrawhi : (n : ℝ) * m2 ≤ (4 / 3 : ℝ) := by
    have hh : 2 / (n : ℝ) ≤ (1 / 3 : ℝ) := (div_le_iff₀ hNp).2 (by linarith)
    linarith only [hhi, hh]
  have hpaid := (sourceTruncation_paid_moments nu n h2 hnorm hmean x epsilon hx
    hepsilon hepsilonHalf hR).1
  change (n : ℝ) * |mu| ≤ 2 * truncationBudget nu n x / (epsilon ^ 2 * a) at hpaid
  have hmuSmall : (n : ℝ) * |mu| ≤ (1 / 8 : ℝ) := by
    apply hpaid.trans
    apply (div_le_iff₀ (mul_pos (pow_pos hepsilon 2) ha0)).2
    have hh := mul_le_mul_of_nonneg_left
      (show 2 * epsilon ≤ a by linarith) (sq_nonneg epsilon)
    nlinarith only [hR, hh]
  have hmuSq : (n : ℝ) * mu ^ 2 ≤ (1 / 64 : ℝ) := by
    have hh := pow_le_pow_left₀ (mul_nonneg hN0 (abs_nonneg mu)) hmuSmall 2
    have hmono := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ n by linarith)
      (mul_nonneg hN0 (sq_nonneg mu))
    rw [mul_pow, sq_abs] at hh
    nlinarith only [hh, hmono]
  obtain ⟨_, _, hprob, _, _, hsq, _, _⟩ :=
    sourceTruncation_law_data nu n h2 hnorm x epsilon hx hepsilon hepsilonHalf hR
  have instProb : IsProbabilityMeasure rho := hprob
  have hL2 : MemLp (id : ℝ → ℝ) 2 rho :=
    (memLp_two_iff_integrable_sq continuous_id.aestronglyMeasurable).2 hsq
  have hVeq : V = m2 - mu ^ 2 := by
    exact variance_eq_sub hL2
  have hq34 : (3 / 4 : ℝ) ≤ retainedCutoffMass nu b := by
    change (3 / 4 : ℝ) ≤ (nu (retainedCutoffSet b)).toReal
    rw [hp.2.1]
    exact (sourceTruncation_law_data nu n h2 hnorm x epsilon hx hepsilon hepsilonHalf hR).1
  have hq : 0 < retainedCutoffMass nu b := by linarith
  have hc := (retainedCutoffLaw_centered_moments nu b hb hq h2).2.2.2.2.1
  rw [hlaw] at hc
  have hcenter : V = ∫ z : ℝ, (z - mu) ^ 2 ∂rho := hVeq.trans hc.symm
  have hVlo : (1 / 2 : ℝ) ≤ (n : ℝ) * V := by
    rw [hVeq]
    nlinarith only [hrawlo, hmuSq]
  have hVhi : (n : ℝ) * V ≤ (4 / 3 : ℝ) := by
    rw [hVeq]
    nlinarith only [hrawhi, mul_nonneg hN0 (sq_nonneg mu)]
  have hVp : 0 < V := by
    by_contra hh
    have hh' := mul_nonpos_of_nonneg_of_nonpos hN0 (le_of_not_gt hh)
    linarith only [hVlo, hh']
  exact ⟨hrawlo, hrawhi, hmuSq.trans (by norm_num), hVeq, hcenter, hVp, hVlo, hVhi⟩

private theorem st_nearby_ratio (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hneigh : |y - x| ≤ 1 / (1 + x)) : 0 ≤ 1 + y ∧ 1 + y ≤ 2 * (1 + x) := by
  have ha : 0 < 1 + x := by linarith
  have hh : y - x ≤ 1 / (1 + x) := (le_abs_self _).trans hneigh
  have hi : 1 / (1 + x) ≤ 1 := (div_le_iff₀ ha).2 (by linarith)
  constructor <;> linarith

private theorem st_nearby_raw
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : truncationBudget nu n x ≤ epsilon ^ 3 / 8)
    (y : ℝ) (hy : 0 ≤ y) (hneigh : |y - x| ≤ 1 / (1 + x)) :
    let rho : Measure ℝ :=
      ProbabilityTheory.cond nu {z | |z| ≤ epsilon / (1 + x)}
    (1 + y) * (epsilon / (1 + x)) ≤ 2 * epsilon ∧
      (1 + y) ^ 3 * (n : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂rho) ≤
        16 * truncationBudget nu n x := by
  let a : ℝ := 1 + x
  let c : ℝ := 1 + y
  let R : ℝ := truncationBudget nu n x
  let rho : Measure ℝ := ProbabilityTheory.cond nu {z | |z| ≤ epsilon / a}
  have ha : 0 < a := by dsimp [a]; linarith
  obtain ⟨hc0, hc⟩ := st_nearby_ratio x y hx hy hneigh
  have hR0 : 0 ≤ R := truncationBudget_nonneg nu n h2 x
  have hr := (st_raw_paid nu n h2 hnorm x epsilon hx hepsilon hepsilonHalf hR).1
  have hcube : c ^ 3 * ((n : ℝ) * ∫ z : ℝ, |z| ^ 3 ∂rho) ≤ 16 * R := by
    calc
      _ ≤ c ^ 3 * (2 * R / a ^ 3) :=
        mul_le_mul_of_nonneg_left hr (pow_nonneg hc0 3)
      _ ≤ (2 * a) ^ 3 * (2 * R / a ^ 3) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc0 hc 3)
          (div_nonneg (by positivity) (pow_nonneg ha.le 3))
      _ = 16 * R := by field_simp; ring
  have hscale : c * (epsilon / a) ≤ 2 * epsilon := by
    calc
      _ ≤ (2 * a) * (epsilon / a) :=
        mul_le_mul_of_nonneg_right hc (div_nonneg hepsilon.le ha.le)
      _ = 2 * epsilon := by field_simp
  exact ⟨hscale, by simpa only [mul_assoc] using hcube⟩

theorem sourceTruncation_nearby_payment
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : truncationBudget nu n x ≤ epsilon ^ 3 / 8)
    (y : ℝ) (hy : 0 ≤ y) (hneigh : |y - x| ≤ 1 / (1 + x)) :
    let rho : Measure ℝ :=
      ProbabilityTheory.cond nu {z | |z| ≤ epsilon / (1 + x)}
    let mu : ℝ := ∫ z : ℝ, z ∂rho
    let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
    let R : ℝ := truncationBudget nu n x
    let Lambda : ℝ := (1 + y) * (n : ℝ) * |mu| +
      (1 + y) ^ 3 * (n : ℝ) * m3
    (1 + y) * (epsilon / (1 + x)) ≤ 2 * epsilon ∧
      (1 + y) ^ 3 * (n : ℝ) * m3 ≤ 16 * R ∧
      Lambda ≤ 20 * R / epsilon ^ 2 ∧
      Lambda * standardNormalTail y ≤
        (20 * Real.exp 2 * R / epsilon ^ 2) * standardNormalTail x := by
  let a : ℝ := 1 + x
  let c : ℝ := 1 + y
  let rho : Measure ℝ := ProbabilityTheory.cond nu {z | |z| ≤ epsilon / a}
  let mu : ℝ := ∫ z : ℝ, z ∂rho
  let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
  let R : ℝ := truncationBudget nu n x
  let Lambda : ℝ := c * (n : ℝ) * |mu| + c ^ 3 * (n : ℝ) * m3
  have ha : 0 < a := by dsimp [a]; linarith
  obtain ⟨hc0, hc⟩ := st_nearby_ratio x y hx hy hneigh
  have hR0 : 0 ≤ R := truncationBudget_nonneg nu n h2 x
  have hpaid := (sourceTruncation_paid_moments nu n h2 hnorm hmean x epsilon hx
    hepsilon hepsilonHalf hR).1
  have hnraw := st_nearby_raw nu n h2 hnorm x epsilon hx hepsilon hepsilonHalf hR y hy hneigh
  have hmu : c * (n : ℝ) * |mu| ≤ 4 * R / epsilon ^ 2 := by
    calc
      _ = c * ((n : ℝ) * |mu|) := by ring
      _ ≤ c * (2 * R / (epsilon ^ 2 * a)) := mul_le_mul_of_nonneg_left hpaid hc0
      _ ≤ (2 * a) * (2 * R / (epsilon ^ 2 * a)) :=
        mul_le_mul_of_nonneg_right hc (div_nonneg (by positivity)
          (mul_nonneg (sq_nonneg epsilon) ha.le))
      _ = 4 * R / epsilon ^ 2 := by field_simp; ring
  have hLambda : Lambda ≤ 20 * R / epsilon ^ 2 := by
    calc
      Lambda ≤ 4 * R / epsilon ^ 2 + 16 * R := add_le_add hmu hnraw.2
      _ ≤ 20 * R / epsilon ^ 2 := by
        apply (le_div_iff₀ (pow_pos hepsilon 2)).2
        rw [add_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hepsilon.ne')]
        have he2 : epsilon ^ 2 ≤ 1 := by nlinarith
        have hh := mul_le_mul_of_nonneg_left he2 hR0
        nlinarith only [hh]
  have htail := (standardNormalTail_local_comparison x y hx hy hneigh).2
  have hweighted : Lambda * standardNormalTail y ≤
      (20 * Real.exp 2 * R / epsilon ^ 2) * standardNormalTail x := by
    calc
      _ ≤ (20 * R / epsilon ^ 2) * standardNormalTail y :=
        mul_le_mul_of_nonneg_right hLambda (standardNormalTail_basic.2.2.1 y).1.le
      _ ≤ (20 * R / epsilon ^ 2) * (Real.exp 2 * standardNormalTail x) :=
        mul_le_mul_of_nonneg_left htail (div_nonneg (by positivity) (sq_nonneg epsilon))
      _ = _ := by ring
  exact ⟨hnraw.1, hnraw.2, hLambda, hweighted⟩

theorem sourceTruncation_clock_inputs
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonEighth : epsilon ≤ 1 / 8)
    (hR : truncationBudget nu n x ≤ epsilon ^ 3 / 8)
    (y : ℝ) (hy : 0 ≤ y) (hneigh : |y - x| ≤ 1 / (1 + x)) :
    let h : ℝ := epsilon / (1 + x)
    let rho : Measure ℝ := ProbabilityTheory.cond nu {z | |z| ≤ h}
    (1 + y) * h ≤ 1 ∧
      8 * (1 + y) ^ 2 * h ^ 2 ≤ 1 ∧
      (8 * (1 + y) ^ 2) ^ 2 * (n : ℝ) *
        (∫ z : ℝ, z ^ 4 ∂rho) ≤ (1 / 2 : ℝ) := by
  let a : ℝ := 1 + x
  let c : ℝ := 1 + y
  let h : ℝ := epsilon / a
  let rho : Measure ℝ := ProbabilityTheory.cond nu {z | |z| ≤ h}
  let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
  let m4 : ℝ := ∫ z : ℝ, z ^ 4 ∂rho
  let R : ℝ := truncationBudget nu n x
  have ha : 0 < a := by dsimp [a]; linarith
  have hc0 : 0 ≤ c := by dsimp [c]; linarith
  have hh0 : 0 ≤ h := div_nonneg hepsilon.le ha.le
  have heHalf : epsilon ≤ 1 / 2 := by linarith
  obtain ⟨hscale, hcube⟩ := st_nearby_raw nu n h2 hnorm x epsilon hx hepsilon heHalf hR y hy hneigh
  change c * h ≤ 2 * epsilon at hscale
  change c ^ 3 * (n : ℝ) * m3 ≤ 16 * R at hcube
  have hfour := (st_raw_paid nu n h2 hnorm x epsilon hx hepsilon heHalf hR).2
  change (n : ℝ) * m4 ≤ h * ((n : ℝ) * m3) at hfour
  have hstep : 8 * c ^ 2 * h ^ 2 ≤ 1 := by
    have hh := pow_le_pow_left₀ (mul_nonneg hc0 hh0) hscale 2
    have he2 := pow_le_pow_left₀ hepsilon.le hepsilonEighth 2
    norm_num at he2
    rw [mul_pow] at hh
    nlinarith only [hh, he2]
  have hcube0 : 0 ≤ c ^ 3 * ((n : ℝ) * m3) := by
    apply mul_nonneg (pow_nonneg hc0 3)
    apply mul_nonneg (Nat.cast_nonneg n)
    exact integral_nonneg (fun z => pow_nonneg (abs_nonneg z) 3)
  have hpay : (8 * c ^ 2) ^ 2 * (n : ℝ) * m4 ≤ 2048 * epsilon * R := by
    calc
      _ = (64 * c ^ 4) * ((n : ℝ) * m4) := by ring
      _ ≤ (64 * c ^ 4) * (h * ((n : ℝ) * m3)) :=
        mul_le_mul_of_nonneg_left hfour (by positivity)
      _ = 64 * ((c * h) * (c ^ 3 * ((n : ℝ) * m3))) := by ring
      _ ≤ 64 * ((2 * epsilon) * (16 * R)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul hscale (by simpa only [mul_assoc] using hcube) hcube0
          (by positivity)
      _ = 2048 * epsilon * R := by ring
  have hsmall : (8 * c ^ 2) ^ 2 * (n : ℝ) * m4 ≤ (1 / 16 : ℝ) := by
    calc
      _ ≤ 2048 * epsilon * R := hpay
      _ ≤ 256 * epsilon ^ 4 := by
        have hh := mul_le_mul_of_nonneg_left hR (show 0 ≤ 2048 * epsilon by positivity)
        nlinarith only [hh]
      _ ≤ 1 / 16 := by
        have hh := pow_le_pow_left₀ hepsilon.le hepsilonEighth 4
        norm_num at hh
        nlinarith only [hh]
  exact ⟨hscale.trans (by linarith), hstep, hsmall.trans (by norm_num)⟩

end Shao
