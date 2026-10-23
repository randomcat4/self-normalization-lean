import Shao.Probability.QuadraticCharacteristicPower
import Shao.Probability.QuadraticFullNoiseDerivatives
import Shao.Probability.SourceFourierScale

/-!
The original conditional-law consumer of highderivatives(d), and the actual
whole-plane D''/(uE)'' estimates used in supplement 3508–3518 and 3539–3547.
The remaining length and clock may be zero. Regional marked integrals and
inversion are separate obligations.
-/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

private lemma signed_power_diffs (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (m : ℕ) (σ u v : ℝ) :
    let f : ℝ → ℂ := fun r => quadraticChar ν (σ * r) v ^ m
    DifferentiableAt ℝ f u ∧ DifferentiableAt ℝ (fun r => deriv f r) u := by
  let P : Measure (Shao.Path m) := Measure.pi (fun _ : Fin m => ν)
  have hlaw (i : Fin m) : IdentDistrib (fun a : Shao.Path m => a i) (id : ℝ → ℝ) P ν := by
    refine ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [Measure.map_id] using (measurePreserving_eval (fun _ : Fin m => ν) i).map_eq
  have hp (r : ℝ) : HasDerivAt (fun t => quadraticChar ν t v ^ m)
      (deriv (fun t => quadraticChar ν t v ^ m) r) r :=
    (iid_quadraticChar_power_hasDerivAt (fun i => measurable_pi_apply i)
      (iIndepFun_pi (fun _ : Fin m => measurable_id.aemeasurable)) hlaw h2 r v).differentiableAt.hasDerivAt
  have hpp (r : ℝ) : HasDerivAt (fun t => deriv (fun s => quadraticChar ν s v ^ m) t)
      (deriv (fun t => deriv (fun s => quadraticChar ν s v ^ m) t) r) r :=
    (iid_quadraticChar_power_deriv_hasDerivAt (fun i => measurable_pi_apply i)
      (iIndepFun_pi (fun _ : Fin m => measurable_id.aemeasurable)) hlaw h2 r v).differentiableAt.hasDerivAt
  have hfirst (r : ℝ) := (hp (σ * r)).scomp r
    (by simpa using (hasDerivAt_id r).const_mul σ)
  have hsecond := ((hpp (σ * u)).scomp u
    (by simpa using (hasDerivAt_id u).const_mul σ)).const_smul σ
  exact ⟨(hfirst u).differentiableAt,
    (hsecond.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => (hfirst r).deriv)).differentiableAt⟩

theorem sourceTruncation_quadraticChar_power_global_derivatives
    (ν0 : Measure ℝ) [IsProbabilityMeasure ν0]
    (n : ℕ) (h2 : Integrable (fun a : ℝ => a ^ 2) ν0)
    (hnorm : (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1)
    (hmean : (∫ a : ℝ, a ∂ν0) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x) (he : 0 < epsilon) (hehalf : epsilon ≤ 1 / 2)
    (hbudget : Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8)
    (i : ℕ) (hi : i ≤ n) (σ u v : ℝ) (hσ : |σ| = 1) :
    let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
    let m : ℕ := n - i
    let T : ℝ := (m : ℝ) * (∫ a : ℝ, a ^ 2 ∂ρ)
    let f : ℝ → ℂ := fun r => quadraticChar ρ (σ * r) v ^ m
    DifferentiableAt ℝ f u ∧
      DifferentiableAt ℝ (fun r : ℝ => deriv f r) u ∧
      ‖f u‖ ≤ 1 ∧
      ‖deriv f u‖ ≤ 2 * Real.sqrt T ∧
      ‖deriv (fun r : ℝ => deriv f r) u‖ ≤ 3 * T := by
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
  obtain ⟨_, _, hp, _, _, h2r, _, _⟩ :=
    Shao.sourceTruncation_law_data ν0 n h2 hnorm x epsilon hx he hehalf hbudget
  have hprob : IsProbabilityMeasure ρ := hp
  let := hprob
  have hscale : (3 / 4 : ℝ) ≤ (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ρ) :=
    (Shao.sourceTruncation_variance_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget).1
  have hpaid := (Shao.sourceTruncation_paid_moments ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget).1
  have ha1 : 1 ≤ 1 + x := by linarith
  have ha : 0 < 1 + x := by linarith
  have hbias : (n : ℝ) * |∫ a : ℝ, a ∂ρ| ≤ 1 := by
    apply hpaid.trans
    apply (div_le_iff₀ (mul_pos (pow_pos he 2) ha)).2
    have hp := mul_le_mul_of_nonneg_left (show 2 * epsilon ≤ 1 + x by linarith)
      (sq_nonneg epsilon)
    nlinarith only [hbudget, hp, pow_pos he 3]
  have hd := signed_power_diffs ρ h2r (n - i) σ u v
  exact ⟨hd.1, hd.2, quadraticChar_power_global_normalized ρ h2r n (n - i)
    (by omega) hscale hbias σ u v hσ⟩

private lemma product_bounds (p q : ℝ → ℂ)
    (hp : ∀ r, HasDerivAt p (deriv p r) r)
    (hq : ∀ r, HasDerivAt q (deriv q r) r) (u A B G H : ℝ)
    (hA : 0 ≤ A) (_hG : 0 ≤ G)
    (hpp : DifferentiableAt ℝ (fun r => deriv p r) u)
    (hqq : DifferentiableAt ℝ (fun r => deriv q r) u)
    (hp0 : ‖p u‖ ≤ 1) (hp1 : ‖deriv p u‖ ≤ A)
    (hp2 : ‖deriv (fun r => deriv p r) u‖ ≤ B)
    (hq0 : ‖q u‖ ≤ 1) (hq1 : ‖deriv q u‖ ≤ G)
    (hq2 : ‖deriv (fun r => deriv q r) u‖ ≤ H) :
    DifferentiableAt ℝ (fun r => p r * q r) u ∧
      DifferentiableAt ℝ (fun r => deriv (fun s => p s * q s) r) u ∧
      ‖deriv (fun r => p r * q r) u‖ ≤ A + G ∧
      ‖deriv (fun r => deriv (fun s => p s * q s) r) u‖ ≤ B + 2 * A * G + H := by
  have hfirst (r : ℝ) : deriv (fun s => p s * q s) r = deriv p r * q r + p r * deriv q r :=
    ((hp r).mul (hq r)).deriv
  have hsecond := ((hpp.hasDerivAt.mul (hq u)).add ((hp u).mul hqq.hasDerivAt)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall hfirst)
  refine ⟨((hp u).mul (hq u)).differentiableAt, hsecond.differentiableAt, ?_, ?_⟩
  · rw [hfirst]
    calc
      _ ≤ ‖deriv p u‖ * ‖q u‖ + ‖p u‖ * ‖deriv q u‖ := by
        simpa only [norm_mul] using norm_add_le (deriv p u * q u) (p u * deriv q u)
      _ ≤ A * 1 + 1 * G := add_le_add
        (mul_le_mul hp1 hq0 (norm_nonneg _) hA)
        (mul_le_mul hp0 hq1 (norm_nonneg _) (by norm_num))
      _ = _ := by ring
  · rw [hsecond.deriv]
    calc
      _ ≤ ‖deriv (fun r => deriv p r) u‖ * ‖q u‖ +
          ‖deriv p u‖ * ‖deriv q u‖ +
          (‖deriv p u‖ * ‖deriv q u‖ + ‖p u‖ * ‖deriv (fun r => deriv q r) u‖) := by
        calc
          _ ≤ ‖deriv (fun r => deriv p r) u * q u + deriv p u * deriv q u‖ +
              ‖deriv p u * deriv q u + p u * deriv (fun r => deriv q r) u‖ := norm_add_le _ _
          _ ≤ _ := by
            simpa only [norm_mul] using add_le_add
              (norm_add_le (deriv (fun r => deriv p r) u * q u) (deriv p u * deriv q u))
              (norm_add_le (deriv p u * deriv q u) (p u * deriv (fun r => deriv q r) u))
      _ ≤ B * 1 + A * G + (A * G + 1 * H) := by
        apply add_le_add
        · apply add_le_add
          · exact (mul_le_mul_of_nonneg_left hq0 (norm_nonneg _)).trans (by simpa using hp2)
          · exact mul_le_mul hp1 hq1 (norm_nonneg _) hA
        · apply add_le_add
          · exact mul_le_mul hp1 hq1 (norm_nonneg _) hA
          · exact (mul_le_mul_of_nonneg_right hp0 (norm_nonneg _)).trans (by simpa using hq2)
      _ = _ := by ring

private lemma half_add_bound (z w : ℂ) (c : ℝ) (hz : ‖z‖ ≤ c) (hw : ‖w‖ ≤ c) :
    ‖(z + w) / 2‖ ≤ c := by
  calc
    _ = ‖z + w‖ / 2 := by simp
    _ ≤ (‖z‖ + ‖w‖) / 2 := div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ ≤ _ := by linarith

private lemma half_sub_bound (z w : ℂ) (c : ℝ) (hz : ‖z‖ ≤ c) (hw : ‖w‖ ≤ c) :
    ‖(z - w) / 2‖ ≤ c := by
  simpa only [sub_eq_add_neg] using half_add_bound z (-w) c hz (by simpa using hw)

private lemma odd_even_calculus (p q : ℝ → ℂ)
    (hp : ∀ r, HasDerivAt p (deriv p r) r)
    (hq : ∀ r, HasDerivAt q (deriv q r) r) (u c1 c2 : ℝ)
    (hpp : DifferentiableAt ℝ (fun r => deriv p r) u)
    (hqq : DifferentiableAt ℝ (fun r => deriv q r) u)
    (hp1 : ‖deriv p u‖ ≤ c1) (hq1 : ‖deriv q u‖ ≤ c1)
    (hp2 : ‖deriv (fun r => deriv p r) u‖ ≤ c2)
    (hq2 : ‖deriv (fun r => deriv q r) u‖ ≤ c2) :
    let D := fun r => (p r - q r) / 2
    let E := fun r => (p r + q r) / 2
    let W := fun r : ℝ => (r : ℂ) * E r
    DifferentiableAt ℝ D u ∧ DifferentiableAt ℝ (fun r => deriv D r) u ∧
      DifferentiableAt ℝ W u ∧ DifferentiableAt ℝ (fun r => deriv W r) u ∧
      ‖deriv (fun r => deriv D r) u‖ ≤ c2 ∧
      ‖deriv (fun r => deriv W r) u‖ ≤ 2 * c1 + |u| * c2 := by
  dsimp only
  let D := fun r => (p r - q r) / 2
  let E := fun r => (p r + q r) / 2
  let W := fun r : ℝ => (r : ℂ) * E r
  have hD (r : ℝ) : HasDerivAt D ((deriv p r - deriv q r) / 2) r :=
    ((hp r).sub (hq r)).div_const 2
  have hE (r : ℝ) : HasDerivAt E ((deriv p r + deriv q r) / 2) r :=
    ((hp r).add (hq r)).div_const 2
  have hDD : HasDerivAt (fun r => deriv D r)
      ((deriv (fun r => deriv p r) u - deriv (fun r => deriv q r) u) / 2) u :=
    (hpp.hasDerivAt.sub hqq.hasDerivAt |>.div_const 2).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => (hD r).deriv)
  have hEE : HasDerivAt (fun r => deriv E r)
      ((deriv (fun r => deriv p r) u + deriv (fun r => deriv q r) u) / 2) u :=
    (hpp.hasDerivAt.add hqq.hasDerivAt |>.div_const 2).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => (hE r).deriv)
  have hEglobal (r : ℝ) : HasDerivAt E (deriv E r) r := (hE r).differentiableAt.hasDerivAt
  have hW (r : ℝ) : HasDerivAt W (E r + (r : ℂ) * deriv E r) r := by
    convert ((hasDerivAt_id r).ofReal_comp.mul (hEglobal r)) using 1 <;> simp [W]
    funext t
    rfl
  have hWW := ((hEglobal u).add ((hasDerivAt_id u).ofReal_comp.mul
    hEE.differentiableAt.hasDerivAt)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun r => (hW r).deriv)
  refine ⟨(hD u).differentiableAt, hDD.differentiableAt, (hW u).differentiableAt,
    hWW.differentiableAt, ?_, ?_⟩
  · change ‖deriv (fun r => deriv D r) u‖ ≤ c2
    rw [hDD.deriv]
    exact half_sub_bound _ _ c2 hp2 hq2
  · have hE1 : ‖deriv E u‖ ≤ c1 := by
      rw [(hE u).deriv]
      exact half_add_bound _ _ c1 hp1 hq1
    have hE2 : ‖deriv (fun r => deriv E r) u‖ ≤ c2 := by
      rw [hEE.deriv]
      exact half_add_bound _ _ c2 hp2 hq2
    change ‖deriv (fun r => deriv W r) u‖ ≤ _
    rw [hWW.deriv]
    calc
      _ = ‖2 * deriv E u + (u : ℂ) * deriv (fun r => deriv E r) u‖ := by
        congr 1
        simp only [Complex.ofReal_one, id_eq]
        ring
      _ ≤ 2 * ‖deriv E u‖ + |u| * ‖deriv (fun r => deriv E r) u‖ := by
        simpa only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs] using
          norm_add_le (2 * deriv E u) ((u : ℂ) * deriv (fun r => deriv E r) u)
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hE1 (by norm_num))
        (mul_le_mul_of_nonneg_left hE2 (abs_nonneg u))

theorem sourceTruncation_odd_even_fullNoise_global_derivatives :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
          (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 →
          (∫ a : ℝ, a ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ i : ℕ, i ≤ n → ∀ h : ℝ, epsilon / (1 + x) ≤ h →
              let ρ : Measure ℝ :=
                ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
              let m : ℕ := n - i
              let T : ℝ := (m : ℝ) * (∫ a : ℝ, a ^ 2 ∂ρ)
              let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
              ∀ u v : ℝ,
                let D : ℝ → ℂ := fun r =>
                  ((quadraticChar ρ r v) ^ m - (quadraticChar ρ (-r) v) ^ m) /
                    2 * quadraticFullNoiseChar ρ r v
                let E : ℝ → ℂ := fun r =>
                  ((quadraticChar ρ r v) ^ m + (quadraticChar ρ (-r) v) ^ m) /
                    2 * quadraticFullNoiseChar ρ r v
                let W : ℝ → ℂ := fun r => (r : ℂ) * E r
                DifferentiableAt ℝ D u ∧
                  DifferentiableAt ℝ (fun r : ℝ => deriv D r) u ∧
                  DifferentiableAt ℝ W u ∧
                  DifferentiableAt ℝ (fun r : ℝ => deriv W r) u ∧
                  ‖deriv (fun r : ℝ => deriv D r) u‖ ≤ C * (T + h * gamma) ∧
                  ‖deriv (fun r : ℝ => deriv W r) u‖ ≤
                    C * (Real.sqrt T + gamma + |u| * (T + h * gamma)) := by
  refine ⟨120, by norm_num, ?_⟩
  intro ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h hh
  dsimp only
  intro u v
  let := hp0
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
  let m : ℕ := n - i
  let T : ℝ := (m : ℝ) * (∫ a : ℝ, a ^ 2 ∂ρ)
  let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
  let s : ℝ := Real.sqrt T
  let p : ℝ → ℂ := fun r => quadraticChar ρ r v ^ m
  let q : ℝ → ℂ := fun r => quadraticChar ρ (-r) v ^ m
  let X : ℝ → ℂ := fun r => quadraticFullNoiseChar ρ r v
  let F : ℝ → ℂ := fun r => p r * X r
  let G : ℝ → ℂ := fun r => q r * X r
  obtain ⟨_, _, hp, hs, _, h2r, h3r, _⟩ :=
    Shao.sourceTruncation_law_data ν0 n h2 hnorm x epsilon hx he hehalf hbudget
  have hprob : IsProbabilityMeasure ρ := hp
  let := hprob
  have hV : 0 < variance (id : ℝ → ℝ) ρ :=
    (Shao.sourceTruncation_variance_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget).2.2.2.2.2.1
  obtain ⟨_, hgamma, _, _, hgamcut, _, _, _, _⟩ :=
    Shao.sourceTruncation_gamma_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget
  change 0 < gamma at hgamma
  have hcut : 0 < epsilon / (1 + x) := div_pos he (by linarith)
  have hhpos : 0 < h := hcut.trans_le hh
  have hsupport : ∀ᵐ a : ℝ ∂ρ, |a| ≤ h := hs.mono fun _ ha => ha.trans hh
  have hgam : gamma ≤ 2 * h := hgamcut.trans (by linarith)
  have hT : 0 ≤ T := mul_nonneg (Nat.cast_nonneg m) (integral_nonneg fun a => sq_nonneg a)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg T
  have hs2 : s ^ 2 = T := Real.sq_sqrt hT
  have hg2 : gamma ^ 2 ≤ 2 * h * gamma := by nlinarith only [mul_le_mul_of_nonneg_right hgam hgamma.le]
  have hcross : s * gamma ≤ T / 2 + h * gamma := by
    nlinarith only [sq_nonneg (s - gamma), hs2, hg2]
  have hpower := sourceTruncation_quadraticChar_power_global_derivatives ν0 n h2 hnorm hmean
    x epsilon hx he hehalf hbudget i hi
  have hpglob (r : ℝ) : HasDerivAt p (deriv p r) r := by
    simpa only [one_mul] using (hpower 1 r v (by norm_num)).1.hasDerivAt
  have hqglob (r : ℝ) : HasDerivAt q (deriv q r) r := by
    simpa only [neg_one_mul] using (hpower (-1) r v (by norm_num)).1.hasDerivAt
  have hXglob (r : ℝ) : HasDerivAt X (deriv X r) r :=
    (quadraticFullNoiseChar_derivatives ρ h3r hV h hhpos hsupport hgam r v).1.differentiableAt.hasDerivAt
  obtain ⟨_, hpp, hp0, hp1, hp2⟩ := hpower 1 u v (by norm_num)
  obtain ⟨_, hqq, hq0, hq1, hq2⟩ := hpower (-1) u v (by norm_num)
  simp only [one_mul, neg_one_mul] at hpp hp0 hp1 hp2 hqq hq0 hq1 hq2
  have hXX := (quadraticFullNoiseChar_derivatives ρ h3r hV h hhpos hsupport hgam u v).2.1.differentiableAt
  have hX0 : ‖X u‖ ≤ 1 := (quadraticFullNoiseChar_product ρ h3r hV h hhpos hsupport u v).2.2.2
  obtain ⟨hX1, hX2⟩ := quadraticFullNoiseChar_derivative_bounds ρ h3r hV h hhpos hsupport hgam u v
  obtain ⟨_, hFF, hF1, hF2⟩ := product_bounds p X hpglob hXglob u (2 * s) (3 * T)
    ((67 / 3 : ℝ) * gamma) ((70 / 3 : ℝ) * h * gamma) (by positivity) (by positivity)
    hpp hXX hp0 hp1 hp2 hX0 hX1 hX2
  obtain ⟨_, hGG, hG1, hG2⟩ := product_bounds q X hqglob hXglob u (2 * s) (3 * T)
    ((67 / 3 : ℝ) * gamma) ((70 / 3 : ℝ) * h * gamma) (by positivity) (by positivity)
    hqq hXX hq0 hq1 hq2 hX0 hX1 hX2
  have hFglob (r : ℝ) : HasDerivAt F (deriv F r) r :=
    ((hpglob r).mul (hXglob r)).differentiableAt.hasDerivAt
  have hGglob (r : ℝ) : HasDerivAt G (deriv G r) r :=
    ((hqglob r).mul (hXglob r)).differentiableAt.hasDerivAt
  have hc1 : 2 * s + (67 / 3 : ℝ) * gamma ≤ 30 * (s + gamma) := by nlinarith only [hs0, hgamma]
  have hc2 : 3 * T + 2 * (2 * s) * ((67 / 3 : ℝ) * gamma) +
      (70 / 3 : ℝ) * h * gamma ≤ 120 * (T + h * gamma) := by
    nlinarith only [hcross, hT, mul_nonneg hhpos.le hgamma.le]
  obtain ⟨hD, hDD, hW, hWW, hD2, hW2⟩ := odd_even_calculus F G hFglob hGglob u
    (30 * (s + gamma)) (120 * (T + h * gamma)) hFF hGG
    (hF1.trans hc1) (hG1.trans hc1) (hF2.trans hc2) (hG2.trans hc2)
  have hDeq : (fun r => (F r - G r) / 2) = (fun r =>
      (quadraticChar ρ r v ^ m - quadraticChar ρ (-r) v ^ m) / 2 *
        quadraticFullNoiseChar ρ r v) := by funext r; dsimp [F, G, p, q, X]; ring
  have hWeq : (fun r : ℝ => (r : ℂ) * ((F r + G r) / 2)) = (fun r : ℝ =>
      (r : ℂ) * ((quadraticChar ρ r v ^ m + quadraticChar ρ (-r) v ^ m) / 2 *
        quadraticFullNoiseChar ρ r v)) := by funext r; dsimp [F, G, p, q, X]; ring
  rw [hDeq] at hD hDD hD2
  rw [hWeq] at hW hWW hW2
  refine ⟨hD, hDD, hW, hWW, hD2, hW2.trans ?_⟩
  change 2 * (30 * (s + gamma)) + |u| * (120 * (T + h * gamma)) ≤
    120 * (s + gamma + |u| * (T + h * gamma))
  nlinarith only [hs0, hgamma]

end Shao.Probability
