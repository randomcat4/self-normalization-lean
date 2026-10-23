import Shao.Probability.CenteredQuadraticCharacteristic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Actual centered characteristic powers with the six-factor gap budget. -/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

private lemma monomial_exp_bound (k : ℕ) (hk : 0 < k) (x : ℝ) (hx : 0 ≤ x) :
    x ^ k * Real.exp (-x) ≤ (k : ℝ) ^ k := by
  have hK : (0 : ℝ) < k := by exact_mod_cast hk
  have h := (Real.mul_exp_neg_le_exp_neg_one (x / (k : ℝ))).trans
    (Real.exp_le_one_iff.mpr (by norm_num : (-1 : ℝ) ≤ 0))
  have hb : x * Real.exp (-(x / (k : ℝ))) ≤ k := by
    calc
      _ = ((x / (k : ℝ)) * Real.exp (-(x / (k : ℝ)))) * k := by
        field_simp
      _ ≤ 1 * (k : ℝ) := mul_le_mul_of_nonneg_right h hK.le
      _ = _ := one_mul _
  have hp := pow_le_pow_left₀ (mul_nonneg hx (Real.exp_pos _).le) hb k
  have he : Real.exp (-(x / (k : ℝ))) ^ k = Real.exp (-x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  simpa only [mul_pow, he] using hp

private lemma gap_budget (m j k : ℕ) (hm : 16 ≤ m) (hj : j ≤ 2)
    (hk : 0 < k) (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    z ^ (m - j) * (1 - z ^ 2) ^ k ≤ (4 * (k : ℝ)) ^ k / (m : ℝ) ^ k := by
  let g : ℝ := 1 - z ^ 2
  have hg : 0 ≤ g := by dsimp [g]; nlinarith
  have hM : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmR : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have hjR : (j : ℝ) ≤ 2 := by exact_mod_cast hj
  have hN : (m : ℝ) / 2 ≤ ((m - j : ℕ) : ℝ) := by
    rw [Nat.cast_sub (show j ≤ m by omega)]
    linarith
  have hze : z ^ 2 ≤ Real.exp (-g) := by
    have h := Real.add_one_le_exp (-g)
    dsimp [g] at h
    linarith
  have hp := pow_le_pow_left₀ (sq_nonneg z) hze (m - j)
  have hs : (z ^ (m - j)) ^ 2 ≤
      (Real.exp (-((m - j : ℕ) : ℝ) * g / 2)) ^ 2 := by
    calc
      _ = (z ^ 2) ^ (m - j) := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        omega
      _ ≤ Real.exp (-g) ^ (m - j) := hp
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
  have hzN : z ^ (m - j) ≤ Real.exp (-((m - j : ℕ) : ℝ) * g / 2) := by
    nlinarith [pow_nonneg hz0 (m - j), Real.exp_pos (-((m - j : ℕ) : ℝ) * g / 2)]
  have hdec : Real.exp (-((m - j : ℕ) : ℝ) * g / 2) ≤
      Real.exp (-(m : ℝ) * g / 4) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hN hg]
  have hmono := monomial_exp_bound k hk ((m : ℝ) * g / 4) (by positivity)
  calc
    _ = z ^ (m - j) * g ^ k := rfl
    _ ≤ Real.exp (-(m : ℝ) * g / 4) * g ^ k :=
      mul_le_mul_of_nonneg_right (hzN.trans hdec) (pow_nonneg hg k)
    _ ≤ (4 * (k : ℝ)) ^ k / (m : ℝ) ^ k := by
      apply (le_div_iff₀ (pow_pos hM k)).mpr
      calc
        _ = (4 : ℝ) ^ k * (((m : ℝ) * g / 4) ^ k *
            Real.exp (-((m : ℝ) * g / 4))) := by
          simp only [mul_pow, div_pow]
          rw [show -(m : ℝ) * g / 4 = -((m : ℝ) * g / 4) by ring]
          field_simp
        _ ≤ (4 : ℝ) ^ k * (k : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
        _ = _ := (mul_pow _ _ _).symm

private lemma scalar_budgets :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 16 ≤ m → ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      let g : ℝ := 1 - z ^ 2
      z ^ m * g ^ 6 ≤ C / (m : ℝ) ^ 6 ∧
        (m : ℝ) * z ^ (m - 1) * Real.sqrt g * g ^ 6 ≤
          C * Real.sqrt (m : ℝ) / (m : ℝ) ^ 6 ∧
        ((m : ℝ) * z ^ (m - 1) * g ^ 6 +
            (m : ℝ) * ((m : ℝ) - 1) * z ^ (m - 2) * g ^ 7) ≤
          C * (m : ℝ) / (m : ℝ) ^ 6 := by
  let A : ℝ := 24 ^ 6
  let B : ℝ := 28 ^ 7
  let K : ℝ := 52 ^ 13
  let C : ℝ := A + B + K + 1
  have hA : 0 < A := by norm_num [A]
  have hB : 0 < B := by norm_num [B]
  have hK : 1 ≤ K := by norm_num [K]
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro m hm z hz0 hz1
  dsimp only
  let M : ℝ := m
  let g : ℝ := 1 - z ^ 2
  have hM : 0 < M := by dsimp [M]; exact_mod_cast (show 0 < m by omega)
  have hM1 : 1 ≤ M := by dsimp [M]; exact_mod_cast (show 1 ≤ m by omega)
  have hg : 0 ≤ g := by dsimp [g]; nlinarith
  have h0 : z ^ m * g ^ 6 ≤ A / M ^ 6 := by
    convert gap_budget m 0 6 hm (by omega) (by omega) z hz0 hz1 using 1;
      norm_num [A, M, g]
  have h1 : z ^ (m - 1) * g ^ 6 ≤ A / M ^ 6 := by
    convert gap_budget m 1 6 hm (by omega) (by omega) z hz0 hz1 using 1;
      norm_num [A, M, g]
  have h2 : z ^ (m - 2) * g ^ 7 ≤ B / M ^ 7 := by
    convert gap_budget m 2 7 hm (by omega) (by omega) z hz0 hz1 using 1;
      norm_num [B, M, g]
  have h13 : z ^ (2 * m - 2) * g ^ 13 ≤ K / M ^ 13 := by
    have h := gap_budget (2 * m) 2 13 (by omega) (by omega) (by omega) z hz0 hz1
    change z ^ (2 * m - 2) * g ^ 13 ≤ (4 * (13 : ℝ)) ^ 13 / ((2 * m : ℕ) : ℝ) ^ 13 at h
    have h' : z ^ (2 * m - 2) * g ^ 13 ≤ K / ((2 * m : ℕ) : ℝ) ^ 13 := by
      convert h using 1; norm_num [K]
    refine h'.trans ?_
    apply div_le_div_of_nonneg_left (by positivity) (pow_pos hM 13)
    apply pow_le_pow_left₀ hM.le
    dsimp [M]
    push_cast
    linarith
  have hhalf : M * z ^ (m - 1) * Real.sqrt g * g ^ 6 ≤ C * Real.sqrt M / M ^ 6 := by
    let X : ℝ := z ^ (m - 1) * Real.sqrt g * g ^ 6
    have hX : 0 ≤ X := by dsimp [X]; positivity
    have hX2 : X ^ 2 ≤ K / M ^ 13 := by
      have he : (z ^ (m - 1)) ^ 2 = z ^ (2 * m - 2) := by
        rw [← pow_mul]
        congr 1
        omega
      have hid : X ^ 2 = z ^ (2 * m - 2) * g ^ 13 := by
        dsimp [X]
        rw [mul_pow, mul_pow, Real.sq_sqrt hg, he]
        ring
      rw [hid]
      exact h13
    have hs : (M * X * M ^ 6) ^ 2 ≤ K * M := by
      calc
        _ = X ^ 2 * M ^ 14 := by ring
        _ ≤ (K / M ^ 13) * M ^ 14 :=
          mul_le_mul_of_nonneg_right hX2 (by positivity)
        _ = K * M := by field_simp
    have hKC : K ≤ C ^ 2 := by dsimp [C]; nlinarith
    have hs' : (M * X * M ^ 6) ^ 2 ≤ (C * Real.sqrt M) ^ 2 := by
      rw [show (C * Real.sqrt M) ^ 2 = C ^ 2 * M by
        rw [mul_pow, Real.sq_sqrt hM.le]]
      exact hs.trans (mul_le_mul_of_nonneg_right hKC hM.le)
    have hroot : M * X * M ^ 6 ≤ C * Real.sqrt M := by
      nlinarith [show 0 ≤ M * X * M ^ 6 by positivity,
        show 0 ≤ C * Real.sqrt M by positivity]
    apply (le_div_iff₀ (pow_pos hM 6)).mpr
    convert hroot using 1; dsimp [X]; ring
  refine ⟨h0.trans ?_, hhalf, ?_⟩
  · apply div_le_div_of_nonneg_right _ (by positivity)
    dsimp [C]
    linarith
  · have ht1 : M * z ^ (m - 1) * g ^ 6 ≤ A * M / M ^ 6 := by
      convert mul_le_mul_of_nonneg_left h1 hM.le using 1 <;> ring
    have ht2 : M * (M - 1) * z ^ (m - 2) * g ^ 7 ≤ B * M / M ^ 6 := by
      calc
        _ = (M * (M - 1)) * (z ^ (m - 2) * g ^ 7) := by ring
        _ ≤ (M * (M - 1)) * (B / M ^ 7) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ M ^ 2 * (B / M ^ 7) := by gcongr; nlinarith
        _ = _ := by field_simp
    calc
      _ ≤ A * M / M ^ 6 + B * M / M ^ 6 := add_le_add ht1 ht2
      _ ≤ C * M / M ^ 6 := by
        rw [← add_div]
        apply (div_le_div_iff_of_pos_right (pow_pos hM 6)).mpr
        dsimp [C]
        nlinarith

private lemma power_data (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (m : ℕ) (hm : 2 ≤ m) (u v : ℝ) :
    let f : ℝ → ℂ := fun r => centeredQuadraticChar ν r v ^ m
    let z : ℝ := ‖quadraticChar ν u v‖
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let g : ℝ := 1 - z ^ 2
    DifferentiableAt ℝ f u ∧ DifferentiableAt ℝ (fun r => deriv f r) u ∧
      ‖deriv f u‖ ≤ (m : ℝ) * z ^ (m - 1) * Real.sqrt V * Real.sqrt g ∧
      ‖deriv (fun r => deriv f r) u‖ ≤
        (m : ℝ) * z ^ (m - 1) * V +
          (m : ℝ) * ((m : ℝ) - 1) * z ^ (m - 2) * V * g := by
  let q : ℝ → ℂ := fun r => centeredQuadraticChar ν r v
  let z : ℝ := ‖quadraticChar ν u v‖
  let V : ℝ := variance (id : ℝ → ℝ) ν
  let g : ℝ := 1 - z ^ 2
  have hq (r : ℝ) : HasDerivAt q (deriv q r) r :=
    (centeredQuadraticChar_hasDerivAt ν h2 r v).differentiableAt.hasDerivAt
  have hqd (r : ℝ) : HasDerivAt (fun s => deriv q s)
      (deriv (fun s => deriv q s) r) r :=
    (centeredQuadraticChar_deriv_hasDerivAt ν h2 r v).differentiableAt.hasDerivAt
  have hp (r : ℝ) := (hq r).pow m
  have hd := (((hq u).pow (m - 1)).const_mul (m : ℂ)).mul (hqd u)
  have hpred : m - 1 - 1 = m - 2 := by omega
  simp only [hpred] at hd
  have hpd := hd.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => (hp r).deriv)
  have hb := centeredQuadraticChar_derivative_bounds ν h2 u v
  have hV : 0 ≤ V := variance_nonneg _ _
  have hz : 0 ≤ z := norm_nonneg _
  have hzone : z ≤ 1 := norm_quadraticChar_le_one ν u v
  have hg : 0 ≤ g := by dsimp [g]; nlinarith
  have hdsq : ‖deriv q u‖ ^ 2 ≤ V * g := by
    calc
      _ ≤ (Real.sqrt V * Real.sqrt g) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb.1 2
      _ = _ := by rw [mul_pow, Real.sq_sqrt hV, Real.sq_sqrt hg]
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_one]
  refine ⟨(hp u).differentiableAt, hpd.differentiableAt, ?_, ?_⟩
  · change ‖deriv (q ^ m) u‖ ≤ (m : ℝ) * z ^ (m - 1) * Real.sqrt V * Real.sqrt g
    rw [(hp u).deriv]
    simp only [norm_mul, Complex.norm_natCast, norm_pow]
    change (m : ℝ) * ‖centeredQuadraticChar ν u v‖ ^ (m - 1) * ‖deriv q u‖ ≤ _
    rw [norm_centeredQuadraticChar]
    convert mul_le_mul_of_nonneg_left hb.1
      (show 0 ≤ (m : ℝ) * z ^ (m - 1) by positivity) using 1 <;> ring
  · change ‖deriv (deriv (q ^ m)) u‖ ≤
      (m : ℝ) * z ^ (m - 1) * V +
        (m : ℝ) * ((m : ℝ) - 1) * z ^ (m - 2) * V * g
    rw [hpd.deriv]
    calc
      _ ≤ ‖((m : ℂ) * (((m - 1 : ℕ) : ℂ) * q u ^ (m - 2) * deriv q u)) * deriv q u‖ +
          ‖((m : ℂ) * q u ^ (m - 1)) * deriv (fun r => deriv q r) u‖ :=
        norm_add_le _ _
      _ = (m : ℝ) * ((m - 1 : ℕ) : ℝ) * z ^ (m - 2) * ‖deriv q u‖ ^ 2 +
          (m : ℝ) * z ^ (m - 1) * ‖deriv (fun r => deriv q r) u‖ := by
        simp only [norm_mul, Complex.norm_natCast, norm_pow]
        change (m : ℝ) * (((m - 1 : ℕ) : ℝ) *
          ‖centeredQuadraticChar ν u v‖ ^ (m - 2) * ‖deriv q u‖) * ‖deriv q u‖ +
          (m : ℝ) * ‖centeredQuadraticChar ν u v‖ ^ (m - 1) *
            ‖deriv (fun r => deriv q r) u‖ = _
        rw [norm_centeredQuadraticChar]
        ring
      _ ≤ (m : ℝ) * ((m - 1 : ℕ) : ℝ) * z ^ (m - 2) * (V * g) +
          (m : ℝ) * z ^ (m - 1) * V :=
        add_le_add (mul_le_mul_of_nonneg_left hdsq (by positivity))
          (mul_le_mul_of_nonneg_left hb.2 (by positivity))
      _ = _ := by rw [hcast]; ring

theorem centeredQuadraticChar_signed_power_gap_bounds :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun a : ℝ => a ^ 2) ν →
        ∀ m : ℕ, 16 ≤ m →
          ∀ σ : ℝ, |σ| = 1 → ∀ u v : ℝ,
            let g : ℝ := 1 - ‖quadraticChar ν (σ * u) v‖ ^ 2
            let S : ℝ := (m : ℝ) * variance (id : ℝ → ℝ) ν
            let f : ℝ → ℂ := fun r => (centeredQuadraticChar ν (σ * r) v) ^ m
            DifferentiableAt ℝ f u ∧
              DifferentiableAt ℝ (fun r : ℝ => deriv f r) u ∧
              ‖f u‖ * g ^ 6 ≤ C / (m : ℝ) ^ 6 ∧
              ‖deriv f u‖ * g ^ 6 ≤ C * Real.sqrt S / (m : ℝ) ^ 6 ∧
              ‖deriv (fun r : ℝ => deriv f r) u‖ * g ^ 6 ≤
                C * S / (m : ℝ) ^ 6 := by
  obtain ⟨C, hC, hscalar⟩ := scalar_budgets
  refine ⟨C, hC, ?_⟩
  intro ν hprob h2 m hm σ hσ u v
  haveI : IsProbabilityMeasure ν := hprob
  let F : ℝ → ℂ := fun r => centeredQuadraticChar ν r v ^ m
  let f : ℝ → ℂ := fun r => F (σ * r)
  let z : ℝ := ‖quadraticChar ν (σ * u) v‖
  let V : ℝ := variance (id : ℝ → ℝ) ν
  let g : ℝ := 1 - z ^ 2
  let M : ℝ := m
  have hdata (r : ℝ) := power_data ν h2 m (by omega : 2 ≤ m) r v
  have hsign (r : ℝ) : HasDerivAt f (σ • deriv F (σ * r)) r :=
    ((hdata (σ * r)).1.hasDerivAt).scomp r
      (by simpa using (hasDerivAt_id r).const_mul σ)
  have hdd := (((hdata (σ * u)).2.1.hasDerivAt).scomp u
    (by simpa using (hasDerivAt_id u).const_mul σ)).const_smul σ
  have hsdd := hdd.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => (hsign r).deriv)
  have hnormd : ‖deriv f u‖ = ‖deriv F (σ * u)‖ := by
    rw [(hsign u).deriv, norm_smul, Real.norm_eq_abs, hσ, one_mul]
  have hnormdd : ‖deriv (fun r => deriv f r) u‖ =
      ‖deriv (fun r => deriv F r) (σ * u)‖ := by
    rw [hsdd.deriv, norm_smul, norm_smul, Real.norm_eq_abs, hσ, one_mul, one_mul]
  have hg : 0 ≤ g := by
    have hz0 : 0 ≤ z := norm_nonneg _
    have hz1 : z ≤ 1 := norm_quadraticChar_le_one ν (σ * u) v
    dsimp [g]
    nlinarith
  have hV : 0 ≤ V := variance_nonneg _ _
  have hM : 0 ≤ M := Nat.cast_nonneg _
  obtain ⟨hb0, hb1, hb2⟩ := hscalar m hm z (norm_nonneg _)
    (norm_quadraticChar_le_one ν (σ * u) v)
  have hd1 := (hdata (σ * u)).2.2.1
  have hd2 := (hdata (σ * u)).2.2.2
  refine ⟨(hsign u).differentiableAt, hsdd.differentiableAt, ?_, ?_, ?_⟩
  · change ‖F (σ * u)‖ * g ^ 6 ≤ _
    simpa only [F, norm_pow, norm_centeredQuadraticChar] using hb0
  · change ‖deriv f u‖ * g ^ 6 ≤ C * Real.sqrt (M * V) / M ^ 6
    rw [hnormd]
    calc
      _ ≤ (M * z ^ (m - 1) * Real.sqrt V * Real.sqrt g) * g ^ 6 :=
        mul_le_mul_of_nonneg_right hd1 (by positivity)
      _ = (M * z ^ (m - 1) * Real.sqrt g * g ^ 6) * Real.sqrt V := by ring
      _ ≤ (C * Real.sqrt M / M ^ 6) * Real.sqrt V :=
        mul_le_mul_of_nonneg_right hb1 (Real.sqrt_nonneg V)
      _ = _ := by rw [Real.sqrt_mul hM V]; ring
  · change ‖deriv (fun r => deriv f r) u‖ * g ^ 6 ≤ C * (M * V) / M ^ 6
    rw [hnormdd]
    calc
      _ ≤ (M * z ^ (m - 1) * V + M * (M - 1) * z ^ (m - 2) * V * g) * g ^ 6 :=
        mul_le_mul_of_nonneg_right hd2 (by positivity)
      _ = (M * z ^ (m - 1) * g ^ 6 + M * (M - 1) * z ^ (m - 2) * g ^ 7) * V := by ring
      _ ≤ (C * M / M ^ 6) * V := mul_le_mul_of_nonneg_right hb2 hV
      _ = _ := by ring

end Shao.Probability
