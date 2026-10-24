import Shao.OQ6.ResidualRowExpansion
import Shao.OQ5.P35.RowIdentity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The actual uncentered remainder envelope

The finite pointwise implication in p39 (4)--(7), with the original uncentered
row square and the exact source event G. The constant 4096 is deliberately
loose. No probability estimate, localization, centered Studentizer conversion,
or original root closure is asserted. The envelope architecture is attributed
to Shao--Zhou, as in the immutable source notes.
-/

set_option autoImplicit false

namespace Shao.OQ6.ActualRemainderEnvelope

noncomputable section

open scoped BigOperators

theorem actual_uncentered_remainder_envelope
    {n : ℕ} (g : Fin n → ℝ) (r : Fin n → Fin n → ℝ)
    (hr : ∀ i j, r i j = r j i) (hn : 3 ≤ n)
    (x : ℝ) (hx : 1 ≤ x) (s : ℝ) (hs : 1 ≤ s)
    (hscale : s * x ≤ Real.sqrt (n : ℝ)) :
    let ψ : Fin n → ℝ := fun i => ∑ j ∈ Finset.univ.erase i, r i j
    let Λsq : ℝ := ∑ i : Fin n, ψ i ^ 2
    let Vsq : ℝ := (∑ i : Fin n, g i ^ 2) / (n : ℝ)
    let W : ℝ := (∑ i : Fin n, g i) / Real.sqrt (n : ℝ)
    let H : Fin n → Fin n → ℝ := fun i j => g i + g j + r i j
    let D₂ : ℝ := Shao.OQ6.FiniteRows.uncenteredSq H / Vsq - 1
    (1 / 2 : ℝ) ≤ Vsq →
      |W| ≤ Real.sqrt x * Real.sqrt (Real.sqrt (n : ℝ)) *
        (4 + Real.sqrt Vsq) →
      |D₂| ≤ 4096 * (s * x / Real.sqrt (n : ℝ) +
        Λsq / (s * x * ((n : ℝ) ^ 2 * Real.sqrt (n : ℝ)))) := by
  classical
  let N : ℝ := (n : ℝ)
  let t : ℝ := Real.sqrt N
  let ψ : Fin n → ℝ := fun i => ∑ j ∈ Finset.univ.erase i, r i j
  let Λsq : ℝ := ∑ i : Fin n, ψ i ^ 2
  let Vsq : ℝ := (∑ i : Fin n, g i ^ 2) / N
  let W : ℝ := (∑ i : Fin n, g i) / t
  let H : Fin n → Fin n → ℝ := fun i j => g i + g j + r i j
  let D₂ : ℝ := Shao.OQ6.FiniteRows.uncenteredSq H / Vsq - 1
  let V : ℝ := Real.sqrt Vsq
  let L : ℝ := Real.sqrt Λsq
  let A : ℝ := N - 1
  let B : ℝ := N - 2
  let F : ℝ := Shao.OQ5.P35.unorderedPairSum r
  let D₁ : ℝ := F / (t * A)
  let C : ℝ := ∑ i : Fin n, g i * ψ i
  change (1 / 2 : ℝ) ≤ Vsq →
    |W| ≤ Real.sqrt x * Real.sqrt t * (4 + V) →
    |D₂| ≤ 4096 * (s * x / t + Λsq / (s * x * (N ^ 2 * t)))
  intro hV hW
  have hN3 : 3 ≤ N := by
    dsimp only [N]
    exact_mod_cast hn
  have hNpos : 0 < N := by linarith only [hN3]
  have hNne : N ≠ 0 := ne_of_gt hNpos
  have hApos : 0 < A := by dsimp [A]; linarith only [hN3]
  have hBpos : 0 < B := by dsimp [B]; linarith only [hN3]
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hBne : B ≠ 0 := ne_of_gt hBpos
  have htpos : 0 < t := Real.sqrt_pos.2 hNpos
  have htne : t ≠ 0 := ne_of_gt htpos
  have htsq : t ^ 2 = N := Real.sq_sqrt hNpos.le
  have ht1 : 1 ≤ t := by
    by_contra hh
    have hprod := mul_nonneg (show 0 ≤ 1 - t by linarith)
      (show 0 ≤ 1 + t by positivity)
    nlinarith only [hprod, htsq, hN3]
  have hxpos : 0 < x := by linarith only [hx]
  have hspos : 0 < s := by linarith only [hs]
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hVpos : 0 < Vsq := by linarith only [hV]
  have hVne : Vsq ≠ 0 := ne_of_gt hVpos
  have hVrootpos : 0 < V := Real.sqrt_pos.2 hVpos
  have hVrootne : V ≠ 0 := ne_of_gt hVrootpos
  have hVsq : V ^ 2 = Vsq := Real.sq_sqrt hVpos.le
  have hΛ : 0 ≤ Λsq := Finset.sum_nonneg (fun i _ => sq_nonneg (ψ i))
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hLsq : L ^ 2 = Λsq := Real.sq_sqrt hΛ
  have hQ : (∑ i : Fin n, g i ^ 2) = N * Vsq := by
    dsimp [Vsq]
    field_simp [hNne]
  have hS : (∑ i : Fin n, g i) = t * W := by
    dsimp [W]
    field_simp [htne]
  have hF : F = t * A * D₁ := by
    dsimp [D₁]
    field_simp [htne, hAne]
    <;> ring

  -- Both Cauchy--Schwarz consequences are proved for the actual finite rows.
  have hCauchy : C ^ 2 ≤ N * Vsq * Λsq := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ g ψ
    change C ^ 2 ≤ (∑ i : Fin n, g i ^ 2) * Λsq at hh
    rw [hQ] at hh
    exact hh
  have hC : |C| ≤ t * V * L := by
    have heq : (t * V * L) ^ 2 = N * Vsq * Λsq := by
      simp only [mul_pow, htsq, hVsq, hLsq]
    have hnonneg : 0 ≤ t * V * L := by positivity
    have habs := sq_abs C
    by_contra hh
    have hp := mul_pos (show 0 < |C| - t * V * L by linarith)
      (show 0 < |C| + t * V * L by
        have := abs_nonneg C
        linarith)
    nlinarith only [hp, hCauchy, habs, heq]
  have hsumψ : (∑ i : Fin n, ψ i) = 2 * F :=
    Shao.OQ5.P35.offDiagonalSum_eq_two_unordered r hr
  have hFsq : 4 * F ^ 2 ≤ N * Λsq := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin n => (1 : ℝ)) ψ
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at hh
    change (∑ i : Fin n, ψ i) ^ 2 ≤ N * Λsq at hh
    rw [hsumψ] at hh
    nlinarith only [hh]
  have hD₁id : N * A ^ 2 * D₁ ^ 2 = F ^ 2 := by
    dsimp only [D₁]
    rw [← htsq]
    field_simp [htne, hAne]
    <;> ring
  have hD₁sq : D₁ ^ 2 ≤ Λsq / (4 * A ^ 2) := by
    apply (le_div_iff₀ (show 0 < 4 * A ^ 2 by positivity)).2
    apply (mul_le_mul_iff_right₀ hNpos).mp
    nlinarith only [hD₁id, hFsq]

  -- The uniform rational coefficients, valid also at n = 3.
  have hAlo : (2 / 3 : ℝ) * N ≤ A := by dsimp [A]; linarith only [hN3]
  have hBlo : (1 / 3 : ℝ) * N ≤ B := by dsimp [B]; linarith only [hN3]
  have hBsqlo : (1 / 9 : ℝ) * N ^ 2 ≤ B ^ 2 := by
    have hh := mul_le_mul hBlo hBlo (by positivity) hBpos.le
    nlinarith only [hh]
  have hAsqlo : (4 / 9 : ℝ) * N ^ 2 ≤ A ^ 2 := by
    have hh := mul_le_mul hAlo hAlo (by positivity) hApos.le
    nlinarith only [hh]
  have hBAlo : (2 / 9 : ℝ) * N ^ 2 ≤ B * A := by
    have hh := mul_le_mul hBlo hAlo (by positivity) hBpos.le
    nlinarith only [hh]
  have hBBAlo : (2 / 27 : ℝ) * N ^ 3 ≤ B ^ 2 * A := by
    have hh := mul_le_mul hBsqlo hAlo (by positivity) (sq_nonneg B)
    nlinarith only [hh]
  have hcoef1 : 1 / A ≤ 3 / (2 * N) := by
    apply (div_le_div_iff₀ hApos (show 0 < 2 * N by positivity)).2
    nlinarith only [hAlo]
  have hcoefW : N * (3 * N - 4) / (B ^ 2 * A) ≤ 54 / N := by
    apply (div_le_div_iff₀ (show 0 < B ^ 2 * A by positivity) hNpos).2
    have hNcube : 0 ≤ N ^ 3 := by positivity
    nlinarith only [hBBAlo, sq_nonneg N, hNcube]
  have hcoefC : 2 / (B * A) ≤ 9 / N ^ 2 := by
    apply (div_le_div_iff₀ (show 0 < B * A by positivity)
      (show 0 < N ^ 2 by positivity)).2
    nlinarith only [hBAlo]
  have hcoefD : 4 * N / B ^ 2 ≤ 36 / N := by
    apply (div_le_div_iff₀ (show 0 < B ^ 2 by positivity) hNpos).2
    nlinarith only [hBsqlo]
  have hcoefΛ : 1 / (B ^ 2 * A) ≤ (27 / 2 : ℝ) / N ^ 3 := by
    apply (div_le_div_iff₀ (show 0 < B ^ 2 * A by positivity)
      (show 0 < N ^ 3 by positivity)).2
    nlinarith only [hBBAlo]
  have hcoefD₁ : 1 / (4 * A ^ 2) ≤ 9 / (16 * N ^ 2) := by
    apply (div_le_div_iff₀ (show 0 < 4 * A ^ 2 by positivity)
      (show 0 < 16 * N ^ 2 by positivity)).2
    nlinarith only [hAsqlo]
  have hD₁sq' : D₁ ^ 2 ≤ (9 / (16 * N ^ 2)) * Λsq := by
    calc
      D₁ ^ 2 ≤ Λsq / (4 * A ^ 2) := hD₁sq
      _ = (1 / (4 * A ^ 2)) * Λsq := by ring
      _ ≤ (9 / (16 * N ^ 2)) * Λsq := mul_le_mul_of_nonneg_right hcoefD₁ hΛ

  -- Consume the accepted cleared expansion without changing the actual D₂.
  have hD₂id : Vsq * D₂ = Shao.OQ6.FiniteRows.uncenteredSq H - Vsq := by
    dsimp only [D₂]
    field_simp [hVne]
    <;> ring
  have hexpansion :
      A * Vsq * D₂ = Vsq + (N * (3 * N - 4) / B ^ 2) * W ^ 2 +
        (2 / B) * C + (4 * N * A / B ^ 2) * W * D₁ + Λsq / B ^ 2 := by
    have hh := Shao.OQ6.FiniteRows.uncenteredSq_sub_projectionSq_expansion g r hr hn
    change A * (Shao.OQ6.FiniteRows.uncenteredSq H - Vsq) =
      Vsq + ((3 * N - 4) / B ^ 2) * (∑ i : Fin n, g i) ^ 2 +
        (2 / B) * C + (4 / B ^ 2) * (∑ i : Fin n, g i) * F + Λsq / B ^ 2 at hh
    calc
      A * Vsq * D₂ = A * (Shao.OQ6.FiniteRows.uncenteredSq H - Vsq) := by
        rw [← hD₂id]
        ring
      _ = _ := hh
      _ = _ := by
        rw [hS, hF]
        ring_nf
        simp only [htsq]
        <;> ring
  let cW : ℝ := N * (3 * N - 4) / (B ^ 2 * A)
  let cC : ℝ := 2 / (B * A)
  let cD : ℝ := 4 * N / B ^ 2
  let cΛ : ℝ := 1 / (B ^ 2 * A)
  have hcW : 0 ≤ cW := by
    dsimp only [cW]
    have hthree : 0 ≤ 3 * N - 4 := by linarith only [hN3]
    exact div_nonneg (mul_nonneg hNpos.le hthree)
      (mul_nonneg (sq_nonneg B) hApos.le)
  have hcC : 0 ≤ cC := by dsimp [cC]; positivity
  have hcD : 0 ≤ cD := by dsimp [cD]; positivity
  have hcΛ : 0 ≤ cΛ := by dsimp [cΛ]; positivity
  have hDeq : D₂ = 1 / A + cW * (W ^ 2 / Vsq) + cC * (C / Vsq) +
      cD * (W * D₁ / Vsq) + cΛ * (Λsq / Vsq) := by
    apply mul_left_cancel₀ (mul_ne_zero hAne hVne)
    calc
      (A * Vsq) * D₂ = Vsq + (N * (3 * N - 4) / B ^ 2) * W ^ 2 +
          (2 / B) * C + (4 * N * A / B ^ 2) * W * D₁ + Λsq / B ^ 2 := by
        nlinarith only [hexpansion]
      _ = (A * Vsq) * (1 / A + cW * (W ^ 2 / Vsq) + cC * (C / Vsq) +
          cD * (W * D₁ / Vsq) + cΛ * (Λsq / Vsq)) := by
        dsimp only [cW, cC, cD, cΛ]
        field_simp [hAne, hBne, hVne]
        <;> ring
  have htriangle (a b c d e : ℝ) :
      |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
    have h1 := abs_add_le a b
    have h2 := abs_add_le (a + b) c
    have h3 := abs_add_le (a + b + c) d
    have h4 := abs_add_le (a + b + c + d) e
    linarith only [h1, h2, h3, h4]
  have hDabs : |D₂| ≤ 1 / A + cW * (W ^ 2 / Vsq) + cC * (|C| / Vsq) +
      cD * (|W * D₁| / Vsq) + cΛ * (Λsq / Vsq) := by
    rw [hDeq]
    refine (htriangle _ _ _ _ _).trans_eq ?_
    simp only [abs_mul, abs_div, abs_one, abs_of_nonneg hcW,
      abs_of_nonneg hcC, abs_of_nonneg hcD, abs_of_nonneg hcΛ,
      abs_of_nonneg (sq_nonneg W), abs_of_nonneg hΛ,
      abs_of_pos hApos, abs_of_pos hVpos]
  have hcoarse : |D₂| ≤ 3 / (2 * N) + (54 / N) * (W ^ 2 / Vsq) +
      (9 / N ^ 2) * (|C| / Vsq) + (36 / N) * (|W * D₁| / Vsq) +
      ((27 / 2 : ℝ) / N ^ 3) * (Λsq / Vsq) := by
    exact hDabs.trans (add_le_add (add_le_add (add_le_add (add_le_add hcoef1
      (mul_le_mul_of_nonneg_right hcoefW (by positivity)))
      (mul_le_mul_of_nonneg_right hcoefC (by positivity)))
      (mul_le_mul_of_nonneg_right hcoefD (by positivity)))
      (mul_le_mul_of_nonneg_right hcoefΛ (by positivity)))
  have hCterm : (9 / N ^ 2) * (|C| / Vsq) ≤ 9 * L / (N * t * V) := by
    calc
      (9 / N ^ 2) * (|C| / Vsq) ≤ (9 / N ^ 2) * (t * V * L / Vsq) :=
        mul_le_mul_of_nonneg_left ((div_le_div_iff_of_pos_right hVpos).2 hC)
          (by positivity)
      _ = 9 * L / (N * t * V) := by
        rw [← htsq, ← hVsq]
        field_simp [htne, hVrootne]
        <;> ring
  have hWD : |W * D₁| ≤ (W ^ 2 + D₁ ^ 2) / 2 := by
    rw [abs_mul]
    have hh := sq_nonneg (|W| - |D₁|)
    have hw := sq_abs W
    have hd := sq_abs D₁
    nlinarith only [hh, hw, hd]
  have hWD' : |W * D₁| ≤ (W ^ 2 + (9 / (16 * N ^ 2)) * Λsq) / 2 := by
    linarith only [hWD, hD₁sq']
  have hDterm : (36 / N) * (|W * D₁| / Vsq) ≤
      (18 / N) * (W ^ 2 / Vsq) + (81 / 8 : ℝ) * (Λsq / (N ^ 3 * Vsq)) := by
    calc
      (36 / N) * (|W * D₁| / Vsq) ≤
          (36 / N) * ((W ^ 2 + (9 / (16 * N ^ 2)) * Λsq) / 2 / Vsq) :=
        mul_le_mul_of_nonneg_left ((div_le_div_iff_of_pos_right hVpos).2 hWD')
          (by positivity)
      _ = _ := by field_simp [hNne, hVne]; ring
  have hsmall : |D₂| ≤ 3 / (2 * N) + 72 * W ^ 2 / (N * Vsq) +
      9 * L / (N * t * V) + 24 * Λsq / (N ^ 3 * Vsq) := by
    calc
      |D₂| ≤ 3 / (2 * N) + (54 / N) * (W ^ 2 / Vsq) +
          9 * L / (N * t * V) +
          ((18 / N) * (W ^ 2 / Vsq) + (81 / 8 : ℝ) * (Λsq / (N ^ 3 * Vsq))) +
          ((27 / 2 : ℝ) / N ^ 3) * (Λsq / Vsq) :=
        hcoarse.trans (add_le_add (add_le_add
          (add_le_add (le_refl (3 / (2 * N) + (54 / N) * (W ^ 2 / Vsq))) hCterm)
          hDterm) (le_refl (((27 / 2 : ℝ) / N ^ 3) * (Λsq / Vsq))))
      _ = 3 / (2 * N) + 72 * W ^ 2 / (N * Vsq) + 9 * L / (N * t * V) +
          (189 / 8 : ℝ) * (Λsq / (N ^ 3 * Vsq)) := by
        field_simp [hNne, htne, hVrootne, hVne]
        ring
      _ ≤ 3 / (2 * N) + 72 * W ^ 2 / (N * Vsq) + 9 * L / (N * t * V) +
          24 * Λsq / (N ^ 3 * Vsq) := by
        have hh : (189 / 8 : ℝ) * (Λsq / (N ^ 3 * Vsq)) ≤
            24 * (Λsq / (N ^ 3 * Vsq)) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        have hh' := add_le_add
          (le_refl (3 / (2 * N) + 72 * W ^ 2 / (N * Vsq) + 9 * L / (N * t * V))) hh
        simpa only [mul_div_assoc] using hh'

  -- The exact event G controls W with the fixed coefficient 49.
  have hVhalf : (1 / 2 : ℝ) ≤ V := by
    by_contra hh
    have hp := mul_nonneg (show 0 ≤ (1 / 2 : ℝ) - V by linarith)
      (show 0 ≤ (1 / 2 : ℝ) + V by positivity)
    nlinarith only [hp, hVsq, hV]
  have h4V : 4 ≤ 6 * V := by
    by_contra hh
    have hp := mul_nonneg (show 0 ≤ 4 - 6 * V by linarith)
      (show 0 ≤ 4 + 6 * V by positivity)
    nlinarith only [hp, hVsq, hV]
  have h49 : (4 + V) ^ 2 ≤ 49 * Vsq := by
    have hp := mul_nonneg (show 0 ≤ 6 * V - 4 by linarith only [h4V])
      (show 0 ≤ 8 * V + 4 by positivity)
    nlinarith only [hp, hVsq]
  have hGsq : W ^ 2 ≤ x * t * (4 + V) ^ 2 := by
    have hR : 0 ≤ Real.sqrt x * Real.sqrt t * (4 + V) := by positivity
    have hh := mul_le_mul hW hW (abs_nonneg W) hR
    have hrootx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hxpos.le
    have hroott : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt htpos.le
    calc
      W ^ 2 = |W| ^ 2 := (sq_abs W).symm
      _ ≤ (Real.sqrt x * Real.sqrt t * (4 + V)) ^ 2 := by nlinarith only [hh]
      _ = x * t * (4 + V) ^ 2 := by simp only [mul_pow, hrootx, hroott]
  have hWbound : W ^ 2 ≤ 49 * x * t * Vsq := by
    have hh := mul_le_mul_of_nonneg_left h49 (show 0 ≤ x * t by positivity)
    nlinarith only [hGsq, hh]
  have hWterm : 72 * W ^ 2 / (N * Vsq) ≤ 3528 * x / t := by
    calc
      72 * W ^ 2 / (N * Vsq) ≤ 72 * (49 * x * t * Vsq) / (N * Vsq) :=
        (div_le_div_iff_of_pos_right (show 0 < N * Vsq by positivity)).2
          (by linarith only [hWbound])
      _ = 3528 * x / t := by
        rw [← htsq]
        field_simp [htne, hVne]
        <;> ring
  have hVinv : 1 / V ≤ 2 := (div_le_iff₀ hVrootpos).2 (by linarith only [hVhalf])
  have hVsqinv : 1 / Vsq ≤ 2 := (div_le_iff₀ hVpos).2 (by linarith only [hV])
  have hCterm' : 9 * L / (N * t * V) ≤ 18 * L / (N * t) := by
    calc
      9 * L / (N * t * V) = (9 * L / (N * t)) * (1 / V) := by
        field_simp [hNne, htne, hVrootne]
        <;> ring
      _ ≤ (9 * L / (N * t)) * 2 :=
        mul_le_mul_of_nonneg_left hVinv (by positivity)
      _ = 18 * L / (N * t) := by ring
  have hΛterm : 24 * Λsq / (N ^ 3 * Vsq) ≤ 48 * Λsq / N ^ 3 := by
    calc
      24 * Λsq / (N ^ 3 * Vsq) = (24 * Λsq / N ^ 3) * (1 / Vsq) := by
        field_simp [hNne, hVne]
        <;> ring
      _ ≤ (24 * Λsq / N ^ 3) * 2 :=
        mul_le_mul_of_nonneg_left hVsqinv (by positivity)
      _ = 48 * Λsq / N ^ 3 := by ring
  have hbase : 3 / (2 * N) ≤ 2 * x / t := by
    have hxt : 1 ≤ x * t := by
      have hp := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr ht1)
      nlinarith only [hp, hx, ht1]
    apply (div_le_iff₀ (show 0 < 2 * N by positivity)).2
    calc
      3 ≤ 4 * x * t := by linarith only [hxt]
      _ = (2 * x / t) * (2 * N) := by
        rw [← htsq]
        field_simp [htne]
        <;> ring

  -- Young absorption keeps the literal source denominator s*x*N^(5/2).
  let u : ℝ := s * x / t
  let y : ℝ := L / (N * t)
  let z : ℝ := Λsq / (s * x * (N ^ 2 * t))
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    apply (div_le_iff₀ htpos).2
    change s * x ≤ 1 * t
    simpa only [one_mul] using hscale
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hy2 : y ^ 2 = Λsq / N ^ 3 := by
    dsimp only [y]
    rw [← hLsq, ← htsq]
    field_simp [htne]
    <;> ring
  have huz : u * z = y ^ 2 := by
    dsimp only [u, z, y]
    rw [← hLsq, ← htsq]
    field_simp [hsne, hxne, htne]
    <;> ring
  have hYoung : 18 * y ≤ 9 * u + 9 * z := by
    have hp := sq_nonneg (y - u)
    have hh : 2 * y ≤ u + z := (mul_le_mul_iff_right₀ hu).mp
      (show u * (2 * y) ≤ u * (u + z) by nlinarith only [hp, huz])
    linarith only [hh]
  have hy2le : y ^ 2 ≤ z := by
    have hh := mul_le_mul_of_nonneg_right hu1 hz
    nlinarith only [hh, huz]
  have hxu : x / t ≤ u := by
    apply (div_le_div_iff_of_pos_right htpos).2
    have hh := mul_nonneg (sub_nonneg.mpr hs) hxpos.le
    nlinarith only [hh]
  have hrough : |D₂| ≤ 3530 * x / t + 18 * y + 48 * y ^ 2 := by
    calc
      |D₂| ≤ 2 * x / t + 3528 * x / t + 18 * L / (N * t) + 48 * Λsq / N ^ 3 :=
        hsmall.trans (add_le_add (add_le_add (add_le_add hbase hWterm) hCterm') hΛterm)
      _ = 3530 * x / t + 18 * y + 48 * y ^ 2 := by
        rw [hy2]
        dsimp only [y]
        ring
  have hmain : |D₂| ≤ 3539 * u + 57 * z := by
    have hh := mul_le_mul_of_nonneg_left hxu (show (0 : ℝ) ≤ 3530 by norm_num)
    have hscaled : 3530 * x / t ≤ 3530 * u := by
      simpa only [mul_div_assoc] using hh
    have hscaled48 : 48 * y ^ 2 ≤ 48 * z :=
      mul_le_mul_of_nonneg_left hy2le (by norm_num)
    calc
      |D₂| ≤ 3530 * x / t + 18 * y + 48 * y ^ 2 := hrough
      _ ≤ 3530 * u + (9 * u + 9 * z) + 48 * z :=
        add_le_add (add_le_add hscaled hYoung) hscaled48
      _ = 3539 * u + 57 * z := by ring
  change |D₂| ≤ 4096 * (u + z)
  nlinarith only [hmain, hu.le, hz]

end

end Shao.OQ6.ActualRemainderEnvelope
