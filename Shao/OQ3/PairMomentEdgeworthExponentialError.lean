import Shao.OQ3.PairProjectionAbsoluteMoments
import Shao.OQ3.ImaginaryRealExponentialQuadraticError

namespace Shao.OQ3
open MeasureTheory
noncomputable section

theorem pair_projection_signed_moment_bound
    (law : Measure (Fin 2 → ℝ)) (m : ℕ)
    (hM : Integrable (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m) law)
    (u v : ℝ) :
    Integrable (fun y : Fin 2 → ℝ => (u * y 0 + v * y 1) ^ m) law ∧
      |∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ m ∂law| ≤
        Real.sqrt (u ^ 2 + v ^ 2) ^ m *
          (∫ y : Fin 2 → ℝ, Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m ∂law) := by
  obtain ⟨ha, _, hb⟩ := pair_projection_absolute_moment_bound law m hM u v
  have hc : Continuous (fun y : Fin 2 → ℝ => (u * y 0 + v * y 1) ^ m) := by
    fun_prop
  have hi : Integrable (fun y : Fin 2 → ℝ => (u * y 0 + v * y 1) ^ m) law := by
    apply ha.mono' hc.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun y => by simp [Real.norm_eq_abs, abs_pow])
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ y : Fin 2 → ℝ, |(u * y 0 + v * y 1) ^ m| ∂law :=
      abs_integral_le_integral_abs
    _ ≤ _ := by simpa only [abs_pow] using hb

theorem uniform_pair_moment_edgeworth_exponential_error
    {ι : Type*} (law : ι → Measure (Fin 2 → ℝ)) (M3 M4 : ℝ)
    (hI3 : ∀ i, Integrable
      (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3) (law i))
    (hM3 : ∀ i, (∫ y : Fin 2 → ℝ,
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3 ∂law i) ≤ M3)
    (hI4 : ∀ i, Integrable
      (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 4) (law i))
    (hM4 : ∀ i, (∫ y : Fin 2 → ℝ,
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 4 ∂law i) ≤ M4) :
    let m3 : ι → ℝ → ℝ → ℝ := fun i u v =>
      ∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ 3 ∂law i
    let m4 : ι → ℝ → ℝ → ℝ := fun i u v =>
      ∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ 4 ∂law i
    let Qn : ι → ℕ → ℝ → ℝ → ℂ := fun i n u v =>
      -((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2 -
        Complex.I * (m3 i u v : ℂ) / (6 * (Real.sqrt (n : ℝ) : ℂ)) +
        ((m4 i u v - 3 * (u ^ 2 + v ^ 2) ^ 2 : ℝ) : ℂ) / (24 * (n : ℂ))
    let Pn : ι → ℕ → ℝ → ℝ → ℂ := fun i n u v =>
      Complex.exp (-((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2) *
        (1 - Complex.I * (m3 i u v : ℂ) / (6 * (Real.sqrt (n : ℝ) : ℂ)) +
          ((((m4 i u v - 3 * (u ^ 2 + v ^ 2) ^ 2) / 24 -
            (m3 i u v) ^ 2 / 72 : ℝ) : ℂ) / (n : ℂ)))
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ i, ∀ u v : ℝ,
        Real.sqrt (u ^ 2 + v ^ 2) ≤ delta * Real.sqrt (n : ℝ) →
        ‖Complex.exp (Qn i n u v) - Pn i n u v‖ ≤
          C * (Real.sqrt (u ^ 2 + v ^ 2) ^ 7 +
            Real.sqrt (u ^ 2 + v ^ 2) ^ 8 + Real.sqrt (u ^ 2 + v ^ 2) ^ 9) /
            ((n : ℝ) * Real.sqrt (n : ℝ)) * Real.exp (-(u ^ 2 + v ^ 2) / 8) := by
  intro m3 m4 Qn Pn
  let A : ℝ := |M3| + 1
  let B : ℝ := |M4| + 4
  let a : ℝ := Real.exp 1 + 4
  let d : ℝ := Real.exp 1 + 2
  let C : ℝ := a * A ^ 3 + d * B * A + B ^ 2 + 1
  let delta : ℝ := min 1 (1 / (8 * B))
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hdelta : 0 < delta := lt_min zero_lt_one (by positivity)
  have hdelta1 : delta ≤ 1 := min_le_left _ _
  have hBdelta : B * delta ≤ 1 / 8 := by
    have h := min_le_right (1 : ℝ) (1 / (8 * B))
    dsimp [delta]
    calc
      B * min 1 (1 / (8 * B)) ≤ B * (1 / (8 * B)) :=
        mul_le_mul_of_nonneg_left h hB.le
      _ = 1 / 8 := by field_simp
  refine ⟨C, delta, by dsimp [C]; positivity, hdelta, hdelta1, ?_⟩
  intro n hn i u v huv
  let S : ℝ := u ^ 2 + v ^ 2
  let r : ℝ := Real.sqrt S
  let s : ℝ := Real.sqrt (n : ℝ)
  let b : ℝ := -m3 i u v / (6 * s)
  let c : ℝ := (m4 i u v - 3 * S ^ 2) / (24 * (n : ℝ))
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = S := Real.sq_sqrt hS
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hs : 0 < s := Real.sqrt_pos.2 hn0
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hs1 : 1 ≤ s := by nlinarith
  have hsn : s ≤ (n : ℝ) := by nlinarith
  have hden : 0 < (n : ℝ) * s := mul_pos hn0 hs
  have hm3 : |m3 i u v| ≤ A * r ^ 3 := by
    have h := (pair_projection_signed_moment_bound (law i) 3 (hI3 i) u v).2
    calc
      _ ≤ r ^ 3 * M3 := h.trans (mul_le_mul_of_nonneg_left (hM3 i) (pow_nonneg hr 3))
      _ ≤ A * r ^ 3 := by
        have hM : M3 ≤ A := (le_abs_self M3).trans (by dsimp [A]; linarith)
        nlinarith [pow_nonneg hr 3]
  have hm4 : |m4 i u v| ≤ |M4| * r ^ 4 := by
    have h := (pair_projection_signed_moment_bound (law i) 4 (hI4 i) u v).2
    calc
      _ ≤ r ^ 4 * M4 := h.trans (mul_le_mul_of_nonneg_left (hM4 i) (pow_nonneg hr 4))
      _ ≤ |M4| * r ^ 4 := by nlinarith [le_abs_self M4, pow_nonneg hr 4]
  have hk : |m4 i u v - 3 * S ^ 2| ≤ B * r ^ 4 := by
    calc
      _ ≤ |m4 i u v| + |3 * S ^ 2| := abs_sub _ _
      _ ≤ B * r ^ 4 := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 3 * S ^ 2)]
        dsimp [B]
        nlinarith [sq_nonneg (r ^ 2), pow_nonneg hr 4]
  have hb0 : 0 ≤ |b| := abs_nonneg _
  have hc0 : 0 ≤ |c| := abs_nonneg _
  have hb : |b| * s ≤ A * r ^ 3 := by
    dsimp [b]
    rw [abs_div, abs_neg, abs_of_pos (mul_pos (by norm_num) hs)]
    apply (le_div_iff₀ hs).mp
    calc
      |m3 i u v| / (6 * s) ≤ (A * r ^ 3) / (6 * s) := div_le_div_of_nonneg_right hm3 (by positivity)
      _ ≤ (A * r ^ 3) / s := by
        apply div_le_div_of_nonneg_left (by positivity) hs
        nlinarith
  have hc : |c| * (n : ℝ) ≤ B * r ^ 4 := by
    dsimp [c]
    rw [abs_div, abs_of_pos (mul_pos (by norm_num) hn0)]
    apply (le_div_iff₀ hn0).mp
    calc
      |m4 i u v - 3 * S ^ 2| / (24 * (n : ℝ)) ≤ (B * r ^ 4) / (24 * (n : ℝ)) :=
        div_le_div_of_nonneg_right hk (by positivity)
      _ ≤ (B * r ^ 4) / (n : ℝ) := by
        apply div_le_div_of_nonneg_left (by positivity) hn0
        nlinarith
  have hrad : r ≤ delta * s := huv
  have hrn : r ^ 2 ≤ delta * (n : ℝ) := by
    have hsq := pow_le_pow_left₀ hr hrad 2
    have hdd : delta ^ 2 ≤ delta := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hdd) hn0.le]
  have hsmall : |c| ≤ S / 8 := by
    have hscaled : B * r ^ 4 ≤ (S / 8) * (n : ℝ) := by
      calc
        _ = (B * r ^ 2) * r ^ 2 := by ring
        _ ≤ (B * r ^ 2) * (delta * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hrn (by positivity)
        _ = (B * delta) * (r ^ 2 * (n : ℝ)) := by ring
        _ ≤ (1 / 8) * (r ^ 2 * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hBdelta (by positivity)
        _ = _ := by rw [hr2]; ring
    exact (mul_le_mul_iff_left₀ hn0).mp (hc.trans hscaled)
  have hb3 : |b| ^ 3 * ((n : ℝ) * s) ≤ A ^ 3 * r ^ 9 := by
    have h := pow_le_pow_left₀ (mul_nonneg hb0 hs.le) hb 3
    calc
      _ = (|b| * s) ^ 3 := by rw [← hs2]; ring
      _ ≤ (A * r ^ 3) ^ 3 := h
      _ = _ := by ring
  have hbc : |c| * |b| * ((n : ℝ) * s) ≤ B * A * r ^ 7 := by
    calc
      _ = (|c| * (n : ℝ)) * (|b| * s) := by ring
      _ ≤ (B * r ^ 4) * (A * r ^ 3) :=
        mul_le_mul hc hb (mul_nonneg hb0 hs.le) (by positivity)
      _ = _ := by ring
  have hc2 : c ^ 2 * ((n : ℝ) * s) ≤ B ^ 2 * r ^ 8 := by
    have h := pow_le_pow_left₀ (mul_nonneg hc0 hn0.le) hc 2
    have hsq : c ^ 2 * (n : ℝ) ^ 2 ≤ B ^ 2 * r ^ 8 := by
      simpa only [mul_pow, sq_abs, ← pow_mul] using h
    calc
      _ = (c ^ 2 * (n : ℝ)) * s := by ring
      _ ≤ (c ^ 2 * (n : ℝ)) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hsn (by positivity)
      _ = c ^ 2 * (n : ℝ) ^ 2 := by ring
      _ ≤ _ := hsq
  let G : ℝ := Real.exp (-S / 8)
  let H : ℝ := Real.exp (-S / 2)
  have hG : 0 < G := Real.exp_pos _
  have hH : 0 < H := Real.exp_pos _
  have hHG : H ≤ G := Real.exp_le_exp.mpr (by linarith)
  have hHcG : H * Real.exp |c| ≤ G := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hweight : H * (a * |b| ^ 3 + d * |c| * |b| + c ^ 2 * Real.exp |c|) ≤
      (a * |b| ^ 3 + d * |c| * |b| + c ^ 2) * G := by
    have h1 := mul_le_mul_of_nonneg_right hHG (by positivity : 0 ≤ a * |b| ^ 3 + d * |c| * |b|)
    have h2 := mul_le_mul_of_nonneg_left hHcG (sq_nonneg c)
    calc
      _ = H * (a * |b| ^ 3 + d * |c| * |b|) + c ^ 2 * (H * Real.exp |c|) := by ring
      _ ≤ G * (a * |b| ^ 3 + d * |c| * |b|) + c ^ 2 * G := add_le_add h1 h2
      _ = _ := by ring
  have hsum : (a * |b| ^ 3 + d * |c| * |b| + c ^ 2) * ((n : ℝ) * s) ≤
      C * (r ^ 7 + r ^ 8 + r ^ 9) := by
    have h1 := mul_le_mul_of_nonneg_left hb3 ha.le
    have h2 := mul_le_mul_of_nonneg_left hbc hd.le
    have hx : 0 ≤ a * A ^ 3 := by positivity
    have hy : 0 ≤ d * B * A := by positivity
    have hz : 0 ≤ B ^ 2 := sq_nonneg B
    have h7 : d * B * A ≤ C := by dsimp [C]; linarith
    have h8 : B ^ 2 ≤ C := by dsimp [C]; linarith
    have h9 : a * A ^ 3 ≤ C := by dsimp [C]; linarith
    calc
      _ = a * (|b| ^ 3 * ((n : ℝ) * s)) +
          d * (|c| * |b| * ((n : ℝ) * s)) + c ^ 2 * ((n : ℝ) * s) := by ring
      _ ≤ a * (A ^ 3 * r ^ 9) + d * (B * A * r ^ 7) + B ^ 2 * r ^ 8 :=
        add_le_add (add_le_add h1 h2) hc2
      _ = (a * A ^ 3) * r ^ 9 + (d * B * A) * r ^ 7 + B ^ 2 * r ^ 8 := by ring
      _ ≤ C * r ^ 9 + C * r ^ 7 + C * r ^ 8 :=
        add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right h9 (pow_nonneg hr 9))
          (mul_le_mul_of_nonneg_right h7 (pow_nonneg hr 7)))
          (mul_le_mul_of_nonneg_right h8 (pow_nonneg hr 8))
      _ = _ := by ring
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hsc2 : (s : ℂ) ^ 2 = (n : ℂ) := by exact_mod_cast hs2
  have hQ : Qn i n u v = -((S : ℝ) : ℂ) / 2 + ((b : ℂ) * Complex.I + (c : ℂ)) := by
    dsimp [Qn, b, c, S, s]
    push_cast
    ring
  have hP : Pn i n u v = Complex.exp (-((S : ℝ) : ℂ) / 2) *
      (1 + (b : ℂ) * Complex.I - (b : ℂ) ^ 2 / 2 + (c : ℂ)) := by
    dsimp only [Pn, b, c, S]
    congr 1
    push_cast
    dsimp only [s] at hsc hsc2 ⊢
    rw [← hsc2]
    field_simp [hsc]
    ring
  have heq : Complex.exp (Qn i n u v) - Pn i n u v =
      Complex.exp (-((S : ℝ) : ℂ) / 2) *
        (Complex.exp ((b : ℂ) * Complex.I + (c : ℂ)) -
          (1 + (b : ℂ) * Complex.I - (b : ℂ) ^ 2 / 2 + (c : ℂ))) := by
    rw [hQ, hP, Complex.exp_add]
    ring
  have hnorm : ‖Complex.exp (-((S : ℝ) : ℂ) / 2)‖ = H := by
    rw [Complex.norm_exp]
    simp [H]
  calc
    _ = H * ‖Complex.exp ((b : ℂ) * Complex.I + (c : ℂ)) -
        (1 + (b : ℂ) * Complex.I - (b : ℂ) ^ 2 / 2 + (c : ℂ))‖ := by
      rw [heq, norm_mul, hnorm]
    _ ≤ H * (a * |b| ^ 3 + d * |c| * |b| + c ^ 2 * Real.exp |c|) :=
      mul_le_mul_of_nonneg_left (imaginary_real_exponential_quadratic_error b c) hH.le
    _ ≤ (a * |b| ^ 3 + d * |c| * |b| + c ^ 2) * G := hweight
    _ ≤ (C * (r ^ 7 + r ^ 8 + r ^ 9) / ((n : ℝ) * s)) * G :=
      mul_le_mul_of_nonneg_right ((le_div_iff₀ hden).mpr hsum) hG.le
    _ = _ := rfl

end
end Shao.OQ3
