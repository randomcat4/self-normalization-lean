import Shao.C2.HalfLineTaylorSegment

noncomputable section
namespace Shao.C2.ProjectionOvershoot

def projectedFactor (u T e : ℝ) : ℝ := 1 - u * e / T
def projectionFactor (B u T e : ℝ) : ℝ := 1 - (B + u) * e / T
def projectionOvershoot (B u T e G : ℝ) : ℝ :=
  -(B - u) * projectionFactor B u T e * G
def zeroFutureRemainder (F b T e G : ℝ) : ℝ :=
  -F - (b - b ^ 2 * e / T) * G

theorem projection_factors_bounds (B u T e : ℝ) (hu : 0 < u) (huB : u ≤ B)
    (hT : 0 < T) (hsmall : B ^ 2 ≤ T / 2) (he : e < u) :
    (1 / 2 : ℝ) ≤ projectedFactor u T e ∧
      0 ≤ projectionFactor B u T e ∧
      projectionFactor B u T e ≤ 2 * (1 + |e| / Real.sqrt T) := by
  have hB : 0 ≤ B := hu.le.trans huB
  have hsum : 0 ≤ B + u := add_nonneg hB hu.le
  have hu2 : u ^ 2 ≤ B ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr huB) hsum
    nlinarith only [h]
  have hue := mul_le_mul_of_nonneg_left he.le hu.le
  have hratio : u * e / T ≤ (1 / 2 : ℝ) :=
    (div_le_iff₀ hT).2 (by nlinarith only [hue, hu2, hsmall])
  have hA : (1 / 2 : ℝ) ≤ projectedFactor u T e := by
    dsimp only [projectedFactor]
    linarith only [hratio]
  have heSum := mul_le_mul_of_nonneg_left he.le hsum
  have huBprod := mul_le_mul_of_nonneg_right huB hB
  have hcRatio : (B + u) * e / T ≤ 1 :=
    (div_le_one hT).2 (by nlinarith only [heSum, huBprod, hu2, hsmall])
  have hc : 0 ≤ projectionFactor B u T e := by
    dsimp only [projectionFactor]
    linarith only [hcRatio]
  let s := Real.sqrt T
  have hs : 0 < s := Real.sqrt_pos.2 hT
  have hs2 : s ^ 2 = T := Real.sq_sqrt hT.le
  have hBs : B ≤ s := by nlinarith only [hB, hs.le, hs2, hT, hsmall]
  have hsumS : B + u ≤ 2 * s := by linarith only [huB, hBs]
  have hneg := mul_le_mul_of_nonneg_left (neg_abs_le e) hsum
  have hcap := mul_le_mul_of_nonneg_right hsumS (abs_nonneg e)
  have hn : -(B + u) * e ≤ 2 * s * |e| := by nlinarith only [hneg, hcap]
  have hd : -(B + u) * e / T ≤ 2 * |e| / s := by
    apply (div_le_iff₀ hT).2
    calc
      _ ≤ 2 * s * |e| := hn
      _ = (2 * |e| / s) * T := by rw [← hs2]; field_simp [ne_of_gt hs] <;> ring
  refine ⟨hA, hc, ?_⟩
  change 1 - (B + u) * e / T ≤ 2 * (1 + |e| / s)
  calc
    1 - (B + u) * e / T = 1 + (-(B + u) * e / T) := by ring
    _ ≤ 1 + 2 * |e| / s := add_le_add (le_refl 1) hd
    _ ≤ (1 + 2 * |e| / s) + 1 := le_add_of_nonneg_right (by norm_num)
    _ = 2 * (1 + |e| / s) := by ring

theorem projection_factor_identity (B u T e : ℝ) :
    (B + u) * projectedFactor u T e - u * projectionFactor B u T e = B := by
  dsimp only [projectedFactor, projectionFactor]
  ring

theorem zero_future_remainder_projection_identity (F B u T e G : ℝ) :
    zeroFutureRemainder F B T e G =
      zeroFutureRemainder F u T e G + projectionOvershoot B u T e G := by
  dsimp only [zeroFutureRemainder, projectionOvershoot, projectionFactor]
  ring

theorem projected_positive_slope_budget (F u T e G : ℝ) (hF : 0 ≤ F) :
    u * projectedFactor u T e * max G 0 ≤ |zeroFutureRemainder F u T e G| := by
  by_cases hG : 0 ≤ G
  · rw [max_eq_left hG]
    have h := neg_abs_le (zeroFutureRemainder F u T e G)
    have hr : zeroFutureRemainder F u T e G = -F - u * projectedFactor u T e * G := by
      dsimp only [zeroFutureRemainder, projectedFactor]
      ring
    rw [hr] at h ⊢
    nlinarith only [h, hF]
  · have hG' : G ≤ 0 := (lt_of_not_ge hG).le
    rw [max_eq_right hG', mul_zero]
    exact abs_nonneg _

theorem projection_own_negative_budget (F B u T e G K : ℝ) (hF : 0 ≤ F)
    (hK : 0 ≤ K) (hu : 0 < u) (huB : u ≤ B) (hT : 0 < T)
    (hsmall : B ^ 2 ≤ T / 2) (he : e < u)
    (hproj : |zeroFutureRemainder F u T e G| ≤ K * u ^ 3) :
    |zeroFutureRemainder F u T e G| + max (-projectionOvershoot B u T e G) 0 ≤
        K * u * B ^ 2 ∧
      K * u * B ^ 2 ≤ K * B ^ 3 := by
  have hB : 0 ≤ B := hu.le.trans huB
  have hsum : 0 ≤ B + u := add_nonneg hB hu.le
  have hδ : 0 ≤ B - u := sub_nonneg.mpr huB
  have hc := (projection_factors_bounds B u T e hu huB hT hsmall he).2.1
  have hG0 : 0 ≤ max G 0 := le_max_right G 0
  have hslope := projected_positive_slope_budget F u T e G hF
  have hAG : projectedFactor u T e * max G 0 ≤ K * u ^ 2 := by
    refine le_of_mul_le_mul_left ?_ hu
    calc
      u * (projectedFactor u T e * max G 0) = u * projectedFactor u T e * max G 0 := by ring
      _ ≤ |zeroFutureRemainder F u T e G| := hslope
      _ ≤ K * u ^ 3 := hproj
      _ = u * (K * u ^ 2) := by ring
  have hid := projection_factor_identity B u T e
  have hcu : u * projectionFactor B u T e ≤ (B + u) * projectedFactor u T e := by
    nlinarith only [hid, hB]
  have hCG : projectionFactor B u T e * max G 0 ≤ K * u * (B + u) := by
    refine le_of_mul_le_mul_left ?_ hu
    calc
      u * (projectionFactor B u T e * max G 0) = (u * projectionFactor B u T e) * max G 0 := by ring
      _ ≤ ((B + u) * projectedFactor u T e) * max G 0 := mul_le_mul_of_nonneg_right hcu hG0
      _ = (B + u) * (projectedFactor u T e * max G 0) := by ring
      _ ≤ (B + u) * (K * u ^ 2) := mul_le_mul_of_nonneg_left hAG hsum
      _ = u * (K * u * (B + u)) := by ring
  have hO : max (-projectionOvershoot B u T e G) 0 =
      (B - u) * projectionFactor B u T e * max G 0 := by
    have hh : -projectionOvershoot B u T e G = (B - u) * projectionFactor B u T e * G := by
      dsimp only [projectionOvershoot]
      ring
    rw [hh]
    by_cases hG : 0 ≤ G
    · rw [max_eq_left (mul_nonneg (mul_nonneg hδ hc) hG), max_eq_left hG]
    · have hG' : G ≤ 0 := (lt_of_not_ge hG).le
      rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hδ hc) hG'), max_eq_right hG', mul_zero]
  constructor
  · rw [hO]
    calc
      _ = |zeroFutureRemainder F u T e G| + (B - u) * (projectionFactor B u T e * max G 0) := by ring
      _ ≤ K * u ^ 3 + (B - u) * (K * u * (B + u)) :=
        add_le_add hproj (mul_le_mul_of_nonneg_left hCG hδ)
      _ = K * u * B ^ 2 := by ring
  · have h := mul_le_mul_of_nonneg_left huB (mul_nonneg hK (sq_nonneg B))
    convert h using 1 <;> ring

end Shao.C2.ProjectionOvershoot
