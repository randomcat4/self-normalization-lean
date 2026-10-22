import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Shao.OQ3
noncomputable section

def gaussianRateProfile (S T b y z : ℝ) : ℝ :=
  y ^ 2 / (2 * S) + (z - b * y) ^ 2 / (2 * T)

private theorem gaussianRateProfile_lower (S T b y z : ℝ) (hS : 0 < S) (hT : 0 < T) :
    (1 / (2 * T)) * z ^ 2 - (|b| / T) * |y * z| ≤ gaussianRateProfile S T b y z := by
  have ha : b * (y * z) ≤ |b| * |y * z| := by
    simpa only [abs_mul] using le_abs_self (b * (y * z))
  have hsq : z ^ 2 - 2 * |b| * |y * z| ≤ (z - b * y) ^ 2 := by
    nlinarith only [ha, sq_nonneg (b * y)]
  have hdrop : 0 ≤ y ^ 2 / (2 * S) := div_nonneg (sq_nonneg _) (by positivity)
  calc
    _ = (z ^ 2 - 2 * |b| * |y * z|) / (2 * T) := by
      field_simp [hT.ne']
    _ ≤ (z - b * y) ^ 2 / (2 * T) := div_le_div_of_nonneg_right hsq (by positivity)
    _ ≤ gaussianRateProfile S T b y z := le_add_of_nonneg_left hdrop

private theorem cubic_small_ratio_bound (u v delta d : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hdelta : 0 ≤ delta) (_hd : 0 ≤ d)
    (hdelta1 : delta ≤ 1) (hudelta : u ≤ delta) (hvdelta : v ≤ delta)
    (huquad : u ≤ d * v ^ 2) :
    (u + v) ^ 3 ≤ 4 * delta * (d + 1) * v ^ 2 := by
  have hu1 : u ≤ 1 := hudelta.trans hdelta1
  have hu2 : u ^ 2 ≤ d * v ^ 2 := by
    have hh := mul_nonneg hu (sub_nonneg.mpr hu1)
    nlinarith only [hh, huquad]
  have hsq : (u + v) ^ 2 ≤ 2 * (u ^ 2 + v ^ 2) := by
    nlinarith only [sq_nonneg (u - v)]
  calc
    (u + v) ^ 3 = (u + v) * (u + v) ^ 2 := by ring
    _ ≤ (u + v) * (2 * (u ^ 2 + v ^ 2)) :=
      mul_le_mul_of_nonneg_left hsq (add_nonneg hu hv)
    _ ≤ (2 * delta) * (2 * (u ^ 2 + v ^ 2)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (4 * delta) * (u ^ 2 + v ^ 2) := by ring
    _ ≤ (4 * delta) * ((d + 1) * v ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith only [hu2]) (by positivity)
    _ = 4 * delta * (d + 1) * v ^ 2 := by ring

theorem exists_cubic_rate_weight_margin (q ell S T b D radius : ℝ)
    (hq : 0 < q) (hell : 0 ≤ ell) (hS : 0 < S) (hT : 0 < T)
    (hD : 0 ≤ D) (hradius : 0 < radius) (hgap : ell < q / (32 * T))
    (I : ℝ → ℝ → ℝ)
    (hI : ∀ y z : ℝ, |y| + |z| ≤ radius →
      gaussianRateProfile S T b y z - D * (|y| + |z|) ^ 3 ≤ I y z) :
    ∃ delta gamma c : ℝ, 0 < delta ∧ 0 < gamma ∧ 0 < c ∧
      ∀ n : ℕ, 1 ≤ n → ∀ k r : ℝ, 0 ≤ k →
        k / (n : ℝ) ≤ delta → |r| / (n : ℝ) ≤ delta →
          (n : ℝ) * q * k / 16 ≤ r ^ 2 →
            gamma * k + c * r ^ 2 / (n : ℝ) ≤
              (n : ℝ) * I (-k / (n : ℝ)) (r / (n : ℝ)) - ell * k := by
  let A : ℝ := 1 / (2 * T)
  let d0 : ℝ := 16 / q
  let B : ℝ := |b| / T
  let g : ℝ := A - ell * d0
  let E : ℝ := B * d0 + 4 * D * (d0 + 1)
  have hd0 : 0 < d0 := div_pos (by norm_num) hq
  have hB : 0 ≤ B := div_nonneg (abs_nonneg _) hT.le
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hnum : 0 < q - 32 * T * ell := by
    have hh := (lt_div_iff₀ (show 0 < 32 * T by positivity)).mp hgap
    nlinarith only [hh]
  have hgform : g = (q - 32 * T * ell) / (2 * T * q) := by
    dsimp only [g, A, d0]
    field_simp [hq.ne', hT.ne']; ring
  have hg : 0 < g := by rw [hgform]; exact div_pos hnum (by positivity)
  let delta : ℝ := min 1 (min (radius / 2) (g / (2 * (E + 1))))
  let gamma : ℝ := g / (4 * d0)
  let c : ℝ := g / 4
  have hdelta : 0 < delta :=
    lt_min (by norm_num) (lt_min (half_pos hradius) (div_pos hg (by positivity)))
  have hgamma : 0 < gamma := div_pos hg (by positivity)
  have hc : 0 < c := div_pos hg (by norm_num)
  have hdelta1 : delta ≤ 1 := min_le_left _ _
  have hdeltaR : delta ≤ radius / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hdeltaE : delta * E ≤ g / 2 := by
    have hh : delta ≤ g / (2 * (E + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    have hh' := (le_div_iff₀ (show 0 < 2 * (E + 1) by positivity)).mp hh
    nlinarith only [hh', hdelta.le]
  refine ⟨delta, gamma, c, hdelta, hgamma, hc, ?_⟩
  intro n hn k r hk hsmallk hsmallr htail
  let N : ℝ := n
  have hN : 0 < N := by dsimp only [N]; exact_mod_cast hn
  let u : ℝ := k / N
  let v : ℝ := |r| / N
  let w : ℝ := r ^ 2 / N
  have hu : 0 ≤ u := div_nonneg hk hN.le
  have hv : 0 ≤ v := div_nonneg (abs_nonneg _) hN.le
  have hw0 : 0 ≤ w := div_nonneg (sq_nonneg _) hN.le
  have hudelta : u ≤ delta := hsmallk
  have hvdelta : v ≤ delta := hsmallr
  have hku : k = N * u := by dsimp only [u]; field_simp [hN.ne']
  have hw : w = N * v ^ 2 := by
    dsimp only [w, v]
    rw [div_pow, sq_abs]
    field_simp [hN.ne']
  have hkw : k ≤ d0 * w := by
    have hh : N * q * k ≤ r ^ 2 * 16 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 16)).mp htail
    have hh' : k ≤ (r ^ 2 * 16) / (N * q) :=
      (le_div_iff₀ (mul_pos hN hq)).mpr (by nlinarith only [hh])
    have heq : (r ^ 2 * 16) / (N * q) = d0 * w := by
      dsimp only [d0, w]
      field_simp [hN.ne', hq.ne']
    exact hh'.trans_eq heq
  have huquad : u ≤ d0 * v ^ 2 := by
    have hmul : N * u ≤ N * (d0 * v ^ 2) := by
      calc
        N * u = k := hku.symm
        _ ≤ d0 * w := hkw
        _ = N * (d0 * v ^ 2) := by rw [hw]; ring
    by_contra hbad
    have hlt := mul_lt_mul_of_pos_left (lt_of_not_ge hbad) hN
    exact (not_lt_of_ge hmul) hlt
  have hyabs : |-k / N| = u := by
    rw [neg_div, abs_neg, abs_of_nonneg (div_nonneg hk hN.le)]
  have hzabs : |r / N| = v := by rw [abs_div, abs_of_pos hN]
  have hzsq : (r / N) ^ 2 = v ^ 2 := by rw [← sq_abs (r / N), hzabs]
  have habsmul : |(-k / N) * (r / N)| = u * v := by rw [abs_mul, hyabs, hzabs]
  have hdomain : |-k / N| + |r / N| ≤ radius := by
    rw [hyabs, hzabs]
    linarith only [hudelta, hvdelta, hdeltaR]
  have hquad := gaussianRateProfile_lower S T b (-k / N) (r / N) hS hT
  rw [hzsq, habsmul] at hquad
  have hi := hI (-k / N) (r / N) hdomain
  rw [hyabs, hzabs] at hi
  have hIlower : A * v ^ 2 - B * (u * v) - D * (u + v) ^ 3 ≤ I (-k / N) (r / N) :=
    (sub_le_sub_right hquad (D * (u + v) ^ 3)).trans hi
  have hcross0 : u * v ≤ d0 * delta * v ^ 2 := by
    calc
      u * v ≤ (d0 * v ^ 2) * v := mul_le_mul_of_nonneg_right huquad hv
      _ ≤ (d0 * v ^ 2) * delta := mul_le_mul_of_nonneg_left hvdelta (by positivity)
      _ = d0 * delta * v ^ 2 := by ring
  have hcross : N * u * v ≤ d0 * delta * w := by
    calc
      N * u * v = N * (u * v) := by ring
      _ ≤ N * (d0 * delta * v ^ 2) := mul_le_mul_of_nonneg_left hcross0 hN.le
      _ = d0 * delta * w := by rw [hw]; ring
  have hcubic0 := cubic_small_ratio_bound u v delta d0 hu hv hdelta.le hd0.le
    hdelta1 hudelta hvdelta huquad
  have hcubic : N * (u + v) ^ 3 ≤ 4 * delta * (d0 + 1) * w := by
    calc
      _ ≤ N * (4 * delta * (d0 + 1) * v ^ 2) := mul_le_mul_of_nonneg_left hcubic0 hN.le
      _ = _ := by rw [hw]; ring
  have herror : B * (N * u * v) + D * (N * (u + v) ^ 3) ≤ delta * E * w := by
    calc
      _ ≤ B * (d0 * delta * w) + D * (4 * delta * (d0 + 1) * w) :=
        add_le_add (mul_le_mul_of_nonneg_left hcross hB) (mul_le_mul_of_nonneg_left hcubic hD)
      _ = delta * E * w := by dsimp only [E]; ring
  have hIn := mul_le_mul_of_nonneg_left hIlower hN.le
  have hleft : N * (A * v ^ 2 - B * (u * v) - D * (u + v) ^ 3) =
      A * w - (B * (N * u * v) + D * (N * (u + v) ^ 3)) := by rw [hw]; ring
  rw [hleft] at hIn
  have hIcost : (A - delta * E) * w ≤ N * I (-k / N) (r / N) := by
    calc
      _ = A * w - delta * E * w := by ring
      _ ≤ A * w - (B * (N * u * v) + D * (N * (u + v) ^ 3)) := sub_le_sub_left herror _
      _ ≤ N * I (-k / N) (r / N) := hIn
  have hcost : (g - delta * E) * w ≤ N * I (-k / N) (r / N) - ell * k := by
    calc
      _ = (A - delta * E) * w - ell * (d0 * w) := by dsimp only [g]; ring
      _ ≤ N * I (-k / N) (r / N) - ell * k :=
        sub_le_sub hIcost (mul_le_mul_of_nonneg_left hkw hell)
  have hfinal : gamma * k + c * w ≤ N * I (-k / N) (r / N) - ell * k := by
    calc
      _ ≤ gamma * (d0 * w) + c * w :=
        add_le_add (mul_le_mul_of_nonneg_left hkw hgamma.le) (le_refl (c * w))
      _ = (g / 2) * w := by dsimp only [gamma, c]; field_simp [hd0.ne']; ring
      _ ≤ (g - delta * E) * w := mul_le_mul_of_nonneg_right (by linarith only [hdeltaE]) hw0
      _ ≤ N * I (-k / N) (r / N) - ell * k := hcost
  simpa only [w, N, div_eq_mul_inv, mul_assoc] using hfinal

end
end Shao.OQ3
