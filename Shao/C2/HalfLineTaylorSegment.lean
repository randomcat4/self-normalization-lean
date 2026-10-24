import Shao.C2.CompletionFirstProfile

noncomputable section
namespace Shao.C2.HalfLineTaylorSegment

def segmentEnergy (T b θ : ℝ) : ℝ := T - θ * b ^ 2
def segmentDistance (u b θ : ℝ) : ℝ := u - θ * b
def incrementProfile (u v T b : ℝ) : ℝ := Real.exp (-(max (u - |b|) 0) * v / T)

theorem segment_energy_bounds (T b θ : ℝ) (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    0 < segmentEnergy T b θ ∧ T / 2 ≤ segmentEnergy T b θ ∧ segmentEnergy T b θ ≤ T := by
  have hb := sq_nonneg b
  have hhi := mul_le_mul_of_nonneg_right hθ1 hb
  have hlo := mul_nonneg hθ0 hb
  dsimp only [segmentEnergy]
  constructor
  · nlinarith
  · constructor <;> nlinarith

theorem segment_distance_nonneg (u b θ : ℝ) (hu : 0 < u) (hnew : 0 ≤ u - b)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    0 ≤ segmentDistance u b θ := by
  have h1 := mul_nonneg (sub_nonneg.mpr hθ1) hu.le
  have h2 := mul_nonneg hθ0 hnew
  dsimp only [segmentDistance]
  nlinarith

theorem segment_distance_pos (u b θ : ℝ) (hu : 0 < u) (hnew : 0 ≤ u - b)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    0 < segmentDistance u b θ := by
  have h1 := mul_pos (sub_pos.mpr hθ1) hu
  have h2 := mul_nonneg hθ0 hnew
  dsimp only [segmentDistance]
  nlinarith

theorem segment_profile_le_increment (u v T b θ : ℝ) (hu : 0 < u) (hv : 0 ≤ v)
    (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2) (hnew : 0 ≤ u - b)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Real.exp (-segmentDistance u b θ * v / segmentEnergy T b θ) ≤ incrementProfile u v T b := by
  have hE := segment_energy_bounds T b θ hT hsmall hθ0 hθ1
  have hU := segment_distance_nonneg u b θ hu hnew hθ0 hθ1
  have hθb : θ * b ≤ |b| := by
    have h1 := mul_le_mul_of_nonneg_left (le_abs_self b) hθ0
    have h2 := mul_le_mul_of_nonneg_right hθ1 (abs_nonneg b)
    nlinarith
  have hmax : max (u - |b|) 0 ≤ segmentDistance u b θ := by
    apply max_le
    · dsimp only [segmentDistance]
      linarith
    · exact hU
  have hnum := mul_le_mul_of_nonneg_right hmax hv
  have hdiv := (div_le_div_iff_of_pos_right hT).2 hnum
  have hden := div_le_div_of_nonneg_left (mul_nonneg hU hv) hE.1 hE.2.2
  have hratio := hdiv.trans hden
  unfold incrementProfile
  apply Real.exp_le_exp.2
  convert neg_le_neg hratio using 1 <;> ring

theorem segment_sqrt_comparison (T b θ : ℝ) (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Real.sqrt T ≤ 2 * Real.sqrt (segmentEnergy T b θ) := by
  have hE := segment_energy_bounds T b θ hT hsmall hθ0 hθ1
  have hsT := Real.sqrt_nonneg T
  have hsE := Real.sqrt_nonneg (segmentEnergy T b θ)
  have heT := Real.sq_sqrt hT.le
  have heE := Real.sq_sqrt hE.1.le
  nlinarith

theorem segment_displacement_bound (d T b θ : ℝ) (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    1 + |d - θ * b| / Real.sqrt (segmentEnergy T b θ) ≤
      3 * (1 + |d| / Real.sqrt T) := by
  have hE := segment_energy_bounds T b θ hT hsmall hθ0 hθ1
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hsE : 0 < Real.sqrt (segmentEnergy T b θ) := Real.sqrt_pos.2 hE.1
  have hs := segment_sqrt_comparison T b θ hT hsmall hθ0 hθ1
  have hInv : 1 / Real.sqrt (segmentEnergy T b θ) ≤ 2 / Real.sqrt T :=
    (div_le_div_iff₀ hsE hsT).2 (by simpa only [one_mul] using hs)
  have hb : |b| ≤ Real.sqrt T := by
    have hab := abs_nonneg b
    have he := Real.sq_sqrt hT.le
    have ha := sq_abs b
    nlinarith
  have hθb : |θ * b| ≤ |b| := by
    rw [abs_mul, abs_of_nonneg hθ0]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hθ1 (abs_nonneg b)
  have hd : |d - θ * b| ≤ |d| + Real.sqrt T := by
    have hh : |d - θ * b| ≤ |d| + |θ * b| := by
      apply abs_le.mpr
      constructor <;> linarith [le_abs_self d, neg_abs_le d,
        le_abs_self (θ * b), neg_abs_le (θ * b)]
    linarith
  have hdiv : |d - θ * b| / Real.sqrt (segmentEnergy T b θ) ≤
      (|d| + Real.sqrt T) * (2 / Real.sqrt T) := by
    calc
      _ ≤ (|d| + Real.sqrt T) / Real.sqrt (segmentEnergy T b θ) :=
        (div_le_div_iff_of_pos_right hsE).2 hd
      _ = (|d| + Real.sqrt T) * (1 / Real.sqrt (segmentEnergy T b θ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hInv (add_nonneg (abs_nonneg _) hsT.le)
  have heq : (|d| + Real.sqrt T) * (2 / Real.sqrt T) = 2 * (1 + |d| / Real.sqrt T) := by
    field_simp [ne_of_gt hsT] <;> ring
  rw [heq] at hdiv
  have hp : 0 ≤ |d| / Real.sqrt T := by positivity
  linarith

theorem segment_profile_transport (u v d T b θ : ℝ) (hu : 0 < u) (hv : 0 ≤ v)
    (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2) (hnew : 0 ≤ u - b)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (r j : ℕ) :
    (1 / Real.sqrt (segmentEnergy T b θ)) ^ r *
        (1 + |d - θ * b| / Real.sqrt (segmentEnergy T b θ)) ^ j *
          Real.exp (-segmentDistance u b θ * v / segmentEnergy T b θ) ≤
      (2 : ℝ) ^ r * (3 : ℝ) ^ j * (1 / Real.sqrt T) ^ r *
        (1 + |d| / Real.sqrt T) ^ j * incrementProfile u v T b := by
  have hE := segment_energy_bounds T b θ hT hsmall hθ0 hθ1
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hsE : 0 < Real.sqrt (segmentEnergy T b θ) := Real.sqrt_pos.2 hE.1
  have hs := segment_sqrt_comparison T b θ hT hsmall hθ0 hθ1
  have hInv : 1 / Real.sqrt (segmentEnergy T b θ) ≤ 2 / Real.sqrt T :=
    (div_le_div_iff₀ hsE hsT).2 (by simpa only [one_mul] using hs)
  have h1 := pow_le_pow_left₀ (by positivity) hInv r
  have h2 := pow_le_pow_left₀ (by positivity)
    (segment_displacement_bound d T b θ hT hsmall hθ0 hθ1) j
  have hp := segment_profile_le_increment u v T b θ hu hv hT hsmall hnew hθ0 hθ1
  have hab := mul_le_mul h1 h2 (by positivity) (by positivity)
  have hall := mul_le_mul hab hp (by positivity) (by positivity)
  convert hall using 1 <;> simp only [div_pow, mul_pow, one_pow] <;> ring

end Shao.C2.HalfLineTaylorSegment
