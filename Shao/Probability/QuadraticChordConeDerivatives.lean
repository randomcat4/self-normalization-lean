import Shao.Probability.QuadraticChordNoise
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

private noncomputable def kernel (d t : ℝ) : ℝ :=
  (1 - Real.cos (d * t)) / t ^ 2

private noncomputable def kernel1 (d t : ℝ) : ℝ :=
  d * Real.sin (d * t) / t ^ 2 - 2 * (1 - Real.cos (d * t)) / t ^ 3

private noncomputable def kernel2 (d t : ℝ) : ℝ :=
  d ^ 2 * Real.cos (d * t) / t ^ 2 - 4 * d * Real.sin (d * t) / t ^ 3 +
    6 * (1 - Real.cos (d * t)) / t ^ 4

private lemma cos_gap_bounds (x : ℝ) :
    0 ≤ 1 - Real.cos x ∧ 1 - Real.cos x ≤ x ^ 2 / 2 := by
  refine ⟨sub_nonneg.mpr (Real.cos_le_one x), ?_⟩
  have hs := Real.abs_sin_le_abs (x := x / 2)
  have hc := Real.sin_sq_eq_half_sub (x / 2)
  rw [show 2 * (x / 2) = x by ring] at hc
  nlinarith [sq_abs (Real.sin (x / 2)), sq_abs (x / 2),
    mul_nonneg (sub_nonneg.mpr hs)
      (add_nonneg (abs_nonneg (x / 2)) (abs_nonneg (Real.sin (x / 2))))]

private lemma kernel_bound (d t : ℝ) : |kernel d t| ≤ d ^ 2 / 2 := by
  by_cases ht : t = 0
  · simp only [kernel, ht, mul_zero, Real.cos_zero, sub_self, zero_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, div_zero, abs_zero]
    positivity
  · obtain ⟨hn, hb⟩ := cos_gap_bounds (d * t)
    rw [kernel, abs_of_nonneg (div_nonneg hn (sq_nonneg t))]
    apply (div_le_iff₀ (sq_pos_of_ne_zero ht)).mpr
    nlinarith [hb]

private lemma sine_term_bound (d t : ℝ) (ht : t ≠ 0) :
    |d * Real.sin (d * t) / t ^ 2| ≤ d ^ 2 / |t| := by
  have hat : 0 < |t| := abs_pos.mpr ht
  have hs : |d * Real.sin (d * t)| ≤ d ^ 2 * |t| := by
    calc
      _ = |d| * |Real.sin (d * t)| := abs_mul _ _
      _ ≤ |d| * |d * t| := mul_le_mul_of_nonneg_left
        (Real.abs_sin_le_abs (x := d * t)) (abs_nonneg d)
      _ = _ := by rw [abs_mul, ← mul_assoc, ← pow_two, sq_abs d]
  rw [abs_div, abs_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hat)).mpr
  calc
    _ ≤ d ^ 2 * |t| := hs
    _ = d ^ 2 / |t| * |t| ^ 2 := by field_simp

private lemma rational_bounds (d t : ℝ) (ht : t ≠ 0) :
    |kernel1 d t| ≤ 2 * d ^ 2 / |t| ∧
      |kernel2 d t| ≤ 8 * d ^ 2 / t ^ 2 := by
  have hat : 0 < |t| := abs_pos.mpr ht
  have hs := sine_term_bound d t ht
  have hk := kernel_bound d t
  have he1 : 2 * (1 - Real.cos (d * t)) / t ^ 3 = 2 * kernel d t / t := by
    unfold kernel
    field_simp
  have he2 : 4 * d * Real.sin (d * t) / t ^ 3 =
      4 * (d * Real.sin (d * t) / t ^ 2) / t := by
    field_simp
  have he3 : 6 * (1 - Real.cos (d * t)) / t ^ 4 = 6 * kernel d t / t ^ 2 := by
    unfold kernel
    field_simp
  have hb1 : |2 * kernel d t / t| ≤ d ^ 2 / |t| := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (by linarith only [hk]) hat.le
  have hb2 : |d ^ 2 * Real.cos (d * t) / t ^ 2| ≤ d ^ 2 / t ^ 2 := by
    rw [abs_div, abs_mul, abs_pow, sq_abs, abs_pow, sq_abs]
    exact div_le_div_of_nonneg_right
      (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (d * t)) (sq_nonneg d)) (sq_nonneg t)
  have hb3 : |4 * (d * Real.sin (d * t) / t ^ 2) / t| ≤ 4 * d ^ 2 / t ^ 2 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    calc
      _ ≤ 4 * (d ^ 2 / |t|) / |t| :=
        div_le_div_of_nonneg_right (by linarith only [hs]) hat.le
      _ = _ := by rw [← sq_abs t]; field_simp
  have hb4 : |6 * kernel d t / t ^ 2| ≤ 3 * d ^ 2 / t ^ 2 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6), abs_pow, sq_abs]
    exact div_le_div_of_nonneg_right (by linarith only [hk]) (sq_nonneg t)
  constructor
  · unfold kernel1
    rw [he1]
    calc
      _ ≤ |d * Real.sin (d * t) / t ^ 2| + |2 * kernel d t / t| := abs_sub _ _
      _ ≤ d ^ 2 / |t| + d ^ 2 / |t| := add_le_add hs hb1
      _ = _ := by ring
  · unfold kernel2
    rw [he2, he3]
    calc
      _ ≤ |d ^ 2 * Real.cos (d * t) / t ^ 2 -
          4 * (d * Real.sin (d * t) / t ^ 2) / t| + |6 * kernel d t / t ^ 2| := abs_add_le _ _
      _ ≤ |d ^ 2 * Real.cos (d * t) / t ^ 2| +
          |4 * (d * Real.sin (d * t) / t ^ 2) / t| + |6 * kernel d t / t ^ 2| :=
        add_le_add (abs_sub _ _) le_rfl
      _ ≤ d ^ 2 / t ^ 2 + 4 * d ^ 2 / t ^ 2 + 3 * d ^ 2 / t ^ 2 :=
        add_le_add (add_le_add hb2 hb3) hb4
      _ = _ := by ring

private lemma kernel_hasDerivAt (d c r : ℝ) (hr : r + c ≠ 0) :
    HasDerivAt (fun u : ℝ => kernel d (u + c)) (kernel1 d (r + c)) r := by
  have ht := (hasDerivAt_id r).add_const c
  have hp := ht.const_mul d
  convert ((hasDerivAt_const r (1 : ℝ)).sub hp.cos).div (ht.pow 2)
    (pow_ne_zero 2 hr) using 1
  · rfl
  · dsimp [kernel1]
    field_simp
    ring

private lemma kernel1_hasDerivAt (d c r : ℝ) (hr : r + c ≠ 0) :
    HasDerivAt (fun u : ℝ => kernel1 d (u + c)) (kernel2 d (r + c)) r := by
  have ht := (hasDerivAt_id r).add_const c
  have hp := ht.const_mul d
  convert (((hp.sin.const_mul d).div (ht.pow 2) (pow_ne_zero 2 hr)).sub
    ((((hasDerivAt_const r (1 : ℝ)).sub hp.cos).const_mul 2).div
      (ht.pow 3) (pow_ne_zero 3 hr))) using 1
  · rfl
  · dsimp [kernel2]
    field_simp
    ring

private lemma pair_support (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ℝ) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) :
    ∀ᵐ p : ℝ × ℝ ∂ν.prod ν, |p.1| ≤ h ∧ |p.2| ≤ h := by
  apply (Measure.ae_prod_iff_ae_ae (p := fun p : ℝ × ℝ => |p.1| ≤ h ∧ |p.2| ≤ h)
    ((measurableSet_le (f := fun p : ℝ × ℝ => |p.1|) (g := fun _ => h)
      (by fun_prop) measurable_const).inter
      (measurableSet_le (f := fun p : ℝ × ℝ => |p.2|) (g := fun _ => h)
        (by fun_prop) measurable_const))).mpr
  filter_upwards [hs] with a ha
  filter_upwards [hs] with b hb
  exact ⟨ha, hb⟩

private lemma phase_cone_lower (a b h u v : ℝ) (hh : 0 < h)
    (ha : |a| ≤ h) (hb : |b| ≤ h) (hv : |v| ≤ |u| / (4 * h)) :
    |u| / 2 ≤ |u + v * (a + b)| := by
  have hab : |a + b| ≤ 2 * h := by linarith [abs_add_le a b]
  have hp : |v * (a + b)| ≤ |u| / 2 := by
    calc
      _ = |v| * |a + b| := abs_mul _ _
      _ ≤ (|u| / (4 * h)) * (2 * h) :=
        mul_le_mul hv hab (abs_nonneg _) (by positivity)
      _ = _ := by field_simp; ring
  have hr := abs_sub (u + v * (a + b)) (v * (a + b))
  rw [add_sub_cancel_right] at hr
  linarith

private lemma phase_local_lower (a b h u v r : ℝ) (hh : 0 < h)
    (ha : |a| ≤ h) (hb : |b| ≤ h) (_hu : u ≠ 0)
    (hv : |v| ≤ |u| / (4 * h)) (hr : r ∈ Metric.ball u (|u| / 4)) :
    |u| / 4 ≤ |r + v * (a + b)| := by
  have hl := phase_cone_lower a b h u v hh ha hb hv
  have hd : |u - r| < |u| / 4 := by
    simpa only [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hr
  have ht := abs_add_le (r + v * (a + b)) (u - r)
  rw [show r + v * (a + b) + (u - r) = u + v * (a + b) by ring] at ht
  linarith

theorem quadraticChordChar_cone_derivatives
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h)
    (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (u0 v0 : ℝ) (hu : u0 ≠ 0)
    (hv : |v0| ≤ |u0| / (4 * h)) :
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let D : ℝ × ℝ → ℝ := fun p => p.1 - p.2
    let theta : ℝ × ℝ → ℝ := fun p => u0 + v0 * (p.1 + p.2)
    let Q1 : ℝ × ℝ → ℝ := fun p =>
      D p * Real.sin (D p * theta p) / theta p ^ 2 -
        2 * (1 - Real.cos (D p * theta p)) / theta p ^ 3
    let Q2 : ℝ × ℝ → ℝ := fun p =>
      D p ^ 2 * Real.cos (D p * theta p) / theta p ^ 2 -
        4 * D p * Real.sin (D p * theta p) / theta p ^ 3 +
        6 * (1 - Real.cos (D p * theta p)) / theta p ^ 4
    let d1 : ℂ := (((∫ p : ℝ × ℝ, Q1 p ∂ν.prod ν) / V : ℝ) : ℂ)
    let d2 : ℂ := (((∫ p : ℝ × ℝ, Q2 p ∂ν.prod ν) / V : ℝ) : ℂ)
    Integrable Q1 (ν.prod ν) ∧
    Integrable Q2 (ν.prod ν) ∧
    HasDerivAt (fun u : ℝ => quadraticChordChar ν u v0) d1 u0 ∧
    HasDerivAt
      (fun u : ℝ => deriv (fun r : ℝ => quadraticChordChar ν r v0) u)
      d2 u0 ∧
    deriv (fun u : ℝ => quadraticChordChar ν u v0) u0 = d1 ∧
    deriv
      (fun u : ℝ => deriv (fun r : ℝ => quadraticChordChar ν r v0) u) u0 = d2 := by
  let V : ℝ := variance (id : ℝ → ℝ) ν
  let F0 : ℝ → ℝ × ℝ → ℝ := fun u p => kernel (p.1 - p.2) (u + v0 * (p.1 + p.2))
  let F1 : ℝ → ℝ × ℝ → ℝ := fun u p => kernel1 (p.1 - p.2) (u + v0 * (p.1 + p.2))
  let F2 : ℝ → ℝ × ℝ → ℝ := fun u p => kernel2 (p.1 - p.2) (u + v0 * (p.1 + p.2))
  let s : Set ℝ := Metric.ball u0 (|u0| / 4)
  have ha : 0 < |u0| := abs_pos.mpr hu
  have hmem : u0 ∈ s := Metric.mem_ball_self (by positivity)
  have hopen : IsOpen s := Metric.isOpen_ball
  have hp := pair_support ν h hs
  have hD := (quadratic_pair_square_moment ν h3).1
  have hloc : ∀ᵐ p : ℝ × ℝ ∂ν.prod ν, ∀ u ∈ s,
      |u0| / 4 ≤ |u + v0 * (p.1 + p.2)| := by
    filter_upwards [hp] with p hp
    intro u hs
    exact phase_local_lower p.1 p.2 h u0 v0 u hh hp.1 hp.2 hu hv hs
  have hzero : ∀ᵐ p : ℝ × ℝ ∂ν.prod ν, ∀ u ∈ s,
      u + v0 * (p.1 + p.2) ≠ 0 := by
    filter_upwards [hloc] with p hp
    intro u hs hz
    have hb := hp u hs
    rw [hz, abs_zero] at hb
    linarith
  have hM0 (u : ℝ) : Measurable (F0 u) := by dsimp [F0, kernel]; fun_prop
  have hM1 (u : ℝ) : Measurable (F1 u) := by dsimp [F1, kernel1]; fun_prop
  have hM2 (u : ℝ) : Measurable (F2 u) := by dsimp [F2, kernel2]; fun_prop
  have hF0 (u : ℝ) : Integrable (F0 u) (ν.prod ν) := by
    refine (hD.div_const 2).mono' (hM0 u).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs, F0] using kernel_bound (p.1 - p.2) (u + v0 * (p.1 + p.2))
  have hb1 : ∀ᵐ p : ℝ × ℝ ∂ν.prod ν, ∀ u ∈ s,
      ‖F1 u p‖ ≤ 8 * (p.1 - p.2) ^ 2 / |u0| := by
    filter_upwards [hloc, hzero] with p hp hz
    intro u hs
    have hb := (rational_bounds (p.1 - p.2) (u + v0 * (p.1 + p.2)) (hz u hs)).1
    have hat : 0 < |u + v0 * (p.1 + p.2)| := abs_pos.mpr (hz u hs)
    change |kernel1 (p.1 - p.2) (u + v0 * (p.1 + p.2))| ≤ _
    exact hb.trans ((div_le_div_iff₀ hat ha).mpr (by
      nlinarith [mul_nonneg (sq_nonneg (p.1 - p.2)) (sub_nonneg.mpr (hp u hs))]))
  have hb2 : ∀ᵐ p : ℝ × ℝ ∂ν.prod ν, ∀ u ∈ s,
      ‖F2 u p‖ ≤ 128 * (p.1 - p.2) ^ 2 / u0 ^ 2 := by
    filter_upwards [hloc, hzero] with p hp hz
    intro u hs
    have hb := (rational_bounds (p.1 - p.2) (u + v0 * (p.1 + p.2)) (hz u hs)).2
    have hsq : u0 ^ 2 / 16 ≤ (u + v0 * (p.1 + p.2)) ^ 2 := by
      nlinarith [sq_abs u0, sq_abs (u + v0 * (p.1 + p.2)),
        mul_nonneg (sub_nonneg.mpr (hp u hs))
          (by positivity : 0 ≤ |u + v0 * (p.1 + p.2)| + |u0| / 4)]
    change |kernel2 (p.1 - p.2) (u + v0 * (p.1 + p.2))| ≤ _
    exact hb.trans ((div_le_div_iff₀ (sq_pos_of_ne_zero (hz u hs))
      (sq_pos_of_ne_zero hu)).mpr (by nlinarith [mul_nonneg (sq_nonneg (p.1 - p.2)) (sub_nonneg.mpr hsq)]))
  have hB1 : Integrable (fun p : ℝ × ℝ => 8 * (p.1 - p.2) ^ 2 / |u0|) (ν.prod ν) :=
    (hD.const_mul 8).div_const _
  have hB2 : Integrable (fun p : ℝ × ℝ => 128 * (p.1 - p.2) ^ 2 / u0 ^ 2) (ν.prod ν) :=
    (hD.const_mul 128).div_const _
  have hF1 (u : ℝ) (hs : u ∈ s) : Integrable (F1 u) (ν.prod ν) :=
    hB1.mono' (hM1 u).aestronglyMeasurable (hb1.mono fun p hp => hp u hs)
  have hF2 (u : ℝ) (hs : u ∈ s) : Integrable (F2 u) (ν.prod ν) :=
    hB2.mono' (hM2 u).aestronglyMeasurable (hb2.mono fun p hp => hp u hs)
  have hG0 (u : ℝ) (hs : u ∈ s) :
      HasDerivAt (fun r : ℝ => ∫ p, F0 r p ∂ν.prod ν) (∫ p, F1 u p ∂ν.prod ν) u := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F0) (F' := F1)
      (hopen.mem_nhds hs)
      (Filter.Eventually.of_forall fun r => (hF0 r).aestronglyMeasurable) (hF0 u)
      (hF1 u hs).aestronglyMeasurable hb1 hB1 ?_).2
    filter_upwards [hzero] with p hp
    intro r hr
    exact kernel_hasDerivAt (p.1 - p.2) (v0 * (p.1 + p.2)) r (hp r hr)
  have hG1 : HasDerivAt (fun r : ℝ => ∫ p, F1 r p ∂ν.prod ν)
      (∫ p, F2 u0 p ∂ν.prod ν) u0 := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F1) (F' := F2)
      (hopen.mem_nhds hmem)
      (Filter.Eventually.of_forall fun r => (hM1 r).aestronglyMeasurable) (hF1 u0 hmem)
      (hF2 u0 hmem).aestronglyMeasurable hb2 hB2 ?_).2
    filter_upwards [hzero] with p hp
    intro r hr
    exact kernel1_hasDerivAt (p.1 - p.2) (v0 * (p.1 + p.2)) r (hp r hr)
  have hK (u : ℝ) (hs : u ∈ s) :
      quadraticChordChar ν u v0 = Complex.ofReal ((∫ p, F0 u p ∂ν.prod ν) / V) := by
    obtain ⟨_, hk, _, _, _⟩ := quadraticChordChar_exact ν h3 hV u v0
    rw [hk]
    congr 2
    apply integral_congr_ae
    filter_upwards [hzero] with p hp
    simp only [hp u hs, ite_false, F0, kernel]
  have hfirst (u : ℝ) (hs : u ∈ s) :
      HasDerivAt (fun r : ℝ => quadraticChordChar ν r v0)
        (Complex.ofReal ((∫ p, F1 u p ∂ν.prod ν) / V)) u := by
    apply ((hG0 u hs).div_const V).ofReal_comp.congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hs] with r hr
    exact hK r hr
  have hsecond :
      HasDerivAt (fun u : ℝ => deriv (fun r : ℝ => quadraticChordChar ν r v0) u)
        (Complex.ofReal ((∫ p, F2 u0 p ∂ν.prod ν) / V)) u0 := by
    apply (hG1.div_const V).ofReal_comp.congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hmem] with r hr
    exact (hfirst r hr).deriv
  exact ⟨hF1 u0 hmem, hF2 u0 hmem, hfirst u0 hmem, hsecond,
    (hfirst u0 hmem).deriv, hsecond.deriv⟩

theorem quadraticChordChar_cone_derivative_bounds
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h)
    (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (u0 v0 : ℝ) (hu : u0 ≠ 0)
    (hv : |v0| ≤ |u0| / (4 * h)) :
    ‖deriv (fun u : ℝ => quadraticChordChar ν u v0) u0‖ ≤ 8 / |u0| ∧
    ‖deriv
      (fun u : ℝ => deriv (fun r : ℝ => quadraticChordChar ν r v0) u) u0‖ ≤
        64 / u0 ^ 2 := by
  let V : ℝ := variance (id : ℝ → ℝ) ν
  let F1 : ℝ × ℝ → ℝ := fun p => kernel1 (p.1 - p.2) (u0 + v0 * (p.1 + p.2))
  let F2 : ℝ × ℝ → ℝ := fun p => kernel2 (p.1 - p.2) (u0 + v0 * (p.1 + p.2))
  obtain ⟨h1, h2, _, _, hd1, hd2⟩ :=
    quadraticChordChar_cone_derivatives ν h3 hV h hh hs u0 v0 hu hv
  have ha : 0 < |u0| := abs_pos.mpr hu
  have hp := pair_support ν h hs
  have hD := (quadratic_pair_square_moment ν h3).1
  have hm := (quadratic_pair_square_moment ν h3).2
  have hb : ∀ᵐ p : ℝ × ℝ ∂ν.prod ν,
      ‖F1 p‖ ≤ 4 * (p.1 - p.2) ^ 2 / |u0| ∧
      ‖F2 p‖ ≤ 32 * (p.1 - p.2) ^ 2 / u0 ^ 2 := by
    filter_upwards [hp] with p hp
    have hl := phase_cone_lower p.1 p.2 h u0 v0 hh hp.1 hp.2 hv
    have ht : u0 + v0 * (p.1 + p.2) ≠ 0 := by
      intro hz
      rw [hz, abs_zero] at hl
      linarith
    have hat := abs_pos.mpr ht
    obtain ⟨hb1, hb2⟩ := rational_bounds (p.1 - p.2) (u0 + v0 * (p.1 + p.2)) ht
    have hsq : u0 ^ 2 / 4 ≤ (u0 + v0 * (p.1 + p.2)) ^ 2 := by
      nlinarith [sq_abs u0, sq_abs (u0 + v0 * (p.1 + p.2)),
        mul_nonneg (sub_nonneg.mpr hl)
          (by positivity : 0 ≤ |u0 + v0 * (p.1 + p.2)| + |u0| / 2)]
    constructor
    · exact hb1.trans ((div_le_div_iff₀ hat ha).mpr
        (by nlinarith [mul_nonneg (sq_nonneg (p.1 - p.2)) (sub_nonneg.mpr hl)]))
    · exact hb2.trans ((div_le_div_iff₀ (sq_pos_of_ne_zero ht) (sq_pos_of_ne_zero hu)).mpr
        (by nlinarith [mul_nonneg (sq_nonneg (p.1 - p.2)) (sub_nonneg.mpr hsq)]))
  have hi1 : |∫ p, F1 p ∂ν.prod ν| ≤ 8 * V / |u0| := by
    have hb1 := norm_integral_le_of_norm_le ((hD.const_mul 4).div_const |u0|)
      (hb.mono fun p hp => hp.1)
    simp only [Real.norm_eq_abs, integral_div, integral_const_mul, hm] at hb1
    convert hb1 using 1
    dsimp [V]
    ring
  have hi2 : |∫ p, F2 p ∂ν.prod ν| ≤ 64 * V / u0 ^ 2 := by
    have hb2 := norm_integral_le_of_norm_le ((hD.const_mul 32).div_const (u0 ^ 2))
      (hb.mono fun p hp => hp.2)
    simp only [Real.norm_eq_abs, integral_div, integral_const_mul, hm] at hb2
    convert hb2 using 1
    dsimp [V]
    ring
  rw [hd1, hd2]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  change |(∫ p, F1 p ∂ν.prod ν) / V| ≤ 8 / |u0| ∧
    |(∫ p, F2 p ∂ν.prod ν) / V| ≤ 64 / u0 ^ 2
  rw [abs_div, abs_div, abs_of_pos hV]
  constructor
  · apply (div_le_iff₀ hV).mpr
    exact hi1.trans_eq (by ring)
  · apply (div_le_iff₀ hV).mpr
    exact hi2.trans_eq (by ring)

end Shao.Probability
