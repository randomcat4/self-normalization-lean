import Shao.C2.RademacherBrownianEndpointLimit

noncomputable section
namespace Shao.C2.BrownianUpperJointReflection
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Shao.C2.BridgeDomination Shao.C2.BrownianUpperJointLimit
open Shao.C2.PolygonalRademacherReflection Shao.C2.RademacherBrownianEndpointLimit
open Shao.OQ4.PolygonalPathTightness

private theorem gaussian_tail_from_right (b : ℝ) :
    Tendsto (fun m : ℕ => (gaussianReal 0 1).real (Ici (b + 1 / ((m : ℝ) + 1))))
      atTop (𝓝 ((gaussianReal 0 1).real (Ici b))) := by
  let r : ℕ → ℝ := fun m => b + 1 / ((m : ℝ) + 1)
  have hr : Antitone r := by
    intro m n hmn
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
    have hd := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (m : ℝ) + 1) hmn'
    dsimp [r]
    linarith
  have hU : (⋃ m : ℕ, Ici (r m)) = Ioi b := by
    ext x
    constructor
    · intro hx
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
      have hp : 0 < 1 / ((m : ℝ) + 1) := by positivity
      change b + 1 / ((m : ℝ) + 1) ≤ x at hm
      change b < x
      linarith
    · intro hx
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < x - b from sub_pos.mpr hx)
      apply Set.mem_iUnion.mpr
      refine ⟨m, ?_⟩
      change b + 1 / ((m : ℝ) + 1) ≤ x
      linarith
  have ht := tendsto_measure_iUnion_atTop
    (fun i j hij => Ici_subset_Ici.mpr (hr hij)) (μ := gaussianReal 0 1)
  rw [hU] at ht
  have hreal := (ENNReal.continuousAt_toReal
    (measure_ne_top (gaussianReal 0 1) (Ioi b))).tendsto.comp ht
  change Tendsto (fun m : ℕ => (gaussianReal 0 1).real (Ici (r m))) atTop
    (𝓝 ((gaussianReal 0 1).real (Ioi b))) at hreal
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have he : (gaussianReal 0 1).real (Ioi b) = (gaussianReal 0 1).real (Ici b) :=
    measureReal_congr (Ioi_ae_eq_Ici' (measure_singleton b))
  rw [he] at hreal
  exact hreal

theorem brownian_upper_joint_reflection {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a v : ℝ) (ha : 0 < a) (hv : v < a) :
    P.real {ω | (∀ t : BridgeTime, B ⟨(t : ℝ), t.property.1⟩ ω < a) ∧ B 1 ω ≤ v} +
      (gaussianReal 0 1).real (Ici (2 * a - v)) = (gaussianReal 0 1).real (Iic v) := by
  let h : ℕ → ℝ := fun j => (j : ℝ) + 1
  let n : ℕ → ℕ := fun j => (j + 1) ^ 2
  let μ (j : ℕ) : Measure (Shao.Path (n j)) :=
    Measure.pi (fun _ : Fin (n j) => Shao.OQ4.RademacherCosine.law)
  let J : ℕ → ℝ := fun j =>
    (polygonalPathLaw 1 (n j) (h j) Shao.OQ4.RademacherCosine.law).real (upperJointSet a v)
  let F : ℕ → ℝ := fun j => (μ j).real {p : Shao.Path (n j) | Shao.prefixSum p (n j) / h j ≤ v}
  let Q : ℕ → ℝ → ℝ := fun j r =>
    (μ j).real {p : Shao.Path (n j) | r ≤ Shao.prefixSum p (n j) / h j}
  let cut : ℕ → ℝ := fun j =>
    (((2 * (⌊a * h j⌋ + 1) - ⌊v * h j⌋ : ℤ) : ℝ) / h j)
  let b : ℝ := 2 * a - v
  let JL : ℝ := P.real {ω |
    (∀ t : BridgeTime, B ⟨(t : ℝ), t.property.1⟩ ω < a) ∧ B 1 ω ≤ v}
  let gaussCDFValue : ℝ := (gaussianReal 0 1).real (Iic v)
  let GT : ℝ → ℝ := fun r => (gaussianReal 0 1).real (Ici r)
  have hpos (j : ℕ) : 0 < h j := by dsimp [h]; positivity
  have hsq (j : ℕ) : h j ^ 2 = (n j : ℝ) := by
    simp only [h, n, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  have hJ : Tendsto J atTop (𝓝 JL) := rademacher_upper_joint_tendsto B P hB a v ha
  have hF : Tendsto F atTop (𝓝 gaussCDFValue) := rademacher_endpoint_cdf_tendsto B P hB v
  have hQ (r : ℝ) : Tendsto (fun j => Q j r) atTop (𝓝 (GT r)) :=
    rademacher_endpoint_tail_tendsto B P hB r
  have he (j : ℕ) : J j + Q j (cut j) = F j :=
    scaled_polygonal_reflection (n j) (h j) (hpos j) (hsq j) a v ha hv
  have hb (j : ℕ) : 0 ≤ cut j - b ∧ cut j - b ≤ 3 / h j :=
    scaled_reflected_cut_bounds a v (h j) (hpos j)
  have hmono (j : ℕ) (r s : ℝ) (hrs : r ≤ s) : Q j s ≤ Q j r := by
    apply measureReal_mono _ (by finiteness)
    intro p hp
    exact hrs.trans hp
  have hlo : gaussCDFValue ≤ JL + GT b := by
    have hlim : Tendsto (fun j => F j - (J j + Q j b)) atTop (𝓝 (gaussCDFValue - (JL + GT b))) :=
      hF.sub (hJ.add (hQ b))
    have hl : gaussCDFValue - (JL + GT b) ≤ 0 := le_of_tendsto hlim (Eventually.of_forall (fun j => by
      have hle := hmono j b (cut j) (by have hh := (hb j).1; linarith)
      have hid := he j
      linarith))
    linarith
  have hupper (δ : ℝ) (hδ : 0 < δ) : JL + GT (b + δ) ≤ gaussCDFValue := by
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show 0 < δ / 3 by positivity)
    have hsmall : ∀ᶠ j : ℕ in atTop, 3 / h j < δ := by
      filter_upwards [eventually_ge_atTop N] with j hj
      have hNj : (N : ℝ) + 1 ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hj 1
      have hd := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (N : ℝ) + 1) hNj
      calc
        3 / h j = 3 * (1 / ((j : ℝ) + 1)) := by dsimp [h]; ring
        _ ≤ 3 * (1 / ((N : ℝ) + 1)) := mul_le_mul_of_nonneg_left hd (by norm_num)
        _ < δ := by linarith
    have hineq : ∀ᶠ j : ℕ in atTop, (J j + Q j (b + δ)) - F j ≤ 0 := by
      filter_upwards [hsmall] with j hj
      have hcut : cut j ≤ b + δ := by have hh := (hb j).2; linarith
      have hle := hmono j (cut j) (b + δ) hcut
      have hid := he j
      linarith
    have hlim := (hJ.add (hQ (b + δ))).sub hF
    have hl : (JL + GT (b + δ)) - gaussCDFValue ≤ 0 := le_of_tendsto hlim hineq
    linarith
  have hlim : Tendsto (fun m : ℕ => JL + GT (b + 1 / ((m : ℝ) + 1))) atTop
      (𝓝 (JL + GT b)) := tendsto_const_nhds.add (gaussian_tail_from_right b)
  have hhi : JL + GT b ≤ gaussCDFValue := le_of_tendsto hlim
    (Eventually.of_forall (fun m => hupper (1 / ((m : ℝ) + 1)) (by positivity)))
  exact le_antisymm hhi hlo

end Shao.C2.BrownianUpperJointReflection
