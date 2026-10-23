import Shao.Probability.BerryEsseen
import Shao.Probability.BoundedQuadraticTilt
import Shao.Probability.GaussianTail
import Shao.Probability.MeasurablePath
import Shao.Probability.FiniteIID

set_option autoImplicit false
set_option Elab.async false

namespace Shao.Probability
open MeasureTheory ProbabilityTheory
open Function
open scoped BigOperators ENNReal

private theorem bgt_integrable (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ᵐ z : ℝ ∂eta, |f z| ≤ C) : Integrable f eta := by
  exact (integrable_const C).mono' hf.aestronglyMeasurable
    (by simpa only [Real.norm_eq_abs] using hC)

private theorem bgt_powers (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (h : ℝ) (hs : ∀ᵐ z : ℝ ∂eta, |z| ≤ h) (p : ℕ) :
    Integrable (fun z : ℝ => z ^ p) eta ∧
      Integrable (fun z : ℝ => |z| ^ p) eta ∧
      (∫ z : ℝ, |z| ^ p ∂eta) ≤ h ^ p := by
  have hp : ∀ᵐ z : ℝ ∂eta, |z| ^ p ≤ h ^ p := by
    filter_upwards [hs] with z hz
    exact pow_le_pow_left₀ (abs_nonneg z) hz p
  have hi : Integrable (fun z : ℝ => |z| ^ p) eta :=
    bgt_integrable eta _ (by fun_prop) _ (by
      filter_upwards [hp] with z hz
      simpa only [abs_of_nonneg (pow_nonneg (abs_nonneg z) p)] using hz)
  refine ⟨bgt_integrable eta _ (by fun_prop) _ (by
    simpa only [abs_pow] using hp), hi, ?_⟩
  simpa only [integral_const, probReal_univ, one_smul] using
    integral_mono_ae hi (integrable_const (h ^ p)) hp

private theorem bgt_mean_bound (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (h : ℝ) (hs : ∀ᵐ z : ℝ ∂eta, |z| ≤ h) :
    |∫ z : ℝ, z ∂eta| ≤ h := by
  have ha : (∫ z : ℝ, ‖z‖ ∂eta) ≤ h := by
    simpa only [pow_one, Real.norm_eq_abs] using (bgt_powers eta h hs 1).2.2
  simpa only [Real.norm_eq_abs] using
    (norm_integral_le_integral_norm (f := fun z : ℝ => z)).trans ha

private theorem bgt_var_formula (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (h2 : Integrable (fun z : ℝ => z ^ 2) eta) :
    variance (id : ℝ → ℝ) eta =
      (∫ z : ℝ, z ^ 2 ∂eta) - (∫ z : ℝ, z ∂eta) ^ 2 := by
  simpa only [Pi.pow_apply, id_eq] using
    variance_eq_sub ((memLp_two_iff_integrable_sq
      measurable_id.aestronglyMeasurable).2 h2)

private theorem bgt_lyapunov (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (h2 : Integrable (fun z : ℝ => z ^ 2) eta)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) eta) :
    |∫ z : ℝ, z ∂eta| * (∫ z : ℝ, z ^ 2 ∂eta) ≤ (∫ z : ℝ, |z| ^ 3 ∂eta) ∧
      |∫ z : ℝ, z ∂eta| ^ 3 ≤ (∫ z : ℝ, |z| ^ 3 ∂eta) := by
  let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂eta
  let r : ℝ := Real.sqrt m2
  let mu : ℝ := ∫ z : ℝ, z ∂eta
  have hm2 : 0 ≤ m2 := integral_nonneg fun z => sq_nonneg z
  have hr : 0 ≤ r := Real.sqrt_nonneg m2
  have hr2 : r ^ 2 = m2 := Real.sq_sqrt hm2
  have hpoint (z : ℝ) : (3 * r) * z ^ 2 ≤ 2 * |z| ^ 3 + r ^ 3 := by
    have hf := mul_nonneg (sq_nonneg (|z| - r))
      (show 0 ≤ 2 * |z| + r by positivity)
    rw [← sq_abs z]
    nlinarith only [hf]
  have hi := integral_mono (h2.const_mul (3 * r))
    ((h3.const_mul 2).add (integrable_const (r ^ 3))) hpoint
  change (∫ z : ℝ, (3 * r) * z ^ 2 ∂eta) ≤
    ∫ z : ℝ, 2 * |z| ^ 3 + r ^ 3 ∂eta at hi
  rw [integral_const_mul, integral_add (h3.const_mul 2) (integrable_const (r ^ 3)),
    integral_const_mul] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  have hr3 : r ^ 3 = r * m2 := by rw [pow_succ, hr2]; ring
  have hlyap : r * m2 ≤ ∫ z : ℝ, |z| ^ 3 ∂eta := by
    change 3 * r * m2 ≤ 2 * (∫ z : ℝ, |z| ^ 3 ∂eta) + r ^ 3 at hi
    linarith only [hi, hr3]
  have hmu2 : mu ^ 2 ≤ m2 := by
    have hv := variance_nonneg (id : ℝ → ℝ) eta
    rw [bgt_var_formula eta h2] at hv
    change 0 ≤ m2 - mu ^ 2 at hv
    linarith
  have hmur : |mu| ≤ r := by nlinarith [sq_abs mu, abs_nonneg mu]
  have hf : |mu| * m2 ≤ ∫ z : ℝ, |z| ^ 3 ∂eta :=
    (mul_le_mul_of_nonneg_right hmur hm2).trans hlyap
  refine ⟨hf, ?_⟩
  have hc := mul_le_mul_of_nonneg_left hmu2 (abs_nonneg mu)
  have he : |mu| ^ 3 = |mu| * mu ^ 2 := by rw [pow_succ, sq_abs]; ring
  change |mu| ^ 3 ≤ _
  rw [he]
  exact hc.trans hf

private theorem bgt_centered_third (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (h : ℝ) (hs : ∀ᵐ z : ℝ ∂eta, |z| ≤ h) :
    Integrable (fun z : ℝ => |z - ∫ y : ℝ, y ∂eta| ^ 3) eta ∧
      (∫ z : ℝ, |z - ∫ y : ℝ, y ∂eta| ^ 3 ∂eta) ≤
        8 * (∫ z : ℝ, |z| ^ 3 ∂eta) := by
  let mu : ℝ := ∫ z : ℝ, z ∂eta
  have hp := bgt_powers eta h hs
  have hc : Integrable (fun z : ℝ => |z - mu| ^ 3) eta :=
    bgt_integrable eta _ (by fun_prop) ((h + |mu|) ^ 3) (by
      filter_upwards [hs] with z hz
      rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub z mu).trans (by linarith)) 3)
  have hpoint (z : ℝ) : |z - mu| ^ 3 ≤ 4 * (|z| ^ 3 + |mu| ^ 3) := by
    have htri := pow_le_pow_left₀ (abs_nonneg (z - mu)) (abs_sub z mu) 3
    have hf := mul_nonneg (sq_nonneg (|z| - |mu|))
      (add_nonneg (abs_nonneg z) (abs_nonneg mu))
    nlinarith only [htri, hf]
  have hi := integral_mono hc (((hp 3).2.1.add (integrable_const (|mu| ^ 3))).const_mul 4)
    hpoint
  change (∫ z : ℝ, |z - mu| ^ 3 ∂eta) ≤
    ∫ z : ℝ, 4 * (|z| ^ 3 + |mu| ^ 3) ∂eta at hi
  rw [integral_const_mul, integral_add (hp 3).2.1 (integrable_const (|mu| ^ 3))] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  have hmu := (bgt_lyapunov eta (hp 2).1 (hp 3).2.1).2
  exact ⟨hc, by dsimp [mu] at hi ⊢; linarith⟩

private theorem bgt_small_parameter_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (r R : ℝ) (hr : r ≤ R) :
    P.real A ≤ (Shao.standardNormalTail R)⁻¹ * Shao.standardNormalTail r := by
  have htail : 0 < Shao.standardNormalTail R :=
    (Shao.standardNormalTail_basic.2.2.1 R).1
  have hmono := Shao.standardNormalTail_basic.1 hr
  calc
    P.real A ≤ 1 := measureReal_le_one
    _ = (Shao.standardNormalTail R)⁻¹ * Shao.standardNormalTail R := by
      rw [inv_mul_cancel₀ (ne_of_gt htail)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr htail.le)

private theorem bgt_iid_interval_mass
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) eta)
    (hV : 0 < variance (id : ℝ → ℝ) eta)
    (k : ℕ) (hk : 1 ≤ k) (a b : ℝ) (hab : a ≤ b) :
    let mu : ℝ := ∫ z : ℝ, z ∂eta
    let tau : ℝ := Real.sqrt (variance (id : ℝ → ℝ) eta) * Real.sqrt (k : ℝ)
    let err : ℝ := 1024 * (∫ z : ℝ, |z - mu| ^ 3 ∂eta) /
      ((Real.sqrt (variance (id : ℝ → ℝ) eta)) ^ 3 * Real.sqrt (k : ℝ))
    (Measure.pi (fun _ : Fin k => eta)).real
      {x : Shao.Path k | a ≤ Shao.prefixSum x k ∧ Shao.prefixSum x k < b} ≤
        (b - a) / tau + 2 * err := by
  dsimp only
  let P := Measure.pi (fun _ : Fin k => eta)
  let mu : ℝ := ∫ z : ℝ, z ∂eta
  let tau : ℝ := Real.sqrt (variance (id : ℝ → ℝ) eta) * Real.sqrt (k : ℝ)
  let Z : Shao.Path k → ℝ := fun x => (Shao.prefixSum x k - (k : ℝ) * mu) / tau
  let law := P.map Z
  have hZ : Measurable Z := (Shao.measurable_prefixSum k).sub_const _ |>.div_const _
  letI : IsProbabilityMeasure law :=
    (Measure.isProbabilityMeasure_map_iff hZ.aemeasurable).mpr inferInstance
  have htau : 0 < tau :=
    mul_pos (Real.sqrt_pos.mpr hV) (Real.sqrt_pos.mpr (by exact_mod_cast hk))
  let err : ℝ := 1024 * (∫ z : ℝ, |z - mu| ^ 3 ∂eta) /
    ((Real.sqrt (variance (id : ℝ → ℝ) eta)) ^ 3 * Real.sqrt (k : ℝ))
  have hCDF (t : ℝ) : |law.real (Set.Iic t) - Shao.OQ4.standardNormalCDF t| ≤ err := by
    rw [Measure.real_def, Measure.map_apply hZ measurableSet_Iic]
    exact iid_centered_berryEsseen eta h3 hV k hk t
  have hi := Shao.OQ4.closed_interval_mass_bound_from_cdf law 1 err
    Shao.OQ4.standardNormalCDF (by norm_num) (by dsimp [err]; positivity)
    (by intro x y; simpa using Shao.OQ4.standardNormalCDF_lipschitz x y) hCDF
    ((a - (k : ℝ) * mu) / tau) ((b - (k : ℝ) * mu) / tau)
    (div_le_div_of_nonneg_right (by linarith) htau.le)
  have hsub : {x : Shao.Path k | a ≤ Shao.prefixSum x k ∧ Shao.prefixSum x k < b} ⊆
      Z ⁻¹' Set.Icc ((a - (k : ℝ) * mu) / tau) ((b - (k : ℝ) * mu) / tau) := by
    intro x hx
    exact ⟨(div_le_div_iff_of_pos_right htau).2 (by linarith [hx.1]),
      (div_le_div_iff_of_pos_right htau).2 (by linarith [hx.2])⟩
  have hmap : law.real (Set.Icc ((a - (k : ℝ) * mu) / tau)
      ((b - (k : ℝ) * mu) / tau)) = P.real (Z ⁻¹' Set.Icc
      ((a - (k : ℝ) * mu) / tau) ((b - (k : ℝ) * mu) / tau)) := by
    rw [Measure.real_def, Measure.map_apply hZ measurableSet_Icc]
    rfl
  rw [hmap] at hi
  calc
    _ ≤ P.real (Z ⁻¹' Set.Icc ((a - (k : ℝ) * mu) / tau)
        ((b - (k : ℝ) * mu) / tau)) := measureReal_mono hsub
    _ ≤ _ := hi
    _ = _ := by dsimp [err, mu, tau]; ring

private theorem bgt_centered_budgets
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (D : ℝ) (hD : 1 ≤ D) (k : ℕ) (u : ℝ) (hu : 1 ≤ u)
    (hs : ∀ᵐ z : ℝ ∂eta, |z| ≤ 1 / u)
    (h2 : Integrable (fun z : ℝ => z ^ 2) eta)
    (hvL : (1 / 4 : ℝ) ≤ (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta))
    (hvU : (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta) ≤ 4)
    (hmean : (k : ℝ) * |∫ z : ℝ, z ∂eta| ≤ D / u)
    (hthird : (k : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂eta) ≤ D / u ^ 3)
    (hlarge : 8 * D ≤ u ^ 2) :
    let mu := ∫ z : ℝ, z ∂eta
    (∀ᵐ z : ℝ ∂eta, |z - mu| ≤ 2 / u) ∧
      (k : ℝ) * mu ^ 2 ≤ D / u ^ 2 ∧
      (1 / 8 : ℝ) ≤ (k : ℝ) * variance (id : ℝ → ℝ) eta ∧
      (k : ℝ) * variance (id : ℝ → ℝ) eta ≤ 4 ∧
      (k : ℝ) * (∫ z : ℝ, |z - mu| ^ 3 ∂eta) ≤ 8 * D / u ^ 3 := by
  let mu : ℝ := ∫ z : ℝ, z ∂eta
  have hu0 : 0 < u := by linarith
  have hmub : |mu| ≤ 1 / u := bgt_mean_bound eta (1 / u) hs
  have hmu2 : (k : ℝ) * mu ^ 2 ≤ D / u ^ 2 := by
    calc
      (k : ℝ) * mu ^ 2 = ((k : ℝ) * |mu|) * |mu| := by rw [← sq_abs]; ring
      _ ≤ (D / u) * (1 / u) :=
        mul_le_mul hmean hmub (abs_nonneg mu) (div_nonneg (by linarith) hu0.le)
      _ = D / u ^ 2 := by ring
  have hvar : (k : ℝ) * variance (id : ℝ → ℝ) eta =
      (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta) - (k : ℝ) * mu ^ 2 := by
    rw [bgt_var_formula eta h2]
    dsimp [mu]
    ring
  have hmuSmall : (k : ℝ) * mu ^ 2 ≤ (1 / 8 : ℝ) := by
    refine hmu2.trans ?_
    exact (div_le_iff₀ (sq_pos_of_pos hu0)).2 (by linarith)
  refine ⟨?_, hmu2, ?_, ?_, ?_⟩
  · filter_upwards [hs] with z hz
    calc
      |z - mu| ≤ |z| + |mu| := abs_sub z mu
      _ ≤ 1 / u + 1 / u := add_le_add hz hmub
      _ = 2 / u := by ring
  · rw [hvar]; linarith
  · rw [hvar]
    nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) (sq_nonneg mu)]
  · have hc := mul_le_mul_of_nonneg_left (bgt_centered_third eta (1 / u) hs).2
      (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    calc
      _ ≤ (k : ℝ) * (8 * (∫ z : ℝ, |z| ^ 3 ∂eta)) := hc
      _ = 8 * ((k : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂eta)) := by ring
      _ ≤ 8 * (D / u ^ 3) := mul_le_mul_of_nonneg_left hthird (by norm_num)
      _ = _ := by ring

private theorem bgt_wall_small
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (k : ℕ) (hk : 0 < k) (u X b v : ℝ)
    (hX : 0 ≤ X) (huX : u ≤ X) (hb : b ≤ 3 * u) (hv : (1 / 4 : ℝ) ≤ v) :
    (Measure.pi (fun _ : Fin k => eta)).real
        {a : Shao.Path k | b ≤ Shao.upperMax a hk} ≤
      (Shao.standardNormalTail (6 * X))⁻¹ * Shao.standardNormalTail (b / Real.sqrt v) := by
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt v := by
    have hh := Real.sq_sqrt (show 0 ≤ v by linarith)
    have hp := Real.sqrt_nonneg v
    nlinarith
  apply bgt_small_parameter_bound
  apply (div_le_iff₀ (by linarith : 0 < Real.sqrt v)).2
  nlinarith

private theorem bgt_first_crossing_completion
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (S : ℕ → Ω → ℝ) (R : Fin k → Ω → ℝ)
    (hS : ∀ j, Measurable (S j)) (hR : ∀ j, Measurable (R j))
    (a b p : ℝ) (hp : 0 < p)
    (hadd : ∀ j : Fin k, ∀ x, S k x = S (j.val + 1) x + R j x)
    (hcompletion : ∀ j : Fin k, p ≤ P.real {x | -a ≤ R j x})
    (hindep : ∀ j : Fin k,
      IndepSet {x | b ≤ S (j.val + 1) x ∧
        ∀ i : ℕ, 1 ≤ i → i < j.val + 1 → S i x < b} {x | -a ≤ R j x} P) :
    P.real {x | ∃ j : ℕ, 1 ≤ j ∧ j ≤ k ∧ b ≤ S j x} ≤
      p⁻¹ * P.real {x | b - a ≤ S k x} := by
  classical
  let A : Fin k → Set Ω := fun j => {x | b ≤ S (j.val + 1) x ∧
    ∀ i : ℕ, 1 ≤ i → i < j.val + 1 → S i x < b}
  let B : Fin k → Set Ω := fun j => A j ∩ {x | -a ≤ R j x}
  have hmA (j : Fin k) : MeasurableSet (A j) := by
    simp only [A, Set.setOf_and, Set.setOf_forall]
    exact (measurableSet_le measurable_const (hS _)).inter
      (MeasurableSet.iInter fun i : ℕ => MeasurableSet.iInter fun _ : 1 ≤ i =>
        MeasurableSet.iInter fun _ : i < j.val + 1 => measurableSet_lt (hS i) measurable_const)
  have hmB (j : Fin k) : MeasurableSet (B j) :=
    (hmA j).inter (measurableSet_le measurable_const (hR j))
  have hdA : Pairwise (Disjoint on A) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    change b ≤ S (i.val + 1) x ∧ _ at hxi
    change b ≤ S (j.val + 1) x ∧ _ at hxj
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact (not_lt_of_ge hxi.1) (hxj.2 (i.val + 1) (by omega) (by omega))
    · exact (not_lt_of_ge hxj.1) (hxi.2 (j.val + 1) (by omega) (by omega))
  have hdB : Pairwise (Disjoint on B) := by
    intro i j hij
    exact (hdA hij).mono Set.inter_subset_left Set.inter_subset_left
  have hcover : {x | ∃ j : ℕ, 1 ≤ j ∧ j ≤ k ∧ b ≤ S j x} = ⋃ j, A j := by
    ext x
    constructor
    · intro hx
      let q : ℕ → Prop := fun j => 1 ≤ j ∧ j ≤ k ∧ b ≤ S j x
      have hex : ∃ j, q j := hx
      let n := Nat.find hex
      have hn : 1 ≤ n ∧ n ≤ k ∧ b ≤ S n x := Nat.find_spec hex
      let j : Fin k := ⟨n - 1, by omega⟩
      apply Set.mem_iUnion.mpr
      refine ⟨j, ?_⟩
      change b ≤ S (j.val + 1) x ∧ _
      have hj : j.val + 1 = n := by dsimp [j]; omega
      rw [hj]
      refine ⟨hn.2.2, ?_⟩
      intro i hi hin
      by_contra hb
      have hqi : q i := ⟨hi, by omega, le_of_not_gt hb⟩
      have hmin := Nat.find_min' hex hqi
      change n ≤ i at hmin
      omega
    · intro hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      exact ⟨j.val + 1, by omega, by omega, hj.1⟩
  have hsub : (⋃ j, B j) ⊆ {x | b - a ≤ S k x} := by
    intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    change b - a ≤ S k x
    rw [hadd j x]
    change (b ≤ S (j.val + 1) x ∧ _) ∧ -a ≤ R j x at hj
    linarith [hj.1.1, hj.2]
  have heq (j : Fin k) : P.real (B j) = P.real (A j) * P.real {x | -a ≤ R j x} := by
    simpa only [A, B, Measure.real_def, ENNReal.toReal_mul] using
      congrArg ENNReal.toReal (hindep j).measure_inter_eq_mul
  have hsum : p * (∑ j : Fin k, P.real (A j)) ≤ ∑ j : Fin k, P.real (B j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [heq]
    nlinarith [hcompletion j, show 0 ≤ P.real (A j) from measureReal_nonneg]
  rw [hcover, measureReal_iUnion_fintype hdA hmA]
  have htotal : (∑ j : Fin k, P.real (B j)) ≤ P.real {x | b - a ≤ S k x} := by
    rw [← measureReal_iUnion_fintype hdB hmB]
    exact measureReal_mono hsub
  have h := hsum.trans htotal
  calc
    _ = p⁻¹ * (p * ∑ j : Fin k, P.real (A j)) := by rw [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hp.le)

private theorem bgt_iid_sum_moments
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (h2 : Integrable (fun z : ℝ => z ^ 2) eta) (k : ℕ) :
    let P := Measure.pi (fun _ : Fin k => eta)
    MemLp (fun x : Shao.Path k => Shao.prefixSum x k) 2 P ∧
      (∫ x : Shao.Path k, Shao.prefixSum x k ∂P) = (k : ℝ) * (∫ z : ℝ, z ∂eta) ∧
      variance (fun x : Shao.Path k => Shao.prefixSum x k) P =
        (k : ℝ) * variance (id : ℝ → ℝ) eta := by
  let P := Measure.pi (fun _ : Fin k => eta)
  have hLp : MemLp (id : ℝ → ℝ) 2 eta :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 h2
  have hcoord (i : Fin k) : MemLp (fun x : Shao.Path k => x i) 2 P :=
    hLp.comp_measurePreserving (measurePreserving_eval (fun _ : Fin k => eta) i)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Shao.prefixSum_length] using
      memLp_finsetSum (Finset.univ : Finset (Fin k)) (fun i _ => hcoord i)
  · simp only [Shao.prefixSum_length]
    rw [integral_finsetSum _ (fun i _ => (hcoord i).integrable (by norm_num))]
    have hint (i : Fin k) : (∫ x : Shao.Path k, x i ∂P) = ∫ z : ℝ, z ∂eta := by
      have hi := integral_map (μ := P) (measurable_pi_apply i).aemeasurable
        measurable_id.aestronglyMeasurable
      rw [(measurePreserving_eval (fun _ : Fin k => eta) i).map_eq] at hi
      exact hi.symm
    simp only [hint, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · have hv := variance_sum_pi (μ := fun _ : Fin k => eta) (X := fun _ => (id : ℝ → ℝ))
      (fun _ => hLp)
    have he : (∑ i : Fin k, fun x : Shao.Path k => x i) =
        (fun x : Shao.Path k => Shao.prefixSum x k) := by
      funext x
      simp only [Finset.sum_apply, Shao.prefixSum_length]
    change variance (∑ i : Fin k, fun x : Shao.Path k => x i) P = _ at hv
    rw [he] at hv
    simpa only [id_eq, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hv

private theorem bgt_iid_completion_probability
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (h2 : Integrable (fun z : ℝ => z ^ 2) eta)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) eta)
    (hV : 0 < variance (id : ℝ → ℝ) eta)
    (m : ℕ) (a : ℝ) (ha : 0 < a)
    (hmean : (m : ℝ) * |∫ z : ℝ, z ∂eta| ≤ a / 2)
    (hthird : 16384 * (∫ z : ℝ, |z - ∫ y : ℝ, y ∂eta| ^ 3 ∂eta) ≤
      a * variance (id : ℝ → ℝ) eta) :
    (1 / 4 : ℝ) ≤ (Measure.pi (fun _ : Fin m => eta)).real
      {x : Shao.Path m | -a ≤ Shao.prefixSum x m} := by
  let P := Measure.pi (fun _ : Fin m => eta)
  let mu : ℝ := ∫ z : ℝ, z ∂eta
  let V : ℝ := variance (id : ℝ → ℝ) eta
  let tau : ℝ := Real.sqrt V * Real.sqrt (m : ℝ)
  have hmabs : |(m : ℝ) * mu| ≤ a / 2 := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
    exact hmean
  have hcomp : P.real {x : Shao.Path m | Shao.prefixSum x m < -a} =
      1 - P.real {x : Shao.Path m | -a ≤ Shao.prefixSum x m} := by
    have h := measureReal_compl (μ := P)
      (s := {x : Shao.Path m | -a ≤ Shao.prefixSum x m})
      (measurableSet_le measurable_const (Shao.measurable_prefixSum m))
    simpa only [Set.compl_setOf, not_le, probReal_univ] using h
  suffices hbad : P.real {x : Shao.Path m | Shao.prefixSum x m < -a} ≤ 3 / 4 by
    change (1 / 4 : ℝ) ≤ P.real _
    linarith
  by_cases hm : m = 0
  · subst m
    have hempty : {x : Shao.Path 0 | Shao.prefixSum x 0 < -a} = ∅ := by
      ext x
      simp only [Shao.prefixSum_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      linarith
    rw [hempty, measureReal_empty]
    norm_num
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have htau : 0 < tau := mul_pos (Real.sqrt_pos.mpr hV) (Real.sqrt_pos.mpr hmpos)
  have htau2 : tau ^ 2 = (m : ℝ) * V := by
    dsimp [tau]
    rw [mul_pow, Real.sq_sqrt hV.le, Real.sq_sqrt hmpos.le]
    ring
  by_cases hsmall : tau ≤ a / 4
  · obtain ⟨hLp, hint, hvar⟩ := bgt_iid_sum_moments eta h2 m
    have hcheb := meas_ge_le_variance_div_sq hLp (show 0 < a / 2 by linarith)
    have hsub : {x : Shao.Path m | Shao.prefixSum x m < -a} ⊆
        {x : Shao.Path m | a / 2 ≤ |Shao.prefixSum x m - (∫ y : Shao.Path m, Shao.prefixSum y m ∂P)|} := by
      intro x hx
      change Shao.prefixSum x m < -a at hx
      change a / 2 ≤ |Shao.prefixSum x m - _|
      rw [hint]
      change a / 2 ≤ |Shao.prefixSum x m - (m : ℝ) * mu|
      have hmu := (abs_le.mp hmabs).1
      nlinarith [neg_le_abs (Shao.prefixSum x m - (m : ℝ) * mu)]
    have hreal := ENNReal.toReal_mono (by finiteness) hcheb
    rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _)), hvar] at hreal
    have hfrac : (m : ℝ) * V / (a / 2) ^ 2 ≤ (1 / 4 : ℝ) := by
      apply (div_le_iff₀ (sq_pos_of_pos (show 0 < a / 2 by linarith))).2
      nlinarith
    have hbound := (measureReal_mono hsub).trans (hreal.trans hfrac)
    exact hbound.trans (by norm_num)
  · have hlarge : a / 4 < tau := lt_of_not_ge hsmall
    let err : ℝ := 1024 * (∫ z : ℝ, |z - mu| ^ 3 ∂eta) /
      ((Real.sqrt V) ^ 3 * Real.sqrt (m : ℝ))
    have hden : (Real.sqrt V) ^ 3 * Real.sqrt (m : ℝ) = V * tau := by
      dsimp [tau]
      calc
        _ = (Real.sqrt V) ^ 2 * (Real.sqrt V * Real.sqrt (m : ℝ)) := by ring
        _ = _ := by rw [Real.sq_sqrt hV.le]
    have herr : err ≤ 1 / 4 := by
      dsimp [err]
      rw [hden]
      apply (div_le_iff₀ (mul_pos hV htau)).2
      change 16384 * (∫ z : ℝ, |z - mu| ^ 3 ∂eta) ≤ a * V at hthird
      nlinarith [mul_pos hV (show 0 < tau - a / 4 by linarith)]
    let x : ℝ := (-a - (m : ℝ) * mu) / tau
    have hx : x ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ htau.le
      linarith [(abs_le.mp hmabs).1]
    have hGzero : Shao.OQ4.standardNormalCDF 0 = (1 / 2 : ℝ) := by
      have hrep := (Shao.standardNormalTail_representation 0).2.1
      rw [Shao.standardNormalTail_basic.2.1] at hrep
      change Shao.OQ4.standardNormalCDF 0 = _
      unfold Shao.OQ4.standardNormalCDF
      linarith
    have hG : Shao.OQ4.standardNormalCDF x ≤ 1 / 2 := by
      rw [← hGzero]
      exact monotone_cdf (gaussianReal 0 1) hx
    have hBE := iid_centered_berryEsseen eta h3 hV m (Nat.one_le_iff_ne_zero.mpr hm) x
    change |P.real {y : Shao.Path m | (Shao.prefixSum y m - (m : ℝ) * mu) / tau ≤ x} -
      Shao.OQ4.standardNormalCDF x| ≤ err at hBE
    have hset : {y : Shao.Path m | (Shao.prefixSum y m - (m : ℝ) * mu) / tau ≤ x} =
        {y : Shao.Path m | Shao.prefixSum y m ≤ -a} := by
      ext y
      change (Shao.prefixSum y m - (m : ℝ) * mu) / tau ≤
        (-a - (m : ℝ) * mu) / tau ↔ Shao.prefixSum y m ≤ -a
      rw [div_le_div_iff_of_pos_right htau]
      constructor <;> intro h <;> linarith
    rw [hset] at hBE
    have hclosed : P.real {y : Shao.Path m | Shao.prefixSum y m ≤ -a} ≤ 3 / 4 := by
      linarith [(abs_le.mp hBE).2]
    exact (measureReal_mono (by
      intro y hy
      change Shao.prefixSum y m < -a at hy
      change Shao.prefixSum y m ≤ -a
      exact hy.le)).trans hclosed

private theorem bgt_subfamily_completion_probability
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (h2 : Integrable (fun z : ℝ => z ^ 2) eta)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) eta)
    (hV : 0 < variance (id : ℝ → ℝ) eta)
    (k : ℕ) (s : Finset (Fin k)) (a : ℝ) (ha : 0 < a)
    (hmean : (k : ℝ) * |∫ z : ℝ, z ∂eta| ≤ a / 2)
    (hthird : 16384 * (∫ z : ℝ, |z - ∫ y : ℝ, y ∂eta| ^ 3 ∂eta) ≤
      a * variance (id : ℝ → ℝ) eta) :
    (1 / 4 : ℝ) ≤ (Measure.pi (fun _ : Fin k => eta)).real
      {x : Shao.Path k | -a ≤ ∑ i ∈ s, x i} := by
  classical
  let P := Measure.pi (fun _ : Fin k => eta)
  let m := Fintype.card s
  let e : Fin m ≃ s := (Fintype.equivFin s).symm
  let X : Fin m → Shao.Path k → ℝ := fun i x => x (e i).val
  have hX (i : Fin m) : Measurable (X i) := measurable_pi_apply (e i).val
  have hI : iIndepFun (fun i : Fin k => Function.eval i) P :=
    iIndepFun_pi (fun _ : Fin k => measurable_id.aemeasurable)
  have hIX : iIndepFun X P :=
    hI.precomp (Subtype.val_injective.comp e.injective)
  have hLaw (i : Fin m) : IdentDistrib (X i) (id : ℝ → ℝ) P eta := by
    refine ⟨(hX i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    exact (measurePreserving_eval (fun _ : Fin k => eta) (e i).val).map_eq.trans
      Measure.map_id.symm
  have hmap := iid_samplePath_map_eq_pi hX hIX hLaw
  have hsum (x : Shao.Path k) : Shao.prefixSum (samplePath X x) m = ∑ i ∈ s, x i := by
    simp only [Shao.prefixSum_length, samplePath, X]
    rw [e.sum_comp (fun i : s => x i.val), Finset.sum_coe_sort]
  have hcard : m ≤ k := by
    dsimp [m]
    simpa only [Fintype.card_coe, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_le_card (Finset.subset_univ s))
  have hmean' : (m : ℝ) * |∫ z : ℝ, z ∂eta| ≤ a / 2 :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (abs_nonneg _)).trans hmean
  have h := bgt_iid_completion_probability eta h2 h3 hV m a ha hmean' hthird
  rw [← hmap, Measure.real_def, Measure.map_apply (measurable_samplePath hX)
    (measurableSet_le measurable_const (Shao.measurable_prefixSum m))] at h
  simpa only [Set.preimage_setOf_eq, hsum, Measure.real_def, P] using h

private theorem bgt_prefix_restriction
    (k j i : ℕ) (hij : i ≤ j) (x : Shao.Path k) :
    let s := Finset.univ.filter (fun r : Fin k => r.val < j)
    Shao.prefixSum x i = ∑ r : s, if r.val.val < i then x r.val else 0 := by
  classical
  dsimp only
  rw [Finset.sum_coe_sort (Finset.univ.filter (fun r : Fin k => r.val < j))
    (fun r : Fin k => if r.val < i then x r else 0)]
  simp only [Shao.prefixSum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : r.val < i
  · have hrj : r.val < j := lt_of_lt_of_le hr hij
    simp only [hr, hrj, ite_true]
  · by_cases hrj : r.val < j <;> simp only [hr, hrj, ite_false, ite_true]

private theorem bgt_prefix_suffix_indep
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (k j : ℕ) (b a : ℝ) :
    let s := Finset.univ.filter (fun r : Fin k => r.val < j)
    IndepSet {x : Shao.Path k | b ≤ Shao.prefixSum x j ∧
      ∀ i : ℕ, 1 ≤ i → i < j → Shao.prefixSum x i < b}
      {x : Shao.Path k | -a ≤ ∑ r ∈ sᶜ, x r}
      (Measure.pi (fun _ : Fin k => eta)) := by
  classical
  let P := Measure.pi (fun _ : Fin k => eta)
  let s := Finset.univ.filter (fun r : Fin k => r.val < j)
  let L : (s → ℝ) → ℕ → ℝ := fun x i => ∑ r : s, if r.val.val < i then x r else 0
  let C : Set (s → ℝ) := {x | b ≤ L x j ∧
    ∀ i : ℕ, 1 ≤ i → i < j → L x i < b}
  let E : Set ((sᶜ : Finset (Fin k)) → ℝ) :=
    {x | -a ≤ ∑ r : (sᶜ : Finset (Fin k)), x r}
  have hL (i : ℕ) : Measurable (fun x : s → ℝ => L x i) := by
    dsimp [L]
    fun_prop
  have hC : MeasurableSet C := by
    simp only [C, Set.setOf_and, Set.setOf_forall]
    exact (measurableSet_le measurable_const (hL j)).inter
      (MeasurableSet.iInter fun i : ℕ => MeasurableSet.iInter fun _ : 1 ≤ i =>
        MeasurableSet.iInter fun _ : i < j => measurableSet_lt (hL i) measurable_const)
  have hE : MeasurableSet E := by
    apply measurableSet_le measurable_const
    fun_prop
  have hI : iIndepFun (fun i : Fin k => Function.eval i) P :=
    iIndepFun_pi (fun _ : Fin k => measurable_id.aemeasurable)
  have hInd := hI.indepFun_finset s sᶜ disjoint_compl_right
    (fun i => measurable_pi_apply i)
  have hIndSet := (indepFun_iff_indepSet_preimage
    (Measurable.of_eval fun r => measurable_pi_apply r.val)
    (Measurable.of_eval fun r => measurable_pi_apply r.val)).mp hInd C E hC hE
  have hpre : (fun x : Shao.Path k => fun r : s => x r.val) ⁻¹' C =
      {x : Shao.Path k | b ≤ Shao.prefixSum x j ∧
        ∀ i : ℕ, 1 ≤ i → i < j → Shao.prefixSum x i < b} := by
    ext x
    have hh (i : ℕ) (hi : i ≤ j) : L (fun r : s => x r.val) i = Shao.prefixSum x i :=
      (bgt_prefix_restriction k j i hi x).symm
    change (b ≤ L _ j ∧ ∀ i : ℕ, 1 ≤ i → i < j → L _ i < b) ↔ _
    rw [hh j le_rfl]
    constructor
    · rintro ⟨hb, hx⟩
      refine ⟨hb, fun i hi hij => ?_⟩
      rw [← hh i hij.le]
      exact hx i hi hij
    · rintro ⟨hb, hx⟩
      refine ⟨hb, fun i hi hij => ?_⟩
      rw [hh i hij.le]
      exact hx i hi hij
  have hsuf : (fun x : Shao.Path k => fun r : (sᶜ : Finset (Fin k)) => x r.val) ⁻¹' E =
      {x : Shao.Path k | -a ≤ ∑ r ∈ sᶜ, x r} := by
    ext x
    change (-a ≤ ∑ r : (sᶜ : Finset (Fin k)), x r.val) ↔ _
    rw [Finset.sum_coe_sort]
    rfl
  rw [hpre, hsuf] at hIndSet
  exact hIndSet

private theorem bgt_actual_max_completion
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (h2 : Integrable (fun z : ℝ => z ^ 2) eta)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) eta)
    (hV : 0 < variance (id : ℝ → ℝ) eta)
    (k : ℕ) (hk : 0 < k) (a b : ℝ) (ha : 0 < a)
    (hmean : (k : ℝ) * |∫ z : ℝ, z ∂eta| ≤ a / 2)
    (hthird : 16384 * (∫ z : ℝ, |z - ∫ y : ℝ, y ∂eta| ^ 3 ∂eta) ≤
      a * variance (id : ℝ → ℝ) eta) :
    (Measure.pi (fun _ : Fin k => eta)).real
      {x : Shao.Path k | b ≤ Shao.upperMax x hk} ≤
      4 * (Measure.pi (fun _ : Fin k => eta)).real
        {x : Shao.Path k | b - a ≤ Shao.prefixSum x k} := by
  classical
  let P := Measure.pi (fun _ : Fin k => eta)
  let s : Fin k → Finset (Fin k) := fun j => Finset.univ.filter (fun r => r.val < j.val + 1)
  let R : Fin k → Shao.Path k → ℝ := fun j x => ∑ r ∈ (s j)ᶜ, x r
  have hR (j : Fin k) : Measurable (R j) := by dsimp [R]; fun_prop
  have hadd (j : Fin k) (x : Shao.Path k) :
      Shao.prefixSum x k = Shao.prefixSum x (j.val + 1) + R j x := by
    rw [Shao.prefixSum_length]
    change (∑ r : Fin k, x r) = (∑ r ∈ s j, x r) + ∑ r ∈ (s j)ᶜ, x r
    exact (Finset.sum_add_sum_compl (s j) (fun r => x r)).symm
  have hc (j : Fin k) : (1 / 4 : ℝ) ≤ P.real {x | -a ≤ R j x} :=
    bgt_subfamily_completion_probability eta h2 h3 hV k (s j)ᶜ a ha hmean hthird
  have hi (j : Fin k) : IndepSet
      {x : Shao.Path k | b ≤ Shao.prefixSum x (j.val + 1) ∧
        ∀ i : ℕ, 1 ≤ i → i < j.val + 1 → Shao.prefixSum x i < b}
      {x : Shao.Path k | -a ≤ R j x} P :=
    bgt_prefix_suffix_indep eta k (j.val + 1) b a
  have h := bgt_first_crossing_completion P k (fun j x => Shao.prefixSum x j) R
    Shao.measurable_prefixSum hR a b (1 / 4) (by norm_num) hadd hc hi
  have he : {x : Shao.Path k | b ≤ Shao.upperMax x hk} =
      {x : Shao.Path k | ∃ j : ℕ, 1 ≤ j ∧ j ≤ k ∧ b ≤ Shao.prefixSum x j} := by
    ext x
    exact Shao.upperMax_ge_iff x hk b
  rw [he]
  simpa only [show (1 / 4 : ℝ)⁻¹ = 4 by norm_num] using h

private theorem bgt_centered_third_pos
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (h : ℝ) (hs : ∀ᵐ z : ℝ ∂eta, |z| ≤ h)
    (hV : 0 < variance (id : ℝ → ℝ) eta) :
    0 < ∫ z : ℝ, |z - ∫ y : ℝ, y ∂eta| ^ 3 ∂eta := by
  have hn : 0 ≤ ∫ z : ℝ, |z - ∫ y : ℝ, y ∂eta| ^ 3 ∂eta :=
    integral_nonneg fun z => pow_nonneg (abs_nonneg _) 3
  by_contra hbad
  have hz : (∫ z : ℝ, |z - ∫ y : ℝ, y ∂eta| ^ 3 ∂eta) = 0 := by linarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun z : ℝ => pow_nonneg (abs_nonneg _) 3)
    (bgt_centered_third eta h hs).1).1 hz
  have he : (id : ℝ → ℝ) =ᵐ[eta] (fun _ => ∫ y : ℝ, y ∂eta) := by
    filter_upwards [hae] with z hz
    exact sub_eq_zero.mp (abs_eq_zero.mp (eq_zero_of_pow_eq_zero hz))
  have hv := variance_congr he
  have hv0 : variance (fun _ : ℝ => ∫ y : ℝ, y ∂eta) eta = 0 := by
    rw [variance_eq_sub (memLp_const _)]
    simp
  linarith

private theorem bgt_completion_correction
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (D : ℝ) (hD : 1 ≤ D) (k : ℕ) (hk : 0 < k) (u : ℝ) (hu : 1 ≤ u)
    (hs : ∀ᵐ z : ℝ ∂eta, |z| ≤ 1 / u)
    (h2 : Integrable (fun z : ℝ => z ^ 2) eta)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) eta)
    (hvL : (1 / 4 : ℝ) ≤ (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta))
    (hvU : (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta) ≤ 4)
    (hmean : (k : ℝ) * |∫ z : ℝ, z ∂eta| ≤ D / u)
    (hthird : (k : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂eta) ≤ D / u ^ 3)
    (hlarge : 8 * D ≤ u ^ 2) :
    ∃ a : ℝ, 0 < a ∧ a ≤ (1048578 : ℝ) * D / u ∧
      ∀ b : ℝ, (Measure.pi (fun _ : Fin k => eta)).real
        {x : Shao.Path k | b ≤ Shao.upperMax x hk} ≤
        4 * (Measure.pi (fun _ : Fin k => eta)).real
          {x : Shao.Path k | b - a ≤ Shao.prefixSum x k} := by
  let mu : ℝ := ∫ z : ℝ, z ∂eta
  let V : ℝ := variance (id : ℝ → ℝ) eta
  let m3 : ℝ := ∫ z : ℝ, |z - mu| ^ 3 ∂eta
  obtain ⟨_, _, hv, _, hm3⟩ :=
    bgt_centered_budgets eta D hD k u hu hs h2 hvL hvU hmean hthird hlarge
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hV : 0 < V := by
    change (1 / 8 : ℝ) ≤ (k : ℝ) * V at hv
    by_contra hbad
    have hh := mul_nonpos_of_nonneg_of_nonpos hkpos.le (le_of_not_gt hbad)
    linarith
  have hm3pos : 0 < m3 := bgt_centered_third_pos eta (1 / u) hs hV
  let a : ℝ := 2 * (k : ℝ) * |mu| + 16384 * m3 / V
  have ha : 0 < a := by dsimp [a]; positivity
  have hmeana : (k : ℝ) * |mu| ≤ a / 2 := by
    have hnn : 0 ≤ 16384 * m3 / V := by positivity
    dsimp [a]
    linarith
  have hthirda : 16384 * m3 ≤ a * V := by
    dsimp [a]
    rw [add_mul, div_mul_cancel₀ _ hV.ne']
    nlinarith [mul_nonneg (mul_nonneg hkpos.le (abs_nonneg mu)) hV.le]
  have hmratio : m3 / V ≤ 64 * D / u ^ 3 := by
    apply (div_le_iff₀ hV).2
    change (k : ℝ) * m3 ≤ 8 * D / u ^ 3 at hm3
    change (1 / 8 : ℝ) ≤ (k : ℝ) * V at hv
    have hprod := mul_le_mul_of_nonneg_right hv hm3pos.le
    have hscaled := mul_le_mul_of_nonneg_right hm3 hV.le
    calc
      m3 = 8 * ((1 / 8 : ℝ) * m3) := by ring
      _ ≤ 8 * (((k : ℝ) * V) * m3) := mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = 8 * (((k : ℝ) * m3) * V) := by ring
      _ ≤ 8 * ((8 * D / u ^ 3) * V) := mul_le_mul_of_nonneg_left hscaled (by norm_num)
      _ = _ := by ring
  have hu0 : 0 < u := by linarith
  have hucube : D / u ^ 3 ≤ D / u := by
    apply div_le_div_of_nonneg_left (by linarith) hu0
    nlinarith [mul_nonneg (show 0 ≤ u - 1 by linarith) (show 0 ≤ u + 1 by linarith)]
  have haU : a ≤ 1048578 * D / u := by
    have hmratio' : m3 / V ≤ 64 * (D / u) := by
      calc
        _ ≤ 64 * D / u ^ 3 := hmratio
        _ = 64 * (D / u ^ 3) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hucube (by norm_num)
    have hr := mul_le_mul_of_nonneg_left hmratio' (by norm_num : (0 : ℝ) ≤ 16384)
    change (k : ℝ) * |mu| ≤ D / u at hmean
    calc
      a = 2 * ((k : ℝ) * |mu|) + 16384 * (m3 / V) := by dsimp [a]; ring
      _ ≤ 2 * (D / u) + 16384 * (64 * (D / u)) :=
        add_le_add (mul_le_mul_of_nonneg_left hmean (by norm_num)) hr
      _ = _ := by ring
  refine ⟨a, ha, haU, fun b => ?_⟩
  exact bgt_actual_max_completion eta h2 h3 hV k hk a b ha hmeana hthirda

private theorem bgt_exp_taylor (r R : ℝ) (hR : |r| ≤ R) :
    Real.exp r ≤ 1 + r + r ^ 2 / 2 + Real.exp R * |r| ^ 3 / 6 := by
  by_cases hr : r = 0
  · subst r
    simp
  let F : ℝ → ℝ := fun x => Real.exp (1 * x)
  have hF (n : ℕ) : iteratedDeriv n F = Real.exp := by
    dsimp [F]
    simp only [one_mul]
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
  have hcont : ContDiff ℝ 3 F := by dsimp [F]; fun_prop
  obtain ⟨t, ht, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := F) (x₀ := 0) (x := r) (n := 2) (Ne.symm hr) hcont.contDiffOn
  have hwithin (k : ℕ) : iteratedDerivWithin k F (Set.uIcc 0 r) 0 = iteratedDeriv k F 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (Ne.symm hr))
      (by dsimp [F]; fun_prop : ContDiffAt ℝ k F 0) Set.left_mem_uIcc
  have htaylor : taylorWithinEval F 2 (Set.uIcc 0 r) 0 r = 1 + r + r ^ 2 / 2 := by
    rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval,
      hwithin 1, hwithin 2]
    rw [hF 1, hF 2]
    norm_num [F]
    ring
  rw [htaylor] at hrem
  have htR : t ≤ R := by
    change min 0 r < t ∧ t < max 0 r at ht
    have hRp : 0 ≤ R := (abs_nonneg r).trans hR
    have hrR : r ≤ R := (le_abs_self r).trans hR
    exact ht.2.le.trans (max_le hRp hrR)
  have hderiv : |iteratedDeriv 3 F t| ≤ Real.exp R := by
    rw [hF 3, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr htR
  have hbound : |F r - (1 + r + r ^ 2 / 2)| ≤ Real.exp R * |r| ^ 3 / 6 := by
    rw [hrem, abs_div, abs_mul, abs_pow]
    norm_num
    gcongr
  change Real.exp r ≤ _
  simp only [F, one_mul] at hbound
  linarith [le_abs_self (Real.exp r - (1 + r + r ^ 2 / 2))]

private theorem bgt_pi_withDensity
    (eta : Measure ℝ) [IsProbabilityMeasure eta] (k : ℕ)
    (w : ℝ → ℝ≥0∞) (hw : Measurable w)
    (hprob : IsProbabilityMeasure (eta.withDensity w)) :
    Measure.pi (fun _ : Fin k => eta.withDensity w) =
      (Measure.pi (fun _ : Fin k => eta)).withDensity (fun x => ∏ i, w (x i)) := by
  classical
  letI : IsProbabilityMeasure (eta.withDensity w) := hprob
  let P := Measure.pi (fun _ : Fin k => eta)
  apply Measure.pi_eq
  intro s hs
  have hsPi : MeasurableSet (Set.pi Set.univ s) :=
    MeasurableSet.pi (Set.to_countable _) (fun i _ => hs i)
  rw [withDensity_apply _ hsPi, ← lintegral_indicator hsPi]
  have hprod : (Set.pi Set.univ s).indicator (fun x : Shao.Path k => ∏ i, w (x i)) =
      (fun x : Shao.Path k => ∏ i, (s i).indicator w (x i)) := by
    funext x
    by_cases hx : ∀ i, x i ∈ s i
    · rw [Set.indicator_of_mem (by simpa only [Set.mem_pi, Set.mem_univ, forall_const] using hx)]
      exact Finset.prod_congr rfl (fun i _ => (Set.indicator_of_mem (hx i) w).symm)
    · rw [Set.indicator_of_notMem (by
        simpa only [Set.mem_pi, Set.mem_univ, forall_const] using hx)]
      obtain ⟨i, hi⟩ := not_forall.mp hx
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi w)
  rw [hprod]
  let X : Fin k → Shao.Path k → ℝ≥0∞ := fun i x => (s i).indicator w (x i)
  have hmX (i : Fin k) : Measurable (X i) :=
    (hw.indicator (hs i)).comp (measurable_pi_apply i)
  have hIX : iIndepFun X P :=
    iIndepFun_pi (fun i : Fin k => (hw.indicator (hs i)).aemeasurable)
  have hfactor := lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ X hIX hmX
  have hcoord (i : Fin k) : (∫⁻ x : Shao.Path k, X i x ∂P) =
      eta.withDensity w (s i) := by
    rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]
    have hmap := (measurePreserving_eval (fun _ : Fin k => eta) i).map_eq
    rw [← hmap, lintegral_map (hw.indicator (hs i)) (measurable_pi_apply i)]
  simpa only [hcoord, X] using hfactor

private theorem bgt_centered_log_normalizer
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Ω → ℝ) (hF : Measurable F)
    (h1 : Integrable F P) (h2 : Integrable (fun x => F x ^ 2) P)
    (h3 : Integrable (fun x => |F x| ^ 3) P)
    (hmean : (∫ x, F x ∂P) = 0)
    (h lam : ℝ) (hlam : 0 ≤ lam)
    (hs : ∀ᵐ x ∂P, |F x| ≤ h) (hsize : lam * h ≤ 64) :
    let q := ∫ x, Real.exp (lam * F x) ∂P
    Integrable (fun x => Real.exp (lam * F x)) P ∧ 0 < q ∧
      Real.log q ≤ (lam ^ 2 / 2) * (∫ x, F x ^ 2 ∂P) +
        (Real.exp 64 * lam ^ 3 / 6) * (∫ x, |F x| ^ 3 ∂P) := by
  let q := ∫ x, Real.exp (lam * F x) ∂P
  have hrange : ∀ᵐ x ∂P, |lam * F x| ≤ 64 := by
    filter_upwards [hs] with x hx
    rw [abs_mul, abs_of_nonneg hlam]
    exact (mul_le_mul_of_nonneg_left hx hlam).trans hsize
  have hW : Integrable (fun x => Real.exp (lam * F x)) P := by
    refine (integrable_const (Real.exp 64)).mono' ((hF.const_mul lam).exp.aestronglyMeasurable) ?_
    filter_upwards [hrange] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans hx)
  have hq : 0 < q := integral_exp_pos hW
  let c2 : ℝ := lam ^ 2 / 2
  let c3 : ℝ := Real.exp 64 * lam ^ 3 / 6
  have hpoly : Integrable (fun x => 1 + lam * F x + c2 * F x ^ 2 + c3 * |F x| ^ 3) P :=
    (((integrable_const 1).add (h1.const_mul lam)).add (h2.const_mul c2)).add (h3.const_mul c3)
  have htaylor : ∀ᵐ x ∂P, Real.exp (lam * F x) ≤
      1 + lam * F x + c2 * F x ^ 2 + c3 * |F x| ^ 3 := by
    filter_upwards [hrange] with x hx
    have ht := bgt_exp_taylor (lam * F x) 64 hx
    rw [abs_mul, abs_of_nonneg hlam, mul_pow, mul_pow] at ht
    convert ht using 1 <;> dsimp [c2, c3] <;> ring
  have hi := integral_mono_ae hW hpoly htaylor
  rw [integral_add (f := fun x => 1 + lam * F x + c2 * F x ^ 2)
      (g := fun x => c3 * |F x| ^ 3)
      (((integrable_const 1).add (h1.const_mul lam)).add (h2.const_mul c2))
      (h3.const_mul c3),
    integral_add (f := fun x => 1 + lam * F x) (g := fun x => c2 * F x ^ 2)
      ((integrable_const 1).add (h1.const_mul lam)) (h2.const_mul c2),
    integral_add (f := fun _ => 1) (g := fun x => lam * F x)
      (integrable_const 1) (h1.const_mul lam), integral_const_mul,
    integral_const_mul, integral_const_mul, hmean] at hi
  simp only [integral_const, probReal_univ, one_smul, mul_zero, add_zero] at hi
  refine ⟨hW, hq, ?_⟩
  have hlog := Real.log_le_sub_one_of_pos hq
  change q ≤ 1 + c2 * (∫ x, F x ^ 2 ∂P) + c3 * (∫ x, |F x| ^ 3 ∂P) at hi
  change Real.log q ≤ c2 * (∫ x, F x ^ 2 ∂P) + c3 * (∫ x, |F x| ^ 3 ∂P)
  linarith

private theorem bgt_pi_tilt_inverse_density
    (eta : Measure ℝ) [IsProbabilityMeasure eta] (k : ℕ)
    (f : ℝ → ℝ) (hf : Measurable f)
    (hW : Integrable (fun z => Real.exp (f z)) eta) :
    let Z := ∫ z, Real.exp (f z) ∂eta
    let rho := eta.tilted f
    Measure.pi (fun _ : Fin k => eta) =
      (Measure.pi (fun _ : Fin k => rho)).withDensity
        (fun x => ENNReal.ofReal (Z ^ k * Real.exp (-(∑ i, f (x i))))) := by
  classical
  let Z := ∫ z, Real.exp (f z) ∂eta
  let rho := eta.tilted f
  have hZ : 0 < Z := integral_exp_pos hW
  letI : IsProbabilityMeasure rho := isProbabilityMeasure_tilted hW
  have hinverse : rho.tilted (-f) = eta := tilted_neg_same hW
  have hnorm : (∫ z, Real.exp ((-f) z) ∂rho) = Z⁻¹ := by
    rw [integral_exp_tilted]
    simp only [Pi.add_apply, Pi.neg_apply, add_neg_cancel, Real.exp_zero, integral_const,
      probReal_univ, one_smul, one_div]
    rfl
  have hprob : IsProbabilityMeasure
      (rho.withDensity (fun z => ENNReal.ofReal (Real.exp ((-f) z) /
        (∫ y, Real.exp ((-f) y) ∂rho)))) := by
    change IsProbabilityMeasure (rho.tilted (-f))
    rw [hinverse]
    infer_instance
  have h := bgt_pi_withDensity rho k
    (fun z => ENNReal.ofReal (Real.exp ((-f) z) / (∫ y, Real.exp ((-f) y) ∂rho)))
    (by fun_prop) hprob
  change Measure.pi (fun _ : Fin k => rho.tilted (-f)) = _ at h
  rw [hinverse, hnorm] at h
  refine h.trans ?_
  apply withDensity_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (∏ i : Fin k, ENNReal.ofReal (Real.exp ((-f) (x i)) / Z⁻¹)) =
      ENNReal.ofReal (Z ^ k * Real.exp (-(∑ i, f (x i))))
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
    congr 1
    simp only [Pi.neg_apply, div_inv_eq_mul, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← Real.exp_sum, ← Finset.sum_neg_distrib]
    ring

private theorem bgt_density_event_le
    {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (w : Ω → ℝ) (hPQ : P = Q.withDensity (fun x => ENNReal.ofReal (w x)))
    (A : Set Ω) (hA : MeasurableSet A) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ x ∈ A, w x ≤ K) : P.real A ≤ K * Q.real A := by
  have hmeasure : P A ≤ ENNReal.ofReal K * Q A := by
    rw [hPQ, withDensity_apply _ hA]
    calc
      _ ≤ ∫⁻ _x in A, ENNReal.ofReal K ∂Q := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hA] with x hx
        exact ENNReal.ofReal_le_ofReal (hbound x hx)
      _ = _ := by simp only [lintegral_const, Measure.restrict_apply_univ]
  have hreal := ENNReal.toReal_mono (by finiteness) hmeasure
  simpa only [Measure.real_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK] using hreal

private theorem bgt_weighted_bins
    {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : Ω → ℝ) (hX : Measurable X) (K lam t A delta : ℝ)
    (hK : 0 ≤ K) (hlam : 0 < lam) (hA : 0 ≤ A) (hdelta : 0 ≤ delta)
    (hPQ : P = Q.withDensity (fun x => ENNReal.ofReal
      (K * Real.exp (-lam * (X x - t)))))
    (hinterval : ∀ a b : ℝ, a ≤ b →
      Q.real {x | a ≤ X x ∧ X x < b} ≤ A * ((b - a) + delta)) :
    P.real {x | t ≤ X x} ≤ K * (A * (lam⁻¹ + delta)) / (1 - Real.exp (-1)) := by
  classical
  let q := Real.exp (-1)
  let B : ℕ → Set Ω := fun j =>
    {x | t + (j : ℝ) / lam ≤ X x ∧ X x < t + ((j : ℝ) + 1) / lam}
  let E : ℕ → Set Ω := fun N => {x | t + (N : ℝ) / lam ≤ X x}
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hden : 0 < 1 - q := by linarith
  have hexp (j : ℕ) : Real.exp (-(j : ℝ)) = q ^ j := by
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hdensity (j : ℕ) (x : Ω) (hx : t + (j : ℝ) / lam ≤ X x) :
      K * Real.exp (-lam * (X x - t)) ≤ K * q ^ j := by
    rw [← hexp]
    apply mul_le_mul_of_nonneg_left _ hK
    apply Real.exp_le_exp.mpr
    have hh : (j : ℝ) ≤ lam * (X x - t) := by
      have h := (div_le_iff₀ hlam).1 (show (j : ℝ) / lam ≤ X x - t by linarith)
      nlinarith only [h]
    linarith
  have hBin (j : ℕ) : P.real (B j) ≤ K * q ^ j * (A * (lam⁻¹ + delta)) := by
    have hmeas : MeasurableSet (B j) :=
      (measurableSet_le measurable_const hX).inter (measurableSet_lt hX measurable_const)
    have hd := bgt_density_event_le P Q _ hPQ (B j) hmeas (K * q ^ j)
      (mul_nonneg hK (pow_nonneg hq0 j)) (fun x hx => hdensity j x hx.1)
    have hi := hinterval (t + (j : ℝ) / lam) (t + ((j : ℝ) + 1) / lam)
      (by
        have hi : (j : ℝ) / lam ≤ ((j : ℝ) + 1) / lam :=
          div_le_div_of_nonneg_right (by linarith) hlam.le
        linarith)
    have hlength : (t + ((j : ℝ) + 1) / lam) - (t + (j : ℝ) / lam) = lam⁻¹ := by ring
    rw [hlength] at hi
    exact hd.trans (mul_le_mul_of_nonneg_left hi (mul_nonneg hK (pow_nonneg hq0 j)))
  have hRest (N : ℕ) : P.real (E N) ≤ K * q ^ N := by
    have hd := bgt_density_event_le P Q _ hPQ (E N)
      (measurableSet_le measurable_const hX) (K * q ^ N)
      (mul_nonneg hK (pow_nonneg hq0 N)) (fun x hx => hdensity N x hx)
    exact hd.trans (mul_le_of_le_one_right (mul_nonneg hK (pow_nonneg hq0 N)) measureReal_le_one)
  have hgeom (N : ℕ) : (∑ j ∈ Finset.range N, q ^ j) ≤ (1 - q)⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hden).2
    have hg := geom_sum_mul q N
    nlinarith [pow_nonneg hq0 N]
  have hfinite (N : ℕ) : P.real {x | t ≤ X x} ≤
      K * (A * (lam⁻¹ + delta)) / (1 - q) + K * q ^ N := by
    have hcover : {x | t ≤ X x} ⊆ (⋃ j ∈ Finset.range N, B j) ∪ E N := by
      intro x hx
      change t ≤ X x at hx
      let y := lam * (X x - t)
      have hy : 0 ≤ y := mul_nonneg hlam.le (sub_nonneg.mpr hx)
      let j := ⌊y⌋₊
      have hjL : (j : ℝ) ≤ y := Nat.floor_le hy
      have hjU : y < (j : ℝ) + 1 := Nat.lt_floor_add_one y
      by_cases hjN : j < N
      · apply Or.inl
        apply Set.mem_iUnion.mpr
        refine ⟨j, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hjN, ?_⟩⟩
        change t + (j : ℝ) / lam ≤ X x ∧ X x < t + ((j : ℝ) + 1) / lam
        constructor
        · have h : (j : ℝ) / lam ≤ X x - t := (div_le_iff₀ hlam).2 (by
            dsimp [y] at hjL
            nlinarith only [hjL])
          linarith only [h]
        · have h : X x - t < ((j : ℝ) + 1) / lam := (lt_div_iff₀ hlam).2 (by
            dsimp [y] at hjU
            nlinarith only [hjU])
          linarith only [h]
      · apply Or.inr
        change t + (N : ℝ) / lam ≤ X x
        have hNj : (N : ℝ) ≤ j := by exact_mod_cast Nat.le_of_not_gt hjN
        have h : (N : ℝ) / lam ≤ X x - t := (div_le_iff₀ hlam).2 (by
          dsimp [y] at hjL
          nlinarith only [hNj, hjL])
        linarith only [h]
    have hcoef : 0 ≤ K * (A * (lam⁻¹ + delta)) := by positivity
    calc
      _ ≤ P.real ((⋃ j ∈ Finset.range N, B j) ∪ E N) := measureReal_mono hcover
      _ ≤ P.real (⋃ j ∈ Finset.range N, B j) + P.real (E N) := measureReal_union_le _ _
      _ ≤ (∑ j ∈ Finset.range N, P.real (B j)) + K * q ^ N :=
        add_le_add (measureReal_biUnion_finset_le _ _) (hRest N)
      _ ≤ (∑ j ∈ Finset.range N, K * q ^ j * (A * (lam⁻¹ + delta))) + K * q ^ N := by
        exact add_le_add (Finset.sum_le_sum (fun j _ => hBin j)) le_rfl
      _ = K * (A * (lam⁻¹ + delta)) * (∑ j ∈ Finset.range N, q ^ j) + K * q ^ N := by
        rw [Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ K * (A * (lam⁻¹ + delta)) * (1 - q)⁻¹ + K * q ^ N :=
        add_le_add (mul_le_mul_of_nonneg_left (hgeom N) hcoef) le_rfl
      _ = _ := by ring
  have hlim : Filter.Tendsto (fun N : ℕ => K * (A * (lam⁻¹ + delta)) / (1 - q) + K * q ^ N)
      Filter.atTop (nhds (K * (A * (lam⁻¹ + delta)) / (1 - q))) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    simpa only [mul_zero, add_zero] using (hpow.const_mul K).const_add
      (K * (A * (lam⁻¹ + delta)) / (1 - q))
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hfinite

private theorem bgt_iid_interval_total
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) eta)
    (hV : 0 < variance (id : ℝ → ℝ) eta)
    (k : ℕ) (hk : 0 < k) (L B delta : ℝ) (hL : 0 < L)
    (hB : 0 ≤ B) (hdelta : 0 ≤ delta)
    (hvar : L ≤ (k : ℝ) * variance (id : ℝ → ℝ) eta)
    (hthird : (k : ℝ) * (∫ z : ℝ, |z - ∫ y : ℝ, y ∂eta| ^ 3 ∂eta) ≤ B * delta)
    (a b : ℝ) (hab : a ≤ b) :
    (Measure.pi (fun _ : Fin k => eta)).real
      {x : Shao.Path k | a ≤ Shao.prefixSum x k ∧ Shao.prefixSum x k < b} ≤
      ((Real.sqrt L)⁻¹ + 2048 * B / (Real.sqrt L) ^ 3) * ((b - a) + delta) := by
  let V := variance (id : ℝ → ℝ) eta
  let m3 := ∫ z : ℝ, |z - ∫ y : ℝ, y ∂eta| ^ 3 ∂eta
  let tau := Real.sqrt V * Real.sqrt (k : ℝ)
  let c := Real.sqrt L
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
  have htau : 0 < tau := mul_pos (Real.sqrt_pos.mpr hV) (Real.sqrt_pos.mpr hkpos)
  have hc : 0 < c := Real.sqrt_pos.mpr hL
  have htau2 : tau ^ 2 = (k : ℝ) * V := by
    dsimp [tau]
    rw [mul_pow, Real.sq_sqrt hV.le, Real.sq_sqrt hkpos.le]
    ring
  have hc2 : c ^ 2 = L := Real.sq_sqrt hL.le
  have hct : c ≤ tau := by
    change L ≤ (k : ℝ) * V at hvar
    nlinarith
  have hden : (Real.sqrt V) ^ 3 * Real.sqrt (k : ℝ) * (k : ℝ) = tau ^ 3 := by
    dsimp [tau]
    calc
      _ = (Real.sqrt V) ^ 3 * ((Real.sqrt (k : ℝ)) ^ 2 * Real.sqrt (k : ℝ)) := by
        rw [Real.sq_sqrt hkpos.le]
        ring
      _ = _ := by ring
  have hdenpos : 0 < (Real.sqrt V) ^ 3 * Real.sqrt (k : ℝ) := by positivity
  have herrEq : 1024 * m3 / ((Real.sqrt V) ^ 3 * Real.sqrt (k : ℝ)) =
      1024 * ((k : ℝ) * m3) / tau ^ 3 := by
    apply (div_eq_div_iff hdenpos.ne' (pow_pos htau 3).ne').2
    rw [← hden]
    ring
  have herr : 1024 * m3 / ((Real.sqrt V) ^ 3 * Real.sqrt (k : ℝ)) ≤
      1024 * B * delta / c ^ 3 := by
    rw [herrEq]
    calc
      _ ≤ 1024 * (B * delta) / tau ^ 3 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hthird (by norm_num)) (by positivity)
      _ ≤ 1024 * (B * delta) / c ^ 3 :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hc 3)
          (pow_le_pow_left₀ hc.le hct 3)
      _ = _ := by ring
  have hlength : (b - a) / tau ≤ (b - a) / c :=
    div_le_div_of_nonneg_left (sub_nonneg.mpr hab) hc hct
  have hi := bgt_iid_interval_mass eta h3 hV k hk a b hab
  change _ ≤ (b - a) / tau + 2 * (1024 * m3 /
    ((Real.sqrt V) ^ 3 * Real.sqrt (k : ℝ))) at hi
  have hbound := hi.trans (add_le_add hlength (mul_le_mul_of_nonneg_left herr (by norm_num)))
  let c2 : ℝ := 2048 * B / c ^ 3
  have hc2pos : 0 ≤ c2 := by dsimp [c2]; positivity
  have hnn1 : 0 ≤ delta / c := div_nonneg hdelta hc.le
  have hnn2 : 0 ≤ c2 * (b - a) := mul_nonneg hc2pos (sub_nonneg.mpr hab)
  change _ ≤ (c⁻¹ + c2) * ((b - a) + delta)
  calc
    _ ≤ (b - a) / c + 2 * (1024 * B * delta / c ^ 3) := hbound
    _ ≤ (b - a) / c + 2 * (1024 * B * delta / c ^ 3) + delta / c + c2 * (b - a) := by linarith
    _ = _ := by dsimp [c2]; ring

private theorem bgt_linear_tilt_data
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (D : ℝ) (hD : 1 ≤ D) (k : ℕ) (hk : 0 < k) (u : ℝ) (hu : 1 ≤ u)
    (hs : ∀ᵐ z : ℝ ∂eta, |z| ≤ 1 / u)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) eta)
    (hvar : (1 / 8 : ℝ) ≤ (k : ℝ) * variance (id : ℝ → ℝ) eta)
    (hthird : (k : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂eta) ≤ D / u ^ 3)
    (lam : ℝ) (hlam : 0 ≤ lam) (hlamU : lam ≤ 32 * u) :
    let rho := eta.tilted (fun z => lam * z)
    let L := Real.exp (-128) / 8
    let B := 64 * Real.exp 128 * D
    IsProbabilityMeasure rho ∧
      (∀ a b : ℝ, a ≤ b →
        (Measure.pi (fun _ : Fin k => rho)).real
          {x : Shao.Path k | a ≤ Shao.prefixSum x k ∧ Shao.prefixSum x k < b} ≤
          ((Real.sqrt L)⁻¹ + 2048 * B / (Real.sqrt L) ^ 3) * ((b - a) + 1 / u ^ 3)) := by
  let rho := eta.tilted (fun z => lam * z)
  let L := Real.exp (-128) / 8
  let B := 64 * Real.exp 128 * D
  have hu0 : 0 < u := by linarith
  have hh : 0 < 1 / u := by positivity
  have hg := boundedQuadraticTilt_density_moments eta (1 / u) lam 0 hh (by norm_num) hs
  dsimp only at hg
  simp only [zero_mul, mul_zero, sub_zero, add_zero, abs_of_nonneg hlam] at hg
  obtain ⟨_, _, _, _, _, _, hprob, _, _, hsR, _, _, _, hcompare, hp,
    _, _, _, _, hvlo, _, _⟩ := hg
  change IsProbabilityMeasure rho at hprob
  letI : IsProbabilityMeasure rho := hprob
  change (∀ᵐ z : ℝ ∂rho, |z| ≤ 1 / u) at hsR
  have hsize : 2 * (lam * (1 / u)) ≤ 128 := by
    have hh := (div_le_iff₀ hu0).2 hlamU
    change lam / u ≤ 32 at hh
    calc
      2 * (lam * (1 / u)) = 2 * (lam / u) := by ring
      _ ≤ 2 * 32 := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ ≤ 128 := by norm_num
  have heU : Real.exp (2 * (lam * (1 / u))) ≤ Real.exp 128 := Real.exp_le_exp.mpr hsize
  have heL : Real.exp (-128) ≤ Real.exp (-(2 * (lam * (1 / u)))) :=
    Real.exp_le_exp.mpr (by linarith)
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hVL : L ≤ (k : ℝ) * variance (id : ℝ → ℝ) rho := by
    calc
      L = Real.exp (-128) * (1 / 8) := by dsimp [L]; ring
      _ ≤ Real.exp (-128) * ((k : ℝ) * variance (id : ℝ → ℝ) eta) :=
        mul_le_mul_of_nonneg_left hvar (Real.exp_pos _).le
      _ ≤ Real.exp (-(2 * (lam * (1 / u)))) * ((k : ℝ) * variance (id : ℝ → ℝ) eta) :=
        mul_le_mul_of_nonneg_right heL (mul_nonneg hkpos.le (variance_nonneg _ _))
      _ = (k : ℝ) * (Real.exp (-(2 * (lam * (1 / u)))) * variance (id : ℝ → ℝ) eta) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hvlo hkpos.le
  have hVR : 0 < variance (id : ℝ → ℝ) rho := by
    have hLpos : 0 < L := by dsimp [L]; positivity
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos hkpos.le (le_of_not_gt hn)
    linarith
  have hRaw3 : (∫ z : ℝ, |z| ^ 3 ∂rho) ≤
      Real.exp 128 * (∫ z : ℝ, |z| ^ 3 ∂eta) := by
    have hc := (hcompare (fun z : ℝ => |z| ^ 3) h3
      (Filter.Eventually.of_forall fun z => pow_nonneg (abs_nonneg z) 3)).2
    exact hc.trans (mul_le_mul_of_nonneg_right heU
      (integral_nonneg fun z => pow_nonneg (abs_nonneg z) 3))
  have hCenter3 : (k : ℝ) * (∫ z : ℝ, |z - ∫ y : ℝ, y ∂rho| ^ 3 ∂rho) ≤ B * (1 / u ^ 3) := by
    calc
      _ ≤ (k : ℝ) * (8 * (∫ z : ℝ, |z| ^ 3 ∂rho)) :=
        mul_le_mul_of_nonneg_left (bgt_centered_third rho (1 / u) hsR).2 hkpos.le
      _ ≤ (k : ℝ) * (8 * (Real.exp 128 * (∫ z : ℝ, |z| ^ 3 ∂eta))) := by gcongr
      _ = (8 * Real.exp 128) * ((k : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂eta)) := by ring
      _ ≤ (8 * Real.exp 128) * (D / u ^ 3) :=
        mul_le_mul_of_nonneg_left hthird (by positivity)
      _ ≤ B * (1 / u ^ 3) := by
        dsimp [B]
        have hp : 0 ≤ Real.exp 128 * (D / u ^ 3) := by positivity
        calc
          _ = 8 * (Real.exp 128 * (D / u ^ 3)) := by ring
          _ ≤ 64 * (Real.exp 128 * (D / u ^ 3)) :=
            mul_le_mul_of_nonneg_right (by norm_num) hp
          _ = _ := by ring
  refine ⟨hprob, fun a b hab => ?_⟩
  exact bgt_iid_interval_total rho (hp 3).2.2.2.1 hVR k hk L B (1 / u ^ 3)
    (by dsimp [L]; positivity) (by dsimp [B]; positivity) (by positivity) hVL hCenter3 a b hab

private theorem bgt_linear_log_normalizer
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (D : ℝ) (hD : 1 ≤ D) (k : ℕ) (u : ℝ) (hu : 1 ≤ u)
    (hs : ∀ᵐ z : ℝ ∂eta, |z| ≤ 1 / u)
    (h2 : Integrable (fun z : ℝ => z ^ 2) eta)
    (hcenter : ∀ᵐ z : ℝ ∂eta, |z - ∫ y : ℝ, y ∂eta| ≤ 2 / u)
    (hthird : (k : ℝ) * (∫ z : ℝ, |z - ∫ y : ℝ, y ∂eta| ^ 3 ∂eta) ≤ 8 * D / u ^ 3)
    (lam : ℝ) (hlam : 0 ≤ lam) (hlamU : lam ≤ 32 * u) :
    let Z := ∫ z, Real.exp (lam * z) ∂eta
    Integrable (fun z => Real.exp (lam * z)) eta ∧ 0 < Z ∧
      (k : ℝ) * Real.log Z ≤ lam * ((k : ℝ) * (∫ z : ℝ, z ∂eta)) +
        lam ^ 2 * ((k : ℝ) * variance (id : ℝ → ℝ) eta) / 2 +
        262144 * Real.exp 64 * D := by
  let mu := ∫ z : ℝ, z ∂eta
  let m3 := ∫ z : ℝ, |z - mu| ^ 3 ∂eta
  let V := variance (id : ℝ → ℝ) eta
  let q := ∫ z : ℝ, Real.exp (lam * (z - mu)) ∂eta
  let Z := ∫ z : ℝ, Real.exp (lam * z) ∂eta
  have hu0 : 0 < u := by linarith
  have h1 : Integrable (fun z : ℝ => z) eta := by
    simpa only [pow_one] using (bgt_powers eta (1 / u) hs 1).1
  have hY1 : Integrable (fun z : ℝ => z - mu) eta := h1.sub (integrable_const mu)
  have hY2 : Integrable (fun z : ℝ => (z - mu) ^ 2) eta := by
    have hh := (h2.sub (h1.const_mul (2 * mu))).add (integrable_const (mu ^ 2))
    convert hh using 1
    funext z
    change (z - mu) ^ 2 = z ^ 2 - 2 * mu * z + mu ^ 2
    ring
  have hY3 : Integrable (fun z : ℝ => |z - mu| ^ 3) eta :=
    (bgt_centered_third eta (1 / u) hs).1
  have hYmean : (∫ z : ℝ, z - mu ∂eta) = 0 := by
    rw [integral_sub h1 (integrable_const mu)]
    simp only [integral_const, probReal_univ, one_smul]
    simp only [mu, sub_self]
  have hYvar : (∫ z : ℝ, (z - mu) ^ 2 ∂eta) = V := by
    simpa only [id_eq] using (variance_eq_integral (μ := eta) aemeasurable_id).symm
  have hsize : lam * (2 / u) ≤ 64 := by
    rw [show lam * (2 / u) = (2 * lam) / u by ring]
    apply (div_le_iff₀ hu0).2 ?_
    nlinarith
  have hqdata := bgt_centered_log_normalizer eta (fun z : ℝ => z - mu)
    (by fun_prop) hY1 hY2 hY3 hYmean (2 / u) lam hlam hcenter hsize
  obtain ⟨hqW, hqpos, hqlog⟩ := hqdata
  have hW : Integrable (fun z : ℝ => Real.exp (lam * z)) eta := by
    convert hqW.const_mul (Real.exp (lam * mu)) using 1
    funext z
    rw [← Real.exp_add]
    congr 1
    ring
  have hZpos : 0 < Z := integral_exp_pos hW
  have hqeq : q = Real.exp (-lam * mu) * Z := by
    calc
      q = ∫ z : ℝ, Real.exp (-lam * mu) * Real.exp (lam * z) ∂eta := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          change Real.exp (lam * (z - mu)) = Real.exp (-lam * mu) * Real.exp (lam * z)
          rw [← Real.exp_add]
          congr 1
          ring
      _ = _ := integral_const_mul _ _
  have hqlogeq : Real.log q = -lam * mu + Real.log Z := by
    rw [hqeq, Real.log_mul (Real.exp_ne_zero _) hZpos.ne', Real.log_exp]
  have hNNm3 : 0 ≤ (k : ℝ) * m3 :=
    mul_nonneg (Nat.cast_nonneg k) (integral_nonneg fun z => pow_nonneg (abs_nonneg _) 3)
  have hcube : lam ^ 3 ≤ (32 * u) ^ 3 := pow_le_pow_left₀ hlam hlamU 3
  change (k : ℝ) * m3 ≤ 8 * D / u ^ 3 at hthird
  have hrembound : lam ^ 3 * ((k : ℝ) * m3) ≤ 262144 * D := by
    calc
      _ ≤ (32 * u) ^ 3 * (8 * D / u ^ 3) :=
        mul_le_mul hcube hthird hNNm3 (by positivity)
      _ = _ := by field_simp; ring
  have hrem : (Real.exp 64 / 6) * (lam ^ 3 * ((k : ℝ) * m3)) ≤
      262144 * Real.exp 64 * D := by
    calc
      _ ≤ (Real.exp 64 / 6) * (262144 * D) := mul_le_mul_of_nonneg_left hrembound (by positivity)
      _ ≤ _ := by
        have hh : 0 ≤ Real.exp 64 * D := by positivity
        nlinarith only [hh]
  change Real.log q ≤ (lam ^ 2 / 2) * (∫ z : ℝ, (z - mu) ^ 2 ∂eta) +
    (Real.exp 64 * lam ^ 3 / 6) * m3 at hqlog
  rw [hYvar] at hqlog
  have htot := mul_le_mul_of_nonneg_left hqlog (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  refine ⟨hW, hZpos, ?_⟩
  change (k : ℝ) * Real.log Z ≤ _
  calc
    (k : ℝ) * Real.log Z = lam * ((k : ℝ) * mu) + (k : ℝ) * Real.log q := by rw [hqlogeq]; ring
    _ ≤ lam * ((k : ℝ) * mu) + (k : ℝ) * ((lam ^ 2 / 2) * V +
        (Real.exp 64 * lam ^ 3 / 6) * m3) := add_le_add le_rfl htot
    _ = lam * ((k : ℝ) * mu) + lam ^ 2 * ((k : ℝ) * V) / 2 +
        (Real.exp 64 / 6) * (lam ^ 3 * ((k : ℝ) * m3)) := by ring
    _ ≤ _ := add_le_add le_rfl hrem

private theorem bgt_endpoint_tilt_bound
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (D : ℝ) (hD : 1 ≤ D) (k : ℕ) (hk : 0 < k) (u : ℝ) (hu : 1 ≤ u)
    (hs : ∀ᵐ z : ℝ ∂eta, |z| ≤ 1 / u)
    (h2 : Integrable (fun z : ℝ => z ^ 2) eta)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) eta)
    (hvar : (1 / 8 : ℝ) ≤ (k : ℝ) * variance (id : ℝ → ℝ) eta)
    (hthird : (k : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂eta) ≤ D / u ^ 3)
    (hcenter : ∀ᵐ z : ℝ ∂eta, |z - ∫ y : ℝ, y ∂eta| ≤ 2 / u)
    (hcenter3 : (k : ℝ) * (∫ z : ℝ, |z - ∫ y : ℝ, y ∂eta| ^ 3 ∂eta) ≤ 8 * D / u ^ 3)
    (lam : ℝ) (hlam : 0 < lam) (hlamU : lam ≤ 32 * u) (wall : ℝ) :
    let L := Real.exp (-128) / 8
    let B := 64 * Real.exp 128 * D
    let A := (Real.sqrt L)⁻¹ + 2048 * B / (Real.sqrt L) ^ 3
    (Measure.pi (fun _ : Fin k => eta)).real
      {x : Shao.Path k | wall ≤ Shao.prefixSum x k} ≤
      Real.exp (lam * ((k : ℝ) * (∫ z : ℝ, z ∂eta)) +
        lam ^ 2 * ((k : ℝ) * variance (id : ℝ → ℝ) eta) / 2 +
        262144 * Real.exp 64 * D - lam * wall) * (A * (lam⁻¹ + 1 / u ^ 3)) /
          (1 - Real.exp (-1)) := by
  let P := Measure.pi (fun _ : Fin k => eta)
  let rho := eta.tilted (fun z => lam * z)
  let Q := Measure.pi (fun _ : Fin k => rho)
  let Z := ∫ z, Real.exp (lam * z) ∂eta
  let K := Z ^ k * Real.exp (-lam * wall)
  let L := Real.exp (-128) / 8
  let B := 64 * Real.exp 128 * D
  let A := (Real.sqrt L)⁻¹ + 2048 * B / (Real.sqrt L) ^ 3
  obtain ⟨hprob, hinterval⟩ := bgt_linear_tilt_data eta D hD k hk u hu hs h3 hvar hthird lam hlam.le hlamU
  change IsProbabilityMeasure rho at hprob
  letI : IsProbabilityMeasure rho := hprob
  obtain ⟨hW, hZ, hlog⟩ := bgt_linear_log_normalizer eta D hD k u hu hs h2 hcenter hcenter3 lam hlam.le hlamU
  change 0 < Z at hZ
  have hRN := bgt_pi_tilt_inverse_density eta k (fun z => lam * z) (by fun_prop) hW
  have hPQ : P = Q.withDensity (fun x => ENNReal.ofReal
      (K * Real.exp (-lam * (Shao.prefixSum x k - wall)))) := by
    refine hRN.trans ?_
    apply withDensity_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change ENNReal.ofReal (Z ^ k * Real.exp (-(∑ i, lam * x i))) = _
      congr 1
      have hsumeq : (∑ i : Fin k, lam * x i) = lam * Shao.prefixSum x k := by
        rw [Shao.prefixSum_length, Finset.mul_sum]
      rw [hsumeq]
      dsimp [K]
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : 0 ≤ A := by dsimp [A, L, B]; positivity
  have htail := bgt_weighted_bins P Q (fun x : Shao.Path k => Shao.prefixSum x k)
    (Shao.measurable_prefixSum k) K lam wall A (1 / u ^ 3) hK hlam hA
    (by positivity) hPQ hinterval
  have hZpow : Z ^ k = Real.exp ((k : ℝ) * Real.log Z) := by
    rw [Real.exp_nat_mul, Real.exp_log hZ]
  have hKbound : K ≤ Real.exp (lam * ((k : ℝ) * (∫ z : ℝ, z ∂eta)) +
      lam ^ 2 * ((k : ℝ) * variance (id : ℝ → ℝ) eta) / 2 +
      262144 * Real.exp 64 * D - lam * wall) := by
    dsimp [K]
    rw [hZpow, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hden : 0 < 1 - Real.exp (-1) := by
    have hh : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  exact htail.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hKbound (mul_nonneg hA (by positivity))) hden.le)

private theorem bgt_gaussian_prefactor_compare
    (z r E K : ℝ) (hz : 0 ≤ z) (hr : 0 ≤ r) (hK : 0 ≤ K)
    (hsquare : r ^ 2 - z ^ 2 ≤ E) (hratio : 1 + r ≤ K * (1 + z)) :
    Real.exp (-z ^ 2 / 2) / (1 + z) ≤
      Real.sqrt (2 * Real.pi) * Real.exp (E / 2) * K * Shao.standardNormalTail r := by
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hformula : Real.exp (-r ^ 2 / 2) = Real.sqrt (2 * Real.pi) * Shao.standardNormalDensity r := by
    simp only [Shao.standardNormalDensity, gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
    field_simp
  have hM : Real.exp (-r ^ 2 / 2) / (1 + r) ≤
      Real.sqrt (2 * Real.pi) * Shao.standardNormalTail r := by
    rw [hformula, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (Shao.standardNormal_mills_bounds r hr).1 hsqrt.le
  have hR : (1 + r) / (1 + z) ≤ K := (div_le_iff₀ (by linarith)).2 hratio
  have he : Real.exp (-z ^ 2 / 2) ≤ Real.exp (E / 2) * Real.exp (-r ^ 2 / 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ (Real.exp (E / 2) * Real.exp (-r ^ 2 / 2)) / (1 + z) :=
      div_le_div_of_nonneg_right he (by linarith)
    _ = Real.exp (E / 2) * ((1 + r) / (1 + z)) *
        (Real.exp (-r ^ 2 / 2) / (1 + r)) := by field_simp <;> ring
    _ ≤ Real.exp (E / 2) * K * (Real.sqrt (2 * Real.pi) * Shao.standardNormalTail r) := by
      gcongr
    _ = _ := by ring

private theorem bgt_wall_scalar_estimates
    (u H b t s v : ℝ) (hu : 1 ≤ u) (hH : 0 ≤ H)
    (hb : 0 ≤ b) (hbU : b ≤ 3 * u) (ht : 0 < t) (htU : t ≤ 4 * u)
    (hsL : (1 / 8 : ℝ) ≤ s) (hsU : s ≤ 4) (hvL : (1 / 4 : ℝ) ≤ v)
    (hsv : s ≤ v) (hshift : |t - b| ≤ H / u)
    (hz : 1 < t / Real.sqrt s) :
    let z := t / Real.sqrt s
    let r := b / Real.sqrt v
    r ^ 2 - z ^ 2 ≤ 56 * H ∧
      1 + r ≤ (4 + 2 * H) * (1 + z) ∧
      (t / s)⁻¹ + 1 / u ^ 3 ≤ 28 / (1 + z) := by
  let z := t / Real.sqrt s
  let r := b / Real.sqrt v
  have hu0 : 0 < u := by linarith only [hu]
  have hs0 : 0 < s := by linarith only [hsL]
  have hv0 : 0 < v := by linarith only [hvL]
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  have hvs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv0
  have hs2 : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs0.le
  have hv2 : (Real.sqrt v) ^ 2 = v := Real.sq_sqrt hv0.le
  have hsqrtL : (1 / 3 : ℝ) ≤ Real.sqrt s := by nlinarith only [hs2, hsL, hss]
  have hsqrtU : Real.sqrt s ≤ 2 := by nlinarith only [hs2, hsU, hss]
  have hvroot : (1 / 2 : ℝ) ≤ Real.sqrt v := by nlinarith only [hv2, hvL, hvs]
  have hz0 : 0 < z := div_pos ht hss
  have hr0 : 0 ≤ r := div_nonneg hb hvs.le
  have htz : z * Real.sqrt s = t := div_mul_cancel₀ _ hss.ne'
  have hrb : r ≤ 2 * b := by
    apply (div_le_iff₀ hvs).2
    nlinarith only [mul_nonneg hb (sub_nonneg.mpr hvroot)]
  have hHu : H / u ≤ H := div_le_self hH hu
  have hbt : b ≤ t + H / u := by linarith only [(abs_le.mp hshift).1]
  have htzU : t ≤ 2 * z := by
    nlinarith only [htz, mul_le_mul_of_nonneg_left hsqrtU hz0.le]
  have hrz : r ≤ 4 * z + 2 * H := by linarith only [hrb, hbt, hHu, htzU]
  have hdiff : b ^ 2 - t ^ 2 ≤ 7 * H := by
    calc
      b ^ 2 - t ^ 2 = (b - t) * (b + t) := by ring
      _ ≤ (H / u) * (b + t) :=
        mul_le_mul_of_nonneg_right (by linarith only [hbt]) (by linarith only [hb, ht])
      _ ≤ (H / u) * (7 * u) :=
        mul_le_mul_of_nonneg_left (by linarith only [hbU, htU]) (div_nonneg hH hu0.le)
      _ = _ := by field_simp <;> ring
  have hr2 : r ^ 2 = b ^ 2 / v := by dsimp [r]; rw [div_pow, hv2]
  have hz2 : z ^ 2 = t ^ 2 / s := by dsimp [z]; rw [div_pow, hs2]
  refine ⟨?_, ?_, ?_⟩
  · rw [hr2, hz2]
    calc
      b ^ 2 / v - t ^ 2 / s ≤ b ^ 2 / s - t ^ 2 / s :=
        sub_le_sub_right (div_le_div_of_nonneg_left (sq_nonneg b) hs0 hsv) _
      _ = (b ^ 2 - t ^ 2) / s := by ring
      _ ≤ 7 * H / s := div_le_div_of_nonneg_right hdiff hs0.le
      _ ≤ _ := (div_le_iff₀ hs0).2 (by nlinarith only [mul_le_mul_of_nonneg_right hsL hH])
  · nlinarith only [hrz, mul_nonneg hH hz0.le]
  · have hzU : z ≤ 12 * u := by
      nlinarith only [htz, htU, mul_le_mul_of_nonneg_left hsqrtL hz0.le]
    have hInv : (t / s)⁻¹ = Real.sqrt s / z := by
      dsimp [z]
      field_simp
      nlinarith only [hs2]
    have hfirst : (t / s)⁻¹ ≤ 2 / z := by
      rw [hInv]
      exact div_le_div_of_nonneg_right hsqrtU hz0.le
    have hu3 : u ≤ u ^ 3 := by
      have hh : 1 ≤ u ^ 2 := by nlinarith only [hu]
      have hp := mul_le_mul_of_nonneg_right hh hu0.le
      nlinarith only [hp]
    have hdelta : 1 / u ^ 3 ≤ 12 / z :=
      (div_le_div_of_nonneg_left (by norm_num) hu0 hu3).trans
        ((div_le_div_iff₀ hu0 hz0).2 (by linarith only [hzU]))
    calc
      _ ≤ 2 / z + 12 / z := add_le_add hfirst hdelta
      _ = 14 / z := by ring
      _ ≤ _ := (div_le_div_iff₀ hz0 (by linarith only [hz0])).2
        (by change 1 < z at hz; nlinarith only [hz])

theorem bounded_deterministic_wall_gaussian_upper
    (D : ℝ) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (eta : Measure ℝ), IsProbabilityMeasure eta →
        ∀ (k : ℕ) (hk : 0 < k) (u : ℝ), 1 ≤ u →
          (∀ᵐ z : ℝ ∂eta, |z| ≤ 1 / u) →
          Integrable (fun z : ℝ => z ^ 2) eta →
          Integrable (fun z : ℝ => |z| ^ 3) eta →
          (1 / 4 : ℝ) ≤ (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta) →
          (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta) ≤ 4 →
          (k : ℝ) * |∫ z : ℝ, z ∂eta| ≤ D / u →
          (k : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂eta) ≤ D / u ^ 3 →
          ∀ b : ℝ, 0 ≤ b → b ≤ 3 * u →
            let v := (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta)
            (Measure.pi (fun _ : Fin k => eta)).real
                {a : Shao.Path k | b ≤ Shao.upperMax a hk} ≤
              C * Shao.standardNormalTail (b / Real.sqrt v) := by
  let H : ℝ := 1048579 * D
  let X : ℝ := 8 + Real.sqrt (8 * D) + Real.sqrt H
  let L : ℝ := Real.exp (-128) / 8
  let B : ℝ := 64 * Real.exp 128 * D
  let A : ℝ := (Real.sqrt L)⁻¹ + 2048 * B / (Real.sqrt L) ^ 3
  let M : ℝ := 262144 * Real.exp 64 * D
  let E : ℝ := 56 * H + 288 * D
  let K : ℝ := 112 * A * Real.exp M / (1 - Real.exp (-1))
  let Csmall : ℝ := (Shao.standardNormalTail (6 * X))⁻¹
  let Clarge : ℝ := K * Real.sqrt (2 * Real.pi) * Real.exp (E / 2) * (4 + 2 * H)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hX8 : 8 ≤ X := by
    dsimp [X]
    linarith only [Real.sqrt_nonneg (8 * D), Real.sqrt_nonneg H]
  have hX0 : 0 ≤ X := by linarith only [hX8]
  have hden : 0 < 1 - Real.exp (-1) := by
    have hh : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith only [hh]
  have hA : 0 ≤ A := by dsimp [A, L, B]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hCs : 0 < Csmall := inv_pos.mpr (Shao.standardNormalTail_basic.2.2.1 _).1
  have hCl : 0 ≤ Clarge := by dsimp [Clarge]; positivity
  refine ⟨Csmall + Clarge, add_pos_of_pos_of_nonneg hCs hCl, ?_⟩
  intro eta hprob
  letI : IsProbabilityMeasure eta := hprob
  intro k hk u hu hs h2 h3 hvL hvU hmean hthird b hb hbU
  let P := Measure.pi (fun _ : Fin k => eta)
  let v := (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta)
  let mu := ∫ z : ℝ, z ∂eta
  let s := (k : ℝ) * variance (id : ℝ → ℝ) eta
  let r := b / Real.sqrt v
  change P.real {a : Shao.Path k | b ≤ Shao.upperMax a hk} ≤
    (Csmall + Clarge) * Shao.standardNormalTail r
  have hu0 : 0 < u := by linarith only [hu]
  have hvpos : 0 < v := by change (1 / 4 : ℝ) ≤ v at hvL; linarith only [hvL]
  have hvs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hvpos
  have hvr : (1 / 2 : ℝ) ≤ Real.sqrt v := by
    have hh := Real.sq_sqrt hvpos.le
    change (1 / 4 : ℝ) ≤ v at hvL
    nlinarith only [hh, hvL, hvs]
  have hr0 : 0 ≤ r := div_nonneg hb hvs.le
  have htail0 : 0 ≤ Shao.standardNormalTail r := (Shao.standardNormalTail_basic.2.2.1 r).1.le
  have hsmallfinish : ∀ (hbound : P.real {a : Shao.Path k | b ≤ Shao.upperMax a hk} ≤
      Csmall * Shao.standardNormalTail r),
      P.real {a : Shao.Path k | b ≤ Shao.upperMax a hk} ≤
        (Csmall + Clarge) * Shao.standardNormalTail r := by
    intro hbound
    exact hbound.trans (mul_le_mul_of_nonneg_right (by linarith only [hCl]) htail0)
  by_cases hsmall : u ≤ X
  · apply hsmallfinish
    exact bgt_wall_small eta k hk u X b v hX0 hsmall hbU hvL
  have hXu : X ≤ u := (lt_of_not_ge hsmall).le
  have hr8u : Real.sqrt (8 * D) ≤ u := by
    have hh : Real.sqrt (8 * D) ≤ X := by
      dsimp [X]
      linarith only [Real.sqrt_nonneg H]
    exact hh.trans hXu
  have hlarge : 8 * D ≤ u ^ 2 := by
    have hh := Real.sq_sqrt (show 0 ≤ 8 * D by positivity)
    have hp := mul_nonneg (sub_nonneg.mpr hr8u) (add_nonneg hu0.le (Real.sqrt_nonneg (8 * D)))
    nlinarith only [hh, hp]
  have hHU : H / u ≤ X := by
    apply (div_le_iff₀ hu0).2
    have hrHX : Real.sqrt H ≤ X := by
      dsimp [X]
      linarith only [Real.sqrt_nonneg (8 * D)]
    have hh := Real.sq_sqrt hH
    have hp := mul_nonneg (sub_nonneg.mpr hrHX) (add_nonneg hX0 (Real.sqrt_nonneg H))
    have hprod := mul_le_mul_of_nonneg_right hXu hX0
    nlinarith only [hh, hp, hprod]
  obtain ⟨hcenter, hmu2, hsL, hsU, hcenter3⟩ :=
    bgt_centered_budgets eta D hD k u hu hs h2 hvL hvU hmean hthird hlarge
  change (1 / 8 : ℝ) ≤ s at hsL
  change s ≤ 4 at hsU
  have hspos : 0 < s := by linarith only [hsL]
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hssU : Real.sqrt s ≤ 2 := by nlinarith only [Real.sq_sqrt hspos.le, hsU, hss]
  have hsv : s ≤ v := by
    have heq : s = v - (k : ℝ) * mu ^ 2 := by
      dsimp [s, v, mu]
      rw [bgt_var_formula eta h2]
      ring
    rw [heq]
    have hh := mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) (sq_nonneg mu)
    linarith only [hh]
  obtain ⟨a, ha, haU, hcompletion⟩ :=
    bgt_completion_correction eta D hD k hk u hu hs h2 h3 hvL hvU hmean hthird hlarge
  let t := b - a - (k : ℝ) * mu
  let z := t / Real.sqrt s
  have hmeanabs : |(k : ℝ) * mu| ≤ D / u := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    exact hmean
  have hshift : |t - b| ≤ H / u := by
    have he : t - b = -a - (k : ℝ) * mu := by dsimp [t]; ring
    rw [he]
    have hh := abs_sub (-a) ((k : ℝ) * mu)
    rw [abs_neg, abs_of_pos ha] at hh
    calc
      _ ≤ a + |(k : ℝ) * mu| := hh
      _ ≤ 1048578 * D / u + D / u := add_le_add haU hmeanabs
      _ = _ := by dsimp [H]; ring
  have htU : t ≤ 4 * u := by
    have hDu : D / u ≤ u := (div_le_iff₀ hu0).2 (by nlinarith only [hlarge])
    have hh := (abs_le.mp hmeanabs).1
    dsimp [t]
    linarith only [hbU, ha, hh, hDu]
  by_cases hzsmall : z ≤ 1
  · have htroot : t ≤ Real.sqrt s := by
      simpa only [one_mul] using (div_le_iff₀ hss).1 hzsmall
    have hbt : b ≤ t + H / u := by linarith only [(abs_le.mp hshift).1]
    have hbX : b ≤ 2 + X := by linarith only [hbt, htroot, hssU, hHU]
    have hrX : r ≤ 6 * X := by
      apply (div_le_iff₀ hvs).2
      have hh := mul_le_mul_of_nonneg_left hvr (show 0 ≤ 6 * X by positivity)
      nlinarith only [hh, hbX, hX8]
    apply hsmallfinish
    exact bgt_small_parameter_bound P _ r (6 * X) hrX
  have hz : 1 < z := lt_of_not_ge hzsmall
  have htpos : 0 < t := by
    have hh := (lt_div_iff₀ hss).1 hz
    nlinarith only [hh, hss]
  let lam := t / s
  have hlam : 0 < lam := div_pos htpos hspos
  have hlamU : lam ≤ 32 * u := by
    apply (div_le_iff₀ hspos).2
    have hh := mul_le_mul_of_nonneg_left hsL (show 0 ≤ 32 * u by positivity)
    nlinarith only [hh, htU]
  have hScalar := bgt_wall_scalar_estimates u H b t s v hu hH hb hbU htpos htU hsL hsU hvL hsv hshift hz
  have hEndpoint := bgt_endpoint_tilt_bound eta D hD k hk u hu hs h2 h3 hsL hthird
    hcenter hcenter3 lam hlam hlamU (b - a)
  change P.real {x : Shao.Path k | b - a ≤ Shao.prefixSum x k} ≤
    Real.exp (lam * ((k : ℝ) * mu) + lam ^ 2 * s / 2 + M - lam * (b - a)) *
      (A * (lam⁻¹ + 1 / u ^ 3)) / (1 - Real.exp (-1)) at hEndpoint
  have hzsq : z ^ 2 = t ^ 2 / s := by dsimp [z]; rw [div_pow, Real.sq_sqrt hspos.le]
  have heq : lam * ((k : ℝ) * mu) + lam ^ 2 * s / 2 + M - lam * (b - a) = M - z ^ 2 / 2 := by
    rw [hzsq, show b - a = t + (k : ℝ) * mu by dsimp [t]; ring]
    dsimp [lam]
    field_simp <;> ring
  rw [heq] at hEndpoint
  have hEndPref : P.real {x : Shao.Path k | b - a ≤ Shao.prefixSum x k} ≤
      (28 * A * Real.exp M / (1 - Real.exp (-1))) * (Real.exp (-z ^ 2 / 2) / (1 + z)) := by
    calc
      _ ≤ Real.exp (M - z ^ 2 / 2) * (A * (lam⁻¹ + 1 / u ^ 3)) / (1 - Real.exp (-1)) := hEndpoint
      _ ≤ Real.exp (M - z ^ 2 / 2) * (A * (28 / (1 + z))) / (1 - Real.exp (-1)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hScalar.2.2 hA) (Real.exp_pos _).le) hden.le
      _ = _ := by rw [show M - z ^ 2 / 2 = M + (-z ^ 2 / 2) by ring, Real.exp_add]; ring
  have hPref := bgt_gaussian_prefactor_compare z r E (4 + 2 * H) (by linarith only [hz]) hr0
    (by positivity) (hScalar.1.trans (by dsimp [E]; linarith only [hD])) hScalar.2.1
  calc
    _ ≤ 4 * P.real {x : Shao.Path k | b - a ≤ Shao.prefixSum x k} := hcompletion b
    _ ≤ 4 * ((28 * A * Real.exp M / (1 - Real.exp (-1))) *
        (Real.exp (-z ^ 2 / 2) / (1 + z))) := mul_le_mul_of_nonneg_left hEndPref (by norm_num)
    _ = K * (Real.exp (-z ^ 2 / 2) / (1 + z)) := by dsimp [K]; ring
    _ ≤ K * (Real.sqrt (2 * Real.pi) * Real.exp (E / 2) * (4 + 2 * H) *
        Shao.standardNormalTail r) := mul_le_mul_of_nonneg_left hPref hK
    _ = Clarge * Shao.standardNormalTail r := by dsimp [Clarge]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hCs]) htail0

private theorem bgt_tilt_integral_div
    (eta : Measure ℝ) (f F : ℝ → ℝ) :
    (∫ z, F z ∂eta.tilted f) =
      (∫ z, F z * Real.exp (f z) ∂eta) / (∫ z, Real.exp (f z) ∂eta) := by
  rw [integral_tilted]
  change (∫ z, (Real.exp (f z) / (∫ y, Real.exp (f y) ∂eta)) * F z ∂eta) = _
  calc
    _ = ∫ z, (F z * Real.exp (f z)) / (∫ y, Real.exp (f y) ∂eta) ∂eta := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by change _ = _; ring
    _ = _ := integral_div _ _

private theorem bgt_tilt_covariance_identity
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (f F : ℝ → ℝ) (hW : Integrable (fun z => Real.exp (f z)) eta)
    (hF : Integrable F eta)
    (hFW : Integrable (fun z => F z * Real.exp (f z)) eta) (c : ℝ) :
    let m := ∫ z, F z ∂eta
    let Z := ∫ z, Real.exp (f z) ∂eta
    let rho := eta.tilted f
    Integrable (fun z => (F z - m) * (Real.exp (f z) - c)) eta ∧
      (∫ z, F z ∂rho) - m =
        (∫ z, (F z - m) * (Real.exp (f z) - c) ∂eta) / Z := by
  let m := ∫ z, F z ∂eta
  let Z := ∫ z, Real.exp (f z) ∂eta
  have hZ : 0 < Z := integral_exp_pos hW
  have hpoly : Integrable (fun z => F z * Real.exp (f z) - c * F z -
      m * Real.exp (f z) + m * c) eta :=
    ((hFW.sub (hF.const_mul c)).sub (hW.const_mul m)).add (integrable_const (m * c))
  have heq : (fun z => (F z - m) * (Real.exp (f z) - c)) =
      (fun z => F z * Real.exp (f z) - c * F z - m * Real.exp (f z) + m * c) := by
    funext z
    ring
  have hc : Integrable (fun z => (F z - m) * (Real.exp (f z) - c)) eta := by
    rw [heq]
    exact hpoly
  have hcov : (∫ z, (F z - m) * (Real.exp (f z) - c) ∂eta) =
      (∫ z, F z * Real.exp (f z) ∂eta) - m * Z := by
    rw [heq,
      integral_add (f := fun z => F z * Real.exp (f z) - c * F z - m * Real.exp (f z))
        (g := fun _ => m * c) ((hFW.sub (hF.const_mul c)).sub (hW.const_mul m)) (integrable_const _),
      integral_sub (f := fun z => F z * Real.exp (f z) - c * F z)
        (g := fun z => m * Real.exp (f z)) (hFW.sub (hF.const_mul c)) (hW.const_mul m),
      integral_sub (f := fun z => F z * Real.exp (f z)) (g := fun z => c * F z) hFW (hF.const_mul c),
      integral_const_mul, integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
    dsimp [m, Z]
    ring
  have htilt : (∫ z, F z ∂eta.tilted f) = (∫ z, F z * Real.exp (f z) ∂eta) / Z := by
    rw [integral_tilted]
    change (∫ z, (Real.exp (f z) / Z) * F z ∂eta) = _
    calc
      _ = ∫ z, (F z * Real.exp (f z)) / Z ∂eta := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by change _ = _; ring
      _ = _ := integral_div _ _
  refine ⟨hc, ?_⟩
  change (∫ z, F z ∂eta.tilted f) - m =
    (∫ z, (F z - m) * (Real.exp (f z) - c) ∂eta) / Z
  rw [htilt, hcov]
  field_simp [hZ.ne'] <;> ring

private theorem bgt_exp_nonpositive_quadratic (r : ℝ) (hr : r ≤ 0) :
    Real.exp r ≤ 1 + r + r ^ 2 / 2 := by
  by_cases hr0 : r = 0
  · subst r; norm_num
  let F : ℝ → ℝ := Real.exp
  have hF (n : ℕ) : iteratedDeriv n F = Real.exp := by
    dsimp [F]
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
  obtain ⟨t, _, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := F) (x₀ := 0) (x := r) (n := 2) (Ne.symm hr0)
    (by dsimp [F]; fun_prop : ContDiffOn ℝ 3 F (Set.uIcc 0 r))
  have hwithin (k : ℕ) : iteratedDerivWithin k F (Set.uIcc 0 r) 0 = iteratedDeriv k F 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (Ne.symm hr0))
      (by dsimp [F]; fun_prop : ContDiffAt ℝ k F 0) Set.left_mem_uIcc
  have htaylor : taylorWithinEval F 2 (Set.uIcc 0 r) 0 r = 1 + r + r ^ 2 / 2 := by
    rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval,
      hwithin 1, hwithin 2, hF 1, hF 2]
    norm_num [F]
    ring
  rw [htaylor, show 2 + 1 = (3 : ℕ) by rfl, hF 3] at hrem
  norm_num [F] at hrem
  have hcube : r ^ 3 ≤ 0 := by
    have hh := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg r) hr
    nlinarith only [hh]
  have hsign : Real.exp t * r ^ 3 / 6 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hcube) (by norm_num)
  linarith only [hrem, hsign]

private theorem bgt_energy_weight_bounds
    (eta : Measure ℝ) [IsProbabilityMeasure eta] (s : ℝ) (hs : 0 ≤ s)
    (hrange : ∀ᵐ z : ℝ ∂eta, s * z ^ 2 ≤ 8) :
    let W := fun z : ℝ => Real.exp (-s * z ^ 2)
    let Z := ∫ z, W z ∂eta
    Integrable W eta ∧ 0 < Z ∧ Real.exp (-8) ≤ Z ∧ Z ≤ 1 ∧
      Z⁻¹ ≤ Real.exp 8 ∧
      (∀ z : ℝ, ‖W z‖ ≤ 1 ∧ |W z - 1| ≤ s * z ^ 2) := by
  let W := fun z : ℝ => Real.exp (-s * z ^ 2)
  let Z := ∫ z, W z ∂eta
  have hpoint (z : ℝ) : ‖W z‖ ≤ 1 ∧ |W z - 1| ≤ s * z ^ 2 := by
    have hW1 : W z ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg hs (sq_nonneg z)])
    constructor
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hW1
    · rw [abs_of_nonpos (sub_nonpos.mpr hW1)]
      have he := Real.add_one_le_exp (-s * z ^ 2)
      change -s * z ^ 2 + 1 ≤ W z at he
      linarith only [he]
  have hW : Integrable W eta := (integrable_const (1 : ℝ)).mono'
    (by dsimp [W]; fun_prop) (Filter.Eventually.of_forall fun z => (hpoint z).1)
  have hZ : 0 < Z := integral_exp_pos hW
  have hZL : Real.exp (-8) ≤ Z := by
    have hh := integral_mono_ae (integrable_const (Real.exp (-8))) hW (by
      filter_upwards [hrange] with z hz
      apply Real.exp_le_exp.mpr
      linarith only [hz])
    simpa only [integral_const, probReal_univ, one_smul] using hh
  have hZU : Z ≤ 1 := by
    have hh := integral_mono_ae hW (integrable_const (1 : ℝ))
      (Filter.Eventually.of_forall fun z => by
        have hn := (hpoint z).1
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hn
        exact hn)
    simpa only [integral_const, probReal_univ, one_smul] using hh
  have hZinv : Z⁻¹ ≤ Real.exp 8 := by
    have hh := one_div_le_one_div_of_le (Real.exp_pos (-8)) hZL
    simpa only [one_div, ← Real.exp_neg, neg_neg] using hh
  exact ⟨hW, hZ, hZL, hZU, hZinv, hpoint⟩

private theorem bgt_energy_shift_bound
    (eta : Measure ℝ) [IsProbabilityMeasure eta] (s : ℝ) (hs : 0 ≤ s)
    (hrange : ∀ᵐ z : ℝ ∂eta, s * z ^ 2 ≤ 8)
    (F G : ℝ → ℝ) (hF : Integrable F eta) (hG : Integrable G eta)
    (T : ℝ) (hT : 0 ≤ T)
    (hdom : ∀ᵐ z : ℝ ∂eta, |F z - ∫ y, F y ∂eta| * z ^ 2 ≤ G z)
    (hGT : (∫ z, G z ∂eta) ≤ 2 * T) :
    |(∫ z, F z ∂eta.tilted (fun z => -s * z ^ 2)) - (∫ z, F z ∂eta)| ≤
      2 * s * Real.exp 8 * T := by
  let W := fun z : ℝ => Real.exp (-s * z ^ 2)
  let Z := ∫ z, W z ∂eta
  obtain ⟨hW, hZ, _, _, hZinv, hpoint⟩ := bgt_energy_weight_bounds eta s hs hrange
  have hFW : Integrable (fun z => F z * W z) eta :=
    hF.mul_bdd (by dsimp [W]; fun_prop) (Filter.Eventually.of_forall fun z => (hpoint z).1)
  have hc := bgt_tilt_covariance_identity eta (fun z => -s * z ^ 2) F hW hF hFW 1
  have hnum : |∫ z, (F z - ∫ y, F y ∂eta) * (W z - 1) ∂eta| ≤ 2 * s * T := by
    calc
      _ ≤ ∫ z, s * G z ∂eta := by
        rw [← Real.norm_eq_abs]
        apply norm_integral_le_of_norm_le (hG.const_mul s)
        filter_upwards [hdom] with z hz
        rw [Real.norm_eq_abs, abs_mul]
        calc
          _ ≤ |F z - ∫ y, F y ∂eta| * (s * z ^ 2) :=
            mul_le_mul_of_nonneg_left (hpoint z).2 (abs_nonneg _)
          _ = s * (|F z - ∫ y, F y ∂eta| * z ^ 2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hz hs
      _ = s * (∫ z, G z ∂eta) := integral_const_mul _ _
      _ ≤ s * (2 * T) := mul_le_mul_of_nonneg_left hGT hs
      _ = _ := by ring
  rw [hc.2, abs_div, abs_of_pos hZ]
  calc
    _ ≤ (2 * s * T) / Z := div_le_div_of_nonneg_right hnum hZ.le
    _ = (2 * s * T) * Z⁻¹ := by ring
    _ ≤ (2 * s * T) * Real.exp 8 := mul_le_mul_of_nonneg_left hZinv (by positivity)
    _ = _ := by ring

private theorem bgt_energy_second_monotone
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (h2 : Integrable (fun z : ℝ => z ^ 2) eta) (s : ℝ) (hs : 0 ≤ s)
    (hrange : ∀ᵐ z : ℝ ∂eta, s * z ^ 2 ≤ 8) :
    (∫ z : ℝ, z ^ 2 ∂eta.tilted (fun z => -s * z ^ 2)) ≤ ∫ z : ℝ, z ^ 2 ∂eta := by
  let m2 := ∫ z : ℝ, z ^ 2 ∂eta
  let W := fun z : ℝ => Real.exp (-s * z ^ 2)
  obtain ⟨hW, hZ, _, _, _, hpoint⟩ := bgt_energy_weight_bounds eta s hs hrange
  have hFW : Integrable (fun z : ℝ => z ^ 2 * W z) eta :=
    h2.mul_bdd (by dsimp [W]; fun_prop) (Filter.Eventually.of_forall fun z => (hpoint z).1)
  have hc := bgt_tilt_covariance_identity eta (fun z => -s * z ^ 2) (fun z => z ^ 2)
    hW h2 hFW (Real.exp (-s * m2))
  have hsign (z : ℝ) : (z ^ 2 - m2) * (W z - Real.exp (-s * m2)) ≤ 0 := by
    rcases le_total (z ^ 2) m2 with hz | hz
    · apply mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hz)
      apply sub_nonneg.mpr
      exact Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hz hs])
    · apply mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hz)
      apply sub_nonpos.mpr
      exact Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hz hs])
  have hi : (∫ z : ℝ, (z ^ 2 - m2) * (W z - Real.exp (-s * m2)) ∂eta) ≤ 0 :=
    integral_nonpos_of_ae (Filter.Eventually.of_forall hsign)
  have hd := hc.2
  have hdiv := div_nonpos_of_nonpos_of_nonneg hi hZ.le
  linarith only [hd, hdiv]

private theorem bgt_energy_log_normalizer
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (h2 : Integrable (fun z : ℝ => z ^ 2) eta)
    (h4 : Integrable (fun z : ℝ => z ^ 4) eta) (s : ℝ) (hs : 0 ≤ s)
    (hrange : ∀ᵐ z : ℝ ∂eta, s * z ^ 2 ≤ 8) :
    Real.log (∫ z : ℝ, Real.exp (-s * z ^ 2) ∂eta) ≤
      -s * (∫ z : ℝ, z ^ 2 ∂eta) + (s ^ 2 / 2) * (∫ z : ℝ, z ^ 4 ∂eta) := by
  obtain ⟨hW, hZ, _, _, _, _⟩ := bgt_energy_weight_bounds eta s hs hrange
  have hpoly : Integrable (fun z : ℝ => 1 - s * z ^ 2 + (s ^ 2 / 2) * z ^ 4) eta :=
    ((integrable_const 1).sub (h2.const_mul s)).add (h4.const_mul (s ^ 2 / 2))
  have hi := integral_mono_ae hW hpoly (Filter.Eventually.of_forall fun z => by
    have hh := bgt_exp_nonpositive_quadratic (-s * z ^ 2)
      (by nlinarith only [mul_nonneg hs (sq_nonneg z)])
    convert hh using 1 <;> ring)
  rw [integral_add (f := fun z : ℝ => 1 - s * z ^ 2) (g := fun z : ℝ => (s ^ 2 / 2) * z ^ 4)
      ((integrable_const 1).sub (h2.const_mul s)) (h4.const_mul _),
    integral_sub (f := fun _ : ℝ => 1) (g := fun z : ℝ => s * z ^ 2)
      (integrable_const 1) (h2.const_mul s), integral_const_mul, integral_const_mul] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  linarith only [hi, Real.log_le_sub_one_of_pos hZ]

private theorem bgt_second_square_le_fourth
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (h4 : Integrable (fun z : ℝ => z ^ 4) eta) :
    (∫ z : ℝ, z ^ 2 ∂eta) ^ 2 ≤ ∫ z : ℝ, z ^ 4 ∂eta := by
  have hLp : MemLp (fun z : ℝ => z ^ 2) 2 eta :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 (by
      convert h4 using 1
      funext z
      ring)
  have hh := variance_nonneg (fun z : ℝ => z ^ 2) eta
  rw [variance_eq_sub hLp] at hh
  have he : (∫ z : ℝ, (z ^ 2) ^ 2 ∂eta) = ∫ z : ℝ, z ^ 4 ∂eta := by
    congr 1
    funext z
    ring
  change 0 ≤ (∫ z : ℝ, (z ^ 2) ^ 2 ∂eta) - (∫ z : ℝ, z ^ 2 ∂eta) ^ 2 at hh
  rw [he] at hh
  linarith only [hh]

private theorem bgt_energy_moment_differences
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (h : ℝ) (hsupport : ∀ᵐ z : ℝ ∂eta, |z| ≤ h)
    (s : ℝ) (hs : 0 ≤ s) (hrange : ∀ᵐ z : ℝ ∂eta, s * z ^ 2 ≤ 8) :
    let rho := eta.tilted (fun z => -s * z ^ 2)
    let m3 := ∫ z : ℝ, |z| ^ 3 ∂eta
    let m4 := ∫ z : ℝ, z ^ 4 ∂eta
    |(∫ z : ℝ, z ∂rho) - (∫ z : ℝ, z ∂eta)| ≤ 2 * s * Real.exp 8 * m3 ∧
      |(∫ z : ℝ, z ^ 2 ∂rho) - (∫ z : ℝ, z ^ 2 ∂eta)| ≤ 2 * s * Real.exp 8 * m4 ∧
      (∫ z : ℝ, |z| ^ 3 ∂rho) ≤ Real.exp 8 * m3 := by
  let rho := eta.tilted (fun z => -s * z ^ 2)
  let mu := ∫ z : ℝ, z ∂eta
  let m2 := ∫ z : ℝ, z ^ 2 ∂eta
  let m3 := ∫ z : ℝ, |z| ^ 3 ∂eta
  let m4 := ∫ z : ℝ, z ^ 4 ∂eta
  let W := fun z : ℝ => Real.exp (-s * z ^ 2)
  let Z := ∫ z, W z ∂eta
  have hp := bgt_powers eta h hsupport
  have h1 : Integrable (fun z : ℝ => z) eta := by simpa only [pow_one] using (hp 1).1
  have h2 : Integrable (fun z : ℝ => z ^ 2) eta := (hp 2).1
  have h3 : Integrable (fun z : ℝ => |z| ^ 3) eta := (hp 3).2.1
  have h4 : Integrable (fun z : ℝ => z ^ 4) eta := (hp 4).1
  have hm2 : 0 ≤ m2 := integral_nonneg fun z => sq_nonneg z
  have hm3 : 0 ≤ m3 := integral_nonneg fun z => pow_nonneg (abs_nonneg z) 3
  have hm4 : 0 ≤ m4 := integral_nonneg fun z => by positivity
  have h4abs (z : ℝ) : z ^ 4 = |z| ^ 3 * |z| := by
    calc
      z ^ 4 = (z ^ 2) ^ 2 := by ring
      _ = (|z| ^ 2) ^ 2 := by rw [sq_abs]
      _ = _ := by ring
  have hG1 : Integrable (fun z : ℝ => |z| ^ 3 + |mu| * z ^ 2) eta := h3.add (h2.const_mul _)
  have hG2 : Integrable (fun z : ℝ => z ^ 4 + m2 * z ^ 2) eta := h4.add (h2.const_mul _)
  have hdom1 : ∀ᵐ z : ℝ ∂eta, |z - mu| * z ^ 2 ≤ |z| ^ 3 + |mu| * z ^ 2 := by
    exact Filter.Eventually.of_forall fun z => by
      calc
        _ ≤ (|z| + |mu|) * z ^ 2 := mul_le_mul_of_nonneg_right (abs_sub z mu) (sq_nonneg z)
        _ = _ := by rw [← sq_abs z]; ring
  have hdom2 : ∀ᵐ z : ℝ ∂eta, |z ^ 2 - m2| * z ^ 2 ≤ z ^ 4 + m2 * z ^ 2 := by
    exact Filter.Eventually.of_forall fun z => by
      have hh := abs_sub (z ^ 2) m2
      rw [abs_of_nonneg (sq_nonneg z), abs_of_nonneg hm2] at hh
      calc
        _ ≤ (z ^ 2 + m2) * z ^ 2 := mul_le_mul_of_nonneg_right hh (sq_nonneg z)
        _ = _ := by ring
  have hGT1 : (∫ z : ℝ, |z| ^ 3 + |mu| * z ^ 2 ∂eta) ≤ 2 * m3 := by
    rw [integral_add h3 (h2.const_mul _), integral_const_mul]
    have hh := (bgt_lyapunov eta h2 h3).1
    change |mu| * m2 ≤ m3 at hh
    change m3 + |mu| * m2 ≤ 2 * m3
    linarith only [hh]
  have hGT2 : (∫ z : ℝ, z ^ 4 + m2 * z ^ 2 ∂eta) ≤ 2 * m4 := by
    rw [integral_add h4 (h2.const_mul _), integral_const_mul]
    have hh := bgt_second_square_le_fourth eta h4
    change m2 ^ 2 ≤ m4 at hh
    change m4 + m2 * m2 ≤ 2 * m4
    nlinarith only [hh]
  refine ⟨bgt_energy_shift_bound eta s hs hrange (fun z => z)
      (fun z => |z| ^ 3 + |mu| * z ^ 2) h1 hG1 m3 hm3 hdom1 hGT1,
    bgt_energy_shift_bound eta s hs hrange (fun z => z ^ 2)
      (fun z => z ^ 4 + m2 * z ^ 2) h2 hG2 m4 hm4 hdom2 hGT2, ?_⟩
  obtain ⟨hW, hZ, _, _, hZinv, hpoint⟩ := bgt_energy_weight_bounds eta s hs hrange
  have h3W : Integrable (fun z : ℝ => |z| ^ 3 * W z) eta :=
    h3.mul_bdd (by dsimp [W]; fun_prop) (Filter.Eventually.of_forall fun z => (hpoint z).1)
  have hnum : (∫ z : ℝ, |z| ^ 3 * W z ∂eta) ≤ m3 := by
    apply integral_mono_ae h3W h3
    exact Filter.Eventually.of_forall fun z => by
      have hn := (hpoint z).1
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hn
      exact mul_le_of_le_one_right (pow_nonneg (abs_nonneg z) 3) hn
  rw [bgt_tilt_integral_div]
  change (∫ z : ℝ, |z| ^ 3 * W z ∂eta) / Z ≤ Real.exp 8 * m3
  calc
    _ ≤ m3 / Z := div_le_div_of_nonneg_right hnum hZ.le
    _ = m3 * Z⁻¹ := by ring
    _ ≤ m3 * Real.exp 8 := mul_le_mul_of_nonneg_left hZinv hm3
    _ = _ := by ring

private theorem bgt_fourth_total
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (D : ℝ) (k : ℕ) (u : ℝ) (hu : 0 < u)
    (hs : ∀ᵐ z : ℝ ∂eta, |z| ≤ 1 / u)
    (hthird : (k : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂eta) ≤ D / u ^ 3) :
    (k : ℝ) * (∫ z : ℝ, z ^ 4 ∂eta) ≤ D / u ^ 4 := by
  have h4 := (bgt_powers eta (1 / u) hs 4).1
  have h3 := (bgt_powers eta (1 / u) hs 3).2.1
  have hi : (∫ z : ℝ, z ^ 4 ∂eta) ≤ (∫ z : ℝ, |z| ^ 3 ∂eta) / u := by
    rw [← integral_div]
    apply integral_mono_ae h4 (h3.div_const u)
    filter_upwards [hs] with z hz
    calc
      z ^ 4 = |z| ^ 3 * |z| := by
        calc
          z ^ 4 = (z ^ 2) ^ 2 := by ring
          _ = (|z| ^ 2) ^ 2 := by rw [sq_abs]
          _ = _ := by ring
      _ ≤ |z| ^ 3 * (1 / u) := mul_le_mul_of_nonneg_left hz (pow_nonneg (abs_nonneg z) 3)
      _ = _ := by ring
  calc
    _ ≤ (k : ℝ) * ((∫ z : ℝ, |z| ^ 3 ∂eta) / u) :=
      mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg k)
    _ = ((k : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂eta)) / u := by ring
    _ ≤ (D / u ^ 3) / u := div_le_div_of_nonneg_right hthird hu.le
    _ = _ := by ring

private theorem bgt_square_tilt_parameters
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (D : ℝ) (hD : 1 ≤ D) (k : ℕ) (hk : 0 < k) (u : ℝ) (hu : 1 ≤ u)
    (hsupport : ∀ᵐ z : ℝ ∂eta, |z| ≤ 1 / u)
    (h2 : Integrable (fun z : ℝ => z ^ 2) eta)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) eta)
    (hvL : (1 / 2 : ℝ) ≤ (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta))
    (hvU : (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta) ≤ 2)
    (hmean : (k : ℝ) * |∫ z : ℝ, z ∂eta| ≤ D / u)
    (hthird : (k : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂eta) ≤ D / u ^ 3)
    (hlarge : 64 * Real.exp 8 * D ≤ u ^ 2) :
    let v := (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta)
    let s := 4 * u ^ 2 / v
    let rho := eta.tilted (fun z => -s * z ^ 2)
    let Ds := (1 + 16 * Real.exp 8) * D
    IsProbabilityMeasure rho ∧ (∀ᵐ z : ℝ ∂rho, |z| ≤ 1 / u) ∧
      Integrable (fun z : ℝ => z ^ 2) rho ∧ Integrable (fun z : ℝ => |z| ^ 3) rho ∧
      (1 / 4 : ℝ) ≤ (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂rho) ∧
      (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂rho) ≤ v ∧
      (k : ℝ) * |∫ z : ℝ, z ∂rho| ≤ Ds / u ∧
      (k : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂rho) ≤ Ds / u ^ 3 ∧
      (k : ℝ) * Real.log (∫ z : ℝ, Real.exp (-s * z ^ 2) ∂eta) ≤ -4 * u ^ 2 + 32 * D := by
  let v := (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta)
  let s := 4 * u ^ 2 / v
  let rho := eta.tilted (fun z => -s * z ^ 2)
  let Ds := (1 + 16 * Real.exp 8) * D
  let m2 := ∫ z : ℝ, z ^ 2 ∂eta
  let m3 := ∫ z : ℝ, |z| ^ 3 ∂eta
  let m4 := ∫ z : ℝ, z ^ 4 ∂eta
  let mu := ∫ z : ℝ, z ∂eta
  let muR := ∫ z : ℝ, z ∂rho
  let vR := (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂rho)
  have hu0 : 0 < u := by linarith only [hu]
  have hvpos : 0 < v := by change (1 / 2 : ℝ) ≤ v at hvL; linarith only [hvL]
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hsU : s ≤ 8 * u ^ 2 := by
    apply (div_le_iff₀ hvpos).2
    change (1 / 2 : ℝ) ≤ v at hvL
    have hh := mul_le_mul_of_nonneg_left hvL (show 0 ≤ 8 * u ^ 2 by positivity)
    nlinarith only [hh]
  have hsv : s * v = 4 * u ^ 2 := div_mul_cancel₀ _ hvpos.ne'
  have hrange : ∀ᵐ z : ℝ ∂eta, s * z ^ 2 ≤ 8 := by
    filter_upwards [hsupport] with z hz
    have hz2 : z ^ 2 ≤ (1 / u) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z) hz 2
    calc
      _ ≤ s * (1 / u) ^ 2 := mul_le_mul_of_nonneg_left hz2 hs
      _ ≤ (8 * u ^ 2) * (1 / u) ^ 2 := mul_le_mul_of_nonneg_right hsU (by positivity)
      _ = _ := by field_simp <;> ring
  obtain ⟨hW, hZ, _, _, _, _⟩ := bgt_energy_weight_bounds eta s hs hrange
  have hdata := boundedQuadraticTilt_density_moments eta (1 / u) 0 s (by positivity) hs hsupport
  dsimp only at hdata
  simp only [zero_mul, abs_zero, zero_add, zero_sub, ← neg_mul] at hdata
  obtain ⟨_, _, _, _, _, _, hprob, _, _, hsR, _, _, _, _, hp, _⟩ := hdata
  change IsProbabilityMeasure rho at hprob
  letI : IsProbabilityMeasure rho := hprob
  change (∀ᵐ z : ℝ ∂rho, |z| ≤ 1 / u) at hsR
  have h2R : Integrable (fun z : ℝ => z ^ 2) rho := (hp 2).2.1
  have h3R : Integrable (fun z : ℝ => |z| ^ 3) rho := (hp 3).2.2.2.1
  have h4 : Integrable (fun z : ℝ => z ^ 4) eta := (bgt_powers eta (1 / u) hsupport 4).1
  have hm3 : 0 ≤ m3 := integral_nonneg fun z => pow_nonneg (abs_nonneg z) 3
  have hm4 : 0 ≤ m4 := integral_nonneg fun z => by positivity
  have h4T : (k : ℝ) * m4 ≤ D / u ^ 4 := bgt_fourth_total eta D k u hu0 hsupport hthird
  obtain ⟨hmuDiff, h2Diff, h3tilt⟩ := bgt_energy_moment_differences eta (1 / u) hsupport s hs hrange
  have hmuT : (k : ℝ) * |muR - mu| ≤ 16 * Real.exp 8 * D / u := by
    calc
      _ ≤ (k : ℝ) * (2 * s * Real.exp 8 * m3) := mul_le_mul_of_nonneg_left hmuDiff hk0
      _ = (2 * s * Real.exp 8) * ((k : ℝ) * m3) := by ring
      _ ≤ (2 * (8 * u ^ 2) * Real.exp 8) * (D / u ^ 3) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsU (by norm_num)) (Real.exp_pos _).le
        · exact hthird
        · exact mul_nonneg hk0 hm3
        · positivity
      _ = _ := by field_simp <;> ring
  have h2T : |vR - v| ≤ 16 * Real.exp 8 * D / u ^ 2 := by
    have he : vR - v = (k : ℝ) * ((∫ z : ℝ, z ^ 2 ∂rho) - m2) := by dsimp [vR, v, m2]; ring
    rw [he, abs_mul, abs_of_nonneg hk0]
    calc
      _ ≤ (k : ℝ) * (2 * s * Real.exp 8 * m4) := mul_le_mul_of_nonneg_left h2Diff hk0
      _ = (2 * s * Real.exp 8) * ((k : ℝ) * m4) := by ring
      _ ≤ (2 * (8 * u ^ 2) * Real.exp 8) * (D / u ^ 4) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsU (by norm_num)) (Real.exp_pos _).le
        · exact h4T
        · exact mul_nonneg hk0 hm4
        · positivity
      _ = _ := by field_simp <;> ring
  have h2L : (1 / 4 : ℝ) ≤ vR := by
    have herror : 16 * Real.exp 8 * D / u ^ 2 ≤ (1 / 4 : ℝ) :=
      (div_le_iff₀ (sq_pos_of_pos hu0)).2 (by linarith only [hlarge])
    change (1 / 2 : ℝ) ≤ v at hvL
    linarith only [(abs_le.mp h2T).1, herror, hvL]
  have h2U : vR ≤ v :=
    mul_le_mul_of_nonneg_left (bgt_energy_second_monotone eta h2 s hs hrange) hk0
  have hmeanR : (k : ℝ) * |muR| ≤ Ds / u := by
    have habs : |muR| ≤ |mu| + |muR - mu| := by
      have hh := abs_add_le mu (muR - mu)
      rw [show mu + (muR - mu) = muR by ring] at hh
      exact hh
    calc
      _ ≤ (k : ℝ) * (|mu| + |muR - mu|) := mul_le_mul_of_nonneg_left habs hk0
      _ = (k : ℝ) * |mu| + (k : ℝ) * |muR - mu| := by ring
      _ ≤ D / u + 16 * Real.exp 8 * D / u := add_le_add hmean hmuT
      _ = _ := by dsimp [Ds]; ring
  have hthirdR : (k : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂rho) ≤ Ds / u ^ 3 := by
    calc
      _ ≤ (k : ℝ) * (Real.exp 8 * m3) := mul_le_mul_of_nonneg_left h3tilt hk0
      _ = Real.exp 8 * ((k : ℝ) * m3) := by ring
      _ ≤ Real.exp 8 * (D / u ^ 3) := mul_le_mul_of_nonneg_left hthird (Real.exp_pos _).le
      _ ≤ _ := by
        dsimp [Ds]
        have hp : 0 ≤ Real.exp 8 * (D / u ^ 3) := by positivity
        have hd : 0 ≤ D / u ^ 3 := by positivity
        calc
          _ = Real.exp 8 * (D / u ^ 3) := by ring
          _ ≤ D / u ^ 3 + 16 * (Real.exp 8 * (D / u ^ 3)) := by linarith only [hp, hd]
          _ = _ := by ring
  have hrem : (s ^ 2 / 2) * ((k : ℝ) * m4) ≤ 32 * D := by
    calc
      _ ≤ ((8 * u ^ 2) ^ 2 / 2) * (D / u ^ 4) := by
        apply mul_le_mul
        · exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hs hsU 2) (by norm_num)
        · exact h4T
        · exact mul_nonneg hk0 hm4
        · positivity
      _ = _ := by field_simp <;> ring
  have hlog := bgt_energy_log_normalizer eta h2 h4 s hs hrange
  have hlogT : (k : ℝ) * Real.log (∫ z : ℝ, Real.exp (-s * z ^ 2) ∂eta) ≤ -4 * u ^ 2 + 32 * D := by
    calc
      _ ≤ (k : ℝ) * (-s * m2 + (s ^ 2 / 2) * m4) := mul_le_mul_of_nonneg_left hlog hk0
      _ = -s * v + (s ^ 2 / 2) * ((k : ℝ) * m4) := by dsimp [v, m2]; ring
      _ = -4 * u ^ 2 + (s ^ 2 / 2) * ((k : ℝ) * m4) := by rw [neg_mul, hsv]; ring
      _ ≤ _ := add_le_add le_rfl hrem
  exact ⟨hprob, hsR, h2R, h3R, h2L, h2U, hmeanR, hthirdR, hlogT⟩

private theorem bgt_energy_layer_change
    (eta : Measure ℝ) [IsProbabilityMeasure eta] (k : ℕ)
    (u v s D : ℝ) (hu : 0 < u) (hs : 0 ≤ s) (hsv : s * v = 4 * u ^ 2)
    (hW : Integrable (fun z : ℝ => Real.exp (-s * z ^ 2)) eta)
    (hprob : IsProbabilityMeasure (eta.tilted (fun z => -s * z ^ 2)))
    (hnorm : (k : ℝ) * Real.log (∫ z : ℝ, Real.exp (-s * z ^ 2) ∂eta) ≤ -4 * u ^ 2 + 32 * D)
    (j : ℕ) (A : Set (Shao.Path k)) (hA : MeasurableSet A)
    (henergy : ∀ x ∈ A, Shao.energy x ≤ v * (1 - (j : ℝ) / u ^ 2)) :
    (Measure.pi (fun _ : Fin k => eta)).real A ≤ Real.exp (32 * D - 4 * (j : ℝ)) *
      (Measure.pi (fun _ : Fin k => eta.tilted (fun z => -s * z ^ 2))).real A := by
  let P := Measure.pi (fun _ : Fin k => eta)
  let rho := eta.tilted (fun z => -s * z ^ 2)
  let Q := Measure.pi (fun _ : Fin k => rho)
  let Z := ∫ z : ℝ, Real.exp (-s * z ^ 2) ∂eta
  letI : IsProbabilityMeasure rho := hprob
  have hZ : 0 < Z := integral_exp_pos hW
  have hRN := bgt_pi_tilt_inverse_density eta k (fun z => -s * z ^ 2) (by fun_prop) hW
  have hPQ : P = Q.withDensity (fun x => ENNReal.ofReal (Z ^ k * Real.exp (s * Shao.energy x))) := by
    refine hRN.trans ?_
    apply withDensity_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change ENNReal.ofReal (Z ^ k * Real.exp (-(∑ i, -s * (x i) ^ 2))) = _
      congr 2
      congr 1
      rw [Shao.energy, Finset.mul_sum]
      simp only [neg_mul, Finset.sum_neg_distrib, neg_neg]
  have hZpow : Z ^ k = Real.exp ((k : ℝ) * Real.log Z) := by
    rw [Real.exp_nat_mul, Real.exp_log hZ]
  have hbound (x : Shao.Path k) (hx : x ∈ A) :
      Z ^ k * Real.exp (s * Shao.energy x) ≤ Real.exp (32 * D - 4 * (j : ℝ)) := by
    rw [hZpow, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (henergy x hx) hs
    calc
      (k : ℝ) * Real.log Z + s * Shao.energy x ≤
          (-4 * u ^ 2 + 32 * D) + s * (v * (1 - (j : ℝ) / u ^ 2)) :=
        add_le_add hnorm hh
      _ = _ := by rw [← mul_assoc s v, hsv]; field_simp <;> ring
  exact bgt_density_event_le P Q _ hPQ A hA (Real.exp (32 * D - 4 * (j : ℝ)))
    (Real.exp_pos _).le hbound

private theorem bgt_gaussian_energy_layer
    (u : ℝ) (hu : 1 ≤ u) (j : ℕ) (hj : (j : ℝ) + 1 ≤ u ^ 2) :
    Real.exp (-4 * (j : ℝ)) * Shao.standardNormalTail (Real.sqrt (u ^ 2 - (j : ℝ) - 1)) ≤
      (8 / 3 : ℝ) * Real.exp 1 * (Real.exp (-3)) ^ j * Shao.standardNormalTail u := by
  let y := Real.sqrt (u ^ 2 - (j : ℝ) - 1)
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hy2 : y ^ 2 = u ^ 2 - (j : ℝ) - 1 := Real.sq_sqrt (by linarith only [hj])
  have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hu0 : 0 ≤ u := by linarith only [hu]
  have huLin : u ≤ y + (j : ℝ) + 1 := by
    have hp := mul_nonneg hy (show 0 ≤ (j : ℝ) + 1 by positivity)
    have hc : (j : ℝ) + 1 ≤ ((j : ℝ) + 1) ^ 2 := by nlinarith only [hj0]
    nlinarith only [hy2, hu0, hy, hp, hc]
  have hratio : (1 + u) / (1 + y) ≤ 2 * Real.exp (((j : ℝ) + 1) / 2) := by
    apply (div_le_iff₀ (by linarith only [hy])).2
    have he := Real.add_one_le_exp (((j : ℝ) + 1) / 2)
    have hcoef : (j : ℝ) + 2 ≤ 2 * Real.exp (((j : ℝ) + 1) / 2) := by linarith only [he]
    calc
      1 + u ≤ ((j : ℝ) + 2) * (1 + y) := by nlinarith only [huLin, hy, mul_nonneg hj0 hy]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by linarith only [hy])
  have htail := Shao.standardNormalTail_ratio_bound u y hu0 hy
  have hsquare : (u ^ 2 - y ^ 2) / 2 = ((j : ℝ) + 1) / 2 := by rw [hy2]; ring
  rw [hsquare] at htail
  have htail0 : 0 ≤ Shao.standardNormalTail u := (Shao.standardNormalTail_basic.2.2.1 u).1.le
  have htail' : Shao.standardNormalTail y ≤
      (8 / 3 : ℝ) * Real.exp ((j : ℝ) + 1) * Shao.standardNormalTail u := by
    calc
      _ ≤ (4 / 3 : ℝ) * ((1 + u) / (1 + y)) *
          Real.exp (((j : ℝ) + 1) / 2) * Shao.standardNormalTail u := htail
      _ ≤ (4 / 3 : ℝ) * (2 * Real.exp (((j : ℝ) + 1) / 2)) *
          Real.exp (((j : ℝ) + 1) / 2) * Shao.standardNormalTail u := by
        gcongr
      _ = _ := by
        have he : Real.exp (((j : ℝ) + 1) / 2) * Real.exp (((j : ℝ) + 1) / 2) =
            Real.exp ((j : ℝ) + 1) := by rw [← Real.exp_add]; congr 1; ring
        calc
          _ = (8 / 3 : ℝ) * (Real.exp (((j : ℝ) + 1) / 2) *
              Real.exp (((j : ℝ) + 1) / 2)) * Shao.standardNormalTail u := by ring
          _ = _ := by rw [he]
  calc
    _ ≤ Real.exp (-4 * (j : ℝ)) *
        ((8 / 3 : ℝ) * Real.exp ((j : ℝ) + 1) * Shao.standardNormalTail u) :=
      mul_le_mul_of_nonneg_left htail' (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_nat_mul]
      have he : Real.exp (-4 * (j : ℝ)) * Real.exp ((j : ℝ) + 1) =
          Real.exp 1 * Real.exp ((j : ℝ) * (-3)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = (8 / 3 : ℝ) * (Real.exp (-4 * (j : ℝ)) * Real.exp ((j : ℝ) + 1)) *
            Shao.standardNormalTail u := by ring
        _ = _ := by rw [he]; ring

private theorem bgt_gaussian_energy_layer_sum
    (u : ℝ) (hu : 1 ≤ u) (J : ℕ) (hJ : (J : ℝ) ≤ u ^ 2) :
    (∑ j ∈ Finset.range J, Real.exp (-4 * (j : ℝ)) *
      Shao.standardNormalTail (Real.sqrt (u ^ 2 - (j : ℝ) - 1))) ≤
        16 * Real.exp 4 * Shao.standardNormalTail u := by
  let q := Real.exp (-3)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hqhalf : q ≤ 1 / 2 := by
    have he := Real.add_one_le_exp (3 : ℝ)
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ Real.exp 3 by linarith only [he])
    simpa only [q, ← Real.exp_neg, one_div] using hh
  have hden : 0 < 1 - q := by linarith only [hqhalf]
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range J, q ^ j := Finset.sum_nonneg fun j _ => pow_nonneg hq0 j
  have hgeom : (∑ j ∈ Finset.range J, q ^ j) ≤ 2 := by
    have hg := geom_sum_mul q J
    have hp := pow_nonneg hq0 J
    have hm := mul_le_mul_of_nonneg_left hqhalf hsum0
    nlinarith only [hg, hp, hm]
  have htail0 := (Shao.standardNormalTail_basic.2.2.1 u).1.le
  calc
    _ ≤ ∑ j ∈ Finset.range J, (8 / 3 : ℝ) * Real.exp 1 * q ^ j * Shao.standardNormalTail u := by
      apply Finset.sum_le_sum
      intro j hj
      apply bgt_gaussian_energy_layer u hu j
      have hjJ : j + 1 ≤ J := Finset.mem_range.mp hj
      have hjR : (j : ℝ) + 1 ≤ J := by exact_mod_cast hjJ
      exact hjR.trans hJ
    _ = ((8 / 3 : ℝ) * Real.exp 1 * Shao.standardNormalTail u) * (∑ j ∈ Finset.range J, q ^ j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ((8 / 3 : ℝ) * Real.exp 1 * Shao.standardNormalTail u) * 2 :=
      mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ ≤ _ := by
      have he : Real.exp 1 ≤ Real.exp 4 := Real.exp_le_exp.mpr (by norm_num)
      have hh := mul_le_mul_of_nonneg_right he htail0
      have hn : 0 ≤ Real.exp 4 * Shao.standardNormalTail u := by positivity
      nlinarith only [hh, hn]

private theorem bgt_low_energy_gaussian (u : ℝ) (hu : 1 ≤ u) :
    Real.exp (-4 * u ^ 2) ≤ Real.sqrt (2 * Real.pi) * Shao.standardNormalTail u := by
  have hu0 : 0 ≤ u := by linarith only [hu]
  have he := Real.add_one_le_exp (7 * u ^ 2 / 2)
  have hexp : 1 + u ≤ Real.exp (7 * u ^ 2 / 2) := by nlinarith only [hu, he]
  have hp : Real.exp (-4 * u ^ 2) * (1 + u) ≤ Real.exp (-u ^ 2 / 2) := by
    calc
      _ ≤ Real.exp (-4 * u ^ 2) * Real.exp (7 * u ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hfrac := (le_div_iff₀ (show 0 < 1 + u by linarith only [hu])).2 hp
  have hM := bgt_gaussian_prefactor_compare u u 0 1 hu0 hu0 (by norm_num)
    (by nlinarith) (by simp)
  exact hfrac.trans (by simpa only [zero_div, Real.exp_zero, mul_one] using hM)

private theorem bgt_energy_layer_cover
    {Ω : Type*} (Q : Ω → ℝ) (A : Set Ω)
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (J : ℕ) :
    let q := fun j : ℕ => v * (1 - (j : ℝ) / u ^ 2)
    A ⊆ (A ∩ {x | v ≤ Q x}) ∪
      (⋃ j ∈ Finset.range J, A ∩ {x | q (j + 1) < Q x ∧ Q x ≤ q j}) ∪
        {x | Q x ≤ q J} := by
  classical
  let q := fun j : ℕ => v * (1 - (j : ℝ) / u ^ 2)
  change A ⊆ (A ∩ {x | v ≤ Q x}) ∪
    (⋃ j ∈ Finset.range J, A ∩ {x | q (j + 1) < Q x ∧ Q x ≤ q j}) ∪ {x | Q x ≤ q J}
  intro x hx
  by_cases hhigh : v ≤ Q x
  · exact Or.inl (Or.inl ⟨hx, hhigh⟩)
  by_cases hlow : Q x ≤ q J
  · exact Or.inr hlow
  let y := u ^ 2 * (1 - Q x / v)
  let c := u ^ 2 / v
  have hc : 0 < c := by dsimp [c]; positivity
  have heq (j : ℕ) : c * (q j - Q x) = y - (j : ℝ) := by
    dsimp [c, q, y]
    field_simp <;> ring
  have hy : 0 ≤ y := by
    have hh : Q x / v ≤ 1 := (div_le_iff₀ hv).2 (by linarith only [hhigh])
    exact mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hh)
  have hyJ : y < (J : ℝ) := by
    have hh := mul_neg_of_pos_of_neg hc (sub_neg.mpr (lt_of_not_ge hlow))
    rw [heq J] at hh
    linarith only [hh]
  let j := ⌊y⌋₊
  have hjL : (j : ℝ) ≤ y := Nat.floor_le hy
  have hjU : y < (j : ℝ) + 1 := Nat.lt_floor_add_one y
  have hjJ : j < J := by
    by_contra hn
    have hh : (J : ℝ) ≤ j := by exact_mod_cast Nat.le_of_not_gt hn
    linarith only [hh, hjL, hyJ]
  have hqj : Q x ≤ q j := by
    by_contra hn
    have hh := mul_neg_of_pos_of_neg hc (sub_neg.mpr (lt_of_not_ge hn))
    rw [heq j] at hh
    linarith only [hh, hjL]
  have hqj1 : q (j + 1) < Q x := by
    by_contra hn
    have hh := mul_nonneg hc.le (sub_nonneg.mpr (le_of_not_gt hn))
    rw [heq (j + 1)] at hh
    norm_num only [Nat.cast_add, Nat.cast_one] at hh
    linarith only [hh, hjU]
  apply Or.inl
  apply Or.inr
  apply Set.mem_iUnion.mpr
  refine ⟨j, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hjJ, ?_⟩⟩
  exact ⟨hx, hqj1, hqj⟩

private theorem bgt_energy_layer_wall
    (k : ℕ) (hk : 0 < k) (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (hvU : v ≤ 4)
    (j : ℕ) (hj : (j : ℝ) + 1 ≤ u ^ 2) :
    let y := Real.sqrt (u ^ 2 - (j : ℝ) - 1)
    let b := Real.sqrt v * y
    0 ≤ b ∧ b ≤ 3 * u ∧
      ∀ x : Shao.Path k, x ∈ Shao.upperCrossing hk u →
        v * (1 - ((j : ℝ) + 1) / u ^ 2) < Shao.energy x → b ≤ Shao.upperMax x hk := by
  let y := Real.sqrt (u ^ 2 - (j : ℝ) - 1)
  let b := Real.sqrt v * y
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hy2 : y ^ 2 = u ^ 2 - (j : ℝ) - 1 := Real.sq_sqrt (by linarith only [hj])
  have hvs : 0 ≤ Real.sqrt v := Real.sqrt_nonneg _
  have hvs2 : (Real.sqrt v) ^ 2 = v := Real.sq_sqrt hv.le
  have hvsU : Real.sqrt v ≤ 2 := by nlinarith only [hvs2, hvU, hvs]
  have hyU : y ≤ u := by
    nlinarith only [hy2, hy, hu, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hb : 0 ≤ b := mul_nonneg hvs hy
  have hbU : b ≤ 3 * u := by
    have hh := mul_le_mul hvsU hyU hy (by norm_num : (0 : ℝ) ≤ 2)
    change b ≤ 2 * u at hh
    linarith only [hh, hu]
  refine ⟨hb, hbU, ?_⟩
  intro x hx hQ
  have he : u ^ 2 * (v * (1 - ((j : ℝ) + 1) / u ^ 2)) =
      v * (u ^ 2 - (j : ℝ) - 1) := by field_simp <;> ring
  have hmul := mul_lt_mul_of_pos_left hQ (sq_pos_of_pos hu)
  rw [he] at hmul
  have hbsq : b ^ 2 = v * (u ^ 2 - (j : ℝ) - 1) := by
    dsimp [b]
    rw [mul_pow, hvs2, hy2]
  have hwall0 : 0 ≤ u * Real.sqrt (Shao.energy x) := by positivity
  have hwallsq : (u * Real.sqrt (Shao.energy x)) ^ 2 = u ^ 2 * Shao.energy x := by
    rw [mul_pow, Real.sq_sqrt (Shao.energy_nonneg x)]
  have hbelow : b ≤ u * Real.sqrt (Shao.energy x) := by
    nlinarith only [hbsq, hwallsq, hmul, hb, hwall0]
  exact hbelow.trans hx

theorem bounded_random_denominator_gaussian_upper
    (D : ℝ) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (eta : Measure ℝ), IsProbabilityMeasure eta →
        ∀ (k : ℕ) (hk : 0 < k) (u : ℝ), 1 ≤ u →
          (∀ᵐ z : ℝ ∂eta, |z| ≤ 1 / u) →
          Integrable (fun z : ℝ => z ^ 2) eta →
          Integrable (fun z : ℝ => |z| ^ 3) eta →
          (1 / 2 : ℝ) ≤ (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta) →
          (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta) ≤ 2 →
          (k : ℝ) * |∫ z : ℝ, z ∂eta| ≤ D / u →
          (k : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂eta) ≤ D / u ^ 3 →
          (Measure.pi (fun _ : Fin k => eta)).real (Shao.upperCrossing hk u) ≤
            C * Shao.standardNormalTail u := by
  let Ds := (1 + 16 * Real.exp 8) * D
  have hDs : 1 ≤ Ds := by
    have hp : 0 ≤ 16 * Real.exp 8 * D := by positivity
    dsimp [Ds]
    nlinarith only [hp, hD]
  obtain ⟨CE, hCE, hwall⟩ := bounded_deterministic_wall_gaussian_upper D hD
  obtain ⟨CEs, hCEs, hwallS⟩ := bounded_deterministic_wall_gaussian_upper Ds hDs
  let X := 8 + Real.sqrt (64 * Real.exp 8 * D)
  let Csmall := (Shao.standardNormalTail X)⁻¹
  let S := 16 * Real.exp 4 / (1 - Real.exp (-(7 / 2 : ℝ)))
  let Clow := 2 * Real.sqrt (2 * Real.pi) * Real.exp (32 * D + 4)
  let C := Csmall + CE + Real.exp (32 * D) * CEs * S + Clow
  have hCs : 0 < Csmall := inv_pos.mpr (Shao.standardNormalTail_basic.2.2.1 _).1
  have hSden : 0 < 1 - Real.exp (-(7 / 2 : ℝ)) := by
    have hh : Real.exp (-(7 / 2 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith only [hh]
  have hS : 16 * Real.exp 4 ≤ S := by
    apply (le_div_iff₀ hSden).2
    have hh : 1 - Real.exp (-(7 / 2 : ℝ)) ≤ 1 := by
      linarith only [(Real.exp_pos (-(7 / 2 : ℝ))).le]
    have hp := mul_le_mul_of_nonneg_left hh (show 0 ≤ 16 * Real.exp 4 by positivity)
    simpa only [mul_one] using hp
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hClow : 0 ≤ Clow := by dsimp [Clow]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro eta hprob
  letI : IsProbabilityMeasure eta := hprob
  intro k hk u hu hsupp h2 h3 hvL hvU hmean hthird
  let P := Measure.pi (fun _ : Fin k => eta)
  have hu0 : 0 < u := by linarith only [hu]
  have htail0 := (Shao.standardNormalTail_basic.2.2.1 u).1.le
  by_cases hsmall : u ≤ X
  · have hh := bgt_small_parameter_bound P (Shao.upperCrossing hk u) u X hsmall
    change P.real (Shao.upperCrossing hk u) ≤ Csmall * Shao.standardNormalTail u at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ htail0
    dsimp [C]
    have hp : 0 ≤ Real.exp (32 * D) * CEs * S := by positivity
    linarith only [hCE, hClow, hp]
  have hlarge : 64 * Real.exp 8 * D ≤ u ^ 2 := by
    have hroot : Real.sqrt (64 * Real.exp 8 * D) ≤ u := by
      have hh : Real.sqrt (64 * Real.exp 8 * D) ≤ X := by dsimp [X]; linarith
      exact hh.trans (lt_of_not_ge hsmall).le
    have hh := Real.sq_sqrt (show 0 ≤ 64 * Real.exp 8 * D by positivity)
    have hp := mul_nonneg (sub_nonneg.mpr hroot)
      (add_nonneg hu0.le (Real.sqrt_nonneg (64 * Real.exp 8 * D)))
    nlinarith only [hh, hp]
  let v := (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta)
  let s := 4 * u ^ 2 / v
  let rho := eta.tilted (fun z => -s * z ^ 2)
  let Q := Measure.pi (fun _ : Fin k => rho)
  let vR := (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂rho)
  have hvpos : 0 < v := by change (1 / 2 : ℝ) ≤ v at hvL; linarith only [hvL]
  have hvs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hvpos
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hsv : s * v = 4 * u ^ 2 := div_mul_cancel₀ _ hvpos.ne'
  obtain ⟨hprobR, hsR, h2R, h3R, hvRL, hvRU, hmeanR, hthirdR, hnorm⟩ :=
    bgt_square_tilt_parameters eta D hD k hk u hu hsupp h2 h3 hvL hvU hmean hthird hlarge
  change IsProbabilityMeasure rho at hprobR
  letI : IsProbabilityMeasure rho := hprobR
  change (1 / 4 : ℝ) ≤ vR at hvRL
  change vR ≤ v at hvRU
  have hvRpos : 0 < vR := by linarith only [hvRL]
  have hvsR : 0 < Real.sqrt vR := Real.sqrt_pos.mpr hvRpos
  have hW : Integrable (fun z : ℝ => Real.exp (-s * z ^ 2)) eta := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg hs (sq_nonneg z)])
  let J := ⌊u ^ 2⌋₊
  let q := fun j : ℕ => v * (1 - (j : ℝ) / u ^ 2)
  let High := Shao.upperCrossing hk u ∩ {x : Shao.Path k | v ≤ Shao.energy x}
  let Layer := fun j : ℕ => Shao.upperCrossing hk u ∩
    {x : Shao.Path k | q (j + 1) < Shao.energy x ∧ Shao.energy x ≤ q j}
  let Low := {x : Shao.Path k | Shao.energy x ≤ q J}
  have hJ : (J : ℝ) ≤ u ^ 2 := Nat.floor_le (sq_nonneg u)
  have hHigh : P.real High ≤ CE * Shao.standardNormalTail u := by
    have hvsU : Real.sqrt v ≤ 2 := by
      change v ≤ 2 at hvU
      nlinarith only [Real.sq_sqrt hvpos.le, hvU, hvs]
    have hwallU : u * Real.sqrt v ≤ 3 * u := by nlinarith only [mul_le_mul_of_nonneg_left hvsU hu0.le, hu]
    have hh := hwall eta hprob k hk u hu hsupp h2 h3
      (by linarith only [hvL]) (by linarith only [hvU]) hmean hthird
      (u * Real.sqrt v) (by positivity) hwallU
    change P.real {x : Shao.Path k | u * Real.sqrt v ≤ Shao.upperMax x hk} ≤
      CE * Shao.standardNormalTail ((u * Real.sqrt v) / Real.sqrt v) at hh
    rw [mul_div_cancel_right₀ _ hvs.ne'] at hh
    apply (measureReal_mono (show High ⊆ {x : Shao.Path k | u * Real.sqrt v ≤ Shao.upperMax x hk} from ?_)).trans hh
    intro x hx
    have hroot := Real.sqrt_le_sqrt hx.2
    exact (mul_le_mul_of_nonneg_left hroot hu0.le).trans hx.1
  have hLayer (j : ℕ) (hj : j ∈ Finset.range J) :
      P.real (Layer j) ≤ (Real.exp (32 * D) * CEs) *
        (Real.exp (-4 * (j : ℝ)) * Shao.standardNormalTail (Real.sqrt (u ^ 2 - (j : ℝ) - 1))) := by
    have hjJ : j + 1 ≤ J := Finset.mem_range.mp hj
    have hjU : (j : ℝ) + 1 ≤ u ^ 2 :=
      (show (j : ℝ) + 1 ≤ J by exact_mod_cast hjJ).trans hJ
    let y := Real.sqrt (u ^ 2 - (j : ℝ) - 1)
    let b := Real.sqrt v * y
    obtain ⟨hb0, hbU, hbarrier⟩ := bgt_energy_layer_wall k hk u v hu0 hvpos
      (by linarith only [hvU]) j hjU
    have hmeas : MeasurableSet (Layer j) := (Shao.measurableSet_upperCrossing hk u).inter
      ((measurableSet_lt measurable_const Shao.measurable_energy).inter
        (measurableSet_le Shao.measurable_energy measurable_const))
    have hchange := bgt_energy_layer_change eta k u v s D hu0 hs hsv hW hprobR hnorm
      j (Layer j) hmeas (fun x hx => hx.2.2)
    have hwallR := hwallS rho hprobR k hk u hu hsR h2R h3R hvRL
      (by exact hvRU.trans (by linarith only [hvU])) hmeanR hthirdR b hb0 hbU
    change Q.real {x : Shao.Path k | b ≤ Shao.upperMax x hk} ≤
      CEs * Shao.standardNormalTail (b / Real.sqrt vR) at hwallR
    have hstd : y ≤ b / Real.sqrt vR := by
      apply (le_div_iff₀ hvsR).2
      have hh := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hvRU) (Real.sqrt_nonneg (u ^ 2 - (j : ℝ) - 1))
      change Real.sqrt vR * y ≤ b at hh
      nlinarith only [hh]
    have hQtail : Q.real (Layer j) ≤ CEs * Shao.standardNormalTail y := by
      have hsub : Layer j ⊆ {x : Shao.Path k | b ≤ Shao.upperMax x hk} := by
        intro x hx
        apply hbarrier x hx.1
        simpa only [q, Nat.cast_add, Nat.cast_one] using hx.2.1
      exact (measureReal_mono hsub).trans (hwallR.trans
        (mul_le_mul_of_nonneg_left (Shao.standardNormalTail_basic.1 hstd) hCEs.le))
    calc
      _ ≤ Real.exp (32 * D - 4 * (j : ℝ)) * Q.real (Layer j) := hchange
      _ ≤ Real.exp (32 * D - 4 * (j : ℝ)) * (CEs * Shao.standardNormalTail y) :=
        mul_le_mul_of_nonneg_left hQtail (Real.exp_pos _).le
      _ = _ := by rw [show 32 * D - 4 * (j : ℝ) = 32 * D + (-4 * (j : ℝ)) by ring, Real.exp_add]; ring
  have hLow : P.real Low ≤ Clow * Shao.standardNormalTail u := by
    have hmeas : MeasurableSet Low := measurableSet_le Shao.measurable_energy measurable_const
    have hchange := bgt_energy_layer_change eta k u v s D hu0 hs hsv hW hprobR hnorm J Low hmeas
      (fun _ hx => hx)
    have hJlower : u ^ 2 < (J : ℝ) + 1 := Nat.lt_floor_add_one (u ^ 2)
    calc
      _ ≤ Real.exp (32 * D - 4 * (J : ℝ)) * Q.real Low := hchange
      _ ≤ Real.exp (32 * D - 4 * (J : ℝ)) := mul_le_of_le_one_right (Real.exp_pos _).le measureReal_le_one
      _ ≤ Real.exp (32 * D + 4 - 4 * u ^ 2) := Real.exp_le_exp.mpr (by linarith only [hJlower])
      _ = Real.exp (32 * D + 4) * Real.exp (-4 * u ^ 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (32 * D + 4) * (Real.sqrt (2 * Real.pi) * Shao.standardNormalTail u) :=
        mul_le_mul_of_nonneg_left (bgt_low_energy_gaussian u hu) (Real.exp_pos _).le
      _ ≤ Clow * Shao.standardNormalTail u := by
        dsimp [Clow]
        have hh : 0 ≤ Real.exp (32 * D + 4) * Real.sqrt (2 * Real.pi) * Shao.standardNormalTail u := by positivity
        nlinarith only [hh]
  have hcover := bgt_energy_layer_cover Shao.energy (Shao.upperCrossing hk u) u v hu0 hvpos J
  change Shao.upperCrossing hk u ⊆ (High ∪ (⋃ j ∈ Finset.range J, Layer j)) ∪ Low at hcover
  have hsum := bgt_gaussian_energy_layer_sum u hu J hJ
  calc
    P.real (Shao.upperCrossing hk u) ≤ P.real ((High ∪ (⋃ j ∈ Finset.range J, Layer j)) ∪ Low) := measureReal_mono hcover
    _ ≤ P.real (High ∪ (⋃ j ∈ Finset.range J, Layer j)) + P.real Low := measureReal_union_le _ _
    _ ≤ (P.real High + P.real (⋃ j ∈ Finset.range J, Layer j)) + P.real Low :=
      add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ (CE * Shao.standardNormalTail u + (∑ j ∈ Finset.range J, P.real (Layer j))) +
        Clow * Shao.standardNormalTail u :=
      add_le_add (add_le_add hHigh (measureReal_biUnion_finset_le _ _)) hLow
    _ ≤ (CE * Shao.standardNormalTail u + (∑ j ∈ Finset.range J,
        (Real.exp (32 * D) * CEs) * (Real.exp (-4 * (j : ℝ)) *
          Shao.standardNormalTail (Real.sqrt (u ^ 2 - (j : ℝ) - 1))))) + Clow * Shao.standardNormalTail u :=
      add_le_add (add_le_add le_rfl (Finset.sum_le_sum hLayer)) le_rfl
    _ = (CE * Shao.standardNormalTail u + (Real.exp (32 * D) * CEs) *
        (∑ j ∈ Finset.range J, Real.exp (-4 * (j : ℝ)) *
          Shao.standardNormalTail (Real.sqrt (u ^ 2 - (j : ℝ) - 1)))) + Clow * Shao.standardNormalTail u := by
      rw [Finset.mul_sum]
    _ ≤ (CE * Shao.standardNormalTail u + (Real.exp (32 * D) * CEs) *
        (16 * Real.exp 4 * Shao.standardNormalTail u)) + Clow * Shao.standardNormalTail u :=
      add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum (by positivity))) le_rfl
    _ ≤ (CE * Shao.standardNormalTail u + (Real.exp (32 * D) * CEs) *
        (S * Shao.standardNormalTail u)) + Clow * Shao.standardNormalTail u :=
      add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hS htail0) (by positivity))) le_rfl
    _ = (CE + Real.exp (32 * D) * CEs * S + Clow) * Shao.standardNormalTail u := by ring
    _ ≤ C * Shao.standardNormalTail u := by
      apply mul_le_mul_of_nonneg_right _ htail0
      dsimp [C]
      linarith only [hCs]

end Shao.Probability
