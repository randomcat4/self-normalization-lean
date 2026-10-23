import Shao.Probability.QuadraticFullNoiseHighFrequency
import Shao.Probability.QuadraticCharacteristicPower
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
The actual D and uE from supplement 2356–2357 and 3520–3537.
This module concerns their cone derivatives and u-tail integrals. The marked
v-integral, integration by parts and inversion remain separate obligations.
-/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory Set

private lemma actual_product_first (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν)
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (hgamma : (∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν ≤ 2 * h)
    (m : ℕ) (σ v r : ℝ) :
    HasDerivAt (fun s => quadraticChar ν (σ * s) v ^ m * quadraticFullNoiseChar ν s v)
      (deriv (fun s => quadraticChar ν (σ * s) v ^ m * quadraticFullNoiseChar ν s v) r) r := by
  let P : Measure (Shao.Path m) := Measure.pi (fun _ : Fin m => ν)
  have hlaw (i : Fin m) : IdentDistrib (fun a : Shao.Path m => a i) (id : ℝ → ℝ) P ν := by
    refine ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [Measure.map_id] using (measurePreserving_eval (fun _ : Fin m => ν) i).map_eq
  have hpower := iid_quadraticChar_power_hasDerivAt (fun i => measurable_pi_apply i)
    (iIndepFun_pi (fun _ : Fin m => measurable_id.aemeasurable)) hlaw h2 (σ * r) v
  have hp := hpower.scomp r (by simpa using (hasDerivAt_id r).const_mul σ)
  have hq := (quadraticFullNoiseChar_derivatives ν h3 hV h hh hs hgamma r v).1
  exact (hp.mul hq).differentiableAt.hasDerivAt

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

theorem sourceTruncation_odd_even_fullNoise_highFrequency_derivatives :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
          (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 →
          (∫ a : ℝ, a ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ i : ℕ, i ≤ n → ∀ h kappa L2 : ℝ,
              epsilon / (1 + x) ≤ h → 0 < kappa → 20 ≤ L2 →
              1 ≤ kappa * Real.sqrt L2 →
              let ρ : Measure ℝ :=
                ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
              let m : ℕ := n - i
              let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
              let V : ℝ := variance (id : ℝ → ℝ) ρ
              let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂ρ) / V
              let T : ℝ := (m : ℝ) * m2
              L2 * gamma ^ 2 ≤ T →
              ∀ u v : ℝ, u ≠ 0 → kappa / gamma ≤ |u| →
                |v| ≤ |u| / (4 * h) →
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
                  ‖deriv (fun r : ℝ => deriv D r) u‖ ≤
                    C / (T ^ 5 * |u| ^ 12) ∧
                  ‖deriv (fun r : ℝ => deriv W r) u‖ ≤
                    C / (T ^ 5 * |u| ^ 11) := by
  obtain ⟨C, hC, hfull⟩ := sourceTruncation_fullNoise_highFrequency_derivatives
  refine ⟨3 * C, by positivity, ?_⟩
  intro ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h kappa L2
    hh hkappa hL2 hkL2
  dsimp only
  intro hT u v hu hufreq hv
  let := hp0
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
  let m : ℕ := n - i
  let V : ℝ := variance (id : ℝ → ℝ) ρ
  let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂ρ) / V
  let T : ℝ := (m : ℝ) * (∫ a : ℝ, a ^ 2 ∂ρ)
  let p : ℝ → ℂ := fun r => quadraticChar ρ r v ^ m * quadraticFullNoiseChar ρ r v
  let q : ℝ → ℂ := fun r => quadraticChar ρ (-r) v ^ m * quadraticFullNoiseChar ρ r v
  obtain ⟨_, _, hp, hs, _, h2r, h3r, _⟩ :=
    Shao.sourceTruncation_law_data ν0 n h2 hnorm x epsilon hx he hehalf hbudget
  have hprob : IsProbabilityMeasure ρ := hp
  let := hprob
  have hVp : 0 < V := (Shao.sourceTruncation_variance_bounds ν0 n h2 hnorm hmean x epsilon
    hx he hehalf hbudget).2.2.2.2.2.1
  obtain ⟨_, hgammapos, _, _, hgamma, _, _, _, _⟩ :=
    Shao.sourceTruncation_gamma_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget
  change 0 < gamma at hgammapos
  have hcutoff : 0 < epsilon / (1 + x) := div_pos he (by linarith)
  have hglob (σ r : ℝ) : HasDerivAt
      (fun s => quadraticChar ρ (σ * s) v ^ m * quadraticFullNoiseChar ρ s v)
      (deriv (fun s => quadraticChar ρ (σ * s) v ^ m * quadraticFullNoiseChar ρ s v) r) r :=
    actual_product_first ρ h2r h3r hVp (epsilon / (1 + x)) hcutoff hs hgamma m σ v r
  have hp' (r : ℝ) : HasDerivAt p (deriv p r) r := by simpa only [one_mul] using hglob 1 r
  have hq' (r : ℝ) : HasDerivAt q (deriv q r) r := by simpa only [neg_one_mul] using hglob (-1) r
  have hinputs := hfull ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget
    i hi h kappa L2 hh hkappa hL2 hkL2 hT
  obtain ⟨_, hpp, _, hp1, hp2⟩ := hinputs 1 u v (by norm_num) hu hufreq hv
  obtain ⟨_, hqq, _, hq1, hq2⟩ := hinputs (-1) u v (by norm_num) hu hufreq hv
  simp only [one_mul, neg_one_mul] at hpp hp1 hp2 hqq hq1 hq2
  obtain ⟨hD, hDD, hW, hWW, hD2, hW2⟩ := odd_even_calculus p q hp' hq' u
    (C * Real.sqrt T / (T ^ 6 * |u| ^ 12)) (C * T / (T ^ 6 * |u| ^ 12))
    hpp hqq hp1 hq1 hp2 hq2
  have hDeq : (fun r => (p r - q r) / 2) = (fun r =>
      (quadraticChar ρ r v ^ m - quadraticChar ρ (-r) v ^ m) / 2 *
        quadraticFullNoiseChar ρ r v) := by funext r; dsimp [p, q]; ring
  have hWeq : (fun r : ℝ => (r : ℂ) * ((p r + q r) / 2)) = (fun r : ℝ =>
      (r : ℂ) * ((quadraticChar ρ r v ^ m + quadraticChar ρ (-r) v ^ m) / 2 *
        quadraticFullNoiseChar ρ r v)) := by funext r; dsimp [p, q]; ring
  rw [hDeq] at hD hDD
  rw [hWeq] at hW hWW
  rw [hDeq] at hD2
  rw [hWeq] at hW2
  have hL : 0 ≤ L2 := by linarith
  have ha : 0 < |u| := abs_pos.mpr hu
  have hTpos : 0 < T := (mul_pos (by linarith : 0 < L2) (sq_pos_of_pos hgammapos)).trans_le hT
  have hfreq : 1 ≤ |u| * Real.sqrt T := by
    have hkg : kappa ≤ |u| * gamma := (div_le_iff₀ hgammapos).1 hufreq
    have hk2 := pow_le_pow_left₀ hkappa.le hkg 2
    have hkLsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hkL2 2
    rw [mul_pow, Real.sq_sqrt hL] at hkLsq
    norm_num only [one_pow] at hkLsq
    have hp : 1 ≤ (|u| * Real.sqrt T) ^ 2 := by
      calc
        _ ≤ kappa ^ 2 * L2 := hkLsq
        _ ≤ (|u| * gamma) ^ 2 * L2 := mul_le_mul_of_nonneg_right hk2 hL
        _ = |u| ^ 2 * (L2 * gamma ^ 2) := by ring
        _ ≤ |u| ^ 2 * T := mul_le_mul_of_nonneg_left hT (sq_nonneg |u|)
        _ = _ := by rw [mul_pow, Real.sq_sqrt hTpos.le]
    nlinarith only [hp, mul_nonneg ha.le (Real.sqrt_nonneg T)]
  have hrootpay : Real.sqrt T ≤ |u| * T := by
    have hp := mul_le_mul_of_nonneg_right hfreq (Real.sqrt_nonneg T)
    calc
      _ = 1 * Real.sqrt T := by ring
      _ ≤ |u| * Real.sqrt T * Real.sqrt T := hp
      _ = |u| * (Real.sqrt T) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hTpos.le]
  refine ⟨hD, hDD, hW, hWW, hD2.trans ?_, hW2.trans ?_⟩
  · change C * T / (T ^ 6 * |u| ^ 12) ≤ 3 * C / (T ^ 5 * |u| ^ 12)
    calc
      _ = C / (T ^ 5 * |u| ^ 12) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)
  · change 2 * (C * Real.sqrt T / (T ^ 6 * |u| ^ 12)) +
      |u| * (C * T / (T ^ 6 * |u| ^ 12)) ≤ 3 * C / (T ^ 5 * |u| ^ 11)
    calc
      _ ≤ 2 * (C * (|u| * T) / (T ^ 6 * |u| ^ 12)) +
          |u| * (C * T / (T ^ 6 * |u| ^ 12)) := by
        gcongr
      _ = _ := by field_simp; ring

private lemma abs_tail_rpow (a p : ℝ) (ha : 0 < a) (hp : p < -1) :
    IntegrableOn (fun u : ℝ => |u| ^ p) {u | a ≤ |u|} ∧
      (∫ u in {u : ℝ | a ≤ |u|}, |u| ^ p) = 2 * (-a ^ (p + 1) / (p + 1)) := by
  have hright : IntegrableOn (fun u : ℝ => |u| ^ p) (Set.Ici a) := by
    have hr : IntegrableOn (fun u : ℝ => u ^ p) (Set.Ici a) :=
      (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).2 (integrableOn_Ioi_rpow_of_lt hp ha)
    exact hr.congr_fun (fun u hu => by dsimp; rw [abs_of_pos (ha.trans_le hu)]) measurableSet_Ici
  have hleft : IntegrableOn (fun u : ℝ => |u| ^ p) (Set.Iic (-a)) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let e : MeasurableEmbedding fun u : ℝ => -u := (Homeomorph.neg ℝ).measurableEmbedding
    rw [e.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_neg]
    exact hright
  have hset : {u : ℝ | a ≤ |u|} = Set.Iic (-a) ∪ Set.Ici a := by
    ext u
    rcases le_total 0 u with hu | hu
    · simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici, abs_of_nonneg hu]
      constructor
      · exact Or.inr
      · rintro (hl | hr)
        · linarith
        · exact hr
    · simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici, abs_of_nonpos hu]
      constructor
      · intro h; exact Or.inl (by linarith)
      · rintro (hl | hr) <;> linarith
  have hdis : Disjoint (Set.Iic (-a)) (Set.Ici a) := by
    apply Set.disjoint_left.2
    intro u hl hr
    have : u ≤ -a := hl
    have : a ≤ u := hr
    linarith
  refine ⟨hset ▸ hleft.union hright, ?_⟩
  rw [hset, setIntegral_union hdis measurableSet_Ici hleft hright]
  have hleftval : (∫ u in Set.Iic (-a), |u| ^ p) = ∫ u in Set.Ioi a, |u| ^ p := by
    simpa only [abs_neg, neg_neg] using
      (integral_comp_neg_Iic (-a) (fun u : ℝ => |u| ^ p))
  have hrightval : (∫ u in Set.Ioi a, |u| ^ p) = ∫ u in Set.Ioi a, u ^ p := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp
    rw [abs_of_pos (ha.trans hu)]
  rw [hleftval, integral_Ici_eq_integral_Ioi, hrightval, integral_Ioi_rpow_of_lt hp ha]
  ring

private lemma tail_envelope (a y : ℝ) (ha : 0 < a) (hy : 0 ≤ y) (k : ℕ) (hk : 3 ≤ k) :
    let H : ℝ → ℝ := fun u => (1 + Real.sqrt (y * |u|)) / |u| ^ k
    IntegrableOn H {u : ℝ | a ≤ |u|} ∧
      (∫ u in {u : ℝ | a ≤ |u|}, H u) ≤
        2 * ((a⁻¹) ^ (k - 1) + Real.sqrt y * (a⁻¹) ^ (k - 2) * Real.sqrt a⁻¹) := by
  dsimp only
  let B0 : ℝ := (a⁻¹) ^ (k - 1)
  let B1 : ℝ := (a⁻¹) ^ (k - 2) * Real.sqrt a⁻¹
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hp0 : -(k : ℝ) < -1 := by linarith
  have hp1 : (1 / 2 : ℝ) - k < -1 := by linarith
  obtain ⟨h0, hi0⟩ := abs_tail_rpow a (-(k : ℝ)) ha hp0
  obtain ⟨h1, hi1⟩ := abs_tail_rpow a ((1 / 2 : ℝ) - k) ha hp1
  have hrepr (u : ℝ) (hu : a ≤ |u|) :
      (1 + Real.sqrt (y * |u|)) / |u| ^ k =
        |u| ^ (-(k : ℝ)) + Real.sqrt y * |u| ^ ((1 / 2 : ℝ) - k) := by
    have hu' : 0 < |u| := ha.trans_le hu
    rw [Real.sqrt_mul hy, Real.rpow_neg hu'.le, Real.rpow_natCast,
      Real.rpow_sub hu', Real.rpow_natCast, ← Real.sqrt_eq_rpow]
    ring
  have hsum := h0.add (h1.const_mul (Real.sqrt y))
  have hmeas : MeasurableSet {u : ℝ | a ≤ |u|} :=
    (isClosed_le continuous_const continuous_abs).measurableSet
  have hint : IntegrableOn (fun u => (1 + Real.sqrt (y * |u|)) / |u| ^ k)
      {u : ℝ | a ≤ |u|} := hsum.congr_fun (fun u hu => (hrepr u hu).symm) hmeas
  have hexp0 : -(k : ℝ) + 1 = -((k - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
    ring
  have hexp1 : (1 / 2 : ℝ) - k + 1 = -(((k - 2 : ℕ) : ℝ) + 1 / 2) := by
    rw [Nat.cast_sub (by omega : 2 ≤ k)]
    norm_num
    ring
  have hpow0 : a ^ (-(k : ℝ) + 1) = B0 := by
    rw [hexp0, Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]
  have hpow1 : a ^ ((1 / 2 : ℝ) - k + 1) = B1 := by
    rw [hexp1, Real.rpow_neg_eq_inv_rpow,
      Real.rpow_add (inv_pos.mpr ha), Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hB0 : 0 ≤ B0 := by dsimp [B0]; positivity
  have hB1 : 0 ≤ B1 := by dsimp [B1]; positivity
  have hb0 : -a ^ (-(k : ℝ) + 1) / (-(k : ℝ) + 1) ≤ B0 := by
    rw [hpow0]
    have heq : -B0 / (-(k : ℝ) + 1) = B0 / ((k : ℝ) - 1) := by
      convert (neg_div_neg_eq B0 ((k : ℝ) - 1)) using 1
      ring
    rw [heq]
    exact div_le_self hB0 (by linarith)
  have hb1 : -a ^ ((1 / 2 : ℝ) - k + 1) / ((1 / 2 : ℝ) - k + 1) ≤ B1 := by
    rw [hpow1]
    have heq : -B1 / ((1 / 2 : ℝ) - k + 1) = B1 / ((k : ℝ) - 3 / 2) := by
      convert (neg_div_neg_eq B1 ((k : ℝ) - 3 / 2)) using 1
      ring
    rw [heq]
    exact div_le_self hB1 (by linarith)
  refine ⟨hint, ?_⟩
  calc
    _ = (∫ u in {u : ℝ | a ≤ |u|}, |u| ^ (-(k : ℝ))) + Real.sqrt y *
        (∫ u in {u : ℝ | a ≤ |u|}, |u| ^ ((1 / 2 : ℝ) - k)) := by
      rw [setIntegral_congr_fun hmeas (fun u hu => hrepr u hu), integral_add h0 (h1.const_mul _),
        integral_const_mul]
    _ ≤ 2 * B0 + Real.sqrt y * (2 * B1) := by
      rw [hi0, hi1]
      exact add_le_add (mul_le_mul_of_nonneg_left hb0 (by norm_num))
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb1 (by norm_num))
          (Real.sqrt_nonneg y))
    _ = _ := by dsimp [B0, B1]; ring

private lemma compare_tail (F : ℝ → ℝ) (A : Set ℝ) (a y c : ℝ) (k : ℕ)
    (ha : 0 < a) (hy : 0 ≤ y) (hc : 0 ≤ c) (hk : 3 ≤ k)
    (hA : MeasurableSet A) (hAB : A ⊆ {u : ℝ | a ≤ |u|})
    (hF : Measurable F) (hF0 : ∀ u, 0 ≤ F u)
    (hbound : ∀ u ∈ A, F u ≤ c * ((1 + Real.sqrt (y * |u|)) / |u| ^ k)) :
    IntegrableOn F A ∧ (∫ u in A, F u) ≤
      2 * c * ((a⁻¹) ^ (k - 1) + Real.sqrt y * (a⁻¹) ^ (k - 2) * Real.sqrt a⁻¹) := by
  obtain ⟨hH, hHval⟩ := tail_envelope a y ha hy k hk
  have henv : IntegrableOn (fun u => c * ((1 + Real.sqrt (y * |u|)) / |u| ^ k))
      {u : ℝ | a ≤ |u|} := hH.const_mul c
  have henvA : IntegrableOn (fun u => c * ((1 + Real.sqrt (y * |u|)) / |u| ^ k)) A :=
    henv.mono_set hAB
  have hint : IntegrableOn F A := by
    refine henvA.mono' hF.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hA] with u hu
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 u)] using hbound u hu
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ u in A, c * ((1 + Real.sqrt (y * |u|)) / |u| ^ k) :=
      setIntegral_mono_on hint henvA hA hbound
    _ ≤ ∫ u in {u : ℝ | a ≤ |u|}, c * ((1 + Real.sqrt (y * |u|)) / |u| ^ k) :=
      setIntegral_mono_set henv (Filter.Eventually.of_forall fun _ => by positivity)
        (Filter.Eventually.of_forall fun u hu => hAB hu)
    _ ≤ c * (2 * ((a⁻¹) ^ (k - 1) + Real.sqrt y * (a⁻¹) ^ (k - 2) * Real.sqrt a⁻¹)) := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hHval hc
    _ = _ := by ring

theorem sourceTruncation_odd_even_fullNoise_highFrequency_tails :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
          (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 →
          (∫ a : ℝ, a ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ i : ℕ, i ≤ n → ∀ h kappa L2 : ℝ,
              epsilon / (1 + x) ≤ h → 0 < kappa → 20 ≤ L2 →
              1 ≤ kappa * Real.sqrt L2 →
              let ρ : Measure ℝ :=
                ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
              let m : ℕ := n - i
              let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
              let V : ℝ := variance (id : ℝ → ℝ) ρ
              let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂ρ) / V
              let T : ℝ := (m : ℝ) * m2
              L2 * gamma ^ 2 ≤ T →
              ∀ y : ℝ, 0 < y → y ≤ 2 → T < y ^ 2 →
                ∀ v : ℝ,
                  let A : Set ℝ :=
                    {u | kappa / gamma ≤ |u| ∧ |v| ≤ |u| / (4 * h)}
                  let b : ℝ := gamma / kappa
                  let D : ℝ → ℂ := fun r =>
                    ((quadraticChar ρ r v) ^ m - (quadraticChar ρ (-r) v) ^ m) /
                      2 * quadraticFullNoiseChar ρ r v
                  let E : ℝ → ℂ := fun r =>
                    ((quadraticChar ρ r v) ^ m + (quadraticChar ρ (-r) v) ^ m) /
                      2 * quadraticFullNoiseChar ρ r v
                  let W : ℝ → ℂ := fun r => (r : ℂ) * E r
                  let Iodd : ℝ → ℝ := fun u =>
                    ‖deriv (fun r : ℝ => deriv D r) u‖ *
                      (1 + Real.sqrt (y * |u|))
                  let Ieven : ℝ → ℝ := fun u =>
                    ‖deriv (fun r : ℝ => deriv W r) u‖ *
                      (1 + Real.sqrt (y * |u|))
                  IntegrableOn Iodd A ∧ IntegrableOn Ieven A ∧
                    (∫ u in A, Iodd u) ≤
                      C * (b ^ 11 + Real.sqrt y * b ^ 10 * Real.sqrt b) / T ^ 5 ∧
                    (∫ u in A, Ieven u) ≤
                      C * (b ^ 10 + Real.sqrt y * b ^ 9 * Real.sqrt b) / T ^ 5 := by
  obtain ⟨C, hC, hpoint⟩ := sourceTruncation_odd_even_fullNoise_highFrequency_derivatives
  refine ⟨2 * C, by positivity, ?_⟩
  intro ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h kappa L2 hh hkappa hL2 hkL2
  dsimp only
  intro hT y hy _hy2 _hTy v
  let := hp0
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
  let m : ℕ := n - i
  let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
  let T : ℝ := (m : ℝ) * (∫ a : ℝ, a ^ 2 ∂ρ)
  let a : ℝ := kappa / gamma
  let A : Set ℝ := {u | a ≤ |u| ∧ |v| ≤ |u| / (4 * h)}
  let D : ℝ → ℂ := fun r => (quadraticChar ρ r v ^ m - quadraticChar ρ (-r) v ^ m) / 2 *
    quadraticFullNoiseChar ρ r v
  let E : ℝ → ℂ := fun r => (quadraticChar ρ r v ^ m + quadraticChar ρ (-r) v ^ m) / 2 *
    quadraticFullNoiseChar ρ r v
  let W : ℝ → ℂ := fun r => (r : ℂ) * E r
  let Iodd : ℝ → ℝ := fun u => ‖deriv (fun r => deriv D r) u‖ * (1 + Real.sqrt (y * |u|))
  let Ieven : ℝ → ℝ := fun u => ‖deriv (fun r => deriv W r) u‖ * (1 + Real.sqrt (y * |u|))
  have hgamma : 0 < gamma := (Shao.sourceTruncation_gamma_bounds ν0 n h2 hnorm hmean x epsilon
    hx he hehalf hbudget).2.1
  have ha : 0 < a := div_pos hkappa hgamma
  have hTp : 0 < T := (mul_pos (by linarith : 0 < L2) (sq_pos_of_pos hgamma)).trans_le hT
  have hA : MeasurableSet A := by
    exact (isClosed_le continuous_const continuous_abs).measurableSet.inter
      (isClosed_le continuous_const (continuous_abs.div_const _)).measurableSet
  have hAB : A ⊆ {u : ℝ | a ≤ |u|} := fun _ hu => hu.1
  have hbound (u : ℝ) (hu : u ∈ A) :
      ‖deriv (fun r => deriv D r) u‖ ≤ C / (T ^ 5 * |u| ^ 12) ∧
      ‖deriv (fun r => deriv W r) u‖ ≤ C / (T ^ 5 * |u| ^ 11) := by
    have hune : u ≠ 0 := abs_pos.1 (ha.trans_le hu.1)
    exact (hpoint ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget
      i hi h kappa L2 hh hkappa hL2 hkL2 hT u v hune hu.1 hu.2).2.2.2.2
  have hiomeas : Measurable Iodd :=
    (measurable_deriv (fun r => deriv D r)).norm.mul (by fun_prop)
  have hiemeas : Measurable Ieven :=
    (measurable_deriv (fun r => deriv W r)).norm.mul (by fun_prop)
  obtain ⟨hio, hioVal⟩ := compare_tail Iodd A a y (C / T ^ 5) 12 ha hy.le (by positivity)
    (by norm_num) hA hAB hiomeas (fun _ => by dsimp [Iodd]; positivity) (by
      intro u hu
      calc
        _ ≤ (C / (T ^ 5 * |u| ^ 12)) * (1 + Real.sqrt (y * |u|)) :=
          mul_le_mul_of_nonneg_right (hbound u hu).1 (by positivity)
        _ = _ := by ring)
  obtain ⟨hie, hieVal⟩ := compare_tail Ieven A a y (C / T ^ 5) 11 ha hy.le (by positivity)
    (by norm_num) hA hAB hiemeas (fun _ => by dsimp [Ieven]; positivity) (by
      intro u hu
      calc
        _ ≤ (C / (T ^ 5 * |u| ^ 11)) * (1 + Real.sqrt (y * |u|)) :=
          mul_le_mul_of_nonneg_right (hbound u hu).2 (by positivity)
        _ = _ := by ring)
  refine ⟨hio, hie, hioVal.trans_eq ?_, hieVal.trans_eq ?_⟩
  · simp only [a, inv_div, Nat.reduceSub]
    ring
  · simp only [a, inv_div, Nat.reduceSub]
    ring

end Shao.Probability
