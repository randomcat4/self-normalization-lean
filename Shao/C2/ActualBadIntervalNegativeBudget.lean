import Shao.C2.ActualSignedDoubleTelescope
import Shao.C2.BridgeIntervalImageResolved
import Shao.Probability.SourceResidualRareSuffix
import Shao.Probability.SourceTrueEnergyStrip

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
noncomputable section
namespace Shao.C2.ActualBadIntervalNegativeBudget
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.ActualSignedDoubleTelescope
open Shao.Probability.SourcePermutationReveal
open Shao.Probability.SourceSeparatedOvershoot

local instance labelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

def actualBadIntervalNegativeBill {n : ℕ} (Q : Measure BridgeNoise) (x : ℝ)
    (nu : Shao.Path n → LabelPerm n → ℕ)
    (p : Shao.Path n × LabelPerm n) : ℝ :=
  ∑ r ∈ Finset.range n,
    if 3 * x * Real.sqrt (remainingEnergy p.1 r p.2) / 2 ≤
        |remainingSum p.1 r p.2| then
      max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
        p.1 x (nu p.1) r p.2) 0
    else 0

private theorem anib_bounded_moment_data
    (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (bound : ℝ) (hbound : 0 < bound)
    (hsupport : ∀ᵐ z : ℝ ∂rho, |z| ≤ bound)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂rho) = 1) :
    let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
    Integrable (fun z : ℝ => z) rho ∧
      Integrable (fun z : ℝ => z ^ 2) rho ∧
      Integrable (fun z : ℝ => |z| ^ 3) rho ∧
      Integrable (fun z : ℝ => z ^ 4) rho ∧
      1 ≤ bound ∧ 1 ≤ beta ∧
      (∫ z : ℝ, z ^ 4 ∂rho) ≤ bound * beta := by
  classical
  intro beta
  have hp (p : ℕ) : Integrable (fun z : ℝ => z ^ p) rho ∧
      Integrable (fun z : ℝ => |z| ^ p) rho := by
    have hb : ∀ᵐ z : ℝ ∂rho, |z| ^ p ≤ bound ^ p :=
      hsupport.mono fun z hz => pow_le_pow_left₀ (abs_nonneg z) hz p
    constructor
    · exact (integrable_const (bound ^ p)).mono' (by fun_prop)
        (by simpa only [Real.norm_eq_abs, abs_pow] using hb)
    · exact (integrable_const (bound ^ p)).mono' (by fun_prop)
        (by
          filter_upwards [hb] with z hz
          simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg z) p)] using hz)
  have h2 := (hp 2).1
  have h3 := (hp 3).2
  have h4 := (hp 4).1
  have hB : 1 ≤ bound := by
    have hi := integral_mono_ae h2 (integrable_const (bound ^ 2))
      (hsupport.mono fun z hz => by nlinarith [sq_abs z, abs_nonneg z])
    simp only [integral_const, probReal_univ, one_smul, hsecond] at hi
    nlinarith only [hi, hbound]
  have hb : 1 ≤ beta := by
    have hpoint (z : ℝ) : 3 * z ^ 2 ≤ 2 * |z| ^ 3 + 1 := by
      have hh := mul_nonneg (sq_nonneg (|z| - 1)) (show 0 ≤ 2 * |z| + 1 by positivity)
      nlinarith only [hh, sq_abs z]
    have hi := integral_mono (h2.const_mul 3)
      ((h3.const_mul 2).add (integrable_const 1)) hpoint
    change (∫ z : ℝ, 3 * z ^ 2 ∂rho) ≤ ∫ z : ℝ, 2 * |z| ^ 3 + 1 ∂rho at hi
    rw [integral_const_mul, integral_add (h3.const_mul 2) (integrable_const 1),
      integral_const_mul, hsecond] at hi
    simp only [integral_const, probReal_univ, one_smul] at hi
    change 1 ≤ ∫ z : ℝ, |z| ^ 3 ∂rho
    linarith only [hi]
  refine ⟨by simpa only [pow_one] using (hp 1).1, h2, h3, h4, hB, hb, ?_⟩
  have hi := integral_mono_ae h4 (h3.const_mul bound)
    (hsupport.mono fun z hz => by
      have hh := mul_le_mul_of_nonneg_right hz (pow_nonneg (abs_nonneg z) 3)
      calc
        z ^ 4 = |z| * |z| ^ 3 := by
          calc
            z ^ 4 = (z ^ 2) ^ 2 := by ring
            _ = (|z| ^ 2) ^ 2 := by rw [sq_abs]
            _ = _ := by ring
        _ ≤ bound * |z| ^ 3 := hh)
  simpa only [integral_const_mul] using hi

private theorem anib_clipped_square_lipschitz
    (bound : ℝ) (hbound : 0 ≤ bound) (s t : ℝ) :
    let clip : ℝ → ℝ := fun z => min bound (max (-bound) z)
    |clip t ^ 2 - clip s ^ 2| ≤ 2 * bound * |t - s| := by
  intro clip
  have hcb (z : ℝ) : |clip z| ≤ bound := by
    apply abs_le.2
    exact ⟨le_min (by linarith) (le_max_left _ _), min_le_left _ _⟩
  have hc : |clip t - clip s| ≤ |t - s| := by
    have hmax := abs_max_sub_max_le_max (-bound) t (-bound) s
    have hmin := abs_min_sub_min_le_max bound (max (-bound) t) bound (max (-bound) s)
    simp only [sub_self, abs_zero] at hmax hmin
    rw [max_eq_right (abs_nonneg (t - s))] at hmax
    rw [max_eq_right (abs_nonneg (max (-bound) t - max (-bound) s))] at hmin
    exact hmin.trans hmax
  calc
    _ = |clip t - clip s| * |clip t + clip s| := by rw [← abs_mul]; congr 1 <;> ring
    _ ≤ |t - s| * (2 * bound) :=
      mul_le_mul hc ((abs_add_le _ _).trans (by linarith only [hcb t, hcb s]))
        (abs_nonneg _) (abs_nonneg _)
    _ = _ := by ring

private theorem anib_floored_statistic_strong
    (k : ℕ) (hk : 0 < k)
    (bound x q : ℝ) (hbound : 0 ≤ bound) (hx : 0 ≤ x) (hq : 0 ≤ q)
    (hslope : x * bound * Real.sqrt (2 / (k : ℝ)) ≤ 1 / 2) :
    let clip : ℝ → ℝ := fun z => min bound (max (-bound) z)
    let F : Shao.Path k → ℝ := fun a =>
      Shao.prefixSum a k - x * Real.sqrt
        (max ((k : ℝ) / 2) (q + ∑ i : Fin k, clip (a i) ^ 2))
    let H : Shao.Path k → ℝ := fun a =>
      2 * F (fun i : Fin k => Real.sqrt (k : ℝ) * a i) / Real.sqrt (k : ℝ)
    Measurable H ∧
      ∀ (a : Shao.Path k) (i : Fin k),
        Monotone (fun t : ℝ => H (Function.update a i t) - t) := by
  classical
  intro clip F H
  have hkp : 0 < (k : ℝ) := by exact_mod_cast hk
  have hs : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkp
  have hs2 := Real.sq_sqrt hkp.le
  have hfroot : 0 < Real.sqrt ((k : ℝ) / 2) := Real.sqrt_pos.2 (by positivity)
  have hrootfactor : bound / Real.sqrt ((k : ℝ) / 2) =
      bound * Real.sqrt (2 / (k : ℝ)) := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_div (by positivity)]
    have ht := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    field_simp <;> nlinarith only [ht]
  have hlip (c s t : ℝ) :
      |Real.sqrt (max ((k : ℝ) / 2) (c + clip t ^ 2)) -
        Real.sqrt (max ((k : ℝ) / 2) (c + clip s ^ 2))| ≤
          bound * Real.sqrt (2 / (k : ℝ)) * |t - s| := by
    let A := max ((k : ℝ) / 2) (c + clip t ^ 2)
    let B := max ((k : ℝ) / 2) (c + clip s ^ 2)
    have ha : (k : ℝ) / 2 ≤ A := le_max_left _ _
    have hb : (k : ℝ) / 2 ≤ B := le_max_left _ _
    have ha0 : 0 ≤ A := (by positivity : (0 : ℝ) ≤ (k : ℝ) / 2).trans ha
    have hb0 : 0 ≤ B := (by positivity : (0 : ℝ) ≤ (k : ℝ) / 2).trans hb
    have haR := Real.sqrt_le_sqrt ha
    have hbR := Real.sqrt_le_sqrt hb
    have hAB : |A - B| ≤ 2 * bound * |t - s| := by
      have hh := abs_max_sub_max_le_max ((k : ℝ) / 2) (c + clip t ^ 2)
        ((k : ℝ) / 2) (c + clip s ^ 2)
      simp only [sub_self, abs_zero, add_sub_add_left_eq_sub] at hh
      rw [max_eq_right (abs_nonneg (clip t ^ 2 - clip s ^ 2))] at hh
      exact hh.trans (anib_clipped_square_lipschitz bound hbound s t)
    have hp : |Real.sqrt A - Real.sqrt B| * (Real.sqrt A + Real.sqrt B) = |A - B| := by
      rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)), ← abs_mul]
      congr 1
      nlinarith only [Real.sq_sqrt ha0, Real.sq_sqrt hb0]
    have hh : |Real.sqrt A - Real.sqrt B| ≤ bound / Real.sqrt ((k : ℝ) / 2) * |t - s| := by
      have hm := mul_le_mul_of_nonneg_left (show 2 * Real.sqrt ((k : ℝ) / 2) ≤
          Real.sqrt A + Real.sqrt B by linarith only [haR, hbR]) (abs_nonneg (Real.sqrt A - Real.sqrt B))
      have hh : |Real.sqrt A - Real.sqrt B| * (2 * Real.sqrt ((k : ℝ) / 2)) ≤
          2 * bound * |t - s| := by
        calc
          _ ≤ |Real.sqrt A - Real.sqrt B| * (Real.sqrt A + Real.sqrt B) := hm
          _ = |A - B| := hp
          _ ≤ _ := hAB
      have hd := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hfroot)).2 hh
      calc
        _ ≤ (2 * bound * |t - s|) / (2 * Real.sqrt ((k : ℝ) / 2)) := hd
        _ = _ := by field_simp <;> ring
    simpa only [hrootfactor] using hh
  refine ⟨by dsimp [H, F, clip]; simp only [Shao.prefixSum_length]; fun_prop, ?_⟩
  intro a i s t hst
  let v : Shao.Path k := fun j => Real.sqrt (k : ℝ) * a j
  have hupdate (w : ℝ) :
      (fun j : Fin k => Real.sqrt (k : ℝ) * Function.update a i w j) =
        Function.update v i (Real.sqrt (k : ℝ) * w) := by
    funext j
    by_cases hj : j = i <;> simp [hj, v]
  have hsum (g : ℝ → ℝ) (w : ℝ) :
      (∑ j : Fin k, g (Function.update v i w j)) =
        (∑ j ∈ (Finset.univ : Finset (Fin k)).erase i, g (v j)) + g w := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    · simp
  have hh := hlip (q + ∑ j ∈ (Finset.univ : Finset (Fin k)).erase i, clip (v j) ^ 2)
    (Real.sqrt (k : ℝ) * s) (Real.sqrt (k : ℝ) * t)
  have hnonneg : 0 ≤ Real.sqrt (k : ℝ) * t - Real.sqrt (k : ℝ) * s :=
    sub_nonneg.2 (mul_le_mul_of_nonneg_left hst hs.le)
  rw [abs_of_nonneg hnonneg] at hh
  have hup := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hh) hx
  have hsl := mul_le_mul_of_nonneg_right hslope hnonneg
  change 2 * F (fun j : Fin k => Real.sqrt (k : ℝ) * Function.update a i s j) / Real.sqrt (k : ℝ) - s ≤
    2 * F (fun j : Fin k => Real.sqrt (k : ℝ) * Function.update a i t j) / Real.sqrt (k : ℝ) - t
  rw [hupdate s, hupdate t]
  dsimp only [F]
  have hS (w : ℝ) : Shao.prefixSum (Function.update v i w) k =
      (∑ j ∈ (Finset.univ : Finset (Fin k)).erase i, v j) + w := by
    simpa only [Shao.prefixSum_length, id_eq] using hsum id w
  rw [hS, hS, hsum (fun z => clip z ^ 2), hsum (fun z => clip z ^ 2)]
  simp only [← add_assoc]
  have hden : ∀ A t : ℝ, 2 * A / Real.sqrt (k : ℝ) - t =
      (2 * A - t * Real.sqrt (k : ℝ)) / Real.sqrt (k : ℝ) := by
    intro A t; field_simp <;> ring
  simp_rw [hden]
  exact (div_le_div_iff_of_pos_right hs).2 (by nlinarith only [hup, hsl])

private theorem anib_normalized_iid_data
    (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (hsecondInt : Integrable (fun z : ℝ => z ^ 2) rho)
    (hthirdInt : Integrable (fun z : ℝ => |z| ^ 3) rho)
    (hmean : (∫ z : ℝ, z ∂rho) = 0)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂rho) = 1)
    (k : ℕ) (hk : 0 < k) :
    let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
    let scale : ℝ := Real.sqrt (k : ℝ)
    let eta : Measure ℝ := Measure.map (fun z : ℝ => z / scale) rho
    0 < scale ∧ IsProbabilityMeasure eta ∧
      Integrable (fun z : ℝ => z ^ 2) eta ∧
      (∫ z : ℝ, z ∂eta) = 0 ∧
      (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta) = 1 ∧
      Shao.truncationBudget eta k 0 ≤ beta / scale ∧
      Measure.map (fun a : Shao.Path k => fun i : Fin k => a i / scale)
        (Measure.pi (fun _ : Fin k => rho)) = Measure.pi (fun _ : Fin k => eta) := by
  classical
  intro beta scale eta
  have hkp : 0 < (k : ℝ) := by exact_mod_cast hk
  have hs : 0 < scale := Real.sqrt_pos.2 hkp
  have hs2 : scale ^ 2 = (k : ℝ) := Real.sq_sqrt hkp.le
  have hm : Measurable (fun z : ℝ => z / scale) := measurable_id.div_const scale
  letI : IsProbabilityMeasure eta := by dsimp [eta]; infer_instance
  have he2 : Integrable (fun z : ℝ => z ^ 2) eta := by
    apply (integrable_map_measure (by fun_prop) hm.aemeasurable).2
    simpa only [Function.comp_def, div_pow] using hsecondInt.div_const (scale ^ 2)
  have hme : (∫ z : ℝ, z ∂eta) = 0 := by
    rw [show eta = Measure.map (fun z : ℝ => z / scale) rho from rfl,
      integral_map hm.aemeasurable (by fun_prop), integral_div, hmean, zero_div]
  have hnorm : (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta) = 1 := by
    rw [show eta = Measure.map (fun z : ℝ => z / scale) rho from rfl,
      integral_map hm.aemeasurable (by fun_prop)]
    simp_rw [div_pow]
    rw [integral_div, hsecond, ← hs2]
    field_simp
  have hR : Shao.truncationBudget eta k 0 ≤ beta / scale := by
    have hf := Shao.integrable_truncationF_mul eta he2 1
    have h3 : Integrable (fun z : ℝ => |z| ^ 3) eta := by
      apply (integrable_map_measure (by fun_prop) hm.aemeasurable).2
      simpa only [Function.comp_def, abs_div, abs_of_pos hs, div_pow] using
        hthirdInt.div_const (scale ^ 3)
    have hi : (∫ z : ℝ, Shao.truncationF z ∂eta) ≤ ∫ z : ℝ, |z| ^ 3 ∂eta := by
      apply integral_mono (by simpa only [one_mul] using hf) h3
      intro z
      have hh := mul_le_mul_of_nonneg_left (min_le_left |z| 1) (sq_nonneg z)
      calc
        Shao.truncationF z = z ^ 2 * min |z| 1 := rfl
        _ ≤ z ^ 2 * |z| := hh
        _ = |z| ^ 3 := by rw [show |z| ^ 3 = |z| ^ 2 * |z| by ring, sq_abs z]
    have hIe : (∫ z : ℝ, |z| ^ 3 ∂eta) = beta / scale ^ 3 := by
      rw [show eta = Measure.map (fun z : ℝ => z / scale) rho from rfl,
        integral_map hm.aemeasurable (by fun_prop)]
      simp_rw [abs_div, abs_of_pos hs, div_pow]
      exact integral_div _ _
    change (k : ℝ) * (∫ z : ℝ, Shao.truncationF ((1 + 0) * z) ∂eta) ≤ _
    simp only [add_zero, one_mul]
    calc
      _ ≤ (k : ℝ) * (beta / scale ^ 3) := by
        rw [← hIe]; exact mul_le_mul_of_nonneg_left hi hkp.le
      _ = _ := by rw [← hs2]; field_simp <;> ring
  exact ⟨hs, inferInstance, he2, hme, hnorm, hR,
    Measure.pi_map_pi (fun _ : Fin k => hm.aemeasurable)⟩

private theorem anib_iid_low_energy
    (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (bound : ℝ) (hbound : 0 < bound)
    (hsupport : ∀ᵐ z : ℝ ∂rho, |z| ≤ bound)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂rho) = 1)
    (k : ℕ) (hk : 0 < k) :
    let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
    (Measure.pi (fun _ : Fin k => rho)).real
      {a : Shao.Path k | Shao.energy a < (k : ℝ) / 2} ≤
      4 * bound * beta / (k : ℝ) := by
  classical
  intro beta
  let P : Measure (Shao.Path k) := Measure.pi (fun _ : Fin k => rho)
  have hdata := anib_bounded_moment_data rho bound hbound hsupport hsecond
  have h2 := hdata.2.1
  have h4 := hdata.2.2.2.1
  have h4b := hdata.2.2.2.2.2.2
  have hLp : MemLp (fun z : ℝ => z ^ 2) 2 rho :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 (by convert h4 using 1; funext z; ring)
  have heLp : MemLp (Shao.energy : Shao.Path k → ℝ) 2 P :=
    memLp_finsetSum Finset.univ (fun i _ => hLp.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin k => rho) i))
  have heMean : (∫ a : Shao.Path k, Shao.energy a ∂P) = (k : ℝ) := by
    have hci (i : Fin k) : Integrable (fun a : Shao.Path k => a i ^ 2) P := by
      simpa only [Function.comp_def] using
        (hLp.comp_measurePreserving (measurePreserving_eval (fun _ : Fin k => rho) i)).integrable (by norm_num)
    change (∫ a : Shao.Path k, ∑ i : Fin k, a i ^ 2 ∂P) = (k : ℝ)
    rw [integral_finsetSum _ (fun i _ => hci i)]
    have hi (i : Fin k) : (∫ a : Shao.Path k, a i ^ 2 ∂P) = 1 := by
      rw [← hsecond]
      have hsqMeas : Measurable (fun z : ℝ => z ^ 2) := by fun_prop
      have hh := integral_map (μ := P) (measurable_pi_apply i).aemeasurable hsqMeas.aestronglyMeasurable
      rw [(measurePreserving_eval (fun _ : Fin k => rho) i).map_eq] at hh
      exact hh.symm
    simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have heVar : variance (Shao.energy : Shao.Path k → ℝ) P ≤ (k : ℝ) * bound * beta := by
    have hv := variance_sum_pi (μ := fun _ : Fin k => rho)
      (X := fun _ => fun z : ℝ => z ^ 2) (fun _ => hLp)
    have hval : variance (fun z : ℝ => z ^ 2) rho ≤ ∫ z : ℝ, z ^ 4 ∂rho := by
      rw [variance_eq_sub hLp]
      simp only [Pi.pow_apply]
      have he : (∫ z : ℝ, (z ^ 2) ^ 2 ∂rho) = ∫ z : ℝ, z ^ 4 ∂rho := by
        congr 1; funext z; ring
      rw [he]
      exact sub_le_self _ (sq_nonneg _)
    have he : (∑ i : Fin k, fun a : Shao.Path k => a i ^ 2) = Shao.energy := by
      funext a; simp only [Finset.sum_apply, Shao.energy]
    rw [he] at hv
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hv
    rw [hv]
    nlinarith only [mul_le_mul_of_nonneg_left (hval.trans h4b) (Nat.cast_nonneg k)]
  let E : Set (Shao.Path k) := {a | Shao.energy a < (k : ℝ) / 2}
  have hEm : MeasurableSet E := measurableSet_lt Shao.measurable_energy measurable_const
  have hcen : Integrable (fun a : Shao.Path k => (Shao.energy a - (k : ℝ)) ^ 2) P :=
    (heLp.sub (memLp_const (k : ℝ))).integrable_sq
  have hi := integral_mono (((integrable_const ((k : ℝ) ^ 2 / 4)).indicator hEm)) hcen
    (fun a => by
      by_cases ha : a ∈ E
      · rw [Set.indicator_of_mem ha]
        change Shao.energy a < (k : ℝ) / 2 at ha
        nlinarith only [ha, Shao.energy_nonneg a,
          show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k]
      · rw [Set.indicator_of_notMem ha]; exact sq_nonneg _)
  rw [integral_indicator_const _ hEm, smul_eq_mul] at hi
  have hvariance : variance (Shao.energy : Shao.Path k → ℝ) P =
      ∫ a : Shao.Path k, (Shao.energy a - (k : ℝ)) ^ 2 ∂P := by
    rw [variance_eq_integral Shao.measurable_energy.aemeasurable, heMean]
  rw [← hvariance] at hi
  have hkp : 0 < (k : ℝ) := by exact_mod_cast hk
  change P.real E ≤ _
  apply (le_div_iff₀ hkp).2
  have hmul : P.real E * (k : ℝ) ^ 2 ≤ 4 * (k : ℝ) * bound * beta := by nlinarith only [hi, heVar]
  apply (mul_le_mul_iff_right₀ hkp).1
  nlinarith only [hmul]

private theorem anib_actual_wall_interval_concentration
    (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (bound : ℝ) (hbound : 0 < bound)
    (hsupport : ∀ᵐ z : ℝ ∂rho, |z| ≤ bound)
    (hmean : (∫ z : ℝ, z ∂rho) = 0)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂rho) = 1)
    (k : ℕ) (hk : 0 < k)
    (hscale : bound ≤ Real.sqrt (k : ℝ))
    (x : ℝ) (hx : 0 ≤ x)
    (hslope : x * bound * Real.sqrt (2 / (k : ℝ)) ≤ 1 / 2)
    (q a b : ℝ) (hq : 0 ≤ q) (hab : a ≤ b) :
    let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
    (Measure.pi (fun _ : Fin k => rho)).real
      {v : Shao.Path k |
        a ≤ Shao.prefixSum v k - x * Real.sqrt (q + Shao.energy v) ∧
        Shao.prefixSum v k - x * Real.sqrt (q + Shao.energy v) ≤ b} ≤
      84 * (b - a + beta) / Real.sqrt (k : ℝ) := by
  classical
  intro beta
  let P : Measure (Shao.Path k) := Measure.pi (fun _ : Fin k => rho)
  let clip : ℝ → ℝ := fun z => min bound (max (-bound) z)
  let F : Shao.Path k → ℝ := fun v => Shao.prefixSum v k - x * Real.sqrt
    (max ((k : ℝ) / 2) (q + ∑ i : Fin k, clip (v i) ^ 2))
  let H : Shao.Path k → ℝ := fun v =>
    2 * F (fun i => Real.sqrt (k : ℝ) * v i) / Real.sqrt (k : ℝ)
  have hraw := anib_bounded_moment_data rho bound hbound hsupport hsecond
  have hn := anib_normalized_iid_data rho hraw.2.1 hraw.2.2.1 hmean hsecond k hk
  let scale : ℝ := Real.sqrt (k : ℝ)
  let eta : Measure ℝ := Measure.map (fun z : ℝ => z / scale) rho
  have hs : 0 < scale := hn.1
  letI : IsProbabilityMeasure eta := hn.2.1
  have hstrong := anib_floored_statistic_strong k hk bound x q hbound.le hx hq hslope
  have hC := Shao.Probability.iid_strong_monotonicity_concentration eta k hk
    hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 H hstrong.1 hstrong.2
    (2 * a / scale) (2 * b / scale) ((div_le_div_iff_of_pos_right hs).2 (by linarith only [hab]))
  let A : Set (Shao.Path k) := {v | a ≤ F v ∧ F v ≤ b}
  have hAm : MeasurableSet A := by dsimp [A, F, clip]; measurability
  let normPath : Shao.Path k → Shao.Path k := fun v i => v i / scale
  have hnm : Measurable normPath := by
    dsimp only [normPath]
    exact Measurable.of_eval fun i => (measurable_pi_apply (X := fun _ : Fin k => ℝ) i).div_const scale
  have hpre : normPath ⁻¹' {v | 2 * a / scale ≤ H v ∧ H v ≤ 2 * b / scale} = A := by
    ext v
    have hv : (fun i : Fin k => Real.sqrt (k : ℝ) * normPath v i) = v := by
      funext i; dsimp [normPath, scale]; field_simp
    change (2 * a / scale ≤ 2 * F (fun i : Fin k => Real.sqrt (k : ℝ) * normPath v i) / scale ∧
      2 * F (fun i : Fin k => Real.sqrt (k : ℝ) * normPath v i) / scale ≤ 2 * b / scale) ↔
      (a ≤ F v ∧ F v ≤ b)
    rw [hv]
    constructor
    · intro hh
      have ha := (div_le_div_iff_of_pos_right hs).1 hh.1
      have hb := (div_le_div_iff_of_pos_right hs).1 hh.2
      constructor <;> linarith only [ha, hb]
    · intro hh
      constructor <;> apply (div_le_div_iff_of_pos_right hs).2 <;> linarith only [hh.1, hh.2]
  have hmap := hn.2.2.2.2.2.2
  have hHm : MeasurableSet {v : Shao.Path k | 2 * a / scale ≤ H v ∧ H v ≤ 2 * b / scale} :=
    (measurableSet_le measurable_const hstrong.1).inter (measurableSet_le hstrong.1 measurable_const)
  rw [← hmap, Measure.real_def, Measure.map_apply hnm hHm, hpre] at hC
  have hCA : P.real A ≤ (4 * (b - a) + 80 * beta) / scale := by
    have hh := hn.2.2.2.2.2.1
    calc
      _ ≤ 2 * (2 * b / scale - 2 * a / scale) + 80 * Shao.truncationBudget eta k 0 := hC
      _ ≤ 2 * (2 * b / scale - 2 * a / scale) + 80 * (beta / scale) := by gcongr
      _ = _ := by ring
  let E : Set (Shao.Path k) := {v | a ≤ Shao.prefixSum v k - x * Real.sqrt (q + Shao.energy v) ∧
    Shao.prefixSum v k - x * Real.sqrt (q + Shao.energy v) ≤ b}
  let L : Set (Shao.Path k) := {v | Shao.energy v < (k : ℝ) / 2}
  have hsupp : ∀ᵐ v : Shao.Path k ∂P, ∀ i : Fin k, |v i| ≤ bound := by
    apply ae_all_iff.2
    intro i
    exact (measurePreserving_eval (fun _ : Fin k => rho) i).quasiMeasurePreserving.ae hsupport
  have hsub : E ≤ᵐ[P] A ∪ L := by
    filter_upwards [hsupp] with v hv hE
    by_cases hl : v ∈ L
    · exact Or.inr hl
    left
    have hc : (∑ i : Fin k, clip (v i) ^ 2) = Shao.energy v := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [clip, max_eq_right (abs_le.1 (hv i)).1, min_eq_right (abs_le.1 (hv i)).2]
    have hfloor : (k : ℝ) / 2 ≤ q + Shao.energy v := by
      have hh : (k : ℝ) / 2 ≤ Shao.energy v := le_of_not_gt hl
      linarith only [hq, hh]
    change a ≤ F v ∧ F v ≤ b
    dsimp only [F]
    rw [hc, max_eq_right hfloor]
    exact hE
  have hL := anib_iid_low_energy rho bound hbound hsupport hsecond k hk
  have hfloor : 4 * bound * beta / (k : ℝ) ≤ 4 * beta / scale := by
    have hb0 : 0 ≤ beta := (show 1 ≤ beta from hraw.2.2.2.2.2.1).trans' (by norm_num)
    have hs2 : scale ^ 2 = (k : ℝ) := Real.sq_sqrt (Nat.cast_nonneg k)
    apply (div_le_div_iff₀ (by exact_mod_cast hk : (0 : ℝ) < k) hs).2
    rw [← hs2]
    nlinarith only [mul_le_mul_of_nonneg_right hscale (mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * beta) hs.le)]
  change P.real E ≤ _
  calc
    _ ≤ P.real (A ∪ L) := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ ≤ P.real A + P.real L := measureReal_union_le _ _
    _ ≤ (4 * (b - a) + 80 * beta) / scale + 4 * beta / scale :=
      add_le_add hCA (hL.trans hfloor)
    _ = (4 * (b - a) + 84 * beta) / scale := by ring
    _ ≤ _ := by
      apply (div_le_div_iff_of_pos_right hs).2
      nlinarith only [hab]

private theorem anib_reverse_closed_survival :
    ∃ C : ℝ, 0 < C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (bound : ℝ), 0 < bound → (∀ᵐ z : ℝ ∂rho, |z| ≤ bound) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ (k : ℕ), 0 < k → ∀ (v : ℝ), 0 ≤ v →
          (Measure.pi (fun _ : Fin k => rho)).real
            {a : Shao.Path k | Shao.maxWithZero (fun i => -a (Fin.rev i)) ≤ v} ≤
            C * (v + beta) / Real.sqrt (k : ℝ) := by
  classical
  obtain ⟨C, hC, hSurv⟩ := Shao.Probability.original_closed_survival_uniform
  refine ⟨C, hC, ?_⟩
  intro rho hProb bound hbound hsupport hmean hsecond beta k hk v hv
  letI : IsProbabilityMeasure rho := hProb
  have hraw := anib_bounded_moment_data rho bound hbound hsupport hsecond
  have hd := anib_normalized_iid_data rho hraw.2.1 hraw.2.2.1 hmean hsecond k hk
  let scale : ℝ := Real.sqrt (k : ℝ)
  let eta : Measure ℝ := Measure.map (fun z : ℝ => z / scale) rho
  have hs : 0 < scale := hd.1
  letI : IsProbabilityMeasure eta := hd.2.1
  let P : Measure (Shao.Path k) := Measure.pi (fun _ : Fin k => rho)
  let T : Shao.Path k → Shao.Path k := fun a i => a i / scale
  have hTm : Measurable T := by
    dsimp only [T]
    exact Measurable.of_eval fun i => (measurable_pi_apply (X := fun _ : Fin k => ℝ) i).div_const scale
  have hmax (a : Shao.Path k) : Shao.maxWithZero ((-1 : ℝ) • T a) =
      Shao.maxWithZero ((-1 : ℝ) • a) / scale := by
    have he : (-1 : ℝ) • T a = scale⁻¹ • ((-1 : ℝ) • a) := by funext i; dsimp [T]; ring
    rw [he, Shao.maxWithZero_eq _ hk, Shao.upperMax_smul_of_nonneg _ (inv_nonneg.2 hs.le),
      Shao.maxWithZero_eq _ hk]
    by_cases ha : 0 ≤ Shao.upperMax ((-1 : ℝ) • a) hk
    · rw [max_eq_right ha, max_eq_right (mul_nonneg (inv_nonneg.2 hs.le) ha)]; ring
    · rw [max_eq_left (le_of_not_ge ha), max_eq_left (mul_nonpos_of_nonneg_of_nonpos
        (inv_nonneg.2 hs.le) (le_of_not_ge ha))]; simp
  let E : Set (Shao.Path k) := {a | Shao.maxWithZero ((-1 : ℝ) • a) ≤ v / scale}
  have hsm : Measurable (fun a : Shao.Path k => (-1 : ℝ) • a) :=
    Measurable.of_eval fun i => measurable_const.mul (measurable_pi_apply (X := fun _ : Fin k => ℝ) i)
  have hEm : MeasurableSet E :=
    measurableSet_le (Shao.measurable_maxWithZero.comp hsm) measurable_const
  have hp := hSurv eta k hk hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1 (-1) (v / scale)
    (Or.inr rfl) (div_nonneg hv hs.le)
  have hpre : T ⁻¹' E = {a : Shao.Path k | Shao.maxWithZero ((-1 : ℝ) • a) ≤ v} := by
    ext a
    change Shao.maxWithZero ((-1 : ℝ) • T a) ≤ v / scale ↔ _
    rw [hmax]; exact div_le_div_iff_of_pos_right hs
  rw [← hd.2.2.2.2.2.2, Measure.real_def, Measure.map_apply hTm hEm, hpre] at hp
  have hrev : MeasurePreserving (fun a : Shao.Path k => fun i => a (Fin.rev i)) P P :=
    (measurePreserving_piCongrLeft (fun _ : Fin k => rho) Fin.revPerm).symm
  have hEv : MeasurableSet {a : Shao.Path k | Shao.maxWithZero ((-1 : ℝ) • a) ≤ v} :=
    measurableSet_le (Shao.measurable_maxWithZero.comp hsm) measurable_const
  have he := congrArg (fun m : Measure (Shao.Path k) =>
    m {a | Shao.maxWithZero ((-1 : ℝ) • a) ≤ v}) hrev.map_eq
  rw [Measure.map_apply hrev.measurable hEv] at he
  have hprob : P.real {a : Shao.Path k | Shao.maxWithZero (fun i => -a (Fin.rev i)) ≤ v} =
      P.real {a : Shao.Path k | Shao.maxWithZero ((-1 : ℝ) • a) ≤ v} := by
    have hsigned (a : Shao.Path k) : (-1 : ℝ) • (fun i => a (Fin.rev i)) =
        (fun i => -a (Fin.rev i)) := by
      funext i
      simp
    have hrevpre : (fun a : Shao.Path k => fun i => a (Fin.rev i)) ⁻¹'
        {a : Shao.Path k | Shao.maxWithZero ((-1 : ℝ) • a) ≤ v} =
        {a : Shao.Path k | Shao.maxWithZero (fun i => -a (Fin.rev i)) ≤ v} := by
      ext a
      change Shao.maxWithZero ((-1 : ℝ) • (fun i => a (Fin.rev i))) ≤ v ↔ _
      rw [hsigned]
      rfl
    rw [hrevpre] at he
    exact congrArg ENNReal.toReal he
  rw [hprob]
  exact hp.trans (by
    have hh := hd.2.2.2.2.2.1
    calc
      _ ≤ C * (v / scale + beta / scale) := by gcongr
      _ = _ := by ring)

private theorem anib_large_x_true_energy_closed_strip :
    ∃ C : ℝ, 0 < C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (bound : ℝ), 0 < bound → (∀ᵐ z : ℝ ∂rho, |z| ≤ bound) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), (1 / 2 : ℝ) ≤ x →
          bound ≤ Real.sqrt (n : ℝ) / (100 * x) →
          ∀ (r : ℕ), 0 < r → r ≤ n → n ≤ 2 * r →
            ∀ (q v s : ℝ), 0 ≤ q → 0 ≤ v → (s = 1 ∨ s = -1) →
              let wall : Shao.Path r → ℝ := fun a =>
                x * Real.sqrt (q + Shao.energy a)
              (Measure.pi (fun _ : Fin r => rho)).real
                {a : Shao.Path r |
                  Shao.maxWithZero (s • a) ≤ wall a ∧
                  wall a - v ≤ s * Shao.prefixSum a r ∧
                  s * Shao.prefixSum a r ≤ wall a} ≤
                C * (v + beta) ^ 2 / (r : ℝ) := by
  classical
  obtain ⟨Cs, hCs, hSurv⟩ := anib_reverse_closed_survival
  let C : ℝ := 336 * Cs
  have hC : 0 < C := by dsimp [C]; positivity
  have hUpper : ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
      (bound : ℝ), 0 < bound → (∀ᵐ z : ℝ ∂rho, |z| ≤ bound) →
      (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
      ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), (1 / 2 : ℝ) ≤ x →
      bound ≤ Real.sqrt (n : ℝ) / (100 * x) →
      ∀ (r : ℕ), 0 < r → r ≤ n → n ≤ 2 * r →
      ∀ q v : ℝ, 0 ≤ q → 0 ≤ v →
      (Measure.pi (fun _ : Fin r => rho)).real
        {a : Shao.Path r | Shao.maxWithZero a ≤ x * Real.sqrt (q + Shao.energy a) ∧
          x * Real.sqrt (q + Shao.energy a) - v ≤ Shao.prefixSum a r ∧
          Shao.prefixSum a r ≤ x * Real.sqrt (q + Shao.energy a)} ≤
          C * (v + ∫ z : ℝ, |z| ^ 3 ∂rho) ^ 2 / (r : ℝ) := by
    intro rho hProb bound hb hsupport hm hsecond n hn x hx hscale r hr hrn hnr q v hq hv
    letI : IsProbabilityMeasure rho := hProb
    let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
    have hraw := anib_bounded_moment_data rho bound hb hsupport hsecond
    have hb1 : 1 ≤ bound := hraw.2.2.2.2.1
    have hbeta : 0 ≤ beta := by dsimp [beta]; exact integral_nonneg fun z => by positivity
    have hx0 : 0 < x := by linarith only [hx]
    have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
    have hsn2 := Real.sq_sqrt hnp.le
    have hxb : 100 * x * bound ≤ Real.sqrt (n : ℝ) := by
      have hh := (le_div_iff₀ (by positivity)).1 hscale
      nlinarith only [hh]
    have hlarge : 10000 * x ^ 2 * bound ^ 2 ≤ (n : ℝ) := by
      have hh := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 100 * x * bound)
        (Real.sqrt_nonneg (n : ℝ))).2 hxb
      nlinarith only [hh, hsn2]
    have hx2 : (1 / 4 : ℝ) ≤ x ^ 2 := by
      nlinarith only [hx, sq_nonneg (x - 1 / 2)]
    have hb2 : 1 ≤ bound ^ 2 := by nlinarith only [hb1, sq_nonneg (bound - 1)]
    have hprod : (1 / 4 : ℝ) ≤ x ^ 2 * bound ^ 2 :=
      (by simpa only [mul_one] using mul_le_mul hx2 hb2 (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg x))
    have hr2 : 2 ≤ r := by
      have hnR : (n : ℝ) ≤ 2 * (r : ℝ) := by exact_mod_cast hnr
      by_contra hh
      have hr1 : r ≤ 1 := by omega
      have hr1R : (r : ℝ) ≤ 1 := by exact_mod_cast hr1
      nlinarith only [hlarge, hprod, hnR, hr1R]
    let k : ℕ := r / 2
    let ell : ℕ := r - k
    have hk : 0 < k := by dsimp [k]; omega
    have hell : 0 < ell := by dsimp [ell, k]; omega
    have hkr : k ≤ r := by dsimp [k]; omega
    have hsum : k + ell = r := by dsimp [ell]; omega
    have hrk : r ≤ 3 * k := by dsimp [k]; omega
    have hrell : r ≤ 3 * ell := by dsimp [ell, k]; omega
    have hnk : (n : ℝ) ≤ 6 * (k : ℝ) := by exact_mod_cast (by omega : n ≤ 6 * k)
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
    have hellR : 0 < (ell : ℝ) := by exact_mod_cast hell
    have hbscale : bound ≤ Real.sqrt (k : ℝ) := by
      apply (sq_le_sq₀ hb.le (Real.sqrt_nonneg _)).1
      rw [Real.sq_sqrt hkR.le]
      have hh := mul_le_mul_of_nonneg_right hx2 (sq_nonneg bound)
      nlinarith only [hlarge, hnk, hh, sq_nonneg bound]
    have hslope : x * bound * Real.sqrt (2 / (k : ℝ)) ≤ 1 / 2 := by
      have hsq := Real.sq_sqrt (show 0 ≤ 2 / (k : ℝ) by positivity)
      have hid : (x * bound * Real.sqrt (2 / (k : ℝ))) ^ 2 * (k : ℝ) =
          2 * x ^ 2 * bound ^ 2 := by rw [mul_pow, mul_pow, hsq]; field_simp <;> ring
      have hnonneg : 0 ≤ x * bound * Real.sqrt (2 / (k : ℝ)) := by positivity
      apply (sq_le_sq₀ hnonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)).1
      apply (mul_le_mul_iff_right₀ hkR).1
      nlinarith only [hlarge, hnk, hid]
    let P : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => rho)
    let Pk : Measure (Shao.Path k) := Measure.pi (fun _ : Fin k => rho)
    let Pl : Measure (Shao.Path ell) := Measure.pi (fun _ : Fin ell => rho)
    let wall : Shao.Path r → ℝ := fun a => x * Real.sqrt (q + Shao.energy a)
    let E : Set (Shao.Path r) := {a | Shao.maxWithZero a ≤ wall a ∧
      wall a - v ≤ Shao.prefixSum a r ∧ Shao.prefixSum a r ≤ wall a}
    let L : Set (Shao.Path ell) :=
      {u | Shao.maxWithZero (fun i => -u (Fin.rev i)) ≤ v}
    let Z : Shao.Path k × Shao.Path ell → ℝ := fun p =>
      Shao.prefixSum p.1 k - x * Real.sqrt (q + Shao.energy p.2 + Shao.energy p.1)
    let G : Set (Shao.Path k × Shao.Path ell) := {p | p.2 ∈ L ∧
      -Shao.prefixSum p.2 ell - v ≤ Z p ∧ Z p ≤ -Shao.prefixSum p.2 ell}
    have hwallm : Measurable wall := measurable_const.mul
      ((measurable_const.add Shao.measurable_energy).sqrt)
    have hEm : MeasurableSet E :=
      (measurableSet_le Shao.measurable_maxWithZero hwallm).inter
        ((measurableSet_le (hwallm.sub_const v) (Shao.measurable_prefixSum r)).inter
          (measurableSet_le (Shao.measurable_prefixSum r) hwallm))
    have hLm : MeasurableSet L := by
      apply measurableSet_le _ measurable_const
      apply Shao.measurable_maxWithZero.comp
      exact Measurable.of_eval fun i => (measurable_pi_apply (X := fun _ : Fin ell => ℝ) (Fin.rev i)).neg
    have hZm : Measurable Z := ((Shao.measurable_prefixSum k).comp measurable_fst).sub
      (measurable_const.mul (((measurable_const.add (Shao.measurable_energy.comp measurable_snd)).add
        (Shao.measurable_energy.comp measurable_fst)).sqrt))
    have hGm : MeasurableSet G := (hLm.preimage measurable_snd).inter
      ((measurableSet_le (((Shao.measurable_prefixSum ell).comp measurable_snd).neg.sub_const v) hZm).inter
        (measurableSet_le hZm (((Shao.measurable_prefixSum ell).comp measurable_snd).neg)))
    have hsplit : MeasurePreserving
        (fun a : Shao.Path r =>
          (Shao.Probability.Spitzer.head a k hkr, Shao.Probability.Spitzer.tail a k hkr))
        P (Pk.prod Pl) := by
      let e : Fin k ⊕ Fin (r - k) ≃ Fin r := finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hkr))
      have h1 := (measurePreserving_piCongrLeft (fun _ : Fin r => rho) e).symm
      have h2 := measurePreserving_sumPiEquivProdPi (fun _ : Fin k ⊕ Fin (r - k) => rho)
      convert h2.comp h1 using 1
      ext a i <;> change a _ = a _ <;> congr 1
    have hsplitSum (a : Shao.Path r) (f : ℝ → ℝ) :
        (∑ i : Fin r, f (a i)) =
          (∑ i : Fin k, f (Shao.Probability.Spitzer.head a k hkr i)) +
          (∑ i : Fin ell, f (Shao.Probability.Spitzer.tail a k hkr i)) := by
      let e : Fin k ⊕ Fin (r - k) ≃ Fin r := finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hkr))
      have hh := e.sum_comp (fun i : Fin r => f (a i))
      rw [Fintype.sum_sum_type] at hh
      exact hh.symm
    have hreversePrefix {m : ℕ} (a : Shao.Path m) (j : ℕ) (hj : j ≤ m) :
        Shao.prefixSum (fun i : Fin m => a (Fin.rev i)) j =
          Shao.prefixSum a m - Shao.prefixSum a (m - j) := by
      have he : (∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < j), a (Fin.rev i)) =
          ∑ i ∈ Finset.univ.filter (fun i : Fin m => m - j ≤ i.val), a i := by
        apply Finset.sum_equiv Fin.revPerm
        · intro i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          change (i.val < j ↔ m - j ≤ (Fin.rev i).val)
          rw [Fin.val_rev]
          have hi := i.is_lt
          omega
        · intro i _; rfl
      have hh := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin m => i.val < m - j) a
      simp only [not_lt] at hh
      rw [Shao.prefixSum_length]
      change (∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < j), a (Fin.rev i)) =
        (∑ i : Fin m, a i) - ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < m - j), a i
      rw [he]
      linarith only [hh]
    have hreverse (a : Shao.Path r) (j : ℕ) (hj : j ≤ ell) :
        Shao.prefixSum (fun i : Fin ell => Shao.Probability.Spitzer.tail a k hkr (Fin.rev i)) j =
          Shao.prefixSum a r - Shao.prefixSum a (r - j) := by
      have hl : ell ≤ r := Nat.sub_le _ _
      have he : (fun i : Fin ell => Shao.Probability.Spitzer.tail a k hkr (Fin.rev i)) =
          Shao.Probability.Spitzer.head (fun i : Fin r => a (Fin.rev i)) ell hl := by
        funext i
        dsimp [Shao.Probability.Spitzer.tail, Shao.Probability.Spitzer.head]
        congr 1
        apply Fin.ext
        simp only [Fin.val_rev]
        have hi := i.is_lt
        dsimp [ell] at hi ⊢
        omega
      rw [he, Shao.Probability.Spitzer.head_prefixSum _ _ _ _ hj,
        hreversePrefix _ _ (hj.trans hl)]
    have hsub : E ⊆ (fun a : Shao.Path r =>
        (Shao.Probability.Spitzer.head a k hkr, Shao.Probability.Spitzer.tail a k hkr)) ⁻¹' G := by
      intro a ha
      have hS : Shao.prefixSum a r =
          Shao.prefixSum (Shao.Probability.Spitzer.head a k hkr) k +
          Shao.prefixSum (Shao.Probability.Spitzer.tail a k hkr) ell := by
        simpa only [ell, Shao.prefixSum_length, id_eq] using hsplitSum a id
      have hQ : Shao.energy a = Shao.energy (Shao.Probability.Spitzer.head a k hkr) +
          Shao.energy (Shao.Probability.Spitzer.tail a k hkr) := hsplitSum a (fun z => z ^ 2)
      have hqe : q + Shao.energy (Shao.Probability.Spitzer.tail a k hkr) +
          Shao.energy (Shao.Probability.Spitzer.head a k hkr) = q + Shao.energy a := by linarith only [hQ]
      refine ⟨?_, ?_, ?_⟩
      · change Shao.maxWithZero (-(fun i : Fin ell => Shao.Probability.Spitzer.tail a k hkr (Fin.rev i))) ≤ v
        apply (Shao.maxWithZero_le_iff _ v).2
        intro j hj
        rw [Shao.prefixSum_neg, hreverse a j hj]
        have hm := (Shao.maxWithZero_le_iff a (wall a)).1 ha.1 (r - j) (Nat.sub_le _ _)
        linarith only [hm, ha.2.1]
      all_goals
        dsimp only [Z, Prod.fst, Prod.snd]
        rw [hqe]
        change _ ≤ _
        dsimp only [E, Set.mem_setOf_eq, wall] at ha
        linarith only [hS, ha.2.1, ha.2.2]
    have hsect (u : Shao.Path ell) : Pk.real {a | (a, u) ∈ G} ≤
        84 * (v + beta) / Real.sqrt (k : ℝ) := by
      have hh := anib_actual_wall_interval_concentration rho bound hb hsupport hm hsecond k hk
        hbscale x hx0.le hslope (q + Shao.energy u)
        (-Shao.prefixSum u ell - v) (-Shao.prefixSum u ell)
        (add_nonneg hq (Shao.energy_nonneg u)) (by linarith only [hv])
      apply (measureReal_mono (μ := Pk) (show {a | (a, u) ∈ G} ⊆
        {a : Shao.Path k | -Shao.prefixSum u ell - v ≤
          Shao.prefixSum a k - x * Real.sqrt (q + Shao.energy u + Shao.energy a) ∧
          Shao.prefixSum a k - x * Real.sqrt (q + Shao.energy u + Shao.energy a) ≤
            -Shao.prefixSum u ell} from fun _ ha => ha.2)).trans
      convert hh using 1 <;> ring
    have hG : (Pk.prod Pl).real G ≤
        (84 * (v + beta) / Real.sqrt (k : ℝ)) * Pl.real L := by
      let A : ℝ := 84 * (v + beta) / Real.sqrt (k : ℝ)
      have hA : 0 ≤ A := by dsimp [A]; positivity
      change (Pk.prod Pl).real G ≤ A * Pl.real L
      let f : Shao.Path k × Shao.Path ell → ℝ := G.indicator (fun _ => 1)
      have hfi : Integrable f (Pk.prod Pl) := (integrable_const 1).indicator hGm
      have hval : (∫ p, f p ∂Pk.prod Pl) = (Pk.prod Pl).real G := integral_indicator_one hGm
      have hLval : (∫ u, L.indicator (fun _ => A) u ∂Pl) = A * Pl.real L := by
        rw [integral_indicator_const A hLm]
        simp only [smul_eq_mul, mul_comm]
      rw [← hval, integral_prod_symm f hfi, ← hLval]
      apply integral_mono hfi.integral_prod_right ((integrable_const A).indicator hLm)
      intro u
      let S : Set (Shao.Path k) := {a | (a, u) ∈ G}
      have hSm : MeasurableSet S := hGm.preimage (measurable_id.prodMk measurable_const)
      have hinner : (∫ a, f (a, u) ∂Pk) = Pk.real S := integral_indicator_one hSm
      change (∫ a, f (a, u) ∂Pk) ≤ L.indicator (fun _ => A) u
      rw [hinner]
      by_cases hu : u ∈ L
      · rw [Set.indicator_of_mem hu]
        exact hsect u
      · rw [Set.indicator_of_notMem hu]
        have hempty : S = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.2
          exact fun a ha => hu ha.1
        simp only [hempty, measureReal_empty, le_refl]
    have hL : Pl.real L ≤ Cs * (v + beta) / Real.sqrt (ell : ℝ) :=
      hSurv rho bound hb hsupport hm hsecond ell hell v hv
    have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
    have hroot : (r : ℝ) ≤ 4 * Real.sqrt (k : ℝ) * Real.sqrt (ell : ℝ) := by
      have hk4 : (r : ℝ) ≤ 4 * (k : ℝ) := by exact_mod_cast (by omega : r ≤ 4 * k)
      have hl4 : (r : ℝ) ≤ 4 * (ell : ℝ) := by exact_mod_cast (by omega : r ≤ 4 * ell)
      have hp := mul_le_mul hk4 hl4 hrR.le (by positivity : (0 : ℝ) ≤ 4 * k)
      have hk2 := Real.sq_sqrt hkR.le
      have hl2 := Real.sq_sqrt hellR.le
      apply (sq_le_sq₀ hrR.le (by positivity)).1
      rw [mul_pow, mul_pow, hk2, hl2]
      nlinarith only [hp]
    have hprob : P.real E ≤ (Pk.prod Pl).real G := by
      apply (measureReal_mono hsub).trans
      have he := congrArg (fun m : Measure (Shao.Path k × Shao.Path ell) => m G) hsplit.map_eq
      rw [Measure.map_apply hsplit.measurable hGm] at he
      exact le_of_eq (congrArg ENNReal.toReal he)
    change P.real E ≤ _
    calc
      _ ≤ (84 * (v + beta) / Real.sqrt (k : ℝ)) * (Cs * (v + beta) / Real.sqrt (ell : ℝ)) :=
        hprob.trans (hG.trans (mul_le_mul_of_nonneg_left hL (by positivity)))
      _ ≤ C * (v + beta) ^ 2 / (r : ℝ) := by
        dsimp [C]
        apply (le_div_iff₀ hrR).2
        have hh := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 84 * Cs * (v + beta) ^ 2 by positivity)
        field_simp at hh ⊢
        nlinarith only [hh]
  refine ⟨C, hC, ?_⟩
  intro rho hProb bound hb hsupport hm hsecond beta n hn x hx hscale r hr hrn hnr q v s hq hv hs wall
  letI : IsProbabilityMeasure rho := hProb
  rcases hs with rfl | rfl
  · simpa only [one_smul, one_mul] using
      hUpper rho bound hb hsupport hm hsecond n hn x hx hscale r hr hrn hnr q v hq hv
  · let rhoNeg : Measure ℝ := Measure.map (fun z : ℝ => -z) rho
    letI : IsProbabilityMeasure rhoNeg := by dsimp [rhoNeg]; infer_instance
    have hbNeg : ∀ᵐ z : ℝ ∂rhoNeg, |z| ≤ bound := by
      rw [ae_map_iff measurable_neg.aemeasurable
        (measurableSet_le continuous_abs.measurable measurable_const)]
      simpa only [abs_neg] using hsupport
    have hmNeg : (∫ z : ℝ, z ∂rhoNeg) = 0 := by
      rw [show rhoNeg = Measure.map (fun z : ℝ => -z) rho from rfl,
        integral_map measurable_neg.aemeasurable (by fun_prop), integral_neg, hm, neg_zero]
    have h2Neg : (∫ z : ℝ, z ^ 2 ∂rhoNeg) = 1 := by
      rw [show rhoNeg = Measure.map (fun z : ℝ => -z) rho from rfl,
        integral_map measurable_neg.aemeasurable (by fun_prop)]
      simpa only [neg_sq] using hsecond
    have hb3 : (∫ z : ℝ, |z| ^ 3 ∂rhoNeg) = beta := by
      rw [show rhoNeg = Measure.map (fun z : ℝ => -z) rho from rfl,
        integral_map measurable_neg.aemeasurable (by fun_prop)]
      simp only [abs_neg]; rfl
    have hh := hUpper rhoNeg bound hb hbNeg hmNeg h2Neg n hn x hx hscale r hr hrn hnr q v hq hv
    have hmap : Measure.map (fun a : Shao.Path r => -a)
        (Measure.pi (fun _ : Fin r => rho)) = Measure.pi (fun _ : Fin r => rhoNeg) :=
      Measure.pi_map_pi (fun _ : Fin r => measurable_neg.aemeasurable)
    have hwm : Measurable (fun a : Shao.Path r => x * Real.sqrt (q + Shao.energy a)) :=
      measurable_const.mul ((measurable_const.add Shao.measurable_energy).sqrt)
    have hEm : MeasurableSet {a : Shao.Path r | Shao.maxWithZero a ≤ x * Real.sqrt (q + Shao.energy a) ∧
        x * Real.sqrt (q + Shao.energy a) - v ≤ Shao.prefixSum a r ∧
        Shao.prefixSum a r ≤ x * Real.sqrt (q + Shao.energy a)} :=
      (measurableSet_le Shao.measurable_maxWithZero hwm).inter
        ((measurableSet_le (hwm.sub_const v) (Shao.measurable_prefixSum r)).inter
          (measurableSet_le (Shao.measurable_prefixSum r) hwm))
    rw [hb3, ← hmap, Measure.real_def, Measure.map_apply (by fun_prop) hEm] at hh
    change ((Measure.pi (fun _ : Fin r => rho)).real
      {a : Shao.Path r | Shao.maxWithZero (-a) ≤ x * Real.sqrt (q + Shao.energy (-a)) ∧
        x * Real.sqrt (q + Shao.energy (-a)) - v ≤ Shao.prefixSum (-a) r ∧
        Shao.prefixSum (-a) r ≤ x * Real.sqrt (q + Shao.energy (-a))}) ≤ _ at hh
    simpa only [Shao.energy_neg, Shao.prefixSum_neg, neg_one_smul, neg_one_mul, wall] using hh

private theorem anib_actual_interval_kernel_data
    {ΩB : Type*} [MeasurableSpace ΩB]
    (Bm : NNReal → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hBm : IsBrownianReal Bm PB) :
    let Q : Measure BridgeNoise := bridgeLaw Bm PB
    Measurable (actualDerivativeFamily Q .interval) ∧
      KernelBounds .interval (eventCompletionKernel .interval Q)
        (actualDerivativeFamily Q .interval) 4 ∧
      ∀ w y T z : ℝ, 0 < w → 0 < T → |y| < w → |z| < w →
        HasDerivAt (fun s : ℝ => eventCompletionKernel .interval Q (w, s, T, z))
          (actualDerivativeFamily Q .interval (w, y, T, z)) y := by
  classical
  intro Q
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw Bm PB hBm
  have hReflection : Shao.Probability.SourceActualLocalProfileBudget.HalflineReflectionIdentities Q := by
    constructor
    · intro w y T z _hw hT hy hz
      simpa only [Shao.C2.HalfLineReflectionFormula.upperReflection] using
        Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula Bm PB hBm w y T z hT hy hz
    · intro w y T z _hw hT hy hz
      simpa only [Shao.C2.HalfLineReflectionFormula.lowerReflection] using
        Shao.C2.BridgeLowerIdentification.bridge_lower_formula Bm PB hBm w y T z hT hy hz
  have hReg (w y T z : ℝ) (hw : 0 < w) (hT : 0 < T) (hy : |y| < w) (hz : |z| < w) :
      DifferentiableAt ℝ (fun s : ℝ =>
        Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w s T z) y :=
    (Shao.C2.BridgeIntervalImageResolved.sourceIntervalCompletion_spatial_hasDerivAt
      Bm PB hBm w y T z hw hy hz hT).differentiableAt
  have hh := Shao.Probability.SourceActualIntervalProfileBudget.actual_interval_kernel_data Q hReflection hReg
  simpa only [actualDerivativeFamily] using hh

private theorem anib_local_actual_negative_cubic :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ΩB : Type*} [MeasurableSpace ΩB]
        (Bm : NNReal → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
        IsBrownianReal Bm PB →
        let Q : Measure BridgeNoise := bridgeLaw Bm PB
        ∀ w y T z b : ℝ, 0 < w → |y| < w → |z| < w → 0 < T →
          max (-localSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
            w y T z b) 0 ≤
            if b ^ 2 ≤ T / 2 ∧ (w ≤ y + b ∨ y + b ≤ -w) then
              C * (|b| / Real.sqrt T) ^ 3 *
                (1 + |z - y| / Real.sqrt T) ^ 3
            else 0 := by
  classical
  let C0 : ℝ := 2 * Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant
  have hC0 : 0 ≤ C0 := mul_nonneg (by norm_num)
    Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant_nonneg
  refine ⟨C0 + 1, by positivity, ?_⟩
  intro ΩB hΩB Bm PB hPB hBm Q w y T z b hw hy hz hT
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw Bm PB hBm
  have hKd := anib_actual_interval_kernel_data Bm PB hBm
  have hDer : deriv (fun s : ℝ => Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w s T z) y =
      actualDerivativeFamily Q .interval (w, y, T, z) := by
    have hf : (fun s : ℝ => Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w s T z) =
        (fun s : ℝ => eventCompletionKernel .interval Q (w, s, T, z)) := by
      funext s
      exact Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion_pos Q w s T z hT
    rw [hf]
    exact (hKd.2.2 w y T z hw hT hy hz).deriv
  have hReg := Shao.C2.BridgeIntervalImageResolved.sourceIntervalCompletion_spatial_hasDerivAt
    Bm PB hBm w y T z hw hy hz hT
  let K : ℝ := C0 * (1 / Real.sqrt T) ^ 3 * (1 + |z - y| / Real.sqrt T) ^ 3
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hp (p : ℝ) (hs : p ^ 2 ≤ T / 2) (hn : |y + p| ≤ w) :
      |Shao.C2.ActualIntervalProjection.sourceRemainder Q w y T z p| ≤ K * |p| ^ 3 := by
    have hh := Shao.C2.BridgeIntervalImageResolved.sourceRemainder_small_bound Bm PB hBm
      w y T z p hw hy hz hT hs hn
    have hprof := (Shao.C2.IntervalGaussianLocal.intervalIncrementProfile_bounds w y T z p hy hz hT).2
    apply hh.trans
    have hmul := mul_le_mul_of_nonneg_left hprof (show 0 ≤
      Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant * (|p| / Real.sqrt T) ^ 3 *
        (1 + |z - y| / Real.sqrt T) ^ 3 by
          exact mul_nonneg (mul_nonneg Shao.C2.IntervalImageRevealBounds.compensatedProfileConstant_nonneg
            (by positivity)) (by positivity))
    convert hmul using 1 <;> dsimp [K, C0] <;> ring
  by_cases hs : b ^ 2 ≤ T / 2
  · by_cases hu : w ≤ y + b
    · have hgap : 0 < w - y := by linarith only [(abs_lt.mp hy).2]
      have hbgap : w - y ≤ b := by linarith only [hu]
      have hb : 0 < b := hgap.trans_le hbgap
      have hpSmall : (w - y) ^ 2 ≤ T / 2 := by nlinarith only [hs, hgap, hbgap]
      have hnew : |y + (w - y)| ≤ w := by
        have he : y + (w - y) = w := by ring
        rw [he, abs_of_pos hw]
      have hbud := Shao.C2.ActualIntervalProjection.source_upper_projection_negative_budget Q
        w y T z b K hw hy hz hT hs hu hK hReg.differentiableAt
        (hp (w - y) hpSmall hnew)
      have hneg : max (-localSeparatedOvershoot .interval (actualDerivativeFamily Q .interval) w y T z b) 0 =
          max (-Shao.C2.ActualIntervalProjection.upperOvershoot Q w y T z b) 0 := by
        simp only [localSeparatedOvershoot, projectionIncrement, hT, hs, true_and, if_true, if_pos hu,
          Shao.C2.ActualIntervalProjection.upperOvershoot, Shao.C2.ProjectionOvershoot.projectionOvershoot,
          Shao.C2.ProjectionOvershoot.projectionFactor, hDer]
      rw [if_pos ⟨hs, Or.inl hu⟩, hneg]
      have hh := (le_add_of_nonneg_left (abs_nonneg _)).trans hbud.1 |>.trans hbud.2
      apply hh.trans
      dsimp [K]
      have hinc := mul_le_mul_of_nonneg_right (show C0 ≤ C0 + 1 by linarith)
        (show 0 ≤ (|b| / Real.sqrt T) ^ 3 * (1 + |z - y| / Real.sqrt T) ^ 3 by positivity)
      convert hinc using 1 <;> ring
    · by_cases hl : y + b ≤ -w
      · have hgap : 0 < w + y := by linarith only [(abs_lt.mp hy).1]
        have hbgap : w + y ≤ -b := by linarith only [hl]
        have hpSmall : (-w - y) ^ 2 ≤ T / 2 := by nlinarith only [hs, hgap, hbgap]
        have hnew : |y + (-w - y)| ≤ w := by
          have he : y + (-w - y) = -w := by ring
          rw [he, abs_neg, abs_of_pos hw]
        have hbud := Shao.C2.ActualIntervalProjection.source_lower_projection_negative_budget Q
          w y T z b K hw hy hz hT hs hl hK hReg.differentiableAt
          (hp (-w - y) hpSmall hnew)
        have hneg : max (-localSeparatedOvershoot .interval (actualDerivativeFamily Q .interval) w y T z b) 0 =
            max (-Shao.C2.ActualIntervalProjection.lowerOvershoot Q w y T z b) 0 := by
          simp only [localSeparatedOvershoot, projectionIncrement, hT, hs, true_and, if_true, if_neg hu, if_pos hl,
            Shao.C2.ActualIntervalProjection.lowerOvershoot, Shao.C2.ProjectionOvershoot.projectionOvershoot,
            Shao.C2.ProjectionOvershoot.projectionFactor, hDer]
          congr 2
          ring
        rw [if_pos ⟨hs, Or.inr hl⟩, hneg]
        have hh := (le_add_of_nonneg_left (abs_nonneg _)).trans hbud.1 |>.trans hbud.2
        apply hh.trans
        dsimp [K]
        have hinc := mul_le_mul_of_nonneg_right (show C0 ≤ C0 + 1 by linarith)
          (show 0 ≤ (|b| / Real.sqrt T) ^ 3 * (1 + |z - y| / Real.sqrt T) ^ 3 by positivity)
        convert hinc using 1 <;> ring
      · simp only [localSeparatedOvershoot, projectionIncrement, hT, hs, true_and, if_true, if_neg hu,
          if_neg hl, sub_self, neg_zero, zero_mul, max_self,
          if_neg (show ¬(w ≤ y + b ∨ y + b ≤ -w) from not_or.mpr ⟨hu, hl⟩), le_refl]
  · simp only [localSeparatedOvershoot, show ¬(0 < T ∧ b ^ 2 ≤ T / 2) by tauto,
      show ¬(b ^ 2 ≤ T / 2 ∧ (w ≤ y + b ∨ y + b ≤ -w)) by tauto,
      if_false, neg_zero, max_self, le_refl]

private theorem anib_capped_source_negative_domination
    {n : ℕ} (Q : Measure BridgeNoise) (a : Shao.Path n) (x h : ℝ)
    (hh : 0 < h) (nu : LabelPerm n → ℕ)
    (hnu : ∀ sigma : LabelPerm n, nu sigma ≤ energyCutoff a h sigma)
    (r : ℕ) (sigma : LabelPerm n) :
    max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
      a x nu r sigma) 0 ≤
      if h ≤ remainingEnergy a r sigma then
        max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
          a x (fun _ : LabelPerm n => n) r sigma) 0
      else 0 := by
  classical
  by_cases hr : r < n
  · by_cases hact : r < nu sigma ∧ sourceAlive .interval a x r sigma ∧ 0 < remainingEnergy a r sigma
    · have hcut := (energy_cutoff_data a h hh).2.2 sigma r (hact.1.trans_le (hnu sigma))
      have hfull : r < n ∧ sourceAlive .interval a x r sigma ∧ 0 < remainingEnergy a r sigma :=
        ⟨hr, hact.2⟩
      simp only [sourceSeparatedOvershoot, dif_pos hr, if_pos hact, if_pos hcut.2,
        if_pos hfull, le_refl]
    · have hzero : sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval) a x nu r sigma = 0 := by
        simp only [sourceSeparatedOvershoot, dif_pos hr, if_neg hact]
      rw [hzero]
      simp only [neg_zero, max_self]
      split_ifs <;> positivity
  · simp only [sourceSeparatedOvershoot, dif_neg hr, neg_zero, max_self]
    split_ifs <;> exact le_rfl

private theorem anib_bill_measurable_integrable
    {ΩB : Type*} [MeasurableSpace ΩB]
    (Bm : NNReal → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hBm : IsBrownianReal Bm PB)
    (n : ℕ) (P : Measure (Shao.Path n)) [IsProbabilityMeasure P]
    (x : ℝ) (hx : 0 < x)
    (nu : Shao.Path n → LabelPerm n → ℕ)
    (hnum : ∀ sigma : LabelPerm n, Measurable (fun a : Shao.Path n => nu a sigma)) :
    let Q : Measure BridgeNoise := bridgeLaw Bm PB
    let bill : (Shao.Path n × LabelPerm n) → ℝ :=
      actualBadIntervalNegativeBill Q x nu
    Measurable bill ∧ Integrable bill (revealLaw P) ∧ ∀ p, 0 ≤ bill p := by
  classical
  intro Q bill
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw Bm PB hBm
  letI : IsProbabilityMeasure (revealLaw P) := by unfold revealLaw; infer_instance
  have hd := anib_actual_interval_kernel_data Bm PB hBm
  have hp := source_parts_measurable_integrable .interval (eventCompletionKernel .interval Q)
    (actualDerivativeFamily Q .interval) (eventCompletionKernel_data .interval Q).1 hd.1
    4 hd.2.1 P x hx nu hnum
  let term : ℕ → (Shao.Path n × LabelPerm n) → ℝ := fun r p =>
    if 3 * x * Real.sqrt (remainingEnergy p.1 r p.2) / 2 ≤ |remainingSum p.1 r p.2| then
      max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
        p.1 x (nu p.1) r p.2) 0 else 0
  have hm (r : ℕ) : Measurable (term r) := by
    have hSep : Measurable (fun p : Shao.Path n × LabelPerm n =>
        sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval) p.1 x (nu p.1) r p.2) := by
      apply measurable_from_prod_countable_left
      intro sigma
      exact (hp.1 sigma r).2
    have hT : Measurable (fun p : Shao.Path n × LabelPerm n => remainingEnergy p.1 r p.2) := by
      apply measurable_from_prod_countable_left
      intro sigma
      change Measurable (fun a : Shao.Path n => remainingEnergy a r sigma)
      exact Shao.measurable_energy.sub ((Shao.measurable_prefixSquares r).comp
        (Measurable.of_eval fun i => measurable_pi_apply (X := fun _ : Fin n => ℝ) (sigma i)))
    have hd : Measurable (fun p : Shao.Path n × LabelPerm n => remainingSum p.1 r p.2) := by
      apply measurable_from_prod_countable_left
      intro sigma
      change Measurable (fun a : Shao.Path n => remainingSum a r sigma)
      exact (Shao.measurable_prefixSum n).sub ((Shao.measurable_prefixSum r).comp
        (Measurable.of_eval fun i => measurable_pi_apply (X := fun _ : Fin n => ℝ) (sigma i)))
    exact Measurable.ite (measurableSet_le ((measurable_const.mul hT.sqrt).div_const 2)
      (continuous_abs.measurable.comp hd))
      (hSep.neg.max measurable_const) measurable_const
  have hbound (r : ℕ) (p : Shao.Path n × LabelPerm n) :
      |term r p| ≤ 16 * (1 + (n : ℝ)) := by
    have h := (source_parts_uniform_bound .interval (eventCompletionKernel .interval Q)
      (actualDerivativeFamily Q .interval) 4 hd.2.1 p.1 x hx (nu p.1) r p.2).1
    dsimp [term]
    split_ifs
    · rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le ((neg_le_abs _).trans (by convert h using 1 <;> ring)) (by positivity)
    · simp; positivity
  have hi (r : ℕ) : Integrable (term r) (revealLaw P) :=
    (integrable_const (16 * (1 + (n : ℝ)))).mono' (hm r).aestronglyMeasurable
      (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hbound r p)
  refine ⟨?_, ?_, ?_⟩
  · dsimp [bill, actualBadIntervalNegativeBill]
    apply Finset.measurable_sum
    intro r _
    exact hm r
  · dsimp [bill, actualBadIntervalNegativeBill]
    exact integrable_finsetSum _ fun r _ => hi r
  · intro p
    apply Finset.sum_nonneg
    intro r _
    split_ifs <;> positivity

private theorem anib_cap_reorder_reduction
    (rho : Measure ℝ) [IsProbabilityMeasure rho]
    {ΩB : Type*} [MeasurableSpace ΩB]
    (Bm : NNReal → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hBm : IsBrownianReal Bm PB)
    (n : ℕ) (x h : ℝ) (hx : 0 < x) (hh : 0 < h)
    (nu : Shao.Path n → LabelPerm n → ℕ)
    (hnum : ∀ sigma : LabelPerm n, Measurable (fun a : Shao.Path n => nu a sigma))
    (hnu : ∀ a sigma, nu a sigma ≤ energyCutoff a h sigma) :
    let Q : Measure BridgeNoise := bridgeLaw Bm PB
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
    let G : Shao.Path n → ℝ := fun a =>
      ∑ r ∈ Finset.range n,
        if h ≤ remainingEnergy a r (Equiv.refl (Fin n)) ∧
            3 * x * Real.sqrt (remainingEnergy a r (Equiv.refl (Fin n))) / 2 ≤
              |remainingSum a r (Equiv.refl (Fin n))| then
          max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
            a x (fun _ : LabelPerm n => n) r (Equiv.refl (Fin n))) 0
        else 0
    Measurable G ∧ Integrable G P ∧
      (∫ p, actualBadIntervalNegativeBill Q x nu p ∂revealLaw P) ≤
        ∫ a, G a ∂P := by
  classical
  intro Q P G
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw Bm PB hBm
  letI : IsProbabilityMeasure (revealLaw P) := by unfold revealLaw; infer_instance
  have hk := anib_actual_interval_kernel_data Bm PB hBm
  have hparts := source_parts_measurable_integrable .interval (eventCompletionKernel .interval Q)
    (actualDerivativeFamily Q .interval) (eventCompletionKernel_data .interval Q).1 hk.1
    4 hk.2.1 P x hx (fun _ _ => n) (fun _ => measurable_const)
  let term : ℕ → Shao.Path n → ℝ := fun r a =>
    if h ≤ remainingEnergy a r (Equiv.refl (Fin n)) ∧
        3 * x * Real.sqrt (remainingEnergy a r (Equiv.refl (Fin n))) / 2 ≤
          |remainingSum a r (Equiv.refl (Fin n))| then
      max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
        a x (fun _ : LabelPerm n => n) r (Equiv.refl (Fin n))) 0 else 0
  have htm (r : ℕ) : Measurable (term r) := by
    have hm := (hparts.1 (Equiv.refl (Fin n)) r).2
    apply Measurable.ite _ (hm.neg.max measurable_const) measurable_const
    have hTm : Measurable (fun a : Shao.Path n => remainingEnergy a r (Equiv.refl (Fin n))) :=
      Shao.measurable_energy.sub ((Shao.measurable_prefixSquares r).comp
        (Measurable.of_eval fun i => measurable_pi_apply (X := fun _ : Fin n => ℝ) i))
    have hdm : Measurable (fun a : Shao.Path n => remainingSum a r (Equiv.refl (Fin n))) :=
      (Shao.measurable_prefixSum n).sub ((Shao.measurable_prefixSum r).comp
        (Measurable.of_eval fun i => measurable_pi_apply (X := fun _ : Fin n => ℝ) i))
    exact (measurableSet_le measurable_const hTm).inter
      (measurableSet_le ((measurable_const.mul hTm.sqrt).div_const 2)
        (continuous_abs.measurable.comp hdm))
  have htb (r : ℕ) (a : Shao.Path n) : |term r a| ≤ 16 * (1 + (n : ℝ)) := by
    have hh := (source_parts_uniform_bound .interval (eventCompletionKernel .interval Q)
      (actualDerivativeFamily Q .interval) 4 hk.2.1 a x hx (fun _ => n) r (Equiv.refl (Fin n))).1
    dsimp [term]
    split_ifs
    · rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le ((neg_le_abs _).trans (by convert hh using 1 <;> ring)) (by positivity)
    · simp; positivity
  have hti (r : ℕ) : Integrable (term r) P :=
    (integrable_const (16 * (1 + (n : ℝ)))).mono' (htm r).aestronglyMeasurable
      (ae_of_all _ fun a => by simpa only [Real.norm_eq_abs] using htb r a)
  have hGm : Measurable G := by
    apply Finset.measurable_sum
    intro r _
    exact htm r
  have hGi : Integrable G P := integrable_finsetSum _ (fun r _ => hti r)
  have hperm (a : Shao.Path n) (sigma : LabelPerm n) :
      Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) n = Shao.prefixSum a n ∧
      Shao.energy (Shao.Probability.Spitzer.reorder a sigma) = Shao.energy a := by
    constructor
    · simp only [Shao.prefixSum_length, Shao.Probability.Spitzer.reorder]
      exact Equiv.sum_comp sigma a
    · exact Equiv.sum_comp sigma (fun i => a i ^ 2)
  have hcanonical (a : Shao.Path n) (sigma : LabelPerm n) (r : ℕ) :
      term r (randomReorder (a, sigma)) =
        if h ≤ remainingEnergy a r sigma ∧
            3 * x * Real.sqrt (remainingEnergy a r sigma) / 2 ≤ |remainingSum a r sigma| then
          max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
            a x (fun _ : LabelPerm n => n) r sigma) 0 else 0 := by
    let R : Shao.Path n := randomReorder (a, sigma)
    have htot : Shao.prefixSum R n = Shao.prefixSum a n ∧ Shao.energy R = Shao.energy a := hperm a sigma
    have hT : remainingEnergy R r (Equiv.refl (Fin n)) = remainingEnergy a r sigma := by
      change Shao.energy R - Shao.prefixSquares R r = Shao.energy a - Shao.prefixSquares R r
      rw [htot.2]
    have hd : remainingSum R r (Equiv.refl (Fin n)) = remainingSum a r sigma := by
      change Shao.prefixSum R n - Shao.prefixSum R r = Shao.prefixSum a n - Shao.prefixSum R r
      rw [htot.1]
    have hAlive : sourceAlive .interval R x r (Equiv.refl (Fin n)) ↔ sourceAlive .interval a x r sigma := by
      change (0 < Shao.energy R ∧ Interior .interval (x * Real.sqrt (Shao.energy R)) (Shao.prefixSum R n) ∧
        ∀ k : ℕ, k ≤ r → Interior .interval (x * Real.sqrt (Shao.energy R)) (Shao.prefixSum R k)) ↔
        (0 < Shao.energy a ∧ Interior .interval (x * Real.sqrt (Shao.energy a)) (Shao.prefixSum a n) ∧
        ∀ k : ℕ, k ≤ r → Interior .interval (x * Real.sqrt (Shao.energy a)) (Shao.prefixSum R k))
      rw [htot.1, htot.2]
    have hSource : sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
        R x (fun _ : LabelPerm n => n) r (Equiv.refl (Fin n)) =
        sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
          a x (fun _ : LabelPerm n => n) r sigma := by
      unfold sourceSeparatedOvershoot
      by_cases hr : r < n
      · rw [dif_pos hr, dif_pos hr]
        simp only [hAlive, hT]
        congr 1
        change localSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
            (x * Real.sqrt (Shao.energy R)) (Shao.prefixSum R r) (remainingEnergy a r sigma)
            (Shao.prefixSum R n) (a (sigma ⟨r, hr⟩)) = _
        rw [htot.1, htot.2]
        rfl
      · rw [dif_neg hr, dif_neg hr]
    change (if h ≤ remainingEnergy R r (Equiv.refl (Fin n)) ∧
        3 * x * Real.sqrt (remainingEnergy R r (Equiv.refl (Fin n))) / 2 ≤
          |remainingSum R r (Equiv.refl (Fin n))| then
      max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
        R x (fun _ : LabelPerm n => n) r (Equiv.refl (Fin n))) 0 else 0) = _
    rw [hT, hd, hSource]
  have hdom (p : Shao.Path n × LabelPerm n) : actualBadIntervalNegativeBill Q x nu p ≤ G (randomReorder p) := by
    apply Finset.sum_le_sum
    intro r _
    change (if 3 * x * Real.sqrt (remainingEnergy p.1 r p.2) / 2 ≤ |remainingSum p.1 r p.2| then
      max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
        p.1 x (nu p.1) r p.2) 0 else 0) ≤ term r (randomReorder (p.1, p.2))
    rw [hcanonical p.1 p.2 r]
    have hh := anib_capped_source_negative_domination Q p.1 x h hh (nu p.1) (hnu p.1) r p.2
    by_cases hbad : 3 * x * Real.sqrt (remainingEnergy p.1 r p.2) / 2 ≤ |remainingSum p.1 r p.2|
    · simpa only [hbad, if_true, and_true] using hh
    · simp only [hbad, if_false, and_false, le_refl]
  have hRm : Measurable (randomReorder : Shao.Path n × LabelPerm n → Shao.Path n) :=
    measurable_from_prod_countable_left (fun sigma => by
      apply Measurable.of_eval
      intro i
      exact measurable_pi_apply (sigma i))
  have hmap : Measure.map randomReorder (revealLaw P) = P := by
    have hInd : iIndepFun (fun i : Fin n => Function.eval i) P :=
      iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)
    have hLaw (i : Fin n) : IdentDistrib (Function.eval i) (id : ℝ → ℝ) P rho :=
      ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable,
        by simp only [Measure.map_id]; exact (measurePreserving_eval (fun _ : Fin n => rho) i).map_eq⟩
    exact iid_randomPermutation_map_eq_pi P rho (fun i : Fin n => Function.eval i)
      (fun i => measurable_pi_apply i) hInd hLaw
  have hmp : MeasurePreserving randomReorder (revealLaw P) P := ⟨hRm, hmap⟩
  have hbill := anib_bill_measurable_integrable Bm PB hBm n P x hx nu hnum
  refine ⟨hGm, hGi, ?_⟩
  calc
    _ ≤ ∫ p, G (randomReorder p) ∂revealLaw P :=
      integral_mono hbill.2.1 (hmp.integrable_comp_of_integrable hGi) hdom
    _ = ∫ a, G a ∂P := by
      have hi := integral_map (μ := revealLaw P) hRm.aemeasurable hGm.aestronglyMeasurable
      rw [hmap] at hi
      exact hi.symm

private theorem anib_iid_rank_negative_disintegration
    (rho : Measure ℝ) [IsProbabilityMeasure rho]
    {ΩB : Type*} [MeasurableSpace ΩB]
    (Bm : NNReal → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hBm : IsBrownianReal Bm PB)
    (r t : ℕ) (ht : 0 < t) (x h : ℝ) (hx : 0 < x) (hh : 0 < h) :
    let Q : Measure BridgeNoise := bridgeLaw Bm PB
    let P : Measure (Shao.Path (r + t)) := Measure.pi (fun _ : Fin (r + t) => rho)
    let Pr : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => rho)
    let Pt : Measure (Shao.Path t) := Measure.pi (fun _ : Fin t => rho)
    let R : Shao.Path (r + t) → ℝ := fun a =>
      if h ≤ remainingEnergy a r (Equiv.refl (Fin (r + t))) ∧
          3 * x * Real.sqrt (remainingEnergy a r (Equiv.refl (Fin (r + t)))) / 2 ≤
            |remainingSum a r (Equiv.refl (Fin (r + t)))| then
        max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
          a x (fun _ : LabelPerm (r + t) => r + t) r (Equiv.refl (Fin (r + t)))) 0
      else 0
    let F : (Shao.Path r × Shao.Path t) → ℝ := fun p =>
      if h ≤ Shao.energy p.2 ∧
          3 * x * Real.sqrt (Shao.energy p.2) / 2 ≤ |Shao.prefixSum p.2 t| then
        max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
          (Fin.append p.1 p.2) x (fun _ : LabelPerm (r + t) => r + t)
          r (Equiv.refl (Fin (r + t)))) 0
      else 0
    Measurable F ∧ Integrable F (Pr.prod Pt) ∧ Integrable R P ∧
      (∫ a, R a ∂P) = ∫ u, (∫ v, F (v, u) ∂Pr) ∂Pt := by
  classical
  intro Q P Pr Pt R F
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw Bm PB hBm
  have hk := anib_actual_interval_kernel_data Bm PB hBm
  have hparts := source_parts_measurable_integrable .interval (eventCompletionKernel .interval Q)
    (actualDerivativeFamily Q .interval) (eventCompletionKernel_data .interval Q).1 hk.1
    4 hk.2.1 P x hx (fun _ _ => r + t) (fun _ => measurable_const)
  have hRm : Measurable R := by
    apply Measurable.ite _ (((hparts.1 (Equiv.refl (Fin (r + t))) r).2).neg.max measurable_const) measurable_const
    have hTm : Measurable (fun a : Shao.Path (r + t) => remainingEnergy a r (Equiv.refl (Fin (r + t)))) :=
      Shao.measurable_energy.sub ((Shao.measurable_prefixSquares r).comp
        (Measurable.of_eval fun i => measurable_pi_apply (X := fun _ : Fin (r + t) => ℝ) i))
    have hdm : Measurable (fun a : Shao.Path (r + t) => remainingSum a r (Equiv.refl (Fin (r + t)))) :=
      (Shao.measurable_prefixSum (r + t)).sub ((Shao.measurable_prefixSum r).comp
        (Measurable.of_eval fun i => measurable_pi_apply (X := fun _ : Fin (r + t) => ℝ) i))
    exact (measurableSet_le measurable_const hTm).inter
      (measurableSet_le ((measurable_const.mul hTm.sqrt).div_const 2)
        (continuous_abs.measurable.comp hdm))
  have hRb (a : Shao.Path (r + t)) : |R a| ≤ 16 * (1 + ((r + t : ℕ) : ℝ)) := by
    have hh := (source_parts_uniform_bound .interval (eventCompletionKernel .interval Q)
      (actualDerivativeFamily Q .interval) 4 hk.2.1 a x hx (fun _ => r + t) r (Equiv.refl (Fin (r + t)))).1
    dsimp [R]
    split_ifs
    · rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le ((neg_le_abs _).trans (by convert hh using 1 <;> ring)) (by positivity)
    · simp; positivity
  have hRi : Integrable R P := (integrable_const (16 * (1 + ((r + t : ℕ) : ℝ)))).mono'
    hRm.aestronglyMeasurable (ae_of_all _ fun a => by simpa only [Real.norm_eq_abs] using hRb a)
  have happ : MeasurePreserving (fun p : Shao.Path r × Shao.Path t => Fin.append p.1 p.2)
      (Pr.prod Pt) P := by
    have h1 := (measurePreserving_piCongrLeft (fun _ : Fin (r + t) => rho)
      (finSumFinEquiv : Fin r ⊕ Fin t ≃ Fin (r + t))).comp
      (measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin r ⊕ Fin t => rho))
    convert h1 using 1
    funext p i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [MeasurableEquiv.coe_piCongrLeft, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
        Equiv.piCongrLeft_apply, Equiv.sumPiEquivProdPi]
  have hstate (v : Shao.Path r) (u : Shao.Path t) :
      remainingEnergy (Fin.append v u) r (Equiv.refl (Fin (r + t))) = Shao.energy u ∧
      remainingSum (Fin.append v u) r (Equiv.refl (Fin (r + t))) = Shao.prefixSum u t := by
    have hE : Shao.energy (Fin.append v u) = Shao.energy v + Shao.energy u := by
      simp only [Shao.energy, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    have hP : Shao.prefixSquares (Fin.append v u) r = Shao.energy v := by
      simp [Shao.prefixSquares, Shao.energy, Finset.sum_filter, Fin.sum_univ_add]
    have hS : Shao.prefixSum (Fin.append v u) (r + t) = Shao.prefixSum v r + Shao.prefixSum u t := by
      simp only [Shao.prefixSum_length, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    have hhead : Shao.prefixSum (Fin.append v u) r = Shao.prefixSum v r := by
      simp [Shao.prefixSum, Finset.sum_filter, Fin.sum_univ_add]
    constructor
    · change Shao.energy (Fin.append v u) - Shao.prefixSquares (Fin.append v u) r = Shao.energy u
      rw [hE, hP]; ring
    · change Shao.prefixSum (Fin.append v u) (r + t) - Shao.prefixSum (Fin.append v u) r = Shao.prefixSum u t
      rw [hS, hhead]; ring
  have hF : F = fun p : Shao.Path r × Shao.Path t => R (Fin.append p.1 p.2) := by
    funext p
    dsimp only [F, R]
    rw [(hstate p.1 p.2).1, (hstate p.1 p.2).2]
  have hFm : Measurable F := by rw [hF]; exact hRm.comp happ.measurable
  have hFi : Integrable F (Pr.prod Pt) := by rw [hF]; exact happ.integrable_comp_of_integrable hRi
  refine ⟨hFm, hFi, hRi, ?_⟩
  calc
    _ = ∫ p, F p ∂Pr.prod Pt := by
      rw [hF]
      have hi := integral_map (μ := Pr.prod Pt) happ.measurable.aemeasurable hRm.aestronglyMeasurable
      rw [happ.map_eq] at hi
      exact hi
    _ = _ := integral_prod_symm _ hFi

private theorem anib_fixed_suffix_cubic_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        {ΩB : Type*} [MeasurableSpace ΩB]
        (Bm : NNReal → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
        IsBrownianReal Bm PB →
        let Q : Measure BridgeNoise := bridgeLaw Bm PB
        ∀ (r t : ℕ), 0 < t → ∀ (x h : ℝ), 0 < x → 0 < h →
          ∀ (u : Shao.Path t),
            let T : ℝ := Shao.energy u
            let d : ℝ := Shao.prefixSum u t
            let b : ℝ := if ht : 0 < t then u ⟨0, ht⟩ else 0
            let D : ℝ := if 0 < T then 1 + |d| / Real.sqrt T else 1
            let F : Shao.Path r → ℝ := fun v =>
              if h ≤ T ∧ 3 * x * Real.sqrt T / 2 ≤ |d| then
                max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
                  (Fin.append v u) x (fun _ : LabelPerm (r + t) => r + t)
                  r (Equiv.refl (Fin (r + t)))) 0
              else 0
            let marked3 : ℝ :=
              if 0 < T ∧ h ≤ T ∧ (3 * x / 2) * Real.sqrt T ≤ |d| then
                |b| ^ 3 / (Real.sqrt T) ^ 3 * D ^ 3
              else 0
            Integrable F (Measure.pi (fun _ : Fin r => rho)) ∧
              (∫ v, F v ∂Measure.pi (fun _ : Fin r => rho)) ≤ C * marked3 := by
  classical
  obtain ⟨C0, hC0, hlocal⟩ := anib_local_actual_negative_cubic
  refine ⟨C0, hC0, ?_⟩
  intro rho hProb ΩB hΩB Bm PB hPB hBm Q r t ht x h hx hh u T d b D F marked3
  letI : IsProbabilityMeasure rho := hProb
  let Pr : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => rho)
  have hdata := anib_iid_rank_negative_disintegration rho Bm PB hBm r t ht x h hx hh
  have hFm : Measurable F := hdata.1.comp (measurable_id.prodMk measurable_const)
  have hr : r < r + t := by omega
  have hstate (v : Shao.Path r) :
      remainingEnergy (Fin.append v u) r (Equiv.refl (Fin (r + t))) = T ∧
      remainingSum (Fin.append v u) r (Equiv.refl (Fin (r + t))) = d ∧
      (Fin.append v u) ⟨r, hr⟩ = b := by
    have hE : Shao.energy (Fin.append v u) = Shao.energy v + T := by
      simp only [Shao.energy, Fin.sum_univ_add, Fin.append_left, Fin.append_right]; rfl
    have hP : Shao.prefixSquares (Fin.append v u) r = Shao.energy v := by
      simp [Shao.prefixSquares, Shao.energy, Finset.sum_filter, Fin.sum_univ_add]
    have hS : Shao.prefixSum (Fin.append v u) (r + t) = Shao.prefixSum v r + d := by
      dsimp only [d]
      simp only [Shao.prefixSum_length, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    have hhead : Shao.prefixSum (Fin.append v u) r = Shao.prefixSum v r := by
      simp [Shao.prefixSum, Finset.sum_filter, Fin.sum_univ_add]
    refine ⟨?_, ?_, ?_⟩
    · change Shao.energy (Fin.append v u) - Shao.prefixSquares (Fin.append v u) r = T
      rw [hE, hP]; ring
    · change Shao.prefixSum (Fin.append v u) (r + t) - Shao.prefixSum (Fin.append v u) r = d
      rw [hS, hhead]; ring
    · have he : (⟨r, hr⟩ : Fin (r + t)) = Fin.natAdd r (⟨0, ht⟩ : Fin t) := by apply Fin.ext; simp
      rw [he, Fin.append_right]
      simp only [b, dif_pos ht]
  have hk := anib_actual_interval_kernel_data Bm PB hBm
  have hFb (v : Shao.Path r) : |F v| ≤ 16 * (1 + ((r + t : ℕ) : ℝ)) := by
    have hbnd := (source_parts_uniform_bound .interval (eventCompletionKernel .interval Q)
      (actualDerivativeFamily Q .interval) 4 hk.2.1 (Fin.append v u) x hx (fun _ => r + t) r (Equiv.refl _)).1
    dsimp only [F]
    split_ifs
    · rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le ((neg_le_abs _).trans (by convert hbnd using 1 <;> ring)) (by positivity)
    · simp; positivity
  have hFi : Integrable F Pr := (integrable_const (16 * (1 + ((r + t : ℕ) : ℝ)))).mono'
    hFm.aestronglyMeasurable (ae_of_all _ fun v => by simpa only [Real.norm_eq_abs] using hFb v)
  refine ⟨hFi, ?_⟩
  have hpoint (v : Shao.Path r) : F v ≤ C0 * marked3 := by
    by_cases hmask : h ≤ T ∧ 3 * x * Real.sqrt T / 2 ≤ |d|
    · have hT : 0 < T := hh.trans_le hmask.1
      have hmark : marked3 = |b| ^ 3 / (Real.sqrt T) ^ 3 * D ^ 3 := by
        apply if_pos
        exact ⟨hT, hmask.1, by nlinarith only [hmask.2]⟩
      rw [hmark]
      dsimp only [F]
      rw [if_pos hmask]
      let a : Shao.Path (r + t) := Fin.append v u
      let sigma : LabelPerm (r + t) := Equiv.refl _
      by_cases ha : sourceAlive .interval a x r sigma ∧ 0 < remainingEnergy a r sigma
      · have hw : 0 < actualWall a x := mul_pos hx (Real.sqrt_pos.2 ha.1.1)
        have hy : |Shao.prefixSum a r| < actualWall a x := by
          have hh := abs_lt.mpr (ha.1.2.2 r le_rfl)
          change |Shao.prefixSum a r| < actualWall a x at hh
          exact hh
        have hz : |Shao.prefixSum a (r + t)| < actualWall a x := abs_lt.mpr ha.1.2.1
        have hc := hlocal Bm PB hBm (actualWall a x) (Shao.prefixSum a r) T
          (Shao.prefixSum a (r + t)) b hw hy hz hT
        have hden : Shao.prefixSum a (r + t) - Shao.prefixSum a r = d := by
          have hh := (hstate v).2.1
          change Shao.prefixSum a (r + t) - Shao.prefixSum a r = d at hh
          exact hh
        have hfull : r < r + t ∧ sourceAlive .interval a x r sigma ∧
            0 < remainingEnergy a r sigma := ⟨hr, ha⟩
        change max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
          a x (fun _ : LabelPerm (r + t) => r + t) r sigma) 0 ≤ _
        rw [sourceSeparatedOvershoot, dif_pos hr, if_pos hfull]
        change max (-localSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
          (actualWall a x) (Shao.prefixSum a r) (remainingEnergy a r sigma)
          (Shao.prefixSum a (r + t)) (a ⟨r, hr⟩)) 0 ≤ _
        rw [show remainingEnergy a r sigma = T from (hstate v).1,
          show a ⟨r, hr⟩ = b from (hstate v).2.2]
        apply hc.trans
        rw [hden]
        simp only [D, if_pos hT]
        split_ifs
        · rw [div_pow]; ring_nf; exact le_rfl
        · positivity
      · have hzero : sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
            a x (fun _ : LabelPerm (r + t) => r + t) r sigma = 0 := by
          rw [sourceSeparatedOvershoot, dif_pos hr,
            if_neg (show ¬(r < (r + t) ∧ sourceAlive .interval a x r sigma ∧
              0 < remainingEnergy a r sigma) by tauto)]
        change max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
          a x (fun _ : LabelPerm (r + t) => r + t) r sigma) 0 ≤ _
        rw [hzero]
        simp only [neg_zero, max_self]
        positivity
    · simp only [F, if_neg hmask]
      have hm : 0 ≤ marked3 := by dsimp [marked3, D]; split_ifs <;> positivity
      positivity
  calc
    _ ≤ ∫ _v : Shao.Path r, C0 * marked3 ∂Pr := integral_mono hFi (integrable_const _) hpoint
    _ = C0 * marked3 := by simp

private theorem anib_fixed_suffix_late_marked1_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (bound : ℝ), 0 < bound → (∀ᵐ z : ℝ ∂rho, |z| ≤ bound) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        let h0 : ℝ := 4 * beta ^ 2
        ∀ (r t : ℕ), 0 < r → 0 < t → r + t ≤ 2 * r →
          ∀ (x : ℝ), 16 ≤ x →
            bound ≤ Real.sqrt ((r + t : ℕ) : ℝ) / (100 * x) →
            ∀ {ΩB : Type*} [MeasurableSpace ΩB]
              (Bm : NNReal → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
              IsBrownianReal Bm PB →
              let Q : Measure BridgeNoise := bridgeLaw Bm PB
              ∀ (u : Shao.Path t),
                let T : ℝ := Shao.energy u
                let d : ℝ := Shao.prefixSum u t
                let b : ℝ := if ht : 0 < t then u ⟨0, ht⟩ else 0
                let D : ℝ := if 0 < T then 1 + |d| / Real.sqrt T else 1
                let F : Shao.Path r → ℝ := fun v =>
                  if h0 ≤ T ∧ 3 * x * Real.sqrt T / 2 ≤ |d| then
                    max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
                      (Fin.append v u) x (fun _ : LabelPerm (r + t) => r + t)
                      r (Equiv.refl (Fin (r + t)))) 0
                  else 0
                let marked1 : ℝ :=
                  if 0 < T ∧ h0 ≤ T ∧ (3 * x / 2) * Real.sqrt T ≤ |d| then
                    |b| ^ 3 / Real.sqrt T * D ^ 3
                  else 0
                Integrable F (Measure.pi (fun _ : Fin r => rho)) ∧
                  (∫ v, F v ∂Measure.pi (fun _ : Fin r => rho)) ≤
                    C / ((r + t : ℕ) : ℝ) * marked1 := by
  classical
  obtain ⟨Cs, hCs, hstrip⟩ := anib_large_x_true_energy_closed_strip
  obtain ⟨C0, hC0, hlocal⟩ := anib_local_actual_negative_cubic
  refine ⟨6 * Cs * C0, by positivity, ?_⟩
  intro rho hProb bound hb hsupport hmean hsecond beta h0 r t hr ht hlate x hx hscale
    ΩB hΩB Bm PB hPB hBm Q u T d b D F marked1
  letI : IsProbabilityMeasure rho := hProb
  let Pr : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => rho)
  have hx0 : 0 < x := by linarith only [hx]
  have hraw := anib_bounded_moment_data rho bound hb hsupport hsecond
  have hbeta : 1 ≤ beta := hraw.2.2.2.2.2.1
  have hh : 0 < h0 := by dsimp [h0]; positivity
  have hN : 0 < r + t := by omega
  have hnr : r < r + t := by omega
  have hR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hNR : 0 < ((r + t : ℕ) : ℝ) := by exact_mod_cast hN
  have hdata := anib_iid_rank_negative_disintegration rho Bm PB hBm r t ht x h0 hx0 hh
  have hFm : Measurable F := hdata.1.comp (measurable_id.prodMk measurable_const)
  have hk := anib_actual_interval_kernel_data Bm PB hBm
  have hstate (v : Shao.Path r) :
      Shao.energy (Fin.append v u) = Shao.energy v + T ∧
      Shao.prefixSum (Fin.append v u) (r + t) = Shao.prefixSum v r + d ∧
      (∀ k : ℕ, k ≤ r → Shao.prefixSum (Fin.append v u) k = Shao.prefixSum v k) ∧
      remainingEnergy (Fin.append v u) r (Equiv.refl (Fin (r + t))) = T ∧
      (Fin.append v u) ⟨r, hnr⟩ = b := by
    have hE : Shao.energy (Fin.append v u) = Shao.energy v + T := by
      simp only [Shao.energy, Fin.sum_univ_add, Fin.append_left, Fin.append_right]; rfl
    have hS : Shao.prefixSum (Fin.append v u) (r + t) = Shao.prefixSum v r + d := by
      dsimp only [d]
      simp only [Shao.prefixSum_length, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    have hhead (k : ℕ) (hk : k ≤ r) : Shao.prefixSum (Fin.append v u) k = Shao.prefixSum v k := by
      simp [Shao.prefixSum, Finset.sum_filter, Fin.sum_univ_add,
        show ∀ i : Fin t, ¬r + i.val < k by intro i; omega]
    have hP : Shao.prefixSquares (Fin.append v u) r = Shao.energy v := by
      simp [Shao.prefixSquares, Shao.energy, Finset.sum_filter, Fin.sum_univ_add]
    refine ⟨hE, hS, hhead, ?_, ?_⟩
    · change Shao.energy (Fin.append v u) - Shao.prefixSquares (Fin.append v u) r = T
      rw [hE, hP]; ring
    · have he : (⟨r, hnr⟩ : Fin (r + t)) = Fin.natAdd r (⟨0, ht⟩ : Fin t) := by apply Fin.ext; simp
      rw [he, Fin.append_right]
      simp only [b, dif_pos ht]
  have hFb (v : Shao.Path r) : |F v| ≤ 16 * (1 + ((r + t : ℕ) : ℝ)) := by
    have hh := (source_parts_uniform_bound .interval (eventCompletionKernel .interval Q)
      (actualDerivativeFamily Q .interval) 4 hk.2.1 (Fin.append v u) x hx0
      (fun _ => r + t) r (Equiv.refl _)).1
    dsimp only [F]
    split_ifs
    · rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le ((neg_le_abs _).trans (by convert hh using 1 <;> ring)) (by positivity)
    · simp; positivity
  have hFi : Integrable F Pr := (integrable_const (16 * (1 + ((r + t : ℕ) : ℝ)))).mono'
    hFm.aestronglyMeasurable (ae_of_all _ fun v => by simpa only [Real.norm_eq_abs] using hFb v)
  refine ⟨hFi, ?_⟩
  by_cases hmask : h0 ≤ T ∧ 3 * x * Real.sqrt T / 2 ≤ |d|
  · have hT : 0 < T := hh.trans_le hmask.1
    have hmark : marked1 = |b| ^ 3 / Real.sqrt T * D ^ 3 := by
      apply if_pos
      exact ⟨hT, hmask.1, by nlinarith only [hmask.2]⟩
    by_cases hsmall : b ^ 2 ≤ T / 2
    · let wall : Shao.Path r → ℝ := fun v => x * Real.sqrt (T + Shao.energy v)
      let E : ℝ → Set (Shao.Path r) := fun s => {v |
        Shao.maxWithZero (s • v) ≤ wall v ∧
        wall v - |b| ≤ s * Shao.prefixSum v r ∧ s * Shao.prefixSum v r ≤ wall v}
      let A : ℝ := C0 * (|b| / Real.sqrt T) ^ 3 * D ^ 3
      have hA : 0 ≤ A := by dsimp [A, D]; positivity
      have hwm : Measurable wall := measurable_const.mul ((measurable_const.add Shao.measurable_energy).sqrt)
      have hEm (s : ℝ) : MeasurableSet (E s) := by
        have hsm : Measurable (fun v : Shao.Path r => s • v) :=
          Measurable.of_eval fun i => measurable_const.mul (measurable_pi_apply (X := fun _ : Fin r => ℝ) i)
        exact (measurableSet_le (Shao.measurable_maxWithZero.comp hsm) hwm).inter
          ((measurableSet_le (hwm.sub_const |b|) (measurable_const.mul (Shao.measurable_prefixSum r))).inter
            (measurableSet_le (measurable_const.mul (Shao.measurable_prefixSum r)) hwm))
      have hpoint (v : Shao.Path r) : F v ≤
          (E 1).indicator (fun _ => A) v + (E (-1)).indicator (fun _ => A) v := by
        dsimp only [F]
        rw [if_pos hmask]
        let a : Shao.Path (r + t) := Fin.append v u
        let sigma : LabelPerm (r + t) := Equiv.refl _
        by_cases hact : sourceAlive .interval a x r sigma ∧ 0 < remainingEnergy a r sigma
        · have hw : 0 < actualWall a x := mul_pos hx0 (Real.sqrt_pos.2 hact.1.1)
          have hwall : actualWall a x = wall v := by
            dsimp [actualWall, a, wall]
            rw [(hstate v).1, add_comm]
          have hy : |Shao.prefixSum v r| < wall v := by
            have hh := abs_lt.mpr (hact.1.2.2 r le_rfl)
            change |Shao.prefixSum a r| < actualWall a x at hh
            rw [(hstate v).2.2.1 r le_rfl, hwall] at hh
            exact hh
          have hz : |Shao.prefixSum a (r + t)| < actualWall a x := abs_lt.mpr hact.1.2.1
          have hsurv (s : ℝ) (hs : s = 1 ∨ s = -1) : Shao.maxWithZero (s • v) ≤ wall v := by
            apply (Shao.maxWithZero_le_iff _ _).2
            intro k hk
            have hlive := hact.1.2.2 k hk
            rw [Shao.prefixSum_smul]
            have heq := (hstate v).2.2.1 k hk
            change Interior .interval (actualWall a x) (Shao.prefixSum a k) at hlive
            rw [heq, hwall] at hlive
            rcases hs with rfl | rfl <;> dsimp [Interior] at hlive <;> nlinarith only [hlive.1, hlive.2]
          have hloc := hlocal Bm PB hBm (actualWall a x) (Shao.prefixSum v r) T
            (Shao.prefixSum a (r + t)) b hw (by rwa [hwall]) hz hT
          have hdiff : Shao.prefixSum a (r + t) - Shao.prefixSum v r = d := by
            rw [(hstate v).2.1]; ring
          have hsource : max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
              a x (fun _ : LabelPerm (r + t) => r + t) r sigma) 0 =
              max (-localSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
                (actualWall a x) (Shao.prefixSum v r) T (Shao.prefixSum a (r + t)) b) 0 := by
            have hfull : r < r + t ∧ sourceAlive .interval a x r sigma ∧
                0 < remainingEnergy a r sigma := ⟨hnr, hact⟩
            rw [sourceSeparatedOvershoot, dif_pos hnr, if_pos hfull]
            change max (-localSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
              (actualWall a x) (Shao.prefixSum a r) (remainingEnergy a r sigma)
              (Shao.prefixSum a (r + t)) (a ⟨r, hnr⟩)) 0 = _
            rw [(hstate v).2.2.1 r le_rfl, show remainingEnergy a r sigma = T from (hstate v).2.2.2.1,
              show a ⟨r, hnr⟩ = b from (hstate v).2.2.2.2]
          rw [hsource]
          by_cases hu : wall v ≤ Shao.prefixSum v r + b
          · have hgap : wall v - |b| ≤ Shao.prefixSum v r := by
              have hbabs := le_abs_self b
              linarith only [hu, hbabs]
            have he : v ∈ E 1 := by
              exact ⟨hsurv 1 (Or.inl rfl), by simpa only [one_mul] using hgap,
                by simpa only [one_mul] using (abs_lt.mp hy).2.le⟩
            rw [Set.indicator_of_mem he]
            have hneg := hloc
            rw [hwall, if_pos ⟨hsmall, Or.inl hu⟩, hdiff] at hneg
            have hAv : max (-localSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
                (actualWall a x) (Shao.prefixSum v r) T (Shao.prefixSum a (r + t)) b) 0 ≤ A := by
              simpa only [A, D, if_pos hT, hwall] using hneg
            exact hAv.trans (le_add_of_nonneg_right (Set.indicator_nonneg (fun _ _ => hA) _))
          · by_cases hl : Shao.prefixSum v r + b ≤ -wall v
            · have hgap : wall v - |b| ≤ -Shao.prefixSum v r := by
                have hbabs := neg_le_abs b
                linarith only [hl, hbabs]
              have he : v ∈ E (-1) := by
                refine ⟨hsurv (-1) (Or.inr rfl), ?_, ?_⟩
                · simpa only [neg_one_mul] using hgap
                · simp only [neg_one_mul]; linarith only [(abs_lt.mp hy).1]
              rw [Set.indicator_of_mem he]
              have hneg := hloc
              rw [hwall, if_pos ⟨hsmall, Or.inr hl⟩, hdiff] at hneg
              have hAv : max (-localSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
                  (actualWall a x) (Shao.prefixSum v r) T (Shao.prefixSum a (r + t)) b) 0 ≤ A := by
                simpa only [A, D, if_pos hT, hwall] using hneg
              exact hAv.trans (le_add_of_nonneg_left (Set.indicator_nonneg (fun _ _ => hA) _))
            · have hzero : max (-localSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
                  (actualWall a x) (Shao.prefixSum v r) T (Shao.prefixSum a (r + t)) b) 0 ≤ 0 := by
                apply hloc.trans
                rw [hwall, if_neg (by tauto)]
              exact hzero.trans (add_nonneg (Set.indicator_nonneg (fun _ _ => hA) _)
                (Set.indicator_nonneg (fun _ _ => hA) _))
        · have hzero : sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
              a x (fun _ : LabelPerm (r + t) => r + t) r sigma = 0 := by
            simp only [sourceSeparatedOvershoot, dif_pos hnr,
              if_neg (show ¬(r < r + t ∧ sourceAlive .interval a x r sigma ∧
                0 < remainingEnergy a r sigma) by tauto)]
          rw [hzero]
          simp only [neg_zero, max_self]
          exact add_nonneg (Set.indicator_nonneg (fun _ _ => hA) _) (Set.indicator_nonneg (fun _ _ => hA) _)
      have hEbound (s : ℝ) (hs : s = 1 ∨ s = -1) :
          Pr.real (E s) ≤ Cs * (|b| + beta) ^ 2 / (r : ℝ) :=
        hstrip rho bound hb hsupport hmean hsecond (r + t) hN x
          (by linarith only [hx]) hscale r hr
          (by omega) hlate T |b| s hT.le (abs_nonneg b) hs
      have hIntegral : (∫ v, F v ∂Pr) ≤ A * (2 * Cs * (|b| + beta) ^ 2 / (r : ℝ)) := by
        have hi := integral_mono hFi
          (((integrable_const A).indicator (hEm 1)).add ((integrable_const A).indicator (hEm (-1)))) hpoint
        change (∫ v, F v ∂Pr) ≤ ∫ v,
          (E 1).indicator (fun _ => A) v + (E (-1)).indicator (fun _ => A) v ∂Pr at hi
        rw [integral_add ((integrable_const A).indicator (hEm 1))
          ((integrable_const A).indicator (hEm (-1))),
          integral_indicator_const _ (hEm 1), integral_indicator_const _ (hEm (-1)), smul_eq_mul, smul_eq_mul] at hi
        have hplus := mul_le_mul_of_nonneg_right (hEbound 1 (Or.inl rfl)) hA
        have hminus := mul_le_mul_of_nonneg_right (hEbound (-1) (Or.inr rfl)) hA
        calc
          _ ≤ Cs * (|b| + beta) ^ 2 / (r : ℝ) * A +
              Cs * (|b| + beta) ^ 2 / (r : ℝ) * A := hi.trans (add_le_add hplus hminus)
          _ = _ := by ring
      have hstripGain : (|b| + beta) ^ 2 / (r : ℝ) ≤ 3 * T / ((r + t : ℕ) : ℝ) := by
        have hbT : beta ^ 2 ≤ T / 4 := by dsimp [h0] at hmask; linarith only [hmask.1]
        have hpoly : (|b| + beta) ^ 2 ≤ 3 * T / 2 := by
          nlinarith only [hsmall, hbT, sq_abs b, sq_nonneg (|b| - beta)]
        have hlateR : ((r + t : ℕ) : ℝ) ≤ 2 * (r : ℝ) := by exact_mod_cast hlate
        apply (div_le_div_iff₀ hR hNR).2
        nlinarith only [mul_le_mul_of_nonneg_right hpoly hNR.le,
          mul_le_mul_of_nonneg_left hlateR (show 0 ≤ 3 * T / 2 by positivity)]
      apply hIntegral.trans
      rw [hmark]
      have hmul := mul_le_mul_of_nonneg_left hstripGain (show 0 ≤ A * (2 * Cs) by positivity)
      have hsq : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hT.le
      have hsqrt : Real.sqrt T ≠ 0 := (Real.sqrt_pos.2 hT).ne'
      have hcancel : (|b| / Real.sqrt T) ^ 3 * T = |b| ^ 3 / Real.sqrt T := by
        calc
          _ = |b| ^ 3 / (Real.sqrt T) ^ 3 * (Real.sqrt T) ^ 2 := by rw [div_pow, hsq]
          _ = _ := by field_simp [hsqrt] <;> ring
      calc
        _ = (A * (2 * Cs)) * ((|b| + beta) ^ 2 / (r : ℝ)) := by ring
        _ ≤ (A * (2 * Cs)) * (3 * T / ((r + t : ℕ) : ℝ)) := hmul
        _ = (6 * Cs * C0 / ((r + t : ℕ) : ℝ) * D ^ 3) *
            ((|b| / Real.sqrt T) ^ 3 * T) := by dsimp only [A]; ring
        _ = _ := by rw [hcancel]; ring
    · have hzero : ∀ v, F v = 0 := by
        intro v
        dsimp only [F]
        rw [if_pos hmask]
        unfold sourceSeparatedOvershoot
        rw [dif_pos hnr]
        split_ifs with hact
        · have hbEq : (Fin.append v u) ((Equiv.refl (Fin (r + t))) ⟨r, hnr⟩) = b := by
            change (Fin.append v u) ⟨r, hnr⟩ = b
            exact (hstate v).2.2.2.2
          simp only [(hstate v).2.2.2.1, hbEq,
            localSeparatedOvershoot, if_neg (show ¬(0 < T ∧ b ^ 2 ≤ T / 2) by tauto),
            neg_zero, max_self]
        · simp only [neg_zero, max_self]
      simp only [hzero, integral_zero]
      have hm0 : 0 ≤ marked1 := by dsimp [marked1, D]; split_ifs <;> positivity
      positivity
  · have hzero : F = fun _ => 0 := by funext v; exact if_neg hmask
    rw [hzero, integral_zero]
    have hm0 : 0 ≤ marked1 := by dsimp [marked1, D]; split_ifs <;> positivity
    positivity

private theorem anib_rank_grid_reindex
    (n : ℕ) (hn : 0 < n) (f g : ℕ → ℝ) (hf : ∀ t, 0 ≤ f t) :
    (∑ r ∈ Finset.range n, if 2 * r < n then f (n - r) else 0) ≤
        (∑ t ∈ Finset.Icc ((n + 1) / 2) n, f t) ∧
      (∑ r ∈ Finset.range n, if n ≤ 2 * r then g (n - r) else 0) =
        (∑ t ∈ Finset.Icc 1 (n / 2), g t) := by
  classical
  have hEarly : ((Finset.range n).filter (fun r => 2 * r < n)).image (fun r => n - r) ⊆
      Finset.Icc ((n + 1) / 2) n := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨r, hr, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    simp only [Finset.mem_Icc]
    omega
  have hinj : Set.InjOn (fun r => n - r) (↑(Finset.range n) : Set ℕ) := by
    intro a ha b hb he
    simp only [Finset.mem_coe, Finset.mem_range] at ha hb
    change n - a = n - b at he
    omega
  have hLate : ((Finset.range n).filter (fun r => n ≤ 2 * r)).image (fun r => n - r) =
      Finset.Icc 1 (n / 2) := by
    ext t
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨r, ⟨hr, hn2r⟩, rfl⟩
      omega
    · rintro ⟨ht1, ht2⟩
      exact ⟨n - t, ⟨by omega, by omega⟩, by omega⟩
  constructor
  · rw [← Finset.sum_filter]
    have hi : ∑ r ∈ (Finset.range n).filter (fun r => 2 * r < n), f (n - r) =
        ∑ t ∈ ((Finset.range n).filter (fun r => 2 * r < n)).image (fun r => n - r), f t := by
      rw [Finset.sum_image]
      intro a ha b hb he
      exact hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 he
    rw [hi]
    exact Finset.sum_le_sum_of_subset_of_nonneg hEarly (fun t _ _ => hf t)
  · rw [← Finset.sum_filter, ← hLate, Finset.sum_image]
    intro a ha b hb he
    exact hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 he

private theorem anib_early_gaussian_factor_comparison :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 16 ≤ x →
      Real.sqrt (Shao.standardNormalTail (3 * x / 2)) + Real.exp (-x ^ 2) ≤
        C * Shao.standardNormalTail x := by
  classical
  refine ⟨8, by norm_num, ?_⟩
  intro x hx
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hP0 : 0 ≤ Shao.standardNormalTail x := (Shao.standardNormalTail_basic.2.2.1 x).1.le
  have hpoly : 1 + x ≤ Real.exp (x ^ 2 / 8) := by
    calc
      1 + x ≤ 1 + x ^ 2 / 8 := by nlinarith [mul_nonneg hx0 (show 0 ≤ x - 8 by linarith)]
      _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (x ^ 2 / 8)
  have hrev : (1 / 2 : ℝ) ≤
      (4 / 3 : ℝ) * (1 + x) * Real.exp (x ^ 2 / 2) * Shao.standardNormalTail x := by
    simpa only [Shao.standardNormalTail_basic.2.1, zero_pow (by decide : (2 : ℕ) ≠ 0),
      add_zero, div_one, sub_zero] using Shao.standardNormalTail_ratio_bound x 0 hx0 (by norm_num)
  have hrevB : (1 / 2 : ℝ) ≤
      (4 / 3 : ℝ) * Real.exp (5 * x ^ 2 / 8) * Shao.standardNormalTail x := by
    apply hrev.trans
    calc
      _ ≤ (4 / 3 : ℝ) * Real.exp (x ^ 2 / 8) * Real.exp (x ^ 2 / 2) * Shao.standardNormalTail x := by gcongr
      _ = _ := by rw [mul_assoc (4 / 3 : ℝ), ← Real.exp_add]; congr 2; ring
  have hNeg : Real.exp (-5 * x ^ 2 / 8) ≤ (8 / 3 : ℝ) * Shao.standardNormalTail x := by
    have hh := mul_le_mul_of_nonneg_left hrevB (Real.exp_nonneg (-5 * x ^ 2 / 8))
    have he : Real.exp (-5 * x ^ 2 / 8) * Real.exp (5 * x ^ 2 / 8) = 1 := by
      rw [← Real.exp_add]; convert Real.exp_zero using 1 <;> ring
    have hh' : Real.exp (-5 * x ^ 2 / 8) * (1 / 2 : ℝ) ≤ (4 / 3 : ℝ) * Shao.standardNormalTail x := by
      calc
        _ ≤ Real.exp (-5 * x ^ 2 / 8) *
          ((4 / 3 : ℝ) * Real.exp (5 * x ^ 2 / 8) * Shao.standardNormalTail x) := hh
        _ = (4 / 3 : ℝ) * (Real.exp (-5 * x ^ 2 / 8) * Real.exp (5 * x ^ 2 / 8)) *
          Shao.standardNormalTail x := by ring
        _ = _ := by rw [he]; ring
    linarith only [hh']
  have hratio : (1 + x) / (1 + 3 * x / 2) ≤ (1 : ℝ) := by
    apply (div_le_one (by positivity)).2
    linarith only [hx0]
  have hforward : Shao.standardNormalTail (3 * x / 2) ≤
      (4 / 3 : ℝ) * Real.exp (-5 * x ^ 2 / 8) * Shao.standardNormalTail x := by
    have hh := Shao.standardNormalTail_ratio_bound x (3 * x / 2) hx0 (by positivity)
    have he : (x ^ 2 - (3 * x / 2) ^ 2) / 2 = -5 * x ^ 2 / 8 := by ring
    rw [he] at hh
    apply hh.trans
    calc
      _ ≤ (4 / 3 : ℝ) * 1 * Real.exp (-5 * x ^ 2 / 8) * Shao.standardNormalTail x := by gcongr
      _ = _ := by ring
  have hsquare : Shao.standardNormalTail (3 * x / 2) ≤ (2 * Shao.standardNormalTail x) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hNeg hP0
    nlinarith [sq_nonneg (Shao.standardNormalTail x)]
  have hsqrt : Real.sqrt (Shao.standardNormalTail (3 * x / 2)) ≤ 2 * Shao.standardNormalTail x :=
    (Real.sqrt_le_iff).2 ⟨by positivity, hsquare⟩
  have hsmall : Real.exp (-x ^ 2) ≤ (8 / 3 : ℝ) * Shao.standardNormalTail x :=
    (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x] : -x ^ 2 ≤ -5 * x ^ 2 / 8)).trans hNeg
  nlinarith only [hsqrt, hsmall, hP0]

theorem actual_auxiliary_level_true_energy_closed_strip :
    ∃ C : ℝ, 0 < C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (bound : ℝ), 0 < bound → (∀ᵐ z : ℝ ∂rho, |z| ≤ bound) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), (1 / 2 : ℝ) ≤ x →
          bound ≤ Real.sqrt (n : ℝ) / (100 * x) →
          ∀ (r : ℕ), 0 < r → r ≤ n → n ≤ 2 * r →
            ∀ (q v s : ℝ), 0 ≤ q → 0 ≤ v → (s = 1 ∨ s = -1) →
              let wall : Shao.Path r → ℝ := fun a =>
                x * Real.sqrt (q + Shao.energy a)
              (Measure.pi (fun _ : Fin r => rho)).real
                {a : Shao.Path r |
                  Shao.maxWithZero (s • a) ≤ wall a ∧
                  wall a - v ≤ s * Shao.prefixSum a r ∧
                  s * Shao.prefixSum a r ≤ wall a} ≤
                C * (v + beta) ^ 2 / (r : ℝ) := by
  exact anib_large_x_true_energy_closed_strip

theorem actual_large_x_true_energy_closed_strip :
    ∃ C : ℝ, 0 < C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (bound : ℝ), 0 < bound → (∀ᵐ z : ℝ ∂rho, |z| ≤ bound) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), 16 ≤ x →
          bound ≤ Real.sqrt (n : ℝ) / (100 * x) →
          ∀ (r : ℕ), 0 < r → r ≤ n → n ≤ 2 * r →
            ∀ (q v s : ℝ), 0 ≤ q → 0 ≤ v → (s = 1 ∨ s = -1) →
              let wall : Shao.Path r → ℝ := fun a =>
                x * Real.sqrt (q + Shao.energy a)
              (Measure.pi (fun _ : Fin r => rho)).real
                {a : Shao.Path r |
                  Shao.maxWithZero (s • a) ≤ wall a ∧
                  wall a - v ≤ s * Shao.prefixSum a r ∧
                  s * Shao.prefixSum a r ≤ wall a} ≤
                C * (v + beta) ^ 2 / (r : ℝ) := by
  obtain ⟨C, hC, hstrip⟩ := anib_large_x_true_energy_closed_strip
  refine ⟨C, hC, ?_⟩
  intro rho hProb bound hb hsupport hm hsecond beta n hn x hx hscale
  exact hstrip rho bound hb hsupport hm hsecond n hn x
    (by linarith only [hx]) hscale

theorem actual_bad_interval_negative_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (bound : ℝ), 0 < bound → (∀ᵐ z : ℝ ∂rho, |z| ≤ bound) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), 16 ≤ x →
          bound ≤ Real.sqrt (n : ℝ) / (100 * x) →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          let delta : ℝ := beta / Real.sqrt (n : ℝ)
          delta * (1 + x) ^ 3 ≤ Real.exp (-3 * x ^ 2) →
          ∀ {ΩB : Type*} [MeasurableSpace ΩB]
            (Bm : NNReal → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
            IsBrownianReal Bm PB →
            let Q : Measure BridgeNoise := bridgeLaw Bm PB
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
            ∀ (nu : Shao.Path n → LabelPerm n → ℕ),
              (∀ sigma : LabelPerm n, Measurable (fun a : Shao.Path n => nu a sigma)) →
              (∀ a sigma, nu a sigma ≤ energyCutoff a (4 * beta ^ 2) sigma) →
              let bill : (Shao.Path n × LabelPerm n) → ℝ :=
                actualBadIntervalNegativeBill Q x nu
              Measurable bill ∧ Integrable bill (revealLaw P) ∧
                0 ≤ (∫ p, bill p ∂revealLaw P) ∧
                (∫ p, bill p ∂revealLaw P) ≤ C * delta * Shao.standardNormalTail x := by
  classical
  obtain ⟨CE, hCE, hEarlyFixed⟩ := anib_fixed_suffix_cubic_bound
  obtain ⟨CL, hCL, hLateFixed⟩ := anib_fixed_suffix_late_marked1_bound
  obtain ⟨CG, hCG, hGaussian⟩ := anib_early_gaussian_factor_comparison
  obtain ⟨CR, hCR, hRare⟩ :=
    Shao.Probability.SourceResidualRareSuffix.iid_marked_and_unmarked_rare_real_suffix_budgets 3
  let C : ℝ := (CE * CG + CL) * CR + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro rho hProb bound hb hsupport hmean hsecond n hn x hx hscale beta delta hres
    ΩB hΩB Bm PB hPB hBm Q P nu hnum hnu bill
  letI : IsProbabilityMeasure rho := hProb
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw Bm PB hBm
  letI : IsProbabilityMeasure (revealLaw P) := by unfold revealLaw; infer_instance
  have hx0 : 0 < x := by linarith only [hx]
  have hraw := anib_bounded_moment_data rho bound hb hsupport hsecond
  have hbeta : 1 ≤ beta := hraw.2.2.2.2.2.1
  have hdelta : 0 ≤ delta := by dsimp [delta]; positivity
  let h0 : ℝ := 4 * beta ^ 2
  have hh0 : 0 < h0 := by dsimp [h0]; positivity
  let Ax : ℝ := Real.sqrt (Shao.standardNormalTail (3 * x / 2)) + Real.exp (-x ^ 2)
  let Pt : (t : ℕ) → Measure (Shao.Path t) := fun t => Measure.pi (fun _ : Fin t => rho)
  let Tt : (t : ℕ) → Shao.Path t → ℝ := fun _ => Shao.energy
  let dt : (t : ℕ) → Shao.Path t → ℝ := fun t a => Shao.prefixSum a t
  let M : (t : ℕ) → Shao.Path t → ℝ := fun t a => if ht : 0 < t then |a ⟨0, ht⟩| ^ 3 else 0
  let Dt : (t : ℕ) → Shao.Path t → ℝ := fun t a =>
    if 0 < Tt t a then 1 + |dt t a| / Real.sqrt (Tt t a) else 1
  let marked : ℕ → (t : ℕ) → Shao.Path t → ℝ := fun q t a =>
    if 0 < Tt t a ∧ h0 ≤ Tt t a ∧ (3 * x / 2) * Real.sqrt (Tt t a) ≤ |dt t a| then
      M t a / (Real.sqrt (Tt t a)) ^ q * Dt t a ^ 3 else 0
  have hrare := hRare rho bound hb hsupport hmean hsecond n hn x hx hres
  rcases hrare with ⟨hBetaR, hh0R, hhH, hm4, hmh, hmn, hInt, hPoint, hEarlyGrid,
    hLateGrid, hFutureInt, hFutureBound⟩
  have hmarkedInt (t q : ℕ) (hq : q = 1 ∨ q = 3) : Integrable (marked q t) (Pt t) := by
    simpa only [marked, M, Dt, Tt, dt, Pt, h0] using (hInt t q hq).1
  have hmarked0 (q t : ℕ) (a : Shao.Path t) : 0 ≤ marked q t a := by
    dsimp [marked, M, Dt]
    split_ifs <;> positivity
  let E : ℕ → ℝ := fun t => ∫ a, marked 3 t a ∂Pt t
  let L : ℕ → ℝ := fun t => ∫ a, marked 1 t a ∂Pt t
  have hE0 (t : ℕ) : 0 ≤ E t := integral_nonneg (hmarked0 3 t)
  have hEarlyPay : (∑ t ∈ Finset.Icc ((n + 1) / 2) n, E t) ≤ CR * delta * Ax := by
    simpa only [E, marked, M, Dt, Tt, dt, Pt, h0, Ax] using hEarlyGrid
  have hLatePay : (1 / (n : ℝ)) * (∑ t ∈ Finset.Icc 1 (n / 2), L t) ≤
      CR * delta * Shao.standardNormalTail x := by
    simpa only [L, marked, M, Dt, Tt, dt, Pt, h0] using hLateGrid
  let R : ℕ → Shao.Path n → ℝ := fun r a =>
    if h0 ≤ remainingEnergy a r (Equiv.refl (Fin n)) ∧
        3 * x * Real.sqrt (remainingEnergy a r (Equiv.refl (Fin n))) / 2 ≤
          |remainingSum a r (Equiv.refl (Fin n))| then
      max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
        a x (fun _ : LabelPerm n => n) r (Equiv.refl (Fin n))) 0 else 0
  let G : Shao.Path n → ℝ := fun a => ∑ r ∈ Finset.range n, R r a
  have hreduce := anib_cap_reorder_reduction rho Bm PB hBm n x h0 hx0 hh0 nu hnum hnu
  change Measurable G ∧ Integrable G P ∧ (∫ p, bill p ∂revealLaw P) ≤ ∫ a, G a ∂P at hreduce
  have hRank (r : ℕ) (hr : r < n) :
      Integrable (R r) P ∧
      (∫ a, R r a ∂P) ≤ if 2 * r < n then CE * E (n - r) else CL / (n : ℝ) * L (n - r) := by
    obtain ⟨t, hnt⟩ : ∃ t : ℕ, n = r + t := ⟨n - r, (Nat.add_sub_of_le hr.le).symm⟩
    subst n
    simp only [Nat.add_sub_cancel_left]
    let n : ℕ := r + t
    have ht : 0 < t := by omega
    have hN : r + t = n := rfl
    let F : Shao.Path r × Shao.Path t → ℝ := fun p =>
      if h0 ≤ Shao.energy p.2 ∧
          3 * x * Real.sqrt (Shao.energy p.2) / 2 ≤ |Shao.prefixSum p.2 t| then
        max (-sourceSeparatedOvershoot .interval (actualDerivativeFamily Q .interval)
          (Fin.append p.1 p.2) x (fun _ : LabelPerm (r + t) => r + t)
          r (Equiv.refl (Fin (r + t)))) 0 else 0
    have hd := anib_iid_rank_negative_disintegration rho Bm PB hBm r t ht x h0 hx0 hh0
    have hRi : Integrable (R r) P := by simpa only [R, P, hN] using hd.2.2.1
    have hEq : (∫ a, R r a ∂P) = ∫ u, (∫ v, F (v, u) ∂Pt r) ∂Pt t := by
      simpa only [R, F, Pt, P, hN] using hd.2.2.2
    have hinnerInt : Integrable (fun u : Shao.Path t => ∫ v, F (v, u) ∂Pt r) (Pt t) :=
      hd.2.1.integral_prod_right
    refine ⟨hRi, ?_⟩
    rw [hEq]
    by_cases hearly : 2 * r < n
    · rw [if_pos hearly]
      have hpoint (u : Shao.Path t) : (∫ v, F (v, u) ∂Pt r) ≤ CE * marked 3 t u := by
        have hh := (hEarlyFixed rho Bm PB hBm r t ht x h0 hx0 hh0 u).2
        have hbFirst : (if ht : 0 < t then |u ⟨0, ht⟩| ^ 3 else 0) =
            |(if ht : 0 < t then u ⟨0, ht⟩ else 0)| ^ 3 := by simp only [dif_pos ht]
        simpa only [F, Pt, marked, M, Dt, Tt, dt, hbFirst] using hh
      have hi := integral_mono hinnerInt ((hmarkedInt t 3 (Or.inr rfl)).const_mul CE) hpoint
      rw [integral_const_mul] at hi
      exact hi
    · rw [if_neg hearly]
      have hlate : r + t ≤ 2 * r := by omega
      have hr0 : 0 < r := by omega
      have hpoint (u : Shao.Path t) : (∫ v, F (v, u) ∂Pt r) ≤ CL / (n : ℝ) * marked 1 t u := by
        have hh := (hLateFixed rho bound hb hsupport hmean hsecond r t hr0 ht hlate x hx
          (by simpa only [hN] using hscale) Bm PB hBm u).2
        have hbFirst : (if ht : 0 < t then |u ⟨0, ht⟩| ^ 3 else 0) =
            |(if ht : 0 < t then u ⟨0, ht⟩ else 0)| ^ 3 := by simp only [dif_pos ht]
        simpa only [F, Pt, marked, M, Dt, Tt, dt, h0, hN, pow_one, hbFirst] using hh
      have hi := integral_mono hinnerInt ((hmarkedInt t 1 (Or.inl rfl)).const_mul (CL / (n : ℝ))) hpoint
      rw [integral_const_mul] at hi
      exact hi
  have hL1 := anib_bill_measurable_integrable Bm PB hBm n P x hx0 nu hnum
  refine ⟨hL1.1, hL1.2.1, integral_nonneg hL1.2.2, ?_⟩
  have hGrid := anib_rank_grid_reindex n hn E L hE0
  have hsumBound : (∫ a, G a ∂P) ≤
      CE * (∑ t ∈ Finset.Icc ((n + 1) / 2) n, E t) +
        CL * ((1 / (n : ℝ)) * ∑ t ∈ Finset.Icc 1 (n / 2), L t) := by
    change (∫ a, ∑ r ∈ Finset.range n, R r a ∂P) ≤ _
    rw [integral_finsetSum _ (fun r hr => (hRank r (Finset.mem_range.mp hr)).1)]
    calc
      _ ≤ ∑ r ∈ Finset.range n,
          if 2 * r < n then CE * E (n - r) else CL / (n : ℝ) * L (n - r) :=
        Finset.sum_le_sum (fun r hr => (hRank r (Finset.mem_range.mp hr)).2)
      _ = CE * (∑ r ∈ Finset.range n, if 2 * r < n then E (n - r) else 0) +
          (CL / (n : ℝ)) * (∑ r ∈ Finset.range n, if n ≤ 2 * r then L (n - r) else 0) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r _
        by_cases hh : 2 * r < n
        · simp only [if_pos hh, if_neg (by omega : ¬n ≤ 2 * r), mul_zero, add_zero]
        · simp only [if_neg hh, if_pos (by omega : n ≤ 2 * r), mul_zero, zero_add]
      _ ≤ CE * (∑ t ∈ Finset.Icc ((n + 1) / 2) n, E t) +
          CL * ((1 / (n : ℝ)) * ∑ t ∈ Finset.Icc 1 (n / 2), L t) := by
        rw [hGrid.2]
        have hh := mul_le_mul_of_nonneg_left hGrid.1 hCE.le
        convert add_le_add_right hh ((CL / (n : ℝ)) * ∑ t ∈ Finset.Icc 1 (n / 2), L t) using 1 <;> ring
  have htail : 0 ≤ Shao.standardNormalTail x := (Shao.standardNormalTail_basic.2.2.1 x).1.le
  calc
    _ ≤ ∫ a, G a ∂P := hreduce.2.2
    _ ≤ CE * (∑ t ∈ Finset.Icc ((n + 1) / 2) n, E t) +
        CL * ((1 / (n : ℝ)) * ∑ t ∈ Finset.Icc 1 (n / 2), L t) := hsumBound
    _ ≤ CE * (CR * delta * Ax) + CL * (CR * delta * Shao.standardNormalTail x) :=
      add_le_add (mul_le_mul_of_nonneg_left hEarlyPay hCE.le)
        (mul_le_mul_of_nonneg_left hLatePay hCL.le)
    _ ≤ CE * (CR * delta * (CG * Shao.standardNormalTail x)) + CL * (CR * delta * Shao.standardNormalTail x) := by
      have hg := hGaussian x hx
      gcongr
    _ = ((CE * CG + CL) * CR) * delta * Shao.standardNormalTail x := by ring
    _ ≤ C * delta * Shao.standardNormalTail x := by
      have hh := mul_le_mul_of_nonneg_right (show (CE * CG + CL) * CR ≤ C by dsimp [C]; linarith)
        (mul_nonneg hdelta htail)
      convert hh using 1 <;> ring

end Shao.C2.ActualBadIntervalNegativeBudget
