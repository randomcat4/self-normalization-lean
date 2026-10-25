import Shao.C2.ActualSignedDoubleTelescope
import Shao.Probability.SourceRegularOppositeWall
import Shao.Probability.SourceSuffixMomentBudgets
import Shao.Probability.SourceSuffixScalarInterfaces
import Shao.C2.AuxiliaryEnergyCentered
import Shao.C2.AuxiliaryEnergyLaplace

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
noncomputable section
namespace Shao.C2.ActualPostwallRetainedBudgets
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.ActualSignedDoubleTelescope
open Shao.Probability.SourcePermutationReveal
open Shao.Probability.SourceSeparatedOvershoot

local instance postwallLabelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

def actualPostwallHalfline (s : ℝ) : MonitoredDomain :=
  if s = 1 then .upper else .lower

def actualOppositePrefixHit {n : ℕ} (s : ℝ) (a : Shao.Path n) (x : ℝ)
    (r : ℕ) (sigma : LabelPerm n) : Prop :=
  ∃ k : Fin (r + 1), 0 < k.val ∧
    s * Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) k.val ≤
      -actualWall a x

def actualPostwallRetainedRank {n : ℕ} (Q : Measure BridgeNoise) (s : ℝ)
    (a : Shao.Path n) (x : ℝ) (nu : LabelPerm n → ℕ)
    (r : Fin n) (sigma : LabelPerm n) : ℝ :=
  |sourceRetainedRemainder (actualPostwallHalfline s)
      (eventCompletionKernel (actualPostwallHalfline s) Q)
      (actualDerivativeFamily Q (actualPostwallHalfline s)) a x nu r.val sigma|

def actualEarlyPostwallRetainedBill {n : ℕ} (Q : Measure BridgeNoise) (x s : ℝ)
    (nu : Shao.Path n → LabelPerm n → ℕ)
    (p : Shao.Path n × LabelPerm n) : ℝ :=
  ∑ r : Fin n, if 2 * r.val < n ∧ actualOppositePrefixHit s p.1 x r.val p.2 then
    actualPostwallRetainedRank Q s p.1 x (nu p.1) r p.2 else 0

def actualLateRegularPostwallRetainedBill {n : ℕ} (Q : Measure BridgeNoise) (x s : ℝ)
    (nu : Shao.Path n → LabelPerm n → ℕ)
    (p : Shao.Path n × LabelPerm n) : ℝ :=
  ∑ r : Fin n, if n ≤ 2 * r.val ∧
      |remainingSum p.1 r.val p.2| ≤
        (3 * x / 2) * Real.sqrt (remainingEnergy p.1 r.val p.2) ∧
      actualOppositePrefixHit s p.1 x r.val p.2 then
    actualPostwallRetainedRank Q s p.1 x (nu p.1) r p.2 else 0

private theorem apw_ordinary_complete_suffix_grids :
    ∃ C : ℝ, 0 < C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho],
        Integrable (fun z : ℝ => z ^ 2) rho →
        Integrable (fun z : ℝ => |z| ^ 3) rho →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        ∀ (n : ℕ), 0 < n →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          let delta : ℝ := beta / Real.sqrt (n : ℝ)
          let h0 : ℝ := 4 * beta ^ 2
          let P : (t : ℕ) → Measure (Shao.Path t) :=
            fun t => Measure.pi (fun _ : Fin t => rho)
          let W : ℕ → (t : ℕ) → Shao.Path t → ℝ := fun q t u =>
            if 0 < Shao.energy u ∧ h0 ≤ Shao.energy u then
              |Shao.Probability.SourceIIDGaussianProfileBudget.firstValue u| ^ 3 /
                (Real.sqrt (Shao.energy u)) ^ q *
                  Shao.Probability.SourceMarkedSuffixAveraging.suffixD u ^ 3
            else 0
          (∀ t q : ℕ, (q = 1 ∨ q = 3) →
            Measurable (W q t) ∧ Integrable (W q t) (P t) ∧
              (∀ u, 0 ≤ W q t u)) ∧
          (∑ t ∈ Finset.Icc (n / 2 + 1) n, ∫ u, W 3 t u ∂P t) ≤ C * delta ∧
          (1 / (n : ℝ)) *
            (∑ t ∈ Finset.Icc 1 (n / 2), ∫ u, W 1 t u ∂P t) ≤ C * delta ∧
          (∑ t ∈ Finset.Icc 1 (n / 2), ∫ u, W 3 t u ∂P t) ≤ C
:= by
  classical
  let c : ℝ := (1 - Real.exp (-2)) / 8
  have hc : 0 < c := by
    dsimp [c]
    have he : Real.exp (-2 : ℝ) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
    exact div_pos (sub_pos.2 he) (by norm_num)
  obtain ⟨K1, hK1, hP1⟩ :=
    Shao.Probability.iid_marked_cutoff_inverse_moments 3 1 (Or.inl rfl)
  obtain ⟨K3, hK3, hP3⟩ :=
    Shao.Probability.iid_marked_cutoff_inverse_moments 3 3 (Or.inr rfl)
  let K : ℕ → ℝ := fun q => if q = 1 then K1 else K3
  have hK (q : ℕ) (hq : q = 1 ∨ q = 3) : 0 < K q := by
    rcases hq with rfl | rfl <;> simp [K, hK1, hK3]
  let g : ℝ := Real.exp (2 * c) / c
  have hg : 0 < g := by dsimp [g]; positivity
  let a : ℝ := c / 4
  have ha : 0 < a := by dsimp [a]; positivity
  let G : ℝ := Real.Gamma (3 / 2) / (a * Real.sqrt a)
  have hG : 0 < G := by
    have hgamma : 0 < Real.Gamma (3 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
    dsimp [G]
    positivity
  let C : ℝ := K3 + K3 * G + K1 * (2 + 4 * g) + K3 * g
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro rho hrho h2 h3 hmean hnorm n hn beta delta h0 P W
  letI : IsProbabilityMeasure rho := hrho
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have hroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hN
  have hbeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one rho h2 h3 hnorm
  have hbeta0 : 0 < beta := lt_of_lt_of_le zero_lt_one hbeta
  have hh : 0 < h0 := by dsimp [h0]; positivity
  have hh4 : 4 ≤ h0 := by dsimp [h0]; nlinarith [sq_nonneg (beta - 1)]
  have hsqrth : Real.sqrt h0 = 2 * beta := by
    apply (Real.sqrt_eq_iff_eq_sq hh.le (by positivity)).2
    dsimp [h0]
    ring
  have hsqrthi : Real.sqrt (1 / h0) = 1 / (2 * beta) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one, hsqrth]
  have hcut : 1 / h0 ≤ 1 := (div_le_iff₀ hh).2 (by linarith)
  -- The atom at z^2 = h0 belongs to the retained part.
  let ret : ℝ → ℝ := fun z => if z ^ 2 ≤ h0 then z ^ 2 else 0
  let tail : ℝ → ℝ := fun z => if h0 < z ^ 2 then z ^ 2 else 0
  have hri : Integrable ret rho := by
    apply h2.mono' ((Measurable.ite
      (measurableSet_le (measurable_id.pow_const 2) measurable_const)
      (measurable_id.pow_const 2) measurable_const).aestronglyMeasurable)
    exact ae_of_all _ fun z => by
      dsimp [ret]
      split_ifs <;> simp [Real.norm_eq_abs, sq_nonneg]
  have hti : Integrable tail rho := by
    apply h2.mono' ((Measurable.ite
      (measurableSet_lt measurable_const (measurable_id.pow_const 2))
      (measurable_id.pow_const 2) measurable_const).aestronglyMeasurable)
    exact ae_of_all _ fun z => by
      dsimp [tail]
      split_ifs <;> simp [Real.norm_eq_abs, sq_nonneg]
  have htail (z : ℝ) : (2 * beta) * tail z ≤ |z| ^ 3 := by
    dsimp [tail]
    split_ifs with hz
    · have hzabs : 2 * beta ≤ |z| := by
        have hz2 : 4 * beta ^ 2 < z ^ 2 := hz
        apply (sq_le_sq₀ (show 0 ≤ 2 * beta by positivity) (abs_nonneg z)).1
        nlinarith only [hz2, sq_abs z]
      calc
        (2 * beta) * z ^ 2 ≤ |z| * z ^ 2 :=
          mul_le_mul_of_nonneg_right hzabs (sq_nonneg z)
        _ = |z| ^ 3 := by rw [← sq_abs z]; ring
    · simp only [mul_zero]
      positivity
  have htbound : (2 * beta) * (∫ z, tail z ∂rho) ≤ beta := by
    simpa only [integral_const_mul] using integral_mono (hti.const_mul (2 * beta)) h3 htail
  have hsplit : (∫ z, ret z ∂rho) + (∫ z, tail z ∂rho) = 1 := by
    rw [← integral_add hri hti, ← hnorm]
    apply integral_congr_ae
    exact ae_of_all _ fun z => by
      dsimp [ret, tail]
      split_ifs <;> simp_all <;> linarith
  have hret : (1 / 2 : ℝ) ≤ ∫ z : ℝ, if z ^ 2 ≤ h0 then z ^ 2 else 0 ∂rho := by
    change (1 / 2 : ℝ) ≤ ∫ z, ret z ∂rho
    have ht : (∫ z, tail z ∂rho) ≤ 1 / 2 :=
      (mul_le_mul_left (show 0 < 2 * beta by positivity)).1 (by nlinarith only [htbound])
    linarith only [hsplit, ht]
  let S : Set ℝ := Set.Ioo 0 (1 / h0)
  let a3 : ℝ → ℝ := fun s => ∫ z : ℝ, |z| ^ 3 * Real.exp (-s * z ^ 2) ∂rho
  let J : ℕ → ℕ → ℝ → ℝ := fun q t s =>
    Real.rpow s ((q : ℝ) / 2 - 1) * a3 (s / 2) *
      Real.exp (-c * s * ((t - 1 : ℕ) : ℝ))
  have ha3nn (s : ℝ) : 0 ≤ a3 s := integral_nonneg fun z => by positivity
  have ha3le (s : ℝ) (hs : 0 ≤ s) : a3 s ≤ beta := by
    have hpoint (z : ℝ) : |z| ^ 3 * Real.exp (-s * z ^ 2) ≤ |z| ^ 3 := by
      exact mul_le_of_le_one_right (by positivity)
        (Real.exp_le_one_iff.2 (by nlinarith only [mul_nonneg hs (sq_nonneg z)]))
    have hi : Integrable (fun z : ℝ => |z| ^ 3 * Real.exp (-s * z ^ 2)) rho := by
      apply h3.mono' (by fun_prop)
      exact ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hpoint z
    exact integral_mono hi h3 hpoint
  have hJnn (q t : ℕ) (s : ℝ) (hs : 0 ≤ s) : 0 ≤ J q t s := by
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hs _) (ha3nn _)) (Real.exp_pos _).le
  have hWm (q t : ℕ) : Measurable (W q t) := by
    have hfirst : Measurable (Shao.Probability.SourceIIDGaussianProfileBudget.firstValue : Shao.Path t → ℝ) := by
      unfold Shao.Probability.SourceIIDGaussianProfileBudget.firstValue
      split_ifs with ht
      · exact measurable_pi_apply ⟨0, ht⟩
      · exact measurable_const
    have hT : Measurable (Shao.energy : Shao.Path t → ℝ) := Shao.measurable_energy
    have hd : Measurable (Shao.Probability.SourceMarkedSuffixAveraging.suffixD : Shao.Path t → ℝ) := by
      unfold Shao.Probability.SourceMarkedSuffixAveraging.suffixD
      exact Measurable.ite (measurableSet_lt measurable_const hT)
        (measurable_const.add ((continuous_abs.measurable.comp (Shao.measurable_prefixSum t)).div hT.sqrt))
        measurable_const
    exact Measurable.ite
      ((measurableSet_lt measurable_const hT).inter (measurableSet_le measurable_const hT))
      ((((continuous_abs.measurable.comp hfirst).pow_const 3).div (hT.sqrt.pow_const q)).mul
        (hd.pow_const 3)) measurable_const
  have hWnn (q t : ℕ) (u : Shao.Path t) : 0 ≤ W q t u := by
    dsimp [W]
    split_ifs
    · exact mul_nonneg (div_nonneg (pow_nonneg (abs_nonneg _) _) (by positivity))
        (pow_nonneg (by
          unfold Shao.Probability.SourceMarkedSuffixAveraging.suffixD
          split_ifs <;> positivity) _)
    · exact le_rfl
  -- This is the exact public P1, with p=3 and the full marked coordinate.
  have hblock (q : ℕ) (hq : q = 1 ∨ q = 3) (m : ℕ) :
      Integrable (W q (m + 1)) (P (m + 1)) ∧ IntegrableOn (J q (m + 1)) S ∧
        (∫ u, W q (m + 1) u ∂P (m + 1)) ≤ K q * ∫ s : ℝ in S, J q (m + 1) s := by
    have hz : (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) = 0 := by
      apply Fin.ext
      simp
    have hform : (fun v : Shao.Path (m + 1) =>
        if 0 < Shao.energy v ∧ h0 ≤ Shao.energy v then
          |v 0| ^ 3 / (Real.sqrt (Shao.energy v)) ^ q *
            (1 + |Shao.prefixSum v (m + 1)| / Real.sqrt (Shao.energy v)) ^ 3
        else 0) = W q (m + 1) := by
      funext v
      by_cases hv : 0 < Shao.energy v ∧ h0 ≤ Shao.energy v
      · simp only [W, if_pos hv,
          Shao.Probability.SourceIIDGaussianProfileBudget.firstValue,
          show 0 < m + 1 by omega, dite_true, hz,
          Shao.Probability.SourceMarkedSuffixAveraging.suffixD, if_pos hv.1]
      · simp only [W, if_neg hv]
    rcases hq with rfl | rfl
    · have hp := hP1 rho h2 hmean hnorm m h0 hh
      dsimp only at hp
      rw [if_pos hret] at hp
      simp only [hform] at hp
      simpa only [P, J, S, a3, K, if_pos (show (1 : ℕ) = 1 from rfl),
        c, Nat.add_sub_cancel] using hp
    · have hp := hP3 rho h2 hmean hnorm m h0 hh
      dsimp only at hp
      rw [if_pos hret] at hp
      simp only [hform] at hp
      simpa only [P, J, S, a3, K, if_neg (show ¬ (3 : ℕ) = 1 by omega),
        c, Nat.add_sub_cancel] using hp
  have hWi (q : ℕ) (hq : q = 1 ∨ q = 3) (t : ℕ) : Integrable (W q t) (P t) := by
    cases t with
    | zero =>
      have hz : W q 0 = fun _ => 0 := by
        funext u
        simp [W, Shao.energy]
      rw [hz]
      exact integrable_const 0
    | succ m => exact (hblock q hq m).1
  have hJi (q : ℕ) (hq : q = 1 ∨ q = 3) (t : ℕ) : IntegrableOn (J q t) S := by
    have hp := (hblock q hq (t - 1)).2.1
    simpa only [J, Nat.add_sub_cancel] using hp
  have hpaid (q : ℕ) (hq : q = 1 ∨ q = 3) (t : ℕ) (ht : 0 < t) :
      (∫ u, W q t u ∂P t) ≤ K q * ∫ s : ℝ in S, J q t s := by
    cases t with
    | zero => omega
    | succ m => exact (hblock q hq m).2.2
  have hhalf (b : ℝ) (hb : 0 < b) :
      IntegrableOn (fun s : ℝ => Real.rpow s (-1 / 2 : ℝ)) (Set.Ioo 0 b) ∧
        (∫ s : ℝ in Set.Ioo 0 b, Real.rpow s (-1 / 2 : ℝ)) = 2 * Real.sqrt b := by
    simp only [Real.rpow_eq_pow]
    have hi : IntervalIntegrable (fun s : ℝ => s ^ (-1 / 2 : ℝ)) volume 0 b :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have hio : IntegrableOn (fun s : ℝ => s ^ (-1 / 2 : ℝ)) (Set.Ioc 0 b) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).1 hi
    refine ⟨hio.mono_set Set.Ioo_subset_Ioc_self, ?_⟩
    have he := integral_rpow (a := 0) (b := b) (r := (-1 / 2 : ℝ)) (Or.inl (by norm_num))
    rw [intervalIntegral.integral_of_le hb.le, integral_Ioc_eq_integral_Ioo] at he
    convert he using 1 <;> norm_num [Real.sqrt_eq_rpow] <;> ring
  have hhigh (N : ℝ) (hNp : 0 < N) :
      IntegrableOn (fun s : ℝ => Real.rpow s (-3 / 2 : ℝ)) (Set.Ioi (1 / N)) ∧
        (∫ s : ℝ in Set.Ioi (1 / N), Real.rpow s (-3 / 2 : ℝ)) = 2 * Real.sqrt N := by
    have hp : 0 < 1 / N := one_div_pos.2 hNp
    refine ⟨integrableOn_Ioi_rpow_of_lt (by norm_num) hp, ?_⟩
    have he := integral_Ioi_rpow_of_lt (a := (-3 / 2 : ℝ)) (by norm_num) hp
    convert he using 1
    norm_num
    rw [Real.rpow_neg (inv_nonneg.mpr hNp.le), ← Real.sqrt_eq_rpow, Real.sqrt_inv, inv_inv]
    ring
  have hgeom (N : ℕ) (s : ℝ) (hs : 0 < s) (hs2 : s ≤ 2) :
      (∑ t ∈ Finset.Icc 1 N, Real.exp (-c * s * ((t - 1 : ℕ) : ℝ))) ≤ (N : ℝ) ∧
      (∑ t ∈ Finset.Icc 1 N, Real.exp (-c * s * ((t - 1 : ℕ) : ℝ))) ≤ g / s := by
    let v : ℝ := Real.exp (-c * s)
    have hv0 : 0 ≤ v := (Real.exp_pos _).le
    have hv1 : v < 1 := Real.exp_lt_one_iff.2 (by nlinarith only [mul_pos hc hs])
    have he (t : ℕ) : Real.exp (-c * s * ((t - 1 : ℕ) : ℝ)) = v ^ (t - 1) := by
      dsimp [v]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hsum : (∑ t ∈ Finset.Icc 1 N, v ^ (t - 1)) = ∑ i ∈ Finset.range N, v ^ i := by
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
        simp only [Nat.add_sub_cancel]
    simp_rw [he]
    rw [hsum]
    refine ⟨?_, ?_⟩
    · calc
        _ ≤ ∑ i ∈ Finset.range N, (1 : ℝ) := Finset.sum_le_sum fun i _ => pow_le_one₀ hv0 hv1.le
        _ = _ := by simp
    · have hden : 0 < 1 - v := sub_pos.2 hv1
      have hgeometric : (∑ i ∈ Finset.range N, v ^ i) ≤ 1 / (1 - v) := by
        apply (le_div_iff₀ hden).2
        have heq := geom_sum_mul v N
        nlinarith only [heq, pow_nonneg hv0 N]
      have hcs : 0 < c * s := mul_pos hc hs
      have hgap : c * s * Real.exp (-c * s) ≤ 1 - v := by
        have heq := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (c * s)) (Real.exp_pos (-c * s)).le
        have hcancel : Real.exp (c * s) * Real.exp (-c * s) = 1 := by
          rw [← Real.exp_add, show c * s + -c * s = 0 by ring, Real.exp_zero]
        rw [hcancel] at heq
        dsimp [v]
        nlinarith only [heq]
      have hexp : Real.exp (-(2 * c)) ≤ Real.exp (-c * s) :=
        Real.exp_le_exp.2 (by nlinarith only [hs2, hc])
      have hlower : c * s * Real.exp (-(2 * c)) ≤ 1 - v :=
        (mul_le_mul_of_nonneg_left hexp hcs.le).trans hgap
      calc
        _ ≤ 1 / (1 - v) := hgeometric
        _ ≤ 1 / (c * s * Real.exp (-(2 * c))) :=
          one_div_le_one_div_of_le (by positivity) hlower
        _ = g / s := by
          dsimp [g]
          rw [Real.exp_neg]
          field_simp [hc.ne', hs.ne', Real.exp_ne_zero _]
          <;> ring
  have hpowshift (s : ℝ) (hs : 0 < s) :
      Real.rpow s (1 / 2 : ℝ) = Real.rpow s (-1 / 2 : ℝ) * s := by
    simp only [Real.rpow_eq_pow]
    rw [show (1 / 2 : ℝ) = -1 / 2 + 1 by norm_num, Real.rpow_add hs, Real.rpow_one]
  have hpowdiv (s : ℝ) (hs : 0 < s) :
      Real.rpow s (-1 / 2 : ℝ) / s = Real.rpow s (-3 / 2 : ℝ) := by
    simp only [Real.rpow_eq_pow]
    rw [show (-1 / 2 : ℝ) = -3 / 2 + 1 by norm_num, Real.rpow_add hs, Real.rpow_one]
    field_simp [hs.ne']
  have hhalfS := hhalf (1 / h0) (one_div_pos.2 hh)
  have hsmall : beta * (∫ s : ℝ in S, Real.rpow s (-1 / 2 : ℝ)) = 1 := by
    rw [hhalfS.2, hsqrthi]
    field_simp [hbeta0.ne']
    <;> ring
  have hsingle3 (t : ℕ) : (∫ s : ℝ in S, J 3 t s) ≤ 1 := by
    calc
      _ ≤ ∫ s : ℝ in S, beta * Real.rpow s (-1 / 2 : ℝ) := by
        apply integral_mono_ae (hJi 3 (Or.inr rfl) t) (hhalfS.1.const_mul beta)
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        have hs0 : 0 < s := hs.1
        have hs1 : s ≤ 1 := hs.2.le.trans hcut
        have hexp : Real.exp (-c * s * ((t - 1 : ℕ) : ℝ)) ≤ 1 :=
          Real.exp_le_one_iff.2 (by
            have hp : 0 ≤ c * s * ((t - 1 : ℕ) : ℝ) := by positivity
            nlinarith only [hp])
        have hp : Real.rpow s (1 / 2 : ℝ) ≤ Real.rpow s (-1 / 2 : ℝ) := by
          rw [hpowshift s hs0]
          exact mul_le_of_le_one_right (Real.rpow_nonneg hs0.le _) hs1
        dsimp only [J]
        norm_num only [show (3 : ℝ) / 2 - 1 = 1 / 2 by norm_num]
        calc
          _ ≤ Real.rpow s (1 / 2 : ℝ) * a3 (s / 2) :=
            mul_le_of_le_one_right (mul_nonneg (Real.rpow_nonneg hs0.le _) (ha3nn _)) hexp
          _ ≤ Real.rpow s (-1 / 2 : ℝ) * beta :=
            mul_le_mul hp (ha3le _ (by positivity)) (ha3nn _) (Real.rpow_nonneg hs0.le _)
          _ = _ := by ring
      _ = 1 := by rw [integral_const_mul, hsmall]
  -- A single finite-sum identity retains every mark, including t=1.
  let A : Finset ℕ := Finset.Icc 1 (n / 2)
  let F : ℕ → ℝ → ℝ := fun q s => ∑ t ∈ A, J q t s
  have hFi (q : ℕ) (hq : q = 1 ∨ q = 3) : IntegrableOn (F q) S :=
    integrable_finsetSum A (fun t _ => hJi q hq t)
  have hsumJ (q : ℕ) (hq : q = 1 ∨ q = 3) :
      (∑ t ∈ A, ∫ s : ℝ in S, J q t s) = ∫ s : ℝ in S, F q s :=
    (integral_finsetSum A (fun t _ => hJi q hq t)).symm
  have hfactor (q : ℕ) (s : ℝ) :
      F q s = (Real.rpow s ((q : ℝ) / 2 - 1) * a3 (s / 2)) *
        ∑ t ∈ A, Real.exp (-c * s * ((t - 1 : ℕ) : ℝ)) := by
    dsimp [F, J]
    rw [Finset.mul_sum]
  have hsumPaid (q : ℕ) (hq : q = 1 ∨ q = 3) :
      (∑ t ∈ A, ∫ u, W q t u ∂P t) ≤ K q * ∫ s : ℝ in S, F q s := by
    calc
      _ ≤ ∑ t ∈ A, K q * ∫ s : ℝ in S, J q t s :=
        Finset.sum_le_sum fun t ht => hpaid q hq t (by have := (Finset.mem_Icc.1 ht).1; omega)
      _ = K q * ∑ t ∈ A, ∫ s : ℝ in S, J q t s := (Finset.mul_sum _ _ _).symm
      _ = _ := by rw [hsumJ q hq]
  have hlate3 : (∑ t ∈ A, ∫ u, W 3 t u ∂P t) ≤ K3 * g := by
    have hbound : (∫ s : ℝ in S, F 3 s) ≤ g := by
      calc
        _ ≤ ∫ s : ℝ in S, (g * beta) * Real.rpow s (-1 / 2 : ℝ) := by
          apply integral_mono_ae (hFi 3 (Or.inr rfl)) (hhalfS.1.const_mul (g * beta))
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
          have hs0 : 0 < s := hs.1
          have hs2 : s ≤ 2 := hs.2.le.trans (hcut.trans (by norm_num))
          have he := (hgeom (n / 2) s hs0 hs2).2
          rw [hfactor]
          norm_num only [show (3 : ℝ) / 2 - 1 = 1 / 2 by norm_num]
          calc
            _ ≤ (Real.rpow s (1 / 2 : ℝ) * a3 (s / 2)) * (g / s) :=
              mul_le_mul_of_nonneg_left he (mul_nonneg (Real.rpow_nonneg hs0.le _) (ha3nn _))
            _ ≤ (Real.rpow s (1 / 2 : ℝ) * beta) * (g / s) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (ha3le _ (by positivity)) (Real.rpow_nonneg hs0.le _))
                (by positivity)
            _ = (g * beta) * Real.rpow s (-1 / 2 : ℝ) := by
              rw [hpowshift s hs0]
              field_simp [hs0.ne']
              <;> ring
        _ = g := by
          rw [integral_const_mul]
          calc
            (g * beta) * (∫ s : ℝ in S, Real.rpow s (-1 / 2 : ℝ)) =
                g * (beta * (∫ s : ℝ in S, Real.rpow s (-1 / 2 : ℝ))) := by ring
            _ = g := by rw [hsmall, mul_one]
    have hpay := hsumPaid 3 (Or.inr rfl)
    simp only [K, if_neg (show ¬ (3 : ℕ) = 1 by omega)] at hpay
    exact hpay.trans (mul_le_mul_of_nonneg_left hbound hK3.le)
  have hlate1 : (∑ t ∈ A, ∫ u, W 1 t u ∂P t) ≤
      K1 * ((2 + 4 * g) * beta * Real.sqrt (n : ℝ)) := by
    let B : Set ℝ := Set.Ioo 0 (1 / (n : ℝ))
    let H : Set ℝ := Set.Ioi (1 / (2 * (n : ℝ)))
    let L : ℝ → ℝ := fun s => Real.rpow s (-1 / 2 : ℝ)
    let V : ℝ → ℝ := fun s => Real.rpow s (-3 / 2 : ℝ)
    have hlow := hhalf (1 / (n : ℝ)) (one_div_pos.2 hN)
    have htailint := hhigh (2 * (n : ℝ)) (by positivity)
    have hLi : Integrable (B.indicator L) volume :=
      (integrable_indicator_iff measurableSet_Ioo).2 hlow.1
    have hVi : Integrable (H.indicator V) volume :=
      (integrable_indicator_iff measurableSet_Ioi).2 htailint.1
    let U : ℝ → ℝ := fun s => ((n : ℝ) * beta) * B.indicator L s +
      (g * beta) * H.indicator V s
    have hUi : Integrable U volume := (hLi.const_mul _).add (hVi.const_mul _)
    have hBnn (s : ℝ) : 0 ≤ B.indicator L s := by
      by_cases hs : s ∈ B
      · rw [Set.indicator_of_mem hs]
        exact Real.rpow_nonneg hs.1.le _
      · rw [Set.indicator_of_notMem hs]
    have hHnn (s : ℝ) : 0 ≤ H.indicator V s := by
      by_cases hs : s ∈ H
      · rw [Set.indicator_of_mem hs]
        exact Real.rpow_nonneg ((one_div_pos.2 (by positivity : 0 < 2 * (n : ℝ))).le.trans hs.le) _
      · rw [Set.indicator_of_notMem hs]
    have hUnn (s : ℝ) : 0 ≤ U s :=
      add_nonneg (mul_nonneg (by positivity) (hBnn s)) (mul_nonneg (by positivity) (hHnn s))
    have hpoint (s : ℝ) (hs : s ∈ S) : F 1 s ≤ U s := by
      have hs0 : 0 < s := hs.1
      have hs2 : s ≤ 2 := hs.2.le.trans (hcut.trans (by norm_num))
      have he := hgeom (n / 2) s hs0 hs2
      have hcoef : Real.rpow s (-1 / 2 : ℝ) * a3 (s / 2) ≤
          Real.rpow s (-1 / 2 : ℝ) * beta :=
        mul_le_mul_of_nonneg_left (ha3le _ (by positivity)) (Real.rpow_nonneg hs0.le _)
      rw [hfactor]
      norm_num only [show (1 : ℝ) / 2 - 1 = -1 / 2 by norm_num]
      by_cases hslow : s < 1 / (n : ℝ)
      · have hmem : s ∈ B := ⟨hs0, hslow⟩
        calc
          _ ≤ (Real.rpow s (-1 / 2 : ℝ) * a3 (s / 2)) * ((n / 2 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left he.1 (mul_nonneg (Real.rpow_nonneg hs0.le _) (ha3nn _))
          _ ≤ (Real.rpow s (-1 / 2 : ℝ) * beta) * ((n / 2 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)
          _ ≤ (Real.rpow s (-1 / 2 : ℝ) * beta) * (n : ℝ) :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.div_le_self n 2) (by positivity)
          _ = ((n : ℝ) * beta) * B.indicator L s := by
            rw [Set.indicator_of_mem hmem]
            dsimp [L]
            ring
          _ ≤ U s := le_add_of_nonneg_right (mul_nonneg (by positivity) (hHnn s))
      · have hsn : 1 / (n : ℝ) ≤ s := le_of_not_gt hslow
        have hmem : s ∈ H := by
          have hh' : 1 / (2 * (n : ℝ)) < 1 / (n : ℝ) :=
            one_div_lt_one_div_of_lt hN (by linarith only [hN])
          exact hh'.trans_le hsn
        calc
          _ ≤ (Real.rpow s (-1 / 2 : ℝ) * a3 (s / 2)) * (g / s) :=
            mul_le_mul_of_nonneg_left he.2 (mul_nonneg (Real.rpow_nonneg hs0.le _) (ha3nn _))
          _ ≤ (Real.rpow s (-1 / 2 : ℝ) * beta) * (g / s) :=
            mul_le_mul_of_nonneg_right hcoef (by positivity)
          _ = (g * beta) * V s := by
            dsimp [V]
            rw [← hpowdiv s hs0]
            ring
          _ = (g * beta) * H.indicator V s := by rw [Set.indicator_of_mem hmem]
          _ ≤ U s := le_add_of_nonneg_left (mul_nonneg (by positivity) (hBnn s))
    have htwo : 2 * Real.sqrt (2 * (n : ℝ)) ≤ 4 * Real.sqrt (n : ℝ) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hs2 : Real.sqrt 2 ≤ 2 := by
        nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
      have he := mul_le_mul_of_nonneg_right hs2 (Real.sqrt_nonneg (n : ℝ))
      linarith only [he]
    have hlowval : (n : ℝ) * (2 * Real.sqrt (1 / (n : ℝ))) = 2 * Real.sqrt (n : ℝ) := by
      calc
        _ = 2 * ((n : ℝ) / Real.sqrt (n : ℝ)) := by
          rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
          ring
        _ = 2 * Real.sqrt (n : ℝ) := by
          congr 1
          apply (div_eq_iff hroot.ne').2
          nlinarith only [Real.sq_sqrt hN.le]
    have hbound : (∫ s : ℝ in S, F 1 s) ≤ (2 + 4 * g) * beta * Real.sqrt (n : ℝ) := by
      calc
        _ ≤ ∫ s : ℝ in S, U s := by
          apply integral_mono_ae (hFi 1 (Or.inl rfl)) hUi.integrableOn
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
          exact hpoint s hs
        _ ≤ ∫ s : ℝ, U s := setIntegral_le_integral hUi (ae_of_all _ hUnn)
        _ = ((n : ℝ) * beta) * (2 * Real.sqrt (1 / (n : ℝ))) +
            (g * beta) * (2 * Real.sqrt (2 * (n : ℝ))) := by
          rw [show U = fun s => ((n : ℝ) * beta) * B.indicator L s +
            (g * beta) * H.indicator V s from rfl,
            integral_add (hLi.const_mul _) (hVi.const_mul _), integral_const_mul, integral_const_mul,
            integral_indicator measurableSet_Ioo, integral_indicator measurableSet_Ioi,
            hlow.2, htailint.2]
        _ ≤ ((n : ℝ) * beta) * (2 * Real.sqrt (1 / (n : ℝ))) +
            (g * beta) * (4 * Real.sqrt (n : ℝ)) :=
          add_le_add_left (mul_le_mul_of_nonneg_left htwo (by positivity)) _
        _ = (2 + 4 * g) * beta * Real.sqrt (n : ℝ) := by
          calc
            _ = beta * ((n : ℝ) * (2 * Real.sqrt (1 / (n : ℝ)))) +
                (g * beta) * (4 * Real.sqrt (n : ℝ)) := by ring
            _ = _ := by rw [hlowval]; ring
    have hpay := hsumPaid 1 (Or.inl rfl)
    simp only [K, if_pos (show (1 : ℕ) = 1 from rfl)] at hpay
    exact hpay.trans (mul_le_mul_of_nonneg_left hbound hK1.le)
  have hgamma3 (rate : ℝ) (hr : 0 < rate) :
      IntegrableOn (fun s : ℝ => Real.rpow s (1 / 2 : ℝ) * Real.exp (-rate * s)) (Set.Ioi 0) ∧
        (∫ s : ℝ in Set.Ioi 0, Real.rpow s (1 / 2 : ℝ) * Real.exp (-rate * s)) =
          Real.Gamma (3 / 2) / (rate * Real.sqrt rate) := by
    have he := Shao.Probability.SourceSuffixScalarInterfaces.gamma_kernel (3 / 2) rate (by norm_num) hr
    norm_num only [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num] at he
    refine ⟨he.1, ?_⟩
    rw [he.2, Real.rpow_eq_pow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by positivity), Real.rpow_one, ← Real.sqrt_eq_rpow,
      Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
    ring
  have hearly : (∑ t ∈ Finset.Icc (n / 2 + 1) n, ∫ u, W 3 t u ∂P t) ≤
      (K3 + K3 * G) * delta := by
    by_cases hn1 : n = 1
    · subst n
      have hpay := hpaid 3 (Or.inr rfl) 1 (by omega)
      simp only [K, if_neg (show ¬ (3 : ℕ) = 1 by omega)] at hpay
      have hval : (∫ u, W 3 1 u ∂P 1) ≤ K3 :=
        hpay.trans (by simpa using mul_le_mul_of_nonneg_left (hsingle3 1) hK3.le)
      have hconst : K3 ≤ (K3 + K3 * G) * beta := by
        calc
          K3 ≤ K3 * beta := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hbeta hK3.le
          _ ≤ (K3 + K3 * G) * beta :=
            mul_le_mul_of_nonneg_right (by linarith only [mul_pos hK3 hG]) hbeta0.le
      simpa [delta] using hval.trans hconst
    · let E : Finset ℕ := Finset.Icc (n / 2 + 1) n
      let kernel : ℝ → ℝ := fun s => Real.rpow s (1 / 2 : ℝ) * Real.exp (-(a * (n : ℝ)) * s)
      have hgam := hgamma3 (a * (n : ℝ)) (by positivity)
      have hki : IntegrableOn kernel (Set.Ioi 0) := hgam.1
      have hknn (s : ℝ) (hs : 0 ≤ s) : 0 ≤ kernel s := by dsimp [kernel]; positivity
      have hkval : (∫ s : ℝ in Set.Ioi 0, kernel s) = G / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
        rw [hgam.2, Real.sqrt_mul ha.le]
        dsimp [G]
        field_simp [ha.ne', hN.ne', (Real.sqrt_pos.2 ha).ne', hroot.ne']
        <;> ring
      have hEach (t : ℕ) (ht : t ∈ E) :
          (∫ u, W 3 t u ∂P t) ≤ K3 * (beta * ∫ s : ℝ in Set.Ioi 0, kernel s) := by
        have htpos : 0 < t := by have := (Finset.mem_Icc.1 ht).1; omega
        have hpay := hpaid 3 (Or.inr rfl) t htpos
        simp only [K, if_neg (show ¬ (3 : ℕ) = 1 by omega)] at hpay
        apply hpay.trans
        apply mul_le_mul_of_nonneg_left _ hK3.le
        have hsub : S ⊆ Set.Ioi 0 := fun _ hs => hs.1
        calc
          _ ≤ ∫ s : ℝ in S, beta * kernel s := by
            apply integral_mono_ae (hJi 3 (Or.inr rfl) t) ((hki.mono_set hsub).const_mul beta)
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
            have h4 : n ≤ 4 * (t - 1) := by
              have ht' := (Finset.mem_Icc.1 ht).1
              have hn2 : 2 ≤ n := by omega
              omega
            have hm : (n : ℝ) / 4 ≤ ((t - 1 : ℕ) : ℝ) := by
              have he : (n : ℝ) ≤ 4 * ((t - 1 : ℕ) : ℝ) := by exact_mod_cast h4
              linarith only [he]
            have hexp : Real.exp (-c * s * ((t - 1 : ℕ) : ℝ)) ≤ Real.exp (-(a * (n : ℝ)) * s) := by
              apply Real.exp_le_exp.2
              have he := mul_le_mul_of_nonneg_left hm (mul_nonneg hc.le hs.1.le)
              dsimp [a]
              nlinarith only [he]
            dsimp only [J, kernel]
            norm_num only [show (3 : ℝ) / 2 - 1 = 1 / 2 by norm_num]
            calc
              _ ≤ (Real.rpow s (1 / 2 : ℝ) * beta) *
                  Real.exp (-c * s * ((t - 1 : ℕ) : ℝ)) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (ha3le _ (by positivity)) (Real.rpow_nonneg hs.1.le _))
                  (Real.exp_pos _).le
              _ ≤ (Real.rpow s (1 / 2 : ℝ) * beta) * Real.exp (-(a * (n : ℝ)) * s) :=
                mul_le_mul_of_nonneg_left hexp (by positivity)
              _ = _ := by ring
          _ ≤ ∫ s : ℝ in Set.Ioi 0, beta * kernel s :=
            setIntegral_mono_set (hki.const_mul beta)
              (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs; exact mul_nonneg hbeta0.le (hknn s hs.le))
              (ae_of_all _ fun _ hs => hsub hs)
          _ = _ := integral_const_mul _ _
      have hcard : (E.card : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (show E.card ≤ n by dsimp [E]; rw [Nat.card_Icc]; omega)
      have hInonneg : 0 ≤ ∫ s : ℝ in Set.Ioi 0, kernel s := by
        apply integral_nonneg_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact hknn s hs.le
      calc
        _ ≤ ∑ t ∈ E, K3 * (beta * ∫ s : ℝ in Set.Ioi 0, kernel s) := Finset.sum_le_sum hEach
        _ = (E.card : ℝ) * (K3 * (beta * ∫ s : ℝ in Set.Ioi 0, kernel s)) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (n : ℝ) * (K3 * (beta * ∫ s : ℝ in Set.Ioi 0, kernel s)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = (K3 * G) * delta := by
          rw [hkval]
          dsimp [delta]
          field_simp [hN.ne', hroot.ne']
          <;> ring
        _ ≤ (K3 + K3 * G) * delta :=
          mul_le_mul_of_nonneg_right (by linarith only [hK3]) (by dsimp [delta]; positivity)
  have hpositive1 : 0 < K1 * (2 + 4 * g) := by positivity
  have hpositive3 : 0 < K3 * g := by positivity
  have hpositiveG : 0 < K3 * G := mul_pos hK3 hG
  have hCE : K3 + K3 * G ≤ C := by dsimp [C]; linarith only [hpositive1, hpositive3]
  have hCL1 : K1 * (2 + 4 * g) ≤ C := by dsimp [C]; linarith only [hK3, hpositiveG, hpositive3]
  have hCL3 : K3 * g ≤ C := by dsimp [C]; linarith only [hK3, hpositiveG, hpositive1]
  refine ⟨fun t q hq => ⟨hWm q t, hWi q hq t, hWnn q t⟩, ?_, ?_, ?_⟩
  · exact hearly.trans (mul_le_mul_of_nonneg_right hCE (by dsimp [delta]; positivity))
  · calc
      _ ≤ (1 / (n : ℝ)) * (K1 * ((2 + 4 * g) * beta * Real.sqrt (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hlate1 (by positivity)
      _ = (K1 * (2 + 4 * g)) * delta := by
        have hratio : Real.sqrt (n : ℝ) / (n : ℝ) = 1 / Real.sqrt (n : ℝ) := by
          apply (div_eq_div_iff hN.ne' hroot.ne').2
          nlinarith only [Real.sq_sqrt hN.le]
        calc
          _ = ((K1 * (2 + 4 * g)) * beta) * (Real.sqrt (n : ℝ) / (n : ℝ)) := by ring
          _ = ((K1 * (2 + 4 * g)) * beta) * (1 / Real.sqrt (n : ℝ)) := by rw [hratio]
          _ = _ := by dsimp [delta]; ring
      _ ≤ C * delta := mul_le_mul_of_nonneg_right hCL1 (by dsimp [delta]; positivity)
  · exact hlate3.trans hCL3

private theorem apw_prefix_energy_lower_tail
    (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (h2 : Integrable (fun z : ℝ => z ^ 2) rho)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) rho)
    (hmean : (∫ z : ℝ, z ∂rho) = 0)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂rho) = 1)
    (r : ℕ) (hr : 0 < r) :
    let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
    let P : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => rho)
    (P {v | Shao.energy v < (r : ℝ) / 2}).toReal ≤
      Real.exp (-3 * (r : ℝ) / (512 * beta ^ 2))
    := by
  intro beta P
  have hBeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one
      rho h2 h3 hsecond
  have hb : 0 < beta := lt_of_lt_of_le zero_lt_one hBeta
  have hb0 : beta ≠ 0 := ne_of_gt hb
  let q : ℝ := 1 / (64 * beta ^ 2)
  have hq : 0 < q := by dsimp only [q]; positivity
  have hqBeta : q * beta ^ 2 = 1 / 64 := by
    dsimp only [q]
    field_simp [hb0]
    <;> ring
  have hCoord : (∫ z : ℝ, Real.exp (-q * z ^ 2) ∂rho) ≤
      Real.exp (-(7 / 8 : ℝ) * q) := by
    apply Shao.C2.AuxiliaryEnergyLaplace.auxiliary_energy_laplace_decay
      rho h2 h3 hmean hsecond q hq.le
    change q * beta ^ 2 ≤ 1 / 64
    exact hqBeta.le
  have hInt : Integrable (fun v : Shao.Path r => Real.exp (-q * Shao.energy v)) P := by
    refine (integrable_const (1 : ℝ)).mono'
      (Real.continuous_exp.comp (continuous_const.mul Shao.continuous_energy)).aestronglyMeasurable ?_
    exact ae_of_all _ fun v => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq.le) (Shao.energy_nonneg v))
  have hProd (v : Shao.Path r) :
      Real.exp (-q * Shao.energy v) = ∏ i : Fin r, Real.exp (-q * (v i) ^ 2) := by
    rw [← Real.exp_sum]
    congr 1
    simp only [Shao.energy, Finset.mul_sum]
  have hMoment : (∫ v : Shao.Path r, Real.exp (-q * Shao.energy v) ∂P) ≤
      Real.exp (-(7 / 8 : ℝ) * q * (r : ℝ)) := by
    calc
      (∫ v : Shao.Path r, Real.exp (-q * Shao.energy v) ∂P) =
          ∏ _ : Fin r, ∫ z : ℝ, Real.exp (-q * z ^ 2) ∂rho := by
        simp_rw [hProd]
        exact integral_fintype_prod_eq_prod
          (fun _ : Fin r => fun z : ℝ => Real.exp (-q * z ^ 2))
      _ ≤ ∏ _ : Fin r, Real.exp (-(7 / 8 : ℝ) * q) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact integral_nonneg (fun z => (Real.exp_pos _).le)
        · intro i hi
          exact hCoord
      _ = _ := by
        rw [← Real.exp_sum]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        congr 1
        ring
  let A : Set (Shao.Path r) := {v | Shao.energy v < (r : ℝ) / 2}
  have hA : MeasurableSet A := measurableSet_lt Shao.measurable_energy measurable_const
  have hWeighted : Real.exp (-q * ((r : ℝ) / 2)) * P.real A ≤
      Real.exp (-(7 / 8 : ℝ) * q * (r : ℝ)) := by
    calc
      Real.exp (-q * ((r : ℝ) / 2)) * P.real A =
          ∫ v : Shao.Path r, A.indicator
            (fun _ => Real.exp (-q * ((r : ℝ) / 2))) v ∂P := by
        rw [integral_indicator_const _ hA, smul_eq_mul, mul_comm]
      _ ≤ ∫ v : Shao.Path r, Real.exp (-q * Shao.energy v) ∂P := by
        apply integral_mono ((integrable_const _).indicator hA) hInt
        intro v
        by_cases hv : v ∈ A
        · rw [Set.indicator_of_mem hv]
          apply Real.exp_le_exp.mpr
          change Shao.energy v < (r : ℝ) / 2 at hv
          have hh := mul_nonneg hq.le (sub_nonneg.mpr hv.le)
          nlinarith only [hh]
        · rw [Set.indicator_of_notMem hv]
          exact (Real.exp_pos _).le
      _ ≤ _ := hMoment
  have hTail : P.real A ≤ Real.exp (-(3 / 8 : ℝ) * q * (r : ℝ)) := by
    calc
      P.real A ≤ Real.exp (-(7 / 8 : ℝ) * q * (r : ℝ)) /
          Real.exp (-q * ((r : ℝ) / 2)) := by
        apply (le_div_iff₀ (Real.exp_pos _)).2
        simpa only [mul_comm] using hWeighted
      _ = _ := by
        rw [← Real.exp_sub]
        congr 1
        ring
  change P.real A ≤ _
  calc
    P.real A ≤ Real.exp (-(3 / 8 : ℝ) * q * (r : ℝ)) := hTail
    _ = Real.exp (-3 * (r : ℝ) / (512 * beta ^ 2)) := by
      congr 1
      dsimp only [q]
      field_simp [hb0]
      <;> ring

private theorem apw_deleted_energy_lower_tail
    (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (h2 : Integrable (fun z : ℝ => z ^ 2) rho)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) rho)
    (hmean : (∫ z : ℝ, z ∂rho) = 0)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂rho) = 1)
    (n : ℕ) (hn : 100 ≤ n) (i : Fin n) :
    let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
    (P {v | Shao.energy v - (v i) ^ 2 < (9 / 10 : ℝ) * (n : ℝ)}).toReal ≤
      Real.exp (-(n : ℝ) / (125000 * beta ^ 2))
    := by
  classical
  intro beta P
  have hBeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one
      rho h2 h3 hsecond
  have hb : 0 < beta := lt_of_lt_of_le zero_lt_one hBeta
  have hb0 : beta ≠ 0 := ne_of_gt hb
  let q : ℝ := 1 / (10000 * beta ^ 2)
  have hq : 0 < q := by dsimp only [q]; positivity
  have hqBeta : q * beta ^ 2 = 1 / 10000 := by
    dsimp only [q]
    field_simp [hb0]
    <;> ring
  have hSqrt : Real.sqrt q * beta ≤ 1 / 100 := by
    have hh : (Real.sqrt q * beta) ^ 2 = 1 / 10000 := by
      rw [mul_pow, Real.sq_sqrt hq.le]
      exact hqBeta
    have hnn := mul_nonneg (Real.sqrt_nonneg q) hb.le
    nlinarith only [hh, hnn]
  have hPhi : (∫ z : ℝ, Real.exp (-q * z ^ 2) ∂rho) ≤
      Real.exp (-(99 / 100 : ℝ) * q) := by
    have hLoss := Shao.C2.AuxiliaryEnergyLaplace.auxiliary_energy_laplace_loss
      rho h2 h3 hmean hsecond q hq.le
    change q - q * Real.sqrt q * beta ≤
      1 - (∫ z : ℝ, Real.exp (-q * z ^ 2) ∂rho) at hLoss
    have hPay := mul_le_mul_of_nonneg_left hSqrt hq.le
    have hLinear : (∫ z : ℝ, Real.exp (-q * z ^ 2) ∂rho) ≤
        1 - (99 / 100 : ℝ) * q := by nlinarith only [hLoss, hPay]
    exact hLinear.trans (by
      simpa only [neg_mul, sub_eq_add_neg, add_comm] using
        Real.add_one_le_exp (-(99 / 100 : ℝ) * q))
  let E : Shao.Path n → ℝ := fun v => Shao.energy v - (v i) ^ 2
  have hEm : Measurable E := by dsimp only [E]; fun_prop
  have hEnn (v : Shao.Path n) : 0 ≤ E v := by
    apply sub_nonneg.mpr
    change (v i) ^ 2 ≤ ∑ j : Fin n, (v j) ^ 2
    exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  have hSplit (v : Shao.Path n) :
      (∑ j : Fin n, if j = i then 0 else (v j) ^ 2) = E v := by
    have hh :
        (∑ j : Fin n, (if j = i then 0 else (v j) ^ 2) +
          (if j = i then (v i) ^ 2 else 0)) = ∑ j : Fin n, (v j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hji : j = i
      · subst j; simp
      · simp only [if_neg hji, add_zero]
    rw [Finset.sum_add_distrib] at hh
    have hrec : (∑ j : Fin n, if j = i then 0 else (v j) ^ 2) + (v i) ^ 2 =
        Shao.energy v := by simpa only [Shao.energy, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hh
    dsimp only [E]
    linarith only [hrec]
  let f : Fin n → ℝ → ℝ := fun j z => if j = i then 1 else Real.exp (-q * z ^ 2)
  have hProd (v : Shao.Path n) : Real.exp (-q * E v) = ∏ j : Fin n, f j (v j) := by
    calc
      Real.exp (-q * E v) =
          Real.exp (-q * (∑ j : Fin n, if j = i then 0 else (v j) ^ 2)) := by rw [hSplit]
      _ = ∏ j : Fin n, Real.exp (-q * (if j = i then 0 else (v j) ^ 2)) := by
        rw [← Real.exp_sum]
        congr 1
        simp only [Finset.mul_sum]
      _ = ∏ j : Fin n, f j (v j) := by
        apply Finset.prod_congr rfl
        intro j hj
        by_cases hji : j = i <;> simp [f, hji]
  have hCoord (j : Fin n) : (∫ z : ℝ, f j z ∂rho) ≤
      Real.exp (-(99 / 100 : ℝ) * q * (if j = i then 0 else 1)) := by
    by_cases hji : j = i
    · simp [f, hji]
    · simpa only [f, if_neg hji, mul_one] using hPhi
  have hCount : (∑ j : Fin n, (if j = i then 0 else 1 : ℝ)) = (n : ℝ) - 1 := by
    have he (j : Fin n) : (if j = i then 0 else 1 : ℝ) =
        1 - (if j = i then 1 else 0) := by split_ifs <;> norm_num
    simp_rw [he]
    rw [Finset.sum_sub_distrib]
    simp
  have hInt : Integrable (fun v : Shao.Path n => Real.exp (-q * E v)) P := by
    refine (integrable_const (1 : ℝ)).mono'
      ((measurable_const.mul hEm).exp).aestronglyMeasurable ?_
    exact ae_of_all _ fun v => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq.le) (hEnn v))
  have hMoment : (∫ v : Shao.Path n, Real.exp (-q * E v) ∂P) ≤
      Real.exp (-(99 / 100 : ℝ) * q * ((n : ℝ) - 1)) := by
    calc
      (∫ v : Shao.Path n, Real.exp (-q * E v) ∂P) =
          ∏ j : Fin n, ∫ z : ℝ, f j z ∂rho := by
        simp_rw [hProd]
        exact integral_fintype_prod_eq_prod f
      _ ≤ ∏ j : Fin n,
          Real.exp (-(99 / 100 : ℝ) * q * (if j = i then 0 else 1)) := by
        apply Finset.prod_le_prod₀
        · intro j hj
          apply integral_nonneg
          intro z
          by_cases hji : j = i
          · simp [f, hji]
          · simpa only [f, if_neg hji] using (Real.exp_pos (-q * z ^ 2)).le
        · intro j hj
          exact hCoord j
      _ = _ := by
        rw [← Real.exp_sum]
        congr 1
        rw [← Finset.mul_sum, hCount]
  let A : Set (Shao.Path n) := {v | E v < (9 / 10 : ℝ) * (n : ℝ)}
  have hA : MeasurableSet A := measurableSet_lt hEm measurable_const
  have hWeighted : Real.exp (-q * ((9 / 10 : ℝ) * (n : ℝ))) * P.real A ≤
      Real.exp (-(99 / 100 : ℝ) * q * ((n : ℝ) - 1)) := by
    calc
      Real.exp (-q * ((9 / 10 : ℝ) * (n : ℝ))) * P.real A =
          ∫ v : Shao.Path n, A.indicator
            (fun _ => Real.exp (-q * ((9 / 10 : ℝ) * (n : ℝ)))) v ∂P := by
        rw [integral_indicator_const _ hA, smul_eq_mul, mul_comm]
      _ ≤ ∫ v : Shao.Path n, Real.exp (-q * E v) ∂P := by
        apply integral_mono ((integrable_const _).indicator hA) hInt
        intro v
        by_cases hv : v ∈ A
        · rw [Set.indicator_of_mem hv]
          apply Real.exp_le_exp.mpr
          change E v < (9 / 10 : ℝ) * (n : ℝ) at hv
          have hh := mul_nonneg hq.le (sub_nonneg.mpr hv.le)
          nlinarith only [hh]
        · rw [Set.indicator_of_notMem hv]
          exact (Real.exp_pos _).le
      _ ≤ _ := hMoment
  have hTail : P.real A ≤ Real.exp (-q * ((9 / 100 : ℝ) * (n : ℝ) - 99 / 100)) := by
    calc
      P.real A ≤ Real.exp (-(99 / 100 : ℝ) * q * ((n : ℝ) - 1)) /
          Real.exp (-q * ((9 / 10 : ℝ) * (n : ℝ))) := by
        apply (le_div_iff₀ (Real.exp_pos _)).2
        simpa only [mul_comm] using hWeighted
      _ = _ := by rw [← Real.exp_sub]; congr 1; ring
  change P.real A ≤ _
  calc
    P.real A ≤ Real.exp (-q * ((9 / 100 : ℝ) * (n : ℝ) - 99 / 100)) := hTail
    _ ≤ Real.exp (-q * ((8 / 100 : ℝ) * (n : ℝ))) := by
      apply Real.exp_le_exp.mpr
      have hN : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hh := mul_le_mul_of_nonneg_left
        (show (8 / 100 : ℝ) * (n : ℝ) ≤ (9 / 100 : ℝ) * (n : ℝ) - 99 / 100 by
          linarith only [hN]) hq.le
      nlinarith only [hh]
    _ = Real.exp (-(n : ℝ) / (125000 * beta ^ 2)) := by
      congr 1
      dsimp only [q]
      field_simp [hb0]
      <;> ring

private theorem apw_centered_sum_sixth_moment
    (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (Bcap : ℝ) (hB : 0 < Bcap) (hsupport : ∀ᵐ z : ℝ ∂rho, |z| ≤ Bcap)
    (hmean : (∫ z : ℝ, z ∂rho) = 0)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂rho) = 1)
    (n : ℕ) (hn : 0 < n) (hBn : Bcap ≤ Real.sqrt (n : ℝ))
    (l : ℕ) (hln : l ≤ n) :
    let P : Measure (Shao.Path l) := Measure.pi (fun _ : Fin l => rho)
    Integrable (fun v : Shao.Path l => |Shao.prefixSum v l| ^ 6) P ∧
      (∫ v : Shao.Path l, |Shao.prefixSum v l| ^ 6 ∂P) ≤ 41 * (n : ℝ) ^ 3
    := by
  classical
  let P : Measure (Shao.Path l) := Measure.pi (fun _ : Fin l => rho)
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    infer_instance
  change Integrable (fun v : Shao.Path l => |Shao.prefixSum v l| ^ 6) P ∧
    (∫ v : Shao.Path l, |Shao.prefixSum v l| ^ 6 ∂P) ≤ 41 * (n : ℝ) ^ 3
  let X : Fin l → Shao.Path l → ℝ := fun i v => v i
  let S : Finset (Fin l) → Shao.Path l → ℝ := fun s v => ∑ i ∈ s, v i
  let mu : ℕ → ℝ := fun k => ∫ z : ℝ, z ^ k ∂rho
  have hscalarI (k : ℕ) : Integrable (fun z : ℝ => z ^ k) rho := by
    refine (integrable_const (Bcap ^ k)).mono'
      (measurable_id.pow_const k).aestronglyMeasurable ?_
    filter_upwards [hsupport] with z hz
    simpa only [Real.norm_eq_abs, abs_pow] using
      pow_le_pow_left₀ (abs_nonneg z) hz k
  have hXm (i : Fin l) : Measurable (X i) := measurable_pi_apply i
  have hXI (i : Fin l) (k : ℕ) :
      Integrable (fun v : Shao.Path l => X i v ^ k) P :=
    (measurePreserving_eval (μ := fun _ : Fin l => rho) i).integrable_comp_of_integrable
      (hscalarI k)
  have hXE (i : Fin l) (k : ℕ) :
      (∫ v : Shao.Path l, X i v ^ k ∂P) = mu k := by
    have he := integral_map
      (measurePreserving_eval (μ := fun _ : Fin l => rho) i).aemeasurable
      (measurable_id.pow_const k).aestronglyMeasurable
    rw [(measurePreserving_eval (μ := fun _ : Fin l => rho) i).map_eq] at he
    exact he.symm
  have hsupportP : ∀ᵐ v : Shao.Path l ∂P, ∀ i : Fin l, |v i| ≤ Bcap := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (μ := fun _ : Fin l => rho) i).quasiMeasurePreserving.ae
      hsupport
  have hSm (s : Finset (Fin l)) : Measurable (S s) := by
    dsimp [S]
    fun_prop
  have hSbound (s : Finset (Fin l)) (v : Shao.Path l)
      (hv : ∀ i : Fin l, |v i| ≤ Bcap) :
      |S s v| ≤ (s.card : ℝ) * Bcap := by
    calc
      |S s v| ≤ ∑ i ∈ s, |v i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ s, Bcap := Finset.sum_le_sum (fun i _ => hv i)
      _ = (s.card : ℝ) * Bcap := by simp
  have hSI (s : Finset (Fin l)) (k : ℕ) :
      Integrable (fun v : Shao.Path l => S s v ^ k) P := by
    refine (integrable_const (((s.card : ℝ) * Bcap) ^ k)).mono'
      ((hSm s).pow_const k).aestronglyMeasurable ?_
    filter_upwards [hsupportP] with v hv
    simpa only [Real.norm_eq_abs, abs_pow] using
      pow_le_pow_left₀ (abs_nonneg (S s v)) (hSbound s v hv) k
  have hIndep : iIndepFun X P :=
    iIndepFun_pi (fun _ : Fin l => measurable_id.aemeasurable)
  have hSX (s : Finset (Fin l)) (a : Fin l) (ha : a ∉ s) :
      IndepFun (S s) (X a) P := by
    have hd : Disjoint s {a} := by simpa using ha
    have hi := hIndep.indepFun_finset s {a} hd hXm
    let f : (s → ℝ) → ℝ := fun w => ∑ i : s, w i
    have hf : Measurable f := by
      dsimp [f]
      fun_prop
    have hc := hi.comp hf
      (measurable_pi_apply (⟨a, by simp⟩ : ({a} : Finset (Fin l))))
    have he : (fun v : Shao.Path l => f (fun i : s => X i v)) = S s := by
      funext v
      change (∑ i : s, v i.val) = ∑ i ∈ s, v i
      exact Finset.sum_coe_sort s (fun i => v i)
    change IndepFun (fun v : Shao.Path l => f (fun i : s => X i v)) (X a) P at hc
    rw [he] at hc
    exact hc
  -- All powers and mixed monomials are L1 before any product integral is split.
  have hstep (s : Finset (Fin l)) (a : Fin l) (ha : a ∉ s) (r : ℕ) :
      (∫ v : Shao.Path l, S (insert a s) v ^ r ∂P) =
        ∑ k ∈ Finset.range (r + 1),
          (r.choose k : ℝ) * ((∫ v : Shao.Path l, S s v ^ k ∂P) * mu (r - k)) := by
    have hind := hSX s a ha
    have hmixI (p q : ℕ) :
        Integrable (fun v : Shao.Path l => S s v ^ p * X a v ^ q) P :=
      (hind.comp (measurable_id.pow_const p) (measurable_id.pow_const q)).integrable_mul
        (hSI s p) (hXI a q)
    have hmixE (p q : ℕ) :
        (∫ v : Shao.Path l, S s v ^ p * X a v ^ q ∂P) =
          (∫ v : Shao.Path l, S s v ^ p ∂P) * mu q := by
      have hL1 := hmixI p q
      rw [(hind.comp (measurable_id.pow_const p)
        (measurable_id.pow_const q)).integral_fun_mul_eq_mul_integral
          (hSI s p).aestronglyMeasurable (hXI a q).aestronglyMeasurable, hXE]
    have hinsert (v : Shao.Path l) : S (insert a s) v = S s v + X a v := by
      dsimp [S, X]
      rw [Finset.sum_insert ha]
      exact add_comm _ _
    have hpoly :
        (fun v : Shao.Path l => S (insert a s) v ^ r) =
          (fun v : Shao.Path l => ∑ k ∈ Finset.range (r + 1),
            (r.choose k : ℝ) * (S s v ^ k * X a v ^ (r - k))) := by
      funext v
      rw [hinsert, add_pow]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hpoly, integral_finsetSum (Finset.range (r + 1))
      (fun k _ => (hmixI k (r - k)).const_mul (r.choose k : ℝ))]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul, hmixE]
  have hm0 : mu 0 = 1 := by simp [mu]
  have hm1 : mu 1 = 0 := by simpa [mu] using hmean
  have hm2 : mu 2 = 1 := hsecond
  -- Real falling-factorial expressions also give zero at cardinalities 0, 1, 2.
  have hmom (s : Finset (Fin l)) :
      (∫ v : Shao.Path l, S s v ∂P) = 0 ∧
      (∫ v : Shao.Path l, S s v ^ 2 ∂P) = (s.card : ℝ) ∧
      (∫ v : Shao.Path l, S s v ^ 3 ∂P) = (s.card : ℝ) * mu 3 ∧
      (∫ v : Shao.Path l, S s v ^ 4 ∂P) =
        (s.card : ℝ) * mu 4 + 3 * (s.card : ℝ) * ((s.card : ℝ) - 1) ∧
      (∫ v : Shao.Path l, S s v ^ 6 ∂P) =
        (s.card : ℝ) * mu 6 +
          15 * (s.card : ℝ) * ((s.card : ℝ) - 1) * mu 4 +
          10 * (s.card : ℝ) * ((s.card : ℝ) - 1) * mu 3 ^ 2 +
          15 * (s.card : ℝ) * ((s.card : ℝ) - 1) * ((s.card : ℝ) - 2) := by
    induction s using Finset.induction_on with
    | empty => simp [S]
    | @insert a s ha ih =>
      have e1 := hstep s a ha 1
      have e2 := hstep s a ha 2
      have e3 := hstep s a ha 3
      have e4 := hstep s a ha 4
      have e6 := hstep s a ha 6
      have e0 : (∫ v : Shao.Path l, S s v ^ 0 ∂P) = 1 := by simp
      norm_num [Finset.sum_range_succ, hm0, hm1, hm2, e0, ih.1, ih.2.1,
        ih.2.2.1, ih.2.2.2.1, ih.2.2.2.2] at e1 e2 e3 e4 e6
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa only [pow_one] using e1
      · rw [Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
        nlinarith only [e2]
      · rw [Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
        nlinarith only [e3]
      · rw [Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
        nlinarith only [e4]
      · rw [Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
        nlinarith only [e6]
  have hB2 : Bcap ^ 2 ≤ (n : ℝ) := by
    calc
      Bcap ^ 2 ≤ (Real.sqrt (n : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hB.le hBn 2
      _ = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hB4 : Bcap ^ 4 ≤ (n : ℝ) ^ 2 := by
    have hh := pow_le_pow_left₀ (sq_nonneg Bcap) hB2 2
    nlinarith only [hh]
  have hm4leB : mu 4 ≤ Bcap ^ 2 := by
    calc
      mu 4 ≤ ∫ z : ℝ, Bcap ^ 2 * z ^ 2 ∂rho := by
        apply integral_mono_ae (hscalarI 4) ((hscalarI 2).const_mul (Bcap ^ 2))
        filter_upwards [hsupport] with z hz
        have hz2 : z ^ 2 ≤ Bcap ^ 2 := by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z) hz 2
        calc
          z ^ 4 = z ^ 2 * z ^ 2 := by ring
          _ ≤ Bcap ^ 2 * z ^ 2 :=
            mul_le_mul_of_nonneg_right hz2 (sq_nonneg z)
      _ = Bcap ^ 2 := by rw [integral_const_mul, hsecond]; ring
  have hm6leB : mu 6 ≤ Bcap ^ 4 := by
    calc
      mu 6 ≤ ∫ z : ℝ, Bcap ^ 4 * z ^ 2 ∂rho := by
        apply integral_mono_ae (hscalarI 6) ((hscalarI 2).const_mul (Bcap ^ 4))
        filter_upwards [hsupport] with z hz
        have hz2 : z ^ 2 ≤ Bcap ^ 2 := by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z) hz 2
        have hz4 : z ^ 4 ≤ Bcap ^ 4 := by
          have hh := pow_le_pow_left₀ (sq_nonneg z) hz2 2
          nlinarith only [hh]
        calc
          z ^ 6 = z ^ 4 * z ^ 2 := by ring
          _ ≤ Bcap ^ 4 * z ^ 2 :=
            mul_le_mul_of_nonneg_right hz4 (sq_nonneg z)
      _ = Bcap ^ 4 := by rw [integral_const_mul, hsecond]; ring
  have hm3upper : mu 3 ≤ Bcap := by
    calc
      mu 3 ≤ ∫ z : ℝ, Bcap * z ^ 2 ∂rho := by
        apply integral_mono_ae (hscalarI 3) ((hscalarI 2).const_mul Bcap)
        filter_upwards [hsupport] with z hz
        calc
          z ^ 3 = z * z ^ 2 := by ring
          _ ≤ Bcap * z ^ 2 :=
            mul_le_mul_of_nonneg_right (abs_le.mp hz).2 (sq_nonneg z)
      _ = Bcap := by rw [integral_const_mul, hsecond]; ring
  have hm3lower : -Bcap ≤ mu 3 := by
    calc
      -Bcap = ∫ z : ℝ, -Bcap * z ^ 2 ∂rho := by
        rw [integral_const_mul, hsecond]
        ring
      _ ≤ mu 3 := by
        apply integral_mono_ae ((hscalarI 2).const_mul (-Bcap)) (hscalarI 3)
        filter_upwards [hsupport] with z hz
        calc
          -Bcap * z ^ 2 ≤ z * z ^ 2 :=
            mul_le_mul_of_nonneg_right (abs_le.mp hz).1 (sq_nonneg z)
          _ = z ^ 3 := by ring
  have hm3sq : mu 3 ^ 2 ≤ (n : ℝ) := by
    have habs : |mu 3| ≤ Bcap := abs_le.mpr ⟨hm3lower, hm3upper⟩
    have hh : mu 3 ^ 2 ≤ Bcap ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (mu 3)) habs 2
    exact hh.trans hB2
  have hm4nonneg : 0 ≤ mu 4 := integral_nonneg (fun z => by positivity)
  have hm4le : mu 4 ≤ (n : ℝ) := hm4leB.trans hB2
  have hm6le : mu 6 ≤ (n : ℝ) ^ 2 := hm6leB.trans hB4
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlnR : (l : ℝ) ≤ n := by exact_mod_cast hln
  have hpair0 : 0 ≤ (l : ℝ) * ((l : ℝ) - 1) := by
    by_cases hl : l = 0
    · simp [hl]
    · have h1 : (1 : ℝ) ≤ l := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hl)
      exact mul_nonneg hl0 (sub_nonneg.mpr h1)
  have hpair : (l : ℝ) * ((l : ℝ) - 1) ≤ (n : ℝ) ^ 2 := by
    calc
      (l : ℝ) * ((l : ℝ) - 1) ≤ (l : ℝ) ^ 2 := by nlinarith only [hl0]
      _ ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ hl0 hlnR 2
  have htriple :
      (l : ℝ) * ((l : ℝ) - 1) * ((l : ℝ) - 2) ≤ (n : ℝ) ^ 3 := by
    by_cases hl : 2 ≤ l
    · have h2 : (2 : ℝ) ≤ l := by exact_mod_cast hl
      have hlast : (l : ℝ) - 2 ≤ n := by linarith
      calc
        (l : ℝ) * ((l : ℝ) - 1) * ((l : ℝ) - 2) ≤
            (n : ℝ) ^ 2 * (n : ℝ) :=
          mul_le_mul hpair hlast (sub_nonneg.mpr h2) (sq_nonneg (n : ℝ))
        _ = (n : ℝ) ^ 3 := by ring
    · have hsmall : l = 0 ∨ l = 1 := by omega
      rcases hsmall with rfl | rfl <;> simp only [Nat.cast_zero, Nat.cast_one] <;>
        nlinarith only [pow_nonneg hn0 3]
  have hterm6 : (l : ℝ) * mu 6 ≤ (n : ℝ) ^ 3 := by
    calc
      (l : ℝ) * mu 6 ≤ (l : ℝ) * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hm6le hl0
      _ ≤ (n : ℝ) * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hlnR (sq_nonneg (n : ℝ))
      _ = (n : ℝ) ^ 3 := by ring
  have hterm4 : (l : ℝ) * ((l : ℝ) - 1) * mu 4 ≤ (n : ℝ) ^ 3 := by
    calc
      (l : ℝ) * ((l : ℝ) - 1) * mu 4 ≤ (n : ℝ) ^ 2 * (n : ℝ) :=
        mul_le_mul hpair hm4le hm4nonneg (sq_nonneg (n : ℝ))
      _ = (n : ℝ) ^ 3 := by ring
  have hterm3 : (l : ℝ) * ((l : ℝ) - 1) * mu 3 ^ 2 ≤ (n : ℝ) ^ 3 := by
    calc
      (l : ℝ) * ((l : ℝ) - 1) * mu 3 ^ 2 ≤ (n : ℝ) ^ 2 * (n : ℝ) :=
        mul_le_mul hpair hm3sq (sq_nonneg (mu 3)) (sq_nonneg (n : ℝ))
      _ = (n : ℝ) ^ 3 := by ring
  have habs6 (z : ℝ) : |z| ^ 6 = z ^ 6 := by
    calc
      |z| ^ 6 = (|z| ^ 2) ^ 3 := by ring
      _ = (z ^ 2) ^ 3 := by rw [sq_abs]
      _ = z ^ 6 := by ring
  have htarget :
      (fun v : Shao.Path l => |Shao.prefixSum v l| ^ 6) =
        (fun v : Shao.Path l => S Finset.univ v ^ 6) := by
    funext v
    rw [habs6, Shao.prefixSum_length]
    rfl
  rw [htarget]
  refine ⟨hSI Finset.univ 6, ?_⟩
  have he := (hmom Finset.univ).2.2.2.2
  simp only [Finset.card_univ, Fintype.card_fin] at he
  rw [he]
  nlinarith only [hterm6, hterm4, hterm3, htriple]

private theorem apw_signed_early_fixed_hit :
    ∃ C : ℝ, 0 < C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (Bcap : ℝ), 0 < Bcap → (∀ᵐ z : ℝ ∂rho, |z| ≤ Bcap) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), 16 ≤ x →
          Bcap ≤ Real.sqrt (n : ℝ) / (200 * x) →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          let delta : ℝ := beta / Real.sqrt (n : ℝ)
          delta * (1 + x) ^ 3 ≤ 1 →
          ∀ (r : ℕ), 2 * r ≤ n → ∀ s : ℝ, (s = 1 ∨ s = -1) →
            let P : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => rho)
            (P {v | ∃ k : Fin (r + 1), 0 < k.val ∧
              s * Shao.prefixSum v k.val ≤
                -x * Real.sqrt ((9 / 10 : ℝ) * (n : ℝ))}).toReal ≤
              C * Real.exp (-(89 / 100 : ℝ) * x ^ 2)
 := by
  classical
  refine ⟨1, zero_lt_one, ?_⟩
  intro rho hProb Bcap hBcap hsupport hmean hsecond n hn x hx hscale
    beta delta hres r hr s hs P
  letI : IsProbabilityMeasure rho := hProb
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hx0 : 0 < x := by linarith only [hx]
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hsabs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hssq : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  let theta : ℝ := 2 * x / Real.sqrt (n : ℝ)
  let L : ℝ := x * Real.sqrt ((9 / 10 : ℝ) * (n : ℝ))
  let a : ℝ := 113 / 225
  have htheta : 0 < theta := by dsimp [theta]; positivity
  have hthetaB : theta * Bcap ≤ (1 / 100 : ℝ) := by
    calc
      theta * Bcap ≤ theta * (Real.sqrt (n : ℝ) / (200 * x)) :=
        mul_le_mul_of_nonneg_left hscale htheta.le
      _ = (1 / 100 : ℝ) := by
        dsimp [theta]
        field_simp [ne_of_gt hx0, ne_of_gt hsn]
        <;> ring
  -- The frozen interface includes the residual condition; bounded support already
  -- pays this particular estimate, so beta, delta and hres are not strengthened.
  have hScalar (y : ℝ) (hy : |y| ≤ (1 / 100 : ℝ)) :
      Real.exp y ≤ 1 + y + a * y ^ 2 := by
    have hy1 : |y| ≤ 1 := hy.trans (by norm_num)
    have ht := Real.exp_bound hy1 (n := 3) (by norm_num)
    have ht' :
        |Real.exp y - ∑ m ∈ Finset.range 3, y ^ m / (m.factorial : ℝ)| ≤
          (2 / 9 : ℝ) * |y| ^ 3 := by
      convert ht using 1 <;> norm_num <;> ring
    have hpoly :
        (∑ m ∈ Finset.range 3, y ^ m / (m.factorial : ℝ)) =
          1 + y + y ^ 2 / 2 := by
      norm_num [Finset.sum_range_succ]
      <;> ring
    rw [hpoly] at ht'
    have hcube : |y| ^ 3 ≤ y ^ 2 / 100 := by
      calc
        |y| ^ 3 = |y| * y ^ 2 := by rw [← sq_abs y]; ring
        _ ≤ (1 / 100 : ℝ) * y ^ 2 :=
          mul_le_mul_of_nonneg_right hy (sq_nonneg y)
        _ = _ := by ring
    have hpoint := le_abs_self (Real.exp y - (1 + y + y ^ 2 / 2))
    dsimp only [a]
    nlinarith only [ht', hcube, hpoint]
  have hZi : Integrable (fun z : ℝ => z) rho := by
    exact (integrable_const Bcap).mono' measurable_id.aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hsupport)
  have hZ2i : Integrable (fun z : ℝ => z ^ 2) rho := by
    refine (integrable_const (Bcap ^ 2)).mono' (by fun_prop) ?_
    filter_upwards [hsupport] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z) hz 2
  have hYabs (z : ℝ) : |-theta * s * z| = theta * |z| := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos htheta, hsabs, mul_one]
  have hYi : Integrable (fun z : ℝ => -theta * s * z) rho :=
    hZi.const_mul (-theta * s)
  have hExpI : Integrable (fun z : ℝ => Real.exp (-theta * s * z)) rho := by
    refine (integrable_const (Real.exp (theta * Bcap))).mono' (by fun_prop) ?_
    filter_upwards [hsupport] with z hz
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      -theta * s * z ≤ |-theta * s * z| := le_abs_self _
      _ = theta * |z| := hYabs z
      _ ≤ theta * Bcap := mul_le_mul_of_nonneg_left hz htheta.le
  let c : ℝ := ∫ z : ℝ, Real.exp (-theta * s * z) ∂rho
  have hcLower : 1 ≤ c := by
    have hpoint (z : ℝ) : 1 + (-theta * s * z) ≤ Real.exp (-theta * s * z) := by
      simpa only [add_comm] using Real.add_one_le_exp (-theta * s * z)
    have hInt := integral_mono ((integrable_const 1).add hYi) hExpI hpoint
    rw [integral_add (integrable_const 1) hYi, integral_const_mul, hmean] at hInt
    simpa only [integral_const, probReal_univ, one_smul, mul_zero, add_zero, c] using hInt
  have hc0 : 0 ≤ c := zero_le_one.trans hcLower
  have hYsq (z : ℝ) : (-theta * s * z) ^ 2 = theta ^ 2 * z ^ 2 := by
    rw [mul_pow, mul_pow, neg_sq, hssq, mul_one]
  have hcUpper : c ≤ Real.exp (a * theta ^ 2) := by
    have hpolyI : Integrable
        (fun z : ℝ => 1 + (-theta * s * z) + (a * theta ^ 2) * z ^ 2) rho :=
      ((integrable_const 1).add hYi).add (hZ2i.const_mul (a * theta ^ 2))
    have hpoint : ∀ᵐ z : ℝ ∂rho,
        Real.exp (-theta * s * z) ≤
          1 + (-theta * s * z) + (a * theta ^ 2) * z ^ 2 := by
      filter_upwards [hsupport] with z hz
      have hsmall : |-theta * s * z| ≤ (1 / 100 : ℝ) := by
        rw [hYabs]
        exact (mul_le_mul_of_nonneg_left hz htheta.le).trans hthetaB
      simpa only [hYsq, mul_assoc] using hScalar (-theta * s * z) hsmall
    have hInt := integral_mono_ae hExpI hpolyI hpoint
    rw [integral_add ((integrable_const 1).add hYi)
        (hZ2i.const_mul (a * theta ^ 2)),
      integral_add (integrable_const 1) hYi,
      integral_const_mul, integral_const_mul, hmean, hsecond] at hInt
    simp only [integral_const, probReal_univ, one_smul, mul_zero, add_zero, mul_one] at hInt
    exact hInt.trans (by simpa only [add_comm] using Real.add_one_le_exp (a * theta ^ 2))
  let Pt : (t : ℕ) → Measure (Shao.Path t) :=
    fun t => Measure.pi (fun _ : Fin t => rho)
  have hPt (t : ℕ) : IsProbabilityMeasure (Pt t) := by dsimp [Pt]; infer_instance
  let E : (t : ℕ) → Shao.Path t → ℝ :=
    fun t v => Real.exp (-theta * s * Shao.prefixSum v t)
  have hEm (t : ℕ) : Measurable (E t) := by
    exact ((Shao.measurable_prefixSum t).const_mul (-theta * s)).exp
  have hEnn (t : ℕ) (v : Shao.Path t) : 0 ≤ E t v := (Real.exp_pos _).le
  have hBox (t : ℕ) : ∀ᵐ v : Shao.Path t ∂Pt t, ∀ i : Fin t, |v i| ≤ Bcap := by
    apply ae_all_iff.2
    intro i
    exact (measurePreserving_eval (μ := fun _ : Fin t => rho) i).quasiMeasurePreserving.ae hsupport
  have hSumBound (t : ℕ) (v : Shao.Path t) (hv : ∀ i : Fin t, |v i| ≤ Bcap) :
      |Shao.prefixSum v t| ≤ (t : ℝ) * Bcap := by
    rw [Shao.prefixSum_length]
    calc
      |∑ i : Fin t, v i| ≤ ∑ i : Fin t, |v i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin t, Bcap := Finset.sum_le_sum (fun i _ => hv i)
      _ = (t : ℝ) * Bcap := by simp
  have hEi (t : ℕ) : Integrable (E t) (Pt t) := by
    letI := hPt t
    refine (integrable_const (Real.exp (theta * ((t : ℝ) * Bcap)))).mono'
      (hEm t).aestronglyMeasurable ?_
    filter_upwards [hBox t] with v hv
    rw [Real.norm_eq_abs, abs_of_nonneg (hEnn t v)]
    apply Real.exp_le_exp.mpr
    calc
      -theta * s * Shao.prefixSum v t ≤ |-theta * s * Shao.prefixSum v t| := le_abs_self _
      _ = theta * |Shao.prefixSum v t| := hYabs _
      _ ≤ theta * ((t : ℝ) * Bcap) :=
        mul_le_mul_of_nonneg_left (hSumBound t v hv) htheta.le
  have hEInt (t : ℕ) : (∫ v, E t v ∂Pt t) = c ^ t := by
    have hprod (v : Shao.Path t) : E t v = ∏ i : Fin t, Real.exp (-theta * s * v i) := by
      dsimp only [E]
      rw [Shao.prefixSum_length, Finset.mul_sum, Real.exp_sum]
    simp_rw [hprod]
    simpa only [Pt, c, Fintype.card_fin] using
      (integral_fintype_prod_eq_pow (ι := Fin t) (μ := rho)
        (fun z : ℝ => Real.exp (-theta * s * z)))
  let Hit : Set (Shao.Path r) :=
    {v | ∃ k : Fin (r + 1), 0 < k.val ∧ s * Shao.prefixSum v k.val ≤ -L}
  have hTargetSet :
      {v : Shao.Path r | ∃ k : Fin (r + 1), 0 < k.val ∧
        s * Shao.prefixSum v k.val ≤
          -x * Real.sqrt ((9 / 10 : ℝ) * (n : ℝ))} = Hit := by
    ext v
    simp only [Hit, L, Set.mem_setOf_eq, neg_mul]
  change P.real {v : Shao.Path r | ∃ k : Fin (r + 1), 0 < k.val ∧
    s * Shao.prefixSum v k.val ≤ -x * Real.sqrt ((9 / 10 : ℝ) * (n : ℝ))} ≤
      1 * Real.exp (-(89 / 100 : ℝ) * x ^ 2)
  rw [hTargetSet]
  -- The zero-length path has no positive possible hit index.
  by_cases hr0 : r = 0
  · have hHit0 : Hit = ∅ := by
      ext v
      simp only [Hit, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      intro k hk
      have hk0 : k.val = 0 := by have hkr := k.is_lt; omega
      exact (Nat.lt_irrefl 0) (hk0 ▸ hk.1)
    change P.real Hit ≤ 1 * Real.exp (-(89 / 100 : ℝ) * x ^ 2)
    rw [hHit0]
    simpa only [measureReal_empty, one_mul] using (Real.exp_pos (-(89 / 100 : ℝ) * x ^ 2)).le
  let A : Fin (r + 1) → Set (Shao.Path r) := fun k =>
    {v | 0 < k.val ∧ s * Shao.prefixSum v k.val ≤ -L ∧
      ∀ j : Fin (r + 1), 0 < j.val → j.val < k.val → -L < s * Shao.prefixSum v j.val}
  have hAm (k : Fin (r + 1)) : MeasurableSet (A k) := by
    by_cases hk : 0 < k.val
    · have hle : MeasurableSet {v : Shao.Path r | s * Shao.prefixSum v k.val ≤ -L} :=
        measurableSet_le ((Shao.measurable_prefixSum k.val).const_mul s) measurable_const
      have hpre : MeasurableSet {v : Shao.Path r |
          ∀ j : Fin (r + 1), 0 < j.val → j.val < k.val → -L < s * Shao.prefixSum v j.val} := by
        simp only [Set.setOf_forall]
        exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
          MeasurableSet.iInter fun _ =>
            measurableSet_lt measurable_const ((Shao.measurable_prefixSum j.val).const_mul s)
      simpa only [A, hk, true_and, Set.setOf_and] using hle.inter hpre
    · simpa only [A, hk, false_and, Set.setOf_false] using MeasurableSet.empty
  have hDisj (i j : Fin (r + 1)) (hij : i ≠ j) : Disjoint (A i) (A j) := by
    apply Set.disjoint_left.2
    rintro v hi hj
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact (not_lt_of_ge hi.2.1) (hj.2.2 i hi.1 h)
    · exact (not_lt_of_ge hj.2.1) (hi.2.2 j hj.1 h)
  have hUnion : (⋃ k : Fin (r + 1), A k) = Hit := by
    ext v
    rw [Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, hk.1, hk.2.1⟩
    · rintro ⟨k, hk0, hk⟩
      have hex : ∃ m : ℕ, 0 < m ∧ m ≤ r ∧ s * Shao.prefixSum v m ≤ -L :=
        ⟨k.val, hk0, by omega, hk⟩
      let m := Nat.find hex
      have hm : 0 < m ∧ m ≤ r ∧ s * Shao.prefixSum v m ≤ -L := Nat.find_spec hex
      refine ⟨⟨m, by omega⟩, hm.1, hm.2.2, ?_⟩
      intro j hj0 hjm
      by_contra hnot
      exact Nat.find_min hex hjm ⟨hj0, by omega, le_of_not_gt hnot⟩
  have hMeasure : P.real Hit = ∑ k : Fin (r + 1), P.real (A k) := by
    rw [← hUnion, measureReal_iUnion_fintype hDisj hAm]
  let split : (k : Fin (r + 1)) → Shao.Path r →
      Shao.Path k.val × Shao.Path (r - k.val) := fun k v =>
    (Shao.Probability.Spitzer.head v k.val (by omega),
      Shao.Probability.Spitzer.tail v k.val (by omega))
  have hSplit (k : Fin (r + 1)) :
      MeasurePreserving (split k) P ((Pt k.val).prod (Pt (r - k.val))) := by
    have hkr : k.val ≤ r := by omega
    let e : Fin k.val ⊕ Fin (r - k.val) ≃ Fin r :=
      finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hkr))
    have h1 := (measurePreserving_piCongrLeft (fun _ : Fin r => rho) e).symm
    have h2 := measurePreserving_sumPiEquivProdPi
      (fun _ : Fin k.val ⊕ Fin (r - k.val) => rho)
    convert h2.comp h1 using 1
    ext v i <;> change v _ = v _ <;> congr 1
  have hHead (k : Fin (r + 1)) :
      MeasurePreserving (fun v : Shao.Path r => (split k v).1) P (Pt k.val) := by
    letI := hPt (r - k.val)
    exact (measurePreserving_fst (μ := Pt k.val) (ν := Pt (r - k.val))).comp (hSplit k)
  have hPrefix (k : Fin (r + 1)) (v : Shao.Path r) (j : ℕ) (hj : j ≤ k.val) :
      Shao.prefixSum (split k v).1 j = Shao.prefixSum v j := by
    exact Shao.Probability.Spitzer.head_prefixSum v k.val (by omega) j hj
  have hTotalSplit (k : Fin (r + 1)) (v : Shao.Path r) :
      Shao.prefixSum v r =
        Shao.prefixSum (split k v).1 k.val +
          Shao.prefixSum (split k v).2 (r - k.val) := by
    have htail : (∑ i : Fin (r - k.val), (split k v).2 i) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin r => k.val ≤ i.val), v i := by
      refine Finset.sum_bij
        (fun (i : Fin (r - k.val)) _ => (⟨k.val + i.val, by omega⟩ : Fin r)) ?_ ?_ ?_ ?_
      · intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩
      · intro i hi j hj heq
        apply Fin.ext
        have hv := congrArg Fin.val heq
        dsimp only at hv
        omega
      · intro i hi
        have hki : k.val ≤ i.val := (Finset.mem_filter.mp hi).2
        let j : Fin (r - k.val) := ⟨i.val - k.val, by omega⟩
        refine ⟨j, Finset.mem_univ _, ?_⟩
        apply Fin.ext
        dsimp only [j]
        omega
      · intro i hi
        rfl
    rw [hPrefix k v k.val le_rfl, Shao.prefixSum_length (split k v).2, htail]
    have hsum := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin r => i.val < k.val) (fun i => v i)
    simp only [not_lt] at hsum
    simpa only [Shao.prefixSum_length, Shao.prefixSum] using hsum.symm
  have hEProd (k : Fin (r + 1)) (v : Shao.Path r) :
      E r v = E k.val (split k v).1 * E (r - k.val) (split k v).2 := by
    dsimp only [E]
    rw [hTotalSplit k v, mul_add, Real.exp_add]
  let H : (k : Fin (r + 1)) → Set (Shao.Path k.val) := fun k =>
    {u | 0 < k.val ∧ s * Shao.prefixSum u k.val ≤ -L ∧
      ∀ j : Fin (r + 1), 0 < j.val → j.val < k.val → -L < s * Shao.prefixSum u j.val}
  have hHm (k : Fin (r + 1)) : MeasurableSet (H k) := by
    by_cases hk : 0 < k.val
    · have hle : MeasurableSet {u : Shao.Path k.val | s * Shao.prefixSum u k.val ≤ -L} :=
        measurableSet_le ((Shao.measurable_prefixSum k.val).const_mul s) measurable_const
      have hpre : MeasurableSet {u : Shao.Path k.val |
          ∀ j : Fin (r + 1), 0 < j.val → j.val < k.val → -L < s * Shao.prefixSum u j.val} := by
        simp only [Set.setOf_forall]
        exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
          MeasurableSet.iInter fun _ =>
            measurableSet_lt measurable_const ((Shao.measurable_prefixSum j.val).const_mul s)
      simpa only [H, hk, true_and, Set.setOf_and] using hle.inter hpre
    · simpa only [H, hk, false_and, Set.setOf_false] using MeasurableSet.empty
  have hAH (k : Fin (r + 1)) (v : Shao.Path r) :
      (split k v).1 ∈ H k ↔ v ∈ A k := by
    change (0 < k.val ∧ s * Shao.prefixSum (split k v).1 k.val ≤ -L ∧ _) ↔ _
    rw [hPrefix k v k.val le_rfl]
    constructor
    · rintro ⟨hk, hh, hp⟩
      refine ⟨hk, hh, fun j hj0 hjk => ?_⟩
      have hh' := hp j hj0 hjk
      rwa [hPrefix k v j.val hjk.le] at hh'
    · rintro ⟨hk, hh, hp⟩
      refine ⟨hk, hh, fun j hj0 hjk => ?_⟩
      rw [hPrefix k v j.val hjk.le]
      exact hp j hj0 hjk
  let F : (k : Fin (r + 1)) → Shao.Path k.val → ℝ := fun k => (H k).indicator (E k.val)
  let V : Fin (r + 1) → Shao.Path r → ℝ :=
    fun k v => (A k).indicator (fun w => E k.val (split k w).1) v
  have hFm (k : Fin (r + 1)) : Measurable (F k) := (hEm k.val).indicator (hHm k)
  have hFi (k : Fin (r + 1)) : Integrable (F k) (Pt k.val) :=
    (hEi k.val).indicator (hHm k)
  have hVeq (k : Fin (r + 1)) (v : Shao.Path r) :
      V k v = F k (split k v).1 := by
    by_cases hv : v ∈ A k
    · rw [show V k v = E k.val (split k v).1 from Set.indicator_of_mem hv _]
      exact (Set.indicator_of_mem ((hAH k v).mpr hv) _).symm
    · rw [show V k v = 0 from Set.indicator_of_notMem hv _]
      exact (Set.indicator_of_notMem (fun h => hv ((hAH k v).mp h)) _).symm
  have hVi (k : Fin (r + 1)) : Integrable (V k) P := by
    exact ((hHead k).integrable_comp_of_integrable (hFi k)).congr
      (ae_of_all _ fun v => (hVeq k v).symm)
  have hVnn (k : Fin (r + 1)) (v : Shao.Path r) : 0 ≤ V k v :=
    Set.indicator_nonneg (fun w _ => hEnn k.val (split k w).1) v
  have hVInt (k : Fin (r + 1)) :
      (∫ v, V k v ∂P) = ∫ u, F k u ∂Pt k.val := by
    have he := integral_map (μ := P) (φ := fun v : Shao.Path r => (split k v).1)
      (f := F k) (hHead k).measurable.aemeasurable (hFm k).aestronglyMeasurable
    rw [(hHead k).map_eq] at he
    exact (integral_congr_ae (ae_of_all _ fun v => hVeq k v)).trans he.symm
  have hFactor (k : Fin (r + 1)) :
      (∫ v, (A k).indicator (E r) v ∂P) = (∫ v, V k v ∂P) * c ^ (r - k.val) := by
    -- Both product factors and their pullback are genuinely L1.
    have hJoint : Integrable
        (fun p : Shao.Path k.val × Shao.Path (r - k.val) =>
          F k p.1 * E (r - k.val) p.2) ((Pt k.val).prod (Pt (r - k.val))) :=
      (hFi k).mul_prod (hEi (r - k.val))
    have hPull : Integrable
        (fun v : Shao.Path r => F k (split k v).1 * E (r - k.val) (split k v).2) P :=
      (hSplit k).integrable_comp_of_integrable hJoint
    have hm : Measurable
        (fun p : Shao.Path k.val × Shao.Path (r - k.val) =>
          F k p.1 * E (r - k.val) p.2) :=
      ((hFm k).comp measurable_fst).mul ((hEm (r - k.val)).comp measurable_snd)
    have he := integral_map (μ := P) (φ := split k)
      (f := fun p : Shao.Path k.val × Shao.Path (r - k.val) =>
        F k p.1 * E (r - k.val) p.2)
      (hSplit k).measurable.aemeasurable hm.aestronglyMeasurable
    rw [(hSplit k).map_eq, integral_prod_mul, hEInt, ← hVInt k] at he
    apply Eq.trans _ he.symm
    apply integral_congr_ae
    exact ae_of_all _ fun v => by
      by_cases hv : v ∈ A k
      · rw [Set.indicator_of_mem hv, ← hVeq k v]
        change E r v = (A k).indicator (fun w => E k.val (split k w).1) v * _
        rw [Set.indicator_of_mem hv]
        exact hEProd k v
      · rw [Set.indicator_of_notMem hv, ← hVeq k v]
        change 0 = (A k).indicator (fun w => E k.val (split k w).1) v * _
        rw [Set.indicator_of_notMem hv, zero_mul]
  have hEach (k : Fin (r + 1)) :
      Real.exp (theta * L) * P.real (A k) ≤ ∫ v, (A k).indicator (E r) v ∂P := by
    have hPrefixLower : Real.exp (theta * L) * P.real (A k) ≤ ∫ v, V k v ∂P := by
      calc
        _ = ∫ v, (A k).indicator (fun _ => Real.exp (theta * L)) v ∂P := by
          rw [integral_indicator (hAm k), setIntegral_const]
          simp only [smul_eq_mul, mul_comm]
        _ ≤ _ := by
          apply integral_mono ((integrable_const _).indicator (hAm k)) (hVi k)
          intro v
          by_cases hv : v ∈ A k
          · change (A k).indicator (fun _ => Real.exp (theta * L)) v ≤
              (A k).indicator (fun w => E k.val (split k w).1) v
            rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]
            apply Real.exp_le_exp.mpr
            rw [hPrefix k v k.val le_rfl]
            have hh := mul_le_mul_of_nonneg_left hv.2.1 htheta.le
            nlinarith only [hh]
          · change (A k).indicator (fun _ => Real.exp (theta * L)) v ≤
              (A k).indicator (fun w => E k.val (split k w).1) v
            rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv]
    rw [hFactor k]
    exact hPrefixLower.trans
      (le_mul_of_one_le_right (integral_nonneg (hVnn k)) (one_le_pow₀ hcLower))
  have hSum : (∑ k : Fin (r + 1), ∫ v, (A k).indicator (E r) v ∂P) ≤ c ^ r := by
    have hEr : Integrable (E r) P := by simpa only [P, Pt] using hEi r
    rw [← integral_finsetSum Finset.univ (fun k _ => hEr.indicator (hAm k)), ← hEInt r]
    change (∫ v, ∑ k : Fin (r + 1), (A k).indicator (E r) v ∂P) ≤ ∫ v, E r v ∂P
    apply integral_mono (integrable_finsetSum _ (fun k _ => hEr.indicator (hAm k))) hEr
    intro v
    by_cases hv : ∃ k, v ∈ A k
    · obtain ⟨k, hk⟩ := hv
      rw [Finset.sum_eq_single k]
      · rw [Set.indicator_of_mem hk]
      · intro j hj hjk
        exact Set.indicator_of_notMem (fun h => Set.disjoint_left.1 (hDisj j k hjk) h hk) _
      · simp
    · simp only [not_exists] at hv
      simp only [Set.indicator_of_notMem (hv _), Finset.sum_const_zero]
      exact hEnn r v
  have hMaximal : Real.exp (theta * L) * P.real Hit ≤ c ^ r := by
    rw [hMeasure, Finset.mul_sum]
    exact (Finset.sum_le_sum (fun k _ => hEach k)).trans hSum
  have hcPower : c ^ r ≤ Real.exp ((r : ℝ) * (a * theta ^ 2)) := by
    calc
      c ^ r ≤ (Real.exp (a * theta ^ 2)) ^ r := pow_le_pow_left₀ hc0 hcUpper r
      _ = _ := (Real.exp_nat_mul _ _).symm
  have hRoot : (237 / 250 : ℝ) ≤ Real.sqrt (9 / 10 : ℝ) := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 9 / 10)
    have hnonneg := Real.sqrt_nonneg (9 / 10 : ℝ)
    nlinarith only [hsq, hnonneg]
  have hThetaL : theta * L = 2 * Real.sqrt (9 / 10 : ℝ) * x ^ 2 := by
    dsimp only [theta, L]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9 / 10)]
    field_simp [ne_of_gt hsn]
    <;> ring
  have hThetaSq : theta ^ 2 * (n : ℝ) = 4 * x ^ 2 := by
    dsimp only [theta]
    rw [div_pow, Real.sq_sqrt hnR.le]
    field_simp [ne_of_gt hnR]
    <;> ring
  have hVariance : (r : ℝ) * (a * theta ^ 2) ≤ (226 / 225 : ℝ) * x ^ 2 := by
    have hrR : 2 * (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hr
    have ht := mul_le_mul_of_nonneg_right hrR (sq_nonneg theta)
    dsimp only [a]
    nlinarith only [ht, hThetaSq]
  have hExponent : -(theta * L) + (r : ℝ) * (a * theta ^ 2) ≤
      -(89 / 100 : ℝ) * x ^ 2 := by
    have hBarrier := mul_le_mul_of_nonneg_right hRoot (sq_nonneg x)
    rw [hThetaL]
    nlinarith only [hBarrier, hVariance, sq_nonneg x]
  change P.real Hit ≤ 1 * Real.exp (-(89 / 100 : ℝ) * x ^ 2)
  rw [one_mul]
  calc
    P.real Hit ≤ c ^ r / Real.exp (theta * L) :=
      (le_div_iff₀ (Real.exp_pos _)).2 (by nlinarith only [hMaximal])
    _ ≤ Real.exp ((r : ℝ) * (a * theta ^ 2)) / Real.exp (theta * L) :=
      div_le_div_of_nonneg_right hcPower (Real.exp_pos _).le
    _ = Real.exp (-(theta * L) + (r : ℝ) * (a * theta ^ 2)) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    _ ≤ Real.exp (-(89 / 100 : ℝ) * x ^ 2) := Real.exp_le_exp.mpr hExponent

private theorem apw_actual_postwall_bill_data
    {ΩB : Type*} [MeasurableSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (Bm : ℝ≥0 → ΩB → ℝ) (hBm : IsBrownianReal Bm PB)
    {n : ℕ} (P : Measure (Shao.Path n)) [IsProbabilityMeasure P]
    (x : ℝ) (hx : 0 < x) (nu : Shao.Path n → LabelPerm n → ℕ)
    (hnu : ∀ sigma, Measurable (fun a => nu a sigma)) (s : ℝ) :
    let Q : Measure BridgeNoise := bridgeLaw Bm PB
    let early := actualEarlyPostwallRetainedBill Q x s nu
    let late := actualLateRegularPostwallRetainedBill Q x s nu
    (Measurable early ∧ Integrable early (revealLaw P) ∧
      (∀ p, 0 ≤ early p)) ∧
    (Measurable late ∧ Integrable late (revealLaw P) ∧
      (∀ p, 0 ≤ late p))
    := by
  classical
  intro Q early late
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw Bm PB hBm
  letI : IsProbabilityMeasure (revealLaw P) := by unfold revealLaw; infer_instance
  let J : MonitoredDomain := actualPostwallHalfline s
  have hReflection : Shao.Probability.SourceActualLocalProfileBudget.HalflineReflectionIdentities Q := by
    constructor
    · intro w y T z _hw hT hy hz
      simpa only [Shao.C2.HalfLineReflectionFormula.upperReflection] using
        Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula Bm PB hBm w y T z hT hy hz
    · intro w y T z _hw hT hy hz
      simpa only [Shao.C2.HalfLineReflectionFormula.lowerReflection] using
        Shao.C2.BridgeLowerIdentification.bridge_lower_formula Bm PB hBm w y T z hT hy hz
  have hJ : J = .upper ∨ J = .lower := by
    by_cases hs : s = 1
    · exact Or.inl (by simp only [J, actualPostwallHalfline, if_pos hs])
    · exact Or.inr (by simp only [J, actualPostwallHalfline, if_neg hs])
  have hk : Measurable (actualDerivativeFamily Q J) ∧
      KernelBounds J (eventCompletionKernel J Q) (actualDerivativeFamily Q J) 4 := by
    rcases hJ with hJu | hJl
    · rw [hJu]
      have hd := Shao.Probability.SourceActualLocalProfileBudget.actual_halfline_kernel_data
        Q hReflection .upper (Or.inl rfl)
      exact ⟨by simpa only [actualDerivativeFamily] using hd.1,
        by simpa only [actualDerivativeFamily] using hd.2.1⟩
    · rw [hJl]
      have hd := Shao.Probability.SourceActualLocalProfileBudget.actual_halfline_kernel_data
        Q hReflection .lower (Or.inr rfl)
      exact ⟨by simpa only [actualDerivativeFamily] using hd.1,
        by simpa only [actualDerivativeFamily] using hd.2.1⟩
  have hp := source_parts_measurable_integrable J
    (eventCompletionKernel J Q) (actualDerivativeFamily Q J)
    (eventCompletionKernel_data J Q).1 hk.1 4 hk.2 P x hx nu hnu
  let rank : Fin n → Shao.Path n × LabelPerm n → ℝ := fun r p =>
    actualPostwallRetainedRank Q s p.1 x (nu p.1) r p.2
  have hRankM (r : Fin n) : Measurable (rank r) := by
    have hRaw : Measurable (fun p : Shao.Path n × LabelPerm n =>
        sourceRetainedRemainder J (eventCompletionKernel J Q)
          (actualDerivativeFamily Q J) p.1 x (nu p.1) r.val p.2) := by
      apply measurable_from_prod_countable_left
      intro sigma
      exact (hp.1 sigma r.val).1
    exact continuous_abs.measurable.comp hRaw
  have hRankNN (r : Fin n) (p : Shao.Path n × LabelPerm n) : 0 ≤ rank r p :=
    abs_nonneg _
  have hRankB (r : Fin n) (p : Shao.Path n × LabelPerm n) :
      rank r p ≤ 1 + 24 * (1 + (n : ℝ)) := by
    have hRaw := source_parts_uniform_bound J
      (eventCompletionKernel J Q) (actualDerivativeFamily Q J) 4 hk.2
      p.1 x hx (nu p.1) r.val p.2
    change |sourceRetainedRemainder J (eventCompletionKernel J Q)
      (actualDerivativeFamily Q J) p.1 x (nu p.1) r.val p.2| ≤ _
    convert hRaw.2 using 1 <;> ring
  have hMasked (r : Fin n) (G : Shao.Path n × LabelPerm n → Prop)
      [DecidablePred G] (hG : MeasurableSet {p | G p}) :
      Measurable (fun p => if G p then rank r p else 0) ∧
        Integrable (fun p => if G p then rank r p else 0) (revealLaw P) ∧
          (∀ p, 0 ≤ if G p then rank r p else 0) := by
    have hm : Measurable (fun p => if G p then rank r p else 0) :=
      Measurable.ite hG (hRankM r) measurable_const
    have hnn (p : Shao.Path n × LabelPerm n) :
        0 ≤ if G p then rank r p else 0 := by
      split_ifs
      · exact hRankNN r p
      · exact le_rfl
    have hb (p : Shao.Path n × LabelPerm n) :
        (if G p then rank r p else 0) ≤ 1 + 24 * (1 + (n : ℝ)) := by
      split_ifs
      · exact hRankB r p
      · positivity
    refine ⟨hm, ?_, hnn⟩
    exact (integrable_const (1 + 24 * (1 + (n : ℝ)))).mono'
      hm.aestronglyMeasurable (ae_of_all _ fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hnn p)]
        exact hb p)
  have hReorderM : Measurable (fun p : Shao.Path n × LabelPerm n =>
      Shao.Probability.Spitzer.reorder p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro sigma
    exact Measurable.of_eval fun i =>
      measurable_pi_apply (X := fun _ : Fin n => ℝ) (sigma i)
  have hPrefixM (k : ℕ) : Measurable (fun p : Shao.Path n × LabelPerm n =>
      Shao.prefixSum (Shao.Probability.Spitzer.reorder p.1 p.2) k) :=
    (Shao.measurable_prefixSum k).comp hReorderM
  have hWallM : Measurable (fun p : Shao.Path n × LabelPerm n => actualWall p.1 x) := by
    change Measurable (fun p : Shao.Path n × LabelPerm n =>
      x * Real.sqrt (Shao.energy p.1))
    exact measurable_const.mul (Shao.measurable_energy.comp measurable_fst).sqrt
  have hOpp (r : Fin n) : MeasurableSet
      {p : Shao.Path n × LabelPerm n | actualOppositePrefixHit s p.1 x r.val p.2} := by
    change MeasurableSet {p : Shao.Path n × LabelPerm n |
      ∃ k : Fin (r.val + 1), 0 < k.val ∧
        s * Shao.prefixSum (Shao.Probability.Spitzer.reorder p.1 p.2) k.val ≤
          -actualWall p.1 x}
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro k
    by_cases hk : 0 < k.val
    · simpa only [hk, true_and] using
        measurableSet_le (measurable_const.mul (hPrefixM k.val)) hWallM.neg
    · simp only [hk, false_and, Set.setOf_false]
      exact MeasurableSet.empty
  have hT (r : Fin n) : Measurable (fun p : Shao.Path n × LabelPerm n =>
      remainingEnergy p.1 r.val p.2) := by
    exact (Shao.measurable_energy.comp measurable_fst).sub
      ((Shao.measurable_prefixSquares r.val).comp hReorderM)
  have hd (r : Fin n) : Measurable (fun p : Shao.Path n × LabelPerm n =>
      remainingSum p.1 r.val p.2) := by
    exact ((Shao.measurable_prefixSum n).comp measurable_fst).sub
      ((Shao.measurable_prefixSum r.val).comp hReorderM)
  have hReg (r : Fin n) : MeasurableSet {p : Shao.Path n × LabelPerm n |
      |remainingSum p.1 r.val p.2| ≤
        (3 * x / 2) * Real.sqrt (remainingEnergy p.1 r.val p.2)} :=
    measurableSet_le (continuous_abs.measurable.comp (hd r))
      (measurable_const.mul (hT r).sqrt)
  let ET : Fin n → Shao.Path n × LabelPerm n → ℝ := fun r p =>
    if 2 * r.val < n ∧ actualOppositePrefixHit s p.1 x r.val p.2
    then rank r p else 0
  let LT : Fin n → Shao.Path n × LabelPerm n → ℝ := fun r p =>
    if n ≤ 2 * r.val ∧
        |remainingSum p.1 r.val p.2| ≤
          (3 * x / 2) * Real.sqrt (remainingEnergy p.1 r.val p.2) ∧
        actualOppositePrefixHit s p.1 x r.val p.2
    then rank r p else 0
  have hET (r : Fin n) : Measurable (ET r) ∧ Integrable (ET r) (revealLaw P) ∧
      (∀ p, 0 ≤ ET r p) := by
    apply hMasked r
    by_cases hr : 2 * r.val < n
    · simpa only [hr, true_and] using hOpp r
    · simp only [hr, false_and, Set.setOf_false]
      exact MeasurableSet.empty
  have hLT (r : Fin n) : Measurable (LT r) ∧ Integrable (LT r) (revealLaw P) ∧
      (∀ p, 0 ≤ LT r p) := by
    apply hMasked r
    by_cases hr : n ≤ 2 * r.val
    · simpa only [hr, true_and, Set.setOf_and] using (hReg r).inter (hOpp r)
    · simp only [hr, false_and, Set.setOf_false]
      exact MeasurableSet.empty
  change
    (Measurable (fun p => ∑ r : Fin n, ET r p) ∧
      Integrable (fun p => ∑ r : Fin n, ET r p) (revealLaw P) ∧
      (∀ p, 0 ≤ ∑ r : Fin n, ET r p)) ∧
    (Measurable (fun p => ∑ r : Fin n, LT r p) ∧
      Integrable (fun p => ∑ r : Fin n, LT r p) (revealLaw P) ∧
      (∀ p, 0 ≤ ∑ r : Fin n, LT r p))
  constructor
  · exact ⟨Finset.measurable_sum _ (fun r _ => (hET r).1),
      integrable_finsetSum _ (fun r _ => (hET r).2.1),
      fun p => Finset.sum_nonneg fun r _ => (hET r).2.2 p⟩
  · exact ⟨Finset.measurable_sum _ (fun r _ => (hLT r).1),
      integrable_finsetSum _ (fun r _ => (hLT r).2.1),
      fun p => Finset.sum_nonneg fun r _ => (hLT r).2.2 p⟩

private theorem apw_actual_postwall_physical_carrier
    {ΩB : Type*} [MeasurableSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (Bm : ℝ≥0 → ΩB → ℝ) (hBm : IsBrownianReal Bm PB)
    {n : ℕ} (a : Shao.Path n) (H x : ℝ) (hH : 0 < H) (hx : 0 < x)
    (nu : LabelPerm n → ℕ) (sigma : LabelPerm n)
    (hcap : nu sigma ≤ energyCutoff a H sigma) (r : Fin n)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    let Q : Measure BridgeNoise := bridgeLaw Bm PB
    0 ≤ actualPostwallRetainedRank Q s a x nu r sigma ∧
      actualPostwallRetainedRank Q s a x nu r sigma ≤
        8000100 * Shao.Probability.SourceIIDGaussianProfileBudget.rankGaussianWeight
          H x {s} false (Shao.Probability.Spitzer.reorder a sigma) r
    := by
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
  refine ⟨abs_nonneg _, ?_⟩
  rcases hs with rfl | rfl
  · have h := Shao.Probability.SourceActualLocalProfileBudget.actual_halfline_retained_rank_domination
      Q hReflection .upper (Or.inl rfl) a H x hH hx nu sigma hcap r
    simpa only [actualPostwallRetainedRank, actualPostwallHalfline,
      if_pos (rfl : (1 : ℝ) = 1), actualDerivativeFamily,
      Shao.Probability.SourceActualLocalProfileBudget.wallSigns] using h
  · have h := Shao.Probability.SourceActualLocalProfileBudget.actual_halfline_retained_rank_domination
      Q hReflection .lower (Or.inr rfl) a H x hH hx nu sigma hcap r
    simpa only [actualPostwallRetainedRank, actualPostwallHalfline,
      if_neg (by norm_num : ¬(-1 : ℝ) = 1), actualDerivativeFamily,
      Shao.Probability.SourceActualLocalProfileBudget.wallSigns] using h

theorem iid_actual_early_postwall_retained_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ΩB : Type*} [MeasurableSpace ΩB]
        (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (Bm : ℝ≥0 → ΩB → ℝ), IsBrownianReal Bm PB →
        let Q : Measure BridgeNoise := bridgeLaw Bm PB
        ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
          (Bcap : ℝ), 0 < Bcap → (∀ᵐ z : ℝ ∂rho, |z| ≤ Bcap) →
          (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
          ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), 16 ≤ x →
            Bcap ≤ Real.sqrt (n : ℝ) / (200 * x) →
            let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
            let delta : ℝ := beta / Real.sqrt (n : ℝ)
            delta * (1 + x) ^ 3 ≤ Real.exp (-3 * x ^ 2) →
            let h0 : ℝ := 4 * beta ^ 2
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
            ∀ (nu : Shao.Path n → LabelPerm n → ℕ),
              (∀ sigma, Measurable (fun a => nu a sigma)) →
              (∀ a sigma, nu a sigma ≤ energyCutoff a h0 sigma) →
              ∀ s : ℝ, (s = 1 ∨ s = -1) →
                let bill := actualEarlyPostwallRetainedBill Q x s nu
                Measurable bill ∧ Integrable bill (revealLaw P) ∧
                  (∀ p, 0 ≤ bill p) ∧
                  (∫ p, bill p ∂revealLaw P) ≤
                    C * delta * Real.exp (-(89 / 100 : ℝ) * x ^ 2)
:= by
  classical
  obtain ⟨CG, hCG, hGrid⟩ := apw_ordinary_complete_suffix_grids
  obtain ⟨CH, hCH, hHit⟩ := apw_signed_early_fixed_hit
  let a0 : ℝ := 1 / 250000
  let CL : ℝ := 2 / a0 ^ 2 + 24 * (1 + Real.sqrt 41) / a0 ^ 4
  let C : ℝ := 1 + 8000100 * (CH * CG + CL)
  have ha0 : 0 < a0 := by norm_num [a0]
  have hCL : 0 < CL := by dsimp [CL]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro ΩB mΩB PB hPB Bm hBm Q rho hRho Bcap hB hsupport hmean hsecond
    n hn x hx hscale beta delta hres h0 P nu hnu hcap s hs bill
  letI : IsProbabilityMeasure rho := hRho
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  letI : IsProbabilityMeasure (revealLaw P) := by unfold revealLaw; infer_instance
  have hx0 : 0 < x := by linarith only [hx]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hroot2 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hscalar (k : ℕ) : Integrable (fun z : ℝ => |z| ^ k) rho := by
    refine (integrable_const (Bcap ^ k)).mono'
      ((continuous_abs.measurable).pow_const k).aestronglyMeasurable ?_
    filter_upwards [hsupport] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg z) k)]
    exact pow_le_pow_left₀ (abs_nonneg z) hz k
  have h2 : Integrable (fun z : ℝ => z ^ 2) rho := by
    simpa only [sq_abs] using hscalar 2
  have h3 : Integrable (fun z : ℝ => |z| ^ 3) rho := hscalar 3
  have hbeta1 : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one
      rho h2 h3 hsecond
  have hbeta : 0 < beta := lt_of_lt_of_le zero_lt_one hbeta1
  have hbetaB : beta ≤ Bcap := by
    calc
      beta ≤ ∫ z : ℝ, Bcap * z ^ 2 ∂rho := by
        apply integral_mono_ae h3 (h2.const_mul Bcap)
        filter_upwards [hsupport] with z hz
        calc
          |z| ^ 3 = |z| * z ^ 2 := by rw [← sq_abs z]; ring
          _ ≤ Bcap * z ^ 2 := mul_le_mul_of_nonneg_right hz (sq_nonneg z)
      _ = Bcap := by rw [integral_const_mul, hsecond, mul_one]
  have hB1 : 1 ≤ Bcap := hbeta1.trans hbetaB
  have hscale' : (200 * x) * Bcap ≤ Real.sqrt (n : ℝ) := by
    have hh := (le_div_iff₀ (show 0 < 200 * x by positivity)).1 hscale
    nlinarith only [hh]
  have hBN : Bcap ≤ Real.sqrt (n : ℝ) := by
    have hh : Bcap ≤ (200 * x) * Bcap := by
      have hp := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 200 * x by linarith) hB.le
      simpa only [one_mul] using hp
    exact hh.trans hscale'
  have hn100 : 100 ≤ n := by
    have h3200 : (3200 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      have hp := mul_le_mul_of_nonneg_left hB1 (show 0 ≤ 200 * x by positivity)
      nlinarith only [hx, hp, hscale']
    have hn100R : (100 : ℝ) ≤ n := by
      nlinarith only [h3200, hroot2, Real.sqrt_nonneg (n : ℝ)]
    exact_mod_cast hn100R
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hdelta1 : delta ≤ 1 := by
    apply (div_le_one hroot).2
    exact hbetaB.trans hBN
  have hh0 : 0 < h0 := by dsimp [h0]; positivity
  have hExp1 : Real.exp (-3 * x ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])
  have hres1 : delta * (1 + x) ^ 3 ≤ 1 := hres.trans hExp1
  have hdeltaExp : delta ≤ Real.exp (-(89 / 100 : ℝ) * x ^ 2) := by
    have hx1 : 1 ≤ (1 + x) ^ 3 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + x)
    calc
      delta ≤ delta * (1 + x) ^ 3 := le_mul_of_one_le_right hdelta.le hx1
      _ ≤ Real.exp (-3 * x ^ 2) := hres
      _ ≤ _ := Real.exp_le_exp.2 (by nlinarith only [sq_nonneg x])
  let Pt : (t : ℕ) → Measure (Shao.Path t) := fun t => Measure.pi (fun _ : Fin t => rho)
  have hPt (t : ℕ) : IsProbabilityMeasure (Pt t) := by dsimp [Pt]; infer_instance
  let W : (t : ℕ) → Shao.Path t → ℝ := fun t u =>
    if 0 < Shao.energy u ∧ h0 ≤ Shao.energy u then
      |Shao.Probability.SourceIIDGaussianProfileBudget.firstValue u| ^ 3 /
        (Real.sqrt (Shao.energy u)) ^ 3 *
          Shao.Probability.SourceMarkedSuffixAveraging.suffixD u ^ 3 else 0
  have hg := hGrid rho h2 h3 hmean hsecond n hn
  have hWm (t : ℕ) : Measurable (W t) := (hg.1 t 3 (Or.inr rfl)).1
  have hWi (t : ℕ) : Integrable (W t) (Pt t) := (hg.1 t 3 (Or.inr rfl)).2.1
  have hWnn (t : ℕ) (u : Shao.Path t) : 0 ≤ W t u := (hg.1 t 3 (Or.inr rfl)).2.2 u
  have hEarlyGrid : (∑ t ∈ Finset.Icc (n / 2 + 1) n, ∫ u, W t u ∂Pt t) ≤ CG * delta :=
    hg.2.1
  -- This bound is independent of all probability estimates below.
  have hWbound (t : ℕ) (u : Shao.Path t) : W t u ≤ (1 + Real.sqrt (t : ℝ)) ^ 3 := by
    rcases Shao.Probability.SourceMarkedSuffixAveraging.suffix_normalized_geometry u with
      ⟨_, _, _, hmark, _, hD, _⟩
    dsimp only [W]
    split_ifs with hT
    · have ht : 0 < t := by
        by_contra hh
        have he : t = 0 := Nat.eq_zero_of_not_pos hh
        subst t
        simpa [Shao.energy] using hT.1
      have hden : (Real.sqrt (Shao.energy u)) ^ 3 =
          Shao.energy u * Real.sqrt (Shao.energy u) := by
        calc
          _ = (Real.sqrt (Shao.energy u)) ^ 2 * Real.sqrt (Shao.energy u) := by ring
          _ = _ := by rw [Real.sq_sqrt hT.1.le]
      have hm := hmark (⟨0, ht⟩ : Fin t)
      rw [Shao.Probability.SourceMarkedSuffixAveraging.normalizedCubicMark, if_pos hT.1] at hm
      rw [hden, Shao.Probability.SourceIIDGaussianProfileBudget.firstValue, dif_pos ht]
      exact (mul_le_mul hm.2 (pow_le_pow_left₀ (by linarith only [hD.1]) hD.2 3)
        (by positivity) (by norm_num)).trans_eq (one_mul _)
    · positivity
  -- Establish the actual bill's Measurable/L1/nonnegative data before comparison.
  have hActual := (apw_actual_postwall_bill_data PB Bm hBm P x hx0 nu hnu s).1
  refine ⟨hActual.1, hActual.2.1, hActual.2.2, ?_⟩
  let split : (k : ℕ) → k ≤ n → Shao.Path n → Shao.Path k × Shao.Path (n - k) :=
    fun k hk v => (Shao.Probability.Spitzer.head v k hk, Shao.Probability.Spitzer.tail v k hk)
  have hSplit (k : ℕ) (hk : k ≤ n) :
      MeasurePreserving (split k hk) P ((Pt k).prod (Pt (n - k))) := by
    let e : Fin k ⊕ Fin (n - k) ≃ Fin n :=
      finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hk))
    have h1 := (measurePreserving_piCongrLeft (fun _ : Fin n => rho) e).symm
    have h2' := measurePreserving_sumPiEquivProdPi (fun _ : Fin k ⊕ Fin (n - k) => rho)
    convert h2'.comp h1 using 1
    ext v i <;> change v _ = v _ <;> congr 1
  have hTailMP (k : ℕ) (hk : k ≤ n) :
      MeasurePreserving (fun v : Shao.Path n => (split k hk v).2) P (Pt (n - k)) := by
    letI := hPt k
    exact (measurePreserving_snd (μ := Pt k) (ν := Pt (n - k))).comp (hSplit k hk)
  let tail : (r : Fin n) → Shao.Path n → Shao.Path (n - r.val) :=
    fun r v => (split r.val r.is_lt.le v).2
  let head : (r : Fin n) → Shao.Path n → Shao.Path r.val :=
    fun r v => (split r.val r.is_lt.le v).1
  let er : Finset (Fin n) := Finset.univ.filter (fun r => 2 * r.val < n)
  let Hit : (r : Fin n) → Set (Shao.Path r.val) := fun r =>
    {v | ∃ k : Fin (r.val + 1), 0 < k.val ∧
      s * Shao.prefixSum v k.val ≤ -x * Real.sqrt ((9 / 10 : ℝ) * (n : ℝ))}
  have hHitM (r : Fin n) : MeasurableSet (Hit r) := by
    simp only [Hit, Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro k
    by_cases hk : 0 < k.val
    · simpa only [hk, true_and] using
        measurableSet_le ((Shao.measurable_prefixSum k.val).const_mul s) measurable_const
    · simp only [hk, false_and, Set.setOf_false]
      exact MeasurableSet.empty
  let Hi : Fin n → Shao.Path n → ℝ := fun r v =>
    (Hit r).indicator (fun _ => (1 : ℝ)) (head r v) * W (n - r.val) (tail r v)
  let Lo : Fin n → Shao.Path n → ℝ := fun r v =>
    {v : Shao.Path n | Shao.energy v < (9 / 10 : ℝ) * (n : ℝ)}.indicator
      (fun v => W (n - r.val) (tail r v)) v
  have hLowSet : MeasurableSet {v : Shao.Path n | Shao.energy v < (9 / 10 : ℝ) * (n : ℝ)} :=
    measurableSet_lt Shao.measurable_energy measurable_const
  have hHi (r : Fin n) : Measurable (Hi r) ∧ Integrable (Hi r) P ∧
      (∀ v, 0 ≤ Hi r v) ∧
      (∫ v, Hi r v ∂P) = (Pt r.val).real (Hit r) * ∫ u, W (n - r.val) u ∂Pt (n - r.val) := by
    let F : Shao.Path r.val × Shao.Path (n - r.val) → ℝ := fun p =>
      (Hit r).indicator (fun _ => (1 : ℝ)) p.1 * W (n - r.val) p.2
    letI := hPt r.val
    letI := hPt (n - r.val)
    have hm : Measurable F :=
      ((measurable_const.indicator (hHitM r)).comp measurable_fst).mul
        ((hWm _).comp measurable_snd)
    have hi : Integrable F ((Pt r.val).prod (Pt (n - r.val))) :=
      ((integrable_const (1 : ℝ)).indicator (hHitM r)).mul_prod (hWi _)
    refine ⟨hm.comp (hSplit r.val r.is_lt.le).measurable,
      (hSplit r.val r.is_lt.le).integrable_comp_of_integrable hi, ?_, ?_⟩
    · intro v
      exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (hWnn _ _)
    · have he := integral_map (μ := P) (φ := split r.val r.is_lt.le) (f := F)
        (hSplit r.val r.is_lt.le).measurable.aemeasurable hm.aestronglyMeasurable
      rw [(hSplit r.val r.is_lt.le).map_eq, integral_prod_mul] at he
      rw [← he]
      congr 1
      rw [integral_indicator_const _ (hHitM r), smul_eq_mul, mul_one]
  have hLo (r : Fin n) : Measurable (Lo r) ∧ Integrable (Lo r) P ∧ (∀ v, 0 ≤ Lo r v) := by
    have hm := (hWm (n - r.val)).comp (hTailMP r.val r.is_lt.le).measurable
    have hi := (hTailMP r.val r.is_lt.le).integrable_comp_of_integrable (hWi (n - r.val))
    exact ⟨hm.indicator hLowSet, hi.indicator hLowSet,
      fun v => Set.indicator_nonneg (fun u _ => hWnn _ _) v⟩
  have hHighPaid (r : Fin n) (hr : r ∈ er) :
      (∫ v, Hi r v ∂P) ≤ (CH * Real.exp (-(89 / 100 : ℝ) * x ^ 2)) *
        ∫ u, W (n - r.val) u ∂Pt (n - r.val) := by
    have hr' : 2 * r.val ≤ n := by have := (Finset.mem_filter.1 hr).2; omega
    have hh := hHit rho Bcap hB hsupport hmean hsecond n hn x hx hscale hres1 r.val hr' s hs
    rw [(hHi r).2.2.2]
    exact mul_le_mul_of_nonneg_right hh (integral_nonneg (hWnn _))
  have hReindex (f : ℕ → ℝ) :
      (∑ r ∈ er, f (n - r.val)) = ∑ t ∈ Finset.Icc (n / 2 + 1) n, f t := by
    apply Finset.sum_bij (fun r _ => n - r.val)
    · intro r hr
      have hh := (Finset.mem_filter.1 hr).2
      simp only [Finset.mem_Icc]
      omega
    · intro r hr r' hr' heq
      apply Fin.ext
      omega
    · intro t ht
      have hh := Finset.mem_Icc.1 ht
      refine ⟨⟨n - t, by omega⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · change 2 * (n - t) < n
        omega
      · dsimp only
        omega
    · intro r hr
      rfl
  have hHighSum : (∑ r ∈ er, ∫ v, Hi r v ∂P) ≤
      CH * CG * delta * Real.exp (-(89 / 100 : ℝ) * x ^ 2) := by
    calc
      _ ≤ ∑ r ∈ er, (CH * Real.exp (-(89 / 100 : ℝ) * x ^ 2)) *
          ∫ u, W (n - r.val) u ∂Pt (n - r.val) := Finset.sum_le_sum hHighPaid
      _ = (CH * Real.exp (-(89 / 100 : ℝ) * x ^ 2)) *
          ∑ t ∈ Finset.Icc (n / 2 + 1) n, ∫ u, W t u ∂Pt t := by
        rw [← Finset.mul_sum, hReindex]
      _ ≤ (CH * Real.exp (-(89 / 100 : ℝ) * x ^ 2)) * (CG * delta) :=
        mul_le_mul_of_nonneg_left hEarlyGrid (by positivity)
      _ = _ := by ring
  -- Low energy: the current mark is removed only from the necessary event.
  let dp : Fin n → Shao.Path n → ℝ := fun r v =>
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => r.val < i.val), v i
  let em : Fin n → Shao.Path n → ℝ := fun r v => Shao.energy v - (v r) ^ 2
  let EP : Fin n → Set (Shao.Path n) := fun r =>
    {v | em r v < (9 / 10 : ℝ) * (n : ℝ)}
  let p0 : ℝ := Real.exp (-(n : ℝ) / (125000 * beta ^ 2))
  let q0 : ℝ := Real.exp (-a0 / delta ^ 2)
  have hp0 : 0 < p0 := Real.exp_pos _
  have hq0 : 0 < q0 := Real.exp_pos _
  have hDpm (r : Fin n) : Measurable (dp r) := by dsimp [dp]; fun_prop
  have hEmm (r : Fin n) : Measurable (em r) := by dsimp [em]; fun_prop
  have hEPm (r : Fin n) : MeasurableSet (EP r) := measurableSet_lt (hEmm r) measurable_const
  have hEPTail (r : Fin n) : P.real (EP r) ≤ p0 :=
    apw_deleted_energy_lower_tail rho h2 h3 hmean hsecond n hn100 r
  have hTailSum (k : ℕ) (hk : k ≤ n) (v : Shao.Path n) :
      Shao.prefixSum (split k hk v).2 (n - k) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), v i := by
    rw [Shao.prefixSum_length]
    refine Finset.sum_bij (fun (i : Fin (n - k)) _ => (⟨k + i.val, by omega⟩ : Fin n)) ?_ ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by dsimp only; omega⟩
    · intro i hi j hj hij
      apply Fin.ext
      have hh := congrArg Fin.val hij
      dsimp only at hh
      omega
    · intro i hi
      have hh := (Finset.mem_filter.1 hi).2
      refine ⟨⟨i.val - k, by omega⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      dsimp only
      omega
    · intro i hi
      rfl
  have hDpTail (r : Fin n) (v : Shao.Path n) :
      dp r v = Shao.prefixSum (split (r.val + 1) (by omega) v).2 (n - (r.val + 1)) := by
    rw [hTailSum]
    dsimp only [dp]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hDSplit (r : Fin n) (v : Shao.Path n) :
      Shao.prefixSum (tail r v) (n - r.val) = v r + dp r v := by
    rw [hTailSum]
    let A : Finset (Fin n) := Finset.univ.filter (fun i => r.val ≤ i.val)
    have hrA : r ∈ A := Finset.mem_filter.2 ⟨Finset.mem_univ _, le_rfl⟩
    have hErase : A.erase r = Finset.univ.filter (fun i : Fin n => r.val < i.val) := by
      ext i
      simp only [A, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hne, hle⟩
        have hv : i.val ≠ r.val := fun hh => hne (Fin.ext hh)
        omega
      · intro hlt
        exact ⟨fun hh => by subst i; omega, hlt.le⟩
    change (∑ i ∈ A, v i) = _
    rw [← Finset.sum_erase_add _ _ hrA, hErase]
    dsimp only [dp]
    ring
  have hDp6 (r : Fin n) : Integrable (fun v => |dp r v| ^ 6) P ∧
      (∫ v, |dp r v| ^ 6 ∂P) ≤ 41 * (n : ℝ) ^ 3 := by
    let l : ℕ := n - (r.val + 1)
    have hh := apw_centered_sum_sixth_moment rho Bcap hB hsupport hmean hsecond
      n hn hBN l (by dsimp [l]; omega)
    have hm : Measurable (fun u : Shao.Path l => |Shao.prefixSum u l| ^ 6) := by fun_prop
    have hi : Integrable (fun v : Shao.Path n =>
        |Shao.prefixSum (split (r.val + 1) (by omega) v).2 l| ^ 6) P :=
      (hTailMP (r.val + 1) (by omega)).integrable_comp_of_integrable hh.1
    have he := integral_map (μ := P) (φ := fun v : Shao.Path n =>
        (split (r.val + 1) (by omega) v).2)
      (f := fun u : Shao.Path l => |Shao.prefixSum u l| ^ 6)
      (hTailMP (r.val + 1) (by omega)).measurable.aemeasurable hm.aestronglyMeasurable
    rw [(hTailMP (r.val + 1) (by omega)).map_eq] at he
    simp_rw [← hDpTail] at hi he
    exact ⟨hi, he.symm.trans_le hh.2⟩
  have hBox : ∀ᵐ v : Shao.Path n ∂P, ∀ i : Fin n, |v i| ≤ Bcap := by
    apply ae_all_iff.2
    intro i
    exact (measurePreserving_eval (μ := fun _ : Fin n => rho) i).quasiMeasurePreserving.ae hsupport
  have hBoxI (f : Shao.Path n → ℝ) (hm : Measurable f) (M : ℝ)
      (hb : ∀ v, (∀ i : Fin n, |v i| ≤ Bcap) → |f v| ≤ M) : Integrable f P := by
    refine (integrable_const M).mono' hm.aestronglyMeasurable ?_
    filter_upwards [hBox] with v hv
    simpa only [Real.norm_eq_abs] using hb v hv
  have hDpBound (r : Fin n) (v : Shao.Path n) (hv : ∀ i : Fin n, |v i| ≤ Bcap) :
      |dp r v| ≤ (n : ℝ) * Bcap := by
    calc
      |dp r v| ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => r.val < i.val), |v i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, |v i| := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun i _ _ => abs_nonneg _)
      _ ≤ ∑ _i : Fin n, Bcap := Finset.sum_le_sum fun i _ => hv i
      _ = _ := by simp
  have hDp3I (r : Fin n) : Integrable (fun v => |dp r v| ^ 3) P := by
    apply hBoxI _ ((hDpm r).abs.pow_const 3) (((n : ℝ) * Bcap) ^ 3)
    intro v hv
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hDpBound r v hv) 3
  let U : Fin n → Shao.Path n → ℝ := fun r => (EP r).indicator (fun _ => (1 : ℝ))
  let V : Fin n → Shao.Path n → ℝ := fun r => (EP r).indicator (fun v => |dp r v| ^ 3)
  have hUm (r : Fin n) : Measurable (U r) := measurable_const.indicator (hEPm r)
  have hUi (r : Fin n) : Integrable (U r) P := (integrable_const _).indicator (hEPm r)
  have hVm (r : Fin n) : Measurable (V r) := ((hDpm r).abs.pow_const 3).indicator (hEPm r)
  have hVi (r : Fin n) : Integrable (V r) P := (hDp3I r).indicator (hEPm r)
  have hUE (r : Fin n) : (∫ v, U r v ∂P) = P.real (EP r) := by
    rw [integral_indicator_const _ (hEPm r), smul_eq_mul, mul_one]
  have hU0 (r : Fin n) (v : Shao.Path n) : 0 ≤ U r v := Set.indicator_nonneg (fun _ _ => zero_le_one) v
  have hV0 (r : Fin n) (v : Shao.Path n) : 0 ≤ V r v := Set.indicator_nonneg (fun _ _ => by positivity) v
  -- Cauchy is applied to dp and EP together; no independence is asserted here.
  have hVBound (r : Fin n) : (∫ v, V r v ∂P) ≤
      (Real.sqrt 41 * ((n : ℝ) * Real.sqrt (n : ℝ))) * Real.sqrt (P.real (EP r)) := by
    let f : Shao.Path n → ℝ := fun v => |dp r v| ^ 3
    let g : Shao.Path n → ℝ := U r
    have hfm : Measurable f := (hDpm r).abs.pow_const 3
    have hgm : Measurable g := hUm r
    have hfsq : (fun v => f v ^ 2) = fun v => |dp r v| ^ 6 := by funext v; dsimp [f]; ring
    have hgsq : (fun v => g v ^ 2) = U r := by
      funext v
      by_cases hv : v ∈ EP r <;> simp [g, U, hv]
    have hflp : MemLp f 2 P := (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).2
      (hfsq.symm ▸ (hDp6 r).1)
    have hglp : MemLp g 2 P := (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2
      (hgsq.symm ▸ hUi r)
    have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (ae_of_all _ fun v => by dsimp [f]; positivity)
      (ae_of_all _ fun v => hU0 r v)
      (by simpa using hflp) (by simpa using hglp)
    have hprod : (fun v => f v * g v) = V r := by
      funext v
      by_cases hv : v ∈ EP r <;> simp [f, g, U, V, hv]
    have hcs' : (∫ v, V r v ∂P) ≤
        Real.sqrt (∫ v, |dp r v| ^ 6 ∂P) * Real.sqrt (P.real (EP r)) := by
      simpa only [Real.rpow_natCast, Real.rpow_ofNat, ← Real.sqrt_eq_rpow,
        hfsq, hgsq, hprod, hUE] using hcs
    have hrootN : Real.sqrt (41 * (n : ℝ) ^ 3) =
        Real.sqrt 41 * ((n : ℝ) * Real.sqrt (n : ℝ)) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 41)]
      congr 1
      apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
      have hh := congrArg (fun z : ℝ => (n : ℝ) ^ 2 * z) hroot2
      nlinarith only [hh]
    exact hcs'.trans (mul_le_mul_of_nonneg_right
      ((Real.sqrt_le_sqrt (hDp6 r).2).trans_eq hrootN) (Real.sqrt_nonneg _))
  -- A single coordinate is independent of every measurable function of the
  -- complete tuple of other coordinates, including (dp,EP) jointly.
  have hCoordRest (r : Fin n) :
      IndepFun (fun v : Shao.Path n => v r)
        (fun v : Shao.Path n => fun i : (Finset.univ.erase r : Finset (Fin n)) => v i) P := by
    have hInd : iIndepFun (fun i : Fin n => Function.eval i) P :=
      iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)
    have hd : Disjoint ({r} : Finset (Fin n)) (Finset.univ.erase r) := by simp
    have hh := hInd.indepFun_finset {r} (Finset.univ.erase r) hd
      (fun i => measurable_pi_apply i)
    have hc := hh.comp (measurable_pi_apply (⟨r, by simp⟩ : ({r} : Finset (Fin n)))) measurable_id
    simpa only [Function.comp_def, id_eq] using hc
  have hIgnore (r : Fin n) (F : Shao.Path n → ℝ) (hFm : Measurable F)
      (hF : ∀ v w, (∀ i : Fin n, i ≠ r → v i = w i) → F v = F w) :
      IndepFun (fun v : Shao.Path n => v r) F P := by
    let lift : ((Finset.univ.erase r : Finset (Fin n)) → ℝ) → Shao.Path n :=
      fun y i => if hi : i ∈ Finset.univ.erase r then y ⟨i, hi⟩ else 0
    have hlift : Measurable lift := by
      apply Measurable.of_eval
      intro i
      by_cases hi : i ∈ Finset.univ.erase r
      · simpa only [lift, dif_pos hi] using (measurable_pi_apply ⟨i, hi⟩)
      · simpa only [lift, dif_neg hi] using (measurable_const : Measurable (fun _ => (0 : ℝ)))
    have heq : (fun v : Shao.Path n => F (lift (fun i => v i))) = F := by
      funext v
      apply hF
      intro i hi
      have hi' : i ∈ Finset.univ.erase r := Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩
      simp only [lift, dif_pos hi']
    have hh := (hCoordRest r).comp measurable_id (hFm.comp hlift)
    simpa only [Function.comp_def, id_eq, heq] using hh
  have hEmIgnore (r : Fin n) (v w : Shao.Path n)
      (hvw : ∀ i : Fin n, i ≠ r → v i = w i) : em r v = em r w := by
    have he (u : Shao.Path n) : em r u = ∑ i ∈ Finset.univ.erase r, (u i) ^ 2 := by
      dsimp only [em, Shao.energy]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ r)]
      ring
    rw [he v, he w]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hvw i (Finset.mem_erase.1 hi).1]
  have hDpIgnore (r : Fin n) (v w : Shao.Path n)
      (hvw : ∀ i : Fin n, i ≠ r → v i = w i) : dp r v = dp r w := by
    apply Finset.sum_congr rfl
    intro i hi
    have hir : i ≠ r := by intro hh; subst i; exact (Nat.lt_irrefl _) (Finset.mem_filter.1 hi).2
    exact hvw i hir
  have hUInd (r : Fin n) : IndepFun (fun v : Shao.Path n => v r) (U r) P := by
    apply hIgnore r (U r) (hUm r)
    intro v w hvw
    have hh : v ∈ EP r ↔ w ∈ EP r := by dsimp only [EP]; rw [hEmIgnore r v w hvw]
    by_cases hv : v ∈ EP r
    · simp only [U, Set.indicator_of_mem hv, Set.indicator_of_mem (hh.mp hv)]
    · simp only [U, Set.indicator_of_notMem hv, Set.indicator_of_notMem (fun hw => hv (hh.mpr hw))]
  have hVInd (r : Fin n) : IndepFun (fun v : Shao.Path n => v r) (V r) P := by
    apply hIgnore r (V r) (hVm r)
    intro v w hvw
    have hh : v ∈ EP r ↔ w ∈ EP r := by dsimp only [EP]; rw [hEmIgnore r v w hvw]
    by_cases hv : v ∈ EP r
    · simp only [V, Set.indicator_of_mem hv, Set.indicator_of_mem (hh.mp hv), hDpIgnore r v w hvw]
    · simp only [V, Set.indicator_of_notMem hv, Set.indicator_of_notMem (fun hw => hv (hh.mpr hw))]
  have hMarkI (r : Fin n) (k : ℕ) : Integrable (fun v : Shao.Path n => |v r| ^ k) P :=
    (measurePreserving_eval (μ := fun _ : Fin n => rho) r).integrable_comp_of_integrable (hscalar k)
  have hMarkE (r : Fin n) (k : ℕ) : (∫ v : Shao.Path n, |v r| ^ k ∂P) = ∫ z : ℝ, |z| ^ k ∂rho := by
    have he := integral_map (μ := P) (φ := fun v : Shao.Path n => v r)
      (f := fun z : ℝ => |z| ^ k)
      (measurePreserving_eval (μ := fun _ : Fin n => rho) r).measurable.aemeasurable
      ((continuous_abs.measurable).pow_const k).aestronglyMeasurable
    rw [(measurePreserving_eval (μ := fun _ : Fin n => rho) r).map_eq] at he
    exact he.symm
  have hSixth : (∫ z : ℝ, |z| ^ 6 ∂rho) ≤ Bcap ^ 3 * beta := by
    calc
      _ ≤ ∫ z : ℝ, Bcap ^ 3 * |z| ^ 3 ∂rho := by
        apply integral_mono_ae (hscalar 6) (h3.const_mul _)
        filter_upwards [hsupport] with z hz
        have hh := pow_le_pow_left₀ (abs_nonneg z) hz 3
        calc
          |z| ^ 6 = |z| ^ 3 * |z| ^ 3 := by ring
          _ ≤ Bcap ^ 3 * |z| ^ 3 :=
            mul_le_mul_of_nonneg_right hh (pow_nonneg (abs_nonneg z) 3)
      _ = _ := integral_const_mul _ _
  have hCube (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
      (u + v) ^ 3 ≤ 4 * (u ^ 3 + v ^ 3) := by
    have hh := mul_nonneg (add_nonneg hu hv) (sq_nonneg (u - v))
    nlinarith only [hh]
  have hCarrier (r : Fin n) (v : Shao.Path n) :
      W (n - r.val) (tail r v) ≤
        |v r| ^ 3 / beta ^ 3 + |v r| ^ 6 / beta ^ 6 +
          |v r| ^ 3 * |dp r v| ^ 3 / beta ^ 6 := by
    let u := tail r v
    let R : ℝ := Real.sqrt (Shao.energy u)
    have ht : 0 < n - r.val := by omega
    have hb : Shao.Probability.SourceIIDGaussianProfileBudget.firstValue u = v r := by
      simp only [Shao.Probability.SourceIIDGaussianProfileBudget.firstValue, dif_pos ht,
        u, tail, split, Shao.Probability.Spitzer.tail]
      congr 1
    by_cases hT : 0 < Shao.energy u ∧ h0 ≤ Shao.energy u
    · have hR : 0 < R := Real.sqrt_pos.2 hT.1
      have hR2 : R ^ 2 = Shao.energy u := Real.sq_sqrt hT.1.le
      have hRbeta : 2 * beta ≤ R := by
        have hh : 4 * beta ^ 2 ≤ Shao.energy u := hT.2
        nlinarith only [hh, hR2, hR.le, hbeta.le]
      have hR3 : 8 * beta ^ 3 ≤ R ^ 3 := by
        have hh := pow_le_pow_left₀ (show 0 ≤ 2 * beta by positivity) hRbeta 3
        nlinarith only [hh]
      have hd : |Shao.prefixSum u (n - r.val)| ^ 3 ≤
          4 * (|v r| ^ 3 + |dp r v| ^ 3) := by
        rw [hDSplit]
        exact (pow_le_pow_left₀ (abs_nonneg _) (abs_add _ _) 3).trans
          (hCube |v r| |dp r v| (abs_nonneg _) (abs_nonneg _))
      have hD : Shao.Probability.SourceMarkedSuffixAveraging.suffixD u ^ 3 ≤
          4 + 2 * (|v r| ^ 3 + |dp r v| ^ 3) / beta ^ 3 := by
        rw [Shao.Probability.SourceMarkedSuffixAveraging.suffixD, if_pos hT.1]
        change (1 + |Shao.prefixSum u (n - r.val)| / R) ^ 3 ≤ _
        calc
          _ ≤ 4 * (1 + (|Shao.prefixSum u (n - r.val)| / R) ^ 3) := by
            simpa only [one_pow] using hCube 1 (|Shao.prefixSum u (n - r.val)| / R)
              zero_le_one (by positivity)
          _ = 4 + 4 * |Shao.prefixSum u (n - r.val)| ^ 3 / R ^ 3 := by rw [div_pow]; ring
          _ ≤ 4 + 16 * (|v r| ^ 3 + |dp r v| ^ 3) / R ^ 3 := by
            apply add_le_add_left _ 4
            apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ R ^ 3)
            nlinarith only [hd]
          _ ≤ 4 + 16 * (|v r| ^ 3 + |dp r v| ^ 3) / (8 * beta ^ 3) := by
            gcongr
          _ = _ := by field_simp [hbeta.ne']; ring
      have hCoef : |v r| ^ 3 / R ^ 3 ≤ |v r| ^ 3 / (8 * beta ^ 3) := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hR3
      have hD0 : 0 ≤ Shao.Probability.SourceMarkedSuffixAveraging.suffixD u ^ 3 := by
        have hh : 1 ≤ Shao.Probability.SourceMarkedSuffixAveraging.suffixD u :=
          (Shao.Probability.SourceMarkedSuffixAveraging.suffix_normalized_geometry u).2.2.2.2.2.1.1
        exact pow_nonneg (zero_le_one.trans hh) 3
      change W (n - r.val) u ≤ _
      rw [W, if_pos hT, hb]
      change |v r| ^ 3 / R ^ 3 * _ ≤ _
      calc
        _ ≤ (|v r| ^ 3 / (8 * beta ^ 3)) *
            (4 + 2 * (|v r| ^ 3 + |dp r v| ^ 3) / beta ^ 3) :=
          mul_le_mul hCoef hD hD0 (by positivity)
        _ ≤ _ := by
          have heq :
              (|v r| ^ 3 / beta ^ 3 + |v r| ^ 6 / beta ^ 6 +
                |v r| ^ 3 * |dp r v| ^ 3 / beta ^ 6) -
              (|v r| ^ 3 / (8 * beta ^ 3)) *
                (4 + 2 * (|v r| ^ 3 + |dp r v| ^ 3) / beta ^ 3) =
              |v r| ^ 3 / (2 * beta ^ 3) +
                3 * |v r| ^ 6 / (4 * beta ^ 6) +
                3 * |v r| ^ 3 * |dp r v| ^ 3 / (4 * beta ^ 6) := by
            field_simp [hbeta.ne']
            ring
          have hnn : 0 ≤ |v r| ^ 3 / (2 * beta ^ 3) +
              3 * |v r| ^ 6 / (4 * beta ^ 6) +
              3 * |v r| ^ 3 * |dp r v| ^ 3 / (4 * beta ^ 6) := by positivity
          linarith only [heq, hnn]
    · change W (n - r.val) u ≤ _
      rw [W, if_neg hT]
      positivity
  let Rlow : Fin n → Shao.Path n → ℝ := fun r v =>
    (|v r| ^ 3 * U r v) / beta ^ 3 + (|v r| ^ 6 * U r v) / beta ^ 6 +
      (|v r| ^ 3 * V r v) / beta ^ 6
  have hMixU (r : Fin n) (k : ℕ) :
      IndepFun (fun v : Shao.Path n => |v r| ^ k) (U r) P := by
    simpa only [Function.comp_def, id_eq] using
      (hUInd r).comp ((continuous_abs.measurable).pow_const k) measurable_id
  have hMixV (r : Fin n) :
      IndepFun (fun v : Shao.Path n => |v r| ^ 3) (V r) P := by
    simpa only [Function.comp_def, id_eq] using
      (hVInd r).comp ((continuous_abs.measurable).pow_const 3) measurable_id
  have hRlowI (r : Fin n) : Integrable (Rlow r) P := by
    have hi3 := ((hMixU r 3).integrable_mul (hMarkI r 3) (hUi r)).div_const (beta ^ 3)
    have hi6 := ((hMixU r 6).integrable_mul (hMarkI r 6) (hUi r)).div_const (beta ^ 6)
    have hiV := ((hMixV r).integrable_mul (hMarkI r 3) (hVi r)).div_const (beta ^ 6)
    exact (hi3.add hi6).add hiV
  have hRlowNN (r : Fin n) (v : Shao.Path n) : 0 ≤ Rlow r v := by
    have hu := hU0 r v
    have hv := hV0 r v
    dsimp only [Rlow]
    positivity
  have hRlowE (r : Fin n) : (∫ v, Rlow r v ∂P) =
      beta * P.real (EP r) / beta ^ 3 +
        (∫ z : ℝ, |z| ^ 6 ∂rho) * P.real (EP r) / beta ^ 6 +
          beta * (∫ v, V r v ∂P) / beta ^ 6 := by
    have hi3 := (hMixU r 3).integrable_mul (hMarkI r 3) (hUi r)
    have hi6 := (hMixU r 6).integrable_mul (hMarkI r 6) (hUi r)
    have hiV := (hMixV r).integrable_mul (hMarkI r 3) (hVi r)
    rw [show Rlow r = fun v =>
      (|v r| ^ 3 * U r v) / beta ^ 3 + (|v r| ^ 6 * U r v) / beta ^ 6 +
        (|v r| ^ 3 * V r v) / beta ^ 6 from rfl,
      integral_add ((hi3.div_const _).add (hi6.div_const _)) (hiV.div_const _),
      integral_add (hi3.div_const _) (hi6.div_const _),
      integral_div, integral_div, integral_div,
      (hMixU r 3).integral_fun_mul_eq_mul_integral (hMarkI r 3).aestronglyMeasurable (hUi r).aestronglyMeasurable,
      (hMixU r 6).integral_fun_mul_eq_mul_integral (hMarkI r 6).aestronglyMeasurable (hUi r).aestronglyMeasurable,
      (hMixV r).integral_fun_mul_eq_mul_integral (hMarkI r 3).aestronglyMeasurable (hVi r).aestronglyMeasurable,
      hMarkE r 3, hMarkE r 6, hUE]
  have hLoPoint (r : Fin n) (v : Shao.Path n) : Lo r v ≤ Rlow r v := by
    by_cases hv : Shao.energy v < (9 / 10 : ℝ) * (n : ℝ)
    · have he : v ∈ EP r := by
        change Shao.energy v - (v r) ^ 2 < _
        exact (sub_le_self _ (sq_nonneg _)).trans_lt hv
      rw [Lo, Set.indicator_of_mem hv]
      have hh := hCarrier r v
      simpa only [Rlow, U, V, Set.indicator_of_mem he, mul_one] using hh
    · rw [Lo, Set.indicator_of_notMem hv]
      exact hRlowNN r v
  have hLoPaid (r : Fin n) : (∫ v, Lo r v ∂P) ≤
      p0 / beta ^ 2 + Bcap ^ 3 * p0 / beta ^ 5 +
        (Real.sqrt 41 * ((n : ℝ) * Real.sqrt (n : ℝ))) * Real.sqrt p0 / beta ^ 5 := by
    have hVpay : (∫ v, V r v ∂P) ≤
        (Real.sqrt 41 * ((n : ℝ) * Real.sqrt (n : ℝ))) * Real.sqrt p0 :=
      (hVBound r).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hEPTail r)) (by positivity))
    have hm6 : 0 ≤ ∫ z : ℝ, |z| ^ 6 ∂rho := integral_nonneg (fun z => by positivity)
    calc
      _ ≤ ∫ v, Rlow r v ∂P := integral_mono (hLo r).2.1 (hRlowI r) (hLoPoint r)
      _ = _ := hRlowE r
      _ ≤ beta * p0 / beta ^ 3 + (Bcap ^ 3 * beta) * p0 / beta ^ 6 +
          beta * ((Real.sqrt 41 * ((n : ℝ) * Real.sqrt (n : ℝ))) * Real.sqrt p0) / beta ^ 6 := by
        gcongr
        · exact hEPTail r
        · exact hSixth
        · exact hEPTail r
        · exact hVpay
      _ = _ := by field_simp [hbeta.ne']; ring
  have hpq : p0 = q0 ^ 2 := by
    rw [q0, ← Real.exp_nat_mul]
    congr 1
    dsimp only [p0, a0, delta]
    field_simp [hbeta.ne', hroot.ne']
    nlinarith only [hroot2]
  have hq1 : q0 ≤ 1 := Real.exp_le_one_iff.2
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 ha0.le) (sq_nonneg delta))
  have hpqle : p0 ≤ q0 := by rw [hpq]; nlinarith only [hq0.le, hq1]
  have hsqrtp : Real.sqrt p0 = q0 := by rw [hpq, Real.sqrt_sq_eq_abs, abs_of_pos hq0]
  have hRatio2 : (n : ℝ) / beta ^ 2 = 1 / delta ^ 2 := by
    dsimp only [delta]
    field_simp [hbeta.ne', hroot.ne']
    nlinarith only [hroot2]
  have hRatio5 : ((n : ℝ) ^ 2 * Real.sqrt (n : ℝ)) / beta ^ 5 = 1 / delta ^ 5 := by
    have hroot4 : (Real.sqrt (n : ℝ)) ^ 4 = (n : ℝ) ^ 2 := by
      calc
        _ = ((Real.sqrt (n : ℝ)) ^ 2) ^ 2 := by ring
        _ = _ := by rw [hroot2]
    dsimp only [delta]
    field_simp [hbeta.ne', hroot.ne']
    nlinarith only [congrArg (fun z : ℝ => z * Real.sqrt (n : ℝ)) hroot4]
  have hB3 : Bcap ^ 3 ≤ (n : ℝ) * Real.sqrt (n : ℝ) := by
    have hh := pow_le_pow_left₀ hB.le hBN 3
    calc
      Bcap ^ 3 ≤ (Real.sqrt (n : ℝ)) ^ 3 := hh
      _ = (n : ℝ) * Real.sqrt (n : ℝ) := by
        calc
          _ = (Real.sqrt (n : ℝ)) ^ 2 * Real.sqrt (n : ℝ) := by ring
          _ = _ := by rw [hroot2]
  have hLowSumRaw : (∑ r ∈ er, ∫ v, Lo r v ∂P) ≤
      (1 / delta ^ 2 + (1 + Real.sqrt 41) / delta ^ 5) * q0 := by
    let K : ℝ := p0 / beta ^ 2 + Bcap ^ 3 * p0 / beta ^ 5 +
      (Real.sqrt 41 * ((n : ℝ) * Real.sqrt (n : ℝ))) * Real.sqrt p0 / beta ^ 5
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hcard : (er.card : ℝ) ≤ n := by
      have hcn : er.card ≤ n := by
        calc
          er.card ≤ (Finset.univ : Finset (Fin n)).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
          _ = n := by simp
      exact_mod_cast hcn
    calc
      _ ≤ ∑ _r ∈ er, K := Finset.sum_le_sum fun r _ => hLoPaid r
      _ = (er.card : ℝ) * K := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℝ) * K := mul_le_mul_of_nonneg_right hcard hK
      _ ≤ (n : ℝ) * (q0 / beta ^ 2 +
          ((n : ℝ) * Real.sqrt (n : ℝ)) * q0 / beta ^ 5 +
          (Real.sqrt 41 * ((n : ℝ) * Real.sqrt (n : ℝ))) * q0 / beta ^ 5) := by
        dsimp only [K]
        rw [hsqrtp]
        gcongr
      _ = ((n : ℝ) / beta ^ 2 + (1 + Real.sqrt 41) *
          ((n : ℝ) ^ 2 * Real.sqrt (n : ℝ) / beta ^ 5)) * q0 := by ring
      _ = _ := by rw [hRatio2, hRatio5]; ring
  -- Only the two displayed inverse powers are paid, using fixed Taylor terms.
  let y : ℝ := a0 / delta ^ 2
  have hy : 0 < y := by dsimp [y]; positivity
  have hExp2 : y ^ 2 / 2 ≤ Real.exp y := by
    simpa only [show (2 : ℕ).factorial = 2 by norm_num, Nat.cast_ofNat] using
      Real.pow_div_factorial_le_exp y hy.le 2
  have hExp4 : y ^ 4 / 24 ≤ Real.exp y := by
    simpa only [show (4 : ℕ).factorial = 24 by norm_num, Nat.cast_ofNat] using
      Real.pow_div_factorial_le_exp y hy.le 4
  have hExpCancel : Real.exp y * q0 = 1 := by
    rw [q0, ← Real.exp_add]
    simp only [y, neg_div, add_neg_cancel, Real.exp_zero]
  have hPay2 : (1 / delta ^ 2) * q0 ≤ (2 / a0 ^ 2) * delta ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hExp2 hq0.le
    rw [hExpCancel] at hh
    have hh' : a0 ^ 2 * q0 ≤ 2 * delta ^ 4 := by
      have hmul := mul_le_mul_of_nonneg_right hh (show 0 ≤ 2 * delta ^ 4 by positivity)
      have heq : (y ^ 2 / 2 * q0) * (2 * delta ^ 4) = a0 ^ 2 * q0 := by
        dsimp only [y]
        field_simp [hdelta.ne']
        ring
      simpa only [heq, one_mul] using hmul
    have hqpay : q0 ≤ (2 * delta ^ 4) / a0 ^ 2 :=
      (le_div_iff₀ (show 0 < a0 ^ 2 by positivity)).2 (by nlinarith only [hh'])
    calc
      _ ≤ (1 / delta ^ 2) * ((2 * delta ^ 4) / a0 ^ 2) :=
        mul_le_mul_of_nonneg_left hqpay (by positivity)
      _ = _ := by field_simp [hdelta.ne', ha0.ne']; ring
  have hPay5 : (1 / delta ^ 5) * q0 ≤ (24 / a0 ^ 4) * delta ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hExp4 hq0.le
    rw [hExpCancel] at hh
    have hh' : a0 ^ 4 * q0 ≤ 24 * delta ^ 8 := by
      have hmul := mul_le_mul_of_nonneg_right hh (show 0 ≤ 24 * delta ^ 8 by positivity)
      have heq : (y ^ 4 / 24 * q0) * (24 * delta ^ 8) = a0 ^ 4 * q0 := by
        dsimp only [y]
        field_simp [hdelta.ne']
        ring
      simpa only [heq, one_mul] using hmul
    have hsmall : 24 * delta ^ 8 ≤ 24 * delta ^ 7 := by
      have hh := mul_le_mul_of_nonneg_left hdelta1 (show 0 ≤ 24 * delta ^ 7 by positivity)
      nlinarith only [hh]
    have hqpay : q0 ≤ (24 * delta ^ 7) / a0 ^ 4 :=
      (le_div_iff₀ (show 0 < a0 ^ 4 by positivity)).2
        (by nlinarith only [hh', hsmall])
    calc
      _ ≤ (1 / delta ^ 5) * ((24 * delta ^ 7) / a0 ^ 4) :=
        mul_le_mul_of_nonneg_left hqpay (by positivity)
      _ = _ := by field_simp [hdelta.ne', ha0.ne']; ring
  have hLowSum : (∑ r ∈ er, ∫ v, Lo r v ∂P) ≤
      CL * delta * Real.exp (-(89 / 100 : ℝ) * x ^ 2) := by
    calc
      _ ≤ (1 / delta ^ 2 + (1 + Real.sqrt 41) / delta ^ 5) * q0 := hLowSumRaw
      _ = (1 / delta ^ 2) * q0 + (1 + Real.sqrt 41) * ((1 / delta ^ 5) * q0) := by ring
      _ ≤ (2 / a0 ^ 2) * delta ^ 2 + (1 + Real.sqrt 41) * ((24 / a0 ^ 4) * delta ^ 2) :=
        add_le_add hPay2 (mul_le_mul_of_nonneg_left hPay5 (by positivity))
      _ = CL * delta ^ 2 := by dsimp only [CL]; ring
      _ ≤ CL * (delta * Real.exp (-(89 / 100 : ℝ) * x ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hCL.le
        nlinarith only [mul_le_mul_of_nonneg_left hdeltaExp hdelta.le]
      _ = _ := by ring
  -- Remove cap and the actual kernel factors pointwise before iid transport.
  have hGaussianLe (r : Fin n) (v : Shao.Path n) :
      Shao.Probability.SourceIIDGaussianProfileBudget.rankGaussianWeight h0 x {s} false v r ≤
        W (n - r.val) (tail r v) := by
    let u := tail r v
    let w := head r v
    have hD0 : 0 ≤ Shao.Probability.SourceMarkedSuffixAveraging.suffixD u :=
      (by norm_num : (0 : ℝ) ≤ 1).trans
        (Shao.Probability.SourceMarkedSuffixAveraging.suffix_normalized_geometry u).2.2.2.2.2.1.1
    have hPi : Shao.Probability.SourceIIDGaussianProfileBudget.gaussianProfiles x {s} w u ≤ 1 := by
      unfold Shao.Probability.SourceIIDGaussianProfileBudget.gaussianProfiles
      split_ifs with hT
      · simp only [Finset.sum_singleton]
        exact Real.exp_le_one_iff.2
          (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) hT.le)
      · norm_num
    change Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {s} false w u ≤
      W (n - r.val) u
    unfold Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight
    split_ifs with hact
    · have hT : 0 < Shao.energy u ∧ h0 ≤ Shao.energy u := ⟨hact.1, hact.2.1⟩
      have hden : (Real.sqrt (Shao.energy u)) ^ 3 =
          Shao.energy u * Real.sqrt (Shao.energy u) := by
        calc
          _ = (Real.sqrt (Shao.energy u)) ^ 2 * Real.sqrt (Shao.energy u) := by ring
          _ = _ := by rw [Real.sq_sqrt hT.1.le]
      rw [W, if_pos hT, hden]
      exact mul_le_of_le_one_right (by positivity) hPi
    · exact hWnn _ _
  let reorder : Shao.Path n × LabelPerm n → Shao.Path n :=
    fun p => Shao.Probability.Spitzer.reorder p.1 p.2
  have hReorderM : Measurable reorder := by
    apply measurable_from_prod_countable_left
    intro sigma
    exact Measurable.of_eval fun i => measurable_pi_apply (sigma i)
  have hMap : Measure.map reorder (revealLaw P) = P := by
    have hInd : iIndepFun (fun i : Fin n => Function.eval i) P :=
      iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)
    have hLaw (i : Fin n) : IdentDistrib (Function.eval i) (id : ℝ → ℝ) P rho :=
      ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable,
        by simp only [Measure.map_id]
           exact (measurePreserving_eval (μ := fun _ : Fin n => rho) i).map_eq⟩
    exact iid_randomPermutation_map_eq_pi P rho (fun i : Fin n => Function.eval i)
      (fun i => measurable_pi_apply i) hInd hLaw
  have hReorderMP : MeasurePreserving reorder (revealLaw P) P := ⟨hReorderM, hMap⟩
  have hEnergyReorder (p : Shao.Path n × LabelPerm n) :
      Shao.energy (reorder p) = Shao.energy p.1 := by
    simpa only [Shao.energy, reorder, Shao.Probability.Spitzer.reorder] using
      Equiv.sum_comp p.2 (fun i => (p.1 i) ^ 2)
  have hHitNec (r : Fin n) (p : Shao.Path n × LabelPerm n)
      (hOpp : actualOppositePrefixHit s p.1 x r.val p.2)
      (hHigh : (9 / 10 : ℝ) * (n : ℝ) ≤ Shao.energy (reorder p)) :
      head r (reorder p) ∈ Hit r := by
    obtain ⟨k, hk0, hk⟩ := hOpp
    refine ⟨k, hk0, ?_⟩
    rw [show Shao.prefixSum (head r (reorder p)) k.val =
        Shao.prefixSum (reorder p) k.val from
      Shao.Probability.Spitzer.head_prefixSum (reorder p) r.val r.is_lt.le k.val (by omega)]
    have hWall : x * Real.sqrt ((9 / 10 : ℝ) * (n : ℝ)) ≤ actualWall p.1 x := by
      change x * Real.sqrt ((9 / 10 : ℝ) * (n : ℝ)) ≤ x * Real.sqrt (Shao.energy p.1)
      rw [← hEnergyReorder p]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hHigh) hx0.le
    change s * Shao.prefixSum (reorder p) k.val ≤ -actualWall p.1 x at hk
    change s * Shao.prefixSum (reorder p) k.val ≤ -x * Real.sqrt ((9 / 10 : ℝ) * (n : ℝ))
    nlinarith only [hk, hWall]
  let G : Shao.Path n → ℝ := fun v => ∑ r ∈ er, Hi r v + Lo r v
  have hGm : Measurable G := Finset.measurable_sum _ fun r _ => (hHi r).1.add (hLo r).1
  have hGi : Integrable G P := integrable_finsetSum _ fun r _ => (hHi r).2.1.add (hLo r).2.1
  have hG0 (v : Shao.Path n) : 0 ≤ G v :=
    Finset.sum_nonneg fun r _ => add_nonneg ((hHi r).2.2.1 v) ((hLo r).2.2 v)
  have hCompare (p : Shao.Path n × LabelPerm n) : bill p ≤ 8000100 * G (reorder p) := by
    change (∑ r : Fin n, if 2 * r.val < n ∧ actualOppositePrefixHit s p.1 x r.val p.2 then
      actualPostwallRetainedRank Q s p.1 x (nu p.1) r p.2 else 0) ≤ _
    rw [show G (reorder p) = ∑ r : Fin n,
      if 2 * r.val < n then Hi r (reorder p) + Lo r (reorder p) else 0 by
        dsimp only [G, er]
        rw [Finset.sum_filter]]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    by_cases hearly : 2 * r.val < n
    · rw [if_pos hearly]
      by_cases hopp : actualOppositePrefixHit s p.1 x r.val p.2
      · rw [if_pos ⟨hearly, hopp⟩]
        have hphys := (apw_actual_postwall_physical_carrier PB Bm hBm p.1 h0 x hh0 hx0
          (nu p.1) p.2 (hcap p.1 p.2) r s hs).2
        apply hphys.trans
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8000100)
        have hGau := hGaussianLe r (reorder p)
        by_cases hHigh : (9 / 10 : ℝ) * (n : ℝ) ≤ Shao.energy (reorder p)
        · have hhit := hHitNec r p hopp hHigh
          have hlo : ¬ Shao.energy (reorder p) < (9 / 10 : ℝ) * (n : ℝ) := not_lt_of_ge hHigh
          simpa only [Hi, Lo, Set.indicator_of_mem hhit, Set.indicator_of_notMem hlo,
            one_mul, add_zero] using hGau
        · have hlo : Shao.energy (reorder p) < (9 / 10 : ℝ) * (n : ℝ) := lt_of_not_ge hHigh
          calc
            _ ≤ W (n - r.val) (tail r (reorder p)) := hGau
            _ ≤ Hi r (reorder p) + Lo r (reorder p) := by
              rw [Lo, Set.indicator_of_mem hlo]
              exact le_add_of_nonneg_left ((hHi r).2.2.1 _)
      · rw [if_neg (by tauto)]
        exact mul_nonneg (by norm_num) (add_nonneg ((hHi r).2.2.1 _) ((hLo r).2.2 _))
    · rw [if_neg (by tauto), if_neg hearly, mul_zero]
  have hPullI : Integrable (fun p => 8000100 * G (reorder p)) (revealLaw P) :=
    (hReorderMP.integrable_comp_of_integrable hGi).const_mul _
  have hGIntegral : (∫ p, G (reorder p) ∂revealLaw P) = ∫ v, G v ∂P := by
    have he := integral_map (μ := revealLaw P) (φ := reorder) (f := G)
      hReorderM.aemeasurable hGm.aestronglyMeasurable
    rw [hMap] at he
    exact he.symm
  calc
    (∫ p, bill p ∂revealLaw P) ≤ ∫ p, 8000100 * G (reorder p) ∂revealLaw P :=
      integral_mono hActual.2.1 hPullI hCompare
    _ = 8000100 * ∫ v, G v ∂P := by rw [integral_const_mul, hGIntegral]
    _ = 8000100 * ((∑ r ∈ er, ∫ v, Hi r v ∂P) + (∑ r ∈ er, ∫ v, Lo r v ∂P)) := by
      dsimp only [G]
      rw [integral_finsetSum _ (fun r _ => (hHi r).2.1.add (hLo r).2.1)]
      simp_rw [integral_add (hHi _).2.1 (hLo _).2.1]
      rw [Finset.sum_add_distrib]
    _ ≤ 8000100 * (CH * CG * delta * Real.exp (-(89 / 100 : ℝ) * x ^ 2) +
        CL * delta * Real.exp (-(89 / 100 : ℝ) * x ^ 2)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hHighSum hLowSum) (by norm_num)
    _ ≤ C * delta * Real.exp (-(89 / 100 : ℝ) * x ^ 2) := by
      dsimp only [C]
      have hh : 0 ≤ delta * Real.exp (-(89 / 100 : ℝ) * x ^ 2) := by positivity
      nlinarith only [hh]

theorem iid_actual_late_regular_postwall_retained_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ΩB : Type*} [MeasurableSpace ΩB]
        (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (Bm : ℝ≥0 → ΩB → ℝ), IsBrownianReal Bm PB →
        let Q : Measure BridgeNoise := bridgeLaw Bm PB
        ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
          (Bcap : ℝ), 0 < Bcap → (∀ᵐ z : ℝ ∂rho, |z| ≤ Bcap) →
          (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
          ∀ (n : ℕ), 0 < n → ∀ (x : ℝ), 16 ≤ x →
            Bcap ≤ Real.sqrt (n : ℝ) / (200 * x) →
            let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
            let delta : ℝ := beta / Real.sqrt (n : ℝ)
            delta * (1 + x) ^ 3 ≤ Real.exp (-3 * x ^ 2) →
            let h0 : ℝ := 4 * beta ^ 2
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
            ∀ (nu : Shao.Path n → LabelPerm n → ℕ),
              (∀ sigma, Measurable (fun a => nu a sigma)) →
              (∀ a sigma, nu a sigma ≤ energyCutoff a h0 sigma) →
              ∀ s : ℝ, (s = 1 ∨ s = -1) →
                let bill := actualLateRegularPostwallRetainedBill Q x s nu
                Measurable bill ∧ Integrable bill (revealLaw P) ∧
                  (∀ p, 0 ≤ bill p) ∧
                  (∫ p, bill p ∂revealLaw P) ≤
                    C * delta * (1 + x) ^ 10 * Real.exp (-(4 / 5 : ℝ) * x ^ 2)
    := by
  classical
  obtain ⟨CG, hCG, hGrids⟩ := apw_ordinary_complete_suffix_grids
  obtain ⟨CR, hCR, hProfile⟩ :=
    Shao.Probability.SourceRegularOppositeWall.actual_signed_opposite_hit_regular_suffix_profile
  have hCR0 : 0 < CR := lt_of_lt_of_le zero_lt_one hCR
  let C : ℝ := (3 * CR + 1024 / 3) * 8000100 * CG + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro ΩB hΩB PB hPB Bm hBm Q rho hProb Bcap hBcap hsupport hmean hsecond
    n hn x hx hscale beta delta hres h0 P nu hnum hnu s hs bill
  letI : IsProbabilityMeasure rho := hProb
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  letI : IsProbabilityMeasure (revealLaw P) := by unfold revealLaw; infer_instance
  have hx0 : 0 < x := by linarith only [hx]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hsn2 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hPow (k : ℕ) : Integrable (fun z : ℝ => |z| ^ k) rho := by
    apply (integrable_const (Bcap ^ k)).mono'
      ((continuous_abs.measurable.pow_const k).aestronglyMeasurable)
    filter_upwards [hsupport] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg z) k)]
    exact pow_le_pow_left₀ (abs_nonneg z) hz k
  have h2 : Integrable (fun z : ℝ => z ^ 2) rho := by
    simpa only [sq_abs] using hPow 2
  have h3 : Integrable (fun z : ℝ => |z| ^ 3) rho := hPow 3
  have hbeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one
      rho h2 h3 hsecond
  have hbeta0 : 0 < beta := lt_of_lt_of_le zero_lt_one hbeta
  have hbeta2 : 0 < beta ^ 2 := sq_pos_of_pos hbeta0
  have hh0 : 0 < h0 := by dsimp [h0]; positivity
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hres1 : delta * (1 + x) ^ 3 ≤ 1 :=
    hres.trans (Real.exp_le_one_iff.2 (by nlinarith only [sq_nonneg x]))
  let Pt : (t : ℕ) → Measure (Shao.Path t) :=
    fun t => Measure.pi (fun _ : Fin t => rho)
  let W : ℕ → (t : ℕ) → Shao.Path t → ℝ := fun q t u =>
    if 0 < Shao.energy u ∧ h0 ≤ Shao.energy u then
      |Shao.Probability.SourceIIDGaussianProfileBudget.firstValue u| ^ 3 /
        (Real.sqrt (Shao.energy u)) ^ q *
          Shao.Probability.SourceMarkedSuffixAveraging.suffixD u ^ 3
    else 0
  rcases hGrids rho h2 h3 hmean hsecond n hn with
    ⟨hW, _hEarlyGrid, hLateOneGrid, hLateThreeGrid⟩
  have hWm (q t : ℕ) (hq : q = 1 ∨ q = 3) : Measurable (W q t) :=
    (hW t q hq).1
  have hWi (q t : ℕ) (hq : q = 1 ∨ q = 3) : Integrable (W q t) (Pt t) :=
    (hW t q hq).2.1
  have hW0 (q t : ℕ) (hq : q = 1 ∨ q = 3) (u : Shao.Path t) : 0 ≤ W q t u :=
    (hW t q hq).2.2 u
  let Fx : ℝ := (1 + x) ^ 10 * Real.exp (-(4 / 5 : ℝ) * x ^ 2)
  have hFx : 0 < Fx := by dsimp [Fx]; positivity
  let ebad : ℝ := Real.exp (-3 * (n : ℝ) / (1024 * beta ^ 2))
  have hebad : 0 < ebad := Real.exp_pos _
  have hebadPay : ebad ≤ (1024 / 3 : ℝ) * delta * Fx := by
    let y : ℝ := 3 * (n : ℝ) / (1024 * beta ^ 2)
    have hy : 0 < y := by dsimp [y]; positivity
    have he : Real.exp y * ebad = 1 := by
      dsimp only [ebad, y]
      rw [← Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
    have hye : y ≤ Real.exp y := by
      linarith only [Real.add_one_le_exp y]
    have hpay2 : ebad ≤ (1024 / 3 : ℝ) * delta ^ 2 := by
      apply (mul_le_mul_left hy).1
      calc
        y * ebad ≤ Real.exp y * ebad := mul_le_mul_of_nonneg_right hye hebad.le
        _ = 1 := he
        _ = y * ((1024 / 3 : ℝ) * delta ^ 2) := by
          dsimp only [y, delta]
          rw [div_pow, hsn2]
          field_simp [hbeta0.ne', hnR.ne']
          <;> ring
    have hpoly3 : 1 ≤ (1 + x) ^ 3 := by
      have hh : 1 ≤ 1 + x := by linarith only [hx0]
      exact one_le_pow₀ hh
    have hdexp : delta ≤ Real.exp (-3 * x ^ 2) :=
      (by nlinarith only [hpoly3, hdelta] : delta ≤ delta * (1 + x) ^ 3).trans hres
    have hdF : delta ≤ Fx := by
      calc
        delta ≤ Real.exp (-3 * x ^ 2) := hdexp
        _ ≤ Real.exp (-(4 / 5 : ℝ) * x ^ 2) :=
          Real.exp_le_exp.mpr (by nlinarith only [sq_nonneg x])
        _ ≤ Fx := by
          have hh : 1 ≤ (1 + x) ^ 10 := one_le_pow₀ (by linarith only [hx0])
          dsimp only [Fx]
          exact (by simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hh (Real.exp_nonneg _))
    calc
      ebad ≤ (1024 / 3 : ℝ) * delta ^ 2 := hpay2
      _ ≤ (1024 / 3 : ℝ) * delta * Fx := by
        have hh := mul_le_mul_of_nonneg_left hdF
          (show 0 ≤ (1024 / 3 : ℝ) * delta by positivity)
        convert hh using 1 <;> ring
  -- Source measurability and genuine L1 precede every integral comparison.
  have hbill : Measurable bill ∧ Integrable bill (revealLaw P) ∧
      (∀ p, 0 ≤ bill p) := (apw_actual_postwall_bill_data PB Bm hBm P x hx0 nu hnum s).2
  -- This is the complete head/tail carrier, with its original first suffix mark.
  let FV : (r t : ℕ) → Shao.Path r × Shao.Path t → ℝ := fun r t p =>
    if |Shao.prefixSum p.2 t| ≤ (3 * x / 2) * Real.sqrt (Shao.energy p.2) ∧
        (∃ k : Fin (r + 1), 0 < k.val ∧
          s * Shao.prefixSum p.1 k.val ≤
            -(x * Real.sqrt (Shao.energy p.1 + Shao.energy p.2))) then
      Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight
        h0 x {s} false p.1 p.2
    else 0
  have hFVData (r t : ℕ) : Measurable (FV r t) ∧
      (∀ p, 0 ≤ FV r t p) ∧
      (∀ p, |FV r t p| ≤ (1 + Real.sqrt (t : ℝ)) ^ 3) := by
    have hd := Shao.Probability.SourceIIDGaussianProfileBudget.fixed_gaussian_weight_measurable_bound
      r t h0 x {s} false
    have hReg : MeasurableSet {p : Shao.Path r × Shao.Path t |
        |Shao.prefixSum p.2 t| ≤ (3 * x / 2) * Real.sqrt (Shao.energy p.2)} :=
      measurableSet_le
        (continuous_abs.measurable.comp ((Shao.measurable_prefixSum t).comp measurable_snd))
        (measurable_const.mul (Shao.measurable_energy.comp measurable_snd).sqrt)
    have hOpp : MeasurableSet {p : Shao.Path r × Shao.Path t |
        ∃ k : Fin (r + 1), 0 < k.val ∧
          s * Shao.prefixSum p.1 k.val ≤
            -(x * Real.sqrt (Shao.energy p.1 + Shao.energy p.2))} := by
      simp only [Set.setOf_exists]
      apply MeasurableSet.iUnion
      intro k
      by_cases hk : 0 < k.val
      · simpa only [hk, true_and] using
          measurableSet_le
            (measurable_const.mul ((Shao.measurable_prefixSum k.val).comp measurable_fst))
            (measurable_const.mul
              ((Shao.measurable_energy.comp measurable_fst).add
                (Shao.measurable_energy.comp measurable_snd)).sqrt).neg
      · simp only [hk, false_and, Set.setOf_false]
        exact MeasurableSet.empty
    refine ⟨Measurable.ite (by simpa only [Set.setOf_and] using hReg.inter hOpp)
      hd.1 measurable_const, ?_, ?_⟩
    · intro p
      dsimp only [FV]
      split_ifs
      · exact (hd.2.1 p.1 p.2).1
      · exact le_rfl
    · intro p
      dsimp only [FV]
      split_ifs
      · simpa only [Finset.card_singleton, Nat.cast_one, one_mul] using
          (hd.2.1 p.1 p.2).2
      · simp only [abs_zero]
        positivity
  have hFVi (r t : ℕ) : Integrable (FV r t) ((Pt r).prod (Pt t)) :=
    (integrable_const ((1 + Real.sqrt (t : ℝ)) ^ 3)).mono'
      (hFVData r t).1.aestronglyMeasurable
      (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using (hFVData r t).2.2 p)
  have hFVsection (r t : ℕ) (u : Shao.Path t) :
      Integrable (fun v => FV r t (v, u)) (Pt r) :=
    (integrable_const ((1 + Real.sqrt (t : ℝ)) ^ 3)).mono'
      ((hFVData r t).1.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (ae_of_all _ fun v => by simpa only [Real.norm_eq_abs] using (hFVData r t).2.2 (v, u))
  have hFixed (r : Fin n) (hlate : n ≤ 2 * r.val) (u : Shao.Path (n - r.val)) :
      (∫ v, FV r.val (n - r.val) (v, u) ∂Pt r.val) ≤
        (3 * CR / (n : ℝ)) * Fx * W 1 (n - r.val) u +
          ebad * W 3 (n - r.val) u := by
    have hr : 0 < r.val := by omega
    have hrR : 0 < (r.val : ℝ) := by exact_mod_cast hr
    have hn2r : (n : ℝ) ≤ 2 * (r.val : ℝ) := by exact_mod_cast hlate
    let t : ℕ := n - r.val
    let Pr : Measure (Shao.Path r.val) := Pt r.val
    let T : ℝ := Shao.energy u
    let b : ℝ := Shao.Probability.SourceIIDGaussianProfileBudget.firstValue u
    let d : ℝ := Shao.prefixSum u t
    let D : ℝ := Shao.Probability.SourceMarkedSuffixAveraging.suffixD u
    let wall : Shao.Path r.val → ℝ := fun v => x * Real.sqrt (Shao.energy v + T)
    let A : Set (Shao.Path r.val) := {v | ∀ k : Fin (r.val + 1),
      0 < k.val → s * Shao.prefixSum v k.val < wall v}
    let G : Set (Shao.Path r.val) := {v | (r.val : ℝ) / 2 ≤ Shao.energy v}
    let O : Set (Shao.Path r.val) := {v | ∃ k : Fin (r.val + 1),
      0 < k.val ∧ s * Shao.prefixSum v k.val ≤ -wall v}
    let M : ℝ := |b| + max (s * d) 0
    let w : Shao.Path r.val → ℝ := fun v => wall v - s * Shao.prefixSum v r.val
    let profile : Shao.Path r.val → ℝ := fun v =>
      Real.exp (-((max (w v - M) 0) ^ 2) / T)
    have hGm : MeasurableSet G := measurableSet_le measurable_const Shao.measurable_energy
    have hGc : MeasurableSet Gᶜ := hGm.compl
    have hbad : (Pr Gᶜ).toReal ≤ ebad := by
      have hh := apw_prefix_energy_lower_tail rho h2 h3 hmean hsecond r.val hr
      have hGeq : Gᶜ = {v : Shao.Path r.val | Shao.energy v < (r.val : ℝ) / 2} := by
        ext v
        simp only [G, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
      rw [hGeq]
      apply hh.trans
      apply Real.exp_le_exp.mpr
      apply (div_le_div_iff₀ (by positivity : 0 < 512 * beta ^ 2)
        (by positivity : 0 < 1024 * beta ^ 2)).2
      nlinarith only [mul_nonneg hbeta2.le (by linarith only [hn2r] : 0 ≤ 2 * (r.val : ℝ) - (n : ℝ))]
    have hD0 : 0 ≤ D := by
      dsimp only [D, Shao.Probability.SourceMarkedSuffixAveraging.suffixD]
      split_ifs <;> positivity
    have hb : b ^ 2 ≤ T := by
      dsimp only [b, Shao.Probability.SourceIIDGaussianProfileBudget.firstValue]
      split_ifs with ht
      · exact Finset.single_le_sum (fun i _ => sq_nonneg (u i))
          (Finset.mem_univ (⟨0, ht⟩ : Fin t))
      · simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using Shao.energy_nonneg u
    by_cases hcut : 0 < T ∧ h0 ≤ T
    · by_cases hReg : |d| ≤ (3 * x / 2) * Real.sqrt T
      · have hT : 0 < T := hcut.1
        have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
        have hsT2 : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hT.le
        let K : ℝ := |b| ^ 3 / (T * Real.sqrt T) * D ^ 3
        have hK : 0 ≤ K := by dsimp only [K]; positivity
        have hW3 : W 3 t u = K := by
          dsimp only [W]
          rw [if_pos hcut]
          dsimp only [K, b, D, T]
          congr 1
          rw [pow_succ, Real.sq_sqrt hT.le]
        have hW1 : W 1 t u = K * T := by
          dsimp only [W]
          rw [if_pos hcut, pow_one]
          dsimp only [K]
          field_simp [hT.ne', hsT.ne']
          <;> ring
        have hPraw := hProfile rho Bcap hBcap hsupport hmean hsecond n hn x hx hscale
          hres1 r.val r.is_lt.le (by linarith only [hn2r]) T b d hT hb
          (by convert hReg using 1 <;> ring) s hs
        have hP : Integrable ((A ∩ G ∩ O).indicator profile) Pr ∧
            (∫ v, (A ∩ G ∩ O).indicator profile v ∂Pr) ≤
              CR * (T + beta ^ 2) / (r.val : ℝ) * Fx := by
          simpa only [Fx, mul_assoc] using hPraw
        have hprofile0 (v : Shao.Path r.val) : 0 ≤ profile v := Real.exp_nonneg _
        have hprofile1 (v : Shao.Path r.val) : profile v ≤ 1 := by
          exact Real.exp_le_one_iff.2
            (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) hT.le)
        have hSurvA (v : Shao.Path r.val)
            (hv : Shao.Probability.SourceIIDGaussianProfileBudget.prefixSurvival
              x {s} false v u) : v ∈ A := by
          have hm : Shao.maxWithZero (s • v) < wall v := by
            simpa [Shao.Probability.SourceIIDGaussianProfileBudget.prefixSurvival,
              wall, T, add_comm] using hv
          intro k _hk
          have hh := (Shao.maxWithZero_le_iff (s • v)
            (Shao.maxWithZero (s • v))).1 le_rfl k.val (by omega)
          rw [Shao.prefixSum_smul] at hh
          exact hh.trans_lt hm
        have hFVeq (v : Shao.Path r.val) (hvO : v ∈ O)
            (hvS : Shao.Probability.SourceIIDGaussianProfileBudget.prefixSurvival
              x {s} false v u) : FV r.val t (v, u) = K * profile v := by
          change (if |d| ≤ (3 * x / 2) * Real.sqrt T ∧ v ∈ O then
            Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight
              h0 x {s} false v u else 0) = K * profile v
          rw [if_pos ⟨hReg, hvO⟩]
          rw [Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight,
            if_pos ⟨hcut.1, hcut.2, hvS⟩]
          simp only [Shao.Probability.SourceIIDGaussianProfileBudget.gaussianProfiles,
            if_pos hcut.1, Finset.sum_singleton]
          change K * Real.exp (-((max (x * Real.sqrt (T + Shao.energy v) -
            s * Shao.prefixSum v r.val - M) 0) ^ 2) / T) = K * profile v
          rw [add_comm T (Shao.energy v)]
        have hFVzero (v : Shao.Path r.val)
            (hv : ¬(v ∈ O ∧ Shao.Probability.SourceIIDGaussianProfileBudget.prefixSurvival
              x {s} false v u)) : FV r.val t (v, u) = 0 := by
          by_cases ho : v ∈ O
          · have hsnot : ¬Shao.Probability.SourceIIDGaussianProfileBudget.prefixSurvival
                x {s} false v u := fun h => hv ⟨ho, h⟩
            change (if |d| ≤ (3 * x / 2) * Real.sqrt T ∧ v ∈ O then
              Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight
                h0 x {s} false v u else 0) = 0
            rw [if_pos ⟨hReg, ho⟩,
              Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight,
              if_neg (by tauto)]
          · exact if_neg (by tauto)
        have hpoint (v : Shao.Path r.val) : FV r.val t (v, u) ≤
            K * (A ∩ G ∩ O).indicator profile v +
              W 3 t u * Gᶜ.indicator (fun _ => (1 : ℝ)) v := by
          by_cases hvg : v ∈ G
          · rw [Set.indicator_of_notMem (show v ∉ Gᶜ from fun hh => hh hvg), mul_zero, add_zero]
            by_cases hv : v ∈ O ∧
                Shao.Probability.SourceIIDGaussianProfileBudget.prefixSurvival x {s} false v u
            · rw [hFVeq v hv.1 hv.2,
                Set.indicator_of_mem (show v ∈ A ∩ G ∩ O from ⟨⟨hSurvA v hv.2, hvg⟩, hv.1⟩)]
            · rw [hFVzero v hv]
              apply mul_nonneg hK
              by_cases hm : v ∈ A ∩ G ∩ O
              · rw [Set.indicator_of_mem hm]
                exact hprofile0 v
              · rw [Set.indicator_of_notMem hm]
          · have hnot : v ∉ A ∩ G ∩ O := fun hh => hvg hh.1.2
            rw [Set.indicator_of_notMem hnot, mul_zero, zero_add,
              Set.indicator_of_mem (show v ∈ Gᶜ from hvg), mul_one, hW3]
            by_cases hv : v ∈ O ∧
                Shao.Probability.SourceIIDGaussianProfileBudget.prefixSurvival x {s} false v u
            · rw [hFVeq v hv.1 hv.2]
              exact (by simpa only [mul_one] using
                mul_le_mul_of_nonneg_left (hprofile1 v) hK)
            · rw [hFVzero v hv]
              exact hK
        have hbadInt : Integrable (Gᶜ.indicator (fun _ => (1 : ℝ))) Pr :=
          (integrable_const 1).indicator hGc
        have hmajorantInt : Integrable
            (fun v => K * (A ∩ G ∩ O).indicator profile v +
              W 3 t u * Gᶜ.indicator (fun _ => (1 : ℝ)) v) Pr :=
          (hP.1.const_mul K).add (hbadInt.const_mul (W 3 t u))
        have hratio : K * ((T + beta ^ 2) / (r.val : ℝ)) ≤
            (3 / (n : ℝ)) * W 1 t u := by
          have hbetaT : 4 * beta ^ 2 ≤ T := hcut.2
          have hc : (T + beta ^ 2) / (r.val : ℝ) ≤ 3 * T / (n : ℝ) := by
            apply (div_le_div_iff₀ hrR hnR).2
            have hmul1 := mul_nonneg hnR.le (sub_nonneg.2 hbetaT)
            have hmul2 := mul_nonneg hT.le (sub_nonneg.2 hn2r)
            have hmul3 := mul_nonneg hrR.le hT.le
            nlinarith only [hmul1, hmul2, hmul3]
          calc
            _ ≤ K * (3 * T / (n : ℝ)) := mul_le_mul_of_nonneg_left hc hK
            _ = _ := by rw [hW1]; ring
        calc
          _ ≤ ∫ v, K * (A ∩ G ∩ O).indicator profile v +
              W 3 t u * Gᶜ.indicator (fun _ => (1 : ℝ)) v ∂Pr :=
            integral_mono (hFVsection r.val t u) hmajorantInt hpoint
          _ = K * (∫ v, (A ∩ G ∩ O).indicator profile v ∂Pr) +
              W 3 t u * (Pr Gᶜ).toReal := by
            rw [integral_add (hP.1.const_mul K) (hbadInt.const_mul (W 3 t u)),
              integral_const_mul, integral_const_mul, integral_indicator_const _ hGc]
            simp only [smul_eq_mul, mul_one]
          _ ≤ K * (CR * (T + beta ^ 2) / (r.val : ℝ) * Fx) +
              W 3 t u * ebad :=
            add_le_add (mul_le_mul_of_nonneg_left hP.2 hK)
              (mul_le_mul_of_nonneg_left hbad (hW0 3 t (Or.inr rfl) u))
          _ ≤ (3 * CR / (n : ℝ)) * Fx * W 1 t u + ebad * W 3 t u := by
            have hh := mul_le_mul_of_nonneg_left hratio (mul_nonneg hCR0.le hFx.le)
            calc
              _ = (CR * Fx) * (K * ((T + beta ^ 2) / (r.val : ℝ))) +
                  ebad * W 3 t u := by ring
              _ ≤ (CR * Fx) * ((3 / (n : ℝ)) * W 1 t u) + ebad * W 3 t u :=
                add_le_add hh le_rfl
              _ = _ := by ring
      · have hzero : (fun v : Shao.Path r.val => FV r.val t (v, u)) = fun _ => 0 := by
          funext v
          exact if_neg (by tauto)
        rw [hzero, integral_zero]
        exact add_nonneg
          (mul_nonneg (mul_nonneg (by positivity) hFx.le) (hW0 1 t (Or.inl rfl) u))
          (mul_nonneg hebad.le (hW0 3 t (Or.inr rfl) u))
    · have hzero : (fun v : Shao.Path r.val => FV r.val t (v, u)) = fun _ => 0 := by
        funext v
        dsimp only [FV]
        split_ifs
        · unfold Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight
          exact if_neg (by tauto)
        · rfl
      have hwzero (q : ℕ) : W q t u = 0 := if_neg hcut
      rw [hzero, integral_zero, hwzero 1, hwzero 3]
      simp only [mul_zero, add_zero, le_refl]
  let R : Fin n → Shao.Path n → ℝ := fun r a =>
    if n ≤ 2 * r.val then
      FV r.val (n - r.val)
        (Shao.Probability.Spitzer.head a r.val r.is_lt.le,
          Shao.Probability.Spitzer.tail a r.val r.is_lt.le)
    else 0
  let E1 : ℕ → ℝ := fun t => ∫ u, W 1 t u ∂Pt t
  let E3 : ℕ → ℝ := fun t => ∫ u, W 3 t u ∂Pt t
  have hE1 (t : ℕ) : 0 ≤ E1 t := integral_nonneg (hW0 1 t (Or.inl rfl))
  have hE3 (t : ℕ) : 0 ≤ E3 t := integral_nonneg (hW0 3 t (Or.inr rfl))
  have hRank (r : Fin n) : Measurable (R r) ∧ Integrable (R r) P ∧
      (∀ a, 0 ≤ R r a) ∧
      (∫ a, R r a ∂P) ≤ if n ≤ 2 * r.val then
        (3 * CR / (n : ℝ)) * Fx * E1 (n - r.val) + ebad * E3 (n - r.val) else 0 := by
    let split : Shao.Path n → Shao.Path r.val × Shao.Path (n - r.val) := fun a =>
      (Shao.Probability.Spitzer.head a r.val r.is_lt.le,
        Shao.Probability.Spitzer.tail a r.val r.is_lt.le)
    have hsplit : MeasurePreserving split P ((Pt r.val).prod (Pt (n - r.val))) := by
      let e : Fin r.val ⊕ Fin (n - r.val) ≃ Fin n :=
        finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le r.is_lt.le))
      have h1 := (measurePreserving_piCongrLeft (fun _ : Fin n => rho) e).symm
      have h2 := measurePreserving_sumPiEquivProdPi
        (fun _ : Fin r.val ⊕ Fin (n - r.val) => rho)
      convert h2.comp h1 using 1
      ext a i <;> change a _ = a _ <;> congr 1
    by_cases hlate : n ≤ 2 * r.val
    · have hRm : Measurable (R r) := by
        change Measurable (fun a => if n ≤ 2 * r.val then
          FV r.val (n - r.val) (split a) else 0)
        simp only [if_pos hlate]
        exact (hFVData r.val (n - r.val)).1.comp hsplit.measurable
      have hRi : Integrable (R r) P := by
        change Integrable (fun a => if n ≤ 2 * r.val then
          FV r.val (n - r.val) (split a) else 0) P
        simp only [if_pos hlate]
        exact hsplit.integrable_comp_of_integrable (hFVi r.val (n - r.val))
      refine ⟨hRm, hRi, ?_, ?_⟩
      · intro a
        exact (by simpa only [R, if_pos hlate] using (hFVData r.val (n - r.val)).2.1 (split a))
      · rw [if_pos hlate]
        have heq : (∫ a, R r a ∂P) =
            ∫ u, (∫ v, FV r.val (n - r.val) (v, u) ∂Pt r.val) ∂Pt (n - r.val) := by
          have he := integral_map (μ := P) (φ := split)
            (f := FV r.val (n - r.val)) hsplit.measurable.aemeasurable
            (hFVData r.val (n - r.val)).1.aestronglyMeasurable
          rw [hsplit.map_eq] at he
          change (∫ a, if n ≤ 2 * r.val then FV r.val (n - r.val) (split a) else 0 ∂P) = _
          simp only [if_pos hlate]
          exact he.symm.trans (integral_prod_symm _ (hFVi r.val (n - r.val)))
        rw [heq]
        calc
          _ ≤ ∫ u, (3 * CR / (n : ℝ)) * Fx * W 1 (n - r.val) u +
              ebad * W 3 (n - r.val) u ∂Pt (n - r.val) :=
            integral_mono (hFVi r.val (n - r.val)).integral_prod_right
              (((hWi 1 (n - r.val) (Or.inl rfl)).const_mul ((3 * CR / (n : ℝ)) * Fx)).add
                ((hWi 3 (n - r.val) (Or.inr rfl)).const_mul ebad)) (hFixed r hlate)
          _ = _ := by
            rw [integral_add
              ((hWi 1 (n - r.val) (Or.inl rfl)).const_mul ((3 * CR / (n : ℝ)) * Fx))
              ((hWi 3 (n - r.val) (Or.inr rfl)).const_mul ebad),
              integral_const_mul, integral_const_mul]
    · have hzero : R r = fun _ => 0 := by funext a; exact if_neg hlate
      rw [hzero, if_neg hlate]
      exact ⟨measurable_const, integrable_const _, fun _ => le_rfl, by simp⟩
  let G : Shao.Path n → ℝ := fun a => ∑ r : Fin n, R r a
  have hGm : Measurable G := Finset.measurable_sum _ fun r _ => (hRank r).1
  have hGi : Integrable G P := integrable_finsetSum _ fun r _ => (hRank r).2.1
  have hperm (a : Shao.Path n) (sigma : LabelPerm n) :
      Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) n = Shao.prefixSum a n ∧
      Shao.energy (Shao.Probability.Spitzer.reorder a sigma) = Shao.energy a := by
    constructor
    · simpa only [Shao.prefixSum_length, Shao.Probability.Spitzer.reorder] using Equiv.sum_comp sigma a
    · exact Equiv.sum_comp sigma (fun i => a i ^ 2)
  -- The arbitrary measurable cap is removed at each point, before transporting iid law.
  have hdom (p : Shao.Path n × LabelPerm n) : bill p ≤ 8000100 * G (randomReorder p) := by
    change (∑ r : Fin n, if n ≤ 2 * r.val ∧
      |remainingSum p.1 r.val p.2| ≤ (3 * x / 2) * Real.sqrt (remainingEnergy p.1 r.val p.2) ∧
      actualOppositePrefixHit s p.1 x r.val p.2 then
        actualPostwallRetainedRank Q s p.1 x (nu p.1) r p.2 else 0) ≤ _
    rw [show G (randomReorder p) = ∑ r : Fin n, R r (randomReorder p) from rfl, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    by_cases hc : n ≤ 2 * r.val ∧
        |remainingSum p.1 r.val p.2| ≤ (3 * x / 2) * Real.sqrt (remainingEnergy p.1 r.val p.2) ∧
        actualOppositePrefixHit s p.1 x r.val p.2
    · rw [if_pos hc]
      let a : Shao.Path n := randomReorder p
      let v : Shao.Path r.val := Shao.Probability.Spitzer.head a r.val r.is_lt.le
      let u : Shao.Path (n - r.val) := Shao.Probability.Spitzer.tail a r.val r.is_lt.le
      have hstate := Shao.Probability.SourceIIDGaussianProfileBudget.gaussian_weight_source_state a r h0 x {s} false
      have hT : Shao.energy u = remainingEnergy p.1 r.val p.2 := by
        calc
          Shao.energy u = Shao.energy a - Shao.prefixSquares a r.val := hstate.1
          _ = _ := by change Shao.energy a - _ = Shao.energy p.1 - _; rw [(hperm p.1 p.2).2]
      have hd : Shao.prefixSum u (n - r.val) = remainingSum p.1 r.val p.2 := by
        calc
          _ = Shao.prefixSum a n - Shao.prefixSum a r.val := hstate.2.1
          _ = _ := by change Shao.prefixSum a n - _ = Shao.prefixSum p.1 n - _; rw [(hperm p.1 p.2).1]
      have henergy : Shao.energy v + Shao.energy u = Shao.energy p.1 := by
        calc
          _ = Shao.energy u + Shao.energy v := add_comm _ _
          _ = Shao.energy a := hstate.2.2.1
          _ = Shao.energy p.1 := (hperm p.1 p.2).2
      have ho : ∃ k : Fin (r.val + 1), 0 < k.val ∧
          s * Shao.prefixSum v k.val ≤ -(x * Real.sqrt (Shao.energy v + Shao.energy u)) := by
        rcases hc.2.2 with ⟨k, hk, hh⟩
        refine ⟨k, hk, ?_⟩
        rw [henergy, Shao.Probability.Spitzer.head_prefixSum a r.val r.is_lt.le k.val (by omega)]
        simpa only [actualWall, neg_mul] using hh
      have hreg : |Shao.prefixSum u (n - r.val)| ≤ (3 * x / 2) * Real.sqrt (Shao.energy u) := by
        rw [hd, hT]
        exact hc.2.1
      have heq : R r a = Shao.Probability.SourceIIDGaussianProfileBudget.rankGaussianWeight h0 x {s} false a r := by
        dsimp only [R]
        rw [if_pos hc.1]
        change (if |Shao.prefixSum u (n - r.val)| ≤ (3 * x / 2) * Real.sqrt (Shao.energy u) ∧
          (∃ k : Fin (r.val + 1), 0 < k.val ∧
            s * Shao.prefixSum v k.val ≤ -(x * Real.sqrt (Shao.energy v + Shao.energy u))) then
          Shao.Probability.SourceIIDGaussianProfileBudget.fixedGaussianWeight h0 x {s} false v u else 0) = _
        rw [if_pos ⟨hreg, ho⟩]
        rfl
      rw [heq]
      exact (apw_actual_postwall_physical_carrier PB Bm hBm p.1 h0 x hh0 hx0
        (nu p.1) p.2 (hnu p.1 p.2) r s hs).2
    · rw [if_neg hc]
      exact mul_nonneg (by norm_num) ((hRank r).2.2.1 (randomReorder p))
  have hRm : Measurable (randomReorder : Shao.Path n × LabelPerm n → Shao.Path n) :=
    measurable_from_prod_countable_left (fun sigma =>
      Measurable.of_eval fun i => measurable_pi_apply (sigma i))
  have hmap : Measure.map randomReorder (revealLaw P) = P := by
    have hInd : iIndepFun (fun i : Fin n => Function.eval i) P :=
      iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)
    have hLaw (i : Fin n) : IdentDistrib (Function.eval i) (id : ℝ → ℝ) P rho :=
      ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable,
        by simp only [Measure.map_id]
           exact (measurePreserving_eval (μ := fun _ : Fin n => rho) i).map_eq⟩
    exact iid_randomPermutation_map_eq_pi P rho (fun i : Fin n => Function.eval i)
      (fun i => measurable_pi_apply i) hInd hLaw
  have hmp : MeasurePreserving randomReorder (revealLaw P) P := ⟨hRm, hmap⟩
  have hreduce : (∫ p, bill p ∂revealLaw P) ≤ 8000100 * ∫ a, G a ∂P := by
    calc
      _ ≤ ∫ p, 8000100 * G (randomReorder p) ∂revealLaw P :=
        integral_mono hbill.2.1 ((hmp.integrable_comp_of_integrable hGi).const_mul 8000100) hdom
      _ = 8000100 * ∫ p, G (randomReorder p) ∂revealLaw P := integral_const_mul _ _
      _ = _ := by
        have hi := integral_map (μ := revealLaw P) hRm.aemeasurable hGm.aestronglyMeasurable
        rw [hmap] at hi
        exact congrArg (fun z : ℝ => 8000100 * z) hi.symm
  have hgrid (E : ℕ → ℝ) (hE : ∀ t, 0 ≤ E t) :
      (∑ r : Fin n, if n ≤ 2 * r.val then E (n - r.val) else 0) ≤
        ∑ t ∈ Finset.Icc 1 (n / 2), E t := by
    have hinj : Function.Injective (fun r : Fin n => n - r.val) := by
      intro a b hh
      apply Fin.ext
      have ha := a.is_lt
      have hb := b.is_lt
      omega
    have hsub : ((Finset.univ.filter (fun r : Fin n => n ≤ 2 * r.val)).image
        (fun r => n - r.val)) ⊆ Finset.Icc 1 (n / 2) := by
      intro t ht
      rcases Finset.mem_image.mp ht with ⟨r, hr, rfl⟩
      have hh := (Finset.mem_filter.mp hr).2
      have hrn := r.is_lt
      simp only [Finset.mem_Icc]
      omega
    rw [← Finset.sum_filter]
    calc
      _ = ∑ t ∈ (Finset.univ.filter (fun r : Fin n => n ≤ 2 * r.val)).image
          (fun r => n - r.val), E t := by
        rw [Finset.sum_image]
        exact fun a _ b _ hh => hinj hh
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => hE t)
  have hsum : (∫ a, G a ∂P) ≤
      (3 * CR) * Fx * ((1 / (n : ℝ)) * ∑ t ∈ Finset.Icc 1 (n / 2), E1 t) +
        ebad * (∑ t ∈ Finset.Icc 1 (n / 2), E3 t) := by
    change (∫ a, ∑ r : Fin n, R r a ∂P) ≤ _
    rw [integral_finsetSum _ (fun r _ => (hRank r).2.1)]
    calc
      _ ≤ ∑ r : Fin n, if n ≤ 2 * r.val then
          (3 * CR / (n : ℝ)) * Fx * E1 (n - r.val) + ebad * E3 (n - r.val) else 0 :=
        Finset.sum_le_sum fun r _ => (hRank r).2.2.2
      _ = ((3 * CR / (n : ℝ)) * Fx) *
            (∑ r : Fin n, if n ≤ 2 * r.val then E1 (n - r.val) else 0) +
          ebad * (∑ r : Fin n, if n ≤ 2 * r.val then E3 (n - r.val) else 0) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r _
        by_cases hh : n ≤ 2 * r.val <;> simp only [hh, if_true, if_false, mul_zero, add_zero]
      _ ≤ ((3 * CR / (n : ℝ)) * Fx) * (∑ t ∈ Finset.Icc 1 (n / 2), E1 t) +
          ebad * (∑ t ∈ Finset.Icc 1 (n / 2), E3 t) :=
        add_le_add (mul_le_mul_of_nonneg_left (hgrid E1 hE1) (by positivity))
          (mul_le_mul_of_nonneg_left (hgrid E3 hE3) hebad.le)
      _ = _ := by ring
  have hpay1 : (1 / (n : ℝ)) * (∑ t ∈ Finset.Icc 1 (n / 2), E1 t) ≤ CG * delta :=
    hLateOneGrid
  have hpay3 : (∑ t ∈ Finset.Icc 1 (n / 2), E3 t) ≤ CG := hLateThreeGrid
  refine ⟨hbill.1, hbill.2.1, hbill.2.2, ?_⟩
  have hFinal : (∫ p, bill p ∂revealLaw P) ≤ C * delta * Fx := by
    calc
      _ ≤ 8000100 * ∫ a, G a ∂P := hreduce
      _ ≤ 8000100 *
          ((3 * CR) * Fx * ((1 / (n : ℝ)) * ∑ t ∈ Finset.Icc 1 (n / 2), E1 t) +
            ebad * (∑ t ∈ Finset.Icc 1 (n / 2), E3 t)) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ ≤ 8000100 * ((3 * CR) * Fx * (CG * delta) + ebad * CG) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8000100)
        exact add_le_add (mul_le_mul_of_nonneg_left hpay1 (by positivity))
          (mul_le_mul_of_nonneg_left hpay3 hebad.le)
      _ ≤ 8000100 * ((3 * CR) * Fx * (CG * delta) +
          ((1024 / 3 : ℝ) * delta * Fx) * CG) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8000100)
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hebadPay hCG.le)
      _ = ((3 * CR + 1024 / 3) * 8000100 * CG) * delta * Fx := by ring
      _ ≤ C * delta * Fx := by
        have hh := mul_le_mul_of_nonneg_right
          (show (3 * CR + 1024 / 3) * 8000100 * CG ≤ C by dsimp only [C]; linarith)
          (mul_nonneg hdelta.le hFx.le)
        convert hh using 1 <;> ring
  simpa only [Fx, mul_assoc] using hFinal

end Shao.C2.ActualPostwallRetainedBudgets
