/- Actual iid Bennett maximum and closed true-energy record strips. Source: supplement.tex 5353-5430. This candidate consumes only the separately qualified cyclic-identity interface from SourceWeightedRecordStrip. No full signed-overshoot or C2 root completion is asserted. -/
import Shao.Probability.SourceWeightedRecordStrip
import Shao.Probability.SourceTrueEnergyStrip
import Shao.Probability.FiniteIIDMoments

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
noncomputable section
namespace Shao.Probability.SourceActualRecordEndstrip
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

private theorem ers_iid_bennett_maximal_tail
    (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (Bcap : ℝ) (hBcap : 0 < Bcap)
    (hsupport : ∀ᵐ z : ℝ ∂rho, |z| ≤ Bcap)
    (hmean : (∫ z : ℝ, z ∂rho) = 0)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂rho) = 1)
    (N : ℕ) (hN : 0 < N) (h : ℝ) (hh : 0 ≤ h) :
    let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => rho)
    let H : Set (Shao.Path N) := {a | h ≤ Shao.maxWithZero a}
    MeasurableSet H ∧
      P.real H ≤ Real.exp (-(h / (2 * Bcap)) *
        Real.log (1 + Bcap * h / (N : ℝ))) := by
  classical
  intro P H
  have hHm : MeasurableSet H :=
    measurableSet_le measurable_const Shao.measurable_maxWithZero
  refine ⟨hHm, ?_⟩
  by_cases hh0 : h = 0
  · simpa only [hh0, zero_div, neg_zero, zero_mul, Real.exp_zero] using
      (measureReal_le_one (μ := P) (s := H))
  have hhp : 0 < h := lt_of_le_of_ne hh (Ne.symm hh0)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hBne : Bcap ≠ 0 := ne_of_gt hBcap
  let t : ℝ := Bcap * h / (N : ℝ)
  let lam : ℝ := Real.log (1 + t) / Bcap
  have ht : 0 < t := by dsimp only [t]; positivity
  have hlog : 0 < Real.log (1 + t) := Real.log_pos (by linarith only [ht])
  have hlam : 0 < lam := by dsimp only [lam]; positivity
  have hPower (r : ℕ) : Integrable (fun z : ℝ => |z| ^ r) rho := by
    apply (integrable_const (Bcap ^ r)).mono' (by fun_prop)
    filter_upwards [hsupport] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg z) r)]
    exact pow_le_pow_left₀ (abs_nonneg z) hz r
  have hi : Integrable (fun z : ℝ => z) rho := by
    exact (hPower 1).mono' measurable_id.aestronglyMeasurable
      (ae_of_all rho fun z => by simp only [Real.norm_eq_abs, pow_one, le_refl])
  have h2 : Integrable (fun z : ℝ => z ^ 2) rho := by
    simpa only [sq_abs] using hPower 2
  -- The remainder ratio is monotone on the positive half-line.  This
  -- proves the all-parameter Bennett majorant, without a small-lambda cap.
  have hRemainder (u v : ℝ) (hv : 0 < v) (huv : |u| ≤ v) :
      Real.exp u ≤ 1 + u + ((Real.exp v - 1 - v) / v ^ 2) * u ^ 2 := by
    have hQ (w : ℝ) (hw : 0 ≤ w) : 1 + w + w ^ 2 / 2 ≤ Real.exp w := by
      let f : ℝ → ℝ := fun s => Real.exp s - 1 - s - s ^ 2 / 2
      have hd (s : ℝ) : HasDerivAt f (Real.exp s - 1 - s) s := by
        convert (((Real.hasDerivAt_exp s).sub_const 1).sub (hasDerivAt_id s)).sub
          (((hasDerivAt_id s).pow 2).div_const 2) using 1 <;>
          first | rfl | (dsimp only [id]; ring)
      have hm : MonotoneOn f (Set.Ici 0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
        · exact fun s _ => (hd s).continuousAt.continuousWithinAt
        · exact fun s _ => (hd s).differentiableAt.differentiableWithinAt
        · intro s _
          rw [(hd s).deriv]
          linarith only [Real.add_one_le_exp s]
      have he := hm (by simp) hw hw
      norm_num only [f, Real.exp_zero, zero_pow (by norm_num : 2 ≠ 0),
        zero_div, sub_zero] at he
      linarith only [he]
    have hK : (1 / 2 : ℝ) ≤ (Real.exp v - 1 - v) / v ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hv)).2
      linarith only [hQ v hv.le]
    by_cases hu : u ≤ 0
    · let f : ℝ → ℝ := fun s => 1 + s + s ^ 2 / 2 - Real.exp s
      have hd (s : ℝ) : HasDerivAt f (1 + s - Real.exp s) s := by
        convert (((hasDerivAt_id s).const_add 1).add
          (((hasDerivAt_id s).pow 2).div_const 2)).sub (Real.hasDerivAt_exp s) using 1 <;>
          first | rfl | (dsimp only [id]; ring)
      have hm : AntitoneOn f (Set.Iic 0) := by
        apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
        · exact fun s _ => (hd s).continuousAt.continuousWithinAt
        · exact fun s _ => (hd s).differentiableAt.differentiableWithinAt
        · intro s _
          rw [(hd s).deriv]
          linarith only [Real.add_one_le_exp s]
      have he := hm hu (by simp) hu
      norm_num only [f, Real.exp_zero, zero_pow (by norm_num : 2 ≠ 0),
        zero_div, add_zero, sub_self] at he
      have hk := mul_le_mul_of_nonneg_right hK (sq_nonneg u)
      linarith only [he, hk]
    · have hup : 0 < u := lt_of_not_ge hu
      have huv' : u ≤ v := (le_abs_self u).trans huv
      let p : ℝ → ℝ := fun s => (s - 1) * Real.exp s + 1
      let q : ℝ → ℝ := fun s => (s - 2) * Real.exp s + s + 2
      have hp (s : ℝ) : HasDerivAt p (s * Real.exp s) s := by
        convert ((((hasDerivAt_id s).sub_const 1).mul
          (Real.hasDerivAt_exp s)).add_const 1) using 1 <;>
          first | rfl | (dsimp only [id]; ring)
      have hpm : MonotoneOn p (Set.Ici 0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
        · exact fun s _ => (hp s).continuousAt.continuousWithinAt
        · exact fun s _ => (hp s).differentiableAt.differentiableWithinAt
        · intro s hs
          rw [(hp s).deriv]
          exact mul_nonneg (interior_subset hs) (Real.exp_pos _).le
      have hp0 (s : ℝ) (hs : 0 ≤ s) : 0 ≤ p s := by
        have he := hpm (by simp) hs hs
        simpa only [p, zero_sub, Real.exp_zero, mul_one, neg_add_cancel] using he
      have hq (s : ℝ) : HasDerivAt q (p s) s := by
        convert (((((hasDerivAt_id s).sub_const 2).mul
          (Real.hasDerivAt_exp s)).add (hasDerivAt_id s)).add_const 2) using 1 <;>
          first | rfl | (dsimp only [id, p]; ring)
      have hqm : MonotoneOn q (Set.Ici 0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
        · exact fun s _ => (hq s).continuousAt.continuousWithinAt
        · exact fun s _ => (hq s).differentiableAt.differentiableWithinAt
        · intro s hs
          rw [(hq s).deriv]
          exact hp0 s (interior_subset hs)
      have hq0 (s : ℝ) (hs : 0 ≤ s) : 0 ≤ q s := by
        have he := hqm (by simp) hs hs
        norm_num only [q, zero_sub, Real.exp_zero, mul_one, add_zero] at he
        exact he
      let g : ℝ → ℝ := fun s => (Real.exp s - 1 - s) / s ^ 2
      have hg (s : ℝ) (hs : 0 < s) : HasDerivAt g (q s / s ^ 3) s := by
        convert ((((Real.hasDerivAt_exp s).sub_const 1).sub
          (hasDerivAt_id s)).div ((hasDerivAt_id s).pow 2) (pow_ne_zero 2 hs.ne')) using 1
        · rfl
        · simp only [q, Pi.pow_apply, Pi.sub_apply, Pi.add_apply, id_eq]
          field_simp [hs.ne']
          <;> ring
      have hgm : MonotoneOn g (Set.Ioi 0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
        · exact fun s hs => (hg s hs).continuousAt.continuousWithinAt
        · exact fun s hs => (hg s (interior_subset hs)).differentiableAt.differentiableWithinAt
        · intro s hs
          have hs0 : 0 < s := interior_subset hs
          rw [(hg s hs0).deriv]
          exact div_nonneg (hq0 s hs0.le) (pow_nonneg hs0.le 3)
      have he := hgm hup hv huv'
      change (Real.exp u - 1 - u) / u ^ 2 ≤
        (Real.exp v - 1 - v) / v ^ 2 at he
      have he' := (div_le_iff₀ (sq_pos_of_pos hup)).1 he
      linarith only [he']
  let c : ℝ := ∫ z : ℝ, Real.exp (lam * z) ∂rho
  have hExpI : Integrable (fun z : ℝ => Real.exp (lam * z)) rho := by
    apply (integrable_const (Real.exp (lam * Bcap))).mono' (by fun_prop)
    filter_upwards [hsupport] with z hz
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
      ((le_abs_self z).trans hz) hlam.le)
  have hc1 : 1 ≤ c := by
    have hlin : Integrable (fun z : ℝ => 1 + lam * z) rho :=
      (integrable_const (1 : ℝ)).add (hi.const_mul lam)
    have he := integral_mono hlin hExpI (fun z => by
      change 1 + lam * z ≤ Real.exp (lam * z)
      linarith only [Real.add_one_le_exp (lam * z)])
    change (∫ z : ℝ, 1 + lam * z ∂rho) ≤ c at he
    rw [integral_add (integrable_const 1) (hi.const_mul lam),
      integral_const_mul, hmean, mul_zero, add_zero] at he
    simpa only [integral_const, probReal_univ, one_smul] using he
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hLog0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  let K : ℝ := (Real.exp (lam * Bcap) - 1 - lam * Bcap) / Bcap ^ 2
  have hcUpper : c ≤ 1 + K := by
    have hlin : Integrable (fun z : ℝ => 1 + lam * z) rho :=
      (integrable_const 1).add (hi.const_mul lam)
    have hmajor : Integrable (fun z : ℝ => 1 + lam * z + K * z ^ 2) rho :=
      hlin.add (h2.const_mul K)
    have hpoint : ∀ᵐ z : ℝ ∂rho,
        Real.exp (lam * z) ≤ 1 + lam * z + K * z ^ 2 := by
      filter_upwards [hsupport] with z hz
      have he := hRemainder (lam * z) (lam * Bcap) (mul_pos hlam hBcap)
        (by rw [abs_mul, abs_of_pos hlam]; exact mul_le_mul_of_nonneg_left hz hlam.le)
      convert he using 1
      dsimp only [K]
      field_simp [hBne, hlam.ne']
      <;> ring
    have he := integral_mono_ae hExpI hmajor hpoint
    rw [integral_add hlin (h2.const_mul K),
      integral_add (integrable_const 1) (hi.const_mul lam), integral_const_mul,
      integral_const_mul, hmean, hsecond] at he
    simpa only [integral_const, probReal_univ, one_smul, mul_zero, add_zero, mul_one] using he
  have hlogUpper : Real.log c ≤ K :=
    (Real.log_le_sub_one_of_pos hc).trans (by linarith only [hcUpper])
  have hRate (s : ℝ) (hs : 0 ≤ s) :
      (s / 2) * Real.log (1 + s) ≤ (1 + s) * Real.log (1 + s) - s := by
    let f : ℝ → ℝ := fun r => (1 + r / 2) * Real.log (1 + r) - r
    have hd (r : ℝ) (hr : 0 ≤ r) :
        HasDerivAt f ((Real.log (1 + r) - r / (1 + r)) / 2) r := by
      have hden : 1 + r ≠ 0 := ne_of_gt (by linarith only [hr])
      convert ((((hasDerivAt_id r).div_const 2).const_add 1).mul
        (((hasDerivAt_id r).const_add 1).log hden)).sub (hasDerivAt_id r) using 1
      · rfl
      · dsimp only [id]
        field_simp [hden]
        <;> ring
    have hm : MonotoneOn f (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact fun r hr => (hd r hr).continuousAt.continuousWithinAt
      · exact fun r hr => (hd r (interior_subset hr)).differentiableAt.differentiableWithinAt
      · intro r hr
        have hr0 : 0 ≤ r := interior_subset hr
        rw [(hd r hr0).deriv]
        have he := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + r by linarith only [hr0])
        have heq : 1 - (1 + r)⁻¹ = r / (1 + r) := by
          field_simp [show 1 + r ≠ 0 by linarith only [hr0]]
          <;> ring
        rw [heq] at he
        exact div_nonneg (sub_nonneg.2 he) (by norm_num)
    have he := hm (by simp) hs hs
    norm_num only [f, zero_div, add_zero, Real.log_one, mul_zero, sub_zero] at he
    linarith only [he]
  run_tac
    let nm : Lean.Name := Lean.mkPrivateNameCore
      ("Shao.Probability.SourceCircularWitnessMoment".toName)
      ("Shao.Probability.SourceCircularWitnessMoment.cwm_canonical_exponential_martingale".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hCanonical".toName)) := $(Lean.mkIdent nm)))
  rcases (hCanonical rho Bcap lam hBcap hsupport).2 N with
    ⟨Filt, hFilt, hMart, hZn, hZi⟩
  let S : ℕ → Finset (Fin N) := fun k => Finset.univ.filter (fun i => i.val < k)
  let Z : ℕ → Shao.Path N → ℝ := fun k a =>
    ∏ i ∈ S k, Real.exp (lam * a i) / c
  have hZexp (k : ℕ) (a : Shao.Path N) :
      Z k a = Real.exp (lam * Shao.prefixSum a k - (S k).card * Real.log c) := by
    calc
      _ = ∏ i ∈ S k, Real.exp (lam * a i - Real.log c) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [Real.exp_sub, Real.exp_log hc]
      _ = Real.exp (∑ i ∈ S k, (lam * a i - Real.log c)) :=
        (Real.exp_sum _ _).symm
      _ = _ := by
        congr 1
        simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
          S, Shao.prefixSum, Finset.mul_sum]
  let e : ℝ := Real.exp (lam * h - (N : ℝ) * Real.log c)
  let U : Shao.Path N → ℝ := fun a =>
    (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one (fun k => Z k a)
  let V : Set (Shao.Path N) := {a | e ≤ U a}
  have he : 0 < e := Real.exp_pos _
  have hZm (k : ℕ) : Continuous (Z k) := by dsimp only [Z]; fun_prop
  have hUm : Continuous U := Continuous.finset_sup'_apply _ (fun k _ => hZm k)
  have hVm : MeasurableSet V := measurableSet_le measurable_const hUm.measurable
  have hsub : H ⊆ V := by
    intro a ha
    change h ≤ (Finset.Icc 0 N).sup' _ (Shao.prefixSum a) at ha
    rw [Finset.le_sup'_iff] at ha
    obtain ⟨k, hk, hhk⟩ := ha
    have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
    have hcard : ((S k).card : ℝ) ≤ N := by
      exact_mod_cast (show (S k).card ≤ N by simpa using Finset.card_le_univ (s := S k))
    have heZ : e ≤ Z k a := by
      rw [hZexp]
      apply Real.exp_le_exp.2
      have h1 := mul_le_mul_of_nonneg_left hhk hlam.le
      have h2' := mul_le_mul_of_nonneg_right hcard hLog0
      linarith only [h1, h2']
    exact heZ.trans (Finset.le_sup' (fun k => Z k a)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hkN)))
  have hsetI : (∫ a in V, Z N a ∂P) ≤ 1 := by
    rw [← (hZi N).2, ← integral_indicator hVm]
    apply integral_mono ((hZi N).1.indicator hVm) (hZi N).1
    intro a
    by_cases ha : a ∈ V
    · rw [Set.indicator_of_mem ha]
    · rw [Set.indicator_of_notMem ha]
      exact hZn N a
  have hsetN : 0 ≤ ∫ a in V, Z N a ∂P := integral_nonneg fun a => hZn N a
  have hDoob := maximal_ineq hMart.submartingale hZn (ε := ⟨e, he.le⟩) N
  have hDoobR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hDoob
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal] at hDoobR
  change e * (P V).toReal ≤ (ENNReal.ofReal (∫ a in V, Z N a ∂P)).toReal at hDoobR
  rw [ENNReal.toReal_ofReal hsetN] at hDoobR
  have hPV : P.real V ≤ 1 / e := by
    apply (le_div_iff₀ he).2
    change (P V).toReal * e ≤ 1
    nlinarith only [hDoobR, hsetI]
  have hTail : P.real H ≤ Real.exp ((N : ℝ) * Real.log c - lam * h) := by
    calc
      _ ≤ P.real V := measureReal_mono hsub
      _ ≤ 1 / e := hPV
      _ = _ := by
        rw [one_div, ← Real.exp_neg]
        congr 1
        ring
  have hlamB : lam * Bcap = Real.log (1 + t) := by
    dsimp only [lam]
    field_simp [hBne]
  have hexp : Real.exp (lam * Bcap) = 1 + t := by
    rw [hlamB, Real.exp_log (show 0 < 1 + t by linarith only [ht])]
  have hScale : (N : ℝ) * t = Bcap * h := by
    dsimp only [t]
    field_simp [hNr.ne']
  have hExponent : (N : ℝ) * Real.log c - lam * h ≤
      -(h / (2 * Bcap)) * Real.log (1 + Bcap * h / (N : ℝ)) := by
    have hmgf := mul_le_mul_of_nonneg_left hlogUpper hNr.le
    have hr := mul_le_mul_of_nonneg_left (hRate t ht.le)
      (show 0 ≤ (N : ℝ) / Bcap ^ 2 by positivity)
    have heq : (N : ℝ) * K - lam * h =
        -((N : ℝ) / Bcap ^ 2) * ((1 + t) * Real.log (1 + t) - t) := by
      dsimp only [K, lam]
      rw [show (Real.log (1 + t) / Bcap) * Bcap = Real.log (1 + t) by
        field_simp [hBne], Real.exp_log (show 0 < 1 + t by linarith only [ht])]
      have hScaleLog := congrArg (fun y : ℝ => y * Real.log (1 + t)) hScale
      field_simp [hBne]
      nlinarith only [hScaleLog]
    have heq2 : -((N : ℝ) / Bcap ^ 2) * ((t / 2) * Real.log (1 + t)) =
        -(h / (2 * Bcap)) * Real.log (1 + t) := by
      dsimp only [t]
      field_simp [hBne, hNr.ne']
      <;> ring
    change (N : ℝ) * Real.log c - lam * h ≤ -(h / (2 * Bcap)) * Real.log (1 + t)
    rw [← heq2]
    linarith only [hmgf, hr, heq]
  exact hTail.trans (Real.exp_le_exp.2 hExponent)

private theorem ers_record_endpoint_moments :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (Bcap : ℝ), 0 < Bcap → (∀ᵐ z : ℝ ∂rho, |z| ≤ Bcap) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ (N : ℕ), 0 < N →
          let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => rho)
          let D : Shao.Path N → ℝ := fun a =>
            max (Shao.prefixSum a N - Shao.maxWithZero
              (Shao.Probability.Spitzer.head a (N - 1) (Nat.sub_le N 1))) 0
          Measurable D ∧
            Integrable (fun a => D a ^ 2 + beta * D a) P ∧
            (∫ a : Shao.Path N, D a ^ 2 + beta * D a ∂P) ≤
              C * beta / Real.sqrt (N : ℝ) ∧
            ∀ h : ℝ, max (8 * Bcap) (Real.sqrt (N : ℝ)) ≤ h →
              let H : Set (Shao.Path N) := {a | h ≤ Shao.prefixSum a N}
              MeasurableSet H ∧
                Integrable (H.indicator (fun a => D a ^ 2 + beta * D a)) P ∧
                (∫ a : Shao.Path N, H.indicator
                  (fun a => D a ^ 2 + beta * D a) a ∂P) ≤
                  C * beta / Real.sqrt (N : ℝ) *
                    Real.exp (-(h / (8 * Bcap)) *
                      Real.log (1 + Bcap * h / (N : ℝ))) := by
  classical
  run_tac
    let mod : Lean.Name := "Shao.Probability.SourceWeightedPrefixWall".toName
    for (src, dst) in
        [("pww_ordinary_closed_lower_survival", "hSurvival"),
         ("pww_fixed_level_hit_before_lower_exit", "hHit")] do
      let nm := Lean.mkPrivateNameCore mod
        (("Shao.Probability.SourceWeightedPrefixWall." ++ src).toName)
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        have $(Lean.mkIdent dst.toName) := $(Lean.mkIdent nm)))
    let mod : Lean.Name := "Shao.Probability.SourceTrueEnergyStrip".toName
    for (src, dst) in
        [("tes_head_tail_measurePreserving", "hSplitMP"),
         ("tes_head_tail_sum", "hSplitSum"),
         ("tes_reverse_prefixSum", "hReverse")] do
      let nm := Lean.mkPrivateNameCore mod (("Shao.Probability." ++ src).toName)
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        have $(Lean.mkIdent dst.toName) := @$(Lean.mkIdent nm)))
    let nm := Lean.mkPrivateNameCore
      ("Shao.Probability.SourceWeightedRecordStrip".toName)
      ("Shao.Probability.SourceWeightedRecordStrip.wrs_cyclic_record_identity".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hCyclic".toName)) := $(Lean.mkIdent nm)))
  obtain ⟨CS, hCS, hOS⟩ := hSurvival
  obtain ⟨CH, hCH, hFH⟩ := hHit
  let C : ℝ := 100 + 16 * CS + 64 * CH
  have hCS0 : 0 ≤ CS := zero_le_one.trans hCS
  have hCH0 : 0 ≤ CH := zero_le_one.trans hCH
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hCS0, hCH0]
  refine ⟨C, hC, ?_⟩
  intro rho hprob Bcap hB hs hmean hsecond beta N hN P D
  let law : (m : ℕ) → Measure (Shao.Path m) := fun m =>
    Measure.pi (fun _ : Fin m => rho)
  let d : (m : ℕ) → Shao.Path m → ℝ := fun m a =>
    max (Shao.prefixSum a m - Shao.maxWithZero
      (Shao.Probability.Spitzer.head a (m - 1) (Nat.sub_le m 1))) 0
  have hPower (r : ℕ) : Integrable (fun z : ℝ => |z| ^ r) rho := by
    apply (integrable_const (Bcap ^ r)).mono' (by fun_prop)
    filter_upwards [hs] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg z) r)]
    exact pow_le_pow_left₀ (abs_nonneg z) hz r
  have h2 : Integrable (fun z : ℝ => z ^ 2) rho := by
    simpa only [sq_abs] using hPower 2
  have hLp : MemLp (id : ℝ → ℝ) 2 rho :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 h2
  have hbeta1 : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one
      rho h2 (hPower 3) hsecond
  have hbeta0 : 0 ≤ beta := zero_le_one.trans hbeta1
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNr
  have hSupport (m : ℕ) : ∀ᵐ a : Shao.Path m ∂law m,
      ∀ i : Fin m, |a i| ≤ Bcap := by
    apply ae_all_iff.2
    intro i
    exact (measurePreserving_eval (fun _ : Fin m => rho) i).quasiMeasurePreserving.ae hs
  have hdm (m : ℕ) : Measurable (d m) := by
    have hh : Measurable (fun a : Shao.Path m =>
        Shao.Probability.Spitzer.head a (m - 1) (Nat.sub_le m 1)) :=
      Measurable.of_eval fun i => measurable_pi_apply _
    exact ((Shao.measurable_prefixSum m).sub
      (Shao.measurable_maxWithZero.comp hh)).max measurable_const
  have hd0 (m : ℕ) (a : Shao.Path m) : 0 ≤ d m a := le_max_right _ _
  have hdCap (m : ℕ) : ∀ᵐ a : Shao.Path m ∂law m, d m a ≤ (m : ℝ) * Bcap := by
    filter_upwards [hSupport m] with a ha
    apply max_le
    · have hsum : Shao.prefixSum a m ≤ (m : ℝ) * Bcap := by
        rw [Shao.prefixSum_length]
        calc
          _ ≤ ∑ _ : Fin m, Bcap := Finset.sum_le_sum fun i _ =>
            (le_abs_self _).trans (ha i)
          _ = _ := by simp
      linarith only [hsum, Shao.maxWithZero_nonneg
        (Shao.Probability.Spitzer.head a (m - 1) (Nat.sub_le m 1))]
    · positivity
  have hdInt (m r : ℕ) : Integrable (fun a : Shao.Path m => d m a ^ r) (law m) := by
    apply (integrable_const (((m : ℝ) * Bcap) ^ r)).mono'
      ((hdm m).pow_const r).aestronglyMeasurable
    filter_upwards [hdCap m] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hd0 m a) r)]
    exact pow_le_pow_left₀ (hd0 m a) ha r
  have hDI : Integrable D P := by simpa only [pow_one] using hdInt N 1
  have hD2I : Integrable (fun a => D a ^ 2) P := hdInt N 2
  have hInt : Integrable (fun a => D a ^ 2 + beta * D a) P := hD2I.add (hDI.const_mul beta)
  have hS2Lp (m : ℕ) : MemLp (fun a : Shao.Path m => Shao.prefixSum a m) 2 (law m) := by
    simpa only [Shao.prefixSum_length, Function.comp_def, id_eq, law] using
      memLp_finsetSum Finset.univ (fun i _ =>
        hLp.comp_measurePreserving (measurePreserving_eval (fun _ : Fin m => rho) i))
  have hS2 (m : ℕ) : (∫ a : Shao.Path m, Shao.prefixSum a m ^ 2 ∂law m) = (m : ℝ) := by
    have hLaw (i : Fin m) : IdentDistrib (fun a : Shao.Path m => a i)
        (id : ℝ → ℝ) (law m) rho :=
      ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable,
        (measurePreserving_eval (fun _ : Fin m => rho) i).map_eq.trans Measure.map_id.symm⟩
    have hh := Shao.Probability.finite_iid_sumSquare_integral
      (fun i : Fin m => measurable_pi_apply i)
      (iIndepFun_pi (fun _ : Fin m => measurable_id.aemeasurable)) hLaw hLp
    simpa only [finiteFeatureSum, Shao.prefixSum_length, hmean, hsecond,
      zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero, mul_one] using hh
  -- Cauchy on this same product law, including the actual closed endpoint mark.
  have hCSmark (H : Set (Shao.Path N)) (hH : MeasurableSet H) :
      (∫ a : Shao.Path N, H.indicator (fun a => max (Shao.prefixSum a N) 0) a ∂P) ≤
        Real.sqrt (N : ℝ) * Real.sqrt (P.real H) := by
    let U : Shao.Path N → ℝ := fun a => |Shao.prefixSum a N|
    let V : Shao.Path N → ℝ := H.indicator (fun _ => 1)
    have hULp : MemLp U 2 P := by
      simpa only [Real.norm_eq_abs] using (hS2Lp N).norm
    have hVLp : MemLp V 2 P := (memLp_const (1 : ℝ)).indicator hH.nullMeasurableSet
    have hUV := integral_mul_le_Lp_mul_Lq_of_nonneg
      (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
        (2 : ℝ).HolderConjugate 2)
      (ae_of_all P fun a => abs_nonneg (Shao.prefixSum a N))
      (ae_of_all P fun a => Set.indicator_nonneg (fun _ _ => zero_le_one) a)
      (show MemLp U (ENNReal.ofReal (2 : ℝ)) P by norm_num; exact hULp)
      (show MemLp V (ENNReal.ofReal (2 : ℝ)) P by norm_num; exact hVLp)
    have hUV' : (∫ a : Shao.Path N, U a * V a ∂P) ≤
        Real.sqrt (∫ a : Shao.Path N, U a ^ 2 ∂P) *
          Real.sqrt (∫ a : Shao.Path N, V a ^ 2 ∂P) := by
      simpa only [Real.rpow_natCast, Real.rpow_ofNat, ← Real.sqrt_eq_rpow] using hUV
    have hU2 : (∫ a : Shao.Path N, U a ^ 2 ∂P) = (N : ℝ) := by
      simpa only [U, sq_abs] using hS2 N
    have hV2 : (∫ a : Shao.Path N, V a ^ 2 ∂P) = P.real H := by
      have heq : (fun a => V a ^ 2) = H.indicator (fun _ => (1 : ℝ)) := by
        funext a
        by_cases ha : a ∈ H <;> simp [V, ha]
      rw [heq]
      simpa only [smul_eq_mul, mul_one] using integral_indicator_const (μ := P) (1 : ℝ) hH
    rw [hU2, hV2] at hUV'
    apply le_trans _ hUV'
    have hMaxI : Integrable (fun a => max (Shao.prefixSum a N) 0) P := by
      apply ((hS2Lp N).integrable (by norm_num)).norm.mono'
        (((Shao.measurable_prefixSum N).max measurable_const).aestronglyMeasurable)
      exact ae_of_all P fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (le_abs_self _) (abs_nonneg _)
    apply integral_mono (hMaxI.indicator hH) (hULp.integrable_mul hVLp)
    intro a
    change H.indicator (fun a => max (Shao.prefixSum a N) 0) a ≤ U a * V a
    by_cases ha : a ∈ H
    · simp only [U, V, Set.indicator_of_mem ha, mul_one]
      exact max_le (le_abs_self _) (abs_nonneg _)
    · simp only [Set.indicator_of_notMem ha, V, mul_zero, le_refl]
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let rot : Fin N → Shao.Path N → Shao.Path N := fun j a i => a (i + j)
  have hRotMP (j : Fin N) : MeasurePreserving (rot j) P P :=
    (measurePreserving_piCongrLeft (fun _ : Fin N => rho) (Equiv.addRight j)).symm
  have hRotSum (j : Fin N) (a : Shao.Path N) :
      Shao.prefixSum (rot j a) N = Shao.prefixSum a N := by
    simp only [Shao.prefixSum_length, rot]
    exact Equiv.sum_comp (Equiv.addRight j) a
  have hMarkedCycle (H : Set (Shao.Path N)) (hH : MeasurableSet H)
      (hInv : ∀ j a, rot j a ∈ H ↔ a ∈ H) :
      (N : ℝ) * (∫ a : Shao.Path N, H.indicator D a ∂P) =
        ∫ a : Shao.Path N, H.indicator (fun a => max (Shao.prefixSum a N) 0) a ∂P := by
    have hRotI (j : Fin N) : Integrable (fun a => (H.indicator D) (rot j a)) P :=
      (hRotMP j).integrable_comp_of_integrable (hDI.indicator hH)
    have hRotVal (j : Fin N) :
        (∫ a : Shao.Path N, (H.indicator D) (rot j a) ∂P) =
          ∫ a : Shao.Path N, H.indicator D a ∂P := by
      have he := integral_map (hRotMP j).aemeasurable
        ((hdm N).indicator hH).aestronglyMeasurable
      rw [(hRotMP j).map_eq] at he
      exact he.symm
    have hPoint (a : Shao.Path N) :
        (∑ j : Fin N, (H.indicator D) (rot j a)) =
          H.indicator (fun a => max (Shao.prefixSum a N) 0) a := by
      have he := (hCyclic N hN a).1
      change (∑ j : Fin N, D (rot j a)) = max (Shao.prefixSum a N) 0 at he
      by_cases ha : a ∈ H
      · rw [Set.indicator_of_mem ha]
        apply le_antisymm
        · rw [← he]
          exact Finset.sum_le_sum fun j _ => by rw [Set.indicator_of_mem ((hInv j a).2 ha)]
        · rw [← he]
          exact Finset.sum_le_sum fun j _ => by rw [Set.indicator_of_mem ((hInv j a).2 ha)]
      · have hr (j : Fin N) : rot j a ∉ H := fun hj => ha ((hInv j a).1 hj)
        simp only [Set.indicator_of_notMem ha, Set.indicator_of_notMem (hr _),
          Finset.sum_const_zero]
    calc
      _ = ∑ j : Fin N, ∫ a : Shao.Path N, (H.indicator D) (rot j a) ∂P := by
        simp only [hRotVal, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ∫ a : Shao.Path N, ∑ j : Fin N, (H.indicator D) (rot j a) ∂P :=
        (integral_finsetSum _ fun j _ => hRotI j).symm
      _ = _ := integral_congr_ae (ae_of_all P hPoint)
  have hFirst : beta * (∫ a : Shao.Path N, D a ∂P) ≤ beta / Real.sqrt (N : ℝ) := by
    have he := hMarkedCycle Set.univ MeasurableSet.univ (by simp)
    simp only [Set.indicator_univ] at he
    have hc := hCSmark Set.univ MeasurableSet.univ
    simp only [Set.indicator_univ, probReal_univ, Real.sqrt_one, mul_one] at hc
    have hdiv : (∫ a : Shao.Path N, D a ∂P) ≤ 1 / Real.sqrt (N : ℝ) := by
      have hdiv' : (∫ a : Shao.Path N, D a ∂P) ≤ Real.sqrt (N : ℝ) / (N : ℝ) := by
        apply (le_div_iff₀ hNr).2
        nlinarith only [he, hc]
      have heq : Real.sqrt (N : ℝ) / (N : ℝ) = 1 / Real.sqrt (N : ℝ) := by
        apply (div_eq_div_iff hNr.ne' hroot.ne').2
        simpa only [one_mul] using Real.mul_self_sqrt hNr.le
      rwa [heq] at hdiv'
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hdiv hbeta0
  have hAliveTail (m : ℕ) (b h : ℝ) (hb : 0 ≤ b)
      (hhB : 8 * Bcap ≤ h) (hhN : Real.sqrt (N : ℝ) ≤ h) (hmN : m ≤ N) :
      let R : Measure (Shao.Path m) := law m
      let Alive : Set (Shao.Path m) :=
        {a | ∀ k : Fin (m + 1), -b ≤ Shao.prefixSum a k.val}
      R.real (Alive ∩ {a | 7 * h / 8 ≤ Shao.prefixSum a m}) ≤
        4 * CH * (b + beta) / h *
          Real.exp (-(h / (4 * Bcap)) * Real.log (1 + Bcap * h / (2 * (N : ℝ)))) := by
    intro R Alive
    have hhp : 0 < h := hroot.trans_le hhN
    let v : ℝ := h / 4
    let T : ℝ := Real.exp (-(h / (4 * Bcap)) *
      Real.log (1 + Bcap * h / (2 * (N : ℝ))))
    have hv : 0 < v := by dsimp only [v]; positivity
    have hT0 : 0 ≤ T := (Real.exp_pos _).le
    let E : Fin (m + 1) → Set (Shao.Path m) := fun k => {a |
      v ≤ Shao.prefixSum a k.val ∧
      (∀ i : Fin (m + 1), i.val < k.val → Shao.prefixSum a i.val < v) ∧
      ∀ i : Fin (m + 1), i.val ≤ k.val → -b ≤ Shao.prefixSum a i.val}
    have hEm (k : Fin (m + 1)) : MeasurableSet (E k) := by
      change MeasurableSet ({a | v ≤ Shao.prefixSum a k.val} ∩
        ({a | ∀ i : Fin (m + 1), i.val < k.val → Shao.prefixSum a i.val < v} ∩
          {a | ∀ i : Fin (m + 1), i.val ≤ k.val → -b ≤ Shao.prefixSum a i.val}))
      refine (measurableSet_le measurable_const (Shao.measurable_prefixSum k.val)).inter ?_
      apply MeasurableSet.inter
      · simp only [Set.setOf_forall]
        exact MeasurableSet.iInter fun i : Fin (m + 1) =>
          MeasurableSet.iInter fun _ : i.val < k.val =>
            measurableSet_lt (Shao.measurable_prefixSum i.val) measurable_const
      · simp only [Set.setOf_forall]
        exact MeasurableSet.iInter fun i : Fin (m + 1) =>
          MeasurableSet.iInter fun _ : i.val ≤ k.val =>
            measurableSet_le measurable_const (Shao.measurable_prefixSum i.val)
    have hDisj (i k : Fin (m + 1)) (hik : i ≠ k) : Disjoint (E i) (E k) := by
      apply Set.disjoint_left.2
      rintro a hi hk
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hik) with hlt | hlt
      · exact (not_lt_of_ge hi.1) (hk.2.1 i hlt)
      · exact (not_lt_of_ge hk.1) (hi.2.1 k hlt)
    have hChoose (a : Shao.Path m) (ha : a ∈ Alive)
        (hend : 7 * h / 8 ≤ Shao.prefixSum a m) : ∃ k : Fin (m + 1), a ∈ E k := by
      have hex : ∃ k : ℕ, k ≤ m ∧ v ≤ Shao.prefixSum a k := by
        refine ⟨m, le_rfl, ?_⟩
        dsimp only [v]
        linarith only [hend, hhp]
      let k := Nat.find hex
      have hk : k ≤ m ∧ v ≤ Shao.prefixSum a k := Nat.find_spec hex
      refine ⟨⟨k, by omega⟩, hk.2, ?_, fun i _ => ha i⟩
      intro i hi
      by_contra hn
      exact Nat.find_min hex hi ⟨by omega, le_of_not_gt hn⟩
    have hSumE : (∑ k : Fin (m + 1), R.real (E k)) ≤ CH * (b + beta) / v := by
      rw [← measureReal_iUnion_fintype hDisj hEm]
      have hsub : (⋃ k : Fin (m + 1), E k) ⊆
          {a : Shao.Path m | ∃ k : Fin (m + 1), 0 < k.val ∧
            v ≤ Shao.prefixSum a k.val ∧
              ∀ i : Fin (m + 1), i.val ≤ k.val → -b ≤ Shao.prefixSum a i.val} := by
        intro a ha
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ha
        have hkp : 0 < k.val := by
          by_contra hn
          have hk0 : k.val = 0 := by omega
          have he := hk.1
          rw [hk0, Shao.prefixSum_zero] at he
          linarith only [he, hv]
        exact ⟨k, hkp, hk.1, hk.2.2⟩
      exact (measureReal_mono hsub).trans (hFH rho Bcap hB hs hmean hsecond m b v hb hv)
    have hFuture (l : ℕ) (hlN : l ≤ N) :
        (law l).real {a | h / 2 ≤ Shao.maxWithZero a} ≤ T := by
      by_cases hl : 0 < l
      · have he := (ers_iid_bennett_maximal_tail rho Bcap hB hs hmean hsecond
          l hl (h / 2) (by positivity)).2
        apply he.trans
        apply Real.exp_le_exp.2
        have hlr : 0 < (l : ℝ) := by exact_mod_cast hl
        have hlNr : (l : ℝ) ≤ (N : ℝ) := by exact_mod_cast hlN
        have hden : Bcap * (h / 2) / (N : ℝ) ≤ Bcap * (h / 2) / (l : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) hlr hlNr
        have hlog : Real.log (1 + Bcap * (h / 2) / (N : ℝ)) ≤
            Real.log (1 + Bcap * (h / 2) / (l : ℝ)) :=
          Real.log_le_log (by positivity) (by linarith only [hden])
        have he' := mul_le_mul_of_nonpos_left hlog
          (neg_nonpos.2 (by positivity : 0 ≤ h / 2 / (2 * Bcap)))
        have hCoeff : h / 2 / (2 * Bcap) = h / (4 * Bcap) := by ring
        have hArg : 1 + Bcap * (h / 2) / (N : ℝ) =
            1 + Bcap * h / (2 * (N : ℝ)) := by ring
        simpa only [hCoeff, hArg] using he'
      · have hl0 : l = 0 := by omega
        subst l
        have hempty : {a : Shao.Path 0 | h / 2 ≤ Shao.maxWithZero a} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.2
          intro a ha
          change h / 2 ≤ Shao.maxWithZero a at ha
          have hm0 : Shao.maxWithZero a ≤ 0 := by
            apply (Shao.maxWithZero_le_iff a 0).2
            intro k hk
            have hk0 : k = 0 := by omega
            simp only [hk0, Shao.prefixSum_zero, le_refl]
          linarith only [ha, hm0, hhp]
        rw [hempty, measureReal_empty]
        exact hT0
    have hSucc (a : Shao.Path m) (k : ℕ) (hk : k < m) :
        Shao.prefixSum a (k + 1) = Shao.prefixSum a k + a ⟨k, hk⟩ := by
      have hset : Finset.univ.filter (fun i : Fin m => i.val < k + 1) =
          insert ⟨k, hk⟩ (Finset.univ.filter (fun i : Fin m => i.val < k)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hi
          by_cases he : i.val = k
          · exact Or.inl (Fin.ext he)
          · exact Or.inr (by omega)
        · rintro (rfl | hi)
          · exact Nat.lt_succ_self _
          · omega
      have hnot : (⟨k, hk⟩ : Fin m) ∉ Finset.univ.filter (fun i : Fin m => i.val < k) := by simp
      dsimp only [Shao.prefixSum]
      rw [hset, Finset.sum_insert hnot]
      ring
    have hEach (k : Fin (m + 1)) :
        R.real (E k ∩ {a | 7 * h / 8 ≤ Shao.prefixSum a m}) ≤ R.real (E k) * T := by
      let K : Shao.Path m → Shao.Path k.val := fun a =>
        Shao.Probability.Spitzer.head a k.val (Nat.le_of_lt_succ k.isLt)
      let L : Shao.Path m → Shao.Path (m - k.val) := fun a =>
        Shao.Probability.Spitzer.tail a k.val (Nat.le_of_lt_succ k.isLt)
      let Pk : Measure (Shao.Path k.val) := law k.val
      let Pl : Measure (Shao.Path (m - k.val)) := law (m - k.val)
      let Pre : Set (Shao.Path k.val) := {a |
        v ≤ Shao.prefixSum a k.val ∧
        (∀ i : Fin (k.val + 1), i.val < k.val → Shao.prefixSum a i.val < v) ∧
        ∀ i : Fin (k.val + 1), i.val ≤ k.val → -b ≤ Shao.prefixSum a i.val}
      let Fut : Set (Shao.Path (m - k.val)) := {a | h / 2 ≤ Shao.maxWithZero a}
      have hPreM : MeasurableSet Pre := by
        change MeasurableSet ({a | v ≤ Shao.prefixSum a k.val} ∩
          ({a | ∀ i : Fin (k.val + 1), i.val < k.val → Shao.prefixSum a i.val < v} ∩
            {a | ∀ i : Fin (k.val + 1), i.val ≤ k.val → -b ≤ Shao.prefixSum a i.val}))
        refine (measurableSet_le measurable_const (Shao.measurable_prefixSum k.val)).inter ?_
        apply MeasurableSet.inter
        · simp only [Set.setOf_forall]
          exact MeasurableSet.iInter fun i : Fin (k.val + 1) =>
            MeasurableSet.iInter fun _ : i.val < k.val =>
              measurableSet_lt (Shao.measurable_prefixSum i.val) measurable_const
        · simp only [Set.setOf_forall]
          exact MeasurableSet.iInter fun i : Fin (k.val + 1) =>
            MeasurableSet.iInter fun _ : i.val ≤ k.val =>
              measurableSet_le measurable_const (Shao.measurable_prefixSum i.val)
      have hFutM : MeasurableSet Fut := measurableSet_le measurable_const Shao.measurable_maxWithZero
      have hMP : MeasurePreserving (fun a => (K a, L a)) R (Pk.prod Pl) :=
        hSplitMP rho m k.val (Nat.le_of_lt_succ k.isLt)
      have hKm : Measurable K := Measurable.of_eval fun i => measurable_pi_apply _
      have hLm : Measurable L := Measurable.of_eval fun i => measurable_pi_apply _
      have hKMP : MeasurePreserving K R Pk := (measurePreserving_fst (μ := Pk) (ν := Pl)).comp hMP
      have hPreEq : K ⁻¹' Pre = E k := by
        ext a
        have hpre (i : ℕ) (hi : i ≤ k.val) :
            Shao.prefixSum (K a) i = Shao.prefixSum a i :=
          Shao.Probability.Spitzer.head_prefixSum _ _ _ _ hi
        change (v ≤ Shao.prefixSum (K a) k.val ∧
          (∀ i : Fin (k.val + 1), i.val < k.val → Shao.prefixSum (K a) i.val < v) ∧
            ∀ i : Fin (k.val + 1), i.val ≤ k.val → -b ≤ Shao.prefixSum (K a) i.val) ↔ _
        rw [hpre k.val le_rfl]
        constructor
        · rintro ⟨h1, h2', h3⟩
          refine ⟨h1, ?_, ?_⟩
          · intro i hi
            have he := h2' ⟨i.val, by omega⟩ hi
            rwa [hpre i.val (by omega)] at he
          · intro i hi
            have he := h3 ⟨i.val, by omega⟩ hi
            rwa [hpre i.val hi] at he
        · rintro ⟨h1, h2', h3⟩
          refine ⟨h1, ?_, ?_⟩
          · intro i hi
            rw [hpre i.val (by omega)]
            exact h2' ⟨i.val, by omega⟩ hi
          · intro i hi
            rw [hpre i.val hi]
            exact h3 ⟨i.val, by omega⟩ hi
      have hPreVal : R.real (E k) = Pk.real Pre := by
        rw [← hPreEq, ← hKMP.map_eq]
        simp only [Measure.real_def, Measure.map_apply hKm hPreM]
      have hProduct : R.real (E k ∩ L ⁻¹' Fut) = R.real (E k) * Pl.real Fut := by
        have hpre : E k ∩ L ⁻¹' Fut = (fun a => (K a, L a)) ⁻¹' (Pre ×ˢ Fut) := by
          rw [← hPreEq]
          rfl
        have he : (Pk.prod Pl) (Pre ×ˢ Fut) =
            R ((fun a => (K a, L a)) ⁻¹' (Pre ×ˢ Fut)) := by
          rw [← hMP.map_eq, Measure.map_apply hMP.measurable (hPreM.prod hFutM)]
        calc
          _ = (Pk.prod Pl).real (Pre ×ˢ Fut) := by
            rw [hpre]
            exact congrArg ENNReal.toReal he.symm
          _ = Pk.real Pre * Pl.real Fut := by
            simp only [Measure.real_def, Measure.prod_prod, ENNReal.toReal_mul]
          _ = _ := by rw [hPreVal]
      have hDom : R (E k ∩ {a | 7 * h / 8 ≤ Shao.prefixSum a m}) ≤
          R (E k ∩ L ⁻¹' Fut) := by
        apply measure_mono_ae
        filter_upwards [hSupport m] with a ha
        rintro ⟨hk, hend⟩
        change 7 * h / 8 ≤ Shao.prefixSum a m at hend
        refine ⟨hk, ?_⟩
        have hkp : 0 < k.val := by
          by_contra hn
          have hk0 : k.val = 0 := by omega
          have he := hk.1
          rw [hk0, Shao.prefixSum_zero] at he
          linarith only [he, hv]
        have hpred := hk.2.1 ⟨k.val - 1, by omega⟩ (by dsimp only; omega)
        have hsucc := hSucc a (k.val - 1) (by omega)
        have hnat : k.val - 1 + 1 = k.val := by omega
        rw [hnat] at hsucc
        have hcoord : a ⟨k.val - 1, by omega⟩ ≤ Bcap :=
          (le_abs_self _).trans (ha _)
        have hUpper : Shao.prefixSum a k.val ≤ h / 4 + Bcap := by
          dsimp only [v] at hpred
          linarith only [hpred, hsucc, hcoord]
        have hTotal : Shao.prefixSum a m =
            Shao.prefixSum a k.val + Shao.prefixSum (L a) (m - k.val) := by
          have he : Shao.prefixSum a m = Shao.prefixSum (K a) k.val +
              Shao.prefixSum (L a) (m - k.val) := by
            simpa only [Shao.prefixSum_length] using
              hSplitSum a k.val (Nat.le_of_lt_succ k.isLt) (fun z => z)
          rw [show Shao.prefixSum (K a) k.val = Shao.prefixSum a k.val from
            Shao.Probability.Spitzer.head_prefixSum _ _ _ _ le_rfl] at he
          exact he
        have hLast : Shao.prefixSum (L a) (m - k.val) ≤ Shao.maxWithZero (L a) :=
          (Shao.maxWithZero_le_iff (L a) _).1 le_rfl _ le_rfl
        change h / 2 ≤ Shao.maxWithZero (L a)
        linarith only [hend, hTotal, hLast, hUpper, hhB]
      calc
        _ ≤ R.real (E k ∩ L ⁻¹' Fut) := ENNReal.toReal_mono (measure_ne_top _ _) hDom
        _ = R.real (E k) * Pl.real Fut := hProduct
        _ ≤ R.real (E k) * T := mul_le_mul_of_nonneg_left
          (hFuture (m - k.val) ((Nat.sub_le _ _).trans hmN)) measureReal_nonneg
    calc
      _ ≤ R.real (⋃ k : Fin (m + 1), E k ∩ {a | 7 * h / 8 ≤ Shao.prefixSum a m}) := by
        apply measureReal_mono (h₂ := measure_ne_top _ _)
        rintro a ⟨ha, hend⟩
        obtain ⟨k, hk⟩ := hChoose a ha hend
        exact Set.mem_iUnion.2 ⟨k, hk, hend⟩
      _ ≤ ∑ k : Fin (m + 1), R.real (E k ∩ {a | 7 * h / 8 ≤ Shao.prefixSum a m}) :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ k : Fin (m + 1), R.real (E k) * T := Finset.sum_le_sum fun k _ => hEach k
      _ = (∑ k : Fin (m + 1), R.real (E k)) * T := (Finset.sum_mul _ _ _).symm
      _ ≤ CH * (b + beta) / v * T := mul_le_mul_of_nonneg_right hSumE hT0
      _ = _ := by dsimp only [v, T]; field_simp <;> ring
  have hLogHalf (s : ℝ) (hs0 : 0 ≤ s) :
      Real.log (1 + s) / 2 ≤ Real.log (1 + s / 2) := by
    have hp : 0 < 1 + s / 2 := by linarith only [hs0]
    have hsq : 1 + s ≤ (1 + s / 2) ^ 2 := by nlinarith only [sq_nonneg s]
    have he := Real.log_le_log (show 0 < 1 + s by linarith only [hs0]) hsq
    rw [Real.log_pow] at he
    linarith only [he]
  have hSecondData :
      (∫ a : Shao.Path N, D a ^ 2 ∂P) ≤ 4 * CS * beta / Real.sqrt (N : ℝ) ∧
        ∀ h : ℝ, max (8 * Bcap) (Real.sqrt (N : ℝ)) ≤ h →
          let H : Set (Shao.Path N) := {a | h ≤ Shao.prefixSum a N}
          (∫ a : Shao.Path N, H.indicator (fun a => D a ^ 2) a ∂P) ≤
            16 * CH * beta / Real.sqrt (N : ℝ) *
              Real.exp (-(h / (8 * Bcap)) * Real.log (1 + Bcap * h / (N : ℝ))) := by
    obtain ⟨m, hmN⟩ : ∃ m : ℕ, N = m + 1 :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
    subst N
    let R : Measure (Shao.Path m) := law m
    let J : ℝ × Shao.Path m → Shao.Path (m + 1) := fun p =>
      Fin.snoc (fun i : Fin m => p.2 (Fin.rev i)) p.1
    have hRevMP : MeasurePreserving (fun a : Shao.Path m => fun i => a (Fin.rev i)) R R :=
      (measurePreserving_piCongrLeft (fun _ : Fin m => rho) Fin.revPerm).symm
    have hSnocMP : MeasurePreserving
        (fun p : ℝ × Shao.Path m => Fin.snoc p.2 p.1) (rho.prod R) P := by
      have heq : (fun p : ℝ × Shao.Path m => Fin.snoc p.2 p.1) =
          (fun p : ℝ × Shao.Path m =>
            (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm p) := by
        funext p
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv_apply, Fin.insertNth_last']
      rw [heq]
      exact (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => rho) (Fin.last m)).symm
    have hJMP : MeasurePreserving J (rho.prod R) P :=
      hSnocMP.comp ((MeasurePreserving.id rho).prod hRevMP)
    have hlastSum (a : Shao.Path (m + 1)) :
        Shao.prefixSum a (m + 1) =
          Shao.prefixSum (Shao.Probability.Spitzer.head a m (by omega)) m + a (Fin.last m) := by
      simp only [Shao.prefixSum_length, Fin.sum_univ_castSucc]
      rfl
    have hJhead (p : ℝ × Shao.Path m) :
        Shao.Probability.Spitzer.head (J p) m (by omega) =
          fun i : Fin m => p.2 (Fin.rev i) := by
      funext i
      simp [J, Shao.Probability.Spitzer.head, Fin.snoc]
    have hJsum (p : ℝ × Shao.Path m) :
        Shao.prefixSum (J p) (m + 1) = Shao.prefixSum p.2 m + p.1 := by
      rw [hlastSum, hJhead]
      have hr := hReverse p.2 m le_rfl
      rw [Nat.sub_self, Shao.prefixSum_zero, sub_zero] at hr
      rw [hr]
      simp only [J, Fin.snoc_last]
    have hDlast (p : ℝ × Shao.Path m) : D (J p) ≤ max p.1 0 := by
      have he := (Shao.maxWithZero_le_iff
        (Shao.Probability.Spitzer.head (J p) m (by omega)) _).1 le_rfl m le_rfl
      have hsum := hlastSum (J p)
      have hlast : J p (Fin.last m) = p.1 := by simp only [J, Fin.snoc_last]
      change max (Shao.prefixSum (J p) (m + 1) -
        Shao.maxWithZero (Shao.Probability.Spitzer.head (J p) m (by omega))) 0 ≤ _
      apply max_le
      · rw [hlast] at hsum
        linarith only [he, hsum, le_max_left p.1 0]
      · exact le_max_right _ _
    let Alive : ℝ → Set (Shao.Path m) := fun b =>
      {a | ∀ k : Fin (m + 1), -max b 0 ≤ Shao.prefixSum a k.val}
    have hAliveM : MeasurableSet {p : ℝ × Shao.Path m | p.2 ∈ Alive p.1} := by
      change MeasurableSet {p : ℝ × Shao.Path m |
        ∀ k : Fin (m + 1), -max p.1 0 ≤ Shao.prefixSum p.2 k.val}
      simp only [Set.setOf_forall]
      exact MeasurableSet.iInter fun k : Fin (m + 1) =>
        measurableSet_le (measurable_fst.max measurable_const).neg
          ((Shao.measurable_prefixSum k.val).comp measurable_snd)
    have hAlive (p : ℝ × Shao.Path m) (hp : 0 < D (J p)) : p.2 ∈ Alive p.1 := by
      have hbefore : Shao.maxWithZero (Shao.Probability.Spitzer.head (J p) m (by omega)) <
          Shao.prefixSum (J p) (m + 1) := by
        by_contra hh
        have hle := le_of_not_gt hh
        change 0 < max (Shao.prefixSum (J p) (m + 1) -
          Shao.maxWithZero (Shao.Probability.Spitzer.head (J p) m (by omega))) 0 at hp
        rw [max_eq_right (sub_nonpos.2 hle)] at hp
        exact (lt_irrefl 0) hp
      intro k
      have hk : k.val ≤ m := Nat.le_of_lt_succ k.isLt
      have he := (Shao.maxWithZero_le_iff
        (Shao.Probability.Spitzer.head (J p) m (by omega)) _).1 le_rfl
          (m - k.val) (Nat.sub_le _ _)
      rw [hJhead, hReverse _ _ (Nat.sub_le _ _)] at he
      have hmk : m - (m - k.val) = k.val := by omega
      rw [hmk] at he
      rw [hJhead, hJsum] at hbefore
      change -max p.1 0 ≤ Shao.prefixSum p.2 k.val
      linarith only [he, hbefore, le_max_left p.1 0]
    have hBPI : Integrable (fun b : ℝ => (max b 0) ^ 2 * (max b 0 + beta)) rho := by
      apply (integrable_const (Bcap ^ 2 * (Bcap + beta))).mono' (by fun_prop)
      filter_upwards [hs] with b hb
      have hbB : max b 0 ≤ Bcap := max_le ((le_abs_self _).trans hb) hB.le
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      gcongr
    have hBP : (∫ b : ℝ, (max b 0) ^ 2 * (max b 0 + beta) ∂rho) ≤ 2 * beta := by
      calc
        _ ≤ ∫ b : ℝ, |b| ^ 3 + beta * b ^ 2 ∂rho := by
          apply integral_mono hBPI ((hPower 3).add (h2.const_mul beta))
          intro b
          change (max b 0) ^ 2 * (max b 0 + beta) ≤ |b| ^ 3 + beta * b ^ 2
          by_cases hb : 0 ≤ b
          · rw [max_eq_left hb, abs_of_nonneg hb]
            ring_nf
            exact le_rfl
          · rw [max_eq_right (le_of_not_ge hb)]
            simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul]
            exact add_nonneg (pow_nonneg (abs_nonneg b) 3) (mul_nonneg hbeta0 (sq_nonneg b))
        _ = _ := by
          rw [integral_add (hPower 3) (h2.const_mul beta), integral_const_mul, hsecond]
          change beta + beta * 1 = 2 * beta
          ring
    have hProdSupport : ∀ᵐ p : ℝ × Shao.Path m ∂rho.prod R, |p.1| ≤ Bcap :=
      (measurePreserving_fst (μ := rho) (ν := R)).quasiMeasurePreserving.ae hs
    -- This generic transfer integrates an explicit deterministic section;
    -- its only input is the displayed pointwise implication, not a law oracle.
    have hTransfer (Mark : Set (Shao.Path (m + 1))) (hMark : MeasurableSet Mark)
        (V : ℝ → Set (Shao.Path m))
        (hVm : MeasurableSet {p : ℝ × Shao.Path m | p.2 ∈ V p.1})
        (hForce : ∀ p : ℝ × Shao.Path m, 0 < D (J p) → J p ∈ Mark → p.2 ∈ V p.1) :
        Integrable (fun b : ℝ => (max b 0) ^ 2 * R.real (V b)) rho ∧
          (∫ a : Shao.Path (m + 1), Mark.indicator (fun a => D a ^ 2) a ∂P) ≤
            ∫ b : ℝ, (max b 0) ^ 2 * R.real (V b) ∂rho := by
      let G : ℝ × Shao.Path m → ℝ := fun p =>
        if p.2 ∈ V p.1 then (max p.1 0) ^ 2 else 0
      have hGm : Measurable G := Measurable.ite hVm
        ((measurable_fst.max measurable_const).pow_const 2) measurable_const
      have hG0 (p : ℝ × Shao.Path m) : 0 ≤ G p := by dsimp only [G]; split_ifs <;> positivity
      have hGI : Integrable G (rho.prod R) := by
        apply (integrable_const (Bcap ^ 2)).mono' hGm.aestronglyMeasurable
        filter_upwards [hProdSupport] with p hp
        rw [Real.norm_eq_abs, abs_of_nonneg (hG0 p)]
        dsimp only [G]
        split_ifs
        · exact pow_le_pow_left₀ (le_max_right _ _)
            (max_le ((le_abs_self _).trans hp) hB.le) 2
        · positivity
      have hPoint (p : ℝ × Shao.Path m) :
          Mark.indicator (fun a => D a ^ 2) (J p) ≤ G p := by
        by_cases hm : J p ∈ Mark
        · rw [Set.indicator_of_mem hm]
          by_cases hd : 0 < D (J p)
          · dsimp only [G]
            rw [if_pos (hForce p hd hm)]
            exact pow_le_pow_left₀ (hd0 _ _) (hDlast p) 2
          · have hz : D (J p) = 0 := le_antisymm (le_of_not_gt hd) (hd0 _ _)
            rw [hz, zero_pow (by norm_num : 2 ≠ 0)]
            exact hG0 p
        · rw [Set.indicator_of_notMem hm]
          exact hG0 p
      have hSection (b : ℝ) : (∫ a : Shao.Path m, G (b, a) ∂R) =
          (max b 0) ^ 2 * R.real (V b) := by
        have hVb : MeasurableSet (V b) := hVm.preimage (measurable_const.prodMk measurable_id)
        change (∫ a : Shao.Path m, (V b).indicator (fun _ => (max b 0) ^ 2) a ∂R) = _
        rw [integral_indicator_const _ hVb]
        simp only [smul_eq_mul, mul_comm]
      have hMap := integral_map hJMP.aemeasurable
        (((hdm (m + 1)).pow_const 2).indicator hMark).aestronglyMeasurable
      rw [hJMP.map_eq] at hMap
      have hQI : Integrable (fun b : ℝ => (max b 0) ^ 2 * R.real (V b)) rho := by
        convert hGI.integral_prod_left using 1
        funext b
        exact (hSection b).symm
      refine ⟨hQI, ?_⟩
      calc
        _ = ∫ p : ℝ × Shao.Path m,
            Mark.indicator (fun a => D a ^ 2) (J p) ∂rho.prod R := hMap
        _ ≤ ∫ p : ℝ × Shao.Path m, G p ∂rho.prod R :=
          integral_mono (hJMP.integrable_comp_of_integrable (hD2I.indicator hMark)) hGI hPoint
        _ = ∫ b : ℝ, ∫ a : Shao.Path m, G (b, a) ∂R ∂rho := integral_prod _ hGI
        _ = _ := integral_congr_ae (ae_of_all rho hSection)
    constructor
    · by_cases hm : 0 < m
      · have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
        have hmrRoot : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmr
        have hT := hTransfer Set.univ MeasurableSet.univ Alive hAliveM
          (fun p hp _ => hAlive p hp)
        simp only [Set.indicator_univ] at hT
        have hSec : ∀ b : ℝ, (max b 0) ^ 2 * R.real (Alive b) ≤
            (CS / Real.sqrt (m : ℝ)) * ((max b 0) ^ 2 * (max b 0 + beta)) := by
          intro b
          have he := hOS rho Bcap hB hs hmean hsecond m hm (max b 0) (le_max_right _ _)
          have he' := mul_le_mul_of_nonneg_left he (sq_nonneg (max b 0))
          convert he' using 1 <;> ring
        have hTotal := hT.2.trans (integral_mono hT.1 (hBPI.const_mul (CS / Real.sqrt (m : ℝ))) hSec)
        rw [integral_const_mul] at hTotal
        have hTotal' := hTotal.trans (mul_le_mul_of_nonneg_left hBP (by positivity : 0 ≤ CS / Real.sqrt (m : ℝ)))
        have hRoots : Real.sqrt ((m + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (m : ℝ) := by
          have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
          have hsq1 := Real.sq_sqrt (show 0 ≤ ((m + 1 : ℕ) : ℝ) by positivity)
          have hsq2 := Real.sq_sqrt hmr.le
          norm_num only [Nat.cast_add, Nat.cast_one] at hsq1 ⊢
          nlinarith only [hsq1, hsq2, hm1,
            Real.sqrt_nonneg ((m : ℝ) + 1), Real.sqrt_nonneg (m : ℝ)]
        have hInv : 1 / Real.sqrt (m : ℝ) ≤ 2 / Real.sqrt ((m + 1 : ℕ) : ℝ) := by
          apply (div_le_div_iff₀ hmrRoot hroot).2
          simpa only [one_mul] using hRoots
        apply hTotal'.trans
        have he := mul_le_mul_of_nonneg_left hInv (show 0 ≤ 2 * CS * beta by positivity)
        convert he using 1 <;> ring
      · have hm0 : m = 0 := by omega
        subst m
        have hDpoint (a : Shao.Path 1) : D a ^ 2 ≤ a 0 ^ 2 := by
          have he := hDlast (a 0, fun i : Fin 0 => Fin.elim0 i)
          have hJ : J (a 0, fun i : Fin 0 => Fin.elim0 i) = a := by
            funext i
            have hi : i = 0 := Fin.ext (by omega)
            subst i
            simp [J, Fin.snoc]
          rw [hJ] at he
          have hDabs : D a ≤ |a 0| := he.trans (max_le (le_abs_self _) (abs_nonneg _))
          simpa only [sq_abs] using pow_le_pow_left₀ (hd0 _ _) hDabs 2
        have hcoordI : Integrable (fun a : Shao.Path 1 => a 0 ^ 2) P :=
          (measurePreserving_eval (fun _ : Fin 1 => rho) 0).integrable_comp_of_integrable h2
        have hcoord : (∫ a : Shao.Path 1, a 0 ^ 2 ∂P) = 1 := by
          have he : (∫ z : ℝ, z ^ 2 ∂P.map (fun a : Shao.Path 1 => a 0)) =
              ∫ a : Shao.Path 1, a 0 ^ 2 ∂P :=
            integral_map (f := fun z : ℝ => z ^ 2)
              (measurePreserving_eval (fun _ : Fin 1 => rho) 0).aemeasurable (by fun_prop)
          rw [(measurePreserving_eval (fun _ : Fin 1 => rho) 0).map_eq] at he
          exact he.symm.trans hsecond
        have he := (integral_mono hD2I hcoordI hDpoint).trans_eq hcoord
        have hprod : (1 : ℝ) ≤ CS * beta := by
          simpa only [one_mul] using
            mul_le_mul hCS hbeta1 (by norm_num : (0 : ℝ) ≤ 1) hCS0
        have hcoeff : (1 : ℝ) ≤ 4 * CS * beta := by nlinarith only [hprod]
        simpa only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add,
          Real.sqrt_one, div_one] using he.trans hcoeff
    · intro h hh H
      have hhB := (le_max_left (8 * Bcap) (Real.sqrt ((m + 1 : ℕ) : ℝ))).trans hh
      have hhN := (le_max_right (8 * Bcap) (Real.sqrt ((m + 1 : ℕ) : ℝ))).trans hh
      have hhp : 0 < h := hroot.trans_le hhN
      let V : ℝ → Set (Shao.Path m) := fun b =>
        Alive b ∩ {a | 7 * h / 8 ≤ Shao.prefixSum a m}
      have hVm : MeasurableSet {p : ℝ × Shao.Path m | p.2 ∈ V p.1} :=
        hAliveM.inter (measurableSet_le measurable_const
          ((Shao.measurable_prefixSum m).comp measurable_snd))
      have hH : MeasurableSet H := measurableSet_le measurable_const (Shao.measurable_prefixSum (m + 1))
      -- Last-increment support is an almost-everywhere input, so retain the
      -- support mark in the transfer instead of pretending it is pointwise.
      let Mark : Set (Shao.Path (m + 1)) := H ∩ {a | |a (Fin.last m)| ≤ Bcap}
      have hMark : MeasurableSet Mark := hH.inter
        (measurableSet_le (measurable_pi_apply (Fin.last m)).norm measurable_const)
      have hMarkAE : Mark =ᵐ[P] H := by
        filter_upwards [hSupport (m + 1)] with a ha
        exact propext ⟨fun hm => hm.1, fun hh => ⟨hh, ha (Fin.last m)⟩⟩
      have hTI := hTransfer Mark hMark V hVm (by
        intro p hp hmark
        refine ⟨hAlive p hp, ?_⟩
        have hend := hmark.1
        have hb : |p.1| ≤ Bcap := by
          have he : |J p (Fin.last m)| ≤ Bcap := hmark.2
          simpa only [J, Fin.snoc_last] using he
        change h ≤ Shao.prefixSum (J p) (m + 1) at hend
        rw [hJsum] at hend
        have hb' : p.1 ≤ Bcap := (le_abs_self _).trans hb
        change 7 * h / 8 ≤ Shao.prefixSum p.2 m
        linarith only [hend, hb', hhB])
      have hLeft : (∫ a : Shao.Path (m + 1), H.indicator (fun a => D a ^ 2) a ∂P) =
          ∫ a : Shao.Path (m + 1), Mark.indicator (fun a => D a ^ 2) a ∂P := by
        apply integral_congr_ae
        filter_upwards [hSupport (m + 1)] with a ha
        by_cases hh : a ∈ H
        · have hm : a ∈ Mark := ⟨hh, ha (Fin.last m)⟩
          rw [Set.indicator_of_mem hh, Set.indicator_of_mem hm]
        · have hm : a ∉ Mark := fun hm => hh hm.1
          rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem hm]
      rw [hLeft]
      let T : ℝ := Real.exp (-(h / (4 * Bcap)) *
        Real.log (1 + Bcap * h / (2 * (((m + 1 : ℕ) : ℝ)))))
      let K : ℝ := 4 * CH / h * T
      have hK0 : 0 ≤ K := by dsimp only [K, T]; positivity
      have hSec (b : ℝ) : (max b 0) ^ 2 * R.real (V b) ≤
          K * ((max b 0) ^ 2 * (max b 0 + beta)) := by
        have he := hAliveTail m (max b 0) h (le_max_right _ _) hhB hhN (by omega)
        change R.real (V b) ≤ 4 * CH * (max b 0 + beta) / h * T at he
        have he' := mul_le_mul_of_nonneg_left he (sq_nonneg (max b 0))
        convert he' using 1 <;> dsimp only [K] <;> ring
      have hTotal := hTI.2.trans (integral_mono hTI.1 (hBPI.const_mul K) hSec)
      rw [integral_const_mul] at hTotal
      have hTotal' := hTotal.trans (mul_le_mul_of_nonneg_left hBP hK0)
      have hLog := hLogHalf (Bcap * h / (((m + 1 : ℕ) : ℝ))) (by positivity)
      have hExponent : -(h / (4 * Bcap)) *
          Real.log (1 + Bcap * h / (2 * (((m + 1 : ℕ) : ℝ)))) ≤
            -(h / (8 * Bcap)) * Real.log (1 + Bcap * h / (((m + 1 : ℕ) : ℝ))) := by
        have he := mul_le_mul_of_nonpos_left hLog
          (neg_nonpos.2 (div_nonneg hhp.le (by positivity : 0 ≤ 4 * Bcap)))
        have hArg : 1 + Bcap * h / (2 * (((m + 1 : ℕ) : ℝ))) =
            1 + (Bcap * h / (((m + 1 : ℕ) : ℝ))) / 2 := by ring
        rw [hArg]
        calc
          _ ≤ -(h / (4 * Bcap)) *
              (Real.log (1 + Bcap * h / (((m + 1 : ℕ) : ℝ))) / 2) := he
          _ = _ := by ring
      have hInv : 1 / h ≤ 1 / Real.sqrt (((m + 1 : ℕ) : ℝ)) :=
        one_div_le_one_div_of_le hroot hhN
      apply hTotal'.trans
      calc
        K * (2 * beta) = 8 * CH * beta * (1 / h) * T := by dsimp only [K]; ring
        _ ≤ 8 * CH * beta * (1 / Real.sqrt (((m + 1 : ℕ) : ℝ))) *
            Real.exp (-(h / (8 * Bcap)) * Real.log (1 + Bcap * h / (((m + 1 : ℕ) : ℝ)))) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hInv (by positivity : 0 ≤ 8 * CH * beta))
            (Real.exp_le_exp.2 hExponent) (Real.exp_pos _).le (by positivity)
        _ ≤ _ := by
          have he : 0 ≤ CH * beta / Real.sqrt (((m + 1 : ℕ) : ℝ)) *
              Real.exp (-(h / (8 * Bcap)) * Real.log (1 + Bcap * h / (((m + 1 : ℕ) : ℝ)))) := by positivity
          have hmul := mul_le_mul_of_nonneg_right (by norm_num : (8 : ℝ) ≤ 16) he
          convert hmul using 1 <;> ring
  refine ⟨hdm N, hInt, ?_, ?_⟩
  · rw [integral_add hD2I (hDI.const_mul beta), integral_const_mul]
    have hc : 4 * CS + 1 ≤ C := by dsimp only [C]; linarith only [hCS0, hCH0]
    have he := add_le_add hSecondData.1 hFirst
    have hm := mul_le_mul_of_nonneg_right hc (show 0 ≤ beta / Real.sqrt (N : ℝ) by positivity)
    calc
      _ ≤ 4 * CS * beta / Real.sqrt (N : ℝ) + beta / Real.sqrt (N : ℝ) := he
      _ = (4 * CS + 1) * (beta / Real.sqrt (N : ℝ)) := by ring
      _ ≤ C * (beta / Real.sqrt (N : ℝ)) := hm
      _ = _ := by ring
  · intro h hh H
    have hhB : 8 * Bcap ≤ h := (le_max_left _ _).trans hh
    have hhN : Real.sqrt (N : ℝ) ≤ h := (le_max_right _ _).trans hh
    have hhp : 0 < h := hroot.trans_le hhN
    have hH : MeasurableSet H := measurableSet_le measurable_const (Shao.measurable_prefixSum N)
    refine ⟨hH, hInt.indicator hH, ?_⟩
    have hInv (j : Fin N) (a : Shao.Path N) : rot j a ∈ H ↔ a ∈ H := by
      change (h ≤ Shao.prefixSum (rot j a) N) ↔ h ≤ Shao.prefixSum a N
      rw [hRotSum]
    have hCycle := hMarkedCycle H hH hInv
    have hCSH := hCSmark H hH
    have hTail := (ers_iid_bennett_maximal_tail rho Bcap hB hs hmean hsecond N hN h hhp.le).2
    have hSub : H ⊆ {a : Shao.Path N | h ≤ Shao.maxWithZero a} := by
      intro a ha
      exact ha.trans ((Shao.maxWithZero_le_iff a _).1 le_rfl N le_rfl)
    have hProb : P.real H ≤ Real.exp (-(h / (2 * Bcap)) * Real.log (1 + Bcap * h / (N : ℝ))) :=
      (measureReal_mono hSub).trans hTail
    have hFirstMarked : beta * (∫ a : Shao.Path N, H.indicator D a ∂P) ≤
        beta / Real.sqrt (N : ℝ) *
          Real.exp (-(h / (8 * Bcap)) * Real.log (1 + Bcap * h / (N : ℝ))) := by
      have hSqrtProb := Real.sqrt_le_sqrt hProb
      have hSqrtExp (r : ℝ) : Real.sqrt (Real.exp r) = Real.exp (r / 2) := by
        have he : Real.exp r = (Real.exp (r / 2)) ^ 2 := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
        rw [he, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [hSqrtExp] at hSqrtProb
      have hLog0 : 0 ≤ Real.log (1 + Bcap * h / (N : ℝ)) :=
        Real.log_nonneg (by
          have hp : 0 ≤ Bcap * h / (N : ℝ) := by positivity
          linarith only [hp])
      have hE : Real.exp ((-(h / (2 * Bcap)) * Real.log (1 + Bcap * h / (N : ℝ))) / 2) ≤
          Real.exp (-(h / (8 * Bcap)) * Real.log (1 + Bcap * h / (N : ℝ))) := by
        apply Real.exp_le_exp.2
        have hp : 0 ≤ h / Bcap * Real.log (1 + Bcap * h / (N : ℝ)) := by positivity
        have he := mul_le_mul_of_nonneg_right (by norm_num : (-1 / 4 : ℝ) ≤ -1 / 8) hp
        convert he using 1 <;> ring
      have hBound := hCSH.trans (mul_le_mul_of_nonneg_left (hSqrtProb.trans hE) hroot.le)
      have hD : (∫ a : Shao.Path N, H.indicator D a ∂P) ≤
          (Real.sqrt (N : ℝ) / (N : ℝ)) *
            Real.exp (-(h / (8 * Bcap)) * Real.log (1 + Bcap * h / (N : ℝ))) := by
        have hD' : (∫ a : Shao.Path N, H.indicator D a ∂P) ≤
            (Real.sqrt (N : ℝ) *
              Real.exp (-(h / (8 * Bcap)) * Real.log (1 + Bcap * h / (N : ℝ)))) / (N : ℝ) := by
          apply (le_div_iff₀ hNr).2
          nlinarith only [hCycle, hBound]
        have heq : (Real.sqrt (N : ℝ) / (N : ℝ) *
            Real.exp (-(h / (8 * Bcap)) * Real.log (1 + Bcap * h / (N : ℝ)))) * (N : ℝ) =
              Real.sqrt (N : ℝ) *
                Real.exp (-(h / (8 * Bcap)) * Real.log (1 + Bcap * h / (N : ℝ))) := by
          field_simp [hNr.ne']
        apply hD'.trans_eq
        ring
      have hRootInv : Real.sqrt (N : ℝ) / (N : ℝ) = 1 / Real.sqrt (N : ℝ) := by
        apply (div_eq_div_iff hNr.ne' hroot.ne').2
        simpa only [one_mul] using Real.mul_self_sqrt hNr.le
      rw [hRootInv] at hD
      have he := mul_le_mul_of_nonneg_left hD hbeta0
      convert he using 1 <;> ring
    have hSplit : H.indicator (fun a => D a ^ 2 + beta * D a) =
        (fun a => H.indicator (fun a => D a ^ 2) a + beta * H.indicator D a) := by
      funext a
      by_cases ha : a ∈ H <;> simp [ha]
    rw [hSplit, integral_add (hD2I.indicator hH) ((hDI.indicator hH).const_mul beta), integral_const_mul]
    have he := add_le_add (hSecondData.2 h hh) hFirstMarked
    have hc : 16 * CH + 1 ≤ C := by dsimp only [C]; linarith only [hCS0, hCH0]
    have hm := mul_le_mul_of_nonneg_right hc
      (show 0 ≤ beta / Real.sqrt (N : ℝ) *
        Real.exp (-(h / (8 * Bcap)) * Real.log (1 + Bcap * h / (N : ℝ))) by positivity)
    calc
      _ ≤ 16 * CH * beta / Real.sqrt (N : ℝ) *
          Real.exp (-(h / (8 * Bcap)) * Real.log (1 + Bcap * h / (N : ℝ))) +
            beta / Real.sqrt (N : ℝ) *
              Real.exp (-(h / (8 * Bcap)) * Real.log (1 + Bcap * h / (N : ℝ))) := he
      _ = (16 * CH + 1) * (beta / Real.sqrt (N : ℝ) *
          Real.exp (-(h / (8 * Bcap)) * Real.log (1 + Bcap * h / (N : ℝ)))) := by ring
      _ ≤ C * (beta / Real.sqrt (N : ℝ) *
          Real.exp (-(h / (8 * Bcap)) * Real.log (1 + Bcap * h / (N : ℝ)))) := hm
      _ = _ := by ring

theorem actual_unweighted_true_energy_record_strip :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (Bcap : ℝ), 0 < Bcap → (∀ᵐ z : ℝ ∂rho, |z| ≤ Bcap) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ (n : ℕ), 0 < n →
          ∀ x : ℝ, 1 ≤ x → Bcap ≤ Real.sqrt (n : ℝ) / (200 * x) →
            ∀ j : ℕ, 2 ≤ j → j ≤ n →
              let P : Measure (Shao.Path j) := Measure.pi (fun _ : Fin j => rho)
              let D : Shao.Path j → ℝ := fun a =>
                max (Shao.prefixSum a j - Shao.maxWithZero
                  (Shao.Probability.Spitzer.head a (j - 1) (Nat.sub_le j 1))) 0
              ∀ q : ℝ, 0 ≤ q →
                let F : Shao.Path j → ℝ := fun a => Shao.prefixSum a j -
                  x * Real.sqrt (max (Shao.energy a + q) ((n : ℝ) / 2))
                let E : Set (Shao.Path j) := {a | 0 ≤ F a ∧ F a ≤ D a}
                Measurable F ∧ MeasurableSet E ∧
                  Integrable (E.indicator D) P ∧
                  (∫ a : Shao.Path j, E.indicator D a ∂P) ≤
                    C * beta / (j : ℝ) := by
  classical
  obtain ⟨CR, hCR, hRecord⟩ := ers_record_endpoint_moments
  let C : ℝ := 1000 * CR + 1
  have hCR0 : 0 ≤ CR := zero_le_one.trans hCR
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hCR0]
  refine ⟨C, hC, ?_⟩
  intro rho hprob Bcap hB hs hmean hsecond beta n hn x hx hcap j hj hjn P D q hq F E
  run_tac
    let mod : Lean.Name := "Shao.Probability.SourceWeightedPrefixWall".toName
    let nm := Lean.mkPrivateNameCore mod
      ("Shao.Probability.SourceWeightedPrefixWall.pww_actual_clipped_wall_statistic".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hClipped".toName)) := $(Lean.mkIdent nm)))
    let mod : Lean.Name := "Shao.Probability.SourceTrueEnergyStrip".toName
    for (src, dst) in
        [("tes_normalization_data", "hNormalization"),
         ("tes_head_tail_measurePreserving", "hSplitMP"),
         ("tes_head_tail_sum", "hSplitSum"),
         ("tes_reverse_prefixSum", "hReversePrefix"),
         ("tes_reverse_tail_prefixSum", "hReverseTail")] do
      let nm := Lean.mkPrivateNameCore mod (("Shao.Probability." ++ src).toName)
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        have $(Lean.mkIdent dst.toName) := @$(Lean.mkIdent nm)))
  have hPower (r : ℕ) : Integrable (fun z : ℝ => |z| ^ r) rho := by
    apply (integrable_const (Bcap ^ r)).mono' (by fun_prop)
    filter_upwards [hs] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg z) r)]
    exact pow_le_pow_left₀ (abs_nonneg z) hz r
  have h2 : Integrable (fun z : ℝ => z ^ 2) rho := by
    simpa only [sq_abs] using hPower 2
  have hbeta0 : 0 ≤ beta := integral_nonneg fun z => pow_nonneg (abs_nonneg z) 3
  have hCoordinate (k : ℕ) (hk : 0 < k) (Phi : Shao.Path k → ℝ)
      (hPhi : Measurable Phi)
      (hSlope : ∀ (v : Shao.Path k) (i : Fin k) (s t : ℝ), s ≤ t →
        (1 / 2 : ℝ) * (t - s) ≤
          Phi (Function.update v i t) - Phi (Function.update v i s))
      (a b : ℝ) (hab : a ≤ b) :
      (Measure.pi (fun _ : Fin k => rho)).real
        {v : Shao.Path k | a ≤ Phi v ∧ Phi v ≤ b} ≤
          84 * ((b - a) + beta) / Real.sqrt (k : ℝ) := by
    let r : ℝ := Real.sqrt (k : ℝ)
    let eta : Measure ℝ := Measure.map (fun z : ℝ => z / r) rho
    let Q : Measure (Shao.Path k) := Measure.pi (fun _ : Fin k => rho)
    let Qeta : Measure (Shao.Path k) := Measure.pi (fun _ : Fin k => eta)
    let scale : Shao.Path k → Shao.Path k := fun v i => v i / r
    let lift : Shao.Path k → Shao.Path k := fun v i => r * v i
    let G : Shao.Path k → ℝ := fun v => 2 * Phi (lift v) / r
    have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
    have hr : 0 < r := Real.sqrt_pos.2 hkr
    have hr2 : r ^ 2 = (k : ℝ) := Real.sq_sqrt hkr.le
    have hNorm := hNormalization rho k hk h2 hmean (by rw [hsecond]; norm_num)
    simp only [hsecond, mul_one] at hNorm
    change 0 < r ∧ IsProbabilityMeasure eta ∧
      Integrable (fun z : ℝ => z ^ 2) eta ∧ (∫ z : ℝ, z ∂eta) = 0 ∧
      (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta) = 1 ∧
      Measure.map scale Q = Qeta at hNorm
    letI : IsProbabilityMeasure eta := hNorm.2.1
    have hGM : Measurable G :=
      (measurable_const.mul (hPhi.comp (Measurable.of_eval fun i =>
        measurable_const.mul (measurable_pi_apply i)))).div_const r
    have hUpdate (v : Shao.Path k) (i : Fin k) (s : ℝ) :
        lift (Function.update v i s) = Function.update (lift v) i (r * s) := by
      funext j
      by_cases hj : j = i <;> simp [hj, lift]
    have hStrong (v : Shao.Path k) (i : Fin k) :
        Monotone (fun s : ℝ => G (Function.update v i s) - s) := by
      intro s t hst
      have hinc := hSlope (lift v) i (r * s) (r * t)
        (mul_le_mul_of_nonneg_left hst hr.le)
      have he := mul_le_mul_of_nonneg_left hinc (show 0 ≤ 2 / r by positivity)
      have hLeft : (2 / r) * ((1 / 2 : ℝ) * (r * t - r * s)) = t - s := by
        field_simp [hr.ne']
        <;> ring
      have hRight : (2 / r) *
          (Phi (Function.update (lift v) i (r * t)) - Phi (Function.update (lift v) i (r * s))) =
            2 * Phi (Function.update (lift v) i (r * t)) / r -
              2 * Phi (Function.update (lift v) i (r * s)) / r := by ring
      rw [hLeft, hRight] at he
      dsimp only [G]
      rw [hUpdate, hUpdate]
      linarith only [he]
    have hMapM : Measurable (fun z : ℝ => z / r) := by fun_prop
    have h3eta : Integrable (fun z : ℝ => |z| ^ 3) eta := by
      apply (integrable_map_measure (by fun_prop) hMapM.aemeasurable).2
      simpa only [Function.comp_def, id_eq, abs_div, abs_of_pos hr, div_pow] using
        (hPower 3).div_const (r ^ 3)
    have h3val : (∫ z : ℝ, |z| ^ 3 ∂eta) = beta / r ^ 3 := by
      rw [show eta = Measure.map (fun z : ℝ => z / r) rho from rfl,
        integral_map (μ := rho) (φ := fun z : ℝ => z / r)
          (f := fun z : ℝ => |z| ^ 3) hMapM.aemeasurable (by fun_prop)]
      simp_rw [abs_div, abs_of_pos hr, div_pow]
      rw [integral_div]
    have hBudget : Shao.truncationBudget eta k 0 ≤ beta / r := by
      have hF (z : ℝ) : 0 ≤ Shao.truncationF z ∧ Shao.truncationF z ≤ |z| ^ 3 := by
        constructor
        · dsimp only [Shao.truncationF]
          positivity
        · calc
            Shao.truncationF z ≤ z ^ 2 * |z| :=
              mul_le_mul_of_nonneg_left (min_le_left _ _) (sq_nonneg z)
            _ = |z| ^ 3 := by rw [← sq_abs z]; ring
      have hFI : Integrable Shao.truncationF eta := by
        apply h3eta.mono' (by
          change AEStronglyMeasurable (fun z : ℝ => z ^ 2 * min |z| 1) eta
          fun_prop)
        exact ae_of_all eta fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hF z).1]
          exact (hF z).2
      have he := mul_le_mul_of_nonneg_left (integral_mono hFI h3eta (fun z => (hF z).2))
        (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      simp only [Shao.truncationBudget, add_zero, one_mul]
      rw [h3val] at he
      apply he.trans_eq
      rw [← hr2]
      field_simp [hr.ne']
      <;> ring
    have hAB : 2 * a / r ≤ 2 * b / r := by gcongr
    have hConc := Shao.Probability.iid_strong_monotonicity_concentration eta k hk
      hNorm.2.2.1 hNorm.2.2.2.1 hNorm.2.2.2.2.1 G hGM hStrong
      (2 * a / r) (2 * b / r) hAB
    let V : Set (Shao.Path k) := {v | 2 * a / r ≤ G v ∧ G v ≤ 2 * b / r}
    have hVM : MeasurableSet V := (measurableSet_le measurable_const hGM).inter
      (measurableSet_le hGM measurable_const)
    have hScaleM : Measurable scale := by
      change Measurable (fun v : Shao.Path k => fun i : Fin k => v i / r)
      exact Measurable.of_eval
        (f := fun v : Shao.Path k => fun i : Fin k => v i / r)
        (fun i => Measurable.div_const (f := fun v : Shao.Path k => v i)
          (c := r) (measurable_pi_apply i))
    have hLiftScale (v : Shao.Path k) : lift (scale v) = v := by
      funext i
      dsimp only [lift, scale]
      field_simp [hr.ne']
    have hSet : scale ⁻¹' V = {v : Shao.Path k | a ≤ Phi v ∧ Phi v ≤ b} := by
      ext v
      change (2 * a / r ≤ 2 * Phi (lift (scale v)) / r ∧
        2 * Phi (lift (scale v)) / r ≤ 2 * b / r) ↔ _
      rw [hLiftScale]
      simp only [div_le_div_iff_of_pos_right hr]
      constructor <;> rintro ⟨h1, h2'⟩ <;> constructor <;> linarith only [h1, h2']
    have hProb : Q.real {v : Shao.Path k | a ≤ Phi v ∧ Phi v ≤ b} = Qeta.real V := by
      rw [← hNorm.2.2.2.2.2]
      simp only [Measure.real_def, Measure.map_apply hScaleM hVM, hSet]
    rw [hProb]
    apply hConc.trans
    have he := mul_le_mul_of_nonneg_left hBudget (by norm_num : (0 : ℝ) ≤ 80)
    have hWidth : 0 ≤ b - a := sub_nonneg.2 hab
    change 2 * (2 * b / r - 2 * a / r) + 80 * Shao.truncationBudget eta k 0 ≤
      84 * (b - a + beta) / r
    have hEq : 2 * (2 * b / r - 2 * a / r) + 80 * (beta / r) =
        (4 * (b - a) + 80 * beta) / r := by ring
    have hCoef : 4 * (b - a) + 80 * beta ≤ 84 * (b - a + beta) := by
      linarith only [hWidth, hbeta0]
    calc
      _ ≤ 2 * (2 * b / r - 2 * a / r) + 80 * (beta / r) := by linarith only [he]
      _ = _ := hEq
      _ ≤ _ := div_le_div_of_nonneg_right hCoef hr.le
  let k : ℕ := j / 2
  let l : ℕ := j - k
  have hk : 0 < k := by dsimp only [k]; omega
  have hl : 0 < l := by dsimp only [l, k]; omega
  have hkj : k ≤ j := by dsimp only [k]; omega
  have hlj : l ≤ j := Nat.sub_le _ _
  have hkl : k + l = j := Nat.add_sub_of_le hkj
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  have hlr : 0 < (l : ℝ) := by exact_mod_cast hl
  have hjr : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hkrRoot : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkr
  have hlrRoot : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.2 hlr
  have hkquarter : (j : ℝ) / 4 ≤ (k : ℝ) := by
    have he : j ≤ 4 * k := by dsimp only [k]; omega
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    have her : (j : ℝ) ≤ 4 * (k : ℝ) := by exact_mod_cast he
    linarith only [her]
  have hlquarter : (j : ℝ) / 4 ≤ (l : ℝ) := by
    have he : j ≤ 4 * l := by dsimp only [l, k]; omega
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    have her : (j : ℝ) ≤ 4 * (l : ℝ) := by exact_mod_cast he
    linarith only [her]
  let Pk : Measure (Shao.Path k) := Measure.pi (fun _ : Fin k => rho)
  let Pl : Measure (Shao.Path l) := Measure.pi (fun _ : Fin l => rho)
  let H : Shao.Path j → Shao.Path k := fun a => Shao.Probability.Spitzer.head a k hkj
  let T : Shao.Path j → Shao.Path l := fun a => Shao.Probability.Spitzer.tail a k hkj
  let dl : Shao.Path l → ℝ := fun a => max (Shao.prefixSum a l -
    Shao.maxWithZero (Shao.Probability.Spitzer.head a (l - 1) (Nat.sub_le l 1))) 0
  let clip : ℝ → ℝ := fun z => max (-Bcap) (min z Bcap)
  let Phi : Shao.Path l → Shao.Path k → ℝ := fun v u => Shao.prefixSum u k -
    x * Real.sqrt (max ((∑ i : Fin k, (clip (u i)) ^ 2) + Shao.energy v + q) ((n : ℝ) / 2))
  let I : Shao.Path l → Set (Shao.Path k) := fun v =>
    {u | -Shao.prefixSum v l ≤ Phi v u ∧ Phi v u ≤ dl v - Shao.prefixSum v l}
  let G : Shao.Path k × Shao.Path l → ℝ := fun p => (I p.2).indicator (fun _ => dl p.2) p.1
  have hM := hRecord rho Bcap hB hs hmean hsecond l hl
  change Measurable dl ∧ Integrable (fun v => dl v ^ 2 + beta * dl v) Pl ∧
    (∫ v : Shao.Path l, dl v ^ 2 + beta * dl v ∂Pl) ≤ CR * beta / Real.sqrt (l : ℝ) ∧
      _ at hM
  have hDm : Measurable D := by
    have hh : Measurable (fun a : Shao.Path j =>
        Shao.Probability.Spitzer.head a (j - 1) (Nat.sub_le j 1)) :=
      Measurable.of_eval fun i => measurable_pi_apply _
    exact ((Shao.measurable_prefixSum j).sub (Shao.measurable_maxWithZero.comp hh)).max measurable_const
  have hFm : Measurable F := (Shao.measurable_prefixSum j).sub
    (measurable_const.mul (((Shao.measurable_energy.add_const q).max measurable_const).sqrt))
  have hEm : MeasurableSet E := (measurableSet_le measurable_const hFm).inter
    (measurableSet_le hFm hDm)
  have hD0 (a : Shao.Path j) : 0 ≤ D a := le_max_right _ _
  have hdl0 (v : Shao.Path l) : 0 ≤ dl v := le_max_right _ _
  have hSupport (m : ℕ) : ∀ᵐ a : Shao.Path m ∂Measure.pi (fun _ : Fin m => rho),
      ∀ i : Fin m, |a i| ≤ Bcap := by
    apply ae_all_iff.2
    intro i
    exact (measurePreserving_eval (fun _ : Fin m => rho) i).quasiMeasurePreserving.ae hs
  have hdCap (m : ℕ) (a : Shao.Path m) (ha : ∀ i : Fin m, |a i| ≤ Bcap) :
      max (Shao.prefixSum a m - Shao.maxWithZero
        (Shao.Probability.Spitzer.head a (m - 1) (Nat.sub_le m 1))) 0 ≤ (m : ℝ) * Bcap := by
    apply max_le
    · have he : Shao.prefixSum a m ≤ (m : ℝ) * Bcap := by
        rw [Shao.prefixSum_length]
        calc
          _ ≤ ∑ _ : Fin m, Bcap := Finset.sum_le_sum fun i _ => (le_abs_self _).trans (ha i)
          _ = _ := by simp
      linarith only [he, Shao.maxWithZero_nonneg
        (Shao.Probability.Spitzer.head a (m - 1) (Nat.sub_le m 1))]
    · positivity
  have hfI : Integrable (E.indicator D) P := by
    apply (integrable_const ((j : ℝ) * Bcap)).mono' (hDm.indicator hEm).aestronglyMeasurable
    filter_upwards [hSupport j] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun a _ => hD0 a) a)]
    by_cases he : a ∈ E
    · rw [Set.indicator_of_mem he]
      exact hdCap j a ha
    · rw [Set.indicator_of_notMem he]
      positivity
  have hPhiM : Measurable (fun p : Shao.Path k × Shao.Path l => Phi p.2 p.1) := by
    dsimp only [Phi, clip, Shao.prefixSum, Shao.energy]
    fun_prop
  have hIM : MeasurableSet {p : Shao.Path k × Shao.Path l | p.1 ∈ I p.2} :=
    (measurableSet_le ((Shao.measurable_prefixSum l).comp measurable_snd).neg hPhiM).inter
      (measurableSet_le hPhiM ((hM.1.comp measurable_snd).sub
        ((Shao.measurable_prefixSum l).comp measurable_snd)))
  have hGm : Measurable G := Measurable.ite hIM (hM.1.comp measurable_snd) measurable_const
  have hG0 (p : Shao.Path k × Shao.Path l) : 0 ≤ G p :=
    Set.indicator_nonneg (fun _ _ => hdl0 p.2) p.1
  have hGI : Integrable G (Pk.prod Pl) := by
    apply (integrable_const ((l : ℝ) * Bcap)).mono' hGm.aestronglyMeasurable
    filter_upwards [(measurePreserving_snd (μ := Pk) (ν := Pl)).quasiMeasurePreserving.ae (hSupport l)] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (hG0 p)]
    by_cases he : p.1 ∈ I p.2
    · rw [show G p = dl p.2 from Set.indicator_of_mem he _]
      exact hdCap l p.2 hp
    · rw [show G p = 0 from Set.indicator_of_notMem he _]
      positivity
  have hPairMP : MeasurePreserving (fun a : Shao.Path j => (H a, T a)) P (Pk.prod Pl) :=
    hSplitMP rho j k hkj
  have hTotal (a : Shao.Path j) :
      Shao.prefixSum a j = Shao.prefixSum (H a) k + Shao.prefixSum (T a) l := by
    simpa only [Shao.prefixSum_length] using hSplitSum a k hkj (fun z => z)
  have hEnergy (a : Shao.Path j) : Shao.energy a = Shao.energy (H a) + Shao.energy (T a) :=
    hSplitSum a k hkj (fun z => z ^ 2)
  have hPrefix (a : Shao.Path j) (r : ℕ) (hr : r ≤ l) :
      Shao.prefixSum a (k + r) = Shao.prefixSum (H a) k + Shao.prefixSum (T a) r := by
    have h1 := hReverseTail a k hkj (l - r) (Nat.sub_le l r)
    have h2' := hReversePrefix (T a) (l - r) (Nat.sub_le l r)
    change Shao.prefixSum (fun i : Fin l => T a (Fin.rev i)) (l - r) =
      Shao.prefixSum a j - Shao.prefixSum a (j - (l - r)) at h1
    have hi1 : j - (l - r) = k + r := by dsimp only [l] at hr ⊢; omega
    have hi2 : l - (l - r) = r := by omega
    rw [hi1, hTotal a] at h1
    rw [hi2] at h2'
    linarith only [h1, h2']
  have hDtail (a : Shao.Path j) : D a ≤ dl (T a) := by
    let Mj : ℝ := Shao.maxWithZero (Shao.Probability.Spitzer.head a (j - 1) (Nat.sub_le j 1))
    let Ml : ℝ := Shao.maxWithZero (Shao.Probability.Spitzer.head (T a) (l - 1) (Nat.sub_le l 1))
    have hM' : Ml ≤ Mj - Shao.prefixSum (H a) k := by
      apply (Shao.maxWithZero_le_iff _ _).2
      intro r hr
      rw [Shao.Probability.Spitzer.head_prefixSum _ _ _ _ hr]
      have hkrj : k + r ≤ j - 1 := by dsimp only [l] at hr hl ⊢; omega
      have he := (Shao.maxWithZero_le_iff
        (Shao.Probability.Spitzer.head a (j - 1) (Nat.sub_le j 1)) Mj).1 le_rfl (k + r) hkrj
      rw [Shao.Probability.Spitzer.head_prefixSum _ _ _ _ hkrj,
        hPrefix a r (by omega)] at he
      linarith only [he]
    change max (Shao.prefixSum a j - Mj) 0 ≤ max (Shao.prefixSum (T a) l - Ml) 0
    apply max_le_max _ le_rfl
    rw [hTotal]
    linarith only [hM']
  have hPhiActual (a : Shao.Path j) (ha : ∀ i : Fin j, |a i| ≤ Bcap) :
      F a = Phi (T a) (H a) + Shao.prefixSum (T a) l := by
    have hc (i : Fin k) : clip (H a i) = H a i := by
      have hb := abs_le.1 (ha ⟨i.val, Nat.lt_of_lt_of_le i.isLt hkj⟩)
      change -Bcap ≤ H a i ∧ H a i ≤ Bcap at hb
      dsimp only [clip]
      rw [min_eq_left hb.2, max_eq_right hb.1]
    have hcs : (∑ i : Fin k, (clip (H a i)) ^ 2) = Shao.energy (H a) := by
      simp only [hc, Shao.energy]
    dsimp only [F, Phi]
    rw [hcs, hTotal, hEnergy]
    ring
  have hPoint : ∀ᵐ a : Shao.Path j ∂P, E.indicator D a ≤ G (H a, T a) := by
    filter_upwards [hSupport j] with a ha
    by_cases he : a ∈ E
    · have hi : H a ∈ I (T a) := by
        have hf := hPhiActual a ha
        exact ⟨by linarith only [he.1, hf], by linarith only [he.2, hf, hDtail a]⟩
      rw [Set.indicator_of_mem he]
      change D a ≤ (I (T a)).indicator (fun _ => dl (T a)) (H a)
      rw [Set.indicator_of_mem hi]
      exact hDtail a
    · rw [Set.indicator_of_notMem he]
      exact hG0 _
  have hSlopeSmall : 4 * x * Bcap ≤ Real.sqrt (n : ℝ) := by
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    have he := (le_div_iff₀ (show 0 < 200 * x by positivity)).1 hcap
    have hxb : 0 ≤ x * Bcap := by positivity
    nlinarith only [he, hxb]
  have hSection (v : Shao.Path l) : (∫ u : Shao.Path k, G (u, v) ∂Pk) ≤
      84 / Real.sqrt (k : ℝ) * (dl v ^ 2 + beta * dl v) := by
    have hPhiData := hClipped k (n : ℝ) Bcap x (Shao.energy v + q) 0
      hnr hB.le (zero_le_one.trans hx) (add_nonneg (Shao.energy_nonneg v) hq) le_rfl hSlopeSmall
    have hPhiV : Measurable (Phi v) := by
      simpa only [Phi, clip, add_zero, add_assoc] using hPhiData.1.measurable
    have hSlopes : ∀ (a : Shao.Path k) (i : Fin k) (s t : ℝ), s ≤ t →
        (1 / 2 : ℝ) * (t - s) ≤ Phi v (Function.update a i t) - Phi v (Function.update a i s) := by
      intro a i s t hst
      simpa only [Phi, clip, add_zero, add_assoc] using (hPhiData.2.1 a i s t hst).1
    have he := hCoordinate k hk (Phi v) hPhiV hSlopes
      (-Shao.prefixSum v l) (dl v - Shao.prefixSum v l) (by linarith only [hdl0 v])
    have hIMv : MeasurableSet (I v) := (measurableSet_le measurable_const hPhiV).inter
      (measurableSet_le hPhiV measurable_const)
    change (∫ u : Shao.Path k, (I v).indicator (fun _ => dl v) u ∂Pk) ≤ _
    rw [integral_indicator_const _ hIMv]
    simp only [smul_eq_mul]
    have he' := mul_le_mul_of_nonneg_left he (hdl0 v)
    convert he' using 1 <;> ring
  have hTotalBound : (∫ a : Shao.Path j, E.indicator D a ∂P) ≤
      84 / Real.sqrt (k : ℝ) * (CR * beta / Real.sqrt (l : ℝ)) := by
    calc
      _ ≤ ∫ a : Shao.Path j, G (H a, T a) ∂P :=
        integral_mono_ae hfI (hPairMP.integrable_comp_of_integrable hGI) hPoint
      _ = ∫ p : Shao.Path k × Shao.Path l, G p ∂Pk.prod Pl := by
        have he := integral_map hPairMP.aemeasurable hGm.aestronglyMeasurable
        rw [hPairMP.map_eq] at he
        exact he.symm
      _ = ∫ v : Shao.Path l, ∫ u : Shao.Path k, G (u, v) ∂Pk ∂Pl := integral_prod_symm _ hGI
      _ ≤ ∫ v : Shao.Path l, 84 / Real.sqrt (k : ℝ) * (dl v ^ 2 + beta * dl v) ∂Pl :=
        integral_mono hGI.integral_prod_right (hM.2.1.const_mul _) hSection
      _ = 84 / Real.sqrt (k : ℝ) * ∫ v : Shao.Path l, dl v ^ 2 + beta * dl v ∂Pl :=
        integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hM.2.2.1 (by positivity)
  have hRootsK : Real.sqrt (j : ℝ) ≤ 2 * Real.sqrt (k : ℝ) := by
    have hsqj := Real.sq_sqrt hjr.le
    have hsqk := Real.sq_sqrt hkr.le
    nlinarith only [hsqj, hsqk, hkquarter, Real.sqrt_nonneg (j : ℝ), Real.sqrt_nonneg (k : ℝ)]
  have hRootsL : Real.sqrt (j : ℝ) ≤ 2 * Real.sqrt (l : ℝ) := by
    have hsqj := Real.sq_sqrt hjr.le
    have hsql := Real.sq_sqrt hlr.le
    nlinarith only [hsqj, hsql, hlquarter, Real.sqrt_nonneg (j : ℝ), Real.sqrt_nonneg (l : ℝ)]
  have hRoots : (j : ℝ) ≤ 4 * (Real.sqrt (k : ℝ) * Real.sqrt (l : ℝ)) := by
    have he := mul_le_mul hRootsK hRootsL (Real.sqrt_nonneg (j : ℝ))
      (show 0 ≤ 2 * Real.sqrt (k : ℝ) by positivity)
    rw [Real.mul_self_sqrt hjr.le] at he
    nlinarith only [he]
  have hInv : 1 / (Real.sqrt (k : ℝ) * Real.sqrt (l : ℝ)) ≤ 4 / (j : ℝ) := by
    apply (div_le_div_iff₀ (mul_pos hkrRoot hlrRoot) hjr).2
    simpa only [one_mul] using hRoots
  refine ⟨hFm, hEm, hfI, hTotalBound.trans ?_⟩
  calc
    _ = 84 * CR * beta * (1 / (Real.sqrt (k : ℝ) * Real.sqrt (l : ℝ))) := by ring
    _ ≤ 84 * CR * beta * (4 / (j : ℝ)) :=
      mul_le_mul_of_nonneg_left hInv (by positivity)
    _ ≤ C * beta / (j : ℝ) := by
      have hc : 336 * CR ≤ C := by dsimp only [C]; linarith only [hCR0]
      have he := mul_le_mul_of_nonneg_right hc (show 0 ≤ beta / (j : ℝ) by positivity)
      convert he using 1 <;> ring

theorem actual_true_energy_record_strip_endpoint_tail :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (Bcap : ℝ), 0 < Bcap → (∀ᵐ z : ℝ ∂rho, |z| ≤ Bcap) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ (n : ℕ), 0 < n →
          ∀ x : ℝ, 1 ≤ x → Bcap ≤ Real.sqrt (n : ℝ) / (200 * x) →
            ∀ j : ℕ, 12 ≤ j → j ≤ n →
              let P : Measure (Shao.Path j) := Measure.pi (fun _ : Fin j => rho)
              let D : Shao.Path j → ℝ := fun a =>
                max (Shao.prefixSum a j - Shao.maxWithZero
                  (Shao.Probability.Spitzer.head a (j - 1) (Nat.sub_le j 1))) 0
              ∀ q : ℝ, 0 ≤ q →
                let F : Shao.Path j → ℝ := fun a => Shao.prefixSum a j -
                  x * Real.sqrt (max (Shao.energy a + q) ((n : ℝ) / 2))
                ∀ A : ℝ, max (24 * Bcap) (3 * Real.sqrt (j : ℝ)) ≤ A →
                  let E : Set (Shao.Path j) :=
                    {a | 0 ≤ F a ∧ F a ≤ D a ∧ A ≤ Shao.prefixSum a j}
                  Measurable F ∧ MeasurableSet E ∧
                    Integrable (E.indicator D) P ∧
                    (∫ a : Shao.Path j, E.indicator D a ∂P) ≤
                      C * beta / (j : ℝ) *
                        Real.exp (-(A / (72 * Bcap)) *
                          Real.log (1 + A * Bcap / (j : ℝ))) := by
  classical
  obtain ⟨CR, hCR, hRecord⟩ := ers_record_endpoint_moments
  let C : ℝ := 10000 * CR + 1
  have hCR0 : 0 ≤ CR := zero_le_one.trans hCR
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hCR0]
  refine ⟨C, hC, ?_⟩
  intro rho hprob Bcap hB hs hmean hsecond beta n hn x hx hcap j hj hjn P D q hq F A hA E
  run_tac
    let mod : Lean.Name := "Shao.Probability.SourceWeightedPrefixWall".toName
    let nm := Lean.mkPrivateNameCore mod
      ("Shao.Probability.SourceWeightedPrefixWall.pww_actual_clipped_wall_statistic".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hClipped".toName)) := $(Lean.mkIdent nm)))
    let mod : Lean.Name := "Shao.Probability.SourceTrueEnergyStrip".toName
    for (src, dst) in
        [("tes_normalization_data", "hNormalization"),
         ("tes_head_tail_measurePreserving", "hSplitMP"),
         ("tes_head_tail_sum", "hSplitSum"),
         ("tes_reverse_prefixSum", "hReversePrefix"),
         ("tes_reverse_tail_prefixSum", "hReverseTail")] do
      let nm := Lean.mkPrivateNameCore mod (("Shao.Probability." ++ src).toName)
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        have $(Lean.mkIdent dst.toName) := @$(Lean.mkIdent nm)))
  have hPower (r : ℕ) : Integrable (fun z : ℝ => |z| ^ r) rho := by
    apply (integrable_const (Bcap ^ r)).mono' (by fun_prop)
    filter_upwards [hs] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg z) r)]
    exact pow_le_pow_left₀ (abs_nonneg z) hz r
  have h2 : Integrable (fun z : ℝ => z ^ 2) rho := by simpa only [sq_abs] using hPower 2
  have hbeta0 : 0 ≤ beta := integral_nonneg fun z => pow_nonneg (abs_nonneg z) 3
  have hCoordinate (k : ℕ) (hk : 0 < k) (Phi : Shao.Path k → ℝ)
      (hPhi : Measurable Phi)
      (hSlope : ∀ (v : Shao.Path k) (i : Fin k) (s t : ℝ), s ≤ t →
        (1 / 2 : ℝ) * (t - s) ≤
          Phi (Function.update v i t) - Phi (Function.update v i s))
      (a b : ℝ) (hab : a ≤ b) :
      (Measure.pi (fun _ : Fin k => rho)).real
        {v : Shao.Path k | a ≤ Phi v ∧ Phi v ≤ b} ≤
          84 * ((b - a) + beta) / Real.sqrt (k : ℝ) := by
    let r : ℝ := Real.sqrt (k : ℝ)
    let eta : Measure ℝ := Measure.map (fun z : ℝ => z / r) rho
    let Q : Measure (Shao.Path k) := Measure.pi (fun _ : Fin k => rho)
    let Qeta : Measure (Shao.Path k) := Measure.pi (fun _ : Fin k => eta)
    let scale : Shao.Path k → Shao.Path k := fun v i => v i / r
    let lift : Shao.Path k → Shao.Path k := fun v i => r * v i
    let G : Shao.Path k → ℝ := fun v => 2 * Phi (lift v) / r
    have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
    have hr : 0 < r := Real.sqrt_pos.2 hkr
    have hr2 : r ^ 2 = (k : ℝ) := Real.sq_sqrt hkr.le
    have hNorm := hNormalization rho k hk h2 hmean (by rw [hsecond]; norm_num)
    simp only [hsecond, mul_one] at hNorm
    change 0 < r ∧ IsProbabilityMeasure eta ∧
      Integrable (fun z : ℝ => z ^ 2) eta ∧ (∫ z : ℝ, z ∂eta) = 0 ∧
      (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂eta) = 1 ∧
      Measure.map scale Q = Qeta at hNorm
    letI : IsProbabilityMeasure eta := hNorm.2.1
    have hGM : Measurable G :=
      (measurable_const.mul (hPhi.comp (Measurable.of_eval fun i =>
        measurable_const.mul (measurable_pi_apply i)))).div_const r
    have hUpdate (v : Shao.Path k) (i : Fin k) (s : ℝ) :
        lift (Function.update v i s) = Function.update (lift v) i (r * s) := by
      funext j
      by_cases hj : j = i <;> simp [hj, lift]
    have hStrong (v : Shao.Path k) (i : Fin k) :
        Monotone (fun s : ℝ => G (Function.update v i s) - s) := by
      intro s t hst
      have hinc := hSlope (lift v) i (r * s) (r * t)
        (mul_le_mul_of_nonneg_left hst hr.le)
      have he := mul_le_mul_of_nonneg_left hinc (show 0 ≤ 2 / r by positivity)
      have hLeft : (2 / r) * ((1 / 2 : ℝ) * (r * t - r * s)) = t - s := by
        field_simp [hr.ne']
        <;> ring
      have hRight : (2 / r) *
          (Phi (Function.update (lift v) i (r * t)) - Phi (Function.update (lift v) i (r * s))) =
            2 * Phi (Function.update (lift v) i (r * t)) / r -
              2 * Phi (Function.update (lift v) i (r * s)) / r := by ring
      rw [hLeft, hRight] at he
      dsimp only [G]
      rw [hUpdate, hUpdate]
      linarith only [he]
    have hMapM : Measurable (fun z : ℝ => z / r) := by fun_prop
    have h3eta : Integrable (fun z : ℝ => |z| ^ 3) eta := by
      apply (integrable_map_measure (by fun_prop) hMapM.aemeasurable).2
      simpa only [Function.comp_def, id_eq, abs_div, abs_of_pos hr, div_pow] using
        (hPower 3).div_const (r ^ 3)
    have h3val : (∫ z : ℝ, |z| ^ 3 ∂eta) = beta / r ^ 3 := by
      rw [show eta = Measure.map (fun z : ℝ => z / r) rho from rfl,
        integral_map (μ := rho) (φ := fun z : ℝ => z / r)
          (f := fun z : ℝ => |z| ^ 3) hMapM.aemeasurable (by fun_prop)]
      simp_rw [abs_div, abs_of_pos hr, div_pow]
      rw [integral_div]
    have hBudget : Shao.truncationBudget eta k 0 ≤ beta / r := by
      have hF (z : ℝ) : 0 ≤ Shao.truncationF z ∧ Shao.truncationF z ≤ |z| ^ 3 := by
        constructor
        · dsimp only [Shao.truncationF]
          positivity
        · calc
            Shao.truncationF z ≤ z ^ 2 * |z| :=
              mul_le_mul_of_nonneg_left (min_le_left _ _) (sq_nonneg z)
            _ = |z| ^ 3 := by rw [← sq_abs z]; ring
      have hFI : Integrable Shao.truncationF eta := by
        apply h3eta.mono' (by
          change AEStronglyMeasurable (fun z : ℝ => z ^ 2 * min |z| 1) eta
          fun_prop)
        exact ae_of_all eta fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hF z).1]
          exact (hF z).2
      have he := mul_le_mul_of_nonneg_left (integral_mono hFI h3eta (fun z => (hF z).2))
        (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      simp only [Shao.truncationBudget, add_zero, one_mul]
      rw [h3val] at he
      apply he.trans_eq
      rw [← hr2]
      field_simp [hr.ne']
      <;> ring
    have hAB : 2 * a / r ≤ 2 * b / r := by gcongr
    have hConc := Shao.Probability.iid_strong_monotonicity_concentration eta k hk
      hNorm.2.2.1 hNorm.2.2.2.1 hNorm.2.2.2.2.1 G hGM hStrong
      (2 * a / r) (2 * b / r) hAB
    let V : Set (Shao.Path k) := {v | 2 * a / r ≤ G v ∧ G v ≤ 2 * b / r}
    have hVM : MeasurableSet V := (measurableSet_le measurable_const hGM).inter
      (measurableSet_le hGM measurable_const)
    have hScaleM : Measurable scale := by
      change Measurable (fun v : Shao.Path k => fun i : Fin k => v i / r)
      exact Measurable.of_eval
        (f := fun v : Shao.Path k => fun i : Fin k => v i / r)
        (fun i => Measurable.div_const (f := fun v : Shao.Path k => v i)
          (c := r) (measurable_pi_apply i))
    have hLiftScale (v : Shao.Path k) : lift (scale v) = v := by
      funext i
      dsimp only [lift, scale]
      field_simp [hr.ne']
    have hSet : scale ⁻¹' V = {v : Shao.Path k | a ≤ Phi v ∧ Phi v ≤ b} := by
      ext v
      change (2 * a / r ≤ 2 * Phi (lift (scale v)) / r ∧
        2 * Phi (lift (scale v)) / r ≤ 2 * b / r) ↔ _
      rw [hLiftScale]
      simp only [div_le_div_iff_of_pos_right hr]
      constructor <;> rintro ⟨h1, h2'⟩ <;> constructor <;> linarith only [h1, h2']
    have hProb : Q.real {v : Shao.Path k | a ≤ Phi v ∧ Phi v ≤ b} = Qeta.real V := by
      rw [← hNorm.2.2.2.2.2]
      simp only [Measure.real_def, Measure.map_apply hScaleM hVM, hSet]
    rw [hProb]
    apply hConc.trans
    have he := mul_le_mul_of_nonneg_left hBudget (by norm_num : (0 : ℝ) ≤ 80)
    have hWidth : 0 ≤ b - a := sub_nonneg.2 hab
    change 2 * (2 * b / r - 2 * a / r) + 80 * Shao.truncationBudget eta k 0 ≤
      84 * (b - a + beta) / r
    have hEq : 2 * (2 * b / r - 2 * a / r) + 80 * (beta / r) =
        (4 * (b - a) + 80 * beta) / r := by ring
    have hCoef : 4 * (b - a) + 80 * beta ≤ 84 * (b - a + beta) := by
      linarith only [hWidth, hbeta0]
    calc
      _ ≤ 2 * (2 * b / r - 2 * a / r) + 80 * (beta / r) := by linarith only [he]
      _ = _ := hEq
      _ ≤ _ := div_le_div_of_nonneg_right hCoef hr.le
  let k : ℕ := j / 3
  let l : ℕ := j - (k + k)
  have hk : 0 < k := by dsimp only [k]; omega
  have hl : 0 < l := by dsimp only [l, k]; omega
  have h2kj : k + k ≤ j := by dsimp only [k]; omega
  have hkl : (k + k) + l = j := Nat.add_sub_of_le h2kj
  have hkquarter : (j : ℝ) / 4 ≤ (k : ℝ) := by
    have he : j ≤ 4 * k := by dsimp only [k]; omega
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    have her : (j : ℝ) ≤ 4 * (k : ℝ) := by exact_mod_cast he
    linarith only [her]
  have hlquarter : (j : ℝ) / 4 ≤ (l : ℝ) := by
    have he : j ≤ 4 * l := by dsimp only [l, k]; omega
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    have her : (j : ℝ) ≤ 4 * (l : ℝ) := by exact_mod_cast he
    linarith only [her]
  have hkj : k ≤ j := by omega
  have hlj : l ≤ j := Nat.sub_le _ _
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  have hlr : 0 < (l : ℝ) := by exact_mod_cast hl
  have hjr : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkr
  have hrl : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.2 hlr
  let Pk : Measure (Shao.Path k) := Measure.pi (fun _ : Fin k => rho)
  let Pl : Measure (Shao.Path l) := Measure.pi (fun _ : Fin l => rho)
  let R : Measure ((Shao.Path k × Shao.Path k) × Shao.Path l) := (Pk.prod Pk).prod Pl
  let U : Shao.Path j → Shao.Path k := fun a i => a ⟨i.val, by omega⟩
  let V : Shao.Path j → Shao.Path k := fun a i => a ⟨k + i.val, by omega⟩
  let W : Shao.Path j → Shao.Path l := fun a => Shao.Probability.Spitzer.tail a (k + k) h2kj
  let Split : Shao.Path j → (Shao.Path k × Shao.Path k) × Shao.Path l :=
    fun a => ((U a, V a), W a)
  let e : (Fin k ⊕ Fin k) ⊕ Fin l ≃ Fin j :=
    (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin l))).trans
      (finSumFinEquiv.trans (finCongr hkl))
  have hTripleMP : MeasurePreserving Split P R := by
    have h1 := (measurePreserving_piCongrLeft (fun _ : Fin j => rho) e).symm
    have h2' := measurePreserving_sumPiEquivProdPi
      (fun _ : (Fin k ⊕ Fin k) ⊕ Fin l => rho)
    have h3 := (measurePreserving_sumPiEquivProdPi (fun _ : Fin k ⊕ Fin k => rho)).prod
      (MeasurePreserving.id Pl)
    convert h3.comp (h2'.comp h1) using 1
    ext a i <;> change a _ = a _ <;> congr 1
  have hTripleSum (a : Shao.Path j) (g : ℝ → ℝ) :
      (∑ i : Fin j, g (a i)) =
        (∑ i : Fin k, g (U a i)) + (∑ i : Fin k, g (V a i)) +
          (∑ i : Fin l, g (W a i)) := by
    have he := e.sum_comp (fun i : Fin j => g (a i))
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at he
    exact he.symm
  have hTotal (a : Shao.Path j) : Shao.prefixSum a j =
      Shao.prefixSum (U a) k + Shao.prefixSum (V a) k + Shao.prefixSum (W a) l := by
    simpa only [Shao.prefixSum_length, id_eq] using hTripleSum a id
  have hEnergy (a : Shao.Path j) : Shao.energy a =
      Shao.energy (U a) + Shao.energy (V a) + Shao.energy (W a) := hTripleSum a (fun z => z ^ 2)
  let dl : Shao.Path l → ℝ := fun v => max (Shao.prefixSum v l - Shao.maxWithZero
    (Shao.Probability.Spitzer.head v (l - 1) (Nat.sub_le l 1))) 0
  have hM := hRecord rho Bcap hB hs hmean hsecond l hl
  change Measurable dl ∧ Integrable (fun v => dl v ^ 2 + beta * dl v) Pl ∧
    (∫ v : Shao.Path l, dl v ^ 2 + beta * dl v ∂Pl) ≤ CR * beta / Real.sqrt (l : ℝ) ∧
      _ at hM
  have hdl0 (v : Shao.Path l) : 0 ≤ dl v := le_max_right _ _
  have hD0 (a : Shao.Path j) : 0 ≤ D a := le_max_right _ _
  have hDm : Measurable D := by
    have hh : Measurable (fun a : Shao.Path j =>
        Shao.Probability.Spitzer.head a (j - 1) (Nat.sub_le j 1)) :=
      Measurable.of_eval fun i => measurable_pi_apply _
    exact ((Shao.measurable_prefixSum j).sub (Shao.measurable_maxWithZero.comp hh)).max measurable_const
  have hFm : Measurable F := (Shao.measurable_prefixSum j).sub
    (measurable_const.mul (((Shao.measurable_energy.add_const q).max measurable_const).sqrt))
  have hEm : MeasurableSet E := (measurableSet_le measurable_const hFm).inter
    ((measurableSet_le hFm hDm).inter (measurableSet_le measurable_const (Shao.measurable_prefixSum j)))
  have hSupport (m : ℕ) : ∀ᵐ a : Shao.Path m ∂Measure.pi (fun _ : Fin m => rho),
      ∀ i : Fin m, |a i| ≤ Bcap := by
    apply ae_all_iff.2
    intro i
    exact (measurePreserving_eval (fun _ : Fin m => rho) i).quasiMeasurePreserving.ae hs
  have hdCap (m : ℕ) (a : Shao.Path m) (ha : ∀ i : Fin m, |a i| ≤ Bcap) :
      max (Shao.prefixSum a m - Shao.maxWithZero
        (Shao.Probability.Spitzer.head a (m - 1) (Nat.sub_le m 1))) 0 ≤ (m : ℝ) * Bcap := by
    apply max_le
    · have he : Shao.prefixSum a m ≤ (m : ℝ) * Bcap := by
        rw [Shao.prefixSum_length]
        calc
          _ ≤ ∑ _ : Fin m, Bcap := Finset.sum_le_sum fun i _ => (le_abs_self _).trans (ha i)
          _ = _ := by simp
      linarith only [he, Shao.maxWithZero_nonneg
        (Shao.Probability.Spitzer.head a (m - 1) (Nat.sub_le m 1))]
    · positivity
  have hfI : Integrable (E.indicator D) P := by
    apply (integrable_const ((j : ℝ) * Bcap)).mono' (hDm.indicator hEm).aestronglyMeasurable
    filter_upwards [hSupport j] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun a _ => hD0 a) a)]
    by_cases he : a ∈ E
    · rw [Set.indicator_of_mem he]
      exact hdCap j a ha
    · rw [Set.indicator_of_notMem he]
      positivity
  have hPrefix (a : Shao.Path j) (r : ℕ) (hr : r ≤ l) :
      Shao.prefixSum a (k + k + r) = Shao.prefixSum (U a) k +
        Shao.prefixSum (V a) k + Shao.prefixSum (W a) r := by
    have h1 := hReverseTail a (k + k) h2kj (l - r) (Nat.sub_le l r)
    have h2' := hReversePrefix (W a) (l - r) (Nat.sub_le l r)
    change Shao.prefixSum (fun i : Fin l => W a (Fin.rev i)) (l - r) =
      Shao.prefixSum a j - Shao.prefixSum a (j - (l - r)) at h1
    have hi1 : j - (l - r) = k + k + r := by dsimp only [l] at hr ⊢; omega
    have hi2 : l - (l - r) = r := by omega
    rw [hi1, hTotal a] at h1
    rw [hi2] at h2'
    linarith only [h1, h2']
  have hDtail (a : Shao.Path j) : D a ≤ dl (W a) := by
    let Mj : ℝ := Shao.maxWithZero (Shao.Probability.Spitzer.head a (j - 1) (Nat.sub_le j 1))
    let Ml : ℝ := Shao.maxWithZero (Shao.Probability.Spitzer.head (W a) (l - 1) (Nat.sub_le l 1))
    have hM' : Ml ≤ Mj - (Shao.prefixSum (U a) k + Shao.prefixSum (V a) k) := by
      apply (Shao.maxWithZero_le_iff _ _).2
      intro r hr
      rw [Shao.Probability.Spitzer.head_prefixSum _ _ _ _ hr]
      have hrj : k + k + r ≤ j - 1 := by dsimp only [l] at hr hl ⊢; omega
      have he := (Shao.maxWithZero_le_iff
        (Shao.Probability.Spitzer.head a (j - 1) (Nat.sub_le j 1)) Mj).1 le_rfl _ hrj
      rw [Shao.Probability.Spitzer.head_prefixSum _ _ _ _ hrj,
        hPrefix a r (by omega)] at he
      linarith only [he]
    change max (Shao.prefixSum a j - Mj) 0 ≤ max (Shao.prefixSum (W a) l - Ml) 0
    apply max_le_max _ le_rfl
    rw [hTotal]
    linarith only [hM']
  let clip : ℝ → ℝ := fun z => max (-Bcap) (min z Bcap)
  let Phi : Shao.Path k → Shao.Path l → Shao.Path k → ℝ := fun v w u =>
    Shao.prefixSum u k - x * Real.sqrt
      (max ((∑ i : Fin k, (clip (u i)) ^ 2) + Shao.energy v + Shao.energy w + q) ((n : ℝ) / 2))
  let I : Shao.Path k → Shao.Path l → Set (Shao.Path k) := fun v w =>
    {u | -(Shao.prefixSum v k + Shao.prefixSum w l) ≤ Phi v w u ∧
      Phi v w u ≤ dl w - (Shao.prefixSum v k + Shao.prefixSum w l)}
  have hSlopeSmall : 4 * x * Bcap ≤ Real.sqrt (n : ℝ) := by
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    have he := (le_div_iff₀ (show 0 < 200 * x by positivity)).1 hcap
    have hxb : 0 ≤ x * Bcap := by positivity
    nlinarith only [he, hxb]
  have hPhiData (v : Shao.Path k) (w : Shao.Path l) :
      Measurable (Phi v w) ∧
        ∀ (a : Shao.Path k) (i : Fin k) (s t : ℝ), s ≤ t →
          (1 / 2 : ℝ) * (t - s) ≤ Phi v w (Function.update a i t) - Phi v w (Function.update a i s) := by
    have he := hClipped k (n : ℝ) Bcap x (Shao.energy v + Shao.energy w + q) 0
      hnr hB.le (zero_le_one.trans hx)
      (add_nonneg (add_nonneg (Shao.energy_nonneg v) (Shao.energy_nonneg w)) hq) le_rfl hSlopeSmall
    refine ⟨?_, ?_⟩
    · simpa only [Phi, clip, add_zero, add_assoc] using he.1.measurable
    · intro a i s t hst
      simpa only [Phi, clip, add_zero, add_assoc] using (he.2.1 a i s t hst).1
  have hIMv (v : Shao.Path k) (w : Shao.Path l) : MeasurableSet (I v w) :=
    (measurableSet_le measurable_const (hPhiData v w).1).inter
      (measurableSet_le (hPhiData v w).1 measurable_const)
  have hConc (v : Shao.Path k) (w : Shao.Path l) :
      (∫ u : Shao.Path k, (I v w).indicator (fun _ => dl w) u ∂Pk) ≤
        84 / Real.sqrt (k : ℝ) * (dl w ^ 2 + beta * dl w) := by
    have he := hCoordinate k hk (Phi v w) (hPhiData v w).1 (hPhiData v w).2
      (-(Shao.prefixSum v k + Shao.prefixSum w l))
      (dl w - (Shao.prefixSum v k + Shao.prefixSum w l)) (by linarith only [hdl0 w])
    rw [integral_indicator_const _ (hIMv v w)]
    simp only [smul_eq_mul]
    have he' := mul_le_mul_of_nonneg_left he (hdl0 w)
    convert he' using 1 <;> ring
  have hIActual (a : Shao.Path j) (ha : ∀ i : Fin j, |a i| ≤ Bcap)
      (he : a ∈ E) : U a ∈ I (V a) (W a) ∧ V a ∈ I (U a) (W a) := by
    have hclipU (i : Fin k) : clip (U a i) = U a i := by
      have hi := abs_le.1 (ha ⟨i.val, by omega⟩)
      dsimp only [clip]
      rw [min_eq_left hi.2, max_eq_right hi.1]
    have hclipV (i : Fin k) : clip (V a i) = V a i := by
      have hi := abs_le.1 (ha ⟨k + i.val, by omega⟩)
      dsimp only [clip]
      rw [min_eq_left hi.2, max_eq_right hi.1]
    have hclipUSum : (∑ i : Fin k, (clip (U a i)) ^ 2) = Shao.energy (U a) := by
      simp only [hclipU, Shao.energy]
    have hclipVSum : (∑ i : Fin k, (clip (V a i)) ^ 2) = Shao.energy (V a) := by
      simp only [hclipV, Shao.energy]
    have hF1 : F a = Phi (V a) (W a) (U a) + Shao.prefixSum (V a) k + Shao.prefixSum (W a) l := by
      dsimp only [F, Phi]
      rw [hTotal, hEnergy, hclipUSum]
      ring
    have hF2 : F a = Phi (U a) (W a) (V a) + Shao.prefixSum (U a) k + Shao.prefixSum (W a) l := by
      dsimp only [F, Phi]
      rw [hTotal, hEnergy, hclipVSum]
      have hcomm : Shao.energy (U a) + Shao.energy (V a) + Shao.energy (W a) + q =
          Shao.energy (V a) + Shao.energy (U a) + Shao.energy (W a) + q := by ring
      rw [hcomm]
      ring
    exact ⟨⟨by linarith only [he.1, hF1], by linarith only [he.2.1, hF1, hDtail a]⟩,
      ⟨by linarith only [he.1, hF2], by linarith only [he.2.1, hF2, hDtail a]⟩⟩
  let G (M : Set (Shao.Path k)) (Z : Set (Shao.Path l))
      (p : (Shao.Path k × Shao.Path k) × Shao.Path l) : ℝ :=
    if p.1.2 ∈ M ∧ p.2 ∈ Z then (I p.1.2 p.2).indicator (fun _ => dl p.2) p.1.1 else 0
  have hGIData (M : Set (Shao.Path k)) (hMset : MeasurableSet M)
      (Z : Set (Shao.Path l)) (hZset : MeasurableSet Z) :
      Measurable (G M Z) ∧ Integrable (G M Z) R ∧
        (∫ p, G M Z p ∂R) ≤
          84 / Real.sqrt (k : ℝ) * Pk.real M *
            (∫ w : Shao.Path l, Z.indicator (fun w => dl w ^ 2 + beta * dl w) w ∂Pl) := by
    have hPhiM : Measurable (fun p : (Shao.Path k × Shao.Path k) × Shao.Path l =>
        Phi p.1.2 p.2 p.1.1) := by
      dsimp only [Phi, clip, Shao.prefixSum, Shao.energy]
      fun_prop
    have hIM : MeasurableSet {p : (Shao.Path k × Shao.Path k) × Shao.Path l |
        p.1.1 ∈ I p.1.2 p.2} :=
      (measurableSet_le (((Shao.measurable_prefixSum k).comp (measurable_snd.comp measurable_fst)).add
        ((Shao.measurable_prefixSum l).comp measurable_snd)).neg hPhiM).inter
        (measurableSet_le hPhiM ((hM.1.comp measurable_snd).sub
          (((Shao.measurable_prefixSum k).comp (measurable_snd.comp measurable_fst)).add
            ((Shao.measurable_prefixSum l).comp measurable_snd))))
    have hMarks : MeasurableSet {p : (Shao.Path k × Shao.Path k) × Shao.Path l |
        p.1.2 ∈ M ∧ p.2 ∈ Z} :=
      (hMset.preimage (measurable_snd.comp measurable_fst)).inter (hZset.preimage measurable_snd)
    have hGm : Measurable (G M Z) := Measurable.ite hMarks
      (Measurable.ite hIM (hM.1.comp measurable_snd) measurable_const) measurable_const
    have hG0 (p : (Shao.Path k × Shao.Path k) × Shao.Path l) : 0 ≤ G M Z p := by
      dsimp only [G]
      split_ifs
      · exact Set.indicator_nonneg (fun _ _ => hdl0 p.2) _
      · exact le_rfl
    have hGle (p : (Shao.Path k × Shao.Path k) × Shao.Path l) : G M Z p ≤ dl p.2 := by
      dsimp only [G]
      split_ifs with hm
      · by_cases hi : p.1.1 ∈ I p.1.2 p.2
        · rw [Set.indicator_of_mem hi]
        · rw [Set.indicator_of_notMem hi]
          exact hdl0 p.2
      · exact hdl0 p.2
    have hGI : Integrable (G M Z) R := by
      apply (integrable_const ((l : ℝ) * Bcap)).mono' hGm.aestronglyMeasurable
      filter_upwards [(measurePreserving_snd (μ := Pk.prod Pk) (ν := Pl)).quasiMeasurePreserving.ae (hSupport l)] with p hp
      rw [Real.norm_eq_abs, abs_of_nonneg (hG0 p)]
      exact (hGle p).trans (hdCap l p.2 hp)
    have hSecI (w : Shao.Path l) : Integrable (fun uv : Shao.Path k × Shao.Path k => G M Z (uv, w))
        (Pk.prod Pk) := by
      apply (integrable_const (dl w)).mono'
        (hGm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      exact ae_of_all _ fun uv => by
        change ‖G M Z (uv, w)‖ ≤ dl w
        rw [Real.norm_eq_abs, abs_of_nonneg (hG0 (uv, w))]
        exact hGle (uv, w)
    have hInner (w : Shao.Path l) :
        (∫ uv : Shao.Path k × Shao.Path k, G M Z (uv, w) ∂Pk.prod Pk) ≤
          Z.indicator (fun w => 84 / Real.sqrt (k : ℝ) * Pk.real M *
            (dl w ^ 2 + beta * dl w)) w := by
      by_cases hw : w ∈ Z
      · rw [Set.indicator_of_mem hw, integral_prod_symm _ (hSecI w)]
        have hInnerEach (v : Shao.Path k) :
            (∫ u : Shao.Path k, G M Z ((u, v), w) ∂Pk) ≤
              M.indicator (fun _ => 84 / Real.sqrt (k : ℝ) * (dl w ^ 2 + beta * dl w)) v := by
          by_cases hv : v ∈ M
          · simp only [G, hv, hw, and_self, if_true, Set.indicator_of_mem hv]
            exact hConc v w
          · simp only [G, hv, false_and, if_false, integral_zero, Set.indicator_of_notMem hv, le_refl]
        calc
          _ ≤ ∫ v : Shao.Path k, M.indicator
              (fun _ => 84 / Real.sqrt (k : ℝ) * (dl w ^ 2 + beta * dl w)) v ∂Pk :=
            integral_mono (hSecI w).integral_prod_right
              ((integrable_const _).indicator hMset) hInnerEach
          _ = _ := by
            rw [integral_indicator_const _ hMset]
            simp only [smul_eq_mul]
            ring
      · rw [Set.indicator_of_notMem hw]
        have heq : (fun uv : Shao.Path k × Shao.Path k => G M Z (uv, w)) = 0 := by
          funext uv
          simp only [G, hw, and_false, if_false, Pi.zero_apply]
        rw [heq]
        change (∫ _uv : Shao.Path k × Shao.Path k, (0 : ℝ) ∂Pk.prod Pk) ≤ 0
        simp only [integral_zero, le_refl]
    refine ⟨hGm, hGI, ?_⟩
    calc
      _ = ∫ w : Shao.Path l, ∫ uv : Shao.Path k × Shao.Path k, G M Z (uv, w) ∂Pk.prod Pk ∂Pl :=
        integral_prod_symm _ hGI
      _ ≤ ∫ w : Shao.Path l, Z.indicator (fun w =>
          84 / Real.sqrt (k : ℝ) * Pk.real M * (dl w ^ 2 + beta * dl w)) w ∂Pl :=
        integral_mono hGI.integral_prod_right
          ((hM.2.1.const_mul _).indicator hZset) hInner
      _ = _ := by
        have heq : Z.indicator (fun w => 84 / Real.sqrt (k : ℝ) * Pk.real M *
            (dl w ^ 2 + beta * dl w)) =
              (fun w => 84 / Real.sqrt (k : ℝ) * Pk.real M *
                Z.indicator (fun w => dl w ^ 2 + beta * dl w) w) := by
          funext w
          by_cases hw : w ∈ Z <;> simp [hw]
        rw [heq, integral_const_mul]
  let h : ℝ := A / 3
  let RareK : Set (Shao.Path k) := {u | h ≤ Shao.prefixSum u k}
  let RareL : Set (Shao.Path l) := {w | h ≤ Shao.prefixSum w l}
  have hRareK : MeasurableSet RareK := measurableSet_le measurable_const (Shao.measurable_prefixSum k)
  have hRareL : MeasurableSet RareL := measurableSet_le measurable_const (Shao.measurable_prefixSum l)
  have hA24 : 24 * Bcap ≤ A := (le_max_left _ _).trans hA
  have hA3 : 3 * Real.sqrt (j : ℝ) ≤ A := (le_max_right _ _).trans hA
  have hAp : 0 < A := (mul_pos (by norm_num) hB).trans_le hA24
  have hhp : 0 < h := by dsimp only [h]; positivity
  have hhB : 8 * Bcap ≤ h := by dsimp only [h]; linarith only [hA24]
  have hhL : Real.sqrt (l : ℝ) ≤ h := by
    have he : Real.sqrt (l : ℝ) ≤ Real.sqrt (j : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hlj)
    dsimp only [h]
    linarith only [he, hA3]
  let Rate : ℝ := Real.exp (-(A / (72 * Bcap)) * Real.log (1 + A * Bcap / (j : ℝ)))
  have hRate0 : 0 ≤ Rate := (Real.exp_pos _).le
  have hLogThird (s : ℝ) (hs0 : 0 ≤ s) :
      Real.log (1 + s) / 3 ≤ Real.log (1 + s / 3) := by
    have hsq : 1 + s ≤ (1 + s / 3) ^ 3 := by
      have hs3 : 0 ≤ s ^ 3 := pow_nonneg hs0 3
      nlinarith only [sq_nonneg s, hs3]
    have he := Real.log_le_log (show 0 < 1 + s by linarith only [hs0]) hsq
    rw [Real.log_pow] at he
    linarith only [he]
  have hCompare (m : ℕ) (hm : 0 < m) (hmj : m ≤ j) (c : ℝ) (hc : 0 < c) (hc8 : c ≤ 8) :
      Real.exp (-(h / (c * Bcap)) * Real.log (1 + Bcap * h / (m : ℝ))) ≤ Rate := by
    have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
    have hmjr : (m : ℝ) ≤ (j : ℝ) := by exact_mod_cast hmj
    have hden : A * Bcap / (j : ℝ) / 3 ≤ Bcap * h / (m : ℝ) := by
      have he := div_le_div_of_nonneg_left (show 0 ≤ Bcap * h by positivity) hmr hmjr
      convert he using 1 <;> dsimp only [h] <;> ring
    have hlogden : Real.log (1 + A * Bcap / (j : ℝ) / 3) ≤
        Real.log (1 + Bcap * h / (m : ℝ)) :=
      Real.log_le_log (by positivity) (by linarith only [hden])
    have hlog : Real.log (1 + A * Bcap / (j : ℝ)) / 3 ≤
        Real.log (1 + Bcap * h / (m : ℝ)) :=
      (hLogThird (A * Bcap / (j : ℝ)) (by positivity)).trans hlogden
    have hlog0 : 0 ≤ Real.log (1 + A * Bcap / (j : ℝ)) :=
      Real.log_nonneg (by
        have hp : 0 ≤ A * Bcap / (j : ℝ) := by positivity
        linarith only [hp])
    have hcoef : A / (72 * Bcap) ≤ h / (c * Bcap) / 3 := by
      have hden : 9 * c * Bcap ≤ 72 * Bcap := by
        have he := mul_le_mul_of_nonneg_right hc8 hB.le
        nlinarith only [he]
      have he := div_le_div_of_nonneg_left hAp.le (show 0 < 9 * c * Bcap by positivity) hden
      apply he.trans_eq
      dsimp only [h]
      ring
    apply Real.exp_le_exp.2
    have he1 := mul_le_mul_of_nonneg_left hlog (show 0 ≤ h / (c * Bcap) by positivity)
    have he2 := mul_le_mul_of_nonneg_right hcoef hlog0
    nlinarith only [he1, he2]
  have hPK : Pk.real RareK ≤ Rate := by
    have hsub : RareK ⊆ {u : Shao.Path k | h ≤ Shao.maxWithZero u} := by
      intro u hu
      exact hu.trans ((Shao.maxWithZero_le_iff u _).1 le_rfl k le_rfl)
    exact (measureReal_mono hsub).trans
      ((ers_iid_bennett_maximal_tail rho Bcap hB hs hmean hsecond k hk h hhp.le).2.trans
        (hCompare k hk hkj 2 (by norm_num) (by norm_num)))
  have hRL : (∫ w : Shao.Path l, RareL.indicator (fun w => dl w ^ 2 + beta * dl w) w ∂Pl) ≤
      CR * beta / Real.sqrt (l : ℝ) * Rate := by
    have he := (hM.2.2.2 h (max_le hhB hhL)).2.2
    exact he.trans (mul_le_mul_of_nonneg_left (hCompare l hl hlj 8 (by norm_num) le_rfl) (by positivity))
  let Swap : (Shao.Path k × Shao.Path k) × Shao.Path l → (Shao.Path k × Shao.Path k) × Shao.Path l :=
    fun p => ((p.1.2, p.1.1), p.2)
  have hSwapMP : MeasurePreserving Swap R R :=
    (Measure.measurePreserving_swap (μ := Pk) (ν := Pk)).prod (MeasurePreserving.id Pl)
  let G2 := G RareK Set.univ
  let G3 := G Set.univ RareL
  have hG2 := hGIData RareK hRareK Set.univ MeasurableSet.univ
  have hG3 := hGIData Set.univ MeasurableSet.univ RareL hRareL
  have hG20 (p : (Shao.Path k × Shao.Path k) × Shao.Path l) : 0 ≤ G2 p := by
    dsimp only [G2, G]
    split_ifs <;> first | exact Set.indicator_nonneg (fun _ _ => hdl0 p.2) _ | exact le_rfl
  have hG30 (p : (Shao.Path k × Shao.Path k) × Shao.Path l) : 0 ≤ G3 p := by
    dsimp only [G3, G]
    split_ifs <;> first | exact Set.indicator_nonneg (fun _ _ => hdl0 p.2) _ | exact le_rfl
  have hPoint : ∀ᵐ a : Shao.Path j ∂P,
      E.indicator D a ≤ G2 (Swap (Split a)) + G2 (Split a) + G3 (Split a) := by
    filter_upwards [hSupport j] with a ha
    by_cases he : a ∈ E
    · have hI := hIActual a ha he
      have hRare : U a ∈ RareK ∨ V a ∈ RareK ∨ W a ∈ RareL := by
        by_contra hr
        push_neg at hr
        have h1 : Shao.prefixSum (U a) k < h := lt_of_not_ge hr.1
        have h2' : Shao.prefixSum (V a) k < h := lt_of_not_ge hr.2.1
        have h3 : Shao.prefixSum (W a) l < h := lt_of_not_ge hr.2.2
        have hend := he.2.2
        rw [hTotal] at hend
        dsimp only [h] at h1 h2' h3
        linarith only [h1, h2', h3, hend]
      rw [Set.indicator_of_mem he]
      rcases hRare with h1 | h2' | h3
      · have hVal : G2 (Swap (Split a)) = dl (W a) := by
          simp only [G2, G, Split, Swap, h1, Set.mem_univ, and_self, if_true,
            Set.indicator_of_mem hI.2]
        rw [hVal]
        linarith only [hDtail a, hG20 (Split a), hG30 (Split a)]
      · have hVal : G2 (Split a) = dl (W a) := by
          simp only [G2, G, Split, h2', Set.mem_univ, and_self, if_true,
            Set.indicator_of_mem hI.1]
        rw [hVal]
        linarith only [hDtail a, hG20 (Swap (Split a)), hG30 (Split a)]
      · have hVal : G3 (Split a) = dl (W a) := by
          simp only [G3, G, Split, h3, Set.mem_univ, and_self, if_true,
            Set.indicator_of_mem hI.1]
        rw [hVal]
        linarith only [hDtail a, hG20 (Swap (Split a)), hG20 (Split a)]
    · rw [Set.indicator_of_notMem he]
      exact add_nonneg (add_nonneg (hG20 _) (hG20 _)) (hG30 _)
  have hG2Bound : (∫ p, G2 p ∂R) ≤ 84 / Real.sqrt (k : ℝ) *
      (CR * beta / Real.sqrt (l : ℝ)) * Rate := by
    have he := hG2.2.2
    simp only [Set.indicator_univ] at he
    apply he.trans
    calc
      _ ≤ 84 / Real.sqrt (k : ℝ) * Rate * (CR * beta / Real.sqrt (l : ℝ)) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hPK (by positivity)) hM.2.2.1
          (integral_nonneg fun w => add_nonneg (sq_nonneg _) (mul_nonneg hbeta0 (hdl0 w)))
          (by positivity)
      _ = _ := by ring
  have hG3Bound : (∫ p, G3 p ∂R) ≤ 84 / Real.sqrt (k : ℝ) *
      (CR * beta / Real.sqrt (l : ℝ)) * Rate := by
    have he := hG3.2.2
    simp only [probReal_univ, mul_one] at he
    apply he.trans
    have he' := mul_le_mul_of_nonneg_left hRL (show 0 ≤ 84 / Real.sqrt (k : ℝ) by positivity)
    convert he' using 1 <;> ring
  have hSwapVal : (∫ p, G2 (Swap p) ∂R) = ∫ p, G2 p ∂R := by
    have he := integral_map hSwapMP.aemeasurable hG2.1.aestronglyMeasurable
    rw [hSwapMP.map_eq] at he
    exact he.symm
  have hTotalBound : (∫ a : Shao.Path j, E.indicator D a ∂P) ≤
      3 * (84 / Real.sqrt (k : ℝ) * (CR * beta / Real.sqrt (l : ℝ)) * Rate) := by
    have hSumI := ((hSwapMP.integrable_comp_of_integrable hG2.2.1).add hG2.2.1).add hG3.2.1
    have hSumM := ((hG2.1.comp hSwapMP.measurable).add hG2.1).add hG3.1
    calc
      _ ≤ ∫ a : Shao.Path j, G2 (Swap (Split a)) + G2 (Split a) + G3 (Split a) ∂P :=
        integral_mono_ae hfI (hTripleMP.integrable_comp_of_integrable hSumI) hPoint
      _ = ∫ p, G2 (Swap p) + G2 p + G3 p ∂R := by
        have he := integral_map hTripleMP.aemeasurable hSumM.aestronglyMeasurable
        rw [hTripleMP.map_eq] at he
        exact he.symm
      _ = (∫ p, G2 (Swap p) ∂R) + (∫ p, G2 p ∂R) + (∫ p, G3 p ∂R) := by
        have hSwapI : Integrable (fun p => G2 (Swap p)) R :=
          hSwapMP.integrable_comp_of_integrable hG2.2.1
        have h2I : Integrable (fun p => G2 p) R := hG2.2.1
        have h3I : Integrable (fun p => G3 p) R := hG3.2.1
        have hPairI : Integrable (fun p => G2 (Swap p) + G2 p) R := hSwapI.add h2I
        rw [integral_add hPairI h3I, integral_add hSwapI h2I]
      _ ≤ _ := by rw [hSwapVal]; nlinarith only [hG2Bound, hG3Bound]
  have hRootsK : Real.sqrt (j : ℝ) ≤ 2 * Real.sqrt (k : ℝ) := by
    have hsqj := Real.sq_sqrt hjr.le
    have hsqk := Real.sq_sqrt hkr.le
    nlinarith only [hsqj, hsqk, hkquarter, Real.sqrt_nonneg (j : ℝ), Real.sqrt_nonneg (k : ℝ)]
  have hRootsL : Real.sqrt (j : ℝ) ≤ 2 * Real.sqrt (l : ℝ) := by
    have hsqj := Real.sq_sqrt hjr.le
    have hsql := Real.sq_sqrt hlr.le
    nlinarith only [hsqj, hsql, hlquarter, Real.sqrt_nonneg (j : ℝ), Real.sqrt_nonneg (l : ℝ)]
  have hRoots : (j : ℝ) ≤ 4 * (Real.sqrt (k : ℝ) * Real.sqrt (l : ℝ)) := by
    have he := mul_le_mul hRootsK hRootsL (Real.sqrt_nonneg (j : ℝ))
      (show 0 ≤ 2 * Real.sqrt (k : ℝ) by positivity)
    rw [Real.mul_self_sqrt hjr.le] at he
    nlinarith only [he]
  have hInv : 1 / (Real.sqrt (k : ℝ) * Real.sqrt (l : ℝ)) ≤ 4 / (j : ℝ) := by
    apply (div_le_div_iff₀ (mul_pos hrk hrl) hjr).2
    simpa only [one_mul] using hRoots
  refine ⟨hFm, hEm, hfI, hTotalBound.trans ?_⟩
  calc
    _ = 252 * CR * beta * Rate * (1 / (Real.sqrt (k : ℝ) * Real.sqrt (l : ℝ))) := by ring
    _ ≤ 252 * CR * beta * Rate * (4 / (j : ℝ)) := mul_le_mul_of_nonneg_left hInv (by positivity)
    _ ≤ C * beta / (j : ℝ) * Rate := by
      have hc : 1008 * CR ≤ C := by dsimp only [C]; linarith only [hCR0]
      have he := mul_le_mul_of_nonneg_right hc (show 0 ≤ beta / (j : ℝ) * Rate by positivity)
      convert he using 1 <;> ring

end Shao.Probability.SourceActualRecordEndstrip
