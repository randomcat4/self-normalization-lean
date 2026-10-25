import Shao.Probability.SourceWeightedPrefixWall
import Shao.C2.ActualOneWallRecordEnvelope
import Shao.Probability.SpitzerFinite

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
noncomputable section
namespace Shao.Probability.SourceWeightedRecordStrip
open MeasureTheory ProbabilityTheory
open Shao.C2.ActualOneWallRecordEnvelope
open scoped BigOperators Classical

private theorem wrs_cyclic_record_identity
    (N : ℕ) (hN : 0 < N) (a : Shao.Path N) :
    let D : Shao.Path N → ℝ := fun v =>
      max (Shao.prefixSum v N - Shao.maxWithZero
        (Shao.Probability.Spitzer.head v (N - 1) (Nat.sub_le N 1))) 0
    let rotate : Fin N → Shao.Path N → Shao.Path N := fun j v i =>
      v ⟨(i.val + j.val) % N, Nat.mod_lt _ hN⟩
    (∑ j : Fin N, D (rotate j a)) = max (Shao.prefixSum a N) 0 ∧
      (∀ j : Fin N, circularWitness (rotate j a) = circularWitness a) := by
  classical
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let D : Shao.Path N → ℝ := fun v =>
    max (Shao.prefixSum v N - Shao.maxWithZero
      (Shao.Probability.Spitzer.head v (N - 1) (Nat.sub_le N 1))) 0
  let rotate : Fin N → Shao.Path N → Shao.Path N := fun j v i => v (i + j)
  change (∑ j : Fin N, D (rotate j a)) = max (Shao.prefixSum a N) 0 ∧
    (∀ j : Fin N, circularWitness (rotate j a) = circularWitness a)
  have htotal (j : Fin N) :
      Shao.prefixSum (rotate j a) N = Shao.prefixSum a N := by
    simp only [Shao.prefixSum_length]
    exact Equiv.sum_comp (Equiv.addRight j) a
  have hcycle : (∑ j : Fin N, D (rotate j a)) = max (Shao.prefixSum a N) 0 := by
    cases N with
    | zero => omega
    | succ n =>
      let M : Fin (n + 1) → ℝ := fun j => Shao.maxWithZero
        (Shao.Probability.Spitzer.head (rotate j a) n (by omega))
      have hhead (j : Fin (n + 1)) (k : ℕ) (hk : k ≤ n) :
          Shao.prefixSum (Shao.Probability.Spitzer.head (rotate j a) n (by omega)) k =
            Shao.prefixSum (rotate j a) k :=
        Shao.Probability.Spitzer.head_prefixSum _ _ _ _ hk
      have hfull (j : Fin (n + 1)) :
          Shao.maxWithZero (rotate j a) = max (M j) (Shao.prefixSum a (n + 1)) := by
        apply le_antisymm
        · apply (Shao.maxWithZero_le_iff _ _).mpr
          intro k hk
          by_cases hkn : k ≤ n
          · rw [← hhead j k hkn]
            exact ((Shao.maxWithZero_le_iff _ _).mp le_rfl k hkn).trans
              (le_max_left _ _)
          · have heq : k = n + 1 := by omega
            rw [heq, htotal]
            exact le_max_right _ _
        · apply max_le
          · apply (Shao.maxWithZero_le_iff _ _).mpr
            intro k hk
            rw [hhead j k hk]
            exact (Shao.maxWithZero_le_iff _ _).mp le_rfl k (by omega)
          · rw [← htotal j]
            exact (Shao.maxWithZero_le_iff _ _).mp le_rfl (n + 1) le_rfl
      have htail (j : Fin (n + 1)) :
          (fun i : Fin n => rotate j a i.succ) =
            Shao.Probability.Spitzer.head (rotate (j + 1) a) n (by omega) := by
        funext i
        change a (i.succ + j) = a (i.castSucc + (j + 1))
        congr 1
        have hi : i.succ = i.castSucc + 1 := by
          cases n with
          | zero => exact i.elim0
          | succ n =>
            apply Fin.ext
            simp only [Fin.val_succ, Fin.val_add, Fin.val_castSucc, Fin.val_one]
            rw [Nat.mod_eq_of_lt (by omega)]
        rw [hi]
        ac_rfl
      run_tac
        let n : Lean.Name := Lean.mkPrivateNameCore ("Shao.Basic.Lindley".toName)
          ("Shao.maxWithZero_cons".toName)
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          have $(Lean.mkIdent ("hCons".toName)) := @$(Lean.mkIdent n)))
      have hstep (j : Fin (n + 1)) :
          max (M j) (Shao.prefixSum a (n + 1)) = max 0 (a j + M (j + 1)) := by
        rw [← hfull j, hCons, htail]
        change max 0 (a (0 + j) + M (j + 1)) = _
        rw [zero_add]
      by_cases hS : 0 < Shao.prefixSum a (n + 1)
      · have hD (j : Fin (n + 1)) :
            D (rotate j a) = a j + M (j + 1) - M j := by
          have hM : 0 ≤ M j := Shao.maxWithZero_nonneg _
          have hmaxpos : 0 < max (M j) (Shao.prefixSum a (n + 1)) :=
            hS.trans_le (le_max_right _ _)
          have hapos : 0 ≤ a j + M (j + 1) := by
            by_contra hn
            rw [hstep j, max_eq_left (le_of_not_ge hn)] at hmaxpos
            exact (lt_irrefl 0) hmaxpos
          have hs := hstep j
          rw [max_eq_right hapos] at hs
          dsimp only [D]
          rw [htotal]
          change max (Shao.prefixSum a (n + 1) - M j) 0 = _
          by_cases hm : M j ≤ Shao.prefixSum a (n + 1)
          · rw [max_eq_right hm] at hs
            rw [max_eq_left (sub_nonneg.mpr hm)]
            linarith only [hs]
          · have hm' := le_of_not_ge hm
            rw [max_eq_left hm'] at hs
            rw [max_eq_right (sub_nonpos.mpr hm')]
            linarith only [hs]
        simp_rw [hD]
        have hMsum := Equiv.sum_comp (Equiv.addRight (1 : Fin (n + 1))) M
        change (∑ j : Fin (n + 1), M (j + 1)) = ∑ j : Fin (n + 1), M j at hMsum
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hMsum,
          add_sub_cancel_right, ← Shao.prefixSum_length, max_eq_left hS.le]
      · have hS' : Shao.prefixSum a (n + 1) ≤ 0 := le_of_not_gt hS
        rw [max_eq_right hS']
        apply Finset.sum_eq_zero
        intro j _
        dsimp only [D]
        rw [htotal]
        apply max_eq_right
        exact sub_nonpos.mpr (hS'.trans (Shao.maxWithZero_nonneg _))
  refine ⟨hcycle, ?_⟩
  intro j
  have harc (i : Fin N) (k : Fin (N + 1)) :
      (∑ q ∈ Finset.range k.val,
        rotate j a ⟨(i.val + q) % N, Nat.mod_lt _ hN⟩) =
      ∑ q ∈ Finset.range k.val,
        a ⟨((i + j).val + q) % N, Nat.mod_lt _ hN⟩ := by
    apply Finset.sum_congr rfl
    intro q hq
    dsimp only [rotate]
    congr 1
    apply Fin.ext
    simp only [Fin.val_add]
    calc
      _ = (i.val + q + j.val) % N := by simp only [Nat.add_mod, Nat.mod_mod]
      _ = (i.val + j.val + q) % N := by congr 1; omega
      _ = _ := by simp only [Nat.add_mod, Nat.mod_mod]
  unfold circularWitness
  rw [dif_pos hN, dif_pos hN, htotal]
  congr 1
  ext w
  constructor
  · rintro ⟨i, k, hw⟩
    exact ⟨i + j, k, by simpa only [harc] using hw⟩
  · rintro ⟨i, k, hw⟩
    obtain ⟨i', hi'⟩ := (Equiv.addRight j).surjective i
    change i' + j = i at hi'
    refine ⟨i', k, ?_⟩
    rw [harc, hi']
    exact hw

theorem actual_circular_weighted_record_moment :
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
          let L : Shao.Path N → ℝ := fun a => circularWitness a
          ∀ theta : ℝ, 0 ≤ theta → theta * Bcap ≤ 1 / 100 →
            1 ≤ theta * Real.sqrt (N : ℝ) →
            Measurable D ∧ Measurable L ∧
              Integrable (fun a => (D a ^ 2 + beta * D a) *
                Real.exp (theta * L a)) P ∧
              (∫ a : Shao.Path N, (D a ^ 2 + beta * D a) *
                Real.exp (theta * L a) ∂P) ≤
                C * beta / Real.sqrt (N : ℝ) *
                  (1 + (N : ℝ) * theta ^ 2) *
                  Real.exp ((253 / 500 : ℝ) * (N : ℝ) * theta ^ 2 +
                    C * (N : ℝ) * theta ^ 3 * beta + C * theta * Bcap) := by
  classical
  run_tac
    let n : Lean.Name := Lean.mkPrivateNameCore ("Shao.Probability.SourceWeightedPrefixWall".toName)
      ("Shao.Probability.SourceWeightedPrefixWall.pww_weighted_closed_lower_survival".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hSurvival".toName)) := $(Lean.mkIdent n)))
  obtain ⟨CW, hCW, hOS⟩ := hSurvival
  obtain ⟨CM, hCM, hMom⟩ :=
    Shao.Probability.SourceCircularWitnessMoment.actual_circular_witness_small_parameter_moment
  let C : ℝ := 10 + 8 * CW + 10000 * CM
  have hCW0 : 0 ≤ CW := zero_le_one.trans hCW
  have hCM0 : 0 ≤ CM := zero_le_one.trans hCM
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hCW0, hCM0]
  refine ⟨C, hC, ?_⟩
  intro rho hprob Bcap hB hs hmean hvar beta N hN P D L theta ht hsmall hlarge
  let d : (m : ℕ) → Shao.Path m → ℝ := fun m v =>
    max (Shao.prefixSum v m - Shao.maxWithZero
      (Shao.Probability.Spitzer.head v (m - 1) (Nat.sub_le m 1))) 0
  let w : (m : ℕ) → Shao.Path m → ℝ := fun _ v => circularWitness v
  let law : (m : ℕ) → Measure (Shao.Path m) := fun m =>
    Measure.pi (fun _ : Fin m => rho)
  have hLawProb (m : ℕ) : IsProbabilityMeasure (law m) := by
    dsimp only [law]
    infer_instance
  have hPower (r : ℕ) : Integrable (fun z : ℝ => |z| ^ r) rho := by
    apply (integrable_const (Bcap ^ r)).mono' (by fun_prop)
    filter_upwards [hs] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg z) r)]
    exact pow_le_pow_left₀ (abs_nonneg z) hz r
  have h2 : Integrable (fun z : ℝ => z ^ 2) rho := by
    simpa only [sq_abs] using hPower 2
  have hbeta1 : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one
      rho h2 (hPower 3) hvar
  have hbeta0 : 0 ≤ beta := zero_le_one.trans hbeta1
  have hBsq : 1 ≤ Bcap ^ 2 := by
    calc
      _ = ∫ z : ℝ, z ^ 2 ∂rho := hvar.symm
      _ ≤ ∫ _ : ℝ, Bcap ^ 2 ∂rho := by
        apply integral_mono_ae h2 (integrable_const _)
        filter_upwards [hs] with z hz
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z) hz 2
      _ = _ := by simp
  have hB1 : 1 ≤ Bcap := by nlinarith only [hBsq, hB]
  have hNne1 : N ≠ 1 := by
    intro heq
    have htheta1 : 1 ≤ theta := by simpa only [heq, Nat.cast_one, Real.sqrt_one, mul_one] using hlarge
    have hh := mul_nonneg ht (sub_nonneg.mpr hB1)
    nlinarith only [hsmall, htheta1, hh]
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNr
  have htp : 0 < theta := by
    by_contra hh
    have hz : theta = 0 := le_antisymm (le_of_not_gt hh) ht
    simp only [hz, zero_mul] at hlarge
    linarith only [hlarge]
  run_tac
    let n : Lean.Name := Lean.mkPrivateNameCore ("Shao.Probability.SourceCircularWitnessMoment".toName)
      ("Shao.Probability.SourceCircularWitnessMoment.cwm_path_extrema_geometry".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hGeom".toName)) := $(Lean.mkIdent n)))
  have hwm (m : ℕ) : Measurable (w m) := (hMom rho Bcap hB hs hmean hvar m).1
  have hdm (m : ℕ) : Measurable (d m) := by
    have hh : Measurable (fun v : Shao.Path m =>
        Shao.Probability.Spitzer.head v (m - 1) (Nat.sub_le m 1)) :=
      measurable_pi_iff.2 fun i => measurable_pi_apply _
    exact ((Shao.measurable_prefixSum m).sub (Shao.measurable_maxWithZero.comp hh)).max
      measurable_const
  have hgeometry (m : ℕ) (v : Shao.Path m) :
      0 ≤ w m v ∧ w m v ≤ ∑ i : Fin m, |v i| ∧
        |Shao.prefixSum v m| ≤ w m v := by
    rcases (hGeom m).2.2.2 v with ⟨hL0, hLu, hA0, hAu, hR0, hRu, hformula, hneg⟩
    let A0 : ℝ := sSup {z : ℝ | ∃ u t : Fin (m + 1), u.val ≤ t.val ∧
      z = Shao.prefixSum v t.val - Shao.prefixSum v u.val}
    let R0 : ℝ := sSup {z : ℝ | ∃ u t : Fin (m + 1), u.val ≤ t.val ∧
      z = Shao.prefixSum v u.val - Shao.prefixSum v t.val}
    have hAnn : 0 ≤ A0 := hA0
    have hRnn : 0 ≤ R0 := hR0
    have hFormula : w m v = max (Shao.prefixSum v m + 2 * R0)
        (2 * A0 - Shao.prefixSum v m) := hformula
    refine ⟨hL0, hLu, abs_le.mpr ⟨?_, ?_⟩⟩
    · have hh : 2 * A0 - Shao.prefixSum v m ≤ w m v := by
        rw [hFormula]
        exact le_max_right _ _
      linarith only [hh, hAnn]
    · have hh : Shao.prefixSum v m + 2 * R0 ≤ w m v := by
        rw [hFormula]
        exact le_max_left _ _
      linarith only [hh, hRnn]
  have hd0 (m : ℕ) (v : Shao.Path m) : 0 ≤ d m v := le_max_right _ _
  have hdSum (m : ℕ) (v : Shao.Path m) : d m v ≤ ∑ i : Fin m, |v i| := by
    apply max_le
    · have hsabs : Shao.prefixSum v m ≤ ∑ i : Fin m, |v i| := by
        rw [Shao.prefixSum_length]
        exact Finset.sum_le_sum fun i _ => le_abs_self (v i)
      linarith only [hsabs, Shao.maxWithZero_nonneg
        (Shao.Probability.Spitzer.head v (m - 1) (Nat.sub_le m 1))]
    · exact Finset.sum_nonneg fun i _ => abs_nonneg (v i)
  have hSupport (m : ℕ) : ∀ᵐ v : Shao.Path m ∂law m, ∀ i : Fin m, |v i| ≤ Bcap := by
    apply ae_all_iff.2
    intro i
    exact (measurePreserving_eval (fun _ : Fin m => rho) i).quasiMeasurePreserving.ae hs
  have hSumCap (m : ℕ) (v : Shao.Path m) (hv : ∀ i : Fin m, |v i| ≤ Bcap) :
      (∑ i : Fin m, |v i|) ≤ (m : ℝ) * Bcap := by
    calc
      _ ≤ ∑ _ : Fin m, Bcap := Finset.sum_le_sum fun i _ => hv i
      _ = _ := by simp
  have hInt (m r : ℕ) : Integrable
      (fun v : Shao.Path m => d m v ^ r * Real.exp (theta * w m v)) (law m) := by
    letI : IsProbabilityMeasure (law m) := hLawProb m
    apply (integrable_const (((m : ℝ) * Bcap) ^ r *
      Real.exp (theta * ((m : ℝ) * Bcap)))).mono'
        (((hdm m).pow_const r).mul ((measurable_const.mul (hwm m)).exp)).aestronglyMeasurable
    filter_upwards [hSupport m] with v hv
    rw [Real.norm_eq_abs]
    change |d m v ^ r * Real.exp (theta * w m v)| ≤
      ((m : ℝ) * Bcap) ^ r * Real.exp (theta * ((m : ℝ) * Bcap))
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg (hd0 m v) r) (Real.exp_pos _).le)]
    exact mul_le_mul (pow_le_pow_left₀ (hd0 m v) ((hdSum m v).trans (hSumCap m v hv)) r)
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
        ((hgeometry m v).2.1.trans (hSumCap m v hv)) ht))
      (Real.exp_pos _).le (by positivity)
  have hDmeas : Measurable D := hdm N
  have hLmeas : Measurable L := hwm N
  have hI1 : Integrable (fun v => D v * Real.exp (theta * L v)) P := by
    simpa only [pow_one] using hInt N 1
  have hI2 : Integrable (fun v => D v ^ 2 * Real.exp (theta * L v)) P := hInt N 2
  have hI : Integrable (fun v => (D v ^ 2 + beta * D v) * Real.exp (theta * L v)) P := by
    convert hI2.add (hI1.const_mul beta) using 1
    funext v
    simp only [Pi.add_apply]
    ring
  refine ⟨hDmeas, hLmeas, hI, ?_⟩
  let A : ℝ := beta / Real.sqrt (N : ℝ) * (1 + (N : ℝ) * theta ^ 2) *
    Real.exp ((253 / 500 : ℝ) * (N : ℝ) * theta ^ 2 +
      C * (N : ℝ) * theta ^ 3 * beta + C * theta * Bcap)
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hFirst : beta * (∫ v : Shao.Path N, D v * Real.exp (theta * L v) ∂P) ≤
      (4000 * CM) * A := by
    letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
    let rot : Fin N → Shao.Path N → Shao.Path N := fun j v i => v (i + j)
    have hRotMP (j : Fin N) : MeasurePreserving (rot j) P P := by
      exact (measurePreserving_piCongrLeft (fun _ : Fin N => rho) (Equiv.addRight j)).symm
    have hRotInt (j : Fin N) :
        Integrable (fun v : Shao.Path N => D (rot j v) * Real.exp (theta * L (rot j v))) P :=
      (hRotMP j).integrable_comp_of_integrable hI1
    have hRotIntegral (j : Fin N) :
        (∫ v : Shao.Path N, D (rot j v) * Real.exp (theta * L (rot j v)) ∂P) =
          ∫ v : Shao.Path N, D v * Real.exp (theta * L v) ∂P := by
      have hh :
          (∫ v : Shao.Path N, D v * Real.exp (theta * L v) ∂P.map (rot j)) =
            ∫ v : Shao.Path N, D (rot j v) * Real.exp (theta * L (rot j v)) ∂P :=
        integral_map (f := fun v : Shao.Path N => D v * Real.exp (theta * L v))
          (hRotMP j).aemeasurable
          (hDmeas.mul ((measurable_const : Measurable (fun _ : Shao.Path N => theta)).mul
            hLmeas).exp).aestronglyMeasurable
      rw [(hRotMP j).map_eq] at hh
      exact hh.symm
    have hCyclic (v : Shao.Path N) :
        (∑ j : Fin N, D (rot j v) * Real.exp (theta * L (rot j v))) =
          max (Shao.prefixSum v N) 0 * Real.exp (theta * L v) := by
      have hh := wrs_cyclic_record_identity N hN v
      change (∑ j : Fin N, D (rot j v)) = max (Shao.prefixSum v N) 0 ∧
        (∀ j : Fin N, L (rot j v) = L v) at hh
      simp_rw [hh.2]
      rw [← Finset.sum_mul, hh.1]
    have hCyclicIntegral :
        (N : ℝ) * (∫ v : Shao.Path N, D v * Real.exp (theta * L v) ∂P) =
          ∫ v : Shao.Path N, max (Shao.prefixSum v N) 0 * Real.exp (theta * L v) ∂P := by
      calc
        _ = ∑ j : Fin N, ∫ v : Shao.Path N,
            D (rot j v) * Real.exp (theta * L (rot j v)) ∂P := by
              simp only [hRotIntegral, Finset.sum_const, Finset.card_univ,
                Fintype.card_fin, nsmul_eq_mul]
        _ = ∫ v : Shao.Path N, ∑ j : Fin N,
            D (rot j v) * Real.exp (theta * L (rot j v)) ∂P :=
              (integral_finsetSum _ (fun j _ => hRotInt j)).symm
        _ = _ := integral_congr_ae (ae_of_all _ hCyclic)
    let lam : ℝ := (1001 / 1000 : ℝ) * theta
    have hlam0 : 0 ≤ lam := by dsimp only [lam]; positivity
    have hlamB : lam * Bcap ≤ 1 / 10 := by
      dsimp only [lam]
      nlinarith only [hsmall]
    have hLM := (hMom rho Bcap hB hs hmean hvar N).2 lam hlam0 hlamB
    change Integrable (fun v : Shao.Path N => Real.exp (lam * L v)) P ∧
      (∫ v : Shao.Path N, Real.exp (lam * L v) ∂P) ≤
        CM * (1 + (N : ℝ) * lam ^ 2) *
          Real.exp ((1002001 / 2000000 : ℝ) * (N : ℝ) * lam ^ 2 +
            CM * (N : ℝ) * lam ^ 3 * beta) at hLM
    have hAbsorb (v : Shao.Path N) :
        max (Shao.prefixSum v N) 0 * Real.exp (theta * L v) ≤
          (1000 / theta) * Real.exp (lam * L v) := by
      have hS : max (Shao.prefixSum v N) 0 ≤ L v :=
        max_le ((le_abs_self _).trans (hgeometry N v).2.2) (hgeometry N v).1
      have hu : (theta / 1000) * L v ≤ Real.exp ((theta / 1000) * L v) :=
        (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
      have hh := mul_le_mul_of_nonneg_right hu (Real.exp_pos (theta * L v)).le
      rw [← Real.exp_add] at hh
      calc
        _ ≤ L v * Real.exp (theta * L v) :=
          mul_le_mul_of_nonneg_right hS (Real.exp_pos _).le
        _ = (1000 / theta) *
            (((theta / 1000) * L v) * Real.exp (theta * L v)) := by
              field_simp [ne_of_gt htp]
              <;> ring
        _ ≤ (1000 / theta) * Real.exp (lam * L v) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          convert hh using 1 <;> congr 1 <;> dsimp only [lam] <;> ring
    have hMarkedI : Integrable
        (fun v : Shao.Path N => max (Shao.prefixSum v N) 0 * Real.exp (theta * L v)) P := by
      have hSumI : Integrable (fun v : Shao.Path N =>
          ∑ j : Fin N, D (rot j v) * Real.exp (theta * L (rot j v))) P :=
        integrable_finsetSum Finset.univ (fun j _ => hRotInt j)
      exact hSumI.congr (ae_of_all _ hCyclic)
    have hmain := integral_mono hMarkedI (hLM.1.const_mul (1000 / theta)) hAbsorb
    rw [integral_const_mul, ← hCyclicIntegral] at hmain
    have hrootinv : 1 / ((N : ℝ) * theta) ≤ 1 / Real.sqrt (N : ℝ) := by
      apply one_div_le_one_div_of_le hroot
      have hh := mul_le_mul_of_nonneg_left hlarge hroot.le
      rw [mul_one, ← mul_assoc, mul_comm (Real.sqrt (N : ℝ)) theta,
        mul_assoc theta, Real.mul_self_sqrt hNr.le] at hh
      simpa only [mul_comm] using hh
    have hpoly : 1 + (N : ℝ) * lam ^ 2 ≤ 2 * (1 + (N : ℝ) * theta ^ 2) := by
      dsimp only [lam]
      nlinarith only [mul_nonneg hNr.le (sq_nonneg theta)]
    have hexponent :
        (1002001 / 2000000 : ℝ) * (N : ℝ) * lam ^ 2 +
            CM * (N : ℝ) * lam ^ 3 * beta ≤
          (253 / 500 : ℝ) * (N : ℝ) * theta ^ 2 +
            C * (N : ℝ) * theta ^ 3 * beta + C * theta * Bcap := by
      have hc : (1001 / 1000 : ℝ) ^ 3 * CM ≤ C := by
        dsimp only [C]
        nlinarith only [hCM0, hCW0]
      have hquad : (1002001 / 2000000 : ℝ) * (1001 / 1000 : ℝ) ^ 2 ≤ 253 / 500 := by
        norm_num
      have hhq := mul_le_mul_of_nonneg_right hquad (mul_nonneg hNr.le (sq_nonneg theta))
      have hhc := mul_le_mul_of_nonneg_right hc
        (mul_nonneg (mul_nonneg hNr.le (pow_nonneg ht 3)) hbeta0)
      have hlin : 0 ≤ C * theta * Bcap := by positivity
      dsimp only [lam]
      nlinarith only [hhq, hhc, hlin]
    have hE := Real.exp_le_exp.2 hexponent
    calc
      _ ≤ beta * (1000 / ((N : ℝ) * theta)) *
          (CM * (1 + (N : ℝ) * lam ^ 2) *
            Real.exp ((1002001 / 2000000 : ℝ) * (N : ℝ) * lam ^ 2 +
              CM * (N : ℝ) * lam ^ 3 * beta)) := by
        have hh0 := hmain.trans (mul_le_mul_of_nonneg_left hLM.2 (by positivity))
        have hh := mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hh0 hNr.le) hbeta0
        convert hh using 1 <;> field_simp [ne_of_gt hNr, ne_of_gt htp] <;> ring
      _ ≤ beta * (1000 / Real.sqrt (N : ℝ)) *
          (CM * (2 * (1 + (N : ℝ) * theta ^ 2)) *
            Real.exp ((253 / 500 : ℝ) * (N : ℝ) * theta ^ 2 +
              C * (N : ℝ) * theta ^ 3 * beta + C * theta * Bcap)) := by
        have hdiv : 1000 / ((N : ℝ) * theta) ≤ 1000 / Real.sqrt (N : ℝ) := by
          convert mul_le_mul_of_nonneg_left hrootinv (by norm_num : (0 : ℝ) ≤ 1000) using 1 <;> ring
        have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hpoly hCM0) hE
          (Real.exp_pos _).le (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hdiv hbeta0) hprod
          (by positivity) (by positivity)
      _ = (2000 * CM) * A := by dsimp only [A]; ring
      _ ≤ (4000 * CM) * A :=
        mul_le_mul_of_nonneg_right (by linarith only [hCM0]) hA0
  have hSecond : (∫ v : Shao.Path N, D v ^ 2 * Real.exp (theta * L v) ∂P) ≤
      (8 * CW) * A := by
    have hlastSum (m : ℕ) (v : Shao.Path (m + 1)) :
        Shao.prefixSum v (m + 1) =
          Shao.prefixSum (Shao.Probability.Spitzer.head v m (by omega)) m + v (Fin.last m) := by
      simp only [Shao.prefixSum_length, Fin.sum_univ_castSucc]
      rfl
    have hlastD (m : ℕ) (v : Shao.Path (m + 1)) : d (m + 1) v ≤ max (v (Fin.last m)) 0 := by
      apply max_le
      · have hh := (Shao.maxWithZero_le_iff
          (Shao.Probability.Spitzer.head v m (by omega)) _).mp le_rfl m le_rfl
        have hs' := hlastSum m v
        change Shao.prefixSum v (m + 1) -
          Shao.maxWithZero (Shao.Probability.Spitzer.head v m (by omega)) ≤ _
        linarith only [hh, hs', le_max_left (v (Fin.last m)) 0]
      · exact le_max_right _ _
    by_cases hN1 : N = 1
    · exact False.elim (hNne1 hN1)
    · obtain ⟨m, hmN⟩ : ∃ m : ℕ, N = m + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
      subst N
      have hm : 0 < m := by omega
      have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
      have hmrRoot : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmr
      let R : Measure (Shao.Path m) := law m
      let J : ℝ × Shao.Path m → Shao.Path (m + 1) := fun p =>
        Fin.snoc (fun i : Fin m => p.2 (Fin.rev i)) p.1
      have hRevMP : MeasurePreserving (fun v : Shao.Path m => fun i => v (Fin.rev i)) R R := by
        exact (measurePreserving_piCongrLeft (fun _ : Fin m => rho) Fin.revPerm).symm
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
      have hJm : Measurable J := hJMP.measurable
      have hJhead (p : ℝ × Shao.Path m) :
          Shao.Probability.Spitzer.head (J p) m (by omega) =
            (fun i : Fin m => p.2 (Fin.rev i)) := by
        funext i
        simp [J, Shao.Probability.Spitzer.head, Fin.snoc]
      run_tac
        let mod : Lean.Name := "Shao.Probability.SourceTrueEnergyStrip".toName
        let n : Lean.Name := Lean.mkPrivateNameCore mod
          ("Shao.Probability.tes_reverse_tail_prefixSum".toName)
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          have $(Lean.mkIdent ("hReversePrefix".toName)) := @$(Lean.mkIdent n)))
        let mod : Lean.Name := "Shao.Probability.SourceWeightedPrefixWall".toName
        let n : Lean.Name := Lean.mkPrivateNameCore mod
          ("Shao.Probability.SourceWeightedPrefixWall.pww_circular_witness_reversal".toName)
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          have $(Lean.mkIdent ("hReverseWitness".toName)) := $(Lean.mkIdent n)))
        let n : Lean.Name := Lean.mkPrivateNameCore mod
          ("Shao.Probability.SourceWeightedPrefixWall.pww_circular_witness_concatenation".toName)
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          have $(Lean.mkIdent ("hConcatenate".toName)) := $(Lean.mkIdent n)))
      have hReverseSum (v : Shao.Path m) (k : ℕ) (hk : k ≤ m) :
          Shao.prefixSum (fun i : Fin m => v (Fin.rev i)) k =
            Shao.prefixSum v m - Shao.prefixSum v (m - k) := by
        simpa only [Shao.Probability.Spitzer.tail, Nat.zero_add, Nat.sub_zero] using
          hReversePrefix v 0 (Nat.zero_le m) k (by simpa only [Nat.sub_zero] using hk)
      let Alive : ℝ → Set (Shao.Path m) := fun b =>
        {v | ∀ k : Fin (m + 1), -max b 0 ≤ Shao.prefixSum v k.val}
      let G : ℝ × Shao.Path m → ℝ := fun p =>
        if p.2 ∈ Alive p.1 then
          (max p.1 0) ^ 2 * Real.exp (theta * (max p.1 0 + w m p.2)) else 0
      have hAliveM : MeasurableSet {p : ℝ × Shao.Path m | p.2 ∈ Alive p.1} := by
        have heq : {p : ℝ × Shao.Path m | p.2 ∈ Alive p.1} =
            ⋂ k : Fin (m + 1), {p : ℝ × Shao.Path m |
              -max p.1 0 ≤ Shao.prefixSum p.2 k.val} := by
          ext p
          simp only [Alive, Set.mem_setOf_eq, Set.mem_iInter]
        rw [heq]
        exact MeasurableSet.iInter fun k : Fin (m + 1) =>
          measurableSet_le (measurable_fst.max (measurable_const (a := (0 : ℝ)))).neg
            ((Shao.measurable_prefixSum k.val).comp measurable_snd)
      have hGm : Measurable G := by
        have hb : Measurable (fun p : ℝ × Shao.Path m => max p.1 0) :=
          measurable_fst.max measurable_const
        have hw : Measurable (fun p : ℝ × Shao.Path m => w m p.2) :=
          (hwm m).comp measurable_snd
        have hbody : Measurable (fun p : ℝ × Shao.Path m =>
            (max p.1 0) ^ 2 * Real.exp (theta * (max p.1 0 + w m p.2))) :=
          (hb.pow_const 2).mul (measurable_const.mul (hb.add hw)).exp
        exact Measurable.ite hAliveM hbody measurable_const
      have hG0 (p : ℝ × Shao.Path m) : 0 ≤ G p := by
        dsimp only [G]
        split_ifs <;> positivity
      have hSupportProd : ∀ᵐ p : ℝ × Shao.Path m ∂rho.prod R,
          |p.1| ≤ Bcap ∧ ∀ i : Fin m, |p.2 i| ≤ Bcap := by
        filter_upwards [(measurePreserving_fst (μ := rho) (ν := R)).quasiMeasurePreserving.ae hs,
          (measurePreserving_snd (μ := rho) (ν := R)).quasiMeasurePreserving.ae (hSupport m)]
          with p hp hv
        exact ⟨hp, hv⟩
      have hGI : Integrable G (rho.prod R) := by
        apply (integrable_const (Bcap ^ 2 * Real.exp (theta * (Bcap + (m : ℝ) * Bcap)))).mono'
          hGm.aestronglyMeasurable
        filter_upwards [hSupportProd] with p hp
        rw [Real.norm_eq_abs, abs_of_nonneg (hG0 p)]
        dsimp only [G]
        split_ifs
        · have hbp : max p.1 0 ≤ Bcap := max_le ((le_abs_self _).trans hp.1) hB.le
          gcongr
          exact (hgeometry m p.2).2.1.trans (hSumCap m p.2 hp.2)
        · positivity
      have hpoint (p : ℝ × Shao.Path m) :
          d (m + 1) (J p) ^ 2 * Real.exp (theta * w (m + 1) (J p)) ≤ G p := by
        by_cases hdpos : 0 < d (m + 1) (J p)
        · have hlast : J p (Fin.last m) = p.1 := by simp [J]
          have hDlast : d (m + 1) (J p) ≤ max p.1 0 := by simpa only [hlast] using hlastD m (J p)
          have hbp : 0 ≤ max p.1 0 := le_max_right _ _
          have hbefore : Shao.maxWithZero (Shao.Probability.Spitzer.head (J p) m (by omega)) <
              Shao.prefixSum (J p) (m + 1) := by
            by_contra hh
            have hle := le_of_not_gt hh
            change 0 < max (Shao.prefixSum (J p) (m + 1) -
              Shao.maxWithZero (Shao.Probability.Spitzer.head (J p) m (by omega))) 0 at hdpos
            rw [max_eq_right (sub_nonpos.mpr hle)] at hdpos
            exact (lt_irrefl 0) hdpos
          have hAlive : p.2 ∈ Alive p.1 := by
            intro k
            have hh := (Shao.maxWithZero_le_iff
              (Shao.Probability.Spitzer.head (J p) m (by omega)) _).mp le_rfl
                (m - k.val) (Nat.sub_le m k.val)
            rw [hlastSum m (J p), hlast, hJhead] at hbefore
            simp only [hJhead] at hh
            rw [hReverseSum _ _ (Nat.sub_le m k.val)] at hh
            rw [hReverseSum _ _ le_rfl, Nat.sub_self, Shao.prefixSum_zero, sub_zero] at hbefore
            have hk : k.val ≤ m := Nat.le_of_lt_succ k.isLt
            have hmk : m - (m - k.val) = k.val := by omega
            rw [hmk] at hh
            change -max p.1 0 ≤ Shao.prefixSum p.2 k.val
            linarith only [hh, hbefore, le_max_left p.1 0]
          have hL : w (m + 1) (J p) ≤ max p.1 0 + w m p.2 := by
            have hh := hConcatenate m 1 (fun i : Fin m => p.2 (Fin.rev i))
              (fun _ : Fin 1 => p.1)
            have hJoin : (fun i : Fin (m + 1) =>
                if hi : i.val < m then p.2 (Fin.rev ⟨i.val, hi⟩) else p.1) = J p := by
              funext i
              refine Fin.lastCases ?_ (fun u => ?_) i
              · simp [J]
              · simp [J, u.isLt]
            change w (m + 1) (fun i : Fin (m + 1) =>
                if hi : i.val < m then p.2 (Fin.rev ⟨i.val, hi⟩) else p.1) ≤
              w m (fun i : Fin m => p.2 (Fin.rev i)) + w 1 (fun _ : Fin 1 => p.1) at hh
            rw [hJoin] at hh
            change w (m + 1) (J p) ≤
              w m (fun i : Fin m => p.2 (Fin.rev i)) + w 1 (fun _ : Fin 1 => p.1) at hh
            have hr : w m (fun i : Fin m => p.2 (Fin.rev i)) = w m p.2 := hReverseWitness m p.2
            have hbpos : 0 < p.1 := by
              by_contra hn
              rw [max_eq_right (le_of_not_gt hn)] at hDlast
              linarith only [hDlast, hdpos]
            have h1 := (hgeometry 1 (fun _ : Fin 1 => p.1)).2.1
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul, Nat.cast_one, one_mul, abs_of_pos hbpos] at h1
            rw [hr] at hh
            linarith only [hh, h1, le_max_left p.1 0]
          dsimp only [G]
          rw [if_pos hAlive]
          exact mul_le_mul (pow_le_pow_left₀ (hd0 _ _) hDlast 2)
            (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hL ht))
            (Real.exp_pos _).le (sq_nonneg _)
        · have hz : d (m + 1) (J p) = 0 := le_antisymm (le_of_not_gt hdpos) (hd0 _ _)
          simp only [hz, zero_pow (by norm_num : 2 ≠ 0), zero_mul]
          exact hG0 p
      let K : ℝ := CW / Real.sqrt (m : ℝ) * (1 + (m : ℝ) * theta ^ 2) *
        Real.exp ((253 / 500 : ℝ) * (m : ℝ) * theta ^ 2 +
          CW * (m : ℝ) * theta ^ 3 * beta + (2 * CW + 1) * theta * Bcap)
      have hK0 : 0 ≤ K := by dsimp only [K]; positivity
      have hInner : ∀ᵐ b : ℝ ∂rho,
          (∫ v : Shao.Path m, G (b, v) ∂R) ≤ K * ((max b 0) ^ 2 * (max b 0 + beta)) := by
        filter_upwards [hs] with b hb
        have hb0 : 0 ≤ max b 0 := le_max_right _ _
        have hbB : max b 0 ≤ Bcap := max_le ((le_abs_self _).trans hb) hB.le
        have hos := hOS rho Bcap hB hs hmean hvar m hm theta (max b 0) ht hsmall hb0
        change Integrable ((Alive b).indicator (fun v : Shao.Path m => Real.exp (theta * w m v))) R ∧
          (∫ v : Shao.Path m, (Alive b).indicator (fun v => Real.exp (theta * w m v)) v ∂R) ≤
            CW * (max b 0 + beta) / Real.sqrt (m : ℝ) *
              (1 + (m : ℝ) * theta ^ 2) *
              Real.exp ((253 / 500 : ℝ) * (m : ℝ) * theta ^ 2 +
                CW * (m : ℝ) * theta ^ 3 * beta + CW * theta * (Bcap + max b 0)) at hos
        have heq (v : Shao.Path m) : G (b, v) =
            ((max b 0) ^ 2 * Real.exp (theta * max b 0)) *
              (Alive b).indicator (fun v => Real.exp (theta * w m v)) v := by
          dsimp only [G]
          by_cases hv : v ∈ Alive b
          · rw [if_pos hv, Set.indicator_of_mem hv]
            rw [mul_add, Real.exp_add]
            ring
          · rw [if_neg hv, Set.indicator_of_notMem hv, mul_zero]
        simp_rw [heq]
        rw [integral_const_mul]
        calc
          _ ≤ ((max b 0) ^ 2 * Real.exp (theta * max b 0)) *
              (CW * (max b 0 + beta) / Real.sqrt (m : ℝ) *
                (1 + (m : ℝ) * theta ^ 2) *
                Real.exp ((253 / 500 : ℝ) * (m : ℝ) * theta ^ 2 +
                  CW * (m : ℝ) * theta ^ 3 * beta + CW * theta * (Bcap + max b 0))) :=
            mul_le_mul_of_nonneg_left hos.2 (by positivity)
          _ ≤ K * ((max b 0) ^ 2 * (max b 0 + beta)) := by
            have he : theta * max b 0 + CW * theta * (Bcap + max b 0) ≤
                (2 * CW + 1) * theta * Bcap := by
              have hh := mul_le_mul_of_nonneg_left hbB (mul_nonneg hCW0 ht)
              have hh' := mul_le_mul_of_nonneg_left hbB ht
              nlinarith only [hh, hh']
            have hex := Real.exp_le_exp.2
              (add_le_add_left he ((253 / 500 : ℝ) * (m : ℝ) * theta ^ 2 +
                CW * (m : ℝ) * theta ^ 3 * beta))
            have hh := mul_le_mul_of_nonneg_left hex
              (show 0 ≤ CW / Real.sqrt (m : ℝ) *
                (1 + (m : ℝ) * theta ^ 2) * (max b 0) ^ 2 * (max b 0 + beta) by positivity)
            convert hh using 1 <;> (try dsimp only [K]) <;> simp only [Real.exp_add] <;> ring
      have hBpI : Integrable (fun b : ℝ => (max b 0) ^ 2 * (max b 0 + beta)) rho := by
        apply (integrable_const (Bcap ^ 2 * (Bcap + beta))).mono' (by fun_prop)
        filter_upwards [hs] with b hb
        have hbB : max b 0 ≤ Bcap := max_le ((le_abs_self _).trans hb) hB.le
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        gcongr
      have hBp : (∫ b : ℝ, (max b 0) ^ 2 * (max b 0 + beta) ∂rho) ≤ 2 * beta := by
        calc
          _ ≤ ∫ b : ℝ, |b| ^ 3 + beta * b ^ 2 ∂rho := by
            apply integral_mono hBpI ((hPower 3).add (h2.const_mul beta))
            intro b
            change (max b 0) ^ 2 * (max b 0 + beta) ≤ |b| ^ 3 + beta * b ^ 2
            by_cases hb : 0 ≤ b
            · rw [max_eq_left hb, abs_of_nonneg hb]
              exact le_of_eq (by ring)
            · rw [max_eq_right (le_of_not_ge hb)]
              calc
                (0 : ℝ) ^ 2 * (0 + beta) = 0 := by ring
                _ ≤ |b| ^ 3 + beta * b ^ 2 :=
                  add_nonneg (pow_nonneg (abs_nonneg b) 3) (mul_nonneg hbeta0 (sq_nonneg b))
          _ = _ := by
            rw [integral_add (hPower 3) (h2.const_mul beta), integral_const_mul, hvar]
            change beta + beta * 1 = 2 * beta
            ring
      have hTotal : (∫ v : Shao.Path (m + 1), D v ^ 2 * Real.exp (theta * L v) ∂P) ≤
          2 * beta * K := by
        have hJI := hJMP.integrable_comp_of_integrable hI2
        have hMap :
            (∫ v : Shao.Path (m + 1), D v ^ 2 * Real.exp (theta * L v) ∂(rho.prod R).map J) =
              ∫ p : ℝ × Shao.Path m, D (J p) ^ 2 * Real.exp (theta * L (J p)) ∂rho.prod R :=
          integral_map (f := fun v : Shao.Path (m + 1) => D v ^ 2 * Real.exp (theta * L v))
            hJMP.aemeasurable
            ((hDmeas.pow_const 2).mul
              ((measurable_const : Measurable (fun _ : Shao.Path (m + 1) => theta)).mul
                hLmeas).exp).aestronglyMeasurable
        rw [hJMP.map_eq] at hMap
        calc
          _ = ∫ p : ℝ × Shao.Path m,
              d (m + 1) (J p) ^ 2 * Real.exp (theta * w (m + 1) (J p)) ∂rho.prod R := hMap
          _ ≤ ∫ p : ℝ × Shao.Path m, G p ∂rho.prod R := integral_mono hJI hGI hpoint
          _ = ∫ b : ℝ, ∫ v : Shao.Path m, G (b, v) ∂R ∂rho := integral_prod _ hGI
          _ ≤ ∫ b : ℝ, K * ((max b 0) ^ 2 * (max b 0 + beta)) ∂rho :=
            integral_mono_ae hGI.integral_prod_left (hBpI.const_mul K) hInner
          _ = K * (∫ b : ℝ, (max b 0) ^ 2 * (max b 0 + beta) ∂rho) := integral_const_mul _ _
          _ ≤ 2 * beta * K := by nlinarith only [mul_le_mul_of_nonneg_left hBp hK0]
      apply hTotal.trans
      have hRoots : Real.sqrt ((m + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (m : ℝ) := by
        have hsq1 : Real.sqrt ((m + 1 : ℕ) : ℝ) ^ 2 = (m : ℝ) + 1 := by
          rw [Real.sq_sqrt (by positivity), Nat.cast_add, Nat.cast_one]
        have hsq2 := Real.sq_sqrt hmr.le
        have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        nlinarith only [hsq1, hsq2, hm1, Real.sqrt_nonneg ((m + 1 : ℕ) : ℝ), Real.sqrt_nonneg (m : ℝ)]
      have hinv : 1 / Real.sqrt (m : ℝ) ≤ 2 / Real.sqrt ((m + 1 : ℕ) : ℝ) := by
        apply (div_le_div_iff₀ hmrRoot hroot).2
        simpa only [one_mul] using hRoots
      have hexp : (253 / 500 : ℝ) * (m : ℝ) * theta ^ 2 +
          CW * (m : ℝ) * theta ^ 3 * beta + (2 * CW + 1) * theta * Bcap ≤
          (253 / 500 : ℝ) * ((m + 1 : ℕ) : ℝ) * theta ^ 2 +
            C * ((m + 1 : ℕ) : ℝ) * theta ^ 3 * beta + C * theta * Bcap := by
        have hc1 : CW ≤ C := by dsimp only [C]; linarith only [hCW0, hCM0]
        have hc2 : 2 * CW + 1 ≤ C := by dsimp only [C]; linarith only [hCW0, hCM0]
        have h1 := mul_le_mul_of_nonneg_right hc1
          (show 0 ≤ (m : ℝ) * theta ^ 3 * beta by positivity)
        have h2' := mul_le_mul_of_nonneg_right hc2 (mul_nonneg ht hB.le)
        have h3' : 0 ≤ C * theta ^ 3 * beta := by positivity
        push_cast
        nlinarith only [h1, h2', h3', sq_nonneg theta]
      have hpoly : 1 + (m : ℝ) * theta ^ 2 ≤ 1 + ((m + 1 : ℕ) : ℝ) * theta ^ 2 := by
        push_cast
        nlinarith only [sq_nonneg theta]
      dsimp only [K, A]
      calc
        _ ≤ 2 * beta * (CW * (2 / Real.sqrt ((m + 1 : ℕ) : ℝ)) *
            (1 + ((m + 1 : ℕ) : ℝ) * theta ^ 2) *
            Real.exp ((253 / 500 : ℝ) * ((m + 1 : ℕ) : ℝ) * theta ^ 2 +
              C * ((m + 1 : ℕ) : ℝ) * theta ^ 3 * beta + C * theta * Bcap)) := by
          have hdiv : CW / Real.sqrt (m : ℝ) ≤
              CW * (2 / Real.sqrt ((m + 1 : ℕ) : ℝ)) := by
            convert mul_le_mul_of_nonneg_left hinv hCW0 using 1 <;> ring
          have hprod := mul_le_mul (mul_le_mul hdiv hpoly (by positivity) (by positivity))
            (Real.exp_le_exp.2 hexp) (Real.exp_pos _).le (by positivity)
          exact mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = (4 * CW) * A := by dsimp only [A]; ring
        _ ≤ (8 * CW) * A :=
          mul_le_mul_of_nonneg_right (by linarith only [hCW0]) hA0
  calc
    _ = (∫ v : Shao.Path N, D v ^ 2 * Real.exp (theta * L v) ∂P) +
        beta * (∫ v : Shao.Path N, D v * Real.exp (theta * L v) ∂P) := by
      rw [← integral_const_mul, ← integral_add hI2 (hI1.const_mul beta)]
      apply integral_congr_ae
      exact ae_of_all _ fun v => by simp only [Pi.add_apply]; ring
    _ ≤ (8 * CW) * A + (4000 * CM) * A := add_le_add hSecond hFirst
    _ ≤ C * A := by
      have hh : 8 * CW + 4000 * CM ≤ C := by dsimp only [C]; linarith only [hCM0]
      nlinarith only [mul_le_mul_of_nonneg_right hh hA0]
    _ = _ := by dsimp only [A]; ring

theorem actual_circular_weighted_true_energy_record_strip :
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
              let L : Shao.Path j → ℝ := fun a => circularWitness a
              ∀ q : ℝ, 0 ≤ q →
                let F : Shao.Path j → ℝ := fun a => Shao.prefixSum a j -
                  x * Real.sqrt (max (Shao.energy a + q) ((n : ℝ) / 2))
                let E : Set (Shao.Path j) := {a | 0 ≤ F a ∧ F a ≤ D a}
                ∀ theta : ℝ, 0 ≤ theta → theta * Bcap ≤ 1 / 100 →
                  1 ≤ theta * Real.sqrt ((j : ℝ) / 4) →
                  Measurable F ∧ MeasurableSet E ∧
                    Integrable (E.indicator
                      (fun a => D a * Real.exp (theta * L a))) P ∧
                    (∫ a : Shao.Path j, E.indicator
                      (fun a => D a * Real.exp (theta * L a)) a ∂P) ≤
                      C * beta / (j : ℝ) *
                        (1 + theta * Real.sqrt (j : ℝ)) ^ 5 *
                        Real.exp ((253 / 500 : ℝ) * (j : ℝ) * theta ^ 2 +
                          C * (j : ℝ) * theta ^ 3 * beta + C * theta * Bcap) := by
  classical
  run_tac
    let mod : Lean.Name := "Shao.Probability.SourceWeightedPrefixWall".toName
    let n : Lean.Name := Lean.mkPrivateNameCore mod
      ("Shao.Probability.SourceWeightedPrefixWall.pww_weighted_coordinate_concentration".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hConcentration".toName)) := $(Lean.mkIdent n)))
    let n : Lean.Name := Lean.mkPrivateNameCore mod
      ("Shao.Probability.SourceWeightedPrefixWall.pww_actual_clipped_wall_statistic".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hClipped".toName)) := $(Lean.mkIdent n)))
    let n : Lean.Name := Lean.mkPrivateNameCore mod
      ("Shao.Probability.SourceWeightedPrefixWall.pww_circular_witness_concatenation".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hConcatenate".toName)) := $(Lean.mkIdent n)))
    let mod : Lean.Name := "Shao.Probability.SourceTrueEnergyStrip".toName
    let n : Lean.Name := Lean.mkPrivateNameCore mod ("Shao.Probability.tes_head_tail_measurePreserving".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hSplitMP".toName)) := $(Lean.mkIdent n)))
    let n : Lean.Name := Lean.mkPrivateNameCore mod ("Shao.Probability.tes_head_tail_sum".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hSplitSum".toName)) := @$(Lean.mkIdent n)))
    let n : Lean.Name := Lean.mkPrivateNameCore mod ("Shao.Probability.tes_reverse_prefixSum".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hReversePrefix".toName)) := @$(Lean.mkIdent n)))
    let n : Lean.Name := Lean.mkPrivateNameCore mod ("Shao.Probability.tes_reverse_tail_prefixSum".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hReverseTail".toName)) := @$(Lean.mkIdent n)))
  obtain ⟨CE, hCE, hCoord⟩ := hConcentration
  obtain ⟨CR, hCR, hRecord⟩ := actual_circular_weighted_record_moment
  let C : ℝ := 10 + 16 * CE * CR + 4 * CE + 4 * CR
  have hCE0 : 0 ≤ CE := zero_le_one.trans hCE
  have hCR0 : 0 ≤ CR := zero_le_one.trans hCR
  have hC : 1 ≤ C := by
    dsimp only [C]
    nlinarith only [hCE0, hCR0, mul_nonneg hCE0 hCR0]
  have hCEC : CE ≤ C := by
    dsimp only [C]
    nlinarith only [hCE0, hCR0, mul_nonneg hCE0 hCR0]
  have hCRC : CR ≤ C := by
    dsimp only [C]
    nlinarith only [hCE0, hCR0, mul_nonneg hCE0 hCR0]
  refine ⟨C, hC, ?_⟩
  intro rho hprob Bcap hB hs hmean hvar beta n hn x hx hcap j hj hjn P D L q hq F E theta ht hsmall hlarge
  let k : ℕ := j / 2
  let l : ℕ := j - k
  have hk : 0 < k := by dsimp only [k]; omega
  have hl : 0 < l := by dsimp only [l, k]; omega
  have hkj : k ≤ j := by dsimp only [k]; omega
  have hlj : l ≤ j := Nat.sub_le j k
  have hkl : k + l = j := Nat.add_sub_of_le hkj
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  have hlr : 0 < (l : ℝ) := by exact_mod_cast hl
  have hjr : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hklr : (k : ℝ) + (l : ℝ) = (j : ℝ) := by exact_mod_cast hkl
  have hkquarter : (j : ℝ) / 4 ≤ (k : ℝ) := by
    have hh : j ≤ 4 * k := by dsimp only [k]; omega
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    have hhr : (j : ℝ) ≤ 4 * (k : ℝ) := by exact_mod_cast hh
    nlinarith only [hhr]
  have hlquarter : (j : ℝ) / 4 ≤ (l : ℝ) := by
    have hh : j ≤ 4 * l := by dsimp only [l, k]; omega
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    have hhr : (j : ℝ) ≤ 4 * (l : ℝ) := by exact_mod_cast hh
    nlinarith only [hhr]
  have htp : 0 < theta := by
    by_contra hh
    have hz : theta = 0 := le_antisymm (le_of_not_gt hh) ht
    simp only [hz, zero_mul] at hlarge
    linarith only [hlarge]
  have hklarge : 1 ≤ theta * Real.sqrt (k : ℝ) :=
    hlarge.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hkquarter) ht)
  have hllarge : 1 ≤ theta * Real.sqrt (l : ℝ) :=
    hlarge.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlquarter) ht)
  let Pk : Measure (Shao.Path k) := Measure.pi (fun _ : Fin k => rho)
  let Pl : Measure (Shao.Path l) := Measure.pi (fun _ : Fin l => rho)
  let H : Shao.Path j → Shao.Path k := fun a => Shao.Probability.Spitzer.head a k hkj
  let T : Shao.Path j → Shao.Path l := fun a => Shao.Probability.Spitzer.tail a k hkj
  let dl : Shao.Path l → ℝ := fun v =>
    max (Shao.prefixSum v l - Shao.maxWithZero
      (Shao.Probability.Spitzer.head v (l - 1) (Nat.sub_le l 1))) 0
  let wk : Shao.Path k → ℝ := fun v => circularWitness v
  let wl : Shao.Path l → ℝ := fun v => circularWitness v
  let clip : ℝ → ℝ := fun z => max (-Bcap) (min z Bcap)
  let Phi : Shao.Path l → Shao.Path k → ℝ := fun v u =>
    Shao.prefixSum u k - x * Real.sqrt
      (max ((∑ i : Fin k, (clip (u i)) ^ 2) + Shao.energy v + q) ((n : ℝ) / 2))
  let I : Shao.Path l → Set (Shao.Path k) := fun v =>
    {u | -Shao.prefixSum v l ≤ Phi v u ∧
      Phi v u ≤ dl v - Shao.prefixSum v l}
  let G : Shao.Path k × Shao.Path l → ℝ := fun p =>
    dl p.2 * Real.exp (theta * wl p.2) *
      (I p.2).indicator (fun u => Real.exp (theta * wk u)) p.1
  have hM := hRecord rho Bcap hB hs hmean hvar l hl theta ht hsmall hllarge
  change Measurable dl ∧ Measurable wl ∧
    Integrable (fun v => (dl v ^ 2 + beta * dl v) * Real.exp (theta * wl v)) Pl ∧
    (∫ v : Shao.Path l, (dl v ^ 2 + beta * dl v) * Real.exp (theta * wl v) ∂Pl) ≤
      CR * beta / Real.sqrt (l : ℝ) * (1 + (l : ℝ) * theta ^ 2) *
        Real.exp ((253 / 500 : ℝ) * (l : ℝ) * theta ^ 2 +
          CR * (l : ℝ) * theta ^ 3 * beta + CR * theta * Bcap) at hM
  obtain ⟨CM, hCM, hMom⟩ :=
    Shao.Probability.SourceCircularWitnessMoment.actual_circular_witness_small_parameter_moment
  have hwkm : Measurable wk := (hMom rho Bcap hB hs hmean hvar k).1
  have hLm : Measurable L := (hMom rho Bcap hB hs hmean hvar j).1
  have hDm : Measurable D := by
    have hh : Measurable (fun a : Shao.Path j =>
        Shao.Probability.Spitzer.head a (j - 1) (Nat.sub_le j 1)) :=
      measurable_pi_iff.2 fun i => measurable_pi_apply _
    exact ((Shao.measurable_prefixSum j).sub
      (Shao.measurable_maxWithZero.comp hh)).max measurable_const
  have hFm : Measurable F := by
    exact (Shao.measurable_prefixSum j).sub
      (measurable_const.mul (((Shao.measurable_energy.add_const q).max measurable_const).sqrt))
  have hEm : MeasurableSet E :=
    (measurableSet_le measurable_const hFm).inter (measurableSet_le hFm hDm)
  have hPhiM : Measurable (fun p : Shao.Path k × Shao.Path l => Phi p.2 p.1) := by
    dsimp only [Phi, clip, Shao.prefixSum, Shao.energy]
    fun_prop
  have hIM : MeasurableSet {p : Shao.Path k × Shao.Path l | p.1 ∈ I p.2} := by
    exact (measurableSet_le ((Shao.measurable_prefixSum l).comp measurable_snd).neg hPhiM).inter
      (measurableSet_le hPhiM ((hM.1.comp measurable_snd).sub
        ((Shao.measurable_prefixSum l).comp measurable_snd)))
  have hGm : Measurable G := by
    have hh : Measurable (fun p : Shao.Path k × Shao.Path l =>
        (I p.2).indicator (fun u => Real.exp (theta * wk u)) p.1) := by
      exact Measurable.ite hIM
        (measurable_const.mul (hwkm.comp measurable_fst)).exp measurable_const
    exact ((hM.1.comp measurable_snd).mul
      (measurable_const.mul (hM.2.1.comp measurable_snd)).exp).mul hh
  have hdl0 (v : Shao.Path l) : 0 ≤ dl v := le_max_right _ _
  have hD0 (a : Shao.Path j) : 0 ≤ D a := le_max_right _ _
  have hG0 (p : Shao.Path k × Shao.Path l) : 0 ≤ G p := by
    exact mul_nonneg (mul_nonneg (hdl0 p.2) (Real.exp_pos _).le)
      (Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _)
  run_tac
    let n : Lean.Name := Lean.mkPrivateNameCore ("Shao.Probability.SourceCircularWitnessMoment".toName)
      ("Shao.Probability.SourceCircularWitnessMoment.cwm_path_extrema_geometry".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have $(Lean.mkIdent ("hGeometry".toName)) := $(Lean.mkIdent n)))
  have hLsum (m : ℕ) (a : Shao.Path m) :
      circularWitness a ≤ ∑ i : Fin m, |a i| := ((hGeometry m).2.2.2 a).2.1
  have hdsum (m : ℕ) (a : Shao.Path m) :
      max (Shao.prefixSum a m - Shao.maxWithZero
        (Shao.Probability.Spitzer.head a (m - 1) (Nat.sub_le m 1))) 0 ≤
          ∑ i : Fin m, |a i| := by
    apply max_le
    · have hh : Shao.prefixSum a m ≤ ∑ i : Fin m, |a i| := by
        rw [Shao.prefixSum_length]
        exact Finset.sum_le_sum fun i _ => le_abs_self _
      linarith only [hh, Shao.maxWithZero_nonneg
        (Shao.Probability.Spitzer.head a (m - 1) (Nat.sub_le m 1))]
    · exact Finset.sum_nonneg fun i _ => abs_nonneg _
  have hSupport (m : ℕ) : ∀ᵐ a : Shao.Path m ∂Measure.pi (fun _ : Fin m => rho),
      ∀ i : Fin m, |a i| ≤ Bcap := by
    apply ae_all_iff.2
    intro i
    exact (measurePreserving_eval (fun _ : Fin m => rho) i).quasiMeasurePreserving.ae hs
  have hSumCap (m : ℕ) (a : Shao.Path m) (ha : ∀ i : Fin m, |a i| ≤ Bcap) :
      (∑ i : Fin m, |a i|) ≤ (m : ℝ) * Bcap := by
    calc
      _ ≤ ∑ _ : Fin m, Bcap := Finset.sum_le_sum fun i _ => ha i
      _ = _ := by simp
  have hfI : Integrable (E.indicator (fun a => D a * Real.exp (theta * L a))) P := by
    apply (integrable_const ((j : ℝ) * Bcap * Real.exp (theta * ((j : ℝ) * Bcap)))).mono'
      ((hDm.mul (measurable_const.mul hLm).exp).indicator hEm).aestronglyMeasurable
    filter_upwards [hSupport j] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      exact Set.indicator_nonneg (fun a _ => mul_nonneg (hD0 a) (Real.exp_pos _).le) a)]
    by_cases hE : a ∈ E
    · rw [Set.indicator_of_mem hE]
      exact mul_le_mul ((hdsum j a).trans (hSumCap j a ha))
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
          ((hLsum j a).trans (hSumCap j a ha)) ht))
        (Real.exp_pos _).le (by positivity)
    · rw [Set.indicator_of_notMem hE]
      positivity
  have hGI : Integrable G (Pk.prod Pl) := by
    have hSP : ∀ᵐ p : Shao.Path k × Shao.Path l ∂Pk.prod Pl,
        (∀ i : Fin k, |p.1 i| ≤ Bcap) ∧ ∀ i : Fin l, |p.2 i| ≤ Bcap := by
      filter_upwards [(measurePreserving_fst (μ := Pk) (ν := Pl)).quasiMeasurePreserving.ae (hSupport k),
        (measurePreserving_snd (μ := Pk) (ν := Pl)).quasiMeasurePreserving.ae (hSupport l)] with p hp hq'
      exact ⟨hp, hq'⟩
    apply (integrable_const ((l : ℝ) * Bcap *
      Real.exp (theta * ((k : ℝ) * Bcap + (l : ℝ) * Bcap)))).mono' hGm.aestronglyMeasurable
    filter_upwards [hSP] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (hG0 p)]
    by_cases hi : p.1 ∈ I p.2
    · dsimp only [G]
      rw [Set.indicator_of_mem hi, mul_assoc, ← Real.exp_add]
      have hDcap : dl p.2 ≤ (l : ℝ) * Bcap :=
        (hdsum l p.2).trans (hSumCap l p.2 hp.2)
      have hLkcap : wk p.1 ≤ (k : ℝ) * Bcap := (hLsum k p.1).trans (hSumCap k p.1 hp.1)
      have hLlcap : wl p.2 ≤ (l : ℝ) * Bcap := (hLsum l p.2).trans (hSumCap l p.2 hp.2)
      gcongr
      nlinarith only [mul_le_mul_of_nonneg_left hLkcap ht,
        mul_le_mul_of_nonneg_left hLlcap ht]
    · dsimp only [G]
      rw [Set.indicator_of_notMem hi, mul_zero]
      positivity
  refine ⟨hFm, hEm, hfI, ?_⟩
  have hHmeas : Measurable H := measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hTmeas : Measurable T := measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hPairMP : MeasurePreserving (fun a : Shao.Path j => (H a, T a)) P (Pk.prod Pl) :=
    hSplitMP rho j k hkj
  have hTotal (a : Shao.Path j) :
      Shao.prefixSum a j = Shao.prefixSum (H a) k + Shao.prefixSum (T a) l := by
    simpa only [Shao.prefixSum_length] using hSplitSum a k hkj (fun z => z)
  have hEnergy (a : Shao.Path j) :
      Shao.energy a = Shao.energy (H a) + Shao.energy (T a) :=
    hSplitSum a k hkj (fun z => z ^ 2)
  have hPrefix (a : Shao.Path j) (r : ℕ) (hr : r ≤ l) :
      Shao.prefixSum a (k + r) = Shao.prefixSum (H a) k + Shao.prefixSum (T a) r := by
    have h1 := hReverseTail a k hkj (l - r) (Nat.sub_le l r)
    have h2 := hReversePrefix (T a) (l - r) (Nat.sub_le l r)
    change Shao.prefixSum (fun i : Fin l => T a (Fin.rev i)) (l - r) =
      Shao.prefixSum a j - Shao.prefixSum a (j - (l - r)) at h1
    have hindex1 : j - (l - r) = k + r := by dsimp only [l] at hr ⊢; omega
    have hindex2 : l - (l - r) = r := by omega
    rw [hindex1, hTotal a] at h1
    rw [hindex2] at h2
    linarith only [h1, h2]
  have hDtail (a : Shao.Path j) : D a ≤ dl (T a) := by
    let Mj : ℝ := Shao.maxWithZero
      (Shao.Probability.Spitzer.head a (j - 1) (Nat.sub_le j 1))
    let Ml : ℝ := Shao.maxWithZero
      (Shao.Probability.Spitzer.head (T a) (l - 1) (Nat.sub_le l 1))
    have hM : Ml ≤ Mj - Shao.prefixSum (H a) k := by
      apply (Shao.maxWithZero_le_iff _ _).mpr
      intro r hr
      rw [Shao.Probability.Spitzer.head_prefixSum _ _ _ _ hr]
      have hkrj : k + r ≤ j - 1 := by dsimp only [l] at hr hl ⊢; omega
      have hh := (Shao.maxWithZero_le_iff
        (Shao.Probability.Spitzer.head a (j - 1) (Nat.sub_le j 1)) Mj).mp le_rfl
          (k + r) hkrj
      rw [Shao.Probability.Spitzer.head_prefixSum _ _ _ _ hkrj, hPrefix a r (by omega)] at hh
      linarith only [hh]
    change max (Shao.prefixSum a j - Mj) 0 ≤ max (Shao.prefixSum (T a) l - Ml) 0
    apply max_le_max _ le_rfl
    rw [hTotal]
    linarith only [hM]
  have hCastWitness {r s : ℕ} (hrs : r = s) (a : Shao.Path s) :
      circularWitness (fun i : Fin r => a ⟨i.val, by omega⟩) = circularWitness a := by
    subst s
    rfl
  have hLsplit (a : Shao.Path j) : L a ≤ wk (H a) + wl (T a) := by
    have hh := hConcatenate k l (H a) (T a)
    have hJoin : (fun i : Fin (k + l) =>
        if hi : i.val < k then H a ⟨i.val, hi⟩ else T a ⟨i.val - k, by omega⟩) =
        (fun i : Fin (k + l) => a ⟨i.val, by omega⟩) := by
      funext i
      by_cases hi : i.val < k
      · rw [dif_pos hi]
        rfl
      · rw [dif_neg hi]
        change a ⟨k + (i.val - k), by omega⟩ = a ⟨i.val, by omega⟩
        apply congrArg a
        apply Fin.ext
        change k + (i.val - k) = i.val
        omega
    change circularWitness (fun i : Fin (k + l) =>
      if hi : i.val < k then H a ⟨i.val, hi⟩ else T a ⟨i.val - k, by omega⟩) ≤
        wk (H a) + wl (T a) at hh
    rwa [hJoin, hCastWitness hkl a] at hh
  have hPhiActual (a : Shao.Path j) (ha : ∀ i : Fin j, |a i| ≤ Bcap) :
      F a = Phi (T a) (H a) + Shao.prefixSum (T a) l := by
    have hc (i : Fin k) : clip (H a i) = H a i := by
      have hb := abs_le.mp (ha ⟨i.val, Nat.lt_of_lt_of_le i.isLt hkj⟩)
      change -Bcap ≤ H a i ∧ H a i ≤ Bcap at hb
      dsimp only [clip]
      rw [min_eq_left hb.2, max_eq_right hb.1]
    have hcs : (∑ i : Fin k, (clip (H a i)) ^ 2) = Shao.energy (H a) := by
      simp only [hc, Shao.energy]
    dsimp only [F, Phi]
    rw [hcs, hTotal, hEnergy]
    ring
  have hPoint : ∀ᵐ a : Shao.Path j ∂P,
      E.indicator (fun a => D a * Real.exp (theta * L a)) a ≤ G (H a, T a) := by
    filter_upwards [hSupport j] with a ha
    by_cases he : a ∈ E
    · have he' : H a ∈ I (T a) := by
        rcases he with ⟨he0, heD⟩
        have hf := hPhiActual a ha
        dsimp only [I]
        exact ⟨by linarith only [he0, hf], by linarith only [heD, hf, hDtail a]⟩
      rw [Set.indicator_of_mem he]
      dsimp only [G]
      rw [Set.indicator_of_mem he', mul_assoc, ← Real.exp_add]
      apply mul_le_mul (hDtail a)
        (Real.exp_le_exp.2 (by
          have hh := mul_le_mul_of_nonneg_left (hLsplit a) ht
          nlinarith only [hh]))
        (Real.exp_pos _).le (hdl0 _)
    · rw [Set.indicator_of_notMem he]
      exact hG0 _
  have hSlopeSmall : 4 * x * Bcap ≤ Real.sqrt (n : ℝ) := by
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    have hh := (le_div_iff₀ (show 0 < 200 * x by positivity)).mp hcap
    have hxb : 0 ≤ x * Bcap := by positivity
    nlinarith only [hh, hxb]
  let K : ℝ := CE * (theta + 1 / (theta * (k : ℝ))) *
    (1 + (k : ℝ) * theta ^ 2) *
    Real.exp ((503 / 1000 : ℝ) * (k : ℝ) * theta ^ 2 +
      CE * (k : ℝ) * theta ^ 3 * beta)
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  have hSection (v : Shao.Path l) : (∫ u : Shao.Path k, G (u, v) ∂Pk) ≤
      K * ((dl v ^ 2 + beta * dl v) * Real.exp (theta * wl v)) := by
    have hFdata := hClipped k (n : ℝ) Bcap x (Shao.energy v + q) 0 hnr hB.le
      (zero_le_one.trans hx) (add_nonneg (Shao.energy_nonneg v) hq) le_rfl hSlopeSmall
    have hPhiV : Measurable (Phi v) := by
      have hh := hFdata.1.measurable
      simpa only [Phi, clip, add_zero, add_assoc] using hh
    have hSlopes : ∀ (a : Shao.Path k) (i : Fin k) (z z' : ℝ), z ≤ z' →
        (1 / 2 : ℝ) * (z' - z) ≤ Phi v (Function.update a i z') - Phi v (Function.update a i z) ∧
        Phi v (Function.update a i z') - Phi v (Function.update a i z) ≤ (3 / 2 : ℝ) * (z' - z) := by
      simpa only [Phi, clip, add_zero, add_assoc] using hFdata.2.1
    have hh := hCoord rho Bcap hB hs hmean hvar k hk theta htp hsmall
      (Phi v) hPhiV hSlopes (-Shao.prefixSum v l) (dl v) (hdl0 v)
    have hIeq : {u : Shao.Path k | -Shao.prefixSum v l ≤ Phi v u ∧
        Phi v u ≤ -Shao.prefixSum v l + dl v} = I v := by
      ext u
      simp only [I, Set.mem_setOf_eq]
      constructor <;> intro hu <;> exact ⟨hu.1, by linarith only [hu.2]⟩
    rw [hIeq] at hh
    change Integrable ((I v).indicator (fun u => Real.exp (theta * wk u))) Pk ∧
      (∫ u : Shao.Path k, (I v).indicator (fun u => Real.exp (theta * wk u)) u ∂Pk) ≤
        CE * (dl v + beta) * (theta + 1 / (theta * (k : ℝ))) *
          (1 + (k : ℝ) * theta ^ 2) *
          Real.exp ((503 / 1000 : ℝ) * (k : ℝ) * theta ^ 2 +
            CE * (k : ℝ) * theta ^ 3 * beta) at hh
    dsimp only [G]
    rw [integral_const_mul]
    have hbound :
        (dl v * Real.exp (theta * wl v)) *
            (∫ u : Shao.Path k, (I v).indicator (fun u => Real.exp (theta * wk u)) u ∂Pk) ≤
          (dl v * Real.exp (theta * wl v)) *
            (CE * (dl v + beta) * (theta + 1 / (theta * (k : ℝ))) *
              (1 + (k : ℝ) * theta ^ 2) *
              Real.exp ((503 / 1000 : ℝ) * (k : ℝ) * theta ^ 2 +
                CE * (k : ℝ) * theta ^ 3 * beta)) :=
      mul_le_mul_of_nonneg_left hh.2
        (mul_nonneg (hdl0 v) (Real.exp_pos (theta * wl v)).le)
    convert hbound using 1 <;> dsimp only [K] <;> ring
  have hTotalBound : (∫ a : Shao.Path j,
      E.indicator (fun a => D a * Real.exp (theta * L a)) a ∂P) ≤
      K * (CR * beta / Real.sqrt (l : ℝ) * (1 + (l : ℝ) * theta ^ 2) *
        Real.exp ((253 / 500 : ℝ) * (l : ℝ) * theta ^ 2 +
          CR * (l : ℝ) * theta ^ 3 * beta + CR * theta * Bcap)) := by
    have hGPairI := hPairMP.integrable_comp_of_integrable hGI
    calc
      _ ≤ ∫ a : Shao.Path j, G (H a, T a) ∂P := integral_mono_ae hfI hGPairI hPoint
      _ = ∫ p : Shao.Path k × Shao.Path l, G p ∂Pk.prod Pl := by
        have hh := integral_map hPairMP.aemeasurable hGm.aestronglyMeasurable
        rw [hPairMP.map_eq] at hh
        exact hh.symm
      _ = ∫ v : Shao.Path l, ∫ u : Shao.Path k, G (u, v) ∂Pk ∂Pl := integral_prod_symm _ hGI
      _ ≤ ∫ v : Shao.Path l,
          K * ((dl v ^ 2 + beta * dl v) * Real.exp (theta * wl v)) ∂Pl :=
        integral_mono hGI.integral_prod_right (hM.2.2.1.const_mul K) hSection
      _ = K * (∫ v : Shao.Path l, (dl v ^ 2 + beta * dl v) * Real.exp (theta * wl v) ∂Pl) :=
        integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hM.2.2.2 hK0
  apply hTotalBound.trans
  have hbeta0 : 0 ≤ beta := integral_nonneg fun z => pow_nonneg (abs_nonneg z) 3
  let t : ℝ := theta * Real.sqrt (j : ℝ)
  have ht0 : 0 ≤ t := by dsimp only [t]; positivity
  have hjroot : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.2 hjr
  have hlroot : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.2 hlr
  have htsq : t ^ 2 = (j : ℝ) * theta ^ 2 := by
    dsimp only [t]
    rw [mul_pow, Real.sq_sqrt hjr.le]
    ring
  have hThetaK : 1 ≤ theta ^ 2 * (k : ℝ) := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hklarge 2
    rw [mul_pow, Real.sq_sqrt hkr.le] at hh
    norm_num only [one_pow] at hh
    exact hh
  have hRate : theta + 1 / (theta * (k : ℝ)) ≤ 2 * theta := by
    have hh : 1 / (theta * (k : ℝ)) ≤ theta :=
      (div_le_iff₀ (mul_pos htp hkr)).2 (by nlinarith only [hThetaK])
    linarith only [hh]
  have hRootL : Real.sqrt (j : ℝ) ≤ 2 * Real.sqrt (l : ℝ) := by
    have hh1 := Real.sq_sqrt hjr.le
    have hh2 := Real.sq_sqrt hlr.le
    nlinarith only [hh1, hh2, hlquarter, Real.sqrt_nonneg (j : ℝ), Real.sqrt_nonneg (l : ℝ)]
  have hInvL : 1 / Real.sqrt (l : ℝ) ≤ 2 / Real.sqrt (j : ℝ) :=
    (div_le_div_iff₀ hlroot hjroot).2 (by simpa only [one_mul] using hRootL)
  have hInvJ : 1 / Real.sqrt (j : ℝ) = Real.sqrt (j : ℝ) / (j : ℝ) := by
    apply (div_eq_div_iff hjroot.ne' hjr.ne').2
    rw [one_mul, Real.mul_self_sqrt hjr.le]
  have hkPoly : 1 + (k : ℝ) * theta ^ 2 ≤ (1 + t) ^ 2 := by
    have hkR : (k : ℝ) ≤ (j : ℝ) := by exact_mod_cast hkj
    have hh := mul_le_mul_of_nonneg_right hkR (sq_nonneg theta)
    nlinarith only [hh, htsq, ht0]
  have hlPoly : 1 + (l : ℝ) * theta ^ 2 ≤ (1 + t) ^ 2 := by
    have hlR : (l : ℝ) ≤ (j : ℝ) := by exact_mod_cast hlj
    have hh := mul_le_mul_of_nonneg_right hlR (sq_nonneg theta)
    nlinarith only [hh, htsq, ht0]
  have hScale :
      1 / Real.sqrt (l : ℝ) * (theta + 1 / (theta * (k : ℝ))) *
          (1 + (k : ℝ) * theta ^ 2) * (1 + (l : ℝ) * theta ^ 2) ≤
        4 / (j : ℝ) * (1 + t) ^ 5 := by
    calc
      _ ≤ (2 / Real.sqrt (j : ℝ)) * (2 * theta) * (1 + t) ^ 2 * (1 + t) ^ 2 := by
        gcongr
      _ = 4 / (j : ℝ) * t * (1 + t) ^ 4 := by
        rw [show 2 / Real.sqrt (j : ℝ) = 2 * (1 / Real.sqrt (j : ℝ)) by ring, hInvJ]
        dsimp only [t]
        ring
      _ ≤ 4 / (j : ℝ) * (1 + t) ^ 5 := by
        have hh : t ≤ 1 + t := by linarith
        have hh' := mul_le_mul_of_nonneg_right hh (show 0 ≤ (4 / (j : ℝ)) * (1 + t) ^ 4 by positivity)
        convert hh' using 1 <;> ring
  have hExponent :
      (503 / 1000 : ℝ) * (k : ℝ) * theta ^ 2 + CE * (k : ℝ) * theta ^ 3 * beta +
        ((253 / 500 : ℝ) * (l : ℝ) * theta ^ 2 +
          CR * (l : ℝ) * theta ^ 3 * beta + CR * theta * Bcap) ≤
      (253 / 500 : ℝ) * (j : ℝ) * theta ^ 2 +
        C * (j : ℝ) * theta ^ 3 * beta + C * theta * Bcap := by
    have he := mul_le_mul_of_nonneg_right hCEC
      (show 0 ≤ (k : ℝ) * theta ^ 3 * beta by positivity)
    have hr := mul_le_mul_of_nonneg_right hCRC
      (show 0 ≤ (l : ℝ) * theta ^ 3 * beta by positivity)
    have hb := mul_le_mul_of_nonneg_right hCRC (mul_nonneg ht hB.le)
    have hkk : 0 ≤ (k : ℝ) * theta ^ 2 := mul_nonneg hkr.le (sq_nonneg theta)
    rw [← hklr]
    nlinarith only [he, hr, hb, hkk]
  have hCoef : 4 * CE * CR ≤ C := by
    dsimp only [C]
    nlinarith only [hCE0, hCR0, mul_nonneg hCE0 hCR0]
  calc
    _ = (CE * CR * beta) *
        (1 / Real.sqrt (l : ℝ) * (theta + 1 / (theta * (k : ℝ))) *
          (1 + (k : ℝ) * theta ^ 2) * (1 + (l : ℝ) * theta ^ 2)) *
        Real.exp ((503 / 1000 : ℝ) * (k : ℝ) * theta ^ 2 +
          CE * (k : ℝ) * theta ^ 3 * beta +
          ((253 / 500 : ℝ) * (l : ℝ) * theta ^ 2 +
            CR * (l : ℝ) * theta ^ 3 * beta + CR * theta * Bcap)) := by
      dsimp only [K]
      simp only [Real.exp_add]
      ring
    _ ≤ (CE * CR * beta) * (4 / (j : ℝ) * (1 + t) ^ 5) *
        Real.exp ((253 / 500 : ℝ) * (j : ℝ) * theta ^ 2 +
          C * (j : ℝ) * theta ^ 3 * beta + C * theta * Bcap) := by
      gcongr
    _ ≤ C * beta / (j : ℝ) * (1 + theta * Real.sqrt (j : ℝ)) ^ 5 *
        Real.exp ((253 / 500 : ℝ) * (j : ℝ) * theta ^ 2 +
          C * (j : ℝ) * theta ^ 3 * beta + C * theta * Bcap) := by
      have hh := mul_le_mul_of_nonneg_right hCoef
        (show 0 ≤ beta / (j : ℝ) * (1 + t) ^ 5 *
          Real.exp ((253 / 500 : ℝ) * (j : ℝ) * theta ^ 2 +
            C * (j : ℝ) * theta ^ 3 * beta + C * theta * Bcap) by positivity)
      convert hh using 1 <;> dsimp only [t] <;> ring

end Shao.Probability.SourceWeightedRecordStrip
