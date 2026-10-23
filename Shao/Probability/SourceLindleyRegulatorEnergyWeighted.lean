import Shao.Probability.BoundedQuadraticTilt
import Shao.Probability.SourceLindleyRegulatorFirstMomentSums
import Shao.Probability.SourceTruncationBridge
import Shao.OQ3.QuadraticSampleChangeOfMeasure
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem ew_state_nonneg {N : ℕ} (a : Shao.Path N) (k : ℕ) (hk : k ≤ N) :
    0 ≤ Shao.lindleyState a k hk := by
  cases k with
  | zero => rfl
  | succ k => exact le_max_left _ _

private theorem ew_reg_bounds {N : ℕ} (a : Shao.Path N) (i : Fin N) :
    0 ≤ lindleyRegulator a i ∧ lindleyRegulator a i ≤ |a i| := by
  refine ⟨le_max_right _ _, max_le ?_ (abs_nonneg _)⟩
  have hw := ew_state_nonneg a i.val (Nat.le_of_lt i.is_lt)
  have ha := neg_le_abs (a i)
  change -(Shao.lindleyState a i.val _ + a i) ≤ |a i|
  linarith

private theorem ew_state_meas {N : ℕ} (k : ℕ) (hk : k ≤ N) :
    Measurable (fun a : Shao.Path N => Shao.lindleyState a k hk) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact measurable_const.max ((ih (by omega)).add (measurable_pi_apply _))

private theorem ew_reg_meas {N : ℕ} (i : Fin N) :
    Measurable (fun a : Shao.Path N => lindleyRegulator a i) :=
  ((ew_state_meas i.val (Nat.le_of_lt i.is_lt)).add
    (measurable_pi_apply i)).neg.max measurable_const

private theorem ew_energy_meas (N : ℕ) : Measurable (Shao.energy : Shao.Path N → ℝ) := by
  unfold Shao.energy
  fun_prop

private theorem ew_prefix_energy_meas (N k : ℕ) :
    Measurable (fun a : Shao.Path N => Shao.prefixSquares a k) := by
  unfold Shao.prefixSquares
  fun_prop

private theorem ew_state_prefix {N : ℕ} (a : Shao.Path N)
    (m : ℕ) (hm : m ≤ N) (k : ℕ) (hk : k ≤ m) :
    Shao.lindleyState (Shao.prefixPath a m hm) k hk =
      Shao.lindleyState a k (hk.trans hm) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Shao.lindleyState_succ, Shao.lindleyState_succ, ih (by omega)]
    rfl

private theorem ew_prefix_energy {N : ℕ} (a : Shao.Path N) (m : ℕ) (hm : m ≤ N) :
    Shao.energy (Shao.prefixPath a m hm) = Shao.prefixSquares a m := by
  classical
  unfold Shao.energy Shao.prefixSquares
  refine Finset.sum_bij (fun j _ => (⟨j.val, lt_of_lt_of_le j.is_lt hm⟩ : Fin N))
    ?_ ?_ ?_ ?_
  · intro j _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact j.is_lt
  · intro j _ k _ he
    exact Fin.ext (congrArg (@Fin.val N) he)
  · intro j hj
    have hjm : j.val < m := (Finset.mem_filter.mp hj).2
    exact ⟨⟨j.val, hjm⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro j _
    rfl

private theorem ew_prefix_mp (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (N m : ℕ) (hm : m ≤ N) :
    MeasurePreserving (fun a : Shao.Path N => Shao.prefixPath a m hm)
      (Measure.pi (fun _ : Fin N => ν)) (Measure.pi (fun _ : Fin m => ν)) := by
  let f : Fin m → Fin N := fun j => ⟨j.val, lt_of_lt_of_le j.is_lt hm⟩
  let X : Fin N → Shao.Path N → ℝ := fun j a => a j
  have hf : Function.Injective f := fun j k he => Fin.ext (congrArg (@Fin.val N) he)
  have hX : ∀ j, Measurable (X j) := fun j => measurable_pi_apply j
  have hind : iIndepFun X (Measure.pi (fun _ : Fin N => ν)) :=
    iIndepFun_pi (fun _ : Fin N => measurable_id.aemeasurable)
  have hlaw (j : Fin N) : IdentDistrib (X j) (id : ℝ → ℝ)
      (Measure.pi (fun _ : Fin N => ν)) ν := by
    refine ⟨(hX j).aemeasurable, measurable_id.aemeasurable, ?_⟩
    exact (measurePreserving_eval (fun _ : Fin N => ν) j).map_eq.trans Measure.map_id.symm
  refine ⟨Measurable.of_eval (fun j => measurable_pi_apply (f j)), ?_⟩
  exact iid_samplePath_map_eq_pi (fun j => hX (f j))
    (hind.precomp hf) (fun j => hlaw (f j))

private theorem ew_prefix_integral (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (N m : ℕ) (hm : m ≤ N) (g : Shao.Path m → ℝ) (hg : Measurable g) :
    (∫ a : Shao.Path N, g (Shao.prefixPath a m hm)
      ∂Measure.pi (fun _ : Fin N => ν)) =
      ∫ b : Shao.Path m, g b ∂Measure.pi (fun _ : Fin m => ν) := by
  have hp := ew_prefix_mp ν N m hm
  have hd : IdentDistrib (fun a : Shao.Path N => Shao.prefixPath a m hm)
      (id : Shao.Path m → Shao.Path m)
      (Measure.pi (fun _ : Fin N => ν)) (Measure.pi (fun _ : Fin m => ν)) :=
    ⟨hp.measurable.aemeasurable, measurable_id.aemeasurable,
      hp.map_eq.trans Measure.map_id.symm⟩
  simpa only [Function.comp_def, id_eq] using (hd.comp hg).integral_eq

private theorem ew_reg_ae_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ℝ) (hsp : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) (N : ℕ) (i : Fin N) :
    ∀ᵐ a : Shao.Path N ∂Measure.pi (fun _ : Fin N => ν),
      lindleyRegulator a i ≤ h := by
  have he := (measurePreserving_eval (fun _ : Fin N => ν) i).quasiMeasurePreserving.ae hsp
  filter_upwards [he] with a ha
  exact (ew_reg_bounds a i).2.trans ha

private theorem ew_reg_power_int (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ℝ) (hh : 0 ≤ h) (hsp : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (N : ℕ) (i : Fin N) (r : ℕ) :
    Integrable (fun a : Shao.Path N => lindleyRegulator a i ^ r)
      (Measure.pi (fun _ : Fin N => ν)) := by
  apply (integrable_const (h ^ r)).mono' ((ew_reg_meas i).pow_const r).aestronglyMeasurable
  filter_upwards [ew_reg_ae_bound ν h hsp N i] with a ha
  rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg (ew_reg_bounds a i).1]
  exact pow_le_pow_left₀ (ew_reg_bounds a i).1 ha r

private theorem ew_energy_exp_int (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (s : ℝ) (hs : 0 ≤ s) : Integrable (fun a : ℝ => Real.exp (-s * a ^ 2)) ν := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  exact ae_of_all ν (fun a => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr hs) (sq_nonneg a)))

/-- Bundle 1: the actual prefix, positive weight, L1 and r=1,2 identities. -/
theorem iid_lindleyRegulator_prefix_energy_change_of_measure
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h s : ℝ) (hh : 0 < h) (hs : 0 ≤ s)
    (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (N : ℕ) (i : Fin N) :
    let Z : ℝ := ∫ a : ℝ, Real.exp (-s * a ^ 2) ∂ν
    let ρ : Measure ℝ := ν.tilted (fun a => -s * a ^ 2)
    let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ν)
    let T : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ρ)
    let p : Shao.Path N → Shao.Path (i.val + 1) := fun a =>
      Shao.prefixPath a (i.val + 1) (Nat.succ_le_of_lt i.is_lt)
    let U : Shao.Path N → ℝ := fun a => lindleyRegulator a i
    let Q : Shao.Path N → ℝ := fun a => Shao.prefixSquares a (i.val + 1)
    let W : Shao.Path N → ℝ := fun a => Real.exp (-s * Q a)
    Integrable (fun a : ℝ => Real.exp (-s * a ^ 2)) ν ∧
      0 < Z ∧ IsProbabilityMeasure ρ ∧
      IsProbabilityMeasure P ∧ IsProbabilityMeasure T ∧
      Measurable U ∧ Measurable Q ∧
      (∀ a : Shao.Path N,
        U a = lindleyRegulator (p a) (Fin.last i.val) ∧
        Q a = Shao.energy (p a) ∧
        0 ≤ U a ∧ 0 ≤ Q a ∧ 0 < W a ∧ W a ≤ 1) ∧
      (∀ᵐ a : Shao.Path N ∂P, U a ≤ h) ∧
      (∀ᵐ a : Shao.Path N ∂T, U a ≤ h) ∧
      Integrable W P ∧
      (∫ a : Shao.Path N, W a ∂P) = Z ^ (i.val + 1) ∧
      (∀ r : ℕ, (r = 1 ∨ r = 2) →
        Integrable (fun a : Shao.Path N => U a ^ r) P ∧
        Integrable (fun a : Shao.Path N => U a ^ r) T ∧
        Integrable (fun a : Shao.Path N => U a ^ r * W a) P ∧
        (∫ a : Shao.Path N, U a ^ r ∂T) =
          ∫ b : Shao.Path (i.val + 1),
            lindleyRegulator b (Fin.last i.val) ^ r
            ∂Measure.pi (fun _ : Fin (i.val + 1) => ρ) ∧
        (∫ a : Shao.Path N, U a ^ r * W a ∂P) =
          Z ^ (i.val + 1) * (∫ a : Shao.Path N, U a ^ r ∂T)) := by
  classical
  dsimp only
  let Z : ℝ := ∫ a : ℝ, Real.exp (-s * a ^ 2) ∂ν
  let ρ : Measure ℝ := ν.tilted (fun a => -s * a ^ 2)
  let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ν)
  let T : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ρ)
  let m := i.val + 1
  let p : Shao.Path N → Shao.Path m := fun a => Shao.prefixPath a m (by dsimp [m]; omega)
  let U : Shao.Path N → ℝ := fun a => lindleyRegulator a i
  let Q : Shao.Path N → ℝ := fun a => Shao.prefixSquares a m
  let W : Shao.Path N → ℝ := fun a => Real.exp (-s * Q a)
  let E : Shao.Path m → ℝ := fun b => -s * Shao.energy b
  let PP : Measure (Shao.Path m) := Measure.pi (fun _ : Fin m => ν)
  let TT : Measure (Shao.Path m) := Measure.pi (fun _ : Fin m => ρ)
  have hWν := ew_energy_exp_int ν s hs
  have hZ : 0 < Z := integral_exp_pos hWν
  letI : IsProbabilityMeasure ρ := isProbabilityMeasure_tilted hWν
  have hspρ : ∀ᵐ a : ℝ ∂ρ, |a| ≤ h :=
    (tilted_absolutelyContinuous ν (fun a => -s * a ^ 2)).ae_le hsupport
  have hU (a : Shao.Path N) : U a = lindleyRegulator (p a) (Fin.last i.val) := by
    dsimp only [U, lindleyRegulator, p]
    rw [ew_state_prefix]
    rfl
  have hQ (a : Shao.Path N) : Q a = Shao.energy (p a) :=
    (ew_prefix_energy a m (by dsimp [m]; omega)).symm
  have hw (a : Shao.Path N) : 0 < W a ∧ W a ≤ 1 := by
    refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr ?_⟩
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs)
      (Shao.prefixSquares_nonneg a m)
  have hWI : Integrable W P := by
    apply (integrable_const (1 : ℝ)).mono'
      (((ew_prefix_energy_meas N m).const_mul (-s)).exp).aestronglyMeasurable
    exact ae_of_all P (fun a => by
      rw [Real.norm_eq_abs, abs_of_pos (hw a).1]
      exact (hw a).2)
  have htheta : (0, -s) ∈ bivariateMGFDomain ν (fun a : ℝ => (a, a ^ 2)) := by
    simpa only [bivariateMGFDomain, Set.mem_setOf_eq, zero_mul, zero_add] using hWν
  obtain ⟨_, hn0, ht0⟩ := Shao.OQ3.iid_quadratic_sample_tilt ν (0, -s) htheta m
  have hn : (∫ b : Shao.Path m, Real.exp (E b) ∂PP) = Z ^ m := by
    simpa only [E, PP, Z, Shao.energy, zero_mul, zero_add, ← Finset.mul_sum] using hn0
  have ht : PP.tilted E = TT := by
    simpa only [E, PP, TT, ρ, Shao.energy, zero_mul, zero_add, ← Finset.mul_sum] using ht0
  have hwE (a : Shao.Path N) : W a = Real.exp (E (p a)) := by
    dsimp only [W, E]
    rw [hQ]
  have hnorm : (∫ a : Shao.Path N, W a ∂P) = Z ^ m := by
    calc
      _ = ∫ a : Shao.Path N, Real.exp (E (p a)) ∂P :=
        integral_congr_ae (ae_of_all P hwE)
      _ = ∫ b : Shao.Path m, Real.exp (E b) ∂PP :=
        ew_prefix_integral ν N m (by dsimp [m]; omega) _
          (((ew_energy_meas m).const_mul (-s)).exp)
      _ = _ := hn
  refine ⟨hWν, hZ, inferInstance, inferInstance, inferInstance,
    ew_reg_meas i, ew_prefix_energy_meas N m, ?_,
    ew_reg_ae_bound ν h hsupport N i, ew_reg_ae_bound ρ h hspρ N i,
    hWI, hnorm, ?_⟩
  · intro a
    exact ⟨hU a, hQ a, (ew_reg_bounds a i).1,
      Shao.prefixSquares_nonneg a m, (hw a).1, (hw a).2⟩
  · intro r _
    have hIr := ew_reg_power_int ν h hh.le hsupport N i r
    have hTr := ew_reg_power_int ρ h hh.le hspρ N i r
    have hIW : Integrable (fun a : Shao.Path N => U a ^ r * W a) P := by
      apply hIr.mono' (((ew_reg_meas i).pow_const r).mul
        (((ew_prefix_energy_meas N m).const_mul (-s)).exp)).aestronglyMeasurable
      exact ae_of_all P (fun a => by
        rw [Real.norm_eq_abs]
        change |U a ^ r * W a| ≤ U a ^ r
        rw [abs_of_nonneg (mul_nonneg (pow_nonneg (ew_reg_bounds a i).1 r) (hw a).1.le)]
        exact mul_le_of_le_one_right (pow_nonneg (ew_reg_bounds a i).1 r) (hw a).2)
    let g : Shao.Path m → ℝ := fun b => lindleyRegulator b (Fin.last i.val) ^ r
    have hg : Measurable g := (ew_reg_meas (Fin.last i.val)).pow_const r
    have hlong : (∫ a : Shao.Path N, U a ^ r ∂T) = ∫ b : Shao.Path m, g b ∂TT := by
      calc
        _ = ∫ a : Shao.Path N, g (p a) ∂T :=
          integral_congr_ae (ae_of_all T (fun a => by dsimp [g]; rw [hU]))
        _ = _ := ew_prefix_integral ρ N m (by dsimp [m]; omega) g hg
    have hbase : (∫ a : Shao.Path N, U a ^ r * W a ∂P) =
        ∫ b : Shao.Path m, g b * Real.exp (E b) ∂PP := by
      calc
        _ = ∫ a : Shao.Path N, g (p a) * Real.exp (E (p a)) ∂P :=
          integral_congr_ae (ae_of_all P (fun a => by dsimp [g]; rw [hU, hwE]))
        _ = _ := ew_prefix_integral ν N m (by dsimp [m]; omega) _
          (hg.mul (((ew_energy_meas m).const_mul (-s)).exp))
    have he := integral_tilted (μ := PP) E g
    rw [ht, hn] at he
    simp only [smul_eq_mul] at he
    have hf : (fun b : Shao.Path m => Real.exp (E b) / Z ^ m * g b) =
        fun b => (g b * Real.exp (E b)) / Z ^ m := by funext b; ring
    rw [hf, integral_div] at he
    have hmul := (eq_div_iff (pow_pos hZ m).ne').mp he
    refine ⟨hIr, hTr, hIW, hlong, ?_⟩
    rw [hbase, hlong]
    exact hmul.symm.trans (mul_comm _ _)

/-- Bundle 2: the same actual weighted first moment, with explicit constants. -/
theorem iid_lindleyRegulator_prefix_energy_first_moment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h s : ℝ) (hh : 0 < h) (hs : 0 ≤ s)
    (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (hsmall : s * h ^ 2 ≤ 1) (N : ℕ) (i : Fin N) :
    let ρ : Measure ℝ := ν.tilted (fun a => -s * a ^ 2)
    let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ν)
    let T : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ρ)
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let S : ℝ := s * h ^ 2
    let B : ℝ := Real.sqrt (Real.exp S * V)
    let M : ℝ := |μ| + 2 * s * Real.exp S * m3
    let U : Shao.Path N → ℝ := fun a => lindleyRegulator a i
    let Q : Shao.Path N → ℝ := fun a => Shao.prefixSquares a (i.val + 1)
    Integrable U T ∧
      Integrable (fun a : Shao.Path N => U a * Real.exp (-s * Q a)) P ∧
      0 ≤ (∫ a : Shao.Path N, U a * Real.exp (-s * Q a) ∂P) ∧
      (∫ a : Shao.Path N, U a ∂T) ≤
        B / Real.sqrt ((i.val + 1 : ℕ) : ℝ) + M ∧
      (∫ a : Shao.Path N, U a * Real.exp (-s * Q a) ∂P) ≤
        Real.exp (-(s * m2 / 2) * ((i.val + 1 : ℕ) : ℝ)) *
          (B / Real.sqrt ((i.val + 1 : ℕ) : ℝ) + M) := by
  dsimp only
  obtain ⟨_, hp, _, _, h2, _, _, _, _, _, _, _, hv, _, _, _, _, _, _, _, hm,
    _, _, _, hpow, _⟩ := boundedEnergyTilt_drift_decay ν h s hh hs hsupport hsmall
  dsimp only at hp h2 hv hm hpow
  let ρ : Measure ℝ := ν.tilted (fun a => -s * a ^ 2)
  letI : IsProbabilityMeasure ρ := hp
  let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ν)
  let T : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ρ)
  let U : Shao.Path N → ℝ := fun a => lindleyRegulator a i
  let Q : Shao.Path N → ℝ := fun a => Shao.prefixSquares a (i.val + 1)
  let Z : ℝ := ∫ a : ℝ, Real.exp (-s * a ^ 2) ∂ν
  let B : ℝ := Real.sqrt (Real.exp (s * h ^ 2) * variance (id : ℝ → ℝ) ν)
  let M : ℝ := |∫ a : ℝ, a ∂ν| + 2 * s * Real.exp (s * h ^ 2) *
    (∫ a : ℝ, |a| ^ 3 ∂ν)
  have hfirst := iid_lindleyRegulator_prefix_first_moment ρ h2 N i
  dsimp only at hfirst
  have htilt : (∫ a : Shao.Path N, U a ∂T) ≤
      B / Real.sqrt ((i.val + 1 : ℕ) : ℝ) + M := by
    exact hfirst.2.2.trans (add_le_add
      (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hv) (Real.sqrt_nonneg _)) hm)
  have hc := iid_lindleyRegulator_prefix_energy_change_of_measure ν h s hh hs hsupport N i
  dsimp only at hc
  have hr := hc.2.2.2.2.2.2.2.2.2.2.2.2 1 (Or.inl rfl)
  simp only [pow_one] at hr
  have hnon : 0 ≤ (∫ a : Shao.Path N, U a ∂T) :=
    integral_nonneg (fun a => (ew_reg_bounds a i).1)
  refine ⟨hfirst.1, hr.2.2.1, integral_nonneg (fun a =>
    mul_nonneg (ew_reg_bounds a i).1 (Real.exp_pos _).le), htilt, ?_⟩
  rw [hr.2.2.2.2]
  exact (mul_le_mul_of_nonneg_right (hpow (i.val + 1)) hnon).trans
    (mul_le_mul_of_nonneg_left htilt (Real.exp_pos _).le)

private theorem ew_weighted_half (w : ℕ → ℝ)
    (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1) (N : ℕ) :
    (∑ i : Fin N, w i.val / Real.sqrt ((i.val + 1 : ℕ) : ℝ)) ≤
      2 * Real.sqrt (∑ i : Fin N, w i.val) := by
  induction N with
  | zero => simp
  | succ N ih =>
    let C : ℝ := ∑ i : Fin N, w i.val
    have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => (hw i.val).1)
    have hCN : C ≤ (N : ℝ) := by
      calc
        _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (hw i.val).2)
        _ = _ := by simp
    have hn : 0 < ((N + 1 : ℕ) : ℝ) := by positivity
    have hnew : 0 ≤ C + w N := add_nonneg hC (hw N).1
    have hnewN : C + w N ≤ ((N + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [(hw N).2]
    have hd : 0 ≤ Real.sqrt (C + w N) - Real.sqrt C :=
      sub_nonneg.mpr (Real.sqrt_le_sqrt (le_add_of_nonneg_right (hw N).1))
    have hden : Real.sqrt (C + w N) + Real.sqrt C ≤
        2 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
      have h1 := Real.sqrt_le_sqrt hnewN
      have hNC : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ N
      have h2 := Real.sqrt_le_sqrt (hCN.trans hNC)
      linarith
    have hid : w N = (Real.sqrt (C + w N) - Real.sqrt C) *
        (Real.sqrt (C + w N) + Real.sqrt C) := by
      nlinarith [Real.sq_sqrt hnew, Real.sq_sqrt hC]
    have hstep : w N / Real.sqrt ((N + 1 : ℕ) : ℝ) ≤
        2 * (Real.sqrt (C + w N) - Real.sqrt C) := by
      apply (div_le_iff₀ (Real.sqrt_pos.mpr hn)).mpr
      have he := mul_le_mul_of_nonneg_left hden hd
      rw [← hid] at he
      nlinarith
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    calc
      _ ≤ 2 * Real.sqrt C +
          2 * (Real.sqrt (C + w N) - Real.sqrt C) := add_le_add ih hstep
      _ = _ := by ring

private theorem ew_clock_telescope (α : ℝ) (hα : 0 ≤ α) (N : ℕ) :
    α * (∑ i : Fin N, Real.exp (-α * ((i.val + 1 : ℕ) : ℝ))) ≤
      1 - Real.exp (-α * (N : ℝ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hexp : 1 + α ≤ Real.exp α := by linarith [Real.add_one_le_exp α]
    have he : Real.exp α * Real.exp (-α * ((N + 1 : ℕ) : ℝ)) =
        Real.exp (-α * (N : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    have hstep : α * Real.exp (-α * ((N + 1 : ℕ) : ℝ)) ≤
        Real.exp (-α * (N : ℝ)) - Real.exp (-α * ((N + 1 : ℕ) : ℝ)) := by
      have hm := mul_le_mul_of_nonneg_right hexp (Real.exp_pos
        (-α * ((N + 1 : ℕ) : ℝ))).le
      rw [he] at hm
      nlinarith
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    nlinarith

/-- Bundle 3: both finite clocks are conclusions, with no integral-comparison
or decay estimate supplied as an assumption. The empty clock is included. -/
theorem finite_energy_decay_clocks (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    let G : ℝ := ∑ i : Fin N,
      Real.exp (-(t / (N : ℝ)) * ((i.val + 1 : ℕ) : ℝ))
    let H : ℝ := ∑ i : Fin N,
      Real.exp (-(t / (N : ℝ)) * ((i.val + 1 : ℕ) : ℝ)) /
        Real.sqrt ((i.val + 1 : ℕ) : ℝ)
    0 ≤ G ∧ G ≤ (N : ℝ) ∧ t * G ≤ (N : ℝ) ∧
      G ≤ 2 * (N : ℝ) / (1 + t) ∧
      0 ≤ H ∧ H ≤ 2 * Real.sqrt G ∧
      H ≤ 2 * Real.sqrt (N : ℝ) ∧
      H ≤ 4 * Real.sqrt (N : ℝ) / (1 + Real.sqrt t) := by
  dsimp only
  by_cases hN : N = 0
  · subst N
    simp
  have hNp : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  let α := t / (N : ℝ)
  let w : ℕ → ℝ := fun k => Real.exp (-α * ((k + 1 : ℕ) : ℝ))
  let G : ℝ := ∑ i : Fin N, w i.val
  let H : ℝ := ∑ i : Fin N, w i.val / Real.sqrt ((i.val + 1 : ℕ) : ℝ)
  have hα : 0 ≤ α := div_nonneg ht hNp.le
  have hw (k : ℕ) : 0 ≤ w k ∧ w k ≤ 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα) (by positivity))⟩
  have hG : 0 ≤ G := Finset.sum_nonneg (fun i _ => (hw i.val).1)
  have hGN : G ≤ (N : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (hw i.val).2)
      _ = _ := by simp
  have htG : t * G ≤ (N : ℝ) := by
    have he := ew_clock_telescope α hα N
    have hh : α * G ≤ 1 := he.trans (by linarith [Real.exp_pos (-α * (N : ℝ))])
    have hm := mul_le_mul_of_nonneg_left hh hNp.le
    have hc : (N : ℝ) * α = t := by dsimp [α]; field_simp
    simpa only [← mul_assoc, hc, mul_one] using hm
  have hGbound : G ≤ 2 * (N : ℝ) / (1 + t) := by
    apply (le_div_iff₀ (by positivity : 0 < 1 + t)).mpr
    nlinarith
  have hH : 0 ≤ H := Finset.sum_nonneg (fun i _ =>
    div_nonneg (hw i.val).1 (Real.sqrt_nonneg _))
  have hhalf : H ≤ 2 * Real.sqrt G := ew_weighted_half w hw N
  have hcoarse : H ≤ 2 * Real.sqrt (N : ℝ) :=
    hhalf.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hGN) (by norm_num))
  refine ⟨hG, hGN, htG, hGbound, hH, hhalf, hcoarse, ?_⟩
  apply (le_div_iff₀ (by positivity : 0 < 1 + Real.sqrt t)).mpr
  have hHsq : H ^ 2 ≤ 4 * G := by
    nlinarith [Real.sq_sqrt hG, Real.sqrt_nonneg G]
  have hfactor : (1 + Real.sqrt t) ^ 2 ≤ 2 * (1 + t) := by
    nlinarith [Real.sq_sqrt ht, sq_nonneg (Real.sqrt t - 1)]
  have hGs : (1 + t) * G ≤ 2 * (N : ℝ) := by nlinarith
  have hs : (H * (1 + Real.sqrt t)) ^ 2 ≤ 16 * (N : ℝ) := by
    calc
      _ = H ^ 2 * (1 + Real.sqrt t) ^ 2 := by ring
      _ ≤ H ^ 2 * (2 * (1 + t)) := mul_le_mul_of_nonneg_left hfactor (sq_nonneg H)
      _ ≤ (4 * G) * (2 * (1 + t)) :=
        mul_le_mul_of_nonneg_right hHsq (by positivity)
      _ ≤ _ := by nlinarith
  have hn2 := Real.sq_sqrt hNp.le
  have hnn := Real.sqrt_nonneg (N : ℝ)
  have hh0 : 0 ≤ H * (1 + Real.sqrt t) := by positivity
  nlinarith

/-- Bundle 4a: genuine finite and restricted sums under one actual long law. -/
theorem iid_lindleyRegulator_energy_weighted_sum_first_moment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h s : ℝ) (hh : 0 < h) (hs : 0 ≤ s)
    (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (hsmall : s * h ^ 2 ≤ 1) (N : ℕ) :
    let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ν)
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let S : ℝ := s * h ^ 2
    let B : ℝ := Real.sqrt (Real.exp S * V)
    let M : ℝ := |μ| + 2 * s * Real.exp S * m3
    let t : ℝ := (s * m2 / 2) * (N : ℝ)
    let U : Fin N → Shao.Path N → ℝ := fun i a => lindleyRegulator a i
    let Q : Fin N → Shao.Path N → ℝ := fun i a =>
      Shao.prefixSquares a (i.val + 1)
    let F : Shao.Path N → ℝ := fun a =>
      ∑ i : Fin N, U i a * Real.exp (-s * Q i a)
    let C : ℝ := 4 * B * Real.sqrt (N : ℝ) / (1 + Real.sqrt t) +
      2 * (N : ℝ) * M / (1 + t)
    Integrable F P ∧ 0 ≤ (∫ a : Shao.Path N, F a ∂P) ∧
      (∫ a : Shao.Path N, F a ∂P) =
        ∑ i : Fin N, ∫ a : Shao.Path N, U i a * Real.exp (-s * Q i a) ∂P ∧
      (∫ a : Shao.Path N, F a ∂P) ≤ C ∧
      (∀ K : ℕ, K ≤ N →
        let FΚ : Shao.Path N → ℝ := fun a =>
          ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < K),
            U i a * Real.exp (-s * Q i a)
        Integrable FΚ P ∧ 0 ≤ (∫ a : Shao.Path N, FΚ a ∂P) ∧
          (∫ a : Shao.Path N, FΚ a ∂P) ≤ (∫ a : Shao.Path N, F a ∂P) ∧
          (∫ a : Shao.Path N, FΚ a ∂P) ≤ C) := by
  classical
  dsimp only
  let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ν)
  let μ : ℝ := ∫ a : ℝ, a ∂ν
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
  let V : ℝ := variance (id : ℝ → ℝ) ν
  let B : ℝ := Real.sqrt (Real.exp (s * h ^ 2) * V)
  let M : ℝ := |μ| + 2 * s * Real.exp (s * h ^ 2) * m3
  let t : ℝ := (s * m2 / 2) * (N : ℝ)
  let f : Fin N → Shao.Path N → ℝ := fun i a =>
    lindleyRegulator a i * Real.exp (-s * Shao.prefixSquares a (i.val + 1))
  let F : Shao.Path N → ℝ := fun a => ∑ i : Fin N, f i a
  let C : ℝ := 4 * B * Real.sqrt (N : ℝ) / (1 + Real.sqrt t) +
    2 * (N : ℝ) * M / (1 + t)
  have h (i : Fin N) := iid_lindleyRegulator_prefix_energy_first_moment ν h s hh hs
    hsupport hsmall N i
  dsimp only at h
  have hi (i : Fin N) : Integrable (f i) P := (h i).2.1
  have hfn (i : Fin N) (a : Shao.Path N) : 0 ≤ f i a :=
    mul_nonneg (ew_reg_bounds a i).1 (Real.exp_pos _).le
  have hFI : Integrable F P := integrable_finsetSum Finset.univ (fun i _ => hi i)
  have hFE : (∫ a : Shao.Path N, F a ∂P) = ∑ i : Fin N, ∫ a, f i a ∂P :=
    integral_finsetSum Finset.univ (fun i _ => hi i)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hm3 : 0 ≤ m3 := integral_nonneg (fun a => pow_nonneg (abs_nonneg a) 3)
  have hM : 0 ≤ M := add_nonneg (abs_nonneg _) (by positivity)
  have hm2 : 0 ≤ m2 := integral_nonneg (fun a => sq_nonneg a)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hbound : (∫ a : Shao.Path N, F a ∂P) ≤ C := by
    by_cases hN : N = 0
    · subst N
      simp [F, C]
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    have hclock := finite_energy_decay_clocks N t ht
    dsimp only at hclock
    have htdiv : t / (N : ℝ) = s * m2 / 2 := by
      dsimp [t]
      exact mul_div_cancel_right₀ _ hNr
    rw [htdiv] at hclock
    let G : ℝ := ∑ i : Fin N, Real.exp (-(s * m2 / 2) * ((i.val + 1 : ℕ) : ℝ))
    let H : ℝ := ∑ i : Fin N,
      Real.exp (-(s * m2 / 2) * ((i.val + 1 : ℕ) : ℝ)) /
        Real.sqrt ((i.val + 1 : ℕ) : ℝ)
    have heq : (∑ i : Fin N, Real.exp (-(s * m2 / 2) * ((i.val + 1 : ℕ) : ℝ)) *
        (B / Real.sqrt ((i.val + 1 : ℕ) : ℝ) + M)) = B * H + M * G := by
      dsimp [G, H]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    calc
      _ = ∑ i : Fin N, ∫ a, f i a ∂P := hFE
      _ ≤ ∑ i : Fin N, Real.exp (-(s * m2 / 2) * ((i.val + 1 : ℕ) : ℝ)) *
          (B / Real.sqrt ((i.val + 1 : ℕ) : ℝ) + M) :=
        Finset.sum_le_sum (fun i _ => (h i).2.2.2.2)
      _ = B * H + M * G := heq
      _ ≤ B * (4 * Real.sqrt (N : ℝ) / (1 + Real.sqrt t)) +
          M * (2 * (N : ℝ) / (1 + t)) :=
        add_le_add (mul_le_mul_of_nonneg_left hclock.2.2.2.2.2.2.2 hB)
          (mul_le_mul_of_nonneg_left hclock.2.2.2.1 hM)
      _ = C := by dsimp [C]; ring
  refine ⟨hFI, integral_nonneg (fun a => Finset.sum_nonneg (fun i _ => hfn i a)),
    hFE, hbound, ?_⟩
  intro K _
  let I := Finset.univ.filter (fun i : Fin N => i.val < K)
  have hKI : Integrable (fun a : Shao.Path N => ∑ i ∈ I, f i a) P :=
    integrable_finsetSum I (fun i _ => hi i)
  have hpoint (a : Shao.Path N) : (∑ i ∈ I, f i a) ≤ F a :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => hfn i a)
  have hle := integral_mono hKI hFI hpoint
  exact ⟨hKI, integral_nonneg (fun a => Finset.sum_nonneg (fun i _ => hfn i a)),
    hle, hle.trans hbound⟩

/-- Bundle 4b: the original conditional increment law and threshold/budget
pay a concrete constant, without a survival or a Lambda-smallness input.
For fixed positive kappa the source constant is 128/sqrt(kappa). -/
theorem sourceTruncation_lindleyRegulator_energy_weighted_first_sum
    (ν0 : Measure ℝ) [IsProbabilityMeasure ν0] (N : ℕ)
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν0)
    (hnorm : (N : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1)
    (hmean : (∫ a : ℝ, a ∂ν0) = 0)
    (x ε ε0 κ y : ℝ) (hx : 0 ≤ x) (hε : 0 < ε)
    (hε0 : 0 < ε0) (hε01 : ε0 ≤ 1) (hεsmall : ε ≤ ε0 / 2)
    (hR : Shao.truncationBudget ν0 N x ≤ ε ^ 3 / 8)
    (hκ : 0 < κ) (hκsmall : κ ≤ (1 / 16 : ℝ)) (hy : 1 ≤ y)
    (hwindow : |y - x| ≤ 1 / (2 * (1 + x))) :
    let ν : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ ε / (1 + x)}
    let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ν)
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let Λ : ℝ := (1 + y) * (N : ℝ) * |μ| +
      (1 + y) ^ 3 * (N : ℝ) * m3
    let U : Fin N → Shao.Path N → ℝ := fun i a => lindleyRegulator a i
    let Q : Fin N → Shao.Path N → ℝ := fun i a =>
      Shao.prefixSquares a (i.val + 1)
    let F : Shao.Path N → ℝ := fun a =>
      ∑ i : Fin N, U i a * Real.exp (-(κ * y ^ 2) * Q i a)
    IsProbabilityMeasure ν ∧
      (∀ᵐ a : ℝ ∂ν, |a| ≤ ε / (1 + x)) ∧
      (κ * y ^ 2) * (ε / (1 + x)) ^ 2 ≤ 1 ∧
      (3 / 4 : ℝ) ≤ (N : ℝ) * m2 ∧
      (N : ℝ) * V ≤ (4 / 3 : ℝ) ∧
      0 ≤ Λ ∧ Λ ≤ (1 / 2 : ℝ) ∧
      Integrable F P ∧ 0 ≤ (∫ a : Shao.Path N, F a ∂P) ∧
      (∫ a : Shao.Path N, F a ∂P) ≤
        128 / (Real.sqrt κ * (1 + y)) ∧
      (∀ K : ℕ, K ≤ N →
        let FΚ : Shao.Path N → ℝ := fun a =>
          ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < K),
            U i a * Real.exp (-(κ * y ^ 2) * Q i a)
        Integrable FΚ P ∧ 0 ≤ (∫ a : Shao.Path N, FΚ a ∂P) ∧
          (∫ a : Shao.Path N, FΚ a ∂P) ≤
            128 / (Real.sqrt κ * (1 + y))) := by
  classical
  dsimp only
  let ν : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ ε / (1 + x)}
  let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ν)
  let μ : ℝ := ∫ a : ℝ, a ∂ν
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
  let V : ℝ := variance (id : ℝ → ℝ) ν
  let a : ℝ := 1 + x
  let b : ℝ := 1 + y
  let R : ℝ := Shao.truncationBudget ν0 N x
  let A : ℝ := (N : ℝ) * |μ|
  let D : ℝ := (N : ℝ) * m3
  let Λ : ℝ := b * A + b ^ 3 * D
  let h : ℝ := ε / a
  let s : ℝ := κ * y ^ 2
  let S : ℝ := s * h ^ 2
  let B : ℝ := Real.sqrt (Real.exp S * V)
  let M : ℝ := |μ| + 2 * s * Real.exp S * m3
  let t : ℝ := (s * m2 / 2) * (N : ℝ)
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hy0 : 0 ≤ y := by linarith
  have hεhalf : ε ≤ (1 / 2 : ℝ) := by linarith
  obtain ⟨_, _, hp, hsp, _, _, _, _⟩ :=
    Shao.sourceTruncation_law_data ν0 N h2 hnorm x ε hx hε hεhalf hR
  letI : IsProbabilityMeasure ν := hp
  obtain ⟨hraw, _, _, _, _, _, _, hvar⟩ :=
    Shao.sourceTruncation_variance_bounds ν0 N h2 hnorm hmean x ε hx hε hεhalf hR
  obtain ⟨hmu, hm3, _, _, _⟩ :=
    Shao.sourceTruncation_paid_moments ν0 N h2 hnorm hmean x ε hx hε hεhalf hR
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hm30 : 0 ≤ m3 := integral_nonneg (fun z => pow_nonneg (abs_nonneg z) 3)
  have hm20 : 0 ≤ m2 := integral_nonneg (fun z => sq_nonneg z)
  have hV0 : 0 ≤ V := variance_nonneg _ _
  have hA0 : 0 ≤ A := mul_nonneg hN (abs_nonneg _)
  have hD0 : 0 ≤ D := mul_nonneg hN hm30
  have hκ1 : κ ≤ 1 := by linarith
  have hratio : b ≤ 2 * a := by
    have hu := (abs_le.mp hwindow).2
    have hfrac : 1 / (2 * (1 + x)) ≤ (1 : ℝ) := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * (1 + x))).mpr
      linarith
    dsimp [a, b]
    linarith
  have hL0 : 0 ≤ Λ := by dsimp [Λ]; positivity
  have hLhalf : Λ ≤ (1 / 2 : ℝ) := by
    have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
    have hApaid : ε ^ 2 * a * A ≤ 2 * R := by
      simpa only [mul_comm] using (le_div_iff₀ (mul_pos hε2 ha)).mp hmu
    have hDpaid : a ^ 3 * D ≤ 2 * R := by
      simpa only [mul_comm] using (le_div_iff₀ (pow_pos ha 3)).mp hm3
    have hAup : b * A ≤ 4 * R / ε ^ 2 := by
      apply (le_div_iff₀ hε2).mpr
      have hrat := mul_le_mul_of_nonneg_right hratio hA0
      have hrat2 := mul_le_mul_of_nonneg_right hrat hε2.le
      nlinarith only [hApaid, hrat2]
    have hDup : b ^ 3 * D ≤ 16 * R := by
      have he := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb.le hratio 3) hD0
      nlinarith only [he, hDpaid]
    have hRε : 4 * R / ε ^ 2 ≤ ε / 2 := by
      apply (div_le_iff₀ hε2).mpr
      change R ≤ ε ^ 3 / 8 at hR
      nlinarith only [hR]
    have hc : ε ^ 3 ≤ (1 / 8 : ℝ) := by
      have he := pow_le_pow_left₀ hε.le hεhalf 3
      norm_num at he ⊢
      exact he
    dsimp only [Λ]
    change R ≤ ε ^ 3 / 8 at hR
    nlinarith only [hAup, hDup, hRε, hR, hc, hεhalf]
  have hh : 0 < h := div_pos hε ha
  have hS : S ≤ 1 := by
    have hbh : b * h ≤ ε0 := by
      have he := mul_le_mul_of_nonneg_right hratio hh.le
      have hah : a * h = ε := by dsimp [h]; field_simp
      rw [mul_assoc, hah] at he
      linarith only [he, hεsmall]
    have hyh : 0 ≤ y * h := mul_nonneg hy0 hh.le
    have hyh1 : y * h ≤ 1 := by dsimp [b] at hbh; nlinarith only [hbh, hε01, hh]
    have hsq : (y * h) ^ 2 ≤ 1 := by nlinarith only [hyh, hyh1]
    have he := mul_le_mul_of_nonneg_left hsq hκ.le
    dsimp [S, s]
    nlinarith only [he, hκ1]
  have hs : 0 ≤ s := mul_nonneg hκ.le (sq_nonneg y)
  have hS0 : 0 ≤ S := mul_nonneg hs (sq_nonneg h)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have heS : Real.exp S ≤ 3 := by
    have he := Real.exp_le_exp.mpr hS
    have he3 : Real.exp (1 : ℝ) < 3 := Real.exp_one_lt_three
    linarith only [he, he3]
  have hBN : B * Real.sqrt (N : ℝ) ≤ 2 := by
    have hi0 : 0 ≤ Real.exp S * V := mul_nonneg (Real.exp_pos _).le hV0
    have hi : Real.exp S * V * (N : ℝ) ≤ 4 := by
      have he := mul_le_mul_of_nonneg_right heS (mul_nonneg hV0 hN)
      change (N : ℝ) * V ≤ (4 / 3 : ℝ) at hvar
      nlinarith only [he, hvar]
    dsimp [B]
    rw [← Real.sqrt_mul hi0]
    have hp0 : 0 ≤ Real.exp S * V * (N : ℝ) := mul_nonneg hi0 hN
    have hsq := Real.sq_sqrt hp0
    have hn := Real.sqrt_nonneg (Real.exp S * V * (N : ℝ))
    nlinarith only [hsq, hn, hi]
  have htlow : (3 * κ / 8) * y ^ 2 ≤ t := by
    change (3 / 4 : ℝ) ≤ (N : ℝ) * m2 at hraw
    have he := mul_le_mul_of_nonneg_left hraw (show 0 ≤ κ * y ^ 2 / 2 by positivity)
    dsimp [t, s]
    nlinarith only [he]
  have hq : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hq1 : Real.sqrt κ ≤ 1 := by
    have he := Real.sqrt_le_sqrt hκ1
    simpa using he
  have htsqrt : (Real.sqrt κ / 2) * y ≤ Real.sqrt t := by
    have heq := Real.sq_sqrt hκ.le
    have het := Real.sq_sqrt ht0
    have hnn := Real.sqrt_nonneg t
    have hleft : 0 ≤ (Real.sqrt κ / 2) * y := by positivity
    have hlsq : ((Real.sqrt κ / 2) * y) ^ 2 ≤ t := by
      calc
        _ = (κ / 4) * y ^ 2 := by rw [mul_pow, div_pow, heq]; ring
        _ ≤ (3 * κ / 8) * y ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith only [hκ]) (sq_nonneg y)
        _ ≤ t := htlow
    nlinarith only [hlsq, het, hnn, hleft]
  have hden : (Real.sqrt κ / 2) * b ≤ 1 + Real.sqrt t := by
    dsimp [b]
    nlinarith only [htsqrt, hq1]
  have hNM : (N : ℝ) * M ≤ 7 * Λ / b := by
    have hyb : κ * y ^ 2 ≤ b ^ 2 := by
      have he := mul_le_mul_of_nonneg_right hκ1 (sq_nonneg y)
      dsimp [b]
      nlinarith only [he, hy0]
    have hL1 : b * A ≤ Λ := le_add_of_nonneg_right (by positivity)
    have hL3 : b ^ 3 * D ≤ Λ := le_add_of_nonneg_left (by positivity)
    have hdy := mul_le_mul_of_nonneg_right hyb (mul_nonneg hb.le hD0)
    have hdyL : b * (κ * y ^ 2) * D ≤ Λ := by nlinarith only [hdy, hL3]
    have hup : (N : ℝ) * M ≤ A + 6 * κ * y ^ 2 * D := by
      have he := mul_le_mul_of_nonneg_right heS (show 0 ≤ 2 * s * D by positivity)
      dsimp only [M, A, D, s] at he ⊢
      nlinarith only [he]
    apply (le_div_iff₀ hb).mpr
    have he := mul_le_mul_of_nonneg_right hup hb.le
    nlinarith only [he, hL1, hdyL]
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hC : 4 * B * Real.sqrt (N : ℝ) / (1 + Real.sqrt t) +
      2 * (N : ℝ) * M / (1 + t) ≤ 128 / (Real.sqrt κ * b) := by
    have h1 : 4 * B * Real.sqrt (N : ℝ) / (1 + Real.sqrt t) ≤
        16 / (Real.sqrt κ * b) := by
      calc
        _ ≤ 8 / (1 + Real.sqrt t) :=
          div_le_div_of_nonneg_right (by nlinarith only [hBN]) (by positivity)
        _ ≤ 8 / ((Real.sqrt κ / 2) * b) := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          nlinarith only [hden]
        _ = _ := by field_simp; ring
    have h2 : 2 * (N : ℝ) * M / (1 + t) ≤ 7 / (Real.sqrt κ * b) := by
      calc
        _ ≤ 2 * (N : ℝ) * M := by
          apply (div_le_iff₀ (by positivity : 0 < 1 + t)).mpr
          nlinarith only [mul_nonneg (show 0 ≤ 2 * (N : ℝ) * M by positivity) ht0]
        _ ≤ 14 * Λ / b := by
          calc
            _ = 2 * ((N : ℝ) * M) := by ring
            _ ≤ 2 * (7 * Λ / b) := mul_le_mul_of_nonneg_left hNM (by norm_num)
            _ = _ := by ring
        _ ≤ 7 / b := div_le_div_of_nonneg_right (by nlinarith only [hLhalf]) hb.le
        _ ≤ 7 / (Real.sqrt κ * b) := by
          apply (div_le_div_iff₀ hb (mul_pos hq hb)).mpr
          nlinarith only [mul_le_mul_of_nonneg_right hq1 hb.le]
    have hdpos : 0 < Real.sqrt κ * b := mul_pos hq hb
    have h23 : 16 / (Real.sqrt κ * b) + 7 / (Real.sqrt κ * b) =
        23 / (Real.sqrt κ * b) := by ring
    exact (add_le_add h1 h2).trans (h23.le.trans
      (div_le_div_of_nonneg_right (by norm_num) hdpos.le))
  have hg := iid_lindleyRegulator_energy_weighted_sum_first_moment ν h s hh hs hsp hS N
  dsimp only at hg
  obtain ⟨hFI, hFn, _, hFC, hpart⟩ := hg
  refine ⟨hp, hsp, hS, hraw, hvar,
    by simpa only [Λ, b, A, D, mul_assoc] using hL0,
    by simpa only [Λ, b, A, D, mul_assoc] using hLhalf,
    hFI, hFn, hFC.trans hC, ?_⟩
  intro K hK
  obtain ⟨hKI, hKn, _, hKC⟩ := hpart K hK
  exact ⟨hKI, hKn, hKC.trans hC⟩

end Shao.Probability
