import Shao.OQ3.JointNonlattice
import Shao.OQ3.FiniteNormalSpan
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Actual finite-stage normal far-arc contraction

Source: current/oq3/proofs/r1/report.md, lines 309-348, especially 338-345.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U12a v2 scope: 9482dfb3ec45d59c19200b20d81692773c033b06021a6855cccc7fe2c76d0da4.
This module does not assert a central expansion or a local limit theorem.
-/

namespace Shao.OQ3

open MeasureTheory

noncomputable section

def centeredNormalTangentCharacteristic (mu : Measure ℝ) (q a t s : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp
    (((t * (normalValue x - q) + s * (x - a) : ℝ) : ℂ) * Complex.I) ∂mu

theorem centeredNormalTangentCharacteristic_factor (mu : Measure ℝ)
    (q a t s : ℝ) :
    centeredNormalTangentCharacteristic mu q a t s =
      Complex.exp (((-(t * q + s * a) : ℝ) : ℂ) * Complex.I) *
        jointCharacteristic mu (8 * t + s) (-t) := by
  have heq : (fun x : ℝ => Complex.exp
      (((t * (normalValue x - q) + s * (x - a) : ℝ) : ℂ) * Complex.I)) =
      (fun x : ℝ => Complex.exp (((-(t * q + s * a) : ℝ) : ℂ) * Complex.I) *
        jointPhase (8 * t + s) (-t) x) := by
    funext x
    unfold jointPhase
    rw [← Complex.exp_add]
    congr 1
    unfold normalValue
    push_cast
    ring
  unfold centeredNormalTangentCharacteristic jointCharacteristic
  rw [heq, integral_const_mul]

private theorem centered_norm_eq_joint (mu : Measure ℝ) (q a t s : ℝ) :
    ‖centeredNormalTangentCharacteristic mu q a t s‖ =
      ‖jointCharacteristic mu (8 * t + s) (-t)‖ := by
  rw [centeredNormalTangentCharacteristic_factor, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]

theorem centeredNormalTangentCharacteristic_continuous (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (q a : ℝ) :
    Continuous (fun v : ℝ × ℝ =>
      centeredNormalTangentCharacteristic mu q a v.1 v.2) := by
  unfold centeredNormalTangentCharacteristic
  apply continuous_of_dominated (bound := fun _ : ℝ => 1)
  · intro v
    have hf : Continuous (fun x : ℝ => Complex.exp
        (((v.1 * (normalValue x - q) + v.2 * (x - a) : ℝ) : ℂ) * Complex.I)) := by
      unfold normalValue
      fun_prop
    exact hf.aestronglyMeasurable
  · intro v
    exact Filter.Eventually.of_forall fun x => (Complex.norm_exp_ofReal_mul_I _).le
  · exact integrable_const 1
  · exact Filter.Eventually.of_forall fun x => by fun_prop

theorem stage_centered_normal_modulus_one_iff (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a t : ℝ)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ‖centeredNormalTangentCharacteristic mu q a t 0‖ = 1 ↔
      ∃ m : ℤ, t * dyadicMesh J = (2 * Real.pi) * (m : ℝ) := by
  rw [centered_norm_eq_joint, add_zero]
  constructor
  · intro hmod
    have hpair (x y : ℝ) (hx : 0 < mu.real {x}) (hy : 0 < mu.real {y}) :
        ∃ m : ℤ, t * (normalValue x - normalValue y) = (2 * Real.pi) * (m : ℝ) := by
      obtain ⟨m, hm⟩ := (jointPhase_eq_iff_lattice (8 * t) (-t) x y).mp
        (jointPhase_eq_of_modulus_one mu (8 * t) (-t) hmod x y hx hy)
      refine ⟨m, ?_⟩
      calc
        t * (normalValue x - normalValue y) =
            (8 * t) * (x - y) + (-t) * (x ^ 2 - y ^ 2) := by
          unfold normalValue
          ring
        _ = _ := hm
    cases J with
    | zero =>
      have hx : 0 < mu.real {baseAtom 1} := hpos (Sum.inl 1)
      have hy : 0 < mu.real {baseAtom 2} := hpos (Sum.inl 2)
      have hd : normalValue (baseAtom 1) - normalValue (baseAtom 2) = (1 : ℝ) := by
        rw [congrFun normalValue_baseAtom 1, congrFun normalValue_baseAtom 2]
        norm_num
      obtain ⟨m, hm⟩ := hpair _ _ hx hy
      refine ⟨m, ?_⟩
      simpa only [hd, mul_one, dyadicMesh, pow_zero, inv_one] using hm
    | succ J =>
      have hx : 0 < mu.real {addedAtom J} := hpos (Sum.inr ⟨J, Nat.lt_succ_self J⟩)
      have hy : 0 < mu.real {baseAtom 2} := hpos (Sum.inl 2)
      obtain ⟨m, hm⟩ := hpair _ _ hx hy
      exact ⟨m, by simpa only [addedAtom_normal_difference] using hm⟩
  · rintro ⟨m, hm⟩
    have hae : ∀ᵐ x ∂mu, jointPhase (8 * t) (-t) x = 1 := by
      filter_upwards [hrange] with x hx
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨k, hk⟩ := stageAtom_normalValue_lattice J i
      have he := (jointPhase_eq_iff_lattice (8 * t) (-t)
        (stageAtom (fun j : Fin J => addedAtom j.val) i) 0).mpr
        (show ∃ l : ℤ,
          (8 * t) * (stageAtom (fun j : Fin J => addedAtom j.val) i - 0) +
            (-t) * ((stageAtom (fun j : Fin J => addedAtom j.val) i) ^ 2 - 0 ^ 2) =
              (2 * Real.pi) * (l : ℝ) from by
          refine ⟨m * k, ?_⟩
          calc
            _ = t * normalValue (stageAtom (fun j : Fin J => addedAtom j.val) i) := by
              unfold normalValue
              ring
            _ = t * (dyadicMesh J * (k : ℝ)) := by rw [hk]
            _ = _ := by rw [← mul_assoc, hm]; push_cast; ring)
      simpa [jointPhase] using he
    have hchar : jointCharacteristic mu (8 * t) (-t) = 1 := by
      unfold jointCharacteristic
      calc
        _ = ∫ _ : ℝ, (1 : ℂ) ∂mu := integral_congr_ae hae
        _ = 1 := by simp [measureReal_def]
    rw [hchar, norm_one]

theorem stage_centered_normal_fundamental_lt (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a t : ℝ)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (ht : 0 < |t|) (hband : |t| ≤ Real.pi / dyadicMesh J) :
    ‖centeredNormalTangentCharacteristic mu q a t 0‖ < 1 := by
  have hh : 0 < dyadicMesh J := by unfold dyadicMesh; positivity
  have hle : ‖centeredNormalTangentCharacteristic mu q a t 0‖ ≤ 1 := by
    rw [centered_norm_eq_joint]
    exact jointCharacteristic_norm_le_one _ _ _
  by_contra hnlt
  have hmod := le_antisymm hle (not_lt.mp hnlt)
  obtain ⟨m, hm⟩ := (stage_centered_normal_modulus_one_iff mu J q a t hrange hpos).mp hmod
  have hsmall : |t| * dyadicMesh J ≤ Real.pi := (le_div_iff₀ hh).mp hband
  have habs : |t| * dyadicMesh J = (2 * Real.pi) * |(m : ℝ)| := by
    simpa only [abs_mul, abs_of_pos hh, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos Real.pi_pos] using
      congrArg abs hm
  by_cases hz : m = 0
  · have ht0 : t = 0 := by simpa [hz, hh.ne'] using hm
    simp [ht0] at ht
  · have hlarge : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hz
    nlinarith [Real.pi_pos]

theorem stage_far_arc_uniform (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (J : ℕ) (q a : ℝ)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (K : Set ℝ) (hK : IsCompact K) (hzero : (0 : ℝ) ∉ K)
    (hband : ∀ t ∈ K, |t| ≤ Real.pi / dyadicMesh J) :
    ∃ eta rho : ℝ, 0 < eta ∧ 0 < rho ∧ rho < 1 ∧
      ∀ t ∈ K, ∀ s : ℝ, |s| < eta →
        ‖centeredNormalTangentCharacteristic mu q a t s‖ < rho := by
  classical
  by_cases hne : K.Nonempty
  · have hcont := centeredNormalTangentCharacteristic_continuous mu q a
    have hcont0 : Continuous (fun t : ℝ =>
        ‖centeredNormalTangentCharacteristic mu q a t 0‖) :=
      (hcont.comp (continuous_id.prodMk continuous_const)).norm
    obtain ⟨tmax, htmax, hmax⟩ := hK.exists_isMaxOn hne hcont0.continuousOn
    have hstrict (t : ℝ) (ht : t ∈ K) :
        ‖centeredNormalTangentCharacteristic mu q a t 0‖ < 1 := by
      apply stage_centered_normal_fundamental_lt mu J q a t hrange hpos
      · exact abs_pos.mpr (fun hz => hzero (hz ▸ ht))
      · exact hband t ht
    let rho := (‖centeredNormalTangentCharacteristic mu q a tmax 0‖ + 1) / 2
    have hrho : 0 < rho := by
      dsimp [rho]
      linarith [norm_nonneg (centeredNormalTangentCharacteristic mu q a tmax 0)]
    have hrho1 : rho < 1 := by dsimp [rho]; linarith [hstrict tmax htmax]
    have hmrho : ‖centeredNormalTangentCharacteristic mu q a tmax 0‖ < rho := by
      dsimp [rho]
      linarith [hstrict tmax htmax]
    let U : Set (ℝ × ℝ) := {v | ‖centeredNormalTangentCharacteristic mu q a v.1 v.2‖ < rho}
    have hU : IsOpen U := isOpen_lt hcont.norm continuous_const
    have hprod : K ×ˢ ({0} : Set ℝ) ⊆ U := by
      intro v hv
      have hv0 : v.2 = 0 := Set.mem_singleton_iff.mp hv.2
      change ‖centeredNormalTangentCharacteristic mu q a v.1 v.2‖ < rho
      rw [hv0]
      exact (hmax hv.1).trans_lt hmrho
    obtain ⟨V, W, _, hW, hKV, h0W, hVW⟩ := generalized_tube_lemma hK
      (isCompact_singleton (x := (0 : ℝ))) hU hprod
    obtain ⟨eta, heta, hball⟩ := Metric.isOpen_iff.mp hW 0 (h0W (by simp))
    refine ⟨eta, rho, heta, hrho, hrho1, ?_⟩
    intro t ht s hs
    change (t, s) ∈ U
    apply hVW
    exact ⟨hKV ht, hball (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hs)⟩
  · have hKe : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨1, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    simp [hKe]

theorem stage_far_arc_power_integral (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (J : ℕ) (q a : ℝ)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (K : Set ℝ) (hK : IsCompact K) (hzero : (0 : ℝ) ∉ K)
    (hband : ∀ t ∈ K, |t| ≤ Real.pi / dyadicMesh J) :
    ∃ eta rho : ℝ, 0 < eta ∧ 0 < rho ∧ rho < 1 ∧
      ∀ s : ℝ, |s| < eta → ∀ n : ℕ,
        (IntegrableOn (fun t : ℝ =>
          centeredNormalTangentCharacteristic mu q a t s ^ n) K) ∧
        ‖∫ t : ℝ in K, centeredNormalTangentCharacteristic mu q a t s ^ n‖ ≤
          volume.real K * rho ^ n := by
  obtain ⟨eta, rho, heta, hrho, hrho1, hbound⟩ :=
    stage_far_arc_uniform mu J q a hrange hpos K hK hzero hband
  refine ⟨eta, rho, heta, hrho, hrho1, ?_⟩
  intro s hs n
  have hcont : Continuous (fun t : ℝ => centeredNormalTangentCharacteristic mu q a t s ^ n) :=
    ((centeredNormalTangentCharacteristic_continuous mu q a).comp
      (continuous_id.prodMk continuous_const)).pow n
  refine ⟨hcont.continuousOn.integrableOn_compact hK, ?_⟩
  have hint := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ))
    hK.measure_lt_top (f := fun t : ℝ => centeredNormalTangentCharacteristic mu q a t s ^ n)
    (C := rho ^ n) (fun t ht => by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound t ht s hs).le n)
  simpa only [mul_comm] using hint

end
end Shao.OQ3
