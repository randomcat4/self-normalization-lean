import Shao.OQ6.FiniteHilbertSignMoments
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

set_option autoImplicit false

namespace Shao.OQ6.FiniteQuadraticSignChaos

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal
open Shao.OQ6.FiniteHilbertSignMoments

def quadratic (n : ℕ) (D : Fin n → Fin n → ℝ) (w : Shao.Path n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, D i j * w i * w j

def entryEnergy (n : ℕ) (D : Fin n → Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, ∑ i : Fin n, D i j ^ 2

private def bilinear (n : ℕ) (D : Fin n → Fin n → ℝ)
    (s : Fin n → Bool) (t : Fin n → Bool) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, D i j * signValue (s i) * signValue (t j)

private def cutMatrix (n : ℕ) (D : Fin n → Fin n → ℝ)
    (δ : Fin n → Bool) : Fin n → Fin n → ℝ :=
  fun (i : Fin n) (j : Fin n) =>
    if δ i then (if δ j then 0 else D i j) else 0

private theorem cubeMean_abs_rpow_jensen
    (n : ℕ) (f : (Fin n → Bool) → ℝ) (q : ℝ) (hq : 1 ≤ q) :
    Real.rpow |cubeMean n f| q ≤
      cubeMean n (fun s : Fin n → Bool => Real.rpow |f s| q) := by
  classical
  let c : ℝ := ((2 : ℝ) ^ n)⁻¹
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hcard : c * (Fintype.card (Fin n → Bool) : ℝ) = 1 := by
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow,
      Nat.cast_ofNat]
    dsimp only [c]
    exact inv_mul_cancel₀ (by positivity)
  have hweights : (∑ s : Fin n → Bool, c) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    exact hcard
  have hsumneg : -(∑ s : Fin n → Bool, |f s|) ≤ ∑ s : Fin n → Bool, f s := by
    calc
      -(∑ s : Fin n → Bool, |f s|) = ∑ s : Fin n → Bool, -|f s| := by
        rw [Finset.sum_neg_distrib]
      _ ≤ ∑ s : Fin n → Bool, f s :=
        Finset.sum_le_sum (fun s _ => neg_abs_le (f s))
  have habs : |cubeMean n f| ≤ cubeMean n (fun s : Fin n → Bool => |f s|) := by
    apply abs_le.mpr
    constructor
    · change -(c * ∑ s : Fin n → Bool, |f s|) ≤ c * ∑ s : Fin n → Bool, f s
      nlinarith [mul_le_mul_of_nonneg_left hsumneg hc]
    · change c * (∑ s : Fin n → Bool, f s) ≤
        c * ∑ s : Fin n → Bool, |f s|
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun s _ => le_abs_self (f s))) hc
  have hjensen :
      Real.rpow (cubeMean n (fun s : Fin n → Bool => |f s|)) q ≤
        cubeMean n (fun s : Fin n → Bool => Real.rpow |f s| q) := by
    have h := (convexOn_rpow (p := q) hq).map_sum_le
      (t := (Finset.univ : Finset (Fin n → Bool)))
      (w := fun _s : Fin n → Bool => c)
      (p := fun s : Fin n → Bool => |f s|)
      (fun _s _hs => hc) hweights (fun s _hs => abs_nonneg (f s))
    simpa only [smul_eq_mul, ← Finset.mul_sum, c, cubeMean, Real.rpow_eq_pow] using h
  exact (Real.rpow_le_rpow (abs_nonneg _) habs (by linarith)).trans hjensen

private theorem cut_entry_mean
    (n : ℕ) (i : Fin n) (j : Fin n) (hij : i ≠ j) :
    cubeMean n (fun δ : Fin n → Bool =>
      if δ i then (if δ j then (0 : ℝ) else 1) else 0) = (1 : ℝ) / 4 := by
  classical
  let flip : Fin n → (Fin n → Bool) → (Fin n → Bool) :=
    fun (k : Fin n) (δ : Fin n → Bool) (r : Fin n) =>
      if r = k then Bool.not (δ r) else δ r
  let chi : (Fin n → Bool) → ℝ :=
    fun δ : Fin n → Bool =>
      if δ i then (if δ j then (0 : ℝ) else 1) else 0
  have hflipinv : ∀ (k : Fin n) (δ : Fin n → Bool), flip k (flip k δ) = δ := by
    intro k δ
    funext r
    by_cases hr : r = k <;> simp [flip, hr]
  have hflipbij : ∀ k : Fin n, Function.Bijective (flip k) := by
    intro k
    constructor
    · intro s t hst
      calc
        s = flip k (flip k s) := (hflipinv k s).symm
        _ = flip k (flip k t) := congrArg (flip k) hst
        _ = t := hflipinv k t
    · intro s
      exact ⟨flip k s, hflipinv k s⟩
  have hcompbij :
      Function.Bijective (fun δ : Fin n → Bool => flip i (flip j δ)) :=
    (hflipbij i).comp (hflipbij j)
  have hpoint : ∀ δ : Fin n → Bool,
      chi δ + chi (flip i δ) + chi (flip j δ) + chi (flip i (flip j δ)) = 1 := by
    intro δ
    cases hi : δ i <;> cases hj : δ j <;>
      simp [chi, flip, hi, hj, hij, Ne.symm hij]
  have hsum :
      (∑ δ : Fin n → Bool,
        (chi δ + chi (flip i δ) + chi (flip j δ) + chi (flip i (flip j δ)))) =
        ∑ _δ : Fin n → Bool, (1 : ℝ) :=
    Finset.sum_congr rfl (fun δ _ => hpoint δ)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hsum
  rw [(hflipbij i).sum_comp chi, (hflipbij j).sum_comp chi,
    hcompbij.sum_comp chi] at hsum
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) = (2 : ℝ) ^ n := by
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow,
      Nat.cast_ofNat]
  rw [hcard] at hsum
  have hS : (∑ δ : Fin n → Bool, chi δ) = (2 : ℝ) ^ n / 4 := by linarith
  change ((2 : ℝ) ^ n)⁻¹ * (∑ δ : Fin n → Bool, chi δ) = (1 : ℝ) / 4
  rw [hS]
  field_simp [pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)] <;> ring

private theorem partition_mean
    (n : ℕ) (D : Fin n → Fin n → ℝ) (w : Shao.Path n)
    (hdiag : ∀ i : Fin n, D i i = 0) :
    cubeMean n (fun δ : Fin n → Bool => quadratic n (cutMatrix n D δ) w) =
      quadratic n D w / 4 := by
  classical
  have hterm : ∀ (i : Fin n) (j : Fin n),
      ((2 : ℝ) ^ n)⁻¹ *
          (∑ δ : Fin n → Bool, cutMatrix n D δ i j * w i * w j) =
        (D i j * w i * w j) / 4 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [cutMatrix, hdiag]
    · have hchi := cut_entry_mean n i j hij
      unfold cubeMean at hchi
      have hfactor : ∀ δ : Fin n → Bool,
          cutMatrix n D δ i j * w i * w j =
            (if δ i then (if δ j then (0 : ℝ) else 1) else 0) *
              (D i j * w i * w j) := by
        intro δ
        cases hi : δ i <;> cases hj : δ j <;> simp [cutMatrix, hi, hj]
      have hsumfactor :
          (∑ δ : Fin n → Bool, cutMatrix n D δ i j * w i * w j) =
            (∑ δ : Fin n → Bool,
              if δ i then (if δ j then (0 : ℝ) else 1) else 0) *
                (D i j * w i * w j) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun δ _ => hfactor δ)
      rw [hsumfactor]
      calc
        ((2 : ℝ) ^ n)⁻¹ *
            ((∑ δ : Fin n → Bool,
              if δ i then (if δ j then (0 : ℝ) else 1) else 0) *
                (D i j * w i * w j)) =
            (((2 : ℝ) ^ n)⁻¹ *
              ∑ δ : Fin n → Bool,
                if δ i then (if δ j then (0 : ℝ) else 1) else 0) *
                  (D i j * w i * w j) := by ring
        _ = (D i j * w i * w j) / 4 := by rw [hchi]; ring
  unfold cubeMean quadratic
  calc
    ((2 : ℝ) ^ n)⁻¹ *
        (∑ δ : Fin n → Bool, ∑ i : Fin n, ∑ j : Fin n,
          cutMatrix n D δ i j * w i * w j) =
        ∑ i : Fin n, ∑ j : Fin n,
          ((2 : ℝ) ^ n)⁻¹ *
            (∑ δ : Fin n → Bool, cutMatrix n D δ i j * w i * w j) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_comm, Finset.mul_sum]
    _ = ∑ i : Fin n, ∑ j : Fin n, (D i j * w i * w j) / 4 := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact Finset.sum_congr rfl (fun j _ => hterm i j)
    _ = (∑ i : Fin n, ∑ j : Fin n, D i j * w i * w j) / 4 := by
      simp_rw [← Finset.sum_div]

private theorem cut_average_eq_decoupled
    (n : ℕ) (D : Fin n → Fin n → ℝ) (δ : Fin n → Bool) (phi : ℝ → ℝ) :
    cubeMean n (fun s : Fin n → Bool =>
      phi (quadratic n (cutMatrix n D δ) (signPath n s))) =
      cubeMean n (fun t : Fin n → Bool =>
        cubeMean n (fun s : Fin n → Bool =>
          phi (bilinear n (cutMatrix n D δ) s t))) := by
  classical
  let swapPair :
      ((Fin n → Bool) × (Fin n → Bool)) →
        ((Fin n → Bool) × (Fin n → Bool)) :=
    fun p : (Fin n → Bool) × (Fin n → Bool) =>
      ((fun i : Fin n => if δ i then p.1 i else p.2 i),
       (fun i : Fin n => if δ i then p.2 i else p.1 i))
  have hinv : ∀ p : (Fin n → Bool) × (Fin n → Bool), swapPair (swapPair p) = p := by
    rintro ⟨s, t⟩
    apply Prod.ext
    · funext i
      cases hδ : δ i <;> simp [swapPair, hδ]
    · funext i
      cases hδ : δ i <;> simp [swapPair, hδ]
  have hbij : Function.Bijective swapPair := by
    constructor
    · intro p r hpr
      calc
        p = swapPair (swapPair p) := (hinv p).symm
        _ = swapPair (swapPair r) := congrArg swapPair hpr
        _ = r := hinv r
    · intro p
      exact ⟨swapPair p, hinv p⟩
  have hpoint : ∀ p : (Fin n → Bool) × (Fin n → Bool),
      bilinear n (cutMatrix n D δ) p.1 p.2 =
        quadratic n (cutMatrix n D δ) (signPath n (swapPair p).1) := by
    rintro ⟨s, t⟩
    unfold bilinear quadratic
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    cases hi : δ i <;> cases hj : δ j <;>
      simp [cutMatrix, signPath, swapPair, hi, hj]
  have hsum :
      (∑ t : Fin n → Bool, ∑ s : Fin n → Bool,
        phi (bilinear n (cutMatrix n D δ) s t)) =
        (Fintype.card (Fin n → Bool) : ℝ) *
          ∑ s : Fin n → Bool, phi (quadratic n (cutMatrix n D δ) (signPath n s)) := by
    calc
      (∑ t : Fin n → Bool, ∑ s : Fin n → Bool,
          phi (bilinear n (cutMatrix n D δ) s t)) =
          ∑ p : (Fin n → Bool) × (Fin n → Bool),
            phi (bilinear n (cutMatrix n D δ) p.1 p.2) := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
      _ = ∑ p : (Fin n → Bool) × (Fin n → Bool),
          phi (quadratic n (cutMatrix n D δ) (signPath n (swapPair p).1)) :=
        Finset.sum_congr rfl (fun p _ => congrArg phi (hpoint p))
      _ = ∑ p : (Fin n → Bool) × (Fin n → Bool),
          phi (quadratic n (cutMatrix n D δ) (signPath n p.1)) :=
        hbij.sum_comp
          (fun p : (Fin n → Bool) × (Fin n → Bool) =>
            phi (quadratic n (cutMatrix n D δ) (signPath n p.1)))
      _ = (Fintype.card (Fin n → Bool) : ℝ) *
          ∑ s : Fin n → Bool, phi (quadratic n (cutMatrix n D δ) (signPath n s)) := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← Finset.mul_sum]
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) = (2 : ℝ) ^ n := by
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow,
      Nat.cast_ofNat]
  unfold cubeMean
  rw [← Finset.mul_sum, hsum, hcard]
  field_simp [pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)] <;> ring

private theorem scalar_sign_moment_bound
    (n : ℕ) (a : Fin n → ℝ) (q : ℝ) (hq : 2 ≤ q) :
    Real.rpow
      (cubeMean n (fun s : Fin n → Bool =>
        Real.rpow |∑ i : Fin n, signValue (s i) * a i| q))
      (1 / q) ≤
      (2 : ℝ) * Real.sqrt q * Real.sqrt (∑ i : Fin n, a i ^ 2) := by
  classical
  let u : Fin n → EuclideanSpace ℝ (Fin 1) :=
    fun i : Fin n =>
      WithLp.toLp (2 : ℝ≥0∞) (V := Fin 1 → ℝ)
        (fun _r : Fin 1 => a i)
  have husq : ∀ i : Fin n, ‖u i‖ ^ 2 = a i ^ 2 := by
    intro i
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [u, PiLp.toLp_apply, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_one, one_mul]
  have hcoord : ∀ (s : Fin n → Bool) (r : Fin 1),
      (signSum n 1 u s) r = ∑ i : Fin n, signValue (s i) * a i := by
    intro s r
    change (WithLp.ofLp (∑ i : Fin n, signValue (s i) • u i)) r =
      ∑ i : Fin n, signValue (s i) * a i
    rw [WithLp.ofLp_sum]
    simp only [Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply,
      u, WithLp.ofLp_toLp, smul_eq_mul]
  have hnorm : ∀ s : Fin n → Bool,
      ‖signSum n 1 u s‖ = |∑ i : Fin n, signValue (s i) * a i| := by
    intro s
    have hsq : ‖signSum n 1 u s‖ ^ 2 =
        (∑ i : Fin n, signValue (s i) * a i) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [hcoord, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_one, one_mul]
    apply le_antisymm
    · apply (sq_le_sq₀ (norm_nonneg (signSum n 1 u s))
        (abs_nonneg (∑ i : Fin n, signValue (s i) * a i))).mp
      rw [hsq, sq_abs]
    · apply (sq_le_sq₀ (abs_nonneg (∑ i : Fin n, signValue (s i) * a i))
        (norm_nonneg (signSum n 1 u s))).mp
      rw [hsq, sq_abs]
  have henergy : Shao.OQ6.FiniteHilbertSignMoments.energy n 1 u = ∑ i : Fin n, a i ^ 2 := by
    unfold Shao.OQ6.FiniteHilbertSignMoments.energy
    exact Finset.sum_congr rfl (fun i _ => husq i)
  simpa only [moment, hnorm, hilbertConstant, henergy] using
    finite_hilbert_sign_moment_bound n 1 u q hq

private theorem decoupled_power_moment_bound
    (n : ℕ) (D : Fin n → Fin n → ℝ) (q : ℝ) (hq : 2 ≤ q) :
    cubeMean n (fun t : Fin n → Bool =>
      cubeMean n (fun s : Fin n → Bool => Real.rpow |bilinear n D s t| q)) ≤
      Real.rpow ((4 : ℝ) * q * Real.sqrt (entryEnergy n D)) q := by
  classical
  let v : Fin n → EuclideanSpace ℝ (Fin n) :=
    fun j : Fin n =>
      WithLp.toLp (2 : ℝ≥0∞) (V := Fin n → ℝ)
        (fun i : Fin n => D i j)
  let a : (Fin n → Bool) → Fin n → ℝ :=
    fun (t : Fin n → Bool) (i : Fin n) =>
      ∑ j : Fin n, signValue (t j) * D i j
  let Y : (Fin n → Bool) → EuclideanSpace ℝ (Fin n) :=
    fun t : Fin n → Bool => signSum n n v t
  let K : ℝ := (2 : ℝ) * Real.sqrt q
  have hq0 : 0 < q := by linarith
  have hK : 0 ≤ K := mul_nonneg (by norm_num) (Real.sqrt_nonneg q)
  have hYcoord : ∀ (t : Fin n → Bool) (i : Fin n), Y t i = a t i := by
    intro t i
    change (WithLp.ofLp (∑ j : Fin n, signValue (t j) • v j)) i =
      ∑ j : Fin n, signValue (t j) * D i j
    rw [WithLp.ofLp_sum]
    simp only [Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply,
      v, WithLp.ofLp_toLp, smul_eq_mul]
  have hYsq : ∀ t : Fin n → Bool, ‖Y t‖ ^ 2 = ∑ i : Fin n, a t i ^ 2 := by
    intro t
    simpa only [hYcoord] using EuclideanSpace.real_norm_sq_eq (Y t)
  have hsqrt : ∀ t : Fin n → Bool,
      Real.sqrt (∑ i : Fin n, a t i ^ 2) = ‖Y t‖ := by
    intro t
    rw [← hYsq t, Real.sqrt_sq (norm_nonneg (Y t))]
  have henergy : Shao.OQ6.FiniteHilbertSignMoments.energy n n v = entryEnergy n D := by
    unfold Shao.OQ6.FiniteHilbertSignMoments.energy entryEnergy
    apply Finset.sum_congr rfl
    intro j _hj
    simpa only [v, PiLp.toLp_apply] using EuclideanSpace.real_norm_sq_eq (v j)
  have hbilinear : ∀ (s : Fin n → Bool) (t : Fin n → Bool),
      bilinear n D s t = ∑ i : Fin n, signValue (s i) * a t i := by
    intro s t
    unfold bilinear
    apply Finset.sum_congr rfl
    intro i _hi
    dsimp only [a]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hinner : ∀ t : Fin n → Bool,
      cubeMean n (fun s : Fin n → Bool => Real.rpow |bilinear n D s t| q) ≤
        Real.rpow K q * Real.rpow ‖Y t‖ q := by
    intro t
    have hroot :
        Real.rpow
          (cubeMean n (fun s : Fin n → Bool => Real.rpow |bilinear n D s t| q))
          (1 / q) ≤ K * ‖Y t‖ := by
      simpa only [hbilinear, K, hsqrt t] using
        scalar_sign_moment_bound n (a t) q hq
    have hnonneg :
        0 ≤ cubeMean n (fun s : Fin n → Bool => Real.rpow |bilinear n D s t| q) := by
      unfold cubeMean
      exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) n))
        (Finset.sum_nonneg (fun s _ => Real.rpow_nonneg (abs_nonneg _) q))
    have hpow :
        cubeMean n (fun s : Fin n → Bool => Real.rpow |bilinear n D s t| q) ≤
          Real.rpow (K * ‖Y t‖) q :=
      (Real.rpow_inv_le_iff_of_pos hnonneg
        (mul_nonneg hK (norm_nonneg (Y t))) hq0).mp
          (by simpa only [one_div, Real.rpow_eq_pow] using hroot)
    simpa only [Real.rpow_eq_pow, Real.mul_rpow hK (norm_nonneg (Y t))] using hpow
  have hvecnonneg :
      0 ≤ cubeMean n (fun t : Fin n → Bool => Real.rpow ‖Y t‖ q) := by
    unfold cubeMean
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) n))
      (Finset.sum_nonneg (fun t _ => Real.rpow_nonneg (norm_nonneg _) q))
  have hvecroot :
      Real.rpow (cubeMean n (fun t : Fin n → Bool => Real.rpow ‖Y t‖ q)) (1 / q) ≤
        K * Real.sqrt (entryEnergy n D) := by
    simpa only [moment, Y, K, hilbertConstant, henergy] using
      finite_hilbert_sign_moment_bound n n v q hq
  have hvecpow :
      cubeMean n (fun t : Fin n → Bool => Real.rpow ‖Y t‖ q) ≤
        Real.rpow (K * Real.sqrt (entryEnergy n D)) q :=
    (Real.rpow_inv_le_iff_of_pos hvecnonneg
      (mul_nonneg hK (Real.sqrt_nonneg _)) hq0).mp
        (by simpa only [one_div, Real.rpow_eq_pow] using hvecroot)
  have hmean :
      cubeMean n (fun t : Fin n → Bool =>
        cubeMean n (fun s : Fin n → Bool => Real.rpow |bilinear n D s t| q)) ≤
        Real.rpow K q * cubeMean n (fun t : Fin n → Bool => Real.rpow ‖Y t‖ q) := by
    calc
      cubeMean n (fun t : Fin n → Bool =>
          cubeMean n (fun s : Fin n → Bool => Real.rpow |bilinear n D s t| q)) ≤
          cubeMean n (fun t : Fin n → Bool => Real.rpow K q * Real.rpow ‖Y t‖ q) := by
        unfold cubeMean
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun t _ => hinner t))
          (inv_nonneg.mpr (pow_nonneg (by norm_num) n))
      _ = Real.rpow K q *
          cubeMean n (fun t : Fin n → Bool => Real.rpow ‖Y t‖ q) := by
        unfold cubeMean
        rw [← Finset.mul_sum]
        ring
  calc
    cubeMean n (fun t : Fin n → Bool =>
        cubeMean n (fun s : Fin n → Bool => Real.rpow |bilinear n D s t| q)) ≤
        Real.rpow K q * cubeMean n (fun t : Fin n → Bool => Real.rpow ‖Y t‖ q) := hmean
    _ ≤ Real.rpow K q * Real.rpow (K * Real.sqrt (entryEnergy n D)) q :=
      mul_le_mul_of_nonneg_left hvecpow (Real.rpow_nonneg hK q)
    _ = Real.rpow ((4 : ℝ) * q * Real.sqrt (entryEnergy n D)) q := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.mul_rpow hK (mul_nonneg hK (Real.sqrt_nonneg _))]
      congr 1
      have hKsq : K * K = (4 : ℝ) * q := by
        dsimp only [K]
        nlinarith [Real.sq_sqrt hq0.le]
      calc
        K * (K * Real.sqrt (entryEnergy n D)) =
            (K * K) * Real.sqrt (entryEnergy n D) := by ring
        _ = (4 : ℝ) * q * Real.sqrt (entryEnergy n D) := by rw [hKsq]

theorem finite_quadratic_sign_moment_bound
    (n : ℕ) (D : Fin n → Fin n → ℝ) (q : ℝ)
    (hdiag : ∀ i : Fin n, D i i = 0) (hq : 2 ≤ q) :
    Real.rpow
      (cubeMean n (fun s : Fin n → Bool =>
        Real.rpow |quadratic n D (signPath n s)| q))
      (1 / q) ≤
      (16 : ℝ) * q * Real.sqrt (entryEnergy n D) := by
  classical
  let C : (Fin n → Bool) → (Fin n → Bool) → ℝ :=
    fun (δ : Fin n → Bool) (s : Fin n → Bool) =>
      quadratic n (cutMatrix n D δ) (signPath n s)
  let R : ℝ := (4 : ℝ) * q * Real.sqrt (entryEnergy n D)
  have hq0 : 0 < q := by linarith
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg (by norm_num) hq0.le) (Real.sqrt_nonneg _)
  have henergycut : ∀ δ : Fin n → Bool,
      entryEnergy n (cutMatrix n D δ) ≤ entryEnergy n D := by
    intro δ
    unfold entryEnergy
    apply Finset.sum_le_sum
    intro j _hj
    apply Finset.sum_le_sum
    intro i _hi
    cases hi : δ i <;> cases hj : δ j <;>
      simp [cutMatrix, hi, hj, sq_nonneg]
  have hcut : ∀ δ : Fin n → Bool,
      cubeMean n (fun s : Fin n → Bool => Real.rpow |C δ s| q) ≤ Real.rpow R q := by
    intro δ
    have hreindex := cut_average_eq_decoupled n D δ
      (fun x : ℝ => Real.rpow |x| q)
    have hmoment :
        cubeMean n (fun s : Fin n → Bool => Real.rpow |C δ s| q) =
          cubeMean n (fun t : Fin n → Bool =>
            cubeMean n (fun s : Fin n → Bool =>
              Real.rpow |bilinear n (cutMatrix n D δ) s t| q)) := by
      simpa only [C] using hreindex
    have hcomp : (4 : ℝ) * q * Real.sqrt (entryEnergy n (cutMatrix n D δ)) ≤ R :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (henergycut δ))
        (mul_nonneg (by norm_num) hq0.le)
    rw [hmoment]
    exact (decoupled_power_moment_bound n (cutMatrix n D δ) q hq).trans
      (Real.rpow_le_rpow
        (mul_nonneg (mul_nonneg (by norm_num) hq0.le) (Real.sqrt_nonneg _))
        hcomp hq0.le)
  have hpoint : ∀ s : Fin n → Bool,
      Real.rpow |quadratic n D (signPath n s)| q ≤
        Real.rpow (4 : ℝ) q *
          cubeMean n (fun δ : Fin n → Bool => Real.rpow |C δ s| q) := by
    intro s
    have hp :
        cubeMean n (fun δ : Fin n → Bool => C δ s) =
          quadratic n D (signPath n s) / 4 := by
      simpa only [C] using partition_mean n D (signPath n s) hdiag
    have hscale :
        |quadratic n D (signPath n s)| =
          (4 : ℝ) * |cubeMean n (fun δ : Fin n → Bool => C δ s)| := by
      rw [hp, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      ring
    calc
      Real.rpow |quadratic n D (signPath n s)| q =
          Real.rpow ((4 : ℝ) * |cubeMean n (fun δ : Fin n → Bool => C δ s)|) q := by
        rw [hscale]
      _ = Real.rpow (4 : ℝ) q *
          Real.rpow |cubeMean n (fun δ : Fin n → Bool => C δ s)| q := by
        exact Real.mul_rpow (by norm_num) (abs_nonneg _)
      _ ≤ Real.rpow (4 : ℝ) q *
          cubeMean n (fun δ : Fin n → Bool => Real.rpow |C δ s| q) :=
        mul_le_mul_of_nonneg_left
          (cubeMean_abs_rpow_jensen n (fun δ : Fin n → Bool => C δ s) q (by linarith))
          (Real.rpow_nonneg (by norm_num) q)
  have hcard : ((2 : ℝ) ^ n)⁻¹ * (Fintype.card (Fin n → Bool) : ℝ) = 1 := by
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow,
      Nat.cast_ofNat]
    exact inv_mul_cancel₀ (by positivity)
  have hconst : cubeMean n (fun _δ : Fin n → Bool => Real.rpow R q) = Real.rpow R q := by
    unfold cubeMean
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc
      ((2 : ℝ) ^ n)⁻¹ * ((Fintype.card (Fin n → Bool) : ℝ) * Real.rpow R q) =
          (((2 : ℝ) ^ n)⁻¹ * (Fintype.card (Fin n → Bool) : ℝ)) * Real.rpow R q := by ring
      _ = Real.rpow R q := by rw [hcard, one_mul]
  have havg :
      cubeMean n (fun δ : Fin n → Bool =>
        cubeMean n (fun s : Fin n → Bool => Real.rpow |C δ s| q)) ≤ Real.rpow R q := by
    calc
      cubeMean n (fun δ : Fin n → Bool =>
          cubeMean n (fun s : Fin n → Bool => Real.rpow |C δ s| q)) ≤
          cubeMean n (fun _δ : Fin n → Bool => Real.rpow R q) := by
        unfold cubeMean
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun δ _ => hcut δ))
          (inv_nonneg.mpr (pow_nonneg (by norm_num) n))
      _ = Real.rpow R q := hconst
  have hpower :
      cubeMean n (fun s : Fin n → Bool =>
        Real.rpow |quadratic n D (signPath n s)| q) ≤
          Real.rpow ((16 : ℝ) * q * Real.sqrt (entryEnergy n D)) q := by
    calc
      cubeMean n (fun s : Fin n → Bool =>
          Real.rpow |quadratic n D (signPath n s)| q) ≤
          cubeMean n (fun s : Fin n → Bool =>
            Real.rpow (4 : ℝ) q *
              cubeMean n (fun δ : Fin n → Bool => Real.rpow |C δ s| q)) := by
        unfold cubeMean
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun s _ => hpoint s))
          (inv_nonneg.mpr (pow_nonneg (by norm_num) n))
      _ = Real.rpow (4 : ℝ) q *
          cubeMean n (fun δ : Fin n → Bool =>
            cubeMean n (fun s : Fin n → Bool => Real.rpow |C δ s| q)) := by
        unfold cubeMean
        simp only [← Finset.mul_sum]
        rw [Finset.sum_comm]
        ring
      _ ≤ Real.rpow (4 : ℝ) q * Real.rpow R q :=
        mul_le_mul_of_nonneg_left havg (Real.rpow_nonneg (by norm_num) q)
      _ = Real.rpow ((16 : ℝ) * q * Real.sqrt (entryEnergy n D)) q := by
        simp only [Real.rpow_eq_pow]
        rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hR]
        congr 1
        dsimp only [R]
        ring
  have hnonneg :
      0 ≤ cubeMean n (fun s : Fin n → Bool =>
        Real.rpow |quadratic n D (signPath n s)| q) := by
    unfold cubeMean
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) n))
      (Finset.sum_nonneg (fun s _ => Real.rpow_nonneg (abs_nonneg _) q))
  simpa only [one_div, Real.rpow_eq_pow] using
    (Real.rpow_inv_le_iff_of_pos hnonneg
      (mul_nonneg (mul_nonneg (by norm_num) hq0.le) (Real.sqrt_nonneg _)) hq0).mpr hpower

theorem finite_half_quadratic_sign_moment_bound
    (n : ℕ) (D : Fin n → Fin n → ℝ) (q : ℝ)
    (hdiag : ∀ i : Fin n, D i i = 0) (hq : 2 ≤ q) :
    Real.rpow
      (cubeMean n (fun s : Fin n → Bool =>
        Real.rpow |quadratic n D (signPath n s) / 2| q))
      (1 / q) ≤
      (8 : ℝ) * q * Real.sqrt (entryEnergy n D) := by
  classical
  have hq0 : 0 < q := by linarith
  have hQnonneg :
      0 ≤ cubeMean n (fun s : Fin n → Bool =>
        Real.rpow |quadratic n D (signPath n s)| q) := by
    unfold cubeMean
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) n))
      (Finset.sum_nonneg (fun s _ => Real.rpow_nonneg (abs_nonneg _) q))
  have hQpower :
      cubeMean n (fun s : Fin n → Bool =>
        Real.rpow |quadratic n D (signPath n s)| q) ≤
          Real.rpow ((16 : ℝ) * q * Real.sqrt (entryEnergy n D)) q :=
    (Real.rpow_inv_le_iff_of_pos hQnonneg
      (mul_nonneg (mul_nonneg (by norm_num) hq0.le) (Real.sqrt_nonneg _)) hq0).mp
        (by simpa only [one_div, Real.rpow_eq_pow] using
          finite_quadratic_sign_moment_bound n D q hdiag hq)
  have hscaled : ∀ s : Fin n → Bool,
      Real.rpow |quadratic n D (signPath n s) / 2| q =
        Real.rpow ((1 : ℝ) / 2) q *
          Real.rpow |quadratic n D (signPath n s)| q := by
    intro s
    have hscale : |quadratic n D (signPath n s) / 2| =
        ((1 : ℝ) / 2) * |quadratic n D (signPath n s)| := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring
    rw [hscale]
    exact Real.mul_rpow (by norm_num) (abs_nonneg _)
  have hpower :
      cubeMean n (fun s : Fin n → Bool =>
        Real.rpow |quadratic n D (signPath n s) / 2| q) ≤
          Real.rpow ((8 : ℝ) * q * Real.sqrt (entryEnergy n D)) q := by
    calc
      cubeMean n (fun s : Fin n → Bool =>
          Real.rpow |quadratic n D (signPath n s) / 2| q) =
          cubeMean n (fun s : Fin n → Bool =>
            Real.rpow ((1 : ℝ) / 2) q *
              Real.rpow |quadratic n D (signPath n s)| q) := by
        simp only [hscaled]
      _ = Real.rpow ((1 : ℝ) / 2) q *
          cubeMean n (fun s : Fin n → Bool =>
            Real.rpow |quadratic n D (signPath n s)| q) := by
        unfold cubeMean
        rw [← Finset.mul_sum]
        ring
      _ ≤ Real.rpow ((1 : ℝ) / 2) q *
          Real.rpow ((16 : ℝ) * q * Real.sqrt (entryEnergy n D)) q :=
        mul_le_mul_of_nonneg_left hQpower (Real.rpow_nonneg (by norm_num) q)
      _ = Real.rpow ((8 : ℝ) * q * Real.sqrt (entryEnergy n D)) q := by
        simp only [Real.rpow_eq_pow]
        rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (mul_nonneg (mul_nonneg (by norm_num) hq0.le) (Real.sqrt_nonneg _))]
        congr 1
        ring
  have hnonneg :
      0 ≤ cubeMean n (fun s : Fin n → Bool =>
        Real.rpow |quadratic n D (signPath n s) / 2| q) := by
    unfold cubeMean
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) n))
      (Finset.sum_nonneg (fun s _ => Real.rpow_nonneg (abs_nonneg _) q))
  simpa only [one_div, Real.rpow_eq_pow] using
    (Real.rpow_inv_le_iff_of_pos hnonneg
      (mul_nonneg (mul_nonneg (by norm_num) hq0.le) (Real.sqrt_nonneg _)) hq0).mpr hpower

theorem quadratic_eq_two_upper
    (n : ℕ) (D : Fin n → Fin n → ℝ) (w : Shao.Path n)
    (hdiag : ∀ i : Fin n, D i i = 0)
    (hsym : ∀ (i : Fin n) (j : Fin n), D i j = D j i) :
    quadratic n D w =
      (2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n,
        if i < j then D i j * w i * w j else 0 := by
  classical
  have hsplit : ∀ (i : Fin n) (j : Fin n),
      D i j * w i * w j =
        (if i < j then D i j * w i * w j else 0) +
          (if j < i then D i j * w i * w j else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | hij | hji
    · simp [hij, not_lt_of_ge (le_of_lt hij)]
    · subst j
      simp [hdiag]
    · simp [hji, not_lt_of_ge (le_of_lt hji)]
  have hswap :
      (∑ i : Fin n, ∑ j : Fin n, if j < i then D i j * w i * w j else 0) =
        ∑ i : Fin n, ∑ j : Fin n, if i < j then D i j * w i * w j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    by_cases hij : i < j
    · simp only [if_pos hij]
      rw [hsym j i]
      ring
    · simp only [if_neg hij]
  unfold quadratic
  calc
    (∑ i : Fin n, ∑ j : Fin n, D i j * w i * w j) =
        ∑ i : Fin n, ∑ j : Fin n,
          ((if i < j then D i j * w i * w j else 0) +
            (if j < i then D i j * w i * w j else 0)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact Finset.sum_congr rfl (fun j _ => hsplit i j)
    _ = (∑ i : Fin n, ∑ j : Fin n, if i < j then D i j * w i * w j else 0) +
        (∑ i : Fin n, ∑ j : Fin n, if j < i then D i j * w i * w j else 0) := by
      simp_rw [Finset.sum_add_distrib]
    _ = (2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n,
        if i < j then D i j * w i * w j else 0 := by
      rw [hswap]
      ring

end

end Shao.OQ6.FiniteQuadraticSignChaos
