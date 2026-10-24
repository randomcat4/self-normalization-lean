/- Mathematical candidate only; no production proof bodies or Lean/AX execution.
   Same actual bridge law and actual strict probability kernels as the shared request. -/
import Shao.C2.BridgeIntervalImageResolved
import Shao.C2.BridgeUpperAffineIdentification
import Shao.C2.IntervalImageIntSeries
import Shao.C2.BrownianBridgeLaw

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
noncomputable section
namespace Shao.Probability.SourceActualRegularPhysicalRatio
open MeasureTheory ProbabilityTheory
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw

private theorem arp_far_image_sum_bound
    (A U V : ℝ) (hA : 16 ≤ A) (hU0 : 0 ≤ U) (hU1 : U ≤ 1)
    (hV0 : 0 ≤ V) (hUV : U + V ≤ 13 * A / 8) :
    let E : ℤ → ℝ → ℝ := fun m t =>
      8 * (m : ℝ) ^ 2 * A ^ 2 + 4 * (m : ℝ) * A * (U - t)
    let F : ℤ → ℝ → ℝ := fun j t =>
      8 * (j : ℝ) ^ 2 * A ^ 2 - 4 * (j : ℝ) * A * (U + t) + 2 * U * t
    let G : ℤ → ℝ → ℝ := fun m t =>
      4 * (m : ℝ) * A * Real.exp (-E m t) -
        (4 * (m : ℝ) * A + 2 * t) * Real.exp (-F (-m) t)
    Summable (fun m : ℤ => if m = 0 then 0 else G m V) ∧
      |tsum (fun m : ℤ => if m = 0 then 0 else G m V)| ≤
        1856 * V * Real.exp (-(11 * A ^ 2 / 8)) := by
  classical
  intro E F G
  have hA0 : 0 < A := by linarith only [hA]
  have hA2 : 16 ≤ A ^ 2 := by nlinarith only [hA, sq_nonneg (A - 1)]
  have hVbound : V ≤ 13 * A / 8 := by linarith only [hUV, hU0]
  let L : ℝ := 928 * V * Real.exp (-(11 * A ^ 2 / 8))
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  let q : ℝ := Real.exp (-1)
  have hq0 : 0 < q := Real.exp_pos _
  have hqhalf : q ≤ 1 / 2 := by
    have he : 2 ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    have heq : q * Real.exp 1 = 1 := by
      dsimp only [q]
      rw [← Real.exp_add]
      norm_num
    have hm := mul_le_mul_of_nonneg_left he hq0.le
    linarith only [hm, heq]
  have hq1 : q < 1 := by linarith only [hqhalf]
  have hqnorm : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos hq0] using hq1
  have hg : HasSum (fun n : ℕ => q ^ (n + 1)) ((1 - q)⁻¹ * q) := by
    simpa only [pow_succ] using (hasSum_geometric_of_norm_lt_one hqnorm).mul_right q
  have hgsum : tsum (fun n : ℕ => q ^ (n + 1)) ≤ 1 := calc
    _ = (1 - q)⁻¹ * q := hg.tsum_eq
    _ = q / (1 - q) := by ring
    _ ≤ 1 := (div_le_iff₀ (sub_pos.mpr hq1)).mpr (by linarith only [hqhalf])
  have hpow (n : ℕ) : Real.exp (-((n : ℝ) + 1)) = q ^ (n + 1) := by
    dsimp only [q]
    rw [← Real.exp_nat_mul]
    push_cast
    congr 1
    ring
  have hterm (m : ℤ) (hm : m ≠ 0) :
      |G m V| ≤ L * Real.exp (-|(m : ℝ)|) := by
    let k : ℝ := |(m : ℝ)|
    let S : ℝ := k ^ 2 * A ^ 2
    have hk : 1 ≤ k := Shao.C2.IntervalImageExponents.int_abs_ge_one m hm
    have hk0 : 0 ≤ k := abs_nonneg _
    have hkA : A ≤ k * A := by nlinarith only [hk, hA0]
    have hS : 1 ≤ S := by
      dsimp only [S]
      nlinarith only [hkA, hA, sq_nonneg (k * A - 1)]
    have hS0 : 0 ≤ S := le_trans (by norm_num) hS
    have hS_eq : S = (m : ℝ) ^ 2 * A ^ 2 := by dsimp only [S, k]; rw [sq_abs]
    have hexps (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) V) :
        3 * S / 2 ≤ E m t ∧ 3 * S / 2 ≤ F (-m) t := by
      have hUt : U + t ≤ 13 * A / 8 := by linarith only [hUV, ht.2]
      have hUt0 : 0 ≤ U + t := add_nonneg hU0 ht.1
      have habsdiff : |U - t| ≤ U + t := abs_le.mpr ⟨by linarith only [hU0], by linarith only [ht.1]⟩
      have hcrossabs : |4 * (m : ℝ) * A * (U - t)| ≤ 4 * k * A * (U + t) := by
        calc
          _ = 4 * k * A * |U - t| := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos hA0]
          _ ≤ _ := mul_le_mul_of_nonneg_left habsdiff (by positivity)
      have hcross := (abs_le.mp hcrossabs).1
      have hsumabs : |4 * (m : ℝ) * A * (U + t)| = 4 * k * A * (U + t) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
          abs_of_pos hA0, abs_of_nonneg hUt0]
      have hsum := neg_abs_le (4 * (m : ℝ) * A * (U + t))
      rw [hsumabs] at hsum
      have hc : 4 * k * A * (U + t) ≤ (13 / 2) * k * A ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_left hUt (show 0 ≤ 4 * k * A by positivity)
        nlinarith only [hmul]
      have hgap : 3 * S / 2 ≤ 8 * S - (13 / 2) * k * A ^ 2 := by
        have hp := mul_nonneg (mul_nonneg hk0 (sub_nonneg.mpr hk)) (sq_nonneg A)
        dsimp only [S]
        nlinarith only [hp]
      have hElo : 8 * S - 4 * k * A * (U + t) ≤ E m t := by
        dsimp only [E]
        rw [hS_eq]
        nlinarith only [hcross]
      have hFlo : 8 * S - 4 * k * A * (U + t) ≤ F (-m) t := by
        dsimp only [F]
        simp only [Int.cast_neg, neg_sq]
        rw [hS_eq]
        nlinarith only [hsum, mul_nonneg hU0 ht.1]
      constructor <;> linarith only [hgap, hc, hElo, hFlo]
    let DG : ℝ → ℝ := fun t =>
      16 * (m : ℝ) ^ 2 * A ^ 2 * Real.exp (-E m t) +
        (-2 + (4 * (m : ℝ) * A + 2 * t) * (4 * (m : ℝ) * A + 2 * U)) *
          Real.exp (-F (-m) t)
    have hderiv (t : ℝ) : HasDerivAt (G m) (DG t) t := by
      have he : HasDerivAt (fun r : ℝ => -E m r) (4 * (m : ℝ) * A) t := by
        convert ((hasDerivAt_id t).const_mul (4 * (m : ℝ) * A)).add_const
          (-8 * (m : ℝ) ^ 2 * A ^ 2 - 4 * (m : ℝ) * A * U) using 1 <;>
          (try funext r) <;> (try simp only [E, id_eq]) <;> ring
      have hf : HasDerivAt (fun r : ℝ => -F (-m) r)
          (-4 * (m : ℝ) * A - 2 * U) t := by
        convert ((hasDerivAt_id t).const_mul (-4 * (m : ℝ) * A - 2 * U)).add_const
          (-8 * (m : ℝ) ^ 2 * A ^ 2 - 4 * (m : ℝ) * A * U) using 1 <;>
          (try funext r) <;> (try simp only [F, id_eq, Int.cast_neg]) <;> ring
      have hl : HasDerivAt (fun r : ℝ => 4 * (m : ℝ) * A + 2 * r) 2 t := by
        convert ((hasDerivAt_id t).const_mul (2 : ℝ)).const_add (4 * (m : ℝ) * A) using 1 <;> (try funext r) <;> (try simp only [id_eq]) <;> ring
      convert (he.exp.const_mul (4 * (m : ℝ) * A)).sub (hl.mul hf.exp) using 1 <;>
        dsimp only [G, DG] <;> ring
    have hderivbound (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) V) :
        |DG t| ≤ 58 * S * Real.exp (-(3 * S / 2)) := by
      obtain ⟨he, hf⟩ := hexps t ht
      have htbound : t ≤ 13 * A / 8 := ht.2.trans hVbound
      have hc1 : |4 * (m : ℝ) * A + 2 * t| ≤ 8 * k * A := by
        have hbase : |4 * (m : ℝ) * A + 2 * t| ≤ 4 * k * A + 2 * t := by
          calc
            _ ≤ |4 * (m : ℝ) * A| + |2 * t| := abs_add_le _ _
            _ = _ := by
              rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
                abs_of_pos hA0, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg ht.1]
        nlinarith only [hbase, htbound, hkA, hA0]
      have hc2 : |4 * (m : ℝ) * A + 2 * U| ≤ 5 * k * A := by
        have hbase : |4 * (m : ℝ) * A + 2 * U| ≤ 4 * k * A + 2 * U := by
          calc
            _ ≤ |4 * (m : ℝ) * A| + |2 * U| := abs_add_le _ _
            _ = _ := by
              rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
                abs_of_pos hA0, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hU0]
        linarith only [hbase, hU1, hkA, hA]
      have hprod : |(4 * (m : ℝ) * A + 2 * t) * (4 * (m : ℝ) * A + 2 * U)| ≤ 40 * S := by
        rw [abs_mul]
        have h := mul_le_mul hc1 hc2 (abs_nonneg _) (show 0 ≤ 8 * k * A by positivity)
        dsimp only [S]
        nlinarith only [h]
      have hcoef : |-2 + (4 * (m : ℝ) * A + 2 * t) * (4 * (m : ℝ) * A + 2 * U)| ≤ 42 * S := by
        have hh := abs_add_le (-2 : ℝ) ((4 * (m : ℝ) * A + 2 * t) * (4 * (m : ℝ) * A + 2 * U))
        rw [show |(-2 : ℝ)| = 2 by norm_num] at hh
        linarith only [hh, hprod, hS]
      have he' : Real.exp (-E m t) ≤ Real.exp (-(3 * S / 2)) :=
        Real.exp_le_exp.mpr (by linarith only [he])
      have hf' : Real.exp (-F (-m) t) ≤ Real.exp (-(3 * S / 2)) :=
        Real.exp_le_exp.mpr (by linarith only [hf])
      calc
        |DG t| ≤ |16 * (m : ℝ) ^ 2 * A ^ 2 * Real.exp (-E m t)| +
            |(-2 + (4 * (m : ℝ) * A + 2 * t) * (4 * (m : ℝ) * A + 2 * U)) *
              Real.exp (-F (-m) t)| := abs_add_le _ _
        _ = 16 * S * Real.exp (-E m t) +
            |-2 + (4 * (m : ℝ) * A + 2 * t) * (4 * (m : ℝ) * A + 2 * U)| *
              Real.exp (-F (-m) t) := by
          rw [abs_of_nonneg (by positivity : 0 ≤ 16 * (m : ℝ) ^ 2 * A ^ 2 * Real.exp (-E m t)),
            abs_mul, abs_of_pos (Real.exp_pos _), hS_eq]
          ring
        _ ≤ 16 * S * Real.exp (-(3 * S / 2)) + 42 * S * Real.exp (-(3 * S / 2)) := by
          exact add_le_add (mul_le_mul_of_nonneg_left he' (by positivity))
            (mul_le_mul hcoef hf' (Real.exp_pos _).le (by positivity))
        _ = _ := by ring
    have hzero : G m 0 = 0 := by
      dsimp only [G, E, F]
      push_cast
      ring_nf
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := G m) (f' := DG) (a := (0 : ℝ)) (b := V)
      (fun t ht => (hderiv t).hasDerivWithinAt)
      (fun t ht => by simpa only [Real.norm_eq_abs] using hderivbound t ⟨ht.1, ht.2.le⟩)
      V ⟨hV0, le_rfl⟩
    have hstep : |G m V| ≤ 58 * V * S * Real.exp (-(3 * S / 2)) := by
      simpa only [Real.norm_eq_abs, hzero, sub_zero, mul_assoc, mul_left_comm, mul_comm] using hmvt
    have habsorb : S * Real.exp (-(3 * S / 2)) ≤ 16 * Real.exp (-(23 * S / 16)) := by
      have he : S ≤ 16 * Real.exp (S / 16) := by
        linarith only [Real.add_one_le_exp (S / 16)]
      calc
        _ ≤ (16 * Real.exp (S / 16)) * Real.exp (-(3 * S / 2)) :=
          mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
        _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 1; ring
    have hpoly : 0 ≤ 23 * k ^ 2 - 22 - k := by
      have hp := mul_nonneg (sub_nonneg.mpr hk) (show 0 ≤ 23 * k + 22 by positivity)
      nlinarith only [hp]
    have hpolyA := mul_nonneg hpoly (sq_nonneg A)
    have hAk := mul_le_mul_of_nonneg_left hA2 hk0
    have hexptail : Real.exp (-(23 * S / 16)) ≤
        Real.exp (-(11 * A ^ 2 / 8)) * Real.exp (-k) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      dsimp only [S]
      nlinarith only [hpolyA, hAk]
    calc
      |G m V| ≤ 58 * V * (S * Real.exp (-(3 * S / 2))) := by simpa only [mul_assoc] using hstep
      _ ≤ 58 * V * (16 * Real.exp (-(23 * S / 16))) :=
        mul_le_mul_of_nonneg_left habsorb (by positivity)
      _ ≤ 58 * V * (16 * (Real.exp (-(11 * A ^ 2 / 8)) * Real.exp (-k))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexptail (by norm_num)) (by positivity)
      _ = L * Real.exp (-|(m : ℝ)|) := by dsimp only [L, k]; ring
  let H : ℤ → ℝ := fun m => if m = 0 then 0 else G m V
  have hpos (n : ℕ) : |H ((n : ℤ) + 1)| ≤ L * q ^ (n + 1) := by
    have hm : (n : ℤ) + 1 ≠ 0 := by omega
    have h := hterm ((n : ℤ) + 1) hm
    simpa only [H, if_neg hm, Int.cast_add, Int.cast_natCast, Int.cast_one,
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1), hpow] using h
  have hneg (n : ℕ) : |H (-((n : ℤ) + 1))| ≤ L * q ^ (n + 1) := by
    have hm : -((n : ℤ) + 1) ≠ 0 := by omega
    have h := hterm (-((n : ℤ) + 1)) hm
    simpa only [H, if_neg hm, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      abs_neg, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1), hpow] using h
  have hmajor : Summable (fun n : ℕ => L * q ^ (n + 1)) := hg.summable.mul_left L
  have hsp : Summable (fun n : ℕ => H ((n : ℤ) + 1)) :=
    Summable.of_norm_bounded hmajor (by intro n; simpa only [Real.norm_eq_abs] using hpos n)
  have hsn : Summable (fun n : ℕ => H (-((n : ℤ) + 1))) :=
    Summable.of_norm_bounded hmajor (by intro n; simpa only [Real.norm_eq_abs] using hneg n)
  have hwhole : Summable H := Summable.of_add_one_of_neg_add_one hsp hsn
  have hbound (f : ℕ → ℝ) (hf : Summable f)
      (hb : ∀ n, |f n| ≤ L * q ^ (n + 1)) : |tsum f| ≤ L := calc
    _ ≤ tsum (fun n : ℕ => |f n|) := by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hf.norm
    _ ≤ tsum (fun n : ℕ => L * q ^ (n + 1)) :=
      Summable.tsum_le_tsum hb hf.abs hmajor
    _ = L * tsum (fun n : ℕ => q ^ (n + 1)) := tsum_mul_left
    _ ≤ L * 1 := mul_le_mul_of_nonneg_left hgsum hL
    _ = L := mul_one _
  refine ⟨hwhole, ?_⟩
  change |tsum H| ≤ _
  calc
    |tsum H| = |tsum (fun n : ℕ => H ((n : ℤ) + 1)) +
        tsum (fun n : ℕ => H (-((n : ℤ) + 1)))| := by
      rw [tsum_of_add_one_of_neg_add_one hsp hsn]
      simp only [H, if_pos rfl, add_zero]
    _ ≤ |tsum (fun n : ℕ => H ((n : ℤ) + 1))| +
        |tsum (fun n : ℕ => H (-((n : ℤ) + 1)))| := abs_add_le _ _
    _ ≤ L + L := add_le_add (hbound _ hsp hpos) (hbound _ hsn hneg)
    _ = 1856 * V * Real.exp (-(11 * A ^ 2 / 8)) := by dsimp only [L]; ring

theorem actual_bridge_first_upper_gradient_ratio :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        (B : NNReal → Ω → ℝ) (PB : Measure Ω) [IsProbabilityMeasure PB],
        IsBrownianReal B PB →
        let Q : Measure BridgeNoise := bridgeLaw B PB
        ∀ (x a y T z b : ℝ), 16 ≤ x → 0 < T →
          x * Real.sqrt T ≤ a →
          let u : ℝ := a - y
          0 < u → u ≤ |b| → b ^ 2 ≤ T / 2 →
          |z| < a → |z - y| ≤ 3 * x * Real.sqrt T / 2 →
          let dI : ℝ := deriv (fun w : ℝ => intervalCompletion Q a w T z) y
          let dU : ℝ := deriv (fun w : ℝ => upperCompletion Q a w T z) y
          0 ≤ dI - dU ∧
            dI - dU ≤ C * Real.exp (-(a ^ 2 / T)) * (-dU) := by
  classical
  refine ⟨2048, by norm_num, ?_⟩
  intro Ω hΩ B PB hPB hB Q x a y T z b hx hT ha u hu hub hb hz hdisp dI dU
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw B PB hB
  let s : ℝ := Real.sqrt T
  let A : ℝ := a / s
  let U : ℝ := u / s
  let V : ℝ := (a - z) / s
  have hs : 0 < s := Real.sqrt_pos.mpr hT
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hs2 : s ^ 2 = T := Real.sq_sqrt hT.le
  have hAx : x ≤ A := (le_div_iff₀ hs).mpr ha
  have hA : 16 ≤ A := hx.trans hAx
  have ha0 : 0 < a := lt_of_lt_of_le (mul_pos (by linarith only [hx]) hs) ha
  have hu2 : u ^ 2 ≤ T / 2 := calc
    u ^ 2 ≤ |b| ^ 2 := (sq_le_sq₀ hu.le (abs_nonneg b)).mpr hub
    _ = b ^ 2 := sq_abs b
    _ ≤ T / 2 := hb
  have hU0 : 0 ≤ U := div_nonneg hu.le hs.le
  have hU2 : U ^ 2 ≤ 1 / 2 := by
    dsimp only [U]
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
    nlinarith only [hu2, hs2]
  have hU1 : U ≤ 1 := by nlinarith only [hU2, sq_nonneg (U - 1)]
  have hu_s : u ≤ s := by simpa only [one_mul] using (div_le_iff₀ hs).mp hU1
  have hy : |y| < a := by
    apply abs_lt.mpr
    have ha16 : 16 * s ≤ a := (mul_le_mul_of_nonneg_right hx hs.le).trans ha
    constructor <;> dsimp only [u] at hu hu_s <;> linarith only [hu, hu_s, ha16, hs]
  have hV : 0 < V := div_pos (sub_pos.mpr (abs_lt.mp hz).2) hs
  have hVU : V - U = (y - z) / s := by dsimp only [V, U, u]; ring
  have hVdisp : V - U ≤ 3 * x / 2 := by
    rw [hVU]
    apply (div_le_iff₀ hs).mpr
    apply (le_abs_self (y - z)).trans
    calc
      |y - z| = |z - y| := abs_sub_comm y z
      _ ≤ 3 * x * Real.sqrt T / 2 := hdisp
      _ = (3 * x / 2) * s := by dsimp only [s]; ring
  have hUV : U + V ≤ 13 * A / 8 := by
    linarith only [hVdisp, hU1, hAx, hx]
  have hi0 := Shao.C2.BridgeIntervalImageResolved.sourceIntervalCompletion_spatial_hasDerivAt
    B PB hB a y T z ha0 hy hz hT
  have hi : HasDerivAt (fun w : ℝ => intervalCompletion Q a w T z)
      (deriv (Shao.C2.IntervalImageCandidateSpatial.intervalImageCandidate a z T) y) y := by
    simpa only [Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion, if_pos hT] using hi0
  have hidI : dI = deriv (Shao.C2.IntervalImageCandidateSpatial.intervalImageCandidate a z T) y := hi.deriv
  have hu0 : HasDerivAt (fun w : ℝ =>
      1 - Real.exp (-2 * (a - w) * (a - z) / T))
      (-(2 * (a - z) / T) * Real.exp (-2 * (a - y) * (a - z) / T)) y := by
    convert (hasDerivAt_const y (1 : ℝ)).sub
      ((((hasDerivAt_const y a).sub (hasDerivAt_id y)).const_mul (-2)
        |>.mul_const (a - z) |>.div_const T).exp) using 1 <;>
      (try funext w) <;> (try simp only [Pi.sub_apply, id_eq]) <;> ring
  have hupper_eq : (fun w : ℝ => upperCompletion Q a w T z) =ᶠ[nhds y]
      (fun w : ℝ => 1 - Real.exp (-2 * (a - w) * (a - z) / T)) := by
    filter_upwards [Iio_mem_nhds (abs_lt.mp hy).2] with w hw
    exact Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula B PB hB a w T z
      hT hw (abs_lt.mp hz).2
  have hup := hu0.congr_of_eventuallyEq hupper_eq
  have hidU : dU = -(2 * V / s) * Real.exp (-2 * U * V) := by
    change deriv (fun w : ℝ => upperCompletion Q a w T z) y = _
    rw [hup.deriv]
    have hc : -(2 * (a - z) / T) = -(2 * V / s) := by
      dsimp only [V]
      rw [← hs2]
      field_simp [hs0] <;> ring
    have he : -2 * (a - y) * (a - z) / T = -2 * U * V := by
      dsimp only [U, V, u]
      rw [← hs2]
      field_simp [hs0] <;> ring
    rw [hc, he]
  have hi' : HasDerivAt (fun w : ℝ => intervalCompletion Q a w T z) dI y := by
    simpa only [hidI] using hi
  have hu' : HasDerivAt (fun w : ℝ => upperCompletion Q a w T z) dU y := by
    simpa only [dU, hup.deriv] using hup
  have hanti : Antitone (fun w : ℝ =>
      upperCompletion Q a w T z - intervalCompletion Q a w T z) := by
    intro w w' hww
    exact upper_deficit_antitone Q a w w' T z z hww le_rfl
  have hsign : 0 ≤ dI - dU := by
    have h := (hu'.sub hi').nonpos_of_antitone hanti
    linarith only [h]
  let E : ℤ → ℝ → ℝ := fun m t =>
    8 * (m : ℝ) ^ 2 * A ^ 2 + 4 * (m : ℝ) * A * (U - t)
  let F : ℤ → ℝ → ℝ := fun j t =>
    8 * (j : ℝ) ^ 2 * A ^ 2 - 4 * (j : ℝ) * A * (U + t) + 2 * U * t
  let G : ℤ → ℝ → ℝ := fun m t =>
    4 * (m : ℝ) * A * Real.exp (-E m t) -
      (4 * (m : ℝ) * A + 2 * t) * Real.exp (-F (-m) t)
  have hfar := arp_far_image_sum_bound A U V hA hU0 hU1 hV.le hUV
  change Summable (fun m : ℤ => if m = 0 then 0 else G m V) ∧
      |tsum (fun m : ℤ => if m = 0 then 0 else G m V)| ≤
        1856 * V * Real.exp (-(11 * A ^ 2 / 8)) at hfar
  let PA : ℤ → ℝ := Shao.C2.IntervalImageIntSeries.spatialImageA 1 a z T y
  let PC : ℤ → ℝ := Shao.C2.IntervalImageIntSeries.spatialImageB 1 a z T y
  obtain ⟨hPA, hPC⟩ := Shao.C2.IntervalImageIntSeries.image_spatial_summable
    1 a z T y ha0 hz.le hT hy.le
  have hseries : dI = tsum (fun m : ℤ => PA m - PC m) := by
    rw [hidI]
    simpa only [iteratedDeriv_one, PA, PC,
      Shao.C2.IntervalImageIntSeries.spatialImageA,
      Shao.C2.IntervalImageIntSeries.spatialImageB] using
      Shao.C2.IntervalImageIntSeries.intervalImageCandidate_iteratedDeriv_eq_intSeries
        1 a z T y ha0 hz.le hT hy
  have hAs : a = s * A := by dsimp only [A]; field_simp [hs0]
  have hUs : u = s * U := by dsimp only [U]; field_simp [hs0]
  have hVs : a - z = s * V := by dsimp only [V]; field_simp [hs0]
  have hys : y = s * (A - U) := by dsimp only [u] at hUs; nlinarith only [hAs, hUs]
  have hzs : z = s * (A - V) := by nlinarith only [hAs, hVs]
  have hEA (m : ℤ) :
      Shao.C2.IntervalImageExponents.imageA a y z (m : ℝ) / T = E m V := by
    dsimp only [Shao.C2.IntervalImageExponents.imageA, E]
    rw [hys, hzs, hAs, ← hs2]
    field_simp [hs0] <;> ring
  have hFB (m : ℤ) :
      Shao.C2.IntervalImageExponents.imageB a y z ((-m - 1 : ℤ) : ℝ) / T = F (-m) V := by
    dsimp only [Shao.C2.IntervalImageExponents.imageB, F]
    push_cast
    rw [hys, hzs, hAs, ← hs2]
    field_simp [hs0] <;> ring
  have hPAvalue (m : ℤ) : PA m = (4 * (m : ℝ) * a / T) *
      Real.exp (-Shao.C2.IntervalImageExponents.imageA a y z (m : ℝ) / T) := by
    dsimp only [PA, Shao.C2.IntervalImageIntSeries.spatialImageA]
    rw [iteratedDeriv_one]
    convert (((Shao.C2.IntervalImageExponents.imageA_hasDerivAt a y z (m : ℝ)).neg.div_const T).exp).deriv using 1 <;> (try simp only [Pi.neg_apply]) <;> ring
  have hPCvalue (m : ℤ) : PC m =
      (-(2 * (z + (2 * (m : ℝ) + 1) * a)) / T) *
        Real.exp (-Shao.C2.IntervalImageExponents.imageB a y z (m : ℝ) / T) := by
    dsimp only [PC, Shao.C2.IntervalImageIntSeries.spatialImageB]
    rw [iteratedDeriv_one]
    convert (((Shao.C2.IntervalImageExponents.imageB_hasDerivAt a y z (m : ℝ)).neg.div_const T).exp).deriv using 1 <;> (try simp only [Pi.neg_apply]) <;> ring
  have hterms (m : ℤ) : s * (PA m - PC (-m - 1)) = G m V := by
    rw [hPAvalue, hPCvalue]
    simp only [neg_div]
    rw [hEA, hFB]
    dsimp only [G]
    push_cast
    rw [hzs, hAs, ← hs2]
    field_simp [hs0] <;> ring
  let e : ℤ ≃ ℤ :=
    { toFun := fun m => -m - 1
      invFun := fun m => -m - 1
      left_inv := by intro m; change -(-m - 1) - 1 = m; omega
      right_inv := by intro m; change -(-m - 1) - 1 = m; omega }
  have he (m : ℤ) : e m = -m - 1 := rfl
  have hPCe : Summable (fun m : ℤ => PC (e m)) := hPC.comp_injective e.injective
  have hPCeq : tsum (fun m : ℤ => PC (e m)) = tsum PC := e.tsum_eq PC
  have hscaled : s * dI = tsum (fun m : ℤ => G m V) := calc
    s * dI = s * tsum (fun m : ℤ => PA m - PC m) := by rw [hseries]
    _ = s * (tsum PA - tsum PC) := by rw [hPA.tsum_sub hPC]
    _ = s * (tsum PA - tsum (fun m : ℤ => PC (e m))) := by rw [hPCeq]
    _ = s * tsum (fun m : ℤ => PA m - PC (e m)) := by rw [hPA.tsum_sub hPCe]
    _ = tsum (fun m : ℤ => s * (PA m - PC (e m))) := by rw [tsum_mul_left]
    _ = tsum (fun m : ℤ => G m V) := by
      congr 1
      funext m
      rw [he]
      exact hterms m
  let H : ℤ → ℝ := fun m => if m = 0 then 0 else G m V
  let J : ℤ → ℝ := fun m => if m = 0 then G 0 V else 0
  have hJ : HasSum J (G 0 V) := hasSum_ite_eq 0 (G 0 V)
  have hsplit : (fun m : ℤ => G m V) = J + H := by
    funext m
    by_cases hm : m = 0 <;> simp [J, H, hm]
  have hsum_split : tsum (fun m : ℤ => G m V) = G 0 V + tsum H := by
    rw [hsplit]
    change tsum (fun m : ℤ => J m + H m) = G 0 V + tsum H
    rw [hJ.summable.tsum_add hfar.1, hJ.tsum_eq]
  have hGzero : G 0 V = -(2 * V) * Real.exp (-2 * U * V) := by
    simp only [G, E, F, Int.cast_zero, Int.neg_zero, zero_pow (by decide : 2 ≠ 0),
      zero_mul, mul_zero, add_zero, zero_add, sub_zero, zero_sub]
    ring
  have hsdU : s * dU = G 0 V := by
    rw [hidU, hGzero]
    field_simp [hs0] <;> ring
  have hsdiff : s * (dI - dU) = tsum H := by
    rw [hsum_split] at hscaled
    nlinarith only [hscaled, hsdU]
  have hbound : s * (dI - dU) ≤ 1856 * V * Real.exp (-(11 * A ^ 2 / 8)) := calc
    _ = tsum H := hsdiff
    _ ≤ |tsum H| := le_abs_self _
    _ ≤ _ := hfar.2
  have hVupper : V ≤ 13 * A / 8 := by linarith only [hUV, hU0]
  have h2UV : 2 * U * V ≤ A ^ 2 / 4 := by
    have hUV1 := mul_le_mul_of_nonneg_right hU1 hV.le
    nlinarith only [hUV1, hVupper, hA, sq_nonneg (A - 13)]
  have hexp : Real.exp (-(11 * A ^ 2 / 8)) ≤
      Real.exp (-A ^ 2) * Real.exp (-2 * U * V) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [h2UV, sq_nonneg A]
  have hscaled_final : s * (dI - dU) ≤
      s * (2048 * Real.exp (-A ^ 2) * (-dU)) := calc
    _ ≤ 1856 * V * Real.exp (-(11 * A ^ 2 / 8)) := hbound
    _ ≤ 1856 * V * (Real.exp (-A ^ 2) * Real.exp (-2 * U * V)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ 4096 * V * (Real.exp (-A ^ 2) * Real.exp (-2 * U * V)) := by
      gcongr <;> norm_num
    _ = s * (2048 * Real.exp (-A ^ 2) * (-dU)) := by
      rw [hidU]
      field_simp [hs0] <;> ring
  have hfinal : dI - dU ≤ 2048 * Real.exp (-A ^ 2) * (-dU) :=
    (mul_le_mul_iff_right₀ hs).mp (by simpa only [mul_comm s] using hscaled_final)
  have hA2 : A ^ 2 = a ^ 2 / T := by dsimp only [A]; rw [div_pow, hs2]
  exact ⟨hsign, by simpa only [hA2] using hfinal⟩

end Shao.Probability.SourceActualRegularPhysicalRatio
