/- Genuine actual separated-overshoot source consumers. -/
import Shao.Probability.SourcePermutationReveal
import Shao.C2.BridgeDomination
import Shao.C2.CompletionMeasurability
import Shao.C1.PermutationEnergyEnvelope
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.Probability.SourceSeparatedOvershoot
open MeasureTheory
open SourcePermutationReveal
open Shao.C2.BridgeDomination
open scoped BigOperators Classical

local instance labelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

/-- 只投影到实际跨越的监测壁；未跨越时保留原增量。 -/
def projectionIncrement (J : MonitoredDomain) (w y b : ℝ) : ℝ :=
  match J with
  | .upper => if w ≤ y + b then w - y else b
  | .lower => if y + b ≤ -w then -w - y else b
  | .interval => if w ≤ y + b then w - y else
      if y + b ≤ -w then -w - y else b

def localRetainedRemainder (J : MonitoredDomain) (F G : BridgeKernel)
    (w y T z b : ℝ) : ℝ :=
  if 0 < T ∧ b ^ 2 ≤ T / 2 then
    localRemainder J F G w y T z (projectionIncrement J w y b)
  else localRemainder J F G w y T z b

/-- 此值就是 S.8.17 的 -η δ c f_y；未跨越及大能量步恰为零。 -/
def localSeparatedOvershoot (J : MonitoredDomain) (G : BridgeKernel)
    (w y T z b : ℝ) : ℝ :=
  if 0 < T ∧ b ^ 2 ≤ T / 2 then
    -(b - projectionIncrement J w y b) *
      (1 - (b + projectionIncrement J w y b) * (z - y) / T) *
      G (w, y, T, z)
  else 0

def sourceRetainedRemainder {n : ℕ} (J : MonitoredDomain) (F G : BridgeKernel)
    (a : Shao.Path n) (x : ℝ) (ν : LabelPerm n → ℕ)
    (r : ℕ) (σ : LabelPerm n) : ℝ :=
  if hr : r < n then
    if r < ν σ ∧ sourceAlive J a x r σ ∧ 0 < remainingEnergy a r σ then
      localRetainedRemainder J F G (actualWall a x)
        (Shao.prefixSum (Spitzer.reorder a σ) r)
        (remainingEnergy a r σ) (Shao.prefixSum a n) (a (σ ⟨r, hr⟩))
    else 0
  else 0

def sourceSeparatedOvershoot {n : ℕ} (J : MonitoredDomain) (G : BridgeKernel)
    (a : Shao.Path n) (x : ℝ) (ν : LabelPerm n → ℕ)
    (r : ℕ) (σ : LabelPerm n) : ℝ :=
  if hr : r < n then
    if r < ν σ ∧ sourceAlive J a x r σ ∧ 0 < remainingEnergy a r σ then
      localSeparatedOvershoot J G (actualWall a x)
        (Shao.prefixSum (Spitzer.reorder a σ) r)
        (remainingEnergy a r σ) (Shao.prefixSum a n) (a (σ ⟨r, hr⟩))
    else 0
  else 0

def retainedSum {n : ℕ} (J : MonitoredDomain) (F G : BridgeKernel)
    (a : Shao.Path n) (x : ℝ) (ν : LabelPerm n → ℕ) (σ : LabelPerm n) : ℝ :=
  ∑ r ∈ Finset.range n, sourceRetainedRemainder J F G a x ν r σ

def separatedSum {n : ℕ} (J : MonitoredDomain) (G : BridgeKernel)
    (a : Shao.Path n) (x : ℝ) (ν : LabelPerm n → ℕ) (σ : LabelPerm n) : ℝ :=
  ∑ r ∈ Finset.range n, sourceSeparatedOvershoot J G a x ν r σ

theorem projection_increment_geometry
    (J : MonitoredDomain) (w y b : ℝ) (hw : 0 < w) (hy : Interior J w y) :
    let p : ℝ := projectionIncrement J w y b
    min 0 b ≤ p ∧ p ≤ max 0 b ∧ |p| ≤ |b| ∧ |b - p| ≤ |b| ∧
      (p ≠ b → ¬Interior J w (y + b) ∧ ¬Interior J w (y + p)) := by
  classical
  have hp (p : ℝ) (hp0 : 0 ≤ p) (hpb : p ≤ b) :
      min 0 b ≤ p ∧ p ≤ max 0 b ∧ |p| ≤ |b| ∧ |b - p| ≤ |b| := by
    have hb : 0 ≤ b := hp0.trans hpb
    simp only [min_eq_left hb, max_eq_right hb, abs_of_nonneg hp0, abs_of_nonneg hb,
      abs_of_nonneg (sub_nonneg.mpr hpb)]
    exact ⟨hp0, hpb, hpb, by linarith⟩
  have hn (p : ℝ) (hbp : b ≤ p) (hp0 : p ≤ 0) :
      min 0 b ≤ p ∧ p ≤ max 0 b ∧ |p| ≤ |b| ∧ |b - p| ≤ |b| := by
    have hb : b ≤ 0 := hbp.trans hp0
    simp only [min_eq_right hb, max_eq_left hb, abs_of_nonpos hp0, abs_of_nonpos hb,
      abs_of_nonpos (sub_nonpos.mpr hbp)]
    exact ⟨hbp, hp0, by linarith, by linarith⟩
  have he : min 0 b ≤ b ∧ b ≤ max 0 b ∧ |b| ≤ |b| ∧ |b - b| ≤ |b| ∧
      (b ≠ b → ¬Interior J w (y + b) ∧ ¬Interior J w (y + b)) := by
    exact ⟨min_le_right _ _, le_max_right _ _, le_rfl, by simp, fun h => False.elim (h rfl)⟩
  dsimp only
  cases J with
  | upper =>
    dsimp only [projectionIncrement]
    split_ifs with hc
    · have hy' : y < w := hy
      rcases hp (w - y) (by linarith) (by linarith) with ⟨h1,h2,h3,h4⟩
      exact ⟨h1,h2,h3,h4, fun _ => ⟨by dsimp only [Interior]; linarith,
        by dsimp only [Interior]; linarith⟩⟩
    · exact he
  | lower =>
    dsimp only [projectionIncrement]
    split_ifs with hc
    · have hy' : -w < y := hy
      rcases hn (-w - y) (by linarith) (by linarith) with ⟨h1,h2,h3,h4⟩
      exact ⟨h1,h2,h3,h4, fun _ => ⟨by dsimp only [Interior]; linarith,
        by dsimp only [Interior]; linarith⟩⟩
    · exact he
  | interval =>
    rcases hy with ⟨hyl,hyu⟩
    dsimp only [projectionIncrement]
    split_ifs with hc hl
    · rcases hp (w - y) (by linarith) (by linarith) with ⟨h1,h2,h3,h4⟩
      refine ⟨h1,h2,h3,h4, fun _ => ⟨?_,?_⟩⟩
      · intro h
        exact (not_lt_of_ge hc) h.2
      · intro h
        dsimp only [Interior] at h
        linarith [h.2]
    · rcases hn (-w - y) (by linarith) (by linarith) with ⟨h1,h2,h3,h4⟩
      refine ⟨h1,h2,h3,h4, fun _ => ⟨?_,?_⟩⟩
      · intro h
        exact (not_lt_of_ge hl) h.1
      · intro h
        dsimp only [Interior] at h
        linarith [h.1]
    · exact he

theorem local_projection_remainder_decomposition
    (J : MonitoredDomain) (F G : BridgeKernel)
    (w y T z b : ℝ) (hw : 0 < w)
    (hy : Interior J w y) (hz : Interior J w z) :
    localRemainder J F G w y T z b =
      localRetainedRemainder J F G w y T z b +
      localSeparatedOvershoot J G w y T z b := by
  classical
  by_cases hs : 0 < T ∧ b ^ 2 ≤ T / 2
  · rw [localRetainedRemainder, localSeparatedOvershoot, if_pos hs, if_pos hs]
    let p : ℝ := projectionIncrement J w y b
    change localRemainder J F G w y T z b =
      localRemainder J F G w y T z p +
        (-(b - p) * (1 - (b + p) * (z - y) / T) * G (w,y,T,z))
    by_cases hp : p = b
    · simp only [hp, sub_self, neg_zero, zero_mul, add_zero]
    · have hg := (projection_increment_geometry J w y b hw hy).2.2.2.2 hp
      have hbzero : completionExt J F w (y + b) (T - b ^ 2) z = 0 := by
        unfold completionExt
        exact if_neg (by tauto)
      have hpzero : completionExt J F w (y + p) (T - p ^ 2) z = 0 := by
        unfold completionExt
        exact if_neg (by tauto)
      change localRemainder J F G w y T z b =
        localRemainder J F G w y T z p +
          (-(b - p) * (1 - (b + p) * (z - y) / T) * G (w,y,T,z))
      unfold localRemainder
      rw [hbzero, hpzero]
      unfold compensationCoefficient
      ring
  · simp only [localRetainedRemainder, localSeparatedOvershoot, if_neg hs, add_zero]

theorem projected_negative_part_control
    (J : MonitoredDomain) (P : Measure BridgeNoise) [IsProbabilityMeasure P]
    (G : BridgeKernel) (η w y T z b : ℝ)
    (hη : η = 1 ∨ η = -1)
    (hwall : J = .interval ∨ (J = .upper ∧ η = 1) ∨ (J = .lower ∧ η = -1))
    (hw : 0 < w) (hT : 0 < T)
    (hy : Interior J w y) (hz : Interior J w z)
    (hcross : w ≤ η * (y + b)) (hsmall : b ^ 2 ≤ T / 2) :
    let B : ℝ := |b|
    let u : ℝ := w - η * y
    let p : ℝ := η * u
    let δ : ℝ := B - u
    let d : ℝ := z - y
    let D : ℝ := 1 + |d| / Real.sqrt T
    let A : ℝ := 1 - η * u * d / T
    let c : ℝ := 1 - η * (B + u) * d / T
    let Rp : ℝ := localRemainder J (eventCompletionKernel J P) G w y T z p
    let O : ℝ := -η * δ * c * G (w, y, T, z)
    η * b = B ∧ 0 < u ∧ u ≤ B ∧ 0 ≤ δ ∧ δ ≤ B ∧
      1 / 2 ≤ A ∧ 0 ≤ c ∧ c ≤ 2 * D ∧
      localSeparatedOvershoot J G w y T z b = O ∧
      u ^ 2 * (|Rp| + max (-O) 0) ≤ B ^ 2 * |Rp| := by
  classical
  intro B u p δ d D A c Rp O
  have hdir (v : ℝ) (hv : Interior J w v) : η * v < w := by
    rcases hwall with hJ | ⟨hJ,he⟩ | ⟨hJ,he⟩
    · subst J
      rcases hη with rfl | rfl
      · simpa only [one_mul] using hv.2
      · simp only [neg_one_mul]
        linarith [hv.1]
    · subst J
      rw [he, one_mul]
      exact hv
    · subst J
      rw [he, neg_one_mul]
      change -w < v at hv
      linarith
  have hu : 0 < u := by dsimp only [u]; linarith [hdir y hy]
  have hub' : u ≤ η * b := by dsimp only [u]; nlinarith only [hcross]
  have hB : 0 ≤ B := abs_nonneg b
  have heb : η * b = B := by
    have hh : 0 < η * b := hu.trans_le hub'
    rcases hη with rfl | rfl
    · have hb : 0 < b := by simpa only [one_mul] using hh
      simp only [B, one_mul, abs_of_pos hb]
    · have hb : b < 0 := by nlinarith only [hh]
      simp only [B, neg_one_mul, abs_of_neg hb]
  have hub : u ≤ B := by rwa [heb] at hub'
  have hδ : 0 ≤ δ := by dsimp only [δ]; linarith
  have hδB : δ ≤ B := by dsimp only [δ]; linarith
  have hdu : η * d < u := by dsimp only [d,u]; nlinarith only [hdir z hz]
  have hBsq : B ^ 2 = b ^ 2 := sq_abs b
  have hu2 : u ^ 2 ≤ b ^ 2 := by
    rw [← hBsq]
    exact pow_le_pow_left₀ hu.le hub 2
  have hA : 1 / 2 ≤ A := by
    have hm := mul_le_mul_of_nonneg_left hdu.le hu.le
    have hnum : η * u * d ≤ T / 2 := by nlinarith only [hm, hu2, hsmall]
    have hf : η * u * d / T ≤ 1 / 2 := (div_le_iff₀ hT).2 (by linarith only [hnum])
    dsimp only [A]
    linarith only [hf]
  have hAp : 0 < A := by linarith only [hA]
  have hBu : 0 ≤ B + u := by linarith
  have hc : 0 ≤ c := by
    have hm := mul_le_mul_of_nonneg_left hdu.le hBu
    have hmB := mul_le_mul_of_nonneg_left hub hB
    have hnum : η * (B + u) * d ≤ T := by nlinarith only [hm, hmB, hu2, hBsq, hsmall]
    have hf : η * (B + u) * d / T ≤ 1 := (div_le_one hT).2 hnum
    dsimp only [c]
    linarith only [hf]
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hBs : B ≤ Real.sqrt T := by
    nlinarith only [hB, hBsq, hsmall, Real.sq_sqrt hT.le, Real.sqrt_nonneg T]
  have hηabs : |η| = 1 := by rcases hη with rfl | rfl <;> norm_num
  have hcD : c ≤ 2 * D := by
    have hnum : -η * (B + u) * d ≤ (B + u) * |d| := by
      calc
        _ ≤ |η * (B + u) * d| := by
          simpa only [neg_mul] using neg_le_abs (η * (B + u) * d)
        _ = _ := by rw [abs_mul, abs_mul, hηabs, abs_of_nonneg hBu, one_mul]
    have hnum2 : (B + u) * |d| ≤ (2 * Real.sqrt T) * |d| :=
      mul_le_mul_of_nonneg_right (by linarith only [hub, hBs]) (abs_nonneg d)
    have heq : (2 * Real.sqrt T) * |d| / T = 2 * |d| / Real.sqrt T := by
      apply (div_eq_div_iff hT.ne' hs.ne').2
      have hh := congrArg (fun z : ℝ => 2 * |d| * z) (Real.sq_sqrt hT.le)
      nlinarith only [hh]
    calc
      c = 1 + (-η * (B + u) * d) / T := by dsimp only [c]; ring
      _ ≤ 1 + (B + u) * |d| / T :=
        add_le_add le_rfl (div_le_div_of_nonneg_right hnum hT.le)
      _ ≤ 1 + (2 * Real.sqrt T) * |d| / T :=
        add_le_add le_rfl (div_le_div_of_nonneg_right hnum2 hT.le)
      _ = 1 + 2 * |d| / Real.sqrt T := by rw [heq]
      _ ≤ 2 * D := by
        dsimp only [D]
        have hh : (1 : ℝ) + 2 * (|d| / Real.sqrt T) ≤ 2 * (1 + |d| / Real.sqrt T) := by linarith
        convert hh using 1 <;> ring
  have hpwallEq : η * (y + p) = w := by
    rcases hη with rfl | rfl <;> dsimp only [p,u] <;> ring
  have hpwall : ¬Interior J w (y + p) := by
    intro hv
    have hh := hdir (y + p) hv
    rw [hpwallEq] at hh
    exact (lt_irrefl w) hh
  have hproj : projectionIncrement J w y b = p := by
    rcases hwall with hJ | ⟨hJ,he⟩ | ⟨hJ,he⟩
    · subst J
      rcases hη with rfl | rfl
      · have hc' : w ≤ y + b := by simpa only [one_mul] using hcross
        simp only [projectionIncrement, if_pos hc', p, u, one_mul]
      · have hc' : y + b ≤ -w := by nlinarith only [hcross]
        have hn : ¬w ≤ y + b := by linarith only [hc',hw]
        simp only [projectionIncrement, if_neg hn, if_pos hc', p,u,neg_one_mul]
        ring
    · subst J
      subst η
      have hc' : w ≤ y + b := by simpa only [one_mul] using hcross
      simp only [projectionIncrement, if_pos hc', p,u,one_mul]
    · subst J
      subst η
      have hc' : y + b ≤ -w := by nlinarith only [hcross]
      simp only [projectionIncrement, if_pos hc', p,u,neg_one_mul]
      ring
  have hO : localSeparatedOvershoot J G w y T z b = O := by
    rw [localSeparatedOvershoot, if_pos ⟨hT,hsmall⟩, hproj]
    have hb : b = η * B := by
      rcases hη with rfl | rfl <;> simp only [one_mul,neg_one_mul] at heb ⊢ <;> linarith
    dsimp only [O,δ,c,p,d]
    rw [hb]
    rcases hη with rfl | rfl <;> ring
  have hRp : Rp = -eventCompletionKernel J P (w,y,T,z) -
      u * A * (η * G (w,y,T,z)) := by
    have hz0 : completionExt J (eventCompletionKernel J P) w (y + p) (T - p ^ 2) z = 0 := by
      unfold completionExt
      exact if_neg (by tauto)
    dsimp only [Rp, localRemainder]
    rw [hz0]
    dsimp only [compensationCoefficient,p,A,d]
    ring
  have hf : 0 ≤ eventCompletionKernel J P (w,y,T,z) :=
    ((eventCompletionKernel_data J P).2.1 (w,y,T,z)).1
  have hgrad : u * A * (η * G (w,y,T,z)) ≤ |Rp| := by
    linarith only [neg_le_abs Rp,hRp,hf]
  have hneg : u * A * max (-O) 0 ≤ δ * c * |Rp| := by
    by_cases hOpos : 0 ≤ -O
    · rw [max_eq_left hOpos]
      calc
        _ = (δ * c) * (u * A * (η * G (w,y,T,z))) := by dsimp only [O]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hgrad (mul_nonneg hδ hc)
    · rw [max_eq_right (le_of_not_ge hOpos)]
      simp only [mul_zero]
      positivity
  have hid : u * c ≤ (B + u) * A := by
    have heq : (B + u) * A - u * c = B := by dsimp only [A,c]; ring
    linarith only [heq,hB]
  have hpart : u ^ 2 * max (-O) 0 ≤ δ * (B + u) * |Rp| := by
    apply (mul_le_mul_iff_left₀ hAp).mp
    calc
      _ = u * (u * A * max (-O) 0) := by ring
      _ ≤ u * (δ * c * |Rp|) := mul_le_mul_of_nonneg_left hneg hu.le
      _ = (δ * |Rp|) * (u * c) := by ring
      _ ≤ (δ * |Rp|) * ((B + u) * A) :=
        mul_le_mul_of_nonneg_left hid (mul_nonneg hδ (abs_nonneg Rp))
      _ = _ := by ring
  refine ⟨heb,hu,hub,hδ,hδB,hA,hc,hcD,hO,?_⟩
  calc
    _ = u ^ 2 * |Rp| + u ^ 2 * max (-O) 0 := by ring
    _ ≤ u ^ 2 * |Rp| + δ * (B + u) * |Rp| := add_le_add le_rfl hpart
    _ = _ := by dsimp only [δ]; ring

theorem source_selected_remainder_decomposition
    {n : ℕ} (J : MonitoredDomain) (F G : BridgeKernel)
    (a : Shao.Path n) (x : ℝ) (hx : 0 < x)
    (ν : LabelPerm n → ℕ) (r : ℕ) (σ : LabelPerm n) :
    (if r < ν σ then sourceRemainder J F G a x r σ else 0) =
      sourceRetainedRemainder J F G a x ν r σ +
      sourceSeparatedOvershoot J G a x ν r σ := by
  classical
  by_cases hr : r < n
  · by_cases hact : r < ν σ ∧ sourceAlive J a x r σ ∧ 0 < remainingEnergy a r σ
    · have hs : sourceAlive J a x r σ ∧ 0 < remainingEnergy a r σ := hact.2
      have hw : 0 < actualWall a x := mul_pos hx (Real.sqrt_pos.2 hact.2.1.1)
      have hy : Interior J (actualWall a x) (Shao.prefixSum (Spitzer.reorder a σ) r) :=
        hact.2.1.2.2 r le_rfl
      have hz : Interior J (actualWall a x) (Shao.prefixSum a n) := hact.2.1.2.1
      simp only [if_pos hact.1, sourceRemainder, sourceRetainedRemainder,
        sourceSeparatedOvershoot, dif_pos hr, if_pos hs, if_pos hact]
      exact local_projection_remainder_decomposition J F G _ _ _ _ _ hw hy hz
    · by_cases hv : r < ν σ
      · have hs : ¬(sourceAlive J a x r σ ∧ 0 < remainingEnergy a r σ) := by tauto
        simp only [sourceRemainder, sourceRetainedRemainder, sourceSeparatedOvershoot,
          dif_pos hr, if_pos hv, if_neg hs, if_neg hact, zero_add]
      · simp only [sourceRetainedRemainder, sourceSeparatedOvershoot, dif_pos hr,
          if_neg hv, if_neg hact, zero_add]
  · simp only [sourceRemainder, sourceRetainedRemainder, sourceSeparatedOvershoot,
      dif_neg hr, ite_self, zero_add]

theorem source_parts_uniform_bound
    {n : ℕ} (J : MonitoredDomain) (F G : BridgeKernel)
    (C : ℝ) (hK : KernelBounds J F G C)
    (a : Shao.Path n) (x : ℝ) (hx : 0 < x)
    (ν : LabelPerm n → ℕ) (r : ℕ) (σ : LabelPerm n) :
    |sourceSeparatedOvershoot J G a x ν r σ| ≤ 4 * C * (1 + (n : ℝ)) ∧
      |sourceRetainedRemainder J F G a x ν r σ| ≤ 1 + 6 * C * (1 + (n : ℝ)) := by
  classical
  have hC := hK.nonnegC
  have hO : |sourceSeparatedOvershoot J G a x ν r σ| ≤ 4 * C * (1 + (n : ℝ)) := by
    by_cases hr : r < n
    · unfold sourceSeparatedOvershoot
      rw [dif_pos hr]
      split_ifs with hact
      · unfold localSeparatedOvershoot
        split_ifs with hsml
        · let w : ℝ := actualWall a x
          let y : ℝ := Shao.prefixSum (Spitzer.reorder a σ) r
          let T : ℝ := remainingEnergy a r σ
          let z : ℝ := Shao.prefixSum a n
          let b : ℝ := a (σ ⟨r,hr⟩)
          let p : ℝ := projectionIncrement J w y b
          let d : ℝ := z - y
          let s : ℝ := Real.sqrt T
          let D : ℝ := 1 + |d| / s
          have hT : 0 < T := hact.2.2
          have hs : 0 < s := Real.sqrt_pos.2 hT
          have hw : 0 < w := mul_pos hx (Real.sqrt_pos.2 hact.2.1.1)
          have hy : Interior J w y := hact.2.1.2.2 r le_rfl
          have hz : Interior J w z := hact.2.1.2.1
          have hg := remaining_population_geometry a r hr.le σ
          have hb2 : b ^ 2 ≤ T := hg.2.2.1 ⟨r,hr⟩ le_rfl
          have hd2 : d ^ 2 ≤ ((n - r : ℕ) : ℝ) * T := hg.2.1
          have hb : |b| ≤ s := by
            nlinarith only [hb2, sq_abs b, Real.sq_sqrt hT.le, Real.sqrt_nonneg T]
          have hratio : (|d| / s) ^ 2 ≤ ((n - r : ℕ) : ℝ) := by
            rw [div_pow, sq_abs, Real.sq_sqrt hT.le]
            exact (div_le_iff₀ hT).2 hd2
          have hn : ((n - r : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n r
          have hD2 : D ^ 2 ≤ 2 * (1 + (n : ℝ)) := by
            dsimp only [D]
            nlinarith only [hratio,hn,sq_nonneg (|d| / s - 1)]
          have hD0 : 0 ≤ D := by dsimp only [D]; positivity
          have hp := projection_increment_geometry J w y b hw hy
          have hbp : |b - p| ≤ s := hp.2.2.2.1.trans hb
          have hbplus : |b + p| ≤ 2 * s := by
            calc
              _ ≤ |b| + |p| := abs_add_le b p
              _ ≤ _ := by linarith only [hp.2.2.1,hb]
          have hrough : |1 - (b + p) * d / T| ≤ 1 + |b + p| * |d| / T := by
            have hh := abs_sub_le (1 : ℝ) 0 ((b + p) * d / T)
            simpa only [sub_zero,zero_sub,abs_neg,abs_one,abs_div,abs_mul,abs_of_pos hT] using hh
          have heq : (2 * s) * |d| / T = 2 * |d| / s := by
            apply (div_eq_div_iff hT.ne' hs.ne').2
            have hh := congrArg (fun z : ℝ => 2 * |d| * z) (Real.sq_sqrt hT.le)
            nlinarith only [hh]
          have hc : |1 - (b + p) * d / T| ≤ 2 * D := by
            calc
              _ ≤ 1 + |b + p| * |d| / T := hrough
              _ ≤ 1 + (2 * s) * |d| / T := add_le_add le_rfl
                (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hbplus (abs_nonneg d)) hT.le)
              _ = 1 + 2 * |d| / s := by rw [heq]
              _ ≤ 2 * D := by
                dsimp only [D]
                have hh : (1 : ℝ) + 2 * (|d| / s) ≤ 2 * (1 + |d| / s) := by linarith
                convert hh using 1 <;> ring
          have hG : |G (w,y,T,z)| ≤ C / s * D := hK.derivative_bound w y T z hw hT hy hz
          change |-(b - p) * (1 - (b + p) * d / T) * G (w,y,T,z)| ≤ _
          rw [abs_mul,abs_mul,abs_neg]
          calc
            _ ≤ (s * (2 * D)) * (C / s * D) :=
              mul_le_mul (mul_le_mul hbp hc (abs_nonneg _) hs.le) hG
                (abs_nonneg _) (mul_nonneg hs.le (mul_nonneg (by norm_num) hD0))
            _ = 2 * C * D ^ 2 := by field_simp
            _ ≤ 2 * C * (2 * (1 + (n : ℝ))) :=
              mul_le_mul_of_nonneg_left hD2 (mul_nonneg (by norm_num) hC)
            _ = _ := by ring
        · simp only [abs_zero]
          positivity
      · simp only [abs_zero]
        positivity
    · simp only [sourceSeparatedOvershoot,dif_neg hr,abs_zero]
      positivity
  have hR : |if r < ν σ then sourceRemainder J F G a x r σ else 0| ≤
      1 + 2 * C * (1 + (n : ℝ)) := by
    split_ifs
    · exact (source_remainder_uniform_bound J F G C hK a x hx r σ).2
    · simp only [abs_zero]
      positivity
  have hsplit := source_selected_remainder_decomposition J F G a x hx ν r σ
  have htri : |sourceRetainedRemainder J F G a x ν r σ| ≤
      |if r < ν σ then sourceRemainder J F G a x r σ else 0| +
        |sourceSeparatedOvershoot J G a x ν r σ| := by
    rw [hsplit]
    have hh := abs_sub_le
      (sourceRetainedRemainder J F G a x ν r σ + sourceSeparatedOvershoot J G a x ν r σ)
      0 (sourceSeparatedOvershoot J G a x ν r σ)
    simpa only [add_sub_cancel_right,sub_zero,zero_sub,abs_neg] using hh
  exact ⟨hO, by linarith only [htri,hR,hO]⟩

theorem source_parts_measurable_integrable
    {n : ℕ} (J : MonitoredDomain) (F G : BridgeKernel)
    (hFm : Measurable F) (hGm : Measurable G)
    (C : ℝ) (hK : KernelBounds J F G C)
    (P : Measure (Shao.Path n)) [IsProbabilityMeasure P]
    (x : ℝ) (hx : 0 < x) (ν : Shao.Path n → LabelPerm n → ℕ)
    (hνm : ∀ σ, Measurable (fun a => ν a σ)) :
    (∀ (σ : LabelPerm n) (r : ℕ),
      Measurable (fun a => sourceRetainedRemainder J F G a x (ν a) r σ) ∧
      Measurable (fun a => sourceSeparatedOvershoot J G a x (ν a) r σ)) ∧
    (∀ r : ℕ,
      Integrable (fun p : Shao.Path n × LabelPerm n =>
        sourceRetainedRemainder J F G p.1 x (ν p.1) r p.2) (revealLaw P) ∧
      Integrable (fun p : Shao.Path n × LabelPerm n =>
        sourceSeparatedOvershoot J G p.1 x (ν p.1) r p.2) (revealLaw P)) ∧
    Integrable (fun p : Shao.Path n × LabelPerm n =>
      retainedSum J F G p.1 x (ν p.1) p.2) (revealLaw P) ∧
    Integrable (fun p : Shao.Path n × LabelPerm n =>
      separatedSum J G p.1 x (ν p.1) p.2) (revealLaw P) := by
  classical
  letI : IsProbabilityMeasure (revealLaw P) := by unfold revealLaw; infer_instance
  have hInterior (W Y : Shao.Path n → ℝ) (hW : Measurable W) (hY : Measurable Y) :
      MeasurableSet {a | Interior J (W a) (Y a)} := by
    cases J with
    | upper => exact measurableSet_lt hY hW
    | lower => exact measurableSet_lt hW.neg hY
    | interval =>
      simpa only [Interior,Set.setOf_and,Pi.neg_apply] using
        (measurableSet_lt hW.neg hY).inter (measurableSet_lt hY hW)
  have hExt (W Y TT Z : Shao.Path n → ℝ) (hW : Measurable W) (hY : Measurable Y)
      (hTT : Measurable TT) (hZ : Measurable Z) :
      Measurable (fun a => completionExt J F (W a) (Y a) (TT a) (Z a)) := by
    unfold completionExt
    apply Measurable.ite ((measurableSet_lt measurable_const hW).inter
      ((hInterior W Y hW hY).inter (hInterior W Z hW hZ)))
    · apply Measurable.ite (measurableSet_lt measurable_const hTT)
      · exact hFm.comp (hW.prodMk (hY.prodMk (hTT.prodMk hZ)))
      · exact Measurable.ite
          ((measurableSet_eq_fun hTT measurable_const).inter (measurableSet_eq_fun hY hZ))
          measurable_const measurable_const
    · exact measurable_const
  have hW : Measurable (fun a : Shao.Path n => actualWall a x) :=
    measurable_const.mul Shao.measurable_energy.sqrt
  have hZ : Measurable (fun a : Shao.Path n => Shao.prefixSum a n) := Shao.measurable_prefixSum n
  have hAlive (σ : LabelPerm n) (r : ℕ) :
      MeasurableSet {a : Shao.Path n | sourceAlive J a x r σ} := by
    have hσ : Measurable (fun a : Shao.Path n => Spitzer.reorder a σ) :=
      Measurable.of_eval (fun i => measurable_pi_apply (σ i))
    have hSurv (s : Finset ℕ) : MeasurableSet {a : Shao.Path n |
        ∀ k ∈ s, Interior J (actualWall a x) (Shao.prefixSum (Spitzer.reorder a σ) k)} := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert k s hk ih =>
        simpa only [Finset.forall_mem_insert,Set.setOf_and,Function.comp_def] using
          (hInterior _ _ hW ((Shao.measurable_prefixSum k).comp hσ)).inter ih
    have hPrefix : MeasurableSet {a : Shao.Path n |
        ∀ k : ℕ, k ≤ r → Interior J (actualWall a x) (Shao.prefixSum (Spitzer.reorder a σ) k)} := by
      simpa only [Finset.mem_range,Nat.lt_succ_iff] using hSurv (Finset.range (r + 1))
    simpa only [sourceAlive,Set.setOf_and] using
      (measurableSet_lt measurable_const Shao.measurable_energy).inter
        ((hInterior _ _ hW hZ).inter hPrefix)
  have hSections (σ : LabelPerm n) (r : ℕ) :
      Measurable (fun a : Shao.Path n => sourceRetainedRemainder J F G a x (ν a) r σ) ∧
      Measurable (fun a : Shao.Path n => sourceSeparatedOvershoot J G a x (ν a) r σ) := by
    by_cases hr : r < n
    · have hσ : Measurable (fun a : Shao.Path n => Spitzer.reorder a σ) :=
        Measurable.of_eval (fun i => measurable_pi_apply (σ i))
      have hY : Measurable (fun a : Shao.Path n => Shao.prefixSum (Spitzer.reorder a σ) r) :=
        (Shao.measurable_prefixSum r).comp hσ
      have hTT : Measurable (fun a : Shao.Path n => remainingEnergy a r σ) :=
        Shao.measurable_energy.sub ((Shao.measurable_prefixSquares r).comp hσ)
      have hB : Measurable (fun a : Shao.Path n => a (σ ⟨r,hr⟩)) := measurable_pi_apply _
      have hProj : Measurable (fun a : Shao.Path n => projectionIncrement J (actualWall a x)
          (Shao.prefixSum (Spitzer.reorder a σ) r) (a (σ ⟨r,hr⟩))) := by
        cases J with
        | upper => exact Measurable.ite (measurableSet_le hW (hY.add hB)) (hW.sub hY) hB
        | lower => exact Measurable.ite (measurableSet_le (hY.add hB) hW.neg) (hW.neg.sub hY) hB
        | interval =>
          exact Measurable.ite (measurableSet_le hW (hY.add hB)) (hW.sub hY)
            (Measurable.ite (measurableSet_le (hY.add hB) hW.neg) (hW.neg.sub hY) hB)
      have hSmall : MeasurableSet {a : Shao.Path n |
          0 < remainingEnergy a r σ ∧ (a (σ ⟨r,hr⟩)) ^ 2 ≤ remainingEnergy a r σ / 2} :=
        (measurableSet_lt measurable_const hTT).inter
          (measurableSet_le (hB.pow_const 2) (hTT.div_const 2))
      have hGuard : MeasurableSet {a : Shao.Path n |
          r < ν a σ ∧ sourceAlive J a x r σ ∧ 0 < remainingEnergy a r σ} :=
        (measurableSet_lt measurable_const (hνm σ)).inter
          ((hAlive σ r).inter (measurableSet_lt measurable_const hTT))
      have hGstate := hGm.comp (hW.prodMk (hY.prodMk (hTT.prodMk hZ)))
      have hFstate := hFm.comp (hW.prodMk (hY.prodMk (hTT.prodMk hZ)))
      have hRem (f : Shao.Path n → ℝ) (hf : Measurable f) :
          Measurable (fun a : Shao.Path n => localRemainder J F G (actualWall a x)
            (Shao.prefixSum (Spitzer.reorder a σ) r) (remainingEnergy a r σ)
            (Shao.prefixSum a n) (f a)) := by
        exact (((hExt _ _ _ _ hW (hY.add hf) (hTT.sub (hf.pow_const 2)) hZ).sub hFstate).sub
          ((hf.sub (((hf.pow_const 2).mul (hZ.sub hY)).div hTT)).mul hGstate))
      have hL : Measurable (fun a : Shao.Path n => localRetainedRemainder J F G (actualWall a x)
          (Shao.prefixSum (Spitzer.reorder a σ) r) (remainingEnergy a r σ)
          (Shao.prefixSum a n) (a (σ ⟨r,hr⟩))) :=
        Measurable.ite hSmall (hRem _ hProj) (hRem _ hB)
      have hO : Measurable (fun a : Shao.Path n => localSeparatedOvershoot J G (actualWall a x)
          (Shao.prefixSum (Spitzer.reorder a σ) r) (remainingEnergy a r σ)
          (Shao.prefixSum a n) (a (σ ⟨r,hr⟩))) :=
        Measurable.ite hSmall
          ((((hB.sub hProj).neg).mul
            (measurable_const.sub (((hB.add hProj).mul (hZ.sub hY)).div hTT))).mul hGstate)
          measurable_const
      constructor
      · simpa only [sourceRetainedRemainder,dif_pos hr] using Measurable.ite hGuard hL measurable_const
      · simpa only [sourceSeparatedOvershoot,dif_pos hr] using Measurable.ite hGuard hO measurable_const
    · constructor
      · simpa only [sourceRetainedRemainder,dif_neg hr] using
          (measurable_const : Measurable (fun _ : Shao.Path n => (0 : ℝ)))
      · simpa only [sourceSeparatedOvershoot,dif_neg hr] using
          (measurable_const : Measurable (fun _ : Shao.Path n => (0 : ℝ)))
  have hJoint (f : Shao.Path n → LabelPerm n → ℝ)
      (hf : ∀ σ, Measurable (fun a => f a σ)) :
      Measurable (fun p : Shao.Path n × LabelPerm n => f p.1 p.2) := by
    have he (p : Shao.Path n × LabelPerm n) :
        (∑ σ : LabelPerm n, if p.2 = σ then f p.1 σ else 0) = f p.1 p.2 := by simp
    have hm : Measurable (fun p : Shao.Path n × LabelPerm n =>
        ∑ σ : LabelPerm n, if p.2 = σ then f p.1 σ else 0) := by
      apply Finset.measurable_sum
      intro σ _
      exact Measurable.ite (measurableSet_eq_fun
          (measurable_snd : Measurable (fun p : Shao.Path n × LabelPerm n => p.2))
          (measurable_const (a := σ)))
        ((hf σ).comp measurable_fst) measurable_const
    simpa only [he] using hm
  have hLi (r : ℕ) : Integrable (fun p : Shao.Path n × LabelPerm n =>
      sourceRetainedRemainder J F G p.1 x (ν p.1) r p.2) (revealLaw P) :=
    (integrable_const (1 + 6 * C * (1 + (n : ℝ)))).mono'
      (hJoint _ (fun σ => (hSections σ r).1)).aestronglyMeasurable
      (ae_of_all _ fun p => by
        simpa only [Real.norm_eq_abs] using
          (source_parts_uniform_bound J F G C hK p.1 x hx (ν p.1) r p.2).2)
  have hOi (r : ℕ) : Integrable (fun p : Shao.Path n × LabelPerm n =>
      sourceSeparatedOvershoot J G p.1 x (ν p.1) r p.2) (revealLaw P) :=
    (integrable_const (4 * C * (1 + (n : ℝ)))).mono'
      (hJoint _ (fun σ => (hSections σ r).2)).aestronglyMeasurable
      (ae_of_all _ fun p => by
        simpa only [Real.norm_eq_abs] using
          (source_parts_uniform_bound J F G C hK p.1 x hx (ν p.1) r p.2).1)
  exact ⟨hSections, fun r => ⟨hLi r,hOi r⟩,
    integrable_finsetSum (Finset.range n) (fun r _ => hLi r),
    integrable_finsetSum (Finset.range n) (fun r _ => hOi r)⟩

theorem source_separated_overshoot_sign_domination
    {n : ℕ} (P : Measure BridgeNoise) [IsProbabilityMeasure P]
    (G : MonitoredDomain → BridgeKernel)
    (hDeriv : ∀ (J : MonitoredDomain) (w y T z : ℝ),
      0 < w → 0 < T → Interior J w y → Interior J w z →
      HasDerivAt (fun s : ℝ => eventCompletionKernel J P (w, s, T, z))
        (G J (w, y, T, z)) y)
    (a : Shao.Path n) (x : ℝ) (hx : 0 < x)
    (ν : LabelPerm n → ℕ) (r : ℕ) (σ : LabelPerm n) :
    let Oplus : ℝ := sourceSeparatedOvershoot .upper (G .upper) a x ν r σ
    let Ominus : ℝ := sourceSeparatedOvershoot .lower (G .lower) a x ν r σ
    let Ointerval : ℝ := sourceSeparatedOvershoot .interval (G .interval) a x ν r σ
    0 ≤ Oplus ∧ 0 ≤ Ominus ∧ Ointerval ≤ Oplus + Ominus ∧
      max Ointerval 0 ≤ Oplus + Ominus ∧ 0 ≤ Oplus + Ominus - Ointerval := by
  classical
  intro Oplus Ominus Ointerval
  have hUpper (w y T z : ℝ) (hw : 0 < w) (hT : 0 < T) (hy : y < w) (hz : z < w) :
      G .upper (w,y,T,z) ≤ 0 := by
    have hm : Antitone (fun s : ℝ => upperCompletion P w s T z) := by
      intro s t hst
      apply measureReal_mono
      · intro g hg q
        exact (bridgePath_mono s t T z z hst le_rfl g q).trans_lt (hg q)
      · finiteness
    exact (hDeriv .upper w y T z hw hT hy hz).nonpos_of_antitone hm
  have hLower (w y T z : ℝ) (hw : 0 < w) (hT : 0 < T) (hy : -w < y) (hz : -w < z) :
      0 ≤ G .lower (w,y,T,z) := by
    have hm : Monotone (fun s : ℝ => lowerCompletion P w s T z) := by
      intro s t hst
      apply measureReal_mono
      · intro g hg q
        exact (hg q).trans_le (bridgePath_mono s t T z z hst le_rfl g q)
      · finiteness
    exact (hDeriv .lower w y T z hw hT hy hz).nonneg_of_monotone hm
  have hOne (J : MonitoredDomain) (η : ℝ)
      (hWhich : (J = .upper ∧ η = 1) ∨ (J = .lower ∧ η = -1)) :
      0 ≤ sourceSeparatedOvershoot J (G J) a x ν r σ := by
    by_cases hr : r < n
    · unfold sourceSeparatedOvershoot
      rw [dif_pos hr]
      by_cases hact : r < ν σ ∧ sourceAlive J a x r σ ∧ 0 < remainingEnergy a r σ
      · rw [if_pos hact]
        let w : ℝ := actualWall a x
        let y : ℝ := Shao.prefixSum (Spitzer.reorder a σ) r
        let T : ℝ := remainingEnergy a r σ
        let z : ℝ := Shao.prefixSum a n
        let b : ℝ := a (σ ⟨r,hr⟩)
        have hw : 0 < w := mul_pos hx (Real.sqrt_pos.2 hact.2.1.1)
        have hT : 0 < T := hact.2.2
        have hy : Interior J w y := hact.2.1.2.2 r le_rfl
        have hz : Interior J w z := hact.2.1.2.1
        have hη : η = 1 ∨ η = -1 := hWhich.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
        have hG : η * G J (w,y,T,z) ≤ 0 := by
          rcases hWhich with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · simpa only [one_mul] using hUpper w y T z hw hT hy hz
          · simpa only [neg_one_mul] using neg_nonpos.mpr (hLower w y T z hw hT hy hz)
        change 0 ≤ localSeparatedOvershoot J (G J) w y T z b
        by_cases hsmall : b ^ 2 ≤ T / 2
        · by_cases hcross : w ≤ η * (y + b)
          · have hc := projected_negative_part_control J P (G J) η w y T z b hη
              (Or.inr hWhich) hw hT hy hz hcross hsmall
            rcases hc with ⟨_,_,_,hδ,_,_,hc,_,heq,_⟩
            rw [heq]
            convert mul_nonneg (mul_nonneg hδ hc) (neg_nonneg.mpr hG) using 1 <;> ring
          · have hp : projectionIncrement J w y b = b := by
              rcases hWhich with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
              · have hn : ¬w ≤ y + b := by simpa only [one_mul] using hcross
                simp only [projectionIncrement,if_neg hn]
              · have hn : ¬y + b ≤ -w := by
                  intro hh
                  apply hcross
                  nlinarith only [hh]
                simp only [projectionIncrement,if_neg hn]
            rw [localSeparatedOvershoot,if_pos (show 0 < T ∧ b ^ 2 ≤ T / 2 from ⟨hT,hsmall⟩),hp]
            simp only [sub_self,neg_zero,zero_mul,le_refl]
        · rw [localSeparatedOvershoot,if_neg (by tauto)]
      · rw [if_neg hact]
    · simp only [sourceSeparatedOvershoot,dif_neg hr,le_refl]
  have hPlus : 0 ≤ Oplus := hOne .upper 1 (Or.inl ⟨rfl,rfl⟩)
  have hMinus : 0 ≤ Ominus := hOne .lower (-1) (Or.inr ⟨rfl,rfl⟩)
  have hComp : Ointerval ≤ Oplus + Ominus := by
    by_cases hr : r < n
    · by_cases hact : r < ν σ ∧ sourceAlive .interval a x r σ ∧ 0 < remainingEnergy a r σ
      · let w : ℝ := actualWall a x
        let y : ℝ := Shao.prefixSum (Spitzer.reorder a σ) r
        let T : ℝ := remainingEnergy a r σ
        let z : ℝ := Shao.prefixSum a n
        let b : ℝ := a (σ ⟨r,hr⟩)
        have hw : 0 < w := mul_pos hx (Real.sqrt_pos.2 hact.2.1.1)
        have hT : 0 < T := hact.2.2
        have hy : Interior .interval w y := hact.2.1.2.2 r le_rfl
        have hz : Interior .interval w z := hact.2.1.2.1
        by_cases hsmall : b ^ 2 ≤ T / 2
        · have hDom := signed_derivative_domination_of_hasDerivAt P w y T z
            (G .upper (w,y,T,z)) (G .interval (w,y,T,z)) (G .lower (w,y,T,z))
            (hDeriv .upper w y T z hw hT hy.2 hz.2)
            (hDeriv .interval w y T z hw hT hy hz)
            (hDeriv .lower w y T z hw hT hy.1 hz.1)
          have hAtWall (J : MonitoredDomain) (η : ℝ)
              (hWhich : (J = .upper ∧ η = 1) ∨ (J = .lower ∧ η = -1))
              (hcross : w ≤ η * (y + b)) :
              Ointerval ≤ sourceSeparatedOvershoot J (G J) a x ν r σ := by
            have hη : η = 1 ∨ η = -1 := hWhich.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
            have hLive : sourceAlive J a x r σ := by
              rcases hWhich with ⟨rfl,_⟩ | ⟨rfl,_⟩
              · exact ⟨hact.2.1.1,hact.2.1.2.1.2,
                  fun k hk => (hact.2.1.2.2 k hk).2⟩
              · exact ⟨hact.2.1.1,hact.2.1.2.1.1,
                  fun k hk => (hact.2.1.2.2 k hk).1⟩
            have hactJ : r < ν σ ∧ sourceAlive J a x r σ ∧ 0 < remainingEnergy a r σ :=
              ⟨hact.1,hLive,hact.2.2⟩
            have hyJ : Interior J w y := hLive.2.2 r le_rfl
            have hzJ : Interior J w z := hLive.2.1
            have hOrd : η * G J (w,y,T,z) ≤ η * G .interval (w,y,T,z) := by
              rcases hWhich with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
              · simpa only [one_mul] using hDom.1
              · simpa only [neg_one_mul] using neg_le_neg hDom.2
            have hI := projected_negative_part_control .interval P (G .interval) η w y T z b
              hη (Or.inl rfl) hw hT hy hz hcross hsmall
            have hJ := projected_negative_part_control J P (G J) η w y T z b
              hη (Or.inr hWhich) hw hT hyJ hzJ hcross hsmall
            rcases hI with ⟨_,_,_,hδ,_,_,hc,_,heI,_⟩
            rcases hJ with ⟨_,_,_,_,_,_,_,_,heJ,_⟩
            change sourceSeparatedOvershoot .interval (G .interval) a x ν r σ ≤ _
            simp only [sourceSeparatedOvershoot,dif_pos hr,if_pos hact,if_pos hactJ]
            change localSeparatedOvershoot .interval (G .interval) w y T z b ≤
              localSeparatedOvershoot J (G J) w y T z b
            rw [heI,heJ]
            have hh := neg_le_neg (mul_le_mul_of_nonneg_left hOrd (mul_nonneg hδ hc))
            convert hh using 1 <;> ring
          by_cases hu : w ≤ y + b
          · have hh := hAtWall .upper 1 (Or.inl ⟨rfl,rfl⟩) (by simpa only [one_mul] using hu)
            exact hh.trans (le_add_of_nonneg_right hMinus)
          · by_cases hl : y + b ≤ -w
            · have hh := hAtWall .lower (-1) (Or.inr ⟨rfl,rfl⟩) (by nlinarith only [hl])
              exact hh.trans (le_add_of_nonneg_left hPlus)
            · have hzO : Ointerval = 0 := by
                change sourceSeparatedOvershoot .interval (G .interval) a x ν r σ = 0
                simp only [sourceSeparatedOvershoot,dif_pos hr,if_pos hact]
                change localSeparatedOvershoot .interval (G .interval) w y T z b = 0
                rw [localSeparatedOvershoot,if_pos (show 0 < T ∧ b ^ 2 ≤ T / 2 from ⟨hT,hsmall⟩)]
                simp only [projectionIncrement,if_neg hu,if_neg hl,sub_self,neg_zero,zero_mul]
              rw [hzO]
              exact add_nonneg hPlus hMinus
        · have hzO : Ointerval = 0 := by
            change sourceSeparatedOvershoot .interval (G .interval) a x ν r σ = 0
            simp only [sourceSeparatedOvershoot,dif_pos hr,if_pos hact]
            exact if_neg (by tauto)
          rw [hzO]
          exact add_nonneg hPlus hMinus
      · have hzO : Ointerval = 0 := by
          change sourceSeparatedOvershoot .interval (G .interval) a x ν r σ = 0
          simp only [sourceSeparatedOvershoot,dif_pos hr,if_neg hact]
        rw [hzO]
        exact add_nonneg hPlus hMinus
    · simp only [Ointerval,Oplus,Ominus,sourceSeparatedOvershoot,dif_neg hr,zero_add,le_refl]
  exact ⟨hPlus,hMinus,hComp,max_le hComp (add_nonneg hPlus hMinus),sub_nonneg.mpr hComp⟩

theorem source_three_domain_overshoot_transfer
    {n : ℕ} (P : Measure (Shao.Path n)) [IsProbabilityMeasure P]
    (Q : Measure BridgeNoise) [IsProbabilityMeasure Q]
    (FY : MonitoredDomain → BridgeKernel)
    (hFYm : ∀ J, Measurable (FY J))
    (C : ℝ) (hC : 0 ≤ C)
    (hFYbound : ∀ (J : MonitoredDomain) (w y T z : ℝ),
      0 < w → 0 < T → Interior J w y → Interior J w z →
      |FY J (w, y, T, z)| ≤ C / Real.sqrt T * (1 + |z - y| / Real.sqrt T))
    (hDeriv : ∀ (J : MonitoredDomain) (w y T z : ℝ),
      0 < w → 0 < T → Interior J w y → Interior J w z →
      HasDerivAt (fun s : ℝ => eventCompletionKernel J Q (w, s, T, z))
        (FY J (w, y, T, z)) y)
    (x : ℝ) (hx : 0 < x) (H : ℝ) (hH : 0 < H)
    (ν : Shao.Path n → LabelPerm n → ℕ)
    (hνm : ∀ σ, Measurable (fun a => ν a σ))
    (hν : ∀ a, IsRevealStoppingRank (ν a))
    (hcap : ∀ a σ, ν a σ ≤ energyCutoff a H σ) :
    let F : MonitoredDomain → BridgeKernel := fun J => eventCompletionKernel J Q
    let L : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℕ → ℝ :=
      fun J p r => sourceRetainedRemainder J (F J) (FY J) p.1 x (ν p.1) r p.2
    let O : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℕ → ℝ :=
      fun J p r => sourceSeparatedOvershoot J (FY J) p.1 x (ν p.1) r p.2
    let Vstop : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ :=
      fun J p => sourceValue J (F J) p.1 x (ν p.1 p.2) p.2
    let Vinitial : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ :=
      fun J p => sourceValue J (F J) p.1 x 0 p.2
    let Afinal : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℝ :=
      fun J p => if sourceAlive J p.1 x n p.2 then 1 else 0
    ∀ B E G : ℝ,
      ((∫ p, ∑ r ∈ Finset.range n, |L .upper p r| ∂revealLaw P) +
        (∫ p, ∑ r ∈ Finset.range n, |L .lower p r| ∂revealLaw P) +
        (∫ p, ∑ r ∈ Finset.range n, |L .interval p r| ∂revealLaw P) +
        (∫ p, ∑ r ∈ Finset.range n, max (-O .interval p r) 0 ∂revealLaw P) ≤ B) →
      (∀ J : MonitoredDomain, (∫ p, |Vstop J p - Afinal J p| ∂revealLaw P) ≤ E) →
      (∀ J : MonitoredDomain, J = .upper ∨ J = .lower →
        |(∫ p, Afinal J p ∂revealLaw P) - (∫ p, Vinitial J p ∂revealLaw P)| ≤ G) →
      (∀ J : MonitoredDomain, J = .upper ∨ J = .lower →
        0 ≤ (∫ p, ∑ r ∈ Finset.range n, O J p r ∂revealLaw P) ∧
        (∫ p, ∑ r ∈ Finset.range n, O J p r ∂revealLaw P) ≤ B + E + G) ∧
      (∫ p, ∑ r ∈ Finset.range n,
        |if r < ν p.1 p.2 then sourceRemainder .interval (F .interval) (FY .interval)
          p.1 x r p.2 else 0| ∂revealLaw P) ≤ 3 * B + 2 * E + 2 * G ∧
      ∀ (m : Shao.Path n → ℝ), Measurable m → (∀ a, |m a| ≤ 1) →
        PermutationInvariant m →
        |(∫ p, m p.1 * (Afinal .interval p - Vinitial .interval p) ∂revealLaw P)| ≤
          3 * B + 3 * E + 2 * G := by
  classical
  intro F L O Vstop Vinitial Afinal B E G hBudget hTerminal hGap
  let μ : Measure (Shao.Path n × LabelPerm n) := revealLaw P
  letI : IsProbabilityMeasure μ := by dsimp only [μ, revealLaw]; infer_instance
  have hFd (J : MonitoredDomain) := eventCompletionKernel_data J Q
  have hK (J : MonitoredDomain) : KernelBounds J (F J) (FY J) C :=
    ⟨hC, fun w y T z _ _ _ _ => (hFd J).2.1 (w,y,T,z), hFYbound J⟩
  have hνbound (a : Shao.Path n) (σ : LabelPerm n) : ν a σ ≤ n := (hν a).1 σ
  have hParts (J : MonitoredDomain) := source_parts_measurable_integrable J (F J) (FY J)
    (hFd J).1 (hFYm J) C (hK J) P x hx ν hνm
  have hLi (J : MonitoredDomain) (r : ℕ) : Integrable (fun p => L J p r) μ :=
    ((hParts J).2.1 r).1
  have hOi (J : MonitoredDomain) (r : ℕ) : Integrable (fun p => O J p r) μ :=
    ((hParts J).2.1 r).2
  let LS (J : MonitoredDomain) (p : Shao.Path n × LabelPerm n) : ℝ :=
    ∑ r ∈ Finset.range n, L J p r
  let OS (J : MonitoredDomain) (p : Shao.Path n × LabelPerm n) : ℝ :=
    ∑ r ∈ Finset.range n, O J p r
  let LA (J : MonitoredDomain) (p : Shao.Path n × LabelPerm n) : ℝ :=
    ∑ r ∈ Finset.range n, |L J p r|
  let NN (p : Shao.Path n × LabelPerm n) : ℝ :=
    ∑ r ∈ Finset.range n, max (-O .interval p r) 0
  let RS (J : MonitoredDomain) (p : Shao.Path n × LabelPerm n) : ℝ :=
    stoppedRemainderSum J (F J) (FY J) p.1 x (ν p.1) p.2
  let RA (p : Shao.Path n × LabelPerm n) : ℝ :=
    ∑ r ∈ Finset.range n,
      |if r < ν p.1 p.2 then sourceRemainder .interval (F .interval) (FY .interval)
        p.1 x r p.2 else 0|
  have hLSi (J : MonitoredDomain) : Integrable (LS J) μ :=
    integrable_finsetSum _ (fun r _ => hLi J r)
  have hOSi (J : MonitoredDomain) : Integrable (OS J) μ :=
    integrable_finsetSum _ (fun r _ => hOi J r)
  have hLAi (J : MonitoredDomain) : Integrable (LA J) μ :=
    integrable_finsetSum _ (fun r _ => (hLi J r).abs)
  have hNNi : Integrable NN μ := by
    apply integrable_finsetSum
    intro r _
    have hi := ((hOi .interval r).abs.sub (hOi .interval r)).const_mul (1 / 2 : ℝ)
    apply hi.congr
    apply ae_of_all
    intro p
    change (1 / 2 : ℝ) * (|O .interval p r| - O .interval p r) = max (-O .interval p r) 0
    by_cases hp : 0 ≤ O .interval p r
    · rw [abs_of_nonneg hp, max_eq_right (neg_nonpos.mpr hp)]
      ring
    · have hp' : O .interval p r ≤ 0 := (lt_of_not_ge hp).le
      rw [abs_of_nonpos hp', max_eq_left (neg_nonneg.mpr hp')]
      ring
  have hSplit (J : MonitoredDomain) (p : Shao.Path n × LabelPerm n) (r : ℕ) :
      (if r < ν p.1 p.2 then sourceRemainder J (F J) (FY J) p.1 x r p.2 else 0) =
        L J p r + O J p r :=
    source_selected_remainder_decomposition J (F J) (FY J) p.1 x hx (ν p.1) r p.2
  have hRAi : Integrable RA μ := by
    apply integrable_finsetSum
    intro r _
    apply ((hLi .interval r).add (hOi .interval r)).abs.congr
    exact ae_of_all _ (fun p => congrArg abs (hSplit .interval p r).symm)
  have hVi (J : MonitoredDomain) :
      Integrable (Vstop J) μ ∧ Integrable (Vinitial J) μ ∧ Integrable (RS J) μ := by
    simpa only [one_mul] using
      source_stopped_integrability J (F J) (FY J) (hFd J).1 (hFYm J) C (hK J)
        P x hx ν hνm hνbound (fun _ => 1) measurable_const (fun _ => by norm_num)
  have hAeq (J : MonitoredDomain) (p : Shao.Path n × LabelPerm n) :
      sourceValue J (F J) p.1 x n p.2 = Afinal J p := by
    have hs : Shao.prefixSum (Spitzer.reorder p.1 p.2) n = Shao.prefixSum p.1 n := by
      simpa only [Shao.prefixSum_length, Spitzer.reorder] using Equiv.sum_comp p.2 p.1
    have he : Shao.energy (Spitzer.reorder p.1 p.2) = Shao.energy p.1 := by
      simpa only [Shao.energy, Spitzer.reorder] using
        Equiv.sum_comp p.2 (fun i => (p.1 i) ^ 2)
    have ht : remainingEnergy p.1 n p.2 = 0 := by
      rw [remainingEnergy, Shao.prefixSquares_length, he, sub_self]
    by_cases hlive : sourceAlive J p.1 x n p.2
    · have hw : 0 < actualWall p.1 x := mul_pos hx (Real.sqrt_pos.2 hlive.1)
      simp only [sourceValue, Afinal, hlive, ite_true]
      rw [hs, ht]
      rw [completionExt, if_pos ⟨hw, hlive.2.1, hlive.2.1⟩]
      norm_num
    · simp only [sourceValue, Afinal, hlive, ite_false]
  have hAi (J : MonitoredDomain) : Integrable (Afinal J) μ := by
    have hi := source_stopped_integrability J (F J) (FY J) (hFd J).1 (hFYm J) C (hK J)
      P x hx (fun _ _ => n) (fun _ => measurable_const) (fun _ _ => le_rfl)
      (fun _ => 1) measurable_const (fun _ => by norm_num)
    have hn : Integrable (fun p : Shao.Path n × LabelPerm n =>
        sourceValue J (F J) p.1 x n p.2) μ := by simpa only [one_mul] using hi.1
    exact hn.congr (ae_of_all _ (hAeq J))
  have hSumSplit (J : MonitoredDomain) : RS J = fun p => LS J p + OS J p := by
    funext p
    simp only [RS, stoppedRemainderSum, LS, OS, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun r _ => hSplit J p r)
  have hTel (J : MonitoredDomain) :
      (∫ p, Vstop J p ∂μ) - (∫ p, Vinitial J p ∂μ) =
        (∫ p, LS J p ∂μ) + (∫ p, OS J p ∂μ) := by
    have ht := source_masked_stopped_telescope_integral J (F J) (FY J)
      (hFd J).1 (hFYm J) C (hK J) P x hx H hH ν hνm hν hcap
      (fun _ => 1) measurable_const (fun _ => by norm_num)
    have ht' : (∫ p, Vstop J p ∂μ) - (∫ p, Vinitial J p ∂μ) =
        ∫ p, RS J p ∂μ := by simpa only [one_mul] using ht
    rw [hSumSplit, integral_add (hLSi J) (hOSi J)] at ht'
    exact ht'
  have hLA0 (J : MonitoredDomain) : 0 ≤ ∫ p, LA J p ∂μ :=
    integral_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hNN0 : 0 ≤ ∫ p, NN p ∂μ :=
    integral_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => le_max_right _ _))
  have hBud : (∫ p, LA .upper p ∂μ) + (∫ p, LA .lower p ∂μ) +
      (∫ p, LA .interval p ∂μ) + (∫ p, NN p ∂μ) ≤ B := hBudget
  have hBJ (J : MonitoredDomain) : (∫ p, LA J p ∂μ) ≤ B := by
    have hu := hLA0 .upper
    have hl := hLA0 .lower
    have hi := hLA0 .interval
    cases J <;> linarith only [hBud,hu,hl,hi,hNN0]
  have hBN : (∫ p, LA .interval p ∂μ) + (∫ p, NN p ∂μ) ≤ B := by
    linarith only [hBud,hLA0 .upper,hLA0 .lower]
  have hSign (p : Shao.Path n × LabelPerm n) (r : ℕ) :=
    source_separated_overshoot_sign_domination Q FY hDeriv p.1 x hx (ν p.1) r p.2
  have hWall (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower) :
      0 ≤ (∫ p, OS J p ∂μ) ∧ (∫ p, OS J p ∂μ) ≤ B + E + G := by
    have hOS0 : 0 ≤ (∫ p, OS J p ∂μ) := by
      apply integral_nonneg
      intro p
      apply Finset.sum_nonneg
      intro r _
      rcases hJ with rfl | rfl
      · exact (hSign p r).1
      · exact (hSign p r).2.1
    have hStopA : (∫ p, Vstop J p ∂μ) - (∫ p, Afinal J p ∂μ) ≤ E := by
      calc
        _ = ∫ p, Vstop J p - Afinal J p ∂μ := (integral_sub (hVi J).1 (hAi J)).symm
        _ ≤ ∫ p, |Vstop J p - Afinal J p| ∂μ :=
          integral_mono ((hVi J).1.sub (hAi J)) ((hVi J).1.sub (hAi J)).abs
            (fun _ => le_abs_self _)
        _ ≤ E := hTerminal J
    have hInitial : (∫ p, Afinal J p ∂μ) - (∫ p, Vinitial J p ∂μ) ≤ G :=
      (le_abs_self _).trans (hGap J hJ)
    have hNegL : -(∫ p, LS J p ∂μ) ≤ ∫ p, LA J p ∂μ := by
      calc
        _ = ∫ p, -LS J p ∂μ := (integral_neg _).symm
        _ ≤ ∫ p, LA J p ∂μ := integral_mono (hLSi J).neg (hLAi J) (fun p => by
          dsimp only [LS, LA]
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_le_sum (fun r _ => neg_le_abs _))
    exact ⟨hOS0, by linarith only [hTel J,hStopA,hInitial,hNegL,hBJ J]⟩
  have hRAp (p : Shao.Path n × LabelPerm n) :
      RA p ≤ LA .interval p + NN p + OS .upper p + OS .lower p := by
    calc
      _ ≤ ∑ r ∈ Finset.range n,
          (|L .interval p r| + max (-O .interval p r) 0 + O .upper p r + O .lower p r) := by
        apply Finset.sum_le_sum
        intro r _
        rw [hSplit]
        have ha : |O .interval p r| = max (O .interval p r) 0 + max (-O .interval p r) 0 := by
          by_cases hp : 0 ≤ O .interval p r
          · rw [abs_of_nonneg hp, max_eq_left hp, max_eq_right (neg_nonpos.mpr hp)]
            ring
          · have hp' : O .interval p r ≤ 0 := (lt_of_not_ge hp).le
            rw [abs_of_nonpos hp', max_eq_right hp', max_eq_left (neg_nonneg.mpr hp')]
            ring
        have ht := abs_add_le (L .interval p r) (O .interval p r)
        have hd := (hSign p r).2.2.2.1
        rw [ha] at ht
        linarith only [ht,hd]
      _ = _ := by simp only [LA, NN, OS, Finset.sum_add_distrib]
  have hRAb : (∫ p, RA p ∂μ) ≤ 3 * B + 2 * E + 2 * G := by
    calc
      _ ≤ ∫ p, LA .interval p + NN p + OS .upper p + OS .lower p ∂μ :=
        integral_mono hRAi ((((hLAi .interval).add hNNi).add (hOSi .upper)).add (hOSi .lower)) hRAp
      _ = (∫ p, LA .interval p ∂μ) + (∫ p, NN p ∂μ) +
          (∫ p, OS .upper p ∂μ) + (∫ p, OS .lower p ∂μ) := by
        have h1 := integral_add (((hLAi .interval).add hNNi).add (hOSi .upper)) (hOSi .lower)
        have h2 := integral_add ((hLAi .interval).add hNNi) (hOSi .upper)
        have h3 := integral_add (hLAi .interval) hNNi
        simp only [Pi.add_apply] at h1 h2 h3
        rw [h2, h3] at h1
        exact h1
      _ ≤ _ := by linarith only [hBN,(hWall .upper (Or.inl rfl)).2,(hWall .lower (Or.inr rfl)).2]
  refine ⟨hWall,hRAb,?_⟩
  intro m hmm hmb _hInvariant
  have hMV := source_stopped_integrability .interval (F .interval) (FY .interval)
    (hFd .interval).1 (hFYm .interval) C (hK .interval) P x hx ν hνm hνbound m hmm hmb
  have hMA : Integrable (fun p : Shao.Path n × LabelPerm n => m p.1 * Afinal .interval p) μ :=
    (hAi .interval).bdd_mul (hmm.comp measurable_fst).aestronglyMeasurable
      (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hmb p.1))
  have hErr : Integrable (fun p : Shao.Path n × LabelPerm n =>
      m p.1 * (Afinal .interval p - Vstop .interval p)) μ := by
    apply (hMA.sub hMV.1).congr
    exact ae_of_all _ (fun p => by
      change m p.1 * Afinal .interval p - m p.1 * Vstop .interval p =
        m p.1 * (Afinal .interval p - Vstop .interval p)
      ring)
  have ht := source_masked_stopped_telescope_integral .interval (F .interval) (FY .interval)
    (hFd .interval).1 (hFYm .interval) C (hK .interval) P x hx H hH ν hνm hν hcap m hmm hmb
  have hIdentity :
      (∫ p, m p.1 * (Afinal .interval p - Vinitial .interval p) ∂μ) =
        (∫ p, m p.1 * (Afinal .interval p - Vstop .interval p) ∂μ) +
        (∫ p, m p.1 * RS .interval p ∂μ) := by
    simp only [mul_sub]
    rw [integral_sub hMA hMV.2.1, integral_sub hMA hMV.1]
    linarith only [ht]
  have hErrBound :
      |∫ p, m p.1 * (Afinal .interval p - Vstop .interval p) ∂μ| ≤ E := by
    calc
      _ ≤ ∫ p, |m p.1 * (Afinal .interval p - Vstop .interval p)| ∂μ := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (μ := μ)
            (fun p => m p.1 * (Afinal .interval p - Vstop .interval p)))
      _ ≤ ∫ p, |Vstop .interval p - Afinal .interval p| ∂μ :=
        integral_mono hErr.abs ((hVi .interval).1.sub (hAi .interval)).abs (fun p => by
          rw [abs_mul, abs_sub_comm (Afinal .interval p) (Vstop .interval p)]
          exact mul_le_of_le_one_left (abs_nonneg _) (hmb p.1))
      _ ≤ E := hTerminal .interval
  have hRemBound : |∫ p, m p.1 * RS .interval p ∂μ| ≤ 3 * B + 2 * E + 2 * G := by
    calc
      _ ≤ ∫ p, |m p.1 * RS .interval p| ∂μ := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (μ := μ) (fun p => m p.1 * RS .interval p))
      _ ≤ ∫ p, RA p ∂μ := integral_mono hMV.2.2.abs hRAi (fun p => by
        rw [abs_mul]
        apply (mul_le_of_le_one_left (abs_nonneg _) (hmb p.1)).trans
        exact Finset.abs_sum_le_sum_abs _ _)
      _ ≤ _ := hRAb
  calc
    _ = |(∫ p, m p.1 * (Afinal .interval p - Vstop .interval p) ∂μ) +
        (∫ p, m p.1 * RS .interval p ∂μ)| := congrArg abs hIdentity
    _ ≤ |∫ p, m p.1 * (Afinal .interval p - Vstop .interval p) ∂μ| +
        |∫ p, m p.1 * RS .interval p ∂μ| := abs_add_le _ _
    _ ≤ E + (3 * B + 2 * E + 2 * G) := add_le_add hErrBound hRemBound
    _ = _ := by ring



end Shao.Probability.SourceSeparatedOvershoot
