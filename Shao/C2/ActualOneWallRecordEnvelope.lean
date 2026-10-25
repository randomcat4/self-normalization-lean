import Shao.Probability.SourceActualLocalProfileBudget
import Shao.C2.AuxiliaryMarkedDeletion
import Shao.C2.CompletedIntervalUpdate

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace Shao.C2.ActualOneWallRecordEnvelope
open Shao.Probability.SourcePermutationReveal
open Shao.Probability.SourceSeparatedOvershoot
open Shao.Probability.SourceActualLocalProfileBudget
open scoped BigOperators Classical

def oneWallSign (J : MonitoredDomain) : ℝ :=
  match J with
  | .lower => -1
  | _ => 1

def recordIncrement {n : ℕ} (J : MonitoredDomain) (a : Shao.Path n)
    (r : Fin n) (sigma : LabelPerm n) : ℝ :=
  let p : Shao.Path n := Shao.Probability.Spitzer.reorder a sigma
  max (oneWallSign J * Shao.prefixSum p (r.val + 1) -
    Shao.maxWithZero (oneWallSign J •
      Shao.Probability.Spitzer.head p r.val r.isLt.le)) 0

def recordStrip {n : ℕ} (J : MonitoredDomain) (a : Shao.Path n)
    (x : ℝ) (r : Fin n) (sigma : LabelPerm n) : Prop :=
  let F : ℝ := oneWallSign J *
    Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) (r.val + 1) -
      actualWall a x
  0 ≤ F ∧ F ≤ recordIncrement J a r sigma

def futureProfile {n : ℕ} (a : Shao.Path n) (j : ℕ)
    (sigma : LabelPerm n) : ℝ :=
  1 / Real.sqrt (remainingEnergy a j sigma) *
    (1 + |remainingSum a j sigma| / Real.sqrt (remainingEnergy a j sigma)) ^ 2

def ordinaryFutureWeight {n : ℕ} (a : Shao.Path n) (beta : ℝ)
    (j : ℕ) (sigma : LabelPerm n) : ℝ :=
  if 0 < remainingEnergy a j sigma ∧ 2 * beta ^ 2 ≤ remainingEnergy a j sigma
  then futureProfile a j sigma else 0

def badFutureWeight {n : ℕ} (a : Shao.Path n) (H : ℝ) (m : ℕ) (x : ℝ)
    (j : ℕ) (sigma : LabelPerm n) : ℝ :=
  if m ≤ n - j ∧ 0 < remainingEnergy a j sigma ∧
      H / 2 ≤ remainingEnergy a j sigma ∧
      Real.sqrt ((9 / 4 : ℝ) * x ^ 2 - 1) *
        Real.sqrt (remainingEnergy a j sigma) ≤ |remainingSum a j sigma|
  then futureProfile a j sigma else 0

def circularWitness {n : ℕ} (a : Shao.Path n) : ℝ :=
  if hn : 0 < n then
    sSup {w : ℝ | ∃ i : Fin n, ∃ k : Fin (n + 1),
      w = Shao.prefixSum a n -
        2 * ∑ q ∈ Finset.range k.val,
          a ⟨(i.val + q) % n, Nat.mod_lt _ hn⟩}
  else 0

def oppositePrefixHit {n : ℕ} (J : MonitoredDomain) (a : Shao.Path n)
    (x : ℝ) (r : Fin n) (sigma : LabelPerm n) : Prop :=
  ∃ k : ℕ, k ≤ r.val ∧
    oneWallSign J * Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) k ≤
      -actualWall a x

private theorem aoer_upper_local_record
    (w y T z b U d M : ℝ) (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2)
    (hU : T = b ^ 2 + U) (hd : z = y + b + d)
    (hy : y < w) (hz : z < w) (hM : M < w) :
    let D : ℝ := max (y + b - M) 0
    let F : ℝ := y + b - w
    let W : ℝ := 1 / Real.sqrt U * (1 + |d| / Real.sqrt U) ^ 2
    let O : ℝ := localSeparatedOvershoot .upper (halflineDerivative .upper) w y T z b
    0 ≤ O ∧ O ≤ if 0 ≤ F ∧ F ≤ D then 6 * D * W else 0 := by
  classical
  intro D F W O
  have hUpos : 0 < U := by nlinarith
  have hroot : 0 < Real.sqrt U := Real.sqrt_pos.mpr hUpos
  have hrootSq : (Real.sqrt U) ^ 2 = U := Real.sq_sqrt hUpos.le
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hD : 0 ≤ D := le_max_right _ _
  by_cases hcross : w ≤ y + b
  · let u : ℝ := w - y
    let v : ℝ := w - z
    let e : ℝ := y + b - w
    let c : ℝ := 1 - (b + u) * (z - y) / T
    let f : ℝ := 1 + |d| / Real.sqrt U
    have hu : 0 < u := sub_pos.mpr hy
    have hv : 0 < v := sub_pos.mpr hz
    have hub : u ≤ b := by dsimp only [u]; linarith
    have hb : 0 < b := hu.trans_le hub
    have he : 0 ≤ e := sub_nonneg.mpr hcross
    have heD : e ≤ D := by
      apply le_trans (b := y + b - M)
      · dsimp only [e]; linarith
      · exact le_max_left _ _
    have hStrip : 0 ≤ F ∧ F ≤ D := ⟨he, heD⟩
    have hc0 : 0 ≤ c := by
      dsimp only [c]
      apply sub_nonneg.mpr
      apply (div_le_one₀ hT).mpr
      have hgap : z - y ≤ u := by dsimp only [u]; linarith
      have hbu : 0 ≤ b + u := by linarith
      have hprod := mul_le_mul_of_nonneg_left hgap hbu
      have hsq := mul_nonneg (sub_nonneg.mpr hub) hbu
      have hlin := mul_nonneg hb.le (sub_nonneg.mpr hub)
      nlinarith
    have hcoeffFirst : c ≤ 1 + 2 * b * |d| / T := by
      have hbu : 0 ≤ b + u := by linarith
      have hprod := mul_le_mul_of_nonneg_left (neg_abs_le d) hbu
      have hdiff := mul_nonneg (abs_nonneg d) (sub_nonneg.mpr hub)
      have hpos := mul_nonneg hbu hb.le
      have hnum : -(2 * b * |d|) ≤ (b + u) * (z - y) := by
        rw [hd]
        nlinarith
      have hcEq : c = (T - (b + u) * (z - y)) / T := by
        dsimp only [c]
        rw [sub_div, div_self hT.ne']
      rw [hcEq]
      apply (div_le_iff₀ hT).mpr
      have hmul : (1 + 2 * b * |d| / T) * T = T + 2 * b * |d| := by
        rw [add_mul, one_mul, div_mul_cancel₀ _ hT.ne']
      rw [hmul]
      linarith
    have hbRoot : b ≤ Real.sqrt U := by nlinarith
    have hTge : U ≤ T := by nlinarith [sq_nonneg b]
    have hbRatio : b / T ≤ 1 / Real.sqrt U := by
      apply (div_le_div_iff₀ hT hroot).mpr
      have hp := mul_le_mul_of_nonneg_right hbRoot hroot.le
      nlinarith
    have hcoeff : c ≤ 3 * f := by
      have hratio := mul_le_mul_of_nonneg_left hbRatio
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg d))
      have hq : 0 ≤ |d| / Real.sqrt U := div_nonneg (abs_nonneg d) hroot.le
      have hcoeff' : c ≤ 1 + 2 * (|d| / Real.sqrt U) := by
        calc
          c ≤ 1 + 2 * b * |d| / T := hcoeffFirst
          _ = 1 + 2 * |d| * (b / T) := by ring
          _ ≤ 1 + 2 * |d| * (1 / Real.sqrt U) := add_le_add (le_refl (1 : ℝ)) hratio
          _ = 1 + 2 * (|d| / Real.sqrt U) := by ring
      dsimp only [f]
      linarith only [hcoeff', hq]
    have hvAbs : v ≤ |d| := by
      have hn := neg_abs_le d
      dsimp only [v, e] at *
      linarith
    have hvRatio : v / T ≤ |d| / U := by
      apply (div_le_div_iff₀ hT hUpos).mpr
      have hp := mul_le_mul_of_nonneg_right hvAbs hUpos.le
      have hq := mul_le_mul_of_nonneg_left hTge (abs_nonneg d)
      nlinarith
    have hfactor : |d| / U = (|d| / Real.sqrt U) / Real.sqrt U := by
      rw [div_div, ← pow_two, hrootSq]
    have hgap : 2 * v / T ≤ 2 * f / Real.sqrt U := by
      have hq : |d| / U ≤ f / Real.sqrt U := by
        rw [hfactor]
        apply (div_le_div_iff_of_pos_right hroot).mpr
        dsimp only [f]
        linarith
      have hh := hvRatio.trans hq
      calc
        2 * v / T = 2 * (v / T) := by ring
        _ ≤ 2 * (f / Real.sqrt U) := mul_le_mul_of_nonneg_left hh (by norm_num)
        _ = 2 * f / Real.sqrt U := by ring
    have hf : 0 ≤ f := by dsimp only [f]; positivity
    have hG : 0 ≤ 2 * v / T := by positivity
    have hExp : Real.exp (-2 * u * v / T) ≤ 1 := by
      have hp : 0 ≤ 2 * u * v / T := by positivity
      apply Real.exp_le_one_iff.mpr
      calc
        -2 * u * v / T = -(2 * u * v / T) := by ring
        _ ≤ 0 := neg_nonpos.mpr hp
    have hFormula : O = e * c * (2 * v / T) * Real.exp (-2 * u * v / T) := by
      dsimp only [O, localSeparatedOvershoot]
      rw [if_pos ⟨hT, hsmall⟩]
      simp only [projectionIncrement, if_pos hcross, halflineDerivative,
        Shao.C2.HalfLineMixedProfiles.slopeTime]
      dsimp only [e, c, u, v]
      ring
    have hO : 0 ≤ O := by rw [hFormula]; positivity
    refine ⟨hO, ?_⟩
    rw [if_pos hStrip]
    calc
      O = e * c * (2 * v / T) * Real.exp (-2 * u * v / T) := hFormula
      _ ≤ e * c * (2 * v / T) :=
        mul_le_of_le_one_right (mul_nonneg (mul_nonneg he hc0) hG) hExp
      _ ≤ e * (3 * f) * (2 * f / Real.sqrt U) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcoeff he) hgap hG
          (mul_nonneg he (mul_nonneg (by norm_num) hf))
      _ = 6 * e * W := by dsimp only [W, f]; ring
      _ ≤ 6 * D * W := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left heD (by norm_num)) hW
  · have hO : O = 0 := by
      dsimp only [O, localSeparatedOvershoot]
      rw [if_pos ⟨hT, hsmall⟩]
      simp only [projectionIncrement, if_neg hcross, sub_self, neg_zero, zero_mul]
    rw [hO]
    refine ⟨le_rfl, ?_⟩
    split_ifs <;> positivity

private theorem aoer_lower_local_reflection (w y T z b : ℝ) :
    localSeparatedOvershoot .lower (halflineDerivative .lower) w y T z b =
      localSeparatedOvershoot .upper (halflineDerivative .upper) w (-y) T (-z) (-b) := by
  classical
  simp only [localSeparatedOvershoot, neg_sq]
  by_cases hs : 0 < T ∧ b ^ 2 ≤ T / 2
  · simp only [if_pos hs]
    by_cases hc : y + b ≤ -w
    · have hc' : w ≤ -y + -b := by linarith
      simp only [projectionIncrement, if_pos hc, if_pos hc', halflineDerivative,
        Shao.C2.HalfLineMixedProfiles.slopeTime, sub_neg_eq_add]
      ring
    · have hc' : ¬w ≤ -y + -b := by linarith
      simp only [projectionIncrement, if_neg hc, if_neg hc', sub_self, neg_zero,
        zero_mul]
  · simp only [if_neg hs]

private theorem aoer_reveal_future_data
    {n : ℕ} (a : Shao.Path n) (r : Fin n) (sigma : LabelPerm n) :
    let p : Shao.Path n := Shao.Probability.Spitzer.reorder a sigma
    let j : ℕ := r.val + 1
    let tail : Shao.Path (n - j) :=
      Shao.Probability.Spitzer.tail p j (Nat.succ_le_of_lt r.isLt)
    Shao.prefixSum p j = Shao.prefixSum p r.val + a (sigma r) ∧
      remainingEnergy a r.val sigma = (a (sigma r)) ^ 2 + remainingEnergy a j sigma ∧
      remainingSum a r.val sigma = a (sigma r) + remainingSum a j sigma ∧
      Shao.energy tail = remainingEnergy a j sigma ∧
      Shao.prefixSum tail (n - j) = remainingSum a j sigma := by
  classical
  intro p j tail
  have hstep : Shao.prefixSum p j = Shao.prefixSum p r.val + a (sigma r) :=
    Shao.C2.CompletedIntervalUpdate.revealed_prefix_sum_step n a sigma r
  have hsq : Shao.prefixSquares p j =
      Shao.prefixSquares p r.val + (a (sigma r)) ^ 2 :=
    Shao.C2.CompletedIntervalUpdate.revealed_prefix_squares_step n a sigma r
  have htail (g : ℝ → ℝ) :
      (∑ i : Fin (n - j), g (tail i)) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => j ≤ i.val), g (p i) := by
    refine Finset.sum_bij
      (fun (i : Fin (n - j)) _ => (⟨j + i.val, by omega⟩ : Fin n)) ?_ ?_ ?_ ?_
    · intro i hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change j ≤ j + i.val
      omega
    · intro i hi k hk heq
      apply Fin.ext
      have hv := congrArg Fin.val heq
      dsimp only at hv
      omega
    · intro i hi
      have hij : j ≤ i.val := (Finset.mem_filter.mp hi).2
      let q : Fin (n - j) := ⟨i.val - j, by omega⟩
      refine ⟨q, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      dsimp only [q]
      omega
    · intro i hi
      rfl
  have hsplit (g : ℝ → ℝ) :
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < j), g (p i)) +
        (∑ i : Fin (n - j), g (tail i)) = ∑ i : Fin n, g (a i) := by
    rw [htail]
    have hh := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin n => i.val < j) (fun i => g (p i))
    simp only [not_lt] at hh
    rw [hh]
    exact Equiv.sum_comp sigma (fun i => g (a i))
  have hE : Shao.energy tail = remainingEnergy a j sigma := by
    have hh := hsplit (fun z => z ^ 2)
    change Shao.prefixSquares p j + Shao.energy tail = Shao.energy a at hh
    dsimp only [remainingEnergy]
    linarith
  have hS : Shao.prefixSum tail (n - j) = remainingSum a j sigma := by
    have hh := hsplit id
    change Shao.prefixSum p j + (∑ i, tail i) = ∑ i, a i at hh
    rw [Shao.prefixSum_length]
    dsimp only [remainingSum]
    rw [Shao.prefixSum_length]
    linarith
  refine ⟨hstep, ?_, ?_, hE, hS⟩
  · dsimp only [remainingEnergy]
    rw [hsq]
    ring
  · dsimp only [remainingSum]
    rw [hstep]
    ring

private theorem aoer_alive_signed_record
    {n : ℕ} (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower)
    (a : Shao.Path n) (x : ℝ) (r : Fin n) (sigma : LabelPerm n)
    (ha : sourceAlive J a x r.val sigma) :
    Shao.maxWithZero (oneWallSign J •
      Shao.Probability.Spitzer.head (Shao.Probability.Spitzer.reorder a sigma)
        r.val r.isLt.le) < actualWall a x := by
  classical
  unfold Shao.maxWithZero
  rw [Finset.sup'_lt_iff]
  intro k hk
  have hkr : k ≤ r.val := (Finset.mem_Icc.mp hk).2
  rw [Shao.prefixSum_smul,
    Shao.Probability.Spitzer.head_prefixSum _ r.val r.isLt.le k hkr]
  rcases hJ with rfl | rfl
  · simpa only [oneWallSign, one_mul, Interior] using ha.2.2 k hkr
  · have hh : -actualWall a x <
        Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) k := ha.2.2 k hkr
    simp only [oneWallSign, neg_one_mul]
    linarith

private theorem aoer_circular_prefix_witness
    {n : ℕ} (a : Shao.Path n) (hn : 0 < n) (k : ℕ) (hk : k ≤ n) :
    Shao.prefixSum a n - 2 * Shao.prefixSum a k ≤ circularWitness a := by
  classical
  let f : Fin n × Fin (n + 1) → ℝ := fun ik =>
    Shao.prefixSum a n - 2 * ∑ q ∈ Finset.range ik.2.val,
      a ⟨(ik.1.val + q) % n, Nat.mod_lt _ hn⟩
  have hset : {w : ℝ | ∃ i : Fin n, ∃ k : Fin (n + 1),
      w = Shao.prefixSum a n - 2 * ∑ q ∈ Finset.range k.val,
        a ⟨(i.val + q) % n, Nat.mod_lt _ hn⟩} = Set.range f := by
    ext w
    constructor
    · rintro ⟨i, k, rfl⟩
      exact ⟨(i, k), rfl⟩
    · rintro ⟨⟨i, k⟩, rfl⟩
      exact ⟨i, k, rfl⟩
  have hbounded : BddAbove {w : ℝ | ∃ i : Fin n, ∃ k : Fin (n + 1),
      w = Shao.prefixSum a n - 2 * ∑ q ∈ Finset.range k.val,
        a ⟨(i.val + q) % n, Nat.mod_lt _ hn⟩} := by
    rw [hset]
    exact (Set.finite_range f).bddAbove
  have hprefix : Shao.prefixSum a k =
      ∑ q ∈ Finset.range k, a ⟨(0 + q) % n, Nat.mod_lt _ hn⟩ := by
    unfold Shao.prefixSum
    refine Finset.sum_bij (fun i _ => i.val) ?_ ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
    · intro i hi j hj hij
      exact Fin.ext hij
    · intro q hq
      have hqk : q < k := Finset.mem_range.mp hq
      let i : Fin n := ⟨q, hqk.trans_le hk⟩
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqk⟩, rfl⟩
    · intro i hi
      congr 1
      apply Fin.ext
      simp only [zero_add, Nat.mod_eq_of_lt i.isLt]
  rw [circularWitness, dif_pos hn]
  rw [hprefix]
  exact le_csSup hbounded ⟨⟨0, hn⟩, ⟨k, Nat.lt_succ_of_le hk⟩, rfl⟩

private theorem aoer_source_record_profile
    {n : ℕ} (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower)
    (a : Shao.Path n) (x H : ℝ) (hx : 0 < x) (hH : 0 < H)
    (nu : LabelPerm n → ℕ) (r : Fin n) (sigma : LabelPerm n)
    (hcap : nu sigma ≤ energyCutoff a H sigma) :
    let O : ℝ := sourceSeparatedOvershoot J (halflineDerivative J) a x nu r.val sigma
    0 ≤ O ∧ O ≤
      if recordStrip J a x r sigma ∧ 0 < remainingEnergy a (r.val + 1) sigma ∧
          H / 2 ≤ remainingEnergy a (r.val + 1) sigma then
        6 * recordIncrement J a r sigma * futureProfile a (r.val + 1) sigma
      else 0 := by
  classical
  intro O
  let p : Shao.Path n := Shao.Probability.Spitzer.reorder a sigma
  let w : ℝ := actualWall a x
  let y : ℝ := Shao.prefixSum p r.val
  let T : ℝ := remainingEnergy a r.val sigma
  let z : ℝ := Shao.prefixSum a n
  let b : ℝ := a (sigma r)
  let U : ℝ := remainingEnergy a (r.val + 1) sigma
  let d : ℝ := remainingSum a (r.val + 1) sigma
  let s : ℝ := oneWallSign J
  let M : ℝ := Shao.maxWithZero (s • Shao.Probability.Spitzer.head p r.val r.isLt.le)
  have hD : 0 ≤ recordIncrement J a r sigma := le_max_right _ _
  have hW : 0 ≤ futureProfile a (r.val + 1) sigma := by
    dsimp only [futureProfile]
    positivity
  have hR : 0 ≤ (if recordStrip J a x r sigma ∧ 0 < U ∧ H / 2 ≤ U then
      6 * recordIncrement J a r sigma * futureProfile a (r.val + 1) sigma else 0) := by
    split_ifs <;> positivity
  by_cases hact : r.val < nu sigma ∧ sourceAlive J a x r.val sigma ∧ 0 < T
  swap
  · have hactRaw : ¬(r.val < nu sigma ∧ sourceAlive J a x r.val sigma ∧
        0 < remainingEnergy a r.val sigma) := hact
    have hz : O = 0 := by
      simp only [O, sourceSeparatedOvershoot, dif_pos r.isLt, if_neg hactRaw]
    simpa only [hz] using And.intro (le_refl (0 : ℝ)) hR
  have hactRaw : r.val < nu sigma ∧ sourceAlive J a x r.val sigma ∧
      0 < remainingEnergy a r.val sigma := hact
  by_cases hsmall : b ^ 2 ≤ T / 2
  swap
  · have hsmallRaw : ¬(0 < remainingEnergy a r.val sigma ∧
        (a (sigma r)) ^ 2 ≤ remainingEnergy a r.val sigma / 2) := by
      intro h
      exact hsmall h.2
    have hz : O = 0 := by
      simp only [O, sourceSeparatedOvershoot, dif_pos r.isLt, if_pos hactRaw,
        localSeparatedOvershoot, if_neg hsmallRaw]
    simpa only [hz] using And.intro (le_refl (0 : ℝ)) hR
  have hg := aoer_reveal_future_data a r sigma
  have hcut : r.val < energyCutoff a H sigma := hact.1.trans_le hcap
  have hTH : H ≤ T := ((energy_cutoff_data a H hH).2.2 sigma r.val hcut).2
  have hU : 0 < U := by nlinarith [hg.2.1]
  have hUH : H / 2 ≤ U := by nlinarith [hg.2.1]
  have hs2 : s ^ 2 = 1 := by
    rcases hJ with rfl | rfl <;> norm_num [s, oneWallSign]
  have hsabs : |s * d| = |d| := by
    rcases hJ with rfl | rfl <;> simp only [s, oneWallSign, one_mul, neg_one_mul, abs_neg]
  have hsmall' : (s * b) ^ 2 ≤ T / 2 := by
    simpa only [mul_pow, hs2, one_mul] using hsmall
  have hU' : T = (s * b) ^ 2 + U := by
    simpa only [mul_pow, hs2, one_mul] using hg.2.1
  have hd : s * z = s * y + s * b + s * d := by
    have hh : z = y + b + d := by
      dsimp only [remainingSum] at hg
      dsimp only [z, y, b, d, remainingSum]
      linarith [hg.1]
    rw [hh]
    ring
  have hy : s * y < w := by
    have hh := hact.2.1.2.2 r.val le_rfl
    rcases hJ with rfl | rfl
    · simpa only [s, oneWallSign, one_mul, Interior, w, y, p] using hh
    · change -w < y at hh
      simp only [s, oneWallSign, neg_one_mul]
      linarith
  have hz : s * z < w := by
    have hh := hact.2.1.2.1
    rcases hJ with rfl | rfl
    · simpa only [s, oneWallSign, one_mul, Interior, w, z] using hh
    · change -w < z at hh
      simp only [s, oneWallSign, neg_one_mul]
      linarith
  have hM : M < w := aoer_alive_signed_record J hJ a x r sigma hact.2.1
  have hlocal : O = localSeparatedOvershoot J (halflineDerivative J) w y T z b := by
    have hr : (⟨r.val, r.isLt⟩ : Fin n) = r := Fin.ext rfl
    simpa only [O, sourceSeparatedOvershoot, dif_pos r.isLt, if_pos hactRaw,
      w, y, p, T, z, b, hr]
  have hreflect : localSeparatedOvershoot J (halflineDerivative J) w y T z b =
      localSeparatedOvershoot .upper (halflineDerivative .upper) w (s * y) T (s * z) (s * b) := by
    rcases hJ with rfl | rfl
    · simp only [s, oneWallSign, one_mul]
    · simpa only [s, oneWallSign, neg_one_mul] using aoer_lower_local_reflection w y T z b
  have hscalar := aoer_upper_local_record w (s * y) T (s * z) (s * b) U (s * d) M
    hact.2.2 hsmall' hU' hd hy hz hM
  have hDval : max (s * y + s * b - M) 0 = recordIncrement J a r sigma := by
    dsimp only [recordIncrement]
    rw [hg.1]
    congr 1
    dsimp only [s, y, b, M, p]
    ring
  have hFval : s * y + s * b - w = s * Shao.prefixSum p (r.val + 1) - w := by
    rw [hg.1]
    dsimp only [y, b]
    ring
  have hbase : 0 ≤ O ∧ O ≤
      if recordStrip J a x r sigma then
        6 * recordIncrement J a r sigma * futureProfile a (r.val + 1) sigma else 0 := by
    dsimp only at hscalar
    rw [← hreflect, ← hlocal, hDval, hFval, hsabs] at hscalar
    refine ⟨hscalar.1, ?_⟩
    by_cases hstrip : recordStrip J a x r sigma
    · have hstrip' : 0 ≤ s * Shao.prefixSum p (r.val + 1) - w ∧
          s * Shao.prefixSum p (r.val + 1) - w ≤ recordIncrement J a r sigma := by
        simpa only [recordStrip, s, p, w] using hstrip
      rw [if_pos hstrip]
      simpa only [if_pos hstrip', futureProfile, U, d] using hscalar.2
    · have hstrip' : ¬(0 ≤ s * Shao.prefixSum p (r.val + 1) - w ∧
          s * Shao.prefixSum p (r.val + 1) - w ≤ recordIncrement J a r sigma) := by
        simpa only [recordStrip, s, p, w] using hstrip
      rw [if_neg hstrip]
      simpa only [if_neg hstrip'] using hscalar.2
  refine ⟨hbase.1, ?_⟩
  have hUraw : 0 < remainingEnergy a (r.val + 1) sigma := hU
  have hUHraw : H / 2 ≤ remainingEnergy a (r.val + 1) sigma := hUH
  simpa only [hUraw, hUHraw, and_true] using hbase.2

private theorem aoer_nonzero_crossing
    {n : ℕ} (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower)
    (a : Shao.Path n) (x : ℝ) (nu : LabelPerm n → ℕ)
    (r : Fin n) (sigma : LabelPerm n)
    (hO : sourceSeparatedOvershoot J (halflineDerivative J) a x nu r.val sigma ≠ 0) :
    actualWall a x ≤ oneWallSign J *
      Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) (r.val + 1) := by
  classical
  have hs := (aoer_reveal_future_data a r sigma).1
  by_contra hc
  rcases hJ with rfl | rfl
  · have hnc : ¬actualWall a x ≤
        Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) r.val + a (sigma r) := by
      intro hh
      apply hc
      simpa only [oneWallSign, one_mul, hs] using hh
    apply hO
    simp [sourceSeparatedOvershoot, r.isLt, localSeparatedOvershoot, projectionIncrement, hnc]
  · have hnc : ¬Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) r.val +
        a (sigma r) ≤ -actualWall a x := by
      intro hh
      apply hc
      simp only [oneWallSign, neg_one_mul, hs]
      linarith
    apply hO
    simp [sourceSeparatedOvershoot, r.isLt, localSeparatedOvershoot, projectionIncrement, hnc]

private theorem aoer_bad_future_guards
    {n : ℕ} (a : Shao.Path n) (x H : ℝ) (hx : 1 ≤ x) (hH : 0 < H)
    (m : ℕ) (hm : m ≤ n) (nu : LabelPerm n → ℕ)
    (r : Fin n) (sigma : LabelPerm n)
    (hcap : nu sigma ≤ min (energyCutoff a H sigma) (n - m))
    (hactive : r.val < nu sigma)
    (hsmall : (a (sigma r)) ^ 2 ≤ remainingEnergy a r.val sigma / 2)
    (hBad : 3 * x * Real.sqrt (remainingEnergy a r.val sigma) / 2 ≤
      |remainingSum a r.val sigma|) :
    m ≤ n - (r.val + 1) ∧ 0 < remainingEnergy a (r.val + 1) sigma ∧
      H / 2 ≤ remainingEnergy a (r.val + 1) sigma ∧
      Real.sqrt ((9 / 4 : ℝ) * x ^ 2 - 1) *
        Real.sqrt (remainingEnergy a (r.val + 1) sigma) ≤
          |remainingSum a (r.val + 1) sigma| := by
  classical
  have hcut : r.val < energyCutoff a H sigma :=
    hactive.trans_le (hcap.trans (min_le_left _ _))
  have hdata := (energy_cutoff_data a H hH).2.2 sigma r.val hcut
  have ht : r.val < n - m := hactive.trans_le (hcap.trans (min_le_right _ _))
  have hlength : m ≤ n - (r.val + 1) := by omega
  let j : ℕ := r.val + 1
  let tail : Shao.Path (n - j) := Shao.Probability.Spitzer.tail
    (Shao.Probability.Spitzer.reorder a sigma) j (Nat.succ_le_of_lt r.isLt)
  have hg := aoer_reveal_future_data a r sigma
  change _ ∧ _ ∧ _ ∧ Shao.energy tail = remainingEnergy a j sigma ∧
    Shao.prefixSum tail (n - j) = remainingSum a j sigma at hg
  have hU : 0 < remainingEnergy a j sigma := by
    nlinarith [hg.2.1, hdata.2]
  have hUH : H / 2 ≤ remainingEnergy a j sigma := by
    nlinarith [hg.2.1, hdata.2]
  have hFull : 0 < (a (sigma r)) ^ 2 + Shao.energy tail := by
    rw [hg.2.2.2.1, ← hg.2.1]
    exact hH.trans_le hdata.2
  have hCross : (3 / 2 : ℝ) * x *
      Real.sqrt ((a (sigma r)) ^ 2 + Shao.energy tail) ≤
        |a (sigma r) + Shao.prefixSum tail (n - j)| := by
    rw [hg.2.2.2.1, ← hg.2.1, hg.2.2.2.2, ← hg.2.2.1]
    convert hBad using 1 <;> ring
  have hDeleted := Shao.C2.AuxiliaryMarkedDeletion.auxiliary_marked_terminal_deletion
    tail (a (sigma r)) x hx hFull hCross
  refine ⟨hlength, hU, hUH, ?_⟩
  simpa only [hg.2.2.2.1, hg.2.2.2.2, j] using hDeleted.2

theorem actual_onewall_record_envelope
    {n : ℕ} (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower)
    (a : Shao.Path n) (x beta : ℝ) (hx : 0 < x) (hbeta : 0 < beta)
    (nu : LabelPerm n → ℕ) (r : Fin n) (sigma : LabelPerm n)
    (hcap : nu sigma ≤ energyCutoff a (4 * beta ^ 2) sigma) :
    let O : ℝ := sourceSeparatedOvershoot J (halflineDerivative J) a x nu r.val sigma
    0 ≤ O ∧ O ≤
      if recordStrip J a x r sigma then
        6 * recordIncrement J a r sigma * ordinaryFutureWeight a beta (r.val + 1) sigma
      else 0 := by
  classical
  intro O
  have hp : 0 < 4 * beta ^ 2 := by positivity
  have hb := aoer_source_record_profile J hJ a x (4 * beta ^ 2) hx hp nu r sigma hcap
  have hhalf : 4 * beta ^ 2 / 2 = 2 * beta ^ 2 := by ring
  have heq :
      (if recordStrip J a x r sigma ∧ 0 < remainingEnergy a (r.val + 1) sigma ∧
          (4 * beta ^ 2) / 2 ≤ remainingEnergy a (r.val + 1) sigma then
        6 * recordIncrement J a r sigma * futureProfile a (r.val + 1) sigma else 0) =
      (if recordStrip J a x r sigma then
        6 * recordIncrement J a r sigma * ordinaryFutureWeight a beta (r.val + 1) sigma else 0) := by
    rw [hhalf]
    by_cases hs : recordStrip J a x r sigma
    · by_cases hg : 0 < remainingEnergy a (r.val + 1) sigma ∧
          2 * beta ^ 2 ≤ remainingEnergy a (r.val + 1) sigma
      · simp only [hs, true_and, hg, ite_true, ordinaryFutureWeight]
      · simp only [hs, true_and, hg, ite_false, ordinaryFutureWeight, mul_zero, ite_true]
    · simp only [hs, false_and, ite_false]
  exact ⟨hb.1, heq ▸ hb.2⟩

theorem actual_onewall_prior_hit_record_envelope
    {n : ℕ} (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower)
    (a : Shao.Path n) (x beta : ℝ) (hx : 0 < x) (hbeta : 0 < beta)
    (nu : LabelPerm n → ℕ) (r : Fin n) (sigma : LabelPerm n)
    (hcap : nu sigma ≤ energyCutoff a (4 * beta ^ 2) sigma) :
    let O : ℝ := sourceSeparatedOvershoot J (halflineDerivative J) a x nu r.val sigma
    let p : Shao.Path (r.val + 1) := oneWallSign J •
      Shao.Probability.Spitzer.head (Shao.Probability.Spitzer.reorder a sigma)
        (r.val + 1) (Nat.succ_le_of_lt r.isLt)
    (if oppositePrefixHit J a x r sigma then O else 0) ≤
      if recordStrip J a x r sigma ∧ 3 * actualWall a x ≤ circularWitness p then
        6 * recordIncrement J a r sigma * ordinaryFutureWeight a beta (r.val + 1) sigma
      else 0 := by
  classical
  intro O p
  have hb := actual_onewall_record_envelope J hJ a x beta hx hbeta nu r sigma hcap
  have hD : 0 ≤ recordIncrement J a r sigma := le_max_right _ _
  have hW : 0 ≤ ordinaryFutureWeight a beta (r.val + 1) sigma := by
    unfold ordinaryFutureWeight
    split_ifs
    · dsimp only [futureProfile]
      positivity
    · exact le_refl 0
  have hR : 0 ≤ (if recordStrip J a x r sigma ∧ 3 * actualWall a x ≤ circularWitness p then
      6 * recordIncrement J a r sigma * ordinaryFutureWeight a beta (r.val + 1) sigma else 0) := by
    split_ifs <;> positivity
  by_cases hop : oppositePrefixHit J a x r sigma
  swap
  · simpa only [if_neg hop] using hR
  rw [if_pos hop]
  by_cases hzero : O = 0
  · simpa only [hzero] using hR
  have hcross := aoer_nonzero_crossing J hJ a x nu r sigma hzero
  obtain ⟨k, hk, hh⟩ := hop
  have hprefix (ell : ℕ) (hell : ell ≤ r.val + 1) :
      Shao.prefixSum p ell = oneWallSign J *
        Shao.prefixSum (Shao.Probability.Spitzer.reorder a sigma) ell := by
    dsimp only [p]
    rw [Shao.prefixSum_smul,
      Shao.Probability.Spitzer.head_prefixSum _ (r.val + 1) (Nat.succ_le_of_lt r.isLt) ell hell]
  have hwitness : 3 * actualWall a x ≤ circularWitness p := by
    have hw := aoer_circular_prefix_witness p (Nat.succ_pos _) k (by omega)
    rw [hprefix _ le_rfl, hprefix _ (by omega)] at hw
    linarith
  simpa only [hwitness, and_true] using hb.2

theorem actual_onewall_bad_future_record_envelope
    {n : ℕ} (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower)
    (a : Shao.Path n) (x beta H : ℝ) (hx : 1 ≤ x) (hbeta : 0 < beta)
    (hH : 4 * beta ^ 2 ≤ H) (m : ℕ) (hm : m ≤ n)
    (nu : LabelPerm n → ℕ) (r : Fin n) (sigma : LabelPerm n)
    (hcap : nu sigma ≤ min (energyCutoff a H sigma) (n - m)) :
    let O : ℝ := sourceSeparatedOvershoot J (halflineDerivative J) a x nu r.val sigma
    let Bad : Prop := 3 * x * Real.sqrt (remainingEnergy a r.val sigma) / 2 ≤
      |remainingSum a r.val sigma|
    0 ≤ (if Bad then O else 0) ∧
      (if Bad then O else 0) ≤
        if recordStrip J a x r sigma then
          6 * recordIncrement J a r sigma * badFutureWeight a H m x (r.val + 1) sigma
        else 0 := by
  classical
  intro O Bad
  have hHpos : 0 < H := lt_of_lt_of_le (by positivity : 0 < 4 * beta ^ 2) hH
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hb := aoer_source_record_profile J hJ a x H hxpos hHpos nu r sigma
    (hcap.trans (min_le_left _ _))
  have hD : 0 ≤ recordIncrement J a r sigma := le_max_right _ _
  have hW : 0 ≤ badFutureWeight a H m x (r.val + 1) sigma := by
    unfold badFutureWeight
    split_ifs
    · dsimp only [futureProfile]
      positivity
    · exact le_refl 0
  have hR : 0 ≤ (if recordStrip J a x r sigma then
      6 * recordIncrement J a r sigma * badFutureWeight a H m x (r.val + 1) sigma else 0) := by
    split_ifs <;> positivity
  by_cases hbad : Bad
  swap
  · simpa only [if_neg hbad] using And.intro (le_refl (0 : ℝ)) hR
  simp only [if_pos hbad]
  refine ⟨hb.1, ?_⟩
  by_cases hzero : O = 0
  · simpa only [hzero] using hR
  have hact : r.val < nu sigma ∧ sourceAlive J a x r.val sigma ∧
      0 < remainingEnergy a r.val sigma := by
    by_contra hn
    apply hzero
    simp only [O, sourceSeparatedOvershoot, dif_pos r.isLt, if_neg hn]
  have hsmall : (a (sigma r)) ^ 2 ≤ remainingEnergy a r.val sigma / 2 := by
    by_contra hn
    apply hzero
    simp only [O, sourceSeparatedOvershoot, dif_pos r.isLt, if_pos hact,
      localSeparatedOvershoot, if_neg (show ¬(0 < remainingEnergy a r.val sigma ∧
        (a (sigma r)) ^ 2 ≤ remainingEnergy a r.val sigma / 2) from fun h => hn h.2)]
  have hg := aoer_bad_future_guards a x H hx hHpos m hm nu r sigma hcap hact.1 hsmall hbad
  rw [badFutureWeight, if_pos hg]
  simpa only [hg.2.1, hg.2.2.1, and_true] using hb.2

end Shao.C2.ActualOneWallRecordEnvelope
