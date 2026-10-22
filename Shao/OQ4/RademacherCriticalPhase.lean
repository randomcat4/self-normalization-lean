/-
LOCAL_IMPLEMENTATION_V1; see author receipt for native-check status.
Exact public interface: frozen-rademacher-critical-phase-formal-statements-v2.lean.txt
SHA256 d2656efb76cbbdba2ad08bc9352b05270461e466aec8a94d09b9dca0ed60a4bc
Deterministic CP0--CP3 only; all additional declarations are private.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

open Filter
open scoped Topology
noncomputable section

namespace Shao.OQ4.RademacherCriticalPhase

def root (n : ℕ) : ℝ := Real.rpow (n : ℝ) ((1 : ℝ) / 3)
def height (c : ℝ) (n : ℕ) : ℝ := c * root n
def phaseFloor (c : ℝ) (n : ℕ) : ℕ := Nat.floor (height c n)
def upperHeight (c : ℝ) (n : ℕ) : ℝ := (phaseFloor c n : ℝ) + 1
def delta (c : ℝ) (n : ℕ) : ℝ := upperHeight c n - height c n
def q (c : ℝ) : ℝ := Real.pi ^ 2 / (4 * c ^ 3)
def exponent (c : ℝ) (n : ℕ) : ℝ := q c * delta c n
def factor (c : ℝ) (n : ℕ) : ℝ := Real.exp (exponent c n)
def cutoff (c : ℝ) : ℕ := max 1 (Nat.ceil (1 / c ^ 3))

def WeakCell (c : ℝ) (n : ℕ) : Prop :=
  1 ≤ height c n ∧ 1 ≤ phaseFloor c n ∧
  (phaseFloor c n : ℝ) ≤ height c n ∧ height c n < upperHeight c n ∧
  upperHeight c n = height c n + delta c n ∧ 0 < delta c n ∧ delta c n ≤ 1

def Cluster (z : ℕ → ℝ) : Set ℝ :=
  {L | ∃ σ : ℕ → ℕ, StrictMono σ ∧ Tendsto (fun j => z (σ j)) atTop (𝓝 L)}

def target (c β : ℝ) (k : ℕ) : ℝ := (((k : ℝ) + β) / c) ^ 3
def upIndex (c : ℝ) (k : ℕ) : ℕ := Nat.ceil (target c 0 k)
def downIndex (c : ℝ) (k : ℕ) : ℕ := Nat.ceil (target c 0 k) - 1
def nearestIndex (c α : ℝ) (k : ℕ) : ℕ := Nat.floor (target c α k + (1 : ℝ) / 2)
def cubeIndex (k : ℕ) : ℕ := k ^ 3
def belowCubeIndex (k : ℕ) : ℕ := k ^ 3 - 1

def phaseIndex (c d : ℝ) (k : ℕ) : ℕ :=
  letI : DecidableEq ℝ := Classical.decEq ℝ
  if d = 0 then downIndex c k
  else if d = 1 then upIndex c k
  else nearestIndex c (1 - d) k

private theorem aux_cube_strict {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) : x ^ 3 < y ^ 3 := by
  have hy : 0 < y := lt_of_le_of_lt hx hxy
  have hQ : 0 < y ^ 2 + y * x + x ^ 2 := by positivity
  have hp := mul_pos (sub_pos.mpr hxy) hQ
  nlinarith

private theorem aux_cube_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : x ^ 3 ≤ y ^ 3 := by
  rcases lt_or_eq_of_le hxy with h | h
  · exact (aux_cube_strict hx h).le
  · rw [h]

private theorem aux_cube_le_inv {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ^ 3 ≤ y ^ 3) : x ≤ y := by
  by_contra hn
  have hh := aux_cube_strict hy (lt_of_not_ge hn)
  linarith

private theorem aux_cube_lt_inv {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ^ 3 < y ^ 3) : x < y := by
  by_contra hn
  have hh := aux_cube_mono hy (le_of_not_gt hn)
  linarith

private theorem aux_cube_injective_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ^ 3 = y ^ 3) : x = y :=
  le_antisymm (aux_cube_le_inv hx hy h.le) (aux_cube_le_inv hy hx h.ge)

private theorem aux_root_nonneg (n : ℕ) : 0 ≤ root n :=
  Real.rpow_nonneg (Nat.cast_nonneg n) _

private theorem aux_root_zero : root 0 = 0 := by
  simp [root]

private theorem aux_root_cube (n : ℕ) : root n ^ 3 = (n : ℝ) := by
  change ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (n : ℝ)
  calc
    ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 =
        (n : ℝ) ^ (((1 : ℝ) / 3) * (3 : ℕ)) :=
      (Real.rpow_mul_natCast (Nat.cast_nonneg n) ((1 : ℝ) / 3) 3).symm
    _ = (n : ℝ) := by norm_num

private theorem aux_root_pos {n : ℕ} (hn : 1 ≤ n) : 0 < root n := by
  apply Real.rpow_pos_of_pos
  exact_mod_cast (show 0 < n by omega)

private theorem aux_height_zero (c : ℝ) : height c 0 = 0 := by simp [height, aux_root_zero]

private theorem aux_height_nonneg {c : ℝ} (hc : 0 < c) (n : ℕ) : 0 ≤ height c n :=
  mul_nonneg hc.le (aux_root_nonneg n)

private theorem aux_height_pos {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) : 0 < height c n :=
  mul_pos hc (aux_root_pos hn)

private theorem aux_height_cube (c : ℝ) (n : ℕ) : height c n ^ 3 = c ^ 3 * (n : ℝ) := by
  simp [height, mul_pow, aux_root_cube]

private theorem aux_nat_floor_bounds {x : ℝ} (hx : 0 ≤ x) :
    (Nat.floor x : ℝ) ≤ x ∧ x < (Nat.floor x : ℝ) + 1 :=
  ⟨Nat.floor_le hx, Nat.lt_floor_add_one x⟩

private theorem aux_nat_floor_agrees_int {x : ℝ} (hx : 0 ≤ x) :
    (Nat.floor x : ℤ) = Int.floor x := by
  symm
  apply Int.floor_eq_iff.mpr
  simpa only [Int.cast_natCast] using aux_nat_floor_bounds hx

private theorem aux_nat_ceil_error {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (Nat.ceil x : ℝ) - x ∧ (Nat.ceil x : ℝ) - x < 1 := by
  have h₁ := Nat.le_ceil x
  have h₂ := Nat.ceil_lt_add_one hx
  constructor <;> linarith

private theorem aux_delta_range {c : ℝ} (hc : 0 < c) (n : ℕ) :
    0 < delta c n ∧ delta c n ≤ 1 := by
  have h := aux_nat_floor_bounds (aux_height_nonneg hc n)
  change 0 < (phaseFloor c n : ℝ) + 1 - height c n ∧
    (phaseFloor c n : ℝ) + 1 - height c n ≤ 1
  dsimp [phaseFloor]
  constructor <;> linarith

private theorem aux_zero_prefix (c : ℝ) :
    height c 0 = 0 ∧ phaseFloor c 0 = 0 ∧ upperHeight c 0 = 1 ∧ delta c 0 = 1 := by
  simp [aux_height_zero, phaseFloor, upperHeight, delta]

private theorem aux_delta_of_nat_height {c : ℝ} {n l : ℕ} (h : height c n = (l : ℝ)) :
    delta c n = 1 := by
  simp [delta, upperHeight, phaseFloor, h]

private theorem aux_cutoff_pos (c : ℝ) : 1 ≤ cutoff c := le_max_left _ _

private theorem aux_weakCell_of_cutoff {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : cutoff c ≤ n) :
    WeakCell c n := by
  have hc3 : 0 < c ^ 3 := pow_pos hc _
  have hnceil : Nat.ceil (1 / c ^ 3) ≤ n := le_trans (le_max_right _ _) hn
  have hnreal : (1 : ℝ) / c ^ 3 ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hnceil)
  have hh3 : 1 ≤ height c n ^ 3 := by
    rw [aux_height_cube]
    have ht := (div_le_iff₀ hc3).mp hnreal
    nlinarith
  have hh : 1 ≤ height c n := aux_cube_le_inv (by norm_num) (aux_height_nonneg hc n) (by simpa using hh3)
  have hm : 1 ≤ phaseFloor c n := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hz
    have hlt : height c n < 1 := Nat.floor_eq_zero.mp hz
    linarith
  have hf := aux_nat_floor_bounds (aux_height_nonneg hc n)
  have hd := aux_delta_range hc n
  refine ⟨hh, hm, hf.1, hf.2, ?_, hd.1, hd.2⟩
  dsimp [delta]
  ring

private theorem aux_time_scale {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) / height c n ^ 3 = 1 / c ^ 3 ∧ 0 < 1 / c ^ 3 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  constructor
  · rw [aux_height_cube]
    field_simp [hc.ne', hnR.ne']
  · positivity

private theorem aux_zero_time_scale (c : ℝ) : (0 : ℝ) / height c 0 ^ 3 = 0 := by simp

private theorem aux_square_scale {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) / height c n ^ 2 = height c n / c ^ 3 := by
  have hh := aux_height_pos hc hn
  have heq := aux_height_cube c n
  field_simp [hc.ne', hh.ne']
  nlinarith [heq]

private theorem aux_height_tendsto_atTop {c : ℝ} (hc : 0 < c) : Tendsto (height c) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro B
  let A : ℝ := max B 0 + 1
  have hA : 0 < A := by dsimp [A]; linarith [le_max_right B 0]
  have hc3 : 0 < c ^ 3 := pow_pos hc _
  obtain ⟨N, hN⟩ := exists_nat_gt (A ^ 3 / c ^ 3)
  refine eventually_atTop.mpr ⟨N, ?_⟩
  intro n hn
  have hnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hp : A ^ 3 < height c n ^ 3 := by
    rw [aux_height_cube]
    have ht := (div_lt_iff₀ hc3).mp hN
    have hm := mul_le_mul_of_nonneg_left hnR hc3.le
    nlinarith
  have hh := aux_cube_lt_inv hA.le (aux_height_nonneg hc n) hp
  dsimp [A] at hh
  linarith [le_max_left B 0]

private theorem aux_square_scale_tendsto_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) / height c n ^ 2) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro B
  have hev := (Filter.tendsto_atTop.mp (aux_height_tendsto_atTop hc))
    (c ^ 3 * (max B 0 + 1))
  filter_upwards [hev, eventually_ge_atTop (1 : ℕ)] with n hh hn
  rw [aux_square_scale hc hn]
  apply (le_div_iff₀ (pow_pos hc 3)).mpr
  have hB : B ≤ max B 0 + 1 := by linarith [le_max_left B 0]
  have hm := mul_le_mul_of_nonneg_left hB (pow_pos hc 3).le
  nlinarith

private theorem aux_strict_index_id_le {σ : ℕ → ℕ} (hσ : StrictMono σ) (j : ℕ) : j ≤ σ j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hσ (Nat.lt_succ_self j)))

private theorem aux_target_cube {c : ℝ} (hc : 0 < c) (β : ℝ) (k : ℕ) :
    c ^ 3 * target c β k = ((k : ℝ) + β) ^ 3 := by
  rw [target, div_pow]
  field_simp [hc.ne'] <;> ring

private theorem aux_inverse_square_zero {g : ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (hb : ∀ k, 1 ≤ k → |g k| ≤ C / (k : ℝ) ^ 2) : Tendsto g atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (C / ε))
  have hN1 : 1 ≤ N := by exact_mod_cast (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hN))
  refine ⟨N, ?_⟩
  intro k hk
  have hk1 : 1 ≤ k := le_trans hN1 hk
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkN : (N : ℝ) ≤ k := by exact_mod_cast hk
  have hquot : C / ε < (k : ℝ) := lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hN) hkN
  have hprod : C < ε * (k : ℝ) := by
    have ht := (div_lt_iff₀ hε).mp hquot
    nlinarith
  have hsq : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hdiv : C / (k : ℝ) ^ 2 < ε := by
    apply (div_lt_iff₀ (by positivity : 0 < (k : ℝ) ^ 2)).mpr
    exact lt_of_lt_of_le hprod (mul_le_mul_of_nonneg_left hsq hε.le)
  simpa only [Real.dist_eq, sub_zero] using lt_of_le_of_lt (hb k hk1) hdiv

private theorem aux_rounded_error_bound {c β M : ℝ} (hc : 0 < c) (hβ : 0 ≤ β) (hM : 0 < M)
    (w : ℕ → ℕ) (hr : ∀ k, 1 ≤ k → |(w k : ℝ) - target c β k| ≤ M)
    {k : ℕ} (hk : 1 ≤ k) :
    |height c (w k) - ((k : ℝ) + β)| ≤ c ^ 3 * M / (k : ℝ) ^ 2 := by
  let x : ℝ := (k : ℝ) + β
  let y : ℝ := height c (w k)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hx : 0 < x := by dsimp [x]; linarith
  have hy : 0 ≤ y := aux_height_nonneg hc _
  have hc3 : 0 < c ^ 3 := pow_pos hc _
  have hQ : 0 < y ^ 2 + y * x + x ^ 2 := by positivity
  have hQk : (k : ℝ) ^ 2 ≤ y ^ 2 + y * x + x ^ 2 := by
    have hxx : (k : ℝ) ≤ x := by dsimp [x]; linarith
    have hsq := mul_nonneg (sub_nonneg.mpr hxx) (by positivity : 0 ≤ x + (k : ℝ))
    nlinarith [sq_nonneg y, mul_nonneg hy hx.le]
  have hfac : (y - x) * (y ^ 2 + y * x + x ^ 2) =
      c ^ 3 * ((w k : ℝ) - target c β k) := by
    have h₁ := aux_height_cube c (w k)
    have h₂ := aux_target_cube hc β k
    dsimp [x, y]
    nlinarith [h₁, h₂]
  have habs := congrArg abs hfac
  rw [abs_mul, abs_of_pos hQ, abs_mul, abs_of_pos hc3] at habs
  have hp : |y - x| * (y ^ 2 + y * x + x ^ 2) ≤ c ^ 3 * M := by
    rw [habs]
    exact mul_le_mul_of_nonneg_left (hr k hk) hc3.le
  apply (le_div_iff₀ (by positivity : 0 < (k : ℝ) ^ 2)).mpr
  change |y - x| * (k : ℝ) ^ 2 ≤ c ^ 3 * M
  exact le_trans (mul_le_mul_of_nonneg_left hQk (abs_nonneg _)) hp

private theorem aux_rounded_error_tendsto {c β M : ℝ} (hc : 0 < c) (hβ : 0 ≤ β) (hM : 0 < M)
    (w : ℕ → ℕ) (hr : ∀ k, 1 ≤ k → |(w k : ℝ) - target c β k| ≤ M) :
    Tendsto (fun k => height c (w k) - ((k : ℝ) + β)) atTop (𝓝 0) :=
  aux_inverse_square_zero (mul_pos (pow_pos hc _) hM)
    (fun k hk => aux_rounded_error_bound hc hβ hM w hr hk)

private theorem aux_rounded_above {c β : ℝ} (hc : 0 < c) (hβ : 0 ≤ β) (w : ℕ → ℕ)
    {k : ℕ} (hr : target c β k ≤ (w k : ℝ)) : (k : ℝ) + β ≤ height c (w k) := by
  apply aux_cube_le_inv (by positivity) (aux_height_nonneg hc _)
  have hmul := mul_nonneg (pow_pos hc 3).le (sub_nonneg.mpr hr)
  nlinarith [aux_height_cube c (w k), aux_target_cube hc β k]

private theorem aux_rounded_below {c β : ℝ} (hc : 0 < c) (hβ : 0 ≤ β) (w : ℕ → ℕ)
    {k : ℕ} (hr : (w k : ℝ) < target c β k) : height c (w k) < (k : ℝ) + β := by
  apply aux_cube_lt_inv (aux_height_nonneg hc _) (by positivity)
  have hmul := mul_neg_of_pos_of_neg (pow_pos hc 3) (sub_neg.mpr hr)
  nlinarith [aux_height_cube c (w k), aux_target_cube hc β k]

private theorem aux_rounded_indices_atTop {c β M : ℝ} (hc : 0 < c) (hβ : 0 ≤ β) (hM : 0 < M)
    (w : ℕ → ℕ) (hr : ∀ k, 1 ≤ k → |(w k : ℝ) - target c β k| ≤ M) :
    Tendsto (fun k => (w k : ℝ)) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro B
  have hc3 : 0 < c ^ 3 := pow_pos hc _
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (c ^ 3 * (max (B + M) 0 + 1)))
  have hN1 : 1 ≤ N := by exact_mod_cast (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hN))
  refine eventually_atTop.mpr ⟨N, ?_⟩
  intro k hk
  have hk1 : 1 ≤ k := le_trans hN1 hk
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkN : (N : ℝ) ≤ k := by exact_mod_cast hk
  have hkbig : c ^ 3 * (max (B + M) 0 + 1) < (k : ℝ) :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hN) hkN
  have hk3 : (k : ℝ) ≤ (k : ℝ) ^ 3 := by
    have hs : 0 ≤ (k : ℝ) ^ 2 - 1 := by nlinarith
    nlinarith [mul_nonneg (by positivity : 0 ≤ (k : ℝ)) hs]
  have hx3 := aux_cube_mono (by positivity : 0 ≤ (k : ℝ))
    (show (k : ℝ) ≤ (k : ℝ) + β by linarith)
  have ht : (k : ℝ) / c ^ 3 ≤ target c β k := by
    apply (div_le_iff₀ hc3).mpr
    nlinarith [aux_target_cube hc β k]
  have hlower := (abs_le.mp (hr k hk1)).1
  have hquot : max (B + M) 0 + 1 < (k : ℝ) / c ^ 3 := by
    apply (lt_div_iff₀ hc3).mpr
    nlinarith
  linarith [le_max_left (B + M) 0]

private theorem aux_rounded_strict_tail {c β M : ℝ} (hc : 0 < c) (hβ : 0 ≤ β) (hM : 0 < M)
    (w : ℕ → ℕ) (hr : ∀ k, 1 ≤ k → |(w k : ℝ) - target c β k| ≤ M) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ k, D ≤ k → w k < w (k + 1) := by
  obtain ⟨D, hD⟩ := exists_nat_gt (max 1 (2 * M * c ^ 3))
  have hD1 : 1 ≤ D := by exact_mod_cast (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hD))
  refine ⟨D, hD1, ?_⟩
  intro k hk
  have hk1 : 1 ≤ k := le_trans hD1 hk
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkD : (D : ℝ) ≤ k := by exact_mod_cast hk
  have hkbig : 2 * M * c ^ 3 < (k : ℝ) :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hD) hkD
  have hstep : c ^ 3 * (target c β (k + 1) - target c β k) =
      3 * ((k : ℝ) + β) ^ 2 + 3 * ((k : ℝ) + β) + 1 := by
    calc
      _ = c ^ 3 * target c β (k + 1) - c ^ 3 * target c β k := by ring
      _ = (((k + 1 : ℕ) : ℝ) + β) ^ 3 - ((k : ℝ) + β) ^ 3 := by
        rw [aux_target_cube hc, aux_target_cube hc]
      _ = _ := by push_cast; ring
  have hpoly : (k : ℝ) ≤ 3 * ((k : ℝ) + β) ^ 2 + 3 * ((k : ℝ) + β) + 1 := by
    nlinarith [sq_nonneg ((k : ℝ) + β)]
  have hgap : 2 * M < target c β (k + 1) - target c β k := by
    have hscaled : c ^ 3 * (2 * M) < c ^ 3 * (target c β (k + 1) - target c β k) := by
      nlinarith
    by_contra hbad
    have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt hbad) (pow_pos hc 3).le
    linarith
  have h₁ := abs_le.mp (hr k hk1)
  have h₂ := abs_le.mp (hr (k + 1) (by omega))
  have hreal : (w k : ℝ) < (w (k + 1) : ℝ) := by linarith
  exact_mod_cast hreal

private theorem aux_rounded_tail_construct {c β M : ℝ} (hc : 0 < c) (hβ : 0 ≤ β)
    (hM : 0 < M) (w : ℕ → ℕ)
    (hr : ∀ k, 1 ≤ k → |(w k : ℝ) - target c β k| ≤ M)
    (P : ℕ → Prop) (hP : ∀ᶠ k in atTop, P k) :
    ∃ K : ℕ, 2 ≤ K ∧ StrictMono (fun j => w (j + K)) ∧
      (∀ j, cutoff c ≤ w (j + K)) ∧ ∀ j, P (j + K) := by
  obtain ⟨D, hD1, hD⟩ := aux_rounded_strict_tail hc hβ hM w hr
  have hlegal := (Filter.tendsto_atTop.mp (aux_rounded_indices_atTop hc hβ hM w hr))
    (cutoff c : ℝ)
  obtain ⟨W, hW⟩ := eventually_atTop.mp hlegal
  obtain ⟨V, hV⟩ := eventually_atTop.mp hP
  let K : ℕ := max 2 (max D (max W V))
  have hK2 : 2 ≤ K := by dsimp [K]; omega
  have hKD : D ≤ K := by dsimp [K]; omega
  have hKW : W ≤ K := by dsimp [K]; omega
  have hKV : V ≤ K := by dsimp [K]; omega
  refine ⟨K, hK2, ?_, ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro j
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hD (j + K) (by omega)
  · intro j
    have hh := hW (j + K) (by omega)
    exact_mod_cast hh
  · intro j
    exact hV (j + K) (by omega)

private theorem aux_q_pos {c : ℝ} (hc : 0 < c) : 0 < q c := by
  exact div_pos (sq_pos_of_pos Real.pi_pos) (mul_pos (by norm_num) (pow_pos hc 3))

private theorem aux_simultaneous_of_delta {c d : ℝ} {σ : ℕ → ℕ}
    (hd : Tendsto (fun j => delta c (σ j)) atTop (𝓝 d)) :
    Tendsto (fun j => exponent c (σ j)) atTop (𝓝 (q c * d)) ∧
    Tendsto (fun j => factor c (σ j)) atTop (𝓝 (Real.exp (q c * d))) := by
  have hE : Tendsto (fun j => exponent c (σ j)) atTop (𝓝 (q c * d)) := by
    simpa [exponent] using (tendsto_const_nhds.mul hd)
  refine ⟨hE, ?_⟩
  simpa only [factor, Function.comp_def] using
    (Real.continuous_exp.tendsto (q c * d)).comp hE

private def aux_TailResult (c : ℝ) (w : ℕ → ℕ) (d : ℝ) (P : ℕ → Prop) : Prop :=
  ∃ K : ℕ, 2 ≤ K ∧ StrictMono (fun j => w (j + K)) ∧
    (∀ j, cutoff c ≤ w (j + K)) ∧ (∀ j, P (j + K)) ∧
    Tendsto (fun j => delta c (w (j + K))) atTop (𝓝 d) ∧
    Tendsto (fun j => exponent c (w (j + K))) atTop (𝓝 (q c * d)) ∧
    Tendsto (fun j => factor c (w (j + K))) atTop (𝓝 (Real.exp (q c * d)))

private theorem aux_build_tail_result {c β M d : ℝ} (hc : 0 < c) (hβ : 0 ≤ β) (hM : 0 < M)
    (w : ℕ → ℕ) (hr : ∀ k, 1 ≤ k → |(w k : ℝ) - target c β k| ≤ M)
    (P : ℕ → Prop) (hP : ∀ᶠ k in atTop, P k)
    (hd : Tendsto (fun k => delta c (w k)) atTop (𝓝 d)) : aux_TailResult c w d P := by
  obtain ⟨K, hK, hs, hl, hp⟩ := aux_rounded_tail_construct hc hβ hM w hr P hP
  have hdK := hd.comp (tendsto_add_atTop_nat K)
  obtain ⟨hE, hF⟩ := aux_simultaneous_of_delta hdK
  exact ⟨K, hK, hs, hl, hp, hdK, hE, hF⟩

private theorem aux_up_error {c : ℝ} (hc : 0 < c) (k : ℕ) :
    0 ≤ (upIndex c k : ℝ) - target c 0 k ∧ (upIndex c k : ℝ) - target c 0 k < 1 := by
  exact aux_nat_ceil_error (by dsimp [target]; positivity)

private theorem aux_up_positive {c : ℝ} (hc : 0 < c) {k : ℕ} (hk : 1 ≤ k) : 1 ≤ upIndex c k := by
  apply Nat.one_le_iff_ne_zero.mpr
  have ht : 0 < target c 0 k := by
    have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    dsimp [target]
    positivity
  have ha : 0 < Nat.ceil (target c 0 k) := Nat.ceil_pos.mpr ht
  change Nat.ceil (target c 0 k) ≠ 0
  omega

private theorem aux_down_zero (c : ℝ) : downIndex c 0 = 0 := by simp [downIndex, target]

private theorem aux_up_zero (c : ℝ) : upIndex c 0 = 0 := by simp [upIndex, target]

private theorem aux_down_cast {c : ℝ} (hc : 0 < c) {k : ℕ} (hk : 1 ≤ k) :
    (downIndex c k : ℝ) = (upIndex c k : ℝ) - 1 := by
  change ((upIndex c k - 1 : ℕ) : ℝ) = (upIndex c k : ℝ) - 1
  rw [Nat.cast_sub (aux_up_positive hc hk), Nat.cast_one]

private theorem aux_down_error {c : ℝ} (hc : 0 < c) {k : ℕ} (hk : 1 ≤ k) :
    -1 ≤ (downIndex c k : ℝ) - target c 0 k ∧ (downIndex c k : ℝ) - target c 0 k < 0 := by
  rw [aux_down_cast hc hk]
  have h := aux_up_error hc k
  constructor <;> linarith

private theorem aux_up_rounding {c : ℝ} (hc : 0 < c) (k : ℕ) (_hk : 1 ≤ k) :
    |(upIndex c k : ℝ) - target c 0 k| ≤ 1 :=
  abs_le.mpr ⟨by linarith [(aux_up_error hc k).1], (aux_up_error hc k).2.le⟩

private theorem aux_down_rounding {c : ℝ} (hc : 0 < c) (k : ℕ) (hk : 1 ≤ k) :
    |(downIndex c k : ℝ) - target c 0 k| ≤ 1 :=
  abs_le.mpr ⟨(aux_down_error hc hk).1, by linarith [(aux_down_error hc hk).2]⟩

private theorem aux_up_height_error {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k => height c (upIndex c k) - (k : ℝ)) atTop (𝓝 0) := by
  simpa using aux_rounded_error_tendsto hc (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) < 1)
    (upIndex c) (aux_up_rounding hc)

private theorem aux_down_height_error {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k => height c (downIndex c k) - (k : ℝ)) atTop (𝓝 0) := by
  simpa using aux_rounded_error_tendsto hc (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) < 1)
    (downIndex c) (aux_down_rounding hc)

private def aux_UpStable (c : ℝ) (k : ℕ) : Prop :=
  1 ≤ k ∧ (k : ℝ) ≤ height c (upIndex c k) ∧
    height c (upIndex c k) < (k : ℝ) + 1 ∧ phaseFloor c (upIndex c k) = k

private def aux_DownStable (c : ℝ) (k : ℕ) : Prop :=
  2 ≤ k ∧ (k : ℝ) - 1 < height c (downIndex c k) ∧
    height c (downIndex c k) < (k : ℝ) ∧ phaseFloor c (downIndex c k) = k - 1

private theorem aux_up_stable {c : ℝ} (hc : 0 < c) : ∀ᶠ k in atTop, aux_UpStable c k := by
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (aux_up_height_error hc)) 1 (by norm_num)
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop (1 : ℕ)] with k hk hk1
  have hs : |height c (upIndex c k) - (k : ℝ)| < 1 := by
    simpa only [Real.dist_eq, sub_zero] using hN k hk
  have hlow : (k : ℝ) ≤ height c (upIndex c k) := by
    simpa using aux_rounded_above hc (le_refl (0 : ℝ)) (upIndex c)
      (show target c 0 k ≤ (upIndex c k : ℝ) by linarith [(aux_up_error hc k).1])
  have hhigh : height c (upIndex c k) < (k : ℝ) + 1 := by
    have ht := (abs_lt.mp hs).2
    linarith
  refine ⟨hk1, hlow, hhigh, ?_⟩
  exact (Nat.floor_eq_iff (aux_height_nonneg hc _)).mpr ⟨hlow, hhigh⟩

private theorem aux_down_stable {c : ℝ} (hc : 0 < c) : ∀ᶠ k in atTop, aux_DownStable c k := by
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (aux_down_height_error hc)) 1 (by norm_num)
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop (2 : ℕ)] with k hk hk2
  have hk1 : 1 ≤ k := by omega
  have hs : |height c (downIndex c k) - (k : ℝ)| < 1 := by
    simpa only [Real.dist_eq, sub_zero] using hN k hk
  have hhigh : height c (downIndex c k) < (k : ℝ) := by
    simpa using aux_rounded_below hc (le_refl (0 : ℝ)) (downIndex c)
      (show (downIndex c k : ℝ) < target c 0 k by linarith [(aux_down_error hc hk1).2])
  have hlow : (k : ℝ) - 1 < height c (downIndex c k) := by
    have ht := (abs_lt.mp hs).1
    linarith
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    simp only [Nat.cast_sub hk1, Nat.cast_one]
  refine ⟨hk2, hlow, hhigh, ?_⟩
  apply (Nat.floor_eq_iff (aux_height_nonneg hc _)).mpr
  rw [hcast]
  constructor <;> linarith

private theorem aux_up_delta_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k => delta c (upIndex c k)) atTop (𝓝 1) := by
  have heq : (fun k => delta c (upIndex c k)) =ᶠ[atTop]
      (fun k => 1 - (height c (upIndex c k) - (k : ℝ))) := by
    filter_upwards [aux_up_stable hc] with k hk
    dsimp [delta, upperHeight]
    rw [hk.2.2.2]
    ring
  apply (tendsto_congr' heq).mpr
  simpa using (tendsto_const_nhds.sub (aux_up_height_error hc))

private theorem aux_down_delta_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k => delta c (downIndex c k)) atTop (𝓝 0) := by
  have heq : (fun k => delta c (downIndex c k)) =ᶠ[atTop]
      (fun k => 0 - (height c (downIndex c k) - (k : ℝ))) := by
    filter_upwards [aux_down_stable hc] with k hk
    have hk1 : 1 ≤ k := by have := hk.1; omega
    dsimp [delta, upperHeight]
    rw [hk.2.2.2, Nat.cast_sub hk1, Nat.cast_one]
    ring
  apply (tendsto_congr' heq).mpr
  simpa using ((tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ))).sub (aux_down_height_error hc))

private theorem aux_up_subsequence {c : ℝ} (hc : 0 < c) :
    aux_TailResult c (upIndex c) 1 (aux_UpStable c) :=
  aux_build_tail_result hc (le_refl (0 : ℝ)) (by norm_num) (upIndex c)
    (aux_up_rounding hc) (aux_UpStable c) (aux_up_stable hc) (aux_up_delta_limit hc)

private theorem aux_down_subsequence {c : ℝ} (hc : 0 < c) :
    aux_TailResult c (downIndex c) 0 (aux_DownStable c) :=
  aux_build_tail_result hc (le_refl (0 : ℝ)) (by norm_num) (downIndex c)
    (aux_down_rounding hc) (aux_DownStable c) (aux_down_stable hc) (aux_down_delta_limit hc)

private theorem aux_nearest_error {c α : ℝ} (hc : 0 < c) (hα : 0 < α) (k : ℕ) :
    -(1 / 2 : ℝ) < (nearestIndex c α k : ℝ) - target c α k ∧
    (nearestIndex c α k : ℝ) - target c α k ≤ 1 / 2 ∧
    |(nearestIndex c α k : ℝ) - target c α k| ≤ 1 / 2 := by
  have ht : 0 < target c α k := by dsimp [target]; positivity
  have hf := aux_nat_floor_bounds (show 0 ≤ target c α k + 1 / 2 by linarith)
  change -(1 / 2 : ℝ) < (Nat.floor (target c α k + 1 / 2) : ℝ) - target c α k ∧
    (Nat.floor (target c α k + 1 / 2) : ℝ) - target c α k ≤ 1 / 2 ∧
    |(Nat.floor (target c α k + 1 / 2) : ℝ) - target c α k| ≤ 1 / 2
  refine ⟨by linarith, by linarith, ?_⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem aux_nearest_tie_up {c α : ℝ} {k l : ℕ}
    (ht : target c α k = (l : ℝ) + 1 / 2) : nearestIndex c α k = l + 1 := by
  unfold nearestIndex
  rw [ht]
  have heq : (l : ℝ) + 1 / 2 + 1 / 2 = ((l + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [heq, Nat.floor_natCast]

private theorem aux_nearest_height_error {c α : ℝ} (hc : 0 < c) (hα : 0 < α) :
    Tendsto (fun k => height c (nearestIndex c α k) - ((k : ℝ) + α)) atTop (𝓝 0) :=
  aux_rounded_error_tendsto hc hα.le (by norm_num : (0 : ℝ) < 1 / 2)
    (nearestIndex c α) (fun k _ => (aux_nearest_error hc hα k).2.2)

private def aux_InternalStable (c α : ℝ) (k : ℕ) : Prop :=
  (k : ℝ) < height c (nearestIndex c α k) ∧
    height c (nearestIndex c α k) < (k : ℝ) + 1 ∧ phaseFloor c (nearestIndex c α k) = k

private theorem aux_nearest_stable {c α : ℝ} (hc : 0 < c) (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ᶠ k in atTop, aux_InternalStable c α k := by
  have hη : 0 < min α (1 - α) := lt_min hα0 (by linarith)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (aux_nearest_height_error hc hα0)) _ hη
  filter_upwards [eventually_ge_atTop N] with k hk
  have hs : |height c (nearestIndex c α k) - ((k : ℝ) + α)| < min α (1 - α) := by
    simpa only [Real.dist_eq, sub_zero] using hN k hk
  have hlo : (k : ℝ) < height c (nearestIndex c α k) := by
    have h := (abs_lt.mp hs).1
    linarith [min_le_left α (1 - α)]
  have hhi : height c (nearestIndex c α k) < (k : ℝ) + 1 := by
    have h := (abs_lt.mp hs).2
    linarith [min_le_right α (1 - α)]
  refine ⟨hlo, hhi, ?_⟩
  exact (Nat.floor_eq_iff (aux_height_nonneg hc _)).mpr ⟨hlo.le, hhi⟩

private theorem aux_nearest_delta_limit {c α : ℝ} (hc : 0 < c) (hα0 : 0 < α) (hα1 : α < 1) :
    Tendsto (fun k => delta c (nearestIndex c α k)) atTop (𝓝 (1 - α)) := by
  have heq : (fun k => delta c (nearestIndex c α k)) =ᶠ[atTop]
      (fun k => (1 - α) - (height c (nearestIndex c α k) - ((k : ℝ) + α))) := by
    filter_upwards [aux_nearest_stable hc hα0 hα1] with k hk
    dsimp [delta, upperHeight]
    rw [hk.2.2]
    ring
  apply (tendsto_congr' heq).mpr
  simpa using (tendsto_const_nhds.sub (aux_nearest_height_error hc hα0))

private theorem aux_nearest_subsequence {c α : ℝ} (hc : 0 < c) (hα0 : 0 < α) (hα1 : α < 1) :
    aux_TailResult c (nearestIndex c α) (1 - α) (aux_InternalStable c α) :=
  aux_build_tail_result hc hα0.le (by norm_num : (0 : ℝ) < 1 / 2) (nearestIndex c α)
    (fun k _ => (aux_nearest_error hc hα0 k).2.2) (aux_InternalStable c α)
    (aux_nearest_stable hc hα0 hα1) (aux_nearest_delta_limit hc hα0 hα1)

private theorem aux_cutoff_one : cutoff 1 = 1 := by norm_num [cutoff]

private theorem aux_exact_cube (k : ℕ) :
    height 1 (cubeIndex k) = (k : ℝ) ∧ phaseFloor 1 (cubeIndex k) = k ∧
      upperHeight 1 (cubeIndex k) = (k : ℝ) + 1 ∧ delta 1 (cubeIndex k) = 1 := by
  have hh : height 1 (cubeIndex k) = (k : ℝ) := by
    apply aux_cube_injective_nonneg (aux_height_nonneg (by norm_num) _) (Nat.cast_nonneg k)
    simpa [cubeIndex, Nat.cast_pow] using aux_height_cube 1 (cubeIndex k)
  refine ⟨hh, ?_, ?_, ?_⟩
  · simp [phaseFloor, hh]
  · simp [upperHeight, phaseFloor, hh]
  · exact aux_delta_of_nat_height hh

private theorem aux_below_cube_cast {k : ℕ} (hk : 1 ≤ k) :
    (belowCubeIndex k : ℝ) = (k : ℝ) ^ 3 - 1 := by
  have hkp : 1 ≤ k ^ 3 := Nat.succ_le_iff.mpr (pow_pos (by omega : 0 < k) 3)
  simp only [belowCubeIndex, Nat.cast_sub hkp, Nat.cast_pow, Nat.cast_one]

private theorem aux_exact_below_cube {k : ℕ} (hk : 2 ≤ k) :
    1 ≤ belowCubeIndex k ∧ (belowCubeIndex k : ℝ) = (k : ℝ) ^ 3 - 1 ∧
    (k : ℝ) - 1 < height 1 (belowCubeIndex k) ∧ height 1 (belowCubeIndex k) < (k : ℝ) ∧
    phaseFloor 1 (belowCubeIndex k) = k - 1 ∧ upperHeight 1 (belowCubeIndex k) = (k : ℝ) ∧
    delta 1 (belowCubeIndex k) = (k : ℝ) - height 1 (belowCubeIndex k) := by
  have hk1 : 1 ≤ k := by omega
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hcast := aux_below_cube_cast hk1
  have hkp := aux_cube_mono (by norm_num : (0 : ℝ) ≤ 2) hkR
  have hnR : (1 : ℝ) ≤ belowCubeIndex k := by rw [hcast]; norm_num at hkp; linarith
  have hn : 1 ≤ belowCubeIndex k := by exact_mod_cast hnR
  have hy := aux_height_nonneg (by norm_num : (0 : ℝ) < 1) (belowCubeIndex k)
  have hy3 : height 1 (belowCubeIndex k) ^ 3 = (k : ℝ) ^ 3 - 1 := by
    simpa [hcast] using aux_height_cube 1 (belowCubeIndex k)
  have hlo : (k : ℝ) - 1 < height 1 (belowCubeIndex k) := by
    apply aux_cube_lt_inv (by linarith) hy
    have hp := mul_pos (show (0 : ℝ) < k by linarith) (show (0 : ℝ) < (k : ℝ) - 1 by linarith)
    nlinarith
  have hhi : height 1 (belowCubeIndex k) < (k : ℝ) := by
    apply aux_cube_lt_inv hy (by positivity)
    linarith
  have hkm : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by simp only [Nat.cast_sub hk1, Nat.cast_one]
  have hm : phaseFloor 1 (belowCubeIndex k) = k - 1 := by
    apply (Nat.floor_eq_iff hy).mpr
    rw [hkm]
    constructor <;> linarith
  have hH : upperHeight 1 (belowCubeIndex k) = (k : ℝ) := by
    dsimp [upperHeight]
    rw [hm, hkm]
    ring
  exact ⟨hn, hcast, hlo, hhi, hm, hH, by dsimp [delta]; rw [hH]⟩

private theorem aux_below_cube_rounding (k : ℕ) (hk : 1 ≤ k) :
    |(belowCubeIndex k : ℝ) - target 1 0 k| ≤ 1 := by
  rw [aux_below_cube_cast hk]
  simp only [target, add_zero, div_one]
  rw [show (k : ℝ) ^ 3 - 1 - (k : ℝ) ^ 3 = -1 by ring]
  norm_num

private theorem aux_below_cube_delta_limit :
    Tendsto (fun k => delta 1 (belowCubeIndex k)) atTop (𝓝 0) := by
  have he := aux_rounded_error_tendsto (by norm_num : (0 : ℝ) < 1) (le_refl (0 : ℝ))
    (by norm_num : (0 : ℝ) < 1) belowCubeIndex aux_below_cube_rounding
  have heq : (fun k => delta 1 (belowCubeIndex k)) =ᶠ[atTop]
      (fun k => 0 - (height 1 (belowCubeIndex k) - ((k : ℝ) + 0))) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with k hk
    rw [(aux_exact_below_cube hk).2.2.2.2.2.2]
    ring
  apply (tendsto_congr' heq).mpr
  simpa using ((tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ))).sub he)

private theorem aux_exact_cube_subsequence :
    StrictMono (fun j : ℕ => cubeIndex (j + 1)) ∧
    (∀ j, cutoff 1 ≤ cubeIndex (j + 1)) ∧
    Tendsto (fun j => exponent 1 (cubeIndex (j + 1))) atTop (𝓝 (Real.pi ^ 2 / 4)) ∧
    Tendsto (fun j => factor 1 (cubeIndex (j + 1))) atTop (𝓝 (Real.exp (Real.pi ^ 2 / 4))) := by
  have hs : StrictMono (fun j : ℕ => cubeIndex (j + 1)) := by
    apply strictMono_nat_of_lt_succ
    intro j
    have hreal : ((j + 1 : ℕ) : ℝ) ^ 3 < ((j + 1 + 1 : ℕ) : ℝ) ^ 3 := by
      apply aux_cube_strict (by positivity)
      push_cast
      linarith
    change (j + 1) ^ 3 < (j + 1 + 1) ^ 3
    exact_mod_cast hreal
  have hl : ∀ j, cutoff 1 ≤ cubeIndex (j + 1) := by
    intro j
    rw [aux_cutoff_one]
    exact Nat.succ_le_iff.mpr (pow_pos (by omega : 0 < j + 1) 3)
  have hd : Tendsto (fun j => delta 1 (cubeIndex (j + 1))) atTop (𝓝 1) := by
    have heq : (fun j => delta 1 (cubeIndex (j + 1))) =ᶠ[atTop] (fun _ => (1 : ℝ)) :=
      Eventually.of_forall (fun j => (aux_exact_cube (j + 1)).2.2.2)
    exact (tendsto_congr' heq).mpr tendsto_const_nhds
  obtain ⟨hE, hF⟩ := aux_simultaneous_of_delta hd
  exact ⟨hs, hl, by simpa [q] using hE, by simpa [q] using hF⟩

private theorem aux_exact_below_cube_subsequence :
    StrictMono (fun j : ℕ => belowCubeIndex (j + 2)) ∧
    (∀ j, cutoff 1 ≤ belowCubeIndex (j + 2)) ∧
    Tendsto (fun j => exponent 1 (belowCubeIndex (j + 2))) atTop (𝓝 0) ∧
    Tendsto (fun j => factor 1 (belowCubeIndex (j + 2))) atTop (𝓝 1) := by
  have hs : StrictMono (fun j : ℕ => belowCubeIndex (j + 2)) := by
    apply strictMono_nat_of_lt_succ
    intro j
    have hreal : (belowCubeIndex (j + 2) : ℝ) < (belowCubeIndex (j + 1 + 2) : ℝ) := by
      rw [aux_below_cube_cast (by omega), aux_below_cube_cast (by omega)]
      apply sub_lt_sub_right
      apply aux_cube_strict (by positivity)
      push_cast
      linarith
    exact_mod_cast hreal
  have hl : ∀ j, cutoff 1 ≤ belowCubeIndex (j + 2) := by
    intro j
    rw [aux_cutoff_one]
    exact (aux_exact_below_cube (by omega : 2 ≤ j + 2)).1
  have hd := aux_below_cube_delta_limit.comp (tendsto_add_atTop_nat 2)
  obtain ⟨hE, hF⟩ := aux_simultaneous_of_delta hd
  exact ⟨hs, hl, by simpa using hE, by simpa using hF⟩

private theorem aux_realize_every_phase {c d : ℝ} (hc : 0 < c) (hd : d ∈ Set.Icc (0 : ℝ) 1) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ (∀ j, cutoff c ≤ σ j) ∧
      Tendsto (fun j => delta c (σ j)) atTop (𝓝 d) ∧
      Tendsto (fun j => exponent c (σ j)) atTop (𝓝 (q c * d)) ∧
      Tendsto (fun j => factor c (σ j)) atTop (𝓝 (Real.exp (q c * d))) := by
  classical
  by_cases h0 : d = 0
  · subst d
    obtain ⟨K, hK, hs, hl, hp, hδ, hE, hF⟩ := aux_down_subsequence hc
    exact ⟨fun j => downIndex c (j + K), hs, hl, hδ, hE, hF⟩
  by_cases h1 : d = 1
  · subst d
    obtain ⟨K, hK, hs, hl, hp, hδ, hE, hF⟩ := aux_up_subsequence hc
    exact ⟨fun j => upIndex c (j + K), hs, hl, hδ, hE, hF⟩
  have hd0 : 0 < d := lt_of_le_of_ne hd.1 (Ne.symm h0)
  have hd1 : d < 1 := lt_of_le_of_ne hd.2 h1
  have ha0 : 0 < 1 - d := by linarith
  have ha1 : 1 - d < 1 := by linarith
  obtain ⟨K, hK, hs, hl, hp, hδ, hE, hF⟩ := aux_nearest_subsequence hc ha0 ha1
  have hid : 1 - (1 - d) = d := by ring
  refine ⟨fun j => nearestIndex c (1 - d) (j + K), hs, hl, ?_, ?_, ?_⟩
  · simpa only [hid] using hδ
  · simpa only [hid] using hE
  · simpa only [hid] using hF

private theorem aux_exponent_range {c : ℝ} (hc : 0 < c) (n : ℕ) :
    0 < exponent c n ∧ exponent c n ≤ q c := by
  have hδ := aux_delta_range hc n
  have hq := aux_q_pos hc
  constructor
  · exact mul_pos hq hδ.1
  · simpa [exponent] using mul_le_mul_of_nonneg_left hδ.2 hq.le

private theorem aux_factor_range {c : ℝ} (hc : 0 < c) (n : ℕ) :
    1 < factor c n ∧ factor c n ≤ Real.exp (q c) := by
  have hE := aux_exponent_range hc n
  constructor
  · simpa [factor] using (Real.exp_lt_exp.mpr hE.1)
  · exact Real.exp_le_exp.mpr hE.2

private theorem aux_cluster_delta {c : ℝ} (hc : 0 < c) : Cluster (delta c) = Set.Icc (0 : ℝ) 1 := by
  ext L
  constructor
  · rintro ⟨σ, hs, hL⟩
    exact ⟨le_of_tendsto_of_tendsto' tendsto_const_nhds hL
      (fun j => (aux_delta_range hc (σ j)).1.le),
      le_of_tendsto' hL (fun j => (aux_delta_range hc (σ j)).2)⟩
  · intro hL
    obtain ⟨σ, hs, hl, hδ, hE, hF⟩ := aux_realize_every_phase hc hL
    exact ⟨σ, hs, hδ⟩

private theorem aux_cluster_exponent {c : ℝ} (hc : 0 < c) :
    Cluster (exponent c) = Set.Icc (0 : ℝ) (q c) := by
  ext L
  constructor
  · rintro ⟨σ, hs, hL⟩
    exact ⟨le_of_tendsto_of_tendsto' tendsto_const_nhds hL
      (fun j => (aux_exponent_range hc (σ j)).1.le),
      le_of_tendsto' hL (fun j => (aux_exponent_range hc (σ j)).2)⟩
  · intro hL
    have hq := aux_q_pos hc
    have hd : L / q c ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨div_nonneg hL.1 hq.le, ?_⟩
      apply (div_le_iff₀ hq).mpr
      simpa using hL.2
    obtain ⟨σ, hs, hl, hδ, hE, hF⟩ := aux_realize_every_phase hc hd
    have heq : q c * (L / q c) = L := by field_simp [hq.ne']
    exact ⟨σ, hs, by simpa [heq] using hE⟩

private theorem aux_cluster_factor {c : ℝ} (hc : 0 < c) :
    Cluster (factor c) = Set.Icc (1 : ℝ) (Real.exp (q c)) := by
  ext L
  constructor
  · rintro ⟨σ, hs, hL⟩
    exact ⟨le_of_tendsto_of_tendsto' tendsto_const_nhds hL
      (fun j => (aux_factor_range hc (σ j)).1.le),
      le_of_tendsto' hL (fun j => (aux_factor_range hc (σ j)).2)⟩
  · intro hL
    have hq := aux_q_pos hc
    have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL.1
    have hlog0 : 0 ≤ Real.log L := by
      simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 1) hL.1
    have hlogq : Real.log L ≤ q c := by
      simpa only [Real.log_exp] using Real.log_le_log hLp hL.2
    have hd : Real.log L / q c ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨div_nonneg hlog0 hq.le, ?_⟩
      apply (div_le_iff₀ hq).mpr
      simpa using hlogq
    obtain ⟨σ, hs, hl, hδ, hE, hF⟩ := aux_realize_every_phase hc hd
    have heq : q c * (Real.log L / q c) = Real.log L := by field_simp [hq.ne']
    exact ⟨σ, hs, by simpa [heq, Real.exp_log hLp] using hF⟩

private theorem aux_delta_not_convergent {c : ℝ} (hc : 0 < c) :
    ¬ ∃ L : ℝ, Tendsto (delta c) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  obtain ⟨σ₀, hs₀, hl₀, hd₀, hE₀, hF₀⟩ := aux_realize_every_phase hc (d := 0) (by simp)
  obtain ⟨σ₁, hs₁, hl₁, hd₁, hE₁, hF₁⟩ := aux_realize_every_phase hc (d := 1) (by simp)
  have heq₀ := tendsto_nhds_unique (hL.comp hs₀.tendsto_atTop) hd₀
  have heq₁ := tendsto_nhds_unique (hL.comp hs₁.tendsto_atTop) hd₁
  linarith

private theorem aux_exponent_not_convergent {c : ℝ} (hc : 0 < c) :
    ¬ ∃ L : ℝ, Tendsto (exponent c) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  obtain ⟨σ₀, hs₀, hl₀, hd₀, hE₀, hF₀⟩ := aux_realize_every_phase hc (d := 0) (by simp)
  obtain ⟨σ₁, hs₁, hl₁, hd₁, hE₁, hF₁⟩ := aux_realize_every_phase hc (d := 1) (by simp)
  have heq₀ := tendsto_nhds_unique (hL.comp hs₀.tendsto_atTop) hE₀
  have heq₁ := tendsto_nhds_unique (hL.comp hs₁.tendsto_atTop) hE₁
  have hq := aux_q_pos hc
  simp only [mul_zero, mul_one] at heq₀ heq₁
  linarith

private theorem aux_factor_not_convergent {c : ℝ} (hc : 0 < c) :
    ¬ ∃ L : ℝ, Tendsto (factor c) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  obtain ⟨σ₀, hs₀, hl₀, hd₀, hE₀, hF₀⟩ := aux_realize_every_phase hc (d := 0) (by simp)
  obtain ⟨σ₁, hs₁, hl₁, hd₁, hE₁, hF₁⟩ := aux_realize_every_phase hc (d := 1) (by simp)
  have heq₀ := tendsto_nhds_unique (hL.comp hs₀.tendsto_atTop) hF₀
  have heq₁ := tendsto_nhds_unique (hL.comp hs₁.tendsto_atTop) hF₁
  have hneq : (1 : ℝ) < Real.exp (q c) := by
    simpa using Real.exp_lt_exp.mpr (aux_q_pos hc)
  simp only [mul_zero, mul_one, Real.exp_zero] at heq₀ heq₁
  linarith

private theorem aux_exact_cube_weakCell {k : ℕ} (hk : 1 ≤ k) : WeakCell 1 (cubeIndex k) := by
  apply aux_weakCell_of_cutoff (by norm_num : (0 : ℝ) < 1)
  rw [aux_cutoff_one]
  exact Nat.succ_le_iff.mpr (pow_pos (by omega : 0 < k) 3)

private theorem aux_exact_below_cube_weakCell {k : ℕ} (hk : 2 ≤ k) : WeakCell 1 (belowCubeIndex k) := by
  apply aux_weakCell_of_cutoff (by norm_num : (0 : ℝ) < 1)
  rw [aux_cutoff_one]
  exact (aux_exact_below_cube hk).1

private theorem aux_exact_cube_delta_subsequence :
    Tendsto (fun j : ℕ => delta 1 (cubeIndex (j + 1))) atTop (𝓝 1) := by
  have heq : (fun j : ℕ => delta 1 (cubeIndex (j + 1))) =ᶠ[atTop] (fun _ => (1 : ℝ)) :=
    Eventually.of_forall (fun j => (aux_exact_cube (j + 1)).2.2.2)
  exact (tendsto_congr' heq).mpr tendsto_const_nhds

private theorem aux_exact_below_cube_delta_subsequence :
    Tendsto (fun j : ℕ => delta 1 (belowCubeIndex (j + 2))) atTop (𝓝 0) :=
  aux_below_cube_delta_limit.comp (tendsto_add_atTop_nat 2)

theorem root_spec (n : ℕ) :
    0 ≤ root n ∧ root n ^ 3 = (n : ℝ) ∧
    (∀ x : ℝ, 0 ≤ x → x ^ 3 = (n : ℝ) → x = root n) := by
  refine ⟨aux_root_nonneg n, aux_root_cube n, ?_⟩
  intro x hx hx3
  exact aux_cube_injective_nonneg hx (aux_root_nonneg n) (hx3.trans (aux_root_cube n).symm)

theorem zero_prefix (c : ℝ) :
    root 0 = 0 ∧ height c 0 = 0 ∧ phaseFloor c 0 = 0 ∧
    upperHeight c 0 = 1 ∧ delta c 0 = 1 ∧ (0 : ℝ) / height c 0 ^ 3 = 0 := by
  obtain ⟨hh, hm, hH, hδ⟩ := aux_zero_prefix c
  exact ⟨aux_root_zero, hh, hm, hH, hδ, aux_zero_time_scale c⟩

theorem positive_time {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) :
    0 < root n ∧ 0 < height c n ∧ height c n ^ 3 = c ^ 3 * (n : ℝ) ∧
    (n : ℝ) / height c n ^ 3 = 1 / c ^ 3 ∧ 0 < 1 / c ^ 3 := by
  exact ⟨aux_root_pos hn, aux_height_pos hc hn, aux_height_cube c n,
    (aux_time_scale hc hn).1, (aux_time_scale hc hn).2⟩

theorem finite_phase {c : ℝ} (hc : 0 < c) (n : ℕ) :
    0 ≤ height c n ∧ (phaseFloor c n : ℤ) = Int.floor (height c n) ∧
    (phaseFloor c n : ℝ) ≤ height c n ∧ height c n < upperHeight c n ∧
    upperHeight c n = height c n + delta c n ∧
    0 < delta c n ∧ delta c n ≤ 1 ∧ 0 < q c ∧
    0 < exponent c n ∧ exponent c n ≤ q c ∧
    1 < factor c n ∧ factor c n ≤ Real.exp (q c) ∧
    (∀ z : ℤ, height c n = (z : ℝ) → delta c n = 1) := by
  have hh := aux_height_nonneg hc n
  have hf := aux_nat_floor_bounds hh
  have hd := aux_delta_range hc n
  have hE := aux_exponent_range hc n
  have hF := aux_factor_range hc n
  refine ⟨hh, ?_, hf.1, hf.2, ?_, hd.1, hd.2, aux_q_pos hc,
    hE.1, hE.2, hF.1, hF.2, ?_⟩
  · exact aux_nat_floor_agrees_int hh
  · dsimp [delta]
    ring
  · intro z hz
    have hmz : (phaseFloor c n : ℤ) = z := by
      change (Nat.floor (height c n) : ℤ) = z
      rw [aux_nat_floor_agrees_int hh, hz, Int.floor_intCast]
    have hmr : (phaseFloor c n : ℝ) = (z : ℝ) := by exact_mod_cast hmz
    dsimp [delta, upperHeight]
    rw [hmr, hz]
    ring

theorem cutoff_spec {c : ℝ} (hc : 0 < c) :
    1 ≤ cutoff c ∧ (∀ n : ℕ, cutoff c ≤ n → WeakCell c n) := by
  exact ⟨aux_cutoff_pos c, fun n hn => aux_weakCell_of_cutoff hc hn⟩

theorem scales {c : ℝ} (hc : 0 < c) :
    Tendsto (height c) atTop atTop ∧
    Tendsto (fun n : ℕ => (n : ℝ) / height c n ^ 2) atTop atTop := by
  exact ⟨aux_height_tendsto_atTop hc, aux_square_scale_tendsto_atTop hc⟩

theorem scales_on_strict_subsequence {c : ℝ} (hc : 0 < c)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) :
    Tendsto (fun j => height c (σ j)) atTop atTop ∧
    Tendsto (fun j => (σ j : ℝ) / height c (σ j) ^ 2) atTop atTop ∧
    (∀ᶠ j in atTop, cutoff c ≤ σ j ∧ WeakCell c (σ j) ∧
      1 ≤ σ j ∧ 0 < height c (σ j) ∧
      (σ j : ℝ) / height c (σ j) ^ 3 = 1 / c ^ 3 ∧ 0 < 1 / c ^ 3) := by
  refine ⟨(aux_height_tendsto_atTop hc).comp hσ.tendsto_atTop,
    (aux_square_scale_tendsto_atTop hc).comp hσ.tendsto_atTop, ?_⟩
  filter_upwards [eventually_ge_atTop (cutoff c)] with j hj
  have hcut : cutoff c ≤ σ j := le_trans hj (aux_strict_index_id_le hσ j)
  have hn : 1 ≤ σ j := le_trans (aux_cutoff_pos c) hcut
  exact ⟨hcut, aux_weakCell_of_cutoff hc hcut, hn, aux_height_pos hc hn,
    (aux_time_scale hc hn).1, (aux_time_scale hc hn).2⟩

theorem exact_cube {k : ℕ} (hk : 1 ≤ k) :
    WeakCell 1 (cubeIndex k) ∧ height 1 (cubeIndex k) = (k : ℝ) ∧
    phaseFloor 1 (cubeIndex k) = k ∧ upperHeight 1 (cubeIndex k) = (k : ℝ) + 1 ∧
    delta 1 (cubeIndex k) = 1 := by
  obtain ⟨hh, hm, hH, hδ⟩ := aux_exact_cube k
  exact ⟨aux_exact_cube_weakCell hk, hh, hm, hH, hδ⟩

theorem exact_below_cube {k : ℕ} (hk : 2 ≤ k) :
    1 ≤ belowCubeIndex k ∧
    (belowCubeIndex k : ℤ) = (k : ℤ) ^ 3 - 1 ∧
    (belowCubeIndex k : ℝ) = (k : ℝ) ^ 3 - 1 ∧
    ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 ∧
    ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 ∧
    WeakCell 1 (belowCubeIndex k) ∧
    (k : ℝ) - 1 < height 1 (belowCubeIndex k) ∧
    height 1 (belowCubeIndex k) < (k : ℝ) ∧
    phaseFloor 1 (belowCubeIndex k) = k - 1 ∧
    upperHeight 1 (belowCubeIndex k) = (k : ℝ) ∧
    delta 1 (belowCubeIndex k) = (k : ℝ) - height 1 (belowCubeIndex k) := by
  obtain ⟨hn, hcast, hlo, hhi, hm, hH, hδ⟩ := aux_exact_below_cube hk
  have hk1 : 1 ≤ k := by omega
  have hkp : 1 ≤ k ^ 3 := Nat.succ_le_iff.mpr (pow_pos (by omega : 0 < k) 3)
  have hcastZ : (belowCubeIndex k : ℤ) = (k : ℤ) ^ 3 - 1 := by
    simp only [belowCubeIndex, Nat.cast_sub hkp, Nat.cast_pow, Nat.cast_one]
  have hkmZ : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
    simp only [Nat.cast_sub hk1, Nat.cast_one]
  have hkmR : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    simp only [Nat.cast_sub hk1, Nat.cast_one]
  exact ⟨hn, hcastZ, hcast, hkmZ, hkmR, aux_exact_below_cube_weakCell hk,
    hlo, hhi, hm, hH, hδ⟩

theorem cube_subsequence :
    StrictMono (fun j : ℕ => cubeIndex (j + 1)) ∧
    (∀ j : ℕ, cutoff 1 ≤ cubeIndex (j + 1) ∧ WeakCell 1 (cubeIndex (j + 1))) ∧
    Tendsto (fun j : ℕ => delta 1 (cubeIndex (j + 1))) atTop (𝓝 1) ∧
    Tendsto (fun j : ℕ => exponent 1 (cubeIndex (j + 1))) atTop (𝓝 (Real.pi ^ 2 / 4)) ∧
    Tendsto (fun j : ℕ => factor 1 (cubeIndex (j + 1))) atTop
      (𝓝 (Real.exp (Real.pi ^ 2 / 4))) := by
  obtain ⟨hs, hl, hE, hF⟩ := aux_exact_cube_subsequence
  exact ⟨hs, fun j => ⟨hl j, aux_weakCell_of_cutoff (by norm_num) (hl j)⟩,
    aux_exact_cube_delta_subsequence, hE, hF⟩

theorem below_cube_subsequence :
    Tendsto (fun k : ℕ => delta 1 (belowCubeIndex k)) atTop (𝓝 0) ∧
    StrictMono (fun j : ℕ => belowCubeIndex (j + 2)) ∧
    (∀ j : ℕ, cutoff 1 ≤ belowCubeIndex (j + 2) ∧ WeakCell 1 (belowCubeIndex (j + 2))) ∧
    Tendsto (fun j : ℕ => delta 1 (belowCubeIndex (j + 2))) atTop (𝓝 0) ∧
    Tendsto (fun j : ℕ => exponent 1 (belowCubeIndex (j + 2))) atTop (𝓝 0) ∧
    Tendsto (fun j : ℕ => factor 1 (belowCubeIndex (j + 2))) atTop (𝓝 1) := by
  obtain ⟨hs, hl, hE, hF⟩ := aux_exact_below_cube_subsequence
  exact ⟨aux_below_cube_delta_limit, hs,
    fun j => ⟨hl j, aux_weakCell_of_cutoff (by norm_num) (hl j)⟩,
    aux_exact_below_cube_delta_subsequence, hE, hF⟩

theorem up_rounding {c : ℝ} (hc : 0 < c) :
    upIndex c 0 = 0 ∧
    (∀ k : ℕ, 0 ≤ (upIndex c k : ℝ) - target c 0 k ∧
      (upIndex c k : ℝ) - target c 0 k < 1) := by
  exact ⟨aux_up_zero c, fun k => aux_up_error hc k⟩

theorem down_rounding {c : ℝ} (hc : 0 < c) :
    downIndex c 0 = 0 ∧
    (∀ k : ℕ, 1 ≤ k → 1 ≤ upIndex c k ∧
      (downIndex c k : ℤ) = (upIndex c k : ℤ) - 1 ∧
      (downIndex c k : ℝ) = (upIndex c k : ℝ) - 1 ∧
      -1 ≤ (downIndex c k : ℝ) - target c 0 k ∧
      (downIndex c k : ℝ) - target c 0 k < 0) := by
  refine ⟨aux_down_zero c, ?_⟩
  intro k hk
  have hp := aux_up_positive hc hk
  refine ⟨hp, ?_, aux_down_cast hc hk, (aux_down_error hc hk).1,
    (aux_down_error hc hk).2⟩
  change ((upIndex c k - 1 : ℕ) : ℤ) = (upIndex c k : ℤ) - 1
  rw [Nat.cast_sub hp, Nat.cast_one]

theorem nearest_rounding {c α : ℝ} (hc : 0 < c) (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ k : ℕ, -(1 / 2 : ℝ) < (nearestIndex c α k : ℝ) - target c α k ∧
      (nearestIndex c α k : ℝ) - target c α k ≤ 1 / 2 ∧
      |(nearestIndex c α k : ℝ) - target c α k| ≤ 1 / 2 ∧
      (∀ l : ℕ, target c α k = (l : ℝ) + 1 / 2 → nearestIndex c α k = l + 1) := by
  intro k
  obtain ⟨hlo, hhi, habs⟩ := aux_nearest_error hc hα0 k
  exact ⟨hlo, hhi, habs, fun l ht => aux_nearest_tie_up ht⟩

theorem up_phase {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k : ℕ => height c (upIndex c k) - (k : ℝ)) atTop (𝓝 0) ∧
    (∀ᶠ (k : ℕ) in atTop, 1 ≤ k ∧ (k : ℝ) ≤ height c (upIndex c k) ∧
      height c (upIndex c k) < (k : ℝ) + 1 ∧ phaseFloor c (upIndex c k) = k) ∧
    Tendsto (fun k : ℕ => delta c (upIndex c k)) atTop (𝓝 1) := by
  exact ⟨aux_up_height_error hc, aux_up_stable hc, aux_up_delta_limit hc⟩

theorem down_phase {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k : ℕ => height c (downIndex c k) - (k : ℝ)) atTop (𝓝 0) ∧
    (∀ᶠ k in atTop, 2 ≤ k ∧ ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 ∧
      ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 ∧
      (k : ℝ) - 1 < height c (downIndex c k) ∧
      height c (downIndex c k) < (k : ℝ) ∧ phaseFloor c (downIndex c k) = k - 1) ∧
    Tendsto (fun k : ℕ => delta c (downIndex c k)) atTop (𝓝 0) := by
  refine ⟨aux_down_height_error hc, ?_, aux_down_delta_limit hc⟩
  filter_upwards [aux_down_stable hc] with k hk
  have hk2 : 2 ≤ k := hk.1
  have hk1 : 1 ≤ k := by omega
  have hkmZ : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
    simp only [Nat.cast_sub hk1, Nat.cast_one]
  have hkmR : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    simp only [Nat.cast_sub hk1, Nat.cast_one]
  exact ⟨hk2, hkmZ, hkmR, hk.2.1, hk.2.2.1, hk.2.2.2⟩

theorem nearest_phase {c α : ℝ} (hc : 0 < c) (hα0 : 0 < α) (hα1 : α < 1) :
    Tendsto (fun k : ℕ => height c (nearestIndex c α k) - ((k : ℝ) + α))
      atTop (𝓝 0) ∧
    (∀ᶠ (k : ℕ) in atTop, (k : ℝ) < height c (nearestIndex c α k) ∧
      height c (nearestIndex c α k) < (k : ℝ) + 1 ∧ phaseFloor c (nearestIndex c α k) = k) ∧
    Tendsto (fun k : ℕ => delta c (nearestIndex c α k)) atTop (𝓝 (1 - α)) := by
  exact ⟨aux_nearest_height_error hc hα0, aux_nearest_stable hc hα0 hα1,
    aux_nearest_delta_limit hc hα0 hα1⟩

theorem up_subsequence {c : ℝ} (hc : 0 < c) :
    ∃ K : ℕ, 1 ≤ K ∧ StrictMono (fun j : ℕ => upIndex c (j + K)) ∧
      (∀ j : ℕ, cutoff c ≤ upIndex c (j + K) ∧ WeakCell c (upIndex c (j + K))) ∧
      Tendsto (fun j : ℕ => delta c (upIndex c (j + K))) atTop (𝓝 1) ∧
      Tendsto (fun j : ℕ => exponent c (upIndex c (j + K))) atTop (𝓝 (q c)) ∧
      Tendsto (fun j : ℕ => factor c (upIndex c (j + K))) atTop (𝓝 (Real.exp (q c))) := by
  obtain ⟨K, hK, hs, hl, hP, hδ, hE, hF⟩ := aux_up_subsequence hc
  refine ⟨K, by omega, hs, fun j => ⟨hl j, aux_weakCell_of_cutoff hc (hl j)⟩,
    hδ, ?_, ?_⟩
  · simpa only [mul_one] using hE
  · simpa only [mul_one] using hF

theorem down_subsequence {c : ℝ} (hc : 0 < c) :
    ∃ K : ℕ, 2 ≤ K ∧ StrictMono (fun j : ℕ => downIndex c (j + K)) ∧
      (∀ j : ℕ, cutoff c ≤ downIndex c (j + K) ∧ WeakCell c (downIndex c (j + K))) ∧
      Tendsto (fun j : ℕ => delta c (downIndex c (j + K))) atTop (𝓝 0) ∧
      Tendsto (fun j : ℕ => exponent c (downIndex c (j + K))) atTop (𝓝 0) ∧
      Tendsto (fun j : ℕ => factor c (downIndex c (j + K))) atTop (𝓝 1) := by
  obtain ⟨K, hK, hs, hl, hP, hδ, hE, hF⟩ := aux_down_subsequence hc
  refine ⟨K, hK, hs, fun j => ⟨hl j, aux_weakCell_of_cutoff hc (hl j)⟩,
    hδ, ?_, ?_⟩
  · simpa only [mul_zero] using hE
  · simpa only [mul_zero, Real.exp_zero] using hF

theorem nearest_subsequence {c α : ℝ} (hc : 0 < c) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ K : ℕ, 1 ≤ K ∧ StrictMono (fun j : ℕ => nearestIndex c α (j + K)) ∧
      (∀ j : ℕ, cutoff c ≤ nearestIndex c α (j + K) ∧ WeakCell c (nearestIndex c α (j + K))) ∧
      Tendsto (fun j : ℕ => delta c (nearestIndex c α (j + K))) atTop (𝓝 (1 - α)) ∧
      Tendsto (fun j : ℕ => exponent c (nearestIndex c α (j + K))) atTop (𝓝 (q c * (1 - α))) ∧
      Tendsto (fun j : ℕ => factor c (nearestIndex c α (j + K))) atTop
        (𝓝 (Real.exp (q c * (1 - α)))) := by
  obtain ⟨K, hK, hs, hl, hP, hδ, hE, hF⟩ := aux_nearest_subsequence hc hα0 hα1
  exact ⟨K, by omega, hs, fun j => ⟨hl j, aux_weakCell_of_cutoff hc (hl j)⟩,
    hδ, hE, hF⟩

private theorem aux_actual_phase_tail {c d : ℝ} (hc : 0 < c)
    (hd : d ∈ Set.Icc (0 : ℝ) 1) :
    ∃ K : ℕ, 2 ≤ K ∧ StrictMono (fun j : ℕ => phaseIndex c d (j + K)) ∧
      (∀ j : ℕ, cutoff c ≤ phaseIndex c d (j + K)) ∧
      Tendsto (fun j : ℕ => delta c (phaseIndex c d (j + K))) atTop (𝓝 d) ∧
      Tendsto (fun j : ℕ => exponent c (phaseIndex c d (j + K))) atTop (𝓝 (q c * d)) ∧
      Tendsto (fun j : ℕ => factor c (phaseIndex c d (j + K))) atTop (𝓝 (Real.exp (q c * d))) := by
  classical
  by_cases h0 : d = 0
  · subst d
    obtain ⟨K, hK, hs, hl, hP, hδ, hE, hF⟩ := aux_down_subsequence hc
    refine ⟨K, hK, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [phaseIndex] using hs
    · simpa [phaseIndex] using hl
    · simpa [phaseIndex] using hδ
    · simpa [phaseIndex] using hE
    · simpa [phaseIndex] using hF
  by_cases h1 : d = 1
  · subst d
    obtain ⟨K, hK, hs, hl, hP, hδ, hE, hF⟩ := aux_up_subsequence hc
    refine ⟨K, hK, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [phaseIndex] using hs
    · simpa [phaseIndex] using hl
    · simpa [phaseIndex] using hδ
    · simpa [phaseIndex] using hE
    · simpa [phaseIndex] using hF
  have hd0 : 0 < d := lt_of_le_of_ne hd.1 (Ne.symm h0)
  have hd1 : d < 1 := lt_of_le_of_ne hd.2 h1
  have ha0 : 0 < 1 - d := by linarith
  have ha1 : 1 - d < 1 := by linarith
  have hid : 1 - (1 - d) = d := by ring
  obtain ⟨K, hK, hs, hl, hP, hδ, hE, hF⟩ := aux_nearest_subsequence hc ha0 ha1
  refine ⟨K, hK, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [phaseIndex, h0, h1] using hs
  · simpa [phaseIndex, h0, h1] using hl
  · simpa [phaseIndex, h0, h1, hid] using hδ
  · simpa [phaseIndex, h0, h1, hid] using hE
  · simpa [phaseIndex, h0, h1, hid] using hF

theorem phase_realization {c d : ℝ} (hc : 0 < c) (hd : d ∈ Set.Icc (0 : ℝ) 1) :
    ∃ K : ℕ, 2 ≤ K ∧ StrictMono (fun j : ℕ => phaseIndex c d (j + K)) ∧
      (∀ j : ℕ, cutoff c ≤ phaseIndex c d (j + K) ∧
        WeakCell c (phaseIndex c d (j + K)) ∧ 1 ≤ phaseIndex c d (j + K) ∧
        0 < height c (phaseIndex c d (j + K)) ∧
        (phaseIndex c d (j + K) : ℝ) / height c (phaseIndex c d (j + K)) ^ 3 = 1 / c ^ 3 ∧
        0 < 1 / c ^ 3) ∧
      Tendsto (fun j : ℕ => delta c (phaseIndex c d (j + K))) atTop (𝓝 d) ∧
      Tendsto (fun j : ℕ => exponent c (phaseIndex c d (j + K))) atTop (𝓝 (q c * d)) ∧
      Tendsto (fun j : ℕ => factor c (phaseIndex c d (j + K))) atTop (𝓝 (Real.exp (q c * d))) := by
  obtain ⟨K, hK, hs, hl, hδ, hE, hF⟩ := aux_actual_phase_tail hc hd
  refine ⟨K, hK, hs, ?_, hδ, hE, hF⟩
  intro j
  have hcut := hl j
  have hn : 1 ≤ phaseIndex c d (j + K) := le_trans (aux_cutoff_pos c) hcut
  exact ⟨hcut, aux_weakCell_of_cutoff hc hcut, hn, aux_height_pos hc hn,
    (aux_time_scale hc hn).1, (aux_time_scale hc hn).2⟩

theorem cluster_sets {c : ℝ} (hc : 0 < c) :
    Cluster (delta c) = Set.Icc (0 : ℝ) 1 ∧
    Cluster (exponent c) = Set.Icc (0 : ℝ) (q c) ∧
    Cluster (factor c) = Set.Icc (1 : ℝ) (Real.exp (q c)) := by
  exact ⟨aux_cluster_delta hc, aux_cluster_exponent hc, aux_cluster_factor hc⟩

theorem not_convergent {c : ℝ} (hc : 0 < c) :
    (¬ ∃ L : ℝ, Tendsto (delta c) atTop (𝓝 L)) ∧
    (¬ ∃ L : ℝ, Tendsto (exponent c) atTop (𝓝 L)) ∧
    (¬ ∃ L : ℝ, Tendsto (factor c) atTop (𝓝 L)) := by
  exact ⟨aux_delta_not_convergent hc, aux_exponent_not_convergent hc,
    aux_factor_not_convergent hc⟩

end Shao.OQ4.RademacherCriticalPhase
