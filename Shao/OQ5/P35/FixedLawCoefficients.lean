import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fixed category coefficients for the p35 construction

Source: `current/oq56/inputs02/p35.md`, §3, lines 66–101.
The law and all coefficients are fixed independently of the eventual sample size.
This component proves the exact discrete series and the offset bounds; it does
not yet construct the probability measure or the independent uniform variable.
-/

namespace Shao.OQ5.P35
noncomputable section

/-- The masses of the fixed category law in p35 §3. -/
def categoryMass (c : ℕ) : ℝ :=
  if c = 0 then 16382 / 16383 else (1 / 16384 : ℝ)^c

def categoryScale (c : ℕ) : ℝ := (4 : ℝ)^c

def categoryValue (c : ℕ) : ℝ := if c = 0 then 0 else (32 : ℝ)^c

def featureMean : ℝ := 1 / 511

def categoryFeature (c : ℕ) : ℝ := categoryValue c - featureMean

def categoryOffset (c : ℕ) : ℝ :=
  if c = 0 then 0 else
    (categoryScale c - 1) * (categoryFeature c)^2 / ((categoryScale c)^4 - 2)

@[simp] theorem categoryMass_zero : categoryMass 0 = 16382 / 16383 := by
  simp [categoryMass]

@[simp] theorem categoryMass_succ (c : ℕ) :
    categoryMass (c + 1) = (1 / 16384 : ℝ) ^ (c + 1) := by
  simp [categoryMass]

@[simp] theorem categoryValue_zero : categoryValue 0 = 0 := by
  simp [categoryValue]

@[simp] theorem categoryValue_succ (c : ℕ) :
    categoryValue (c + 1) = (32 : ℝ) ^ (c + 1) := by
  simp [categoryValue]

@[simp] theorem categoryOffset_zero : categoryOffset 0 = 0 := by
  simp [categoryOffset]

theorem categoryMass_pos (c : ℕ) : 0 < categoryMass c := by
  unfold categoryMass
  split_ifs <;> positivity

theorem categoryMass_nonneg (c : ℕ) : 0 ≤ categoryMass c :=
  (categoryMass_pos c).le

private theorem hasSum_geometric_succ {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    HasSum (fun c : ℕ => q ^ (c + 1)) (q / (1 - q)) := by
  simpa [pow_succ', div_eq_mul_inv] using
    (hasSum_geometric_of_lt_one h0 h1).mul_left q

theorem hasSum_categoryMass : HasSum categoryMass 1 := by
  apply (hasSum_nat_add_iff' 1).mp
  have h := hasSum_geometric_succ (q := (1 / 16384 : ℝ)) (by norm_num) (by norm_num)
  norm_num at h
  convert h using 1 <;> norm_num [categoryMass]

theorem hasSum_mass_value :
    HasSum (fun c => categoryMass c * categoryValue c) (1 / 511) := by
  apply (hasSum_nat_add_iff' 1).mp
  have h := hasSum_geometric_succ (q := (1 / 512 : ℝ)) (by norm_num) (by norm_num)
  norm_num at h
  convert h using 1
  · funext c
    simp only [categoryMass_succ, categoryValue_succ]
    rw [← mul_pow]
    norm_num
  · norm_num

theorem hasSum_mass_value_sq :
    HasSum (fun c => categoryMass c * categoryValue c ^ 2) (1 / 15) := by
  apply (hasSum_nat_add_iff' 1).mp
  have h := hasSum_geometric_succ (q := (1 / 16 : ℝ)) (by norm_num) (by norm_num)
  norm_num at h
  convert h using 1
  · funext c
    simp only [categoryMass_succ, categoryValue_succ]
    rw [← pow_mul, Nat.mul_comm (c + 1) 2, pow_mul, ← mul_pow]
    norm_num
  · norm_num

/-- On every positive category the value square is exactly the fifth scale power. -/
theorem categoryValue_sq_succ (c : ℕ) :
    categoryValue (c + 1) ^ 2 = categoryScale (c + 1) ^ 5 := by
  simp only [categoryValue_succ, categoryScale]
  calc
    ((32 : ℝ) ^ (c + 1)) ^ 2 = ((32 : ℝ) ^ 2) ^ (c + 1) := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm (c + 1) 2]
    _ = ((4 : ℝ) ^ 5) ^ (c + 1) := by norm_num
    _ = ((4 : ℝ) ^ (c + 1)) ^ 5 := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm (c + 1) 5]

theorem categoryScale_one_le (c : ℕ) : 1 ≤ categoryScale c := by
  exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4)

theorem categoryScale_succ_ge (c : ℕ) : 4 ≤ categoryScale (c + 1) := by
  dsimp [categoryScale]
  rw [pow_succ]
  have h := categoryScale_one_le c
  dsimp [categoryScale] at h
  linarith

theorem categoryValue_succ_ge (c : ℕ) : 32 ≤ categoryValue (c + 1) := by
  rw [categoryValue_succ, pow_succ]
  have h : (1 : ℝ) ≤ 32 ^ c := one_le_pow₀ (by norm_num)
  linarith

private theorem categoryScale_four_ge (c : ℕ) :
    4 ≤ categoryScale (c + 1) ^ 4 := by
  calc
    (4 : ℝ) ≤ 4 ^ 4 := by norm_num
    _ ≤ categoryScale (c + 1) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) (categoryScale_succ_ge c) 4

theorem categoryOffset_nonneg (c : ℕ) : 0 ≤ categoryOffset c := by
  cases c with
  | zero => simp
  | succ c =>
    simp only [categoryOffset, Nat.succ_ne_zero, ite_false]
    exact div_nonneg (mul_nonneg (by linarith [categoryScale_succ_ge c]) (sq_nonneg _))
      (by linarith [categoryScale_four_ge c])

theorem categoryOffset_le (c : ℕ) : categoryOffset c ≤ 2 * categoryScale c ^ 2 := by
  cases c with
  | zero => norm_num [categoryOffset, categoryScale]
  | succ c =>
    have hk := categoryScale_succ_ge c
    have hk4 := categoryScale_four_ge c
    have hv := categoryValue_succ_ge c
    have ht : categoryFeature (c + 1) ^ 2 ≤ categoryScale (c + 1) ^ 5 := by
      rw [← categoryValue_sq_succ]
      dsimp [categoryFeature, featureMean]
      nlinarith
    have hnum := mul_le_mul_of_nonneg_left ht (show 0 ≤ categoryScale (c + 1) - 1 by linarith)
    have haux := mul_nonneg (sq_nonneg (categoryScale (c + 1)))
      (show 0 ≤ categoryScale (c + 1) ^ 4 - 4 by linarith)
    have hk5 : 0 ≤ categoryScale (c + 1) ^ 5 := pow_nonneg (by linarith) 5
    simp only [categoryOffset, Nat.succ_ne_zero, ite_false]
    apply (div_le_iff₀ (by linarith [hk4] : 0 < categoryScale (c + 1) ^ 4 - 2)).mpr
    nlinarith

private theorem mass_scale_six_succ (c : ℕ) :
    categoryMass (c + 1) * categoryScale (c + 1) ^ 6 = (1 / 4 : ℝ) ^ (c + 1) := by
  simp only [categoryMass_succ, categoryScale]
  rw [← pow_mul, Nat.mul_comm (c + 1) 6, pow_mul, ← mul_pow]
  norm_num

theorem summable_mass_offset_pow (r : ℕ) (hr : r ≤ 3) :
    Summable (fun c => categoryMass c * categoryOffset c ^ r) := by
  apply (summable_nat_add_iff 1).mp
  have hgeom : Summable (fun c : ℕ => 8 * (1 / 4 : ℝ) ^ (c + 1)) :=
    (hasSum_geometric_succ (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)).summable.mul_left 8
  apply Summable.of_nonneg_of_le
    (fun c => mul_nonneg (categoryMass_nonneg _) (pow_nonneg (categoryOffset_nonneg _) _))
    (fun c => ?_) hgeom
  have hk := categoryScale_one_le (c + 1)
  have hk0 : 0 ≤ categoryScale (c + 1) := by linarith
  have hbase : 1 ≤ 2 * categoryScale (c + 1) ^ 2 := by nlinarith
  have hpow := (pow_le_pow_left₀ (categoryOffset_nonneg (c + 1)) (categoryOffset_le (c + 1)) r).trans
    (pow_le_pow_right₀ hbase hr)
  calc
    categoryMass (c + 1) * categoryOffset (c + 1) ^ r ≤
        categoryMass (c + 1) * (2 * categoryScale (c + 1) ^ 2) ^ 3 :=
      mul_le_mul_of_nonneg_left hpow (categoryMass_nonneg _)
    _ = 8 * (categoryMass (c + 1) * categoryScale (c + 1) ^ 6) := by ring
    _ = 8 * (1 / 4 : ℝ) ^ (c + 1) := by rw [mass_scale_six_succ]

end
end Shao.OQ5.P35
