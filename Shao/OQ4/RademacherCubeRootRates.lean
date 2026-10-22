/-
Local implementation candidate for the frozen R1/R2 public interface.
The two transparent definitions and four public types are unchanged.
Proof source: the explicitly released anonymous cube-root-rate proof.
Only CP transparent definitions and public heads are consumed.
No Lean execution or mechanical verification has been performed in this stage.
-/
import Shao.OQ4.RademacherCriticalPhase
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

namespace Shao.OQ4.RademacherCubeRootRates

open Shao.OQ4.RademacherCriticalPhase

/-- Exact positive-constant tail meaning of the R1 O(k⁻⁵) remainder. -/
def BelowCubeBigO (C : ℝ) (k₀ : ℕ) : Prop :=
  0 < C ∧
  ∀ k : ℕ, k₀ ≤ k →
    |root (belowCubeIndex k) -
      ((k : ℝ) - 1 / (3 * (k : ℝ) ^ 2))| ≤ C / (k : ℝ) ^ 5

/-- Exact positive-constant tail meaning of the R2 O(k⁻²) remainder. -/
def NearestCubeBigO (α C : ℝ) (k₀ : ℕ) : Prop :=
  0 < C ∧
  ∀ k : ℕ, k₀ ≤ k →
    |root (nearestIndex 1 α k) - ((k : ℝ) + α)| ≤ C / (k : ℝ) ^ 2


private theorem below_cube_error {K r : ℝ} (hK : 2 ≤ K)
    (hr : 0 ≤ r) (hr3 : r ^ 3 = K ^ 3 - 1) :
    |r - (K - 1 / (3 * K ^ 2))| ≤ 1 / K ^ 5 := by
  have hKpos : 0 < K := by linarith
  have hKne : K ≠ 0 := ne_of_gt hKpos
  have hK3 : 8 ≤ K ^ 3 := by
    have hp := mul_nonneg (sub_nonneg.mpr hK) (sq_nonneg (K + 1))
    nlinarith [hp]
  let a : ℝ := K - 1 / (3 * K ^ 2)
  let D : ℝ := a ^ 2 + a * r + r ^ 2
  have hshift : 1 / (3 * K ^ 2) ≤ K / 3 := by
    apply (div_le_iff₀ (show 0 < 3 * K ^ 2 by positivity)).2
    nlinarith [hK3]
  have halower : 2 * K / 3 ≤ a := by
    dsimp only [a]
    linarith
  have ha0 : 0 ≤ a := by linarith
  have ha2 : 4 * K ^ 2 / 9 ≤ a ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr halower)
      (show 0 ≤ a + 2 * K / 3 by linarith)
    nlinarith [hp]
  have hDlower : K ^ 2 / 3 ≤ D := by
    dsimp only [D]
    nlinarith [sq_nonneg r, sq_nonneg K, mul_nonneg ha0 hr]
  have hDpos : 0 < D := by
    have hK2pos : 0 < K ^ 2 := by positivity
    linarith
  have hB :
      a ^ 3 - r ^ 3 = 1 / (3 * K ^ 3) - 1 / (27 * K ^ 6) := by
    rw [hr3]
    dsimp only [a]
    field_simp [hKne] <;> ring
  have hBfraction :
      a ^ 3 - r ^ 3 = (9 * K ^ 3 - 1) / (27 * K ^ 6) := by
    rw [hB]
    field_simp [hKne] <;> ring
  have hBnonneg : 0 ≤ a ^ 3 - r ^ 3 := by
    rw [hBfraction]
    exact div_nonneg (by nlinarith [hK3]) (by positivity)
  have hBupper : a ^ 3 - r ^ 3 ≤ 1 / (3 * K ^ 3) := by
    rw [hB]
    have hq : 0 ≤ 1 / (27 * K ^ 6) := by positivity
    linarith
  have hfactor : a ^ 3 - r ^ 3 = (a - r) * D := by
    dsimp only [D]
    ring
  have hrle : r ≤ a := by
    by_contra h
    have hneg : a - r < 0 := by linarith
    have hprodneg : (a - r) * D < 0 :=
      mul_neg_of_neg_of_pos hneg hDpos
    have hprodnonneg : 0 ≤ (a - r) * D := by
      rw [← hfactor]
      exact hBnonneg
    linarith
  have hscaled : (a - r) * (K ^ 2 / 3) ≤ 1 / (3 * K ^ 3) := by
    calc
      (a - r) * (K ^ 2 / 3) ≤ (a - r) * D :=
        mul_le_mul_of_nonneg_left hDlower (sub_nonneg.mpr hrle)
      _ = a ^ 3 - r ^ 3 := hfactor.symm
      _ ≤ 1 / (3 * K ^ 3) := hBupper
  have hratio : (1 / (3 * K ^ 3)) / (K ^ 2 / 3) = 1 / K ^ 5 := by
    field_simp [hKne] <;> ring
  have herr : a - r ≤ 1 / K ^ 5 := by
    rw [← hratio]
    exact (le_div_iff₀ (show 0 < K ^ 2 / 3 by positivity)).2 hscaled
  change |r - a| ≤ 1 / K ^ 5
  rw [abs_of_nonpos (sub_nonpos.mpr hrle)]
  linarith

private theorem nearest_cube_error {K t r : ℝ} (hK : 2 ≤ K)
    (ht : K ≤ t) (hr : 0 ≤ r) (hcube : |r ^ 3 - t ^ 3| ≤ (1 : ℝ) / 2) :
    |r - t| ≤ 1 / (2 * K ^ 2) := by
  have hKpos : 0 < K := by linarith
  have ht0 : 0 ≤ t := by linarith
  let D : ℝ := r ^ 2 + r * t + t ^ 2
  have ht2 : K ^ 2 ≤ t ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr ht)
      (show 0 ≤ t + K by linarith)
    nlinarith [hp]
  have hDlower : K ^ 2 ≤ D := by
    dsimp only [D]
    nlinarith [sq_nonneg r, mul_nonneg hr ht0]
  have hDpos : 0 < D := by
    have hK2pos : 0 < K ^ 2 := by positivity
    linarith
  have hfactor : (r - t) * D = r ^ 3 - t ^ 3 := by
    dsimp only [D]
    ring
  have habsfactor : |r - t| * D = |r ^ 3 - t ^ 3| := by
    rw [← hfactor, abs_mul, abs_of_pos hDpos]
  have hscaled : |r - t| * K ^ 2 ≤ (1 : ℝ) / 2 := by
    calc
      |r - t| * K ^ 2 ≤ |r - t| * D :=
        mul_le_mul_of_nonneg_left hDlower (abs_nonneg _)
      _ = |r ^ 3 - t ^ 3| := habsfactor
      _ ≤ (1 : ℝ) / 2 := hcube
  have herr : |r - t| ≤ ((1 : ℝ) / 2) / K ^ 2 :=
    (le_div_iff₀ (show 0 < K ^ 2 by positivity)).2 hscaled
  simpa only [div_div] using herr

/- BEGIN_PUBLIC_HEAD below_cube_finite -/
theorem below_cube_finite {k : ℕ} (hk : 2 ≤ k) :
    (belowCubeIndex k : ℝ) = (k : ℝ) ^ 3 - 1 ∧
    1 ≤ belowCubeIndex k ∧
    0 ≤ root (belowCubeIndex k) ∧
    root (belowCubeIndex k) ^ 3 = (k : ℝ) ^ 3 - 1 ∧
    height 1 (belowCubeIndex k) = root (belowCubeIndex k) ∧
    |root (belowCubeIndex k) -
      ((k : ℝ) - 1 / (3 * (k : ℝ) ^ 2))| ≤ 1 / (k : ℝ) ^ 5
/- END_PUBLIC_HEAD below_cube_finite -/
    := by
  have hK : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hindex := exact_below_cube hk
  have hcast : (belowCubeIndex k : ℝ) = (k : ℝ) ^ 3 - 1 :=
    hindex.2.2.1
  have hroot := root_spec (belowCubeIndex k)
  have hcube : root (belowCubeIndex k) ^ 3 = (k : ℝ) ^ 3 - 1 :=
    hroot.2.1.trans hcast
  refine ⟨hcast, hindex.1, hroot.1, hcube, ?_, ?_⟩
  · simp only [height, one_mul]
  · exact below_cube_error hK hroot.1 hcube

/- BEGIN_PUBLIC_HEAD below_cube_bigO -/
theorem below_cube_bigO :
    ∃ C : ℝ, ∃ k₀ : ℕ,
      C = 1 ∧ k₀ = 2 ∧ 0 < C ∧ BelowCubeBigO C k₀
/- END_PUBLIC_HEAD below_cube_bigO -/
    := by
  refine ⟨1, 2, rfl, rfl, by norm_num, ?_⟩
  refine ⟨by norm_num, ?_⟩
  intro k hk
  rcases below_cube_finite hk with ⟨_, _, _, _, _, herr⟩
  simpa only [one_div] using herr

/- BEGIN_PUBLIC_HEAD nearest_cube_finite -/
theorem nearest_cube_finite {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {k : ℕ} (hk : 2 ≤ k) :
    nearestIndex 1 α k = Nat.floor (((k : ℝ) + α) ^ 3 + (1 : ℝ) / 2) ∧
    0 < (k : ℝ) + α ∧
    1 ≤ nearestIndex 1 α k ∧
    0 ≤ root (nearestIndex 1 α k) ∧
    root (nearestIndex 1 α k) ^ 3 = (nearestIndex 1 α k : ℝ) ∧
    height 1 (nearestIndex 1 α k) = root (nearestIndex 1 α k) ∧
    -(1 / 2 : ℝ) < (nearestIndex 1 α k : ℝ) - ((k : ℝ) + α) ^ 3 ∧
    (nearestIndex 1 α k : ℝ) - ((k : ℝ) + α) ^ 3 ≤ (1 : ℝ) / 2 ∧
    |(nearestIndex 1 α k : ℝ) - ((k : ℝ) + α) ^ 3| ≤ (1 : ℝ) / 2 ∧
    (∀ l : ℕ, ((k : ℝ) + α) ^ 3 = (l : ℝ) + (1 : ℝ) / 2 →
      nearestIndex 1 α k = l + 1) ∧
    |root (nearestIndex 1 α k) - ((k : ℝ) + α)| ≤
      1 / (2 * (k : ℝ) ^ 2)
/- END_PUBLIC_HEAD nearest_cube_finite -/
    := by
  have hK : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have ht : 0 < (k : ℝ) + α := by linarith
  have htK : (k : ℝ) ≤ (k : ℝ) + α := by linarith
  have ht2 : (2 : ℝ) ≤ (k : ℝ) + α := by linarith
  have ht3 : 8 ≤ ((k : ℝ) + α) ^ 3 := by
    have hp := mul_nonneg (sub_nonneg.mpr ht2)
      (sq_nonneg ((k : ℝ) + α + 1))
    nlinarith [hp]
  have hround := nearest_rounding (c := (1 : ℝ)) (α := α)
    (by norm_num) hα0 hα1 k
  have hlower :
      -(1 / 2 : ℝ) < (nearestIndex 1 α k : ℝ) - ((k : ℝ) + α) ^ 3 := by
    simpa only [target, div_one] using hround.1
  have hupper :
      (nearestIndex 1 α k : ℝ) - ((k : ℝ) + α) ^ 3 ≤ (1 : ℝ) / 2 := by
    simpa only [target, div_one] using hround.2.1
  have hhalf :
      |(nearestIndex 1 α k : ℝ) - ((k : ℝ) + α) ^ 3| ≤ (1 : ℝ) / 2 := by
    simpa only [target, div_one] using hround.2.2.1
  have hties :
      ∀ l : ℕ, ((k : ℝ) + α) ^ 3 = (l : ℝ) + (1 : ℝ) / 2 →
        nearestIndex 1 α k = l + 1 := by
    intro l hl
    apply hround.2.2.2 l
    simpa only [target, div_one] using hl
  have hncast : 0 < (nearestIndex 1 α k : ℝ) := by
    nlinarith [ht3]
  have hn : 1 ≤ nearestIndex 1 α k := by
    have hnne : nearestIndex 1 α k ≠ 0 := by
      intro hz
      rw [hz] at hncast
      norm_num at hncast
    exact Nat.pos_of_ne_zero hnne
  have hroot := root_spec (nearestIndex 1 α k)
  have hcube :
      |root (nearestIndex 1 α k) ^ 3 - ((k : ℝ) + α) ^ 3| ≤ (1 : ℝ) / 2 := by
    rw [hroot.2.1]
    exact hhalf
  refine ⟨?_, ht, hn, hroot.1, hroot.2.1, ?_, hlower, hupper, hhalf, hties, ?_⟩
  · simp only [nearestIndex, target, div_one]
  · simp only [height, one_mul]
  · exact nearest_cube_error hK htK hroot.1 hcube

/- BEGIN_PUBLIC_HEAD nearest_cube_bigO -/
theorem nearest_cube_bigO {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, ∃ k₀ : ℕ,
      C = (1 : ℝ) / 2 ∧ k₀ = 2 ∧ 0 < C ∧ NearestCubeBigO α C k₀
/- END_PUBLIC_HEAD nearest_cube_bigO -/
    := by
  refine ⟨(1 : ℝ) / 2, 2, rfl, rfl, by norm_num, ?_⟩
  refine ⟨by norm_num, ?_⟩
  intro k hk
  rcases nearest_cube_finite hα0 hα1 hk with
    ⟨_, _, _, _, _, _, _, _, _, _, herr⟩
  simpa only [div_div] using herr

end Shao.OQ4.RademacherCubeRootRates

end
