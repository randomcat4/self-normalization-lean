import Shao.C2.IntervalSineHighTimeProfiles

noncomputable section
namespace Shao.C2.IntervalSineCosineSeries
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalSineTerms Shao.C2.IntervalSineSeries Shao.C2.IntervalSpectralGaussian

def integerCosineTerm (a T u : ℝ) (n : ℤ) : ℝ :=
  Real.exp (-(Real.pi ^ 2 * T / (8 * a ^ 2)) * (n : ℝ) ^ 2) *
    Real.cos (Real.pi * (n : ℝ) * u / (2 * a))

theorem integerCosineTerm_neg (a T u : ℝ) (n : ℤ) :
    integerCosineTerm a T u (-n) = integerCosineTerm a T u n := by
  dsimp only [integerCosineTerm]
  push_cast
  rw [neg_sq]
  have hp : Real.pi * -(n : ℝ) * u / (2 * a) = -(Real.pi * (n : ℝ) * u / (2 * a)) := by ring
  rw [hp, Real.cos_neg]

theorem integerCosineTerm_pos_summable (a T u : ℝ) (ha : 0 < a) (hT : 0 < T) :
    Summable (fun n : ℕ => integerCosineTerm a T u ((n : ℤ) + 1)) := by
  have hs := weightedGaussian_summable (Real.pi ^ 2 / 8) (T / a ^ 2) 0 (by positivity) (by positivity)
  apply hs.of_norm_bounded
  intro n
  have he : -(Real.pi ^ 2 * T / (8 * a ^ 2)) * ((((n : ℤ) + 1 : ℤ) : ℝ)) ^ 2 =
      -(Real.pi ^ 2 / 8) * ((n : ℝ) + 1) ^ 2 * (T / a ^ 2) := by
    push_cast
    field_simp [ne_of_gt ha] <;> ring
  rw [Real.norm_eq_abs, integerCosineTerm, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-(Real.pi ^ 2 * T / (8 * a ^ 2)) * ((((n : ℤ) + 1 : ℤ) : ℝ)) ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
    _ = _ := by dsimp only [weightedGaussian]; rw [he]; simp only [pow_zero, one_mul, mul_one]

theorem integerCosineTerm_hasSum (a T u : ℝ) (ha : 0 < a) (hT : 0 < T) :
    HasSum (integerCosineTerm a T u)
      (1 + 2 * (∑' n : ℕ, integerCosineTerm a T u ((n : ℤ) + 1))) := by
  have hs := integerCosineTerm_pos_summable a T u ha hT
  let S := ∑' n : ℕ, integerCosineTerm a T u ((n : ℤ) + 1)
  have hp : HasSum (fun n : ℕ => integerCosineTerm a T u ((n + 1 : ℕ) : ℤ)) S := by
    simpa only [Nat.cast_add, Nat.cast_one] using hs.hasSum
  have hNat := HasSum.zero_add (f := fun n : ℕ => integerCosineTerm a T u (n : ℤ)) hp
  have hNeg : HasSum (fun n : ℕ => integerCosineTerm a T u (-((n : ℤ) + 1))) S := by
    have heq : (fun n : ℕ => integerCosineTerm a T u (-((n : ℤ) + 1))) =
        (fun n : ℕ => integerCosineTerm a T u ((n : ℤ) + 1)) := by
      funext n
      exact integerCosineTerm_neg a T u ((n : ℤ) + 1)
    rw [heq]
    exact hs.hasSum
  have hAll := HasSum.of_nat_of_neg_add_one (f := integerCosineTerm a T u) hNat hNeg
  have hz : integerCosineTerm a T u 0 = 1 := by simp [integerCosineTerm]
  change HasSum (integerCosineTerm a T u) (1 + 2 * S)
  have hv : integerCosineTerm a T u (0 : ℤ) + S + S = 1 + 2 * S := by
    rw [hz]
    ring
  rw [← hv]
  exact hAll

theorem integerCosineTerm_summable (a T u : ℝ) (ha : 0 < a) (hT : 0 < T) :
    Summable (integerCosineTerm a T u) := by
  exact (integerCosineTerm_hasSum a T u ha hT).summable

theorem sineTerm_cosine_difference (a z T y : ℝ) (n : ℕ) (ha : 0 < a) :
    sineTerm a z T y n = (1 / (2 * a)) *
      (integerCosineTerm a T (z - y) ((n : ℤ) + 1) -
        integerCosineTerm a T (z + y + 2 * a) ((n : ℤ) + 1)) := by
  have hn : ((((n : ℤ) + 1 : ℤ) : ℝ)) = (n : ℝ) + 1 := by push_cast; rfl
  have he : -(Real.pi ^ 2 * T / (8 * a ^ 2)) * ((n : ℝ) + 1) ^ 2 =
      -(frequency a n) ^ 2 * T / 2 := by dsimp only [frequency]; field_simp [ne_of_gt ha] <;> ring
  have hp : Real.pi * ((n : ℝ) + 1) * (z - y) / (2 * a) =
      -(frequency a n * (y + a) - frequency a n * (z + a)) := by
    dsimp only [frequency]
    field_simp [ne_of_gt ha] <;> ring
  have hq : Real.pi * ((n : ℝ) + 1) * (z + y + 2 * a) / (2 * a) =
      frequency a n * (y + a) + frequency a n * (z + a) := by
    dsimp only [frequency]
    field_simp [ne_of_gt ha] <;> ring
  dsimp only [sineTerm, integerCosineTerm]
  simp only [hn, he, hp, hq, Real.cos_neg, Real.cos_sub, Real.cos_add]
  field_simp [ne_of_gt ha] <;> ring

theorem sineSeries_eq_integer_cosine (a z T y : ℝ) (ha : 0 < a) (hT : 0 < T) :
    mixedSineSeries 0 0 a z T y = (1 / (4 * a)) *
      ((∑' n : ℤ, integerCosineTerm a T (z - y) n) -
        (∑' n : ℤ, integerCosineTerm a T (z + y + 2 * a) n)) := by
  have hU := integerCosineTerm_pos_summable a T (z - y) ha hT
  have hV := integerCosineTerm_pos_summable a T (z + y + 2 * a) ha hT
  have hsum := (hU.hasSum.sub hV.hasSum).mul_left (1 / (2 * a))
  have heq : (fun n : ℕ => mixedSineTerm 0 0 a z T y n) =
      (fun n : ℕ => (1 / (2 * a)) * (integerCosineTerm a T (z - y) ((n : ℤ) + 1) -
        integerCosineTerm a T (z + y + 2 * a) ((n : ℤ) + 1))) := by
    funext n
    simpa only [mixedSineTerm, iteratedDeriv_zero] using sineTerm_cosine_difference a z T y n ha
  change (∑' n : ℕ, mixedSineTerm 0 0 a z T y n) = _
  rw [heq, hsum.tsum_eq,
    (integerCosineTerm_hasSum a T (z - y) ha hT).tsum_eq,
    (integerCosineTerm_hasSum a T (z + y + 2 * a) ha hT).tsum_eq]
  field_simp [ne_of_gt ha] <;> ring

end Shao.C2.IntervalSineCosineSeries
