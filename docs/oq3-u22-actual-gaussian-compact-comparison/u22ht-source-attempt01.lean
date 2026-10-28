import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Shao.OQ3
open scoped Matrix
noncomputable section

theorem pair_linear_map_determinant_of_rows
    (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) (a b c d : ℝ)
    (hL : ∀ w : ℝ × ℝ, L w = (a * w.1 + b * w.2, c * w.1 + d * w.2)) :
    L.det = a * d - b * c := by
  have hmap : L = Matrix.toLin (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ) !![a, b; c, d] := by
    apply LinearMap.ext
    intro w
    rw [Matrix.toLin_finTwoProd_apply]
    exact hL w
  calc
    L.det = (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℝ).det := by
      rw [hmap, LinearMap.det_toLin]
    _ = a * d - b * c := by simp [Matrix.det_fin_two]

theorem canonical_pair_whitening_determinant_quadratic
    (a b d : ℝ) (ha : 0 < a) (hdet : 0 < a * d - b ^ 2)
    (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
    let s : ℝ := Real.sqrt (a * d - b ^ 2)
    let t : ℝ := Real.sqrt (a + d + 2 * s)
    (∀ w : ℝ × ℝ, E w =
      (((d + s) / (s * t)) * w.1 + (-(b) / (s * t)) * w.2,
        (-(b) / (s * t)) * w.1 + ((a + s) / (s * t)) * w.2)) →
    (E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).toLinearMap.det = 1 / s ∧
      |(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).toLinearMap.det| = 1 / s ∧
      ∀ w : ℝ × ℝ, (E w).1 ^ 2 + (E w).2 ^ 2 =
        (d * w.1 ^ 2 - 2 * b * w.1 * w.2 + a * w.2 ^ 2) / (a * d - b ^ 2) := by
  intro s t hrows
  have hd : 0 < d := by
    by_contra h
    have had : a * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt h)
    nlinarith [sq_nonneg b]
  have hs : 0 < s := Real.sqrt_pos.mpr hdet
  have hs2 : s ^ 2 = a * d - b ^ 2 := Real.sq_sqrt hdet.le
  have htarg : 0 < a + d + 2 * s := by positivity
  have ht : 0 < t := Real.sqrt_pos.mpr htarg
  have ht2 : t ^ 2 = a + d + 2 * s := Real.sq_sqrt htarg.le
  have hdetNum : (d + s) * (a + s) - b ^ 2 = s * t ^ 2 := by
    nlinarith [hs2, congrArg (fun r : ℝ => s * r) ht2]
  have hEDet := pair_linear_map_determinant_of_rows
    (E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).toLinearMap
    ((d + s) / (s * t)) (-b / (s * t)) (-b / (s * t)) ((a + s) / (s * t)) hrows
  have hDet : (E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).toLinearMap.det = 1 / s := by
    calc
      _ = ((d + s) / (s * t)) * ((a + s) / (s * t)) -
        (-b / (s * t)) * (-b / (s * t)) := hEDet
      _ = ((d + s) * (a + s) - b ^ 2) / (s ^ 2 * t ^ 2) := by
        field_simp [hs.ne', ht.ne']
        <;> ring
      _ = (s * t ^ 2) / (s ^ 2 * t ^ 2) := by rw [hdetNum]
      _ = 1 / s := by
        field_simp [hs.ne', ht.ne']
        <;> ring
  refine ⟨hDet, ?_, ?_⟩
  · rw [hDet, abs_of_pos (div_pos (by norm_num) hs)]
  · intro w
    have hcoef1 : (d + s) ^ 2 + b ^ 2 = d * t ^ 2 := by
      nlinarith [hs2, congrArg (fun r : ℝ => d * r) ht2]
    have hcoef2 : b ^ 2 + (a + s) ^ 2 = a * t ^ 2 := by
      nlinarith [hs2, congrArg (fun r : ℝ => a * r) ht2]
    have hcoef3 : (d + s) + (a + s) = t ^ 2 := by linarith [ht2]
    have hnum : ((d + s) * w.1 - b * w.2) ^ 2 +
        (-b * w.1 + (a + s) * w.2) ^ 2 =
      t ^ 2 * (d * w.1 ^ 2 - 2 * b * w.1 * w.2 + a * w.2 ^ 2) := by
      calc
        _ = ((d + s) ^ 2 + b ^ 2) * w.1 ^ 2 -
          2 * b * ((d + s) + (a + s)) * w.1 * w.2 +
          (b ^ 2 + (a + s) ^ 2) * w.2 ^ 2 := by ring
        _ = _ := by rw [hcoef1, hcoef2, hcoef3]; ring
    rw [hrows]
    change (((d + s) / (s * t)) * w.1 + (-b / (s * t)) * w.2) ^ 2 +
      ((-b / (s * t)) * w.1 + ((a + s) / (s * t)) * w.2) ^ 2 = _
    calc
      _ = (((d + s) * w.1 - b * w.2) ^ 2 +
        (-b * w.1 + (a + s) * w.2) ^ 2) / (s ^ 2 * t ^ 2) := by
        field_simp [hs.ne', ht.ne']
        <;> ring
      _ = (t ^ 2 * (d * w.1 ^ 2 - 2 * b * w.1 * w.2 + a * w.2 ^ 2)) /
        (s ^ 2 * t ^ 2) := by rw [hnum]
      _ = (d * w.1 ^ 2 - 2 * b * w.1 * w.2 + a * w.2 ^ 2) / (a * d - b ^ 2) := by
        rw [← hs2]
        field_simp [hs.ne', ht.ne']
        <;> ring

end
end Shao.OQ3
