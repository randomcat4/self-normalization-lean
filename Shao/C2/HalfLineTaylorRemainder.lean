import Shao.C2.HalfLineTaylorPath

noncomputable section
namespace Shao.C2.HalfLineTaylorRemainder
open Shao.C2.HalfLineTaylorSegment Shao.C2.HalfLineTaylorPath
open Shao.C2.HalfLineMixedProfiles Shao.C2.HalfLineTimeProfiles

theorem third_path_derivative_decomposition (u v T b θ : ℝ)
    (hE : 0 < segmentEnergy T b θ) :
    deriv (deriv (deriv (completionAlongSegment u v T b))) θ =
      -b ^ 3 * ((2 * v / segmentEnergy T b θ) ^ 3 *
        Real.exp (-2 * segmentDistance u b θ * v / segmentEnergy T b θ)) -
      3 * b ^ 4 * deriv (curvatureTime (segmentDistance u b θ) v) (segmentEnergy T b θ) -
      3 * b ^ 5 * deriv (deriv (slopeTime (segmentDistance u b θ) v)) (segmentEnergy T b θ) -
      b ^ 6 * deriv (deriv (deriv (timeCompletion (2 * segmentDistance u b θ * v))))
        (segmentEnergy T b θ) := by
  rw [(completionAlongSegment_third_hasDerivAt u v T b θ hE).deriv,
    (curvatureTime_hasDerivAt (segmentDistance u b θ) v (segmentEnergy T b θ) hE).deriv,
    (slopeTime_second_hasDerivAt (segmentDistance u b θ) v (segmentEnergy T b θ) hE).deriv,
    (timeCompletion_third_hasDerivAt (2 * segmentDistance u b θ * v)
      (segmentEnergy T b θ) hE).deriv]
  simp only [neg_mul]
  dsimp only [exponentSlope]
  field_simp [ne_of_gt hE] <;> dsimp only [segmentEnergy, segmentDistance] <;> ring

theorem compensated_lagrange_remainder (u v T b : ℝ) (hT : 0 < T)
    (hsmall : b ^ 2 ≤ T / 2) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) 1,
      completionAlongSegment u v T b 1 - completionAlongSegment u v T b 0 -
          (b - b ^ 2 * (u - v) / T) * (-slopeTime u v T) =
        (1 / 6 : ℝ) * deriv (deriv (deriv (completionAlongSegment u v T b))) θ +
          b ^ 3 * deriv (slopeTime u v) T +
          (1 / 2 : ℝ) * b ^ 4 * deriv (deriv (timeCompletion (2 * u * v))) T := by
  let g := completionAlongSegment u v T b
  have hzero : (0 : ℝ) ≠ 1 := by norm_num
  have hle : (0 : ℝ) ≤ 1 := by norm_num
  have he (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) : 0 < segmentEnergy T b t := by
    have hh : t ∈ Set.Icc (0 : ℝ) 1 := by simpa only [Set.uIcc_of_le hle] using ht
    exact (segment_energy_bounds T b t hT hsmall hh.1 hh.2).1
  have hf : ContDiffOn ℝ (3 : ℕ) g (Set.uIcc (0 : ℝ) 1) := by
    intro t ht
    exact (completionAlongSegment_contDiffAt u v T b t (he t ht) 3).contDiffWithinAt
  have hu : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) 1) := uniqueDiffOn_uIcc hzero
  have hz : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by simp
  have hiter (n : ℕ) : iteratedDerivWithin n g (Set.uIcc (0 : ℝ) 1) 0 = iteratedDeriv n g 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hu
      (completionAlongSegment_contDiffAt u v T b 0 (he 0 hz) n) hz
  have hpoly : taylorWithinEval g 2 (Set.uIcc (0 : ℝ) 1) 0 1 =
      g 0 + deriv g 0 + (1 / 2 : ℝ) * deriv (deriv g) 0 := by
    simp only [taylor_within_apply, hiter]
    norm_num [Finset.sum_range_succ, iteratedDeriv_succ, iteratedDeriv_zero, smul_eq_mul]
    <;> ring
  obtain ⟨θ, hθ, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hzero hf
  have hθ' : θ ∈ Set.Ioo (0 : ℝ) 1 := by simpa only [Set.uIoo_of_lt (by norm_num : (0 : ℝ) < 1)] using hθ
  refine ⟨θ, hθ', ?_⟩
  rw [hpoly] at hrem
  norm_num [iteratedDeriv_succ, iteratedDeriv_zero] at hrem
  have hc := compensated_second_taylor_identity u v T b hT
  change g 1 - g 0 - (b - b ^ 2 * (u - v) / T) * (-slopeTime u v T) = _
  change deriv g 0 + (1 / 2 : ℝ) * deriv (deriv g) 0 - _ = _ at hc
  linarith only [hrem, hc]

end Shao.C2.HalfLineTaylorRemainder
