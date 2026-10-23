import Shao.OQ4.IntervalConcentration
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Algebra.Order.Floor.Semiring

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
noncomputable section

theorem standard_gaussian_plane_translated_ball_bound
    (z : ℝ × ℝ) (r : ℝ) (hr : 0 ≤ r) :
    ((ProbabilityTheory.gaussianReal 0 1).prod
      (ProbabilityTheory.gaussianReal 0 1)).real (Metric.closedBall z r) ≤ 4 * r ^ 2 := by
  let γ : Measure ℝ := gaussianReal 0 1
  have hCDF : ∀ x, |γ.real (Set.Iic x) - Shao.OQ4.standardNormalCDF x| ≤ 0 := by
    intro x
    change |(gaussianReal 0 1).real (Set.Iic x) - Shao.OQ4.standardNormalCDF x| ≤ 0
    rw [← Shao.OQ4.standardNormalCDF_eq_real]
    simp
  have hinterval (a b : ℝ) (hab : a ≤ b) : γ.real (Set.Icc a b) ≤ b - a := by
    have hi := Shao.OQ4.closed_interval_mass_bound_from_cdf γ 1 0
      Shao.OQ4.standardNormalCDF (by norm_num) (by norm_num)
      (by intro x y; simpa only [one_mul] using Shao.OQ4.standardNormalCDF_lipschitz x y)
      hCDF a b hab
    simpa only [one_mul, mul_zero, add_zero] using hi
  let I : Set ℝ := Set.Icc (z.1 - r) (z.1 + r)
  let J : Set ℝ := Set.Icc (z.2 - r) (z.2 + r)
  have hI : γ.real I ≤ 2 * r := by
    have hi := hinterval (z.1 - r) (z.1 + r) (by linarith)
    dsimp only [I]
    linarith
  have hJ : γ.real J ≤ 2 * r := by
    have hi := hinterval (z.2 - r) (z.2 + r) (by linarith)
    dsimp only [J]
    linarith
  have hsub : Metric.closedBall z r ⊆ I ×ˢ J := by
    intro x hx
    have hn : max |x.1 - z.1| |x.2 - z.2| ≤ r := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def,
        Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs] using hx
    have h1 := abs_le.mp ((le_max_left _ _).trans hn)
    have h2 := abs_le.mp ((le_max_right _ _).trans hn)
    exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩,
      ⟨by linarith [h2.1], by linarith [h2.2]⟩⟩
  calc
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).real (Metric.closedBall z r) ≤
        (γ.prod γ).real (I ×ˢ J) :=
      measureReal_mono hsub (measure_ne_top (γ.prod γ) _)
    _ = γ.real I * γ.real J := measureReal_prod_prod I J
    _ ≤ (2 * r) * (2 * r) :=
      mul_le_mul hI hJ (measureReal_nonneg (μ := γ)) (by linarith)
    _ = 4 * r ^ 2 := by ring

theorem standard_gaussian_plane_finite_ball_cover_tube_bound
    (F : Set (ℝ × ℝ)) (hF : IsCompact F) (S : Finset (ℝ × ℝ))
    (h : ℝ) (hh : 0 ≤ h)
    (hcover : ∀ x ∈ F, ∃ c ∈ S, dist x c ≤ h) :
    ((ProbabilityTheory.gaussianReal 0 1).prod
      (ProbabilityTheory.gaussianReal 0 1)).real (Metric.cthickening h F) ≤
        16 * (S.card : ℝ) * h ^ 2 := by
  classical
  let Φ : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)
  have hsub : Metric.cthickening h F ⊆ ⋃ c ∈ S, Metric.closedBall c (2 * h) := by
    intro z hz
    rw [hF.cthickening_eq_biUnion_closedBall hh] at hz
    rcases Set.mem_iUnion.mp hz with ⟨x, hz⟩
    rcases Set.mem_iUnion.mp hz with ⟨hx, hz⟩
    obtain ⟨c, hc, hxc⟩ := hcover x hx
    refine Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hc, ?_⟩⟩
    change dist z c ≤ 2 * h
    have hzx : dist z x ≤ h := hz
    calc
      dist z c ≤ dist z x + dist x c := dist_triangle _ _ _
      _ ≤ h + h := add_le_add hzx hxc
      _ = 2 * h := by ring
  calc
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).real (Metric.cthickening h F) ≤
        Φ.real (⋃ c ∈ S, Metric.closedBall c (2 * h)) :=
      measureReal_mono hsub (measure_ne_top Φ _)
    _ ≤ ∑ c ∈ S, Φ.real (Metric.closedBall c (2 * h)) :=
      measureReal_biUnion_finset_le S _
    _ ≤ ∑ _c ∈ S, (16 * h ^ 2) := by
      apply Finset.sum_le_sum
      intro c hc
      have hb := standard_gaussian_plane_translated_ball_bound c (2 * h) (by linarith)
      change Φ.real (Metric.closedBall c (2 * h)) ≤ 16 * h ^ 2
      dsimp only [Φ]
      nlinarith [hb]
    _ = 16 * (S.card : ℝ) * h ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

theorem standard_gaussian_plane_lipschitz_arc_tube_bound
    (f : ℝ → ℝ × ℝ) (K : NNReal)
    (hf : LipschitzOnWith K f (Set.Icc (0 : ℝ) 1))
    (h : ℝ) (hh : 0 < h) :
    ((ProbabilityTheory.gaussianReal 0 1).prod
      (ProbabilityTheory.gaussianReal 0 1)).real
        (Metric.cthickening h (f '' Set.Icc (0 : ℝ) 1)) ≤
          64 * ((K : ℝ) * h + h ^ 2) := by
  classical
  let N : ℕ := Nat.ceil ((K : ℝ) / h) + 1
  have hN : 0 < N := Nat.succ_pos _
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hceil : (K : ℝ) / h ≤ (N : ℝ) := by
    have hc := Nat.le_ceil ((K : ℝ) / h)
    dsimp only [N]
    push_cast
    linarith
  have hKN : (K : ℝ) ≤ (N : ℝ) * h := (div_le_iff₀ hh).mp hceil
  have hNupper : (N : ℝ) + 1 ≤ (K : ℝ) / h + 3 := by
    have hc := Nat.ceil_lt_add_one (div_nonneg K.property hh.le)
    calc
      (N : ℝ) + 1 = (Nat.ceil ((K : ℝ) / h) : ℝ) + 2 := by
        dsimp only [N]
        push_cast
        ring
      _ ≤ ((K : ℝ) / h + 1) + 2 := add_le_add hc.le le_rfl
      _ = (K : ℝ) / h + 3 := by ring
  let S : Finset (ℝ × ℝ) :=
    (Finset.range (N + 1)).image (fun i : ℕ => f ((i : ℝ) / (N : ℝ)))
  have hcover : ∀ x ∈ f '' Set.Icc (0 : ℝ) 1, ∃ c ∈ S, dist x c ≤ h := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hx
    let i : ℕ := Nat.floor (t * (N : ℝ))
    have hi : i ≤ N := Nat.floor_le_of_le (by nlinarith [ht.2])
    have hifloor : (i : ℝ) ≤ t * (N : ℝ) :=
      Nat.floor_le (mul_nonneg ht.1 hNr.le)
    have htfloor : t * (N : ℝ) < (i : ℝ) + 1 := Nat.lt_floor_add_one _
    have hi0 : 0 ≤ (i : ℝ) / (N : ℝ) := div_nonneg (Nat.cast_nonneg _) hNr.le
    have hi1 : (i : ℝ) / (N : ℝ) ≤ 1 := by
      apply (div_le_iff₀ hNr).mpr
      simpa only [one_mul] using (show (i : ℝ) ≤ (N : ℝ) by exact_mod_cast hi)
    have hit : (i : ℝ) / (N : ℝ) ≤ t := (div_le_iff₀ hNr).mpr hifloor
    have hdist : dist t ((i : ℝ) / (N : ℝ)) ≤ 1 / (N : ℝ) := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hit)]
      calc
        t - (i : ℝ) / (N : ℝ) = (t * (N : ℝ) - i) / (N : ℝ) := by
          field_simp [hNr.ne']
          <;> ring
        _ ≤ 1 / (N : ℝ) :=
          div_le_div_of_nonneg_right (by linarith) hNr.le
    refine ⟨f ((i : ℝ) / (N : ℝ)), Finset.mem_image.mpr
      ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩, ?_⟩
    calc
      dist (f t) (f ((i : ℝ) / (N : ℝ))) ≤
          (K : ℝ) * dist t ((i : ℝ) / (N : ℝ)) := hf.dist_le_mul t ht _ ⟨hi0, hi1⟩
      _ ≤ (K : ℝ) * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_left hdist K.property
      _ ≤ h := by
        rw [mul_one_div]
        exact (div_le_iff₀ hNr).mpr (by nlinarith [hKN])
  have hcard0 : S.card ≤ N + 1 := by
    dsimp only [S]
    exact Finset.card_image_le.trans_eq (Finset.card_range _)
  have hcard : (S.card : ℝ) ≤ (K : ℝ) / h + 3 :=
    (show (S.card : ℝ) ≤ (N : ℝ) + 1 by exact_mod_cast hcard0).trans hNupper
  have hcompact : IsCompact (f '' Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn hf.continuousOn
  calc
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
        (Metric.cthickening h (f '' Set.Icc (0 : ℝ) 1)) ≤ 16 * (S.card : ℝ) * h ^ 2 :=
      standard_gaussian_plane_finite_ball_cover_tube_bound _ hcompact S h hh.le hcover
    _ ≤ 16 * ((K : ℝ) / h + 3) * h ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by norm_num)) (sq_nonneg h)
    _ = 16 * ((K : ℝ) * h) + 48 * h ^ 2 := by
      field_simp [hh.ne']
      <;> ring
    _ ≤ 64 * ((K : ℝ) * h + h ^ 2) := by
      calc
        16 * ((K : ℝ) * h) + 48 * h ^ 2 ≤
            64 * ((K : ℝ) * h) + 64 * h ^ 2 :=
          add_le_add
            (mul_le_mul_of_nonneg_right (by norm_num : (16 : ℝ) ≤ 64)
              (mul_nonneg K.property hh.le))
            (mul_le_mul_of_nonneg_right (by norm_num : (48 : ℝ) ≤ 64) (sq_nonneg h))
        _ = 64 * ((K : ℝ) * h + h ^ 2) := by ring

end
end Shao.OQ3
