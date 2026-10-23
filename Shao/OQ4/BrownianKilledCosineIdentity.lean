import Shao.OQ4.PolygonalKilledFunctionalLimit
import Shao.OQ4.RademacherIteration
import Shao.OQ4.RademacherScalarBounds
import Shao.OQ4.KilledPathLaw
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Actual source B4, proved by the finite Rademacher eigenidentity and the actual
general-row killed-functional limit. The source's argument uses Itô's formula;
this module implements an alternative proof of the same expectation identity.
Exact declaration/value freeze: frozen-brownian-killed-cosine-identity-formal-v1.
-/

noncomputable section
namespace Shao.OQ4.BrownianKilledCosineIdentity
open MeasureTheory ProbabilityTheory Filter Set
open RademacherScalarBounds
open scoped NNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω]

private def stripRadius (m : ℕ) : ℝ≥0 :=
  (m : ℝ≥0) / ((m : ℝ≥0) + 1)

private def latticeStart (m : ℕ) (u : ℝ) : ℤ :=
  max (-(m : ℤ)) (min (m : ℤ) ⌊H m * u⌋)

private def rowLength (T : ℝ≥0) (m : ℕ) : ℕ :=
  ⌈(T : ℝ) * H m ^ 2⌉₊

private def prefixFamily (n l : ℕ) (hl : l ≤ n) :
    Fin l → Shao.Path n → ℝ :=
  fun i a => a (Fin.castLE hl i)

private theorem latticeStart_bounds (m : ℕ) (u : ℝ) :
    -(m : ℤ) ≤ latticeStart m u ∧ latticeStart m u ≤ (m : ℤ) := by
  unfold latticeStart
  constructor
  · exact le_max_left _ _
  · exact max_le_iff.mpr ⟨by omega, min_le_left _ _⟩

private theorem scaledStart_error (m : ℕ) (hm : 1 ≤ m)
    (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    |(latticeStart m u : ℝ) / H m - u| ≤ 1 / H m := by
  have hH : 0 < H m := H_pos hm
  let p : ℤ := ⌊H m * u⌋
  have hp0 : (p : ℝ) ≤ H m * u := Int.floor_le _
  have hp1 : H m * u < (p : ℝ) + 1 := Int.lt_floor_add_one _
  have hxlo : -H m ≤ H m * u := by
    simpa using mul_le_mul_of_nonneg_left hu.1 hH.le
  have hxhi : H m * u ≤ H m := by
    simpa using mul_le_mul_of_nonneg_left hu.2 hH.le
  have hraw : |(latticeStart m u : ℝ) - H m * u| ≤ 1 := by
    by_cases hlo : p < -(m : ℤ)
    · have hpm : p ≤ (m : ℤ) := by omega
      have hr : latticeStart m u = -(m : ℤ) := by
        change max (-(m : ℤ)) (min (m : ℤ) p) = -(m : ℤ)
        rw [min_eq_right hpm, max_eq_left hlo.le]
      have hpupper : (p : ℝ) + 1 ≤ -(m : ℝ) := by
        exact_mod_cast (show p + 1 ≤ -(m : ℤ) by omega)
      rw [hr]
      push_cast
      apply abs_le.mpr
      dsimp [H] at hxlo hxhi hp0 hp1 ⊢
      constructor <;> linarith
    · have hplo : -(m : ℤ) ≤ p := le_of_not_gt hlo
      by_cases hhi : (m : ℤ) < p
      · have hr : latticeStart m u = (m : ℤ) := by
          change max (-(m : ℤ)) (min (m : ℤ) p) = (m : ℤ)
          rw [min_eq_left hhi.le, max_eq_right (by omega)]
        have hplower : (m : ℝ) + 1 ≤ (p : ℝ) := by
          exact_mod_cast (show (m : ℤ) + 1 ≤ p by omega)
        rw [hr]
        push_cast
        apply abs_le.mpr
        dsimp [H] at hxlo hxhi hp0 hp1 ⊢
        constructor <;> linarith
      · have hphi : p ≤ (m : ℤ) := le_of_not_gt hhi
        have hr : latticeStart m u = p := by
          change max (-(m : ℤ)) (min (m : ℤ) p) = p
          rw [min_eq_right hphi, max_eq_right hplo]
        rw [hr]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    |(latticeStart m u : ℝ) / H m - u| =
        |((latticeStart m u : ℝ) - H m * u) / H m| := by
      congr 1
      field_simp [hH.ne'] <;> ring
    _ = |(latticeStart m u : ℝ) - H m * u| / H m := by
      rw [abs_div, abs_of_pos hH]
    _ ≤ 1 / H m := div_le_div_of_nonneg_right hraw hH.le

private theorem scale_tendsto :
    Tendsto (fun j : ℕ => H (j + 1)) atTop atTop := by
  apply tendsto_atTop_mono (fun j : ℕ => ?_)
    (tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop)
  simp only [H, Nat.cast_add, Nat.cast_one]
  linarith

private theorem radius_tendsto :
    Tendsto (fun j : ℕ => stripRadius (j + 1)) atTop (𝓝 (1 : ℝ≥0)) := by
  apply NNReal.tendsto_coe.1
  have hi : Tendsto (fun j : ℕ => 1 / H (j + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp scale_tendsto
  have heq (j : ℕ) : (stripRadius (j + 1) : ℝ) = 1 - 1 / H (j + 1) := by
    change ((j + 1 : ℕ) : ℝ) / (((j + 1 : ℕ) : ℝ) + 1) =
      1 - 1 / H (j + 1)
    dsimp [H]
    field_simp [show (((j + 1 : ℕ) : ℝ) + 1) ≠ 0 by positivity] <;> ring
  simp_rw [heq]
  simpa using
    (tendsto_const_nhds.sub hi :
      Tendsto (fun j : ℕ => (1 : ℝ) - 1 / H (j + 1)) atTop (𝓝 (1 - 0)))

private theorem start_tendsto (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun j : ℕ => (latticeStart (j + 1) u : ℝ) / H (j + 1))
      atTop (𝓝 u) := by
  have hi : Tendsto (fun j : ℕ => 1 / H (j + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp scale_tendsto
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _))
    (Eventually.of_forall (fun j => scaledStart_error (j + 1) (by omega) u hu)) hi

private theorem rowLength_horizon (T : ℝ≥0) (m : ℕ) :
    (T : ℝ) * H m ^ 2 ≤ (rowLength T m : ℝ) := by
  exact Nat.le_ceil _

private theorem rademacher_moments :
    Integrable (fun x : ℝ => |x| ^ 3) RademacherCosine.law ∧
      (∫ x : ℝ, x ∂RademacherCosine.law) = 0 ∧
      (∫ x : ℝ, x ^ 2 ∂RademacherCosine.law) = 1 ∧
      (∫ x : ℝ, |x| ^ 3 ∂RademacherCosine.law) = 1 := by
  have hhalf : RademacherCosine.halfENNReal ≠ ⊤ := by
    norm_num [RademacherCosine.halfENNReal]
  have hreal : RademacherCosine.halfENNReal.toReal = (1 / 2 : ℝ) := by
    norm_num [RademacherCosine.halfENNReal, ENNReal.toReal_div]
  have hp (f : ℝ → ℝ) :
      Integrable f (RademacherCosine.halfENNReal • Measure.dirac (1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure hhalf
  have hn (f : ℝ → ℝ) :
      Integrable f (RademacherCosine.halfENNReal • Measure.dirac (-1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure hhalf
  have hi (f : ℝ → ℝ) : Integrable f RademacherCosine.law := by
    rw [RademacherCosine.law]
    exact (hp f).add_measure (hn f)
  have hformula (f : ℝ → ℝ) :
      (∫ x : ℝ, f x ∂RademacherCosine.law) =
        (1 / 2 : ℝ) * f 1 + (1 / 2 : ℝ) * f (-1) := by
    rw [RademacherCosine.law, integral_add_measure (hp f) (hn f),
      integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac, hreal]
    rfl
  refine ⟨hi _, ?_, ?_, ?_⟩
  · norm_num [hformula]
  · norm_num [hformula]
  · norm_num [hformula]

private theorem prefixFamily_iid (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n l : ℕ) (hl : l ≤ n) :
    (∀ i, Measurable (prefixFamily n l hl i)) ∧
      iIndepFun (prefixFamily n l hl) (Measure.pi (fun _ : Fin n => ν)) ∧
      ∀ i, IdentDistrib (prefixFamily n l hl i) (id : ℝ → ℝ)
        (Measure.pi (fun _ : Fin n => ν)) ν := by
  have hi : iIndepFun (fun i : Fin n => fun a : Shao.Path n => a i)
      (Measure.pi (fun _ : Fin n => ν)) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  refine ⟨fun i => measurable_pi_apply (Fin.castLE hl i), ?_, ?_⟩
  · change iIndepFun (fun i : Fin l => fun a : Shao.Path n => a (Fin.castLE hl i)) _
    exact hi.precomp (Fin.castLE_injective hl)
  intro i
  refine ⟨(measurable_pi_apply (Fin.castLE hl i)).aemeasurable, aemeasurable_id, ?_⟩
  change Measure.map (Function.eval (Fin.castLE hl i)) (Measure.pi (fun _ : Fin n => ν)) =
    Measure.map (id : ℝ → ℝ) ν
  rw [Measure.map_id]
  exact (measurePreserving_eval (fun _ : Fin n => ν) (Fin.castLE hl i)).map_eq

private theorem prefixSum_prefixFamily (n l : ℕ) (hl : l ≤ n)
    (a : Shao.Path n) (k : ℕ) (hk : k ≤ l) :
    Shao.prefixSum (Shao.Probability.samplePath (prefixFamily n l hl) a) k =
      Shao.prefixSum a k := by
  classical
  unfold Shao.prefixSum
  refine Finset.sum_bij (fun i _ => Fin.castLE hl i) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ hij
    exact Fin.castLE_injective hl hij
  · intro j hj
    have hjk : j.val < k := (Finset.mem_filter.mp hj).2
    refine ⟨⟨j.val, lt_of_lt_of_le hjk hk⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjk⟩, ?_⟩
    exact Fin.ext rfl
  · intro i _
    rfl

private theorem discrete_event_iff_shifted_scaled (n l : ℕ)
    (hl : l ≤ n) (h : ℝ) (hh : 0 < h) (b : ℝ≥0)
    (z : ℝ) (hz : |z| ≤ (b : ℝ) * h) (a : Shao.Path n) :
    a ∈ PolygonalKilledFunctionalLimit.discreteClosedSurvival
      n l h (z / h) b ↔
      Shao.Probability.samplePath (prefixFamily n l hl) a ∈
        shiftedClosedSurvival (n := l) ((b : ℝ) * h) z := by
  have hscale (s : ℝ) : |z / h + s / h| ≤ (b : ℝ) ↔ |z + s| ≤ (b : ℝ) * h := by
    rw [← add_div, abs_div, abs_of_pos hh, div_le_iff₀ hh]
  change (∀ k : ℕ, k ≤ l → |z / h + Shao.prefixSum a k / h| ≤ (b : ℝ)) ↔
    ∀ k : ℕ, 1 ≤ k → k ≤ l →
      |z + Shao.prefixSum (Shao.Probability.samplePath (prefixFamily n l hl) a) k| ≤
        (b : ℝ) * h
  constructor
  · intro ha k _hk hkl
    rw [prefixSum_prefixFamily n l hl a k hkl]
    exact (hscale _).mp (ha k hkl)
  · intro ha k hkl
    apply (hscale _).mpr
    by_cases hk : k = 0
    · simpa [hk] using hz
    · rw [← prefixSum_prefixFamily n l hl a k hkl]
      exact ha k (by omega) hkl

theorem discrete_killed_test_integral
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n l : ℕ) (hl : l ≤ n)
    (h : ℝ) (hh : 0 < h) (b : ℝ≥0) (z : ℝ) (hz : |z| ≤ (b : ℝ) * h)
    (F : ℝ → ℝ) (hF : Measurable F) (hbound : ∃ M : ℝ, ∀ w, |F w| ≤ M) :
    Integrable F (killedIterKernel ν ((b : ℝ) * h) l z) ∧
      Integrable
        ((PolygonalKilledFunctionalLimit.discreteClosedSurvival n l h (z / h) b).indicator
          (fun a : Shao.Path n => F (z + Shao.prefixSum a l)))
        (Measure.pi (fun _ : Fin n => ν)) ∧
      (∫ a : Shao.Path n,
        (PolygonalKilledFunctionalLimit.discreteClosedSurvival n l h (z / h) b).indicator
          (fun a => F (z + Shao.prefixSum a l)) a
          ∂Measure.pi (fun _ : Fin n => ν)) =
        killedAction ν ((b : ℝ) * h) l F z := by
  classical
  rcases prefixFamily_iid ν n l hl with ⟨hX, hXi, hXlaw⟩
  have ht := killedIterKernel_integral_iid_path ν
    (Measure.pi (fun _ : Fin n => ν)) l ((b : ℝ) * h) z
    (prefixFamily n l hl) hX hXi hXlaw F hF hbound
  have hcut :
      ((PolygonalKilledFunctionalLimit.discreteClosedSurvival n l h (z / h) b).indicator
        (fun a : Shao.Path n => F (z + Shao.prefixSum a l))) =
      (fun a : Shao.Path n =>
        if Shao.Probability.samplePath (prefixFamily n l hl) a ∈
            shiftedClosedSurvival (n := l) ((b : ℝ) * h) z then
          F (shiftedEndpoint z (Shao.Probability.samplePath (prefixFamily n l hl) a))
        else 0) := by
    funext a
    have hE := discrete_event_iff_shifted_scaled n l hl h hh b z hz a
    by_cases he : a ∈ PolygonalKilledFunctionalLimit.discreteClosedSurvival n l h (z / h) b
    · have hs := hE.mp he
      simp only [Set.indicator_of_mem he, if_pos hs, shiftedEndpoint]
      rw [prefixSum_prefixFamily n l hl a l le_rfl]
    · have hs : Shao.Probability.samplePath (prefixFamily n l hl) a ∉
          shiftedClosedSurvival (n := l) ((b : ℝ) * h) z :=
        fun hs => he (hE.mpr hs)
      simp only [Set.indicator_of_notMem he, if_neg hs]
  refine ⟨ht.1, ?_, ?_⟩
  · rw [hcut]
    exact ht.2.1
  · rw [hcut]
    exact ht.2.2.symm

private theorem discreteKilledCosine_eq_cut (n l m : ℕ)
    (r : ℤ) (a : Shao.Path n) :
    PolygonalKilledFunctionalLimit.discreteKilledCosine
      n l (H m) ((r : ℝ) / H m) (stripRadius m) a =
      (PolygonalKilledFunctionalLimit.discreteClosedSurvival
        n l (H m) ((r : ℝ) / H m) (stripRadius m)).indicator
        (fun a => Real.cos (RademacherCosine.angle m *
          ((r : ℝ) + Shao.prefixSum a l))) a := by
  unfold PolygonalKilledFunctionalLimit.discreteKilledCosine
  by_cases he : a ∈ PolygonalKilledFunctionalLimit.discreteClosedSurvival
      n l (H m) ((r : ℝ) / H m) (stripRadius m)
  · simp only [Set.indicator_of_mem he]
    congr 1
    dsimp [RademacherCosine.angle, H]
    field_simp [show (m : ℝ) + 1 ≠ 0 by positivity] <;> ring
  · simp only [Set.indicator_of_notMem he]

private theorem finite_row_identity (n l m : ℕ)
    (hm : 1 ≤ m) (hl : l ≤ n) (r : ℤ)
    (hrlo : -(m : ℤ) ≤ r) (hrhi : r ≤ (m : ℤ)) :
    (∫ a : Shao.Path n, PolygonalKilledFunctionalLimit.discreteKilledCosine
      n l (H m) ((r : ℝ) / H m) (stripRadius m) a
        ∂Measure.pi (fun _ : Fin n => RademacherCosine.law)) =
      RademacherCosine.rho m ^ l *
        Real.cos (RademacherCosine.angle m * (r : ℝ)) := by
  have hH : 0 < H m := H_pos hm
  have hrad : (stripRadius m : ℝ) * H m = (m : ℝ) := by
    change ((m : ℝ) / ((m : ℝ) + 1)) * ((m : ℝ) + 1) = (m : ℝ)
    field_simp [show (m : ℝ) + 1 ≠ 0 by positivity]
  have hz : |(r : ℝ)| ≤ (stripRadius m : ℝ) * H m := by
    rw [hrad]
    apply abs_le.mpr
    constructor
    · exact_mod_cast hrlo
    · exact_mod_cast hrhi
  have hf : Measurable (fun w : ℝ => Real.cos (RademacherCosine.angle m * w)) := by
    fun_prop
  have ht := discrete_killed_test_integral RademacherCosine.law n l hl
    (H m) hH (stripRadius m) (r : ℝ) hz
    (fun w : ℝ => Real.cos (RademacherCosine.angle m * w)) hf
    ⟨1, fun w => Real.abs_cos_le_one _⟩
  calc
    _ = ∫ a : Shao.Path n,
        (PolygonalKilledFunctionalLimit.discreteClosedSurvival
          n l (H m) ((r : ℝ) / H m) (stripRadius m)).indicator
          (fun a => Real.cos (RademacherCosine.angle m *
            ((r : ℝ) + Shao.prefixSum a l))) a
          ∂Measure.pi (fun _ : Fin n => RademacherCosine.law) :=
      integral_congr_ae (Eventually.of_forall (fun a => discreteKilledCosine_eq_cut n l m r a))
    _ = killedAction RademacherCosine.law ((stripRadius m : ℝ) * H m) l
        (fun w : ℝ => Real.cos (RademacherCosine.angle m * w)) (r : ℝ) := ht.2.2
    _ = _ := by
      rw [hrad]
      exact RademacherIteration.killedAction_principal_power m hm (m : ℝ)
        le_rfl (by linarith) r hrlo hrhi l

private theorem principal_power_error (T : ℝ≥0) (m : ℕ) (hm : 1 ≤ m) :
    |(PolygonalKilledFunctionalLimit.floorHorizon T (H m) : ℝ) *
        Real.log (RademacherCosine.rho m) + lambda * (T : ℝ)| ≤
      (lambda + (T : ℝ) * C_rho) / H m ^ 2 := by
  let L : ℕ := PolygonalKilledFunctionalLimit.floorHorizon T (H m)
  have hH : 0 < H m := H_pos hm
  have hH2 : 0 < H m ^ 2 := pow_pos hH 2
  have hL0 : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
  have hLle : (L : ℝ) ≤ (T : ℝ) * H m ^ 2 :=
    Nat.floor_le (mul_nonneg T.2 (sq_nonneg _))
  have hLlt : (T : ℝ) * H m ^ 2 < (L : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hratio : (L : ℝ) / H m ^ 2 ≤ (T : ℝ) :=
    (div_le_iff₀ hH2).2 hLle
  have hgap0 : 0 ≤ (T : ℝ) - (L : ℝ) / H m ^ 2 := sub_nonneg.mpr hratio
  have hgap1 : (T : ℝ) - (L : ℝ) / H m ^ 2 ≤ 1 / H m ^ 2 := by
    apply (le_div_iff₀ hH2).2
    calc
      ((T : ℝ) - (L : ℝ) / H m ^ 2) * H m ^ 2 =
          (T : ℝ) * H m ^ 2 - (L : ℝ) := by
        field_simp [hH.ne'] <;> ring
      _ ≤ 1 := by linarith
  have hlam : 0 ≤ lambda := by
    dsimp [lambda]
    positivity
  have hC : 0 ≤ C_rho := C_rho_pos.le
  have he : |Real.log (RademacherCosine.rho m) + lambda / H m ^ 2| ≤
      C_rho / H m ^ 4 := by
    simpa only [rho_eq_cosine_rho] using SCA2 hm
  have hscale : (L : ℝ) * (C_rho / H m ^ 4) ≤
      (T : ℝ) * C_rho / H m ^ 2 := by
    calc
      (L : ℝ) * (C_rho / H m ^ 4) =
          ((L : ℝ) / H m ^ 2) * (C_rho / H m ^ 2) := by
        field_simp [hH.ne'] <;> ring
      _ ≤ (T : ℝ) * (C_rho / H m ^ 2) :=
        mul_le_mul_of_nonneg_right hratio (div_nonneg hC hH2.le)
      _ = (T : ℝ) * C_rho / H m ^ 2 := by ring
  change |(L : ℝ) * Real.log (RademacherCosine.rho m) + lambda * (T : ℝ)| ≤ _
  calc
    _ = |(L : ℝ) * (Real.log (RademacherCosine.rho m) + lambda / H m ^ 2) +
        lambda * ((T : ℝ) - (L : ℝ) / H m ^ 2)| := by congr 1; ring
    _ ≤ |(L : ℝ) * (Real.log (RademacherCosine.rho m) + lambda / H m ^ 2)| +
        |lambda * ((T : ℝ) - (L : ℝ) / H m ^ 2)| := abs_add_le _ _
    _ = (L : ℝ) * |Real.log (RademacherCosine.rho m) + lambda / H m ^ 2| +
        lambda * ((T : ℝ) - (L : ℝ) / H m ^ 2) := by
      rw [abs_mul, abs_of_nonneg hL0, abs_mul, abs_of_nonneg hlam, abs_of_nonneg hgap0]
    _ ≤ (L : ℝ) * (C_rho / H m ^ 4) + lambda * (1 / H m ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left he hL0)
        (mul_le_mul_of_nonneg_left hgap1 hlam)
    _ ≤ (T : ℝ) * C_rho / H m ^ 2 + lambda * (1 / H m ^ 2) :=
      add_le_add hscale le_rfl
    _ = (lambda + (T : ℝ) * C_rho) / H m ^ 2 := by ring

private theorem principal_power_tendsto (T : ℝ≥0) :
    Tendsto (fun j : ℕ => RademacherCosine.rho (j + 1) ^
      PolygonalKilledFunctionalLimit.floorHorizon T (H (j + 1))) atTop
      (𝓝 (Real.exp (-lambda * (T : ℝ)))) := by
  have hi : Tendsto (fun j : ℕ => 1 / H (j + 1) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa [one_div, inv_pow] using (tendsto_inv_atTop_zero.comp scale_tendsto).pow 2
  have hb : Tendsto (fun j : ℕ => (lambda + (T : ℝ) * C_rho) / H (j + 1) ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa [div_eq_mul_inv] using hi.const_mul (lambda + (T : ℝ) * C_rho)
  have hlog : Tendsto (fun j : ℕ =>
      (PolygonalKilledFunctionalLimit.floorHorizon T (H (j + 1)) : ℝ) *
        Real.log (RademacherCosine.rho (j + 1))) atTop (𝓝 (-lambda * (T : ℝ))) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq]
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_ hb
    exact Eventually.of_forall fun j => by
      simpa only [sub_neg_eq_add, neg_mul] using
        principal_power_error T (j + 1) (by omega)
  have heq :
      (fun j : ℕ => RademacherCosine.rho (j + 1) ^
        PolygonalKilledFunctionalLimit.floorHorizon T (H (j + 1))) =
      (fun j : ℕ => Real.exp
        ((PolygonalKilledFunctionalLimit.floorHorizon T (H (j + 1)) : ℝ) *
          Real.log (RademacherCosine.rho (j + 1)))) := by
    funext j
    rw [Real.exp_nat_mul, Real.exp_log (RademacherCosine.rho_pos (j + 1) (by omega))]
  rw [heq]
  exact (Real.continuous_exp.tendsto _).comp hlog

private theorem brownianKilledCosine_zero_ae
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    PolygonalKilledFunctionalLimit.brownianKilledCosine B 0 u =ᵐ[P]
      (fun _ : Ω => Real.cos (Real.pi * u / 2)) := by
  filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hzero
  have he : ω ∈ BrownianSurvivalBoundary.closedSurvival B 0 u := by
    intro t ht
    have ht0 : t = 0 := le_antisymm ht zero_le
    simpa only [ht0, hzero, add_zero] using (abs_le.mpr hu : |u| ≤ 1)
  rw [PolygonalKilledFunctionalLimit.brownianKilledCosine, Set.indicator_of_mem he,
    hzero, add_zero]
  congr 1
  ring

private theorem brownianKilledCosine_integral_pos
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0) (hT : 0 < T)
    (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    (∫ ω, PolygonalKilledFunctionalLimit.brownianKilledCosine B T u ω ∂P) =
      Real.exp (-lambda * (T : ℝ)) * Real.cos (Real.pi * u / 2) := by
  let nSeq : ℕ → ℕ := fun j => rowLength T (j + 1)
  let hSeq : ℕ → ℝ := fun j => H (j + 1)
  let bSeq : ℕ → ℝ≥0 := fun j => stripRadius (j + 1)
  let uSeq : ℕ → ℝ := fun j => (latticeStart (j + 1) u : ℝ) / H (j + 1)
  have hpos (j : ℕ) : 0 < hSeq j := H_pos (by omega)
  have horizon (j : ℕ) : (T : ℝ) * hSeq j ^ 2 ≤ (nSeq j : ℝ) :=
    rowLength_horizon T (j + 1)
  rcases rademacher_moments with ⟨h3, hmean, hsecond, hthird⟩
  have hconv := PolygonalKilledFunctionalLimit.discrete_killed_cosine_tendsto_brownian
    B P hB T hT nSeq hSeq (fun _ => RademacherCosine.law)
    (fun _ => inferInstance) hpos horizon (fun _ => h3) (fun _ => hmean)
    (fun _ => hsecond) 1 (fun _ => hthird.le) scale_tendsto
    bSeq radius_tendsto uSeq u (start_tendsto u hu) hu
  have hrow (j : ℕ) :
      (∫ a : Shao.Path (nSeq j), PolygonalKilledFunctionalLimit.discreteKilledCosine
        (nSeq j) (PolygonalKilledFunctionalLimit.floorHorizon T (hSeq j))
        (hSeq j) (uSeq j) (bSeq j) a
          ∂Measure.pi (fun _ : Fin (nSeq j) => RademacherCosine.law)) =
      RademacherCosine.rho (j + 1) ^
        PolygonalKilledFunctionalLimit.floorHorizon T (H (j + 1)) *
        Real.cos (RademacherCosine.angle (j + 1) * (latticeStart (j + 1) u : ℝ)) := by
    exact finite_row_identity (nSeq j)
      (PolygonalKilledFunctionalLimit.floorHorizon T (hSeq j)) (j + 1) (by omega)
      (PolygonalKilledFunctionalLimit.floorHorizon_le T (hSeq j) (nSeq j) (horizon j))
      (latticeStart (j + 1) u) (latticeStart_bounds (j + 1) u).1
      (latticeStart_bounds (j + 1) u).2
  have hconv' : Tendsto (fun j : ℕ =>
      RademacherCosine.rho (j + 1) ^
        PolygonalKilledFunctionalLimit.floorHorizon T (H (j + 1)) *
        Real.cos (RademacherCosine.angle (j + 1) * (latticeStart (j + 1) u : ℝ)))
      atTop (𝓝 (∫ ω, PolygonalKilledFunctionalLimit.brownianKilledCosine B T u ω ∂P)) :=
    Filter.Tendsto.congr' (Eventually.of_forall hrow) hconv
  have harg : Tendsto (fun j : ℕ => RademacherCosine.angle (j + 1) *
      (latticeStart (j + 1) u : ℝ)) atTop (𝓝 (Real.pi * u / 2)) := by
    convert (start_tendsto u hu).const_mul (Real.pi / 2) using 1
    · funext j
      dsimp [RademacherCosine.angle, H]
      field_simp [show (((j + 1 : ℕ) : ℝ) + 1) ≠ 0 by positivity] <;> ring
    · ring
  have hcos : Tendsto (fun j : ℕ => Real.cos (RademacherCosine.angle (j + 1) *
      (latticeStart (j + 1) u : ℝ))) atTop (𝓝 (Real.cos (Real.pi * u / 2))) :=
    (Real.continuous_cos.tendsto _).comp harg
  exact tendsto_nhds_unique hconv' ((principal_power_tendsto T).mul hcos)

theorem brownian_killed_cosine_identity
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (T : ℝ≥0)
    (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    (∫ ω, PolygonalKilledFunctionalLimit.brownianKilledCosine B T u ω ∂P) =
      Real.exp (-(Real.pi ^ 2 / 8) * (T : ℝ)) * Real.cos (Real.pi * u / 2) := by
  by_cases hT : T = 0
  · subst T
    calc
      _ = ∫ _ω : Ω, Real.cos (Real.pi * u / 2) ∂P :=
        integral_congr_ae (brownianKilledCosine_zero_ae B P hB u hu)
      _ = _ := by simp
  · simpa only [lambda] using brownianKilledCosine_integral_pos B P hB T
      (lt_of_le_of_ne (show (0 : ℝ≥0) ≤ T from zero_le) (Ne.symm hT)) u hu

end Shao.OQ4.BrownianKilledCosineIdentity
end
