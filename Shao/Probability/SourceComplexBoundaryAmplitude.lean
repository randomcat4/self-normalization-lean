import Shao.Probability.SourceFourierTestKernel
import Shao.Probability.SourceKernelAmplitudeFamily
import Shao.Probability.SourceMarkFourierNorms
import Shao.Probability.SourceKernelMarkedOutside
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory
open scoped ContDiff FourierTransform Topology

noncomputable def sourceComplexSplitTheta (t : ℝ) : ℝ :=
  Real.smoothTransition ((t + 1) / 2)

noncomputable def sourceComplexBoundaryAmplitude
    (j : Fin 2) (y N lam r : ℝ) : ℝ :=
  if j = 0 then
    sourceKernelCutoff r *
      sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹) *
      Real.exp (-lam * y * (Real.sqrt r - Real.sqrt N))
  else
    sourceKernelCutoff r *
      (1 - sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)) *
      Real.exp ((lam * y / Real.sqrt N) * r - lam * y * Real.sqrt r)

noncomputable def sourceComplexBoundaryMark
    (j : Fin 2) (y N lam u v : ℝ) : ℂ :=
  sourceMarkExponential (sourceComplexBoundaryAmplitude j y N lam) y (-u) v

private theorem splitTheta_smooth : ContDiff ℝ ∞ sourceComplexSplitTheta := by
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_id.add contDiff_const).div_const 2)

private theorem splitTheta_range (t : ℝ) :
    0 ≤ sourceComplexSplitTheta t ∧ sourceComplexSplitTheta t ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private theorem splitTheta_zero (t : ℝ) (ht : t ≤ -1) :
    sourceComplexSplitTheta t = 0 := by
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem splitTheta_one (t : ℝ) (ht : 1 ≤ t) :
    sourceComplexSplitTheta t = 1 := by
  exact Real.smoothTransition.one_of_one_le (by linarith)

theorem sourceComplexSplitTheta_data :
    ContDiff ℝ ∞ sourceComplexSplitTheta ∧
      (∀ t : ℝ,
        0 ≤ sourceComplexSplitTheta t ∧ sourceComplexSplitTheta t ≤ 1) ∧
      (∀ t : ℝ, t ≤ -1 → sourceComplexSplitTheta t = 0) ∧
      (∀ t : ℝ, 1 ≤ t → sourceComplexSplitTheta t = 1) ∧
      ∃ M : ℝ, 0 < M ∧
        ∀ (k : ℕ), k ≤ 32 → ∀ t : ℝ,
          |iteratedDeriv k sourceComplexSplitTheta t| ≤ M := by
  refine ⟨splitTheta_smooth, splitTheta_range, splitTheta_zero, splitTheta_one, ?_⟩
  have hb : ∀ k : Fin 33, ∃ C : ℝ,
      ∀ t ∈ Set.Icc (-1 : ℝ) 1,
        |iteratedDeriv k.val sourceComplexSplitTheta t| ≤ C := by
    intro k
    obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
      (splitTheta_smooth.continuous_iteratedDeriv k.val (by simp)).abs.continuousOn
    exact ⟨C, fun t ht => hC ⟨t, ht, rfl⟩⟩
  choose C hC using hb
  let S : ℝ := ∑ k : Fin 33, max 0 (C k)
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => le_max_left _ _
  refine ⟨S + 1, by linarith, ?_⟩
  intro k hk t
  have hM : (1 : ℝ) ≤ S + 1 := by linarith
  by_cases hlo : t < -1
  · have he : sourceComplexSplitTheta =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [gt_mem_nhds hlo] with z hz
      exact splitTheta_zero z hz.le
    rw [he.iteratedDeriv_eq k]
    simp only [iteratedDeriv_const, ite_self, abs_zero]
    linarith
  · by_cases hhi : 1 < t
    · have he : sourceComplexSplitTheta =ᶠ[𝓝 t] (fun _ => (1 : ℝ)) := by
        filter_upwards [lt_mem_nhds hhi] with z hz
        exact splitTheta_one z hz.le
      rw [he.iteratedDeriv_eq k]
      simp only [iteratedDeriv_const]
      split_ifs <;> norm_num <;> linarith
    · let k' : Fin 33 := ⟨k, by omega⟩
      have ht : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩
      have hsum : max 0 (C k') ≤ S :=
        Finset.single_le_sum (fun i _ => le_max_left 0 (C i)) (Finset.mem_univ k')
      exact (hC k' t ht).trans ((le_max_right 0 (C k')).trans (by linarith))

private theorem boundary_sobolev (b : SchwartzMap ℝ ℂ) (A R : ℝ)
    (hA : 0 ≤ A) (hR : 1 ≤ R)
    (h0 : (∫ r : ℝ, ‖b r‖ ^ 2) ≤ A ^ 2)
    (h1 : (∫ r : ℝ, ‖SchwartzMap.derivCLM ℂ ℂ b r‖ ^ 2) ≤ (A * R) ^ 2)
    (h2 : (∫ r : ℝ, ‖SchwartzMap.derivCLM ℂ ℂ
      (SchwartzMap.derivCLM ℂ ℂ b) r‖ ^ 2) ≤ (A * R ^ 2) ^ 2) :
    Integrable (fun v : ℝ => ‖∫ r : ℝ, b r *
      Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I))‖) ∧
      Integrable (fun v : ℝ => |v| * ‖∫ r : ℝ, b r *
        Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I))‖) ∧
      (∫ v : ℝ, ‖∫ r : ℝ, b r *
        Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I))‖) ≤
          256 * A * Real.sqrt R ∧
      (∫ v : ℝ, |v| * ‖∫ r : ℝ, b r *
        Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I))‖) ≤
          256 * A * R * Real.sqrt R := by
  run_tac
    let n : Lean.Name := .str (.str (.str
      (.num (.str (.str (.str (.str .anonymous "_private") "Shao")
        "Probability") "SourceMarkFourierNorms") 0) "Shao") "Probability")
      "unitFourier_schwartz_norms"
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      apply $(Lean.mkIdent n) <;> assumption))

private theorem boundaryAmplitude_tsupport (j : Fin 2) (y N lam : ℝ) :
    tsupport (sourceComplexBoundaryAmplitude j y N lam) ⊆
      tsupport sourceKernelCutoff := by
  apply closure_mono
  intro r hr hc
  exact hr (by simp [sourceComplexBoundaryAmplitude, hc])

private theorem boundaryAmplitude_smooth (j : Fin 2) (y N lam : ℝ) :
    ContDiff ℝ ∞ (sourceComplexBoundaryAmplitude j y N lam) := by
  have htheta : ContDiff ℝ ∞ (fun r : ℝ =>
      sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)) :=
    splitTheta_smooth.comp ((contDiff_id.sub contDiff_const).div_const _)
  rw [contDiff_iff_contDiffAt]
  intro r
  change ContDiffAt ℝ ∞ (fun x : ℝ => sourceComplexBoundaryAmplitude j y N lam x) r
  by_cases hr : r ∈ tsupport sourceKernelCutoff
  · have hr' := sourceKernelCutoff_data.2.2.2.2 hr
    have hs : ContDiffAt ℝ ∞ Real.sqrt r :=
      contDiffAt_id.sqrt (show r ≠ 0 by linarith [hr'.1])
    by_cases hj : j = 0
    · have he : ContDiffAt ℝ ∞ (fun x : ℝ =>
          Real.exp (-lam * y * (Real.sqrt x - Real.sqrt N))) r :=
        (contDiffAt_const.mul (hs.sub contDiffAt_const)).exp
      simpa only [sourceComplexBoundaryAmplitude, ite_eq_left hj] using
        (sourceKernelCutoff_data.1.contDiffAt.mul htheta.contDiffAt).mul he
    · have he : ContDiffAt ℝ ∞ (fun x : ℝ =>
          Real.exp ((lam * y / Real.sqrt N) * x - lam * y * Real.sqrt x)) r :=
        ((contDiffAt_const.mul contDiffAt_id).sub (contDiffAt_const.mul hs)).exp
      have hc : ContDiffAt ℝ ∞ (fun x : ℝ =>
          1 - sourceComplexSplitTheta ((x - N) / (1 + lam * y)⁻¹)) r :=
        contDiffAt_const.sub htheta.contDiffAt
      simpa only [sourceComplexBoundaryAmplitude, ite_eq_right hj] using
        (sourceKernelCutoff_data.1.contDiffAt.mul
          hc).mul he
  · have hc := notMem_tsupport_iff_eventuallyEq.mp hr
    have he : sourceComplexBoundaryAmplitude j y N lam =ᶠ[𝓝 r] 0 := by
      filter_upwards [hc] with z hz
      simp only [Pi.zero_apply] at hz ⊢
      simp [sourceComplexBoundaryAmplitude, hz]
    exact contDiffAt_const.congr_of_eventuallyEq he

private theorem boundaryAmplitude_compact (j : Fin 2) (y N lam : ℝ) :
    HasCompactSupport (sourceComplexBoundaryAmplitude j y N lam) :=
  sourceKernelCutoff_data.2.1.of_isClosed_subset (isClosed_tsupport _)
    (boundaryAmplitude_tsupport j y N lam)

private theorem boundaryAmplitude_nonneg (j : Fin 2) (y N lam r : ℝ) :
    0 ≤ sourceComplexBoundaryAmplitude j y N lam r := by
  have hc := (sourceKernelCutoff_data.2.2.1 r).1
  have ht := splitTheta_range ((r - N) / (1 + lam * y)⁻¹)
  unfold sourceComplexBoundaryAmplitude
  split_ifs
  · exact mul_nonneg (mul_nonneg hc ht.1) (Real.exp_pos _).le
  · exact mul_nonneg (mul_nonneg hc (sub_nonneg.mpr ht.2)) (Real.exp_pos _).le

private theorem boundaryAmplitude_split_support (j : Fin 2) (y N lam : ℝ)
    (hD : 0 < (1 + lam * y)⁻¹) :
    tsupport (sourceComplexBoundaryAmplitude j y N lam) ⊆
      tsupport sourceKernelCutoff ∩
        (if j = 0 then Set.Ici (N - (1 + lam * y)⁻¹)
          else Set.Iic (N + (1 + lam * y)⁻¹)) := by
  refine Set.subset_inter (boundaryAmplitude_tsupport j y N lam) ?_
  by_cases hj : j = 0
  · rw [if_pos hj]
    apply closure_minimal ?_ isClosed_Ici
    intro r hr
    change N - (1 + lam * y)⁻¹ ≤ r
    by_contra hn
    have ht : (r - N) / (1 + lam * y)⁻¹ ≤ -1 :=
      (div_le_iff₀ hD).mpr (by linarith)
    exact hr (by simp only [sourceComplexBoundaryAmplitude, ite_eq_left hj,
      splitTheta_zero _ ht, mul_zero, zero_mul])
  · rw [if_neg hj]
    apply closure_minimal ?_ isClosed_Iic
    intro r hr
    change r ≤ N + (1 + lam * y)⁻¹
    by_contra hn
    have ht : 1 ≤ (r - N) / (1 + lam * y)⁻¹ :=
      (le_div_iff₀ hD).mpr (by linarith)
    exact hr (by simp only [sourceComplexBoundaryAmplitude, ite_eq_right hj,
      splitTheta_one _ ht, sub_self, mul_zero, zero_mul])

private theorem boundaryAmplitude_recombine (y N lam r : ℝ) :
    Real.exp (-lam * y * Real.sqrt N) *
        sourceComplexBoundaryAmplitude 0 y N lam r +
      Real.exp (-(lam * y / Real.sqrt N) * r) *
        sourceComplexBoundaryAmplitude 1 y N lam r =
      sourceKernelCutoff r * Real.exp (-lam * y * Real.sqrt r) := by
  let v : ℝ := sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)
  have h0 : Real.exp (-lam * y * Real.sqrt N) *
      sourceComplexBoundaryAmplitude 0 y N lam r =
      sourceKernelCutoff r * v * Real.exp (-lam * y * Real.sqrt r) := by
    simp only [sourceComplexBoundaryAmplitude, if_pos rfl]
    calc
      _ = sourceKernelCutoff r * v *
          (Real.exp (-lam * y * Real.sqrt N) *
            Real.exp (-lam * y * (Real.sqrt r - Real.sqrt N))) := by dsimp [v]; ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  have h1 : Real.exp (-(lam * y / Real.sqrt N) * r) *
      sourceComplexBoundaryAmplitude 1 y N lam r =
      sourceKernelCutoff r * (1 - v) * Real.exp (-lam * y * Real.sqrt r) := by
    simp only [sourceComplexBoundaryAmplitude, show (1 : Fin 2) ≠ 0 by decide, if_false]
    calc
      _ = sourceKernelCutoff r * (1 - v) *
          (Real.exp (-(lam * y / Real.sqrt N) * r) *
            Real.exp ((lam * y / Real.sqrt N) * r - lam * y * Real.sqrt r)) := by
        dsimp [v]; ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  rw [h0, h1]
  ring

private theorem finite_jet_compact_bound (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (a b : ℝ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ k : ℕ, k ≤ 32 → ∀ r ∈ Set.Icc a b,
      |iteratedDeriv k f r| ≤ M := by
  have hb : ∀ k : Fin 33, ∃ C : ℝ,
      ∀ r ∈ Set.Icc a b, |iteratedDeriv k.val f r| ≤ C := by
    intro k
    obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
      (hf.continuous_iteratedDeriv k.val (by simp)).abs.continuousOn
    exact ⟨C, fun r hr => hC ⟨r, hr, rfl⟩⟩
  choose C hC using hb
  let S : ℝ := ∑ k : Fin 33, max 0 (C k)
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => le_max_left _ _
  refine ⟨S + 1, by linarith, ?_⟩
  intro k hk r hr
  let k' : Fin 33 := ⟨k, by omega⟩
  have hsum : max 0 (C k') ≤ S :=
    Finset.single_le_sum (fun i _ => le_max_left 0 (C i)) (Finset.mem_univ k')
  exact (hC k' r hr).trans ((le_max_right 0 (C k')).trans (by linarith))

private theorem smooth_sqrt_extension :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
      (∀ r : ℝ, (1 / 16 : ℝ) ≤ r → g r = Real.sqrt r) ∧
      ∃ M : ℝ, 1 ≤ M ∧ ∀ k : ℕ, k ≤ 32 →
        ∀ r ∈ Set.Icc (1 / 16 : ℝ) 4, |iteratedDeriv k g r| ≤ M := by
  let rho : ℝ → ℝ := fun r =>
    (1 / 32 : ℝ) + (r - 1 / 32) * sourceComplexSplitTheta (64 * r - 3)
  have hRho : ContDiff ℝ ∞ rho :=
    contDiff_const.add ((contDiff_id.sub contDiff_const).mul
      (splitTheta_smooth.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)))
  have hpos : ∀ r : ℝ, 0 < rho r := by
    intro r
    by_cases hr : r ≤ (1 / 32 : ℝ)
    · have ht : 64 * r - 3 ≤ -1 := by linarith
      simp only [rho, splitTheta_zero _ ht, mul_zero, add_zero]
      norm_num
    · have hp := mul_nonneg (show 0 ≤ r - 1 / 32 by linarith)
        (splitTheta_range (64 * r - 3)).1
      dsimp [rho]
      linarith
  let g : ℝ → ℝ := fun r => Real.sqrt (rho r)
  have hg : ContDiff ℝ ∞ g := hRho.sqrt (fun r => (hpos r).ne')
  refine ⟨g, hg, ?_, finite_jet_compact_bound g hg (1 / 16) 4⟩
  intro r hr
  have ht : 1 ≤ 64 * r - 3 := by linarith
  dsimp [g, rho]
  rw [splitTheta_one _ ht, mul_one]
  congr 1
  ring

private theorem exp_jet_bound (E : ℝ → ℝ) (hE : ContDiff ℝ ∞ E)
    (k : ℕ) (r D : ℝ)
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ k → |iteratedDeriv i E r| ≤ D ^ i) :
    |iteratedDeriv k (fun x : ℝ => Real.exp (E x)) r| ≤
      (k.factorial : ℝ) * Real.exp (E r) * D ^ k := by
  have hC : ∀ i : ℕ, i ≤ k →
      ‖iteratedFDeriv ℝ i Real.exp (E r)‖ ≤ Real.exp (E r) := by
    intro i _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
      Real.iter_deriv_exp]
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), le_refl]
  have hb := norm_iteratedFDeriv_comp_le Real.contDiff_exp hE (by simp : (k : ℕ∞ω) ≤ ∞)
    r hC (fun i hi hik => by
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using hD i hi hik)
  simpa only [Function.comp_def, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    Real.norm_eq_abs] using hb

private theorem boundary_setup (y N lam : ℝ) (hy : 2 ≤ y)
    (hNlo : (1 / 16 : ℝ) ≤ N) (hNhi : N ≤ 7)
    (hlam : y / Real.sqrt N ≤ lam) :
    1 ≤ lam * y ∧ (1 / 4 : ℝ) ≤ Real.sqrt N ∧ Real.sqrt N ≤ 3 ∧
      0 < (1 + lam * y)⁻¹ ∧ (1 + lam * y)⁻¹ ≤ 1 := by
  have hN : 0 < N := by linarith
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hslo : (1 / 4 : ℝ) ≤ Real.sqrt N := by
    have hsq := Real.sq_sqrt hN.le
    nlinarith [Real.sqrt_nonneg N]
  have hshi : Real.sqrt N ≤ 3 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hypos : 0 < y := by linarith
  have hlpos : 0 < lam := lt_of_lt_of_le (div_pos hypos hs) hlam
  have hl : y ≤ 3 * lam := by
    calc
      y ≤ lam * Real.sqrt N := (div_le_iff₀ hs).mp hlam
      _ ≤ lam * 3 := mul_le_mul_of_nonneg_left hshi hlpos.le
      _ = 3 * lam := mul_comm _ _
  have ht : 1 ≤ lam * y := by
    have hp := mul_nonneg (show 0 ≤ 3 * lam - y by linarith) hypos.le
    nlinarith [sq_nonneg (y - 2)]
  refine ⟨ht, hslo, hshi, inv_pos.mpr (by linarith), ?_⟩
  exact (inv_le_one₀ (by linarith : 0 < 1 + lam * y)).mpr (by linarith)

private theorem product_jet_bound (f g : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (k : ℕ) (r A B Q : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hQ : 0 ≤ Q)
    (hfb : ∀ i : ℕ, i ≤ k → |iteratedDeriv i f r| ≤ A * Q ^ i)
    (hgb : ∀ i : ℕ, i ≤ k → |iteratedDeriv i g r| ≤ B * Q ^ i) :
    |iteratedDeriv k (fun x => f x * g x) r| ≤ A * B * (2 * Q) ^ k := by
  change |iteratedDeriv k (f * g) r| ≤ _
  rw [iteratedDeriv_mul (hf.contDiffAt.of_le (by simp))
    (hg.contDiffAt.of_le (by simp))]
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1),
        |(k.choose i : ℝ) * iteratedDeriv i f r * iteratedDeriv (k - i) g r| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * (A * Q ^ i) * (B * Q ^ (k - i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      simp only [abs_mul,
        abs_of_nonneg (Nat.cast_nonneg (k.choose i) : (0 : ℝ) ≤ (k.choose i : ℝ))]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfb i hik)
          (Nat.cast_nonneg (k.choose i) : (0 : ℝ) ≤ (k.choose i : ℝ)))
        (hgb (k - i) (Nat.sub_le _ _)) (abs_nonneg _) (by positivity)
    _ = A * B * Q ^ k * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hp : Q ^ i * Q ^ (k - i) = Q ^ k := by
        rw [← pow_add, Nat.add_sub_of_le hik]
      calc
        _ = (k.choose i : ℝ) * A * B * (Q ^ i * Q ^ (k - i)) := by ring
        _ = _ := by rw [hp]; ring
    _ = A * B * (2 * Q) ^ k := by
      rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat, mul_pow]
      ring

private theorem exponential_linear_jet_bound (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (M : ℝ) (hM : 0 ≤ M) (r : ℝ)
    (hgb : ∀ i : ℕ, i ≤ 32 → |iteratedDeriv i g r| ≤ M)
    (a b c D : ℝ) (hD : 1 ≤ D) (hab : |a| + |b| * M ≤ D)
    (k : ℕ) (hk : k ≤ 32) :
    |iteratedDeriv k (fun x : ℝ => Real.exp (a * x + b * g x + c)) r| ≤
      (k.factorial : ℝ) * Real.exp (a * r + b * g r + c) * D ^ k := by
  let E : ℝ → ℝ := fun x => a * x + b * g x + c
  have hE : ContDiff ℝ ∞ E :=
    ((contDiff_const.mul contDiff_id).add (contDiff_const.mul hg)).add contDiff_const
  apply exp_jet_bound E hE k r D
  intro i hi hik
  have hi0 : i ≠ 0 := by omega
  have hid : |iteratedDeriv i (fun x : ℝ => x) r| ≤ 1 := by
    simp only [iteratedDeriv_fun_id, if_neg hi0]
    split_ifs <;> norm_num
  have heq : E = fun x => c + (a * x + b * g x) := by
    funext x
    dsimp [E]
    ring
  have he : iteratedDeriv i E r =
      a * iteratedDeriv i (fun x : ℝ => x) r + b * iteratedDeriv i g r := by
    rw [heq, iteratedDeriv_const_add (by omega : 0 < i)]
    change iteratedDeriv i ((fun x : ℝ => a * x) + (fun x => b * g x)) r = _
    have hl : ContDiffAt ℝ i (fun x : ℝ => a * x) r :=
      ((contDiff_const.mul (contDiff_id : ContDiff ℝ ∞ (fun x : ℝ => x))).contDiffAt.of_le
        (by simp))
    have hgg : ContDiffAt ℝ i (fun x : ℝ => b * g x) r :=
      (contDiff_const.mul hg).contDiffAt.of_le (by simp)
    rw [iteratedDeriv_add hl hgg,
      iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  have hle : |iteratedDeriv i E r| ≤ D := by
    rw [he]
    calc
      _ ≤ |a * iteratedDeriv i (fun x : ℝ => x) r| + |b * iteratedDeriv i g r| :=
        abs_add_le _ _
      _ ≤ |a| * 1 + |b| * M := by
        simp only [abs_mul]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hid (abs_nonneg a))
          (mul_le_mul_of_nonneg_left (hgb i (hik.trans hk)) (abs_nonneg b))
      _ ≤ D := by simpa only [mul_one] using hab
  exact hle.trans (by simpa only [pow_one] using pow_le_pow_right₀ hD hi)

private theorem upper_exponent_decay (t N r : ℝ) (ht : 1 ≤ t)
    (hNlo : (1 / 16 : ℝ) ≤ N) (hNhi : N ≤ 7)
    (hrlo : (1 / 16 : ℝ) ≤ r) (hrhi : r ≤ 4)
    (hside : N - (1 + t)⁻¹ ≤ r) :
    -t * (Real.sqrt r - Real.sqrt N) ≤
      4 - (1 / 256 : ℝ) * |r - N| * (1 + t) := by
  have hN : 0 ≤ N := by linarith
  have hr : 0 ≤ r := by linarith
  have hsnlo : (1 / 4 : ℝ) ≤ Real.sqrt N := by
    nlinarith [Real.sq_sqrt hN, Real.sqrt_nonneg N]
  have hsrlo : (1 / 4 : ℝ) ≤ Real.sqrt r := by
    nlinarith [Real.sq_sqrt hr, Real.sqrt_nonneg r]
  have hsnhi : Real.sqrt N ≤ 3 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsrhi : Real.sqrt r ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hid : (Real.sqrt r - Real.sqrt N) * (Real.sqrt r + Real.sqrt N) = r - N := by
    nlinarith [Real.sq_sqrt hr, Real.sq_sqrt hN]
  have ht0 : 0 ≤ t := by linarith
  by_cases h : N ≤ r
  · have hd : 0 ≤ r - N := sub_nonneg.mpr h
    have hdiff0 : 0 ≤ Real.sqrt r - Real.sqrt N := sub_nonneg.mpr (Real.sqrt_le_sqrt h)
    have hdiff : (r - N) / 5 ≤ Real.sqrt r - Real.sqrt N := by
      have hm := mul_le_mul_of_nonneg_left
        (show Real.sqrt r + Real.sqrt N ≤ 5 by linarith) hdiff0
      nlinarith [hid]
    have hc : (1 + t) / 256 ≤ t / 5 := by linarith
    have hb : (1 + t) * (r - N) / 256 ≤ t * (Real.sqrt r - Real.sqrt N) := by
      calc
        _ = ((1 + t) / 256) * (r - N) := by ring
        _ ≤ (t / 5) * (r - N) := mul_le_mul_of_nonneg_right hc hd
        _ = t * ((r - N) / 5) := by ring
        _ ≤ t * (Real.sqrt r - Real.sqrt N) := mul_le_mul_of_nonneg_left hdiff ht0
    rw [abs_of_nonneg hd]
    nlinarith
  · have hd : 0 ≤ N - r := by linarith
    have hQ : 0 < 1 + t := by linarith
    have hqd : (1 + t) * (N - r) ≤ 1 := by
      calc
        _ ≤ (1 + t) * (1 + t)⁻¹ := mul_le_mul_of_nonneg_left (by linarith) hQ.le
        _ = 1 := mul_inv_cancel₀ hQ.ne'
    have htd : t * (N - r) ≤ 1 :=
      (mul_le_mul_of_nonneg_right (by linarith : t ≤ 1 + t) hd).trans hqd
    have hdiff0 : 0 ≤ Real.sqrt N - Real.sqrt r :=
      sub_nonneg.mpr (Real.sqrt_le_sqrt (le_of_not_ge h))
    have hdiff : Real.sqrt N - Real.sqrt r ≤ 2 * (N - r) := by
      have hm := mul_le_mul_of_nonneg_left
        (show (1 / 2 : ℝ) ≤ Real.sqrt r + Real.sqrt N by linarith) hdiff0
      nlinarith [hid]
    have he : t * (Real.sqrt N - Real.sqrt r) ≤ 2 := by
      have hm := mul_le_mul_of_nonneg_left hdiff ht0
      nlinarith [htd]
    rw [abs_of_neg (show r - N < 0 by linarith)]
    nlinarith [hqd]

private theorem lower_exponent_decay (t N r : ℝ) (ht : 1 ≤ t)
    (hNlo : (1 / 16 : ℝ) ≤ N) (hNhi : N ≤ 7)
    (hrlo : (1 / 16 : ℝ) ≤ r) (hrhi : r ≤ 4)
    (hside : r ≤ N + (1 + t)⁻¹) :
    (t / Real.sqrt N) * r - t * Real.sqrt r ≤
      4 - (1 / 256 : ℝ) * |r - N| * (1 + t) := by
  have hN : 0 ≤ N := by linarith
  have hr : 0 ≤ r := by linarith
  have hsnlo : (1 / 4 : ℝ) ≤ Real.sqrt N := by
    nlinarith [Real.sq_sqrt hN, Real.sqrt_nonneg N]
  have hsrlo : (1 / 4 : ℝ) ≤ Real.sqrt r := by
    nlinarith [Real.sq_sqrt hr, Real.sqrt_nonneg r]
  have hsnhi : Real.sqrt N ≤ 3 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsrhi : Real.sqrt r ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsn : 0 < Real.sqrt N := by linarith
  have hsum : 0 < Real.sqrt N + Real.sqrt r := by linarith
  let c : ℝ := Real.sqrt r / (Real.sqrt N * (Real.sqrt N + Real.sqrt r))
  have hden : 0 < Real.sqrt N * (Real.sqrt N + Real.sqrt r) := mul_pos hsn hsum
  have hdenhi : Real.sqrt N * (Real.sqrt N + Real.sqrt r) ≤ 15 := by
    have hm := mul_le_mul hsnhi
      (show Real.sqrt N + Real.sqrt r ≤ 5 by linarith) hsum.le (by norm_num : (0 : ℝ) ≤ 3)
    norm_num at hm ⊢
    exact hm
  have hclo : (1 / 60 : ℝ) ≤ c := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  have hcEq : c = 1 / Real.sqrt N - 1 / (Real.sqrt N + Real.sqrt r) := by
    dsimp [c]
    field_simp
    ring
  have hchi : c ≤ (19 / 5 : ℝ) := by
    have h1 : 1 / Real.sqrt N ≤ (4 : ℝ) := (div_le_iff₀ hsn).mpr (by linarith)
    have h2 : (1 / 5 : ℝ) ≤ 1 / (Real.sqrt N + Real.sqrt r) :=
      (le_div_iff₀ hsum).mpr (by linarith)
    linarith [hcEq]
  have hid : Real.sqrt r - Real.sqrt N =
      (r - N) / (Real.sqrt N + Real.sqrt r) := by
    apply (eq_div_iff hsum.ne').mpr
    nlinarith [Real.sq_sqrt hr, Real.sq_sqrt hN]
  have hrid : r / Real.sqrt N - Real.sqrt r =
      (Real.sqrt r / Real.sqrt N) * (Real.sqrt r - Real.sqrt N) := by
    field_simp
    nlinarith [Real.sq_sqrt hr]
  have heq : (t / Real.sqrt N) * r - t * Real.sqrt r = t * c * (r - N) := by
    calc
      _ = t * (r / Real.sqrt N - Real.sqrt r) := by ring
      _ = t * ((Real.sqrt r / Real.sqrt N) *
          ((r - N) / (Real.sqrt N + Real.sqrt r))) := by rw [hrid, hid]
      _ = _ := by dsimp [c]; field_simp <;> ring
  have ht0 : 0 ≤ t := by linarith
  rw [heq]
  by_cases h : r ≤ N
  · have hd : 0 ≤ N - r := sub_nonneg.mpr h
    have hc : (1 + t) / 256 ≤ t * c := by
      have hm := mul_le_mul_of_nonneg_left hclo ht0
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hc hd
    rw [abs_of_nonpos (show r - N ≤ 0 by linarith)]
    nlinarith
  · have hd : 0 ≤ r - N := by linarith
    have hQ : 0 < 1 + t := by linarith
    have hqd : (1 + t) * (r - N) ≤ 1 := by
      calc
        _ ≤ (1 + t) * (1 + t)⁻¹ := mul_le_mul_of_nonneg_left (by linarith) hQ.le
        _ = 1 := mul_inv_cancel₀ hQ.ne'
    have htd : t * (r - N) ≤ 1 :=
      (mul_le_mul_of_nonneg_right (by linarith : t ≤ 1 + t) hd).trans hqd
    have he : t * c * (r - N) ≤ (19 / 5 : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hchi (mul_nonneg ht0 hd)
      nlinarith [htd]
    rw [abs_of_nonneg hd]
    nlinarith [hqd]

private theorem scaled_split_jet_bound :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (Q N : ℝ), 1 ≤ Q → ∀ j : Fin 2,
      let f : ℝ → ℝ := fun x =>
        if j = 0 then sourceComplexSplitTheta (Q * (x - N))
        else 1 - sourceComplexSplitTheta (Q * (x - N))
      ContDiff ℝ ∞ f ∧ ∀ i : ℕ, i ≤ 32 → ∀ r : ℝ,
        |iteratedDeriv i f r| ≤ M * Q ^ i := by
  obtain ⟨M, hM, hb⟩ := sourceComplexSplitTheta_data.2.2.2.2
  have hM1 : 1 ≤ M := by
    have h := hb 0 (by omega) 1
    simpa only [iteratedDeriv_zero, splitTheta_one 1 le_rfl, abs_one] using h
  refine ⟨M, hM1, ?_⟩
  intro Q N hQ j
  let f : ℝ → ℝ := fun x => sourceComplexSplitTheta (Q * (x - N))
  have hf : ContDiff ℝ ∞ f :=
    splitTheta_smooth.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
  have hfb : ∀ i : ℕ, i ≤ 32 → ∀ r : ℝ, |iteratedDeriv i f r| ≤ M * Q ^ i := by
    intro i hi r
    have he : iteratedDeriv i f r =
        Q ^ i * iteratedDeriv i sourceComplexSplitTheta (Q * (r - N)) := by
      change iteratedDeriv i
        (fun x => (fun z => sourceComplexSplitTheta (Q * z)) (x - N)) r = _
      calc
        _ = iteratedDeriv i (fun z : ℝ => sourceComplexSplitTheta (Q * z)) (r - N) :=
          congrFun (iteratedDeriv_comp_sub_const i
            (fun z : ℝ => sourceComplexSplitTheta (Q * z)) N) r
        _ = _ := congrFun (iteratedDeriv_comp_const_mul
          (splitTheta_smooth.of_le (by simp)) Q) (r - N)
    rw [he, abs_mul, abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ Q) i)]
    exact (mul_le_mul_of_nonneg_left (hb i hi _) (by positivity)).trans_eq (mul_comm _ _)
  by_cases hj : j = 0
  · simpa only [ite_eq_left hj] using And.intro hf hfb
  · refine ⟨?_, ?_⟩
    · simpa only [ite_eq_right hj] using (contDiff_const.sub hf :
        ContDiff ℝ ∞ (fun x => 1 - f x))
    · intro i hi r
      simp only [ite_eq_right hj]
      by_cases hi0 : i = 0
      · subst i
        have hθ := splitTheta_range (Q * (r - N))
        simp only [iteratedDeriv_zero, pow_zero, mul_one]
        rw [abs_of_nonneg (sub_nonneg.mpr hθ.2)]
        linarith [hθ.1]
      · have he : iteratedDeriv i (fun x => 1 - f x) r = -iteratedDeriv i f r := by
          rw [iteratedDeriv_const_sub (by omega : 0 < i), iteratedDeriv_neg]
        rw [he, abs_neg]
        exact hfb i hi r

private theorem actual_amplitude_derivative_envelope :
    ∃ C : ℝ, 0 < C ∧ ∀ (y N lam : ℝ),
      2 ≤ y → (1 / 16 : ℝ) ≤ N → N ≤ 7 → y / Real.sqrt N ≤ lam →
      ∀ (j : Fin 2) (k : ℕ), k ≤ 32 → ∀ r : ℝ,
        |iteratedDeriv k (sourceComplexBoundaryAmplitude j y N lam) r| ≤
          C * (1 + lam * y) ^ k *
            Real.exp (-((1 / 256 : ℝ) * |r - N| * (1 + lam * y))) := by
  obtain ⟨X, hX, hXb⟩ := sourceKernel_marked_amplitude_family
  have hchi : ∀ k : ℕ, k ≤ 32 → ∀ r : ℝ,
      |iteratedDeriv k sourceKernelCutoff r| ≤ X := by
    intro k hk r
    simpa only [pow_zero, div_one] using
      (hXb 0 (Or.inl rfl) 0 (by norm_num)).2.2 k hk r
  obtain ⟨Theta, hTheta, hThetaB⟩ := scaled_split_jet_bound
  obtain ⟨g, hg, hgeq, G, hG, hGb⟩ := smooth_sqrt_extension
  let K : ℝ := G + 4
  let Ce : ℝ := ((32 : ℕ).factorial : ℝ) * K ^ 32
  let C : ℝ := X * Theta * Ce * 4 ^ 32 * Real.exp 4
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hKpos : 0 < K := by linarith
  have hCe : 0 < Ce := mul_pos
    (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos hKpos _)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro y N lam hy hNlo hNhi hlam j k hk r
  obtain ⟨ht, hsnlo, hsnhi, hDpos, hDle⟩ := boundary_setup y N lam hy hNlo hNhi hlam
  let t : ℝ := lam * y
  let Q : ℝ := 1 + t
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have hQ : 1 ≤ Q := by dsimp [Q, t]; linarith
  have hQ0 : 0 ≤ Q := by linarith
  let a : ℝ → ℝ := sourceComplexBoundaryAmplitude j y N lam
  change |iteratedDeriv k a r| ≤ _
  by_cases hr : r ∈ tsupport a
  · have hsupp := boundaryAmplitude_split_support j y N lam hDpos hr
    have hχr := sourceKernelCutoff_data.2.2.2.2 hsupp.1
    have hri : r ∈ Set.Icc (1 / 16 : ℝ) 4 := ⟨hχr.1.le, hχr.2.le⟩
    let f : ℝ → ℝ := fun x =>
      if j = 0 then sourceComplexSplitTheta (Q * (x - N))
      else 1 - sourceComplexSplitTheta (Q * (x - N))
    obtain ⟨hf, hfb⟩ := hThetaB Q N hQ j
    let alpha : ℝ := if j = 0 then 0 else t / Real.sqrt N
    let gamma : ℝ := if j = 0 then t * Real.sqrt N else 0
    let e : ℝ → ℝ := fun x => Real.exp (alpha * x + (-t) * g x + gamma)
    have he : ContDiff ℝ ∞ e :=
      (((contDiff_const.mul contDiff_id).add (contDiff_const.mul hg)).add contDiff_const).exp
    have halpha : |alpha| ≤ 4 * t := by
      have hsn : 0 < Real.sqrt N := by linarith
      dsimp [alpha]
      split_ifs
      · simp only [abs_zero]
        positivity
      · rw [abs_of_nonneg (div_nonneg ht0 hsn.le)]
        exact (div_le_iff₀ hsn).mpr (by nlinarith)
    have hcoeff : |alpha| + |-t| * G ≤ K * Q := by
      rw [abs_neg, abs_of_nonneg ht0]
      dsimp [K, Q]
      nlinarith [halpha]
    have hD : 1 ≤ K * Q := by
      nlinarith [mul_nonneg (show 0 ≤ K - 1 by linarith) (show 0 ≤ Q - 1 by linarith)]
    have heb : ∀ i : ℕ, i ≤ 32 →
        |iteratedDeriv i e r| ≤ (Ce * e r) * Q ^ i := by
      intro i hi
      have hb := exponential_linear_jet_bound g hg G (by linarith) r
        (fun m hm => hGb m hm r hri) alpha (-t) gamma (K * Q) hD hcoeff i hi
      have hfact : (i.factorial : ℝ) ≤ ((32 : ℕ).factorial : ℝ) :=
        Nat.cast_le.mpr (Nat.factorial_le hi)
      have hpow : K ^ i ≤ K ^ 32 := pow_le_pow_right₀ hK hi
      have hconst : (i.factorial : ℝ) * K ^ i ≤ Ce :=
        mul_le_mul hfact hpow (by positivity) (by positivity)
      calc
        _ ≤ (i.factorial : ℝ) * e r * (K * Q) ^ i := hb
        _ = ((i.factorial : ℝ) * K ^ i) * (e r * Q ^ i) := by rw [mul_pow]; ring
        _ ≤ Ce * (e r * Q ^ i) := mul_le_mul_of_nonneg_right hconst (by dsimp [e]; positivity)
        _ = _ := by ring
    have hedecay : alpha * r + (-t) * g r + gamma ≤
        4 - (1 / 256 : ℝ) * |r - N| * Q := by
      rw [hgeq r hri.1]
      by_cases hj : j = 0
      · have hside : N - (1 + t)⁻¹ ≤ r := by
          simpa only [ite_eq_left hj, Set.mem_Ici, t] using hsupp.2
        have hd := upper_exponent_decay t N r ht hNlo hNhi hri.1 hri.2 hside
        simp only [alpha, gamma, ite_eq_left hj, zero_mul]
        dsimp [Q]
        nlinarith
      · have hside : r ≤ N + (1 + t)⁻¹ := by
          simpa only [ite_eq_right hj, Set.mem_Iic, t] using hsupp.2
        have hd := lower_exponent_decay t N r ht hNlo hNhi hri.1 hri.2 hside
        simp only [alpha, gamma, ite_eq_right hj, add_zero]
        dsimp [Q]
        nlinarith
    have heexp : e r ≤ Real.exp 4 *
        Real.exp (-((1 / 256 : ℝ) * |r - N| * Q)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by simpa only [sub_eq_add_neg] using hedecay)
    have haeq : a = fun x => (sourceKernelCutoff x * f x) * e x := by
      funext x
      by_cases hc : sourceKernelCutoff x = 0
      · simp [a, sourceComplexBoundaryAmplitude, hc]
      · have hx := sourceKernelCutoff_data.2.2.2.2 (subset_tsupport _ hc)
        have hgx := hgeq x hx.1.le
        have harg : (x - N) / (1 + lam * y)⁻¹ = Q * (x - N) := by
          dsimp [Q, t]
          rw [div_inv_eq_mul]
          ring
        dsimp [a, f, e, alpha, gamma]
        rw [sourceComplexBoundaryAmplitude, harg, hgx]
        split_ifs <;> congr 1 <;> congr 1 <;> dsimp [t] <;> ring
    have hfirst : ∀ i : ℕ, i ≤ 32 →
        |iteratedDeriv i (fun x => sourceKernelCutoff x * f x) r| ≤
          (X * Theta) * (2 * Q) ^ i := by
      intro i hi
      apply product_jet_bound sourceKernelCutoff f sourceKernelCutoff_data.1 hf i r
        X Theta Q hX.le (by linarith) hQ0
      · intro m hm
        exact (hchi m (hm.trans hi) r).trans
          (le_mul_of_one_le_right hX.le (one_le_pow₀ hQ))
      · exact fun m hm => hfb m (hm.trans hi) r
    rw [haeq]
    have hb := product_jet_bound (fun x => sourceKernelCutoff x * f x) e
      (sourceKernelCutoff_data.1.mul hf) he k r (X * Theta) (Ce * e r) (2 * Q)
      (by positivity) (by dsimp [e]; positivity) (by positivity)
      (fun i hi => hfirst i (hi.trans hk))
      (fun i hi => (heb i (hi.trans hk)).trans
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hQ0 (by linarith : Q ≤ 2 * Q) i) (by dsimp [e]; positivity)))
    calc
      _ ≤ X * Theta * (Ce * e r) * (2 * (2 * Q)) ^ k := hb
      _ = (X * Theta * Ce) * (4 ^ k * Q ^ k) * e r := by
        rw [show 2 * (2 * Q) = 4 * Q by ring, mul_pow]
        ring
      _ ≤ (X * Theta * Ce) * (4 ^ 32 * Q ^ k) *
          (Real.exp 4 * Real.exp (-((1 / 256 : ℝ) * |r - N| * Q))) := by
        gcongr <;> norm_num
      _ = _ := by dsimp [C, Q, t]; ring
  · have he : a =ᶠ[𝓝 r] (fun _ => (0 : ℝ)) := notMem_tsupport_iff_eventuallyEq.mp hr
    rw [he.iteratedDeriv_eq k]
    simp only [iteratedDeriv_const, ite_self, abs_zero]
    positivity

private theorem exp_abs_integral (b N : ℝ) (hb : 0 < b) :
    Integrable (fun r : ℝ => Real.exp (-b * |r - N|)) ∧
      (∫ r : ℝ, Real.exp (-b * |r - N|)) = 2 / b := by
  let F : ℝ → ℝ := fun r => Real.exp (-b * |r|)
  have hL : IntegrableOn F (Set.Iic 0) := by
    refine (integrableOn_exp_mul_Iic hb 0).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    dsimp [F]
    rw [abs_of_nonpos hx]
    congr 1
    ring
  have hR : IntegrableOn F (Set.Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (by linarith : -b < 0) 0).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [F, abs_of_pos (show (0 : ℝ) < x from hx)]
  have hi : Integrable F := by
    simpa only [Set.Iic_union_Ioi, integrableOn_univ] using hL.union hR
  have hLi : (∫ x in Set.Iic 0, F x) = 1 / b := by
    calc
      _ = ∫ x in Set.Iic 0, Real.exp (b * x) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro x hx
        dsimp [F]
        rw [abs_of_nonpos hx]
        congr 1
        ring
      _ = _ := by rw [integral_exp_mul_Iic hb]; simp
  have hRi : (∫ x in Set.Ioi 0, F x) = 1 / b := by
    calc
      _ = ∫ x in Set.Ioi 0, Real.exp (-b * x) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        simp only [F, abs_of_pos (show (0 : ℝ) < x from hx)]
      _ = _ := by rw [integral_exp_mul_Ioi (by linarith : -b < 0)]; simp
  have hFi : (∫ r : ℝ, F r) = 2 / b := by
    have hs := integral_add_compl (s := Set.Iic (0 : ℝ)) measurableSet_Iic hi
    rw [Set.compl_Iic, hLi, hRi] at hs
    rw [← hs]
    ring
  refine ⟨hi.comp_sub_right N, ?_⟩
  change (∫ r : ℝ, F (r - N)) = 2 / b
  rw [integral_sub_right_eq_self]
  exact hFi

theorem sourceComplexBoundaryAmplitude_localized :
    ∃ C : ℝ, 0 < C ∧
      ∀ (y N lam : ℝ),
        2 ≤ y → (1 / 16 : ℝ) ≤ N → N ≤ 7 →
        y / Real.sqrt N ≤ lam →
          let Delta : ℝ := (1 + lam * y)⁻¹
          let s : ℝ := lam * y / Real.sqrt N
          0 < Delta ∧ Delta ≤ 1 ∧
            (∀ r : ℝ,
              Real.exp (-lam * y * Real.sqrt N) *
                  sourceComplexBoundaryAmplitude 0 y N lam r +
                Real.exp (-s * r) *
                  sourceComplexBoundaryAmplitude 1 y N lam r =
                sourceKernelCutoff r * Real.exp (-lam * y * Real.sqrt r)) ∧
            ∀ j : Fin 2,
              let a : ℝ → ℝ := sourceComplexBoundaryAmplitude j y N lam
              ContDiff ℝ ∞ a ∧ HasCompactSupport a ∧
                (∀ r : ℝ, 0 ≤ a r) ∧
                tsupport a ⊆ tsupport sourceKernelCutoff ∩
                  (if j = 0 then Set.Ici (N - Delta)
                    else Set.Iic (N + Delta)) ∧
                ∀ (k : ℕ), k ≤ 32 →
                  Integrable (iteratedDeriv k a) ∧
                    (∀ r : ℝ,
                      |iteratedDeriv k a r| ≤
                        C / Delta ^ k *
                          Real.exp (-((1 / 256 : ℝ) * |r - N| / Delta))) ∧
                    (∫ r : ℝ, |iteratedDeriv k a r|) ≤
                      C * Delta / Delta ^ k := by
  obtain ⟨C, hC, hb⟩ := actual_amplitude_derivative_envelope
  refine ⟨512 * C, by positivity, ?_⟩
  intro y N lam hy hNlo hNhi hlam
  obtain ⟨ht, hsnlo, hsnhi, hDpos, hDle⟩ := boundary_setup y N lam hy hNlo hNhi hlam
  dsimp only
  refine ⟨hDpos, hDle, boundaryAmplitude_recombine y N lam, ?_⟩
  intro j
  refine ⟨boundaryAmplitude_smooth j y N lam, boundaryAmplitude_compact j y N lam,
    boundaryAmplitude_nonneg j y N lam,
    boundaryAmplitude_split_support j y N lam hDpos, ?_⟩
  intro k hk
  let a : ℝ → ℝ := sourceComplexBoundaryAmplitude j y N lam
  let Q : ℝ := 1 + lam * y
  let beta : ℝ := (1 / 256 : ℝ) * Q
  let E : ℝ → ℝ := fun r => Real.exp (-beta * |r - N|)
  have hQ : 0 < Q := by dsimp [Q]; linarith
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  obtain ⟨hEi, hEv⟩ := exp_abs_integral beta N hbeta
  have heq : ∀ r : ℝ, E r =
      Real.exp (-((1 / 256 : ℝ) * |r - N| * (1 + lam * y))) := by
    intro r
    dsimp [E, beta, Q]
    congr 1
    ring
  have hbound : ∀ r : ℝ, |iteratedDeriv k a r| ≤ C * Q ^ k * E r := by
    intro r
    simpa only [heq] using hb y N lam hy hNlo hNhi hlam j k hk r
  have hEnv : Integrable (fun r : ℝ => C * Q ^ k * E r) := hEi.const_mul _
  have hi : Integrable (iteratedDeriv k a) :=
    hEnv.mono' ((boundaryAmplitude_smooth j y N lam).continuous_iteratedDeriv k (by simp)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun r => by simpa only [Real.norm_eq_abs] using hbound r)
  refine ⟨hi, ?_, ?_⟩
  · intro r
    have hc : C * Q ^ k ≤ (512 * C) / ((1 + lam * y)⁻¹) ^ k := by
      simp only [inv_pow, div_inv_eq_mul]
      dsimp [Q]
      nlinarith [mul_nonneg hC.le (pow_nonneg (show 0 ≤ 1 + lam * y by linarith) k)]
    have h := mul_le_mul_of_nonneg_right hc (Real.exp_pos
      (-((1 / 256 : ℝ) * |r - N| * (1 + lam * y)))).le
    have hbr : |iteratedDeriv k a r| ≤ C * Q ^ k *
        Real.exp (-((1 / 256 : ℝ) * |r - N| * (1 + lam * y))) := by
      simpa only [heq] using hbound r
    exact hbr.trans (by
      simpa only [div_inv_eq_mul] using h)
  · calc
      _ ≤ ∫ r : ℝ, C * Q ^ k * E r := integral_mono hi.abs hEnv hbound
      _ = C * Q ^ k * (2 / beta) := by rw [integral_const_mul, hEv]
      _ = _ := by
        dsimp [beta]
        change C * Q ^ k * (2 / ((1 / 256 : ℝ) * Q)) =
          512 * C * Q⁻¹ / (Q⁻¹) ^ k
        rw [inv_pow, div_inv_eq_mul]
        field_simp [hQ.ne'] <;> ring

private theorem boundaryMark_eq (j : Fin 2) (y N lam u v : ℝ) :
    sourceComplexBoundaryMark j y N lam u v =
      ∫ r : ℝ, (sourceComplexBoundaryAmplitude j y N lam r : ℂ) *
        Complex.exp (-(((u * y * Real.sqrt r + v * r : ℝ) : ℂ) * Complex.I)) := by
  unfold sourceComplexBoundaryMark sourceMarkExponential
  apply integral_congr_ae
  filter_upwards with r
  congr 1
  congr 1
  push_cast
  ring

private theorem boundaryMark_phase_integrable (j : Fin 2) (y N lam u v : ℝ) :
    Integrable (fun r : ℝ => (sourceComplexBoundaryAmplitude j y N lam r : ℂ) *
      Complex.exp (-(((u * y * Real.sqrt r + v * r : ℝ) : ℂ) * Complex.I))) := by
  have ha : Integrable (sourceComplexBoundaryAmplitude j y N lam) :=
    (boundaryAmplitude_smooth j y N lam).continuous.integrable_of_hasCompactSupport
    (boundaryAmplitude_compact j y N lam)
  have hp : Continuous (fun r : ℝ =>
      Complex.exp (-(((u * y * Real.sqrt r + v * r : ℝ) : ℂ) * Complex.I))) := by
    fun_prop
  refine ha.norm.mono' ((ha.ofReal (𝕜 := ℂ)).aestronglyMeasurable.mul
    hp.aestronglyMeasurable) (Filter.Eventually.of_forall fun r => ?_)
  simp [Complex.norm_exp, Complex.mul_re]

private theorem boundaryMark_continuous (j : Fin 2) (y N lam u : ℝ) :
    Continuous (sourceComplexBoundaryMark j y N lam u) := by
  have heq : sourceComplexBoundaryMark j y N lam u = fun v =>
      ∫ r : ℝ, (sourceComplexBoundaryAmplitude j y N lam r : ℂ) *
        Complex.exp (-(((u * y * Real.sqrt r + v * r : ℝ) : ℂ) * Complex.I)) := by
    funext v
    exact boundaryMark_eq j y N lam u v
  rw [heq]
  apply continuous_of_dominated (bound := fun r => |sourceComplexBoundaryAmplitude j y N lam r|)
  · intro v
    exact (boundaryMark_phase_integrable j y N lam u v).aestronglyMeasurable
  · intro v
    filter_upwards with r
    simp [Complex.norm_exp, Complex.mul_re]
  · simpa only [Real.norm_eq_abs] using
      ((boundaryAmplitude_smooth j y N lam).continuous.integrable_of_hasCompactSupport
        (boundaryAmplitude_compact j y N lam)).norm
  · filter_upwards with r
    fun_prop

private theorem boundaryMark_genuine_norm_integrability :
    ∀ (y N lam : ℝ), 2 ≤ y → (1 / 16 : ℝ) ≤ N → N ≤ 7 →
      y / Real.sqrt N ≤ lam → ∀ (j : Fin 2) (u : ℝ),
        Integrable (fun v : ℝ => ‖sourceComplexBoundaryMark j y N lam u v‖) ∧
          Integrable (fun v : ℝ => |v| * ‖sourceComplexBoundaryMark j y N lam u v‖) := by
  obtain ⟨C, hC, hb⟩ := actual_amplitude_derivative_envelope
  obtain ⟨Cg, hCg, hglobal⟩ := sourceMarkExponential_norms (1 / 16) 4
    (by norm_num) (by norm_num)
  intro y N lam hy hNlo hNhi hlam j u
  obtain ⟨ht, _, _, _, _⟩ := boundary_setup y N lam hy hNlo hNhi hlam
  let Q : ℝ := 1 + lam * y
  let M : ℝ := C * Q ^ 2
  let a : ℝ → ℝ := sourceComplexBoundaryAmplitude j y N lam
  have hQ : 1 ≤ Q := by dsimp [Q]; linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hd : ∀ k : ℕ, k ≤ 2 → ∀ r : ℝ, |iteratedDeriv k a r| ≤ M := by
    intro k hk r
    have he : Real.exp (-((1 / 256 : ℝ) * |r - N| * Q)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    calc
      _ ≤ C * Q ^ k * Real.exp (-((1 / 256 : ℝ) * |r - N| * Q)) :=
        hb y N lam hy hNlo hNhi hlam j k (by omega) r
      _ ≤ C * Q ^ 2 * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hQ hk) hC.le)
        he (Real.exp_pos _).le (by positivity)
      _ = M := by dsimp [M]; ring
  have hsupport : tsupport a ⊆ Set.Icc (1 / 16 : ℝ) 4 := by
    intro r hr
    have h := sourceKernelCutoff_data.2.2.2.2 (boundaryAmplitude_tsupport j y N lam hr)
    exact ⟨h.1.le, h.2.le⟩
  have hC2 : ∀ r : ℝ, |a r| ≤ M ∧ |deriv a r| ≤ M ∧ |deriv (deriv a) r| ≤ M := by
    intro r
    refine ⟨by simpa only [iteratedDeriv_zero] using hd 0 (by omega) r,
      by simpa only [iteratedDeriv_one] using hd 1 (by omega) r, ?_⟩
    have h := hd 2 (by omega) r
    change |iteratedDeriv (1 + 1) a r| ≤ M at h
    rw [iteratedDeriv_succ, iteratedDeriv_one] at h
    exact h
  have h := hglobal M hM a (boundaryAmplitude_smooth j y N lam) hsupport hC2
    y (-u) (by linarith)
  exact ⟨h.1, h.2.1⟩

private theorem polynomial_exp_absorb (m : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    x ^ m * Real.exp (-x / 256) ≤
      (m.factorial : ℝ) * 512 ^ m * Real.exp (-x / 512) := by
  have hfact : (0 : ℝ) < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hp := Real.pow_div_factorial_le_exp (x / 512) (show 0 ≤ x / 512 by positivity) m
  have h1 := (div_le_iff₀ hfact).mp hp
  rw [div_pow] at h1
  have hpow : x ^ m ≤ (m.factorial : ℝ) * 512 ^ m * Real.exp (x / 512) := by
    have h := (div_le_iff₀ (show (0 : ℝ) < 512 ^ m by positivity)).mp h1
    nlinarith only [h]
  calc
    _ ≤ ((m.factorial : ℝ) * 512 ^ m * Real.exp (x / 512)) * Real.exp (-x / 256) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = ((m.factorial : ℝ) * 512 ^ m) *
        (Real.exp (x / 512) * Real.exp (-x / 256)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 1; congr 1; ring

private theorem actual_amplitude_weighted_envelope :
    ∃ C : ℝ, 0 < C ∧ ∀ (y N lam : ℝ),
      2 ≤ y → (1 / 16 : ℝ) ≤ N → N ≤ 7 → y / Real.sqrt N ≤ lam →
      ∀ (j : Fin 2) (k m : ℕ), k ≤ 32 → m ≤ 2 → ∀ r : ℝ,
        |r - N| ^ m * |iteratedDeriv k (sourceComplexBoundaryAmplitude j y N lam) r| ≤
          C * ((1 + lam * y) ^ k / (1 + lam * y) ^ m) *
            Real.exp (-((|r - N| * (1 + lam * y)) / 512)) := by
  obtain ⟨C, hC, hb⟩ := actual_amplitude_derivative_envelope
  refine ⟨524288 * C, by positivity, ?_⟩
  intro y N lam hy hNlo hNhi hlam j k m hk hm r
  obtain ⟨ht, _, _, _, _⟩ := boundary_setup y N lam hy hNlo hNhi hlam
  let Q : ℝ := 1 + lam * y
  let x : ℝ := |r - N| * Q
  have hQ : 0 < Q := by dsimp [Q]; linarith
  have hx : 0 ≤ x := mul_nonneg (abs_nonneg _) hQ.le
  have hfactor : (m.factorial : ℝ) * 512 ^ m ≤ (524288 : ℝ) := by
    have hf : (m.factorial : ℝ) ≤ ((2 : ℕ).factorial : ℝ) := Nat.cast_le.mpr (Nat.factorial_le hm)
    have hp : (512 : ℝ) ^ m ≤ 512 ^ 2 := pow_le_pow_right₀ (by norm_num) hm
    have h := mul_le_mul hf hp (by positivity) (by positivity)
    norm_num at h ⊢
    exact h
  have hbase : |iteratedDeriv k (sourceComplexBoundaryAmplitude j y N lam) r| ≤
      C * Q ^ k * Real.exp (-x / 256) := by
    have h := hb y N lam hy hNlo hNhi hlam j k hk r
    convert h using 1 <;> dsimp [Q, x] <;> congr 2 <;> ring
  calc
    _ ≤ |r - N| ^ m * (C * Q ^ k * Real.exp (-x / 256)) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = C * (Q ^ k / Q ^ m) * (x ^ m * Real.exp (-x / 256)) := by
      dsimp [x]
      rw [mul_pow]
      field_simp [hQ.ne'] <;> ring
    _ ≤ C * (Q ^ k / Q ^ m) *
        ((m.factorial : ℝ) * 512 ^ m * Real.exp (-x / 512)) :=
      mul_le_mul_of_nonneg_left (polynomial_exp_absorb m x hx) (by positivity)
    _ ≤ C * (Q ^ k / Q ^ m) * (524288 * Real.exp (-x / 512)) := by
      gcongr
    _ = _ := by dsimp [Q, x]; ring

private theorem boundary_product_derivatives (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
    (g : ℝ → ℂ) (hg : ∀ r : ℝ, 0 < r → ContDiffAt ℝ ∞ g r)
    (r : ℝ) (hr : 0 < r) :
    deriv (fun x : ℝ => (a x : ℂ) * g x) r =
        ((deriv a r : ℝ) : ℂ) * g r + (a r : ℂ) * deriv g r ∧
      deriv (deriv (fun x : ℝ => (a x : ℂ) * g x)) r =
        ((deriv (deriv a) r : ℝ) : ℂ) * g r +
          2 * ((deriv a r : ℝ) : ℂ) * deriv g r +
            (a r : ℂ) * deriv (deriv g) r := by
  run_tac
    let n : Lean.Name := .str (.str (.str
      (.num (.str (.str (.str (.str .anonymous "_private") "Shao")
        "Probability") "SourceMarkFourierNorms") 0) "Shao") "Probability")
      "product_derivatives"
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      apply $(Lean.mkIdent n) <;> assumption))

private theorem real_phase_norm_derivatives (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (r : ℝ) :
    let e : ℝ → ℂ := fun x => Complex.exp ((p x : ℂ) * Complex.I)
    ‖e r‖ = 1 ∧ ‖deriv e r‖ = |deriv p r| ∧
      ‖deriv (deriv e) r‖ ≤ |deriv (deriv p) r| + |deriv p r| ^ 2 := by
  let e : ℝ → ℂ := fun x => Complex.exp ((p x : ℂ) * Complex.I)
  have hp' : ContDiff ℝ ∞ (deriv p) := (contDiff_infty_iff_deriv.mp hp).2
  have hd (x : ℝ) : HasDerivAt e (((deriv p x : ℝ) : ℂ) * Complex.I * e x) x := by
    convert ((((hp.differentiable (by simp)).differentiableAt (x := x)).hasDerivAt.ofReal_comp.mul_const
      Complex.I).cexp) using 1 <;> dsimp [e] <;> ring
  have hnorm : ‖e r‖ = 1 := by simp [e, Complex.norm_exp, Complex.mul_re]
  have hd2 : deriv (deriv e) r =
      ((((deriv (deriv p) r : ℝ) : ℂ) * Complex.I) -
        ((deriv p r : ℝ) : ℂ) ^ 2) * e r := by
    have heq : deriv e = fun x => ((deriv p x : ℝ) : ℂ) * Complex.I * e x :=
      funext fun x => (hd x).deriv
    rw [heq]
    have hh := (((((hp'.differentiable (by simp)).differentiableAt (x := r)).hasDerivAt.ofReal_comp.mul_const
      Complex.I).mul (hd r))).deriv
    change deriv (fun x : ℝ => ((deriv p x : ℝ) : ℂ) * Complex.I * e x) r = _ at hh
    rw [hh]
    ring_nf
    simp only [Complex.I_sq]
    ring
  refine ⟨hnorm, ?_, ?_⟩
  · rw [(hd r).deriv]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, hnorm, mul_one]
  · rw [hd2, norm_mul, hnorm, mul_one]
    have hs : ‖((deriv p r : ℝ) : ℂ) ^ 2‖ = |deriv p r| ^ 2 := by
      simp only [pow_two, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (norm_sub_le (((deriv (deriv p) r : ℝ) : ℂ) * Complex.I)
      (((deriv p r : ℝ) : ℂ) ^ 2)).trans
        (add_le_add (by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_I, mul_one, le_refl]) hs.le)

private theorem demodulated_real_phase_bounds (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hgeq : ∀ x : ℝ, (1 / 16 : ℝ) ≤ x → g x = Real.sqrt x)
    (G t N r : ℝ) (hG2 : |deriv (deriv g) r| ≤ G)
    (hNlo : (1 / 16 : ℝ) ≤ N) (hrlo : (1 / 16 : ℝ) < r) :
    let p : ℝ → ℝ := fun x => (t / (2 * Real.sqrt N)) * x + (-t) * g x
    ContDiff ℝ ∞ p ∧ |deriv p r| ≤ 16 * |t| * |r - N| ∧
      |deriv (deriv p) r| ≤ G * |t| := by
  let p : ℝ → ℝ := fun x => (t / (2 * Real.sqrt N)) * x + (-t) * g x
  have hp : ContDiff ℝ ∞ p :=
    (contDiff_const.mul contDiff_id).add (contDiff_const.mul hg)
  have hgp : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
  have hd (x : ℝ) : HasDerivAt p
      (t / (2 * Real.sqrt N) + (-t) * deriv g x) x := by
    convert ((hasDerivAt_id x).const_mul (t / (2 * Real.sqrt N))).add
      ((((hg.differentiable (by simp)).differentiableAt (x := x)).hasDerivAt).const_mul (-t)) using 1 <;>
      (try funext z) <;> (try dsimp [p]) <;> ring
  have hd2 : deriv (deriv p) r = -t * deriv (deriv g) r := by
    have heq : deriv p = fun x => t / (2 * Real.sqrt N) + (-t) * deriv g x :=
      funext fun x => (hd x).deriv
    rw [heq]
    change deriv ((fun _ : ℝ => t / (2 * Real.sqrt N)) + (fun x : ℝ => (-t) * deriv g x)) r = _
    simpa only [zero_add] using
      ((hasDerivAt_const r (t / (2 * Real.sqrt N))).add
        ((((hgp.differentiable (by simp)).differentiableAt (x := r)).hasDerivAt).const_mul (-t))).deriv
  have hr : 0 < r := by linarith
  have hN : 0 < N := by linarith
  have hsn : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hsnlo : (1 / 4 : ℝ) ≤ Real.sqrt N := by
    nlinarith [Real.sq_sqrt hN.le, Real.sqrt_nonneg N]
  have hsrlo : (1 / 4 : ℝ) ≤ Real.sqrt r := by
    nlinarith [Real.sq_sqrt hr.le, Real.sqrt_nonneg r]
  have heqg : g =ᶠ[𝓝 r] Real.sqrt := by
    filter_upwards [lt_mem_nhds hrlo] with x hx
    exact hgeq x hx.le
  have hgd : deriv g r = 1 / (2 * Real.sqrt r) := by
    rw [heqg.deriv_eq]
    convert (Real.hasDerivAt_sqrt hr.ne').deriv using 1 <;> ring
  let D : ℝ := 2 * Real.sqrt N * Real.sqrt r * (Real.sqrt r + Real.sqrt N)
  have hD : 0 < D := by dsimp [D]; positivity
  have hDlo : (1 / 16 : ℝ) ≤ D := by
    dsimp [D]
    calc
      _ = (2 * (1 / 4 : ℝ) * (1 / 4)) * (1 / 4 + 1 / 4) := by norm_num
      _ ≤ _ := by gcongr
  have hinv : 1 / (2 * Real.sqrt N) - 1 / (2 * Real.sqrt r) = (r - N) / D := by
    dsimp [D]
    field_simp
    nlinarith [Real.sq_sqrt hN.le, Real.sq_sqrt hr.le]
  have hdiff : |1 / (2 * Real.sqrt N) - 1 / (2 * Real.sqrt r)| ≤ 16 * |r - N| := by
    rw [hinv, abs_div, abs_of_pos hD]
    apply (div_le_iff₀ hD).mpr
    nlinarith [mul_nonneg (abs_nonneg (r - N)) (show 0 ≤ D - 1 / 16 by linarith)]
  refine ⟨hp, ?_, ?_⟩
  · rw [(hd r).deriv, hgd]
    have he : t / (2 * Real.sqrt N) + -t * (1 / (2 * Real.sqrt r)) =
        t * (1 / (2 * Real.sqrt N) - 1 / (2 * Real.sqrt r)) := by ring
    rw [he, abs_mul]
    have h := mul_le_mul_of_nonneg_left hdiff (abs_nonneg t)
    nlinarith only [h]
  · rw [hd2, abs_mul, abs_neg]
    exact (mul_le_mul_of_nonneg_left hG2 (abs_nonneg t)).trans_eq (mul_comm _ _)

private theorem actual_demodulated_pointwise :
    ∃ D : ℝ, 0 < D ∧ ∀ (y N lam : ℝ),
      2 ≤ y → (1 / 16 : ℝ) ≤ N → N ≤ 7 → y / Real.sqrt N ≤ lam →
      ∀ (j : Fin 2) (u : ℝ),
        let Q : ℝ := 1 + lam * y
        let T : ℝ := y * |u|
        let R : ℝ := Q + T / Q
        let a : ℝ → ℝ := sourceComplexBoundaryAmplitude j y N lam
        let b : ℝ → ℂ := fun r => (a r : ℂ) *
          Complex.exp (((-(u * y) * Real.sqrt r +
            (u * y / (2 * Real.sqrt N)) * r : ℝ) : ℂ) * Complex.I)
        ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
          ∀ r : ℝ,
            ‖b r‖ ≤ D * Real.exp (-((|r - N| * Q) / 512)) ∧
              ‖deriv b r‖ ≤ D * R * Real.exp (-((|r - N| * Q) / 512)) ∧
              ‖deriv (deriv b) r‖ ≤ D * R ^ 2 *
                Real.exp (-((|r - N| * Q) / 512)) := by
  obtain ⟨Cw, hCw, hw⟩ := actual_amplitude_weighted_envelope
  obtain ⟨g, hg, hgeq, G, hG, hGb⟩ := smooth_sqrt_extension
  let H : ℝ := G + 512
  let D : ℝ := H * Cw
  have hH : 512 ≤ H := by dsimp [H]; linarith
  have hD : 0 < D := mul_pos (by linarith : 0 < H) hCw
  have hDC : Cw ≤ D := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ H by linarith) hCw.le
  have hD16 : 16 * Cw ≤ D :=
    mul_le_mul_of_nonneg_right (by linarith : (16 : ℝ) ≤ H) hCw.le
  have hD256 : 256 * Cw ≤ D :=
    mul_le_mul_of_nonneg_right (by linarith : (256 : ℝ) ≤ H) hCw.le
  have hDmid : (32 + G) * Cw ≤ 2 * D := by
    have h := mul_le_mul_of_nonneg_right (show 32 + G ≤ 2 * H by dsimp [H]; linarith) hCw.le
    simpa only [mul_assoc] using h
  refine ⟨D, hD, ?_⟩
  intro y N lam hy hNlo hNhi hlam j u
  dsimp only
  let Q : ℝ := 1 + lam * y
  let T : ℝ := y * |u|
  let R : ℝ := Q + T / Q
  let t : ℝ := u * y
  let a : ℝ → ℝ := sourceComplexBoundaryAmplitude j y N lam
  let b : ℝ → ℂ := fun r => (a r : ℂ) *
    Complex.exp (((-(u * y) * Real.sqrt r +
      (u * y / (2 * Real.sqrt N)) * r : ℝ) : ℂ) * Complex.I)
  let p : ℝ → ℝ := fun r => (t / (2 * Real.sqrt N)) * r + (-t) * g r
  let e : ℝ → ℂ := fun r => Complex.exp ((p r : ℂ) * Complex.I)
  have hpa : ContDiff ℝ ∞ p :=
    (contDiff_const.mul contDiff_id).add (contDiff_const.mul hg)
  have he : ContDiff ℝ ∞ e :=
    ((Complex.ofRealCLM.contDiff.comp hpa).mul contDiff_const).cexp
  have ha : ContDiff ℝ ∞ a := boundaryAmplitude_smooth j y N lam
  have hac : HasCompactSupport a := boundaryAmplitude_compact j y N lam
  have hbeq : b = fun r => (a r : ℂ) * e r := by
    funext r
    by_cases hc : sourceKernelCutoff r = 0
    · simp [b, a, e, sourceComplexBoundaryAmplitude, hc]
    · have hr := sourceKernelCutoff_data.2.2.2.2 (subset_tsupport _ hc)
      have hgr := hgeq r hr.1.le
      dsimp [b, e, p]
      rw [hgr]
      congr 1
      congr 1
      dsimp [t]
      push_cast
      ring
  have hbc : ContDiff ℝ ∞ b := by
    rw [hbeq]
    exact (Complex.ofRealCLM.contDiff.comp ha).mul he
  have hbcompact : HasCompactSupport b := by
    rw [hbeq]
    exact (hac.comp_left (g := Complex.ofReal) rfl).mul_right
  have hbsupp : tsupport b ⊆ tsupport a := by
    apply closure_mono
    intro r hr hzero
    exact hr (by rw [hbeq]; simp [hzero])
  obtain ⟨ht, _, _, _, _⟩ := boundary_setup y N lam hy hNlo hNhi hlam
  have hQ : 0 < Q := by dsimp [Q]; linarith
  have hQ1 : 1 ≤ Q := by dsimp [Q]; linarith
  have hT : 0 ≤ T := mul_nonneg (by linarith) (abs_nonneg u)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have htAbs : |t| = T := by
    dsimp [t, T]
    rw [abs_mul, abs_of_nonneg (show 0 ≤ y by linarith)]
    ring
  change ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ _
  refine ⟨hbc, hbcompact, ?_⟩
  intro r
  let E : ℝ := Real.exp (-((|r - N| * Q) / 512))
  change ‖b r‖ ≤ D * E ∧ ‖deriv b r‖ ≤ D * R * E ∧
    ‖deriv (deriv b) r‖ ≤ D * R ^ 2 * E
  have hE : 0 ≤ E := (Real.exp_pos _).le
  by_cases hr : r ∈ tsupport a
  · have hχr := sourceKernelCutoff_data.2.2.2.2 (boundaryAmplitude_tsupport j y N lam hr)
    have hrpos : 0 < r := by linarith [hχr.1]
    have hg2 : |deriv (deriv g) r| ≤ G := by
      have h := hGb 2 (by omega) r ⟨hχr.1.le, hχr.2.le⟩
      change |iteratedDeriv (1 + 1) g r| ≤ G at h
      rw [iteratedDeriv_succ, iteratedDeriv_one] at h
      exact h
    obtain ⟨_, hp1, hp2⟩ := demodulated_real_phase_bounds g hg hgeq G t N r hg2 hNlo hχr.1
    rw [htAbs] at hp1 hp2
    obtain ⟨he0, he1eq, he2bound⟩ := real_phase_norm_derivatives p hpa r
    change ‖e r‖ = 1 at he0
    have he1 : ‖deriv e r‖ ≤ 16 * T * |r - N| := he1eq.le.trans hp1
    have he2 : ‖deriv (deriv e) r‖ ≤ G * T + 256 * T ^ 2 * |r - N| ^ 2 := by
      have hs := pow_le_pow_left₀ (abs_nonneg (deriv p r)) hp1 2
      nlinarith only [he2bound, hp2, hs]
    obtain ⟨hd1, hd2⟩ := boundary_product_derivatives a ha e (fun _ _ => he.contDiffAt) r hrpos
    have hb0 : ‖b r‖ = |a r| := by
      rw [hbeq]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, he0, mul_one]
    have hb1 : ‖deriv b r‖ ≤ |deriv a r| + 16 * T * (|r - N| * |a r|) := by
      rw [hbeq, hd1]
      have htri := norm_add_le (((deriv a r : ℝ) : ℂ) * e r) ((a r : ℂ) * deriv e r)
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, he0, mul_one] at htri
      have hm := mul_le_mul_of_nonneg_left he1 (abs_nonneg (a r))
      nlinarith only [htri, hm]
    have hb2 : ‖deriv (deriv b) r‖ ≤ |deriv (deriv a) r| +
        32 * T * (|r - N| * |deriv a r|) +
          G * T * |a r| + 256 * T ^ 2 * (|r - N| ^ 2 * |a r|) := by
      rw [hbeq, hd2]
      have htri := (norm_add_le
        (((deriv (deriv a) r : ℝ) : ℂ) * e r + 2 * ((deriv a r : ℝ) : ℂ) * deriv e r)
        ((a r : ℂ) * deriv (deriv e) r)).trans
        (add_le_add (norm_add_le
          (((deriv (deriv a) r : ℝ) : ℂ) * e r)
          (2 * ((deriv a r : ℝ) : ℂ) * deriv e r)) le_rfl)
      simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, he0, mul_one] at htri
      have hm1 := mul_le_mul_of_nonneg_left he1
        (show 0 ≤ 2 * |deriv a r| by positivity)
      have hm2 := mul_le_mul_of_nonneg_left he2 (abs_nonneg (a r))
      nlinarith only [htri, hm1, hm2]
    have hw' (k m : ℕ) (hk : k ≤ 2) (hm : m ≤ 2) :
        |r - N| ^ m * |iteratedDeriv k a r| ≤ Cw * (Q ^ k / Q ^ m) * E :=
      hw y N lam hy hNlo hNhi hlam j k m (by omega) hm r
    have ha00 : |a r| ≤ Cw * E := by
      simpa only [pow_zero, div_one, one_mul, mul_one, iteratedDeriv_zero] using hw' 0 0 (by omega) (by omega)
    have ha10 : |deriv a r| ≤ Cw * Q * E := by
      simpa only [pow_zero, pow_one, div_one, one_mul, iteratedDeriv_one] using hw' 1 0 (by omega) (by omega)
    have ha20 : |deriv (deriv a) r| ≤ Cw * Q ^ 2 * E := by
      simpa only [pow_zero, div_one, one_mul, iteratedDeriv_succ, iteratedDeriv_one,
        iteratedDeriv_zero] using hw' 2 0 (by omega) (by omega)
    have ha01 : |r - N| * |a r| ≤ (Cw / Q) * E := by
      simpa only [pow_zero, pow_one, div_eq_mul_inv, one_mul, iteratedDeriv_zero] using hw' 0 1 (by omega) (by omega)
    have ha11 : |r - N| * |deriv a r| ≤ Cw * E := by
      simpa only [pow_one, div_self hQ.ne', mul_one, iteratedDeriv_one] using hw' 1 1 (by omega) (by omega)
    have ha02 : |r - N| ^ 2 * |a r| ≤ (Cw / Q ^ 2) * E := by
      simpa only [pow_zero, div_eq_mul_inv, one_mul, iteratedDeriv_zero] using hw' 0 2 (by omega) (by omega)
    refine ⟨by rw [hb0]; exact ha00.trans (mul_le_mul_of_nonneg_right hDC hE), ?_, ?_⟩
    · calc
        _ ≤ |deriv a r| + 16 * T * (|r - N| * |a r|) := hb1
        _ ≤ Cw * Q * E + 16 * T * ((Cw / Q) * E) :=
          add_le_add ha10 (mul_le_mul_of_nonneg_left ha01 (by positivity))
        _ = Cw * Q * E + (16 * Cw) * (T / Q) * E := by ring
        _ ≤ D * Q * E + D * (T / Q) * E := by gcongr
        _ = _ := by dsimp [R]; ring
    · calc
        _ ≤ |deriv (deriv a) r| + 32 * T * (|r - N| * |deriv a r|) +
            G * T * |a r| + 256 * T ^ 2 * (|r - N| ^ 2 * |a r|) := hb2
        _ ≤ Cw * Q ^ 2 * E + 32 * T * (Cw * E) +
            G * T * (Cw * E) + 256 * T ^ 2 * ((Cw / Q ^ 2) * E) := by
          gcongr
        _ = Cw * Q ^ 2 * E + ((32 + G) * Cw) * T * E +
            (256 * Cw) * (T ^ 2 / Q ^ 2) * E := by ring
        _ ≤ D * Q ^ 2 * E + (2 * D) * T * E + D * (T ^ 2 / Q ^ 2) * E := by
          gcongr
        _ = _ := by dsimp [R]; field_simp [hQ.ne'] <;> ring
  · have hrb : r ∉ tsupport b := fun h => hr (hbsupp h)
    have hz : b =ᶠ[𝓝 r] (fun _ => (0 : ℂ)) := notMem_tsupport_iff_eventuallyEq.mp hrb
    have hz0 : b r = 0 := hz.eq_of_nhds
    have hz1 : deriv b r = 0 := by rw [hz.deriv_eq]; simp
    have hz2 : deriv (deriv b) r = 0 := by
      have h := hz.iteratedDeriv_eq 2
      change iteratedDeriv (1 + 1) b r = iteratedDeriv (1 + 1) (fun _ : ℝ => (0 : ℂ)) r at h
      simp only [iteratedDeriv_succ, iteratedDeriv_one] at h
      simpa using h
    rw [hz0, hz1, hz2]
    simp only [norm_zero]
    exact ⟨by positivity, by positivity, by positivity⟩

private theorem scalar_square_envelope_budget (f : ℝ → ℂ)
    (hfi : Integrable (fun r : ℝ => ‖f r‖ ^ 2))
    (Q N A : ℝ) (hQ : 0 < Q) (hA : 0 ≤ A)
    (hb : ∀ r : ℝ, ‖f r‖ ≤ A * Real.exp (-((|r - N| * Q) / 512))) :
    (∫ r : ℝ, ‖f r‖ ^ 2) ≤ 512 * A ^ 2 / Q := by
  let F : ℝ → ℝ := fun r => Real.exp (-((|r - N| * Q) / 256))
  have hFeq : F = fun r : ℝ => Real.exp (-(Q / 256) * |r - N|) := by
    funext r
    dsimp [F]
    congr 1
    ring
  obtain ⟨hi, hv⟩ := exp_abs_integral (Q / 256) N (by positivity)
  have hFi : Integrable F := by rw [hFeq]; exact hi
  have hFv : (∫ r : ℝ, F r) = 512 / Q := by
    rw [hFeq, hv]
    field_simp <;> norm_num
  have hpoint : ∀ r : ℝ, ‖f r‖ ^ 2 ≤ A ^ 2 * F r := by
    intro r
    have he : (Real.exp (-((|r - N| * Q) / 512))) ^ 2 = F r := by
      rw [pow_two, ← Real.exp_add]
      dsimp [F]
      congr 1
      ring
    have h := pow_le_pow_left₀ (norm_nonneg (f r)) (hb r) 2
    simpa only [mul_pow, he] using h
  calc
    _ ≤ ∫ r : ℝ, A ^ 2 * F r := integral_mono hfi (hFi.const_mul _) hpoint
    _ = A ^ 2 * (512 / Q) := by rw [integral_const_mul, hFv]
    _ = _ := by ring

private theorem actual_demodulated_schwartz_budget :
    ∃ C : ℝ, 0 < C ∧ ∀ (y N lam : ℝ),
      2 ≤ y → (1 / 16 : ℝ) ≤ N → N ≤ 7 → y / Real.sqrt N ≤ lam →
      ∀ (j : Fin 2) (u : ℝ),
        let Q : ℝ := 1 + lam * y
        let T : ℝ := y * |u|
        let R : ℝ := Q + T / Q
        let a : ℝ → ℝ := sourceComplexBoundaryAmplitude j y N lam
        let bfun : ℝ → ℂ := fun r => (a r : ℂ) *
          Complex.exp (((-(u * y) * Real.sqrt r +
            (u * y / (2 * Real.sqrt N)) * r : ℝ) : ℂ) * Complex.I)
        ∃ b : SchwartzMap ℝ ℂ, (b : ℝ → ℂ) = bfun ∧
          (∫ r : ℝ, ‖b r‖ ^ 2) ≤ (C / Real.sqrt Q) ^ 2 ∧
          (∫ r : ℝ, ‖SchwartzMap.derivCLM ℂ ℂ b r‖ ^ 2) ≤
            ((C / Real.sqrt Q) * R) ^ 2 ∧
          (∫ r : ℝ, ‖SchwartzMap.derivCLM ℂ ℂ
            (SchwartzMap.derivCLM ℂ ℂ b) r‖ ^ 2) ≤
              ((C / Real.sqrt Q) * R ^ 2) ^ 2 := by
  obtain ⟨D, hD, hDb⟩ := actual_demodulated_pointwise
  refine ⟨32 * D, by positivity, ?_⟩
  intro y N lam hy hNlo hNhi hlam j u
  dsimp only
  let Q : ℝ := 1 + lam * y
  let T : ℝ := y * |u|
  let R : ℝ := Q + T / Q
  let a : ℝ → ℝ := sourceComplexBoundaryAmplitude j y N lam
  let bfun : ℝ → ℂ := fun r => (a r : ℂ) *
    Complex.exp (((-(u * y) * Real.sqrt r +
      (u * y / (2 * Real.sqrt N)) * r : ℝ) : ℂ) * Complex.I)
  obtain ⟨hbc, hbcomp, hpoint⟩ := hDb y N lam hy hNlo hNhi hlam j u
  let b : SchwartzMap ℝ ℂ := hbcomp.toSchwartzMap hbc
  let db : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ b
  let ddb : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ db
  have hsq (z : SchwartzMap ℝ ℂ) : Integrable (fun r : ℝ => ‖z r‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm z.continuous.aestronglyMeasurable).mp (z.memLp 2 volume)
  obtain ⟨ht, _, _, _, _⟩ := boundary_setup y N lam hy hNlo hNhi hlam
  have hQ : 0 < Q := by dsimp [Q]; linarith
  have hT : 0 ≤ T := mul_nonneg (by linarith) (abs_nonneg u)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hScale : 512 * D ^ 2 / Q ≤ ((32 * D) / Real.sqrt Q) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hQ.le]
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg D]) hQ.le
  have hScaleAll (S : ℝ) : 512 * (D * S) ^ 2 / Q ≤
      (((32 * D) / Real.sqrt Q) * S) ^ 2 := by
    calc
      _ = (512 * D ^ 2 / Q) * S ^ 2 := by ring
      _ ≤ (((32 * D) / Real.sqrt Q) ^ 2) * S ^ 2 :=
        mul_le_mul_of_nonneg_right hScale (sq_nonneg S)
      _ = _ := by ring

  have h0 := scalar_square_envelope_budget b (hsq b) Q N D hQ hD.le
    (fun r => (hpoint r).1)
  have h1 := scalar_square_envelope_budget db (hsq db) Q N (D * R) hQ (by positivity)
    (fun r => (hpoint r).2.1)
  have h2 := scalar_square_envelope_budget ddb (hsq ddb) Q N (D * R ^ 2) hQ (by positivity)
    (fun r => (hpoint r).2.2)
  refine ⟨b, rfl, h0.trans hScale, h1.trans (hScaleAll R), h2.trans (hScaleAll (R ^ 2))⟩

private theorem boundary_oscillatory_ibp (f q phi : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ (fun r => f r / q r))
    (hq : ∀ r ∈ tsupport f, q r ≠ 0)
    (hphi : Continuous phi) (hphid : ∀ r ∈ tsupport f, HasDerivAt phi (q r) r)
    (v : ℝ) :
    ((v : ℂ) * Complex.I) *
        (∫ r : ℝ, (f r : ℂ) * Complex.exp (((v * phi r : ℝ) : ℂ) * Complex.I)) =
      -(∫ r : ℝ, ((deriv (fun z => f z / q z) r : ℝ) : ℂ) *
        Complex.exp (((v * phi r : ℝ) : ℂ) * Complex.I)) := by
  run_tac
    let n : Lean.Name := .str (.str (.str
      (.num (.str (.str (.str (.str .anonymous "_private") "Shao")
        "Probability") "SourceKernelMarkedOutside") 0) "Shao") "Probability")
      "markedOscillatory_ibp"
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      apply $(Lean.mkIdent n) <;> assumption))

private theorem inverse_slope_family :
    ∃ J : ℝ → ℝ → ℝ, ∃ M : ℝ, 1 ≤ M ∧
      (∀ w : ℝ, ContDiff ℝ ∞ (J w) ∧
        ∀ k : ℕ, k ≤ 32 → ∀ r : ℝ, |iteratedDeriv k (J w) r| ≤ M) ∧
      ∀ w : ℝ, |w| ≤ (1 / 16 : ℝ) → ∀ r ∈ Set.Icc (1 / 16 : ℝ) 4,
        J w r = (1 + w / (2 * Real.sqrt r))⁻¹ := by
  let pw : ContDiffBump (0 : ℝ) := ⟨1 / 16, 1 / 8, by norm_num, by norm_num⟩
  let pr : ContDiffBump (65 / 32 : ℝ) := ⟨63 / 32, 127 / 64, by norm_num, by norm_num⟩
  let H : (ℝ × ℝ) → ℝ := fun p =>
    pw p.1 * pr p.2 / (1 + p.1 / (2 * Real.sqrt p.2))
  have hnum : ContDiff ℝ ∞ (fun p : ℝ × ℝ => pw p.1 * pr p.2) :=
    (pw.contDiff.comp contDiff_fst).mul (pr.contDiff.comp contDiff_snd)
  have hH : ContDiff ℝ ∞ H := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hw : p.1 ∈ tsupport (pw : ℝ → ℝ)
    · by_cases hr : p.2 ∈ tsupport (pr : ℝ → ℝ)
      · have hw' : |p.1| ≤ (1 / 8 : ℝ) := by
          rw [pw.tsupport_eq] at hw
          change dist p.1 (0 : ℝ) ≤ 1 / 8 at hw
          simpa only [Real.dist_eq, sub_zero] using hw
        have hr' : (3 / 64 : ℝ) ≤ p.2 := by
          rw [pr.tsupport_eq] at hr
          change dist p.2 (65 / 32 : ℝ) ≤ 127 / 64 at hr
          rw [Real.dist_eq] at hr
          linarith [(abs_le.mp hr).1]
        have hrpos : 0 < p.2 := by linarith
        have hs : (1 / 8 : ℝ) < Real.sqrt p.2 := by
          nlinarith [Real.sq_sqrt hrpos.le, Real.sqrt_nonneg p.2]
        have hden : 0 < 2 * Real.sqrt p.2 := by linarith
        have hq : 0 < 1 + p.1 / (2 * Real.sqrt p.2) := by
          have heq : 1 + p.1 / (2 * Real.sqrt p.2) =
              (2 * Real.sqrt p.2 + p.1) / (2 * Real.sqrt p.2) := by field_simp <;> ring
          rw [heq]
          exact div_pos (by linarith [(abs_le.mp hw').1]) hden
        have hqd : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ =>
            1 + p.1 / (2 * Real.sqrt p.2)) p :=
          contDiffAt_const.add (contDiffAt_fst.div
            (contDiffAt_const.mul (contDiffAt_snd.sqrt hrpos.ne')) hden.ne')
        exact hnum.contDiffAt.div hqd hq.ne'
      · have he : (fun z : ℝ × ℝ => pr z.2) =ᶠ[𝓝 p] 0 :=
          (notMem_tsupport_iff_eventuallyEq.mp hr).comp_tendsto continuous_snd.continuousAt
        apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ × ℝ => (0 : ℝ)) p).congr_of_eventuallyEq
        filter_upwards [he] with z hz
        simp only [Pi.zero_apply] at hz ⊢
        simp [H, hz]
    · have he : (fun z : ℝ × ℝ => pw z.1) =ᶠ[𝓝 p] 0 :=
        (notMem_tsupport_iff_eventuallyEq.mp hw).comp_tendsto continuous_fst.continuousAt
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ × ℝ => (0 : ℝ)) p).congr_of_eventuallyEq
      filter_upwards [he] with z hz
      simp only [Pi.zero_apply] at hz ⊢
      simp [H, hz]
  have hHc : HasCompactSupport H := by
    apply (pw.hasCompactSupport.prod pr.hasCompactSupport).of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal ?_ ((isClosed_tsupport _).prod (isClosed_tsupport _))
    intro p hp
    have hn : pw p.1 * pr p.2 ≠ 0 := by
      intro hzero
      exact hp (by simp [H, hzero])
    exact ⟨subset_tsupport _ (left_ne_zero_of_mul hn),
      subset_tsupport _ (right_ne_zero_of_mul hn)⟩
  let J : ℝ → ℝ → ℝ := fun w r => H (w, r)
  have hJ : ∀ w : ℝ, ContDiff ℝ ∞ (J w) := fun w =>
    hH.comp (contDiff_const.prodMk contDiff_id)
  have hder (w : ℝ) (k : ℕ) (r : ℝ) :
      iteratedDeriv k (J w) r = iteratedFDeriv ℝ k H (w, r)
        (fun _ : Fin k => ((0, 1) : ℝ × ℝ)) := by
    let L : ℝ →L[ℝ] ℝ × ℝ := (0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)
    let HH : ℝ × ℝ → ℝ := fun p => H ((w, 0) + p)
    have hHH : ContDiff ℝ ∞ HH := hH.comp (contDiff_const.add contDiff_id)
    have heq : HH ∘ L = J w := by funext s; simp [HH, L, J]
    rw [← heq, iteratedDeriv_eq_iteratedFDeriv,
      L.iteratedFDeriv_comp_right hHH r (by simp)]
    simp [HH, L, iteratedFDeriv_comp_add_left]
  obtain ⟨M, hM, hMb⟩ := hHc.exists_bound_iteratedFDeriv hH 32
  refine ⟨J, M + 1, by linarith, ?_, ?_⟩
  · intro w
    refine ⟨hJ w, ?_⟩
    intro k hk r
    rw [hder, ← Real.norm_eq_abs]
    calc
      _ ≤ ‖iteratedFDeriv ℝ k H (w, r)‖ := by
        simpa using (iteratedFDeriv ℝ k H (w, r)).le_opNorm
          (fun _ : Fin k => ((0, 1) : ℝ × ℝ))
      _ ≤ M := hMb k hk (w, r)
      _ ≤ M + 1 := by linarith
  · intro w hw r hr
    have hpw : pw w = 1 := by
      apply pw.one_of_mem_closedBall
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hw
    have hpr : pr r = 1 := by
      apply pr.one_of_mem_closedBall
      change dist r (65 / 32 : ℝ) ≤ 63 / 32
      rw [Real.dist_eq]
      exact abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩
    dsimp [J, H]
    rw [hpw, hpr]
    simp only [one_mul, one_div]

private theorem actual_localized_two_norms :
    ∃ C : ℝ, 0 < C ∧ ∀ (y N lam : ℝ),
      2 ≤ y → (1 / 16 : ℝ) ≤ N → N ≤ 7 → y / Real.sqrt N ≤ lam →
      ∀ (j : Fin 2) (u : ℝ),
        let Q : ℝ := 1 + lam * y
        let T : ℝ := y * |u|
        (∫ v : ℝ, ‖sourceComplexBoundaryMark j y N lam u v‖) ≤
          C * (1 + Real.sqrt T / Q) ∧
        (∫ v : ℝ, |v| * ‖sourceComplexBoundaryMark j y N lam u v‖) ≤
          C * (Q + T) * (1 + Real.sqrt T / Q) := by
  obtain ⟨S, hS, hSb⟩ := actual_demodulated_schwartz_budget
  refine ⟨1024 * S, by positivity, ?_⟩
  intro y N lam hy hNlo hNhi hlam j u
  dsimp only
  let Q : ℝ := 1 + lam * y
  let T : ℝ := y * |u|
  let R : ℝ := Q + T / Q
  let A : ℝ := S / Real.sqrt Q
  let c : ℝ := u * y / (2 * Real.sqrt N)
  let B : ℝ → ℂ := sourceComplexBoundaryMark j y N lam u
  obtain ⟨ht, hsnlo, _, _, _⟩ := boundary_setup y N lam hy hNlo hNhi hlam
  have hQ : 0 < Q := by dsimp [Q]; linarith
  have hQ1 : 1 ≤ Q := by dsimp [Q]; linarith
  have hT : 0 ≤ T := mul_nonneg (by linarith) (abs_nonneg u)
  have hR : 1 ≤ R := by dsimp [R]; have h := div_nonneg hT hQ.le; linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨b, hbeq, hb0, hb1, hb2⟩ := hSb y N lam hy hNlo hNhi hlam j u
  let U : ℝ → ℂ := fun v => ∫ r : ℝ, b r *
    Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I))
  obtain ⟨hi0, hi1, hu0, hu1⟩ := boundary_sobolev b A R hA hR hb0 hb1 hb2
  change Integrable (fun v : ℝ => ‖U v‖) at hi0
  change Integrable (fun v : ℝ => |v| * ‖U v‖) at hi1
  change (∫ v : ℝ, ‖U v‖) ≤ 256 * A * Real.sqrt R at hu0
  change (∫ v : ℝ, |v| * ‖U v‖) ≤ 256 * A * R * Real.sqrt R at hu1
  have hB : B = fun v => U (v + c) := by
    funext v
    change sourceComplexBoundaryMark j y N lam u v = _
    rw [boundaryMark_eq]
    dsimp [U]
    rw [hbeq]
    apply integral_congr_ae
    filter_upwards with r
    symm
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    dsimp [c]
    push_cast
    ring
  have hI0 : (∫ v : ℝ, ‖B v‖) = ∫ v : ℝ, ‖U v‖ := by
    rw [hB]
    exact integral_add_right_eq_self (fun v : ℝ => ‖U v‖) c
  have hShift0 : Integrable (fun v : ℝ => ‖U (v + c)‖) := hi0.comp_add_right c
  have hShift1 : Integrable (fun v : ℝ => |v + c| * ‖U (v + c)‖) := hi1.comp_add_right c
  have hWenv : Integrable (fun v : ℝ =>
      |v + c| * ‖U (v + c)‖ + |c| * ‖U (v + c)‖) :=
    hShift1.add (hShift0.const_mul _)
  have hBasic := boundaryMark_genuine_norm_integrability y N lam hy hNlo hNhi hlam j u
  have hW : (∫ v : ℝ, |v| * ‖B v‖) ≤
      (∫ v : ℝ, |v| * ‖U v‖) + |c| * (∫ v : ℝ, ‖U v‖) := by
    calc
      _ ≤ ∫ v : ℝ, (|v + c| * ‖U (v + c)‖ + |c| * ‖U (v + c)‖) := by
        apply integral_mono hBasic.2 hWenv
        intro v
        change |v| * ‖B v‖ ≤ |v + c| * ‖U (v + c)‖ + |c| * ‖U (v + c)‖
        rw [hB]
        have hv : |v| ≤ |v + c| + |c| := by
          calc
            _ = |(v + c) + (-c)| := by congr 1; ring
            _ ≤ |v + c| + |-c| := abs_add_le _ _
            _ = _ := by rw [abs_neg]
        have h := mul_le_mul_of_nonneg_right hv (norm_nonneg (U (v + c)))
        nlinarith only [h]
      _ = _ := by
        rw [integral_add hShift1 (hShift0.const_mul _), integral_const_mul,
          integral_add_right_eq_self (fun v : ℝ => |v| * ‖U v‖) c,
          integral_add_right_eq_self (fun v : ℝ => ‖U v‖) c]
  have htAbs : |u * y| = T := by
    dsimp [T]
    rw [abs_mul, abs_of_nonneg (show 0 ≤ y by linarith)]
    ring
  have hc : |c| ≤ 2 * T := by
    have hsn : 0 < Real.sqrt N := by linarith only [hsnlo]
    dsimp [c]
    rw [abs_div, abs_of_pos (show 0 < 2 * Real.sqrt N by positivity), htAbs]
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt N)).mpr
    nlinarith only [mul_nonneg hT (show 0 ≤ Real.sqrt N - 1 / 4 by linarith only [hsnlo])]
  have hRootRatio : Real.sqrt R / Real.sqrt Q = Real.sqrt (1 + T / Q ^ 2) := by
    rw [← Real.sqrt_div (le_trans zero_le_one hR) Q]
    congr 1
    dsimp [R]
    field_simp [hQ.ne'] <;> ring
  have hRootT : Real.sqrt (T / Q ^ 2) = Real.sqrt T / Q := by
    rw [Real.sqrt_div hT (Q ^ 2), Real.sqrt_sq_eq_abs, abs_of_pos hQ]
  have hAdd : Real.sqrt (1 + T / Q ^ 2) ≤ 1 + Real.sqrt (T / Q ^ 2) := by
    have hTp : 0 ≤ T / Q ^ 2 := by positivity
    have hs := Real.sq_sqrt hTp
    have hn := Real.sqrt_nonneg (T / Q ^ 2)
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith only [hs, hn]⟩
  have hAS : A * Real.sqrt R ≤ S * (1 + Real.sqrt T / Q) := by
    calc
      _ = S * (Real.sqrt R / Real.sqrt Q) := by dsimp [A]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by rw [hRootRatio]; simpa only [hRootT] using hAdd) hS.le
  have hRQ : R ≤ Q + T := by
    dsimp [R]
    apply add_le_add le_rfl
    apply (div_le_iff₀ hQ).mpr
    nlinarith only [mul_nonneg hT (show 0 ≤ Q - 1 by linarith only [hQ1])]
  have hu0' : (∫ v : ℝ, ‖U v‖) ≤ 256 * S * (1 + Real.sqrt T / Q) := by
    exact hu0.trans (by nlinarith only [mul_le_mul_of_nonneg_left hAS (by norm_num : (0 : ℝ) ≤ 256)])
  have hu1' : (∫ v : ℝ, |v| * ‖U v‖) ≤ 256 * S * (1 + Real.sqrt T / Q) * R := by
    have h := mul_le_mul_of_nonneg_right hAS (show 0 ≤ 256 * R by positivity)
    nlinarith only [hu1, h]
  have hH : 0 ≤ 1 + Real.sqrt T / Q := by positivity
  change (∫ v : ℝ, ‖B v‖) ≤ (1024 * S) * (1 + Real.sqrt T / Q) ∧
    (∫ v : ℝ, |v| * ‖B v‖) ≤ (1024 * S) * (Q + T) * (1 + Real.sqrt T / Q)
  constructor
  · rw [hI0]
    exact hu0'.trans (mul_le_mul_of_nonneg_right (by nlinarith only [hS] : 256 * S ≤ 1024 * S) hH)
  · calc
      _ ≤ (∫ v : ℝ, |v| * ‖U v‖) + |c| * (∫ v : ℝ, ‖U v‖) := hW
      _ ≤ 256 * S * (1 + Real.sqrt T / Q) * R +
          (2 * T) * (256 * S * (1 + Real.sqrt T / Q)) := by
        exact add_le_add hu1' (mul_le_mul hc hu0' (integral_nonneg (fun v => norm_nonneg (U v))) (by positivity))
      _ = (256 * S * (1 + Real.sqrt T / Q)) * (R + 2 * T) := by ring
      _ ≤ (256 * S * (1 + Real.sqrt T / Q)) * (4 * (Q + T)) := by
        exact mul_le_mul_of_nonneg_left (by linarith only [hRQ, hQ.le, hT]) (by positivity)
      _ = _ := by ring

private theorem compact_iterated_derivative_data (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k f) ∧ HasCompactSupport (iteratedDeriv k f) ∧
      Integrable (iteratedDeriv k f) := by
  induction k with
  | zero =>
    simpa only [iteratedDeriv_zero] using
      And.intro hf (And.intro hc (hf.continuous.integrable_of_hasCompactSupport hc))
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hd : ContDiff ℝ ∞ (deriv (iteratedDeriv k f)) := (contDiff_infty_iff_deriv.mp ih.1).2
    have hdc : HasCompactSupport (deriv (iteratedDeriv k f)) := ih.2.1.deriv
    exact ⟨hd, hdc, hd.continuous.integrable_of_hasCompactSupport hdc⟩

private theorem localized_ibp_recursion (J : ℝ → ℝ) (hJ : ContDiff ℝ ∞ J)
    (M : ℝ) (hM : 1 ≤ M)
    (hMb : ∀ k : ℕ, k ≤ 32 → ∀ r : ℝ, |iteratedDeriv k J r| ≤ M)
    (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (A Q : ℝ) (hA : 0 ≤ A) (hQ : 1 ≤ Q)
    (haL1 : ∀ j : ℕ, j ≤ 32 → Integrable (iteratedDeriv j a) ∧
      (∫ r : ℝ, |iteratedDeriv j a r|) ≤ A * Q ^ j / Q) :
    ∃ F : ℕ → ℝ → ℝ, F 0 = a ∧
      (∀ m : ℕ, F (m + 1) = deriv (fun r => F m r * J r)) ∧
      (∀ m : ℕ, ContDiff ℝ ∞ (F m) ∧ HasCompactSupport (F m) ∧
        tsupport (F m) ⊆ tsupport a) ∧
      ∀ m : ℕ, m ≤ 32 → ∀ j : ℕ, m + j ≤ 32 →
        Integrable (iteratedDeriv j (F m)) ∧
          (∫ r : ℝ, |iteratedDeriv j (F m) r|) ≤
            A * (M * 2 ^ 32) ^ m * Q ^ (m + j) / Q := by
  let F : ℕ → ℝ → ℝ := Nat.rec a (fun _ f => deriv (fun r => f r * J r))
  have hF0 : F 0 = a := rfl
  have hFs (m : ℕ) : F (m + 1) = deriv (fun r => F m r * J r) := rfl
  have hreg : ∀ m : ℕ, ContDiff ℝ ∞ (F m) ∧ HasCompactSupport (F m) ∧
      tsupport (F m) ⊆ tsupport a := by
    intro m
    induction m with
    | zero => exact ⟨ha, hac, Set.Subset.rfl⟩
    | succ m ih =>
      rw [hFs]
      have hd : ContDiff ℝ ∞ (fun r => F m r * J r) := ih.1.mul hJ
      have hdc : HasCompactSupport (fun r => F m r * J r) := ih.2.1.mul_right
      have hs : tsupport (fun r => F m r * J r) ⊆ tsupport (F m) := by
        apply closure_mono
        intro r hr hzero
        exact hr (by simp [hzero])
      exact ⟨(contDiff_infty_iff_deriv.mp hd).2, hdc.deriv,
        tsupport_deriv_subset.trans (hs.trans ih.2.2)⟩
  refine ⟨F, hF0, hFs, hreg, ?_⟩
  let L : ℝ := M * 2 ^ 32
  have hM0 : 0 ≤ M := by linarith
  have hQ0 : 0 < Q := by linarith
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  intro m
  induction m with
  | zero =>
    intro hm j hj
    simpa only [hF0, pow_zero, zero_add, mul_one] using
      haL1 j (by simpa only [zero_add] using hj)
  | succ m ih =>
    intro hm j hj
    have hm0 : m ≤ 32 := by omega
    let n : ℕ := j + 1
    have hn : n ≤ 32 := by dsimp [n]; omega
    have hDi (i : ℕ) : Integrable (iteratedDeriv i (F m)) :=
      (compact_iterated_derivative_data (F m) (hreg m).1 (hreg m).2.1 i).2.2
    have hparts (i : ℕ) (_hi : i ∈ Finset.range (n + 1)) :
        Integrable (fun r : ℝ => (n.choose i : ℝ) * M * |iteratedDeriv i (F m) r|) :=
      (hDi i).abs.const_mul _
    let W : ℝ → ℝ := fun r => ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * M * |iteratedDeriv i (F m) r|
    have hWi : Integrable W := integrable_finsetSum (Finset.range (n + 1)) hparts
    have hformula (r : ℝ) : iteratedDeriv j (F (m + 1)) r =
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * iteratedDeriv i (F m) r * iteratedDeriv (n - i) J r := by
      rw [hFs]
      change iteratedDeriv j (deriv (F m * J)) r = _
      rw [← iteratedDeriv_succ']
      exact iteratedDeriv_mul ((hreg m).1.contDiffAt.of_le (by simp))
        (hJ.contDiffAt.of_le (by simp))
    have hpoint (r : ℝ) : |iteratedDeriv j (F (m + 1)) r| ≤ W r := by
      rw [hformula]
      calc
        _ ≤ ∑ i ∈ Finset.range (n + 1),
            |(n.choose i : ℝ) * iteratedDeriv i (F m) r * iteratedDeriv (n - i) J r| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro i hi
          have hb := hMb (n - i) (by omega) r
          simp only [abs_mul,
            abs_of_nonneg (Nat.cast_nonneg (n.choose i) : (0 : ℝ) ≤ (n.choose i : ℝ))]
          have h := mul_le_mul_of_nonneg_left hb
            (show 0 ≤ (n.choose i : ℝ) * |iteratedDeriv i (F m) r| by positivity)
          nlinarith only [h]
    have hcur : Integrable (iteratedDeriv j (F (m + 1))) :=
      (compact_iterated_derivative_data (F (m + 1)) (hreg (m + 1)).1 (hreg (m + 1)).2.1 j).2.2
    refine ⟨hcur, ?_⟩
    have hWval : (∫ r : ℝ, W r) = ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * M * (∫ r : ℝ, |iteratedDeriv i (F m) r|) := by
      dsimp [W]
      rw [integral_finsetSum (Finset.range (n + 1)) hparts]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_const_mul _ _
    have hterm (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
        (n.choose i : ℝ) * M * (∫ r : ℝ, |iteratedDeriv i (F m) r|) ≤
          (n.choose i : ℝ) * M * (A * L ^ m * Q ^ (m + n) / Q) := by
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hmi : m + i ≤ 32 := by dsimp [n] at hin; omega
      have hp : Q ^ (m + i) ≤ Q ^ (m + n) := pow_le_pow_right₀ hQ (by omega)
      have hscale : A * L ^ m * Q ^ (m + i) / Q ≤ A * L ^ m * Q ^ (m + n) / Q :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) hQ0.le
      exact mul_le_mul_of_nonneg_left ((ih hm0 i hmi).2.trans hscale) (by positivity)
    calc
      _ ≤ ∫ r : ℝ, W r := integral_mono hcur.abs hWi hpoint
      _ = _ := hWval
      _ ≤ ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * M * (A * L ^ m * Q ^ (m + n) / Q) :=
        Finset.sum_le_sum hterm
      _ = (2 : ℝ) ^ n * M * (A * L ^ m * Q ^ (m + n) / Q) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum,
          Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ (2 : ℝ) ^ 32 * M * (A * L ^ m * Q ^ (m + n) / Q) := by
        gcongr <;> norm_num
      _ = _ := by
        change (2 : ℝ) ^ 32 * M * (A * L ^ m * Q ^ (m + n) / Q) =
          A * L ^ (m + 1) * Q ^ ((m + 1) + j) / Q
        have hindex : m + n = (m + 1) + j := by dsimp [n]; omega
        rw [pow_succ L m, hindex]
        dsimp [L]
        ring
private theorem actual_nonstationary_power_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (y N lam : ℝ),
      2 ≤ y → (1 / 16 : ℝ) ≤ N → N ≤ 7 → y / Real.sqrt N ≤ lam →
      ∀ (j : Fin 2) (u v : ℝ), v ≠ 0 → |u * y / v| ≤ (1 / 16 : ℝ) →
        |v| ^ 32 * ‖sourceComplexBoundaryMark j y N lam u v‖ ≤
          C * (1 + lam * y) ^ 31 := by
  obtain ⟨A, hA, hAb⟩ := sourceComplexBoundaryAmplitude_localized
  obtain ⟨J, M, hM, hJ, hJvalue⟩ := inverse_slope_family
  let L : ℝ := M * 2 ^ 32
  let C : ℝ := A * L ^ 32
  have hL : 0 < L := by dsimp [L]; positivity
  have hC : 0 < C := mul_pos hA (pow_pos hL _)
  refine ⟨C, hC, ?_⟩
  intro y N lam hy hNlo hNhi hlam j u v hv hcone
  let Q : ℝ := 1 + lam * y
  let w : ℝ := u * y / v
  let a : ℝ → ℝ := sourceComplexBoundaryAmplitude j y N lam
  let q : ℝ → ℝ := fun r => 1 + w / (2 * Real.sqrt r)
  let phi : ℝ → ℝ := fun r => r + w * Real.sqrt r
  let B : ℂ := sourceComplexBoundaryMark j y N lam u v
  obtain ⟨ht, _, _, _, _⟩ := boundary_setup y N lam hy hNlo hNhi hlam
  have hQ : 1 ≤ Q := by dsimp [Q]; linarith
  have hQpos : 0 < Q := by linarith
  obtain ⟨hDpos, hDle, hrec, hAmp⟩ := hAb y N lam hy hNlo hNhi hlam
  obtain ⟨ha, hac, hapos, hasupp, haJet⟩ := hAmp j
  have haL1 (k : ℕ) (hk : k ≤ 32) : Integrable (iteratedDeriv k a) ∧
      (∫ r : ℝ, |iteratedDeriv k a r|) ≤ A * Q ^ k / Q := by
    refine ⟨(haJet k hk).1, (haJet k hk).2.2.trans_eq ?_⟩
    change A * Q⁻¹ / (Q⁻¹) ^ k = A * Q ^ k / Q
    rw [inv_pow, div_inv_eq_mul]
    ring
  obtain ⟨F, hF0, hFs, hreg, hFbudget⟩ := localized_ibp_recursion (J w) (hJ w).1
    M hM (hJ w).2 a ha hac A Q hA.le hQ haL1
  have hq (r : ℝ) (hr : r ∈ tsupport a) : q r ≠ 0 := by
    have hχr := sourceKernelCutoff_data.2.2.2.2 (hasupp hr).1
    have hrpos : 0 < r := by linarith [hχr.1]
    have hs : (1 / 4 : ℝ) ≤ Real.sqrt r := by
      nlinarith only [Real.sq_sqrt hrpos.le, Real.sqrt_nonneg r, hχr.1]
    have hden : 0 < 2 * Real.sqrt r := by linarith
    have hn : 0 < 2 * Real.sqrt r + w := by linarith [(abs_le.mp hcone).1]
    have heq : q r = (2 * Real.sqrt r + w) / (2 * Real.sqrt r) := by
      dsimp [q]
      field_simp <;> ring
    rw [heq]
    exact (div_pos hn hden).ne'
  have hphi : Continuous phi := by dsimp [phi]; fun_prop
  have hphid (r : ℝ) (hr : r ∈ tsupport a) : HasDerivAt phi (q r) r := by
    have hχr := sourceKernelCutoff_data.2.2.2.2 (hasupp hr).1
    have hrpos : 0 < r := by linarith [hχr.1]
    convert (hasDerivAt_id r).add ((Real.hasDerivAt_sqrt hrpos.ne').const_mul w) using 1 <;>
      (try funext z) <;> (try dsimp [phi, q]) <;> ring
  have hquot (m : ℕ) : (fun r => F m r / q r) = fun r => F m r * J w r := by
    funext r
    by_cases hr : r ∈ tsupport (F m)
    · have hχr := sourceKernelCutoff_data.2.2.2.2 (hasupp ((hreg m).2.2 hr)).1
      rw [hJvalue w hcone r ⟨hχr.1.le, hχr.2.le⟩]
      exact div_eq_mul_inv _ _
    · simp only [image_eq_zero_of_notMem_tsupport hr, zero_div, zero_mul]
  have hquotSmooth (m : ℕ) : ContDiff ℝ ∞ (fun r => F m r / q r) := by
    rw [hquot]
    exact (hreg m).1.mul (hJ w).1
  let I : ℕ → ℂ := fun m => ∫ r : ℝ, (F m r : ℂ) *
    Complex.exp ((((-v) * phi r : ℝ) : ℂ) * Complex.I)
  have hI0 : I 0 = B := by
    dsimp [I, B]
    rw [hF0, boundaryMark_eq]
    apply integral_congr_ae
    filter_upwards with r
    congr 1
    congr 1
    dsimp [phi, w]
    push_cast
    field_simp [hv, Complex.ofReal_ne_zero.mpr hv] <;> ring
  have hstep (m : ℕ) : |v| * ‖I m‖ = ‖I (m + 1)‖ := by
    have h := boundary_oscillatory_ibp (F m) q phi (hreg m).1 (hreg m).2.1
      (hquotSmooth m) (fun r hr => hq r ((hreg m).2.2 hr)) hphi
      (fun r hr => hphid r ((hreg m).2.2 hr)) (-v)
    have hd : deriv (fun r => F m r / q r) = F (m + 1) := by
      rw [hquot, ← hFs m]
    rw [hd] at h
    have hn := congrArg norm h
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one, norm_neg, abs_neg] using hn
  have hPower (m : ℕ) : |v| ^ m * ‖B‖ = ‖I m‖ := by
    induction m with
    | zero => simp only [pow_zero, one_mul, hI0]
    | succ m ih =>
      calc
        _ = |v| * (|v| ^ m * ‖B‖) := by rw [pow_succ]; ring
        _ = |v| * ‖I m‖ := by rw [ih]
        _ = _ := hstep m
  change |v| ^ 32 * ‖B‖ ≤ C * Q ^ 31
  calc
    _ = ‖I 32‖ := hPower 32
    _ ≤ ∫ r : ℝ, ‖(F 32 r : ℂ) *
        Complex.exp ((((-v) * phi r : ℝ) : ℂ) * Complex.I)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ r : ℝ, |F 32 r| := by
      apply integral_congr_ae
      filter_upwards with r
      simp [Complex.norm_exp, Complex.mul_re]
    _ ≤ A * (M * 2 ^ 32) ^ 32 * Q ^ (32 + 0) / Q := by
      simpa only [iteratedDeriv_zero] using (hFbudget 32 (by omega) 0 (by omega)).2
    _ = C * Q ^ 31 := by
      change A * L ^ 32 * Q ^ 32 / Q = (A * L ^ 32) * Q ^ 31
      rw [show (32 : ℕ) = 31 + 1 by rfl, pow_succ Q 31]
      field_simp [hQpos.ne'] <;> ring

private theorem actual_mark_uniform_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ (y N lam : ℝ),
      2 ≤ y → (1 / 16 : ℝ) ≤ N → N ≤ 7 → y / Real.sqrt N ≤ lam →
      ∀ (j : Fin 2) (u v : ℝ),
        ‖sourceComplexBoundaryMark j y N lam u v‖ ≤ A / (1 + lam * y) := by
  obtain ⟨A, hA, hAb⟩ := sourceComplexBoundaryAmplitude_localized
  refine ⟨A, hA, ?_⟩
  intro y N lam hy hNlo hNhi hlam j u v
  obtain ⟨_, _, _, hAmp⟩ := hAb y N lam hy hNlo hNhi hlam
  obtain ⟨_, _, _, _, hJet⟩ := hAmp j
  rw [boundaryMark_eq]
  calc
    _ ≤ ∫ r : ℝ, ‖(sourceComplexBoundaryAmplitude j y N lam r : ℂ) *
        Complex.exp (-(((u * y * Real.sqrt r + v * r : ℝ) : ℂ) * Complex.I))‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ r : ℝ, |sourceComplexBoundaryAmplitude j y N lam r| := by
      apply integral_congr_ae
      filter_upwards with r
      simp [Complex.norm_exp, Complex.mul_re]
    _ ≤ A * (1 + lam * y)⁻¹ := by
      simpa only [iteratedDeriv_zero, pow_zero, div_one] using (hJet 0 (by omega)).2.2
    _ = _ := (div_eq_mul_inv _ _).symm

private theorem actual_nonstationary_profile :
    ∃ C : ℝ, 0 < C ∧ ∀ (y N lam : ℝ),
      2 ≤ y → (1 / 16 : ℝ) ≤ N → N ≤ 7 → y / Real.sqrt N ≤ lam →
      ∀ (j : Fin 2) (u v : ℝ), |u * y / v| ≤ (1 / 16 : ℝ) →
        (1 + |v| / (1 + lam * y)) ^ 32 *
          ‖sourceComplexBoundaryMark j y N lam u v‖ ≤ C / (1 + lam * y) := by
  obtain ⟨A, hA, hLow⟩ := actual_mark_uniform_bound
  obtain ⟨P, hP, hPower⟩ := actual_nonstationary_power_bound
  let C : ℝ := 2 ^ 32 * max A P
  have hC : 0 < C := mul_pos (by positivity)
    (lt_of_lt_of_le hA (le_max_left A P))
  refine ⟨C, hC, ?_⟩
  intro y N lam hy hNlo hNhi hlam j u v hcone
  let Q : ℝ := 1 + lam * y
  let B : ℂ := sourceComplexBoundaryMark j y N lam u v
  obtain ⟨ht, _, _, _, _⟩ := boundary_setup y N lam hy hNlo hNhi hlam
  have hQ : 0 < Q := by dsimp [Q]; linarith
  have hLow' : ‖B‖ ≤ A / Q := hLow y N lam hy hNlo hNhi hlam j u v
  change (1 + |v| / Q) ^ 32 * ‖B‖ ≤ C / Q
  by_cases h : |v| ≤ Q
  · have hratio : |v| / Q ≤ 1 := (div_le_one hQ).mpr h
    have hpow : (1 + |v| / Q) ^ 32 ≤ (2 : ℝ) ^ 32 :=
      pow_le_pow_left₀ (by positivity) (by linarith only [hratio]) 32
    calc
      _ ≤ (2 : ℝ) ^ 32 * (A / Q) :=
        mul_le_mul hpow hLow' (norm_nonneg B) (by positivity)
      _ ≤ (2 : ℝ) ^ 32 * (max A P / Q) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (le_max_left A P) hQ.le) (by positivity)
      _ = C / Q := by dsimp [C]; ring
  · have hv : v ≠ 0 := by intro hz; subst v; simp only [abs_zero] at h; linarith only [hQ, h]
    have hratio : 1 ≤ |v| / Q := (le_div_iff₀ hQ).mpr (by linarith)
    have hpow : (1 + |v| / Q) ^ 32 ≤ (2 * (|v| / Q)) ^ 32 :=
      pow_le_pow_left₀ (by positivity) (by linarith only [hratio]) 32
    have hp : |v| ^ 32 * ‖B‖ ≤ P * Q ^ 31 :=
      hPower y N lam hy hNlo hNhi hlam j u v hv hcone
    calc
      _ ≤ (2 * (|v| / Q)) ^ 32 * ‖B‖ := mul_le_mul_of_nonneg_right hpow (norm_nonneg B)
      _ = ((2 : ℝ) ^ 32 / Q ^ 32) * (|v| ^ 32 * ‖B‖) := by rw [mul_pow, div_pow]; ring
      _ ≤ ((2 : ℝ) ^ 32 / Q ^ 32) * (P * Q ^ 31) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (2 : ℝ) ^ 32 * P / Q := by
        rw [show (32 : ℕ) = 31 + 1 by rfl, pow_succ Q 31]
        field_simp [hQ.ne'] <;> ring
      _ ≤ C / Q := by
        apply div_le_div_of_nonneg_right _ hQ.le
        exact mul_le_mul_of_nonneg_left (le_max_right A P) (by positivity)

private theorem outside_profile_compare (F : ℝ → ℝ) (hF : Continuous F)
    (hF0 : ∀ v : ℝ, 0 ≤ F v) (L D : ℝ) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hb : ∀ v : ℝ, L < |v| → (1 + |v|) ^ 32 * F v ≤ D) :
    IntegrableOn F {v : ℝ | L < |v|} ∧
      (∫ v in {v : ℝ | L < |v|}, F v) ≤ 2 * D / (1 + L) ^ 31 := by
  have hfull : IntegrableOn F {v : ℝ | L < |v|} ∧
      IntegrableOn (fun v => |v| * F v) {v : ℝ | L < |v|} ∧
      (∫ v in {v : ℝ | L < |v|}, F v) ≤ 2 * D / (1 + L) ^ 31 ∧
      (∫ v in {v : ℝ | L < |v|}, |v| * F v) ≤ 2 * D / (1 + L) ^ 30 := by
    run_tac
      let n : Lean.Name := .str (.str (.str
        (.num (.str (.str (.str (.str .anonymous "_private") "Shao")
          "Probability") "SourceKernelMarkedOutside") 0) "Shao") "Probability")
        "outsideProfile_moments_compare"
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        apply $(Lean.mkIdent n) <;> assumption))
  exact ⟨hfull.1, hfull.2.2.1⟩

private theorem scaled_outside_integral (F : ℝ → ℝ) (Q L : ℝ) (hQ : 0 < Q) :
    (∫ z in {z : ℝ | L / Q < |z|}, Q * F (Q * z)) =
      ∫ v in {v : ℝ | L < |v|}, F v := by
  let A : Set ℝ := {v : ℝ | L < |v|}
  let Z : Set ℝ := {z : ℝ | L / Q < |z|}
  have hA : MeasurableSet A := (isOpen_lt continuous_const continuous_abs).measurableSet
  have hZ : MeasurableSet Z := (isOpen_lt continuous_const continuous_abs).measurableSet
  have hmem (z : ℝ) : Q * z ∈ A ↔ z ∈ Z := by
    dsimp [A, Z]
    rw [abs_mul, abs_of_pos hQ, div_lt_iff₀ hQ]
    constructor <;> intro h <;> nlinarith only [h]
  have hind : Z.indicator (fun z => Q * F (Q * z)) =
      fun z => Q * A.indicator F (Q * z) := by
    funext z
    by_cases hz : z ∈ Z
    · simp only [Set.indicator_of_mem hz, Set.indicator_of_mem ((hmem z).mpr hz)]
    · have ha : Q * z ∉ A := fun h => hz ((hmem z).mp h)
      simp only [Set.indicator_of_notMem hz, Set.indicator_of_notMem ha, mul_zero]
  change (∫ z in Z, Q * F (Q * z)) = ∫ v in A, F v
  rw [← integral_indicator hZ, ← integral_indicator hA, hind, integral_const_mul,
    Measure.integral_comp_mul_left (A.indicator F) Q]
  simp only [smul_eq_mul]
  change Q * (|Q⁻¹| * (∫ y : ℝ, A.indicator F y)) = ∫ y : ℝ, A.indicator F y
  rw [abs_inv, abs_of_pos hQ, ← mul_assoc, mul_inv_cancel₀ hQ.ne', one_mul]

private theorem actual_localized_outside_norms :
    ∃ C : ℝ, 0 < C ∧ ∀ (y N lam : ℝ),
      2 ≤ y → (1 / 16 : ℝ) ≤ N → N ≤ 7 → y / Real.sqrt N ≤ lam →
      ∀ (j : Fin 2) (u aStar : ℝ), 0 < aStar → aStar * y ≤ (1 / 16 : ℝ) →
        let Q : ℝ := 1 + lam * y
        let L : ℝ := |u| / aStar
        IntegrableOn (fun v : ℝ => ‖sourceComplexBoundaryMark j y N lam u v‖)
          {v : ℝ | L < |v|} ∧
          (∫ v in {v : ℝ | L < |v|}, ‖sourceComplexBoundaryMark j y N lam u v‖) ≤
            C / (1 + L / Q) ^ 31 := by
  obtain ⟨P, hP, hPb⟩ := actual_nonstationary_profile
  refine ⟨2 * P, by positivity, ?_⟩
  intro y N lam hy hNlo hNhi hlam j u aStar haStar hsmall
  dsimp only
  let Q : ℝ := 1 + lam * y
  let L : ℝ := |u| / aStar
  let F : ℝ → ℝ := fun v => ‖sourceComplexBoundaryMark j y N lam u v‖
  let G : ℝ → ℝ := fun z => Q * F (Q * z)
  obtain ⟨ht, _, _, _, _⟩ := boundary_setup y N lam hy hNlo hNhi hlam
  have hQ : 0 < Q := by dsimp [Q]; linarith only [ht]
  have hL : 0 ≤ L := div_nonneg (abs_nonneg u) haStar.le
  have hy0 : 0 ≤ y := by linarith only [hy]
  have hF : Continuous F := (boundaryMark_continuous j y N lam u).norm
  have hG : Continuous G := continuous_const.mul (hF.comp (continuous_const.mul continuous_id))
  have hG0 (z : ℝ) : 0 ≤ G z := mul_nonneg hQ.le (norm_nonneg _)
  have hprof (z : ℝ) (hz : L / Q < |z|) : (1 + |z|) ^ 32 * G z ≤ P := by
    have hv : L < |Q * z| := by
      rw [abs_mul, abs_of_pos hQ]
      have h := (div_lt_iff₀ hQ).mp hz
      nlinarith only [h]
    have hv0 : 0 < |Q * z| := lt_of_le_of_lt hL hv
    have hu : |u| < |Q * z| * aStar := (div_lt_iff₀ haStar).mp hv
    have hratio : |u| / |Q * z| ≤ aStar :=
      (div_le_iff₀ hv0).mpr (by nlinarith only [hu])
    have hcone : |u * y / (Q * z)| ≤ (1 / 16 : ℝ) := by
      calc
        _ = (|u| / |Q * z|) * y := by rw [abs_div, abs_mul, abs_of_nonneg hy0]; ring
        _ ≤ aStar * y := mul_le_mul_of_nonneg_right hratio hy0
        _ ≤ _ := hsmall
    have hb := hPb y N lam hy hNlo hNhi hlam j u (Q * z) hcone
    change (1 + |Q * z| / Q) ^ 32 * F (Q * z) ≤ P / Q at hb
    have hratioEq : |Q * z| / Q = |z| := by
      rw [abs_mul, abs_of_pos hQ]
      field_simp [hQ.ne']
    rw [hratioEq] at hb
    have h := mul_le_mul_of_nonneg_left hb hQ.le
    have hc : Q * (P / Q) = P := by field_simp [hQ.ne']
    rw [hc] at h
    change (1 + |z|) ^ 32 * (Q * F (Q * z)) ≤ P
    nlinarith only [h]
  have hScaled := outside_profile_compare G hG hG0 (L / Q) P
    (div_nonneg hL hQ.le) hP.le hprof
  have hscale := scaled_outside_integral F Q L hQ
  have hBasic := boundaryMark_genuine_norm_integrability y N lam hy hNlo hNhi hlam j u
  refine ⟨hBasic.1.integrableOn, ?_⟩
  change (∫ v in {v : ℝ | L < |v|}, F v) ≤ (2 * P) / (1 + L / Q) ^ 31
  rw [← hscale]
  exact hScaled.2

theorem sourceComplexBoundaryMark_localized_norms :
    ∃ C : ℝ, 0 < C ∧
      ∀ (y N lam : ℝ),
        2 ≤ y → (1 / 16 : ℝ) ≤ N → N ≤ 7 →
        y / Real.sqrt N ≤ lam →
          let Delta : ℝ := (1 + lam * y)⁻¹
          ∀ (j : Fin 2) (u : ℝ),
            let a : ℝ → ℝ := sourceComplexBoundaryAmplitude j y N lam
            let B : ℝ → ℂ := sourceComplexBoundaryMark j y N lam u
            (∀ v : ℝ,
              B v = ∫ r : ℝ, (a r : ℂ) *
                Complex.exp
                  (-(((u * y * Real.sqrt r + v * r : ℝ) : ℂ) * Complex.I))) ∧
              (∀ v : ℝ,
                Integrable (fun r : ℝ => (a r : ℂ) *
                  Complex.exp
                    (-(((u * y * Real.sqrt r + v * r : ℝ) : ℂ) * Complex.I)))) ∧
              Continuous B ∧
              Integrable (fun v : ℝ => ‖B v‖) ∧
              Integrable (fun v : ℝ => |v| * ‖B v‖) ∧
              (∫ v : ℝ, ‖B v‖) ≤
                C * (1 + Delta * Real.sqrt (y * |u|)) ∧
              (∫ v : ℝ, |v| * ‖B v‖) ≤
                C * (Delta⁻¹ + y * |u|) *
                  (1 + Delta * Real.sqrt (y * |u|)) ∧
              ∀ aStar : ℝ, 0 < aStar → aStar * y ≤ (1 / 16 : ℝ) →
                let A : Set ℝ := {v : ℝ | |u| / aStar < |v|}
                IntegrableOn (fun v : ℝ => ‖B v‖) A ∧
                  (∫ v in A, ‖B v‖) ≤
                    C / (1 + Delta * |u| / aStar) ^ 31 := by
  obtain ⟨Cn, hCn, hn⟩ := actual_localized_two_norms
  obtain ⟨Co, hCo, ho⟩ := actual_localized_outside_norms
  let C : ℝ := max Cn Co
  have hC : 0 < C := lt_of_lt_of_le hCn (le_max_left Cn Co)
  refine ⟨C, hC, ?_⟩
  intro y N lam hy hNlo hNhi hlam
  dsimp only
  intro j u
  obtain ⟨hi0, hi1⟩ := boundaryMark_genuine_norm_integrability y N lam hy hNlo hNhi hlam j u
  have hnorm := hn y N lam hy hNlo hNhi hlam j u
  dsimp only at hnorm
  obtain ⟨ht, _, _, _, _⟩ := boundary_setup y N lam hy hNlo hNhi hlam
  have hQ : 0 < 1 + lam * y := by linarith only [ht]
  have hT : 0 ≤ y * |u| := mul_nonneg (by linarith only [hy]) (abs_nonneg u)
  refine ⟨boundaryMark_eq j y N lam u, boundaryMark_phase_integrable j y N lam u,
    boundaryMark_continuous j y N lam u, hi0, hi1, ?_, ?_, ?_⟩
  · calc
      _ ≤ Cn * (1 + Real.sqrt (y * |u|) / (1 + lam * y)) := hnorm.1
      _ ≤ C * (1 + Real.sqrt (y * |u|) / (1 + lam * y)) :=
        mul_le_mul_of_nonneg_right (le_max_left Cn Co) (by positivity)
      _ = _ := by rw [div_eq_mul_inv]; ring
  · calc
      _ ≤ Cn * (1 + lam * y + y * |u|) *
          (1 + Real.sqrt (y * |u|) / (1 + lam * y)) := hnorm.2
      _ ≤ C * (1 + lam * y + y * |u|) *
          (1 + Real.sqrt (y * |u|) / (1 + lam * y)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (le_max_left Cn Co) (by positivity)
      _ = _ := by rw [inv_inv, div_eq_mul_inv]; ring
  · intro aStar haStar hsmall
    have hout := ho y N lam hy hNlo hNhi hlam j u aStar haStar hsmall
    dsimp only at hout
    refine ⟨hout.1, ?_⟩
    calc
      _ ≤ Co / (1 + |u| / aStar / (1 + lam * y)) ^ 31 := hout.2
      _ ≤ C / (1 + |u| / aStar / (1 + lam * y)) ^ 31 :=
        div_le_div_of_nonneg_right (le_max_right Cn Co) (by positivity)
      _ = _ := by congr 2; rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]; ring

end Shao.Probability
