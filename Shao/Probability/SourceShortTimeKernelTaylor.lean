import Shao.Probability.SourceShortTimeKernelBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

/- A finite simultaneous-choice estimate produces deterministic uniform bounds.
   The half-supremum selections below are actual spatial points, separately
   chosen for each derivative family.  No interchange of sums and suprema is used. -/
private theorem finite_uniform_budgets (J : Finset ℕ)
    (F : ℕ → ℝ → ℝ → ℝ) (a B cap : ℝ) (ha : 0 < a) (hcap : 0 ≤ cap)
    (hF : ∀ i q w, 0 ≤ F i q w)
    (hsum : ∀ q w : ℕ → ℝ, (∀ i ∈ J, |w i| ≤ cap) →
      a * (∑ i ∈ J, F i (q i) (w i)) ≤ B) :
    ∃ O : ℕ → ℝ, (∀ i, 0 ≤ O i) ∧
      (∀ i ∈ J, ∀ q w, |w| ≤ cap → F i q w ≤ O i) ∧
      a * (∑ i ∈ J, O i) ≤ 2 * B := by
  classical
  have hzero : |(0 : ℝ)| ≤ cap := by simpa using hcap
  have hchoose : ∀ i : ℕ, ∃ p : ℝ × ℝ, |p.2| ≤ cap ∧
      (i ∈ J → ∀ q w, |w| ≤ cap → F i q w ≤ 2 * F i p.1 p.2) := by
    intro i
    by_cases hi : i ∈ J
    · let S : Set ℝ := {v | ∃ q w, |w| ≤ cap ∧ v = F i q w}
      have hne : S.Nonempty := ⟨F i 0 0, 0, 0, hzero, rfl⟩
      have hbd : BddAbove S := by
        refine ⟨B / a, ?_⟩
        rintro v ⟨q, w, hw, rfl⟩
        have hsingle : F i q w ≤ ∑ j ∈ J, F j q w :=
          Finset.single_le_sum (fun j _ => hF j q w) hi
        have hb := hsum (fun _ => q) (fun _ => w) (fun _ _ => hw)
        apply (le_div_iff₀ ha).2
        calc
          F i q w * a = a * F i q w := mul_comm _ _
          _ ≤ a * (∑ j ∈ J, F j q w) := mul_le_mul_of_nonneg_left hsingle ha.le
          _ ≤ B := hb
      have hM : 0 ≤ sSup S := (hF i 0 0).trans (le_csSup hbd ⟨0, 0, hzero, rfl⟩)
      by_cases hpos : 0 < sSup S
      · obtain ⟨v, hv, hhalf⟩ := exists_lt_of_lt_csSup hne
          (show sSup S / 2 < sSup S by linarith)
        rcases hv with ⟨q, w, hw, rfl⟩
        refine ⟨(q, w), hw, fun _ q' w' hw' => ?_⟩
        exact (le_csSup hbd ⟨q', w', hw', rfl⟩).trans (by linarith)
      · refine ⟨(0, 0), hzero, fun _ q w hw => ?_⟩
        have hv : F i q w ≤ sSup S := le_csSup hbd ⟨q, w, hw, rfl⟩
        have hz := hF i 0 0
        linarith
    · exact ⟨(0, 0), hzero, fun h => (hi h).elim⟩
  choose p hp using hchoose
  let O : ℕ → ℝ := fun i => if i ∈ J then 2 * F i (p i).1 (p i).2 else 0
  refine ⟨O, ?_, ?_, ?_⟩
  · intro i
    dsimp only [O]
    split_ifs
    · exact mul_nonneg (by norm_num) (hF _ _ _)
    · exact le_rfl
  · intro i hi q w hw
    simpa only [O, if_pos hi] using (hp i).2 hi q w hw
  · have hb := hsum (fun i => (p i).1) (fun i => (p i).2)
      (fun i _ => (hp i).1)
    have hOs : (∑ i ∈ J, O i) = 2 * (∑ i ∈ J, F i (p i).1 (p i).2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [O, if_pos hi]
    calc
      a * (∑ i ∈ J, O i) = 2 * (a * (∑ i ∈ J, F i (p i).1 (p i).2)) := by
        rw [hOs]
        ring
      _ ≤ 2 * B := mul_le_mul_of_nonneg_left hb (by norm_num)

private theorem even_deriv_zero (g : ℝ → ℝ) (heven : ∀ t, g (-t) = g t)
    (hd : DifferentiableAt ℝ g 0) : deriv g 0 = 0 := by
  have hdneg : HasDerivAt g (deriv g 0) (-(0 : ℝ)) := by simpa only [neg_zero] using hd.hasDerivAt
  have hn : HasDerivAt (fun t : ℝ => g (-t)) (-deriv g 0) 0 := by
    simpa only [Function.comp_def, Pi.neg_apply, id_eq, mul_neg, mul_one] using
      hdneg.comp 0 ((hasDerivAt_id (0 : ℝ)).neg)
  have hfun : (fun t : ℝ => g (-t)) = g := funext heven
  rw [hfun] at hn
  have heq := hn.unique hd.hasDerivAt
  linarith

/- The genuine second derivative first controls g', then comparison with
   ±E t²/2 gives the exact quadratic remainder on the closed interval. -/
private theorem local_quadratic_remainder (g : ℝ → ℝ) (E u : ℝ) (hu : 0 ≤ u)
    (hzero : deriv g 0 = 0)
    (hd : ∀ t ∈ Set.Icc 0 u, DifferentiableAt ℝ g t)
    (hdd : ∀ t ∈ Set.Icc 0 u, DifferentiableAt ℝ (deriv g) t)
    (hbound : ∀ t ∈ Set.Icc 0 u, |deriv (deriv g) t| ≤ E) :
    |g u - g 0| ≤ u ^ 2 / 2 * E := by
  by_cases hz : u = 0
  · subst u
    simp
  have h0 : (0 : ℝ) ∈ Set.Icc 0 u := ⟨le_rfl, hu⟩
  have huI : u ∈ Set.Icc 0 u := ⟨hu, le_rfl⟩
  have hp (t : ℝ) (ht : t ∈ Set.Icc 0 u) : |deriv g t| ≤ E * t := by
    have hh := (convex_Icc (0 : ℝ) u).norm_image_sub_le_of_norm_deriv_le hdd
      (fun r hr => by simpa only [Real.norm_eq_abs] using hbound r hr) h0 ht
    simpa only [hzero, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht.1] using hh
  have hplus (t : ℝ) (ht : t ∈ Set.Icc 0 u) :
      HasDerivAt (fun r : ℝ => E / 2 * r ^ 2 - (g r - g 0))
        (E * t - deriv g t) t := by
    convert (((hasDerivAt_id t).pow 2).const_mul (E / 2)).sub
      ((hd t ht).hasDerivAt.sub_const (g 0)) using 1
    · funext r
      rfl
    · dsimp
      ring
  have hminus (t : ℝ) (ht : t ∈ Set.Icc 0 u) :
      HasDerivAt (fun r : ℝ => E / 2 * r ^ 2 + (g r - g 0))
        (E * t + deriv g t) t := by
    convert (((hasDerivAt_id t).pow 2).const_mul (E / 2)).add
      ((hd t ht).hasDerivAt.sub_const (g 0)) using 1
    · funext r
      rfl
    · dsimp
      ring
  have hmplus : MonotoneOn (fun r : ℝ => E / 2 * r ^ 2 - (g r - g 0))
      (Set.Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) u)
    · exact fun t ht => (hplus t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hplus t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hplus t (interior_subset ht)).deriv]
      exact sub_nonneg.mpr ((le_abs_self _).trans (hp t (interior_subset ht)))
  have hmminus : MonotoneOn (fun r : ℝ => E / 2 * r ^ 2 + (g r - g 0))
      (Set.Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) u)
    · exact fun t ht => (hminus t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hminus t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hminus t (interior_subset ht)).deriv]
      have hh := (abs_le.mp (hp t (interior_subset ht))).1
      linarith
  have hupper := hmplus h0 huI hu
  have hlower := hmminus h0 huI hu
  apply abs_le.mpr
  constructor <;> nlinarith

theorem sourceTruncation_futureNoise_short_kernel_local_shift_budgets :
    ∃ C epsilon0 L2 : ℝ, 0 < C ∧ 0 < epsilon0 ∧ epsilon0 ≤ 1 / 2 ∧
      (16384 : ℝ) ≤ L2 ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
          (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 →
          (∫ a : ℝ, a ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ epsilon0 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            let ρ : Measure ℝ :=
              ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
            let mu : ℝ := ∫ a : ℝ, a ∂ρ
            let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
            let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
            let gamma : ℝ := m3 / variance (id : ℝ → ℝ) ρ
            ∀ y : ℝ, gamma ≤ y → y ≤ 2 →
              let T : ℕ → ℝ := fun i => ((n - i : ℕ) : ℝ) * m2
              let J : Finset ℕ := (Finset.range (n + 1)).filter
                (fun i => n / 2 < i ∧ L2 * gamma ^ 2 ≤ T i ∧
                  T i < max (L2 * gamma ^ 2) (y ^ 2))
              let f : ℕ → ℝ → ℝ → ℝ := fun i q w =>
                sourceFutureNoiseKernel ρ (n - i) y (w, q)
              let o : ℕ → ℝ → ℝ → ℝ := fun i q w =>
                (f i q w - f i q (-w)) / 2
              let e : ℕ → ℝ → ℝ → ℝ := fun i q w =>
                (f i q w + f i q (-w)) / 2
              ∃ O E : ℕ → ℝ,
                (∀ i : ℕ, 0 ≤ O i ∧ 0 ≤ E i) ∧
                (∀ i ∈ J,
                  (∀ w q : ℝ, |w| ≤ y / 16 →
                    |deriv (o i q) w| ≤ O i ∧
                      |deriv (fun r : ℝ => deriv (e i q) r) w| ≤ E i) ∧
                  (∀ u q : ℝ, 0 ≤ u → u ≤ y / 16 →
                    |f i q 0 - f i q (-u)| ≤ u * O i + u ^ 2 / 2 * E i)) ∧
                m2 * (∑ i ∈ J, O i) ≤
                  C * ((n : ℝ) * |mu| + (n : ℝ) * m3) ∧
                m2 * (∑ i ∈ J, E i) ≤ C := by
  classical
  obtain ⟨K, epsilon0, L2, hK, he0, he02, hL2, hkernel⟩ :=
    sourceTruncation_futureNoise_short_kernel_sums
  refine ⟨2 * K, epsilon0, L2, by positivity, he0, he02, hL2, ?_⟩
  intro ν0 hp n h2 hn hm x epsilon hx he he0le hbudget
  letI : IsProbabilityMeasure ν0 := hp
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
  let mu : ℝ := ∫ a : ℝ, a ∂ρ
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
  let gamma : ℝ := m3 / variance (id : ℝ → ℝ) ρ
  change ∀ y : ℝ, gamma ≤ y → y ≤ 2 → _
  intro y hgy hy2
  let T : ℕ → ℝ := fun i => ((n - i : ℕ) : ℝ) * m2
  let J : Finset ℕ := (Finset.range (n + 1)).filter
    (fun i => n / 2 < i ∧ L2 * gamma ^ 2 ≤ T i ∧ T i < max (L2 * gamma ^ 2) (y ^ 2))
  let f : ℕ → ℝ → ℝ → ℝ := fun i q w => sourceFutureNoiseKernel ρ (n - i) y (w, q)
  let o : ℕ → ℝ → ℝ → ℝ := fun i q w => (f i q w - f i q (-w)) / 2
  let e : ℕ → ℝ → ℝ → ℝ := fun i q w => (f i q w + f i q (-w)) / 2
  let A : ℝ := (n : ℝ) * |mu| + (n : ℝ) * m3
  change ∃ O E : ℕ → ℝ, (∀ i, 0 ≤ O i ∧ 0 ≤ E i) ∧
    (∀ i ∈ J, (∀ w q : ℝ, |w| ≤ y / 16 →
      |deriv (o i q) w| ≤ O i ∧ |deriv (fun r : ℝ => deriv (e i q) r) w| ≤ E i) ∧
      (∀ u q : ℝ, 0 ≤ u → u ≤ y / 16 →
        |f i q 0 - f i q (-u)| ≤ u * O i + u ^ 2 / 2 * E i)) ∧
    m2 * (∑ i ∈ J, O i) ≤ 2 * K * A ∧ m2 * (∑ i ∈ J, E i) ≤ 2 * K
  have hdata := hkernel ν0 hp n h2 hn hm x epsilon hx he he0le hbudget y hgy hy2
  change (∀ i ∈ J, ∀ w q : ℝ, |w| ≤ y / 16 →
    DifferentiableAt ℝ (o i q) w ∧ DifferentiableAt ℝ (e i q) w ∧
      DifferentiableAt ℝ (fun r : ℝ => deriv (e i q) r) w) ∧
    (∀ q w : ℕ → ℝ, (∀ i ∈ J, |w i| ≤ y / 16) →
      m2 * (∑ i ∈ J, |deriv (o i (q i)) (w i)|) ≤ K * A ∧
        m2 * (∑ i ∈ J, |deriv (fun r : ℝ => deriv (e i (q i)) r) (w i)|) ≤ K) at hdata
  have heHalf : epsilon ≤ 1 / 2 := he0le.trans he02
  rcases sourceTruncation_variance_bounds ν0 n h2 hn hm x epsilon hx he heHalf hbudget with
    ⟨_, _, _, hVm, _, hV, _, _⟩
  change 0 < variance (id : ℝ → ℝ) ρ at hV
  change variance (id : ℝ → ℝ) ρ = m2 - mu ^ 2 at hVm
  have hm2 : 0 < m2 := by nlinarith [sq_nonneg mu]
  have hg : 0 < gamma := (sourceTruncation_gamma_bounds ν0 n h2 hn hm x epsilon
    hx he heHalf hbudget).2.1
  have hy : 0 < y := hg.trans_le hgy
  have hcap : 0 ≤ y / 16 := by positivity
  obtain ⟨O, hO, hOb, hOs⟩ := finite_uniform_budgets J
    (fun i q w => |deriv (o i q) w|) m2 (K * A) (y / 16) hm2 hcap
    (fun _ _ _ => abs_nonneg _) (fun q w hw => (hdata.2 q w hw).1)
  obtain ⟨E, hE, hEb, hEs⟩ := finite_uniform_budgets J
    (fun i q w => |deriv (fun r : ℝ => deriv (e i q) r) w|) m2 K (y / 16) hm2 hcap
    (fun _ _ _ => abs_nonneg _) (fun q w hw => (hdata.2 q w hw).2)
  refine ⟨O, E, fun i => ⟨hO i, hE i⟩, ?_, ?_, hEs⟩
  · intro i hi
    refine ⟨fun w q hw => ⟨hOb i hi q w hw, hEb i hi q w hw⟩, ?_⟩
    intro u q hu hucap
    by_cases hz : u = 0
    · subst u
      simp
    have hlocal (t : ℝ) (ht : t ∈ Set.Icc 0 u) : |t| ≤ y / 16 := by
      rw [abs_of_nonneg ht.1]
      exact ht.2.trans hucap
    have h0 : (0 : ℝ) ∈ Set.Icc 0 u := ⟨le_rfl, hu⟩
    have huI : u ∈ Set.Icc 0 u := ⟨hu, le_rfl⟩
    have hozero : o i q 0 = 0 := by simp only [o, neg_zero, sub_self, zero_div]
    have heven : ∀ t : ℝ, e i q (-t) = e i q t := by
      intro t
      dsimp only [e]
      rw [neg_neg]
      ring
    have hezero : deriv (e i q) 0 = 0 := even_deriv_zero (e i q) heven
      (hdata.1 i hi 0 q (by simpa using hcap)).2.1
    have hoBound : |o i q u| ≤ u * O i := by
      have hb := (convex_Icc (0 : ℝ) u).norm_image_sub_le_of_norm_deriv_le
        (fun t ht => (hdata.1 i hi t q (hlocal t ht)).1)
        (fun t ht => by simpa only [Real.norm_eq_abs] using hOb i hi q t (hlocal t ht)) h0 huI
      simpa only [hozero, sub_zero, Real.norm_eq_abs, abs_of_nonneg hu, mul_comm] using hb
    have heBound : |e i q u - e i q 0| ≤ u ^ 2 / 2 * E i :=
      local_quadratic_remainder (e i q) (E i) u hu hezero
        (fun t ht => (hdata.1 i hi t q (hlocal t ht)).2.1)
        (fun t ht => (hdata.1 i hi t q (hlocal t ht)).2.2)
        (fun t ht => hEb i hi q t (hlocal t ht))
    have hident : f i q 0 - f i q (-u) = (e i q 0 - e i q u) + o i q u := by
      dsimp only [e, o]
      rw [neg_zero]
      ring
    rw [hident]
    calc
      |(e i q 0 - e i q u) + o i q u| ≤ |e i q 0 - e i q u| + |o i q u| := abs_add_le _ _
      _ ≤ u ^ 2 / 2 * E i + u * O i :=
        add_le_add (by simpa only [abs_sub_comm] using heBound) hoBound
      _ = u * O i + u ^ 2 / 2 * E i := add_comm _ _
  · calc
      m2 * (∑ i ∈ J, O i) ≤ 2 * (K * A) := hOs
      _ = 2 * K * A := by ring

/- BEGIN FIXED CUTOFF PUBLIC COMPANIONS.
Additive export of the fixed one-sixteenth cutoff from the existing proof.
The original source is recovered exactly by deleting this marked block.
-/

theorem sourceTruncation_futureNoise_short_kernel_local_shift_budgets_fixed_cutoff :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
          (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 →
          (∫ a : ℝ, a ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ (1 / 8192 : ℝ) →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            let ρ : Measure ℝ :=
              ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
            let mu : ℝ := ∫ a : ℝ, a ∂ρ
            let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
            let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
            let gamma : ℝ := m3 / variance (id : ℝ → ℝ) ρ
            ∀ y : ℝ, gamma ≤ y → y ≤ 2 →
              let T : ℕ → ℝ := fun i => ((n - i : ℕ) : ℝ) * m2
              let J : Finset ℕ := (Finset.range (n + 1)).filter
                (fun i => n / 2 < i ∧ (16384 : ℝ) * gamma ^ 2 ≤ T i ∧
                  T i < max ((16384 : ℝ) * gamma ^ 2) (y ^ 2))
              let f : ℕ → ℝ → ℝ → ℝ := fun i q w =>
                sourceFutureNoiseKernel ρ (n - i) y (w, q)
              let o : ℕ → ℝ → ℝ → ℝ := fun i q w =>
                (f i q w - f i q (-w)) / 2
              let e : ℕ → ℝ → ℝ → ℝ := fun i q w =>
                (f i q w + f i q (-w)) / 2
              ∃ O E : ℕ → ℝ,
                (∀ i : ℕ, 0 ≤ O i ∧ 0 ≤ E i) ∧
                (∀ i ∈ J,
                  (∀ w q : ℝ, |w| ≤ y / 16 →
                    |deriv (o i q) w| ≤ O i ∧
                      |deriv (fun r : ℝ => deriv (e i q) r) w| ≤ E i) ∧
                  (∀ u q : ℝ, 0 ≤ u → u ≤ y / 16 →
                    |f i q 0 - f i q (-u)| ≤ u * O i + u ^ 2 / 2 * E i)) ∧
                m2 * (∑ i ∈ J, O i) ≤
                  C * ((n : ℝ) * |mu| + (n : ℝ) * m3) ∧
                m2 * (∑ i ∈ J, E i) ≤ C := by
  classical
  obtain ⟨K, hK, hkernel⟩ := sourceTruncation_futureNoise_short_kernel_sums_fixed_cutoff
  let epsilon0 : ℝ := 1 / 8192
  let L2 : ℝ := 16384
  have he0 : 0 < epsilon0 := by norm_num [epsilon0]
  have he02 : epsilon0 ≤ 1 / 2 := by norm_num [epsilon0]
  have hL2 : (16384 : ℝ) ≤ L2 := le_rfl
  refine ⟨2 * K, by positivity, ?_⟩
  intro ν0 hp n h2 hn hm x epsilon hx he he0le hbudget
  letI : IsProbabilityMeasure ν0 := hp
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ epsilon / (1 + x)}
  let mu : ℝ := ∫ a : ℝ, a ∂ρ
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
  let gamma : ℝ := m3 / variance (id : ℝ → ℝ) ρ
  change ∀ y : ℝ, gamma ≤ y → y ≤ 2 → _
  intro y hgy hy2
  let T : ℕ → ℝ := fun i => ((n - i : ℕ) : ℝ) * m2
  let J : Finset ℕ := (Finset.range (n + 1)).filter
    (fun i => n / 2 < i ∧ L2 * gamma ^ 2 ≤ T i ∧ T i < max (L2 * gamma ^ 2) (y ^ 2))
  let f : ℕ → ℝ → ℝ → ℝ := fun i q w => sourceFutureNoiseKernel ρ (n - i) y (w, q)
  let o : ℕ → ℝ → ℝ → ℝ := fun i q w => (f i q w - f i q (-w)) / 2
  let e : ℕ → ℝ → ℝ → ℝ := fun i q w => (f i q w + f i q (-w)) / 2
  let A : ℝ := (n : ℝ) * |mu| + (n : ℝ) * m3
  change ∃ O E : ℕ → ℝ, (∀ i, 0 ≤ O i ∧ 0 ≤ E i) ∧
    (∀ i ∈ J, (∀ w q : ℝ, |w| ≤ y / 16 →
      |deriv (o i q) w| ≤ O i ∧ |deriv (fun r : ℝ => deriv (e i q) r) w| ≤ E i) ∧
      (∀ u q : ℝ, 0 ≤ u → u ≤ y / 16 →
        |f i q 0 - f i q (-u)| ≤ u * O i + u ^ 2 / 2 * E i)) ∧
    m2 * (∑ i ∈ J, O i) ≤ 2 * K * A ∧ m2 * (∑ i ∈ J, E i) ≤ 2 * K
  have hdata := hkernel ν0 hp n h2 hn hm x epsilon hx he he0le hbudget y hgy hy2
  change (∀ i ∈ J, ∀ w q : ℝ, |w| ≤ y / 16 →
    DifferentiableAt ℝ (o i q) w ∧ DifferentiableAt ℝ (e i q) w ∧
      DifferentiableAt ℝ (fun r : ℝ => deriv (e i q) r) w) ∧
    (∀ q w : ℕ → ℝ, (∀ i ∈ J, |w i| ≤ y / 16) →
      m2 * (∑ i ∈ J, |deriv (o i (q i)) (w i)|) ≤ K * A ∧
        m2 * (∑ i ∈ J, |deriv (fun r : ℝ => deriv (e i (q i)) r) (w i)|) ≤ K) at hdata
  have heHalf : epsilon ≤ 1 / 2 := he0le.trans he02
  rcases sourceTruncation_variance_bounds ν0 n h2 hn hm x epsilon hx he heHalf hbudget with
    ⟨_, _, _, hVm, _, hV, _, _⟩
  change 0 < variance (id : ℝ → ℝ) ρ at hV
  change variance (id : ℝ → ℝ) ρ = m2 - mu ^ 2 at hVm
  have hm2 : 0 < m2 := by nlinarith [sq_nonneg mu]
  have hg : 0 < gamma := (sourceTruncation_gamma_bounds ν0 n h2 hn hm x epsilon
    hx he heHalf hbudget).2.1
  have hy : 0 < y := hg.trans_le hgy
  have hcap : 0 ≤ y / 16 := by positivity
  obtain ⟨O, hO, hOb, hOs⟩ := finite_uniform_budgets J
    (fun i q w => |deriv (o i q) w|) m2 (K * A) (y / 16) hm2 hcap
    (fun _ _ _ => abs_nonneg _) (fun q w hw => (hdata.2 q w hw).1)
  obtain ⟨E, hE, hEb, hEs⟩ := finite_uniform_budgets J
    (fun i q w => |deriv (fun r : ℝ => deriv (e i q) r) w|) m2 K (y / 16) hm2 hcap
    (fun _ _ _ => abs_nonneg _) (fun q w hw => (hdata.2 q w hw).2)
  refine ⟨O, E, fun i => ⟨hO i, hE i⟩, ?_, ?_, hEs⟩
  · intro i hi
    refine ⟨fun w q hw => ⟨hOb i hi q w hw, hEb i hi q w hw⟩, ?_⟩
    intro u q hu hucap
    by_cases hz : u = 0
    · subst u
      simp
    have hlocal (t : ℝ) (ht : t ∈ Set.Icc 0 u) : |t| ≤ y / 16 := by
      rw [abs_of_nonneg ht.1]
      exact ht.2.trans hucap
    have h0 : (0 : ℝ) ∈ Set.Icc 0 u := ⟨le_rfl, hu⟩
    have huI : u ∈ Set.Icc 0 u := ⟨hu, le_rfl⟩
    have hozero : o i q 0 = 0 := by simp only [o, neg_zero, sub_self, zero_div]
    have heven : ∀ t : ℝ, e i q (-t) = e i q t := by
      intro t
      dsimp only [e]
      rw [neg_neg]
      ring
    have hezero : deriv (e i q) 0 = 0 := even_deriv_zero (e i q) heven
      (hdata.1 i hi 0 q (by simpa using hcap)).2.1
    have hoBound : |o i q u| ≤ u * O i := by
      have hb := (convex_Icc (0 : ℝ) u).norm_image_sub_le_of_norm_deriv_le
        (fun t ht => (hdata.1 i hi t q (hlocal t ht)).1)
        (fun t ht => by simpa only [Real.norm_eq_abs] using hOb i hi q t (hlocal t ht)) h0 huI
      simpa only [hozero, sub_zero, Real.norm_eq_abs, abs_of_nonneg hu, mul_comm] using hb
    have heBound : |e i q u - e i q 0| ≤ u ^ 2 / 2 * E i :=
      local_quadratic_remainder (e i q) (E i) u hu hezero
        (fun t ht => (hdata.1 i hi t q (hlocal t ht)).2.1)
        (fun t ht => (hdata.1 i hi t q (hlocal t ht)).2.2)
        (fun t ht => hEb i hi q t (hlocal t ht))
    have hident : f i q 0 - f i q (-u) = (e i q 0 - e i q u) + o i q u := by
      dsimp only [e, o]
      rw [neg_zero]
      ring
    rw [hident]
    calc
      |(e i q 0 - e i q u) + o i q u| ≤ |e i q 0 - e i q u| + |o i q u| := abs_add_le _ _
      _ ≤ u ^ 2 / 2 * E i + u * O i :=
        add_le_add (by simpa only [abs_sub_comm] using heBound) hoBound
      _ = u * O i + u ^ 2 / 2 * E i := add_comm _ _
  · calc
      m2 * (∑ i ∈ J, O i) ≤ 2 * (K * A) := hOs
      _ = 2 * K * A := by ring

/- END FIXED CUTOFF PUBLIC COMPANIONS. -/

end Shao.Probability
