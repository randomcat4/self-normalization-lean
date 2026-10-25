import Shao.Probability.MeasurablePath
import Shao.Probability.BoundedQuadraticTilt
import Shao.C2.AuxiliaryEnergyCentered
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Martingale.OptionalStopping

import Shao.Probability.EndpointRelativeError
import Lean

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace Shao.Probability.SourceCircularWitnessMoment
open MeasureTheory ProbabilityTheory
open scoped BigOperators
private theorem cwm_log_mgf_taylor :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (B : ℝ), 0 < B → (∀ᵐ z : ℝ ∂rho, |z| ≤ B) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        let c : ℝ → ℝ := fun t => ∫ z : ℝ, Real.exp (t * z) ∂rho
        ∀ t : ℝ, |t| * B ≤ 3 / 5 →
          Integrable (fun z : ℝ => Real.exp (t * z)) rho ∧
            1 ≤ c t ∧
            |Real.log (c t) - t ^ 2 / 2| ≤ C * |t| ^ 3 * beta := by
  let E : ℝ := 24 * Real.exp 1
  let K : ℝ := 1 + E
  have hE : 0 < E := by dsimp [E]; positivity
  have hK : 1 ≤ K := by dsimp [K]; linarith
  refine ⟨E + K ^ 2, by nlinarith [sq_nonneg (K - 1)], ?_⟩
  intro rho hprob B hB hs hmean hsecond beta c t ht
  have hbase := boundedQuadraticTilt_density_moments rho B 0 0 hB (le_refl 0) hs
  rcases hbase with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hpows, _⟩
  have hi : Integrable (fun z : ℝ => z) rho := by simpa using (hpows 1).1
  have h2 : Integrable (fun z : ℝ => z ^ 2) rho := (hpows 2).1
  have h3 : Integrable (fun z : ℝ => |z| ^ 3) rho := (hpows 3).2.2.1
  have hb1 : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one
      rho h2 h3 hsecond
  have hbB : beta ≤ B := by
    have hh : ∀ᵐ z : ℝ ∂rho, |z| ^ 3 ≤ B * z ^ 2 := by
      filter_upwards [hs] with z hz
      calc
        |z| ^ 3 = |z| * z ^ 2 := by rw [← sq_abs z]; ring
        _ ≤ B * z ^ 2 := mul_le_mul_of_nonneg_right hz (sq_nonneg z)
    have hh' := integral_mono_ae h3 (h2.const_mul B) hh
    simpa only [integral_const_mul, hsecond, mul_one] using hh'
  have hB1 : 1 ≤ B := hb1.trans hbB
  have habs : |t| ≤ 3 / 5 := by
    have hx := mul_nonneg (abs_nonneg t) (sub_nonneg.mpr hB1)
    nlinarith
  have hbeta0 : 0 ≤ beta := by linarith
  have habsBeta : |t| * beta ≤ 1 := by
    calc
      |t| * beta ≤ |t| * B := mul_le_mul_of_nonneg_left hbB (abs_nonneg t)
      _ ≤ 3 / 5 := ht
      _ ≤ 1 := by norm_num
  have hsign : t = |t| ∨ t = -|t| := by
    by_cases hh : 0 ≤ t
    · exact Or.inl (abs_of_nonneg hh).symm
    · exact Or.inr (by rw [abs_of_neg (lt_of_not_ge hh)]; ring)
  have hnormal := boundedQuadraticTilt_joint_moments_normalizer
    rho B |t| t 0 hB (abs_nonneg t) hsign (le_refl 0)
    (sq_nonneg |t|) (by simpa using abs_nonneg t) hs
  rcases hnormal with
    ⟨hExp0, _, _, _, _, _, _, hPos0, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hTaylor0, hLog0, _⟩
  have hExp : Integrable (fun z : ℝ => Real.exp (t * z)) rho := by
    simpa only [zero_mul, sub_zero] using hExp0
  have hPos : 0 < c t := by simpa only [zero_mul, sub_zero] using hPos0
  have hct1 : 1 ≤ c t := by
    have hlin : Integrable (fun z : ℝ => 1 + t * z) rho :=
      (integrable_const 1).add (hi.const_mul t)
    have hh := integral_mono hlin hExp (fun z => by
      linarith [Real.add_one_le_exp (t * z)])
    have htint : (∫ z : ℝ, t * z ∂rho) = 0 := by
      rw [integral_const_mul, hmean, mul_zero]
    rw [integral_add (integrable_const 1) (hi.const_mul t), htint, add_zero] at hh
    simpa only [integral_const, probReal_univ, one_smul] using hh
  have hTaylor : |c t - 1 - t ^ 2 / 2| ≤ E * |t| ^ 3 * beta := by
    simp only [zero_mul, sub_zero, hmean, hsecond, mul_zero, mul_one, sq_abs] at hTaylor0
    change |c t - 1 - t ^ 2 / 2| ≤
      24 * |t| ^ 3 * beta * Real.exp (|t| * B) at hTaylor0
    calc
      |c t - 1 - t ^ 2 / 2| ≤
          24 * |t| ^ 3 * beta * Real.exp (|t| * B) := hTaylor0
      _ ≤ 24 * |t| ^ 3 * beta * Real.exp 1 := by
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (ht.trans (by norm_num))) (by positivity)
      _ = E * |t| ^ 3 * beta := by dsimp [E]; ring
  let u : ℝ := c t - 1
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  have heq : |t| ^ 3 * beta = t ^ 2 * (|t| * beta) := by
    calc
      |t| ^ 3 * beta = |t| ^ 2 * (|t| * beta) := by ring
      _ = _ := by rw [sq_abs]
  have herr : E * |t| ^ 3 * beta ≤ E * t ^ 2 := by
    rw [mul_assoc E, heq]
    simpa only [mul_assoc, mul_one] using
      (mul_le_mul_of_nonneg_left habsBeta (mul_nonneg hE.le (sq_nonneg t)))
  have huK : u ≤ K * t ^ 2 := by
    have hh := (abs_le.mp hTaylor).2
    dsimp [u, K]
    nlinarith [sq_nonneg t]
  have hu2 : u ^ 2 ≤ K ^ 2 * t ^ 4 := by
    have hh := pow_le_pow_left₀ hu0 huK 2
    convert hh using 1 <;> ring
  have h41 : t ^ 4 ≤ |t| ^ 3 * beta := by
    have htBeta : |t| ≤ beta := habs.trans ((by norm_num : (3 / 5 : ℝ) ≤ 1).trans hb1)
    calc
      t ^ 4 = (t ^ 2) ^ 2 := by ring
      _ = (|t| ^ 2) ^ 2 := by rw [sq_abs]
      _ = |t| ^ 3 * |t| := by ring
      _ ≤ |t| ^ 3 * beta :=
        mul_le_mul_of_nonneg_left htBeta (pow_nonneg (abs_nonneg t) 3)
  have hu2' : u ^ 2 ≤ K ^ 2 * (|t| ^ 3 * beta) := by
    exact hu2.trans (mul_le_mul_of_nonneg_left h41 (sq_nonneg K))
  have hlo : u - u ^ 2 ≤ Real.log (c t) := by
    have hh := Real.le_log_one_add_of_nonneg hu0
    have hden : 0 < u + 2 := by linarith
    have hfrac : u - u ^ 2 ≤ 2 * u / (u + 2) := by
      apply (le_div_iff₀ hden).2
      nlinarith [sq_nonneg u, mul_nonneg hu0 (sq_nonneg u)]
    have he : 1 + u = c t := by dsimp [u]; ring
    rw [he] at hh
    exact hfrac.trans hh
  have hhi : Real.log (c t) ≤ u := by
    exact Real.log_le_sub_one_of_pos hPos
  refine ⟨hExp, hct1, abs_le.mpr ⟨?_, ?_⟩⟩
  · have hh := (abs_le.mp hTaylor).1
    dsimp [u] at hlo hu2'
    nlinarith
  · have hh := (abs_le.mp hTaylor).2
    have hp : 0 ≤ |t| ^ 3 * beta := by positivity
    dsimp [u] at hhi
    nlinarith [mul_nonneg (sq_nonneg K) hp]

private theorem cwm_canonical_exponential_martingale
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (B q : ℝ) (hB : 0 < B)
    (hsupport : ∀ᵐ z : ℝ ∂nu, |z| ≤ B) :
    let c : ℝ := ∫ z : ℝ, Real.exp (q * z) ∂nu
    0 < c ∧
      ∀ N : ℕ,
        let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => nu)
        let S : ℕ → Finset (Fin N) := fun k =>
          Finset.univ.filter (fun i : Fin N => i.val < k)
        let Z : ℕ → Shao.Path N → ℝ := fun k a =>
          ∏ i ∈ S k, Real.exp (q * a i) / c
        ∃ Filt : Filtration ℕ (inferInstance : MeasurableSpace (Shao.Path N)),
          (∀ k : ℕ, Filt k =
            MeasurableSpace.comap
              (fun a : Shao.Path N => fun i : S k => a i)
              (inferInstance : MeasurableSpace ((S k) → ℝ))) ∧
          Martingale Z Filt P ∧
          (∀ (k : ℕ) (a : Shao.Path N), 0 ≤ Z k a) ∧
          ∀ k : ℕ, Integrable (Z k) P ∧ (∫ a, Z k a ∂P) = 1 := by
  classical
  intro c
  have hData := boundedQuadraticTilt_density_moments nu B q 0 hB (le_refl 0) hsupport
  have hE0 := hData.1
  have hc0 := hData.2.1
  clear hData
  have hE : Integrable (fun z : ℝ => Real.exp (q * z)) nu := by
    simpa only [zero_mul, sub_zero] using hE0
  have hc : 0 < c := by simpa only [zero_mul, sub_zero] using hc0
  refine ⟨hc, ?_⟩
  intro N P S Z
  let Y : ℝ → ℝ := fun z => Real.exp (q * z) / c
  have hYm : Measurable Y := by fun_prop
  have hYi : Integrable Y nu := hE.div_const c
  have hYmean : (∫ z, Y z ∂nu) = 1 := by
    dsimp [Y]
    rw [integral_div]
    exact div_self hc.ne'
  have hYnonneg (z : ℝ) : 0 ≤ Y z := div_nonneg (Real.exp_pos _).le hc.le
  have hSm : Monotone S := by
    intro j k hjk i hi
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact lt_of_lt_of_le hi hjk
  let Filt : Filtration ℕ (inferInstance : MeasurableSpace (Shao.Path N)) :=
    { seq := fun k => Filtration.piFinset (X := fun _ : Fin N => ℝ) (S k)
      mono' := fun j k hjk => Filtration.piFinset.mono (hSm hjk)
      le' := fun k => Filtration.piFinset.le (S k) }
  have hFilt (k : ℕ) : Filt k =
      MeasurableSpace.comap
        (fun a : Shao.Path N => fun i : S k => a i)
        (inferInstance : MeasurableSpace ((S k) → ℝ)) := rfl
  have hZsub (k : ℕ) (a : Shao.Path N) :
      Z k a = ∏ i : S k, Y (a i) := by
    dsimp only [Z, Y]
    exact (Finset.prod_coe_sort (S k)
      (fun i : Fin N => Real.exp (q * a i) / c)).symm
  have hZfull (k : ℕ) (a : Shao.Path N) :
      Z k a = ∏ i : Fin N, if i.val < k then Y (a i) else 1 := by
    dsimp only [Z, S, Y]
    exact Finset.prod_filter _ _
  have hZi (k : ℕ) : Integrable (Z k) P := by
    have hi (i : Fin N) : Integrable
        (fun z : ℝ => if i.val < k then Y z else 1) nu := by
      by_cases h : i.val < k
      · simpa only [if_pos h] using hYi
      · simpa only [if_neg h] using (integrable_const (1 : ℝ) : Integrable _ nu)
    exact (Integrable.fintype_prod hi).congr (ae_of_all _ fun a => (hZfull k a).symm)
  have hZmean (k : ℕ) : (∫ a, Z k a ∂P) = 1 := by
    calc
      _ = ∫ a : Shao.Path N, ∏ i : Fin N,
          if i.val < k then Y (a i) else 1 ∂P :=
        integral_congr_ae (ae_of_all _ (hZfull k))
      _ = ∏ i : Fin N, ∫ z : ℝ,
          (if i.val < k then Y z else 1) ∂nu :=
        integral_fintype_prod_eq_prod
          (μ := fun _ : Fin N => nu)
          (fun i : Fin N => fun z : ℝ => if i.val < k then Y z else 1)
      _ = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        by_cases h : i.val < k <;> simp [h, hYmean]
  have hZa : StronglyAdapted Filt Z := by
    intro k
    have hG : Measurable (fun b : (S k) → ℝ => ∏ i, Y (b i)) := by
      fun_prop
    have hRes : @Measurable (Shao.Path N) ((S k) → ℝ)
        (Filt k) inferInstance (fun a i => a i) := by
      exact comap_measurable _
    have heq : Z k = (fun b : (S k) → ℝ => ∏ i, Y (b i)) ∘
        (fun a : Shao.Path N => fun i : S k => a i) :=
      funext (hZsub k)
    rw [heq]
    exact (hG.comp hRes).stronglyMeasurable
  refine ⟨Filt, hFilt, ?_, ?_, fun k => ⟨hZi k, hZmean k⟩⟩
  · apply martingale_of_setIntegral_eq_succ hZa hZi
    intro k s hs
    by_cases hk : k < N
    · let i : Fin N := ⟨k, hk⟩
      have hi : i ∉ S k := by simp [S, i]
      have hSk : S (k + 1) = insert i (S k) := by
        ext j
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hj
          by_cases h : j.val = k
          · left; exact Fin.ext h
          · right; omega
        · rintro (rfl | hj)
          · exact Nat.lt_succ_self k
          · omega
      have hsucc (a : Shao.Path N) : Z (k + 1) a = Z k a * Y (a i) := by
        simp only [Z, hSk, Finset.prod_insert hi]
        dsimp [Y]
        ring
      have hcoord : iIndepFun (fun j : Fin N => fun a : Shao.Path N => a j) P :=
        iIndepFun_pi (fun _ : Fin N => measurable_id.aemeasurable)
      have hdis : Disjoint (S k) ({i} : Finset (Fin N)) := by
        simpa using hi
      have hind := hcoord.indepFun_finset (S k) {i} hdis
        (fun j : Fin N => measurable_pi_apply j)
      rw [hFilt k] at hs
      rcases hs with ⟨t, ht, rfl⟩
      let G : ((S k) → ℝ) → ℝ :=
        t.indicator (fun b => ∏ j : S k, Y (b j))
      have hG : Measurable G := by
        apply Measurable.indicator _ ht
        fun_prop
      let j : ({i} : Finset (Fin N)) := ⟨i, by simp⟩
      have hV : Measurable (fun b : ({i} : Finset (Fin N)) → ℝ => Y (b j)) :=
        hYm.comp (measurable_pi_apply j)
      have hind' := hind.comp hG hV
      have hKind (a : Shao.Path N) :
          G (fun j : S k => a j) =
            ((fun a : Shao.Path N => (fun b : (S k) → ℝ => b) (fun j => a j)) ⁻¹' t).indicator
              (Z k) a := by
        simp only [G, Set.indicator_apply, Set.mem_preimage]
        split_ifs <;> simp_all [hZsub]
      have hYcoord : (∫ a : Shao.Path N, Y (a i) ∂P) = 1 := by
        rw [← hYmean]
        have hm := (measurePreserving_eval (fun _ : Fin N => nu) i).map_eq
        rw [← hm]
        exact (integral_map (measurable_pi_apply i).aemeasurable
          hYm.aestronglyMeasurable).symm
      have hmul : (∫ a : Shao.Path N,
          G (fun j : S k => a j) * Y (a i) ∂P) =
          ∫ a : Shao.Path N, G (fun j : S k => a j) ∂P := by
        have hh := hind'.integral_mul_eq_mul_integral
          (hG.comp (by fun_prop)).aestronglyMeasurable
          (hYm.comp (measurable_pi_apply i)).aestronglyMeasurable
        change (∫ a : Shao.Path N, G (fun j : S k => a j) * Y (a i) ∂P) =
          (∫ a : Shao.Path N, G (fun j : S k => a j) ∂P) *
            (∫ a : Shao.Path N, Y (a i) ∂P) at hh
        rw [hYcoord, mul_one] at hh
        exact hh
      rw [← integral_indicator (ht.preimage (by fun_prop) : MeasurableSet
          ((fun a : Shao.Path N => fun j : S k => a j) ⁻¹' t)),
        ← integral_indicator (ht.preimage (by fun_prop) : MeasurableSet
          ((fun a : Shao.Path N => fun j : S k => a j) ⁻¹' t))]
      calc
        _ = ∫ a : Shao.Path N, G (fun j : S k => a j) ∂P := by
          congr 1
          funext a
          simpa only [Function.comp_apply, id_eq] using (hKind a).symm
        _ = ∫ a : Shao.Path N,
            G (fun j : S k => a j) * Y (a i) ∂P := hmul.symm
        _ = _ := by
          apply integral_congr_ae
          exact ae_of_all _ fun a => by
            simp only [G, Set.indicator_apply, Set.mem_preimage]
            split_ifs
            · rw [hsucc, hZsub]
            · simp
    · have hcap : S (k + 1) = S k := by
        ext i
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        have hi := i.isLt
        omega
      have hz : Z (k + 1) = Z k := by funext a; simp only [Z, hcap]
      rw [hz]
  · intro k a
    exact Finset.prod_nonneg (fun i _ => hYnonneg (a i))

private theorem cwm_finite_exponential_maximum
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (B q r : ℝ) (hB : 0 < B)
    (hsupport : ∀ᵐ z : ℝ ∂nu, |z| ≤ B)
    (hr : 0 < r) (hrq : r < q) :
    let c : ℝ := ∫ z : ℝ, Real.exp (q * z) ∂nu
    ∀ N : ℕ,
      let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => nu)
      Integrable (fun a : Shao.Path N => Real.exp (r * Shao.maxWithZero a)) P ∧
        (∫ a : Shao.Path N, Real.exp (r * Shao.maxWithZero a) ∂P) ≤
          1 + r / (q - r) * Real.exp ((N : ℝ) * max (Real.log c) 0) := by
  classical
  intro c N P
  have hq : 0 < q := hr.trans hrq
  rcases cwm_canonical_exponential_martingale nu B q hB hsupport with ⟨hc, hCan⟩
  let S : ℕ → Finset (Fin N) := fun k => Finset.univ.filter (fun i => i.val < k)
  let Z : ℕ → Shao.Path N → ℝ := fun k a =>
    ∏ i ∈ S k, Real.exp (q * a i) / c
  rcases hCan N with ⟨Filt, hFilt, hMart, hZn, hZi⟩
  let D : ℝ := (N : ℝ) * max (Real.log c) 0
  let H : Shao.Path N → ℝ := Shao.maxWithZero
  have hHm : Measurable H := Shao.measurable_maxWithZero
  have hHn (a : Shao.Path N) : 0 ≤ H a := Shao.maxWithZero_nonneg a
  have hZexp (k : ℕ) (a : Shao.Path N) :
      Z k a = Real.exp (q * Shao.prefixSum a k - (S k).card * Real.log c) := by
    calc
      _ = ∏ i ∈ S k, Real.exp (q * a i - Real.log c) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [Real.exp_sub, Real.exp_log hc]
      _ = Real.exp (∑ i ∈ S k, (q * a i - Real.log c)) :=
        (Real.exp_sum _ _).symm
      _ = _ := by
        congr 1
        simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
          S, Shao.prefixSum, Finset.mul_sum]
  have hZm (k : ℕ) : Continuous (Z k) := by
    dsimp only [Z]
    fun_prop
  have hTail (u : ℝ) : P.real {a | u ≤ H a} ≤ Real.exp D * Real.exp (-q * u) := by
    let e : ℝ := Real.exp (q * u - D)
    have he : 0 < e := Real.exp_pos _
    let F : Shao.Path N → ℝ := fun a =>
      (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one (fun k => Z k a)
    let E : Set (Shao.Path N) := {a | e ≤ F a}
    have hFm : Continuous F :=
      Continuous.finset_sup'_apply _ (fun k _ => hZm k)
    have hEm : MeasurableSet E := measurableSet_le measurable_const hFm.measurable
    have hsub : {a : Shao.Path N | u ≤ H a} ⊆ E := by
      intro a ha
      change u ≤ (Finset.Icc 0 N).sup' _ (Shao.prefixSum a) at ha
      rw [Finset.le_sup'_iff] at ha
      obtain ⟨k, hk, huk⟩ := ha
      have hkn : k ≤ N := (Finset.mem_Icc.mp hk).2
      have hcard : ((S k).card : ℝ) ≤ N := by
        have hh : (S k).card ≤ N := by simpa using (Finset.card_le_univ (s := S k))
        exact_mod_cast hh
      have hcost : (S k).card * Real.log c ≤ D :=
        (mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg _)).trans
          (mul_le_mul_of_nonneg_right hcard (le_max_right _ _))
      have heZ : e ≤ Z k a := by
        rw [hZexp]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left huk hq.le]
      exact heZ.trans (Finset.le_sup' (fun k => Z k a)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hkn)))
    have hsetI : (∫ a in E, Z N a ∂P) ≤ 1 := by
      rw [← (hZi N).2, ← integral_indicator hEm]
      apply integral_mono ((hZi N).1.indicator hEm) (hZi N).1
      intro a
      by_cases ha : a ∈ E
      · simp only [Set.indicator_of_mem ha]
        exact le_refl _
      · simp only [Set.indicator_of_notMem ha]
        exact hZn N a
    have hsetN : 0 ≤ ∫ a in E, Z N a ∂P :=
      integral_nonneg (fun a => hZn N a)
    have hDoob := maximal_ineq hMart.submartingale hZn (ε := ⟨e, he.le⟩) N
    have hDoobR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hDoob
    simp only [ENNReal.toReal_mul, ENNReal.coe_toReal] at hDoobR
    change (e * (P E).toReal) ≤ (ENNReal.ofReal (∫ a in E, Z N a ∂P)).toReal at hDoobR
    rw [ENNReal.toReal_ofReal hsetN] at hDoobR
    have hPE : P.real E ≤ 1 / e := by
      change (P E).toReal ≤ 1 / e
      apply (le_div_iff₀ he).mpr
      nlinarith [hDoobR, hsetI]
    calc
      _ ≤ P.real E := measureReal_mono hsub
      _ ≤ 1 / e := hPE
      _ = Real.exp D * Real.exp (-q * u) := by
        rw [one_div, ← Real.exp_neg, ← Real.exp_add]
        congr 1
        ring
  have hsP : ∀ᵐ a : Shao.Path N ∂P, ∀ i : Fin N, |a i| ≤ B := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin N => nu) (i := i)).eventually
      hsupport
  have hHb : ∀ᵐ a : Shao.Path N ∂P, H a ≤ (N : ℝ) * B := by
    filter_upwards [hsP] with a ha
    apply (Shao.maxWithZero_le_iff a _).mpr
    intro k hk
    calc
      Shao.prefixSum a k ≤ ∑ i ∈ S k, |a i| :=
        Finset.sum_le_sum (fun i hi => le_abs_self (a i))
      _ ≤ ∑ i : Fin N, |a i| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i hi hnot => abs_nonneg _)
      _ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum (fun i hi => ha i)
      _ = (N : ℝ) * B := by simp
  have hExpI : Integrable (fun a : Shao.Path N => Real.exp (r * H a)) P := by
    apply (integrable_const (Real.exp (r * (N : ℝ) * B))).mono'
      ((measurable_const.mul hHm).exp.aestronglyMeasurable)
    filter_upwards [hHb] with a ha
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    change r * H a ≤ r * (N : ℝ) * B
    nlinarith
  refine ⟨hExpI, ?_⟩
  let g : ℝ → ℝ := fun t => r * Real.exp (r * t)
  have hgCont : Continuous g := by fun_prop
  have hprimitive (t : ℝ) : (∫ v in 0..t, g v) = Real.exp (r * t) - 1 := by
    have hh : (∫ v in 0..t, g v) = Real.exp (r * t) - Real.exp (r * 0) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro v hv
        convert ((hasDerivAt_id v).const_mul r).exp using 1 <;> simp [g, mul_comm]
      · exact hgCont.intervalIntegrable 0 t
    simpa using hh
  have hLC := lintegral_comp_eq_lintegral_meas_le_mul_of_measurable P hHn hHm
    (fun t ht => hgCont.intervalIntegrable 0 t) hgCont.measurable
    (fun t ht => mul_nonneg hr.le (Real.exp_pos _).le)
  simp_rw [hprimitive] at hLC
  have hdiffI : Integrable (fun a : Shao.Path N => Real.exp (r * H a) - 1) P :=
    hExpI.sub (integrable_const 1)
  have hdiffN (a : Shao.Path N) : 0 ≤ Real.exp (r * H a) - 1 := by
    have hh : 0 ≤ r * H a := mul_nonneg hr.le (hHn a)
    linarith [Real.one_le_exp_iff.mpr hh]
  have hK : IntegrableOn (fun t : ℝ => Real.exp D * r * Real.exp ((r - q) * t))
      (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : r - q < 0) 0).const_mul _
  have hKint : (∫ t : ℝ in Set.Ioi 0,
      Real.exp D * r * Real.exp ((r - q) * t)) =
      Real.exp D * r / (q - r) := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : r - q < 0)]
    simp only [mul_zero, Real.exp_zero]
    rw [show r - q = -(q - r) by ring]
    simp only [neg_div_neg_eq]
    ring
  have hENN : ENNReal.ofReal (∫ a, Real.exp (r * H a) - 1 ∂P) ≤
      ENNReal.ofReal (Real.exp D * r / (q - r)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hdiffI (ae_of_all _ hdiffN), hLC]
    calc
      _ ≤ ∫⁻ t : ℝ in Set.Ioi 0,
          ENNReal.ofReal (Real.exp D * r * Real.exp ((r - q) * t)) := by
        apply lintegral_mono
        intro t
        have ht : P {a : Shao.Path N | t ≤ H a} ≤
            ENNReal.ofReal (Real.exp D * Real.exp (-q * t)) := by
          rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
          exact ENNReal.ofReal_le_ofReal (hTail t)
        calc
          _ ≤ ENNReal.ofReal (Real.exp D * Real.exp (-q * t)) * ENNReal.ofReal (g t) :=
            mul_le_mul ht le_rfl (by positivity) (by positivity)
          _ = _ := by
            rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp D * Real.exp (-q * t))]
            congr 1
            dsimp only [g]
            calc
              _ = Real.exp D * r * (Real.exp (-q * t) * Real.exp (r * t)) := by ring
              _ = _ := by rw [← Real.exp_add]; congr 2 <;> ring
      _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal hK
          (ae_of_all _ fun t => by positivity), hKint]
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity :
      0 ≤ Real.exp D * r / (q - r))).mp hENN
  rw [integral_sub hExpI (integrable_const 1)] at hreal
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hreal
  change (∫ a, Real.exp (r * H a) ∂P) ≤
    1 + r / (q - r) * Real.exp ((N : ℝ) * max (Real.log c) 0)
  dsimp only [D] at hreal
  have hcomm : Real.exp ((N : ℝ) * max (Real.log c) 0) * r / (q - r) =
      r / (q - r) * Real.exp ((N : ℝ) * max (Real.log c) 0) := by ring
  rw [hcomm] at hreal
  linarith

private theorem cwm_circular_arc_prefix_formula
    (N : ℕ) (hN : 0 < N) (a : Shao.Path N)
    (i : Fin N) (k : Fin (N + 1)) :
    (∑ r ∈ Finset.range k.val,
      a ⟨(i.val + r) % N, Nat.mod_lt _ hN⟩) =
      if i.val + k.val ≤ N then
        Shao.prefixSum a (i.val + k.val) - Shao.prefixSum a i.val
      else
        Shao.prefixSum a N - Shao.prefixSum a i.val +
          Shao.prefixSum a (i.val + k.val - N) := by
  classical
  let f : ℕ → ℝ := fun r => a ⟨r % N, Nat.mod_lt _ hN⟩
  have hp (t : ℕ) (ht : t ≤ N) :
      Shao.prefixSum a t = ∑ r ∈ Finset.range t, f r := by
    unfold Shao.prefixSum
    refine Finset.sum_bij (fun j _ => j.val) ?_ ?_ ?_ ?_
    · intro j hj
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
    · intro j hj l hl heq
      exact Fin.ext heq
    · intro r hr
      have hrN : r < N := (Finset.mem_range.mp hr).trans_le ht
      refine ⟨⟨r, hrN⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.mem_range.mp hr
    · intro j hj
      congr 1
      apply Fin.ext
      exact (Nat.mod_eq_of_lt j.isLt).symm
  have hAdd := Finset.sum_range_add f i.val k.val
  have hiN : i.val ≤ N := i.isLt.le
  have hkN : k.val ≤ N := Nat.le_of_lt_succ k.isLt
  have hperiod (r : ℕ) : f (N + r) = f r := by
    dsimp only [f]
    congr 1
    apply Fin.ext
    simp [Nat.add_mod]
  by_cases hwrap : i.val + k.val ≤ N
  · rw [if_pos hwrap, hp _ hwrap, hp _ hiN]
    change (∑ r ∈ Finset.range k.val, f (i.val + r)) = _
    linarith [hAdd]
  · rw [if_neg hwrap, hp _ (le_refl N), hp _ hiN,
      hp _ (by omega : i.val + k.val - N ≤ N)]
    change (∑ r ∈ Finset.range k.val, f (i.val + r)) = _
    have hsplit := Finset.sum_range_add f N (i.val + k.val - N)
    have htotal : N + (i.val + k.val - N) = i.val + k.val := by omega
    rw [htotal] at hsplit
    have hsum : (∑ r ∈ Finset.range (i.val + k.val - N), f (N + r)) =
        ∑ r ∈ Finset.range (i.val + k.val - N), f r := by
      apply Finset.sum_congr rfl
      intro r hr
      exact hperiod r
    rw [hsum] at hsplit
    linarith [hAdd, hsplit]

private theorem cwm_path_extrema_geometry (N : ℕ) :
  let L : Shao.Path N → ℝ := fun a =>
    if hN : 0 < N then
      sSup {w : ℝ | ∃ i : Fin N, ∃ k : Fin (N + 1),
        w = Shao.prefixSum a N -
          2 * ∑ r ∈ Finset.range k.val,
            a ⟨(i.val + r) % N, Nat.mod_lt _ hN⟩}
    else 0
  let A : Shao.Path N → ℝ := fun a =>
    sSup {w : ℝ | ∃ u v : Fin (N + 1), u.val ≤ v.val ∧
      w = Shao.prefixSum a v.val - Shao.prefixSum a u.val}
  let R : Shao.Path N → ℝ := fun a =>
    sSup {w : ℝ | ∃ u v : Fin (N + 1), u.val ≤ v.val ∧
      w = Shao.prefixSum a u.val - Shao.prefixSum a v.val}
  Measurable L ∧ Measurable A ∧ Measurable R ∧
    ∀ a : Shao.Path N,
      0 ≤ L a ∧ L a ≤ ∑ i : Fin N, |a i| ∧
      0 ≤ A a ∧ A a ≤ ∑ i : Fin N, |a i| ∧
      0 ≤ R a ∧ R a ≤ ∑ i : Fin N, |a i| ∧
      L a = max (Shao.prefixSum a N + 2 * R a)
        (2 * A a - Shao.prefixSum a N) ∧
      R (-a) = A a := by
  classical
  intro L A R
  let J := {uv : Fin (N + 1) × Fin (N + 1) // uv.1.val ≤ uv.2.val}
  letI : Nonempty J := ⟨⟨(0, 0), le_refl _⟩⟩
  have hSupEq {I : Type} [Fintype I] [Nonempty I] (f : I → ℝ) :
      sSup (Set.range f) = Finset.univ.sup' Finset.univ_nonempty f := by
    apply le_antisymm
    · apply csSup_le (Set.range_nonempty f)
      rintro w ⟨j, rfl⟩
      exact Finset.le_sup' f (Finset.mem_univ j)
    · apply Finset.sup'_le
      intro j hj
      exact le_csSup (Set.finite_range f).bddAbove ⟨j, rfl⟩
  have hAset (a : Shao.Path N) :
      {w : ℝ | ∃ u v : Fin (N + 1), u.val ≤ v.val ∧
        w = Shao.prefixSum a v.val - Shao.prefixSum a u.val} =
      Set.range (fun j : J => Shao.prefixSum a j.val.2.val -
        Shao.prefixSum a j.val.1.val) := by
    ext w
    constructor
    · rintro ⟨u, v, huv, rfl⟩
      exact ⟨⟨(u, v), huv⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j.val.1, j.val.2, j.property, rfl⟩
  have hRset (a : Shao.Path N) :
      {w : ℝ | ∃ u v : Fin (N + 1), u.val ≤ v.val ∧
        w = Shao.prefixSum a u.val - Shao.prefixSum a v.val} =
      Set.range (fun j : J => Shao.prefixSum a j.val.1.val -
        Shao.prefixSum a j.val.2.val) := by
    ext w
    constructor
    · rintro ⟨u, v, huv, rfl⟩
      exact ⟨⟨(u, v), huv⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j.val.1, j.val.2, j.property, rfl⟩
  have hArep : A = fun a => Finset.univ.sup' Finset.univ_nonempty
      (fun j : J => Shao.prefixSum a j.val.2.val - Shao.prefixSum a j.val.1.val) := by
    funext a
    dsimp only [A]
    rw [hAset, hSupEq]
  have hRrep : R = fun a => Finset.univ.sup' Finset.univ_nonempty
      (fun j : J => Shao.prefixSum a j.val.1.val - Shao.prefixSum a j.val.2.val) := by
    funext a
    dsimp only [R]
    rw [hRset, hSupEq]
  have hAm : Measurable A := by
    rw [hArep]
    exact (Continuous.finset_sup'_apply _ (fun j _ =>
      (Shao.continuous_prefixSum j.val.2.val).sub
        (Shao.continuous_prefixSum j.val.1.val))).measurable
  have hRm : Measurable R := by
    rw [hRrep]
    exact (Continuous.finset_sup'_apply _ (fun j _ =>
      (Shao.continuous_prefixSum j.val.1.val).sub
        (Shao.continuous_prefixSum j.val.2.val))).measurable
  have hLset (hN : 0 < N) (a : Shao.Path N) :
      {w : ℝ | ∃ i : Fin N, ∃ k : Fin (N + 1),
        w = Shao.prefixSum a N - 2 * ∑ r ∈ Finset.range k.val,
          a ⟨(i.val + r) % N, Nat.mod_lt _ hN⟩} =
      Set.range (fun j : Fin N × Fin (N + 1) => Shao.prefixSum a N -
        2 * ∑ r ∈ Finset.range j.2.val,
          a ⟨(j.1.val + r) % N, Nat.mod_lt _ hN⟩) := by
    ext w
    constructor
    · rintro ⟨i, k, rfl⟩
      exact ⟨(i, k), rfl⟩
    · rintro ⟨⟨i, k⟩, rfl⟩
      exact ⟨i, k, rfl⟩
  have hLm : Measurable L := by
    by_cases hN : 0 < N
    · letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
      have hrep : L = fun a => Finset.univ.sup' Finset.univ_nonempty
          (fun j : Fin N × Fin (N + 1) => Shao.prefixSum a N -
            2 * ∑ r ∈ Finset.range j.2.val,
              a ⟨(j.1.val + r) % N, Nat.mod_lt _ hN⟩) := by
        funext a
        dsimp only [L]
        rw [dif_pos hN, hLset hN, hSupEq]
      rw [hrep]
      exact (Continuous.finset_sup'_apply _ (fun j _ =>
        (Shao.continuous_prefixSum N).sub (continuous_const.mul
          (continuous_finsetSum _ fun r _ => continuous_apply _)))).measurable
    · have hrep : L = fun _ => 0 := by funext a; simp [L, hN]
      rw [hrep]
      exact measurable_const
  refine ⟨hLm, hAm, hRm, ?_⟩
  intro a
  have hAd : BddAbove {w : ℝ | ∃ u v : Fin (N + 1), u.val ≤ v.val ∧
      w = Shao.prefixSum a v.val - Shao.prefixSum a u.val} := by
    rw [hAset]
    exact (Set.finite_range _).bddAbove
  have hRd : BddAbove {w : ℝ | ∃ u v : Fin (N + 1), u.val ≤ v.val ∧
      w = Shao.prefixSum a u.val - Shao.prefixSum a v.val} := by
    rw [hRset]
    exact (Set.finite_range _).bddAbove
  have hAn : 0 ≤ A a := le_csSup hAd ⟨0, 0, le_refl _, by simp⟩
  have hRn : 0 ≤ R a := le_csSup hRd ⟨0, 0, le_refl _, by simp⟩
  have hAbound (u v : ℕ) :
      Shao.prefixSum a v - Shao.prefixSum a u ≤ ∑ i : Fin N, |a i| := by
    simp only [Shao.prefixSum, Finset.sum_filter]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i hi
    by_cases hu : i.val < u <;> by_cases hv : i.val < v
    all_goals simp only [hu, hv, ite_true, ite_false]
    · simpa using (abs_nonneg (a i))
    · simpa using (neg_le_abs (a i))
    · simpa using (le_abs_self (a i))
    · simpa only [sub_self] using abs_nonneg (a i)
  have hAu : A a ≤ ∑ i : Fin N, |a i| := by
    rw [hArep]
    apply Finset.sup'_le
    intro j hj
    exact hAbound j.val.1.val j.val.2.val
  have hRu : R a ≤ ∑ i : Fin N, |a i| := by
    rw [hRrep]
    apply Finset.sup'_le
    intro j hj
    exact hAbound j.val.2.val j.val.1.val
  have hNeg : R (-a) = A a := by
    dsimp only [R, A]
    congr 1
    ext w
    simp only [Shao.prefixSum_neg]
    constructor
    · rintro ⟨u, v, huv, hw⟩
      exact ⟨u, v, huv, by linarith⟩
    · rintro ⟨u, v, huv, hw⟩
      exact ⟨u, v, huv, by linarith⟩
  have hSigned (u v : ℕ) (huv : u ≤ v) :
      |Shao.prefixSum a N - 2 * (Shao.prefixSum a v - Shao.prefixSum a u)| ≤
        ∑ i : Fin N, |a i| := by
    have heq : Shao.prefixSum a N -
        2 * (Shao.prefixSum a v - Shao.prefixSum a u) =
        ∑ i : Fin N, (a i - 2 *
          ((if i.val < v then a i else 0) - (if i.val < u then a i else 0))) := by
      rw [Shao.prefixSum_length]
      simp only [Shao.prefixSum, Finset.sum_filter,
        Finset.sum_sub_distrib, mul_sub, Finset.mul_sum]
    rw [heq]
    calc
      _ ≤ ∑ i : Fin N, |a i - 2 *
          ((if i.val < v then a i else 0) - (if i.val < u then a i else 0))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hu : i.val < u
        · have hv : i.val < v := lt_of_lt_of_le hu huv
          simp [hu, hv]
        · by_cases hv : i.val < v
          · simp only [hu, hv, ite_true, ite_false, sub_zero]
            have he : a i - 2 * a i = -a i := by ring
            rw [he, abs_neg]
          · simp [hu, hv]
  by_cases hN : 0 < N
  · letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    have hLd : BddAbove {w : ℝ | ∃ i : Fin N, ∃ k : Fin (N + 1),
        w = Shao.prefixSum a N - 2 * ∑ r ∈ Finset.range k.val,
          a ⟨(i.val + r) % N, Nat.mod_lt _ hN⟩} := by
      rw [hLset hN]
      exact (Set.finite_range _).bddAbove
    have hLne : Set.Nonempty {w : ℝ | ∃ i : Fin N, ∃ k : Fin (N + 1),
        w = Shao.prefixSum a N - 2 * ∑ r ∈ Finset.range k.val,
          a ⟨(i.val + r) % N, Nat.mod_lt _ hN⟩} :=
      ⟨Shao.prefixSum a N, ⟨0, hN⟩, 0, by simp⟩
    have hLmem (i : Fin N) (k : Fin (N + 1)) :
        Shao.prefixSum a N - 2 * ∑ r ∈ Finset.range k.val,
          a ⟨(i.val + r) % N, Nat.mod_lt _ hN⟩ ≤ L a := by
      dsimp only [L]
      rw [dif_pos hN]
      exact le_csSup hLd ⟨i, k, rfl⟩
    have hLowR (u v : Fin (N + 1)) (huv : u.val ≤ v.val) :
        Shao.prefixSum a N + 2 * (Shao.prefixSum a u.val -
          Shao.prefixSum a v.val) ≤ L a := by
      by_cases hu : u.val < N
      · have h := hLmem ⟨u.val, hu⟩ ⟨v.val - u.val, by omega⟩
        rw [cwm_circular_arc_prefix_formula N hN] at h
        simp only [Fin.val_mk] at h
        have hle : u.val + (v.val - u.val) ≤ N := by omega
        rw [if_pos hle] at h
        have heq : u.val + (v.val - u.val) = v.val := by omega
        rw [heq] at h
        linarith
      · have huN : u.val = N := by omega
        have hvN : v.val = N := by omega
        have h := hLmem ⟨0, hN⟩ 0
        simpa [huN, hvN] using h
    have hLowA (u v : Fin (N + 1)) (huv : u.val ≤ v.val) :
        2 * (Shao.prefixSum a v.val - Shao.prefixSum a u.val) -
          Shao.prefixSum a N ≤ L a := by
      by_cases hv : v.val < N
      · have h := hLmem ⟨v.val, hv⟩ ⟨N - (v.val - u.val), by omega⟩
        rw [cwm_circular_arc_prefix_formula N hN] at h
        simp only [Fin.val_mk] at h
        by_cases hu0 : u.val = 0
        · have hs : v.val + (N - (v.val - u.val)) = N := by omega
          rw [if_pos (by omega), hs] at h
          simp only [hu0, Shao.prefixSum_zero] at h ⊢
          linarith
        · have hs : v.val + (N - (v.val - u.val)) - N = u.val := by omega
          rw [if_neg (by omega), hs] at h
          linarith
      · have hvN : v.val = N := by omega
        have h := hLmem ⟨0, hN⟩ u
        rw [cwm_circular_arc_prefix_formula N hN] at h
        simp only [Fin.val_mk] at h
        simp only [Fin.val_mk, zero_add] at h
        rw [if_pos (by omega)] at h
        simp only [hvN, zero_add, Shao.prefixSum_zero] at h ⊢
        linarith
    obtain ⟨jR, hjR⟩ := (Set.range_nonempty
      (fun j : J => Shao.prefixSum a j.val.1.val - Shao.prefixSum a j.val.2.val)).csSup_mem
        (Set.finite_range _)
    obtain ⟨jA, hjA⟩ := (Set.range_nonempty
      (fun j : J => Shao.prefixSum a j.val.2.val - Shao.prefixSum a j.val.1.val)).csSup_mem
        (Set.finite_range _)
    have hRatt : R a = Shao.prefixSum a jR.val.1.val -
        Shao.prefixSum a jR.val.2.val := by
      dsimp only [R]
      rw [hRset]
      exact hjR.symm
    have hAatt : A a = Shao.prefixSum a jA.val.2.val -
        Shao.prefixSum a jA.val.1.val := by
      dsimp only [A]
      rw [hAset]
      exact hjA.symm
    have heq : L a = max (Shao.prefixSum a N + 2 * R a)
        (2 * A a - Shao.prefixSum a N) := by
      apply le_antisymm
      · dsimp only [L]
        rw [dif_pos hN]
        apply csSup_le hLne
        rintro w ⟨i, k, rfl⟩
        rw [cwm_circular_arc_prefix_formula N hN]
        split_ifs with hw
        · have hd : Shao.prefixSum a i.val - Shao.prefixSum a (i.val + k.val) ≤ R a :=
            le_csSup hRd ⟨⟨i.val, by omega⟩, ⟨i.val + k.val, by omega⟩,
              by dsimp only; omega, rfl⟩
          linarith [le_max_left (Shao.prefixSum a N + 2 * R a)
            (2 * A a - Shao.prefixSum a N)]
        · have hd : Shao.prefixSum a i.val -
              Shao.prefixSum a (i.val + k.val - N) ≤ A a :=
            le_csSup hAd ⟨⟨i.val + k.val - N, by omega⟩,
              ⟨i.val, by omega⟩, by dsimp only; omega, rfl⟩
          linarith [le_max_right (Shao.prefixSum a N + 2 * R a)
            (2 * A a - Shao.prefixSum a N)]
      · apply max_le
        · rw [hRatt]
          exact hLowR _ _ jR.property
        · rw [hAatt]
          exact hLowA _ _ jA.property
    have hLn : 0 ≤ L a := by
      rw [heq]
      have h1 := le_max_left (Shao.prefixSum a N + 2 * R a)
        (2 * A a - Shao.prefixSum a N)
      have h2 := le_max_right (Shao.prefixSum a N + 2 * R a)
        (2 * A a - Shao.prefixSum a N)
      linarith
    have hLu : L a ≤ ∑ i : Fin N, |a i| := by
      dsimp only [L]
      rw [dif_pos hN]
      apply csSup_le hLne
      rintro w ⟨i, k, rfl⟩
      rw [cwm_circular_arc_prefix_formula N hN]
      split_ifs with hw
      · exact (le_abs_self _).trans (hSigned i.val (i.val + k.val) (by omega))
      · have h := hSigned (i.val + k.val - N) i.val (by omega)
        have he : Shao.prefixSum a N - 2 *
              (Shao.prefixSum a N - Shao.prefixSum a i.val +
                Shao.prefixSum a (i.val + k.val - N)) =
            -(Shao.prefixSum a N - 2 *
              (Shao.prefixSum a i.val - Shao.prefixSum a (i.val + k.val - N))) := by ring
        rw [he]
        exact (neg_le_abs _).trans h
    exact ⟨hLn, hLu, hAn, hAu, hRn, hRu, heq, hNeg⟩
  · have hN0 : N = 0 := by omega
    have hL0 : L a = 0 := by simp [L, hN]
    have hA0 : A a = 0 := le_antisymm (by simpa [hN0] using hAu) hAn
    have hR0 : R a = 0 := le_antisymm (by simpa [hN0] using hRu) hRn
    simp only [hL0, hA0, hR0, hNeg]
    simp [hN0]

private theorem cwm_linear_tilt_product_density
    (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (B theta : ℝ) (hB : 0 < B)
    (hsupport : ∀ᵐ z : ℝ ∂rho, |z| ≤ B) :
    let c : ℝ := ∫ z : ℝ, Real.exp (theta * z) ∂rho
    let nu : Measure ℝ := rho.tilted (fun z => theta * z)
    0 < c ∧ IsProbabilityMeasure nu ∧
      (∀ᵐ z : ℝ ∂nu, |z| ≤ B) ∧
      ∀ N : ℕ,
        let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => rho)
        let Ptilt : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => nu)
        ∀ g : Shao.Path N → ℝ, Integrable g P →
          Integrable g Ptilt ∧
            Integrable (fun a => g a * Real.exp (theta * Shao.prefixSum a N)) P ∧
            (∫ a, g a * Real.exp (theta * Shao.prefixSum a N) ∂P) =
              c ^ N * (∫ a, g a ∂Ptilt) := by
  intro c nu
  rcases boundedQuadraticTilt_density_moments rho B theta 0 hB (le_refl 0) hsupport with
    ⟨hExp0, hc0, _, _, _, _, hNu0, _, _, hsNu0, _⟩
  have hExpScalar : Integrable (fun z : ℝ => Real.exp (theta * z)) rho := by
    simpa only [zero_mul, sub_zero] using hExp0
  have hc : 0 < c := by simpa only [zero_mul, sub_zero] using hc0
  have hNu : IsProbabilityMeasure nu := by
    simpa only [zero_mul, sub_zero] using hNu0
  have hsNu : ∀ᵐ z : ℝ ∂nu, |z| ≤ B := by
    simpa only [zero_mul, sub_zero] using hsNu0
  letI : IsProbabilityMeasure nu := hNu
  refine ⟨hc, hNu, hsNu, ?_⟩
  intro N P Ptilt g hg
  let F : Shao.Path N → ℝ := fun a => theta * Shao.prefixSum a N
  have hsum (a : Shao.Path N) : Shao.prefixSum a N = ∑ i : Fin N, a i := by
    simp [Shao.prefixSum]
  have hF : Measurable F := measurable_const.mul (Shao.measurable_prefixSum N)
  have heq (a : Shao.Path N) : Real.exp (F a) =
      ∏ i : Fin N, Real.exp (theta * a i) := by
    dsimp [F]
    rw [hsum, Finset.mul_sum, Real.exp_sum]
  have hExpF : Integrable (fun a => Real.exp (F a)) P := by
    have hh : Integrable (fun a : Shao.Path N =>
        ∏ i : Fin N, Real.exp (theta * a i)) P :=
      Integrable.fintype_prod (fun _ : Fin N => hExpScalar)
    exact hh.congr (ae_of_all _ fun a => (heq a).symm)
  have hZ : (∫ a, Real.exp (F a) ∂P) = c ^ N := by
    calc
      (∫ a, Real.exp (F a) ∂P) =
          ∫ a : Shao.Path N, ∏ i : Fin N, Real.exp (theta * a i) ∂P :=
        integral_congr_ae (ae_of_all _ heq)
      _ = c ^ N := by
        simpa only [Fintype.card_fin] using
          (integral_fintype_prod_eq_pow (ι := Fin N) (μ := rho)
            (fun z : ℝ => Real.exp (theta * z)))
  have hpi0 : Measure.pi (fun _ : Fin N => rho.tilted (fun z => theta * z)) =
      P.tilted (fun a : Shao.Path N => ∑ i : Fin N, theta * a i) := by
    run_tac
      let n := Lean.mkPrivateNameCore ("Shao.Probability.EndpointRelativeError".toName)
        ("Shao.Probability.er_pi_tilted".toName)
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n)
        $(Lean.mkIdent ("rho".toName)) $(Lean.mkIdent ("N".toName))
        (fun z : ℝ => $(Lean.mkIdent ("theta".toName)) * z)
        (by fun_prop) $(Lean.mkIdent ("hExpScalar".toName))))
  have hpi : Ptilt = P.tilted F := by
    convert hpi0 using 1
    congr 1
    funext a
    dsimp [F]
    rw [hsum, Finset.mul_sum]
  have hsP : ∀ᵐ a : Shao.Path N ∂P, ∀ i : Fin N, |a i| ≤ B := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin N => rho) (i := i)).eventually
      hsupport
  have hsumBound : ∀ᵐ a : Shao.Path N ∂P,
      |Shao.prefixSum a N| ≤ (N : ℝ) * B := by
    filter_upwards [hsP] with a ha
    calc
      |Shao.prefixSum a N| = ‖∑ i : Fin N, a i‖ := by rw [hsum, Real.norm_eq_abs]
      _ ≤ ∑ i : Fin N, |a i| := by
        simpa only [Real.norm_eq_abs] using norm_sum_le Finset.univ (fun i : Fin N => a i)
      _ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum (fun i _ => ha i)
      _ = (N : ℝ) * B := by simp
  have hBound : ∀ᵐ a : Shao.Path N ∂P,
      ‖Real.exp (F a)‖ ≤ Real.exp (|theta| * (N : ℝ) * B) := by
    filter_upwards [hsumBound] with a ha
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    dsimp [F]
    calc
      theta * Shao.prefixSum a N ≤ |theta * Shao.prefixSum a N| := le_abs_self _
      _ = |theta| * |Shao.prefixSum a N| := abs_mul _ _
      _ ≤ |theta| * ((N : ℝ) * B) :=
        mul_le_mul_of_nonneg_left ha (abs_nonneg theta)
      _ = |theta| * (N : ℝ) * B := by ring
  have hw : Integrable (fun a => g a * Real.exp (F a)) P :=
    hg.mul_bdd hF.exp.aestronglyMeasurable hBound
  have hgTilted : Integrable g (P.tilted F) :=
    (integrable_tilted_iff hExpF g).2
      (by simpa only [smul_eq_mul, mul_comm] using hw)
  have hgPtilt : Integrable g Ptilt := by rw [hpi]; exact hgTilted
  refine ⟨hgPtilt, hw, ?_⟩
  have hI : (∫ a, g a ∂Ptilt) = (∫ a, g a * Real.exp (F a) ∂P) / c ^ N := by
    rw [hpi, integral_tilted]
    simp only [smul_eq_mul]
    calc
      (∫ a, Real.exp (F a) / (∫ v, Real.exp (F v) ∂P) * g a ∂P) =
          ∫ a, (g a * Real.exp (F a)) / (∫ v, Real.exp (F v) ∂P) ∂P :=
        integral_congr_ae (ae_of_all _ fun a => by ring)
      _ = (∫ a, g a * Real.exp (F a) ∂P) / (∫ v, Real.exp (F v) ∂P) :=
        integral_div _ _
      _ = _ := by rw [hZ]
  have hcpow : c ^ N ≠ 0 := pow_ne_zero N hc.ne'
  have hI' := (eq_div_iff hcpow).mp hI
  simpa only [mul_comm] using hI'.symm

private theorem cwm_tilt_future_negative_maximum :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (B : ℝ), 0 < B → (∀ᵐ z : ℝ ∂rho, |z| ≤ B) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ theta : ℝ, 0 < theta → theta * B ≤ 1 / 10 →
          let nu : Measure ℝ := rho.tilted (fun z => theta * z)
          ∀ N : ℕ,
            let Ptilt : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => nu)
            Integrable
              (fun a : Shao.Path N => Real.exp (2 * theta * Shao.maxWithZero (-a)))
              Ptilt ∧
              (∫ a : Shao.Path N,
                Real.exp (2 * theta * Shao.maxWithZero (-a)) ∂Ptilt) ≤
                C * Real.exp ((2001 / 2000000 : ℝ) * (N : ℝ) * theta ^ 2 +
                  C * (N : ℝ) * theta ^ 3 * beta) := by
  classical
  rcases cwm_log_mgf_taylor with ⟨K, hK, hTaylor⟩
  let C : ℝ := 2001 + 4 * K
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro rho hprob B hB hs hmean hsecond beta theta ht htB nu N Ptilt
  let c : ℝ → ℝ := fun t => ∫ z : ℝ, Real.exp (t * z) ∂rho
  have hb : 0 ≤ beta := integral_nonneg (fun z => pow_nonneg (abs_nonneg z) 3)
  have hT := hTaylor rho B hB hs hmean hsecond theta (by
    rw [abs_of_pos ht]
    linarith)
  have hL := hTaylor rho B hB hs hmean hsecond
    (-(1001 / 1000 : ℝ) * theta) (by
      rw [abs_of_neg (by nlinarith only [ht] : -(1001 / 1000 : ℝ) * theta < 0)]
      nlinarith only [htB])
  have hcT : 0 < c theta := lt_of_lt_of_le zero_lt_one hT.2.1
  have hcL : 0 < c (-(1001 / 1000 : ℝ) * theta) :=
    lt_of_lt_of_le zero_lt_one hL.2.1
  have hNuData := boundedQuadraticTilt_density_moments rho B theta 0 hB (le_refl 0) hs
  have hNu : IsProbabilityMeasure nu := by
    simpa only [zero_mul, sub_zero] using hNuData.2.2.2.2.2.2.1
  letI : IsProbabilityMeasure nu := hNu
  have hsNu : ∀ᵐ z : ℝ ∂nu, |z| ≤ B := by
    simpa only [zero_mul, sub_zero] using hNuData.2.2.2.2.2.2.2.2.2.1
  clear hNuData
  let mu : Measure ℝ := nu.map (fun z : ℝ => -z)
  have hm : Measurable (fun z : ℝ => -z) := measurable_neg
  letI : IsProbabilityMeasure mu :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  have hsMu : ∀ᵐ z : ℝ ∂mu, |z| ≤ B := by
    apply (ae_map_iff hm.aemeasurable (measurableSet_le (continuous_abs.measurable : Measurable (fun z : ℝ => |z|)) measurable_const)).2
    simpa only [abs_neg] using hsNu
  let q : ℝ := (2001 / 1000 : ℝ) * theta
  let cn : ℝ := ∫ z : ℝ, Real.exp (q * z) ∂mu
  have hcn : cn = c (-(1001 / 1000 : ℝ) * theta) / c theta := by
    dsimp only [cn, mu]
    rw [integral_map hm.aemeasurable (by fun_prop)]
    change (∫ z : ℝ, Real.exp (q * -z) ∂rho.tilted (fun z => theta * z)) = _
    rw [integral_exp_tilted]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun z => by
      congr 1
      dsimp [q]
      ring
  have hlog : Real.log cn ≤ (2001 / 2000000 : ℝ) * theta ^ 2 +
      4 * K * theta ^ 3 * beta := by
    rw [hcn, Real.log_div hcL.ne' hcT.ne']
    have h1 := (abs_le.mp hL.2.2).2
    have h2 := (abs_le.mp hT.2.2).1
    rw [abs_of_pos ht] at h2
    rw [abs_of_neg (by nlinarith only [ht] : -(1001 / 1000 : ℝ) * theta < 0)] at h1
    nlinarith only [h1, h2, mul_nonneg (by linarith : 0 ≤ K) (mul_nonneg (pow_nonneg ht.le 3) hb)]
  have hupper : 0 ≤ (2001 / 2000000 : ℝ) * theta ^ 2 +
      4 * K * theta ^ 3 * beta := by positivity
  have hlogmax : max (Real.log cn) 0 ≤ (2001 / 2000000 : ℝ) * theta ^ 2 +
      4 * K * theta ^ 3 * beta := max_le hlog hupper
  let Pm : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => mu)
  have hMax := cwm_finite_exponential_maximum mu B q (2 * theta) hB hsMu
    (by positivity) (by dsimp [q]; nlinarith) N
  have hMap : Ptilt.map (fun a : Shao.Path N => -a) = Pm :=
    Measure.pi_map_pi (fun _ : Fin N => hm.aemeasurable)
  have hPathM : Measurable (fun a : Shao.Path N => -a) := by fun_prop
  have hExpM : Measurable (fun a : Shao.Path N =>
      Real.exp (2 * theta * Shao.maxWithZero a)) :=
    (measurable_const.mul Shao.measurable_maxWithZero).exp
  have hInt : Integrable (fun a : Shao.Path N =>
      Real.exp (2 * theta * Shao.maxWithZero (-a))) Ptilt := by
    have hh : Integrable (fun a : Shao.Path N =>
        Real.exp (2 * theta * Shao.maxWithZero a))
        (Ptilt.map (fun a : Shao.Path N => -a)) := by rw [hMap]; exact hMax.1
    exact (integrable_map_measure hExpM.aestronglyMeasurable hPathM.aemeasurable).1 hh
  refine ⟨hInt, ?_⟩
  have hEq : (∫ a : Shao.Path N,
      Real.exp (2 * theta * Shao.maxWithZero (-a)) ∂Ptilt) =
      ∫ a : Shao.Path N, Real.exp (2 * theta * Shao.maxWithZero a) ∂Pm := by
    rw [← hMap, integral_map hPathM.aemeasurable hExpM.aestronglyMeasurable]
  rw [hEq]
  have hRatio : 2 * theta / (q - 2 * theta) = 2000 := by
    dsimp only [q]
    field_simp [ht.ne']
    <;> ring
  have hMaxBound : (∫ a : Shao.Path N,
      Real.exp (2 * theta * Shao.maxWithZero a) ∂Pm) ≤
      1 + 2000 * Real.exp ((N : ℝ) * max (Real.log cn) 0) := by
    simpa only [hRatio] using hMax.2
  have hEx : Real.exp ((N : ℝ) * max (Real.log cn) 0) ≤
      Real.exp ((2001 / 2000000 : ℝ) * (N : ℝ) * theta ^ 2 +
        C * (N : ℝ) * theta ^ 3 * beta) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hlogmax (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    dsimp [C]
    nlinarith only [hh, mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
      (mul_nonneg (pow_nonneg ht.le 3) hb)]
  have hOne : 1 ≤ Real.exp ((2001 / 2000000 : ℝ) * (N : ℝ) * theta ^ 2 +
      C * (N : ℝ) * theta ^ 3 * beta) :=
    Real.one_le_exp_iff.mpr (by dsimp [C]; positivity)
  have hC : 2001 ≤ C := by dsimp [C]; linarith
  nlinarith only [hMaxBound, hEx, hOne, mul_le_mul_of_nonneg_right hC (Real.exp_pos
    ((2001 / 2000000 : ℝ) * (N : ℝ) * theta ^ 2 +
      C * (N : ℝ) * theta ^ 3 * beta)).le]

private theorem cwm_tilt_short_block_range :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (B : ℝ), 0 < B → (∀ᵐ z : ℝ ∂rho, |z| ≤ B) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ theta : ℝ, 0 < theta → theta * B ≤ 1 / 10 →
          let nu : Measure ℝ := rho.tilted (fun z => theta * z)
          ∀ N : ℕ, (N : ℝ) * theta ^ 2 ≤ 101 / 100 →
            let Ptilt : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => nu)
            let range : Shao.Path N → ℝ := fun a =>
              Shao.maxWithZero a + Shao.maxWithZero (-a)
            Integrable (fun a : Shao.Path N => Real.exp (2 * theta * range a)) Ptilt ∧
              (∫ a : Shao.Path N, Real.exp (2 * theta * range a) ∂Ptilt) ≤ C := by
  classical
  rcases cwm_log_mgf_taylor with ⟨K, hK, hTaylor⟩
  let E : ℝ := Real.exp (100 + 1000 * K)
  let C : ℝ := 1 + 4 * E
  refine ⟨C, by dsimp [C]; have he : 0 < E := Real.exp_pos _; linarith only [he], ?_⟩
  intro rho hprob B hB hs hmean hsecond beta theta ht htB nu N hN Ptilt range
  let c : ℝ → ℝ := fun t => ∫ z : ℝ, Real.exp (t * z) ∂rho
  have hb : 0 ≤ beta := integral_nonneg (fun z => pow_nonneg (abs_nonneg z) 3)
  have hBase := boundedQuadraticTilt_density_moments rho B theta 0 hB (le_refl 0) hs
  have hNu : IsProbabilityMeasure nu := by
    simpa only [zero_mul, sub_zero] using hBase.2.2.2.2.2.2.1
  letI : IsProbabilityMeasure nu := hNu
  have hsNu : ∀ᵐ z : ℝ ∂nu, |z| ≤ B := by
    simpa only [zero_mul, sub_zero] using hBase.2.2.2.2.2.2.2.2.2.1
  have hPows := hBase.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h2 : Integrable (fun z : ℝ => z ^ 2) rho := (hPows 2).1
  have h3 : Integrable (fun z : ℝ => |z| ^ 3) rho := (hPows 3).2.2.1
  clear hBase hPows
  have hbB : beta ≤ B := by
    have hpoint : ∀ᵐ z : ℝ ∂rho, |z| ^ 3 ≤ B * z ^ 2 := by
      filter_upwards [hs] with z hz
      calc
        |z| ^ 3 = |z| * z ^ 2 := by rw [← sq_abs z]; ring
        _ ≤ B * z ^ 2 := mul_le_mul_of_nonneg_right hz (sq_nonneg z)
    have hh := integral_mono_ae h3 (h2.const_mul B) hpoint
    simpa only [integral_const_mul, hsecond, mul_one] using hh
  have htBeta : theta * beta ≤ 1 / 10 :=
    (mul_le_mul_of_nonneg_left hbB ht.le).trans htB
  have hT := hTaylor rho B hB hs hmean hsecond theta (by
    rw [abs_of_pos ht]; linarith only [htB])
  have hcT : 0 < c theta := lt_of_lt_of_le zero_lt_one hT.2.1
  have hMoment (sgn : ℝ) (hsign : sgn = 1 ∨ sgn = -1) :
      Integrable (fun a : Shao.Path N =>
        Real.exp (4 * theta * Shao.maxWithZero (sgn • a))) Ptilt ∧
        (∫ a : Shao.Path N,
          Real.exp (4 * theta * Shao.maxWithZero (sgn • a)) ∂Ptilt) ≤ C := by
    have habs : |sgn| = 1 := by rcases hsign with rfl | rfl <;> norm_num
    let mu : Measure ℝ := nu.map (fun z => sgn * z)
    have hm : Measurable (fun z : ℝ => sgn * z) := by fun_prop
    letI : IsProbabilityMeasure mu :=
      (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
    have hsMu : ∀ᵐ z : ℝ ∂mu, |z| ≤ B := by
      apply (ae_map_iff hm.aemeasurable
        (measurableSet_le (continuous_abs.measurable : Measurable (fun z : ℝ => |z|)) measurable_const)).2
      simpa only [abs_mul, habs, one_mul] using hsNu
    let t : ℝ := theta + sgn * (5 * theta)
    have hlegal : |t| * B ≤ 3 / 5 := by
      rcases hsign with rfl | rfl
      · have heq : t = 6 * theta := by dsimp [t]; ring
        rw [heq, abs_of_pos (by positivity)]
        nlinarith only [htB]
      · have heq : t = -(4 * theta) := by dsimp [t]; ring
        rw [heq, abs_neg, abs_of_pos (by positivity)]
        nlinarith only [htB]
    have hL := hTaylor rho B hB hs hmean hsecond t hlegal
    have hcL : 0 < c t := lt_of_lt_of_le zero_lt_one hL.2.1
    let cn : ℝ := ∫ z : ℝ, Real.exp ((5 * theta) * z) ∂mu
    have hcn : cn = c t / c theta := by
      dsimp only [cn, mu]
      rw [integral_map hm.aemeasurable (by fun_prop)]
      change (∫ z : ℝ, Real.exp ((5 * theta) * (sgn * z))
        ∂rho.tilted (fun z => theta * z)) = _
      rw [integral_exp_tilted]
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ fun z => by congr 1; dsimp [t]; ring
    have hlog : Real.log cn ≤ 18 * theta ^ 2 + 217 * K * theta ^ 3 * beta := by
      rw [hcn, Real.log_div hcL.ne' hcT.ne']
      have h1 := (abs_le.mp hL.2.2).2
      have h2' := (abs_le.mp hT.2.2).1
      rw [abs_of_pos ht] at h2'
      have hn : 0 ≤ K * theta ^ 3 * beta := by positivity
      rcases hsign with hsign | hsign
      · have heq : t = 6 * theta := by dsimp [t]; rw [hsign]; ring
        rw [heq, abs_of_pos (by positivity)] at h1
        rw [heq]
        dsimp only [c, beta] at h1 h2' hn ⊢
        nlinarith only [h1, h2', hn, sq_nonneg theta]
      · have heq : t = -(4 * theta) := by dsimp [t]; rw [hsign]; ring
        rw [heq, abs_neg, abs_of_pos (by positivity)] at h1
        rw [heq]
        dsimp only [c, beta] at h1 h2' hn ⊢
        nlinarith only [h1, h2', hn, sq_nonneg theta]
    have hlogmax : max (Real.log cn) 0 ≤
        18 * theta ^ 2 + 217 * K * theta ^ 3 * beta := by
      exact max_le hlog (by positivity)
    have hNlog : (N : ℝ) * max (Real.log cn) 0 ≤ 100 + 1000 * K := by
      have hmul := mul_le_mul_of_nonneg_left htBeta
        (by positivity : 0 ≤ 217 * K * theta ^ 2)
      have hpoint : 18 * theta ^ 2 + 217 * K * theta ^ 3 * beta ≤
          (18 + 217 / 10 * K) * theta ^ 2 := by nlinarith only [hmul]
      have hfirst := mul_le_mul_of_nonneg_left (hlogmax.trans hpoint)
        (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
      have hlast := mul_le_mul_of_nonneg_left hN
        (by positivity : 0 ≤ 18 + 217 / 10 * K)
      nlinarith only [hfirst, hlast, hK]
    let Pm : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => mu)
    have hMax := cwm_finite_exponential_maximum mu B (5 * theta) (4 * theta)
      hB hsMu (by positivity) (by linarith only [ht]) N
    have hMap : Ptilt.map (fun a : Shao.Path N => sgn • a) = Pm :=
      Measure.pi_map_pi (fun _ : Fin N => hm.aemeasurable)
    have hPathM : Measurable (fun a : Shao.Path N => sgn • a) := by fun_prop
    have hExpM : Measurable (fun a : Shao.Path N =>
        Real.exp (4 * theta * Shao.maxWithZero a)) :=
      (measurable_const.mul Shao.measurable_maxWithZero).exp
    have hInt : Integrable (fun a : Shao.Path N =>
        Real.exp (4 * theta * Shao.maxWithZero (sgn • a))) Ptilt := by
      have hh : Integrable (fun a : Shao.Path N =>
          Real.exp (4 * theta * Shao.maxWithZero a))
          (Ptilt.map (fun a : Shao.Path N => sgn • a)) := by rw [hMap]; exact hMax.1
      exact (integrable_map_measure hExpM.aestronglyMeasurable hPathM.aemeasurable).1 hh
    refine ⟨hInt, ?_⟩
    have hEq : (∫ a : Shao.Path N,
        Real.exp (4 * theta * Shao.maxWithZero (sgn • a)) ∂Ptilt) =
        ∫ a : Shao.Path N, Real.exp (4 * theta * Shao.maxWithZero a) ∂Pm := by
      rw [← hMap, integral_map hPathM.aemeasurable hExpM.aestronglyMeasurable]
    rw [hEq]
    have hratio : 4 * theta / (5 * theta - 4 * theta) = 4 := by
      field_simp [ht.ne']
      <;> ring
    have hh : (∫ a : Shao.Path N,
        Real.exp (4 * theta * Shao.maxWithZero a) ∂Pm) ≤
        1 + 4 * Real.exp ((N : ℝ) * max (Real.log cn) 0) := by
      simpa only [hratio] using hMax.2
    have hE : Real.exp ((N : ℝ) * max (Real.log cn) 0) ≤ E :=
      Real.exp_le_exp.mpr hNlog
    dsimp only [C]
    linarith only [hh, hE]
  have hpos := hMoment 1 (Or.inl rfl)
  have hneg := hMoment (-1) (Or.inr rfl)
  simp only [one_smul] at hpos
  simp only [neg_one_smul] at hneg
  let f : Shao.Path N → ℝ := fun a => Real.exp (4 * theta * Shao.maxWithZero a)
  let g : Shao.Path N → ℝ := fun a => Real.exp (4 * theta * Shao.maxWithZero (-a))
  have hYoung (a : Shao.Path N) : Real.exp (2 * theta * range a) ≤ (f a + g a) / 2 := by
    have hmul : Real.exp (2 * theta * range a) =
        Real.exp (2 * theta * Shao.maxWithZero a) *
          Real.exp (2 * theta * Shao.maxWithZero (-a)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [range]
      ring
    have hf : Real.exp (2 * theta * Shao.maxWithZero a) ^ 2 = f a := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hg : Real.exp (2 * theta * Shao.maxWithZero (-a)) ^ 2 = g a := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hh := sq_nonneg (Real.exp (2 * theta * Shao.maxWithZero a) -
      Real.exp (2 * theta * Shao.maxWithZero (-a)))
    nlinarith only [hmul, hf, hg, hh]
  have hSumI : Integrable (fun a => (f a + g a) / 2) Ptilt :=
    (hpos.1.add hneg.1).div_const 2
  have hInt : Integrable (fun a : Shao.Path N => Real.exp (2 * theta * range a)) Ptilt := by
    have hm : Measurable range :=
      Shao.measurable_maxWithZero.add
        (Shao.measurable_maxWithZero.comp (by fun_prop))
    apply hSumI.mono' ((measurable_const.mul hm).exp.aestronglyMeasurable)
    exact ae_of_all _ fun a => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hYoung a
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∫ a, (f a + g a) / 2 ∂Ptilt := integral_mono hInt hSumI hYoung
    _ = ((∫ a, f a ∂Ptilt) + (∫ a, g a ∂Ptilt)) / 2 := by
      rw [integral_div, integral_add hpos.1 hneg.1]
    _ ≤ C := by linarith only [hpos.2, hneg.2]

private theorem cwm_drawdown_block_pointwise
    (N m : ℕ) (hN : 0 < N) (hm : 0 < m) (theta : ℝ) (htheta : 0 ≤ theta) :
  let R : Shao.Path N → ℝ := fun a =>
    sSup {w : ℝ | ∃ u v : Fin (N + 1), u.val ≤ v.val ∧
      w = Shao.prefixSum a u.val - Shao.prefixSum a v.val}
  let count : ℕ := (N + m - 1) / m
  let start : Fin count → ℕ := fun i => i.val * m
  let stop : Fin count → ℕ := fun i => min ((i.val + 1) * m) N
  let localRange : Fin count → Shao.Path N → ℝ := fun i a =>
    sSup {w : ℝ | ∃ u v : Fin (N + 1),
      start i ≤ u.val ∧ u.val ≤ stop i ∧
      start i ≤ v.val ∧ v.val ≤ stop i ∧
      w = Shao.prefixSum a u.val - Shao.prefixSum a v.val}
  let future : Fin count → Shao.Path N → ℝ := fun i a =>
    sSup {w : ℝ | ∃ v : Fin (N + 1), stop i ≤ v.val ∧
      w = Shao.prefixSum a (stop i) - Shao.prefixSum a v.val}
  ∀ a : Shao.Path N,
    Real.exp (2 * theta * R a) ≤
      ∑ i : Fin count,
        Real.exp (2 * theta * localRange i a) *
          Real.exp (2 * theta * future i a) := by
  classical
  intro R count start stop localRange future a
  have hRfin : Set.Finite {w : ℝ | ∃ u v : Fin (N + 1), u.val ≤ v.val ∧
      w = Shao.prefixSum a u.val - Shao.prefixSum a v.val} := by
    apply (Set.finite_range (fun uv : Fin (N + 1) × Fin (N + 1) =>
      Shao.prefixSum a uv.1.val - Shao.prefixSum a uv.2.val)).subset
    rintro w ⟨u, v, _, hw⟩
    exact ⟨(u, v), hw.symm⟩
  have hRne : Set.Nonempty {w : ℝ | ∃ u v : Fin (N + 1), u.val ≤ v.val ∧
      w = Shao.prefixSum a u.val - Shao.prefixSum a v.val} := by
    exact ⟨0, 0, 0, le_rfl, by simp⟩
  have hRmem := hRne.csSup_mem hRfin
  rcases hRmem with ⟨u, v, huv, hrval⟩
  change R a = Shao.prefixSum a u.val - Shao.prefixSum a v.val at hrval
  have hceil : N ≤ count * m := by
    have he := Nat.mod_add_div (N + m - 1) m
    have hr := Nat.mod_lt (N + m - 1) hm
    rw [Nat.mul_comm m] at he
    dsimp [count]
    omega
  let u0 : ℕ := min u.val (N - 1)
  let q : ℕ := u0 / m
  have hqmul : q * m ≤ u0 := Nat.div_mul_le_self _ _
  have hu0N : u0 < N := by dsimp [u0]; omega
  have hq : q < count := by
    by_contra h
    have hmul := Nat.mul_le_mul_right m (Nat.le_of_not_gt h)
    omega
  let i : Fin count := ⟨q, hq⟩
  have hnext : u0 < (q + 1) * m := by
    have he := Nat.mod_add_div u0 m
    have hr := Nat.mod_lt u0 hm
    rw [Nat.mul_comm m] at he
    dsimp [q]
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hstartu : start i ≤ u.val := by
    change q * m ≤ u.val
    exact hqmul.trans (Nat.min_le_left _ _)
  have hstopN : stop i ≤ N := Nat.min_le_right _ _
  have hustop : u.val ≤ stop i := by
    change u.val ≤ min ((q + 1) * m) N
    apply le_min
    · have hugap : u.val ≤ u0 + 1 := by dsimp [u0]; omega
      omega
    · exact Nat.le_of_lt_succ u.is_lt
  have hstartstop : start i ≤ stop i := hstartu.trans hustop
  let z : Fin (N + 1) := ⟨stop i, by omega⟩
  have hLocalBdd (j : Fin count) : BddAbove {w : ℝ |
      ∃ u v : Fin (N + 1),
        start j ≤ u.val ∧ u.val ≤ stop j ∧
        start j ≤ v.val ∧ v.val ≤ stop j ∧
        w = Shao.prefixSum a u.val - Shao.prefixSum a v.val} := by
    have hfin : Set.Finite {w : ℝ | ∃ u v : Fin (N + 1),
        start j ≤ u.val ∧ u.val ≤ stop j ∧
        start j ≤ v.val ∧ v.val ≤ stop j ∧
        w = Shao.prefixSum a u.val - Shao.prefixSum a v.val} := by
      apply (Set.finite_range (fun uv : Fin (N + 1) × Fin (N + 1) =>
        Shao.prefixSum a uv.1.val - Shao.prefixSum a uv.2.val)).subset
      rintro w ⟨u, v, _, _, _, _, hw⟩
      exact ⟨(u, v), hw.symm⟩
    exact hfin.bddAbove
  have hFutureBdd (j : Fin count) : BddAbove {w : ℝ |
      ∃ v : Fin (N + 1), stop j ≤ v.val ∧
        w = Shao.prefixSum a (stop j) - Shao.prefixSum a v.val} := by
    have hfin : Set.Finite {w : ℝ | ∃ v : Fin (N + 1), stop j ≤ v.val ∧
        w = Shao.prefixSum a (stop j) - Shao.prefixSum a v.val} := by
      apply (Set.finite_range (fun v : Fin (N + 1) =>
        Shao.prefixSum a (stop j) - Shao.prefixSum a v.val)).subset
      rintro w ⟨v, _, hw⟩
      exact ⟨v, hw.symm⟩
    exact hfin.bddAbove
  have hfuture0 : 0 ≤ future i a := by
    apply le_csSup (hFutureBdd i)
    exact ⟨z, le_rfl, by simp [z]⟩
  have hbound : R a ≤ localRange i a + future i a := by
    by_cases hv : v.val ≤ stop i
    · have hl : Shao.prefixSum a u.val - Shao.prefixSum a v.val ≤ localRange i a := by
        apply le_csSup (hLocalBdd i)
        exact ⟨u, v, hstartu, hustop, hstartu.trans huv, hv, rfl⟩
      linarith
    · have hstopv : stop i ≤ v.val := Nat.le_of_not_ge hv
      have hl : Shao.prefixSum a u.val - Shao.prefixSum a (stop i) ≤ localRange i a := by
        apply le_csSup (hLocalBdd i)
        exact ⟨u, z, hstartu, hustop, hstartstop, le_rfl, rfl⟩
      have hf : Shao.prefixSum a (stop i) - Shao.prefixSum a v.val ≤ future i a := by
        apply le_csSup (hFutureBdd i)
        exact ⟨v, hstopv, rfl⟩
      linarith
  calc
    Real.exp (2 * theta * R a) ≤
        Real.exp (2 * theta * (localRange i a + future i a)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbound (by positivity))
    _ = Real.exp (2 * theta * localRange i a) *
        Real.exp (2 * theta * future i a) := by rw [mul_add, Real.exp_add]
    _ ≤ ∑ j : Fin count,
        Real.exp (2 * theta * localRange j a) * Real.exp (2 * theta * future j a) :=
      Finset.single_le_sum
        (f := fun j : Fin count =>
          Real.exp (2 * theta * localRange j a) * Real.exp (2 * theta * future j a))
        (fun j _ => mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
        (Finset.mem_univ i)

private theorem cwm_iid_adjacent_windows
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (N lo mid : ℕ) (hlo : lo ≤ mid) (hmid : mid ≤ N) :
    let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => nu)
    let W1 : Shao.Path N → Shao.Path (mid - lo) := fun a j =>
      a ⟨lo + j.val, by have hj := j.isLt; omega⟩
    let W2 : Shao.Path N → Shao.Path (N - mid) := fun a j =>
      a ⟨mid + j.val, by have hj := j.isLt; omega⟩
    P.map W1 = Measure.pi (fun _ : Fin (mid - lo) => nu) ∧
      P.map W2 = Measure.pi (fun _ : Fin (N - mid) => nu) ∧
      IndepFun W1 W2 P ∧
      ∀ a : Shao.Path N,
        (∀ k : ℕ, k ≤ mid - lo →
          Shao.prefixSum (W1 a) k =
            Shao.prefixSum a (lo + k) - Shao.prefixSum a lo) ∧
        (∀ k : ℕ, k ≤ N - mid →
          Shao.prefixSum (W2 a) k =
            Shao.prefixSum a (mid + k) - Shao.prefixSum a mid) := by
  classical
  intro P W1 W2
  have hcoord : iIndepFun (fun j : Fin N => fun a : Shao.Path N => a j) P :=
    iIndepFun_pi (fun _ : Fin N => measurable_id.aemeasurable)
  have hWindowMap (b l : ℕ) (hbl : b + l ≤ N) :
      P.map (fun a : Shao.Path N => fun j : Fin l =>
        a ⟨b + j.val, by have hj := j.isLt; omega⟩) =
        Measure.pi (fun _ : Fin l => nu) := by
    let e : Fin l → Fin N := fun j => ⟨b + j.val, by have hj := j.isLt; omega⟩
    have he : Function.Injective e := by
      intro j k h
      apply Fin.ext
      have hh := congrArg Fin.val h
      dsimp only [e] at hh
      omega
    have hind : iIndepFun (fun j : Fin l => fun a : Shao.Path N => a (e j)) P :=
      iIndepFun.precomp he hcoord
    have hmap := iIndepFun.map_fun_eq_pi_map
      (fun j : Fin l => (measurable_pi_apply (e j)).aemeasurable) hind
    have heval (j : Fin l) : P.map (fun a : Shao.Path N => a (e j)) = nu :=
      (measurePreserving_eval (fun _ : Fin N => nu) (e j)).map_eq
    simpa only [heval] using hmap
  have hPrefix (b l : ℕ) (hbl : b + l ≤ N) (a : Shao.Path N)
      (k : ℕ) (hk : k ≤ l) :
      Shao.prefixSum (fun j : Fin l =>
        a ⟨b + j.val, by have hj := j.isLt; omega⟩) k =
        Shao.prefixSum a (b + k) - Shao.prefixSum a b := by
    have hdiff : Shao.prefixSum a (b + k) - Shao.prefixSum a b =
        ∑ j ∈ Finset.univ.filter (fun j : Fin N => b ≤ j.val ∧ j.val < b + k), a j := by
      simp only [Shao.prefixSum, Finset.sum_filter]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hb : j.val < b
      · have hb' : j.val < b + k := by omega
        simp [hb, hb', Nat.not_le_of_gt hb]
      · have hb' : b ≤ j.val := by omega
        by_cases htop : j.val < b + k <;> simp [hb, hb', htop]
    rw [hdiff]
    unfold Shao.prefixSum
    refine Finset.sum_bij (fun j _ =>
      (⟨b + j.val, by have hj := j.isLt; omega⟩ : Fin N)) ?_ ?_ ?_ ?_
    · intro j hj
      have hjk := (Finset.mem_filter.mp hj).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      dsimp only
      constructor <;> omega
    · intro j hj k' hk' heq
      apply Fin.ext
      have hh := congrArg Fin.val heq
      dsimp only at hh
      omega
    · intro j hj
      have hb := (Finset.mem_filter.mp hj).2
      have hrel : j.val - b < l := by omega
      refine ⟨⟨j.val - b, hrel⟩, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        dsimp only
        omega
      · apply Fin.ext
        dsimp only
        omega
    · intro j hj
      rfl
  refine ⟨hWindowMap lo (mid - lo) (by omega),
    hWindowMap mid (N - mid) (by omega), ?_, ?_⟩
  · let U : Set (Fin N) := {j | lo ≤ j.val ∧ j.val < mid}
    let V : Set (Fin N) := {j | mid ≤ j.val}
    have hdis : Disjoint U V := by
      apply Set.disjoint_left.mpr
      intro j hu hv
      exact (not_lt_of_ge hv) hu.2
    have hind := hcoord.indepFun_set U V hdis (fun j => measurable_pi_apply j)
    let F : (U → ℝ) → Shao.Path (mid - lo) := fun a j =>
      a ⟨⟨lo + j.val, by have hj := j.isLt; omega⟩, by
        change lo ≤ lo + j.val ∧ lo + j.val < mid
        have hj := j.isLt
        constructor <;> omega⟩
    let G : (V → ℝ) → Shao.Path (N - mid) := fun a j =>
      a ⟨⟨mid + j.val, by have hj := j.isLt; omega⟩, by
        change mid ≤ mid + j.val
        omega⟩
    have hF : Measurable F := by
      exact Measurable.of_eval (fun j => measurable_pi_apply _)
    have hG : Measurable G := by
      exact Measurable.of_eval (fun j => measurable_pi_apply _)
    exact hind.comp hF hG
  · intro a
    exact ⟨fun k hk => hPrefix lo (mid - lo) (by omega) a k hk,
      fun k hk => hPrefix mid (N - mid) (by omega) a k hk⟩

private theorem cwm_tilt_drawdown_moment :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (B : ℝ), 0 < B → (∀ᵐ z : ℝ ∂rho, |z| ≤ B) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ theta : ℝ, 0 < theta → theta * B ≤ 1 / 10 →
          let nu : Measure ℝ := rho.tilted (fun z => theta * z)
          ∀ N : ℕ,
            let Ptilt : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => nu)
            let R : Shao.Path N → ℝ := fun a =>
              sSup {w : ℝ | ∃ u v : Fin (N + 1), u.val ≤ v.val ∧
                w = Shao.prefixSum a u.val - Shao.prefixSum a v.val}
            Integrable (fun a : Shao.Path N => Real.exp (2 * theta * R a)) Ptilt ∧
              (∫ a : Shao.Path N, Real.exp (2 * theta * R a) ∂Ptilt) ≤
                C * (1 + (N : ℝ) * theta ^ 2) *
                  Real.exp ((2001 / 2000000 : ℝ) * (N : ℝ) * theta ^ 2 +
                    C * (N : ℝ) * theta ^ 3 * beta) := by
  classical
  rcases cwm_tilt_future_negative_maximum with ⟨CF, hCF, hFuture⟩
  rcases cwm_tilt_short_block_range with ⟨CS, hCS, hShort⟩
  let C : ℝ := 1 + CS * CF
  have hC : 1 ≤ C := by dsimp [C]; nlinarith only [hCS, hCF]
  refine ⟨C, hC, ?_⟩
  intro rho hprob B hB hs hmean hsecond beta theta ht htB nu N Ptilt R
  have hb : 0 ≤ beta := integral_nonneg (fun z => pow_nonneg (abs_nonneg z) 3)
  have hBase := boundedQuadraticTilt_density_moments rho B theta 0 hB (le_refl 0) hs
  have hNu : IsProbabilityMeasure nu := by
    simpa only [zero_mul, sub_zero] using hBase.2.2.2.2.2.2.1
  letI : IsProbabilityMeasure nu := hNu
  have hsNu : ∀ᵐ z : ℝ ∂nu, |z| ≤ B := by
    simpa only [zero_mul, sub_zero] using hBase.2.2.2.2.2.2.2.2.2.1
  have hPows := hBase.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h2 : Integrable (fun z : ℝ => z ^ 2) rho := (hPows 2).1
  have h3 : Integrable (fun z : ℝ => |z| ^ 3) rho := (hPows 3).2.2.1
  clear hBase hPows
  have hb1 : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one
      rho h2 h3 hsecond
  have hbB : beta ≤ B := by
    have hh : ∀ᵐ z : ℝ ∂rho, |z| ^ 3 ≤ B * z ^ 2 := by
      filter_upwards [hs] with z hz
      calc
        |z| ^ 3 = |z| * z ^ 2 := by rw [← sq_abs z]; ring
        _ ≤ B * z ^ 2 := mul_le_mul_of_nonneg_right hz (sq_nonneg z)
    have hh' := integral_mono_ae h3 (h2.const_mul B) hh
    simpa only [integral_const_mul, hsecond, mul_one] using hh'
  have hB1 : 1 ≤ B := hb1.trans hbB
  have htSmall : theta ≤ 1 / 10 := by nlinarith only [hB1, htB, ht]
  rcases cwm_path_extrema_geometry N with ⟨_, _, hRm, hGeom⟩
  have hsP : ∀ᵐ a : Shao.Path N ∂Ptilt, ∀ i : Fin N, |a i| ≤ B := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin N => nu) (i := i)).eventually hsNu
  have hInt : Integrable (fun a : Shao.Path N => Real.exp (2 * theta * R a)) Ptilt := by
    apply (integrable_const (Real.exp (2 * theta * (N : ℝ) * B))).mono'
      ((measurable_const.mul hRm).exp.aestronglyMeasurable)
    filter_upwards [hsP] with a ha
    rcases hGeom a with ⟨_, _, _, _, hRn, hRu, _, _⟩
    have hu : R a ≤ (N : ℝ) * B := hRu.trans (by
      calc
        (∑ i : Fin N, |a i|) ≤ ∑ _i : Fin N, B :=
          Finset.sum_le_sum (fun i hi => ha i)
        _ = (N : ℝ) * B := by simp)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    change 2 * theta * R a ≤ 2 * theta * (N : ℝ) * B
    nlinarith only [hu, ht]
  refine ⟨hInt, ?_⟩
  by_cases hN : 0 < N
  swap
  · have hN0 : N = 0 := by omega
    have hR0 (a : Shao.Path N) : R a = 0 := by
      rcases hGeom a with ⟨_, _, _, _, hn, hu, _, _⟩
      change R a ≤ ∑ i : Fin N, |a i| at hu
      change 0 ≤ R a at hn
      have hsum0 : (∑ i : Fin N, |a i|) = 0 := by
        letI : IsEmpty (Fin N) := ⟨fun i => by have hi := i.isLt; omega⟩
        simp
      rw [hsum0] at hu
      exact le_antisymm hu hn
    simp_rw [hR0, mul_zero, Real.exp_zero]
    simpa [hN0] using hC
  let m : ℕ := ⌈1 / theta ^ 2⌉₊
  have hm : 0 < m := Nat.ceil_pos.mpr (by positivity)
  have hmLower : 1 ≤ (m : ℝ) * theta ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right (Nat.le_ceil (1 / theta ^ 2)) (sq_nonneg theta)
    simpa only [div_mul_cancel₀ _ (pow_ne_zero 2 ht.ne')] using hh
  have hmUpper : (m : ℝ) * theta ^ 2 ≤ 101 / 100 := by
    have hh := mul_le_mul_of_nonneg_right
      (Nat.ceil_lt_add_one (by positivity : 0 ≤ 1 / theta ^ 2)).le (sq_nonneg theta)
    have hcancel : (1 / theta ^ 2) * theta ^ 2 = 1 :=
      div_mul_cancel₀ _ (pow_ne_zero 2 ht.ne')
    nlinarith only [hh, hcancel, htSmall, ht]
  let count : ℕ := (N + m - 1) / m
  let start : Fin count → ℕ := fun i => i.val * m
  let stop : Fin count → ℕ := fun i => min ((i.val + 1) * m) N
  have hBounds (i : Fin count) : start i ≤ stop i ∧ stop i ≤ N ∧
      stop i - start i ≤ m := by
    have hi : i.val + 1 ≤ count := i.isLt
    have hmul : (i.val + 1) * m ≤ N + m - 1 :=
      (Nat.le_div_iff_mul_le hm).mp hi
    have hstartN : start i ≤ N := by
      dsimp only [start]
      rw [Nat.add_mul, Nat.one_mul] at hmul
      omega
    have hstartstop : start i ≤ stop i := by
      apply le_min
      · dsimp only [start]
        exact Nat.mul_le_mul_right m (Nat.le_succ i.val)
      · exact hstartN
    have hstopN : stop i ≤ N := Nat.min_le_right _ _
    have hstopMul : stop i ≤ (i.val + 1) * m := Nat.min_le_left _ _
    dsimp only [start] at hstartstop ⊢
    rw [Nat.add_mul, Nat.one_mul] at hstopMul
    exact ⟨hstartstop, hstopN, by omega⟩
  let localRange : Fin count → Shao.Path N → ℝ := fun i a =>
    sSup {w : ℝ | ∃ u v : Fin (N + 1),
      start i ≤ u.val ∧ u.val ≤ stop i ∧ start i ≤ v.val ∧ v.val ≤ stop i ∧
      w = Shao.prefixSum a u.val - Shao.prefixSum a v.val}
  let future : Fin count → Shao.Path N → ℝ := fun i a =>
    sSup {w : ℝ | ∃ v : Fin (N + 1), stop i ≤ v.val ∧
      w = Shao.prefixSum a (stop i) - Shao.prefixSum a v.val}
  let W1 (i : Fin count) : Shao.Path N → Shao.Path (stop i - start i) :=
    fun a j => a ⟨start i + j.val, by have hj := j.isLt; have hi := hBounds i; omega⟩
  let W2 (i : Fin count) : Shao.Path N → Shao.Path (N - stop i) :=
    fun a j => a ⟨stop i + j.val, by have hj := j.isLt; have hi := hBounds i; omega⟩
  let F : Fin count → Shao.Path N → ℝ := fun i a => Real.exp (2 * theta *
    (Shao.maxWithZero (W1 i a) + Shao.maxWithZero (-W1 i a)))
  let G : Fin count → Shao.Path N → ℝ := fun i a =>
    Real.exp (2 * theta * Shao.maxWithZero (-W2 i a))
  let V : ℝ := CF * Real.exp ((2001 / 2000000 : ℝ) * (N : ℝ) * theta ^ 2 +
    CF * (N : ℝ) * theta ^ 3 * beta)
  have hBlock (i : Fin count) :
      Integrable (fun a => F i a * G i a) Ptilt ∧
        (∫ a, F i a * G i a ∂Ptilt) ≤ CS * V ∧
        ∀ a, Real.exp (2 * theta * localRange i a) *
          Real.exp (2 * theta * future i a) ≤ F i a * G i a := by
    have hi := hBounds i
    rcases cwm_iid_adjacent_windows nu N (start i) (stop i) hi.1 hi.2.1 with
      ⟨hMap1, hMap2, hInd, hPrefix⟩
    have hW1m : Measurable (W1 i) := by fun_prop
    have hW2m : Measurable (W2 i) := by fun_prop
    let f : Shao.Path (stop i - start i) → ℝ := fun b => Real.exp
      (2 * theta * (Shao.maxWithZero b + Shao.maxWithZero (-b)))
    let g : Shao.Path (N - stop i) → ℝ := fun b =>
      Real.exp (2 * theta * Shao.maxWithZero (-b))
    have hfm : Measurable f :=
      (measurable_const.mul (Shao.measurable_maxWithZero.add
        (Shao.measurable_maxWithZero.comp (by fun_prop)))).exp
    have hgm : Measurable g :=
      (measurable_const.mul (Shao.measurable_maxWithZero.comp (by fun_prop))).exp
    have hShortLength : ((stop i - start i : ℕ) : ℝ) * theta ^ 2 ≤ 101 / 100 :=
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hi.2.2) (sq_nonneg theta)).trans hmUpper
    have hS := hShort rho B hB hs hmean hsecond theta ht htB
      (stop i - start i) hShortLength
    have hT := hFuture rho B hB hs hmean hsecond theta ht htB (N - stop i)
    have hFI : Integrable (F i) Ptilt := by
      have hh : Integrable f (Ptilt.map (W1 i)) := by rw [hMap1]; exact hS.1
      exact (integrable_map_measure hfm.aestronglyMeasurable hW1m.aemeasurable).1 hh
    have hGI : Integrable (G i) Ptilt := by
      have hh : Integrable g (Ptilt.map (W2 i)) := by rw [hMap2]; exact hT.1
      exact (integrable_map_measure hgm.aestronglyMeasurable hW2m.aemeasurable).1 hh
    have hFM : Measurable (F i) := hfm.comp hW1m
    have hGM : Measurable (G i) := hgm.comp hW2m
    have hindFG : IndepFun (F i) (G i) Ptilt := hInd.comp hfm hgm
    have hFbound : (∫ a, F i a ∂Ptilt) ≤ CS := by
      have heq : (∫ a, F i a ∂Ptilt) =
          ∫ b, f b ∂Measure.pi (fun _ : Fin (stop i - start i) => nu) := by
        rw [← hMap1, integral_map hW1m.aemeasurable hfm.aestronglyMeasurable]
      rw [heq]
      exact hS.2
    have hGbound : (∫ a, G i a ∂Ptilt) ≤ V := by
      have heq : (∫ a, G i a ∂Ptilt) =
          ∫ b, g b ∂Measure.pi (fun _ : Fin (N - stop i) => nu) := by
        rw [← hMap2, integral_map hW2m.aemeasurable hgm.aestronglyMeasurable]
      rw [heq]
      apply hT.2.trans
      apply mul_le_mul_of_nonneg_left _ (by linarith only [hCF])
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (Nat.sub_le N (stop i)) : ((N - stop i : ℕ) : ℝ) ≤ N)
        (by positivity : 0 ≤ (2001 / 2000000 : ℝ) * theta ^ 2 + CF * theta ^ 3 * beta)
      nlinarith only [hh]
    have hProdI : Integrable (fun a => F i a * G i a) Ptilt :=
      hindFG.integrable_mul hFI hGI
    have hProdBound : (∫ a, F i a * G i a ∂Ptilt) ≤ CS * V := by
      have heq := hindFG.integral_mul_eq_mul_integral
        hFI.aestronglyMeasurable hGI.aestronglyMeasurable
      change (∫ a, F i a * G i a ∂Ptilt) =
        (∫ a, F i a ∂Ptilt) * (∫ a, G i a ∂Ptilt) at heq
      rw [heq]
      exact mul_le_mul hFbound hGbound
        (integral_nonneg fun a => (Real.exp_pos _).le) (by linarith only [hCS])
    refine ⟨hProdI, hProdBound, ?_⟩
    intro a
    have hLocal : localRange i a ≤ Shao.maxWithZero (W1 i a) +
        Shao.maxWithZero (-W1 i a) := by
      have hne : Set.Nonempty {w : ℝ | ∃ u v : Fin (N + 1),
          start i ≤ u.val ∧ u.val ≤ stop i ∧ start i ≤ v.val ∧ v.val ≤ stop i ∧
          w = Shao.prefixSum a u.val - Shao.prefixSum a v.val} :=
        ⟨0, ⟨stop i, by omega⟩, ⟨stop i, by omega⟩, hi.1, le_refl _, hi.1,
          le_refl _, by simp⟩
      apply csSup_le hne
      rintro w ⟨u, v, hsu, hus, hsv, hvs, rfl⟩
      have hpu := (hPrefix a).1 (u.val - start i) (by omega)
      have hpv := (hPrefix a).1 (v.val - start i) (by omega)
      have heu : start i + (u.val - start i) = u.val := by omega
      have hev : start i + (v.val - start i) = v.val := by omega
      rw [heu] at hpu
      rw [hev] at hpv
      have hu := (Shao.maxWithZero_le_iff (W1 i a) _).mp le_rfl
        (u.val - start i) (by omega)
      have hv := (Shao.maxWithZero_le_iff (-W1 i a) _).mp le_rfl
        (v.val - start i) (by omega)
      rw [Shao.prefixSum_neg] at hv
      nlinarith only [hpu, hpv, hu, hv]
    have hFut : future i a ≤ Shao.maxWithZero (-W2 i a) := by
      have hne : Set.Nonempty {w : ℝ | ∃ v : Fin (N + 1), stop i ≤ v.val ∧
          w = Shao.prefixSum a (stop i) - Shao.prefixSum a v.val} :=
        ⟨0, ⟨stop i, by omega⟩, le_refl _, by simp⟩
      apply csSup_le hne
      rintro w ⟨v, hv, rfl⟩
      have hp := (hPrefix a).2 (v.val - stop i) (by omega)
      have he : stop i + (v.val - stop i) = v.val := by omega
      rw [he] at hp
      have hh := (Shao.maxWithZero_le_iff (-W2 i a) _).mp le_rfl
        (v.val - stop i) (by omega)
      rw [Shao.prefixSum_neg] at hh
      nlinarith only [hp, hh]
    apply mul_le_mul
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hLocal (by positivity))
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hFut (by positivity))
    · exact (Real.exp_pos _).le
    · exact (Real.exp_pos _).le
  have hCount : (count : ℝ) ≤ 1 + (N : ℝ) * theta ^ 2 := by
    have hMulN : count * m ≤ N + m :=
      (Nat.div_mul_le_self (N + m - 1) m).trans (by omega)
    have hMul : (count : ℝ) * (m : ℝ) ≤ (N : ℝ) + (m : ℝ) := by exact_mod_cast hMulN
    by_cases hcount : 1 ≤ (count : ℝ)
    · have hh := mul_le_mul_of_nonneg_right hMul (sq_nonneg theta)
      have hh' := mul_le_mul_of_nonneg_left hmLower (sub_nonneg.mpr hcount)
      nlinarith only [hh, hh']
    · have hn : 0 ≤ (N : ℝ) * theta ^ 2 := by positivity
      linarith only [hcount, hn]
  have hSumI : Integrable (fun a => ∑ i : Fin count, F i a * G i a) Ptilt :=
    integrable_finsetSum _ (fun i hi => (hBlock i).1)
  have hPoint (a : Shao.Path N) : Real.exp (2 * theta * R a) ≤
      ∑ i : Fin count, F i a * G i a := by
    have hh := cwm_drawdown_block_pointwise N m hN hm theta ht.le a
    apply hh.trans
    exact Finset.sum_le_sum (fun i hi => (hBlock i).2.2 a)
  calc
    _ ≤ ∫ a, ∑ i : Fin count, F i a * G i a ∂Ptilt := integral_mono hInt hSumI hPoint
    _ = ∑ i : Fin count, ∫ a, F i a * G i a ∂Ptilt :=
      integral_finsetSum _ (fun i hi => (hBlock i).1)
    _ ≤ ∑ _i : Fin count, CS * V := Finset.sum_le_sum (fun i hi => (hBlock i).2.1)
    _ = (count : ℝ) * (CS * V) := by simp
    _ ≤ (1 + (N : ℝ) * theta ^ 2) * (CS * V) :=
      mul_le_mul_of_nonneg_right hCount (by dsimp [V]; positivity)
    _ ≤ C * (1 + (N : ℝ) * theta ^ 2) * Real.exp
        ((2001 / 2000000 : ℝ) * (N : ℝ) * theta ^ 2 + C * (N : ℝ) * theta ^ 3 * beta) := by
      dsimp only [V]
      have hreassoc : (1 + (N : ℝ) * theta ^ 2) *
          (CS * (CF * Real.exp ((2001 / 2000000 : ℝ) * (N : ℝ) * theta ^ 2 +
            CF * (N : ℝ) * theta ^ 3 * beta))) =
          (CS * CF) * (1 + (N : ℝ) * theta ^ 2) * Real.exp
            ((2001 / 2000000 : ℝ) * (N : ℝ) * theta ^ 2 +
              CF * (N : ℝ) * theta ^ 3 * beta) := by ring
      rw [hreassoc]
      apply mul_le_mul
      · dsimp [C]
        have hn : 0 ≤ 1 + (N : ℝ) * theta ^ 2 := by positivity
        nlinarith only [hn]
      · apply Real.exp_le_exp.mpr
        have hCFle : CF ≤ C := by dsimp [C]; nlinarith only [hCS, hCF]
        have hh := mul_le_mul_of_nonneg_right hCFle
          (by positivity : 0 ≤ (N : ℝ) * theta ^ 3 * beta)
        nlinarith only [hh]
      · exact (Real.exp_pos _).le
      · dsimp [C]
        positivity

private theorem cwm_first_exponential_piece :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (B : ℝ), 0 < B → (∀ᵐ z : ℝ ∂rho, |z| ≤ B) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ theta : ℝ, 0 ≤ theta → theta * B ≤ 1 / 10 →
          ∀ N : ℕ,
            let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => rho)
            let R : Shao.Path N → ℝ := fun a =>
              sSup {w : ℝ | ∃ u v : Fin (N + 1), u.val ≤ v.val ∧
                w = Shao.prefixSum a u.val - Shao.prefixSum a v.val}
            Integrable
              (fun a : Shao.Path N =>
                Real.exp (theta * Shao.prefixSum a N + 2 * theta * R a)) P ∧
              (∫ a : Shao.Path N,
                Real.exp (theta * Shao.prefixSum a N + 2 * theta * R a) ∂P) ≤
                C * (1 + (N : ℝ) * theta ^ 2) *
                  Real.exp ((1002001 / 2000000 : ℝ) * (N : ℝ) * theta ^ 2 +
                    C * (N : ℝ) * theta ^ 3 * beta) := by
  classical
  rcases cwm_log_mgf_taylor with ⟨CL, hCL, hTaylor⟩
  rcases cwm_tilt_drawdown_moment with ⟨CD, hCD, hDraw⟩
  let C : ℝ := 1 + CL + CD
  refine ⟨C, by dsimp [C]; linarith only [hCL, hCD], ?_⟩
  intro rho hprob B hB hs hmean hsecond beta theta ht htB N P R
  have hb : 0 ≤ beta := integral_nonneg (fun z => pow_nonneg (abs_nonneg z) 3)
  by_cases ht0 : theta = 0
  · subst theta
    simp only [zero_mul, mul_zero, zero_pow (by decide : 3 ≠ 0),
      zero_pow (by decide : 2 ≠ 0), zero_add, add_zero, Real.exp_zero, mul_one]
    refine ⟨integrable_const 1, ?_⟩
    simpa only [integral_const, probReal_univ, one_smul] using
      (by dsimp [C]; linarith only [hCL, hCD] : (1 : ℝ) ≤ C)
  have htheta : 0 < theta := lt_of_le_of_ne ht (Ne.symm ht0)
  let c : ℝ := ∫ z : ℝ, Real.exp (theta * z) ∂rho
  let nu : Measure ℝ := rho.tilted (fun z => theta * z)
  let Ptilt : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => nu)
  have hD := cwm_linear_tilt_product_density rho B theta hB hs
  have hc : 0 < c := hD.1
  have hNu : IsProbabilityMeasure nu := hD.2.1
  letI : IsProbabilityMeasure nu := hNu
  have hM := hDraw rho B hB hs hmean hsecond theta htheta htB N
  let g : Shao.Path N → ℝ := fun a => Real.exp (2 * theta * R a)
  rcases cwm_path_extrema_geometry N with ⟨_, _, hRm, hGeom⟩
  have hsP : ∀ᵐ a : Shao.Path N ∂P, ∀ i : Fin N, |a i| ≤ B := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin N => rho) (i := i)).eventually hs
  have hgI : Integrable g P := by
    apply (integrable_const (Real.exp (2 * theta * (N : ℝ) * B))).mono'
      ((measurable_const.mul hRm).exp.aestronglyMeasurable)
    filter_upwards [hsP] with a ha
    rcases hGeom a with ⟨_, _, _, _, hRn, hRu, _, _⟩
    have hu : R a ≤ (N : ℝ) * B := hRu.trans (by
      calc
        (∑ i : Fin N, |a i|) ≤ ∑ _i : Fin N, B :=
          Finset.sum_le_sum (fun i hi => ha i)
        _ = (N : ℝ) * B := by simp)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    change 2 * theta * R a ≤ 2 * theta * (N : ℝ) * B
    nlinarith only [hu, htheta]
  have hDensity := hD.2.2.2 N g hgI
  have hFun (a : Shao.Path N) :
      Real.exp (theta * Shao.prefixSum a N + 2 * theta * R a) =
      g a * Real.exp (theta * Shao.prefixSum a N) := by
    rw [Real.exp_add]
    exact mul_comm _ _
  have hInt : Integrable (fun a : Shao.Path N =>
      Real.exp (theta * Shao.prefixSum a N + 2 * theta * R a)) P :=
    hDensity.2.1.congr (ae_of_all _ fun a => (hFun a).symm)
  refine ⟨hInt, ?_⟩
  have hEq : (∫ a : Shao.Path N,
      Real.exp (theta * Shao.prefixSum a N + 2 * theta * R a) ∂P) =
      c ^ N * (∫ a, g a ∂Ptilt) := by
    rw [integral_congr_ae (ae_of_all _ hFun)]
    exact hDensity.2.2
  have hT := hTaylor rho B hB hs hmean hsecond theta (by
    rw [abs_of_pos htheta]; linarith only [htB])
  have hlog : Real.log c ≤ theta ^ 2 / 2 + CL * theta ^ 3 * beta := by
    have hh := (abs_le.mp hT.2.2).2
    rw [abs_of_pos htheta] at hh
    linarith only [hh]
  have hcPow : c ^ N ≤ Real.exp ((N : ℝ) * theta ^ 2 / 2 +
      CL * (N : ℝ) * theta ^ 3 * beta) := by
    have heq : c ^ N = Real.exp ((N : ℝ) * Real.log c) := by
      rw [Real.exp_nat_mul, Real.exp_log hc]
    rw [heq]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    nlinarith only [hh]
  rw [hEq]
  calc
    _ ≤ Real.exp ((N : ℝ) * theta ^ 2 / 2 + CL * (N : ℝ) * theta ^ 3 * beta) *
        (CD * (1 + (N : ℝ) * theta ^ 2) * Real.exp
          ((2001 / 2000000 : ℝ) * (N : ℝ) * theta ^ 2 +
            CD * (N : ℝ) * theta ^ 3 * beta)) :=
      mul_le_mul hcPow hM.2 (integral_nonneg fun a => (Real.exp_pos _).le)
        (Real.exp_pos _).le
    _ = CD * (1 + (N : ℝ) * theta ^ 2) * Real.exp
        ((1002001 / 2000000 : ℝ) * (N : ℝ) * theta ^ 2 +
          (CL + CD) * (N : ℝ) * theta ^ 3 * beta) := by
      have hreassoc : Real.exp ((N : ℝ) * theta ^ 2 / 2 +
          CL * (N : ℝ) * theta ^ 3 * beta) *
          (CD * (1 + (N : ℝ) * theta ^ 2) * Real.exp
            ((2001 / 2000000 : ℝ) * (N : ℝ) * theta ^ 2 +
              CD * (N : ℝ) * theta ^ 3 * beta)) =
          CD * (1 + (N : ℝ) * theta ^ 2) *
            (Real.exp ((N : ℝ) * theta ^ 2 / 2 + CL * (N : ℝ) * theta ^ 3 * beta) *
              Real.exp ((2001 / 2000000 : ℝ) * (N : ℝ) * theta ^ 2 +
                CD * (N : ℝ) * theta ^ 3 * beta)) := by ring
      rw [hreassoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ C * (1 + (N : ℝ) * theta ^ 2) * Real.exp
        ((1002001 / 2000000 : ℝ) * (N : ℝ) * theta ^ 2 +
          C * (N : ℝ) * theta ^ 3 * beta) := by
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [C]
        linarith only [hCL]
      · apply Real.exp_le_exp.mpr
        dsimp [C]
        nlinarith only [mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
          (mul_nonneg (pow_nonneg htheta.le 3) hb)]
      · exact (Real.exp_pos _).le
      · dsimp [C]
        positivity

theorem actual_circular_witness_small_parameter_moment :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
        (B : ℝ), 0 < B → (∀ᵐ z : ℝ ∂rho, |z| ≤ B) →
        (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
        let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
        ∀ N : ℕ,
          let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => rho)
          let L : Shao.Path N → ℝ := fun a =>
            if hN : 0 < N then
              sSup {w : ℝ | ∃ i : Fin N, ∃ k : Fin (N + 1),
                w = Shao.prefixSum a N -
                  2 * ∑ r ∈ Finset.range k.val,
                    a ⟨(i.val + r) % N, Nat.mod_lt _ hN⟩}
            else 0
          Measurable L ∧
            ∀ theta : ℝ, 0 ≤ theta → theta * B ≤ 1 / 10 →
              Integrable (fun a : Shao.Path N => Real.exp (theta * L a)) P ∧
                (∫ a : Shao.Path N, Real.exp (theta * L a) ∂P) ≤
                  C * (1 + (N : ℝ) * theta ^ 2) *
                    Real.exp ((1002001 / 2000000 : ℝ) * (N : ℝ) * theta ^ 2 +
                      C * (N : ℝ) * theta ^ 3 * beta) := by
  classical
  rcases cwm_first_exponential_piece with ⟨C0, hC0, hPiece⟩
  let C : ℝ := 2 * C0
  refine ⟨C, by dsimp [C]; linarith only [hC0], ?_⟩
  intro rho hprob B hB hs hmean hsecond beta N P L
  let A : Shao.Path N → ℝ := fun a =>
    sSup {w : ℝ | ∃ u v : Fin (N + 1), u.val ≤ v.val ∧
      w = Shao.prefixSum a v.val - Shao.prefixSum a u.val}
  let R : Shao.Path N → ℝ := fun a =>
    sSup {w : ℝ | ∃ u v : Fin (N + 1), u.val ≤ v.val ∧
      w = Shao.prefixSum a u.val - Shao.prefixSum a v.val}
  rcases cwm_path_extrema_geometry N with ⟨hLm, hAm, hRm, hGeom⟩
  refine ⟨hLm, ?_⟩
  intro theta ht htB
  have hb : 0 ≤ beta := integral_nonneg (fun z => pow_nonneg (abs_nonneg z) 3)
  have hP1 := hPiece rho B hB hs hmean hsecond theta ht htB N
  let F1 : Shao.Path N → ℝ := fun a =>
    Real.exp (theta * Shao.prefixSum a N + 2 * theta * R a)
  let F2 : Shao.Path N → ℝ := fun a =>
    Real.exp (2 * theta * A a - theta * Shao.prefixSum a N)
  let rhoNeg : Measure ℝ := rho.map (fun z : ℝ => -z)
  have hm : Measurable (fun z : ℝ => -z) := measurable_neg
  letI : IsProbabilityMeasure rhoNeg :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  have hsNeg : ∀ᵐ z : ℝ ∂rhoNeg, |z| ≤ B := by
    apply (ae_map_iff hm.aemeasurable
      (measurableSet_le (continuous_abs.measurable : Measurable (fun z : ℝ => |z|))
        measurable_const)).2
    simpa only [abs_neg] using hs
  have hMeanNeg : (∫ z : ℝ, z ∂rhoNeg) = 0 := by
    change (∫ z : ℝ, z ∂rho.map (fun z : ℝ => -z)) = 0
    rw [integral_map hm.aemeasurable (by fun_prop), integral_neg, hmean, neg_zero]
  have hSecondNeg : (∫ z : ℝ, z ^ 2 ∂rhoNeg) = 1 := by
    change (∫ z : ℝ, z ^ 2 ∂rho.map (fun z : ℝ => -z)) = 1
    rw [integral_map hm.aemeasurable (by fun_prop)]
    simpa only [neg_sq] using hsecond
  have hBetaNeg : (∫ z : ℝ, |z| ^ 3 ∂rhoNeg) = beta := by
    change (∫ z : ℝ, |z| ^ 3 ∂rho.map (fun z : ℝ => -z)) = beta
    rw [integral_map hm.aemeasurable (by fun_prop)]
    simp only [abs_neg]
    rfl
  have hP2 := hPiece rhoNeg B hB hsNeg hMeanNeg hSecondNeg theta ht htB N
  let PN : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => rhoNeg)
  have hMap : P.map (fun a : Shao.Path N => -a) = PN :=
    Measure.pi_map_pi (fun _ : Fin N => hm.aemeasurable)
  have hPathM : Measurable (fun a : Shao.Path N => -a) := by fun_prop
  have hF1m : Measurable F1 :=
    ((measurable_const.mul (Shao.measurable_prefixSum N)).add
      (measurable_const.mul hRm)).exp
  have hNeg (a : Shao.Path N) : F1 (-a) = F2 a := by
    rcases hGeom a with ⟨_, _, _, _, _, _, _, hRneg⟩
    change R (-a) = A a at hRneg
    dsimp only [F1, F2]
    rw [Shao.prefixSum_neg, hRneg]
    congr 1
    ring
  have hF2I : Integrable F2 P := by
    have hh : Integrable F1 (P.map (fun a : Shao.Path N => -a)) := by
      rw [hMap]
      exact hP2.1
    have hh' := (integrable_map_measure hF1m.aestronglyMeasurable hPathM.aemeasurable).1 hh
    exact hh'.congr (ae_of_all _ hNeg)
  have hF2B : (∫ a, F2 a ∂P) ≤ C0 * (1 + (N : ℝ) * theta ^ 2) *
      Real.exp ((1002001 / 2000000 : ℝ) * (N : ℝ) * theta ^ 2 +
        C0 * (N : ℝ) * theta ^ 3 * beta) := by
    calc
      _ = ∫ a : Shao.Path N, F1 (-a) ∂P :=
        integral_congr_ae (ae_of_all _ fun a => (hNeg a).symm)
      _ = ∫ a, F1 a ∂PN := by
        rw [← hMap, integral_map hPathM.aemeasurable hF1m.aestronglyMeasurable]
      _ ≤ _ := by simpa only [hBetaNeg] using hP2.2
  have hBound (a : Shao.Path N) : Real.exp (theta * L a) ≤ F1 a + F2 a := by
    rcases hGeom a with ⟨_, _, _, _, _, _, hL, _⟩
    change L a = max (Shao.prefixSum a N + 2 * R a)
      (2 * A a - Shao.prefixSum a N) at hL
    rw [hL]
    rcases le_total (Shao.prefixSum a N + 2 * R a)
      (2 * A a - Shao.prefixSum a N) with hh | hh
    · rw [max_eq_right hh]
      have he : theta * (2 * A a - Shao.prefixSum a N) =
          2 * theta * A a - theta * Shao.prefixSum a N := by ring
      rw [he]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
    · rw [max_eq_left hh]
      have he : theta * (Shao.prefixSum a N + 2 * R a) =
          theta * Shao.prefixSum a N + 2 * theta * R a := by ring
      rw [he]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
  have hInt : Integrable (fun a : Shao.Path N => Real.exp (theta * L a)) P := by
    apply (hP1.1.add hF2I).mono'
      ((measurable_const.mul hLm).exp.aestronglyMeasurable)
    exact ae_of_all _ fun a => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hBound a
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∫ a, F1 a + F2 a ∂P := integral_mono hInt (hP1.1.add hF2I) hBound
    _ = (∫ a, F1 a ∂P) + (∫ a, F2 a ∂P) := integral_add hP1.1 hF2I
    _ ≤ 2 * (C0 * (1 + (N : ℝ) * theta ^ 2) * Real.exp
        ((1002001 / 2000000 : ℝ) * (N : ℝ) * theta ^ 2 +
          C0 * (N : ℝ) * theta ^ 3 * beta)) := by linarith only [hP1.2, hF2B]
    _ = C * (1 + (N : ℝ) * theta ^ 2) * Real.exp
        ((1002001 / 2000000 : ℝ) * (N : ℝ) * theta ^ 2 +
          C0 * (N : ℝ) * theta ^ 3 * beta) := by dsimp [C]; ring
    _ ≤ C * (1 + (N : ℝ) * theta ^ 2) * Real.exp
        ((1002001 / 2000000 : ℝ) * (N : ℝ) * theta ^ 2 +
          C * (N : ℝ) * theta ^ 3 * beta) := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [C]; positivity)
      apply Real.exp_le_exp.mpr
      dsimp [C]
      have hn : 0 ≤ C0 * (N : ℝ) * theta ^ 3 * beta := by positivity
      nlinarith only [hn]

end Shao.Probability.SourceCircularWitnessMoment
