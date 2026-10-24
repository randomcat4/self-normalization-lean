/-
Complete proposed heads only, with no implementation bodies and no Lean check.
These are not frozen/accepted by root. All stopping objects are literal actual
finite-product paths; there is no completion-envelope or squared-strip premise.
Zero proposed new definitions.
-/
import Shao.Probability.TruncationIntegrals
import Shao.Probability.TruncationRegularity
import Shao.Probability.FiniteIID
import Shao.Probability.MeasurablePath
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.Fin
import Mathlib.Probability.Independence.Integration
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Order.Lattice

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Shao.Probability
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem sourceBackward_clipped_square_mean
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (H : ℝ) (hR : Shao.truncationBudget nu n 0 ≤ 1 / 2)
    (hH : 4 * Shao.truncationBudget nu n 0 ^ 2 ≤ H) :
    let R : ℝ := Shao.truncationBudget nu n 0
    0 < R ∧ 0 < H ∧
      Integrable (fun z : ℝ => min (z ^ 2) H) nu ∧
      (1 / 2 : ℝ) ≤ (n : ℝ) * (∫ z : ℝ, min (z ^ 2) H ∂nu) := by
  intro R
  have hn : 0 < n := by
    by_contra hh
    have hn0 : n = 0 := by omega
    simp [hn0] at hnorm
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂nu := by
    have hnon : 0 ≤ ∫ z : ℝ, z ^ 2 ∂nu := integral_nonneg (fun z => sq_nonneg z)
    nlinarith only [hnorm, hnon, hN]
  have hRp : 0 < R := Shao.truncationBudget_pos nu n h2 hn hsecond 0 (by norm_num)
  have hHp : 0 < H := (mul_pos (by norm_num : (0 : ℝ) < 4) (sq_pos_of_pos hRp)).trans_le hH
  have hclip0 (z : ℝ) : 0 ≤ min (z ^ 2) H := le_min (sq_nonneg z) hHp.le
  have hclip : Integrable (fun z : ℝ => min (z ^ 2) H) nu := by
    apply h2.mono' (by fun_prop)
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (hclip0 z)]
    exact min_le_left _ _
  let tail : ℝ → ℝ := fun z => if H < z ^ 2 then z ^ 2 else 0
  have htail : Integrable tail nu := by
    apply h2.mono' ((Measurable.ite
      (measurableSet_lt measurable_const (continuous_id.pow 2).measurable)
      (continuous_id.pow 2).measurable measurable_const).aestronglyMeasurable)
    filter_upwards [] with z
    dsimp [tail]
    split_ifs
    · rw [abs_of_nonneg (sq_nonneg z)]
    · simpa only [abs_zero] using sq_nonneg z
  have hpoint (z : ℝ) : (2 * R) * tail z ≤ Shao.truncationF z := by
    dsimp [tail]
    split_ifs with hz
    · have habs : 2 * R ≤ |z| := by
        nlinarith only [hz, hH, hRp, abs_nonneg z, sq_abs z]
      have hmin : 2 * R ≤ min |z| 1 := le_min habs (by change R ≤ 1 / 2 at hR; linarith only [hR])
      unfold Shao.truncationF
      nlinarith only [mul_le_mul_of_nonneg_left hmin (sq_nonneg z)]
    · simpa only [mul_zero] using Shao.truncationF_nonneg z
  have hF : Integrable Shao.truncationF nu := by
    simpa only [one_mul] using Shao.integrable_truncationF_mul nu h2 1
  have hi := integral_mono (htail.const_mul (2 * R)) hF hpoint
  rw [integral_const_mul] at hi
  have hRform : (n : ℝ) * (∫ z : ℝ, Shao.truncationF z ∂nu) = R := by
    simp only [R, Shao.truncationBudget, add_zero, one_mul]
  have htailpay : (n : ℝ) * (∫ z : ℝ, tail z ∂nu) ≤ 1 / 2 := by
    apply (mul_le_mul_iff_right₀ (show 0 < 2 * R by positivity)).mp
    have hh := mul_le_mul_of_nonneg_left hi hN.le
    nlinarith only [hh, hRform]
  have hdecomp (z : ℝ) : z ^ 2 ≤ min (z ^ 2) H + tail z := by
    dsimp [tail]
    split_ifs with hz
    · rw [min_eq_right hz.le]
      linarith only [hHp]
    · rw [min_eq_left (le_of_not_gt hz)]
      simp only [add_zero, le_refl]
  have hid := integral_mono h2 (hclip.add htail) hdecomp
  change (∫ z : ℝ, z ^ 2 ∂nu) ≤ ∫ z : ℝ, min (z ^ 2) H + tail z ∂nu at hid
  rw [integral_add hclip htail] at hid
  refine ⟨hRp, hHp, hclip, ?_⟩
  have hh := mul_le_mul_of_nonneg_left hid hN.le
  nlinarith only [hh, hnorm, htailpay]

private theorem bse_prefixSquares_mono {n : ℕ} (a : Shao.Path n) :
    Monotone (Shao.prefixSquares a) := by
  intro k l hkl
  unfold Shao.prefixSquares
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.trans_le hkl
  · intro i _ _
    exact sq_nonneg _

private theorem bse_reverse_sum {n : ℕ} (f : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), f (Fin.rev i)) =
      (∑ i : Fin n, f i) -
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < n - k), f i := by
  classical
  have hreindex : (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), f (Fin.rev i)) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => n - k ≤ i.val), f i := by
    apply Finset.sum_equiv Fin.revPerm
    · intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (i.val < k ↔ n - k ≤ (Fin.rev i).val)
      rw [Fin.val_rev]
      have hi := i.is_lt
      omega
    · intro i _
      rfl
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : Fin n => i.val < n - k) f
  simp only [not_lt] at hsplit
  rw [hreindex]
  linarith only [hsplit]

private theorem bse_reverse_prefixSquares {n : ℕ} (a : Shao.Path n)
    (k : ℕ) (hk : k ≤ n) :
    Shao.prefixSquares (fun i : Fin n => a (Fin.rev i)) k =
      Shao.energy a - Shao.prefixSquares a (n - k) := by
  exact bse_reverse_sum (fun i : Fin n => (a i) ^ 2) k hk

private theorem bse_reverse_prefixSum {n : ℕ} (a : Shao.Path n)
    (k : ℕ) (hk : k ≤ n) :
    Shao.prefixSum (fun i : Fin n => a (Fin.rev i)) k =
      Shao.prefixSum a n - Shao.prefixSum a (n - k) := by
  rw [Shao.prefixSum_length]
  exact bse_reverse_sum a k hk

private theorem bse_capped_find_data
    (L : ℕ) (hL : 0 < L) (H : ℝ) (hH : 0 < H)
    (Q : ℕ → ℝ) (hQ0 : Q 0 = 0) (hQ : Monotone Q) :
    let NH : ℕ := @dite ℕ (∃ k : ℕ, k ≤ L ∧ H ≤ Q k)
      (Classical.propDecidable _)
      (fun h => @Nat.find (fun k : ℕ => k ≤ L ∧ H ≤ Q k)
        (fun k => Classical.propDecidable _) h)
      (fun _ => L)
    1 ≤ NH ∧ NH ≤ L ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ L → (i ≤ NH ↔ Q (i - 1) < H)) ∧
      (Q L < H → NH = L) := by
  classical
  intro NH
  letI : DecidablePred (fun k : ℕ => k ≤ L ∧ H ≤ Q k) :=
    fun k => Classical.propDecidable _
  by_cases hh : ∃ k : ℕ, k ≤ L ∧ H ≤ Q k
  · simp only [NH, dif_pos hh]
    have hspec := Nat.find_spec hh
    have hpos : 1 ≤ Nat.find hh := by
      by_contra h
      have hzero : Nat.find hh = 0 := by omega
      rw [hzero, hQ0] at hspec
      exact (not_le_of_gt hH) hspec.2
    change 1 ≤ Nat.find hh ∧ Nat.find hh ≤ L ∧ _ ∧ _
    refine ⟨hpos, hspec.1, ?_, ?_⟩
    · intro i hi hiL
      constructor
      · intro hif
        by_contra hnot
        have himin : i - 1 < Nat.find hh := by omega
        exact Nat.find_min hh himin ⟨by omega, le_of_not_gt hnot⟩
      · intro hiQ
        by_contra hnot
        have hfi : Nat.find hh ≤ i - 1 := by omega
        exact (not_le_of_gt hiQ) (hspec.2.trans (hQ hfi))
    · intro hfail
      exact False.elim ((not_le_of_gt hfail) (hspec.2.trans (hQ hspec.1)))
  · simp only [NH, dif_neg hh]
    change 1 ≤ L ∧ L ≤ L ∧ _ ∧ _
    refine ⟨hL, le_rfl, ?_, fun _ => True.intro⟩
    intro i hi hiL
    constructor
    · intro _
      by_contra hnot
      exact hh ⟨i - 1, by omega, le_of_not_gt hnot⟩
    · intro _
      exact hiL

private theorem bse_reverse_past_factor
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (s : Finset (Fin n)) (i : Fin n) (hi : i ∉ s)
    (f : (s → ℝ) → ℝ) (hf : Measurable f)
    (g : ℝ → ℝ) (hg : Measurable g) (hgi : Integrable g nu)
    (hfi : Integrable (fun a : Shao.Path n =>
      f (fun j : s => a (Fin.rev (j : Fin n))))
        (Measure.pi (fun _ : Fin n => nu))) :
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let past : Shao.Path n → ℝ := fun a => f (fun j : s => a (Fin.rev (j : Fin n)))
    let current : Shao.Path n → ℝ := fun a => g (a (Fin.rev i))
    Integrable current P ∧ Integrable (fun a : Shao.Path n => past a * current a) P ∧
      (∫ a : Shao.Path n, past a * current a ∂P) =
        (∫ a : Shao.Path n, past a ∂P) * (∫ z : ℝ, g z ∂nu) := by
  classical
  intro P past current
  let X : Fin n → Shao.Path n → ℝ := fun j a => a (Fin.rev j)
  have hXm (j : Fin n) : Measurable (X j) := measurable_pi_apply (Fin.rev j)
  have hXi : iIndepFun X P :=
    (iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)).precomp Fin.rev_injective
  have hdisj : Disjoint s ({i} : Finset (Fin n)) := by
    simpa only [Finset.disjoint_singleton_right] using hi
  have htuples := hXi.indepFun_finset s {i} hdisj hXm
  have hright : Measurable (fun v : ({i} : Finset (Fin n)) → ℝ => g (v ⟨i, by simp⟩)) :=
    hg.comp (measurable_pi_apply
      (X := fun _ : ({i} : Finset (Fin n)) => ℝ)
      (⟨i, by simp⟩ : ({i} : Finset (Fin n))))
  have hind : IndepFun past current P := htuples.comp hf hright
  have hcur : Integrable current P :=
    (measurePreserving_eval (fun _ : Fin n => nu) (Fin.rev i)).integrable_comp_of_integrable hgi
  have hint : Integrable (fun a : Shao.Path n => past a * current a) P := hind.integrable_mul hfi hcur
  have hmap : Measure.map (fun a : Shao.Path n => a (Fin.rev i)) P = nu :=
    (measurePreserving_eval (fun _ : Fin n => nu) (Fin.rev i)).map_eq
  have hcurEq : (∫ a : Shao.Path n, current a ∂P) = ∫ z : ℝ, g z ∂nu := by
    calc
      _ = ∫ z : ℝ, g z ∂Measure.map (fun a : Shao.Path n => a (Fin.rev i)) P :=
        (integral_map (measurable_pi_apply (Fin.rev i)).aemeasurable hg.aestronglyMeasurable).symm
      _ = _ := by rw [hmap]
  refine ⟨hcur, hint, ?_⟩
  have hh := hind.integral_fun_mul_eq_mul_integral hfi.aestronglyMeasurable hcur.aestronglyMeasurable
  rw [hcurEq] at hh
  exact hh

private theorem bse_bounded_predictable_wald
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (T : Shao.Path n → ℕ) (hT : ∀ a : Shao.Path n, T a ≤ n)
    (g : ℝ → ℝ) (hg : Measurable g) (hgi : Integrable g nu) :
    let S : Fin n → Finset (Fin n) := fun i =>
      Finset.univ.filter (fun j : Fin n => j.val < i.val)
    ∀ c : (i : Fin n) → (S i → ℝ) → ℝ,
      (∀ i : Fin n, Measurable (c i)) →
      (∀ (i : Fin n) (a : Shao.Path n),
        c i (fun j : S i => a (Fin.rev (j : Fin n))) =
          if i.val < T a then 1 else 0) →
      let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
      Integrable (fun a : Shao.Path n => (T a : ℝ)) P ∧
        Integrable (fun a : Shao.Path n =>
          ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < T a),
            g (a (Fin.rev i))) P ∧
        (∫ a : Shao.Path n,
          (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < T a),
            g (a (Fin.rev i))) ∂P) =
          (∫ z : ℝ, g z ∂nu) * (∫ a : Shao.Path n, (T a : ℝ) ∂P) := by
  classical
  intro S c hc hpred P
  let C : Fin n → Shao.Path n → ℝ := fun i a =>
    c i (fun j : S i => a (Fin.rev (j : Fin n)))
  have hCm (i : Fin n) : Measurable (C i) :=
    (hc i).comp (Measurable.of_eval (fun j => measurable_pi_apply (Fin.rev (j : Fin n))))
  have hCi (i : Fin n) : Integrable (C i) P := by
    apply (integrable_const (1 : ℝ)).mono' (hCm i).aestronglyMeasurable
    filter_upwards [] with a
    change |C i a| ≤ 1
    dsimp [C]
    rw [hpred]
    split_ifs <;> norm_num
  have hres (i : Fin n) := bse_reverse_past_factor nu n (S i) i
    (by simp [S]) (c i) (hc i) g hg hgi (hCi i)
  have hcount (a : Shao.Path n) : (∑ i : Fin n, C i a) = (T a : ℝ) := by
    simp only [C, hpred]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
      Fin.card_filter_val_lt, min_eq_right (hT a)]
  have hsum (a : Shao.Path n) :
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < T a), g (a (Fin.rev i))) =
        ∑ i : Fin n, C i a * g (a (Fin.rev i)) := by
    simp only [C, hpred, ite_mul, one_mul, zero_mul, Finset.sum_filter]
  have hTi : Integrable (fun a : Shao.Path n => (T a : ℝ)) P :=
    (integrable_finsetSum Finset.univ (fun i _ => hCi i)).congr (ae_of_all P hcount)
  have hsi : Integrable (fun a : Shao.Path n =>
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < T a), g (a (Fin.rev i))) P :=
    (integrable_finsetSum Finset.univ (fun i _ => (hres i).2.1)).congr
      (ae_of_all P (fun a => (hsum a).symm))
  refine ⟨hTi, hsi, ?_⟩
  simp_rw [hsum]
  rw [integral_finsetSum Finset.univ (fun i _ => (hres i).2.1)]
  simp_rw [fun i => (hres i).2.2]
  rw [← Finset.sum_mul, ← integral_finsetSum Finset.univ (fun i _ => hCi i)]
  simp_rw [hcount]
  ring

private theorem bse_capped_find_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (L : ℕ) (hL : 0 < L) (H : ℝ) (hH : 0 < H)
    (Q : Ω → ℕ → ℝ) (hQm : ∀ k : ℕ, Measurable (fun a : Ω => Q a k))
    (hQ0 : ∀ a : Ω, Q a 0 = 0) (hQ : ∀ a : Ω, Monotone (Q a)) :
    let NH : Ω → ℕ := fun a =>
      @dite ℕ (∃ k : ℕ, k ≤ L ∧ H ≤ Q a k)
        (Classical.propDecidable _)
        (fun h => @Nat.find (fun k : ℕ => k ≤ L ∧ H ≤ Q a k)
          (fun k => Classical.propDecidable _) h)
        (fun _ => L)
    Measurable NH ∧ ∀ a : Ω, 1 ≤ NH a ∧ NH a ≤ L ∧
      ∀ k : ℕ, (k < NH a ↔ k < L ∧ Q a k < H) := by
  classical
  intro NH
  have hdata (a : Ω) := bse_capped_find_data L hL H hH (Q a) (hQ0 a) (hQ a)
  have hchar (a : Ω) (k : ℕ) : k < NH a ↔ k < L ∧ Q a k < H := by
    by_cases hk : k < L
    · have hh := (hdata a).2.2.1 (k + 1) (by omega) (by omega)
      have hindex : k + 1 - 1 = k := by omega
      rw [hindex] at hh
      change (k + 1 ≤ NH a ↔ Q a k < H) at hh
      change (k < NH a ↔ k < L ∧ Q a k < H)
      constructor
      · intro hkn
        exact ⟨hk, hh.mp (by omega)⟩
      · intro hQk
        have hh' := hh.mpr hQk.2
        omega
    · have hbound := (hdata a).2.1
      constructor
      · intro hkn
        change NH a ≤ L at hbound
        omega
      · intro hbad
        exact False.elim (hk hbad.1)
  have hmeas : Measurable NH := by
    apply measurable_of_Ioi
    intro k
    have hset : NH ⁻¹' Set.Ioi k = {a : Ω | k < L ∧ Q a k < H} := by
      ext a
      exact hchar a k
    rw [hset]
    by_cases hk : k < L
    · simp only [hk, true_and]
      exact measurableSet_lt (hQm k) measurable_const
    · simp only [hk, false_and, Set.setOf_false]
      exact MeasurableSet.empty
  refine ⟨hmeas, ?_⟩
  intro a
  exact ⟨(hdata a).1, (hdata a).2.1, hchar a⟩

private theorem bse_prefix_step {n : ℕ} (f : Fin n → ℝ) (k : Fin n) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k.val + 1), f i) =
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k.val), f i) + f k := by
  classical
  have hset : Finset.univ.filter (fun i : Fin n => i.val < k.val + 1) =
      insert k (Finset.univ.filter (fun i : Fin n => i.val < k.val)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hi
      by_cases hik : i = k
      · exact Or.inl hik
      · right
        have hne : i.val ≠ k.val := fun h => hik (Fin.ext h)
        omega
    · intro hi
      rcases hi with rfl | hi <;> omega
  rw [hset, Finset.sum_insert (by simp)]
  ring

private theorem bse_clipped_prefix_bound {n : ℕ}
    (a : Shao.Path n) (H : ℝ) (hH : 0 < H)
    (T : ℕ) (hT0 : 1 ≤ T) (hTn : T ≤ n)
    (hprev : Shao.prefixSquares a (T - 1) < H) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < T), min ((a i) ^ 2) H) ≤ 2 * H := by
  classical
  let k : Fin n := ⟨T - 1, by omega⟩
  have hstep := bse_prefix_step (fun i : Fin n => min ((a i) ^ 2) H) k
  have hindex : k.val + 1 = T := by dsimp [k]; omega
  rw [hindex] at hstep
  rw [hstep]
  have hsum : (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k.val), min ((a i) ^ 2) H) ≤
      Shao.prefixSquares a (T - 1) := by
    apply Finset.sum_le_sum
    intro i _
    exact min_le_left _ _
  have hend : min ((a k) ^ 2) H ≤ H := min_le_right _ _
  linarith only [hsum, hend, hprev]

theorem sourceBackward_capped_stopping_energy_budget
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 4 ≤ n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (H : ℝ) (hR : Shao.truncationBudget nu n 0 ≤ 1 / 2)
    (hH : 4 * Shao.truncationBudget nu n 0 ^ 2 ≤ H) :
    let R : ℝ := Shao.truncationBudget nu n 0
    let L : ℕ := n / 2
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let rev : Shao.Path n → Shao.Path n := fun a i => a (Fin.rev i)
    let Qrev : Shao.Path n → ℕ → ℝ := fun a k => Shao.prefixSquares (rev a) k
    let NH : Shao.Path n → ℕ := fun a =>
      @dite ℕ (∃ k : ℕ, k ≤ L ∧ H ≤ Qrev a k)
        (Classical.propDecidable _)
        (fun h => @Nat.find (fun k : ℕ => k ≤ L ∧ H ≤ Qrev a k)
          (fun k => Classical.propDecidable _) h)
        (fun _ => L)
    ∀ m : ℕ, m ≤ L → (m : ℝ) ≤ 3 * (n : ℝ) * H →
      let N : Shao.Path n → ℕ := fun a => max m (NH a)
      let U : Shao.Path n → ℝ := fun a =>
        Shao.energy a - Shao.prefixSquares a (n - N a)
      Measurable NH ∧ Measurable N ∧ Measurable U ∧
        (∀ a : Shao.Path n, 1 ≤ NH a ∧ NH a ≤ N a ∧ N a ≤ L ∧
          U a = Qrev a (N a)) ∧
        Integrable (fun a : Shao.Path n => (NH a : ℝ)) P ∧
        Integrable (fun a : Shao.Path n => (N a : ℝ)) P ∧ Integrable U P ∧
        (∫ a : Shao.Path n, (NH a : ℝ) ∂P) ≤ 4 * (n : ℝ) * H ∧
        (∫ a : Shao.Path n, (N a : ℝ) ∂P) ≤ 7 * (n : ℝ) * H ∧
        P.real {a : Shao.Path n |
          Shao.energy a - Shao.prefixSquares a (n - L) < H} ≤ 12 * H ∧
        (∫ a : Shao.Path n, U a ∂P) =
          (1 / (n : ℝ)) * (∫ a : Shao.Path n, (N a : ℝ) ∂P) := by
  classical
  intro R L P rev Qrev NH m hmL hmH N U
  have hn0 : 0 < n := by omega
  have hNpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hLn : L ≤ n := Nat.div_le_self n 2
  have hLpos : 0 < L := by dsimp [L]; omega
  obtain ⟨hRp, hHp, hclip, hclipMean⟩ := sourceBackward_clipped_square_mean nu n h2 hnorm H hR hH
  have hrev : Measurable rev := Measurable.of_eval (fun i => measurable_pi_apply (Fin.rev i))
  have hQm (k : ℕ) : Measurable (fun a : Shao.Path n => Qrev a k) :=
    (Shao.measurable_prefixSquares k).comp hrev
  have hfind := bse_capped_find_measurable L hLpos H hHp Qrev hQm
    (fun a => Shao.prefixSquares_zero (rev a)) (fun a => bse_prefixSquares_mono (rev a))
  change Measurable NH ∧ ∀ a : Shao.Path n, 1 ≤ NH a ∧ NH a ≤ L ∧
    ∀ k : ℕ, (k < NH a ↔ k < L ∧ Qrev a k < H) at hfind
  have hNm : Measurable N := measurable_const.max hfind.1
  have hNH0 (a : Shao.Path n) : 1 ≤ NH a := (hfind.2 a).1
  have hNHle (a : Shao.Path n) : NH a ≤ L := (hfind.2 a).2.1
  have hNle (a : Shao.Path n) : N a ≤ L := max_le hmL (hNHle a)
  have hUeq (a : Shao.Path n) : U a = Qrev a (N a) :=
    (bse_reverse_prefixSquares a (N a) ((hNle a).trans hLn)).symm
  have hQjoint : Measurable (fun p : Shao.Path n × ℕ => Qrev p.1 p.2) :=
    measurable_from_prod_countable_left hQm
  have hUm : Measurable U := by
    have hfun : U = fun a : Shao.Path n => Qrev a (N a) := funext hUeq
    rw [hfun]
    exact hQjoint.comp (measurable_id.prodMk hNm)
  let S : Fin n → Finset (Fin n) := fun i =>
    Finset.univ.filter (fun j : Fin n => j.val < i.val)
  let cH : (i : Fin n) → (S i → ℝ) → ℝ := fun i v =>
    if i.val < L then (if (∑ j : S i, (v j) ^ 2) < H then 1 else 0) else 0
  let cN : (i : Fin n) → (S i → ℝ) → ℝ := fun i v =>
    if i.val < m then 1 else cH i v
  have hcH (i : Fin n) : Measurable (cH i) := by
    dsimp [cH]
    split_ifs
    · have hsm : Measurable (fun v : S i → ℝ => ∑ j : S i, (v j) ^ 2) := by fun_prop
      exact Measurable.ite (measurableSet_lt hsm measurable_const) measurable_const measurable_const
    · exact measurable_const
  have hcN (i : Fin n) : Measurable (cN i) := by
    dsimp [cN]
    split_ifs
    · exact measurable_const
    · exact hcH i
  have hsumQ (i : Fin n) (a : Shao.Path n) :
      (∑ j : S i, (a (Fin.rev (j : Fin n))) ^ 2) = Qrev a i.val :=
    Finset.sum_coe_sort (S i) (fun j : Fin n => (a (Fin.rev j)) ^ 2)
  have hpredH (i : Fin n) (a : Shao.Path n) :
      cH i (fun j : S i => a (Fin.rev (j : Fin n))) = if i.val < NH a then 1 else 0 := by
    dsimp only [cH]
    rw [hsumQ]
    simp only [(hfind.2 a).2.2 i.val, ite_and]
  have hpredN (i : Fin n) (a : Shao.Path n) :
      cN i (fun j : S i => a (Fin.rev (j : Fin n))) = if i.val < N a then 1 else 0 := by
    dsimp only [cN, N]
    rw [hpredH]
    by_cases him : i.val < m <;> simp [him, lt_max_iff]
  have wH := bse_bounded_predictable_wald nu n NH (fun a => (hNHle a).trans hLn)
    (fun z : ℝ => min (z ^ 2) H) (by fun_prop) hclip cH hcH hpredH
  have wN := bse_bounded_predictable_wald nu n N (fun a => (hNle a).trans hLn)
    (fun z : ℝ => z ^ 2) (by fun_prop) h2 cN hcN hpredN
  let EH : ℝ := ∫ a : Shao.Path n, (NH a : ℝ) ∂P
  let EN : ℝ := ∫ a : Shao.Path n, (N a : ℝ) ∂P
  have hEH0 : 0 ≤ EH := integral_nonneg (fun a => Nat.cast_nonneg (NH a))
  have hclipBound : (∫ a : Shao.Path n,
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < NH a),
        min ((a (Fin.rev i)) ^ 2) H) ∂P) ≤ 2 * H := by
    have hpoint (a : Shao.Path n) :
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < NH a),
          min ((a (Fin.rev i)) ^ 2) H) ≤ 2 * H := by
      have hprev : Qrev a (NH a - 1) < H :=
        (((hfind.2 a).2.2 (NH a - 1)).mp (by have hh := hNH0 a; omega)).2
      exact bse_clipped_prefix_bound (rev a) H hHp (NH a) (hNH0 a)
        ((hNHle a).trans hLn) hprev
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
      integral_mono wH.2.1 (integrable_const (2 * H)) hpoint
  have hEH : EH ≤ 4 * (n : ℝ) * H := by
    rw [wH.2.2] at hclipBound
    have hh := mul_le_mul_of_nonneg_right hclipMean hEH0
    have hh' := mul_le_mul_of_nonneg_left hclipBound hNpos.le
    dsimp [EH] at *
    nlinarith only [hh, hh']
  have hEN : EN ≤ 7 * (n : ℝ) * H := by
    have hpoint (a : Shao.Path n) : (N a : ℝ) ≤ (m : ℝ) + (NH a : ℝ) := by
      have hh : N a ≤ m + NH a := by dsimp [N]; omega
      exact_mod_cast hh
    have hh := integral_mono wN.1 ((integrable_const (m : ℝ)).add wH.1) hpoint
    change EN ≤ ∫ a : Shao.Path n, (m : ℝ) + (NH a : ℝ) ∂P at hh
    rw [integral_add (integrable_const (m : ℝ)) wH.1] at hh
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
    change EN ≤ (m : ℝ) + EH at hh
    linarith only [hh, hmH, hEH]
  let Efail : Set (Shao.Path n) := {a | Shao.energy a - Shao.prefixSquares a (n - L) < H}
  have hfailm : MeasurableSet Efail := measurableSet_lt
    (Shao.measurable_energy.sub (Shao.measurable_prefixSquares (n - L))) measurable_const
  have hfailQ (a : Shao.Path n) : Shao.energy a - Shao.prefixSquares a (n - L) = Qrev a L :=
    (bse_reverse_prefixSquares a L hLn).symm
  have hfailNH (a : Shao.Path n) (ha : a ∈ Efail) : NH a = L := by
    have hq : Qrev a L < H := by change _ < H at ha; rwa [hfailQ a] at ha
    by_contra hh
    have hlt : NH a < L := by have hh' := hNHle a; omega
    have hnext := ((hfind.2 a).2.2 (NH a)).mpr ⟨hlt, (bse_prefixSquares_mono (rev a) (hNHle a)).trans_lt hq⟩
    exact (lt_irrefl (NH a)) hnext
  have hmarkov : (L : ℝ) * P.real Efail ≤ EH := by
    have hi : Integrable (Efail.indicator (fun _ : Shao.Path n => (L : ℝ))) P :=
      (integrable_const (L : ℝ)).indicator hfailm
    have hpoint (a : Shao.Path n) : Efail.indicator (fun _ => (L : ℝ)) a ≤ (NH a : ℝ) := by
      by_cases ha : a ∈ Efail
      · rw [Set.indicator_of_mem ha, hfailNH a ha]
      · rw [Set.indicator_of_notMem ha]
        exact Nat.cast_nonneg _
    have hh := integral_mono hi wH.1 hpoint
    rw [integral_indicator_const _ hfailm, smul_eq_mul] at hh
    dsimp [EH]
    nlinarith only [hh]
  have hLratio : (n : ℝ) / 3 ≤ (L : ℝ) := by
    have hh : n ≤ 3 * L := by dsimp [L]; omega
    have hh' : (n : ℝ) ≤ 3 * (L : ℝ) := by exact_mod_cast hh
    linarith only [hh']
  have hfail : P.real Efail ≤ 12 * H := by
    apply (mul_le_mul_iff_right₀ hNpos).mp
    have hh := mul_le_mul_of_nonneg_right hLratio (measureReal_nonneg (μ := P) (s := Efail))
    nlinarith only [hh, hmarkov, hEH]
  have hsumU (a : Shao.Path n) :
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < N a), (a (Fin.rev i)) ^ 2) = U a :=
    bse_reverse_prefixSquares a (N a) ((hNle a).trans hLn)
  have hUi : Integrable U P := wN.2.1.congr (ae_of_all P hsumU)
  have hEU : (∫ a : Shao.Path n, U a ∂P) = (1 / (n : ℝ)) * EN := by
    have hh := wN.2.2
    simp_rw [hsumU] at hh
    have hsecondEq : (∫ z : ℝ, z ^ 2 ∂nu) = 1 / (n : ℝ) := by
      apply (eq_div_iff hNpos.ne').2
      nlinarith only [hnorm]
    simpa only [hsecondEq] using hh
  refine ⟨hfind.1, hNm, hUm, ?_, wH.1, wN.1, hUi, hEH, hEN, hfail, hEU⟩
  intro a
  exact ⟨hNH0 a, le_max_right _ _, hNle a, hUeq a⟩

private theorem bse_forward_displacement_control {n : ℕ}
    (a : Shao.Path n) (N : ℕ) (hN : N ≤ n) :
    let B : ℕ → ℝ := fun k => Shao.prefixSum (fun i : Fin n => a (Fin.rev i)) k
    let K : ℝ := (Finset.Icc 0 N).sup' (by exact ⟨0, by simp⟩) (fun k => |B k|)
    let J : ℝ := (Finset.Icc 0 N).sup' (by exact ⟨0, by simp⟩)
      (fun l => |Shao.prefixSum a (n - N + l) - Shao.prefixSum a (n - N)|)
    0 ≤ K ∧ 0 ≤ J ∧ J ≤ 2 * K := by
  intro B K J
  have hK (k : ℕ) (hk : k ≤ N) : |B k| ≤ K :=
    Finset.le_sup' (fun k => |B k|) (by simp only [Finset.mem_Icc]; omega)
  have hK0 : 0 ≤ K := (abs_nonneg (B 0)).trans (hK 0 (Nat.zero_le N))
  have hJ0 : 0 ≤ J := (abs_nonneg (Shao.prefixSum a (n - N + 0) - Shao.prefixSum a (n - N))).trans
    (Finset.le_sup' (fun l : ℕ =>
      |Shao.prefixSum a (n - N + l) - Shao.prefixSum a (n - N)|)
      (show (0 : ℕ) ∈ Finset.Icc 0 N by simp))
  refine ⟨hK0, hJ0, ?_⟩
  apply Finset.sup'_le
  intro l hl
  have hlN : l ≤ N := (Finset.mem_Icc.mp hl).2
  have hidx : n - (N - l) = n - N + l := by omega
  have hgeom : Shao.prefixSum a (n - N + l) - Shao.prefixSum a (n - N) = B N - B (N - l) := by
    dsimp [B]
    rw [bse_reverse_prefixSum a N hN,
      bse_reverse_prefixSum a (N - l) (by omega), hidx]
    ring
  rw [hgeom]
  exact (abs_sub (B N) (B (N - l))).trans (by linarith only [hK N le_rfl, hK (N - l) (by omega)])

private theorem bse_reverse_factor_of_dep
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (i : Fin n)
    (F : Shao.Path n → ℝ) (hFm : Measurable F)
    (hFi : Integrable F (Measure.pi (fun _ : Fin n => nu)))
    (hdep : ∀ a b : Shao.Path n,
      (∀ j : Fin n, j.val < i.val → a (Fin.rev j) = b (Fin.rev j)) → F a = F b)
    (g : ℝ → ℝ) (hg : Measurable g) (hgi : Integrable g nu) :
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    Integrable (fun a : Shao.Path n => g (a (Fin.rev i))) P ∧
      Integrable (fun a : Shao.Path n => F a * g (a (Fin.rev i))) P ∧
      (∫ a : Shao.Path n, F a * g (a (Fin.rev i)) ∂P) =
        (∫ a : Shao.Path n, F a ∂P) * (∫ z : ℝ, g z ∂nu) := by
  classical
  intro P
  let s : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => j.val < i.val)
  let ext : (s → ℝ) → Shao.Path n := fun v q =>
    if h : Fin.rev q ∈ s then v ⟨Fin.rev q, h⟩ else 0
  have hEm : Measurable ext := by
    apply Measurable.of_eval
    intro q
    dsimp [ext]
    split_ifs with h
    · exact measurable_pi_apply (X := fun _ : s => ℝ) (⟨Fin.rev q, h⟩ : s)
    · exact measurable_const
  let f : (s → ℝ) → ℝ := fun v => F (ext v)
  have hfm : Measurable f := hFm.comp hEm
  have hrep (a : Shao.Path n) : f (fun j : s => a (Fin.rev (j : Fin n))) = F a := by
    apply hdep
    intro j hj
    have hjs : j ∈ s := by simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]; exact hj
    dsimp [ext]
    simp only [Fin.rev_rev, ite_eq_left hjs, dite_eq_left hjs]
  have hfi : Integrable (fun a : Shao.Path n =>
      f (fun j : s => a (Fin.rev (j : Fin n)))) P :=
    hFi.congr (ae_of_all P (fun a => (hrep a).symm))
  have hh := bse_reverse_past_factor nu n s i (by simp [s]) f hfm g hg hgi hfi
  dsimp only at hh
  simpa only [hrep] using hh

private theorem bse_stopped_second
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (T : Shao.Path n → ℕ) (hTm : Measurable T)
    (hTn : ∀ a : Shao.Path n, T a ≤ n)
    (hdep : ∀ (i : Fin n) (a b : Shao.Path n),
      (∀ j : Fin n, j.val < i.val → a (Fin.rev j) = b (Fin.rev j)) →
        (i.val < T a ↔ i.val < T b)) :
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let B : Shao.Path n → ℕ → ℝ := fun a k =>
      Shao.prefixSum (fun i : Fin n => a (Fin.rev i)) k
    Integrable (fun a : Shao.Path n => (B a (T a)) ^ 2) P ∧
      (∫ a : Shao.Path n, (B a (T a)) ^ 2 ∂P) =
        (∫ z : ℝ, z ^ 2 ∂nu) * (∫ a : Shao.Path n, (T a : ℝ) ∂P) := by
  classical
  intro P B
  let A : Fin n → Shao.Path n → ℝ := fun i a => if i.val < T a then 1 else 0
  let D : Fin n → Shao.Path n → ℝ := fun i a => if i.val < T a then a (Fin.rev i) else 0
  have h1 : Integrable (fun z : ℝ => z) nu := by
    apply ((integrable_const (1 : ℝ)).add h2).mono' measurable_id.aestronglyMeasurable
    filter_upwards [] with z
    change |z| ≤ 1 + z ^ 2
    nlinarith only [sq_nonneg (|z| - 1), sq_abs z]
  have hset (i : Fin n) : MeasurableSet {a : Shao.Path n | i.val < T a} :=
    measurableSet_lt measurable_const hTm
  have hAm (i : Fin n) : Measurable (A i) :=
    Measurable.ite (hset i) measurable_const measurable_const
  have hAi (i : Fin n) : Integrable (A i) P := by
    apply (integrable_const (1 : ℝ)).mono' (hAm i).aestronglyMeasurable
    filter_upwards [] with a
    change |A i a| ≤ 1
    dsimp [A]
    split_ifs <;> norm_num
  have hDm (i : Fin n) : Measurable (D i) :=
    Measurable.ite (hset i) (measurable_pi_apply (Fin.rev i)) measurable_const
  have hDi (i : Fin n) : Integrable (D i) P := by
    have hh := ((measurePreserving_eval (fun _ : Fin n => nu) (Fin.rev i)).integrable_comp_of_integrable h1).indicator (hset i)
    apply hh.congr
    filter_upwards [] with a
    by_cases ha : i.val < T a <;> simp [D, Set.indicator, ha, Function.comp_def]
  have hAdep (i : Fin n) (a b : Shao.Path n)
      (hab : ∀ j : Fin n, j.val < i.val → a (Fin.rev j) = b (Fin.rev j)) : A i a = A i b := by
    have hh := hdep i a b hab
    by_cases ha : i.val < T a
    · have hb := hh.mp ha
      simp only [A, ha, hb, ite_true]
    · have hb : ¬i.val < T b := fun hb => ha (hh.mpr hb)
      simp only [A, ha, hb, ite_false]
  have hDpast (i j : Fin n) (hij : i.val < j.val) (a b : Shao.Path n)
      (hab : ∀ k : Fin n, k.val < j.val → a (Fin.rev k) = b (Fin.rev k)) : D i a = D i b := by
    have hcoord := hab i hij
    have htail := hdep i a b (fun k hk => hab k (hk.trans hij))
    by_cases ha : i.val < T a
    · have hb := htail.mp ha
      simpa only [D, ha, hb, ite_true] using hcoord
    · have hb : ¬i.val < T b := fun hb => ha (htail.mpr hb)
      simp only [D, ha, hb, ite_false]
  have hdiag (i : Fin n) : Integrable (fun a : Shao.Path n => D i a * D i a) P ∧
      (∫ a : Shao.Path n, D i a * D i a ∂P) =
        (∫ a : Shao.Path n, A i a ∂P) * (∫ z : ℝ, z ^ 2 ∂nu) := by
    have hh := bse_reverse_factor_of_dep nu n i (A i) (hAm i) (hAi i) (hAdep i)
      (fun z : ℝ => z ^ 2) (by fun_prop) h2
    have hpoint (a : Shao.Path n) : A i a * (a (Fin.rev i)) ^ 2 = D i a * D i a := by
      by_cases ha : i.val < T a <;> simp only [A, D, ha, ite_true, ite_false, one_mul, zero_mul, pow_two]
    refine ⟨hh.2.1.congr (ae_of_all P hpoint), ?_⟩
    simpa only [hpoint] using hh.2.2
  have hoff (i j : Fin n) (hij : i.val < j.val) :
      Integrable (fun a : Shao.Path n => D i a * D j a) P ∧
        (∫ a : Shao.Path n, D i a * D j a ∂P) = 0 := by
    let F : Shao.Path n → ℝ := fun a => if j.val < T a then D i a else 0
    have hFm : Measurable F := Measurable.ite (hset j) (hDm i) measurable_const
    have hFi : Integrable F P := by
      apply ((hDi i).indicator (hset j)).congr
      filter_upwards [] with a
      by_cases ha : j.val < T a <;> simp [F, Set.indicator, ha]
    have hFdep (a b : Shao.Path n)
        (hab : ∀ k : Fin n, k.val < j.val → a (Fin.rev k) = b (Fin.rev k)) : F a = F b := by
      have htail := hdep j a b hab
      have hD := hDpast i j hij a b hab
      by_cases ha : j.val < T a
      · have hb := htail.mp ha
        simpa only [F, ha, hb, ite_true] using hD
      · have hb : ¬j.val < T b := fun hb => ha (htail.mpr hb)
        simp only [F, ha, hb, ite_false]
    have hh := bse_reverse_factor_of_dep nu n j F hFm hFi hFdep
      (fun z : ℝ => z) measurable_id h1
    have hpoint (a : Shao.Path n) : F a * a (Fin.rev j) = D i a * D j a := by
      by_cases ha : j.val < T a <;> simp only [F, D, ha, ite_true, ite_false, mul_zero, zero_mul]
    refine ⟨hh.2.1.congr (ae_of_all P hpoint), ?_⟩
    simpa only [hpoint, hmean, mul_zero] using hh.2.2
  have hpair (i j : Fin n) : Integrable (fun a : Shao.Path n => D i a * D j a) P ∧
      (∫ a : Shao.Path n, D i a * D j a ∂P) =
        if i = j then (∫ a : Shao.Path n, A i a ∂P) * (∫ z : ℝ, z ^ 2 ∂nu) else 0 := by
    by_cases heq : i = j
    · subst j
      simpa only [ite_true] using hdiag i
    · by_cases hij : i.val < j.val
      · simpa only [heq, ite_false] using hoff i j hij
      · have hji : j.val < i.val := by have hh : i.val ≠ j.val := fun h => heq (Fin.ext h); omega
        have hh := hoff j i hji
        simpa only [mul_comm, heq, ite_false] using hh
  have hBsum (a : Shao.Path n) : B a (T a) = ∑ i : Fin n, D i a := by
    simp only [B, Shao.prefixSum, D, Finset.sum_filter]
  have hsquare (a : Shao.Path n) : (B a (T a)) ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, D i a * D j a := by
    rw [hBsum, pow_two, Finset.sum_mul_sum]
  have hsi : Integrable (fun a : Shao.Path n => ∑ i : Fin n, ∑ j : Fin n, D i a * D j a) P :=
    integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => (hpair i j).1))
  have hbi : Integrable (fun a : Shao.Path n => (B a (T a)) ^ 2) P :=
    hsi.congr (ae_of_all P (fun a => (hsquare a).symm))
  have hcount (a : Shao.Path n) : (∑ i : Fin n, A i a) = (T a : ℝ) := by
    simp only [A]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
      Fin.card_filter_val_lt, min_eq_right (hTn a)]
  refine ⟨hbi, ?_⟩
  simp_rw [hsquare]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => (hpair i j).1))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => (hpair _ j).1)]
  simp_rw [fun i j => (hpair i j).2]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.sum_mul, ← integral_finsetSum Finset.univ (fun i _ => hAi i)]
  simp_rw [hcount]
  ring

private theorem bse_maximal_weights (M : ℕ → ℝ) (hM0 : M 0 = 0) (L : ℕ) :
    let K : ℕ → ℝ := fun k => Nat.rec (motive := fun _ => ℝ) 0
      (fun j v => max v |M (j + 1)|) k
    let W : ℕ → ℝ := fun k =>
      (if 0 ≤ M (k + 1) then 1 else -1) * (K (k + 1) - K k)
    (∀ k : ℕ, 0 ≤ K k ∧
      K k = (Finset.Icc 0 k).sup' (by exact ⟨0, by simp⟩) (fun j => |M j|)) ∧
      (∀ k : ℕ, 0 ≤ K (k + 1) - K k) ∧
      (∀ k : ℕ, |W k| = K (k + 1) - K k) ∧
      K L ^ 2 ≤ 2 * (∑ k ∈ Finset.range L, M (k + 1) * W k) ∧
      |∑ k ∈ Finset.range L, W k| ≤ K L ∧
      (∀ k : ℕ, k < L → |W k| ≤ K L) := by
  intro K W
  have hK0 : K 0 = 0 := rfl
  have hKsucc (k : ℕ) : K (k + 1) = max (K k) |M (k + 1)| := rfl
  have hKnonneg (k : ℕ) : 0 ≤ K k := by
    cases k with
    | zero => rw [hK0]
    | succ k => exact (abs_nonneg _).trans (le_max_right _ _)
  have hKdom (k : ℕ) : ∀ j : ℕ, j ≤ k → |M j| ≤ K k := by
    induction k with
    | zero =>
      intro j hj
      have hj0 : j = 0 := by omega
      rw [hj0, hM0, hK0, abs_zero]
    | succ k ih =>
      intro j hj
      by_cases hjk : j ≤ k
      · exact (ih j hjk).trans (le_max_left _ _)
      · have heq : j = k + 1 := by omega
        rw [heq]
        exact le_max_right _ _
  have hKupper (k : ℕ) (Z : ℝ) (hZ : 0 ≤ Z)
      (hbound : ∀ j : ℕ, j ≤ k → |M j| ≤ Z) : K k ≤ Z := by
    induction k with
    | zero => exact hZ
    | succ k ih =>
      rw [hKsucc]
      exact max_le (ih (fun j hj => hbound j (by omega))) (hbound (k + 1) le_rfl)
  have hKsup (k : ℕ) :
      K k = (Finset.Icc 0 k).sup' (by exact ⟨0, by simp⟩) (fun j => |M j|) := by
    apply le_antisymm
    · apply hKupper
      · exact (abs_nonneg (M 0)).trans
          (Finset.le_sup' (fun j : ℕ => |M j|) (show (0 : ℕ) ∈ Finset.Icc 0 k by simp))
      · intro j hj
        exact Finset.le_sup' (fun j : ℕ => |M j|) (by simp only [Finset.mem_Icc]; omega)
    · apply Finset.sup'_le
      intro j hj
      exact hKdom k j (Finset.mem_Icc.mp hj).2
  have hdelta (k : ℕ) : 0 ≤ K (k + 1) - K k :=
    sub_nonneg.mpr (le_max_left _ _)
  have hWabs (k : ℕ) : |W k| = K (k + 1) - K k := by
    dsimp [W]
    rw [abs_mul, abs_of_nonneg (hdelta k)]
    split_ifs <;> norm_num
  have hprod (k : ℕ) : M (k + 1) * W k = |M (k + 1)| * (K (k + 1) - K k) := by
    dsimp [W]
    by_cases hk : 0 ≤ M (k + 1)
    · rw [ite_eq_left hk, abs_of_nonneg hk]
      ring
    · rw [ite_eq_right hk, abs_of_neg (lt_of_not_ge hk)]
      ring
  have hstep (k : ℕ) : K (k + 1) ^ 2 - K k ^ 2 ≤ 2 * (M (k + 1) * W k) := by
    rw [hprod, hKsucc]
    by_cases hk : K k ≤ |M (k + 1)|
    · rw [max_eq_right hk]
      nlinarith only [sq_nonneg (|M (k + 1)| - K k)]
    · rw [max_eq_left (le_of_not_ge hk)]
      simp only [sub_self, mul_zero, le_refl]
  have htel (k : ℕ) :
      (∑ j ∈ Finset.range k, (K (j + 1) ^ 2 - K j ^ 2)) = K k ^ 2 := by
    induction k with
    | zero => simp [hK0]
    | succ k ih => rw [Finset.sum_range_succ, ih]; ring
  have hsumdelta (k : ℕ) :
      (∑ j ∈ Finset.range k, (K (j + 1) - K j)) = K k := by
    induction k with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, hK0]
    | succ k ih => rw [Finset.sum_range_succ, ih]; ring
  have hsq : K L ^ 2 ≤ 2 * (∑ k ∈ Finset.range L, M (k + 1) * W k) := by
    have hh := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range L) => hstep k)
    simpa only [htel, Finset.mul_sum] using hh
  have hsumW : |∑ k ∈ Finset.range L, W k| ≤ K L := by
    have hh := Finset.abs_sum_le_sum_abs W (Finset.range L)
    simp_rw [hWabs] at hh
    rw [hsumdelta] at hh
    exact hh
  refine ⟨fun k => ⟨hKnonneg k, hKsup k⟩, hdelta, hWabs, hsq, hsumW, ?_⟩
  intro k hk
  rw [hWabs]
  have hnext : K (k + 1) ≤ K L :=
    hKupper (k + 1) (K L) (hKnonneg L) (fun j hj => hKdom L j (by omega))
  linarith only [hnext, hKnonneg k]

private theorem bse_prefix_sum_sq_bound {n : ℕ} (a : Shao.Path n) (k : ℕ) :
    Shao.prefixSum a k ^ 2 ≤ (n : ℝ) * Shao.energy a := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => i.val < k)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ : Fin n => (1 : ℝ)) a
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hcard : (s.card : ℝ) ≤ n := by
    exact_mod_cast (show s.card ≤ n by simpa only [Fintype.card_fin] using (Finset.card_le_univ s))
  have hsum : (∑ i ∈ s, (a i) ^ 2) ≤ Shao.energy a :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => sq_nonneg _)
  exact hcs.trans (mul_le_mul hcard hsum
    (Finset.sum_nonneg (fun i _ => sq_nonneg (a i))) (Nat.cast_nonneg n))

private theorem bse_integrable_energy
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu) :
    Integrable (Shao.energy : Shao.Path n → ℝ) (Measure.pi (fun _ : Fin n => nu)) := by
  exact integrable_finsetSum Finset.univ (fun i _ =>
    (measurePreserving_eval (fun _ : Fin n => nu) i).integrable_comp_of_integrable h2)

private theorem bse_finite_max_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (F : Ω → ℕ → ℝ)
    (hF : ∀ k : ℕ, Measurable (fun a : Ω => F a k))
    (hF0 : ∀ a : Ω, F a 0 = 0) (k : ℕ) :
    Measurable (fun a : Ω =>
      (Finset.Icc 0 k).sup' (by exact ⟨0, by simp⟩) (fun j => |F a j|)) := by
  classical
  let A : Ω → ℕ → ℝ := fun a j => Nat.rec (motive := fun _ => ℝ) 0
    (fun l v => max v |F a (l + 1)|) j
  have hAm (j : ℕ) : Measurable (fun a : Ω => A a j) := by
    induction j with
    | zero => exact measurable_const
    | succ j ih =>
      have hf : Measurable (fun a : Ω => |F a (j + 1)|) := by
        simpa only [Real.norm_eq_abs] using (hF (j + 1)).norm
      exact ih.max hf
  have heq (a : Ω) : A a k =
      (Finset.Icc 0 k).sup' (by exact ⟨0, by simp⟩) (fun j => |F a j|) :=
    ((bse_maximal_weights (F a) (hF0 a) k).1 k).2
  have hfun : (fun a : Ω =>
      (Finset.Icc 0 k).sup' (by exact ⟨0, by simp⟩) (fun j => |F a j|)) =
      fun a : Ω => A a k := funext (fun a => (heq a).symm)
  rw [hfun]
  exact hAm k

private theorem bse_bounded_stopped_path_measurable
    (n : ℕ) (T : Shao.Path n → ℕ) (hTm : Measurable T)
    (hTn : ∀ a : Shao.Path n, T a ≤ n) :
    let B : Shao.Path n → ℕ → ℝ := fun a k =>
      Shao.prefixSum (fun i : Fin n => a (Fin.rev i)) k
    let K : Shao.Path n → ℝ := fun a =>
      (Finset.Icc 0 (T a)).sup' (by exact ⟨0, by simp⟩) (fun k => |B a k|)
    let J : Shao.Path n → ℝ := fun a =>
      (Finset.Icc 0 (T a)).sup' (by exact ⟨0, by simp⟩)
        (fun l => |Shao.prefixSum a (n - T a + l) - Shao.prefixSum a (n - T a)|)
    Measurable (fun a : Shao.Path n => B a (T a)) ∧ Measurable K ∧ Measurable J := by
  classical
  intro B K J
  have hrev : Measurable (fun a : Shao.Path n => fun i : Fin n => a (Fin.rev i)) :=
    Measurable.of_eval (fun i => measurable_pi_apply (Fin.rev i))
  have hBm (k : ℕ) : Measurable (fun a : Shao.Path n => B a k) :=
    (Shao.measurable_prefixSum k).comp hrev
  have hBjoint : Measurable (fun p : Shao.Path n × ℕ => B p.1 p.2) :=
    measurable_from_prod_countable_left hBm
  have hBTm : Measurable (fun a : Shao.Path n => B a (T a)) :=
    hBjoint.comp (measurable_id.prodMk hTm)
  have hSjoint : Measurable (fun p : Shao.Path n × ℕ => Shao.prefixSum p.1 p.2) :=
    measurable_from_prod_countable_left (fun k => Shao.measurable_prefixSum (n := n) k)
  let F : Shao.Path n → ℕ → ℝ := fun a k => if k ≤ T a then B a k else 0
  let G : Shao.Path n → ℕ → ℝ := fun a k => if k ≤ T a then
    Shao.prefixSum a (n - T a + k) - Shao.prefixSum a (n - T a) else 0
  have hFm (k : ℕ) : Measurable (fun a : Shao.Path n => F a k) :=
    Measurable.ite (measurableSet_le measurable_const hTm) (hBm k) measurable_const
  have hGm (k : ℕ) : Measurable (fun a : Shao.Path n => G a k) := by
    have hi : Measurable (fun a : Shao.Path n => n - T a + k) :=
      (show Measurable (fun l : ℕ => n - l + k) from measurable_of_countable (fun l : ℕ => n - l + k)).comp hTm
    have hi0 : Measurable (fun a : Shao.Path n => n - T a) :=
      (show Measurable (fun l : ℕ => n - l) from measurable_of_countable (fun l : ℕ => n - l)).comp hTm
    exact Measurable.ite (measurableSet_le measurable_const hTm)
      ((hSjoint.comp (measurable_id.prodMk hi)).sub
        (hSjoint.comp (measurable_id.prodMk hi0))) measurable_const
  have hF0 (a : Shao.Path n) : F a 0 = 0 := by simp [F, B, Shao.prefixSum_zero]
  have hG0 (a : Shao.Path n) : G a 0 = 0 := by simp [G]
  have hFmMax := bse_finite_max_measurable F hFm hF0 n
  have hGmMax := bse_finite_max_measurable G hGm hG0 n
  have hgeom (a : Shao.Path n) : 0 ≤ K a ∧ 0 ≤ J a ∧ J a ≤ 2 * K a :=
    bse_forward_displacement_control a (T a) (hTn a)
  have hFeq (a : Shao.Path n) :
      (Finset.Icc 0 n).sup' (by exact ⟨0, by simp⟩) (fun k => |F a k|) = K a := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro k hk
      by_cases hkt : k ≤ T a
      · have hh := Finset.le_sup' (fun l => |B a l|)
          (show k ∈ Finset.Icc 0 (T a) from Finset.mem_Icc.mpr ⟨Nat.zero_le _, hkt⟩)
        simpa only [F, hkt, ite_true] using hh
      · simpa only [F, hkt, ite_false, abs_zero] using (hgeom a).1
    · apply Finset.sup'_le
      intro k hk
      have hkt := (Finset.mem_Icc.mp hk).2
      have hh := Finset.le_sup' (fun l => |F a l|)
        (show k ∈ Finset.Icc 0 n from Finset.mem_Icc.mpr ⟨Nat.zero_le _, hkt.trans (hTn a)⟩)
      simpa only [F, hkt, ite_true] using hh
  have hGeq (a : Shao.Path n) :
      (Finset.Icc 0 n).sup' (by exact ⟨0, by simp⟩) (fun k => |G a k|) = J a := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro k hk
      by_cases hkt : k ≤ T a
      · have hh := Finset.le_sup'
          (fun l => |Shao.prefixSum a (n - T a + l) - Shao.prefixSum a (n - T a)|)
          (show k ∈ Finset.Icc 0 (T a) from Finset.mem_Icc.mpr ⟨Nat.zero_le _, hkt⟩)
        simpa only [G, hkt, ite_true] using hh
      · simpa only [G, hkt, ite_false, abs_zero] using (hgeom a).2.1
    · apply Finset.sup'_le
      intro k hk
      have hkt := (Finset.mem_Icc.mp hk).2
      have hh := Finset.le_sup' (fun l => |G a l|)
        (show k ∈ Finset.Icc 0 n from Finset.mem_Icc.mpr ⟨Nat.zero_le _, hkt.trans (hTn a)⟩)
      simpa only [G, hkt, ite_true] using hh
  have hKm : Measurable K := by
    have heq : (fun a : Shao.Path n =>
        (Finset.Icc 0 n).sup' (by exact ⟨0, by simp⟩) (fun k => |F a k|)) = K := funext hFeq
    rw [← heq]
    exact hFmMax
  have hJm : Measurable J := by
    have heq : (fun a : Shao.Path n =>
        (Finset.Icc 0 n).sup' (by exact ⟨0, by simp⟩) (fun k => |G a k|)) = J := funext hGeq
    rw [← heq]
    exact hGmMax
  exact ⟨hBTm, hKm, hJm⟩

private theorem bse_stopped_max_data
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (T : Shao.Path n → ℕ) (hTm : Measurable T)
    (hTn : ∀ a : Shao.Path n, T a ≤ n) :
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let B : Shao.Path n → ℕ → ℝ := fun a k =>
      Shao.prefixSum (fun i : Fin n => a (Fin.rev i)) k
    let K : Shao.Path n → ℝ := fun a =>
      (Finset.Icc 0 (T a)).sup' (by exact ⟨0, by simp⟩) (fun k => |B a k|)
    let J : Shao.Path n → ℝ := fun a =>
      (Finset.Icc 0 (T a)).sup' (by exact ⟨0, by simp⟩)
        (fun l => |Shao.prefixSum a (n - T a + l) - Shao.prefixSum a (n - T a)|)
    Measurable (fun a : Shao.Path n => B a (T a)) ∧ Measurable K ∧ Measurable J ∧
      Integrable (fun a : Shao.Path n => (B a (T a)) ^ 2) P ∧
      Integrable (fun a : Shao.Path n => K a ^ 2) P ∧
      Integrable (fun a : Shao.Path n => J a ^ 2) P ∧
      (∀ a : Shao.Path n, 0 ≤ K a ∧ 0 ≤ J a ∧ J a ≤ 2 * K a) := by
  classical
  intro P B K J
  obtain ⟨hBTm, hKm, hJm⟩ := bse_bounded_stopped_path_measurable n T hTm hTn
  have hgeom (a : Shao.Path n) : 0 ≤ K a ∧ 0 ≤ J a ∧ J a ≤ 2 * K a :=
    bse_forward_displacement_control a (T a) (hTn a)
  have hrevE (a : Shao.Path n) : Shao.energy (fun i : Fin n => a (Fin.rev i)) = Shao.energy a := by
    simpa only [Shao.prefixSquares_length, Nat.sub_self, Shao.prefixSquares_zero, sub_zero] using
      bse_reverse_prefixSquares a n le_rfl
  have hBsquare (a : Shao.Path n) (k : ℕ) : (B a k) ^ 2 ≤ (n : ℝ) * Shao.energy a := by
    have hh := bse_prefix_sum_sq_bound (fun i : Fin n => a (Fin.rev i)) k
    rwa [hrevE] at hh
  have hKsquare (a : Shao.Path n) : K a ^ 2 ≤ (n : ℝ) * Shao.energy a := by
    let V : ℝ := (n : ℝ) * Shao.energy a
    have hV : 0 ≤ V := mul_nonneg (Nat.cast_nonneg n) (Shao.energy_nonneg a)
    have hKroot : K a ≤ Real.sqrt V := by
      apply Finset.sup'_le
      intro k _
      apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
      rw [sq_abs, Real.sq_sqrt hV]
      exact hBsquare a k
    have hh := pow_le_pow_left₀ (hgeom a).1 hKroot 2
    rwa [Real.sq_sqrt hV] at hh
  have hEi := (bse_integrable_energy nu n h2).const_mul (n : ℝ)
  have hBTi : Integrable (fun a : Shao.Path n => (B a (T a)) ^ 2) P := by
    apply hEi.mono' (hBTm.pow_const 2).aestronglyMeasurable
    filter_upwards [] with a
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hBsquare a (T a)
  have hKi : Integrable (fun a : Shao.Path n => K a ^ 2) P := by
    apply hEi.mono' (hKm.pow_const 2).aestronglyMeasurable
    filter_upwards [] with a
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hKsquare a
  have hJi : Integrable (fun a : Shao.Path n => J a ^ 2) P := by
    apply (hKi.const_mul 4).mono' (hJm.pow_const 2).aestronglyMeasurable
    filter_upwards [] with a
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hh := pow_le_pow_left₀ (hgeom a).2.1 (hgeom a).2.2 2
    nlinarith only [hh]
  exact ⟨hBTm, hKm, hJm, hBTi, hKi, hJi, hgeom⟩

private theorem bse_stopped_prefix_dep {n : ℕ}
    (T : Shao.Path n → ℕ)
    (hdep : ∀ (i : Fin n) (a b : Shao.Path n),
      (∀ j : Fin n, j.val < i.val → a (Fin.rev j) = b (Fin.rev j)) →
        (i.val < T a ↔ i.val < T b))
    (k : ℕ) (a b : Shao.Path n)
    (hab : ∀ j : Fin n, j.val < k → a (Fin.rev j) = b (Fin.rev j)) :
    Shao.prefixSum (fun i : Fin n => a (Fin.rev i)) (min k (T a)) =
      Shao.prefixSum (fun i : Fin n => b (Fin.rev i)) (min k (T b)) := by
  classical
  simp only [Shao.prefixSum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hik : i.val < k
  · have hcoord := hab i hik
    have ht := hdep i a b (fun j hj => hab j (hj.trans hik))
    by_cases ha : i.val < T a
    · have hb := ht.mp ha
      simp only [lt_min_iff, hik, ha, hb, and_self, ite_true, hcoord]
    · have hb : ¬i.val < T b := fun hb => ha (ht.mpr hb)
      simp only [lt_min_iff, hik, ha, hb, and_false, ite_false]
  · simp only [lt_min_iff, hik, false_and, ite_false]

private theorem bse_stopped_tail_test
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (T : Shao.Path n → ℕ) (hTm : Measurable T)
    (hTn : ∀ a : Shao.Path n, T a ≤ n)
    (hdep : ∀ (i : Fin n) (a b : Shao.Path n),
      (∀ j : Fin n, j.val < i.val → a (Fin.rev j) = b (Fin.rev j)) →
        (i.val < T a ↔ i.val < T b))
    (k : ℕ) (F : Shao.Path n → ℝ) (hFm : Measurable F)
    (hFi : Integrable F (Measure.pi (fun _ : Fin n => nu)))
    (hFdep : ∀ a b : Shao.Path n,
      (∀ j : Fin n, j.val < k → a (Fin.rev j) = b (Fin.rev j)) → F a = F b) :
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let B : Shao.Path n → ℕ → ℝ := fun a l =>
      Shao.prefixSum (fun i : Fin n => a (Fin.rev i)) l
    Integrable (fun a : Shao.Path n => F a * (B a (T a) - B a (min k (T a)))) P ∧
      (∫ a : Shao.Path n, F a * (B a (T a) - B a (min k (T a))) ∂P) = 0 := by
  classical
  intro P B
  have h1 : Integrable (fun z : ℝ => z) nu := by
    apply ((integrable_const (1 : ℝ)).add h2).mono' measurable_id.aestronglyMeasurable
    filter_upwards [] with z
    change |z| ≤ 1 + z ^ 2
    nlinarith only [sq_nonneg (|z| - 1), sq_abs z]
  let G : Fin n → Shao.Path n → ℝ := fun i a =>
    if k ≤ i.val then (if i.val < T a then F a * a (Fin.rev i) else 0) else 0
  have hpart (i : Fin n) : Integrable (G i) P ∧ (∫ a : Shao.Path n, G i a ∂P) = 0 := by
    by_cases hik : k ≤ i.val
    · let V : Shao.Path n → ℝ := fun a => if i.val < T a then F a else 0
      have hset : MeasurableSet {a : Shao.Path n | i.val < T a} :=
        measurableSet_lt measurable_const hTm
      have hVm : Measurable V := Measurable.ite hset hFm measurable_const
      have hVi : Integrable V P := by
        apply (hFi.indicator hset).congr
        filter_upwards [] with a
        by_cases ha : i.val < T a <;> simp [V, Set.indicator, ha]
      have hVdep (a b : Shao.Path n)
          (hab : ∀ j : Fin n, j.val < i.val → a (Fin.rev j) = b (Fin.rev j)) : V a = V b := by
        have htail := hdep i a b hab
        have hF := hFdep a b (fun j hj => hab j (hj.trans_le hik))
        by_cases ha : i.val < T a
        · have hb := htail.mp ha
          simpa only [V, ha, hb, ite_true] using hF
        · have hb : ¬i.val < T b := fun hb => ha (htail.mpr hb)
          simp only [V, ha, hb, ite_false]
      have hh := bse_reverse_factor_of_dep nu n i V hVm hVi hVdep
        (fun z : ℝ => z) measurable_id h1
      have hpoint (a : Shao.Path n) : V a * a (Fin.rev i) = G i a := by
        by_cases ha : i.val < T a <;> simp only [V, G, hik, ha, ite_true, ite_false, zero_mul]
      refine ⟨hh.2.1.congr (ae_of_all P hpoint), ?_⟩
      simpa only [hpoint, hmean, mul_zero] using hh.2.2
    · have hzero : G i = fun _ : Shao.Path n => (0 : ℝ) := by
        funext a
        simp only [G, hik, ite_false]
      rw [hzero]
      exact ⟨integrable_const 0, by simp⟩
  have hpoint (a : Shao.Path n) : F a * (B a (T a) - B a (min k (T a))) = ∑ i : Fin n, G i a := by
    simp only [B, Shao.prefixSum, Finset.sum_filter]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hit : i.val < T a
    · by_cases hik : i.val < k
      · have hki : ¬ k ≤ i.val := Nat.not_le.mpr hik
        simp [G, hit, hik, hki, lt_min_iff]
      · have hki : k ≤ i.val := Nat.le_of_not_gt hik
        simp [G, hit, hik, hki, lt_min_iff]
    · simp [G, hit, lt_min_iff]
  have hi := integrable_finsetSum Finset.univ (fun i _ => (hpart i).1)
  refine ⟨hi.congr (ae_of_all P (fun a => (hpoint a).symm)), ?_⟩
  simp_rw [hpoint]
  rw [integral_finsetSum Finset.univ (fun i _ => (hpart i).1)]
  simp only [fun i => (hpart i).2, Finset.sum_const_zero]

private theorem bse_stopped_l2_maximal
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (T : Shao.Path n → ℕ) (hTm : Measurable T)
    (hTn : ∀ a : Shao.Path n, T a ≤ n)
    (hdep : ∀ (i : Fin n) (a b : Shao.Path n),
      (∀ j : Fin n, j.val < i.val → a (Fin.rev j) = b (Fin.rev j)) →
        (i.val < T a ↔ i.val < T b)) :
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let B : Shao.Path n → ℕ → ℝ := fun a k =>
      Shao.prefixSum (fun i : Fin n => a (Fin.rev i)) k
    let K : Shao.Path n → ℝ := fun a =>
      (Finset.Icc 0 (T a)).sup' (by exact ⟨0, by simp⟩) (fun k => |B a k|)
    (∫ a : Shao.Path n, K a ^ 2 ∂P) ≤
      4 * (∫ a : Shao.Path n, B a (T a) ^ 2 ∂P) := by
  classical
  intro P B K
  obtain ⟨hBTm, hKm, hJm, hBTi, hKi, hJi, hgeom⟩ :=
    bse_stopped_max_data nu n h2 T hTm hTn
  change Measurable (fun a : Shao.Path n => B a (T a)) at hBTm
  change Measurable K at hKm
  change Integrable (fun a : Shao.Path n => B a (T a) ^ 2) P at hBTi
  change Integrable (fun a : Shao.Path n => K a ^ 2) P at hKi
  change ∀ a : Shao.Path n, 0 ≤ K a ∧ _ at hgeom
  let M : Shao.Path n → ℕ → ℝ := fun a k => B a (min k (T a))
  let A : Shao.Path n → ℕ → ℝ := fun a k => Nat.rec (motive := fun _ => ℝ) 0
    (fun j v => max v |M a (j + 1)|) k
  let W : ℕ → Shao.Path n → ℝ := fun k a =>
    (if 0 ≤ M a (k + 1) then 1 else -1) * (A a (k + 1) - A a k)
  let V : Shao.Path n → ℝ := fun a => ∑ k ∈ Finset.range n, W k a
  have hM0 (a : Shao.Path n) : M a 0 = 0 := by simp [M, B, Shao.prefixSum_zero]
  have hdata (a : Shao.Path n) :
      (∀ k : ℕ, 0 ≤ A a k ∧ A a k =
        (Finset.Icc 0 k).sup' (by exact ⟨0, by simp⟩) (fun j => |M a j|)) ∧
      (∀ k : ℕ, 0 ≤ A a (k + 1) - A a k) ∧
      (∀ k : ℕ, |W k a| = A a (k + 1) - A a k) ∧
      A a n ^ 2 ≤ 2 * (∑ k ∈ Finset.range n, M a (k + 1) * W k a) ∧
      |∑ k ∈ Finset.range n, W k a| ≤ A a n ∧
      (∀ k : ℕ, k < n → |W k a| ≤ A a n) :=
    bse_maximal_weights (M a) (hM0 a) n
  have hAbound (a : Shao.Path n) (k : ℕ) : A a k ≤ K a := by
    rw [((hdata a).1 k).2]
    apply Finset.sup'_le
    intro j _
    exact Finset.le_sup' (fun l => |B a l|) (by simp [Nat.min_le_right])
  have hAn (a : Shao.Path n) : A a n = K a := by
    apply le_antisymm (hAbound a n)
    apply Finset.sup'_le
    intro j hj
    have hjT : j ≤ T a := (Finset.mem_Icc.mp hj).2
    have hjn : j ≤ n := hjT.trans (hTn a)
    have hh := Finset.le_sup' (fun l => |M a l|)
      (show j ∈ Finset.Icc 0 n by simp [hjn])
    rw [← ((hdata a).1 n).2] at hh
    simpa only [M, Nat.min_eq_left hjT] using hh
  have hMbound (a : Shao.Path n) (k : ℕ) : |M a k| ≤ K a :=
    Finset.le_sup' (fun l => |B a l|) (by simp [Nat.min_le_right])
  have hWbound (k : ℕ) (hk : k < n) (a : Shao.Path n) : |W k a| ≤ K a := by
    have hh := (hdata a).2.2.2.2.2 k hk
    rwa [hAn a] at hh
  have hVbound (a : Shao.Path n) : |V a| ≤ K a := by
    have hh := (hdata a).2.2.2.2.1
    change |V a| ≤ A a n at hh
    rwa [hAn a] at hh
  have hpath (a : Shao.Path n) : K a ^ 2 ≤
      2 * ∑ k ∈ Finset.range n, M a (k + 1) * W k a := by
    have hh := (hdata a).2.2.2.1
    rwa [hAn a] at hh
  have hrev : Measurable (fun a : Shao.Path n => fun i : Fin n => a (Fin.rev i)) :=
    Measurable.of_eval (fun i => measurable_pi_apply (Fin.rev i))
  have hBm (k : ℕ) : Measurable (fun a : Shao.Path n => B a k) :=
    (Shao.measurable_prefixSum k).comp hrev
  have hBjoint : Measurable (fun p : Shao.Path n × ℕ => B p.1 p.2) :=
    measurable_from_prod_countable_left hBm
  have hMm (k : ℕ) : Measurable (fun a : Shao.Path n => M a k) :=
    hBjoint.comp (measurable_id.prodMk (measurable_const.min hTm))
  have hAm (k : ℕ) : Measurable (fun a : Shao.Path n => A a k) := by
    induction k with
    | zero => exact measurable_const
    | succ k ih =>
      have hmabs : Measurable (fun a : Shao.Path n => |M a (k + 1)|) := by
        simpa only [Real.norm_eq_abs] using (hMm (k + 1)).norm
      exact ih.max hmabs
  have hWm (k : ℕ) : Measurable (W k) :=
    (Measurable.ite (measurableSet_le measurable_const (hMm (k + 1)))
      measurable_const measurable_const).mul ((hAm (k + 1)).sub (hAm k))
  have hK1 : Integrable K P := by
    apply ((integrable_const (1 : ℝ)).add hKi).mono' hKm.aestronglyMeasurable
    filter_upwards [] with a
    change |K a| ≤ 1 + K a ^ 2
    rw [abs_of_nonneg (hgeom a).1]
    nlinarith only [sq_nonneg (K a - 1)]
  have hWi (k : ℕ) (hk : k < n) : Integrable (W k) P := by
    apply hK1.mono' (hWm k).aestronglyMeasurable
    exact ae_of_all P (fun a => hWbound k hk a)
  have hMdep (k : ℕ) (a b : Shao.Path n)
      (hab : ∀ j : Fin n, j.val < k → a (Fin.rev j) = b (Fin.rev j)) : M a k = M b k :=
    bse_stopped_prefix_dep T hdep k a b hab
  have hAdep (k : ℕ) (a b : Shao.Path n)
      (hab : ∀ j : Fin n, j.val < k → a (Fin.rev j) = b (Fin.rev j)) : A a k = A b k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      change max (A a k) |M a (k + 1)| = max (A b k) |M b (k + 1)|
      rw [ih (fun j hj => hab j (by omega)), hMdep (k + 1) a b hab]
  have hWdep (k : ℕ) (a b : Shao.Path n)
      (hab : ∀ j : Fin n, j.val < k + 1 → a (Fin.rev j) = b (Fin.rev j)) : W k a = W k b := by
    dsimp only [W]
    rw [hMdep (k + 1) a b hab, hAdep (k + 1) a b hab,
      hAdep k a b (fun j hj => hab j (by omega))]
  have hMWi (k : ℕ) (hk : k < n) (l : ℕ) :
      Integrable (fun a : Shao.Path n => M a l * W k a) P := by
    apply hKi.mono' ((hMm l).mul (hWm k)).aestronglyMeasurable
    filter_upwards [] with a
    change |M a l * W k a| ≤ K a ^ 2
    rw [abs_mul]
    simpa only [pow_two] using
      mul_le_mul (hMbound a l) (hWbound k hk a) (abs_nonneg _) (hgeom a).1
  have hMn (a : Shao.Path n) : M a n = B a (T a) := by
    simp only [M, Nat.min_eq_right (hTn a)]
  have hBTWi (k : ℕ) (hk : k < n) :
      Integrable (fun a : Shao.Path n => B a (T a) * W k a) P := by
    simpa only [hMn] using hMWi k hk n
  have hcross (k : ℕ) (hk : k < n) :
      (∫ a : Shao.Path n, M a (k + 1) * W k a ∂P) =
        ∫ a : Shao.Path n, B a (T a) * W k a ∂P := by
    have ht := (bse_stopped_tail_test nu n h2 hmean T hTm hTn hdep
      (k + 1) (W k) (hWm k) (hWi k hk) (hWdep k)).2
    have hz : (∫ a : Shao.Path n,
        B a (T a) * W k a - M a (k + 1) * W k a ∂P) = 0 := by
      convert ht using 1
      congr 1
      funext a
      dsimp only [M]
      ring
    rw [integral_sub (hBTWi k hk) (hMWi k hk (k + 1))] at hz
    linarith
  have hSi : Integrable (fun a : Shao.Path n =>
      ∑ k ∈ Finset.range n, M a (k + 1) * W k a) P :=
    integrable_finsetSum (Finset.range n) (fun k hk => hMWi k (Finset.mem_range.mp hk) (k + 1))
  have hBVi : Integrable (fun a : Shao.Path n => B a (T a) * V a) P := by
    simpa only [V, Finset.mul_sum] using
      integrable_finsetSum (Finset.range n) (fun k hk => hBTWi k (Finset.mem_range.mp hk))
  have hsumEq : (∫ a : Shao.Path n,
      ∑ k ∈ Finset.range n, M a (k + 1) * W k a ∂P) =
        ∫ a : Shao.Path n, B a (T a) * V a ∂P := by
    simp only [V, Finset.mul_sum]
    rw [integral_finsetSum (Finset.range n)
      (fun k hk => hMWi k (Finset.mem_range.mp hk) (k + 1)),
      integral_finsetSum (Finset.range n) (fun k hk => hBTWi k (Finset.mem_range.mp hk))]
    exact Finset.sum_congr rfl (fun k hk => hcross k (Finset.mem_range.mp hk))
  have hlow := integral_mono hKi (hSi.const_mul 2) hpath
  change (∫ a : Shao.Path n, K a ^ 2 ∂P) ≤
    ∫ a : Shao.Path n, 2 * (∑ k ∈ Finset.range n, M a (k + 1) * W k a) ∂P at hlow
  rw [integral_const_mul, hsumEq] at hlow
  have hpoint (a : Shao.Path n) : 2 * (B a (T a) * V a) ≤
      2 * B a (T a) ^ 2 + K a ^ 2 / 2 := by
    have hv2 : V a ^ 2 ≤ K a ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (V a)) (hVbound a) 2
    nlinarith only [sq_nonneg (2 * B a (T a) - V a), hv2]
  have hupp := integral_mono (hBVi.const_mul 2)
    ((hBTi.const_mul 2).add (hKi.div_const 2)) hpoint
  change (∫ a : Shao.Path n, 2 * (B a (T a) * V a) ∂P) ≤
    ∫ a : Shao.Path n, 2 * B a (T a) ^ 2 + K a ^ 2 / 2 ∂P at hupp
  rw [integral_const_mul, integral_add (hBTi.const_mul 2) (hKi.div_const 2),
    integral_const_mul, integral_div] at hupp
  linarith

theorem sourceBackward_stopped_second_and_maximal
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 4 ≤ n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (H : ℝ) (hR : Shao.truncationBudget nu n 0 ≤ 1 / 2)
    (hH : 4 * Shao.truncationBudget nu n 0 ^ 2 ≤ H) :
    let R : ℝ := Shao.truncationBudget nu n 0
    let L : ℕ := n / 2
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let rev : Shao.Path n → Shao.Path n := fun a i => a (Fin.rev i)
    let Qrev : Shao.Path n → ℕ → ℝ := fun a k => Shao.prefixSquares (rev a) k
    let NH : Shao.Path n → ℕ := fun a =>
      @dite ℕ (∃ k : ℕ, k ≤ L ∧ H ≤ Qrev a k)
        (Classical.propDecidable _)
        (fun h => @Nat.find (fun k : ℕ => k ≤ L ∧ H ≤ Qrev a k)
          (fun k => Classical.propDecidable _) h)
        (fun _ => L)
    ∀ m : ℕ, m ≤ L → (m : ℝ) ≤ 3 * (n : ℝ) * H →
      let N : Shao.Path n → ℕ := fun a => max m (NH a)
      let B : Shao.Path n → ℕ → ℝ := fun a k => Shao.prefixSum (rev a) k
      let backwardMax : Shao.Path n → ℝ := fun a =>
        (Finset.Icc 0 (N a)).sup' (by exact ⟨0, by simp⟩) (fun k => |B a k|)
      let J : Shao.Path n → ℝ := fun a =>
        (Finset.Icc 0 (N a)).sup' (by exact ⟨0, by simp⟩)
          (fun l => |Shao.prefixSum a (n - N a + l) - Shao.prefixSum a (n - N a)|)
      Measurable (fun a : Shao.Path n => B a (N a)) ∧
        Measurable backwardMax ∧ Measurable J ∧
        Integrable (fun a : Shao.Path n => (B a (N a)) ^ 2) P ∧
        Integrable (fun a : Shao.Path n => backwardMax a ^ 2) P ∧
        Integrable (fun a : Shao.Path n => J a ^ 2) P ∧
        (∀ a : Shao.Path n, J a ≤ 2 * backwardMax a) ∧
        (∫ a : Shao.Path n, (B a (N a)) ^ 2 ∂P) =
          (1 / (n : ℝ)) * (∫ a : Shao.Path n, (N a : ℝ) ∂P) ∧
        (∫ a : Shao.Path n, backwardMax a ^ 2 ∂P) ≤
          4 * (1 / (n : ℝ)) * (∫ a : Shao.Path n, (N a : ℝ) ∂P) ∧
        (∫ a : Shao.Path n, J a ^ 2 ∂P) ≤
          16 * (1 / (n : ℝ)) * (∫ a : Shao.Path n, (N a : ℝ) ∂P) := by
  classical
  intro R L P rev Qrev NH m hmL hmH N B backwardMax J
  have hn0 : 0 < n := by omega
  have hLn : L ≤ n := Nat.div_le_self n 2
  have hLpos : 0 < L := by dsimp [L]; omega
  obtain ⟨hRp, hHp, hclip, hclipMean⟩ :=
    sourceBackward_clipped_square_mean nu n h2 hnorm H hR hH
  have hrev : Measurable rev := Measurable.of_eval (fun i => measurable_pi_apply (Fin.rev i))
  have hQm (k : ℕ) : Measurable (fun a : Shao.Path n => Qrev a k) :=
    (Shao.measurable_prefixSquares k).comp hrev
  have hfind := bse_capped_find_measurable L hLpos H hHp Qrev hQm
    (fun a => Shao.prefixSquares_zero (rev a)) (fun a => bse_prefixSquares_mono (rev a))
  change Measurable NH ∧ ∀ a : Shao.Path n, 1 ≤ NH a ∧ NH a ≤ L ∧
    ∀ k : ℕ, (k < NH a ↔ k < L ∧ Qrev a k < H) at hfind
  have hNm : Measurable N := measurable_const.max hfind.1
  have hNn (a : Shao.Path n) : N a ≤ n :=
    (max_le hmL (hfind.2 a).2.1).trans hLn
  have hdep (i : Fin n) (a b : Shao.Path n)
      (hab : ∀ j : Fin n, j.val < i.val → a (Fin.rev j) = b (Fin.rev j)) :
      i.val < N a ↔ i.val < N b := by
    have hQab : Qrev a i.val = Qrev b i.val := by
      dsimp only [Qrev, Shao.prefixSquares, rev]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hab j (Finset.mem_filter.mp hj).2]
    change i.val < max m (NH a) ↔ i.val < max m (NH b)
    rw [lt_max_iff, lt_max_iff, (hfind.2 a).2.2 i.val,
      (hfind.2 b).2.2 i.val, hQab]
  obtain ⟨hBTm, hKm, hJm, hBTi, hKi, hJi, hgeom⟩ :=
    bse_stopped_max_data nu n h2 N hNm hNn
  have hsecond := (bse_stopped_second nu n h2 hmean N hNm hNn hdep).2
  have hnne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn0)
  have hv : (∫ z : ℝ, z ^ 2 ∂nu) = 1 / (n : ℝ) := by
    apply (eq_div_iff hnne).mpr
    nlinarith only [hnorm]
  rw [hv] at hsecond
  have hmax := bse_stopped_l2_maximal nu n h2 hmean N hNm hNn hdep
  change (∫ a : Shao.Path n, backwardMax a ^ 2 ∂P) ≤
    4 * (∫ a : Shao.Path n, B a (N a) ^ 2 ∂P) at hmax
  change (∫ a : Shao.Path n, B a (N a) ^ 2 ∂P) =
    (1 / (n : ℝ)) * (∫ a : Shao.Path n, (N a : ℝ) ∂P) at hsecond
  rw [hsecond] at hmax
  have hmax' : (∫ a : Shao.Path n, backwardMax a ^ 2 ∂P) ≤
      4 * (1 / (n : ℝ)) * (∫ a : Shao.Path n, (N a : ℝ) ∂P) := by
    simpa only [mul_assoc] using hmax
  have hJsquare (a : Shao.Path n) : J a ^ 2 ≤ 4 * backwardMax a ^ 2 := by
    have hh := pow_le_pow_left₀ (hgeom a).2.1 (hgeom a).2.2 2
    nlinarith only [hh]
  have hJbound := integral_mono hJi (hKi.const_mul 4) hJsquare
  rw [integral_const_mul] at hJbound
  refine ⟨hBTm, hKm, hJm, hBTi, hKi, hJi, fun a => (hgeom a).2.2,
    hsecond, hmax', ?_⟩
  calc
    (∫ a : Shao.Path n, J a ^ 2 ∂P) ≤
        4 * (∫ a : Shao.Path n, backwardMax a ^ 2 ∂P) := hJbound
    _ ≤ 4 * (4 * (1 / (n : ℝ)) * (∫ a : Shao.Path n, (N a : ℝ) ∂P)) :=
      mul_le_mul_of_nonneg_left hmax' (by norm_num)
    _ = 16 * (1 / (n : ℝ)) * (∫ a : Shao.Path n, (N a : ℝ) ∂P) := by ring

end Shao.Probability
