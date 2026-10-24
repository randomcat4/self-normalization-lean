/- Mathematical candidate only: no production proof or Lean/AX invocation.
   This pays the actual centered bounded-law nonresidual double-crossing
   probability, not the Brownian double-hit error or the original C1/C2 roots. -/
import Shao.Probability.QuadraticEnergyLowerTail
import Shao.Probability.GaussianTail
import Shao.Probability.MeasurablePath
import Shao.C2.TwoSided
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace Shao.Probability.SourceOriginalLargeThreshold
open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem olt_deterministic_double_crossing
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (n : ℕ) (hn : 0 < n) (b a lam : ℝ)
    (hb : 0 ≤ b) (ha : 0 < a) (hlam : 0 ≤ lam)
    (hsupport : ∀ᵐ z : ℝ ∂nu, |z| ≤ b)
    (hlamb : lam * b ≤ 1)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1) :
    let beta : ℝ := (n : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂nu)
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    Integrable (fun z : ℝ => z ^ 2) nu ∧
      Integrable (fun z : ℝ => |z| ^ 3) nu ∧
      P.real {w : Shao.Path n |
        a ≤ Shao.upperMax w hn ∧ a ≤ Shao.lowerMax w hn} ≤
        2 * Real.exp (-3 * lam * a + lam ^ 2 / 2 + lam ^ 3 * beta) := by
  classical
  intro beta P
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  let clip : ℕ → Shao.Path n → Shao.Path n :=
    fun k w j => if j.val < k then w j else 0
  have h2 : Integrable (fun z : ℝ => z ^ 2) nu := by
    apply (integrable_const (b ^ 2)).mono' (by fun_prop)
    filter_upwards [hsupport] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z), ← sq_abs z]
    exact pow_le_pow_left₀ (abs_nonneg z) hz 2
  have h3 : Integrable (fun z : ℝ => |z| ^ 3) nu := by
    apply (integrable_const (b ^ 3)).mono' (by fun_prop)
    filter_upwards [hsupport] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg z) 3)]
    exact pow_le_pow_left₀ (abs_nonneg z) hz 3
  refine ⟨h2, h3, ?_⟩
  have h1 : Integrable (fun z : ℝ => z) nu := by
    apply (integrable_const b).mono' (by fun_prop)
    simpa only [Real.norm_eq_abs] using hsupport
  let q : ℝ := lam ^ 2 / 2 * (∫ z : ℝ, z ^ 2 ∂nu) +
    lam ^ 3 * (∫ z : ℝ, |z| ^ 3 ∂nu)
  have hq : 0 ≤ q := by
    dsimp [q]
    exact add_nonneg (mul_nonneg (by positivity) (integral_nonneg fun z => sq_nonneg z))
      (mul_nonneg (pow_nonneg hlam 3)
        (integral_nonneg fun z => pow_nonneg (abs_nonneg z) 3))
  have hnq : (n : ℝ) * q = lam ^ 2 / 2 + lam ^ 3 * beta := by
    calc
      _ = lam ^ 2 / 2 * ((n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu)) +
          lam ^ 3 * ((n : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂nu)) := by dsimp [q]; ring
      _ = _ := by rw [hnorm]; simp only [mul_one]; rfl
  have hTaylor (v : ℝ) (hv : |v| ≤ 1) :
      Real.exp v ≤ 1 + v + v ^ 2 / 2 + |v| ^ 3 := by
    have hr := Real.exp_bound (x := v) (n := 3) hv (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at hr
    have hh := (abs_le.mp hr).2
    nlinarith [pow_nonneg (abs_nonneg v) 3]
  have hMG (s : ℝ) (hs : s = 1 ∨ s = -1) :
      Integrable (fun z : ℝ => Real.exp (lam * s * z)) nu ∧
        (∫ z : ℝ, Real.exp (lam * s * z) ∂nu) ≤ Real.exp q := by
    have hsabs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
    have hssq : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
    have harg : ∀ᵐ z : ℝ ∂nu, |lam * s * z| ≤ 1 := by
      filter_upwards [hsupport] with z hz
      rw [abs_mul, abs_mul, abs_of_nonneg hlam, hsabs, mul_one]
      exact (mul_le_mul_of_nonneg_left hz hlam).trans hlamb
    have hi : Integrable (fun z : ℝ => Real.exp (lam * s * z)) nu := by
      apply (integrable_const (Real.exp 1)).mono' (by fun_prop)
      filter_upwards [harg] with z hz
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans hz)
    refine ⟨hi, ?_⟩
    have hp : ∀ᵐ z : ℝ ∂nu, Real.exp (lam * s * z) ≤
        1 + (lam * s) * z + (lam ^ 2 / 2) * z ^ 2 + lam ^ 3 * |z| ^ 3 := by
      filter_upwards [harg] with z hz
      have hh := hTaylor (lam * s * z) hz
      simp only [abs_mul, abs_of_nonneg hlam, hsabs, mul_one, mul_pow, hssq] at hh
      convert hh using 1 <;> ring
    have hpoly : Integrable (fun z : ℝ =>
        1 + (lam * s) * z + (lam ^ 2 / 2) * z ^ 2 + lam ^ 3 * |z| ^ 3) nu :=
      (((integrable_const (1 : ℝ)).add (h1.const_mul _)).add (h2.const_mul _)).add
        (h3.const_mul _)
    have hMeanTerm : (∫ z : ℝ, (lam * s) * z ∂nu) = 0 := by
      rw [integral_const_mul (lam * s) (fun z : ℝ => z), hmean, mul_zero]
    calc
      _ ≤ ∫ z : ℝ, 1 + (lam * s) * z + (lam ^ 2 / 2) * z ^ 2 +
          lam ^ 3 * |z| ^ 3 ∂nu := integral_mono_ae hi hpoly hp
      _ = 1 + q := by
        rw [integral_add
          (f := fun z : ℝ => 1 + (lam * s) * z + (lam ^ 2 / 2) * z ^ 2)
          (g := fun z : ℝ => lam ^ 3 * |z| ^ 3)
          (((integrable_const (1 : ℝ)).add (h1.const_mul (lam * s))).add
            (h2.const_mul (lam ^ 2 / 2))) (h3.const_mul (lam ^ 3)),
          integral_add (f := fun z : ℝ => 1 + (lam * s) * z)
            (g := fun z : ℝ => (lam ^ 2 / 2) * z ^ 2)
            ((integrable_const (1 : ℝ)).add (h1.const_mul (lam * s))) (h2.const_mul (lam ^ 2 / 2)),
          integral_add (f := fun _ : ℝ => (1 : ℝ)) (g := fun z : ℝ => (lam * s) * z)
            (integrable_const (1 : ℝ)) (h1.const_mul (lam * s))]
        rw [hMeanTerm]
        simp only [integral_const_mul, integral_const, probReal_univ,
          one_smul, hmean, mul_zero, add_zero, q]
        ring
      _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp q
  have hSuppP : ∀ᵐ w : Shao.Path n ∂P, ∀ i : Fin n, |w i| ≤ b := by
    apply ae_all_iff.mpr
    intro i
    have hmap := (measurePreserving_eval (fun _ : Fin n => nu) i).map_eq
    apply (ae_map_iff (measurable_pi_apply i).aemeasurable
      (measurableSet_le continuous_abs.measurable measurable_const)).mp
    rw [hmap]
    exact hsupport
  have hFactor (i : Fin n) (F : Shao.Path n → ℝ) (hFm : Measurable F)
      (hFi : Integrable F P) (hdep : ∀ w, F (clip i.val w) = F w)
      (g : ℝ → ℝ) (hgm : Measurable g) (hgi : Integrable g nu) :
      Integrable (fun w : Shao.Path n => F w * g (w i)) P ∧
        (∫ w : Shao.Path n, F w * g (w i) ∂P) =
          (∫ w : Shao.Path n, F w ∂P) * (∫ z : ℝ, g z ∂nu) := by
    let past : Finset (Fin n) := Finset.univ.filter (fun j => j.val < i.val)
    let f : (past → ℝ) → ℝ := fun v =>
      F (fun j => if hj : j ∈ past then v ⟨j, hj⟩ else 0)
    have hfm : Measurable f := by
      apply hFm.comp
      apply Measurable.of_eval
      intro j
      by_cases hj : j ∈ past
      · simpa only [hj, dite_true] using
          (measurable_pi_apply (X := fun _ : past => ℝ) ⟨j, hj⟩)
      · simp only [hj, dite_false]
        exact measurable_const
    have hfeq (w : Shao.Path n) : f (fun j : past => w j) = F w := by
      simpa [f, past, clip] using hdep w
    have hXi : iIndepFun (fun j : Fin n => fun w : Shao.Path n => w j) P :=
      iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)
    have hdisj : Disjoint past ({i} : Finset (Fin n)) := by
      simp [past, Finset.disjoint_singleton_right]
    have ht := hXi.indepFun_finset past {i} hdisj (fun j => measurable_pi_apply j)
    have hright : Measurable (fun v : ({i} : Finset (Fin n)) → ℝ => g (v ⟨i, by simp⟩)) :=
      hgm.comp (measurable_pi_apply (X := fun _ : ({i} : Finset (Fin n)) => ℝ) ⟨i, by simp⟩)
    have hind : IndepFun F (fun w : Shao.Path n => g (w i)) P := by
      simpa only [Function.comp_def, hfeq] using ht.comp hfm hright
    have hcur : Integrable (fun w : Shao.Path n => g (w i)) P :=
      (measurePreserving_eval (fun _ : Fin n => nu) i).integrable_comp_of_integrable hgi
    refine ⟨hind.integrable_mul hFi hcur, ?_⟩
    rw [hind.integral_fun_mul_eq_mul_integral hFi.aestronglyMeasurable hcur.aestronglyMeasurable]
    congr 1
    exact integral_comp_eval hgi.aestronglyMeasurable
  have hPrefixClip (w : Shao.Path n) (k j : ℕ) (hj : j ≤ k) :
      Shao.prefixSum (clip k w) j = Shao.prefixSum w j := by
    unfold Shao.prefixSum
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i.val < j := (Finset.mem_filter.mp hi).2
    simp only [clip, if_pos (lt_of_lt_of_le hi' hj)]
  have hOrder (eta : ℝ) (heta : eta = 1 ∨ eta = -1) :
      P.real {w : Shao.Path n | ∃ j k : Fin (n + 1), j.val ≤ k.val ∧
        a ≤ eta * Shao.prefixSum w j.val ∧ eta * Shao.prefixSum w k.val ≤ -a} ≤
        Real.exp (-3 * lam * a + (n : ℝ) * q) := by
    let eps : Fin n → Shao.Path n → ℝ := fun i w =>
      if ∃ j : Fin (i.val + 1), a ≤ eta * Shao.prefixSum w j.val then -eta else eta
    let Y : ℕ → Shao.Path n → ℝ := fun k w =>
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), eps i w * w i
    let Z : ℕ → Shao.Path n → ℝ := fun k w => Real.exp (lam * Y k w - (k : ℝ) * q)
    let live : ℕ → Shao.Path n → Prop := fun k w =>
      ∀ j : Fin (k + 1), Y j.val w < 3 * a
    let delta : ℕ → Shao.Path n → ℝ := fun k w =>
      if live k w then Z (k + 1) w - Z k w else 0
    let W : Shao.Path n → ℝ := fun w => 1 + ∑ k ∈ Finset.range n, delta k w
    let E : Set (Shao.Path n) := {w | ∃ j k : Fin (n + 1), j.val ≤ k.val ∧
      a ≤ eta * Shao.prefixSum w j.val ∧ eta * Shao.prefixSum w k.val ≤ -a}
    have hEtaAbs : |eta| = 1 := by rcases heta with rfl | rfl <;> norm_num
    have hEpsSign (i : Fin n) (w : Shao.Path n) : eps i w = 1 ∨ eps i w = -1 := by
      dsimp [eps]
      split_ifs <;> rcases heta with rfl | rfl <;> norm_num
    have hEpsAbs (i : Fin n) (w : Shao.Path n) : |eps i w| = 1 := by
      rcases hEpsSign i w with h | h <;> rw [h] <;> norm_num
    have hEpsM (i : Fin n) : Measurable (eps i) := by
      apply Measurable.ite _ measurable_const measurable_const
      simpa only [Set.setOf_exists, Pi.mul_apply] using MeasurableSet.iUnion
        (fun j : Fin (i.val + 1) => measurableSet_le measurable_const
          (measurable_const.mul (Shao.measurable_prefixSum j.val)))
    have hYM (k : ℕ) : Measurable (Y k) :=
      Finset.measurable_sum _ (fun i _ => (hEpsM i).mul (measurable_pi_apply i))
    have hZM (k : ℕ) : Measurable (Z k) := by dsimp [Z]; fun_prop
    have hLiveM (k : ℕ) : MeasurableSet {w | live k w} := by
      simpa only [live, Set.setOf_forall] using MeasurableSet.iInter
        (fun j : Fin (k + 1) => measurableSet_lt (hYM j.val) measurable_const)
    have hY0 (w : Shao.Path n) : Y 0 w = 0 := by simp [Y]
    have hZ0 (w : Shao.Path n) : Z 0 w = 1 := by simp [Z, hY0]
    have hYStep (i : Fin n) (w : Shao.Path n) :
        Y (i.val + 1) w = Y i.val w + eps i w * w i := by
      have hsets : Finset.univ.filter (fun j : Fin n => j.val < i.val + 1) =
          insert i (Finset.univ.filter (fun j : Fin n => j.val < i.val)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hj
          by_cases he : j = i
          · exact Or.inl he
          · exact Or.inr (by have : j.val ≠ i.val := fun h => he (Fin.ext h); omega)
        · rintro (rfl | hj) <;> omega
      dsimp [Y]
      rw [hsets, Finset.sum_insert (by simp)]
      ring
    have hYBound (k : ℕ) : ∀ᵐ w : Shao.Path n ∂P, |Y k w| ≤ (n : ℝ) * b := by
      filter_upwards [hSuppP] with w hw
      calc
        _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), |eps i w * w i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), b := by
          apply Finset.sum_le_sum
          intro i _
          simpa only [abs_mul, hEpsAbs, one_mul] using hw i
        _ ≤ ∑ _i : Fin n, b :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => hb)
        _ = _ := by simp
    have hZI (k : ℕ) : Integrable (Z k) P := by
      apply (integrable_const (Real.exp (lam * (n : ℝ) * b))).mono' (hZM k).aestronglyMeasurable
      filter_upwards [hYBound k] with w hw
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have hy := (le_abs_self (Y k w)).trans hw
      have hkq : 0 ≤ (k : ℝ) * q := mul_nonneg (Nat.cast_nonneg _) hq
      nlinarith [mul_le_mul_of_nonneg_left hy hlam]
    have hEpsClip (k : ℕ) (i : Fin n) (hi : i.val ≤ k) (w : Shao.Path n) :
        eps i (clip k w) = eps i w := by
      have he : (∃ j : Fin (i.val + 1), a ≤ eta * Shao.prefixSum (clip k w) j.val) ↔
          ∃ j : Fin (i.val + 1), a ≤ eta * Shao.prefixSum w j.val := by
        constructor <;> rintro ⟨j, hj⟩ <;> refine ⟨j, ?_⟩
        · simpa only [hPrefixClip w k j.val (by omega)] using hj
        · simpa only [hPrefixClip w k j.val (by omega)] using hj
      simp only [eps, he]
    have hYClip (k j : ℕ) (hj : j ≤ k) (w : Shao.Path n) : Y j (clip k w) = Y j w := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i.val < j := (Finset.mem_filter.mp hi).2
      rw [hEpsClip k i (by omega) w]
      simp only [clip, if_pos (by omega : i.val < k)]
    have hZClip (k j : ℕ) (hj : j ≤ k) (w : Shao.Path n) : Z j (clip k w) = Z j w := by
      simp only [Z, hYClip k j hj w]
    have hLiveClip (k : ℕ) (w : Shao.Path n) : live k (clip k w) ↔ live k w := by
      dsimp [live]
      constructor <;> intro h j <;> simpa only [hYClip k j.val (by omega) w] using h j
    have hDelta (k : ℕ) (hk : k < n) : Integrable (delta k) P ∧ (∫ w, delta k w ∂P) ≤ 0 := by
      let i : Fin n := ⟨k, hk⟩
      let Hplus : Shao.Path n → ℝ := fun w => if live k w ∧ eps i w = 1 then Z k w else 0
      let Hminus : Shao.Path n → ℝ := fun w => if live k w ∧ eps i w = -1 then Z k w else 0
      have hHpM : Measurable Hplus := Measurable.ite
        ((hLiveM k).inter (measurableSet_eq_fun (hEpsM i) measurable_const)) (hZM k) measurable_const
      have hHmM : Measurable Hminus := Measurable.ite
        ((hLiveM k).inter (measurableSet_eq_fun (hEpsM i) measurable_const)) (hZM k) measurable_const
      have hHpI : Integrable Hplus P := by
        apply (hZI k).mono' hHpM.aestronglyMeasurable
        exact ae_of_all P fun w => by simp only [Hplus]; split_ifs <;> simp [Z, (Real.exp_pos _).le]
      have hHmI : Integrable Hminus P := by
        apply (hZI k).mono' hHmM.aestronglyMeasurable
        exact ae_of_all P fun w => by simp only [Hminus]; split_ifs <;> simp [Z, (Real.exp_pos _).le]
      have hHpDep (w : Shao.Path n) : Hplus (clip i.val w) = Hplus w := by
        simp only [Hplus, i, hLiveClip, hEpsClip k i le_rfl w, hZClip k k le_rfl w]
      have hHmDep (w : Shao.Path n) : Hminus (clip i.val w) = Hminus w := by
        simp only [Hminus, i, hLiveClip, hEpsClip k i le_rfl w, hZClip k k le_rfl w]
      have hp := hFactor i Hplus hHpM hHpI hHpDep (fun z => Real.exp (lam * z))
        (by fun_prop) (by simpa using (hMG 1 (Or.inl rfl)).1)
      have hm := hFactor i Hminus hHmM hHmI hHmDep (fun z => Real.exp (-lam * z))
        (by fun_prop) (by simpa using (hMG (-1) (Or.inr rfl)).1)
      have hpoint (w : Shao.Path n) : delta k w =
          Real.exp (-q) * (Hplus w * Real.exp (lam * w i) +
            Hminus w * Real.exp (-lam * w i)) - (Hplus w + Hminus w) := by
        have hz : Z (k + 1) w = Z k w * Real.exp (lam * eps i w * w i) * Real.exp (-q) := by
          dsimp [Z]
          rw [show k = i.val from rfl, hYStep i w, ← Real.exp_add, ← Real.exp_add]
          congr 1
          push_cast
          ring
        by_cases hl : live k w
        · rcases hEpsSign i w with he | he
          · have hne : (1 : ℝ) ≠ -1 := by norm_num
            simp [delta, Hplus, Hminus, hl, he, hne]
            rw [hz, he]
            ring
          · have hne : (-1 : ℝ) ≠ 1 := by norm_num
            simp [delta, Hplus, Hminus, hl, he, hne]
            rw [hz, he]
            ring
        · simp [delta, Hplus, Hminus, hl]
      have hi : Integrable (fun w => Real.exp (-q) *
          (Hplus w * Real.exp (lam * w i) + Hminus w * Real.exp (-lam * w i)) -
          (Hplus w + Hminus w)) P :=
        ((hp.1.add hm.1).const_mul _).sub (hHpI.add hHmI)
      have hdI : Integrable (delta k) P := hi.congr (ae_of_all P fun w => (hpoint w).symm)
      refine ⟨hdI, ?_⟩
      have hHp0 : 0 ≤ ∫ w, Hplus w ∂P := integral_nonneg fun w => by dsimp [Hplus]; split_ifs <;> positivity
      have hHm0 : 0 ≤ ∫ w, Hminus w ∂P := integral_nonneg fun w => by dsimp [Hminus]; split_ifs <;> positivity
      calc
        _ = Real.exp (-q) * ((∫ w, Hplus w ∂P) * (∫ z, Real.exp (lam * z) ∂nu) +
            (∫ w, Hminus w ∂P) * (∫ z, Real.exp (-lam * z) ∂nu)) -
            ((∫ w, Hplus w ∂P) + (∫ w, Hminus w ∂P)) := by
          rw [integral_congr_ae (ae_of_all P hpoint), integral_sub
            (f := fun w : Shao.Path n => Real.exp (-q) *
              (Hplus w * Real.exp (lam * w i) + Hminus w * Real.exp (-lam * w i)))
            (g := fun w : Shao.Path n => Hplus w + Hminus w)
            ((hp.1.add hm.1).const_mul (Real.exp (-q))) (hHpI.add hHmI), integral_const_mul,
            integral_add (f := fun w : Shao.Path n => Hplus w * Real.exp (lam * w i))
              (g := fun w : Shao.Path n => Hminus w * Real.exp (-lam * w i)) hp.1 hm.1,
            hp.2, hm.2, integral_add (f := Hplus) (g := Hminus) hHpI hHmI]
        _ ≤ Real.exp (-q) * ((∫ w, Hplus w ∂P) * Real.exp q +
            (∫ w, Hminus w ∂P) * Real.exp q) -
            ((∫ w, Hplus w ∂P) + (∫ w, Hminus w ∂P)) := by
          gcongr
          · simpa using (hMG 1 (Or.inl rfl)).2
          · simpa using (hMG (-1) (Or.inr rfl)).2
        _ = 0 := by
          have he : Real.exp (-q) * Real.exp q = 1 := by rw [← Real.exp_add]; simp
          calc
            _ = (Real.exp (-q) * Real.exp q - 1) *
                ((∫ w, Hplus w ∂P) + (∫ w, Hminus w ∂P)) := by ring
            _ = 0 := by rw [he]; ring
    have hTel (w : Shao.Path n) (m : ℕ) :
        (∑ k ∈ Finset.range m, (Z (k + 1) w - Z k w)) = Z m w - 1 := by
      induction m with
      | zero => simp [hZ0]
      | succ m ih => rw [Finset.sum_range_succ, ih]; ring
    have hStop (w : Shao.Path n) :
        0 ≤ W w ∧ ((∃ k : Fin (n + 1), 3 * a ≤ Y k.val w) →
          Real.exp (3 * lam * a - (n : ℝ) * q) ≤ W w) := by
      by_cases hh : ∃ k : ℕ, k ≤ n ∧ 3 * a ≤ Y k w
      · let j : ℕ := Nat.find hh
        have hjn : j ≤ n := (Nat.find_spec hh).1
        have hjhit : 3 * a ≤ Y j w := (Nat.find_spec hh).2
        have hLive (k : ℕ) (hkn : k < n) : live k w ↔ k < j := by
          constructor
          · intro hl
            by_contra hk
            have hjk : j ≤ k := Nat.le_of_not_gt hk
            have hj := hl ⟨j, by omega⟩
            linarith
          · intro hkj ell
            have hellj : ell.val < j := by omega
            have hnot := Nat.find_min hh hellj
            have helln : ell.val ≤ n := by omega
            exact lt_of_not_ge (fun h => hnot ⟨helln, h⟩)
        have hsum : (∑ k ∈ Finset.range n, delta k w) =
            ∑ k ∈ Finset.range j, (Z (k + 1) w - Z k w) := by
          calc
            _ = ∑ k ∈ Finset.range n, if k < j then Z (k + 1) w - Z k w else 0 := by
              apply Finset.sum_congr rfl
              intro k hk
              simp only [delta, hLive k (Finset.mem_range.mp hk)]
            _ = _ := by
              symm
              have he : (∑ k ∈ Finset.range j, (Z (k + 1) w - Z k w)) =
                  ∑ k ∈ Finset.range j, if k < j then Z (k + 1) w - Z k w else 0 := by
                apply Finset.sum_congr rfl
                intro k hk
                simp only [if_pos (Finset.mem_range.mp hk)]
              rw [he]
              apply Finset.sum_subset (Finset.range_mono hjn)
              intro k hkn hkj
              simp only [Finset.mem_range] at hkn hkj
              simp only [if_neg hkj]
        have hW : W w = Z j w := by dsimp [W]; rw [hsum, hTel]; ring
        refine ⟨by rw [hW]; exact (Real.exp_pos _).le, ?_⟩
        intro _
        rw [hW]
        apply Real.exp_le_exp.mpr
        have hmul := mul_le_mul_of_nonneg_left hjhit hlam
        have htime := mul_le_mul_of_nonneg_right (show (j : ℝ) ≤ (n : ℝ) by exact_mod_cast hjn) hq
        nlinarith
      · have hLive (k : ℕ) (hk : k < n) : live k w := by
          intro j
          apply lt_of_not_ge
          intro hj
          exact hh ⟨j.val, by omega, hj⟩
        have hW : W w = Z n w := by
          dsimp [W]
          have he : (∑ k ∈ Finset.range n, delta k w) =
              ∑ k ∈ Finset.range n, (Z (k + 1) w - Z k w) := by
            apply Finset.sum_congr rfl
            intro k hk
            simp only [delta, if_pos (hLive k (Finset.mem_range.mp hk))]
          rw [he, hTel]
          ring
        refine ⟨by rw [hW]; exact (Real.exp_pos _).le, ?_⟩
        rintro ⟨k, hk⟩
        exact False.elim (hh ⟨k.val, by omega, hk⟩)
    have hEhit (w : Shao.Path n) (hw : w ∈ E) : ∃ k : Fin (n + 1), 3 * a ≤ Y k.val w := by
      obtain ⟨j, k, hjk, hj, hk⟩ := hw
      have hex : ∃ ell : ℕ, a ≤ eta * Shao.prefixSum w ell := ⟨j.val, hj⟩
      let tau : ℕ := Nat.find hex
      have htau : a ≤ eta * Shao.prefixSum w tau := Nat.find_spec hex
      have htauj : tau ≤ j.val := Nat.find_min' hex hj
      have htauk : tau ≤ k.val := htauj.trans hjk
      have heps (i : Fin n) : eps i w = if i.val < tau then eta else -eta := by
        by_cases hi : i.val < tau
        · have hnot : ¬∃ ell : Fin (i.val + 1), a ≤ eta * Shao.prefixSum w ell.val := by
            rintro ⟨ell, hell⟩
            exact Nat.find_min hex (by omega : ell.val < tau) hell
          simp only [eps, if_neg hnot, if_pos hi]
        · have hyes : ∃ ell : Fin (i.val + 1), a ≤ eta * Shao.prefixSum w ell.val :=
            ⟨⟨tau, by omega⟩, htau⟩
          simp only [eps, if_pos hyes, if_neg hi]
      have hsets : (Finset.univ.filter (fun i : Fin n => i.val < k.val)).filter
          (fun i : Fin n => i.val < tau) = Finset.univ.filter (fun i : Fin n => i.val < tau) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      have hY : Y k.val w = 2 * eta * Shao.prefixSum w tau - eta * Shao.prefixSum w k.val := by
        calc
          _ = ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k.val),
              ((if i.val < tau then 2 * eta * w i else 0) - eta * w i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [heps]
            split_ifs <;> ring
          _ = _ := by
            rw [Finset.sum_sub_distrib, ← Finset.sum_filter, hsets]
            simp only [Shao.prefixSum, Finset.mul_sum]
      refine ⟨k, ?_⟩
      rw [hY]
      nlinarith
    have hEM : MeasurableSet E := by
      dsimp [E]
      simp only [Set.setOf_exists]
      apply MeasurableSet.iUnion
      intro j
      apply MeasurableSet.iUnion
      intro k
      by_cases hjk : j.val ≤ k.val
      · simp only [hjk, true_and]
        exact (measurableSet_le measurable_const (measurable_const.mul (Shao.measurable_prefixSum _))).inter
          (measurableSet_le (measurable_const.mul (Shao.measurable_prefixSum _)) measurable_const)
      · simp only [hjk, false_and, Set.setOf_false, MeasurableSet.empty]
    have hWI : Integrable W P := (integrable_const (1 : ℝ)).add
      (integrable_finsetSum _ fun k hk => (hDelta k (Finset.mem_range.mp hk)).1)
    have hWmean : (∫ w, W w ∂P) ≤ 1 := by
      rw [show W = fun w => 1 + ∑ k ∈ Finset.range n, delta k w from rfl,
        integral_add (integrable_const (1 : ℝ))
          (integrable_finsetSum _ fun k hk => (hDelta k (Finset.mem_range.mp hk)).1),
        integral_const, probReal_univ, one_smul,
        integral_finsetSum _ fun k hk => (hDelta k (Finset.mem_range.mp hk)).1]
      have hs : (∑ k ∈ Finset.range n, ∫ w, delta k w ∂P) ≤ 0 :=
        Finset.sum_nonpos fun k hk => (hDelta k (Finset.mem_range.mp hk)).2
      linarith
    have hInd : ∀ w : Shao.Path n, E.indicator
        (fun _ => Real.exp (3 * lam * a - (n : ℝ) * q)) w ≤ W w := by
      intro w
      by_cases hw : w ∈ E
      · rw [Set.indicator_of_mem hw]
        exact (hStop w).2 (hEhit w hw)
      · rw [Set.indicator_of_notMem hw]
        exact (hStop w).1
    have hprob : P.real E * Real.exp (3 * lam * a - (n : ℝ) * q) ≤ 1 := by
      calc
        _ = ∫ w, E.indicator (fun _ => Real.exp (3 * lam * a - (n : ℝ) * q)) w ∂P := by
          rw [integral_indicator_const _ hEM, smul_eq_mul]
        _ ≤ ∫ w, W w ∂P := integral_mono ((integrable_const _).indicator hEM) hWI hInd
        _ ≤ _ := hWmean
    have hh := (le_div_iff₀ (Real.exp_pos (3 * lam * a - (n : ℝ) * q))).mpr hprob
    change P.real E ≤ Real.exp (-3 * lam * a + (n : ℝ) * q)
    convert hh using 1 <;> rw [one_div, ← Real.exp_neg] <;> congr 1 <;> ring
  have hsub : {w : Shao.Path n | a ≤ Shao.upperMax w hn ∧ a ≤ Shao.lowerMax w hn} ⊆
      {w : Shao.Path n | ∃ j k : Fin (n + 1), j.val ≤ k.val ∧
        a ≤ 1 * Shao.prefixSum w j.val ∧ 1 * Shao.prefixSum w k.val ≤ -a} ∪
      {w : Shao.Path n | ∃ j k : Fin (n + 1), j.val ≤ k.val ∧
        a ≤ (-1) * Shao.prefixSum w j.val ∧ (-1) * Shao.prefixSum w k.val ≤ -a} := by
    intro w hw
    obtain ⟨j, hj0, hjn, hj⟩ := (Shao.upperMax_ge_iff w hn a).mp hw.1
    obtain ⟨k, hk0, hkn, hk⟩ := (Shao.upperMax_ge_iff (-w) hn a).mp hw.2
    rw [Shao.prefixSum_neg] at hk
    by_cases hjk : j ≤ k
    · left
      exact ⟨⟨j, by omega⟩, ⟨k, by omega⟩, hjk, by simpa using hj, by simpa using (neg_le_neg hk)⟩
    · right
      exact ⟨⟨k, by omega⟩, ⟨j, by omega⟩, by change k ≤ j; omega,
        by simpa using hk, by simpa using (neg_le_neg hj)⟩
  have hbound := (measureReal_mono (μ := P) hsub).trans ((measureReal_union_le _ _).trans
    (add_le_add (hOrder 1 (Or.inl rfl)) (hOrder (-1) (Or.inr rfl))))
  rw [hnq] at hbound
  convert hbound using 1 <;> ring

theorem source_centered_bounded_nonresidual_double_crossing :
    ∀ cstar : ℝ, 0 < cstar →
      let C : ℝ := Real.sqrt (2 * Real.pi) *
        (2 + 4 * Real.exp 1 / cstar)
      0 < C ∧
        ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu]
          (n : ℕ) (hn : 0 < n) (x : ℝ), 1 ≤ x →
          (∀ᵐ z : ℝ ∂nu, |z| ≤ 1 / (4 * x)) →
          (∫ z : ℝ, z ∂nu) = 0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
          let beta : ℝ := (n : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂nu)
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
          let u : ℝ := beta * (1 + x) ^ 3
          let D : Set (Shao.Path n) := Shao.C2.doubleCrossing hn x
          Integrable (fun z : ℝ => z ^ 2) nu ∧
            Integrable (fun z : ℝ => |z| ^ 3) nu ∧
            0 < beta ∧ 16 * x ^ 2 ≤ (n : ℝ) ∧ MeasurableSet D ∧
            Shao.truncationBudget nu n x = u ∧
            P.real D ≤
              Real.exp (-(1 / (5832 * beta ^ 2))) +
                2 * Real.exp (-4 * x ^ 2 + 24 * beta * x ^ 3) ∧
            (u ≤ 1 / 20000 → cstar * Real.exp (-3 * x ^ 2) ≤ u →
              P.real D ≤ C * u * Shao.standardNormalTail x) := by
  classical
  intro cstar hcstar C
  refine ⟨by dsimp [C]; positivity, ?_⟩
  intro nu hnu n hn x hx hsupport hmean hnorm beta P u D
  letI : IsProbabilityMeasure nu := hnu
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hx0 : 0 < x := by linarith
  let b : ℝ := 1 / (4 * x)
  let a : ℝ := 2 * Real.sqrt 2 * x / 3
  let lam : ℝ := 2 * Real.sqrt 2 * x
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hlam : 0 ≤ lam := by dsimp [lam]; positivity
  have hlamb : lam * b ≤ 1 := by
    have he : lam * b = Real.sqrt 2 / 2 := by dsimp [lam, b]; field_simp [ne_of_gt hx0]; ring
    rw [he]
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hdet := olt_deterministic_double_crossing nu n hn b a lam hb ha hlam hsupport hlamb hmean hnorm
  change Integrable (fun z : ℝ => z ^ 2) nu ∧ Integrable (fun z : ℝ => |z| ^ 3) nu ∧
    P.real {w : Shao.Path n | a ≤ Shao.upperMax w hn ∧ a ≤ Shao.lowerMax w hn} ≤
      2 * Real.exp (-3 * lam * a + lam ^ 2 / 2 + lam ^ 3 * beta) at hdet
  have h2 := hdet.1
  have h3 := hdet.2.1
  have hEnergy := finite_iid_energy_lower_tail nu n hn h2 h3 hnorm (1 / 9) (by norm_num) (by norm_num)
  change 0 < beta ∧ P.real {w : Shao.Path n | Shao.energy w ≤ 1 - (1 / 9 : ℝ)} ≤
    Real.exp (-((1 / 9 : ℝ) ^ 3 / (8 * beta ^ 2))) at hEnergy
  have hbeta : 0 < beta := hEnergy.1
  have hlow : P.real {w : Shao.Path n | Shao.energy w ≤ (8 / 9 : ℝ)} ≤
      Real.exp (-(1 / (5832 * beta ^ 2))) := by
    convert hEnergy.2 using 1 <;> norm_num <;> ring
  have hsecond : (∫ z : ℝ, z ^ 2 ∂nu) ≤ b ^ 2 := by
    apply (integral_mono_ae h2 (integrable_const (b ^ 2)) ?_).trans_eq
      (by simp)
    filter_upwards [hsupport] with z hz
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z) hz 2
  have hsize : 16 * x ^ 2 ≤ (n : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hsecond (Nat.cast_nonneg n)
    rw [hnorm] at hh
    have hb2 : b ^ 2 = 1 / (16 * x ^ 2) := by dsimp [b]; field_simp [ne_of_gt hx0]; ring
    rw [hb2] at hh
    have hdiv : 1 ≤ (n : ℝ) / (16 * x ^ 2) := by simpa only [div_eq_mul_inv, one_div, one_mul] using hh
    simpa only [one_mul] using (le_div_iff₀ (by positivity : 0 < 16 * x ^ 2)).mp hdiv
  have hDM : MeasurableSet D := Shao.C2.measurableSet_doubleCrossing hn x
  have hBudget : Shao.truncationBudget nu n x = u := by
    have heq : (fun z : ℝ => Shao.truncationF ((1 + x) * z)) =ᵐ[nu]
        (fun z : ℝ => (1 + x) ^ 3 * |z| ^ 3) := by
      filter_upwards [hsupport] with z hz
      have hbnd : (4 * x) * |z| ≤ 1 := by
        simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < 4 * x)).mp hz
      have hs : |(1 + x) * z| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 + x)]
        nlinarith [mul_nonneg (show 0 ≤ 4 * x - (1 + x) by linarith) (abs_nonneg z)]
      rw [Shao.truncationF_of_abs_le_one _ hs, abs_mul, abs_of_nonneg (by linarith), mul_pow]
    dsimp [Shao.truncationBudget]
    rw [integral_congr_ae heq, integral_const_mul]
    dsimp [u, beta]
    ring
  have hsub : D ⊆ {w : Shao.Path n | Shao.energy w ≤ (8 / 9 : ℝ)} ∪
      {w : Shao.Path n | a ≤ Shao.upperMax w hn ∧ a ≤ Shao.lowerMax w hn} := by
    intro w hw
    by_cases hq : Shao.energy w ≤ (8 / 9 : ℝ)
    · exact Or.inl hq
    · have hq0 : 0 ≤ Shao.energy w := Shao.energy_nonneg w
      have hrs := Real.sq_sqrt hq0
      have hr : 2 * Real.sqrt 2 / 3 ≤ Real.sqrt (Shao.energy w) := by
        nlinarith [Real.sqrt_nonneg (Shao.energy w)]
      have hwall : a ≤ x * Real.sqrt (Shao.energy w) := by
        have hh := mul_le_mul_of_nonneg_left hr hx0.le
        dsimp [a]
        nlinarith
      exact Or.inr ⟨hwall.trans hw.1, hwall.trans hw.2⟩
  have hhigh : 2 * Real.exp (-3 * lam * a + lam ^ 2 / 2 + lam ^ 3 * beta) ≤
      2 * Real.exp (-4 * x ^ 2 + 24 * beta * x ^ 3) := by
    have hid : -3 * lam * a + lam ^ 2 / 2 = -4 * x ^ 2 := by
      dsimp [lam, a]
      ring_nf
      rw [hsqrt]
      ring
    have hlam3 : lam ^ 3 ≤ 24 * x ^ 3 := by
      have hs : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [Real.sqrt_nonneg (2 : ℝ)]
      have hroot3 : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by
        calc
          _ = (Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring
          _ = _ := by rw [hsqrt]
      dsimp [lam]
      rw [mul_pow, mul_pow, hroot3]
      nlinarith [mul_le_mul_of_nonneg_right hs (pow_nonneg hx0.le 3)]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right hlam3 hbeta.le]
  have hExp : P.real D ≤ Real.exp (-(1 / (5832 * beta ^ 2))) +
      2 * Real.exp (-4 * x ^ 2 + 24 * beta * x ^ 3) :=
    (measureReal_mono (μ := P) hsub).trans ((measureReal_union_le _ _).trans
      (add_le_add hlow (hdet.2.2.trans hhigh)))
  refine ⟨h2, h3, hbeta, hsize, hDM, hBudget, hExp, ?_⟩
  intro husmall hunonres
  have hu : 0 < u := by dsimp [u]; positivity
  have hxplus : 1 ≤ 1 + x := by linarith
  have hpow1 : 1 ≤ (1 + x) ^ 6 := one_le_pow₀ hxplus
  have hpowx : x ^ 2 ≤ (1 + x) ^ 6 := by
    calc
      _ ≤ (1 + x) ^ 2 := pow_le_pow_left₀ hx0.le (by linarith) 2
      _ ≤ _ := pow_le_pow_right₀ hxplus (by norm_num : 2 ≤ 6)
  have huA : u ≤ (1 / 11664 : ℝ) := by linarith
  have hu2A : u ^ 2 ≤ (1 / 11664 : ℝ) := by nlinarith
  have hpower : u + u ^ 2 * x ^ 2 ≤ (1 / 5832 : ℝ) * (1 + x) ^ 6 := by
    have hleft : u ≤ (1 / 11664 : ℝ) * (1 + x) ^ 6 := by nlinarith
    have hright : u ^ 2 * x ^ 2 ≤ (1 / 11664 : ℝ) * (1 + x) ^ 6 := by
      exact (mul_le_mul_of_nonneg_right hu2A (sq_nonneg x)).trans
        (mul_le_mul_of_nonneg_left hpowx (by norm_num))
    linarith
  have hden : (1 / 5832 : ℝ) * (1 + x) ^ 6 / u ^ 2 = 1 / (5832 * beta ^ 2) := by
    dsimp [u]
    field_simp [ne_of_gt hbeta] <;> ring
  have hinv : x ^ 2 + 1 / u ≤ 1 / (5832 * beta ^ 2) := by
    rw [← hden]
    apply (le_div_iff₀ (sq_pos_of_pos hu)).mpr
    have hid : (x ^ 2 + 1 / u) * u ^ 2 = u + u ^ 2 * x ^ 2 := by field_simp [ne_of_gt hu]; ring
    rw [hid]
    exact hpower
  have hexpinv : Real.exp (-(1 / u)) ≤ u := by
    rw [Real.exp_neg, ← one_div]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    have hh := Real.add_one_le_exp (1 / u)
    have huinv : u * (1 / u) = 1 := by field_simp [ne_of_gt hu]
    nlinarith [mul_le_mul_of_nonneg_left hh hu.le]
  have hLowPaid : Real.exp (-(1 / (5832 * beta ^ 2))) ≤ u * Real.exp (-x ^ 2) := by
    calc
      _ ≤ Real.exp (-(x ^ 2 + 1 / u)) := Real.exp_le_exp.mpr (neg_le_neg hinv)
      _ = Real.exp (-x ^ 2) * Real.exp (-(1 / u)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-x ^ 2) * u := mul_le_mul_of_nonneg_left hexpinv (Real.exp_pos _).le
      _ = _ := mul_comm _ _
  have hcorrection : 24 * beta * x ^ 3 ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hx0.le (by linarith : x ≤ 1 + x) 3) hbeta.le
    change beta * x ^ 3 ≤ u at hh
    nlinarith
  have hHighPaid : 2 * Real.exp (-4 * x ^ 2 + 24 * beta * x ^ 3) ≤
      2 * Real.exp 1 * Real.exp (-4 * x ^ 2) := by
    rw [Real.exp_add]
    have hh := Real.exp_le_exp.mpr hcorrection
    nlinarith [mul_le_mul_of_nonneg_left hh (Real.exp_pos (-4 * x ^ 2)).le]
  have hRare : Real.exp (-4 * x ^ 2) ≤ (u / cstar) * Real.exp (-x ^ 2) := by
    have hh := mul_le_mul_of_nonneg_right hunonres (Real.exp_pos (-x ^ 2)).le
    have hid : Real.exp (-3 * x ^ 2) * Real.exp (-x ^ 2) = Real.exp (-4 * x ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_assoc, hid] at hh
    have hdiv := (le_div_iff₀ hcstar).mpr (by simpa only [mul_comm] using hh)
    convert hdiv using 1 <;> ring
  have hGauss : Real.exp (-x ^ 2) ≤ 2 * Real.sqrt (2 * Real.pi) * Shao.standardNormalTail x := by
    have ht : 0 < Shao.standardNormalTail x := (Shao.standardNormalTail_basic.2.2.1 x).1
    have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    have hd : Shao.standardNormalDensity x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
      simp [Shao.standardNormalDensity, ProbabilityTheory.gaussianPDFReal]
    have hm := (div_le_iff₀ (show 0 < 1 + x by linarith)).mp
      (Shao.standardNormal_mills_bounds x hx0.le).1
    rw [hd] at hm
    have hm' : Real.exp (-x ^ 2 / 2) ≤
        Real.sqrt (2 * Real.pi) * (Shao.standardNormalTail x * (1 + x)) := by
      have hh := mul_le_mul_of_nonneg_left hm hs.le
      simpa only [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] using hh
    have hexp : x ≤ Real.exp (x ^ 2 / 2) := by
      have hh := Real.add_one_le_exp (x ^ 2 / 2)
      nlinarith [sq_nonneg (x - 1)]
    have hweight : (1 + x) * Real.exp (-x ^ 2 / 2) ≤ 2 := by
      have hh : 1 + x ≤ 2 * Real.exp (x ^ 2 / 2) := by linarith
      have hp := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-x ^ 2 / 2)).le
      have he : Real.exp (x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) = 1 := by
        rw [← Real.exp_add]
        convert Real.exp_zero using 1 <;> congr 1 <;> ring
      nlinarith only [hp, he]
    calc
      _ = Real.exp (-x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ (Real.sqrt (2 * Real.pi) * (Shao.standardNormalTail x * (1 + x))) *
          Real.exp (-x ^ 2 / 2) := mul_le_mul_of_nonneg_right hm' (Real.exp_pos _).le
      _ = (Real.sqrt (2 * Real.pi) * Shao.standardNormalTail x) *
          ((1 + x) * Real.exp (-x ^ 2 / 2)) := by ring
      _ ≤ (Real.sqrt (2 * Real.pi) * Shao.standardNormalTail x) * 2 :=
        mul_le_mul_of_nonneg_left hweight (by positivity)
      _ = _ := by ring
  calc
    P.real D ≤ u * Real.exp (-x ^ 2) + 2 * Real.exp 1 * Real.exp (-4 * x ^ 2) :=
      hExp.trans (add_le_add hLowPaid hHighPaid)
    _ ≤ u * Real.exp (-x ^ 2) + 2 * Real.exp 1 * ((u / cstar) * Real.exp (-x ^ 2)) := by
      gcongr
    _ = (1 + 2 * Real.exp 1 / cstar) * u * Real.exp (-x ^ 2) := by ring
    _ ≤ (1 + 2 * Real.exp 1 / cstar) * u *
        (2 * Real.sqrt (2 * Real.pi) * Shao.standardNormalTail x) :=
      mul_le_mul_of_nonneg_left hGauss (by positivity)
    _ = C * u * Shao.standardNormalTail x := by dsimp [C]; ring

end Shao.Probability.SourceOriginalLargeThreshold
