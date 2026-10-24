/- Mathematical candidate only. No production bodies, Lean checks, or AX replay.
   PR328 is an exact-source mathematical dependency pending Root qualification.
   All Brownian events below use the actual process, including every real time.
   No new definitions, instances, global helpers, or private helpers are proposed. -/
import Shao.Probability.SourceOriginalLargeThreshold
import Shao.C2.BrownianUpperJointReflection
import Shao.OQ4.PolygonalBrownianWeakLimit
import Mathlib.Probability.Distributions.Gaussian.Real

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
noncomputable section
namespace Shao.Probability.SourceNonresidualBrownian
open MeasureTheory ProbabilityTheory
open Shao.C2.BridgeDomination
open scoped BigOperators NNReal

private theorem gaussian_grid_two_wall_bound
    (N : ℕ) (hN : 0 < N) (a : ℝ) (ha : 0 < a) :
    let gamma : Measure ℝ := gaussianReal 0 ((N : ℝ≥0)⁻¹)
    let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => gamma)
    P.real {w : Shao.Path N |
      a ≤ Shao.upperMax w hN ∧ a ≤ Shao.lowerMax w hN} ≤
        2 * Real.exp (-9 * a ^ 2 / 2) := by
  classical
  intro gamma P
  letI : IsProbabilityMeasure gamma := by dsimp [gamma]; infer_instance
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  let lam : ℝ := 3 * a
  have hlam : 0 ≤ lam := by dsimp [lam]; positivity
  let clip : ℕ → Shao.Path N → Shao.Path N :=
    fun k w j => if j.val < k then w j else 0
  let q : ℝ := lam ^ 2 / (2 * (N : ℝ))
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hnq : (N : ℝ) * q = lam ^ 2 / 2 := by
    dsimp [q]
    field_simp [hNr] <;> ring
  have hMG (s : ℝ) (hs : s = 1 ∨ s = -1) :
      Integrable (fun z : ℝ => Real.exp (lam * s * z)) gamma ∧
        (∫ z : ℝ, Real.exp (lam * s * z) ∂gamma) ≤ Real.exp q := by
    have hi := integrable_exp_mul_gaussianReal
      (μ := (0 : ℝ)) (v := (N : ℝ≥0)⁻¹) (lam * s)
    have hLaw : HasLaw (fun z : ℝ => z) gamma gamma :=
      ⟨measurable_id.aemeasurable, by simp⟩
    have hm := mgf_gaussianReal hLaw (lam * s)
    change (∫ z : ℝ, Real.exp (lam * s * z) ∂gamma) =
      Real.exp (0 * (lam * s) + ((N : ℝ≥0)⁻¹ : ℝ≥0) * (lam * s) ^ 2 / 2) at hm
    refine ⟨hi, le_of_eq (hm.trans ?_)⟩
    congr 1
    rcases hs with rfl | rfl <;>
      simp only [zero_mul, zero_add, mul_one, mul_neg, mul_zero, neg_sq,
        NNReal.coe_inv, NNReal.coe_natCast] <;> dsimp [q] <;> field_simp [hNr] <;> ring
  have hExpAbs : Integrable (fun z : ℝ => Real.exp (lam * |z|)) gamma := by
    apply ((hMG 1 (Or.inl rfl)).1.add ((hMG (-1) (Or.inr rfl)).1)).mono'
      (by fun_prop)
    exact ae_of_all gamma fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      simp only [Pi.add_apply]
      by_cases hz : 0 ≤ z
      · rw [abs_of_nonneg hz]
        simp only [mul_one]
        linarith [Real.exp_pos (lam * (-1) * z)]
      · rw [abs_of_neg (lt_of_not_ge hz)]
        have he : lam * -z = lam * (-1) * z := by ring
        rw [he]
        linarith [Real.exp_pos (lam * 1 * z)]
  have hFactor (i : Fin N) (F : Shao.Path N → ℝ) (hFm : Measurable F)
      (hFi : Integrable F P) (hdep : ∀ w, F (clip i.val w) = F w)
      (g : ℝ → ℝ) (hgm : Measurable g) (hgi : Integrable g gamma) :
      Integrable (fun w : Shao.Path N => F w * g (w i)) P ∧
        (∫ w : Shao.Path N, F w * g (w i) ∂P) =
          (∫ w : Shao.Path N, F w ∂P) * (∫ z : ℝ, g z ∂gamma) := by
    let past : Finset (Fin N) := Finset.univ.filter (fun j => j.val < i.val)
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
    have hfeq (w : Shao.Path N) : f (fun j : past => w j) = F w := by
      simpa [f, past, clip] using hdep w
    have hXi : iIndepFun (fun j : Fin N => fun w : Shao.Path N => w j) P :=
      iIndepFun_pi (fun _ : Fin N => measurable_id.aemeasurable)
    have hdisj : Disjoint past ({i} : Finset (Fin N)) := by
      simp [past, Finset.disjoint_singleton_right]
    have ht := hXi.indepFun_finset past {i} hdisj (fun j => measurable_pi_apply j)
    have hright : Measurable (fun v : ({i} : Finset (Fin N)) → ℝ => g (v ⟨i, by simp⟩)) :=
      hgm.comp (measurable_pi_apply (X := fun _ : ({i} : Finset (Fin N)) => ℝ) ⟨i, by simp⟩)
    have hind : IndepFun F (fun w : Shao.Path N => g (w i)) P := by
      simpa only [Function.comp_def, hfeq] using ht.comp hfm hright
    have hcur : Integrable (fun w : Shao.Path N => g (w i)) P :=
      (measurePreserving_eval (fun _ : Fin N => gamma) i).integrable_comp_of_integrable hgi
    refine ⟨hind.integrable_mul hFi hcur, ?_⟩
    rw [hind.integral_fun_mul_eq_mul_integral hFi.aestronglyMeasurable hcur.aestronglyMeasurable]
    congr 1
    exact integral_comp_eval hgi.aestronglyMeasurable
  have hPrefixClip (w : Shao.Path N) (k j : ℕ) (hj : j ≤ k) :
      Shao.prefixSum (clip k w) j = Shao.prefixSum w j := by
    unfold Shao.prefixSum
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i.val < j := (Finset.mem_filter.mp hi).2
    simp only [clip, if_pos (lt_of_lt_of_le hi' hj)]
  let MA : ℕ → Shao.Path N → ℝ := fun k w =>
    Real.exp (lam * ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k), |w i|)
  have hMAM (k : ℕ) : Measurable (MA k) := by
    dsimp [MA]
    fun_prop
  have hMAStep (i : Fin N) (w : Shao.Path N) :
      MA (i.val + 1) w = MA i.val w * Real.exp (lam * |w i|) := by
    have hs : Finset.univ.filter (fun j : Fin N => j.val < i.val + 1) =
        insert i (Finset.univ.filter (fun j : Fin N => j.val < i.val)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hj
        by_cases he : j = i
        · exact Or.inl he
        · exact Or.inr (by have : j.val ≠ i.val := fun h => he (Fin.ext h); omega)
      · rintro (rfl | hj) <;> omega
    dsimp [MA]
    rw [hs, Finset.sum_insert (by simp), ← Real.exp_add]
    congr 1
    ring
  have hMAI : ∀ k : ℕ, k ≤ N → Integrable (MA k) P := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa [MA] using (integrable_const (1 : ℝ) : Integrable (fun _ : Shao.Path N => (1 : ℝ)) P)
    | succ k ih =>
      intro hk
      let i : Fin N := ⟨k, by omega⟩
      have hdep (w : Shao.Path N) : MA k (clip i.val w) = MA k w := by
        dsimp [MA]
        congr 1
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        have hji : j.val < k := (Finset.mem_filter.mp hj).2
        simp only [clip, i, if_pos hji]
      have hh := hFactor i (MA k) (hMAM k) (ih (by omega)) hdep
        (fun z => Real.exp (lam * |z|)) (by fun_prop) hExpAbs
      exact hh.1.congr (ae_of_all P fun w => (hMAStep i w).symm)
  have hOrder (eta : ℝ) (heta : eta = 1 ∨ eta = -1) :
      P.real {w : Shao.Path N | ∃ j k : Fin (N + 1), j.val ≤ k.val ∧
        a ≤ eta * Shao.prefixSum w j.val ∧ eta * Shao.prefixSum w k.val ≤ -a} ≤
        Real.exp (-3 * lam * a + (N : ℝ) * q) := by
    let eps : Fin N → Shao.Path N → ℝ := fun i w =>
      if ∃ j : Fin (i.val + 1), a ≤ eta * Shao.prefixSum w j.val then -eta else eta
    let Y : ℕ → Shao.Path N → ℝ := fun k w =>
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k), eps i w * w i
    let Z : ℕ → Shao.Path N → ℝ := fun k w => Real.exp (lam * Y k w - (k : ℝ) * q)
    let live : ℕ → Shao.Path N → Prop := fun k w =>
      ∀ j : Fin (k + 1), Y j.val w < 3 * a
    let delta : ℕ → Shao.Path N → ℝ := fun k w =>
      if live k w then Z (k + 1) w - Z k w else 0
    let W : Shao.Path N → ℝ := fun w => 1 + ∑ k ∈ Finset.range N, delta k w
    let E : Set (Shao.Path N) := {w | ∃ j k : Fin (N + 1), j.val ≤ k.val ∧
      a ≤ eta * Shao.prefixSum w j.val ∧ eta * Shao.prefixSum w k.val ≤ -a}
    have hEtaAbs : |eta| = 1 := by rcases heta with rfl | rfl <;> norm_num
    have hEpsSign (i : Fin N) (w : Shao.Path N) : eps i w = 1 ∨ eps i w = -1 := by
      dsimp [eps]
      split_ifs <;> rcases heta with rfl | rfl <;> norm_num
    have hEpsAbs (i : Fin N) (w : Shao.Path N) : |eps i w| = 1 := by
      rcases hEpsSign i w with h | h <;> rw [h] <;> norm_num
    have hEpsM (i : Fin N) : Measurable (eps i) := by
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
    have hY0 (w : Shao.Path N) : Y 0 w = 0 := by simp [Y]
    have hZ0 (w : Shao.Path N) : Z 0 w = 1 := by simp [Z, hY0]
    have hYStep (i : Fin N) (w : Shao.Path N) :
        Y (i.val + 1) w = Y i.val w + eps i w * w i := by
      have hsets : Finset.univ.filter (fun j : Fin N => j.val < i.val + 1) =
          insert i (Finset.univ.filter (fun j : Fin N => j.val < i.val)) := by
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
    have hYBound (k : ℕ) (w : Shao.Path N) :
        |Y k w| ≤ ∑ i : Fin N, |w i| := by
      calc
        _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k), |eps i w * w i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k), |w i| := by
          apply Finset.sum_congr rfl
          intro i _
          rw [abs_mul, hEpsAbs, one_mul]
        _ ≤ ∑ i : Fin N, |w i| :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => abs_nonneg _)
    have hZI (k : ℕ) : Integrable (Z k) P := by
      apply (hMAI N le_rfl).mono' (hZM k).aestronglyMeasurable
      exact ae_of_all P fun w => by
        change |Real.exp (lam * Y k w - (k : ℝ) * q)| ≤
          Real.exp (lam * ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < N), |w i|)
        rw [abs_of_pos (Real.exp_pos _),
          Finset.filter_eq_self.mpr (fun i _ => i.isLt)]
        apply Real.exp_le_exp.mpr
        have hy := (le_abs_self (Y k w)).trans (hYBound k w)
        have hkq : 0 ≤ (k : ℝ) * q := mul_nonneg (Nat.cast_nonneg _) hq
        nlinarith [mul_le_mul_of_nonneg_left hy hlam]
    have hEpsClip (k : ℕ) (i : Fin N) (hi : i.val ≤ k) (w : Shao.Path N) :
        eps i (clip k w) = eps i w := by
      have he : (∃ j : Fin (i.val + 1), a ≤ eta * Shao.prefixSum (clip k w) j.val) ↔
          ∃ j : Fin (i.val + 1), a ≤ eta * Shao.prefixSum w j.val := by
        constructor <;> rintro ⟨j, hj⟩ <;> refine ⟨j, ?_⟩
        · simpa only [hPrefixClip w k j.val (by omega)] using hj
        · simpa only [hPrefixClip w k j.val (by omega)] using hj
      simp only [eps, he]
    have hYClip (k j : ℕ) (hj : j ≤ k) (w : Shao.Path N) : Y j (clip k w) = Y j w := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i.val < j := (Finset.mem_filter.mp hi).2
      rw [hEpsClip k i (by omega) w]
      simp only [clip, if_pos (by omega : i.val < k)]
    have hZClip (k j : ℕ) (hj : j ≤ k) (w : Shao.Path N) : Z j (clip k w) = Z j w := by
      simp only [Z, hYClip k j hj w]
    have hLiveClip (k : ℕ) (w : Shao.Path N) : live k (clip k w) ↔ live k w := by
      dsimp [live]
      constructor <;> intro h j <;> simpa only [hYClip k j.val (by omega) w] using h j
    have hDelta (k : ℕ) (hk : k < N) : Integrable (delta k) P ∧ (∫ w, delta k w ∂P) ≤ 0 := by
      let i : Fin N := ⟨k, hk⟩
      let Hplus : Shao.Path N → ℝ := fun w => if live k w ∧ eps i w = 1 then Z k w else 0
      let Hminus : Shao.Path N → ℝ := fun w => if live k w ∧ eps i w = -1 then Z k w else 0
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
      have hHpDep (w : Shao.Path N) : Hplus (clip i.val w) = Hplus w := by
        simp only [Hplus, i, hLiveClip, hEpsClip k i le_rfl w, hZClip k k le_rfl w]
      have hHmDep (w : Shao.Path N) : Hminus (clip i.val w) = Hminus w := by
        simp only [Hminus, i, hLiveClip, hEpsClip k i le_rfl w, hZClip k k le_rfl w]
      have hp := hFactor i Hplus hHpM hHpI hHpDep (fun z => Real.exp (lam * z))
        (by fun_prop) (by simpa using (hMG 1 (Or.inl rfl)).1)
      have hm := hFactor i Hminus hHmM hHmI hHmDep (fun z => Real.exp (-lam * z))
        (by fun_prop) (by simpa using (hMG (-1) (Or.inr rfl)).1)
      have hpoint (w : Shao.Path N) : delta k w =
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
        _ = Real.exp (-q) * ((∫ w, Hplus w ∂P) * (∫ z, Real.exp (lam * z) ∂gamma) +
            (∫ w, Hminus w ∂P) * (∫ z, Real.exp (-lam * z) ∂gamma)) -
            ((∫ w, Hplus w ∂P) + (∫ w, Hminus w ∂P)) := by
          rw [integral_congr_ae (ae_of_all P hpoint), integral_sub
            (f := fun w : Shao.Path N => Real.exp (-q) *
              (Hplus w * Real.exp (lam * w i) + Hminus w * Real.exp (-lam * w i)))
            (g := fun w : Shao.Path N => Hplus w + Hminus w)
            ((hp.1.add hm.1).const_mul (Real.exp (-q))) (hHpI.add hHmI), integral_const_mul,
            integral_add (f := fun w : Shao.Path N => Hplus w * Real.exp (lam * w i))
              (g := fun w : Shao.Path N => Hminus w * Real.exp (-lam * w i)) hp.1 hm.1,
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
    have hTel (w : Shao.Path N) (m : ℕ) :
        (∑ k ∈ Finset.range m, (Z (k + 1) w - Z k w)) = Z m w - 1 := by
      induction m with
      | zero => simp [hZ0]
      | succ m ih => rw [Finset.sum_range_succ, ih]; ring
    have hStop (w : Shao.Path N) :
        0 ≤ W w ∧ ((∃ k : Fin (N + 1), 3 * a ≤ Y k.val w) →
          Real.exp (3 * lam * a - (N : ℝ) * q) ≤ W w) := by
      by_cases hh : ∃ k : ℕ, k ≤ N ∧ 3 * a ≤ Y k w
      · let j : ℕ := Nat.find hh
        have hjn : j ≤ N := (Nat.find_spec hh).1
        have hjhit : 3 * a ≤ Y j w := (Nat.find_spec hh).2
        have hLive (k : ℕ) (hkn : k < N) : live k w ↔ k < j := by
          constructor
          · intro hl
            by_contra hk
            have hjk : j ≤ k := Nat.le_of_not_gt hk
            have hj := hl ⟨j, by omega⟩
            linarith
          · intro hkj ell
            have hellj : ell.val < j := by omega
            have hnot := Nat.find_min hh hellj
            have helln : ell.val ≤ N := by omega
            exact lt_of_not_ge (fun h => hnot ⟨helln, h⟩)
        have hsum : (∑ k ∈ Finset.range N, delta k w) =
            ∑ k ∈ Finset.range j, (Z (k + 1) w - Z k w) := by
          calc
            _ = ∑ k ∈ Finset.range N, if k < j then Z (k + 1) w - Z k w else 0 := by
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
        have htime := mul_le_mul_of_nonneg_right (show (j : ℝ) ≤ (N : ℝ) by exact_mod_cast hjn) hq
        nlinarith
      · have hLive (k : ℕ) (hk : k < N) : live k w := by
          intro j
          apply lt_of_not_ge
          intro hj
          exact hh ⟨j.val, by omega, hj⟩
        have hW : W w = Z N w := by
          dsimp [W]
          have he : (∑ k ∈ Finset.range N, delta k w) =
              ∑ k ∈ Finset.range N, (Z (k + 1) w - Z k w) := by
            apply Finset.sum_congr rfl
            intro k hk
            simp only [delta, if_pos (hLive k (Finset.mem_range.mp hk))]
          rw [he, hTel]
          ring
        refine ⟨by rw [hW]; exact (Real.exp_pos _).le, ?_⟩
        rintro ⟨k, hk⟩
        exact False.elim (hh ⟨k.val, by omega, hk⟩)
    have hEhit (w : Shao.Path N) (hw : w ∈ E) : ∃ k : Fin (N + 1), 3 * a ≤ Y k.val w := by
      obtain ⟨j, k, hjk, hj, hk⟩ := hw
      have hex : ∃ ell : ℕ, a ≤ eta * Shao.prefixSum w ell := ⟨j.val, hj⟩
      let tau : ℕ := Nat.find hex
      have htau : a ≤ eta * Shao.prefixSum w tau := Nat.find_spec hex
      have htauj : tau ≤ j.val := Nat.find_min' hex hj
      have htauk : tau ≤ k.val := htauj.trans hjk
      have heps (i : Fin N) : eps i w = if i.val < tau then eta else -eta := by
        by_cases hi : i.val < tau
        · have hnot : ¬∃ ell : Fin (i.val + 1), a ≤ eta * Shao.prefixSum w ell.val := by
            rintro ⟨ell, hell⟩
            exact Nat.find_min hex (by omega : ell.val < tau) hell
          simp only [eps, if_neg hnot, if_pos hi]
        · have hyes : ∃ ell : Fin (i.val + 1), a ≤ eta * Shao.prefixSum w ell.val :=
            ⟨⟨tau, by omega⟩, htau⟩
          simp only [eps, if_pos hyes, if_neg hi]
      have hsets : (Finset.univ.filter (fun i : Fin N => i.val < k.val)).filter
          (fun i : Fin N => i.val < tau) = Finset.univ.filter (fun i : Fin N => i.val < tau) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      have hY : Y k.val w = 2 * eta * Shao.prefixSum w tau - eta * Shao.prefixSum w k.val := by
        calc
          _ = ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k.val),
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
      rw [show W = fun w => 1 + ∑ k ∈ Finset.range N, delta k w from rfl,
        integral_add (integrable_const (1 : ℝ))
          (integrable_finsetSum _ fun k hk => (hDelta k (Finset.mem_range.mp hk)).1),
        integral_const, probReal_univ, one_smul,
        integral_finsetSum _ fun k hk => (hDelta k (Finset.mem_range.mp hk)).1]
      have hs : (∑ k ∈ Finset.range N, ∫ w, delta k w ∂P) ≤ 0 :=
        Finset.sum_nonpos fun k hk => (hDelta k (Finset.mem_range.mp hk)).2
      linarith
    have hInd : ∀ w : Shao.Path N, E.indicator
        (fun _ => Real.exp (3 * lam * a - (N : ℝ) * q)) w ≤ W w := by
      intro w
      by_cases hw : w ∈ E
      · rw [Set.indicator_of_mem hw]
        exact (hStop w).2 (hEhit w hw)
      · rw [Set.indicator_of_notMem hw]
        exact (hStop w).1
    have hprob : P.real E * Real.exp (3 * lam * a - (N : ℝ) * q) ≤ 1 := by
      calc
        _ = ∫ w, E.indicator (fun _ => Real.exp (3 * lam * a - (N : ℝ) * q)) w ∂P := by
          rw [integral_indicator_const _ hEM, smul_eq_mul]
        _ ≤ ∫ w, W w ∂P := integral_mono ((integrable_const _).indicator hEM) hWI hInd
        _ ≤ _ := hWmean
    have hh := (le_div_iff₀ (Real.exp_pos (3 * lam * a - (N : ℝ) * q))).mpr hprob
    change P.real E ≤ Real.exp (-3 * lam * a + (N : ℝ) * q)
    convert hh using 1 <;> rw [one_div, ← Real.exp_neg] <;> congr 1 <;> ring
  have hsub : {w : Shao.Path N | a ≤ Shao.upperMax w hN ∧ a ≤ Shao.lowerMax w hN} ⊆
      {w : Shao.Path N | ∃ j k : Fin (N + 1), j.val ≤ k.val ∧
        a ≤ 1 * Shao.prefixSum w j.val ∧ 1 * Shao.prefixSum w k.val ≤ -a} ∪
      {w : Shao.Path N | ∃ j k : Fin (N + 1), j.val ≤ k.val ∧
        a ≤ (-1) * Shao.prefixSum w j.val ∧ (-1) * Shao.prefixSum w k.val ≤ -a} := by
    intro w hw
    obtain ⟨j, hj0, hjn, hj⟩ := (Shao.upperMax_ge_iff w hN a).mp hw.1
    obtain ⟨k, hk0, hkn, hk⟩ := (Shao.upperMax_ge_iff (-w) hN a).mp hw.2
    rw [Shao.prefixSum_neg] at hk
    by_cases hjk : j ≤ k
    · left
      exact ⟨⟨j, by omega⟩, ⟨k, by omega⟩, hjk, by simpa using hj, by simpa using (neg_le_neg hk)⟩
    · right
      exact ⟨⟨k, by omega⟩, ⟨j, by omega⟩, by change k ≤ j; omega,
        by simpa using hk, by simpa using (neg_le_neg hj)⟩
  have hbound := (measureReal_mono (μ := P) hsub).trans ((measureReal_union_le _ _).trans
    (add_le_add (hOrder 1 (Or.inl rfl)) (hOrder (-1) (Or.inr rfl))))
  have he : -3 * lam * a + lam ^ 2 / 2 = -9 * a ^ 2 / 2 := by
    dsimp [lam]
    ring
  rw [hnq, he] at hbound
  simpa only [two_mul] using hbound

theorem actual_brownian_weak_double_crossing
    {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hB : IsBrownianReal B PB) (x : ℝ) (hx : 0 < x) :
    let U : Set ΩB :=
      {omega | ∃ t : BridgeTime, x ≤ B ⟨(t : ℝ), t.property.1⟩ omega}
    let L : Set ΩB :=
      {omega | ∃ t : BridgeTime, B ⟨(t : ℝ), t.property.1⟩ omega ≤ -x}
    let DB : Set ΩB := U ∩ L
    let H : ℝ := PB.real
      {omega | ∃ t : BridgeTime, x ≤ |B ⟨(t : ℝ), t.property.1⟩ omega|}
    let d : ℝ := PB.real DB
    NullMeasurableSet U PB ∧ NullMeasurableSet L PB ∧
      NullMeasurableSet DB PB ∧ NullMeasurableSet (U ∪ L) PB ∧
      d = 4 * Shao.standardNormalTail x - H ∧
      0 ≤ d ∧ d ≤ 2 * Shao.standardNormalTail x ∧
      d ≤ 2 * Real.exp (-9 * x ^ 2 / 2) := by
  classical
  exact (open Filter Topology Shao.OQ4.PolygonalBrownianWeakLimit in by
    intro U L DB H d
    have hUpperNull (Y : ℝ≥0 → ΩB → ℝ) (hY : IsBrownianReal Y PB) :
        NullMeasurableSet {omega | ∃ t : BridgeTime,
          x ≤ Y ⟨(t : ℝ), t.property.1⟩ omega} PB := by
      let K : Set C(BridgeTime, ℝ) := {f | ∃ t : BridgeTime, x ≤ f t}
      have ho : IsOpen {f : C(BridgeTime, ℝ) | ∀ t : BridgeTime, f t < x} := by
        simpa [Set.MapsTo] using
          (ContinuousMap.isOpen_setOfPred_mapsTo (X := BridgeTime)
            isCompact_univ (isOpen_Iio (a := x)))
      have hK : MeasurableSet K := by
        have he : K = {f : C(BridgeTime, ℝ) | ∀ t : BridgeTime, f t < x}ᶜ := by
          ext f
          simp only [K, Set.mem_setOf_eq, Set.mem_compl_iff, not_forall, not_lt]
        rw [he]
        exact ho.measurableSet.compl
      have hn := (aemeasurable_brownianUnitPath Y 1 PB hY).nullMeasurableSet_preimage hK
      apply hn.congr
      filter_upwards [ae_brownianUnitPath_eq Y 1 PB hY] with omega homega
      apply propext
      change (∃ t : BridgeTime, x ≤ brownianUnitPath Y 1 omega t) ↔ _
      have he (t : BridgeTime) : brownianUnitPath Y 1 omega t =
          Y ⟨(t : ℝ), t.property.1⟩ omega := by
        have hh := homega t
        change brownianUnitPath Y 1 omega t =
          Y (1 * ⟨(t : ℝ), t.property.1⟩) omega at hh
        exact hh.trans (congrArg (fun q : ℝ≥0 => Y q omega) (_root_.one_mul _))
      simp only [he]
    have hU : NullMeasurableSet U PB := hUpperNull B hB
    have hLEq : L = {omega | ∃ t : BridgeTime,
        x ≤ (-B) ⟨(t : ℝ), t.property.1⟩ omega} := by
      ext omega
      change (∃ t : BridgeTime, B ⟨(t : ℝ), t.property.1⟩ omega ≤ -x) ↔
        ∃ t : BridgeTime, x ≤ -B ⟨(t : ℝ), t.property.1⟩ omega
      constructor <;> rintro ⟨t, ht⟩ <;> exact ⟨t, by linarith⟩
    have hL : NullMeasurableSet L PB := by
      rw [hLEq]
      exact hUpperNull (-B) hB.neg
    have hDB : NullMeasurableSet DB PB := hU.inter hL
    have hUL : NullMeasurableSet (U ∪ L) PB := hU.union hL
    have hSingle (Y : ℝ≥0 → ΩB → ℝ) (hY : IsBrownianReal Y PB) :
        PB.real {omega | ∃ t : BridgeTime,
          x ≤ Y ⟨(t : ℝ), t.property.1⟩ omega} = 2 * Shao.standardNormalTail x := by
      let S : Set ΩB := {omega | ∀ t : BridgeTime,
        Y ⟨(t : ℝ), t.property.1⟩ omega < x}
      let r : ℕ → ℝ := fun j => x - 1 / ((j : ℝ) + 1)
      let E : ℕ → Set ΩB := fun j => S ∩ {omega | Y 1 omega ≤ r j}
      have hrx (j : ℕ) : r j < x := by
        have hp : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
        dsimp [r]
        linarith
      have hrmono : Monotone r := by
        intro i j hij
        have hij' : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by
          exact_mod_cast Nat.add_le_add_right hij 1
        have hd := one_div_le_one_div_of_le
          (by positivity : (0 : ℝ) < (i : ℝ) + 1) hij' 
        dsimp [r]
        linarith
      have hEmono : Monotone E := by
        intro i j hij omega homega
        exact ⟨homega.1, homega.2.trans (hrmono hij)⟩
      have hEU : (⋃ j, E j) = S := by
        ext omega
        constructor
        · intro hj
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hj
          exact hj.1
        · intro homega
          have he : Y 1 omega < x := homega 1
          obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.mpr he)
          apply Set.mem_iUnion.mpr
          refine ⟨j, homega, ?_⟩
          dsimp [r]
          linarith
      have hELimit : Filter.Tendsto (fun j => PB.real (E j)) Filter.atTop
          (nhds (PB.real S)) := by
        have hh := tendsto_measure_iUnion_atTop (μ := PB) hEmono
        rw [hEU] at hh
        exact (ENNReal.continuousAt_toReal (measure_ne_top PB S)).tendsto.comp hh
      have hJ (j : ℕ) : PB.real (E j) = 1 - Shao.standardNormalTail (r j) -
          Shao.standardNormalTail (2 * x - r j) := by
        have hh := Shao.C2.BrownianUpperJointReflection.brownian_upper_joint_reflection
          Y PB hY x (r j) hx (hrx j)
        change PB.real (E j) + (gaussianReal 0 1).real (Set.Ici (2 * x - r j)) =
          (gaussianReal 0 1).real (Set.Iic (r j)) at hh
        have htail := (Shao.standardNormalTail_representation (2 * x - r j)).1
        have hcdf := (Shao.standardNormalTail_representation (r j)).2.1
        rw [ProbabilityTheory.cdf_eq_real] at hcdf
        change Shao.standardNormalTail (2 * x - r j) =
          (gaussianReal 0 1).real (Set.Ici (2 * x - r j)) at htail
        rw [← htail] at hh
        linarith
      have hr : Filter.Tendsto r Filter.atTop (nhds x) := by
        simpa only [r, sub_zero] using (tendsto_const_nhds.sub
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
      have hrr : Filter.Tendsto (fun j => 2 * x - r j) Filter.atTop (nhds x) := by
        convert tendsto_const_nhds.sub hr using 1 <;> ring
      have hc := (Shao.standardNormal_derivatives x).2.continuousAt.tendsto
      have hf : Filter.Tendsto (fun j => 1 - Shao.standardNormalTail (r j) -
          Shao.standardNormalTail (2 * x - r j)) Filter.atTop
          (nhds (1 - 2 * Shao.standardNormalTail x)) := by
        have hconst : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
          tendsto_const_nhds
        have hh := (hconst.sub (hc.comp hr)).sub (hc.comp hrr)
        simpa only [Function.comp_apply, show 1 - Shao.standardNormalTail x -
          Shao.standardNormalTail x = 1 - 2 * Shao.standardNormalTail x from by ring] using hh
      have hS : PB.real S = 1 - 2 * Shao.standardNormalTail x :=
        tendsto_nhds_unique hELimit (by simpa only [hJ] using hf)
      have hCEq : {omega | ∃ t : BridgeTime,
          x ≤ Y ⟨(t : ℝ), t.property.1⟩ omega}ᶜ = S := by
        ext omega
        simp only [S, Set.mem_compl_iff, Set.mem_setOf_eq, not_exists, not_le]
      have hh := measureReal_add_measureReal_compl₀ (hUpperNull Y hY)
      rw [hCEq, probReal_univ, hS] at hh
      linarith
    have hUP : PB.real U = 2 * Shao.standardNormalTail x := hSingle B hB
    have hLP : PB.real L = 2 * Shao.standardNormalTail x := by
      rw [hLEq]
      exact hSingle (-B) hB.neg
    have hHEq : {omega | ∃ t : BridgeTime,
        x ≤ |B ⟨(t : ℝ), t.property.1⟩ omega|} = U ∪ L := by
      ext omega
      constructor
      · rintro ⟨t, ht⟩
        by_cases hpos : 0 ≤ B ⟨(t : ℝ), t.property.1⟩ omega
        · left
          exact ⟨t, by simpa only [abs_of_nonneg hpos] using ht⟩
        · right
          refine ⟨t, ?_⟩
          rw [abs_of_neg (lt_of_not_ge hpos)] at ht
          linarith
      · rintro (⟨t, ht⟩ | ⟨t, ht⟩)
        · exact ⟨t, ht.trans (le_abs_self _)⟩
        · exact ⟨t, (by linarith : x ≤ -B ⟨(t : ℝ), t.property.1⟩ omega).trans (neg_le_abs _)⟩
    have hIdentity : d = 4 * Shao.standardNormalTail x - H := by
      have hh := measureReal_union_add_inter₀ (s := U) hL
      rw [hUP, hLP] at hh
      change PB.real (U ∪ L) + d = _ at hh
      have he : H = PB.real (U ∪ L) := by dsimp [H]; rw [hHEq]
      linarith
    refine ⟨hU, hL, hDB, hUL, hIdentity, measureReal_nonneg,
      (measureReal_mono (μ := PB) Set.inter_subset_left).trans hUP.le, ?_⟩
    -- Actual all-real-time bound, with weak walls obtained by a < x then a ↑ x.
    let T : ℕ → ℕ → ℝ≥0 := fun m k => (k : ℝ≥0) / ((2 ^ m : ℕ) : ℝ≥0)
    have hN (m : ℕ) : 0 < 2 ^ m := by positivity
    let grid : (m : ℕ) → Fin (2 ^ m) → BridgeTime := fun m i =>
      ⟨((i.val + 1 : ℕ) : ℝ) / ((2 ^ m : ℕ) : ℝ), by
        have hn : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by positivity
        constructor
        · positivity
        · exact (div_le_one hn).mpr (by exact_mod_cast (Nat.succ_le_iff.mpr i.isLt))⟩
    have hGridTime (m : ℕ) (i : Fin (2 ^ m)) :
        (⟨(grid m i : ℝ), (grid m i).property.1⟩ : ℝ≥0) = T m (i.val + 1) := by
      apply NNReal.coe_injective
      simp only [grid, T, NNReal.coe_div, NNReal.coe_natCast] <;> rfl
    have hStep (m : ℕ) (i : Fin (2 ^ m)) : ∃ j : Fin (2 ^ (m + 1)),
        T (m + 1) (j.val + 1) = T m (i.val + 1) := by
      let j : Fin (2 ^ (m + 1)) := ⟨2 * i.val + 1, by
        rw [pow_succ]
        omega⟩
      refine ⟨j, ?_⟩
      dsimp [T, j]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Nat.cast_pow]
      rw [pow_succ]
      field_simp
      ring
    have hLift (m n : ℕ) (hmn : m ≤ n) (i : Fin (2 ^ m)) :
        ∃ j : Fin (2 ^ n), T n (j.val + 1) = T m (i.val + 1) := by
      induction n, hmn using Nat.le_induction with
      | base => exact ⟨i, rfl⟩
      | succ n hmn ih =>
        obtain ⟨j, hj⟩ := ih
        obtain ⟨k, hk⟩ := hStep n j
        exact ⟨k, hk.trans hj⟩
    have hPow : Filter.Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hDense (t : BridgeTime) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
        ∃ m : ℕ, ∃ i : Fin (2 ^ m), dist (grid m i) t < epsilon := by
      have ht : Filter.Tendsto (fun m : ℕ => 1 / ((2 ^ m : ℕ) : ℝ))
          Filter.atTop (nhds 0) := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat, one_div, inv_pow] using hPow
      obtain ⟨m, hm⟩ := (ht.eventually (gt_mem_nhds hepsilon)).exists
      let N : ℕ := 2 ^ m
      have hn : (0 : ℝ) < (N : ℝ) := by dsimp [N]; positivity
      let k : ℕ := max 1 (Nat.ceil ((N : ℝ) * (t : ℝ)))
      have hk1 : 1 ≤ k := le_max_left _ _
      have hkn : k ≤ N := by
        apply max_le (hN m)
        apply Nat.ceil_le.mpr
        simpa only [mul_one] using (mul_le_mul_of_nonneg_left t.property.2 hn.le)
      have ht0 : 0 ≤ (N : ℝ) * (t : ℝ) := mul_nonneg hn.le t.property.1
      have hbelow : (N : ℝ) * (t : ℝ) ≤ (k : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 (Nat.ceil ((N : ℝ) * (t : ℝ)))))
      have habove : (k : ℝ) ≤ (N : ℝ) * (t : ℝ) + 1 := by
        dsimp [k]
        rw [Nat.cast_max]
        refine max_le ?_ (Nat.ceil_lt_add_one ht0).le
        simpa only [Nat.cast_one] using
          (le_add_of_nonneg_left ht0 : (1 : ℝ) ≤ (N : ℝ) * (t : ℝ) + 1)
      have hdiff : |(k : ℝ) / (N : ℝ) - (t : ℝ)| ≤ 1 / (N : ℝ) := by
        have hlo : (t : ℝ) ≤ (k : ℝ) / (N : ℝ) :=
          (le_div_iff₀ hn).mpr (by simpa only [mul_comm] using hbelow)
        have hhi : (k : ℝ) / (N : ℝ) ≤ (t : ℝ) + 1 / (N : ℝ) := by
          apply (div_le_iff₀ hn).mpr
          have he : ((t : ℝ) + 1 / (N : ℝ)) * (N : ℝ) = (N : ℝ) * (t : ℝ) + 1 := by
            field_simp [ne_of_gt hn] <;> ring
          rwa [he]
        rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
        linarith
      let i : Fin (2 ^ m) := ⟨k - 1, by change k - 1 < N; omega⟩
      have hik : i.val + 1 = k := by dsimp [i]; omega
      refine ⟨m, i, ?_⟩
      change |((i.val + 1 : ℕ) : ℝ) / ((2 ^ m : ℕ) : ℝ) - (t : ℝ)| < epsilon
      rw [hik]
      exact hdiff.trans_lt hm
    have hBoundBelow (a : ℝ) (ha : 0 < a) (hax : a < x) :
        d ≤ 2 * Real.exp (-9 * a ^ 2 / 2) := by
      let F : ℕ → Set ΩB := fun m => {omega |
        (∃ i : Fin (2 ^ m), a ≤ B (T m (i.val + 1)) omega) ∧
          ∃ i : Fin (2 ^ m), B (T m (i.val + 1)) omega ≤ -a}
      have hFmono : Monotone F := by
        intro m n hmn omega homega
        obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := homega
        obtain ⟨i', hi'⟩ := hLift m n hmn i
        obtain ⟨j', hj'⟩ := hLift m n hmn j
        exact ⟨⟨i', by simpa only [hi'] using hi⟩,
          ⟨j', by simpa only [hj'] using hj⟩⟩
      have hFinite (m : ℕ) : PB.real (F m) ≤ 2 * Real.exp (-9 * a ^ 2 / 2) := by
        let N : ℕ := 2 ^ m
        let D : Fin N → ℝ≥0 := fun _ => (N : ℝ≥0)⁻¹
        let G : Set (Shao.Path N) := {v | (∃ i : Fin N, a ≤ v i) ∧
          ∃ i : Fin N, v i ≤ -a}
        have hGM : MeasurableSet G := by
          have hu : ∀ i : Fin N, MeasurableSet {v : Shao.Path N | a ≤ v i} :=
            fun i => measurableSet_le measurable_const (measurable_pi_apply i)
          have hl : ∀ i : Fin N, MeasurableSet {v : Shao.Path N | v i ≤ -a} :=
            fun i => measurableSet_le (measurable_pi_apply i) measurable_const
          change MeasurableSet ({v : Shao.Path N | ∃ i : Fin N, a ≤ v i} ∩
            {v : Shao.Path N | ∃ i : Fin N, v i ≤ -a})
          have hu' : MeasurableSet {v : Shao.Path N | ∃ i : Fin N, a ≤ v i} := by
            simpa only [Set.setOf_exists] using MeasurableSet.iUnion hu
          have hl' : MeasurableSet {v : Shao.Path N | ∃ i : Fin N, v i ≤ -a} := by
            simpa only [Set.setOf_exists] using MeasurableSet.iUnion hl
          exact hu'.inter hl' 
        have hPrefix (k : ℕ) (hk : k ≤ N) :
            Shao.OQ4.RowPolygonalFDD.durationPrefix D k = (k : ℝ≥0) * (N : ℝ≥0)⁻¹ := by
          induction k with
          | zero => simp [Shao.OQ4.RowPolygonalFDD.durationPrefix]
          | succ k ih =>
            let i : Fin N := ⟨k, by omega⟩
            have hs : Finset.univ.filter (fun j : Fin N => j.val < k + 1) =
                insert i (Finset.univ.filter (fun j : Fin N => j.val < k)) := by
              ext j
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
              constructor
              · intro hj
                by_cases he : j = i
                · exact Or.inl he
                · exact Or.inr (by have : j.val ≠ k := fun h => he (Fin.ext h); omega)
              · rintro (rfl | hj)
                · change k < k + 1
                  omega
                · omega
            change (∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val < k + 1), D j) = _
            rw [hs, Finset.sum_insert (by simp [i])]
            change D i + Shao.OQ4.RowPolygonalFDD.durationPrefix D k = _
            rw [ih (by omega)]
            dsimp [D]
            push_cast
            ring
        have hObs (i : Fin N) : Shao.OQ4.RowPolygonalFDD.observationTime D i =
            T m (i.val + 1) := by
          unfold Shao.OQ4.RowPolygonalFDD.observationTime
          rw [hPrefix (i.val + 1) (by omega)]
          exact (div_eq_mul_inv _ _).symm
        have hLaw := Shao.OQ4.PolygonalBrownianWeakLimit.brownian_vector_hasLaw_cumulativeGaussian
          B PB hB N D
        have hF : F m = (fun omega (i : Fin N) =>
            B (Shao.OQ4.RowPolygonalFDD.observationTime D i) omega) ⁻¹' G := by
          ext omega
          simp only [F, Set.mem_setOf_eq, Set.mem_preimage, G, hObs] <;> rfl
        have hEvent : (Shao.OQ4.RowPolygonalFDD.cumulativeMap N) ⁻¹' G =
            {w : Shao.Path N | a ≤ Shao.upperMax w (hN m) ∧
              a ≤ Shao.lowerMax w (hN m)} := by
          ext w
          change ((∃ i : Fin N, a ≤ Shao.prefixSum w (i.val + 1)) ∧
            (∃ i : Fin N, Shao.prefixSum w (i.val + 1) ≤ -a)) ↔ _
          constructor
          · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
            refine ⟨(Shao.upperMax_ge_iff w (hN m) a).mpr
              ⟨i.val + 1, by omega, by omega, hi⟩, ?_⟩
            apply (Shao.upperMax_ge_iff (-w) (hN m) a).mpr
            refine ⟨j.val + 1, by omega, by omega, ?_⟩
            rw [Shao.prefixSum_neg]
            linarith
          · rintro ⟨hu, hl⟩
            obtain ⟨k, hk1, hkn, hk⟩ := (Shao.upperMax_ge_iff w (hN m) a).mp hu
            obtain ⟨l, hl1, hln, hl⟩ := (Shao.upperMax_ge_iff (-w) (hN m) a).mp hl
            rw [Shao.prefixSum_neg] at hl
            refine ⟨⟨⟨k - 1, by omega⟩, ?_⟩, ⟨⟨l - 1, by omega⟩, ?_⟩⟩
            · simpa only [show k - 1 + 1 = k from by omega] using hk
            · simpa only [neg_neg, show l - 1 + 1 = l from by omega] using (neg_le_neg hl)
        have hMap : Measurable (Shao.OQ4.RowPolygonalFDD.cumulativeMap N) := by
          unfold Shao.OQ4.RowPolygonalFDD.cumulativeMap Shao.prefixSum
          fun_prop
        calc
          PB.real (F m) = (Shao.OQ4.RowPolygonalFDD.cumulativeGaussianLaw D).real G := by
            rw [hF]
            exact hLaw.measureReal_eq hGM
          _ = (Shao.OQ4.RowPolygonalFDD.gaussianIncrementLaw D).real
              {w : Shao.Path N | a ≤ Shao.upperMax w (hN m) ∧
                a ≤ Shao.lowerMax w (hN m)} := by
            unfold Shao.OQ4.RowPolygonalFDD.cumulativeGaussianLaw
            rw [Measure.real, Measure.map_apply hMap hGM, hEvent]
            rfl
          _ ≤ _ := gaussian_grid_two_wall_bound N (hN m) a ha
      have hSub : ∀ᵐ omega ∂PB, omega ∈ DB → omega ∈ ⋃ m, F m := by
        filter_upwards [Shao.OQ4.PolygonalBrownianWeakLimit.ae_brownianUnitPath_eq B 1 PB hB]
          with omega homega
        intro hdouble
        obtain ⟨⟨t, ht⟩, ⟨s, hs⟩⟩ := hdouble
        let f : C(BridgeTime, ℝ) := Shao.OQ4.PolygonalBrownianWeakLimit.brownianUnitPath B 1 omega
        have he (r : BridgeTime) : f r = B ⟨(r : ℝ), r.property.1⟩ omega := by
          have hh := homega r
          change f r = B (1 * ⟨(r : ℝ), r.property.1⟩) omega at hh
          exact hh.trans (congrArg (fun q : ℝ≥0 => B q omega) (_root_.one_mul _))
        have htu : a < f t := by rw [he]; linarith
        have hsl : f s < -a := by rw [he]; linarith
        have hOU : IsOpen {r : BridgeTime | a < f r} := isOpen_lt continuous_const f.continuous
        have hOL : IsOpen {r : BridgeTime | f r < -a} := isOpen_lt f.continuous continuous_const
        obtain ⟨eu, heu, hbu⟩ := Metric.isOpen_iff.mp hOU t htu
        obtain ⟨el, hel, hbl⟩ := Metric.isOpen_iff.mp hOL s hsl
        obtain ⟨mu, iu, hiu⟩ := hDense t eu heu
        obtain ⟨ml, il, hil⟩ := hDense s el hel
        have hu : a ≤ B (T mu (iu.val + 1)) omega := by
          have hh : a < f (grid mu iu) := hbu hiu
          rw [he, hGridTime] at hh
          exact hh.le
        have hl : B (T ml (il.val + 1)) omega ≤ -a := by
          have hh : f (grid ml il) < -a := hbl hil
          rw [he, hGridTime] at hh
          exact hh.le
        obtain ⟨ju, hju⟩ := hLift mu (max mu ml) (le_max_left _ _) iu
        obtain ⟨jl, hjl⟩ := hLift ml (max mu ml) (le_max_right _ _) il
        exact Set.mem_iUnion.mpr ⟨max mu ml,
          ⟨⟨ju, by simpa only [hju] using hu⟩, ⟨jl, by simpa only [hjl] using hl⟩⟩⟩
      have hUnionBound : PB.real (⋃ m, F m) ≤ 2 * Real.exp (-9 * a ^ 2 / 2) := by
        have hh := tendsto_measure_iUnion_atTop (μ := PB) hFmono
        have ht := (ENNReal.continuousAt_toReal (measure_ne_top PB (⋃ m, F m))).tendsto.comp hh
        exact le_of_tendsto ht (Filter.Eventually.of_forall hFinite)
      exact (ENNReal.toReal_mono (measure_ne_top PB (⋃ m, F m)) (measure_mono_ae hSub)).trans hUnionBound
    let a : ℕ → ℝ := fun j => x * (1 - (1 / 2 : ℝ) ^ (j + 1))
    have ha0 (j : ℕ) : 0 < a j := by
      dsimp [a]
      apply mul_pos hx
      exact sub_pos.mpr (pow_lt_one₀ (by norm_num) (by norm_num) (by omega))
    have hax (j : ℕ) : a j < x := by
      have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ (j + 1) := by positivity
      dsimp [a]
      nlinarith only [mul_pos hx hp]
    have ha : Filter.Tendsto a Filter.atTop (nhds x) := by
      have hp : Filter.Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1))
          Filter.atTop (nhds 0) := by
        simpa only [pow_succ, zero_mul] using hPow.mul_const (1 / 2 : ℝ)
      have hcx : Filter.Tendsto (fun _ : ℕ => x) Filter.atTop (nhds x) := tendsto_const_nhds
      have hc1 : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
      simpa only [a, sub_zero, mul_one] using hcx.mul (hc1.sub hp)
    have hc : Continuous (fun z : ℝ => 2 * Real.exp (-9 * z ^ 2 / 2)) := by fun_prop
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (hc.continuousAt.tendsto.comp ha)
      (Filter.Eventually.of_forall fun j => hBoundBelow (a j) (ha0 j) (hax j))
  )

theorem source_centered_bounded_nonresidual_brownian_comparison :
    ∀ cstar : ℝ, 0 < cstar →
      let K : ℝ := Real.sqrt (2 * Real.pi)
      let C : ℝ := 2 * K + 2 * Real.exp 1 + 2
      let Crel : ℝ := K * (2 + 4 * Real.exp 1 / cstar) + 4 * K / cstar
      0 < C ∧ 0 < Crel ∧
        ∀ {ΩB : Type*} [MeasurableSpace ΩB]
          (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
          IsBrownianReal B PB →
          ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu]
            (n : ℕ) (hn : 0 < n) (x : ℝ), 1 ≤ x →
            (∀ᵐ z : ℝ ∂nu, |z| ≤ 1 / (4 * x)) →
            (∫ z : ℝ, z ∂nu) = 0 →
            (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
            let beta : ℝ := (n : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂nu)
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
            let u : ℝ := beta * (1 + x) ^ 3
            let D : Set (Shao.Path n) := Shao.C2.doubleCrossing hn x
            let DB : Set ΩB :=
              {omega | (∃ t : BridgeTime, x ≤ B ⟨(t : ℝ), t.property.1⟩ omega) ∧
                ∃ t : BridgeTime, B ⟨(t : ℝ), t.property.1⟩ omega ≤ -x}
            let d : ℝ := PB.real DB
            Integrable (fun z : ℝ => z ^ 2) nu ∧
              Integrable (fun z : ℝ => |z| ^ 3) nu ∧
              0 < beta ∧ 16 * x ^ 2 ≤ (n : ℝ) ∧
              MeasurableSet D ∧ NullMeasurableSet DB PB ∧
              Shao.truncationBudget nu n x = u ∧
              (u ≤ 1 / 20000 →
                |P.real D - d| ≤ C * u * Shao.standardNormalTail x +
                  C * Real.exp (-4 * x ^ 2) ∧
                (cstar * Real.exp (-3 * x ^ 2) ≤ u →
                  |P.real D - d| ≤ Crel * u * Shao.standardNormalTail x)) := by
  classical
  intro cstar hcstar K C Crel
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨by dsimp [C]; positivity, by dsimp [Crel]; positivity, ?_⟩
  intro ΩB hΩB B PB hPB hB nu hnu n hn x hx hsupport hmean hnorm beta P u D DB d
  letI : IsProbabilityMeasure PB := hPB
  letI : IsProbabilityMeasure nu := hnu
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hx0 : 0 < x := by linarith
  have hpaid :=
    (SourceOriginalLargeThreshold.source_centered_bounded_nonresidual_double_crossing
      cstar hcstar).2 nu n hn x hx hsupport hmean hnorm
  rcases hpaid with ⟨h2, h3, hbeta, hsize, hDM, hBudget, hExp, hrelative⟩
  rcases actual_brownian_weak_double_crossing B PB hB x hx0 with
    ⟨hU, hL, hBM, hUnion, hIdentity, hd0, hdPsi, hdExp⟩
  change NullMeasurableSet DB PB at hBM
  change 0 ≤ d at hd0
  change d ≤ 2 * Real.exp (-9 * x ^ 2 / 2) at hdExp
  have hdPaid : d ≤ 2 * Real.exp (-4 * x ^ 2) := hdExp.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x])) (by norm_num))
  have hp0 : 0 ≤ P.real D := measureReal_nonneg
  have hErr : |P.real D - d| ≤ P.real D + d := by
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  refine ⟨h2, h3, hbeta, hsize, hDM, hBM, hBudget, ?_⟩
  intro husmall
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
  change Real.exp (-x ^ 2) ≤ 2 * K * Shao.standardNormalTail x at hGauss
  have htail : 0 < Shao.standardNormalTail x := (Shao.standardNormalTail_basic.2.2.1 x).1
  have hPpaid : P.real D ≤
      (2 * K) * u * Shao.standardNormalTail x + 2 * Real.exp 1 * Real.exp (-4 * x ^ 2) := by
    calc
      _ ≤ u * Real.exp (-x ^ 2) + 2 * Real.exp 1 * Real.exp (-4 * x ^ 2) :=
        hExp.trans (add_le_add hLowPaid hHighPaid)
      _ ≤ u * (2 * K * Shao.standardNormalTail x) +
          2 * Real.exp 1 * Real.exp (-4 * x ^ 2) := by gcongr
      _ = _ := by ring
  constructor
  · calc
      |P.real D - d| ≤ P.real D + d := hErr
      _ ≤ (2 * K) * u * Shao.standardNormalTail x +
          (2 * Real.exp 1 + 2) * Real.exp (-4 * x ^ 2) := by
        nlinarith only [hPpaid, hdPaid]
      _ ≤ C * u * Shao.standardNormalTail x + C * Real.exp (-4 * x ^ 2) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_right _ htail.le
          apply mul_le_mul_of_nonneg_right _ hu.le
          dsimp [C]
          linarith [Real.exp_pos (1 : ℝ)]
        · apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          dsimp [C]
          linarith
  · intro hunonres
    have hRare : Real.exp (-4 * x ^ 2) ≤ (u / cstar) * Real.exp (-x ^ 2) := by
      have hh := mul_le_mul_of_nonneg_right hunonres (Real.exp_pos (-x ^ 2)).le
      have hid : Real.exp (-3 * x ^ 2) * Real.exp (-x ^ 2) = Real.exp (-4 * x ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [mul_assoc, hid] at hh
      have hdiv := (le_div_iff₀ hcstar).mpr (by simpa only [mul_comm] using hh)
      convert hdiv using 1 <;> ring
    have hDPaid : d ≤ (4 * K / cstar) * u * Shao.standardNormalTail x := by
      calc
        _ ≤ 2 * Real.exp (-4 * x ^ 2) := hdPaid
        _ ≤ 2 * ((u / cstar) * Real.exp (-x ^ 2)) := by gcongr
        _ ≤ 2 * ((u / cstar) * (2 * K * Shao.standardNormalTail x)) := by gcongr
        _ = _ := by ring
    have hR := hrelative husmall hunonres
    calc
      |P.real D - d| ≤ P.real D + d := hErr
      _ ≤ (K * (2 + 4 * Real.exp 1 / cstar)) * u * Shao.standardNormalTail x +
          (4 * K / cstar) * u * Shao.standardNormalTail x := add_le_add hR hDPaid
      _ = Crel * u * Shao.standardNormalTail x := by dsimp [Crel]; ring

end Shao.Probability.SourceNonresidualBrownian
