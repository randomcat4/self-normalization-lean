/- Mathematical candidate only. Actual interval probability consumers.
   Physical regularity, halfline reflection, and small Taylor remain explicit upstream inputs. -/
import Shao.Probability.SourceActualLocalProfileBudget
import Shao.C2.IntervalGaussianLocal
import Shao.C2.InteriorDerivativeMeasurability
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.Probability.SourceActualIntervalProfileBudget
open MeasureTheory ProbabilityTheory
open SourcePermutationReveal SourceSeparatedOvershoot SourceActualLocalProfileBudget
open Shao.C2.BridgeDomination
open scoped BigOperators Classical

local instance labelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

def intervalDerivative (Q : Measure BridgeNoise) : BridgeKernel := fun p =>
  if 0 < p.1 ∧ 0 < p.2.2.1 ∧ |p.2.1| < p.1 ∧ |p.2.2.2| < p.1 then
    deriv (fun y : ℝ => eventCompletionKernel .interval Q
      (p.1, y, p.2.2.1, p.2.2.2)) p.2.1
  else 0

theorem actual_interval_kernel_data
    (Q : Measure BridgeNoise) [IsProbabilityMeasure Q]
    (hReflection : HalflineReflectionIdentities Q)
    (hRegular : ∀ w y T z : ℝ, 0 < w → 0 < T → |y| < w → |z| < w →
      DifferentiableAt ℝ
        (fun s : ℝ => Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w s T z) y) :
    Measurable (intervalDerivative Q) ∧
    KernelBounds .interval (eventCompletionKernel .interval Q) (intervalDerivative Q) 4 ∧
    (∀ w y T z : ℝ, 0 < w → 0 < T → |y| < w → |z| < w →
      HasDerivAt (fun s : ℝ => eventCompletionKernel .interval Q (w, s, T, z))
        (intervalDerivative Q (w, y, T, z)) y) := by
  classical
  have hr (w y T z : ℝ) (hw : 0 < w) (hT : 0 < T) (hy : |y| < w) (hz : |z| < w) :
      DifferentiableAt ℝ (fun s : ℝ => intervalCompletion Q w s T z) y := by
    have he : (fun s : ℝ => Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w s T z) =
        (fun s : ℝ => intervalCompletion Q w s T z) := by
      funext s
      exact Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion_pos Q w s T z hT
    have hh := hRegular w y T z hw hT hy hz
    rwa [he] at hh
  have hm := Shao.C2.InteriorDerivativeMeasurability.measurable_interiorSpatialDerivative Q
    (fun w y T z hw hT hy hz => (hr w y T z hw hT hy hz).hasDerivAt)
  have he : intervalDerivative Q =
      (fun p : Shao.C2.CompletionMeasurability.CompletionParameters =>
        Shao.C2.InteriorDerivativeMeasurability.interiorSpatialDerivative Q
          p.1 p.2.1 p.2.2.1 p.2.2.2) := by
    funext p
    by_cases hg : 0 < p.2.2.1 ∧ |p.2.1| < p.1 ∧ |p.2.2.2| < p.1
    · have hw : 0 < p.1 := (abs_nonneg _).trans_lt hg.2.1
      simp only [intervalDerivative, Shao.C2.InteriorDerivativeMeasurability.interiorSpatialDerivative,
        Shao.C2.CompletedIntervalDerivative.spatialDerivative, eventCompletionKernel,
        if_pos hg, if_pos (show 0 < p.1 ∧ 0 < p.2.2.1 ∧ |p.2.1| < p.1 ∧ |p.2.2.2| < p.1 from ⟨hw, hg⟩)]
    · have hfull : ¬ (0 < p.1 ∧ 0 < p.2.2.1 ∧ |p.2.1| < p.1 ∧ |p.2.2.2| < p.1) :=
        fun h => hg h.2
      simp only [intervalDerivative, Shao.C2.InteriorDerivativeMeasurability.interiorSpatialDerivative,
        if_neg hg, if_neg hfull]
  refine ⟨by rw [he]; exact hm, ⟨by norm_num, ?_, ?_⟩, ?_⟩
  · intro w y T z _ _ _ _
    exact (eventCompletionKernel_data .interval Q).2.1 (w,y,T,z)
  · intro w y T z hw hT hy hz
    have hya : |y| < w := abs_lt.mpr hy
    have hza : |z| < w := abs_lt.mpr hz
    have hb := Shao.C2.IntervalDerivativeBound.interval_deriv_bound_of_reflection Q w y T z hT hya hza
      (fun s hs => hReflection.1 w s T z hw hT hs hz.2)
      (fun s hs => hReflection.2 w s T z hw hT hs hz.1)
      (hr w y T z hw hT hya hza)
    simpa only [intervalDerivative, eventCompletionKernel, if_pos (show 0 < w ∧ 0 < T ∧ |y| < w ∧ |z| < w from ⟨hw, hT, hya, hza⟩)] using hb
  · intro w y T z hw hT hy hz
    simpa only [intervalDerivative, eventCompletionKernel, if_pos (show 0 < w ∧ 0 < T ∧ |y| < w ∧ |z| < w from ⟨hw, hT, hy, hz⟩)] using
      (hr w y T z hw hT hy hz).hasDerivAt


theorem iid_actual_interval_retained_negative_budget :
    ∀ Csmall : ℝ, 0 ≤ Csmall → ∃ C : ℝ, 0 < C ∧
      ∀ (Q : Measure BridgeNoise) [IsProbabilityMeasure Q],
        HalflineReflectionIdentities Q →
        (∀ w y T z : ℝ, 0 < w → 0 < T → |y| < w → |z| < w →
          DifferentiableAt ℝ
            (fun s : ℝ => Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w s T z) y) →
        (∀ w y T z beta : ℝ, 0 < w → 0 < T → |y| < w → |z| < w →
          beta ^ 2 ≤ T / 2 → |y + beta| ≤ w →
          |Shao.C2.ActualIntervalProjection.sourceRemainder Q w y T z beta| ≤
            Csmall * |beta| ^ 3 * (1 / Real.sqrt T) ^ 3 *
              (1 + |z - y| / Real.sqrt T) ^ 3 *
                Shao.C2.IntervalGaussianLocal.intervalIncrementProfile w y T z beta) →
        ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho] (n : ℕ) (hn : 0 < n),
          Integrable (fun z : ℝ => z ^ 2) rho →
          (∫ z : ℝ, z ∂rho) = 0 → 0 < (∫ z : ℝ, z ^ 2 ∂rho) →
          let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
          let scale : ℝ := Real.sqrt ((n : ℝ) * sigmaSq)
          let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / scale) rho
          let R : ℝ := Shao.truncationBudget normalizedLaw n 0
          let h : ℝ := 4 * (n : ℝ) * sigmaSq * R ^ 2
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
          let nu : Shao.Path n → LabelPerm n → ℕ := fun a sigma => energyCutoff a h sigma
          ∀ (x : ℝ), 0 ≤ x → x ≤ 1 →
            let L : (Shao.Path n × LabelPerm n) → ℕ → ℝ := fun p r =>
              sourceRetainedRemainder .interval (eventCompletionKernel .interval Q)
                (intervalDerivative Q) p.1 x (nu p.1) r p.2
            let O : (Shao.Path n × LabelPerm n) → ℕ → ℝ := fun p r =>
              sourceSeparatedOvershoot .interval (intervalDerivative Q)
                p.1 x (nu p.1) r p.2
            (∀ sigma : LabelPerm n, Measurable (fun a : Shao.Path n => nu a sigma)) ∧
            (∀ r : ℕ, Measurable (fun p => L p r) ∧ Measurable (fun p => O p r)) ∧
            (∀ r : ℕ, Integrable (fun p => L p r) (revealLaw P) ∧
              Integrable (fun p => O p r) (revealLaw P)) ∧
            Integrable (fun p => ∑ r ∈ Finset.range n, (|L p r| + max (-O p r) 0))
              (revealLaw P) ∧
            (∫ p, ∑ r ∈ Finset.range n, (|L p r| + max (-O p r) 0) ∂revealLaw P) ≤ C * R := by
  classical
  intro Csmall hCs
  obtain ⟨CG, hCG, hGaussian⟩ := SourceIIDGaussianProfileBudget.iid_gaussian_profile_early_late_budget
  let K : ℝ := 2 * Csmall + 40
  have hKpos : 0 < K := by dsimp [K]; positivity
  refine ⟨K * CG, mul_pos hKpos hCG, ?_⟩
  intro Q hQ hReflection hRegular hSmall rho hrho n hn h2 hmean hsecond
    sigmaSq scale normalizedLaw R h P nu x hx0 hx1 L O
  letI : IsProbabilityMeasure Q := hQ
  letI : IsProbabilityMeasure rho := hrho
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hGeom := Shao.Probability.raw_truncation_budget_suffix_geometry rho n hn h2 hsecond
  have hR : 0 < R := hGeom.1
  have hh : 0 < h := hGeom.2.2.2.1
  have hnum (sigma : LabelPerm n) : Measurable (fun a : Shao.Path n => nu a sigma) :=
    actual_energy_cutoff_measurable h hh sigma
  refine ⟨hnum, ?_⟩
  by_cases hx : x = 0
  · have hdead (a : Shao.Path n) (r : ℕ) (sigma : LabelPerm n) :
        ¬ sourceAlive .interval a x r sigma := by
      intro ha
      have hz := ha.2.2 0 (Nat.zero_le r)
      simpa [Interior, actualWall, hx, Shao.prefixSum_zero] using hz
    have hL (p : Shao.Path n × LabelPerm n) (r : ℕ) : L p r = 0 := by
      dsimp [L]
      unfold sourceRetainedRemainder
      split_ifs <;> simp_all only [and_false, false_and, if_false]
    have hO (p : Shao.Path n × LabelPerm n) (r : ℕ) : O p r = 0 := by
      dsimp [O]
      unfold sourceSeparatedOvershoot
      split_ifs <;> simp_all only [and_false, false_and, if_false]
    simp only [hL, hO, abs_zero, neg_zero, max_self, add_zero, Finset.sum_const_zero,
      integral_zero]
    exact ⟨fun _ => ⟨measurable_const, measurable_const⟩,
      fun _ => ⟨integrable_zero _ _ _, integrable_zero _ _ _⟩, integrable_zero _ _ _, by positivity⟩
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
  have hKernel := actual_interval_kernel_data Q hReflection hRegular
  have hParts := source_parts_measurable_integrable .interval
    (eventCompletionKernel .interval Q) (intervalDerivative Q)
    (eventCompletionKernel_data .interval Q).1 hKernel.1 4 hKernel.2.1 P x hxpos nu hnum
  have hJoint (r : ℕ) : Measurable (fun p => L p r) ∧ Measurable (fun p => O p r) := by
    constructor
    · apply measurable_from_prod_countable_left
      intro sigma
      exact (hParts.1 sigma r).1
    · apply measurable_from_prod_countable_left
      intro sigma
      exact (hParts.1 sigma r).2
  have hInt (r : ℕ) : Integrable (fun p => L p r) (revealLaw P) ∧
      Integrable (fun p => O p r) (revealLaw P) := hParts.2.1 r
  have hSi : Integrable (fun p => ∑ r ∈ Finset.range n,
      (|L p r| + max (-O p r) 0)) (revealLaw P) := by
    apply integrable_finsetSum
    intro r _
    have hi := ((hInt r).2.abs.sub (hInt r).2).div_const 2
    have he : (fun p => (|O p r| - O p r) / 2) = (fun p => max (-O p r) 0) := by
      funext p
      by_cases ho : 0 ≤ O p r
      · rw [abs_of_nonneg ho, max_eq_right (neg_nonpos.mpr ho)]
        ring
      · have hn : O p r ≤ 0 := le_of_not_ge ho
        rw [abs_of_nonpos hn, max_eq_left (neg_nonneg.mpr hn)]
        ring
    change Integrable (fun p => (|O p r| - O p r) / 2) (revealLaw P) at hi
    rw [he] at hi
    exact (hInt r).1.abs.add hi
  have hsigns : ∀ s ∈ wallSigns .interval, s = 1 ∨ s = -1 := by
    simp only [wallSigns, Finset.mem_insert, Finset.mem_singleton]
    exact fun s hs => hs
  have hGbudget := hGaussian rho n hn h2 hmean hsecond x hxpos hx1
    (wallSigns .interval) hsigns false
  let G : Shao.Path n → ℝ := fun a => ∑ r : Fin n,
    SourceIIDGaussianProfileBudget.rankGaussianWeight h x (wallSigns .interval) false a r
  have hGi : Integrable G P := hGbudget.2.2.2.1
  have hGle : (∫ a, G a ∂P) ≤ CG * R := hGbudget.2.2.2.2.2.2
  have hRankMeas (r : Fin n) : Measurable (fun a : Shao.Path n =>
      SourceIIDGaussianProfileBudget.rankGaussianWeight h x (wallSigns .interval) false a r) := by
    have hs : Measurable (fun a : Shao.Path n =>
        (Spitzer.head a r.val r.is_lt.le, Spitzer.tail a r.val r.is_lt.le)) :=
      (Measurable.of_eval fun i => measurable_pi_apply _).prodMk
        (Measurable.of_eval fun i => measurable_pi_apply _)
    exact (SourceIIDGaussianProfileBudget.fixed_gaussian_weight_measurable_bound
      r.val (n-r.val) h x (wallSigns .interval) false).1.comp hs
  have hGm : Measurable G := Finset.measurable_sum _ (fun r _ => hRankMeas r)
  let X : Fin n → Shao.Path n → ℝ := fun i a => a i
  have hX (i : Fin n) : Measurable (X i) := measurable_pi_apply i
  have hLaw (i : Fin n) : IdentDistrib (X i) (id : ℝ → ℝ) P rho := by
    refine ⟨(hX i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [Measure.map_id] using
      (measurePreserving_eval (μ := fun _ : Fin n => rho) i).map_eq
  have hIndep : iIndepFun X P :=
    iIndepFun_pi (X := fun _ : Fin n => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)
  have hMap : Measure.map (fun p : Shao.Path n × LabelPerm n =>
      Spitzer.reorder p.1 p.2) (revealLaw P) = P :=
    iid_randomPermutation_map_eq_pi P rho X hX hIndep hLaw
  have hRm : Measurable (fun p : Shao.Path n × LabelPerm n =>
      Spitzer.reorder p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro sigma
    exact Measurable.of_eval (fun i => measurable_pi_apply (sigma i))
  have hPath : IdentDistrib (fun p : Shao.Path n × LabelPerm n =>
      Spitzer.reorder p.1 p.2) (id : Shao.Path n → Shao.Path n) (revealLaw P) P :=
    ⟨hRm.aemeasurable, measurable_id.aemeasurable, by simpa only [Measure.map_id] using hMap⟩
  have hGid := hPath.comp hGm
  have hReorderedGi : Integrable (fun p : Shao.Path n × LabelPerm n =>
      G (Spitzer.reorder p.1 p.2)) (revealLaw P) := hGid.integrable_iff.mpr hGi
  have hDomRank (a : Shao.Path n) (sigma : LabelPerm n) (r : Fin n) :
      |L (a,sigma) r.val| + max (-O (a,sigma) r.val) 0 ≤ K *
        SourceIIDGaussianProfileBudget.rankGaussianWeight h x (wallSigns .interval) false
          (Spitzer.reorder a sigma) r := by
    let w : ℝ := actualWall a x
    let y : ℝ := Shao.prefixSum (Spitzer.reorder a sigma) r.val
    let T : ℝ := remainingEnergy a r.val sigma
    let z : ℝ := Shao.prefixSum a n
    let b : ℝ := a (sigma r)
    have hNN : 0 ≤ SourceIIDGaussianProfileBudget.rankGaussianWeight h x (wallSigns .interval) false
        (Spitzer.reorder a sigma) r :=
      ((SourceIIDGaussianProfileBudget.fixed_gaussian_weight_measurable_bound
        r.val (n-r.val) h x (wallSigns .interval) false).2.1 _ _).1
    by_cases hact : r.val < nu a sigma ∧ sourceAlive .interval a x r.val sigma ∧ 0 < T
    · have hw : 0 < w := mul_pos hxpos (Real.sqrt_pos.2 hact.2.1.1)
      have hy : |y| < w := abs_lt.mpr (hact.2.1.2.2 r.val le_rfl)
      have hz : |z| < w := abs_lt.mpr hact.2.1.2.1
      have hT : 0 < T := hact.2.2
      have hcut : h ≤ T := ((energy_cutoff_data a h hh).2.2 sigma r.val hact.1).2
      have hb : b ^ 2 ≤ T := (remaining_population_geometry a r.val r.is_lt.le sigma).2.2.1 r le_rfl
      have hzero : T - b ^ 2 = 0 → y + b = z := actual_reveal_zero_future_reachable a r sigma
      have hExt (Y S : ℝ) : completionExt .interval (eventCompletionKernel .interval Q) w Y S z =
          Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w Y S z := by
        by_cases hY : |Y| < w
        · have hYi := abs_lt.mp hY
          have hzi := abs_lt.mp hz
          simp [completionExt, Interior, hw, hYi.1, hYi.2, hzi.1, hzi.2,
            Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion, eventCompletionKernel, hY]
        · rw [Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion_exterior Q w Y S z (by tauto)]
          have hYi : ¬(-w < Y ∧ Y < w) := fun hh => hY (abs_lt.mpr hh)
          simp only [completionExt, Interior, hYi, false_and, and_false, if_false]
      have hDer : deriv (fun Y : ℝ =>
          Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w Y T z) y =
          intervalDerivative Q (w,y,T,z) := by
        have hf : (fun Y : ℝ => Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion Q w Y T z) =
            (fun Y : ℝ => eventCompletionKernel .interval Q (w,Y,T,z)) := by
          funext Y
          exact Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion_pos Q w Y T z hT
        rw [hf]
        exact (hKernel.2.2 w y T z hw hT hy hz).deriv
      have hRem (beta : ℝ) :
          localRemainder .interval (eventCompletionKernel .interval Q) (intervalDerivative Q) w y T z beta =
            Shao.C2.ActualIntervalProjection.sourceRemainder Q w y T z beta := by
        unfold localRemainder Shao.C2.ActualIntervalProjection.sourceRemainder
        rw [hExt, hDer]
        simp only [Shao.C2.SourceIntervalCompletion.sourceIntervalCompletion, if_pos hT,
          eventCompletionKernel, compensationCoefficient]
      have hRet : localRetainedRemainder .interval (eventCompletionKernel .interval Q)
          (intervalDerivative Q) w y T z b = Shao.C2.IntervalGaussianLocal.retainedRemainder Q w y T z b := by
        by_cases hs : b^2 ≤ T/2 <;> by_cases hu : w ≤ y+b <;> by_cases hl : y+b ≤ -w
        all_goals
          have hh : ¬ |y+b| < w ↔ w ≤ y+b ∨ y+b ≤ -w := by
            constructor
            · intro hh
              by_contra hc
              push_neg at hc
              exact hh (abs_lt.mpr ⟨by linarith only [hc.2], hc.1⟩)
            · rintro (hu | hl) hh
              · exact not_lt_of_ge hu (abs_lt.mp hh).2
              · exact not_lt_of_ge hl (abs_lt.mp hh).1
          simp only [localRetainedRemainder, projectionIncrement, Shao.C2.IntervalGaussianLocal.retainedRemainder,
            hT, hs, hu, hl, hh, hRem, true_and, and_true, and_false, false_and,
            true_or, or_true, false_or, or_false, if_true, if_false]
      have hNeg : max (-localSeparatedOvershoot .interval (intervalDerivative Q) w y T z b) 0 =
          Shao.C2.IntervalGaussianLocal.negativeOvershoot Q w y T z b := by
        have huEq : -(b-(w-y))*(1-(b+(w-y))*(z-y)/T)*intervalDerivative Q (w,y,T,z) =
            Shao.C2.ActualIntervalProjection.upperOvershoot Q w y T z b := by
          simp only [Shao.C2.ActualIntervalProjection.upperOvershoot,
            Shao.C2.ProjectionOvershoot.projectionOvershoot, Shao.C2.ProjectionOvershoot.projectionFactor, hDer]
        have hlEq : -(b-(-w-y))*(1-(b+(-w-y))*(z-y)/T)*intervalDerivative Q (w,y,T,z) =
            Shao.C2.ActualIntervalProjection.lowerOvershoot Q w y T z b := by
          simp only [Shao.C2.ActualIntervalProjection.lowerOvershoot,
            Shao.C2.ProjectionOvershoot.projectionOvershoot, Shao.C2.ProjectionOvershoot.projectionFactor, hDer]
          ring
        by_cases hs : b^2 ≤ T/2 <;> by_cases hu : w ≤ y+b <;> by_cases hl : y+b ≤ -w
        all_goals
          have hh : ¬ |y+b| < w ↔ w ≤ y+b ∨ y+b ≤ -w := by
            constructor
            · intro hh
              by_contra hc
              push_neg at hc
              exact hh (abs_lt.mpr ⟨by linarith only [hc.2], hc.1⟩)
            · rintro (hu | hl) hh
              · exact not_lt_of_ge hu (abs_lt.mp hh).2
              · exact not_lt_of_ge hl (abs_lt.mp hh).1
          simp only [localSeparatedOvershoot, projectionIncrement, Shao.C2.IntervalGaussianLocal.negativeOvershoot,
            hT, hs, hu, hl, hh, true_and, and_true, and_false, false_and,
            true_or, or_true, false_or, or_false, if_true, if_false, huEq, hlEq,
            sub_self, neg_zero, zero_mul, max_self]
      have hbound := Shao.C2.IntervalGaussianLocal.actual_interval_local_gaussian_bound Q w y T z b Csmall
        hw hy hz hT hb hCs hzero (hRegular w y T z hw hT hy hz)
        (fun S hS Y hY => hReflection.1 w Y S z hw hS hY (abs_lt.mp hz).2)
        (fun S hS Y hY => hReflection.2 w Y S z hw hS hY (abs_lt.mp hz).1)
        (fun beta hs hn => hSmall w y T z beta hw hT hy hz hs hn)
      have hqperm : Shao.energy (Spitzer.reorder a sigma) = Shao.energy a := by
        simpa only [Shao.energy, Spitzer.reorder] using Equiv.sum_comp sigma (fun i => (a i)^2)
      have hsperm : Shao.prefixSum (Spitzer.reorder a sigma) n = Shao.prefixSum a n := by
        simpa only [Shao.prefixSum_length, Spitzer.reorder] using Equiv.sum_comp sigma a
      have hA : ∀ s ∈ wallSigns .interval,
          Shao.maxWithZero (s • Spitzer.head (Spitzer.reorder a sigma) r.val r.is_lt.le) < w := by
        intro s hs
        rcases hsigns s hs with rfl | rfl
        all_goals
          unfold Shao.maxWithZero
          rw [Finset.sup'_lt_iff]
          intro k hk
          rw [Shao.prefixSum_smul, Spitzer.head_prefixSum _ _ _ k (Finset.mem_Icc.1 hk).2]
          have hkLive := hact.2.1.2.2 k (Finset.mem_Icc.1 hk).2
        · simpa only [one_mul] using hkLive.2
        · simp only [neg_one_mul]
          linarith only [hkLive.1]
      have hRank : SourceIIDGaussianProfileBudget.rankGaussianWeight h x (wallSigns .interval) false
          (Spitzer.reorder a sigma) r =
          (|b|/Real.sqrt T)^3 * (1+|z-y|/Real.sqrt T)^3 *
            Shao.C2.IntervalGaussianLargeStep.intervalEnvelope w y T z b := by
        have he := (SourceIIDGaussianProfileBudget.gaussian_weight_source_state
          (Spitzer.reorder a sigma) r h x (wallSigns .interval) false).2.2.2.2
        rw [hqperm, hsperm] at he
        have hsel : 0 < Shao.energy a - Shao.prefixSquares (Spitzer.reorder a sigma) r.val ∧
            h ≤ Shao.energy a - Shao.prefixSquares (Spitzer.reorder a sigma) r.val ∧
            (∀ s ∈ wallSigns .interval,
              if false = true then Shao.maxWithZero
                (s • Spitzer.head (Spitzer.reorder a sigma) r.val r.is_lt.le) ≤ x*Real.sqrt (Shao.energy a)
              else Shao.maxWithZero
                (s • Spitzer.head (Spitzer.reorder a sigma) r.val r.is_lt.le) < x*Real.sqrt (Shao.energy a)) :=
          ⟨hT,hcut,by simpa only [Bool.false_eq_true, ite_false, w, actualWall] using hA⟩
        rw [if_pos hsel, if_pos (show 0 < Shao.energy a -
          Shao.prefixSquares (Spitzer.reorder a sigma) r.val from hT)] at he
        convert he using 1
        simp only [wallSigns, Finset.sum_insert (by norm_num : (1:ℝ) ∉ ({-1}:Finset ℝ)),
          Finset.sum_singleton, one_mul, neg_one_mul, sub_neg_eq_add,
          Shao.C2.IntervalGaussianLargeStep.intervalEnvelope, Shao.C2.GaussianWallEnvelope.wallEnvelope]
        dsimp only [w, y, z, b, T, actualWall, remainingEnergy, Spitzer.reorder]
        congr 2 <;> ring
      dsimp only [L, O]
      simp only [sourceRetainedRemainder, sourceSeparatedOvershoot, dif_pos r.is_lt,
        if_pos (show r.val < nu a sigma ∧ sourceAlive .interval a x r.val sigma ∧
          0 < remainingEnergy a r.val sigma from hact)]
      change |localRetainedRemainder .interval (eventCompletionKernel .interval Q) (intervalDerivative Q) w y T z b| +
        max (-localSeparatedOvershoot .interval (intervalDerivative Q) w y T z b) 0 ≤ _
      rw [hRet, hNeg, hRank]
      simpa only [K, mul_assoc] using hbound
    · dsimp only [L, O]
      have hinactive : ¬ (r.val < nu a sigma ∧ sourceAlive .interval a x r.val sigma ∧
          0 < remainingEnergy a r.val sigma) := hact
      simp only [sourceRetainedRemainder, sourceSeparatedOvershoot, dif_pos r.is_lt,
        if_neg hinactive, abs_zero, neg_zero, max_self, add_zero]
      exact mul_nonneg hKpos.le hNN
  have hDom (p : Shao.Path n × LabelPerm n) :
      (∑ r ∈ Finset.range n, (|L p r| + max (-O p r) 0)) ≤ K * G (Spitzer.reorder p.1 p.2) := by
    rw [← Fin.sum_univ_eq_sum_range (fun r : ℕ => |L p r| + max (-O p r) 0) n]
    calc
      _ ≤ ∑ r : Fin n, K * SourceIIDGaussianProfileBudget.rankGaussianWeight
          h x (wallSigns .interval) false (Spitzer.reorder p.1 p.2) r :=
        Finset.sum_le_sum (fun r _ => hDomRank p.1 p.2 r)
      _ = _ := by simp only [G, Finset.mul_sum]
  refine ⟨hJoint, hInt, hSi, ?_⟩
  calc
    _ ≤ ∫ p, K * G (Spitzer.reorder p.1 p.2) ∂revealLaw P :=
      integral_mono hSi (hReorderedGi.const_mul K) hDom
    _ = K * ∫ a, G a ∂P := by
      rw [integral_const_mul]
      exact congrArg (fun v : ℝ => K * v) hGid.integral_eq
    _ ≤ K * (CG * R) := mul_le_mul_of_nonneg_left hGle hKpos.le
    _ = _ := by ring


end Shao.Probability.SourceActualIntervalProfileBudget
