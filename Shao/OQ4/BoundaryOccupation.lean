import Shao.OQ4.KilledPathLaw
import Shao.OQ4.OccupationPayment
import Mathlib.Data.Fin.Rev
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! Conditional boundary occupation using unconditioned blocks and fixed reversal. -/

namespace Shao.OQ4

open MeasureTheory ProbabilityTheory
open scoped Classical

def reverseBlock {r : ℕ} (b : Shao.Path r) : Shao.Path r := fun i => b i.rev

def lowerBlockSurvival {r : ℕ} (d : ℝ) : Set (Shao.Path r) :=
  {b | -b ∈ Shao.closedUpper d}

theorem measurable_reverseBlock (r : ℕ) : Measurable (reverseBlock : Shao.Path r → Shao.Path r) :=
  Measurable.of_eval fun i => measurable_pi_apply i.rev

theorem measurableSet_closedUpper (r : ℕ) (d : ℝ) :
    MeasurableSet (Shao.closedUpper d : Set (Shao.Path r)) := by
  simp only [Shao.closedUpper, Set.ofPred_forall]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    measurableSet_le (Shao.measurable_prefixSum k) measurable_const

theorem measurableSet_lowerBlockSurvival (r : ℕ) (d : ℝ) :
    MeasurableSet (lowerBlockSurvival d : Set (Shao.Path r)) :=
  (measurableSet_closedUpper r d).preimage (by fun_prop)

theorem prefixSum_append (l r : ℕ) (a : Shao.Path l) (b : Shao.Path r) (k : ℕ) :
    Shao.prefixSum (Fin.append a b) (l + k) = Shao.prefixSum a l + Shao.prefixSum b k := by
  rw [Shao.prefixSum, Finset.sum_filter, Fin.sum_univ_add]
  have hf (i : Fin l) : i.val < l + k := by omega
  simp [hf, Shao.prefixSum, Finset.sum_filter]

theorem prefixSum_reverseBlock (r k : ℕ) (hk : k ≤ r) (b : Shao.Path r) :
    Shao.prefixSum (reverseBlock b) k = Shao.prefixSum b r - Shao.prefixSum b (r - k) := by
  have hc (i : Fin r) : i.rev.val < k ↔ ¬i.val < r - k := by
    change r - (i.val + 1) < k ↔ ¬i.val < r - k
    omega
  have he := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin r))
    (fun i => if i.rev.val < k then b i else 0)
  have hs : (∑ i : Fin r, if i.val < k then b i.rev else 0) =
      ∑ i : Fin r, if ¬i.val < r - k then b i else 0 := by
    simpa only [Fin.revPerm_apply, Fin.rev_rev, hc] using he
  have hadd : Shao.prefixSum (reverseBlock b) k + Shao.prefixSum b (r - k) = Shao.prefixSum b r := by
    simp only [Shao.prefixSum, Finset.sum_filter, reverseBlock]
    rw [hs, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hi : i.val < r := i.is_lt
    split_ifs <;> simp_all
  linarith

variable (ν : Measure ℝ) [IsProbabilityMeasure ν]

theorem measurePreserving_reverseBlock (r : ℕ) :
    MeasurePreserving (reverseBlock : Shao.Path r → Shao.Path r)
      (Measure.pi (fun _ : Fin r => ν)) (Measure.pi (fun _ : Fin r => ν)) := by
  have hp := measurePreserving_piCongrLeft (fun _ : Fin r => ν) (Fin.revPerm : Equiv.Perm (Fin r))
  convert hp using 1
  funext b i
  simp [reverseBlock, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast,
    Fin.revPerm_symm]

theorem measurePreserving_append (l r : ℕ) :
    MeasurePreserving (fun p : Shao.Path l × Shao.Path r => Fin.append p.1 p.2)
      ((Measure.pi (fun _ : Fin l => ν)).prod (Measure.pi (fun _ : Fin r => ν)))
      (Measure.pi (fun _ : Fin (l + r) => ν)) := by
  have hp := (measurePreserving_piCongrLeft (fun _ : Fin (l + r) => ν)
    (finSumFinEquiv : Fin l ⊕ Fin r ≃ Fin (l + r))).comp
      (measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin l ⊕ Fin r => ν))
  convert hp using 1
  funext p i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [MeasurableEquiv.coe_piCongrLeft, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
      Equiv.piCongrLeft_apply, Equiv.sumPiEquivProdPi]

def movingIntervalEvent {l r : ℕ} (T : Set (Shao.Path r)) (x : Shao.Path r → ℝ) :
    Set (Shao.Path l × Shao.Path r) :=
  {p | p.2 ∈ T ∧ x p.2 ≤ Shao.prefixSum p.1 l ∧ Shao.prefixSum p.1 l ≤ x p.2 + 1}

theorem measurableSet_movingIntervalEvent (l r : ℕ) (T : Set (Shao.Path r))
    (hT : MeasurableSet T) (x : Shao.Path r → ℝ) (hx : Measurable x) :
    MeasurableSet (movingIntervalEvent (l := l) T x) :=
  (hT.preimage measurable_snd).inter
    ((measurableSet_le (hx.comp measurable_snd) ((Shao.measurable_prefixSum l).comp measurable_fst)).inter
      (measurableSet_le ((Shao.measurable_prefixSum l).comp measurable_fst)
        ((hx.comp measurable_snd).add measurable_const)))

/-- Fix the whole unconditioned last block before using first-block concentration. -/
theorem movingIntervalEvent_probability_le (l r : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hconcentration : ∀ x : ℝ,
      (Measure.pi (fun _ : Fin l => ν)).real {a | Shao.prefixSum a l ∈ Set.Icc x (x + 1)} ≤ q)
    (T : Set (Shao.Path r)) (hT : MeasurableSet T) (x : Shao.Path r → ℝ) (hx : Measurable x) :
    ((Measure.pi (fun _ : Fin l => ν)).prod (Measure.pi (fun _ : Fin r => ν))).real
      (movingIntervalEvent (l := l) T x) ≤ q * (Measure.pi (fun _ : Fin r => ν)).real T := by
  have hs (b : Shao.Path r) :
      (Measure.pi (fun _ : Fin l => ν)) {a | (a, b) ∈ movingIntervalEvent (l := l) T x} ≤
        T.indicator (fun _ => ENNReal.ofReal q) b := by
    by_cases hb : b ∈ T
    · rw [Set.indicator_of_mem hb]
      have heq : {a | (a, b) ∈ movingIntervalEvent (l := l) T x} =
          {a | Shao.prefixSum a l ∈ Set.Icc (x b) (x b + 1)} := by
        ext a
        simp [movingIntervalEvent, hb]
      rw [heq, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal (hconcentration (x b))
    · rw [Set.indicator_of_notMem hb]
      have heq : {a | (a, b) ∈ movingIntervalEvent (l := l) T x} = ∅ := by
        ext a
        simp [movingIntervalEvent, hb]
      simp [heq]
  have hbound : ((Measure.pi (fun _ : Fin l => ν)).prod (Measure.pi (fun _ : Fin r => ν)))
      (movingIntervalEvent (l := l) T x) ≤ ENNReal.ofReal q * (Measure.pi (fun _ : Fin r => ν)) T := by
    rw [Measure.prod_apply_symm (measurableSet_movingIntervalEvent l r T hT x hx)]
    calc
      _ ≤ ∫⁻ b, T.indicator (fun _ => ENNReal.ofReal q) b ∂Measure.pi (fun _ : Fin r => ν) :=
        lintegral_mono hs
      _ = _ := by rw [lintegral_indicator hT, lintegral_const, Measure.restrict_apply_univ]
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)) hbound
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hq] using ht

/-- Upper endpoints force reversed lower survival; lower endpoints force upper survival. -/
theorem surviving_layer_subset (l r : ℕ) (hl : 1 ≤ l) (h z : ℝ) (j : ℕ) :
    {p : Shao.Path l × Shao.Path r |
      Fin.append p.1 p.2 ∈ shiftedClosedSurvival h z ∧
      shiftedEndpoint z (Fin.append p.1 p.2) ∈ boundaryLayer (fun w : ℝ => h - |w|) j} ⊆
    movingIntervalEvent (l := l) {b | reverseBlock b ∈ lowerBlockSurvival ((j : ℝ) + 1)}
      (fun b => h - (j : ℝ) - 1 - z - Shao.prefixSum b r) ∪
    movingIntervalEvent (l := l) {b | reverseBlock b ∈ Shao.closedUpper ((j : ℝ) + 1)}
      (fun b => -h + (j : ℝ) - z - Shao.prefixSum b r) := by
  rintro ⟨a, b⟩ ⟨hs, hj⟩
  let w : ℝ := shiftedEndpoint z (Fin.append a b)
  have hw : w = z + Shao.prefixSum a l + Shao.prefixSum b r := by
    dsimp [w, shiftedEndpoint]
    rw [prefixSum_append]
    ring
  change (j : ℝ) ≤ h - |w| ∧ h - |w| < (j : ℝ) + 1 at hj
  have hstate (k : ℕ) (hk : k ≤ r) :
      |z + Shao.prefixSum (Fin.append a b) (l + (r - k))| ≤ h :=
    hs _ (by omega) (by omega)
  have hrev (k : ℕ) (hk : k ≤ r) : Shao.prefixSum (reverseBlock b) k =
      w - (z + Shao.prefixSum (Fin.append a b) (l + (r - k))) := by
    rw [prefixSum_reverseBlock r k hk, prefixSum_append, hw]
    ring
  by_cases hw0 : 0 ≤ w
  · apply Or.inl
    change reverseBlock b ∈ lowerBlockSurvival ((j : ℝ) + 1) ∧ _
    rw [abs_of_nonneg hw0] at hj
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      rw [Shao.prefixSum_neg, hrev k hk]
      have hx := (abs_le.mp (hstate k hk)).2
      linarith
    · linarith
    · linarith
  · apply Or.inr
    change reverseBlock b ∈ Shao.closedUpper ((j : ℝ) + 1) ∧ _
    rw [abs_of_neg (lt_of_not_ge hw0)] at hj
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      rw [hrev k hk]
      have hx := (abs_le.mp (hstate k hk)).1
      linarith
    · linarith
    · linarith

/-- The conditional probability mechanism, with all S/AC inputs retained. -/
theorem boundary_occupation_block_bound (l r : ℕ) (hl : 1 ≤ l) (_hr : 1 ≤ r)
    (h z : ℝ) (_hh : 0 ≤ h) (_hz : |z| ≤ h) (j : ℕ)
    (q sPlus sMinus : ℝ) (hq : 0 ≤ q) (_hsp : 0 ≤ sPlus) (_hsm : 0 ≤ sMinus)
    (hconcentration : ∀ x : ℝ,
      (Measure.pi (fun _ : Fin l => ν)).real {a | Shao.prefixSum a l ∈ Set.Icc x (x + 1)} ≤ q)
    (hplus : (Measure.pi (fun _ : Fin r => ν)).real (Shao.closedUpper ((j : ℝ) + 1)) ≤ sPlus)
    (hminus : (Measure.pi (fun _ : Fin r => ν)).real (lowerBlockSurvival ((j : ℝ) + 1)) ≤ sMinus) :
    (killedIterKernel ν h (l + r) z).real (boundaryLayer (fun w : ℝ => h - |w|) j) ≤
      q * (sPlus + sMinus) := by
  let L : Set (Shao.Path r) := {b | reverseBlock b ∈ lowerBlockSurvival ((j : ℝ) + 1)}
  let U : Set (Shao.Path r) := {b | reverseBlock b ∈ Shao.closedUpper ((j : ℝ) + 1)}
  let xL : Shao.Path r → ℝ := fun b => h - (j : ℝ) - 1 - z - Shao.prefixSum b r
  let xU : Shao.Path r → ℝ := fun b => -h + (j : ℝ) - z - Shao.prefixSum b r
  have hL : MeasurableSet L := (measurableSet_lowerBlockSurvival r _).preimage (measurable_reverseBlock r)
  have hU : MeasurableSet U := (measurableSet_closedUpper r _).preimage (measurable_reverseBlock r)
  have hxL : Measurable xL := measurable_const.sub (Shao.measurable_prefixSum r)
  have hxU : Measurable xU := measurable_const.sub (Shao.measurable_prefixSum r)
  have hlayer : MeasurableSet (boundaryLayer (fun w : ℝ => h - |w|) j) :=
    measurableSet_boundaryLayer (by fun_prop) j
  let V : Set (Shao.Path (l + r)) := {c | c ∈ shiftedClosedSurvival h z ∧
    shiftedEndpoint z c ∈ boundaryLayer (fun w : ℝ => h - |w|) j}
  have hV : MeasurableSet V := (measurableSet_shiftedClosedSurvival _ h z).inter
    (hlayer.preimage (measurable_shiftedEndpoint _ z))
  have hrow : (killedIterKernel ν h (l + r) z).real (boundaryLayer (fun w : ℝ => h - |w|) j) =
      (Measure.pi (fun _ : Fin (l + r) => ν)).real V := by
    simp only [measureReal_def]
    rw [killedIterKernel_eq_path_law ν (l + r) h z,
      Measure.map_apply (measurable_shiftedEndpoint _ z) hlayer,
      Measure.restrict_apply (hlayer.preimage (measurable_shiftedEndpoint _ z))]
    congr 2
    ext c
    simp [V, and_comm]
  have hsplit : ((Measure.pi (fun _ : Fin l => ν)).prod (Measure.pi (fun _ : Fin r => ν))).real
      {p | Fin.append p.1 p.2 ∈ V} = (Measure.pi (fun _ : Fin (l + r) => ν)).real V := by
    simp only [measureReal_def]
    congr 1
    exact (measurePreserving_append ν l r).measure_preimage hV.nullMeasurableSet
  have hLprob : (Measure.pi (fun _ : Fin r => ν)).real L ≤ sMinus := by
    have heq := (measurePreserving_reverseBlock ν r).measure_preimage
      (measurableSet_lowerBlockSurvival r ((j : ℝ) + 1)).nullMeasurableSet
    change (Measure.pi (fun _ : Fin r => ν)) L = _ at heq
    simpa only [measureReal_def, heq] using hminus
  have hUprob : (Measure.pi (fun _ : Fin r => ν)).real U ≤ sPlus := by
    have heq := (measurePreserving_reverseBlock ν r).measure_preimage
      (measurableSet_closedUpper r ((j : ℝ) + 1)).nullMeasurableSet
    change (Measure.pi (fun _ : Fin r => ν)) U = _ at heq
    simpa only [measureReal_def, heq] using hplus
  rw [hrow, ← hsplit]
  calc
    _ ≤ ((Measure.pi (fun _ : Fin l => ν)).prod (Measure.pi (fun _ : Fin r => ν))).real
        (movingIntervalEvent (l := l) L xL ∪ movingIntervalEvent (l := l) U xU) :=
      measureReal_mono (surviving_layer_subset l r hl h z j)
    _ ≤ ((Measure.pi (fun _ : Fin l => ν)).prod (Measure.pi (fun _ : Fin r => ν))).real
        (movingIntervalEvent (l := l) L xL) +
        ((Measure.pi (fun _ : Fin l => ν)).prod (Measure.pi (fun _ : Fin r => ν))).real
          (movingIntervalEvent (l := l) U xU) := measureReal_union_le _ _
    _ ≤ q * (Measure.pi (fun _ : Fin r => ν)).real L + q * (Measure.pi (fun _ : Fin r => ν)).real U :=
      add_le_add (movingIntervalEvent_probability_le ν l r q hq hconcentration L hL xL hxL)
        (movingIntervalEvent_probability_le ν l r q hq hconcentration U hU xU hxU)
    _ ≤ q * sMinus + q * sPlus := add_le_add (mul_le_mul_of_nonneg_left hLprob hq)
      (mul_le_mul_of_nonneg_left hUprob hq)
    _ = q * (sPlus + sMinus) := by ring

theorem half_blocks_sqrt_bound (m : ℕ) (hm : 6 ≤ m) :
    1 ≤ m / 2 ∧ 1 ≤ m - m / 2 ∧
      (m : ℝ) ≤ 3 * (Real.sqrt (m / 2 : ℕ) * Real.sqrt (m - m / 2 : ℕ)) := by
  have hl : 1 ≤ m / 2 := by omega
  have hr : 1 ≤ m - m / 2 := by omega
  have hml : (m : ℝ) ≤ 3 * (m / 2 : ℕ) := by exact_mod_cast (show m ≤ 3 * (m / 2) by omega)
  have hmr : (m : ℝ) ≤ 3 * (m - m / 2 : ℕ) := by exact_mod_cast (show m ≤ 3 * (m - m / 2) by omega)
  have hxl : (m : ℝ) / 3 ≤ (m / 2 : ℕ) := by linarith
  have hxr : (m : ℝ) / 3 ≤ (m - m / 2 : ℕ) := by linarith
  have hprod := mul_le_mul hxl hxr (by positivity : 0 ≤ (m : ℝ) / 3)
    (by positivity : 0 ≤ ((m / 2 : ℕ) : ℝ))
  have hs : ((m : ℝ) / 3) ^ 2 ≤
      (Real.sqrt (m / 2 : ℕ) * Real.sqrt (m - m / 2 : ℕ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    nlinarith
  have horder : ∀ p : ℝ, 0 ≤ p → ((m : ℝ) / 3) ^ 2 ≤ p ^ 2 → (m : ℝ) / 3 ≤ p := by
    intro p hp hsq
    have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  have hp := horder _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hs
  exact ⟨hl, hr, by linarith⟩

/-- The safe half-block constant, retaining the actual concentration and survival inputs. -/
theorem boundary_occupation_half_bound (m : ℕ) (hm : 6 ≤ m) (h z : ℝ)
    (hh : 0 ≤ h) (hz : |z| ≤ h) (j : ℕ) (β Cq Cs : ℝ)
    (hβ : 0 ≤ β) (hCq : 0 ≤ Cq) (hCs : 0 ≤ Cs)
    (hconcentration : ∀ x : ℝ,
      (Measure.pi (fun _ : Fin (m / 2) => ν)).real
        {a | Shao.prefixSum a (m / 2) ∈ Set.Icc x (x + 1)} ≤ Cq * β / Real.sqrt (m / 2 : ℕ))
    (hplus : (Measure.pi (fun _ : Fin (m - m / 2) => ν)).real (Shao.closedUpper ((j : ℝ) + 1)) ≤
      Cs * ((j : ℝ) + 1 + β) / Real.sqrt (m - m / 2 : ℕ))
    (hminus : (Measure.pi (fun _ : Fin (m - m / 2) => ν)).real (lowerBlockSurvival ((j : ℝ) + 1)) ≤
      Cs * ((j : ℝ) + 1 + β) / Real.sqrt (m - m / 2 : ℕ)) :
    (killedIterKernel ν h m z).real (boundaryLayer (fun w : ℝ => h - |w|) j) ≤
      6 * Cq * Cs * β * ((j : ℝ) + 1 + β) / (m : ℝ) := by
  obtain ⟨hl, hr, hden⟩ := half_blocks_sqrt_bound m hm
  have hmadd : m / 2 + (m - m / 2) = m := by omega
  have hprob := boundary_occupation_block_bound ν (m / 2) (m - m / 2) hl hr h z hh hz j
    (Cq * β / Real.sqrt (m / 2 : ℕ))
    (Cs * ((j : ℝ) + 1 + β) / Real.sqrt (m - m / 2 : ℕ))
    (Cs * ((j : ℝ) + 1 + β) / Real.sqrt (m - m / 2 : ℕ))
    (by positivity) (by positivity) (by positivity) hconcentration hplus hminus
  rw [hmadd] at hprob
  have hxl : 0 < Real.sqrt (m / 2 : ℕ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < m / 2 by omega))
  have hxr : 0 < Real.sqrt (m - m / 2 : ℕ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < m - m / 2 by omega))
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  calc
    _ ≤ (Cq * β / Real.sqrt (m / 2 : ℕ)) *
        (Cs * ((j : ℝ) + 1 + β) / Real.sqrt (m - m / 2 : ℕ) +
          Cs * ((j : ℝ) + 1 + β) / Real.sqrt (m - m / 2 : ℕ)) := hprob
    _ = 2 * (Cq * Cs * β * ((j : ℝ) + 1 + β)) /
        (Real.sqrt (m / 2 : ℕ) * Real.sqrt (m - m / 2 : ℕ)) := by
      field_simp [ne_of_gt hxl, ne_of_gt hxr]
      ring
    _ ≤ 6 * (Cq * Cs * β * ((j : ℝ) + 1 + β)) / (m : ℝ) := by
      apply (div_le_div_iff₀ (mul_pos hxl hxr) hm0).2
      convert mul_le_mul_of_nonneg_left hden
        (by positivity : 0 ≤ 2 * (Cq * Cs * β * ((j : ℝ) + 1 + β))) using 1; ring
    _ = _ := by ring

/-- The h-squared block form used to supply all layers, conditional on the same S/AC inputs. -/
theorem boundary_occupation_hsq_bound (h z : ℝ) (hh3 : 3 ≤ h) (hz : |z| ≤ h)
    (j : ℕ) (β M Cq Cs : ℝ) (hβ : 0 ≤ β) (hM : 0 ≤ M) (hβM : β ≤ M)
    (hCq : 0 ≤ Cq) (hCs : 0 ≤ Cs)
    (hconcentration : ∀ x : ℝ,
      (Measure.pi (fun _ : Fin (⌊h ^ 2⌋₊ / 2) => ν)).real
        {a | Shao.prefixSum a (⌊h ^ 2⌋₊ / 2) ∈ Set.Icc x (x + 1)} ≤
          Cq * β / Real.sqrt (⌊h ^ 2⌋₊ / 2 : ℕ))
    (hplus : (Measure.pi (fun _ : Fin (⌊h ^ 2⌋₊ - ⌊h ^ 2⌋₊ / 2) => ν)).real
        (Shao.closedUpper ((j : ℝ) + 1)) ≤
      Cs * ((j : ℝ) + 1 + β) / Real.sqrt (⌊h ^ 2⌋₊ - ⌊h ^ 2⌋₊ / 2 : ℕ))
    (hminus : (Measure.pi (fun _ : Fin (⌊h ^ 2⌋₊ - ⌊h ^ 2⌋₊ / 2) => ν)).real
        (lowerBlockSurvival ((j : ℝ) + 1)) ≤
      Cs * ((j : ℝ) + 1 + β) / Real.sqrt (⌊h ^ 2⌋₊ - ⌊h ^ 2⌋₊ / 2 : ℕ)) :
    (killedIterKernel ν h ⌊h ^ 2⌋₊ z).real (boundaryLayer (fun w : ℝ => h - |w|) j) ≤
      (12 * Cq * Cs * M * (1 + M) / h ^ 2) * ((j : ℝ) + 1) := by
  let m : ℕ := ⌊h ^ 2⌋₊
  have hh : 0 < h := by linarith
  have hsq : 9 ≤ h ^ 2 := by nlinarith
  have ht : h ^ 2 < (m : ℝ) + 1 := Nat.lt_floor_add_one (h ^ 2)
  have hm : 6 ≤ m := by
    have hmreal : (6 : ℝ) ≤ (m : ℝ) := by linarith
    exact_mod_cast hmreal
  have hmhalf : h ^ 2 ≤ 2 * (m : ℝ) := by linarith
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hterm : (j : ℝ) + 1 + β ≤ (1 + M) * ((j : ℝ) + 1) := by
    nlinarith [mul_nonneg hM hj]
  have hβterm : β * ((j : ℝ) + 1 + β) ≤ M * (1 + M) * ((j : ℝ) + 1) := by
    calc
      _ ≤ M * ((j : ℝ) + 1 + β) := mul_le_mul_of_nonneg_right hβM (by positivity)
      _ ≤ M * ((1 + M) * ((j : ℝ) + 1)) := mul_le_mul_of_nonneg_left hterm hM
      _ = _ := by ring
  have hp := boundary_occupation_half_bound ν m hm h z (le_of_lt hh) hz j β Cq Cs hβ hCq hCs
    hconcentration hplus hminus
  calc
    _ ≤ 6 * Cq * Cs * β * ((j : ℝ) + 1 + β) / (m : ℝ) := hp
    _ ≤ 6 * Cq * Cs * M * (1 + M) * ((j : ℝ) + 1) / (m : ℝ) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hm0)
      convert mul_le_mul_of_nonneg_left hβterm (by positivity : 0 ≤ 6 * Cq * Cs) using 1 <;> ring
    _ ≤ 12 * Cq * Cs * M * (1 + M) * ((j : ℝ) + 1) / h ^ 2 := by
      apply (div_le_div_iff₀ hm0 (sq_pos_of_pos hh)).2
      convert mul_le_mul_of_nonneg_left hmhalf
        (by positivity : 0 ≤ 6 * Cq * Cs * M * (1 + M) * ((j : ℝ) + 1)) using 1; ring
    _ = _ := by ring

end Shao.OQ4
