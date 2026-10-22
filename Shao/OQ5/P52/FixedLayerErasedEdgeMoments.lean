import Shao.OQ5.P52.FixedLayerErasedCanonical
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Integration

/-!
# Genuine residual-edge moments under the actual erased finite product law

Ordinary pair and triple pushforwards transport honest L2 and L1 inputs.
Canonical rows kill a unique endpoint almost everywhere. Symmetry handles
all shared-endpoint orientations and reversal of an unordered edge.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

attribute [local instance] fixedErasedLaw_isProbabilityMeasure

private theorem coordinate_independence (j n : ℕ) :
    iIndepFun (fun i (x : Fin n → LayerObs) => x i)
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) :=
  iIndepFun_pi (μ := fun _ : Fin n => fixedErasedLaw j)
    (X := fun _ (o : LayerObs) => o) (fun _ => measurable_id.aemeasurable)

private theorem coordinate_map (j n : ℕ) (i : Fin n) :
    (Measure.pi (fun _ : Fin n => fixedErasedLaw j)).map
      (fun x : Fin n → LayerObs => x i) = fixedErasedLaw j :=
  (measurePreserving_eval (μ := fun _ : Fin n => fixedErasedLaw j) i).map_eq

private theorem coordinate_pair_mp (j n : ℕ) (a b : Fin n) (hab : a ≠ b) :
    MeasurePreserving (fun x : Fin n → LayerObs => (x a, x b))
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j))
      ((fixedErasedLaw j).prod (fixedErasedLaw j)) := by
  refine ⟨(measurable_pi_apply a).prodMk (measurable_pi_apply b), ?_⟩
  have hi := (coordinate_independence j n).indepFun hab
  simpa only [coordinate_map] using hi.map_prod_eq_prod_map_map
    (measurable_pi_apply a).aemeasurable (measurable_pi_apply b).aemeasurable

private theorem integral_pair_pullback (j n : ℕ) (a b : Fin n) (hab : a ≠ b)
    (f : LayerObs × LayerObs → ℝ)
    (hf : Integrable f ((fixedErasedLaw j).prod (fixedErasedLaw j))) :
    (∫ x : Fin n → LayerObs, f (x a, x b)
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) =
      ∫ z : LayerObs × LayerObs, f z ∂(fixedErasedLaw j).prod (fixedErasedLaw j) := by
  have hp := coordinate_pair_mp j n a b hab
  have hfm : Integrable f ((Measure.pi (fun _ : Fin n => fixedErasedLaw j)).map
      (fun x : Fin n → LayerObs => (x a, x b))) := by
    rw [hp.map_eq]
    exact hf
  calc
    _ = ∫ z : LayerObs × LayerObs, f z
        ∂(Measure.pi (fun _ : Fin n => fixedErasedLaw j)).map
          (fun x : Fin n → LayerObs => (x a, x b)) :=
      (integral_map hp.measurable.aemeasurable hfm.aestronglyMeasurable).symm
    _ = _ := by rw [hp.map_eq]

theorem fixedErasedResidualEdge_memLp_two (j n : ℕ) (a b : Fin n) (hab : a ≠ b) :
    MemLp (fun x : Fin n → LayerObs => fixedResidualKernel (x a, x b)) 2
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) :=
  (fixedResidualKernel_memLp_two_fixedErasedLaw j).comp_measurePreserving
    (coordinate_pair_mp j n a b hab)

theorem integral_fixedErasedResidualEdge_eq_zero
    (j n : ℕ) (a b : Fin n) (hab : a ≠ b) :
    (∫ x : Fin n → LayerObs, fixedResidualKernel (x a, x b)
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = 0 := by
  have _hedge : Integrable (fun x : Fin n → LayerObs => fixedResidualKernel (x a, x b))
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) :=
    (fixedErasedResidualEdge_memLp_two j n a b hab).integrable (by norm_num)
  have hr : Integrable fixedResidualKernel ((fixedErasedLaw j).prod (fixedErasedLaw j)) :=
    (fixedResidualKernel_memLp_two_fixedErasedLaw j).integrable (by norm_num)
  rw [integral_pair_pullback j n a b hab fixedResidualKernel hr]
  exact integral_fixedResidualKernel_fixedErasedLaw_eq_zero j

theorem integrable_fixedErasedResidualEdge_mul
    (j n : ℕ) (a b c d : Fin n) (hab : a ≠ b) (hcd : c ≠ d) :
    Integrable (fun x : Fin n → LayerObs =>
      fixedResidualKernel (x a, x b) * fixedResidualKernel (x c, x d))
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) :=
  (fixedErasedResidualEdge_memLp_two j n a b hab).integrable_mul
    (fixedErasedResidualEdge_memLp_two j n c d hcd)

private theorem coordinate_triple_mp (j n : ℕ) (a b c : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    MeasurePreserving (fun x : Fin n → LayerObs => ((x a, x b), x c))
      (Measure.pi (fun _ : Fin n => fixedErasedLaw j))
      (((fixedErasedLaw j).prod (fixedErasedLaw j)).prod (fixedErasedLaw j)) := by
  have hp := coordinate_pair_mp j n a b hab
  have hi := (coordinate_independence j n).indepFun_prodMk
    (fun i => measurable_pi_apply i) a b c hac hbc
  refine ⟨((measurable_pi_apply a).prodMk (measurable_pi_apply b)).prodMk
    (measurable_pi_apply c), ?_⟩
  simpa only [hp.map_eq, coordinate_map] using hi.map_prod_eq_prod_map_map
    ((measurable_pi_apply a).prodMk (measurable_pi_apply b)).aemeasurable
    (measurable_pi_apply c).aemeasurable

private theorem shared_edge_zero (j n : ℕ) (s u v : Fin n)
    (hsu : s ≠ u) (hsv : s ≠ v) (huv : u ≠ v) :
    (∫ x : Fin n → LayerObs,
      fixedResidualKernel (x s, x u) * fixedResidualKernel (x s, x v)
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) = 0 := by
  let β := fixedErasedLaw j
  let P := Measure.pi (fun _ : Fin n => β)
  let T : (Fin n → LayerObs) → (LayerObs × LayerObs) × LayerObs :=
    fun x => ((x s, x u), x v)
  let H : (LayerObs × LayerObs) × LayerObs → ℝ := fun z =>
    fixedResidualKernel (z.1.1, z.1.2) * fixedResidualKernel (z.1.1, z.2)
  have hT : MeasurePreserving T P ((β.prod β).prod β) :=
    coordinate_triple_mp j n s u v hsu hsv huv
  have hH : Measurable H :=
    (measurable_fixedResidualKernel.comp
      ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst))).mul
      (measurable_fixedResidualKernel.comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hpull : Integrable (H ∘ T) P :=
    integrable_fixedErasedResidualEdge_mul j n s u s v hsu hsv
  have hI : Integrable H ((β.prod β).prod β) :=
    (hT.integrable_comp hH.aestronglyMeasurable).mp hpull
  have hrowI : ∀ᵐ z : LayerObs × LayerObs ∂β.prod β,
      Integrable (fun c : LayerObs => fixedResidualKernel (z.1, c)) β :=
    (measurePreserving_fst (μ := β) (ν := β)).quasiMeasurePreserving.ae
      (integrable_fixedResidualKernel_row_fixedErasedLaw_ae j)
  have hrow0 : ∀ᵐ z : LayerObs × LayerObs ∂β.prod β,
      (∫ c : LayerObs, fixedResidualKernel (z.1, c) ∂β) = 0 :=
    (measurePreserving_fst (μ := β) (ν := β)).quasiMeasurePreserving.ae
      (integral_fixedResidualKernel_row_fixedErasedLaw_eq_zero_ae j)
  have hz : (∫ z : (LayerObs × LayerObs) × LayerObs, H z ∂(β.prod β).prod β) = 0 := by
    rw [integral_prod H hI]
    calc
      _ = ∫ _z : LayerObs × LayerObs, (0 : ℝ) ∂β.prod β := by
        apply integral_congr_ae
        filter_upwards [hrowI, hrow0] with z hi hz
        have _hinner : Integrable (fun c : LayerObs =>
            fixedResidualKernel (z.1, z.2) * fixedResidualKernel (z.1, c)) β :=
          hi.const_mul (fixedResidualKernel (z.1, z.2))
        change (∫ c : LayerObs,
          fixedResidualKernel (z.1, z.2) * fixedResidualKernel (z.1, c) ∂β) = 0
        rw [integral_const_mul, hz, mul_zero]
      _ = 0 := by simp only [integral_zero]
  have hImap : Integrable H (P.map T) := by
    rw [hT.map_eq]
    exact hI
  calc
    _ = ∫ z : (LayerObs × LayerObs) × LayerObs, H z ∂P.map T :=
      (integral_map hT.measurable.aemeasurable hImap.aestronglyMeasurable).symm
    _ = ∫ z : (LayerObs × LayerObs) × LayerObs, H z ∂(β.prod β).prod β := by
      rw [hT.map_eq]
    _ = 0 := hz

private theorem edge_square_moment (j n : ℕ) (a b : Fin n) (hab : a ≠ b) :
    (∫ x : Fin n → LayerObs, (fixedResidualKernel (x a, x b)) ^ 2
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) =
      ∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
        ∂(fixedErasedLaw j).prod (fixedErasedLaw j) := by
  have _hIsample := (fixedErasedResidualEdge_memLp_two j n a b hab).integrable_sq
  exact integral_pair_pullback j n a b hab (fun z => (fixedResidualKernel z) ^ 2)
    (fixedResidualKernel_memLp_two_fixedErasedLaw j).integrable_sq

theorem integral_fixedErasedResidualEdge_mul
    (j n : ℕ) (a b c d : Fin n) (hab : a ≠ b) (hcd : c ≠ d) :
    (∫ x : Fin n → LayerObs,
      fixedResidualKernel (x a, x b) * fixedResidualKernel (x c, x d)
      ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j)) =
      if ({a, b} : Finset (Fin n)) = {c, d} then
        ∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
          ∂(fixedErasedLaw j).prod (fixedErasedLaw j)
      else 0 := by
  classical
  have _hproduct := integrable_fixedErasedResidualEdge_mul j n a b c d hab hcd
  by_cases hsets : ({a, b} : Finset (Fin n)) = {c, d}
  · rw [ite_eq_left hsets]
    have ha : a = c ∨ a = d := by
      have hm : a ∈ ({c, d} : Finset (Fin n)) := by rw [← hsets]; simp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    rcases ha with hac | had
    · subst c
      have hbd : b = d := by
        have hm : b ∈ ({a, d} : Finset (Fin n)) := by rw [← hsets]; simp
        rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hm :
          b = a ∨ b = d) with hba | hbd
        · exact False.elim (hab hba.symm)
        · exact hbd
      subst d
      calc
        _ = ∫ x : Fin n → LayerObs, (fixedResidualKernel (x a, x b)) ^ 2
            ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j) := by
          apply integral_congr_ae
          exact Eventually.of_forall (fun x => (pow_two (fixedResidualKernel (x a, x b))).symm)
        _ = _ := edge_square_moment j n a b hab
    · subst d
      have hbc : b = c := by
        have hm : b ∈ ({c, a} : Finset (Fin n)) := by rw [← hsets]; simp
        rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hm :
          b = c ∨ b = a) with hbc | hba
        · exact hbc
        · exact False.elim (hab hba.symm)
      subst c
      calc
        _ = ∫ x : Fin n → LayerObs, (fixedResidualKernel (x a, x b)) ^ 2
            ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j) := by
          apply integral_congr_ae
          exact Eventually.of_forall (fun x => by
            dsimp only
            rw [fixedResidualKernel_symmetric (x b) (x a)]
            exact (pow_two _).symm)
        _ = _ := edge_square_moment j n a b hab
  · rw [ite_eq_right hsets]
    by_cases hac : a = c
    · subst c
      have hbd : b ≠ d := by intro h; apply hsets; subst d; rfl
      exact shared_edge_zero j n a b d hab hcd hbd
    · by_cases had : a = d
      · subst d
        have hbc : b ≠ c := by
          intro h
          apply hsets
          rw [h]
          exact Finset.pair_comm _ _
        calc
          _ = ∫ x : Fin n → LayerObs,
              fixedResidualKernel (x a, x b) * fixedResidualKernel (x a, x c)
              ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j) := by
            apply integral_congr_ae
            exact Eventually.of_forall (fun x => by
              dsimp only
              rw [fixedResidualKernel_symmetric (x c) (x a)])
          _ = 0 := shared_edge_zero j n a b c hab hcd.symm hbc
      · by_cases hbc : b = c
        · subst c
          calc
            _ = ∫ x : Fin n → LayerObs,
                fixedResidualKernel (x b, x a) * fixedResidualKernel (x b, x d)
                ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j) := by
              apply integral_congr_ae
              exact Eventually.of_forall (fun x => by
                dsimp only
                rw [fixedResidualKernel_symmetric (x a) (x b)])
            _ = 0 := shared_edge_zero j n b a d hab.symm hcd had
        · by_cases hbd : b = d
          · subst d
            calc
              _ = ∫ x : Fin n → LayerObs,
                  fixedResidualKernel (x b, x a) * fixedResidualKernel (x b, x c)
                  ∂Measure.pi (fun _ : Fin n => fixedErasedLaw j) := by
                apply integral_congr_ae
                exact Eventually.of_forall (fun x => by
                  dsimp only
                  rw [fixedResidualKernel_symmetric (x a) (x b),
                    fixedResidualKernel_symmetric (x c) (x b)])
              _ = 0 := shared_edge_zero j n b a c hab.symm hcd.symm hac
          · have hind := (coordinate_independence j n).indepFun_prodMk_prodMk
              (fun i => measurable_pi_apply i) a b c d hac had hbc hbd
            have hi : IndepFun
                (fun x : Fin n → LayerObs => fixedResidualKernel (x a, x b))
                (fun x : Fin n → LayerObs => fixedResidualKernel (x c, x d))
                (Measure.pi (fun _ : Fin n => fixedErasedLaw j)) :=
              hind.comp measurable_fixedResidualKernel measurable_fixedResidualKernel
            rw [hi.integral_fun_mul_eq_mul_integral
              (fixedErasedResidualEdge_memLp_two j n a b hab).aestronglyMeasurable
              (fixedErasedResidualEdge_memLp_two j n c d hcd).aestronglyMeasurable,
              integral_fixedErasedResidualEdge_eq_zero j n a b hab,
              integral_fixedErasedResidualEdge_eq_zero j n c d hcd]
            exact zero_mul _

end
end Shao.OQ5.P52
