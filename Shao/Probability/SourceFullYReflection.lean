import Shao.Probability.SourceGrowingYReflection
import Shao.Probability.SourceBoundedYReflection

/-!
Same-law full-threshold smoothed maximum/endpoint comparison.
The exact growing cutoff is retained. The low-threshold comparison is
transported by the joint Lindley/energy distribution, including zero energy
and atoms; the high-threshold comparison reuses the accepted growing bound.
This supplies the smoothed comparison only, not the original root assembly.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000

namespace Shao.Probability
open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem fy_test_data (y : ℝ) :
    Measurable (sourceFourierTest y) ∧
      ∀ p : ℝ × ℝ, 0 ≤ sourceFourierTest y p ∧ sourceFourierTest y p ≤ 1 := by
  constructor
  · have hA : MeasurableSet {p : ℝ × ℝ | |p.1| < y * Real.sqrt p.2} :=
      (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet
    exact (sourceKernelCutoff_data.1.continuous.measurable.comp measurable_snd).mul
      (Measurable.ite hA measurable_const measurable_const)
  · intro p
    unfold sourceFourierTest
    split_ifs
    · simpa using sourceKernelCutoff_data.2.2.1 p.2
    · simp

private theorem fy_noise_measurable (noise : Measure (ℝ × ℝ))
    [IsProbabilityMeasure noise] (y : ℝ) :
    Measurable (fun p : ℝ × ℝ => ∫ z : ℝ × ℝ,
      sourceFourierTest y (p.1 + z.1, p.2 + z.2) ∂noise) := by
  have hm : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      sourceFourierTest y (p.1.1 + p.2.1, p.1.2 + p.2.2)) :=
    (fy_test_data y).1.comp (by fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

private theorem fy_joint_data {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (noise : Measure (ℝ × ℝ))
    [IsProbabilityMeasure P] [IsProbabilityMeasure noise]
    (y : ℝ) (Z : Ω → ℝ × ℝ) (hZ : Measurable Z) :
    let f : Ω × (ℝ × ℝ) → ℝ := fun p => sourceFourierTest y
      ((Z p.1).1 + p.2.1, (Z p.1).2 + p.2.2)
    Measurable f ∧ Integrable f (P.prod noise) ∧
      (∫ a : Ω, ∫ z : ℝ × ℝ, sourceFourierTest y
        ((Z a).1 + z.1, (Z a).2 + z.2) ∂noise ∂P) =
          ∫ p : Ω × (ℝ × ℝ), f p ∂P.prod noise := by
  dsimp only
  have hm : Measurable (fun p : Ω × (ℝ × ℝ) => sourceFourierTest y
      ((Z p.1).1 + p.2.1, (Z p.1).2 + p.2.2)) :=
    (fy_test_data y).1.comp
      (((hZ.fst.comp measurable_fst).add measurable_snd.fst).prodMk
        ((hZ.snd.comp measurable_fst).add measurable_snd.snd))
  have hi : Integrable (fun p : Ω × (ℝ × ℝ) => sourceFourierTest y
      ((Z p.1).1 + p.2.1, (Z p.1).2 + p.2.2)) (P.prod noise) :=
    (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg ((fy_test_data y).2 _).1]
          using ((fy_test_data y).2 _).2)
  exact ⟨hm, hi, (integral_prod _ hi).symm⟩

private theorem fy_moment_payment
    (ν0 : Measure ℝ) [IsProbabilityMeasure ν0] (n : ℕ)
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν0)
    (hn : (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1)
    (hm : (∫ a : ℝ, a ∂ν0) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x) (he : 0 < epsilon)
    (he2 : epsilon ≤ 1 / 2)
    (hR : Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8) :
    let ρ : Measure ℝ := ProbabilityTheory.cond ν0
      {a : ℝ | |a| ≤ epsilon / (1 + x)}
    (n : ℝ) * |∫ a : ℝ, a ∂ρ| + (n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂ρ) ≤
      4 * Shao.truncationBudget ν0 n x / epsilon ^ 2 := by
  dsimp only
  have hp := Shao.sourceTruncation_paid_moments ν0 n h2 hn hm x epsilon hx he he2 hR
  have hR0 := Shao.truncationBudget_nonneg ν0 n h2 x
  have heSq : epsilon ^ 2 ≤ 1 := by nlinarith
  have ha3 : 1 ≤ (1 + x) ^ 3 := by
    nlinarith [mul_nonneg hx (sq_nonneg x)]
  have hd1 : epsilon ^ 2 ≤ epsilon ^ 2 * (1 + x) := by
    nlinarith [mul_nonneg (sq_nonneg epsilon) hx]
  have hmupay := hp.1.trans
    (div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * Shao.truncationBudget ν0 n x)
      (sq_pos_of_pos he) hd1)
  have hbpay := hp.2.1.trans
    (div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * Shao.truncationBudget ν0 n x)
      (sq_pos_of_pos he) (heSq.trans ha3))
  calc
    _ ≤ 2 * Shao.truncationBudget ν0 n x / epsilon ^ 2 +
        2 * Shao.truncationBudget ν0 n x / epsilon ^ 2 := add_le_add hmupay hbpay
    _ = _ := by ring

theorem sourceGrowingCutoff_exact_and_bounded_compatible :
    let L : ℝ := 1600
    let L2 : ℝ := 16384
    let alpha : ℝ := 1 / 1024
    let epsilon0 : ℝ := min (1 / (64 * Real.sqrt L2)) (alpha / (8 * L))
    let epsilonG : ℝ := min (epsilon0 / 2)
      (1 / (4 * (8 * (1 + L) + 1) * L))
    epsilon0 = (1 / 13107200 : ℝ) ∧
      epsilonG = (1 / 81977600 : ℝ) ∧
      0 < epsilonG ∧ epsilonG ≤ (1 / 16384 : ℝ) ∧
      epsilonG ≤ (1 / 800 : ℝ) := by
  have hs : Real.sqrt (16384 : ℝ) = 128 := by
    rw [show (16384 : ℝ) = 128 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 128)]
  norm_num [hs]

theorem sourceTruncation_full_y_smoothed_probability_comparison :
    let L : ℝ := 1600
    let L2 : ℝ := 16384
    let alpha : ℝ := 1 / 1024
    let epsilon0 : ℝ := min (1 / (64 * Real.sqrt L2)) (alpha / (8 * L))
    let t0 : ℝ := Real.exp (-(48 * alpha / epsilon0))
    let eta0 : ℝ := min (1 / 16)
      (min (Real.sqrt t0 / (2 * Real.sqrt L2))
        (min ((epsilon0 / 20480) ^ 2)
          (1 / (16384 * (1 + 3 / t0) *
            Real.exp (24 * epsilon0 / t0)))))
    let epsilon : ℝ := min (epsilon0 / 2)
      (1 / (4 * (8 * (1 + L) + 1) * L))
    ∃ Cs : ℝ, 0 < Cs ∧
      ∀ (nu0 : Measure ℝ), IsProbabilityMeasure nu0 →
        ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) nu0 →
          (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu0) = 1 →
          (∫ a : ℝ, a ∂nu0) = 0 →
          ∀ x : ℝ, 0 ≤ x →
            Shao.truncationBudget nu0 n x ≤ epsilon ^ 3 / 8 →
            Shao.truncationBudget nu0 n x ≤ epsilon ^ 2 * eta0 / 40 →
            let rho : Measure ℝ := ProbabilityTheory.cond nu0
              {a : ℝ | |a| ≤ epsilon / (1 + x)}
            let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂rho) / variance (id : ℝ → ℝ) rho
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
            let noise : Measure (ℝ × ℝ) := quadraticFullNoiseLaw rho
            let w : ℝ := Shao.truncationBudget nu0 n x * Shao.standardNormalTail x
            IsProbabilityMeasure rho ∧ IsProbabilityMeasure P ∧
              IsProbabilityMeasure noise ∧
              ∀ y : ℝ, gamma ≤ y → |y - x| ≤ 1 / (2 * (1 + x)) →
                let fmax : Shao.Path n × (ℝ × ℝ) → ℝ := fun p =>
                  sourceFourierTest y
                    (Shao.maxWithZero p.1 + p.2.1, Shao.energy p.1 + p.2.2)
                let fend : Shao.Path n × (ℝ × ℝ) → ℝ := fun p =>
                  sourceFourierTest y
                    (Shao.prefixSum p.1 n + p.2.1, Shao.energy p.1 + p.2.2)
                let Jmax : ℝ := ∫ a : Shao.Path n,
                  (∫ z : ℝ × ℝ, sourceFourierTest y
                    (Shao.maxWithZero a + z.1, Shao.energy a + z.2) ∂noise) ∂P
                let Jend : ℝ := ∫ a : Shao.Path n,
                  (∫ z : ℝ × ℝ, sourceFourierTest y
                    (Shao.prefixSum a n + z.1, Shao.energy a + z.2) ∂noise) ∂P
                Measurable fmax ∧ Measurable fend ∧
                  Integrable fmax (P.prod noise) ∧ Integrable fend (P.prod noise) ∧
                  Jmax = (∫ p : Shao.Path n × (ℝ × ℝ), fmax p ∂P.prod noise) ∧
                  Jend = (∫ p : Shao.Path n × (ℝ × ℝ), fend p ∂P.prod noise) ∧
                  |Jmax - Jend| ≤ Cs * w := by
  classical
  intro L L2 alpha epsilon0 t0 eta0 epsilon
  have hcut := sourceGrowingCutoff_exact_and_bounded_compatible
  change epsilon0 = (1 / 13107200 : ℝ) ∧ epsilon = (1 / 81977600 : ℝ) ∧
    0 < epsilon ∧ epsilon ≤ (1 / 16384 : ℝ) ∧ epsilon ≤ (1 / 800 : ℝ) at hcut
  obtain ⟨he0eq, heeq, he, heBounded, he800⟩ := hcut
  have he2 : epsilon ≤ 1 / 2 := heBounded.trans (by norm_num)
  obtain ⟨Cb, hCb, HB⟩ := sourceTruncation_bounded_y_reflection_fixed_cutoff
  obtain ⟨_, _, _, _, _, Cg, hCg, HG⟩ :=
    sourceTruncation_growing_y_reflection_probability_comparison.{0}
  have ht2 : 0 < Shao.standardNormalTail 2 := (Shao.standardNormalTail_basic.2.2.1 2).1
  let Cs : ℝ := max
    (20 * Real.exp 2 * Cb / (epsilon ^ 2 * Shao.standardNormalTail 2))
    (20 * Real.exp 2 * Cg / epsilon ^ 2)
  have hCs : 0 < Cs := lt_of_lt_of_le (by positivity)
    (le_max_right _ _)
  refine ⟨Cs, hCs, ?_⟩
  intro ν0 hp n h2 hn hm x hx hR hReta ρ gamma P noise w
  letI : IsProbabilityMeasure ν0 := hp
  obtain ⟨hpρ, hpnoise, hIndep, hsupp, hnoisepay, HGy⟩ :=
    HG ν0 hp n h2 hn hm x hx hR hReta
  letI : IsProbabilityMeasure ρ := hpρ
  letI : IsProbabilityMeasure noise := hpnoise
  have hpP : IsProbabilityMeasure P := inferInstance
  letI : IsProbabilityMeasure P := hpP
  refine ⟨hpρ, hpP, hpnoise, ?_⟩
  intro y hgy hnear fmax fend Jmax Jend
  have hmax := fy_joint_data P noise y
    (fun a : Shao.Path n => (Shao.maxWithZero a, Shao.energy a))
    (Shao.measurable_maxWithZero.prodMk Shao.measurable_energy)
  have hend := fy_joint_data P noise y
    (fun a : Shao.Path n => (Shao.prefixSum a n, Shao.energy a))
    ((Shao.measurable_prefixSum n).prodMk Shao.measurable_energy)
  have hJmax : Jmax = ∫ p : Shao.Path n × (ℝ × ℝ), fmax p ∂P.prod noise := hmax.2.2
  have hJend : Jend = ∫ p : Shao.Path n × (ℝ × ℝ), fend p ∂P.prod noise := hend.2.2
  refine ⟨hmax.1, hend.1, hmax.2.1, hend.2.1, hmax.2.2, hend.2.2, ?_⟩
  have hR0 : 0 ≤ Shao.truncationBudget ν0 n x := Shao.truncationBudget_nonneg ν0 n h2 x
  have hw : 0 ≤ w := mul_nonneg hR0 (Shao.standardNormalTail_basic.2.2.1 x).1.le
  by_cases hy2 : 2 ≤ y
  · rcases HGy y hy2 hnear with
      ⟨hγ, hΛ, hψ, hψb, hψ0, hD, hD0, hE, hearly, hbad, hmacro, hshort,
        hmicro, hlate, hsum, hmax0, hmax1, hend0, hend1, hid, hcmp, hpay, htransfer⟩
    rw [hJmax, hJend]
    calc
      _ ≤ (20 * Real.exp 2 * Cg / epsilon ^ 2) *
          Shao.truncationBudget ν0 n x * Shao.standardNormalTail x := hpay
      _ = (20 * Real.exp 2 * Cg / epsilon ^ 2) * w := by dsimp [w]; ring
      _ ≤ Cs * w := mul_le_mul_of_nonneg_right (le_max_right _ _) hw
  · have hy : 0 ≤ y :=
      ((Shao.sourceTruncation_gamma_bounds ν0 n h2 hn hm x epsilon hx he he2 hR).2.1.le).trans hgy
    have hy2' : y ≤ 2 := le_of_lt (lt_of_not_ge hy2)
    let ψ : ℝ × ℝ → ℝ := fun p => ∫ z : ℝ × ℝ,
      sourceFourierTest y (p.1 + z.1, p.2 + z.2) ∂noise
    have hψ : Measurable ψ := fy_noise_measurable noise y
    have hLaw (j : Fin n) : IdentDistrib (fun a : Shao.Path n => a j)
        (id : ℝ → ℝ) P ρ := by
      refine ⟨(measurable_pi_apply j).aemeasurable, aemeasurable_id, ?_⟩
      simpa only [Measure.map_id] using
        (measurePreserving_eval (fun _ : Fin n => ρ) j).map_eq
    have hInd := iIndepFun_pi (fun _ : Fin n => (aemeasurable_id :
      AEMeasurable (id : ℝ → ℝ) ρ))
    have heq := ((iid_lindley_energy_identDistrib_maxWithZero
      (fun j : Fin n => measurable_pi_apply j) hInd hLaw).comp hψ).integral_eq
    change (∫ a : Shao.Path n, ψ (Shao.lindleyState a n le_rfl, Shao.energy a) ∂P) =
      ∫ a : Shao.Path n, ψ (Shao.maxWithZero a, Shao.energy a) ∂P at heq
    have hb := (HB ν0 hp n h2 hn hm x epsilon hx he heBounded hR y hgy hy2').2.2.2
    change |(∫ a : Shao.Path n, ψ (Shao.lindleyState a n le_rfl, Shao.energy a) ∂P) -
      (∫ a : Shao.Path n, ψ (Shao.prefixSum a n, Shao.energy a) ∂P)| ≤
        Cb * ((n : ℝ) * |∫ a : ℝ, a ∂ρ| + (n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂ρ)) at hb
    rw [heq] at hb
    change |Jmax - Jend| ≤
      Cb * ((n : ℝ) * |∫ a : ℝ, a ∂ρ| + (n : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂ρ)) at hb
    have hmoment := fy_moment_payment ν0 n h2 hn hm x epsilon hx he he2 hR
    have hnear' : |y - x| ≤ 1 / (1 + x) :=
      hnear.trans (by apply one_div_le_one_div_of_le (by positivity); linarith)
    have htail : Shao.standardNormalTail 2 ≤ Real.exp 2 * Shao.standardNormalTail x :=
      (Shao.standardNormalTail_basic.1 hy2').trans
        (Shao.standardNormalTail_local_comparison x y hx hy hnear').2
    have hRpay : Shao.truncationBudget ν0 n x ≤
        (Real.exp 2 / Shao.standardNormalTail 2) * w := by
      calc
        _ = Shao.truncationBudget ν0 n x * Shao.standardNormalTail 2 /
            Shao.standardNormalTail 2 := by field_simp
        _ ≤ Shao.truncationBudget ν0 n x *
            (Real.exp 2 * Shao.standardNormalTail x) / Shao.standardNormalTail 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htail hR0) ht2.le
        _ = _ := by dsimp [w]; ring
    calc
      |Jmax - Jend| ≤ Cb * (4 * Shao.truncationBudget ν0 n x / epsilon ^ 2) :=
        hb.trans (mul_le_mul_of_nonneg_left hmoment hCb.le)
      _ = (4 * Cb / epsilon ^ 2) * Shao.truncationBudget ν0 n x := by ring
      _ ≤ (4 * Cb / epsilon ^ 2) * ((Real.exp 2 / Shao.standardNormalTail 2) * w) :=
        mul_le_mul_of_nonneg_left hRpay (by positivity)
      _ = (4 * Real.exp 2 * Cb / (epsilon ^ 2 * Shao.standardNormalTail 2)) * w := by ring
      _ ≤ (20 * Real.exp 2 * Cb / (epsilon ^ 2 * Shao.standardNormalTail 2)) * w := by
        apply mul_le_mul_of_nonneg_right _ hw
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [mul_pos (Real.exp_pos 2) hCb]
      _ ≤ Cs * w := mul_le_mul_of_nonneg_right (le_max_left _ _) hw

end Shao.Probability
