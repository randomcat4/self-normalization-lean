import Shao.Probability.SourceKernelAmplitudeFamily
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Actual outside-v marked Fourier estimates for the accepted source cutoff.

The exact source amplitude uses k=0 or2 and the full closed signed range
|theta|≤1/16. A compact joint family and the actual recursion ∂r(F/phi')
pay nonstationary integration by parts 32 times. For small y|u|, genuine
parameter differentiation under the integral and the mean value theorem
retain the sine factor; for large y|u| use its two true complex exponentials.
Continuity of the actual integrals pays measurability. The final real tails
give exponents31/30 and include y=0 and u=0.

Source supplement LF2402–2424,2571–2582,3252–3266. Actual Region3/5 scale
adapters, whole-u integration by parts, inversion, probability contributions
and C1/C2 remain separate open obligations. -/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory
open scoped ContDiff Topology

private abbrev MarkedParameters := ℝ × ℝ × ℝ

private noncomputable def markedRDirection : MarkedParameters := (0, 0, 1)

private lemma markedQuotient_tsupport (F q : MarkedParameters → ℝ) :
    tsupport (fun p => F p / q p) ⊆ tsupport F := by
  apply closure_mono
  intro p hp hF
  exact hp (by simp [hF])

private lemma markedQuotient_contDiff (F q : MarkedParameters → ℝ)
    (hF : ContDiff ℝ ∞ F)
    (hq : ∀ p ∈ tsupport F, ContDiffAt ℝ ∞ q p ∧ q p ≠ 0) :
    ContDiff ℝ ∞ (fun p => F p / q p) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ tsupport F
  · exact hF.contDiffAt.div (hq p hp).1 (hq p hp).2
  · have he : F =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp hp
    have hz : ContDiffAt ℝ ∞ (fun _ : MarkedParameters => (0 : ℝ)) p := contDiffAt_const
    apply hz.congr_of_eventuallyEq
    filter_upwards [he] with z hz
    simp only [Pi.zero_apply] at hz ⊢
    simp [hz]

private noncomputable def markedIBPAmplitude (F q : MarkedParameters → ℝ) :
    ℕ → MarkedParameters → ℝ
  | 0 => F
  | n + 1 => fun p => fderiv ℝ
      (fun z => markedIBPAmplitude F q n z / q z) p markedRDirection

private lemma markedIBPAmplitude_regular (F q : MarkedParameters → ℝ)
    (hF : ContDiff ℝ ∞ F)
    (hq : ∀ p ∈ tsupport F, ContDiffAt ℝ ∞ q p ∧ q p ≠ 0) (n : ℕ) :
    ContDiff ℝ ∞ (markedIBPAmplitude F q n) ∧
      tsupport (markedIBPAmplitude F q n) ⊆ tsupport F := by
  induction n with
  | zero => exact ⟨hF, fun _ h => h⟩
  | succ n ih =>
    have hd := markedQuotient_contDiff (markedIBPAmplitude F q n) q ih.1
      (fun p hp => hq p (ih.2 hp))
    refine ⟨(hd.fderiv_right (by simp)).clm_apply contDiff_const, ?_⟩
    exact (tsupport_fderiv_apply_subset ℝ markedRDirection).trans
      ((markedQuotient_tsupport _ q).trans ih.2)

private lemma markedIBPAmplitude_compact (F q : MarkedParameters → ℝ)
    (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hq : ∀ p ∈ tsupport F, ContDiffAt ℝ ∞ q p ∧ q p ≠ 0) (n : ℕ) :
    HasCompactSupport (markedIBPAmplitude F q n) :=
  hFc.of_isClosed_subset (isClosed_tsupport _)
    (markedIBPAmplitude_regular F q hF hq n).2

private lemma markedIBPAmplitude_uniform_bound (F q : MarkedParameters → ℝ)
    (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hq : ∀ p ∈ tsupport F, ContDiffAt ℝ ∞ q p ∧ q p ≠ 0) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p, |markedIBPAmplitude F q n p| ≤ M := by
  obtain ⟨M, hM⟩ := Continuous.bounded_above_of_compact_support
    (markedIBPAmplitude_regular F q hF hq n).1.continuous
    (markedIBPAmplitude_compact F q hF hFc hq n)
  refine ⟨max 0 M, le_max_left _ _, fun p => ?_⟩
  calc
    _ ≤ M := by simpa only [Real.norm_eq_abs] using hM p
    _ ≤ max 0 M := le_max_right _ _

private lemma markedSlice_contDiff (F : MarkedParameters → ℝ)
    (hF : ContDiff ℝ ∞ F) (s theta : ℝ) :
    ContDiff ℝ ∞ (fun r => F (s, theta, r)) :=
  hF.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))

private lemma markedSlice_mem (F : MarkedParameters → ℝ) (s theta r : ℝ)
    (hr : r ∈ tsupport (fun r => F (s, theta, r))) :
    (s, theta, r) ∈ tsupport F :=
  tsupport_comp_subset_preimage F
    (continuous_const.prodMk (continuous_const.prodMk continuous_id)) hr

private lemma markedSlice_hasDerivAt (F : MarkedParameters → ℝ)
    (hF : ContDiff ℝ ∞ F) (s theta r : ℝ) :
    HasDerivAt (fun r => F (s, theta, r))
      (fderiv ℝ F (s, theta, r) markedRDirection) r := by
  have he : HasDerivAt (fun r : ℝ => ((s, theta, r) : MarkedParameters))
      markedRDirection r := by
    simpa [markedRDirection] using
      (hasDerivAt_const r s).prodMk ((hasDerivAt_const r theta).prodMk (hasDerivAt_id r))
  exact (hF.differentiable (by simp) (s, theta, r)).hasFDerivAt.comp_hasDerivAt r he

private lemma markedSlice_support (F : MarkedParameters → ℝ) (a b : ℝ)
    (hF : ∀ p ∈ tsupport F, p.2.2 ∈ Set.Icc a b) (s theta : ℝ) :
    tsupport (fun r => F (s, theta, r)) ⊆ Set.Icc a b := by
  apply closure_minimal
  · intro r hr
    exact hF (s, theta, r) (subset_tsupport _ hr)
  · exact isClosed_Icc

private lemma markedSlice_compact (F : MarkedParameters → ℝ) (a b : ℝ)
    (hF : ∀ p ∈ tsupport F, p.2.2 ∈ Set.Icc a b) (s theta : ℝ) :
    HasCompactSupport (fun r => F (s, theta, r)) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (markedSlice_support F a b hF s theta)

private noncomputable def markedPhase (phi : ℝ → ℝ) (v r : ℝ) : ℂ :=
  Complex.exp (((v * phi r : ℝ) : ℂ) * Complex.I)

private lemma markedPhase_norm (phi : ℝ → ℝ) (v r : ℝ) :
    ‖markedPhase phi v r‖ = 1 := by
  simp [markedPhase, Complex.norm_exp, Complex.mul_re]

private lemma markedPhase_continuous (phi : ℝ → ℝ) (hphi : Continuous phi) (v : ℝ) :
    Continuous (markedPhase phi v) := by
  unfold markedPhase
  fun_prop

private lemma markedPhase_hasDerivAt (phi : ℝ → ℝ) (v q r : ℝ)
    (hphi : HasDerivAt phi q r) :
    HasDerivAt (markedPhase phi v)
      (((v * q : ℝ) : ℂ) * Complex.I * markedPhase phi v r) r := by
  unfold markedPhase
  simpa only [mul_comm] using
    (((hphi.const_mul v).ofReal_comp.mul_const Complex.I).cexp)

private lemma markedOscillatory_integrable (f phi : ℝ → ℝ)
    (hf : Continuous f) (hfc : HasCompactSupport f) (hphi : Continuous phi) (v : ℝ) :
    Integrable (fun r => (f r : ℂ) * markedPhase phi v r) := by
  have hcf : Continuous (fun r => (f r : ℂ)) := Complex.continuous_ofReal.comp hf
  have hcs : HasCompactSupport (fun r => (f r : ℂ)) :=
    hfc.comp_left (g := Complex.ofReal) rfl
  exact (hcf.mul (markedPhase_continuous phi hphi v)).integrable_of_hasCompactSupport
    hcs.mul_right

private lemma markedOscillatory_norm_bound (f phi : ℝ → ℝ) (v M : ℝ)
    (hM : 0 ≤ M) (hb : ∀ r, |f r| ≤ M)
    (hsupp : tsupport f ⊆ Set.Icc (1 / 16 : ℝ) 4) :
    ‖∫ r : ℝ, (f r : ℂ) * markedPhase phi v r‖ ≤ 4 * M := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Set.Icc (1 / 16 : ℝ) 4) (fun r hr => ?_)]
  · calc
      _ ≤ M * (volume.real (Set.Icc (1 / 16 : ℝ) 4)) :=
        norm_setIntegral_le_of_norm_le_const (by simp) (fun r _ => by
          simpa only [norm_mul, markedPhase_norm, mul_one, Complex.norm_real,
            Real.norm_eq_abs] using hb r)
      _ ≤ 4 * M := by
        have hv : volume.real (Set.Icc (1 / 16 : ℝ) 4) = 63 / 16 := by
          simp [Measure.real, Real.volume_Icc]
          norm_num
        rw [hv]
        nlinarith
  · have hf : f r = 0 := image_eq_zero_of_notMem_tsupport (fun h => hr (hsupp h))
    simp [hf]

private lemma markedOscillatory_ibp (f q phi : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ (fun r => f r / q r))
    (hq : ∀ r ∈ tsupport f, q r ≠ 0)
    (hphi : Continuous phi) (hphid : ∀ r ∈ tsupport f, HasDerivAt phi (q r) r)
    (v : ℝ) :
    ((v : ℂ) * Complex.I) * (∫ r : ℝ, (f r : ℂ) * markedPhase phi v r) =
      -(∫ r : ℝ, ((deriv (fun z => f z / q z) r : ℝ) : ℂ) * markedPhase phi v r) := by
  let g : ℝ → ℝ := fun r => f r / q r
  have hgs : tsupport g ⊆ tsupport f := by
    apply closure_mono
    intro r hr hzero
    exact hr (by simp [g, hzero])
  have hgc : HasCompactSupport g := hfc.of_isClosed_subset (isClosed_tsupport _) hgs
  have hcast : tsupport (fun r => (g r : ℂ)) ⊆ tsupport g :=
    tsupport_comp_subset (g := Complex.ofReal) rfl g
  have hgd : Continuous (deriv g) :=
    (hg.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).continuous_deriv (by simp)
  have hgdC : HasCompactSupport (deriv g) := hgc.deriv
  have hmul (r : ℝ) : g r * q r = f r := by
    by_cases hr : r ∈ tsupport f
    · exact div_mul_cancel₀ (f r) (hq r hr)
    · simp [g, image_eq_zero_of_notMem_tsupport hr]
  have he (r : ℝ) : (g r : ℂ) *
      ((((v * q r : ℝ) : ℂ) * Complex.I) * markedPhase phi v r) =
      ((v : ℂ) * Complex.I) * ((f r : ℂ) * markedPhase phi v r) := by
    rw [← hmul r]
    push_cast
    ring
  have hi := markedOscillatory_integrable f phi hf.continuous hfc hphi v
  have hib := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun r : ℝ => (g r : ℂ))
    (u' := fun r : ℝ => ((deriv g r : ℝ) : ℂ))
    (v := markedPhase phi v)
    (v' := fun r => (((v * q r : ℝ) : ℂ) * Complex.I) * markedPhase phi v r)
    (fun r _ => ((hg.differentiable (by simp) r).hasDerivAt).ofReal_comp)
    (fun r hr => markedPhase_hasDerivAt phi v (q r) r (hphid r (hgs (hcast hr))))
    (by
      change Integrable (fun r => (g r : ℂ) *
        ((((v * q r : ℝ) : ℂ) * Complex.I) * markedPhase phi v r))
      simp_rw [he]
      exact hi.const_mul _)
    (markedOscillatory_integrable (deriv g) phi hgd hgdC hphi v)
    (markedOscillatory_integrable g phi hg.continuous hgc hphi v)
  simpa only [Pi.mul_apply, he, integral_const_mul] using hib

private lemma markedOscillatory_recursion (F q : MarkedParameters → ℝ)
    (hF : ContDiff ℝ ∞ F) (_hFc : HasCompactSupport F)
    (hq : ∀ p ∈ tsupport F, ContDiffAt ℝ ∞ q p ∧ q p ≠ 0)
    (hsupp : ∀ p ∈ tsupport F, p.2.2 ∈ Set.Icc (1 / 16 : ℝ) 4)
    (s theta : ℝ) (phi : ℝ → ℝ) (hphi : Continuous phi)
    (hphid : ∀ r, (s, theta, r) ∈ tsupport F → HasDerivAt phi (q (s, theta, r)) r)
    (v : ℝ) (n : ℕ) :
    |v| * ‖∫ r : ℝ, (markedIBPAmplitude F q n (s, theta, r) : ℂ) *
        markedPhase phi v r‖ =
      ‖∫ r : ℝ, (markedIBPAmplitude F q (n + 1) (s, theta, r) : ℂ) *
        markedPhase phi v r‖ := by
  have hn := markedIBPAmplitude_regular F q hF hq n
  have hqn := markedQuotient_contDiff (markedIBPAmplitude F q n) q hn.1
    (fun p hp => hq p (hn.2 hp))
  have hsn : ∀ p ∈ tsupport (markedIBPAmplitude F q n),
      p.2.2 ∈ Set.Icc (1 / 16 : ℝ) 4 := fun p hp => hsupp p (hn.2 hp)
  have hd : deriv (fun r => markedIBPAmplitude F q n (s, theta, r) / q (s, theta, r)) =
      fun r => markedIBPAmplitude F q (n + 1) (s, theta, r) := by
    funext r
    exact (markedSlice_hasDerivAt (fun p => markedIBPAmplitude F q n p / q p)
      hqn s theta r).deriv
  have hi := markedOscillatory_ibp (fun r => markedIBPAmplitude F q n (s, theta, r))
    (fun r => q (s, theta, r)) phi (markedSlice_contDiff _ hn.1 s theta)
    (markedSlice_compact _ _ _ hsn s theta) (markedSlice_contDiff _ hqn s theta)
    (fun r hr => (hq _ (hn.2 (markedSlice_mem _ s theta r hr))).2) hphi
    (fun r hr => hphid r (hn.2 (markedSlice_mem _ s theta r hr))) v
  rw [hd] at hi
  have hh := congrArg norm hi
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    mul_one, norm_neg] using hh

private lemma markedOscillatory_power_decay (F q : MarkedParameters → ℝ)
    (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hq : ∀ p ∈ tsupport F, ContDiffAt ℝ ∞ q p ∧ q p ≠ 0)
    (hsupp : ∀ p ∈ tsupport F, p.2.2 ∈ Set.Icc (1 / 16 : ℝ) 4)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s theta : ℝ) (phi : ℝ → ℝ), Continuous phi →
      (∀ r, (s, theta, r) ∈ tsupport F → HasDerivAt phi (q (s, theta, r)) r) →
      ∀ v : ℝ, |v| ^ n * ‖∫ r : ℝ, (F (s, theta, r) : ℂ) *
        markedPhase phi v r‖ ≤ C := by
  obtain ⟨M, hM, hMb⟩ := markedIBPAmplitude_uniform_bound F q hF hFc hq n
  refine ⟨4 * M, by positivity, fun s theta phi hphi hphid v => ?_⟩
  have he (j : ℕ) : |v| ^ j * ‖∫ r : ℝ, (F (s, theta, r) : ℂ) *
      markedPhase phi v r‖ =
      ‖∫ r : ℝ, (markedIBPAmplitude F q j (s, theta, r) : ℂ) *
        markedPhase phi v r‖ := by
    induction j with
    | zero => simp [markedIBPAmplitude]
    | succ j ih =>
      rw [pow_succ, mul_comm (|v| ^ j), mul_assoc, ih]
      exact markedOscillatory_recursion F q hF hFc hq hsupp s theta phi hphi hphid v j
  rw [he n]
  exact markedOscillatory_norm_bound _ phi v M hM (fun r => hMb (s, theta, r))
    (markedSlice_support _ _ _
      (fun p hp => hsupp p ((markedIBPAmplitude_regular F q hF hq n).2 hp)) s theta)

private noncomputable def outsideParameterBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 16, 1 / 8, by norm_num, by norm_num⟩

private noncomputable def outsideParameterBox : Set MarkedParameters :=
  Set.Icc (-1 / 8 : ℝ) (1 / 8) ×ˢ
    (Set.Icc (-1 / 8 : ℝ) (1 / 8) ×ˢ Set.Icc (1 / 16 : ℝ) 4)

private noncomputable def outsideNumerator (p : MarkedParameters) : ℝ :=
  outsideParameterBump p.1 * outsideParameterBump p.2.1 * sourceKernelCutoff p.2.2

private noncomputable def outsideInitialAmplitude (k : ℕ) (p : MarkedParameters) : ℝ :=
  outsideNumerator p / (Real.sqrt p.2.2 + p.2.1) ^ k

private noncomputable def outsidePhaseDerivative (p : MarkedParameters) : ℝ :=
  p.1 / (2 * Real.sqrt p.2.2) - 1

private lemma outsideParameterBump_abs (s : ℝ)
    (hs : s ∈ tsupport (outsideParameterBump : ℝ → ℝ)) :
    |s| ≤ (1 / 8 : ℝ) := by
  rw [outsideParameterBump.tsupport_eq] at hs
  simpa [outsideParameterBump, Real.dist_eq] using hs

private lemma outsideParameterBump_one (s : ℝ) (hs : |s| ≤ (1 / 16 : ℝ)) :
    outsideParameterBump s = 1 := by
  apply outsideParameterBump.one_of_mem_closedBall
  simpa [outsideParameterBump, Real.dist_eq] using hs

private lemma outsideNumerator_support : tsupport outsideNumerator ⊆ outsideParameterBox := by
  apply closure_minimal
  · intro p hp
    have hn : outsideParameterBump p.1 * outsideParameterBump p.2.1 *
        sourceKernelCutoff p.2.2 ≠ 0 := hp
    have hsp := left_ne_zero_of_mul hn
    have hs := abs_le.mp (outsideParameterBump_abs p.1
      (subset_tsupport _ (left_ne_zero_of_mul hsp)))
    have ht := abs_le.mp (outsideParameterBump_abs p.2.1
      (subset_tsupport _ (right_ne_zero_of_mul hsp)))
    have hr := sourceKernelCutoff_data.2.2.2.2
      (subset_tsupport _ (right_ne_zero_of_mul hn))
    exact ⟨⟨by linarith [hs.1], hs.2⟩, ⟨by linarith [ht.1], ht.2⟩, hr.1.le, hr.2.le⟩
  · exact isClosed_Icc.prod (isClosed_Icc.prod isClosed_Icc)

private lemma outsideBox_sqrt (p : MarkedParameters) (hp : p ∈ outsideParameterBox) :
    (1 / 4 : ℝ) ≤ Real.sqrt p.2.2 := by
  have hr := hp.2.2.1
  have hsq := Real.sq_sqrt (show 0 ≤ p.2.2 by linarith)
  have hn := Real.sqrt_nonneg p.2.2
  nlinarith

private lemma outsideInitialAmplitude_regular (k : ℕ) :
    ContDiff ℝ ∞ (outsideInitialAmplitude k) ∧
      tsupport (outsideInitialAmplitude k) ⊆ outsideParameterBox := by
  have hn : ContDiff ℝ ∞ outsideNumerator :=
    ((outsideParameterBump.contDiff.comp contDiff_fst).mul
      (outsideParameterBump.contDiff.comp (contDiff_fst.comp contDiff_snd))).mul
      (sourceKernelCutoff_data.1.comp (contDiff_snd.comp contDiff_snd))
  refine ⟨markedQuotient_contDiff outsideNumerator
    (fun p => (Real.sqrt p.2.2 + p.2.1) ^ k) hn (fun p hp => ?_),
    (markedQuotient_tsupport _ _).trans outsideNumerator_support⟩
  have hb := outsideNumerator_support hp
  have hr : p.2.2 ≠ 0 := by linarith [hb.2.2.1]
  have hs : ContDiffAt ℝ ∞ (fun p : MarkedParameters => Real.sqrt p.2.2 + p.2.1) p :=
    (((contDiffAt_snd.comp p contDiffAt_snd).sqrt hr).add
      (contDiffAt_fst.comp p contDiffAt_snd))
  exact ⟨hs.pow k, pow_ne_zero k (ne_of_gt (by
    have h := outsideBox_sqrt p hb
    linarith [hb.2.1.1]))⟩

private lemma outsidePhaseDerivative_regular (p : MarkedParameters)
    (hp : p ∈ outsideParameterBox) :
    ContDiffAt ℝ ∞ outsidePhaseDerivative p ∧ outsidePhaseDerivative p ≠ 0 := by
  have hs := outsideBox_sqrt p hp
  have hr : p.2.2 ≠ 0 := by linarith [hp.2.2.1]
  have hd : ContDiffAt ℝ ∞ (fun p : MarkedParameters => 2 * Real.sqrt p.2.2) p :=
    contDiffAt_const.mul ((contDiffAt_snd.comp p contDiffAt_snd).sqrt hr)
  refine ⟨(contDiffAt_fst.div hd (by linarith)).sub contDiffAt_const, ?_⟩
  apply ne_of_lt
  change p.1 / (2 * Real.sqrt p.2.2) - 1 < 0
  exact sub_neg.mpr ((div_lt_one (by linarith)).mpr (by linarith [hp.1.2]))

private lemma outsideInitialAmplitude_slice (k : ℕ) (s theta : ℝ)
    (hs : |s| ≤ (1 / 16 : ℝ)) (ht : |theta| ≤ (1 / 16 : ℝ)) :
    (fun r : ℝ => outsideInitialAmplitude k (s, theta, r)) =
      (fun r : ℝ => sourceKernelCutoff r / (Real.sqrt r + theta) ^ k) := by
  funext r
  simp [outsideInitialAmplitude, outsideNumerator,
    outsideParameterBump_one s hs, outsideParameterBump_one theta ht]

private lemma outsideActual_phase_power_decay (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (theta s : ℝ), |theta| ≤ (1 / 16 : ℝ) →
      |s| ≤ (1 / 16 : ℝ) → ∀ v : ℝ,
        |v| ^ 32 * ‖∫ r : ℝ,
          ((sourceKernelCutoff r / (Real.sqrt r + theta) ^ k : ℝ) : ℂ) *
          Complex.exp (((v * (s * Real.sqrt r - r) : ℝ) : ℂ) * Complex.I)‖ ≤ C := by
  have hF := outsideInitialAmplitude_regular k
  have hc : HasCompactSupport (outsideInitialAmplitude k) :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset
      (isClosed_tsupport _) hF.2
  obtain ⟨C, hC, hb⟩ := markedOscillatory_power_decay (outsideInitialAmplitude k)
    outsidePhaseDerivative hF.1 hc
    (fun p hp => outsidePhaseDerivative_regular p (hF.2 hp))
    (fun _ hp => (hF.2 hp).2.2) 32
  refine ⟨C, hC, fun theta s ht hs v => ?_⟩
  have hd : ∀ r, (s, theta, r) ∈ tsupport (outsideInitialAmplitude k) →
      HasDerivAt (fun r => s * Real.sqrt r - r) (outsidePhaseDerivative (s, theta, r)) r := by
    intro r hr
    have hr' := (hF.2 hr).2.2.1
    convert ((Real.hasDerivAt_sqrt (show r ≠ 0 by linarith)).const_mul s).fun_sub
      (hasDerivAt_id r) using 1 <;> simp [outsidePhaseDerivative, div_eq_mul_inv]
  have h := hb s theta (fun r => s * Real.sqrt r - r) (by fun_prop) hd v
  have he := congrFun (outsideInitialAmplitude_slice k s theta hs ht)
  simpa only [he, markedPhase] using h

private lemma outsideScaledParameter (aStar y u v : ℝ)
    (ha : 0 < aStar) (hy : 0 ≤ y) (hsmall : aStar * y ≤ (1 / 16 : ℝ))
    (hv : |u| / aStar < |v|) :
    v ≠ 0 ∧ |u * y / v| ≤ (1 / 16 : ℝ) := by
  have hvp : 0 < |v| := lt_of_le_of_lt (div_nonneg (abs_nonneg _) ha.le) hv
  have hvc : v ≠ 0 := abs_pos.mp hvp
  refine ⟨hvc, ?_⟩
  rw [abs_div, abs_mul, abs_of_nonneg hy, div_le_iff₀ hvp]
  have hu : |u| ≤ aStar * |v| := by
    have h := (div_lt_iff₀ ha).mp hv
    nlinarith
  have h1 := mul_le_mul_of_nonneg_right hu hy
  have h2 := mul_le_mul_of_nonneg_right hsmall (abs_nonneg v)
  nlinarith

private lemma outsideActual_exponential_pointwise :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, (k = 0 ∨ k = 2) →
      ∀ theta : ℝ, |theta| ≤ (1 / 16 : ℝ) → ∀ aStar y u v : ℝ,
        0 < aStar → 0 ≤ y → aStar * y ≤ (1 / 16 : ℝ) →
          |u| / aStar < |v| →
        (1 + |v|) ^ 32 * ‖∫ r : ℝ,
          ((sourceKernelCutoff r / (Real.sqrt r + theta) ^ k : ℝ) : ℂ) *
          Complex.exp ((((u * y * Real.sqrt r - v * r : ℝ) : ℂ)) * Complex.I)‖ ≤ C := by
  obtain ⟨M, hM, hMb⟩ := sourceKernel_marked_amplitude_family
  obtain ⟨C0, hC0, hb0⟩ := outsideActual_phase_power_decay 0
  obtain ⟨C2, hC2, hb2⟩ := outsideActual_phase_power_decay 2
  let D : ℝ := max (4 * M) (max C0 C2)
  refine ⟨2 ^ 32 * D + 1, by dsimp [D]; positivity, ?_⟩
  intro k hk theta ht aStar y u v ha hy hsmall hv
  let a : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + theta) ^ k
  let B : ℂ := ∫ r : ℝ, (a r : ℂ) *
    Complex.exp ((((u * y * Real.sqrt r - v * r : ℝ) : ℂ)) * Complex.I)
  have hB : ‖B‖ ≤ 4 * M := by
    have h := markedOscillatory_norm_bound a
      (fun r => u * y * Real.sqrt r - v * r) 1 M hM.le
      ((hMb k hk theta ht).2.2 0 (by norm_num)) (hMb k hk theta ht).2.1
    simpa only [iteratedDeriv_zero, markedPhase, one_mul] using h
  have hvt := outsideScaledParameter aStar y u v ha hy hsmall hv
  have hp (r : ℝ) : v * ((u * y / v) * Real.sqrt r - r) =
      u * y * Real.sqrt r - v * r := by
    field_simp [hvt.1]
  have hpower : |v| ^ 32 * ‖B‖ ≤ max C0 C2 := by
    rcases hk with rfl | rfl
    · have h := hb0 theta (u * y / v) ht hvt.2 v
      simpa only [hp] using h.trans (le_max_left C0 C2)
    · have h := hb2 theta (u * y / v) ht hvt.2 v
      simpa only [hp] using h.trans (le_max_right C0 C2)
  change (1 + |v|) ^ 32 * ‖B‖ ≤ _
  have hD0 : 0 ≤ D := le_trans (by positivity : 0 ≤ 4 * M) (le_max_left _ _)
  by_cases hv1 : |v| ≤ 1
  · have hp32 : (1 + |v|) ^ 32 ≤ 2 ^ 32 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 32
    calc
      _ ≤ 2 ^ 32 * (4 * M) := mul_le_mul hp32 hB (norm_nonneg _) (by positivity)
      _ ≤ 2 ^ 32 * D := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      _ ≤ _ := by linarith
  · have hp32 : (1 + |v|) ^ 32 ≤ 2 ^ 32 * |v| ^ 32 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) 32
    calc
      _ ≤ (2 ^ 32 * |v| ^ 32) * ‖B‖ := mul_le_mul_of_nonneg_right hp32 (norm_nonneg _)
      _ = 2 ^ 32 * (|v| ^ 32 * ‖B‖) := by ring
      _ ≤ 2 ^ 32 * max C0 C2 := mul_le_mul_of_nonneg_left hpower (by positivity)
      _ ≤ 2 ^ 32 * D := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      _ ≤ _ := by linarith

private lemma markedOscillatory_fourier_decay (F : MarkedParameters → ℝ)
    (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hsupp : ∀ p ∈ tsupport F, p.2.2 ∈ Set.Icc (1 / 16 : ℝ) 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ s theta v : ℝ,
      (1 + |v|) ^ 32 * ‖∫ r : ℝ, (F (s, theta, r) : ℂ) *
        Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I))‖ ≤ C := by
  have hq : ∀ p ∈ tsupport F, ContDiffAt ℝ ∞ (fun _ : MarkedParameters => (-1 : ℝ)) p ∧
      (-1 : ℝ) ≠ 0 := fun _ _ => ⟨contDiffAt_const, by norm_num⟩
  obtain ⟨C0, hC0, hb0⟩ := markedOscillatory_power_decay F (fun _ => -1) hF hFc hq hsupp 32
  obtain ⟨M, hM, hMb⟩ := markedIBPAmplitude_uniform_bound F (fun _ => -1) hF hFc hq 0
  let D : ℝ := max (4 * M) C0
  refine ⟨2 ^ 32 * D + 1, by dsimp [D]; positivity, fun s theta v => ?_⟩
  let B : ℂ := ∫ r : ℝ, (F (s, theta, r) : ℂ) * markedPhase (fun r => -r) v r
  have hBe : B = ∫ r : ℝ, (F (s, theta, r) : ℂ) *
      Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I)) := by
    dsimp [B]
    apply integral_congr_ae
    filter_upwards with r
    simp [markedPhase]
  rw [← hBe]
  have hB : ‖B‖ ≤ 4 * M := markedOscillatory_norm_bound _ _ _ M hM
    (fun r => hMb (s, theta, r)) (markedSlice_support F _ _ hsupp s theta)
  have hpower : |v| ^ 32 * ‖B‖ ≤ C0 :=
    hb0 s theta (fun r => -r) (by fun_prop) (fun r _ => (hasDerivAt_id r).neg) v
  by_cases hv1 : |v| ≤ 1
  · have hp32 : (1 + |v|) ^ 32 ≤ 2 ^ 32 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 32
    calc
      _ ≤ 2 ^ 32 * (4 * M) := mul_le_mul hp32 hB (norm_nonneg _) (by positivity)
      _ ≤ 2 ^ 32 * D := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      _ ≤ _ := by linarith
  · have hp32 : (1 + |v|) ^ 32 ≤ 2 ^ 32 * |v| ^ 32 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) 32
    calc
      _ ≤ (2 ^ 32 * |v| ^ 32) * ‖B‖ := mul_le_mul_of_nonneg_right hp32 (norm_nonneg _)
      _ = 2 ^ 32 * (|v| ^ 32 * ‖B‖) := by ring
      _ ≤ 2 ^ 32 * C0 := mul_le_mul_of_nonneg_left hpower (by positivity)
      _ ≤ 2 ^ 32 * D := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      _ ≤ _ := by linarith

private lemma markedProduct_contDiff (F g : MarkedParameters → ℝ)
    (hF : ContDiff ℝ ∞ F) (hg : ∀ p ∈ tsupport F, ContDiffAt ℝ ∞ g p) :
    ContDiff ℝ ∞ (fun p => F p * g p) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ tsupport F
  · exact hF.contDiffAt.mul (hg p hp)
  · have he : F =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp hp
    have hz : ContDiffAt ℝ ∞ (fun _ : MarkedParameters => (0 : ℝ)) p := contDiffAt_const
    apply hz.congr_of_eventuallyEq
    filter_upwards [he] with z hz
    simp only [Pi.zero_apply] at hz ⊢
    simp [hz]

private noncomputable def outsideLowBump : ContDiffBump (0 : ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

private noncomputable def outsideLowBase (k : ℕ) (p : MarkedParameters) : ℝ :=
  outsideLowBump p.1 * outsideInitialAmplitude k (0, p.2.1, p.2.2)

private lemma outsideLowBase_regular (k : ℕ) :
    ContDiff ℝ ∞ (outsideLowBase k) ∧
      tsupport (outsideLowBase k) ⊆
        Set.Icc (-2 : ℝ) 2 ×ˢ (Set.Icc (-1 / 8 : ℝ) (1 / 8) ×ˢ Set.Icc (1 / 16 : ℝ) 4) := by
  refine ⟨(outsideLowBump.contDiff.comp contDiff_fst).mul
    ((outsideInitialAmplitude_regular k).1.comp (contDiff_const.prodMk contDiff_snd)), ?_⟩
  apply closure_minimal
  · intro p hp
    have hn : outsideLowBump p.1 * outsideInitialAmplitude k (0, p.2.1, p.2.2) ≠ 0 := hp
    have hs : p.1 ∈ Metric.closedBall (0 : ℝ) 2 := by
      have h := subset_tsupport _ (left_ne_zero_of_mul hn)
      rwa [outsideLowBump.tsupport_eq] at h
    have ht := (outsideInitialAmplitude_regular k).2
      (subset_tsupport _ (right_ne_zero_of_mul hn))
    have hsa : |p.1| ≤ 2 := by simpa [Real.dist_eq] using hs
    exact ⟨abs_le.mp hsa, ht.2⟩
  · exact isClosed_Icc.prod (isClosed_Icc.prod isClosed_Icc)

private noncomputable def outsideLowCosine (k : ℕ) (p : MarkedParameters) : ℝ :=
  outsideLowBase k p * Real.cos (p.1 * Real.sqrt p.2.2)

private noncomputable def outsideLowSineDerivative (k : ℕ) (p : MarkedParameters) : ℝ :=
  outsideLowBase k p * (Real.sqrt p.2.2 * Real.cos (p.1 * Real.sqrt p.2.2))

private lemma outsideLowCosine_regular (k : ℕ) :
    ContDiff ℝ ∞ (outsideLowCosine k) ∧ HasCompactSupport (outsideLowCosine k) ∧
      (∀ p ∈ tsupport (outsideLowCosine k), p.2.2 ∈ Set.Icc (1 / 16 : ℝ) 4) := by
  have hb := outsideLowBase_regular k
  have hc : HasCompactSupport (outsideLowBase k) :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset
      (isClosed_tsupport _) hb.2
  have hs : tsupport (outsideLowCosine k) ⊆ tsupport (outsideLowBase k) :=
    tsupport_mul_subset_left
  refine ⟨markedProduct_contDiff _ _ hb.1 (fun p hp => ?_),
    hc.of_isClosed_subset (isClosed_tsupport _) hs, fun _ hp => (hb.2 (hs hp)).2.2⟩
  exact (contDiffAt_fst.mul ((contDiffAt_snd.comp p contDiffAt_snd).sqrt
    (show p.2.2 ≠ 0 by linarith [(hb.2 hp).2.2.1]))).cos

private lemma outsideLowSineDerivative_regular (k : ℕ) :
    ContDiff ℝ ∞ (outsideLowSineDerivative k) ∧ HasCompactSupport (outsideLowSineDerivative k) ∧
      (∀ p ∈ tsupport (outsideLowSineDerivative k), p.2.2 ∈ Set.Icc (1 / 16 : ℝ) 4) := by
  have hb := outsideLowBase_regular k
  have hc : HasCompactSupport (outsideLowBase k) :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset
      (isClosed_tsupport _) hb.2
  have hs : tsupport (outsideLowSineDerivative k) ⊆ tsupport (outsideLowBase k) :=
    tsupport_mul_subset_left
  refine ⟨markedProduct_contDiff _ _ hb.1 (fun p hp => ?_),
    hc.of_isClosed_subset (isClosed_tsupport _) hs, fun _ hp => (hb.2 (hs hp)).2.2⟩
  have hsq : ContDiffAt ℝ ∞ (fun p : MarkedParameters => Real.sqrt p.2.2) p :=
    (contDiffAt_snd.comp p contDiffAt_snd).sqrt
      (show p.2.2 ≠ 0 by linarith [(hb.2 hp).2.2.1])
  exact hsq.mul (contDiffAt_fst.mul hsq).cos

private lemma outsideLowBase_slice (k : ℕ) (s theta : ℝ)
    (hs : |s| ≤ 1) (ht : |theta| ≤ (1 / 16 : ℝ)) :
    (fun r => outsideLowBase k (s, theta, r)) =
      (fun r : ℝ => sourceKernelCutoff r / (Real.sqrt r + theta) ^ k) := by
  have he : outsideLowBump s = 1 := outsideLowBump.one_of_mem_closedBall
    (by simpa [outsideLowBump, Real.dist_eq] using hs)
  funext r
  simp [outsideLowBase, outsideInitialAmplitude, outsideNumerator, he,
    outsideParameterBump_one theta ht, outsideParameterBump_one 0 (by norm_num)]

private lemma outsideLowCosine_decay (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta s : ℝ, |theta| ≤ (1 / 16 : ℝ) → |s| ≤ 1 →
      ∀ v : ℝ, (1 + |v|) ^ 32 * ‖∫ r : ℝ,
        ((sourceKernelCutoff r / (Real.sqrt r + theta) ^ k *
          Real.cos (s * Real.sqrt r) : ℝ) : ℂ) * markedPhase (fun r => -r) v r‖ ≤ C := by
  have hr := outsideLowCosine_regular k
  obtain ⟨C, hC, hb⟩ := markedOscillatory_fourier_decay _ hr.1 hr.2.1 hr.2.2
  refine ⟨C, hC, fun theta s ht hs v => ?_⟩
  have he := congrFun (outsideLowBase_slice k s theta hs ht)
  simpa [outsideLowCosine, he, markedPhase] using hb s theta v

private lemma outsideLowSineDerivative_decay (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta s : ℝ, |theta| ≤ (1 / 16 : ℝ) → |s| ≤ 1 →
      ∀ v : ℝ, (1 + |v|) ^ 32 * ‖∫ r : ℝ,
        ((sourceKernelCutoff r / (Real.sqrt r + theta) ^ k *
          (Real.sqrt r * Real.cos (s * Real.sqrt r)) : ℝ) : ℂ) *
          markedPhase (fun r => -r) v r‖ ≤ C := by
  have hr := outsideLowSineDerivative_regular k
  obtain ⟨C, hC, hb⟩ := markedOscillatory_fourier_decay _ hr.1 hr.2.1 hr.2.2
  refine ⟨C, hC, fun theta s ht hs v => ?_⟩
  have he := congrFun (outsideLowBase_slice k s theta hs ht)
  simpa [outsideLowSineDerivative, he, markedPhase] using hb s theta v

private lemma markedSineIntegral_hasDerivAt (a : ℝ → ℝ) (ha : Continuous a)
    (hac : HasCompactSupport a) (v s : ℝ) :
    HasDerivAt
      (fun t : ℝ => ∫ r : ℝ, ((a r * Real.sin (t * Real.sqrt r) : ℝ) : ℂ) *
        markedPhase (fun r => -r) v r)
      (∫ r : ℝ, ((a r * (Real.sqrt r * Real.cos (s * Real.sqrt r)) : ℝ) : ℂ) *
        markedPhase (fun r => -r) v r) s := by
  let F : ℝ → ℝ → ℂ := fun t r => ((a r * Real.sin (t * Real.sqrt r) : ℝ) : ℂ) *
    markedPhase (fun r => -r) v r
  let D : ℝ → ℝ → ℂ := fun t r => ((a r *
    (Real.sqrt r * Real.cos (t * Real.sqrt r)) : ℝ) : ℂ) * markedPhase (fun r => -r) v r
  have hcont (t : ℝ) : Continuous (F t) := by
    dsimp [F]
    exact (Complex.continuous_ofReal.comp (ha.mul (by fun_prop))).mul
      (markedPhase_continuous _ (by fun_prop) v)
  have hcD (t : ℝ) : Continuous (D t) := by
    dsimp [D]
    exact (Complex.continuous_ofReal.comp (ha.mul (by fun_prop))).mul
      (markedPhase_continuous _ (by fun_prop) v)
  have hFs (t : ℝ) : HasCompactSupport (F t) := by
    have hreal : HasCompactSupport (fun r => a r * Real.sin (t * Real.sqrt r)) := hac.mul_right
    have hcast : HasCompactSupport (fun r => ((a r * Real.sin (t * Real.sqrt r) : ℝ) : ℂ)) :=
      hreal.comp_left (g := Complex.ofReal) rfl
    exact hcast.mul_right
  have hbi : Integrable (fun r => |a r * Real.sqrt r|) := by
    simpa only [Real.norm_eq_abs, Pi.mul_apply] using
      ((ha.mul Real.continuous_sqrt).integrable_of_hasCompactSupport
        (hac.mul_right (f' := Real.sqrt))).norm
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := D) (s := Set.univ) (bound := fun r => |a r * Real.sqrt r|)
    (by simp) (Filter.Eventually.of_forall fun t => (hcont t).aestronglyMeasurable)
    ((hcont s).integrable_of_hasCompactSupport (hFs s)) (hcD s).aestronglyMeasurable
    (Filter.Eventually.of_forall fun r t _ => ?_) hbi
    (Filter.Eventually.of_forall fun r t _ => ?_)).2
  · dsimp [D]
    rw [norm_mul, markedPhase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
    calc
      |a r * (Real.sqrt r * Real.cos (t * Real.sqrt r))| =
          |a r * Real.sqrt r| * |Real.cos (t * Real.sqrt r)| := by
        rw [← mul_assoc, abs_mul]
      _ ≤ |a r * Real.sqrt r| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = _ := mul_one _
  · dsimp [F, D]
    have hd : HasDerivAt (fun t : ℝ => a r * Real.sin (t * Real.sqrt r))
        (a r * (Real.sqrt r * Real.cos (t * Real.sqrt r))) t := by
      simpa only [id_eq, mul_comm, one_mul] using
        (((hasDerivAt_id t).mul_const (Real.sqrt r)).sin).const_mul (a r)
    exact hd.ofReal_comp.mul_const _

private lemma outsideActual_low_sine_pointwise (k : ℕ) (hk : k = 0 ∨ k = 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta s : ℝ, |theta| ≤ (1 / 16 : ℝ) → |s| ≤ 1 →
      ∀ v : ℝ, (1 + |v|) ^ 32 * ‖∫ r : ℝ,
        ((sourceKernelCutoff r / (Real.sqrt r + theta) ^ k *
          Real.sin (s * Real.sqrt r) : ℝ) : ℂ) *
          markedPhase (fun r => -r) v r‖ ≤ C * |s| := by
  obtain ⟨C, hC, hb⟩ := outsideLowSineDerivative_decay k
  obtain ⟨M, hM, hMb⟩ := sourceKernel_marked_amplitude_family
  refine ⟨C, hC, fun theta s ht hs v => ?_⟩
  let a : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + theta) ^ k
  have ha : Continuous a := (hMb k hk theta ht).1.continuous
  have hac : HasCompactSupport a :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hMb k hk theta ht).2.1
  let S : ℝ → ℂ := fun t => ∫ r : ℝ, ((a r * Real.sin (t * Real.sqrt r) : ℝ) : ℂ) *
    markedPhase (fun r => -r) v r
  let D : ℝ → ℂ := fun t => ∫ r : ℝ, ((a r *
    (Real.sqrt r * Real.cos (t * Real.sqrt r)) : ℝ) : ℂ) * markedPhase (fun r => -r) v r
  have hP : 0 ≤ (1 + |v|) ^ 32 := by positivity
  have hd (t : ℝ) : HasDerivAt S (D t) t := markedSineIntegral_hasDerivAt a ha hac v t
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => (((1 + |v|) ^ 32 : ℝ) : ℂ) * S t)
    (f' := fun t => (((1 + |v|) ^ 32 : ℝ) : ℂ) * D t)
    (s := Set.Icc (-1 : ℝ) 1) (C := C)
    (fun t _ => ((hd t).const_mul _).hasDerivWithinAt)
    (fun t ht' => by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hP] using
        hb theta t ht (abs_le.mpr ht') v)
    (convex_Icc (-1 : ℝ) 1) (by norm_num : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1) (abs_le.mp hs)
  change (1 + |v|) ^ 32 * ‖S s‖ ≤ C * |s|
  have hS0 : S 0 = 0 := by simp [S]
  simpa only [hS0, mul_zero, sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hP] using hm

private lemma markedModulation_integrable (a m : ℝ → ℝ)
    (ha : Continuous a) (hac : HasCompactSupport a) (hm : Continuous m) (v : ℝ) :
    Integrable (fun r => ((a r * m r : ℝ) : ℂ) * markedPhase (fun r => -r) v r) :=
  markedOscillatory_integrable _ _ (ha.mul hm) hac.mul_right (by fun_prop) v

private lemma outsideActual_low_shifted_sine_pointwise (k : ℕ) (hk : k = 0 ∨ k = 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta : ℝ, |theta| ≤ (1 / 16 : ℝ) →
      ∀ y u w v : ℝ, 0 ≤ y → |w| ≤ y / 16 → y * |u| ≤ 1 →
        (1 + |v|) ^ 32 * ‖∫ r : ℝ,
          ((sourceKernelCutoff r / (Real.sqrt r + theta) ^ k *
            Real.sin (u * (y * Real.sqrt r + w)) : ℝ) : ℂ) *
            markedPhase (fun r => -r) v r‖ ≤ C * (y * |u|) := by
  obtain ⟨Cs, hCs, hbs⟩ := outsideActual_low_sine_pointwise k hk
  obtain ⟨Cc, hCc, hbc⟩ := outsideLowCosine_decay k
  obtain ⟨M, hM, hMb⟩ := sourceKernel_marked_amplitude_family
  refine ⟨Cs + Cc + 1, by positivity, fun theta ht y u w v hy hw hsmall => ?_⟩
  let a : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + theta) ^ k
  let s : ℝ := u * y
  let L : ℝ := u * w
  let S : ℂ := ∫ r : ℝ, ((a r * Real.sin (s * Real.sqrt r) : ℝ) : ℂ) *
    markedPhase (fun r => -r) v r
  let K : ℂ := ∫ r : ℝ, ((a r * Real.cos (s * Real.sqrt r) : ℝ) : ℂ) *
    markedPhase (fun r => -r) v r
  have hs : |s| = y * |u| := by simp [s, abs_mul, abs_of_nonneg hy, mul_comm]
  have hL : |L| ≤ |s| := by
    dsimp [L]
    rw [abs_mul, hs]
    have hwy : |w| ≤ y := by linarith
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hwy (abs_nonneg u)
  have ha := (hMb k hk theta ht).1.continuous
  have hac : HasCompactSupport a :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hMb k hk theta ht).2.1
  have hSi := markedModulation_integrable a (fun r => Real.sin (s * Real.sqrt r)) ha hac (by fun_prop) v
  have hKi := markedModulation_integrable a (fun r => Real.cos (s * Real.sqrt r)) ha hac (by fun_prop) v
  have he : (∫ r : ℝ, ((a r * Real.sin (u * (y * Real.sqrt r + w)) : ℝ) : ℂ) *
      markedPhase (fun r => -r) v r) = (Real.cos L : ℂ) * S + (Real.sin L : ℂ) * K := by
    calc
      _ = ∫ r : ℝ,
          (Real.cos L : ℂ) * (((a r * Real.sin (s * Real.sqrt r) : ℝ) : ℂ) * markedPhase (fun r => -r) v r) +
          (Real.sin L : ℂ) * (((a r * Real.cos (s * Real.sqrt r) : ℝ) : ℂ) * markedPhase (fun r => -r) v r) := by
        apply integral_congr_ae
        filter_upwards with r
        have hp : u * (y * Real.sqrt r + w) = s * Real.sqrt r + L := by dsimp [s, L]; ring
        rw [hp, Real.sin_add]
        push_cast
        ring
      _ = _ := by
        rw [integral_add (hSi.const_mul _) (hKi.const_mul _), integral_const_mul, integral_const_mul]
  rw [he]
  have hnorm : ‖(Real.cos L : ℂ) * S + (Real.sin L : ℂ) * K‖ ≤ ‖S‖ + |s| * ‖K‖ := by
    calc
      _ ≤ ‖(Real.cos L : ℂ) * S‖ + ‖(Real.sin L : ℂ) * K‖ := norm_add_le _ _
      _ = |Real.cos L| * ‖S‖ + |Real.sin L| * ‖K‖ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 1 * ‖S‖ + |s| * ‖K‖ := add_le_add
        (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one L) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right
          ((show |Real.sin L| ≤ |L| from Real.abs_sin_le_abs).trans hL) (norm_nonneg _))
      _ = _ := by rw [one_mul]
  have hSB : (1 + |v|) ^ 32 * ‖S‖ ≤ Cs * |s| := hbs theta s ht (by rwa [hs]) v
  have hKB : (1 + |v|) ^ 32 * ‖K‖ ≤ Cc := hbc theta s ht (by rwa [hs]) v
  calc
    _ ≤ (1 + |v|) ^ 32 * (‖S‖ + |s| * ‖K‖) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = (1 + |v|) ^ 32 * ‖S‖ + |s| * ((1 + |v|) ^ 32 * ‖K‖) := by ring
    _ ≤ Cs * |s| + |s| * Cc := add_le_add hSB (mul_le_mul_of_nonneg_left hKB (abs_nonneg s))
    _ ≤ (Cs + Cc + 1) * (y * |u|) := by rw [← hs]; nlinarith [abs_nonneg s]

private lemma markedSine_phase_split (a u y w v r : ℝ) :
    ((a * Real.sin (u * (y * Real.sqrt r + w)) : ℝ) : ℂ) *
        markedPhase (fun r => -r) v r =
      (Complex.exp (-(((u * w : ℝ) : ℂ) * Complex.I)) *
          ((a : ℂ) * Complex.exp ((((-u * y * Real.sqrt r - v * r : ℝ) : ℂ)) * Complex.I)) -
        Complex.exp ((((u * w : ℝ) : ℂ)) * Complex.I) *
          ((a : ℂ) * Complex.exp ((((u * y * Real.sqrt r - v * r : ℝ) : ℂ)) * Complex.I))) *
        Complex.I / 2 := by
  have hp : Complex.exp ((((u * w : ℝ) : ℂ)) * Complex.I) *
      Complex.exp ((((u * y * Real.sqrt r - v * r : ℝ) : ℂ)) * Complex.I) =
      Complex.exp ((((u * (y * Real.sqrt r + w) : ℝ) : ℂ)) * Complex.I) *
        markedPhase (fun r => -r) v r := by
    unfold markedPhase
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hm : Complex.exp (-(((u * w : ℝ) : ℂ) * Complex.I)) *
      Complex.exp ((((-u * y * Real.sqrt r - v * r : ℝ) : ℂ)) * Complex.I) =
      Complex.exp (-((((u * (y * Real.sqrt r + w) : ℝ) : ℂ))) * Complex.I) *
        markedPhase (fun r => -r) v r := by
    unfold markedPhase
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [Complex.ofReal_mul, Complex.ofReal_sin, Complex.sin]
  calc
    _ = (a : ℂ) *
        (Complex.exp (-((((u * (y * Real.sqrt r + w) : ℝ) : ℂ))) * Complex.I) *
          markedPhase (fun r => -r) v r -
         Complex.exp ((((u * (y * Real.sqrt r + w) : ℝ) : ℂ)) * Complex.I) *
          markedPhase (fun r => -r) v r) * Complex.I / 2 := by ring
    _ = _ := by rw [← hp, ← hm]; ring

private lemma outsideActual_shifted_sine_coarse_pointwise :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, (k = 0 ∨ k = 2) →
      ∀ theta : ℝ, |theta| ≤ (1 / 16 : ℝ) → ∀ aStar y u w v : ℝ,
        0 < aStar → 0 ≤ y → aStar * y ≤ (1 / 16 : ℝ) →
          |u| / aStar < |v| →
        (1 + |v|) ^ 32 * ‖∫ r : ℝ,
          ((sourceKernelCutoff r / (Real.sqrt r + theta) ^ k *
            Real.sin (u * (y * Real.sqrt r + w)) : ℝ) : ℂ) *
            markedPhase (fun r => -r) v r‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := outsideActual_exponential_pointwise
  obtain ⟨M, hM, hMb⟩ := sourceKernel_marked_amplitude_family
  refine ⟨2 * C, by positivity, fun k hk theta ht aStar y u w v ha hy hsmall hv => ?_⟩
  let a : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + theta) ^ k
  let B : ℝ → ℂ := fun U => ∫ r : ℝ, (a r : ℂ) *
    Complex.exp ((((U * y * Real.sqrt r - v * r : ℝ) : ℂ)) * Complex.I)
  let ep : ℂ := Complex.exp ((((u * w : ℝ) : ℂ)) * Complex.I)
  let em : ℂ := Complex.exp (-(((u * w : ℝ) : ℂ) * Complex.I))
  have haC := (hMb k hk theta ht).1.continuous
  have hac : HasCompactSupport a :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hMb k hk theta ht).2.1
  have hBi (U : ℝ) : Integrable (fun r => (a r : ℂ) *
      Complex.exp ((((U * y * Real.sqrt r - v * r : ℝ) : ℂ)) * Complex.I)) := by
    simpa only [markedPhase, one_mul] using markedOscillatory_integrable a
      (fun r => U * y * Real.sqrt r - v * r) haC hac (by fun_prop) 1
  have he : (∫ r : ℝ,
      ((a r * Real.sin (u * (y * Real.sqrt r + w)) : ℝ) : ℂ) *
        markedPhase (fun r => -r) v r) = (em * B (-u) - ep * B u) * Complex.I / 2 := by
    simp_rw [markedSine_phase_split]
    rw [integral_div, integral_mul_const, integral_sub ((hBi (-u)).const_mul _) ((hBi u).const_mul _),
      integral_const_mul, integral_const_mul]
  rw [he]
  have hem : ‖em‖ = 1 := by simp [em, Complex.norm_exp, Complex.mul_re]
  have hep : ‖ep‖ = 1 := by simp [ep, Complex.norm_exp, Complex.mul_re]
  have hn : ‖(em * B (-u) - ep * B u) * Complex.I / 2‖ ≤ ‖B (-u)‖ + ‖B u‖ := by
    calc
      _ = ‖em * B (-u) - ep * B u‖ / 2 := by norm_num [norm_div, norm_mul]
      _ ≤ ‖em * B (-u) - ep * B u‖ := div_le_self (norm_nonneg _) (by norm_num)
      _ ≤ ‖em * B (-u)‖ + ‖ep * B u‖ := norm_sub_le _ _
      _ = _ := by rw [norm_mul, norm_mul, hem, hep, one_mul, one_mul]
  have hmB : (1 + |v|) ^ 32 * ‖B (-u)‖ ≤ C := by
    apply hb k hk theta ht aStar y (-u) v ha hy hsmall
    simpa only [abs_neg] using hv
  have hpB : (1 + |v|) ^ 32 * ‖B u‖ ≤ C := hb k hk theta ht aStar y u v ha hy hsmall hv
  calc
    _ ≤ (1 + |v|) ^ 32 * (‖B (-u)‖ + ‖B u‖) := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (1 + |v|) ^ 32 * ‖B (-u)‖ + (1 + |v|) ^ 32 * ‖B u‖ := by ring
    _ ≤ 2 * C := by linarith

private lemma outsideActual_sine_pointwise :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, (k = 0 ∨ k = 2) →
      ∀ theta : ℝ, |theta| ≤ (1 / 16 : ℝ) → ∀ aStar y u w v : ℝ,
        0 < aStar → 0 ≤ y → |w| ≤ y / 16 → aStar * y ≤ (1 / 16 : ℝ) →
          |u| / aStar < |v| →
        (1 + |v|) ^ 32 * ‖∫ r : ℝ,
          ((sourceKernelCutoff r / (Real.sqrt r + theta) ^ k *
            Real.sin (u * (y * Real.sqrt r + w)) : ℝ) : ℂ) *
            markedPhase (fun r => -r) v r‖ ≤ C * min (y * |u|) 1 := by
  obtain ⟨C0, hC0, hb0⟩ := outsideActual_low_shifted_sine_pointwise 0 (Or.inl rfl)
  obtain ⟨C2, hC2, hb2⟩ := outsideActual_low_shifted_sine_pointwise 2 (Or.inr rfl)
  obtain ⟨Ch, hCh, hbh⟩ := outsideActual_shifted_sine_coarse_pointwise
  let C : ℝ := max C0 C2 + Ch + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro k hk theta ht aStar y u w v ha hy hw hsmall hv
  by_cases hl : y * |u| ≤ 1
  · rw [min_eq_left hl]
    have hlow : (1 + |v|) ^ 32 * ‖∫ r : ℝ,
        ((sourceKernelCutoff r / (Real.sqrt r + theta) ^ k *
          Real.sin (u * (y * Real.sqrt r + w)) : ℝ) : ℂ) *
          markedPhase (fun r => -r) v r‖ ≤ max C0 C2 * (y * |u|) := by
      rcases hk with rfl | rfl
      · exact (hb0 theta ht y u w v hy hw hl).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      · exact (hb2 theta ht y u w v hy hw hl).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    exact hlow.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity))
  · rw [min_eq_right (by linarith : 1 ≤ y * |u|), mul_one]
    exact (hbh k hk theta ht aStar y u w v ha hy hsmall hv).trans
      (by dsimp [C]; linarith [le_max_left C0 C2])

private lemma markedParameterizedIntegral_continuous (a : ℝ → ℝ)
    (ha : Continuous a) (hac : HasCompactSupport a) (Phi : ℝ → ℝ → ℝ)
    (hPhi : Continuous (Function.uncurry Phi)) :
    Continuous (fun v : ℝ => ∫ r : ℝ, (a r : ℂ) * Complex.exp (((Phi v r : ℝ) : ℂ) * Complex.I)) := by
  apply continuous_of_dominated (bound := fun r => |a r|)
  · intro v
    have hp : Continuous (Phi v) := hPhi.comp (continuous_const.prodMk continuous_id)
    exact ((Complex.continuous_ofReal.comp ha).mul (by fun_prop)).aestronglyMeasurable
  · intro v
    filter_upwards with r
    simp [Complex.norm_exp, Complex.mul_re]
  · simpa only [Real.norm_eq_abs] using (ha.integrable_of_hasCompactSupport hac).norm
  · filter_upwards with r
    have hp : Continuous (fun v => Phi v r) := hPhi.comp (continuous_id.prodMk continuous_const)
    fun_prop

private lemma outsideAbsProfile_integrable (p : ℝ) (hp : p < -1) :
    Integrable (fun v : ℝ => (1 + |v|) ^ p) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := -p) (by simp; linarith)
  simpa only [neg_neg, Real.norm_eq_abs] using h

private lemma outsideAbsProfile_tail (L p : ℝ) (hL : 0 ≤ L) (hp : p < -1) :
    (∫ v in {v : ℝ | L < |v|}, (1 + |v|) ^ p) =
      2 * (-(1 + L) ^ (p + 1) / (p + 1)) := by
  have hi := outsideAbsProfile_integrable p hp
  have hset : {v : ℝ | L < |v|} = Set.Iio (-L) ∪ Set.Ioi L := by
    ext v
    rcases le_total 0 v with hv | hv
    · simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, abs_of_nonneg hv]
      constructor
      · exact Or.inr
      · rintro (h | h) <;> linarith
    · simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, abs_of_nonpos hv]
      constructor
      · intro h; exact Or.inl (by linarith)
      · rintro (h | h) <;> linarith
  have hdis : Disjoint (Set.Iio (-L)) (Set.Ioi L) := by
    apply Set.disjoint_left.mpr
    intro v hv hv'
    change v < -L at hv
    change L < v at hv'
    linarith
  rw [hset, setIntegral_union hdis measurableSet_Ioi hi.integrableOn hi.integrableOn]
  have hleft : (∫ v in Set.Iio (-L), (1 + |v|) ^ p) =
      ∫ v in Set.Ioi L, (1 + |v|) ^ p := by
    rw [← integral_Iic_eq_integral_Iio]
    simpa only [abs_neg, neg_neg] using
      integral_comp_neg_Iic (-L) (fun v : ℝ => (1 + |v|) ^ p)
  have hright : (∫ v in Set.Ioi L, (1 + |v|) ^ p) =
      -(1 + L) ^ (p + 1) / (p + 1) := by
    have he := (measurePreserving_add_left (volume : Measure ℝ) 1).setIntegral_preimage_emb
      (Homeomorph.addLeft (1 : ℝ)).measurableEmbedding (fun v : ℝ => v ^ p) (Set.Ioi (1 + L))
    have hpre : (fun v : ℝ => 1 + v) ⁻¹' Set.Ioi (1 + L) = Set.Ioi L := by
      ext v
      simp only [Set.mem_preimage, Set.mem_Ioi, add_lt_add_iff_left]
    rw [hpre] at he
    calc
      _ = ∫ v in Set.Ioi L, (1 + v) ^ p := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro v hv
        dsimp
        rw [abs_of_pos (hL.trans_lt hv)]
      _ = ∫ v in Set.Ioi (1 + L), v ^ p := he
      _ = _ := integral_Ioi_rpow_of_lt hp (by linarith)
  rw [hleft, hright]
  ring

private lemma outsidePowerProfile_integrable (n : ℕ) (hn : 1 < n) :
    Integrable (fun v : ℝ => 1 / (1 + |v|) ^ n) := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have h := outsideAbsProfile_integrable (-(n : ℝ)) (by linarith)
  have he (v : ℝ) : (1 + |v|) ^ (-(n : ℝ)) = 1 / (1 + |v|) ^ n := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, one_div]
  simpa only [he] using h

private lemma outsidePowerProfile_tail32 (L : ℝ) (hL : 0 ≤ L) :
    (∫ v in {v : ℝ | L < |v|}, 1 / (1 + |v|) ^ 32) ≤ 2 / (1 + L) ^ 31 := by
  have he (v : ℝ) : (1 + |v|) ^ (-32 : ℝ) = 1 / (1 + |v|) ^ 32 := by
    rw [show (-32 : ℝ) = -(32 : ℝ) by norm_num, Real.rpow_neg (by positivity),
      Real.rpow_ofNat, one_div]
  have hp : (1 + L) ^ (-31 : ℝ) = 1 / (1 + L) ^ 31 := by
    rw [show (-31 : ℝ) = -(31 : ℝ) by norm_num, Real.rpow_neg (by positivity),
      Real.rpow_ofNat, one_div]
  have h := outsideAbsProfile_tail L (-32) hL (by norm_num)
  norm_num only at h
  simp_rw [he] at h
  rw [h, hp]
  have hn : 0 ≤ 1 / (1 + L) ^ 31 := by positivity
  simp only [div_eq_mul_inv, one_mul] at hn ⊢
  nlinarith only [hn]

private lemma outsidePowerProfile_tail31 (L : ℝ) (hL : 0 ≤ L) :
    (∫ v in {v : ℝ | L < |v|}, 1 / (1 + |v|) ^ 31) ≤ 2 / (1 + L) ^ 30 := by
  have he (v : ℝ) : (1 + |v|) ^ (-31 : ℝ) = 1 / (1 + |v|) ^ 31 := by
    rw [show (-31 : ℝ) = -(31 : ℝ) by norm_num, Real.rpow_neg (by positivity),
      Real.rpow_ofNat, one_div]
  have hp : (1 + L) ^ (-30 : ℝ) = 1 / (1 + L) ^ 30 := by
    rw [show (-30 : ℝ) = -(30 : ℝ) by norm_num, Real.rpow_neg (by positivity),
      Real.rpow_ofNat, one_div]
  have h := outsideAbsProfile_tail L (-31) hL (by norm_num)
  norm_num only at h
  simp_rw [he] at h
  rw [h, hp]
  have hn : 0 ≤ 1 / (1 + L) ^ 30 := by positivity
  simp only [div_eq_mul_inv, one_mul] at hn ⊢
  nlinarith only [hn]

private lemma outsideProfile_integral_compare (F : ℝ → ℝ) (hF : Continuous F)
    (hF0 : ∀ v, 0 ≤ F v) (n : ℕ) (hn : 1 < n) (L D : ℝ) (_hD : 0 ≤ D)
    (hb : ∀ v, L < |v| → (1 + |v|) ^ n * F v ≤ D) :
    IntegrableOn F {v : ℝ | L < |v|} ∧
      (∫ v in {v : ℝ | L < |v|}, F v) ≤ D *
        (∫ v in {v : ℝ | L < |v|}, 1 / (1 + |v|) ^ n) := by
  let A : Set ℝ := {v : ℝ | L < |v|}
  have hA : MeasurableSet A := (isOpen_lt continuous_const continuous_abs).measurableSet
  have henv : IntegrableOn (fun v : ℝ => D * (1 / (1 + |v|) ^ n)) A :=
    ((outsidePowerProfile_integrable n hn).integrableOn).const_mul D
  have hpoint (v : ℝ) (hv : v ∈ A) : F v ≤ D * (1 / (1 + |v|) ^ n) := by
    rw [mul_one_div]
    exact (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hb v hv)
  have hi : IntegrableOn F A := henv.mono' hF.aestronglyMeasurable.restrict
    (by
      filter_upwards [ae_restrict_mem hA] with v hv
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 v)] using hpoint v hv)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ v in A, D * (1 / (1 + |v|) ^ n) := integral_mono_ae hi henv
      (by filter_upwards [ae_restrict_mem hA] with v hv using hpoint v hv)
    _ = _ := integral_const_mul _ _

private lemma outsideProfile_moments_compare (F : ℝ → ℝ) (hF : Continuous F)
    (hF0 : ∀ v, 0 ≤ F v) (L D : ℝ) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hb : ∀ v, L < |v| → (1 + |v|) ^ 32 * F v ≤ D) :
    IntegrableOn F {v : ℝ | L < |v|} ∧
      IntegrableOn (fun v => |v| * F v) {v : ℝ | L < |v|} ∧
      (∫ v in {v : ℝ | L < |v|}, F v) ≤ 2 * D / (1 + L) ^ 31 ∧
      (∫ v in {v : ℝ | L < |v|}, |v| * F v) ≤ 2 * D / (1 + L) ^ 30 := by
  have h0 := outsideProfile_integral_compare F hF hF0 32 (by norm_num) L D hD hb
  have hw (v : ℝ) (hv : L < |v|) : (1 + |v|) ^ 31 * (|v| * F v) ≤ D := by
    calc
      _ = |v| * ((1 + |v|) ^ 31 * F v) := by ring
      _ ≤ (1 + |v|) * ((1 + |v|) ^ 31 * F v) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (by positivity) (hF0 v))
      _ = (1 + |v|) ^ 32 * F v := by rw [show 32 = 31 + 1 by rfl, pow_succ]; ring
      _ ≤ D := hb v hv
  have h1 := outsideProfile_integral_compare (fun v => |v| * F v) (continuous_abs.mul hF)
    (fun v => mul_nonneg (abs_nonneg v) (hF0 v)) 31 (by norm_num) L D hD hw
  refine ⟨h0.1, h1.1, ?_, ?_⟩
  · calc
      _ ≤ D * (2 / (1 + L) ^ 31) := h0.2.trans
        (mul_le_mul_of_nonneg_left (outsidePowerProfile_tail32 L hL) hD)
      _ = _ := by ring
  · calc
      _ ≤ D * (2 / (1 + L) ^ 30) := h1.2.trans
        (mul_le_mul_of_nonneg_left (outsidePowerProfile_tail31 L hL) hD)
      _ = _ := by ring

theorem sourceKernel_marked_outside_norms :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ (1 / 16 : ℝ) ∧
      ∀ (k : ℕ), (k = 0 ∨ k = 2) →
        ∀ (theta : ℝ), |theta| ≤ (1 / 16 : ℝ) →
          ∀ (aStar y u w : ℝ),
            0 < aStar → 0 ≤ y → y ≤ 2 → aStar * y ≤ delta →
              |w| ≤ y / 16 →
              let a : ℝ → ℝ := fun r =>
                sourceKernelCutoff r / (Real.sqrt r + theta) ^ k
              let B : ℝ → ℂ := fun v =>
                ∫ r : ℝ, (a r : ℂ) *
                  Complex.exp
                    ((((u * y * Real.sqrt r - v * r : ℝ) : ℂ)) * Complex.I)
              let Bsin : ℝ → ℂ := fun v =>
                ∫ r : ℝ,
                  ((a r * Real.sin (u * (y * Real.sqrt r + w)) : ℝ) : ℂ) *
                    Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I))
              let A : Set ℝ := {v : ℝ | |u| / aStar < |v|}
              IntegrableOn (fun v : ℝ => ‖B v‖) A ∧
                IntegrableOn (fun v : ℝ => |v| * ‖B v‖) A ∧
                IntegrableOn (fun v : ℝ => ‖Bsin v‖) A ∧
                IntegrableOn (fun v : ℝ => |v| * ‖Bsin v‖) A ∧
                (∫ v in A, ‖B v‖) ≤ C / (1 + |u| / aStar) ^ 31 ∧
                (∫ v in A, |v| * ‖B v‖) ≤ C / (1 + |u| / aStar) ^ 30 ∧
                (∫ v in A, ‖Bsin v‖) ≤
                  C * min (y * |u|) 1 / (1 + |u| / aStar) ^ 31 ∧
                (∫ v in A, |v| * ‖Bsin v‖) ≤
                  C * min (y * |u|) 1 / (1 + |u| / aStar) ^ 30 := by
  obtain ⟨Ce, hCe, hbe⟩ := outsideActual_exponential_pointwise
  obtain ⟨Cs, hCs, hbs⟩ := outsideActual_sine_pointwise
  obtain ⟨M, hM, hMb⟩ := sourceKernel_marked_amplitude_family
  let C : ℝ := 2 * max Ce Cs
  refine ⟨C, 1 / 16, by dsimp [C]; positivity, by norm_num, by norm_num, ?_⟩
  intro k hk theta ht aStar y u w ha hy hy2 hsmall hw
  let a : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + theta) ^ k
  let B : ℝ → ℂ := fun v => ∫ r : ℝ, (a r : ℂ) *
    Complex.exp ((((u * y * Real.sqrt r - v * r : ℝ) : ℂ)) * Complex.I)
  let Bsin : ℝ → ℂ := fun v => ∫ r : ℝ,
    ((a r * Real.sin (u * (y * Real.sqrt r + w)) : ℝ) : ℂ) *
      Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I))
  let L : ℝ := |u| / aStar
  have hL : 0 ≤ L := div_nonneg (abs_nonneg u) ha.le
  have hm : 0 ≤ min (y * |u|) 1 := le_min (by positivity) (by norm_num)
  have haC : Continuous a := (hMb k hk theta ht).1.continuous
  have hac : HasCompactSupport a :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hMb k hk theta ht).2.1
  have hBC : Continuous B := markedParameterizedIntegral_continuous a haC hac
    (fun v r => u * y * Real.sqrt r - v * r) (by fun_prop)
  have hBsinC : Continuous Bsin := by
    have h := markedParameterizedIntegral_continuous
      (fun r => a r * Real.sin (u * (y * Real.sqrt r + w))) (haC.mul (by fun_prop))
      hac.mul_right (fun v r => -(v * r)) (by fun_prop)
    simpa only [Complex.ofReal_neg, neg_mul] using h
  have he := outsideProfile_moments_compare (fun v => ‖B v‖) hBC.norm
    (fun v => norm_nonneg (B v)) L Ce hL hCe.le
    (fun v hv => hbe k hk theta ht aStar y u v ha hy hsmall hv)
  have hs := outsideProfile_moments_compare (fun v => ‖Bsin v‖) hBsinC.norm
    (fun v => norm_nonneg (Bsin v)) L (Cs * min (y * |u|) 1) hL (mul_nonneg hCs.le hm)
    (fun v hv => by
      have h := hbs k hk theta ht aStar y u w v ha hy hw hsmall hv
      simpa [Bsin, a, markedPhase, mul_neg] using h)
  refine ⟨he.1, he.2.1, hs.1, hs.2.1, ?_, ?_, ?_, ?_⟩
  · exact he.2.2.1.trans (by dsimp [C]; gcongr; exact le_max_left Ce Cs)
  · exact he.2.2.2.trans (by dsimp [C]; gcongr; exact le_max_left Ce Cs)
  · calc
      _ ≤ 2 * (Cs * min (y * |u|) 1) / (1 + L) ^ 31 := hs.2.2.1
      _ = (2 * Cs) * min (y * |u|) 1 / (1 + L) ^ 31 := by ring
      _ ≤ _ := by dsimp [C]; gcongr; exact le_max_right Ce Cs
  · calc
      _ ≤ 2 * (Cs * min (y * |u|) 1) / (1 + L) ^ 30 := hs.2.2.2
      _ = (2 * Cs) * min (y * |u|) 1 / (1 + L) ^ 30 := by ring
      _ ≤ _ := by dsimp [C]; gcongr; exact le_max_right Ce Cs

end Shao.Probability
