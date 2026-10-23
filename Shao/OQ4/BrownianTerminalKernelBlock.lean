-- Complete LOCAL implementation of the parent-frozen10 heads and sole literal value.
-- Formal freeze SHA256 e15b865a07e8c837bb55693a7f6cf14654f40945f42bc01682e41adcebc09057.
-- Unchecked source: upstream qualification, server kernel/axiom receipt and final review pending.
import Shao.OQ4.CanonicalBrownian
import Shao.OQ4.BrownianUniformSurvival
import Shao.OQ4.BrownianTerminalSpectral
import Shao.OQ4.KilledIteration
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace Shao.OQ4.BrownianTerminalKernelBlock
open MeasureTheory ProbabilityTheory Filter Set
open RademacherScalarBounds (lambda)
open scoped NNReal Topology

-- D1 PUBLIC: the actual canonical model, instantiated in the literal all-start supremum.
def sourceSurvivalError (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (T : ℝ≥0) (h : ℝ) : ℝ :=
  BrownianUniformSurvival.survivalError CanonicalBrownian.B CanonicalBrownian.law ν T h

-- L1 PRIVATE: no interval nonemptiness is needed for this upper-bound statement.
private theorem survival_error_image_bddAbove
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (T : ℝ≥0) (h : ℝ) :
    BddAbove ((fun z : ℝ =>
      |killedMass ν h (PolygonalKilledFunctionalLimit.floorHorizon T h) z -
        BrownianUniformSurvival.brownianSurvival CanonicalBrownian.B
          CanonicalBrownian.law T (z / h)|) '' Icc (-h) h) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨z, _, rfl⟩
  have hk0 := killedMass_nonneg ν h (PolygonalKilledFunctionalLimit.floorHorizon T h) z
  have hk1 := killedMass_le_one ν h (PolygonalKilledFunctionalLimit.floorHorizon T h) z
  have hg0 : 0 ≤ BrownianUniformSurvival.brownianSurvival CanonicalBrownian.B
      CanonicalBrownian.law T (z / h) := measureReal_nonneg
  have hg1 : BrownianUniformSurvival.brownianSurvival CanonicalBrownian.B
      CanonicalBrownian.law T (z / h) ≤ 1 := measureReal_le_one
  exact abs_le.mpr ⟨by linarith, by linarith⟩

-- L2 PRIVATE: both estimates concern the actual real sSup, not a supplied error.
private theorem sourceSurvivalError_bounds
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (T : ℝ≥0)
    (h : ℝ) (hh : 0 ≤ h) :
    0 ≤ sourceSurvivalError ν T h ∧ sourceSurvivalError ν T h ≤ 1 := by
  let e : ℝ → ℝ := fun z =>
    |killedMass ν h (PolygonalKilledFunctionalLimit.floorHorizon T h) z -
      BrownianUniformSurvival.brownianSurvival CanonicalBrownian.B
        CanonicalBrownian.law T (z / h)|
  have he1 (z : ℝ) : e z ≤ 1 := by
    have hk0 := killedMass_nonneg ν h (PolygonalKilledFunctionalLimit.floorHorizon T h) z
    have hk1 := killedMass_le_one ν h (PolygonalKilledFunctionalLimit.floorHorizon T h) z
    have hg0 : 0 ≤ BrownianUniformSurvival.brownianSurvival CanonicalBrownian.B
        CanonicalBrownian.law T (z / h) := measureReal_nonneg
    have hg1 : BrownianUniformSurvival.brownianSurvival CanonicalBrownian.B
        CanonicalBrownian.law T (z / h) ≤ 1 := measureReal_le_one
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hz0 : (0 : ℝ) ∈ Icc (-h) h := ⟨neg_nonpos.mpr hh, hh⟩
  have hne : (e '' Icc (-h) h).Nonempty := ⟨e 0, ⟨0, hz0, rfl⟩⟩
  have hb : BddAbove (e '' Icc (-h) h) := survival_error_image_bddAbove ν T h
  change 0 ≤ sSup (e '' Icc (-h) h) ∧ sSup (e '' Icc (-h) h) ≤ 1
  constructor
  · have he0 : 0 ≤ e 0 := abs_nonneg _
    exact he0.trans (le_csSup hb ⟨0, hz0, rfl⟩)
  · apply csSup_le hne
    rintro _ ⟨z, _, rfl⟩
    exact he1 z

-- L3 PRIVATE: membership plus boundedness, with no attainment assumption.
private theorem source_survival_error_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (T : ℝ≥0)
    (h z : ℝ) (hz : |z| ≤ h) :
    |killedMass ν h (PolygonalKilledFunctionalLimit.floorHorizon T h) z -
      BrownianUniformSurvival.brownianSurvival CanonicalBrownian.B
        CanonicalBrownian.law T (z / h)| ≤ sourceSurvivalError ν T h := by
  unfold sourceSurvivalError BrownianUniformSurvival.survivalError
  exact le_csSup (survival_error_image_bddAbove ν T h) ⟨z, abs_le.mp hz, rfl⟩

-- L4 PRIVATE: P0 and the literal B0 error, for all closed-interval physical starts.
private theorem terminal_row_error
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (T : ℝ≥0) (hT : 1 ≤ T)
    (h : ℝ) (hh : 0 < h) (z : ℝ) (hz : |z| ≤ h) :
    |killedMass ν h (PolygonalKilledFunctionalLimit.floorHorizon T h) z -
      (4 / Real.pi) * Real.exp (-lambda * (T : ℝ)) *
        Real.cos (Real.pi * z / (2 * h))| ≤
      sourceSurvivalError ν T h +
        BrownianTerminalSpectral.remainderC * Real.exp (-9 * lambda * (T : ℝ)) := by
  have hb := abs_le.mp hz
  have hu : z / h ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · exact (le_div_iff₀ hh).mpr (by simpa only [neg_one_mul] using hb.1)
    · exact (div_le_iff₀ hh).mpr (by simpa only [one_mul] using hb.2)
  have hangle : Real.pi * (z / h) / 2 = Real.pi * z / (2 * h) := by
    field_simp [ne_of_gt hh] <;> ring
  have htail := (BrownianTerminalSpectral.brownian_terminal_block
    CanonicalBrownian.B CanonicalBrownian.law CanonicalBrownian.isBrownianReal
      T hT (z / h) hu).2
  have hgbound :
      |BrownianUniformSurvival.brownianSurvival CanonicalBrownian.B
          CanonicalBrownian.law T (z / h) -
        (4 / Real.pi) * Real.exp (-lambda * (T : ℝ)) *
          Real.cos (Real.pi * z / (2 * h))| ≤
        BrownianTerminalSpectral.remainderC * Real.exp (-9 * lambda * (T : ℝ)) := by
    simpa only [BrownianUniformSurvival.brownianSurvival,
      BrownianTerminalSpectral.terminalRemainder, hangle] using htail
  calc
    |killedMass ν h (PolygonalKilledFunctionalLimit.floorHorizon T h) z -
        (4 / Real.pi) * Real.exp (-lambda * (T : ℝ)) *
          Real.cos (Real.pi * z / (2 * h))| =
      |(killedMass ν h (PolygonalKilledFunctionalLimit.floorHorizon T h) z -
          BrownianUniformSurvival.brownianSurvival CanonicalBrownian.B
            CanonicalBrownian.law T (z / h)) +
        (BrownianUniformSurvival.brownianSurvival CanonicalBrownian.B
            CanonicalBrownian.law T (z / h) -
          (4 / Real.pi) * Real.exp (-lambda * (T : ℝ)) *
            Real.cos (Real.pi * z / (2 * h)))| := by congr 1; ring
    _ ≤ |killedMass ν h (PolygonalKilledFunctionalLimit.floorHorizon T h) z -
          BrownianUniformSurvival.brownianSurvival CanonicalBrownian.B
            CanonicalBrownian.law T (z / h)| +
        |BrownianUniformSurvival.brownianSurvival CanonicalBrownian.B
            CanonicalBrownian.law T (z / h) -
          (4 / Real.pi) * Real.exp (-lambda * (T : ℝ)) *
            Real.cos (Real.pi * z / (2 * h))| := abs_add_le _ _
    _ ≤ sourceSurvivalError ν T h +
        BrownianTerminalSpectral.remainderC * Real.exp (-9 * lambda * (T : ℝ)) :=
      add_le_add (source_survival_error_le ν T h z hz) hgbound

-- L5 PRIVATE: the integrated residual is globally measurable and genuinely integrable.
-- No Brownian survival function is integrated in this module.
private theorem terminal_residual_regular
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (T : ℝ≥0)
    (h : ℝ) (n : ℕ) (z : ℝ) :
    Measurable (fun w : ℝ =>
      killedMass ν h (PolygonalKilledFunctionalLimit.floorHorizon T h) w -
        (4 / Real.pi) * Real.exp (-lambda * (T : ℝ)) *
          Real.cos (Real.pi * w / (2 * h))) ∧
    Integrable (fun w : ℝ =>
      killedMass ν h (PolygonalKilledFunctionalLimit.floorHorizon T h) w -
        (4 / Real.pi) * Real.exp (-lambda * (T : ℝ)) *
          Real.cos (Real.pi * w / (2 * h))) (killedIterKernel ν h n z) := by
  let L : ℕ := PolygonalKilledFunctionalLimit.floorHorizon T h
  let a : ℝ := (4 / Real.pi) * Real.exp (-lambda * (T : ℝ))
  let R : ℝ → ℝ := fun w => killedMass ν h L w - a * Real.cos (Real.pi * w / (2 * h))
  have hmass : Measurable (killedMass ν h L) :=
    killedAction_measurable ν h L (fun _ : ℝ => 1) measurable_const
  have hcos : Measurable (fun w : ℝ => Real.cos (Real.pi * w / (2 * h))) := by
    fun_prop
  have hR : Measurable R := hmass.sub (measurable_const.mul hcos)
  have hbound (w : ℝ) : |R w| ≤ 1 + |a| := by
    calc
      |R w| ≤ |killedMass ν h L w| + |a * Real.cos (Real.pi * w / (2 * h))| :=
        abs_sub _ _
      _ = killedMass ν h L w + |a| * |Real.cos (Real.pi * w / (2 * h))| := by
        rw [abs_of_nonneg (killedMass_nonneg ν h L w), abs_mul]
      _ ≤ 1 + |a| * 1 :=
        add_le_add (killedMass_le_one ν h L w)
          (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg a))
      _ = 1 + |a| := by rw [mul_one]
  change Measurable R ∧ Integrable R (killedIterKernel ν h n z)
  exact ⟨hR, killedAction_integrable ν h n z R hR ⟨1 + |a|, hbound⟩⟩

-- L6 PRIVATE: exact semigroup and linearity, valid also at n=0 and floorHorizon=0.
private theorem terminal_integral_identity
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (T : ℝ≥0) (h : ℝ) (n : ℕ) :
    killedMass ν h (n + PolygonalKilledFunctionalLimit.floorHorizon T h) 0 -
      (4 / Real.pi) * Real.exp (-lambda * (T : ℝ)) *
        killedAction ν h n (fun w : ℝ => Real.cos (Real.pi * w / (2 * h))) 0 =
      ∫ w : ℝ,
        (killedMass ν h (PolygonalKilledFunctionalLimit.floorHorizon T h) w -
          (4 / Real.pi) * Real.exp (-lambda * (T : ℝ)) *
            Real.cos (Real.pi * w / (2 * h))) ∂killedIterKernel ν h n 0 := by
  let L : ℕ := PolygonalKilledFunctionalLimit.floorHorizon T h
  let a : ℝ := (4 / Real.pi) * Real.exp (-lambda * (T : ℝ))
  have hmass : Integrable (killedMass ν h L) (killedIterKernel ν h n 0) :=
    killedAction_iterated_integrable ν h n L 0 (fun _ : ℝ => 1)
      measurable_const ⟨1, by simp⟩
  have hcos : Integrable (fun w : ℝ => Real.cos (Real.pi * w / (2 * h)))
      (killedIterKernel ν h n 0) :=
    killedAction_integrable ν h n 0 _ (by fun_prop)
      ⟨1, fun w => Real.abs_cos_le_one _⟩
  have hscaled : Integrable (fun w : ℝ => a * Real.cos (Real.pi * w / (2 * h)))
      (killedIterKernel ν h n 0) := hcos.const_mul a
  have hsemigroup : killedMass ν h (n + L) 0 =
      ∫ w : ℝ, killedMass ν h L w ∂killedIterKernel ν h n 0 :=
    killedAction_semigroup ν h n L 0 (fun _ : ℝ => 1) measurable_const ⟨1, by simp⟩
  change killedMass ν h (n + L) 0 -
      a * killedAction ν h n (fun w : ℝ => Real.cos (Real.pi * w / (2 * h))) 0 =
    ∫ w : ℝ, (killedMass ν h L w - a * Real.cos (Real.pi * w / (2 * h)))
      ∂killedIterKernel ν h n 0
  rw [hsemigroup]
  change (∫ w : ℝ, killedMass ν h L w ∂killedIterKernel ν h n 0) -
      a * (∫ w : ℝ, Real.cos (Real.pi * w / (2 * h)) ∂killedIterKernel ν h n 0) = _
  rw [integral_sub hmass hscaled, integral_const_mul]

-- P1 PUBLIC: finite actual-kernel terminal block. No moment condition is used.
theorem terminal_kernel_block
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (T : ℝ≥0) (hT : 1 ≤ T)
    (h : ℝ) (hh : 0 < h) (n : ℕ) :
    |killedMass ν h (n + PolygonalKilledFunctionalLimit.floorHorizon T h) 0 -
      (4 / Real.pi) * Real.exp (-lambda * (T : ℝ)) *
        killedAction ν h n (fun w : ℝ => Real.cos (Real.pi * w / (2 * h))) 0| ≤
      (sourceSurvivalError ν T h +
        BrownianTerminalSpectral.remainderC * Real.exp (-9 * lambda * (T : ℝ))) *
          killedMass ν h n 0 := by
  let M : ℝ := sourceSurvivalError ν T h +
    BrownianTerminalSpectral.remainderC * Real.exp (-9 * lambda * (T : ℝ))
  let R : ℝ → ℝ := fun w =>
    killedMass ν h (PolygonalKilledFunctionalLimit.floorHorizon T h) w -
      (4 / Real.pi) * Real.exp (-lambda * (T : ℝ)) *
        Real.cos (Real.pi * w / (2 * h))
  have hfi : Integrable R (killedIterKernel ν h n 0) :=
    (terminal_residual_regular ν T h n 0).2
  have hsupp : ∀ᵐ w ∂killedIterKernel ν h n 0, |w| ≤ h :=
    killedIterKernel_ae_support ν h n 0 (by simpa only [abs_zero] using hh.le)
  have hbound : ∀ᵐ w ∂killedIterKernel ν h n 0, |R w| ≤ M :=
    hsupp.mono fun w hw => terminal_row_error ν T hT h hh w hw
  rw [terminal_integral_identity ν T h n]
  change |∫ w : ℝ, R w ∂killedIterKernel ν h n 0| ≤ M * killedMass ν h n 0
  calc
    |∫ w : ℝ, R w ∂killedIterKernel ν h n 0| ≤
        ∫ w : ℝ, |R w| ∂killedIterKernel ν h n 0 := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := killedIterKernel ν h n 0) R)
    _ ≤ ∫ _w : ℝ, M ∂killedIterKernel ν h n 0 :=
      integral_mono_ae hfi.abs (integrable_const M) hbound
    _ = M * killedMass ν h n 0 := by
      simp [killedMass_eq_real, mul_comm]

-- P2 PUBLIC: pure fixed-law B0, with the exact source third/first/second moments.
theorem tendsto_sourceSurvivalError
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (T : ℝ≥0) (hT : 0 < T)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    Tendsto (sourceSurvivalError ν T) atTop (𝓝 (0 : ℝ)) := by
  change Tendsto (BrownianUniformSurvival.survivalError CanonicalBrownian.B
    CanonicalBrownian.law ν T) atTop (𝓝 (0 : ℝ))
  exact BrownianUniformSurvival.tendsto_survivalError CanonicalBrownian.B
    CanonicalBrownian.law CanonicalBrownian.isBrownianReal T hT ν h3 hmean hsecond

-- P3 PUBLIC: H depends on ν,T,ε; it is uniform over every natural n, including 0.
-- This theorem is an eventual P1 corollary, not the original normalized source P2.
theorem eventually_terminal_kernel_block
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (T : ℝ≥0) (hT : 1 ≤ T)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℝ, 0 < H ∧ ∀ h : ℝ, H ≤ h → ∀ n : ℕ,
      |killedMass ν h (n + PolygonalKilledFunctionalLimit.floorHorizon T h) 0 -
        (4 / Real.pi) * Real.exp (-lambda * (T : ℝ)) *
          killedAction ν h n (fun w : ℝ => Real.cos (Real.pi * w / (2 * h))) 0| ≤
        (ε + BrownianTerminalSpectral.remainderC * Real.exp (-9 * lambda * (T : ℝ))) *
          killedMass ν h n 0 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hlim := tendsto_sourceSurvivalError ν T hTpos h3 hmean hsecond
  have hsmall : ∀ᶠ h : ℝ in atTop, sourceSurvivalError ν T h < ε :=
    hlim.eventually (Iio_mem_nhds hε)
  obtain ⟨H₀, hH₀⟩ := eventually_atTop.mp hsmall
  have hH : 0 < max (1 : ℝ) H₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨max 1 H₀, hH, ?_⟩
  intro h hh n
  have hhpos : 0 < h := lt_of_lt_of_le hH hh
  have hE : sourceSurvivalError ν T h ≤ ε :=
    (hH₀ h ((le_max_right _ _).trans hh)).le
  exact (terminal_kernel_block ν T hT h hhpos n).trans
    (mul_le_mul_of_nonneg_right
      (add_le_add hE le_rfl)
      (killedMass_nonneg ν h n 0))

end Shao.OQ4.BrownianTerminalKernelBlock
end
