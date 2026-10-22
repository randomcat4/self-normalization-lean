import Shao.OQ4.RademacherS3Assembly
import Shao.OQ4.RademacherLatticeShift
import Shao.OQ4.RademacherScaleAssembly
import Shao.Probability.BrownianSup
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Declaration-only text for frozen original S4, sections 3 through 7.
All theorem bodies are empty comment placeholders. This is not a Lean module.
The S3 module import is pendingformalplacement against the exact public S3
declaration freeze 3efdc04e86d5c69a1e823b93daa86d6f1ab874bf3af2f3faca9f2829d9e86fcc.
S3 has not been compiled or accepted by this declaration task.
The scale module is published as PR138; root integration is pending.
The actual Brownian B1 and B2 interfaces are available in accepted root v35.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Shao.OQ4.RademacherS4Assembly

def H (m : ℕ) : ℝ := RademacherS3Assembly.H m

def N (n : ℕ) : ℝ := RademacherS3Assembly.N n

def t (m n : ℕ) : ℝ := RademacherS3Assembly.t m n

def u (m : ℕ) : ℝ := RademacherS3Assembly.u m

def a (m : ℕ) : ℝ := RademacherS3Assembly.a m

def rho (m : ℕ) : ℝ := RademacherS3Assembly.rho m

def lambda : ℝ := RademacherS3Assembly.lambda

def p (n : ℕ) (h : ℝ) : ℝ := RademacherS3Assembly.p n h

def K (n : ℕ) (h : ℝ) : ℝ := RademacherS3Assembly.K n h

def D (m n : ℕ) (h : ℝ) : ℝ := RademacherS3Assembly.D m n h

def x (n : ℕ) (h : ℝ) : ℝ := RademacherS3Assembly.x n h

def g (s : ℝ) : ℝ := RademacherS3Assembly.g s

def b {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (s : ℝ) : ℝ :=
  RademacherS3Assembly.b B P hB s

def T {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (s : ℝ) : ℝ :=
  RademacherS3Assembly.T B P hB s

def Cdet (m n : ℕ) (h : ℝ) : ℝ := RademacherS3Assembly.C m n h

def delta (m : ℕ) (h : ℝ) : ℝ := RademacherLatticeShift.delta m h

-- This is the third scale, not the actual S3 error eta3 below.
def scale3 (n : ℕ) (h : ℝ) : ℝ := RademacherScaleAssembly.eta3 n h

-- A fixed named DA1 witness; there is no sequence-dependent constant choice.
def C_DA : ℝ := RademacherLatticeShift.C

def w (m n : ℕ) (h : ℝ) : ℝ :=
  (Real.pi ^ 2 / 4) * scale3 n h * delta m h

def Q {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (n : ℕ) (h : ℝ) : ℝ :=
  p n h / b B P hB (x n h)

def QK {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (n : ℕ) (h : ℝ) : ℝ :=
  K n h / b B P hB (x n h)

def eta3 {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (m n : ℕ) (h : ℝ) : ℝ :=
  Real.log (Q B P hB n h) - Cdet m n h

def shift {α : Type*} (f : ℕ → α) (K_0 : ℕ) : ℕ → α :=
  fun j : ℕ => f (j + K_0)

-- These transparent predicates contain conclusions only.
def TimeLegal (m n : ℕ) (h : ℝ) : Prop :=
  1 ≤ m ∧ (m : ℝ) ≤ h ∧ h < H m ∧
  1 ≤ n ∧ 0 < N n ∧ 0 < Real.sqrt (N n) ∧
  (Real.sqrt (N n)) ^ 2 = N n ∧ (H m) ^ 2 ≤ N n ∧
  0 < h ∧ 0 < x n h ∧ x n h = h / Real.sqrt (N n)

def ProbabilityLegal {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (m n : ℕ) (h : ℝ) : Prop :=
  1 ≤ h ∧ 0 < h ∧ 0 < H m ∧ 0 < a m ∧
  0 < rho m ∧ rho m < 1 ∧ 0 < a m * rho m ^ n ∧
  0 < Real.pi * a m / 4 ∧
  p n h = K n h ∧ 0 < p n h ∧ 0 < K n h ∧ 0 < D m n h ∧
  0 < b B P hB (x n h) ∧ 0 < g (x n h) ∧
  0 < T B P hB (x n h) ∧
  Q B P hB n h = QK B P hB n h ∧
  0 < Q B P hB n h ∧ 0 < QK B P hB n h

def LogIdentities {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (m n : ℕ) (h : ℝ) : Prop :=
  Real.log (Q B P hB n h) =
    Real.log (p n h) - Real.log (b B P hB (x n h)) ∧
  Real.log (QK B P hB n h) =
    Real.log (K n h) - Real.log (b B P hB (x n h)) ∧
  eta3 B P hB m n h = Real.log (QK B P hB n h) - Cdet m n h ∧
  eta3 B P hB m n h =
    Real.log (D m n h) - Real.log (T B P hB (x n h)) ∧
  Real.log (Q B P hB n h) - w m n h =
    (Cdet m n h - w m n h) + eta3 B P hB m n h ∧
  Real.log (QK B P hB n h) - w m n h =
    (Cdet m n h - w m n h) + eta3 B P hB m n h

-- Total real expressions occur in the limits. Their ordinary probability/log
-- meanings are separately returned on the same positive tail below.
def S4Outputs {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (m_ n_ : ℕ → ℕ) (h_ : ℕ → ℝ) : Prop :=
  Tendsto (fun k : ℕ => H (m_ k)) atTop atTop ∧
  Tendsto (fun k : ℕ => N (n_ k) / (H (m_ k)) ^ 2) atTop atTop ∧
  Tendsto (fun k : ℕ => N (n_ k) / (h_ k) ^ 4)
    atTop (𝓝 (0 : ℝ)) ∧
  Tendsto (fun k : ℕ => 1 / (H (m_ k)) ^ 2)
    atTop (𝓝 (0 : ℝ)) ∧
  Tendsto (fun k : ℕ => x (n_ k) (h_ k)) atTop (𝓝 (0 : ℝ)) ∧
  (∀ d : ℝ, 0 < d → ∃ K_d : ℕ, ∀ k : ℕ, K_d ≤ k →
    0 < x (n_ k) (h_ k) ∧ x (n_ k) (h_ k) < d) ∧
  Tendsto (fun k : ℕ => eta3 B P hB (m_ k) (n_ k) (h_ k))
    atTop (𝓝 (0 : ℝ)) ∧
  Tendsto
    (fun k : ℕ => Real.log (Q B P hB (n_ k) (h_ k)) -
      w (m_ k) (n_ k) (h_ k))
    atTop (𝓝 (0 : ℝ)) ∧
  Tendsto
    (fun k : ℕ => Real.log (QK B P hB (n_ k) (h_ k)) -
      w (m_ k) (n_ k) (h_ k))
    atTop (𝓝 (0 : ℝ)) ∧
  (∃ K_time K_pos : ℕ, K_time ≤ K_pos ∧
    (∀ k : ℕ, K_time ≤ k → TimeLegal (m_ k) (n_ k) (h_ k)) ∧
    (∀ k : ℕ, K_pos ≤ k →
      ProbabilityLegal B P hB (m_ k) (n_ k) (h_ k) ∧
      LogIdentities B P hB (m_ k) (n_ k) (h_ k) ∧
      |(Real.log (Q B P hB (n_ k) (h_ k)) -
          w (m_ k) (n_ k) (h_ k)) -
          eta3 B P hB (m_ k) (n_ k) (h_ k)| ≤
        C_DA * (N (n_ k) / (h_ k) ^ 4 + 1 / (H (m_ k)) ^ 2) ∧
      |(Real.log (QK B P hB (n_ k) (h_ k)) -
          w (m_ k) (n_ k) (h_ k)) -
          eta3 B P hB (m_ k) (n_ k) (h_ k)| ≤
        C_DA * (N (n_ k) / (h_ k) ^ 4 + 1 / (H (m_ k)) ^ 2)) ∧
    (∀ e : ℝ, 0 < e → ∃ K_e : ℕ, K_pos ≤ K_e ∧
      ∀ k : ℕ, K_e ≤ k →
        TimeLegal (m_ k) (n_ k) (h_ k) ∧
        ProbabilityLegal B P hB (m_ k) (n_ k) (h_ k) ∧
        LogIdentities B P hB (m_ k) (n_ k) (h_ k) ∧
        |Real.log (Q B P hB (n_ k) (h_ k)) -
          w (m_ k) (n_ k) (h_ k)| < e ∧
        |Real.log (QK B P hB (n_ k) (h_ k)) -
          w (m_ k) (n_ k) (h_ k)| < e))

theorem definition_bridges (m n : ℕ) (h : ℝ) :
    H m = (m : ℝ) + 1 ∧ H m = RademacherScalarBounds.H m ∧
    N n = (n : ℝ) ∧ t m n = N n / (H m) ^ 2 ∧
    u m = Real.pi / (4 * H m) ∧
    a m = RademacherSpectralPairing.amplitude m ∧
    a m = RademacherScalarBounds.a m ∧
    a m = (1 / H m) * (Real.cos (u m) / Real.sin (u m)) ∧
    rho m = RademacherSpectralPairing.rho m ∧
    rho m = RademacherScalarBounds.rho m ∧
    rho m = Real.cos (Real.pi / (2 * H m)) ∧
    lambda = Real.pi ^ 2 / 8 ∧
    delta m h = H m - h ∧ scale3 n h = N n / h ^ 3 ∧
    RademacherS3Assembly.A m n = a m * rho m ^ n ∧
    x n h = h / Real.sqrt (N n) ∧
    Cdet m n h = lambda * N n / h ^ 2 +
      N n * Real.log (rho m) + Real.log (Real.pi * a m / 4) ∧
    w m n h = (Real.pi ^ 2 / 4) * (N n / h ^ 3) * (H m - h) ∧
    C_DA = RademacherLatticeShift.C := by
  -- Proof placeholder.

theorem finite_cell (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (n : ℕ) :
    1 ≤ h ∧ 0 < h ∧ 2 ≤ H m ∧ 0 < H m ∧
    H m = h + delta m h ∧ 0 < delta m h ∧ delta m h ≤ 1 ∧
    (h = (m : ℝ) → delta m h = 1) ∧
    h ^ 2 ≠ 0 ∧ h ^ 3 ≠ 0 ∧ h ^ 4 ≠ 0 ∧ (H m) ^ 2 ≠ 0 ∧
    4 * H m ≠ 0 ∧ 2 * H m ≠ 0 ∧ Real.sin (u m) ≠ 0 ∧
    0 < a m ∧ 0 < rho m ∧ rho m < 1 ∧
    0 < a m * rho m ^ n ∧ 0 < Real.pi * a m / 4 ∧
    p n h =
      (Measure.pi (fun _ : Fin n => RademacherCosine.law)).real
        (@Shao.closedStrip n h) ∧
    K n h =
      @Shao.OQ4.killedMass RademacherCosine.law
        RademacherCosine.law_isProbabilityMeasure h n (0 : ℝ) ∧
    p n h = K n h ∧
    D m n h = p n h / (a m * rho m ^ n) ∧
    D m n h = K n h / (a m * rho m ^ n) ∧
    (n = 0 → p n h = 1 ∧ K n h = 1 ∧ x n h = 0) := by
  -- Proof placeholder.

theorem actual_brownian_bridges {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (s : ℝ) :
    b B P hB s = Shao.Probability.BrownianSup.probability B P hB s ∧
    b B P hB s =
      P.real {ω | Shao.Probability.BrownianSup.U B P hB ω ≤ s} ∧
    b B P hB s = P.real (Shao.Probability.BrownianSup.fullStrip B s) ∧
    g s = (4 / Real.pi) * Real.exp (-lambda / s ^ 2) ∧
    0 < g s ∧ T B P hB s = b B P hB s / g s := by
  -- Proof placeholder.

theorem fixed_DA_constant :
    0 < C_DA ∧
    ∀ m : ℕ, 1 ≤ m →
      ∀ h : ℝ, (m : ℝ) ≤ h → h < (m : ℝ) + 1 →
        ∀ n : ℕ,
          |Cdet m n h - w m n h| ≤
            C_DA * (N n / h ^ 4 + 1 / (H m) ^ 2) := by
  -- Proof placeholder.

theorem S4_ALL {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (m_ n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hm : ∀ k : ℕ, 1 ≤ m_ k)
    (hmh : ∀ k : ℕ, (m_ k : ℝ) ≤ h_ k)
    (hhm : ∀ k : ℕ, h_ k < (m_ k : ℝ) + 1)
    (hh : Tendsto h_ atTop atTop)
    (hscale2 : Tendsto (fun k : ℕ => N (n_ k) / (h_ k) ^ 2) atTop atTop)
    (hscale3 : ∃ M : ℝ, 0 < M ∧
      ∃ K_M : ℕ, ∀ k : ℕ, K_M ≤ k → scale3 (n_ k) (h_ k) ≤ M) :
    S4Outputs B P hB m_ n_ h_ := by
  -- Proof placeholder.

theorem S4_SUB {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (m_ n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hm : ∀ k : ℕ, 1 ≤ m_ k)
    (hmh : ∀ k : ℕ, (m_ k : ℝ) ≤ h_ k)
    (hhm : ∀ k : ℕ, h_ k < (m_ k : ℝ) + 1)
    (hh : Tendsto h_ atTop atTop)
    (hscale2 : Tendsto (fun k : ℕ => N (n_ k) / (h_ k) ^ 2) atTop atTop)
    (hsubcritical : Tendsto (fun k : ℕ => scale3 (n_ k) (h_ k))
      atTop (𝓝 (0 : ℝ))) :
    S4Outputs B P hB m_ n_ h_ ∧
    Tendsto (fun k : ℕ => Real.log (Q B P hB (n_ k) (h_ k)))
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun k : ℕ => Q B P hB (n_ k) (h_ k))
      atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (fun k : ℕ => QK B P hB (n_ k) (h_ k))
      atTop (𝓝 (1 : ℝ)) ∧
    (∀ e : ℝ, 0 < e → ∃ K_e : ℕ, ∀ k : ℕ, K_e ≤ k →
      TimeLegal (m_ k) (n_ k) (h_ k) ∧
      ProbabilityLegal B P hB (m_ k) (n_ k) (h_ k) ∧
      |Real.log (Q B P hB (n_ k) (h_ k))| < e ∧
      |Q B P hB (n_ k) (h_ k) - 1| < e ∧
      |QK B P hB (n_ k) (h_ k) - 1| < e) := by
  -- Proof placeholder.

theorem shifted_inputs
    (m_ n_ : ℕ → ℕ) (h_ : ℕ → ℝ) (K_cell K_0 : ℕ)
    (hcell : ∀ k : ℕ, K_cell ≤ k →
      1 ≤ m_ k ∧ (m_ k : ℝ) ≤ h_ k ∧ h_ k < (m_ k : ℝ) + 1)
    (hK_0 : K_cell ≤ K_0)
    (hh : Tendsto h_ atTop atTop)
    (hscale2 : Tendsto (fun k : ℕ => N (n_ k) / (h_ k) ^ 2) atTop atTop)
    (M : ℝ) (hM : 0 < M) (K_M : ℕ)
    (hM_bound : ∀ k : ℕ, K_M ≤ k → scale3 (n_ k) (h_ k) ≤ M) :
    (∀ j : ℕ,
      1 ≤ shift m_ K_0 j ∧
      (shift m_ K_0 j : ℝ) ≤ shift h_ K_0 j ∧
      shift h_ K_0 j < (shift m_ K_0 j : ℝ) + 1) ∧
    Tendsto (shift h_ K_0) atTop atTop ∧
    Tendsto
      (fun j : ℕ => N (shift n_ K_0 j) / (shift h_ K_0 j) ^ 2)
      atTop atTop ∧
    (∃ K_shift : ℕ, ∀ j : ℕ, K_shift ≤ j →
      scale3 (shift n_ K_0 j) (shift h_ K_0 j) ≤ M) ∧
    (Tendsto (fun k : ℕ => scale3 (n_ k) (h_ k)) atTop (𝓝 (0 : ℝ)) →
      Tendsto (fun j : ℕ => scale3 (shift n_ K_0 j) (shift h_ K_0 j))
        atTop (𝓝 (0 : ℝ))) := by
  -- Proof placeholder.

-- These are identities of total expressions at the unchanged shifted index.
-- Positive-time and probability interpretations are supplied by S4_EVENTUAL.
theorem shifted_objects {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (m_ n_ : ℕ → ℕ) (h_ : ℕ → ℝ) (K_0 : ℕ) :
    ∀ j : ℕ,
      N (shift n_ K_0 j) = N (n_ (j + K_0)) ∧
      H (shift m_ K_0 j) = H (m_ (j + K_0)) ∧
      a (shift m_ K_0 j) = a (m_ (j + K_0)) ∧
      rho (shift m_ K_0 j) = rho (m_ (j + K_0)) ∧
      delta (shift m_ K_0 j) (shift h_ K_0 j) =
        delta (m_ (j + K_0)) (h_ (j + K_0)) ∧
      scale3 (shift n_ K_0 j) (shift h_ K_0 j) =
        scale3 (n_ (j + K_0)) (h_ (j + K_0)) ∧
      p (shift n_ K_0 j) (shift h_ K_0 j) =
        p (n_ (j + K_0)) (h_ (j + K_0)) ∧
      K (shift n_ K_0 j) (shift h_ K_0 j) =
        K (n_ (j + K_0)) (h_ (j + K_0)) ∧
      x (shift n_ K_0 j) (shift h_ K_0 j) =
        x (n_ (j + K_0)) (h_ (j + K_0)) ∧
      b B P hB (x (shift n_ K_0 j) (shift h_ K_0 j)) =
        b B P hB (x (n_ (j + K_0)) (h_ (j + K_0))) ∧
      g (x (shift n_ K_0 j) (shift h_ K_0 j)) =
        g (x (n_ (j + K_0)) (h_ (j + K_0))) ∧
      Cdet (shift m_ K_0 j) (shift n_ K_0 j) (shift h_ K_0 j) =
        Cdet (m_ (j + K_0)) (n_ (j + K_0)) (h_ (j + K_0)) ∧
      D (shift m_ K_0 j) (shift n_ K_0 j) (shift h_ K_0 j) =
        D (m_ (j + K_0)) (n_ (j + K_0)) (h_ (j + K_0)) ∧
      T B P hB (x (shift n_ K_0 j) (shift h_ K_0 j)) =
        T B P hB (x (n_ (j + K_0)) (h_ (j + K_0))) ∧
      Q B P hB (shift n_ K_0 j) (shift h_ K_0 j) =
        Q B P hB (n_ (j + K_0)) (h_ (j + K_0)) ∧
      QK B P hB (shift n_ K_0 j) (shift h_ K_0 j) =
        QK B P hB (n_ (j + K_0)) (h_ (j + K_0)) ∧
      eta3 B P hB (shift m_ K_0 j) (shift n_ K_0 j) (shift h_ K_0 j) =
        eta3 B P hB (m_ (j + K_0)) (n_ (j + K_0)) (h_ (j + K_0)) ∧
      w (shift m_ K_0 j) (shift n_ K_0 j) (shift h_ K_0 j) =
        w (m_ (j + K_0)) (n_ (j + K_0)) (h_ (j + K_0)) := by
  -- Proof placeholder.

theorem S4_EVENTUAL {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (m_ n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hcell : ∃ K_cell : ℕ, ∀ k : ℕ, K_cell ≤ k →
      1 ≤ m_ k ∧ (m_ k : ℝ) ≤ h_ k ∧ h_ k < (m_ k : ℝ) + 1)
    (hh : Tendsto h_ atTop atTop)
    (hscale2 : Tendsto (fun k : ℕ => N (n_ k) / (h_ k) ^ 2) atTop atTop)
    (hscale3 : ∃ M : ℝ, 0 < M ∧
      ∃ K_M : ℕ, ∀ k : ℕ, K_M ≤ k → scale3 (n_ k) (h_ k) ≤ M) :
    S4Outputs B P hB m_ n_ h_ := by
  -- Proof placeholder.

theorem S4_SUB_EVENTUAL {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (m_ n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hcell : ∃ K_cell : ℕ, ∀ k : ℕ, K_cell ≤ k →
      1 ≤ m_ k ∧ (m_ k : ℝ) ≤ h_ k ∧ h_ k < (m_ k : ℝ) + 1)
    (hh : Tendsto h_ atTop atTop)
    (hscale2 : Tendsto (fun k : ℕ => N (n_ k) / (h_ k) ^ 2) atTop atTop)
    (hsubcritical : Tendsto (fun k : ℕ => scale3 (n_ k) (h_ k))
      atTop (𝓝 (0 : ℝ))) :
    S4Outputs B P hB m_ n_ h_ ∧
    Tendsto (fun k : ℕ => Real.log (Q B P hB (n_ k) (h_ k)))
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun k : ℕ => Q B P hB (n_ k) (h_ k))
      atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (fun k : ℕ => QK B P hB (n_ k) (h_ k))
      atTop (𝓝 (1 : ℝ)) ∧
    (∀ e : ℝ, 0 < e → ∃ K_e : ℕ, ∀ k : ℕ, K_e ≤ k →
      TimeLegal (m_ k) (n_ k) (h_ k) ∧
      ProbabilityLegal B P hB (m_ k) (n_ k) (h_ k) ∧
      |Real.log (Q B P hB (n_ k) (h_ k))| < e ∧
      |Q B P hB (n_ k) (h_ k) - 1| < e ∧
      |QK B P hB (n_ k) (h_ k) - 1| < e) := by
  -- Proof placeholder.

end Shao.OQ4.RademacherS4Assembly

end
