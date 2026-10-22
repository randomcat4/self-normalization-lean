import Shao.OQ4.RademacherCriticalPhase
import Shao.OQ4.RademacherS4Assembly
import Shao.Probability.FiniteIID
import Shao.Probability.MeasurablePath
import Shao.Basic.ClosedSurvival
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Declaration-only freeze for original S5, mathematical freeze sections 3--8.
Expected future module: Shao/OQ4/RademacherS5Assembly.lean.
S4 import: pendingformalplacement against the exact public declaration freeze
0c4af1e038d7290b08daf6da9578519be7ffc913611f91fca2b833129d5fe6f1.
No S3/S4 implementation or S5 proof was read. No Lean command was run.
Every theorem body below is an empty comment placeholder.
This text is not a compiled or accepted implementation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology

namespace Shao.OQ4.RademacherS5Assembly

-- Exact aliases: all deterministic quantities belong to the same CP object.
def N (n : ℕ) : ℝ := RademacherS4Assembly.N n
def root (n : ℕ) : ℝ := RademacherCriticalPhase.root n
def height (c : ℝ) (n : ℕ) : ℝ := RademacherCriticalPhase.height c n
def phaseFloor (c : ℝ) (n : ℕ) : ℕ := RademacherCriticalPhase.phaseFloor c n
def upperHeight (c : ℝ) (n : ℕ) : ℝ := RademacherCriticalPhase.upperHeight c n
def delta (c : ℝ) (n : ℕ) : ℝ := RademacherCriticalPhase.delta c n
def coeff (c : ℝ) : ℝ := RademacherCriticalPhase.q c
def E (c : ℝ) (n : ℕ) : ℝ := RademacherCriticalPhase.exponent c n
def F (c : ℝ) (n : ℕ) : ℝ := RademacherCriticalPhase.factor c n
def Ncell (c : ℝ) : ℕ := RademacherCriticalPhase.cutoff c

def x (c : ℝ) (n : ℕ) : ℝ :=
  c * Real.rpow (n : ℝ) (-((1 : ℝ) / 6))

def p (n : ℕ) (h : ℝ) : ℝ := RademacherS4Assembly.p n h
def K (n : ℕ) (h : ℝ) : ℝ := RademacherS4Assembly.K n h

def b {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (s : ℝ) : ℝ :=
  RademacherS4Assembly.b B P hB s

def pathLaw (n : ℕ) : Measure (Shao.Path n) :=
  Measure.pi (fun _ : Fin n => RademacherCosine.law)

def V {n : ℕ} (a : Shao.Path n) : ℝ := Real.sqrt (Shao.energy a)

def selfNormalizedEvent (n : ℕ) (s : ℝ) : Set (Shao.Path n) :=
  {a | ∀ k : ℕ, k ≤ n → |Shao.prefixSum a k| ≤ s * V a}

def Q {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (c : ℝ) (n : ℕ) : ℝ :=
  p n (height c n) / b B P hB (x c n)

def QK {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (c : ℝ) (n : ℕ) : ℝ :=
  K n (height c n) / b B P hB (x c n)

def Qsource {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (c : ℝ) (n : ℕ) : ℝ :=
  (pathLaw n).real (selfNormalizedEvent n (x c n)) / b B P hB (x c n)

def shift {α : Type*} (f : ℕ → α) (J : ℕ) : ℕ → α :=
  RademacherS4Assembly.shift f J

def cubeSeq (j : ℕ) : ℕ := RademacherCriticalPhase.cubeIndex (j + 1)
def cubeMinusOneSeq (j : ℕ) : ℕ := RademacherCriticalPhase.belowCubeIndex (j + 2)
def upSeq (c : ℝ) (J : ℕ) (j : ℕ) : ℕ :=
  RademacherCriticalPhase.upIndex c (j + J)
def downSeq (c : ℝ) (J : ℕ) (j : ℕ) : ℕ :=
  RademacherCriticalPhase.downIndex c (j + J)
def nearestSeq (c α : ℝ) (J : ℕ) (j : ℕ) : ℕ :=
  RademacherCriticalPhase.nearestIndex c α (j + J)
def phaseSeq (c d : ℝ) (J : ℕ) (j : ℕ) : ℕ :=
  RademacherCriticalPhase.phaseIndex c d (j + J)

-- The endpoint offsets are reused, and the interior offset is at alpha = 1-d.
def phaseOffset (Ja Jb : ℕ) (Jα : ℝ → ℕ) (d : ℝ) : ℕ :=
  letI : DecidableEq ℝ := Classical.decEq ℝ
  if d = 0 then Jb else if d = 1 then Ja else Jα (1 - d)

def Cluster (z : ℕ → ℝ) : Set ℝ := RademacherCriticalPhase.Cluster z

-- Every predicate below is transparent and contains outputs only.
def PositiveTime (c : ℝ) (n : ℕ) : Prop :=
  1 ≤ n ∧ 0 < N n ∧ 0 < Real.sqrt (N n) ∧
  (Real.sqrt (N n)) ^ 2 = N n ∧ 0 < root n ∧ 0 < height c n ∧ 0 < x c n ∧
  height c n ^ 3 = c ^ 3 * N n ∧ N n / height c n ^ 3 = 1 / c ^ 3 ∧
  0 < 1 / c ^ 3 ∧ x c n = height c n / Real.sqrt (N n) ∧
  x c n * Real.sqrt (N n) = height c n

def ProbabilityLegal {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (c : ℝ) (n : ℕ) : Prop :=
  p n (height c n) = K n (height c n) ∧
  0 < p n (height c n) ∧ 0 < K n (height c n) ∧
  0 < b B P hB (x c n) ∧
  Q B P hB c n = QK B P hB c n ∧
  0 < Q B P hB c n ∧ 0 < QK B P hB c n ∧
  Qsource B P hB c n = Q B P hB c n ∧ 0 < Qsource B P hB c n

def LogIdentities {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (c : ℝ) (n : ℕ) : Prop :=
  Real.log (Q B P hB c n) =
    Real.log (p n (height c n)) - Real.log (b B P hB (x c n)) ∧
  Real.log (QK B P hB c n) =
    Real.log (K n (height c n)) - Real.log (b B P hB (x c n)) ∧
  Real.log (Q B P hB c n) = Real.log (QK B P hB c n) ∧
  Real.log (Qsource B P hB c n) = Real.log (Q B P hB c n)

def LegalAt {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (c : ℝ) (n : ℕ) : Prop :=
  PositiveTime c n ∧ RademacherCriticalPhase.WeakCell c n ∧
  ProbabilityLegal B P hB c n ∧ LogIdentities B P hB c n ∧
  RademacherS4Assembly.TimeLegal (phaseFloor c n) n (height c n) ∧
  RademacherS4Assembly.ProbabilityLegal B P hB (phaseFloor c n) n (height c n) ∧
  RademacherS4Assembly.LogIdentities B P hB (phaseFloor c n) n (height c n)

def ShiftedObjects {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (c : ℝ) (σ : ℕ → ℕ) (J j : ℕ) : Prop :=
  let n := σ (j + J)
  shift σ J j = n ∧
  height c (shift σ J j) = height c n ∧
  phaseFloor c (shift σ J j) = phaseFloor c n ∧
  delta c (shift σ J j) = delta c n ∧
  E c (shift σ J j) = E c n ∧ F c (shift σ J j) = F c n ∧
  p (shift σ J j) (height c (shift σ J j)) = p n (height c n) ∧
  K (shift σ J j) (height c (shift σ J j)) = K n (height c n) ∧
  x c (shift σ J j) = x c n ∧
  b B P hB (x c (shift σ J j)) = b B P hB (x c n) ∧
  Q B P hB c (shift σ J j) = Q B P hB c n ∧
  QK B P hB c (shift σ J j) = QK B P hB c n ∧
  Qsource B P hB c (shift σ J j) = Qsource B P hB c n ∧
  Real.log (Q B P hB c (shift σ J j)) = Real.log (Q B P hB c n) ∧
  Real.log (QK B P hB c (shift σ J j)) = Real.log (QK B P hB c n)

def TailS4Inputs (c : ℝ) (J : ℕ) : Prop :=
  (∀ j : ℕ,
    1 ≤ shift (phaseFloor c) J j ∧
    (shift (phaseFloor c) J j : ℝ) ≤ shift (height c) J j ∧
    shift (height c) J j < (shift (phaseFloor c) J j : ℝ) + 1) ∧
  Tendsto (shift (height c) J) atTop atTop ∧
  Tendsto (fun j : ℕ => N (shift (fun n : ℕ => n) J j) /
    (shift (height c) J j) ^ 2) atTop atTop ∧
  0 < 1 / c ^ 3 ∧
  (∀ j : ℕ, RademacherS4Assembly.scale3 (shift (fun n : ℕ => n) J j)
    (shift (height c) J j) = 1 / c ^ 3) ∧
  (∃ M : ℝ, 0 < M ∧ ∃ J_M : ℕ, ∀ j : ℕ, J_M ≤ j →
    RademacherS4Assembly.scale3 (shift (fun n : ℕ => n) J j)
      (shift (height c) J j) ≤ M)

def S4ReturnOutputs {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (c : ℝ) : Prop :=
  RademacherS4Assembly.S4Outputs B P hB
    (phaseFloor c) (fun n : ℕ => n) (height c) ∧
  ∀ J : ℕ, Ncell c ≤ J → TailS4Inputs c J ∧
    RademacherS4Assembly.S4Outputs B P hB
      (shift (phaseFloor c) J) (shift (fun n : ℕ => n) J) (shift (height c) J) ∧
    ∀ j : ℕ,
      ShiftedObjects B P hB c (fun n : ℕ => n) J j ∧
      RademacherS4Assembly.x (j + J) (height c (j + J)) = x c (j + J) ∧
      RademacherS4Assembly.delta (phaseFloor c (j + J)) (height c (j + J)) =
        delta c (j + J) ∧
      RademacherS4Assembly.w (phaseFloor c (j + J)) (j + J) (height c (j + J)) =
        E c (j + J) ∧
      RademacherS4Assembly.Q B P hB (j + J) (height c (j + J)) = Q B P hB c (j + J) ∧
      RademacherS4Assembly.QK B P hB (j + J) (height c (j + J)) = QK B P hB c (j + J)

def MainLimits {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (c : ℝ) : Prop :=
  Tendsto (fun n : ℕ => Real.log (Q B P hB c n) - E c n) atTop (𝓝 (0 : ℝ)) ∧
  Tendsto (fun n : ℕ => Real.log (QK B P hB c n) - E c n) atTop (𝓝 (0 : ℝ)) ∧
  Tendsto (fun n : ℕ => Q B P hB c n / F c n) atTop (𝓝 (1 : ℝ)) ∧
  Tendsto (fun n : ℕ => QK B P hB c n / F c n) atTop (𝓝 (1 : ℝ)) ∧
  Tendsto (fun n : ℕ => Q B P hB c n - F c n) atTop (𝓝 (0 : ℝ)) ∧
  Tendsto (fun n : ℕ => QK B P hB c n - F c n) atTop (𝓝 (0 : ℝ))

def MainOutputs {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (c : ℝ) : Prop :=
  MainLimits B P hB c ∧
  ∃ Npos : ℕ, Ncell c ≤ Npos ∧
    (∀ n : ℕ, Npos ≤ n → LegalAt B P hB c n) ∧
    (∀ ε : ℝ, 0 < ε → ∃ Nε : ℕ, Npos ≤ Nε ∧
      ∀ n : ℕ, Nε ≤ n → LegalAt B P hB c n ∧
        |Real.log (Q B P hB c n) - coeff c * delta c n| < ε ∧
        |Real.log (QK B P hB c n) - coeff c * delta c n| < ε)

def CPPhaseOutputs (c : ℝ) (σ : ℕ → ℕ) (d : ℝ) : Prop :=
  StrictMono σ ∧
  (∀ j : ℕ, Ncell c ≤ σ j ∧ RademacherCriticalPhase.WeakCell c (σ j) ∧
    1 ≤ σ j ∧ 0 < height c (σ j) ∧
    N (σ j) / height c (σ j) ^ 3 = 1 / c ^ 3 ∧ 0 < 1 / c ^ 3) ∧
  Tendsto (fun j : ℕ => delta c (σ j)) atTop (𝓝 d) ∧
  Tendsto (fun j : ℕ => E c (σ j)) atTop (𝓝 (coeff c * d)) ∧
  Tendsto (fun j : ℕ => F c (σ j)) atTop (𝓝 (Real.exp (coeff c * d)))

def PhaseLimits {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (c : ℝ) (σ : ℕ → ℕ) (d : ℝ) : Prop :=
  CPPhaseOutputs c σ d ∧
  (∃ Jpos : ℕ, ∀ j : ℕ, Jpos ≤ j → LegalAt B P hB c (σ j)) ∧
  Tendsto (fun j : ℕ => Real.log (Q B P hB c (σ j))) atTop (𝓝 (coeff c * d)) ∧
  Tendsto (fun j : ℕ => Real.log (QK B P hB c (σ j))) atTop (𝓝 (coeff c * d)) ∧
  Tendsto (fun j : ℕ => Q B P hB c (σ j)) atTop (𝓝 (Real.exp (coeff c * d))) ∧
  Tendsto (fun j : ℕ => QK B P hB c (σ j)) atTop (𝓝 (Real.exp (coeff c * d))) ∧
  Tendsto (fun j : ℕ => Qsource B P hB c (σ j)) atTop (𝓝 (Real.exp (coeff c * d)))

def PhaseOutputs {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (c : ℝ) (σ : ℕ → ℕ) (d : ℝ) : Prop :=
  PhaseLimits B P hB c σ d ∧
  ∀ J : ℕ, PhaseLimits B P hB c (shift σ J) d ∧
    ∀ j : ℕ, ShiftedObjects B P hB c σ J j

theorem definition_bridges {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (c : ℝ) (n : ℕ) (s : ℝ) :
    N n = (n : ℝ) ∧ root n = Real.rpow (n : ℝ) ((1 : ℝ) / 3) ∧
    height c n = c * root n ∧ phaseFloor c n = Nat.floor (height c n) ∧
    upperHeight c n = (phaseFloor c n : ℝ) + 1 ∧
    delta c n = upperHeight c n - height c n ∧ coeff c = Real.pi ^ 2 / (4 * c ^ 3) ∧
    E c n = coeff c * delta c n ∧ F c n = Real.exp (E c n) ∧
    Ncell c = max 1 (Nat.ceil (1 / c ^ 3)) ∧
    RademacherCosine.law =
      (1 / 2 : ENNReal) • Measure.dirac (1 : ℝ) +
      (1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ) ∧
    p n s = (pathLaw n).real (@Shao.closedStrip n s) ∧
    K n s = @Shao.OQ4.killedMass RademacherCosine.law
      RademacherCosine.law_isProbabilityMeasure s n (0 : ℝ) ∧
    b B P hB s = Shao.Probability.BrownianSup.probability B P hB s ∧
    b B P hB s = P.real {ω | Shao.Probability.BrownianSup.U B P hB ω ≤ s} ∧
    b B P hB s = P.real (Shao.Probability.BrownianSup.fullStrip B s) ∧
    (∀ a : Shao.Path n, V a = Real.sqrt (∑ i : Fin n, (a i) ^ 2)) ∧
    Cluster (Q B P hB c) =
      {L : ℝ | ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun j : ℕ => Q B P hB c (σ j)) atTop (𝓝 L)} := by
  /- -/

theorem zero_time (c : ℝ) :
    root 0 = 0 ∧ height c 0 = 0 ∧ phaseFloor c 0 = 0 ∧
    upperHeight c 0 = 1 ∧ delta c 0 = 1 ∧
    (∀ a : Shao.Path 0, Shao.energy a = 0 ∧ V a = 0) ∧
    selfNormalizedEvent 0 (x c 0) = Set.univ ∧
    p 0 (height c 0) = 1 ∧ K 0 (height c 0) = 1 := by
  /- -/

theorem positive_time {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) :
    PositiveTime c n := by
  /- -/

theorem actual_path_energy (n : ℕ) :
    IsProbabilityMeasure (pathLaw n) ∧
    (∀ᵐ a ∂(pathLaw n),
      (∀ i : Fin n, a i = 1 ∨ a i = -1) ∧
      Shao.energy a = N n ∧ V a = Real.sqrt (N n)) := by
  /- -/

theorem actual_source_event {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) :
    MeasurableSet (selfNormalizedEvent n (x c n)) ∧
    MeasurableSet (@Shao.closedStrip n (height c n)) ∧
    (∀ᵐ a ∂(pathLaw n),
      V a = Real.sqrt (N n) ∧
      (a ∈ selfNormalizedEvent n (x c n) ↔ a ∈ @Shao.closedStrip n (height c n))) ∧
    (pathLaw n).real (selfNormalizedEvent n (x c n)) = p n (height c n) ∧
    Qsource B P hB c n = Q B P hB c n := by
  /- -/

theorem positive_time_S4_bridges {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) :
    upperHeight c n = RademacherS4Assembly.H (phaseFloor c n) ∧
    delta c n = RademacherS4Assembly.delta (phaseFloor c n) (height c n) ∧
    RademacherS4Assembly.scale3 n (height c n) = 1 / c ^ 3 ∧
    RademacherS4Assembly.x n (height c n) = x c n ∧
    RademacherS4Assembly.w (phaseFloor c n) n (height c n) = E c n ∧
    RademacherS4Assembly.Q B P hB n (height c n) = Q B P hB c n ∧
    RademacherS4Assembly.QK B P hB n (height c n) = QK B P hB c n := by
  /- -/

theorem S5_DOM {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) :
    1 ≤ Ncell c ∧
    (∀ n : ℕ, Ncell c ≤ n → PositiveTime c n ∧
      RademacherCriticalPhase.WeakCell c n ∧
      (∀ z : ℤ, height c n = (z : ℝ) → delta c n = 1)) ∧
    0 < coeff c ∧ (∀ n : ℕ, 0 < F c n ∧ F c n ≤ Real.exp (coeff c)) ∧
    Tendsto (height c) atTop atTop ∧
    Tendsto (fun n : ℕ => N n / height c n ^ 2) atTop atTop ∧
    Tendsto (x c) atTop (𝓝 (0 : ℝ)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ Nε : ℕ, ∀ n : ℕ, Nε ≤ n → 0 < x c n ∧ x c n < ε) ∧
    (∃ Npos : ℕ, Ncell c ≤ Npos ∧ ∀ n : ℕ, Npos ≤ n → LegalAt B P hB c n) := by
  /- -/

-- The input cell is eventual. Every all-j use is on this same shifted tail.
theorem S5_S4_EVENTUAL {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) :
    S4ReturnOutputs B P hB c := by
  /- -/

theorem S5_MAIN {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) :
    MainOutputs B P hB c := by
  /- -/

theorem S5_CUBE_GEOMETRY :
    StrictMono cubeSeq ∧ StrictMono cubeMinusOneSeq ∧
    (∀ j : ℕ, Ncell 1 ≤ cubeSeq j ∧ RademacherCriticalPhase.WeakCell 1 (cubeSeq j) ∧
      height 1 (cubeSeq j) = ((j + 1 : ℕ) : ℝ) ∧
      phaseFloor 1 (cubeSeq j) = j + 1 ∧
      upperHeight 1 (cubeSeq j) = ((j + 1 : ℕ) : ℝ) + 1 ∧ delta 1 (cubeSeq j) = 1) ∧
    (∀ j : ℕ, 1 ≤ cubeMinusOneSeq j ∧ Ncell 1 ≤ cubeMinusOneSeq j ∧
      (cubeMinusOneSeq j : ℤ) = ((j + 2 : ℕ) : ℤ) ^ 3 - 1 ∧
      (cubeMinusOneSeq j : ℝ) = ((j + 2 : ℕ) : ℝ) ^ 3 - 1 ∧
      ((j + 2 - 1 : ℕ) : ℤ) = ((j + 2 : ℕ) : ℤ) - 1 ∧
      ((j + 2 - 1 : ℕ) : ℝ) = ((j + 2 : ℕ) : ℝ) - 1 ∧
      RademacherCriticalPhase.WeakCell 1 (cubeMinusOneSeq j) ∧
      ((j + 2 : ℕ) : ℝ) - 1 < height 1 (cubeMinusOneSeq j) ∧
      height 1 (cubeMinusOneSeq j) < ((j + 2 : ℕ) : ℝ) ∧
      phaseFloor 1 (cubeMinusOneSeq j) = j + 2 - 1 ∧
      upperHeight 1 (cubeMinusOneSeq j) = ((j + 2 : ℕ) : ℝ) ∧
      delta 1 (cubeMinusOneSeq j) = ((j + 2 : ℕ) : ℝ) - height 1 (cubeMinusOneSeq j)) := by
  /- -/

theorem S5_CUBE {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    coeff 1 = Real.pi ^ 2 / 4 ∧
    PhaseOutputs B P hB 1 cubeSeq 1 ∧
    PhaseOutputs B P hB 1 cubeMinusOneSeq 0 ∧
    (∀ α : ℝ, 0 < α → α < 1 → ∃ Jα : ℕ, 2 ≤ Jα ∧
      PhaseOutputs B P hB 1 (nearestSeq 1 α Jα) (1 - α)) := by
  /- -/

theorem S5_ROUNDING {c : ℝ} (hc : 0 < c) :
    RademacherCriticalPhase.upIndex c 0 = 0 ∧
    RademacherCriticalPhase.downIndex c 0 = 0 ∧
    (∀ k : ℕ,
      0 ≤ (RademacherCriticalPhase.upIndex c k : ℝ) - RademacherCriticalPhase.target c 0 k ∧
      (RademacherCriticalPhase.upIndex c k : ℝ) - RademacherCriticalPhase.target c 0 k < 1) ∧
    (∀ k : ℕ, 1 ≤ k → 1 ≤ RademacherCriticalPhase.upIndex c k ∧
      (RademacherCriticalPhase.downIndex c k : ℤ) =
        (RademacherCriticalPhase.upIndex c k : ℤ) - 1 ∧
      (RademacherCriticalPhase.downIndex c k : ℝ) =
        (RademacherCriticalPhase.upIndex c k : ℝ) - 1 ∧
      -1 ≤ (RademacherCriticalPhase.downIndex c k : ℝ) - RademacherCriticalPhase.target c 0 k ∧
      (RademacherCriticalPhase.downIndex c k : ℝ) - RademacherCriticalPhase.target c 0 k < 0) ∧
    (∀ α : ℝ, 0 < α → α < 1 → ∀ k : ℕ,
      -(1 / 2 : ℝ) < (RademacherCriticalPhase.nearestIndex c α k : ℝ) -
        RademacherCriticalPhase.target c α k ∧
      (RademacherCriticalPhase.nearestIndex c α k : ℝ) -
        RademacherCriticalPhase.target c α k ≤ 1 / 2 ∧
      |(RademacherCriticalPhase.nearestIndex c α k : ℝ) -
        RademacherCriticalPhase.target c α k| ≤ 1 / 2 ∧
      (∀ l : ℕ, RademacherCriticalPhase.target c α k = (l : ℝ) + 1 / 2 →
        RademacherCriticalPhase.nearestIndex c α k = l + 1)) := by
  /- -/

theorem phase_index_bridges (c d : ℝ) (k : ℕ) :
    RademacherCriticalPhase.target c 0 k = ((k : ℝ) / c) ^ 3 ∧
    (∀ α : ℝ, RademacherCriticalPhase.target c α k = (((k : ℝ) + α) / c) ^ 3) ∧
    RademacherCriticalPhase.upIndex c k = Nat.ceil (RademacherCriticalPhase.target c 0 k) ∧
    RademacherCriticalPhase.downIndex c k = Nat.ceil (RademacherCriticalPhase.target c 0 k) - 1 ∧
    (∀ α : ℝ, RademacherCriticalPhase.nearestIndex c α k =
      Nat.floor (RademacherCriticalPhase.target c α k + (1 : ℝ) / 2)) ∧
    (d = 0 → RademacherCriticalPhase.phaseIndex c d k = RademacherCriticalPhase.downIndex c k) ∧
    (d = 1 → RademacherCriticalPhase.phaseIndex c d k = RademacherCriticalPhase.upIndex c k) ∧
    (0 < d → d < 1 → RademacherCriticalPhase.phaseIndex c d k =
      RademacherCriticalPhase.nearestIndex c (1 - d) k) := by
  /- -/

-- A single family of offsets serves endpoints, alpha phases, and CP3 phases.
-- PhaseOutputs synchronizes every additional common cutoff on all quantities.
theorem S5_PHASE {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) :
    ∃ Ja Jb : ℕ, ∃ Jα : ℝ → ℕ,
      2 ≤ Ja ∧ 2 ≤ Jb ∧
      PhaseOutputs B P hB c (upSeq c Ja) 1 ∧
      PhaseOutputs B P hB c (downSeq c Jb) 0 ∧
      (∀ j : ℕ, 1 ≤ RademacherCriticalPhase.upIndex c (j + Jb) ∧
        (downSeq c Jb j : ℤ) = (RademacherCriticalPhase.upIndex c (j + Jb) : ℤ) - 1 ∧
        (downSeq c Jb j : ℝ) = (RademacherCriticalPhase.upIndex c (j + Jb) : ℝ) - 1) ∧
      (∀ α : ℝ, 0 < α → α < 1 → 2 ≤ Jα α ∧
        PhaseOutputs B P hB c (nearestSeq c α (Jα α)) (1 - α)) ∧
      (∀ d : ℝ, d ∈ Set.Icc (0 : ℝ) 1 →
        2 ≤ phaseOffset Ja Jb Jα d ∧
        PhaseOutputs B P hB c (phaseSeq c d (phaseOffset Ja Jb Jα d)) d ∧
        (d = 0 → phaseSeq c d (phaseOffset Ja Jb Jα d) = downSeq c Jb) ∧
        (d = 1 → phaseSeq c d (phaseOffset Ja Jb Jα d) = upSeq c Ja) ∧
        (0 < d → d < 1 → phaseSeq c d (phaseOffset Ja Jb Jα d) =
          nearestSeq c (1 - d) (Jα (1 - d)))) := by
  /- -/

theorem S5_CLUSTER_BOUND_Q {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c)
    {τ : ℕ → ℕ} (hτ : StrictMono τ) {L : ℝ}
    (hL : Tendsto (fun j : ℕ => Q B P hB c (τ j)) atTop (𝓝 L)) :
    L ∈ Set.Icc (1 : ℝ) (Real.exp (coeff c)) ∧
    (∀ᶠ j in atTop, Ncell c ≤ τ j ∧ LegalAt B P hB c (τ j)) ∧
    Tendsto (fun j : ℕ => QK B P hB c (τ j)) atTop (𝓝 L) := by
  /- -/

theorem S5_CLUSTER_BOUND_QK {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c)
    {τ : ℕ → ℕ} (hτ : StrictMono τ) {L : ℝ}
    (hL : Tendsto (fun j : ℕ => QK B P hB c (τ j)) atTop (𝓝 L)) :
    L ∈ Set.Icc (1 : ℝ) (Real.exp (coeff c)) ∧
    (∀ᶠ j in atTop, Ncell c ≤ τ j ∧ LegalAt B P hB c (τ j)) ∧
    Tendsto (fun j : ℕ => Q B P hB c (τ j)) atTop (𝓝 L) := by
  /- -/

theorem S5_CLUSTER_REALIZE {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) {L : ℝ}
    (hL : L ∈ Set.Icc (1 : ℝ) (Real.exp (coeff c))) :
    ∃ d : ℝ, d ∈ Set.Icc (0 : ℝ) 1 ∧ L = Real.exp (coeff c * d) ∧
      ∃ J : ℕ, 2 ≤ J ∧ PhaseOutputs B P hB c (phaseSeq c d J) d ∧
        Tendsto (fun j : ℕ => Q B P hB c (phaseSeq c d J j)) atTop (𝓝 L) ∧
        Tendsto (fun j : ℕ => QK B P hB c (phaseSeq c d J j)) atTop (𝓝 L) := by
  /- -/

theorem S5_CLUSTER {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) :
    Cluster (Q B P hB c) = Cluster (QK B P hB c) ∧
    Cluster (Q B P hB c) = Set.Icc (1 : ℝ) (Real.exp (coeff c)) ∧
    Cluster (QK B P hB c) = Set.Icc (1 : ℝ) (Real.exp (coeff c)) := by
  /- -/

theorem S5_NOT_CONVERGENT {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) :
    0 < coeff c ∧ 1 < Real.exp (coeff c) ∧
    (¬ ∃ L : ℝ, Tendsto (Q B P hB c) atTop (𝓝 L)) ∧
    (¬ ∃ L : ℝ, Tendsto (QK B P hB c) atTop (𝓝 L)) := by
  /- -/

theorem S5_UNIT_CLUSTER {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    Cluster (Q B P hB 1) = Set.Icc (1 : ℝ) (Real.exp (Real.pi ^ 2 / 4)) ∧
    Cluster (QK B P hB 1) = Set.Icc (1 : ℝ) (Real.exp (Real.pi ^ 2 / 4)) ∧
    (¬ ∃ L : ℝ, Tendsto (Q B P hB 1) atTop (𝓝 L)) ∧
    (¬ ∃ L : ℝ, Tendsto (QK B P hB 1) atTop (𝓝 L)) := by
  /- -/

end Shao.OQ4.RademacherS5Assembly

end
