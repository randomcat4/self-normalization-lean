import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Choose
import Aesop
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Constructions.Pi
import Shao.OQ4.RademacherCriticalPhase
import Shao.OQ4.RademacherS4Assembly
import Shao.Probability.FiniteIID
import Shao.Probability.MeasurablePath
import Shao.Basic.ClosedSurvival
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Local proof source for the exact accepted S5 public interface.
Public declarations are unchanged. This source has not been run through Lean.
S4 import and all native checks remain pendingformalplacement / pending.
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

attribute [elab_without_expected_type] shift

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
  have hb := RademacherS4Assembly.actual_brownian_bridges B P hB s
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [b] using hb.1
  · simpa only [b] using hb.2.1
  · simpa only [b] using hb.2.2.1
  · intro a
    rfl
  · rfl

theorem zero_time (c : ℝ) :
    root 0 = 0 ∧ height c 0 = 0 ∧ phaseFloor c 0 = 0 ∧
    upperHeight c 0 = 1 ∧ delta c 0 = 1 ∧
    (∀ a : Shao.Path 0, Shao.energy a = 0 ∧ V a = 0) ∧
    selfNormalizedEvent 0 (x c 0) = Set.univ ∧
    p 0 (height c 0) = 1 ∧ K 0 (height c 0) = 1 := by
  have hz : ∀ a : Shao.Path 0, Shao.energy a = 0 ∧ V a = 0 := by
    intro a
    simp [Shao.energy, V]
  have he : selfNormalizedEvent 0 (x c 0) = Set.univ := by
    ext a
    simp [selfNormalizedEvent, Shao.prefixSum, V, Shao.energy]
  have hp : p 0 (height c 0) = 1 := by
    simp [p, RademacherS4Assembly.p, RademacherS3Assembly.p,
      RademacherS2Assembly.p, height, RademacherCriticalPhase.height,
      RademacherCriticalPhase.root, Shao.closedStrip, Shao.prefixSum]
  have hK : K 0 (height c 0) = 1 := by
    simp [K, RademacherS4Assembly.K, RademacherS3Assembly.K,
      RademacherS2Assembly.K, Shao.OQ4.killedMass,
      Shao.OQ4.killedAction_zero]
  have hcp := RademacherCriticalPhase.zero_prefix c
  exact ⟨hcp.1, hcp.2.1, hcp.2.2.1, hcp.2.2.2.1,
    hcp.2.2.2.2.1, hz, he, hp, hK⟩

theorem positive_time {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) :
    PositiveTime c n := by
  rcases RademacherCriticalPhase.positive_time hc hn with
    ⟨hr, hh, hcube, hratio, hthird⟩
  have hN : 0 < N n := by
    change 0 < (n : ℝ)
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hs : 0 < Real.sqrt (N n) := Real.sqrt_pos.2 hN
  have hx : 0 < x c n := mul_pos hc (Real.rpow_pos_of_pos hN _)
  have hmul : x c n * Real.sqrt (N n) = height c n := by
    change (c * Real.rpow (n : ℝ) (-((1 : ℝ) / 6))) *
      Real.sqrt (n : ℝ) = c * Real.rpow (n : ℝ) ((1 : ℝ) / 3)
    rw [Real.sqrt_eq_rpow, mul_assoc]
    change c * ((n : ℝ) ^ (-((1 : ℝ) / 6)) * (n : ℝ) ^ ((1 : ℝ) / 2)) =
      c * (n : ℝ) ^ ((1 : ℝ) / 3)
    rw [← Real.rpow_add (show (0 : ℝ) < (n : ℝ) from hN)]
    norm_num
  have hdiv : x c n = height c n / Real.sqrt (N n) :=
    (eq_div_iff hs.ne').2 hmul
  exact ⟨hn, hN, hs, Real.sq_sqrt hN.le, hr, hh, hx, hcube, hratio,
    hthird, hdiv, hmul⟩

theorem actual_path_energy (n : ℕ) :
    IsProbabilityMeasure (pathLaw n) ∧
    (∀ᵐ a ∂(pathLaw n),
      (∀ i : Fin n, a i = 1 ∨ a i = -1) ∧
      Shao.energy a = N n ∧ V a = Real.sqrt (N n)) := by
  classical
  have hp : IsProbabilityMeasure (pathLaw n) := by
    unfold pathLaw
    infer_instance
  have hsingle : ∀ᵐ z ∂RademacherCosine.law, z = 1 ∨ z = -1 := by
    rw [ae_iff]
    simp [RademacherCosine.law, RademacherCosine.halfENNReal,
      Measure.add_apply, Measure.smul_apply]
  have hcoord (i : Fin n) : ∀ᵐ a ∂(pathLaw n), a i = 1 ∨ a i = -1 := by
    rw [ae_iff] at hsingle ⊢
    exact Measure.pi_eval_preimage_null (fun _ : Fin n => RademacherCosine.law) (i := i) hsingle
  have hall : ∀ᵐ a ∂(pathLaw n), ∀ i : Fin n, a i = 1 ∨ a i = -1 :=
    (ae_all_iff).2 hcoord
  refine ⟨hp, ?_⟩
  filter_upwards [hall] with a ha
  have hsq (i : Fin n) : (a i) ^ 2 = (1 : ℝ) := by
    rcases ha i with h | h <;> simp [h]
  have henergy : Shao.energy a = N n := by
    simp [Shao.energy, hsq, N, RademacherS4Assembly.N,
      RademacherS3Assembly.N, RademacherS2Assembly.N]
  exact ⟨ha, henergy, by simp only [V, henergy]⟩

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
  have hself : MeasurableSet (selfNormalizedEvent n (x c n)) := by
    simp only [selfNormalizedEvent, Set.setOf_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_le (Shao.continuous_prefixSum k).abs.measurable
        (by simpa only [V] using (Shao.continuous_energyWall (x c n)).measurable)
  have hstrip : MeasurableSet (@Shao.closedStrip n (height c n)) := by
    simp only [Shao.closedStrip, Set.setOf_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_le (Shao.continuous_prefixSum k).abs.measurable measurable_const
  have hmul : x c n * Real.sqrt (N n) = height c n := (positive_time hc hn).2.2.2.2.2.2.2.2.2.2.2
  have hae : ∀ᵐ a ∂(pathLaw n), V a = Real.sqrt (N n) ∧
      (a ∈ selfNormalizedEvent n (x c n) ↔ a ∈ @Shao.closedStrip n (height c n)) := by
    filter_upwards [(actual_path_energy n).2] with a ha
    refine ⟨ha.2.2, ?_⟩
    simp only [selfNormalizedEvent, Shao.closedStrip, Set.mem_setOf_eq, ha.2.2, hmul]
  have hsets : selfNormalizedEvent n (x c n) =ᵐ[pathLaw n]
      @Shao.closedStrip n (height c n) := by
    filter_upwards [hae] with a ha
    exact propext ha.2
  have heq : (pathLaw n).real (selfNormalizedEvent n (x c n)) = p n (height c n) := by
    change ((pathLaw n) (selfNormalizedEvent n (x c n))).toReal =
      ((pathLaw n) (@Shao.closedStrip n (height c n))).toReal
    exact congrArg ENNReal.toReal (measure_congr hsets)
  exact ⟨hself, hstrip, hae, heq, by simp only [Qsource, Q, heq]⟩

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
  have hd := RademacherS4Assembly.definition_bridges (phaseFloor c n) n (height c n)
  have hH : upperHeight c n = RademacherS4Assembly.H (phaseFloor c n) := by
    simpa only [upperHeight, RademacherCriticalPhase.upperHeight, phaseFloor]
      using hd.1.symm
  have hδdef : RademacherS4Assembly.delta (phaseFloor c n) (height c n) =
      RademacherS4Assembly.H (phaseFloor c n) - height c n := by aesop
  have hδ : delta c n = RademacherS4Assembly.delta (phaseFloor c n) (height c n) := by
    rw [hδdef, ← hH]
    rfl
  have hsdef : RademacherS4Assembly.scale3 n (height c n) = N n / height c n ^ 3 := by
    change RademacherS4Assembly.scale3 n (height c n) =
      RademacherS4Assembly.N n / height c n ^ 3
    aesop
  have hxdef : RademacherS4Assembly.x n (height c n) = height c n / Real.sqrt (N n) := by
    change RademacherS4Assembly.x n (height c n) =
      height c n / Real.sqrt (RademacherS4Assembly.N n)
    aesop
  rcases positive_time hc hn with
    ⟨_, _, _, _, _, _, _, _, hthird, _, hxdiv, _⟩
  have hs : RademacherS4Assembly.scale3 n (height c n) = 1 / c ^ 3 := by
    rw [hsdef, hthird]
  have hx : RademacherS4Assembly.x n (height c n) = x c n := hxdef.trans hxdiv.symm
  have hwdef : RademacherS4Assembly.w (phaseFloor c n) n (height c n) =
      (Real.pi ^ 2 / 4) * (N n / height c n ^ 3) *
        (RademacherS4Assembly.H (phaseFloor c n) - height c n) := by
    change RademacherS4Assembly.w (phaseFloor c n) n (height c n) =
      (Real.pi ^ 2 / 4) * (RademacherS4Assembly.N n / height c n ^ 3) *
        (RademacherS4Assembly.H (phaseFloor c n) - height c n)
    aesop
  have hw : RademacherS4Assembly.w (phaseFloor c n) n (height c n) = E c n := by
    rw [hwdef, hthird, ← hH]
    change (Real.pi ^ 2 / 4) * (1 / c ^ 3) * delta c n =
      (Real.pi ^ 2 / (4 * c ^ 3)) * delta c n
    field_simp [hc.ne'] <;> ring
  refine ⟨hH, hδ, hs, hx, hw, ?_, ?_⟩
  · simp only [RademacherS4Assembly.Q, Q, p, b, hx]
  · simp only [RademacherS4Assembly.QK, QK, K, b, hx]


private theorem critical_inputs {c : ℝ} (hc : 0 < c) :
    (∃ J : ℕ, ∀ n : ℕ, J ≤ n →
      1 ≤ phaseFloor c n ∧ (phaseFloor c n : ℝ) ≤ height c n ∧
        height c n < (phaseFloor c n : ℝ) + 1) ∧
    Tendsto (height c) atTop atTop ∧
    Tendsto (fun n : ℕ => N n / height c n ^ 2) atTop atTop ∧
    (∃ M : ℝ, 0 < M ∧ ∃ J : ℕ, ∀ n : ℕ, J ≤ n →
      RademacherS4Assembly.scale3 n (height c n) ≤ M) := by
  rcases RademacherCriticalPhase.cutoff_spec hc with ⟨hcut, hcell⟩
  rcases RademacherCriticalPhase.scales hc with ⟨hh, h2⟩
  refine ⟨⟨Ncell c, ?_⟩, hh, h2, 1 / c ^ 3, by positivity, 1, ?_⟩
  · intro n hn
    rcases hcell n hn with ⟨_, hm, hmh, hhm, _⟩
    exact ⟨hm, hmh, hhm⟩
  · intro n hn
    have hd := RademacherS4Assembly.definition_bridges (phaseFloor c n) n (height c n)
    have hscale : RademacherS4Assembly.scale3 n (height c n) = N n / height c n ^ 3 := by
      change RademacherS4Assembly.scale3 n (height c n) =
        RademacherS4Assembly.N n / height c n ^ 3
      aesop
    rcases positive_time hc hn with ⟨_, _, _, _, _, _, _, _, hthird, _⟩
    exact (hscale.trans hthird).le

private theorem actual_s4 {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) :
    RademacherS4Assembly.S4Outputs B P hB (phaseFloor c) (fun n : ℕ => n) (height c) := by
  rcases critical_inputs hc with ⟨hcell, hh, h2, h3⟩
  exact RademacherS4Assembly.S4_EVENTUAL B P hB (phaseFloor c)
    (fun n : ℕ => n) (height c) hcell hh h2 h3

private theorem legal_of_s4 {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) {n : ℕ}
    (hn : 1 ≤ n) (hcell : RademacherCriticalPhase.WeakCell c n)
    (ht : RademacherS4Assembly.TimeLegal (phaseFloor c n) n (height c n))
    (hp : RademacherS4Assembly.ProbabilityLegal B P hB (phaseFloor c n) n (height c n))
    (hl : RademacherS4Assembly.LogIdentities B P hB (phaseFloor c n) n (height c n)) :
    LegalAt B P hB c n := by
  rcases positive_time_S4_bridges B P hB hc hn with ⟨_, _, _, hx, _, hQ, hQK⟩
  have hs := (actual_source_event B P hB hc hn).2.2.2.2
  have hp0 := hp
  rcases hp0 with ⟨_, _, _, _, _, _, _, _, hpK, hpp, hKp, _, hbp, _, _, hQQK, hQp, hQKp⟩
  have hreal : ProbabilityLegal B P hB c n := by
    refine ⟨hpK, hpp, hKp, ?_, ?_, ?_, ?_, hs, ?_⟩
    · simpa only [b, hx] using hbp
    · simpa only [hQ, hQK] using hQQK
    · simpa only [hQ] using hQp
    · simpa only [hQK] using hQKp
    · rw [hs]
      simpa only [hQ] using hQp
  have hlogs : LogIdentities B P hB c n := by
    rcases hl with ⟨hlQ, hlK, _⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [hQ, hx, p, b] using hlQ
    · simpa only [hQK, hx, K, b] using hlK
    · rw [hreal.2.2.2.2.1]
    · rw [hs]
  exact ⟨positive_time hc hn, hcell, hreal, hlogs, ht, hp, hl⟩

private theorem ratio_from_log_error (c : ℝ) (z : ℕ → ℝ)
    (hz : ∀ᶠ n in atTop, 0 < z n)
    (he : Tendsto (fun n : ℕ => Real.log (z n) - E c n) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n : ℕ => z n / F c n) atTop (𝓝 (1 : ℝ)) := by
  have h := Real.continuous_exp.continuousAt.tendsto.comp he
  have heq : (fun n : ℕ => Real.exp (Real.log (z n) - E c n)) =ᶠ[atTop]
      (fun n : ℕ => z n / F c n) := by
    filter_upwards [hz] with n hn
    rw [Real.exp_sub, Real.exp_log hn]
    rfl
  have hexp : Tendsto (fun n : ℕ => Real.exp (Real.log (z n) - E c n))
      atTop (𝓝 (1 : ℝ)) := by simpa only [Real.exp_zero, Function.comp_def] using h
  exact hexp.congr' heq

private theorem difference_from_ratio {c : ℝ} (hc : 0 < c) (z : ℕ → ℝ)
    (hz : Tendsto (fun n : ℕ => z n / F c n) atTop (𝓝 (1 : ℝ))) :
    Tendsto (fun n : ℕ => z n - F c n) atTop (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hB : 0 < Real.exp (coeff c) := Real.exp_pos _
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.1 hz (ε / Real.exp (coeff c)) (div_pos hε hB)
  refine ⟨J, ?_⟩
  intro n hn
  have hphase := RademacherCriticalPhase.finite_phase hc n
  have hF : 0 < F c n := Real.exp_pos _
  have hFb : F c n ≤ Real.exp (coeff c) := by aesop
  have hrat : |z n / F c n - 1| < ε / Real.exp (coeff c) := by
    simpa only [Real.dist_eq] using hJ n hn
  have hid : z n - F c n = F c n * (z n / F c n - 1) := by
    field_simp [hF.ne']
    <;> ring
  rw [Real.dist_eq, sub_zero, hid, abs_mul, abs_of_pos hF]
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right hFb (abs_nonneg _))
  simpa only [mul_comm] using (lt_div_iff₀ hB).1 hrat

private theorem main_outputs_proof {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) :
    MainOutputs B P hB c := by
  rcases actual_s4 B P hB hc with
    ⟨_, _, _, _, _, _, _, he, heK, Jtime, Jpos, hord, htime, hpos, _⟩
  let Npos := max (Ncell c) (max 1 (max Jtime Jpos))
  have hcell := (RademacherCriticalPhase.cutoff_spec hc).2
  have hlegal : ∀ n : ℕ, Npos ≤ n → LegalAt B P hB c n := by
    intro n hn
    have hnc : Ncell c ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := by dsimp [Npos] at hn; omega
    have hnt : Jtime ≤ n := by dsimp [Npos] at hn; omega
    have hnp : Jpos ≤ n := by dsimp [Npos] at hn; omega
    exact legal_of_s4 B P hB hc hn1 (hcell n hnc)
      (htime n hnt) (hpos n hnp).1 (hpos n hnp).2.1
  have heQ : Tendsto (fun n : ℕ => Real.log (Q B P hB c n) - E c n)
      atTop (𝓝 (0 : ℝ)) := by
    apply he.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rcases positive_time_S4_bridges B P hB hc hn with ⟨_, _, _, _, hw, hQ, _⟩
    rw [hw, hQ]
  have heQK : Tendsto (fun n : ℕ => Real.log (QK B P hB c n) - E c n)
      atTop (𝓝 (0 : ℝ)) := by
    apply heK.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rcases positive_time_S4_bridges B P hB hc hn with ⟨_, _, _, _, hw, _, hQK⟩
    rw [hw, hQK]
  have hz : ∀ᶠ n in atTop, 0 < Q B P hB c n := by
    filter_upwards [eventually_ge_atTop Npos] with n hn
    exact (hlegal n hn).2.2.1.2.2.2.2.2.1
  have hzK : ∀ᶠ n in atTop, 0 < QK B P hB c n := by
    filter_upwards [eventually_ge_atTop Npos] with n hn
    exact (hlegal n hn).2.2.1.2.2.2.2.2.2.1
  have hr := ratio_from_log_error c (Q B P hB c) hz heQ
  have hrK := ratio_from_log_error c (QK B P hB c) hzK heQK
  refine ⟨⟨heQ, heQK, hr, hrK, difference_from_ratio hc _ hr,
    difference_from_ratio hc _ hrK⟩, Npos, le_max_left _ _, hlegal, ?_⟩
  intro ε hε
  obtain ⟨JQ, hJQ⟩ := Metric.tendsto_atTop.1 heQ ε hε
  obtain ⟨JK, hJK⟩ := Metric.tendsto_atTop.1 heQK ε hε
  refine ⟨max Npos (max JQ JK), le_max_left _ _, ?_⟩
  intro n hn
  refine ⟨hlegal n (by omega), ?_, ?_⟩
  · change |Real.log (Q B P hB c n) - E c n| < ε
    simpa only [Real.dist_eq, sub_zero] using hJQ n (by omega)
  · change |Real.log (QK B P hB c n) - E c n| < ε
    simpa only [Real.dist_eq, sub_zero] using hJK n (by omega)

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
  rcases RademacherCriticalPhase.cutoff_spec hc with ⟨hcut, hcell⟩
  rcases RademacherCriticalPhase.scales hc with ⟨hh, h2⟩
  have hx0 : Tendsto (x c) atTop (𝓝 (0 : ℝ)) := by
    rcases actual_s4 B P hB hc with ⟨_, _, _, _, hxs, _⟩
    apply hxs.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (positive_time_S4_bridges B P hB hc hn).2.2.2.1
  rcases (main_outputs_proof B P hB hc).2 with ⟨Npos, hNc, hlegal, _⟩
  refine ⟨hcut, ?_, ?_, ?_, hh, h2, hx0, ?_, Npos, hNc, hlegal⟩
  · intro n hn
    have hphase := RademacherCriticalPhase.finite_phase hc n
    refine ⟨positive_time hc (hcut.trans hn), hcell n hn, ?_⟩
    aesop
  · have hphase := RademacherCriticalPhase.finite_phase hc 0
    aesop
  · intro n
    have hphase := RademacherCriticalPhase.finite_phase hc n
    constructor
    · exact Real.exp_pos _
    · aesop
  · intro ε hε
    obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.1 hx0 ε hε
    refine ⟨max J 1, ?_⟩
    intro n hn
    have hxpos : 0 < x c n := (positive_time hc (by omega)).2.2.2.2.2.2.1
    refine ⟨hxpos, ?_⟩
    have ha : |x c n| < ε := by
      simpa only [Real.dist_eq, sub_zero] using hJ n (by omega)
    exact (abs_lt.1 ha).2

-- The input cell is eventual. Every all-j use is on this same shifted tail.
theorem S5_S4_EVENTUAL {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) :
    S4ReturnOutputs B P hB c := by
  refine ⟨actual_s4 B P hB hc, ?_⟩
  intro J hJ
  rcases critical_inputs hc with ⟨hcell, hh, h2, _⟩
  have hcut : 1 ≤ Ncell c := (RademacherCriticalPhase.cutoff_spec hc).1
  have hcells := (RademacherCriticalPhase.cutoff_spec hc).2
  have ht : TailS4Inputs c J := by
    refine ⟨?_, ?_, ?_, by positivity, ?_, 1 / c ^ 3, by positivity, 0, ?_⟩
    · intro j
      rcases hcells (j + J) (by change Ncell c ≤ j + J; omega) with ⟨_, hm, hmh, hhm, _⟩
      exact ⟨hm, hmh, hhm⟩
    · have heq : shift (height c) J = (fun j : ℕ => height c (j + J)) := by
        funext j
        rfl
      change Tendsto (shift (height c) J) atTop atTop
      rw [heq]
      simpa only [Function.comp_def] using hh.comp (tendsto_add_atTop_nat J)
    · simpa only [shift, RademacherS4Assembly.shift, Function.comp_def] using
        h2.comp (tendsto_add_atTop_nat J)
    · intro j
      exact (positive_time_S4_bridges B P hB hc (by omega : 1 ≤ j + J)).2.2.1
    · intro j hj
      have hs := (positive_time_S4_bridges B P hB hc (by omega : 1 ≤ j + J)).2.2.1
      exact hs.le
  have hall := RademacherS4Assembly.S4_ALL B P hB
    (shift (phaseFloor c) J) (shift (fun n : ℕ => n) J) (shift (height c) J)
    (fun j => (ht.1 j).1) (fun j => (ht.1 j).2.1) (fun j => (ht.1 j).2.2)
    ht.2.1 ht.2.2.1 ht.2.2.2.2.2
  refine ⟨ht, hall, ?_⟩
  intro j
  rcases positive_time_S4_bridges B P hB hc (by omega : 1 ≤ j + J) with
    ⟨_, hδ, _, hx, hw, hQ, hQK⟩
  refine ⟨?_, hx, hδ.symm, hw, hQ, hQK⟩
  simp [ShiftedObjects, shift, RademacherS4Assembly.shift]

theorem S5_MAIN {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) :
    MainOutputs B P hB c := by
  exact main_outputs_proof B P hB hc


private theorem cp_phase_of_data {c d : ℝ} (hc : 0 < c) (σ : ℕ → ℕ)
    (hσ : StrictMono σ)
    (hcell : ∀ j : ℕ, RademacherCriticalPhase.cutoff c ≤ σ j ∧
      RademacherCriticalPhase.WeakCell c (σ j))
    (hδ : Tendsto (fun j => delta c (σ j)) atTop (𝓝 d))
    (hE : Tendsto (fun j => E c (σ j)) atTop (𝓝 (coeff c * d)))
    (hF : Tendsto (fun j => F c (σ j)) atTop (𝓝 (Real.exp (coeff c * d)))) :
    CPPhaseOutputs c σ d := by
  refine ⟨hσ, ?_, hδ, hE, hF⟩
  intro j
  have hn : 1 ≤ σ j := (RademacherCriticalPhase.cutoff_spec hc).1.trans (hcell j).1
  rcases positive_time hc hn with ⟨_, _, _, _, _, hh, _, _, hthird, hthirdpos, _⟩
  exact ⟨(hcell j).1, (hcell j).2, hn, hh, hthird, hthirdpos⟩

private theorem cp_phase_shift {c d : ℝ} {σ : ℕ → ℕ}
    (hp : CPPhaseOutputs c σ d) (J : ℕ) :
    CPPhaseOutputs c (shift σ J) d := by
  rcases hp with ⟨hσ, hcell, hδ, hE, hF⟩
  refine ⟨hσ.comp (by intro i j hij; change i + J < j + J; omega), (fun j => hcell (j + J)), ?_, ?_, ?_⟩
  · simpa only [shift, RademacherS4Assembly.shift, Function.comp_def] using
      hδ.comp (tendsto_add_atTop_nat J)
  · simpa only [shift, RademacherS4Assembly.shift, Function.comp_def] using
      hE.comp (tendsto_add_atTop_nat J)
  · simpa only [shift, RademacherS4Assembly.shift, Function.comp_def] using
      hF.comp (tendsto_add_atTop_nat J)

private theorem actual_phase_limits {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c d : ℝ} (hc : 0 < c) {σ : ℕ → ℕ}
    (hp : CPPhaseOutputs c σ d) : PhaseLimits B P hB c σ d := by
  have hp0 := hp
  rcases hp0 with ⟨hσ, hcell, hδ, hE, hF⟩
  rcases S5_MAIN B P hB hc with
    ⟨⟨heQ, heQK, _, _, hdQ, hdQK⟩, Npos, hNc, hlegal, _⟩
  have hsub : Tendsto σ atTop atTop := hσ.tendsto_atTop
  have hlQ : Tendsto (fun j => Real.log (Q B P hB c (σ j)))
      atTop (𝓝 (coeff c * d)) := by
    simpa only [Function.comp_def, sub_add_cancel, zero_add] using
      (heQ.comp hsub).add hE
  have hlQK : Tendsto (fun j => Real.log (QK B P hB c (σ j)))
      atTop (𝓝 (coeff c * d)) := by
    simpa only [Function.comp_def, sub_add_cancel, zero_add] using
      (heQK.comp hsub).add hE
  have hQ : Tendsto (fun j => Q B P hB c (σ j))
      atTop (𝓝 (Real.exp (coeff c * d))) := by
    simpa only [Function.comp_def, sub_add_cancel, zero_add] using
      (hdQ.comp hsub).add hF
  have hQK : Tendsto (fun j => QK B P hB c (σ j))
      atTop (𝓝 (Real.exp (coeff c * d))) := by
    simpa only [Function.comp_def, sub_add_cancel, zero_add] using
      (hdQK.comp hsub).add hF
  have hlegsub : ∀ j : ℕ, Npos ≤ j → LegalAt B P hB c (σ j) := by
    intro j hj
    exact hlegal (σ j) (hj.trans (hσ.id_le j))
  have hsource : (fun j => Q B P hB c (σ j)) =ᶠ[atTop]
      (fun j => Qsource B P hB c (σ j)) := by
    filter_upwards [eventually_ge_atTop Npos] with j hj
    rcases (hlegsub j hj).2.2.1 with ⟨_, _, _, _, _, _, _, hs, _⟩
    exact hs.symm
  exact ⟨hp, ⟨Npos, hlegsub⟩, hlQ, hlQK, hQ, hQK, hQ.congr' hsource⟩

private theorem phase_outputs_of_cp {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c d : ℝ} (hc : 0 < c) {σ : ℕ → ℕ}
    (hp : CPPhaseOutputs c σ d) : PhaseOutputs B P hB c σ d := by
  refine ⟨actual_phase_limits B P hB hc hp, ?_⟩
  intro J
  refine ⟨actual_phase_limits B P hB hc (cp_phase_shift hp J), ?_⟩
  intro j
  simp [ShiftedObjects, shift, RademacherS4Assembly.shift]

private theorem up_actual_phase {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) :
    ∃ J : ℕ, 2 ≤ J ∧ PhaseOutputs B P hB c (upSeq c J) 1 := by
  rcases RademacherCriticalPhase.up_subsequence hc with ⟨J, hJ, hσ, hcell, hδ, hE, hF⟩
  have hp : CPPhaseOutputs c (upSeq c J) 1 :=
    cp_phase_of_data hc _ hσ hcell hδ
      (by simpa only [E, coeff, mul_one, upSeq] using hE)
      (by simpa only [F, coeff, mul_one, upSeq] using hF)
  refine ⟨J + 2, by omega, ?_⟩
  have hout := phase_outputs_of_cp B P hB hc (cp_phase_shift hp 2)
  have heq : shift (upSeq c J) 2 = upSeq c (J + 2) := by
    funext j
    simp only [shift, RademacherS4Assembly.shift, upSeq]
    congr 1
    omega
  rw [heq] at hout
  exact hout

private theorem down_actual_phase {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) :
    ∃ J : ℕ, 2 ≤ J ∧ PhaseOutputs B P hB c (downSeq c J) 0 := by
  rcases RademacherCriticalPhase.down_subsequence hc with ⟨J, hJ, hσ, hcell, hδ, hE, hF⟩
  have hp : CPPhaseOutputs c (downSeq c J) 0 :=
    cp_phase_of_data hc _ hσ hcell hδ
      (by simpa only [E, coeff, mul_zero, downSeq] using hE)
      (by simpa only [F, coeff, mul_zero, Real.exp_zero, downSeq] using hF)
  exact ⟨J, hJ, phase_outputs_of_cp B P hB hc hp⟩

private theorem nearest_actual_phase {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c α : ℝ} (hc : 0 < c) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ J : ℕ, 2 ≤ J ∧ PhaseOutputs B P hB c (nearestSeq c α J) (1 - α) := by
  rcases RademacherCriticalPhase.nearest_subsequence hc hα0 hα1 with
    ⟨J, hJ, hσ, hcell, hδ, hE, hF⟩
  have hp : CPPhaseOutputs c (nearestSeq c α J) (1 - α) :=
    cp_phase_of_data hc _ hσ hcell hδ hE hF
  refine ⟨J + 2, by omega, ?_⟩
  have hout := phase_outputs_of_cp B P hB hc (cp_phase_shift hp 2)
  have heq : shift (nearestSeq c α J) 2 = nearestSeq c α (J + 2) := by
    funext j
    simp only [shift, RademacherS4Assembly.shift, nearestSeq]
    congr 1
    omega
  rw [heq] at hout
  exact hout

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
  have hcube := RademacherCriticalPhase.cube_subsequence
  have hbelow := RademacherCriticalPhase.below_cube_subsequence
  refine ⟨hcube.1, hbelow.2.1, ?_, ?_⟩
  · intro j
    rcases RademacherCriticalPhase.exact_cube (by omega : 1 ≤ j + 1) with
      ⟨hcell, hh, hm, hH, hδ⟩
    exact ⟨(hcube.2.1 j).1, hcell, hh, hm, hH, hδ⟩
  · intro j
    rcases RademacherCriticalPhase.exact_below_cube (by omega : 2 ≤ j + 2) with
      ⟨hn, hZ, hR, hZminus, hRminus, hcell, hlo, hhi, hm, hH, hδ⟩
    exact ⟨hn, (hbelow.2.2.1 j).1, hZ, hR, hZminus, hRminus,
      hcell, hlo, hhi, hm, hH, hδ⟩

theorem S5_CUBE {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    coeff 1 = Real.pi ^ 2 / 4 ∧
    PhaseOutputs B P hB 1 cubeSeq 1 ∧
    PhaseOutputs B P hB 1 cubeMinusOneSeq 0 ∧
    (∀ α : ℝ, 0 < α → α < 1 → ∃ Jα : ℕ, 2 ≤ Jα ∧
      PhaseOutputs B P hB 1 (nearestSeq 1 α Jα) (1 - α)) := by
  have hc : (0 : ℝ) < 1 := by norm_num
  rcases RademacherCriticalPhase.cube_subsequence with ⟨hσ1, hc1, hd1, hE1, hF1⟩
  rcases RademacherCriticalPhase.below_cube_subsequence with ⟨_, hσ0, hc0, hd0, hE0, hF0⟩
  have hp1 : CPPhaseOutputs 1 cubeSeq 1 :=
    cp_phase_of_data hc _ hσ1 hc1 hd1
      (by simpa [E, coeff, RademacherCriticalPhase.q, cubeSeq] using hE1)
      (by simpa [F, coeff, RademacherCriticalPhase.q, cubeSeq] using hF1)
  have hp0 : CPPhaseOutputs 1 cubeMinusOneSeq 0 :=
    cp_phase_of_data hc _ hσ0 hc0 hd0
      (by simpa only [E, coeff, mul_zero, cubeMinusOneSeq] using hE0)
      (by simpa only [F, coeff, mul_zero, Real.exp_zero, cubeMinusOneSeq] using hF0)
  refine ⟨by simp [coeff, RademacherCriticalPhase.q],
    phase_outputs_of_cp B P hB hc hp1, phase_outputs_of_cp B P hB hc hp0, ?_⟩
  intro α hα0 hα1
  exact nearest_actual_phase B P hB hc hα0 hα1

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
  refine ⟨(RademacherCriticalPhase.up_rounding hc).1,
    (RademacherCriticalPhase.down_rounding hc).1,
    (RademacherCriticalPhase.up_rounding hc).2,
    (RademacherCriticalPhase.down_rounding hc).2, ?_⟩
  intro α hα0 hα1
  exact RademacherCriticalPhase.nearest_rounding hc hα0 hα1

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
  refine ⟨by simp [RademacherCriticalPhase.target], (fun α => rfl), rfl, rfl,
    (fun α => rfl), ?_, ?_, ?_⟩
  · intro hd
    subst d
    simp [RademacherCriticalPhase.phaseIndex]
  · intro hd
    subst d
    simp [RademacherCriticalPhase.phaseIndex]
  · intro hd0 hd1
    simp [RademacherCriticalPhase.phaseIndex, ne_of_gt hd0, ne_of_lt hd1]

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
  classical
  rcases up_actual_phase B P hB hc with ⟨Ja, hJa, hPa⟩
  rcases down_actual_phase B P hB hc with ⟨Jb, hJb, hPb⟩
  have hex : ∀ α : ℝ, ∃ J : ℕ, 0 < α → α < 1 →
      2 ≤ J ∧ PhaseOutputs B P hB c (nearestSeq c α J) (1 - α) := by
    intro α
    by_cases ha : 0 < α ∧ α < 1
    · rcases nearest_actual_phase B P hB hc ha.1 ha.2 with ⟨J, hJ, hp⟩
      exact ⟨J, fun _ _ => ⟨hJ, hp⟩⟩
    · exact ⟨2, fun h0 h1 => (ha ⟨h0, h1⟩).elim⟩
  choose Jα hJα using hex
  refine ⟨Ja, Jb, Jα, hJa, hJb, hPa, hPb, ?_, hJα, ?_⟩
  · intro j
    rcases (RademacherCriticalPhase.down_rounding hc).2 (j + Jb) (by omega) with
      ⟨hu, hZ, hR, _⟩
    exact ⟨hu, hZ, hR⟩
  · intro d hd
    by_cases hd0 : d = 0
    · subst d
      have hseq : phaseSeq c 0 Jb = downSeq c Jb := by
        funext j
        simp [phaseSeq, downSeq, RademacherCriticalPhase.phaseIndex]
      have hoff : phaseOffset Ja Jb Jα 0 = Jb := by simp [phaseOffset]
      rw [hoff, hseq]
      exact ⟨hJb, hPb, fun _ => rfl, by norm_num, by norm_num⟩
    · by_cases hd1 : d = 1
      · subst d
        have hseq : phaseSeq c 1 Ja = upSeq c Ja := by
          funext j
          simp [phaseSeq, upSeq, RademacherCriticalPhase.phaseIndex]
        have hoff : phaseOffset Ja Jb Jα 1 = Ja := by simp [phaseOffset]
        rw [hoff, hseq]
        exact ⟨hJa, hPa, by norm_num, fun _ => rfl, by norm_num⟩
      · have hdpos : 0 < d := by
          by_contra h
          exact hd0 (le_antisymm (le_of_not_gt h) hd.1)
        have hdlt : d < 1 := by
          by_contra h
          exact hd1 (le_antisymm hd.2 (le_of_not_gt h))
        have ha0 : 0 < 1 - d := by linarith
        have ha1 : 1 - d < 1 := by linarith
        rcases hJα (1 - d) ha0 ha1 with ⟨hJ, hP⟩
        have hdd : 1 - (1 - d) = d := by ring
        have hseq : phaseSeq c d (phaseOffset Ja Jb Jα d) =
            nearestSeq c (1 - d) (Jα (1 - d)) := by
          funext j
          simp [phaseSeq, phaseOffset, nearestSeq, RademacherCriticalPhase.phaseIndex, hd0, hd1]
        refine ⟨by simpa [phaseOffset, hd0, hd1] using hJ, ?_, ?_, ?_, ?_⟩
        · rw [hseq]
          simpa only [hdd] using hP
        · exact fun h => (hd0 h).elim
        · exact fun h => (hd1 h).elim
        · exact fun _ _ => hseq

theorem S5_CLUSTER_BOUND_Q {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c)
    {τ : ℕ → ℕ} (hτ : StrictMono τ) {L : ℝ}
    (hL : Tendsto (fun j : ℕ => Q B P hB c (τ j)) atTop (𝓝 L)) :
    L ∈ Set.Icc (1 : ℝ) (Real.exp (coeff c)) ∧
    (∀ᶠ j in atTop, Ncell c ≤ τ j ∧ LegalAt B P hB c (τ j)) ∧
    Tendsto (fun j : ℕ => QK B P hB c (τ j)) atTop (𝓝 L) := by
  rcases S5_MAIN B P hB hc with ⟨⟨_, _, _, _, hdiff, _⟩, Npos, hNc, hlegal, _⟩
  have hF : Tendsto (fun j : ℕ => F c (τ j)) atTop (𝓝 L) := by
    have hid : (fun j : ℕ => Q B P hB c (τ j) -
        (Q B P hB c (τ j) - F c (τ j))) = (fun j : ℕ => F c (τ j)) := by
      funext j
      ring
    simpa only [Function.comp_def, hid, sub_zero] using
      hL.sub (hdiff.comp hτ.tendsto_atTop)
  have hmem : L ∈ RademacherCriticalPhase.Cluster (RademacherCriticalPhase.factor c) :=
    ⟨τ, hτ, hF⟩
  have hbound : L ∈ Set.Icc (1 : ℝ) (Real.exp (coeff c)) := by
    have heq := (RademacherCriticalPhase.cluster_sets hc).2.2
    rw [heq] at hmem
    exact hmem
  have htail : ∀ᶠ j in atTop, Ncell c ≤ τ j ∧ LegalAt B P hB c (τ j) := by
    filter_upwards [eventually_ge_atTop Npos] with j hj
    have hn : Npos ≤ τ j := hj.trans (hτ.id_le j)
    exact ⟨hNc.trans hn, hlegal (τ j) hn⟩
  refine ⟨hbound, htail, hL.congr' ?_⟩
  filter_upwards [htail] with j hj
  exact hj.2.2.2.1.2.2.2.2.1

theorem S5_CLUSTER_BOUND_QK {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c)
    {τ : ℕ → ℕ} (hτ : StrictMono τ) {L : ℝ}
    (hL : Tendsto (fun j : ℕ => QK B P hB c (τ j)) atTop (𝓝 L)) :
    L ∈ Set.Icc (1 : ℝ) (Real.exp (coeff c)) ∧
    (∀ᶠ j in atTop, Ncell c ≤ τ j ∧ LegalAt B P hB c (τ j)) ∧
    Tendsto (fun j : ℕ => Q B P hB c (τ j)) atTop (𝓝 L) := by
  rcases S5_MAIN B P hB hc with ⟨⟨_, _, _, _, _, hdiff⟩, Npos, hNc, hlegal, _⟩
  have hF : Tendsto (fun j : ℕ => F c (τ j)) atTop (𝓝 L) := by
    have hid : (fun j : ℕ => QK B P hB c (τ j) -
        (QK B P hB c (τ j) - F c (τ j))) = (fun j : ℕ => F c (τ j)) := by
      funext j
      ring
    simpa only [Function.comp_def, hid, sub_zero] using
      hL.sub (hdiff.comp hτ.tendsto_atTop)
  have hmem : L ∈ RademacherCriticalPhase.Cluster (RademacherCriticalPhase.factor c) :=
    ⟨τ, hτ, hF⟩
  have hbound : L ∈ Set.Icc (1 : ℝ) (Real.exp (coeff c)) := by
    have heq := (RademacherCriticalPhase.cluster_sets hc).2.2
    rw [heq] at hmem
    exact hmem
  have htail : ∀ᶠ j in atTop, Ncell c ≤ τ j ∧ LegalAt B P hB c (τ j) := by
    filter_upwards [eventually_ge_atTop Npos] with j hj
    have hn : Npos ≤ τ j := hj.trans (hτ.id_le j)
    exact ⟨hNc.trans hn, hlegal (τ j) hn⟩
  refine ⟨hbound, htail, hL.congr' ?_⟩
  filter_upwards [htail] with j hj
  exact hj.2.2.2.1.2.2.2.2.1.symm

theorem S5_CLUSTER_REALIZE {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) {L : ℝ}
    (hL : L ∈ Set.Icc (1 : ℝ) (Real.exp (coeff c))) :
    ∃ d : ℝ, d ∈ Set.Icc (0 : ℝ) 1 ∧ L = Real.exp (coeff c * d) ∧
      ∃ J : ℕ, 2 ≤ J ∧ PhaseOutputs B P hB c (phaseSeq c d J) d ∧
        Tendsto (fun j : ℕ => Q B P hB c (phaseSeq c d J j)) atTop (𝓝 L) ∧
        Tendsto (fun j : ℕ => QK B P hB c (phaseSeq c d J j)) atTop (𝓝 L) := by
  have hq : 0 < coeff c := by
    unfold coeff RademacherCriticalPhase.q
    positivity
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL.1
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL.1
  have hlogq : Real.log L ≤ coeff c := by
    simpa only [Real.log_exp] using Real.log_le_log hLpos hL.2
  let d : ℝ := Real.log L / coeff c
  have hd : d ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg hlog0 hq.le, ?_⟩
    exact (div_le_iff₀ hq).2 (by simpa only [one_mul] using hlogq)
  have hcancel : coeff c * d = Real.log L := by
    dsimp [d]
    field_simp [hq.ne']
  have hrepr : L = Real.exp (coeff c * d) := by
    rw [hcancel]
    exact (Real.exp_log hLpos).symm
  rcases RademacherCriticalPhase.phase_realization hc hd with
    ⟨J, hJ, hσ, hcells, hδ, hE, hF⟩
  have hp : CPPhaseOutputs c (phaseSeq c d J) d :=
    cp_phase_of_data hc _ hσ (fun j => ⟨(hcells j).1, (hcells j).2.1⟩) hδ hE hF
  have hout := phase_outputs_of_cp B P hB hc hp
  refine ⟨d, hd, hrepr, J, hJ, hout, ?_, ?_⟩
  · simpa only [← hrepr] using hout.1.2.2.2.2.1
  · simpa only [← hrepr] using hout.1.2.2.2.2.2.1

theorem S5_CLUSTER {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) :
    Cluster (Q B P hB c) = Cluster (QK B P hB c) ∧
    Cluster (Q B P hB c) = Set.Icc (1 : ℝ) (Real.exp (coeff c)) ∧
    Cluster (QK B P hB c) = Set.Icc (1 : ℝ) (Real.exp (coeff c)) := by
  have hQ : Cluster (Q B P hB c) = Set.Icc (1 : ℝ) (Real.exp (coeff c)) := by
    apply Set.Subset.antisymm
    · rintro L ⟨τ, hτ, hL⟩
      exact (S5_CLUSTER_BOUND_Q B P hB hc hτ hL).1
    · intro L hL
      rcases S5_CLUSTER_REALIZE B P hB hc hL with ⟨d, hd, hr, J, hJ, hp, hLQ, hLK⟩
      exact ⟨phaseSeq c d J, hp.1.1.1, hLQ⟩
  have hK : Cluster (QK B P hB c) = Set.Icc (1 : ℝ) (Real.exp (coeff c)) := by
    apply Set.Subset.antisymm
    · rintro L ⟨τ, hτ, hL⟩
      exact (S5_CLUSTER_BOUND_QK B P hB hc hτ hL).1
    · intro L hL
      rcases S5_CLUSTER_REALIZE B P hB hc hL with ⟨d, hd, hr, J, hJ, hp, hLQ, hLK⟩
      exact ⟨phaseSeq c d J, hp.1.1.1, hLK⟩
  exact ⟨hQ.trans hK.symm, hQ, hK⟩

theorem S5_NOT_CONVERGENT {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) :
    0 < coeff c ∧ 1 < Real.exp (coeff c) ∧
    (¬ ∃ L : ℝ, Tendsto (Q B P hB c) atTop (𝓝 L)) ∧
    (¬ ∃ L : ℝ, Tendsto (QK B P hB c) atTop (𝓝 L)) := by
  have hq : 0 < coeff c := by
    unfold coeff RademacherCriticalPhase.q
    positivity
  have hexp : 1 < Real.exp (coeff c) := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hq
  have hnc := (RademacherCriticalPhase.not_convergent hc).2.2
  rcases (S5_MAIN B P hB hc).1 with ⟨_, _, _, _, hdQ, hdK⟩
  refine ⟨hq, hexp, ?_, ?_⟩
  · rintro ⟨L, hL⟩
    apply hnc
    refine ⟨L, ?_⟩
    have hid : (fun n : ℕ => Q B P hB c n - (Q B P hB c n - F c n)) = F c := by
      funext n
      ring
    have hFc : F c = RademacherCriticalPhase.factor c := by funext n; rfl
    rw [← hFc]
    simpa only [hid, sub_zero] using hL.sub hdQ
  · rintro ⟨L, hL⟩
    apply hnc
    refine ⟨L, ?_⟩
    have hid : (fun n : ℕ => QK B P hB c n - (QK B P hB c n - F c n)) = F c := by
      funext n
      ring
    have hFc : F c = RademacherCriticalPhase.factor c := by funext n; rfl
    rw [← hFc]
    simpa only [hid, sub_zero] using hL.sub hdK

theorem S5_UNIT_CLUSTER {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    Cluster (Q B P hB 1) = Set.Icc (1 : ℝ) (Real.exp (Real.pi ^ 2 / 4)) ∧
    Cluster (QK B P hB 1) = Set.Icc (1 : ℝ) (Real.exp (Real.pi ^ 2 / 4)) ∧
    (¬ ∃ L : ℝ, Tendsto (Q B P hB 1) atTop (𝓝 L)) ∧
    (¬ ∃ L : ℝ, Tendsto (QK B P hB 1) atTop (𝓝 L)) := by
  have hc : (0 : ℝ) < 1 := by norm_num
  rcases S5_CLUSTER B P hB hc with ⟨_, hQ, hK⟩
  rcases S5_NOT_CONVERGENT B P hB hc with ⟨_, _, hnQ, hnK⟩
  simpa only [coeff, RademacherCriticalPhase.q, one_pow, mul_one] using
    And.intro hQ (And.intro hK (And.intro hnQ hnK))

end Shao.OQ4.RademacherS5Assembly

end
