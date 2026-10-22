import Shao.OQ4.RademacherS3Assembly
import Shao.OQ4.RademacherLatticeShift
import Shao.OQ4.RademacherScaleAssembly
import Shao.Probability.BrownianSup
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Local full proof text for frozen original S4, sections 3 through 7.
The public definitions and theorem signatures retain the exact accepted freeze.
No Lean invocation or import availability check has been run for this file.
The S3 module import is pendingformalplacement against the exact public S3
declaration freeze 3efdc04e86d5c69a1e823b93daa86d6f1ab874bf3af2f3faca9f2829d9e86fcc.
S3 has not been compiled or accepted by this implementation task.
The scale module is accepted in root v36 according to the assigned handoff.
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

private theorem tendsto_shift_iff {α : Type*} (f : ℕ → α) (K_0 : ℕ)
    (l : Filter α) :
    Tendsto (shift f K_0) atTop l ↔ Tendsto f atTop l := by
  exact Filter.tendsto_add_atTop_iff_nat K_0

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
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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
  rcases RademacherLatticeShift.DA0 hm hmh hhm with
    ⟨hh1, hhpos, hH2, hHpos, hHadd, hdpos, hdle, hh2, hh3, hh4,
      hHsq, _, hfour, htwo, hsin, hapos, hrpos, hrlt, hpiapos⟩
  rcases RademacherS3Assembly.finite_identities m hm h hmh hhm n with
    ⟨_, _, _, _, _, _, _, hApos, hpdef, hKdef, hpK, _, hDp, hDK, _⟩
  refine ⟨hh1, hhpos, hH2, hHpos, hHadd, hdpos, hdle, ?_,
    hh2, hh3, hh4, hHsq, hfour, htwo, hsin, hapos, hrpos, hrlt,
    hApos, hpiapos, hpdef, hKdef, hpK, hDp, hDK, ?_⟩
  · intro hleft
    subst h
    exact RademacherLatticeShift.delta_at_left m
  · intro hn
    subst n
    rcases RademacherS3Assembly.zero_time m hm h hmh hhm with
      ⟨hp0, hK0, hx0, _⟩
    exact ⟨hp0, hK0, hx0⟩

theorem actual_brownian_bridges {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (s : ℝ) :
    b B P hB s = Shao.Probability.BrownianSup.probability B P hB s ∧
    b B P hB s =
      P.real {ω | Shao.Probability.BrownianSup.U B P hB ω ≤ s} ∧
    b B P hB s = P.real (Shao.Probability.BrownianSup.fullStrip B s) ∧
    g s = (4 / Real.pi) * Real.exp (-lambda / s ^ 2) ∧
    0 < g s ∧ T B P hB s = b B P hB s / g s := by
  rcases RademacherS3Assembly.brownian_object B P hB with ⟨_, _, hprob⟩
  rcases hprob s with ⟨hU, hstrip⟩
  rcases RademacherS3Assembly.g_pos s with ⟨hg, _, _, hgpos⟩
  exact ⟨rfl, hU, hstrip, hg, hgpos, rfl⟩

theorem fixed_DA_constant :
    0 < C_DA ∧
    ∀ m : ℕ, 1 ≤ m →
      ∀ h : ℝ, (m : ℝ) ≤ h → h < (m : ℝ) + 1 →
        ∀ n : ℕ,
          |Cdet m n h - w m n h| ≤
            C_DA * (N n / h ^ 4 + 1 / (H m) ^ 2) := by
  refine ⟨RademacherLatticeShift.C_pos, ?_⟩
  intro m hm h hmh hhm n
  have hb := RademacherLatticeShift.finite_bound hm hmh hhm n
  change |Cdet m n h - (2 * lambda) * scale3 n h * delta m h| ≤
    C_DA * (N n / h ^ 4 + 1 / (H m) ^ 2) at hb
  have hc : 2 * lambda = Real.pi ^ 2 / 4 := by
    dsimp [lambda, RademacherS3Assembly.lambda, RademacherScalarBounds.lambda]
    ring
  simpa only [w, hc] using hb

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
  rcases RademacherScaleAssembly.DA2 m_ n_ h_ hm hmh hhm hh hscale2 hscale3 with
    ⟨_, ⟨hH, _, htH, ⟨K_T, hTbound⟩, _⟩,
      ⟨hfour, hHinv, _, _⟩, hdetDA⟩
  have hdet : Tendsto
      (fun k : ℕ => Cdet (m_ k) (n_ k) (h_ k) - w (m_ k) (n_ k) (h_ k))
      atTop (𝓝 (0 : ℝ)) := hdetDA
  rcases RademacherS3Assembly.S3_DOM B P hB m_ n_ h_ hm hmh hhm hH htH with
    ⟨_, _, _, hx, hxpos, _⟩
  rcases RademacherS3Assembly.S3_ALG B P hB m_ n_ h_ hm hmh hhm hH htH with
    ⟨K_alg, halg⟩
  have heta : Tendsto
      (fun k : ℕ => eta3 B P hB (m_ k) (n_ k) (h_ k))
      atTop (𝓝 (0 : ℝ)) :=
    RademacherS3Assembly.S3_MAIN B P hB m_ n_ h_ hm hmh hhm hH htH
  have hpK : ∀ k : ℕ, p (n_ k) (h_ k) = K (n_ k) (h_ k) := by
    intro k
    rcases RademacherS3Assembly.finite_identities (m_ k) (hm k)
        (h_ k) (hmh k) (hhm k) (n_ k) with
      ⟨_, _, _, _, _, _, _, _, _, _, heq, _⟩
    exact heq
  have hQQK : ∀ k : ℕ, Q B P hB (n_ k) (h_ k) = QK B P hB (n_ k) (h_ k) := by
    intro k
    dsimp [Q, QK]
    rw [hpK k]
  have hmain : Tendsto
      (fun k : ℕ => Real.log (Q B P hB (n_ k) (h_ k)) -
        w (m_ k) (n_ k) (h_ k)) atTop (𝓝 (0 : ℝ)) := by
    have heq :
        (fun k : ℕ => Real.log (Q B P hB (n_ k) (h_ k)) -
          w (m_ k) (n_ k) (h_ k)) =
        (fun k : ℕ => (Cdet (m_ k) (n_ k) (h_ k) -
          w (m_ k) (n_ k) (h_ k)) + eta3 B P hB (m_ k) (n_ k) (h_ k)) := by
      funext k
      dsimp [eta3]
      ring
    rw [heq]
    simpa only [zero_add] using hdet.add heta
  have hmainK : Tendsto
      (fun k : ℕ => Real.log (QK B P hB (n_ k) (h_ k)) -
        w (m_ k) (n_ k) (h_ k)) atTop (𝓝 (0 : ℝ)) := by
    have heq :
        (fun k : ℕ => Real.log (QK B P hB (n_ k) (h_ k)) -
          w (m_ k) (n_ k) (h_ k)) =
        (fun k : ℕ => Real.log (Q B P hB (n_ k) (h_ k)) -
          w (m_ k) (n_ k) (h_ k)) := by
      funext k
      rw [hQQK k]
    rw [heq]
    exact hmain
  let K_time : ℕ := max K_T K_alg
  have htime : ∀ k : ℕ, K_time ≤ k → TimeLegal (m_ k) (n_ k) (h_ k) := by
    intro k hk
    have hka : K_alg ≤ k := le_trans (le_max_right K_T K_alg) hk
    have hkt : K_T ≤ k := le_trans (le_max_left K_T K_alg) hk
    rcases halg k hka with ⟨hn, hN, hsqrt, hhpos, hxposk, _⟩
    exact ⟨hm k, hmh k, hhm k, hn, hN, hsqrt, Real.sq_sqrt (le_of_lt hN),
      hTbound k hkt, hhpos, hxposk, rfl⟩
  have hpositive : ∀ k : ℕ, K_time ≤ k →
      ProbabilityLegal B P hB (m_ k) (n_ k) (h_ k) ∧
      LogIdentities B P hB (m_ k) (n_ k) (h_ k) ∧
      |(Real.log (Q B P hB (n_ k) (h_ k)) - w (m_ k) (n_ k) (h_ k)) -
          eta3 B P hB (m_ k) (n_ k) (h_ k)| ≤
        C_DA * (N (n_ k) / (h_ k) ^ 4 + 1 / (H (m_ k)) ^ 2) ∧
      |(Real.log (QK B P hB (n_ k) (h_ k)) - w (m_ k) (n_ k) (h_ k)) -
          eta3 B P hB (m_ k) (n_ k) (h_ k)| ≤
        C_DA * (N (n_ k) / (h_ k) ^ 4 + 1 / (H (m_ k)) ^ 2) := by
    intro k hk
    have hka : K_alg ≤ k := le_trans (le_max_right K_T K_alg) hk
    rcases halg k hka with
      ⟨_, _, _, hhpos, _, ha, hr, hA, hpi, hp, hK, hD, hb, hg, hT,
        hQ, hQK, _, _, _, hL, hLK, hE, _⟩
    rcases RademacherS3Assembly.finite_identities (m_ k) (hm k)
        (h_ k) (hmh k) (hhm k) (n_ k) with
      ⟨hh1, _, _, hHpos, _, _, hrlt, _⟩
    have hEtaK : eta3 B P hB (m_ k) (n_ k) (h_ k) =
        Real.log (QK B P hB (n_ k) (h_ k)) - Cdet (m_ k) (n_ k) (h_ k) := by
      dsimp only [eta3]
      rw [hQQK k]
    have hsplit : Real.log (Q B P hB (n_ k) (h_ k)) - w (m_ k) (n_ k) (h_ k) =
        (Cdet (m_ k) (n_ k) (h_ k) - w (m_ k) (n_ k) (h_ k)) +
          eta3 B P hB (m_ k) (n_ k) (h_ k) := by
      dsimp only [eta3]
      ring
    have hsplitK : Real.log (QK B P hB (n_ k) (h_ k)) - w (m_ k) (n_ k) (h_ k) =
        (Cdet (m_ k) (n_ k) (h_ k) - w (m_ k) (n_ k) (h_ k)) +
          eta3 B P hB (m_ k) (n_ k) (h_ k) := by
      rw [← hQQK k]
      exact hsplit
    have hbnd := fixed_DA_constant.2 (m_ k) (hm k) (h_ k) (hmh k) (hhm k) (n_ k)
    refine ⟨⟨hh1, hhpos, hHpos, ha, hr, hrlt, hA, hpi, hpK k, hp, hK, hD,
      hb, hg, hT, hQQK k, hQ, hQK⟩,
      ⟨hL, hLK, hEtaK, hE, hsplit, hsplitK⟩, ?_, ?_⟩
    · have heq :
          (Real.log (Q B P hB (n_ k) (h_ k)) - w (m_ k) (n_ k) (h_ k)) -
              eta3 B P hB (m_ k) (n_ k) (h_ k) =
          Cdet (m_ k) (n_ k) (h_ k) - w (m_ k) (n_ k) (h_ k) := by
        dsimp only [eta3]
        ring
      rw [heq]
      exact hbnd
    · rw [← hQQK k]
      have heq :
          (Real.log (Q B P hB (n_ k) (h_ k)) - w (m_ k) (n_ k) (h_ k)) -
              eta3 B P hB (m_ k) (n_ k) (h_ k) =
          Cdet (m_ k) (n_ k) (h_ k) - w (m_ k) (n_ k) (h_ k) := by
        dsimp only [eta3]
        ring
      rw [heq]
      exact hbnd
  refine ⟨hH, htH, hfour, hHinv, hx, hxpos, heta, hmain, hmainK,
    K_time, K_time, le_rfl, htime, hpositive, ?_⟩
  intro e he
  rcases Metric.tendsto_atTop.1 hmain e he with ⟨K_Q, hK_Q⟩
  rcases Metric.tendsto_atTop.1 hmainK e he with ⟨K_K, hK_K⟩
  refine ⟨max K_time (max K_Q K_K), le_max_left _ _, ?_⟩
  intro k hk
  have hkt : K_time ≤ k := le_trans (le_max_left _ _) hk
  have hkQ : K_Q ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkK : K_K ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  exact ⟨htime k hkt, (hpositive k hkt).1, (hpositive k hkt).2.1,
    by simpa only [Real.dist_eq, sub_zero] using hK_Q k hkQ,
    by simpa only [Real.dist_eq, sub_zero] using hK_K k hkK⟩

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
  rcases Metric.tendsto_atTop.1 hsubcritical (1 : ℝ) zero_lt_one with ⟨K_M, hK_M⟩
  have hbounded : ∃ M : ℝ, 0 < M ∧
      ∃ K_M : ℕ, ∀ k : ℕ, K_M ≤ k → scale3 (n_ k) (h_ k) ≤ M := by
    refine ⟨1, zero_lt_one, K_M, ?_⟩
    intro k hk
    have habs : |scale3 (n_ k) (h_ k)| < 1 := by
      simpa only [Real.dist_eq, sub_zero] using hK_M k hk
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) habs)
  have hout := S4_ALL B P hB m_ n_ h_ hm hmh hhm hh hscale2 hbounded
  rcases (show S4Outputs B P hB m_ n_ h_ from hout) with
    ⟨_, _, _, _, _, _, heta, _, _, K_time, K_pos, horder, htime, hpositive, _⟩
  have hcenter : Tendsto
      (fun k : ℕ => Cdet (m_ k) (n_ k) (h_ k)) atTop (𝓝 (0 : ℝ)) :=
    RademacherScaleAssembly.DA2_subcritical m_ n_ h_ hm hmh hhm hh
      hscale2 hbounded hsubcritical
  have hlog : Tendsto
      (fun k : ℕ => Real.log (Q B P hB (n_ k) (h_ k)))
      atTop (𝓝 (0 : ℝ)) := by
    have heq :
        (fun k : ℕ => Real.log (Q B P hB (n_ k) (h_ k))) =
        (fun k : ℕ => eta3 B P hB (m_ k) (n_ k) (h_ k) +
          Cdet (m_ k) (n_ k) (h_ k)) := by
      funext k
      dsimp only [eta3]
      ring
    rw [heq]
    simpa only [zero_add] using heta.add hcenter
  have hexp : Tendsto
      (fun k : ℕ => Real.exp (Real.log (Q B P hB (n_ k) (h_ k))))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [Real.exp_zero, Function.comp_def] using
      (Real.continuous_exp.tendsto (0 : ℝ)).comp hlog
  have hQ : Tendsto (fun k : ℕ => Q B P hB (n_ k) (h_ k))
      atTop (𝓝 (1 : ℝ)) := by
    have heq :
        (fun k : ℕ => Real.exp (Real.log (Q B P hB (n_ k) (h_ k)))) =ᶠ[atTop]
        (fun k : ℕ => Q B P hB (n_ k) (h_ k)) := by
      filter_upwards [eventually_ge_atTop K_pos] with k hk
      rcases (hpositive k hk).1 with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hQpos, _⟩
      exact Real.exp_log hQpos
    exact Filter.Tendsto.congr' heq hexp
  have hQK : Tendsto (fun k : ℕ => QK B P hB (n_ k) (h_ k))
      atTop (𝓝 (1 : ℝ)) := by
    have heq : (fun k : ℕ => Q B P hB (n_ k) (h_ k)) =ᶠ[atTop]
        (fun k : ℕ => QK B P hB (n_ k) (h_ k)) := by
      filter_upwards [eventually_ge_atTop K_pos] with k hk
      rcases (hpositive k hk).1 with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hQQK, _⟩
      exact hQQK
    exact Filter.Tendsto.congr' heq hQ
  refine ⟨hout, hlog, hQ, hQK, ?_⟩
  intro e he
  rcases Metric.tendsto_atTop.1 hlog e he with ⟨K_L, hK_L⟩
  rcases Metric.tendsto_atTop.1 hQ e he with ⟨K_Q, hK_Q⟩
  rcases Metric.tendsto_atTop.1 hQK e he with ⟨K_K, hK_K⟩
  refine ⟨max K_pos (max K_L (max K_Q K_K)), ?_⟩
  intro k hk
  have hkp : K_pos ≤ k := le_trans (le_max_left _ _) hk
  have hkt : K_time ≤ k := le_trans horder hkp
  have hkL : K_L ≤ k := by omega
  have hkQ : K_Q ≤ k := by omega
  have hkK : K_K ≤ k := by omega
  exact ⟨htime k hkt, (hpositive k hkp).1,
    by simpa only [Real.dist_eq, sub_zero] using hK_L k hkL,
    by simpa only [Real.dist_eq] using hK_Q k hkQ,
    by simpa only [Real.dist_eq] using hK_K k hkK⟩

attribute [elab_without_expected_type] shift

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
  refine ⟨?_, (tendsto_shift_iff h_ K_0 atTop).2 hh,
    (tendsto_shift_iff (fun k : ℕ => N (n_ k) / (h_ k) ^ 2) K_0 atTop).2 hscale2,
    ?_, ?_⟩
  · intro j
    exact hcell (j + K_0) (by omega)
  · refine ⟨K_M - K_0, ?_⟩
    intro j hj
    exact hM_bound (j + K_0) (by omega)
  · intro hsub
    exact (tendsto_shift_iff (fun k : ℕ => scale3 (n_ k) (h_ k))
      K_0 (𝓝 (0 : ℝ))).2 hsub

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
  intro j
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem outputs_unshift {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (m_ n_ : ℕ → ℕ) (h_ : ℕ → ℝ) (K_0 : ℕ)
    (hs : S4Outputs B P hB (shift m_ K_0) (shift n_ K_0) (shift h_ K_0)) :
    S4Outputs B P hB m_ n_ h_ := by
  rcases hs with
    ⟨hH, htH, hfour, hHinv, hx, hxpos, heta, hmain, hmainK,
      K_time, K_pos, horder, htime, hpositive, heps⟩
  refine ⟨
    (tendsto_shift_iff (fun k : ℕ => H (m_ k)) K_0 atTop).1 hH,
    (tendsto_shift_iff (fun k : ℕ => N (n_ k) / (H (m_ k)) ^ 2) K_0 atTop).1 htH,
    (tendsto_shift_iff (fun k : ℕ => N (n_ k) / (h_ k) ^ 4)
      K_0 (𝓝 (0 : ℝ))).1 hfour,
    (tendsto_shift_iff (fun k : ℕ => 1 / (H (m_ k)) ^ 2)
      K_0 (𝓝 (0 : ℝ))).1 hHinv,
    (tendsto_shift_iff (fun k : ℕ => x (n_ k) (h_ k))
      K_0 (𝓝 (0 : ℝ))).1 hx,
    ?_,
    (tendsto_shift_iff (fun k : ℕ => eta3 B P hB (m_ k) (n_ k) (h_ k))
      K_0 (𝓝 (0 : ℝ))).1 heta,
    (tendsto_shift_iff
      (fun k : ℕ => Real.log (Q B P hB (n_ k) (h_ k)) - w (m_ k) (n_ k) (h_ k))
      K_0 (𝓝 (0 : ℝ))).1 hmain,
    (tendsto_shift_iff
      (fun k : ℕ => Real.log (QK B P hB (n_ k) (h_ k)) - w (m_ k) (n_ k) (h_ k))
      K_0 (𝓝 (0 : ℝ))).1 hmainK,
    K_time + K_0, K_pos + K_0, by omega, ?_, ?_, ?_⟩
  · intro d hd
    rcases hxpos d hd with ⟨J, hJ⟩
    refine ⟨J + K_0, ?_⟩
    intro k hk
    have hj : J ≤ k - K_0 := by omega
    have hidx : k - K_0 + K_0 = k := by omega
    simpa only [shift, hidx] using hJ (k - K_0) hj
  · intro k hk
    have hj : K_time ≤ k - K_0 := by omega
    have hidx : k - K_0 + K_0 = k := by omega
    simpa only [shift, hidx] using htime (k - K_0) hj
  · intro k hk
    have hj : K_pos ≤ k - K_0 := by omega
    have hidx : k - K_0 + K_0 = k := by omega
    simpa only [shift, hidx] using hpositive (k - K_0) hj
  · intro e he
    rcases heps e he with ⟨J, hJpos, hJ⟩
    refine ⟨J + K_0, by omega, ?_⟩
    intro k hk
    have hj : J ≤ k - K_0 := by omega
    have hidx : k - K_0 + K_0 = k := by omega
    simpa only [shift, hidx] using hJ (k - K_0) hj

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
  rcases hcell with ⟨K_cell, hcell⟩
  rcases hscale3 with ⟨M, hM, K_M, hM_bound⟩
  rcases shifted_inputs m_ n_ h_ K_cell K_cell hcell le_rfl
      hh hscale2 M hM K_M hM_bound with
    ⟨hcellS, hhS, hscale2S, ⟨K_shift, hboundS⟩, _⟩
  have hs := S4_ALL B P hB (shift m_ K_cell) (shift n_ K_cell) (shift h_ K_cell)
    (fun j : ℕ => (hcellS j).1)
    (fun j : ℕ => (hcellS j).2.1)
    (fun j : ℕ => (hcellS j).2.2)
    hhS hscale2S ⟨M, hM, K_shift, hboundS⟩
  exact outputs_unshift B P hB m_ n_ h_ K_cell hs

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
  rcases hcell with ⟨K_cell, hcell⟩
  have hcellS : ∀ j : ℕ,
      1 ≤ shift m_ K_cell j ∧
      (shift m_ K_cell j : ℝ) ≤ shift h_ K_cell j ∧
      shift h_ K_cell j < (shift m_ K_cell j : ℝ) + 1 := by
    intro j
    exact hcell (j + K_cell) (by omega)
  have hhS : Tendsto (shift h_ K_cell) atTop atTop :=
    (tendsto_shift_iff h_ K_cell atTop).2 hh
  have hscale2S : Tendsto
      (fun j : ℕ => N (shift n_ K_cell j) / (shift h_ K_cell j) ^ 2) atTop atTop :=
    (tendsto_shift_iff (fun k : ℕ => N (n_ k) / (h_ k) ^ 2) K_cell atTop).2 hscale2
  have hsubS : Tendsto
      (fun j : ℕ => scale3 (shift n_ K_cell j) (shift h_ K_cell j))
      atTop (𝓝 (0 : ℝ)) :=
    (tendsto_shift_iff (fun k : ℕ => scale3 (n_ k) (h_ k))
      K_cell (𝓝 (0 : ℝ))).2 hsubcritical
  rcases S4_SUB B P hB (shift m_ K_cell) (shift n_ K_cell) (shift h_ K_cell)
      (fun j : ℕ => (hcellS j).1)
      (fun j : ℕ => (hcellS j).2.1)
      (fun j : ℕ => (hcellS j).2.2) hhS hscale2S hsubS with
    ⟨houtS, hlogS, hQS, hQKS, hepsS⟩
  refine ⟨outputs_unshift B P hB m_ n_ h_ K_cell houtS,
    (tendsto_shift_iff (fun k : ℕ => Real.log (Q B P hB (n_ k) (h_ k)))
      K_cell (𝓝 (0 : ℝ))).1 hlogS,
    (tendsto_shift_iff (fun k : ℕ => Q B P hB (n_ k) (h_ k))
      K_cell (𝓝 (1 : ℝ))).1 hQS,
    (tendsto_shift_iff (fun k : ℕ => QK B P hB (n_ k) (h_ k))
      K_cell (𝓝 (1 : ℝ))).1 hQKS, ?_⟩
  intro e he
  rcases hepsS e he with ⟨J, hJ⟩
  refine ⟨J + K_cell, ?_⟩
  intro k hk
  have hj : J ≤ k - K_cell := by omega
  have hidx : k - K_cell + K_cell = k := by omega
  simpa only [shift, hidx] using hJ (k - K_cell) hj

end Shao.OQ4.RademacherS4Assembly

end
