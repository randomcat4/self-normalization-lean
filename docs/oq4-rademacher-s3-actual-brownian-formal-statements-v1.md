import Shao.OQ4.RademacherS2Assembly
import Shao.OQ4.RademacherLatticeShift
import Shao.Probability.BrownianSup
import Shao.Probability.BrownianFirstTerm
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Declaration-only draft for the frozen original S3, using the actual B1 object.
The theorem bodies below are deliberately empty comment placeholders.
This text is not a checked Lean module and asserts no completed proof.
The actual Brownian first-term asymptotic B2 is accepted in PR140/v35.
Only its first-term ratio and eventual positivity APIs are consumed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Shao.OQ4.RademacherS3Assembly

def H (m : ℕ) : ℝ := RademacherS2Assembly.H m

def N (n : ℕ) : ℝ := RademacherS2Assembly.N n

def t (m n : ℕ) : ℝ := RademacherS2Assembly.t m n

def a (m : ℕ) : ℝ := RademacherS2Assembly.a m

def rho (m : ℕ) : ℝ := RademacherS2Assembly.rho m

def eps (m n : ℕ) : ℝ := RademacherS2Assembly.eps m n

def q (m : ℕ) : ℝ := RademacherS2Assembly.q m

def R (m n : ℕ) : ℝ := RademacherS2Assembly.R m n

-- A is exactly the S2 spectral normalizer; B denotes the Brownian process.
def A (m n : ℕ) : ℝ := RademacherS2Assembly.B m n

def p (n : ℕ) (h : ℝ) : ℝ := RademacherS2Assembly.p n h

def K (n : ℕ) (h : ℝ) : ℝ := RademacherS2Assembly.K n h

def D (m n : ℕ) (h : ℝ) : ℝ := RademacherS2Assembly.D m n h

def u (m : ℕ) : ℝ := RademacherScalarBounds.u m

def z (m : ℕ) : ℝ := RademacherScalarBounds.z m

def lambda : ℝ := RademacherScalarBounds.lambda

-- The total real expression is 0 at n = 0; the probability comparison is
-- interpreted on the positive-time tails supplied by S3_DOM.
def x (n : ℕ) (h : ℝ) : ℝ := h / Real.sqrt (N n)

def g (s : ℝ) : ℝ := Shao.Probability.BrownianSup.firstTerm s

def G (n : ℕ) (h : ℝ) : ℝ :=
  (4 / Real.pi) * Real.exp (-lambda * N n / h ^ 2)

def b {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (s : ℝ) : ℝ :=
  Shao.Probability.BrownianSup.probability B P hB s

def T {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (s : ℝ) : ℝ :=
  b B P hB s / g s

def W {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (n : ℕ) (h : ℝ) : ℝ :=
  b B P hB (x n h) / G n h

def C (m n : ℕ) (h : ℝ) : ℝ :=
  lambda * N n / h ^ 2 + N n * Real.log (rho m) +
    Real.log (Real.pi * a m / 4)

theorem definition_bridges (m : ℕ) :
    H m = (m : ℝ) + 1 ∧
    H m = RademacherScalarBounds.H m ∧
    u m = Real.pi / (4 * H m) ∧
    z m = Real.pi / (2 * H m) ∧
    RademacherSpectralPairing.alpha m 0 = u m ∧
    RademacherSpectralPairing.beta m 0 = z m ∧
    a m = (1 / H m) * (Real.cos (u m) / Real.sin (u m)) ∧
    a m = RademacherScalarBounds.a m ∧
    rho m = Real.cos (z m) ∧
    rho m = RademacherScalarBounds.rho m ∧
    lambda = Real.pi ^ 2 / 8 ∧
    (∀ n : ℕ, N n = (n : ℝ) ∧
      eps m n = (-1 : ℝ) ^ (n + m)) := by
  -- Declaration only: proof not supplied in this draft.

theorem finite_identities (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (n : ℕ) :
    1 ≤ h ∧ 0 < h ∧ 2 ≤ H m ∧ 0 < H m ∧
    0 < a m ∧ 0 < rho m ∧ rho m < 1 ∧ 0 < A m n ∧
    p n h =
      (Measure.pi (fun _ : Fin n => RademacherCosine.law)).real
        (@Shao.closedStrip n h) ∧
    K n h =
      @Shao.OQ4.killedMass RademacherCosine.law
        RademacherCosine.law_isProbabilityMeasure h n (0 : ℝ) ∧
    p n h = K n h ∧
    p n h = A m n * (1 + eps m n * q m + R m n) ∧
    D m n h = p n h / A m n ∧
    D m n h = K n h / A m n ∧
    D m n h = 1 + eps m n * q m + R m n := by
  -- Declaration only: proof not supplied in this draft.

theorem zero_time (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) :
    p 0 h = 1 ∧ K 0 h = 1 ∧ x 0 h = 0 ∧
    RademacherSpectralPairing.zeroMode m 0 =
      (if Even m then (-1 : ℝ) ^ (m / 2) / H m else 0) := by
  -- Declaration only: proof not supplied in this draft.

theorem small_cells :
    (∀ n : ℕ, R 1 n = 0) ∧
    (∀ n : ℕ, 1 ≤ n → R 2 n = 0) ∧
    RademacherSpectralPairing.zeroMode 2 0 = -(1 / 3 : ℝ) ∧
    R 2 0 = -1 / (3 * a 2) ∧ R 2 0 ≠ 0 := by
  -- Declaration only: proof not supplied in this draft.

theorem brownian_object {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    Measurable (Shao.Probability.BrownianSup.U B P hB) ∧
    Shao.Probability.BrownianSup.U B P hB =ᵐ[P]
      Shao.Probability.BrownianSup.pathSup B ∧
    (∀ s : ℝ,
      b B P hB s =
        P.real {ω | Shao.Probability.BrownianSup.U B P hB ω ≤ s} ∧
      b B P hB s =
        P.real (Shao.Probability.BrownianSup.fullStrip B s)) := by
  -- Declaration only: proof not supplied in this draft.

theorem g_pos (s : ℝ) :
    g s = (4 / Real.pi) * Real.exp (-lambda / s ^ 2) ∧
    0 < lambda ∧ 0 < (4 / Real.pi : ℝ) ∧ 0 < g s := by
  -- Declaration only: proof not supplied in this draft.

theorem finite_ALG (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1)
    (n : ℕ) (hn : 1 ≤ n) :
    0 < N n ∧ 0 < Real.sqrt (N n) ∧
    (Real.sqrt (N n)) ^ 2 = N n ∧ 0 < h ∧ 0 < x n h ∧
    (x n h) ^ 2 = h ^ 2 / N n ∧
    1 / (x n h) ^ 2 = N n / h ^ 2 ∧
    g (x n h) = G n h ∧ 0 < G n h ∧
    0 < rho m ^ n ∧ 0 < Real.pi * a m / 4 ∧
    Real.log (rho m ^ n) = N n * Real.log (rho m) ∧
    Real.log (g (x n h)) =
      Real.log (4 / Real.pi) - lambda * N n / h ^ 2 ∧
    Real.log (a m) - Real.log (4 / Real.pi) =
      Real.log (Real.pi * a m / 4) := by
  -- Declaration only: proof not supplied in this draft.

theorem S3_DOM {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (m_ n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hm : ∀ k : ℕ, 1 ≤ m_ k)
    (hmh : ∀ k : ℕ, (m_ k : ℝ) ≤ h_ k)
    (hhm : ∀ k : ℕ, h_ k < (m_ k : ℝ) + 1)
    (hH : Tendsto (fun k : ℕ => H (m_ k)) atTop atTop)
    (ht : Tendsto (fun k : ℕ => t (m_ k) (n_ k)) atTop atTop) :
    (∀ k : ℕ,
      1 ≤ h_ k ∧ 2 ≤ H (m_ k) ∧
      0 < a (m_ k) ∧ 0 < rho (m_ k) ∧ rho (m_ k) < 1 ∧
      0 < A (m_ k) (n_ k) ∧
      p (n_ k) (h_ k) = K (n_ k) (h_ k) ∧
      D (m_ k) (n_ k) (h_ k) =
        1 + eps (m_ k) (n_ k) * q (m_ k) + R (m_ k) (n_ k) ∧
      (n_ k = 0 → p (n_ k) (h_ k) = 1 ∧ K (n_ k) (h_ k) = 1)) ∧
    Tendsto h_ atTop atTop ∧
    Tendsto (fun k : ℕ => N (n_ k) / (h_ k) ^ 2) atTop atTop ∧
    Tendsto (fun k : ℕ => x (n_ k) (h_ k)) atTop (𝓝 (0 : ℝ)) ∧
    (∀ d : ℝ, 0 < d → ∃ K_d : ℕ, ∀ k : ℕ, K_d ≤ k →
      0 < x (n_ k) (h_ k) ∧ x (n_ k) (h_ k) < d) ∧
    Tendsto (fun k : ℕ => D (m_ k) (n_ k) (h_ k))
      atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (fun k : ℕ => Real.log (D (m_ k) (n_ k) (h_ k)))
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun k : ℕ => T B P hB (x (n_ k) (h_ k)))
      atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (fun k : ℕ => W B P hB (n_ k) (h_ k))
      atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (fun k : ℕ => Real.log (T B P hB (x (n_ k) (h_ k))))
      atTop (𝓝 (0 : ℝ)) ∧
    (∃ K_time : ℕ,
      (∀ k : ℕ, K_time ≤ k →
        1 ≤ n_ k ∧ 0 < N (n_ k) ∧ 0 < Real.sqrt (N (n_ k)) ∧
        0 < x (n_ k) (h_ k) ∧
        g (x (n_ k) (h_ k)) = G (n_ k) (h_ k) ∧
        W B P hB (n_ k) (h_ k) = T B P hB (x (n_ k) (h_ k))) ∧
      ∃ K_pos : ℕ, K_time ≤ K_pos ∧
        ∀ k : ℕ, K_pos ≤ k →
          p (n_ k) (h_ k) = K (n_ k) (h_ k) ∧
          0 < p (n_ k) (h_ k) ∧ 0 < K (n_ k) (h_ k) ∧
          0 < D (m_ k) (n_ k) (h_ k) ∧
          0 < b B P hB (x (n_ k) (h_ k)) ∧
          0 < T B P hB (x (n_ k) (h_ k)) ∧
          0 < W B P hB (n_ k) (h_ k) ∧
          0 < p (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k)) ∧
          0 < K (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k))) := by
  -- Declaration only: accepted actual B2 API is available; proof not supplied.

theorem S3_ALG {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (m_ n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hm : ∀ k : ℕ, 1 ≤ m_ k)
    (hmh : ∀ k : ℕ, (m_ k : ℝ) ≤ h_ k)
    (hhm : ∀ k : ℕ, h_ k < (m_ k : ℝ) + 1)
    (hH : Tendsto (fun k : ℕ => H (m_ k)) atTop atTop)
    (ht : Tendsto (fun k : ℕ => t (m_ k) (n_ k)) atTop atTop) :
    ∃ K_alg : ℕ, ∀ k : ℕ, K_alg ≤ k →
      1 ≤ n_ k ∧ 0 < N (n_ k) ∧ 0 < Real.sqrt (N (n_ k)) ∧
      0 < h_ k ∧ 0 < x (n_ k) (h_ k) ∧
      0 < a (m_ k) ∧ 0 < rho (m_ k) ∧
      0 < A (m_ k) (n_ k) ∧
      0 < Real.pi * a (m_ k) / 4 ∧
      0 < p (n_ k) (h_ k) ∧ 0 < K (n_ k) (h_ k) ∧
      0 < D (m_ k) (n_ k) (h_ k) ∧
      0 < b B P hB (x (n_ k) (h_ k)) ∧
      0 < g (x (n_ k) (h_ k)) ∧
      0 < T B P hB (x (n_ k) (h_ k)) ∧
      0 < p (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k)) ∧
      0 < K (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k)) ∧
      Real.log (p (n_ k) (h_ k)) - Real.log (a (m_ k)) -
          N (n_ k) * Real.log (rho (m_ k)) =
        Real.log (D (m_ k) (n_ k) (h_ k)) ∧
      Real.log (K (n_ k) (h_ k)) - Real.log (a (m_ k)) -
          N (n_ k) * Real.log (rho (m_ k)) =
        Real.log (D (m_ k) (n_ k) (h_ k)) ∧
      Real.log (b B P hB (x (n_ k) (h_ k))) -
          Real.log (g (x (n_ k) (h_ k))) =
        Real.log (T B P hB (x (n_ k) (h_ k))) ∧
      Real.log (p (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k))) =
        Real.log (p (n_ k) (h_ k)) -
          Real.log (b B P hB (x (n_ k) (h_ k))) ∧
      Real.log (K (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k))) =
        Real.log (K (n_ k) (h_ k)) -
          Real.log (b B P hB (x (n_ k) (h_ k))) ∧
      Real.log (p (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k))) -
          C (m_ k) (n_ k) (h_ k) =
        Real.log (D (m_ k) (n_ k) (h_ k)) -
          Real.log (T B P hB (x (n_ k) (h_ k))) ∧
      Real.log (K (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k))) -
          C (m_ k) (n_ k) (h_ k) =
        Real.log (D (m_ k) (n_ k) (h_ k)) -
          Real.log (T B P hB (x (n_ k) (h_ k))) := by
  -- Declaration only: accepted actual B2 API is available; proof not supplied.

theorem S3_MAIN {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (m_ n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hm : ∀ k : ℕ, 1 ≤ m_ k)
    (hmh : ∀ k : ℕ, (m_ k : ℝ) ≤ h_ k)
    (hhm : ∀ k : ℕ, h_ k < (m_ k : ℝ) + 1)
    (hH : Tendsto (fun k : ℕ => H (m_ k)) atTop atTop)
    (ht : Tendsto (fun k : ℕ => t (m_ k) (n_ k)) atTop atTop) :
    Tendsto
      (fun k : ℕ =>
        Real.log (p (n_ k) (h_ k) /
          Shao.Probability.BrownianSup.probability B P hB
            (h_ k / Real.sqrt (N (n_ k)))) -
        (lambda * N (n_ k) / (h_ k) ^ 2 +
          N (n_ k) * Real.log (rho (m_ k)) +
          Real.log (Real.pi * a (m_ k) / 4)))
      atTop (𝓝 (0 : ℝ)) := by
  -- Declaration only: accepted actual B2 API is available; proof not supplied.

theorem S3_MAIN_epsilon {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (m_ n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hm : ∀ k : ℕ, 1 ≤ m_ k)
    (hmh : ∀ k : ℕ, (m_ k : ℝ) ≤ h_ k)
    (hhm : ∀ k : ℕ, h_ k < (m_ k : ℝ) + 1)
    (hH : Tendsto (fun k : ℕ => H (m_ k)) atTop atTop)
    (ht : Tendsto (fun k : ℕ => t (m_ k) (n_ k)) atTop atTop) :
    ∃ K_time K_pos : ℕ, K_time ≤ K_pos ∧
        (∀ k : ℕ, K_time ≤ k →
          1 ≤ n_ k ∧ 0 < N (n_ k) ∧ 0 < Real.sqrt (N (n_ k)) ∧
          0 < x (n_ k) (h_ k)) ∧
        (∀ k : ℕ, K_pos ≤ k →
          0 < h_ k ∧ 0 < a (m_ k) ∧ 0 < rho (m_ k) ∧
          0 < Real.pi * a (m_ k) / 4 ∧
          p (n_ k) (h_ k) = K (n_ k) (h_ k) ∧
          0 < p (n_ k) (h_ k) ∧ 0 < K (n_ k) (h_ k) ∧
          0 < D (m_ k) (n_ k) (h_ k) ∧
          0 < b B P hB (x (n_ k) (h_ k)) ∧
          0 < T B P hB (x (n_ k) (h_ k)) ∧
          0 < p (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k)) ∧
          0 < K (n_ k) (h_ k) / b B P hB (x (n_ k) (h_ k))) ∧
        (∀ e : ℝ, 0 < e → ∃ K_e : ℕ, K_pos ≤ K_e ∧
          ∀ k : ℕ, K_e ≤ k →
          |Real.log (p (n_ k) (h_ k) /
            Shao.Probability.BrownianSup.probability B P hB
              (h_ k / Real.sqrt (N (n_ k)))) -
            (lambda * N (n_ k) / (h_ k) ^ 2 +
              N (n_ k) * Real.log (rho (m_ k)) +
              Real.log (Real.pi * a (m_ k) / 4))| < e) := by
  -- Declaration only: accepted actual B2 API is available; proof not supplied.

end Shao.OQ4.RademacherS3Assembly

end
