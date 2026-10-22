# 完整实际 S2：形式声明冻结 v1

STATUS: FROZEN_FOR_FRESH_STATIC_STATEMENT_REVIEW
LEAN_STATUS: NOT_RUN
PROOF_IMPLEMENTATION_AUTHORIZATION: NONE
ROOT_STATUS: OPEN

本冻结只固定下列透明定义、命名空间和完整定理头。只做来源到声明的独立核对，不含任何证明或证明占位，也不授权 Source、Lean、发射或 Git。数学范围以原 spectrum01.md b65f9e0c 和数学冻结 c59971859b432bf312d5c1d65ca82d0a02254c06d4d56833322364f87f69146e 为准；不得增加、删除、弱化或重新解释前提。任何修改另立版本，原件保留。

实际 U1 已认证并发布 PR127，冻结 head c340b9f27c497ce0959e54aa49bc41ef055ae959，公开 Tail.absoluteC / remainder_uniform 可消费；这只是 hash-only 上游门，不读取其作者或审查理由。以下代码从已交付声明提案唯一 Lean 代码块连续逐字抽取，不附作者的解释、自查或身份。

```lean
import Shao.OQ4.RademacherSpectralTail
import Shao.OQ4.RademacherScalarBounds

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Shao.OQ4.RademacherS2Assembly

def H (m : ℕ) : ℝ := (m : ℝ) + 1

def N (n : ℕ) : ℝ := (n : ℝ)

def t (m n : ℕ) : ℝ := N n / H m ^ 2

def a (m : ℕ) : ℝ := RademacherSpectralPairing.amplitude m

def rho (m : ℕ) : ℝ := RademacherSpectralPairing.rho m

def eps (m n : ℕ) : ℝ := RademacherSpectralPairing.epsilon m n

def q (m : ℕ) : ℝ := (Real.tan (RademacherScalarBounds.u m)) ^ 2

def R (m n : ℕ) : ℝ := RademacherSpectralPairing.remainder m n

def B (m n : ℕ) : ℝ := a m * rho m ^ n

def p (n : ℕ) (h : ℝ) : ℝ :=
  (Measure.pi (fun _ : Fin n => RademacherCosine.law)).real
    (@Shao.closedStrip n h)

def K (n : ℕ) (h : ℝ) : ℝ :=
  @Shao.OQ4.killedMass RademacherCosine.law
    RademacherCosine.law_isProbabilityMeasure h n (0 : ℝ)

def D (m n : ℕ) (h : ℝ) : ℝ := p n h / B m n

def C_U : ℝ := RademacherSpectralTail.absoluteC

theorem definition_bridges (m : ℕ) :
    RademacherSpectralPairing.alpha m 0 = RademacherScalarBounds.u m ∧
    RademacherSpectralPairing.beta m 0 = RademacherScalarBounds.z m ∧
    a m =
      (1 / H m) *
        (Real.cos (RademacherScalarBounds.u m) /
          Real.sin (RademacherScalarBounds.u m)) ∧
    a m = RademacherScalarBounds.a m ∧
    rho m = Real.cos (RademacherScalarBounds.z m) ∧
    rho m = RademacherScalarBounds.rho m

theorem F0 (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) (n : ℕ) :
    0 < a m ∧
    0 < rho m ∧
    rho m < 1 ∧
    0 < B m n ∧
    p n h = K n h ∧
    p n h = B m n * (1 + eps m n * q m + R m n) ∧
    D m n h = K n h / B m n ∧
    D m n h = 1 + eps m n * q m + R m n

theorem F0_zero_time (m : ℕ) (hm : 1 ≤ m) (h : ℝ)
    (hmh : (m : ℝ) ≤ h) (hhm : h < (m : ℝ) + 1) :
    p 0 h = 1 ∧
    K 0 h = 1 ∧
    RademacherSpectralPairing.zeroMode m 0 =
      (if Even m then (-1 : ℝ) ^ (m / 2) / H m else 0)

theorem F0_small_cells :
    (∀ n : ℕ, R 1 n = 0) ∧
    (∀ n : ℕ, 1 ≤ n → R 2 n = 0) ∧
    RademacherSpectralPairing.zeroMode 2 0 = -(1 / 3 : ℝ) ∧
    R 2 0 = -1 / (3 * a 2) ∧
    R 2 0 ≠ 0

theorem T0 {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ q m ∧
    q m ≤ Real.pi ^ 2 / (4 * H m ^ 2) ∧
    ∀ n : ℕ, |eps m n| = 1

theorem F1 :
    0 < C_U ∧
    ∀ m : ℕ, 1 ≤ m →
    ∀ h : ℝ, (m : ℝ) ≤ h → h < (m : ℝ) + 1 →
    ∀ n : ℕ, H m ^ 2 ≤ N n →
      |R m n| ≤
        C_U * Real.exp (-Real.pi ^ 2 * N n / H m ^ 2) ∧
      |D m n h - 1 - eps m n * q m| ≤
        C_U * Real.exp (-Real.pi ^ 2 * N n / H m ^ 2) ∧
      |D m n h - 1| ≤
        Real.pi ^ 2 / (4 * H m ^ 2) +
          C_U * Real.exp (-Real.pi ^ 2 * N n / H m ^ 2)

theorem Q1 (m_ n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hm : ∀ k : ℕ, 1 ≤ m_ k)
    (hmh : ∀ k : ℕ, (m_ k : ℝ) ≤ h_ k)
    (hhm : ∀ k : ℕ, h_ k < (m_ k : ℝ) + 1)
    (hH : Tendsto (fun k : ℕ => H (m_ k)) atTop atTop)
    (ht : Tendsto (fun k : ℕ => t (m_ k) (n_ k)) atTop atTop) :
    (∀ k : ℕ,
      0 < a (m_ k) ∧
      0 < rho (m_ k) ∧
      rho (m_ k) < 1 ∧
      0 < B (m_ k) (n_ k) ∧
      p (n_ k) (h_ k) = K (n_ k) (h_ k) ∧
      p (n_ k) (h_ k) =
        B (m_ k) (n_ k) *
          (1 + eps (m_ k) (n_ k) * q (m_ k) + R (m_ k) (n_ k)) ∧
      D (m_ k) (n_ k) (h_ k) =
        K (n_ k) (h_ k) / B (m_ k) (n_ k) ∧
      D (m_ k) (n_ k) (h_ k) =
        1 + eps (m_ k) (n_ k) * q (m_ k) + R (m_ k) (n_ k) ∧
      (n_ k = 0 →
        p (n_ k) (h_ k) = 1 ∧ K (n_ k) (h_ k) = 1)) ∧
    (∃ K_time : ℕ, ∀ k : ℕ, K_time ≤ k →
      H (m_ k) ^ 2 ≤ N (n_ k) ∧
      1 ≤ n_ k ∧
      |R (m_ k) (n_ k)| ≤
        C_U * Real.exp
          (-Real.pi ^ 2 * N (n_ k) / H (m_ k) ^ 2) ∧
      |D (m_ k) (n_ k) (h_ k) - 1 -
          eps (m_ k) (n_ k) * q (m_ k)| ≤
        C_U * Real.exp
          (-Real.pi ^ 2 * N (n_ k) / H (m_ k) ^ 2) ∧
      |D (m_ k) (n_ k) (h_ k) - 1| ≤
        Real.pi ^ 2 / (4 * H (m_ k) ^ 2) +
          C_U * Real.exp
            (-Real.pi ^ 2 * N (n_ k) / H (m_ k) ^ 2)) ∧
    Tendsto
      (fun k : ℕ => Real.pi ^ 2 / (4 * H (m_ k) ^ 2))
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto
      (fun k : ℕ =>
        C_U * Real.exp (-Real.pi ^ 2 * N (n_ k) / H (m_ k) ^ 2))
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun k : ℕ => D (m_ k) (n_ k) (h_ k))
      atTop (𝓝 (1 : ℝ)) ∧
    Tendsto
      (fun k : ℕ => K (n_ k) (h_ k) / B (m_ k) (n_ k))
      atTop (𝓝 (1 : ℝ)) ∧
    (∃ K_pos : ℕ, ∀ k : ℕ, K_pos ≤ k →
      0 < D (m_ k) (n_ k) (h_ k) ∧
      0 < p (n_ k) (h_ k) ∧
      0 < K (n_ k) (h_ k) ∧
      Real.log (p (n_ k) (h_ k)) - Real.log (a (m_ k)) -
          N (n_ k) * Real.log (rho (m_ k)) =
        Real.log (D (m_ k) (n_ k) (h_ k)) ∧
      Real.log (K (n_ k) (h_ k)) - Real.log (a (m_ k)) -
          N (n_ k) * Real.log (rho (m_ k)) =
        Real.log (D (m_ k) (n_ k) (h_ k))) ∧
    Tendsto
      (fun k : ℕ => Real.log (D (m_ k) (n_ k) (h_ k)))
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto
      (fun k : ℕ =>
        Real.log (p (n_ k) (h_ k)) - Real.log (a (m_ k)) -
          N (n_ k) * Real.log (rho (m_ k)))
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto
      (fun k : ℕ =>
        Real.log (K (n_ k) (h_ k)) - Real.log (a (m_ k)) -
          N (n_ k) * Real.log (rho (m_ k)))
      atTop (𝓝 (0 : ℝ))

end Shao.OQ4.RademacherS2Assembly

end
```
