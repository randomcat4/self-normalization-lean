# DA2 精确 Lean 声明候选 v1

STATUS: FROZEN_FOR_INDEPENDENT_STATEMENT_REVIEW
SCOPE: DA2_DETERMINISTIC_DERIVED_ASSEMBLY
NEW_RAW_LEAF_COUNT: 0
IMPLEMENTATION_STATUS: NOT_IMPLEMENTED
LEAN_STATUS: NOT_RUN

拟模块名：Shao.OQ4.RademacherScaleAssembly。公开增量恰为一个透明定义 eta3 和两个定理头 DA2、DA2_subcritical。下列代码块是声明契约；定理头没有证明右端，不是可直接编译的完整源文件。冻结和独立声明审查之后，才可另行授权实现。

## 共同词法环境与唯一新定义

~~~lean
import Shao.OQ4.RademacherLatticeShift
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

namespace Shao.OQ4.RademacherScaleAssembly

open Filter
open scoped Topology

open Shao.OQ4.RademacherScalarBounds
open Shao.OQ4.RademacherLatticeShift

def eta3 (n : ℕ) (h : ℝ) : ℝ := (n : ℝ) / h ^ 3
~~~

eta3 的实参是实际自然数时间和实际实阈值；没有自由相位、自由余项或自由三次尺度序列。H、u、a、rho、lambda 和 delta 均直接使用认证上游，不新建同名替身。原 N_k 在全部代码中写作 (n k : ℝ)。

## 主定理：DA2.0–DA2.3

~~~lean
theorem DA2
    (m n : ℕ → ℕ) (h : ℕ → ℝ)
    (hm : ∀ k : ℕ, 1 ≤ m k)
    (hmh : ∀ k : ℕ, (m k : ℝ) ≤ h k)
    (hmh1 : ∀ k : ℕ, h k < (m k : ℝ) + 1)
    (hh : Tendsto h atTop atTop)
    (hscale2 :
      Tendsto (fun k : ℕ => (n k : ℝ) / (h k) ^ 2) atTop atTop)
    (hscale3 :
      ∃ M : ℝ, 0 < M ∧
        ∃ K : ℕ, ∀ k : ℕ, K ≤ k → eta3 (n k) (h k) ≤ M) :
    (∀ k : ℕ,
      1 ≤ h k ∧
      0 < h k ∧
      2 ≤ H (m k) ∧
      0 < H (m k) ∧
      H (m k) = h k + delta (m k) (h k) ∧
      0 < delta (m k) (h k) ∧
      delta (m k) (h k) ≤ 1 ∧
      (h k = (m k : ℝ) → delta (m k) (h k) = 1) ∧
      h k ≠ 0 ∧
      H (m k) ≠ 0 ∧
      (h k) ^ 2 ≠ 0 ∧
      (h k) ^ 3 ≠ 0 ∧
      (h k) ^ 4 ≠ 0 ∧
      (H (m k)) ^ 2 ≠ 0 ∧
      (H (m k)) ^ 3 ≠ 0 ∧
      (H (m k)) ^ 4 ≠ 0 ∧
      4 * H (m k) ≠ 0 ∧
      2 * H (m k) ≠ 0 ∧
      0 < Real.sin (u (m k)) ∧
      Real.sin (u (m k)) ≠ 0 ∧
      0 < a (m k) ∧
      0 < rho (m k) ∧
      rho (m k) < 1 ∧
      0 < Real.pi * a (m k) / 4) ∧
    (Tendsto (fun k : ℕ => H (m k)) atTop atTop ∧
      Tendsto (fun k : ℕ => H (m k) / h k) atTop (𝓝 (1 : ℝ)) ∧
      Tendsto (fun k : ℕ => (n k : ℝ) / (H (m k)) ^ 2)
        atTop atTop ∧
      (∃ K_T : ℕ, ∀ k : ℕ, K_T ≤ k →
        (H (m k)) ^ 2 ≤ (n k : ℝ)) ∧
      (∃ K_pos : ℕ, ∀ k : ℕ, K_pos ≤ k → 0 < n k)) ∧
    (Tendsto (fun k : ℕ => (n k : ℝ) / (h k) ^ 4)
        atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun k : ℕ => 1 / (H (m k)) ^ 2)
        atTop (𝓝 (0 : ℝ)) ∧
      (∃ M' : ℝ, 0 < M' ∧
        ∃ K' : ℕ, ∀ k : ℕ, K' ≤ k →
          0 ≤ eta3 (n k) (H (m k)) ∧
          eta3 (n k) (H (m k)) ≤ M') ∧
      Tendsto
        (fun k : ℕ => eta3 (n k) (h k) -
          eta3 (n k) (H (m k)))
        atTop (𝓝 (0 : ℝ))) ∧
    Tendsto
      (fun k : ℕ =>
        lambda * (n k : ℝ) / (h k) ^ 2 +
          (n k : ℝ) * Real.log (rho (m k)) +
          Real.log (Real.pi * a (m k) / 4) -
          (Real.pi ^ 2 / 4) * eta3 (n k) (h k) *
            delta (m k) (h k))
      atTop (𝓝 (0 : ℝ))
~~~

结论第一组是全 k 的 DA2.0，第二组是 DA2.1，第三组是 DA2.2，最后的 Tendsto 是 DA2.3。没有把任何结论侧合法性或桥接条件加入假设。hscale3 只要求最终上界；其下界由自然时间和阈值正性导出。M、K、M'、K'、K_T、K_pos 均在 k 量词之前选定。

## 次临界定理：DA2.4

~~~lean
theorem DA2_subcritical
    (m n : ℕ → ℕ) (h : ℕ → ℝ)
    (hm : ∀ k : ℕ, 1 ≤ m k)
    (hmh : ∀ k : ℕ, (m k : ℝ) ≤ h k)
    (hmh1 : ∀ k : ℕ, h k < (m k : ℝ) + 1)
    (hh : Tendsto h atTop atTop)
    (hscale2 :
      Tendsto (fun k : ℕ => (n k : ℝ) / (h k) ^ 2) atTop atTop)
    (hscale3 :
      ∃ M : ℝ, 0 < M ∧
        ∃ K : ℕ, ∀ k : ℕ, K ≤ k → eta3 (n k) (h k) ≤ M)
    (hsubcritical :
      Tendsto (fun k : ℕ => eta3 (n k) (h k))
        atTop (𝓝 (0 : ℝ))) :
    Tendsto
      (fun k : ℕ =>
        lambda * (n k : ℝ) / (h k) ^ 2 +
          (n k : ℝ) * Real.log (rho (m k)) +
          Real.log (Real.pi * a (m k) / 4))
      atTop (𝓝 (0 : ℝ))
~~~

DA2_subcritical 保留冻结要求的同一固定域及全部三个尺度条件，只另加实际 eta3 趋零。即使该额外趋零本身可推出最终有界，本候选也不擅自删除冻结已有的 hscale3。

两项定理均允许早期 n k = 0；没有全项正时间或序列单调性假设。n k = k 的原文时间索引是直接特化，不另增公开包装定理。末尾 namespace 的关闭属于未来源文件排版，不是第三项公开声明。
