# U21e 冻结：完整有界紧倾斜族的实际白化、统一矩与弱Cramér装配

状态：FROZEN_FOR_INDEPENDENT_STATEMENT_REVIEW，2026-10-23。新OQ3负责人01a1669a-bca1-75e0-9d87-d07baee7b90a已获root激活。这里只冻结一条完整公开声明，不是生产实现文件或Lean认证。正式接受基线仍v42；PR169/170精确head均已获root完整独立CORRECT，root正在v43服务器整合门，尚未正式通知接受。实现分支/生产源/Lean须等正式v43通知与本声明独立CORRECT全文核读后才可开始。

原目标与来源：root-contract.md第5节有界稳定性；只读R2 report.md第38–60、74–76、83–92、343–373行，SHA572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55。直接消费者为有界情形的真实标准化族输入；本单元将PR170真实共同谱/同m原始WC与PR169真实正对称白化/实际像律均值协方差/Euclidean矩/WC合为同一公开定理。不是另加标量helper，也不把原B分析链包成假设便宣称B完成。

精确待整合seed：169 head c06e026254837782a706bcde0b8c7218c7f71eb4，CovarianceWhitening源d1f90abf2ecd59032dc5f934dbedbe9c3ab9e468f73b0d4f40b24b4a7851eec8；170 head7bf3e70682f203a08aa36043f8dc6e6e7362d701，CompactTiltCovarianceSpectrum源99b8b9b20f1860ddd7890d8b4d317825ce76572e1c0d209d6843340a33b0c634。两完整公开TYPE、全文实现和最终独立票已接收；当前只按这些精确冻结对象做静态组合声明审查，不声称它们已在main。不得将未整合源复制到旧branch或自行merge/rebase/cherry-pick/retarget。

拟模块Shao.OQ3.CompactTiltWhitenedFamily，namespace Shao.OQ3，open MeasureTheory，open scoped Matrix ENNReal NNReal，noncomputable section；0公开DEF，1公开THM。精确imports与完整TYPE如下，证明实例不得改前提或let对象。

```lean
import Shao.OQ3.CovarianceWhitening
import Shao.OQ3.CompactTiltCovarianceSpectrum
```

```lean
theorem exists_compact_tilted_whitened_family
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ᵐ x ∂mu, |x| ≤ M)
    (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (u0 v0 beta c R : ℝ)
    (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic (mu.tilted (fun x => u0 * x + v0 * x ^ 2)) xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) :
    let mu0 : Measure ℝ := mu.tilted (fun x => u0 * x + v0 * x ^ 2)
    let D0 : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance mu0
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧
      let lo : ℝ := m * D0.det / (D0 0 0 + D0 1 1)
      let hi : ℝ := 2 * (M ^ 2 + M ^ 4) + 1 + lo
      let c0 : ℝ := m ^ 2 * c / 2
      let mup : (ℝ × ℝ) → Measure ℝ := fun p =>
        mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
      let D : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p => parabolaCovariance (mup p)
      let s : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 * D p 1 1 - (D p 0 1) ^ 2)
      let t : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 + D p 1 1 + 2 * s p)
      let A : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p =>
        ![![(D p 1 1 + s p) / (s p * t p), -(D p 0 1) / (s p * t p)],
          ![-(D p 0 1) / (s p * t p), (D p 0 0 + s p) / (s p * t p)]]
      let means : (ℝ × ℝ) → (Fin 2 → ℝ) := fun p =>
        ![∫ x, x ∂mup p, ∫ x, x ^ 2 ∂mup p]
      let Y : (ℝ × ℝ) → ℝ → (Fin 2 → ℝ) := fun p x =>
        A p *ᵥ (![x, x ^ 2] - means p)
      let nu : (ℝ × ℝ) → Measure (Fin 2 → ℝ) := fun p => (mup p).map (Y p)
      let Phi : (ℝ × ℝ) → ℝ → ℝ → ℂ := fun p xi eta =>
        ∫ y : Fin 2 → ℝ,
          Complex.exp (((xi * y 0 + eta * y 1 : ℝ) : ℂ) * Complex.I) ∂nu p
      let L : ℝ := 1 / Real.sqrt hi
      let U : ℝ := 1 / Real.sqrt lo
      let Q : ℝ := 4 * U * (M + M ^ 2)
      let cA : ℝ := c0 * Real.rpow U (-beta)
      let RA : ℝ := R / L
      0 < lo ∧ lo < hi ∧ 0 < c0 ∧
        0 < L ∧ 0 < U ∧ 0 ≤ Q ∧ 0 < cA ∧ 0 ≤ RA ∧
        ∀ p ∈ K,
          IsProbabilityMeasure (mup p) ∧ (∀ᵐ x ∂mup p, |x| ≤ M) ∧
          MemLp (fun x : ℝ => x) 2 (mup p) ∧
          MemLp (fun x : ℝ => x ^ 2) 2 (mup p) ∧
          (ENNReal.ofReal m • mu0 ≤ mup p) ∧
          (∀ xi eta : ℝ,
            lo * (xi ^ 2 + eta ^ 2) ≤
                xi ^ 2 * D p 0 0 + 2 * xi * eta * D p 0 1 + eta ^ 2 * D p 1 1 ∧
              xi ^ 2 * D p 0 0 + 2 * xi * eta * D p 0 1 + eta ^ 2 * D p 1 1 ≤
                hi * (xi ^ 2 + eta ^ 2)) ∧
          (∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
            ‖jointCharacteristic (mup p) xi eta‖ ≤
              1 - c0 * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) ∧
          0 < s p ∧ 0 < t p ∧ (A p)ᵀ = A p ∧ A p * D p * A p = 1 ∧
          (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 →
            0 < xi * (A p *ᵥ ![xi, eta]) 0 + eta * (A p *ᵥ ![xi, eta]) 1) ∧
          IsProbabilityMeasure (nu p) ∧
          (∀ i : Fin 2, MemLp (fun y : Fin 2 → ℝ => y i) 2 (nu p) ∧
            (∫ y : Fin 2 → ℝ, y i ∂nu p) = 0) ∧
          (∀ i j : Fin 2,
            ProbabilityTheory.covariance (fun y : Fin 2 → ℝ => y i)
              (fun y : Fin 2 → ℝ => y j) (nu p) = if i = j then 1 else 0) ∧
          (∀ᵐ y : Fin 2 → ℝ ∂nu p, Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2) ≤ Q) ∧
          (∀ k : ℕ,
            Integrable (fun y : Fin 2 → ℝ => (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k)
              (nu p) ∧
            (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k ∂nu p) ≤ Q ^ k) ∧
          ∀ xi eta : ℝ, RA < Real.sqrt (xi ^ 2 + eta ^ 2) →
            ‖Phi p xi eta‖ ≤
              1 - cA * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)
```

对象与量词契约：输入仅同一个真实基础概率mu、有限M及真实AE界、任意紧K、任意参考u0/v0、诚实非负beta/R与正c及该参考倾斜上的实际WC。不输入任何族概率/L²/共同谱/矩/白化矩阵/频率比较或全族WC。参考不必在K，K可空，M=0、beta=0、R=0及零频率/自然零阶必须保留；不加入参数联合可测性。m先于全部p/频率/k选定，measure lower/c0/lo/cA使用同m；D/means/Y/nu/Phi均为字面实际对象，不能替换代理law/自由中心/任意矩阵。全部半径与矩均使用字面Euclidean sqrt。k=9可供有界8+delta且delta=1，未宣称一般非整数矩或无界情形。

声明可消费性门：170的exists_compact_tilted_covariance_spectral_bounds一次产生同m、lo>0、lo<hi、c0>0和全部p的概率/AE/L²/measure lower/谱/rawWC；lo<hi与lo>0给169所需hi>0。169的uniform_covariance_whitened_moments_weakCramer一次消费该真实族、同lo/hi/M/beta/c0/R，产生同一字面D/s/t/A/means/Y/nu/Phi和L/U/Q/cA/RA下的全部白化/矩/WC。不得在实现中另选m、重新归一化law、手给hspec或hfreq；不新增语义假设。此段是待独立审查的接口匹配说明，不替代独立票。

来源范围与剩余：本候选承担原C有界紧倾斜族从单点真实WC到同族实际谱/标准化及统一矩/WC的端到端组合；其通过仍须完整实现、全部actual module-owner TYPE/公理、fresh proof与root原C最终冻结范围验收，不能凭声明审查关闭C。原A仅修正vCorr/fixedx0已正式闭合；B仍需实际generic Hessian/covariance及均值逆、外部Song逐条件证明/Edgeworth、胞重建、Laplace/远概率链，D仍需丢番图十六原子和小x鞍点；beta<2/5仅充分，未声称最优/端点/新颖性。

执行与完整性：本轮仅local轻量写本冻结scope与本线状态；不创建生产Lean源、Audit/probe或远程分支。后续收到root正式v43接受通知后，才在own worktree从正式accepted checkpoint正常新分支，所有旧refs与已成功源保持，不自行整合。唯一fresh独立声明审查者只拥有u21e-statement-review.md，不读作者证明/implementation notes，先仅对fence完整imports/TYPE盲译落盘，再读冻结说明、原来源和精确public seed做来源/接口门；本门不运行Lean、不扫描全Mathlib/缓存、不重跑成功检查。全部后续Lean仅serverCPU14–17/native8192MiB/j4/autoImplicit=false/oneheavy，root独占cache/common/imports/pins/integration，外部CPU0–9/80GiB不动。禁sorry/admit/newaxiom/unsafe/native_decide/implemented_by/证明设置弱化。模型gpt-6.1-sol xhigh fresh，租约1且实际平台上限优先；不启动math-ultra。
