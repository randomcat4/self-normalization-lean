# U22a 原根A冻结候选：单一固定联合非格点律的实际自归一化反例

状态：FROZEN_FOR_INDEPENDENT_ROOT_STATEMENT_REVIEW。root v39已正式接受153/156/158联合checkpoint，要求优先补原A最后同律/有限乘积概率组装。U21a完整200行终票已全文读并PR159发布；其后U20e v1完整202行CRITICAL GAPS终票亦全文读并保留：数学C∞路线有效，但冻结header缺ContDiff作用域，DEFERRED_UNIMPLEMENTED_ENVIRONMENT_GAP，无源/probe/Audit/branch。该正则性路线不作为本A的前提或阻塞，也不被称已通过。

原目标：root-contract.md§3拟定的exists_fixed_jointNonlattice_saddleExpansion_counterexample；R1 report.md全反例链，特别141–159、161–257、259–307、495–550和(31)，SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662。原ICM OQ3固定x误差问题由root v39 oq3-review§1/§7核过；本节点只回答固定x反例，不覆盖随x变化的一致展开。使用R1已冻结修正常数vCorr，不照抄有误的印刷常数。不要求一般rho KL9/10、精确ζ系数24或可选超多项式近共振14a；既有直接指数测试和严格正h^(3/2)下界已由root接受为反例所需生产链。

模块Shao.OQ3.SourceCounterexampleRoot，namespace Shao.OQ3，0公开定义/1完整公开原根THM。精确imports：

```lean
import Shao.OQ3.SourceRemainderNotBigO
import Shao.OQ3.SourceCanonicalSaddle
```

open MeasureTheory Shao.Probability，open scoped Matrix Topology BigOperators，noncomputable section。完整TYPE如下；没有调用者数学前提，所有q/w/概率等均为输出见证。

```lean
theorem exists_fixed_jointNonlattice_saddleExpansion_counterexample :
    ∃ (q : ℝ) (w : AtomicIndex → ℝ),
      (1 < q ∧ q < 103 / 100 ∧ (∀ i, 0 < w i) ∧
        ∀ k : Fin 4,
          HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
            (constraintTarget q k)) ∧
      let P : Measure ℝ := originalMeasure sourceEll w
      ∃ hP : IsProbabilityMeasure P,
        letI : IsProbabilityMeasure P := hP
        let W : ℝ → ℝ × ℝ := fun x => (x, x ^ 2)
        let x0 : ℝ := Real.sqrt q / 4
        let a0 : ℝ := q / 4
        let s0 : ℝ := 8 * sourceEll
        let t0 : ℝ := -sourceEll
        let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (atomicMeasure w)
        let Dtail : Set (ℝ × ℝ) := {z | 0 < z.2 ∧ x0 * Real.sqrt z.2 ≤ z.1}
        (Integrable (fun x : ℝ => x) P ∧ (∫ x : ℝ, x ∂P) = 0) ∧
          (∀ᵐ x ∂P, 1 ≤ |x| ∧ |x| ≤ 4 + Real.sqrt 10) ∧
          0 < P.real (Set.Ioi 0) ∧
          (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 → ‖jointCharacteristic P xi eta‖ < 1) ∧
          Filter.Tendsto (fun J => |resonanceXi J| + |resonanceEta J|)
            Filter.atTop Filter.atTop ∧
          Filter.Tendsto (fun J => ‖jointCharacteristic P (resonanceXi J) (resonanceEta J)‖)
            Filter.atTop (nhds (1 : ℝ)) ∧
          bivariateMGFDomain P W = Set.univ ∧
          (∀ theta : bivariateMGFDomain P W,
            (0 < ∫ x : ℝ, Real.exp
              ((theta : ℝ × ℝ).1 * x + (theta : ℝ × ℝ).2 * x ^ 2) ∂P) ∧
            bivariateLogMGF P W theta =
              Real.log (∫ x : ℝ, Real.exp
                ((theta : ℝ × ℝ).1 * x + (theta : ℝ × ℝ).2 * x ^ 2) ∂P)) ∧
          ∃ lift : (Fin 2 → ℝ) → bivariateMGFDomain P W,
            (∀ theta, (lift theta : ℝ × ℝ) = (theta 0, theta 1)) ∧
            let K : (Fin 2 → ℝ) → ℝ := fun theta => bivariateLogMGF P W (lift theta)
            let theta0 : Fin 2 → ℝ := ![s0, t0]
            let pr : Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
            let gradient : (Fin 2 → ℝ) →L[ℝ] ℝ :=
              (pr 0).smulRight a0 + (pr 1).smulRight q
            let hessian : (Fin 2 → ℝ) →L[ℝ] ((Fin 2 → ℝ) →L[ℝ] ℝ) :=
              ∑ i : Fin 2, ∑ j : Fin 2, (pr i).smulRight ((pr j).smulRight (D i j))
            let v : Fin 2 → ℝ := ![1, 2 * a0 / x0 ^ 2]
            let lambda0 : ℝ := s0 * a0 + t0 * q - K theta0
            let lambda1 : ℝ := 2 * t0 / x0 ^ 2 + dotProduct v (D⁻¹ *ᵥ v)
            let vCorr : ℝ := (-t0) * Real.sqrt D.det * Real.sqrt lambda1
            let nu : (n : ℕ) → Measure (Shao.Path n) :=
              fun n => Measure.pi (fun _ : Fin n => P)
            let Tail : (n : ℕ) → Set (Shao.Path n) := fun n =>
              {z | x0 ≤ (∑ i, z i) / (Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy z))}
            let C : ℕ → ℝ := fun n =>
              Real.sqrt (2 * Real.pi * (n : ℝ)) * Real.exp ((n : ℝ) * lambda0) *
                (nu n).real (Tail n)
            (∀ theta, K theta =
              Real.log (∫ x : ℝ, Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂P)) ∧
            HasFDerivAt K gradient theta0 ∧
            HasFDerivAt (fun theta => fderiv ℝ K theta) hessian theta0 ∧
            (∀ u : Fin 2 → ℝ, u ≠ 0 → 0 < dotProduct u (D *ᵥ u)) ∧
            0 < x0 ∧ x0 < 1 / 2 ∧ 0 < a0 ∧
            q = a0 ^ 2 / x0 ^ 2 ∧ s0 = -2 * a0 * t0 / x0 ^ 2 ∧ t0 < 0 ∧
            lambda0 = saddleRate sourceEll q w ∧ 0 < lambda0 ∧
            0 < D.det ∧ 0 < lambda1 ∧ 0 < vCorr ∧
            correctedInverseScale sourceEll q (atomicMeasure w) = vCorr⁻¹ ∧
            (a0, q) ∈ Dtail ∧
            bivariateLegendreRate P W (a0, q) = (lambda0 : EReal) ∧
            (∀ z ∈ Dtail,
              bivariateLegendreRate P W (a0, q) ≤ bivariateLegendreRate P W z ∧
              (bivariateLegendreRate P W z = bivariateLegendreRate P W (a0, q) ↔
                z = (a0, q))) ∧
            (∀ n : ℕ, MeasurableSet (Tail n)) ∧
            (∀ n : ℕ, 0 < n → ∀ᵐ z ∂nu n, 0 < Shao.energy z) ∧
            (∀ n : ℕ, 0 < n → sourceTail q n =ᵐ[nu n] Tail n) ∧
            (∀ n : ℕ, normalizedTailCoefficient sourceEll q w n = C n) ∧
            (∃ nseq : ℕ → ℕ, StrictMono nseq ∧
              Filter.Tendsto nseq Filter.atTop Filter.atTop ∧
              ∀ J : ℕ, 0 < nseq J ∧
                (J : ℝ) < Real.sqrt (nseq J : ℝ) * (C (nseq J) - vCorr⁻¹)) ∧
            ¬ Asymptotics.IsBigO Filter.atTop
              (fun n : ℕ => C n - vCorr⁻¹)
              (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹)
```

单律/量词门：没有caller前提，q/w只存在一次，所有严格质量、完整四约束均为输出；∃hP是同P概率的输出证明见证，随后letI只是让规范对象取得真实NeZero，不是暗加假设。先取U20b一个同q/w/P/nseq，全部后续全称适配只实例化该同w/q；不得分别取存在族后拼接。P、x0、theta0、D、lambda0/1、vCorr和C均固定于全部n/J之外。nseq严格递增/atTop/正自然数及每J严格缩放差>J同时保留，比原bJ最终下界更强，取b=1/J0=0即可；标准否大O使用真实范数定义，非带符号或子列自定义谓词。

规范门：true Integrable domK=univ、所有域内正partition/literal值，以及全Fin2 lift坐标/整个K函数身份/真实梯度/fderiv二阶/实际D严格二次型均来自接受156/158。D只为同w的atomicMeasure下Cov(X,X²)，不是原P未倾斜协方差。候选(a0,q)有限EReal率=lambda0以及完整c>0弱尾域全局比较/等号唯一保留不可实现点及+∞，不对所有矩点设有限、不给toReal、不纳c=0。theta0/梯度/鞍点方程/actual lambda0/1/vCorr/倒数尺度全部同值绑定，a0>0由q>1合法产生。

真实概率门：nu n字面为同一个P的有限产品，Tail n字面为S_n/(sqrt(n)*sqrt(energy))≥x0，与源S_n/V_n≥x0 sqrt(n)等价。必须证明Tail Borel可测。n>0下从P的AE1≤|X|逐坐标拉回/ae_all_iff/平方求和得energy≥n>0；不能假定所有实向量都正能量。正分母后用sqrt_mul、le_div_iff给sourceTail与Tail的实际AE集合等式；再用测度同余而非事件名称宣称概率等。n=0无需正能量，归一化前因子sqrt0=0单独证明全n coefficient身份；这使完整函数上的标准notIsBigO和同nseq差可真实重写。不得换抽象标量序列、n依赖律、平方后丢正尾符号或在energy0上非法约分。

承重/闭合边界：这是root v39 oq3-review§7点名尚缺的原A组装THM，完成后仍须本原根完整独立source/statement/proof/首servercheck/ownerAudit和root正式验收，lead不能仅据旧三个辅助模块数量提前关A。一般KL9/10、精确ζ系数24、可选14a不是本反例必要义务且不宣称已证；均值逆/全邻域C∞、B的标准化谱/矩/WC/Edgeworth/格胞/远概率、C/D后续均仍独立。当前所有原根A/B/C/D OPEN，β<2/5仅充分，不声称最优。

接受/环境：root PR160 main67df1c9775f519d34260a14b78f120485539eba3，accepted59a531b89eff7c11e4fc53583067f2cd3b53a517，finaltree43577d0d66de8325a756c9ac25e43e53809c3525，receipt-v39 SHAdfea5cdd6b37f0509af4cd9412e0188e5de8f28934d8970cfdf908f61af9b2c3。receipt的gatecode808c786b/tree6f41da6c另记，不冒充最终树。接受依赖并集：PR153正式67项+PR158正式25项+两seed，74canonical source paths无冲突，与v39receipt及实际接受worktree源全匹配；canonical74c0e75a48979e6cf28bcd1f232624543b313425df2d0280da7057c32ede836703。candidate-source-union.json SHA55584f88d8f05b3616147818250113799d8fa99f7a412f2c61cbba019ba67925；readiness.json SHAdeaec5a5039afba553ab36b95eb78e565a50da87a7b4b4ac571e1305976e4194。74既有对象沿已实际核验U20c只读单Shao-root view存在，OQ3为own build，Probability引用接受v38目录（本依赖Common源与v39相同），Mathlib路径保留。复用接受完整图/统一gate，不重扫大图/pins/cachehash/smoke，不复制二进制或写shared/root。

执行：整份独立CORRECT原根声明终票hash核且全部lead读完后，才从v39 accepted正常新建owned feat/oq3-source-counterexample-root，无reset/rebase/merge/fetch/retarget/sourcecopy，9旧frozenheads保留。首完整源targeted Lean/serverCPU14–17/native8192MiB/j4/autoImplicit=false，仅一个heavy；失败/修正全留，首成功不重跑。随后首次actualmoduleowner全部TYPE及传递公理Audit，禁止sorry/admit/newaxiom/unsafe/native_decide/implemented_by/设置弱化，白名单propext/Classical.choice/Quot.sound；再独立完整原根proof终票hash核且整份lead读完后才接受/commit/精确PR并交root验收。不新agent/chat/goal，复用sole reviewer lease1，root独占commondefs/cache/pins/rootimports/integration，外部CPU0–9/80GiB不动。
