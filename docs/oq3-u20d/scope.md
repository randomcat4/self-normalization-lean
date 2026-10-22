# U20d 冻结候选：同源律的规范鞍点、实际正定 Hessian 与几何常数

状态：FROZEN_FOR_INDEPENDENT_STATEMENT_REVIEW。上一U20c完整235行CORRECT终票已全文读后接受并精确发布PR156，head7dcf60695c046d0d89e96b92ccd25604e444cfe9，parent为v38 accepted ffdedd610d0af501c3dd4672cf7f78d80eee543c；六文件一提交已核并附chat。U21a声明CORRECT仍DEFERRED_UNIMPLEMENTED，不改其命题或计作proof。

来源：current/oq3/proofs/r1/report.md 141–159、239–257、431–443，SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662；root-contract.md对同P的规范K/实际协方差和几何常数要求；接受PR151的真实积分一阶/完整二阶导数、PR148的实际几何恒等式、PR156的真实全域/规范值绑定。只用调用者同一个q/w和full4约束，不另选law，不手给导数、正定或几何结论。

模块Shao.OQ3.SourceCanonicalSaddle，namespace Shao.OQ3，0公开定义/1公开完整定理。精确imports：

```lean
import Shao.OQ3.SourceCanonicalRate
import Shao.OQ3.SourceLogPartitionDerivatives
import Shao.OQ3.SourceGeometricScale
import Shao.OQ3.PositiveRate
```

open MeasureTheory Shao.Probability，open scoped Matrix Topology BigOperators，noncomputable section。完整公开TYPE如下；letI内hm0实际证明也是冻结内容。

```lean
theorem source_canonical_saddle_hessian_and_scale
    (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 < w i)
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k)) :
    let P : Measure ℝ := originalMeasure sourceEll w
    letI : IsProbabilityMeasure P := originalMeasure_isProbabilityMeasure sourceEll w
      (fun i => (hw i).le)
      (by simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one]
        using hm 0)
    let W : ℝ → ℝ × ℝ := fun x => (x, x ^ 2)
    ∃ lift : (Fin 2 → ℝ) → bivariateMGFDomain P W,
      (∀ theta, (lift theta : ℝ × ℝ) = (theta 0, theta 1)) ∧
      let K : (Fin 2 → ℝ) → ℝ := fun theta => bivariateLogMGF P W (lift theta)
      let theta0 : Fin 2 → ℝ := ![8 * sourceEll, -sourceEll]
      let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (atomicMeasure w)
      let pr : Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
      let gradient : (Fin 2 → ℝ) →L[ℝ] ℝ :=
        (pr 0).smulRight (q / 4) + (pr 1).smulRight q
      let hessian : (Fin 2 → ℝ) →L[ℝ] ((Fin 2 → ℝ) →L[ℝ] ℝ) :=
        ∑ i : Fin 2, ∑ j : Fin 2, (pr i).smulRight ((pr j).smulRight (D i j))
      let x0 : ℝ := Real.sqrt q / 4
      let a0 : ℝ := q / 4
      let s0 : ℝ := 8 * sourceEll
      let t0 : ℝ := -sourceEll
      let v : Fin 2 → ℝ := ![1, 2 * a0 / x0 ^ 2]
      let lambda0 : ℝ := s0 * a0 + t0 * q - K theta0
      let lambda1 : ℝ := 2 * t0 / x0 ^ 2 + dotProduct v (D⁻¹ *ᵥ v)
      let vCorr : ℝ := (-t0) * Real.sqrt D.det * Real.sqrt lambda1
      (∀ theta, K theta =
        Real.log (∫ x : ℝ, Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂P)) ∧
      HasFDerivAt K gradient theta0 ∧
      HasFDerivAt (fun theta => fderiv ℝ K theta) hessian theta0 ∧
      (∀ u : Fin 2 → ℝ, u ≠ 0 → 0 < dotProduct u (D *ᵥ u)) ∧
      0 < x0 ∧ q = a0 ^ 2 / x0 ^ 2 ∧ s0 = -2 * a0 * t0 / x0 ^ 2 ∧ t0 < 0 ∧
      lambda0 = saddleRate sourceEll q w ∧ 0 < lambda0 ∧
      0 < D.det ∧ 0 < lambda1 ∧ 0 < vCorr ∧
      correctedInverseScale sourceEll q (atomicMeasure w) = vCorr⁻¹
```

量词/域门：P是originalMeasure，不是atomicMeasure；倾斜后的atomicMeasure只出现在真实D中。所有正权给非负权和四个正base原子，hm0给真实概率。lift覆盖所有Fin2实参数，输出其pair坐标恒等式和规范K对整个ambient函数的literal积分等式。必须先证明整体函数等式，再在K和fderiv K内部重写并转移PR151的真实HasFDerivAt；禁止直接对子类型求导，也不能仅用鞍点处数值相等转移导数。

正定门：对所有非零u，证明真实dotProduct u (D*ᵥu)>0，不仅detD>0。可由RegularCovariance公开centered_parabola_integral_pos/eq、实际bounded atomic概率与正base单点质量产生；u≠0须真实给u0≠0或u1≠0，Fin2矩阵展开且D10=D01。PR151的导数矩阵与几何PR148必须是这同一个actual D，不能引入自由正定矩阵代替。

标量门：x0=sqrtq/4、a0=q/4、s0=8ell、t0=-ell，输出正x0、q=a0²/x0²、s0=-2a0t0/x0²与t0<0。lambda0是此规范K真实测试值，须识别为同saddleRate且严格正。lambda1是完整逆矩阵切向二次型与2t0/x0²的实际源曲率，vCorr=(-t0)sqrt(detD)sqrt(lambda1)严格正，并与真实correctedInverseScale互为倒数。q>1消除全部分母/sqrt退化，不能利用零倒数的全定义值掩盖退化。

承重/直接消费者：消除原A同sourceP规范ambient梯度/完整Hessian/正定及实际鞍点和几何常数绑定的缺口；下一rootA组装从U20b一次取同q/w/P，然后同时消费PR156和本全称producer，保持真正有限乘积尾概率、同律严格递增余项见证和标准非大O。没有在此输出全称C²邻域、均值映射邻域逆、统一远域率间隙/概率界、标准化WC、Edgeworth或原B/C/D后续。原A/B/C/D全部OPEN，不声称β<2/5最优。

环境/执行门：从已接受PR156 exact head正常新建owned feat/oq3-source-canonical-saddle；未读完整CORRECT声明终票前不建branch/写Lean源/跑probe。复用已验证U20c run只读单Shao-root import-view：OQ3指own现有build、Probability指接受v38 build，原Mathlib等路径保留；没有二进制复制、cache/shared/root写。实际四imports候选图/源哈希与对象元数据作为独立门附件，已过图不重复。首次完整源strict targeted Lean native8192MiB/j4/autoImplicit=false/CPU14–17，一个heavy；首次成功后不重跑。随后首次实际module-owner全常量TYPE/传递公理Audit，完整独立proof终票hash核并整份lead阅读后才接受/commit/精确PR。失败/修正历史不删，无sorry/admit/newaxiom/unsafe/native_decide/implemented_by或设置弱化。root独占公共定义/cache/pins/import/integration/merge/rebase/retarget，153/156等冻结heads不动，外部CPU0–9/80GiB不动。

精确四imports候选图已一次完成：25Shao/2783Mathlib物理图，公开图25Shao/2533Mathlib+189external，全部source/olean存在，formal25 compact a2bc1daeb0e36fb2393964fd1e113b073b30ddf3419439097c29d2c7915a4867，candidate-cache.json SHA2cb1d88b595345f6594f95cff9ce803a005c7140acfcdfac1de05072e2db3a89。所有25项目源码来自当前已接受PR156/v38祖先；导入对象沿已核只读view存在。首次transport等待30秒超时，但随后只读检查确认完整artifact已生成；未重放或重复图。
