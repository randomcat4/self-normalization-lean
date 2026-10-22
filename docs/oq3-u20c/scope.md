# U20c v2 环境修正冻结候选：同源律的规范Legendre率与完整正能量尾域唯一极小点

状态：FROZEN_FOR_INDEPENDENT_ENVIRONMENT_REVIEW_V2。U20b已完整接受/发布PR153；U21a声明通过后暂存UNIMPLEMENTED。本U20c v1完整191行声明CORRECT已全部读完后正常新建feat/oq3-source-canonical-rate于v38 ffdedd，并写完整99行源；首次build01仅import失败，proof未elaborate。当前有未跟踪源且无成功Lean/Audit/proof验收；不是无源/未建分支状态。v1历史文件原样保留。

来源：R1 report.md161–307，SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662；root-contract.md真实domK/EReal与正能量弱尾域规范；已接受PR146真实全参数指数上界/达到及逐点严格分离器。root明确v38后第一优先消费者。全部w/q来自调用者同一全4约束，禁止另选存在族；实际最终law在后续用已接受U20b的同w/q实例化此全称适配。

模块Shao.OQ3.SourceCanonicalRate，namespace Shao.OQ3，0公开定义/1公开完整定理。精确imports：

```lean
import Shao.OQ3.SourceGlobalExponentialTests
import Shao.Probability.BivariateLegendre
```

open MeasureTheory Shao.Probability，open scoped Matrix，noncomputable section。以下完整公开TYPE冻结；let内实际概率实例的hm0证明亦属精确声明，不得改成新caller概率或全局极小前提。

```lean
theorem source_canonical_rate_unique_minimizer
    (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k)) :
    let P : Measure ℝ := originalMeasure sourceEll w
    letI : IsProbabilityMeasure P := originalMeasure_isProbabilityMeasure sourceEll w hw
      (by simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one]
        using hm 0)
    let W : ℝ → ℝ × ℝ := fun x => (x, x ^ 2)
    let D : Set (ℝ × ℝ) :=
      {z | 0 < z.2 ∧ (Real.sqrt q / 4) * Real.sqrt z.2 ≤ z.1}
    bivariateMGFDomain P W = Set.univ ∧
      (∀ theta : bivariateMGFDomain P W,
        (0 < ∫ x : ℝ, Real.exp
          ((theta : ℝ × ℝ).1 * x + (theta : ℝ × ℝ).2 * x ^ 2) ∂P) ∧
        bivariateLogMGF P W theta =
          Real.log (∫ x : ℝ, Real.exp
            ((theta : ℝ × ℝ).1 * x + (theta : ℝ × ℝ).2 * x ^ 2) ∂P)) ∧
      ∃ theta0 : bivariateMGFDomain P W,
        (theta0 : ℝ × ℝ) = (8 * sourceEll, -sourceEll) ∧
        ((theta0 : ℝ × ℝ).1 * (q / 4) + (theta0 : ℝ × ℝ).2 * q -
          bivariateLogMGF P W theta0 = saddleRate sourceEll q w) ∧
        (q / 4, q) ∈ D ∧
        bivariateLegendreRate P W (q / 4, q) = (saddleRate sourceEll q w : EReal) ∧
        ∀ z ∈ D,
          bivariateLegendreRate P W (q / 4, q) ≤ bivariateLegendreRate P W z ∧
          (bivariateLegendreRate P W z = bivariateLegendreRate P W (q / 4, q) ↔
            z = (q / 4, q))
```

域/量词门：P仅为同一w的originalMeasure，不是atomic倾斜律；hm0真实给HasSum w1，产生概率和NeZero。W是真(X,X²)。整个真实Integrable指数域取all实参数，证明domK=univ只对本有界sourceP；域内log定义为真实正配分的log，明确输出正积分和literal值。theta0要带真实域成员，且明示实际有限theta=(8ell,-ell)达到候选测试值，不凭等式推可积。候选EReal率是对完整domK的真实上确界，与实saddleRate的有限coercion相等；不对top/bot做减法或toReal，不把所有其他矩点的率强行设有限。

尾域精确为c>0且a≥sqrt(q)/4*sqrt(c)，含弱尾边界，绝不增添c=0，也不删不可实现矩点、c<1或c>1+H等。必须证明候选在D，且对全部z∈D同时有全局比较与等号唯一性。不得只证局部严格凸、只比较候选参数或把全局极小结论作为caller前提。theta0存在在同P/W范围，不另选law。

实际生产路径供独立核实：PR146 source_saddle_exponential_value_bound 的all(s,t)项给真实Integrable/正积分/有限实测试≤同L，及同theta0精确达到；exists_source_tail_exponential_separator 在全部c>0弱尾域非候选点给真实可积有限严格测试。root v38公开 bivariateLegendreRate_unique_minimizer_of_tests 消费这些实际输入，不能用其一般定理名代替实例化。pair不等需真实得到a≠q/4或c≠q；q>0及sqrtq乘方给候选D成员。域内log与literalK的值绑定为后续PR151的ambient Fin2参数函数连接提供基础，当前不声称对子类型直接求导。

承重：消除原A同sourceP的规范域/有限候选率/完整正能量弱尾域全局唯一极小性这项实际缺口，直接消费于同一最终P/q/w的rootA组装；后接PR151真实梯度/full Hessian、PR148几何常数及U20b标准余项失败。矩阵标准化、均值逆邻域、统一far率间隙/概率界、一般KL9/10、原B/C/D后续仍另有义务；本节点不自动关闭任何原根，不声称beta最优。

接受基线v38：main63f82bd7ea2a0fba92a4ad217c4ad27bfa3ead00，accepted ffdedd610d0af501c3dd4672cf7f78d80eee543c，tree433377aee492752840f9396896bd00f668634442；receipt0e10017d614e4e519e64df72ee2cc09563eec174810395d3b3ea1fb159bc50de。公共实际源BivariateLegendre SHAd8bd5dc7099ffdbf52282ebb41ad03145a50b42547dec55bb42caacb31ed5f58，全源已读且root已独立声明/完整证明/整合kernel+axiom接受。

v2环境修正：精确2imports图仍为13Shao2776Mathlib/public2525内部+189external，canonical13 f158e2cad3e7a0dc5f0c7c31d85c111820fb38cb483188a4e9fe653e8ec2ecd2，13源与v38接受源一致。完整TYPE及imports两个Lean fence与v1逐字相同。v1 scope535657a9和191行CORRECT声明票cf2f5e05原字节保留；完整源99行4662B cbf43455e2d182fc0a342736d415190c4898878e622f6778c96a7b4e60c7cdae首次build01在import阶段失败，未进入proof体，日志242B SHA260cc7c835654100a3cb9b99dd704774a04f9d735d2f06db59e5a0809565dbd6。实际Lean4.36 Lean/Util/Path.lean69–76及findOLean138–149按模块顶层package选第一个root并缓存，所以原own先/root次并列路径对同Shao包不能逐模块fallback；原静态适用假设被实际执行纠正。

环境v2使用仅本run内的 import-view/Shao，首个LEAN_PATH条目指向import-view；其OQ3目录符号链接到lane现有build/Shao/OQ3（包括未来本target/Audit导入），Probability目录符号链接到已验收v38 build/Shao/Probability。其他需要的Shao顶层目录链接原lane同目录。这样同一个Shao root内完整解析13前置和新target，符号链接只读引用接受对象，不复制二进制、不写既有cache/root目录、不修改源/公开TYPE/数学前提/pins/证明设置。保留原Mathlib等路径。实际13对象沿view均须存在，未来target自身在首次成功后沿OQ3链接可见。此只读视图元数据构造/源码API读取不是Lean成功票。当前branch已在完整v1声明整份读后正常建自v38，当前source尚未成功；v2独立环境门及整份终票读完前不运行build02，不修proof来掩盖导入失败。

执行顺序：v1完整声明终票已全部读完后正常新分支的步骤已完成；v2不重新建branch或重置，当前ffdedd parent及153/152/151/148/146/144冻结heads保留。v2独立环境终票hash核实且整份读完后，才用只读view进行完整build02。无reset/merge/rebase/fetch/retarget/sourcecopy；本adapter没有叶PR依赖。所有Lean只在serverCPU14–17/native8192MiB/j4/autoImplicit=false，首次成功后不重跑。首次实际module-owner全常量TYPE/公理审计，再独立完整proof及最终整份lead读票后才接受/commit/精确PR。root独占shareddefs/cache/pins/integration，原A-D全部OPEN，外部CPU0–9/80GiB不动。
