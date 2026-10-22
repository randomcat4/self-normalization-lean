# U20e v2 冻结候选（显式ContDiff环境修订）：同源律的全参数光滑对数母函数与真实倾斜均值映射

状态：FROZEN_FOR_FOCUSED_INDEPENDENT_V2_STATEMENT_REVIEW。v1 scope76及202行CRITICAL GAPS原票原字节保留；其唯一环境缺口是header未显式启用ContDiff作用域，数学C∞路径已独立确认。本v2仅在冻结header增加ContDiff，精确4imports与唯一完整公开TYPE逐字不变。上一原根A完整326行CORRECT终票已全部lead读完并发布PR161/head293d3394546eaec284d39b86ed1f6449af7f70c8，等待root正式验收；本单元仍无Lean源/probe/Audit/新分支。

来源：current/oq3/proofs/r1/report.md137–159中有界原P及真实反倾斜、R2 report.md38–60的K/真实倾斜/m=梯度与均值逆邻域要求，以及root-contract.md定义域/真实均值图要求。R1 SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662；R2 SHA572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55。当前PR151/158只公开鞍点处的真实一阶/二阶，不能据此直接推邻域C2或均值逆；本节点实补同一有界sourceP的全参数C∞正则性，并绑定实际tilted概率下的均值。C∞指所有有限阶连续可微，不声称解析ω。

模块Shao.OQ3.SourceSmoothMeanMap，namespace Shao.OQ3，0公开定义/1公开完整定理。精确imports：

```lean
import Shao.OQ3.InverseTilt
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
```

open MeasureTheory，open scoped Matrix Topology BigOperators ContDiff，noncomputable section。显式ContDiff使∞为真正C∞的内层ENat top嵌入，不能用外层top的解析ω替换；完整公开TYPE与v1逐字相同如下：

```lean
theorem source_log_partition_and_tilted_mean_smooth
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) :
    let P : Measure ℝ := originalMeasure sourceEll w
    let Z : (Fin 2 → ℝ) → ℝ := fun theta =>
      ∫ x : ℝ, Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂P
    let K : (Fin 2 → ℝ) → ℝ := fun theta => Real.log (Z theta)
    let tilt : (Fin 2 → ℝ) → Measure ℝ := fun theta =>
      P.tilted (fun x => theta 0 * x + theta 1 * x ^ 2)
    let mean : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun theta =>
      ![∫ x : ℝ, x ∂tilt theta, ∫ x : ℝ, x ^ 2 ∂tilt theta]
    let pr : Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
    IsProbabilityMeasure P ∧
      (∀ theta : Fin 2 → ℝ,
        Integrable (fun x : ℝ => Real.exp (theta 0 * x + theta 1 * x ^ 2)) P ∧
        0 < Z theta ∧ IsProbabilityMeasure (tilt theta) ∧
        Integrable (fun x : ℝ => x) (tilt theta) ∧
        Integrable (fun x : ℝ => x ^ 2) (tilt theta)) ∧
      ContDiff ℝ ∞ K ∧ ContDiff ℝ ∞ mean ∧
      ∀ theta : Fin 2 → ℝ,
        HasFDerivAt K
          ((pr 0).smulRight (mean theta 0) + (pr 1).smulRight (mean theta 1)) theta
```

量词/真实对象门：只有同w的非负权和真HasSum w1，没有caller P概率/exp可积/正分割函数/光滑性前提。q及其他3约束在本正则性证明中并不需要；最终同q/w的消费者可由hm0取得hs，不另取law或另解约束。P是originalMeasure sourceEll w，不是atomicMeasure。Z在同P下对每个实Fin2参数都真可积且严格正，K才是其真实log；输出真实P及每个tilt概率，并给tilt下x/x²真Integrable。禁止借总化积分/不可积倾斜0来制造假均值或log0。

mean定义必须是实际P.tilted概率下的两个真实积分，不得把一个未绑定归一化矩代理命名mean。证明可以先建立N_k(theta)=∫x^k exp(theta·W)dP，真概率/有界支撑给所有k与theta的可积性；再在参数闭球×固定支撑紧集上给每阶真共同导数支配，产生HasFDerivAt N_k及实际momentSlope。已有PR151 private helpers可以作为来源对照，但不能跨模块调用生成private名字；本节点要在自己源里诚实重证所需私有辅助事实，不更改接受旧源。

光滑门：自然阶数归纳可用固定Mathlib contDiff_succ_iff_hasFDerivAt（自然n版），每阶导数函数由N_(k+1)与N_(k+2)乘固定连续线性投影并相加组成；先对所有k共同归纳每个有限阶，再contDiff_infty。每阶/每个参数邻域的支配常数可依赖k/中心，不声称全参数统一数值界。Z=N_0严格正后，ContDiff.log/除法合法；用真实integral_tilted及integral_div绑定归一化N_1/Z、N_2/Z与上述actual mean，才转移整个mean函数的光滑性。真实tilt绝对连续继承固定有界支撑并有概率，可产两个真Integrable门。不得只在鞍点识别函数值就转移全参数正则性。

梯度门：最后∀theta的HasFDerivAt针对实际literal K，连续线性梯度是h↦mean(theta)0*h0+mean(theta)1*h1；两坐标次序与W=(x,x²)和PR151/158一致。必须先完成全部moment/正配分及真实均值身份再用log链式法则，不能把m=∇K当作输入或仅输出形式偏导。此节点不要求mean的导数非退化，允许只具非负质量的退化law；正定性与实际源鞍点窗口由另一个全正权消费者提供。

承重/直接消费者：补齐同源律均值映射邻域逆及标准化稳定性路线的全参数光滑生产者；原A已完成独立proof/PR161但仍待root正式验收，此光滑节点不是A的新增前提。下一步再在同最终w/full4hm与全正权下，结合PR158实际Hessian/严格正定，证明均值导数等价及真正局部逆。根B无界一般律不会由此自动覆盖，本节点严格只针对有界sourceP；标准化谱界、统一WC频率变换、远区概率、Edgeworth/格胞与原C/D仍分别待证。当前不输出均值逆、正定性、率间隙/概率界、全局最小或任何原根闭合，原A/B/C/D全部OPEN，不声称β最优。

环境门：精确4imports候选图已一次完成，5Shao/2501Mathlib物理，公开5Shao/2458Mathlib+189external，source/olean缺失0；5项目源与已接受v38 source checkpoint绑定且沿用到当前v39；common5源未变，canonical5=5d1b1c34f11a05f81e8636f3809e739b4942d03d2d5f7f82dabbb7fff8e28307。candidate-cache.json2168B SHA5da34cadad30873e42e6d0cb038c5e3036582d04d1a3986cf9d3b6f578808d83。不需缺失的ContDiff.FiniteDimension或InverseFunctionTheorem.ContDiff模块；后者只在未来实际逆单元需要时另做门。沿原单own-Shao-root Lake路径，未使用U20c的额外view，也无新共享模块或二进制复制/cache写。候选图已过不重复，独立审查应核实际数学/API与必要元数据，不凭candidate说明自认证。

执行顺序：整份独立v2 CORRECT声明终票hash核并全部lead读完，才从已接受v39 checkpoint59a531b89eff7c11e4fc53583067f2cd3b53a517正常新建owned feat/oq3-source-smooth-mean-map（本单元无153/156/158/159叶依赖），不merge/reset/rebase/fetch/retarget/copy源。完整源唯一heavy targeted Lean在serverCPU14–17/native8192MiB/j4/autoImplicit=false，首次完整成功后不重复；首实际module-owner全常量TYPE/公理Audit；再独立完整proof终票hash核并整份lead读完后才接受/commit/精确PR。禁止sorry/admit/newaxiom/unsafe/native_decide/implemented_by/设置弱化，标准公理propext/Classical.choice/Quot.sound。root独占commondefs/cache/pins/rootimports/integration；旧10冻结heads（含161）保留，外部CPU0–9/80GiB不动。不新agent/chat/goal，复用sole reviewer lease1。
