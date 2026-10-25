# 单元184 repair-01独立受影响源码续审

STATUS: CORRECT

阶段：SOURCE_REVIEW_COMPLETE_MACHINE_PENDING。对象为 `d0fad94a739902f5e9ac36f4c81df0485571e797914b51d7d7e17d2d233503ab`，19278字节、384个LF、UTF-8无BOM、CR0。审阅者沿用 `/root/oq56_ghost184_final_review01` 独立上下文，不是修复作者；作者RELEASE0 SHA `19225589cf4fc297d8b6a4bc2e3a4b90a6c93e06c1c0de4133158dbd4da1f315` 实际五项为0。全部新工件仅在本目录；旧source-only报告、manifest及RELEASE字节保留。

## 旧失败与原静态判断的更正

完整读取首次native受影响诊断，旧源a58b…的自然退出码为1、6.425527822226286秒、三个T01错误、没有输出对象、没有超时、进程组结束、5102条保护记录保持；原receipt `0ebca88f0f3850e3ebe609574925d9b678dd4245648bff44ce88f4a8d002a804` 原样保留。没有把旧静态CORRECT当作内核通过。

原source-only报告将最终 `intro q hq` 的期望类型直接写为q:ℝ，这项关于旧实际控制作用域的静态判断错误。旧目标前面仍有νn/Yn/S的let；另行建立同值的证明局部let并不会消耗目标中的let。实际native诊断明确给q的类型为 `Fin n → Measure (Ω × Ω)`。因此旧报告的这部分只能说明预定的数学意图，不能充作旧源码已获得真实q:ℝ的证据。新稿的明确change及其后真实预期控制范围在本续审重新核对，最终实际展开仍以新服务器证据为准。

另两个旧失败也是实际Lean证明表达缺陷：未展开Cmom时等式搬运不匹配；非负比较的匿名项缺少确定实数表达式，产生未确定元变量。原自然数学比较成立不等于那些旧tactic表达式通过；三项失败均保留，不降低为警告。

## 精确差异和复用

已完整读新repair-reasons、T01-full-source.delta、primary-api-conditions、source-declaration-manifest、formatcomparison、inputbindings、frozen-scope-read、affected-types-values-ordered-scopes及embedded-and-control-coverage。完整读新源码104–379的T01头与全部证明。独立脚本从实际源重新计算差异，仅三块；三个完整声明头、prefix/suffix与冻结相同，29公开let的完整类型和值不变。

P01/P02整个proofBody与原稿逐字相同，proofBody SHA分别为 `3f8f8103019d7a589b4254f11ebbbf65e796dda53269e4d6b0c429c767e5742c`、`f9a59dcfb44be2ccb86a818b39b5e3d645a37e10ff4b38d2d6d6ed28f422691f`。因此复用原独立完整P01/P02审阅，未为这两helper重复委托或重跑检查。182/183精确qualified的源/公共TYPE/defs和旧审阅、内核、AX证据按原hash绑定复用，旧证明未重审、旧check未重跑。

对新稿143份源级记录逐项核其完整type/value/kind/rawBinder、有序scopeIDs与此前独立补全版相等；每份sourceRaw重新定位并与实际新源码行范围精确相等；以完整唯一绑定字典与有序ID重构每份rawscope，其SHA全部匹配。这是实际独立核对结果，未采用作者描述数代替检查。h182Threshold/hN0Spec的完整类型包含内部C/d/ν及全部lam残差链，与新源206–230、275–299的最后have赋值符号前完整文本精确一致；320行真实letI得到保留。原受这三项补全影响的62份后续作用域继续有效。

所有嵌入围合表达式逐项与新源对应记录完整类型/值/sourceRaw核对；既有threshold/uniform模板与原独立全文相同，原嵌入控制范围复用。本次四个proofControls另行核了完整期望类型、RHS、外层有序scope、匿名Prop和新增change中的量词/积分变量。143仅是命名源记录数，不是全部actual binder或所属常量数；实际module-index owner、展开TYPE/FULLVALUE、recursiveAX数量仍UNKNOWN。

## 三处修复的完整证明与控制范围

272–273行：已有 `hC0Spec.1 : 0 < C0` 和 `hC0Spec.2.1 : C0 = sumMomentScale β tauPair Mpair`；Cmom的冻结值正是右端。`simpa only [Cmom, hC0Spec.2.1] using hC0Spec.1` 同时把目标Cmom展开、把已有事实的C0重写成同一值。完整目标为0<Cmom，完全由既有事实支付；没有变更常数或添加假设。hCmom不在其自身RHS的上下文中。

336–340行：当前实际边缘指数积分记作I仅为本报告说明，未新增Lean数据。已有I≥0、I≤2Mexp、Mexp≥1。匿名证明现在明确标注完整目标 `0 ≤ 2 * Mexp`，由hMexp线性推出。sub_nonneg.mpr hFstdBound给2Mexp−I≥0；add_nonneg给I+2Mexp≥0；mul_nonneg的积非负即(2Mexp)²−I²≥0。nlinarith因此可以关闭展开Mpair后的完整目标。被积函数、真实ν、已先建立的L¹和Mpair均未改变，不存在自由平方比较假设。

347–370行：intro n后，证明局部νn(i)=pairLaw、Yn(i)=Y、S=coordinateSum Yn与公开头中同名三个let的全值相同。363–366的完整change目标是

```text
∀ q : ℝ, 1 ≤ q →
  Integrable (fun x => Real.rpow (S x) q) (Measure.pi νn) ∧
  Real.rpow (∫ x, Real.rpow (S x) q ∂(Measure.pi νn)) (1 / q) ≤
    Cmom * ((n : ℝ) + Real.rpow q (1 / β))
```

该目标只规约原目标的三个let，未引入新的data定义。change前的完整外层scope以hYnExpBound结束，包含原μ/h/w等输入、g/r和全部固定尺度、原producer事实、同一R条件律、真实鬼样本输入、n/νn/Yn/S及五项坐标事实；没有q或hq。change表达式内q:ℝ只作用于其后续命题，两处x分别是独立的 `Fin n → Ω × Ω` 局部绑定，仅作用于各自Integrable或积分被积函数，外层scope为上述base加change内q。

367行intro的直接目标现在真正以∀q:ℝ及1≤q开头；新预期引入顺序是q:ℝ，然后hq:1≤q。它不再有前导let供intro先行消费。独立检查把这个完整scope与新源q/hq记录逐项比较，并明确与旧native中measurefamily类型区分。368–370按T03的原完整参数序列传Ω×Ω、n、νn、五项坐标事实、q/hq；simpa只展开Cmom/S、重写C0相等式及rpow记号。371后的lam分支scope不含n、νn、Yn、S、q、hq，七个实际残差let保持原定义。

## 完整T01语义与未支付范围

其余T01依赖和构造完整重读后无变化：182同一原输入支付真实条件ν和固定wstd的可测/L²/边缘指数L¹、积分≤2Mexp及同lam的真实Kstd包络；α∈(0,2]给β∈(0,1]；tauPair=tauStd/2^α>0、Mpair=(2Mexp)²≥1，Cmom精确为sumMomentScale且先于全部R/lam/n/q。原截断仍为C={w≤R}，实际pairLaw=ν.prodν，Y=(wstd₁+wstd₂)²。

P02在真实ν下先证D与E的L¹，再积分比较；公开T01以真实边缘积分的非负平方比较支付配对矩上界。全n含0、全实q≥1含1、α=2/β=1端点保留；没有新增Nonempty、标准Borel、无原子、n≥1、独立g/w、额外矩或因子分解合同。真实H、κ、G、σ2、σ、K、Kstd及其两个AE包络按原182接口保留。

本单元仍只支付p44 §3的实际条件鬼样本平方指数输入到§2非负和全q矩的适配；没有Hilbert对称化、Khintchine/二阶混沌、实际F/行能量尾、DC、source upper/compact概率引擎或原根闭合。p54否定的p矩任意多项式变化率未被使用，p54实际坏事件/原子/零分母修复义务未据此支付。mathlib、182、183与Shao–Zhou外部归属保留。C2/C12/OQ56仍OPEN，OQ3仍PAUSED_BY_USER，无新颖性声明。

静态未见sorry/admit/新增axiom/unsafe/native_decide。本续审当前未运行Lean/服务器/网络/Git/上传/缓存/子代理；需父级新源native和同对象的module-index全owner、完整TYPE、全部非thm FULLVALUE及逐名递归AX白名单回执，再在同一独立上下文完成最终qualification。当前不能给出实际owner数量或本模块机械通过结论。
