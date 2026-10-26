# unit195 repair-01：同一独立审阅者的受影响 SOURCE 续审

STATUS: CORRECT

JUSTIFICATION: 对精确修复源 `3f3d699297f33685dad57eed265727d538dac2ff5812966dc97093f6b0f5f169` 独立重建了冻结的两处逐字替换，完整重读 D03、D05 的新声明及证明，并读取新增 `Real.rpow_eq_pow` 的完整 raw 声明、八项时序 scope 和一项既有 Pow instance。两处旧实现缺口均已在源级数学推导中正确修复；没有改变假设、声明、数据、模型量词或源范围。结合精确保全的原完整 SOURCE 审阅，本版完整源文/陈述/证明审阅为 CORRECT。此结论不推断 Lean 实际通过：`qualified=false`、`actualOwned=UNKNOWN`，本阶段没有接收成功 native02 或同原对象的全所属声明证据。

本角色仍为 `/root/oq56_polylog195_final_review`，独立于同作者 `/root/oq56_polylog195_stage1`。使用 math-theorem，禁 math-ultra。旧 SOURCE 审阅与 SOURCE-RELEASE0 保持封存；本阶段仅写本 repair-01 目录，没有修改作者、新旧源码、旧审阅文件或其他 owner 的字节。请求模型 gpt-6.1-sol/xhigh；实际模型/强度内省 UNKNOWN，输入/缓存输入/输出/推理子集计数为 null。实际 RUNTIME-ACK 先于审阅写入。

## 精确输入及最小差异

新源码为 `drafts/oq56/unit195/author-01/stage2/repair-01/BoundedPolylogConcentration.lean`：11447 字节、205 LF、UTF-8/BOM0、无 CR。作者 manifest SHA256 `489b0113e560254140fe59998fe7c8407b01a54cdcfdf131048d6c444ce4af86`，RELEASE0 SHA256 `ea2460485eb722dad3469a0af587f63e20d31cce67dd9863a0c7f1d08909a350`，writer/execution/heavy/inflight/pendingExternal/children 全零。

父在修复前冻结的 delta 为 `parent-freeze-delta01-two-prop-repairs.json`，SHA256 `ee7cce13d08737f4a4a606bb3d593583139d48ea24b64edfe21b4535deb1016e`。其 base freeze 仍为 `374eb47684b73f8125339925ec2cfdebc4c044c1b044c380e89cc375514088ae`；base source 仍为 `95eea1690b4d10a2794eff9595b3c4f7a85c473a715aee961249a8770e1548f7`。

独立从 base source 字节出发，只执行 delta 两个 exact old→new 替换，每个 old 恰出现一次，重建结果与新源逐字节完全相同。它们是第 83 行 `by linarith only [hInner]` 与第 186 行简化列表增加 `Real.rpow_eq_pow`。所有其他字节由此严格保全，未把作者的“两个改动”描述当作独立证据。

再次核对五个声明头、唯一 D01 RHS、12 项时序环境与闭合；36 个直接表达式的完整类型/初值/捕获/λ 范围；23 个 Prop 的名称、顺序、完整预期类型、显式类型注记、捕获及 scope，全部与原映射和冻结相等。新映射 78 个完整源码区间均按新源重新定位，原文、字节长度、行号和 SHA256 一致。这里是受影响字节与接口核对，未重新执行旧 producer 检查或重审旧 producer 证明。

## D03：完整新证明与第 83 行修复

已逐字重读新源第 35–94 行，含完整模型/资格参数、返回事件与完整证明。完整 proof body 为 53–94 行，SHA256 `40875fd2a8eaae2b482d095ff3021cc09e08cab98d9b6148d7056ee91e9c3c33`。

所有原 193 资格和显式实参次序保持：n、同一概率法则 ν、r、w、R、M、q、非负性、产品可测与可积、双向 a.e. 典范、a.e. 非负及高度、平方可积与 M 界、a.e. 乘积包络、q≥2、逐点对称和窗口。`h193.2.2.2.2` 仍准确取得实际三个严格失败概率之和 ≤3 exp(-q)。已合格真实接口及其完整类型的审阅从原 SOURCE 证据复用，未重复读旧证明。

用说明记号 A=μ.real(E_Q∪E_F)、B=μ.real(E_Q)、C=μ.real(E_F)、D=μ.real(E_L)，`hInner` 为 A≤B+C，`hOuter` 为 μ.real((E_Q∪E_F)∪E_L)≤A+D。第 83 行新目标是 A+D≤(B+C)+D。其否定经实数线性算术化为 A>B+C，与 hInner 矛盾；所以 `linarith only [hInner]` 只需这一条不等式，不需要 D 非负、可测性、有限性或任何新前提。该证明不再依赖旧 `add_le_add_right` term 的加法位置，也没有产生新数据值。

新 hLifted 与 hOuter 中间项准确一致，`hOuter.trans hLifted` 给三项和界，再 `hUnionSum.trans hSum` 得 ≤3 exp(-q)。目标事件按唯一透明 D01 定义是同一个左括号并集。第 83 行旧类型不匹配由此在完整数学证明中消除，其后所有传递步骤仍匹配。有限窗口、严格事件和 n=0/1 的语义不变。

## D05：完整新证明与第 186 行修复

已逐字重读新源第 149–202 行，含外层固定实参数、全部 eventual 内模型量词与完整证明。完整 proof body 为 169–202 行，SHA256 `788fdaec026710b485ca841c2b319331bddf26de0a56e8ee225a73bb157394fe`。

首先按原参数次序调用 194 的 `eventually_boundedLogCutoff_window`。Eventually.mono 回调先取 n/hp，从 1<n 获 1<(n:ℝ)，继而 `log_nonneg` 得 log(n)≥0；用 A>0、tau>0 的弱化及乘除非负性得 hBase0。令 x=A log(n)/tau、y=1/alpha，原 `rpow_nonneg hBase0 y` 的结论是 0≤x^y，真实 cutoff 透明展开的目标是 0≤Real.rpow x y。

新增简化列表 `[boundedLogCutoffHeight, Real.rpow_eq_pow]` 先展开同一个 cutoff 初值，再以无条件等式 Real.rpow x y=x^y 重写目标，使其与 hBase0/y 的 rpow_nonneg 结论一致。只改变普通 Prop 证明的表示转换，没有改变底数、实指数、参数正性或 cutoff 定义。原第 186 行缺少的正是此记号转换，本修复在数学上准确补齐。

随后 hp.2.1 给 q_n≥2，hp.2.2 给 2R_n²q_n≤n。直到这些数值条件获得以后才引入任意 Ω/mΩ/ν/hν/r/w 及全部资格，调用已修复的 D03。每个实参位置和类型均保持原样，所得失败集及上界恰为目标。统一 eventual 起点仍先于所有模型量词，允许模型随 n 变化；M 固定且 CT 只依赖 M。没有选择 N 或模型族，也没有把 cutoff 资格、典范化或统一 M 改为隐含结论。

## 新 raw 记号桥的完整 scope 与保全

新增主要原始声明唯一为同固定 Mathlib `Analysis/SpecialFunctions/Pow/Real.lean` 第 39–40 行：

`@[simp] theorem rpow_eq_pow (x y : ℝ) : rpow x y = x ^ y := rfl`。

完整类型是 `(x y:ℝ) → Real.rpow x y = x^y`，显式参数顺序 x、y；无正性、非零或其他前提。声明使用已有第 37 行的 `noncomputable instance : Pow ℝ ℝ := ⟨rpow⟩`，它是记号本身的 rfl 等值，并非新定义、实例或统计假设。

完整 scope 已按原文读取并切片核对：第 7 行 module；第 9 行 public meta import；第 10 行 public import；第 17 行 expose/public section；第 20 行 noncomputable section；第 22 行 open Real Finset Set；第 27 行 namespace Real；第 28 行 variable {x y z:ℝ}。另有第 37 行既有 Pow 实例。两行 raw、八项 scope、一项 instance 均与固定 fullFile 逐字相等。完整 fullFile SHA256 `f8a26d662fb7966fa5b45aef95c8d7cf0383c9921fa3e9ee1cd2c41561e9fbfd`、50402 字节与原记录匹配；packet SHA256 `fa40811a001b5ed199b4338031681de84d9cb3862a1f2b7126427c7c241cf4db`。有效主要 raw 总数为 3+1=4；旧 29 项 scope/instance 证据保留，新增重叠的原文 scope 不是新增环境实例。

原作者 Stage2 的 10 个 payload 和 manifest/DONE/RELEASE0 三个封存文件全部逐 hash/bytes/LF 保全；原独立 SOURCE 的八个 payload 和 manifest/DONE/SOURCE-RELEASE0 三个封存文件也全部保全。旧完整报告 SHA256 `cf0c70c37e04e643b329d01b02bd1bc89b0b0de4219fe4b84552e17f6ffe316d`，旧释放 SHA256 `3d517c377133258f92610662c73f157582d5024ae684ef9ddd16eb8b8ee1aca3`。旧报告对 95ee 源的 CRITICAL_GAPS 结论不被覆盖；本报告对 3f3d 修复源闭合那两个缺口。

D02 完整 proof bytes 保持 SHA256 `ba6158a18318f666c6754a743abc18af227d1cb3957122c5dbe43e5f3c220997`，D04 保持 `96554a79e4875cf2ba3b19bd85deff992ee662af767c60060831174786e7dbbe`；本轮没有重复完整审读这些未变证明。首次 native01 的 RC1/2 errors/13 warnings/no object 及诊断绑定保持归档，不当作修复版成功证据，也不重放调用。

## 合并审阅范围与正式资格边界

原 SOURCE 完整审阅加本受影响续审覆盖当前精确修复源：原统计量、五个声明、全部四个完整证明、所有冻结数据/Prop/作用域和四个有效主要 raw 库材料。阈值等号原子、重复观测、只排索引对角、a.e. 与逐点资格、C=0/a=0/M=0、小 n 和统一模型窗口语义没有变化；不添加 measurable w、topology Ω、zeroDiag、nonatomic、独立性或高阶矩。

范围仍为 p51 S16 联合失败概率衔接。S17 的真实 Studentizer 几何、S15 付款、p54 严格 1/8 修复与 p 矩仅统一有界的修正、SZ6.1 归属继续保留；124 非前置。原 C1 immutablev85 完成，C2/C12/OQ56 OPEN，OQ3 仍用户暂停。

本轮纯本地，Lean/AX/server/network/Git/API/uploads/cache/children 全部为 0。正式合格必须等待修复源 native 成功及同一次首次成功原对象的完整 module-index 所有权/所有 TYPE/全部非定理 FULLVALUE/body/levels/components/递归 AX 白名单和精确 source/object/receipt provenance。当前 SOURCE 数学审阅 CORRECT，qualified=false，actualOwned=UNKNOWN。下一依赖为同审阅者在新父授权下接收并审阅完整机器包；本阶段随附 RELEASE0 全零释放，不留不明在途请求。
