STATUS: CORRECT

JUSTIFICATION: EE216 最终精确源码的三个冻结公共声明均被完整证明。对象是真实概率测度 mu、真实实值函数 X、真实指数可积集的内点及真实加权矩；没有用自由系数相容性、待证累积量身份或新公理代替解析步骤。三阶与四阶公式来自真实积分的求导、开邻域函数等式及商/乘积/幂求导；中心化结论正确使用概率质量一和显式 hmean。当前判断仅覆盖本单元冻结的标量解析桥，不表示其前提已对原始标准化投影律完成实例化，不表示原 OQ3 B/D 或根结论闭合。

审查者：新鲜、独立、非作者上下文 /root/oq3_ee216_final_review；本次派发明确指定 gpt-6.1-sol / xhigh。使用 math-theorem；未使用 math-ultra，未派生子上下文。审查日期为 2026-10-27，证据只读核验完成于 14:30 UTC 附近。仅写本报告；没有编辑源、冻结声明、收据或其他文件，没有运行 Lean/AX、重新编译或上传服务器文件，没有向其他聊天发送工具消息。

## 1. 精确字节与证据绑定

以下本地输入均完整读取；哈希由审查者实际计算，与服务器 runs/oq3/u22ee-20261027 中相应字节再次只读核对一致。

| 输入 | 字节数 | SHA256 |
| --- | ---: | --- |
| u22ee-source.lean | 4523，88 LF，0 CR | e45f0061beaa274734b17fe61f484f9cfc2199d0ec33d884b59b9c77c2644b8a |
| u22ee-frozen-declaration.lean.txt | 1399 | 4447ef1dd7b5f4e36f6ac1b510353fc1d772b906db62ba4835ef620504e24f9c |
| two-hundred-sixteenth-unit-scope.md | 1627 | a15c0b99f536a532b8a4ff7e38bbd3f9ab711c11c03e914c5d0c49fa72d687ec |
| u22ee-actual-types.txt | 1640，26 LF | 364225218818d9d17e67cb99387ef11e10a417ca188c432e46d18f5116f1f8fe |
| u22ee-receipt.json | 7774 | b8abefd3afb4b2502ed6843cd1d37692fc0572c7bf2cd3665cf66a2969020045 |
| u22ee-Audit.lean | 2098 | 59d528cb4359198207ed517288080c2a377fbf17a4ad3e1d0a3d63d73a1f82cf |
| u22ee-audit-record.json | 3122 | 9212875c946d56e4f55689374e1fd725a489312316eceef25e87c422a4bc37d1 |
| u22ee-build-history.json | 4310 | afadd16f36289c539528b1a9b2dc90b0b9f4a47084dc415b1456ea6ffe7ec235 |
| u22ee-primary-API-binding.json | 3219 | 503d28ab302a15e59d8d8ec8cf28241d4be259a9318225e486b482523764a4ea |

服务器生产路径为 /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3/Shao/OQ3/ScalarCGFThirdFourthDerivatives.lean；审查者只读复核为相同 4523 B / 88 LF / 0 CR / e45f0061… 源。其现存 .lake/build/lib/lean/Shao/OQ3/ScalarCGFThirdFourthDerivatives.olean 为首次成功原对象：441152 B，SHA256 97621896a1fb97829675965fdbdba8176ddfd30a00237d98faa326a85965bab1，与原生 native02 成功收据及同对象 AX 收据一致。

沿用既有原生证据：native02 RC0，5.190987607464194 秒；其 build-02.log 为 965 B / c1c32d0bc5c17f6f05710dab2cad8fd8b3c3febd1f54e64ee7b36d04f43911ac。同首次原对象审计 RC0，5.795895375311375 秒；audit.log 为 1892 B / 7c5da96fee13a3ade0087ee62149e2255d2ac9cff6ce7058114f3691242e24e1。审查者读取了完整两份编译日志和完整 audit.log，并核对服务器实际源/对象；本报告没有制造新的核验执行。

钉死工具链为 leanprover/lean4:v4.36.0-rc1；当前工作树的 mathlib 链接实际解析到 cache-overlays/shared-v34/packages/mathlib，实际 Git HEAD 为 807d3836b165983210ee2ecf3cd28f239436949c。日志保留 mathlib 工作树含本地改动提示与四条无害 tactic linter 警告；本单元消费的原生 API 源/对象另按下面精确哈希绑定，未因警告修订源码或重放编译。

## 2. 自然来源到冻结陈述

仅为本次承重语义读取了只读 C:/game/shao/current/oq3/proofs/r2/report.md 第 1、2 节：W=(X,X²)，K(theta)=log E exp(theta·W)，真实倾斜律 dP_theta=exp(theta·W-K(theta))dP，以及 Y_theta=Delta(theta)^(-1/2)(W-m(theta))。整份来源文件 SHA256 为 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55；从“## 1. 精确陈述”至“## 3. 对曲边界”之前的第 1、2 节原文本按 UTF-8 编码 SHA256 为 da158d1e1c1adbe22bdf71ce3d8ace0b66a448e2b866b73b731c38b21bf4485d。未读取或重审已合格 EB/EC/DJ 等旧证明。

该来源定义要求累积量最终来自同一真实倾斜/标准化律的对数矩母函数。本单元提供其中独立的实标量恒等式：给任意 Ω、MeasurableSpace Ω、真实概率测度 mu、真实 X:Ω→ℝ，以及 v 属于真实 integrableExpSet X mu 的内部，令 M_k(v)=∫X^k exp(vX)dmu，求实际 cgf X mu 的三、四阶 iteratedDeriv。量词覆盖任意这些输入；没有额外的有界性、方差一、自由矩序列或系数相容性假设。

该一般标量结果本身与来源一致，但不是来源二维 Y_theta 或其投影的已完成应用。中心化定理明确保留 h0:0∈interior(integrableExpSet X mu) 和 hmean:∫X dmu=0；这两项没有被本报告认作 canonical standardized law 的既得事实。后续消费者必须在 SAME law 上由合格 open-domain tilt/标准化接口给出这些前提，不能仅凭“standardized”一词省略 h0，也不能切换 E/rho 或概率律。

冻结文件中三个完整公共头（源 8–14、39–46、75–82 行）均逐项审查。另以只读文本提取从 theorem 到“:= by”之前的完整三个头，与冻结文本去除文件首尾空白后逐字比较，结果为 exact=true；两份声明内的 M 值也包含在该比较中。实际 26 LF TYPE 输出的三个声明均逐字完整读取，未用摘要或截断输出替代。实际 TYPE 的“have M := fun k => …”是对应固定 let 值的打印形式，不是可自由选择 M 的前提；源中的“intro M”只是打开该 let。

## 3. 全部真实原生 API 与定义值

完整审查 primary-API-binding 的全部七项，并只读核对实际钉死 mathlib 中对应原文和实际依赖 .olean 哈希：

| 所属原生源 | 源 SHA256 | 原生对象 SHA256 |
| --- | --- | --- |
| Mathlib/Probability/Moments/Basic.lean | 73264d34c22038347bc73821a45442346ce12756475359325ebb9340a89af8fa | 3614e47849b1ba8ad14ae453d28cd25b14a3afa1e229211714cfaf49d02eff2b |
| Mathlib/Probability/Moments/IntegrableExpMul.lean | 9ddfb99776091f424dc7e1a86b6a456180e8186cae9ca1084541eff41aa9e3a8 | 4730cf8979e86ab3145fcfe3573a5b7a8963f2f54c0a1551408fe64ddbd3ed47 |
| Mathlib/Probability/Moments/MGFAnalytic.lean | 4cd9ee9d7724459443aef04ad083267bc1e11da13a98b28b6cf59bee9dbb94c2 | 55b4c2304c45d3789ae22b8591282300aced1d1074f229c61bc7ba0716a2f6d1 |

1. Basic:122 的 mgf 定义值是 mu[fun w => exp(t*X w)]，即真实积分；Basic:126 的 cgf 定义值是 log(mgf X mu t)，不是待指定累积量或形式级数。两项定义值完整审查。
2. IntegrableExpMul:112 的 integrableExpSet 定义值是 {t | Integrable (fun w => exp(t*X w)) mu}。故 interior_subset hv 确实提供用于 mgf_pos 的真实指数可积性。
3. Basic:202 的 mgf_pos 在 [IsProbabilityMeasure mu] 和上述 Integrable 前提下给出 0<mgf X mu t；本单元两处 hpos 都精确满足条件。
4. MGFAnalytic:43 的 hasDerivAt_integral_pow_mul_exp_real 对任意自然数 n、任意内点 t 给出真实积分函数 t↦∫X^n exp(tX)dmu 的 HasDerivAt，导数值为 ∫X^(n+1) exp(tX)dmu。源码变量上下文没有被遗漏的额外 X 可测性或矩身份前提；已实际读取其完整签名与上下文。指数可积集内部正是库中保证这些真实加权矩可积并可求导的条件。这里没有用 Lean 非可积积分的默认零值冒充真实矩，也没有自行交换未获条件的极限和积分。
5. MGFAnalytic:189 的 deriv_cgf 在同一内点条件下给出 (∫X exp(vX)dmu)/mgf X mu v；:204 的 iteratedDeriv_two_cgf 给出 (∫X² exp(vX)dmu)/mgf X mu v-(deriv(cgf X mu)v)²。签名、分母、参数顺序和全部条件均与源中的调用吻合。

另只读核对 Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean 的真实定义与递推，源 SHA256 95e6b06e0b5094f2404bef7f871317a22065cf3f4eea2775011be4fff7bdd491，对象 SHA256 ed273c6fda15116b704c068ca06088eb955cefbdbf13f1be29e0ebd678e03503。第 55 行 iteratedDeriv n f x 是 iteratedFDeriv 的 n 线性映射在全 1 方向的取值；第 306 行 iteratedDeriv_succ 为 iteratedDeriv(n+1)f=deriv(iteratedDeriv n f)，第 312 行等于 deriv^[n] f。因此目标确是通常未除以 n! 的 n 阶实导数，没有 factorial、方向或次数错配。

## 4. 全部证明与 M/F 值逐项核验

两处声明 M（源 12、43 行）分别完整核验为 ℕ→ℝ、k↦∫(X w)^k exp(v*X w)dmu；两处证明 F（源 16、48 行）分别完整核验为 ℕ→ℝ→ℝ、(k,t)↦∫(X w)^k exp(t*X w)dmu。F k v 与对应 M k 为同一字面积分的定义展开，且所有 k,t 均用同一 X/mu。两个 M、两个 F 的完整值都已覆盖；不存在未审查的抽象矩或局部自由系数。

为说明代数，以下 a=F 0 v、b=F 1 v、c=F 2 v、d=F 3 v、e=F 4 v 仅是审查记号。

### 4.1 cgf_third_derivative_actual_moments（源 8–37 行）

- 源 17–20 行 hF 对所有 k 与所有指数可积内点 t 调用真实积分导数 API，故 (F k)'(t)=F(k+1)t；没有把 M 当独立可微系数。
- 源 21–23 行 hpos 将 F 0 v 的 X^0 和 1 乘法展开为 mgf X mu v，使用概率性与 interior_subset hv 得到 a>0，进而 a≠0。所有商分母 a、a²、a³都受覆盖。
- 源 24–29 行利用 I=interior(integrableExpSet X mu) 为开集且 v∈I，得到邻域内所有 t 都在 I；对每个这样的 t 用真实二阶 cgf 公式和真实一阶公式建立 iteratedDeriv 2 cgf = F2/F0-(F1/F0)² 的 EventuallyEq。这里是邻域等式，不是仅 v 处等式。
- 源 30–32 行 hD 是同一个函数表达式的 HasDerivAt，分别使用商法则、幂法则与减法；iteratedDeriv_succ、hlocal.deriv_eq、hD.deriv 因此合法把三阶目标改写为该商式的实际导数值。
- 代数值为 d/a-cb/a²-2(b/a)(c/a-b²/a²)，合并后是 d/a-3cb/a²+2b³/a³。故系数 −3、+2 和分母幂 1、2、3 全部正确。源 33–37 行只是同积分值改写、自然数/函数点值化简和在 a≠0 下清分母后 ring，没有附加假设。

### 4.2 cgf_fourth_derivative_actual_moments（源 39–73 行）

- 源 49–55 行 hF、hpos 完整重复了同一真实积分导数及 mgf 严格正性论证，仍是相同 X/mu；没有跨概率律替换。
- 源 56–61 行在同一开邻域逐 t 调用前一已证三阶公式，建立 iteratedDeriv 3 cgf 与完整三阶商式的 EventuallyEq。函数 RHS 使用点态除/幂/乘以及显式 const_mul 函数的组合，正好与源 62–66 行 hD 所证明的可微函数一致；Pi.*_apply 化简仅作点值形式转换。
- 源 62–67 行 hD 对 F3/F0、−3F2F1/F0²、+2F1³/F0³ 分别运用商/乘积/常数乘/幂法则，并用 a≠0 推出 a²、a³非零。邻域等式再求一次导数得到实际四阶导数，未把单点数值恒等式非法求导。
- 三项导数分别为 e/a-db/a²，−3(db+c²)/a²+6cb²/a³，6b²c/a³−6b⁴/a⁴。相加是 e/a−4db/a²−3c²/a²+12cb²/a³−6b⁴/a⁴。系数 −4、−3、+12、−6、各负号及分母幂 1、2、2、3、4 全部逐项吻合。源 68–73 行 field_simp/ring 仅核验此代数恒等式。

### 4.3 centered_cgf_third_fourth_derivatives（源 75–85 行）

源 83–85 行分别将两个一般公式在 v=0、hv=h0 处实例化。此时 exp(0*X)=1；概率性给出 M0=∫1 dmu=1，hmean 给出 M1=∫X dmu=0，其余 Mk=∫X^k dmu。因此第三阶只剩 ∫X³，第四阶只剩 ∫X⁴−3(∫X²)²。这一推导不要求再假设方差一；显式 h0 保留为真实指数域内部条件。两个 simpa [hmean] 正好完成以上化简，没有遗漏概率归一化或把未中心化四阶矩直接误当四阶累积量。

依赖图为原生真实积分/一二阶 API → 本单元三阶 → 本单元四阶 → 中心化合取；导入只有 Mathlib.Probability.Moments.MGFAnalytic。不存在循环、自证、自由系数相容性前提、额外隐藏解析假设或声明降格。

## 5. 所有实际 TYPE、VALUE 与递归公理覆盖

audit.lean 完整读取。它按 env.getModuleIdxFor? 的真实模块归属遍历整个环境而不是按 Shao.OQ3 名称前缀筛选；对每个实际 owner 拒绝 isAxiom，调用 Lean.collectAxioms 递归检查，并打印完整 TYPE；所有 .defnInfo 会打印 VALUE。目标数组同时强制三个冻结目标存在且属于 theorem；没有把生成/私有 owner 排除在审计外。

实际 audit.log 与本地 actual-types 的全部三个声明均完整读完：

| 实际声明 | KIND | 已审 TYPE 内容 | recursive AX |
| --- | --- | --- | --- |
| Shao.OQ3.cgf_third_derivative_actual_moments | theorem | 任意 Ω/可测空间、mu/概率实例、X、内点 v；完整 M let；完整三阶商式 | propext, Classical.choice, Quot.sound |
| Shao.OQ3.cgf_fourth_derivative_actual_moments | theorem | 同一完整量词/前提、完整 M let；完整四阶五项商式 | propext, Classical.choice, Quot.sound |
| Shao.OQ3.centered_cgf_third_fourth_derivatives | theorem | 任意 Ω/可测空间、mu/概率实例、X；显式 h0/hmean；完整三/四阶合取 | propext, Classical.choice, Quot.sound |

audit 原输出为 FROZEN_DEFINITIONS 0、FROZEN_THEOREMS 3、ALL_THEOREMS 3、ALL_DECLARATIONS 3、AXIOM_GATE PASS；这与源逐项清点及收据吻合。实际所属共 3，全部为上述 theorem，无其他 private/generated owner，无非 theorem VALUE（0 项）；并非因没有打印 VALUE 就假定为零。局部 M/F 不产生额外环境定义，其完整值已在第 4 节单独审查。全部源证明已完整阅读，不要求重新输出 tactic 生成的巨型 proof term。

源文本禁止项扫描实际得到 0 个 sorry/admit/axiom/unsafe/native_decide；结合所有实际 owner 的 recursive collectAxioms，依赖仅标准白名单 propext、Classical.choice、Quot.sound，无 sorryAx 或新公理。没有编译成功却跳过转述忠实性、完整 TYPE/必要值、递归 AX 的情况。

## 6. 失败保留、最终版本及结论边界

native01 的 4288 B / 84 LF 源 SHA256 faf09f7be7dc738490a0548823586cc74f23f90910b5349e49a8d7c8703ca51b、RC1、完整 3218 B 失败日志 SHA256 7030113d8c2307ea55d2dcd84c2451e1c09fe904aac1d286daa96e6fa562c8cd 均仍在原服务器 run 目录。审查者完整读取失败日志，并只读比较 source-01 与 source-02。失败有两处 rewrite 未匹配：hlocal RHS 是显式 lambda，hD 使用点态函数代数形式。最终修订统一了邻域函数的表达形式并补充 Pi.*_apply/Nat.reduceAdd 化简，三个完整声明及两个 M 值未改。失败不是被当作通过，也没有重放已成功 producer/旧 AX。

最终 native02/same-first-O AX 的合格既有证据与本次独立完整源码→声明/全部 proof/全部实际 TYPE/全部 M/F/0 个非 theorem VALUE/全部 recursive AX 审查相互匹配。未发现该冻结单元的关键证明或证据缺口。

本报告不将本单元升级为原论文定理或完整 OQ3。严格 0<beta<2/5、p54 修复、外部结果归属、SAME E/rho、原 B/D、完整 order-six/full-frequency/Fourier inversion/exterior 范围均按既有状态保留；本单元没有关闭这些依赖。真实二维倾斜/标准化投影律上的 h0/hmean 实例化仍须另给合格同律接口。

REPORT_WRITE_AUTHORITY: RELEASED_ON_COMPLETION。报告写入后仅核验报告和输入哈希并向父任务返回结论及报告 SHA256；不继续写源、开检查、派发工作或持有后续报告写权。
