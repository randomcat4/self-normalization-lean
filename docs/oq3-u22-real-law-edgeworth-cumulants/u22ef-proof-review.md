# EF217 独立完整终审

STATUS: CORRECT

JUSTIFICATION: 冻结的唯一公共声明、全部五个声明内 let、完整实际 TYPE 与最终 90 LF 源码一致；证明从同一原始二次倾斜律导出推前概率性、真实零均值和每个实际投影的开邻域指数可积性，再消费精确合格 EE216 接口得到真 CGF 三、四阶导数身份。未发现关键数学缺口、附加前提或源题范围越界。首次成功目标对象与同一对象上的全实际拥有声明递归公理回执可精确复用。

## 审查身份与边界

- 独立非作者审查上下文：`/root/oq3_ef217_final_review`；模型 `gpt-6.1-sol`，推理强度 `xhigh`，全新上下文；使用 math-theorem，未使用 math-ultra。
- 完整阅读本次源码 1–90 行、冻结声明 1–18 行、范围文件 1–20 行、实际类型 1–19 行，以及 receipt、Audit、audit-record、build-history、dependency-source-binding、qualified-dependency-binding 全文。
- 对旧 U22A 只完整读取被消费公共源头 84–102 行和对应实际 TYPE 9–27 行，含全部 nu/means/D/F/f 值；对 EE216 完整读取冻结三声明、全部 26 行实际类型与资格文件。只校验既有独审报告精确哈希与资格，未重读旧证明或旧报告内容。
- 原始只读来源为 `C:/game/shao/current/oq3/proofs/r2/report.md`，本次完整阅读第 1、2 节（36–158 行），并核对前置结论中的严格指数范围。
- 本次未编译、未执行 Lean/公理审计、未修改服务器、未派生子实例或发送跨聊天消息。服务器操作仅为读取既有源码、回执、日志、对象哈希及钉死库接口。本报告是唯一写入文件；完成后停止并释放报告写权。
- 分项用量未由当前工具提供：输入、缓存输入、输出、推理子集均记为未取得；未把原始计数或估算换算为订阅百分比。

## 精确版本与证据绑定

下表为本次实际核对的 SHA256；源码、冻结、TYPE、Audit、范围及服务器回执/日志在本地副本与服务器现物间相符。

| 对象 | SHA256 / 覆盖 |
| --- | --- |
| `u22ef-source.lean` | `6ab4f76096963a17d26e30d9d935eb2f6b4b691339521c5859ebfaa460363672`；4414 B，90 LF，0 CR，无 BOM |
| `u22ef-frozen-declaration.lean.txt` | `f34723a6e5e6515c3e324c7ada6ba6c020e1434f8ff769abcee73365e215b910`；1134 B，18 LF |
| `two-hundred-seventeenth-unit-scope.md` | `78cf52faa30a762c2c4840cb627a8d30808679121557512e3a4653d92d3f8b7d`；1482 B |
| `u22ef-actual-types.txt` | `495dfa3c19aae1a5fbc401e39cfc2df8530da5c55e54c8d61d217f81f6f90452`；1190 B，19 LF，完整 1 TYPE / 0 VALUE |
| `u22ef-receipt.json` | `2adb88d99d2e9e91ae468353fa467f20f6b8dfba709e58c10b79209a60062b75`；8019 B |
| `u22ef-Audit.lean` | `8b250a46b66802ab3a4722cc9939ead8de44df414d6d94198b2b8967bb88120d`；2020 B，47 LF |
| `u22ef-audit-record.json` | `1830acb252c269d0733bfe5525a9322eb1eea78ba5f7fa0d9871416476690bfb`；3145 B |
| `u22ef-build-history.json` | `2f914f77680642e88322e1837fb6937fc04c2254f46c901fdddd35dd6bc14015`；4528 B |
| `u22ef-dependency-source-binding.json` | `8661d2a6ca4995dd4a599cad58acbb0a4beea0b5dc6b5229c7e0fc2796c828e5`；801 B |
| `u22ef-qualified-dependency-binding.json` | `455df3c58ec038be35a05c5ff0fb8fd78db7a0da25ef886ab225d5c64d970ccd` |
| 最终 `build-02.log` | `76d3c6726cfc380631d8d77a445cd6cca56d8818b99dd3f003fa58f432323bd7`；867 B；既有 native02 RC0 |
| 同首次对象 `audit.log` | `22d4f80eed761d84354cbf7e2df3da05a868c5149874cb6567b87af0fd46117b`；1442 B；既有 AX RC0 / PASS |
| 首次成功原始 `.olean` | `83d1c9741417f5d38a3dd40bea790df57e1d623f0ad579fcc55bb825e0a49ae8`；336032 B；服务器现物相符 |

服务器证据根目录为 `/root/rivermind-data/shao-lean-20261021/runs/oq3/u22ef-20261027`。当前工作树目标源码与 `source-02.lean` 同为上述 6ab4… 哈希；accepted-source-view 中目标对象解析到 lead-oq3 的首次成功对象，哈希与尺寸相符。钉死工具链文件为 `leanprover/lean4:v4.36.0-rc1`，实际工作树 manifest 的 mathlib rev 为 `807d3836b165983210ee2ecf3cd28f239436949c`。本次只读取这些记录，没有调用工具链。

## 完整声明、实际类型和 let 审查

源码 1–7 行仅导入 `QuadraticTiltCumulants`、`ScalarCGFThirdFourthDerivatives`，打开命名空间/记号并进入 noncomputable section。源码 9–26 行去掉证明分隔符后与冻结稿逐字相同；不存在额外公共或私有声明。

完整实际 TYPE 如下，已核对五个 let 及每个量词、测度、阶次与幂次，未省略内部值：

```lean
∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu],
  ∀ theta ∈ interior (Shao.Probability.bivariateMGFDomain mu fun x => (x, x ^ 2)),
    ∀ (A : Matrix (Fin 2) (Fin 2) ℝ),
      have nu := mu.tilted fun x => theta.1 * x + theta.2 * x ^ 2;
      have means := ![∫ (x : ℝ), x ∂nu, ∫ (x : ℝ), x ^ 2 ∂nu];
      have Y := fun x => A.mulVec (![x, x ^ 2] - means);
      have law := MeasureTheory.Measure.map Y nu;
      MeasureTheory.IsProbabilityMeasure law ∧
        ∀ (u v : ℝ),
          have X := fun y => u * y 0 + v * y 1;
          0 ∈ interior (ProbabilityTheory.integrableExpSet X law) ∧
            ∫ (y : Fin 2 → ℝ), X y ∂law = 0 ∧
              iteratedDeriv 3 (ProbabilityTheory.cgf X law) 0 = ∫ (y : Fin 2 → ℝ), (u * y 0 + v * y 1) ^ 3 ∂law ∧
                iteratedDeriv 4 (ProbabilityTheory.cgf X law) 0 =
                  ∫ (y : Fin 2 → ℝ), (u * y 0 + v * y 1) ^ 4 ∂law -
                    3 * (∫ (y : Fin 2 → ℝ), (u * y 0 + v * y 1) ^ 2 ∂law) ^ 2
```

`nu` 是同一 mu、theta 的实际倾斜测度；`means` 是这个 nu 下的 x、x² 真积分；`Y` 在原实数样本空间中先中心化实际二次对，再左乘固定 A；`law` 是这个 Y 的真推前；`X` 是推前空间上的任意实方向投影。声明中没有独立可选择的 law、means、中心化常数或 CGF 值，也没有把指数可积性/零均值作为 law 的输入前提。

## 精确依赖资格与完整接口使用

U22A 的源哈希为 `ea105db471a073ac5eca67b4f94ff986766fd3fe3685790fb4859497da49289a`，实际类型文件哈希为 `4c6d4ab35fb2f7e24be183aeab1e3c7b30d90a6a54aeec6c0691e598d4094c7a`。已核 `u22-milestone-manifest.json` 中 U22a 精确映射，既有完整独审为 `f90d463b84a42513f088e7c72c199c6352f6b6e0210f463bfbd873ff844663e9`，180 LF，`CORRECT_FULL_REPORT_LEAD_READ`；报告文件实际哈希相符，仅复用资格。服务器被消费旧对象 `820239a2a46ae6f3fa5658c5a5f8aca431638d25fbd3a6075ab480d7616b087e` / 258112 B 与绑定相符。

完整被消费 U22A 接口的量词正是同一 mu 为概率测度、theta 位于二次二元 MGF 域内部；其 let 值逐一为：nu 等于 mu 对 theta₁x+theta₂x² 的倾斜，means 等于 nu 下 x/x² 积分，D 等于 `parabolaCovariance nu`；任意 d 下 F(x)=d₁x+d₂x²，f(t)=log∫exp((theta₁+td₁)x+(theta₂+td₂)x²)dmu。返回 nu 的概率性、x/x² 的 MemLp 2；对每个 d 返回 `0 ∈ interior(integrableExpSet F nu)`、F 的 MemLp 2、所有自然幂可积、f 的一阶导数为 d₁means₀+d₂means₁，以及二阶导数为 d₁²D₀₀+2d₁d₂D₀₁+d₂²D₁₁。本次只使用前述概率性、两坐标 L² 和每个 F 的开域/L²，未误用后两条导数结论或更强假设。

EE216 源哈希为 `e45f0061beaa274734b17fe61f484f9cfc2199d0ec33d884b59b9c77c2644b8a`，冻结文件 `4447ef1dd7b5f4e36f6ac1b510353fc1d772b906db62ba4835ef620504e24f9c`，实际类型 `364225218818d9d17e67cb99387ef11e10a417ca188c432e46d18f5116f1f8fe`。资格文件 `020a556447a8c309595eac6c6f35c0e5859da95d1dee73ca3bbf5a349eb7ed30` 已是 COMPLETE_QUALIFIED；它绑定完整独审 `4297ee009177bbcab1a6814fe1f0057c5d7d701b741ad5c10fa5c73f38ba3191` / 108 LF、parent 全文读取并停止、receipt `b8abefd3afb4b2502ed6843cd1d37692fc0572c7bf2cd3665cf66a2969020045`。实际报告/receipt 哈希均相符；服务器首次原始对象 `97621896a1fb97829675965fdbdba8176ddfd30a00237d98faa326a85965bab1` / 441152 B 相符。未重审旧证明或重跑其检查。

EE216 前两声明的全部 M let 均是 `M k = ∫X^k exp(vX)dmu`，分别给出标准 M₃/M₀−3M₂M₁/M₀²+2M₁³/M₀³ 与 M₄/M₀−4M₃M₁/M₀²−3M₂²/M₀²+12M₂M₁²/M₀³−6M₁⁴/M₀⁴。第三个被直接消费接口只要求某概率测度、同一 X 的 0 内部指数可积和真实积分均值 0，结论恰为 `cgf'''(0)=∫X³` 与 `cgf''''(0)=∫X⁴−3(∫X²)²`；不存在额外 coherence、目标系数或高斯前提。

## 全部证明逐段核对

1. **源码 27–30 行：保持测度身份。** 展开冻结五对象中的前四个 let 后，原 mu/theta/htheta 原样调用 U22A。返回 hnu 是定义上同一个 nu 的概率证据，hxL2、hx2L2 也是这个 nu 下实际 x、x² 的 L² 证据；局部实例仅登记已证概率性。
2. **31–42 行：推前概率性。** 对每个输出坐标 j，Y 的值是两项有限和 `Σk A j k * (Wk−means k)`；means 对 x 为常数，因此连续。连续导出可测/几乎处处可测。`Measure.isProbabilityMeasure_map_iff` 使用的是 nu 下 Y 的 AEMeasurable，`.mpr` 从已证 nu 概率性推出同一 `nu.map Y` 概率性；方向正确。没有把任意非可测推前默认为概率律。
3. **43–51 行：实际投影的全部 proof-let。** 对任意 u,v，定义 `d=(u*A00+v*A10, u*A01+v*A11)`，`F(x)=d₁x+d₂x²`，`center=d₁means₀+d₂means₁`。这是 A 的转置作用于方向 (u,v)，并非错误的 A 乘方向。逐点展开 mulVec/dotProduct/Fin2 后，ring 证明 `X(Y x)=F x−center`；例如 u 投影行 0、v 投影行 1，x 与 x² 的系数分别正是这两个 d 分量，常数项完全对应真 means。hX 的连续性对所有 u,v 成立。
4. **52–59 行：真均值计算与可积性。** U22A 对这个实际 d 给 hF0/hFL2。nu 是概率律，故有限测度；`MemLp 2 → Integrable` 在 1≤2 条件下给 hFI，hxL2/hx2L2 同理。积分加法前分别提供 d₁x 与 d₂x² 的可积证据，再用常数乘积分，得到 `∫F dnu=d₁∫x dnu+d₂∫x² dnu=center`。末尾 rfl 只消除 nu 的定义展开；未换测度或把形式均值替代实际积分。
5. **60–68 行：同一 law 下的真实零均值。** `integral_map` 的两个条件是 Y 在 nu 下几乎处处可测，以及 X 在推前律下几乎处处强可测；分别来自 hY、hX 连续性。它把 ∫X dlaw 精确变成 ∫X(Yx)dnu。用逐点 hid，合法的 `integral_sub hFI (integrable_const center)` 与 nu 总质量 1，得到 ∫F−center，再由 hFmean 等于 0。不存在先假设中心化再调用结论的循环。事实上 F−center 可积，结合相同 map-measure 可积等价也保证这个真实均值不是未定义积分被置零的伪象。
6. **69–78 行：指数平移的系数与符号。** 对任意 `q∈integrableExpSet F nu`，hiq 是 exp(qF) 的可积证据。常数乘选择 `exp(−q*center)`，正好满足 `exp(−q*center)*exp(qF)=exp(q(F−center))`；exp_add 后的环恒等式符号正确。q 可以为任意正、负或 0；不需要非零分母、额外有界性或依赖样本的中心常数。
7. **79–83 行：推前指数可积等价。** `g(y)=exp(q X(y))` 连续，因此在 `nu.map Y` 下几乎处处强可测。`integrable_map_measure` 的 `.mpr` 从 `Integrable (g∘Y) nu` 推出 `Integrable g (nu.map Y)`；方向正确，Y 的 AEMeasurable 已具备。显式 change 仅把组合函数显示为 x↦exp(qX(Yx))，再由 hid 转成已证 hshift。没有将原空间可积性错当作推前空间同名函数可积性。
8. **84–85 行：开邻域方向。** 已证集合包含是 `integrableExpSet F nu ⊆ integrableExpSet X law`；故 interior_mono 将已知左集合内部的 0 送入右集合内部。这里保留了双侧开邻域，未以单点 q=0 可积冒充解析条件；也没有把包含方向倒置。
9. **86–87 行：真 CGF 三、四导数。** 调用 EE216 的测度是本声明的 law，函数是本声明的 X，实例是 39–41 行建立的 hlaw，两个前提为本证明 60–68、84–85 行导出的 hmeanX/h0。返回的 ∫X³、∫X⁴、∫X² 正是同一 law 下实际投影矩，X 的 let 展开后逐字匹配目标。四阶式确实是 `m4−3*m2^2`；未将其改为 Gaussian/目标系数或误写成三阶矩平方。88–90 行只结束 section/namespace，无未覆盖源码。

本次还读取了钉死 mathlib 的原接口：`MeasureTheory/Measure/Typeclasses/Probability.lean:139` 的 map 概率等价；`MeasureTheory/Integral/Bochner/Basic.lean:1076` 的 integral_map；`MeasureTheory/Function/L1Space/Integrable.lean:355` 的 integrable_map_measure；`Probability/Moments/IntegrableExpMul.lean:112` 的 integrableExpSet 定义；`Probability/Moments/Basic.lean:122/126` 的 mgf/cgf 定义。它们的可测性条件与两个 `.mpr` 的方向均和上述逐行分析相符；cgf 是实际 `log (∫exp(tX)dlaw)`，不是另置的形式级数。

## 原来源语义、边界和后续承重范围

原报告 40–45 行定义 W=(X,X²)、K 和真实指数倾斜 P_theta，并把 m(theta) 记为真均值/梯度；83–88 行取标准化变量 `Delta(theta)^(-1/2)(W−m(theta))`。EF217 对实际倾斜的两个真矩中心化，再取任意固定 A，保留了这个构造；选择已存在的准确白化矩阵时可供同一原始变量消费。它没有引入一个与原模型脱钩的概率律或目标累积量。

A 完全任意，包括零矩阵、奇异矩阵、非对称矩阵；u,v 允许坐标轴及 (0,0)。上述连续性、代数、可积性和平移证明不需要可逆性、正定性或非零方向，因此这些退化情形都覆盖。EF217 没有声称任意 A 下 m2=u²+v²；必须由后续同一 law 的协方差 I 消费者实际证明后才能代换。它也未宣称参数一致半径、统一导数界或高阶余项控制。

本单元没有 beta、E、rho、weak-Cramér、误差系数或外部 Edgeworth 定理前提，因而没有改变原来源的严格 `0<beta<2/5`、p54 修复、外部结果归属、同一 E/rho 及原模型身份。order-six、全频率、反演、外区、原 B/D 与 OQ3 根目标仍未由本桥接闭合；不以此一阶有限单元冒充根定理完成。

## 全拥有声明、公理与失败保留

Audit 完整读取后确认：它枚举环境中 owner 恰等于 `Shao.OQ3.OpenDomainAffinePairCGFCumulants` 的每个常量，拒绝新 axiom，对每个实际拥有常量执行递归 `Lean.collectAxioms`，只接受 propext、Classical.choice、Quot.sound；不是只打印预列目标而忽略隐藏拥有者。现物 audit.log 完整给出唯一实际 DECL/TYPE/AXIOMS/KIND，并记录 FROZEN_DEFINITIONS=0、FROZEN_THEOREMS=1、ALL_THEOREMS=1、ALL_DECLARATIONS=1、AXIOM_GATE PASS。因此完整覆盖为 1 公共定理 / 1 实际拥有定理 / 1 TYPE / 0 非定理 VALUE；全部五个声明 let 和三个 proof-let 已在上文完整复核。

实际递归公理集合严格为 `[propext, Classical.choice, Quot.sound]`。最终源码没有 sorry、admit、新 axiom、unsafe 或 native_decide；两处 letI 风格警告只影响书写建议。原日志的 mathlib working-tree 提示保留为历史输出；本次读取的钉死 manifest、精确依赖源码和已接受对象绑定相符，没有更新库或触发旧证明重建。

失败 native01 精确源码为 `06ab87a025796661bfd5812e2758ba124b380e89d5055be6c47336ae8e03ff01` / 4362 B / 88 LF，失败日志 `8d900eea2dcbb51d9d4d31a93b8359b2bf7b1128553016b3490b3f7691cd7b56` / 5234 B；两者服务器现物与 build-history 相符，RC1 保留。已读取完整失败日志和 source01→02 差异：只在 hFmean 末尾增加 rfl，以及在 map 可积证明中显式 change 组合函数并用 hid；源码声明、所有量词/前提和结论未变。native02 的首次 RC0 与其首次 O 是新的最终精确源码证据，未把失败01计为通过，也没有重跑成功检查。

服务器记录的成功 native02 与 AX 使用恢复后 phase40、CPU36–39/44–47、原 c12-heavy.lock 资源约束，native `-M8192 -j4`；内存记录保留 Root-owned phase39 helper 的历史名字/公式而顶层 resourcePhase 为 ROOT_OQ56_OQ3_40，不能把这个字符串误读成另一次数学执行。本审查复用既有执行，不分配任何新资源。

## 最终裁决与释放

EF217 最终精确 6ab4… 源码的完整源到声明语义、全部证明、完整实际 TYPE/let、0 VALUE 与同首次 O 的递归公理证据通过独立终审。没有要求修改冻结声明、增加前提或重跑任何旧/新成功检查。结论是该桥接单元 CORRECT；数学新颖性及 OQ3 根目标完成不在该裁决之内。

报告写入完成后，本独立审查上下文停止，报告写权释放；未保留源码、冻结、服务器执行或其他文件写权。
