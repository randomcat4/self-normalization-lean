# Unit231 repair-01 同一独立审查者的完整受影响审查

STATUS: CORRECT

SOURCE_STATUS: SOURCE_ACCEPTED_FOR_NEW_NATIVE_ONLY

QUALIFIED: false

KERNEL_STATUS: PENDING

新精确源为 `3489dafa4bce4cafbb4ed26bcd7399c08561f536291a6556f203e40dbf19ed1e`，33073B、573LF、0CR、UTF-8 无 BOM。此次三块限定修复在原冻结命题、模型与普通数据下成立，未发现新增数学／来源／量词／实质接口缺口，可进入该精确版本的新 native。此判断不宣称新源已通过 elaboration 或内核。

角色仍是 `/root/oq56_original_coded_strict_frontier231_source_review`，即从未作者的原完整 SOURCE 审查者；沿用 math-theorem，不启用 math-ultra。完整读取并核验 repair-review activation `eb32400b0f931aaa58e55b390f6760250cb372917d227a20699a281bc8f5dfe2`／2966B 后已实际 ACK。本轮只拥有 `source-review-01/repair-01/**`；此前完整审查、manifest 与最后 RELEASE 的字节保留。没有修改任何证明源、冻结或其他所有者文件。

## 复用证据与独立改动边界

基线 `885505f80bd8640a95a13d17694373faec66ece6a4df10614d456c475e20d227`／32683B／566LF 的完整逐行 SOURCE／证明／primary／所需 API 审查精确复用，绑定原 manifest `0434f3dfc86c415667632a07e55d3630c4a690be7a9ab33678dd8ec38b5e0c3e` 和 release `5ed6c0e30aace711ab59527f463cf324bdb9dbe28a20b930a927a2d010b2019a`。原9个 manifest payload 全部重新核对绑定；这不是另一遍旧完整证明审查。

已独立阅读作者完整 repair REPORT、全部 EXACT-DELTA.json／patch、当前三块改动和周围上下文、受影响的可积性／积分运输／极限／窗口／最终组装，并核对实际 pinned API。7个作者 payload、14个作者输入均逐项核验。本人从基线按三段 before→after 重新构造得到新源，完全相等；另以独立逐行差分得到4个原子修改位置，因为第三个作者逻辑块中的积分 API 调用与后续 rw 被一条保持不变的 q 改写行隔开。此差别是逻辑块与原子差分的不同分段，不是额外源修改。

独立差分的5个相等区间合计32381B，旧变更区合计302B，新变更区合计692B，净增390B／7LF。所有三段冻结 preamble/head/closing 与完整公开声明均逐字节不变，因此已审的63个公开普通值类型／RHS、19个目标块及其全部量词保持。证明普通 let 仍只有 zeroSection、tailIndex；五条既有 letI 行完全相同。新增 hDifferenceMeas 是当前 k 分支内的派生 Prop，既不是普通数据，也不是 caller 前提、callback、实例或顶层 helper。

## 实际失败及修复一：可测截面复合

完整 native01 诊断显示旧314处的项类型残留 `ξi ∘ zeroSection`，而目标是 ξ0i 的显式 λ 函数。旧源码已有具体 zeroSection、逐坐标 Pi/Prod 可测证明以及逐点定义关系；数学关系没有缺失，原 simp 列表缺少复合展开。

当前314–315只在原 simp 列表加入 `Function.comp_def`，再展开原 zeroSection／ξ／ξlocal／ξ0。对任意 ζ 和 i，`ξ i (zeroSection ζ)` 归约为 `g ((ζ i,0).1)/N = g(ζ i)/N`。这是同一个原函数，不改变截面值、类型、可测空间或均值。固定 Constructions 的完整 Prod.mk 与 Pi 可测 API 被读取；输入与目标仍分别是 mN₀、mAug。

下游318–324仍沿同一 q 保测律运输 ξ0 在 P₀ 上的均值零，325起 Ylocal 的 canonical code 和 quantizer 路线没有变更。这里依旧不要求0在 Uniform(Ioo 0 1)支持中、不要求 Ω 有默认元素、不把截面当成保测映射。P05 与依赖该可测性的 P07、Fz 可测性及后续 API 前提保持原语义。

## 修复二：同一 Qε 的可测 Prop

旧430处诊断返回 `Measurable (Dη k - fun x => D1(q x))`，而目标是 `Measurable (Qε k)`。已完整读取 pinned Arithmetic 205–290 的 MeasurableSub₂、生成的 Measurable.sub 对应声明及上下文：它给函数空间差的可测性。原 hQDifference 是逐点等式，因此需要明确把被证明函数写成逐点 λ 形式，供原等式改写。

当前431–434先由原 hEnvDEta.sub hD1Meas 证明

`hDifferenceMeas : Measurable[mAug,borel ℝ] (fun x => Dη k x - D1(q x))`，

再按未改的 hQDifference k 识别成 Qεk 的可测性。λ 的函数差与 Measurable.sub 返回值定义相等；逐点等式给的仍是原 Qε。没有重新定义 Qε、Dη、H、M 或 η；没有额外外部假设。

完整 hQEnvelope 的其余四个返回项、ρ=Kεk 的识别、Q／|Q| 真实可积性、积分上界、两条逐点包络界和442–450的夹逼极限均保持字节（仅行号平移）。P10/P11 的含义和 hQEnvelope 的字段投影没有改变。最终同尾段继续消费同一个 hQLimit，未扩大成 weighted 或 sourceCost 极限。

## 修复三：原产品到约化产品的显式 map 积分

旧482／484两条实际诊断都区分 synthesized mN₀ 与由原测度 P 的类型推得的 mN。原载体相同而可测结构不同；需在该积分映射调用明确原域和目标域，不能让当前局部实例替代原空间。

已完整读取 pinned Bochner.Basic 的实际全局参数上下文139–184、1008，以及1065–1085的完整映射积分声明。当前486–489的全 @ 参数依次固定：α=Fin n→Ω、G=ℝ、既有实数 NormedAddCommGroup／NormedSpace 实例、原 m=mN、原 μ=P、β=Fin n→Ω、目标可测结构 mN₀、φ=id、hφ=hIdMeas、具体函数 `fun ζ => Fz(ξ0 i ζ)` 及其已有强可测证明。参数与实际声明相符，两个显式 inferInstance 只是原 API 所需的既有全局代数实例，没有增加局部 letI。

因此得到的等式仍精确为

`∫ζ Fz(ξ0 i ζ) ∂(@Measure.map ... mN mN₀ id P) = ∫ζ Fz(ξ0 i ζ) ∂P`。

当前491用已由同一226包提供的 hP₀map.symm，将左端的原→约化推前测度改写成 P₀。方向正确：hP₀map 原来是 P₀=map id P。这里不再从 hId.map_eq 重新推断被遮蔽的原空间。hIdMeas、hId、原 P 与 P₀、实际 Fz 函数均未改变。

增广 q 分支483–484／490完全保留；492–494的两个具体积分目标与最终 `hFromAug.symm.trans hFromOriginal` 完全保留。476–481已经分别给 P₀ 与原 P 的真实可积性，因此这次显式化没有以总化积分默认零替代实际成本。495–500的有限求和运输与坐标／总极限仍到达原 P 的 δ0／L0。

## 受影响下游及未改范围的完整覆盖

已阅读502–518原 μ 上230完整预算的当前上下文，519–554的确切闭窗口／229严格尾段／Q容差相交，以及555–570的最终右结合构造器。β、cWindow、原 μ 的 p 阶矩前提、源 z 而非1+z、β=0分支、闭窗口端点、同一实际 η／ν／q 序列均未改变。P20仍只在原窗口内取得严格 δν/Lν余量，再取 kb 与 kq 的 max；没有跨 n/z/模型的统一 k0 声称。

目标覆盖复合如下：

| 目标 | 此次覆盖 |
|---|---|
| P01/P02/P03/P04/P06 | 原完整证据精确复用；全部声明和对应证明不变 |
| P05 | 修复一及当前截面上下文完整受影响复核 |
| P07 | ξ0可测→q均值运输→泛用 producer 输入的下游复核 |
| P08/P09/P12/P13/P14 | 同一当前 εk 编码／归一化／完整与删除因子化旧完整证据复用，相关字节不变 |
| P10/P11 | 修复二、完整 Q 包络输入／返回与 L¹ 极限下游复核 |
| P16 | 截面派生 Fz 可测性、P₀／P／ν真实可积性上下文复核；未改的原解析证明复用 |
| P17 | 修复三的两次保测积分、有限求和运输完整复核 |
| P18 | 原 μ 230量化预算证明精确复用，并核对当前使用处原 P／scalarBudget 未改 |
| P19 | δ/L运输后的无条件极限受影响复核 |
| P20 | 原窗口余量运输、同229序列与 Q-L¹公共尾指标受影响复核 |

一次226存在性调用和同一 m₀ 的先后作用域保持；所有当前 k 的因子化仍来自同一返回 forall 包，而不是另选模型。63个普通值和19个目标块的完整已审类型／RHS 通过未改的冻结 head 精确承接。未改变的 primary 或旧226／229／230证明不重复全审；没有旧 producer／leaf AX 重放。

## 证据状态与释放

完整读到的本单元 native01 是自然 RC1、4个 errors、5个样式 warnings、109.05352794751525秒、objectAfter=null、非 timeout，owned组已自然结束，19468保护记录保持。该失败继续作为旧精确源的失败，不是成功或不确定在途。没有改动对应失败源、收据、配置、日志或既有独立报告；没有关闭样式检查，五个 warning 位置保持。

本轮 source／freeze／other-owner edits=0，Lean／server／network／upload／GitAPI／children=0；没有读228或232实现／诊断。请求 model/effort 为原 gpt-6.1-sol/xhigh，未暴露实际配置与四项 usage 均 null。未做新内核或 AX 审计，qualified=false、kernelPending=true。

结论为 CORRECT／SOURCE_ACCEPTED_FOR_NEW_NATIVE_ONLY。下一步仅是 lead 对3489…新精确源的新 native；成功后，同首次原对象的全部实际所属 TYPE／必要 VALUE／递归 AX 与本同一独立上下文的源覆盖合并，方能判断 qualified。OQ56／原根及 weighted、CDF、外部 Shao–Zhou、p0小量等未付范围不因这次修复改变。
