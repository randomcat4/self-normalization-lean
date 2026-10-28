# unit253 作者来源与证明路线

本件是冻结定理 `actual_original_level_dependent_countably_generated_model` 的完整本地证明候选。它只提供一个在全部 n、当前 z 之前选定的可数生成模型，并在同一裁剪测度上保留完整现有包与任意有限可测观测的分布律。`qualified=false`、`machinePending=true`、`fullOQ56=OPEN`。

## 原始数学来源

原始只读输入为 `C:/game/shao/current/oq56/inputs02/p51.md`（SHA256 `96920f428b8fc09788a6388103cefe398e3ec739129a5922b984babd09e99359`）与 `p54.md`（`e03649e1324def02de3ff234bcc94c9e1cb643e074a324e1817ef940f5e01c43`）。两篇全文读取，原字节保持。p51 S1 的原实际 D/J/分母系数、S2–S3 的当前层级与真实删除费用、S4 的两矩纠正包络背景保持；p54 对条件 p 矩任意多项式速率的否定、统一有界修复，以及真实坏事件的原子安全付款边界保持。本件不使用这些未闭合概率付款结论来冒充模型构造。

p51 明确命名的 Shao–Zhou (2016), arXiv:1405.1218v5 的随机区间、自归一化及 DC 输入仍属外部结果；本件不改变其归属，也不声称从零证明这些结果。

## 精确已接受接口

1. `library/Shao/OQ6/OriginalCountablyGeneratedModel.lean`：SHA256 `8691f69ca9ab84649f92b20385c415a2129250cc8f64375d6296e2d59a381627`、21808B。调用唯一原定理 `actual_normalized_original_countably_generated_model.{u,v,w}` 一次。声明前半的完整 core 在重命名主定理后逐字一致。本件保留它的同一个 m₀≤mΩ、可数生成性、原 h 产品可测性、常零 f 可测性及全部前21个核心结果；仅丢弃旧最后一项固定层级1的专用有限样本包。
2. unit251 完整源 `OriginalLevelDependentClippedSourcePackage.lean`：SHA256 `ab6f36156e138a4616fa769bd7ad123b3cd0adf92be79414e6ab226598291e53`、14424B；资格 `4fcd76676abfb79c7e1aac9c8fec68f4bb58d5b12adf13d5b4361113a096c5f0`。完整当前512预算、真实删除因子、裁剪、零分母约定、几何窗口与五项 weightedcost 包直接实例化在同一 μ₀。
3. unit252 完整源 `OriginalLevelDependentCorrectionEnvelope.lean`：SHA256 `fc91fdfe3a92b472deba8ecea7183c62381643524d9cf875a3e594c649782020`、10857B、201LF；资格 `b5c4d850a7d3a97de99e6ad9e2bddcadc4b583acab2b28bca26efb216cf4acb0`。完整原 D/J/A/B/e 无权可积性、真实坐标矩、H/M/κ/Δ 全实 ε 的 L¹ 包和双侧趋零直接实例化在同一 μ₀。已完整读取其最终报告、裁决及875LF实际所属TYPE；复用已资格化证据，不重做其旧检查或扩大旧审阅。

冻结声明 SHA256 `7b08f567f410e05f78e93155a395528b20b70d8d2a3be77e5a93d43e0932550e` 与激活 `e22867e5a8b3b2591629d24d13d9fad7dfb5766e4b3d05fe9a43fbdebe63e081` 保持。冻结时的252待资格状态只作历史事实；其后资格和明确激活才授权本作者。

## 证明构造与接口匹配

先引入原声明的九个 let 定义；从旧模型一次取得 m₀、hm₀、countability、hh₀、hf₀ 与 hcore，立即提交同一见证。随后只定义 μ₀=μ.trim hm₀、m₀ 的局部可测实例及原 g₀/r₀/v₀/rho₀。hcore 的概率、map-id、逐点投影／残差／能量／rho恒等式、逐行可积性、h与r的L²、均值／投影二矩、典范性、投影律／Lp与产品律，连同任意有限 J／任意可测目标 B 的观测律，均直接作为原项返回。

最后才引入任意 n≥4、当前 z≥1与原 tiltwindow。显式传入相同 Ω、m₀、μ₀、hprob₀、h、hh₀、hh₂₀、hhsymm、hcenter₀、hgsecond，分别调用251与252。外部 h 假设均由同一旧模型 core 实际给出；对称性是与可测实例无关的同一逐点 h 对称性。没有跨 n/z 重新选择 m₀。两包的局部 g/r/v/rho 虽遮蔽外层同名符号，其定义正是 μ₀ 下的原投影与残差，核心等式又将它们与原 μ 下的量逐点相连。

没有新增选择器、标准Borel、高阶矩、混合四阶矩、产品包络或 sourcecost 小性假设。没有从 weighted 可积性反推 unweighted 可积性。没有重新证明旧producer或重放旧native／TYPE／AX。

## 开放范围

本件没有构造增广标量编码、没有消费完整 weighted-source-law、没有给物理坏事件付款，没有证明CDF、relative tail、DC或fullOQ56。后续链仍需独立完成。本地源清单中的79个定义型条目与42个引入／析构绑定只是源级库存，实际模块所属常量数待服务器环境枚举。
