# general116 consumer 最终独立审查 v1

STATUS: CORRECT_FINAL_SOURCE_ACTUAL_INTERFACE_AXIOMS

本审查仅接受冻结的整数序列 `Shao.OQ4.RademacherAdjacentLog.adjacent_log_bound`。完整候选为 `general116-resume-consumer-author-v1/Source.lean.txt`，SHA256 `ac6c3088b3b1306c133a61ad9ff7e29a4090baa452eabd013aa8f0a488c85e26`，4674 字节、102 行；与最初匿名候选逐字相同，UTF-8、LF、无 BOM。数学冻结 `14886712…` 与完整形式冻结 `3926e18b…` 均核对原始字节，公开声明头与形式冻结逐字相同。审查者 context131，按父实例明确调度使用 fresh gpt-6.1-sol/xhigh；作者与审查者分离，未修改证明或其他所有者文件，未读作者修复总结或其他当前审查票。

来源是只读 `C:/game/shao/current/oq4/c01/spectrum01.md` 的既定渐近域及相邻格点移动代价。逐序列量词是冻结文件明确披露的保守规范化；本结论不冒充原文逐字定理，也不关闭原始 OQ4、Spectrum 或 energy 根。rawleaf 增量为 0。

完整数学审查覆盖如下。

- 对象确为 `Fin N → ℝ` 路径、通常有限产品 Borel 结构，以及固定 `law = (δ₁ + δ₋₁)/2` 的产品律。所读 Bridge 定义是 `Measure.real` 作用于全部正前缀的实际弱/严格事件；`prefixSum` 是按 `i.val < r` 求和。`S2.p` 是同一产品律的实际 `closedStrip` 概率，没有把概率替换为谱和或目标表达式。
- `nSeq kSeq : ℕ → ℕ`、`hk`、二次尺度趋于正无穷及固定实数 `M > 0` 的最终三次尺度上界，全部保留。实际公开类型也完整保留 `hscale3`。证明没有用到它，是因为已验收有限定理给出更强的统一有限域结果；没有改动声明或暗添概率正性、单调性、奇偶性、三次尺度正下界等条件。
- 从有限定理取得 `C > 0`、`K ≥ 2`、`T ≥ 1`，且这三个见证先于所有 `N,k`。`hk` 与 `hscale2` 分别给出 `K ≤ k_j` 和 `4T ≤ N_j/k_j²` 的最终尾段，取二者交集得到一个共同自然数 `J`，满足任意 `j ≥ J`。不要求序列单调。
- 在此尾段 `k_j ≥ 2`，所以实数嵌入 `k_j > 0`、平方严格为正；先合法消去分母得 `4T k_j² ≤ N_j`。由 `(k_j+1)² ≤ 4k_j²` 及 `T ≥ 0` 得 `T(k_j+1)² ≤ N_j`，恰为有限定理的共同域。由 `T ≥ 1` 和 `(k_j+1)² ≥ 1` 推出 `N_j ≥ 1`，再精确转换回自然数。未利用除零的总函数值。
- 有限定理在完全相同的 `N_j,k_j` 上给出两项实际 `S2.p` 的严格正性、对数差非负和 `C(N_j/k_j³)` 上界。`weakEvent_eq_closedStrip` 需要阈值非负：高阈值由 `k_j > 0`，低阈值由 `k_j ≥ 2`，均已证明。展开两概率及产品测度后，只以已证事件相等重写，完整保留同一 `N_j` 与实数阈值 `(k_j:ℝ)-1`。
- `strictProbability_eq_integer N_j k_j` 的唯一自然数域条件 `1 ≤ k_j` 由 `k_j ≥ 2` 推出。它给出实际严格概率等于低阈值弱概率，后者已严格为正。所有要求的合取都在同一 `J` 上成立；两个对数都有通常正概率意义，未使用 `Real.log 0`。

Bridge 与 finite 内部证明复用既有合格完整审查，未重新审查其已验收内部证明。所需 Bridge 定义、`weakEvent_eq_closedStrip`、`strictProbability_eq_integer` 的源码及完整实际类型、有限定理完整实际类型，以及相关 `law`、`prefixSum`、`closedStrip`、`S2.p` 定义均已核对。精确复用的最终依赖 receipt 分别是 `real-threshold-v6-final-review/receipt.json` SHA256 `11357a1c3c37b18da187087050458b36099b51dc59ea333f7958a4d6ff78dcff` 与 `general116-finite-final-review-v4/receipt.json` SHA256 `003e0bfc2d3e1c7b279ca4d3d7704e7c3faf75aab486c8d5afcce5c518399daf`。

实际所属声明覆盖不是按命名空间抽样。未过滤环境差、module ownership、stage2、audit、actual-owned 和 raw rows 的名称集合全部一致：1 个公开定理、0 个显式 private、1 个 generated，共 2 个 theorem；0 个 definition value、0 个 owned opaque value。2 个完整实际类型全部阅读，全文接口按 JSON 逐字重建一致。公开类型的全部量词、三条前提、固定 `M`、尾段见证及八项合取与冻结一致。generated `adjacent_log_bound._proof_1_1` 的完整类型是：对任意两条自然数序列、`K,J,j`，由 `2 ≤ kSeq j` 和 `¬ 1 ≤ kSeq j` 导出 `False`。额外未使用参数不提供数学假设；该辅助命题只是合法自然数算术矛盾。

独立校验复用既有完整 Lean.Expr repr parser 的原始函数，其文件 SHA256 `7f22721b8265c4c90f36a7c78033ad3ff3ac3b4c9743cb1ad0a32b5cbe87873d`。本单元只对实际新接口适配输入：2 个 raw type 表达式全部解析，856 个表达式节点，所有 bound variables 在作用域内，完整消费输入且常量引用逐项等于 audit。没有不存在的定义值需要补读。完整 type+value 引用图独立验证为 40,202 个唯一节点、1,209,724 条边，恰等于从全部 2 个 owned 声明递归可达的闭包；无悬空引用、unsafe/partial 或缺失的定义/定理/opaque 值。36 个 imported opaque 均提供值。逐个 owned 声明重算传递公理集合，均仅含 `propext`、`Classical.choice`、`Quot.sound`；没有 `sorryAx`、`ofReduceBool` 或 `native_decide` 引用。

完整 `findOLean` 表有 4,816 个唯一导入，恰为旧 4,814 加 Bridge、finite。旧 4,792 个非项目实际路径逐字不变；22 个原项目导入改用统一别名目录，但其原始解析对象路径、源码及对象 SHA256 与既有完整验收映射相同，22 个本地只读源码 hash 也逐项相等。新 Bridge 对象为 `a8ea9dcc…`，源 `644f10f1…`；新 finite 对象为 `13ef20d6…`，源 `ec4b34c5…`。两者路径、hash、字节数、device/inode 与纯源对象 receipt 一一吻合。24 个项目别名覆盖全部实际项目导入，15 个项目模块内共 383 个闭包声明；未发现未知项目所有者或名称遮蔽。

服务器检查复用作者成功记录：Lean `v4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，CPU18–21、`-M8192 -j4`、标准 lane flock、`autoImplicit=false`、`debug.skipKernelTC=false`、trustLevel1025，exit0 / 12.470 秒。审计追加文本 SHA256 `c2dab4ce…`；`Source + LF + suffix` SHA256 `57d81b51…`；完整 audit SHA256 `97e34cfd…`。已读完整 audit suffix，确认全环境捕获、全部类型和透明定义值导出、`value? true` 包含 opaque、type/value 双递归及实际导入查找均在成功服务器调用中执行。

最终作者 receipt SHA256 `b09f4dd8513a6578d734283f9cb21ed7357528e34ba100c544a63d33ee1466c7` 与原始 transport 响应及本地 artifact hashes 已核对。缺少独立本地 `actual-imports.json` 副本不构成内容缺口：完整表在 canonical audit 中，按既定导出格式逐字重建后的 SHA256 `a072418d…` 与服务器导出记录相同。

根集成所需唯一纯源 consumer 对象已单次成功生成，exit0 / 4.102 秒，源码仍为同一 4674 字节 `ac6c…`，未追加 audit suffix。对象 `8588160d6a59ba6093b2f51b3a84ad64601d649c897f14b1f41b170669fe0704`，255496 字节，device64947/inode3546960，路径见 receipt。后验 Bridge、finite 对象身份及 hash 不变，进程已回收、flock 已释放。审查者服务器、Lean、Git、网络及子代理调用均为 0；只写本审查目录。

没有 CRITICAL GAPS。此报告和 receipt 可供父实例按精确 hash 接受冻结整数序列116单元；不表示已执行集成、发布或原始研究根闭合。模型用量计数未暴露，input/cached input/output/reasoning subset 全部为 null。
