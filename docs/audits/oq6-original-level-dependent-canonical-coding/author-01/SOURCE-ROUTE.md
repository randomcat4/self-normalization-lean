# 第254单元源码路线与依赖

本路线只说明作者构造。`qualified=false`、`machinePending=true`；未运行 Lean 或服务器检查。

1. 唯一新公共接口来自 `freeze-01/FROZEN-HEAD.txt`：固定512，当前 y≥1 及原窗口，且比较 z 保持全实。冻结 preamble/head/closing 原字节不改。历史描述164LF已由冻结 COUNT-PROVENANCE 更正为旧165LF、新167LF，本源使用新167LF原字节。
2. 在任何 n/y/ε之前，仅调用253的 `actual_original_level_dependent_countably_generated_model.{u,0,0}` 一次。它给同一 m₀、trim μ₀、21个core、所有有限目标观测的 map 律，以及每个合法当前层级的251/252完整包。253源00c05d34、合格证3331f3b3、最终独审cc0a0eb8/ddc80248原样复用，没有重检旧生产者。
3. μ₀上的投影/残差/尺度先明确命名 g₀/r₀/v₀/rho₀。core提供逐点函数等式，故当前251包的承重 D1、D2、Tclip、Z0 和真实 E_i 可逐项显式改写到冻结外层 g/r/rho。不能把旧固定层级统计包当作当前层级接口。
4. 先用有限 J=(Fin n) 的一般 hfiniteLaw 运输当前 Tclip。坐标eval保测与产品律给独立；积分推前给每个 g/√n 的均值0、二矩1/n和总能量1；有限和/平方恒等式给 W/V/Q/T0 精确识别。没有新矩前提。
5. 由当前 global-half 得 1+D2>0，直接调用已接受 ambient canonical consumer。它的条件不依赖 clipping 层级。边缘律等式统一其实际 ν/q/c/ξ/Y/η/C 与冻结定义；全/retained Borel因子、归一 η 独立/无原子/矩、signed恒等式和比较结果完整保留。
6. 当前 E_i 三元组由保留增广观测的第一投影得到三个实可测分量，再由同一 retained scalar factor 分别编码并组成 Borel Fdel。删除量维持原 n 的系数和真实当前 Bdelete，不含被删坐标或好集指示。
7. 对任意实 z 和五种 R，正原分母上逐点比较等价；等号单独双向处理。所有差异仅落在原投影零事件 Z0，其 P/P₀/ν 法则给 p0 误差。不存在尾原子连续性假设，也没有用编码后 Vη>0 推出原物理分母处处正。

完整来源范围按只读 p51 S1–S5/S20–S27 与 p54修正。Root v149 衔接审查强调当前 B_y 的必要性；固定clip1三次费用的二点反例是该审查的普通数学输入，不是本单元新增形式证据。Shao–Zhou命名外部输入归属保留。

当前单元不消费252的 weighted/correction极限输出；该完整第二包在253中存在，但冻结254只要求第一包中的可测、全局半正和删除因子。下一 source-bound 依赖是当前层级完整 weighted-integral/source-law consumer，结合真实 correction包、严格预算和实际 upper-events；physical付款/CDF/relative tail/DC/fullOQ56仍 OPEN。

库存材料：SOURCE-INVENTORY.json/md给每个let/letI/have的完整类型、完整右端、词法可见范围和UTF8切片；PRODUCER-BINDINGS.json与INTRO-AND-DESTRUCTURING-INVENTORY.md给全部intro/rcases等绑定的完整依赖类型；PRODUCER-TYPES.json保留完整承重接口与实例化。它们均为源码层材料，实际编译owner计数为null直到服务器。
