# unit252 实际源码承重路径

精确源码 `OriginalLevelDependentCorrectionEnvelope.lean`：10857B、201LF，SHA256 `fc91fdfe3a92b472deba8ecea7183c62381643524d9cf875a3e594c649782020`。

| 源码行 | 实际依赖／本件推导 | 保留范围 |
| --- | --- | --- |
| 17–92 | freeze-01 完整声明与24个冻结let | 同一原 μ、h、n≥4、当前 z≥1、原倾斜窗口、全部原 RHS／量词 |
| 95–107 | 定义引入、局部乘积概率实例、常数非负和 n>0 | 没有新增数学前提 |
| 108–110 | `actual_original_clipped_cost_integrability` | 仅原 D／Ddelete 的 L²、J／Jdelete 和 A／Adelete 的无权可积；固定1的 B／e 结果全部丢弃 |
| 111–114 | qualified251 `actual_original_level_dependent_clipped_source_package` | 当前 B／e 可测、当前 e 的绝对值不超过 B、完整删除观测结果；没有使用 weighted test 推无权可积 |
| 115–139 | 当前 B／删除 B 定义、原 J／删除 J；真实 clipped 契约 | 原 (n−2)² 和当前 z 保持；得到当前预算与 e 的无权可积及所有非负契约 |
| 140–146 | `actual_quadratic_source_moments`，仅辅助 level0 | 原 g 可测／L²／均值0／二阶矩1；不保留或重建额外倾斜费用 |
| 147–171 | 原 P=μ^n 的坐标保测与积分拉回 | 真实 ξ0_i=g_i/√n 可测／L²／均值0、二阶矩1/n、总能量1 |
| 172–176 | 原 projectionEnergy／projectionV 定义 | 逐样本 V=projectionV n g，无替代 Studentizer |
| 177–184 | `literal_deleted_remainder_envelope_spec` | 同一 P、ξ0、当前 B／Bdelete 和 z；H／Hdelete／M／Mdelete／κ 全部定义相同 |
| 185–197 | 完整结论组装，generic Δ 精确取 A／Adelete | 所有实 ε 的积分恒等式、真实抵消差的 L¹界及 ε→0；非负性仅在 ε≥0 分支 |

原文承重范围为 p51 S22／S23 的 signed 精确阈值校正与 S24／S25 的二阶包络机制；p54 条件 p 矩及实际上尾付款修正保留。命名外部结果继续归属于 Shao–Zhou，不新增外部来源结论。

本件所补缺口是当前层级 coded scalar source-law 消费者所需的原无权 A／B／删除量可积性、原坐标总能量和 literal H／删除 H 的纠正 L¹包络。下一依赖是同当前层级的可数可观测因子、增广编码及真实加权 source-law 组装。本件没有执行 scalar coding、source external SZ、physical-event 付款、CDF、relative tail、DC 或 OQ56 根闭合。

旧 qualified251、其原始对象和旧 producer 的机器证据只按精确字节复用。本件候选独立审查和指定服务器首次核验待做；作者没有执行 Lean 或远程操作，`qualified=false`，`fullOQ56=OPEN`。
