# 修复01 受影响主 API 与证据来源

旧 `source-review-01/API-SOURCE-TRACE.md`、`INTERFACE-CONSUMPTION.json` 和完整阅读覆盖均在本次 193 输入中精确核验。176 的完整实际公共 TYPE（237079B，2201 显示行／2200LF，SHA256 `fb0aa27d11246907aa1f47eb8be5f351bcf7629a584fe955a2b5a4053216b905`）及 278 三个完整 TYPE／FULLVALUE 的已有阅读保持有效；没有重复旧 producer 证明或检查。

T02 当前 263–287 的同一 176 调用消费关系，连同 288–369 的 η／Πη／ν-a.e. 传递和实际负坏尾均值，已经在完整当前 T02 证明中重审。旧型的全局前提、r 定义、截断 ν、w 的 L2／平方积分和原行积分事实都没有变化。T03／T05 的旧证据仅按精确相同组件复用。

新提供的固定主源是 `parent-api-05/Mathlib/MeasureTheory/Measure/CompleteLattice.lean`，SHA256 `cb882927c13e87912b7734a22b318dbc5a9c707359067b978f3dbc40ad2c0a39`，10229B；绑定 JSON SHA256 `e212d0af3fa81a266053f52bfa50e0f1af4e80aa587fdeb6089b3be8fa5821f8`。固定 mathlib 提交 `807d3836b165983210ee2ecf3cd28f239436949c`。完整源 1–245 已读，含实际 namespace `MeasureTheory.Measure` 和变量环境。225–228 的完整 HEAD/body 是 `measure_univ_eq_zero : μ univ=0 ↔ μ=0`，没有有限、概率、非空或集合可测前提。T04 在完整零因子测度上用 `.mp`，方向正确；非空性只用于后续选一个乘积零因子。

T01 受影响部分重新对读以下原固定主源：

- `L1Space/Integrable.lean` 403–445：完整 integrable_zero、Integrable.add 和原通用有限和接口的定义环境；另复核 449–453、1023–1035 的原运算环境。当前局部归纳直接消费同一行可积性与 Integrable.add。
- `BigOperators/Group/Finset/Basic.lean` 27–57：实际有限和插入接口由 prod_insert 的 to_additive 生成，需 hi:i∉s，当前归纳步明确供给。
- `MeasureTheory/Group/Arithmetic.lean` 797–834：完整有限和可测接口的生成源及交换幺半群／可测运算环境；显式实值行函数与目标相同。

有限集归纳、函数逐点加法和定义展开只作用在原有限指标与实值函数上；没有建立新全局 helper 或改动数学类型。其余平方积分、积分线性、Pi、cond 与 AC 的完整旧来源上下文继续精确复用，并在完整变更证明中核对前提用途。所有实际编译／类型实例接受情况留待新的服务器 native；本轮没有 API probe 或新机器清单声明。
