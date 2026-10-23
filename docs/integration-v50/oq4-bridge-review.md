# Real-threshold Bridge v6 最终独立审查

结论：**CORRECT_FINAL_SOURCE_ACTUAL_INTERFACE_AXIOMS**。

本票绑定 Source `644f10f118e2765a346cf64e47e6637ce97f23b292a377c43ec06620318a0df2`（13,659 bytes，394 个逻辑行，末行无换行），范围仅为实阈值 Bridge T1–T5。独立的完整 Source 证明覆盖、全部实际声明接口、成功的服务器内核检查和递归公理证据现已关联闭合。OQ4 原始 root、定量概率/log、谱与 energy 根仍 **OPEN**；rawleaf 增量为 0。本票没有执行集成或新的 Lean 检查。

## 证据和复用边界

- 冻结数学契约 SHA256 `08e8756d0d591408f4fe5a7755c2a01d0c20274d022ef99a1da5a1da44fadc72`；冻结 public 27 声明 SHA256 `641c4651cca31de11590f873e6a8c82dcff3c1c1b71bccc98c620620e67b2a50`。
- 直接复用同一独立审查上下文的 v6 完整 Source 票：report `8801ee04d9bedcb7d6f569e69f5f4e081ae4b686c4cea4be478f9f33bc1a653b`，receipt `60eaed3c4883512dfe241dcd66bdb41b3e624ec1531267f0797b79ecc0e62ae6`。它以旧 Source `8f808c5e04c5ebab40b91ab083a69f53035dbba09f4fa901119119e6edb13e34` 的 qualified 完整审查覆盖 324 个不变行/11,269 bytes，并完整新审四个改变的证明，70 行/2,390 bytes；合为当前全部 394 行/13,659 bytes。35 个 Source 声明头和 7 个值及冻结接口均已核对。本次不重审这些不变证明。
- 本次完整阅读 `owned-interface.txt` 全 521 行的 **53 个完整实际类型、7 个完整定义值**。文件 SHA256 `8e652df2c7275f3340e94eeb439a033eb1a5a31ebf0afe5d7bca33b09d5a0336`，28,845 bytes。其全部正文逐字对应 audit 的显式类型/值打印；重建文本只在最后额外空行处不同，没有表达式差异。
- `raw-expressions.json` SHA256 `1665b8a70e55611293cc3690ee73702b641f60943f08626eb687e8a883dd439f`，147,579 bytes；53 个 raw 类型与 7 个 raw 定义值全量解析，类型/值常量引用分别与 audit 完全一致，无 free/meta 变量。语义阅读使用上述完整显式表达式，未把 raw 引用计数当作类型语义审查。
- `audit-native.json` SHA256 `52290e5673953e3d4b181abb8e2be7f262515d310ed5bb4a0d046f55fb0402fd`，13,272,803 bytes；全量结构化核验，无大依赖图抽样。

## 全部实际接口

实际集合为 **27 public + 8 明写 private + 18 generated = 53**，即 7 definitions + 46 theorems，0 owned opaque。53 个名字与 unfiltered environmentDifference、moduleOwnership、stage2 及 raw 导出集合完全相等，均归属于 `Shao.OQ4.RademacherRealThresholdBridge`；无漏项、重名替代、别的模块声明混入。receipt 保存全部 53 个完整实际名字。

七个值逐一核对：`pathMeasure N` 是固定 `RademacherCosine.law` 的 Fin N 实坐标乘积测度；`weakEvent`/`strictEvent` 正好量化 Nat j 的 `1 ≤ j ≤ N` 和同一个 `|prefixSum a j|`，比较符分别为 ≤/<；两个 probability 正好是该测度对对应事件的 `Measure.real`；`weakIndex` 是 Int.floor，`strictIndex` 是 **Int.ceil h − (1 : Int)**。实际类型中的乘积 Borel 可测结构和全部实例均与 Source 含义一致，未引入不同空间或替换概率。

20 个 public theorem 全量对冻结和 Source 核对如下：

| 实际 public theorem | 完整参数/结论语义核对 |
|---|---|
| measurableSet_weakEvent, measurableSet_strictEvent | 任意 N、实数 t，无额外阈值或正时间假设。 |
| ae_coordinates_sign | 任意 N，在同一 pathMeasure 下几乎处处所有 Fin N 坐标为 −1 或 1。 |
| ae_prefixSum_integer | 任意 N，几乎处处对每个 1≤j≤N 的和存在 Int z，实数和等于 z 的实嵌入。 |
| weakIndex_one_le | h≥1 得到 Int 的 1≤floor h。 |
| weakEvent_ae_floor, weakProbability_eq_floor | h≥1，前者是 AE 的事件等价，后者是实际 real 概率等式；使用同一 N 和 floor 的实嵌入。 |
| weakEvent_eq_closedStrip | t≥0 时的逐点集合等式，含 j=0 的 closedStrip；没有把 AE 等价升级为逐点等价。 |
| strictIndex_nonneg, strictIndex_one | h≥1 时 Int ceil h−1≥0；h=1 时该 Int 值为 0。 |
| strictEvent_ae_ceil_sub_one, strictProbability_eq_ceil_sub_one | h≥1，严格事件转为弱事件，阈值是 Int ceil h−1 的实嵌入；事件结论仅为 AE。 |
| strictEvent_ae_weak_of_noninteger, strictProbability_eq_weak_of_noninteger | 原 h≥1 和“没有 Int z 使 h=(z:ℝ)”前提均保留；同一 h 的严格/弱事件 AE 等价及概率相等。 |
| strictEvent_ae_integer, strictProbability_eq_integer | Int k≥1，严格实阈值 (k:ℝ) 转为弱实阈值 (k:ℝ)−1；无 Nat 截断。 |
| weakProbability_zero_time, strictProbability_zero_time | 对任意实数 t，N=0 的概率为 1；没有暗加 t≥0。 |
| strictProbability_one, weakProbability_zero | N≥1 时，严格阈值 1 或弱阈值 0 的实际概率为 0。 |

8 个 private 完整实际类型也逐一核对：`measurableSet_sign`、`ae_law_sign` 使用相同实 Borel 空间/固定 law；`prefixSum_integer_of_sign` 正确保留全坐标 sign 前提；两个 `intCast_*_iff` 对任意 Int q 和实数 h，分别是 q≤h 与 q≤floor h、q<h 与 q≤ceil h−1 的等价；`real_eq_of_ae_membership_iff` 使用同一 N/测度和 AE 成员等价；`prefixSum_one_eq_zero_coordinate` 保留 i0:Fin N、i0.val=0；`pathMeasure_isProbabilityMeasure` 对所有 N 成立。无额外假设被藏入 public 类型，也无未经证明的 instance。

18 个 generated 的完整类型全部新读，逐一覆盖：

- 4 个 `.eq_1`：pathMeasure、strictEvent、strictIndex、weakEvent 的精确展开等式。没有加强数学结论。
- 5 个 `_simp`：strictProbability_one 的双重否定等式；private measurableSet_sign 的 Or 交换等式；private prefixSum_one_eq_zero_coordinate 的 filter/univ/singleton 成员等式。类型中的隐式命题、Type 宇宙、DecidablePred/Fintype 参数均为相应通用库事实所需参数。
- 9 个 `_proof`：strictProbability_one 的 2 个 Nat 矛盾；两个 zero_time 的 `1≤j≤0` 矛盾；weakEvent_eq_closedStrip 的 j≠0 与 ¬1≤j 矛盾；weakProbability_zero 的 ¬1≤1 矛盾；private intCast_lt_ceil_sub_one_iff 的 2 个 Int 离散序矛盾；private prefixSum_one_eq_zero_coordinate 的 Fin 索引值唯一性矛盾。所有量词和局部前提均读全，前提确实足以推出 False，无无条件 False、额外数学假设或隐藏前提替换。

## 内核、公理与完整导入绑定

保存的唯一 v6 Native 调用 exit=0（约 7.22446 秒），audit 为 `NATIVE_MACHINE_PASS`，`skipKernelTC=false`、`autoImplicit=false`、trustLevel=1025。Source SHA 与保存的 result/source-own 指纹及本机当前文件一致；冻结声明、audit、显式接口和 raw 表达式的 SHA 链一致。5 条 warning 不改变声明或内核成功；没有 error。这里复用已有服务器结果，本次没有编译。

对完整 21,557 节点逐个核验字段、类型引用和值引用，共 485,389 条边：53 个 owned 的可达集合恰好等于闭包，无 dangling refs、缺失节点、空 owner；所有非主模块 owner 均在实际导入集合。所有节点 unsafe=false、partial=false；所有 theorem/definition/opaque 的值可取，导入闭包内 21 个 opaque 的值也已纳入审计。无 sorryAx/ofReduceBool/native_decide 引用。闭包仅有 3 个 axiom 节点：`propext`、`Classical.choice`、`Quot.sound`。对每个 owned 独立遍历其类型和值引用重算 AX，53/53 与记录一致，白名单外公理为 0。

补证 receipt `eecc4fb4ddb3cf1f9b43eb7f35ef7f98347f0505390e7f4b084581614935fa27` 与 import map `32f1f5b42a959000e280cf8391d6fc865acea096d846d1d8a02d1815f7fbb097` 已校验。独立集合运算确认 **4,476 actual imports = 4,313 原 frozen imports ⊔ 163 supplemental imports**：没有原项缺失或交集；163 项全为固定 Lean 4.36.0-rc1 工具链中的 Init 161、Lake 2。每项 actual findOLean raw、首选路径、resolved、SHA256 和目标 identity 均与保存的完整差集原始采样一致，路径均精确位于固定只读工具链 lib/lean。无新增 Shao、第三方包或未知对象；812 个闭包导入 owner 均已绑定。

原 4,313 对象的 before/pre/post 同表指纹 `c4a94b6521506ec4fe9b3cfb48b38f14c9c48ac00567ba37ba4c6fba84316a8c`、11 个 actual project aliases 对已接受 original 的绑定复用保存的 guard 证据。`result-guard-summary.json` SHA256 `34033f7c30b115b33e003fd14d100be199a4f5050d67ef012079285b3892cf0d`，完整差集 receipt SHA256 `b9ca341b849ee31ba16bab1384c09e8e4f3b0fdc2c792de90e25466bdb116267` 均实核。

**时间信任边界：**新增 163 项只有既存调用后 findOLean 采集的对象指纹，原 before/pre/post 表中没有它们。本票没有虚称其存在初始前阶段哈希；其初始信任来自 root 已固定版本、只读工具链契约，随后采样完成实际路径/字节关联。这项证据边界不影响已成功的同源内核/AX 结果；按当前 streamlined-acceptance 规则补齐元数据即可。

原 Python wrapper exit=1 的记录 `failure-receipt-v6.json`（SHA256 `d650629926b59ad9c0c6da1b14f5b5cedddebce97cddcbb57b530ebbae07f450`）保持原样：失败原因是最初 frozen 导入图没有 Init；其 ordinary_mechanical_PASS=false 没有改写为 true。本最终票评估的是成功内核/AX 加完整后续绑定证据，不把原包装器历史重标为成功。

审查者与作者分离。仅本机文件读取、确定性解析/哈希及本目录报告写入；没有修改 Source、他人/共享文件，没有服务器、Lean、Git、网络、委派或 W 写入。无待补的本范围数学接口或公理缺口。完成 report/receipt 全文读回及哈希后 STOP。
