STATUS: CORRECT

独立最终审阅者：`/root/true_energy_strip_final_review`，新上下文，`gpt-6.1-sol` / `xhigh`。使用 math-theorem；未使用 math-ultra，未参与本模块声明、候选证明或生产证明写作，未修改生产源。此裁决只覆盖下列精确源版本的四个公共头及全部实际归属常量，不是合并裁决，不关闭 C1/C2、joint 或任何原始根目标。

## 精确审阅对象和冻结

- 模块：`Shao.Probability.SourceTrueEnergyStrip`。
- 完整源：`drafts/c12-true-energy-strip-production/SourceTrueEnergyStrip.lean`，75086 字节，1395 行，SHA256 `b935aed89d0c0b0779d657c4790e33d6faf8ba8a550147e72fca2ccb661ff70e`。
- 分支 `author/common-true-energy-strip-v71`；提交 `3f6e879a1b7c17dd24f6d3552866c1704f588f43`；草稿 [PR255](https://github.com/randomcat4/shao-lean/pull/255)。基线为 `3c22f929de772b0d5efbe43d90353b4a415f45e2`。服务器只读检查确认该提交仅新增本文件，提交内源、当前工作树源和成功 check19 源逐字节哈希相同，工作树干净。
- 四头冻结 `candidate-declarations.lean.txt`：`db53109d7f8a72f9f9a079eb53b9efe8557893eb7a4b6a659fd8ec96141fee98`；候选完整数学稿 `proof-candidate.md`：`542f548b00413609bba784d7cbb9799699705d51c01742d46d4b171497453895`；公共声明冻结 `coordination/public-true-energy-strip-declaration-freeze.md`：`18a6165d203a32eb9424d3aa864f6d4952bc6242e1a979260def4ae2ea063238`。
- 已完整读候选稿、四个冻结头及其所有 let 值。独立文本比较确认 4 公共头与 21 私有源头全部与各自冻结一致，仅忽略空白，不重解释前提。四份私有头冻结及逐项比较、各自哈希见 `drafts/c12-true-energy-strip-final-review/coverage.json`。最终作者 `header-comparison.json` SHA256 为 `546f04604fc6f14333c275bc910ff2123ddbf6eff05eb0e272cacc19519088d6`，已绑定最终源；早先比较记录的旧源哈希缺口已仅通过机械元数据更新关闭，数学源未变，未重编。

## 原文到形式陈述

完整读原文 `C:/game/shao/current/c12/supplement.tex` 4028–4190 行的 SM、AC、ordinary、BS 四项及其全部证明；另读 `main.tex` 150–185、233–244、1077–1109 和 1251–1265 行。原文主假设是 iid、零均值、有限正二阶矩；更高矩只是另行标记的其他定理条件，未导入本模块。

原文快照哈希：supplement `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`；main `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`。

基础定义逐项核对：`Path n = Fin n → ℝ`；`prefixSum` 是真实前缀和；`energy` 是真实坐标平方和；`maxWithZero` 是包含时刻零的前缀最大值；`F(z)=z² min(|z|,1)`；`truncationBudget nu n 0=n∫F dnu`；Spitzer 的 head/tail 是真实首尾坐标。两条 raw 头的 `scale=sqrt(n∫z² dnu)`、`eta=map(z/scale) nu`、`R=truncationBudget eta n 0` 与原文 `R_n(0)` 完全对应，未将实际平方和换成方差。

SM 和 AC 原文允许独立非同分布；本模块明确只证明 iid 专门化，适合原文前缀消费者，未声称实现其完整非 iid 版本。BS 头形式化的是确定非负外部能量 q 的一致界；随机独立外部能量、固定完整后缀和反射版可由后续消费者利用此一致性，但这些尚未导出为本模块额外公共定理。`main.tex` 1258–1261 的低能量指数界和 C2 结论也不在本模块裁决内。

四个公共头没有原分布三阶/四阶矩、有界支撑、对称、密度、无原子、非格点、样本能量为正、目标浓度或 C1 比较前提。常数的存在量词在分布、n、区间、能量及阈值之前；SM 固定系数保持 `2*(b-a)+80R`，未放宽。

## 全部生产证明审阅

已逐字全文读 `SourceTrueEnergyStrip.lean` 第 1–1395 行，包含每一个新增私有证明和最后四个公共证明。没有用机器内核成功替代源码证明审阅。下述行号均指该精确源。

1. **普通闭生存，第 14–246 行。** 小 R 分支只对真实截断条件律 rho 使用已接受的非零漂移有限闭生存定理。完整核对所调用的 `sourceTruncation_law_data`、paid moments、variance、gamma、original CDF pullback 和 `iid_closed_survival_nonzero_drift` 的输入输出头：rho 的三阶矩是截断后导出的，未要求原律三阶矩。由 `n|mu|≤1/8`、`nV≥1/2` 得漂移比至多 1/4；分母至少 1/2、中心三阶项至多 32R、指数项至多 exp(1) 都以正分母/非负因子支付。保留事件 N 的真实乘积条件律给出 `P_rho(A)*p=P_original(N∩A)`，再分解 A 与 N，补集至多 `R/e³`；没有假设 A 与 N 独立。大 R 分支由概率至多一支付。双符号结论通过 `map(z↦s*z)` 的真实 iid 产品输运，二阶矩、均值和 F 都逐项保持，未假定分布对称。u=0 的闭纪录原子未删除。

2. **截断平方、零替换与 SM，第 249–621 行。** 截断 A(z) 在 d² 内有界，从原二阶可积获得所需 L² 和截断四阶可积；真实独立产品的方差相加给出 `Var(U)≤d²` 和 `≤dR`，不是原律四阶矩假设。零替换的 H_i^0 显式由除 i 外的所有坐标重构，因此与 Z_i 独立。全局强单调输入对正负 z 分别给出正确方向；clip 步骤保证乘积总非负，闭区间和 `|z|≤d` 内至少 z²，包括端点和 z=0。所有积分乘积因 f 有界及坐标 L² 而可积，零均值独立项积分严格为零。真实和 S 的二阶矩为一，`E|S|≤1` 由平方不等式直接积分证明。最终证明用 `I(m-1/4)-(U-m)²≤IU` 包装方差损失，得 `P(E)/2-Var(U)≤E[IU]`，再代入 d=4R、R<1/16。它与原稿 Chebyshev 分解等价地支付目标，且余量严格足以保持冻结的 80R；R 大分支和 R>0 都已支付。

3. **外部能量浓度，第 624–974 行。** 双侧 clamp 的全局 1-Lipschitz 和幅度 1/4 给平方差至多 `|t-s|/2`。floor 至少 1/2 使两平方根之和至少一，代数恒等式得根差仍至多 `|t-s|/2`；这一证明覆盖所有夹断/floor 转折点，无几乎处处导数遗漏。`T=2H` 的坐标强单调性由该差界和 `0≤x≤1` 全局推出。真实统计量与夹断统计量在所有坐标小且实际 Q≥1/2 时完全相等；大坐标并集至多 64R，低实际能量通过截断平方方差支付至多 16R，包含 Q=0。合并得到 160(width+R)。raw 版证明 scale>0，完整导出 eta 的概率律、二阶可积、零均值、总二阶归一化及真实有限乘积映射；平方根正尺度齐次和区间两端缩放完全一致。q=0、x=0/1、a=b 和原子均保留。

4. **反转、生存分块和真实能量平方条带，第 977–1393 行。** raw 反转生存先做正尺度归一化再用真实坐标逆序测度保持，不从条件独立猜测反转律。head/tail 的乘积律通过 Fin 的真实互补坐标等价得到，sum 与 energy 分割均为逐路径恒等式；所有逆序前缀索引覆盖 0≤j≤l。原事件中 `S_(n-j)≤wall(v)` 与 `S_n≥wall(v)-u` 在第 1342–1344 行消去同一随机 wall，给出只依尾块的反向下生存 L，没有把随机墙的命中当自然过滤停时。固定完整尾块 c 后，首块仍为原 iid 产品，external q 精确为 `q+energy(c)`，区间为 `[-S(c)-u,-S(c)]`，长度恰为 u。product-section 引理用可积指标的 Fubini 完整积分，不是仅把边际概率相乘。n≥2 时两块严格非空；证明采用 `n≤4j`，由实际归一化预算的 F 单调/三次缩放界得每块因子≤8A，故积≤64*Cac*Cs*A²。此处常数比候选 sqrt3 比较粗，但绝对常数存在的冻结头未变。n=1 单独积分 `z²≤1/4+2F(z)` 得 R≥3/8，再由 `min(1,A²)≥1/8` 和 C≥8 支付概率一。最终 small/large A² 两支保留 literal `min 1`，全零路径和弱闭墙没有被排除。

没有发现关键数学缺口。上述证明只调用已接受依赖的实际接口；原有限生存、Berry–Esseen/Spitzer 等归属保留，不把其已接受证明计为本次新证明或重新独审。

## 实际归属类型、值和公理覆盖

作者审计驱动完整读过，按 `env.getModuleIdxFor?` 的实际 module owner 选择目标，未按 namespace 前缀筛选。该环境 module-local index 为 5084。审计对每个实际 owner 都要求 `.thmInfo`，并递归运行 `Lean.collectAxioms`，只允许 `propext`、`Classical.choice`、`Quot.sound`。结果为 **40 常量/40 定理/0 非定理值**：4 公共源头、21 私有源头和 15 生成定理。全部 40 类型及其递归公理逐项读过，名字集合与审计 JSON 严格相等，逐 owner 名称、源证明范围、生成标志、完整类型哈希、公理和裁决见 `drafts/c12-true-energy-strip-final-review/coverage.json`。非定理值为零由实际环境 kind 门确认，非仅源码关键字统计。

原始完整类型文件 `all-owned-types.txt` 为 117129 字节，SHA256 `e73128ff18ab487c7a15fec7688d0327209a417b828733685a2ce530ed302920`。实际阅读使用 132 项无损字典，逐项完整读取 `type-dictionary.txt`，再完整读取压缩体第 1–12、13–26、27–40 块。字典只重用原始相同括号子串和相同长标识文本片段；保留所有隐式参数、类型类实例、量词、let 值、前提和结论。无省略号、无 summary 替换。对“展示的字典定义+展示的压缩体”递归解码，验证与原始文件逐字节相等，而不只是比较语义。所有字典内容和压缩块均在本次上下文中全文出现并被审读。详见 `type-roundtrip.json`、`coverage.json` 及 `compress-types.py` / `finalize-coverage.py`。

15 个生成类型覆盖：strip 的 `_proof_1` 到 `_proof_7`；external-normalized 的 `_simp_1`；reverse-prefix 的 `_proof_2`、`_simp_1`、`_simp_2`、`_simp_3`；reverse-tail 的 `_proof_1`；small-closed 的 `_simp_1`；product-section 的 `_simp_1`。它们分别为真实索引/自然数关系、集合成员化简、反身序关系或结合律定理，没有额外数学前提。巨大定理机器 proof value 未输出；全部源码证明已全文审读。

## 原成功服务器证据复用

首次完整四头检查是 **check19，kernel rc=0；同次 all-owner recursive AX rc=0**。本次独审新编译次数 0、新 AX 执行次数 0、旧 producer 重编次数 0。全部 Lean 仍只在指定服务器；原收据记录 CPU10–13、`root-heavy.lock`、`-M8192 -j4`。钉死 Lean `leanprover/lean4:v4.36.0-rc1` 和 mathlib `807d3836b165983210ee2ecf3cd28f239436949c` 与服务器实际文件/仓库一致。

机械只读服务器核验已完成，见 `server-artifact-verification.json` 与 `original-import-verification.json`：

| 工件 | SHA256 |
| --- | --- |
| 原 `producer19.olean` | `9a53771d5fa32f66796e591a2de1b1c1b762fba1dec7ae4f94d34a7664725e12` |
| actual-owner 审计 JSON | `128a9b1a20e774634f0fa519077d6c388bfd54d6605fcf27d32a3afc2b480e79` |
| 审计驱动 | `22f179eb642c2a804aa0fb045dd286173797fe939965a2d3005529835a1b5354` |
| 原 kernel 日志 whole19.log | `8a24d0edfefec0362fa04ddacbdd5e5845ede263cfd0b70e7930ebc8181fca97` |
| 原类型/AX 日志 owned19.log | `ae6598168ca2e8aeaf331a75119b552be0e189e1efba4be8b426a85f70ec79f9` |
| 保留失败与成功的 check-index | `3763f495fd66765a37d6b5ebc37c53791920cd64c82990daaf36e3aab5f3bcaa` |
| 整文件 kernel/AX 收据 | `353db26ffcd524910e5861cb8f7b7062de3359243b10a25016e8adc5d86b9557` |

本地源、服务器生产源、check19 归档源、提交内源都匹配前述最终源哈希。服务器 import 路径中的目标 `.olean` 与原 producer19 对象哈希完全相同；原 owned19.log 的 40 个完整类型块与 `all-owned-types.txt` 对应块逐字相等。审计成功、40 种类/完整类型、原对象和冻结源不是互不关联的口头报告。原日志/二进制保留服务器，仅紧凑核验结果本地落盘。禁用语法扫描无 sorry/admit/新 axiom/unsafe/native_decide 命中。check18 及更早失败来源均保留，未被改写为成功。

## 所有权释放及结论范围

作者 `RELEASE.json` SHA256 `a0e449fa5076779f580e63d0e02df44c33242e5973d777c11dad8e64284bbe69` 已完整核对，绑定的 14 个文件逐一哈希/字节数匹配。它明确释放本目标生产源写权给 root，记录原 head/source/object、无旧 writer 复活、本人 Lean/lake 在途为空；父协调员亦已确认作者 writer+execution release。审阅期间源保持不变。

因此本精确版本可以按项目规则复用既有服务器内核/全 owner 公理证据，并携此独立完整 source-to-statement/proof 审阅交 root 接受。四头合计的新增 producer 结论为真实普通闭生存、iid SM 浓度、确定外能量一致浓度和真实能量平方闭条带。共同 completion、overshoot、terminal envelope、endpoint/joint 比较及 C2 根定理仍 OPEN，不由此报告关闭。

本审阅者未持有生产源、共享缓存或集成写权，未启动 Lean/AX 命令。报告完成后释放 `drafts/c12-true-energy-strip-final-review/` 及 `coordination/common-true-energy-strip-full-review.md/.json` 的本次报告写权和全部执行权，执行/写入在途 **0**；具体完成释放记录为报告目录 `RELEASE.json`。模型实际为 gpt-6.1-sol/xhigh；运行时未提供 input、cached input、output、reasoning subset 用量，均记 null，不估算订阅占用。
