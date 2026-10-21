# U4 最终独立源语义、声明与证明审查

STATUS: CORRECT

独立 reviewer：OQ3 reviewer，gpt-6.1-sol xhigh。仅拥有本报告，不修改任何实现、scope 或其他文件，不再委派；不读作者 inverse-tilt-api、notes 或 frontier。

裁决绑定指定哈希的 174 行实现，覆盖两定义、十三个公开目标、全部局部辅助和两项生成证明。实际声明与冻结 scope 一致，源语义忠实、完整证明无关键缺口，真实服务器已有成功构建/传递公理证据相符。只认证无限逆倾斜原律 P 单元，不关闭有限阶段、正 KL、鞍点唯一性、联合非格点、LLT、对角或根 A/B/C/D。

## 第一阶段：实际声明的独立翻译

本节在本轮读取实际证明、scope 内容、真实源锚点及作者 receipt/Audit 之前落盘，仅读取两定义与十三个实际目标签名。`InverseTilt.lean` 为 174 行，实际 SHA256 为 `b2febe8e52d87bce3a1599a7d1c7b335f8c40b7b96f72e5c00bf43c29099a48d`，与委派值相同。前序独立声明审查上下文存在，本轮以实际声明重建语义。

记 `π_w=atomicMeasure w`、`Y(x)=8x−x²`、`β=4+√10`。实际定义 20–21 是实归一化积分 `Z=∫exp(−ellY)dπ_w`；23–24 是实轴测度 `P=π_w.tilted(x↦−ellY(x))`。既有原始库定义已独立核实：tilted 按指数权重除同一真实指数积分作 withDensity。定义本身总化，真正概率、可积性与正 Z 由明确目标准备。

| 实际目标及行号 | 精确自然语言语义与量词 |
| --- | --- |
| `integrable_continuous_of_fixed_bounds`，26–28 | 任意实线概率 μ，若几乎处处 `|x|≤β`，则任意连续实函数 f 对 μ 可积。概率与紧界均为明确条件。 |
| `inverseExp_integrable`，36–38 | 任意实 ell、非负且真实 HasSum w 1 的 w，逆倾斜指数对 π_w 可积；ell 不限符号。 |
| `inverseNormalizer_pos`，45–47 | 同样条件，实际实积分 Z 严格正。 |
| `originalMeasure_isProbabilityMeasure`，51–53 | 同样条件，实际逆倾斜测度 P 为概率测度。 |
| `originalMeasure_ae_bounds`，57–58 | 对任意实 ell 和任意实 w，P 几乎处处 `1≤|x|≤β`，不在该无条件版本中承诺概率或 Z 正。 |
| `originalMeasure_integrable_id`，62–64 | 非负真实概率质量门下，恒等函数 x 对 P 可积。 |
| `originalMeasure_singleton`，69–72 | 对每个完整原子索引 i，在相同概率质量门下，实际实轴单点的扩展非负质量为 `ofReal(w_i exp(−ellY(a_i))/Z)`。w 与 Z 在公式中必须是同一对参数。 |
| `originalMeasure_real_singleton`，80–83 | 同一门下，实单点质量等于该归一化实比值。 |
| `originalMeasure_atom_pos`，88–90 | 同一门加该项 w_i>0，则其 P 实单点质量严格正；不要求其他项也严格正。 |
| `originalMeasure_centered`，94–99 | 任意实 ell,q、非负 w，若四特征真实 HasSum 为 `(1,0,0,q)`，则 x 对 P 可积，且实际积分为 0。质量 HasSum 1 可由第 0 坐标取得；第三特征提供的是逆倾斜中心化矩。 |
| `originalMeasure_retilt`，116–118 | 非负真实概率质量门下，以正对数权重 ellY 再倾斜 P，完整测度精确返回 π_w。 |
| `originalMeasure_forward_normalizer`，129–133 | 同一门下，正向指数 exp(ellY) 对 P 可积，实际积分为 Z⁻¹。 |
| `exists_source_original_family`，149–160 | 无调用方前提，先取同一 p>0、q∈(1,103/100)、eps>0 和源旧矩方程；然后对每条严格正可求和且总量<eps 的整条 r，给同一实际 P 的概率性、x 可积且均值 0、所有指定原子的正实质量、AE 支撑界和精确再倾斜至对应 π。p/q/eps 在所有 r/J/n 之前，所有结论使用同一 r。 |

当前只覆盖无限源原律 P。没有有限阶段律、独立样本、正 KL、鞍点唯一性、概率联合非格点、LLT、对角或根 A/B/C/D 闭合声明。

## 第二阶段：冻结与真实源对照

盲译先落盘后，独立空白归一化比较确认两定义、十三个实际目标签名与冻结 scope 完全相同，没有前提、类型或量词变化。实际 scope SHA256 为 `dc793b872b31118dba4ae1bd85c5cf2f4f5b24007c7e3749c3034552f4720b56`；此前独立声明报告 SHA256 为 `3f1ffdd44edbd2cc7dba4d35cda179222a70572c12228c928dc9665d040b82ae`，与委派值相同。

本轮实际重新读取真实只读 R1 89–108、127–145 行；实际源 SHA256 为 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。

| R1 锚点 | 实际实现覆盖与边界 |
| --- | --- |
| 89–108 | 四维目标与特征顺序不变。第 0 坐标给 π 真实总质量 1，第 2 坐标为逆倾斜中心化特征，不是 π 的均值。 |
| 127–130 | 源固定无限 π 及其矩由前序 U3a/U3b 提供；当前同一 w 定义同一 Z 和 P，无额外源假设。 |
| 132–135 | 最终族先取同一 p/q/eps，再消费以后任意合格整条 r；并未选择随样本量 n 或阶段 J 变化的原律。逐 witness 递归选尾仍在范围外。 |
| 137–140 | 原始库 tilted 对数参数 −ellY 给密度 `exp(−ellY)/Z`；实轴 singleton 两个版本与原律公式精确一致，归一化常数与同一 w 绑定。 |
| 142–143 | 原律 P 的恒等函数真实可积且均值零，每个正原子在 P 下仍正，且有 AE 支撑界。没有提前输出独立样本或 V_n>0。 |
| 144–145 | 正向对数参数 ellY 恒等于源 `8ell x−ell x²`，完整测度再倾斜精确返回同一 π。 |

## 第三阶段：完整证明与辅助项审查

完整阅读固定哈希实现 1–174 行后，在读取 receipt、Audit 或真实 build 日志之前形成独立数学判断：CORRECT，未发现关键缺口。没有读取作者 inverse-tilt-api、notes 或 frontier。原始固定 Mathlib tilted 定义与主要条件在前序独立声明审查中已经只读核实，当前按实际调用逐项核对。

| 实现行 | 全步骤、条件与边界检查 |
| --- | --- |
| 29–34 | 连续 f 在紧区间 `[-β,β]` 的范数有有限界 C；全局连续性给 AE 强可测，概率测度给有限总量。`abs_le.mp` 把明确 AE 绝对值界送入该紧区间，满足 `Integrable.of_bound`，并未假定连续函数在任意支撑上可积。 |
| 39–43 | 由非负 w 与真实 HasSum=1 安装前序实际 π 概率性，继承所有原子的 AE 上界；`exp(−ellY)` 是全局连续实函数，所以可积桥对任意实 ell 成立。没有误用 U3a 仅对 ell≥0 的统一新增特征界。 |
| 48–49 | 同一 π 概率性给非零测度，`integral_exp_pos` 消费刚证真实指数可积，故 Z 严格正。不是从指数非负或总化零积分推正；指数处处严格正。 |
| 54–55 | π 的非零概率性与真实逆指数可积满足 `isProbabilityMeasure_tilted` 条件，得到真正原律概率；未落在 tilted 不可积时的总化零测度分支。 |
| 59–60 | 原始库 `tilted_absolutelyContinuous` 无条件成立，将 π 的 AE 双侧支撑界传给 P。此目标在任意有符号/不可求和 w 的总化情况下只断言支撑，不声称概率或正 Z。 |
| 65–67 | P 的已证概率性、AE 上界与连续 identity 调用同一紧支撑桥，给真实 x 可积。 |
| 73–78 | π 概率性提供有限/SFinite 测度；对实际实轴 singleton 使用 tilted 的真实密度积分公式，再由 integral_singleton 与 U3b 精确实单点质量取值。ring 只重排 `w_i·exp/Z`；展开 inverseNormalizer 后分母正是同一 ell,w 的 Z。没有借索引空间质量替换实轴 singleton。 |
| 84–86 | 由扩展单点公式转为实数；hw、指数正性与已证 Z>0 保证比值非负，合法使用 toReal_ofReal。单项是有限实数，没有将 ENNReal.top 转实数为零的误用。 |
| 91–92 | 该项 w_i>0、指数处处正及同一 Z>0 给严格正比值；一般零权重没有被声称为正。 |
| 100–104 | hm 第 0 坐标精确给真实 HasSum w 1；hm 第 2 坐标经已审查 U3b 给实际 `∫centeringFeature=0`，其可积性已包含在该前序结论中。没有用 π 的均值 q/4 冒充此中心化特征。 |
| 105–114 | 先独立给 P 下 x 的 Integrable。tilted 积分公式变为 π 下 `exp(−ellY)x/Z`；点态 ring 等式精确改写为 centeringFeature/Z，再以积分除常数与真实中心化矩得零。P 的概率/可积门已由 hmass 与先前证明消去，不是在总化积分分支得到虚假的零。 |
| 119–127 | 再倾斜前明确提供 π 概率性和逆指数真实可积；`hneg` 精确证明负对数权重的相反函数为 +ellY。库 `tilted_neg_same` 的条件全部满足，返回完整 π，而非一般非概率 μ 的归一化版本。 |
| 134–140 | 明确 π、P 两个概率实例；固定支撑上的连续正向指数给 P 下真实 Integrable，任意实 ell（含 0、负）均成立。 |
| 141–147 | `integral_exp_tilted` 化为 π 下两个对数权重之和的指数积分除 Z。局部 hzero 逐点证明该和为零，所以分子是概率 π 下的 ∫1=1，目标为 Z⁻¹。可积性已在前一分支独立给出，未用总化公式冒充指数矩存在。 |
| 161–171 | 一次取前序 U3a 的 p/q/eps 和 hfamily，输出见证后才引入任意整条 r。得到该 r 的全索引正质量/四 HasSum，导出非负与真实总质量 1；P 概率、centered、每原子正质量、AE 界及再倾斜全部由同一 w 组合。没有分别选择不同 r、Z 或 p/q/eps。 |

无额外顶层私有引理；全部局部辅助（hmass、hc、hfun、hneg、hzero、hpos）和组合项均已审查。证明仅使用已独立通过的 U1/U2/U3a/U3b 精确接口，没有加强或删减冻结假设。

### 特别边界与外部 tilted 语义

固定库 `Measure.tilted` 是以 `ofReal(exp f/∫exp f)` 作 withDensity。原始库的不可积零分支不能给本单元概率结论；当前先真实证明所有所需指数可积与 Z>0，并明确 π 为非零概率。库的无条件绝对连续性仅用于一般 AE 支撑目标，适用范围正确。

ell=0 时逆指数为 1、Z=1，P=π，前向归一化也为 1；一般负 ell 仍因连续性与同一紧支撑可积，没有新增指数矩假设。任意带零项的非负概率质量仍满足所有一般结论；严格单点正性只在显式 hi 或 source 的 hpos 下输出。

P 的均值为零来自第三特征；π 的均值仍为 q/4，两个律未交换。当前只构造无限原律 P，不证明有限阶段、独立样本、正 KL、鞍点唯一性、联合非格点、LLT、对角或完整根 A/B/C/D。

## 第四阶段：真实服务器机械证据与绑定回执

在上述独立数学判断写成后才读取 U4 receipt、审计脚本和真实服务器产物。`U4-receipt.json` 实际 SHA256 为 `b7eff53ebfbdf5e4652356423bb98b7bdce962fa27170fc79a6c2807715fd25a`，与委派值相同。依照 SERVER 与 lead 的现有通道授权，用 `tools/server_direct.py` 作一次只读核验；不重复已成功目标构建，不写缓存，也不验收其他未冻结续作文件。

- 实际服务器工作树 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`，分支 `feat/oq3-inverse-tilt`，HEAD `0a2847bd23f06935e25a85867230f3b57368f58a`，与 receipt 执行基线相同。目标当时仍为未提交新文件；该核查不声称最新 main 或整个项目已集成此单元。
- 真实服务器 `InverseTilt.lean` SHA256 为 `b2febe8e52d87bce3a1599a7d1c7b335f8c40b7b96f72e5c00bf43c29099a48d`，与本地审查源相同。核查只指向该目标文件；其他 untracked continuation 不在本报告接受范围内。
- 真实导入源 SHA256：U1 `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0`；U2 `0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d`；U3a `0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b`；U3b `59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39`。均与此前独立 CORRECT 的冻结实现及 receipt 相符。
- 实际只读版本探测：Lean `4.36.0-rc1`，commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`；Lake `5.0.0-src+c9afcdd`；项目 pin `leanprover/lean4:v4.36.0-rc1`，manifest mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。
- receipt 记录实际已执行 `lake env lean -o .lake/build/lib/lean/Shao/OQ3/InverseTilt.olean Shao/OQ3/InverseTilt.lean`，退出码 0。真实服务器 `runs/oq3/u4-20261021/build-02.log` 为空，SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`，与 receipt 相符。
- receipt 记录实际已执行 `lake env lean /root/rivermind-data/shao-lean-20261021/runs/oq3/u4-20261021/Audit.lean`，退出码 0。本地 U4Audit.lean 已完整读取，SHA256 为 `649935d5acc30eef098d7d76cc5d76db1f4b045856a7c04c5453f29ded6c22c8`，与真实服务器审计源相符。真实 Audit.log SHA256 为 `ea4b653b8f885a358eee75571c15487a7bf4f7cc91a5ed8546c2154fc2925552`，完整读取且与 receipt 相符。
- 审计脚本列出十三冻结目标和两定义，确认目标均为 theorem、定义存在；遍历全部十五源名字前缀与 `_private.Shao.OQ3.InverseTilt`，拒绝新增项目公理，并对每项调用 `Lean.collectAxioms`，包含局部辅助与导入 U1/U2/U3a/U3b 的传递依赖。
- 实际日志输出 `U4_FROZEN_THEOREMS 13`、`U4_ALL_THEOREMS 15`、`U4_ALL_DECLARATIONS 17`、`U4_AXIOM_GATE PASS`。两个生成证明 `inverseNormalizer.eq_1` 与 `originalMeasure.eq_1` 也实际列入。全部依赖仅在 `propext`、`Classical.choice`、`Quot.sound` 白名单内。
- 实际源码禁用项扫描为空：无 `sorry`、`admit`、新增 `axiom`、`unsafe` 或 `native_decide`。receipt 绑定的 target、scope、R1、此前独立声明报告、四导入源及机械日志哈希均实际匹配。receipt 的“等待独立 review”是作者检查时历史状态，本报告完成该审查，不回写历史 receipt。

机械覆盖仅限指定固定哈希 U4 的全部冻结目标与其传递依赖。本次另完成源到实际声明忠实性和逐步证明检查；没有重复目标构建，也没有执行根集成构建。前序缓存缺失已由 root 补齐且作者真实构建成功，不再作为本单元未检查的理由；其他分支/根状态不随本报告提升。

JUSTIFICATION: 两定义与十三实际签名精确匹配冻结接口。紧概率支撑的连续可积桥、真实正 Z、实际实轴单点同一 w/Z 归一化、正确第三特征的 P 中心化、任意实 ell 的可积性、双倾斜相消、正向归一化及固定 source p/q/eps 都有完整证明。真实成功构建和传递公理审计绑定同一审查源哈希，无必须修复的关键缺口。有限阶段、正 KL、鞍点唯一性、联合非格点、LLT、对角和根 A/B/C/D 仍 OPEN。

## LF 规范化补充审查

ADDENDUM STATUS: CORRECT

本补充仅更新最终交付字节绑定，保留以上历史数学审查及其原始 CRLF 源信息，不改写原正文。补充前本报告 SHA256 为 `e7d55fd72679efc51ef8720db03bd059a3a045cf6c85416df595057099471670`。

独立实际读取保留的 `InverseTilt-checked-crlf.lean` 和当前 `InverseTilt.lean`，逐字节断言如下，全部通过：

```text
old.replace(b'\r\n', b'\n') == new
old.splitlines() == new.splitlines()
len(old.splitlines()) == len(new.splitlines()) == 174
```

旧文件 SHA256 仍为 `b2febe8e52d87bce3a1599a7d1c7b335f8c40b7b96f72e5c00bf43c29099a48d`，8597 字节、174 个 CRLF；当前规范 LF 文件 SHA256 为 `c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811`，8423 字节、无 CR。差异恰为每行一个 CR 的删除；全部 174 行正文逐字节相同，因此定义、声明、所有证明 token 与原独立审查完全相同，无数学或假设变动。

实际读取新 `U4-receipt-lf.json`，SHA256 为 `49ce12edf4ce0053df7bc9bf2b5ff44dae2658d08170891cc67b77c2bd00b52e`，绑定上述规范 LF 哈希。新回执记录仅重跑该变更 U4 目标：build-03 退出码 0、空日志 SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`；Audit-lf 退出码 0，13 个冻结目标、15 个 theorem、17 个声明及白名单 PASS，日志 SHA256 为 `ea4b653b8f885a358eee75571c15487a7bf4f7cc91a5ed8546c2154fc2925552`，与上文已实际核对的原审计日志完全相同。原 `U4-receipt.json` SHA256 仍为 `b7eff53ebfbdf5e4652356423bb98b7bdce962fa27170fc79a6c2807715fd25a`，历史回执未改。

本补充未再执行 Lean 或拉取服务器日志；独立核验的是本地保留源到规范 LF 源的严格字节等价、新回执及保留旧回执的精确哈希，新的执行状态按上述实际读取的新回执记录。不存在需要重做数学证明审查的变化。

最终 U4 裁决继续为 CORRECT，现同时接受规范 LF 源 `c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811` 与新 LF 回执的绑定。此补充不扩大原数学覆盖范围；根 A/B/C/D 仍 OPEN。
