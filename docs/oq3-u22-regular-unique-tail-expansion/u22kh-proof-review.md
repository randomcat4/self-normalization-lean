# KH374 独立最终完整审查

STATUS: CORRECT

JUSTIFICATION: 最终 56LF 源码忠实证明冻结的通用分析引理。联合 C3 正则性经两次真实能量偏导构造给出二阶能量导数的联合 C1 正则性；其基点严格正性由连续性扩展到同一个邻域。有限阶 C3 的邻域性质与该正性取交，再用实数乘积的 max 距离及半径减半，得到含边界的统一闭矩形。每个矩形点的切片 C2 由联合 C3 降阶后与仿射切片映射复合获得。所有前提、导数、量词和闭边界均与冻结声明及实际导入 TYPE 一致；未发现关键缺口。判定只覆盖下述精确 helper，不把它认作实际速率的正曲率、全局唯一性或完整 OQ3 的证明。

## 独立性、授权与输入边界

- 审查上下文：`/root/oq3_kh374_final_review`，新的独立最终审查上下文；没有参与该证明的编写或修订，只取得本报告的写权。生产源码、冻结文件、输入 map、其他报告及共享文件均未改动，没有子实例。
- 规定配置：`gpt-6.1-sol` / `xhigh` / fresh。工具不能独立观测实际服务端 model、effort 或 token 细分，故 `actualModel=null`、`actualEffort=null`，`usage={input:null,cachedInput:null,output:null,reasoningSubset:null}`；不从规定配置推造实际计费记录。
- 已完整阅读 math-theorem 的 SKILL、prompt-library、openai-workflow、lean-verification，以及 SERVER、当前 streamlined acceptance。已按最新明确 OQ3 恢复条款、phase40 与 REGISTRY 的 `currentStateSelectionPolicy` 选取权威状态；没有把历史 PAUSED 条款或陈旧顶层字段当作当前状态。
- 当前 Root 为 `01a17d3c-6dfd-7cc0-94ed-35d758a423a5`，OQ3 唯一 owner 为 `01a16c48-80ee-7520-a9d9-faeeb6d05c78`，状态 `ACTIVE_EXPLICITLY_RESUMED_BY_USER`，子上限 1。权威 phase 为 `ROOT_OQ56_OQ3_40`，Root/OQ56/OQ3 各 heavy1、OQ4/C12 heavy0，项目最多3；OQ3 CPU36–39,44–47、历史名 c12-heavy.lock、原生 -M8192 -j4，140/60/180/200GiB 分配与阈值。此审查没有申请或使用 heavy 槽。
- 输入 map `u22kh-review-input-map.json`：SHA256 `8ced18cad044fbaeb5f48b382f3695d456f38f7511a7b3e90995deabaa5296e8`，4713B，145LF。26 行全部逐项独立重算 SHA256 与 bytes，全部吻合；26 个文件内容均已阅读，历史请求仅当作证据读取，没有执行。
- scope `three-hundred-seventy-fourth-unit-scope.md` 已另行全文读：SHA256 `1c4b3b71fcab98032709bad576cae1f49e4e7020e28d823e73085525b7bf8d27`，1731B，7LF。该 scope 的边界明确，没有独立 SOURCE 前审的未覆盖必要风险，也没有因此添加新的前提或流程。

## 精确源、冻结声明与实际 TYPE

最终源码 `u22kh-source.lean` 的 SHA256 为 `b29ebe1b35c27dd0f1400b9bf84ddfd1e33ade28dffd3deff758711086e21a68`，2904B，56LF，无 CR、无 BOM，UTF-8 可严格解码。冻结声明 `u22kh-frozen-declaration.lean.txt` 为 `9501d9587cdf7657150c47bbafe43812698768c3b63759336bac918cb2b06877`，500B，8LF。声明头在忽略空白后完全相同，三个历史源版本的声明均未变。冻结记录在 2026-10-28T13:02:36.129695Z，首次源写入绑定在 13:03:08.465904Z，符合先冻结、后实现。

唯一实际 owner 名称是 `Shao.OQ3.joint_energy_positive_curvature_neighborhood`。我已全文阅读 14LF 的实际 TYPE 文件及 audit.log 中的相同 TYPE；以 SHA256 `070ba17711da6c79aa34fe1d88ce3713f553e65e47f8d428b2b6a735d3a73133`、557B 绑定完整内容，不重复粘贴。实际为 1TYPE / 0VALUE / 0 statement lets，包含且仅包含以下数学对象与量词：任意总函数 F:ℝ×ℝ→ℝ、任意实数 q0；F 在 (0,q0) 为联合 C3；q↦F(0,q) 的实际二次标量导数在 q0 严格正。结论先存在共同的正 eta、rho，然后对所有实数 level、q，在 |level|≤eta、|q−q0|≤rho 时，同时给出能量切片在 q 的 C2 与实际二次导数严格正。

eta、rho 不依赖随后量化的 level、q。闭边界、level=0、负 level、q=q0 及 q 的两侧均被覆盖。helper 没有要求 q0>0，也没有声称矩形全部落在正能量半轴；这是任意实函数的局部分析接口。实际能量应用若需要 q>0，须由其正均值与进一步缩小邻域完成。这里没有把 q 限制为有限集合，没有随机性、事件、零测集、选择器或隐含几乎处处例外。

## 完整证明与全部局部值审查

1. 源码17–29行的局部 `hpartial` 对任意自然数 n、函数 G 与点 p 证明：G 在 p 为 C(n+1)，则 `(a,b)↦deriv (q↦G(a,q)) b` 在 p 为 Cn。顺序明确是先固定第一个坐标 a，再在第二个坐标 b 求标量导数；没有混成 level 偏导或沿对角线求导。
2. `huncurry` 的值是 H((a,b),q)=G(a,q)，基点为 (p,p.2)。它由 G 与坐标选择映射 `v↦(v.1.1,v.2)` 复合，基点像正是 p；坐标选择是光滑线性映射，`fun_prop` 的条件完整。这里保留了参数 p 的第一坐标，而导数变量 q 独立变化。
3. `hpart` 使用完整接口 `ContDiffAt.fderiv_succ`。取参数空间 E=ℝ×ℝ、微分变量空间 ℝ、f(v)(q)=G(v.1,q)、g(v)=v.2，uncurry 基点是 `(p,g p)`，所需正则阶为 n+1，g 是 Cn 的投影。输出恰为 `v↦fderiv ℝ (q↦G(v.1,q)) v.2` 的 Cn。没有额外的全局可微性或参数一致性假设。
4. `heval` 用 `ContDiffAt.clm_apply` 将该连续线性映射值作用到恒定的实数1；恒1函数为 Cn。固定版本的定义是 `deriv f x := fderiv ℝ f x 1`，故 `simpa only [deriv]` 直接得到真实标量导数，而非人为定义的替代曲率。
5. 局部 `D1(a,b)=deriv(q↦F(a,q)) b`；局部 `D2(a,b)=deriv(deriv(q↦F(a,q))) b`。两者都是精确值定义，虽不产生导出的 VALUE，已完整审查。第一次取 n=2，C3 给 D1 在 (0,q0) 为 C2。第二次对 D1 取 n=1，C2 给其第二坐标偏导为 C1；展开 D1 后，内层表达式 `q↦deriv(r↦F(a,r)) q` 与 `deriv(r↦F(a,r))` 按函数 eta 化完全相同，所以它正是 D2。`Nat.cast_one` 只归一化有限正则阶的类型表示。
6. `hD2.continuousAt` 提供 D2 的联合连续性。`hcurvature` 按上述定义正是 `0<D2(0,q0)`，`lt_mem_nhds` 给值域开正半轴的邻域，连续性拉回得到 `hpositive`。这一推理用的是点处真实二阶导数严格正，没有把经验曲率、有限差分或二阶形式界换成导数。
7. `hnear` 将 hpositive 与 `hsmooth.eventually` 相交。这里 ContDiffAt 的阶3是有限阶；固定接口只要求该阶不等于∞，`norm_num` 合法关闭。因而不仅基点 C3，而且同一邻域内每点 C3。这一步避免了仅由任意点态可微性错误声称邻域可微性的缺口。
8. `Metric.eventually_nhds_iff` 给出实数 d>0 与全部 `dist(p,(0,q0))<d` 点上的联合 C3 和 D2>0。构造的 eta=rho=d/2，`half_pos hd` 分别证明两者严格正。`d`、`hd`、`hpoint` 均来自同一邻域存在量词，没有随 level、q 重选。
9. `hdist` 用 `Prod.dist_eq` 将乘积距离精确改写为 `max(|level−0|,|q−q0|)`，再用 max_lt_iff。两个给定弱界都通过 `≤d/2<d` 变为严格界；`half_lt_self hd` 的前提 d>0 已有。因此闭矩形的四条边与四角仍严格位于开放球内；无需把结论的≤偷改成<，也没有误用欧氏距离的平方和。
10. `hp=hpoint hdist` 的第二项就是最终二次能量导数严格正。第一项降阶 `of_le (2≤3)` 得 `hF2`，再与光滑仿射映射 `energy↦(level,energy)` 在 q 处复合，得到所需切片 C2。其像为 (level,q)，所有基点、函数类型和正则阶匹配。

全部 `have`、`let`、存在见证与最终 pair 的值/作用均在以上覆盖。C2 切片保证导数是常规实导数；Mathlib 对不可微函数把 deriv 定义为0的全函数化约定没有被利用来假证结论。没有新增数学假设，没有 sorry/admit/new axiom/unsafe/native_decide；最终源的禁用关键词检查也为空。

## 固定库接口与实际导入

通过 server.py 的只读 exec 定向阅读了本机所用 mathlib 的相关完整声明、局部假设和证明，而非依赖最新在线版本。mathlib HEAD 实际为 `807d3836b165983210ee2ecf3cd28f239436949c`；worktree 的 lean-toolchain 为 `leanprover/lean4:v4.36.0-rc1`，文件 SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`。没有为审查新运行 Lean、Lake 或版本探测。

已逐字与该 commit 的 Git blob 比较，以下使用到的源文件均 exact_pinned=true：ContDiff/Comp.lean（`a616137e4d47245bbb576430d569109a2020e7478faa01b8dfd8286eb2d3de5a`，44731B）、ContDiff/Defs.lean（`c436e0c185d3a52da5be9be371a3c954e7a63714288aaba7ae67bc769f32b825`，64696B）、Deriv/Basic.lean（`31e8aceba6c650a5628a321b25feaff0d2e1f4e198cc5f540e64b80d31ee51b3`，41765B）、MetricSpace/Pseudo/Constructions.lean（`fac54be28ca7fe2f4afaee7a041456caf5614b394067471cc64eb437a7763787`，10379B）、MetricSpace/Pseudo/Defs.lean（`3463e90a92cb1c28bcf0062c46ea9ad4eb2737e1774232e8796bf69bad98d64b`，59586B）。

具体核对了 Comp 中的局部 normed-space 假设、comp、clm_apply、fderiv/fderiv_succ，Defs 中的 ContDiffAt 定义、of_le、continuousAt、有限阶 eventually，以及 deriv 的 fderiv-at1 定义、Metric.eventually_nhds_iff 和 Prod.pseudoMetricSpaceMax/Prod.dist_eq。所有实例在 ℝ、ℝ×ℝ 上满足，无未声明的有限维、紧性或额外完备性条件。

源码只直接导入三个 Mathlib 模块，没有项目上游；因此 server-dependency-binding 中 `sourceDependenciesExact=[]` 与真实导入一致。三个实际编译依赖对象均解析到已接受的 shared-v34 包视图：ContDiff.Comp O 为 `af152ab67bf507486a4118814e26900c4dc243370cd94a327028299b244cbcd0`（544800B），Deriv.Basic O 为 `e4c123e4bdcd986941b70c2badac1de6b748a1969a7031e21141c6caa3a25b25`（395968B），Pseudo.Constructions O 为 `39cbd1dd5e47a6e0c2c32f8c2a3c754c76d4df8549d30f4fd87eed2c372c7d5f`（216168B）。日志的 mathlib repository-local-changes 警告并不表示上述被用到的接口源码偏离固定 commit；这里未声称整个 curated 包 checkout 为 Git clean，也未修改或重建缓存。

## 失败、修订与现有内核证据

服务器 run 为 `/root/rivermind-data/shao-lean-20261021/runs/oq3/u22kh-20261028`；工作树为 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`。全部 `build-*.log`（恰3份）和 audit.log 均只读全文读取并现场重算 hash/bytes。三份历史完整源也已阅读，diff 只有33、35行的阶数归一化，不存在声明或数学前提变化。

| 原生尝试 | 源 SHA256 | 源字节/LF | RC | 完整日志 SHA256 | 日志字节 |
|---|---|---:|---:|---|---:|
| 001 | b4cd16c52a39d015aa90e7c850e5008c1389d6f42c172712fc5bda7858bb1bc0 | 2856/56 | 1 | 2f0cd82fcdd498a892247f8458aa4209f47b25451ca84b19eaada1b225343412 | 1195 |
| 002 | 2e578b4dd3fe4514dbb577afd434c6a158bfd668adf8f9ec0e6a1c68927f355a | 2890/56 | 1 | 2c42cdbe2d514d804eadbe7fc5db5a0b398034e123ed3841f160700f9b830528 | 1937 |
| 003 | b29ebe1b35c27dd0f1400b9bf84ddfd1e33ade28dffd3deff758711086e21a68 | 2904/56 | 0 | b07f26a0e65551603dce4b764d0645abe2a0be091e6c5f59eb6607ac214c55a2 | 969 |

001 在33、35行的 `simpa` 无法把有限 WithTop ENat 阶3和2分别匹配2+1和1+1；002 改用 convert/norm_num 后只剩35行的自然数1强制转换与字面1表示差异。003 仅在该行的 simp 列表加入 Nat.cast_one，关闭剩余表示差异；嵌套实导数的 eta 形式没有数学变化。两次失败都保留为 RC1，未被解释为通过或被删除。

003 的四个 tactic linter 警告分别是33、35行的 unusedTactic 和 unnecessarySeqFocus（各两项）。它们只针对 `<;>` 的冗余写法，不涉及未证明目标。完整成功日志没有 error，没有 sorry 相关警告；未修源码或关闭 linter 来消除这些警告。

首个成功原始对象位于 `.lake/build/lib/lean/Shao/OQ3/JointEnergyCurvatureNeighborhood.olean`，SHA256 `c754ce0408c6fb64ea8c8fc994541de62ce5cd0bf60e4f47e3fe27131ce2e0f7`，100880B。当前服务器现场 hash、run/source-03、生产源、冻结声明、scope、Audit 源、实际 TYPE、receipt、build-history、audit-record 均与 map/记录吻合。accepted-source-view 中本模块的链接现场解析回这个同一原始对象，hash与字节数相同；own-firstO 绑定记录原有条目修改0、shared cache写0、二进制复制0。审计请求使用该视图导入本模块，并在审计前后检查同一个对象 hash；本次审查又只读确认其仍不变，没有重建对象或复跑已接受检查。

完整 `Audit.lean` 为 `167ccb99837f681906ab748a6f26c72aa2226520a372e07a7cb39d0e2a505708`，2120B，49LF。审计按 `getModuleIdxFor?` 的实际 module owner 遍历所有常量，拒绝新 axiom，对每个 owner 执行 `Lean.collectAxioms` 递归检查允许列表，并输出完整 TYPE；对于可能的非定理定义还检查 safe 与输出 VALUE。唯一冻结 target 另行检查存在且是 theorem；实际输出1个owner/1 theorem/1 frozen theorem/0 definitions，未漏掉任何本模块的 private/generated owner，也没有额外的非定理 VALUE 待审。

audit.log 为 `698125fe865fac05db820995a8174df21e0d84b004d088ffa6b82dee2cac9248`，809B，完整输出 `U22KH_AXIOM_GATE PASS`；audit RC0。唯一 owner 的全部传递公理是 `[propext, Classical.choice, Quot.sound]`，与白名单相同，无 sorryAx 或项目新增 axiom。`u22kh-receipt.json` 为 `002e03893c27985680610f643906dfc8210880c618712407a4ca874e4faec69a`，10342B；`u22kh-audit-record.json` 为 `8a9ec1733ad437823f012019f329351f294347cbbf7026460ab0b6d81ba2342a`，3029B。保留其当时 PENDING_FRESH_FULL_REVIEW 的历史状态，本报告提供此前缺少的独立 final review，不回写旧收据。

## 26行输入覆盖核对

以下各项 SHA256 均与已绑定的 input-map 对应行逐项相同；表给出独立计数 bytes/LF，所有项 CR=0。表中的历史 exec/put/get 请求只阅读其原文，未提交执行。完整数学源、冻结声明、actual TYPE、Audit、失败源及收据内容已在本报告的相应分析中覆盖。

| 文件（均在 drafts/oq3） | bytes | LF | SHA/bytes核对 |
|---|---:|---:|---|
| u22kh-actual-types.txt | 557 | 14 | MATCH |
| u22kh-all-history-audit-read.local.json | 331 | 1 | MATCH |
| u22kh-audit-record.json | 3029 | 103 | MATCH |
| u22kh-audit-request.local.json | 3646 | 0 | MATCH |
| u22kh-Audit.lean | 2120 | 49 | MATCH |
| u22kh-build-history.json | 6805 | 245 | MATCH |
| u22kh-failed001-source.lean | 2856 | 56 | MATCH |
| u22kh-failed002-source.lean | 2890 | 56 | MATCH |
| u22kh-failure001-read.local.json | 199 | 0 | MATCH |
| u22kh-final-source-binding.json | 580 | 18 | MATCH |
| u22kh-freeze-binding.json | 321 | 9 | MATCH |
| u22kh-frozen-declaration.lean.txt | 500 | 8 | MATCH |
| u22kh-get-evidence-request.local.json | 1068 | 0 | MATCH |
| u22kh-native-request.local.json | 2607 | 0 | MATCH |
| u22kh-own-firstO-view-binding.json | 571 | 10 | MATCH |
| u22kh-preflight-request.local.json | 2340 | 0 | MATCH |
| u22kh-put-request.local.json | 731 | 0 | MATCH |
| u22kh-receipt.json | 10342 | 348 | MATCH |
| u22kh-repair001-binding.json | 602 | 13 | MATCH |
| u22kh-repair001-put-request.local.json | 214 | 0 | MATCH |
| u22kh-repair002-binding.json | 628 | 12 | MATCH |
| u22kh-repair002-put-request.local.json | 215 | 1 | MATCH |
| u22kh-server-dependency-binding.json | 273 | 18 | MATCH |
| u22kh-source-written-binding.json | 294 | 7 | MATCH |
| u22kh-source.lean | 2904 | 56 | MATCH |
| u22kh-whole-logs-read-request.local.json | 245 | 0 | MATCH |

## 原始来源与结论范围

已核对原始只读 `C:/game/shao/current/oq3/proofs/r2/report.md` 的完整文件 SHA256 `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`，20102B，并完整读取47–67行及相关上下文。原文在固定 x 的鞍点条件中列出正的边界切向二阶系数，且另有全局唯一率极小点及远区率间隙。KH374 的冻结 scope 只提供以后处理小正 level 所需的通用局部正曲率邻域接口；它没有把原文那些更强条件宣称为已被本 helper 推出。

本定理的 F 任意，实际应用中的 `F(level,q)=J(level*sqrt(q),q)` 并没有在此实例化。消费者仍需使用同一实际模型的已接受 chart/Hessian 等结果，证明该 F 在实际均值附近联合 C3，并证明实际基点二阶能量导数为 `q0/basecovdet>0`（或等价的所需严格正性）。本报告没有代替该消费者验收这两个输入，也没有声称实际 Legendre rate 已满足它们。

因此本单元的数学正确性与精确机械覆盖可接受；它没有给出实际正曲率公式、优化切向曲率、鞍点存在/全局唯一、远区 gap、完整 D 应用、随 x 一致性或 full OQ3 完成。现有已接受 B/C、反例及其他旧证据不被本次审查重开或扩大。这里未作新颖性检索或宣传，不把通用连续性/微分法引理当作新的研究主定理。

## 终止交接

`verificationStatus=LEAN_FULLY_CHECKED_FOR_FROZEN_KH374_HELPER_BY_REUSED_EXACT_AUTHOR_NATIVE_AND_ALL_OWNED_RECURSIVE_AXIOM_RECEIPT`；该标签只指上面精确的单个冻结 helper。

`reviewStatus=COMPLETED_STOPPED`；`soleReportWriter=RELEASED`；本审查上下文的 `heavy=0, inflight=0, pending=0, uncertain=0, children=0`；`nextTask=NO_NEXT_TASK`。释放仅指本上下文对本报告的独占写权，不是 OQ3 lane/source owner 的释放。写后由本上下文全文读回报告并重新核对全部26输入；报告自身最终 SHA256/bytes/LF 随最终交接给父实例。父实例应全文读本报告并实际观察此上下文 stop 后，才轮换 solechild。
