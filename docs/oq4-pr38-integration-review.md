# PR38 独立集成证据验收

STATUS: CORRECT / INTEGRATION_EVIDENCE_PASS

范围：验收现有冻结证明、独立票、机械回执及 Git payload 的证据链；不是重新证明。
本轮没有运行 Lean、生成 olean、重型计算、修改源/缓存/锁/manifest/lane 状态，
没有联系 lead。唯一写入文件为本报告。OddPower 源保持冻结。

裁决：PR38 的新增单元证据完整，可进入 root 的最终全库集成门；本报告不是
该全库门的执行回执，也不宣称任何完整根闭合。未发现需退回作者的缺失证据。

## 1. 冻结提交与实际 payload

PR：[randomcat4/shao-lean#38](https://github.com/randomcat4/shao-lean/pull/38)。
GitHub 只读元数据实际确认 OPEN、未合并、mergeable，head 为
`f46ee95e7ecbac3686caae481c9a03fd6bad96f7`，分支 `feat/oq4-one-sided`。
服务器同名分支引用及冻结 commit 对象均为该 head。其唯一父提交为认证 base
`f73e3ca6534783c94dc6855fe4277a83b145dcf0`。

直接读取冻结 Git blob（不是当前工作树的未提交续作）确认：

| 新源 | 冻结 blob、本机已读源、远端当前源 SHA256 | 公开定理 / 全部 owned |
|---|---|---|
| `Shao/OQ4/LaplaceGenerating.lean` | `eab53afb87248fc0f9b94ddf84e986eedae51f2446e9b7ea176e517c4a861ed8` | 13 / 25 |
| `Shao/OQ4/FiniteSurvivalLaplace.lean` | `49241958f2ae692b56db5fe0aa021a5e88b0020ac6487ddb463d05efb69518cb` | 24 / 30 |

从 f73 到 f46 恰为24项新增：2个数学源、每单元8个 docs、3套 audit/receipt。
所有24项冻结 blob 的 SHA256 与本机所读对应文件逐项一致；不是只核源码和票名。
对该base到head运行 `git diff --check` 实际 exit0。该增量不修改既审数学源、共同定义、
根导入、manifest、共享审计、版本锁，也没有 ReflectedSurvival、SpitzerKernelBounds
或其它未审续作。

**49与24的区别已核实。** 本次 GitHub API 报告 live base 为
`3eca0987931433203129a01443c5a72e73b992b8`，Files changed 为49项。
其中额外25项是继承 PR29 的 IntervalConcentration/LaplaceTail 包，不是另25项
未审工作。本轮将这25项在 f46 中的字节逐项与已接受 PR29 最终 head
`ad965f7bcb3dc6f8f08a0afafb2099fd28198980` 比较，**25/25完全相同**，
包含最终 LF 格式源、format-note、独立票、audits 和 receipts。两继承数学源仍为：

```text
IntervalConcentration 491e088fccc4457f18701ab7440da8cc9811183d462e3f3b7f22b096ccbf0875
LaplaceTail           664df6aa0c3221b9a0212580a20b141b7f0a0eea1d8adbeb4af15d486dcf68e2
```

因此 live 49项全部属于已审内容；root 集成时应以其当前接受 main 和 PR29
已入库字节为准，不能把“24项新增”误读为当前 GitHub 页只有24项，也不应重复
计算 PR29 的27个公开定理。API 的 mergeable 仅为 Git 状态，不能替代下述全库门。

## 2. 两项源前提确实保留

已读原始本地只读数学源 `C:/game/shao/current/oq4/b01/proof01.md` §2–§3，
实际 SHA256 为 `7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38`，
与两份 lead receipt 的 source_proof_sha256 一致。§2 明列普通和 BE 与原始 SP。
再对照最终 FiniteSurvivalLaplace 的主接口（205、266行起），确认二者没有被
目标 S 或等价生成式替代：

- **普通和 BE 型 CDF 输入**：`C_BE≥0`、`β≥1`，所有自然 `k≥1`、所有实 `x`，
  在真实 `Π_k=Measure.pi(fun _ : Fin k => ν)` 下，
  `|Π_k.real{prefixSum(a,k)/sqrt(k)≤x}−standardNormalCDF(x)|≤C_BE β/sqrt(k)`。
  β在此是显式误差参数；没有将它默认为已证的第三矩，也未从未给出的中心/方差/
  矩条件自动推出 BE。
- **原始 Spitzer 输入**：所有 `L>0`、`0<s<1`，
  `laplaceG(maxLaplaceMean ν L)s = exp(laplaceW(endpointLaplaceMean ν L)s)`。
  左侧含 j=0，右侧为正时刻 endpoint 正部指数均值。所需
  `(1−s)⁻¹ exp(−laplaceW(payment)s)` 是由内部真正可和的级数及 A=1−b 推出的结论，
  不是额外假设。

生成函数模块本身是明确 S1、有界序列、Antitone 和精确归一化 SP 型等式下的
确定性解析链。有限 law 模块内部证明实际均值 Antitone、可积性、三个级数可和性、
从原始 SP 的改写和闭事件 Markov 支付，再实例化该解析链。因此最终条件结论确为

```text
Π_m.real(closedUpper d) ≤ sqrt(2) exp(6+3 C_BE) (d+β)/sqrt(m), d≥0, m≥1.
```

这里用公共 Path/prefixSum/maxWithZero/closedUpper，含零前缀、原子、闭等号、
d=0、m=1；没有把生存后独立、所需 S、可和性或非增性再次列为前提。
本轮复用既有独立语义/数学/形式票，不对这些证明另发新数学票。

## 3. 独立票与最终字节的锁定

完整阅读两套 statement、MATH_ONLY 与最终 FULLY_CHECKED 票，均为 CORRECT；
最终形式审查者先完成隔离数学票，再读最终实现，明确未读作者 receipt/summary/
declarations，且没有生成目标 olean。下表全部哈希同时吻合本机文件和 f46 docs blob：

| 工件 | LaplaceGenerating | FiniteSurvivalLaplace |
|---|---|---|
| frozen | `a6fddda60883208834258b774b8f77455973584c468afabac76cd8c885eae577` | `988db8de1f059c3cc49dacdd72346a1459b7e40773ef96f4c19370221634ec76` |
| 匿名 proof | `1484b50453d9df0f9879848f8fe4f74965c316812b283ab417a7e82d37dd4099` | `83c93e47bf987d500f2d05e17920893b3211e19d390c78d0fcf17f26837aad37` |
| math review | `e8f6f6fac05be4bb8626761de257b175fddaef18c784569b30341da8c8418f56` | `062f91c75cf38e1d53089c7c3267db55be9ee51a33c9080a5a0e3c4801372c82` |
| final formal review | `f050d3b7dc70f9b601d0541a44990108ae1e286487ae4bd4106fe7c88757ecc0` | `ca30a99cae47f7bf9cdc267744b97e948b4344e48578020fe99a35ef801762cf` |
| statement review | `772a8384cd2c6ab47fec911f9a81cf980f78e06e6f51e69eb3eccf870e26bceb` | `852fa6d5b558e324e47f351fb9e47035e89c275687349a46cc98a20b850a745f` |

对应本机票为 `drafts/oq4/review/{laplace-generating,finite-survival-laplace}-{math,formal}-review-v1.md`
及 translation/ 同名 statement 票；冻结 Git docs 使用 oq4-generating/oq4-survival 名称。
两份 scope、author-receipt、declarations 同样逐项字节一致，未以摘要替代完整最终票。

生成函数独立形式票实际记录 UTC `2026-10-21T14:50:11Z`：无-o目标及完整源动态
审计 exit0、无警告，全部25项新增（15显式+10生成）无namespace筛选逐项传递公理
白名单通过；前后源SHA固定 eab53afb...。

有限生存最终独立形式票记录认证 base f73、UTC `2026-10-21T16:06:36Z`：
无-o目标、完整4924源全部新增常量动态审计、指定21模块共存三个过程均 exit0，
无警告、stderr空；30项（28显式+2生成）全部通过。21源及4项共同依赖前后SHA
不变；两个旧/新 measurableSet 名和最终主界实际同时检查成功。

冻结中 `finiteSumLaplacePayment ν L k` 的手写记号顺序事项没有隐去：独立数学及
最终形式票都明确采用实际 API `ν k L`，对象仍是 k步真实Π、尺度L；没有改量词或前提。

## 4. 重名历史没有被旧票掩盖

旧候选 SHA为 `63f00181f50ab082e0c1e1695ec5c983191bcf25a01bb901454844fe4316b0b5`。
本轮对本机留存旧字节实际计算：恰有2次 `measurableSet_closedUpper`；将这2处换成
`measurableSet_closedUpper_laplace` 后，与当前4924源**逐字节相等**，没有其它变动。

旧 standalone 成功没有被当成共存认证。旧候选已撤回，数学票保留；最终独立形式票
明确未给旧63f候选形式认证，而只审新4924源码并重新执行无-o/全部新增/21模块共存。
这满足复用未改数学票、补充修复后完整机械票的证据要求。

服务器旧作者效果本轮只读实查：`namefixTarget.exit`、`namefixOlean.exit`、
`namefixAudit.exit` 全为0；前两个 log为0字节，Audit log末尾30项。
这些只是补强已有独立最终票，没有用作者 olean哈希代替独立证明检查。

## 5. 既有机械效果与全归属审计

全部日志仍只在服务器 `workspaces/lead-oq4/` 下；本轮只读取既有 exit、大小、
SHA和末尾计数，未重放任何 Lean。

| 既有 gate | 本轮读到的 exit / 计数 | 既有日志 SHA256 |
|---|---|---|
| generating `repro_outputs/oq4-generating/{target12,olean,audit}` | 0/0/0；target/olean空；25 owned | audit `79ae1cf4c0a6fbacf310305edb64a71f64c7f79f7ac1aa798f48527fdc7a12e1` |
| survival `repro_outputs/oq4-survival/namefix{Target,Olean,Audit}` | 0/0/0；target/olean空；30 owned | audit `96f952572ecf73a7a14d0e2fb44ebbf29f739b345e2f446f8a42c81be602abe2` |
| generating `verification/oq4-generating/lead-audit` | 0；13 public /25 new /25 audited | `08ad288fa4d2fa506eb926b4f052b069042c2b814ef75fc4e39774ef513d14b2` |
| survival `verification/oq4-survival/lead-audit` | 0；24 public /30 new /97 audited | `33a06c7265977259a24e2fa9ed4f575f8833973251c167d7263c66ba19a9b021` |
| combined `verification/oq4-one-sided/combined-audit` | 0；55 new /375 audited，21模块 | `e4c5da0a7398696683bfc11520f9dfd80a32ee107a8e5418d8ba18ba2ed5da9b` |

作者唯一生成的现有目标 olean 本轮SHA也吻合其收据：

```text
LaplaceGenerating     b5d5b308ec183dc097cdb856974ac3a5f0724c274ae17ef06fd80861a942f4ee
FiniteSurvivalLaplace 49159bb33819ebe0bf2c654a9d031e7a0f9233b3f9de3f34aca47a4c12ee4413
```

已读三个 audit 的选择代码。模块owned由实际 moduleidx决定，combined还纳入
`Shao.OQ4` namespace常量，因而不会漏掉导入名称下生成或跨namespace helper。
三个 audit/receipt 的本机与冻结 Git blob 一致，精确SHA为：

| 包 | audit SHA256 | receipt SHA256 |
|---|---|---|
| generating | `298a834bdd10e59acd8f319d3728b197d34b2d6f32654b110dd4ce1e3a431229` | `6d02cc91660f4e18abd6f96fefc7d50d8a12ea05672e00fe4fe4ebd9d430cd7e` |
| survival | `c333813a11a8e62b0591b5596606acb85af7451b637e4a3a0d8107d7828f6e25` | `1e9b2da2c98def923363b791f31a4bb6daaa3a42e5780f96f08ce9af3844b18c` |
| combined | `a69db0469be61ec7e1d343257af7b450d6c3f0bdc3119d3485d5e8f9968fdc71` | `c62cff35591997b94c9ab13b6bb9ea15cf32db2004d005a15beb8d41a58347aa` |

本轮静态重新计数13+24=37个公开 theorem（另2+4定义），禁用源token无命中。
所有既有票与回执一致采用 Lean `4.36.0-rc1`、mathlib
`807d3836b165983210ee2ecf3cd28f239436949c`，仅允许 `propext`、
`Classical.choice`、`Quot.sound`。本轮不将这些历史实际运行改写成本轮 Lean 执行。
服务器记录的本轮只读证据核对时间为 `2026-10-21T16:28:45Z`。

## 6. root 的最终集成门与非闭合项

证据链可以接收；root仍需在其当前接受 main 上执行实际集成门：

1. 固定f46及上述源SHA，保留PR29最终664df6aa源和format-note，排除独立续作。
   根据实际树关系合入这两个新模块及对应已审证据，不回退共同文件或重复旧包。
2. 由root接两个真实根导入并更新其拥有的manifest/公开清单；检查版本锁、接受源
   哈希和禁用项，实际编译完整 root 入口和项目要求的集成目标。
3. 在实际完整导入环境中按module归属枚举所有项目常量，包含public/private/generated
   及跨namespace声明，进行全传递公理白名单门；重新生成共同receipt和实际计数。
   本包375项lane审计不能冒充该全库门。源字节不变时不用再次重复作者或独立单元目标。
4. 发布/合并前核对PR head仍为f46（或记录明确集成head及相同源SHA），保存精确服务器
   命令、exit、日志绑定、独立票与集成差异检查；本报告没有替root执行或授权merge。

本包关闭：真正W/G解析链，以及在显式ordinary-sum BE-CDF和原始SP输入下，
真实有限产品law的**上侧闭生存**推导；常数 `sqrt(2)exp(6+3C_BE)`。

BE本身、原始SP本身、反射law及双向S接合、无条件S/AC/O0/R3/R4、B1/Brownian
输入、长期K/Kv、4/π、能量分母E1–E6及完整OQ4/C1/C2/其它完整根均未由PR38闭合。
不把lane后续已经另有进展的ReflectedSurvival票计入本冻结PR。
