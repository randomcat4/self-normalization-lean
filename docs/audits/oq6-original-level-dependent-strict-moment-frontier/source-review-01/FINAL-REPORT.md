# OQ56 unit257 最终独立完整审查

结论：**接受精确修复源码，qualified=true，machinePending=false**。此次资格只属于 SHA256 `48197cc58c7274bd41d296d9370fc41704b0a606c98d2abc01173f9a956e9ebd` 的 46695 字节、733 LF 源码及其首个成功原始对象 `5daa848eb1ea061eb5a9e232cbdc6770e5a7b26bd5b7411b740b81f1cf1aa689`。完整 SOURCE 审查、两行受影响证明补审和本次完整新机器类型/所有实际 owner 公理审计构成一个连续独立审查。没有未解决问题，也不要求作者修改声明或证明。full OQ56 与 root 继续 **OPEN**。

## 独立性、固定版本和证据复用

审查者为 `/root/oq56_unit257_review`，父 lead 为 `01a1822b-1815-7f21-a1af-2e0b15ee67a5`。按请求使用 math-theorem，未启动 math-ultra、子代理、Lean、lake、PP、AX、服务器、网络、Git、API、上传、Goal、计划或侧栏操作。唯一写入范围为本目录；没有改写作者源码、冻结文件、已接受证据或其他目录。请求模型为 gpt-6.1-sol/xhigh/fresh；实际模型、backend、effort 及 input/cached-input/output/reasoning-subset usage 不可见，均记录 null。

原完整 SOURCE 报告 `SOURCE-REPORT.md` 的 SHA256 为 `95dbb8ba33eed4a9a589710e23d98b02ec3dbd9fd99b91048983b40494e0c681`（12708B）；原补审报告 `REPAIR01-REPORT.md` 为 `2fd7e932c9816a2eb9bb65d42056507fdb31576cedfec8fea4e585b7e3a5311c`（6383B）。两阶段报告、覆盖、静态核验、ACK、脚本和 manifest 全部保持原字节。源码冻结仍为完整 517 LF head，SHA256 `2dc9f8a5c0e192638d9b8907c0ab5f66f8877d3b62962d087299c899115a26d0`（35639B），冻结声明 JSON 为 `1638ec2044887cd2c81851a8910d5e0062ef1909d589081e203356d00ea1bae0`（1995B）。

原 SOURCE 已完整读原 731 LF 新源码、全部声明和证明、作者路线/报告/静态完整类型及绑定库存、p51/p54 原文和 v149 的 21632B 原始 t 相对尾费用含义审查。新 generic IIDSourceStrictMomentBudgets/NormalizedStrictMomentBudgets 合同及其证明得到完整阅读；旧 OriginalSingleWitnessAnalyticStrictFrontier 仅作定向 API 参考。承重 qualified256 使用修复源码 `bbab19f1d8c091b81e3c06e7cfbc0dcc3c6acb16ce39261d0f08b2dc3ac1efcf`（66823B/1053LF）及其已合格证据；历史 8165 候选不被误当承重版本。其已接受完整 proof/actualTYPE/AX 按精确绑定复用，没有重做旧 7912 LF 实际类型审查。

修复仅在当前源码第 703、708 行各插入一条 `change Filter.Tendsto ... at hSourceLim`，分别把 sourceCostη/sourceCost0 和 compactCostη/compactCost0 的已展开端点作定义性统一。其后 sub_const、abs、eventually 的原字节不变。两处局部证明正确，删除这两行精确恢复原完整源码；没有删除或其他改写。49 个 immutable inputs、18 个作者 payload、全部静态库存差异及冻结/类型/声明/producer 合同不变已核验。原 SOURCE 完整覆盖加两处受影响补审精确覆盖新源码，未重新审阅未变旧 proof。

## 全部实际类型与数学含义

本次完整读取 `actual-owned-types.txt` 的全部 8507 LF（1132278B），其中主定理 8504 LF、生成的 `._proof_1_1` 3 LF；完整 metadata、两条 rawOwnedJSON、每 owner AX 和空 VALUE 文件也已读完。打印时两次截断的 309–551、5255–5274 段已分别补读，覆盖没有缺口。类型规范化文本与 metadata 内完整 type 逐字相等，声明前缀、量词、约化测度空间及所有结论均按以下范围对照；完整逐段索引保存在 FINAL-COVERAGE.json。

- 实际类型第 1–96 行保留原可测 Ω、概率 μ、核 h 的可测/L²/对称/中心化条件、原投影二阶矩 1，以及原 g/r/v/rho。一个 m0 在所有后续 n/current z/ε/p/cBudget 之前一次选定；没有参数依赖的重选。
- 第 97–5062 行保留整个 255 首包，包括所有 n/y/原 tilt window/ε 前提、原空间与约化/增强空间、同一 observable、删除和费用转移、三次费用结论。第 5063–7962 行保留当前 n/z 和 qualified256 的全部 49 字段 consumer，而不是截取部分结论。Q 的符号、绝对 L¹、积因子、full/deleted/compact 可积性、正完整 I 和各极限均保留。
- 第 7963–7994 行中 2<p≤3、cBudget>0 和 p 矩可积性仍明确出现。p 矩只针对原 mΩ/μ 下的 g，未增加 trim μ0 的 p 矩前提。原投影 g 的可测/L² 在原 mΩ 中先建立，约化实例切换未偷换此义务。
- 第 7995–8177 行使用同一个 q 与 id:P→P0 的测度保持、可测性、可积性和 Bochner 积分转移。Fz 始终是 zt 的平方乘 min(|zt|,1)；每个 δ0=δoriginal 与 L0=Loriginal 都在实际类型中。约化/增强空间合法性与原 p 矩通过同一投影连接。
- 第 8060–8247 行保留 β=0 与 β>0 分支。正分支精确为 z≤cWindow·β^(-1/p)·n^((p−2)/(2p))；cWindow=(min(1/2,cBudget)/2)^(1/p)，其 p 次幂和严格小于 min 的常数性质保留，结论为 δ0<1/2 及 L0<cBudget·z²。原 tilt-window 也仍是条件。
- 第 8248–8285 行保留同一个 ξ/Y/ε 及 η=actualNormalizedFamily，逐坐标截断项极限与有限总和极限均在同一序列上。没有替换归一化族或只证明总和而遗漏坐标。
- 第 8286–8504 行是每个 τ,δ>0 选一个共同最终 k0，对所有 k≥k0 同时覆盖严格预算、Q 的绝对 L¹<τ、两项费用连续性误差<τ，以及三次费用上界加 δ。原 eventual 量词、正 δ 余量均保留；未改成所有有限 k，也未把 +δ 去除。
- 第 6844–7355 行及整个 consumer 内所有部分归一化比率的分母仍为完整 Iη/I0。source 的 Fz 与 compact 的 1+z 截断各自保留，没有混用固定 clip1。
- 第 8505–8507 行生成定理为 n≥4 下排除 ¬(1≤n) 的算术辅助证明；它不引入新的数学模型假设。

13 项 unused-binder 警告已对照实际类型逐项确认：首包 hn/hy/window/ε 条件、当前 hn/hz/window、ξ 的索引以及 hp2/hp3/hgp/hcBudget 均仍在完整实际类型中。警告不表示这些前提被删除。原源码证明与实际声明之间未发现弱化、量词移位、测度偷换或隐藏假设。

## 首对象与全部 owner 机器证据

原始成功对象的物理路径为 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/.lake/build/lib/lean/Shao/OQ6/OriginalLevelDependentStrictMomentFrontier.olean`，SHA256 `5daa848eb1ea061eb5a9e232cbdc6770e5a7b26bd5b7411b740b81f1cf1aa689`，6353520B，mtime_ns=`1793209786508587003`。native02 前没有该新对象；native02 后的对象指纹与 audit01 前/后/current 的指纹逐项相同。

| 既有执行 | 实际 Lean 退出码 | 自然耗时 | 原 receipt SHA256 |
| --- | ---: | ---: | --- |
| native02 | 0 | 26.180721012875438s | `392a20f5caacd58e1cbdce5bd978ee58106c823d563e4d956b7acd62145be5e9` |
| audit01 | 0 | 6.435998382046819s | `7da8eeee9a5b6f18c39a8561037c2bc6965fda50faf04a1801642736590f61cb` |

两条执行均自然结束、owned ended，未发生 timeout、cleanup、ownership issue 或不确定 in-flight；protected before=after，分别 27904/27914 记录。两条外层 transport 均为 1，strictWrapperSuccess 均为 false；native 有 20 项源码警告，审计有完整输出流，因此本结论**没有**把严格空流 wrapper 描写成成功。资格使用已验证的实际 Lean0、完整诊断、同首对象及实际全部 owner 的审计结果。

窄化既有 receipt 投影 `machine-command-and-stop-existing-receipts-projection.json`（12037B，SHA256 `14456c3a7f0b32d457f73e5ddbb59c923bbc3a5ea9435ad12aa1e9ef24ba1732`）补齐并核实实际 command/config/STOP 证据：两次实际 argv 均为 taskset CPU52–55、lake env lean、-M8192、-j4；native 显式 -o 首对象，audit 实际 argv 无 -o，且 audit 输入只 import 本新模块。CPU before/after 都是52–55。Mathlib HEAD 为 `807d3836b165983210ee2ecf3cd28f239436949c`，toolchain 完整内容是 `leanprover/lean4:v4.36.0-rc1\n`，其 before/current 指纹相等。AUTHORSTOP 的完整 1290B 文本、解析值和 SHA256 `d3a66f378ab99ad3fd0be965342c5e7d10d425aeadb1c9c35a1c70a82c250a67` 已核验；其记录 author Lean STOP、无需为警告重编译，FIRSTEMPTY=null 并明确不是 runner 返回字段。

62 LF 审计输入全文已读。owner 发现使用 anchor 的实际 module index 遍历全部 env.constants，无 namespace 过滤；因此 owner 数不是按名字猜测。每个实际 owner 都有完整类型、bodyExpressionPresent 和递归 Lean.collectAxioms 结果，未遇到 axiomInfo 或其他不支持种类。实际 owner 只有以下两条：

| 实际 owner | 种类 | TYPE 行数 | 递归公理 |
| --- | --- | ---: | --- |
| actual_original_level_dependent_strict_moment_frontier | thmInfo | 8504 | propext, Classical.choice, Quot.sound |
| actual_original_level_dependent_strict_moment_frontier._proof_1_1 | thmInfo | 3 | propext, Quot.sound |

实际合计 2 owner、2 theorem、0 non-theorem、0 required VALUE。VALUE 文件实际为 0B，SHA256 为空文件标准值；这是实际完整 owner 扫描后的空义务，不是遗漏非定理值。公理出现次数从两份实际列表导出为 propext=2、Classical.choice=1、Quot.sound=2；全部在既定三项白名单内，无 sorryAx 或新公理。

## 归一文本、失败保留与警告

五个完整归一文本共 2285128B；其 metadata/types/values/summary/server binding 指纹全部核对。归一脚本完全读过，并与已建立的 256 脚本作精确比较：只有新路径、模块、anchor、source/receipt 指纹及三处版本/attempt 描述替换；实际 owner 审计模板也仅替换模块与 anchor。未新建执行 wrapper，未重跑旧 proof 或旧 AX。

完整 metadata 中两条 rawOwnedJSON 与各 canonical metadata 字段相等；按原输出顺序和实际完整 TYPE 在**内存**无损重建审计 stdout 为 1133354B，SHA256 `b2f5dacee31b01cb9df68f57790e36a310d93092fc154c830475fa59c41b0250`，与原 audit receipt 完全相等。五文本通过内存 gzip 传递；未复制 raw log、对象、cache 或环境到本地。37 个新机器/版本/既有审查绑定的具体路径、字节数、SHA256 记录于 FINAL-COVERAGE.json，既有 source/repair manifests 的所有 payload 也已重新核实原字节。

完整 20 项 native 警告均读过并逐条核对原诊断消息指纹：7 项 style（5 letI、2 introMerge）和 13 项 unused；源码 errors=0。stderr 的 mathlib localchanges 环境警告保留。警告分类以实际完整诊断派生，不沿用错误的“19”描述。

原 native01 对旧源码的实际 RC1/25.739878229796886s/noO 记录保留。native02 准备脚本曾因换行 SyntaxError 在 Python 执行前拒绝，已有完整 known-effects 证明无 source/config/run 效果；audit 准备曾因“19警告”断言在 STOP/config/run 前拒绝，后修正为实际20项元数据且未重编译。两项行政失败及所有 receipt 都保留，未改写为数学成功。本审查中的可选 PowerShell 字段展示错误、截断显示补读和 normalizer 比较补足三处描述替换也只有本地读/比较作用，不是服务器数学执行。

## 原始范围与最终交付

p54 仍仅提供条件 p 矩收敛/统一有界修复；固定 clip1 的三次费用反例保留，外部 source engine/SZ 结果归属保留，先前249的条件 physical-relative 支付没有被本单元抹去。actual upper/current physical、external engine、Gaussian CDF、relative/DC、full OQ56 和 root 均继续 OPEN。当前合格结论是冻结条件合同中的完整 level-dependent strict-moment frontier 及共同 eventual 控制；它不声称原题根定理已闭合。

FINAL-VERDICT.json 给出精确资格，FINAL-COVERAGE.json 逐项枚举完整阅读、数学义务、owner/AX/VALUE、实际执行与版本绑定；MANIFEST.json 封存所有既有和新增审查 payload。最后写入 FINALWRITE.json 六零释放，随后停止本上下文写入。本次所有 reviewer 数学/服务器/网络/发布执行计数均为0。

