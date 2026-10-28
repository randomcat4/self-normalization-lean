# 257 repair01：两处局部费用极限类型对齐

STATUS: DIRECTED_PROOF_EXPRESSION_REPAIR_DELIVERED。完整修复源及完整 proof 已交付，纯本地静态核对 PASS。新精确源尚待既有独立审阅上下文对受影响证明表达与新源绑定复核，并待父线服务器 native；本作者未执行 Lean/lake/PP/AX/server/network/upload/Git/API，不自行 qualified。

唯一 Lean 源 `OriginalLevelDependentStrictMomentFrontier.lean` 的 SHA256 为 `48197cc58c7274bd41d296d9370fc41704b0a606c98d2abc01173f9a956e9ebd`，46695B、733LF。完整 proof 在532–728行；独立的 `PROOF-BODY.txt` 为 `a19fb57e2ef8fa412b777fb99895b49e6120691445b1b5a5e8a845d9d1f8c801`，10584B、197LF，包含完整实际证明。`exact.patch` 为 `5e99d482f01e440960a09c8f159dc036a270948aee0b2d8e39ddd348c036e486`，987B、15LF。

本修复只在源703、708行各插入一条 `change … at …`。删除这两行即可逐字恢复原源 `ee2f5ff993bc92f6d5154be82ebb4da683f909717f0b20a98a4b8c76255f305b`／46525B731LF。完整冻结517LF head、前言、closing及所有其他原 Lean 源字节不变。旧 proof-body 工件原先包含一个边界空行；新 proof-body 以单末尾LF保存，这个继承的1LF在拼接公式中显式保留，故完整 Lean 源没有额外空白改动。全部新文本为 UTF-8无BOM、LF、单末尾LF。

## 精确授权、失败事实与原证据

本作者为 fresh `/root/oq56_unit257_author_repair01`，唯一写入 `author-repair-01/`。activation `afa1c8b4b2ac4d9307c8a71782ad7bd68afe3aa6f00a9f96c4ae2e3dd2f6c762`／2884B明确禁止更改数学声明、前提、量词、常数、实际η或费用。原作者 FINALWRITE `6f10deb6bffefe1d174ed664e1a39aff96f6a6dbbaec0ac5d91580ed8d79a1c8`／2875B的六零释放与原 MANIFEST `55d675d24a673d5bf4ad0cd99fca0d0213a447d1b23abd610d8b71f94012615a`／4892B均已验证。ACTUAL_READ_ACK先于任何修复源写入。

原源已经独立完整 SOURCE 审查，原 SOURCE-REPORT `95dbb8ba33eed4a9a589710e23d98b02ec3dbd9fd99b91048983b40494e0c681`／12708B及 verdict/coverage/manifest均读取并绑定。该 SOURCE 接受不等于257已 qualified。原服务器 native01自然结束 actualRC1、25.739878229796886s、无对象、before=after27834，timedOut=false、cleanup空、inflight/pending/uncertain均0。完整7064B源码诊断和134B环境warning只从父已投影的 `native01-actual-projection.json`读取；未读远端原始大日志或重放任何请求。

原诊断仅在旧源704、708行：`eventually_lt_nhds hτ` 的邻域点为0，但此前 `.sub_const … |>.abs` 的目标点仍以完全展开的原费用减局部命名费用呈现。`simpa only [sub_self, abs_zero]`不主动展开这些局部名称，无法把两个表示统一后消去。原诊断已经表明 `sub_const`、`abs`、`eventually` 的调用被接受；此次不改这些API调用，也不为样式warning改源。

合格承重256仍是 `bbab19f1d8c091b81e3c06e7cfbc0dcc3c6acb16ce39261d0f08b2dc3ac1efcf`／66823B1053LF，对应 e052资格 `e052e31d745497938fa02c8f5875ea9904331a7a0a7ff93011dda97b000882c0`／9469B。其完整公共合同与当前保留包核对；既有精确首O和独立最终资格复用，不再审旧完整proof、7912LF actualTYPE/AX或重跑旧checks。历史8165候选没有被当作合格实现使用。所有旧失败、warning及严格wrapper事实均原样保留。

## 两处改动的完整推导

在 `hSourceEvent` 的局部 `by` 内，新增：

```lean
change Filter.Tendsto sourceCostη Filter.atTop (nhds sourceCost0) at hSourceLim
```

这只把同一256 consumer字段的定义等价类型改写成当前冻结的局部名称。`sourceCostη`仍为同一ν、同一η(k)、同一full/deleted权重及完整Iη(k)定义；`sourceCost0`仍为原P及完整I0的同一费用。它没有构造新费用、没有使用等式假设，也没有改写公共定理。局部 change 后，原表达 `hSourceLim.sub_const sourceCost0` 的类型具有极限点 `sourceCost0 - sourceCost0`，取绝对值后极限点为 `|sourceCost0 - sourceCost0|`，原 `simpa only [sub_self, abs_zero]` 精确化为0。由τ>0，`eventually_lt_nhds hτ`及Tendsto.eventually给出最终 `|sourceCostη k-sourceCost0|<τ`。

在 `hCostEvent` 的局部 `by` 内，新增：

```lean
change Filter.Tendsto compactCostη Filter.atTop (nhds compactCost0) at hCostLim
```

同样只统一已有compact费用的定义等价表示。原 `sub_const compactCost0` 后的极限点变为同名量之差，原 `abs` 与同样两条simp规则给0，τ>0给最终 `|compactCostη k-compactCost0|<τ`。每次 change 的作用域只在相应have证明内；公共类型、父结果字段及后续事件交并不变。具体命令、全let上下文、原始静态类型、对齐类型、后续sub/abs派生类型及精确源切片完整记录在 `CHANGE-TYPE-ALIGNMENTS.json`。这些记录是源码推导，不是机器PP。

这两步不改变任何实质数学推理。对每个τ,δ>0，严格截断预算事件、Q的绝对L¹事件、两项费用误差事件和带原+δ余量的三次费用事件仍按原五事件交并取得一个共同k₀。证明没有把最终预算升级为所有k成立，没有消去δ余量。无需更改任何冻结数学声明或增加前提。

## 全部范围和量词保持

完整 head 仍为 `2dc9f8a5c0e192638d9b8907c0ab5f66f8877d3b62962d087299c899115a26d0`／35639B517LF。唯一m₀在全部n/current-z/ε/p/cBudget之前选定；同μ₀、同ν、同ξ/Y/ε/η、实际归一尺度和signed Q均不变。完整255首包和49字段256 consumer保留为原合取，不摘除旧声明。原μ下 `Integrable[mΩ] (|g|^p) μ` 与β定义不变，无新增trim律的p矩前提。

每个δ0(i)=δoriginal(i)及L0=Loriginal的两次真实积分运输不变；非负性、原量化率、β=0分支、正β窗口和cWindow常数不变。所有完整及partial比值的分母仍是完整Iη(k)和I0。当前费用保持512、rho、current-z，compact预算保持1+z的原定义，没有混同Fz与compact预算，也没有换成fixed clip1费用。

完整IIDSourceStrictMomentBudgets、NormalizedStrictMomentBudgets和TruncationBudget的实际合同/proof已读。新声明保留的合格256公共合同完整对照同一冻结包；本次未重新审查已合格256完整旧证明或机器材料。p51、p54和v149来源衔接报告全文已读。p54条件p矩仅收敛/统一有界修复不变；v149 fixed clip1三次费用反例不变；外部Shao–Zhou随机区间、自归一鞅和DC来源归属不变。旧249在其显式前提内已有的条件性physical relative付款也保持原资格。

actual upper/current physical联合付款、external engine、Gaussian CDF/relative-tail、DC、fullOQ56/root仍OPEN。本次修复不补这些独立接口，且不修改先前已接受的原始范围。

## 静态库存、字节校验与下一依赖

在新目录复制并最小适配原纯静态 `build_evidence.py`，只改输出目录与上述明确的proof边界separator拼接。运行后真实导出 `PRODUCER-TYPES.json` 的3个完整producer声明、5处全部实参和完整返回type；`LOCAL-CONTEXTS.json` 的198个完整header/type/RHS及词法范围/源切片；`BINDING-TYPES.json` 的22个pattern命令、199个完整绑定type及scope。49 consumer、89首包、IID外层5/每n11、normalized5字段均从实际合同推导并断言。所有producer声明/实参/返回type、所有pattern类型与旧库存相同；198个local中只有两个event的RHS增加相应change。新源所有切片均以实际UTF-8起止byte、SHA、原文及行号roundtrip。

`REPAIR-CHECK.json`记录修复目录的全部静态比较、精确2增0删、完整源逆恢复、冻结匹配、输入不变性和格式结果。库存为PURE_SOURCE_DERIVED_STATIC_NOT_MACHINE_PP；actualOwner/TYPE/VALUE/AX均null。新sourceAccepted=false、independentAffectedReviewPending=true、machinePending=true、qualified=false。

本地仅有一个行政打印失败：ACK与INPUT-BINDINGS保存后，可选REGISTRY owner显示把list当dict，抛AttributeError；源当时尚未写入。已读回ACK，错误及无源码/外部效果记录于LOCAL-READ-NOTES，未重放任何不确定写入。长合并输出截断已通过限定完整区间重读处理。没有新增Lean检查失败。

请求fresh gpt-6.1-sol/xhigh；实际backend/model/effort及input、cachedInput、output、reasoningSubset均不可见，分别null，不推测使用量。最终MANIFEST从真实文件派生并核对全部payload，之后最后写FINALWRITE释放writers/heavy/inflight/pendingExternal/children/uncertain六项为0并停止写入。

下一依赖是父线让原独立SOURCE审阅上下文只复核两处受影响proof和新源精确绑定，并安排新源服务器native；若成功，再取同首原对象的实际全部所属TYPE/requiredVALUE/传递AX并完成独立资格。原完整SOURCE审查按精确旧源与此次2行补充的并集复用，不自动再做全部旧局部证明审查。作者不自行执行、不自行qualified或发布。
