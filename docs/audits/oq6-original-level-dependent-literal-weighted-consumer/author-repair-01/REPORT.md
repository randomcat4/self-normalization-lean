# 第256单元三处证明表达修复交付

AUTHOR_STATUS: PROVED_AS_REPAIRED_COMPLETE_SOURCE_CANDIDATE。

新完整源 `OriginalLevelDependentLiteralWeightedConsumer.lean` 的 SHA256 为 `bbab19f1d8c091b81e3c06e7cfbc0dcc3c6acb16ce39261d0f08b2dc3ac1efcf`，66823B、1053LF。完整证明 `PROOF-BODY.txt` 为 `03325066041df6ad3fc4b5d5a266f44caa3597e74fb573efdc931a4028f84b07`，33117B、561LF，仍在完整源489–1049行。qualified=false、machinePending=true；此稿尚待同一独立审阅上下文的受影响证明审查以及父线新源服务器检查。

本作者是受限修复角色 `/root/oq56_unit256_author_repair01`。唯一写域为 `author-repair-01`，未取得其他作者、冻结、library、共享实现、服务器或发布权限。使用math-theorem，不使用math-ultra。所有Lean/lake/PP/AX、server、network、upload、Git/API、children、sidebar、Goal、schedule操作为0。没有安装或探测本地Lean，没有执行任何native重试。

原源 `8165e387c4f04ae5a751b76468d98fe8a5909d980f3d5f70384475b1c02d3466`／66807B、原MANIFEST `b26c98712d21495cc115b0eb88329a71610fb93bf2bc114b725a96d3ca90a6b8`／9112B、原FINALWRITE `8c17b37feaf3ad246e049c6c7300146284587d8bfca66137b86c8cf3a7a5374a`／2925B均已重算精确绑定。原35个payload逐一核验，原件与历史失败保持原位，只记录绑定，没有复制raw log、O、缓存或环境。原作者六零释放已核验。

原1053LF源码已经完整读取，初次显示截断的650–684行已单独补读。冻结声明、冻结路线、作者REPORT/ROUTE、旧独立SOURCE报告/VERDICT以及native02的完整diagnosticStdout/Stderr全部已读。修复后561LF证明再次连续全文读取；前488行与原源冻结前缀严格相同，结尾也相同。READ_ACK记录实际阅读与请求/实际模型字段，不继承旧作者的全文阅读主张。

仅第757、797、1030行改变，完整可审差异见EXACT-DIFF.patch和EXACT-DIFF.json，行数不变。没有更改任何函数定义、声明、前提、量词、选取顺序、常数或结论。

第757行在Fdelete第二分量的可测性证明中，将 `simpa only [Real.norm_eq_abs] using hFdelMeas.fst.norm.add ...` 替换为 `exact (continuous_abs.measurable.comp hFdelMeas.fst).add ...`。这直接将连续绝对值函数复合到真实Fdel第一投影，得到同一个逐点绝对值函数，再与原来的可测Mdelete表达式相加。没有改变Fdelete的完整三元函数、FU、Fdel、任何其他算术项或保留坐标输入。此写法与同一源未改动的hGap等绝对值可测性组合一致，避开norm化简后留下裸Pi加乘表达式的匹配问题。

第797行仅在 `simpa only [hDeltaEq k i]` 中增加 `Pi.sub_apply`。原 `(hMI.sub hMdI).abs` 的可积函数为 `fun x => |(M k - Mdelete k i) x|`；逐点函数减法展开为 `fun x => |M k x - Mdelete k i x|`，再由原hDeltaEq恰好识别冻结的 `fun x => |Δ k i x|`。hMI、hMdI、真正signed Δ、积分上界及非负性来源全部保持。

第1030行将 `add_le_add_right hSourceBound δ` 替换为 `add_le_add hSourceBound (le_refl δ)`，按两个输入不等式给出恰好的 `sourceCost0 + δ ≤ C + δ`，与原hk₀产生的 `sourceCostη k < sourceCost0 + δ`同向连接。原δ>0、最终量词、三次常数C、非严格最终结论和同一sourceCost均未改变。

冻结preamble a52e8a0b…／399B、head79510133…／33236B474LF、closing ea4bd4ef…／65B原字保持；精确拼接为preamble＋head＋`:= by`及LF＋完整PROOF-BODY＋closing。UTF-8无BOM、无CR、单个末尾LF，只有一个公开theorem，无顶层helper/def/instance，禁用标记零命中。完整255首合取的字面比较以及证明中直接交付整项hfor均保持。

完整库存复用旧作者已经建立的静态生成逻辑，仅替换输出目录与阅读/证据身份前缀；从 `source=SRC.read_bytes();` 开始的生成逻辑逐字复用，未增加机器执行包装器。LOCAL-CONTEXTS包含从实际源解析出的278条局部声明，完整类型/header、RHS、源切片、字节坐标和词法范围；BINDING-TYPES含27条绑定语句对应的349个完整pattern绑定；PRODUCER-TYPES保留5个完整输入合同及所有实际实例参数。每份库存明确为PURE_SOURCE_DERIVED_STATIC_NOT_MACHINE_OWNER，actual TYPE/VALUE/AX均为null。

与旧库存逐条比较，全部声明类型与词法范围、全部349个绑定类型/来源/RHS保持。受影响的局部完整RHS共有5条：hCurrent、hFdeleteMeas、hDeltaI、hDI、hSourceEventually；前两者以及hDeltaI分别包含其嵌套修改。CHANGED-CONTEXTS同时保存这5条旧/新完整局部、直接Fdel/FU/k₀/hk₀绑定的完整类型来源、相关未改动hMI/hMdI/hDeltaEq/hDeltaBound/hSourceBound/htail/Fdelete，以及全库存精确引用。全部305个局部/绑定命令源码切片逐字roundtrip。

native02保留为自然RC1、57.328906551003456秒、无O；投影文件绑定为f1b305a0…／6736B，原服务器receipt为19f622b9…／28093409B。此前预检/cwd以及RC127/PATH失败保持原位，不视为数学通过。此次修复未重放任何检查。旧SOURCE报告b1668b3e…／10987B及VERDICT0c533f9b…／2966B不变；它们对旧精确源的数学覆盖可由父线按受影响范围复用，不能自动标为新源内核通过。

同一个m₀仍在所有n/current-z/ε前选定；完整255 hfor保留；每个k仍从当前ε(k)包取得实际η及full/retained/deleted因子。当前B、Bdelete仍用512 rho z。H/M、真删除Δ、signed Q的L¹、full与partial费用及比值极限均保持，所有partial分母仍为完整Iη和I0。sourceCost0非负/三次界与任意δ正余量的最终η费用界保持。

承重255 source a2db2c09…／38774B、qualified3f042124…／8204B及完整generic合同按精确绑定复用；未重审或重跑任何已接受旧producer实际TYPE/AX或旧证明。原p严格budget、actual upper-event、truephysical付款、外部source engine、CDF/relative-tail/DC、fullOQ56/root仍OPEN；p54修正与Shao–Zhou外部归属保持。

请求模型gpt-6.1-sol、xhigh、fresh。实际model/backend/effort及input、cachedInput、output、reasoningSubset不可见，分别null，不根据请求值推测实际运行量。

本地静态结果只证明字节、范围、差异与库存一致性，不替代作者/审阅者分离的数学审查或Lean内核/递归公理资格。交付先写MANIFEST，最后FINALWRITE六零释放并停止所有写入。下一步由父线安排受影响独审和新完整源首次native；若成功，再对同一首次原O执行全所属TYPE/所需VALUE/递归AX。
