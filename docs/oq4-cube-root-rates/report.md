# OQ4 细根率独立最终审查109：综合裁决

STATUS: CORRECT
COVERAGE: PHASE_A_FULL_SEMANTICS + PHASE_B_UNIQUE_INDEPENDENT_NATIVE_ACTUALKERNEL
RAW_LEAF_INCREMENT: 0
ORIGINAL_ROOT_STATUS: OPEN
PARENT_TARGET_COMPILE: 0
CANONICAL_OR_EMIT: false

本裁决由本审查者独立作出：匿名数学证明与完整Source的语义核验，加上本次唯一独立检查及全部实际owner接口的逐项阅读，均支持冻结R1/R2。不是因PASS自动接受。未发现关键数学缺口、实际类型弱化、定义值偷换、非白名单公理、unsafe/partial或遗漏owner。原Spectrum及一般OQ4等原根均保持OPEN。Phase A文件原样保留，本报告只追加最终结论。

## 1. 实际执行与范围

Phase B获明确授权后先全文重读TEAM 1–93行，SHA256 ff2258843a9b097863a13f73fc616d0c5eabac1e267f09b65a02ecf01cc660ba。该文件相对Phase A的变动只是协作历史推进到v39，权限与lease未变；本轮仍固定实际运行基线 b6573a104d12d0fa333a7645eb1c0e73d67563ea、分支 feat/oq4-cube-root-rates，没有吸收新的root、更改数学Source、重放历史检查或阅读Root OQ4审查推理。

唯一完整Native检查：round001，exit 0，8.692977806553245秒，INDEPENDENT_FULL_NATIVE_PASS_STOP。通过server.py，先activate，再cd W，taskset CPU18–21运行固定runner；实际Lean参数为-M8192 -j4 -DautoImplicit=false -R independent-v1/private，未使用-o、RLIMIT_AS或ulimit-v。工具链是SERVER固定的leanprover/lean4:v4.36.0-rc1，实际二进制哈希db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00；没有本地Lean或其他工具链替代。

检查后立即向父报告精确结果并释放heavy。首个完整PASS以后未再运行Lean；后续只有我自己的JSON读取/派生/curation脚本与小文件下载。没有guard-only重跑、author命令、canonical、emit、cache操作、旧对象build或Git命令。server-only runtime-env未读取或下载；runner消费该固定文件，本报告只记录其哈希及环境键名。

原Source 9422B/SHA256 6f51957e561b4b693bcff304f797e284d905fc7a5ea3b5457819c3fe5e851247 未改。实际combined为原Source+b'\n'+审计suffix，17683B/SHA256 570b554a053d5d2d575bdcd3688dc840d9e2f1492ed9cb041fec6f628cc9628c；suffix为8260B/SHA256 813430bbb15157751217fd6c1a8ab04c7e91781dd1c54eae31ae78c89728407a。runner为17581B/SHA256 5e449204c7db5b8ccae6948706051fbcbc640a6dd2d5087634a3c54e328655a6。审计suffix 1–114和runner 1–155/156–292全文读完；其作用是只追加机器审计，无数学声明改写。

## 2. actualkernel与全owner覆盖

实际trustLevel=1025，skipKernelTC=false，autoImplicit=false。完整environmentDifference=moduleOwnership=stage2，三份名册相同，且与owned行名册严格相等。不是按命名空间前缀抽样。共有10项owned：2个definition、8个theorem；其中公开6项，private2项，generated2项。

[完整实际接口及定义值](curatedactual-owned-interfaces.md) 1–555行均已人工阅读，分块为1–152、153–271、272–401、402–555，无截断；全部10项actual type以及2项definition的完整普通/pp.all value均逐项判断。[逐项语义账](semantic-ledger.json)记录每项type、raw type Expr、显式type、definition value、raw definition Expr、显式value的SHA256及语义理由；非definition无定义值而未伪填。raw Expr与全closure仅机器通读，未下载或声称人工全文阅读。

| 序号 / curated行 | 实际声明与语义判断 |
|---|---|
| 1 / 5–14 | Shao.OQ4.RademacherCriticalPhase.nearestIndex.eq_1：名称在CP命名空间，但实际owner为本模块，已覆盖。全称c/α/k的原nearestIndex定义展开为Nat.floor(target+1/2)，无新根或假设。补读typeRefs确认Real运算；valueRefs仅Real/Nat/Eq.refl/原nearestIndex，故为生成的定义等式。 |
| 2 / 16–73 | BelowCubeBigO：Real→Nat→Prop；完整value是C>0及全自然尾部实际根误差≤C/K⁵，二阶修正1/(3K²)、casts、Real除法和Nat幂均正确。 |
| 3 / 75–82 | BelowCubeBigO._proof_1：自然数(2+1).AtLeastTwo，仅为实数常数3的OfNat实例生成。补读typeRefs/valueRefs确认Nat.AtLeastTwo与标准Nat实例，不是新数学前提。 |
| 4 / 84–132 | NearestCubeBigO：Real→Real→Nat→Prop，参数α/C/k₀；完整value是正C与全自然尾部同一CP.root(nearestIndex 1 α k)误差≤C/K²。 |
| 5 / 134–151 | below_cube_bigO：输出∃C:Real,∃k₀:Nat及C=1、k₀=2、C正性和完整全尾谓词，无额外参数。 |
| 6 / 153–237 | below_cube_finite：全部自然k≥2；实际natcast、正索引、同根非负/cube/height与含修正项的≤1/K⁵界全部保留，pp.all实例均为预期Nat/Real。 |
| 7 / 239–270 | nearest_cube_bigO：固定每个0<α<1，输出Real常数1/2与Nat阈值2，完整谓词保留全尾∀k。 |
| 8 / 272–483 | nearest_cube_finite：完整读取普通与pp.all类型；实际floor、t正性、正索引、同根身份、有符号半单位两侧、绝对舍入、∀l并列向上及≤1/(2K²)均为输出，没有自由root或误差假设。 |
| 9 / 485–500 | private below_cube_error：真实类型仅K≥2、r≥0、r³=K³−1推出目标含修正界，与已审Source代数论证相符；公开调用锁定同一CP根。 |
| 10 / 502–515 | private nearest_cube_error：真实类型仅K≥2、t≥K、r≥0、真实cube差≤1/2推出根误差，与已审Source相符。 |

两个def的value哈希分别为5122610e26198c550856d28c11d192479e3850a9e11d9dcd7934c72a3ce59891、136b67da012833c853cd6828409fbb748938732f703b917ea3851d188ad0c390；逐字完整显示在curated 33–42/47–72及101–110/115–131行。它们不是有限样例谓词，也未将输出根率作为新输入。全部10项type哈希及每项阅读理由见semantic-ledger，无仅按计数作结论的条目。

## 3. 数学语义与边界的综合判断

Phase A已完整审阅151行匿名数学证明、246行原Source、85行冻结形式接口、53行自然语言冻结、原Spectrum119行及frozen01全文；指定数学文件哈希未变。Source的2个透明def与4个公开head与冻结文本逐字相同，本轮实际表达式再次确认编码忠实。

R1：对每个自然k≥2先合法恢复自然减法的实数身份。a=K−1/(3K²)，B=a³−r³=(9K³−1)/(27K⁶)，0≤B≤1/(3K³)；D=a²+ar+r²≥K²/3>0，因此0≤a−r≤1/K⁵。源中两个field_simp等式、非负项、分母正性、绝对值方向已在Phase A逐步审查，本轮内核成功接受同一源码。C=1、k₀=2确为输出。

R2：同一Nat.floor((K+α)³+1/2)给−1/2<n−(K+α)³≤1/2，并覆盖半整数并列向上；r=同一CP.root(n)。D=r²+rt+t²≥t²≥K²>0，将实际cube差≤1/2转为|r−t|≤1/(2K²)。C=1/2、k₀=2为输出，且每个固定0<α<1/所有k≥2量词均保留。

k=2的自然减法不截断，R1 n=7、K²/3=4/3，R2因子下界≥4。α接近0或1都不要求正距离或更大阈值；精确α=0、1仍在冻结域外。并列的−1/2严格、+1/2非严格方向正确。未发现边界异常，也未从确定性一致常数推断概率一致极限或一般c率。

## 4. 递归闭包、公理与项目依赖

审计suffix73–98行从所有owner出发，递归展开每个常量的type及value，其中value? true纳入opaque theorem证明体引用。我的derive-curated-audit.py又从该完整图的10个owner独立作可达性遍历：16829个节点、393912个边引用出现次数；所有引用有节点，重算可达集合严格等于全部closure行，没有不可达多余项或漏边终点。owned与project行的module/kind/typeRefs/valueRefs逐项和closure行一致；不是只核数量。

闭包内axiom-kind节点恰为Classical.choice、Quot.sound、propext。每个owned及每个项目依赖的collectAxioms也仅在这三项中，allowned/allproject的unsafe、partial、axiom-kind计数全部0。大图与raw Expr留在服务器：audit-native.json为8995878B/SHA256 e5c01f6c92b16451a7082333701b96efccadf042057018ae8932efd9daf573e3；raw-expressions.json为199165B/SHA256 ad1e30da32592fdafa73d3b57046de4d66ef7a2154fe29a5f8342e11d563972a。原始大型包全部由脚本通读，未下载、未声称人工审读opaque证明正文。

项目依赖恰37项，唯一owner/module为Shao.OQ4.RademacherCriticalPhase；37项的全名称、kind、安全、公理逐项列在curated519–555行及semantic-ledger.project_dependencies。包含CP的private/generated依赖，没有只保留公开heads。全部closure的module计数亦保留在semantic-ledger。只展示上游名称与安全元数据，没有读取/展示CP实现证明。

## 5. 实际import绑定、Source与保护映射

Lean.findOLean实际返回唯一CP别名：
W/repro_outputs/oq4-cube-root-rates-implementation-v1/runtime-project-lib-v1/Shao/OQ4/RademacherCriticalPhase.olean，
该路径确为symlink，并实际解析到唯一原对象
W/.lake/build/lib/lean/Shao/OQ4/RademacherCriticalPhase.olean，
SHA256 2d11da742f05a509d66a7646edf8b97cf64d7f4a9826f092ba0424b32ed278ec。其实际Source W/Shao/OQ4/RademacherCriticalPhase.lean哈希388f17e1c257d9b1fe74914866937bd9dc6ce1fb1398e72761b3f65c8464a96f。本次pre/post以及我自己的机器派生均逐项重算source/object哈希和解析等式；alias成员集合与实际project importbinding计数均恰1，无对象复制。

W表示/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4。前后四个完整映射计数固定52/224/276/109，逐文件哈希差异均空，pre/post观察映射摘要也分别相同。源码成员、旧build成员、packages只读symlink和6条冻结分支ref均匹配；wholeW目标前缀恰2，只有author与independent的私有Source；canonical源、canonical对象、所有canonical build前缀均不存在。目标原Source、实际combined及suffix的拼接字节等式前后都匹配。

result.json哈希 bfe232d786a607b077def9fd847b8d0c7e0bb5b3d51ba6dac4bdcb7c29d1bf5a；command.json哈希9efe7e0118adab41b458d5687cd86768b625f32e1214b072a0e41c863ddfdd69；pre/post guard哈希8df19092f43078792aa062a9c867cd1a4f99b7c540efc7317df406eb1441af25 / e65049cc7283066d689beeeb4215f85399f66b8754b7abc551ce896d500012c1；stderr为空。完整收据元数据见report.json与semantic-ledger。

## 6. 新输入账、读取方式与披露

Phase A全部输入的全文范围/原字节哈希、唯一初始截断及完整补读均保存在phase-a-review.md/json；两个Phase A报告分别保持SHA256 690c005d4224328cfb4ae715b0c06473f6b4183dae00758d44953a17b6475b6d / 4a8355423b90a7866759dbb282feb3071294854b21dddedb160d2fe1d7e9ea36。新增读取如下，完整指纹详见report.json：

- TEAM 1–93全文；suffix1–114全文；runner1–155与156–292全文。
- tools/server.py1–5、transport_client.py1–104全文，哈希分别6f8812c3749030efe89bb33834090a8b498db54715041f086b6780b43658a878、bb0d3003815b2e65fbde3eefdb3678345ccfe88e50313aa2ad53a8b9d2e02058。
- selected-runtime-bindings1–15及runtime-project-view1–13全文，哈希6e9d060fa411a2d052ab086cb732be9f2e7221f05abc64bfb8a1632a2423cd52 / 007861bd61eda5c6fddf90ffd822d6e93a2e6fd8ec46dbc931ac0e8c3d14c8a0。
- stable-base 77786B/710行，SHA256 e34415dde885cbcff7c04c938ff4d78f25d76bc562a68f25486ad3ecd41ce988：仅schema/scalars/计数人工投影，不声称全文人工阅读；四张完整map由runner机器前后通读比对。首次PowerShell计数显示表达式产生连续1串，已用数组Count更正为6/52/224/276/109，实际审计Python len未受影响。
- native-result1–35与native-command1–27全文；curated实际接口1–555全文；machine-derived-ledger仅人工读取scalars、全部owned哈希行、pre/post小型保护摘要与绑定，其他字段由机器派生保留，不声称1604行全文人工阅读。
- 服务器audit-native/raw-expressions/pre/post guard为机器全文输入；未下载大raw、完整closure、日志或runtime-env。额外生成定理的typeRefs/valueRefs小投影另存generated-refs-response.json并全文阅读。Phase B无任何工具输出截断。

未读取任何其他审查、authorreceipt/progress、父推理或CP/strict cube实现证明；实际生成定理、project私有常量的名称/依赖边元数据不等于泄露其实现证明。Phase A的数学公开输入范围保持不变。

## 7. 最终状态

CORRECT：指定冻结R1/R2的完整数学/Source语义与实际内核检查、全owner/definition values、完整递归type+value闭包、公理及实际绑定均通过本审查。对这两个确定性精细余项达到本轮完整验证；不扩大概率、strict、一般c或一般OQ4作用域。

rawleaf=0，所有本单元原根OPEN，parenttargetcompile=0；无canonical/emit。STOP，等待父实例后续安排，不重跑首次成功Native。
